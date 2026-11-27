//! ATAQUE-02: Binomial Ideal Lift `(z3 ^ z4) * E_MAJ3` & Logged Degree-Absorbing Macaulay Cascade.
//!
//! For compact fibers (`|all_active| <= 48`), computes the full local vanishing ideal `I_{<=d}(S_sat)`
//! on each support `S` (`|S| <= 7`), forms shifted Macaulay multiples `v * p2` for `d_cur == 3`
//! (`|S'| <= 8`), runs sparse `GF(2)` RREF with degree-lex ordering (`deg 3 > deg 2 > deg 1 > const`),
//! and certifies either `0 == 1` directly or derived degree-1 units / 2-XORs via the `VeroneseRecord`
//! `pol + red` sum-and-halve engine, simplifying the fiber across up to 5 rounds.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::{
    collapse_clause_cube, emit_veronese_linear_combination, ensure_uniform_guard,
    normalize_clause, try_certify_guarded_php, try_certify_guarded_veronese_rm_d,
    unroll_11_chains_logged, weaken_clause_to_target, VeriPBLogger, VeroneseRecord,
};

struct BaseBlock {
    supp: Vec<i32>,
    forbid_map: Vec<Option<(usize, HashSet<i32>)>>,
}

struct LazyPolyRecord {
    base_idx: usize,
    shift_var: Option<i32>,
    lin_vars: Vec<i32>,
    higher_mons: Vec<Vec<i32>>,
    rhs: u8,
}

impl LazyPolyRecord {
    fn materialize(&self, blocks: &[BaseBlock]) -> VeroneseRecord {
        let base = &blocks[self.base_idx];
        match self.shift_var {
            None => VeroneseRecord {
                supp: base.supp.clone(),
                lin_vars: self.lin_vars.clone(),
                higher_mons: self.higher_mons.clone(),
                rhs: self.rhs,
                forbid_map: base.forbid_map.clone(),
            },
            Some(sv) => {
                let mut supp_new = base.supp.clone();
                let ins_pos = supp_new.binary_search(&sv).unwrap_err();
                supp_new.insert(ins_pos, sv);
                let k_new = supp_new.len();
                let full_new = 1usize << k_new;
                let mut f_new: Vec<Option<(usize, HashSet<i32>)>> = vec![None; full_new];
                let low_mask = (1usize << ins_pos) - 1;
                for m_new in 0..full_new {
                    let m_old = (m_new & low_mask) | ((m_new >> 1) & !low_mask);
                    if let Some(ref entry) = base.forbid_map[m_old] {
                        f_new[m_new] = Some(entry.clone());
                    }
                }
                VeroneseRecord {
                    supp: supp_new,
                    lin_vars: self.lin_vars.clone(),
                    higher_mons: self.higher_mons.clone(),
                    rhs: self.rhs,
                    forbid_map: f_new,
                }
            }
        }
    }
}

/// Compute local vanishing ideal `I_{<=deg_lim}(S_sat)` on `block` (`|supp| <= 7`).
/// Returns `Err(contra_cid)` if `S_sat` is empty, otherwise `Ok(list_of_polys)`.
fn compute_local_vanishing_ideal(
    block: &BaseBlock,
    base_idx: usize,
    deg_lim: usize,
    guard_lits: &[i32],
    logger: &mut VeriPBLogger,
) -> Result<Vec<LazyPolyRecord>, usize> {
    let supp = &block.supp;
    let k = supp.len();
    let full_cube = 1usize << k;

    let mut sat_masks: Vec<usize> = Vec::new();
    for m in 0..full_cube {
        if block.forbid_map[m].is_none() {
            sat_masks.push(m);
        }
    }

    if sat_masks.is_empty() {
        let mut leaves = vec![0usize; full_cube];
        for mask in 0..full_cube {
            let mut target = guard_lits.to_vec();
            for q in 0..k {
                target.push(if ((mask >> q) & 1) == 1 {
                    -supp[q]
                } else {
                    supp[q]
                });
            }
            let (base_cid, ref pres) = block.forbid_map[mask].as_ref().unwrap();
            leaves[mask] = weaken_clause_to_target(*base_cid, pres, &target, logger);
        }
        return Err(collapse_clause_cube(k, &leaves, logger));
    }

    if sat_masks.len() == full_cube || sat_masks.len() > 128 {
        return Ok(Vec::new());
    }

    let mut mon_masks: Vec<usize> = Vec::new();
    for deg in 0..=deg_lim.min(k) {
        for m in 0..full_cube {
            if (m.count_ones() as usize) == deg {
                mon_masks.push(m);
            }
        }
    }
    let n_mons = mon_masks.len();
    let comb_words = (n_mons + 63) / 64;
    let mut pivots: BTreeMap<usize, (u128, Vec<u64>)> = BTreeMap::new();
    let mut out: Vec<LazyPolyRecord> = Vec::new();

    for (m_idx, &mm) in mon_masks.iter().enumerate() {
        let mut vec_eval: u128 = 0;
        for (s_idx, &sm) in sat_masks.iter().enumerate() {
            if (sm & mm) == mm {
                vec_eval |= 1u128 << s_idx;
            }
        }
        let mut comb = vec![0u64; comb_words];
        comb[m_idx / 64] |= 1u64 << (m_idx % 64);

        let reduced_comb = loop {
            if vec_eval == 0 {
                break Some(comb);
            }
            let msb = 127usize - (vec_eval.leading_zeros() as usize);
            if let Some((p_vec, p_comb)) = pivots.get(&msb) {
                vec_eval ^= *p_vec;
                for w in 0..comb_words {
                    comb[w] ^= p_comb[w];
                }
            } else {
                pivots.insert(msb, (vec_eval, comb));
                break None;
            }
        };

        if let Some(comb) = reduced_comb {
            let rhs = (comb[0] & 1) as u8;
            let mut lin_vars = Vec::new();
            let mut higher_mons = Vec::new();
            for b in 1..n_mons {
                if ((comb[b / 64] >> (b % 64)) & 1) == 1 {
                    let bm = mon_masks[b];
                    if bm.count_ones() == 1 {
                        lin_vars.push(supp[bm.trailing_zeros() as usize]);
                    } else {
                        let mut mon = Vec::new();
                        for j in 0..k {
                            if ((bm >> j) & 1) == 1 {
                                mon.push(supp[j]);
                            }
                        }
                        higher_mons.push(mon);
                    }
                }
            }
            if !lin_vars.is_empty() || !higher_mons.is_empty() || rhs == 1 {
                out.push(LazyPolyRecord {
                    base_idx,
                    shift_var: None,
                    lin_vars,
                    higher_mons,
                    rhs,
                });
            }
        }
    }

    Ok(out)
}

fn shift_deg2_poly(p2: &LazyPolyRecord, v: i32) -> LazyPolyRecord {
    let mut lin_vars = Vec::new();
    if p2.rhs == 1 {
        lin_vars.push(v);
    }
    let mut higher_mons: Vec<Vec<i32>> = Vec::with_capacity(p2.lin_vars.len() + p2.higher_mons.len());
    for &u in &p2.lin_vars {
        let mut m = if u < v { vec![u, v] } else { vec![v, u] };
        m.dedup();
        if m.len() == 1 {
            if let Some(pos) = lin_vars.iter().position(|&x| x == m[0]) {
                lin_vars.swap_remove(pos);
            } else {
                lin_vars.push(m[0]);
            }
        } else {
            higher_mons.push(m);
        }
    }
    for mon in &p2.higher_mons {
        let mut m = mon.clone();
        m.push(v);
        m.sort_unstable();
        m.dedup();
        higher_mons.push(m);
    }
    LazyPolyRecord {
        base_idx: p2.base_idx,
        shift_var: Some(v),
        lin_vars,
        higher_mons,
        rhs: 0,
    }
}

fn decode_comb_indices(comb: &[u64]) -> Vec<usize> {
    let mut active = Vec::new();
    for (w_idx, &word) in comb.iter().enumerate() {
        let mut tmp = word;
        while tmp != 0 {
            let bit = tmp.trailing_zeros() as usize;
            active.push(w_idx * 64 + bit);
            tmp &= tmp - 1;
        }
    }
    active
}

/// Apply derived guarded units and 2-XORs to `work_fiber` via logged `pol` resolution,
/// then unroll (1,1)-chains protecting `cut_set`.
/// Returns `Err(contra_cid)` if an empty core clause is derived.
fn simplify_fiber_with_linear_lemmas(
    work_fiber: &[(Vec<i32>, usize)],
    derived_units: &[(i32, usize)],
    derived_2xors: &[(i32, i32, u8, usize, usize)], // (v_hi, v_lo, rhs, cid_hi_pos, cid_hi_neg)
    guard_lits: &[i32],
    cut_set: &HashSet<i32>,
    logger: &mut VeriPBLogger,
) -> Result<Vec<(Vec<i32>, usize)>, usize> {
    let has_guard = !guard_lits.is_empty();
    let mut unit_map: HashMap<i32, (i32, usize)> = HashMap::new();
    for &(u_lit, u_cid) in derived_units {
        let v = u_lit.abs();
        if let Some(&(prev_lit, prev_cid)) = unit_map.get(&v) {
            if prev_lit == -u_lit {
                let contra = logger.emit_pol_add2(prev_cid, u_cid, has_guard);
                return Err(contra);
            }
        } else {
            unit_map.insert(v, (u_lit, u_cid));
        }
    }

    // Map v_hi -> (l_when_hi_pos, cid_hi_neg, l_when_hi_neg, cid_hi_pos)
    // cid_hi_neg is clause (guard U {-v_hi, l_when_hi_pos}) -> resolves with +v_hi to replace +v_hi by l_when_hi_pos
    // cid_hi_pos is clause (guard U {+v_hi, l_when_hi_neg}) -> resolves with -v_hi to replace -v_hi by l_when_hi_neg
    let mut xor_map: HashMap<i32, (i32, usize, i32, usize)> = HashMap::new();
    for &(v_hi, v_lo, rhs, cid_hi_pos, cid_hi_neg) in derived_2xors {
        if unit_map.contains_key(&v_hi) {
            continue;
        }
        let (l_for_pos, l_for_neg) = if rhs == 0 {
            (v_lo, -v_lo)
        } else {
            (-v_lo, v_lo)
        };
        xor_map
            .entry(v_hi)
            .or_insert((l_for_pos, cid_hi_neg, l_for_neg, cid_hi_pos));
    }

    let mut simplified: Vec<(Vec<i32>, usize)> = Vec::with_capacity(work_fiber.len());
    for (cl, cid) in work_fiber {
        let mut cur_cl = cl.clone();
        let mut cur_cid = *cid;
        let mut subsumed = false;

        // First apply unit resolutions
        let mut i = 0;
        while i < cur_cl.len() {
            let lit = cur_cl[i];
            if let Some(&(u_lit, u_cid)) = unit_map.get(&lit.abs()) {
                if u_lit == lit {
                    subsumed = true;
                    break;
                } else {
                    // lit == -u_lit: resolve out
                    cur_cid = logger.emit_pol_add2(cur_cid, u_cid, has_guard);
                    cur_cl.remove(i);
                    continue;
                }
            }
            i += 1;
        }
        if subsumed {
            continue;
        }
        if cur_cl.is_empty() {
            return Err(cur_cid);
        }

        // Next apply 2-XOR substitutions (up to a small fixed bound to follow chains)
        for _ in 0..8 {
            let mut replaced = false;
            for idx in 0..cur_cl.len() {
                let lit = cur_cl[idx];
                let v = lit.abs();
                if let Some(&(l_for_pos, cid_hi_neg, l_for_neg, cid_hi_pos)) = xor_map.get(&v) {
                    let (rep_lit, rep_cid) = if lit > 0 {
                        (l_for_pos, cid_hi_neg)
                    } else {
                        (l_for_neg, cid_hi_pos)
                    };
                    if cur_cl.contains(&(-rep_lit)) {
                        subsumed = true;
                        break;
                    }
                    let overlap = has_guard || cur_cl.contains(&rep_lit);
                    cur_cid = logger.emit_pol_add2(cur_cid, rep_cid, overlap);
                    cur_cl.remove(idx);
                    if !cur_cl.contains(&rep_lit) {
                        cur_cl.push(rep_lit);
                    }
                    replaced = true;
                    break;
                }
            }
            if subsumed || !replaced {
                break;
            }
        }
        if subsumed {
            continue;
        }
        // Re-check units after 2-XOR substitutions
        let mut j = 0;
        while j < cur_cl.len() {
            let lit = cur_cl[j];
            if let Some(&(u_lit, u_cid)) = unit_map.get(&lit.abs()) {
                if u_lit == lit {
                    subsumed = true;
                    break;
                } else {
                    cur_cid = logger.emit_pol_add2(cur_cid, u_cid, has_guard);
                    cur_cl.remove(j);
                    continue;
                }
            }
            j += 1;
        }
        if subsumed {
            continue;
        }
        if cur_cl.is_empty() {
            return Err(cur_cid);
        }
        if let Some(norm) = normalize_clause(&cur_cl) {
            simplified.push((norm, cur_cid));
        }
    }

    // Re-attach guard_lits and unroll (1,1)-chains
    let re_items: Vec<(Vec<i32>, usize)> = simplified
        .into_iter()
        .map(|(core, u_cid)| {
            let mut full = guard_lits.to_vec();
            full.extend_from_slice(&core);
            full.sort_by_key(|&z| (z.abs(), z));
            (full, u_cid)
        })
        .collect();
    let re_unrolled = unroll_11_chains_logged(&re_items, logger, cut_set);

    let mut clean: Vec<(Vec<i32>, usize)> = Vec::with_capacity(re_unrolled.len());
    for (full_cl, f_cid) in re_unrolled {
        let present_g: HashSet<i32> = full_cl
            .iter()
            .copied()
            .filter(|x| cut_set.contains(&x.abs()))
            .collect();
        let core: Vec<i32> = full_cl
            .iter()
            .copied()
            .filter(|x| !cut_set.contains(&x.abs()))
            .collect();
        let u_cid = ensure_uniform_guard(f_cid, &present_g, guard_lits, logger);
        if core.is_empty() {
            return Err(u_cid);
        }
        clean.push((core, u_cid));
    }
    Ok(clean)
}

/// Single-branch Logged Degree-Absorbing Macaulay Cascade on compact fibers (`<= 48` active vars).
fn try_certify_guarded_binom_macaulay_single(
    fiber_clean: &[(Vec<i32>, usize)],
    guard_lits: &[i32],
    cut_set: &HashSet<i32>,
    logger: &mut VeriPBLogger,
    next_var: &mut i32,
) -> Option<(usize, usize)> {
    let mut init_active: BTreeSet<i32> = BTreeSet::new();
    for (cl, _) in fiber_clean {
        for &l in cl {
            init_active.insert(l.abs());
        }
    }
    if init_active.is_empty() || init_active.len() > 48 {
        return None;
    }

    let guard_set: HashSet<i32> = guard_lits.iter().copied().collect();
    let mut work_fiber: Vec<(Vec<i32>, usize)> = fiber_clean.to_vec();

    for round in 0..5usize {
        if round > 0 {
            if let Some(php_cid) = try_certify_guarded_php(&work_fiber, guard_lits, logger) {
                return Some((php_cid, 3));
            }
            if let Some((v_cid, deg_u)) =
                try_certify_guarded_veronese_rm_d(&work_fiber, guard_lits, logger, next_var, 4, 8)
            {
                return Some((v_cid, deg_u.max(2)));
            }
        }

        let mut active_set: BTreeSet<i32> = BTreeSet::new();
        for (cl, _) in &work_fiber {
            for &l in cl {
                active_set.insert(l.abs());
            }
        }
        if active_set.is_empty() || active_set.len() > 48 {
            return None;
        }
        let all_active: Vec<i32> = active_set.iter().copied().collect();
        let n_active = all_active.len();
        let var_to_lin_id: HashMap<i32, usize> = all_active
            .iter()
            .enumerate()
            .map(|(i, &v)| (v, i + 1))
            .collect();

        // Group clauses of width <= 7 by support S
        let mut by_supp: BTreeMap<Vec<i32>, Vec<(Vec<i32>, usize)>> = BTreeMap::new();
        for (cl, cid) in &work_fiber {
            if !cl.is_empty() && cl.len() <= 7 {
                let mut supp: Vec<i32> = cl.iter().map(|x| x.abs()).collect();
                supp.sort_unstable();
                supp.dedup();
                if supp.len() == cl.len() {
                    by_supp.entry(supp).or_default().push((cl.clone(), *cid));
                }
            }
        }
        if by_supp.is_empty() {
            return None;
        }

        // Build BaseBlocks, also populating forbid_map from any shorter clause whose vars ⊆ S
        let mut blocks: Vec<BaseBlock> = Vec::with_capacity(by_supp.len());
        let short_clauses: Vec<(Vec<i32>, usize, HashSet<i32>)> = work_fiber
            .iter()
            .filter(|(cl, _)| !cl.is_empty() && cl.len() <= 6)
            .map(|(cl, cid)| {
                let vs: HashSet<i32> = cl.iter().map(|x| x.abs()).collect();
                (cl.clone(), *cid, vs)
            })
            .collect();

        for (supp, items) in by_supp {
            let k = supp.len();
            let full_cube = 1usize << k;
            let mut forbid_map: Vec<Option<(usize, HashSet<i32>)>> = vec![None; full_cube];
            for (cl, cid) in items {
                let mut mask = 0usize;
                for &lit in &cl {
                    let pos = supp.binary_search(&lit.abs()).unwrap();
                    if lit < 0 {
                        mask |= 1usize << pos;
                    }
                }
                if forbid_map[mask].is_none() {
                    let mut pres = guard_set.clone();
                    for &lit in &cl {
                        pres.insert(lit);
                    }
                    forbid_map[mask] = Some((cid, pres));
                }
            }
            // Also include any shorter clause whose support is a strict subset of `supp`
            let supp_set: HashSet<i32> = supp.iter().copied().collect();
            for (scl, scid, svs) in &short_clauses {
                if scl.len() < k && svs.is_subset(&supp_set) {
                    let mut req_pos = 0usize;
                    let mut req_val = 0usize;
                    for &lit in scl {
                        let pos = supp.binary_search(&lit.abs()).unwrap();
                        req_pos |= 1usize << pos;
                        if lit < 0 {
                            req_val |= 1usize << pos;
                        }
                    }
                    let mut pres = guard_set.clone();
                    for &lit in scl {
                        pres.insert(lit);
                    }
                    for mask in 0..full_cube {
                        if (mask & req_pos) == req_val && forbid_map[mask].is_none() {
                            forbid_map[mask] = Some((*scid, pres.clone()));
                        }
                    }
                }
            }
            blocks.push(BaseBlock { supp, forbid_map });
        }

        // Precompute I_{<=2}(S_sat) once per round (used for both d_cur == 2 and shifts in d_cur == 3)
        let mut ideal_deg2_per_block: Vec<Vec<LazyPolyRecord>> = Vec::with_capacity(blocks.len());
        for (b_idx, blk) in blocks.iter().enumerate() {
            match compute_local_vanishing_ideal(blk, b_idx, 2, guard_lits, logger) {
                Ok(polys) => ideal_deg2_per_block.push(polys),
                Err(contra_cid) => return Some((contra_cid, 2)),
            }
        }

        let mut progressed_round = false;

        for d_cur in [2usize, 3usize] {
            let mut records: Vec<LazyPolyRecord> = Vec::new();
            if d_cur == 2 {
                for polys in &ideal_deg2_per_block {
                    for p in polys {
                        records.push(LazyPolyRecord {
                            base_idx: p.base_idx,
                            shift_var: None,
                            lin_vars: p.lin_vars.clone(),
                            higher_mons: p.higher_mons.clone(),
                            rhs: p.rhs,
                        });
                    }
                }
            } else {
                // d_cur == 3: include full I_{<=3}(S_sat) + shifted v * p2 for p2 in I_{<=2}(S_sat)
                for (b_idx, blk) in blocks.iter().enumerate() {
                    match compute_local_vanishing_ideal(blk, b_idx, 3, guard_lits, logger) {
                        Ok(polys) => records.extend(polys),
                        Err(contra_cid) => return Some((contra_cid, 3)),
                    }
                }
                for (b_idx, polys2) in ideal_deg2_per_block.iter().enumerate() {
                    let blk_supp = &blocks[b_idx].supp;
                    if blk_supp.len() >= 8 {
                        continue;
                    }
                    for p2 in polys2 {
                        // Only shift polynomials that actually have degree <= 2 (guaranteed) and are non-trivial
                        for &v in &all_active {
                            if blk_supp.binary_search(&v).is_ok() {
                                continue;
                            }
                            records.push(shift_deg2_poly(p2, v));
                        }
                    }
                }
            }

            if records.is_empty() {
                continue;
            }

            // Degree-lex coordinate IDs:
            // deg 1 -> 1..=n_active
            // deg 2 -> 1000..
            // deg 3 -> 1_000_000..
            let mut mon2_to_id: HashMap<Vec<i32>, usize> = HashMap::new();
            let mut mon3_to_id: HashMap<Vec<i32>, usize> = HashMap::new();
            let mut next_deg2_id = 1000usize;
            let mut next_deg3_id = 1_000_000usize;

            let comb_words = (records.len() + 63) / 64;
            let mut pivots: BTreeMap<usize, (BTreeSet<usize>, u8, Vec<u64>)> = BTreeMap::new();
            let mut unsat_comb: Option<Vec<u64>> = None;

            for (idx_r, rec) in records.iter().enumerate() {
                let mut row_coords: BTreeSet<usize> = BTreeSet::new();
                for &v in &rec.lin_vars {
                    let c = var_to_lin_id[&v];
                    if !row_coords.remove(&c) {
                        row_coords.insert(c);
                    }
                }
                for mon in &rec.higher_mons {
                    let c = if mon.len() == 2 {
                        *mon2_to_id.entry(mon.clone()).or_insert_with(|| {
                            let id = next_deg2_id;
                            next_deg2_id += 1;
                            id
                        })
                    } else {
                        *mon3_to_id.entry(mon.clone()).or_insert_with(|| {
                            let id = next_deg3_id;
                            next_deg3_id += 1;
                            id
                        })
                    };
                    if !row_coords.remove(&c) {
                        row_coords.insert(c);
                    }
                }

                let mut rhs = rec.rhs;
                let mut comb = vec![0u64; comb_words];
                comb[idx_r / 64] |= 1u64 << (idx_r % 64);

                loop {
                    let Some(&lead) = row_coords.iter().next_back() else {
                        if rhs == 1 {
                            unsat_comb = Some(comb);
                        }
                        break;
                    };
                    if let Some((p_coords, p_rhs, p_comb)) = pivots.get(&lead) {
                        for &pc in p_coords {
                            if !row_coords.remove(&pc) {
                                row_coords.insert(pc);
                            }
                        }
                        rhs ^= *p_rhs;
                        for w in 0..comb_words {
                            comb[w] ^= p_comb[w];
                        }
                    } else {
                        // If this is a degree-1 pivot (lead <= n_active), also back-substitute into
                        // existing degree-1 pivots to expose all units and 2-XORs!
                        if lead <= n_active {
                            let deg1_keys: Vec<usize> = pivots
                                .range(..=n_active)
                                .map(|(&k, _)| k)
                                .collect();
                            for pk in deg1_keys {
                                if pivots[&pk].0.contains(&lead) {
                                    let (p_coords, p_rhs, p_comb) = pivots.get_mut(&pk).unwrap();
                                    for &rc in &row_coords {
                                        if !p_coords.remove(&rc) {
                                            p_coords.insert(rc);
                                        }
                                    }
                                    *p_rhs ^= rhs;
                                    for w in 0..comb_words {
                                        p_comb[w] ^= comb[w];
                                    }
                                }
                            }
                        }
                        pivots.insert(lead, (row_coords, rhs, comb));
                        break;
                    }
                }
                if unsat_comb.is_some() {
                    break;
                }
            }

            // 1. Direct contradiction `0 == 1`!
            if let Some(ucomb) = unsat_comb {
                let active_idxs = decode_comb_indices(&ucomb);
                let mat_recs: Vec<VeroneseRecord> = active_idxs
                    .iter()
                    .map(|&idx| records[idx].materialize(&blocks))
                    .collect();
                let cid = emit_veronese_linear_combination(
                    &mat_recs,
                    &[],
                    guard_lits,
                    logger,
                    next_var,
                );
                return Some((cid, d_cur));
            }

            // 2. Check for derived degree-1 units (`z_u == c`) and 2-XORs (`z_u ^ z_v == c`)
            let mut unit_lemmas: Vec<(i32, Vec<usize>)> = Vec::new();
            let mut xor2_lemmas: Vec<(i32, i32, u8, Vec<usize>)> = Vec::new();
            let mut seen_unit_vars: HashSet<i32> = HashSet::new();
            let mut seen_xor_hi: HashSet<i32> = HashSet::new();

            for (&_lead, (p_coords, p_rhs, p_comb)) in pivots.range(..=n_active) {
                if p_coords.len() == 1 {
                    let c1 = *p_coords.iter().next().unwrap();
                    let v1 = all_active[c1 - 1];
                    if seen_unit_vars.insert(v1) {
                        let u_lit = if *p_rhs == 1 { v1 } else { -v1 };
                        unit_lemmas.push((u_lit, decode_comb_indices(p_comb)));
                    }
                } else if p_coords.len() == 2 {
                    let mut it = p_coords.iter();
                    let c1 = *it.next().unwrap();
                    let c2 = *it.next().unwrap();
                    let v1 = all_active[c1 - 1];
                    let v2 = all_active[c2 - 1];
                    let (v_lo, v_hi) = if v1 < v2 { (v1, v2) } else { (v2, v1) };
                    if seen_xor_hi.insert(v_hi) {
                        xor2_lemmas.push((v_hi, v_lo, *p_rhs, decode_comb_indices(p_comb)));
                    }
                }
            }

            if unit_lemmas.is_empty() && xor2_lemmas.is_empty() {
                continue;
            }

            // Certify derived guarded units and 2-XORs in VeriPB!
            let mut cert_units: Vec<(i32, usize)> = Vec::with_capacity(unit_lemmas.len());
            for (u_lit, active_idxs) in unit_lemmas {
                let mat_recs: Vec<VeroneseRecord> = active_idxs
                    .iter()
                    .map(|&idx| records[idx].materialize(&blocks))
                    .collect();
                let u_cid = emit_veronese_linear_combination(
                    &mat_recs,
                    &[u_lit],
                    guard_lits,
                    logger,
                    next_var,
                );
                cert_units.push((u_lit, u_cid));
            }

            let mut cert_2xors: Vec<(i32, i32, u8, usize, usize)> =
                Vec::with_capacity(xor2_lemmas.len());
            for (v_hi, v_lo, rhs, active_idxs) in xor2_lemmas {
                if seen_unit_vars.contains(&v_hi) {
                    continue;
                }
                let mat_recs: Vec<VeroneseRecord> = active_idxs
                    .iter()
                    .map(|&idx| records[idx].materialize(&blocks))
                    .collect();
                let (cl_pos, cl_neg) = if rhs == 0 {
                    ([v_hi, -v_lo], [-v_hi, v_lo])
                } else {
                    ([v_hi, v_lo], [-v_hi, -v_lo])
                };
                let cid_pos = emit_veronese_linear_combination(
                    &mat_recs,
                    &cl_pos,
                    guard_lits,
                    logger,
                    next_var,
                );
                let cid_neg = emit_veronese_linear_combination(
                    &mat_recs,
                    &cl_neg,
                    guard_lits,
                    logger,
                    next_var,
                );
                cert_2xors.push((v_hi, v_lo, rhs, cid_pos, cid_neg));
            }

            match simplify_fiber_with_linear_lemmas(
                &work_fiber,
                &cert_units,
                &cert_2xors,
                guard_lits,
                cut_set,
                logger,
            ) {
                Err(contra_cid) => return Some((contra_cid, d_cur)),
                Ok(next_fiber) => {
                    work_fiber = next_fiber;
                    progressed_round = true;
                    break; // proceed to next round with simplified fiber
                }
            }
        }

        if !progressed_round {
            break;
        }
    }

    None
}

/// ATAQUE-02 entry point: Logged Degree-Absorbing Macaulay Cascade on compact fibers (`<= 48` active vars),
/// with logged `Lift-1 / Lift-2 / Lift-3` case-split cube fallback (`pol id0 id1 + 2 d ;`, zero `rup`).
pub fn try_certify_guarded_binom_macaulay(
    fiber_clean: &[(Vec<i32>, usize)],
    guard_lits: &[i32],
    cut_set: &HashSet<i32>,
    logger: &mut VeriPBLogger,
    next_var: &mut i32,
) -> Option<(usize, usize)> {
    if let Some(res) = try_certify_guarded_binom_macaulay_single(
        fiber_clean,
        guard_lits,
        cut_set,
        logger,
        next_var,
    ) {
        return Some(res);
    }

    // Collect active variables and rank by (distinct-support frequency, clause frequency)
    let mut supp_sets: HashMap<i32, HashSet<Vec<i32>>> = HashMap::new();
    let mut cl_freq: HashMap<i32, usize> = HashMap::new();
    for (cl, _) in fiber_clean {
        let mut supp: Vec<i32> = cl.iter().map(|x| x.abs()).collect();
        supp.sort_unstable();
        supp.dedup();
        for &v in &supp {
            *cl_freq.entry(v).or_insert(0) += 1;
            supp_sets.entry(v).or_default().insert(supp.clone());
        }
    }
    let n_active = cl_freq.len();
    if n_active < 4 || n_active > 48 {
        return None;
    }

    let mut ranked_vars: Vec<i32> = cl_freq.keys().copied().collect();
    ranked_vars.sort_by_key(|&v| {
        (
            std::cmp::Reverse(supp_sets.get(&v).map_or(0, |s| s.len())),
            std::cmp::Reverse(cl_freq[&v]),
            v,
        )
    });

    let max_b = if n_active <= 32 { 3usize } else { 2usize };
    for b in 1..=max_b.min(ranked_vars.len()) {
        let branch_vars = &ranked_vars[..b];
        let mut branch_cut_set = cut_set.clone();
        for &bv in branch_vars {
            branch_cut_set.insert(bv);
        }

        let n_branches = 1usize << b;
        let mut branch_cids = vec![0usize; n_branches];
        let mut max_deg = 3usize;
        let mut all_ok = true;

        for b_mask in 0..n_branches {
            let mut b_guard = guard_lits.to_vec();
            let mut sat_lits: HashSet<i32> = HashSet::with_capacity(b);
            for (q, &bv) in branch_vars.iter().enumerate() {
                let bit = (b_mask >> q) & 1;
                if bit == 1 {
                    b_guard.push(-bv);
                    sat_lits.insert(bv);
                } else {
                    b_guard.push(bv);
                    sat_lits.insert(-bv);
                }
            }

            let mut proj_raw: Vec<(Vec<i32>, usize)> = Vec::with_capacity(fiber_clean.len());
            let mut direct_cid: Option<usize> = None;
            for (cl, cid) in fiber_clean {
                if cl.iter().any(|x| sat_lits.contains(x)) {
                    continue;
                }
                let mut present_g: HashSet<i32> = guard_lits.iter().copied().collect();
                let mut core: Vec<i32> = Vec::with_capacity(cl.len());
                for &x in cl {
                    if branch_cut_set.contains(&x.abs()) {
                        present_g.insert(x);
                    } else {
                        core.push(x);
                    }
                }
                let u_cid = ensure_uniform_guard(*cid, &present_g, &b_guard, logger);
                if core.is_empty() {
                    direct_cid = Some(u_cid);
                    break;
                }
                proj_raw.push((core, u_cid));
            }
            if let Some(dcid) = direct_cid {
                branch_cids[b_mask] = dcid;
                continue;
            }

            let re_items: Vec<(Vec<i32>, usize)> = proj_raw
                .into_iter()
                .map(|(core, u_cid)| {
                    let mut full = b_guard.clone();
                    full.extend_from_slice(&core);
                    full.sort_by_key(|&z| (z.abs(), z));
                    (full, u_cid)
                })
                .collect();
            let re_unrolled = unroll_11_chains_logged(&re_items, logger, &branch_cut_set);

            let mut branch_clean: Vec<(Vec<i32>, usize)> = Vec::with_capacity(re_unrolled.len());
            let mut hit_empty: Option<usize> = None;
            for (full_cl, f_cid) in re_unrolled {
                let present_g: HashSet<i32> = full_cl
                    .iter()
                    .copied()
                    .filter(|x| branch_cut_set.contains(&x.abs()))
                    .collect();
                let core: Vec<i32> = full_cl
                    .iter()
                    .copied()
                    .filter(|x| !branch_cut_set.contains(&x.abs()))
                    .collect();
                let u_cid = ensure_uniform_guard(f_cid, &present_g, &b_guard, logger);
                if core.is_empty() {
                    hit_empty = Some(u_cid);
                    break;
                }
                branch_clean.push((core, u_cid));
            }
            if let Some(hcid) = hit_empty {
                branch_cids[b_mask] = hcid;
                continue;
            }

            if let Some(php_cid) = try_certify_guarded_php(&branch_clean, &b_guard, logger) {
                branch_cids[b_mask] = php_cid;
                continue;
            }
            if let Some((v_cid, deg_u)) =
                try_certify_guarded_veronese_rm_d(&branch_clean, &b_guard, logger, next_var, 4, 8)
            {
                max_deg = max_deg.max(deg_u);
                branch_cids[b_mask] = v_cid;
                continue;
            }
            if let Some((m_cid, deg_u)) = try_certify_guarded_binom_macaulay_single(
                &branch_clean,
                &b_guard,
                &branch_cut_set,
                logger,
                next_var,
            ) {
                max_deg = max_deg.max(deg_u);
                branch_cids[b_mask] = m_cid;
                continue;
            }

            all_ok = false;
            break;
        }

        if all_ok {
            let merged_cid = collapse_clause_cube(b, &branch_cids, logger);
            return Some((merged_cid, max_deg));
        }
    }

    None
}
