//! ATAQUE-01: Local-Intersection Zassenhaus + Directional Derivative `dP/du == 1`
//! + Logged Ray Rewriting (`pol` + `red`, zero `rup`).
//!
//! Recovers atomic linear (`deg = 1`) and quadratic (`deg = 2`) lifted rays from wide CNF blocks
//! (`4 <= k <= 12`), allocates shared `VeriPB` `red` monomial witnesses and chained 2-XOR ray wires,
//! rewrites covered blocks into ray clauses via `collapse_clause_cube`, unrolls split ALO chains,
//! and refutes the lifted core via guarded PHP or guarded Veronese `RM(d, n)`.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::{
    collapse_clause_cube, ensure_uniform_guard, try_certify_guarded_php,
    try_certify_guarded_veronese_rm_d, unroll_11_chains_logged, weaken_clause_to_target,
    VeriPBLogger,
};

struct WideBlock {
    supp: Vec<i32>,
    k: usize,
    n_words: usize,
    bad_mask: Vec<u64>,
    forbid_map: Vec<Option<(usize, HashSet<i32>)>>,
}

struct CandidateBlock {
    blk_idx: usize,
    u_basis: Vec<u128>, // basis of U_B in RM_+(deg_d, supp)
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct RayPoly {
    mons: Vec<Vec<i32>>, // sorted list of sorted monomials (len 1 or 2)
    vars: Vec<i32>,      // sorted unique variables appearing in mons
}

struct AllocatedRay {
    wire: i32,
    higher_mons: Vec<Vec<i32>>,
    steps: Vec<(i32, i32, i32, usize, usize, usize, usize)>,
}

#[inline]
fn mask_last_word(full_cube: usize) -> u64 {
    let rem = full_cube & 63;
    if rem == 0 {
        u64::MAX
    } else {
        (1u64 << rem) - 1
    }
}

#[inline]
fn bitset_is_zero(a: &[u64]) -> bool {
    a.iter().all(|&w| w == 0)
}

#[inline]
fn bitset_popcount(a: &[u64]) -> u32 {
    a.iter().map(|&w| w.count_ones()).sum()
}

#[inline]
fn bitset_first_set(a: &[u64]) -> Option<usize> {
    for (wi, &w) in a.iter().enumerate() {
        if w != 0 {
            return Some(wi * 64 + (w.trailing_zeros() as usize));
        }
    }
    None
}

#[inline]
fn bitset_get(a: &[u64], bit: usize) -> bool {
    ((a[bit >> 6] >> (bit & 63)) & 1) == 1
}

#[inline]
fn bitset_and_not_is_zero(a: &[u64], b: &[u64]) -> bool {
    a.iter().zip(b.iter()).all(|(&x, &y)| (x & !y) == 0)
}

#[inline]
fn bitset_and2_not_is_zero(a: &[u64], b: &[u64], c: &[u64]) -> bool {
    a.iter()
        .zip(b.iter())
        .zip(c.iter())
        .all(|((&x, &y), &z)| ((x & y) & !z) == 0)
}

#[inline]
fn bitset_and2_is_zero(a: &[u64], b: &[u64]) -> bool {
    a.iter().zip(b.iter()).all(|(&x, &y)| (x & y) == 0)
}

/// Build the homogeneous monomial list `RM_+(deg_d, 0..k)`:
/// indices `0..k` are degree-1 `(i, usize::MAX)`, followed by degree-2 `(i, j)` for `i < j`.
fn build_rm_plus_mons(k: usize, deg_d: usize) -> Vec<(usize, usize)> {
    let mut mons = Vec::with_capacity(k + if deg_d >= 2 { k * (k.saturating_sub(1)) / 2 } else { 0 });
    for i in 0..k {
        mons.push((i, usize::MAX));
    }
    if deg_d >= 2 {
        for i in 0..k {
            for j in (i + 1)..k {
                mons.push((i, j));
            }
        }
    }
    mons
}

fn eval_mon_at(mon: (usize, usize), mask: usize) -> u8 {
    let b0 = ((mask >> mon.0) & 1) as u8;
    if mon.1 == usize::MAX {
        b0
    } else {
        b0 & (((mask >> mon.1) & 1) as u8)
    }
}

fn build_mon_tts(k: usize, mons: &[(usize, usize)]) -> Vec<Vec<u64>> {
    let full_cube = 1usize << k;
    let n_words = (full_cube + 63) / 64;
    let mut var_tts: Vec<Vec<u64>> = vec![vec![0u64; n_words]; k];
    for m in 0..full_cube {
        let w = m >> 6;
        let b = 1u64 << (m & 63);
        for j in 0..k {
            if ((m >> j) & 1) == 1 {
                var_tts[j][w] |= b;
            }
        }
    }
    let mut mon_tts: Vec<Vec<u64>> = Vec::with_capacity(mons.len());
    for &(a, b) in mons {
        if b == usize::MAX {
            mon_tts.push(var_tts[a].clone());
        } else {
            let mut tt = vec![0u64; n_words];
            for w in 0..n_words {
                tt[w] = var_tts[a][w] & var_tts[b][w];
            }
            mon_tts.push(tt);
        }
    }
    mon_tts
}

/// Compute the homogeneous dual annihilator `U_B` (polynomials in `RM_+(deg_d, supp)` constant on `bad_mask`),
/// and verify that `locus(U_B) == bad_mask`.
fn compute_dual_annihilator_if_exact(blk: &WideBlock, deg_d: usize) -> Option<Vec<u128>> {
    let k = blk.k;
    let mons = build_rm_plus_mons(k, deg_d);
    let dim = mons.len();
    if dim > 128 {
        return None;
    }

    let m0 = bitset_first_set(&blk.bad_mask)?;
    let mut base_eval = 0u128;
    for (idx, &mon) in mons.iter().enumerate() {
        if eval_mon_at(mon, m0) == 1 {
            base_eval |= 1u128 << idx;
        }
    }

    // RREF over GF(2) on columns 0..dim
    let mut piv_row: Vec<u128> = vec![0u128; dim];
    let mut has_piv: Vec<bool> = vec![false; dim];

    let full_cube = 1usize << k;
    for wi in 0..blk.n_words {
        let mut w = blk.bad_mask[wi];
        while w != 0 {
            let bit = w.trailing_zeros() as usize;
            let m = (wi << 6) | bit;
            w &= w - 1;
            if m == m0 || m >= full_cube {
                continue;
            }
            let mut row = 0u128;
            for (idx, &mon) in mons.iter().enumerate() {
                if eval_mon_at(mon, m) == 1 {
                    row |= 1u128 << idx;
                }
            }
            row ^= base_eval;

            while row != 0 {
                let col = row.trailing_zeros() as usize;
                if has_piv[col] {
                    row ^= piv_row[col];
                } else {
                    // Eliminate any existing higher pivots from `row` so `piv_row` stays in full RREF
                    let mut tmp = row & !(1u128 << col);
                    while tmp != 0 {
                        let pc = tmp.trailing_zeros() as usize;
                        tmp &= tmp - 1;
                        if has_piv[pc] {
                            row ^= piv_row[pc];
                        }
                    }
                    // Back-substitute into existing pivots
                    for pc in 0..dim {
                        if has_piv[pc] && ((piv_row[pc] >> col) & 1) == 1 {
                            piv_row[pc] ^= row;
                        }
                    }
                    piv_row[col] = row;
                    has_piv[col] = true;
                    break;
                }
            }
        }
    }

    let mut u_basis: Vec<u128> = Vec::new();
    for free_c in 0..dim {
        if !has_piv[free_c] {
            let mut vec = 1u128 << free_c;
            for pc in 0..dim {
                if has_piv[pc] && ((piv_row[pc] >> free_c) & 1) == 1 {
                    vec |= 1u128 << pc;
                }
            }
            u_basis.push(vec);
        }
    }

    if u_basis.is_empty() {
        return None;
    }

    // Verify locus(U_B) == bad_mask
    let mon_tts = build_mon_tts(k, &mons);
    let last_m = mask_last_word(full_cube);
    let mut locus = vec![u64::MAX; blk.n_words];
    locus[blk.n_words - 1] = last_m;

    let mut tt_p = vec![0u64; blk.n_words];
    for &poly in &u_basis {
        for x in &mut tt_p {
            *x = 0;
        }
        let mut tmp = poly;
        while tmp != 0 {
            let idx = tmp.trailing_zeros() as usize;
            tmp &= tmp - 1;
            for w in 0..blk.n_words {
                tt_p[w] ^= mon_tts[idx][w];
            }
        }
        let val_m0 = bitset_get(&tt_p, m0);
        if val_m0 {
            for w in 0..blk.n_words {
                locus[w] &= tt_p[w];
            }
        } else {
            for w in 0..blk.n_words {
                locus[w] &= !tt_p[w];
            }
        }
        locus[blk.n_words - 1] &= last_m;
    }

    if locus == blk.bad_mask {
        Some(u_basis)
    } else {
        None
    }
}

/// Project subspace `u_basis` from `RM_+(deg_d, supp)` down to `RM_+(deg_d, s_inter)`.
fn project_subspace_to_inter(
    u_basis: &[u128],
    supp: &[i32],
    s_inter: &[i32],
    deg_d: usize,
) -> Vec<u128> {
    let k_s = supp.len();
    let k_i = s_inter.len();
    let mons_s = build_rm_plus_mons(k_s, deg_d);
    let mons_i = build_rm_plus_mons(k_i, deg_d);

    let mut var_to_inter: Vec<Option<usize>> = vec![None; k_s];
    for (p_s, &v) in supp.iter().enumerate() {
        if let Ok(p_i) = s_inter.binary_search(&v) {
            var_to_inter[p_s] = Some(p_i);
        }
    }

    let mut mon_i_map: HashMap<(usize, usize), usize> = HashMap::with_capacity(mons_i.len());
    for (idx, &m) in mons_i.iter().enumerate() {
        mon_i_map.insert(m, idx);
    }

    let mut out_mask = 0u128;
    let mut s_to_i: Vec<Option<usize>> = vec![None; mons_s.len()];
    for (idx, &(a, b)) in mons_s.iter().enumerate() {
        let mapped = if b == usize::MAX {
            var_to_inter[a].map(|ia| mon_i_map[&(ia, usize::MAX)])
        } else {
            match (var_to_inter[a], var_to_inter[b]) {
                (Some(ia), Some(ib)) => {
                    let pair = if ia < ib { (ia, ib) } else { (ib, ia) };
                    Some(mon_i_map[&pair])
                }
                _ => None,
            }
        };
        if let Some(mi) = mapped {
            s_to_i[idx] = Some(mi);
        } else {
            out_mask |= 1u128 << idx;
        }
    }

    // Eliminate OUT coordinates first
    let mut piv_out: HashMap<usize, u128> = HashMap::new();
    let mut proj_in: Vec<u128> = Vec::new();

    for &vec_orig in u_basis {
        let mut v = vec_orig;
        while (v & out_mask) != 0 {
            let col = (v & out_mask).trailing_zeros() as usize;
            if let Some(&pv) = piv_out.get(&col) {
                v ^= pv;
            } else {
                piv_out.insert(col, v);
                v = 0;
                break;
            }
        }
        if v != 0 {
            let mut v_i = 0u128;
            let mut tmp = v;
            while tmp != 0 {
                let idx = tmp.trailing_zeros() as usize;
                tmp &= tmp - 1;
                if let Some(mi) = s_to_i[idx] {
                    v_i |= 1u128 << mi;
                }
            }
            if v_i != 0 {
                proj_in.push(v_i);
            }
        }
    }

    proj_in
}

/// Zassenhaus intersection of two GF(2) subspaces in `u128`.
fn zassenhaus_intersect(a: &[u128], b: &[u128]) -> Vec<u128> {
    let mut piv_first: HashMap<usize, (u128, u128)> = HashMap::new();
    let mut inter_pivs: HashMap<usize, u128> = HashMap::new();
    let mut inter_basis: Vec<u128> = Vec::new();

    let mut insert_pair = |mut x: u128, mut y: u128| {
        while x != 0 {
            let col = x.trailing_zeros() as usize;
            if let Some(&(px, py)) = piv_first.get(&col) {
                x ^= px;
                y ^= py;
            } else {
                piv_first.insert(col, (x, y));
                return;
            }
        }
        while y != 0 {
            let col = y.trailing_zeros() as usize;
            if let Some(&py) = inter_pivs.get(&col) {
                y ^= py;
            } else {
                inter_pivs.insert(col, y);
                inter_basis.push(y);
                return;
            }
        }
    };

    for &v in a {
        if v != 0 {
            insert_pair(v, v);
        }
    }
    for &w in b {
        if w != 0 {
            insert_pair(w, 0);
        }
    }
    inter_basis
}

fn poly_u128_to_ray(poly: u128, s_inter: &[i32], mons_inter: &[(usize, usize)]) -> Option<RayPoly> {
    if poly == 0 {
        return None;
    }
    let mut mons: Vec<Vec<i32>> = Vec::new();
    let mut var_set: BTreeSet<i32> = BTreeSet::new();
    let mut tmp = poly;
    while tmp != 0 {
        let idx = tmp.trailing_zeros() as usize;
        tmp &= tmp - 1;
        let (a, b) = mons_inter[idx];
        if b == usize::MAX {
            let va = s_inter[a];
            var_set.insert(va);
            mons.push(vec![va]);
        } else {
            let va = s_inter[a];
            let vb = s_inter[b];
            var_set.insert(va);
            var_set.insert(vb);
            mons.push(if va < vb { vec![va, vb] } else { vec![vb, va] });
        }
    }
    if var_set.len() < 2 {
        return None;
    }
    mons.sort();
    let vars: Vec<i32> = var_set.into_iter().collect();
    Some(RayPoly { mons, vars })
}

fn is_poly_balanced(poly: u128, k_inter: usize, mons_inter: &[(usize, usize)]) -> bool {
    if poly == 0 {
        return false;
    }
    // Fast path: if any variable appears linearly and in NO degree-2 monomial, dP/du == 1 => balanced!
    let mut quad_vars = 0u32;
    let mut used_vars = 0u32;
    let mut tmp = poly;
    while tmp != 0 {
        let idx = tmp.trailing_zeros() as usize;
        tmp &= tmp - 1;
        let (a, b) = mons_inter[idx];
        used_vars |= 1u32 << a;
        if b != usize::MAX {
            used_vars |= 1u32 << b;
            quad_vars |= (1u32 << a) | (1u32 << b);
        }
    }
    let lin_mask = (poly & ((1u128 << k_inter) - 1)) as u32;
    if (lin_mask & !quad_vars) != 0 {
        return true;
    }

    // General check on active variables of `poly`
    let mut act_vars: Vec<usize> = Vec::new();
    for j in 0..k_inter {
        if ((used_vars >> j) & 1) == 1 {
            act_vars.push(j);
        }
    }
    let kv = act_vars.len();
    if kv == 0 || kv > 12 {
        return false;
    }
    let mut var_pos = [0usize; 16];
    for (p, &orig) in act_vars.iter().enumerate() {
        var_pos[orig] = p;
    }
    let mut active_mons: Vec<(usize, usize)> = Vec::new();
    let mut tmp2 = poly;
    while tmp2 != 0 {
        let idx = tmp2.trailing_zeros() as usize;
        tmp2 &= tmp2 - 1;
        let (a, b) = mons_inter[idx];
        if b == usize::MAX {
            active_mons.push((var_pos[a], usize::MAX));
        } else {
            active_mons.push((var_pos[a], var_pos[b]));
        }
    }

    let full = 1usize << kv;
    let mut ones = 0usize;
    for m in 0..full {
        let mut val = 0u8;
        for &(a, b) in &active_mons {
            val ^= if b == usize::MAX {
                ((m >> a) & 1) as u8
            } else {
                (((m >> a) & 1) & ((m >> b) & 1)) as u8
            };
        }
        ones += val as usize;
    }
    ones == (full >> 1)
}

/// Filter candidate rays (`|vars| >= 2`) to atomic rays: not in the GF(2) span of strictly fewer-variable rays.
fn filter_atomic_rays(cand_rays: HashSet<RayPoly>) -> Vec<RayPoly> {
    let mut by_size: BTreeMap<usize, Vec<RayPoly>> = BTreeMap::new();
    for r in cand_rays {
        by_size.entry(r.vars.len()).or_default().push(r);
    }

    let mut mon_to_id: HashMap<Vec<i32>, usize> = HashMap::new();
    let mut get_mon_id = |m: &Vec<i32>| -> usize {
        if let Some(&id) = mon_to_id.get(m) {
            id
        } else {
            let id = mon_to_id.len() + 1;
            mon_to_id.insert(m.clone(), id);
            id
        }
    };

    let mut basis: HashMap<usize, BTreeSet<usize>> = HashMap::new();
    let mut atomic: Vec<RayPoly> = Vec::new();

    for (_sz, mut group) in by_size {
        group.sort();
        let mut accepted_rows: Vec<BTreeSet<usize>> = Vec::new();
        for ray in group {
            let mut row: BTreeSet<usize> = BTreeSet::new();
            for m in &ray.mons {
                let id = get_mon_id(m);
                if !row.remove(&id) {
                    row.insert(id);
                }
            }
            let mut reduced = row.clone();
            while let Some(&lead) = reduced.iter().next_back() {
                if let Some(prow) = basis.get(&lead) {
                    for &pc in prow {
                        if !reduced.remove(&pc) {
                            reduced.insert(pc);
                        }
                    }
                } else {
                    break;
                }
            }
            if !reduced.is_empty() {
                atomic.push(ray);
                accepted_rows.push(row);
            }
        }
        // Insert accepted rays of this size into the basis for strictly larger sizes
        for mut row in accepted_rows {
            while let Some(&lead) = row.iter().next_back() {
                if let Some(prow) = basis.get(&lead) {
                    for &pc in prow {
                        if !row.remove(&pc) {
                            row.insert(pc);
                        }
                    }
                } else {
                    basis.insert(lead, row);
                    break;
                }
            }
        }
    }

    atomic
}

/// Evaluate a ray polynomial on `0..(1 << k)` for a block `supp`.
fn eval_ray_tt_on_supp(ray: &RayPoly, supp: &[i32], n_words: usize) -> Vec<u64> {
    let k = supp.len();
    let full_cube = 1usize << k;
    let mut pos_mons: Vec<(usize, usize)> = Vec::with_capacity(ray.mons.len());
    for m in &ray.mons {
        let p0 = supp.binary_search(&m[0]).unwrap();
        if m.len() == 1 {
            pos_mons.push((p0, usize::MAX));
        } else {
            let p1 = supp.binary_search(&m[1]).unwrap();
            pos_mons.push((p0, p1));
        }
    }
    let mut tt = vec![0u64; n_words];
    for mask in 0..full_cube {
        let mut val = 0u8;
        for &(a, b) in &pos_mons {
            val ^= if b == usize::MAX {
                ((mask >> a) & 1) as u8
            } else {
                (((mask >> a) & 1) & ((mask >> b) & 1)) as u8
            };
        }
        if val == 1 {
            tt[mask >> 6] |= 1u64 << (mask & 63);
        }
    }
    tt
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum RayLit {
    Var(i32),            // signed original variable literal
    Ray(usize, bool),    // (ray_idx in atomic_rays, is_positive)
}

impl RayLit {
    fn base_key(self) -> (bool, usize) {
        match self {
            RayLit::Var(l) => (false, l.abs() as usize),
            RayLit::Ray(idx, _) => (true, idx),
        }
    }
}

/// Extract ray clauses covering `blk.bad_mask` from available atomic rays `⊆ supp` + singletons.
/// Returns `(extracted_clauses, fully_covered)`.
fn extract_ray_clauses_for_block(
    blk: &WideBlock,
    atomic_rays: &[RayPoly],
    matching_ray_idxs: &[usize],
) -> (Vec<Vec<RayLit>>, bool) {
    let k = blk.k;
    let full_cube = 1usize << k;
    let n_words = blk.n_words;
    let last_m = mask_last_word(full_cube);

    // Build (RayLit, bad_when_false) for all matching atomic rays and all singletons
    let mut lits_info: Vec<(RayLit, Vec<u64>)> =
        Vec::with_capacity((matching_ray_idxs.len() + k) * 2);

    for &r_idx in matching_ray_idxs {
        let tt = eval_ray_tt_on_supp(&atomic_rays[r_idx], &blk.supp, n_words);
        let mut neg_tt = vec![0u64; n_words];
        for w in 0..n_words {
            neg_tt[w] = !tt[w];
        }
        neg_tt[n_words - 1] &= last_m;
        // +w_R is FALSE when tt == 0 (neg_tt)
        lits_info.push((RayLit::Ray(r_idx, true), neg_tt));
        // -w_R is FALSE when tt == 1 (tt)
        lits_info.push((RayLit::Ray(r_idx, false), tt));
    }

    for (j, &v) in blk.supp.iter().enumerate() {
        let mut tt = vec![0u64; n_words];
        for mask in 0..full_cube {
            if ((mask >> j) & 1) == 1 {
                tt[mask >> 6] |= 1u64 << (mask & 63);
            }
        }
        let mut neg_tt = vec![0u64; n_words];
        for w in 0..n_words {
            neg_tt[w] = !tt[w];
        }
        neg_tt[n_words - 1] &= last_m;
        lits_info.push((RayLit::Var(v), neg_tt));
        lits_info.push((RayLit::Var(-v), tt));
    }

    let mut extracted: Vec<Vec<RayLit>> = Vec::new();
    let mut union_cov = vec![0u64; n_words];

    // (a) Width-1 ray clauses
    let mut unit_keys: HashSet<(bool, usize)> = HashSet::new();
    for (rlit, bm) in &lits_info {
        if !bitset_is_zero(bm) && bitset_and_not_is_zero(bm, &blk.bad_mask) {
            extracted.push(vec![*rlit]);
            unit_keys.insert(rlit.base_key());
            for w in 0..n_words {
                union_cov[w] |= bm[w];
            }
        }
    }

    // (b) Width-2 ray clauses
    let n_lits = lits_info.len();
    for i in 0..n_lits {
        let (l1, ref b1) = lits_info[i];
        let k1 = l1.base_key();
        if unit_keys.contains(&k1) {
            continue;
        }
        for j in (i + 1)..n_lits {
            let (l2, ref b2) = lits_info[j];
            let k2 = l2.base_key();
            if k1 == k2 || unit_keys.contains(&k2) {
                continue;
            }
            if !bitset_and2_is_zero(b1, b2) && bitset_and2_not_is_zero(b1, b2, &blk.bad_mask) {
                extracted.push(vec![l1, l2]);
                for w in 0..n_words {
                    union_cov[w] |= b1[w] & b2[w];
                }
            }
        }
    }

    // (c) Greedy higher-width ray clauses to cover any remaining bad bits
    for _step in 0..64 {
        if union_cov == blk.bad_mask {
            break;
        }
        let mut rem_bad = vec![0u64; n_words];
        for w in 0..n_words {
            rem_bad[w] = blk.bad_mask[w] & !union_cov[w];
        }
        if bitset_is_zero(&rem_bad) {
            break;
        }

        // Helper to greedily cover a target bitset `target_req` (either all of rem_bad, or a single uncovered bit)
        let try_greedy = |target_req: &[u64]| -> Option<(Vec<RayLit>, Vec<u64>)> {
            let mut cur = vec![u64::MAX; n_words];
            cur[n_words - 1] = last_m;
            let mut chosen: Vec<RayLit> = Vec::new();
            let mut used_keys: HashSet<(bool, usize)> = HashSet::new();

            for _ in 0..12 {
                if bitset_and_not_is_zero(&cur, &blk.bad_mask) {
                    return Some((chosen, cur));
                }
                let cur_pop = bitset_popcount(&cur);
                let mut best_idx: Option<usize> = None;
                let mut best_pop = cur_pop;

                for (idx, (rlit, bm)) in lits_info.iter().enumerate() {
                    if used_keys.contains(&rlit.base_key()) {
                        continue;
                    }
                    // Must contain target_req: (target_req & !bm) == 0
                    if !bitset_and_not_is_zero(target_req, bm) {
                        continue;
                    }
                    let mut new_pop = 0u32;
                    for w in 0..n_words {
                        new_pop += (cur[w] & bm[w]).count_ones();
                    }
                    if new_pop < best_pop {
                        best_pop = new_pop;
                        best_idx = Some(idx);
                    }
                }

                let b_idx = best_idx?;
                let (rlit, ref bm) = lits_info[b_idx];
                for w in 0..n_words {
                    cur[w] &= bm[w];
                }
                chosen.push(rlit);
                used_keys.insert(rlit.base_key());
            }

            if bitset_and_not_is_zero(&cur, &blk.bad_mask) {
                Some((chosen, cur))
            } else {
                None
            }
        };

        let found = try_greedy(&rem_bad).or_else(|| {
            let p0 = bitset_first_set(&rem_bad)?;
            let mut single = vec![0u64; n_words];
            single[p0 >> 6] = 1u64 << (p0 & 63);
            try_greedy(&single)
        });

        if let Some((clause, cov)) = found {
            if !clause.is_empty() && !bitset_is_zero(&cov) {
                extracted.push(clause);
                for w in 0..n_words {
                    union_cov[w] |= cov[w];
                }
            } else {
                break;
            }
        } else {
            break;
        }
    }

    (extracted, union_cov == blk.bad_mask)
}

/// ATAQUE-01 entry point: Local-Intersection Zassenhaus + Derivative `dP/du == 1` + Logged Ray Rewriting.
pub fn try_certify_guarded_lifted_zassenhaus(
    fiber_clean: &[(Vec<i32>, usize)],
    guard_lits: &[i32],
    cut_set: &HashSet<i32>,
    logger: &mut VeriPBLogger,
    next_var: &mut i32,
) -> Option<(usize, usize)> {
    // Group wide supports 4 <= k <= 12
    let mut by_supp: BTreeMap<Vec<i32>, Vec<(usize, Vec<i32>, usize)>> = BTreeMap::new();
    for (cl_idx, (cl, cid)) in fiber_clean.iter().enumerate() {
        let k = cl.len();
        if k >= 4 && k <= 12 {
            let mut supp: Vec<i32> = cl.iter().map(|x| x.abs()).collect();
            supp.sort_unstable();
            supp.dedup();
            if supp.len() == k {
                by_supp
                    .entry(supp)
                    .or_default()
                    .push((cl_idx, cl.clone(), *cid));
            }
        }
    }
    if by_supp.is_empty() {
        return None;
    }

    let guard_set: HashSet<i32> = guard_lits.iter().copied().collect();
    let mut wide_blocks: Vec<WideBlock> = Vec::new();
    let mut block_clause_indices: Vec<Vec<usize>> = Vec::new();

    for (supp, items) in by_supp {
        let k = supp.len();
        let full_cube = 1usize << k;
        let n_words = (full_cube + 63) / 64;
        let mut bad_mask = vec![0u64; n_words];
        let mut forbid_map: Vec<Option<(usize, HashSet<i32>)>> = vec![None; full_cube];
        let mut cl_idxs = Vec::with_capacity(items.len());
        let mut n_bad = 0usize;

        for (cl_idx, cl, cid) in items {
            cl_idxs.push(cl_idx);
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
                bad_mask[mask >> 6] |= 1u64 << (mask & 63);
                n_bad += 1;
            }
        }

        if n_bad >= 2 && n_bad < full_cube {
            wide_blocks.push(WideBlock {
                supp,
                k,
                n_words,
                bad_mask,
                forbid_map,
            });
            block_clause_indices.push(cl_idxs);
        }
    }

    let debug = std::env::var("CAP_DEBUG").is_ok();
    if debug {
        eprintln!(
            "[zassenhaus] fiber_clean={} wide_blocks={}",
            fiber_clean.len(),
            wide_blocks.len()
        );
    }
    if wide_blocks.len() < 2 {
        return None;
    }

    // Shared VeriPB witnesses across deg_d attempts (unconditional `red` definitions)
    let mut monom_witness: HashMap<Vec<i32>, (i32, usize, Vec<usize>)> = HashMap::new();
    let mut ray_witness: HashMap<RayPoly, AllocatedRay> = HashMap::new();
    let mut taut_cache: HashMap<i32, usize> = HashMap::new();

    for deg_d in [1usize, 2usize] {
        let mut cand_blocks: Vec<CandidateBlock> = Vec::new();
        for (blk_idx, blk) in wide_blocks.iter().enumerate() {
            if let Some(u_basis) = compute_dual_annihilator_if_exact(blk, deg_d) {
                cand_blocks.push(CandidateBlock { blk_idx, u_basis });
            }
        }
        if cand_blocks.len() < 2 {
            continue;
        }

        // Inverted index: var -> candidate block indices
        let mut var_to_cands: HashMap<i32, Vec<usize>> = HashMap::new();
        for (ci, cb) in cand_blocks.iter().enumerate() {
            for &v in &wide_blocks[cb.blk_idx].supp {
                var_to_cands.entry(v).or_default().push(ci);
            }
        }

        // Intersect pairs (ci, cj) sharing >= 2 variables
        let mut cand_rays: HashSet<RayPoly> = HashSet::new();
        let mut share_counts: Vec<u16> = vec![0u16; cand_blocks.len()];
        let mut touched_js: Vec<usize> = Vec::new();

        for ci in 0..cand_blocks.len() {
            let blk_i = &wide_blocks[cand_blocks[ci].blk_idx];
            touched_js.clear();
            for &v in &blk_i.supp {
                if let Some(list) = var_to_cands.get(&v) {
                    for &cj in list {
                        if cj > ci {
                            if share_counts[cj] == 0 {
                                touched_js.push(cj);
                            }
                            share_counts[cj] += 1;
                        }
                    }
                }
            }

            for &cj in &touched_js {
                let cnt = share_counts[cj];
                share_counts[cj] = 0;
                if cnt < 2 {
                    continue;
                }
                let blk_j = &wide_blocks[cand_blocks[cj].blk_idx];
                let mut s_inter: Vec<i32> = Vec::with_capacity(cnt as usize);
                for &v in &blk_i.supp {
                    if blk_j.supp.binary_search(&v).is_ok() {
                        s_inter.push(v);
                    }
                }
                if s_inter.len() < 2 || s_inter.len() > 11 {
                    continue;
                }

                let proj_i = project_subspace_to_inter(
                    &cand_blocks[ci].u_basis,
                    &blk_i.supp,
                    &s_inter,
                    deg_d,
                );
                if proj_i.is_empty() {
                    continue;
                }
                let proj_j = project_subspace_to_inter(
                    &cand_blocks[cj].u_basis,
                    &blk_j.supp,
                    &s_inter,
                    deg_d,
                );
                if proj_j.is_empty() {
                    continue;
                }

                let inter = zassenhaus_intersect(&proj_i, &proj_j);
                if inter.is_empty() {
                    continue;
                }

                let k_inter = s_inter.len();
                let mons_inter = build_rm_plus_mons(k_inter, deg_d);

                if inter.len() == 1 {
                    if is_poly_balanced(inter[0], k_inter, &mons_inter) {
                        if let Some(rp) = poly_u128_to_ray(inter[0], &s_inter, &mons_inter) {
                            cand_rays.insert(rp);
                        }
                    }
                } else {
                    // Directional Boolean derivative dP/du == 1 for each u in s_inter
                    for u_pos in 0..k_inter {
                        let mut bad_mask_u = 0u128;
                        if deg_d >= 2 {
                            for (idx, &(a, b)) in mons_inter.iter().enumerate().skip(k_inter) {
                                if a == u_pos || b == u_pos {
                                    bad_mask_u |= 1u128 << idx;
                                }
                            }
                        }

                        // Project `inter` to kernel of `bad_mask_u`
                        let mut piv_bad: HashMap<usize, u128> = HashMap::new();
                        let mut proj_u: Vec<u128> = Vec::new();
                        for &vec_orig in &inter {
                            let mut v = vec_orig;
                            while (v & bad_mask_u) != 0 {
                                let col = (v & bad_mask_u).trailing_zeros() as usize;
                                if let Some(&pv) = piv_bad.get(&col) {
                                    v ^= pv;
                                } else {
                                    piv_bad.insert(col, v);
                                    v = 0;
                                    break;
                                }
                            }
                            if v != 0 {
                                proj_u.push(v);
                            }
                        }
                        if proj_u.is_empty() {
                            continue;
                        }
                        proj_u.sort_by_key(|v| v.count_ones());

                        let u_bit = 1u128 << u_pos;
                        let mut p_base: Option<u128> = None;
                        let mut null_u: Vec<u128> = Vec::new();
                        for v in proj_u {
                            if (v & u_bit) != 0 {
                                if let Some(pb) = p_base {
                                    let diff = v ^ pb;
                                    if diff != 0 {
                                        null_u.push(diff);
                                    }
                                } else {
                                    p_base = Some(v);
                                }
                            } else {
                                null_u.push(v);
                            }
                        }

                        if let Some(pb) = p_base {
                            let n_null = null_u.len().min(4);
                            let n_combs = 1usize << n_null;
                            for c_mask in 0..n_combs.min(16) {
                                let mut cand = pb;
                                for j in 0..n_null {
                                    if ((c_mask >> j) & 1) == 1 {
                                        cand ^= null_u[j];
                                    }
                                }
                                if let Some(rp) = poly_u128_to_ray(cand, &s_inter, &mons_inter) {
                                    cand_rays.insert(rp);
                                }
                            }
                        }
                    }
                }
            }
        }

        if cand_rays.is_empty() {
            continue;
        }

        let n_cand_rays = cand_rays.len();
        let atomic_rays = filter_atomic_rays(cand_rays);
        if atomic_rays.is_empty() {
            continue;
        }

        // Index atomic rays by their first variable for fast subset matching
        let mut var_to_rays: HashMap<i32, Vec<usize>> = HashMap::new();
        for (r_idx, ray) in atomic_rays.iter().enumerate() {
            var_to_rays.entry(ray.vars[0]).or_default().push(r_idx);
        }

        // Extract ray clauses for EVERY wide block (including multi-clause blocks that failed single-locus dual check)
        let mut extracted_per_block: Vec<(usize, Vec<Vec<RayLit>>, bool)> = Vec::new();
        let mut any_extracted = false;

        for (blk_idx, blk) in wide_blocks.iter().enumerate() {
            let mut matching: Vec<usize> = Vec::new();
            for &v in &blk.supp {
                if let Some(rlist) = var_to_rays.get(&v) {
                    for &r_idx in rlist {
                        let rvars = &atomic_rays[r_idx].vars;
                        if rvars.len() <= blk.k
                            && rvars.iter().all(|rv| blk.supp.binary_search(rv).is_ok())
                        {
                            matching.push(r_idx);
                        }
                    }
                }
            }
            if matching.is_empty() {
                continue;
            }
            let (clauses_out, fully_cov) =
                extract_ray_clauses_for_block(blk, &atomic_rays, &matching);
            if !clauses_out.is_empty() {
                any_extracted = true;
                extracted_per_block.push((blk_idx, clauses_out, fully_cov));
            }
        }

        if debug {
            let n_full = extracted_per_block.iter().filter(|x| x.2).count();
            eprintln!(
                "[zassenhaus] deg_d={} cand_blocks={} cand_rays={} atomic_rays={} extracted_blocks={} fully_cov={}",
                deg_d,
                cand_blocks.len(),
                n_cand_rays,
                atomic_rays.len(),
                extracted_per_block.len(),
                n_full
            );
        }
        if !any_extracted {
            continue;
        }

        // Helper to lazily allocate VeriPB `red` witnesses for a ray
        let ensure_ray_allocated = |ray: &RayPoly,
                                    monom_witness: &mut HashMap<Vec<i32>, (i32, usize, Vec<usize>)>,
                                    ray_witness: &mut HashMap<RayPoly, AllocatedRay>,
                                    logger: &mut VeriPBLogger,
                                    next_var: &mut i32| {
            if ray_witness.contains_key(ray) {
                return;
            }
            let mut z_list: Vec<i32> = Vec::with_capacity(ray.mons.len());
            let mut higher_mons: Vec<Vec<i32>> = Vec::new();
            for mon in &ray.mons {
                if mon.len() == 1 {
                    z_list.push(mon[0]);
                } else {
                    higher_mons.push(mon.clone());
                    let p_var = if let Some(&(pv, _, _)) = monom_witness.get(mon) {
                        pv
                    } else {
                        *next_var += 1;
                        let pv = *next_var;
                        let mut terms_all: Vec<(i64, i32)> = Vec::with_capacity(mon.len() + 1);
                        for &u in mon {
                            terms_all.push((1, -u));
                        }
                        terms_all.push((1, pv));
                        let and_all = logger.emit_red(&terms_all, 1, pv, 1);
                        let mut and_0s: Vec<usize> = Vec::with_capacity(mon.len());
                        for &u in mon {
                            let cid0 = logger.emit_red(&[(1, u), (1, -pv)], 1, pv, 0);
                            and_0s.push(cid0);
                        }
                        monom_witness.insert(mon.clone(), (pv, and_all, and_0s));
                        pv
                    };
                    z_list.push(p_var);
                }
            }

            let mut acc_var = z_list[0];
            let mut steps: Vec<(i32, i32, i32, usize, usize, usize, usize)> =
                Vec::with_capacity(z_list.len().saturating_sub(1));
            for &nxt_z in &z_list[1..] {
                *next_var += 1;
                let s_var = *next_var;
                let z_01 = logger.emit_red(&[(1, acc_var), (1, -nxt_z), (1, s_var)], 1, s_var, 1);
                let z_10 = logger.emit_red(&[(1, -acc_var), (1, nxt_z), (1, s_var)], 1, s_var, 1);
                let z_00 = logger.emit_red(&[(1, acc_var), (1, nxt_z), (1, -s_var)], 1, s_var, 0);
                let z_11 = logger.emit_red(&[(1, -acc_var), (1, -nxt_z), (1, -s_var)], 1, s_var, 0);
                steps.push((acc_var, nxt_z, s_var, z_00, z_01, z_10, z_11));
                acc_var = s_var;
            }

            ray_witness.insert(
                ray.clone(),
                AllocatedRay {
                    wire: acc_var,
                    higher_mons,
                    steps,
                },
            );
        };

        // Derive every extracted ray clause via `collapse_clause_cube` (zero `rup`!)
        let mut derived_ray_clauses: Vec<(Vec<i32>, usize)> = Vec::new();
        let mut replaced_clause_idxs: HashSet<usize> = HashSet::new();

        for (blk_idx, clauses_out, fully_cov) in &extracted_per_block {
            let blk = &wide_blocks[*blk_idx];
            let k = blk.k;
            let full_cube = 1usize << k;
            let supp_set: HashSet<i32> = blk.supp.iter().copied().collect();

            if *fully_cov {
                for &orig_idx in &block_clause_indices[*blk_idx] {
                    replaced_clause_idxs.insert(orig_idx);
                }
            }

            for r_clause in clauses_out {
                // Allocate any rays used in this clause and build concrete literal list
                let mut concrete_lits: Vec<i32> = Vec::with_capacity(r_clause.len());
                for &rl in r_clause {
                    match rl {
                        RayLit::Var(l) => concrete_lits.push(l),
                        RayLit::Ray(r_idx, is_pos) => {
                            let ray = &atomic_rays[r_idx];
                            ensure_ray_allocated(
                                ray,
                                &mut monom_witness,
                                &mut ray_witness,
                                logger,
                                next_var,
                            );
                            let w_var = ray_witness[ray].wire;
                            concrete_lits.push(if is_pos { w_var } else { -w_var });
                        }
                    }
                }

                let mut leaves = vec![0usize; full_cube];
                for mask in 0..full_cube {
                    let mut full_target = Vec::with_capacity(guard_lits.len() + k + concrete_lits.len());
                    full_target.extend_from_slice(guard_lits);
                    for q in 0..k {
                        full_target.push(if ((mask >> q) & 1) == 1 {
                            -blk.supp[q]
                        } else {
                            blk.supp[q]
                        });
                    }
                    full_target.extend_from_slice(&concrete_lits);

                    if let Some((base_cid, ref pres)) = blk.forbid_map[mask] {
                        leaves[mask] = weaken_clause_to_target(base_cid, pres, &full_target, logger);
                        continue;
                    }

                    // Satisfying point: find a literal in `r_clause` that evaluates to TRUE on `mask`
                    let mut leaf_cid: Option<usize> = None;
                    for &rl in r_clause {
                        match rl {
                            RayLit::Var(l) => {
                                let pos = blk.supp.binary_search(&l.abs()).unwrap();
                                let bit = ((mask >> pos) & 1) as u8;
                                let is_true = if l > 0 { bit == 1 } else { bit == 0 };
                                if is_true {
                                    let v = l.abs();
                                    let tid = *taut_cache.entry(v).or_insert_with(|| {
                                        logger.emit_pol_raw(&format!("x{} ~x{} + 2 d", v, v))
                                    });
                                    let pres: HashSet<i32> = [v, -v].into_iter().collect();
                                    leaf_cid = Some(weaken_clause_to_target(
                                        tid,
                                        &pres,
                                        &full_target,
                                        logger,
                                    ));
                                    break;
                                }
                            }
                            RayLit::Ray(r_idx, is_pos) => {
                                let ray = &atomic_rays[r_idx];
                                let mut rval = 0u8;
                                for mon in &ray.mons {
                                    let mut mv = 1u8;
                                    for &u in mon {
                                        let pos = blk.supp.binary_search(&u).unwrap();
                                        mv &= ((mask >> pos) & 1) as u8;
                                    }
                                    rval ^= mv;
                                }
                                let is_true = if is_pos { rval == 1 } else { rval == 0 };
                                if is_true {
                                    let alloc = &ray_witness[ray];
                                    let mut val_of: HashMap<i32, u8> =
                                        HashMap::with_capacity(k + alloc.higher_mons.len() + alloc.steps.len());
                                    for q in 0..k {
                                        val_of.insert(blk.supp[q], ((mask >> q) & 1) as u8);
                                    }
                                    let mut derived_unit: HashMap<i32, (usize, HashSet<i32>)> =
                                        HashMap::with_capacity(
                                            alloc.higher_mons.len() + alloc.steps.len(),
                                        );

                                    for mon in &alloc.higher_mons {
                                        let (p_var, and_all, ref and_0s) = monom_witness[mon];
                                        if let Some((j0, &u0)) = mon
                                            .iter()
                                            .enumerate()
                                            .find(|&(_, &u)| val_of[&u] == 0)
                                        {
                                            val_of.insert(p_var, 0);
                                            let supp_u: HashSet<i32> =
                                                [u0, -p_var].into_iter().collect();
                                            derived_unit.insert(p_var, (and_0s[j0], supp_u));
                                        } else {
                                            val_of.insert(p_var, 1);
                                            let mut supp_all: HashSet<i32> =
                                                mon.iter().map(|&u| -u).collect();
                                            supp_all.insert(p_var);
                                            derived_unit.insert(p_var, (and_all, supp_all));
                                        }
                                    }

                                    for &(v1, v2, s_var, z_00, z_01, z_10, z_11) in &alloc.steps {
                                        let b1 = val_of[&v1];
                                        let b2 = val_of[&v2];
                                        let bs = b1 ^ b2;
                                        val_of.insert(s_var, bs);
                                        let lit1_u = if b1 == 1 { v1 } else { -v1 };
                                        let lit2_u = if b2 == 1 { v2 } else { -v2 };
                                        let s_lit = if bs == 1 { s_var } else { -s_var };

                                        let mut cur_cid = match (b1, b2) {
                                            (0, 0) => z_00,
                                            (0, 1) => z_01,
                                            (1, 0) => z_10,
                                            _ => z_11,
                                        };
                                        let mut cur_supp: HashSet<i32> =
                                            [-lit1_u, -lit2_u, s_lit].into_iter().collect();

                                        if !supp_set.contains(&v1) {
                                            let (c1, ref s1) = derived_unit[&v1];
                                            cur_supp.remove(&(-lit1_u));
                                            let overlap =
                                                s1.iter().any(|&x| x != lit1_u && cur_supp.contains(&x));
                                            cur_cid = logger.emit_pol_add2(cur_cid, c1, overlap);
                                            for &x in s1 {
                                                if x != lit1_u {
                                                    cur_supp.insert(x);
                                                }
                                            }
                                        }
                                        if !supp_set.contains(&v2) {
                                            let (c2, ref s2) = derived_unit[&v2];
                                            cur_supp.remove(&(-lit2_u));
                                            let overlap =
                                                s2.iter().any(|&x| x != lit2_u && cur_supp.contains(&x));
                                            cur_cid = logger.emit_pol_add2(cur_cid, c2, overlap);
                                            for &x in s2 {
                                                if x != lit2_u {
                                                    cur_supp.insert(x);
                                                }
                                            }
                                        }
                                        derived_unit.insert(s_var, (cur_cid, cur_supp));
                                    }

                                    let (dcid, ref dsupp) = derived_unit[&alloc.wire];
                                    leaf_cid = Some(weaken_clause_to_target(
                                        dcid,
                                        dsupp,
                                        &full_target,
                                        logger,
                                    ));
                                    break;
                                }
                            }
                        }
                    }

                    leaves[mask] = leaf_cid.expect("Allowed point violated extracted ray clause");
                }

                let rc_cid = collapse_clause_cube(k, &leaves, logger);
                derived_ray_clauses.push((concrete_lits, rc_cid));
            }
        }

        if derived_ray_clauses.is_empty() {
            continue;
        }

        // Build rewritten fiber: keep non-replaced clauses + derived ray clauses
        let mut rewritten: Vec<(Vec<i32>, usize)> =
            Vec::with_capacity(fiber_clean.len() - replaced_clause_idxs.len() + derived_ray_clauses.len());
        for (idx, item) in fiber_clean.iter().enumerate() {
            if !replaced_clause_idxs.contains(&idx) {
                rewritten.push(item.clone());
            }
        }
        rewritten.extend(derived_ray_clauses);

        // Attach guards and unroll (1,1)-chains (collapsing split ALO chains `~a_{r-1} v w_g v a_r`!)
        let re_items: Vec<(Vec<i32>, usize)> = rewritten
            .into_iter()
            .map(|(core, u_cid)| {
                let mut full = guard_lits.to_vec();
                full.extend_from_slice(&core);
                full.sort_by_key(|&z| (z.abs(), z));
                (full, u_cid)
            })
            .collect();
        let re_unrolled = unroll_11_chains_logged(&re_items, logger, cut_set);

        let mut clean_rewritten: Vec<(Vec<i32>, usize)> = Vec::with_capacity(re_unrolled.len());
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
                return Some((u_cid, deg_d));
            }
            clean_rewritten.push((core, u_cid));
        }

        if debug {
            let mut w_hist: BTreeMap<usize, usize> = BTreeMap::new();
            let mut vars_cr: HashSet<i32> = HashSet::new();
            for (c, _) in &clean_rewritten {
                *w_hist.entry(c.len()).or_default() += 1;
                for &l in c {
                    vars_cr.insert(l.abs());
                }
            }
            eprintln!(
                "[zassenhaus] deg_d={} clean_rewritten={} active_vars={} widths={:?}",
                deg_d,
                clean_rewritten.len(),
                vars_cr.len(),
                w_hist
            );
        }

        // Refute the rewritten ray core via guarded PHP or guarded Veronese RM(d, n)!
        if let Some(php_cid) = try_certify_guarded_php(&clean_rewritten, guard_lits, logger) {
            return Some((php_cid, deg_d));
        }
        if let Some((v_cid, deg_u)) =
            try_certify_guarded_veronese_rm_d(&clean_rewritten, guard_lits, logger, next_var, 4, 8)
        {
            return Some((v_cid, deg_u.max(deg_d)));
        }

        // Compact ray-wire core (e.g. Lifted_PHP65_o_Keccak4L where 30 PHP vars fold onto 13 shift rays):
        // filter clean_rewritten to clauses supported solely on allocated ray wires.
        let ray_wire_set: HashSet<i32> = ray_witness.values().map(|a| a.wire).collect();
        let ray_only: Vec<(Vec<i32>, usize)> = clean_rewritten
            .iter()
            .filter(|(cl, _)| !cl.is_empty() && cl.iter().all(|l| ray_wire_set.contains(&l.abs())))
            .cloned()
            .collect();
        if !ray_only.is_empty() {
            let mut rv_set: BTreeSet<i32> = BTreeSet::new();
            for (cl, _) in &ray_only {
                for &l in cl {
                    rv_set.insert(l.abs());
                }
            }
            let rv_list: Vec<i32> = rv_set.into_iter().collect();
            let k_rv = rv_list.len();
            if debug {
                eprintln!(
                    "[zassenhaus] deg_d={} ray_only={} clauses on {} ray vars",
                    deg_d,
                    ray_only.len(),
                    k_rv
                );
            }
            if k_rv > 0 && k_rv <= 16 {
                // Direct 2^{k_rv} pure-`pol` cube collapse if UNSAT!
                let full_cube = 1usize << k_rv;
                let mut cover: Vec<Option<usize>> = vec![None; full_cube];
                let mut n_cov = 0usize;
                for (cl_idx, (cl, _)) in ray_only.iter().enumerate() {
                    let mut req_pos = 0usize;
                    let mut req_val = 0usize;
                    for &lit in cl {
                        let pos = rv_list.binary_search(&lit.abs()).unwrap();
                        req_pos |= 1usize << pos;
                        if lit < 0 {
                            req_val |= 1usize << pos;
                        }
                    }
                    // Clause is falsified when (mask & req_pos) == req_val
                    let free_mask = (full_cube - 1) ^ req_pos;
                    let mut sub = free_mask;
                    loop {
                        let m = req_val | sub;
                        if cover[m].is_none() {
                            cover[m] = Some(cl_idx);
                            n_cov += 1;
                        }
                        if sub == 0 {
                            break;
                        }
                        sub = (sub - 1) & free_mask;
                    }
                    if n_cov == full_cube {
                        break;
                    }
                }
                if n_cov == full_cube {
                    let mut leaves = vec![0usize; full_cube];
                    for mask in 0..full_cube {
                        let cl_idx = cover[mask].unwrap();
                        let (ref cl, base_cid) = ray_only[cl_idx];
                        let mut pres = guard_set.clone();
                        for &l in cl {
                            pres.insert(l);
                        }
                        let mut target = Vec::with_capacity(guard_lits.len() + k_rv);
                        target.extend_from_slice(guard_lits);
                        for q in 0..k_rv {
                            target.push(if ((mask >> q) & 1) == 1 {
                                -rv_list[q]
                            } else {
                                rv_list[q]
                            });
                        }
                        leaves[mask] = weaken_clause_to_target(base_cid, &pres, &target, logger);
                    }
                    let contra_cid = collapse_clause_cube(k_rv, &leaves, logger);
                    return Some((contra_cid, deg_d));
                }
            }
            if k_rv > 0 && k_rv <= 48 {
                if let Some((m_cid, deg_u)) = crate::binom_macaulay::try_certify_guarded_binom_macaulay(
                    &ray_only,
                    guard_lits,
                    cut_set,
                    logger,
                    next_var,
                ) {
                    return Some((m_cid, deg_u.max(deg_d)));
                }
            }
        }
    }

    None
}
