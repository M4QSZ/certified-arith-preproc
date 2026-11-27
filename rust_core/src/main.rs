//! Native Rust `VeriPB 3.0` proof emitter (`v0.5.0`) for blind higher-order Veronese
//! Reed-Muller `RM(d, n)` (`1 <= d <= 4`), native `Z`-adder telescoping & 2-adic Hensel peeling
//! (ATAQUE-04), logged degree-absorbing Macaulay binomial ideal lift (ATAQUE-02),
//! local-intersection Zassenhaus ray rewriting (ATAQUE-01), and guarded Cutting-Planes decomposition.

mod binom_macaulay;
mod lifted_zassenhaus;
mod z_adder;

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::env;
use std::fmt::Write as FmtWrite;
use std::fs::{self, File};
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::PathBuf;
use std::time::Instant;

#[inline]
pub(crate) fn write_lit(out: &mut String, lit: i32) {
    if lit > 0 {
        let _ = write!(out, "x{}", lit);
    } else {
        let _ = write!(out, "~x{}", -lit);
    }
}

pub(crate) struct VeriPBLogger {
    pub(crate) cid: usize,
    pub(crate) lines_count: usize,
    buf: String,
    scratch: String,
}

impl VeriPBLogger {
    pub(crate) fn new(n_clauses: usize) -> Self {
        let mut buf = String::with_capacity(8 * 1024 * 1024);
        let _ = writeln!(buf, "pseudo-Boolean proof version 3.0");
        let _ = writeln!(buf, "f {} ;", n_clauses);
        Self {
            cid: n_clauses,
            lines_count: 2,
            buf,
            scratch: String::with_capacity(256),
        }
    }

    #[inline]
    pub(crate) fn emit_pol_raw(&mut self, expr: &str) -> usize {
        self.cid += 1;
        self.lines_count += 1;
        let _ = writeln!(self.buf, "pol {} ;", expr);
        self.cid
    }

    #[inline]
    pub(crate) fn emit_pol_add2(&mut self, id1: usize, id2: usize, saturate: bool) -> usize {
        self.cid += 1;
        self.lines_count += 1;
        if saturate {
            let _ = writeln!(self.buf, "pol {} {} + s ;", id1, id2);
        } else {
            let _ = writeln!(self.buf, "pol {} {} + ;", id1, id2);
        }
        self.cid
    }

    #[inline]
    pub(crate) fn emit_pol_halve2(&mut self, id1: usize, id2: usize) -> usize {
        self.cid += 1;
        self.lines_count += 1;
        let _ = writeln!(self.buf, "pol {} {} + 2 d ;", id1, id2);
        self.cid
    }

    /// Emit a RUP clause (`ONLY` used by the Z-adder telescoping module `src/z_adder.rs`).
    #[inline]
    pub(crate) fn emit_rup_clause(&mut self, lits: &[i32]) -> usize {
        self.cid += 1;
        self.lines_count += 1;
        self.scratch.clear();
        self.scratch.push_str("rup ");
        for &l in lits {
            self.scratch.push_str("1 ");
            write_lit(&mut self.scratch, l);
            self.scratch.push(' ');
        }
        self.scratch.push_str(">= 1 ;\n");
        self.buf.push_str(&self.scratch);
        self.cid
    }

    pub(crate) fn emit_red(&mut self, terms: &[(i64, i32)], rhs: i64, w_var: i32, w_val: u8) -> usize {
        self.cid += 1;
        self.lines_count += 1;
        self.scratch.clear();
        self.scratch.push_str("red ");
        for &(coeff, lit) in terms {
            let _ = write!(self.scratch, "{} ", coeff);
            write_lit(&mut self.scratch, lit);
            self.scratch.push(' ');
        }
        let _ = writeln!(self.scratch, ">= {} : x{} -> {} ;", rhs, w_var, w_val);
        self.buf.push_str(&self.scratch);
        self.cid
    }

    fn finish_to_file(&mut self, contra_id: usize, path: &PathBuf) -> std::io::Result<()> {
        let _ = writeln!(self.buf, "output NONE ;");
        let _ = writeln!(self.buf, "conclusion UNSAT : {} ;", contra_id);
        let _ = writeln!(self.buf, "end pseudo-Boolean proof ;");
        self.lines_count += 3;
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        let f = File::create(path)?;
        let mut w = BufWriter::with_capacity(4 * 1024 * 1024, f);
        w.write_all(self.buf.as_bytes())?;
        w.flush()
    }
}

fn read_dimacs(path: &PathBuf) -> std::io::Result<(i32, Vec<Vec<i32>>)> {
    let f = File::open(path)?;
    let reader = BufReader::new(f);
    let mut n_vars: i32 = 0;
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    for line in reader.lines() {
        let s = line?;
        let st = s.trim();
        if st.is_empty() || st.starts_with('c') {
            continue;
        }
        if st.starts_with('p') {
            let parts: Vec<&str> = st.split_whitespace().collect();
            if parts.len() >= 3 {
                if let Ok(v) = parts[2].parse::<i32>() {
                    if v > n_vars {
                        n_vars = v;
                    }
                }
            }
            continue;
        }
        let mut cl: Vec<i32> = Vec::with_capacity(4);
        for tok in st.split_whitespace() {
            if tok == "0" {
                continue;
            }
            if let Ok(lit) = tok.parse::<i32>() {
                if lit.abs() > n_vars {
                    n_vars = lit.abs();
                }
                cl.push(lit);
            }
        }
        if !cl.is_empty() {
            clauses.push(cl);
        }
    }
    Ok((n_vars, clauses))
}

fn write_dimacs(path: &PathBuf, n_vars: i32, clauses: &[Vec<i32>]) -> std::io::Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    let f = File::create(path)?;
    let mut w = BufWriter::with_capacity(2 * 1024 * 1024, f);
    writeln!(w, "p cnf {} {}", n_vars, clauses.len())?;
    for cl in clauses {
        for &x in cl {
            write!(w, "{} ", x)?;
        }
        writeln!(w, "0")?;
    }
    w.flush()
}

fn normalize_clause(cl: &[i32]) -> Option<Vec<i32>> {
    let mut v: Vec<i32> = cl.to_vec();
    v.sort_by_key(|&z| (z.abs(), z));
    v.dedup();
    for i in 1..v.len() {
        if v[i - 1].abs() == v[i].abs() {
            return None; // tautology x and -x
        }
    }
    Some(v)
}

fn unroll_11_chains_logged(
    clauses_with_ids: &[(Vec<i32>, usize)],
    logger: &mut VeriPBLogger,
    protected: &HashSet<i32>,
) -> Vec<(Vec<i32>, usize)> {
    let mut work: Vec<(Vec<i32>, usize)> = Vec::with_capacity(clauses_with_ids.len());
    let mut seen_init: HashSet<Vec<i32>> = HashSet::with_capacity(clauses_with_ids.len());
    for (cl, cid) in clauses_with_ids {
        if let Some(norm) = normalize_clause(cl) {
            if seen_init.insert(norm.clone()) {
                work.push((norm, *cid));
            }
        }
    }

    loop {
        let mut pos: BTreeMap<i32, Vec<usize>> = BTreeMap::new();
        let mut neg: HashMap<i32, Vec<usize>> = HashMap::new();
        for (idx, (cl, _)) in work.iter().enumerate() {
            for &lit in cl {
                let v = lit.abs();
                if protected.contains(&v) {
                    continue;
                }
                if lit > 0 {
                    pos.entry(v).or_default().push(idx);
                } else {
                    neg.entry(v).or_default().push(idx);
                }
            }
        }

        let mut used: Vec<bool> = vec![false; work.len()];
        let mut merges: Vec<(i32, usize, usize)> = Vec::new();
        for (&v, p_idxs) in &pos {
            if p_idxs.len() == 1 {
                if let Some(n_idxs) = neg.get(&v) {
                    if n_idxs.len() == 1 {
                        let pi = p_idxs[0];
                        let ni = n_idxs[0];
                        if pi != ni && !used[pi] && !used[ni] {
                            used[pi] = true;
                            used[ni] = true;
                            merges.push((v, pi, ni));
                        }
                    }
                }
            }
        }

        if merges.is_empty() {
            break;
        }

        let mut nxt: Vec<(Vec<i32>, usize)> = Vec::with_capacity(work.len());
        for (idx, item) in work.iter().enumerate() {
            if !used[idx] {
                nxt.push(item.clone());
            }
        }

        for (v, pi, ni) in merges {
            let (ref cl_p, id_p) = work[pi];
            let (ref cl_n, id_n) = work[ni];
            let mut combined: Vec<i32> = Vec::with_capacity(cl_p.len() + cl_n.len());
            let mut overlap = false;
            let cp: Vec<i32> = cl_p.iter().copied().filter(|&x| x != v).collect();
            let cn: Vec<i32> = cl_n.iter().copied().filter(|&x| x != -v).collect();
            for &x in &cp {
                if cn.contains(&x) {
                    overlap = true;
                }
                combined.push(x);
            }
            combined.extend_from_slice(&cn);
            if let Some(norm) = normalize_clause(&combined) {
                let new_cid = logger.emit_pol_add2(id_p, id_n, overlap);
                nxt.push((norm, new_cid));
            }
        }

        let mut dedup: Vec<(Vec<i32>, usize)> = Vec::with_capacity(nxt.len());
        let mut seen: HashSet<Vec<i32>> = HashSet::with_capacity(nxt.len());
        for (cl, cid) in nxt {
            if seen.insert(cl.clone()) {
                dedup.push((cl, cid));
            }
        }
        work = dedup;
    }

    work
}

fn discover_primal_vertex_cut(unrolled_clauses: &[Vec<i32>], max_cut: usize) -> Option<Vec<i32>> {
    let mut adj: HashMap<i32, HashSet<i32>> = HashMap::new();
    let mut all_v: BTreeSet<i32> = BTreeSet::new();
    for cl in unrolled_clauses {
        for &x in cl {
            all_v.insert(x.abs());
        }
        for i in 0..cl.len() {
            let ui = cl[i].abs();
            for j in (i + 1)..cl.len() {
                let vj = cl[j].abs();
                adj.entry(ui).or_default().insert(vj);
                adj.entry(vj).or_default().insert(ui);
            }
        }
    }
    if all_v.len() < 8 {
        return None;
    }

    let mut v_by_deg: Vec<i32> = all_v.iter().copied().collect();
    v_by_deg.sort_by_key(|&v| (adj.get(&v).map_or(0, |s| s.len()), v));
    let mut tested: HashSet<Vec<i32>> = HashSet::new();
    let n_anchors = v_by_deg.len().min(64);
    let mut best_cut: Option<Vec<i32>> = None;

    for &u in &v_by_deg[..n_anchors] {
        let Some(nu) = adj.get(&u) else { continue };
        if nu.len() >= all_v.len() - 1 {
            continue;
        }
        for &v in &v_by_deg {
            if v == u || nu.contains(&v) {
                continue;
            }
            let Some(nv) = adj.get(&v) else { continue };
            let mut s_cand: Vec<i32> = nu.intersection(nv).copied().collect();
            if s_cand.is_empty() || s_cand.len() > max_cut {
                continue;
            }
            if let Some(ref bc) = best_cut {
                if s_cand.len() > bc.len() {
                    continue;
                }
            }
            s_cand.sort_unstable();
            if let Some(ref bc) = best_cut {
                if s_cand.len() == bc.len() && s_cand >= *bc {
                    continue;
                }
            }
            if !tested.insert(s_cand.clone()) {
                continue;
            }
            let s_set: HashSet<i32> = s_cand.iter().copied().collect();
            let rem_len = all_v.len() - s_cand.len();
            if rem_len < 6 {
                continue;
            }
            let mut comp_u: HashSet<i32> = HashSet::new();
            comp_u.insert(u);
            let mut q = vec![u];
            while let Some(cur) = q.pop() {
                if let Some(nbs) = adj.get(&cur) {
                    for &nb in nbs {
                        if !s_set.contains(&nb) && comp_u.insert(nb) {
                            q.push(nb);
                        }
                    }
                }
            }
            if comp_u.len() == rem_len {
                continue;
            }
            let mut visited = comp_u.clone();
            let mut big_comps = if comp_u.len() >= 3 { 1 } else { 0 };
            let mut total_comps = 1;
            for &start in &all_v {
                if s_set.contains(&start) || visited.contains(&start) {
                    continue;
                }
                total_comps += 1;
                let mut csize = 0usize;
                let mut qq = vec![start];
                visited.insert(start);
                while let Some(cur) = qq.pop() {
                    csize += 1;
                    if let Some(nbs) = adj.get(&cur) {
                        for &nb in nbs {
                            if !s_set.contains(&nb) && visited.insert(nb) {
                                qq.push(nb);
                            }
                        }
                    }
                }
                if csize >= 3 {
                    big_comps += 1;
                }
            }
            if total_comps >= 2 && big_comps >= 2 {
                if s_cand.len() == 1 {
                    return Some(s_cand);
                }
                best_cut = Some(s_cand);
            }
        }
    }
    best_cut
}

fn weaken_clause_to_target(
    cid: usize,
    present: &HashSet<i32>,
    target: &[i32],
    logger: &mut VeriPBLogger,
) -> usize {
    let mut rpn = String::new();
    let mut added = false;
    let mut seen: HashSet<i32> = present.clone();
    let _ = write!(rpn, "{}", cid);
    for &l in target {
        if seen.insert(l) {
            rpn.push(' ');
            write_lit(&mut rpn, l);
            rpn.push_str(" +");
            added = true;
        }
    }
    if !added {
        cid
    } else {
        logger.emit_pol_raw(&rpn)
    }
}

fn try_certify_guarded_php(
    fiber_items: &[(Vec<i32>, usize)],
    guard_lits: &[i32],
    logger: &mut VeriPBLogger,
) -> Option<usize> {
    let mut amo_cid: HashMap<(i32, i32), usize> = HashMap::new();
    for (cl, cid) in fiber_items {
        if cl.len() == 2 {
            let a = -cl[0];
            let b = -cl[1];
            if a != b && !amo_cid.contains_key(&(a, b)) {
                amo_cid.insert((a, b), *cid);
                amo_cid.insert((b, a), *cid);
            }
        }
    }
    if amo_cid.is_empty() {
        return None;
    }

    let mut amo_deg: HashMap<i32, usize> = HashMap::new();
    for &(l1, _) in amo_cid.keys() {
        *amo_deg.entry(l1).or_insert(0) += 1;
    }

    for min_alo_len in [3usize, 2usize] {
        let mut alo_cands: Vec<&(Vec<i32>, usize)> = fiber_items
            .iter()
            .filter(|(cl, _)| cl.len() >= min_alo_len)
            .collect();
        if alo_cands.len() < 2 {
            continue;
        }
        alo_cands.sort_by_key(|(cl, _)| {
            let min_d = cl
                .iter()
                .map(|x| *amo_deg.get(x).unwrap_or(&0))
                .min()
                .unwrap_or(0);
            (std::cmp::Reverse(cl.len()), std::cmp::Reverse(min_d))
        });

        let mut valid_alo: Vec<(Vec<i32>, usize)> = Vec::new();
        let mut used_lits: HashSet<i32> = HashSet::new();
        for &(ref cl, cid) in &alo_cands {
            if cl.iter().all(|x| *amo_deg.get(x).unwrap_or(&0) >= 1)
                && cl.iter().all(|x| !used_lits.contains(x))
            {
                for &x in cl {
                    used_lits.insert(x);
                }
                valid_alo.push((cl.clone(), *cid));
            }
        }
        if valid_alo.len() < 2 {
            continue;
        }

        let mut unassigned: BTreeSet<i32> = used_lits.iter().copied().collect();
        let mut cliques: Vec<Vec<i32>> = Vec::new();
        while !unassigned.is_empty() {
            let seed = *unassigned
                .iter()
                .max_by_key(|&&x| {
                    unassigned
                        .iter()
                        .filter(|&&y| y != x && amo_cid.contains_key(&(x, y)))
                        .count()
                })
                .unwrap();
            let mut clique = vec![seed];
            let mut cands: Vec<i32> = unassigned
                .iter()
                .copied()
                .filter(|&y| y != seed && amo_cid.contains_key(&(seed, y)))
                .collect();
            cands.sort_by_key(|&y| {
                std::cmp::Reverse(
                    unassigned
                        .iter()
                        .filter(|&&z| z != y && amo_cid.contains_key(&(y, z)))
                        .count(),
                )
            });
            for y in cands {
                if clique.iter().all(|&cur| amo_cid.contains_key(&(y, cur))) {
                    clique.push(y);
                }
            }
            for &x in &clique {
                unassigned.remove(&x);
            }
            cliques.push(clique);
        }

        let p_count = valid_alo.len();
        let h_count = cliques.len();
        if p_count <= h_count {
            continue;
        }

        let mut hole_ids: Vec<usize> = Vec::with_capacity(h_count);
        let mut c_guard = p_count;
        for q in &cliques {
            let m_q = q.len();
            if m_q == 1 {
                let mut s = String::new();
                write_lit(&mut s, -q[0]);
                hole_ids.push(logger.emit_pol_raw(&s));
                continue;
            }
            let mut cur_id = amo_cid[&(q[0], q[1])];
            for m_step in 2..m_q {
                let nxt_lit = q[m_step];
                let mut rpn = String::new();
                if m_step - 1 == 1 {
                    let _ = write!(rpn, "{}", cur_id);
                } else {
                    let _ = write!(rpn, "{} {} *", cur_id, m_step - 1);
                }
                for &prev_lit in &q[..m_step] {
                    let pid = amo_cid[&(prev_lit, nxt_lit)];
                    let _ = write!(rpn, " {} +", pid);
                }
                let _ = write!(rpn, " {} d", m_step);
                cur_id = logger.emit_pol_raw(&rpn);
            }
            hole_ids.push(cur_id);
            c_guard += m_q - 1;
        }

        let mut sum_rpn = format!("{}", valid_alo[0].1);
        for &(_, cid) in &valid_alo[1..] {
            let _ = write!(sum_rpn, " {} +", cid);
        }
        for &hid in &hole_ids {
            let _ = write!(sum_rpn, " {} +", hid);
        }
        let sum_cid = logger.emit_pol_raw(&sum_rpn);
        if guard_lits.is_empty() {
            return Some(sum_cid);
        }
        let div_rpn = format!("{} {} d", sum_cid, c_guard);
        return Some(logger.emit_pol_raw(&div_rpn));
    }
    None
}

#[derive(Clone)]
pub(crate) struct VeroneseRecord {
    supp: Vec<i32>,
    lin_vars: Vec<i32>,
    higher_mons: Vec<Vec<i32>>, // each sorted, len 2..=deg_lim
    rhs: u8,
    forbid_map: Vec<Option<(usize, HashSet<i32>)>>, // indexed by mask 0..(1<<k)
}

fn realize_parity3_bounds(
    v1: i32,
    v2: i32,
    v3: i32,
    rhs: u8,
    forbid3: &HashMap<(u8, u8, u8), usize>,
    guard_lits: &[i32],
    logger: &mut VeriPBLogger,
    next_var: &mut i32,
) -> (usize, usize, usize, usize) {
    let y1 = if rhs == 1 { -v1 } else { v1 };
    let y2 = v2;
    let y3 = v3;
    let map_pt = |by1: u8, by2: u8, by3: u8| -> usize {
        let bv1 = if rhs == 1 { 1 - by1 } else { by1 };
        forbid3[&(bv1, by2, by3)]
    };
    let k1 = map_pt(1, 0, 0);
    let k2 = map_pt(0, 1, 0);
    let k3 = map_pt(0, 0, 1);
    let k4 = map_pt(1, 1, 1);

    *next_var += 1;
    let w_var = *next_var;
    let r1 = logger.emit_red(&[(1, y1), (1, y2), (1, y3), (2, -w_var)], 2, w_var, 0);
    let r2 = logger.emit_red(&[(1, -y1), (1, -y2), (1, -y3), (2, w_var)], 2, w_var, 1);

    let l1 = logger.emit_pol_halve2(r2, k1);
    let l2 = logger.emit_pol_halve2(r2, k2);
    let l3 = logger.emit_pol_halve2(r2, k3);
    let u_minus = logger.emit_pol_raw(&format!("{} {} + {} + 2 * {} + 3 d", l1, l2, l3, k4));
    let gamma_m = if guard_lits.is_empty() { 0 } else { 3 };
    (r1, 0, u_minus, gamma_m)
}

fn extract_veronese_records(
    fiber_items: &[(Vec<i32>, usize)],
    guard_lits: &[i32],
    deg_lim: usize,
    max_arity: usize,
) -> Vec<VeroneseRecord> {
    let mut by_supp: BTreeMap<Vec<i32>, Vec<(Vec<i32>, usize)>> = BTreeMap::new();
    for (cl, cid) in fiber_items {
        if !cl.is_empty() && cl.len() <= max_arity {
            let mut supp: Vec<i32> = cl.iter().map(|x| x.abs()).collect();
            supp.sort_unstable();
            supp.dedup();
            if supp.len() == cl.len() {
                by_supp.entry(supp).or_default().push((cl.clone(), *cid));
            }
        }
    }

    let guard_set: HashSet<i32> = guard_lits.iter().copied().collect();
    let mut records: Vec<VeroneseRecord> = Vec::new();

    for (supp, items) in by_supp {
        let k = supp.len();
        let full_cube = 1usize << k;
        let half_cube = 1usize << (k - 1);
        if items.len() < half_cube {
            continue;
        }

        let mut forbid_map: Vec<Option<(usize, HashSet<i32>)>> = vec![None; full_cube];
        let mut n_forbid = 0usize;
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
                n_forbid += 1;
            }
        }

        if n_forbid < half_cube {
            continue;
        }

        if n_forbid == full_cube {
            records.push(VeroneseRecord {
                supp,
                lin_vars: Vec::new(),
                higher_mons: Vec::new(),
                rhs: 1,
                forbid_map,
            });
            continue;
        }

        if n_forbid == half_cube {
            let mut anf = vec![0u8; full_cube];
            for m in 0..full_cube {
                if forbid_map[m].is_some() {
                    anf[m] = 1;
                }
            }
            for j in 0..k {
                let step = 1usize << j;
                for m in 0..full_cube {
                    if (m & step) != 0 {
                        anf[m] ^= anf[m ^ step];
                    }
                }
            }

            if (0..full_cube).any(|m| anf[m] == 1 && (m.count_ones() as usize) > deg_lim) {
                continue;
            }

            let rhs = anf[0];
            let mut lin_vars = Vec::new();
            let mut higher_mons = Vec::new();
            for m in 1..full_cube {
                if anf[m] == 1 {
                    let deg = m.count_ones() as usize;
                    if deg == 1 {
                        let j = m.trailing_zeros() as usize;
                        lin_vars.push(supp[j]);
                    } else {
                        let mut mon = Vec::with_capacity(deg);
                        for j in 0..k {
                            if ((m >> j) & 1) == 1 {
                                mon.push(supp[j]);
                            }
                        }
                        higher_mons.push(mon);
                    }
                }
            }
            if lin_vars.is_empty() && higher_mons.is_empty() && rhs == 0 {
                continue;
            }
            records.push(VeroneseRecord {
                supp,
                lin_vars,
                higher_mons,
                rhs,
                forbid_map,
            });
        } else {
            // Overconstrained block (n_forbid > 2^{k-1}, sat_pts < 128 -> fits in u128!)
            let mut sat_masks: Vec<usize> = Vec::new();
            for m in 0..full_cube {
                if forbid_map[m].is_none() {
                    sat_masks.push(m);
                }
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

            for (m_idx, &mm) in mon_masks.iter().enumerate() {
                let mut vec_eval: u128 = 0;
                for (s_idx, &sm) in sat_masks.iter().enumerate() {
                    if (sm & mm) == mm {
                        vec_eval |= 1u128 << s_idx;
                    }
                }
                let mut comb = vec![0u64; comb_words];
                comb[m_idx / 64] |= 1u64 << (m_idx % 64);

                let mut reduced_zero = false;
                loop {
                    if vec_eval == 0 {
                        reduced_zero = true;
                        break;
                    }
                    let msb = 127usize - (vec_eval.leading_zeros() as usize);
                    if let Some((p_vec, p_comb)) = pivots.get(&msb) {
                        vec_eval ^= *p_vec;
                        for w in 0..comb_words {
                            comb[w] ^= p_comb[w];
                        }
                    } else {
                        pivots.insert(msb, (vec_eval, comb.clone()));
                        break;
                    }
                }
                if reduced_zero {
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
                        records.push(VeroneseRecord {
                            supp: supp.clone(),
                            lin_vars,
                            higher_mons,
                            rhs,
                            forbid_map: forbid_map.clone(),
                        });
                    }
                }
            }
        }
    }
    records
}

pub(crate) fn collapse_clause_cube(k: usize, leaves: &[usize], logger: &mut VeriPBLogger) -> usize {
    let mut cur: Vec<usize> = leaves.to_vec();
    for q in (0..k).rev() {
        let stride = 1usize << q;
        let mut nxt = Vec::with_capacity(stride);
        for prefix in 0..stride {
            let id0 = cur[prefix];
            let id1 = cur[prefix | stride];
            nxt.push(logger.emit_pol_halve2(id0, id1));
        }
        cur = nxt;
    }
    cur[0]
}

/// Emit a VeriPB `pol + red` proof of `guard_lits v target_lits >= 1` from a collection of
/// `VeroneseRecord` equations whose GF(2) XOR sum equals the parity constraint violated when
/// all `target_lits` are false (empty `target_lits` means direct `0 == 1` contradiction).
pub(crate) fn emit_veronese_linear_combination(
    active_recs: &[VeroneseRecord],
    target_lits: &[i32],
    guard_lits: &[i32],
    logger: &mut VeriPBLogger,
    next_var: &mut i32,
) -> usize {
    let mut eff_guards: Vec<i32> = guard_lits.to_vec();
    for &tl in target_lits {
        if !eff_guards.contains(&tl) {
            eff_guards.push(tl);
        }
    }

    let mut owned_recs: Vec<VeroneseRecord>;
    let recs_slice: &[VeroneseRecord] = if target_lits.is_empty() {
        active_recs
    } else if target_lits.len() == 1 {
        let u_lit = target_lits[0];
        let v = u_lit.abs();
        let tid = logger.emit_pol_raw(&format!("x{} ~x{} + 2 d", v, v));
        let pres: HashSet<i32> = [v, -v].into_iter().collect();
        let mut fmap: Vec<Option<(usize, HashSet<i32>)>> = vec![None, None];
        if u_lit > 0 {
            fmap[1] = Some((tid, pres));
        } else {
            fmap[0] = Some((tid, pres));
        }
        owned_recs = active_recs.to_vec();
        owned_recs.push(VeroneseRecord {
            supp: vec![v],
            lin_vars: vec![v],
            higher_mons: Vec::new(),
            rhs: if u_lit > 0 { 0 } else { 1 },
            forbid_map: fmap,
        });
        &owned_recs
    } else if target_lits.len() == 2 {
        let mut pair = [target_lits[0], target_lits[1]];
        if pair[0].abs() > pair[1].abs() {
            pair.swap(0, 1);
        }
        let l1 = pair[0];
        let l2 = pair[1];
        let v1 = l1.abs();
        let v2 = l2.abs();
        let t1 = logger.emit_pol_raw(&format!("x{} ~x{} + 2 d", v1, v1));
        let t2 = logger.emit_pol_raw(&format!("x{} ~x{} + 2 d", v2, v2));
        let p1: HashSet<i32> = [v1, -v1].into_iter().collect();
        let p2: HashSet<i32> = [v2, -v2].into_iter().collect();
        let mut fmap: Vec<Option<(usize, HashSet<i32>)>> = vec![None; 4];
        let same_sign = (l1 > 0) == (l2 > 0);
        if !same_sign {
            if l1 > 0 {
                fmap[0] = Some((t2, p2));
                fmap[3] = Some((t1, p1));
            } else {
                fmap[0] = Some((t1, p1));
                fmap[3] = Some((t2, p2));
            }
        } else {
            if l1 > 0 {
                fmap[1] = Some((t1, p1));
                fmap[2] = Some((t2, p2));
            } else {
                fmap[1] = Some((t2, p2));
                fmap[2] = Some((t1, p1));
            }
        }
        owned_recs = active_recs.to_vec();
        owned_recs.push(VeroneseRecord {
            supp: vec![v1, v2],
            lin_vars: vec![v1, v2],
            higher_mons: Vec::new(),
            rhs: if !same_sign { 1 } else { 0 },
            forbid_map: fmap,
        });
        &owned_recs
    } else {
        panic!("Unsupported target_lits length > 2");
    };

    let guard_lits: &[i32] = &eff_guards;
    let has_extra_targets = !target_lits.is_empty();

    // Lazily allocate shared degree-d Veronese product witnesses `p_M <-> AND_{u in M} x_u`
    // Stores `(p_var, and_all_cid, vec_of_and_0_u_cids)`
    let mut monom_witness: HashMap<Vec<i32>, (i32, usize, Vec<usize>)> = HashMap::new();
    for rec in recs_slice {
        for mon in &rec.higher_mons {
            if !monom_witness.contains_key(mon) {
                *next_var += 1;
                let p_var = *next_var;
                let mut terms_all: Vec<(i64, i32)> = Vec::with_capacity(mon.len() + 1);
                for &u in mon {
                    terms_all.push((1, -u));
                }
                terms_all.push((1, p_var));
                let and_all = logger.emit_red(&terms_all, 1, p_var, 1);
                let mut and_0s: Vec<usize> = Vec::with_capacity(mon.len());
                for &u in mon {
                    let cid0 = logger.emit_red(&[(1, u), (1, -p_var)], 1, p_var, 0);
                    and_0s.push(cid0);
                }
                monom_witness.insert(mon.clone(), (p_var, and_all, and_0s));
            }
        }
    }

    let mut taut_cache: HashMap<i32, usize> = HashMap::new();
    let mut plus_terms: Vec<(usize, usize)> = Vec::new();
    let mut minus_terms: Vec<(usize, usize)> = Vec::new();
    let g_flag = if guard_lits.is_empty() { 0 } else { 1 };

    for rec in recs_slice {
        let supp = &rec.supp;
        let k = supp.len();
        let full_cube = 1usize << k;
        let supp_set: HashSet<i32> = supp.iter().copied().collect();

        let mut z_vars: Vec<i32> = rec.lin_vars.clone();
        for mon in &rec.higher_mons {
            z_vars.push(monom_witness[mon].0);
        }
        let r = z_vars.len();
        let c0 = rec.rhs;

        if r == 0 {
            let mut leaves = vec![0usize; full_cube];
            for mask in 0..full_cube {
                let mut target = guard_lits.to_vec();
                for q in 0..k {
                    let bit = (mask >> q) & 1;
                    target.push(if bit == 1 { -supp[q] } else { supp[q] });
                }
                let (base_cid, ref pres) = rec.forbid_map[mask].as_ref().unwrap();
                leaves[mask] = weaken_clause_to_target(*base_cid, pres, &target, logger);
            }
            return collapse_clause_cube(k, &leaves, logger);
        }

        // Fast path for width <= 3 PURE linear equations (zero cube overhead!)
        if !has_extra_targets && rec.higher_mons.is_empty() && r <= 3 && full_cube == (1usize << r) && k == r {
            if r == 1 {
                let v1 = z_vars[0];
                if c0 == 1 {
                    let id_p = rec.forbid_map[0].as_ref().unwrap().0;
                    let id_m = logger.emit_pol_raw(&format!("~x{}", v1));
                    plus_terms.push((id_p, g_flag));
                    minus_terms.push((id_m, 0));
                } else {
                    let id_p = logger.emit_pol_raw(&format!("x{}", v1));
                    let id_m = rec.forbid_map[1].as_ref().unwrap().0;
                    plus_terms.push((id_p, 0));
                    minus_terms.push((id_m, g_flag));
                }
                continue;
            } else if r == 2 {
                let (id_p, id_m) = if c0 == 0 {
                    (
                        rec.forbid_map[2].as_ref().unwrap().0,
                        rec.forbid_map[1].as_ref().unwrap().0,
                    )
                } else {
                    (
                        rec.forbid_map[0].as_ref().unwrap().0,
                        rec.forbid_map[3].as_ref().unwrap().0,
                    )
                };
                plus_terms.push((id_p, g_flag));
                minus_terms.push((id_m, g_flag));
                continue;
            } else if r == 3 {
                let mut forbid3: HashMap<(u8, u8, u8), usize> = HashMap::new();
                for mask in 0..8usize {
                    if let Some((cid, _)) = rec.forbid_map[mask] {
                        forbid3.insert(
                            (
                                (mask & 1) as u8,
                                ((mask >> 1) & 1) as u8,
                                ((mask >> 2) & 1) as u8,
                            ),
                            cid,
                        );
                    }
                }
                let (idp, gp, idm, gm) = realize_parity3_bounds(
                    z_vars[0],
                    z_vars[1],
                    z_vars[2],
                    c0,
                    &forbid3,
                    guard_lits,
                    logger,
                    next_var,
                );
                plus_terms.push((idp, gp));
                minus_terms.push((idm, gm));
                continue;
            }
        }

        if r == 1 {
            let z1 = z_vars[0];
            let target_lit = if c0 == 1 { z1 } else { -z1 };
            let mut leaves = vec![0usize; full_cube];
            for mask in 0..full_cube {
                let mut full_target = guard_lits.to_vec();
                for q in 0..k {
                    full_target.push(if ((mask >> q) & 1) == 1 {
                        -supp[q]
                    } else {
                        supp[q]
                    });
                }
                full_target.push(target_lit);

                if let Some((base_cid, ref pres)) = rec.forbid_map[mask] {
                    leaves[mask] = weaken_clause_to_target(base_cid, pres, &full_target, logger);
                } else if supp_set.contains(&z1) {
                    let tid = *taut_cache.entry(z1).or_insert_with(|| {
                        logger.emit_pol_raw(&format!("x{} ~x{} + 2 d", z1, z1))
                    });
                    let pres: HashSet<i32> = [z1, -z1].into_iter().collect();
                    leaves[mask] = weaken_clause_to_target(tid, &pres, &full_target, logger);
                } else {
                    let mon = &rec.higher_mons[0];
                    let (p_var, and_all, ref and_0s) = monom_witness[mon];
                    let first_zero = mon.iter().enumerate().find(|&(_, &u)| {
                        let pos = supp.binary_search(&u).unwrap();
                        ((mask >> pos) & 1) == 0
                    });
                    if let Some((j0, &u0)) = first_zero {
                        let pres: HashSet<i32> = [u0, -p_var].into_iter().collect();
                        leaves[mask] =
                            weaken_clause_to_target(and_0s[j0], &pres, &full_target, logger);
                    } else {
                        let mut pres: HashSet<i32> = mon.iter().map(|&u| -u).collect();
                        pres.insert(p_var);
                        leaves[mask] =
                            weaken_clause_to_target(and_all, &pres, &full_target, logger);
                    }
                }
            }
            let unit_cid = collapse_clause_cube(k, &leaves, logger);
            if c0 == 1 {
                let id_m = logger.emit_pol_raw(&format!("~x{}", z1));
                plus_terms.push((unit_cid, g_flag));
                minus_terms.push((id_m, 0));
            } else {
                let id_p = logger.emit_pol_raw(&format!("x{}", z1));
                plus_terms.push((id_p, 0));
                minus_terms.push((unit_cid, g_flag));
            }
            continue;
        }

        // General width r >= 2: fold z_vars[0 .. r-1] via unconditional 3-XOR witness steps
        let mut acc_var = z_vars[0];
        let mut fold_steps: Vec<(i32, i32, i32, usize, usize, usize, usize)> =
            Vec::with_capacity(r.saturating_sub(2));
        for &nxt_z in &z_vars[1..(r - 1)] {
            *next_var += 1;
            let s_var = *next_var;
            let z_01 = logger.emit_red(&[(1, acc_var), (1, -nxt_z), (1, s_var)], 1, s_var, 1);
            let z_10 = logger.emit_red(&[(1, -acc_var), (1, nxt_z), (1, s_var)], 1, s_var, 1);
            let z_00 = logger.emit_red(&[(1, acc_var), (1, nxt_z), (1, -s_var)], 1, s_var, 0);
            let z_11 = logger.emit_red(&[(1, -acc_var), (1, -nxt_z), (1, -s_var)], 1, s_var, 0);

            let mut f_a: HashMap<(u8, u8, u8), usize> = HashMap::with_capacity(4);
            f_a.insert((1, 0, 0), z_10);
            f_a.insert((0, 1, 0), z_01);
            f_a.insert((0, 0, 1), z_00);
            f_a.insert((1, 1, 1), z_11);
            let (idp_a, _, idm_a, _) =
                realize_parity3_bounds(acc_var, nxt_z, s_var, 0, &f_a, &[], logger, next_var);
            plus_terms.push((idp_a, 0));
            minus_terms.push((idm_a, 0));
            fold_steps.push((acc_var, nxt_z, s_var, z_00, z_01, z_10, z_11));
            acc_var = s_var;
        }

        let last_a = acc_var;
        let last_b = z_vars[r - 1];
        let (pair_p, pair_m) = if c0 == 0 {
            ((last_a, -last_b), (-last_a, last_b))
        } else {
            ((last_a, last_b), (-last_a, -last_b))
        };

        let mut leaves_p = vec![0usize; full_cube];
        let mut leaves_m = vec![0usize; full_cube];

        for mask in 0..full_cube {
            let mut base_target = guard_lits.to_vec();
            for q in 0..k {
                base_target.push(if ((mask >> q) & 1) == 1 {
                    -supp[q]
                } else {
                    supp[q]
                });
            }
            let mut full_p = base_target.clone();
            full_p.push(pair_p.0);
            full_p.push(pair_p.1);
            let mut full_m = base_target;
            full_m.push(pair_m.0);
            full_m.push(pair_m.1);

            if let Some((base_cid, ref pres)) = rec.forbid_map[mask] {
                leaves_p[mask] = weaken_clause_to_target(base_cid, pres, &full_p, logger);
                leaves_m[mask] = weaken_clause_to_target(base_cid, pres, &full_m, logger);
                continue;
            }

            let mut val_of: HashMap<i32, u8> = HashMap::with_capacity(k + r * 2);
            for q in 0..k {
                val_of.insert(supp[q], ((mask >> q) & 1) as u8);
            }
            let mut derived_unit: HashMap<i32, (usize, HashSet<i32>)> =
                HashMap::with_capacity(rec.higher_mons.len() + fold_steps.len());

            for mon in &rec.higher_mons {
                let (p_var, and_all, ref and_0s) = monom_witness[mon];
                if let Some((j0, &u0)) = mon
                    .iter()
                    .enumerate()
                    .find(|&(_, &u)| val_of[&u] == 0)
                {
                    val_of.insert(p_var, 0);
                    let supp_u: HashSet<i32> = [u0, -p_var].into_iter().collect();
                    derived_unit.insert(p_var, (and_0s[j0], supp_u));
                } else {
                    val_of.insert(p_var, 1);
                    let mut supp_all: HashSet<i32> = mon.iter().map(|&u| -u).collect();
                    supp_all.insert(p_var);
                    derived_unit.insert(p_var, (and_all, supp_all));
                }
            }

            for &(v1, v2, s_var, z_00, z_01, z_10, z_11) in &fold_steps {
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
                let mut cur_supp: HashSet<i32> = [-lit1_u, -lit2_u, s_lit].into_iter().collect();

                if !supp_set.contains(&v1) {
                    let (c1, ref s1) = derived_unit[&v1];
                    cur_supp.remove(&(-lit1_u));
                    let mut overlap = false;
                    for &x in s1 {
                        if x != lit1_u && cur_supp.contains(&x) {
                            overlap = true;
                        }
                    }
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
                    let mut overlap = false;
                    for &x in s2 {
                        if x != lit2_u && cur_supp.contains(&x) {
                            overlap = true;
                        }
                    }
                    cur_cid = logger.emit_pol_add2(cur_cid, c2, overlap);
                    for &x in s2 {
                        if x != lit2_u {
                            cur_supp.insert(x);
                        }
                    }
                }

                derived_unit.insert(s_var, (cur_cid, cur_supp));
            }

            let mut realize_pair =
                |t_pair: (i32, i32), full_target: &[i32], logger: &mut VeriPBLogger| -> usize {
                    for t_lit in [t_pair.0, t_pair.1] {
                        let tv = t_lit.abs();
                        let vbit = val_of[&tv];
                        let is_true = if t_lit > 0 { vbit == 1 } else { vbit == 0 };
                        if is_true {
                            if supp_set.contains(&tv) {
                                let tid = *taut_cache.entry(tv).or_insert_with(|| {
                                    logger.emit_pol_raw(&format!("x{} ~x{} + 2 d", tv, tv))
                                });
                                let pres: HashSet<i32> = [tv, -tv].into_iter().collect();
                                return weaken_clause_to_target(tid, &pres, full_target, logger);
                            } else {
                                let (dcid, ref dsupp) = derived_unit[&tv];
                                return weaken_clause_to_target(dcid, dsupp, full_target, logger);
                            }
                        }
                    }
                    panic!("Allowed point violated extracted RM(d, k) identity");
                };

            leaves_p[mask] = realize_pair(pair_p, &full_p, logger);
            leaves_m[mask] = realize_pair(pair_m, &full_m, logger);
        }

        let cid_p = collapse_clause_cube(k, &leaves_p, logger);
        let cid_m = collapse_clause_cube(k, &leaves_m, logger);
        plus_terms.push((cid_p, g_flag));
        minus_terms.push((cid_m, g_flag));
    }

    let sum_and_halve = |terms: &[(usize, usize)], logger: &mut VeriPBLogger| -> (usize, usize) {
        let mut rpn = format!("{}", terms[0].0);
        let mut g_tot = terms[0].1;
        for &(cid, gc) in &terms[1..] {
            let _ = write!(rpn, " {} +", cid);
            g_tot += gc;
        }
        if !guard_lits.is_empty() && (g_tot & 1) == 1 {
            for &g in guard_lits {
                rpn.push(' ');
                write_lit(&mut rpn, g);
                rpn.push_str(" +");
            }
            g_tot += 1;
        }
        rpn.push_str(" 2 d");
        (logger.emit_pol_raw(&rpn), g_tot / 2)
    };

    let (half_p, mp) = sum_and_halve(&plus_terms, logger);
    let (half_m, mm) = sum_and_halve(&minus_terms, logger);
    let comb_id = logger.emit_pol_add2(half_p, half_m, false);
    let tot_m = mp + mm;
    if guard_lits.is_empty() || tot_m <= 1 {
        return comb_id;
    }
    logger.emit_pol_raw(&format!("{} {} d", comb_id, tot_m))
}

fn try_certify_guarded_veronese_rm_d(
    fiber_items: &[(Vec<i32>, usize)],
    guard_lits: &[i32],
    logger: &mut VeriPBLogger,
    next_var: &mut i32,
    max_deg: usize,
    max_arity: usize,
) -> Option<(usize, usize)> {
    for deg_lim in 1..=max_deg {
        let records = extract_veronese_records(fiber_items, guard_lits, deg_lim, max_arity);
        if records.is_empty() {
            continue;
        }

        // Sparse GF(2) RREF over RM(deg_lim, n) coordinates
        let mut monom_to_id: HashMap<Vec<i32>, usize> = HashMap::new();
        let mut get_coord = |m: Vec<i32>| -> usize {
            let nxt = monom_to_id.len() + 1;
            *monom_to_id.entry(m).or_insert(nxt)
        };

        let comb_words = (records.len() + 63) / 64;
        let mut pivots: HashMap<usize, (BTreeSet<usize>, u8, Vec<u64>)> = HashMap::new();
        let mut unsat_comb: Option<Vec<u64>> = None;

        for (idx_r, rec) in records.iter().enumerate() {
            let mut row_coords: BTreeSet<usize> = BTreeSet::new();
            for &v in &rec.lin_vars {
                let c = get_coord(vec![v]);
                if !row_coords.remove(&c) {
                    row_coords.insert(c);
                }
            }
            for mon in &rec.higher_mons {
                let c = get_coord(mon.clone());
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
                    pivots.insert(lead, (row_coords, rhs, comb));
                    break;
                }
            }
            if unsat_comb.is_some() {
                break;
            }
        }

        let Some(ucomb) = unsat_comb else { continue };

        let mut active_recs: Vec<VeroneseRecord> = Vec::new();
        for (w_idx, &word) in ucomb.iter().enumerate() {
            let mut tmp = word;
            while tmp != 0 {
                let bit = tmp.trailing_zeros() as usize;
                active_recs.push(records[w_idx * 64 + bit].clone());
                tmp &= tmp - 1;
            }
        }

        let cid =
            emit_veronese_linear_combination(&active_recs, &[], guard_lits, logger, next_var);
        return Some((cid, deg_lim));
    }
    None
}

fn ensure_uniform_guard(
    cid: usize,
    present_guard: &HashSet<i32>,
    target_guard: &[i32],
    logger: &mut VeriPBLogger,
) -> usize {
    let mut rpn = format!("{}", cid);
    let mut added = false;
    for &g in target_guard {
        if !present_guard.contains(&g) {
            rpn.push(' ');
            write_lit(&mut rpn, g);
            rpn.push_str(" +");
            added = true;
        }
    }
    if !added {
        cid
    } else {
        logger.emit_pol_raw(&rpn)
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut cnf_in: Option<PathBuf> = None;
    let mut pbp_out: Option<PathBuf> = None;
    let mut veripb_cnf_out: Option<PathBuf> = None;
    let mut max_deg: usize = 4;
    let mut max_arity: usize = 8;
    let mut max_cut: usize = 6;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--cnf" => {
                i += 1;
                cnf_in = Some(PathBuf::from(&args[i]));
            }
            "--pbp" => {
                i += 1;
                pbp_out = Some(PathBuf::from(&args[i]));
            }
            "--veripb-cnf" => {
                i += 1;
                veripb_cnf_out = Some(PathBuf::from(&args[i]));
            }
            "--max-deg" => {
                i += 1;
                max_deg = args[i].parse().unwrap();
            }
            "--max-arity" => {
                i += 1;
                max_arity = args[i].parse().unwrap();
            }
            "--max-cut" => {
                i += 1;
                max_cut = args[i].parse().unwrap();
            }
            "--gen-trunc-miter" => {
                let k_bits: usize = args[i + 1].parse().unwrap();
                let keep_lsb: usize = args[i + 2].parse().unwrap();
                let seed: u64 = args[i + 3].parse().unwrap();
                let out_path = PathBuf::from(&args[i + 4]);
                let (nv, cls) =
                    z_adder::gen_truncated_schoolbook_vs_wallace_miter(k_bits, keep_lsb, seed);
                write_dimacs(&out_path, nv, &cls).expect("Failed to write truncated miter CNF");
                println!(
                    "{{\"status\":\"GENERATED\",\"vars\":{},\"clauses\":{},\"path\":\"{}\"}}",
                    nv,
                    cls.len(),
                    out_path.display()
                );
                return;
            }
            other => {
                eprintln!("Unknown flag: {}", other);
                std::process::exit(2);
            }
        }
        i += 1;
    }

    let cnf_path = cnf_in.expect("--cnf <path> is required");
    let pbp_path = pbp_out.expect("--pbp <path> is required");

    let (n_vars, clauses) = read_dimacs(&cnf_path).expect("Failed to read DIMACS CNF");
    if let Some(ref vcnf) = veripb_cnf_out {
        write_dimacs(vcnf, n_vars, &clauses).expect("Failed to write clean DIMACS CNF");
    }

    let t0 = Instant::now();

    // ATAQUE-04: Blind Z-adder telescoping & 2-adic/mod-2^k Hensel peeling for arithmetic miters
    if let Some((mut z_logger, contra_id)) = z_adder::try_certify_z_adder_miter(&clauses, n_vars) {
        z_logger
            .finish_to_file(contra_id, &pbp_path)
            .expect("Failed to write .pbp proof");
        let emit_ms = t0.elapsed().as_secs_f64() * 1000.0;
        println!(
            "{{\"status\":\"EMITTED\",\"engine\":\"z_adder\",\"vars\":{},\"clauses\":{},\"ext_vars\":0,\"cut_size\":0,\"max_deg_used\":0,\"pbp_lines\":{},\"emit_ms\":{:.2}}}",
            n_vars,
            clauses.len(),
            z_logger.lines_count,
            emit_ms
        );
        return;
    }

    let mut logger = VeriPBLogger::new(clauses.len());
    let mut next_var = n_vars;

    let init_items: Vec<(Vec<i32>, usize)> = clauses
        .iter()
        .enumerate()
        .map(|(idx, cl)| (cl.clone(), idx + 1))
        .collect();
    let empty_prot: HashSet<i32> = HashSet::new();
    let unrolled_items = unroll_11_chains_logged(&init_items, &mut logger, &empty_prot);
    let unrolled_clauses: Vec<Vec<i32>> = unrolled_items.iter().map(|(c, _)| c.clone()).collect();

    let cut_list = discover_primal_vertex_cut(&unrolled_clauses, max_cut).unwrap_or_default();
    let cut_set: HashSet<i32> = cut_list.iter().copied().collect();
    let n_fibers = 1usize << cut_list.len();
    let mut fiber_cids = vec![0usize; n_fibers];
    let mut max_deg_used = 0usize;

    for f_mask in 0..n_fibers {
        let mut guard_lits = Vec::with_capacity(cut_list.len());
        let mut sat_lits: HashSet<i32> = HashSet::with_capacity(cut_list.len());
        for (q, &sv) in cut_list.iter().enumerate() {
            let bit = (f_mask >> q) & 1;
            if bit == 1 {
                guard_lits.push(-sv);
                sat_lits.insert(sv);
            } else {
                guard_lits.push(sv);
                sat_lits.insert(-sv);
            }
        }

        let mut proj_raw: Vec<(Vec<i32>, usize)> = Vec::new();
        let mut direct_cid: Option<usize> = None;

        for (cl, cid) in &unrolled_items {
            if cl.iter().any(|x| sat_lits.contains(x)) {
                continue;
            }
            let present_g: HashSet<i32> = cl
                .iter()
                .copied()
                .filter(|x| cut_set.contains(&x.abs()))
                .collect();
            let core: Vec<i32> = cl
                .iter()
                .copied()
                .filter(|x| !cut_set.contains(&x.abs()))
                .collect();
            let u_cid = ensure_uniform_guard(*cid, &present_g, &guard_lits, &mut logger);
            if core.is_empty() {
                direct_cid = Some(u_cid);
                break;
            }
            proj_raw.push((core, u_cid));
        }

        if let Some(dcid) = direct_cid {
            fiber_cids[f_mask] = dcid;
            continue;
        }

        let re_items: Vec<(Vec<i32>, usize)> = proj_raw
            .into_iter()
            .map(|(core, u_cid)| {
                let mut full = guard_lits.clone();
                full.extend_from_slice(&core);
                full.sort_by_key(|&z| (z.abs(), z));
                (full, u_cid)
            })
            .collect();
        let re_unrolled = unroll_11_chains_logged(&re_items, &mut logger, &cut_set);

        let mut fiber_clean: Vec<(Vec<i32>, usize)> = Vec::with_capacity(re_unrolled.len());
        let mut hit_empty: Option<usize> = None;
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
            let u_cid = ensure_uniform_guard(f_cid, &present_g, &guard_lits, &mut logger);
            if core.is_empty() {
                hit_empty = Some(u_cid);
                break;
            }
            fiber_clean.push((core, u_cid));
        }

        if let Some(hcid) = hit_empty {
            fiber_cids[f_mask] = hcid;
            continue;
        }

        if let Some(php_cid) = try_certify_guarded_php(&fiber_clean, &guard_lits, &mut logger) {
            fiber_cids[f_mask] = php_cid;
            continue;
        }

        if let Some((v_cid, deg_u)) = try_certify_guarded_veronese_rm_d(
            &fiber_clean,
            &guard_lits,
            &mut logger,
            &mut next_var,
            max_deg,
            max_arity,
        ) {
            if deg_u > max_deg_used {
                max_deg_used = deg_u;
            }
            fiber_cids[f_mask] = v_cid;
            continue;
        }

        // ATAQUE-02: Logged Degree-Absorbing Macaulay Binomial Ideal Lift (compact fibers <= 48 vars)
        if let Some((m_cid, deg_u)) = binom_macaulay::try_certify_guarded_binom_macaulay(
            &fiber_clean,
            &guard_lits,
            &cut_set,
            &mut logger,
            &mut next_var,
        ) {
            if deg_u > max_deg_used {
                max_deg_used = deg_u;
            }
            fiber_cids[f_mask] = m_cid;
            continue;
        }

        // ATAQUE-01: Local-Intersection Zassenhaus + Derivative dP/du == 1 + Logged Ray Rewriting
        if let Some((z_cid, deg_u)) = lifted_zassenhaus::try_certify_guarded_lifted_zassenhaus(
            &fiber_clean,
            &guard_lits,
            &cut_set,
            &mut logger,
            &mut next_var,
        ) {
            if deg_u > max_deg_used {
                max_deg_used = deg_u;
            }
            fiber_cids[f_mask] = z_cid;
            continue;
        }

        eprintln!(
            "REJECTED: Fiber mask={} on separator {:?} is FEASIBLE or outside RM({}, n) calculus",
            f_mask, cut_list, max_deg
        );
        std::process::exit(10);
    }

    let mut cur_cube = fiber_cids;
    for q in (0..cut_list.len()).rev() {
        let stride = 1usize << q;
        let mut nxt = Vec::with_capacity(stride);
        for prefix in 0..stride {
            let id0 = cur_cube[prefix];
            let id1 = cur_cube[prefix | stride];
            nxt.push(logger.emit_pol_halve2(id0, id1));
        }
        cur_cube = nxt;
    }

    let contra_id = cur_cube[0];
    logger
        .finish_to_file(contra_id, &pbp_path)
        .expect("Failed to write .pbp proof");
    let emit_ms = t0.elapsed().as_secs_f64() * 1000.0;

    println!(
        "{{\"status\":\"EMITTED\",\"vars\":{},\"clauses\":{},\"ext_vars\":{},\"cut_size\":{},\"max_deg_used\":{},\"pbp_lines\":{},\"emit_ms\":{:.2}}}",
        n_vars,
        clauses.len(),
        next_var - n_vars,
        cut_list.len(),
        max_deg_used,
        logger.lines_count,
        emit_ms
    );
}
