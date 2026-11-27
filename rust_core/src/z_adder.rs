//! ATAQUE-04: Native Rust `Z`-Adder Telescoping & 2-Adic/Mod-`2^k` Hensel Peeling
//! with exact `i128` rational arithmetic and VeriPB 3.0 proof emission.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::Write as FmtWrite;

use crate::{write_lit, VeriPBLogger};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Rat {
    num: i128,
    den: i128,
}

fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

fn lcm_i128(a: i128, b: i128) -> Option<i128> {
    if a == 0 || b == 0 {
        return Some(0);
    }
    let ua = a.unsigned_abs();
    let ub = b.unsigned_abs();
    let g = gcd_u128(ua, ub);
    let prod = (ua / g).checked_mul(ub)?;
    if prod > i128::MAX as u128 {
        None
    } else {
        Some(prod as i128)
    }
}

impl Rat {
    #[inline]
    fn zero() -> Self {
        Self { num: 0, den: 1 }
    }

    #[inline]
    fn from_int(n: i128) -> Self {
        Self { num: n, den: 1 }
    }

    #[inline]
    fn is_zero(self) -> bool {
        self.num == 0
    }

    fn new(mut num: i128, mut den: i128) -> Option<Self> {
        if den == 0 {
            return None;
        }
        if num == 0 {
            return Some(Self::zero());
        }
        if den < 0 {
            num = num.checked_neg()?;
            den = den.checked_neg()?;
        }
        let g = gcd_u128(num.unsigned_abs(), den.unsigned_abs()) as i128;
        Some(Self {
            num: num / g,
            den: den / g,
        })
    }

    fn add(self, rhs: Self) -> Option<Self> {
        if self.num == 0 {
            return Some(rhs);
        }
        if rhs.num == 0 {
            return Some(self);
        }
        let g = gcd_u128(self.den.unsigned_abs(), rhs.den.unsigned_abs()) as i128;
        let a = self.num.checked_mul(rhs.den / g)?;
        let b = rhs.num.checked_mul(self.den / g)?;
        let n = a.checked_add(b)?;
        let d = (self.den / g).checked_mul(rhs.den)?;
        Self::new(n, d)
    }

    fn sub(self, rhs: Self) -> Option<Self> {
        self.add(Self {
            num: rhs.num.checked_neg()?,
            den: rhs.den,
        })
    }

    fn mul(self, rhs: Self) -> Option<Self> {
        if self.num == 0 || rhs.num == 0 {
            return Some(Self::zero());
        }
        let g1 = gcd_u128(self.num.unsigned_abs(), rhs.den.unsigned_abs()) as i128;
        let g2 = gcd_u128(rhs.num.unsigned_abs(), self.den.unsigned_abs()) as i128;
        let n = (self.num / g1).checked_mul(rhs.num / g2)?;
        let d = (self.den / g2).checked_mul(rhs.den / g1)?;
        Self::new(n, d)
    }

    fn inv(self) -> Option<Self> {
        Self::new(self.den, self.num)
    }

    fn mul_int_exact(self, scale: i128) -> Option<i128> {
        if self.num == 0 {
            return Some(0);
        }
        if scale % self.den != 0 {
            return None;
        }
        self.num.checked_mul(scale / self.den)
    }
}

fn derive_clause_over_cube(
    logger: &mut VeriPBLogger,
    target_lits: &[i32],
    cube_vars: &[i32],
) -> usize {
    let mut base: Vec<i32> = Vec::with_capacity(target_lits.len());
    for &l in target_lits {
        if !base.contains(&l) {
            base.push(l);
        }
    }
    for &l in &base {
        if base.contains(&(-l)) {
            let v = l.abs();
            return logger.emit_pol_raw(&format!("x{} ~x{} +", v, v));
        }
    }
    let base_vars: HashSet<i32> = base.iter().map(|x| x.abs()).collect();
    let rem_vars: Vec<i32> = cube_vars
        .iter()
        .copied()
        .filter(|v| !base_vars.contains(v))
        .collect();

    fn rec(
        logger: &mut VeriPBLogger,
        base: &[i32],
        rem_vars: &[i32],
        idx: usize,
        extra: &mut Vec<i32>,
    ) -> usize {
        if idx == rem_vars.len() {
            let mut full = Vec::with_capacity(base.len() + extra.len());
            full.extend_from_slice(base);
            full.extend_from_slice(extra);
            return logger.emit_rup_clause(&full);
        }
        let v = rem_vars[idx];
        extra.push(v);
        let id_pos = rec(logger, base, rem_vars, idx + 1, extra);
        extra.pop();
        extra.push(-v);
        let id_neg = rec(logger, base, rem_vars, idx + 1, extra);
        extra.pop();
        logger.emit_pol_halve2(id_pos, id_neg)
    }

    let mut extra = Vec::with_capacity(rem_vars.len());
    rec(logger, &base, &rem_vars, 0, &mut extra)
}

fn derive_half_adder_z_eq(
    logger: &mut VeriPBLogger,
    u_lit: i32,
    w_lit: i32,
    s_lit: i32,
    c_lit: i32,
    gate_inputs: &[i32],
) -> (usize, usize) {
    let a1 = derive_clause_over_cube(logger, &[-c_lit, u_lit], gate_inputs);
    let a2 = derive_clause_over_cube(logger, &[-c_lit, w_lit], gate_inputs);
    let a3 = derive_clause_over_cube(logger, &[-c_lit, -s_lit], gate_inputs);
    let a4 = derive_clause_over_cube(logger, &[u_lit, w_lit, -s_lit], gate_inputs);
    let id_ge = logger.emit_pol_raw(&format!("{} {} + {} + 2 * {} + 3 d", a1, a2, a3, a4));

    let d1 = derive_clause_over_cube(logger, &[-u_lit, s_lit, c_lit], gate_inputs);
    let d2 = derive_clause_over_cube(logger, &[-w_lit, s_lit, c_lit], gate_inputs);
    let b1 = derive_clause_over_cube(logger, &[-u_lit, -w_lit, c_lit], gate_inputs);
    let mut rpn = format!("{} {} + {} + ", d1, d2, b1);
    write_lit(&mut rpn, c_lit);
    rpn.push_str(" + 2 d");
    let id_le = logger.emit_pol_raw(&rpn);
    (id_ge, id_le)
}

fn derive_disjoint_or_z_eq(
    logger: &mut VeriPBLogger,
    c1_lit: i32,
    c2_lit: i32,
    cout_lit: i32,
    fa_inputs: &[i32],
) -> (usize, usize) {
    let id_ge = derive_clause_over_cube(logger, &[c1_lit, c2_lit, -cout_lit], fa_inputs);
    let e1 = derive_clause_over_cube(logger, &[-c1_lit, cout_lit], fa_inputs);
    let e2 = derive_clause_over_cube(logger, &[-c2_lit, cout_lit], fa_inputs);
    let e3 = derive_clause_over_cube(logger, &[-c1_lit, -c2_lit], fa_inputs);
    let id_le = logger.emit_pol_raw(&format!("{} {} + {} + 2 d", e1, e2, e3));
    (id_ge, id_le)
}

fn resolve_var(mut v: i32, equiv: &HashMap<i32, (i32, u8)>) -> (i32, u8) {
    let mut flip = 0u8;
    while let Some(&(lo, f)) = equiv.get(&v) {
        v = lo;
        flip ^= f;
    }
    (v, flip)
}

fn apply_fixed_and_equivs(
    clauses: &[Vec<i32>],
    fixed: &HashMap<i32, u8>,
    equiv: &HashMap<i32, (i32, u8)>,
) -> Option<Vec<Vec<i32>>> {
    let mut out: Vec<Vec<i32>> = Vec::with_capacity(clauses.len());
    let mut seen: HashSet<Vec<i32>> = HashSet::with_capacity(clauses.len());
    for cl in clauses {
        let mut new_cl: Vec<i32> = Vec::with_capacity(cl.len());
        let mut sat = false;
        for &lit in cl {
            let v0 = lit.abs();
            let pol = if lit > 0 { 1u8 } else { 0u8 };
            let (rv, fl) = resolve_var(v0, equiv);
            let req_val = pol ^ fl;
            if let Some(&fv) = fixed.get(&rv) {
                if fv == req_val {
                    sat = true;
                    break;
                }
                continue;
            }
            let nlit = if req_val == 1 { rv } else { -rv };
            if new_cl.contains(&(-nlit)) {
                sat = true;
                break;
            }
            if !new_cl.contains(&nlit) {
                new_cl.push(nlit);
            }
        }
        if sat {
            continue;
        }
        if new_cl.is_empty() {
            return None; // UNSAT
        }
        new_cl.sort_by_key(|&z| (z.abs(), z));
        if seen.insert(new_cl.clone()) {
            out.push(new_cl);
        }
    }
    Some(out)
}

type GatesByIn = BTreeMap<(i32, i32), Vec<(i32, [u8; 4])>>;
type GateOfOut = BTreeMap<i32, (i32, i32, [u8; 4])>;

const VAR_TT3: [u8; 3] = [0b1111_0000, 0b1100_1100, 0b1010_1010];

fn scan_deterministic_2input_gates(work_cls: &[Vec<i32>]) -> Option<(GatesByIn, GateOfOut)> {
    let mut two_by_pair: HashMap<(i32, i32), Vec<&Vec<i32>>> = HashMap::new();
    let mut three_by_trip: BTreeMap<(i32, i32, i32), Vec<&Vec<i32>>> = BTreeMap::new();
    for c in work_cls {
        if c.len() == 2 {
            let a = c[0].abs();
            let b = c[1].abs();
            let pair = if a < b { (a, b) } else { (b, a) };
            two_by_pair.entry(pair).or_default().push(c);
        } else if c.len() == 3 {
            let mut vs = [c[0].abs(), c[1].abs(), c[2].abs()];
            vs.sort_unstable();
            three_by_trip
                .entry((vs[0], vs[1], vs[2]))
                .or_default()
                .push(c);
        }
    }

    let mut gates_by_in: GatesByIn = BTreeMap::new();
    let mut gate_of_quad_out: GateOfOut = BTreeMap::new();

    for (&(v0, v1, v2), t_list) in &three_by_trip {
        let trip = [v0, v1, v2];
        let mut sat_m: u8 = 0xFF;

        let mut apply_clause = |c: &[i32]| {
            let mut sub: u8 = 0xFF;
            for &l in c {
                let va = l.abs();
                let j = if va == v0 {
                    0
                } else if va == v1 {
                    1
                } else {
                    2
                };
                let vt = VAR_TT3[j];
                sub &= if l < 0 { vt } else { vt ^ 0xFF };
            }
            sat_m &= !sub;
        };

        for c in t_list {
            apply_clause(c);
        }
        if let Some(v) = two_by_pair.get(&(v0, v1)) {
            for c in v {
                apply_clause(c);
            }
        }
        if let Some(v) = two_by_pair.get(&(v0, v2)) {
            for c in v {
                apply_clause(c);
            }
        }
        if let Some(v) = two_by_pair.get(&(v1, v2)) {
            for c in v {
                apply_clause(c);
            }
        }

        if sat_m == 0 {
            return None; // UNSAT
        }

        for out_j in 0..3 {
            let in_js = match out_j {
                0 => [1usize, 2],
                1 => [0, 2],
                _ => [0, 1],
            };
            let u_v = trip[in_js[0]];
            let w_v = trip[in_js[1]];
            let out_v = trip[out_j];
            let mut tt4 = [0u8; 4];
            let mut ok_f = true;
            for bu in 0..2u8 {
                for bw in 0..2u8 {
                    let mut cnt = 0u8;
                    let mut chosen_bo = 0u8;
                    for bo in 0..2u8 {
                        let b0 = if 0 == in_js[0] {
                            bu
                        } else if 0 == in_js[1] {
                            bw
                        } else {
                            bo
                        };
                        let b1 = if 1 == in_js[0] {
                            bu
                        } else if 1 == in_js[1] {
                            bw
                        } else {
                            bo
                        };
                        let b2 = if 2 == in_js[0] {
                            bu
                        } else if 2 == in_js[1] {
                            bw
                        } else {
                            bo
                        };
                        if ((sat_m >> ((b0 << 2) | (b1 << 1) | b2)) & 1) == 1 {
                            cnt += 1;
                            chosen_bo = bo;
                        }
                    }
                    if cnt != 1 {
                        ok_f = false;
                        break;
                    }
                    tt4[((bu << 1) | bw) as usize] = chosen_bo;
                }
                if !ok_f {
                    break;
                }
            }
            if ok_f {
                gates_by_in.entry((u_v, w_v)).or_default().push((out_v, tt4));
                if (tt4[0] ^ tt4[1] ^ tt4[2] ^ tt4[3]) == 1 {
                    gate_of_quad_out.insert(out_v, (u_v, w_v, tt4));
                }
            }
        }
    }

    Some((gates_by_in, gate_of_quad_out))
}

/// Fast pre-filter: check whether the CNF has at least 4 candidate 3-variable triples
/// with >= 3 clauses (necessary for deterministic 2-input half/full adders).
fn has_candidate_2input_gates(clauses: &[Vec<i32>]) -> bool {
    if clauses.len() > 150_000 {
        return false;
    }
    let mut trip_cnt: HashMap<(i32, i32, i32), u16> = HashMap::new();
    let mut pair_cnt: HashMap<(i32, i32), u16> = HashMap::new();
    for c in clauses {
        if c.len() == 2 {
            let a = c[0].abs();
            let b = c[1].abs();
            let p = if a < b { (a, b) } else { (b, a) };
            *pair_cnt.entry(p).or_insert(0) += 1;
        } else if c.len() == 3 {
            let mut vs = [c[0].abs(), c[1].abs(), c[2].abs()];
            vs.sort_unstable();
            *trip_cnt.entry((vs[0], vs[1], vs[2])).or_insert(0) += 1;
        }
    }
    let mut rich = 0usize;
    for (&(v0, v1, v2), &cnt) in &trip_cnt {
        let tot = cnt
            + *pair_cnt.get(&(v0, v1)).unwrap_or(&0)
            + *pair_cnt.get(&(v0, v2)).unwrap_or(&0)
            + *pair_cnt.get(&(v1, v2)).unwrap_or(&0);
        if tot >= 3 {
            rich += 1;
            if rich >= 4 {
                return true;
            }
        }
    }
    false
}

/// Attempt to certify an arithmetic miter via blind Z-adder telescoping and 2-adic/mod-2^k Hensel peeling.
/// Returns `Some((logger, contra_id))` on UNSAT proof emission, or `None` to fall through cleanly.
pub fn try_certify_z_adder_miter(
    clauses: &[Vec<i32>],
    _n_vars: i32,
) -> Option<(VeriPBLogger, usize)> {
    if !has_candidate_2input_gates(clauses) {
        return None;
    }

    let mut logger = VeriPBLogger::new(clauses.len());
    let mut fixed: HashMap<i32, u8> = HashMap::new();
    let mut equiv: HashMap<i32, (i32, u8)> = HashMap::new();
    let mut unit_eq_ids: HashMap<i32, (u8, usize, usize)> = HashMap::new();
    let mut equiv_eq_ids: HashMap<i32, (i32, u8, usize, usize)> = HashMap::new();

    let mut known_db_2cls: HashSet<(i32, i32)> = HashSet::new();
    for c in clauses {
        if c.len() == 2 {
            let mut pair = [c[0], c[1]];
            pair.sort_by_key(|&z| (z.abs(), z));
            known_db_2cls.insert((pair[0], pair[1]));
        }
    }

    let record_unit = |v: i32,
                       val: u8,
                       id_unit: Option<usize>,
                       fixed: &mut HashMap<i32, u8>,
                       unit_eq_ids: &mut HashMap<i32, (u8, usize, usize)>,
                       logger: &mut VeriPBLogger|
     -> bool {
        if let Some(&prev) = fixed.get(&v) {
            return prev != val;
        }
        fixed.insert(v, val);
        let (id_ge, id_le) = if val == 1 {
            let ig = id_unit.unwrap_or_else(|| logger.emit_rup_clause(&[v]));
            let il = logger.emit_pol_raw(&format!("~x{}", v));
            (ig, il)
        } else {
            let ig = logger.emit_pol_raw(&format!("x{}", v));
            let il = id_unit.unwrap_or_else(|| logger.emit_rup_clause(&[-v]));
            (ig, il)
        };
        unit_eq_ids.insert(v, (val, id_ge, id_le));
        false
    };

    let record_equiv = |hi: i32,
                        lo: i32,
                        fl: u8,
                        ids_pair: Option<(usize, usize)>,
                        fixed: &HashMap<i32, u8>,
                        equiv: &mut HashMap<i32, (i32, u8)>,
                        equiv_eq_ids: &mut HashMap<i32, (i32, u8, usize, usize)>,
                        logger: &mut VeriPBLogger| {
        if fixed.contains_key(&hi) || equiv.contains_key(&hi) {
            return;
        }
        equiv.insert(hi, (lo, fl));
        let (id_ge, id_le) = match ids_pair {
            Some(pair) => pair,
            None => {
                if fl == 0 {
                    (
                        logger.emit_rup_clause(&[hi, -lo]),
                        logger.emit_rup_clause(&[-hi, lo]),
                    )
                } else {
                    (
                        logger.emit_rup_clause(&[hi, lo]),
                        logger.emit_rup_clause(&[-hi, -lo]),
                    )
                }
            }
        };
        equiv_eq_ids.insert(hi, (lo, fl, id_ge, id_le));
    };

    let bcp_and_log = |mut work_cls: Vec<Vec<i32>>,
                       fixed: &mut HashMap<i32, u8>,
                       equiv: &mut HashMap<i32, (i32, u8)>,
                       unit_eq_ids: &mut HashMap<i32, (u8, usize, usize)>,
                       equiv_eq_ids: &mut HashMap<i32, (i32, u8, usize, usize)>,
                       known_db_2cls: &mut HashSet<(i32, i32)>,
                       logger: &mut VeriPBLogger|
     -> Result<Vec<Vec<i32>>, usize> {
        loop {
            match apply_fixed_and_equivs(&work_cls, fixed, equiv) {
                None => return Err(logger.emit_rup_clause(&[])),
                Some(next_cls) => work_cls = next_cls,
            }
            for c in &work_cls {
                if c.len() == 2 {
                    let key = (c[0], c[1]);
                    if known_db_2cls.insert(key) {
                        logger.emit_rup_clause(&[c[0], c[1]]);
                    }
                }
            }
            let mut chg = false;
            let cl2_set: HashSet<(i32, i32)> = work_cls
                .iter()
                .filter(|c| c.len() == 2)
                .map(|c| (c[0], c[1]))
                .collect();
            let norm2 = |x: i32, y: i32| -> (i32, i32) {
                if (x.abs(), x) <= (y.abs(), y) {
                    (x, y)
                } else {
                    (y, x)
                }
            };
            for c in &work_cls {
                if c.len() == 1 {
                    let v = c[0].abs();
                    let val = if c[0] > 0 { 1 } else { 0 };
                    if !fixed.contains_key(&v) {
                        if record_unit(v, val, None, fixed, unit_eq_ids, logger) {
                            return Err(logger.emit_rup_clause(&[]));
                        }
                        chg = true;
                    }
                } else if c.len() == 2 && c[0].abs() != c[1].abs() {
                    let (a, b) = (c[0], c[1]);
                    if cl2_set.contains(&norm2(-a, b)) {
                        let vb = b.abs();
                        let valb = if b > 0 { 1 } else { 0 };
                        if !fixed.contains_key(&vb) {
                            if record_unit(vb, valb, None, fixed, unit_eq_ids, logger) {
                                return Err(logger.emit_rup_clause(&[]));
                            }
                            chg = true;
                        }
                    }
                    if cl2_set.contains(&norm2(a, -b)) {
                        let va = a.abs();
                        let vala = if a > 0 { 1 } else { 0 };
                        if !fixed.contains_key(&va) {
                            if record_unit(va, vala, None, fixed, unit_eq_ids, logger) {
                                return Err(logger.emit_rup_clause(&[]));
                            }
                            chg = true;
                        }
                    }
                    if cl2_set.contains(&norm2(-a, -b)) {
                        let (va, vb) = (a.abs(), b.abs());
                        let (hi, lo) = if va > vb { (va, vb) } else { (vb, va) };
                        let fl = if (a > 0) == (b > 0) { 1 } else { 0 };
                        if !fixed.contains_key(&hi) && !equiv.contains_key(&hi) {
                            record_equiv(hi, lo, fl, None, fixed, equiv, equiv_eq_ids, logger);
                            chg = true;
                        }
                    }
                }
            }
            if !chg {
                return Ok(work_cls);
            }
        }
    };

    let mut work: Vec<Vec<i32>> = clauses.to_vec();

    // Phase 1: Blind gate congruence closure
    let mut had_congruence_merge = false;
    for _ in 0..10 {
        work = match bcp_and_log(
            work,
            &mut fixed,
            &mut equiv,
            &mut unit_eq_ids,
            &mut equiv_eq_ids,
            &mut known_db_2cls,
            &mut logger,
        ) {
            Ok(w) => w,
            Err(cid_u) => {
                if had_congruence_merge {
                    return Some((logger, cid_u));
                }
                return None;
            }
        };

        let Some((gates_by_in, _)) = scan_deterministic_2input_gates(&work) else {
            if had_congruence_merge {
                let cid_u = logger.emit_rup_clause(&[]);
                return Some((logger, cid_u));
            }
            return None;
        };

        let mut merged = false;
        for (&(u_v, w_v), glist) in &gates_by_in {
            if glist.len() >= 2 {
                for i in 0..glist.len() {
                    let (o1, t1) = glist[i];
                    let comp1 = [1 ^ t1[0], 1 ^ t1[1], 1 ^ t1[2], 1 ^ t1[3]];
                    for &(o2, t2) in &glist[(i + 1)..] {
                        if o1 != o2 && (t2 == t1 || t2 == comp1) {
                            let (hi, lo) = if o1 > o2 { (o1, o2) } else { (o2, o1) };
                            let fl = if t2 == t1 { 0 } else { 1 };
                            if !fixed.contains_key(&hi) && !equiv.contains_key(&hi) {
                                let (ig, il) = if fl == 0 {
                                    (
                                        derive_clause_over_cube(&mut logger, &[hi, -lo], &[u_v, w_v]),
                                        derive_clause_over_cube(&mut logger, &[-hi, lo], &[u_v, w_v]),
                                    )
                                } else {
                                    (
                                        derive_clause_over_cube(&mut logger, &[hi, lo], &[u_v, w_v]),
                                        derive_clause_over_cube(&mut logger, &[-hi, -lo], &[u_v, w_v]),
                                    )
                                };
                                record_equiv(
                                    hi,
                                    lo,
                                    fl,
                                    Some((ig, il)),
                                    &fixed,
                                    &mut equiv,
                                    &mut equiv_eq_ids,
                                    &mut logger,
                                );
                                merged = true;
                                had_congruence_merge = true;
                            }
                        }
                    }
                }
            }
        }
        if !merged {
            break;
        }
    }

    work = match bcp_and_log(
        work,
        &mut fixed,
        &mut equiv,
        &mut unit_eq_ids,
        &mut equiv_eq_ids,
        &mut known_db_2cls,
        &mut logger,
    ) {
        Ok(w) => w,
        Err(cid_u) => {
            if had_congruence_merge {
                return Some((logger, cid_u));
            }
            return None;
        }
    };

    let (gates_by_in, gate_of_out) = scan_deterministic_2input_gates(&work)?;

    // Phase 2: Extract half-adder and disjoint-OR full-adder Z-linear equations
    let mut base_z_eqs: Vec<(BTreeMap<i32, i128>, usize, usize)> = Vec::new();
    let mut xor_on_pair: HashMap<(i32, i32), Vec<(i32, [u8; 4])>> = HashMap::new();

    for (&(u_v, w_v), glist) in &gates_by_in {
        let mut xors: Vec<(i32, [u8; 4])> = Vec::new();
        let mut quads: Vec<(i32, [u8; 4])> = Vec::new();
        for &(o, t) in glist {
            let par = t[0] ^ t[1] ^ t[2] ^ t[3];
            if par == 0 && t[0] != t[1] && t[0] != t[2] {
                xors.push((o, t));
                xor_on_pair.entry((u_v, w_v)).or_default().push((o, t));
            } else if par == 1 {
                quads.push((o, t));
            }
        }
        for &(s_v, ts) in &xors {
            for &(c_v, tc) in &quads {
                let cnt_0 = tc.iter().filter(|&&b| b == 0).count();
                let spec_val = if cnt_0 == 1 { 0u8 } else { 1u8 };
                let idx_spec = tc.iter().position(|&b| b == spec_val).unwrap();
                let bu0 = (idx_spec >> 1) as u8;
                let bw0 = (idx_spec & 1) as u8;
                let opp_idx = (((1 - bu0) << 1) | (1 - bw0)) as usize;
                let s_flip = ts[opp_idx];

                let u_lit = if bu0 == 1 { u_v } else { -u_v };
                let w_lit = if bw0 == 1 { w_v } else { -w_v };
                let s_lit = if s_flip == 0 { s_v } else { -s_v };
                let c_lit = if spec_val == 1 { c_v } else { -c_v };

                let (id_ge, id_le) =
                    derive_half_adder_z_eq(&mut logger, u_lit, w_lit, s_lit, c_lit, &[u_v, w_v]);

                let mut row: BTreeMap<i32, i128> = BTreeMap::new();
                let mut rhs = 0i128;
                if bu0 == 1 {
                    *row.entry(u_v).or_insert(0) += 1;
                } else {
                    *row.entry(u_v).or_insert(0) -= 1;
                    rhs -= 1;
                }
                if bw0 == 1 {
                    *row.entry(w_v).or_insert(0) += 1;
                } else {
                    *row.entry(w_v).or_insert(0) -= 1;
                    rhs -= 1;
                }
                if s_flip == 0 {
                    *row.entry(s_v).or_insert(0) -= 1;
                } else {
                    *row.entry(s_v).or_insert(0) += 1;
                    rhs += 1;
                }
                if spec_val == 1 {
                    *row.entry(c_v).or_insert(0) -= 2;
                } else {
                    *row.entry(c_v).or_insert(0) += 2;
                    rhs += 2;
                }
                row.insert(0, rhs);
                base_z_eqs.push((row, id_ge, id_le));
            }
        }
    }

    for (&cout_v, &(c1_v, c2_v, t_out)) in &gate_of_out {
        if let (Some(&(p1a, p1b, t1)), Some(&(p2a, p2b, t2))) =
            (gate_of_out.get(&c1_v), gate_of_out.get(&c2_v))
        {
            let p1 = (p1a, p1b);
            let p2 = (p2a, p2b);
            let mut found_dc = false;
            for &(pa, pb, first_is_1) in &[(p1, p2, true), (p2, p1, false)] {
                if let Some(xlist) = xor_on_pair.get(&pa) {
                    for &(x_wire, tx) in xlist {
                        if pb.0 == x_wire || pb.1 == x_wire {
                            let mut reachable = [false; 4];
                            let x_pos = if pb.0 == x_wire { 0 } else { 1 };
                            let ta_use = if first_is_1 { t1 } else { t2 };
                            let tb_use = if first_is_1 { t2 } else { t1 };
                            for ba in 0..2usize {
                                for bb in 0..2usize {
                                    let bx = tx[(ba << 1) | bb] as usize;
                                    let v_a = ta_use[(ba << 1) | bb] as usize;
                                    for bo in 0..2usize {
                                        let v_b = tb_use[if x_pos == 0 {
                                            (bx << 1) | bo
                                        } else {
                                            (bo << 1) | bx
                                        }] as usize;
                                        let (r1, r2) = if first_is_1 { (v_a, v_b) } else { (v_b, v_a) };
                                        reachable[(r1 << 1) | r2] = true;
                                    }
                                }
                            }
                            if reachable.iter().filter(|&&b| b).count() == 3 {
                                let excl_idx = reachable.iter().position(|&b| !b).unwrap();
                                let excl0 = (excl_idx >> 1) as u8;
                                let excl1 = (excl_idx & 1) as u8;
                                let c1_eff = if excl0 == 1 { c1_v } else { -c1_v };
                                let c2_eff = if excl1 == 1 { c2_v } else { -c2_v };
                                let out_at_00 =
                                    t_out[(((1 - excl0) << 1) | (1 - excl1)) as usize];
                                let cout_eff = if out_at_00 == 0 { cout_v } else { -cout_v };
                                let mut fa_in_set: BTreeSet<i32> = BTreeSet::new();
                                fa_in_set.insert(pa.0);
                                fa_in_set.insert(pa.1);
                                if pb.0 != x_wire {
                                    fa_in_set.insert(pb.0);
                                }
                                if pb.1 != x_wire {
                                    fa_in_set.insert(pb.1);
                                }
                                let fa_in: Vec<i32> = fa_in_set.into_iter().collect();
                                let (ig, il) = derive_disjoint_or_z_eq(
                                    &mut logger,
                                    c1_eff,
                                    c2_eff,
                                    cout_eff,
                                    &fa_in,
                                );

                                let mut row: BTreeMap<i32, i128> = BTreeMap::new();
                                let mut rhs = 0i128;
                                for &(v_x, eff_l, sgn) in
                                    &[(c1_v, c1_eff, 1i128), (c2_v, c2_eff, 1), (cout_v, cout_eff, -1)]
                                {
                                    if eff_l > 0 {
                                        *row.entry(v_x).or_insert(0) += sgn;
                                    } else {
                                        *row.entry(v_x).or_insert(0) -= sgn;
                                        rhs -= sgn;
                                    }
                                }
                                row.insert(0, rhs);
                                base_z_eqs.push((row, ig, il));
                                found_dc = true;
                                break;
                            }
                        }
                    }
                }
                if found_dc {
                    break;
                }
            }
        }
    }

    if base_z_eqs.len() < 4 {
        return None;
    }

    // Phase 3: Exact sparse rational RREF + 2-adic/GCD/Archimedean bit-peeling
    let mut eq_bank: Vec<(usize, usize)> = base_z_eqs.iter().map(|&(_, ig, il)| (ig, il)).collect();
    let mut unit_bank_idx: HashMap<i32, usize> = HashMap::new();
    let mut equiv_bank_idx: HashMap<i32, usize> = HashMap::new();

    let mut get_unit_eq_idx = |v: i32,
                               unit_eq_ids: &HashMap<i32, (u8, usize, usize)>,
                               eq_bank: &mut Vec<(usize, usize)>|
     -> usize {
        if let Some(&idx) = unit_bank_idx.get(&v) {
            idx
        } else {
            let &(_, ig, il) = &unit_eq_ids[&v];
            let idx = eq_bank.len();
            eq_bank.push((ig, il));
            unit_bank_idx.insert(v, idx);
            idx
        }
    };

    let mut get_equiv_eq_idx = |u_hi: i32,
                                equiv_eq_ids: &HashMap<i32, (i32, u8, usize, usize)>,
                                eq_bank: &mut Vec<(usize, usize)>|
     -> usize {
        if let Some(&idx) = equiv_bank_idx.get(&u_hi) {
            idx
        } else {
            let &(_, _, ig, il) = &equiv_eq_ids[&u_hi];
            let idx = eq_bank.len();
            eq_bank.push((ig, il));
            equiv_bank_idx.insert(u_hi, idx);
            idx
        }
    };

    let emit_int_combination = |comb_map: &BTreeMap<usize, Rat>,
                                scale_int: i128,
                                side_ge: bool,
                                eq_bank: &[(usize, usize)],
                                logger: &mut VeriPBLogger|
     -> Option<usize> {
        let mut rpn = String::new();
        let mut first = true;
        for (&e_id, &frac_c) in comb_map {
            let mult = frac_c.mul_int_exact(scale_int)?;
            if mult == 0 {
                continue;
            }
            let (ig, il) = eq_bank[e_id];
            let use_id = if side_ge {
                if mult > 0 { ig } else { il }
            } else if mult > 0 {
                il
            } else {
                ig
            };
            let absm = mult.unsigned_abs();
            if !first {
                rpn.push(' ');
            }
            if absm == 1 {
                let _ = write!(rpn, "{}", use_id);
            } else {
                let _ = write!(rpn, "{} {} *", use_id, absm);
            }
            if !first {
                rpn.push_str(" +");
            }
            first = false;
        }
        Some(logger.emit_pol_raw(&rpn))
    };

    let mut zeq_occ: HashMap<i32, usize> = HashMap::new();
    for (r_d, _, _) in &base_z_eqs {
        for (&k, &val) in r_d {
            if k != 0 && val != 0 {
                *zeq_occ.entry(k).or_insert(0) += 1;
            }
        }
    }

    let col_prio = |k: i32| -> (u8, i32) {
        (if *zeq_occ.get(&k).unwrap_or(&0) >= 2 { 1 } else { 0 }, k)
    };

    // pivots: lead_var -> (row: BTreeMap<i32, Rat>, comb: BTreeMap<usize, Rat>)
    let mut pivots: HashMap<i32, (BTreeMap<i32, Rat>, BTreeMap<usize, Rat>)> = HashMap::new();

    let insert_row = |mut row: BTreeMap<i32, Rat>,
                      mut comb: BTreeMap<usize, Rat>,
                      pivots: &mut HashMap<i32, (BTreeMap<i32, Rat>, BTreeMap<usize, Rat>)>,
                      eq_bank: &[(usize, usize)],
                      logger: &mut VeriPBLogger|
     -> Option<Option<usize>> {
        row.entry(0).or_insert(Rat::zero());
        loop {
            let lead_opt = row
                .iter()
                .filter(|&(&k, &v)| k != 0 && !v.is_zero())
                .map(|(&k, _)| k)
                .max_by_key(|&k| col_prio(k));
            let Some(lead) = lead_opt else {
                let r0 = *row.get(&0).unwrap_or(&Rat::zero());
                if !r0.is_zero() {
                    let mut lcm_d = r0.den;
                    for &c_val in comb.values() {
                        lcm_d = lcm_i128(lcm_d, c_val.den)?;
                    }
                    let r_int = r0.mul_int_exact(lcm_d)?;
                    let cid =
                        emit_int_combination(&comb, lcm_d, r_int < 0, eq_bank, logger)?;
                    return Some(Some(cid));
                }
                return Some(None);
            };
            if let Some((prow, pcomb)) = pivots.get(&lead) {
                let fac = row[&lead];
                for (&k, &pv) in prow {
                    let cur = *row.get(&k).unwrap_or(&Rat::zero());
                    let nv = cur.sub(fac.mul(pv)?)?;
                    if k != 0 && nv.is_zero() {
                        row.remove(&k);
                    } else {
                        row.insert(k, nv);
                    }
                }
                for (&e, &pc) in pcomb {
                    let cur = *comb.get(&e).unwrap_or(&Rat::zero());
                    let nc = cur.sub(fac.mul(pc)?)?;
                    if nc.is_zero() {
                        comb.remove(&e);
                    } else {
                        comb.insert(e, nc);
                    }
                }
            } else {
                let inv_l = row[&lead].inv()?;
                let mut nrow: BTreeMap<i32, Rat> = BTreeMap::new();
                for (&k, &v) in &row {
                    let nv = v.mul(inv_l)?;
                    if k == 0 || !nv.is_zero() {
                        nrow.insert(k, nv);
                    }
                }
                let mut ncomb: BTreeMap<usize, Rat> = BTreeMap::new();
                for (&e, &c) in &comb {
                    let nc = c.mul(inv_l)?;
                    if !nc.is_zero() {
                        ncomb.insert(e, nc);
                    }
                }
                let pkeys: Vec<i32> = pivots.keys().copied().collect();
                for pk in pkeys {
                    let has_lead = pivots[&pk].0.contains_key(&lead);
                    if has_lead {
                        let (prow, pcomb) = pivots.get_mut(&pk).unwrap();
                        let f2 = prow[&lead];
                        for (&k, &nv2) in &nrow {
                            let cur = *prow.get(&k).unwrap_or(&Rat::zero());
                            let val2 = cur.sub(f2.mul(nv2)?)?;
                            if k != 0 && val2.is_zero() {
                                prow.remove(&k);
                            } else {
                                prow.insert(k, val2);
                            }
                        }
                        for (&e, &nc2) in &ncomb {
                            let cur = *pcomb.get(&e).unwrap_or(&Rat::zero());
                            let vc2 = cur.sub(f2.mul(nc2)?)?;
                            if vc2.is_zero() {
                                pcomb.remove(&e);
                            } else {
                                pcomb.insert(e, vc2);
                            }
                        }
                    }
                }
                pivots.insert(lead, (nrow, ncomb));
                return Some(None);
            }
        }
    };

    for (idx_e, (r_d, _, _)) in base_z_eqs.iter().enumerate() {
        let mut row: BTreeMap<i32, Rat> = BTreeMap::new();
        for (&k, &v) in r_d {
            if k == 0 || v != 0 {
                row.insert(k, Rat::from_int(v));
            }
        }
        let mut comb: BTreeMap<usize, Rat> = BTreeMap::new();
        comb.insert(idx_e, Rat::from_int(1));
        if let Some(cid_contra) = insert_row(row, comb, &mut pivots, &eq_bank, &mut logger)? {
            return Some((logger, cid_contra));
        }
    }

    let mut touched_vars: HashSet<i32> = HashSet::new();
    for &v in fixed.keys() {
        touched_vars.insert(v);
    }
    for &v in equiv.keys() {
        touched_vars.insert(v);
    }

    for _peel_iter in 1..80 {
        if !touched_vars.is_empty() {
            let affected: Vec<i32> = pivots
                .iter()
                .filter(|&(&ld, (prow, _))| {
                    touched_vars.contains(&ld)
                        || prow.keys().any(|&k| k != 0 && touched_vars.contains(&k))
                })
                .map(|(&ld, _)| ld)
                .collect();
            let mut reinsert: Vec<(BTreeMap<i32, Rat>, BTreeMap<usize, Rat>)> =
                Vec::with_capacity(affected.len());
            for ld in affected {
                let (mut cur_row, mut cur_comb) = pivots.remove(&ld).unwrap();
                let mut changed_v = true;
                while changed_v {
                    changed_v = false;
                    let cols: Vec<i32> = cur_row
                        .iter()
                        .filter(|&(&k, &v)| k != 0 && !v.is_zero())
                        .map(|(&k, _)| k)
                        .collect();
                    for k in cols {
                        let coeff = match cur_row.get(&k) {
                            Some(&c) if !c.is_zero() => c,
                            _ => continue,
                        };
                        if let Some(&(lo, fl)) = equiv.get(&k) {
                            let e_idx = get_equiv_eq_idx(k, &equiv_eq_ids, &mut eq_bank);
                            cur_row.remove(&k);
                            if fl == 0 {
                                let nv = cur_row
                                    .get(&lo)
                                    .copied()
                                    .unwrap_or(Rat::zero())
                                    .add(coeff)?;
                                if nv.is_zero() {
                                    cur_row.remove(&lo);
                                } else {
                                    cur_row.insert(lo, nv);
                                }
                            } else {
                                let nv = cur_row
                                    .get(&lo)
                                    .copied()
                                    .unwrap_or(Rat::zero())
                                    .sub(coeff)?;
                                if nv.is_zero() {
                                    cur_row.remove(&lo);
                                } else {
                                    cur_row.insert(lo, nv);
                                }
                                let r0 = cur_row
                                    .get(&0)
                                    .copied()
                                    .unwrap_or(Rat::zero())
                                    .sub(coeff)?;
                                cur_row.insert(0, r0);
                            }
                            let nc = cur_comb
                                .get(&e_idx)
                                .copied()
                                .unwrap_or(Rat::zero())
                                .sub(coeff)?;
                            if nc.is_zero() {
                                cur_comb.remove(&e_idx);
                            } else {
                                cur_comb.insert(e_idx, nc);
                            }
                            changed_v = true;
                        } else if let Some(&val) = fixed.get(&k) {
                            let u_idx = get_unit_eq_idx(k, &unit_eq_ids, &mut eq_bank);
                            cur_row.remove(&k);
                            if val == 1 {
                                let r0 = cur_row
                                    .get(&0)
                                    .copied()
                                    .unwrap_or(Rat::zero())
                                    .sub(coeff)?;
                                cur_row.insert(0, r0);
                            }
                            let nc = cur_comb
                                .get(&u_idx)
                                .copied()
                                .unwrap_or(Rat::zero())
                                .sub(coeff)?;
                            if nc.is_zero() {
                                cur_comb.remove(&u_idx);
                            } else {
                                cur_comb.insert(u_idx, nc);
                            }
                            changed_v = true;
                        }
                    }
                }
                reinsert.push((cur_row, cur_comb));
            }
            touched_vars.clear();
            for (r_d, c_d) in reinsert {
                if let Some(cid_contra) = insert_row(r_d, c_d, &mut pivots, &eq_bank, &mut logger)? {
                    return Some((logger, cid_contra));
                }
            }
        }

        let prev_f: HashSet<i32> = fixed.keys().copied().collect();
        let prev_e: HashSet<i32> = equiv.keys().copied().collect();
        let mut found_new = false;

        let p_leads: Vec<i32> = {
            let mut ks: Vec<i32> = pivots.keys().copied().collect();
            ks.sort_unstable();
            ks
        };

        for ld in p_leads {
            let (prow, pcomb) = match pivots.get(&ld) {
                Some(pair) => pair.clone(),
                None => continue,
            };
            let cols: Vec<i32> = prow
                .iter()
                .filter(|&(&k, &v)| k != 0 && !v.is_zero())
                .map(|(&k, _)| k)
                .collect();
            if cols.is_empty() || cols.len() > 80 {
                continue;
            }
            let mut lcm_d = 1i128;
            let mut ok_lcm = true;
            for &val in prow.values().chain(pcomb.values()) {
                match lcm_i128(lcm_d, val.den) {
                    Some(l) => lcm_d = l,
                    None => {
                        ok_lcm = false;
                        break;
                    }
                }
            }
            if !ok_lcm {
                continue;
            }

            let mut i_coeffs: Vec<(i32, i128)> = Vec::with_capacity(cols.len());
            let mut ok_ic = true;
            for &k in &cols {
                match prow[&k].mul_int_exact(lcm_d) {
                    Some(iv) => i_coeffs.push((k, iv)),
                    None => {
                        ok_ic = false;
                        break;
                    }
                }
            }
            let i_rhs_opt = prow
                .get(&0)
                .copied()
                .unwrap_or(Rat::zero())
                .mul_int_exact(lcm_d);
            if !ok_ic || i_rhs_opt.is_none() {
                continue;
            }
            let mut i_rhs = i_rhs_opt.unwrap();

            let mut g_all = 0u128;
            for &(_, cv) in &i_coeffs {
                g_all = gcd_u128(g_all, cv.unsigned_abs());
            }

            if g_all > 1 && (i_rhs.rem_euclid(g_all as i128) != 0) {
                let id_raw_ge =
                    emit_int_combination(&pcomb, lcm_d, true, &eq_bank, &mut logger)?;
                let id_raw_le =
                    emit_int_combination(&pcomb, lcm_d, false, &eq_bank, &mut logger)?;
                let id_div_ge = logger.emit_pol_raw(&format!("{} {} d", id_raw_ge, g_all));
                let id_div_le = logger.emit_pol_raw(&format!("{} {} d", id_raw_le, g_all));
                let cid_contra = logger.emit_pol_add2(id_div_ge, id_div_le, false);
                return Some((logger, cid_contra));
            }

            let mut row_ids: Option<(usize, usize)> = None;
            let mut ensure_row_ids = |logger: &mut VeriPBLogger| -> Option<(usize, usize)> {
                if let Some(pair) = row_ids {
                    return Some(pair);
                }
                let mut rg = emit_int_combination(&pcomb, lcm_d, true, &eq_bank, logger)?;
                let mut rl = emit_int_combination(&pcomb, lcm_d, false, &eq_bank, logger)?;
                if g_all > 1 {
                    rg = logger.emit_pol_raw(&format!("{} {} d", rg, g_all));
                    rl = logger.emit_pol_raw(&format!("{} {} d", rl, g_all));
                }
                row_ids = Some((rg, rl));
                Some((rg, rl))
            };

            if g_all > 1 {
                let gi = g_all as i128;
                for &mut (_, ref mut cv) in &mut i_coeffs {
                    *cv /= gi;
                }
                i_rhs /= gi;
            }

            let min_s: i128 = i_coeffs
                .iter()
                .filter(|&&(_, c)| c < 0)
                .map(|&(_, c)| c)
                .sum();
            let max_s: i128 = i_coeffs
                .iter()
                .filter(|&&(_, c)| c > 0)
                .map(|&(_, c)| c)
                .sum();

            if i_rhs < min_s || i_rhs > max_s {
                let (rg, rl) = ensure_row_ids(&mut logger)?;
                let cid_c = if i_rhs > max_s {
                    let mut rpn = format!("{}", rg);
                    for &(k, c) in &i_coeffs {
                        if c > 0 {
                            let _ = write!(rpn, " ~x{} {} * +", k, c);
                        } else {
                            let _ = write!(rpn, " x{} {} * +", k, -c);
                        }
                    }
                    logger.emit_pol_raw(&rpn)
                } else {
                    let mut rpn = format!("{}", rl);
                    for &(k, c) in &i_coeffs {
                        if c < 0 {
                            let _ = write!(rpn, " ~x{} {} * +", k, -c);
                        } else {
                            let _ = write!(rpn, " x{} {} * +", k, c);
                        }
                    }
                    logger.emit_pol_raw(&rpn)
                };
                return Some((logger, cid_c));
            }

            let odd_vars: Vec<i32> = i_coeffs
                .iter()
                .filter(|&&(_, c)| (c.unsigned_abs() & 1) == 1)
                .map(|&(k, _)| k)
                .collect();
            let rhs_mod2 = (i_rhs.rem_euclid(2)) as u8;

            if odd_vars.is_empty() && rhs_mod2 == 1 {
                let (rg, rl) = ensure_row_ids(&mut logger)?;
                let d_ge = logger.emit_pol_raw(&format!("{} 2 d", rg));
                let d_le = logger.emit_pol_raw(&format!("{} 2 d", rl));
                let cid_c = logger.emit_pol_add2(d_ge, d_le, false);
                return Some((logger, cid_c));
            } else if odd_vars.len() == 1 {
                let v0 = odd_vars[0];
                if !fixed.contains_key(&v0) {
                    let (rg, rl) = ensure_row_ids(&mut logger)?;
                    let lit_tok = if rhs_mod2 == 1 {
                        format!("x{}", v0)
                    } else {
                        format!("~x{}", v0)
                    };
                    let p_a = logger.emit_pol_raw(&format!("{} {} + 2 d", rg, lit_tok));
                    let p_b = logger.emit_pol_raw(&format!("{} {} + 2 d", rl, lit_tok));
                    let id_u = logger.emit_pol_add2(p_a, p_b, false);
                    record_unit(
                        v0,
                        rhs_mod2,
                        Some(id_u),
                        &mut fixed,
                        &mut unit_eq_ids,
                        &mut logger,
                    );
                    found_new = true;
                }
            } else if odd_vars.len() == 2 {
                let (v1, v2) = if odd_vars[0] < odd_vars[1] {
                    (odd_vars[0], odd_vars[1])
                } else {
                    (odd_vars[1], odd_vars[0])
                };
                if !fixed.contains_key(&v2) && !equiv.contains_key(&v2) {
                    let (rg, rl) = ensure_row_ids(&mut logger)?;
                    if rhs_mod2 == 1 {
                        let pa1 = logger.emit_pol_raw(&format!("{} x{} + x{} + 2 d", rg, v1, v2));
                        let pb1 = logger.emit_pol_raw(&format!("{} x{} + x{} + 2 d", rl, v1, v2));
                        let id_pos = logger.emit_pol_add2(pa1, pb1, false);

                        let pa2 =
                            logger.emit_pol_raw(&format!("{} ~x{} + ~x{} + 2 d", rg, v1, v2));
                        let pb2 =
                            logger.emit_pol_raw(&format!("{} ~x{} + ~x{} + 2 d", rl, v1, v2));
                        let id_neg = logger.emit_pol_add2(pa2, pb2, false);
                        record_equiv(
                            v2,
                            v1,
                            1,
                            Some((id_pos, id_neg)),
                            &fixed,
                            &mut equiv,
                            &mut equiv_eq_ids,
                            &mut logger,
                        );
                    } else {
                        let pa1 =
                            logger.emit_pol_raw(&format!("{} ~x{} + x{} + 2 d", rg, v1, v2));
                        let pb1 =
                            logger.emit_pol_raw(&format!("{} ~x{} + x{} + 2 d", rl, v1, v2));
                        let id_ge21 = logger.emit_pol_add2(pa1, pb1, false);

                        let pa2 =
                            logger.emit_pol_raw(&format!("{} x{} + ~x{} + 2 d", rg, v1, v2));
                        let pb2 =
                            logger.emit_pol_raw(&format!("{} x{} + ~x{} + 2 d", rl, v1, v2));
                        let id_le21 = logger.emit_pol_add2(pa2, pb2, false);
                        record_equiv(
                            v2,
                            v1,
                            0,
                            Some((id_ge21, id_le21)),
                            &fixed,
                            &mut equiv,
                            &mut equiv_eq_ids,
                            &mut logger,
                        );
                    }
                    found_new = true;
                }
            }
        }

        work = match bcp_and_log(
            work,
            &mut fixed,
            &mut equiv,
            &mut unit_eq_ids,
            &mut equiv_eq_ids,
            &mut known_db_2cls,
            &mut logger,
        ) {
            Ok(w) => w,
            Err(cid_u) => return Some((logger, cid_u)),
        };

        for &v in fixed.keys() {
            if !prev_f.contains(&v) {
                touched_vars.insert(v);
            }
        }
        for &v in equiv.keys() {
            if !prev_e.contains(&v) {
                touched_vars.insert(v);
            }
        }
        if !found_new && touched_vars.is_empty() {
            break;
        }
    }

    None
}

/// Generate a scrambled truncated mod-`2^keep_lsb_bits` Schoolbook-vs-Wallace multiplier miter
/// (comparing only the low `keep_lsb_bits` product bits without MSBs).
pub fn gen_truncated_schoolbook_vs_wallace_miter(
    k_bits: usize,
    keep_lsb_bits: usize,
    seed: u64,
) -> (i32, Vec<Vec<i32>>) {
    let mut top: i32 = 0;
    let new_var = |top: &mut i32| -> i32 {
        *top += 1;
        *top
    };
    let mut clauses: Vec<Vec<i32>> = Vec::new();

    let a_in: Vec<i32> = (0..k_bits).map(|_| new_var(&mut top)).collect();
    let b_in: Vec<i32> = (0..k_bits).map(|_| new_var(&mut top)).collect();

    let new_and = |u: i32, v: i32, top: &mut i32, clauses: &mut Vec<Vec<i32>>| -> i32 {
        *top += 1;
        let z = *top;
        clauses.push(vec![-z, u]);
        clauses.push(vec![-z, v]);
        clauses.push(vec![z, -u, -v]);
        z
    };
    let new_xor = |u: i32, v: i32, top: &mut i32, clauses: &mut Vec<Vec<i32>>| -> i32 {
        *top += 1;
        let z = *top;
        clauses.push(vec![-u, -v, -z]);
        clauses.push(vec![u, v, -z]);
        clauses.push(vec![-u, v, z]);
        clauses.push(vec![u, -v, z]);
        z
    };
    let new_or = |u: i32, v: i32, top: &mut i32, clauses: &mut Vec<Vec<i32>>| -> i32 {
        *top += 1;
        let z = *top;
        clauses.push(vec![z, -u]);
        clauses.push(vec![z, -v]);
        clauses.push(vec![-z, u, v]);
        z
    };

    let half_adder = |u: i32, v: i32, top: &mut i32, clauses: &mut Vec<Vec<i32>>| -> (i32, i32) {
        (new_xor(u, v, top, clauses), new_and(u, v, top, clauses))
    };
    let full_adder =
        |u: i32, v: i32, w: i32, top: &mut i32, clauses: &mut Vec<Vec<i32>>| -> (i32, i32) {
            let (t, c1) = half_adder(u, v, top, clauses);
            let (s, c2) = half_adder(t, w, top, clauses);
            (s, new_or(c1, c2, top, clauses))
        };

    // Schoolbook ripple multiplier
    let mut acc_a: Vec<i32> = (0..k_bits)
        .map(|j| new_and(a_in[0], b_in[j], &mut top, &mut clauses))
        .collect();
    let mut out_a: Vec<i32> = Vec::new();
    for i in 1..k_bits {
        out_a.push(acc_a[0]);
        let vec1: Vec<i32> = acc_a[1..].to_vec();
        let vec2: Vec<i32> = (0..k_bits)
            .map(|j| new_and(a_in[i], b_in[j], &mut top, &mut clauses))
            .collect();
        let n_m = vec1.len().max(vec2.len());
        let mut res = Vec::with_capacity(n_m + 1);
        let mut carry: Option<i32> = None;
        for idx in 0..n_m {
            let x = vec1.get(idx).copied();
            let y = vec2.get(idx).copied();
            let s = match (x, y) {
                (Some(vx), Some(vy)) => {
                    let (s, c) = match carry {
                        None => half_adder(vx, vy, &mut top, &mut clauses),
                        Some(vc) => full_adder(vx, vy, vc, &mut top, &mut clauses),
                    };
                    carry = Some(c);
                    s
                }
                (Some(v), None) | (None, Some(v)) => match carry {
                    None => v,
                    Some(vc) => {
                        let (s, c) = half_adder(v, vc, &mut top, &mut clauses);
                        carry = Some(c);
                        s
                    }
                },
                (None, None) => unreachable!(),
            };
            res.push(s);
        }
        if let Some(c) = carry {
            res.push(c);
        }
        acc_a = res;
    }
    out_a.extend_from_slice(&acc_a);
    out_a.truncate(2 * k_bits);

    // Shuffled Wallace-tree multiplier
    let mut rng_state = seed ^ 0x9E37_79B9_7F4A_7C15;
    let mut next_u64 = || -> u64 {
        rng_state ^= rng_state << 13;
        rng_state ^= rng_state >> 7;
        rng_state ^= rng_state << 17;
        rng_state
    };

    let mut order_ij: Vec<(usize, usize)> = Vec::with_capacity(k_bits * k_bits);
    for i in 0..k_bits {
        for j in 0..k_bits {
            order_ij.push((i, j));
        }
    }
    for i in (1..order_ij.len()).rev() {
        let j = (next_u64() as usize) % (i + 1);
        order_ij.swap(i, j);
    }

    let mut cols: Vec<Vec<i32>> = vec![Vec::new(); 2 * k_bits + 2];
    for (i, j) in order_ij {
        cols[i + j].push(new_and(a_in[i], b_in[j], &mut top, &mut clauses));
    }
    let mut out_b: Vec<i32> = Vec::with_capacity(2 * k_bits);
    for col_idx in 0..(2 * k_bits) {
        let mut bkt = std::mem::take(&mut cols[col_idx]);
        while bkt.len() >= 3 {
            let (s, c) = full_adder(bkt[0], bkt[1], bkt[2], &mut top, &mut clauses);
            bkt.drain(0..3);
            bkt.push(s);
            cols[col_idx + 1].push(c);
        }
        if bkt.len() == 2 {
            let (s, c) = half_adder(bkt[0], bkt[1], &mut top, &mut clauses);
            bkt.clear();
            bkt.push(s);
            cols[col_idx + 1].push(c);
        }
        out_b.push(bkt[0]);
    }

    // Compare ONLY the low `keep_lsb_bits` product bits (truncated mod 2^keep_lsb_bits miter!)
    let n_cmp = keep_lsb_bits.min(2 * k_bits).max(1);
    let mut cur: Vec<i32> = (0..n_cmp)
        .map(|t| new_xor(out_a[t], out_b[t], &mut top, &mut clauses))
        .collect();
    while cur.len() > 3 {
        top += 1;
        let aux = top;
        clauses.push(vec![cur[0], cur[1], aux]);
        let mut nxt = Vec::with_capacity(cur.len() - 1);
        nxt.push(-aux);
        nxt.extend_from_slice(&cur[2..]);
        cur = nxt;
    }
    clauses.push(cur);

    // Scramble variable IDs, polarities, literal order, and clause order
    let n_vars = top;
    let mut perm: Vec<i32> = (1..=n_vars).collect();
    for i in (1..perm.len()).rev() {
        let j = (next_u64() as usize) % (i + 1);
        perm.swap(i, j);
    }
    let signs: Vec<i32> = (0..=n_vars)
        .map(|_| if (next_u64() & 1) == 0 { 1 } else { -1 })
        .collect();

    let mut scrambled: Vec<Vec<i32>> = Vec::with_capacity(clauses.len());
    for c in clauses {
        let mut sc: Vec<i32> = c
            .into_iter()
            .map(|lit| {
                let v = lit.abs() as usize;
                let nv = perm[v - 1];
                let sg = signs[v] * if lit > 0 { 1 } else { -1 };
                if sg > 0 { nv } else { -nv }
            })
            .collect();
        for i in (1..sc.len()).rev() {
            let j = (next_u64() as usize) % (i + 1);
            sc.swap(i, j);
        }
        scrambled.push(sc);
    }
    for i in (1..scrambled.len()).rev() {
        let j = (next_u64() as usize) % (i + 1);
        scrambled.swap(i, j);
    }

    (n_vars, scrambled)
}
