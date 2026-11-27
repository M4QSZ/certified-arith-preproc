use std::collections::{BTreeMap, HashMap, HashSet};
use std::env;
use std::fs;
use std::io::{self, Read};
use std::time::Instant;

// Literal encoding: lit = 2 * var + (if neg { 1 } else { 0 }), var in 0..n
#[inline(always)]
fn mk_lit(var: usize, neg: bool) -> u32 {
    ((var as u32) << 1) | (if neg { 1 } else { 0 })
}

#[inline(always)]
fn lit_var(lit: u32) -> usize {
    (lit >> 1) as usize
}

#[inline(always)]
fn lit_neg(lit: u32) -> bool {
    (lit & 1) == 1
}

#[inline(always)]
fn neg_lit(lit: u32) -> u32 {
    lit ^ 1
}

fn lit_to_pbp(lit: u32) -> String {
    let v = lit_var(lit) + 1;
    if lit_neg(lit) {
        format!("~x{v}")
    } else {
        format!("x{v}")
    }
}

fn var_lit_to_pbp(var1: usize, pos: bool) -> String {
    if pos {
        format!("x{var1}")
    } else {
        format!("~x{var1}")
    }
}

// Monomial encoding for RM(4, n) with n <= 1023 (10 bits per variable):
// deg 0 (const 1):     0
// deg 1 (i):           (1 << 40) | i
// deg 2 (i < j):       (2 << 40) | (i << 10) | j
// deg 3 (i < j < k):   (3 << 40) | (i << 20) | (j << 10) | k
// deg 4 (i<j<k<l):     (4 << 40) | (i << 30) | (j << 20) | (k << 10) | l
#[inline(always)]
fn mono0() -> u64 {
    0
}
#[inline(always)]
fn mono1(i: usize) -> u64 {
    (1u64 << 40) | (i as u64)
}
#[inline(always)]
fn mono2(mut i: usize, mut j: usize) -> u64 {
    if i > j {
        std::mem::swap(&mut i, &mut j);
    }
    (2u64 << 40) | ((i as u64) << 10) | (j as u64)
}
#[inline(always)]
fn mono3(a: usize, b: usize, c: usize) -> u64 {
    let mut v = [a, b, c];
    v.sort_unstable();
    (3u64 << 40) | ((v[0] as u64) << 20) | ((v[1] as u64) << 10) | (v[2] as u64)
}
#[inline(always)]
fn mono4(a: usize, b: usize, c: usize, d: usize) -> u64 {
    let mut v = [a, b, c, d];
    v.sort_unstable();
    (4u64 << 40)
        | ((v[0] as u64) << 30)
        | ((v[1] as u64) << 20)
        | ((v[2] as u64) << 10)
        | (v[3] as u64)
}

#[inline(always)]
fn mono_deg(m: u64) -> u64 {
    m >> 40
}

#[inline(always)]
fn mono_vars4(m: u64) -> ([usize; 4], usize) {
    match m >> 40 {
        0 => ([0, 0, 0, 0], 0),
        1 => ([(m & 0x3ff) as usize, 0, 0, 0], 1),
        2 => (
            [((m >> 10) & 0x3ff) as usize, (m & 0x3ff) as usize, 0, 0],
            2,
        ),
        3 => (
            [
                ((m >> 20) & 0x3ff) as usize,
                ((m >> 10) & 0x3ff) as usize,
                (m & 0x3ff) as usize,
                0,
            ],
            3,
        ),
        _ => (
            [
                ((m >> 30) & 0x3ff) as usize,
                ((m >> 20) & 0x3ff) as usize,
                ((m >> 10) & 0x3ff) as usize,
                (m & 0x3ff) as usize,
            ],
            4,
        ),
    }
}

/// XOR two sorted descending monomial vectors in GF(2).
fn xor_poly_desc(a: &[u64], b: &[u64]) -> Vec<u64> {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        if a[i] > b[j] {
            out.push(a[i]);
            i += 1;
        } else if b[j] > a[i] {
            out.push(b[j]);
            j += 1;
        } else {
            i += 1;
            j += 1;
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
    out
}

/// XOR two sorted ascending usize provenance lists in GF(2).
fn xor_comb_asc(a: &[usize], b: &[usize]) -> Vec<usize> {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        if a[i] < b[j] {
            out.push(a[i]);
            i += 1;
        } else if b[j] < a[i] {
            out.push(b[j]);
            j += 1;
        } else {
            i += 1;
            j += 1;
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
    out
}

/// Multiply a deg<=2 (or deg<=3) polynomial by variable x_k (idempotent x_k^2 = x_k in GF(2)).
fn mul_var_poly_desc(poly: &[u64], k: usize, max_deg: u64) -> Vec<u64> {
    let mut monos = Vec::with_capacity(poly.len());
    for &m in poly {
        let (vs, deg) = mono_vars4(m);
        match deg {
            0 => monos.push(mono1(k)),
            1 => {
                if vs[0] == k {
                    monos.push(m);
                } else {
                    monos.push(mono2(vs[0], k));
                }
            }
            2 => {
                if vs[0] == k || vs[1] == k {
                    monos.push(m);
                } else if max_deg >= 3 {
                    monos.push(mono3(vs[0], vs[1], k));
                }
            }
            3 => {
                if vs[0] == k || vs[1] == k || vs[2] == k {
                    monos.push(m);
                } else if max_deg >= 4 {
                    monos.push(mono4(vs[0], vs[1], vs[2], k));
                }
            }
            _ => {}
        }
    }
    canonical_poly_desc(monos)
}

/// Convert monomial list into canonical sorted descending GF(2) poly.
fn canonical_poly_desc(mut monos: Vec<u64>) -> Vec<u64> {
    monos.sort_unstable_by(|a, b| b.cmp(a));
    let mut out = Vec::with_capacity(monos.len());
    let mut i = 0;
    while i < monos.len() {
        if i + 1 < monos.len() && monos[i] == monos[i + 1] {
            i += 2;
        } else {
            out.push(monos[i]);
            i += 1;
        }
    }
    out
}

fn clause2_to_poly(l1: u32, l2: u32) -> Vec<u64> {
    let (v1, p1) = (lit_var(l1), !lit_neg(l1));
    let (v2, p2) = (lit_var(l2), !lit_neg(l2));
    let mut monos = vec![mono2(v1, v2)];
    if p1 {
        monos.push(mono1(v2));
    }
    if p2 {
        monos.push(mono1(v1));
    }
    if p1 && p2 {
        monos.push(mono0());
    }
    canonical_poly_desc(monos)
}

fn clause3_to_poly(l1: u32, l2: u32, l3: u32) -> Vec<u64> {
    let (v1, p1) = (lit_var(l1), !lit_neg(l1));
    let (v2, p2) = (lit_var(l2), !lit_neg(l2));
    let (v3, p3) = (lit_var(l3), !lit_neg(l3));
    let mut monos = vec![mono3(v1, v2, v3)];
    if p1 {
        monos.push(mono2(v2, v3));
    }
    if p2 {
        monos.push(mono2(v1, v3));
    }
    if p3 {
        monos.push(mono2(v1, v2));
    }
    if p1 && p2 {
        monos.push(mono1(v3));
    }
    if p1 && p3 {
        monos.push(mono1(v2));
    }
    if p2 && p3 {
        monos.push(mono1(v1));
    }
    if p1 && p2 && p3 {
        monos.push(mono0());
    }
    canonical_poly_desc(monos)
}

fn clause4_rm3_tail(v: [usize; 4], p: [bool; 4]) -> Vec<u64> {
    let mut monos = Vec::with_capacity(15);
    if p[0] {
        monos.push(mono3(v[1], v[2], v[3]));
    }
    if p[1] {
        monos.push(mono3(v[0], v[2], v[3]));
    }
    if p[2] {
        monos.push(mono3(v[0], v[1], v[3]));
    }
    if p[3] {
        monos.push(mono3(v[0], v[1], v[2]));
    }
    if p[0] && p[1] {
        monos.push(mono2(v[2], v[3]));
    }
    if p[0] && p[2] {
        monos.push(mono2(v[1], v[3]));
    }
    if p[0] && p[3] {
        monos.push(mono2(v[1], v[2]));
    }
    if p[1] && p[2] {
        monos.push(mono2(v[0], v[3]));
    }
    if p[1] && p[3] {
        monos.push(mono2(v[0], v[2]));
    }
    if p[2] && p[3] {
        monos.push(mono2(v[0], v[1]));
    }
    if p[0] && p[1] && p[2] {
        monos.push(mono1(v[3]));
    }
    if p[0] && p[1] && p[3] {
        monos.push(mono1(v[2]));
    }
    if p[0] && p[2] && p[3] {
        monos.push(mono1(v[1]));
    }
    if p[1] && p[2] && p[3] {
        monos.push(mono1(v[0]));
    }
    if p[0] && p[1] && p[2] && p[3] {
        monos.push(mono0());
    }
    canonical_poly_desc(monos)
}

fn clause4_to_poly(v: [usize; 4], p: [bool; 4]) -> Vec<u64> {
    let mut tail = clause4_rm3_tail(v, p);
    tail.push(mono4(v[0], v[1], v[2], v[3]));
    canonical_poly_desc(tail)
}

/// Tail of a 5-clause `prod_{i=0..5} (x_{v_i} + p_i)` after removing the deg-5 term `x_0 x_1 x_2 x_3 x_4`.
fn clause5_rm4_tail(v: [usize; 5], p: [bool; 5]) -> Vec<u64> {
    let mut monos = Vec::with_capacity(31);
    for mask in 0u8..31u8 {
        // mask bit i = 1 means variable v[i] is included in the monomial;
        // bit i = 0 means we pick constant p[i].
        let mut ok = true;
        let mut vars = [0usize; 4];
        let mut deg = 0usize;
        for i in 0..5 {
            if (mask & (1 << i)) != 0 {
                vars[deg] = v[i];
                deg += 1;
            } else if !p[i] {
                ok = false;
                break;
            }
        }
        if !ok {
            continue;
        }
        let m = match deg {
            0 => mono0(),
            1 => mono1(vars[0]),
            2 => mono2(vars[0], vars[1]),
            3 => mono3(vars[0], vars[1], vars[2]),
            4 => mono4(vars[0], vars[1], vars[2], vars[3]),
            _ => unreachable!(),
        };
        monos.push(m);
    }
    canonical_poly_desc(monos)
}

/// Given a set of surviving truth assignments (bitmask over 0..16) on 4 variables v[0..4],
/// compute the exact GF(2) vanishing ideal in RM(3, 4) (15 monomials: 1 const, 4 deg1, 6 deg2, 4 deg3).
fn extract_rm3_4_ideal(v: [usize; 4], surv_mask: u16) -> Vec<Vec<u64>> {
    let m_list: [u64; 15] = [
        mono0(),
        mono1(v[0]),
        mono1(v[1]),
        mono1(v[2]),
        mono1(v[3]),
        mono2(v[0], v[1]),
        mono2(v[0], v[2]),
        mono2(v[0], v[3]),
        mono2(v[1], v[2]),
        mono2(v[1], v[3]),
        mono2(v[2], v[3]),
        mono3(v[0], v[1], v[2]),
        mono3(v[0], v[1], v[3]),
        mono3(v[0], v[2], v[3]),
        mono3(v[1], v[2], v[3]),
    ];

    let mut cols = [0u16; 15];
    for a in 0..16u16 {
        if (surv_mask & (1 << a)) == 0 {
            continue;
        }
        let b0 = (a & 1) != 0;
        let b1 = ((a >> 1) & 1) != 0;
        let b2 = ((a >> 2) & 1) != 0;
        let b3 = ((a >> 3) & 1) != 0;
        let vals = [
            true,
            b0,
            b1,
            b2,
            b3,
            b0 && b1,
            b0 && b2,
            b0 && b3,
            b1 && b2,
            b1 && b3,
            b2 && b3,
            b0 && b1 && b2,
            b0 && b1 && b3,
            b0 && b2 && b3,
            b1 && b2 && b3,
        ];
        for c in 0..15 {
            if vals[c] {
                cols[c] |= 1 << a;
            }
        }
    }

    let mut piv_map: HashMap<u16, (u16, u16)> = HashMap::new();
    let mut out = Vec::new();
    for c in 0..15 {
        let mut vec = cols[c];
        let mut poly = 1u16 << c;
        while vec != 0 {
            let hb = 1u16 << (15 - vec.leading_zeros() as u16);
            if let Some(&(pvec, ppoly)) = piv_map.get(&hb) {
                vec ^= pvec;
                poly ^= ppoly;
            } else {
                piv_map.insert(hb, (vec, poly));
                break;
            }
        }
        if vec == 0 && poly != 0 {
            let mut monos = Vec::new();
            for bit in (0..15).rev() {
                if (poly & (1u16 << bit)) != 0 {
                    monos.push(m_list[bit]);
                }
            }
            out.push(monos);
        }
    }
    out
}

/// Given surviving truth assignments (bitmask over 0..32) on 5 variables v[0..5],
/// compute the exact GF(2) vanishing ideal in RM(4, 5) (31 monomials: deg 0..4).
fn extract_rm4_5_ideal(v: [usize; 5], surv_mask: u32) -> Vec<Vec<u64>> {
    let m_list: [u64; 31] = [
        mono0(),
        mono1(v[0]),
        mono1(v[1]),
        mono1(v[2]),
        mono1(v[3]),
        mono1(v[4]),
        mono2(v[0], v[1]),
        mono2(v[0], v[2]),
        mono2(v[0], v[3]),
        mono2(v[0], v[4]),
        mono2(v[1], v[2]),
        mono2(v[1], v[3]),
        mono2(v[1], v[4]),
        mono2(v[2], v[3]),
        mono2(v[2], v[4]),
        mono2(v[3], v[4]),
        mono3(v[0], v[1], v[2]),
        mono3(v[0], v[1], v[3]),
        mono3(v[0], v[1], v[4]),
        mono3(v[0], v[2], v[3]),
        mono3(v[0], v[2], v[4]),
        mono3(v[0], v[3], v[4]),
        mono3(v[1], v[2], v[3]),
        mono3(v[1], v[2], v[4]),
        mono3(v[1], v[3], v[4]),
        mono3(v[2], v[3], v[4]),
        mono4(v[0], v[1], v[2], v[3]),
        mono4(v[0], v[1], v[2], v[4]),
        mono4(v[0], v[1], v[3], v[4]),
        mono4(v[0], v[2], v[3], v[4]),
        mono4(v[1], v[2], v[3], v[4]),
    ];

    let mut cols = [0u32; 31];
    for a in 0..32u32 {
        if (surv_mask & (1u32 << a)) == 0 {
            continue;
        }
        let b0 = (a & 1) != 0;
        let b1 = ((a >> 1) & 1) != 0;
        let b2 = ((a >> 2) & 1) != 0;
        let b3 = ((a >> 3) & 1) != 0;
        let b4 = ((a >> 4) & 1) != 0;
        let vals = [
            true,
            b0,
            b1,
            b2,
            b3,
            b4,
            b0 && b1,
            b0 && b2,
            b0 && b3,
            b0 && b4,
            b1 && b2,
            b1 && b3,
            b1 && b4,
            b2 && b3,
            b2 && b4,
            b3 && b4,
            b0 && b1 && b2,
            b0 && b1 && b3,
            b0 && b1 && b4,
            b0 && b2 && b3,
            b0 && b2 && b4,
            b0 && b3 && b4,
            b1 && b2 && b3,
            b1 && b2 && b4,
            b1 && b3 && b4,
            b2 && b3 && b4,
            b0 && b1 && b2 && b3,
            b0 && b1 && b2 && b4,
            b0 && b1 && b3 && b4,
            b0 && b2 && b3 && b4,
            b1 && b2 && b3 && b4,
        ];
        let bit = 1u32 << a;
        for c in 0..31 {
            if vals[c] {
                cols[c] |= bit;
            }
        }
    }

    let mut piv_vec = [0u32; 32];
    let mut piv_poly = [0u32; 32];
    let mut out = Vec::new();
    for c in 0..31 {
        let mut vec = cols[c];
        let mut poly = 1u32 << c;
        while vec != 0 {
            let hb = 31 - vec.leading_zeros() as usize;
            if piv_vec[hb] != 0 {
                vec ^= piv_vec[hb];
                poly ^= piv_poly[hb];
            } else {
                piv_vec[hb] = vec;
                piv_poly[hb] = poly;
                break;
            }
        }
        if vec == 0 && poly != 0 {
            let mut monos = Vec::new();
            for bit in (0..31).rev() {
                if (poly & (1u32 << bit)) != 0 {
                    monos.push(m_list[bit]);
                }
            }
            out.push(monos);
        }
    }
    out
}

// =========================================================================
// Native VeriPB 3.0.2 Proof Logger (`rup`, `pol`, `red` with witnesses)
// =========================================================================

#[derive(Clone)]
struct PolyOrigin {
    poly: Vec<u64>,
    supp: Vec<usize>,
    extra_clauses: Vec<Vec<u32>>,
}

#[derive(Clone)]
struct VeriPBLogger {
    cid: usize,
    next_var: usize, // 1-indexed next fresh variable
    lines: Vec<String>,
    known_clauses: HashSet<Vec<u32>>,
    // Monomial (deg >= 2) -> 1-indexed extension variable z_m
    mono_var: HashMap<u64, usize>,
    contra_cid: Option<usize>,
}

impl VeriPBLogger {
    fn new(n_vars: usize, orig_clauses: &[Vec<u32>]) -> Self {
        let mut known_clauses = HashSet::with_capacity(orig_clauses.len() * 2);
        for cl in orig_clauses {
            let mut c = cl.clone();
            c.sort_unstable();
            c.dedup();
            known_clauses.insert(c);
        }
        Self {
            cid: orig_clauses.len(),
            next_var: n_vars + 1,
            lines: vec![
                "pseudo-Boolean proof version 3.0".to_string(),
                format!("f {} ;", orig_clauses.len()),
            ],
            known_clauses,
            mono_var: HashMap::new(),
            contra_cid: None,
        }
    }

    fn alloc_var(&mut self) -> usize {
        let v = self.next_var;
        self.next_var += 1;
        v
    }

    fn emit_pol(&mut self, rpn: &[String]) -> usize {
        self.cid += 1;
        self.lines.push(format!("pol {} ;", rpn.join(" ")));
        self.cid
    }

    /// Emit a VeriPB 3.0 `red` constraint with witness `x{w_var} -> {w_val}`.
    /// `terms`: slice of `(coeff, var1_idx, is_pos)`.
    fn emit_red(&mut self, terms: &[(i64, usize, bool)], rhs: i64, w_var: usize, w_val: u8) -> usize {
        self.cid += 1;
        let lhs: Vec<String> = terms
            .iter()
            .map(|&(c, v, pos)| format!("{} {}", c, var_lit_to_pbp(v, pos)))
            .collect();
        self.lines.push(format!(
            "red {} >= {} : x{} -> {} ;",
            lhs.join(" "),
            rhs,
            w_var,
            w_val
        ));
        self.cid
    }

    /// Emit a RUP clause over 0-indexed `u32` literals; skips tautologies and duplicates.
    fn emit_rup_lits(&mut self, lits: &[u32]) -> Option<usize> {
        let mut c = lits.to_vec();
        c.sort_unstable();
        c.dedup();
        for w in c.windows(2) {
            if (w[0] ^ 1) == w[1] {
                return None;
            }
        }
        if !c.is_empty() && !self.known_clauses.insert(c.clone()) {
            return None;
        }
        self.cid += 1;
        if c.is_empty() {
            self.lines.push("rup >= 1 ;".to_string());
            self.contra_cid = Some(self.cid);
        } else {
            let terms: Vec<String> = c.iter().map(|&l| format!("1 {}", lit_to_pbp(l))).collect();
            self.lines.push(format!("rup {} >= 1 ;", terms.join(" ")));
        }
        Some(self.cid)
    }

    /// Emit a RUP clause over 1-indexed signed literals `(var1, is_pos)` unconditionally.
    fn emit_rup_raw(&mut self, lits: &[(usize, bool)]) -> usize {
        self.cid += 1;
        if lits.is_empty() {
            self.lines.push("rup >= 1 ;".to_string());
            self.contra_cid = Some(self.cid);
        } else {
            let terms: Vec<String> = lits
                .iter()
                .map(|&(v, pos)| format!("1 {}", var_lit_to_pbp(v, pos)))
                .collect();
            self.lines.push(format!("rup {} >= 1 ;", terms.join(" ")));
        }
        self.cid
    }

    /// Derive clause `target` (1-indexed `(var1, is_pos)`) by case-splitting over 0-indexed `cube_vars`.
    fn derive_clause_over_cube_raw(
        &mut self,
        target: &[(usize, bool)],
        cube_vars0: &[usize],
    ) -> usize {
        let target_vars: HashSet<usize> = target.iter().map(|&(v, _)| v).collect();
        let rem: Vec<usize> = cube_vars0
            .iter()
            .map(|&v0| v0 + 1)
            .filter(|v1| !target_vars.contains(v1))
            .collect();

        fn rec(
            logger: &mut VeriPBLogger,
            base: &[(usize, bool)],
            rem: &[usize],
            idx: usize,
            extra: &mut Vec<(usize, bool)>,
        ) -> usize {
            if idx == rem.len() {
                let mut full = Vec::with_capacity(base.len() + extra.len());
                full.extend_from_slice(base);
                full.extend_from_slice(extra);
                return logger.emit_rup_raw(&full);
            }
            let v1 = rem[idx];
            extra.push((v1, true));
            let id_pos = rec(logger, base, rem, idx + 1, extra);
            extra.pop();
            extra.push((v1, false));
            let id_neg = rec(logger, base, rem, idx + 1, extra);
            extra.pop();
            logger.emit_pol(&[
                id_pos.to_string(),
                id_neg.to_string(),
                "+".to_string(),
                "2".to_string(),
                "d".to_string(),
            ])
        }

        let mut extra = Vec::with_capacity(rem.len());
        let cid = rec(self, target, &rem, 0, &mut extra);
        if target.is_empty() {
            self.contra_cid = Some(cid);
        }
        cid
    }

    /// Allocate (or fetch cached) Veronese extension variable `z_m` for monomial `m` (deg >= 1).
    /// Returns 1-indexed variable ID.
    fn get_mono_var(&mut self, m: u64) -> usize {
        let (vs, deg) = mono_vars4(m);
        if deg == 1 {
            return vs[0] + 1;
        }
        if let Some(&zv) = self.mono_var.get(&m) {
            return zv;
        }
        let (a_var, b_var) = match deg {
            2 => (vs[0] + 1, vs[1] + 1),
            3 => (self.get_mono_var(mono2(vs[0], vs[1])), vs[2] + 1),
            4 => (self.get_mono_var(mono3(vs[0], vs[1], vs[2])), vs[3] + 1),
            _ => unreachable!(),
        };
        let z = self.alloc_var();
        // z <-> (a_var & b_var)
        self.emit_red(&[(1, a_var, false), (1, b_var, false), (1, z, true)], 1, z, 1);
        self.emit_red(&[(1, a_var, true), (1, z, false)], 1, z, 0);
        self.emit_red(&[(1, b_var, true), (1, z, false)], 1, z, 0);
        self.mono_var.insert(m, z);
        z
    }

    /// Realize 3-XOR integer bounds `v1 + v2 + v3 - 2*w == 0` via `red` MAJ_3 witness `w`.
    /// `z_00, z_01, z_10, z_11` forbid `(0,0,1), (0,1,0), (1,0,0), (1,1,1)` on `(v1, v2, v3)`.
    fn realize_parity3_bounds(
        &mut self,
        v1: usize,
        v2: usize,
        v3: usize,
        k_100: usize,
        k_010: usize,
        k_001: usize,
        k_111: usize,
    ) -> (usize, usize) {
        let w = self.alloc_var();
        let r1 = self.emit_red(
            &[(1, v1, true), (1, v2, true), (1, v3, true), (2, w, false)],
            2,
            w,
            0,
        );
        let r2 = self.emit_red(
            &[(1, v1, false), (1, v2, false), (1, v3, false), (2, w, true)],
            2,
            w,
            1,
        );
        let l1 = self.emit_pol(&[
            r2.to_string(),
            k_100.to_string(),
            "+".to_string(),
            "2".to_string(),
            "d".to_string(),
        ]);
        let l2 = self.emit_pol(&[
            r2.to_string(),
            k_010.to_string(),
            "+".to_string(),
            "2".to_string(),
            "d".to_string(),
        ]);
        let l3 = self.emit_pol(&[
            r2.to_string(),
            k_001.to_string(),
            "+".to_string(),
            "2".to_string(),
            "d".to_string(),
        ]);
        let u_minus = self.emit_pol(&[
            l1.to_string(),
            l2.to_string(),
            "+".to_string(),
            l3.to_string(),
            "+".to_string(),
            "2".to_string(),
            "*".to_string(),
            k_111.to_string(),
            "+".to_string(),
            "3".to_string(),
            "d".to_string(),
        ]);
        (r1, u_minus)
    }

    /// Certify a GF(2) RREF derivation `sum_{t in comb} P_t(x) == Q(x) (mod 2)` in VeriPB 3.0.2!
    /// For each `target_lits` in `targets`, `target_lits` is a list of `(mono, is_pos)` representing
    /// a forbidden parity assignment of `Q`'s non-constant monomials (where `sum_{m in Q} lit_m >= 1`
    /// is derived by `pol` + `2 d`).
    /// If `Q = 1` (UNSAT), pass `targets = &[vec![]]` -> derives `0 >= 1`!
    fn certify_gf2_combination(
        &mut self,
        origins: &[PolyOrigin],
        comb: &[usize],
        targets: &[Vec<(u64, bool)>],
    ) -> Vec<usize> {
        let mut plus_terms: Vec<usize> = Vec::new();
        let mut minus_terms: Vec<usize> = Vec::new();

        for &idx in comb {
            let orig = &origins[idx];
            // Emit any RUP parent clauses (e.g. derived 4-clauses/5-clauses) on demand
            for ec in &orig.extra_clauses {
                self.emit_rup_lits(ec);
            }

            let mut z_vars: Vec<usize> = Vec::new();
            let mut c0 = false;
            for &m in &orig.poly {
                if m == 0 {
                    c0 = true;
                } else {
                    z_vars.push(self.get_mono_var(m));
                }
            }

            let r = z_vars.len();
            if r == 0 {
                if c0 {
                    let cid = self.derive_clause_over_cube_raw(&[], &orig.supp);
                    return vec![cid];
                }
                continue;
            }
            if r == 1 {
                let z1 = z_vars[0];
                let unit_cid = self.derive_clause_over_cube_raw(&[(z1, c0)], &orig.supp);
                if c0 {
                    let id_m = self.emit_pol(&[var_lit_to_pbp(z1, false)]);
                    plus_terms.push(unit_cid);
                    minus_terms.push(id_m);
                } else {
                    let id_p = self.emit_pol(&[var_lit_to_pbp(z1, true)]);
                    plus_terms.push(id_p);
                    minus_terms.push(unit_cid);
                }
                continue;
            }

            // r >= 2: fold z_vars[0..r-1] via red XOR-3 witnesses
            let mut acc_var = z_vars[0];
            for &nxt_z in &z_vars[1..r - 1] {
                let s_var = self.alloc_var();
                let z_01 = self.emit_red(
                    &[(1, acc_var, true), (1, nxt_z, false), (1, s_var, true)],
                    1,
                    s_var,
                    1,
                );
                let z_10 = self.emit_red(
                    &[(1, acc_var, false), (1, nxt_z, true), (1, s_var, true)],
                    1,
                    s_var,
                    1,
                );
                let z_00 = self.emit_red(
                    &[(1, acc_var, true), (1, nxt_z, true), (1, s_var, false)],
                    1,
                    s_var,
                    0,
                );
                let z_11 = self.emit_red(
                    &[(1, acc_var, false), (1, nxt_z, false), (1, s_var, false)],
                    1,
                    s_var,
                    0,
                );
                let (idp, idm) =
                    self.realize_parity3_bounds(acc_var, nxt_z, s_var, z_10, z_01, z_00, z_11);
                plus_terms.push(idp);
                minus_terms.push(idm);
                acc_var = s_var;
            }

            let last_a = acc_var;
            let last_b = z_vars[r - 1];
            let (pair_p, pair_m) = if !c0 {
                (
                    [(last_a, true), (last_b, false)],
                    [(last_a, false), (last_b, true)],
                )
            } else {
                (
                    [(last_a, true), (last_b, true)],
                    [(last_a, false), (last_b, false)],
                )
            };
            let cid_p = self.derive_clause_over_cube_raw(&pair_p, &orig.supp);
            let cid_m = self.derive_clause_over_cube_raw(&pair_m, &orig.supp);
            plus_terms.push(cid_p);
            minus_terms.push(cid_m);
        }

        // Sum all plus_terms once and all minus_terms once
        let sum_p = if plus_terms.len() == 1 {
            plus_terms[0]
        } else {
            let mut rpn = vec![plus_terms[0].to_string()];
            for &id in &plus_terms[1..] {
                rpn.push(id.to_string());
                rpn.push("+".to_string());
            }
            self.emit_pol(&rpn)
        };
        let sum_m = if minus_terms.len() == 1 {
            minus_terms[0]
        } else {
            let mut rpn = vec![minus_terms[0].to_string()];
            for &id in &minus_terms[1..] {
                rpn.push(id.to_string());
                rpn.push("+".to_string());
            }
            self.emit_pol(&rpn)
        };

        let mut derived_cids = Vec::with_capacity(targets.len());
        for t_lits in targets {
            let mut rpn_p = vec![sum_p.to_string()];
            let mut rpn_m = vec![sum_m.to_string()];
            for &(m, is_pos) in t_lits {
                let zv = self.get_mono_var(m);
                let tok = var_lit_to_pbp(zv, is_pos);
                rpn_p.push(tok.clone());
                rpn_p.push("+".to_string());
                rpn_m.push(tok);
                rpn_m.push("+".to_string());
            }
            rpn_p.push("2".to_string());
            rpn_p.push("d".to_string());
            rpn_m.push("2".to_string());
            rpn_m.push("d".to_string());
            let hp = self.emit_pol(&rpn_p);
            let hm = self.emit_pol(&rpn_m);
            let cid = self.emit_pol(&[hp.to_string(), hm.to_string(), "+".to_string()]);
            if t_lits.is_empty() {
                self.contra_cid = Some(cid);
            }
            derived_cids.push(cid);
        }
        derived_cids
    }

    fn finish_unsat(&mut self) -> String {
        let cid = self.contra_cid.unwrap_or_else(|| self.emit_rup_raw(&[]));
        self.lines.push("output NONE ;".to_string());
        self.lines.push(format!("conclusion UNSAT : {} ;", cid));
        self.lines.push("end pseudo-Boolean proof ;".to_string());
        self.lines.join("\n") + "\n"
    }
}

// =========================================================================
// Main Solver (RM(3,4) / RM(4,5) + Witt Pairwise Cutting Planes + FL1)
// =========================================================================

struct Solver {
    n: usize,
    fixed: Vec<Option<bool>>,
    uf_parent: Vec<usize>,
    uf_parity: Vec<bool>,
    clauses: Vec<Vec<u32>>,
    pair_mask: Vec<u8>,
    units_deduced: usize,
    xors_deduced: usize,
    rm3_polys: usize,
    rm4_polys: usize,
    witt_cuts: usize,
    use_rm4: bool,
    logger: Option<VeriPBLogger>,
}

impl Solver {
    fn new(n: usize, clauses: Vec<Vec<u32>>, use_rm4: bool, emit_pbp: bool) -> Self {
        let logger = if emit_pbp {
            Some(VeriPBLogger::new(n, &clauses))
        } else {
            None
        };
        Self {
            n,
            fixed: vec![None; n],
            uf_parent: (0..n).collect(),
            uf_parity: vec![false; n],
            clauses,
            pair_mask: vec![0b1111; n * n],
            units_deduced: 0,
            xors_deduced: 0,
            rm3_polys: 0,
            rm4_polys: 0,
            witt_cuts: 0,
            use_rm4,
            logger,
        }
    }

    fn log_rup(&mut self, lits: &[u32]) {
        if let Some(ref mut lg) = self.logger {
            lg.emit_rup_lits(lits);
        }
    }

    fn uf_find(&mut self, v: usize) -> (usize, bool) {
        if self.uf_parent[v] == v {
            return (v, false);
        }
        let p = self.uf_parent[v];
        let (root, rpar) = self.uf_find(p);
        let total = self.uf_parity[v] ^ rpar;
        self.uf_parent[v] = root;
        self.uf_parity[v] = total;
        (root, total)
    }

    fn resolve_lit(&mut self, lit: u32) -> Result<u32, bool> {
        let v = lit_var(lit);
        let neg = lit_neg(lit);
        let (r, par) = self.uf_find(v);
        if let Some(val) = self.fixed[r] {
            let actual = val ^ par ^ neg;
            return Err(actual);
        }
        Ok(mk_lit(r, neg ^ par))
    }

    fn set_var_inner(&mut self, v: usize, val: bool, log_rup: bool) -> Result<bool, &'static str> {
        let (r, par) = self.uf_find(v);
        let rval = val ^ par;
        if let Some(old) = self.fixed[r] {
            if old != rval {
                if log_rup {
                    self.log_rup(&[mk_lit(v, !val)]);
                    self.log_rup(&[]);
                }
                return Err("UNSAT_UNIT_CONFLICT");
            }
            return Ok(false);
        }
        self.fixed[r] = Some(rval);
        self.units_deduced += 1;
        if log_rup {
            self.log_rup(&[mk_lit(v, !val)]);
            if r != v {
                self.log_rup(&[mk_lit(r, !rval)]);
            }
        }
        Ok(true)
    }

    fn set_var(&mut self, v: usize, val: bool) -> Result<bool, &'static str> {
        self.set_var_inner(v, val, true)
    }

    fn set_xor2_inner(
        &mut self,
        u: usize,
        v: usize,
        rhs: bool,
        log_rup: bool,
    ) -> Result<bool, &'static str> {
        let (ru, pu) = self.uf_find(u);
        let (rv, pv) = self.uf_find(v);
        let rel = rhs ^ pu ^ pv;
        if log_rup {
            if !rhs {
                self.log_rup(&[mk_lit(u, true), mk_lit(v, false)]);
                self.log_rup(&[mk_lit(u, false), mk_lit(v, true)]);
            } else {
                self.log_rup(&[mk_lit(u, false), mk_lit(v, false)]);
                self.log_rup(&[mk_lit(u, true), mk_lit(v, true)]);
            }
        }
        if ru == rv {
            if rel {
                if log_rup {
                    self.log_rup(&[mk_lit(ru, false)]);
                    self.log_rup(&[]);
                }
                return Err("UNSAT_2XOR_SELF_CONFLICT");
            }
            return Ok(false);
        }
        if let (Some(fu), Some(fv)) = (self.fixed[ru], self.fixed[rv]) {
            if (fu ^ fv) != rel {
                if log_rup {
                    self.log_rup(&[]);
                }
                return Err("UNSAT_2XOR_FIXED_CONFLICT");
            }
            return Ok(false);
        }
        if let Some(fu) = self.fixed[ru] {
            return self.set_var_inner(rv, fu ^ rel, log_rup);
        }
        if let Some(fv) = self.fixed[rv] {
            return self.set_var_inner(ru, fv ^ rel, log_rup);
        }
        let (keep, drop) = if ru < rv { (ru, rv) } else { (rv, ru) };
        self.uf_parent[drop] = keep;
        self.uf_parity[drop] = rel;
        self.xors_deduced += 1;
        if log_rup && (keep != u || drop != v) {
            if !rel {
                self.log_rup(&[mk_lit(keep, true), mk_lit(drop, false)]);
                self.log_rup(&[mk_lit(keep, false), mk_lit(drop, true)]);
            } else {
                self.log_rup(&[mk_lit(keep, false), mk_lit(drop, false)]);
                self.log_rup(&[mk_lit(keep, true), mk_lit(drop, true)]);
            }
        }
        Ok(true)
    }

    fn set_xor2(&mut self, u: usize, v: usize, rhs: bool) -> Result<bool, &'static str> {
        self.set_xor2_inner(u, v, rhs, true)
    }

    #[inline]
    fn get_mask(&self, i: usize, j: usize) -> u8 {
        if i < j {
            self.pair_mask[i * self.n + j]
        } else {
            let m = self.pair_mask[j * self.n + i];
            (m & 0b1001) | ((m & 0b0010) << 1) | ((m & 0b0100) >> 1)
        }
    }

    fn tighten_mask_inner(
        &mut self,
        i: usize,
        j: usize,
        allowed: u8,
        log_rup: bool,
    ) -> Result<bool, &'static str> {
        if i == j {
            return Ok(false);
        }
        let (a, b, norm) = if i < j {
            (i, j, allowed)
        } else {
            (
                j,
                i,
                (allowed & 0b1001) | ((allowed & 0b0010) << 1) | ((allowed & 0b0100) >> 1),
            )
        };
        let idx = a * self.n + b;
        let old = self.pair_mask[idx];
        let new_m = old & norm;
        if log_rup {
            let newly_forbid = old & !new_m;
            if newly_forbid != 0 {
                for ba in 0..2usize {
                    for bb in 0..2usize {
                        if (newly_forbid & (1u8 << (ba * 2 + bb))) != 0 {
                            self.log_rup(&[mk_lit(a, ba == 1), mk_lit(b, bb == 1)]);
                        }
                    }
                }
            }
        }
        if new_m == 0 {
            if self.logger.is_some() {
                self.log_rup(&[mk_lit(a, false)]);
                self.log_rup(&[]);
            }
            return Err("UNSAT_PAIR_MASK_EMPTY");
        }
        if new_m == old {
            return Ok(false);
        }
        self.pair_mask[idx] = new_m;
        self.witt_cuts += 1;
        if (new_m & 0b1100) == 0 {
            self.set_var(a, false)?;
        } else if (new_m & 0b0011) == 0 {
            self.set_var(a, true)?;
        }
        if (new_m & 0b1010) == 0 {
            self.set_var(b, false)?;
        } else if (new_m & 0b0101) == 0 {
            self.set_var(b, true)?;
        }
        if new_m == 0b1001 {
            self.set_xor2(a, b, false)?;
        } else if new_m == 0b0110 {
            self.set_xor2(a, b, true)?;
        }
        Ok(true)
    }

    fn tighten_mask(&mut self, i: usize, j: usize, allowed: u8) -> Result<bool, &'static str> {
        self.tighten_mask_inner(i, j, allowed, true)
    }

    fn forbid_2clause(&mut self, l1: u32, l2: u32) -> Result<bool, &'static str> {
        let v1 = lit_var(l1);
        let v2 = lit_var(l2);
        if v1 == v2 {
            if l1 == l2 {
                return self.set_var(v1, !lit_neg(l1));
            }
            return Ok(false);
        }
        let bad1 = if lit_neg(l1) { 1 } else { 0 };
        let bad2 = if lit_neg(l2) { 1 } else { 0 };
        let bad_bit = 1u8 << (bad1 * 2 + bad2);
        self.tighten_mask(v1, v2, 0b1111 ^ bad_bit)
    }

    fn simplify_clauses(&mut self) -> Result<bool, &'static str> {
        let mut changed = false;
        loop {
            let mut unit_found = false;
            let mut new_clauses = Vec::with_capacity(self.clauses.len());
            let mut seen: HashSet<Vec<u32>> = HashSet::with_capacity(self.clauses.len());
            let old_clauses = std::mem::take(&mut self.clauses);
            for cl in old_clauses {
                let mut sat = false;
                let mut lits = Vec::with_capacity(cl.len());
                for lit in cl {
                    match self.resolve_lit(lit) {
                        Ok(rl) => lits.push(rl),
                        Err(true) => {
                            sat = true;
                            break;
                        }
                        Err(false) => {}
                    }
                }
                if sat {
                    continue;
                }
                lits.sort_unstable();
                lits.dedup();
                for w in lits.windows(2) {
                    if (w[0] ^ 1) == w[1] {
                        sat = true;
                        break;
                    }
                }
                if sat {
                    continue;
                }
                if lits.is_empty() {
                    self.log_rup(&[]);
                    return Err("UNSAT_BCP");
                }
                if lits.len() == 1 {
                    let l = lits[0];
                    if self.set_var(lit_var(l), !lit_neg(l))? {
                        unit_found = true;
                        changed = true;
                    }
                    continue;
                }
                if lits.len() == 2 {
                    self.forbid_2clause(lits[0], lits[1])?;
                }
                if seen.insert(lits.clone()) {
                    if self.logger.is_some() && lits.len() <= 3 {
                        self.log_rup(&lits);
                    }
                    new_clauses.push(lits);
                }
            }
            self.clauses = new_clauses;
            if !unit_found {
                break;
            }
        }
        for i in 0..self.n {
            if self.uf_find(i).0 != i || self.fixed[i].is_some() {
                continue;
            }
            for j in (i + 1)..self.n {
                if self.uf_find(j).0 != j || self.fixed[j].is_some() {
                    continue;
                }
                let m = self.get_mask(i, j);
                if m == 0 {
                    if self.logger.is_some() {
                        self.log_rup(&[mk_lit(i, false)]);
                        self.log_rup(&[]);
                    }
                    return Err("UNSAT_PAIR_MASK");
                }
                if (m & 0b1100) == 0 {
                    if self.set_var(i, false)? {
                        changed = true;
                    }
                } else if (m & 0b0011) == 0 {
                    if self.set_var(i, true)? {
                        changed = true;
                    }
                }
                if (m & 0b1010) == 0 {
                    if self.set_var(j, false)? {
                        changed = true;
                    }
                } else if (m & 0b0101) == 0 {
                    if self.set_var(j, true)? {
                        changed = true;
                    }
                }
            }
        }
        Ok(changed)
    }

    fn phase_a_2sat_closure_and_fl1(&mut self) -> Result<bool, &'static str> {
        let mut changed = false;
        let num_lits = 2 * self.n;
        let mut adj: Vec<Vec<u32>> = vec![Vec::new(); num_lits];

        for i in 0..self.n {
            let (ri, _) = self.uf_find(i);
            if ri != i || self.fixed[i].is_some() {
                continue;
            }
            for j in (i + 1)..self.n {
                let (rj, _) = self.uf_find(j);
                if rj != j || self.fixed[j].is_some() {
                    continue;
                }
                let m = self.get_mask(i, j);
                if m != 0b1111 {
                    for bi in 0..2 {
                        for bj in 0..2 {
                            if (m & (1 << (bi * 2 + bj))) == 0 {
                                let li_true = mk_lit(i, bi == 0);
                                let lj_false = mk_lit(j, bj == 1);
                                let lj_true = mk_lit(j, bj == 0);
                                let li_false = mk_lit(i, bi == 1);
                                adj[li_true as usize].push(lj_false);
                                adj[lj_true as usize].push(li_false);
                            }
                        }
                    }
                }
            }
        }
        for cl in &self.clauses {
            if cl.len() == 2 {
                let (a, b) = (cl[0], cl[1]);
                adj[neg_lit(a) as usize].push(b);
                adj[neg_lit(b) as usize].push(a);
            }
        }

        let mut index = 0usize;
        let mut indices = vec![usize::MAX; num_lits];
        let mut lowlink = vec![0usize; num_lits];
        let mut on_stack = vec![false; num_lits];
        let mut stack = Vec::new();
        let mut comp = vec![usize::MAX; num_lits];
        let mut sccs: Vec<Vec<u32>> = Vec::new();

        fn strongconnect(
            v: usize,
            adj: &[Vec<u32>],
            index: &mut usize,
            indices: &mut [usize],
            lowlink: &mut [usize],
            on_stack: &mut [bool],
            stack: &mut Vec<usize>,
            comp: &mut [usize],
            sccs: &mut Vec<Vec<u32>>,
        ) {
            indices[v] = *index;
            lowlink[v] = *index;
            *index += 1;
            stack.push(v);
            on_stack[v] = true;
            for &w_u32 in &adj[v] {
                let w = w_u32 as usize;
                if indices[w] == usize::MAX {
                    strongconnect(w, adj, index, indices, lowlink, on_stack, stack, comp, sccs);
                    if lowlink[w] < lowlink[v] {
                        lowlink[v] = lowlink[w];
                    }
                } else if on_stack[w] && indices[w] < lowlink[v] {
                    lowlink[v] = indices[w];
                }
            }
            if lowlink[v] == indices[v] {
                let cid = sccs.len();
                let mut members = Vec::new();
                while let Some(w) = stack.pop() {
                    on_stack[w] = false;
                    comp[w] = cid;
                    members.push(w as u32);
                    if w == v {
                        break;
                    }
                }
                sccs.push(members);
            }
        }

        for v in 0..num_lits {
            if indices[v] == usize::MAX {
                strongconnect(
                    v,
                    &adj,
                    &mut index,
                    &mut indices,
                    &mut lowlink,
                    &mut on_stack,
                    &mut stack,
                    &mut comp,
                    &mut sccs,
                );
            }
        }

        for v in 0..self.n {
            if comp[2 * v] == comp[2 * v + 1] {
                if self.logger.is_some() {
                    self.log_rup(&[mk_lit(v, true)]);
                    self.log_rup(&[]);
                }
                return Err("UNSAT_2SAT_SCC");
            }
        }
        for scc in &sccs {
            if scc.len() > 1 {
                let rep = scc[0];
                let rv = lit_var(rep);
                let rn = lit_neg(rep);
                for &m in &scc[1..] {
                    let mv = lit_var(m);
                    let mn = lit_neg(m);
                    if self.set_xor2(rv, mv, rn ^ mn)? {
                        changed = true;
                    }
                }
            }
        }

        let words = (num_lits + 63) / 64;
        let mut reach = vec![vec![0u64; words]; num_lits];
        for u in 0..num_lits {
            reach[u][u / 64] |= 1u64 << (u % 64);
            for &w in &adj[u] {
                let wu = w as usize;
                reach[u][wu / 64] |= 1u64 << (wu % 64);
            }
        }
        for scc in &sccs {
            let rep = scc[0] as usize;
            let mut combined = reach[rep].clone();
            for &m in scc {
                let mu = m as usize;
                for w in 0..words {
                    combined[w] |= reach[mu][w];
                }
                for &nbr in &adj[mu] {
                    let nu = nbr as usize;
                    for w in 0..words {
                        combined[w] |= reach[nu][w];
                    }
                }
            }
            for &m in scc {
                reach[m as usize] = combined.clone();
            }
        }

        for l in 0..num_lits {
            let nl = l ^ 1;
            if (reach[l][nl / 64] >> (nl % 64)) & 1 == 1 {
                if self.set_var(lit_var(l as u32), lit_neg(l as u32))? {
                    changed = true;
                }
            }
            for w_idx in 0..words {
                let mut bits = reach[l][w_idx];
                while bits != 0 {
                    let tz = bits.trailing_zeros() as usize;
                    bits &= bits - 1;
                    let target = w_idx * 64 + tz;
                    if target != l && lit_var(l as u32) < lit_var(target as u32) {
                        if self.forbid_2clause((l as u32) ^ 1, target as u32)? {
                            changed = true;
                        }
                    }
                }
            }
        }

        let mut shortened_2cls: Vec<[u32; 2]> = Vec::new();
        for cl in &mut self.clauses {
            if cl.len() == 3 {
                let (a, b, c) = (cl[0], cl[1], cl[2]);
                let checks = [(a, b, c), (b, a, c), (c, a, b)];
                for (drop, keep1, keep2) in checks {
                    let du = drop as usize;
                    let k1 = keep1 as usize;
                    let k2 = keep2 as usize;
                    if ((reach[du][k1 / 64] >> (k1 % 64)) & 1 == 1)
                        || ((reach[du][k2 / 64] >> (k2 % 64)) & 1 == 1)
                    {
                        *cl = vec![keep1, keep2];
                        shortened_2cls.push([keep1, keep2]);
                        changed = true;
                        break;
                    }
                }
            }
        }
        if self.logger.is_some() {
            for [k1, k2] in shortened_2cls {
                self.log_rup(&[k1, k2]);
            }
        }

        if changed {
            self.simplify_clauses()?;
        }

        // Failed-Literal 0-depth lookahead (FL1) with 2-clause + pair_mask propagation
        let active_vars: Vec<usize> = (0..self.n)
            .filter(|&v| self.uf_find(v).0 == v && self.fixed[v].is_none())
            .collect();
        for v in active_vars {
            if self.fixed[v].is_some() {
                continue;
            }
            let (res_t, hints_t) = self.probe_bcp_2sat(v, true);
            let (res_f, hints_f) = self.probe_bcp_2sat(v, false);
            match (res_t, res_f) {
                (None, None) => {
                    if self.logger.is_some() {
                        for h in &hints_t {
                            self.log_rup(h);
                        }
                        self.log_rup(&[mk_lit(v, true)]);
                        for h in &hints_f {
                            self.log_rup(h);
                        }
                        self.log_rup(&[]);
                    }
                    return Err("UNSAT_FL1");
                }
                (None, Some(_)) => {
                    if self.logger.is_some() {
                        for h in &hints_t {
                            self.log_rup(h);
                        }
                    }
                    if self.set_var(v, false)? {
                        changed = true;
                    }
                }
                (Some(_), None) => {
                    if self.logger.is_some() {
                        for h in &hints_f {
                            self.log_rup(h);
                        }
                    }
                    if self.set_var(v, true)? {
                        changed = true;
                    }
                }
                (Some(imp_t), Some(imp_f)) => {
                    let mut flushed = false;
                    for u in 0..self.n {
                        if u == v || self.fixed[u].is_some() {
                            continue;
                        }
                        if let (Some(bt), Some(bf)) = (imp_t[u], imp_f[u]) {
                            if self.logger.is_some() && !flushed {
                                for h in &hints_t {
                                    self.log_rup(h);
                                }
                                for h in &hints_f {
                                    self.log_rup(h);
                                }
                                flushed = true;
                            }
                            if bt == bf {
                                if self.logger.is_some() {
                                    // Emit (~v \/ u=bt) so u=bt is directly RUP
                                    self.log_rup(&[mk_lit(v, true), mk_lit(u, !bt)]);
                                }
                                if self.set_var(u, bt)? {
                                    changed = true;
                                }
                            } else if self.set_xor2(v, u, !bt)? {
                                changed = true;
                            }
                        }
                    }
                }
            }
        }

        Ok(changed)
    }

    fn probe_bcp_2sat(&self, var: usize, val: bool) -> (Option<Vec<Option<bool>>>, Vec<Vec<u32>>) {
        let mut assign = self.fixed.clone();
        let mut lmask = self.pair_mask.clone();
        let mut hints: Vec<Vec<u32>> = Vec::new();
        let track_hints = self.logger.is_some();
        let guard_lit = mk_lit(var, val); // clause (guard_lit \/ derived_lit) means (var == val => derived_lit)
        assign[var] = Some(val);

        let get_lm = |lm: &[u8], i: usize, j: usize| -> u8 {
            if i < j {
                lm[i * self.n + j]
            } else {
                let m = lm[j * self.n + i];
                (m & 0b1001) | ((m & 0b0010) << 1) | ((m & 0b0100) >> 1)
            }
        };

        let forbid_lm = |lm: &mut [u8], assign: &mut [Option<bool>], l1: u32, l2: u32| -> bool {
            let v1 = lit_var(l1);
            let v2 = lit_var(l2);
            if v1 == v2 {
                if l1 == l2 {
                    let b = !lit_neg(l1);
                    if let Some(old) = assign[v1] {
                        return old == b;
                    }
                    assign[v1] = Some(b);
                }
                return true;
            }
            let (a, b, bad_bit) = if v1 < v2 {
                let b1 = if lit_neg(l1) { 1 } else { 0 };
                let b2 = if lit_neg(l2) { 1 } else { 0 };
                (v1, v2, 1u8 << (b1 * 2 + b2))
            } else {
                let b1 = if lit_neg(l2) { 1 } else { 0 };
                let b2 = if lit_neg(l1) { 1 } else { 0 };
                (v2, v1, 1u8 << (b1 * 2 + b2))
            };
            let idx = a * self.n + b;
            lm[idx] &= 0b1111 ^ bad_bit;
            if lm[idx] == 0 {
                return false;
            }
            true
        };

        loop {
            let mut pushed = false;

            // Propagate assign through pair_mask
            for u in 0..self.n {
                if let Some(uval) = assign[u] {
                    for w in 0..self.n {
                        if w == u {
                            continue;
                        }
                        let m = get_lm(&lmask, u, w);
                        if m == 0b1111 {
                            continue;
                        }
                        let shifted = if uval { m >> 2 } else { m & 0b0011 };
                        match shifted & 0b11 {
                            0 => return (None, hints),
                            0b01 => {
                                if let Some(old) = assign[w] {
                                    if old {
                                        return (None, hints);
                                    }
                                } else {
                                    assign[w] = Some(false);
                                    pushed = true;
                                }
                            }
                            0b10 => {
                                if let Some(old) = assign[w] {
                                    if !old {
                                        return (None, hints);
                                    }
                                } else {
                                    assign[w] = Some(true);
                                    pushed = true;
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }

            // Propagate clauses (units and newly formed 2-clauses!)
            for cl in &self.clauses {
                let mut sat = false;
                let mut unset = [0u32; 3];
                let mut ucnt = 0usize;
                for &lit in cl {
                    let v = lit_var(lit);
                    let neg = lit_neg(lit);
                    match assign[v] {
                        Some(b) => {
                            if b ^ neg {
                                sat = true;
                                break;
                            }
                        }
                        None => {
                            if ucnt < 3 {
                                unset[ucnt] = lit;
                            }
                            ucnt += 1;
                        }
                    }
                }
                if sat {
                    continue;
                }
                if ucnt == 0 {
                    return (None, hints);
                }
                if ucnt == 1 {
                    let ul = unset[0];
                    let uv = lit_var(ul);
                    let uval = !lit_neg(ul);
                    if let Some(old) = assign[uv] {
                        if old != uval {
                            return (None, hints);
                        }
                    } else {
                        assign[uv] = Some(uval);
                        pushed = true;
                    }
                } else if ucnt == 2 {
                    let old_m = get_lm(&lmask, lit_var(unset[0]), lit_var(unset[1]));
                    if !forbid_lm(&mut lmask, &mut assign, unset[0], unset[1]) {
                        if track_hints {
                            let va = lit_var(unset[0]);
                            hints.push(vec![guard_lit, mk_lit(va, true)]);
                        }
                        return (None, hints);
                    }
                    let new_m = get_lm(&lmask, lit_var(unset[0]), lit_var(unset[1]));
                    if new_m != old_m {
                        pushed = true;
                    }
                }
            }

            if !pushed {
                // Run fast 2-SAT bitset transitive closure on lmask to uncover hidden 2-SAT conflicts/units!
                let num_lits = 2 * self.n;
                let words = (num_lits + 63) / 64;
                let mut reach = vec![0u64; num_lits * words];
                for u in 0..num_lits {
                    reach[u * words + u / 64] |= 1u64 << (u % 64);
                }
                for i in 0..self.n {
                    if assign[i].is_some() {
                        continue;
                    }
                    for j in (i + 1)..self.n {
                        if assign[j].is_some() {
                            continue;
                        }
                        let m = get_lm(&lmask, i, j);
                        if m != 0b1111 {
                            for bi in 0..2 {
                                for bj in 0..2 {
                                    if (m & (1 << (bi * 2 + bj))) == 0 {
                                        let li_t = mk_lit(i, bi == 0) as usize;
                                        let lj_f = mk_lit(j, bj == 1) as usize;
                                        let lj_t = mk_lit(j, bj == 0) as usize;
                                        let li_f = mk_lit(i, bi == 1) as usize;
                                        reach[li_t * words + lj_f / 64] |= 1u64 << (lj_f % 64);
                                        reach[lj_t * words + li_f / 64] |= 1u64 << (li_f % 64);
                                    }
                                }
                            }
                        }
                    }
                }
                for k in 0..num_lits {
                    let kw = k / 64;
                    let kb = 1u64 << (k % 64);
                    let k_off = k * words;
                    for i in 0..num_lits {
                        if (reach[i * words + kw] & kb) != 0 {
                            let i_off = i * words;
                            for w in 0..words {
                                reach[i_off + w] |= reach[k_off + w];
                            }
                        }
                    }
                }
                for v in 0..self.n {
                    if assign[v].is_some() {
                        continue;
                    }
                    let lt = 2 * v;
                    let lf = 2 * v + 1;
                    let lt_implies_lf = (reach[lt * words + lf / 64] >> (lf % 64)) & 1 != 0;
                    let lf_implies_lt = (reach[lf * words + lt / 64] >> (lt % 64)) & 1 != 0;
                    if lt_implies_lf && lf_implies_lt {
                        if track_hints {
                            hints.push(vec![guard_lit, mk_lit(v, true)]);
                        }
                        return (None, hints);
                    } else if lt_implies_lf {
                        assign[v] = Some(false);
                        if track_hints {
                            hints.push(vec![guard_lit, mk_lit(v, true)]);
                        }
                        pushed = true;
                    } else if lf_implies_lt {
                        assign[v] = Some(true);
                        if track_hints {
                            hints.push(vec![guard_lit, mk_lit(v, false)]);
                        }
                        pushed = true;
                    }
                }
                if !pushed {
                    break;
                }
            }
        }
        (Some(assign), hints)
    }

    fn insert_rref_row(
        basis: &mut BTreeMap<u64, (Vec<u64>, Vec<usize>)>,
        mut row: Vec<u64>,
        mut comb: Vec<usize>,
        track_comb: bool,
    ) -> Result<Option<Vec<u64>>, Vec<usize>> {
        while let Some(&piv) = row.first() {
            if let Some((brow, bcomb)) = basis.get(&piv) {
                row = xor_poly_desc(&row, brow);
                if track_comb {
                    comb = xor_comb_asc(&comb, bcomb);
                }
            } else {
                if piv == 0 {
                    return Err(comb);
                }
                basis.insert(piv, (row.clone(), comb));
                return Ok(Some(row));
            }
        }
        Ok(None)
    }

    fn phase_b_rm_rref(&mut self) -> Result<bool, &'static str> {
        let mut changed = false;
        let track_comb = self.logger.is_some();
        let mut origins: Vec<PolyOrigin> = Vec::new();
        let mut basis: BTreeMap<u64, (Vec<u64>, Vec<usize>)> = BTreeMap::new();
        let mut polys_inserted = 0usize;
        let max_polys = if self.use_rm4 { 110_000usize } else { 45_000usize };
        let max_deg: u64 = if self.use_rm4 { 4 } else { 3 };

        macro_rules! push_poly {
            ($poly:expr, $supp:expr, $extras:expr) => {{
                let p_vec: Vec<u64> = $poly;
                if !p_vec.is_empty() {
                    let comb = if track_comb {
                        let idx = origins.len();
                        origins.push(PolyOrigin {
                            poly: p_vec.clone(),
                            supp: $supp,
                            extra_clauses: $extras,
                        });
                        vec![idx]
                    } else {
                        Vec::new()
                    };
                    if let Err(unsat_comb) =
                        Self::insert_rref_row(&mut basis, p_vec, comb, track_comb)
                    {
                        if let Some(ref mut lg) = self.logger {
                            lg.certify_gf2_combination(&origins, &unsat_comb, &[vec![]]);
                        }
                        return Err(if self.use_rm4 {
                            "UNSAT_RM4_RREF"
                        } else {
                            "UNSAT_RM3_RREF"
                        });
                    }
                    polys_inserted += 1;
                }
            }};
        }

        // 0) Width-3 Diamond Resolution on 3-clauses -> derived 2-clauses & 3-clauses!
        let mut existing_cl_set: HashSet<Vec<u32>> = self.clauses.iter().cloned().collect();
        let mut supp3_set: HashSet<[usize; 3]> = HashSet::new();
        let mut pair_idx3: HashMap<(u32, u32), Vec<u32>> = HashMap::new();
        let mut clauses3_init: Vec<[u32; 3]> = Vec::new();

        for cl in &self.clauses {
            if cl.len() == 3 {
                let c = [cl[0], cl[1], cl[2]];
                clauses3_init.push(c);
                let mut vs = [lit_var(c[0]), lit_var(c[1]), lit_var(c[2])];
                vs.sort_unstable();
                supp3_set.insert(vs);
                for (a, b, d) in [
                    (c[0], c[1], c[2]),
                    (c[0], c[2], c[1]),
                    (c[1], c[0], c[2]),
                    (c[1], c[2], c[0]),
                    (c[2], c[0], c[1]),
                    (c[2], c[1], c[0]),
                ] {
                    pair_idx3.entry((a, b)).or_default().push(d);
                }
            }
        }

        let mut diamond_added = Vec::new();
        for (&(piv, sh), thirds_pos) in &pair_idx3 {
            if lit_neg(piv) {
                continue;
            }
            if let Some(thirds_neg) = pair_idx3.get(&(neg_lit(piv), sh)) {
                for &b_lit in thirds_pos {
                    for &c_lit in thirds_neg {
                        if b_lit == neg_lit(c_lit)
                            || sh == neg_lit(b_lit)
                            || sh == neg_lit(c_lit)
                        {
                            continue;
                        }
                        let mut nc = vec![sh, b_lit, c_lit];
                        nc.sort_unstable();
                        nc.dedup();
                        if !existing_cl_set.contains(&nc) {
                            if nc.len() <= 2 {
                                existing_cl_set.insert(nc.clone());
                                diamond_added.push(nc);
                            } else {
                                let mut sp = [lit_var(nc[0]), lit_var(nc[1]), lit_var(nc[2])];
                                sp.sort_unstable();
                                if supp3_set.contains(&sp)
                                    || clauses3_init.len() + diamond_added.len() < 3000
                                {
                                    existing_cl_set.insert(nc.clone());
                                    diamond_added.push(nc);
                                }
                            }
                        }
                    }
                }
            }
        }
        if !diamond_added.is_empty() {
            changed = true;
            for nc in diamond_added {
                if nc.len() == 1 {
                    if self.set_var(lit_var(nc[0]), !lit_neg(nc[0]))? {
                        changed = true;
                    }
                } else if nc.len() == 2 {
                    if self.forbid_2clause(nc[0], nc[1])? {
                        changed = true;
                    }
                    self.clauses.push(nc);
                } else {
                    self.log_rup(&nc);
                    self.clauses.push(nc);
                }
            }
        }

        // 1) All 2-clauses and non-trivial pair_masks -> RM(2, n) + Macaulay deg-3 lift
        let mut polys_2: Vec<(usize, usize, Vec<u64>)> = Vec::new();
        for i in 0..self.n {
            if self.uf_find(i).0 != i || self.fixed[i].is_some() {
                continue;
            }
            for j in (i + 1)..self.n {
                if self.uf_find(j).0 != j || self.fixed[j].is_some() {
                    continue;
                }
                let m = self.get_mask(i, j);
                if m != 0b1111 {
                    for bi in 0..2 {
                        for bj in 0..2 {
                            if (m & (1 << (bi * 2 + bj))) == 0 {
                                let l1 = mk_lit(i, bi == 1);
                                let l2 = mk_lit(j, bj == 1);
                                let p = clause2_to_poly(l1, l2);
                                push_poly!(p.clone(), vec![i, j], Vec::new());
                                polys_2.push((i, j, p));
                            }
                        }
                    }
                }
            }
        }

        // 2) Width-3 RM(2, 3) collisions + 3-clauses in RM(3, n)
        let mut support3: HashMap<[usize; 3], Vec<[u32; 3]>> = HashMap::new();
        let mut by_lit: Vec<Vec<usize>> = vec![Vec::new(); 2 * self.n];
        let mut clauses3: Vec<[u32; 3]> = Vec::new();
        let mut var_nbrs: Vec<HashSet<usize>> = vec![HashSet::new(); self.n];
        for cl in &self.clauses {
            if cl.len() == 3 {
                let c = [cl[0], cl[1], cl[2]];
                let mut vs = [lit_var(c[0]), lit_var(c[1]), lit_var(c[2])];
                vs.sort_unstable();
                support3.entry(vs).or_default().push(c);
                let idx = clauses3.len();
                clauses3.push(c);
                for &l in &c {
                    by_lit[l as usize].push(idx);
                }
                var_nbrs[vs[0]].insert(vs[1]);
                var_nbrs[vs[0]].insert(vs[2]);
                var_nbrs[vs[1]].insert(vs[0]);
                var_nbrs[vs[1]].insert(vs[2]);
                var_nbrs[vs[2]].insert(vs[0]);
                var_nbrs[vs[2]].insert(vs[1]);
            }
        }

        // Macaulay deg-3 lift of 2-clauses with neighboring variables
        for (i, j, p2) in &polys_2 {
            for &k in var_nbrs[*i].iter().chain(var_nbrs[*j].iter()) {
                if k == *i || k == *j || polys_inserted >= max_polys {
                    continue;
                }
                let p3 = mul_var_poly_desc(p2, k, max_deg);
                push_poly!(p3, vec![*i, *j, k], Vec::new());
            }
        }

        // RM(2, 3) collisions on same 3-var support
        for (vs, cls) in &support3 {
            if cls.len() >= 2 {
                let p0 = clause3_to_poly(cls[0][0], cls[0][1], cls[0][2]);
                for c in &cls[1..] {
                    let pk = clause3_to_poly(c[0], c[1], c[2]);
                    let diff = xor_poly_desc(&p0, &pk);
                    push_poly!(diff, vs.to_vec(), Vec::new());
                }
            }
        }

        // 2b) 4-Variable Petal Vanishing Ideals in RM(3, 4)!
        let mut by_pair_supp: HashMap<(usize, usize), Vec<[usize; 3]>> = HashMap::new();
        for &sp in support3.keys() {
            by_pair_supp.entry((sp[0], sp[1])).or_default().push(sp);
            by_pair_supp.entry((sp[0], sp[2])).or_default().push(sp);
            by_pair_supp.entry((sp[1], sp[2])).or_default().push(sp);
        }
        let mut cand_u4: HashSet<[usize; 4]> = HashSet::new();
        for sp_list in by_pair_supp.values() {
            if sp_list.len() >= 2 && sp_list.len() <= 16 {
                for a in 0..sp_list.len() {
                    for b in (a + 1)..sp_list.len() {
                        let s1 = sp_list[a];
                        let s2 = sp_list[b];
                        let mut u = [s1[0], s1[1], s1[2], 0];
                        let mut ulen = 3;
                        for x in s2 {
                            if !u[..ulen].contains(&x) {
                                if ulen < 4 {
                                    u[ulen] = x;
                                }
                                ulen += 1;
                            }
                        }
                        if ulen == 4 {
                            u.sort_unstable();
                            cand_u4.insert(u);
                        }
                    }
                }
            }
        }

        let mut dense_u4: Vec<([usize; 4], usize)> = Vec::new();
        for &u4 in &cand_u4 {
            if polys_inserted >= max_polys {
                break;
            }
            let (v0, v1, v2, v3) = (u4[0], u4[1], u4[2], u4[3]);
            let mut local_cls: Vec<[u32; 3]> = Vec::new();
            for tri in [[v0, v1, v2], [v0, v1, v3], [v0, v2, v3], [v1, v2, v3]] {
                if let Some(cs) = support3.get(&tri) {
                    local_cls.extend_from_slice(cs);
                }
            }
            if local_cls.len() < 2 {
                continue;
            }
            if self.use_rm4 && local_cls.len() >= 3 {
                dense_u4.push((u4, local_cls.len()));
            }
            let masks = [
                (0usize, 1usize, self.get_mask(v0, v1)),
                (0, 2, self.get_mask(v0, v2)),
                (0, 3, self.get_mask(v0, v3)),
                (1, 2, self.get_mask(v1, v2)),
                (1, 3, self.get_mask(v1, v3)),
                (2, 3, self.get_mask(v2, v3)),
            ];
            let mut surv_mask = 0u16;
            let mut pair_surv = [0u8; 6];
            let mut tri_surv = [0u8; 4];
            let tris4 = [
                (0usize, 1usize, 2usize),
                (0, 1, 3),
                (0, 2, 3),
                (1, 2, 3),
            ];
            for a in 0..16u16 {
                let bs = [
                    (a & 1) != 0,
                    ((a >> 1) & 1) != 0,
                    ((a >> 2) & 1) != 0,
                    ((a >> 3) & 1) != 0,
                ];
                let mut ok = true;
                for &(i, j, m) in &masks {
                    let bi = if bs[i] { 1 } else { 0 };
                    let bj = if bs[j] { 1 } else { 0 };
                    if (m & (1 << (bi * 2 + bj))) == 0 {
                        ok = false;
                        break;
                    }
                }
                if !ok {
                    continue;
                }
                for c in &local_cls {
                    let mut c_sat = false;
                    for &l in c {
                        let lv = lit_var(l);
                        let b = if lv == v0 {
                            bs[0]
                        } else if lv == v1 {
                            bs[1]
                        } else if lv == v2 {
                            bs[2]
                        } else {
                            bs[3]
                        };
                        if b ^ lit_neg(l) {
                            c_sat = true;
                            break;
                        }
                    }
                    if !c_sat {
                        ok = false;
                        break;
                    }
                }
                if ok {
                    surv_mask |= 1 << a;
                    if self.use_rm4 {
                        for (pi, &(i, j, _)) in masks.iter().enumerate() {
                            let bi = if bs[i] { 1 } else { 0 };
                            let bj = if bs[j] { 1 } else { 0 };
                            pair_surv[pi] |= 1u8 << (bi * 2 + bj);
                        }
                        for (ti, &(i, j, k)) in tris4.iter().enumerate() {
                            let bi = if bs[i] { 1 } else { 0 };
                            let bj = if bs[j] { 1 } else { 0 };
                            let bk = if bs[k] { 1 } else { 0 };
                            tri_surv[ti] |= 1u8 << (bi * 4 + bj * 2 + bk);
                        }
                    }
                }
            }
            if surv_mask == 0 {
                if let Some(ref mut lg) = self.logger {
                    lg.derive_clause_over_cube_raw(&[], &u4);
                }
                return Err("UNSAT_PETAL4");
            }
            if self.use_rm4 {
                for (pi, &(i, j, old_m)) in masks.iter().enumerate() {
                    let ps = pair_surv[pi];
                    let newly_forbid = old_m & !ps;
                    if newly_forbid != 0 {
                        let va = u4[i];
                        let vb = u4[j];
                        if let Some(ref mut lg) = self.logger {
                            for ba in 0..2usize {
                                for bb in 0..2usize {
                                    if (newly_forbid & (1u8 << (ba * 2 + bb))) != 0 {
                                        lg.derive_clause_over_cube_raw(
                                            &[(va + 1, ba == 0), (vb + 1, bb == 0)],
                                            &u4,
                                        );
                                    }
                                }
                            }
                        }
                        if self.tighten_mask_inner(va, vb, ps, false)? {
                            changed = true;
                        }
                    }
                }
                if self.clauses.len() < 3600 {
                    for (ti, &(i, j, k)) in tris4.iter().enumerate() {
                        let ts = tri_surv[ti];
                        if ts == 0xff {
                            continue;
                        }
                        let (va, vb, vc) = (u4[i], u4[j], u4[k]);
                        let mab = self.get_mask(va, vb);
                        let mac = self.get_mask(va, vc);
                        let mbc = self.get_mask(vb, vc);
                        for bit in 0..8u8 {
                            if (ts & (1u8 << bit)) != 0 {
                                continue;
                            }
                            let ba = ((bit >> 2) & 1) as usize;
                            let bb = ((bit >> 1) & 1) as usize;
                            let bc = (bit & 1) as usize;
                            // Skip if already forbidden by pair_mask
                            if (mab & (1 << (ba * 2 + bb))) == 0
                                || (mac & (1 << (ba * 2 + bc))) == 0
                                || (mbc & (1 << (bb * 2 + bc))) == 0
                            {
                                continue;
                            }
                            let mut nc = vec![
                                mk_lit(va, ba == 1),
                                mk_lit(vb, bb == 1),
                                mk_lit(vc, bc == 1),
                            ];
                            nc.sort_unstable();
                            if existing_cl_set.insert(nc.clone()) {
                                if let Some(ref mut lg) = self.logger {
                                    lg.derive_clause_over_cube_raw(
                                        &[
                                            (va + 1, ba == 0),
                                            (vb + 1, bb == 0),
                                            (vc + 1, bc == 0),
                                        ],
                                        &u4,
                                    );
                                }
                                self.clauses.push(nc);
                                changed = true;
                                if self.clauses.len() >= 3600 {
                                    break;
                                }
                            }
                        }
                    }
                }
            }
            let ideal_polys = extract_rm3_4_ideal(u4, surv_mask);
            for p in ideal_polys {
                push_poly!(p, u4.to_vec(), Vec::new());
            }
        }

        // 2c) RM(4, 5) 5-Variable Simplex Vanishing Ideals & Pairwise Projections (in --rm4 mode!)
        if self.use_rm4 && !dense_u4.is_empty() {
            let mut cand_u5_score: HashMap<[usize; 5], usize> = HashMap::new();
            for &(u4, cnt4) in &dense_u4 {
                // Expand u4 by any triangle sharing 2 variables with u4
                let pairs6 = [
                    (u4[0], u4[1]),
                    (u4[0], u4[2]),
                    (u4[0], u4[3]),
                    (u4[1], u4[2]),
                    (u4[1], u4[3]),
                    (u4[2], u4[3]),
                ];
                for pr in pairs6 {
                    if let Some(tris) = by_pair_supp.get(&pr) {
                        if tris.len() > 14 {
                            continue;
                        }
                        for &tri in tris {
                            let mut extra = None;
                            for x in tri {
                                if !u4.contains(&x) {
                                    extra = Some(x);
                                    break;
                                }
                            }
                            if let Some(v5) = extra {
                                let mut u5 = [u4[0], u4[1], u4[2], u4[3], v5];
                                u5.sort_unstable();
                                let e = cand_u5_score.entry(u5).or_insert(0);
                                *e = (*e).max(cnt4 + 1);
                            }
                        }
                    }
                }
            }

            let mut u5_list: Vec<([usize; 5], usize)> = Vec::new();
            for (u5, _) in cand_u5_score {
                let mut tri_cnt = 0usize;
                for a in 0..5 {
                    for b in (a + 1)..5 {
                        for c in (b + 1)..5 {
                            if let Some(cs) = support3.get(&[u5[a], u5[b], u5[c]]) {
                                tri_cnt += cs.len();
                            }
                        }
                    }
                }
                if tri_cnt >= 4 {
                    u5_list.push((u5, tri_cnt));
                }
            }
            u5_list.sort_unstable_by(|a, b| b.1.cmp(&a.1));
            u5_list.truncate(1200);

            let mut rm4_added = 0usize;
            for (u5, _) in u5_list {
                if polys_inserted >= max_polys {
                    break;
                }
                let mut local_cls: Vec<[u32; 3]> = Vec::new();
                for a in 0..5 {
                    for b in (a + 1)..5 {
                        for c in (b + 1)..5 {
                            if let Some(cs) = support3.get(&[u5[a], u5[b], u5[c]]) {
                                local_cls.extend_from_slice(cs);
                            }
                        }
                    }
                }
                let mut masks = [(0usize, 0usize, 0u8); 10];
                let mut mi = 0;
                for i in 0..5 {
                    for j in (i + 1)..5 {
                        masks[mi] = (i, j, self.get_mask(u5[i], u5[j]));
                        mi += 1;
                    }
                }
                let mut surv_mask = 0u32;
                let mut pair_surv = [0u8; 10];
                let mut tri_surv5 = [0u8; 10];
                let tris5 = [
                    (0usize, 1usize, 2usize),
                    (0, 1, 3),
                    (0, 1, 4),
                    (0, 2, 3),
                    (0, 2, 4),
                    (0, 3, 4),
                    (1, 2, 3),
                    (1, 2, 4),
                    (1, 3, 4),
                    (2, 3, 4),
                ];
                for a in 0..32u32 {
                    let bs = [
                        (a & 1) != 0,
                        ((a >> 1) & 1) != 0,
                        ((a >> 2) & 1) != 0,
                        ((a >> 3) & 1) != 0,
                        ((a >> 4) & 1) != 0,
                    ];
                    let mut ok = true;
                    for &(i, j, m) in &masks {
                        let bi = if bs[i] { 1 } else { 0 };
                        let bj = if bs[j] { 1 } else { 0 };
                        if (m & (1 << (bi * 2 + bj))) == 0 {
                            ok = false;
                            break;
                        }
                    }
                    if !ok {
                        continue;
                    }
                    for c in &local_cls {
                        let mut c_sat = false;
                        for &l in c {
                            let lv = lit_var(l);
                            let b = if lv == u5[0] {
                                bs[0]
                            } else if lv == u5[1] {
                                bs[1]
                            } else if lv == u5[2] {
                                bs[2]
                            } else if lv == u5[3] {
                                bs[3]
                            } else {
                                bs[4]
                            };
                            if b ^ lit_neg(l) {
                                c_sat = true;
                                break;
                            }
                        }
                        if !c_sat {
                            ok = false;
                            break;
                        }
                    }
                    if ok {
                        surv_mask |= 1u32 << a;
                        for (pi, &(i, j, _)) in masks.iter().enumerate() {
                            let bi = if bs[i] { 1 } else { 0 };
                            let bj = if bs[j] { 1 } else { 0 };
                            pair_surv[pi] |= 1u8 << (bi * 2 + bj);
                        }
                        for (ti, &(i, j, k)) in tris5.iter().enumerate() {
                            let bi = if bs[i] { 1 } else { 0 };
                            let bj = if bs[j] { 1 } else { 0 };
                            let bk = if bs[k] { 1 } else { 0 };
                            tri_surv5[ti] |= 1u8 << (bi * 4 + bj * 2 + bk);
                        }
                    }
                }
                if surv_mask == 0 {
                    if let Some(ref mut lg) = self.logger {
                        lg.derive_clause_over_cube_raw(&[], &u5);
                    }
                    return Err("UNSAT_SIMPLEX5");
                }
                for (pi, &(i, j, old_m)) in masks.iter().enumerate() {
                    let ps = pair_surv[pi];
                    let newly_forbid = old_m & !ps;
                    if newly_forbid != 0 {
                        let va = u5[i];
                        let vb = u5[j];
                        if let Some(ref mut lg) = self.logger {
                            for ba in 0..2usize {
                                for bb in 0..2usize {
                                    if (newly_forbid & (1u8 << (ba * 2 + bb))) != 0 {
                                        lg.derive_clause_over_cube_raw(
                                            &[(va + 1, ba == 0), (vb + 1, bb == 0)],
                                            &u5,
                                        );
                                    }
                                }
                            }
                        }
                        if self.tighten_mask_inner(va, vb, ps, false)? {
                            changed = true;
                        }
                    }
                }
                if self.clauses.len() < 3600 {
                    for (ti, &(i, j, k)) in tris5.iter().enumerate() {
                        let ts = tri_surv5[ti];
                        if ts == 0xff {
                            continue;
                        }
                        let (va, vb, vc) = (u5[i], u5[j], u5[k]);
                        let mab = self.get_mask(va, vb);
                        let mac = self.get_mask(va, vc);
                        let mbc = self.get_mask(vb, vc);
                        for bit in 0..8u8 {
                            if (ts & (1u8 << bit)) != 0 {
                                continue;
                            }
                            let ba = ((bit >> 2) & 1) as usize;
                            let bb = ((bit >> 1) & 1) as usize;
                            let bc = (bit & 1) as usize;
                            if (mab & (1 << (ba * 2 + bb))) == 0
                                || (mac & (1 << (ba * 2 + bc))) == 0
                                || (mbc & (1 << (bb * 2 + bc))) == 0
                            {
                                continue;
                            }
                            let mut nc = vec![
                                mk_lit(va, ba == 1),
                                mk_lit(vb, bb == 1),
                                mk_lit(vc, bc == 1),
                            ];
                            nc.sort_unstable();
                            if existing_cl_set.insert(nc.clone()) {
                                if let Some(ref mut lg) = self.logger {
                                    lg.derive_clause_over_cube_raw(
                                        &[
                                            (va + 1, ba == 0),
                                            (vb + 1, bb == 0),
                                            (vc + 1, bc == 0),
                                        ],
                                        &u5,
                                    );
                                }
                                self.clauses.push(nc);
                                changed = true;
                                if self.clauses.len() >= 3600 {
                                    break;
                                }
                            }
                        }
                    }
                }
                let ideal_polys = extract_rm4_5_ideal(u5, surv_mask);
                for p in ideal_polys {
                    if polys_inserted >= max_polys {
                        break;
                    }
                    push_poly!(p, u5.to_vec(), Vec::new());
                    rm4_added += 1;
                }
            }
            self.rm4_polys += rm4_added;
        }

        // 3) 1-step resolution on 3-clauses -> derived 2/3-clauses & Tetrahedral RM(3, 4) collisions!
        let mut support4: HashMap<[usize; 4], Vec<[bool; 4]>> = HashMap::new();
        let mut derived_2cls: Vec<[u32; 2]> = Vec::new();
        let mut derived_3cls: Vec<[u32; 3]> = Vec::new();

        for v in 0..self.n {
            if self.uf_find(v).0 != v || self.fixed[v].is_some() {
                continue;
            }
            let pos = &by_lit[mk_lit(v, false) as usize];
            let neg = &by_lit[mk_lit(v, true) as usize];
            if pos.is_empty() || neg.is_empty() {
                continue;
            }
            for &ip in pos {
                let cp = clauses3[ip];
                for &in_ in neg {
                    let cn = clauses3[in_];
                    let mut res = [0u32; 4];
                    let mut rlen = 0usize;
                    for &l in &cp {
                        if lit_var(l) != v {
                            res[rlen] = l;
                            rlen += 1;
                        }
                    }
                    let mut taut = false;
                    for &l in &cn {
                        if lit_var(l) != v {
                            let mut dup = false;
                            for k in 0..rlen {
                                if res[k] == l {
                                    dup = true;
                                    break;
                                }
                                if (res[k] ^ 1) == l {
                                    taut = true;
                                    break;
                                }
                            }
                            if taut {
                                break;
                            }
                            if !dup {
                                res[rlen] = l;
                                rlen += 1;
                            }
                        }
                    }
                    if taut {
                        continue;
                    }
                    if rlen == 2 {
                        derived_2cls.push([res[0], res[1]]);
                    } else if rlen == 3 {
                        if derived_3cls.len() < 4000 {
                            let mut s = [res[0], res[1], res[2]];
                            s.sort_unstable();
                            derived_3cls.push(s);
                        }
                    } else if rlen == 4 {
                        let mut pair = [
                            (lit_var(res[0]), !lit_neg(res[0])),
                            (lit_var(res[1]), !lit_neg(res[1])),
                            (lit_var(res[2]), !lit_neg(res[2])),
                            (lit_var(res[3]), !lit_neg(res[3])),
                        ];
                        pair.sort_unstable_by_key(|x| x.0);
                        let vs = [pair[0].0, pair[1].0, pair[2].0, pair[3].0];
                        let ps = [pair[0].1, pair[1].1, pair[2].1, pair[3].1];
                        let entry = support4.entry(vs).or_default();
                        if !entry.contains(&ps) && entry.len() < 8 {
                            entry.push(ps);
                        }
                    }
                }
            }
        }

        for [a, b] in derived_2cls {
            if self.forbid_2clause(a, b)? {
                changed = true;
            }
            let p = clause2_to_poly(a, b);
            push_poly!(p, vec![lit_var(a), lit_var(b)], Vec::new());
        }
        for &[a, b, c] in &derived_3cls {
            let p = clause3_to_poly(a, b, c);
            if polys_inserted < max_polys {
                let extra = if track_comb {
                    vec![vec![a, b, c]]
                } else {
                    Vec::new()
                };
                push_poly!(p, vec![lit_var(a), lit_var(b), lit_var(c)], extra);
            }
        }

        // Tetrahedral RM(3, 4) collisions on 4-var supports
        for (vs, pols) in &support4 {
            if pols.len() >= 2 && polys_inserted < max_polys {
                let t0 = clause4_rm3_tail(*vs, pols[0]);
                let cl0: Vec<u32> = (0..4).map(|q| mk_lit(vs[q], !pols[0][q])).collect();
                for pk in &pols[1..] {
                    let tk = clause4_rm3_tail(*vs, *pk);
                    let col = xor_poly_desc(&t0, &tk);
                    let extras = if track_comb {
                        let clk: Vec<u32> = (0..4).map(|q| mk_lit(vs[q], !pk[q])).collect();
                        vec![cl0.clone(), clk]
                    } else {
                        Vec::new()
                    };
                    push_poly!(col, vs.to_vec(), extras);
                    if polys_inserted >= max_polys {
                        break;
                    }
                }
            }
            // In --rm4 mode, also insert full degree-4 4-clauses that sit on dense triangles
            if self.use_rm4 && polys_inserted < max_polys && pols.len() >= 2 {
                let p4 = clause4_to_poly(*vs, pols[0]);
                let extras = if track_comb {
                    vec![(0..4).map(|q| mk_lit(vs[q], !pols[0][q])).collect()]
                } else {
                    Vec::new()
                };
                push_poly!(p4, vs.to_vec(), extras);
                self.rm4_polys += 1;
            }
        }

        // 3b) In --rm4 mode: 5-local RM(4, 5) collisions (resolving 4-clauses from support4 with 3-clauses
        // filtered by shared variables so they land on dense 5-var simplices!)
        if self.use_rm4 && polys_inserted < max_polys {
            let mut support5: HashMap<[usize; 5], Vec<([bool; 5], Vec<u32>)>> = HashMap::new();
            let mut c4_checked = 0usize;
            for (vs4, pols4) in &support4 {
                if pols4.len() < 2 {
                    continue;
                }
                c4_checked += 1;
                if c4_checked > 1500 {
                    break;
                }
                for &p4 in pols4.iter().take(2) {
                    let cl4 = [
                        mk_lit(vs4[0], !p4[0]),
                        mk_lit(vs4[1], !p4[1]),
                        mk_lit(vs4[2], !p4[2]),
                        mk_lit(vs4[3], !p4[3]),
                    ];
                    for piv_i in 0..4 {
                        let piv_l = cl4[piv_i];
                        let neg_p = neg_lit(piv_l);
                        let opp_list = &by_lit[neg_p as usize];
                        if opp_list.len() > 12 {
                            continue;
                        }
                        for &c3_idx in opp_list {
                            let c3 = clauses3[c3_idx];
                            // Filter: require c3 to share at least 1 other variable with vs4 (so resolvent has <= 5 vars)
                            let mut res = [0u32; 5];
                            let mut rlen = 0usize;
                            for k in 0..4 {
                                if k != piv_i {
                                    res[rlen] = cl4[k];
                                    rlen += 1;
                                }
                            }
                            let mut taut = false;
                            for &l in &c3 {
                                if l == neg_p {
                                    continue;
                                }
                                let mut dup = false;
                                for k in 0..rlen {
                                    if res[k] == l {
                                        dup = true;
                                        break;
                                    }
                                    if (res[k] ^ 1) == l {
                                        taut = true;
                                        break;
                                    }
                                }
                                if taut {
                                    break;
                                }
                                if !dup {
                                    if rlen < 5 {
                                        res[rlen] = l;
                                    }
                                    rlen += 1;
                                }
                            }
                            if taut || rlen != 5 {
                                continue;
                            }
                            let mut pairs5 = [
                                (lit_var(res[0]), !lit_neg(res[0])),
                                (lit_var(res[1]), !lit_neg(res[1])),
                                (lit_var(res[2]), !lit_neg(res[2])),
                                (lit_var(res[3]), !lit_neg(res[3])),
                                (lit_var(res[4]), !lit_neg(res[4])),
                            ];
                            pairs5.sort_unstable_by_key(|x| x.0);
                            let vs5 = [
                                pairs5[0].0,
                                pairs5[1].0,
                                pairs5[2].0,
                                pairs5[3].0,
                                pairs5[4].0,
                            ];
                            let ps5 = [
                                pairs5[0].1,
                                pairs5[1].1,
                                pairs5[2].1,
                                pairs5[3].1,
                                pairs5[4].1,
                            ];
                            let entry = support5.entry(vs5).or_default();
                            if entry.len() < 4 && !entry.iter().any(|(ep, _)| *ep == ps5) {
                                let parent4 = if track_comb {
                                    cl4.to_vec()
                                } else {
                                    Vec::new()
                                };
                                entry.push((ps5, parent4));
                            }
                        }
                    }
                }
            }

            let mut rm4_col_added = 0usize;
            for (vs5, pols5) in &support5 {
                if pols5.len() >= 2 && polys_inserted < max_polys {
                    let t0 = clause5_rm4_tail(*vs5, pols5[0].0);
                    let cl5_0: Vec<u32> = (0..5).map(|q| mk_lit(vs5[q], !pols5[0].0[q])).collect();
                    for (pk, parent4_k) in &pols5[1..] {
                        let tk = clause5_rm4_tail(*vs5, *pk);
                        let col = xor_poly_desc(&t0, &tk);
                        let extras = if track_comb {
                            let cl5_k: Vec<u32> = (0..5).map(|q| mk_lit(vs5[q], !pk[q])).collect();
                            vec![pols5[0].1.clone(), cl5_0.clone(), parent4_k.clone(), cl5_k]
                        } else {
                            Vec::new()
                        };
                        push_poly!(col, vs5.to_vec(), extras);
                        rm4_col_added += 1;
                        if polys_inserted >= max_polys {
                            break;
                        }
                    }
                }
            }
            self.rm4_polys += rm4_col_added;
        }

        // Insert original 3-clauses into RM(3, n) / RM(4, n)
        for c in &clauses3 {
            if polys_inserted >= max_polys {
                break;
            }
            let p = clause3_to_poly(c[0], c[1], c[2]);
            push_poly!(p, vec![lit_var(c[0]), lit_var(c[1]), lit_var(c[2])], Vec::new());
        }

        self.rm3_polys += polys_inserted;

        // Back-substitute degree <= 2 rows among themselves to uncover hidden degree <= 1 equations!
        let mut deg2_basis: BTreeMap<u64, (Vec<u64>, Vec<usize>)> = BTreeMap::new();
        for (row, comb) in basis.values() {
            if let Some(&piv) = row.first() {
                if mono_deg(piv) <= 2 {
                    if let Err(unsat_comb) = Self::insert_rref_row(
                        &mut deg2_basis,
                        row.clone(),
                        comb.clone(),
                        track_comb,
                    ) {
                        if let Some(ref mut lg) = self.logger {
                            lg.certify_gf2_combination(&origins, &unsat_comb, &[vec![]]);
                        }
                        return Err("UNSAT_RM3_DEG2_RREF");
                    }
                }
            }
        }
        let d2_keys: Vec<u64> = deg2_basis.keys().copied().collect();
        for &k in &d2_keys {
            let (mut row, mut comb) = deg2_basis.get(&k).unwrap().clone();
            let mut idx = 1;
            while idx < row.len() {
                let m = row[idx];
                if let Some((brow, bcomb)) = deg2_basis.get(&m) {
                    row = xor_poly_desc(&row, brow);
                    if track_comb {
                        comb = xor_comb_asc(&comb, bcomb);
                    }
                } else {
                    idx += 1;
                }
            }
            if row.len() == 1 && row[0] == 0 {
                if let Some(ref mut lg) = self.logger {
                    lg.certify_gf2_combination(&origins, &comb, &[vec![]]);
                }
                return Err("UNSAT_RM3_DEG2_RREF");
            }
            deg2_basis.insert(k, (row, comb));
        }

        let mut linear_rows: Vec<(Vec<u64>, Vec<usize>)> = Vec::new();
        let mut deg2_rows: Vec<(Vec<u64>, Vec<usize>)> = Vec::new();
        for (row, comb) in deg2_basis.values() {
            if let Some(&piv) = row.first() {
                if mono_deg(piv) <= 1 {
                    linear_rows.push((row.clone(), comb.clone()));
                } else if mono_deg(piv) == 2 {
                    deg2_rows.push((row.clone(), comb.clone()));
                }
            }
        }

        let mut lin_basis: BTreeMap<u64, (Vec<u64>, Vec<usize>)> = BTreeMap::new();
        for (row, comb) in linear_rows {
            if let Err(unsat_comb) =
                Self::insert_rref_row(&mut lin_basis, row, comb, track_comb)
            {
                if let Some(ref mut lg) = self.logger {
                    lg.certify_gf2_combination(&origins, &unsat_comb, &[vec![]]);
                }
                return Err("UNSAT_RM3_LIN_RREF");
            }
        }
        let keys: Vec<u64> = lin_basis.keys().copied().collect();
        for &k in &keys {
            let (mut row, mut comb) = lin_basis.get(&k).unwrap().clone();
            let mut idx = 1;
            while idx < row.len() {
                let m = row[idx];
                if let Some((brow, bcomb)) = lin_basis.get(&m) {
                    row = xor_poly_desc(&row, brow);
                    if track_comb {
                        comb = xor_comb_asc(&comb, bcomb);
                    }
                } else {
                    idx += 1;
                }
            }
            if row.len() == 1 && row[0] == 0 {
                if let Some(ref mut lg) = self.logger {
                    lg.certify_gf2_combination(&origins, &comb, &[vec![]]);
                }
                return Err("UNSAT_RM3_LIN_RREF");
            }
            lin_basis.insert(k, (row, comb));
        }

        for (row, comb) in lin_basis.values() {
            let mut vars = Vec::new();
            let mut has_const = false;
            for &m in row {
                if m == 0 {
                    has_const = true;
                } else {
                    vars.push(mono_vars4(m).0[0]);
                }
            }
            if vars.is_empty() && has_const {
                if let Some(ref mut lg) = self.logger {
                    lg.certify_gf2_combination(&origins, comb, &[vec![]]);
                }
                return Err("UNSAT_RM3_CONST1");
            }
            if vars.len() == 1 {
                let v = vars[0];
                let (r, par) = self.uf_find(v);
                let rval = has_const ^ par;
                let need_cert = self.fixed[r].map_or(true, |old| old != rval);
                if need_cert {
                    if let Some(ref mut lg) = self.logger {
                        // x_v + has_const = 0 (mod 2) => x_v = has_const
                        lg.certify_gf2_combination(
                            &origins,
                            comb,
                            &[vec![(mono1(v), has_const)]],
                        );
                    }
                    if self.set_var_inner(v, has_const, false)? {
                        changed = true;
                    } else if self.logger.is_some() {
                        // Already fixed to opposite -> handled by set_var_inner returning Err
                    }
                }
            } else if vars.len() == 2 {
                let (u, v) = (vars[0], vars[1]);
                let (ru, pu) = self.uf_find(u);
                let (rv, pv) = self.uf_find(v);
                let rel = has_const ^ pu ^ pv;
                let need_cert = if ru == rv {
                    rel
                } else {
                    match (self.fixed[ru], self.fixed[rv]) {
                        (Some(fu), Some(fv)) => (fu ^ fv) != rel,
                        _ => true,
                    }
                };
                if need_cert {
                    if let Some(ref mut lg) = self.logger {
                        let targets = if has_const {
                            vec![
                                vec![(mono1(u), true), (mono1(v), true)],
                                vec![(mono1(u), false), (mono1(v), false)],
                            ]
                        } else {
                            vec![
                                vec![(mono1(u), false), (mono1(v), true)],
                                vec![(mono1(u), true), (mono1(v), false)],
                            ]
                        };
                        lg.certify_gf2_combination(&origins, comb, &targets);
                    }
                    if self.set_xor2_inner(u, v, has_const, false)? {
                        changed = true;
                    }
                }
            }
        }

        for (row, comb) in &deg2_rows {
            let mut vs = [usize::MAX; 3];
            let mut vcnt = 0usize;
            let mut too_many = false;
            for &m in row {
                let (mvs, deg) = mono_vars4(m);
                match deg {
                    0 => {}
                    1 => {
                        let a = mvs[0];
                        if !vs[..vcnt].contains(&a) {
                            if vcnt >= 2 {
                                too_many = true;
                                break;
                            }
                            vs[vcnt] = a;
                            vcnt += 1;
                        }
                    }
                    2 => {
                        for x in [mvs[0], mvs[1]] {
                            if !vs[..vcnt].contains(&x) {
                                if vcnt >= 2 {
                                    too_many = true;
                                    break;
                                }
                                vs[vcnt] = x;
                                vcnt += 1;
                            }
                        }
                        if too_many {
                            break;
                        }
                    }
                    _ => {
                        too_many = true;
                        break;
                    }
                }
            }
            if !too_many && vcnt == 2 {
                let (v0, v1) = (vs[0], vs[1]);
                let mut allowed = 0u8;
                for b0 in 0..2usize {
                    for b1 in 0..2usize {
                        let mut val = false;
                        for &m in row {
                            let (mvs, deg) = mono_vars4(m);
                            let term = match deg {
                                0 => true,
                                1 => {
                                    if mvs[0] == v0 {
                                        b0 == 1
                                    } else {
                                        b1 == 1
                                    }
                                }
                                2 => (b0 == 1) && (b1 == 1),
                                _ => false,
                            };
                            val ^= term;
                        }
                        if !val {
                            allowed |= 1u8 << (b0 * 2 + b1);
                        }
                    }
                }
                let old_m = self.get_mask(v0, v1);
                let newly_forbid = old_m & !allowed;
                if newly_forbid != 0 {
                    if let Some(ref mut lg) = self.logger {
                        // Certify each newly forbidden (b0, b1) via GF(2) parity + RUP 2-clause
                        let mut targets: Vec<Vec<(u64, bool)>> = Vec::new();
                        let mut rup_2cls: Vec<[u32; 2]> = Vec::new();
                        for b0 in 0..2usize {
                            for b1 in 0..2usize {
                                if (newly_forbid & (1u8 << (b0 * 2 + b1))) != 0 {
                                    let mut tl = Vec::new();
                                    for &m in row {
                                        let (mvs, deg) = mono_vars4(m);
                                        if deg == 0 {
                                            continue;
                                        }
                                        let m_val = match deg {
                                            1 => {
                                                if mvs[0] == v0 {
                                                    b0 == 1
                                                } else {
                                                    b1 == 1
                                                }
                                            }
                                            2 => (b0 == 1) && (b1 == 1),
                                            _ => false,
                                        };
                                        // lit_m is 0 when m == m_val -> pos if !m_val, neg if m_val
                                        tl.push((m, !m_val));
                                    }
                                    targets.push(tl);
                                    rup_2cls.push([mk_lit(v0, b0 == 1), mk_lit(v1, b1 == 1)]);
                                }
                            }
                        }
                        lg.certify_gf2_combination(&origins, comb, &targets);
                        for cl2 in rup_2cls {
                            lg.emit_rup_lits(&cl2);
                        }
                    }
                    if self.tighten_mask_inner(v0, v1, allowed, false)? {
                        changed = true;
                    }
                }
            }
        }

        Ok(changed)
    }

    fn phase_c_witt_triple_project_and_lift(&mut self) -> Result<bool, &'static str> {
        let mut changed = false;
        let mut support3: HashMap<[usize; 3], Vec<[u32; 3]>> = HashMap::new();
        for cl in &self.clauses {
            if cl.len() == 3 {
                let c = [cl[0], cl[1], cl[2]];
                let mut vs = [lit_var(c[0]), lit_var(c[1]), lit_var(c[2])];
                vs.sort_unstable();
                support3.entry(vs).or_default().push(c);
            }
        }

        let mut adj_pair: Vec<Vec<usize>> = vec![Vec::new(); self.n];
        for i in 0..self.n {
            if self.uf_find(i).0 != i || self.fixed[i].is_some() {
                continue;
            }
            for j in (i + 1)..self.n {
                if self.uf_find(j).0 != j || self.fixed[j].is_some() {
                    continue;
                }
                if self.get_mask(i, j) != 0b1111 {
                    adj_pair[i].push(j);
                    adj_pair[j].push(i);
                }
            }
        }
        let mut triangles: Vec<[usize; 3]> = support3.keys().copied().collect();
        for i in 0..self.n {
            for &j in &adj_pair[i] {
                if j <= i {
                    continue;
                }
                for &k in &adj_pair[j] {
                    if k <= j {
                        continue;
                    }
                    if self.get_mask(i, k) != 0b1111 {
                        let tri = [i, j, k];
                        if !support3.contains_key(&tri) {
                            triangles.push(tri);
                        }
                    }
                }
            }
        }

        for tri in triangles {
            let (v0, v1, v2) = (tri[0], tri[1], tri[2]);
            let m01 = self.get_mask(v0, v1);
            let m02 = self.get_mask(v0, v2);
            let m12 = self.get_mask(v1, v2);
            let cls = support3.get(&tri);

            let mut surv01 = 0u8;
            let mut surv02 = 0u8;
            let mut surv12 = 0u8;
            let mut any_surv = false;

            for b0 in 0..2usize {
                for b1 in 0..2usize {
                    if (m01 & (1 << (b0 * 2 + b1))) == 0 {
                        continue;
                    }
                    for b2 in 0..2usize {
                        if (m02 & (1 << (b0 * 2 + b2))) == 0
                            || (m12 & (1 << (b1 * 2 + b2))) == 0
                        {
                            continue;
                        }
                        let mut ok = true;
                        if let Some(c_list) = cls {
                            for c in c_list {
                                let mut c_sat = false;
                                for &l in c {
                                    let lv = lit_var(l);
                                    let b = if lv == v0 {
                                        b0 == 1
                                    } else if lv == v1 {
                                        b1 == 1
                                    } else {
                                        b2 == 1
                                    };
                                    if b ^ lit_neg(l) {
                                        c_sat = true;
                                        break;
                                    }
                                }
                                if !c_sat {
                                    ok = false;
                                    break;
                                }
                            }
                        }
                        if ok {
                            any_surv = true;
                            surv01 |= 1 << (b0 * 2 + b1);
                            surv02 |= 1 << (b0 * 2 + b2);
                            surv12 |= 1 << (b1 * 2 + b2);
                        }
                    }
                }
            }

            if !any_surv {
                if let Some(ref mut lg) = self.logger {
                    lg.derive_clause_over_cube_raw(&[], &tri);
                }
                return Err("UNSAT_WITT_TRIPLE");
            }
            if self.tighten_mask(v0, v1, surv01)? {
                changed = true;
            }
            if self.tighten_mask(v0, v2, surv02)? {
                changed = true;
            }
            if self.tighten_mask(v1, v2, surv12)? {
                changed = true;
            }
        }

        for ci in 0..self.clauses.len() {
            if self.clauses[ci].len() == 3 {
                let (a, b, c) = (self.clauses[ci][0], self.clauses[ci][1], self.clauses[ci][2]);
                let va = lit_var(a);
                let vb = lit_var(b);
                let vc = lit_var(c);
                let ba = if lit_neg(a) { 0 } else { 1 };
                let bb = if lit_neg(b) { 0 } else { 1 };
                let bc = if lit_neg(c) { 0 } else { 1 };
                for vd in 0..self.n {
                    if vd == va || vd == vb || vd == vc || self.fixed[vd].is_some() {
                        continue;
                    }
                    let ma = self.get_mask(va, vd);
                    let mb = self.get_mask(vb, vd);
                    let mc = self.get_mask(vc, vd);
                    for bd in 0..2usize {
                        let bit_a = 1 << (ba * 2 + bd);
                        let bit_b = 1 << (bb * 2 + bd);
                        let bit_c = 1 << (bc * 2 + bd);
                        if (ma & bit_a) == 0 && (mb & bit_b) == 0 && (mc & bit_c) == 0 {
                            if self.set_var(vd, bd == 0)? {
                                self.witt_cuts += 1;
                                changed = true;
                            }
                        }
                    }
                }
            }
        }

        Ok(changed)
    }

    fn solve(&mut self, max_rounds: usize) -> (bool, String, usize) {
        let mut rounds = 0usize;
        if let Err(e) = self.simplify_clauses() {
            return (true, e.to_string(), rounds);
        }
        for r in 1..=max_rounds {
            rounds = r;
            let mut progress = false;

            match self.phase_a_2sat_closure_and_fl1() {
                Err(e) => return (true, format!("{e}_R{r}"), rounds),
                Ok(c) => {
                    if c {
                        progress = true;
                        if let Err(e) = self.simplify_clauses() {
                            return (true, format!("{e}_R{r}"), rounds);
                        }
                    }
                }
            }

            match self.phase_c_witt_triple_project_and_lift() {
                Err(e) => return (true, format!("{e}_R{r}"), rounds),
                Ok(c) => {
                    if c {
                        progress = true;
                        if let Err(e) = self.simplify_clauses() {
                            return (true, format!("{e}_R{r}"), rounds);
                        }
                    }
                }
            }

            match self.phase_b_rm_rref() {
                Err(e) => return (true, format!("{e}_R{r}"), rounds),
                Ok(c) => {
                    if c {
                        progress = true;
                        if let Err(e) = self.simplify_clauses() {
                            return (true, format!("{e}_R{r}"), rounds);
                        }
                    }
                }
            }

            if !progress {
                break;
            }
        }
        (false, "UNKNOWN_FIXED_POINT".to_string(), rounds)
    }
}

fn parse_dimacs(input: &str) -> (usize, Vec<Vec<u32>>) {
    let mut n = 0usize;
    let mut clauses = Vec::new();
    let mut cur = Vec::new();
    for line in input.lines() {
        let s = line.trim();
        if s.is_empty() || s.starts_with('c') {
            continue;
        }
        if s.starts_with("p ") {
            let parts: Vec<&str> = s.split_whitespace().collect();
            if parts.len() >= 3 {
                n = parts[2].parse().unwrap_or(0);
            }
            continue;
        }
        for tok in s.split_whitespace() {
            if let Ok(v) = tok.parse::<i32>() {
                if v == 0 {
                    if !cur.is_empty() {
                        clauses.push(std::mem::take(&mut cur));
                    }
                } else {
                    let var = (v.abs() as usize) - 1;
                    if var + 1 > n {
                        n = var + 1;
                    }
                    cur.push(mk_lit(var, v < 0));
                }
            }
        }
    }
    if !cur.is_empty() {
        clauses.push(cur);
    }
    (n, clauses)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut cnf_arg: Option<String> = None;
    let mut emit_pbp_path: Option<String> = None;
    let mut use_rm4 = false;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--rm3" => {
                use_rm4 = false;
            }
            "--rm4" => {
                use_rm4 = true;
            }
            "--emit-pbp" => {
                i += 1;
                if i < args.len() {
                    emit_pbp_path = Some(args[i].clone());
                } else {
                    panic!("--emit-pbp requires a path argument");
                }
            }
            other => {
                cnf_arg = Some(other.to_string());
            }
        }
        i += 1;
    }

    let content = match cnf_arg.as_deref() {
        Some(path) if path != "-" => fs::read_to_string(path).expect("Failed to read CNF file"),
        _ => {
            let mut buf = String::new();
            io::stdin()
                .read_to_string(&mut buf)
                .expect("Failed to read stdin");
            buf
        }
    };

    let (n, clauses) = parse_dimacs(&content);
    let t0 = Instant::now();
    let mut solver = Solver::new(n, clauses, use_rm4, emit_pbp_path.is_some());
    let max_rounds = if use_rm4 { 18 } else { 12 };
    let (unsat, status, rounds) = solver.solve(max_rounds);
    let ms = t0.elapsed().as_secs_f64() * 1000.0;

    let mut pbp_lines = 0usize;
    if unsat {
        if let (Some(pbp_path), Some(ref mut lg)) = (emit_pbp_path, &mut solver.logger) {
            let pbp_text = lg.finish_unsat();
            pbp_lines = lg.lines.len();
            if let Some(parent) = std::path::Path::new(&pbp_path).parent() {
                if !parent.as_os_str().is_empty() {
                    let _ = fs::create_dir_all(parent);
                }
            }
            fs::write(&pbp_path, pbp_text).expect("Failed to write PBP proof file");
        }
    }

    println!(
        "{{\"unsat\":{},\"status\":\"{}\",\"mode\":\"{}\",\"rounds\":{},\"units_deduced\":{},\"xors_deduced\":{},\"rm3_polys\":{},\"rm4_polys\":{},\"witt_cuts\":{},\"pbp_lines\":{},\"ms\":{:.3}}}",
        unsat,
        status,
        if use_rm4 { "rm4" } else { "rm3" },
        rounds,
        solver.units_deduced,
        solver.xors_deduced,
        solver.rm3_polys,
        solver.rm4_polys,
        solver.witt_cuts,
        pbp_lines,
        ms
    );
}
