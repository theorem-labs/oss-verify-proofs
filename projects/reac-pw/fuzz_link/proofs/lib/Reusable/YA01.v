(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YA01.v, with its module paths changed. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0c YK0d YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Import AX2. Import AX2B. Import APC.
Open Scope Z_scope.
Definition TOPMAX : Z := 0x7fffff800000.
Definition STACK_LO : Z := -8388608.
Definition STACK_LEN : Z := 0x800000000000.
Definition STACK_END : Z := 140737488355328.
Definition stack_side : expr * expr := (eadd e_sp0 (ELit STACK_LO), esub (ELit (STACK_END - STACK_LO)) e_sp0).
Section G.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Definition BLO : Z := shadow_off A - 4096.
Definition BL1 : Z := shadow_off A + shadow_off A / 8.
Definition BL2 : Z := shadow_off A + shadow_off A / 8 + 2199023255552.
Definition BHI : Z := shadow_off A + 17592186044416.
Definition BMEM : Z := 140737488355328.
Definition band_laws : bool :=
let OFF := shadow_off A in
((4096 <=? OFF) && (BLO mod 8 =? 0) && (BLO / 8 + OFF <=? BL1) && (BHI / 8 + OFF =? BL2) && (BMEM / 8 + OFF <=? BHI)
&& (BLO <=? BL1) && (BL1 <=? BL2) && (BL2 <=? BHI) && (BHI <=? BMEM))%bool.
Definition lit_entry_b (b n : Z) (kd : mkind) (m : amap) : bool :=
(negb (is_fog m) && mkind_eqb (am_kind m) kd
&& match am_base m, am_len m with ELit b', ELit n' => Z.eqb b' b && Z.eqb n' n | _, _ => false end)%bool.
Definition find_lit_entry (ms : list amap) (b n : Z) (kd : mkind) : option amap := List.find (lit_entry_b b n kd) ms.
Definition find_band (ms : list amap) : option (amap * amap * amap) :=
if band_laws then
match find_lit_entry ms BLO (BL1 - BLO) KRWLAZY, find_lit_entry ms BL1 (BL2 - BL1) KNONELAZY, find_lit_entry ms BL2 (BHI - BL2) KRWLAZY with
| Some mL, Some mG, Some mH => Some (mL, mG, mH)
| _, _, _ => None
end
else None.
Definition shadow_facts_g (k : list kentry) (ms : list amap) (b n : expr) : list kentry :=
let '(sb, sk, sn) := shadow_of A k b n in
match find_containing k ms [KRWLAZY] sb sk sn with
| Some _ => [KWr (SA sb sk) sn; KZero (SA sb sk) sn]
| None =>
match find_band ms with
| Some (mL, mG, mH) =>
let '(bb, bk) := split_lit b in
match find_containing k ms [KRW; KRWLAZY; KNONE; KNONELAZY] bb bk n with
| Some m' => if (flat_x k sb sk sn && negb (amap_eqb m' mL) && negb (amap_eqb m' mG) && negb (amap_eqb m' mH))%bool
then [KWr (SA sb sk) sn; KZero (SA sb sk) sn] else []
| None => []
end
| None => []
end
end.
Definition shadow_facts_gB (bc : bctx) (ms : list amap) (b n : expr) : list kentry :=
let '(sb, sk, sn) := shadow_ofB A bc b n in
match find_containingB bc ms [KRWLAZY] sb sk sn with
| Some _ => [KWr (SA sb sk) sn; KZero (SA sb sk) sn]
| None =>
match find_band ms with
| Some (mL, mG, mH) =>
let '(bb, bk) := split_lit b in
match find_containingB bc ms [KRW; KRWLAZY; KNONE; KNONELAZY] bb bk n with
| Some m' => if (flat_xB bc sb sk sn && negb (amap_eqb m' mL) && negb (amap_eqb m' mG) && negb (amap_eqb m' mH))%bool
then [KWr (SA sb sk) sn; KZero (SA sb sk) sn] else []
| None => []
end
| None => []
end
end.
Lemma shadow_facts_gB_eqf : forall fk, shadow_facts_gB (mkbc fk) = shadow_facts_g fk.
Proof.
intros. apply functional_extensionality; intros ms. apply functional_extensionality; intros b. apply functional_extensionality; intros n.
unfold shadow_facts_gB, shadow_facts_g. rewrite shadow_ofB_eqf, !find_containingB_eqf, flat_xB_eqf. reflexivity.
Qed.
Definition vis_add_g_ref (cs : acs) (b n : expr) (k : list kentry) : option (acs) :=
let k0 := kn cs in
let '(bb, bk) := split_lit b in
let '(sb, sk, sn) := shadow_of A k0 b n in
match xhi k0 n with
| Some nhi =>
if (Z.leb 3 (ealign k0 b) && Z.leb 3 (ealign k0 n) && flat_x k0 bb bk n
&& expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n
&& forallb (fun p => let '(pb, pk) := split_lit (fst p) in
flat_x k0 pb pk (snd p)
&& ranges_apart_x k0 bb bk n pb pk (snd p) && ranges_apart_x k0 sb sk sn pb pk (snd p)) (a_vis cs)
&& forallb (fun p => let '(pb, pk) := split_lit (fst p) in
flat_x k0 pb pk (snd p) && ranges_apart_x k0 sb sk sn pb pk (snd p)) (a_ghost cs)
&& Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_facts_g k0 (a_maps cs) b n ++ k) (nxt cs))
(a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs))
else None
| None => None
end.
Definition vis_add_g (cs : acs) (b n : expr) (k : list kentry) : option (acs) :=
let k0 := kn cs in let bc := mkbc k0 in
let '(bb, bk) := split_lit b in
let '(sb, sk, sn) := shadow_ofB A bc b n in
match xhiB bc n with
| Some nhi =>
if (Z.leb 3 (ealignB bc b) && Z.leb 3 (ealignB bc n) && flat_xB bc bb bk n
&& expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n
&& forallb (fun p => let '(pb, pk) := split_lit (fst p) in
flat_xB bc pb pk (snd p)
&& ranges_apart_xB bc bb bk n pb pk (snd p) && ranges_apart_xB bc sb sk sn pb pk (snd p)) (a_vis cs)
&& forallb (fun p => let '(pb, pk) := split_lit (fst p) in
flat_xB bc pb pk (snd p) && ranges_apart_xB bc sb sk sn pb pk (snd p)) (a_ghost cs)
&& Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_facts_gB bc (a_maps cs) b n ++ k) (nxt cs))
(a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs))
else None
| None => None
end.
Lemma vis_add_g_eq : forall cs b n k, vis_add_g cs b n k = vis_add_g_ref cs b n k.
Proof. intros. unfold vis_add_g, vis_add_g_ref. unfold ehi, elo. rewrite ?ealignB_eqf, ?flat_xB_eqf, ?ranges_apart_xB_eqf, ?shadow_facts_gB_eqf, ?shadow_ofB_eqf, ?xhiB_eqf. reflexivity. Qed.
Definition safe_range_g (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
((expr_eqb b e_sp0 && Z.leb STACK_LO off)
|| match xhi k len, base_range k b with
| Some lh, Some (lo, hi) => Z.leb (img_lo A) (lo + off) && Z.leb (hi + off + lh) (img_hi A)
| _, _ => false
end
|| inside_maps k ms b off len)%bool.
Definition grant_keep_g (k : list kentry) (ms : list amap) (K : kentry) : bool :=
match K with
| KWord (SA b o) w _ => Nat.leb w 8 && safe_range_g k ms b o (ELit (Z.of_nat w))
| KZero (SA b o) l => safe_range_g k ms b o l
| KBlob (SA b o) l _ => safe_range_g k ms b o l
| KImg lo hi => true
| KAlign _ _ => true
| KRange _ _ _ => true
| KDisj _ _ _ _ => true
| KWr (SA b o) n => safe_range_g k ms b o n
| KFill (SA b o) l _ => safe_range_g k ms b o l
| KUnk (SA b o) l => safe_range_g k ms b o l
end.
Definition kn_grant_filter_g (k : list kentry) (ms : list amap) : list kentry :=
kimg_clip A (List.filter (grant_keep_g k ms) k).
Definition kdisj_all (ms : list amap) (nb ne : expr) : list kentry :=
flat_map (fun m => if is_fog m then [] else [KDisj (SA (am_base m) 0) (am_len m) (SA nb 0) ne]) ms.
Definition kdisj_img (nb ne : expr) : kentry :=
KDisj (SA (ELit (img_lo A)) 0) (ELit (img_hi A - img_lo A)) (SA nb 0) ne.
Definition kdisj_stack (nb ne : expr) : kentry :=
KDisj (SA e_sp0 STACK_LO) (ELit STACK_LEN) (SA nb 0) ne.
Definition null_kend_g (base ne : expr) (nlo : Z) : list kentry :=
match ne with
| ELit _ => []
| _ => [KRange (eadd base ne) (4096 + nlo) TOPMAX]
end.
Definition is_lit_b (e : expr) : bool := match e with ELit _ => true | _ => false end.
Definition kdisj_band (nb ne : expr) : kentry :=
KDisj (SA (ELit BLO) 0) (ELit (BHI - BLO)) (SA nb 0) ne.
Definition stack_shadow_kdisj (k : list kentry) (sb : expr) (sk : Z) (sn : expr) : list kentry :=
let '(tb, tk, tn) := shadow_of A k (fst stack_side) (snd stack_side) in
if (flat_x k tb tk tn && flat_x k sb sk sn)%bool then [KDisj (SA tb tk) tn (SA sb sk) sn] else [].
Definition stack_shadow_app_kdisj (k : list kentry) (nb ne : expr) : list kentry :=
let '(tb, tk, tn) := shadow_of A k (fst stack_side) (snd stack_side) in
if flat_x k tb tk tn then [KDisj (SA tb tk) tn (SA nb 0) ne] else [].
Definition img_shadow_kdisj (k : list kentry) (sb : expr) (sk : Z) (sn : expr) : list kentry :=
let '(ib, ik, iN) := shadow_of A k (ELit (img_lo A)) (ELit (img_hi A - img_lo A)) in
if (flat_x k ib ik iN && flat_x k sb sk sn)%bool then [KDisj (SA ib ik) iN (SA sb sk) sn] else [].
Definition shadow_kdisj (k : list kentry) (ms : list amap) (nb ne : expr) : list kentry :=
match find_band ms with
| None => []
| Some _ =>
let '(sb, sk, sn) := shadow_of A k nb ne in
kdisj_band nb ne
:: stack_shadow_kdisj k sb sk sn
++ stack_shadow_app_kdisj k nb ne
++ img_shadow_kdisj k sb sk sn
++ flat_map (fun m =>
if (is_fog m || is_lit_b (am_base m))%bool then []
else let '(mb, mk, mn) := shadow_of A k (am_base m) (am_len m) in
if (flat_x k sb sk sn && flat_x k mb mk mn)%bool
then [KDisj (SA mb mk) mn (SA sb sk) sn]
else []) ms
end.
Definition band_present (ms : list amap) : bool := match find_band ms with Some _ => true | None => false end.
Definition null_vlo (ms : list amap) (nlo : Z) : Z :=
if (img_lo A - 4096 <? nlo) then (if (band_present ms && (BLO - img_hi A <? nlo))%bool then BHI / 4096 else img_hi A / 4096) else 1.
Definition null_kfacts_g0 (cs : acs) (base ne : expr) (nlo : Z) : list kentry :=
KRange (EVar (nxt cs)) (null_vlo (a_maps cs) nlo) ((TOPMAX - nlo) / 4096)
:: null_kend_g base ne nlo ++ kdisj_stack base ne :: kdisj_img base ne :: kdisj_all (a_maps cs) base ne.
Definition null_kctx_g (cs : acs) (base ne : expr) (nlo : Z) : list kentry :=
null_kfacts_g0 cs base ne nlo ++ kn cs.
Definition null_kfacts_g (cs : acs) (base ne : expr) (nlo : Z) : list kentry :=
shadow_kdisj (null_kctx_g cs base ne nlo) (a_maps cs) base ne ++ null_kfacts_g0 cs base ne nlo.
Definition null_kctx2_g (cs : acs) (base ne : expr) (nlo : Z) : list kentry :=
null_kfacts_g cs base ne nlo ++ kn cs.
Definition lend_inside_maps (k : list kentry) (ms : list amap) (b : expr) (o : Z) (l : expr) : bool :=
match mkAlu Instr.ALU_ADD (eaddz b o) l, base_range k b with
| ELit zend, Some (blo, _) =>
((0 <? zend) && (zend <? two64)
&& existsb (fun m => negb (is_fog m)
&& match am_base m, am_len m with
| ELit mb, ELit ml => (0 <=? mb) && (0 <=? ml) && (mb + ml <? two64) && (mb <=? blo + o) && (zend <=? mb + ml)
| _, _ => false
end) ms)%bool
| _, _ => false
end.
Definition keep_lend (k : list kentry) (ms : list amap) (K : kentry) : bool :=
match K with
| KZero (SA b o) l | KWr (SA b o) l | KUnk (SA b o) l | KBlob (SA b o) l _ | KFill (SA b o) l _ => lend_inside_maps k ms b o l
| _ => false
end.
Definition kn_grant_filter_g2 (kctx k : list kentry) (ms : list amap) (nb ne : expr) : list kentry :=
let sp := mk_sprep kctx nb 0 ne in
kimg_clip A (List.filter (fun K => grant_keep_g k ms K || kentry_apart_bp kctx sp nb 0 ne K || keep_lend k ms K) k).
Definition mmap_null_g (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
match mmap_len cs with
| Some (ne, nlo, nhi) =>
if (fresh_ok nx0 cs && expr_vars_lt (nxt cs) ne
&& gap_ok A cs nhi && (negb eager || budget_ok LIMIT cs nhi)
&& no_holes (a_maps cs))%bool then
let v := nxt cs in
let base := escale 4096 (EVar v) in
let kmem := [KWr (SA base 0) ne; KZero (SA base 0) ne] in
let k' := null_kfacts_g cs base ne nlo
++ kn_grant_filter_g2 (null_kctx2_g cs base ne nlo) (kn cs) (a_maps cs) base ne in
let cs1 := add_entry cs (sr_upd (s_regs (a_ss cs)) 10 base) k' (S v) (AM base ne kind) nhi eager (a_ylo cs) in
if visible then vis_add_g cs1 base ne (kmem ++ kn cs1) else Some cs1
else None
| None => None
end.
Definition shadow_facts_lend (k : list kentry) (m : amap) (b n : expr) : list kentry :=
match shadow_facts A k [m] b n with
| (_ :: _) as r => r
| [] =>
let '(sb, sk, sn) := shadow_of A k b n in
match am_base m, am_len m, mkAlu Instr.ALU_ADD (eaddz sb sk) sn, base_range k sb with
| ELit mb, ELit ml, ELit zend, Some (slo, shi) =>
if (negb (is_fog m) && mkind_eqb (am_kind m) KRWLAZY && flat_x k sb sk sn
&& (0 <=? mb) && (0 <=? ml) && (mb <=? slo + sk) && (0 <? zend) && (zend <=? mb + ml) && (mb + ml <? two64))%bool
then
let L := zend - (shi + sk) in
[KWr (SA sb sk) sn; KZero (SA sb sk) sn]
++ (if 0 <? L then [KWr (SA sb sk) (ELit L); KZero (SA sb sk) (ELit L)] else [])
else []
| _, _, _, _ => []
end
end.
Definition kn_grant_filter_f2 (k : list kentry) (ms : list amap) (b : expr) (off : Z) (ne : expr) : list kentry :=
let sp := mk_sprep k b off ne in
kimg_clip A (List.filter (fun K => grant_keep_b A k ms K || kentry_apart_bp k sp b off ne K || keep_lend k ms K) k).
Definition mmap_fixed_grant_g (cs : acs) (ms0 : list amap) (b : expr) (off : Z) (ne : expr) (nhi : Z)
(kind : mkind) (eager visible : bool) : option acs :=
let k := kn cs in
let a := reg cs 10 in
let m := AM a ne kind in
let kmem := [KWr (SA b off) ne; KZero (SA b off) ne] in
let ksh := if mkind_eqb kind KRWLAZY then flat_map (fun p => shadow_facts_lend k m (fst p) (snd p)) (a_vis cs) else [] in
let k' := ksh ++ kn_grant_filter_f2 k ms0 b off ne in
let cs1 := add_entry (with_maps0 cs ms0) (s_regs (a_ss cs)) k' (nxt cs) m nhi eager (a_ylo cs) in
if visible then vis_add A LIMIT cs1 a ne (kmem ++ kn cs1) else Some cs1.
Definition mmap_fixed_free_g (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
let k := kn cs in
let a := reg cs 10 in
match fixed_args A cs KHI with
| Some (b, off, ne, nlo, nhi) =>
if (no_fog (a_maps cs)
&& forallb (fun m => ranges_apart_x k b off ne (am_base m) 0 (am_len m)) (a_maps cs)
&& (negb eager || budget_ok LIMIT cs nhi)
&& expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) a)%bool
then mmap_fixed_grant_g cs (a_maps cs) b off ne nhi kind eager visible
else None
| None =>
match fixed_args A cs CEIL with
| Some (b, off, ne, nlo, nhi) =>
match find_hole k (a_maps cs) a ne with
| Some h =>
let ms0 := unhole (a_maps cs) h in
if (forallb (fun m => negb (is_hole m) || ranges_apart_x k b off ne (am_base m) 0 (am_len m)) ms0
&& (negb eager || budget_ok LIMIT cs nhi)
&& expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) a)%bool
then mmap_fixed_grant_g cs ms0 b off ne nhi kind eager visible
else None
| None => None
end
| None => None
end
end.
Definition node_mmap2g (cs : acs) : option (acs * acs) :=
match mmap_gate cs with
| Some (prot, flags, isnull) =>
let g := if isnull then
match prot, flags with
| 3, 0x22 => mmap_null_g cs KRW true true
| 3, 0x4022 => mmap_null_g cs KRWLAZY false true
| 0, 0x22 => mmap_null_g cs KNONE false false
| 0, 0x4022 => mmap_null_g cs KNONELAZY false false
| _, _ => None
end
else
match prot, flags with
| 3, 0x4032 | 3, 0x104022 | 3, 0x104032 => mmap_fixed_free_g cs KRWLAZY false false
| 3, 0x32 | 3, 0x100022 | 3, 0x100032 => mmap_fixed_free_g cs KRW true true
| 0, 0x4032 | 0, 0x104022 | 0, 0x104032 => mmap_fixed_free_g cs KNONELAZY false false
| 0, 0x32 | 0, 0x100022 | 0, 0x100032 => mmap_fixed_free_g cs KNONE false false
| _, _ => None
end in
match g with Some csG => Some (refuse cs, csG) | None => None end
| None => None
end.
Definition brk_grow_possible_g (cs : acs) (d : Z) : bool :=
(brk_base_ok A cs d && no_fog (a_maps cs) && budget_ok LIMIT cs d)%bool.
Definition brk_kfacts_g0 (cs : acs) (b : expr) (d : Z) : list kentry :=
kdisj_stack b (ELit d) :: kdisj_img b (ELit d) :: kdisj_all (a_maps cs) b (ELit d).
Definition brk_kctx_g (cs : acs) (b : expr) (d : Z) : list kentry := brk_kfacts_g0 cs b d ++ kn cs.
Definition brk_kfacts_g (cs : acs) (b : expr) (d : Z) : list kentry :=
shadow_kdisj (brk_kctx_g cs b d) (a_maps cs) b (ELit d) ++ brk_kfacts_g0 cs b d.
Definition brk_kctx2_g (cs : acs) (b : expr) (d : Z) : list kentry := brk_kfacts_g cs b d ++ kn cs.
Definition node_brk2g (cs : acs) : option (acs * acs) :=
match reg_lit cs 17, brk_req cs with
| Some 214, Some d =>
if (brk_grow_possible_g cs d && expr_vars_lt (nxt cs) (reg cs 10))%bool then
let k := kn cs in let b := a_brk cs in let '(bb, bk) := split_lit b in
let csA := set_pc (set_reg cs 10 b) (pc cs + 4) in
let k' := brk_kfacts_g cs b d ++ kn_grant_filter_g2 (brk_kctx2_g cs b d) k (a_maps cs) b (ELit d) in
let ss := a_ss cs in
let csB := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
(AM b (ELit d) KRW :: a_maps cs) (a_totsz cs + d) (a_ylo cs) (a_eager cs + d)
(a_vis cs) (a_ghost cs) (a_abytes cs) (reg cs 10) (a_fd cs) (a_tidset cs) in
match vis_add_g csB b (ELit d) (KWr (SA bb bk) (ELit d) :: KZero (SA bb bk) (ELit d) :: kn csB) with
| Some csB' => Some (csA, csB')
| None => None
end
else None
| _, _ => None
end.
Definition var_scale (e : expr) : option (Z * nat) :=
match e with
| EMd Instr.M_MUL (ELit c) (EVar v) => if ((0 <? c) && (c <? two64))%bool then Some (c, v) else None
| EVar v => Some (1, v)
| _ => None
end.
Definition zceil_div (a c : Z) : Z := - ((- a) / c).
Definition side_below_vfacts (k : list kentry) (cX : expr) (oX : Z) (nX : expr) (cY : expr) (oY : Z) : list kentry :=
(match var_scale cY, base_range k cX, xlo k nX with
| Some (c, v), Some (xl, _), Some nl =>
match xlo k (EVar v), xhi k (EVar v) with
| Some vlo, Some vhi => if ((0 <=? vlo) && (c * vhi <? two64))%bool
then [KRange (EVar v) (Z.max vlo (zceil_div (xl + oX + nl - oY) c)) vhi] else []
| _, _ => []
end
| _, _, _ => []
end)
++
(match var_scale cX, base_range k cY, xlo k nX with
| Some (c, v), Some (_, yh), Some nl =>
match xlo k (EVar v), xhi k (EVar v) with
| Some vlo, Some vhi => if ((0 <=? vlo) && (c * vhi <? two64))%bool
then [KRange (EVar v) vlo (Z.min vhi ((yh + oY - oX - nl) / c))] else []
| _, _ => []
end
| _, _, _ => []
end).
Definition node_casedisj_g (cs : acs) (b1 b2 : expr) : option (acs * acs) :=
let k := kn cs in
match find_disj k b1 b2, node_casedisj cs b1 b2 with
| Some (c1, o1, n1, c2, o2, n2), Some (csa, csb) =>
Some (add_kn csa (side_below_vfacts k c1 o1 n1 c2 o2), add_kn csb (side_below_vfacts k c2 o2 n2 c1 o1))
| _, _ => None
end.
Fixpoint hole_all (s : shape) (h : nat) : bool :=
match s with
| SHole h' => Nat.eqb h' h
| SAlt2 a b => hole_all a h || hole_all b h
| SCase _ _ a b => hole_all a h && hole_all b h
| _ => false
end.
Fixpoint holes_any (s : shape) : list nat :=
match s with
| SHole h => [h]
| SAlt2 a b | SCase _ _ a b => holes_any a ++ holes_any b
| _ => []
end.
Fixpoint event_free (s : shape) : bool :=
match s with
| SNil | SHole _ => true
| SAlt2 a b | SCase _ _ a b => event_free a && event_free b
| SExit _ | SEmitP _ _ _ | SNext => false
end.
Definition brk2_holes_ok (hole_le : nat -> nat -> bool) (sa sb : shape) : bool :=
(event_free sa && event_free sb
&& forallb (fun h' => existsb (fun h => hole_le h' h && hole_all sa h) (holes_any sa ++ holes_any sb)) (holes_any sb))%bool.
Definition fixed_args_g (cs : acs) (top : Z) : option (expr * Z * expr * Z * Z) :=
let k := kn cs in let a := reg cs 10 in
let '(b, off) := split_lit a in
match mmap_len cs, xlo k a, xhi k a with
| Some (ne, nlo, nhi), Some alo, Some ahi =>
if (page_aligned k a && Z.ltb 0 alo && Z.leb (ahi + nhi) top && flat_x k b off ne)%bool then Some (b, off, ne, nlo, nhi) else None
| _, _, _ => None
end.
Definition fixed_in_args_g_ref (cs : acs) (arm : fixed_in_arm) : option (expr * Z * expr * Z * Z * amap) :=
match fixed_args_g cs TOPMAX with
| Some (b, off, ne, nlo, nhi) =>
let k := kn cs in
let kinds := match arm with ArmE => [KRW; KNONE; KNONELAZY] | ArmF => [KRWLAZY] | ArmG => [KRW; KNONE; KNONELAZY] end in
match find_containing k (a_maps cs) kinds b off ne with
| Some m =>
if (expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then Some (b, off, ne, nlo, nhi, m) else None
| None => None
end
| None => None
end.
Definition fixed_in_args_g (cs : acs) (arm : fixed_in_arm) : option (expr * Z * expr * Z * Z * amap) :=
match fixed_args_g cs TOPMAX with
| Some (b, off, ne, nlo, nhi) =>
let k := kn cs in let bc := mkbc k in
let kinds := match arm with ArmE => [KRW; KNONE; KNONELAZY] | ArmF => [KRWLAZY] | ArmG => [KRW; KNONE; KNONELAZY] end in
match find_containingB bc (a_maps cs) kinds b off ne with
| Some m =>
if (expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then Some (b, off, ne, nlo, nhi, m) else None
| None => None
end
| None => None
end.
Lemma fixed_in_args_g_eq : forall cs arm, fixed_in_args_g cs arm = fixed_in_args_g_ref cs arm.
Proof. intros. unfold fixed_in_args_g, fixed_in_args_g_ref. unfold ehi, elo. rewrite ?find_containingB_eqf. reflexivity. Qed.
Definition mmap_fixed_in_g_ref (cs : acs) (arm : fixed_in_arm) : option acs :=
match fixed_in_args_g cs arm with
| Some (b, off, ne, nlo, nhi, m) =>
let k := kn cs in
if match arm with ArmE => budget_ok LIMIT cs nhi | _ => true end then
let k' := match arm with
| ArmE => kimg_clip A (kn_unfill k b off ne)
| ArmF => kimg_clip A (kn_rezero k b off ne)
| ArmG => kimg_clip A (kn_cutout k b off ne)
end in
let ms' := match arm with ArmF => a_maps cs | _ => rekind (a_maps cs) m end in
let ss := a_ss cs in
let cs1 := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
ms' (a_totsz cs) (a_ylo cs)
(match arm with ArmE => a_eager cs + nhi | _ => a_eager cs end)
(a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
match arm with ArmE => vis_add_g cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1) | _ => Some cs1 end
else None
| None => None
end.
Definition mmap_fixed_in_g (cs : acs) (arm : fixed_in_arm) : option acs :=
match fixed_in_args_g cs arm with
| Some (b, off, ne, nlo, nhi, m) =>
let k := kn cs in let bc := mkbc k in
if match arm with ArmE => budget_ok LIMIT cs nhi | _ => true end then
let k' := match arm with
| ArmE => kimg_clip A (kn_unfillB bc b off ne)
| ArmF => kimg_clip A (kn_rezeroB bc b off ne)
| ArmG => kimg_clip A (kn_cutoutB bc b off ne)
end in
let ms' := match arm with ArmF => a_maps cs | _ => rekind (a_maps cs) m end in
let ss := a_ss cs in
let cs1 := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
ms' (a_totsz cs) (a_ylo cs)
(match arm with ArmE => a_eager cs + nhi | _ => a_eager cs end)
(a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
match arm with ArmE => vis_add_g cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1) | _ => Some cs1 end
else None
| None => None
end.
Lemma mmap_fixed_in_g_eq : forall cs arm, mmap_fixed_in_g cs arm = mmap_fixed_in_g_ref cs arm.
Proof. intros. unfold mmap_fixed_in_g, mmap_fixed_in_g_ref. unfold ehi, elo. rewrite ?kn_cutoutB_eqf, ?kn_rezeroB_eqf, ?kn_unfillB_eqf. reflexivity. Qed.
Definition node_mmapin_g (hole : bool) (cs : acs) : option (acs * acs * list acs) :=
match mmap_gate cs with
| Some (prot, flags, false) =>
let arm := match prot, flags with
| 3, 0x32 => Some ArmE
| 3, 0x4032 => Some ArmF
| 0, 0x32 => Some ArmG
| _, _ => None
end in
match arm with
| Some arm =>
match fixed_in_args_g cs arm, mmap_fixed_in_g cs arm with
| Some (b, off, ne, nlo, nhi, m), Some csO => Some (refuse cs, csO, mmap_destroyed A hole cs b off ne m)
| _, _ => None
end
| None => None
end
| _ => None
end.
Definition node_mmapin2_g (cs : acs) : option (acs * acs) :=
let _ := A in let _ := LIMIT in None.
Definition node_mprotect_g_ref (cs : acs) : option acs :=
match reg_lit cs 17, reg_lit cs 12, fixed_args_g cs TOPMAX with
| Some 226, Some 3, Some (b, off, ne, nlo, nhi) =>
let k := kn cs in
match find_containing k (a_maps cs) [KNONE; KNONELAZY] b off ne with
| Some m =>
if (budget_ok LIMIT cs nhi && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then
let k' := kimg_clip A (kn_unfill k b off ne) in
let ss := a_ss cs in
let cs1 := ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k' (s_next ss))
(rekind (a_maps cs) m) (a_totsz cs) (a_ylo cs) (a_eager cs + nhi)
(a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
vis_add_g cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1)
else None
| None => None
end
| _, _, _ => None
end.
Definition node_mprotect_g (cs : acs) : option acs :=
match reg_lit cs 17, reg_lit cs 12, fixed_args_g cs TOPMAX with
| Some 226, Some 3, Some (b, off, ne, nlo, nhi) =>
let k := kn cs in let bc := mkbc k in
match find_containingB bc (a_maps cs) [KNONE; KNONELAZY] b off ne with
| Some m =>
if (budget_ok LIMIT cs nhi && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then
let k' := kimg_clip A (kn_unfillB bc b off ne) in
let ss := a_ss cs in
let cs1 := ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k' (s_next ss))
(rekind (a_maps cs) m) (a_totsz cs) (a_ylo cs) (a_eager cs + nhi)
(a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) in
vis_add_g cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1)
else None
| None => None
end
| _, _, _ => None
end.
Lemma node_mprotect_g_eq : forall cs, node_mprotect_g cs = node_mprotect_g_ref cs.
Proof. intros. unfold node_mprotect_g, node_mprotect_g_ref. unfold ehi, elo. rewrite ?find_containingB_eqf, ?kn_unfillB_eqf. reflexivity. Qed.
Definition node_mprotect2g (cs : acs) : option (acs * acs) :=
match node_mprotect_g cs with Some csG => Some (refuse cs, csG) | None => None end.
Definition node_unvis_g_ref (cs : acs) (b n : expr) : option acs :=
let k := kn cs in
let '(bb, bk) := split_lit b in
let '(sb, sk, sn) := shadow_of A k b n in
match xhi k b, xhi k n with
| Some bh, Some nh =>
if (existsb (vis_here b n) (a_vis cs)
&& Z.leb 3 (ealign k b) && Z.leb 3 (ealign k n) && flat_x k bb bk n && Z.leb (bh + nh) TOPMAX
&& flat_x k sb sk sn && kzero_x k k sb sk sn)%bool
then
let k1 := kn_unfill k bb bk n in
let k2 := kn_unfill k1 sb sk sn in
let ss := a_ss cs in
Some (ACS (mk_ss (s_pc ss) (s_regs ss) k2 (s_next ss))
(a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
(List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) (a_ghost cs ++ [(b, n)])
(a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
else None
| _, _ => None
end.
Definition node_unvis_g (cs : acs) (b n : expr) : option acs :=
let k := kn cs in let bc := mkbc k in
let '(bb, bk) := split_lit b in
let '(sb, sk, sn) := shadow_ofB A bc b n in
match xhiB bc b, xhiB bc n with
| Some bh, Some nh =>
if (existsb (vis_here b n) (a_vis cs)
&& Z.leb 3 (ealignB bc b) && Z.leb 3 (ealignB bc n) && flat_xB bc bb bk n && Z.leb (bh + nh) TOPMAX
&& flat_xB bc sb sk sn && kzero_xB bc k sb sk sn)%bool
then
let k1 := kn_unfillB bc bb bk n in
let k2 := kn_unfillM k1 sb sk sn in
let ss := a_ss cs in
Some (ACS (mk_ss (s_pc ss) (s_regs ss) k2 (s_next ss))
(a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
(List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) (a_ghost cs ++ [(b, n)])
(a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
else None
| _, _ => None
end.
Lemma node_unvis_g_eq : forall cs b n, node_unvis_g cs b n = node_unvis_g_ref cs b n.
Proof. intros. unfold node_unvis_g, node_unvis_g_ref. unfold ehi, elo. rewrite ?ealignB_eqf, ?flat_xB_eqf, ?kn_unfillB_eqf, ?kzero_xB_eqf, ?shadow_ofB_eqf, ?xhiB_eqf, ?kn_unfillM_eq. reflexivity. Qed.
Definition havoc_covered (k : list kentry) (b : expr) (o n : Z) : bool :=
(Z.ltb 0 n && Z.leb n 8 && flat_x k b o (ELit n) && cover_x (S (length k)) k b o (o + n))%bool.
Fixpoint img_cell_readable (segs : list Segment) (a : Z) (n : nat) : bool :=
match n with
| O => true
| S n' => match seg_rom segs (Z_to_bv 64 a) with
| Some _ => img_cell_readable segs (a + 1) n'
| None => false
end
end.
Definition havoc_readable (segs : list Segment) (k : list kentry) (b : expr) (o n : Z) : bool :=
havoc_covered k b o n
|| (Z.ltb 0 n && Z.leb n 8 && flat_x k b o (ELit n)
&& match b with ELit 0 => img_cell_readable segs o (Z.to_nat n) | _ => false end)%bool.
Definition xn_havoccell (segs : list Segment) (args : list expr) (cs : acs) : option acs :=
match args with
| [b; ELit n] =>
let k := kn cs in
let '(bb, bo) := split_lit b in
if (fresh_ok nx0 cs && expr_vars_lt (nxt cs) b && havoc_readable segs k bb bo n)%bool then
let ss := a_ss cs in
Some (with_ss cs (mk_ss (s_pc ss) (s_regs ss)
(KWord (SA bb bo) (Z.to_nat n) (EVar (nxt cs)) :: kn_cutout k bb bo (ELit n))
(S (nxt cs))))
else None
| _ => None
end.
Definition split_here (k : list kentry) (a : expr) (p : expr * expr) : bool :=
(lin_ge0 k [(a, -1)] [(fst p, 0)] && lin_ge0 k [(fst p, -1); (snd p, 0)] [(a, 0)])%bool.
Definition split_pair (a : expr) (p : expr * expr) : list (expr * expr) :=
[(fst p, esub a (fst p)); (a, esub (eadd (fst p) (snd p)) a)].
Definition node_splitvis_g (cs : acs) (a : expr) : option acs :=
let k := kn cs in
match List.filter (split_here k a) (a_vis cs) with
| [p] =>
let '(pb, pk) := split_lit (fst p) in
if (Z.leb 12 (ealign k a) && flat_x k pb pk (snd p) && expr_vars_lt (nxt cs) a
&& match xhi k (fst p), xhi k (snd p) with Some h1, Some h2 => Z.ltb (h1 + h2) two64 | _, _ => false end
&& Z.leb (a_eager cs + a_abytes cs + 8192) LIMIT)%bool
then Some (ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
(flat_map (fun q => if split_here k a q then split_pair a q else [q]) (a_vis cs))
(a_ghost cs) (a_abytes cs + 8192) (a_brk cs) (a_fd cs) (a_tidset cs))
else None
| _ => None
end.
Definition xn_splitvis (args : list expr) (cs : acs) : option acs :=
match args with [a] => node_splitvis_g cs a | _ => None end.
Definition P0b : expr := escale 4096 (EVar V_S1).
Definition P0k : Z := shadow_off A + STACK_LO / 8.
Definition pair_eqb (p q : expr * expr) : bool := (expr_eqb (fst p) (fst q) && expr_eqb (snd p) (snd q))%bool.
Definition inside_nonband (k : list kentry) (ms : list amap) (mL mG mH : amap) (pb : expr) (pk : Z) (pn : expr) : bool :=
existsb (fun m => negb (is_fog m) && negb (amap_eqb m mL) && negb (amap_eqb m mG) && negb (amap_eqb m mH)
&& xinside k pb pk pn (am_base m) 0 (am_len m))%bool ms.
Definition sh_below (k : list kentry) (p : expr * expr) (db : expr) (dk : Z) : bool :=
match xhi k (fst p), xhi k (snd p), base_range k db with
| Some ph, Some lh, Some (dlo, _) => ((0 <=? ph) && (0 <=? lh) && (shadow_off A + (ph + lh) / 8 <=? dlo + dk))%bool
| _, _, _ => false
end.
Definition spad_parse (ms : list amap) : option (Z * Z * amap * amap * amap) :=
match find_band ms with
| Some (mL, mG, mH) => match am_base mH, am_len mH with ELit hb, ELit hl => Some (hb, hl, mL, mG, mH) | _, _ => None end
| None => None
end.
Definition spad_cond (cs : acs) (db : expr) (dk : Z) (ne cb : expr) (ck : Z) (mL mG mH : amap) (hb hl plo phi nhi nlo : Z) : bool :=
let k := kn cs in
(negb (is_fog mH) && mkind_eqb (am_kind mH) KRWLAZY
&& (0 <=? hb) && (hb + hl <? two64) && (hb <=? plo + P0k) && (phi + P0k + 4096 <=? hb + hl) && (0 <=? plo + P0k)
&& Z.eqb (shadow_off A mod 4096) 0
&& (0 <? nlo) && (nhi <=? 4096)
&& flat_x k db dk ne
&& Z.leb 12 (ealign k (escale 8 (eaddz db (dk - shadow_off A))))
&& lin_ge0 k [(escale 8 (eaddz db (dk - shadow_off A)), 4095)] [(e_sp0, STACK_LO)]
&& existsb (pair_eqb stack_side) (a_vis cs)
&& flat_x k cb ck (ELit 4096) && kwritable_x k k cb ck (ELit 4096)
&& forallb (fun p => pair_eqb stack_side p
|| (let '(pb, pk) := split_lit (fst p) in
flat_x k pb pk (snd p) && ranges_apart_x k pb pk (snd p) db dk ne
&& (inside_nonband k (a_maps cs) mL mG mH pb pk (snd p) || sh_below k p db dk)))%bool
(a_vis cs)
&& forallb (fun q => let '(qb, qk) := split_lit (fst q) in
flat_x k qb qk (snd q) && ranges_apart_x k qb qk (snd q) db dk ne)%bool (a_ghost cs))%bool.
Definition spad_keep (k : list kentry) (cb : expr) (ck : Z) (cn : expr) : list kentry :=
let core := KZero (SA cb ck) cn in
if existsb (kentry_eqb core) k then [core] else [].
Definition spad_fill0 (cs : acs) (entry cmax : Z) : option acs :=
let k := kn cs in
if negb (Z.eqb (pc cs) entry) then None else
match ret_lit cs, reg_lit cs 11, spad_parse (a_maps cs) with
| Some ret, Some c, Some (hb, hl, mL, mG, mH) =>
let dst := reg cs 10 in let ne := reg cs 12 in
let '(db, dk) := split_lit dst in
if negb (Z.eqb (c mod 256) 0 && Z.ltb c cmax && Z.leb 0 c && xinside k db dk ne P0b P0k (ELit 4096))%bool then None else
let '(cb, ck, cn) := shadow_of A k (fst stack_side) (snd stack_side) in
match base_range k P0b, xhi k ne, xlo k ne with
| Some (plo, phi), Some nhi, Some nlo =>
if spad_cond cs db dk ne cb ck mL mG mH hb hl plo phi nhi nlo
then after_call nx0 cs ret (Some dst) (spad_keep k cb ck cn ++ kn_havoc k db dk ne)
else None
| _, _, _ => None
end
| _, _, _ => None
end.
Definition spad_condz (cs : acs) (db : expr) (dk : Z) (ne cb : expr) (ck : Z) (cn : expr) (mL mG mH : amap) (hb hl plo phi nhi nlo : Z) : bool :=
let k := kn cs in
(negb (is_fog mH) && mkind_eqb (am_kind mH) KRWLAZY
&& (0 <=? hb) && (hb + hl <? two64) && (hb <=? plo + P0k) && (shadow_off A + 17592186044416 <=? hb + hl) && (0 <=? plo + P0k)
&& Z.eqb (shadow_off A mod 4096) 0
&& (0 <? nlo) && (nhi <=? 2 ^ 40)
&& flat_x k db dk ne
&& Z.leb 12 (ealign k (escale 8 (eaddz db (dk - shadow_off A))))
&& lin_ge0 k [(escale 8 (eaddz db (dk - shadow_off A)), 4095)] [(e_sp0, STACK_LO)]
&& lin_ge0 k [(db, dk)] [(P0b, P0k)]
&& lin_ge0 k [(cb, ck); (cn, 0)] [(db, dk); (ne, 0)]
&& existsb (pair_eqb stack_side) (a_vis cs)
&& flat_x k cb ck cn && kwritable_x k k cb ck cn
&& existsb (kentry_eqb (KZero (SA cb ck) cn)) k
&& forallb (fun p => pair_eqb stack_side p
|| (let '(pb, pk) := split_lit (fst p) in
flat_x k pb pk (snd p) && ranges_apart_x k pb pk (snd p) db dk ne
&& (inside_nonband k (a_maps cs) mL mG mH pb pk (snd p) || sh_below k p db dk)))%bool
(a_vis cs)
&& forallb (fun q => let '(qb, qk) := split_lit (fst q) in
flat_x k qb qk (snd q) && ranges_apart_x k qb qk (snd q) db dk ne)%bool (a_ghost cs))%bool.
Definition spad_fillz (cs : acs) (entry cmax : Z) : option acs :=
let k := kn cs in
if negb (Z.eqb (pc cs) entry) then None else
match ret_lit cs, reg_lit cs 11, spad_parse (a_maps cs) with
| Some ret, Some c, Some (hb, hl, mL, mG, mH) =>
let dst := reg cs 10 in let ne := reg cs 12 in
let '(db, dk) := split_lit dst in
if negb (Z.eqb (c mod 256) 0 && Z.ltb c cmax && Z.leb 0 c)%bool then None else
let '(cb, ck, cn) := shadow_of A k (fst stack_side) (snd stack_side) in
match base_range k P0b, xhi k ne, xlo k ne with
| Some (plo, phi), Some nhi, Some nlo =>
if spad_condz cs db dk ne cb ck cn mL mG mH hb hl plo phi nhi nlo
then after_call nx0 cs ret (Some dst) k
else None
| _, _, _ => None
end
| _, _, _ => None
end.
End G.
Definition V_HW : nat := 9.
Definition NX0G : nat := 10.
Definition init_kn_g (A : atable) : list kentry :=
KRange e_atr8 0xFFFF0000001 0xFFFFFFFFFE7
:: init_kn A ++ KRange (EVar V_HW) 0x112D 0x20112D :: auxw 3 16 (EVar V_HW).
Definition STACK_VIS : Z := 0x80800000.
Definition init_vis_g (A : atable) : list (expr * expr) :=
[(ELit (img_lo A), ELit (img_hi A - img_lo A)); stack_side].
Definition init_acs_of_g (A : atable) : acs :=
ACS (mk_ss (a_entry A) init_regs (init_kn_g A) NX0G) [] (img_hi A - img_lo A) MBASE_MIN 0 (init_vis_g A) []
(vis_cost (img_hi A - img_lo A) + vis_cost STACK_VIS) (escale 4096 (EVar V_BRK)) FdStd false.
Fixpoint cover_sweep (l : list (word * word)) (z hi : Z) (fuel : nat) : bool :=
match fuel with
| O => false
| S f => if (hi <=? z)%Z then true else
match List.find (fun iv => ((bv_unsigned (fst iv) <=? z) && (z <? bv_unsigned (fst iv) + bv_unsigned (snd iv)))%Z%bool) l with
| Some iv => cover_sweep l (bv_unsigned (fst iv) + bv_unsigned (snd iv)) hi f
| None => false
end
end.
Definition res_cover_check (segs : list Segment) (A : atable) : bool :=
((img_lo A <? img_hi A)%Z && cover_sweep (segments_reserved segs) (img_lo A) (img_hi A) (S (length (segments_reserved segs))))%bool.
