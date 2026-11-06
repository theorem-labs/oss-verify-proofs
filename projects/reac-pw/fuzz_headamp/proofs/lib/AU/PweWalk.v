(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at 5afd8b87436 (its entry-state proof, the run / keep / register-value chain and the call through the runtime's intrinsic law) and proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b01 (the `ret` leaf) for reac-pw/fuzz_rate's image B: the walk is of pod_write_ent 0x83cc4 against lib/AU/PweSpec.v's pod_write_ent_specX. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/PweWalk.v at d75b4b9c2458; module paths changed to reac-pw/fuzz_headamp; comments' addresses and image hashes moved to fuzz_headamp's image B; no term changed. *)
(* The walk of pod_write_ent at 0x84634 on reac-pw/fuzz_headamp's image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address is measured on its unstripped
   twin sha256 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff).

   proves function pod_write_ent

   WHY NO INSTRUMENTED CHECK FAILS: each of the fourteen checks reads the shadow byte of an address inside pp's
   19744-byte block or inside e's 104 bytes, and the contract's premises mark both ranges usable; the walk gives
   the engine those two ranges as shadow entries (and a third for the eight bytes at pp + len, which the two
   put32s write), so each `bnez` after a check is decided as not taken and no call of an __asan_report_ entry is
   ever stepped.
   WHY NO UBSan TRAP FIRES: the ten trap branches to `unimp` 0x8487c are the alignment tests of e and pp and four
   pairs of bounds / wrap tests at pp + len, pp + len + 4, pp + len + 8 and pp + len + 8 + size. The alignment
   tests are decided by the atom facts (8 | pp, 8 | e); each bounds test by len + n <= 16384 (the capacity
   premise); each wrap test by pp + 19744 <= 2^63.
   WHAT THE TWO RUNTIME CALLS GIVE: __asan_memcpy(pp + len + 8, e + 8, size) and __asan_memset(pp + len + 8 + size,
   0, pad) enter as the kit's intrinsic law (PweKit.pwe_intrin_at), whose premises the walk discharges from the
   contract's: the destination is the caller's to write, both ranges are in the application range, marked usable
   and have readable shadow hulls, and the source and destination do not overlap. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import PweSpec PweMem PweKit PweStates.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the arithmetic the states' branch conditions need ---- *)
Lemma pwe_lxor_m1 : forall a, Z.lxor a (-1) = - a - 1.
Proof.
intros a. apply Z.bits_inj'. intros n Hn.
rewrite Z.lxor_spec, Z.bits_m1 by lia.
replace (- a - 1) with (Z.lnot a) by (unfold Z.lnot; lia).
rewrite Z.lnot_spec by lia. destruct (Z.testbit a n); reflexivity.
Qed.
Lemma pwe_land7 : forall a, 0 <= a -> Z.land a 7 = a mod 8.
Proof.
intros a Ha. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.
(* `not x` is `xor x (-1)`, and the engine evaluates the literal to 2 ^ 64 - 1: the complement in 64 bits. *)
Lemma pwe_lxor_ones64 : forall a, 0 <= a < 2 ^ 64 -> Z.lxor a (2 ^ 64 - 1) = 2 ^ 64 - 1 - a.
Proof.
intros a Ha.
assert (Hones : Z.ones 64 = 2 ^ 64 - 1) by reflexivity.
assert (Hb : forall n, 64 <= n -> Z.testbit a n = false).
{ intros n Hn. destruct (Z.eq_dec a 0) as [->|Hz]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|].
  assert (Z.log2 a < 64); [|lia]. apply Z.log2_lt_pow2; lia. }
assert (E : Z.lxor a (2 ^ 64 - 1) = Z.land (- a - 1) (2 ^ 64 - 1)).
{ apply Z.bits_inj'. intros n Hn. rewrite <- Hones.
  rewrite Z.land_spec, Z.lxor_spec.
  replace (- a - 1) with (Z.lnot a) by (unfold Z.lnot; lia).
  rewrite Z.lnot_spec by lia.
  destruct (Z.lt_ge_cases n 64) as [Hl|Hl].
  - rewrite Z.ones_spec_low by lia. rewrite andb_true_r. destruct (Z.testbit a n); reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite andb_false_r, Hb by lia. reflexivity. }
rewrite E. rewrite <- Hones at 1. rewrite Z.land_ones by lia.
rewrite <- (Z_mod_plus_full (- a - 1) 1 (2 ^ 64)), Z.mul_1_l.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma pwe_u8 : forall v, 0 <= v < 256 -> bv_unsigned (Z_to_bv 8 v) = v.
Proof.
intros v Hv. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. lia.
Qed.
(* ((x mod 2 ^ 64) mod 8) is x mod 8: the shadow granule is a divisor of the word *)
Lemma pwe_mod64_8 : forall x, (x mod 2 ^ 64) mod 8 = x mod 8.
Proof.
intros x. rewrite (Z.div_mod x (2 ^ 64)) at 2 by lia.
replace (2 ^ 64 * (x / 2 ^ 64)) with ((2 ^ 61 * (x / 2 ^ 64)) * 8) by (change (2 ^ 64) with (2 ^ 61 * 8); ring).
rewrite Z.add_comm, Z_mod_plus_full. reflexivity.
Qed.
(* the pad the code computes is the model's pad8 of the entry's size, when len is 8-aligned *)
Lemma pwe_pad_is : forall len size, len mod 8 = 0 ->
  (- (len + 8 + size)) mod 8 = Model.pad8 size.
Proof.
intros len size Hl8.
assert (H8 : (- (len + 8 + size)) mod 8 = (- size) mod 8).
{ pose proof (Z.div_mod len 8 ltac:(lia)) as Hd. rewrite Hl8, Z.add_0_r in Hd.
  replace (- (len + 8 + size)) with ((- size) + (- (len / 8) - 1) * 8) by lia.
  apply Z_mod_plus_full. }
rewrite H8. unfold Model.pad8. symmetry.
rewrite Zminus_mod_idemp_r. replace (8 - size) with (- size + 1 * 8) by ring.
apply Z_mod_plus_full.
Qed.

(* the value of an atom plus a negative offset, as the engine canonises it *)
Lemma pwe_U_off_neg : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> - M64 <= v + c < 0 ->
  U E (SOff n c) = v + c + M64.
Proof.
intros E n v c H Hv Hc. rewrite U_SOff, H, unsigned_lit_small by lia. apply pwe_zneg. lia.
Qed.
Lemma pwe_U_m1 : forall E, U E (SLit (-1)) = 2 ^ 64 - 1.
Proof. intros E. rewrite U_SLit, pwe_zneg by (unfold M64; lia). unfold M64. lia. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis HBgot : as_got_shadow B = PWE_GOT.
Hypothesis HBcell : as_shadow_cell B = PWE_CELL.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy PWE_MEMCPY.
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet PWE_MEMSET.

(* ---- R0's entry state: the save slot, the GOT slot and the shadow-offset cell ---- *)
Lemma pwe_entry0 : forall (W : world rsegs) regs memc q,
getr regs 11 = w64 q -> 0 <= q -> q + Layout.ENT_SIZE <= 2 ^ 47 -> q mod 8 = 0 ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - 48 <= a < spZ regs -> apresent (w_H W) memc a) ->
rdword (aview rsegs (w_H W) memc) PWE_GOT = Some PWE_CELL ->
rdword (aview rsegs (w_H W) memc) PWE_CELL = Some SHADOW_OFF ->
st_ok rsegs (Ereg regs (pwe_extra [])) ss_p0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 PWE_A) memc (seg_rom rsegs))).
Proof.
intros W regs memc q H11 Hq0 Hq47 Hq8 Hsp Hal Hpr Kgot Kcell.
cbv [Layout.ENT_SIZE] in *.
rewrite restrict_mkst_fx.
set (E := Ereg regs (pwe_extra [])).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E11 : ew E 11 = Z_to_bv 64 q) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (U11 : bv_unsigned (ew E 11) = q) by (rewrite E11; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
unfold ss_p0. apply (entry_st_ok_full rsegs); change (Ereg regs (pwe_extra [])) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold p0_regions, pwe_stack_region, pwe_got_region, pwe_cell_region.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
  unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply Hpr. lia.
  + split; [unfold PWE_GOT; lia|]. split; [unfold PWE_GOT; lia|]. split; [intros o Ho; unfold PWE_GOT in *; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs E _ 0 PWE_GOT 8 (SLit PWE_CELL) PWE_CELL);
    [reflexivity | unfold PWE_CELL; zside | zside |].
    exact (val_mem_of_rdword rsegs (w_H W) memc _ _ Kgot).
  + split; [unfold PWE_CELL; lia|]. split; [unfold PWE_CELL; lia|]. split; [intros o Ho; unfold PWE_CELL in *; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs E _ 0 PWE_CELL 8 (SOff 32 0) SHADOW_OFF);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
    exact (val_mem_of_rdword rsegs (w_H W) memc _ _ Kcell).
- apply pairwise_disjoint_of_extents.
  unfold p0_regions, pwe_stack_region, pwe_got_region, pwe_cell_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold PWE_GOT, PWE_CELL. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [p0_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, U11, U32. change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
  rewrite Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia.
Qed.
(* ---- R1's entry state: the len cell, e's two words and the eight bytes at pp + len ---- *)
Lemma pwe_entry1 : forall (W : world rsegs) regs memc pp q len size type,
getr regs 9 = w64 pp -> getr regs 11 = w64 q -> getr regs 15 = w64 SHADOW_OFF ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
0 <= pp -> pp mod 8 = 0 -> pp + 19744 <= 2 ^ 47 ->
0 <= q -> q mod 8 = 0 -> q + 104 <= 2 ^ 47 ->
0 <= len -> len mod 8 = 0 -> len + 8 + size <= 16384 ->
0 <= size <= 96 -> 0 <= type < 2 ^ 32 ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 16384) 8 len ->
val_mem rsegs (mrestrict (w_H W) memc) q 4 type ->
val_mem rsegs (mrestrict (w_H W) memc) (q + 4) 4 size ->
(forall a, pp + len <= a < pp + len + 8 \/ pp + 16384 <= a < pp + 16392 -> apresent (w_H W) memc a) ->
(pp + 19744 <= q \/ q + 104 <= pp) ->
st_ok rsegs (Ereg regs (pwe_extra [len; size; type; pp + len])) ss_p1
  (restrict (w_H W) (mkst regs (Z_to_bv 64 PWE_P1) memc (seg_rom rsegs))).
Proof.
intros W regs memc pp q len size type H9 H11 H15 Hsp Hal16 Hpp0 Hpp8 Hpp47 Hq0 Hq8 Hq47
Hlen0 Hlen8 Hcap Hsz Hty Vlen Vty Vsz Hpres Hsep.
rewrite restrict_mkst_fx.
set (E := Ereg regs (pwe_extra [len; size; type; pp + len])).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E9 : ew E 9 = Z_to_bv 64 pp) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E11 : ew E 11 = Z_to_bv 64 q) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (E33 : ew E 33 = Z_to_bv 64 len) by reflexivity.
assert (E34 : ew E 34 = Z_to_bv 64 size) by reflexivity.
assert (E35 : ew E 35 = Z_to_bv 64 type) by reflexivity.
assert (E36 : ew E 36 = Z_to_bv 64 (pp + len)) by reflexivity.
assert (U9 : bv_unsigned (ew E 9) = pp) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = q) by (rewrite E11; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33) = len) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = size) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = type) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = pp + len) by (rewrite E36; apply unsigned_lit_small; lia).
assert (Hnp : U E pwe_notpp = 2 ^ 64 - 1 - pp).
{ unfold pwe_notpp. rewrite U_SAlu, (U_atom E 9 pp E9) by lia. rewrite pwe_U_m1.
  cbn [zalu_raw]. rewrite pwe_lxor_ones64 by lia. apply zcanon_id. unfold M64. lia. }
assert (Htot : U E pwe_tot = len + 8 + size).
{ unfold pwe_tot. rewrite U_SAlu, (U_atom_off E 33 len 8 E33), (U_atom_off E 34 size 0 E34) by lia.
  cbn [zalu_raw]. rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia. }
unfold ss_p1. apply (entry_st_ok_full rsegs);
change (Ereg regs (pwe_extra [len; size; type; pp + len])) with E.
- unfold p1_regs. apply regs_ok_override; [subst E; apply regs_ok_Ereg | |].
  + intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
  + cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. exact H15.
- vm_compute. reflexivity.
- unfold p1_regions, p1_len_region, p1_ent_region, p1_body_region.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
  unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
  rewrite ?U9, ?U11, ?U36.
  + split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable rsegs); apply Hpres; right; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 33 0) len);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vlen].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val rsegs E _ q 0 4 (SOff 35 0) type);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |
       rewrite Z.add_0_r; exact Vty].
    * apply (chunk_ok_val rsegs E _ q 4 4 (SOff 34 0) size);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vsz].
  + split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable rsegs); apply Hpres; left; lia | constructor].
- apply pairwise_disjoint_of_extents.
  unfold p1_regions, p1_len_region, p1_ent_region, p1_body_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U11, U36.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split].
  + cbn [p1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, U9, U11, U32, U33, U34, U35, U36.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
    rewrite !Z.mod_1_r. unfold SHADOW_OFF.
    repeat split; try lia.
    * pose proof (Z.div_mod pp 8 ltac:(lia)) as Hp. rewrite Hpp8, Z.add_0_r in Hp.
      pose proof (Z.div_mod len 8 ltac:(lia)) as Hl. rewrite Hlen8, Z.add_0_r in Hl.
      rewrite Hp, Hl. replace (8 * (pp / 8) + 8 * (len / 8)) with ((pp / 8 + len / 8) * 8) by ring.
      apply Z.mod_mul. lia.
  + cbn [p1_facts f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b].
    repeat split.
    * rewrite branch_geu_U, (pwe_U_off_neg E 33 len (-16381) E33) by (unfold M64; lia).
      rewrite (U_lit E 18446744073709535231) by lia.
      apply negb_true_iff, Z.ltb_ge. unfold M64. lia.
    * rewrite branch_geu_U, (pwe_U_off_neg E 33 len (-16377) E33) by (unfold M64; lia).
      rewrite (U_lit E 18446744073709535231) by lia.
      apply negb_true_iff, Z.ltb_ge. unfold M64. lia.
    * rewrite branch_geu_U, Hnp, (U_atom_off E 33 len 0 E33) by lia.
      apply negb_true_iff, Z.ltb_ge. lia.
    * rewrite branch_geu_U, Hnp, (U_atom_off E 33 len 4 E33) by lia.
      apply negb_true_iff, Z.ltb_ge. lia.
    * rewrite branch_geu_U, Hnp, (U_atom_off E 33 len 8 E33) by lia.
      apply negb_true_iff, Z.ltb_ge. lia.
    * rewrite branch_geu_U, Htot, (U_lit E 16384) by lia.
      apply negb_true_iff, Z.ltb_ge. lia.
  + cbn [p1_facts f_alias alias_ok]. split; [|exact I].
    rewrite denot_lit_U, (denot_lit_U E (SOff 36 0)). f_equal.
    rewrite U_SAlu, (U_atom E 9 pp E9), (U_atom E 33 len E33), (U_atom E 36 (pp + len) E36) by lia.
    cbn [zalu_raw]. apply zcanon_id. unfold M64. lia.
Qed.
(* ---- the shadow entries: pp's block, e's object and the eight bytes at pp + len ---- *)
Lemma pwe_band : forall a n x, amem_range a n -> a <= x < a + n ->
  ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Proof.
intros a n x Ham Hx Hb.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.
Lemma pwe_shent_pp : forall (W : world rsegs) memc E (m : nat) p pp n lo hi,
ew E 32 = Z_to_bv 64 SHADOW_OFF -> ew E m = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF pp n -> amem_range pp n ->
pp <= p + lo -> p + hi <= pp + n -> 0 <= lo -> lo <= hi ->
shent_ok rsegs PWE_Bx E (mrestrict (w_H W) memc) (mkSHE m lo hi).
Proof.
intros W memc E m p pp n lo hi E32 Em Hp Hra Ham H1 H2 H3 H4.
assert (U32 : U E PWE_Bx = SHADOW_OFF).
{ unfold PWE_Bx. apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF. lia. }
apply (shent_ok_of_range rsegs (w_H W) memc E PWE_Bx m pp n p lo hi);
[exact Hra | exact U32 | apply (U_atom E m p Em); lia | lia | lia |].
intros x Hx. apply (pwe_band pp n x Ham). lia.
Qed.
Lemma pwe_sh1 : forall (W : world rsegs) memc E pp q len,
ew E 32 = Z_to_bv 64 SHADOW_OFF -> ew E 9 = Z_to_bv 64 pp -> ew E 11 = Z_to_bv 64 q ->
ew E 36 = Z_to_bv 64 (pp + len) ->
0 <= pp -> pp + 19744 <= 2 ^ 47 -> amem_range pp 19744 ->
0 <= q -> q + 104 <= 2 ^ 47 -> amem_range q 104 ->
0 <= len -> len + 8 <= 16384 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF pp 19744 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF q 104 ->
sh_ok rsegs PWE_Bx p1_SH E (mrestrict (w_H W) memc).
Proof.
intros W memc E pp q len E32 E9 E11 E36 Hpp0 Hpp47 Hppam Hq0 Hq47 Hqam Hlen0 Hcap Rapp Raq.
unfold p1_SH. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (pwe_shent_pp W memc E 9 pp pp 19744 0 19744); try assumption; lia.
- apply (pwe_shent_pp W memc E 11 q q 104 0 104); try assumption; lia.
- apply (pwe_shent_pp W memc E 36 (pp + len) pp 19744 0 8); try assumption; lia.
Qed.
Lemma pwe_shblk : forall (W : world rsegs) memc E pp (SHl : list shent),
SHl = [mkSHE 9 0 19744] ->
ew E 32 = Z_to_bv 64 SHADOW_OFF -> ew E 9 = Z_to_bv 64 pp ->
0 <= pp -> pp + 19744 <= 2 ^ 47 -> amem_range pp 19744 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF pp 19744 ->
sh_ok rsegs PWE_Bx SHl E (mrestrict (w_H W) memc).
Proof.
intros W memc E pp SHl -> E32 E9 Hpp0 Hpp47 Hppam Rapp.
constructor; [|constructor].
apply (pwe_shent_pp W memc E 9 pp pp 19744 0 19744); try assumption; lia.
Qed.
(* ---- R2's entry state, after the body copy: the len cell holds len + 8, and the pad is Model.pad8 ---- *)
Lemma pwe_pad_val : forall E len size, ew E 33 = Z_to_bv 64 len -> ew E 34 = Z_to_bv 64 size ->
  0 <= len <= 16376 -> len mod 8 = 0 -> 0 <= size <= 96 ->
  U E pwe_pad = Model.pad8 size.
Proof.
intros E len size E33 E34 Hlen Hl8 Hsz.
assert (Hm1 : U E (SLit (-1)) = 2 ^ 64 - 1) by apply pwe_U_m1.
assert (Hm8 : U E (SLit (-8)) = 2 ^ 64 - 8).
{ rewrite U_SLit, pwe_zneg by (unfold M64; lia). unfold M64. lia. }
assert (HA : U E (SMd M_MUL (SOff 33 0) (SLit (-1))) = (- len) mod 2 ^ 64).
{ rewrite U_SMd, (U_atom_off E 33 len 0 E33) by lia. rewrite Hm1. cbn [zmd_raw].
  unfold zcanon, M64. rewrite Z.add_0_r.
  replace ((len) * (2 ^ 64 - 1)) with ((- len) + len * 2 ^ 64) by ring.
  apply Z_mod_plus_full. }
assert (HC : U E (SMd M_MUL (SOff 34 0) (SLit (-1))) = (- size) mod 2 ^ 64).
{ rewrite U_SMd, (U_atom_off E 34 size 0 E34) by lia. rewrite Hm1. cbn [zmd_raw].
  unfold zcanon, M64. rewrite Z.add_0_r.
  replace ((size) * (2 ^ 64 - 1)) with ((- size) + size * 2 ^ 64) by ring.
  apply Z_mod_plus_full. }
assert (HB : U E (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit (-1))) (SLit (-8))) = (- len - 8) mod 2 ^ 64).
{ rewrite U_SAlu, HA, Hm8. cbn [zalu_raw]. unfold zcanon, M64.
  rewrite Zplus_mod_idemp_l.
  replace ((- len) + (2 ^ 64 - 8)) with ((- len - 8) + 1 * 2 ^ 64) by ring.
  apply Z_mod_plus_full. }
assert (HD : U E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit (-1))) (SLit (-8)))
               (SMd M_MUL (SOff 34 0) (SLit (-1)))) = (- len - 8 - size) mod 2 ^ 64).
{ rewrite U_SAlu, HB, HC. cbn [zalu_raw]. unfold zcanon, M64.
  rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r.
  replace ((- len - 8) + (- size)) with (- len - 8 - size) by ring. reflexivity. }
unfold pwe_pad. rewrite U_SAlu, HD, U_SLit. cbn [zalu_raw].
rewrite (zcanon_id 7) by (unfold M64; lia).
rewrite pwe_land7 by (apply Z.mod_pos_bound; lia).
rewrite pwe_mod64_8.
replace (- len - 8 - size) with (- (len + 8 + size)) by ring.
rewrite pwe_pad_is by exact Hl8.
pose proof (pwm_pad8_range size) as Hp. apply zcanon_id. unfold M64. lia.
Qed.
(* s3 holds the shadow address of the len cell *)
Lemma pwe_sh3_denot : forall E pp, ew E 9 = Z_to_bv 64 pp -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
0 <= pp -> pp + 16384 < 2 ^ 64 -> sv_denot E pwe_sh3 = w64 (shadow_addr (pp + 16384)).
Proof.
intros E pp H9 H32 H0 H1.
rewrite (match_x_denot (SOff 32 0) E pwe_sh3 (SOff 9 16384) ltac:(vm_compute; reflexivity)).
unfold cell_x, w64, shadow_addr. f_equal.
rewrite (U_atom E 32 SHADOW_OFF H32) by (unfold SHADOW_OFF; lia).
rewrite (U_atom_off E 9 pp 16384 H9) by lia. reflexivity.
Qed.

Lemma pwe_entry2 : forall (W : world rsegs) regs memc pp len size,
getr regs 9 = w64 pp ->
getr regs 8 = w64 (pp + 16384) -> getr regs 18 = w64 size ->
getr regs 19 = w64 (shadow_addr (pp + 16384)) ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
0 <= pp -> pp mod 8 = 0 -> pp + 19744 <= 2 ^ 47 ->
0 <= len -> len mod 8 = 0 -> len + 8 + size + Model.pad8 size <= 16384 ->
0 <= size <= 96 ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 16384) 8 (len + 8) ->
(forall a, pp + 16384 <= a < pp + 16392 -> apresent (w_H W) memc a) ->
st_ok rsegs (Ereg regs (pwe_extra [len; size])) ss_p2
  (restrict (w_H W) (mkst regs (Z_to_bv 64 PWE_P2) memc (seg_rom rsegs))).
Proof.
intros W regs memc pp len size H9 H8 H18 H19 Hsp Hal16 Hpp0 Hpp8 Hpp47 Hlen0 Hlen8 Hcap Hsz Vlen Hpres.
pose proof (pwm_pad8_range size) as Hpad.
rewrite restrict_mkst_fx.
set (E := Ereg regs (pwe_extra [len; size])).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E9 : ew E 9 = Z_to_bv 64 pp) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (E33 : ew E 33 = Z_to_bv 64 len) by reflexivity.
assert (E34 : ew E 34 = Z_to_bv 64 size) by reflexivity.
assert (U9 : bv_unsigned (ew E 9) = pp) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33) = len) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = size) by (rewrite E34; apply unsigned_lit_small; lia).
assert (Htot : U E pwe_tot = len + 8 + size).
{ unfold pwe_tot. rewrite U_SAlu, (U_atom_off E 33 len 8 E33), (U_atom_off E 34 size 0 E34) by lia.
  cbn [zalu_raw]. rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia. }
assert (Hnp : U E pwe_notpp = 2 ^ 64 - 1 - pp).
{ unfold pwe_notpp. rewrite U_SAlu, (U_atom E 9 pp E9) by lia. rewrite pwe_U_m1.
  cbn [zalu_raw]. rewrite pwe_lxor_ones64 by lia. apply zcanon_id. unfold M64. lia. }
assert (Hpd : U E pwe_pad = Model.pad8 size) by (apply (pwe_pad_val E len size E33 E34); lia).
unfold ss_p2. apply (entry_st_ok_full rsegs); change (Ereg regs (pwe_extra [len; size])) with E.
- unfold p2_regs.
  apply regs_ok_override; [apply regs_ok_override; [apply regs_ok_override;
    [subst E; apply regs_ok_Ereg | | ] | | ] | | ];
  try (intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz).
  + rewrite (pwe_soff E 9 pp 16384 E9). symmetry. exact H8.
  + rewrite (pwe_sh3_denot E pp E9 E32) by lia. symmetry. exact H19.
  + rewrite (pwe_soff E 34 size 0 E34), Z.add_0_r. symmetry. exact H18.
- vm_compute. reflexivity.
- unfold p2_regions, p2_len_region.
  apply Forall_cons; [|apply Forall_nil];
  unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
  rewrite ?U9.
  split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (apresent_writable rsegs); apply Hpres; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 33 8) (len + 8));
  [rewrite (pwe_soff E 33 len 8 E33); reflexivity | zside | zside | exact Vlen].
- apply pairwise_disjoint_of_extents.
  unfold p2_regions, p2_len_region, extent_of_region. cbn [map]. cbn [zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split].
  + cbn [p2_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, U9, U32, U33, U34.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
    rewrite !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia.
  + cbn [p2_facts f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b].
    repeat split.
    * rewrite branch_geu_U, U_SAlu, Hpd, Htot, (U_lit E 16384) by lia.
      cbn [zalu_raw]. rewrite (zcanon_id (Model.pad8 size + (len + 8 + size))) by (unfold M64; lia).
      apply negb_true_iff, Z.ltb_ge. lia.
    * rewrite branch_ltu_U, Htot, (U_lit E 16385) by lia. apply Z.ltb_lt. lia.
    * rewrite branch_geu_U, Hnp, Htot. apply negb_true_iff, Z.ltb_ge. lia.
  + cbn [p2_facts f_alias alias_ok]. exact I.
Qed.
(* ---- R3's entry state, after the pad fill: the len cell holds len + 8 + size, and the save slot the
   five registers the prologue stored ---- *)
Lemma pwe_entry3 : forall (W : world rsegs) regs memc pp len size ra0 s00 s10 s20 s30,
getr regs 9 = w64 pp ->
getr regs 8 = w64 (pp + 16384) -> getr regs 18 = w64 (Model.pad8 size) ->
getr regs 19 = w64 (shadow_addr (pp + 16384)) ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
0 <= pp -> pp mod 8 = 0 -> pp + 19744 <= 2 ^ 47 -> (pp + 19744 <= spZ regs \/ spZ regs + 48 <= pp) ->
0 <= len -> len mod 8 = 0 -> len + 8 + size + Model.pad8 size <= 16384 ->
0 <= size <= 96 ->
0 <= ra0 < 2 ^ 64 -> 0 <= s00 < 2 ^ 64 -> 0 <= s10 < 2 ^ 64 -> 0 <= s20 < 2 ^ 64 -> 0 <= s30 < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 16384) 8 (len + 8 + size) ->
val_mem rsegs (mrestrict (w_H W) memc) (spZ regs + 40) 8 ra0 ->
val_mem rsegs (mrestrict (w_H W) memc) (spZ regs + 32) 8 s00 ->
val_mem rsegs (mrestrict (w_H W) memc) (spZ regs + 24) 8 s10 ->
val_mem rsegs (mrestrict (w_H W) memc) (spZ regs + 16) 8 s20 ->
val_mem rsegs (mrestrict (w_H W) memc) (spZ regs + 8) 8 s30 ->
(forall a, pp + 16384 <= a < pp + 16392 -> apresent (w_H W) memc a) ->
st_ok rsegs (Ereg regs (pwe_extra [len; size; ra0; s00; s10; s20; s30])) ss_p3
  (restrict (w_H W) (mkst regs (Z_to_bv 64 PWE_P3) memc (seg_rom rsegs))).
Proof.
intros W regs memc pp len size ra0 s00 s10 s20 s30 H9 H8 H18 H19 Hsp Hal16 Hpp0 Hpp8 Hpp47 Hppsp
Hlen0 Hlen8 Hcap Hsz Hra0 Hs00 Hs10 Hs20 Hs30 Vlen Vra Vs0 Vs1 Vs2 Vs3 Hpres.
pose proof (pwm_pad8_range size) as Hpad.
rewrite restrict_mkst_fx.
set (E := Ereg regs (pwe_extra [len; size; ra0; s00; s10; s20; s30])).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E9 : ew E 9 = Z_to_bv 64 pp) by (subst E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (E33 : ew E 33 = Z_to_bv 64 len) by reflexivity.
assert (E34 : ew E 34 = Z_to_bv 64 size) by reflexivity.
assert (E35 : ew E 35 = Z_to_bv 64 ra0) by reflexivity.
assert (E36 : ew E 36 = Z_to_bv 64 s00) by reflexivity.
assert (E37 : ew E 37 = Z_to_bv 64 s10) by reflexivity.
assert (E38 : ew E 38 = Z_to_bv 64 s20) by reflexivity.
assert (E39 : ew E 39 = Z_to_bv 64 s30) by reflexivity.
assert (U9 : bv_unsigned (ew E 9) = pp) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33) = len) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = size) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = ra0) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = s00) by (rewrite E36; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E 37) = s10) by (rewrite E37; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew E 38) = s20) by (rewrite E38; apply unsigned_lit_small; lia).
assert (U39 : bv_unsigned (ew E 39) = s30) by (rewrite E39; apply unsigned_lit_small; lia).
assert (Hpd : U E pwe_pad = Model.pad8 size) by (apply (pwe_pad_val E len size E33 E34); lia).
unfold ss_p3. apply (entry_st_ok_full rsegs);
change (Ereg regs (pwe_extra [len; size; ra0; s00; s10; s20; s30])) with E.
- unfold p3_regs.
  apply regs_ok_override; [apply regs_ok_override; [apply regs_ok_override;
    [subst E; apply regs_ok_Ereg | | ] | | ] | | ];
  try (intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz).
  + rewrite (pwe_soff E 9 pp 16384 E9). symmetry. exact H8.
  + rewrite (pwe_sh3_denot E pp E9 E32) by lia. symmetry. exact H19.
  + rewrite denot_lit_U, Hpd. symmetry. exact H18.
- vm_compute. reflexivity.
- unfold p3_regions, p3_stack_region, p3_len_region.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
  unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
  rewrite ?E2, ?U9.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
    * apply (chunk_ok_val rsegs E _ (spZ regs) 40 8 (SOff 35 0) ra0);
      [rewrite (pwe_soff E 35 ra0 0 E35), Z.add_0_r; reflexivity | zside | zside | exact Vra].
    * apply (chunk_ok_val rsegs E _ (spZ regs) 32 8 (SOff 36 0) s00);
      [rewrite (pwe_soff E 36 s00 0 E36), Z.add_0_r; reflexivity | zside | zside | exact Vs0].
    * apply (chunk_ok_val rsegs E _ (spZ regs) 24 8 (SOff 37 0) s10);
      [rewrite (pwe_soff E 37 s10 0 E37), Z.add_0_r; reflexivity | zside | zside | exact Vs1].
    * apply (chunk_ok_val rsegs E _ (spZ regs) 16 8 (SOff 38 0) s20);
      [rewrite (pwe_soff E 38 s20 0 E38), Z.add_0_r; reflexivity | zside | zside | exact Vs2].
    * apply (chunk_ok_val rsegs E _ (spZ regs) 8 8 (SOff 39 0) s30);
      [rewrite (pwe_soff E 39 s30 0 E39), Z.add_0_r; reflexivity | zside | zside | exact Vs3].
  + split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable rsegs); apply Hpres; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs E _ pp 0x4000 8 pwe_tot (len + 8 + size));
    [unfold pwe_tot; rewrite denot_lit_U; f_equal;
     rewrite U_SAlu, (U_atom_off E 33 len 8 E33), (U_atom_off E 34 size 0 E34) by lia;
     cbn [zalu_raw]; rewrite Z.add_0_r; apply zcanon_id; unfold M64; lia
    | zside | zside | exact Vlen].
- apply pairwise_disjoint_of_extents.
  unfold p3_regions, p3_stack_region, p3_len_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, U9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split].
  + cbn [p3_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, U9, U32, U33, U34, U35, U36, U37, U38, U39.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
    rewrite !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia.
  + cbn [p3_facts f_conds conds_ok]. exact I.
  + cbn [p3_facts f_alias alias_ok]. exact I.
Qed.
(* ---- the post's byte list: the four pieces the function writes ----
   The runtime copy's post gives the body as an equality of views between the destination and the source; the
   runtime fill's post gives each pad byte as 0. pwe_garr8_copy turns the first into a byte list at the
   destination, and pwe_post_bytes assembles all four pieces into the bytes of Model.enc_pod e. *)
Lemma pwe_garr8_copy : forall (H H' : word -> bool) m m' d x (l : list Z),
garr8 rsegs (mrestrict H m) x l ->
(forall i, 0 <= i < Z.of_nat (length l) -> aview rsegs H' m' (d + i) = aview rsegs H m (x + i)) ->
garr8 rsegs (mrestrict H' m') d l.
Proof.
intros H H' m m' d x l Hg Hc. apply pwm_garr8_of_bytes.
- intros j Hj. destruct (Hg j Hj) as [Hv Hr].
  apply (pwm_byte_val rsegs (mrestrict H m) (x + Z.of_nat j) (nth j l 0) Hr) in Hv.
  assert (Ha : aview rsegs H m (x + Z.of_nat j) = Some (nth j l 0)).
  { unfold aview. rewrite Hv. cbn [option_map]. f_equal.
    rewrite pwe_u8 by lia; try reflexivity. }
  apply (pwm_aview_mbyte rsegs H' m' (d + Z.of_nat j) (Z_to_bv 8 (nth j l 0))).
  rewrite (Hc (Z.of_nat j)) by lia. rewrite Ha. f_equal.
  symmetry. rewrite pwe_u8 by lia; try reflexivity.
- intros j Hj. exact (proj2 (Hg j Hj)).
Qed.

Lemma pwe_post_bytes : forall (H H' : word -> bool) (memc mem : word -> option byte) pp q len e,
Z.of_nat (length (Model.e_body e)) = Model.e_size e ->
0 <= Model.e_size e <= 96 -> 0 <= Model.e_type e < 2 ^ 32 ->
garr8 rsegs (mrestrict H memc) q (map (fun x : byte => bv_unsigned x) (Layout.ent_mem e)) ->
val_mem rsegs (mrestrict H' mem) (pp + len) 4 (Model.e_size e) ->
val_mem rsegs (mrestrict H' mem) (pp + len + 4) 4 (Model.e_type e) ->
(forall i, 0 <= i < Model.e_size e ->
 aview rsegs H' mem (pp + len + 8 + i) = aview rsegs H memc (q + 8 + i)) ->
(forall i, 0 <= i < Model.pad8 (Model.e_size e) ->
 mbyte rsegs (mrestrict H' mem) (pp + len + 8 + Model.e_size e + i) = Some (Z_to_bv 8 0)) ->
garr8 rsegs (mrestrict H' mem) (pp + len) (map (fun x : byte => bv_unsigned x) (Model.enc_pod e)).
Proof.
intros H H' memc mem pp q len e Hblen Hsz Hty Hent Vsz Vty Hbody Hpad.
apply (pwm_enc_of_parts rsegs (mrestrict H' mem) (pp + len) e Hblen Hsz Hty Vsz Vty); [|exact Hpad].
apply (pwe_garr8_copy H H' memc mem (pp + len + 8) (q + 8)).
- apply (pwm_ent_body rsegs (mrestrict H memc) q e Hent Hblen). lia.
- intros i Hi.
  assert (Hlen : Z.of_nat (length (map (fun x : byte => bv_unsigned x) (Model.e_body e))) = Model.e_size e)
    by (rewrite length_map; exact Hblen).
  rewrite Hlen in Hi. apply Hbody. exact Hi.
Qed.
(* ---- the shadow clause of the post ----
   pod_write_ent writes no shadow byte: it takes no side-stack frame and calls no poison helper. The post's
   "every byte outside the callee's stack and outside pwe_E is as at the call" therefore already says it, because
   a shadow address is in neither place: the shadow band lies below the allocator's ceiling, and the stack above
   it, while pp's block is in the application range, which the band misses on both sides. *)
Lemma pwe_shadow_kept : forall (W W2 : world rsegs) mem mem2 sp T pp len e,
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp - T <= a < sp) -> ~ pwe_E pp len e a ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W) mem a) ->
alloc_ceiling <= sp - T -> 0 <= len -> len + pwe_len e <= Layout.POD_BUF_MAX ->
amem_range pp Layout.PP_SIZE -> 0 <= pp ->
forall x, 0 <= x < kHighMemEnd ->
aview rsegs (w_H W2) mem2 (shadow_addr x) = aview rsegs (w_H W) mem (shadow_addr x).
Proof.
intros W W2 mem mem2 sp T pp len e HK Hceil Hlen0 Hcap Hppam Hpp0 x Hx.
pose proof (shadow_addr_bounds x Hx) as Hsb.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hn : 0 <= pwe_len e) by (unfold pwe_len; lia).
assert (Hcap' : len + pwe_len e <= 16384) by (cbv [Layout.POD_BUF_MAX] in Hcap; lia).
assert (Hs1 : 2147450880 <= shadow_addr x < 17594333495296).
{ cbv [kLowMemEnd kHighShadowEnd] in Hsb. exact Hsb. }
assert (Hceil' : 140735332483072 <= sp - T) by lia.
assert (Hpa : pp + 19744 <= 2147450879 \/ 17594333495296 <= pp).
{ cbv [amem_range kLowMemEnd kHighMemBeg kHighMemEnd Layout.PP_SIZE] in Hppam.
  destruct Hppam as [H | [H _]]; [left | right]; lia. }
apply HK.
- lia.
- lia.
- cbv [pwe_E Layout.OFF_LEN]. intros Hc.
  destruct Hpa as [Hlow | Hhi]; destruct Hc as [Hc | Hc]; lia.
Qed.

(* and then every range the contract said was marked usable still is *)
Lemma pwe_ra_kept_of_shadow : forall (W W2 : world rsegs) mem mem2 a n,
(forall x, 0 <= x < kHighMemEnd ->
 aview rsegs (w_H W2) mem2 (shadow_addr x) = aview rsegs (w_H W) mem (shadow_addr x)) ->
amem_range a n -> 0 <= a -> 0 <= n ->
range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF a n ->
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF a n.
Proof.
intros W W2 mem mem2 a n HS Ham Ha0 Hn Hra.
apply (pwm_ra_kept rsegs (w_H W) (w_H W2) mem mem2 a n SHADOW_OFF Hra).
intros y Hy. unfold shadow_of_addr. change (SHADOW_OFF + y / 8) with (shadow_addr y).
apply HS. unfold amem_range in Ham. cbv [kLowMemEnd kHighMemBeg kHighMemEnd] in *. lia.
Qed.
(* ---- two premises of the runtime copy, from the contract's premises on e ---- *)
Lemma pwe_amem_sub : forall a n a' n',
amem_range a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n -> amem_range a' n'.
Proof.
intros a n a' n' H H1 H2 H3. unfold amem_range in *.
destruct H as [H|[H H']]; [left; lia | right; split; lia].
Qed.
(* the source of the copy is readable and outside the callee's own stack *)
Lemma pwe_src_ok : forall (W : world rsegs) (regs : bvmap 5 word) mem x n (l : list Z),
garr8 rsegs (mrestrict (w_H W) mem) x l -> Z.of_nat (length l) = n ->
(forall a, x <= a < x + n -> ~ (spZ regs - ESTACK <= a < spZ regs)) ->
src_ok rsegs W regs mem x n.
Proof.
intros W regs mem x n l Hg Hl Hst a Ha. split; [|exact (Hst a Ha)].
assert (Hj : (Z.to_nat (a - x) < length l)%nat) by lia.
destruct (Hg (Z.to_nat (a - x)) Hj) as [Hv Hr].
rewrite Z2Nat.id in Hv by lia. replace (x + (a - x)) with a in Hv by ring.
apply (pwm_byte_val rsegs (mrestrict (w_H W) mem) a (nth (Z.to_nat (a - x)) l 0) Hr) in Hv.
unfold aview. rewrite Hv. discriminate.
Qed.
(* ---- the engine's path, as a closed computation ----
   With the four states of lib/AU/PweStates.v, the engine runs each leg to its target pc, with its shadow entries
   accepted by the static check: R0 to 0x84664, R1 to __asan_memcpy's entry 0x51d8c (the `jal` at 0x84800 has
   executed), R2 to __asan_memset's entry 0x52228 (the `jal` at 0x84848), R3 to the `ret` at 0x84878. So the trap
   `unimp` 0x8487c and the error path 0x84880 .. 0x84938 are never stepped on the path the contract's premises
   select. *)
Definition pwe_leg (SH : list shent) (ss : sstate) (stop : Z) : (Z * bool)%type :=
  let st := fst (sym_run_toN_tok rsegs pwe_tbl (run_K 0 PWE_Bx SH ss) PWE_Bx PWE_Bspan SH FUEL stop ss) in
  pair (ss_pc (sh_ss st)) (sh_chk st).
Lemma pwe_runs_reach :
  pwe_leg (@nil shent) ss_p0 PWE_P1 = pair PWE_P1 true /\
  pwe_leg p1_SH ss_p1 PWE_MEMCPY = pair PWE_MEMCPY true /\
  pwe_leg p2_SH ss_p2 PWE_MEMSET = pair PWE_MEMSET true /\
  pwe_leg p3_SH ss_p3 PWE_RET = pair PWE_RET true.
Proof. vm_compute. repeat split; reflexivity. Qed.
End d.
End b.

