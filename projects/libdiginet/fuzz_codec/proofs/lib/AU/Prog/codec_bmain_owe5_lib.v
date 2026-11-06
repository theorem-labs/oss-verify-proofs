(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 571 of its 593 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/U/Prog/codec_main_owe0.v; 247 of its 266 lines of code are new or changed and 574 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe1.v, with its addresses and numbers changed; 434 of its 520 lines of code are new or changed and 180 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/codec_amain_owe5.v, with its module paths and module names changed; 375 of its 421 lines of code are new or changed and 474 lines of the source are left out. *)
(* The led loop of OWE5 (RING) in the image-B walk of LLVMFuzzerTestOneInput, 0x82b54-0x82bd4 (fuzz_codec.c:179-182,
   owe_ring of lib/Prog/codec_owe.v). Image B keeps the two accumulators in memory: the payload p[3] at F + 32
   (its shadow byte, frame shadow byte 4, set to 3 at 0x82b2c), p[1] at F + 33 and p[2] at F + 34. A pass with
   led = 2 .. 15 in a2 and -led in a3, b in a1: it tests bit led - 1 of b (0x82b60 beqz); when the bit is set it
   checks the pointer F + 32 against overflow (0x82b70, a trap edge of bm_trap_taken), takes F + 33 (led <= 8,
   from the spill 96(sp1)) or F + 34 (from 88(sp1)), checks that byte's shadow (slow block 0x82bd8), and ors
   1 << (8 - led) or 1 << (15 - led) into p[1] or p[2] (0x82ba0-0x82bc0); then led + 1, -led - 1, and back to
   0x82b54 or, after led = 15, on to 0x82fb0.
   The test depends on b, so the executor would double its paths at each pass. o5_pass is one pass as a lemma over
   machine states: the pass runs from its own executor state (the registers it reads, the three spills, p[1] and
   p[2] as a writable region, the shadow entry of p[3]), built from the pass's numbers; led is split into its 14
   values, so each run has literal registers and decides the trap edge and the led <= 8 test. o5_loop chains the
   14 passes by induction, as the image-A walk's o5_loop (lib/A/Prog/codec_amain_owe5_lib.v) chains its register
   passes; o5_step / o5_acc and their lemmas are that file's. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require codec_owe.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ the loop's arithmetic ================================ *)
(* one pass of owe_ring, as owe_ring's own step *)
Definition o5_step (b : Z) : Z * Z -> Z -> Z * Z :=
fun '(p1, p2) led =>
  if Z.testbit b (led - 1) then
    if led <=? 8 then (Z.lor p1 (2 ^ (8 - led)), p2) else (p1, Z.lor p2 (2 ^ (15 - led)))
  else (p1, p2).
(* the accumulators after j passes *)
Definition o5_acc (b : Z) (j : nat) : Z * Z := fold_left (o5_step b) (map Z.of_nat (seq 2 j)) (0, 0).

Lemma o5_acc_14 : forall b, o5_acc b 14 = codec_owe.owe_ring b.
Proof. intros b. reflexivity. Qed.

Lemma o5_acc_S : forall b j, o5_acc b (S j) = o5_step b (o5_acc b j) (2 + Z.of_nat j).
Proof.
intros b j. unfold o5_acc. rewrite seq_S, map_app, fold_left_app. cbn [map fold_left].
f_equal. lia.
Qed.

Lemma o5_lor_lt : forall p k, 0 <= p < 128 -> 0 <= k <= 6 -> 0 <= Z.lor p (2 ^ k) < 128.
Proof.
intros p k Hp Hk.
assert (Hk2 : 0 < 2 ^ k <= 64) by (split; [apply Z.pow_pos_nonneg; lia | change 64 with (2 ^ 6); apply Z.pow_le_mono_r; lia]).
split; [apply Z.lor_nonneg; lia|].
assert (E : Z.lor p (2 ^ k) = Z.land (Z.lor p (2 ^ k)) (Z.ones 7)).
{ rewrite Z.land_lor_distr_l, !Z.land_ones by lia. change (2 ^ 7) with 128. rewrite !Z.mod_small by lia. reflexivity. }
rewrite E, Z.land_ones by lia. change (2 ^ 7) with 128. pose proof (Z.mod_pos_bound (Z.lor p (2 ^ k)) 128 ltac:(lia)). lia.
Qed.

Lemma o5_acc_range : forall b j, (j <= 14)%nat ->
0 <= fst (o5_acc b j) < 128 /\ 0 <= snd (o5_acc b j) < 128.
Proof.
intros b j. induction j as [|j IH]; intros Hj; [cbn; lia|].
rewrite o5_acc_S. destruct (o5_acc b j) as [p1 p2]. cbn [fst snd] in IH |- *.
destruct (IH ltac:(lia)) as [H1 H2]. unfold o5_step.
destruct (Z.testbit b (2 + Z.of_nat j - 1)); [|cbn; lia].
destruct (Z.leb_spec (2 + Z.of_nat j) 8); cbn [fst snd].
- split; [apply o5_lor_lt; lia | exact H2].
- split; [exact H1 | apply o5_lor_lt; lia].
Qed.

(* ================================ a pass's executor state ================================
   env Ereg regs (cw_extra [F; p1; p2]): atoms 0 .. 31 the registers, 32 SB, 33 F, 34 p[1], 35 p[2].
   Registers: a2 = led and a3 = -led as literals, s5 = atom 32 (the shadow base the instrumented check adds),
   s10 = 1; every other register its own atom. Regions: the spills 88(sp1) = F + 34, 96(sp1) = F + 33,
   112(sp1) = F + 32 (read-only, on s1 = atom 9), and p[1], p[2] (writable, on atom 33). *)
Definition o5p_sregs (led : Z) : list sv :=
sr_set (sr_set (sr_set (sr_set sr_atoms 12%bv (SLit led)) 13%bv (SLit (2 ^ 64 - led))) 21%bv (SOff 32 0)) 26%bv (SLit 1).
Definition o5p_sp : YP09.region :=
YP09.mkRegion (Some 9%nat) 88 120 0 0
[YP09.mkChunk 88 (CVal 8 (SOff 33 34)); YP09.mkChunk 96 (CVal 8 (SOff 33 33)); YP09.mkChunk 112 (CVal 8 (SOff 33 32))].
Definition o5p_pl : YP09.region :=
YP09.mkRegion (Some 33%nat) 33 35 33 35 [YP09.mkChunk 33 (CVal 1 (SOff 34 0)); YP09.mkChunk 34 (CVal 1 (SOff 35 0))].
Definition o5p_AF : list (nat * afact) :=
[(32%nat, mkAF SB SB 0); (33%nat, mkAF 4096 0x7fffff800000 6); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0)].
Definition o5p_ss (led : Z) : sstate :=
mkSS 0x82b54 (o5p_sregs led) [o5p_sp; o5p_pl] None (mkFacts o5p_AF [] []).
Definition o5p_SH : shent := mkSHE 33 32 35.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

Lemma o5p_st : forall led (W : world tfibsegs) regs mem b p1 p2 F sp1,
getr regs 11 = w64 b -> getr regs 12 = w64 led -> getr regs 13 = w64 (2 ^ 64 - led) ->
getr regs 9 = w64 sp1 -> getr regs 21 = w64 SHADOW_OFF -> getr regs 26 = w64 1 ->
2 <= led <= 15 -> F mod 64 = 0 -> 4096 <= F -> F + 512 <= sp1 -> sp1 + 120 <= 2 ^ 47 -> F <= 0x7fffff800000 ->
0 <= p1 < 256 -> 0 <= p2 < 256 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (sp1 + 88) 8 (F + 34) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (sp1 + 96) 8 (F + 33) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (sp1 + 112) 8 (F + 32) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F + 33) 1 p1 -> val_mem tfibsegs (mrestrict (w_H W) mem) (F + 34) 1 p2 ->
(forall a, F + 33 <= a < F + 35 -> apresent (w_H W) mem a) ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (F + 32) 3 -> amem_range (F + 32) 3 ->
st_ok tfibsegs (Ereg regs (cw_extra [F; p1; p2])) (o5p_ss led)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82b54) mem (seg_rom tfibsegs))) /\
sh_ok tfibsegs CW_Bx [o5p_SH] (Ereg regs (cw_extra [F; p1; p2])) (mrestrict (w_H W) mem).
Proof.
intros led W regs mem b p1 p2 F sp1 R11 R12 R13 R9 R21 R26 Hled Hf64 Hf4096 HFsp Hsp47 HFhi Hp1 Hp2
  V88 V96 V112 V33 V34 Hpres Hra Ham.
set (E := Ereg regs (cw_extra [F; p1; p2])).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 F) by (subst E; exact (cw_ew_x regs [F; p1; p2] 0)).
assert (E34 : ew E 34 = Z_to_bv 64 p1) by (subst E; exact (cw_ew_x regs [F; p1; p2] 1)).
assert (E35 : ew E 35 = Z_to_bv 64 p2) by (subst E; exact (cw_ew_x regs [F; p1; p2] 2)).
assert (E9 : ew E 9 = getr regs 9) by (subst E; exact (cw_ew_reg regs _ 9 9%bv eq_refl)).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9, R9; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = F) by (rewrite E33; apply unsigned_lit_small; lia).
assert (DF : forall o, 0 <= o < 512 -> sv_denot E (SOff 33 o) = Z_to_bv 64 (F + o)).
{ intros o Ho. cbn [sv_denot]. rewrite E33, unsigned_lit_small by lia. reflexivity. }
split.
- assert (Hrs : Forall (region_ok tfibsegs E (mrestrict (w_H W) mem)) [o5p_sp; o5p_pl]).
  { apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - unfold o5p_sp, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      + apply (chunk_ok_val tfibsegs E _ sp1 88 8 (SOff 33 34) (F + 34)); [exact (DF 34 ltac:(lia)) | zside | zside | exact V88].
      + apply (chunk_ok_val tfibsegs E _ sp1 96 8 (SOff 33 33) (F + 33)); [exact (DF 33 ltac:(lia)) | zside | zside | exact V96].
      + apply (chunk_ok_val tfibsegs E _ sp1 112 8 (SOff 33 32) (F + 32)); [exact (DF 32 ltac:(lia)) | zside | zside | exact V112].
    - unfold o5p_pl, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U33.
      split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable tfibsegs); apply Hpres; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      + apply (chunk_ok_val tfibsegs E _ F 33 1 (SOff 34 0) p1);
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V33].
      + apply (chunk_ok_val tfibsegs E _ F 34 1 (SOff 35 0) p2);
         [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V34].
  }
  assert (Hpd : pairwise_disjoint E [o5p_sp; o5p_pl]).
  { unfold o5p_sp, o5p_pl. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U33. repeat split; lia. }
  assert (HG : facts_ok E (mkFacts o5p_AF [] [])).
  { split; [|split; exact I].
    unfold o5p_AF. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, E33, E34, E35. rewrite !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia. }
  pose proof (cw_st_ok_at E 0x82b54 sr_atoms [o5p_sp; o5p_pl] (mkFacts o5p_AF [] []) regs (mrestrict (w_H W) mem)
    (regs_ok_Ereg regs _) ltac:(vm_compute; reflexivity) Hrs Hpd HG) as H0.
  pose proof (ast_ok_set_reg_fp tfibsegs E _ _ 12%bv (SLit led) H0 ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs mkst]; rewrite R12; reflexivity)) as H1.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H1. clear H0.
  pose proof (ast_ok_set_reg_fp tfibsegs E _ _ 13%bv (SLit (2 ^ 64 - led)) H1 ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs mkst]; rewrite R13; reflexivity)) as H2.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H2. clear H1.
  pose proof (ast_ok_set_reg_fp tfibsegs E _ _ 21%bv (SOff 32 0) H2 ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs mkst]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned, R21, <- SB_SHADOW_OFF; reflexivity)) as H3.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H3. clear H2.
  pose proof (ast_ok_set_reg_fp tfibsegs E _ _ 26%bv (SLit 1) H3 ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs mkst]; rewrite R26; reflexivity)) as H4.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in H4. clear H3.
  rewrite restrict_mkst_fx. exact H4.
- apply Forall_cons; [|apply Forall_nil]. unfold o5p_SH. change 35 with (32 + 3).
  apply (cw_shent_ra_off W mem E 33 F 32 3 Hra Ham); [lia | lia | lia | lia | exact E33 | exact E32].
Qed.

(* ================================ the executor's values ================================ *)
(* the value of a `SAluw` whose 32-bit result is r (the image-A walk's o5_Uw) *)
Lemma o5_Uw : forall E op a b r, - 2 ^ 31 <= r < 2 ^ 31 ->
zalu_raw 31 32 op (U E a mod 2 ^ 32) (U E b mod 2 ^ 32) mod 2 ^ 32 = r mod 2 ^ 32 ->
U E (SAluw op a b) = r mod 2 ^ 64.
Proof.
intros E op a b r Hr H. rewrite U_of_S, S_SAluw.
set (x := zalu_raw 31 32 op (U E a mod 2 ^ 32) (U E b mod 2 ^ 32)) in *.
unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
assert (Hx : (x + 2 ^ 31) mod 2 ^ 32 = r + 2 ^ 31).
{ rewrite Zplus_mod, H, <- Zplus_mod. apply Z.mod_small. lia. }
rewrite Hx. f_equal. lia.
Qed.
Lemma o5_land1 : forall x k, 0 <= x -> 0 <= k ->
Z.land (Z.shiftr x k) 1 = if Z.testbit x k then 1 else 0.
Proof.
intros x k Hx Hk. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. rewrite Z.pow_1_r.
rewrite Zmod_odd. replace (Z.testbit x k) with (Z.testbit (Z.shiftr x k) 0)
  by (rewrite Z.shiftr_spec by lia; f_equal; lia).
rewrite Z.bit0_odd. reflexivity.
Qed.
(* 0x82b54-0x82b5c: a0 = (b >>w (led - 1)) & 1, led - 1 a literal k *)
Lemma o5_U_bitB : forall E b k, ew E 11 = Z_to_bv 64 b -> 0 <= b < 2 ^ 16 -> 0 <= k <= 14 ->
U E (SAlu ALU_AND (SAluw ALU_SRL (SOff 11 0) (SLit k)) (SLit 1)) = if Z.testbit b k then 1 else 0.
Proof.
intros E b k E11 Hb Hk.
assert (Hs : 0 <= Z.shiftr b k < 2 ^ 16).
{ rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]; nia]. }
assert (Ux : U E (SAluw ALU_SRL (SOff 11 0) (SLit k)) = Z.shiftr b k).
{ rewrite (o5_Uw E ALU_SRL _ _ (Z.shiftr b k)) by (try lia;
    rewrite (U_atom E 11 b E11) by lia; rewrite U_lit by lia;
    cbn [zalu_raw]; rewrite (Z.mod_small b) by lia; rewrite (Z.mod_small k) by lia;
    replace (Z.land k 31) with k
      by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; change (2 ^ 5) with 32; lia);
    reflexivity).
  apply Z.mod_small. lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite Ux, U_lit by lia. rewrite o5_land1 by lia.
unfold zcanon, M64. destruct (Z.testbit b k); reflexivity.
Qed.
(* 0x82bbc or a4,a4,a5: the byte or'ed with the literal bit *)
Lemma o5_lor_ltn : forall n x y, 0 <= n -> 0 <= x < 2 ^ n -> 0 <= y < 2 ^ n -> 0 <= Z.lor x y < 2 ^ n.
Proof.
intros n x y Hn Hx Hy. split; [apply Z.lor_nonneg; lia|].
assert (E : Z.lor x y = Z.land (Z.lor x y) (Z.ones n)).
{ rewrite Z.land_lor_distr_l, !Z.land_ones by lia. rewrite !Z.mod_small by lia. reflexivity. }
rewrite E, Z.land_ones by lia. pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) Hn).
pose proof (Z.mod_pos_bound (Z.lor x y) (2 ^ n) ltac:(lia)). lia.
Qed.
Lemma o5_U_orB : forall E n p m, ew E n = Z_to_bv 64 p -> 0 <= p < 256 -> 0 <= m < 256 ->
U E (SAlu ALU_OR (SOff n 0) (SLit m)) = Z.lor p m.
Proof.
intros E n p m En Hp Hm. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n p En), U_lit by lia.
pose proof (o5_lor_ltn 8 p m ltac:(lia) ltac:(change (2 ^ 8) with 256; lia) ltac:(change (2 ^ 8) with 256; lia)) as L.
change (2 ^ 8) with 256 in L. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.

(* one pass of owe_ring, by the bit and the side *)
Lemma o5_step_clear : forall b p1 p2 led, Z.testbit b (led - 1) = false -> o5_step b (p1, p2) led = (p1, p2).
Proof. intros b p1 p2 led H. unfold o5_step. rewrite H. reflexivity. Qed.
Lemma o5_step_lo : forall b p1 p2 led, Z.testbit b (led - 1) = true -> led <= 8 ->
o5_step b (p1, p2) led = (Z.lor p1 (2 ^ (8 - led)), p2).
Proof.
intros b p1 p2 led H Hl. unfold o5_step. rewrite H. replace (led <=? 8) with true by (symmetry; apply Z.leb_le; lia).
reflexivity.
Qed.
Lemma o5_step_hi : forall b p1 p2 led, Z.testbit b (led - 1) = true -> 9 <= led ->
o5_step b (p1, p2) led = (p1, Z.lor p2 (2 ^ (15 - led))).
Proof.
intros b p1 p2 led H Hl. unfold o5_step. rewrite H. replace (led <=? 8) with false by (symmetry; apply Z.leb_gt; lia).
reflexivity.
Qed.

(* ================================ registers a pass keeps ================================ *)
Definition O5_CLOB : list (bv 5) := [10; 12; 13; 14; 15; 16; 17]%bv.
Definition o5_keep_b (sr : list sv) (led : Z) : bool :=
forallb (fun r => reg_in r O5_CLOB ||
  (sv_eqb (sr_get sr r) (sr_get (o5p_sregs led) r) && sv_atoms_lt 36 (sr_get (o5p_sregs led) r))) all_regs.
Lemma o5_keep_ok : forall E E' (sr' : list sv) led (regs regs' : bvmap 5 word),
env_agree 36 E E' -> o5_keep_b sr' led = true ->
(forall r, getr regs' r = sv_denot E' (sr_get sr' r)) ->
(forall r, getr regs r = sv_denot E (sr_get (o5p_sregs led) r)) ->
forall r, reg_in r O5_CLOB = false -> getr regs' r = getr regs r.
Proof.
intros E E' sr' led regs regs' HA Hb H' H r Hr.
unfold o5_keep_b in Hb. rewrite forallb_forall in Hb. specialize (Hb r (all_regs_in r)).
rewrite Hr in Hb. cbn [orb] in Hb. apply andb_prop in Hb as [Heq Hlt].
rewrite H', (sv_eqb_eq _ _ Heq), (sv_denot_agree 36 E E' _ HA Hlt), H. reflexivity.
Qed.

(* ================================ one pass ================================ *)
Lemma owe_vm_l : forall m a (n : nat) u v, val_mem tfibsegs m a n u ->
u mod 2 ^ (8 * Z.of_nat n) = v mod 2 ^ (8 * Z.of_nat n) -> val_mem tfibsegs m a n v.
Proof. intros m a n u v H Heq k Hk. rewrite (H k Hk). unfold YO0f.le_byte. rewrite Heq. reflexivity. Qed.
Ltac o5_awr Hown EFA U33 pos F :=
  idtac;
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat F);
    [ reflexivity | rewrite ?ew_ewset_other by lia; exact U33
    | let a := fresh "a" in let Ha := fresh "Ha" in
      intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; exists 3, pos;
      split; [exact Hown|]; left; unfold in_zr; cbn [fst snd]; rewrite EFA;
      change (fs_frame_bytes 3) with 512; lia
    | ] ].
Ltac o5_kwr U33 :=
  idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia; rewrite ?U33 in Hb; lia | ]);
  destruct Hr.
(* the field off of p[1] / p[2] at the stop, from the region's chunk e: its value as v *)
Ltac o5_byte HS W U33 E34 E35 off :=
  lazymatch type of HS with st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
    let rg := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
    let Rpl := fresh "Rpl" in
    pose proof (st_ok_region_nth Ev ssx (restrict (w_H W) msx) 1 rg HS ltac:(vm_compute; reflexivity)) as Rpl;
    rewrite restrict_mkst_fx in Rpl; cbn [ms_mem] in Rpl;
    let V := fresh "V" in
    pose proof (field_of_region_any _ _ _ _ _ _ _ _ _ off 1 _ Rpl
      ltac:(rewrite ?ew_ewset_other by lia; exact U33) ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))
      ltac:(lia)) as V;
    apply (owe_vm_l _ _ 1 _ _ V);
    change (bv_unsigned (sv_denot ?E ?e)) with (U E e);
    first [ rewrite (U_atom Ev 34 _ ltac:(rewrite ?ew_ewset_other by lia; exact E34)) by lia
          | rewrite (U_atom Ev 35 _ ltac:(rewrite ?ew_ewset_other by lia; exact E35)) by lia
          | rewrite (o5_U_orB Ev 34 _ _ ltac:(rewrite ?ew_ewset_other by lia; exact E34)) by lia
          | rewrite (o5_U_orB Ev 35 _ _ ltac:(rewrite ?ew_ewset_other by lia; exact E35)) by lia ];
    change (2 ^ (8 * Z.of_N 1)) with 256; change (2 ^ (8 * Z.of_nat 1)) with 256; rewrite Z.mod_mod by lia;
    reflexivity
  end.


Lemma o5_pass : forall led, 2 <= led <= 15 ->
forall (W : world tfibsegs) regs mem md STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc k
(Q : world tfibsegs -> config -> Prop) pos b p1 p2 F sp1,
ajournal tfibsegs B STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc W mem md k ->
In (3, pos) own -> In (3, pos) (frames Sc) -> frame_addr lyc 3 pos = F ->
getr regs 11 = w64 b -> getr regs 12 = w64 led -> getr regs 13 = w64 (2 ^ 64 - led) ->
getr regs 9 = w64 sp1 -> getr regs 21 = w64 SHADOW_OFF -> getr regs 26 = w64 1 ->
F mod 64 = 0 -> 4096 <= F -> F + 512 <= sp1 -> sp1 + 120 <= 2 ^ 47 -> F <= 0x7fffff800000 ->
0 <= p1 < 256 -> 0 <= p2 < 256 -> 0 <= b < 2 ^ 15 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (sp1 + 88) 8 (F + 34) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (sp1 + 96) 8 (F + 33) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (sp1 + 112) 8 (F + 32) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F + 33) 1 p1 -> val_mem tfibsegs (mrestrict (w_H W) mem) (F + 34) 1 p2 ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (F + 32) 3 -> amem_range (F + 32) 3 ->
(forall regs' mem' md',
  ajournal tfibsegs B STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc W mem' md' k ->
  (forall r, reg_in r O5_CLOB = false -> getr regs' r = getr regs r) ->
  getr regs' 12 = w64 (led + 1) -> getr regs' 13 = w64 (2 ^ 64 - (led + 1)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (F + 33) 1 (fst (o5_step b (p1, p2) led)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (F + 34) 1 (snd (o5_step b (p1, p2) led)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 33 <= a < F + 35) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 (if led =? 15 then 0x82fb0 else 0x82b54)) mem' (seg_rom tfibsegs)) md') Q) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 0x82b54) mem (seg_rom tfibsegs)) md) Q.
Proof.
intros led Hled W regs mem md STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc k Q pos b p1 p2 F sp1 HJ Hown HinS EFA
  R11 R12 R13 R9 R21 R26 Hf64 Hf4096 HFsp Hsp47 HFhi Hp1 Hp2 Hb V88 V96 V112 V33 V34 Hra Ham KC.
pose proof HJ as (HAR & _).
destruct (al_frames _ _ LAWS lyc Sc W mem md 3 pos HAR HinS) as (_ & _ & Hpr & _). rewrite EFA in Hpr.
assert (Hpres : forall a, F + 33 <= a < F + 35 -> apresent (w_H W) mem a)
  by (intros a Ha; exact (proj1 (Hpr a ltac:(change (fs_frame_bytes 3) with 512; lia)))).
clear Hpr.
destruct (o5p_st led W regs mem b p1 p2 F sp1 R11 R12 R13 R9 R21 R26 Hled Hf64 Hf4096 HFsp Hsp47 HFhi Hp1 Hp2
  V88 V96 V112 V33 V34 Hpres Hra Ham) as [HS SHOK].
set (E := Ereg regs (cw_extra [F; p1; p2])) in *.
assert (E33 : ew E 33 = Z_to_bv 64 F) by (subst E; exact (cw_ew_x regs [F; p1; p2] 0)).
assert (E34 : ew E 34 = Z_to_bv 64 p1) by (subst E; exact (cw_ew_x regs [F; p1; p2] 1)).
assert (E35 : ew E 35 = Z_to_bv 64 p2) by (subst E; exact (cw_ew_x regs [F; p1; p2] 2)).
assert (E11 : ew E 11 = Z_to_bv 64 b) by (subst E; rewrite (cw_ew_reg regs _ 11 11%bv eq_refl), R11; reflexivity).
assert (U33 : bv_unsigned (ew E 33) = F) by (rewrite E33; apply unsigned_lit_small; lia).
assert (KEEP0 : forall r, getr regs r = sv_denot E (sr_get (o5p_sregs led) r))
  by (intros r; exact (st_ok_restrict_reg tfibsegs (w_H W) E (o5p_ss led) _ r HS)).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 33 <= a < F + 35) ->
  aview tfibsegs (w_H W) mem a = aview tfibsegs (w_H W) mem a) by (intros; reflexivity).
clear V33 V34 V88 V96 V112 Hra Ham Hpres.
unfold o5p_ss in HS.
assert (Hcase : led = 2 \/ led = 3 \/ led = 4 \/ led = 5 \/ led = 6 \/ led = 7 \/ led = 8 \/ led = 9 \/ led = 10 \/
  led = 11 \/ led = 12 \/ led = 13 \/ led = 14 \/ led = 15) by lia.
destruct Hcase as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]].
all: cw_run ltac:(o5_awr Hown EFA U33 pos F); cw_keep ltac:(o5_kwr U33).
all: cw_branch Hb1.
all: rewrite branch_eq_U, U_lit in Hb1 by lia.
all: lazymatch type of Hb1 with context [U ?Ev (SAlu ALU_AND (SAluw ALU_SRL (SOff 11 0) (SLit ?kk)) (SLit 1))] =>
       rewrite (o5_U_bitB Ev b kk ltac:(rewrite ?ew_ewset_other by lia; exact E11) ltac:(lia) ltac:(lia)) in Hb1;
       destruct (Z.testbit b kk) eqn:Tb; cbn in Hb1; try discriminate end.
all: lazymatch type of KC with context [o5_step ?bb (?q1, ?q2) ?L] =>
       first [ rewrite (o5_step_clear bb q1 q2 L Tb) in KC
             | rewrite (o5_step_lo bb q1 q2 L Tb ltac:(lia)) in KC
             | rewrite (o5_step_hi bb q1 q2 L Tb ltac:(lia)) in KC ] end.
all: cbn [fst snd] in KC.
1-26: cw_run_to ltac:(o5_awr Hown EFA U33 pos F) 0x82b54; cw_keep ltac:(o5_kwr U33).
27-28: cw_run_to ltac:(o5_awr Hown EFA U33 pos F) 0x82fb0; cw_keep ltac:(o5_kwr U33).
all: lazymatch goal with HS : st_ok _ ?Ev ?ssx (restrict _ ?msx) |- _ =>
  assert (HA : env_agree 36 E Ev) by (first [apply env_agree_refl | apply env_agree_ewset2]);
  assert (RR : forall r, getr (ms_regs msx) r = sv_denot Ev (sr_get (ss_regs ssx) r))
    by (intros r; exact (st_ok_restrict_reg tfibsegs (w_H W) Ev ssx msx r HS));
  let Ems := fresh "Ems" in
  pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) as Ems; rewrite Ems in HS; rewrite Ems; clear Ems;
  let pcv := eval vm_compute in (ss_pc ssx) in change (ss_pc ssx) with pcv in HS |- *;
  apply KC;
  [ exact HJ
  | lazymatch type of KEEP0 with context [o5p_sregs ?L] =>
      exact (o5_keep_ok E Ev (ss_regs ssx) L regs (ms_regs msx) HA ltac:(vm_compute; reflexivity) RR KEEP0) end
  | rewrite (RR 12%bv); let e := eval vm_compute in (sr_get (ss_regs ssx) 12%bv) in change (sr_get (ss_regs ssx) 12%bv) with e;
    reflexivity
  | rewrite (RR 13%bv); let e := eval vm_compute in (sr_get (ss_regs ssx) 13%bv) in change (sr_get (ss_regs ssx) 13%bv) with e;
    reflexivity
  | o5_byte HS W U33 E34 E35 33
  | o5_byte HS W U33 E34 E35 34
  | exact KE ] end.
Qed.
(* ================================ the 14 passes ================================ *)
Lemma o5_loop : forall n j (W : world tfibsegs) regs mem md STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc k
(Q : world tfibsegs -> config -> Prop) pos b F sp1,
(j + n = 14)%nat -> (1 <= n)%nat -> 0 <= b < 2 ^ 15 ->
ajournal tfibsegs B STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc W mem md k ->
In (3, pos) own -> In (3, pos) (frames Sc) -> frame_addr lyc 3 pos = F ->
getr regs 11 = w64 b -> getr regs 12 = w64 (2 + Z.of_nat j) -> getr regs 13 = w64 (2 ^ 64 - (2 + Z.of_nat j)) ->
getr regs 9 = w64 sp1 -> getr regs 21 = w64 SHADOW_OFF -> getr regs 26 = w64 1 ->
F mod 64 = 0 -> in_app F 512 -> F + 512 <= sp1 -> sp1 + 120 <= 2 ^ 47 -> F <= 0x7fffff800000 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (sp1 + 88) 8 (F + 34) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (sp1 + 96) 8 (F + 33) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (sp1 + 112) 8 (F + 32) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F + 33) 1 (fst (o5_acc b j)) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (F + 34) 1 (snd (o5_acc b j)) ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (F + 32) 3 -> amem_range (F + 32) 3 ->
(forall regs' mem' md',
  ajournal tfibsegs B STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc W mem' md' k ->
  (forall r, reg_in r O5_CLOB = false -> getr regs' r = getr regs r) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (F + 33) 1 (fst (codec_owe.owe_ring b)) ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (F + 34) 1 (snd (codec_owe.owe_ring b)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 33 <= a < F + 35) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 0x82fb0) mem' (seg_rom tfibsegs)) md') Q) ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 0x82b54) mem (seg_rom tfibsegs)) md) Q.
Proof.
induction n as [|n IH]; intros j W regs mem md STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc k Q pos b F sp1
  Hjn Hn1 Hb HJ Hown HinS EFA R11 R12 R13 R9 R21 R26 Hf64 Hfhi HFsp Hsp47 HFhi V88 V96 V112 V33 V34 Hra Ham KC;
  [lia|].
assert (HF0 : 4096 <= F) by (unfold in_app in Hfhi; lia).
destruct (o5_acc_range b j ltac:(lia)) as (P1 & P2).
pose proof (o5_acc_S b j) as AS.
apply (o5_pass (2 + Z.of_nat j) ltac:(lia) W regs mem md STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc k Q pos b
  (fst (o5_acc b j)) (snd (o5_acc b j)) F sp1 HJ Hown HinS EFA R11 R12 R13 R9 R21 R26 Hf64 ltac:(appn; lia) HFsp Hsp47 HFhi
  ltac:(lia) ltac:(lia) Hb V88 V96 V112 V33 V34 Hra Ham).
intros regs' mem' md' HJ' Hk' R12' R13' V33' V34' KE'.
rewrite <- surjective_pairing, <- AS in V33', V34'.
destruct n as [|n].
- replace (2 + Z.of_nat j =? 15) with true by (symmetry; apply Z.eqb_eq; lia).
  replace (S j) with 14%nat in V33', V34' by lia. rewrite o5_acc_14 in V33', V34'.
  exact (KC regs' mem' md' HJ' Hk' V33' V34' KE').
- replace (2 + Z.of_nat j =? 15) with false by (symmetry; apply Z.eqb_neq; lia).
  assert (KV : forall a (m : nat) v, (forall i, 0 <= i < Z.of_nat m -> ~ (F + 33 <= a + i < F + 35)) ->
    0 <= a -> a + Z.of_nat m <= 2 ^ 64 ->
    val_mem tfibsegs (mrestrict (w_H W) mem) a m v -> val_mem tfibsegs (mrestrict (w_H W) mem') a m v).
  { intros a m v Hz Ha Ham' Hv. apply (cw_val_mem_kept (w_H W) (w_H W) mem mem'); [|exact Hv].
    intros x Hx. apply KE'; [lia|]. replace x with (a + (x - a)) by lia. apply Hz. lia. }
  eapply (IH (S j) W regs' mem' md' STK sp0 FP ly Sx W0 mem0 md0 own lyc Sc k Q pos b F sp1);
  [ lia | lia | exact Hb | exact HJ' | exact Hown | exact HinS | exact EFA
  | rewrite (Hk' 11%bv eq_refl); exact R11
  | rewrite R12'; rewrite Nat2Z.inj_succ; f_equal; lia
  | rewrite R13'; rewrite Nat2Z.inj_succ; f_equal; lia
  | rewrite (Hk' 9%bv eq_refl); exact R9
  | rewrite (Hk' 21%bv eq_refl); exact R21
  | rewrite (Hk' 26%bv eq_refl); exact R26
  | exact Hf64 | exact Hfhi | exact HFsp | exact Hsp47 | exact HFhi
  | apply (KV _ 8%nat); [intros i Hi; cbn in Hi; lia | lia | cbn; lia | exact V88]
  | apply (KV _ 8%nat); [intros i Hi; cbn in Hi; lia | lia | cbn; lia | exact V96]
  | apply (KV _ 8%nat); [intros i Hi; cbn in Hi; lia | lia | cbn; lia | exact V112]
  | exact V33' | exact V34'
  | apply (range_addressable_agree (aview tfibsegs (w_H W) mem) (aview tfibsegs (w_H W) mem') SHADOW_OFF (F + 32) 3);
    [ intros x Hx; apply KE'; unfold shadow_of_addr, SHADOW_OFF;
      assert (x / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia); change (2 ^ 47 / 8) with 17592186044416 in *;
      assert (0 <= x / 8) by (apply Z.div_pos; lia); appn; lia
    | exact Hra ]
  | exact Ham
  | ].
  intros regs'' mem'' md'' HJ'' Hk'' V33'' V34'' KE''.
  apply (KC regs'' mem'' md'' HJ''); [| exact V33'' | exact V34'' |].
  + intros r Hr. rewrite (Hk'' r Hr). exact (Hk' r Hr).
  + intros a Ha Hz. rewrite (KE'' a Ha Hz). exact (KE' a Ha Hz).
Qed.
End p.
