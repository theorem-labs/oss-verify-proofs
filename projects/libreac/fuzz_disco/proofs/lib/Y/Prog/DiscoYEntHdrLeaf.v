(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 437 of its 472 lines of code are new or changed and 1243 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntProE.v, with its module names changed; 249 of its 305 lines of code are new or changed and 416 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC81 YC1g YC1h YC4b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntHdrLib DiscoYEntHdrSem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require FP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma hl_A_range : forall S, S - MFRAME - 31 <= 32 * ((S - MFRAME) / 32) <= S - MFRAME.
Proof.
intros S. pose proof (Z.div_mod (S - MFRAME) 32 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound (S - MFRAME) 32 ltac:(lia)) as Hmp. lia.
Qed.

Lemma hl_bvr : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range _ w) as Hr. unfold bv_modulus in Hr. exact Hr. Qed.

Lemma hl_has : forall cs o e, hd_has cs o e = true -> In (YP09.mkChunk o (CVal 8 e)) cs.
Proof.
intros cs o e H. unfold hd_has in H. apply existsb_exists in H as (c & Hc & Hm).
destruct c as [off cv]. cbn [YP09.c_off YP09.c_val] in Hm. apply andb_true_iff in Hm as [Ho Hm].
apply Z.eqb_eq in Ho. subst off.
destruct cv as [w e'|l|l|d s l]; try discriminate Hm.
apply andb_true_iff in Hm as [Hw He]. apply N.eqb_eq in Hw. apply sv_eqb_eq in He. subst. exact Hc.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma hl_reg : forall (fq : YK11.FPState) E ss ms (W : world SEGS) (r : bv 5) e v,
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) r = e -> sv_denot E e = v ->
  getr (ms_regs ms) r = v.
Proof.
intros fq E ss ms W r e v HS He Hv. rewrite (st_ok_pi_restrict_reg (w_H W) E ss ms r HS), He. exact Hv.
Qed.

Lemma hl_slot : forall (fq : YK11.FPState) E ss ms (W : world SEGS) r o e v A,
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> In r (ss_mem ss) ->
  YP09.r_base r = Some AT_A -> bv_unsigned (ew E AT_A) = A ->
  hd_has (YP09.r_chunks r) o e = true -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS (rd W (ms_mem ms)) (A + o) 8 v.
Proof.
intros fq E ss ms W r o e v A HS Hin Hb HA Hh He Hv.
destruct (In_nth_error _ _ Hin) as (j & Hj).
pose proof (st_ok_pi_region_nth E ss _ j r HS Hj) as HR.
destruct r as [rb lo hi wlo whi cs]. cbn [YP09.r_base YP09.r_chunks] in Hb, Hh. subst rb.
change 8%nat with (N.to_nat 8).
exact (field_of_region E _ AT_A A cs lo hi wlo whi o 8%N e v HR HA (hl_has cs o e Hh) He
  ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

Lemma hl_x : forall cx E h i n now regs (j : nat), (j < 38)%nat ->
  ew (d_env cx E (hd_vals cx h i n now regs)) (AT_X + j) = nth j (hd_vals cx h i n now regs) (Z_to_bv 64 0).
Proof. intros cx E h i n now regs j Hj. apply hd_env_x. unfold hd_vals. cbn [length]. exact Hj. Qed.

Lemma hl_e532 : forall cx E h i n now regs, ew (d_env cx E (hd_vals cx h i n now regs)) 532 = w64 i.
Proof. intros. exact (hl_x cx E h i n now regs 1 ltac:(lia)). Qed.
Lemma hl_e552 : forall cx E h i n now regs, ew (d_env cx E (hd_vals cx h i n now regs)) 552 = w64 h.
Proof. intros. exact (hl_x cx E h i n now regs 21 ltac:(lia)). Qed.
Lemma hl_e553 : forall cx E h i n now regs,
  ew (d_env cx E (hd_vals cx h i n now regs)) 553 = w64 (dnot (d_obj cx OG)).
Proof. intros. exact (hl_x cx E h i n now regs 22 ltac:(lia)). Qed.
Lemma hl_e554 : forall cx E h i n now regs,
  ew (d_env cx E (hd_vals cx h i n now regs)) 554 = w64 (dnot (d_obj cx OT)).
Proof. intros. exact (hl_x cx E h i n now regs 23 ltac:(lia)). Qed.
Lemma hl_e555 : forall cx E h i n now regs,
  ew (d_env cx E (hd_vals cx h i n now regs)) 555 = w64 (dnot (d_obj cx OO)).
Proof. intros. exact (hl_x cx E h i n now regs 24 ltac:(lia)). Qed.
Lemma hl_e556 : forall cx E h i n now regs,
  ew (d_env cx E (hd_vals cx h i n now regs)) 556 = w64 (dnot (d_obj cx OUSED)).
Proof. intros. exact (hl_x cx E h i n now regs 25 ltac:(lia)). Qed.
Lemma hl_e563 : forall cx E h i n now regs,
  ew (d_env cx E (hd_vals cx h i n now regs)) 563 = w64 (yh_bv cx n 0).
Proof. intros. exact (hl_x cx E h i n now regs 32 ltac:(lia)). Qed.

Lemma hl_dnot : forall FB o, 0 <= FB -> FB + 4096 <= 2 ^ 47 -> 0 <= dobj_off o <= 4096 ->
  0 <= dnot (FB + dobj_off o) < 2 ^ 64.
Proof. intros FB o H1 H2 H3. unfold dnot. lia. Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MT_TRIV : MT = ameter_triv.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis LAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BKEEP : d_body_keep_stmt B.

Lemma hl_at : forall (fq : YK11.FPState) (cx : dcx) ly3 S3 (W : world SEGS) md k acc (E : env) (ss : sstate)
  (ms : machine_state) (pc kmax accmax : Z)
  (P : bvmap 5 word -> alayout -> astate -> world SEGS -> (word -> option byte) -> Model -> Prop),
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= kmax -> st_nev S3 <= st_nev (c_S cx) + kmax ->
  mo_le MT (c_S cx) S3 acc -> acc <= accmax ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
  P (ms_regs ms) ly3 S3 W (ms_mem ms) md ->
  d_at B MT XM_LIB RLO RHI tfib_K cx pc kmax accmax P W (mkCfg ms md).
Proof.
intros fq cx ly3 S3 W md k acc E ss ms pc kmax accmax P FR HB HJ HFR Hk Hev Hmo Hacc HS Hrv Hpc HP.
pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv) as Hms.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md, k, acc.
split; [unfold cfg_at; rewrite Hms at 1; rewrite Hpc; reflexivity|].
split; [exact FR|]. split; [exact HB|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|]. split; [exact Hev|].
split; [exact Hmo|]. split; [exact Hacc | exact HP].
Qed.

Lemma hd_leaf : forall (arm : bool) (fq : YK11.FPState) (cx : dcx) (h i n now : Z) ly3 S3 (W : world SEGS) mem3 md3 k acc
  (regs : bvmap 5 word) (E0 : env) (ss : sstate) (ms : machine_state) (md : Model) (n' : Z) (e14 e25 : sv),
  hd_ctx B MT XM_LIB RLO RHI tfib_K cx h i n now ly3 S3 W mem3 md3 k acc regs E0 -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  hd_keep W mem3 (ms_mem ms) (d_A cx) -> hd_pres W mem3 (ms_mem ms) ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E0 (hd_vals cx h i n now regs)) ss (restrict (w_H W) ms) ->
  ss_resv ss = None -> ss_pc ss = (if arm then ARM3_OFF else REC_OFF) -> hd_leafb ss = true ->
  sr_get (ss_regs ss) 14 = e14 -> sv_denot (d_env cx E0 (hd_vals cx h i n now regs)) e14 = w64 n' ->
  sr_get (ss_regs ss) 25 = e25 -> sv_denot (d_env cx E0 (hd_vals cx h i n now regs)) e25 = w64 (d_cur cx n') ->
  0 <= n' <= n ->
  (if arm then yh_bv cx n 0 mod 4 = 3 else yh_bv cx n 0 mod 4 <> 3) ->
  hd_post B MT XM_LIB RLO RHI tfib_K cx h i W (mkCfg ms md).
Proof.
intros arm fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 ss ms md n' e14 e25
  HC FR HJ HK HP HS Hrv Hpc Hlb Hg14 Hd14 Hg25 Hd25 Rn' Harm.
destruct HC as (HB & _ & HFR & Hk & Hev & Hmo & Hacc & Ri & Rn & _ & _ & HBD & HE0 & _ & _).
pose proof asan_consts as (C1 & _).
pose proof HB as ((HPRE & _) & _).
pose proof HPRE as (_ & _ & _ & Hgp0 & Htp0 & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
change (spZ (c_regs cx)) with (d_S cx) in Hslo, Hshi.
pose proof (hl_A_range (d_S cx)) as HAr.
change (32 * ((d_S cx - MFRAME) / 32)) with (d_A cx) in HAr.
assert (RA : 0 <= d_A cx < 2 ^ 64) by (clear - C1 Hceil Hslo Hshi H47 HAr; unfold MFRAME, LLVMF_STK in *; lia).
assert (Hlo : d_S cx - LLVMF_STK <= d_A cx) by (clear - HAr; unfold MFRAME, LLVMF_STK in *; lia).
assert (Hhi : d_A cx + 472 <= d_S cx) by (clear - HAr; unfold MFRAME, LLVMF_STK in *; lia).
pose proof HBD as (T & G & Lk & H & _ & _ & _ & _ & _ & _ & _ & HGEO & _).
destruct HGEO as (G1 & G2 & G3 & G4 & _).
change (fs_frame_bytes DFRAME_CLASS) with 4096 in G2.
assert (Rh : 0 <= h /\ h + 440 < 2 ^ 64) by (clear - G3 G4 C1; unfold HUNT_SIZE in G4; lia).
assert (RFB : 0 <= d_FB cx /\ d_FB cx + 4096 <= 2 ^ 47) by (clear - G1 G2 C1; lia).
pose proof (hd_E_env cx E0 (hd_vals cx h i n now regs) HE0) as HEd.
pose proof (hd_env_fl cx E0 (hd_vals cx h i n now regs)) as Efl.
pose proof (hl_e532 cx E0 h i n now regs) as E532.
pose proof (hl_e552 cx E0 h i n now regs) as E552.
pose proof (hl_e553 cx E0 h i n now regs) as E553.
pose proof (hl_e554 cx E0 h i n now regs) as E554.
pose proof (hl_e555 cx E0 h i n now regs) as E555.
pose proof (hl_e556 cx E0 h i n now regs) as E556.
pose proof (hl_e563 cx E0 h i n now regs) as E563.
set (Ed := d_env cx E0 (hd_vals cx h i n now regs)) in *.
assert (Rop : 0 <= yh_bv cx n 0 < 256) by (unfold yh_bv; apply yh_bv_range).
remember (yh_bv cx n 0) as op eqn:Eop.
pose proof HEd as (EE & E32 & _ & E60 & _ & E529).
assert (HA60 : bv_unsigned (ew Ed AT_A) = d_A cx) by (rewrite E60; unfold w64; apply unsigned_lit_small; exact RA).
assert (D60 : sv_denot Ed (SOff 60 0) = w64 (d_A cx)) by (rewrite sv_denot_SOff0; exact E60).
assert (D2 : sv_denot Ed (SOff 2 0) = w64 (d_S cx))
  by (rewrite sv_denot_SOff0, (EE 2%nat 2%bv eq_refl); unfold w64, d_S, spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (D3 : sv_denot Ed (SOff 3 0) = w64 (as_gp B)) by (rewrite sv_denot_SOff0, (EE 3%nat 3%bv eq_refl); exact Hgp0).
assert (D4 : sv_denot Ed (SOff 4 0) = w64 (as_tp B)) by (rewrite sv_denot_SOff0, (EE 4%nat 4%bv eq_refl); exact Htp0).
assert (D32 : sv_denot Ed (SOff 32 0) = w64 SHADOW_OFF) by (rewrite sv_denot_SOff0; exact E32).
assert (D529 : sv_denot Ed (SOff 529 0) = w64 (shadow_addr (d_FB cx))) by (rewrite sv_denot_SOff0; exact E529).
assert (D532 : sv_denot Ed (SOff 532 0) = w64 i) by (rewrite sv_denot_SOff0; exact E532).
assert (D16 : sv_denot Ed (SExt true 8 (SOff 563 0)) = w64 (if op <? 128 then op else op - 256))
  by exact (yh_sext8 Ed 563 op E563 Rop).
assert (D23 : sv_denot Ed (SAlu ALU_AND (SExt true 8 (SOff 563 0)) (SLit 3)) = w64 (op mod 4))
  by (rewrite denot_lit_U, (yh_and3 Ed 563 op E563 Rop); reflexivity).
unfold hd_leafb in Hlb. apply andb_true_iff in Hlb as [Hlb HFG]. apply andb_true_iff in Hlb as [HLC HSL].
unfold hd_fregs in HFG. cbn [forallb fst snd] in HFG.
apply andb_true_iff in HFG as [F2 HFG]. apply andb_true_iff in HFG as [F3 HFG].
apply andb_true_iff in HFG as [F4 HFG]. apply andb_true_iff in HFG as [F8 HFG].
apply andb_true_iff in HFG as [F9 HFG]. apply andb_true_iff in HFG as [F18 HFG].
apply andb_true_iff in HFG as [F19 HFG]. apply andb_true_iff in HFG as [F20 HFG].
apply andb_true_iff in HFG as [F22 HFG]. apply andb_true_iff in HFG as [F27 HFG].
apply andb_true_iff in HFG as [F21 HFG]. apply andb_true_iff in HFG as [F16 HFG].
apply andb_true_iff in HFG as [F23 HFG]. apply andb_true_iff in HFG as [F15 _].
apply sv_eqb_eq in F2. apply sv_eqb_eq in F3. apply sv_eqb_eq in F4. apply sv_eqb_eq in F8.
apply sv_eqb_eq in F9. apply sv_eqb_eq in F18. apply sv_eqb_eq in F19. apply sv_eqb_eq in F20.
apply sv_eqb_eq in F22. apply sv_eqb_eq in F27. apply sv_eqb_eq in F21. apply sv_eqb_eq in F16.
apply sv_eqb_eq in F23. apply sv_eqb_eq in F15.
assert (R2 : getr (ms_regs ms) 2 = w64 (d_A cx)) by exact (hl_reg fq Ed ss ms W 2%bv _ _ HS F2 D60).
assert (R3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by exact (hl_reg fq Ed ss ms W 3%bv _ _ HS F3 D3).
assert (R4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by exact (hl_reg fq Ed ss ms W 4%bv _ _ HS F4 D4).
assert (R8 : getr (ms_regs ms) 8 = w64 (d_S cx)) by exact (hl_reg fq Ed ss ms W 8%bv _ _ HS F8 D2).
assert (R9 : getr (ms_regs ms) 9 = w64 (d_A cx)) by exact (hl_reg fq Ed ss ms W 9%bv _ _ HS F9 D60).
assert (R18 : getr (ms_regs ms) 18 = w64 WS_MASK) by exact (hl_reg fq Ed ss ms W 18%bv _ _ HS F18 eq_refl).
assert (R19 : getr (ms_regs ms) 19 = w64 SHADOW_OFF) by exact (hl_reg fq Ed ss ms W 19%bv _ _ HS F19 D32).
assert (R20 : getr (ms_regs ms) 20 = w64 32) by exact (hl_reg fq Ed ss ms W 20%bv _ _ HS F20 eq_refl).
assert (R22 : getr (ms_regs ms) 22 = w64 1) by exact (hl_reg fq Ed ss ms W 22%bv _ _ HS F22 eq_refl).
assert (R27 : getr (ms_regs ms) 27 = w64 (shadow_addr (d_FB cx))) by exact (hl_reg fq Ed ss ms W 27%bv _ _ HS F27 D529).
assert (R21 : getr (ms_regs ms) 21 = w64 i) by exact (hl_reg fq Ed ss ms W 21%bv _ _ HS F21 D532).
assert (R16 : getr (ms_regs ms) 16 = w64 (if op <? 128 then op else op - 256))
  by exact (hl_reg fq Ed ss ms W 16%bv _ _ HS F16 D16).
assert (R23 : getr (ms_regs ms) 23 = w64 (op mod 4)) by exact (hl_reg fq Ed ss ms W 23%bv _ _ HS F23 D23).
assert (R15 : getr (ms_regs ms) 15 = w64 (STALE_NS + 1)) by exact (hl_reg fq Ed ss ms W 15%bv _ _ HS F15 eq_refl).
assert (R14 : getr (ms_regs ms) 14 = w64 n') by exact (hl_reg fq Ed ss ms W 14%bv _ _ HS Hg14 Hd14).
assert (R25 : getr (ms_regs ms) 25 = w64 (d_cur cx n')) by exact (hl_reg fq Ed ss ms W 25%bv _ _ HS Hg25 Hd25).
assert (R26 : getr (ms_regs ms) 26 = w64 (bv_unsigned (getr (ms_regs ms) 26)))
  by (unfold w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (HRL : d_rL B cx (ms_regs ms)).
{ unfold d_rL. split; [unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; exact RA|].
  exact (conj R3 (conj R4 (conj R8 (conj R9 (conj R19 (conj R18 (conj R20 R27))))))). }
unfold hd_slotb in HSL. apply existsb_exists in HSL as (r & Hin & Hr).
apply andb_true_iff in Hr as [Hrb Hall].
assert (Eb : YP09.r_base r = Some AT_A).
{ clear - Hrb. destruct (YP09.r_base r) as [b|]; [|discriminate Hrb].
  cbn [obase_eqb] in Hrb. apply Nat.eqb_eq in Hrb. subst b. reflexivity. }
unfold hd_need in Hall. cbn [forallb fst snd] in Hall.
apply andb_true_iff in Hall as [S184 Hall]. apply andb_true_iff in Hall as [S120 Hall].
apply andb_true_iff in Hall as [S136 Hall]. apply andb_true_iff in Hall as [S376 Hall].
apply andb_true_iff in Hall as [S280 Hall]. apply andb_true_iff in Hall as [S232 Hall].
apply andb_true_iff in Hall as [S264 Hall]. apply andb_true_iff in Hall as [S208 Hall].
apply andb_true_iff in Hall as [S320 Hall]. apply andb_true_iff in Hall as [S352 Hall].
apply andb_true_iff in Hall as [S360 _].
assert (V184 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 184) 8 h).
{ apply (hl_slot fq Ed ss ms W r 184 (SOff 552 0) h (d_A cx) HS Hin Eb HA60 S184); [|clear - Rh; lia].
  rewrite sv_denot_SOff0. exact E552. }
assert (V120 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 120) 8 (h + 440)).
{ apply (hl_slot fq Ed ss ms W r 120 (SOff 552 440) (h + 440) (d_A cx) HS Hin Eb HA60 S120); [|clear - Rh; lia].
  cbn [sv_denot]. rewrite E552. unfold w64. rewrite unsigned_lit_small by (clear - Rh; lia). reflexivity. }
assert (V136 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 136) 8 0).
{ apply (hl_slot fq Ed ss ms W r 136 (SLit 0) 0 (d_A cx) HS Hin Eb HA60 S136); [reflexivity | lia]. }
assert (V376 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 376) 8 (dnot (d_obj cx OG))).
{ apply (hl_slot fq Ed ss ms W r 376 (SOff 553 0) (dnot (d_obj cx OG)) (d_A cx) HS Hin Eb HA60 S376).
  - rewrite sv_denot_SOff0. exact E553.
  - unfold d_obj. apply hl_dnot; [exact (proj1 RFB) | exact (proj2 RFB) | cbn [dobj_off]; lia]. }
assert (V280 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 280) 8 (dnot (d_obj cx OT))).
{ apply (hl_slot fq Ed ss ms W r 280 (SOff 554 0) (dnot (d_obj cx OT)) (d_A cx) HS Hin Eb HA60 S280).
  - rewrite sv_denot_SOff0. exact E554.
  - unfold d_obj. apply hl_dnot; [exact (proj1 RFB) | exact (proj2 RFB) | cbn [dobj_off]; lia]. }
assert (V232 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 232) 8 (dnot (d_obj cx OO))).
{ apply (hl_slot fq Ed ss ms W r 232 (SOff 555 0) (dnot (d_obj cx OO)) (d_A cx) HS Hin Eb HA60 S232).
  - rewrite sv_denot_SOff0. exact E555.
  - unfold d_obj. apply hl_dnot; [exact (proj1 RFB) | exact (proj2 RFB) | cbn [dobj_off]; lia]. }
assert (V264 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 264) 8 (dnot (d_obj cx OUSED))).
{ apply (hl_slot fq Ed ss ms W r 264 (SOff 556 0) (dnot (d_obj cx OUSED)) (d_A cx) HS Hin Eb HA60 S264).
  - rewrite sv_denot_SOff0. exact E556.
  - unfold d_obj. apply hl_dnot; [exact (proj1 RFB) | exact (proj2 RFB) | cbn [dobj_off]; lia]. }
assert (V208 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 208) 8 i).
{ apply (hl_slot fq Ed ss ms W r 208 (SOff 532 0) i (d_A cx) HS Hin Eb HA60 S208).
  - rewrite sv_denot_SOff0. exact E532.
  - clear - Ri. unfold MAX_OPS in Ri. lia. }
assert (V320 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 320) 8 (bv_unsigned (getr (ms_regs ms) 26))).
{ apply (hl_slot fq Ed ss ms W r 320 (sr_get (ss_regs ss) 26) (bv_unsigned (getr (ms_regs ms) 26)) (d_A cx)
    HS Hin Eb HA60 S320).
  - rewrite <- (st_ok_pi_restrict_reg (w_H W) Ed ss ms 26%bv HS). symmetry. apply Z_to_bv_bv_unsigned.
  - exact (hl_bvr (getr (ms_regs ms) 26)). }
assert (V352 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 352) 8 (if op <? 128 then op else op - 256)).
{ apply (yh_val_mem_mod SEGS (rd W (ms_mem ms)) (d_A cx + 352)
    ((if op <? 128 then op else op - 256) mod 2 ^ 64) (if op <? 128 then op else op - 256)).
  - apply Z.mod_mod. lia.
  - apply (hl_slot fq Ed ss ms W r 352 (SExt true 8 (SOff 563 0)) ((if op <? 128 then op else op - 256) mod 2 ^ 64)
      (d_A cx) HS Hin Eb HA60 S352).
    + rewrite D16. unfold w64. apply Z_to_bv64_eq_mod. rewrite Z.mod_mod by lia. reflexivity.
    + apply Z.mod_pos_bound. lia. }
assert (V360 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 360) 8 op).
{ apply (hl_slot fq Ed ss ms W r 360 (SAlu ALU_AND (SExt true 8 (SOff 563 0)) (SLit 255)) op (d_A cx)
    HS Hin Eb HA60 S360).
  - rewrite denot_lit_U, (yh_and255 Ed 563 op E563 Rop). reflexivity.
  - clear - Rop. lia. }
destruct (LAND LAWS FFL fq cx h dsh_loop ly3 S3 W md k Ed ss ms (conj HB (conj HJ HFR)) HEd Efl HS HLC
  V184 V120 V136 V376 V280 V232 V264) as [HFRAME HSHADOW].
assert (HBD' : d_body B cx h n' [] dsh_loop ly3 S3 W (ms_mem ms))
  by exact (BKEEP cx h n n' dsh_loop ly3 S3 W mem3 (ms_mem ms) (d_A cx) (d_A cx + 472) HBD Hlo Hhi HK
    (fun a _ Ha => HP a Ha) HFRAME HSHADOW Rn').
unfold hd_post. right. exists n', (bv_unsigned (getr (ms_regs ms) 26)), op.
destruct arm; [left | right]; (split; [exact Harm|]).
- unfold arm3_in.
  apply (hl_at fq cx ly3 S3 W md k acc Ed ss ms ARM3_OFF (EV_HEAD i) (ACC_HEAD MT i) _
    FR HB HJ HFR Hk Hev Hmo Hacc HS Hrv Hpc).
  cbv beta.
  assert (HRA : d_rA3 B cx n' (bv_unsigned (getr (ms_regs ms) 26)) op (ms_regs ms))
    by exact (conj HRL (conj R22 (conj R14 (conj R26 (conj R25 (conj R16 (conj R23 R15))))))).
  exact (conj Ri (conj (proj1 Rn') (conj (hl_bvr _) (conj Rop (conj Harm (conj HRA
    (conj (conj V208 V320) (conj (conj V360 V352) HBD')))))))).
- unfold rec_in.
  apply (hl_at fq cx ly3 S3 W md k acc Ed ss ms REC_OFF (EV_HEAD i) (ACC_HEAD MT i) _
    FR HB HJ HFR Hk Hev Hmo Hacc HS Hrv Hpc).
  cbv beta.
  assert (HRD : d_rD B cx i n' (bv_unsigned (getr (ms_regs ms) 26)) op (ms_regs ms))
    by exact (conj HRL (conj R22 (conj R21 (conj R14 (conj R26 (conj R25 (conj R16 R23))))))).
  exact (conj Ri (conj (proj1 Rn') (conj (hl_bvr _) (conj Rop (conj Harm (conj HRD
    (conj (conj V208 V320) (conj (conj V360 V352) HBD')))))))).
Qed.
End h.
End f.
End d.
