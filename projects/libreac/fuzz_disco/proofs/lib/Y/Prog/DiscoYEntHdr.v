(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 733 of its 792 lines of code are new or changed and 1219 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntR27.v; 657 of its 734 lines of code are new or changed and 715 lines of the source are left out. *)
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
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntHdrLib DiscoYEntHdrSem DiscoYEntHdrLeaf DiscoYEntHdrSeat.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require FP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition hd_ssD1 : sstate := Eval vm_compute in
  hd_run (add_cond (hd_run (hd_addb 0 563 hd_ssJ1)) (mkAC BC_EQ (SOff 531 0) (SLit 1))).
Definition hd_ssD2 : sstate := Eval vm_compute in
  hd_run (add_cond (hd_run (hd_addb 1 564 hd_ssJ2)) (mkAC BC_EQ (SOff 531 0) (SLit 2))).
Definition hd_ssD3 : sstate := Eval vm_compute in hd_run (hd_addb 2 565 hd_ssJ3).
Definition hd_ssC1 : sstate := Eval vm_compute in hd_run (add_cond hd_ss0 (mkAC BC_NE (SOff 531 0) (SLit 0))).
Definition hd_ssC2 : sstate := Eval vm_compute in
  hd_run (add_cond (hd_run (hd_addb 0 563 hd_ssJ1)) (mkAC BC_NE (SOff 531 0) (SLit 1))).
Definition hd_ssC3 : sstate := Eval vm_compute in
  hd_run (add_cond (hd_run (hd_addb 1 564 hd_ssJ2)) (mkAC BC_NE (SOff 531 0) (SLit 2))).

Lemma yh_bvne : forall r : bv 5, bv_eqb r 0 = false -> r <> 0%bv.
Proof. intros r H Hx. rewrite Hx in H. vm_compute in H. discriminate. Qed.

Ltac hd_srget := match goal with |- context [sr_get ?sr ?rr] =>
  let v := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with v end.

Lemma yh_A_range : forall S, 0 <= S - MFRAME ->
  S - MFRAME - 31 <= 32 * ((S - MFRAME) / 32) <= S - MFRAME.
Proof.
intros S Hs. pose proof (Z.div_mod (S - MFRAME) 32 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound (S - MFRAME) 32 ltac:(lia)) as Hmp. lia.
Qed.

Lemma yh_off_den : forall E (c : nat) x j, ew E c = w64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + j < 2 ^ 64 ->
  sv_denot E (SOff c j) = Z_to_bv 64 (x + j).
Proof. intros E c x j Hc Hx Hxj. rewrite denot_lit_U. f_equal. exact (U_atom_off E c x j Hc Hx Hxj). Qed.

Lemma yh_caddr_den : forall E (c : nat) x j, ew E c = w64 x -> 0 <= x -> 0 <= j -> x + j < 2 ^ 47 ->
  ew E 32 = w64 SHADOW_OFF ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff c j) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (yh_caddr (x + j)).
Proof.
intros E c x j Hc Hx Hj Hxj H32. unfold w64 in Hc, H32. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3, !U_SOff, Hc, H32, Z.add_0_r.
rewrite (unsigned_lit_small x) by lia. rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
rewrite (zcanon_id (x + j)) by (unfold M64; lia). rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
assert (Hd : 0 <= (x + j) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
unfold yh_caddr. rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). lia.
Qed.

Lemma yh_cellU : forall E (v : nat) s, ew E v = w64 s -> 0 <= s < 8 -> U E (SExt true 8 (SOff v 0)) = s.
Proof.
intros E v s Hv Hs. unfold U. rewrite (yh_sext8 E v s Hv ltac:(lia)).
destruct (Z.ltb_spec s 128); [|lia]. apply unsigned_lit_small. lia.
Qed.

Lemma yh_and7 : forall E (c : nat) x j, ew E c = w64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + j < 2 ^ 64 ->
  U E (SAlu ALU_AND (SOff c j) (SLit 7)) = (x + j) mod 8.
Proof.
intros E c x j Hc Hx Hxj. rewrite U_and_lit by lia. rewrite (U_atom_off E c x j Hc Hx Hxj).
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma yh_bge : forall E (c v : nat) x j s, ew E c = w64 x -> ew E v = w64 s -> 0 <= x < 2 ^ 64 ->
  0 <= x + j < 2 ^ 64 -> 0 <= s < 8 ->
  branch_taken BC_GE (sv_denot E (SAlu ALU_AND (SOff c j) (SLit 7))) (sv_denot E (SExt true 8 (SOff v 0))) =
  negb ((x + j) mod 8 <? s).
Proof.
intros E c v x j s Hc Hv Hx Hxj Hs. cbn [branch_taken].
rewrite (denot_lit_U E (SAlu _ _ _)), (denot_lit_U E (SExt _ _ _)).
rewrite (yh_and7 E c x j Hc Hx Hxj), (yh_cellU E v s Hv Hs).
rewrite bv_lts_small by (pose proof (Z.mod_pos_bound (x + j) 8 ltac:(lia)); lia). reflexivity.
Qed.

Lemma yh_bltu1 : forall E (c : nat) x j, ew E c = w64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + j < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SLit 1)) (sv_denot E (SOff c j)) = (1 <? x + j).
Proof. intros E c x j Hc Hx Hxj. rewrite branch_ltu_U, U_lit by lia. rewrite (U_atom_off E c x j Hc Hx Hxj). reflexivity. Qed.

Lemma yh_bne_lit : forall E (c : nat) x z, ew E c = w64 x -> 0 <= x < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff c 0)) (sv_denot E (SLit z)) = negb (x =? z).
Proof. intros E c x z Hc Hx Hz. rewrite branch_ne_U, U_lit by lia. rewrite (U_atom E c x Hc Hx). reflexivity. Qed.

Lemma yh_beq_cell : forall E (v : nat) s, ew E v = w64 s -> 0 <= s < 8 ->
  branch_taken BC_EQ (sv_denot E (SExt true 8 (SOff v 0))) (sv_denot E (SLit 0)) = (s =? 0).
Proof. intros E v s Hv Hs. rewrite branch_eq_U, U_lit by lia. rewrite (yh_cellU E v s Hv Hs). reflexivity. Qed.

Lemma yh_bne_op : forall E (q : nat) op, ew E q = w64 op -> 0 <= op < 256 ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SExt true 8 (SOff q 0)) (SLit 3))) (sv_denot E (SLit 3)) =
  negb (op mod 4 =? 3).
Proof. intros E q op Hq Hop. rewrite branch_ne_U, U_lit by lia. rewrite (yh_and3 E q op Hq Hop). reflexivity. Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma yh_in_aview : forall (W : world SEGS) m p (pl : list byte) idx,
  garr8 SEGS (rd W m) p (map (fun b : byte => bv_unsigned b) pl) -> 0 <= idx < Z.of_nat (length pl) ->
  aview SEGS (w_H W) m (p + idx) = Some (nth (Z.to_nat idx) (map (fun b : byte => bv_unsigned b) pl) 0).
Proof.
intros W m p pl idx G Hi. unfold aview.
replace (p + idx) with (p + Z.of_nat (Z.to_nat idx)) by lia.
rewrite (garr8_mbyte SEGS _ _ _ (Z.to_nat idx) G ltac:(rewrite length_map; lia)). cbn [option_map]. f_equal.
pose proof (yh_bv_range pl (Z.to_nat idx)) as Hr. rewrite Z_to_bv_unsigned. apply Z.mod_small. exact Hr.
Qed.

Lemma hd_awr_ro : forall E rs STK sp0 FP bl0 blc ly own,
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
intros E rs STK sp0 FP bl0 blc ly own Hb. induction rs as [|r rs IH]; [apply awr_ok_nil|].
cbn [forallb] in Hb. apply andb_true_iff in Hb as [Hr Hrs].
apply awr_ok_cons_ro; [apply Z.leb_le in Hr; exact Hr | exact (IH Hrs)].
Qed.

Lemma hd_zone_nb : forall E cur nb nb' p cn S A FB, hd_zone E cur nb p cn S A FB -> 0 <= nb' -> cur + nb' <= p + cn ->
  hd_zone E cur nb' p cn S A FB.
Proof.
intros E cur nb nb' p cn S A FB (Z0 & Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & _ & _ & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & Z17 & Z18 & Z19 & Z20) H1 H2.
unfold hd_zone. tauto.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MT_TRIV : MT = ameter_triv.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis LAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BKEEP : d_body_keep_stmt B.
Lemma hd_wfacts : forall cx h i n now ly3 S3 (W : world SEGS) mem3 md3 k acc regs E0,
  hd_ctx B MT XM_LIB RLO RHI tfib_K cx h i n now ly3 S3 W mem3 md3 k acc regs E0 -> 0 < n ->
  img_env VAL A_LIM (d_env cx E0 (hd_vals cx h i n now regs)) /\
  bv_unsigned (ew (d_env cx E0 (hd_vals cx h i n now regs)) AT_A) = d_A cx /\
  ew (d_env cx E0 (hd_vals cx h i n now regs)) AT_A = w64 (d_A cx) /\
  0 <= d_A cx < 2 ^ 64 /\ - LLVMF_STK <= d_A cx - d_S cx /\ d_A cx - d_S cx + 472 <= 0 /\
  ew (d_env cx E0 (hd_vals cx h i n now regs)) 32 = w64 SHADOW_OFF /\
  hd_zone (d_env cx E0 (hd_vals cx h i n now regs)) (d_cur cx n) 0 (c_p cx) (c_n cx) (d_S cx) (d_A cx) (d_FB cx) /\
  d_cur cx n + n = c_p cx + c_n cx /\ c_p cx mod 8 = 0 /\
  AR SEGS B ly3 S3 W mem3 md3 /\ In (c_p cx, c_n cx) (ablocks B ly3 S3) /\
  garr8 SEGS (rd W mem3) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  Z.of_nat (length (c_pl cx)) = c_n cx.
Proof.
intros cx h i n now ly3 S3 W mem3 md3 k acc regs E0 HC Hn.
destruct HC as (HB & HJ & HFR & _ & _ & _ & _ & _ & Rn & _ & _ & HBD & HE & _ & _).
pose proof asan_consts as (C1 & _).
pose proof HB as ((HPRE & _ & _ & _ & Hpn & _) & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
change (spZ (c_regs cx)) with (d_S cx) in Hslo, Hshi.
assert (HSb : alloc_ceiling + LLVMF_STK <= d_S cx /\ d_S cx <= 2 ^ 47)
  by (clear - C1 Hceil Hslo Hshi H47; unfold LLVMF_STK in *; lia).
pose proof HJ as (HAR3 & Hly3 & _).
pose proof HBD as (T & G & Lk & H & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HGEO & _).
destruct HINP as (Hn' & Harr & Hoff).
destruct Hpn as [(Hn0 & _) | (Hcn' & Hin0)]; [rewrite Hn0 in Hn'; lia|].
assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)).
{ destruct HBLK as (Hperm & _). apply (Permutation_in _ (Permutation_sym Hperm)).
  apply in_or_app. right. right. exact Hin0. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin0) as (H16 & H4096 & Hpc & Hpapp & _).
assert (Hrq : req_size (c_n cx) = c_n cx)
  by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); [lia | reflexivity]).
rewrite Hrq in Hpc, Hpapp.
assert (Hpimg : off_img (c_p cx) (c_n cx)) by (apply Hoff; lia).
assert (Hfin : In (DFRAME_CLASS, c_fpos cx) (frames S3)) by (rewrite HFR; left; reflexivity).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 Hly3) as (_ & Efa & _).
destruct (frames_bounds _ _ LAWS _ _ _ _ _ DFRAME_CLASS (c_fpos cx) HAR3 Hfin) as (HF0 & HFc & HFia).
destruct (al_frames _ _ LAWS _ _ _ _ _ DFRAME_CLASS (c_fpos cx) HAR3 Hfin) as (Hal & _).
rewrite Efa in HF0, HFc, HFia, Hal.
change (frame_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) with (d_FB cx) in *.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in *.
pose proof (hd_E_env cx E0 (hd_vals cx h i n now regs) HE) as (EE & E32 & HEI & E60 & EF & ESH).
pose proof (yh_A_range (d_S cx) ltac:(clear - C1 HSb; unfold MFRAME, LLVMF_STK in *; lia)) as HAr.
change (32 * ((d_S cx - MFRAME) / 32)) with (d_A cx) in HAr.
assert (RA : 0 <= d_A cx < 2 ^ 64) by (clear - C1 HSb HAr; unfold MFRAME, LLVMF_STK in *; lia).
assert (A533 : ew (d_env cx E0 (hd_vals cx h i n now regs)) 533 = w64 (d_cur cx n))
  by exact (hd_env_x cx E0 (hd_vals cx h i n now regs) 2 ltac:(unfold hd_vals; cbn [length]; lia)).
assert (E2 : ew (d_env cx E0 (hd_vals cx h i n now regs)) AT_STK = w64 (d_S cx)).
{ change AT_STK with 2%nat. rewrite (EE 2%nat 2%bv eq_refl). unfold w64, d_S, spZ. symmetry. apply Z_to_bv_bv_unsigned. }
destruct HGEO as (HG1 & HG2 & _ & _ & _ & _ & _ & HG8).
destruct (HG8 ltac:(lia)) as (_ & _ & HGF & _).
change (fs_frame_bytes DFRAME_CLASS) with 4096 in HG2, HGF.
split; [exact HEI|].
split; [rewrite E60; unfold w64; apply unsigned_lit_small; exact RA|].
split; [exact E60|]. split; [exact RA|].
split; [clear - HAr; unfold MFRAME, LLVMF_STK in *; lia|]. split; [clear - HAr; unfold MFRAME in *; lia|].
split; [exact E32|].
split.
{ unfold hd_zone. split; [exact A533|]. split; [exact E2|]. split; [exact E60|]. split; [exact EF|].
  split; [rewrite ESH; unfold shadow_addr; reflexivity|]. split; [exact HEI|].
  unfold in_app, ASAN_CEIL in Hpapp, HFia. unfold d_cur.
  clear - C1 HSb HAr H4096 Hpc Hpapp Hpimg HF0 HFc HFia Hal HGF Hn Hn'.
  unfold off_img, MFRAME, LLVMF_STK in *.
  repeat match goal with |- _ /\ _ => split end; lia. }
split; [unfold d_cur; lia|].
split; [clear - H16; lia|].
split; [exact HAR3|]. split; [exact Hin3|]. split; [exact Harr|].
destruct HB as ((_ & _ & _ & _ & _ & Hlen & _) & _). lia.
Qed.

Ltac hd_awr_tac cx UA HA1 HA2 :=
  lazymatch goal with |- awr_ok ?E ?rs ?STK ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    exact (hd_awr E rs STK sp0 fp b0 bc ly own (d_A cx) ltac:(vm_compute; reflexivity) UA HA1 HA2) end.

Ltac hd_upd EA RA :=
  lazymatch goal with
  | HFr : frame_of ?E ?rs (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _,
    HK : hd_keep _ _ _ _, HP : hd_pres _ _ _ |- _ =>
    let HK2 := fresh "HK" in let HP2 := fresh "HP" in
    pose proof (hd_keep_step E rs _ _ _ _ _ (hd_wr_ok E rs _ ltac:(vm_compute; reflexivity) EA RA) HFr HK) as HK2;
    pose proof (hd_pres_step _ _ _ _ HG HP) as HP2;
    clear HK HP HFr HG; rename HK2 into HK; rename HP2 into HP
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.

Ltac hd_leaf_tac arm fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 HC n' e14 e25 D14 D25 Rn' Harm :=
  lazymatch goal with
  | HS : st_ok_pi _ _ _ ?ss (restrict _ ?msx), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HK : hd_keep _ _ _ _, HP : hd_pres _ _ _, FRh : lib.Lib.FP.frm0 _ |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
    apply SRr_ret;
    exact (hd_leaf B MT XM_LIB RLO RHI tfib_K LAWS FFL LAND BKEEP arm fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0
      ss msx mdx n' e14 e25 HC FRh HJ HK HP HS eq_refl eq_refl
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) D14 ltac:(vm_compute; reflexivity) D25 Rn' Harm)
  end.

Ltac hd_dgo fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 HC UA HA1 HA2 EA RA n' e14 e25 D14 D25 Rn' A563 Rop :=
  let RUNP := fresh "RUNP" in let RUNTO := fresh "RUNTO" in let BR := fresh "BR" in
  pose proof (SRr_run_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNP;
  pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO;
  pose proof (paj_branch (fx := fq) (PI := PI)) as BR;
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  apply (BR W _ _ _ _ _ BC_LT (SExt true 8 (SOff 563 0)) (SLit 0) HS);
  let Hsg := fresh "Hsg" in let HS1 := fresh "HS" in intros Hsg HS1; clear HS Hsg;
  paj_run_sh RUNP HS1 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA;
  let Hdc := fresh "Hdc" in let HS2 := fresh "HS" in
  apply (BR W _ _ _ _ _ BC_NE (SAlu ALU_AND (SExt true 8 (SOff 563 0)) (SLit 3)) (SLit 3) HS1); intros Hdc HS2; clear HS1;
  rewrite (yh_bne_op _ 563 (yh_bv cx n 0) A563 Rop) in Hdc;
  [ apply negb_true_iff, Z.eqb_neq in Hdc;
    paj_run_to_sh RUNTO HS2 HJ REC_OFF; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA;
    hd_leaf_tac false fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 HC n' e14 e25 D14 D25 Rn' Hdc]
  | apply negb_false_iff, Z.eqb_eq in Hdc;
    paj_run_to_sh RUNTO HS2 HJ ARM3_OFF; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA;
    hd_leaf_tac true fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 HC n' e14 e25 D14 D25 Rn' Hdc] ] ]
  end.

Lemma hd_d3 : forall (fq : YK11.FPState) cx h i n now ly3 S3 (W : world SEGS) mem3 md3 k acc regs E0 ms md,
  hd_ctx B MT XM_LIB RLO RHI tfib_K cx h i n now ly3 S3 W mem3 md3 k acc regs E0 -> 3 <= n -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E0 (hd_vals cx h i n now regs)) hd_ssD3 (restrict (w_H W) ms) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  hd_keep W mem3 (ms_mem ms) (d_A cx) -> hd_pres W mem3 (ms_mem ms) ->
  SRr SEGS W (mkCfg ms md) (hd_post B MT XM_LIB RLO RHI tfib_K cx h i).
Proof.
intros fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 ms md HC Hn FR HS HJ HK HP.
destruct (hd_wfacts cx h i n now ly3 S3 W mem3 md3 k acc regs E0 HC ltac:(lia))
  as (HEI & UA & EA & RA & HA1 & HA2 & E32 & HZ & Hcur & Hp8 & HAR3 & Hin3 & Harr & Hlen).
pose proof HZ as (A533 & _ & _ & _ & _ & _ & Z1 & Z2 & _ & _ & Z5 & _).
pose proof asan_consts as (C1 & _).
assert (B1 : 4096 <= d_cur cx n /\ d_cur cx n + n <= alloc_ceiling /\ alloc_ceiling <= 0x7fffff800000)
  by (clear - Z1 Z2 Z5 Hcur C1; lia).
assert (A531 : ew (d_env cx E0 (hd_vals cx h i n now regs)) 531 = w64 n)
  by exact (hd_env_x cx E0 (hd_vals cx h i n now regs) 0 ltac:(unfold hd_vals; cbn [length]; lia)).
assert (A563 : ew (d_env cx E0 (hd_vals cx h i n now regs)) 563 = w64 (yh_bv cx n 0))
  by exact (hd_env_x cx E0 (hd_vals cx h i n now regs) 32 ltac:(unfold hd_vals; cbn [length]; lia)).
assert (Rop : 0 <= yh_bv cx n 0 < 256) by (unfold yh_bv; apply yh_bv_range).
assert (D14 : sv_denot (d_env cx E0 (hd_vals cx h i n now regs)) (SOff 531 (-3)) = w64 (n - 3)).
{ rewrite (yh_off_den _ 531 n (-3) A531 ltac:(clear - B1 Hn; lia) ltac:(clear - B1 Hn; lia)). reflexivity. }
assert (D25 : sv_denot (d_env cx E0 (hd_vals cx h i n now regs)) (SOff 533 3) = w64 (d_cur cx (n - 3))).
{ rewrite (yh_off_den _ 533 (d_cur cx n) 3 A533 ltac:(clear - B1 Hn; lia) ltac:(clear - B1 Hn; lia)).
  unfold w64. f_equal. clear - Hcur. unfold d_cur in *. lia. }
hd_dgo fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 HC UA HA1 HA2 EA RA (n - 3) (SOff 531 (-3)) (SOff 533 3)
  D14 D25 (conj (ltac:(lia) : 0 <= n - 3) (ltac:(lia) : n - 3 <= n)) A563 Rop.
Qed.

Lemma hd_k3 : forall (fq : YK11.FPState) cx h i n now ly3 S3 (W : world SEGS) mem3 md3 k acc regs E0 ms md,
  hd_ctx B MT XM_LIB RLO RHI tfib_K cx h i n now ly3 S3 W mem3 md3 k acc regs E0 -> 3 <= n -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E0 (hd_vals cx h i n now regs)) hd_ssJ3 (restrict (w_H W) ms) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  hd_keep W mem3 (ms_mem ms) (d_A cx) -> hd_pres W mem3 (ms_mem ms) ->
  SRr SEGS W (mkCfg ms md) (hd_post B MT XM_LIB RLO RHI tfib_K cx h i).
Proof.
intros fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 ms md HC Hn FR HS HJ HK HP.
destruct (hd_wfacts cx h i n now ly3 S3 W mem3 md3 k acc regs E0 HC ltac:(lia))
  as (HEI & UA & EA & RA & HA1 & HA2 & E32 & HZ & Hcur & Hp8 & HAR3 & Hin3 & Harr & Hlen).
pose proof HZ as (A533 & _ & _ & _ & _ & _ & Z1 & Z2 & _ & _ & Z5 & _ & _ & Z8 & _ & Z10 & _).
pose proof asan_consts as (C1 & _).
assert (B1 : 4096 <= d_cur cx n /\ d_cur cx n + n <= alloc_ceiling /\ alloc_ceiling <= 0x7fffff800000)
  by (clear - Z1 Z2 Z5 Hcur C1; lia).
assert (A565 : ew (d_env cx E0 (hd_vals cx h i n now regs)) 565 = w64 (yh_bv cx n 2))
  by exact (hd_env_x cx E0 (hd_vals cx h i n now regs) 34 ltac:(unfold hd_vals; cbn [length]; lia)).
assert (Hb : aview SEGS (w_H W) (ms_mem ms) (d_cur cx n + 2) = Some (yh_bv cx n 2)).
{ rewrite (HK (d_cur cx n + 2) ltac:(clear - B1 Hn; lia) ltac:(clear - B1 Hn Z8 Z10; lia)).
  replace (d_cur cx n + 2) with (c_p cx + (c_n cx - n + 2)) by (clear - Hcur; unfold d_cur in *; lia).
  exact (yh_in_aview W mem3 (c_p cx) (c_pl cx) (c_n cx - n + 2) Harr ltac:(clear - Hlen Hn Hcur Z2; unfold d_cur in *; lia)). }
pose proof (hd_addb_ok fq _ hd_ssJ3 ms W 2 565 (d_cur cx n) (yh_bv cx n 2) HS A533
  ltac:(clear - B1; lia) ltac:(lia) ltac:(clear - B1 Hn; lia) A565 ltac:(unfold yh_bv; apply yh_bv_range) Hb
  (hd_byte_disj _ (ss_mem hd_ssJ3) 2 565 (d_cur cx n) (c_p cx) (c_n cx) (d_S cx) (d_A cx) (d_FB cx)
     (hd_zone_nb _ _ 0 3 _ _ _ _ _ HZ ltac:(lia) ltac:(clear - Hcur Hn; lia)) ltac:(vm_compute; reflexivity) ltac:(lia)))
  as HS1.
clear HS.
pose proof (SRr_run_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNP.
unfold hd_addb in HS1. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts hd_ssJ3] in HS1.
paj_run_sh RUNP HS1 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
exact (hd_d3 fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 _ _ HC Hn FR HS1 HJ HK HP).
Qed.

Lemma hd_d12 : forall (fq : YK11.FPState) (j : Z) (ssD : sstate) cx h i n now ly3 S3 (W : world SEGS) mem3 md3 k acc regs E0 ms md,
  (j = 1 /\ ssD = hd_ssD1) \/ (j = 2 /\ ssD = hd_ssD2) ->
  hd_ctx B MT XM_LIB RLO RHI tfib_K cx h i n now ly3 S3 W mem3 md3 k acc regs E0 -> n = j -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E0 (hd_vals cx h i n now regs)) ssD (restrict (w_H W) ms) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  hd_keep W mem3 (ms_mem ms) (d_A cx) -> hd_pres W mem3 (ms_mem ms) ->
  SRr SEGS W (mkCfg ms md) (hd_post B MT XM_LIB RLO RHI tfib_K cx h i).
Proof.
intros fq j ssD cx h i n now ly3 S3 W mem3 md3 k acc regs E0 ms md Hj HC Hn FR HS HJ HK HP.
destruct (hd_wfacts cx h i n now ly3 S3 W mem3 md3 k acc regs E0 HC ltac:(destruct Hj as [[-> _]|[-> _]]; lia))
  as (HEI & UA & EA & RA & HA1 & HA2 & E32 & HZ & Hcur & Hp8 & HAR3 & Hin3 & Harr & Hlen).
pose proof HZ as (A533 & _ & _ & _ & _ & _ & Z1 & Z2 & _ & _ & Z5 & _).
pose proof asan_consts as (C1 & _).
assert (B1 : 4096 <= d_cur cx n /\ d_cur cx n + n <= alloc_ceiling /\ alloc_ceiling <= 0x7fffff800000)
  by (clear - Z1 Z2 Z5 Hcur C1; lia).
assert (A563 : ew (d_env cx E0 (hd_vals cx h i n now regs)) 563 = w64 (yh_bv cx n 0))
  by exact (hd_env_x cx E0 (hd_vals cx h i n now regs) 32 ltac:(unfold hd_vals; cbn [length]; lia)).
assert (Rop : 0 <= yh_bv cx n 0 < 256) by (unfold yh_bv; apply yh_bv_range).
assert (D14 : sv_denot (d_env cx E0 (hd_vals cx h i n now regs)) (SLit 0) = w64 0) by reflexivity.
destruct Hj as [[-> ->] | [-> ->]].
- assert (D25 : sv_denot (d_env cx E0 (hd_vals cx h i n now regs)) (SOff 533 1) = w64 (d_cur cx 0)).
  { rewrite (yh_off_den _ 533 (d_cur cx n) 1 A533 ltac:(clear - B1 Hn; lia) ltac:(clear - B1 Hn; lia)).
    unfold w64. f_equal. clear - Hcur Hn. unfold d_cur in *. lia. }
  hd_dgo fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 HC UA HA1 HA2 EA RA 0 (SLit 0) (SOff 533 1)
    D14 D25 (conj (ltac:(lia) : 0 <= 0) (ltac:(lia) : 0 <= n)) A563 Rop.
- assert (D25 : sv_denot (d_env cx E0 (hd_vals cx h i n now regs)) (SOff 533 2) = w64 (d_cur cx 0)).
  { rewrite (yh_off_den _ 533 (d_cur cx n) 2 A533 ltac:(clear - B1 Hn; lia) ltac:(clear - B1 Hn; lia)).
    unfold w64. f_equal. clear - Hcur Hn. unfold d_cur in *. lia. }
  hd_dgo fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 HC UA HA1 HA2 EA RA 0 (SLit 0) (SOff 533 2)
    D14 D25 (conj (ltac:(lia) : 0 <= 0) (ltac:(lia) : 0 <= n)) A563 Rop.
Qed.

Lemma hd_c3 : forall (fq : YK11.FPState) cx h i n now ly3 S3 (W : world SEGS) mem3 md3 k acc regs E0 ms md,
  hd_ctx B MT XM_LIB RLO RHI tfib_K cx h i n now ly3 S3 W mem3 md3 k acc regs E0 -> 3 <= n -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E0 (hd_vals cx h i n now regs)) hd_ssC3 (restrict (w_H W) ms) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  hd_keep W mem3 (ms_mem ms) (d_A cx) -> hd_pres W mem3 (ms_mem ms) ->
  SRr SEGS W (mkCfg ms md) (hd_post B MT XM_LIB RLO RHI tfib_K cx h i).
Proof.
intros fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 ms md HC Hn FR HS HJ HK HP.
destruct (hd_wfacts cx h i n now ly3 S3 W mem3 md3 k acc regs E0 HC ltac:(lia))
  as (HEI & UA & EA & RA & HA1 & HA2 & E32 & HZ & Hcur & Hp8 & HAR3 & Hin3 & Harr & Hlen).
pose proof HZ as (A533 & _ & _ & _ & _ & _ & Z1 & Z2 & _ & _ & Z5 & _ & _ & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & _ & Z15).
pose proof asan_consts as (C1 & _).
assert (B1 : 4096 <= d_cur cx n /\ d_cur cx n + n <= alloc_ceiling /\ alloc_ceiling <= 0x7fffff800000)
  by (clear - Z1 Z2 Z5 Hcur C1; lia).
assert (Bx : c_p cx <= d_cur cx n + 2 < c_p cx + c_n cx) by (clear - Z2 Hcur Hn; lia).
assert (A561 : ew (d_env cx E0 (hd_vals cx h i n now regs)) 561 = w64 (yh_caddr (d_cur cx n + 2)))
  by exact (hd_env_x cx E0 (hd_vals cx h i n now regs) 30 ltac:(unfold hd_vals; cbn [length]; lia)).
assert (A562 : ew (d_env cx E0 (hd_vals cx h i n now regs)) 562 = w64 (yh_cell (c_p cx) (c_n cx) (d_cur cx n + 2)))
  by exact (hd_env_x cx E0 (hd_vals cx h i n now regs) 31 ltac:(unfold hd_vals; cbn [length]; lia)).
assert (A568 : ew (d_env cx E0 (hd_vals cx h i n now regs)) 568 =
  (if yh_cell (c_p cx) (c_n cx) (d_cur cx n + 2) =? 0 then getr regs 13 else w64 ((d_cur cx n + 2) mod 8)))
  by exact (hd_env_x cx E0 (hd_vals cx h i n now regs) 37 ltac:(unfold hd_vals; cbn [length]; lia)).
assert (A542 : ew (d_env cx E0 (hd_vals cx h i n now regs)) 542 = getr regs 13)
  by exact (hd_env_x cx E0 (hd_vals cx h i n now regs) 11 ltac:(unfold hd_vals; cbn [length]; lia)).
pose proof (yh_cell_range (c_p cx) (c_n cx) (d_cur cx n + 2)) as Rs.
pose proof (yh_caddr_range (d_cur cx n + 2) ltac:(clear - B1 Hn; lia)) as Ry.
pose proof (hd_cell_val B LAWS ly3 S3 W mem3 md3 (c_p cx) (c_n cx) (d_cur cx n + 2) HAR3 Hin3 Bx) as Hcv.
pose proof (SRr_run_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNP.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
apply (BR W _ _ _ _ _ BC_LTU (SLit 1) (SOff 533 3) HS); intros Hc HS1; clear HS.
2: { exfalso. rewrite (yh_bltu1 _ 533 (d_cur cx n) 3 A533 ltac:(clear - B1 Hn; lia) ltac:(clear - B1 Hn; lia)) in Hc.
     apply Z.ltb_ge in Hc. clear - Hc B1. lia. }
clear Hc.
paj_run_sh RUNP HS1 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
lazymatch goal with HS1 : st_ok_pi _ _ _ ?ss (restrict _ ?msx) |- _ =>
  assert (Hr : getr (ms_regs msx) 12%bv = ew (d_env cx E0 (hd_vals cx h i n now regs)) 561)
    by (rewrite (st_ok_pi_restrict_reg (w_H W) _ ss msx 12%bv HS1); hd_srget;
        rewrite (yh_caddr_den _ 533 (d_cur cx n) 2 A533 ltac:(clear - B1; lia) ltac:(lia) ltac:(clear - B1 Hn; lia) E32), A561;
        reflexivity);
  assert (Hav : aview SEGS (w_H W) (ms_mem msx) (yh_caddr (d_cur cx n + 2)) = Some (yh_cell (c_p cx) (c_n cx) (d_cur cx n + 2)))
    by (rewrite (HK (yh_caddr (d_cur cx n + 2)) ltac:(clear - Ry; unfold SHADOW_OFF in *; lia)
          ltac:(clear - Ry Z8 Z10 C1; unfold SHADOW_OFF in *; lia)); exact Hcv);
  pose proof (hd_retgt_ok fq _ ss msx W 12%bv 561 562 (yh_caddr (d_cur cx n + 2)) (yh_cell (c_p cx) (c_n cx) (d_cur cx n + 2))
    HS1 (yh_bvne 12%bv ltac:(vm_compute; reflexivity)) Hr A561 ltac:(clear - Ry; unfold SHADOW_OFF in *; lia) A562 ltac:(clear - Rs; lia) Hav
    (hd_cell_disj _ (ss_mem ss) 561 562 (yh_caddr (d_cur cx n + 2)) (d_cur cx n) 2 (c_p cx) (c_n cx) (d_S cx) (d_A cx) (d_FB cx)
       (hd_zone_nb _ _ 0 2 _ _ _ _ _ HZ ltac:(lia) ltac:(clear - Hcur Hn; lia)) ltac:(vm_compute; reflexivity) A561 Ry
       (yh_caddr_ne (d_cur cx n + 2) (d_FB cx) ltac:(clear - B1; lia) ltac:(clear - Z11; lia) Z13 ltac:(clear - Bx Z15; lia))))
    as HS2
end.
clear HS1.
paj_run_sh RUNP HS2 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
apply (BR W _ _ _ _ _ BC_EQ (SExt true 8 (SOff 562 0)) (SLit 0) HS2); intros Hc HS3; clear HS2;
  rewrite (yh_beq_cell _ 562 _ A562 Rs) in Hc.
- apply Z.eqb_eq in Hc.
  paj_run_sh RUNP HS3 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
  lazymatch goal with HS3 : st_ok_pi _ _ _ ?ss (restrict _ ?msx) |- _ =>
    assert (Hj : getr (ms_regs msx) 13%bv = ew (d_env cx E0 (hd_vals cx h i n now regs)) 568)
      by (rewrite (st_ok_pi_restrict_reg (w_H W) _ ss msx 13%bv HS3); hd_srget; rewrite sv_denot_SOff0, A542, A568, Hc;
          reflexivity);
    pose proof (hd_join_ok fq _ ss _ 13%bv 568 HS3 (yh_bvne 13%bv ltac:(vm_compute; reflexivity)) Hj
      ltac:(vm_compute; reflexivity)) as HSJ;
    assert (EJ : hd_join 13%bv 568 ss = hd_ssJ3) by (vm_compute; reflexivity)
  end.
  rewrite EJ in HSJ.
  exact (hd_k3 fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 _ _ HC Hn FR HSJ HJ HK HP).
- apply Z.eqb_neq in Hc.
  paj_run_sh RUNP HS3 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
  apply (BR W _ _ _ _ _ BC_GE (SAlu ALU_AND (SOff 533 2) (SLit 7)) (SExt true 8 (SOff 562 0)) HS3); intros Hc2 HS4; clear HS3.
  { exfalso. rewrite (yh_bge _ 533 562 (d_cur cx n) 2 _ A533 A562 ltac:(clear - B1 Hn; lia) ltac:(clear - B1 Hn; lia) Rs) in Hc2.
    apply negb_true_iff, Z.ltb_ge in Hc2.
    pose proof (yh_cell_lt (c_p cx) (c_n cx) (d_cur cx n + 2) Hp8 ltac:(clear - Bx; lia) Bx Hc) as Hlt.
    clear - Hc2 Hlt. lia. }
  paj_run_sh RUNP HS4 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
  lazymatch goal with HS4 : st_ok_pi _ _ _ ?ss (restrict _ ?msx) |- _ =>
    assert (Hj : getr (ms_regs msx) 13%bv = ew (d_env cx E0 (hd_vals cx h i n now regs)) 568)
      by (rewrite (st_ok_pi_restrict_reg (w_H W) _ ss msx 13%bv HS4); hd_srget;
          rewrite (denot_lit_U _ (SAlu _ _ _)), (yh_and7 _ 533 (d_cur cx n) 2 A533 ltac:(clear - B1 Hn; lia) ltac:(clear - B1 Hn; lia)),
            A568, (proj2 (Z.eqb_neq _ _) Hc); reflexivity);
    pose proof (hd_join_ok fq _ ss _ 13%bv 568 HS4 (yh_bvne 13%bv ltac:(vm_compute; reflexivity)) Hj
      ltac:(vm_compute; reflexivity)) as HSJ;
    assert (EJ : hd_join 13%bv 568 ss = hd_ssJ3) by (vm_compute; reflexivity)
  end.
  rewrite EJ in HSJ.
  exact (hd_k3 fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 _ _ HC Hn FR HSJ HJ HK HP).
Qed.

Lemma hd_k2 : forall (fq : YK11.FPState) cx h i n now ly3 S3 (W : world SEGS) mem3 md3 k acc regs E0 ms md,
  hd_ctx B MT XM_LIB RLO RHI tfib_K cx h i n now ly3 S3 W mem3 md3 k acc regs E0 -> 2 <= n -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E0 (hd_vals cx h i n now regs)) hd_ssJ2 (restrict (w_H W) ms) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  hd_keep W mem3 (ms_mem ms) (d_A cx) -> hd_pres W mem3 (ms_mem ms) ->
  SRr SEGS W (mkCfg ms md) (hd_post B MT XM_LIB RLO RHI tfib_K cx h i).
Proof.
intros fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 ms md HC Hn FR HS HJ HK HP.
destruct (hd_wfacts cx h i n now ly3 S3 W mem3 md3 k acc regs E0 HC ltac:(lia))
  as (HEI & UA & EA & RA & HA1 & HA2 & E32 & HZ & Hcur & Hp8 & HAR3 & Hin3 & Harr & Hlen).
pose proof HZ as (A533 & _ & _ & _ & _ & _ & Z1 & Z2 & _ & _ & Z5 & _ & _ & Z8 & _ & Z10 & _).
pose proof asan_consts as (C1 & _).
assert (B1 : 4096 <= d_cur cx n /\ d_cur cx n + n <= alloc_ceiling /\ alloc_ceiling <= 0x7fffff800000)
  by (clear - Z1 Z2 Z5 Hcur C1; lia).
assert (A531 : ew (d_env cx E0 (hd_vals cx h i n now regs)) 531 = w64 n)
  by exact (hd_env_x cx E0 (hd_vals cx h i n now regs) 0 ltac:(unfold hd_vals; cbn [length]; lia)).
assert (A564 : ew (d_env cx E0 (hd_vals cx h i n now regs)) 564 = w64 (yh_bv cx n 1))
  by exact (hd_env_x cx E0 (hd_vals cx h i n now regs) 33 ltac:(unfold hd_vals; cbn [length]; lia)).
assert (Hb : aview SEGS (w_H W) (ms_mem ms) (d_cur cx n + 1) = Some (yh_bv cx n 1)).
{ rewrite (HK (d_cur cx n + 1) ltac:(clear - B1 Hn; lia) ltac:(clear - B1 Hn Z8 Z10; lia)).
  replace (d_cur cx n + 1) with (c_p cx + (c_n cx - n + 1)) by (clear - Hcur; unfold d_cur in *; lia).
  exact (yh_in_aview W mem3 (c_p cx) (c_pl cx) (c_n cx - n + 1) Harr ltac:(clear - Hlen Hn Hcur Z2; unfold d_cur in *; lia)). }
pose proof (hd_addb_ok fq _ hd_ssJ2 ms W 1 564 (d_cur cx n) (yh_bv cx n 1) HS A533
  ltac:(clear - B1; lia) ltac:(lia) ltac:(clear - B1 Hn; lia) A564 ltac:(unfold yh_bv; apply yh_bv_range) Hb
  (hd_byte_disj _ (ss_mem hd_ssJ2) 1 564 (d_cur cx n) (c_p cx) (c_n cx) (d_S cx) (d_A cx) (d_FB cx)
     (hd_zone_nb _ _ 0 2 _ _ _ _ _ HZ ltac:(lia) ltac:(clear - Hcur Hn; lia)) ltac:(vm_compute; reflexivity) ltac:(lia)))
  as HS1.
clear HS.
pose proof (SRr_run_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNP.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
paj_run_sh RUNP HS1 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
apply (BR W _ _ _ _ _ BC_NE (SOff 531 0) (SLit 2) HS1); intros Hc HS2; clear HS1;
  rewrite (yh_bne_lit _ 531 n 2 A531 ltac:(clear - B1 Hn; lia) ltac:(lia)) in Hc.
- apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_sh RUNP HS2 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
  exact (hd_c3 fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 _ _ HC ltac:(clear - Hn Hc; lia) FR HS2 HJ HK HP).
- apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_sh RUNP HS2 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
  exact (hd_d12 fq 2 hd_ssD2 cx h i n now ly3 S3 W mem3 md3 k acc regs E0 _ _ (or_intror (conj eq_refl eq_refl)) HC Hc FR HS2 HJ HK HP).
Qed.

Lemma hd_c2 : forall (fq : YK11.FPState) cx h i n now ly3 S3 (W : world SEGS) mem3 md3 k acc regs E0 ms md,
  hd_ctx B MT XM_LIB RLO RHI tfib_K cx h i n now ly3 S3 W mem3 md3 k acc regs E0 -> 2 <= n -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E0 (hd_vals cx h i n now regs)) hd_ssC2 (restrict (w_H W) ms) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  hd_keep W mem3 (ms_mem ms) (d_A cx) -> hd_pres W mem3 (ms_mem ms) ->
  SRr SEGS W (mkCfg ms md) (hd_post B MT XM_LIB RLO RHI tfib_K cx h i).
Proof.
intros fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 ms md HC Hn FR HS HJ HK HP.
destruct (hd_wfacts cx h i n now ly3 S3 W mem3 md3 k acc regs E0 HC ltac:(lia))
  as (HEI & UA & EA & RA & HA1 & HA2 & E32 & HZ & Hcur & Hp8 & HAR3 & Hin3 & Harr & Hlen).
pose proof HZ as (A533 & _ & _ & _ & _ & _ & Z1 & Z2 & _ & _ & Z5 & _ & _ & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & _ & Z15).
pose proof asan_consts as (C1 & _).
assert (B1 : 4096 <= d_cur cx n /\ d_cur cx n + n <= alloc_ceiling /\ alloc_ceiling <= 0x7fffff800000)
  by (clear - Z1 Z2 Z5 Hcur C1; lia).
assert (Bx : c_p cx <= d_cur cx n + 1 < c_p cx + c_n cx) by (clear - Z2 Hcur Hn; lia).
assert (A559 : ew (d_env cx E0 (hd_vals cx h i n now regs)) 559 = w64 (yh_caddr (d_cur cx n + 1)))
  by exact (hd_env_x cx E0 (hd_vals cx h i n now regs) 28 ltac:(unfold hd_vals; cbn [length]; lia)).
assert (A560 : ew (d_env cx E0 (hd_vals cx h i n now regs)) 560 = w64 (yh_cell (c_p cx) (c_n cx) (d_cur cx n + 1)))
  by exact (hd_env_x cx E0 (hd_vals cx h i n now regs) 29 ltac:(unfold hd_vals; cbn [length]; lia)).
assert (A566 : ew (d_env cx E0 (hd_vals cx h i n now regs)) 566 =
  (if yh_cell (c_p cx) (c_n cx) (d_cur cx n) =? 0 then getr regs 11 else w64 (d_cur cx n mod 8)))
  by exact (hd_env_x cx E0 (hd_vals cx h i n now regs) 35 ltac:(unfold hd_vals; cbn [length]; lia)).
assert (A567 : ew (d_env cx E0 (hd_vals cx h i n now regs)) 567 =
  (if yh_cell (c_p cx) (c_n cx) (d_cur cx n + 1) =? 0
   then (if yh_cell (c_p cx) (c_n cx) (d_cur cx n) =? 0 then getr regs 11 else w64 (d_cur cx n mod 8))
   else w64 ((d_cur cx n + 1) mod 8)))
  by exact (hd_env_x cx E0 (hd_vals cx h i n now regs) 36 ltac:(unfold hd_vals; cbn [length]; lia)).
pose proof (yh_cell_range (c_p cx) (c_n cx) (d_cur cx n + 1)) as Rs.
pose proof (yh_caddr_range (d_cur cx n + 1) ltac:(clear - B1 Hn; lia)) as Ry.
pose proof (hd_cell_val B LAWS ly3 S3 W mem3 md3 (c_p cx) (c_n cx) (d_cur cx n + 1) HAR3 Hin3 Bx) as Hcv.
pose proof (SRr_run_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNP.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
apply (BR W _ _ _ _ _ BC_LTU (SLit 1) (SOff 533 2) HS); intros Hc HS1; clear HS.
2: { exfalso. rewrite (yh_bltu1 _ 533 (d_cur cx n) 2 A533 ltac:(clear - B1 Hn; lia) ltac:(clear - B1 Hn; lia)) in Hc.
     apply Z.ltb_ge in Hc. clear - Hc B1. lia. }
clear Hc.
paj_run_sh RUNP HS1 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
lazymatch goal with HS1 : st_ok_pi _ _ _ ?ss (restrict _ ?msx) |- _ =>
  assert (Hr : getr (ms_regs msx) 10%bv = ew (d_env cx E0 (hd_vals cx h i n now regs)) 559)
    by (rewrite (st_ok_pi_restrict_reg (w_H W) _ ss msx 10%bv HS1); hd_srget;
        rewrite (yh_caddr_den _ 533 (d_cur cx n) 1 A533 ltac:(clear - B1; lia) ltac:(lia) ltac:(clear - B1 Hn; lia) E32), A559;
        reflexivity);
  assert (Hav : aview SEGS (w_H W) (ms_mem msx) (yh_caddr (d_cur cx n + 1)) = Some (yh_cell (c_p cx) (c_n cx) (d_cur cx n + 1)))
    by (rewrite (HK (yh_caddr (d_cur cx n + 1)) ltac:(clear - Ry; unfold SHADOW_OFF in *; lia)
          ltac:(clear - Ry Z8 Z10 C1; unfold SHADOW_OFF in *; lia)); exact Hcv);
  pose proof (hd_retgt_ok fq _ ss msx W 10%bv 559 560 (yh_caddr (d_cur cx n + 1)) (yh_cell (c_p cx) (c_n cx) (d_cur cx n + 1))
    HS1 (yh_bvne 10%bv ltac:(vm_compute; reflexivity)) Hr A559 ltac:(clear - Ry; unfold SHADOW_OFF in *; lia) A560 ltac:(clear - Rs; lia) Hav
    (hd_cell_disj _ (ss_mem ss) 559 560 (yh_caddr (d_cur cx n + 1)) (d_cur cx n) 1 (c_p cx) (c_n cx) (d_S cx) (d_A cx) (d_FB cx)
       (hd_zone_nb _ _ 0 1 _ _ _ _ _ HZ ltac:(lia) ltac:(clear - Hcur Hn; lia)) ltac:(vm_compute; reflexivity) A559 Ry
       (yh_caddr_ne (d_cur cx n + 1) (d_FB cx) ltac:(clear - B1; lia) ltac:(clear - Z11; lia) Z13 ltac:(clear - Bx Z15; lia))))
    as HS2
end.
clear HS1.
paj_run_sh RUNP HS2 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
apply (BR W _ _ _ _ _ BC_EQ (SExt true 8 (SOff 560 0)) (SLit 0) HS2); intros Hc HS3; clear HS2;
  rewrite (yh_beq_cell _ 560 _ A560 Rs) in Hc.
- apply Z.eqb_eq in Hc.
  paj_run_sh RUNP HS3 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
  lazymatch goal with HS3 : st_ok_pi _ _ _ ?ss (restrict _ ?msx) |- _ =>
    assert (Hj : getr (ms_regs msx) 11%bv = ew (d_env cx E0 (hd_vals cx h i n now regs)) 567)
      by (rewrite (st_ok_pi_restrict_reg (w_H W) _ ss msx 11%bv HS3); hd_srget; rewrite sv_denot_SOff0, A566, A567, Hc;
          reflexivity);
    pose proof (hd_join_ok fq _ ss _ 11%bv 567 HS3 (yh_bvne 11%bv ltac:(vm_compute; reflexivity)) Hj
      ltac:(vm_compute; reflexivity)) as HSJ;
    assert (EJ : hd_join 11%bv 567 ss = hd_ssJ2) by (vm_compute; reflexivity)
  end.
  rewrite EJ in HSJ.
  exact (hd_k2 fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 _ _ HC Hn FR HSJ HJ HK HP).
- apply Z.eqb_neq in Hc.
  paj_run_sh RUNP HS3 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
  apply (BR W _ _ _ _ _ BC_GE (SAlu ALU_AND (SOff 533 1) (SLit 7)) (SExt true 8 (SOff 560 0)) HS3); intros Hc2 HS4; clear HS3.
  { exfalso. rewrite (yh_bge _ 533 560 (d_cur cx n) 1 _ A533 A560 ltac:(clear - B1 Hn; lia) ltac:(clear - B1 Hn; lia) Rs) in Hc2.
    apply negb_true_iff, Z.ltb_ge in Hc2.
    pose proof (yh_cell_lt (c_p cx) (c_n cx) (d_cur cx n + 1) Hp8 ltac:(clear - Bx; lia) Bx Hc) as Hlt.
    clear - Hc2 Hlt. lia. }
  paj_run_sh RUNP HS4 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
  lazymatch goal with HS4 : st_ok_pi _ _ _ ?ss (restrict _ ?msx) |- _ =>
    assert (Hj : getr (ms_regs msx) 11%bv = ew (d_env cx E0 (hd_vals cx h i n now regs)) 567)
      by (rewrite (st_ok_pi_restrict_reg (w_H W) _ ss msx 11%bv HS4); hd_srget;
          rewrite (denot_lit_U _ (SAlu _ _ _)), (yh_and7 _ 533 (d_cur cx n) 1 A533 ltac:(clear - B1 Hn; lia) ltac:(clear - B1 Hn; lia)),
            A567, (proj2 (Z.eqb_neq _ _) Hc); reflexivity);
    pose proof (hd_join_ok fq _ ss _ 11%bv 567 HS4 (yh_bvne 11%bv ltac:(vm_compute; reflexivity)) Hj
      ltac:(vm_compute; reflexivity)) as HSJ;
    assert (EJ : hd_join 11%bv 567 ss = hd_ssJ2) by (vm_compute; reflexivity)
  end.
  rewrite EJ in HSJ.
  exact (hd_k2 fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 _ _ HC Hn FR HSJ HJ HK HP).
Qed.

Lemma hd_k1 : forall (fq : YK11.FPState) cx h i n now ly3 S3 (W : world SEGS) mem3 md3 k acc regs E0 ms md,
  hd_ctx B MT XM_LIB RLO RHI tfib_K cx h i n now ly3 S3 W mem3 md3 k acc regs E0 -> 1 <= n -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E0 (hd_vals cx h i n now regs)) hd_ssJ1 (restrict (w_H W) ms) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  hd_keep W mem3 (ms_mem ms) (d_A cx) -> hd_pres W mem3 (ms_mem ms) ->
  SRr SEGS W (mkCfg ms md) (hd_post B MT XM_LIB RLO RHI tfib_K cx h i).
Proof.
intros fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 ms md HC Hn FR HS HJ HK HP.
destruct (hd_wfacts cx h i n now ly3 S3 W mem3 md3 k acc regs E0 HC ltac:(lia))
  as (HEI & UA & EA & RA & HA1 & HA2 & E32 & HZ & Hcur & Hp8 & HAR3 & Hin3 & Harr & Hlen).
pose proof HZ as (A533 & _ & _ & _ & _ & _ & Z1 & Z2 & _ & _ & Z5 & _ & _ & Z8 & _ & Z10 & _).
pose proof asan_consts as (C1 & _).
assert (B1 : 4096 <= d_cur cx n /\ d_cur cx n + n <= alloc_ceiling /\ alloc_ceiling <= 0x7fffff800000)
  by (clear - Z1 Z2 Z5 Hcur C1; lia).
assert (A531 : ew (d_env cx E0 (hd_vals cx h i n now regs)) 531 = w64 n)
  by exact (hd_env_x cx E0 (hd_vals cx h i n now regs) 0 ltac:(unfold hd_vals; cbn [length]; lia)).
assert (A563 : ew (d_env cx E0 (hd_vals cx h i n now regs)) 563 = w64 (yh_bv cx n 0))
  by exact (hd_env_x cx E0 (hd_vals cx h i n now regs) 32 ltac:(unfold hd_vals; cbn [length]; lia)).
assert (Hb : aview SEGS (w_H W) (ms_mem ms) (d_cur cx n + 0) = Some (yh_bv cx n 0)).
{ rewrite (HK (d_cur cx n + 0) ltac:(clear - B1 Hn; lia) ltac:(clear - B1 Hn Z8 Z10; lia)).
  replace (d_cur cx n + 0) with (c_p cx + (c_n cx - n + 0)) by (clear - Hcur; unfold d_cur in *; lia).
  exact (yh_in_aview W mem3 (c_p cx) (c_pl cx) (c_n cx - n + 0) Harr ltac:(clear - Hlen Hn Hcur Z2; unfold d_cur in *; lia)). }
pose proof (hd_addb_ok fq _ hd_ssJ1 ms W 0 563 (d_cur cx n) (yh_bv cx n 0) HS A533
  ltac:(clear - B1; lia) ltac:(lia) ltac:(clear - B1 Hn; lia) A563 ltac:(unfold yh_bv; apply yh_bv_range) Hb
  (hd_byte_disj _ (ss_mem hd_ssJ1) 0 563 (d_cur cx n) (c_p cx) (c_n cx) (d_S cx) (d_A cx) (d_FB cx)
     (hd_zone_nb _ _ 0 1 _ _ _ _ _ HZ ltac:(lia) ltac:(clear - Hcur Hn; lia)) ltac:(vm_compute; reflexivity) ltac:(lia)))
  as HS1.
clear HS.
pose proof (SRr_run_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNP.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
paj_run_sh RUNP HS1 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
apply (BR W _ _ _ _ _ BC_NE (SOff 531 0) (SLit 1) HS1); intros Hc HS2; clear HS1;
  rewrite (yh_bne_lit _ 531 n 1 A531 ltac:(clear - B1 Hn; lia) ltac:(lia)) in Hc.
- apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_sh RUNP HS2 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
  exact (hd_c2 fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 _ _ HC ltac:(clear - Hn Hc; lia) FR HS2 HJ HK HP).
- apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_sh RUNP HS2 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
  exact (hd_d12 fq 1 hd_ssD1 cx h i n now ly3 S3 W mem3 md3 k acc regs E0 _ _ (or_introl (conj eq_refl eq_refl)) HC Hc FR HS2 HJ HK HP).
Qed.

Lemma hd_c1 : forall (fq : YK11.FPState) cx h i n now ly3 S3 (W : world SEGS) mem3 md3 k acc regs E0 ms md,
  hd_ctx B MT XM_LIB RLO RHI tfib_K cx h i n now ly3 S3 W mem3 md3 k acc regs E0 -> 1 <= n -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E0 (hd_vals cx h i n now regs)) hd_ssC1 (restrict (w_H W) ms) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  hd_keep W mem3 (ms_mem ms) (d_A cx) -> hd_pres W mem3 (ms_mem ms) ->
  SRr SEGS W (mkCfg ms md) (hd_post B MT XM_LIB RLO RHI tfib_K cx h i).
Proof.
intros fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 ms md HC Hn FR HS HJ HK HP.
destruct (hd_wfacts cx h i n now ly3 S3 W mem3 md3 k acc regs E0 HC ltac:(lia))
  as (HEI & UA & EA & RA & HA1 & HA2 & E32 & HZ & Hcur & Hp8 & HAR3 & Hin3 & Harr & Hlen).
pose proof HZ as (A533 & _ & _ & _ & _ & _ & Z1 & Z2 & _ & _ & Z5 & _ & _ & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & _ & Z15).
pose proof asan_consts as (C1 & _).
assert (B1 : 4096 <= d_cur cx n /\ d_cur cx n + n <= alloc_ceiling /\ alloc_ceiling <= 0x7fffff800000)
  by (clear - Z1 Z2 Z5 Hcur C1; lia).
assert (Bx : c_p cx <= d_cur cx n < c_p cx + c_n cx) by (clear - Z2 Hcur Hn; lia).
assert (A557 : ew (d_env cx E0 (hd_vals cx h i n now regs)) 557 = w64 (yh_caddr (d_cur cx n)))
  by exact (hd_env_x cx E0 (hd_vals cx h i n now regs) 26 ltac:(unfold hd_vals; cbn [length]; lia)).
assert (A558 : ew (d_env cx E0 (hd_vals cx h i n now regs)) 558 = w64 (yh_cell (c_p cx) (c_n cx) (d_cur cx n)))
  by exact (hd_env_x cx E0 (hd_vals cx h i n now regs) 27 ltac:(unfold hd_vals; cbn [length]; lia)).
assert (A566 : ew (d_env cx E0 (hd_vals cx h i n now regs)) 566 =
  (if yh_cell (c_p cx) (c_n cx) (d_cur cx n) =? 0 then getr regs 11 else w64 (d_cur cx n mod 8)))
  by exact (hd_env_x cx E0 (hd_vals cx h i n now regs) 35 ltac:(unfold hd_vals; cbn [length]; lia)).
assert (A540 : ew (d_env cx E0 (hd_vals cx h i n now regs)) 540 = getr regs 11)
  by exact (hd_env_x cx E0 (hd_vals cx h i n now regs) 9 ltac:(unfold hd_vals; cbn [length]; lia)).
pose proof (yh_cell_range (c_p cx) (c_n cx) (d_cur cx n)) as Rs.
pose proof (yh_caddr_range (d_cur cx n) ltac:(clear - B1 Hn; lia)) as Ry.
pose proof (hd_cell_val B LAWS ly3 S3 W mem3 md3 (c_p cx) (c_n cx) (d_cur cx n) HAR3 Hin3 Bx) as Hcv.
pose proof (SRr_run_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNP.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
apply (BR W _ _ _ _ _ BC_LTU (SLit 1) (SOff 533 1) HS); intros Hc HS1; clear HS.
2: { exfalso. rewrite (yh_bltu1 _ 533 (d_cur cx n) 1 A533 ltac:(clear - B1 Hn; lia) ltac:(clear - B1 Hn; lia)) in Hc.
     apply Z.ltb_ge in Hc. clear - Hc B1. lia. }
clear Hc.
paj_run_sh RUNP HS1 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
lazymatch goal with HS1 : st_ok_pi _ _ _ ?ss (restrict _ ?msx) |- _ =>
  assert (Hr : getr (ms_regs msx) 10%bv = ew (d_env cx E0 (hd_vals cx h i n now regs)) 557)
    by (rewrite (st_ok_pi_restrict_reg (w_H W) _ ss msx 10%bv HS1); hd_srget;
        rewrite (yh_caddr_den _ 533 (d_cur cx n) 0 A533 ltac:(clear - B1; lia) ltac:(lia) ltac:(clear - B1 Hn; lia) E32), A557,
          Z.add_0_r; reflexivity);
  assert (Hav : aview SEGS (w_H W) (ms_mem msx) (yh_caddr (d_cur cx n)) = Some (yh_cell (c_p cx) (c_n cx) (d_cur cx n)))
    by (rewrite (HK (yh_caddr (d_cur cx n)) ltac:(clear - Ry; unfold SHADOW_OFF in *; lia)
          ltac:(clear - Ry Z8 Z10 C1; unfold SHADOW_OFF in *; lia)); exact Hcv);
  pose proof (hd_retgt_ok fq _ ss msx W 10%bv 557 558 (yh_caddr (d_cur cx n)) (yh_cell (c_p cx) (c_n cx) (d_cur cx n))
    HS1 (yh_bvne 10%bv ltac:(vm_compute; reflexivity)) Hr A557 ltac:(clear - Ry; unfold SHADOW_OFF in *; lia) A558 ltac:(clear - Rs; lia) Hav
    (hd_cell_disj _ (ss_mem ss) 557 558 (yh_caddr (d_cur cx n)) (d_cur cx n) 0 (c_p cx) (c_n cx) (d_S cx) (d_A cx) (d_FB cx)
       HZ ltac:(vm_compute; reflexivity) A557 Ry
       (yh_caddr_ne (d_cur cx n) (d_FB cx) ltac:(clear - B1; lia) ltac:(clear - Z11; lia) Z13 ltac:(clear - Bx Z15; lia))))
    as HS2
end.
clear HS1.
paj_run_sh RUNP HS2 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
apply (BR W _ _ _ _ _ BC_EQ (SExt true 8 (SOff 558 0)) (SLit 0) HS2); intros Hc HS3; clear HS2;
  rewrite (yh_beq_cell _ 558 _ A558 Rs) in Hc.
- apply Z.eqb_eq in Hc.
  paj_run_sh RUNP HS3 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
  lazymatch goal with HS3 : st_ok_pi _ _ _ ?ss (restrict _ ?msx) |- _ =>
    assert (Hj : getr (ms_regs msx) 11%bv = ew (d_env cx E0 (hd_vals cx h i n now regs)) 566)
      by (rewrite (st_ok_pi_restrict_reg (w_H W) _ ss msx 11%bv HS3); hd_srget; rewrite sv_denot_SOff0, A540, A566, Hc;
          reflexivity);
    pose proof (hd_join_ok fq _ ss _ 11%bv 566 HS3 (yh_bvne 11%bv ltac:(vm_compute; reflexivity)) Hj
      ltac:(vm_compute; reflexivity)) as HSJ;
    assert (EJ : hd_join 11%bv 566 ss = hd_ssJ1) by (vm_compute; reflexivity)
  end.
  rewrite EJ in HSJ.
  exact (hd_k1 fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 _ _ HC Hn FR HSJ HJ HK HP).
- apply Z.eqb_neq in Hc.
  paj_run_sh RUNP HS3 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
  apply (BR W _ _ _ _ _ BC_GE (SAlu ALU_AND (SOff 533 0) (SLit 7)) (SExt true 8 (SOff 558 0)) HS3); intros Hc2 HS4; clear HS3.
  { exfalso. rewrite (yh_bge _ 533 558 (d_cur cx n) 0 _ A533 A558 ltac:(clear - B1 Hn; lia) ltac:(clear - B1 Hn; lia) Rs) in Hc2.
    apply negb_true_iff, Z.ltb_ge in Hc2. rewrite Z.add_0_r in Hc2.
    pose proof (yh_cell_lt (c_p cx) (c_n cx) (d_cur cx n) Hp8 ltac:(clear - Bx; lia) Bx Hc) as Hlt.
    clear - Hc2 Hlt. lia. }
  paj_run_sh RUNP HS4 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
  lazymatch goal with HS4 : st_ok_pi _ _ _ ?ss (restrict _ ?msx) |- _ =>
    assert (Hj : getr (ms_regs msx) 11%bv = ew (d_env cx E0 (hd_vals cx h i n now regs)) 566)
      by (rewrite (st_ok_pi_restrict_reg (w_H W) _ ss msx 11%bv HS4); hd_srget;
          rewrite (denot_lit_U _ (SAlu _ _ _)), (yh_and7 _ 533 (d_cur cx n) 0 A533 ltac:(clear - B1 Hn; lia) ltac:(clear - B1 Hn; lia)),
            A566, (proj2 (Z.eqb_neq _ _) Hc), Z.add_0_r; reflexivity);
    pose proof (hd_join_ok fq _ ss _ 11%bv 566 HS4 (yh_bvne 11%bv ltac:(vm_compute; reflexivity)) Hj
      ltac:(vm_compute; reflexivity)) as HSJ;
    assert (EJ : hd_join 11%bv 566 ss = hd_ssJ1) by (vm_compute; reflexivity)
  end.
  rewrite EJ in HSJ.
  exact (hd_k1 fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 _ _ HC Hn FR HSJ HJ HK HP).
Qed.

Lemma hd_frame_eq : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' HF Hw x. apply HF. intros (r & Hr & Ha).
rewrite forallb_forall in Hw. specialize (Hw r Hr). apply Z.leb_le in Hw. lia.
Qed.

Theorem pb_hdr : hdr_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold hdr_spec. intros cx h i W c Hinv.
destruct Hinv as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & FR & HB & HJ & HFR & Hk & Hev & Hmo & Hacc &
  (n & now & Ri & Rn & Rnow & HR & HBD)).
pose proof HBD as (T & G & Lk & H & (E0 & HE & HRG & HFL & _) & _).
assert (HC : hd_ctx B MT XM_LIB RLO RHI tfib_K cx h i n now ly3 S3 W mem3 md3 k acc regs E0).
{ unfold hd_ctx. repeat (split; [eassumption|]). exact HFL. }
pose proof (hd_seat0 B MT XM_LIB RLO RHI tfib_K LAWS TL SEAT FACTS fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 HC) as HS.
assert (A531 : ew (d_env cx E0 (hd_vals cx h i n now regs)) 531 = w64 n)
  by exact (hd_env_x cx E0 (hd_vals cx h i n now regs) 0 ltac:(unfold hd_vals; cbn [length]; lia)).
pose proof HB as ((_ & _ & _ & _ & Hpn & _) & _).
pose proof HBD as (_ & _ & _ & _ & _ & _ & _ & _ & (Hn' & _) & _).
assert (Rn64 : 0 <= n < 2 ^ 64) by (clear - Hpn Hn' Rn; destruct Hpn as [(H0 & _) | (Hr & _)]; lia).
assert (HK0 : hd_keep W mem3 mem3 (d_A cx)) by (intros a _ _; reflexivity).
assert (HP0 : hd_pres W mem3 mem3) by (intros a Ha; exact Ha).
pose proof (SRr_run_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNP.
pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + HDR_OFF)) with (Z_to_bv 64 (BASE + HDR_OFF)).
apply (BR W _ _ _ _ _ BC_NE (SOff 531 0) (SLit 0) HS); intros Hc HS1; clear HS;
  rewrite (yh_bne_lit _ 531 n 0 A531 Rn64 ltac:(lia)) in Hc.
- apply negb_true_iff, Z.eqb_neq in Hc.
  destruct (hd_wfacts cx h i n now ly3 S3 W mem3 md3 k acc regs E0 HC ltac:(lia))
    as (HEI & UA & EA & RA & HA1 & HA2 & _).
  paj_run_sh RUNP HS1 HJ; [hd_awr_tac cx UA HA1 HA2 | hd_upd EA RA].
  exact (hd_c1 fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 _ _ HC ltac:(lia) FR HS1 HJ HK0 HP0).
- apply negb_false_iff, Z.eqb_eq in Hc.
  pose proof (hd_E_env cx E0 (hd_vals cx h i n now regs) HE) as (_ & _ & HEI & _).
  hd_ro HS1 60%nat.
  paj_run_to_sh RUNTO HS1 HJ EXIT_OFF;
    [lazymatch goal with |- awr_ok ?E ?rs ?STK ?sp0 ?fp ?b0 ?bc ?ly ?own =>
       exact (hd_awr_ro E rs STK sp0 fp b0 bc ly own ltac:(vm_compute; reflexivity)) end|].
  lazymatch goal with HF : frame_of _ ?rs (ms_mem _) (ms_mem _) |- _ =>
    pose proof (hd_frame_eq _ _ _ _ HF ltac:(vm_compute; reflexivity)) as MEQ end.
  lazymatch goal with HS1 : st_ok_pi _ _ _ ?ss (restrict _ ?msx) |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
    apply SRr_ret;
    exact (hd_exit B MT MT_TRIV XM_LIB RLO RHI tfib_K BKEEP fq cx h i n now ly3 S3 W mem3 md3 k acc regs E0 ss msx mdx
      HC FR HJ MEQ HS1 eq_refl eq_refl ltac:(vm_compute; reflexivity))
  end.
Qed.

End h.
End f.
End d.
