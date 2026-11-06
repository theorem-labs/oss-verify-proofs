(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 437 of its 472 lines of code are new or changed and 1243 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntProE.v; 283 of its 330 lines of code are new or changed and 425 lines of the source are left out. *)
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
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntHdrLib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition hd_xregs : list (bv 5 * sv) :=
  [(2%bv, SOff 60 0); (3%bv, SOff 3 0); (4%bv, SOff 4 0); (8%bv, SOff 2 0); (9%bv, SOff 60 0);
   (19%bv, SOff 32 0); (27%bv, SOff 529 0)].
Definition hd_xregb (ss : sstate) : bool :=
  forallb (fun re => sv_eqb (sr_get (ss_regs ss) (fst re)) (snd re)) hd_xregs.

Definition hd_kinds (nb : Z) (rs : smem) : bool :=
  forallb (fun r => match YP09.r_base r with
    | Some b =>
      if Nat.eqb b 533 then (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? nb)
      else if Nat.eqb b AT_STK then (-104 <=? YP09.r_lo r) && (YP09.r_hi r <=? 0)
      else if Nat.eqb b AT_A then (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 472)
      else if Nat.eqb b AT_F then (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 4096)
      else if Nat.eqb b AT_SH then (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 512)
      else if (Nat.eqb b (A_OBJ 0) || Nat.eqb b (A_OBJ 12))%bool then (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 8)
      else false
    | None => false end) rs.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Definition yh_bv (cx : dcx) (n j : Z) : Z :=
  nth (Z.to_nat (c_n cx - n + j)) (map (fun b : byte => bv_unsigned b) (c_pl cx)) 0.
Definition hd_vals (cx : dcx) (h i n now : Z) (regs : bvmap 5 word) : list word :=
  let p := c_p cx in let cn := c_n cx in let cur := d_cur cx n in
  let a1j := if yh_cell p cn cur =? 0 then getr regs 11 else w64 (cur mod 8) in
  [w64 n; w64 i; w64 cur; w64 now; getr regs 1; getr regs 5; getr regs 6; getr regs 7; getr regs 10;
   getr regs 11; getr regs 12; getr regs 13; getr regs 15; getr regs 16; getr regs 17; getr regs 23;
   getr regs 25; getr regs 28; getr regs 29; getr regs 30; getr regs 31;
   w64 h; w64 (dnot (d_obj cx OG)); w64 (dnot (d_obj cx OT)); w64 (dnot (d_obj cx OO)); w64 (dnot (d_obj cx OUSED));
   w64 (yh_caddr cur); w64 (yh_cell p cn cur); w64 (yh_caddr (cur + 1)); w64 (yh_cell p cn (cur + 1));
   w64 (yh_caddr (cur + 2)); w64 (yh_cell p cn (cur + 2));
   w64 (yh_bv cx n 0); w64 (yh_bv cx n 1); w64 (yh_bv cx n 2);
   a1j; (if yh_cell p cn (cur + 1) =? 0 then a1j else w64 ((cur + 1) mod 8));
   (if yh_cell p cn (cur + 2) =? 0 then getr regs 13 else w64 ((cur + 2) mod 8))].

Lemma hd_env_old : forall cx E vals n, (n < AT_FL)%nat -> ew (d_env cx E vals) n = ew E n.
Proof. intros cx E vals n Hn. unfold d_env. apply ew_havoc_old. exact Hn. Qed.

Lemma hd_env_fl : forall cx E vals,
  ew (d_env cx E vals) AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)).
Proof.
intros cx E vals. unfold d_env. replace AT_FL with (AT_FL + 0)%nat at 2 by lia.
rewrite (ew_havoc_new _ AT_FL _ 0 (Z_to_bv 64 0)) by (cbn [length]; lia). reflexivity.
Qed.

Lemma hd_env_x : forall cx E vals j, (j < length vals)%nat ->
  ew (d_env cx E vals) (AT_X + j) = nth j vals (Z_to_bv 64 0).
Proof.
intros cx E vals j Hj. unfold d_env. replace (AT_X + j)%nat with (AT_FL + S j)%nat by (unfold AT_X, AT_FL; lia).
rewrite (ew_havoc_new _ AT_FL _ (S j) (Z_to_bv 64 0)) by (cbn [length]; lia). reflexivity.
Qed.

Lemma hd_E_env : forall cx E vals, d_E cx E -> d_E cx (d_env cx E vals).
Proof.
intros cx E vals (EE & E32 & HEI & E60 & EF & ESH). unfold d_E.
rewrite !hd_env_old by (unfold AT_FL, AT_A, AT_F, AT_SH; lia).
split; [|split; [exact E32 | split; [|split; [exact E60 | split; [exact EF | exact ESH]]]]].
- intros n r Hn. rewrite hd_env_old; [exact (EE n r Hn)|].
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr. unfold AT_FL. lia.
- unfold d_env. apply img_env_havoc_hi; [exact HEI | unfold A_LIM, AT_FL; lia].
Qed.

Definition hd_keep (W : world SEGS) (m0 m : word -> option byte) (A : Z) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (A <= a < A + 472) -> aview SEGS (w_H W) m a = aview SEGS (w_H W) m0 a.
Definition hd_pres (W : world SEGS) (m0 m : word -> option byte) : Prop :=
  forall a, apresent (w_H W) m0 a -> apresent (w_H W) m a.

Lemma hd_wr_ok : forall E rs A, hd_wrb rs = true -> ew E AT_A = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
  forall x, in_wrange E rs x -> A <= x < A + 472.
Proof.
intros E rs A Hb HA HAr x (r & Hin & Hx). unfold hd_wrb in Hb. rewrite forallb_forall in Hb.
specialize (Hb r Hin). apply orb_true_iff in Hb as [Hb | Hb]; [apply Z.leb_le in Hb; lia|].
apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [Hb H1].
apply Z.leb_le in H1. apply Z.leb_le in H2.
destruct (YP09.r_base r) as [b|] eqn:Eb; [|discriminate]. cbn [obase_eqb] in Hb. apply Nat.eqb_eq in Hb. subst b.
try rewrite Eb in Hx. cbn [base_val] in Hx. rewrite HA, unsigned_lit_small in Hx by lia. lia.
Qed.

Lemma hd_keep_step : forall E rs (W : world SEGS) m0 m m' A,
  (forall x, in_wrange E rs x -> A <= x < A + 472) ->
  frame_of E rs (rd W m) (rd W m') -> hd_keep W m0 m A -> hd_keep W m0 m' A.
Proof.
intros E rs W m0 m m' A Hw HF HK a Ha Hna. rewrite <- (HK a Ha Hna). apply aview_eq_of. apply HF.
rewrite unsigned_lit_small by lia. intros Hin. apply Hna. exact (Hw a Hin).
Qed.

Lemma hd_pres_step : forall (W : world SEGS) m0 m m',
  mem_grows (rd W m) (rd W m') -> hd_pres W m0 m -> hd_pres W m0 m'.
Proof.
intros W m0 m m' HG HP a Ha. destruct (HP a Ha) as [Hh [b Hb]]. split; [exact Hh|].
assert (G : mrestrict (w_H W) m' (Z_to_bv 64 a) <> None)
  by (apply HG; unfold mrestrict; rewrite Hh, Hb; discriminate).
unfold mrestrict in G. rewrite Hh in G.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | contradiction].
Qed.

Lemma hd_awr : forall E rs STK sp0 FP bl0 blc ly own A,
  hd_wrb rs = true -> bv_unsigned (ew E AT_A) = A -> - STK <= A - sp0 -> A - sp0 + 472 <= 0 ->
  awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
intros E rs STK sp0 FP bl0 blc ly own A Hb HA H1 H2. unfold hd_wrb in Hb.
induction rs as [|r rs IH]; [apply awr_ok_nil|].
cbn [forallb] in Hb. apply andb_true_iff in Hb as [Hr Hrs].
apply orb_true_iff in Hr as [Hr | Hr].
- apply awr_ok_cons_ro; [apply Z.leb_le in Hr; exact Hr | exact (IH Hrs)].
- apply andb_true_iff in Hr as [Hr Hw2]. apply andb_true_iff in Hr as [Hr Hw1].
  apply Z.leb_le in Hw1. apply Z.leb_le in Hw2.
  destruct (YP09.r_base r) as [b|] eqn:Eb; [|discriminate]. cbn [obase_eqb] in Hr. apply Nat.eqb_eq in Hr. subst b.
  apply (awr_ok_cons_stack_off E r rs STK sp0 FP bl0 blc ly own AT_A (A - sp0) Eb);
    [rewrite HA; lia | lia | lia | exact (IH Hrs)].
Qed.

Lemma hd_join_ok : forall (fq : YK11.FPState) E ss ms (r : bv 5) (a : nat),
  st_ok_pi (fx := fq) SEGS VAL E ss ms -> r <> 0%bv -> getr (ms_regs ms) r = ew E a ->
  regions_wf (tl (ss_mem ss)) = true ->
  st_ok_pi (fx := fq) SEGS VAL E (hd_join r a ss) ms.
Proof.
intros fq E ss ms r a HS Hr Ha Hwf.
pose proof (st_ok_pi_set_reg (fx := fq) E ss ms r (SOff a 0) HS Hr ltac:(rewrite sv_denot_SOff0; exact Ha)) as HS1.
assert (Hsub : submem (tl (ss_mem ss)) (ss_mem ss)).
{ destruct (ss_mem ss) as [|r0 rs]; [constructor | apply submem_drop; apply submem_refl]. }
pose proof (st_ok_pi_submem (fx := fq) E _ ms (tl (ss_mem ss)) HS1 Hsub Hwf) as HS2.
exact (st_ok_pi_facts_incl3 (fx := fq) E _ ms (f_atoms (ss_facts ss)) [] (f_alias (ss_facts ss)) HS2
  (fun x H => H) (fun x H => match H with end) (fun x H => H)).
Qed.

Lemma hd_cell_ok : forall E (W : world SEGS) mem (q v : nat) (y s : Z),
  ew E q = w64 y -> 0 <= y < 2 ^ 64 -> ew E v = w64 s -> 0 <= s < 256 ->
  aview SEGS (w_H W) mem y = Some s -> region_ok SEGS E (rd W mem) (hd_cell q v).
Proof.
intros E W mem q v y s Hq Hy Hv Hs Hav. unfold w64 in Hq, Hv.
unfold region_ok, hd_cell.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hq, (unsigned_lit_small y) by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
intros i Hi. cbn [YP09.c_off YP09.c_val YP09.c_len cv_len Z.of_N] in *.
assert (Hi0 : i = 0) by lia. subst i.
assert (Hdv : sv_denot E (SOff v 0) = Z_to_bv 64 s).
{ rewrite denot_lit_U, U_SOff, Hv, Z.add_0_r, (unsigned_lit_small s) by lia.
  f_equal. apply zcanon_id. unfold M64. lia. }
unfold cbyte. cbn [YP09.c_val]. rewrite Hdv.
unfold byte_of_word. rewrite (unsigned_lit_small s) by lia. cbn [Z.mul]. rewrite Z.shiftr_0_r.
unfold aview in Hav. destruct (mbyte SEGS (mrestrict (w_H W) mem) y) as [b|] eqn:Hb; [|discriminate].
cbn [option_map] in Hav. injection Hav as Hav.
exists (Z_to_bv 8 s). split; [reflexivity|].
rewrite !Z.add_0_r, Hb. f_equal. rewrite <- Hav. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma hd_byte_ok : forall E (W : world SEGS) mem (j : Z) (v : nat) (c s : Z),
  ew E 533 = w64 c -> 0 <= c -> 0 <= j -> c + j + 1 <= 2 ^ 64 -> ew E v = w64 s -> 0 <= s < 256 ->
  aview SEGS (w_H W) mem (c + j) = Some s -> region_ok SEGS E (rd W mem) (hd_byte j v).
Proof.
intros E W mem j v c s Hc Hc0 Hj Hcj Hv Hs Hav. unfold w64 in Hc, Hv.
unfold region_ok, hd_byte.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hc, (unsigned_lit_small c) by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
intros i Hi. cbn [YP09.c_off YP09.c_val YP09.c_len cv_len Z.of_N] in *.
assert (Hi0 : i = 0) by lia. subst i.
assert (Hdv : sv_denot E (SOff v 0) = Z_to_bv 64 s).
{ rewrite denot_lit_U, U_SOff, Hv, Z.add_0_r, (unsigned_lit_small s) by lia.
  f_equal. apply zcanon_id. unfold M64. lia. }
unfold cbyte. cbn [YP09.c_val]. rewrite Hdv.
unfold byte_of_word. rewrite (unsigned_lit_small s) by lia. cbn [Z.mul]. rewrite Z.shiftr_0_r.
unfold aview in Hav. destruct (mbyte SEGS (mrestrict (w_H W) mem) (c + j)) as [b|] eqn:Hb; [|discriminate].
cbn [option_map] in Hav. injection Hav as Hav.
exists (Z_to_bv 8 s). split; [reflexivity|].
rewrite !Z.add_0_r, Hb. f_equal. rewrite <- Hav. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma hd_retgt_ok : forall (fq : YK11.FPState) E ss ms (W : world SEGS) (r : bv 5) (q v : nat) (y s : Z),
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> r <> 0%bv ->
  getr (ms_regs ms) r = ew E q -> ew E q = w64 y -> 0 <= y < 2 ^ 64 -> ew E v = w64 s -> 0 <= s < 256 ->
  aview SEGS (w_H W) (ms_mem ms) y = Some s -> all_disjoint E (hd_cell q v) (ss_mem ss) ->
  st_ok_pi (fx := fq) SEGS VAL E (hd_retgt r q v ss) (restrict (w_H W) ms).
Proof.
intros fq E ss ms W r q v y s HS Hr Hq Eq Hy Ev Hs Hav Hd.
pose proof (st_ok_pi_set_reg (fx := fq) E ss _ r (SOff q 0) HS Hr ltac:(rewrite sv_denot_SOff0; exact Hq)) as HS1.
exact (st_ok_pi_add_region (fx := fq) E _ _ (hd_cell q v) HS1 eq_refl
  (hd_cell_ok E W (ms_mem ms) q v y s Eq Hy Ev Hs Hav) Hd).
Qed.

Lemma hd_addb_ok : forall (fq : YK11.FPState) E ss ms (W : world SEGS) (j : Z) (v : nat) (c s : Z),
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) ->
  ew E 533 = w64 c -> 0 <= c -> 0 <= j -> c + j + 1 <= 2 ^ 64 -> ew E v = w64 s -> 0 <= s < 256 ->
  aview SEGS (w_H W) (ms_mem ms) (c + j) = Some s -> all_disjoint E (hd_byte j v) (ss_mem ss) ->
  st_ok_pi (fx := fq) SEGS VAL E (hd_addb j v ss) (restrict (w_H W) ms).
Proof.
intros fq E ss ms W j v c s HS Hc Hc0 Hj Hcj Hv Hs Hav Hd.
assert (Hwf : region_wf (hd_byte j v) = true).
{ unfold region_wf, hd_byte, chunk_inside. cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks forallb
    YP09.c_off YP09.c_len YP09.c_val cv_len Z.of_N].
  apply andb_true_iff; split; [apply andb_true_iff; split; [apply Z.leb_le; lia | reflexivity]|].
  rewrite andb_true_r. apply andb_true_iff; split; [apply andb_true_iff; split; apply Z.leb_le; lia | reflexivity]. }
exact (st_ok_pi_add_region (fx := fq) E _ _ (hd_byte j v) HS Hwf
  (hd_byte_ok E W (ms_mem ms) j v c s Hc Hc0 Hj Hcj Hv Hs Hav) Hd).
Qed.

Definition hd_zone (E : env) (cur nb p cn S A FB : Z) : Prop :=
  ew E 533 = w64 cur /\ ew E AT_STK = w64 S /\ ew E AT_A = w64 A /\ ew E AT_F = w64 FB /\
  ew E AT_SH = w64 (SHADOW_OFF + FB / 8) /\ img_env VAL A_LIM E /\
  4096 <= p /\ p <= cur /\ 0 <= nb /\ cur + nb <= p + cn /\ p + cn <= alloc_ceiling /\
  (p + cn <= kLowShadowBeg \/ kHighMemBeg <= p) /\ (p + cn <= IMG_LO \/ IMG_TOP <= p) /\
  alloc_ceiling + 32768 <= S /\ S <= 2 ^ 47 /\ S - 607 <= A <= S - 576 /\
  4096 <= FB /\ FB + 4096 <= alloc_ceiling /\ FB mod 8 = 0 /\
  (FB + 4096 <= kLowShadowBeg \/ kHighMemBeg <= FB) /\ (p + cn <= FB \/ FB + 4096 <= p).

Ltac hd_dcase Hr E1 :=
  apply andb_true_iff in Hr as [Hl Hh]; apply Z.leb_le in Hl; apply Z.leb_le in Hh;
  rewrite E1, unsigned_lit_small by lia; lia.

Lemma hd_cell_disj : forall E rs (q v : nat) y cur nb p cn S A FB,
  hd_zone E cur nb p cn S A FB -> hd_kinds nb rs = true -> ew E q = w64 y ->
  SHADOW_OFF <= y < SHADOW_OFF + 2 ^ 44 -> (y + 1 <= SHADOW_OFF + FB / 8 \/ SHADOW_OFF + FB / 8 + 512 <= y) ->
  all_disjoint E (hd_cell q v) rs.
Proof.
intros E rs q v y cur nb p cn S A FB Hz Hk Hq Hy Hfy.
destruct Hz as (Ec & ES & EA & EF & ESH & HEI & Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15).
pose proof (pa_obj_img 0 ltac:(lia)) as G0. pose proof (pa_obj_img 12 ltac:(lia)) as G12.
pose proof (HEI (A_OBJ 0) ltac:(cbv; lia)) as E0. pose proof (HEI (A_OBJ 12) ltac:(cbv; lia)) as E12.
pose proof asan_consts as (C1 & _).
unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP, w64 in *.
change (A_OBJ 0) with 241%nat in E0, G0. change (A_OBJ 12) with 253%nat in E12, G12.
unfold hd_kinds in Hk. induction rs as [|r rs IH]; cbn [all_disjoint]; [exact I|].
cbn [forallb] in Hk. apply andb_true_iff in Hk as [Hr Hk]. split; [|exact (IH Hk)].
unfold extent_disjoint. cbn [hd_cell YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Hq, (unsigned_lit_small y) by lia.
destruct (YP09.r_base r) as [b|]; [|discriminate]. cbn [base_val]. revert Hr.
destruct (Nat.eqb_spec b 533) as [->|N1]; intros Hr; cbn in Hr; [hd_dcase Hr Ec|].
revert Hr. destruct (Nat.eqb_spec b AT_STK) as [->|N2]; intros Hr; cbn in Hr; [hd_dcase Hr ES|].
revert Hr. destruct (Nat.eqb_spec b AT_A) as [->|N3]; intros Hr; cbn in Hr; [hd_dcase Hr EA|].
revert Hr. destruct (Nat.eqb_spec b AT_F) as [->|N4]; intros Hr; cbn in Hr; [hd_dcase Hr EF|].
revert Hr. destruct (Nat.eqb_spec b AT_SH) as [->|N5]; intros Hr; cbn in Hr; [hd_dcase Hr ESH|].
revert Hr. destruct (Nat.eqb_spec b 241) as [->|N6]; intros Hr; cbn in Hr.
{ apply andb_true_iff in Hr as [Hl Hh]. apply Z.leb_le in Hl. apply Z.leb_le in Hh. rewrite E0. lia. }
revert Hr. destruct (Nat.eqb_spec b 253) as [->|N7]; intros Hr; cbn in Hr.
{ apply andb_true_iff in Hr as [Hl Hh]. apply Z.leb_le in Hl. apply Z.leb_le in Hh. rewrite E12. lia. }
discriminate.
Qed.

Lemma hd_byte_disj : forall E rs (j : Z) (v : nat) cur p cn S A FB,
  hd_zone E cur (j + 1) p cn S A FB -> hd_kinds j rs = true -> 0 <= j ->
  all_disjoint E (hd_byte j v) rs.
Proof.
intros E rs j v cur p cn S A FB Hz Hk Hj.
destruct Hz as (Ec & ES & EA & EF & ESH & HEI & Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15).
pose proof (pa_obj_img 0 ltac:(lia)) as G0. pose proof (pa_obj_img 12 ltac:(lia)) as G12.
pose proof (HEI (A_OBJ 0) ltac:(cbv; lia)) as E0. pose proof (HEI (A_OBJ 12) ltac:(cbv; lia)) as E12.
pose proof asan_consts as (C1 & _).
assert (Hfb : FB / 8 + 512 <= 2 ^ 44).
{ assert (FB / 8 < 2 ^ 44 - 512) by (apply Z.div_lt_upper_bound; lia). lia. }
assert (Hfb0 : 0 <= FB / 8) by (apply Z.div_pos; lia).
unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, IMG_LO, IMG_TOP, w64 in *.
change (A_OBJ 0) with 241%nat in E0, G0. change (A_OBJ 12) with 253%nat in E12, G12.
unfold hd_kinds in Hk. induction rs as [|r rs IH]; cbn [all_disjoint]; [exact I|].
cbn [forallb] in Hk. apply andb_true_iff in Hk as [Hr Hk]. split; [|exact (IH Hk)].
unfold extent_disjoint. cbn [hd_byte YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Ec, (unsigned_lit_small cur) by lia.
destruct (YP09.r_base r) as [b|]; [|discriminate]. cbn [base_val]. revert Hr.
destruct (Nat.eqb_spec b 533) as [->|N1]; intros Hr; cbn in Hr; [hd_dcase Hr Ec|].
revert Hr. destruct (Nat.eqb_spec b AT_STK) as [->|N2]; intros Hr; cbn in Hr; [hd_dcase Hr ES|].
revert Hr. destruct (Nat.eqb_spec b AT_A) as [->|N3]; intros Hr; cbn in Hr; [hd_dcase Hr EA|].
revert Hr. destruct (Nat.eqb_spec b AT_F) as [->|N4]; intros Hr; cbn in Hr; [hd_dcase Hr EF|].
revert Hr. destruct (Nat.eqb_spec b AT_SH) as [->|N5]; intros Hr; cbn in Hr; [hd_dcase Hr ESH|].
revert Hr. destruct (Nat.eqb_spec b 241) as [->|N6]; intros Hr; cbn in Hr.
{ apply andb_true_iff in Hr as [Hl Hh]. apply Z.leb_le in Hl. apply Z.leb_le in Hh. rewrite E0. lia. }
revert Hr. destruct (Nat.eqb_spec b 253) as [->|N7]; intros Hr; cbn in Hr.
{ apply andb_true_iff in Hr as [Hl Hh]. apply Z.leb_le in Hl. apply Z.leb_le in Hh. rewrite E12. lia. }
discriminate.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Definition hd_post (cx : dcx) (h i : Z) : world SEGS -> config -> Prop :=
  fun W' c' => exit_pre B MT XM_LIB RLO RHI tfib_K cx h W' c' \/ exists n now op,
    (op mod 4 = 3 /\ arm3_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W' c') \/
    (op mod 4 <> 3 /\ rec_in B MT XM_LIB RLO RHI tfib_K cx h i n now op W' c').

Definition hd_ctx (cx : dcx) (h i n now : Z) (ly3 : alayout) (S3 : astate) (W : world SEGS)
  (mem3 : word -> option byte) (md3 : Model) (k acc : Z) (regs : bvmap 5 word) (E0 : env) : Prop :=
  d_base B MT XM_LIB RLO RHI tfib_K cx /\
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md3 k /\
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] /\
  0 <= k <= EV_HEAD i /\ st_nev S3 <= st_nev (c_S cx) + EV_HEAD i /\
  mo_le MT (c_S cx) S3 acc /\ acc <= ACC_HEAD MT i /\
  0 <= i < MAX_OPS /\ 0 <= n /\ 0 <= now < 2 ^ 64 /\
  d_rH B cx h i n now regs /\ d_body B cx h n [] dsh_loop ly3 S3 W mem3 /\
  d_E cx E0 /\ Forall (region_ok SEGS E0 (rd W mem3)) (d_regions cx dsh_loop) /\
  rdword (aview SEGS (w_H W) mem3) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) =
    Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)).

Lemma hd_cell_val : AR_laws SEGS B -> forall ly S (W : world SEGS) mem md p n x,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= x < p + n ->
  aview SEGS (w_H W) mem (yh_caddr x) = Some (yh_cell p n x).
Proof.
intros LAWS ly S W mem md p n x HAR Hin Hx.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (H16 & H4096 & Hc & Hia & Hpres & Hn).
destruct (al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as (Hbs & _).
unfold block_shadow in Hbs. destruct Hbs as (Hp8 & Hn0 & Hbytes).
assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); [lia | reflexivity]).
rewrite Hrq in *.
assert (Hsplit : x / 8 = p / 8 + (x - p) / 8)
  by (rewrite <- (yh_div8_shift p (x - p) Hp8); f_equal; lia).
assert (Hidx : 0 <= (x - p) / 8 < (n + 7) / 8).
{ split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as Dn.
  pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). lia. }
pose proof (Hbytes ((x - p) / 8) Hidx) as Hb.
unfold shadow_of_addr in Hb. unfold yh_caddr, yh_cell.
replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + p / 8 + (x - p) / 8) by lia.
exact Hb.
Qed.
End h.
End f.
End d.
