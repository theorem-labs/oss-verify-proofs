(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fs program part, READER lane (a Theorem Labs lane): the CALL-SITE facts of parse_items' member path, as
   the measured segments (FSW_parse_items_seg.v) leave them and a Theorem Labs lane's call steps (FSW_parse_items_grow.v /
   _calls.v) take them: the frame's words as values (pi_frame0 / pi_frameL, the val_mem form FSW_pj_set.v's
   pj_set_frame uses), and from them the chunk lists pi_cs0 / pi_csL under any resume env whose atoms 8 / 20 / 32 and
   xatom 3 .. 15 hold q, v, the shadow base and the saved registers.
   Rule 24: no function is proved in this file. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.omx_clap_core.fuzz_state.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSW_K FSW_ret FSW_pj
FSW_parse_items_tbl FSW_parse_items FSW_parse_items_grow FSW_parse_items_calls FSW_parse_items_kit
FSW_parse_items_seg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (S0): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= the frame's words ================= *)
(* the ASan shadow address of x, as the walk computes it (pi_shv) *)
Definition pi_sh (x : Z) : Z := x / 8 + SHADOW_OFF.
(* the thirteen saved registers at sp0 - 8 .. sp0 - 104 (pi_saved order), the prologue's frame *)
Definition pi_frame0 (m : word -> option byte) (sp0 : Z) (xr : list word) : Prop :=
  Forall (fun j => val_mem tfibsegs m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (nth j xr (Z_to_bv 64 0)))) (seq 0 13).
(* ... and the member loop's four locals at sp0 - 136 .. sp0 - 112 (the set-up 0x84b70 .. 0x84ba4) *)
Definition pi_frameL (m : word -> option byte) (sp0 : Z) (xr : list word) (q v : Z) : Prop :=
  pi_frame0 m sp0 xr /\
  val_mem tfibsegs m (sp0 - 136) 8 (q + 8) /\ val_mem tfibsegs m (sp0 - 128) 8 (pi_sh (q + 16)) /\
  val_mem tfibsegs m (sp0 - 120) 8 (pi_sh (v + 24)) /\ val_mem tfibsegs m (sp0 - 112) 8 (v + 32).

(* the shadow address's denotation, for an atom below 2 ^ 47 *)
Lemma pi_shv_denot : forall E b x c, ew E b = Z_to_bv 64 x -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  0 <= x < 2 ^ 47 -> x + c < 2 ^ 47 -> 0 <= x + c ->
  sv_denot E (pi_shv b c) = Z_to_bv 64 (pi_sh (x + c)).
Proof.
intros E b x c Hb H32 Hx Hxc Hxc0. apply bv_eq. unfold pi_shv, pi_sh.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff b c) (SLit 3)) (SOff 32 0))))
  with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff b c) (SLit 3)) (SOff 32 0))).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E b x c Hb ltac:(lia) ltac:(lia)).
rewrite (U_atom E 32 SHADOW_OFF H32 ltac:(unfold SHADOW_OFF; lia)). rewrite U_SLit.
rewrite (zcanon_id 3) by (unfold M64; lia).
change 63 with (Z.ones 6). rewrite Z.land_ones by lia. rewrite (Z.mod_small 3) by lia.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hd : 0 <= (x + c) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (zcanon_id ((x + c) / 8)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia).
rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
Qed.

(* the prologue's chunks under a resume env holding the saved registers at xatom 3 .. 15 *)
Lemma pi_cs0_ok : forall E m sp0 xr, length xr = 13%nat ->
  (forall j, (j < 13)%nat -> ew E (xatom (3 + j)) = nth j xr (Z_to_bv 64 0)) ->
  pi_frame0 m sp0 xr -> Forall (YP09.chunk_ok tfibsegs E m (sp0 - 144)) pi_cs0.
Proof.
intros E m sp0 xr Hl HX HF. unfold pi_frame0 in HF. rewrite Forall_forall in HF.
unfold pi_cs0. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
apply (chunk_ok_val tfibsegs E m (sp0 - 144) (136 - 8 * Z.of_nat j) 8 (SOff (xatom (3 + j)) 0)
  (bv_unsigned (nth j xr (Z_to_bv 64 0)))).
- rewrite fsw_SOff0, HX by lia. symmetry. apply Z_to_bv_bv_unsigned.
- apply u64_range.
- cbn. lia.
- replace (sp0 - 144 + (136 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia.
  apply HF. apply in_seq. lia.
Qed.
Lemma pi_csL_ok : forall E m sp0 xr q v, length xr = 13%nat ->
  (forall j, (j < 13)%nat -> ew E (xatom (3 + j)) = nth j xr (Z_to_bv 64 0)) ->
  ew E 8 = Z_to_bv 64 q -> ew E 20 = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  0 <= q -> q + 24 <= 2 ^ 47 -> 0 <= v -> v + 56 <= 2 ^ 47 ->
  pi_frameL m sp0 xr q v -> Forall (YP09.chunk_ok tfibsegs E m (sp0 - 144)) pi_csL.
Proof.
intros E m sp0 xr q v Hl HX E8 E20 E32 Hq0 Hq1 Hv0 Hv1 (HF0 & F8 & F16 & F24 & F32).
unfold pi_csL. apply Forall_app. split; [|exact (pi_cs0_ok E m sp0 xr Hl HX HF0)].
assert (Hsh : forall x, 0 <= x < 2 ^ 47 -> 0 <= pi_sh x < 2 ^ 64).
{ intros x Hx. unfold pi_sh, SHADOW_OFF. split; [pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)); lia|].
  pose proof (Z.div_le_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val tfibsegs E m (sp0 - 144) 8 8 (SOff 8 8) (q + 8));
    [apply bv_eq; rewrite denot_SOff, E8, !unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia
    | cbn; lia | cbn; lia | replace (sp0 - 144 + 8) with (sp0 - 136) by lia; exact F8].
- apply (chunk_ok_val tfibsegs E m (sp0 - 144) 16 8 (pi_shv 8 16) (pi_sh (q + 16)));
    [apply pi_shv_denot; [exact E8 | exact E32 | lia | lia | lia]
    | cbn; pose proof (Hsh (q + 16) ltac:(lia)); lia | cbn; lia
    | replace (sp0 - 144 + 16) with (sp0 - 128) by lia; exact F16].
- apply (chunk_ok_val tfibsegs E m (sp0 - 144) 24 8 (pi_shv 20 24) (pi_sh (v + 24)));
    [apply pi_shv_denot; [exact E20 | exact E32 | lia | lia | lia]
    | cbn; pose proof (Hsh (v + 24) ltac:(lia)); lia | cbn; lia
    | replace (sp0 - 144 + 24) with (sp0 - 120) by lia; exact F24].
- apply (chunk_ok_val tfibsegs E m (sp0 - 144) 32 8 (SOff 20 32) (v + 32));
    [apply bv_eq; rewrite denot_SOff, E20, !unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia
    | cbn; lia | cbn; lia | replace (sp0 - 144 + 32) with (sp0 - 112) by lia; exact F32].
Qed.

(* the resume env of every call step holds the saved registers at xatom 3 .. 15 *)
Lemma pi_pig_xs_saved : forall regs' p e d xr k' y' n cap' j, length xr = 13%nat -> (j < 13)%nat ->
  ew (Ereg regs' (fs_extraT ++ pig_xs p e d xr k' y' n cap')) (xatom (3 + j)) = nth j xr (Z_to_bv 64 0).
Proof.
intros regs' p e d xr k' y' n cap' j Hl Hj. rewrite fsw_ew_xatom. unfold pig_xs.
rewrite app_nth2 by (cbn [length]; lia). cbn [length]. replace (3 + j - 3)%nat with j by lia.
rewrite app_nth1 by lia. reflexivity.
Qed.
Lemma pi_ps_xs_saved : forall regs' p e d xr k' y' n cap' a kl j, length xr = 13%nat -> (j < 13)%nat ->
  ew (Ereg regs' (fs_extraT ++ pic_xs_ps p e d xr k' y' n cap' a kl)) (xatom (3 + j)) = nth j xr (Z_to_bv 64 0).
Proof.
intros regs' p e d xr k' y' n cap' a kl j Hl Hj. rewrite fsw_ew_xatom. unfold pic_xs_ps.
rewrite app_nth1 by (unfold pig_xs; rewrite !length_app; cbn [length]; lia).
exact (eq_trans (eq_sym (fsw_ew_xatom regs' _ (3 + j))) (pi_pig_xs_saved regs' p e d xr k' y' n cap' j Hl Hj)).
Qed.
