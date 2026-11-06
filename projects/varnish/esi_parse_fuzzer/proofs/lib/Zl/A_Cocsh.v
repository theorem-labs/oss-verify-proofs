(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Stgw7 V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp0e6 AIcpya4 AIcp3q7 AIcpii0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpii0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_La0bg A_Img.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.

Module DA_R1e4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Img.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Set Warnings "-abstract-large-number".
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma rodata_bytes : forall (v : word -> option byte) a bs,
  mem_inv rsegs v -> ro_bytes_b rsegs a bs = true -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  bytes_at rsegs v a bs.
Proof.
  intros v a bs MI RB A0 A1. apply (ro_bytes_at rsegs v a bs MI A0 A1). apply ro_bytes_b_sound. exact RB.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rod_index a l i :=
  lazymatch l with
  | (a, _) :: _ => i
  | _ :: ?r => rod_index a r constr:(S i)
  end.
Ltac rod_in_table :=
  lazymatch goal with
  | |- In (?a, ?n) ?l =>
      let l' := eval red in l in
      let i := rod_index a l' constr:(O) in
      exact (@nth_error_In _ l i (a, n) eq_refl)
  end.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma zstretch_bytes_gen : forall v (Z0 : Z) (n : nat),
  consts_hold LPA v -> In (Z0, n) pa_zero_shadow -> bytes_at rsegs v Z0 (zeros n).
Proof.
  intros v Z0 n CH HIn. unfold consts_hold in CH. rewrite Forall_forall in CH.
  apply (CH (Z0, zeros n)). change (cl_consts LPA) with pa_consts. unfold pa_consts. rewrite !in_app_iff. right. right.
  unfold pa_zshadow. apply (in_map (fun p : Z * nat => (fst p, repeat (Z_to_bv 8 0) (snd p))) pa_zero_shadow (Z0, n)). exact HIn.
Qed.

(* [comment removed for export] *)
Lemma zeros_window : forall (v : word -> option byte) Z0 (N : Z) A (w : nat),
  bytes_at rsegs v Z0 (zeros (Z.to_nat N)) -> 0 <= N -> Z0 <= A -> A + Z.of_nat w <= Z0 + N -> bytes_at rsegs v A (zeros w).
Proof.
  intros v Z0 N A w (B0 & B1 & B) N0 LO HI. unfold zeros in *. rewrite repeat_length in B1, B. rewrite Z2Nat.id in B1 by exact N0.
  split; [lia|]. split; [rewrite repeat_length; lia|]. rewrite repeat_length. intros i Hi.
  replace (A + Z.of_nat i) with (Z0 + Z.of_nat (Z.to_nat (A - Z0) + i)) by lia.
  rewrite (B (Z.to_nat (A - Z0) + i)%nat) by lia.
  rewrite !(nth_error_repeat (Z_to_bv 8 0)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zeros_present : forall (v : word -> option byte) Z0 (N : Z) a,
  bytes_at rsegs v Z0 (zeros (Z.to_nat N)) -> 0 <= N -> 0x60a000 <= Z0 -> Z0 <= a < Z0 + N -> v (Z_to_bv 64 a) <> None.
Proof.
  intros v Z0 N a (B0 & B1 & B) N0 HZ Ha. unfold zeros in *. rewrite repeat_length in B1, B. rewrite Z2Nat.id in B1 by exact N0.
  specialize (B (Z.to_nat (a - Z0)) ltac:(lia)). rewrite Z2Nat.id in B by lia. replace (Z0 + (a - Z0)) with a in B by lia.
  rewrite (nth_error_repeat (Z_to_bv 8 0)) in B by lia.
  rewrite pa_mrd_overlay in B by (rewrite unsigned_lit by lia; lia). unfold wa in B. rewrite B. discriminate.
Qed.

(* [comment removed for export] *)
Lemma zstretch_range_ok : forall v (Z0 N a k : Z),
  bytes_at rsegs v Z0 (zeros (Z.to_nat N)) -> 0 <= N -> 0x60a000 <= Z0 ->
  1 <= k -> 0 <= a -> a + k + 8 <= 0x7fff8000 ->
  Z0 <= sha a - sha a mod 8 -> sha (a + k - 1) - sha (a + k - 1) mod 8 + 8 <= Z0 + N ->
  range_ok v a k.
Proof.
  intros v Z0 N a k ZB N0 ZLO K A0 AHI WLO WHI.
  assert (MONO : sha a <= sha (a + k - 1)) by (unfold sha; Z.div_mod_to_equations; lia).
  pose proof (Z.mod_pos_bound (sha a) 8 ltac:(lia)) as M1. pose proof (Z.mod_pos_bound (sha (a + k - 1)) 8 ltac:(lia)) as M2.
  split; [| split; [| split]].
  - left. lia.
  - assert (NG : 0 <= (a + k - 1) / 8 - a / 8) by (Z.div_mod_to_equations; lia).
    destruct (Z_of_nat_complete _ NG) as [ng NGE].
    exists ng, 0. split; [exact NGE|]. split; [| left; reflexivity].
    replace (zeros ng ++ [Z_to_bv 8 0]) with (zeros (S ng)).
    2:{ unfold zeros. rewrite <- repeat_cons. reflexivity. }
    apply (zeros_window v Z0 N); [exact ZB| lia| unfold sha, shadow_off in *; lia|].
    rewrite Nat2Z.inj_succ, <- NGE. unfold sha, shadow_off in *. lia.
  - intros i Hi. apply (zeros_present v Z0 N); [exact ZB| lia| lia| unfold sha, shadow_off in *; Z.div_mod_to_equations; lia].
  - intros i Hi. apply (zeros_present v Z0 N); [exact ZB| lia| lia| unfold sha, shadow_off in *; Z.div_mod_to_equations; lia].
Qed.

(* [comment removed for export] *)
Lemma rodata_range_ok : forall v a k, consts_hold LPA v -> 1 <= k -> 0x10000 <= a -> a + k <= 0x216d8 -> range_ok v a k.
Proof.
  intros v a k CH K LO HI.
  pose proof (zstretch_bytes_gen v 0x7fffa000 8930 CH ltac:(rod_in_table)) as ZB.
  change (zeros 8930) with (zeros (Z.to_nat 8930)) in ZB.
  apply (zstretch_range_ok v 0x7fffa000 8930 a k ZB); try lia; unfold sha, shadow_off; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_zeros_sub : forall m Z0 n d k,
  bytes_at rsegs m Z0 (zeros n) -> 0 <= d -> d + Z.of_nat k <= Z.of_nat n -> bytes_at rsegs m (Z0 + d) (zeros k).
Proof.
  intros m Z0 n d k (H0 & H1 & H) Hd Hk. unfold zeros in *. rewrite repeat_length in H1, H.
  split; [lia|]. split; [rewrite repeat_length; lia|]. rewrite repeat_length.
  intros i Hi. rewrite nth_error_repeat by exact Hi.
  specialize (H (Z.to_nat (d + Z.of_nat i)) ltac:(lia)). rewrite Z2Nat.id in H by lia.
  rewrite nth_error_repeat in H by lia. replace (Z0 + d + Z.of_nat i) with (Z0 + (d + Z.of_nat i)) by lia. exact H.
Qed.

(* [comment removed for export] *)
Lemma stage_range_ok : forall v a k, consts_hold LPA v -> 1 <= k -> 0x5d7210 <= a -> a + k <= 0x5e7210 -> range_ok v a k.
Proof.
  intros v a k CH K LO HI.
  assert (HIn : In (0x8000e2a0, 682921%nat) pa_zero_shadow) by rod_in_table.
  pose proof (zstretch_bytes_gen v 0x8000e2a0 682921 CH HIn) as ZB0.
  assert (EN : Z.of_nat 682921%nat = 682921) by (vm_compute; reflexivity).
  pose proof (bytes_at_zeros_sub v 0x8000e2a0 682921%nat 674720 8201%nat ZB0 ltac:(lia) ltac:(rewrite EN; cbn; lia)) as ZB.
  clear ZB0 EN. change (0x8000e2a0 + 674720) with 0x800b2e40 in ZB.
  change (zeros 8201) with (zeros (Z.to_nat 8201)) in ZB.
  apply (zstretch_range_ok v 0x800b2e40 8201 a k ZB); try lia; unfold sha, shadow_off; Z.div_mod_to_equations; lia.
Qed.

Lemma bss_range_ok : forall v a k, consts_hold LPA v -> 1 <= k -> 0x5e72c0 <= a -> a + k <= 0x609f00 -> range_ok v a k.
Proof.
  intros v a k CH K LO HI.
  assert (HIn : In (0x800b4e58, 17832%nat) pa_zero_shadow) by rod_in_table.
  pose proof (zstretch_bytes_gen v 0x800b4e58 17832 CH HIn) as ZB.
  change (zeros 17832) with (zeros (Z.to_nat 17832)) in ZB.
  apply (zstretch_range_ok v 0x800b4e58 17832 a k ZB); try lia; unfold sha, shadow_off; Z.div_mod_to_equations; lia.
Qed.

End CEIL.
End DA_R1e4.

Module A_Henv.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Img.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma bss_vsc_layout :
    cl_rw_lo LPA <= vi_bss_vsc VIA /\ vi_bss_vsc VIA + 8 <= cl_image_hi LPA /\
    (forall i, 0 <= i < 8 -> ~ cl_static LPA (vi_bss_vsc VIA + i)) /\
    (vi_bss_vsc VIA + 8 <= cl_errno LPA \/ cl_errno LPA + 4 <= vi_bss_vsc VIA).
  Proof.
    cbn [cl_rw_lo cl_image_hi cl_static cl_errno LPA vi_bss_vsc VIA]. unfold pa_static.
    split; [lia|]. split; [lia|]. split; [intros i Hi; lia| lia].
  Qed.
  Lemma bss_cp_layout :
    cl_rw_lo LPA <= vi_bss_cp VIA /\ vi_bss_cp VIA + 8 <= cl_image_hi LPA /\
    (forall i, 0 <= i < 8 -> ~ cl_static LPA (vi_bss_cp VIA + i)) /\
    (vi_bss_cp VIA + 8 <= cl_errno LPA \/ cl_errno LPA + 4 <= vi_bss_cp VIA).
  Proof.
    cbn [cl_rw_lo cl_image_hi cl_static cl_errno LPA vi_bss_cp VIA]. unfold pa_static.
    split; [lia|]. split; [lia|]. split; [intros i Hi; lia| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma glob_ok_acall : forall H A A' m md v' sp win Vc N,
    ainv A m md -> hframe LPA A H -> cframe LPA (owned A) (owned A') sp win Vc N (aview A m) v' ->
    glob_ok LPA VIA H (aview A m) -> alloc_ceiling <= sp - win ->
    (forall a, (0x5e7240 <= a < 0x5e7240 + 8 \/ 0x5e7260 <= a < 0x5e7260 + 8 \/
                h_cp H <= a < h_cp H + 752 \/ h_vsc H + 1304 <= a < h_vsc H + 1320) -> ~ Vc a) ->
    glob_ok LPA VIA H v'.
  Proof.
    intros H A A' m md v' sp win Vc N AI0 HF CF GL Hw NV.
    pose proof bss_vsc_layout as (R1 & R2 & R3 & R4). pose proof bss_cp_layout as (R5 & R6 & R7 & R8).
    eapply glob_ok_ccall; [exact AI0| exact HF| exact CF| exact GL| exact Hw| exact R1| exact R2| exact R3| exact R4
                          | exact R5| exact R6| exact R7| exact R8|].
    intros a Ha. apply NV. cbn [vi_bss_vsc vi_bss_cp VIA] in Ha. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Lemma hshadow_acall0 : forall A A' m md v' sp win N H,
    ainv A m md -> hframe LPA A H -> cframe LPA (owned A) (owned A') sp win nowhere N (aview A m) v' ->
    hshadow LPA H (aview A m) -> alloc_ceiling <= sp - win ->
    hshadow LPA H v'.
  Proof.
    intros A A' m md v' sp win N H AI0 HF CF HS Hw.
    eapply hshadow_ccall; [exact AI0| exact HF| exact CF| exact HS| exact Hw| intros x _ X; exact X].
  Qed.

  (* [comment removed for export] *)
  Lemma hshadow_acall_blk : forall A A' m md v' sp win N H q k,
    ainv A m md -> hframe LPA A H -> cframe LPA (owned A) (owned A') sp win (newblk q k) N (aview A m) v' ->
    hshadow LPA H (aview A m) -> alloc_ceiling <= sp - win -> a_live A q = Some k ->
    hshadow LPA H v'.
  Proof.
    intros A A' m md v' sp win N H q k AI0 HF CF HS Hw LV. destruct HF as [age HFR].
    eapply hshadow_ccall; [exact AI0| exists age; exact HFR| exact CF| exact HS| exact Hw|].
    intros x Hx. change (HFSIZE / 8) with (fsize HCLASS / 8) in Hx.
    intros X. exact (newblk_avoids_fshadow LPA A m md q k (h_ff H) HCLASS age x AI0 LV HFR X Hx).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  Lemma glob_ok_acall_blk : forall H A A' m md v' sp win N q k,
    ainv A m md -> hframe LPA A H -> cframe LPA (owned A) (owned A') sp win (newblk q k) N (aview A m) v' ->
    glob_ok LPA VIA H (aview A m) -> alloc_ceiling <= sp - win -> a_live A q = Some k ->
    glob_ok LPA VIA H v'.
  Proof.
    intros H A A' m md v' sp win N q k AI0 HF CF GL Hw LV. pose proof HF as [age HFR].
    pose proof (henv_geom_of_frame LPA A m md H AI0 HF) as (G1 & G2 & G3).
    destruct (live_geom LPA A m md q k AI0 LV) as (K0 & Q16 & QLO & QHI & _).
    pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS age q k AI0 HFR LV) as DJ.
    change (fsize HCLASS) with 8192 in DJ. unfold HFSIZE in G3.
    pose proof alloc_ceiling_num as ACV. unfold kHighMemBeg in *.
    pose proof (app_facts LPA (h_ff H) 8192 G2) as (GB & _ & GNS & _). pose proof SHMAX_below_highmem as SBH. unfold kHighMemBeg in SBH.   (* [comment removed for export] *)
    eapply glob_ok_acall; [exact AI0| exact HF| exact CF| exact GL| exact Hw|].
    intros a Ha X. unfold h_cp, h_vsc in Ha. unfold newblk, blk in X.
    pose proof (app_facts LPA q k QLO) as (QB & QIMG & QNS & _). unfold off_image in QIMG. cbn [cl_image_lo cl_image_hi LPA] in QIMG. pose proof (app_sh_facts LPA q k QLO) as (SQLO & SB & SB3 & SQNS). rewrite SHMAX_val in SB, SB3, SBH.   (* [comment removed for export] *)
    lia.
  Qed.

  (* [comment removed for export] *)
  Lemma stack_shadow_open : forall v SB N lo hi, stack_shadow LPA v SB N lo hi -> 0 <= lo ->
    exists P zs, bytes_at rsegs v SB zs /\ zs = repeat (Z_to_bv 8 0) (Z.to_nat N) /\ Z.of_nat (length zs) = N /\
      sh P = SB /\ P mod 8 = 0 /\ 0 <= P /\ P <= lo /\ hi <= P + 8 * Z.of_nat (Z.to_nat N) /\
      sh alloc_ceiling <= SB (* [comment removed for export] *) /\ SB + N <= kHighMemBeg.
  Proof.
    intros v SB N lo hi (B & N0 & Lq & Hh & SLO & T) LO0.
    pose proof alloc_ceiling_num as ACV.
    assert (SLO' : 17591916560384 + 2147450880 <= SB) by (unfold sh, kShadowOffset in SLO; Z.div_mod_to_equations; lia).
    exists ((SB - kShadowOffset) * 8), (repeat (Z_to_bv 8 0) (Z.to_nat N)).
    split; [exact B|]. split; [reflexivity|]. split; [rewrite repeat_length; lia|].
    unfold sh, kShadowOffset in *.
    split; [rewrite Z.div_mul by lia; lia|].
    split; [apply Z_mod_mult|].
    split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
    split; [exact SLO| exact T].
  Qed.

  (* [comment removed for export] *)

  Lemma stack_shadow_pure : forall v SB N lo hi, stack_shadow LPA v SB N lo hi ->
    0 <= N /\ SB <= sh lo /\ sh hi < SB + N /\ sh alloc_ceiling <= SB /\ SB + N <= kHighMemBeg.
  Proof. intros v SB N lo hi (B & P). exact P. Qed.

  (* [comment removed for export] *)
  Lemma crange_sshadow : forall A m md SB N zs,
    ainv A m md -> bytes_at rsegs (aview A m) SB zs -> Z.of_nat (length zs) = N ->
    sh alloc_ceiling <= SB (* [comment removed for export] *) -> SB + N <= kHighMemBeg ->
    crange A (aview A m) SB (Z.of_nat (length zs)).
  Proof.
    intros A m md SB N zs AI0 B LZ SLO T. rewrite LZ.
    pose proof alloc_ceiling_num as ACV. unfold kHighMemBeg in T.
    assert (SLO' : 17591916560384 + 2147450880 <= SB) by (unfold sh, kShadowOffset in SLO; Z.div_mod_to_equations; lia).
    pose proof (bytes_at_mapped LPA (aview A m) SB _ B) as MP. rewrite LZ in MP.
    split; [lia|]. split; [lia|].
    intros i Hi. split; [|split].
    - apply (as_owned_not_stack_shadow LPA A m md); [exact AI0|]. unfold kHighMemBeg. lia.
    - cbn [cl_errno LPA]. lia.
    - left. apply MP; [| exact Hi]. right. cbn [cl_image_hi LPA]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma henv_ok_acall0 : forall H A A' m md v' sp win N,
    ainv A m md -> cframe LPA (owned A) (owned A') sp win nowhere N (aview A m) v' ->
    henv_ok LPA VIA H A (aview A m) -> alloc_ceiling <= sp - win ->
    (forall ff, a_frame A' ff = a_frame A ff) ->
    henv_ok LPA VIA H A' v'.
  Proof.
    intros H A A' m md v' sp win N AI0 CF HE Hw FS.
    pose proof bss_vsc_layout as (R1 & R2 & R3 & R4). pose proof bss_cp_layout as (R5 & R6 & R7 & R8).
    eapply henv_ok_ccall; [exact AI0| exact CF| exact HE| exact Hw| exact FS| exact R1| exact R2| exact R3| exact R4
                          | exact R5| exact R6| exact R7| exact R8| intros a _ X; exact X].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma vep_obj_munch : forall A W (v v' : mem) VEP vv tag q,
    vep_obj LPA A v VEP vv tag q -> munch W v v' -> wmono rsegs v v' ->
    (forall a, VEP <= a < VEP + 312 -> outside W a) -> vep_obj LPA A v' VEP vv tag q.
  Proof.
    intros A W v v' VEP vv tag q (LV & C & T8 & PW) MU WM OUT.
    split; [exact LV|]. split; [| split; [exact T8| exact PW]].
    eapply (rw_cells_munch LPA); [exact C| exact MU| exact WM|].
    rewrite (vep_cells_size vv tag q T8 PW). change (Z.of_nat 312) with 312. exact OUT.
  Qed.

  Lemma vsb_obj_munch : forall A W v v' S vr fin,
    vsb_obj LPA A v S vr fin -> munch W v v' -> wmono rsegs v v' ->
    (forall a, (S <= a < S + 40 \/ vb_buf vr <= a < vb_buf vr + vb_size vr) -> outside W a) ->
    vsb_obj LPA A v' S vr fin.
  Proof.
    intros A W v v' S vr fin (VC & VI & LS & LB & NE & (bs & [UB UW] & LEN & NUL)) MU WM OUT.
    split; [|split; [exact VI| split; [exact LS| split; [exact LB| split; [exact NE|]]]]].
    - eapply (rw_cells_munch LPA); [exact VC| exact MU| exact WM|]. rewrite vsb_cells_size. intros a Ha. apply OUT. left. lia.
    - exists bs. split; [|split; [exact LEN| exact NUL]]. split.
      + eapply (bytes_at_munch LPA); [exact UB| exact MU|]. intros a Ha. apply OUT. right. lia.
      + eapply wr_at_transport; [exact UW| exact WM].
  Qed.

  (* [comment removed for export] *)
  Lemma vsb_obj_ccall : forall A A' m md v' sp win Vc N S vr fin,
    ainv A m md -> cframe LPA (owned A) (owned A') sp win Vc N (aview A m) v' ->
    vsb_obj LPA A (aview A m) S vr fin -> alloc_ceiling <= sp - win ->
    a_live A' S = Some 40 -> a_live A' (vb_buf vr) = Some (vb_size vr) ->
    (forall a, (S <= a < S + 40 \/ vb_buf vr <= a < vb_buf vr + vb_size vr) -> ~ Vc a) ->
    vsb_obj LPA A' v' S vr fin.
  Proof.
    intros A A' m md v' sp win Vc N S vr fin AI0 CF VO Hw LS' LB' NV.
    pose proof VO as (VC & VI & LS & LB & NE & VB).
    destruct (live_geom LPA A m md S 40 AI0 LS) as (_ & _ & _ & SHI & _).
    destruct (live_geom LPA A m md _ _ AI0 LB) as (B0 & _ & _ & BHI & _).
    split; [|split; [exact VI| split; [exact LS'| split; [exact LB'| split; [exact NE|]]]]].
    - eapply (rw_cells_ccall LPA A A' sp win Vc N _ v' CF); [| | exact VC]; rewrite vsb_cells_size.
      + eapply crange_block; [exact AI0| exact LS| lia| cbn; lia| cbn; lia].
      + split; [left; cbn; lia|]. intros i Hi. apply NV. left. cbn in Hi. lia.
    - eapply (vsb_buf_ok_ccall LPA A A' m (aview A m) v' sp win Vc N vr fin md AI0 eq_refl LB CF); [lia| | exact VB].
      intros a Ha. apply NV. right. exact Ha.
  Qed.
  (* [comment removed for export] *)
  Lemma henv_ok_acall_gen : forall H A A' m md v' sp win Vc N,
    ainv A m md -> cframe LPA (owned A) (owned A') sp win Vc N (aview A m) v' ->
    henv_ok LPA VIA H A (aview A m) -> alloc_ceiling <= sp - win ->
    (forall ff k age, a_frame A ff = Some (k, age) -> exists age', a_frame A' ff = Some (k, age')) ->
    (forall a, Vc a -> exists q k, a_live A q = Some k /\ (q <= a < q + k \/ sh q <= a < sh q + (k + 7) / 8)) ->
    henv_ok LPA VIA H A' v'.
  Proof.
    intros H A A' m md v' sp win Vc N AI0 CF HE Hw FS HV.
    pose proof HE as (HF & GL & HO & HS). pose proof HF as [age HFR].
    pose proof (henv_geom_of_frame LPA A m md H AI0 HF) as (G1 & G2 & G3). unfold HFSIZE in G3.
    pose proof alloc_ceiling_num as ACV.
    pose proof (app_facts LPA (h_ff H) 8192 G2) as (GB & _ & GNS & _). pose proof (app_sh_facts LPA (h_ff H) 8192 G2) as (SFLO & SF & SF3 & SFNS).   (* [comment removed for export] *)
    change ((8192 + 7) / 8) with 1024 in SF, SFNS. rewrite SHMAX_val in SF, SF3.
    assert (Q8 : (h_ff H) mod 8 = 0).
    { pose proof (Z.div_mod (h_ff H) 4096 ltac:(lia)) as Dv. rewrite G1, Z.add_0_r in Dv. rewrite Dv.
      replace (4096 * (h_ff H / 4096)) with ((512 * (h_ff H / 4096)) * 8) by lia. apply Z_mod_mult. }
    assert (NV : forall a, (0x5e7240 <= a < 0x5e7240 + 8 \/ 0x5e7260 <= a < 0x5e7260 + 8 \/
                            h_ff H <= a < h_ff H + 8192 \/ sh (h_ff H) <= a < sh (h_ff H) + 1024) -> ~ Vc a).
    { intros a Ha X. destruct (HV a X) as (q & k & LV & IN).
      destruct (live_geom LPA A m md q k AI0 LV) as (K0 & Q16 & QLO & QHI & _).
      pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS age q k AI0 HFR LV) as DJ.
      change (fsize HCLASS) with 8192 in DJ.
      pose proof (app_facts LPA q k QLO) as (QB & QIMG & QNS & _). unfold off_image in QIMG. cbn [cl_image_lo cl_image_hi LPA] in QIMG. pose proof (app_sh_facts LPA q k QLO) as (SQLO & SB & SB3 & SQNS).   (* [comment removed for export] *)
    pose proof SHMAX_below_highmem as SBH. unfold kHighMemBeg in SBH. rewrite SHMAX_val in SB, SB3, SBH.
      unfold kHighMemBeg in *.
      destruct IN as [IN|IN]; [lia|].
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [lia|lia|lia|].
      destruct DJ as [D|D].
      - pose proof (sh_sep (h_ff H) 8192 q ltac:(lia) ltac:(exact (mod8_of_mod16 q Q16)) ltac:(lia)) as SS.
        change ((8192 + 7) / 8) with 1024 in SS. lia.
      - pose proof (sh_sep q k (h_ff H) ltac:(lia) Q8 ltac:(lia)) as SS. lia. }
    split; [eapply hframe_keep_aged; [exact HF| exact FS]|]. split; [|split].
    - eapply glob_ok_acall; [exact AI0| exact HF| exact CF| exact GL| exact Hw|].
      intros a Ha. apply NV. unfold h_cp, h_vsc in Ha. lia.
    - eapply hobj_ok_ccall; [exact AI0| exact HF| exact CF| exact HO| exact Hw|].
      intros a Ha. apply NV. unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha. lia.
    - eapply hshadow_ccall; [exact AI0| exact HF| exact CF| exact HS| exact Hw|].
      intros a Ha. apply NV. change (HFSIZE / 8) with 1024 in Ha. lia.
  Qed.
End S.
End A_Henv.

Module A_ImgLow.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_La0bg A_Img.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

(* [comment removed for export] *)
Definition CONSTS_TOP2 : Z := 0x800b9400.

Definition const_free_ivl2 (iv : Z * Z) : Prop :=
  const_free_ivl iv \/ CONSTS_TOP2 <= fst iv \/ (0x60a000 <= fst iv /\ snd iv <= 0x7fffa000).

Lemma const_free_ivl2_of : forall iv, const_free_ivl iv -> const_free_ivl2 iv.
Proof. intros iv H. left. exact H. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma consts_const_free2 :
  Forall (fun c => (fst c + Z.of_nat (length (snd c)) <= 0x5e7210 \/ 0x5e7b80 <= fst c)
                   /\ 0x10000 <= fst c
                   /\ (fst c + Z.of_nat (length (snd c)) <= 0x60a000
                       \/ (0x7fffa000 <= fst c /\ fst c + Z.of_nat (length (snd c)) <= CONSTS_TOP2)))
         (cl_consts LPA).
Proof.
  apply Forall_forall. intros c Hc.
  assert (B : forallb (fun c => ((fst c + Z.of_nat (length (snd c)) <=? 0x5e7210) || (0x5e7b80 <=? fst c))
                               && (0x10000 <=? fst c)
                               && ((fst c + Z.of_nat (length (snd c)) <=? 0x60a000)
                                   || ((0x7fffa000 <=? fst c) && (fst c + Z.of_nat (length (snd c)) <=? CONSTS_TOP2))))%bool
                      (cl_consts LPA) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in B. specialize (B c Hc). cbn beta in B.
  apply andb_prop in B as [B B3]. apply andb_prop in B as [B1 B2].
  apply Z.leb_le in B2.
  apply Bool.orb_prop in B1 as [B1|B1]; apply Z.leb_le in B1;
  apply Bool.orb_prop in B3 as [B3|B3];
  (apply Z.leb_le in B3 || (apply andb_prop in B3 as [B3 B4]; apply Z.leb_le in B3; apply Z.leb_le in B4));
  unfold CONSTS_TOP2 in *; lia.
Qed.

Section CEIL.
Context {Clg : Ceiling}.

Lemma consts_hold_munch2 : forall W m m',
  consts_hold LPA m -> munch W m m' -> Forall const_free_ivl2 W -> consts_hold LPA m'.
Proof.
  intros W m m' CH MU FW. unfold consts_hold in *. rewrite Forall_forall in CH |- *.
  pose proof consts_const_free2 as CF. rewrite Forall_forall in CF.
  intros c Hc. specialize (CH c Hc). destruct (CF c Hc) as (C1 & C2 & C3).
  eapply bytes_at_munch; [exact CH| exact MU|].
  intros a Ha. clear CH Hc MU. induction W as [|[lo hi] W IH]; [exact I|].
  cbn. apply Forall_cons_iff in FW as [F1 FW]. split; [| exact (IH FW)].
  unfold const_free_ivl2, const_free_ivl, CONSTS_TOP, CONSTS_TOP2 in F1. cbn in F1. unfold CONSTS_TOP2 in C3. lia.
Qed.

Lemma const_free_outside2 : forall W a, Forall const_free_ivl2 W ->
  0x7fffa000 <= a < CONSTS_TOP2 -> outside W a.
Proof.
  intros W a FW Ha. unfold CONSTS_TOP2 in *. induction W as [|[lo hi] W IH]; [exact I|].
  cbn. apply Forall_cons_iff in FW as [F1 FW]. split; [| exact (IH FW)].
  unfold const_free_ivl2, const_free_ivl, CONSTS_TOP, CONSTS_TOP2 in F1. cbn in F1. lia.
Qed.

Lemma cenv_munch2 : forall W m m',
  cenv m -> munch W m m' -> Forall const_free_ivl2 W -> cenv m'.
Proof.
  intros W m m' [CH VIS] MU FW. split; [eapply consts_hold_munch2; eauto|].
  intros a Ha NS. eapply mapped_munch; [exact MU| | | | exact (VIS a Ha NS)].
  - unfold sh, kShadowOffset. pose proof (Z.mod_pos_bound (a / 8 + 2147450880) 8 ltac:(lia)).
    assert (0 <= a / 8) by (apply Z.div_pos; lia). lia.
  - unfold sh, kShadowOffset. pose proof (Z.mod_pos_bound (a / 8 + 2147450880) 8 ltac:(lia)).
    assert (a / 8 <= 0x60a000 / 8) by (apply Z.div_le_mono; lia). change (0x60a000 / 8) with 791552 in *. lia.
  - intros i Hi. apply const_free_outside2; [exact FW|]. unfold sh, kShadowOffset, CONSTS_TOP2.
    pose proof (Z.div_mod (a / 8 + 2147450880) 8 ltac:(lia)) as DM.
    pose proof (Z.mod_pos_bound (a / 8 + 2147450880) 8 ltac:(lia)).
    assert (0x10000 / 8 <= a / 8) by (apply Z.div_le_mono; lia).
    assert (a / 8 <= 0x609fff / 8) by (apply Z.div_le_mono; lia).
    change (0x10000 / 8) with 8192 in *. change (0x609fff / 8) with 791551 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma app_shadow_const_free2 : forall (L : clayout) {AI : AsanAlloc L} p n k,
  app_range L p n -> cl_image_lo L = 0x10000 -> cl_image_hi L = 0x60a000 -> 0 <= k -> k <= (n + 7) / 8 ->
  const_free_ivl2 (sh p, sh p + k).
Proof.
  intros L AI p n k AR HLO HHI K0 K1.
  destruct (app_lin L p n AR) as (ix & sx & B). rewrite HLO, HHI in B.
  unfold const_free_ivl2, const_free_ivl, CONSTS_TOP, CONSTS_TOP2. cbn [fst snd].
  unfold sh, kShadowOffset in *. Z.div_mod_to_equations. lia.
Qed.

End CEIL.
End A_ImgLow.


Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | first [ lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; nia ] ].
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition assert_VSB_integrity_entry : Z := 0x898e8.
Definition vsb_indent_entry : Z := 0x89d18.
Definition VSB_extend_entry : Z := 0x89f98.
Definition VSB_putc_entry : Z := 0x8aa50.
Definition VSB_bcat_entry : Z := 0x89a1c.
Definition VSB_finish_entry : Z := 0x8ac7c.
Definition VSB_data_entry : Z := 0x8adf4.
Definition VSB_len_entry : Z := 0x8ae64.
Definition VSB_new_auto_entry : Z := 0x89840.
Definition VSB_destroy_entry : Z := 0x8aefc.
Definition VSB_vprintf_entry : Z := 0x8a350.
Definition VSB_printf_entry : Z := 0x8a8a4.
Definition VSLb_entry : Z := 0x86c98.
Definition WS_Assert_entry : Z := 0x87674.
Definition ws_emu_entry : Z := 0x87dcc.
Definition WS_Init_entry : Z := 0x87e94.
Definition WS_Reset_entry : Z := 0x88168.
Definition ws_alloc_free_entry : Z := 0x88470.
Definition WS_Alloc_entry : Z := 0x88628.
Definition ws_emu_alloc_entry : Z := 0x88790.
Definition WS_MarkOverflow_entry : Z := 0x8b1dc.
Definition WS_Overflowed_entry : Z := 0x8b2a8.
Definition WS_Rollback_entry : Z := 0x8b394.
Definition vep_error_entry : Z := 0x8e828.
Definition vep_match_entry : Z := 0x8f6f0.
Definition vep_default_cb_entry : Z := 0x8fda4.
Definition vep_emit_len_entry : Z := 0x90794.
Definition vep_emit_common_entry : Z := 0x90294.
Definition vep_mark_common_entry : Z := 0x8e0f4.
Definition vep_do_comment_entry : Z := 0x8f64c.
Definition vep_do_remove_entry : Z := 0x8f4e8.
Definition vep_do_include_entry : Z := 0x8e958.
Definition VEP_Init_entry : Z := 0x8f8fc.
Definition VEP_Parse_entry : Z := 0x8b4c8.
Definition VEP_Finish_entry : Z := 0x8feac.
Definition crc32_entry : Z := 0x917c8.
Definition crc32_z_entry : Z := 0x90ae0.
Definition crc32_combine_entry : Z := 0x91938.

(* [comment removed for export] *)
Definition ERRNOA : Z := 0x5e7b34.
Definition errno_location_entry : Z := 0x98068.
Lemma ERRNOA_eq : cl_errno LPA = ERRNOA. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASSERT_STACK : Z := 32.   (* [comment removed for export] *)
Definition INDENT_STACK : Z := 80.                        (* [comment removed for export] *)
Definition EXT_STACK : Z := 80 + ASTK.                     (* [comment removed for export] *)
Definition PUTC_STACK : Z := 64 + EXT_STACK.
Definition BCAT_STACK : Z := 80 + EXT_STACK.               (* [comment removed for export] *)
Definition FINISH_STACK : Z := 32 + ASSERT_STACK.          (* [comment removed for export] *)
Definition DATA_STACK : Z := 32 + ASSERT_STACK.
Definition LEN_STACK : Z := 32 + ASSERT_STACK.
Definition NEWAUTO_STACK : Z := 128 + ASTK.   (* [comment removed for export] *)                 (* [comment removed for export] *)
Definition DESTROY_STACK : Z := 32 + ASTK.
(* [comment removed for export] *)
Definition ICPT_STACK : Z := 4608.
Definition VEPERR_STACK : Z := 16 + 48.                  (* [comment removed for export] *)
Definition CB_STACK : Z := 32.   (* [comment removed for export] *)                            (* [comment removed for export] *)
Definition CRC_STACK : Z := 128.                          (* [comment removed for export] *)
Definition C64_STACK : Z := 32 + 16.                      (* [comment removed for export] *)
Definition WSEMU_STACK : Z := 16.
Definition WSASSERT_STACK : Z := 64 + WSEMU_STACK.
Definition WSMARK_STACK : Z := 16.
Definition WSINIT_STACK : Z := 64 + ICPT_STACK.            (* [comment removed for export] *)
Definition WSEMUALLOC_STACK : Z := 80 + ASTK.             (* [comment removed for export] *)
Definition WSALLOC_STACK : Z := 48 + WSEMUALLOC_STACK.
Definition WSAFREE_STACK : Z := 32 + ASTK.                (* [comment removed for export] *)
Definition WSRESET_STACK : Z := 64 + WSAFREE_STACK.
Definition WSROLLBACK_STACK : Z := 32 + WSRESET_STACK.
(* [comment removed for export] *)
Definition VPRINTF_STACK : Z := 192 + 16 + EXT_STACK.     (* [comment removed for export] *)
Definition PRINTF_STACK : Z := 128 + 16 + VPRINTF_STACK.
Definition EMITLEN_STACK : Z := 128 + 16 + BCAT_STACK.
Definition EMITC_STACK : Z := 128 + 16 + EMITLEN_STACK.
Definition MARK_STACK : Z := 160 + EMITC_STACK.           (* [comment removed for export] *)
Definition VEPINIT_STACK : Z := 80 + PRINTF_STACK.         (* [comment removed for export] *)
Definition VEPFIN_STACK : Z := 64 + MARK_STACK.            (* [comment removed for export] *)
Definition DOINCL_STACK : Z := 160 + PRINTF_STACK.   (* [comment removed for export] *)         (* [comment removed for export] *)
Definition PARSE_STACK : Z := 320 + Z.max MARK_STACK DOINCL_STACK.   (* [comment removed for export] *)  (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac unfold_stacks :=
  unfold PARSE_STACK, DOINCL_STACK, VEPFIN_STACK, VEPINIT_STACK, MARK_STACK, EMITC_STACK, EMITLEN_STACK,
         PRINTF_STACK, VPRINTF_STACK, WSROLLBACK_STACK, WSRESET_STACK, WSAFREE_STACK, WSALLOC_STACK, WSEMUALLOC_STACK,
         WSINIT_STACK, WSASSERT_STACK, WSEMU_STACK, VEPERR_STACK, DESTROY_STACK, NEWAUTO_STACK, LEN_STACK, DATA_STACK,
         FINISH_STACK, BCAT_STACK, PUTC_STACK, EXT_STACK, INDENT_STACK, ASSERT_STACK, ICPT_STACK, ASTK in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition vkeep (v v' : vep) (ch : list vf) : Prop := forall f, ~ In f ch -> v' f = v f.

(* [comment removed for export] *)
Definition vep_cnt (v : vep) (n : Z) : Prop :=
  0 <= v Fo_pending /\ 0 <= v Fcb_x /\ v Fcb_x + v Fo_pending = n /\
  0 <= v Fo_total <= v Fo_last /\ v Fo_last <= v Fcb_x /\
  v Fo_wait = v Fcb_x - v Fo_last /\ v Fo_crc = v Fo_wait.

(* [comment removed for export] *)
Definition vsb_room (vv : vsb_rec) (N : Z) : Prop :=
  vb_size vv <= vb_len vv + 4096 /\ vb_len vv <= 7 * N.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition NMAX : Z := 2^26.

(* [comment removed for export] *)
Definition vsb_result (e r : Z) : Z := if e =? 0 then r else -1.

Section C.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition frames_same (A A' : AS) : Prop := forall ff, a_frame A' ff = a_frame A ff.

  (* [comment removed for export] *)
  Definition fbound (k : Z) (n0 n1 : nat) : nat := if Z.eqb k 0 then n0 else if Z.eqb k 1 then n1 else 0%nat.
  Definition frames_aged (A A' : AS) (n0 n1 : nat) : Prop :=
    (forall ff k age, a_frame A ff = Some (k, age) ->
        exists d, a_frame A' ff = Some (k, (age + d)%nat) /\ (d <= fbound k n0 n1)%nat)
    /\ (forall ff, a_frame A ff = None -> a_frame A' ff = None).

  (* [comment removed for export] *)
  Definition frames_young (A : AS) (n0 n1 : nat) : Prop :=
    forall ff k age, a_frame A ff = Some (k, age) -> (k = 0 \/ k = 1) ->
      Z.of_nat age + 2 + Z.of_nat (fbound k n0 n1) <= fslots k.

  (* [comment removed for export] *)
  Definition lib_frames (A : AS) : Prop := forall ff k age, a_frame A ff = Some (k, age) -> 2 <= k.

  Lemma lib_frames_young : forall A n0 n1, lib_frames A -> frames_young A n0 n1.
  Proof. intros A n0 n1 LF ff k age HF [K|K]; pose proof (LF _ _ _ HF); lia. Qed.

  Lemma lib_frames_same : forall A A' n0 n1, lib_frames A -> frames_aged A A' n0 n1 -> frames_same A A'.
  Proof.
    intros A A' n0 n1 LF [AG NN] ff. destruct (a_frame A ff) as [[k age]|] eqn:E.
    - destruct (AG _ _ _ E) as (d & E' & Hd). pose proof (LF _ _ _ E) as K.
      unfold fbound in Hd. destruct (Z.eqb_spec k 0); [lia|]. destruct (Z.eqb_spec k 1); [lia|].
      rewrite E'. f_equal. f_equal. lia.
    - exact (NN _ E).
  Qed.

  Lemma frames_same_lib : forall A A', frames_same A A' -> lib_frames A -> lib_frames A'.
  Proof. intros A A' FS LF ff k age HF. rewrite FS in HF. exact (LF _ _ _ HF). Qed.

  Lemma frames_same_aged : forall A A' n0 n1, frames_same A A' -> frames_aged A A' n0 n1.
  Proof.
    intros A A' n0 n1 FS. split.
    - intros ff k age HF. exists 0%nat. rewrite FS, Nat.add_0_r. split; [exact HF| lia].
    - intros ff HN. rewrite FS. exact HN.
  Qed.

  Lemma frames_aged_trans : forall A A' A'' a0 a1 b0 b1,
    frames_aged A A' a0 a1 -> frames_aged A' A'' b0 b1 -> frames_aged A A'' (a0 + b0) (a1 + b1).
  Proof.
    intros A A' A'' a0 a1 b0 b1 [AG1 N1] [AG2 N2]. split.
    - intros ff k age HF. destruct (AG1 _ _ _ HF) as (d1 & E1 & D1). destruct (AG2 _ _ _ E1) as (d2 & E2 & D2).
      exists (d1 + d2)%nat. rewrite Nat.add_assoc. split; [exact E2|]. unfold fbound in *.
      destruct (Z.eqb k 0); [lia|]. destruct (Z.eqb k 1); lia.
    - intros ff HN. exact (N2 _ (N1 _ HN)).
  Qed.

  Lemma frames_young_aged : forall A A' a0 a1 n0 n1,
    frames_young A (a0 + n0) (a1 + n1) -> frames_aged A A' a0 a1 ->
    (forall ff k age, a_frame A' ff = Some (k, age) -> (k = 0 \/ k = 1) -> exists age0, a_frame A ff = Some (k, age0)) ->
    frames_young A' n0 n1.
  Proof.
    intros A A' a0 a1 n0 n1 FY [AG NN] BACK ff k age HF K.
    destruct (BACK _ _ _ HF K) as [age0 HF0]. destruct (AG _ _ _ HF0) as (d & E & D).
    rewrite HF in E. injection E as E. pose proof (FY _ _ _ HF0 K) as Y. unfold fbound in *.
    destruct K as [-> | ->]; cbn in *; lia.
  Qed.

  (* [comment removed for export] *)
  Definition vep_base (H : henv) (VEP : Z) (v : vep) : Prop :=
    v Fvc = h_vc H /\ v Fcb = vi_cb VIA /\ v Fcb_priv = VEP + 56 /\ v Fdogzip = 0 /\ v Furl = vi_url VIA.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition leaf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (r : option Z) (W : Z) (lo : Z) (v : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 v',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (match r with Some z => Z_to_bv 64 z | None => a0 end) a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None v' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - W, bv_unsigned sp)] v v' /\ wmono rsegs v v' /\ mem_inv rsegs v'
      /\ stk rsegs v' lo (bv_unsigned sp).
  Definition vsb_leaf_post := leaf_post.

  Definition assert_VSB_integrity_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem) (S : Z) (vr : vsb_rec) (fin : bool) (lo : Z),
      a0 = Z_to_bv 64 S ->
      rw_cells rsegs v S (vsb_cells vr) -> vsb_inv vr fin ->
      shadowed LPA v S 40 -> cenv v ->
      S mod 8 = 0 -> kHighMemBeg <= S -> S + 40 <= alloc_ceiling ->
      stk rsegs v lo (bv_unsigned sp) -> lo + ASSERT_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs v ->
      evt rsegs (vsb_leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc None ASSERT_STACK lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 assert_VSB_integrity_entry) fc None v (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vsb_indent_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem) (S : Z) (vr : vsb_rec) (fin : bool) (lo : Z),
      a0 = Z_to_bv 64 S ->
      rw_cells rsegs v S (vsb_cells vr) -> vsb_inv vr fin ->
      shadowed LPA v S 40 -> cenv v ->
      S mod 8 = 0 -> kHighMemBeg <= S -> S + 40 <= alloc_ceiling ->
      stk rsegs v lo (bv_unsigned sp) -> lo + INDENT_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs v ->
      evt rsegs (vsb_leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc None INDENT_STACK lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 vsb_indent_entry) fc None v (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition VSB_data_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem) (S : Z) (vr : vsb_rec) (lo : Z),
      a0 = Z_to_bv 64 S ->
      rw_cells rsegs v S (vsb_cells vr) -> vsb_inv vr true ->
      shadowed LPA v S 40 -> cenv v ->
      S mod 8 = 0 -> kHighMemBeg <= S -> S + 40 <= alloc_ceiling ->
      stk rsegs v lo (bv_unsigned sp) -> lo + DATA_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs v ->
      evt rsegs (vsb_leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Some (vb_buf vr)) DATA_STACK lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 VSB_data_entry) fc None v (seg_rom rsegs)).

  Definition VSB_len_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem) (S : Z) (vr : vsb_rec) (fin : bool) (lo : Z),
      a0 = Z_to_bv 64 S ->
      rw_cells rsegs v S (vsb_cells vr) -> vsb_inv vr fin ->
      shadowed LPA v S 40 -> cenv v ->
      S mod 8 = 0 -> kHighMemBeg <= S -> S + 40 <= alloc_ceiling ->
      stk rsegs v lo (bv_unsigned sp) -> lo + LEN_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs v ->
      evt rsegs (vsb_leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                   (Some (vsb_result (vb_error vr) (vb_len vr))) LEN_STACK lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 VSB_len_entry) fc None v (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition VSB_finish_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (S : Z) (vr : vsb_rec) (bs : list byte) (lo : Z) (v : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 v',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (vsb_result (vb_error vr) 0)) a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None v' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - FINISH_STACK, bv_unsigned sp); (S, S + 40); (vb_buf vr, vb_buf vr + vb_size vr);
                (ERRNOA, ERRNOA + 4)] v v'
      /\ wmono rsegs v v' /\ mem_inv rsegs v'
      /\ rw_cells rsegs v' S (vsb_cells (vsb_set_flags vr VSB_FLAGS_FIN))
      /\ u8arr rsegs v' (vb_buf vr) (upd bs (Z.to_nat (vb_len vr)) (Z_to_bv 8 0))
      /\ rw_cells rsegs v' ERRNOA [C4 (Z_to_bv 64 (vb_error vr))]
      /\ stk rsegs v' lo (bv_unsigned sp).

  Definition VSB_finish_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem) (S : Z) (vr : vsb_rec) (bs : list byte) (e : word) (lo : Z),
      a0 = Z_to_bv 64 S -> tp = cl_tp LPA ->
      rw_cells rsegs v S (vsb_cells vr) -> vsb_inv vr false ->
      u8arr rsegs v (vb_buf vr) bs -> Z.of_nat (length bs) = vb_size vr ->
      rw_cells rsegs v ERRNOA [C4 e] ->
      shadowed LPA v S 40 -> shadowed LPA v (vb_buf vr) (vb_size vr) -> shadowed LPA v ERRNOA 4 -> cenv v ->
      S mod 8 = 0 -> kHighMemBeg <= S -> S + 40 <= alloc_ceiling -> app_range LPA (vb_buf vr) (vb_size vr) (* [comment removed for export] *) -> vb_buf vr + vb_size vr <= alloc_ceiling ->
      (S + 40 <= vb_buf vr \/ vb_buf vr + vb_size vr <= S) ->
      stk rsegs v lo (bv_unsigned sp) -> lo + FINISH_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs v ->
      evt rsegs (VSB_finish_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S vr bs lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 VSB_finish_entry) fc None v (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition VSB_extend_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (S addlen : Z) (vr : vsb_rec) (lo : Z) (T : TSet),
      let v := aview A m in
      let ns := vsb_extendsize (vb_size vr + addlen) in
      ainv A m md -> mem_inv rsegs v ->
      a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 addlen ->
      vsb_obj LPA A v S vr false ->
      1 <= addlen -> vb_size vr + addlen <= EXT_MAX ->
      a_livebytes A + ns <= LIVE_MAX -> a_nlive A + 1 <= NLIVE_MAX -> (kMaxPrimaryUser < ns -> 1 <= a_seccred A) ->
      prim_cost ns <= a_primcred A (* [comment removed for export] *) ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs v lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + EXT_STACK <= bv_unsigned sp ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model)
              (vr' : vsb_rec),
          let v' := aview A' m' in
          ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md md' ->
          vsb_obj LPA A' v' S vr' false ->
          (forall q, q <> vb_buf vr -> q <> vb_buf vr' -> a_live A' q = a_live A q) ->
          frames_same A A' -> a_tinycred A' = a_tinycred A -> a_nlive A' = a_nlive A ->
          stk rsegs v' lo (bv_unsigned sp) ->
          (* [comment removed for export] *)
          (exists nb, r = 0 /\ vr' = vsb_set_buf_size vr nb ns /\
               (forall i, 0 <= i < vb_size vr -> v' (Z_to_bv 64 (nb + i)) = v (Z_to_bv 64 (vb_buf vr + i))) /\
               a_live A nb = None /\ a_live A' (vb_buf vr) = None /\
               a_livebytes A' = a_livebytes A + ns - vb_size vr /\
               a_seccred A' = a_seccred A - (if Z.ltb kMaxPrimaryUser ns then 1 else 0) /\
               a_primcred A' = a_primcred A - prim_cost ns (* [comment removed for export] *) /\
               cframe LPA (owned A) (owned A') (bv_unsigned sp) EXT_STACK
                        (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (S <= a < S + 40))
                        (newblk nb ns) v v') ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 VSB_extend_entry) fc None m (seg_rom rsegs)) md) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition VSB_putc_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (S : Z) (vr : vsb_rec) (lo : Z) (T : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v ->
      a0 = Z_to_bv 64 S ->
      vsb_obj LPA A v S vr false ->
      vb_size vr + 1 <= EXT_MAX ->
      a_livebytes A + vsb_extendsize (vb_size vr + 1) <= LIVE_MAX ->
      a_nlive A + 1 <= NLIVE_MAX -> 1 <= a_seccred A -> PRIM_ROOM <= a_primcred A (* [comment removed for export] *) ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs v lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + PUTC_STACK <= bv_unsigned sp ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (vr' : vsb_rec),
          let v' := aview A' m' in
          ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md md' ->
          vsb_obj LPA A' v' S vr' false ->
          vb_len vr' = vb_len vr + 1 (* [comment removed for export] *) -> vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
          (vb_size vr' = vb_size vr \/ (vb_size vr <= vb_len vr + 1 /\ vb_size vr' = vsb_extendsize (vb_size vr + 1))) ->   (* [comment removed for export] *)
          (forall q, q <> vb_buf vr -> q <> vb_buf vr' -> a_live A' q = a_live A q) ->
          (vb_buf vr' = vb_buf vr \/ (a_live A (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
          frames_same A A' ->
          a_livebytes A' = a_livebytes A + vb_size vr' - vb_size vr ->
          a_tinycred A' = a_tinycred A -> a_nlive A' = a_nlive A ->
          a_seccred A - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A ->
          a_primcred A - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A ->   (* [comment removed for export] *)
          stk rsegs v' lo (bv_unsigned sp) ->
          cframe LPA (owned A) (owned A') (bv_unsigned sp) PUTC_STACK
                   (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (S <= a < S + 40))
                   (newblk (vb_buf vr') (vb_size vr')) v v' ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 VSB_putc_entry) fc None m (seg_rom rsegs)) md) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition VSB_bcat_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (S SRC : Z) (src : list byte)
           (vr : vsb_rec) (lo : Z) (T : TSet),
      let v := aview A m in
      let l := Z.of_nat (length src) in
      ainv A m md -> mem_inv rsegs v ->
      a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 SRC -> a2 = Z_to_bv 64 l ->
      vsb_obj LPA A v S vr false ->
      bytes_at rsegs v SRC src -> 1 <= l <= 9 ->
      cobj LPA A v [S; vb_buf vr] SRC l ->
      vb_size vr + 9 <= EXT_MAX ->
      a_livebytes A + vsb_extendsize (vb_size vr + 9) <= LIVE_MAX ->
      a_nlive A + 1 <= NLIVE_MAX -> 1 <= a_seccred A -> PRIM_ROOM <= a_primcred A (* [comment removed for export] *) ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs v lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + BCAT_STACK <= bv_unsigned sp ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (vr' : vsb_rec),
          let v' := aview A' m' in
          ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md md' ->
          vsb_obj LPA A' v' S vr' false ->
          vb_len vr <= vb_len vr' <= vb_len vr + l ->
          vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
          (forall q, q <> vb_buf vr -> q <> vb_buf vr' -> a_live A' q = a_live A q) ->
          (vb_buf vr' = vb_buf vr \/ (a_live A (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
          frames_same A A' ->
          a_livebytes A' = a_livebytes A + vb_size vr' - vb_size vr ->
          a_tinycred A' = a_tinycred A -> a_nlive A' = a_nlive A ->
          a_seccred A - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A ->
          a_primcred A - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A ->   (* [comment removed for export] *)
          stk rsegs v' lo (bv_unsigned sp) ->
          cframe LPA (owned A) (owned A') (bv_unsigned sp) BCAT_STACK
                   (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (S <= a < S + 40))
                   (newblk (vb_buf vr') (vb_size vr')) v v' ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 VSB_bcat_entry) fc None m (seg_rom rsegs)) md) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition VSB_new_auto_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (lo : Z) (T : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v ->
      a_livebytes A + 56 <= LIVE_MAX -> a_nlive A + 2 <= NLIVE_MAX -> 96 <= a_primcred A (* [comment removed for export] *) ->
      bv_unsigned s0 < alloc_ceiling ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs v lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + NEWAUTO_STACK <= bv_unsigned sp ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model),
          let v' := aview A' m' in
          ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md md' ->
          frames_same A A' -> a_tinycred A' = a_tinycred A -> a_seccred A' = a_seccred A -> a_primcred A' = a_primcred A - 96 ->   (* [comment removed for export] *)
          stk rsegs v' lo (bv_unsigned sp) ->
          (* [comment removed for export] *)
              (exists b, r <> 0 /\ vsb_obj LPA A' v' r (vsb_fresh b) false /\
               a_live A r = None /\ a_live A b = None /\
               (forall q, q <> r -> q <> b -> a_live A' q = a_live A q) /\ a_livebytes A' = a_livebytes A + 56 /\ a_nlive A' = a_nlive A + 2 /\
               cframe LPA (owned A) (owned A') (bv_unsigned sp) NEWAUTO_STACK nowhere
                      (fun a => newblk r 40 a \/ newblk b 16 a) v v') ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 VSB_new_auto_entry) fc None m (seg_rom rsegs)) md) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition VSB_destroy_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (PS S : Z) (vr : vsb_rec) (fin : bool)
           (lo : Z) (T : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v ->
      a0 = Z_to_bv 64 PS ->
      rw_cells rsegs v PS [C8 (Z_to_bv 64 S)] -> cobj LPA A v [S; vb_buf vr] PS 8 -> PS mod 8 = 0 ->
      PS + 8 <= alloc_ceiling ->
      vsb_obj LPA A v S vr fin ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs v lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + DESTROY_STACK <= bv_unsigned sp ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model),
          let v' := aview A' m' in
          ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md md' ->
          frames_same A A' ->
          a_livebytes A' = a_livebytes A - 40 - vb_size vr -> a_tinycred A' = a_tinycred A -> a_nlive A' = a_nlive A - 2 ->
          a_seccred A' = a_seccred A -> a_primcred A' = a_primcred A (* [comment removed for export] *) ->
          stk rsegs v' lo (bv_unsigned sp) ->
          rw_cells rsegs v' PS [C8 (Z_to_bv 64 0)] ->
          a_live A' S = None -> a_live A' (vb_buf vr) = None ->
          (forall q, q <> S -> q <> vb_buf vr -> a_live A' q = a_live A q) ->
          cframe LPA (owned A) (owned A') (bv_unsigned sp) DESTROY_STACK
                 (fun a => newblk S 40 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (PS <= a < PS + 8)) nowhere v v' ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 VSB_destroy_entry) fc None m (seg_rom rsegs)) md) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition ws_emu_stmt : Prop :=
    forall (H : henv) (wr : ws_rec) (we : wsemu_rec) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem),
      a0 = Z_to_bv 64 (h_ws H) ->
      rw_cells rsegs v (h_ws H) (ws_cells wr) -> length (ws_id wr) = 4%nat -> ws_s wr = h_wsbuf H ->
      rw_cells rsegs v (h_wsbuf H) (wsemu_cells we) ->
      hshadow LPA H v -> henv_geom LPA H -> cenv v ->
      stk rsegs v lo (bv_unsigned sp) -> lo + WSEMU_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs v ->
      evt rsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Some (h_wsbuf H)) WSEMU_STACK lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ws_emu_entry) fc None v (seg_rom rsegs)).

  (* [comment removed for export] *)
  Definition WS_Assert_stmt : Prop :=
    forall (H : henv) (E : option (AS * Z * Z)) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem),
      a0 = Z_to_bv 64 (h_ws H) ->
      match E with
      | None => ws0_obj LPA H v
      | Some (A, wa, vep) => ws1_obj LPA H A v wa vep /\ shadowed LPA v wa 40
                          /\ wa mod 16 = 0 /\ kHighMemBeg <= wa /\ wa + 40 <= alloc_ceiling
                          /\ kHighMemBeg <= vep /\ vep + 312 <= alloc_ceiling   (* [comment removed for export] *)
      end ->
      glob_ok LPA VIA H v -> hshadow LPA H v -> henv_geom LPA H -> cenv v ->
      stk rsegs v lo (bv_unsigned sp) -> lo + WSASSERT_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs v ->
      evt rsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc None WSASSERT_STACK lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 WS_Assert_entry) fc None v (seg_rom rsegs)).

  (* [comment removed for export] *)
  Definition WS_MarkOverflow_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (H : henv) (lo : Z) (v : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 v',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None v' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - WSMARK_STACK, bv_unsigned sp); (h_ws H, h_ws H + 40)] v v'
      /\ wmono rsegs v v' /\ mem_inv rsegs v' /\ stk rsegs v' lo (bv_unsigned sp)
      /\ ws0_obj LPA H v'.

  Definition WS_MarkOverflow_stmt : Prop :=
    forall (H : henv) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem),
      a0 = Z_to_bv 64 (h_ws H) ->
      ws0_obj LPA H v -> hshadow LPA H v -> henv_geom LPA H -> cenv v ->
      stk rsegs v lo (bv_unsigned sp) -> lo + WSMARK_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs v ->
      evt rsegs (WS_MarkOverflow_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc H lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 WS_MarkOverflow_entry) fc None v (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition WS_Init_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (H : henv) (lo : Z) (v : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 v',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None v' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - WSINIT_STACK, bv_unsigned sp); (h_ws H, h_ws H + 40); (h_wsbuf H, h_wsbuf H + 32)] v v'
      /\ wmono rsegs v v' /\ mem_inv rsegs v' /\ stk rsegs v' lo (bv_unsigned sp)
      /\ ws0_obj LPA H v' /\ glob_ok LPA VIA H v'.

  Definition WS_Init_stmt : Prop :=
    forall (H : henv) (junk40 junk32 : list byte) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem),
      a0 = Z_to_bv 64 (h_ws H) -> a1 = Z_to_bv 64 (vi_wsid VIA) -> a2 = Z_to_bv 64 (h_wsbuf H) -> a3 = Z_to_bv 64 1024 ->
      rw_cells rsegs v (h_ws H) [CB 40 junk40] -> rw_cells rsegs v (h_wsbuf H) [CB 32 junk32] ->
      glob_ok LPA VIA H v -> hshadow LPA H v -> hvis H v -> henv_geom LPA H -> cenv v ->
      stk rsegs v lo (bv_unsigned sp) -> lo + WSINIT_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs v ->
      evt rsegs (WS_Init_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc H lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 WS_Init_entry) fc None v (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition WS_Alloc_stmt : Prop :=
    forall (H : henv) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (T : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v ->
      a0 = Z_to_bv 64 (h_ws H) -> a1 = Z_to_bv 64 312 ->
      ws0_obj LPA H v -> glob_ok LPA VIA H v -> hshadow LPA H v -> hframe LPA A H ->
      a_livebytes A + 352 <= LIVE_MAX -> a_nlive A + 2 <= NLIVE_MAX -> 448 <= a_primcred A (* [comment removed for export] *) ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs v lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + WSALLOC_STACK <= bv_unsigned sp ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model),
          let v' := aview A' m' in
          ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md md' ->
          frames_same A A' -> a_tinycred A' = a_tinycred A -> a_seccred A' = a_seccred A -> a_primcred A' = a_primcred A - 448 ->   (* [comment removed for export] *)
          stk rsegs v' lo (bv_unsigned sp) -> glob_ok LPA VIA H v' -> hshadow LPA H v' ->
          (* [comment removed for export] *)
              (exists wa junk, r <> 0 /\ ws1_obj LPA H A' v' wa r /\ rw_cells rsegs v' r [CB 312 junk] /\
               a_live A wa = None /\ a_live A r = None /\
               (forall p, p <> wa -> p <> r -> a_live A' p = a_live A p) /\ a_livebytes A' = a_livebytes A + 352 /\ a_nlive A' = a_nlive A + 2 /\
               cframe LPA (owned A) (owned A') (bv_unsigned sp) WSALLOC_STACK
                      (fun a => h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32)
                      (fun a => newblk wa 40 a \/ newblk r 312 a) v v') ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 WS_Alloc_entry) fc None m (seg_rom rsegs)) md) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition WS_Rollback_stmt : Prop :=
    forall (H : henv) (E : option (Z * Z)) (lo SB N : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (T : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v ->
      a0 = Z_to_bv 64 (h_ws H) -> a1 = Z_to_bv 64 0 ->
      match E with None => ws0_obj LPA H v | Some (wa, vep) => ws1_obj LPA H A v wa vep end ->
      glob_ok LPA VIA H v -> hshadow LPA H v -> hframe LPA A H ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs v lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + WSROLLBACK_STACK <= bv_unsigned sp ->
      (* [comment removed for export] *)
      stack_shadow LPA v SB N (bv_unsigned sp - WSROLLBACK_STACK - 64) (bv_unsigned sp + 64) ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model),
          let v' := aview A' m' in
          ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md md' ->
          frames_same A A' -> a_tinycred A' = a_tinycred A -> a_seccred A' = a_seccred A -> a_primcred A' = a_primcred A ->   (* [comment removed for export] *)
          stk rsegs v' lo (bv_unsigned sp) -> glob_ok LPA VIA H v' -> hshadow LPA H v' -> ws0_obj LPA H v' ->
          match E with
          | None => (forall p, a_live A' p = a_live A p) /\ a_livebytes A' = a_livebytes A /\ a_nlive A' = a_nlive A
          | Some (wa, vep) => a_live A' wa = None /\ a_live A' vep = None /\
                              (forall p, p <> wa -> p <> vep -> a_live A' p = a_live A p) /\
                              a_livebytes A' = a_livebytes A - 352 /\ a_nlive A' = a_nlive A - 2
          end ->
          cframe LPA (owned A) (owned A') (bv_unsigned sp) WSROLLBACK_STACK
                 (fun a => h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32 \/
                           match E with None => False | Some (wa, vep) => newblk wa 40 a \/ newblk vep 312 a end)
                 nowhere v v' ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 WS_Rollback_entry) fc None m (seg_rom rsegs)) md) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition vsb_blocks (S : Z) (x : vsb_rec) (a : Z) : Prop := newblk S 40 a \/ newblk (vb_buf x) (vb_size x) a.
  Definition vsb_apart (S : Z) (x : vsb_rec) (others : list Z) : Prop :=
    forall y, In y others -> S <> y /\ vb_buf x <> y.

  (* [comment removed for export] *)
  Definition vep_error_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (H : henv) (lo : Z) (v : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 v',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None v' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - VEPERR_STACK, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320)] v v'
      /\ wmono rsegs v v' /\ mem_inv rsegs v' /\ glob_ok LPA VIA H v' /\ hobj_ok LPA VIA H v' /\ stk rsegs v' lo (bv_unsigned sp).

  Definition vep_error_stmt : Prop :=
    forall (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (H : henv) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem),
      a0 = Z_to_bv 64 VEP ->
      rw_cells rsegs v VEP (vep_cells vv tag q) -> length tag = 8%nat -> vep_pads_wf q ->
      vv Fvc = h_vc H -> glob_ok LPA VIA H v -> hobj_ok LPA VIA H v -> hshadow LPA H v -> henv_geom LPA H -> cenv v ->
      shadowed LPA v VEP 312 -> kHighMemBeg <= VEP -> VEP mod 8 = 0 -> VEP + 312 <= alloc_ceiling ->
      (h_ff H + HFSIZE <= VEP \/ VEP + 312 <= h_ff H) ->
      stk rsegs v lo (bv_unsigned sp) -> lo + VEPERR_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs v ->
      evt rsegs (vep_error_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc H lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 vep_error_entry) fc None v (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition crc32_stmt : Prop :=
    forall (B : Z) (inp : list byte) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem),
      a1 = Z_to_bv 64 B -> bv_unsigned a2 mod 2^32 = Z.of_nat (length inp) ->
      (B = 0 \/ (bytes_at rsegs v B inp /\ shadowed LPA v B (Z.of_nat (length inp)))) ->
      cenv v ->
      stk rsegs v lo (bv_unsigned sp) -> lo + CRC_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs v ->
      evt rsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (if Z.eqb B 0 then Some 0 else None) CRC_STACK lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 crc32_entry) fc None v (seg_rom rsegs)).

  (* [comment removed for export] *)
  Definition crc32_combine_stmt : Prop :=
    forall (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem),
      cenv v ->
      stk rsegs v lo (bv_unsigned sp) -> lo + C64_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs v ->
      evt rsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc None C64_STACK lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 crc32_combine_entry) fc None v (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vep_default_cb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (l lo : Z) (v : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 v',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (vv Fcb_x + l)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None v' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - CB_STACK, bv_unsigned sp); (VEP + 56, VEP + 64)] v v'
      /\ wmono rsegs v v' /\ mem_inv rsegs v' /\ stk rsegs v' lo (bv_unsigned sp)
      /\ rw_cells rsegs v' VEP (vep_cells (fupd vv Fcb_x (vv Fcb_x + l)) tag q).

  Definition vep_default_cb_stmt : Prop :=
    forall (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (H : henv) (l lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem),
      a0 = Z_to_bv 64 (h_vc H) -> a1 = Z_to_bv 64 (VEP + 56) -> a2 = Z_to_bv 64 l ->
      rw_cells rsegs v VEP (vep_cells vv tag q) -> length tag = 8%nat -> vep_pads_wf q ->
      hobj_ok LPA VIA H v -> hshadow LPA H v -> henv_geom LPA H -> cenv v ->
      shadowed LPA v VEP 312 -> kHighMemBeg <= VEP -> VEP mod 8 = 0 -> VEP + 312 <= alloc_ceiling ->
      (h_ff H + HFSIZE <= VEP \/ VEP + 312 <= h_ff H) ->
      0 <= vv Fcb_x -> 0 <= l -> vv Fcb_x + l < 2^62 ->
      stk rsegs v lo (bv_unsigned sp) -> lo + CB_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs v ->
      evt rsegs (vep_default_cb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc VEP vv tag q l lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 vep_default_cb_entry) fc None v (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vep_emit_len_stmt : Prop :=
    forall (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (vr : vsb_rec) (l c8 c16 c64 : Z) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (T : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v ->
      a0 = Z_to_bv 64 VEP -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 c8 -> a3 = Z_to_bv 64 c16 -> a4 = Z_to_bv 64 c64 ->
      1 <= l < 2^62 -> 0 <= c8 < 256 -> 0 <= c16 < 256 -> 0 <= c64 < 256 ->
      vep_obj LPA A v VEP vv tag q -> vsb_obj LPA A v (vv Fvsb) vr false -> VEP <> vv Fvsb -> VEP <> vb_buf vr ->
      vb_size vr + 9 <= EXT_MAX ->
      a_livebytes A + vsb_extendsize (vb_size vr + 9) <= LIVE_MAX ->
      a_nlive A + 1 <= NLIVE_MAX -> 1 <= a_seccred A -> PRIM_ROOM <= a_primcred A (* [comment removed for export] *) ->
      frames_young A 1 0 ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs v lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + EMITLEN_STACK <= bv_unsigned sp ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model) (vr' : vsb_rec),
          let v' := aview A' m' in
          ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md md' ->
          stk rsegs v' lo (bv_unsigned sp) ->
          vep_obj LPA A' v' VEP vv tag q ->
          vsb_obj LPA A' v' (vv Fvsb) vr' false ->
          vb_len vr <= vb_len vr' <= vb_len vr + Z.min 9 (2 + l) ->
          vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
          (vb_buf vr' = vb_buf vr \/ (a_live A (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
          (forall p, p <> vb_buf vr -> p <> vb_buf vr' -> a_live A' p = a_live A p) ->
          frames_aged A A' 1 0 ->
          a_livebytes A' = a_livebytes A + vb_size vr' - vb_size vr ->
          a_tinycred A' = a_tinycred A -> a_nlive A' = a_nlive A ->
          a_seccred A - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A ->
          a_primcred A - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A ->   (* [comment removed for export] *)
          cframe LPA (owned A) (owned A') (bv_unsigned sp) EMITLEN_STACK
                 (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40))
                 (newblk (vb_buf vr') (vb_size vr')) v v' ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 vep_emit_len_entry) fc None m (seg_rom rsegs)) md) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vep_emit_common_stmt : Prop :=
    forall (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (vr : vsb_rec) (l mark : Z) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (T : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v ->
      a0 = Z_to_bv 64 VEP -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 mark ->
      0 <= l -> vv Fo_total + l < 2^62 -> 0 <= vv Fo_total -> bool01 mark ->
      vep_obj LPA A v VEP vv tag q -> vv Fdogzip = 0 -> vsb_obj LPA A v (vv Fvsb) vr false -> VEP <> vv Fvsb -> VEP <> vb_buf vr ->
      vb_size vr + 9 <= EXT_MAX ->
      a_livebytes A + vsb_extendsize (vb_size vr + 9) <= LIVE_MAX ->
      a_nlive A + 1 <= NLIVE_MAX -> 1 <= a_seccred A -> PRIM_ROOM <= a_primcred A (* [comment removed for export] *) ->
      frames_young A 2 0 ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs v lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + EMITC_STACK <= bv_unsigned sp ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (vv' : vep) (vr' : vsb_rec),
          let v' := aview A' m' in
          ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md md' ->
          stk rsegs v' lo (bv_unsigned sp) ->
          vep_obj LPA A' v' VEP vv' tag q ->
          (   (l = 0 /\ vv' = vv /\ vr' = vr)
           \/ (1 <= l /\ exists c, vv' = fupd (fupd (fupd vv Fcrc c) Fo_crc 0) Fo_total (vv Fo_total + l))) ->
          vsb_obj LPA A' v' (vv Fvsb) vr' false ->
          vb_len vr <= vb_len vr' <= vb_len vr + Z.min 9 (2 + l) ->
          vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
          (vb_buf vr' = vb_buf vr \/ (a_live A (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
          (forall p, p <> vb_buf vr -> p <> vb_buf vr' -> a_live A' p = a_live A p) ->
          frames_aged A A' 2 0 ->
          a_livebytes A' = a_livebytes A + vb_size vr' - vb_size vr ->
          a_tinycred A' = a_tinycred A -> a_nlive A' = a_nlive A ->
          a_seccred A - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A ->
          a_primcred A - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A ->   (* [comment removed for export] *)
          cframe LPA (owned A) (owned A') (bv_unsigned sp) EMITC_STACK
                 (fun a => blk VEP 312 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40))
                 (newblk (vb_buf vr') (vb_size vr')) v v' ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 vep_emit_common_entry) fc None m (seg_rom rsegs)) md) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition MARK_FIELDS : list vf :=
    [Fcrc; Fcrcp; Fo_crc; Fo_wait; Fo_pending; Fo_last; Fo_total; Fver_p; Flast_mark; Fcb_x].

  Definition vep_mark_common_stmt : Prop :=
    forall (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (vr : vsb_rec) (H : henv) (p mark n : Z) (seg : list byte) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (T : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v ->
      a0 = Z_to_bv 64 VEP -> a1 = Z_to_bv 64 p -> a2 = Z_to_bv 64 mark -> bool01 mark ->
      vep_obj LPA A v VEP vv tag q -> vep_base H VEP vv -> henv_ok LPA VIA H A v ->
      bool01 (vv Flast_mark) -> vep_cnt vv n -> 0 <= n -> n + (p - vv Fver_p) < NMAX ->
      vsb_obj LPA A v (vv Fvsb) vr false -> VEP <> vv Fvsb -> VEP <> vb_buf vr -> vb_size vr + 9 <= EXT_MAX ->
      a_livebytes A + vsb_extendsize (vb_size vr + 9) <= LIVE_MAX ->
      a_nlive A + 1 <= NLIVE_MAX -> 1 <= a_seccred A -> PRIM_ROOM <= a_primcred A (* [comment removed for export] *) ->
      frames_young A 2 0 ->
      (* [comment removed for export] *)
      bytes_at rsegs v (vv Fver_p) seg -> Z.of_nat (length seg) = p - vv Fver_p -> 4096 <= vv Fver_p -> p <= alloc_ceiling ->
      shadowed LPA v (vv Fver_p) (p - vv Fver_p) ->
      (* [comment removed for export] *)
      ((vv Fver_p = vi_empty VIA /\ seg = []) \/
       (exists d k, a_live A d = Some k /\ 0 < k /\ d <= vv Fver_p /\ p <= d + k /\ d <> VEP /\ d <> vv Fvsb /\ d <> vb_buf vr)) ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs v lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + MARK_STACK <= bv_unsigned sp ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (vv' : vep) (vr' : vsb_rec),
          let v' := aview A' m' in
          ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md md' ->
          stk rsegs v' lo (bv_unsigned sp) ->
          vep_obj LPA A' v' VEP vv' tag q -> vkeep vv vv' MARK_FIELDS ->
          vv' Fver_p = p -> vv' Flast_mark = mark -> vv' Fo_pending = 0 -> vep_cnt vv' (n + (p - vv Fver_p)) ->
          0 <= vv' Fcrc < 2^64 -> 0 <= vv' Fcrcp < 2^64 ->
          vsb_obj LPA A' v' (vv Fvsb) vr' false ->
          vb_len vr <= vb_len vr' <= vb_len vr + Z.min 9 (3 * (vv' Fo_last - vv Fo_last)) ->   (* [comment removed for export] *)
          vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
          (vb_buf vr' = vb_buf vr \/ (a_live A (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
          (forall r, r <> vb_buf vr -> r <> vb_buf vr' -> a_live A' r = a_live A r) ->
          frames_aged A A' 2 0 ->
          a_livebytes A' = a_livebytes A + vb_size vr' - vb_size vr ->
          a_tinycred A' = a_tinycred A -> a_nlive A' = a_nlive A ->
          a_seccred A - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A ->
          a_primcred A - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A ->   (* [comment removed for export] *)
          henv_ok LPA VIA H A' v' -> bytes_at rsegs v' (vv Fver_p) seg ->
          cframe LPA (owned A) (owned A') (bv_unsigned sp) MARK_STACK
                 (fun a => blk VEP 312 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40))
                 (newblk (vb_buf vr') (vb_size vr')) v v' ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 vep_mark_common_entry) fc None m (seg_rom rsegs)) md) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vep_do_comment_stmt : Prop :=
    forall (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (H : henv) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem),
      a0 = Z_to_bv 64 VEP -> a1 = Z_to_bv 64 1 ->
      rw_cells rsegs v VEP (vep_cells vv tag q) -> length tag = 8%nat -> vep_pads_wf q -> bool01 (vv Femptytag) ->
      vv Fvc = h_vc H -> glob_ok LPA VIA H v -> hobj_ok LPA VIA H v -> hshadow LPA H v -> henv_geom LPA H -> cenv v ->
      shadowed LPA v VEP 312 -> kHighMemBeg <= VEP -> VEP mod 8 = 0 -> VEP + 312 <= alloc_ceiling ->
      (h_ff H + HFSIZE <= VEP \/ VEP + 312 <= h_ff H) ->
      stk rsegs v lo (bv_unsigned sp) -> lo + VEPERR_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs v ->
      evt rsegs (vep_error_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc H lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 vep_do_comment_entry) fc None v (seg_rom rsegs)).

  (* [comment removed for export] *)
  Definition vep_do_remove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (H : henv) (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (lo : Z) (v : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 v' rm,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None v' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - VEPERR_STACK, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP + 92, VEP + 96)] v v'
      /\ wmono rsegs v v' /\ mem_inv rsegs v' /\ glob_ok LPA VIA H v' /\ hobj_ok LPA VIA H v' /\ stk rsegs v' lo (bv_unsigned sp)
      /\ bool01 rm /\ rw_cells rsegs v' VEP (vep_cells (fupd vv Fremove rm) tag q).

  Definition vep_do_remove_stmt : Prop :=
    forall (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (H : henv) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem),
      a0 = Z_to_bv 64 VEP -> a1 = Z_to_bv 64 1 ->
      rw_cells rsegs v VEP (vep_cells vv tag q) -> length tag = 8%nat -> vep_pads_wf q ->
      bool01 (vv Femptytag) -> bool01 (vv Fendtag) -> bool01 (vv Fremove) ->
      vv Fvc = h_vc H -> glob_ok LPA VIA H v -> hobj_ok LPA VIA H v -> hshadow LPA H v -> henv_geom LPA H -> cenv v ->
      shadowed LPA v VEP 312 -> kHighMemBeg <= VEP -> VEP mod 8 = 0 -> VEP + 312 <= alloc_ceiling ->
      (h_ff H + HFSIZE <= VEP \/ VEP + 312 <= h_ff H) ->
      stk rsegs v lo (bv_unsigned sp) -> lo + VEPERR_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs v ->
      evt rsegs (vep_do_remove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc H VEP vv tag q lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 vep_do_remove_entry) fc None v (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vep_do_include_attr_stmt : Prop :=
    forall (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (ya : vsb_rec) (vi : option vsb_rec) (H : henv) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (T : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v ->
      a0 = Z_to_bv 64 VEP -> a1 = Z_to_bv 64 0 ->
      vep_obj LPA A v VEP vv tag q -> vep_base H VEP vv -> henv_ok LPA VIA H A v ->
      (vv Fmatch_hit = vi_tbl_attr_include VIA \/ vv Fmatch_hit = vi_tbl_attr_include VIA + 16) -> bool01 (vv Finclude_continue) ->
      vv Fattr_vsb <> 0 -> vsb_obj LPA A v (vv Fattr_vsb) ya true -> vb_error ya = 0 ->
      vv Fattr_vsb <> VEP -> vb_buf ya <> VEP ->
      match vi with
      | None => vv Finclude_src = 0
      | Some yi => vv Finclude_src <> 0 /\ vsb_obj LPA A v (vv Finclude_src) yi true /\ vb_error yi = 0 /\
                   vv Finclude_src <> VEP /\ vb_buf yi <> VEP /\ vv Finclude_src <> vv Fattr_vsb /\ vv Finclude_src <> vb_buf ya /\
                   vb_buf yi <> vv Fattr_vsb /\ vb_buf yi <> vb_buf ya
      end ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs v lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + DOINCL_STACK <= bv_unsigned sp ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (vv' : vep) (vi' : option vsb_rec),
          let v' := aview A' m' in
          ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md md' ->
          stk rsegs v' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' v' ->
          vep_obj LPA A' v' VEP vv' tag q ->
          frames_same A A' -> a_tinycred A' = a_tinycred A -> a_seccred A' = a_seccred A -> a_primcred A' = a_primcred A ->   (* [comment removed for export] *)
          (  (* [comment removed for export] *) (vi = None /\ vv' = fupd (fupd vv Finclude_src (vv Fattr_vsb)) Fattr_vsb 0 /\ vi' = Some ya /\
                        (forall r, a_live A' r = a_live A r) /\ a_livebytes A' = a_livebytes A /\ a_nlive A' = a_nlive A)
          \/ (* [comment removed for export] *) (vi <> None /\ vv' = fupd (fupd (fupd vv Fstate (vi_st VIA S_TagError)) Fattr_vsb 0) Finclude_src 0 /\ vi' = None /\
                        a_live A' (vv Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                        (match vi with Some yi => a_live A' (vv Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                                                  a_livebytes A' = a_livebytes A - 80 - vb_size ya - vb_size yi /\ a_nlive A' = a_nlive A - 4
                                     | None => False end) /\
                        (forall r, r <> vv Fattr_vsb -> r <> vb_buf ya -> r <> vv Finclude_src ->
                                   r <> match vi with Some yi => vb_buf yi | None => 0 end -> a_live A' r = a_live A r))
          \/ (* [comment removed for export] *) (vi = None /\ vv' = fupd (fupd vv Fstate (vi_st VIA S_TagError)) Fattr_vsb 0 /\ vi' = None /\
                        a_live A' (vv Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                        a_livebytes A' = a_livebytes A - 40 - vb_size ya /\ a_nlive A' = a_nlive A - 2 /\
                        (forall r, r <> vv Fattr_vsb -> r <> vb_buf ya -> a_live A' r = a_live A r))
          \/ (* [comment removed for export] *) (vv Fmatch_hit = vi_tbl_attr_include VIA + 16 (* [comment removed for export] *) /\ exists ic, bool01 ic /\ vv' = fupd (fupd vv Finclude_continue ic) Fattr_vsb 0 /\ vi' = vi /\
                        a_live A' (vv Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                        a_livebytes A' = a_livebytes A - 40 - vb_size ya /\ a_nlive A' = a_nlive A - 2 /\
                        (forall r, r <> vv Fattr_vsb -> r <> vb_buf ya -> a_live A' r = a_live A r))) ->
          match vi' with
          | None => vv' Finclude_src = 0
          | Some yi => vv' Finclude_src <> 0 /\ vsb_obj LPA A' v' (vv' Finclude_src) yi true /\ vb_error yi = 0
          end ->
          cframe LPA (owned A) (owned A') (bv_unsigned sp) DOINCL_STACK
                 (fun a => blk VEP 312 a \/ vsb_blocks (vv Fattr_vsb) ya a
                           \/ match vi with Some yi => vsb_blocks (vv Finclude_src) yi a | None => False end
                           \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
                 nowhere v v' ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 vep_do_include_entry) fc None m (seg_rom rsegs)) md) T.

  (* [comment removed for export] *)
  Definition vep_do_include_tag_stmt : Prop :=
    forall (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) (vr : vsb_rec) (vi : option vsb_rec) (H : henv) (lo SB N : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (T : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v ->
      a0 = Z_to_bv 64 VEP -> a1 = Z_to_bv 64 1 ->
      vep_obj LPA A v VEP vv tag q -> vep_base H VEP vv -> henv_ok LPA VIA H A v ->
      0 <= vv Fflags < 16 -> bool01 (vv Femptytag) -> bool01 (vv Finclude_continue) -> vv Flast_mark = 1 -> vv Fattr_vsb = 0 ->
      vsb_obj LPA A v (vv Fvsb) vr false -> VEP <> vv Fvsb -> VEP <> vb_buf vr ->
      vb_size vr <= vb_len vr + 4096 ->
      vb_len vr + match vi with Some yi => vb_len yi | None => 0 end + 8 <= 2^29 ->
      (* [comment removed for export] *)
      a_livebytes A + vb_size vr + vb_len vr + 2 * match vi with Some yi => vb_len yi | None => 0 end + 12304 <= LIVE_MAX ->
      a_nlive A + 1 <= NLIVE_MAX ->
      (* [comment removed for export] *)
      match vi with Some yi => vb_len yi / 4096 | None => 0 end + 8 <= a_seccred A ->
      PRIM_ROOM + (PPOT_CAP - vsb_ppot vr) <= a_primcred A ->   (* [comment removed for export] *)
      (* [comment removed for export] *)
      lib_frames A ->
      match vi with
      | None => vv Finclude_src = 0
      | Some yi => vv Finclude_src <> 0 /\ vsb_obj LPA A v (vv Finclude_src) yi true /\ vb_error yi = 0 /\
                   vv Finclude_src <> VEP /\ vb_buf yi <> VEP /\ vv Finclude_src <> vv Fvsb /\ vv Finclude_src <> vb_buf vr /\
                   vb_buf yi <> vv Fvsb /\ vb_buf yi <> vb_buf vr
      end ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs v lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + DOINCL_STACK <= bv_unsigned sp ->
      stack_shadow LPA v SB N (bv_unsigned sp - DOINCL_STACK - 64) (bv_unsigned sp + 64) ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (vv' : vep) (vr' : vsb_rec),
          let v' := aview A' m' in
          ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md md' ->
          stk rsegs v' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' v' ->
          vep_obj LPA A' v' VEP vv' tag q -> vkeep vv vv' [Fstate; Finclude_src; Finclude_continue] ->
          (vv' Fstate = vv Fstate \/ vv' Fstate = vi_st VIA S_TagError) -> bool01 (vv' Finclude_continue) -> vv' Finclude_src = 0 ->
          vsb_obj LPA A' v' (vv Fvsb) vr' false ->
          vb_len vr <= vb_len vr' <= vb_len vr + match vi with Some yi => vb_len yi + 8 | None => 0 end ->
          vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
          (vb_buf vr' = vb_buf vr \/ (a_live A (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
          match vi with
          | None => (forall r, a_live A' r = a_live A r) /\ a_livebytes A' = a_livebytes A /\ a_nlive A' = a_nlive A
          | Some yi => a_live A' (vv Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                       (forall r, r <> vb_buf vr -> r <> vb_buf vr' -> r <> vv Finclude_src -> r <> vb_buf yi -> a_live A' r = a_live A r) /\
                       a_livebytes A' = a_livebytes A + (vb_size vr' - vb_size vr) - 40 - vb_size yi /\ a_nlive A' = a_nlive A - 2
          end ->
          frames_aged A A' 1 1 -> a_tinycred A' = a_tinycred A ->
          a_seccred A - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A ->
          a_primcred A - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A ->   (* [comment removed for export] *)
          cframe LPA (owned A) (owned A') (bv_unsigned sp) DOINCL_STACK
                 (fun a => blk VEP 312 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (vv Fvsb <= a < vv Fvsb + 40)
                           \/ match vi with Some yi => vsb_blocks (vv Finclude_src) yi a | None => False end
                           \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
                 (newblk (vb_buf vr') (vb_size vr')) v v' ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 vep_do_include_entry) fc None m (seg_rom rsegs)) md) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition vep_init_map (H : henv) (VEP S flags : Z) : vep :=
    fun f => match f with
             | Fflags => flags | Fvsb => S | Furl => vi_url VIA | Fvc => h_vc H | Fcb => vi_cb VIA
             | Fcb_priv => VEP + 56 | Fstate => vi_st VIA S_Start | Fstartup => 1 | _ => 0 end.

  Definition VEP_Init_stmt : Prop :=
    forall (H : henv) (flags : Z) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (T : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v ->
      a0 = Z_to_bv 64 (h_vc H) -> a1 = Z_to_bv 64 (h_req H) -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 flags ->
      0 <= flags < 16 ->
      ws0_obj LPA H v -> henv_ok LPA VIA H A v ->
      a_livebytes A + 408 <= LIVE_MAX -> a_nlive A + 4 <= NLIVE_MAX -> 544 <= a_primcred A (* [comment removed for export] *) ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs v lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + VEPINIT_STACK <= bv_unsigned sp ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model),
          let v' := aview A' m' in
          ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md md' ->
          stk rsegs v' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' v' ->
          frames_same A A' -> a_tinycred A' = a_tinycred A -> a_seccred A' = a_seccred A -> a_primcred A' = a_primcred A - 544 ->   (* [comment removed for export] *)
          (* [comment removed for export] *)
              (exists wa tag q b, r <> 0 /\ ws1_obj LPA H A' v' wa r /\
               (exists S, vep_obj LPA A' v' r (vep_init_map H r S flags) tag q /\ S <> 0 /\
                          vsb_obj LPA A' v' S (vsb_fresh b) false /\
                          a_live A S = None /\ a_live A b = None /\ S <> r /\ b <> r /\ S <> wa /\ b <> wa /\
                          a_live A wa = None /\ a_live A r = None /\
                          (forall p, p <> wa -> p <> r -> p <> S -> p <> b -> a_live A' p = a_live A p) /\
                          a_livebytes A' = a_livebytes A + 408 /\ a_nlive A' = a_nlive A + 4 /\
                          cframe LPA (owned A) (owned A') (bv_unsigned sp) VEPINIT_STACK
                                 (fun a => h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32)
                                 (fun a => newblk wa 40 a \/ newblk r 312 a \/ newblk S 40 a \/ newblk b 16 a) v v')) ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 VEP_Init_entry) fc None m (seg_rom rsegs)) md) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vsb_small (x : vsb_rec) (N : Z) : Prop := vb_size x <= vb_len x + 4096 /\ vb_len x <= N.
  (* [comment removed for export] *)
  Definition PARSE_LIVE (N : Z) : Z := 24 * N + 32768.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition PARSE_NLIVE : Z := 5.
  (* [comment removed for export] *)
  Definition PARSE_PRIM (N : Z) : Z := 12 * N + PRIM_ROOM + PPOT_CAP - 96.
  (* [comment removed for export] *)
  Definition PARSE_CRED (N : Z) : Z := N / 682 + 16.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition FIN_CRED (N : Z) : Z := 8.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition world_nlive (va : option vsb_rec) (vi : option (vsb_rec * bool)) : Z :=
    match va with None => 0 | Some _ => 2 end + match vi with None => 0 | Some _ => 2 end.
  Lemma world_nlive_nonneg : forall va vi, 0 <= world_nlive va vi <= 4.
  Proof. intros [x|] [[y b]|]; unfold world_nlive; lia. Qed.
  (* [comment removed for export] *)
  Definition FIN_LIVE (N : Z) : Z := 20 * N + 16384.

  Definition parsed_world (H : henv) (A : AS) (v : mem) (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads)
             (vr : vsb_rec) (va : option vsb_rec) (vi : option (vsb_rec * bool)) (wa n N : Z) : Prop :=
       vep_obj LPA A v VEP vv tag q /\ vep_base H VEP vv
    /\ (exists st, vv Fstate = vi_st VIA st) /\ bool01 (vv Flast_mark) /\ bool01 (vv Fesi_found)
    /\ vep_cnt vv n /\ 0 <= n <= N /\ N < NMAX /\ 4096 <= vv Fver_p <= alloc_ceiling
    /\ vsb_obj LPA A v (vv Fvsb) vr false /\ vsb_room vr N /\ vsb_apart (vv Fvsb) vr [VEP; wa]
    /\ match va with
       | None => vv Fattr_vsb = 0
       | Some x => vsb_obj LPA A v (vv Fattr_vsb) x false /\ vb_size x + 9 <= EXT_MAX /\ vsb_small x N /\
                   vsb_apart (vv Fattr_vsb) x [VEP; wa; vv Fvsb; vb_buf vr]
       end
    /\ match vi with
       | None => vv Finclude_src = 0
       | Some (x, fi) => vsb_obj LPA A v (vv Finclude_src) x fi /\ vsb_small x N /\
                   vsb_apart (vv Finclude_src) x [VEP; wa; vv Fvsb; vb_buf vr] /\
                   match va with None => True | Some y => vsb_apart (vv Finclude_src) x [vv Fattr_vsb; vb_buf y] end
       end.

  (* [comment removed for export] *)
  Definition world_bytes (vr : vsb_rec) (va : option vsb_rec) (vi : option (vsb_rec * bool)) : Z :=
    40 + vb_size vr
    + match va with None => 0 | Some x => 40 + vb_size x end
    + match vi with None => 0 | Some (x, _) => 40 + vb_size x end.

  (* [comment removed for export] *)
  Definition parse_changed (H : henv) (VEP S b : Z) (a : Z) : Prop :=
    blk VEP 312 a \/ blk S 40 a \/ newblk b 16 a \/ (h_vsc H + 1304 <= a < h_vsc H + 1320).
  Definition finish_changed (H : henv) (VEP : Z) (vv : vep) (vr : vsb_rec) (va : option vsb_rec)
             (vi : option (vsb_rec * bool)) (a : Z) : Prop :=
    blk VEP 312 a \/ vsb_blocks (vv Fvsb) vr a
    \/ match va with None => False | Some x => vsb_blocks (vv Fattr_vsb) x a end
    \/ match vi with None => False | Some (x, _) => vsb_blocks (vv Finclude_src) x a end
    \/ (h_vsc H + 1304 <= a < h_vsc H + 1320).
  (* [comment removed for export] *)
  Definition parse_blocks (vv : vep) (vr : vsb_rec) (va : option vsb_rec) (vi : option (vsb_rec * bool)) (x : Z) : Prop :=
    x = vb_buf vr
    \/ match va with None => False | Some y => x = vv Fattr_vsb \/ x = vb_buf y end
    \/ match vi with None => False | Some (y, _) => x = vv Finclude_src \/ x = vb_buf y end.
  (* [comment removed for export] *)
  Definition parse_new (vv : vep) (vr : vsb_rec) (va : option vsb_rec) (vi : option (vsb_rec * bool)) (a : Z) : Prop :=
    newblk (vb_buf vr) (vb_size vr) a
    \/ match va with None => False | Some x => vsb_blocks (vv Fattr_vsb) x a end
    \/ match vi with None => False | Some (x, _) => vsb_blocks (vv Finclude_src) x a end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition VEP_Parse_stmt : Prop :=
    forall (H : henv) (VEP S b flags wa DATA : Z) (inp : list byte) (tag : list byte) (q : vep_pads) (lo SB N : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (T : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v ->
      a0 = Z_to_bv 64 VEP -> a1 = Z_to_bv 64 DATA -> a2 = Z_to_bv 64 (Z.of_nat (length inp)) ->
      0 <= flags < 16 ->
      vep_obj LPA A v VEP (vep_init_map H VEP S flags) tag q -> S <> 0 ->
      vsb_obj LPA A v S (vsb_fresh b) false ->
      ws1_obj LPA H A v wa VEP -> data_obj LPA A v DATA inp ->
      henv_ok LPA VIA H A v ->
      VEP <> S -> VEP <> b -> wa <> S -> wa <> b -> DATA <> VEP -> DATA <> S -> DATA <> b -> DATA <> wa ->
      a_livebytes A + PARSE_LIVE (Z.of_nat (length inp)) <= LIVE_MAX -> a_nlive A + PARSE_NLIVE <= NLIVE_MAX ->
      PARSE_CRED (Z.of_nat (length inp)) <= a_seccred A -> PARSE_PRIM (Z.of_nat (length inp)) <= a_primcred A (* [comment removed for export] *) ->
      lib_frames A ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 64 <= 2^47 ->
      stk rsegs v lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + PARSE_STACK <= bv_unsigned sp ->
      stack_shadow LPA v SB N (bv_unsigned sp - PARSE_STACK - 64) (bv_unsigned sp + 64) ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (vv' : vep) (tag' : list byte) (q' : vep_pads) (vr' : vsb_rec) (va : option vsb_rec)
              (vi : option (vsb_rec * bool)) (n : Z),
          let v' := aview A' m' in
          ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md md' ->
          stk rsegs v' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' v' ->
          parsed_world H A' v' VEP vv' tag' q' vr' va vi wa n (Z.of_nat (length inp)) -> vv' Fvsb = S ->
          DATA <= vv' Fver_p <= DATA + Z.of_nat (length inp) ->
          ws1_obj LPA H A' v' wa VEP -> data_obj LPA A' v' DATA inp ->
          (* [comment removed for export] *)
          (forall p k, a_live A p = Some k -> p <> b -> a_live A' p = Some k) ->
          (forall x, parse_blocks vv' vr' va vi x -> x = b \/ a_live A x = None) ->
          frames_same A A' ->
          a_livebytes A' = a_livebytes A - 56 + world_bytes vr' va vi ->
          a_tinycred A' = a_tinycred A -> a_nlive A' = a_nlive A + world_nlive va vi ->
          a_seccred A - PARSE_CRED (Z.of_nat (length inp)) <= a_seccred A' <= a_seccred A ->
          a_primcred A - (12 * Z.of_nat (length inp) + (vsb_ppot vr' - 96)) <= a_primcred A' <= a_primcred A ->   (* [comment removed for export] *)
          cframe LPA (owned A) (owned A') (bv_unsigned sp) PARSE_STACK (parse_changed H VEP S b)
                 (parse_new vv' vr' va vi) v v' ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 VEP_Parse_entry) fc None m (seg_rom rsegs)) md) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition VEP_Finish_stmt : Prop :=
    forall (H : henv) (VEP wa n N DATA : Z) (vv : vep) (tag : list byte) (q : vep_pads) (vr : vsb_rec) (va : option vsb_rec)
           (vi : option (vsb_rec * bool)) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (T : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v ->
      a0 = Z_to_bv 64 VEP ->
      parsed_world H A v VEP vv tag q vr va vi wa n N ->
      ws1_obj LPA H A v wa VEP -> henv_ok LPA VIA H A v ->
      (* [comment removed for export] *)
      a_live A DATA = Some N -> 0 < N -> DATA <= vv Fver_p <= DATA + N -> DATA <> VEP -> DATA <> vv Fvsb ->
      ~ parse_blocks vv vr va vi DATA ->
      a_livebytes A + FIN_LIVE N <= LIVE_MAX -> a_nlive A + 1 <= NLIVE_MAX -> FIN_CRED N <= a_seccred A ->
      PRIM_ROOM + (PPOT_CAP - vsb_ppot vr) <= a_primcred A ->   (* [comment removed for export] *)
      frames_young A 4 0 ->   (* [comment removed for export] *)
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs v lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + VEPFIN_STACK <= bv_unsigned sp ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model)
              (vv' : vep) (vr' : vsb_rec),
          let v' := aview A' m' in
          ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md md' ->
          stk rsegs v' lo (bv_unsigned sp) -> henv_ok LPA VIA H A' v' ->
          vep_obj LPA A' v' VEP vv' tag q -> ws1_obj LPA H A' v' wa VEP ->
          (r = 0 \/ (r <> 0 /\ r = vv Fvsb /\ vsb_obj LPA A' v' r vr' true /\ vsb_apart r vr' [VEP; wa] /\
                     (parse_blocks vv vr va vi (vb_buf vr') \/ a_live A (vb_buf vr') = None))) ->
          (* [comment removed for export] *)
          (forall p k, a_live A p = Some k -> p <> vv Fvsb -> ~ parse_blocks vv vr va vi p -> a_live A' p = Some k) ->
          frames_aged A A' 4 0 ->
          a_livebytes A' = a_livebytes A - world_bytes vr va vi + (if Z.eqb r 0 then 0 else 40 + vb_size vr') ->
          a_tinycred A' = a_tinycred A -> a_nlive A' = a_nlive A - world_nlive va vi - (if Z.eqb r 0 then 2 else 0) ->
          a_seccred A - FIN_CRED N <= a_seccred A' <= a_seccred A ->
          a_primcred A - (PPOT_CAP - vsb_ppot vr) <= a_primcred A' <= a_primcred A ->   (* [comment removed for export] *)
          cframe LPA (owned A) (owned A') (bv_unsigned sp) VEPFIN_STACK (finish_changed H VEP vv vr va vi)
                 (fun a => r <> 0 /\ vsb_blocks r vr' a) v v' ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 VEP_Finish_entry) fc None m (seg_rom rsegs)) md) T.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition LIB_ENTRY : Z := 0x86cdc.
  (* [comment removed for export] *)
  Definition LIB_STACK : Z := 12288.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition LIB_LIVE (N : Z) : Z := 29 * N + 16777216.
  Definition LIB_NLIVE : Z := 16.
  (* [comment removed for export] *)
  Definition LIB_PRIM (N : Z) : Z := 12 * N + 1048576.
  (* [comment removed for export] *)
  Definition LIB_SECC (N : Z) : Z := N / 682 + 64.   (* [comment removed for export] *)

  Record alib_pre (sp tp a0 a1 : word) (m : mem) (md : Model) (A : AS) (data : Z) (inp : list byte) (SB N : Z) : Prop := {
    lp_a0 : a0 = Z_to_bv 64 data;
    lp_a1 : a1 = Z_to_bv 64 (Z.of_nat (length inp));
    lp_tp : tp = cl_tp LPA;
    lp_sp16 : bv_unsigned sp mod 16 = 0;
    lp_sp_lo : alloc_ceiling + 65536 + LIB_STACK <= bv_unsigned sp;
    lp_sp_hi : bv_unsigned sp + 64 <= 2^47;
    lp_ainv : ainv A m md;
    lp_mi : mem_inv rsegs (aview A m);
    lp_stk : stk rsegs (aview A m) (bv_unsigned sp - LIB_STACK) (bv_unsigned sp);
    lp_stksh : stack_shadow LPA (aview A m) SB N (bv_unsigned sp - LIB_STACK) (bv_unsigned sp + 64);
    lp_errno : exists e, rw_cells rsegs (aview A m) ERRNOA [C4 e];
    lp_bss_vsc : exists w, rw_cells rsegs (aview A m) (vi_bss_vsc VIA) [C8 w];
    lp_bss_cp : exists w, rw_cells rsegs (aview A m) (vi_bss_cp VIA) [C8 w];
    lp_frames : forall ff, a_frame A ff = None;
    lp_size : Z.of_nat (length inp) < NMAX;
    lp_inp : length inp <> 0%nat ->
             data <> 0 /\ a_live A data = Some (Z.of_nat (length inp)) /\ bytes_at rsegs (aview A m) data inp;
    lp_budget : a_livebytes A + LIB_LIVE (Z.of_nat (length inp)) <= LIVE_MAX /\ a_nlive A + LIB_NLIVE <= NLIVE_MAX;
    lp_seccred : LIB_SECC (Z.of_nat (length inp)) <= a_seccred A;
    lp_primcred : LIB_PRIM (Z.of_nat (length inp)) <= a_primcred A   (* [comment removed for export] *)
  }.

  Record alib_post (sp : word) (m : mem) (md : Model) (A : AS) (inp : list byte) (SB N : Z)
                   (m' : mem) (md' : Model) (A' : AS) : Prop := {
    lq_ainv : ainv A' m' md';
    lq_mi : mem_inv rsegs (aview A' m');
    lq_mdf : amd_frame md md';
    lq_live : forall p n, a_live A p = Some n -> a_live A' p = Some n;   (* [comment removed for export] *)
    lq_live_bytes : forall p n i, a_live A p = Some n -> 0 <= i < n -> aview A' m' (Z_to_bv 64 (p + i)) = aview A m (Z_to_bv 64 (p + i));
    lq_frames : forall ff, a_frame A' ff = a_frame A ff;
    lq_budget : a_livebytes A' = a_livebytes A /\ a_nlive A' = a_nlive A /\ a_tinycred A' = a_tinycred A;
    lq_seccred : a_seccred A - LIB_SECC (Z.of_nat (length inp)) <= a_seccred A' <= a_seccred A;
    lq_primcred : a_primcred A - LIB_PRIM (Z.of_nat (length inp)) <= a_primcred A' <= a_primcred A;   (* [comment removed for export] *)
    lq_stk : stk rsegs (aview A' m') (bv_unsigned sp - LIB_STACK) (bv_unsigned sp);
    lq_stksh : stack_shadow LPA (aview A' m') SB N (bv_unsigned sp - LIB_STACK) (bv_unsigned sp + 64);
    lq_errno : exists e, rw_cells rsegs (aview A' m') ERRNOA [C4 e];
    lq_bss_vsc : exists w, rw_cells rsegs (aview A' m') (vi_bss_vsc VIA) [C8 w];
    lq_bss_cp : exists w, rw_cells rsegs (aview A' m') (vi_bss_cp VIA) [C8 w];
    lq_cframe : cframe LPA (owned A) (owned A') (bv_unsigned sp) LIB_STACK
                       (fun a => (vi_bss_vsc VIA <= a < vi_bss_vsc VIA + 8) \/ (vi_bss_cp VIA <= a < vi_bss_cp VIA + 8))
                       nowhere (aview A m) (aview A' m')
  }.

  Definition alib_call_ok : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (data : Z) (inp : list byte) (SB N : Z) (T : TSet),
      alib_pre sp tp a0 a1 m md A data inp SB N ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (md' : Model) (A' : AS),
          alib_post sp m md A inp SB N m' md' A' ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 LIB_ENTRY) fc None m (seg_rom rsegs)) md) T.
End C.
