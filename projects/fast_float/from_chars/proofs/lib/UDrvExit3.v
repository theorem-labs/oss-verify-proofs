(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec CatSim SeqExec StepTac StoreOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Frame DriverCfg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.Frame OSSVerify.Proofs.fast_float.from_chars.lib.Common.DriverCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxSubst FxStep FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UDrvData UDrvMain UDrvCall UbStdioDefs UbExitBase UDrvExit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac bvlit := vm_compute; try (f_equal; repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]); try reflexivity).

(* [comment removed for export] *)
Definition c21_reg (c21 : tree bval) : Prop :=
  get_bytes c21 16 8 = Some (bks 0x979f0 8) /\ get_bytes c21 8 4 = Some (bks 1 4) /\
  get_bytes c21 32 8 = Some (bks 0x52b8c 8) /\ get_bytes c21 288 8 = Some (bks 0x22cf4 8) /\
  untracked c21 4 4 = true /\ untracked c21 24 8 = true.

Section ExitGen3.
Variable sp0 tid : word.
Hypothesis SL : 0x7fff80000000 <= bv_unsigned sp0.
Hypothesis SH : bv_unsigned sp0 <= 0x800000000000.
Hypothesis Htid : 0 < bv_unsigned tid < 2 ^ 22.

#[using="SL SH Htid"] Theorem exit_pre_gen2r : forall E3 L ms3 model (csp c : Z) (i0 i3 i7 i9 i21 : nat) (o0 : Z) (c7 c9 c21 : tree bval) (k7 k9 : rkind) (wp2 rp2 : word) (pending : list byte),
  sden PSEGS E3 L ms3 -> lden E3 SP0 = sp0 -> lden E3 T = tid -> -65536 + 144 <= csp <= 0 -> 0 <= c < 2 ^ 64 ->
  exit_glob (ms_mem ms3) -> m_halted model = None -> m_vm_lazy model = [] ->
  rget (s_regs L) (rkey 2) = laddc SP0 csp -> rget (s_regs L) (rkey 4) = lconst 0x77990 ->
  rget (s_regs L) (rkey 10) = lconst c ->
  nth_error (s_rgs L) i3 = Some (RGz (lconst 0x65a18) 344 RO TEmpty) ->
  nth_error (s_rgs L) i7 = Some (RGz (lconst 0x778e8) 8 k7 c7) -> get_bytes c7 0 4 = Some (bvs_of T 4) ->
  nth_error (s_rgs L) i9 = Some (RGz (lconst 0x76e20) 24 k9 c9) -> get_bytes c9 4 1 = Some [BK 0] ->
  nth_error (s_rgs L) i21 = Some (RGz (lconst 0x979d8) 296 RI c21) -> c21_reg c21 ->
  frame_in E3 L i0 o0 144 (bv_unsigned sp0 + csp - 144) ->
  file_clean (ms_mem ms3) 0x66bd8 wp2 rp2 ->
  ((pending = [] /\ exists wp1 rp1, file_clean (ms_mem ms3) 0x66cc8 wp1 rp1)
   \/ (exists (wb wp : Z) (bufp bufsz rp1 can : word), stdout_pending (ms_mem ms3) wb wp bufp bufsz rp1 can pending
          /\ fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)))) ->
  exit_pre (ms_regs ms3) (ms_mem ms3) model (Z_to_bv 64 c) pending.
Proof. LiaFast.lf_pins (fun (SL SH Htid : LiaFast.U) => LiaFast.u0).
  intros E3 L ms3 model csp c i0 i3 i7 i9 i21 o0 c7 c9 c21 k7 k9 wp2 rp2 pending Hd3 HSP HT Hcsp Hc EG Hh Hl G2 G4 G10 N3 N7 C7 N9 C9 N21 C21 FRM FC5 SO.
  assert (Q2 : getr (ms_regs ms3) 2 = Z_to_bv 64 (bv_unsigned sp0 + csp)).
  { rewrite (getr_leaf PSEGS E3 L ms3 2 (laddc SP0 csp) Hd3 G2). rewrite lden_laddc, HSP. reflexivity. }
  assert (Q4 : getr (ms_regs ms3) 4 = Z_to_bv 64 0x77990) by exact (getr_leaf_c PSEGS E3 L ms3 4 _ Hd3 G4).
  assert (Q10 : getr (ms_regs ms3) 10 = Z_to_bv 64 c) by exact (getr_leaf_c PSEGS E3 L ms3 10 _ Hd3 G10).
  destruct EG as (G1 & Gfa & Gc & Gn & Go & Gi & Gso & Gse).
  pose proof (sden_rg _ _ _ _ _ _ Hd3 N3) as HR3.
  assert (GOT : forall o, 0 <= o -> o + 8 <= 344 ->
            rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x65a18 + o)) 8 = rdn PSEGS (fun _ => None) (Z_to_bv 64 (0x65a18 + o)) 8).
  { intros o Ho1 Ho2.
    pose proof (rg_rdn_img PSEGS E3 _ _ o 8 HR3 (or_introl eq_refl) Ho1 ltac:(rsz_simpl; lia)) as X.
    cbn [RGz rg_base] in X. rewrite u_lconst in X by lia. apply X. intros j Hj. apply tget_empty. }
  (* [comment removed for export] *)
  pose proof (sden_rg _ _ _ _ _ _ Hd3 N21) as HR21.
  destruct C21 as (Ahd & Asl & Af0 & Aa0 & Ulk & Unx).
  assert (ATK : forall o n bvs, get_bytes c21 o n = Some bvs -> 0 <= o ->
            rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x979d8 + o)) n = Some (map (bden E3) bvs)).
  { intros o n bvs Hg Ho. pose proof (rg_rdn_gb PSEGS E3 _ _ o n bvs HR21 Ho Hg) as X. cbn [RGz rg_base] in X.
    rewrite u_lconst in X by lia. exact X. }
  assert (AUN : forall o n, untracked c21 o n = true -> 0 <= o -> o + Z.of_nat n <= 296 ->
            rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x979d8 + o)) n = rdn PSEGS (fun _ => None) (Z_to_bv 64 (0x979d8 + o)) n).
  { intros o n Hu Ho1 Ho2.
    pose proof (rg_rdn_img PSEGS E3 _ _ o n HR21 (or_intror eq_refl) Ho1 ltac:(rsz_simpl; lia)) as X.
    cbn [RGz rg_base] in X. rewrite u_lconst in X by lia. apply X. intros j Hj. exact (untracked_spec _ _ _ Hu j Hj). }
  (* [comment removed for export] *)
  pose proof (sden_rg _ _ _ _ _ _ Hd3 N9) as HR9.
  assert (ACB : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x76e20 + 4)) 1 = Some (map (bden E3) [BK 0])).
  { pose proof (rg_rdn_gb PSEGS E3 _ _ 4 1 [BK 0] HR9 ltac:(lia) C9) as X. cbn [RGz rg_base] in X.
    rewrite u_lconst in X by lia. exact X. }
  pose proof (sden_rg _ _ _ _ _ _ Hd3 N7) as HR7.
  assert (TD : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x778e8 + 0)) 4 = Some (word_to_le_bytes 4 tid)).
  { pose proof (rg_rdn_gb PSEGS E3 _ _ 0 4 (bvs_of T 4) HR7 ltac:(lia) C7) as X. cbn [RGz rg_base] in X.
    rewrite u_lconst in X by lia. rewrite X, bvs_of_den_lin, HT. reflexivity. }
  pose proof (frame_in_store_ok E3 L ms3 i0 o0 144 _ Hd3 FRM ltac:(lia)) as SOK.
  exists (Z_to_bv 64 (bv_unsigned sp0 + csp)), (Z_to_bv 64 0x77990), (bv_unsigned tid), wp2, rp2.
  split; [|split; [exact Hh|split; [exact Hl|exact SO]]].
  constructor.
  + exact Q2.
  + exact Q4.
  + exact Q10.
  + rewrite u_small64 by (unfold two64; lia). lia.
  + rewrite u_small64 by (unfold two64; lia). lia.
  + rewrite u_small64 by (unfold two64; lia). exact SOK.
  + vm_compute. intros Hc'; discriminate Hc'.
  + vm_compute. intros Hc'; discriminate Hc'.
  + lia.
  + rewrite Z_to_bv_bv_unsigned. replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0x77990) - 168)) with (Z_to_bv 64 (0x778e8 + 0)) by reflexivity.
    exact TD.
  + exact G1.
  + replace (Z_to_bv 64 0x65b60) with (Z_to_bv 64 (0x65a18 + 328)) by reflexivity. rewrite GOT by lia. bvlit.
  + replace (Z_to_bv 64 0x65b68) with (Z_to_bv 64 (0x65a18 + 336)) by reflexivity. rewrite GOT by lia. bvlit.
  + exact Gfa.
  + exact Gc.
  + replace (Z_to_bv 64 0x65a48) with (Z_to_bv 64 (0x65a18 + 48)) by reflexivity. rewrite GOT by lia. bvlit.
  + replace (Z_to_bv 64 0x65a50) with (Z_to_bv 64 (0x65a18 + 56)) by reflexivity. rewrite GOT by lia. bvlit.
  + split; [exact Gn|split; [exact Go|split; [exact Gi|split; [exact Gso|exact Gse]]]].
  + exact FC5.
  + replace (Z_to_bv 64 0x979dc) with (Z_to_bv 64 (0x979d8 + 4)) by reflexivity. rewrite (AUN 4 4%nat Ulk) by lia. bvlit.
  + right. unfold atx_reg.
    split; [replace (Z_to_bv 64 0x979e8) with (Z_to_bv 64 (0x979d8 + 16)) by reflexivity; rewrite (ATK 16 8%nat _ Ahd) by lia; bvlit|].
    split; [replace (Z_to_bv 64 0x979e0) with (Z_to_bv 64 (0x979d8 + 8)) by reflexivity; rewrite (ATK 8 4%nat _ Asl) by lia; bvlit|].
    split; [replace (Z_to_bv 64 0x979f8) with (Z_to_bv 64 (0x979d8 + 32)) by reflexivity; rewrite (ATK 32 8%nat _ Af0) by lia; bvlit|].
    split; [replace (Z_to_bv 64 0x97af8) with (Z_to_bv 64 (0x979d8 + 288)) by reflexivity; rewrite (ATK 288 8%nat _ Aa0) by lia; bvlit|].
    split; [replace (Z_to_bv 64 0x979f0) with (Z_to_bv 64 (0x979d8 + 24)) by reflexivity; rewrite (AUN 24 8%nat Unx) by lia; bvlit|].
    replace (Z_to_bv 64 0x76e24) with (Z_to_bv 64 (0x76e20 + 4)) by reflexivity. rewrite ACB. bvlit.
Qed.
End ExitGen3.
