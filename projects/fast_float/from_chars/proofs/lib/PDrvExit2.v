(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec CatSim SeqExec StepTac StoreOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Frame DriverCfg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.Frame OSSVerify.Proofs.fast_float.from_chars.lib.Common.DriverCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxSubst FxStep FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PDrvData PDrvMain PDrvCall RefStdioDefs RefExitBase PDrvExit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section ExitGen2.
Variable sp0 tid : word.
Hypothesis SL : 0x7fff80000000 <= bv_unsigned sp0.
Hypothesis SH : bv_unsigned sp0 <= 0x800000000000.
Hypothesis Htid : 0 < bv_unsigned tid < 2 ^ 22.

#[using="SL SH Htid"] Theorem exit_pre_gen2 : forall E3 L ms3 model (csp c : Z) (i0 i3 i7 i21 : nat) (o0 : Z) (c7 : tree bval) (k7 : rkind) (wp2 rp2 : word) (pending : list byte),
  sden PSEGS E3 L ms3 -> lden E3 SP0 = sp0 -> lden E3 T = tid -> -65536 + 144 <= csp <= 0 -> 0 <= c < 2 ^ 64 ->
  exit_glob (ms_mem ms3) -> m_halted model = None -> m_vm_lazy model = [] ->
  rget (s_regs L) (rkey 2) = laddc SP0 csp -> rget (s_regs L) (rkey 4) = lconst 0x75bd0 ->
  rget (s_regs L) (rkey 10) = lconst c ->
  nth_error (s_rgs L) i3 = Some (RGz (lconst 0x63c60) 344 RO TEmpty) ->
  nth_error (s_rgs L) i7 = Some (RGz (lconst 0x75b28) 8 k7 c7) -> get_bytes c7 0 4 = Some (bvs_of T 4) ->
  nth_error (s_rgs L) i21 = Some (RGz (lconst 0x95c18) 296 RI TEmpty) ->
  frame_in E3 L i0 o0 144 (bv_unsigned sp0 + csp - 144) ->
  file_clean (ms_mem ms3) 0x64e20 wp2 rp2 ->
  ((pending = [] /\ exists wp1 rp1, file_clean (ms_mem ms3) 0x64f10 wp1 rp1)
   \/ (exists (wb wp : Z) (bufp bufsz rp1 can : word), stdout_pending (ms_mem ms3) wb wp bufp bufsz rp1 can pending
          /\ fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)))) ->
  exit_pre (ms_regs ms3) (ms_mem ms3) model (Z_to_bv 64 c) pending.
Proof. LiaFast.lf_pins (fun (SL SH Htid : LiaFast.U) => LiaFast.u0).
  intros E3 L ms3 model csp c i0 i3 i7 i21 o0 c7 k7 wp2 rp2 pending Hd3 HSP HT Hcsp Hc EG Hh Hl G2 G4 G10 N3 N7 C7 N21 FRM FC5 SO.
  assert (Q2 : getr (ms_regs ms3) 2 = Z_to_bv 64 (bv_unsigned sp0 + csp)).
  { rewrite (getr_leaf PSEGS E3 L ms3 2 (laddc SP0 csp) Hd3 G2). rewrite lden_laddc, HSP. reflexivity. }
  assert (Q4 : getr (ms_regs ms3) 4 = Z_to_bv 64 0x75bd0) by exact (getr_leaf_c PSEGS E3 L ms3 4 _ Hd3 G4).
  assert (Q10 : getr (ms_regs ms3) 10 = Z_to_bv 64 c) by exact (getr_leaf_c PSEGS E3 L ms3 10 _ Hd3 G10).
  destruct EG as (G1 & Gfa & Gc & Gn & Go & Gi & Gso & Gse).
  pose proof (sden_rg _ _ _ _ _ _ Hd3 N3) as HR3.
  assert (GOT : forall o, 0 <= o -> o + 8 <= 344 ->
            rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x63c60 + o)) 8 = rdn PSEGS (fun _ => None) (Z_to_bv 64 (0x63c60 + o)) 8).
  { intros o Ho1 Ho2.
    pose proof (rg_rdn_img PSEGS E3 _ _ o 8 HR3 (or_introl eq_refl) Ho1 ltac:(rsz_simpl; lia)) as X.
    cbn [RGz rg_base] in X. rewrite u_lconst in X by lia. apply X. intros j Hj. apply tget_empty. }
  pose proof (sden_rg _ _ _ _ _ _ Hd3 N21) as HR21.
  assert (ATX : forall o n, 0 <= o -> o + Z.of_nat n <= 296 ->
            rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x95c18 + o)) n = rdn PSEGS (fun _ => None) (Z_to_bv 64 (0x95c18 + o)) n).
  { intros o n Ho1 Ho2.
    pose proof (rg_rdn_img PSEGS E3 _ _ o n HR21 (or_intror eq_refl) Ho1 ltac:(rsz_simpl; lia)) as X.
    cbn [RGz rg_base] in X. rewrite u_lconst in X by lia. apply X. intros j Hj. apply tget_empty. }
  pose proof (sden_rg _ _ _ _ _ _ Hd3 N7) as HR7.
  assert (TD : rdn PSEGS (ms_mem ms3) (Z_to_bv 64 (0x75b28 + 0)) 4 = Some (word_to_le_bytes 4 tid)).
  { pose proof (rg_rdn_gb PSEGS E3 _ _ 0 4 (bvs_of T 4) HR7 ltac:(lia) C7) as X. cbn [RGz rg_base] in X.
    rewrite u_lconst in X by lia. rewrite X, bvs_of_den_lin, HT. reflexivity. }
  pose proof (frame_in_store_ok E3 L ms3 i0 o0 144 _ Hd3 FRM ltac:(lia)) as SOK.
  exists (Z_to_bv 64 (bv_unsigned sp0 + csp)), (Z_to_bv 64 0x75bd0), (bv_unsigned tid), wp2, rp2.
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
  + rewrite Z_to_bv_bv_unsigned. replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0x75bd0) - 168)) with (Z_to_bv 64 (0x75b28 + 0)) by reflexivity.
    exact TD.
  + exact G1.
  + replace (Z_to_bv 64 0x63da8) with (Z_to_bv 64 (0x63c60 + 328)) by reflexivity. rewrite GOT by lia. bvlit.
  + replace (Z_to_bv 64 0x63db0) with (Z_to_bv 64 (0x63c60 + 336)) by reflexivity. rewrite GOT by lia. bvlit.
  + exact Gfa.
  + exact Gc.
  + replace (Z_to_bv 64 0x63c90) with (Z_to_bv 64 (0x63c60 + 48)) by reflexivity. rewrite GOT by lia. bvlit.
  + replace (Z_to_bv 64 0x63c98) with (Z_to_bv 64 (0x63c60 + 56)) by reflexivity. rewrite GOT by lia. bvlit.
  + split; [exact Gn|split; [exact Go|split; [exact Gi|split; [exact Gso|exact Gse]]]].
  + exact FC5.
  + replace (Z_to_bv 64 0x95c1c) with (Z_to_bv 64 (0x95c18 + 4)) by reflexivity. rewrite (ATX 4 4%nat) by lia. bvlit.
  + left. unfold atx_idle.
    replace (Z_to_bv 64 0x95c28) with (Z_to_bv 64 (0x95c18 + 16)) by reflexivity. rewrite (ATX 16 8%nat) by lia. bvlit.
Qed.
End ExitGen2.
