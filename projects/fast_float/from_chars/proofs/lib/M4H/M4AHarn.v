(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxStep FxSubst FxEnt FxFrame FxCall FxGenA.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn M4A_kfnf.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.M4A_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfnf.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4X Require FcdA FcdAThm FcfA FcfAThm.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require Import M4Pure.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition CON_FCD : m4con := M4Con FcdA.FP0 FcdA.FCD_Q (CKFn FcdA.FRETS).
Definition CON_FCI : m4con := M4Con OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.M4A_fci.P0 OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.M4A_fci.Q (CKFn OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.M4A_fci.RETS).
Definition CON_FCF : m4con := M4Con FcfA.FP0 FcfA.FCF_Q (CKFn FcfA.FRETS).
Definition M4A_CONS : list m4con := [CON_FCD; CON_FCI; CON_FCF].

Section H.
Hypothesis H_SM4 : kfn_ok ASEGS SM4_P0 SM4_Q.
Hypothesis H_MS32 : kfn_ok ASEGS MEMSET32_P0 MEMSET32_Q.
Hypothesis H_MS27 : kfn_ok ASEGS MEMSET27_P0 MEMSET27_Q.
Hypothesis H_SSF5 : kfn_ok ASEGS SSF5_P0 SSF5_Q.
Hypothesis H_DCF : forall frac, kfrag_ok ASEGS (DCF_P0 frac) (DCF_Q frac) 0x93b98.
Hypothesis H_DCFf : forall frac, kfrag_ok ASEGS (DCF_P0f frac) (DCF_Qf frac) 0x9b078.

#[using="H_SM4 H_MS32 H_MS27 H_SSF5 H_DCF H_DCFf"] Theorem M4A_cons_ok : Forall (con_ok ASEGS) M4A_CONS.
Proof. LiaFast.lf_pins (fun (H_SM4 H_MS32 H_MS27 H_SSF5 H_DCF H_DCFf : LiaFast.U) => LiaFast.u0).
  unfold M4A_CONS. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold con_ok; cbn [mc_kind mc_p0 mc_q].
  - exact (FcdAThm.fcd_ok H_SM4 H_MS32 H_MS27 H_SSF5 H_DCF).
  - exact OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.M4A_fci.fci_ok.
  - exact (FcfAThm.fcf_ok H_SM4 H_MS32 H_MS27 H_SSF5 H_DCFf).
Qed.

(* [comment removed for export] *)
#[using="H_SM4 H_MS32 H_MS27 H_SSF5 H_DCF H_DCFf"] Theorem ppostM4A_ok {MT : Type} : forall p S (M : MT) K, ppostM M4A_CONS p S M = Some K ->
  (forall E ms, sden ASEGS E S ms ->
     exists ms'' E'', isteps ASEGS ms ms'' /\ sden ASEGS E'' K ms'' /\ agree (s_next S) E E'' /\
       (forall x, fr_pt E (s_rgs S) x -> ms_mem ms'' x = ms_mem ms x)) /\
  (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins (fun (H_SM4 H_MS32 H_MS27 H_SSF5 H_DCF H_DCFf : LiaFast.U) => LiaFast.u0). exact (ppostM_ok ASEGS M4A_CONS M4A_cons_ok). Qed.
End H.
