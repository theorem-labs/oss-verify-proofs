(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths changed; 150 of its 167 lines of code are new or changed and 50 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_lock/lib/Prog/FrameRet.v, with its module paths and module names changed; 15 of its 59 lines of code are new or changed and 123 lines of the source are left out. *)
(* The agreement side of the frame step for a fuzz target that returns 0 or -1, U half, for fuzz_lock.ubsan:
   U/SlotAgree.v lib_contract_cg for a return function ret, over U/Prog/FrameRet.v's lib_post_gr.

   U/SlotAgree.v lib_contract_cg is U/Contract.v lib_contract_g with crealizes (realizes and cut_free) in place
   of realizes; its leaf carries U/Contract.v lib_post_g, which fixes the return register and ll_ret l at 0.
   fuzz_lock's LLVMFuzzerTestOneInput returns -1 on an empty name and on a name byte that is NUL, LF or a
   separator (fuzz_lock.c:191-197), so no walk of that binary meets lib_contract_cg; it meets lib_contract_cgr
   lock_ret, which is lib_contract_cg with lib_post_gr (ret pl) in place of lib_post_g, exactly as
   U/Prog/FrameRet.v's lib_contract_gr does for the halting side. lib_contract_cgr_0_iff: lib_contract_cgr
   (fun _ => 0) and lib_contract_cg are equivalent, so at the return 0 the statement asks exactly what the kit's
   asks. This file is the specification of a change to the K2 kit; nothing here is proved about the image. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Contract Img0 SlotAgree.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import FrameRet.
Import ListNotations.
Local Open Scope Z_scope.

Section R.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.

(* U/SlotAgree.v lib_contract_cg, with lib_post_gr (ret pl): on the payload pl every call returns ret pl *)
Definition lib_contract_cgr (ret : list byte -> Z) (G R : list (Z * Z))
    (GI : nat -> (word -> option byte) -> Prop) (j : nat) (pc ra empty stk : Z) : Prop :=
  forall L A regs mem md p n pl b (K : lleaf -> TSet),
    lib_pre_x B API stk empty L A regs mem md ra p n pl b ->
    GI j mem ->
    G_img_c B R mem ->
    ro_agree segs mem ->
    spZ regs <= TASK_SIZE ->
    frm_zero fp_csr ->
    (forall (l : lleaf) (c' : config),
       (exists (fx' : FPState) L' A' regs' mem' md',
          c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
          frm_zero (@fp_csr fx') /\
          lib_post_gr B API (ret pl) G stk L A regs mem md p n b l L' A' regs' mem' md' /\
          GI (S j) mem') ->
       crealizes B c' (K l)) ->
    crealizes B (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (LIBK pl (m_fs md) K).

(* every function that meets U/SlotAgree.v lib_contract_cg meets lib_contract_cgr for the return 0 *)
Lemma lib_contract_cgr_of_cg : forall G R GI j pc ra empty stk,
  lib_contract_cg B API G R GI j pc ra empty stk -> lib_contract_cgr (fun _ => 0) G R GI j pc ra empty stk.
Proof.
  intros G R GI j pc ra empty stk H L A regs mem md p n pl b K Hpre HGI HR Hro Hsp Hfrm HK.
  apply (H L A regs mem md p n pl b K Hpre HGI HR Hro Hsp Hfrm).
  intros l c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hpost & HGI').
  apply HK. exists fx', L', A', regs', mem', md'. split; [exact Hc|]. split; [exact Hf|].
  split; [exact (lib_post_gr_of_g B API G stk L A regs mem md p n b l L' A' regs' mem' md' Hpost) | exact HGI'].
Qed.

(* every function that meets lib_contract_cgr for the return 0 meets U/SlotAgree.v lib_contract_cg *)
Lemma lib_contract_cg_of_cgr0 : forall G R GI j pc ra empty stk,
  lib_contract_cgr (fun _ => 0) G R GI j pc ra empty stk -> lib_contract_cg B API G R GI j pc ra empty stk.
Proof.
  intros G R GI j pc ra empty stk H L A regs mem md p n pl b K Hpre HGI HR Hro Hsp Hfrm HK.
  apply (H L A regs mem md p n pl b K Hpre HGI HR Hro Hsp Hfrm).
  intros l c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hpost & HGI').
  apply HK. exists fx', L', A', regs', mem', md'. split; [exact Hc|]. split; [exact Hf|].
  split; [exact (lib_post_g_of_gr0 B API G stk L A regs mem md p n b l L' A' regs' mem' md' Hpost) | exact HGI'].
Qed.

(* at the return 0 the two contracts are the same *)
Lemma lib_contract_cgr_0_iff : forall G R GI j pc ra empty stk,
  lib_contract_cgr (fun _ => 0) G R GI j pc ra empty stk <-> lib_contract_cg B API G R GI j pc ra empty stk.
Proof.
  intros. split; [apply lib_contract_cg_of_cgr0 | apply lib_contract_cgr_of_cg].
Qed.

End R.
