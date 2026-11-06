(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec StepTac DriverCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxSubst FxStep FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PDrvData PDrvCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition KEEPALL : list positive := [2;3;4;5;6;7;8;9;10;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31;32]%positive.

Lemma keepall_ne : forall r : reg, existsb (Pos.eqb (rkey r)) KEEPALL = true -> r <> 10%bv.
Proof. intros r H Hr. subst r. vm_compute in H. discriminate H. Qed.

Theorem fx_sys_ret : forall E L ms model (v : word) (res : option lin) T,
  sden PSEGS E L ms -> havoc_ok L [] res = true ->
  (forall l, res = Some l -> lden E l = v) -> 0 <= s_pc L -> s_pc L + 4 < 2 ^ 64 ->
  (forall E' ms', agree (s_next L) E E' -> sden PSEGS E' (havoc_call L (s_pc L + 4) KEEPALL [] res) ms' ->
      ms_mem ms' = ms_mem ms -> ms_rom ms' = ms_rom ms -> getr (ms_regs ms') 10 = v ->
      realizes PSEGS (mkCfg ms' model) T) ->
  realizes PSEGS (mkCfg (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (regupd (ms_regs ms) 10 v)
                           (v_addi (Z_to_bv 64 (s_pc L)) 4) (ms_mem ms) (ms_rom ms)) model) T.
Proof.
  intros E L ms model v res T Hd Hok Hres Hp1 Hp2 Hk.
  set (ms' := @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (regupd (ms_regs ms) 10 v) (v_addi (Z_to_bv 64 (s_pc L)) 4) (ms_mem ms) (ms_rom ms)).
  destruct (havoc_call_sound PSEGS E L ms ms' (s_pc L + 4) KEEPALL [] res Hok Hd) as (E' & Ha & Hd').
  - unfold ms', mkst, v_addi. cbn [ms_pc_val]. rewrite u_small64 by (unfold two64; lia). reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & _ & _ & _ & Hf). exact Hf.
  - intros r Hr _. unfold ms', mkst; cbn [ms_regs]. apply getr_other. exact (keepall_ne r Hr).
  - intros l Hl. unfold ms', mkst; cbn [ms_regs]. replace (Z_to_bv 5 10) with (10%bv : reg) by (apply bv_eq; reflexivity).
    rewrite getr_same by (intros Hc; discriminate Hc). symmetry. exact (Hres l Hl).
  - intros i R x _ _ _. reflexivity.
  - intros i R x _ _ Hx. exact Hx.
  - apply (Hk E' ms' Ha Hd' eq_refl eq_refl). unfold ms', mkst; cbn [ms_regs]. apply getr_same. intros Hc; discriminate Hc.
Qed.
