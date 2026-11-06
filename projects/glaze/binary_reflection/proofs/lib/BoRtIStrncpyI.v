(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.ZStores.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIStrncpy. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIStrncpy.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPGen2.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition both_istrncpy_entry : word := 0x80dd4.
Definition both_sealed_src : Z := 0x11aae.

Lemma both_istrncpy_code :
  code_at AsanUbsan.M.loaded_segments both_istrncpy_entry 0 istrncpy_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold istrncpy_words in G in change_no_check G' end). code_at_vm. Qed.

(* [comment removed for export] *)
Lemma both_sealed_src_img : forall mem,
  (forall i, (both_sealed_src <= i < both_sealed_src + 9)%Z -> mem (Z_to_bv 64 i) = None) ->
  rdn AsanUbsan.M.loaded_segments mem (Z_to_bv 64 both_sealed_src) 8 = Some sealed8
  /\ rdn AsanUbsan.M.loaded_segments mem (at_ (Z_to_bv 64 both_sealed_src) 8) 1 = Some [Z_to_bv 8 0].
Proof using.
  intros mem Hnone. unfold both_sealed_src in *. split.
  - rewrite (rdn_ext _ 8 mem (fun _ => None)); [vm_compute; reflexivity | u_norm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
    intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hnone. revert Hx. u_norm. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). lia.
  - rewrite (rdn_ext _ 1 mem (fun _ => None)); [vm_compute; reflexivity | rewrite at_u by (u_norm; lia); u_norm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
    intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hnone. revert Hx. rewrite at_u by (u_norm; lia). u_norm. (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end). lia.
Qed.

Theorem both_istrncpy_sealed : forall mem0 (dst : word) rom regs (ret : word),
  (forall i, (both_sealed_src <= i < both_sealed_src + 9)%Z -> mem0 (Z_to_bv 64 i) = None) ->
  store_ok AsanUbsan.M.loaded_segments mem0 dst 4095%nat = true ->
  (bv_unsigned dst + 4095 < 2 ^ 64)%Z ->
  (bv_unsigned dst + 4095 <= both_sealed_src \/ both_sealed_src + 9 <= bv_unsigned dst)%Z ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = dst -> getr regs 11 = Z_to_bv 64 both_sealed_src -> getr regs 12 = Z_to_bv 64 4095 ->
  exists regs',
    msteps AsanUbsan.M.loaded_segments
           (mkst regs both_istrncpy_entry mem0 rom) (mkst regs' ret (wbytes mem0 dst strncpy_sealed_bytes) rom)
    /\ regs_agree (fun r => In r istrncpy_clob) regs regs'.
Proof using.
  intros mem0 dst rom regs ret Hnone Hok Hnw Hdisj Hret H1 H10 H11 H12.
  destruct (both_sealed_src_img mem0 Hnone) as [Hs Hn].
  rewrite <- (at_0 both_istrncpy_entry).
  apply (istrncpy_run _ _ mem0 dst (Z_to_bv 64 both_sealed_src) rom both_istrncpy_code Hs Hn); try assumption;
    unfold both_sealed_src in *; u_norm; lia.
Qed.

End FPGen2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
