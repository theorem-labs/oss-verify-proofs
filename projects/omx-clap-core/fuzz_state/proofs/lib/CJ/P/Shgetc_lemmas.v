(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Lib Require Import SFModel Arr.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec Require Import Prelim SoftFloat StrFun FloatScan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P Require Exit_tac.
Import OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P.Exit_tac.STRW_tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition zbytes (l : list Z) : list byte := map (Z_to_bv 8) l.

(* [comment removed for export] *)
Definition sh_ok (T : Z) (txt : list Z) (f : shfile) : Prop :=
  sh_buf f = txt /\ zlength txt <= 2^40 /\ 0 <= sh_rpos f <= 2^40 /\ 0 <= sh_cnt0 f <= 2^40
  /\ 0 <= sh_n f <= zlength txt /\ (sh_stdio f = true -> sh_rpos f <= sh_n f).

Lemma sx32_small : forall e, -2^31 <= e < 2^31 -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, bv_swrap32_eq.
  change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

Lemma b2z_range : forall b, 0 <= Z.b2z b <= 1.
Proof. intros [|]; cbn; lia. Qed.

Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma znth_In' : forall l i, 0 <= i < zlength l -> In (znth l i) l.
Proof.
  intros l i Hi. unfold znth, zlength in *. destruct (Z.ltb_spec0 i 0); [lia|].
  apply nth_In. lia.
Qed.
Lemma zbytes_nth : forall txt i, 0 <= i < zlength txt ->
  nth_error (zbytes txt) (Z.to_nat i) = Some (Z_to_bv 8 (znth txt i)).
Proof.
  intros txt i Hi. unfold zbytes, zlength, znth in *. rewrite nth_error_map.
  destruct (Z.ltb_spec0 i 0); [lia|].
  destruct (nth_error txt (Z.to_nat i)) as [c|] eqn:E.
  - cbn. f_equal. f_equal. symmetry. apply nth_error_nth. exact E.
  - apply nth_error_None in E. lia.
Qed.