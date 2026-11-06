(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface F_memchr ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState
     ECH_C1_stmt ECH_C5_stmt ECH_C12_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog StrFun.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Lemma vsn_spec : vsn_stmt.
  Proof.
    unfold vsn_stmt. intros until rest. intros A0 A1 NPOS BS NONUL L1 NLO LEN LLO LNA ST CEIL LO MI RAE. subst a0 a1.
    unfold P_validate_string_name, VSN_STACK, FR_validate_string_name, zlength in *.
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. cbn [length] in BB.
    pose proof (munch_refl [(lo, bv_unsigned sp); (lenp, lenp + 8)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 32%nat ST.
    do 5 st1. step. step. step.
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    st1. unfold wz. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step.
    (* [comment removed for export] *)
    destruct (nth_error ns (Z.to_nat (Z.of_nat (length ns) - 1))) as [b|] eqn:NTH; [| apply nth_error_None in NTH; lia].
    assert (NTH' : nth_error (ns ++ Z_to_bv 8 0 :: rest) (Z.to_nat (Z.of_nat (length ns) - 1)) = Some b) by (rewrite nth_error_app1 by lia; exact NTH).
    assert (BNZ : bv_unsigned b <> 0).
    { intros E. apply NONUL. replace (Z_to_bv 8 0) with b; [eapply nth_error_In; exact NTH|]. apply bv_eq. rewrite E. reflexivity. }
    pose proof (byte_range b) as BR.
    pose proof (u8ro_read rsegs _ name (ns ++ Z_to_bv 8 0 :: rest) (Z.of_nat (length ns) - 1) b _ BS NTH' ltac:(lia) eq_refl) as RD.
    replace (name + (Z.of_nat (length ns) - 1)) with (name + Z.of_nat (length ns) + -1) in RD by lia.
    step. change (zxb b) with (Z_to_bv 64 (bv_unsigned b)).
    zstep. replace (bv_unsigned b <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
    cbn [Z.b2z]. zstep. replace (Z.of_nat (length ns) + - 0) with (Z.of_nat (length ns)) by lia.
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. step.
    eapply evt_cut.
    { eapply memchr_spec with (buf := ns ++ Z_to_bv 8 0 :: rest); rewrite ?unsigned_lit by lia.
      - exact BS.
      - unfold memchr_ok. change (0 mod 256) with 0. rewrite (find_byte_cstr_short name) by (first [exact NONUL | lia]). rewrite length_app. cbn [length]. lia.
      - exact MI. }
    unfold memchr_post. land MU WM.
    rewrite !unsigned_lit by lia. change (0 mod 256) with 0. rewrite memchr_res_cstr by exact NONUL. rewrite Z.ltb_irrefl. cbv beta iota.
    (* [comment removed for export] *)
    step. if_true. st1. step. step.
    do 4 st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.
End S.
