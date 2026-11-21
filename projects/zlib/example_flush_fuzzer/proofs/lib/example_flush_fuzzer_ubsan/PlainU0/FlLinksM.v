(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require PropExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import ExFlushIface FL4Inst FlLibStmtU.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0 Require Import FlLinks.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Deflate InflateState Inflate InflateSync HarnessKit HarnessFacts
  HarnessSmallStages HarnessSmallFacts Prog.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec Require Import FlushStages FlushLinks.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Strategy expand [DZC1 DSV1 DX1 DRC1 DOUT1 DNOUT1 DNIN1 DZR1 LC1 B3 LC1' DZC2 DSV2 DX2 DRC2 DOUT2 DNOUT2 DZR2 LC2 DTOT
                 IZC1 ICALL1 IS1 IR1 ICONS1 INOUT1 IZC2 ISYNC IS2 IR2 ICONS2 IZC3 ICALL3 IS3 IR3 FlLinks.DZS0 FlLinks.IZS0 WANS
                 L_DZC1 L_DSV1 L_DX1 L_DRC1 L_DOUT1 L_DNOUT1 L_DNIN1 L_DZR1 L_LC1 L_B3 L_LC1' L_DZC2 L_DSV2 L_DX2 L_DRC2 L_DOUT2 L_DNOUT2 L_DZR2 L_LC2 L_DTOT
                 L_IZC1 L_ICALL1 L_IS1 L_IR1 L_ICONS1 L_INOUT1 L_IZC2 L_ISYNC L_IS2 L_IR2 L_ICONS2 L_IZC3 L_ICALL3 L_IS3 L_IR3 FlushLinks.DZS0 FlushLinks.IZS0 WANS8].

Ltac unfold_all :=
  cbv beta zeta delta [DZC1 DSV1 DX1 DRC1 DOUT1 DNOUT1 DNIN1 DZR1 LC1 B3 LC1' DZC2 DSV2 DX2 DRC2 DOUT2 DNOUT2 DZR2 LC2 DTOT
                  IZC1 ICALL1 IS1 IR1 ICONS1 INOUT1 IZC2 ISYNC IS2 IR2 ICONS2 IZC3 ICALL3 IS3 IR3 FlLinks.DZS0 FlLinks.IZS0 WANS
                  L_DZC1 L_DSV1 L_DX1 L_DRC1 L_DOUT1 L_DNOUT1 L_DNIN1 L_DZR1 L_LC1 L_B3 L_LC1' L_DZC2 L_DSV2 L_DX2 L_DRC2 L_DOUT2 L_DNOUT2 L_DZR2 L_LC2 L_DTOT
                  L_IZC1 L_ICALL1 L_IS1 L_IR1 L_ICONS1 L_INOUT1 L_IZC2 L_ISYNC L_IS2 L_IR2 L_ICONS2 L_IZC3 L_ICALL3 L_IS3 L_IR3 FlushLinks.DZS0 FlushLinks.IZS0 WANS8].

Section M.
  Context {fx : PropExec.FPState}.
  Variable FL : @fl_lib fx.
  Variable d : list Z.
  Hypothesis Hn : 4 <= zlength d <= 2 ^ 20.
  Hypothesis Hb : Forall (fun b => 0 <= b < 256) d.
  Hypothesis Hds0 : fl_ds0 FL = ds0.
  Hypothesis His0 : fl_is0 FL = is0 KI.
  Hypothesis S_d1 : fl_dsafe FL (DSV1 FL d) 3.
  Hypothesis S_d2 : fl_dsafe FL (DSV2 FL d) 4.
  Hypothesis S_i1 : fl_isafe FL (fl_is0 FL) (IZC1 FL4 d) 0.
  Hypothesis S_sy : ZI.zr_rc (IR1 FL FL4 8%N d) = Z_OK -> fl_ssafe FL (IS1 FL FL4 8%N d) (IZC2 FL FL4 8%N d).
  Hypothesis S_i3 : ZI.zr_rc (IR1 FL FL4 8%N d) = Z_OK -> ZI.zr_rc (IR2 FL FL4 8%N d) = Z_OK -> fl_isafe FL (IS2 FL FL4 8%N d) (IZC3 FL FL4 8%N d) 4.

  Local Ltac eqM := unfold_all; rewrite ?Hds0, ?His0; reflexivity.
  Lemma DSV1_eqM : DSV1 FL d = L_DSV1 d. Proof. eqM. Qed.
  Lemma DSV2_eqM : DSV2 FL d = L_DSV2 d. Proof. eqM. Qed.
  Lemma DRC1_eqM : DRC1 FL d = L_DRC1 d. Proof. eqM. Qed.
  Lemma DX2_eqM : DX2 FL d = L_DX2 d. Proof. eqM. Qed.
  Lemma DTOT_eqM : DTOT FL d = L_DTOT d. Proof. eqM. Qed.
  Lemma LC2_eqM : LC2 FL d = L_LC2 d. Proof. eqM. Qed.
  Lemma IZC1_eqM : IZC1 FL4 d = L_IZC1 d. Proof. eqM. Qed.
  Lemma ICALL1_eqM : ICALL1 FL FL4 8%N d = L_ICALL1 d. Proof. eqM. Qed.
  Lemma IS1_eqM : IS1 FL FL4 8%N d = L_IS1 d. Proof. eqM. Qed.
  Lemma IR1_eqM : IR1 FL FL4 8%N d = L_IR1 d. Proof. eqM. Qed.
  Lemma IZC2_eqM : IZC2 FL FL4 8%N d = L_IZC2 d. Proof. eqM. Qed.
  Lemma IS2_eqM : IS2 FL FL4 8%N d = L_IS2 d. Proof. eqM. Qed.
  Lemma IR2_eqM : IR2 FL FL4 8%N d = L_IR2 d. Proof. eqM. Qed.
  Lemma IZC3_eqM : IZC3 FL FL4 8%N d = L_IZC3 d. Proof. eqM. Qed.
  Lemma ICALL3_eqM : ICALL3 FL FL4 8%N d = L_ICALL3 d. Proof. eqM. Qed.
  Lemma IR3_eqM : IR3 FL FL4 8%N d = L_IR3 d. Proof. eqM. Qed.

  Theorem fl_links_of : fl_links FL FL4 8%N d.
  Proof.
    constructor.
    - exact S_d1.
    - rewrite DRC1_eqM. apply (links_rc1 d); assumption.
    - exact S_d2.
    - rewrite DX2_eqM. apply (links_st2 d); assumption.
    - rewrite DX2_eqM. apply (links_busy d); assumption.
    - rewrite DTOT_eqM. apply (links_tot d); assumption.
    - rewrite LC2_eqM. apply (fl4_compr_links d); assumption.
    - exact S_i1.
    - rewrite ICALL1_eqM. apply (links_nw1 d); assumption.
    - rewrite IR1_eqM. apply (links_i1 d); assumption.
    - exact S_sy.
    - rewrite IR2_eqM. apply (links_is d); assumption.
    - exact S_i3.
    - rewrite ICALL3_eqM, IR3_eqM. apply (links_i2 d); assumption.
    - rewrite ICALL3_eqM, IR3_eqM. apply (links_i2b d); assumption.
  Qed.

  Lemma safe_terms :
    DSV1 FL d = fl_ds1 d /\ DSV2 FL d = fl_ds2 d
    /\ IZC1 FL4 d = L_IZC1 d /\ IS1 FL FL4 8%N d = L_IS1 d /\ IZC2 FL FL4 8%N d = L_IZC2 d /\ IS2 FL FL4 8%N d = L_IS2 d /\ IZC3 FL FL4 8%N d = L_IZC3 d.
  Proof.
    split; [rewrite DSV1_eqM; apply (L_DSV1_eq d); assumption|]. split; [rewrite DSV2_eqM; apply (L_DSV2_eq d); assumption|].
    split; [exact IZC1_eqM|]. split; [exact IS1_eqM|]. split; [exact IZC2_eqM|]. split; [exact IS2_eqM | exact IZC3_eqM].
  Qed.
End M.
