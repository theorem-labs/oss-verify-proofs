(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHex LbB_PmLeaf.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma w_mul_litA : forall a b, mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
  intros a b. apply bv_eq. cbn [mul_div].
  rewrite bv_mul_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Zmult_mod. reflexivity.
Qed.

Lemma ev_idx4 : forall E (r n : N) (x y : Z), edenot E (EVar r) = Z_to_bv 64 x -> edenot E (EVar n) = Z_to_bv 64 y ->
  0 <= x -> 0 <= y -> y + 4 * x < 2 ^ 64 ->
  edenot E (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar r)) (EVar n)) = Z_to_bv 64 (y + 4 * x).
Proof.
  intros E r n x y Hx Hy H0 H1 H2. cbn [edenot]. change (ev E r) with (edenot E (EVar r)). change (ev E n) with (edenot E (EVar n)).
  rewrite Hx, Hy. rewrite w_mul_litA. cbn [alu64 alu]. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small (4 * x) (2 ^ 64)) by lia. rewrite (Z.mod_small y (2 ^ 64)) by lia.
  rewrite (Z.mod_small (4 * x + y) (2 ^ 64)) by lia. rewrite (Z.mod_small (y + 4 * x) (2 ^ 64)) by lia. lia.
Qed.

Section WordsIdx.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.

  Lemma pmk_sh_wordsE : forall w s LB LBs m mo c ins tbl ftbl TB spal E e i,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> wa_words w <> 0 ->
    edenot E e = Z_to_bv 64 (wa_words w + 4 * i) -> 0 <= i -> 4 * i + 4 <= 8 * ((4 * wa_n w) / 8) ->
    kentry_ok ASEGS E m (KWord (SA (EAlu ALU_SRL e (ELit 3)) SHBASE) 1 (ELit 0)).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E e i OK X Hw He Hi Hg.
    destruct (wk_words H w OK) as [[E0 _]|(pw & k & Hin & Rg & W0 & W16 & Whi & Wdef & Wsh)]; [contradiction|].
    pose proof (wk_n H w OK) as N1.
    assert (D8 : 8 * ((4 * wa_n w) / 8) <= 4 * wa_n w) by (apply Z.mul_div_le; lia).
    apply (kshadow0 E m e (wa_words w + 4 * i)); [exact He | lia |].
    exact (pmx_words_sh0 H HH LINV w s LB LBs m mo c ins tbl ftbl TB spal (4 * i) OK X Hw ltac:(lia)).
  Qed.

  Lemma pmk_sh_wordsE_part : forall w s LB LBs m mo c ins tbl ftbl TB spal E e i,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> wa_words w <> 0 ->
    edenot E e = Z_to_bv 64 (wa_words w + 4 * i) -> 4 * i = 8 * ((4 * wa_n w) / 8) -> (4 * wa_n w) mod 8 = 4 ->
    kentry_ok ASEGS E m (KWord (SA (EAlu ALU_SRL e (ELit 3)) SHBASE) 1 (ELit 4)).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E e i OK X Hw He Hj Hr.
    destruct (wk_words H w OK) as [[E0 _]|(pw & k & Hin & Rg & W0 & W16 & Whi & Wdef & Wsh)]; [contradiction|].
    pose proof (wk_n H w OK) as N1.
    assert (Hk : 0 < k) by (assert (0 < 4 * wa_n w) by (Z.div_mod_to_equations; lia); lia).
    assert (Hl : Z.of_nat (length (LbB_PrsStmt.cc_gen k (4 * wa_n w))) = nsh k).
    { unfold LbB_PrsStmt.cc_gen, poison_bytes. rewrite length_app, repeat_length, Nat2Z.inj_add, shadow_of_length by lia.
      assert (nsh (4 * wa_n w) <= nsh k) by (unfold nsh; apply Z.div_le_mono; lia). lia. }
    pose proof (pmx_words_sh H HH LINV w s LB LBs m mo c ins tbl ftbl TB spal pw k _ OK X Hin Hk Hl Wsh) as SH.
    assert (D8 : 8 * ((4 * wa_n w) / 8) + 4 = 4 * wa_n w) by (Z.div_mod_to_equations; lia).
    assert (Hx : wa_words w <= wa_words w + 4 * i < wa_words w + 8 * Z.of_nat (length (LbB_PrsStmt.cc_gen k (4 * wa_n w)))).
    { rewrite Hl. unfold nsh. assert (0 <= (4 * wa_n w) / 8) by (apply Z.div_pos; lia). split; [lia|].
      assert (8 * ((4 * wa_n w) / 8) + 8 <= 8 * ((k + 7) / 8)) by (Z.div_mod_to_equations; lia). lia. }
    destruct (shk_of_SHAD m _ _ _ SH Hx) as (b & Hb & K).
    replace (wa_words w + 4 * i - wa_words w) with (4 * i) in Hb by lia.
    assert (Ej : Z.to_nat ((4 * i) / 8) = Z.to_nat ((4 * wa_n w) / 8)) by (rewrite Hj, Z.mul_comm, Z.div_mul by lia; reflexivity).
    rewrite Ej in Hb. rewrite (cc_gen_nth_part k (4 * wa_n w) ltac:(lia) ltac:(lia)) in Hb. injection Hb as <-.
    rewrite Hr in K. change (bv_unsigned (b8 4)) with 4 in K.
    apply (kshadow E m e (wa_words w + 4 * i) 4 (ELit 4)); [exact He | lia | lia | reflexivity | exact K].
  Qed.

  Lemma words_rd4 : forall w s LB LBs m mo c ins tbl ftbl TB spal i,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> wa_words w <> 0 -> 0 <= i < wa_n w ->
    exists bs, PropExec.rdn asegs m (Z_to_bv 64 (wa_words w + 4 * i)) 4 = Some bs /\ length bs = 4%nat.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal i OK X Hw Hi.
    pose proof (xa_wbuf _ _ _ _ _ _ _ _ _ _ _ _ _ _ X Hw) as WB.
    assert (WR : 0 <= wa_words w /\ wa_words w + 4 * wa_n w <= 2 ^ 47).
    { destruct (wk_words H w OK) as [[E0 _]|(pw & k0 & _ & Rg & W0 & _ & Whi & _ & _)]; [contradiction | lia]. }
    apply rdn4_of_mdef; [| lia | lia].
    intros j Hj. replace (wa_words w + 4 * i + j) with (wa_words w + (4 * i + j)) by lia. apply WB. lia.
  Qed.
End WordsIdx.
