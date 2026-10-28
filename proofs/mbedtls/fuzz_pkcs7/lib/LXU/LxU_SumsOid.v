(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA AEvt HeapIface PropExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Export LxSum LxSoundSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxRun LxDenot LxSoundRun LxTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Lemma bytes_at_sliceK : forall (mX : mem) (B : Z) (bsx : list byte) (P0 Lz : Z),
  bytes_at usegs mX B bsx -> B <= P0 -> 0 <= Lz -> P0 + Lz <= B + Z.of_nat (length bsx) ->
  bytes_at usegs mX P0 (firstn (Z.to_nat Lz) (skipn (Z.to_nat (P0 - B)) bsx)) /\
  Z.of_nat (length (firstn (Z.to_nat Lz) (skipn (Z.to_nat (P0 - B)) bsx))) = Lz.
Proof.
  intros mX B bsx P0 Lz (HB0 & HB1 & HB) H1 H2 H3.
  assert (HL : length (firstn (Z.to_nat Lz) (skipn (Z.to_nat (P0 - B)) bsx)) = Z.to_nat Lz).
  { rewrite firstn_length, skipn_length. lia. }
  split; [| rewrite HL; lia]. split; [lia|]. split; [rewrite HL; lia|].
  intros i Hi. rewrite HL in Hi. rewrite nth_error_firstn. destruct (Nat.ltb_spec i (Z.to_nat Lz)); [| lia].
  rewrite nth_error_skipn. rewrite <- (HB (Z.to_nat (P0 - B) + i)%nat) by lia. f_equal. f_equal. lia.
Qed.
Definition q (i : positive) : expr := EZv i.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_LxP_SumsOid () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LX.LxSum.SUM"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Numbers.BinNums.positive"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.mfact"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.pfact"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FEq"; "q"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLe"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EAdd"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLt"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.ELit"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.expr"].


(* [comment removed for export] *)
Definition SUM_bcmpCP (pc : Z) : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsOid ()) "(0.O1.$1.#6.#5.#2.(2.(3.$4.$5.)(6.$4.$5.+:.^1.)(2.(3.$4.$5.)(6.$4.$5.+;.^2.)(2.(3.$4.$5.)(6.$4.$5.+<.^3.)(7.(3.$4.$5.)))))(8.$5.)(7.$9.)(8.(3.$5.$5.))(2.(3.(3.$5.$5.)$5.)(6.(3.$5.$5.)$5.(6.$5.$5.^1.^4.)^1.)(2.(3.(3.$5.$5.)$5.)(6.(3.$5.$5.)$5.(6.$5.$5.^5.^6.)^2.)(7.(3.(3.$5.$5.)$5.))))(7.$9.)(2.$:.(;.(<.^4.)(<.^3.))(2.$:.(=.(<.^5.)(<.^2.))(2.$:.(=.(>.(<.^2.)(<.^3.))(>.(<.^5.)(<.^6.)))(2.$:.(?.(10.=)(<.^3.))(2.$:.(=.(10.=)(<.^1.))(2.$:.(?.(>.(<.^1.)(<.^3.))(10.(11.+2.+40.)))(2.$:.(?.(10.=)(<.^5.))(2.$:.(=.(>.(<.^5.)(<.^6.))(10.(11.+2.+40.)))(7.$:.)))))))))(7.(3.$12.$12.))(2.(3.$4.$5.)(6.$4.$5.+:.^7.)(2.(3.$4.$5.)(6.$4.$5.+;.^8.)(2.(3.$4.$5.)(6.$4.$5.+<.^9.)(2.(3.$4.$5.)(6.$4.$5.+=.^:.)(2.(3.$4.$5.)(6.$4.$5.+>.^;.)(7.(3.$4.$5.)))))))(7.$9.)(2.$:.(=.(10.-??.)(<.^7.))(2.$:.(=.(<.^7.)(10.+??.))(7.$:.))))")
(* [comment removed for export] *).

Lemma sum_bcmpCP_valid : forall pc AL, memcmp_stmt usegs pc -> summary_valid usegs AL (SUM_bcmpCP pc).
Proof.
  intros pc AL BC. unfold SUM_bcmpCP, q. lx_sum_unfold.
  intros P1 P2 NN L1 BUF BLEN xs bs CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI R10 R11 R12 _ [HB1 HL1] [HB2 HL2] E1 Q1 Q2 Q0 Q3 A1 A3 A4.
  apply (evt_evtA_all usegs AL CS _ _ ALLCS).
  destruct (bytes_at_sliceK m BUF bs P2 NN HB2 ltac:(lia) ltac:(lia) ltac:(lia)) as [PBY PLEN].
  pose proof BC as SP. unfold memcmp_stmt in SP.
  eapply evt_cut.
  { eapply (SP x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m xs _);
      subst x10 x11 x12; rewrite ?lx_uw64 by (unfold two64; lia); first [eassumption | lia]. }
  clear SP. intros ms' POST. unfold memcmp_post in POST.
  destruct POST as (a0' & a1' & a2' & a3' & a4' & r & -> & -> & Hr & _).
  apply evt_done. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
  lx_sum_post.
Qed.

Lemma sum_bcmpCP_ok : forall pc AL, memcmp_stmt usegs pc -> summary_ok usegs AL (SUM_bcmpCP pc).
Proof. intros. apply apply_summary_sound. apply sum_bcmpCP_valid. assumption. Qed.
