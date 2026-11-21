(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.World Require Import Tgt_example_flush_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u DS6u Callee6u CalleeKits6u Memset6u_run TreesRod6u TreesApi6u TrApi6u DeflBlkApi6u
  FillWin6uA DeflSlow6u_9 TrSmall6u TrStored6u TFB6uSafe Defl6uApi Defl6u_5.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout ZSLayout RomRead TreesRod FillWinMem TreeMem DeflM.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees TreesTab TreeModel SendModel DeflateLz DeflateBlk Deflate LmatchModel FillWinModel DeflFastModel DeflSlowModel
  DeflateInvHash DeflateInvKeep OverlayFBS DeflRoom RefFlushBlk11 RefFlushPend1 RefDeflFastOk RefDeflSlowOk
  RefDeflateRel RefDeflateEnd1 RefDeflateHdrKit RefDeflateHdr1 RefDeflateHdr2 RefDeflateHdr3 RefDeflateHdr4 RefDeflateHdr5 RefDeflateTrl1 RefDeflatePost
  DeflateInv DeflInvTally DeflInvBits DeflInvTfb DeflInvLm DeflInvStep DeflInvFbo DeflInvFw DeflInvFast DeflInvSlow DeflInvSlow2 DeflInvCore DeflInvMain DeflInvWk FB6
  BoundArith HarnessKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import DeflSlow6_1 DeflSlow6_M DeflSlow6_Bridge Defl6_M.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Definition SSAFE6u (ds : deflate_state) (f : Z) : Prop := DWF ds /\ slow_safe6u FB6 ds f.
Definition DSAFE6u (ds : deflate_state) (f : Z) : Prop := DWF ds /\ dsafe6u SSAFE6u ds f.


Section TRIPU.
  Variables (ws hs PBL ILEN OCAP tot0 : Z).
  Hypothesis HPBL : 2048 <= PBL.
  Variable flush : Z.
  Hypothesis Hflush : 0 <= flush <= 5.

  Let DRUN rm hb fz := drunR rm hb fz ws hs PBL ILEN OCAP tot0.

  Lemma BSI_of_drun : forall rm hb fz s, 0 <= rm -> DRUN rm hb fz s -> BSI s.
  Proof.
    intros rm hb fz s Hrm D. pose proof D as [P _ _].
    pose proof (drun_span _ _ _ _ _ _ _ _ _ s Hrm P) as (SP & STR & _).
    unfold BSI. clear -SP STR. lia.
  Qed.

  Lemma sloop_oku_of : forall n s, DRUN 3 0 true s -> 4 <= ds_level s -> lz_strat s -> sloop_oku n s flush.
  Proof.
    induction n as [|n IH]; intros s D Hlv Hst; [exact Logic.I|].
    rewrite sloop_oku_S. split; [intros _; exact (BSI_of_drun 3 0 true s ltac:(lia) D)|].
    rewrite <- st_sbody_eq.
    destruct (strip_run ws hs PBL ILEN OCAP tot0 tfb_safe_holds tfb_room_holds HPBL flush s D Hlv Hst) as [_ PQ].
    destruct (deflate_slow_body s flush) as [s' o]. cbn [fst snd] in PQ |- *. unfold DeflInvFast.LZPOST in PQ.
    destruct PQ as [[EL ES] PQ]. destruct o; [| exact Logic.I | exact Logic.I].
    destruct PQ as [D' M']. apply IH; [exact D' | rewrite EL; exact Hlv | unfold lz_strat; rewrite ES; exact Hst].
  Qed.

  Theorem slow_safe6u_of_drun : forall s, DRUN 3 0 true s -> 4 <= ds_level s -> lz_strat s -> ds_wrap s = 1 ->
    ds_w_size s = ws -> ds_hash_size s = hs ->
    slow_safe6u FB6 s flush.
  Proof.
    intros s D Hlv Hst Hw Ews Ehs. unfold slow_safe6u.
    split; [exact (slow_safe6_of_drun ws hs PBL ILEN OCAP tot0 HPBL flush Hflush s D Hlv Hst Hw Ews Ehs)|].
    split; [exact (sloop_oku_of (lz_fuel s) s D Hlv Hst)|].
    pose proof D as [[C I CL _ _ _ _ _ _ _] _ _].
    assert (HM : DeflInvFast.lzm s < Z.of_nat (lz_fuel s)).
    { unfold lz_fuel, DeflInvFast.lzm. pose proof (di_look _ _ _ _ I). pose proof (dc_ai _ _ _ _ CL). rewrite Z2Nat.id by lia. lia. }
    destruct (sloop_run ws hs PBL ILEN OCAP tot0 tfb_safe_holds tfb_room_holds HPBL flush (lz_fuel s) s D Hlv Hst HM) as [_ LP].
    destruct (deflate_slow_loop (lz_fuel s) s flush) as [s1 [bs|]]; cbn [fst snd]; [exact Logic.I|].
    destruct LP as (EL & ES & D1 & L1 & NF).
    pose proof (BSI_of_drun 3 0 true s1 ltac:(lia) D1) as B. unfold BSI in B.
    pose proof D1 as [P1 _ _]. pose proof (drun_span 3 0 true _ _ _ _ _ _ s1 ltac:(lia) P1) as (SP & STR & _).
    clear -B SP STR. lia.
  Qed.
End TRIPU.


Theorem deflate_run6u_U6 : deflate_run6u ROM6u DSAFE6u.
Proof.
  pose proof (deflate_run6u_ok ROM6u SSAFE6u memcpy_run6u_ok tr_flush_bits_run6u_ok adler32_null_run6u_ok
                (deflate_slow_run6u_ok ROM6u FB6 memcpy_run6u_ok memset_run6u_ok adler32_run6u_ok tr_flush_bits_run6u_ok tr_flush_block_run6u_FB6 rom_local6u_ok)
                rom_local6u_ok memset_run6u_ok tr_stored_block_run6u_ok) as H.
  exact H.
Qed.
End FXG.
