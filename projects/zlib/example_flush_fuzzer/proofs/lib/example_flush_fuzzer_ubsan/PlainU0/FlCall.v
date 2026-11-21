(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require PropExec FlLibStmtU.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Lib Require Import Tac Image ZBridge Walk Arr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CkP Require Import RegsFull BridgeKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0 Require Import PImg FlKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0 Require Import RunDraw.
Require OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ZlibStmtBase OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require ZIface DeflateState Deflate InflateState Inflate InflateRc InflateSync HarnessKit HarnessFacts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Module OL := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.FlLibStmtU.
(* kitfix4 alias stage: Module OZ := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ZlibStmtBase expanded *)
(* kitfix4 alias stage: Module OX := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface expanded *)
Module ZI := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface.
(* kitfix4 alias stage: Module ZD := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Deflate expanded *)
Module ZDS := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.DeflateState.
Module ZIS := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState.
(* kitfix4 alias stage: Module ZSY := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateSync expanded *)
Module ZHF := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.HarnessFacts.
Module ZPG := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog.
(* kitfix4 alias stage: Module ZRC := OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateRc expanded *)

Section GR.
Variables x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word.
Local Notation RR := (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
Lemma gr1 : OP.getr RR 1 = x1. Proof. reflexivity. Qed.    Lemma gr2 : OP.getr RR 2 = x2. Proof. reflexivity. Qed.
Lemma gr3 : OP.getr RR 3 = x3. Proof. reflexivity. Qed.    Lemma gr4 : OP.getr RR 4 = x4. Proof. reflexivity. Qed.
Lemma gr5 : OP.getr RR 5 = x5. Proof. reflexivity. Qed.    Lemma gr6 : OP.getr RR 6 = x6. Proof. reflexivity. Qed.
Lemma gr7 : OP.getr RR 7 = x7. Proof. reflexivity. Qed.    Lemma gr8 : OP.getr RR 8 = x8. Proof. reflexivity. Qed.
Lemma gr9 : OP.getr RR 9 = x9. Proof. reflexivity. Qed.    Lemma gr10 : OP.getr RR 10 = x10. Proof. reflexivity. Qed.
Lemma gr11 : OP.getr RR 11 = x11. Proof. reflexivity. Qed. Lemma gr12 : OP.getr RR 12 = x12. Proof. reflexivity. Qed.
Lemma gr13 : OP.getr RR 13 = x13. Proof. reflexivity. Qed. Lemma gr14 : OP.getr RR 14 = x14. Proof. reflexivity. Qed.
Lemma gr15 : OP.getr RR 15 = x15. Proof. reflexivity. Qed. Lemma gr16 : OP.getr RR 16 = x16. Proof. reflexivity. Qed.
Lemma gr17 : OP.getr RR 17 = x17. Proof. reflexivity. Qed. Lemma gr18 : OP.getr RR 18 = x18. Proof. reflexivity. Qed.
Lemma gr19 : OP.getr RR 19 = x19. Proof. reflexivity. Qed. Lemma gr20 : OP.getr RR 20 = x20. Proof. reflexivity. Qed.
Lemma gr21 : OP.getr RR 21 = x21. Proof. reflexivity. Qed. Lemma gr22 : OP.getr RR 22 = x22. Proof. reflexivity. Qed.
Lemma gr23 : OP.getr RR 23 = x23. Proof. reflexivity. Qed. Lemma gr24 : OP.getr RR 24 = x24. Proof. reflexivity. Qed.
Lemma gr25 : OP.getr RR 25 = x25. Proof. reflexivity. Qed. Lemma gr26 : OP.getr RR 26 = x26. Proof. reflexivity. Qed.
Lemma gr27 : OP.getr RR 27 = x27. Proof. reflexivity. Qed. Lemma gr28 : OP.getr RR 28 = x28. Proof. reflexivity. Qed.
Lemma gr29 : OP.getr RR 29 = x29. Proof. reflexivity. Qed. Lemma gr30 : OP.getr RR 30 = x30. Proof. reflexivity. Qed.
Lemma gr31 : OP.getr RR 31 = x31. Proof. reflexivity. Qed.
End GR.
Ltac grw H := rewrite ?gr1, ?gr2, ?gr3, ?gr4, ?gr5, ?gr6, ?gr7, ?gr8, ?gr9, ?gr10, ?gr11, ?gr12, ?gr13, ?gr14, ?gr15, ?gr16, ?gr17, ?gr18, ?gr19, ?gr20,
  ?gr21, ?gr22, ?gr23, ?gr24, ?gr25, ?gr26, ?gr27, ?gr28, ?gr29, ?gr30, ?gr31 in H.

Lemma rkeep_FL_KEEP : forall (R R' : bvmap 5 word), OL.rkeep R R' OL.FL_KEEP ->
  OP.getr R' 3 = OP.getr R 3 /\ OP.getr R' 4 = OP.getr R 4 /\ OP.getr R' 8 = OP.getr R 8 /\ OP.getr R' 9 = OP.getr R 9 /\
  OP.getr R' 18 = OP.getr R 18 /\ OP.getr R' 19 = OP.getr R 19 /\ OP.getr R' 20 = OP.getr R 20 /\ OP.getr R' 21 = OP.getr R 21 /\
  OP.getr R' 22 = OP.getr R 22 /\ OP.getr R' 23 = OP.getr R 23 /\ OP.getr R' 24 = OP.getr R 24 /\ OP.getr R' 25 = OP.getr R 25 /\
  OP.getr R' 26 = OP.getr R 26 /\ OP.getr R' 27 = OP.getr R 27.
Proof. intros R R' K. unfold OL.rkeep, OL.FL_KEEP in K. repeat split; apply K; cbn [In]; auto 16. Qed.
Lemma rkeep_DI : forall (R R' : bvmap 5 word), OL.rkeep R R' [3; 4; 24; 25; 26; 27]%bv ->
  OP.getr R' 3 = OP.getr R 3 /\ OP.getr R' 4 = OP.getr R 4 /\
  OP.getr R' 24 = OP.getr R 24 /\ OP.getr R' 25 = OP.getr R 25 /\ OP.getr R' 26 = OP.getr R 26 /\ OP.getr R' 27 = OP.getr R 27.
Proof. intros R R' K. unfold OL.rkeep in K. repeat split; apply K; cbn [In]; auto 10. Qed.
(* 1.4 UBSan: deflateInit2_ saves and restores s7 (x23), so fl_di keeps only 3, 4, 24..27 *)
Lemma rkeep_DIu : forall (R R' : bvmap 5 word), OL.rkeep R R' [3; 4; 24; 25; 26; 27]%bv ->
  OP.getr R' 3 = OP.getr R 3 /\ OP.getr R' 4 = OP.getr R 4 /\
  OP.getr R' 24 = OP.getr R 24 /\ OP.getr R' 25 = OP.getr R 25 /\ OP.getr R' 26 = OP.getr R 26 /\ OP.getr R' 27 = OP.getr R 27.
Proof. intros R R' K. unfold OL.rkeep in K. repeat split; apply K; cbn [In]; auto 10. Qed.
Lemma rkeep_II : forall (R R' : bvmap 5 word), OL.rkeep R R' [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  OP.getr R' 3 = OP.getr R 3 /\ OP.getr R' 4 = OP.getr R 4 /\ OP.getr R' 19 = OP.getr R 19 /\
  OP.getr R' 20 = OP.getr R 20 /\ OP.getr R' 21 = OP.getr R 21 /\ OP.getr R' 22 = OP.getr R 22 /\ OP.getr R' 23 = OP.getr R 23 /\
  OP.getr R' 24 = OP.getr R 24 /\ OP.getr R' 25 = OP.getr R 25 /\ OP.getr R' 26 = OP.getr R 26 /\ OP.getr R' 27 = OP.getr R 27.
Proof. intros R R' K. unfold OL.rkeep in K. repeat split; apply K; cbn [In]; auto 14. Qed.

Section CALL.
Context {rc : runConstT}.
Variable FLIB : forall fx : OP.FPState, @OL.fl_lib fx.
Variables (F : bvmap 5 word) (fc : bv 32).
Notation CT := (FLIB (OP.mkFP F fc)).

Lemma di_evt : forall (Q : machine_state -> Prop) (m : word -> option byte) (hh s wnd prv hd pb zc ra v16 v24 v32 : Z) (sv20 sv21 sv22 sv23 : word)
    (x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  let R0 := mkR x1 (Z_to_bv 64 (hh - 80)) x3 x4 x5 x6 x7 (Z_to_bv 64 (hh + 8)) (Z_to_bv 64 s) (Z_to_bv 64 pb) x11 x12 x13 x14 x15 x16 x17
                (Z_to_bv 64 (s + 5888)) (Z_to_bv 64 0) (Z_to_bv 64 6) (Z_to_bv 64 1) (Z_to_bv 64 8) x23 x24 x25 x26 x27 x28 x29 x30 x31 in
  hh mod 16 = 0 -> zc + 1024 <= hh -> hh + 120 <= 2^47 -> 0x5f000 <= zc ->
  OL.blocks_ok m zc (OL.dblocks (OL.DP (hh + 8) s wnd prv hd pb)) -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart (OL.dblocks (OL.DP (hh + 8) s wnd prv hd pb)) -> OL.img_clear m ->
  store_ok psegs m (Z_to_bv 64 (hh - 1024)) (Z.to_nat (1024 + 120)) = true ->
  OL.ra_ok ra -> 0 <= v16 < 2^63 -> 0 <= v24 < 2^63 -> 0 <= v32 < 2^63 ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m wnd 65536 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m prv 65536 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m hd 65536 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m pb 65536 ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m (s + 12) 36 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m (s + 52) 4 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m (s + 64) 16 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m (s + 92) 4 ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m (s + 104) 8 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m (s + 128) 4 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m (s + 148) 5748 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m (s + 5900) 52 ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m (s + 5960) 8 ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m s (hh + 8) -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 psegs m (s + 8) 42 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 psegs m (s + 48) 1 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (s + 56) 0 ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 psegs m (s + 80) 32768 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 psegs m (s + 84) 15 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 psegs m (s + 88) 32767 ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (s + 96) wnd -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (s + 112) prv -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (s + 120) hd ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 psegs m (s + 132) 32768 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 psegs m (s + 136) 15 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 psegs m (s + 140) 32767 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 psegs m (s + 144) 5 ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 psegs m (s + 5896) 16384 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (s + 5952) 0 ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (hh - 8) ra -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (hh - 16) v16 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (hh - 24) v24 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (hh - 32) v32 ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (hh - 40) OL.FL_DATALEN ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cellw psegs m (hh - 48) sv20 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cellw psegs m (hh - 56) sv21 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cellw psegs m (hh - 64) sv22 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cellw psegs m (hh - 72) sv23 ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (hh + 56) 0 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (hh + 64) s -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (hh + 72) OL.FL_ZCALLOC -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (hh + 80) OL.FL_ZCFREE ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (hh + 88) 0 ->
  (forall (m' : word -> option byte) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     OF.frame_mod m m' ((Z_to_bv 64 (hh - 1024), 1024) :: (Z_to_bv 64 (hh + 8), 112) ::
                        [(Z_to_bv 64 s, 5968); (Z_to_bv 64 wnd, 65536); (Z_to_bv 64 prv, 65536); (Z_to_bv 64 hd, 65536); (Z_to_bv 64 pb, 65536)]) ->
     OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (hh + 24) 0 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (hh + 48) 0 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (hh + 56) 0 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (hh + 64) s ->
     OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (hh + 72) OL.FL_ZCALLOC -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (hh + 80) OL.FL_ZCFREE -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (hh + 88) 0 ->
     OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 psegs m' (hh + 96) 2 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (hh + 104) 1 ->
     OL.fl_drep CT m' (OL.DP (hh + 8) s wnd prv hd pb) (OL.fl_ds0 CT) ->
     Q (MS (mkR y1 (Z_to_bv 64 hh) x3 x4 y5 y6 y7 (Z_to_bv 64 v16) (Z_to_bv 64 v24) (Z_to_bv 64 0) y11 y12 y13 y14 y15 y16 y17
                (Z_to_bv 64 v32) (Z_to_bv 64 OL.FL_DATALEN) sv20 sv21 sv22 sv23 x24 x25 x26 x27 y28 y29 y30 y31)
           F (Z_to_bv 64 ra) fc None m' (seg_rom psegs))) ->
  evt psegs Q (MS R0 F (Z_to_bv 64 OL.FL_A_DI) fc None m (seg_rom psegs)).
Proof.
  intros Q m hh s wnd prv hd pb zc ra v16 v24 v32 sv20 sv21 sv22 sv23 x1 x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27 x28 x29 x30 x31 R0.
  intros H16 HZC H47 HTOP BOK AP IC SOK RA V16 V24 V32 Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13
         C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 F1 F2 F3 F4 F5 F6 F7 F8 F9 S1 S2 S3 S4 S5 HK.
  pose proof (OL.fl_di CT R0 m (OL.DP (hh + 8) s wnd prv hd pb) zc ra v16 v24 v32 sv20 sv21 sv22 sv23 OL.FL_ZCALLOC OL.FL_ZCFREE) as X.
  cbn [OL.dp_strm OL.dp_s OL.dp_wnd OL.dp_prv OL.dp_hd OL.dp_pb] in X. replace (hh + 8 - 8) with hh in X by lia.
  specialize (X ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
                H16 HZC H47 HTOP BOK AP IC SOK RA V16 V24 V32 Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13
                C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 F1 F2 F3 F4 F5 F6 F7 F8 F9 S1 S2 S3 S4 S5 eq_refl eq_refl).
  destruct X as (R' & m' & RUN & FM & G10 & G2 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & GK & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & DR).
  eapply (evt_of_msteps_mkR psegs _ R0 F _ _ fc m m' (seg_rom psegs) R'); [apply rfull_mkR| exact RUN|].
  intros y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 ER'.
  subst R'. grw G10. grw G2. grw G8. grw G9. grw G18. grw G19. grw G20. grw G21. grw G22. grw G23.
  apply rkeep_DIu in GK. grw GK. destruct GK as (G3 & G4 & G24 & G25 & G26 & G27). subst R0. grw G3. grw G4. grw G24. grw G25. grw G26. grw G27.
  subst. apply (HK m' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31); assumption.
Qed.

Lemma dfl_evt : forall (Q : machine_state -> Prop) (m : word -> option byte) (strm s wnd prv hd pb sp ra inp outp zcl f : Z)
    (ds : ZDS.deflate_state) (zc : ZI.ZCall)
    (x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  let R0 := mkR (Z_to_bv 64 ra) (Z_to_bv 64 sp) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 strm) (Z_to_bv 64 f) x12 x13 x14 x15 x16 x17
                x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 in
  let q := OL.DP strm s wnd prv hd pb in
  let dsv := ZDS.set_strm ds (ZDS.cstrm_of_call zc) in
  let X := fst (OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Deflate.deflate_core dsv f) in let rcd := snd (OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Deflate.deflate_core dsv f) in
  let nout := Z.of_nat (length (ZDS.cs_out_rev (ZDS.ds_strm X))) in
  OL.ra_ok ra -> sp mod 16 = 0 -> zcl + 1024 <= sp -> sp <= 2^47 -> 0x5f000 <= zcl ->
  OL.blocks_ok m zcl (OL.dblocks q) -> OL.img_clear m ->
  0 < strm -> strm + 112 <= 2^63 -> strm mod 8 = 0 -> 0 < inp -> 0 < outp ->
  store_ok psegs m (Z_to_bv 64 (sp - 1024)) (Z.to_nat 1024) = true ->
  store_ok psegs m (Z_to_bv 64 strm) 112%nat = true ->
  store_ok psegs m (Z_to_bv 64 outp) (Z.to_nat (ZI.zc_avail_out zc)) = true ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart ((sp - 1024, 1024) :: (strm, 112) :: (outp, ZI.zc_avail_out zc) :: (inp, ZI.zlength (ZI.zc_input zc)) :: OL.dblocks q) ->
  (forall a n, In (a, n) ((sp - 1024, 1024) :: (strm, 112) :: (outp, ZI.zc_avail_out zc) :: OL.dblocks q) -> a + n <= 0x10000 \/ 0x5f000 <= a) ->
  inp + ZI.zlength (ZI.zc_input zc) < 2^63 -> outp + ZI.zc_avail_out zc < 2^63 ->
  OL.fl_drep CT m q ds -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.holds psegs m inp (ZI.zc_input zc) ->
  OL.zs_cells (OL.fl_msga CT) m strm inp (ZI.zlength (ZI.zc_input zc)) outp (ZI.zc_avail_out zc) (ZI.zc_strm zc) s OL.FL_ZCALLOC OL.FL_ZCFREE ->
  OL.fl_dsafe CT dsv f ->
  (forall (m' : word -> option byte) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     OF.frame_mod m m' ((Z_to_bv 64 (sp - 1024), 1024) :: (Z_to_bv 64 strm, 112) :: (Z_to_bv 64 outp, nout) :: OL.wz (OL.dblocks q)) ->
     0 <= rcd <= 1 -> 0 <= nout <= ZI.zc_avail_out zc -> 0 <= ZDS.cs_next_in (ZDS.ds_strm X) <= ZI.zlength (ZI.zc_input zc) ->
     OL.fl_drep CT m' q X ->
     OL.zs_cells (OL.fl_msga CT) m' strm (inp + ZDS.cs_next_in (ZDS.ds_strm X)) (ZI.zlength (ZI.zc_input zc) - ZDS.cs_next_in (ZDS.ds_strm X))
                 (outp + nout) (ZI.zc_avail_out zc - nout) (ZI.zr_strm (ZDS.zret_of_cs (ZDS.ds_strm X) rcd)) s OL.FL_ZCALLOC OL.FL_ZCFREE ->
     OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.holds psegs m' outp (ZDS.cs_output (ZDS.ds_strm X)) ->
     Q (MS (mkR y1 (Z_to_bv 64 sp) x3 x4 y5 y6 y7 x8 x9 (Z_to_bv 64 rcd) y11 y12 y13 y14 y15 y16 y17
                x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
           F (Z_to_bv 64 ra) fc None m' (seg_rom psegs))) ->
  evt psegs Q (MS R0 F (Z_to_bv 64 OL.FL_A_DEFLATE) fc None m (seg_rom psegs)).
Proof.
  intros Q m strm s wnd prv hd pb sp ra inp outp zcl f ds zc x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         R0 q dsv X rcd nout.
  intros RA SP16 HZC H47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 OUTP0 SOK1 SOK2 SOK3 AP IMG B1 B2 DR HLD ZS SAFE HK.
  pose proof (OL.fl_dfl CT R0 m q ds zc f sp ra inp outp zcl OL.FL_ZCALLOC OL.FL_ZCFREE) as Y.
  cbv zeta in Y. subst q. cbn [OL.dp_strm OL.dp_s OL.dp_wnd OL.dp_prv OL.dp_hd OL.dp_pb] in Y.
  specialize (Y ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) RA SP16 HZC H47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 OUTP0 SOK1 SOK2 SOK3 AP IMG B1 B2 DR HLD ZS eq_refl eq_refl SAFE).
  destruct Y as (R' & m' & RUN & FM & G10 & RC & G2 & GK & DR' & NO & NI & ZS' & HLD').
  eapply (evt_of_msteps_mkR psegs _ R0 F _ _ fc m m' (seg_rom psegs) R'); [apply rfull_mkR| exact RUN|].
  intros y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 ER'.
  subst R'. grw G10. grw G2.
  apply rkeep_FL_KEEP in GK. grw GK. destruct GK as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27). subst R0.
  grw G3. grw G4. grw G8. grw G9. grw G18. grw G19. grw G20. grw G21. grw G22. grw G23. grw G24. grw G25. grw G26. grw G27.
  subst. apply (HK m' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31); assumption.
Qed.

Lemma ii_evt : forall (Q : machine_state -> Prop) (m : word -> option byte) (strm p tt zc ra v16 v24 v32 ni ai : Z)
    (x1 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  let R0 := mkR x1 (Z_to_bv 64 (tt - 32)) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 7176) (Z_to_bv 64 p) x11 x12 x13 x14 x15 x16 x17
                (Z_to_bv 64 strm) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 in
  tt mod 16 = 0 -> zc + 1024 <= tt -> tt <= 2^47 -> 0x5f000 <= zc ->
  OL.blocks_ok m zc (OL.iblocks (OL.IP strm p 0)) -> OL.img_clear m -> 0 < strm -> strm mod 8 = 0 -> strm + 112 <= 2^47 ->
  store_ok psegs m (Z_to_bv 64 (tt - 1024)) (Z.to_nat 1024) = true -> store_ok psegs m (Z_to_bv 64 strm) 112%nat = true ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart [(tt - 1024, 1024); (strm, 112); (p, 7176)] -> (strm + 112 <= 0x10000 \/ 0x5f000 <= strm) ->
  OL.ra_ok ra -> 0 <= v16 < 2^63 -> 0 <= v24 < 2^63 -> 0 <= v32 < 2^63 ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m p 7176 ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (tt - 8) ra -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (tt - 16) v16 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (tt - 24) v24 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (tt - 32) v32 ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (strm + 48) 0 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (strm + 64) OL.FL_ZCALLOC -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (strm + 72) OL.FL_ZCFREE -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m (strm + 80) 0 ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m strm ni -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 psegs m (strm + 8) ai ->
  (forall (m' : word -> option byte) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     OF.frame_mod m m' [(Z_to_bv 64 (tt - 1024), 1024); (Z_to_bv 64 strm, 112); (Z_to_bv 64 p, 7176)] ->
     OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (strm + 16) 0 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (strm + 40) 0 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (strm + 48) 0 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (strm + 56) p ->
     OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (strm + 64) OL.FL_ZCALLOC -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (strm + 72) OL.FL_ZCFREE -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (strm + 80) 0 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' (strm + 96) 1 ->
     OL.fl_irep CT m' (OL.IP strm p 0) (OL.fl_is0 CT) ->
     OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell8 psegs m' strm ni -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.cell4 psegs m' (strm + 8) ai ->
     Q (MS (mkR y1 (Z_to_bv 64 tt) x3 x4 y5 y6 y7 (Z_to_bv 64 v16) (Z_to_bv 64 v24) (Z_to_bv 64 0) y11 y12 y13 y14 y15 y16 y17
                (Z_to_bv 64 v32) x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
           F (Z_to_bv 64 ra) fc None m' (seg_rom psegs))) ->
  evt psegs Q (MS R0 F (Z_to_bv 64 OL.FL_A_II) fc None m (seg_rom psegs)).
Proof.
  intros Q m strm p tt zc ra v16 v24 v32 ni ai x1 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 R0.
  intros T16 HZC H47 HTOP BOK IC STRM0 STRM8 STRM47 SOK1 SOK2 AP IMG RA V16 V24 V32 ZP F1 F2 F3 F4 C1 C2 C3 C4 N0 A8 HK.
  pose proof (OL.fl_ii CT R0 m (OL.IP strm p 0) zc tt ra v16 v24 v32 OL.FL_ZCALLOC OL.FL_ZCFREE ni ai) as Y.
  cbv zeta in Y. cbn [OL.ip_strm OL.ip_p OL.ip_w] in Y.
  specialize (Y ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) T16 HZC H47 HTOP BOK IC STRM0 STRM8 STRM47 SOK1 SOK2 AP IMG RA V16 V24 V32 ZP F1 F2 F3 F4 C1 C2 C3 C4 eq_refl eq_refl N0 A8).
  destruct Y as (R' & m' & RUN & FM & G10 & G2 & G8 & G9 & G18 & GK & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & IR & N0' & A8').
  eapply (evt_of_msteps_mkR psegs _ R0 F _ _ fc m m' (seg_rom psegs) R'); [apply rfull_mkR| exact RUN|].
  intros y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 ER'.
  subst R'. grw G10. grw G2. grw G8. grw G9. grw G18.
  apply rkeep_II in GK. grw GK. destruct GK as (G3 & G4 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27). subst R0.
  grw G3. grw G4. grw G19. grw G20. grw G21. grw G22. grw G23. grw G24. grw G25. grw G26. grw G27.
  subst. apply (HK m' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31); assumption.
Qed.

Lemma inf_evt : forall (Q : machine_state -> Prop) (m : word -> option byte) (strm p w sp ra inp outp zcl f : Z)
    (s : ZIS.inflate_state) (zc : ZI.ZCall) (ans : option (ZPG.blk * (Z -> Z)))
    (x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  let R0 := mkR (Z_to_bv 64 ra) (Z_to_bv 64 sp) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 strm) (Z_to_bv 64 f) x12 x13 x14 x15 x16 x17
                x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 in
  let q := OL.IP strm p w in
  let res := ZHF.inflate_p ZIS.ivar_ref ans s zc f in
  let s' := fst (fst res) in let r := snd (fst res) in
  OL.ra_ok ra -> sp mod 16 = 0 -> zcl + 1024 <= sp -> sp <= 2^47 -> 0x5f000 <= zcl ->
  OL.blocks_ok m zcl (OL.iblocks q) -> OL.img_clear m -> 0 < strm -> strm + 112 <= 2^47 -> strm mod 8 = 0 -> 0 < inp -> 0 < outp ->
  store_ok psegs m (Z_to_bv 64 (sp - 1024)) (Z.to_nat 1024) = true -> store_ok psegs m (Z_to_bv 64 strm) 112%nat = true ->
  store_ok psegs m (Z_to_bv 64 outp) (Z.to_nat (ZI.zc_avail_out zc)) = true ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart ((sp - 1024, 1024) :: (strm, 112) :: (outp, ZI.zc_avail_out zc) :: (inp, ZI.zlength (ZI.zc_input zc)) :: OL.iblocks q) ->
  (forall a n, In (a, n) [(sp - 1024, 1024); (strm, 112); (outp, ZI.zc_avail_out zc); (inp, ZI.zlength (ZI.zc_input zc))] -> a + n <= 0x10000 \/ 0x5f000 <= a) ->
  inp + ZI.zlength (ZI.zc_input zc) < 2^63 -> outp + ZI.zc_avail_out zc < 2^63 -> ZI.zc_avail_out zc < 2^31 -> ZI.zlength (ZI.zc_input zc) < 2^31 ->
  OL.fl_irep CT m q s -> (w = 0 <-> ZIS.is_window_blk s = None) -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.holds psegs m inp (ZI.zc_input zc) ->
  OL.izs_cells (OL.fl_msga CT) m strm inp (ZI.zlength (ZI.zc_input zc)) outp (ZI.zc_avail_out zc) (ZI.zc_strm zc) p OL.FL_ZCALLOC OL.FL_ZCFREE ->
  OL.fl_isafe CT s zc f ->
  (forall (m' : word -> option byte) (nout : Z) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     snd res = None ->
     0 <= nout <= ZI.zc_avail_out zc ->
     OF.frame_mod m m' ((Z_to_bv 64 (sp - 464), 464) :: (Z_to_bv 64 strm, 112) :: (Z_to_bv 64 outp, nout) :: OL.wz (OL.iblocks q)) ->
     (~ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateRc.RR (ZI.zr_rc r) ->
        nout = ZI.zlength (ZI.zr_output r) /\ 0 <= ZI.zr_consumed r <= ZI.zlength (ZI.zc_input zc) /\
        OL.fl_irep CT m' q s' /\
        OL.izs_cells (OL.fl_msga CT) m' strm (inp + ZI.zr_consumed r) (ZI.zlength (ZI.zc_input zc) - ZI.zr_consumed r) (outp + nout) (ZI.zc_avail_out zc - nout)
                     (ZI.zr_strm r) p OL.FL_ZCALLOC OL.FL_ZCFREE /\
        OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.holds psegs m' outp (ZI.zr_output r) /\ (w = 0 <-> ZIS.is_window_blk s' = None)) ->
     Q (MS (mkR y1 (Z_to_bv 64 sp) x3 x4 y5 y6 y7 x8 x9 (Z_to_bv 64 (ZI.zr_rc r)) y11 y12 y13 y14 y15 y16 y17
                x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
           F (Z_to_bv 64 ra) fc None m' (seg_rom psegs))) ->
  (forall (m' : word -> option byte) (nout : Z) (y1 y5 y6 y7 y8 y9 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
     snd res = Some 32768 -> w = 0 ->
     0 <= nout <= ZI.zc_avail_out zc ->
     OF.frame_mod m m' ((Z_to_bv 64 (sp - 464), 464) :: (Z_to_bv 64 strm, 112) :: (Z_to_bv 64 outp, nout) :: OL.wz (OL.iblocks q)) ->
     OL.fl_tw CT R0 (mkR y1 (Z_to_bv 64 (sp - 320)) x3 x4 y5 y6 y7 y8 y9 (Z_to_bv 64 0) (Z_to_bv 64 32768) (Z_to_bv 64 1) (Z_to_bv 64 OL.FL_ZCALLOC)
                      y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) q inp outp s zc f m' ->
     Q (MS (mkR y1 (Z_to_bv 64 (sp - 320)) x3 x4 y5 y6 y7 y8 y9 (Z_to_bv 64 0) (Z_to_bv 64 32768) (Z_to_bv 64 1) (Z_to_bv 64 OL.FL_ZCALLOC)
                y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
           F (Z_to_bv 64 OL.FL_A_ZW) fc None m' (seg_rom psegs))) ->
  evt psegs Q (MS R0 F (Z_to_bv 64 OL.FL_A_INFLATE) fc None m (seg_rom psegs)).
Proof.
  intros Q m strm p w sp ra inp outp zcl f s zc ans x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         R0 q res s' r.
  intros RA SP16 HZC H47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 OUTP0 SOK1 SOK2 SOK3 AP IMG B1 B2 B3 B4 IR WIN HLD ZS SAFE KR KW.
  pose proof (OL.fl_inf CT R0 m q s zc f sp ra inp outp zcl OL.FL_ZCALLOC OL.FL_ZCFREE ans) as Y.
  cbv zeta in Y. subst q. cbn [OL.ip_strm OL.ip_p OL.ip_w] in Y.
  specialize (Y ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) RA SP16 HZC H47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 OUTP0 SOK1 SOK2 SOK3 AP IMG B1 B2 B3 B4 IR WIN HLD ZS eq_refl eq_refl SAFE).
  destruct Y as (R' & m' & nout & NO & FM & EX).
  subst res. destruct (snd (ZHF.inflate_p ZIS.ivar_ref ans s zc f)) as [sz|] eqn:ASK.
  - destruct EX as (-> & W0 & RUN & G13 & G10 & G11 & G12 & G2 & G3 & G4 & TW).
    eapply (evt_of_msteps_mkR psegs _ R0 F _ _ fc m m' (seg_rom psegs) R'); [apply rfull_mkR| exact RUN|].
    intros y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 ER'.
    subst R'. grw G13. grw G10. grw G11. grw G12. grw G2. grw G3. grw G4. subst R0. grw G3. grw G4. subst.
    apply (KW m' nout); [first [reflexivity| exact ASK]| first [reflexivity| exact W0]| exact NO| exact FM| exact TW].
  - destruct EX as (RUN & G10 & G2 & GK & GRD).
    eapply (evt_of_msteps_mkR psegs _ R0 F _ _ fc m m' (seg_rom psegs) R'); [apply rfull_mkR| exact RUN|].
    intros y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 ER'.
    subst R'. grw G10. grw G2.
    apply rkeep_FL_KEEP in GK. grw GK. destruct GK as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27). subst R0.
    grw G3. grw G4. grw G8. grw G9. grw G18. grw G19. grw G20. grw G21. grw G22. grw G23. grw G24. grw G25. grw G26. grw G27.
    subst. eapply (KR m'); [first [reflexivity| exact ASK]| exact NO| exact FM| exact GRD].
Qed.

Lemma inb_evt : forall (Q : machine_state -> Prop) (m : word -> option byte) (strm p w sp ra inp outp zcl f : Z)
    (s : ZIS.inflate_state) (zc : ZI.ZCall) (b : ZPG.blk) (RW : bvmap 5 word)
    (e3 e4 e5 e6 e7 e8 e9 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 : word)
    (x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  let R0 := mkR (Z_to_bv 64 ra) (Z_to_bv 64 sp) e3 e4 e5 e6 e7 e8 e9 (Z_to_bv 64 strm) (Z_to_bv 64 f) e12 e13 e14 e15 e16 e17
                e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 in
  let R1 := mkR x1 (Z_to_bv 64 (sp - 320)) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 w) x11 x12 x13 x14 x15 x16 x17
                x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 in
  let ans := Some (b, fun _ : Z => 0) in
  let res := ZHF.inflate_p ZIS.ivar_ref ans s zc f in
  let s' := fst (fst res) in let r := snd (fst res) in
  OL.fl_tw CT R0 RW (OL.IP strm p 0) inp outp s zc f m -> OL.rkeep RW R1 OL.FL_KEEP ->
  zcl + 1024 <= sp -> sp <= 2^47 -> OL.img_clear m ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.blk_okz psegs m 0x5f000 zcl w 32768 -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.zeros_at psegs m w 32768 ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart ((w, 32768) :: (sp - 1024, 1024) :: (strm, 112) :: (outp, ZI.zc_avail_out zc) :: (inp, ZI.zlength (ZI.zc_input zc)) :: OL.iblocks (OL.IP strm p 0)) ->
  snd res = Some 32768 ->
  (forall (m' : word -> option byte) (nout : Z) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     0 <= nout <= ZI.zc_avail_out zc ->
     OF.frame_mod m m' ((Z_to_bv 64 (sp - 464), 464) :: (Z_to_bv 64 strm, 112) :: (Z_to_bv 64 outp, nout) :: OL.wz (OL.iblocks (OL.IP strm p w))) ->
     (~ OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateRc.RR (ZI.zr_rc r) ->
        nout = ZI.zlength (ZI.zr_output r) /\ 0 <= ZI.zr_consumed r <= ZI.zlength (ZI.zc_input zc) /\
        OL.fl_irep CT m' (OL.IP strm p w) s' /\
        OL.izs_cells (OL.fl_msga CT) m' strm (inp + ZI.zr_consumed r) (ZI.zlength (ZI.zc_input zc) - ZI.zr_consumed r) (outp + nout) (ZI.zc_avail_out zc - nout)
                     (ZI.zr_strm r) p OL.FL_ZCALLOC OL.FL_ZCFREE /\
        OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.holds psegs m' outp (ZI.zr_output r)) ->
     Q (MS (mkR y1 (Z_to_bv 64 sp) e3 e4 y5 y6 y7 e8 e9 (Z_to_bv 64 (ZI.zr_rc r)) y11 y12 y13 y14 y15 y16 y17
                e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 y28 y29 y30 y31)
           F (Z_to_bv 64 ra) fc None m' (seg_rom psegs))) ->
  evt psegs Q (MS R1 F (Z_to_bv 64 OL.FL_A_ZB) fc None m (seg_rom psegs)).
Proof.
  intros Q m strm p w sp ra inp outp zcl f s zc b RW e3 e4 e5 e6 e7 e8 e9 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31
         x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 R0 R1 ans res s' r.
  intros TW RK HZC H47 IC BW ZW AP ASK HK.
  pose proof (OL.fl_inb CT R0 RW R1 m (OL.IP strm p 0) s zc f sp ra inp outp zcl OL.FL_ZCALLOC OL.FL_ZCFREE w b) as Y.
  cbv zeta in Y. cbn [OL.ip_strm OL.ip_p OL.ip_w] in Y. subst ans res.
  specialize (Y TW RK ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) HZC H47 IC eq_refl eq_refl BW ZW AP ASK).
  destruct Y as (R' & m' & nout & RUN & NO & FM & G10 & G2 & GK & GRD).
  eapply (evt_of_msteps_mkR psegs _ R1 F _ _ fc m m' (seg_rom psegs) R'); [apply rfull_mkR| exact RUN|].
  intros y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 ER'.
  subst R'. grw G10. grw G2.
  apply rkeep_FL_KEEP in GK. grw GK. destruct GK as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27). subst R0 R1.
  grw G3. grw G4. grw G8. grw G9. grw G18. grw G19. grw G20. grw G21. grw G22. grw G23. grw G24. grw G25. grw G26. grw G27.
  subst. eapply (HK m'); [exact NO| exact FM| exact GRD].
Qed.

Lemma isy_evt : forall (Q : machine_state -> Prop) (m : word -> option byte) (strm p w sp ra inp outp zcl : Z)
    (s : ZIS.inflate_state) (zc : ZI.ZCall)
    (x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  let R0 := mkR (Z_to_bv 64 ra) (Z_to_bv 64 sp) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 strm) x11 x12 x13 x14 x15 x16 x17
                x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 in
  let q := OL.IP strm p w in
  let s' := fst (OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateSync.inflateSync_m ZIS.ivar_ref s zc) in let r := snd (OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateSync.inflateSync_m ZIS.ivar_ref s zc) in
  OL.ra_ok ra -> sp mod 16 = 0 -> zcl + 1024 <= sp -> sp <= 2^47 -> 0x5f000 <= zcl ->
  OL.blocks_ok m zcl (OL.iblocks q) -> OL.img_clear m -> 0 < strm -> strm + 112 <= 2^63 -> strm mod 8 = 0 -> 0 < inp ->
  store_ok psegs m (Z_to_bv 64 (sp - 96)) 96%nat = true -> store_ok psegs m (Z_to_bv 64 strm) 112%nat = true ->
  OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.all_apart ((sp - 96, 96) :: (strm, 112) :: (inp, ZI.zlength (ZI.zc_input zc)) :: OL.iblocks q) ->
  (forall a n, In (a, n) [(sp - 96, 96); (strm, 112); (inp, ZI.zlength (ZI.zc_input zc))] -> a + n <= 0x10000 \/ 0x5f000 <= a) ->
  inp + ZI.zlength (ZI.zc_input zc) < 2^63 -> ZI.zlength (ZI.zc_input zc) < 2^32 ->
  OL.fl_irep CT m q s -> OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ExSmallIface.holds psegs m inp (ZI.zc_input zc) ->
  OL.izs_cells (OL.fl_msga CT) m strm inp (ZI.zlength (ZI.zc_input zc)) outp (ZI.zc_avail_out zc) (ZI.zc_strm zc) p OL.FL_ZCALLOC OL.FL_ZCFREE ->
  OL.fl_ssafe CT s zc ->
  (forall (m' : word -> option byte) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     OF.frame_mod m m' ((Z_to_bv 64 (sp - 96), 96) :: (Z_to_bv 64 strm, 112) :: OL.wz (OL.iblocks q)) ->
     ZI.zr_output r = [] -> 0 <= ZI.zr_consumed r <= ZI.zlength (ZI.zc_input zc) ->
     OL.fl_irep CT m' q s' ->
     OL.izs_cells (OL.fl_msga CT) m' strm (inp + ZI.zr_consumed r) (ZI.zlength (ZI.zc_input zc) - ZI.zr_consumed r) outp (ZI.zc_avail_out zc)
                  (ZI.zr_strm r) p OL.FL_ZCALLOC OL.FL_ZCFREE ->
     (w = 0 <-> ZIS.is_window_blk s' = None) ->
     Q (MS (mkR y1 (Z_to_bv 64 sp) x3 x4 y5 y6 y7 x8 x9 (Z_to_bv 64 (ZI.zr_rc r)) y11 y12 y13 y14 y15 y16 y17
                x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
           F (Z_to_bv 64 ra) fc None m' (seg_rom psegs))) ->
  evt psegs Q (MS R0 F (Z_to_bv 64 OL.FL_A_ISY) fc None m (seg_rom psegs)).
Proof.
  intros Q m strm p w sp ra inp outp zcl s zc x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
         R0 q s' r.
  intros RA SP16 HZC H47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS SAFE HK.
  pose proof (OL.fl_isy CT R0 m q s zc sp ra inp outp zcl OL.FL_ZCALLOC OL.FL_ZCFREE) as Y.
  cbv zeta in Y. subst q. cbn [OL.ip_strm OL.ip_p OL.ip_w] in Y.
  specialize (Y ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) RA SP16 HZC H47 HTOP BOK IC STRM0 STRM63 STRM8 INP0 SOK1 SOK2 AP IMG B1 B2 IR HLD ZS eq_refl eq_refl SAFE).
  destruct Y as (R' & m' & RUN & FM & G10 & G2 & GK & OUT0 & CONS & IR' & ZS' & WIN').
  eapply (evt_of_msteps_mkR psegs _ R0 F _ _ fc m m' (seg_rom psegs) R'); [apply rfull_mkR| exact RUN|].
  intros y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 ER'.
  subst R'. grw G10. grw G2.
  apply rkeep_FL_KEEP in GK. grw GK. destruct GK as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27). subst R0.
  grw G3. grw G4. grw G8. grw G9. grw G18. grw G19. grw G20. grw G21. grw G22. grw G23. grw G24. grw G25. grw G26. grw G27.
  subst. apply (HK m' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31); assumption.
Qed.

End CALL.
