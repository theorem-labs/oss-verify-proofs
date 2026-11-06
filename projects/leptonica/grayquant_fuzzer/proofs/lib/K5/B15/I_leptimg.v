(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.G3 Require Import LeptFormats LeptShapes.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import I_pck I_pcbits.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma lf_cstr_00 : forall m, mem_inv asegs m -> cstr_at m 0x236a0 (zb8 (fst LS_00 ++ pshape_bytes (snd LS_00))).
Proof. cstr_tac. Qed.
Lemma lf_cstr_01 : forall m, mem_inv asegs m -> cstr_at m 0x242a0 (zb8 (fst LS_01 ++ pshape_bytes (snd LS_01))).
Proof. cstr_tac. Qed.
Lemma lf_cstr_02 : forall m, mem_inv asegs m -> cstr_at m 0x24360 (zb8 (fst LS_02 ++ pshape_bytes (snd LS_02))).
Proof. cstr_tac. Qed.
Lemma lf_cstr_03 : forall m, mem_inv asegs m -> cstr_at m 0x243c0 (zb8 (fst LS_03 ++ pshape_bytes (snd LS_03))).
Proof. cstr_tac. Qed.
Lemma lf_cstr_04 : forall m, mem_inv asegs m -> cstr_at m 0x24420 (zb8 (fst LS_04 ++ pshape_bytes (snd LS_04))).
Proof. cstr_tac. Qed.
Lemma lf_cstr_05 : forall m, mem_inv asegs m -> cstr_at m 0x244a0 (zb8 (fst LS_05 ++ pshape_bytes (snd LS_05))).
Proof. cstr_tac. Qed.
Lemma lf_cstr_06 : forall m, mem_inv asegs m -> cstr_at m 0x24e00 (zb8 (fst LS_06 ++ pshape_bytes (snd LS_06))).
Proof. cstr_tac. Qed.
Lemma lf_cstr_07 : forall m, mem_inv asegs m -> cstr_at m 0x24aa0 (zb8 (fst LS_07 ++ pshape_bytes (snd LS_07))).
Proof. cstr_tac. Qed.
Lemma lf_cstr_08 : forall m, mem_inv asegs m -> cstr_at m 0x24f60 (zb8 (fst LS_08 ++ pshape_bytes (snd LS_08))).
Proof. cstr_tac. Qed.
Lemma lf_cstr_09 : forall m, mem_inv asegs m -> cstr_at m 0x24fc0 (zb8 (fst LS_09 ++ pshape_bytes (snd LS_09))).
Proof. cstr_tac. Qed.
Lemma lf_cstr_10 : forall m, mem_inv asegs m -> cstr_at m 0x25020 (zb8 (fst LS_10 ++ pshape_bytes (snd LS_10))).
Proof. cstr_tac. Qed.
Lemma lf_cstr_11 : forall m, mem_inv asegs m -> cstr_at m 0x25080 (zb8 (fst LS_11 ++ pshape_bytes (snd LS_11))).
Proof. cstr_tac. Qed.
Lemma lf_cstr_12 : forall m, mem_inv asegs m -> cstr_at m 0x250c0 (zb8 (fst LS_12 ++ pshape_bytes (snd LS_12))).
Proof. cstr_tac. Qed.
Lemma lf_cstr_13 : forall m, mem_inv asegs m -> cstr_at m 0x25120 (zb8 (fst LS_13 ++ pshape_bytes (snd LS_13))).
Proof. cstr_tac. Qed.
Lemma lf_cstr_14 : forall m, mem_inv asegs m -> cstr_at m 0x25180 (zb8 (fst LS_14 ++ pshape_bytes (snd LS_14))).
Proof. cstr_tac. Qed.
Lemma lf_cstr_15 : forall m, mem_inv asegs m -> cstr_at m 0x251e0 (zb8 (fst LS_15 ++ pshape_bytes (snd LS_15))).
Proof. cstr_tac. Qed.
Lemma lf_cstr_16 : forall m, mem_inv asegs m -> cstr_at m 0x26c60 (zb8 (fst LS_16 ++ pshape_bytes (snd LS_16))).
Proof. cstr_tac. Qed.
Lemma lf_cstr_17 : forall m, mem_inv asegs m -> cstr_at m 0x26dc0 (zb8 (fst LS_17 ++ pshape_bytes (snd LS_17))).
Proof. cstr_tac. Qed.

(* [comment removed for export] *)
Definition LEPT_IMG : list (Z * (list Z * list lkind * (list Z * pshape))) :=
  [ (0x236a0, (LF_00, map (fun it => fst (fst it)) (snd LS_00), LS_00))
  ; (0x242a0, (LF_01, map (fun it => fst (fst it)) (snd LS_01), LS_01))
  ; (0x24360, (LF_02, map (fun it => fst (fst it)) (snd LS_02), LS_02))
  ; (0x243c0, (LF_03, map (fun it => fst (fst it)) (snd LS_03), LS_03))
  ; (0x24420, (LF_04, map (fun it => fst (fst it)) (snd LS_04), LS_04))
  ; (0x244a0, (LF_05, map (fun it => fst (fst it)) (snd LS_05), LS_05))
  ; (0x24e00, (LF_06, map (fun it => fst (fst it)) (snd LS_06), LS_06))
  ; (0x24aa0, (LF_07, map (fun it => fst (fst it)) (snd LS_07), LS_07))
  ; (0x24f60, (LF_08, map (fun it => fst (fst it)) (snd LS_08), LS_08))
  ; (0x24fc0, (LF_09, map (fun it => fst (fst it)) (snd LS_09), LS_09))
  ; (0x25020, (LF_10, map (fun it => fst (fst it)) (snd LS_10), LS_10))
  ; (0x25080, (LF_11, map (fun it => fst (fst it)) (snd LS_11), LS_11))
  ; (0x250c0, (LF_12, map (fun it => fst (fst it)) (snd LS_12), LS_12))
  ; (0x25120, (LF_13, map (fun it => fst (fst it)) (snd LS_13), LS_13))
  ; (0x25180, (LF_14, map (fun it => fst (fst it)) (snd LS_14), LS_14))
  ; (0x251e0, (LF_15, map (fun it => fst (fst it)) (snd LS_15), LS_15))
  ; (0x26c60, (LF_16, map (fun it => fst (fst it)) (snd LS_16), LS_16))
  ; (0x26dc0, (LF_17, map (fun it => fst (fst it)) (snd LS_17), LS_17)) ].

Lemma LEPT_IMG_rows : map snd LEPT_IMG = LEPT_SHAPES.
Proof. reflexivity. Qed.

Lemma lept_img_cstr : forall A f ks t0 sh m, In (A, (f, ks, (t0, sh))) LEPT_IMG -> mem_inv asegs m ->
  cstr_at m A (zb8 (t0 ++ pshape_bytes sh)) /\ 65536 <= A /\ A + Z.of_nat (length f) <= 0x2a3c4.
Proof.
  intros A f ks t0 sh m Hin MI. unfold LEPT_IMG in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <- <- <-; split; [first [exact (lf_cstr_00 m MI) | exact (lf_cstr_01 m MI) | exact (lf_cstr_02 m MI) | exact (lf_cstr_03 m MI) | exact (lf_cstr_04 m MI) | exact (lf_cstr_05 m MI) | exact (lf_cstr_06 m MI) | exact (lf_cstr_07 m MI) | exact (lf_cstr_08 m MI) | exact (lf_cstr_09 m MI) | exact (lf_cstr_10 m MI) | exact (lf_cstr_11 m MI) | exact (lf_cstr_12 m MI) | exact (lf_cstr_13 m MI) | exact (lf_cstr_14 m MI) | exact (lf_cstr_15 m MI) | exact (lf_cstr_16 m MI) | exact (lf_cstr_17 m MI)] | split; [lia | vm_compute; discriminate]]|]).
  destruct Hin.
Qed.
