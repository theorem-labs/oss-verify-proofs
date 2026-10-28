(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AF_huf_w4s3b AF_huf_w4s34k AF_huf_w4s34k2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation amem := (word -> option byte).

Ltac w4br6 b :=
  lazymatch goal with
  | |- branch_taken BC_EQ (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
         (EAlu ALU_XOR ?P (EAluw ALU_SRL ?X (ELit 3))) (ELit 1)))) (edenot ?E (ELit 0)) = false =>
      apply (w4_br_nzk E P (EAluw ALU_SRL X (ELit 3)));
      rewrite (w4_srlw3 E X b); [ | w4ez; first [reflexivity | f_equal; lia] | lia ];
      w4uzm
  end.


Section CANSEC1. Context {rc : runConstT}.
Theorem w4s34_d4L : w4s34_d4L_case.
Proof.
  unfold w4s34_d4L_case.
  intros.
  match goal with HB : bytes_at _ _ (_ + 4) _, TB : w4_tbok _ _ |- _ =>
    pose proof (ztab_fact_bytes_at bsegs _ (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] _ HB ltac:(lia) TB) as HZ end.
  kx_runFLd [0x8c024; 0x8c3ec; 0x8c4f8] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 0 (2^32); KZRange b 0 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 1 (2^32); KZRange (len - off) 0 (2^32);
       KZRange (dcap - 3 * seg - q) 4 (2^32);
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWord (SP + -384) 8 (DST + dcap); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)].
  all: try w4br5.
  all: try w4br.
  all: try w4word4.
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs;
      replace (Z_to_bv 64 (- tl + 64)) with (Z_to_bv 64 (64 - tl)) by (f_equal; lia);
      replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (- DT - 5)) by (f_equal; lia);
      replace (Z_to_bv 64 (DST + (3 * seg + q))) with (Z_to_bv 64 (DST + 3 * seg + q)) by (f_equal; lia);
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_fix_x5 dl tl rsv;
      try replace (Z_to_bv 64 (-3 * seg + (- q + dcap))) with (Z_to_bv 64 (dcap - 3 * seg - q)) by (f_equal; lia);
      try change (mem_denot _ mm []) with mm end).
  all: try (lazymatch goal with KK : forall _ : word, _ |- evtF _ _ _ _ => eapply KK end).
Time Qed.

Theorem w4s34_d4E : w4s34_d4E_case.
Proof.
  unfold w4s34_d4E_case.
  intros.
  match goal with HB : bytes_at _ _ (_ + 4) _, TB : w4_tbok _ _ |- _ =>
    pose proof (ztab_fact_bytes_at bsegs _ (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] _ HB ltac:(lia) TB) as HZ end.
  kx_runFLd [0x8c024; 0x8c3ec; 0x8c4f8] 400%nat (repeat true 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 0 (2^32); KZRange b 0 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 1 (2^32); KZRange (len - off) 0 (2^32);
       KZRange (dcap - 3 * seg - q) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWord (SP + -384) 8 (DST + dcap); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)].
  all: try w4br5.
  all: try w4br.
  all: try w4word4.
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs;
      replace (Z_to_bv 64 (- tl + 64)) with (Z_to_bv 64 (64 - tl)) by (f_equal; lia);
      replace (Z_to_bv 64 (- DT + -5)) with (Z_to_bv 64 (- DT - 5)) by (f_equal; lia);
      replace (Z_to_bv 64 (DST + (3 * seg + q))) with (Z_to_bv 64 (DST + 3 * seg + q)) by (f_equal; lia);
      replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => w4_fix_x5 dl tl rsv;
      try replace (Z_to_bv 64 (-3 * seg + (- q + dcap))) with (Z_to_bv 64 (dcap - 3 * seg - q)) by (f_equal; lia);
      try change (mem_denot _ mm []) with mm end).
  all: try (lazymatch goal with KK : forall _ : word, _ |- evtF _ _ _ _ => eapply KK end).
Time Qed.

Definition w4s34_d4XL_case2 : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> 3 * seg + q + 4 <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> off = 0 -> 1 <= len -> len <= 2^32 -> 64 < b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  w4_tbok cbs tl ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (wp ws we : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -224, SP + -184)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 wp; C8 ws; C8 we] ->
     0 <= c' < 2^64 -> 0 <= b' < 2^32 ->
     evtF bsegs RNG Q
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13
                 y14 y15 y16 y17 y18
                 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23
                 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x8c4f8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) x22 x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8bff0) fc None mm (seg_rom bsegs)).

Theorem w4s34_d4XL : w4s34_d4XL_case2.
Proof.
  unfold w4s34_d4XL_case2.
  intros.
  match goal with HB : bytes_at _ _ (_ + 4) _, TB : w4_tbok _ _ |- _ =>
    pose proof (ztab_fact_bytes_at bsegs _ (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] _ HB ltac:(lia) TB) as HZ end.
  kx_runFLd [0x8c024; 0x8c3ec; 0x8c4f8] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 0 0; KZRange b 65 (2^31 - 1); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 1 (2^32); KZRange (len - off) 1 (2^32);
       KZRange (dcap - 3 * seg - q) 4 (2^32);
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWord (SP + -384) 8 (DST + dcap); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)].
  all: try w4br5.
  all: try w4br.
  all: try w4word4.
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; w4_norm_to (DST + 3 * seg + q) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -224, SP + -184)] mm) as MUW;
      pose proof (wmono_refl bsegs mm) as WMr;
      kx_munch_wins MUW [(SP + -224, 40)];
      kx_post_mem_free end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (?A + -224) _ |- _ => kx_cells_split H end end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_cells_post; w4_c4fix end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (_ + -224) [C8 (Z_to_bv 64 ?X)] |- _ =>
        rewrite <- (Z_to_bv_mod64 X) in H end; idtac end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?log) _) =>
      eapply (KK _ (replay E log DST ob)) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -224) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- u8arr _ _ _ _ => apply kx_u8arr_replay; eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- 0 <= _ mod 2 ^ 64 < 2 ^ 64 => apply Z.mod_pos_bound; lia end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4_bnd; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => eassumption end).
Time Qed.

Definition w4s34_d4XE_case2 : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> 3 * seg + q <= dcap -> dcap < 3 * seg + q + 4 ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> off = 0 -> 1 <= len -> len <= 2^32 -> 64 < b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  w4_tbok cbs tl ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (wp ws we : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -224, SP + -184)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 wp; C8 ws; C8 we] ->
     0 <= c' < 2^64 -> 0 <= b' < 2^32 ->
     evtF bsegs RNG Q
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13
                 y14 y15 y16 y17 y18
                 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23
                 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x8c4f8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) x22 x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8bff0) fc None mm (seg_rom bsegs)).

Theorem w4s34_d4XE : w4s34_d4XE_case2.
Proof.
  unfold w4s34_d4XE_case2.
  intros.
  match goal with HB : bytes_at _ _ (_ + 4) _, TB : w4_tbok _ _ |- _ =>
    pose proof (ztab_fact_bytes_at bsegs _ (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] _ HB ltac:(lia) TB) as HZ end.
  kx_runFLd [0x8c024; 0x8c3ec; 0x8c4f8] 400%nat (repeat true 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 0 0; KZRange b 65 (2^31 - 1); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 1 (2^32); KZRange (len - off) 1 (2^32);
       KZRange (dcap - 3 * seg - q) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWord (SP + -384) 8 (DST + dcap); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
      [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)].
  all: try w4br5.
  all: try w4br6 b.
  all: try w4br.
  all: try w4word4.
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; w4_phase_clear;
      try replace (Z_to_bv 64 (-3 * seg + (- q + dcap))) with (Z_to_bv 64 (dcap - 3 * seg - q)) by (f_equal; lia) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
  kx_runFLd [0x8c4f8; 0x8c4e8; 0x8c69c] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 0 0; KZRange b 65 (2^31 - 1); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 1 (2^32); KZRange (len - off) 1 (2^32);
       KZRange (dcap - 3 * seg - q) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]]
       [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap)]
    end).
  all: try w4br5.
  all: try w4br6 b.
  all: try w4br.
  all: try w4word4.
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; w4_norm_to (DST + 3 * seg + q) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -224, SP + -184)] mm) as MUW;
      pose proof (wmono_refl bsegs mm) as WMr;
      kx_munch_wins MUW [(SP + -224, 40)];
      kx_post_mem_free end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (?A + -224) _ |- _ => kx_cells_split H end end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_cells_post; w4_c4fix end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (_ + -224) [C8 (Z_to_bv 64 ?X)] |- _ =>
        rewrite <- (Z_to_bv_mod64 X) in H end; idtac end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?log) _) =>
      eapply (KK _ (replay E log DST ob)) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -224) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- u8arr _ _ _ _ => apply kx_u8arr_replay; eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- 0 <= _ mod 2 ^ 64 < 2 ^ 64 => apply Z.mod_pos_bound; lia end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4_bnd; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => eassumption end).
Time Qed.

Definition w4s34_eov_case2 : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  rw_cells bsegs mm 0xba2f8 [C8 (Z_to_bv 64 0x7fff8000)] ->
  unpoisoned mm (SP + -480) SP -> SP mod 16 = 0 -> rng RNG (shad (SP + -480)) (shlen (480 + 7)) ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> 3 * seg + q <= dcap -> dcap - 3 * seg - q <= 3 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> off = 0 -> 64 < b -> 1 <= len -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (wp ws we : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -224, SP + -184)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 wp; C8 ws; C8 we] ->
     0 <= c' < 2^64 -> 0 <= b' < 2^32 ->
     evtF bsegs RNG Q
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13
                 y14 y15 y16 y17 y18
                 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23
                 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x8c4f8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (dcap - 3 * seg - q)) (Z_to_bv 64 b) (Z_to_bv 64 4) x13
               x14 x15 x16 x17 x18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) x22 x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c3ec) fc None mm (seg_rom bsegs)).

Theorem w4s34_eov : w4s34_eov_case2.
Proof.
  unfold w4s34_eov_case2.
  intros.
  kx_runFLd [0x8c4f8; 0x8c4e8; 0x8c69c] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 0 0; KZRange b 65 (2^31 - 1); KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 1 (2^32); KZRange (len - off) 1 (2^32);
       KZRange (dcap - 3 * seg - q) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]; KZAlign SP 16; KZWord 0xba2f8 8 0x7fff8000]
       [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap); (SP + -480, 480)].
  all: try w4br5.
  all: try w4br.
  all: try w4word4.
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; w4_norm_to (DST + 3 * seg + q) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -224, SP + -184)] mm) as MUW;
      pose proof (wmono_refl bsegs mm) as WMr;
      kx_munch_wins MUW [(SP + -224, 40)];
      kx_post_mem_free end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (?A + -224) _ |- _ => kx_cells_split H end end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_cells_post; w4_c4fix end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (_ + -224) [C8 (Z_to_bv 64 ?X)] |- _ =>
        rewrite <- (Z_to_bv_mod64 X) in H end; idtac end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?log) _) =>
      eapply (KK _ (replay E log DST ob)) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -224) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- u8arr _ _ _ _ => apply kx_u8arr_replay; eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- 0 <= _ mod 2 ^ 64 < 2 ^ 64 => apply Z.mod_pos_bound; lia end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4_bnd; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => eassumption end).
Time Qed.

Definition w4s34_ef_case2 : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  rw_cells bsegs mm 0xba2f8 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells bsegs mm 0xb2128 [C8 (Z_to_bv 64 0xba2f8)] -> rng RNG 0xb2128 8 -> rng RNG 0xba2f8 8 ->
  wr_at bsegs mm (SP + -496) 16 -> rng RNG (SP + -496) 16 -> KXGoM.apart S len (SP + -496) 16 ->
  unpoisoned mm (SP + -480) SP -> SP mod 16 = 0 -> rng RNG (shad (SP + -480)) (shlen (480 + 7)) ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> 3 * seg + q <= dcap -> dcap - 3 * seg - q <= 3 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 8 <= off -> b <= 64 -> off + 8 <= len -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (wp ws we : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -224, SP + -184); (SP + -496, SP + -480)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 wp; C8 ws; C8 we] ->
     0 <= c' < 2^64 -> 0 <= b' < 2^32 ->
     evtF bsegs RNG Q
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13
                 y14 y15 y16 y17 y18
                 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23
                 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x8c4f8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (dcap - 3 * seg - q)) (Z_to_bv 64 b) (Z_to_bv 64 4) x13
               x14 x15 x16 x17 x18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) x22 x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c3ec) fc None mm (seg_rom bsegs)).

Theorem w4s34_ef : w4s34_ef_case2.
Proof.
  unfold w4s34_ef_case2.
  intros.
  match goal with HU : _ mm (SP + -480) SP |- _ =>
    assert (SHZ : forall s, ASHOFF + (SP + -480) / 8 <= s < ASHOFF + SP / 8 -> mm (wa s) = Some (Z_to_bv 8 0))
      by (destruct HU as (HU0 & HU1 & HU2); intros s Hs; destruct (HU2 (s - ASHOFF)) as (bb & Hb & Hg);
          [lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia |];
          replace (ASHOFF + (s - ASHOFF)) with s in Hb by lia;
          rewrite (gran_ok_full _ _ Hg) in Hb by (Z.div_mod_to_equations; lia); exact Hb) end.
  unfold ASHOFF in SHZ.
  kx_runFLd [0x8c4f8; 0x8c4e8; 0x8c69c] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 8 (2^32); KZRange (b / 8) 0 8; KZRange (off - b / 8) 0 (2^32); KZRange b 0 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 16 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]; KZAlign SP 16; KZWord 0xb2128 8 0xba2f8; KZWr (SP + -496) 16; KZDisj S len (SP + -496) 16; KZWord 0xba2f8 8 0x7fff8000]
       [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl); (SP + -496, 16); (0xb2128, 8); (0xba2f8, 8)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap); (SP + -480, 480)].
  all: try (lazymatch goal with |- branch_taken BC_NE (edenot _ (EVar _)) _ = false => kx_asan SHZ end).
  all: try w4br5.
  all: try w4br6 b.
  all: try w4br.
  all: try w4word4.
  all: try w4shd.
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 8)) /\ _ =>
      apply (w4_shd8 E X B O k); [ first [ w4xbw | w4s34_xbs | w4s34_xbt tl ] | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) (elenZ _ (ELit 4)) /\ _ =>
      apply (w4_shd4 E X B O k); [ first [ w4xbw | w4s34_xbs | w4s34_xbt tl ] | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) _ /\ _ =>
      apply (w4_shd_ap E X B O k); [ first [ w4xbw | w4s34_xbs | w4s34_xbt tl ] | lia | lia | w4uz | w4uz | w4apz ] end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; w4_norm_to (DST + 3 * seg + q) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -224, SP + -184); (SP + -496, SP + -480)] mm) as MUW;
      pose proof (wmono_refl bsegs mm) as WMr;
      kx_munch_wins MUW [(SP + -224, 40); (SP + -496, 16)];
      kx_post_mem_free end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (?A + -224) _ |- _ => kx_cells_split H end end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_cells_post; w4_c4fix end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (_ + -224) [C8 (Z_to_bv 64 ?X)] |- _ =>
        rewrite <- (Z_to_bv_mod64 X) in H end; idtac end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?log) _) =>
      eapply (KK _ (replay E log DST ob)) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -224) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- u8arr _ _ _ _ => apply kx_u8arr_replay; eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- 0 <= _ mod 2 ^ 64 < 2 ^ 64 => apply Z.mod_pos_bound; lia end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4_bnd; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => eassumption end).
Time Qed.

Definition w4s34_ez_case2 : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  rw_cells bsegs mm 0xba2f8 [C8 (Z_to_bv 64 0x7fff8000)] ->
  unpoisoned mm (SP + -480) SP -> SP mod 16 = 0 -> rng RNG (shad (SP + -480)) (shlen (480 + 7)) ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> 3 * seg + q <= dcap -> dcap - 3 * seg - q <= 3 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> off = 0 -> b <= 64 -> 1 <= len -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (wp ws we : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -224, SP + -184)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 wp; C8 ws; C8 we] ->
     0 <= c' < 2^64 -> 0 <= b' < 2^32 ->
     evtF bsegs RNG Q
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13
                 y14 y15 y16 y17 y18
                 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23
                 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x8c4f8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (dcap - 3 * seg - q)) (Z_to_bv 64 b) (Z_to_bv 64 4) x13
               x14 x15 x16 x17 x18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) x22 x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c3ec) fc None mm (seg_rom bsegs)).

Theorem w4s34_ez : w4s34_ez_case2.
Proof.
  unfold w4s34_ez_case2.
  intros.
  kx_runFLd [0x8c4f8; 0x8c4e8; 0x8c69c] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 0 0; KZRange b 0 64; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 1 (2^32); KZRange (len - off) 1 (2^32);
       KZRange (dcap - 3 * seg - q) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]; KZAlign SP 16; KZWord 0xba2f8 8 0x7fff8000]
       [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap); (SP + -480, 480)].
  all: try w4br5.
  all: try w4br.
  all: try w4word4.
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; w4_norm_to (DST + 3 * seg + q) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -224, SP + -184)] mm) as MUW;
      pose proof (wmono_refl bsegs mm) as WMr;
      kx_munch_wins MUW [(SP + -224, 40)];
      kx_post_mem_free end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (?A + -224) _ |- _ => kx_cells_split H end end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_cells_post; w4_c4fix end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (_ + -224) [C8 (Z_to_bv 64 ?X)] |- _ =>
        rewrite <- (Z_to_bv_mod64 X) in H end; idtac end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?log) _) =>
      eapply (KK _ (replay E log DST ob)) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -224) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- u8arr _ _ _ _ => apply kx_u8arr_replay; eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- 0 <= _ mod 2 ^ 64 < 2 ^ 64 => apply Z.mod_pos_bound; lia end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4_bnd; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => eassumption end).
Time Qed.

Definition w4s34_eca_case2 : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  rw_cells bsegs mm 0xba2f8 [C8 (Z_to_bv 64 0x7fff8000)] ->
  unpoisoned mm (SP + -480) SP -> SP mod 16 = 0 -> rng RNG (shad (SP + -480)) (shlen (480 + 7)) ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> 3 * seg + q <= dcap -> dcap - 3 * seg - q <= 3 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> b <= 64 -> b / 8 <= off -> off + 8 <= len -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (wp ws we : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -224, SP + -184)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 wp; C8 ws; C8 we] ->
     0 <= c' < 2^64 -> 0 <= b' < 2^32 ->
     evtF bsegs RNG Q
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13
                 y14 y15 y16 y17 y18
                 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23
                 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x8c4f8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (dcap - 3 * seg - q)) (Z_to_bv 64 b) (Z_to_bv 64 4) x13
               x14 x15 x16 x17 x18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) x22 x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c3ec) fc None mm (seg_rom bsegs)).

Theorem w4s34_eca : w4s34_eca_case2.
Proof.
  unfold w4s34_eca_case2.
  intros.
  assert (HBND : 0 <= b <= 7 \/ 8 <= b <= 15 \/ 16 <= b <= 23 \/ 24 <= b <= 31 \/ 32 <= b <= 39 \/ 40 <= b <= 47 \/ 48 <= b <= 55 \/ 56 <= b <= 63) by (Z.div_mod_to_equations; lia).
  destruct HBND as [HB|[HB|[HB|[HB|[HB|[HB|[HB|HB]]]]]]]; [
  kx_runFLd [0x8c4f8; 0x8c4e8; 0x8c69c] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 1 7; KZRange (off - b / 8) 0 7; KZRange b 0 7; KZRange (b / 8) 0 0; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]; KZAlign SP 16; KZWord 0xba2f8 8 0x7fff8000]
       [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap); (SP + -480, 480)]
  |
  kx_runFLd [0x8c4f8; 0x8c4e8; 0x8c69c] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 1 7; KZRange (off - b / 8) 0 7; KZRange b 8 15; KZRange (b / 8) 1 1; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]; KZAlign SP 16; KZWord 0xba2f8 8 0x7fff8000]
       [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap); (SP + -480, 480)]
  |
  kx_runFLd [0x8c4f8; 0x8c4e8; 0x8c69c] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 2 7; KZRange (off - b / 8) 0 7; KZRange b 16 23; KZRange (b / 8) 2 2; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]; KZAlign SP 16; KZWord 0xba2f8 8 0x7fff8000]
       [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap); (SP + -480, 480)]
  |
  kx_runFLd [0x8c4f8; 0x8c4e8; 0x8c69c] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 3 7; KZRange (off - b / 8) 0 7; KZRange b 24 31; KZRange (b / 8) 3 3; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]; KZAlign SP 16; KZWord 0xba2f8 8 0x7fff8000]
       [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap); (SP + -480, 480)]
  |
  kx_runFLd [0x8c4f8; 0x8c4e8; 0x8c69c] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 4 7; KZRange (off - b / 8) 0 7; KZRange b 32 39; KZRange (b / 8) 4 4; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]; KZAlign SP 16; KZWord 0xba2f8 8 0x7fff8000]
       [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap); (SP + -480, 480)]
  |
  kx_runFLd [0x8c4f8; 0x8c4e8; 0x8c69c] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 5 7; KZRange (off - b / 8) 0 7; KZRange b 40 47; KZRange (b / 8) 5 5; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]; KZAlign SP 16; KZWord 0xba2f8 8 0x7fff8000]
       [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap); (SP + -480, 480)]
  |
  kx_runFLd [0x8c4f8; 0x8c4e8; 0x8c69c] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 6 7; KZRange (off - b / 8) 0 7; KZRange b 48 55; KZRange (b / 8) 6 6; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]; KZAlign SP 16; KZWord 0xba2f8 8 0x7fff8000]
       [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap); (SP + -480, 480)]
  |
  kx_runFLd [0x8c4f8; 0x8c4e8; 0x8c69c] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 7 7; KZRange (off - b / 8) 0 7; KZRange b 56 63; KZRange (b / 8) 7 7; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]; KZAlign SP 16; KZWord 0xba2f8 8 0x7fff8000]
       [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap); (SP + -480, 480)]
  ].
  all: try w4br6 b.
  all: try w4br5.
  all: try w4br.
  all: try w4word4.
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; w4_norm_to (DST + 3 * seg + q) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -224, SP + -184)] mm) as MUW;
      pose proof (wmono_refl bsegs mm) as WMr;
      kx_munch_wins MUW [(SP + -224, 40)];
      kx_post_mem_free end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (?A + -224) _ |- _ => kx_cells_split H end end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_cells_post; w4_c4fix end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (_ + -224) [C8 (Z_to_bv 64 ?X)] |- _ =>
        rewrite <- (Z_to_bv_mod64 X) in H end; idtac end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?log) _) =>
      eapply (KK _ (replay E log DST ob)) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -224) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- u8arr _ _ _ _ => apply kx_u8arr_replay; eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- 0 <= _ mod 2 ^ 64 < 2 ^ 64 => apply Z.mod_pos_bound; lia end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4_bnd; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => eassumption end).
Time Qed.

Definition w4s34_ecb_case2 : Prop :=
  forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 w0 w8 w16 w40 w48 w56 : word) (pad1 : list byte) (bs cbs ob : list byte)
    (SP DST dcap seg q DT dl S off b c tl rsv len : Z),
  rw_cells bsegs mm (SP + -480) [C8 w0; C8 w8; C8 w16; C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 seg); C8 w40; C8 w48; C8 w56;
            C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + 2 * seg));
            C8 (Z_to_bv 64 (DST + dcap))] ->
  rw_cells bsegs mm (SP + -224) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 pad1; C8 (Z_to_bv 64 (S + off)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))] ->
  bytes_at bsegs mm S bs -> Z.of_nat (length bs) = len ->
  bytes_at bsegs mm (DT + 4) cbs -> Z.of_nat (length cbs) = 2 * 2^tl -> 2 <= 2^tl <= 4096 ->
  u8arr bsegs mm DST ob -> Z.of_nat (length ob) = dcap ->
  unpoisoned mm S (S + len) -> unpoisoned mm (DT + 4) (DT + 4 + 2 * 2^tl) -> unpoisoned mm DST (DST + dcap) ->
  rng RNG S len -> rng RNG (DT + 4) (2 * 2^tl) -> rng RNG DST dcap ->
  forall (A1 L1 A2 L2 A3 L3 : Z), A1 mod 8 = 0 -> A2 mod 8 = 0 -> A3 mod 8 = 0 -> 0 <= A1 -> 0 <= A2 -> 0 <= A3 ->
  A1 <= S -> S + len <= A1 + L1 -> A2 <= DT + 4 -> DT + 4 + 2 * 2^tl <= A2 + L2 -> A3 <= DST -> DST + dcap <= A3 + L3 ->
  rng RNG (shad A1) (shlen (L1 + 7)) -> rng RNG (shad A2) (shlen (L2 + 7)) -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart S len (SP + -480) 480 -> KXGoM.apart DST dcap (SP + -480) 480 -> KXGoM.apart DST dcap S len ->
  KXGoM.apart (DT + 4) (2 * 2^tl) (SP + -480) 480 -> KXGoM.apart DST dcap (DT + 4) (2 * 2^tl) -> KXGoM.apart DST dcap 0x7fff8000 (2^44) -> KXGoM.apart DST dcap 2147450880 (2^44) -> DST + dcap <= 2^47 -> DT + 4 + 2 * 2^tl <= 2^47 ->
  mem_inv bsegs mm -> rng RNG (SP + -480) 480 ->
  rw_cells bsegs mm 0xba2f8 [C8 (Z_to_bv 64 0x7fff8000)] ->
  unpoisoned mm (SP + -480) SP -> SP mod 16 = 0 -> rng RNG (shad (SP + -480)) (shlen (480 + 7)) ->
  4096 <= DST <= 2^47 -> 1 <= dcap <= 2^32 -> 0 <= seg <= dcap -> 0 <= q -> 3 * seg + q <= dcap -> dcap - 3 * seg - q <= 3 -> 3 * seg + q <= dcap ->
  0x10007fff8000 + 2720 <= SP <= 2^47 -> 4096 <= S -> S + len <= 2^47 -> 1 <= off <= 7 -> b <= 64 -> off < b / 8 -> off + 8 <= len -> len <= 2^32 -> 0 <= b < 2^31 -> 4096 <= DT <= 2^47 ->
  1 <= tl <= 12 -> 0 <= rsv <= 255 -> dl = tl + 256 * rsv -> 0 <= c < 2^64 ->
  ztab_fact bsegs mm (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)] ->
  (forall (mm' : amem) (ob' : list byte) (c' b' : Z) (wp ws we : word)
          (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 : word),
     munch [(DST, DST + dcap); (SP + -224, SP + -184)] mm mm' -> wmono bsegs mm mm' -> mem_inv bsegs mm' ->
     u8arr bsegs mm' DST ob' -> Z.of_nat (length ob') = dcap ->
     rw_cells bsegs mm' (SP + -224) [C8 (Z_to_bv 64 c'); C4 (Z_to_bv 64 b'); CB 4 pad1; C8 wp; C8 ws; C8 we] ->
     0 <= c' < 2^64 -> 0 <= b' < 2^32 ->
     evtF bsegs RNG Q
        (MS (mkR y1 (Z_to_bv 64 (SP + -480)) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13
                 y14 y15 y16 y17 y18
                 (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) y22 y23
                 (Z_to_bv 64 0x7fff8000) y25 (Z_to_bv 64 (DT + 4)) y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x8c4f8) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -480)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (dcap - 3 * seg - q)) (Z_to_bv 64 b) (Z_to_bv 64 4) x13
               x14 x15 x16 x17 x18
               (Z_to_bv 64 dl) (Z_to_bv 64 (DST + 3 * seg + q)) (Z_to_bv 64 4611686018427387904) x22 x23
               (Z_to_bv 64 0x7fff8000) x25 (Z_to_bv 64 (DT + 4)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8c3ec) fc None mm (seg_rom bsegs)).

Theorem w4s34_ecb : w4s34_ecb_case2.
Proof.
  unfold w4s34_ecb_case2.
  intros.
  assert (HBND : 16 <= b <= 23 \/ 24 <= b <= 31 \/ 32 <= b <= 39 \/ 40 <= b <= 47 \/ 48 <= b <= 55 \/ 56 <= b <= 63 \/ 64 <= b <= 64) by (Z.div_mod_to_equations; lia).
  destruct HBND as [HB|[HB|[HB|[HB|[HB|[HB|HB]]]]]]; [
  kx_runFLd [0x8c4f8; 0x8c4e8; 0x8c69c] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 1 1; KZRange (b / 8 - off) 1 8; KZRange b 16 23; KZRange (b / 8) 2 2; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]; KZAlign SP 16; KZWord 0xba2f8 8 0x7fff8000]
       [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap); (SP + -480, 480)]
  |
  kx_runFLd [0x8c4f8; 0x8c4e8; 0x8c69c] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 1 2; KZRange (b / 8 - off) 1 8; KZRange b 24 31; KZRange (b / 8) 3 3; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]; KZAlign SP 16; KZWord 0xba2f8 8 0x7fff8000]
       [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap); (SP + -480, 480)]
  |
  kx_runFLd [0x8c4f8; 0x8c4e8; 0x8c69c] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 1 3; KZRange (b / 8 - off) 1 8; KZRange b 32 39; KZRange (b / 8) 4 4; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]; KZAlign SP 16; KZWord 0xba2f8 8 0x7fff8000]
       [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap); (SP + -480, 480)]
  |
  kx_runFLd [0x8c4f8; 0x8c4e8; 0x8c69c] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 1 4; KZRange (b / 8 - off) 1 8; KZRange b 40 47; KZRange (b / 8) 5 5; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]; KZAlign SP 16; KZWord 0xba2f8 8 0x7fff8000]
       [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap); (SP + -480, 480)]
  |
  kx_runFLd [0x8c4f8; 0x8c4e8; 0x8c69c] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 1 5; KZRange (b / 8 - off) 1 8; KZRange b 48 55; KZRange (b / 8) 6 6; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]; KZAlign SP 16; KZWord 0xba2f8 8 0x7fff8000]
       [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap); (SP + -480, 480)]
  |
  kx_runFLd [0x8c4f8; 0x8c4e8; 0x8c69c] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 1 6; KZRange (b / 8 - off) 1 8; KZRange b 56 63; KZRange (b / 8) 7 7; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]; KZAlign SP 16; KZWord 0xba2f8 8 0x7fff8000]
       [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap); (SP + -480, 480)]
  |
  kx_runFLd [0x8c4f8; 0x8c4e8; 0x8c69c] 400%nat (repeat false 64)
      [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 1 (2^32); KZRange seg 0 (2^32); KZRange q 0 (2^32); KZRange SP (0x10007fff8000 + 2720) (2^47);
       KZRange S 4096 (2^47); KZRange (S + len) 4096 (2^47); KZRange off 1 7; KZRange (b / 8 - off) 1 8; KZRange b 64 64; KZRange (b / 8) 8 8; KZRange DT 4096 (2^47); KZRange tl 1 12; KZRange rsv 0 255;
       KZRange c 0 (2^64 - 1); KZRange len 9 (2^32); KZRange (len - off) 8 (2^32);
       KZRange (dcap - 3 * seg - q) 0 3;
       KZWord (SP + -224) 8 c; KZWord (SP + -216) 4 b; KZWord (SP + -208) 8 (S + off); KZWord (SP + -200) 8 S; KZWord (SP + -192) 8 (S + 8);
       KZWord (SP + -456) 8 (DST + dcap - 3); KZWr (SP + -224) 40; KZWr DST dcap;
       KZDisj S len (SP + -480) 480; KZDisj DST dcap (SP + -480) 480; KZDisj DST dcap S len;
       KZDisj (DT + 4) (2 * 2^tl) (SP + -480) 480; KZDisj DST dcap (DT + 4) (2 * 2^tl);
       KZTab (DT + 4) (2 * 2^tl) 2 [(0, 0, 12)]; KZAlign SP 16; KZWord 0xba2f8 8 0x7fff8000]
       [(S, len); (DT + 4, 2 * 2^tl)] [(SP + -480, 480); (DST, dcap); (S, len); (DT + 4, 2 * 2^tl)] [(S, len); (DT + 4, 2 * 2^tl); (DST, dcap); (SP + -480, 480)]
  ].
  all: try w4br6 b.
  all: try w4br5.
  all: try w4br.
  all: try w4word4.
  all: try w4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; w4_norm_to (DST + 3 * seg + q) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; vm_compute; reflexivity) end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      pose proof (munch_refl [(DST, DST + dcap); (SP + -224, SP + -184)] mm) as MUW;
      pose proof (wmono_refl bsegs mm) as WMr;
      kx_munch_wins MUW [(SP + -224, 40)];
      kx_post_mem_free end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (?A + -224) _ |- _ => kx_cells_split H end end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_cells_post; w4_c4fix end).
  all: try (lazymatch goal with |- evtF _ _ _ _ =>
      match goal with H : rw_cells _ _ (_ + -224) [C8 (Z_to_bv 64 ?X)] |- _ =>
        rewrite <- (Z_to_bv_mod64 X) in H end; idtac end).
  all: try (lazymatch goal with KK : forall mm' : amem, _ |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E ?m ?log) _) =>
      eapply (KK _ (replay E log DST ob)) end).
  all: try (lazymatch goal with |- rw_cells _ _ (_ + -224) _ => kx_cells_merge end).
  all: try (lazymatch goal with |- _ \/ _ => unfold KXGoM.apart in *; cbn [cells_size csize length] in *; rewrite ?length_map in *; lia end).
  all: try (lazymatch goal with |- u8arr _ _ _ _ => apply kx_u8arr_replay; eassumption end).
  all: try (lazymatch goal with |- Z.of_nat (length (replay _ _ _ _)) = _ => rewrite replay_length; assumption end).
  all: try (lazymatch goal with |- 0 <= _ mod 2 ^ 64 < 2 ^ 64 => apply Z.mod_pos_bound; lia end).
  all: try (lazymatch goal with |- 0 <= _ < 2 ^ 32 => w4_bnd; lia end).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => eassumption end).
Time Qed.

End CANSEC1.








