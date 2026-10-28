(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4s_iface AF_huf_z4s3_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_reloadi.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXCell KXCell2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_reloadi AF_huf_z4s3b.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Lemma z4s34_E : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w10 w11 : word) (jp : list byte)
    (SP DST dcap SS DT q O L pt b cz tl mtl : Z),
  rw_cells bsegs mm (SP + -384) [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7));
        C8 w4; C8 w5; C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
        C8 (Z_to_bv 64 dcap)] ->
  rw_cells bsegs mm (SP + -264) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O -> 1 <= L < 2^26 -> 0 <= pt <= L -> 0 <= b < 2^31 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> tl <= mtl -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> O <= 2^26 ->
  (dcap - q < 8 -> forall mm',
      rw_cells bsegs mm' (SP + -384) [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7));
        C8 w4; C8 w5; C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
        C8 (Z_to_bv 64 dcap)] ->
      rw_cells bsegs mm' (SP + -264) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -264, SP + -224)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dcap - q)) (Z_to_bv 64 8) x12 x13 x14 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
               (Z_to_bv 64 (DT + 4)) x31) F (Z_to_bv 64 0x93984) fc None mm' (seg_rom bsegs))) ->
  (8 <= dcap - q -> 12 <= tl -> forall mm',
      rw_cells bsegs mm' (SP + -384) [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7));
        C8 w4; C8 w5; C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
        C8 (Z_to_bv 64 dcap)] ->
      rw_cells bsegs mm' (SP + -264) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -264, SP + -224)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 12) (Z_to_bv 64 tl) x12 x13 x14 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
               (Z_to_bv 64 (DT + 4)) x31) F (Z_to_bv 64 0x93aa4) fc None mm' (seg_rom bsegs))) ->
  (8 <= dcap - q -> tl < 12 -> b <= 64 -> forall mm',
      rw_cells bsegs mm' (SP + -384) [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7));
        C8 w4; C8 w5; C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
        C8 (Z_to_bv 64 dcap)] ->
      rw_cells bsegs mm' (SP + -264) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -264, SP + -224)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (- tl + -256 * mtl)) (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 64) (Z_to_bv 64 (DST + dcap + -9)) (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 AZ4_SB) x22 (Z_to_bv 64 (- DT + -5)) x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
               (Z_to_bv 64 (DT + 4)) x31) F (Z_to_bv 64 0x9333c) fc None mm' (seg_rom bsegs))) ->
  (8 <= dcap - q -> tl < 12 -> 64 < b -> forall mm',
      rw_cells bsegs mm' (SP + -384) [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7));
        C8 w4; C8 w5; C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
        C8 (Z_to_bv 64 dcap)] ->
      rw_cells bsegs mm' (SP + -264) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 0x20e00);
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -264, SP + -224)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 0x20e00) (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 64) x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
               (Z_to_bv 64 (DT + 4)) x31) F (Z_to_bv 64 0x94028) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 (Z_to_bv 64 (DST + q)) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
               (Z_to_bv 64 (DT + 4)) x31) F (Z_to_bv 64 AZ4_S4) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w10 w11 jp SP DST dcap SS DT q O L pt b cz tl mtl
    SPL BD MI RS HD HDE HDC HQ HS HSE HO HL HPT HB HCZ HTL HMT HTM HDT HSP HO2 K1 K2 K3 K4.
  unfold AZ4_S4, AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -264, SP + -224)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  destruct (Z_lt_ge_dec (dcap - q) 8) as [C1|C1]; [|destruct (Z_lt_ge_dec tl 12) as [C2|C2]; [destruct (Z_le_gt_dec b 64) as [C3|C3]|]].
  4: kx_runFmd [0x9333c; 0x93984; 0x93aa4; 0x94028; 0x8fbec] 60%nat [false; true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 (2^26); KZRange b 0 (2^31 - 1); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -288) 8 tl; KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -264) 8 cz; KZWord (SP + -256) 4 b; KZWord (SP + -248) 8 (SS + O + pt); KZWord (SP + -240) 8 (SS + O);
     KZWord (SP + -232) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -264) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  3: kx_runFmd [0x9333c; 0x93984; 0x93aa4; 0x94028; 0x8fbec] 60%nat [false; false; false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 (2^26); KZRange b 0 (2^31 - 1); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -288) 8 tl; KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -264) 8 cz; KZWord (SP + -256) 4 b; KZWord (SP + -248) 8 (SS + O + pt); KZWord (SP + -240) 8 (SS + O);
     KZWord (SP + -232) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -264) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  2: kx_runFmd [0x9333c; 0x93984; 0x93aa4; 0x94028; 0x8fbec] 60%nat [false; false; true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 (2^26); KZRange b 0 (2^31 - 1); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -288) 8 tl; KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -264) 8 cz; KZWord (SP + -256) 4 b; KZWord (SP + -248) 8 (SS + O + pt); KZWord (SP + -240) 8 (SS + O);
     KZWord (SP + -232) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -264) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [0x9333c; 0x93984; 0x93aa4; 0x94028; 0x8fbec] 60%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 (2^26); KZRange b 0 (2^31 - 1); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -288) 8 tl; KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -264) 8 cz; KZWord (SP + -256) 4 b; KZWord (SP + -248) 8 (SS + O + pt); KZWord (SP + -240) 8 (SS + O);
     KZWord (SP + -232) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -264) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4brdl.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: rewrite ?z4_eext in *.
  all: repeat (lazymatch goal with |- context [edenot ?E ?e] =>
         let b := eval unfold E in E in lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
         rewrite ?(ez_ok zv E (kE_atoms zv xs) e); let na := eval vm_compute in (length zv) in
         cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb] end end).
  all: rewrite ?z4_dl_b0 in * by lia.
  all: rewrite ?Z_to_bv_bv_unsigned in *.
  all: repeat match goal with H : rw_cells _ _ _ [C8 (ext_val false 0 1 (edenot ?E ?e))] |- _ =>
         let b := eval unfold E in E in lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
         rewrite (ez_ok zv E (kE_atoms zv xs) e) in H; let na := eval vm_compute in (length zv) in
         cbv [ez] in H; change (length zv) with na in H; cbv [nth Nat.ltb Nat.leb] in H; rewrite z4_dl_b0 in H by lia end end.
  4: (eapply K2; [lia | lia | kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
  3: (eapply K4; [lia | lia | lia | kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
  2: z4_m64.
  2: (eapply K3; [lia | lia | lia | kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
  1: (eapply K1; [lia | kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Notation Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT :=
  [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7)); C8 w4; C8 w5;
   C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
   C8 (Z_to_bv 64 dcap)] (only parsing).

Lemma z4s34_R5A : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x14 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w10 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q O L pt qb b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
  rw_cells bsegs mm (SP + -264) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  1 <= pt <= 7 -> pt + 8 <= L -> 0 <= qb <= 8 -> qb <= pt -> 8 * qb <= b <= 8 * qb + 7 -> SS + O + L + 400 <= SP ->
  (forall mm' (c' : word) (z11 z12 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
      rw_cells bsegs mm' (SP + -264) [C8 c'; C4 (Z_to_bv 64 (b - 8 * qb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + (pt - qb)));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -264, SP + -224)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) z11 z12 z13 z14 z15 z16 z17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x9345c) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b)
           (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) x14 (Z_to_bv 64 qb) x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB)
           x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x93354) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x14 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w10 w11 jp sb SP DST dcap SS DT q O L pt qb b cz tl mtl A1 L1
    SPL BD4 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HS HSE HO HL HCZ HTL HMT HDT HSP
    HPT HPL HQB HPQ HBQ HSS KA.
  unfold AZ4_SB in *.
  assert (HP2 : exists p2, pt = p2 + qb /\ 0 <= p2 <= 7) by (exists (pt - qb); lia).
  destruct HP2 as (p2 & -> & HP2). rewrite Z.add_simpl_r in KA.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -264, SP + -224)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x9345c] 80%nat [true; true; false; false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange p2 0 7; KZRange qb 0 8; KZRange (p2 + qb) 1 7; KZRange b 0 64; KZRange (b - 8 * qb) 0 7;
     KZRange (L - p2) 8 (2^26); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -288) 8 tl; KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -264) 8 cz; KZWord (SP + -256) 4 b; KZWord (SP + -248) 8 (SS + O + (p2 + qb)); KZWord (SP + -240) 8 (SS + O);
     KZWord (SP + -232) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -264) 40; KZDisj (SS + O) L (SP + -400) 400]
     [(SS + O, L)] [(SP + -400, 400); (SS + O, L)] [(SS + O, L)].
  all: try z4word4.
  all: try z4brx.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD4; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: try replace (b + -8 * qb) with (b - 8 * qb) in * by lia.
  all: try rewrite (Z.add_assoc _ O p2) in *.
  all: (eapply KA; [kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Lemma z4s34_R5B : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x14 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w10 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q O L pt qb b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
  rw_cells bsegs mm (SP + -264) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  1 <= pt <= 7 -> pt < qb <= 8 -> pt + 8 <= L -> 8 * qb <= b <= 8 * qb + 7 -> b <= 64 ->
  SS + O + L + 400 <= SP ->
  (forall mm' (c' : word) (z11 z12 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
      rw_cells bsegs mm' (SP + -264) [C8 c'; C4 (Z_to_bv 64 (b - 8 * pt)); CB 4 jp; C8 (Z_to_bv 64 (SS + O));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -264, SP + -224)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) z11 z12 z13 z14 z15 z16 z17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x9345c) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b)
           (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) x14 (Z_to_bv 64 qb) x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB)
           x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x93354) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x14 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w10 w11 jp sb SP DST dcap SS DT q O L pt qb b cz tl mtl A1 L1
    SPL BD4 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HS HSE HO HL HCZ HTL HMT HDT HSP
    HPT HPQ HPL HBQ HB6 HSS KB.
  unfold AZ4_SB in *.
  assert (HD2 : exists d, qb = pt + d /\ 1 <= d <= 7) by (exists (qb - pt); lia).
  destruct HD2 as (d & -> & HDD).
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -264, SP + -224)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x9345c] 80%nat [true; true; false; false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 9 (2^26); KZRange pt 1 7; KZRange d 1 7; KZRange (pt + d) 2 8; KZRange b 0 64;
     KZRange (b - 8 * (pt + d)) 0 7; KZRange (b - 8 * pt) 8 63; KZRange (L - pt) 8 (2^26); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -288) 8 tl; KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -264) 8 cz; KZWord (SP + -256) 4 b; KZWord (SP + -248) 8 (SS + O + pt); KZWord (SP + -240) 8 (SS + O);
     KZWord (SP + -232) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -264) 40; KZDisj (SS + O) L (SP + -400) 400]
     [(SS + O, L)] [(SP + -400, 400); (SS + O, L)] [(SS + O, L)].
  all: try z4word4.
  all: try z4brx.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD4; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: try replace (b + -8 * pt) with (b - 8 * pt) in * by lia.
  all: (eapply KB; [kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Lemma z4s34_H5 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w10 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q O L pt b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
  rw_cells bsegs mm (SP + -264) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  0 <= pt -> (pt = 0 \/ pt + 8 <= L) -> 0 <= b <= 64 -> SS + O + L + 400 <= SP ->
  (8 <= pt -> forall z12 : word,
      evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 0x93454) (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (SP + -264))
               (Z_to_bv 64 b) z12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 AHUF_RELOADI) fc None mm (seg_rom bsegs))) ->
  (pt = 0 -> forall z10 z12 z13 : word,
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 b) z12 z13 x14 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x94028) fc None mm (seg_rom bsegs))) ->
  (1 <= pt <= 7 -> b / 8 <= pt -> forall mm' (c' : word) (z11 z12 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
      rw_cells bsegs mm' (SP + -264) [C8 c'; C4 (Z_to_bv 64 (b - 8 * (b / 8))); CB 4 jp; C8 (Z_to_bv 64 (SS + O + (pt - b / 8)));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -264, SP + -224)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) z11 z12 z13 z14 z15 z16 z17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x9345c) fc None mm' (seg_rom bsegs))) ->
  (1 <= pt <= 7 -> pt < b / 8 -> forall mm' (c' : word) (z11 z12 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
      rw_cells bsegs mm' (SP + -264) [C8 c'; C4 (Z_to_bv 64 (b - 8 * pt)); CB 4 jp; C8 (Z_to_bv 64 (SS + O));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -264, SP + -224)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) z11 z12 z13 z14 z15 z16 z17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x9345c) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
           x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x9333c) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w10 w11 jp sb SP DST dcap SS DT q O L pt b cz tl mtl A1 L1
    SPL BD4 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HS HSE HO HL HCZ HTL HMT HDT HSP
    HP0 HPL HB HSS KC KZ KA KB.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -264, SP + -224)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  destruct (Z_lt_ge_dec pt 8) as [P7|P8]; [destruct (Z.eq_dec pt 0) as [P0|P1]|].
  3: kx_runFmd [AHUF_RELOADI; 0x94028; 0x93354] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 8 (2^26); KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -264) 8 cz; KZWord (SP + -256) 4 b; KZWord (SP + -248) 8 (SS + O + pt); KZWord (SP + -240) 8 (SS + O);
     KZWord (SP + -232) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -264) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  2: kx_runFmd [AHUF_RELOADI; 0x94028; 0x93354] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 1 7; KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -264) 8 cz; KZWord (SP + -256) 4 b; KZWord (SP + -248) 8 (SS + O + pt); KZWord (SP + -240) 8 (SS + O);
     KZWord (SP + -232) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -264) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [AHUF_RELOADI; 0x94028; 0x93354] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 0; KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -264) 8 cz; KZWord (SP + -256) 4 b; KZWord (SP + -248) 8 (SS + O + pt); KZWord (SP + -240) 8 (SS + O);
     KZWord (SP + -232) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -264) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD4; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: cbn [mem_denot] in *.
  3: (apply KC; lia).
  2: { lazymatch goal with |- context [edenot ?E (EAluw ALU_SRL ?e (ELit 3))] =>
         rewrite (z4_srlw3 E e b) by (first [reflexivity | lia | (z4ez; reflexivity)]) end.
       rewrite (Z.add_assoc _ O pt).
       assert (HB8 : 0 <= b / 8 <= 8 /\ 8 * (b / 8) <= b <= 8 * (b / 8) + 7) by (clear - HB; Z.div_mod_to_equations; lia).
       destruct (Z_le_gt_dec (b / 8) pt) as [Q1|Q1].
       - eapply z4s34_R5A with (qb := b / 8) (DST := DST) (dcap := dcap) (DT := DT) (q := q) (cz := cz)
           (tl := tl) (mtl := mtl) (w0 := w0) (w1 := w1) (w4 := w4) (w5 := w5) (w7 := w7) (w8 := w8) (w9 := w9) (w10 := w10)
           (w11 := w11) (jp := jp) (sb := sb) (A1 := A1) (L1 := L1).
         all: try (lazymatch goal with |- rw_cells _ _ _ _ => kx_cells_merge end).
         all: try eassumption. all: try lia.
         all: exact (KA ltac:(lia) Q1).
       - eapply z4s34_R5B with (qb := b / 8) (DST := DST) (dcap := dcap) (DT := DT) (q := q) (cz := cz)
           (tl := tl) (mtl := mtl) (w0 := w0) (w1 := w1) (w4 := w4) (w5 := w5) (w7 := w7) (w8 := w8) (w9 := w9) (w10 := w10)
           (w11 := w11) (jp := jp) (sb := sb) (A1 := A1) (L1 := L1).
         all: try (lazymatch goal with |- rw_cells _ _ _ _ => kx_cells_merge end).
         all: try eassumption. all: try lia.
         all: exact (KB ltac:(lia) ltac:(lia)). }
  1: (apply (KZ P0)).
Qed.

Lemma z4s34_J : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w10 w11 c p s l : word) (jp : list byte)
    (SP DST dcap DT q b tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
  rw_cells bsegs mm (SP + -264) [C8 c; C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= dcap -> 0 <= b < 2^31 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (dcap - q < 2 ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 (Z_to_bv 64 (DST + q)) (Z_to_bv 64 (dcap - q)) (Z_to_bv 64 2) x12 x13 x14 x15 x16 x17
            x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
        F (Z_to_bv 64 0x942a4) fc None mm (seg_rom bsegs))) ->
  (2 <= dcap - q -> b <= 64 -> forall z10 : word,
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) z10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
        F (Z_to_bv 64 0x9405c) fc None mm (seg_rom bsegs))) ->
  (2 <= dcap - q -> 64 < b -> forall z10 : word,
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) z10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
        F (Z_to_bv 64 0x94294) fc None mm (seg_rom bsegs))) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 (Z_to_bv 64 (DST + q)) x10 x11 x12 x13 x14 x15 x16 x17
            x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
        F (Z_to_bv 64 0x94028) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w10 w11 c p s l jp SP DST dcap DT q b tl mtl
    SPL BD4 MI RS HD HDE HDC HQ HB HTL HMT HDT HSP K1 K2 K3.
  unfold AZ4_SB in *.
  destruct (Z_lt_ge_dec (dcap - q) 2) as [C1|C1]; [|destruct (Z_le_gt_dec b 64) as [C2|C2]].
  3: kx_runFmd [0x9405c; 0x942a4; 0x94294; 0x8fbec] 40%nat [false; true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange b 0 (2^31 - 1);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -280) 8 (DT + 4);
      KZWord (SP + -256) 4 b; KZWr (SP + -384) 120; KZWr (SP + -264) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  2: kx_runFmd [0x9405c; 0x942a4; 0x94294; 0x8fbec] 40%nat [false; false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange b 0 (2^31 - 1);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -280) 8 (DT + 4);
      KZWord (SP + -256) 4 b; KZWr (SP + -384) 120; KZWr (SP + -264) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [0x9405c; 0x942a4; 0x94294; 0x8fbec] 40%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange b 0 (2^31 - 1);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -280) 8 (DT + 4);
      KZWord (SP + -256) 4 b; KZWr (SP + -384) 120; KZWr (SP + -264) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4brdl.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD4; kx_cells_post.
  all: kx_post_mem_free.
  all: z4post_ez.
  all: cbn [mem_denot] in *.
  3: z4_m64.
  3: (eapply K3; lia).
  2: z4_m64.
  2: (eapply K2; lia).
  1: (apply K1; lia).
Qed.

Lemma z4_br_nzf : forall E P B,
  bv_unsigned (edenot E B) <= 64 -> 64 < bv_unsigned (edenot E P) ->
  branch_taken BC_EQ
    (edenot E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR P B) (ELit 1))))
    (edenot E (ELit 0)) = false.
Proof.
  intros E P B HB HP.
  pose proof (bv_unsigned_in_range _ (edenot E B)) as [RB _].
  cbn [edenot branch_taken].
  rewrite bv_eqb_Z, u_xor64, u_sltu64, u_xor64.
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  assert (HL : 0 < Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B))).
  { assert (0 <= Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B))).
    { apply Z.lxor_nonneg; split; intros; lia. }
    assert (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B)) <> 0).
    { intros H0. pose proof (Z.lxor_eq _ _ H0). lia. }
    lia. }
  destruct (Z.ltb_spec (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B))) 1); [lia|].
  reflexivity.
Qed.

Ltac z4brxf :=
  lazymatch goal with
  | |- branch_taken BC_EQ (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR ?P ?B) (ELit 1))))
         (edenot ?E (ELit 0)) = false =>
      apply (z4_br_nzf E P B); z4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; lia
  end.

Lemma z4s34_R2A : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x14 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w10 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q O L pt qb b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
  rw_cells bsegs mm (SP + -264) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  1 <= pt <= 7 -> pt + 8 <= L -> 0 <= qb <= 8 -> qb <= pt -> 8 * qb <= b <= 8 * qb + 7 -> SS + O + L + 400 <= SP ->
  (forall mm' (c' : word) (z11 z12 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
      rw_cells bsegs mm' (SP + -264) [C8 c'; C4 (Z_to_bv 64 (b - 8 * qb)); CB 4 jp; C8 (Z_to_bv 64 (SS + O + (pt - qb)));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -264, SP + -224)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) z11 z12 z13 z14 z15 z16 z17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x9416c) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b)
           (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) x14 (Z_to_bv 64 qb) x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB)
           x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x94074) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x14 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w10 w11 jp sb SP DST dcap SS DT q O L pt qb b cz tl mtl A1 L1
    SPL BD4 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HS HSE HO HL HCZ HTL HMT HDT HSP
    HPT HPL HQB HPQ HBQ HSS KA.
  unfold AZ4_SB in *.
  assert (HP2 : exists p2, pt = p2 + qb /\ 0 <= p2 <= 7) by (exists (pt - qb); lia).
  destruct HP2 as (p2 & -> & HP2). rewrite Z.add_simpl_r in KA.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -264, SP + -224)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x9416c] 80%nat [false; false; false; false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange p2 0 7; KZRange qb 0 8; KZRange (p2 + qb) 1 7; KZRange b 0 64; KZRange (b - 8 * qb) 0 7;
     KZRange (L - p2) 8 (2^26); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -288) 8 tl; KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -264) 8 cz; KZWord (SP + -256) 4 b; KZWord (SP + -248) 8 (SS + O + (p2 + qb)); KZWord (SP + -240) 8 (SS + O);
     KZWord (SP + -232) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -264) 40; KZDisj (SS + O) L (SP + -400) 400]
     [(SS + O, L)] [(SP + -400, 400); (SS + O, L)] [(SS + O, L)].
  all: try z4word4.
  all: try z4brxf.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD4; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: try replace (b + -8 * qb) with (b - 8 * qb) in * by lia.
  all: try rewrite (Z.add_assoc _ O p2) in *.
  all: (eapply KA; [kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Lemma z4s34_R2B : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x14 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w10 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q O L pt qb b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
  rw_cells bsegs mm (SP + -264) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  1 <= pt <= 7 -> pt < qb <= 8 -> pt + 8 <= L -> 8 * qb <= b <= 8 * qb + 7 -> b <= 64 ->
  SS + O + L + 400 <= SP ->
  (forall mm' (c' : word) (z11 z12 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
      rw_cells bsegs mm' (SP + -264) [C8 c'; C4 (Z_to_bv 64 (b - 8 * pt)); CB 4 jp; C8 (Z_to_bv 64 (SS + O));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -264, SP + -224)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) z11 z12 z13 z14 z15 z16 z17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x9416c) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b)
           (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) x14 (Z_to_bv 64 qb) x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB)
           x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x94074) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x14 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w10 w11 jp sb SP DST dcap SS DT q O L pt qb b cz tl mtl A1 L1
    SPL BD4 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HS HSE HO HL HCZ HTL HMT HDT HSP
    HPT HPQ HPL HBQ HB6 HSS KB.
  unfold AZ4_SB in *.
  assert (HD2 : exists d, qb = pt + d /\ 1 <= d <= 7) by (exists (qb - pt); lia).
  destruct HD2 as (d & -> & HDD).
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -264, SP + -224)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  kx_runFmd [0x9416c] 80%nat [false; false; false; false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 9 (2^26); KZRange pt 1 7; KZRange d 1 7; KZRange (pt + d) 2 8; KZRange b 0 64;
     KZRange (b - 8 * (pt + d)) 0 7; KZRange (b - 8 * pt) 8 63; KZRange (L - pt) 8 (2^26); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -288) 8 tl; KZWord (SP + -360) 8 (DST + dcap - 7);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -264) 8 cz; KZWord (SP + -256) 4 b; KZWord (SP + -248) 8 (SS + O + pt); KZWord (SP + -240) 8 (SS + O);
     KZWord (SP + -232) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -264) 40; KZDisj (SS + O) L (SP + -400) 400]
     [(SS + O, L)] [(SP + -400, 400); (SS + O, L)] [(SS + O, L)].
  all: try z4word4.
  all: try z4brxf.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD4; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: try replace (b + -8 * pt) with (b - 8 * pt) in * by lia.
  all: (eapply KB; [kx_cells_merge | kx_cells_merge | eassumption | eassumption | eassumption]).
Qed.

Lemma z4s34_H2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w10 w11 : word) (jp : list byte) (sb : list Z)
    (SP DST dcap SS DT q O L pt b cz tl mtl A1 L1 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
  rw_cells bsegs mm (SP + -264) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) sb) -> zlen sb = L -> unpoisoned mm (SS + O) (SS + O + L) ->
  rng RNG (SS + O) L -> A1 mod 8 = 0 -> 0 <= A1 -> A1 <= SS + O -> SS + O + L <= A1 + L1 -> rng RNG (shad A1) (shlen (L1 + 7)) ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O <= 2^26 -> 1 <= L < 2^26 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  0 <= pt -> (pt = 0 \/ pt + 8 <= L) -> 0 <= b <= 64 -> SS + O + L + 400 <= SP ->
  (8 <= pt -> forall z12 : word,
      evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 0x94160) (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (SP + -264))
               (Z_to_bv 64 b) z12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 AHUF_RELOADI) fc None mm (seg_rom bsegs))) ->
  (pt = 0 -> forall z10 z12 z13 : word,
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 z10 (Z_to_bv 64 b) z12 z13 x14 x15 x16 x17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x942a0) fc None mm (seg_rom bsegs))) ->
  (1 <= pt <= 7 -> b / 8 <= pt -> forall mm' (c' : word) (z11 z12 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
      rw_cells bsegs mm' (SP + -264) [C8 c'; C4 (Z_to_bv 64 (b - 8 * (b / 8))); CB 4 jp; C8 (Z_to_bv 64 (SS + O + (pt - b / 8)));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -264, SP + -224)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 1) z11 z12 z13 z14 z15 z16 z17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x9416c) fc None mm' (seg_rom bsegs))) ->
  (1 <= pt <= 7 -> pt < b / 8 -> forall mm' (c' : word) (z11 z12 z13 z14 z15 z16 z17 : word),
      rw_cells bsegs mm' (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
      rw_cells bsegs mm' (SP + -264) [C8 c'; C4 (Z_to_bv 64 (b - 8 * pt)); CB 4 jp; C8 (Z_to_bv 64 (SS + O));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -264, SP + -224)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) z11 z12 z13 z14 z15 z16 z17
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x9416c) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
           x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
       F (Z_to_bv 64 0x9405c) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w10 w11 jp sb SP DST dcap SS DT q O L pt b cz tl mtl A1 L1
    SPL BD4 MI RS SRC SRL SUN SRR HA1 HA2 HA3 HA4 SRS HD HDE HDC HQ HS HSE HO HL HCZ HTL HMT HDT HSP
    HP0 HPL HB HSS KC KZ KA KB.
  unfold AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -264, SP + -224)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  destruct (Z_lt_ge_dec pt 8) as [P7|P8]; [destruct (Z.eq_dec pt 0) as [P0|P1]|].
  3: kx_runFmd [AHUF_RELOADI; 0x942a0; 0x94074] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 8 (2^26); KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -264) 8 cz; KZWord (SP + -256) 4 b; KZWord (SP + -248) 8 (SS + O + pt); KZWord (SP + -240) 8 (SS + O);
     KZWord (SP + -232) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -264) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  2: kx_runFmd [AHUF_RELOADI; 0x942a0; 0x94074] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 1 7; KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -264) 8 cz; KZWord (SP + -256) 4 b; KZWord (SP + -248) 8 (SS + O + pt); KZWord (SP + -240) 8 (SS + O);
     KZWord (SP + -232) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -264) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [AHUF_RELOADI; 0x942a0; 0x94074] 60%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 0; KZRange b 0 64; KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -264) 8 cz; KZWord (SP + -256) 4 b; KZWord (SP + -248) 8 (SS + O + pt); KZWord (SP + -240) 8 (SS + O);
     KZWord (SP + -232) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -264) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD4; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: cbn [mem_denot] in *.
  3: (apply KC; lia).
  2: { lazymatch goal with |- context [edenot ?E (EAluw ALU_SRL ?e (ELit 3))] =>
         rewrite (z4_srlw3 E e b) by (first [reflexivity | lia | (z4ez; reflexivity)]) end.
       rewrite (Z.add_assoc _ O pt).
       assert (HB8 : 0 <= b / 8 <= 8 /\ 8 * (b / 8) <= b <= 8 * (b / 8) + 7) by (clear - HB; Z.div_mod_to_equations; lia).
       destruct (Z_le_gt_dec (b / 8) pt) as [Q1|Q1].
       - eapply z4s34_R2A with (qb := b / 8) (DST := DST) (dcap := dcap) (DT := DT) (q := q) (cz := cz)
           (tl := tl) (mtl := mtl) (w0 := w0) (w1 := w1) (w4 := w4) (w5 := w5) (w7 := w7) (w8 := w8) (w9 := w9) (w10 := w10)
           (w11 := w11) (jp := jp) (sb := sb) (A1 := A1) (L1 := L1).
         all: try (lazymatch goal with |- rw_cells _ _ _ _ => kx_cells_merge end).
         all: try eassumption. all: try lia.
         all: exact (KA ltac:(lia) Q1).
       - eapply z4s34_R2B with (qb := b / 8) (DST := DST) (dcap := dcap) (DT := DT) (q := q) (cz := cz)
           (tl := tl) (mtl := mtl) (w0 := w0) (w1 := w1) (w4 := w4) (w5 := w5) (w7 := w7) (w8 := w8) (w9 := w9) (w10 := w10)
           (w11 := w11) (jp := jp) (sb := sb) (A1 := A1) (L1 := L1).
         all: try (lazymatch goal with |- rw_cells _ _ _ _ => kx_cells_merge end).
         all: try eassumption. all: try lia.
         all: exact (KB ltac:(lia) ltac:(lia)). }
  1: (apply (KZ P0)).
Qed.

Lemma z4_br_tixf : forall E D X Y,
  2^64 - 2^47 <= bv_unsigned (edenot E D) -> 52 <= bv_unsigned (edenot E Y) mod 64 <= 63 ->
  branch_taken BC_LTU (edenot E D) (edenot E (EMd M_MUL (ELit 4) (EAlu ALU_SRL X Y))) = false.
Proof.
  intros E D X Y HD HY.
  assert (RX : bv_unsigned (edenot E X) < 2^64)
    by (pose proof (bv_unsigned_in_range _ (edenot E X)); unfold bv_modulus in *; lia).
  pose proof (bv_unsigned_in_range _ (edenot E X)) as [RX0 _].
  cbn [edenot branch_taken].
  rewrite bv_ltu_Z, u_mul64, u_srl64.
  set (s := bv_unsigned (edenot E Y) mod 64) in *.
  change (bv_unsigned (Z_to_bv 64 4)) with 4.
  assert (HI : bv_unsigned (edenot E X) / 2 ^ s < 2 ^ (64 - s)).
  { apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    rewrite <- Z.pow_add_r by lia. replace (s + (64 - s)) with 64 by lia. exact RX. }
  assert (H12 : 2 ^ (64 - s) <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia).
  assert (HP : 0 <= bv_unsigned (edenot E X) / 2 ^ s) by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
  change (2 ^ 12) with 4096 in H12.
  rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec (bv_unsigned (edenot E D)) (4 * (bv_unsigned (edenot E X) / 2 ^ s))); [lia | reflexivity].
Qed.

Lemma z4_br_shf : forall E K X Y,
  bv_unsigned (edenot E K) = 2^61 -> 52 <= bv_unsigned (edenot E Y) mod 64 <= 63 ->
  branch_taken BC_NE (edenot E (EAlu ALU_SRL (EAlu ALU_ADD K (EAlu ALU_SRL X Y)) (ELit 62))) (edenot E (ELit 0)) = false.
Proof.
  intros E K X Y HK HY.
  pose proof (z4_srl_lt E X Y HY) as HI.
  cbn [edenot branch_taken] in *.
  rewrite bv_eqb_Z, u_srl64, u_add64, HK.
  change (bv_unsigned (Z_to_bv 64 62)) with 62. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  change (62 mod 64) with 62.
  rewrite Z.mod_small by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Ltac z4brtf :=
  lazymatch goal with
  | |- branch_taken BC_LTU (edenot ?E ?D) (edenot ?E (EMd M_MUL (ELit 4) (EAlu ALU_SRL ?X ?Y))) = false =>
      apply (z4_br_tixf E D X Y); z4uzm
  | |- branch_taken BC_NE (edenot ?E (EAlu ALU_SRL (EAlu ALU_ADD ?K (EAlu ALU_SRL ?X ?Y)) (ELit 62))) (edenot ?E (ELit 0)) = false =>
      apply (z4_br_shf E K X Y); z4uzm
  end.

Lemma z4s34_B2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w10 w11 p s l : word) (jp cbs : list byte) (ob : list Z)
    (SP DST dcap DT q b c tl mtl A2 L2 A3 L3 : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
  rw_cells bsegs mm (SP + -264) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  bytes_at bsegs mm (DT + 4) cbs -> zlen cbs = 4 * 2^tl -> unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) -> rng RNG (DT + 4) (4 * 2^tl) ->
  u8arr bsegs mm DST (map (Z_to_bv 8) ob) -> zlen ob = dcap -> unpoisoned mm DST (DST + dcap) -> rng RNG DST dcap ->
  A2 mod 8 = 0 -> 0 <= A2 -> A2 <= DT + 4 -> DT + 4 + 4 * 2^tl <= A2 + L2 -> rng RNG (shad A2) (shlen (L2 + 7)) ->
  A3 mod 8 = 0 -> 0 <= A3 -> A3 <= DST -> DST + dcap <= A3 + L3 -> rng RNG (shad A3) (shlen (L3 + 7)) ->
  KXGoM.apart DST dcap (SP + -400) 400 -> KXGoM.apart (DT + 4) (4 * 2^tl) (SP + -400) 400 ->
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) -> KXGoM.apart DST dcap AZ4_SB (2^44) ->
  ztab_fact bsegs mm (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)] ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q -> q + 2 <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> 0 <= b <= 64 -> 0 <= c < 2^64 ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47 -> 2 <= 2^tl <= 4096 ->
  (forall (mm' : amem) (z10 y12 y13 y14 y15 y16 y17 : word) (nb : Z), 0 <= nb <= 12 -> 1 <= bv_unsigned z10 <= 2 ->
     rw_cells bsegs mm' (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
     rw_cells bsegs mm' (SP + -264) [C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 (b + nb)); CB 4 jp; C8 p; C8 s; C8 l] ->
     mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -264, SP + -224); (DST, DST + dcap)] mm mm' ->
     wmono bsegs mm mm' -> (exists ob', u8arr bsegs mm' DST (map (Z_to_bv 8) ob') /\ zlen ob' = dcap) ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + (q + bv_unsigned z10))) z10 (Z_to_bv 64 (b + nb)) y12 y13
              y14 y15 y16 y17 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
              x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 0x9422c) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 1) x11 x12 x13
           x14 x15 x16 x17 (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22
           x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x9416c) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w10 w11 p s l jp cbs ob SP DST dcap DT q b c tl mtl A2 L2 A3 L3
    SPL BD4 MI RS CB CBL CBU CBR OB OBL OBU OBR HA21 HA22 HA23 HA24 HA25 HA31 HA32 HA33 HA34 HA35
    AP1 AP2 AP3 AP4 ZT HD HDE HDC HQ HQD HTL HMT HDT HSP HB HC HTE HT2 K.
  unfold AZ4_SB in *. assert (HDQ : q + 2 <= dcap) by lia.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -264, SP + -224); (DST, DST + dcap)] mm) as MUW.
  pose proof (wmono_refl bsegs mm) as WMr.
  pose proof AP1 as AQ1; unfold KXGoM.apart in AQ1.
  kx_runFmd [0x9422c] 200%nat [false; false]
     [KZIdx tl (2^tl); KZRange (64 - tl) 52 63; KZRange (2^tl) 2 4096; KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1);
      KZRange q 0 (2^32); KZRange (dcap - q) 2 (2^32); KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
      KZRange tl 1 12; KZRange mtl 1 12; KZRange b 0 64; KZRange c 0 (2^64 - 1); KZRange (DT + 4 + 4 * 2^tl) 4096 (2^47 - 8);
      KZWord (SP + -264) 8 c; KZWord (SP + -256) 4 b;
      KZWr (SP + -384) 120; KZWr (SP + -264) 40; KZWr DST dcap;
      KZDisj DST dcap (SP + -400) 400; KZDisj (DT + 4) (4 * 2^tl) (SP + -400) 400; KZDisj DST dcap (DT + 4) (4 * 2^tl); KZDisj DST dcap 0x7fff8000 (2^44);
      KZTab (DT + 4) (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)]]
     [(DT + 4, 4 * 2^tl)] [(SP + -400, 400); (DST, dcap); (DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (DST, dcap)].
  all: try z4word4.
  all: try z4brx.
  all: try z4brtf.
  all: try z4shd.
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | _ => lia end).
  all: let R39 := fresh "R39" in kx_range (EVar 39) R39.
  all: let R41 := fresh "R41" in kx_range (EVar 41) R41.
  all: kx_post_regs_keep.
  all: lazymatch goal with H : u8arr bsegs ?m ?D (map _ ?b), HL : log_flat _ _ |- _ =>
    destruct (kx_u8arr_ex bsegs _ m _ D b H HL) as (ob' & OB' & LB') end.
  all: kx_cells_split SPL; kx_cells_split BD4; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: eapply K.
  all: first [ eassumption | lia | kx_cells_merge
             | (eexists; split; [eassumption | unfold zlen in *; rewrite LB'; assumption]) ].
Qed.

Lemma z4s34_C2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w10 w11 c p s l : word) (jp : list byte)
    (SP DST dcap DT q b tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
  rw_cells bsegs mm (SP + -264) [C8 c; C4 (Z_to_bv 64 b); CB 4 jp; C8 p; C8 s; C8 l] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= dcap -> 0 <= b < 2^31 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (b <= 64 ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
         F (Z_to_bv 64 0x9405c) fc None mm (seg_rom bsegs))) ->
  (64 < b ->
     evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
         F (Z_to_bv 64 0x94294) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) x10 (Z_to_bv 64 b) x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x9422c) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w10 w11 c p s l jp SP DST dcap DT q b tl mtl
    SPL BD4 MI RS HD HDE HDC HQ HB HTL HMT HDT HSP K1 K2.
  unfold AZ4_SB in *.
  destruct (Z_le_gt_dec b 64) as [C|C].
  2: kx_runFmd [0x9405c; 0x94294] 10%nat [false]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange b 65 (2^31 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -256) 4 b; KZWr (SP + -384) 120; KZWr (SP + -264) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [0x9405c; 0x94294] 10%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange b 0 64;
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -256) 4 b; KZWr (SP + -384) 120; KZWr (SP + -264) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4brx.
  all: try z4br.
  all: kx_post_regs_keep.
  all: z4post_ez.
  1: apply K1; lia.
  1: apply K2; lia.
Qed.

Lemma z4s34_RT : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w10 w11 : word) (bd4 : list cell)
    (SP DST dcap DT q tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 0x94160) (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x9416c) fc None mm (seg_rom bsegs)) ->
  evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 0x94160) (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) x10 x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            x30 x31)
       F (Z_to_bv 64 0x94160) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x27 x28 x29 x30 x31
    w0 w1 w4 w5 w7 w8 w9 w10 w11 bd4 SP DST dcap DT q tl mtl SPL MI RS HD HDE HDC HQ HTL HMT HDT HSP K.
  unfold AZ4_SB in *.
  kx_runFmd [0x9416c] 10%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -336) 8 (DST + dcap); KZWord (SP + -280) 8 (DT + 4); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: kx_post_regs_keep.
  all: z4post_ez.
  exact K.
Qed.

Lemma z4s34_X2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w9 w10 w11 : word)
    (SP DST dcap DT q tl mtl : Z),
  rw_cells bsegs mm (SP + -384) (Z4SPL4 w0 w1 w4 w5 w7 w8 w9 w10 w11 tl mtl DST dcap DT) ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= dcap ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 ->
  (dcap - q < 2 \/ x10 = Z_to_bv 64 0) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) x10 x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x942a0) fc None mm (seg_rom bsegs)) ->
  evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 (Z_to_bv 64 (DST + dcap + -2)) (Z_to_bv 64 (DST + q)) x10 x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 64) (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29
            (Z_to_bv 64 (DT + 4)) x31)
       F (Z_to_bv 64 0x9416c) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w9 w10 w11 SP DST dcap DT q tl mtl SPL MI RS HD HDE HDC HQ HTL HMT HDT HSP HC K.
  unfold AZ4_SB in *.
  destruct (Z_lt_ge_dec (dcap - q) 2) as [C|C].
  - kx_runFmd [0x9422c; 0x942a0] 10%nat [true]
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4br.
    all: kx_post_regs_keep.
    all: z4post_ez.
    exact K.
  - destruct HC as [HC|HC]; [lia|]. subst x10.
    kx_runFmd [0x9422c; 0x942a0] 10%nat (@nil bool)
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange (dcap - q) 2 (2^32);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47); KZWr (SP + -384) 120]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
    all: try z4br.
    all: kx_post_regs_keep.
    all: z4post_ez.
    exact K.
Qed.















