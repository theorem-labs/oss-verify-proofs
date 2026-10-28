(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import HufWalkKit2 HufWalkKit3.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell KXCell2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AF_huf_z4s3_iface AF_huf_z4s3b.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".
Notation amem := (word -> option byte).
Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
Ltac kxg_cell H :=
  lazymatch type of H with
  | rw_cells _ _ _ [C8 ?v] => let w := fresh "cw" in let EQ := fresh "EQ" in remember v as w eqn:EQ in H; clear EQ
  | rw_cells _ _ _ [C4 ?v] => let w := fresh "cw" in let EQ := fresh "EQ" in remember v as w eqn:EQ in H; clear EQ
  end.

(* [comment removed for export] *)
Lemma z4s31_E : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (gp tp x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x31 : word)
    (w0 w1 w4 w5 w7 w8 w10 w11 w12 : word) (jp : list byte)
    (SP DST dcap SS DT q Qe O L pt b cz tl mtl : Z),
  rw_cells bsegs mm (SP + -384) [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7)); C8 w4; C8 w5;
        C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 (Z_to_bv 64 (DST + Qe)); C8 w10; C8 w11; C8 w12; C8 (Z_to_bv 64 (DT + 4));
        C8 (Z_to_bv 64 dcap)] ->
  rw_cells bsegs mm (SP + -144) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  4096 <= DST -> DST + dcap <= 2^47 -> 6 <= dcap < 2^32 -> 0 <= q <= Qe -> Qe <= dcap ->
  4096 <= SS -> SS + O + L <= 2^47 -> 6 <= O -> 1 <= L < 2^26 -> 0 <= pt -> pt <= L -> 0 <= b < 2^31 -> 0 <= cz < 2^64 ->
  1 <= tl <= 12 -> 1 <= mtl <= 12 -> tl <= mtl -> 4096 <= DT <= 2^47 -> 2^46 <= SP <= 2^47 -> O <= 2^26 ->
  (Qe - q < 8 -> forall mm',
      rw_cells bsegs mm' (SP + -384) [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7)); C8 w4; C8 w5;
        C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 (Z_to_bv 64 (DST + Qe)); C8 w10; C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
        C8 (Z_to_bv 64 dcap)] ->
      rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (- q + Qe)) (Z_to_bv 64 8) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 tl) x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
           F (Z_to_bv 64 0x90328) fc None mm' (seg_rom bsegs))) ->
  (8 <= Qe - q -> 12 <= tl -> forall mm',
      rw_cells bsegs mm' (SP + -384) [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7)); C8 w4; C8 w5;
        C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 (Z_to_bv 64 (DST + Qe)); C8 w10; C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
        C8 (Z_to_bv 64 dcap)] ->
      rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 (Z_to_bv 64 12) (Z_to_bv 64 8) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 tl) x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
           F (Z_to_bv 64 0x90460) fc None mm' (seg_rom bsegs))) ->
  (8 <= Qe - q -> tl < 12 -> b <= 64 -> forall mm',
      rw_cells bsegs mm' (SP + -384) [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7)); C8 w4; C8 w5;
        C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 (Z_to_bv 64 (DST + Qe)); C8 w10; C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
        C8 (Z_to_bv 64 dcap)] ->
      rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 (SS + O + pt));
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 (Z_to_bv 64 (- tl + -256 * mtl)) (Z_to_bv 64 b) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 tl) x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
           F (Z_to_bv 64 0x8fcd4) fc None mm' (seg_rom bsegs))) ->
  (8 <= Qe - q -> tl < 12 -> 64 < b -> forall mm',
      rw_cells bsegs mm' (SP + -384) [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7)); C8 w4; C8 w5;
        C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 (Z_to_bv 64 (DST + Qe)); C8 w10; C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
        C8 (Z_to_bv 64 dcap)] ->
      rw_cells bsegs mm' (SP + -144) [C8 (Z_to_bv 64 cz); C4 (Z_to_bv 64 b); CB 4 jp; C8 (Z_to_bv 64 0x20e00);
        C8 (Z_to_bv 64 (SS + O)); C8 (Z_to_bv 64 (SS + O + 8))] ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm mm' -> wmono bsegs mm mm' ->
      evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 (Z_to_bv 64 0x20e00) (Z_to_bv 64 b) (Z_to_bv 64 (DST + q)) (Z_to_bv 64 tl) x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 x20 (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
           F (Z_to_bv 64 0x90a08) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe))
               x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 x26 x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
          F (Z_to_bv 64 AZ4_S1) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc gp tp x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x31
    w0 w1 w4 w5 w7 w8 w10 w11 w12 jp SP DST dcap SS DT q Qe O L pt b cz tl mtl
    SPL BD1 MI RS HD HDE HDC HQ HQE HS HSE HO HL HPT HPL HB HCZ HTL HMT HTM HDT HSP HO2 K1 K2 K3 K4.
  unfold AZ4_S1, AZ4_SB in *.
  pose proof (munch_refl [(SP + -384, SP + -264); (SP + -144, SP + -104)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  destruct (Z_lt_ge_dec (Qe - q) 8) as [C1|C1]; [|destruct (Z_lt_ge_dec tl 12) as [C2|C2]; [destruct (Z_le_gt_dec b 64) as [C3|C3]|]].
  4: kx_runFmd [0x8fcd4; 0x90328; 0x90460; 0x90a08; 0x8fbec] 60%nat [false; true] 
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 (2^26); KZRange b 0 (2^31 - 1); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -360) 8 (DST + dcap - 7); KZWord (SP + -336) 8 (DST + dcap);
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  3: kx_runFmd [0x8fcd4; 0x90328; 0x90460; 0x90a08; 0x8fbec] 60%nat [false; false; false] 
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 (2^26); KZRange b 0 (2^31 - 1); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -360) 8 (DST + dcap - 7); KZWord (SP + -336) 8 (DST + dcap);
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  2: kx_runFmd [0x8fcd4; 0x90328; 0x90460; 0x90a08; 0x8fbec] 60%nat [false; false; true] 
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 (2^26); KZRange b 0 (2^31 - 1); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -360) 8 (DST + dcap - 7); KZWord (SP + -336) 8 (DST + dcap);
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  1: kx_runFmd [0x8fcd4; 0x90328; 0x90460; 0x90a08; 0x8fbec] 60%nat [true] 
     [KZRange DST 4096 (2^47); KZRange dcap 6 (2^32 - 1); KZRange q 0 (2^32); KZRange Qe 0 (2^32); KZRange SS 4096 (2^47);
     KZRange O 6 (2^26); KZRange L 1 (2^26); KZRange pt 0 (2^26); KZRange b 0 (2^31 - 1); KZRange cz 0 (2^64 - 1);
     KZRange tl 1 12; KZRange mtl 1 12; KZRange DT 4096 (2^47); KZRange SP (2^46) (2^47);
     KZWord (SP + -368) 8 (tl + 256 * mtl); KZWord (SP + -360) 8 (DST + dcap - 7); KZWord (SP + -336) 8 (DST + dcap);
     KZWord (SP + -312) 8 (DST + Qe); KZWord (SP + -280) 8 (DT + 4); KZWord (SP + -272) 8 dcap;
     KZWord (SP + -144) 8 cz; KZWord (SP + -136) 4 b; KZWord (SP + -128) 8 (SS + O + pt); KZWord (SP + -120) 8 (SS + O);
     KZWord (SP + -112) 8 (SS + O + 8); KZWr (SP + -384) 120; KZWr (SP + -144) 40]
     (@nil (Z * Z)) [(SP + -400, 400)] (@nil (Z * Z)).
  all: try z4word4.
  all: try z4brdl.
  all: try z4br.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_split BD1; kx_cells_post.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition K31S2 (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell) : Prop :=
  forall mm' (c' b' p' s' l' : word) (jp' : list byte) (v0 v4 v5 v7 v8 v9 v11 : word)
         (z1 z5 z7 z8 z10 z11 z12 z13 z14 z15 z16 z17 z20 z22 z23 z24 z25 z27 z28 z29 z31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm'
           (SPD v0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) v4 v5 (Z_to_bv 64 (DST + dcap)) v7 v8 v9 w10 v11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
           (BD4A c' b' jp' p' s' l') ->
    evtF bsegs RNG Q (MS (mkR z1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp z5 (Z_to_bv 64 (DST + dcap)) z7 z8 x9 z10 z11 z12 z13 z14 z15 z16 z17 x18 x19 z20 (Z_to_bv 64 AZ4_SB) z22 z23 z24 z25 (Z_to_bv 64 (2^61)) z27 z28 z29 (Z_to_bv 64 (DT + 4)) z31)
                           FR (Z_to_bv 64 AZ4_S2) fc None mm' (seg_rom bsegs)).

Definition C31J (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell) : Prop :=
  forall (q b : Z) (c p : word) (jp : list byte) (w0 w4 w5 w7 w8 w11 : word) mm (x1 x5 x7 x8 x10 x11 x13 x14 x15 x16 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
           (BD4A c (Z_to_bv 64 b) jp p (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
    0 <= q <= Qe ->
    ((exists pt, p = (Z_to_bv 64 (SS + O + pt)) /\ 0 <= pt /\ (pt = 0 \/ pt + 8 <= Lk)) /\ 0 <= b <= 64 \/ 64 < b < 2^31) ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
                           FR (Z_to_bv 64 0x90a08) fc None mm (seg_rom bsegs)).

Definition C31H5 (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell) : Prop :=
  forall (q pt b : Z) (c : word) (jp : list byte) (w0 w4 w5 w7 w8 w11 : word) mm (x1 x5 x7 x8 x10 x11 x13 x14 x15 x16 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
           (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
    0 <= q <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b <= 64 -> tl < 12 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 (Z_to_bv 64 b) (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 (Z_to_bv 64 (- DT + -5)) (Z_to_bv 64 AZ4_SB) (Z_to_bv 64 64) (Z_to_bv 64 (DST + Qe + -9)) (Z_to_bv 64 (64 - tl)) x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
                           FR (Z_to_bv 64 0x8fcd4) fc None mm (seg_rom bsegs)).

Definition C31H4 (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell) : Prop :=
  forall (q pt b : Z) (c : word) (jp : list byte) (w0 w4 w5 w7 w8 w11 : word) mm (x1 x5 x7 x8 x10 x11 x13 x14 x15 x16 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
           (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
    0 <= q -> q + 8 <= Qe -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b < 2^31 -> 12 <= tl ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 (Z_to_bv 64 (DST + dcap)) x7 x8 x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 (Z_to_bv 64 (DST + Qe)) x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
                           FR (Z_to_bv 64 0x90460) fc None mm (seg_rom bsegs)).

Definition C31R (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (m0 : amem) (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cbs : list byte) (Q : machine_state -> Prop)
    (O Lk Qe : Z) (w1 w10 x9 x18 x19 : word) (bd4 bd3 bd2 : list cell) : Prop :=
  forall (q pt b : Z) (c : word) (jp : list byte) (w0 w4 w5 w7 w8 w11 : word) mm (x6 x17 x1 x5 x7 x8 x10 x11 x13 x14 x15 x16 x20 x22 x23 x24 x25 x27 x28 x29 x31 : word),
    Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm
           (SPD w0 w1 (Z_to_bv 64 (tl + 256 * mtl)) (Z_to_bv 64 (DST + dcap - 7)) w4 w5 (Z_to_bv 64 (DST + dcap)) w7 w8 (Z_to_bv 64 (DST + Qe)) w10 w11 (Z_to_bv 64 tl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 dcap)) bd4 bd3 bd2
           (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
    0 <= q <= Qe -> Qe < q + 8 -> 0 <= pt -> (pt = 0 \/ pt + 8 <= Lk) -> 0 <= b < 2^31 ->
    evtF bsegs RNG Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 (DST + q)) x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 AZ4_SB) x22 x23 x24 x25 (Z_to_bv 64 (2^61)) x27 x28 x29 (Z_to_bv 64 (DT + 4)) x31)
                           FR (Z_to_bv 64 0x90328) fc None mm (seg_rom bsegs)).
