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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import Stdio_pure.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import MState PropExec Frame.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.

Ltac z4ebr :=
  lazymatch goal with
  | |- branch_taken _ _ _ = _ =>
      z4ez; unfold branch_taken; try unfold bv_lts;
      rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?zb_signed, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      rewrite ?Z.mod_small by lia;
      repeat match goal with |- context [(?x <? ?y)%Z] => destruct (Z.ltb_spec x y) end;
      repeat match goal with |- context [(?x =? ?y)%Z] => destruct (Z.eqb_spec x y) end;
      cbn [negb]; first [reflexivity | exfalso; lia]
  end.

Lemma z4e_rg : forall x : word, 0 <= bv_unsigned x < 2^64.
Proof. intros x. pose proof (bv_unsigned_in_range _ x). unfold bv_modulus in *. lia. Qed.

Lemma z4e_cells : forall m A (c bw p a e : word) pad,
  rw_cells bsegs m A [C8 c; C4 bw; CB 4 pad; C8 p; C8 a; C8 e] ->
  rw_cells bsegs m A [C8 c; C4 (Z_to_bv 64 (bv_unsigned bw mod 2^32)); CB 4 pad; C8 (Z_to_bv 64 (bv_unsigned p));
                      C8 (Z_to_bv 64 (bv_unsigned a)); C8 e].
Proof.
  intros m A c bw p a e pad H. rewrite !Z_to_bv_bv_unsigned.
  apply (rw_cells_C4_eq bsegs m A [C8 c] bw (Z_to_bv 64 (bv_unsigned bw mod 2^32)) [CB 4 pad; C8 p; C8 a; C8 e]); [|exact H].
  pose proof (bv_unsigned_in_range _ bw) as R. pose proof (Z.mod_pos_bound (bv_unsigned bw) (2^32) ltac:(lia)) as B.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  rewrite (Z.mod_small (bv_unsigned bw mod 2^32) (2^64)) by lia. rewrite Zmod_mod. reflexivity.
Qed.

Lemma z4e_ck1 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x10 c e : word)
    (pad : list byte) (SP P A B : Z),
  rw_cells bsegs mm (SP + -144) [C8 c; C4 (Z_to_bv 64 B); CB 4 pad; C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 A); C8 e] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  2^20 <= SP <= 2^47 -> 0 <= P < 2^64 -> 0 <= A < 2^64 -> 0 <= B < 2^32 ->
  (forall y10 y11 y12 y13 y14 : word, evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
               x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 607404) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
               x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 607372) fc None mm (seg_rom bsegs)).
Proof.
  intros. destruct (Z.eq_dec P A) as [HE|HE];
  [ kx_runFmd [607404] 24%nat [true] [KZRange SP (2^20) (2^47); KZRange P 0 (2^64 - 1); KZRange A 0 (2^64 - 1);
      KZRange B 0 (2^32 - 1); KZWord (SP + -128) 8 P; KZWord (SP + -120) 8 A; KZWord (SP + -136) 4 B; KZWr (SP + -144) 40]
      [] [(SP + -400, 400)] []
  | kx_runFmd [607404] 24%nat [false] [KZRange SP (2^20) (2^47); KZRange P 0 (2^64 - 1); KZRange A 0 (2^64 - 1);
      KZRange B 0 (2^32 - 1); KZWord (SP + -128) 8 P; KZWord (SP + -120) 8 A; KZWord (SP + -136) 4 B; KZWr (SP + -144) 40]
      [] [(SP + -400, 400)] [] ].
  all: try z4ebr.
  all: try z4word4.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; cbn [mem_denot];
      match goal with KK : forall y10 y11 y12 y13 y14 : word, _ |- _ => eapply KK end end).
Qed.

Lemma z4e_ck2 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x10 c e : word)
    (pad : list byte) (SP P A B : Z),
  rw_cells bsegs mm (SP + -184) [C8 c; C4 (Z_to_bv 64 B); CB 4 pad; C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 A); C8 e] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  2^20 <= SP <= 2^47 -> 0 <= P < 2^64 -> 0 <= A < 2^64 -> 0 <= B < 2^32 ->
  (forall y10 y11 y12 y13 y14 : word, evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
               x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 607436) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
               x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 607404) fc None mm (seg_rom bsegs)).
Proof.
  intros. destruct (Z.eq_dec P A) as [HE|HE];
  [ kx_runFmd [607436] 24%nat [true] [KZRange SP (2^20) (2^47); KZRange P 0 (2^64 - 1); KZRange A 0 (2^64 - 1);
      KZRange B 0 (2^32 - 1); KZWord (SP + -168) 8 P; KZWord (SP + -160) 8 A; KZWord (SP + -176) 4 B; KZWr (SP + -184) 40]
      [] [(SP + -400, 400)] []
  | kx_runFmd [607436] 24%nat [false] [KZRange SP (2^20) (2^47); KZRange P 0 (2^64 - 1); KZRange A 0 (2^64 - 1);
      KZRange B 0 (2^32 - 1); KZWord (SP + -168) 8 P; KZWord (SP + -160) 8 A; KZWord (SP + -176) 4 B; KZWr (SP + -184) 40]
      [] [(SP + -400, 400)] [] ].
  all: try z4ebr.
  all: try z4word4.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; cbn [mem_denot];
      match goal with KK : forall y10 y11 y12 y13 y14 : word, _ |- _ => eapply KK end end).
Qed.

Lemma z4e_ck3 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x10 c e : word)
    (pad : list byte) (SP P A B : Z),
  rw_cells bsegs mm (SP + -224) [C8 c; C4 (Z_to_bv 64 B); CB 4 pad; C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 A); C8 e] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  2^20 <= SP <= 2^47 -> 0 <= P < 2^64 -> 0 <= A < 2^64 -> 0 <= B < 2^32 ->
  (forall y10 y11 y12 y13 y14 : word, evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
               x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 607472) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
               x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 607436) fc None mm (seg_rom bsegs)).
Proof.
  intros. destruct (Z.eq_dec P A) as [HE|HE];
  [ kx_runFmd [607472] 24%nat [true] [KZRange SP (2^20) (2^47); KZRange P 0 (2^64 - 1); KZRange A 0 (2^64 - 1);
      KZRange B 0 (2^32 - 1); KZWord (SP + -208) 8 P; KZWord (SP + -200) 8 A; KZWord (SP + -216) 4 B; KZWr (SP + -224) 40]
      [] [(SP + -400, 400)] []
  | kx_runFmd [607472] 24%nat [false] [KZRange SP (2^20) (2^47); KZRange P 0 (2^64 - 1); KZRange A 0 (2^64 - 1);
      KZRange B 0 (2^32 - 1); KZWord (SP + -208) 8 P; KZWord (SP + -200) 8 A; KZWord (SP + -216) 4 B; KZWr (SP + -224) 40]
      [] [(SP + -400, 400)] [] ].
  all: try z4ebr.
  all: try z4word4.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; cbn [mem_denot];
      match goal with KK : forall y10 y11 y12 y13 y14 : word, _ |- _ => eapply KK end end).
Qed.

Lemma z4e_ck4 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x10 c e : word)
    (pad : list byte) (SP P A B : Z),
  rw_cells bsegs mm (SP + -264) [C8 c; C4 (Z_to_bv 64 B); CB 4 pad; C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 A); C8 e] ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 ->
  2^20 <= SP <= 2^47 -> 0 <= P < 2^64 -> 0 <= A < 2^64 -> 0 <= B < 2^32 ->
  (forall y10 y11 y12 y13 y14 : word, evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 y10 y11 y12 y13 y14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
               x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 607512) fc None mm (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
               x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 607472) fc None mm (seg_rom bsegs)).
Proof.
  intros. destruct (Z.eq_dec P A) as [HE|HE];
  [ kx_runFmd [607512] 24%nat [true] [KZRange SP (2^20) (2^47); KZRange P 0 (2^64 - 1); KZRange A 0 (2^64 - 1);
      KZRange B 0 (2^32 - 1); KZWord (SP + -248) 8 P; KZWord (SP + -240) 8 A; KZWord (SP + -256) 4 B; KZWr (SP + -264) 40]
      [] [(SP + -400, 400)] []
  | kx_runFmd [607512] 24%nat [false] [KZRange SP (2^20) (2^47); KZRange P 0 (2^64 - 1); KZRange A 0 (2^64 - 1);
      KZRange B 0 (2^32 - 1); KZWord (SP + -248) 8 P; KZWord (SP + -240) 8 A; KZWord (SP + -256) 4 B; KZWr (SP + -264) 40]
      [] [(SP + -400, 400)] [] ].
  all: try z4ebr.
  all: try z4word4.
  all: try (lazymatch goal with |- evtF _ _ _ _ => kx_post_regs; cbn [mem_denot];
      match goal with KK : forall y10 y11 y12 y13 y14 : word, _ |- _ => eapply KK end end).
Qed.

Lemma z4e_ck5 : forall (Q : machine_state -> Prop) (RNG : footprint) (mm : amem) (F : bvmap 5 word) (fc : bv 32)
    (x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word) (SP dcap V : Z),
  rw_cells bsegs mm (SP + -384) (SPD w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 dcap)) ->
  mem_inv bsegs mm -> rng RNG (SP + -400) 400 -> 2^20 <= SP <= 2^47 -> 0 <= dcap < 2^32 -> 0 <= V < 2^64 ->
  (forall mm' (r : Z) (y10 y11 y12 y13 y14 : word),
      rw_cells bsegs mm' (SP + -384) (SPD w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 r)) ->
      mem_inv bsegs mm' -> munch [(SP + -384, SP + -264)] mm mm' -> wmono bsegs mm mm' ->
      r = dcap \/ r = 2^64 - 20 ->
      evtF bsegs RNG Q
        (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp (Z_to_bv 64 r) x6 x7 x8 x9 y10 y11 y12 y13 y14 x15 x16 x17 x18 x19 x20 x21
                 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 588780) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q
      (MS (mkR x1 (Z_to_bv 64 (SP + -384)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 V) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
               x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 607512) fc None mm (seg_rom bsegs)).
Proof.
  intros Q RNG mm F fc x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
    x31 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 SP dcap V SPL MI RS HSP HDC HV KA.
  unfold SPD in *.
  pose proof (munch_refl [(SP + -384, SP + -264)] mm) as MUW. pose proof (wmono_refl bsegs mm) as WMr.
  destruct (Z.eq_dec V 0) as [HE|HE];
  [ kx_runFmd [588780] 16%nat [false] [KZRange SP (2^20) (2^47); KZRange V 0 (2^64 - 1); KZRange dcap 0 (2^32 - 1);
      KZWord (SP + -272) 8 dcap; KZWr (SP + -384) 120] [] [(SP + -400, 400)] []
  | kx_runFmd [588780] 16%nat [true] [KZRange SP (2^20) (2^47); KZRange V 0 (2^64 - 1); KZRange dcap 0 (2^32 - 1);
      KZWord (SP + -272) 8 dcap; KZWr (SP + -384) 120] [] [(SP + -400, 400)] [] ].
  all: try z4ebr.
  all: try lia.
  all: kx_post_regs_keep.
  all: kx_cells_split SPL; kx_cells_post.
  all: kx_munch MUW; kx_post_mem_free.
  all: z4post_ez.
  all: lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ (Z_to_bv 64 ?v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
         first [ eapply (KA _ v); [ kx_cells_merge | eassumption | eassumption | eassumption | left; reflexivity ]
               | rewrite (z4_bvm v (2^64 - 20)) in * by reflexivity;
                 eapply (KA _ (2^64 - 20)); [ kx_cells_merge | eassumption | eassumption | eassumption | right; reflexivity ] ]
       end.
Qed.


Lemma z4e_rebuild : forall (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region)
    (mm m' : amem) (spl spl' bd4 bd3 bd2 bd1 : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  1 <= dcap ->
  Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm spl bd4 bd3 bd2 bd1 ->
  munch [(bv_unsigned sp + -384, bv_unsigned sp + -264)] mm m' -> wmono bsegs mm m' -> mem_inv bsegs m' ->
  rw_cells bsegs m' (bv_unsigned sp + -384) spl' -> cells_size spl' = 120%nat ->
  Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs m' spl' bd4 bd3 bd2 bd1.
Proof.
  intros AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cells cbs pdt
    SBL SBH rstk mm m' spl spl' bd4 bd3 bd2 bd1 C D1 FR MU' WM' MI' SP' SPS'.
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C D1)
    as (FD1 & FD2 & FD3 & FD4 & FD5 & FSS & FSP1 & FSP2 & FRS).
  destruct C as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  destruct FR as (BUF & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRM & MI & MU & WM).
  set (SP := bv_unsigned sp) in *.
  assert (NZ : 0 < zlen src -> SS + zlen src <= ATOP).
  { intros NZ. destruct (SRCB NZ) as (psb & HSB & SB1 & SB2).
    pose proof (ablk_lin _ _ (ABL _ HSB)) as A. cbn [ab_addr ab_size] in A. lia. }
  destruct DSTF as [(E1 & E2)|(pb & HDB)]; [lia|].
  pose proof (ablk_lin _ _ (ABL _ HDB)) as HDL. cbn [ab_addr ab_size] in HDL.
  pose proof (ablk_lin _ _ (ABL _ HDT)) as HTL. cbn [ab_addr ab_size] in HTL.
  assert (DTB : DT + 4 + zlen cbs <= ATOP).
  { rewrite LCB. unfold DTABLE_BYTES, HufHarness.DT_BYTES in HTL.
    pose proof (Z.pow_le_mono_r 2 tl mtl ltac:(lia) ltac:(lia)). lia. }
  destruct BUF as (buf & BU & BL).
  split; [exists buf; split; [eapply u8arr_transport; [exact BU | exact MU' | exact WM' |] | exact BL] |].
  { rewrite length_map, BL. cbn [disjoint_from]. lia. }
  split.
  { destruct (Z.eq_dec (zlen src) 0) as [Z0|Z0].
    - assert (SR0 : src = []) by (destruct src; [reflexivity | cbn [length] in Z0; lia]). subst src.
      unfold bytes_at in BSS |- *. destruct BSS as (BS1 & BS2 & _). split; [exact BS1|]. split; [exact BS2|].
      intros i Hi. cbn [length map] in Hi. lia.
    - eapply bytes_at_transport; [exact BSS | exact MU' |]; rewrite length_map; cbn [disjoint_from].
      specialize (NZ ltac:(lia)); lia. }
  split; [eapply bytes_at_transport; [exact BDT4 | exact MU' |]; cbn [disjoint_from]; lia |].
  split; [eapply bytes_at_transport; [exact BDT | exact MU' |]; cbn [disjoint_from length]; lia |].
  split; [eapply stk_transport_disjoint; [exact STK | exact MU' | exact WM' |]; cbn [disjoint_from]; lia |].
  split; [exact SP' |].
  split; [exact SPS' |].
  split; [eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]; rewrite B4S; cbn [disjoint_from]; lia |].
  split; [exact B4S |].
  split; [eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]; rewrite B3S; cbn [disjoint_from]; lia |].
  split; [exact B3S |].
  split; [eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]; rewrite B2S; cbn [disjoint_from]; lia |].
  split; [exact B2S |].
  split; [eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]; rewrite B1S; cbn [disjoint_from]; lia |].
  split; [exact B1S |].
  split; [eapply rw_cells_transport; [exact FRM | exact MU' | exact WM' |]; cbn [disjoint_from cells_size csize]; lia |].
  split; [exact MI' |].
  split.
  - eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU']].
    intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia.
  - eapply wmono_trans; [exact WM | exact WM'].
Qed.

Theorem z4end_proof : z4end_stmtA.
Proof.
  intros Q AI L RNG st LB rng_fs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m0
    DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk HC D6.
  unfold z4end_goal.
  intros w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 c1 b1 p1 s1' l1 c2 b2 p2 s2' l2 c3 b3 p3 s3' l3 c4 b4 p4 s4' l4
    jp1 jp2 jp3 jp4 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31 Z4 K.
  pose proof (z4ctx_facts AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk HC ltac:(lia))
    as (FD1 & FD2 & FDC & FT1 & FT2 & FS & FSP1 & FSP2 & FRNG).
  pose proof HC as HC'.
  destruct HC' as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof (AI_layout AI L RNG st LB m0 AH) as HL. pose proof (@ATOP_lo rc) as HA.
  pose proof Z4 as Z4'.
  destruct Z4' as (BUF & SRC & CBS & DTH & STK & SPL & SPLs & B4 & B4s & B3 & B3s & B2 & B2s & B1 & B1s & FRSc & MI & MU & WM).
  assert (RS : rng RNG (bv_unsigned sp + -400) 400)
    by (replace (bv_unsigned sp + -400) with (bv_unsigned sp - 400) by lia; exact FRNG).
  assert (HSP : 2^20 <= bv_unsigned sp <= 2^47) by lia.
  unfold BD4A in B1, B2, B3, B4.
  apply z4e_cells in B1, B2, B3, B4.
  pose proof (z4e_rg p1) as R1. pose proof (z4e_rg s1') as R2. pose proof (z4e_rg p2) as R3. pose proof (z4e_rg s2') as R4.
  pose proof (z4e_rg p3) as R5. pose proof (z4e_rg s3') as R6. pose proof (z4e_rg p4) as R7. pose proof (z4e_rg s4') as R8.
  pose proof (Z.mod_pos_bound (bv_unsigned b1) (2^32) ltac:(lia)) as M1.
  pose proof (Z.mod_pos_bound (bv_unsigned b2) (2^32) ltac:(lia)) as M2.
  pose proof (Z.mod_pos_bound (bv_unsigned b3) (2^32) ltac:(lia)) as M3.
  pose proof (Z.mod_pos_bound (bv_unsigned b4) (2^32) ltac:(lia)) as M4.
  unfold AZ4_END. unfold AZ4_DEPI in K.
  eapply z4e_ck1 with (P := bv_unsigned p1) (A := bv_unsigned s1') (B := bv_unsigned b1 mod 2^32) (pad := jp1) (c := c1) (e := l1);
    [exact B1 | exact MI | exact RS | lia .. | intros y10 y11 y12 y13 y14].
  eapply z4e_ck2 with (P := bv_unsigned p2) (A := bv_unsigned s2') (B := bv_unsigned b2 mod 2^32) (pad := jp2) (c := c2) (e := l2);
    [exact B2 | exact MI | exact RS | lia .. | intros z10 z11 z12 z13 z14].
  eapply z4e_ck3 with (P := bv_unsigned p3) (A := bv_unsigned s3') (B := bv_unsigned b3 mod 2^32) (pad := jp3) (c := c3) (e := l3);
    [exact B3 | exact MI | exact RS | lia .. | intros u10 u11 u12 u13 u14].
  eapply z4e_ck4 with (P := bv_unsigned p4) (A := bv_unsigned s4') (B := bv_unsigned b4 mod 2^32) (pad := jp4) (c := c4) (e := l4);
    [exact B4 | exact MI | exact RS | lia .. | intros v10 v11 v12 v13 v14].
  rewrite <- (Z_to_bv_bv_unsigned v10).
  eapply z4e_ck5 with (V := bv_unsigned v10) (dcap := dcap); [exact SPL | exact MI | exact RS | lia | lia | apply z4e_rg |].
  intros mm' r t10 t11 t12 t13 t14 SPL' MI' MU' WM' HR.
  eapply (K mm' (SPD w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 r)) r); [| exact HR].
  eapply z4e_rebuild; [exact HC | lia | exact Z4 | exact MU' | exact WM' | exact MI' | exact SPL' | apply SPD_size].
Qed.

End CANSEC1.
