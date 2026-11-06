(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI PcapRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.libpcap.fuzz_pcap.images Require Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3.
From Stdlib Require Permutation.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3.
From Ltac2 Require Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_sfpcapng_blkA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma le4_le_bytes : forall x, 0 <= x < 2^32 -> le4 (Z_to_bv 64 x) = map b8 (le_bytes 4 x).
Proof using Type. pin_using tt.
  intros x Hx. unfold le_bytes. cbn [le_bytes_nat Z.to_nat Pos.to_nat Pos.iter_op Nat.add map].
  rewrite (le4_of_val _ (x mod 256) (x / 256 mod 256) (x / 256 / 256 mod 256) (x / 256 / 256 / 256 mod 256) 0);
    [reflexivity | | | | | lia |]; try (Z.div_mod_to_equations; lia).
  rewrite unsigned_lit by lia. Z.div_mod_to_equations. lia.
Qed.

Lemma le8_two : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^32 ->
  le8 (Z_to_bv 64 (x + 4294967296 * y)) = map b8 (le_bytes 4 x ++ le_bytes 4 y).
Proof using Type. pin_using tt.
  intros x y Hx Hy.
  replace (Z_to_bv 64 (x + 4294967296 * y)) with (pack2 (Z_to_bv 64 x) (Z_to_bv 64 y))
    by (unfold pack2; rewrite !unsigned_lit by lia; rewrite !Z.mod_small by lia; reflexivity).
  rewrite le8_pack2, map_app, !le4_le_bytes by lia. reflexivity.
Qed.

Lemma le4_mod32 : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^32 -> le4 (Z_to_bv 64 (x + 4294967296 * y)) = le4 (Z_to_bv 64 x).
Proof using Type. pin_using tt.
  intros x y Hx Hy. unfold le4. rewrite !unsigned_lit by lia.
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr, !Z.shiftr_div_pow2 by lia. cbn [Z.add Z.pow Z.pow_pos Pos.iter Z.mul].
  f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|]. f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|].
  f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|]. f_equal. apply Z_to_bv8_mod. Z.div_mod_to_equations; lia.
Qed.

Lemma le_bytes_4_range : forall x, Forall (fun z => 0 <= z < 256) (le_bytes 4 x).
Proof using Type. pin_using tt.
  intros x. unfold le_bytes. cbn [le_bytes_nat Z.to_nat Pos.to_nat Pos.iter_op Nat.add].
  repeat constructor; Z.div_mod_to_equations; lia.
Qed.
Lemma length_le_bytes : forall k x, length (le_bytes k x) = Z.to_nat k.
Proof using Type. pin_using tt. intros k x. unfold le_bytes. generalize x. induction (Z.to_nat k) as [|n IH]; intros; cbn; [reflexivity| now rewrite IH]. Qed.

Lemma lastn4 : forall {A} (l : list A), (4 <= length l)%nat -> exists l1 a b c d, l = l1 ++ [a; b; c; d] /\ length l1 = (length l - 4)%nat.
Proof using Type. pin_using tt.
  intros A l Hl. exists (firstn (length l - 4) l).
  pose proof (firstn_skipn (length l - 4) l) as E.
  pose proof (length_skipn (length l - 4) l) as L.
  destruct (skipn (length l - 4) l) as [|a [|b [|c [|d [|e r]]]]]; cbn in L; try lia.
  exists a, b, c, d. split; [symmetry; exact E| rewrite length_firstn; lia].
Qed.

(* [comment removed for export] *)
Lemma Z_to_bv_s32_inj : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^32 -> Z_to_bv 64 (s32 x) = Z_to_bv 64 (s32 y) -> x = y.
Proof using Type. pin_using tt.
  intros x y Hx Hy E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit_wrap in E. unfold s32 in E.
  Z.div_mod_to_equations. lia.
Qed.
Lemma eqb_s32 : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^32 -> bv_eqb (Z_to_bv 64 (s32 x)) (Z_to_bv 64 (s32 y)) = (x =? y).
Proof using Type. pin_using tt.
  intros x y Hx Hy. destruct (Z.eqb_spec x y) as [->|NE]; [apply Z.eqb_refl|].
  unfold bv_eqb. apply Z.eqb_neq. intros E. apply NE. apply (Z_to_bv_s32_inj x y Hx Hy). apply bv_eq. exact E.
Qed.

(* [comment removed for export] *)
Lemma swrap32_low : forall u x hi, u = x + 4294967296 * hi -> Z_to_bv 64 (bv_swrap 32 (u + 0)) = Z_to_bv 64 (s32 x).
Proof using Type. pin_using tt.
  intros u x hi ->. f_equal. unfold bv_swrap, bv_wrap, s32, bv_half_modulus, bv_modulus. cbn -[Z.add Z.sub Z.modulo Z.mul].
  Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma shl_shr_32 : forall u x hi, u = x + 4294967296 * hi -> 0 <= x < 2^32 -> 0 <= hi ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl u 32))) 32) = Z_to_bv 64 x.
Proof using Type. pin_using tt.
  intros u x hi -> Hx Hhi. f_equal. rewrite Z.shiftl_mul_pow2, unsigned_lit_wrap, Z.shiftr_div_pow2 by lia.
  Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma land3_low : forall u x hi, u = x + 4294967296 * hi -> 0 <= x -> 0 <= hi -> Z.land u 3 = x mod 4.
Proof using Type. pin_using tt.
  intros u x hi -> Hx Hhi. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2^2) with 4. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
End WithCeil.

Ltac fix_sb :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
           change (le1 w) with [Z_to_bv 8 (bv_unsigned w)]; mem_after_store
       end).
Ltac bstep := step; fix_sb.

Open Scope bv_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition blk_swap_hdr__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (g0 g1 g2 g3 g4 g5 g6 g7 : Z),
    mem_inv ssegs m -> (96 <= bv_unsigned sp)%Z ->
    (0 <= g0 < 256)%Z -> (0 <= g1 < 256)%Z -> (0 <= g2 < 256)%Z -> (0 <= g3 < 256)%Z ->
    (0 <= g4 < 256)%Z -> (0 <= g5 < 256)%Z -> (0 <= g6 < 256)%Z -> (0 <= g7 < 256)%Z ->
    rw_cells ssegs m (bv_unsigned sp + -96) [C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C4 (Z_to_bv 64 (le4val g4 g5 g6 g7))] ->
    evt ssegs (fun ms' => exists (a0' a1' a2' a3' a4' a5' : word) (hi : Z) m',
        ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x16ce8) fc None m' (seg_rom ssegs)
        /\ munch [(bv_unsigned sp + -96, bv_unsigned sp + -88)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
        /\ rw_cells ssegs m' (bv_unsigned sp + -96) [C4 (Z_to_bv 64 (le4val g3 g2 g1 g0)); C4 (Z_to_bv 64 (le4val g7 g6 g5 g4))]
        /\ (bv_unsigned a0' = le4val g7 g6 g5 g4 + 4294967296 * hi)%Z /\ (0 <= hi < 2^32)%Z)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16c88) fc None m (seg_rom ssegs)).
Section Sz12.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m g0 g1 g2 g3 g4 g5 g6 g7 : ltac2:(SecDiet.SzSec.tyM 'blk_swap_hdr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma blk_swap_hdr__body : ltac2:(SecDiet.SzSec.bodyP 'blk_swap_hdr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
  intros MI SPL B0 B1 B2 B3 B4 B5 B6 B7 FR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP.
  pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp + -88)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  do 24 step.
  apply evt_done. do 6 eexists. exists (g5 + 256 * g6 + 65536 * g7 + 16777216 * (((g7 / 128) * 4294967295) mod 256))%Z. eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [| split; [| Z.div_mod_to_equations; lia]].
  - eapply rw_cells_recell; [exact FR | cbn; repeat split; exact Logic.I |].
    cbn [cells_bytes cbytes app].
    rewrite (le4_lit g3 g2 g1 g0), (le4_lit g7 g6 g5 g4) by lia.
    rewrite (le4_of_val _ g3 g2 g1 g0 (g1 + 256 * g2 + 65536 * g3 + 16777216 * (((g3 / 128) * 4294967295) mod 256)));
      [| lia | lia | lia | lia | Z.div_mod_to_equations; lia
       | apply (swap32_val _ g0 g1 g2 g3); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
    rewrite (le4_of_val _ g7 g6 g5 g4 (g5 + 256 * g6 + 65536 * g7 + 16777216 * (((g7 / 128) * 4294967295) mod 256)));
      [| lia | lia | lia | lia | Z.div_mod_to_equations; lia
       | apply (swap32_val _ g4 g5 g6 g7); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
    reflexivity.
  - rewrite (swap32_val _ g4 g5 g6 g7 ((g7 / 128) * 4294967295)); [unfold le4val; lia | lia | lia | lia | lia | Z.div_mod_to_equations; lia |].
    rewrite unsigned_sx32 by lia. unfold sxv, le4val. lia.
Qed.
End Sz12.
Lemma blk_swap_hdr : ltac:(let t := eval cbv delta [blk_swap_hdr__stmt] in blk_swap_hdr__stmt in exact t).
Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m g0 g1 g2 g3 g4 g5 g6 g7. ltac2:(SecDiet.SzSec.closeP 'blk_swap_hdr__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition hdr_copy_block__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (V B0 : Z) (jk : list byte),
    mem_inv ssegs m -> (0 <= V < 2^64)%Z -> (0 < B0)%Z -> (B0 + 8 <= bv_unsigned sp + -96)%Z -> (bv_unsigned sp < 2^64)%Z ->
    a0 = Z_to_bv 64 B0 ->
    rw_cells ssegs m (bv_unsigned sp + -96) [C8 (Z_to_bv 64 V)] ->
    rw_cells ssegs m B0 [CB 8 jk] ->
    evt ssegs (fun ms' => exists (a1' a2' a3' a4' a5' a6' : word) m',
        ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 (Z_to_bv 64 V) s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x16e54) fc None m' (seg_rom ssegs)
        /\ munch [(B0, B0 + 8)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
        /\ rw_cells ssegs m' B0 [CB 8 (le8 (Z_to_bv 64 V))]
        /\ rw_cells ssegs m' (bv_unsigned sp + -96) [C8 (Z_to_bv 64 V)])
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16e14) fc None m (seg_rom ssegs)).
Section Sz13.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m V B0 jk : ltac2:(SecDiet.SzSec.tyM 'hdr_copy_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma hdr_copy_block__body : ltac2:(SecDiet.SzSec.bodyP 'hdr_copy_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
  intros MI HV HB0 HB8 RSP -> HDR HB.
  pose proof (munch_refl [(B0, B0 + 8)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  do 7 step. do 9 bstep.
  apply evt_done. do 7 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [| exact HDR].
  eapply rw_cells_recell; [exact HB | cbn; repeat split; exact Logic.I |].
  cbn [cells_bytes cbytes app]. unfold le8, word_to_le_bytes. rewrite !unsigned_lit_wrap. rewrite !(Z.mod_small V) by lia.
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr by lia. rewrite !Z.shiftr_div_pow2 by lia.
  cbn [Z.add Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Pos.add]. rewrite app_nil_r.
  repeat match goal with |- (_ :: _) = (_ :: _) => f_equal end; try reflexivity; apply Z_to_bv8_mod; Z.div_mod_to_equations; lia.
Qed.
End Sz13.
Lemma hdr_copy_block : ltac:(let t := eval cbv delta [hdr_copy_block__stmt] in hdr_copy_block__stmt in exact t).
Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m V B0 jk. ltac2:(SecDiet.SzSec.closeP 'hdr_copy_block__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition trl_swap_block__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (A : Z) (u0 u1 u2 u3 : Z),
    mem_inv ssegs m -> (4 < A)%Z -> (A < 2^64)%Z ->
    (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> (0 <= u2 < 256)%Z -> (0 <= u3 < 256)%Z ->
    a0 = Z_to_bv 64 A -> a4 = sx32 (Z_to_bv 64 (le4val u0 u1 u2 u3)) ->
    rw_cells ssegs m (A + -4) [C4 (Z_to_bv 64 (le4val u0 u1 u2 u3))] ->
    evt ssegs (fun ms' => exists (a1' a2' a4' a5' : word) (hi : Z) m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x16ebc) fc None m' (seg_rom ssegs)
        /\ munch [(A + -4, A)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
        /\ rw_cells ssegs m' (A + -4) [C4 (Z_to_bv 64 (le4val u3 u2 u1 u0))]
        /\ (bv_unsigned a4' = le4val u3 u2 u1 u0 + 4294967296 * hi)%Z /\ (0 <= hi < 2^32)%Z)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16e8c) fc None m (seg_rom ssegs)).
Section Sz14.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A u0 u1 u2 u3 : ltac2:(SecDiet.SzSec.tyM 'trl_swap_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma trl_swap_block__body : ltac2:(SecDiet.SzSec.bodyP 'trl_swap_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
  intros MI HA1 HA2 B0 B1 B2 B3 -> -> TR.
  pose proof (munch_refl [(A + -4, A)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  do 12 step.
  apply evt_done. do 4 eexists. exists (u1 + 256 * u2 + 65536 * u3 + 16777216 * (((u3 / 128) * 4294967295) mod 256))%Z. eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [| split; [| Z.div_mod_to_equations; lia]].
  - eapply rw_cells_recell; [exact TR | cbn; repeat split; exact Logic.I |].
    cbn [cells_bytes cbytes app].
    rewrite (le4_lit u3 u2 u1 u0) by lia.
    rewrite (le4_of_val _ u3 u2 u1 u0 (u1 + 256 * u2 + 65536 * u3 + 16777216 * (((u3 / 128) * 4294967295) mod 256)));
      [reflexivity | lia | lia | lia | lia | Z.div_mod_to_equations; lia
       | apply (swap32_val _ u0 u1 u2 u3); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
  - rewrite (swap32_val _ u0 u1 u2 u3 ((u3 / 128) * 4294967295)); [unfold le4val; lia | lia | lia | lia | lia | Z.div_mod_to_equations; lia |].
    rewrite unsigned_sx32 by lia. unfold sxv, le4val. lia.
Qed.
End Sz14.
Lemma trl_swap_block : ltac:(let t := eval cbv delta [trl_swap_block__stmt] in trl_swap_block__stmt in exact t).
Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A u0 u1 u2 u3. ltac2:(SecDiet.SzSec.closeP 'trl_swap_block__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End WithCeil.


Close Scope bv_scope.
Section WithCeil.
Context {CEILV : CEIL}.
Lemma firstn_len_app : forall {X} (l1 l2 : list X), firstn (length l1) (l1 ++ l2) = l1.
Proof using Type. pin_using tt. intros X l1 l2. rewrite firstn_app, Nat.sub_diag, firstn_all by lia. cbn. apply app_nil_r. Qed.
Lemma skipn_len_app : forall {X} (l1 l2 : list X), skipn (length l1) (l1 ++ l2) = l2.
Proof using Type. pin_using tt. intros X l1 l2. rewrite skipn_app, Nat.sub_diag, skipn_all by lia. reflexivity. Qed.
Lemma firstn_len_app' : forall {X} (l1 l2 : list X) n, n = length l1 -> firstn n (l1 ++ l2) = l1.
Proof using Type. pin_using tt. intros X l1 l2 n ->. apply firstn_len_app. Qed.
(* [comment removed for export] *)
Lemma swap_field_last4 : forall (pre : list Z) a b c d tl, Z.of_nat (length pre) = tl - 4 ->
  swap_field 4 (tl - 4) (pre ++ [a; b; c; d]) = pre ++ [d; c; b; a].
Proof using Type. pin_using tt.
  intros pre a b c d tl HL. unfold swap_field, buf_write_at, zslice, zfirstn, zskipn, zlength.
  replace (Z.to_nat (tl - 4)) with (length pre) by lia. change (Z.to_nat 4) with 4%nat.
  rewrite firstn_len_app, skipn_len_app. cbn [firstn length Z.of_nat Pos.of_succ_nat Pos.succ rev app].
  rewrite skipn_all2 by (rewrite length_app; cbn; lia). cbn [app]. reflexivity.
Qed.
Lemma get_le32_last4 : forall (pre : list Z) a b c d tl, Z.of_nat (length pre) = tl - 4 ->
  get_le32 (pre ++ [a; b; c; d]) (tl - 4) = le4val a b c d.
Proof using Type. pin_using tt.
  intros pre a b c d tl HL. unfold get_le32, zslice, zfirstn, zskipn.
  replace (Z.to_nat (tl - 4)) with (length pre) by lia. change (Z.to_nat 4) with 4%nat. rewrite skipn_len_app. cbn. unfold le4val. lia.
Qed.

(* [comment removed for export] *)
Definition realloc_prefix__stmt : Prop := forall (data : list Z) (bs junk : list byte) (sz tl : Z),
  firstn (length data) bs = map b8 data -> Z.of_nat (length data) <= sz -> length bs = Z.to_nat sz -> 0 <= tl ->
  firstn (length (firstn (Z.to_nat tl) data)) (firstn (Z.to_nat (Z.min sz tl)) bs ++ junk) = map b8 (firstn (Z.to_nat tl) data).
Section Sz20.
Variables data bs junk sz tl : ltac2:(SecDiet.SzSec.tyM 'realloc_prefix__stmt "vvvvv" @data).
Lemma realloc_prefix__body : ltac2:(SecDiet.SzSec.bodyP 'realloc_prefix__stmt "vvvvv").
Proof using Type. pin_using tt.
  intros PF LD LB TL.
  rewrite length_firstn. rewrite firstn_app, length_firstn.
  replace (Nat.min (Z.to_nat tl) (length data) - Nat.min (Z.to_nat (Z.min sz tl)) (length bs))%nat with 0%nat by lia.
  cbn [firstn]. rewrite app_nil_r, firstn_firstn.
  replace (Nat.min (Nat.min (Z.to_nat tl) (length data)) (Z.to_nat (Z.min sz tl))) with (Nat.min (Z.to_nat tl) (length data)) by lia.
  rewrite <- firstn_map, <- PF, firstn_firstn. reflexivity.
Qed.
End Sz20.
Lemma realloc_prefix : ltac:(let t := eval cbv delta [realloc_prefix__stmt] in realloc_prefix__stmt in exact t).
Proof using Type. intros data bs junk sz tl. ltac2:(SecDiet.SzSec.closeP 'realloc_prefix__body "vvvvv"). Qed.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (S3.PcapRep.TwB.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma le4_le_bytes : forall x, 0 <= x < 2^32 -> le4 (Z_to_bv 64 x) = map b8 (le_bytes 4 x).
Proof using Type. pin_using tt.
  intros x Hx. unfold le_bytes. cbn [le_bytes_nat Z.to_nat Pos.to_nat Pos.iter_op Nat.add map].
  rewrite (le4_of_val _ (x mod 256) (x / 256 mod 256) (x / 256 / 256 mod 256) (x / 256 / 256 / 256 mod 256) 0);
    [reflexivity | | | | | lia |]; try (Z.div_mod_to_equations; lia).
  rewrite unsigned_lit by lia. Z.div_mod_to_equations. lia.
Qed.

Lemma le8_two : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^32 ->
  le8 (Z_to_bv 64 (x + 4294967296 * y)) = map b8 (le_bytes 4 x ++ le_bytes 4 y).
Proof using Type. pin_using tt.
  intros x y Hx Hy.
  replace (Z_to_bv 64 (x + 4294967296 * y)) with (pack2 (Z_to_bv 64 x) (Z_to_bv 64 y))
    by (unfold pack2; rewrite !unsigned_lit by lia; rewrite !Z.mod_small by lia; reflexivity).
  rewrite le8_pack2, map_app, !le4_le_bytes by lia. reflexivity.
Qed.

Lemma le4_mod32 : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^32 -> le4 (Z_to_bv 64 (x + 4294967296 * y)) = le4 (Z_to_bv 64 x).
Proof using Type. pin_using tt.
  intros x y Hx Hy. unfold le4. rewrite !unsigned_lit by lia.
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr, !Z.shiftr_div_pow2 by lia. cbn [Z.add Z.pow Z.pow_pos Pos.iter Z.mul].
  f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|]. f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|].
  f_equal; [apply Z_to_bv8_mod; Z.div_mod_to_equations; lia|]. f_equal. apply Z_to_bv8_mod. Z.div_mod_to_equations; lia.
Qed.

Lemma le_bytes_4_range : forall x, Forall (fun z => 0 <= z < 256) (le_bytes 4 x).
Proof using Type. pin_using tt.
  intros x. unfold le_bytes. cbn [le_bytes_nat Z.to_nat Pos.to_nat Pos.iter_op Nat.add].
  repeat constructor; Z.div_mod_to_equations; lia.
Qed.
Lemma length_le_bytes : forall k x, length (le_bytes k x) = Z.to_nat k.
Proof using Type. pin_using tt. intros k x. unfold le_bytes. generalize x. induction (Z.to_nat k) as [|n IH]; intros; cbn; [reflexivity| now rewrite IH]. Qed.

Lemma lastn4 : forall {A} (l : list A), (4 <= length l)%nat -> exists l1 a b c d, l = l1 ++ [a; b; c; d] /\ length l1 = (length l - 4)%nat.
Proof using Type. pin_using tt.
  intros A l Hl. exists (firstn (length l - 4) l).
  pose proof (firstn_skipn (length l - 4) l) as E.
  pose proof (length_skipn (length l - 4) l) as L.
  destruct (skipn (length l - 4) l) as [|a [|b [|c [|d [|e r]]]]]; cbn in L; try lia.
  exists a, b, c, d. split; [symmetry; exact E| rewrite length_firstn; lia].
Qed.

(* [comment removed for export] *)
Lemma Z_to_bv_s32_inj : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^32 -> Z_to_bv 64 (s32 x) = Z_to_bv 64 (s32 y) -> x = y.
Proof using Type. pin_using tt.
  intros x y Hx Hy E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit_wrap in E. unfold s32 in E.
  Z.div_mod_to_equations. lia.
Qed.
Lemma eqb_s32 : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^32 -> bv_eqb (Z_to_bv 64 (s32 x)) (Z_to_bv 64 (s32 y)) = (x =? y).
Proof using Type. pin_using tt.
  intros x y Hx Hy. destruct (Z.eqb_spec x y) as [->|NE]; [apply Z.eqb_refl|].
  unfold bv_eqb. apply Z.eqb_neq. intros E. apply NE. apply (Z_to_bv_s32_inj x y Hx Hy). apply bv_eq. exact E.
Qed.

(* [comment removed for export] *)
Lemma swrap32_low : forall u x hi, u = x + 4294967296 * hi -> Z_to_bv 64 (bv_swrap 32 (u + 0)) = Z_to_bv 64 (s32 x).
Proof using Type. pin_using tt.
  intros u x hi ->. f_equal. unfold bv_swrap, bv_wrap, s32, bv_half_modulus, bv_modulus. cbn -[Z.add Z.sub Z.modulo Z.mul].
  Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma shl_shr_32 : forall u x hi, u = x + 4294967296 * hi -> 0 <= x < 2^32 -> 0 <= hi ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl u 32))) 32) = Z_to_bv 64 x.
Proof using Type. pin_using tt.
  intros u x hi -> Hx Hhi. f_equal. rewrite Z.shiftl_mul_pow2, unsigned_lit_wrap, Z.shiftr_div_pow2 by lia.
  Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma land3_low : forall u x hi, u = x + 4294967296 * hi -> 0 <= x -> 0 <= hi -> Z.land u 3 = x mod 4.
Proof using Type. pin_using tt.
  intros u x hi -> Hx Hhi. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2^2) with 4. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
End WithCeil.

Ltac fix_sb :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
           change (le1 w) with [Z_to_bv 8 (bv_unsigned w)]; mem_after_store
       end).
Ltac bstep := step; fix_sb.

Open Scope bv_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition blk_swap_hdr__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (g0 g1 g2 g3 g4 g5 g6 g7 : Z),
    mem_inv usegs m -> (96 <= bv_unsigned sp)%Z ->
    (0 <= g0 < 256)%Z -> (0 <= g1 < 256)%Z -> (0 <= g2 < 256)%Z -> (0 <= g3 < 256)%Z ->
    (0 <= g4 < 256)%Z -> (0 <= g5 < 256)%Z -> (0 <= g6 < 256)%Z -> (0 <= g7 < 256)%Z ->
    rw_cells usegs m (bv_unsigned sp + -96) [C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); C4 (Z_to_bv 64 (le4val g4 g5 g6 g7))] ->
    evt usegs (fun ms' => exists (a0' a1' a2' a3' a4' a5' : word) (hi : Z) m',
        ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x171f4) fc None m' (seg_rom usegs)
        /\ munch [(bv_unsigned sp + -96, bv_unsigned sp + -88)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
        /\ rw_cells usegs m' (bv_unsigned sp + -96) [C4 (Z_to_bv 64 (le4val g3 g2 g1 g0)); C4 (Z_to_bv 64 (le4val g7 g6 g5 g4))]
        /\ (bv_unsigned a0' = le4val g7 g6 g5 g4 + 4294967296 * hi)%Z /\ (0 <= hi < 2^32)%Z)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x17194) fc None m (seg_rom usegs)).
Section Sz12.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m g0 g1 g2 g3 g4 g5 g6 g7 : ltac2:(SecDiet.SzSec.tyM 'blk_swap_hdr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma blk_swap_hdr__body : ltac2:(SecDiet.SzSec.bodyP 'blk_swap_hdr__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
 intros MI SPL B0 B1 B2 B3 B4 B5 B6 B7 FR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP.
  pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp + -88)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  do 24 step.
  apply evt_done. do 6 eexists. exists (g5 + 256 * g6 + 65536 * g7 + 16777216 * (((g7 / 128) * 4294967295) mod 256))%Z. eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [| split; [| Z.div_mod_to_equations; lia]].
  - eapply rw_cells_recell; [exact FR | cbn; repeat split; exact Logic.I |].
    cbn [cells_bytes cbytes app].
    rewrite (le4_lit g3 g2 g1 g0), (le4_lit g7 g6 g5 g4) by lia.
    rewrite (le4_of_val _ g3 g2 g1 g0 (g1 + 256 * g2 + 65536 * g3 + 16777216 * (((g3 / 128) * 4294967295) mod 256)));
      [| lia | lia | lia | lia | Z.div_mod_to_equations; lia
       | apply (swap32_val _ g0 g1 g2 g3); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
    rewrite (le4_of_val _ g7 g6 g5 g4 (g5 + 256 * g6 + 65536 * g7 + 16777216 * (((g7 / 128) * 4294967295) mod 256)));
      [| lia | lia | lia | lia | Z.div_mod_to_equations; lia
       | apply (swap32_val _ g4 g5 g6 g7); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
    reflexivity.
  - rewrite (swap32_val _ g4 g5 g6 g7 ((g7 / 128) * 4294967295)); [unfold le4val; lia | lia | lia | lia | lia | Z.div_mod_to_equations; lia |].
    rewrite unsigned_sx32 by lia. unfold sxv, le4val. lia.
Qed.
End Sz12.
Lemma blk_swap_hdr : ltac:(let t := eval cbv delta [blk_swap_hdr__stmt] in blk_swap_hdr__stmt in exact t).
Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m g0 g1 g2 g3 g4 g5 g6 g7. ltac2:(SecDiet.SzSec.closeP 'blk_swap_hdr__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition hdr_copy_block__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (V B0 : Z) (jk : list byte),
    mem_inv usegs m -> (0 <= V < 2^64)%Z -> (0 < B0)%Z -> (B0 + 8 < 2^64)%Z ->
    rw_cells usegs m B0 [CB 8 jk] ->
    evt usegs (fun ms' => exists (a1' a2' a3' a4' a5' a6' : word) m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B0) a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 (Z_to_bv 64 V) s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x17378) fc None m' (seg_rom usegs)
        /\ munch [(B0, B0 + 8)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
        /\ rw_cells usegs m' B0 [CB 8 (le8 (Z_to_bv 64 V))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 V) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1733c) fc None m (seg_rom usegs)).
Section Sz13.
Variables ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m V B0 jk : ltac2:(SecDiet.SzSec.tyM 'hdr_copy_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma hdr_copy_block__body : ltac2:(SecDiet.SzSec.bodyP 'hdr_copy_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
 intros MI HV HB0 HB8 HB.
  pose proof (munch_refl [(B0, B0 + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  do 6 step. do 9 bstep.
  apply evt_done. do 7 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  eapply rw_cells_recell; [exact HB | cbn; repeat split; exact Logic.I |].
  cbn [cells_bytes cbytes app]. unfold le8, word_to_le_bytes. rewrite !unsigned_lit_wrap. rewrite !(Z.mod_small V) by lia.
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr by lia. rewrite !Z.shiftr_div_pow2 by lia.
  cbn [Z.add Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Pos.add]. rewrite app_nil_r.
  repeat match goal with |- (_ :: _) = (_ :: _) => f_equal end; try reflexivity; apply Z_to_bv8_mod; Z.div_mod_to_equations; lia.
Qed.
End Sz13.
Lemma hdr_copy_block : ltac:(let t := eval cbv delta [hdr_copy_block__stmt] in hdr_copy_block__stmt in exact t).
Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m V B0 jk. ltac2:(SecDiet.SzSec.closeP 'hdr_copy_block__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition trl_swap_block__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (A : Z) (u0 u1 u2 u3 : Z),
    mem_inv usegs m -> (0 < A)%Z -> (A + 4 < 2^64)%Z ->
    (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> (0 <= u2 < 256)%Z -> (0 <= u3 < 256)%Z ->
    a0 = Z_to_bv 64 A ->
    rw_cells usegs m A [C4 (Z_to_bv 64 (le4val u0 u1 u2 u3))] ->
    evt usegs (fun ms' => exists (a1' a2' a4' a5' : word) m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x17458) fc None m' (seg_rom usegs)
        /\ munch [(A, A + 4)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
        /\ rw_cells usegs m' A [C4 (Z_to_bv 64 (le4val u3 u2 u1 u0))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x173d0) fc None m (seg_rom usegs)).
Section Sz14.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A u0 u1 u2 u3 : ltac2:(SecDiet.SzSec.tyM 'trl_swap_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma trl_swap_block__body : ltac2:(SecDiet.SzSec.bodyP 'trl_swap_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
 intros MI HA1 HA2 B0 B1 B2 B3 -> TR.
  pose proof (munch_refl [(A, A + 4)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  do 14 step.
  apply evt_done. do 5 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  eapply rw_cells_recell; [exact TR | cbn; repeat split; exact Logic.I |].
  cbn [cells_bytes cbytes app].
  rewrite (le4_lit u3 u2 u1 u0) by lia.
  rewrite (le4_of_val _ u3 u2 u1 u0 (u1 + 256 * u2 + 65536 * u3 + 16777216 * (((u3 / 128) * 4294967295) mod 256)));
    [reflexivity | lia | lia | lia | lia | Z.div_mod_to_equations; lia
     | apply (swap32_val _ u0 u1 u2 u3); [lia|lia|lia|lia| Z.div_mod_to_equations; lia | rewrite unsigned_sx32 by lia; unfold sxv, le4val; lia]].
Qed.
End Sz14.
Lemma trl_swap_block : ltac:(let t := eval cbv delta [trl_swap_block__stmt] in trl_swap_block__stmt in exact t).
Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A u0 u1 u2 u3. ltac2:(SecDiet.SzSec.closeP 'trl_swap_block__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Lemma geu_lits_false : forall x y, (0 <= x < y)%Z -> (y < 2^64)%Z -> negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) = false.
Proof using Type. pin_using tt. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. Qed.
Lemma ltu_lits_false : forall x y, (0 <= y <= x)%Z -> (x < 2^64)%Z -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof using Type. pin_using tt. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia. Qed.
End WithCeil.


Close Scope bv_scope.
Section WithCeil.
Context {CEILV : CEIL}.
Lemma firstn_len_app : forall {X} (l1 l2 : list X), firstn (length l1) (l1 ++ l2) = l1.
Proof using Type. pin_using tt. intros X l1 l2. rewrite firstn_app, Nat.sub_diag, firstn_all by lia. cbn. apply app_nil_r. Qed.
Lemma skipn_len_app : forall {X} (l1 l2 : list X), skipn (length l1) (l1 ++ l2) = l2.
Proof using Type. pin_using tt. intros X l1 l2. rewrite skipn_app, Nat.sub_diag, skipn_all by lia. reflexivity. Qed.
Lemma firstn_len_app' : forall {X} (l1 l2 : list X) n, n = length l1 -> firstn n (l1 ++ l2) = l1.
Proof using Type. pin_using tt. intros X l1 l2 n ->. apply firstn_len_app. Qed.
(* [comment removed for export] *)
Lemma swap_field_last4 : forall (pre : list Z) a b c d tl, Z.of_nat (length pre) = tl - 4 ->
  swap_field 4 (tl - 4) (pre ++ [a; b; c; d]) = pre ++ [d; c; b; a].
Proof using Type. pin_using tt.
  intros pre a b c d tl HL. unfold swap_field, buf_write_at, zslice, zfirstn, zskipn, zlength.
  replace (Z.to_nat (tl - 4)) with (length pre) by lia. change (Z.to_nat 4) with 4%nat.
  rewrite firstn_len_app, skipn_len_app. cbn [firstn length Z.of_nat Pos.of_succ_nat Pos.succ rev app].
  rewrite skipn_all2 by (rewrite length_app; cbn; lia). cbn [app]. reflexivity.
Qed.
Lemma get_le32_last4 : forall (pre : list Z) a b c d tl, Z.of_nat (length pre) = tl - 4 ->
  get_le32 (pre ++ [a; b; c; d]) (tl - 4) = le4val a b c d.
Proof using Type. pin_using tt.
  intros pre a b c d tl HL. unfold get_le32, zslice, zfirstn, zskipn.
  replace (Z.to_nat (tl - 4)) with (length pre) by lia. change (Z.to_nat 4) with 4%nat. rewrite skipn_len_app. cbn. unfold le4val. lia.
Qed.

(* [comment removed for export] *)
Definition realloc_prefix__stmt : Prop := forall (data : list Z) (bs junk : list byte) (sz tl : Z),
  firstn (length data) bs = map b8 data -> Z.of_nat (length data) <= sz -> length bs = Z.to_nat sz -> 0 <= tl ->
  firstn (length (firstn (Z.to_nat tl) data)) (firstn (Z.to_nat (Z.min sz tl)) bs ++ junk) = map b8 (firstn (Z.to_nat tl) data).
Section Sz22.
Variables data bs junk sz tl : ltac2:(SecDiet.SzSec.tyM 'realloc_prefix__stmt "vvvvv" @data).
Lemma realloc_prefix__body : ltac2:(SecDiet.SzSec.bodyP 'realloc_prefix__stmt "vvvvv").
Proof using Type. pin_using tt.
  intros PF LD LB TL.
  rewrite length_firstn. rewrite firstn_app, length_firstn.
  replace (Nat.min (Z.to_nat tl) (length data) - Nat.min (Z.to_nat (Z.min sz tl)) (length bs))%nat with 0%nat by lia.
  cbn [firstn]. rewrite app_nil_r, firstn_firstn.
  replace (Nat.min (Nat.min (Z.to_nat tl) (length data)) (Z.to_nat (Z.min sz tl))) with (Nat.min (Z.to_nat tl) (length data)) by lia.
  rewrite <- firstn_map, <- PF, firstn_firstn. reflexivity.
Qed.
End Sz22.
Lemma realloc_prefix : ltac:(let t := eval cbv delta [realloc_prefix__stmt] in realloc_prefix__stmt in exact t).
Proof using Type. intros data bs junk sz tl. ltac2:(SecDiet.SzSec.closeP 'realloc_prefix__body "vvvvv"). Qed.

End WithCeil.
End TwB.
End F_sfpcapng_blkA.

(* [comment removed for export] *)
Module FuzzKit.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithCeil.
Context {CEILV : CEIL}.
Lemma sx32_small : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof using Type. pin_using tt.
  intros x Hx. unfold sx32. f_equal. rewrite unsigned_lit by lia. rewrite bv_swrap32_eq.
  rewrite Z.mod_small by lia. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Outfile.
  Context {H hptr : Type} (K : modkit H hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.

  Lemma GIo_set_outfile : forall R (s : PState H hptr) CL FB m m' (o : option hptr) W,
    GIo K R s CL FB m -> munch ((0x339c0, 0x339c8) :: W) m m' -> wmono ssegs m m' ->
    Forall (client_iv R CL) W ->
    match o with
    | None => rw_cells ssegs m' 0x339c0 [C8 (Z_to_bv 64 0)]
    | Some q => exists A, In (q, A, 1264) FB /\ rw_cells ssegs m' 0x339c0 [C8 (Z_to_bv 64 A)]
    end ->
    GIo K R (set_outfile o s) CL FB m'.
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt).
    intros R s CL FB m m' o W G MU WM HW HO'.
    destruct G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof BOK as BOK'. destruct BOK' as [BO BA].
    pose proof (blocks_apart_app_inv _ _ BA) as (BA1 & BA2 & BAX).
    apply Forall_app in BO. destruct BO as [BO1 BO2].
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    assert (OUT : forall a, 0 <= a < 2^64 -> ~ (0x339c0 <= a < 0x339c8) ->
              (a < rc_lo R \/ (rc_spmain R <= a)) -> ~ in_block CL a -> outside ((0x339c0, 0x339c8) :: W) a).
    { intros a Ha Hne H1 H2. cbn [outside]. split; [cbn [fst snd]; lia|]. eapply outside_of_Forall; [exact HW|]. intros [lo hi] [Hs|Hb]; [cbn [fst snd] in Hs |- *; lia|]. cbn [fst snd].
      intros Hin. apply H2. unfold iv_in_block in Hb. apply Exists_exists in Hb as (b & HbIn & Hb1 & Hb2). cbn [fst snd] in Hb1, Hb2.
      unfold in_block. apply Exists_exists. exists b. split; [exact HbIn | lia]. }
    assert (NIB : forall a, (0x10000 <= a < 0x55000 \/ CEILZ <= a \/ (utp R - 200 <= a < utp R - 200 + 4096) \/ in_block FB a) -> ~ in_block CL a).
    { intros a Ha Hin. unfold in_block in Hin. apply Exists_exists in Hin as (b & HbIn & Hb).
      pose proof (proj1 (Forall_forall _ _) BO1 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; try lia.
      apply Exists_exists in Ha as (b' & Hb'In & Hb'). pose proof (BAX b b' HbIn Hb'In) as AP. unfold apart in AP. lia. }
    assert (LO : rc_lo R >= CEILZ). { unfold rc_lo in *. lia. } pose proof LO as LOu__; unfold rc_lo in LOu__.   (* [comment removed for export] *)
    unfold rc_spmain in *.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact Etls|split; [exact TB|split; [exact BOK|exact SPW]]]]]]]]]]]]; cbn [ps_heap ps_libc ps_outfile set_outfile].
    - eapply HFL; [exact HH|exact MU|exact WM|].
      apply Forall_cons; [unfold heap_client_iv; right; right; left; cbn [fst snd]; lia|].
      apply Forall_forall. intros [lo' hi'] Hiv. unfold heap_client_iv. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as [Hs|Hb]; cbn [fst snd] in *.
      + left. unfold rc_lo in *. lia.
      + right; left. unfold iv_in_block in *. rewrite Exists_app. left. exact Hb.
    - eapply SFL; [exact HS|]. eapply agrees_on_of_munch; [exact MU|exact WM|].
      intros a Ha Hfp. unfold stdio_fp, stdio_static in Hfp.
      destruct Hfp as [Hst|Hfb].
      + apply OUT; [exact Ha| lia | left; lia | apply NIB; lia].
      + apply Exists_exists in Hfb as (b & HbIn & Hb). pose proof (proj1 (Forall_forall _ _) BO2 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
        apply OUT; [exact Ha| lia | left; lia | apply NIB]. right; right; right. apply Exists_exists. exists b. auto.
    - (* [comment removed for export] *)
      destruct HA as ((ib & HAi) & (ej & HAe) & _). split; [|split].
      + exists ib. eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU|exact WM|intros a Ha Hp; exact (Hp Ha)] | exact HAi |].
        intros a Hp Ha. cbn in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
      + exists ej. eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU|exact WM|intros a Ha Hp; exact (Hp Ha)] | exact HAe |].
        intros a Hp Ha. cbn in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
      + destruct o as [q|]; exact HO'.
    - eapply CORE_TLS_agree; [| |exact CT]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_tls_fp in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
    - eapply PCAP_TLS_agree; [| |exact PT]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold pcap_tls_fp in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
    - eapply CORE_LIBC_agree; [| |exact CLI]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_libc_fp in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
    - eapply CORE_MISC_agree; [| |exact CM]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_misc_fp in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
    - eapply CORE_EXIT_agree; [| |exact CE]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_exit_fp in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
    - eapply CORE_STK_agree; [| |exact CS]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_stk_fp in Hp. apply OUT; [exact Ha|lia|right; lia|apply NIB; lia].
  Qed.
End Outfile.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.MLeaf.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithCeil.
Context {CEILV : CEIL}.
Lemma sx32_small : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof using Type. pin_using tt.
  intros x Hx. unfold sx32. f_equal. rewrite unsigned_lit by lia. rewrite bv_swrap32_eq.
  rewrite Z.mod_small by lia. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Outfile.
  Context {H hptr : Type} (K : modkit H hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.

  Definition GIo_set_outfile__stmt : Prop := forall R (s : PState H hptr) CL FB m m' (o : option hptr) W,
    GIo K R s CL FB m -> munch ((0x34180, 0x34188) :: W) m m' -> wmono usegs m m' ->
    Forall (client_iv R CL) W ->
    match o with
    | None => rw_cells usegs m' 0x34180 [C8 (Z_to_bv 64 0)]
    | Some q => exists A, In (q, A, 1264) FB /\ rw_cells usegs m' 0x34180 [C8 (Z_to_bv 64 A)]
    end ->
    GIo K R (set_outfile o s) CL FB m'.
  Section Sz2.
  Variables R s CL FB m m' o W : ltac2:(SecDiet.SzSec.tyM 'GIo_set_outfile__stmt "vvvvvvvv" @R).
  Lemma GIo_set_outfile__body : ltac2:(SecDiet.SzSec.bodyP 'GIo_set_outfile__stmt "vvvvvvvv").
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt).
    intros G MU WM HW HO'.
    destruct G as (HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW). (let X := fresh "SPWu__" in pose proof SPW as X; unfold rc_lo in X).   (* [comment removed for export] *)
    pose proof BOK as BOK'. destruct BOK' as [BO BA].
    pose proof (blocks_apart_app_inv _ _ BA) as (BA1 & BA2 & BAX).
    apply Forall_app in BO. destruct BO as [BO1 BO2].
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    assert (OUT : forall a, 0 <= a < 2^64 -> ~ (0x34180 <= a < 0x34188) ->
              (a < rc_lo R \/ (rc_spmain R <= a)) -> ~ in_block CL a -> outside ((0x34180, 0x34188) :: W) a).
    { intros a Ha Hne H1 H2. cbn [outside]. split; [cbn [fst snd]; lia|]. eapply outside_of_Forall; [exact HW|]. intros [lo hi] [Hs|Hb]; [cbn [fst snd] in Hs |- *; lia|]. cbn [fst snd].
      intros Hin. apply H2. unfold iv_in_block in Hb. apply Exists_exists in Hb as (b & HbIn & Hb1 & Hb2). cbn [fst snd] in Hb1, Hb2.
      unfold in_block. apply Exists_exists. exists b. split; [exact HbIn | lia]. }
    assert (NIB : forall a, (0x10000 <= a < 0x56000 \/ CEILZ <= a \/ (utp R - 200 <= a < utp R - 200 + 4096) \/ in_block FB a) -> ~ in_block CL a).
    { intros a Ha Hin. unfold in_block in Hin. apply Exists_exists in Hin as (b & HbIn & Hb).
      pose proof (proj1 (Forall_forall _ _) BO1 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; try lia.
      apply Exists_exists in Ha as (b' & Hb'In & Hb'). pose proof (BAX b b' HbIn Hb'In) as AP. unfold apart in AP. lia. }
    assert (LO : rc_lo R >= CEILZ). { unfold rc_lo in *. lia. } pose proof LO as LOu__; unfold rc_lo in LOu__.   (* [comment removed for export] *)
    unfold rc_spmain in *.
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact Etls|split; [exact TB|split; [exact BOK|exact SPW]]]]]]]]]]]]; cbn [ps_heap ps_libc ps_outfile set_outfile].
    - eapply HFL; [exact HH|exact MU|exact WM|].
      apply Forall_cons; [unfold heap_client_iv; right; right; left; cbn [fst snd]; lia|].
      apply Forall_forall. intros [lo' hi'] Hiv. unfold heap_client_iv. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as [Hs|Hb]; cbn [fst snd] in *.
      + left. unfold rc_lo in *. lia.
      + right; left. unfold iv_in_block in *. rewrite Exists_app. left. exact Hb.
    - eapply SFL; [exact HS|]. eapply agrees_on_of_munch; [exact MU|exact WM|].
      intros a Ha Hfp. unfold stdio_fp, stdio_static in Hfp.
      destruct Hfp as [Hst|Hfb].
      + apply OUT; [exact Ha| lia | left; lia | apply NIB; lia].
      + apply Exists_exists in Hfb as (b & HbIn & Hb). pose proof (proj1 (Forall_forall _ _) BO2 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
        apply OUT; [exact Ha| lia | left; lia | apply NIB]. right; right; right. apply Exists_exists. exists b. auto.
    - (* [comment removed for export] *)
      destruct HA as ((ib & HAi) & (ej & HAe) & _). split; [|split].
      + exists ib. eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU|exact WM|intros a Ha Hp; exact (Hp Ha)] | exact HAi |].
        intros a Hp Ha. cbn in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
      + exists ej. eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU|exact WM|intros a Ha Hp; exact (Hp Ha)] | exact HAe |].
        intros a Hp Ha. cbn in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
      + destruct o as [q|]; exact HO'.
    - eapply CORE_TLS_agree; [| |exact CT]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_tls_fp in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
    - eapply PCAP_TLS_agree; [| |exact PT]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold pcap_tls_fp in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
    - eapply CORE_LIBC_agree; [| |exact CLI]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_libc_fp in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
    - eapply CORE_MISC_agree; [| |exact CM]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_misc_fp in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
    - eapply CORE_EXIT_agree; [| |exact CE]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_exit_fp in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
    - eapply CORE_STK_agree; [| |exact CS]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_stk_fp in Hp. apply OUT; [exact Ha|lia|right; lia|apply NIB; lia].
  Qed.
  End Sz2.
  Lemma GIo_set_outfile : ltac:(let t := eval cbv delta [GIo_set_outfile__stmt] in GIo_set_outfile__stmt in exact t).
  Proof using HFL SFL. intros R s CL FB m m' o W. ltac2:(SecDiet.SzSec.closeP 'GIo_set_outfile__body "vvvvvvvv"). Qed.
End Outfile.

End WithCeil.
End TwB.
End FuzzKit.

(* [comment removed for export] *)
Module F_sfpcapng_aiD.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (PcapRep.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition le8val (b0 b1 b2 b3 b4 b5 b6 b7 : Z) : Z :=
  b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 + 4294967296 * (b4 + 256 * b5 + 65536 * b6 + 16777216 * b7).

Lemma unsigned_b8 : forall u, 0 <= u < 256 -> bv_unsigned (Z_to_bv 8 u) = u.
Proof using Type. pin_using tt. intros u Hu. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma le_of_bytes_8 : forall b0 b1 b2 b3 b4 b5 b6 b7, le_of_bytes [b0; b1; b2; b3; b4; b5; b6; b7] = le8val b0 b1 b2 b3 b4 b5 b6 b7.
Proof using Type. pin_using tt. intros. cbn [le_of_bytes]. unfold le8val. lia. Qed.
#[using="Type"] Lemma dm256_div : forall r q, 0 <= r < 256 -> (r + 256 * q) / 256 = q.
Proof. intros r q Hr. rewrite (Z.mul_comm 256 q), Z.div_add by lia. rewrite Z.div_small by lia. lia. Qed.
#[using="Type"] Lemma dm256_mod : forall r q, 0 <= r < 256 -> (r + 256 * q) mod 256 = r.
Proof. intros r q Hr. rewrite (Z.mul_comm 256 q), Z.mod_add by lia. apply Z.mod_small. exact Hr. Qed.
Lemma bswap64_bytes : forall b0 b1 b2 b3 b4 b5 b6 b7,
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 -> 0 <= b7 < 256 ->
  bswap64 (le8val b0 b1 b2 b3 b4 b5 b6 b7) = le8val b7 b6 b5 b4 b3 b2 b1 b0.
Proof using Type. pin_using tt.
  intros. unfold bswap64, le_bytes. change (Z.to_nat 8) with 8%nat. cbn [le_bytes_nat rev app le_of_bytes].
  unfold le8val.
  set (V := b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 + 4294967296 * (b4 + 256 * b5 + 65536 * b6 + 16777216 * b7)).
  (* [comment removed for export] *)
  assert (EV : V = b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * (b4 + 256 * (b5 + 256 * (b6 + 256 * (b7 + 256 * 0)))))))) by (subst V; ring).
  rewrite EV; clear EV V.
  rewrite !dm256_div by assumption. rewrite !dm256_mod by assumption.
  lia.
Qed.


(* [comment removed for export] *)
Section Le8Bytes.
  Variables u0 u1 u2 u3 u4 u5 u6 u7 : Z.
  Hypothesis B0 : 0 <= u0 < 256. Hypothesis B1 : 0 <= u1 < 256. Hypothesis B2 : 0 <= u2 < 256. Hypothesis B3 : 0 <= u3 < 256.
  Hypothesis B4 : 0 <= u4 < 256. Hypothesis B5 : 0 <= u5 < 256. Hypothesis B6 : 0 <= u6 < 256. Hypothesis B7 : 0 <= u7 < 256.
  #[local] Notation V := (le8val u0 u1 u2 u3 u4 u5 u6 u7).
  Lemma le8_x0 : (V * 2 ^ 56) mod 2 ^ 64 = u0 * 2 ^ 56. Proof using B0. pin_using (fun (B0 : unit) => tt). unfold le8val. Z.div_mod_to_equations. lia. Qed.
  Lemma le8_x1 : (V / 256) mod 256 = u1. Proof using B0 B1. pin_using (fun (B0 B1 : unit) => tt). unfold le8val. Z.div_mod_to_equations. lia. Qed.
  Lemma le8_x2 : (V / 65536) mod 256 = u2. Proof using B0 B1 B2. pin_using (fun (B0 B1 B2 : unit) => tt). unfold le8val. Z.div_mod_to_equations. lia. Qed.
  Lemma le8_x3 : V mod 2 ^ 32 / 2 ^ 24 = u3. Proof using B0 B1 B2 B3. pin_using (fun (B0 B1 B2 B3 : unit) => tt). unfold le8val. Z.div_mod_to_equations. lia. Qed.
  Lemma le8_x4 : (V / 2 ^ 8) mod 2 ^ 32 / 2 ^ 24 = u4. Proof using B0 B1 B2 B3 B4. pin_using (fun (B0 B1 B2 B3 B4 : unit) => tt). unfold le8val. Z.div_mod_to_equations. lia. Qed.
  Lemma le8_x5 : (V / 2 ^ 24 / 65536) mod 256 = u5. Proof using B0 B1 B2 B3 B4 B5. pin_using (fun (B0 B1 B2 B3 B4 B5 : unit) => tt). unfold le8val. Z.div_mod_to_equations. lia. Qed.
  (* [comment removed for export] *)
  Lemma le8_x6 : (V / 2 ^ 40 / 256) mod 256 = u6. Proof using B0 B1 B2 B3 B4 B5 B6. pin_using (fun (B0 B1 B2 B3 B4 B5 B6 : unit) => tt). unfold le8val.
    rewrite Z.div_div by lia.
    assert (Q : (u0 + 256 * u1 + 65536 * u2 + 16777216 * u3 + 4294967296 * (u4 + 256 * u5 + 65536 * u6 + 16777216 * u7)) / (2 ^ 40 * 256)
                = u6 + 256 * u7).
    { symmetry; apply (Z.div_unique_pos _ _ _ (u0 + 256 * u1 + 65536 * u2 + 16777216 * u3 + 4294967296 * (u4 + 256 * u5))); lia. }
    rewrite Q. symmetry; apply (Z.mod_unique_pos _ _ u7 u6); lia. Qed.
  Lemma le8_x7 : V / 2 ^ 56 = u7. Proof using B0 B1 B2 B3 B4 B5 B6. pin_using (fun (B0 B1 B2 B3 B4 B5 B6 : unit) => tt). unfold le8val. Z.div_mod_to_equations. lia. Qed.
End Le8Bytes.

Section AID.
  Context {H hptr : Type} (K : modkit H hptr).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).

  (* [comment removed for export] *)
  Definition ai_AGP (sp : word) (C1 C2 : list cblk) (P B CUR EB : Z) (p : pcapT) (m m' : mem) : Prop :=
    agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + PCAP_PRIV_OFF <= a < P + PCAP_NG_SF_TOTAL)
                        /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256) /\ ~ (B <= a < B + pc_bufalloc p)) m m'.
  (* [comment removed for export] *)
  Definition ai_FRAME (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m' : mem) : Prop :=
    rw_cells ssegs m' (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Definition ai_REST (R : rctx) (C1 C2 FB : list cblk) (P B CUR EB : Z) (p : pcapT) (s : pcap_ng_sf) (c : cursor) (ej : list byte) (o : option hptr)
      (m' : mem) (st' : PS) (r : bool * cursor * pcapT * list Z) : Prop :=
    let '(ok, c', p', msg) := r in
    exists (s' : pcap_ng_sf) (i' : option hptr) (I' : Z) (pad' bs' : list byte),
      ps_outfile st' = o /\ p' = set_ng s' i' (set_bufdata (pc_bufdata p') p)
      /\ GIo K R st' (IBLK i' I' s' ++ C1 ++ C2) FB m'
      /\ rw_cells ssegs m' (P + PCAP_PRIV_OFF) (ng_cells s' I' pad')
      /\ ng_user_tsresol s' = ng_user_tsresol s /\ ng_max_blocksize s' = ng_max_blocksize s /\ 0 <= ng_ifcount s' < 2^32 /\ 0 <= ng_ifaces_size s' < 2^32
      /\ rw_cells ssegs m' B [CB (Z.to_nat (pc_bufalloc p)) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p')
      /\ length (pc_bufdata p') = length (pc_bufdata p) /\ Forall (fun z => 0 <= z < 256) (pc_bufdata p')
      /\ if ok then
           ifaces_ok p' I' m'
           /\ (exists cpad', rw_cells ssegs m' CUR (cursor_cells B c' cpad'))
           /\ 0 <= cur_remaining c' /\ cur_off c <= cur_off c' /\ cur_off c' + cur_remaining c' <= cur_off c + cur_remaining c
           /\ cur_block_type c' = cur_block_type c
           /\ rw_cells ssegs m' EB [CB 256 ej] /\ msg = []
         else
           ng_ifaces_closable s' i' I' m'
           /\ (exists ccs', rw_cells ssegs m' CUR ccs' /\ cells_size ccs' = 24%nat)
           /\ (exists junk'', rw_cells ssegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''])
           /\ Z.of_nat (length msg) < 256 /\ Forall (fun z => 0 < z < 256) msg.
  (* [comment removed for export] *)
  Definition ai_REST_F (R : rctx) (C1 C2 FB : list cblk) (P B CUR : Z) (p : pcapT) (s : pcap_ng_sf) (o : option hptr)
      (m' : mem) (st' : PS) (c' : cursor) (p' : pcapT) : Prop :=
    exists (s' : pcap_ng_sf) (i' : option hptr) (I' : Z) (pad' bs' : list byte),
      ps_outfile st' = o /\ p' = set_ng s' i' (set_bufdata (pc_bufdata p') p)
      /\ GIo K R st' (IBLK i' I' s' ++ C1 ++ C2) FB m'
      /\ rw_cells ssegs m' (P + PCAP_PRIV_OFF) (ng_cells s' I' pad')
      /\ ng_user_tsresol s' = ng_user_tsresol s /\ ng_max_blocksize s' = ng_max_blocksize s /\ 0 <= ng_ifcount s' < 2^32 /\ 0 <= ng_ifaces_size s' < 2^32
      /\ rw_cells ssegs m' B [CB (Z.to_nat (pc_bufalloc p)) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p')
      /\ length (pc_bufdata p') = length (pc_bufdata p) /\ Forall (fun z => 0 <= z < 256)%Z (pc_bufdata p')
      /\ ng_ifaces_closable s' i' I' m'
      /\ (exists ccs', rw_cells ssegs m' CUR ccs' /\ cells_size ccs' = 24%nat).
End AID.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (S3.PcapRep.TwB.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition le8val (b0 b1 b2 b3 b4 b5 b6 b7 : Z) : Z :=
  b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 + 4294967296 * (b4 + 256 * b5 + 65536 * b6 + 16777216 * b7).

Lemma unsigned_b8 : forall u, 0 <= u < 256 -> bv_unsigned (Z_to_bv 8 u) = u.
Proof using Type. pin_using tt. intros u Hu. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma le_of_bytes_8 : forall b0 b1 b2 b3 b4 b5 b6 b7, le_of_bytes [b0; b1; b2; b3; b4; b5; b6; b7] = le8val b0 b1 b2 b3 b4 b5 b6 b7.
Proof using Type. pin_using tt. intros. cbn [le_of_bytes]. unfold le8val. lia. Qed.
#[using="Type"] Lemma dm256_div : forall r q, 0 <= r < 256 -> (r + 256 * q) / 256 = q.
Proof. intros r q Hr. rewrite (Z.mul_comm 256 q), Z.div_add by lia. rewrite Z.div_small by lia. lia. Qed.
#[using="Type"] Lemma dm256_mod : forall r q, 0 <= r < 256 -> (r + 256 * q) mod 256 = r.
Proof. intros r q Hr. rewrite (Z.mul_comm 256 q), Z.mod_add by lia. apply Z.mod_small. exact Hr. Qed.
Lemma bswap64_bytes : forall b0 b1 b2 b3 b4 b5 b6 b7,
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 -> 0 <= b7 < 256 ->
  bswap64 (le8val b0 b1 b2 b3 b4 b5 b6 b7) = le8val b7 b6 b5 b4 b3 b2 b1 b0.
Proof using Type. pin_using tt.
  intros. unfold bswap64, le_bytes. change (Z.to_nat 8) with 8%nat. cbn [le_bytes_nat rev app le_of_bytes].
  unfold le8val.
  set (V := b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 + 4294967296 * (b4 + 256 * b5 + 65536 * b6 + 16777216 * b7)).
  (* [comment removed for export] *)
  assert (EV : V = b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * (b4 + 256 * (b5 + 256 * (b6 + 256 * (b7 + 256 * 0)))))))) by (subst V; ring).
  rewrite EV; clear EV V.
  rewrite !dm256_div by assumption. rewrite !dm256_mod by assumption.
  lia.
Qed.


(* [comment removed for export] *)
Section Le8Bytes.
  Variables u0 u1 u2 u3 u4 u5 u6 u7 : Z.
  Hypothesis B0 : 0 <= u0 < 256. Hypothesis B1 : 0 <= u1 < 256. Hypothesis B2 : 0 <= u2 < 256. Hypothesis B3 : 0 <= u3 < 256.
  Hypothesis B4 : 0 <= u4 < 256. Hypothesis B5 : 0 <= u5 < 256. Hypothesis B6 : 0 <= u6 < 256. Hypothesis B7 : 0 <= u7 < 256.
  #[local] Notation V := (le8val u0 u1 u2 u3 u4 u5 u6 u7).
  Lemma le8_x0 : (V * 2 ^ 56) mod 2 ^ 64 = u0 * 2 ^ 56. Proof using B0. pin_using (fun (B0 : unit) => tt). unfold le8val. Z.div_mod_to_equations. lia. Qed.
  Lemma le8_x1 : (V / 256) mod 256 = u1. Proof using B0 B1. pin_using (fun (B0 B1 : unit) => tt). unfold le8val. Z.div_mod_to_equations. lia. Qed.
  Lemma le8_x2 : (V / 65536) mod 256 = u2. Proof using B0 B1 B2. pin_using (fun (B0 B1 B2 : unit) => tt). unfold le8val. Z.div_mod_to_equations. lia. Qed.
  Lemma le8_x3 : V mod 2 ^ 32 / 2 ^ 24 = u3. Proof using B0 B1 B2 B3. pin_using (fun (B0 B1 B2 B3 : unit) => tt). unfold le8val. Z.div_mod_to_equations. lia. Qed.
  Lemma le8_x4 : (V / 2 ^ 8) mod 2 ^ 32 / 2 ^ 24 = u4. Proof using B0 B1 B2 B3 B4. pin_using (fun (B0 B1 B2 B3 B4 : unit) => tt). unfold le8val. Z.div_mod_to_equations. lia. Qed.
  Lemma le8_x5 : (V / 2 ^ 24 / 65536) mod 256 = u5. Proof using B0 B1 B2 B3 B4 B5. pin_using (fun (B0 B1 B2 B3 B4 B5 : unit) => tt). unfold le8val. Z.div_mod_to_equations. lia. Qed.
  (* [comment removed for export] *)
  Lemma le8_x6 : (V / 2 ^ 40 / 256) mod 256 = u6. Proof using B0 B1 B2 B3 B4 B5 B6. pin_using (fun (B0 B1 B2 B3 B4 B5 B6 : unit) => tt). unfold le8val.
    rewrite Z.div_div by lia.
    assert (Q : (u0 + 256 * u1 + 65536 * u2 + 16777216 * u3 + 4294967296 * (u4 + 256 * u5 + 65536 * u6 + 16777216 * u7)) / (2 ^ 40 * 256)
                = u6 + 256 * u7).
    { symmetry; apply (Z.div_unique_pos _ _ _ (u0 + 256 * u1 + 65536 * u2 + 16777216 * u3 + 4294967296 * (u4 + 256 * u5))); lia. }
    rewrite Q. symmetry; apply (Z.mod_unique_pos _ _ u7 u6); lia. Qed.
  Lemma le8_x7 : V / 2 ^ 56 = u7. Proof using B0 B1 B2 B3 B4 B5 B6. pin_using (fun (B0 B1 B2 B3 B4 B5 B6 : unit) => tt). unfold le8val. Z.div_mod_to_equations. lia. Qed.
End Le8Bytes.

Section AID.
  Context {H hptr : Type} (K : modkit H hptr).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).

  (* [comment removed for export] *)
  Definition ai_AGP (sp : word) (C1 C2 : list cblk) (P B CUR EB : Z) (p : pcapT) (m m' : mem) : Prop :=
    agrees_on (fun a => client_keeps (C1 ++ C2) (bv_unsigned sp) a /\ ~ (P + PCAP_PRIV_OFF <= a < P + PCAP_NG_SF_TOTAL)
                        /\ ~ (CUR <= a < CUR + 24) /\ ~ (EB <= a < EB + 256) /\ ~ (B <= a < B + pc_bufalloc p)) m m'.
  (* [comment removed for export] *)
  Definition ai_FRAME (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m' : mem) : Prop :=
    rw_cells usegs m' (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Definition ai_REST (R : rctx) (C1 C2 FB : list cblk) (P B CUR EB : Z) (p : pcapT) (s : pcap_ng_sf) (c : cursor) (ej : list byte) (o : option hptr)
      (m' : mem) (st' : PS) (r : bool * cursor * pcapT * list Z) : Prop :=
    let '(ok, c', p', msg) := r in
    exists (s' : pcap_ng_sf) (i' : option hptr) (I' : Z) (pad' bs' : list byte),
      ps_outfile st' = o /\ p' = set_ng s' i' (set_bufdata (pc_bufdata p') p)
      /\ GIo K R st' (IBLK i' I' s' ++ C1 ++ C2) FB m'
      /\ rw_cells usegs m' (P + PCAP_PRIV_OFF) (ng_cells s' I' pad')
      /\ ng_user_tsresol s' = ng_user_tsresol s /\ ng_max_blocksize s' = ng_max_blocksize s /\ 0 <= ng_ifcount s' < 2^32 /\ 0 <= ng_ifaces_size s' < 2^32
      /\ rw_cells usegs m' B [CB (Z.to_nat (pc_bufalloc p)) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p')
      /\ length (pc_bufdata p') = length (pc_bufdata p) /\ Forall (fun z => 0 <= z < 256) (pc_bufdata p')
      /\ if ok then
           ifaces_ok p' I' m'
           /\ (exists cpad', rw_cells usegs m' CUR (cursor_cells B c' cpad'))
           /\ 0 <= cur_remaining c' /\ cur_off c <= cur_off c' /\ cur_off c' + cur_remaining c' <= cur_off c + cur_remaining c
           /\ cur_block_type c' = cur_block_type c
           /\ rw_cells usegs m' EB [CB 256 ej] /\ msg = []
         else
           ng_ifaces_closable s' i' I' m'
           /\ (exists ccs', rw_cells usegs m' CUR ccs' /\ cells_size ccs' = 24%nat)
           /\ (exists junk'', rw_cells usegs m' EB [CB (length msg + 1) (map b8 msg ++ [Z_to_bv 8 0]); CB (255 - length msg) junk''])
           /\ Z.of_nat (length msg) < 256 /\ Forall (fun z => 0 < z < 256) msg.
  (* [comment removed for export] *)
  Definition ai_REST_F (R : rctx) (C1 C2 FB : list cblk) (P B CUR : Z) (p : pcapT) (s : pcap_ng_sf) (o : option hptr)
      (m' : mem) (st' : PS) (c' : cursor) (p' : pcapT) : Prop :=
    exists (s' : pcap_ng_sf) (i' : option hptr) (I' : Z) (pad' bs' : list byte),
      ps_outfile st' = o /\ p' = set_ng s' i' (set_bufdata (pc_bufdata p') p)
      /\ GIo K R st' (IBLK i' I' s' ++ C1 ++ C2) FB m'
      /\ rw_cells usegs m' (P + PCAP_PRIV_OFF) (ng_cells s' I' pad')
      /\ ng_user_tsresol s' = ng_user_tsresol s /\ ng_max_blocksize s' = ng_max_blocksize s /\ 0 <= ng_ifcount s' < 2^32 /\ 0 <= ng_ifaces_size s' < 2^32
      /\ rw_cells usegs m' B [CB (Z.to_nat (pc_bufalloc p)) bs'] /\ firstn (length (pc_bufdata p')) bs' = map b8 (pc_bufdata p')
      /\ length (pc_bufdata p') = length (pc_bufdata p) /\ Forall (fun z => 0 <= z < 256)%Z (pc_bufdata p')
      /\ ng_ifaces_closable s' i' I' m'
      /\ (exists ccs', rw_cells usegs m' CUR ccs' /\ cells_size ccs' = 24%nat).
End AID.

End WithCeil.
End TwB.
End F_sfpcapng_aiD.

(* [comment removed for export] *)
Module SfNgKit.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma length_list_ascii fs : length (list_ascii_of_string fs) = String.length fs.
Proof using Type. pin_using tt. induction fs as [|c fs IH]; cbn; [reflexivity| now rewrite IH]. Qed.
Lemma fmt_at_intro m A fs :
  mem_inv ssegs m ->
  ro_bytes_b ssegs A (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string fs) ++ [Z_to_bv 8 0]) = true ->
  0x10000 <= A -> A + Z.of_nat (String.length fs) + 1 <= 0x13000 -> fmt_at m A fs.
Proof using Type. pin_using tt.
  intros MI RO LO HI. split; [| lia].
  pose proof (ro_cells_image ssegs m A _ MI RO ltac:(lia)) as X. rewrite length_app, length_map, length_list_ascii in X. cbn [length] in X.
  pose proof (ro_cells_bytes_at _ _ _ _ (X ltac:(lia))) as Y. cbn [cells_bytes cbytes] in Y. rewrite app_nil_r in Y. exact Y.
Qed.

Lemma eqb_lits_eq : forall x y, x = y -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof using Type. pin_using tt. intros x y ->. unfold bv_eqb. apply Z.eqb_refl. Qed.

(* [comment removed for export] *)
End WithCeil.

Ltac transport H m' AG tac :=
  lazymatch type of H with rw_cells ?sg _ ?A ?cs =>
    let X := fresh in
    assert (X : rw_cells sg m' A cs) by (eapply agrees_rw_cells; [exact AG | exact H | tac]);
    clear H; rename X into H end.

Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac ienter := lazymatch goal with |- implM _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; unfold implM; iprefix.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma u32_s32 : forall v, u32 (s32 v) = u32 v.
Proof using Type. pin_using tt. intros v. unfold u32, s32. Z.div_mod_to_equations. lia. Qed.
Lemma s32_s32 : forall v, s32 (s32 v) = s32 v.
Proof using Type. pin_using tt. intros v. unfold s32. Z.div_mod_to_equations. lia. Qed.
Lemma s32_small : forall v, 0 <= v < 2^31 -> s32 v = v.
Proof using Type. pin_using tt. intros v Hv. unfold s32. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Definition conv32 (c : conv) : bool := match c with Cd | Cu | Cx | C08x => true | _ => false end.
Inductive aeq32 : conv -> farg -> farg -> Prop :=
| aeq_same c a : aeq32 c a a
| aeq_s32 c v : conv32 c = true -> aeq32 c (AInt (s32 v)) (AInt v).
Fixpoint convs (items : list fitem) : list conv :=
  match items with [] => [] | FConv c :: r => c :: convs r | _ :: r => convs r end.
Inductive pargs : list conv -> list farg -> list farg -> Prop :=
| pargs_nil cs : pargs cs [] []
| pargs_cons c cs a a' r r' : aeq32 c a a' -> pargs cs r r' -> pargs (c :: cs) (a :: r) (a' :: r').
Lemma conv_pieces_aeq : forall c a a', aeq32 c a a' -> conv_pieces c a = conv_pieces c a'.
Proof using Type. pin_using tt.
  intros c a a' Hq. destruct Hq as [c a| c v Hc]; [reflexivity|].
  destruct c; try discriminate Hc; cbn [conv_pieces]; rewrite ?u32_s32, ?s32_s32; reflexivity.
Qed.
Lemma fmt_pieces_pargs : forall items args args', pargs (convs items) args args' -> fmt_pieces items args = fmt_pieces items args'.
Proof using Type. pin_using tt.
  induction items as [|it items IH]; intros args args' Hp; [reflexivity|].
  destruct it as [l|c|sb]; cbn [fmt_pieces convs] in *.
  - f_equal. apply IH. exact Hp.
  - inversion Hp as [cs0 | c0 cs0 a0 a0' r r' Ha Hr]; subst.
    + reflexivity.
    + cbn [hd tl]. rewrite (conv_pieces_aeq _ _ _ Ha). f_equal. f_equal. apply IH. exact Hr.
  - reflexivity.
Qed.
Lemma snprintf_pargs : forall n fs args args', pargs (convs (fmt fs)) args args' -> Fmt.snprintf n fs args = Fmt.snprintf n fs args'.
Proof using Type. pin_using tt. intros n fs args args' Hp. unfold Fmt.snprintf, snprintf_out, fmt_output. rewrite (fmt_pieces_pargs _ _ _ Hp). reflexivity. Qed.

(* [comment removed for export] *)
Lemma unsigned_s32 : forall x, 0 <= x < 2^32 -> bv_unsigned (Z_to_bv 64 (s32 x)) = x + (x / 2^31) * (2^64 - 2^32).
Proof using Type. pin_using tt.
  intros x Hx. rewrite unsigned_lit_wrap. unfold s32. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
End WithCeil.

Ltac zc_lia := unfold le4val in *; Z.div_mod_to_equations; lia.
Ltac zc_base := first [ reflexivity | apply Z.ltb_lt; zc_lia | apply Z.ltb_ge; zc_lia | apply Z.leb_le; zc_lia | apply Z.leb_gt; zc_lia
                      | apply Z.eqb_eq; zc_lia | apply Z.eqb_neq; zc_lia ].
Ltac zc_rec := lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); zc_rec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); zc_rec
  | _ => zc_base end.
Ltac if_tf b := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with b; [cbv iota | symmetry; unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb]; fold_lit_ux; rewrite ?unsigned_s32 by (unfold le4val in *; lia); zc_rec] end.


Section WithCeil.
Context {CEILV : CEIL}.
Section KitK.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Lemma set_bufdata_twice : forall d d' (q : pcapT), set_bufdata d (set_bufdata d' q) = set_bufdata d q.
  Proof using Type. pin_using tt. intros. reflexivity. Qed.
  Lemma pc_bufdata_set : forall d (q : pcapT), pc_bufdata (set_bufdata d q) = d.
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma head_apart : forall R st (CL FB : list cblk) b b' m,
    GIo K R st (b :: CL) FB m -> In b' CL ->
    cb_addr b + cb_size b <= cb_addr b' \/ cb_addr b' + cb_size b' <= cb_addr b.
  Proof using Type. pin_using tt.
    intros R st CL FB b b' m G Hin. destruct (GIo_blocks K _ _ _ _ _ G) as [_ BA].
    change ((b :: CL) ++ FB) with ([] ++ b :: (CL ++ FB)) in BA.
    apply blocks_apart_app_inv in BA as (_ & BA2 & _). cbn [app] in BA2. destruct BA2 as [FA _].
    apply Forall_app in FA as [FA _]. pose proof (proj1 (Forall_forall _ _) FA b' Hin) as AP. unfold apart in AP. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mid_apart : forall R st (C1 C2 FB : list cblk) b b' m,
    GIo K R st (C1 ++ b :: C2) FB m -> In b' (C1 ++ C2) ->
    cb_addr b + cb_size b <= cb_addr b' \/ cb_addr b' + cb_size b' <= cb_addr b.
  Proof using Type. pin_using tt.
    intros R st C1 C2 FB b b' m G Hin. destruct (GIo_blocks K _ _ _ _ _ G) as [_ BA].
    rewrite <- app_assoc in BA. apply blocks_apart_app_inv in BA as (_ & BA2 & X12). cbn [app] in BA2. destruct BA2 as [FA BA3].
    apply in_app_iff in Hin as [H1|H2].
    - pose proof (X12 b' b H1 ltac:(left; reflexivity)) as AP. unfold apart in AP. lia.
    - apply Forall_app in FA as [FA _]. pose proof (proj1 (Forall_forall _ _) FA b' H2) as AP. unfold apart in AP. lia.
  Qed.

End KitK.

(* [comment removed for export] *)
End WithCeil.

Ltac prs_in := fastfirst (first [ noevar_assumption | match goal with HI : forall a, _ -> in_block ?L a |- in_block ?L ?x => apply HI; lia end ]).
(* [comment removed for export] *)
Ltac prs1 := fastfirst (first [ noevar_assumption | exact Logic.I | left; lia | right; prs_in | lia ]).
Ltac prs :=
  intros a Ha; cbn [cells_size csize Nat.add ng_cells cursor_cells length] in Ha;
  try match goal with Hc : cells_size ?c = 24%nat |- _ => rewrite Hc in Ha end;
  try match goal with Hc : csize ?c = 8%nat |- _ => rewrite Hc in Ha end;
  unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in Ha; cbn [outside];
  repeat match goal with |- _ /\ _ => split end;
  first [ prs1
        | match goal with HE : ((bv_unsigned _ <= ?E /\ _) \/ ?E = _)%Z |- _ => destruct HE as [?X1| ?X1]; prs1 end ].

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (S3.PcapRep.TwB.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma length_list_ascii fs : length (list_ascii_of_string fs) = String.length fs.
Proof using Type. pin_using tt. induction fs as [|c fs IH]; cbn; [reflexivity| now rewrite IH]. Qed.
Lemma fmt_at_intro m A fs :
  mem_inv usegs m ->
  ro_bytes_b usegs A (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string fs) ++ [Z_to_bv 8 0]) = true ->
  0x10000 <= A -> A + Z.of_nat (String.length fs) + 1 <= 0x13000 -> fmt_at m A fs.
Proof using Type. pin_using tt.
  intros MI RO LO HI. split; [| lia].
  pose proof (ro_cells_image usegs m A _ MI RO ltac:(lia)) as X. rewrite length_app, length_map, length_list_ascii in X. cbn [length] in X.
  pose proof (ro_cells_bytes_at _ _ _ _ (X ltac:(lia))) as Y. cbn [cells_bytes cbytes] in Y. rewrite app_nil_r in Y. exact Y.
Qed.

Lemma eqb_lits_eq : forall x y, x = y -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof using Type. pin_using tt. intros x y ->. unfold bv_eqb. apply Z.eqb_refl. Qed.

(* [comment removed for export] *)
End WithCeil.

Ltac transport H m' AG tac :=
  lazymatch type of H with rw_cells ?sg _ ?A ?cs =>
    let X := fresh in
    assert (X : rw_cells sg m' A cs) by (eapply agrees_rw_cells; [exact AG | exact H | tac]);
    clear H; rename X into H end.

Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac ienter := lazymatch goal with |- implM _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; unfold implM; iprefix.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma u32_s32 : forall v, u32 (s32 v) = u32 v.
Proof using Type. pin_using tt. intros v. unfold u32, s32. Z.div_mod_to_equations. lia. Qed.
Lemma s32_s32 : forall v, s32 (s32 v) = s32 v.
Proof using Type. pin_using tt. intros v. unfold s32. Z.div_mod_to_equations. lia. Qed.
Lemma s32_small : forall v, 0 <= v < 2^31 -> s32 v = v.
Proof using Type. pin_using tt. intros v Hv. unfold s32. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Definition conv32 (c : conv) : bool := match c with Cd | Cu | Cx | C08x => true | _ => false end.
Inductive aeq32 : conv -> farg -> farg -> Prop :=
| aeq_same c a : aeq32 c a a
| aeq_s32 c v : conv32 c = true -> aeq32 c (AInt (s32 v)) (AInt v).
Fixpoint convs (items : list fitem) : list conv :=
  match items with [] => [] | FConv c :: r => c :: convs r | _ :: r => convs r end.
Inductive pargs : list conv -> list farg -> list farg -> Prop :=
| pargs_nil cs : pargs cs [] []
| pargs_cons c cs a a' r r' : aeq32 c a a' -> pargs cs r r' -> pargs (c :: cs) (a :: r) (a' :: r').
Lemma conv_pieces_aeq : forall c a a', aeq32 c a a' -> conv_pieces c a = conv_pieces c a'.
Proof using Type. pin_using tt.
  intros c a a' Hq. destruct Hq as [c a| c v Hc]; [reflexivity|].
  destruct c; try discriminate Hc; cbn [conv_pieces]; rewrite ?u32_s32, ?s32_s32; reflexivity.
Qed.
Lemma fmt_pieces_pargs : forall items args args', pargs (convs items) args args' -> fmt_pieces items args = fmt_pieces items args'.
Proof using Type. pin_using tt.
  induction items as [|it items IH]; intros args args' Hp; [reflexivity|].
  destruct it as [l|c|sb]; cbn [fmt_pieces convs] in *.
  - f_equal. apply IH. exact Hp.
  - inversion Hp as [cs0 | c0 cs0 a0 a0' r r' Ha Hr]; subst.
    + reflexivity.
    + cbn [hd tl]. rewrite (conv_pieces_aeq _ _ _ Ha). f_equal. f_equal. apply IH. exact Hr.
  - reflexivity.
Qed.
Lemma snprintf_pargs : forall n fs args args', pargs (convs (fmt fs)) args args' -> Fmt.snprintf n fs args = Fmt.snprintf n fs args'.
Proof using Type. pin_using tt. intros n fs args args' Hp. unfold Fmt.snprintf, snprintf_out, fmt_output. rewrite (fmt_pieces_pargs _ _ _ Hp). reflexivity. Qed.

(* [comment removed for export] *)
Lemma unsigned_s32 : forall x, 0 <= x < 2^32 -> bv_unsigned (Z_to_bv 64 (s32 x)) = x + (x / 2^31) * (2^64 - 2^32).
Proof using Type. pin_using tt.
  intros x Hx. rewrite unsigned_lit_wrap. unfold s32. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
End WithCeil.

Ltac zc_lia := unfold le4val in *; Z.div_mod_to_equations; lia.
Ltac zc_base := first [ reflexivity | apply Z.ltb_lt; zc_lia | apply Z.ltb_ge; zc_lia | apply Z.leb_le; zc_lia | apply Z.leb_gt; zc_lia
                      | apply Z.eqb_eq; zc_lia | apply Z.eqb_neq; zc_lia ].
Ltac zc_rec := lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); zc_rec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); zc_rec
  | _ => zc_base end.
Ltac if_tf b := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with b; [cbv iota | symmetry; unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb]; fold_lit_ux; rewrite ?unsigned_s32 by (unfold le4val in *; lia); zc_rec] end.


Section WithCeil.
Context {CEILV : CEIL}.
Section KitK.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Lemma set_bufdata_twice : forall d d' (q : pcapT), set_bufdata d (set_bufdata d' q) = set_bufdata d q.
  Proof using Type. pin_using tt. intros. reflexivity. Qed.
  Lemma pc_bufdata_set : forall d (q : pcapT), pc_bufdata (set_bufdata d q) = d.
  Proof using Type. pin_using tt. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma head_apart : forall R st (CL FB : list cblk) b b' m,
    GIo K R st (b :: CL) FB m -> In b' CL ->
    cb_addr b + cb_size b <= cb_addr b' \/ cb_addr b' + cb_size b' <= cb_addr b.
  Proof using Type. pin_using tt.
    intros R st CL FB b b' m G Hin. destruct (GIo_blocks K _ _ _ _ _ G) as [_ BA].
    change ((b :: CL) ++ FB) with ([] ++ b :: (CL ++ FB)) in BA.
    apply blocks_apart_app_inv in BA as (_ & BA2 & _). cbn [app] in BA2. destruct BA2 as [FA _].
    apply Forall_app in FA as [FA _]. pose proof (proj1 (Forall_forall _ _) FA b' Hin) as AP. unfold apart in AP. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mid_apart : forall R st (C1 C2 FB : list cblk) b b' m,
    GIo K R st (C1 ++ b :: C2) FB m -> In b' (C1 ++ C2) ->
    cb_addr b + cb_size b <= cb_addr b' \/ cb_addr b' + cb_size b' <= cb_addr b.
  Proof using Type. pin_using tt.
    intros R st C1 C2 FB b b' m G Hin. destruct (GIo_blocks K _ _ _ _ _ G) as [_ BA].
    rewrite <- app_assoc in BA. apply blocks_apart_app_inv in BA as (_ & BA2 & X12). cbn [app] in BA2. destruct BA2 as [FA BA3].
    apply in_app_iff in Hin as [H1|H2].
    - pose proof (X12 b' b H1 ltac:(left; reflexivity)) as AP. unfold apart in AP. lia.
    - apply Forall_app in FA as [FA _]. pose proof (proj1 (Forall_forall _ _) FA b' H2) as AP. unfold apart in AP. lia.
  Qed.

End KitK.

(* [comment removed for export] *)
End WithCeil.

Ltac prs_in := fastfirst (first [ noevar_assumption | match goal with HI : forall a, _ -> in_block ?L a |- in_block ?L ?x => apply HI; lia end ]).
(* [comment removed for export] *)
Ltac prs1 := fastfirst (first [ noevar_assumption | exact Logic.I | left; lia | right; prs_in | lia ]).
Ltac prs :=
  intros a Ha; cbn [cells_size csize Nat.add ng_cells cursor_cells length] in Ha;
  try match goal with Hc : cells_size ?c = 24%nat |- _ => rewrite Hc in Ha end;
  try match goal with Hc : csize ?c = 8%nat |- _ => rewrite Hc in Ha end;
  unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in Ha; cbn [outside];
  repeat match goal with |- _ /\ _ => split end;
  first [ prs1
        | match goal with HE : ((bv_unsigned _ <= ?E /\ _) \/ ?E = _)%Z |- _ => destruct HE as [?X1| ?X1]; prs1 end ].
End TwB.
End SfNgKit.

(* [comment removed for export] *)
Module F_sfpcapng_aiC.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
(* [comment removed for export] *) From Ltac2 Require Ltac2.
#[local] Ltac2 Set StepFast.sf_fold_goal := Ltac2.Init.false.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (PcapRep.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma land_ff0000 : forall x, 0 <= x -> Z.land x 16711680 = ((x / 65536) mod 256) * 65536.
Proof using Type. pin_using tt.
  intros x Hx. change 16711680 with (Z.shiftl (Z.ones 8) 16). rewrite land_ones_shift by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lor_disj : forall x y k, 0 <= k -> 0 <= x -> x mod 2^k = 0 -> 0 <= y < 2^k -> Z.lor x y = x + y.
Proof using Type. pin_using tt.
  intros x y k Hk Hx Hm Hy. assert (E : x = (x / 2^k) * 2^k) by (Z.div_mod_to_equations; nia).
  rewrite E at 1. rewrite lor_high_low; [lia| Z.div_mod_to_equations; nia | lia | lia].
Qed.
Lemma lor_disj' : forall x y k, 0 <= k -> 0 <= x -> x mod 2^k = 0 -> 0 <= y < 2^k -> Z.lor y x = x + y.
Proof using Type. pin_using tt. intros x y k Hk Hx Hm Hy. rewrite Z.lor_comm. apply (lor_disj x y k); assumption. Qed.

(* [comment removed for export] *)
End WithCeil.

Ltac zlia := unfold le8val in *; Z.div_mod_to_equations; lia.
Ltac norm_word1 :=
  fastfirst (first [ noevar_assumption | rewrite Z.shiftl_mul_pow2 by lia
        | rewrite Z.shiftr_div_pow2 by lia
        | rewrite bv_wrap32_eq
        | rewrite land_ff00 by zlia
        | rewrite land_ff0000 by zlia
        | match goal with |- context [bv_swrap 32 ?x] => rewrite (bv_swrap32_small x) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) end
        | match goal with |- context [bv_unsigned (Z_to_bv 64 ?x)] =>
            lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
            rewrite (unsigned_lit x) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) end
        | match goal with |- context [Z.lor ?x ?y] =>
            lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
            lazymatch y with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
            first [ rewrite (lor_disj x y 8) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj x y 16) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj x y 24) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj x y 32) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj x y 40) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj x y 48) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj x y 56) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj' y x 8) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj' y x 16) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj' y x 24) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj' y x 32) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj' y x 40) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj' y x 48) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj' y x 56) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) ] end
        | match goal with |- context [bv_unsigned (Z_to_bv 64 ?x)] =>
            lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
            rewrite (unsigned_lit_wrap x) end ]).
Ltac norm_word := repeat norm_word1; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
(* [comment removed for export] *)
Local Ltac nwr_2 := rewrite Z.shiftl_mul_pow2 by lia.
Local Ltac nwr_3 := rewrite Z.shiftr_div_pow2 by lia.
Local Ltac nwr_4 := rewrite bv_wrap32_eq.
Local Ltac nwr_5 := rewrite land_ff00 by zlia.
Local Ltac nwr_6 := rewrite land_ff0000 by zlia.
Local Ltac nwr_7 := match goal with |- context [bv_swrap 32 ?x] => rewrite (bv_swrap32_small x) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) end.
Local Ltac nwr_8 := match goal with |- context [bv_unsigned (Z_to_bv 64 ?x)] =>
    lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    rewrite (unsigned_lit x) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) end.
Local Ltac nwr_10 := match goal with |- context [bv_unsigned (Z_to_bv 64 ?x)] =>
    lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    rewrite (unsigned_lit_wrap x) end.
Local Ltac nwr_L8 := match goal with |- context [Z.lor ?x ?y] =>
    lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    lazymatch y with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    rewrite (lor_disj x y 8) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) end.
Local Ltac nwr_L16 := match goal with |- context [Z.lor ?x ?y] =>
    lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    lazymatch y with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    rewrite (lor_disj x y 16) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) end.
Local Ltac nwr_L24 := match goal with |- context [Z.lor ?x ?y] =>
    lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    lazymatch y with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    rewrite (lor_disj x y 24) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) end.
Local Ltac nwr_L32 := match goal with |- context [Z.lor ?x ?y] =>
    lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    lazymatch y with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    rewrite (lor_disj x y 32) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) end.
Local Ltac nwr_L40 := match goal with |- context [Z.lor ?x ?y] =>
    lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    lazymatch y with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    rewrite (lor_disj x y 40) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) end.
Local Ltac nwr_L48 := match goal with |- context [Z.lor ?x ?y] =>
    lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    lazymatch y with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    rewrite (lor_disj x y 48) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) end.
Local Ltac nwr_L56 := match goal with |- context [Z.lor ?x ?y] =>
    lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    lazymatch y with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    rewrite (lor_disj x y 56) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) end.
Local Ltac nw_ldu64 := nwr_2; nwr_2; nwr_2; nwr_2; nwr_2; nwr_2; nwr_2; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_L24; nwr_8; nwr_L8; nwr_8; nwr_L16; nwr_8; nwr_8; nwr_L24; nwr_8; nwr_L8; nwr_8; nwr_L16; nwr_8; nwr_L32.
Local Ltac nw_bswap64 := nwr_2; nwr_2; nwr_2; nwr_2; nwr_2; nwr_3; nwr_3; nwr_3; nwr_3; nwr_3; nwr_3; nwr_4; nwr_4; nwr_7; nwr_7; nwr_8; nwr_5; nwr_6; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_6; nwr_8; nwr_8; nwr_5; nwr_8; nwr_8; nwr_L40; nwr_8; nwr_L24; nwr_8; nwr_L8; nwr_8; nwr_L16; nwr_8; nwr_10; nwr_L56; nwr_8; nwr_L48; nwr_8; nwr_L32.

Ltac lstep := step; cbn [firstn skipn app]; rewrite ?zext_extract_byte, ?sext_extract_byte; rewrite ?zxb_lit by lia.

Open Scope bv_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition ldu64_block__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (A : Z) (u0 u1 u2 u3 u4 u5 u6 u7 : Z),
    mem_inv ssegs m -> (0 < A)%Z -> (A + 8 < 2^64)%Z ->
    (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> (0 <= u2 < 256)%Z -> (0 <= u3 < 256)%Z ->
    (0 <= u4 < 256)%Z -> (0 <= u5 < 256)%Z -> (0 <= u6 < 256)%Z -> (0 <= u7 < 256)%Z ->
    t3 = Z_to_bv 64 A ->
    rw_cells ssegs m A [CB 8 (map b8 [u0; u1; u2; u3; u4; u5; u6; u7])] ->
    evt ssegs (fun ms' => exists (a3' s8' s10' t3' : word),
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3' a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 1) s7 s8' s9 s10' s11 t3' t4 t5
                     (Z_to_bv 64 (le8val u0 u1 u2 u3 u4 u5 u6 u7)))
                 F (Z_to_bv 64 0x17178) fc None m (seg_rom ssegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1711c) fc None m (seg_rom ssegs)).
Section Sz4.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A u0 u1 u2 u3 u4 u5 u6 u7 : ltac2:(SecDiet.SzSec.tyM 'ldu64_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma ldu64_block__body : ltac2:(SecDiet.SzSec.bodyP 'ldu64_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
  intros MI HA1 HA2 B0 B1 B2 B3 B4 B5 B6 B7 -> HV.
  cbn [map] in HV.
  do 23 (step; cbn [firstn skipn app]; rewrite ?zext_extract_byte; rewrite ?zxb_lit by lia).
  match goal with |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] =>
    replace (Z_to_bv 64 (Z.lor a b)) with (Z_to_bv 64 (le8val u0 u1 u2 u3 u4 u5 u6 u7)) by (f_equal; nw_ldu64; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; unfold le8val; zlia) end.
  apply evt_done. do 4 eexists. reflexivity.
Qed.
End Sz4.
Lemma ldu64_block : ltac:(let t := eval cbv delta [ldu64_block__stmt] in ldu64_block__stmt in exact t).
Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A u0 u1 u2 u3 u4 u5 u6 u7. ltac2:(SecDiet.SzSec.closeP 'ldu64_block__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition bswap64_block__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (u0 u1 u2 u3 u4 u5 u6 u7 : Z),
    (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> (0 <= u2 < 256)%Z -> (0 <= u3 < 256)%Z ->
    (0 <= u4 < 256)%Z -> (0 <= u5 < 256)%Z -> (0 <= u6 < 256)%Z -> (0 <= u7 < 256)%Z ->
    evt ssegs (fun ms' => exists (a3' t3' s8' s9' : word),
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3' a4 a5 a6 a7 s2 (Z_to_bv 64 65280) (Z_to_bv 64 16711680) s5 s6 s7 s8' s9' s10 s11 t3' t4 t5
                     (Z_to_bv 64 (le8val u7 u6 u5 u4 u3 u2 u1 u0)))
                 F (Z_to_bv 64 0x17078) fc None m (seg_rom ssegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 65280) (Z_to_bv 64 16711680) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5
               (Z_to_bv 64 (le8val u0 u1 u2 u3 u4 u5 u6 u7)))
          F (Z_to_bv 64 0x1717c) fc None m (seg_rom ssegs)).
Section Sz5.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 F fc m u0 u1 u2 u3 u4 u5 u6 u7 : ltac2:(SecDiet.SzSec.tyM 'bswap64_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma bswap64_block__body : ltac2:(SecDiet.SzSec.bodyP 'bswap64_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
  intros B0 B1 B2 B3 B4 B5 B6 B7.
  do 23 step.
  match goal with |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] =>
    replace (Z_to_bv 64 (Z.lor a b)) with (Z_to_bv 64 (le8val u7 u6 u5 u4 u3 u2 u1 u0))
      by (f_equal; nw_bswap64; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; rewrite le8_x0, le8_x1, le8_x2, le8_x3, le8_x4, le8_x5, le8_x6, le8_x7 by lia; unfold le8val; lia) end.
  apply evt_done. do 4 eexists. reflexivity.
Qed.
End Sz5.
Lemma bswap64_block : ltac:(let t := eval cbv delta [bswap64_block__stmt] in bswap64_block__stmt in exact t).
Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 F fc m u0 u1 u2 u3 u4 u5 u6 u7. ltac2:(SecDiet.SzSec.closeP 'bswap64_block__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Lemma pow10_block : forall (n : nat) (k acc : Z)
    (ra sp gp tp t0 t1 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    k = Z.of_nat (S n) -> (k <= 19)%Z -> (0 <= acc)%Z -> (acc * 10 ^ k < 2^64)%Z ->
    evt ssegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 10) s0 s1 a0 a1 a2 (Z_to_bv 64 0) (Z_to_bv 64 (acc * 10 ^ k)) (Z_to_bv 64 0) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x17078) fc None m (seg_rom ssegs))
      (MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 10) s0 s1 a0 a1 a2 (Z_to_bv 64 k) (Z_to_bv 64 acc) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x171fc) fc None m (seg_rom ssegs)).
Proof using Type. pin_using tt.
  induction n as [|n IH]; intros until m; intros Hk K19 A0 AB.
  - subst k. change (Z.of_nat 1) with 1%Z in *.
    assert (A1 : (acc * 10 < 2^64)%Z) by (rewrite Z.pow_1_r in AB; exact AB).
    step. step. step. if_tf false. rewrite (unsigned_lit acc) by lia.
    step. step. apply evt_done. rewrite Z.pow_1_r. reflexivity.
  - step. rewrite (unsigned_lit k) by lia. rewrite (bv_swrap32_small (k + -1)) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; lia).
    step. rewrite (unsigned_lit acc) by lia.
    assert (P1 : (0 < 10 ^ (k - 1))%Z) by (apply Z.pow_pos_nonneg; lia).
    assert (E : (acc * 10 ^ k = (acc * 10) * 10 ^ (k - 1))%Z).
    { replace k with (k - 1 + 1)%Z at 1 by lia. rewrite Z.pow_add_r, Z.pow_1_r by lia. lia. }
    step. rewrite (eqb_lits_false (k + -1) 0) by lia. cbv beta iota delta [negb].
    rewrite E. replace (k + -1)%Z with (k - 1)%Z by lia.
    apply (IH (k - 1)%Z (acc * 10)%Z); [lia | lia | lia | rewrite <- E; exact AB].
Qed.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_aiD.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (S3.PcapRep.TwB.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma land_ff0000 : forall x, 0 <= x -> Z.land x 16711680 = ((x / 65536) mod 256) * 65536.
Proof using Type. pin_using tt.
  intros x Hx. change 16711680 with (Z.shiftl (Z.ones 8) 16). rewrite land_ones_shift by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lor_disj : forall x y k, 0 <= k -> 0 <= x -> x mod 2^k = 0 -> 0 <= y < 2^k -> Z.lor x y = x + y.
Proof using Type. pin_using tt.
  intros x y k Hk Hx Hm Hy. assert (E : x = (x / 2^k) * 2^k) by (Z.div_mod_to_equations; nia).
  rewrite E at 1. rewrite lor_high_low; [lia| Z.div_mod_to_equations; nia | lia | lia].
Qed.
Lemma lor_disj' : forall x y k, 0 <= k -> 0 <= x -> x mod 2^k = 0 -> 0 <= y < 2^k -> Z.lor y x = x + y.
Proof using Type. pin_using tt. intros x y k Hk Hx Hm Hy. rewrite Z.lor_comm. apply (lor_disj x y k); assumption. Qed.

(* [comment removed for export] *)
End WithCeil.

Ltac zlia := unfold le8val in *; Z.div_mod_to_equations; lia.
Ltac norm_word1 :=
  fastfirst (first [ noevar_assumption | rewrite Z.shiftl_mul_pow2 by lia
        | rewrite Z.shiftr_div_pow2 by lia
        | rewrite bv_wrap32_eq
        | rewrite land_ff00 by zlia
        | rewrite land_ff0000 by zlia
        | match goal with |- context [bv_swrap 32 ?x] => rewrite (bv_swrap32_small x) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) end
        | match goal with |- context [bv_unsigned (Z_to_bv 64 ?x)] =>
            lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
            rewrite (unsigned_lit x) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) end
        | match goal with |- context [Z.lor ?x ?y] =>
            lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
            lazymatch y with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
            first [ rewrite (lor_disj x y 8) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj x y 16) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj x y 24) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj x y 32) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj x y 40) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj x y 48) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj x y 56) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj' y x 8) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj' y x 16) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj' y x 24) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj' y x 32) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj' y x 40) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj' y x 48) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia)
                  | rewrite (lor_disj' y x 56) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) ] end
        | match goal with |- context [bv_unsigned (Z_to_bv 64 ?x)] =>
            lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
            rewrite (unsigned_lit_wrap x) end ]).
Ltac norm_word := repeat norm_word1; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
(* [comment removed for export] *)
Local Ltac nwr_2 := rewrite Z.shiftl_mul_pow2 by lia.
Local Ltac nwr_3 := rewrite Z.shiftr_div_pow2 by lia.
Local Ltac nwr_4 := rewrite bv_wrap32_eq.
Local Ltac nwr_5 := rewrite land_ff00 by zlia.
Local Ltac nwr_6 := rewrite land_ff0000 by zlia.
Local Ltac nwr_7 := match goal with |- context [bv_swrap 32 ?x] => rewrite (bv_swrap32_small x) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) end.
Local Ltac nwr_8 := match goal with |- context [bv_unsigned (Z_to_bv 64 ?x)] =>
    lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    rewrite (unsigned_lit x) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) end.
Local Ltac nwr_10 := match goal with |- context [bv_unsigned (Z_to_bv 64 ?x)] =>
    lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    rewrite (unsigned_lit_wrap x) end.
Local Ltac nwr_L8 := match goal with |- context [Z.lor ?x ?y] =>
    lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    lazymatch y with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    rewrite (lor_disj x y 8) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) end.
Local Ltac nwr_L16 := match goal with |- context [Z.lor ?x ?y] =>
    lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    lazymatch y with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    rewrite (lor_disj x y 16) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) end.
Local Ltac nwr_L24 := match goal with |- context [Z.lor ?x ?y] =>
    lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    lazymatch y with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    rewrite (lor_disj x y 24) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) end.
Local Ltac nwr_L32 := match goal with |- context [Z.lor ?x ?y] =>
    lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    lazymatch y with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    rewrite (lor_disj x y 32) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) end.
Local Ltac nwr_L40 := match goal with |- context [Z.lor ?x ?y] =>
    lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    lazymatch y with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    rewrite (lor_disj x y 40) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) end.
Local Ltac nwr_L48 := match goal with |- context [Z.lor ?x ?y] =>
    lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    lazymatch y with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    rewrite (lor_disj x y 48) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) end.
Local Ltac nwr_L56 := match goal with |- context [Z.lor ?x ?y] =>
    lazymatch x with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    lazymatch y with context [bv_unsigned _] => fail | context [Z.lor _ _] => fail | _ => idtac end;
    rewrite (lor_disj x y 56) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; zlia) end.
Local Ltac nw_ldu64 := nwr_2; nwr_2; nwr_2; nwr_2; nwr_2; nwr_2; nwr_2; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_L24; nwr_8; nwr_L8; nwr_8; nwr_L16; nwr_8; nwr_8; nwr_L24; nwr_8; nwr_L8; nwr_8; nwr_L16; nwr_8; nwr_L32.
Local Ltac nw_bswap64 := nwr_2; nwr_2; nwr_2; nwr_2; nwr_2; nwr_3; nwr_3; nwr_3; nwr_3; nwr_3; nwr_3; nwr_4; nwr_4; nwr_7; nwr_7; nwr_8; nwr_5; nwr_6; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_8; nwr_6; nwr_8; nwr_8; nwr_5; nwr_8; nwr_8; nwr_L40; nwr_8; nwr_L24; nwr_8; nwr_L8; nwr_8; nwr_L16; nwr_8; nwr_10; nwr_L56; nwr_8; nwr_L48; nwr_8; nwr_L32.

Ltac lstep := step; cbn [firstn skipn app]; rewrite ?zext_extract_byte, ?sext_extract_byte; rewrite ?zxb_lit by lia.

Open Scope bv_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition ldu64_block__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (A : Z) (u0 u1 u2 u3 u4 u5 u6 u7 : Z),
    mem_inv usegs m -> (0 < A)%Z -> (A + 8 < 2^64)%Z ->
    (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> (0 <= u2 < 256)%Z -> (0 <= u3 < 256)%Z ->
    (0 <= u4 < 256)%Z -> (0 <= u5 < 256)%Z -> (0 <= u6 < 256)%Z -> (0 <= u7 < 256)%Z ->
    s8 = Z_to_bv 64 A ->
    rw_cells usegs m A [CB 8 (map b8 [u0; u1; u2; u3; u4; u5; u6; u7])] ->
    evt usegs (fun ms' => exists (a3' s8' s10' s11' : word),
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3' a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (le8val u0 u1 u2 u3 u4 u5 u6 u7)) (Z_to_bv 64 1) s6 s7 s8' s9 s10' s11' t3 t4 t5 t6)
                 F (Z_to_bv 64 0x177a8) fc None m (seg_rom usegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1774c) fc None m (seg_rom usegs)).
Section Sz4.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A u0 u1 u2 u3 u4 u5 u6 u7 : ltac2:(SecDiet.SzSec.tyM 'ldu64_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma ldu64_block__body : ltac2:(SecDiet.SzSec.bodyP 'ldu64_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
 intros MI HA1 HA2 B0 B1 B2 B3 B4 B5 B6 B7 -> HV.
  cbn [map] in HV.
  do 23 (step; cbn [firstn skipn app]; rewrite ?zext_extract_byte; rewrite ?zxb_lit by lia).
  match goal with |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] =>
    replace (Z_to_bv 64 (Z.lor a b)) with (Z_to_bv 64 (le8val u0 u1 u2 u3 u4 u5 u6 u7)) by (f_equal; nw_ldu64; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; unfold le8val; zlia) end.
  apply evt_done. do 4 eexists. reflexivity.
Qed.
End Sz4.
Lemma ldu64_block : ltac:(let t := eval cbv delta [ldu64_block__stmt] in ldu64_block__stmt in exact t).
Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A u0 u1 u2 u3 u4 u5 u6 u7. ltac2:(SecDiet.SzSec.closeP 'ldu64_block__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition bswap64_block__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (u0 u1 u2 u3 u4 u5 u6 u7 : Z),
    (0 <= u0 < 256)%Z -> (0 <= u1 < 256)%Z -> (0 <= u2 < 256)%Z -> (0 <= u3 < 256)%Z ->
    (0 <= u4 < 256)%Z -> (0 <= u5 < 256)%Z -> (0 <= u6 < 256)%Z -> (0 <= u7 < 256)%Z ->
    evt usegs (fun ms' => exists (a3' s8' s9' s10' : word),
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3' a4 a5 a6 a7 (Z_to_bv 64 65280) (Z_to_bv 64 16711680)
                     (Z_to_bv 64 (le8val u7 u6 u5 u4 u3 u2 u1 u0)) s5 s6 s7 s8' s9' s10' s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x176a8) fc None m (seg_rom usegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 65280) (Z_to_bv 64 16711680)
               (Z_to_bv 64 (le8val u0 u1 u2 u3 u4 u5 u6 u7)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x177ac) fc None m (seg_rom usegs)).
Section Sz5.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m u0 u1 u2 u3 u4 u5 u6 u7 : ltac2:(SecDiet.SzSec.tyM 'bswap64_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma bswap64_block__body : ltac2:(SecDiet.SzSec.bodyP 'bswap64_block__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt.
 intros B0 B1 B2 B3 B4 B5 B6 B7.
  do 23 step.
  match goal with |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] =>
    replace (Z_to_bv 64 (Z.lor a b)) with (Z_to_bv 64 (le8val u7 u6 u5 u4 u3 u2 u1 u0))
      by (f_equal; nw_bswap64; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; rewrite le8_x0, le8_x1, le8_x2, le8_x3, le8_x4, le8_x5, le8_x6, le8_x7 by lia; unfold le8val; lia) end.
  apply evt_done. do 4 eexists. reflexivity.
Qed.
End Sz5.
Lemma bswap64_block : ltac:(let t := eval cbv delta [bswap64_block__stmt] in bswap64_block__stmt in exact t).
Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m u0 u1 u2 u3 u4 u5 u6 u7. ltac2:(SecDiet.SzSec.closeP 'bswap64_block__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
Lemma pow10_block : forall (n : nat) (k acc : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    k = Z.of_nat (S n) -> (k <= 19)%Z -> (0 <= acc)%Z -> (acc * 10 ^ k < 2^64)%Z ->
    evt usegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 0) t2 s0 s1 a0 (Z_to_bv 64 (acc * 10 ^ k)) a2 (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 10) t4 t5 t6)
                 F (Z_to_bv 64 0x176a8) fc None m (seg_rom usegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 acc) a2 (Z_to_bv 64 k) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 10) t4 t5 t6)
          F (Z_to_bv 64 0x1782c) fc None m (seg_rom usegs)).
Proof using Type. pin_using tt.
  induction n as [|n IH]; intros until m; intros Hk K19 A0 AB.
  - subst k. change (Z.of_nat 1) with 1%Z in *.
    assert (A1 : (acc * 10 < 2^64)%Z) by (rewrite Z.pow_1_r in AB; exact AB).
    step. step. step. if_tf false. rewrite (unsigned_lit acc) by lia.
    step. step. apply evt_done. rewrite Z.pow_1_r. reflexivity.
  - step. rewrite (unsigned_lit k) by lia. rewrite (bv_swrap32_small (k + -1)) by (cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; lia).
    step. rewrite (unsigned_lit acc) by lia.
    assert (P1 : (0 < 10 ^ (k - 1))%Z) by (apply Z.pow_pos_nonneg; lia).
    assert (E : (acc * 10 ^ k = (acc * 10) * 10 ^ (k - 1))%Z).
    { replace k with (k - 1 + 1)%Z at 1 by lia. rewrite Z.pow_add_r, Z.pow_1_r by lia. lia. }
    step. rewrite (eqb_lits_false (k + -1) 0) by lia. cbv beta iota delta [negb].
    rewrite E. replace (k + -1)%Z with (k - 1)%Z by lia.
    apply (IH (k - 1)%Z (acc * 10)%Z); [lia | lia | lia | rewrite <- E; exact AB].
Qed.

End WithCeil.
End TwB.
End F_sfpcapng_aiC.
