(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import Layout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Gm_ropkit LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation SBV_W data ld := [(data, data + 4 * ld)]%Z (only parsing).

(* [comment removed for export] *)
Definition bsb_fill1_exit (ra sp gp tp s0 s1 a0 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (data ld pw w : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a7' t3' : word) (m' : mem) (bs' : list byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2 a3 a4 a5 a6 a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
             F (Z_to_bv 64 0x961b8) fc None m' (seg_rom asegs)
    /\ munch (SBV_W data ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' data bs' /\ Z.of_nat (length bs') = 4 * ld /\ acc asegs m' data (4 * ld)
    /\ rw_cells asegs m' pw [C4 (Z_to_bv 64 w)].

Lemma bsb_fill1 : forall (k : nat) (j : Z)
    (ra sp gp tp t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (data ld pw w q wpl p l : Z) (bs : list byte),
  p = data + 4 * q + j -> l = data + 4 * q ->
  Z.of_nat k = w - j -> 0 <= j -> (1 <= k)%nat -> 0 < w <= 20000 -> w <= 4 * wpl -> 0 <= q -> q + wpl <= ld -> ld <= 2^24 ->
  0 < data -> data mod 8 = 0 -> data + 4 * ld <= 2^47 -> (data + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= data) ->
  (data + 4 * ld <= 0x10000 \/ SEGTOP_A <= data) ->
  (pw + 4 <= data \/ data + 4 * ld <= pw) ->
  u8arr asegs m data bs -> Z.of_nat (length bs) = 4 * ld -> acc asegs m data (4 * ld) -> mem_inv asegs m ->
  rw_cells asegs m pw [C4 (Z_to_bv 64 w)] ->
  evt asegs (bsb_fill1_exit ra sp gp tp s0 s1 a0 a2 a3 (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 l) s2 s3 s4 s5 s6 s7 (Z_to_bv 64 pw) (Z_to_bv 64 SHB)
                            s10 s11 t4 t5 t6 F fc m data ld pw w)
    (MS (mkR ra sp gp tp (Z_to_bv 64 p) (Z_to_bv 64 p) t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 1) (Z_to_bv 64 3)
             (Z_to_bv 64 l) (Z_to_bv 64 j)
             s2 s3 s4 s5 s6 s7 (Z_to_bv 64 pw) (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x96210) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 F fc m
    data ld pw w q wpl p l bs -> -> HK HJ HK1 WR W4 Q0 QL LD D0 D8 DHI DSH DSEG PWA UA UAL ACC MI PWC.
  { lia. }
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (SBV_W data ld) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0x96238].
  (* [comment removed for export] *)
  assert (E : Z.lxor (data + 4 * q + j) 3 = data + (4 * q + j + 3 - 2 * (j mod 4))) by (rewrite lxor3_eq; clear - D8; Z.div_mod_to_equations; lia).
  rewrite E. clear E.
  assert (IDX : 0 <= 4 * q + j + 3 - 2 * (j mod 4) < 4 * ld) by (clear - HK HJ W4 Q0 QL; Z.div_mod_to_equations; lia).
  pose proof (u8arr_store_ok asegs m data bs (4 * q + j + 3 - 2 * (j mod 4)) (wa (data + (4 * q + j + 3 - 2 * (j mod 4)))) UA ltac:(rewrite UAL; exact IDX) ltac:(reflexivity)) as SOK.
  zstep.
  change (le1 s3) with [Z_to_bv 8 (bv_unsigned s3)].
  pose proof (u8arr_write asegs m data bs (4 * q + j + 3 - 2 * (j mod 4)) (Z_to_bv 8 (bv_unsigned s3)) UA ltac:(rewrite UAL; exact IDX)) as UA2.
  clear UA. store_done.
  rewrite <- (upd_length bs (Z.to_nat (4 * q + j + 3 - 2 * (j mod 4))) (Z_to_bv 8 (bv_unsigned s3))) in UAL.
  set (bs1 := upd bs (Z.to_nat (4 * q + j + 3 - 2 * (j mod 4))) (Z_to_bv 8 (bv_unsigned s3))) in *. clearbody bs1. clear IDX.
  lwalk [0x9624c].
  rewrite ?(sx32_small w) by lia.
  lstep.
  destruct k as [|k].
  - brF. lwalk [0x961b8].
    apply evt_done. unfold bsb_fill1_exit. do 6 eexists. exists m0, bs1. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UA2|]. split; [exact UAL|]. split; [exact ACC| exact PWC].
  - brT.
    eapply evt_cut.
    + eapply (IH (j + 1)) with (bs := bs1) (q := q) (wpl := wpl) (ld := ld) (w := w) (p := data + 4 * q + j + 1) (l := data + 4 * q); try eassumption; try lia.
      all: try (f_equal; lia).
    +
      intros ms' PO. apply evt_done. unfold bsb_fill1_exit in PO |- *.
      destruct PO as (x1 & x2 & x3 & x4 & x5 & x6 & m' & bs' & E & MU' & WM' & R).
      do 8 eexists.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Definition bsb_fill3_exit (ra sp gp tp s0 s1 a0 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (data ld pw w : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a7' t3' : word) (m' : mem) (bs' : list byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2 a3 a4 a5 a6 a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
             F (Z_to_bv 64 0x96814) fc None m' (seg_rom asegs)
    /\ munch (SBV_W data ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' data bs' /\ Z.of_nat (length bs') = 4 * ld /\ acc asegs m' data (4 * ld)
    /\ rw_cells asegs m' pw [C4 (Z_to_bv 64 w)].

Lemma bsb_fill3 : forall (k : nat) (j : Z)
    (ra sp gp tp t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (data ld pw w q wpl p l : Z) (bs : list byte),
  p = data + 4 * q + j -> l = data + 4 * q ->
  Z.of_nat k = w - j -> 0 <= j -> (1 <= k)%nat -> 0 < w <= 20000 -> w <= 4 * wpl -> 0 <= q -> q + wpl <= ld -> ld <= 2^24 ->
  0 < data -> data mod 8 = 0 -> data + 4 * ld <= 2^47 -> (data + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= data) ->
  (data + 4 * ld <= 0x10000 \/ SEGTOP_A <= data) ->
  (pw + 4 <= data \/ data + 4 * ld <= pw) ->
  u8arr asegs m data bs -> Z.of_nat (length bs) = 4 * ld -> acc asegs m data (4 * ld) -> mem_inv asegs m ->
  rw_cells asegs m pw [C4 (Z_to_bv 64 w)] ->
  evt asegs (bsb_fill3_exit ra sp gp tp s0 s1 a0 a2 a3 (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 l) s2 s3 s4 s5 s6 s7 (Z_to_bv 64 pw) (Z_to_bv 64 SHB)
                            s10 s11 t4 t5 t6 F fc m data ld pw w)
    (MS (mkR ra sp gp tp (Z_to_bv 64 p) (Z_to_bv 64 p) t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 1) (Z_to_bv 64 3)
             (Z_to_bv 64 l) (Z_to_bv 64 j)
             s2 s3 s4 s5 s6 s7 (Z_to_bv 64 pw) (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x967c4) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 F fc m
    data ld pw w q wpl p l bs -> -> HK HJ HK1 WR W4 Q0 QL LD D0 D8 DHI DSH DSEG PWA UA UAL ACC MI PWC.
  { lia. }
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (SBV_W data ld) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0x967ec].
  (* [comment removed for export] *)
  assert (E : Z.lxor (data + 4 * q + j) 3 = data + (4 * q + j + 3 - 2 * (j mod 4))) by (rewrite lxor3_eq; clear - D8; Z.div_mod_to_equations; lia).
  rewrite E. clear E.
  assert (IDX : 0 <= 4 * q + j + 3 - 2 * (j mod 4) < 4 * ld) by (clear - HK HJ W4 Q0 QL; Z.div_mod_to_equations; lia).
  pose proof (u8arr_store_ok asegs m data bs (4 * q + j + 3 - 2 * (j mod 4)) (wa (data + (4 * q + j + 3 - 2 * (j mod 4)))) UA ltac:(rewrite UAL; exact IDX) ltac:(reflexivity)) as SOK.
  zstep.
  change (le1 s3) with [Z_to_bv 8 (bv_unsigned s3)].
  pose proof (u8arr_write asegs m data bs (4 * q + j + 3 - 2 * (j mod 4)) (Z_to_bv 8 (bv_unsigned s3)) UA ltac:(rewrite UAL; exact IDX)) as UA2.
  clear UA. store_done.
  rewrite <- (upd_length bs (Z.to_nat (4 * q + j + 3 - 2 * (j mod 4))) (Z_to_bv 8 (bv_unsigned s3))) in UAL.
  set (bs1 := upd bs (Z.to_nat (4 * q + j + 3 - 2 * (j mod 4))) (Z_to_bv 8 (bv_unsigned s3))) in *. clearbody bs1. clear IDX.
  lwalk [0x96800].
  rewrite ?(sx32_small w) by lia.
  lstep.
  destruct k as [|k].
  - brF. lwalk [0x96814].
    apply evt_done. unfold bsb_fill3_exit. do 6 eexists. exists m0, bs1. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UA2|]. split; [exact UAL|]. split; [exact ACC| exact PWC].
  - brT.
    eapply evt_cut.
    + eapply (IH (j + 1)) with (bs := bs1) (q := q) (wpl := wpl) (ld := ld) (w := w) (p := data + 4 * q + j + 1) (l := data + 4 * q); try eassumption; try lia.
      all: try (f_equal; lia).
    +
      intros ms' PO. apply evt_done. unfold bsb_fill3_exit in PO |- *.
      destruct PO as (x1 & x2 & x3 & x4 & x5 & x6 & m' & bs' & E & MU' & WM' & R).
      do 8 eexists.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Definition bsb_left_exit (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 t3 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (data ld pw w : Z) : machine_state -> Prop :=
  fun ms' => exists (a1' s2' s11' t4' t5' t6' : word) (m' : mem) (bs' : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11' t3 t4' t5' t6')
             F (Z_to_bv 64 0x966e0) fc None m' (seg_rom asegs)
    /\ munch (SBV_W data ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' data bs' /\ Z.of_nat (length bs') = 4 * ld /\ acc asegs m' data (4 * ld)
    /\ rw_cells asegs m' pw [C4 (Z_to_bv 64 w)].

Lemma bsb_left : forall (k : nat) (j : Z)
    (ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 : word) F fc (m : mem)
    (data ld pw w q wpl n c p l : Z) (bs : list byte),
  p = data + 4 * q + j -> l = data + 4 * q -> c = n - j ->
  Z.of_nat k = n - j -> 0 <= j -> (1 <= k)%nat -> n <= 4 * wpl -> 0 < wpl <= 5001 -> 0 <= q -> q + wpl <= ld -> ld <= 2^24 ->
  0 < data -> data mod 8 = 0 -> data + 4 * ld <= 2^47 -> (data + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= data) ->
  (data + 4 * ld <= 0x10000 \/ SEGTOP_A <= data) ->
  (pw + 4 <= data \/ data + 4 * ld <= pw) ->
  u8arr asegs m data bs -> Z.of_nat (length bs) = 4 * ld -> acc asegs m data (4 * ld) -> mem_inv asegs m ->
  rw_cells asegs m pw [C4 (Z_to_bv 64 w)] ->
  evt asegs (bsb_left_exit ra sp gp tp (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 l) s0 s1 a0 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 SHB) s10 t3
                           F fc m data ld pw w)
    (MS (mkR ra sp gp tp (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 l) s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 SHB) s10 s11 t3 (Z_to_bv 64 p) (Z_to_bv 64 c) (Z_to_bv 64 p))
        F (Z_to_bv 64 0x96694) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 F fc m
    data ld pw w q wpl n c p l bs -> -> -> HK HJ HK1 W4 WPLB Q0 QL LD D0 D8 DHI DSH DSEG PWA UA UAL ACC MI PWC.
  { lia. }
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (SBV_W data ld) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0x966bc].
  (* [comment removed for export] *)
  assert (E : Z.lxor (data + 4 * q + j) 3 = data + (4 * q + j + 3 - 2 * (j mod 4))) by (rewrite lxor3_eq; clear - D8; Z.div_mod_to_equations; lia).
  rewrite E. clear E.
  assert (IDX : 0 <= 4 * q + j + 3 - 2 * (j mod 4) < 4 * ld) by (clear - HK HJ W4 Q0 QL; Z.div_mod_to_equations; lia).
  pose proof (u8arr_store_ok asegs m data bs (4 * q + j + 3 - 2 * (j mod 4)) (wa (data + (4 * q + j + 3 - 2 * (j mod 4)))) UA ltac:(rewrite UAL; exact IDX) ltac:(reflexivity)) as SOK.
  zstep.
  change (le1 s3) with [Z_to_bv 8 (bv_unsigned s3)].
  pose proof (u8arr_write asegs m data bs (4 * q + j + 3 - 2 * (j mod 4)) (Z_to_bv 8 (bv_unsigned s3)) UA ltac:(rewrite UAL; exact IDX)) as UA2.
  clear UA. store_done.
  rewrite <- (upd_length bs (Z.to_nat (4 * q + j + 3 - 2 * (j mod 4))) (Z_to_bv 8 (bv_unsigned s3))) in UAL.
  set (bs1 := upd bs (Z.to_nat (4 * q + j + 3 - 2 * (j mod 4))) (Z_to_bv 8 (bv_unsigned s3))) in *. clearbody bs1. clear IDX.
  lwalk [0x966cc].
  lstep.
  destruct k as [|k].
  - replace (n - j + -1) with 0 by lia. brF. lwalk [0x966e0].
    apply evt_done. unfold bsb_left_exit. do 6 eexists. exists m0, bs1. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UA2|]. split; [exact UAL|]. split; [exact ACC| exact PWC].
  - brT.
    eapply evt_cut.
    + eapply (IH (j + 1)) with (bs := bs1) (q := q) (wpl := wpl) (ld := ld) (w := w) (n := n) (c := n - j + -1) (p := data + 4 * q + j + 1) (l := data + 4 * q);
        try eassumption; try lia.
    +
      intros ms' PO. apply evt_done. unfold bsb_left_exit in PO |- *.
      destruct PO as (x1 & x2 & x3 & x4 & x5 & x6 & m' & bs' & E & MU' & WM' & R).
      do 8 eexists.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Definition bsb_right_exit (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (data ld pw w : Z) : machine_state -> Prop :=
  fun ms' => exists (a1' s2' t3' t4' t5' t6' : word) (m' : mem) (bs' : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x96750) fc None m' (seg_rom asegs)
    /\ munch (SBV_W data ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' data bs' /\ Z.of_nat (length bs') = 4 * ld /\ acc asegs m' data (4 * ld)
    /\ rw_cells asegs m' pw [C4 (Z_to_bv 64 w)].

Lemma bsb_right : forall (k : nat) (j : Z)
    (ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t6 : word) F fc (m : mem)
    (data ld pw w q wpl p p2 l : Z) (bs : list byte),
  p = data + 4 * q + j -> p2 = data + 4 * q + j -> l = data + 4 * q ->
  Z.of_nat k = w - j -> 0 <= j -> (1 <= k)%nat -> 0 < w <= 20000 -> w <= 4 * wpl -> 0 <= q -> q + wpl <= ld -> ld <= 2^24 ->
  0 < data -> data mod 8 = 0 -> data + 4 * ld <= 2^47 -> (data + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= data) ->
  (data + 4 * ld <= 0x10000 \/ SEGTOP_A <= data) ->
  (pw + 4 <= data \/ data + 4 * ld <= pw) ->
  u8arr asegs m data bs -> Z.of_nat (length bs) = 4 * ld -> acc asegs m data (4 * ld) -> mem_inv asegs m ->
  rw_cells asegs m pw [C4 (Z_to_bv 64 w)] ->
  evt asegs (bsb_right_exit ra sp gp tp (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 l) s0 s1 a0 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 (Z_to_bv 64 pw) (Z_to_bv 64 SHB)
                            s10 s11 F fc m data ld pw w)
    (MS (mkR ra sp gp tp (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 l) s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 (Z_to_bv 64 pw) (Z_to_bv 64 SHB) s10 s11 (Z_to_bv 64 p) (Z_to_bv 64 p2) (Z_to_bv 64 j) t6)
        F (Z_to_bv 64 0x966f4) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11 t6 F fc m
    data ld pw w q wpl p p2 l bs -> -> -> HK HJ HK1 WR W4 Q0 QL LD D0 D8 DHI DSH DSEG PWA UA UAL ACC MI PWC.
  { lia. }
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl (SBV_W data ld) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0x96728].
  (* [comment removed for export] *)
  assert (E : Z.lxor (data + 4 * q + j) 3 = data + (4 * q + j + 3 - 2 * (j mod 4))) by (rewrite lxor3_eq; clear - D8; Z.div_mod_to_equations; lia).
  rewrite E. clear E.
  assert (IDX : 0 <= 4 * q + j + 3 - 2 * (j mod 4) < 4 * ld) by (clear - HK HJ W4 Q0 QL; Z.div_mod_to_equations; lia).
  pose proof (u8arr_store_ok asegs m data bs (4 * q + j + 3 - 2 * (j mod 4)) (wa (data + (4 * q + j + 3 - 2 * (j mod 4)))) UA ltac:(rewrite UAL; exact IDX) ltac:(reflexivity)) as SOK.
  zstep.
  change (le1 s3) with [Z_to_bv 8 (bv_unsigned s3)].
  pose proof (u8arr_write asegs m data bs (4 * q + j + 3 - 2 * (j mod 4)) (Z_to_bv 8 (bv_unsigned s3)) UA ltac:(rewrite UAL; exact IDX)) as UA2.
  clear UA. store_done.
  rewrite <- (upd_length bs (Z.to_nat (4 * q + j + 3 - 2 * (j mod 4))) (Z_to_bv 8 (bv_unsigned s3))) in UAL.
  set (bs1 := upd bs (Z.to_nat (4 * q + j + 3 - 2 * (j mod 4))) (Z_to_bv 8 (bv_unsigned s3))) in *. clearbody bs1. clear IDX.
  lwalk [0x9673c].
  rewrite ?(sx32_small w) by lia.
  lstep.
  destruct k as [|k].
  - brF. lwalk [0x96750].
    apply evt_done. unfold bsb_right_exit. do 6 eexists. exists m0, bs1. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UA2|]. split; [exact UAL|]. split; [exact ACC| exact PWC].
  - brT.
    eapply evt_cut.
    + eapply (IH (j + 1)) with (bs := bs1) (q := q) (wpl := wpl) (ld := ld) (w := w) (p := data + 4 * q + j + 1) (p2 := data + 4 * q + j + 1) (l := data + 4 * q);
        try eassumption; try lia.
    +
      intros ms' PO. apply evt_done. unfold bsb_right_exit in PO |- *.
      destruct PO as (x1 & x2 & x3 & x4 & x5 & x6 & m' & bs' & E & MU' & WM' & R).
      do 8 eexists.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bsb_rows1_exit (ra sp gp tp s0 s1 a0 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (data ld pw w : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a6' a7' t3' : word) (m' : mem) (bs' : list byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4 a5 a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
             F (Z_to_bv 64 0x965e4) fc None m' (seg_rom asegs)
    /\ munch (SBV_W data ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' data bs' /\ Z.of_nat (length bs') = 4 * ld /\ acc asegs m' data (4 * ld)
    /\ rw_cells asegs m' pw [C4 (Z_to_bv 64 w)].

Lemma bsb_rows1 : forall (k : nat) (i : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a6 a7 s2 s3 s7 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (data ld pw w wpl n : Z) (bs : list byte),
  Z.of_nat k = n - i -> 0 <= i -> (1 <= k)%nat -> n <= 20000 -> 0 < w <= 20000 -> w <= 4 * wpl -> 0 < wpl <= 5001 -> n * wpl <= ld -> ld <= 2^24 ->
  0 < data -> data mod 8 = 0 -> data + 4 * ld <= 2^47 -> (data + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= data) ->
  (data + 4 * ld <= 0x10000 \/ SEGTOP_A <= data) ->
  (pw + 4 <= data \/ data + 4 * ld <= pw) ->
  u8arr asegs m data bs -> Z.of_nat (length bs) = 4 * ld -> acc asegs m data (4 * ld) -> mem_inv asegs m ->
  rw_cells asegs m pw [C4 (Z_to_bv 64 w)] ->
  evt asegs (bsb_rows1_exit ra sp gp tp s0 s1 a0 (Z_to_bv 64 1) (Z_to_bv 64 3) s2 s3 (Z_to_bv 64 data) (Z_to_bv 64 wpl) (Z_to_bv 64 n) s7 (Z_to_bv 64 pw) (Z_to_bv 64 SHB)
                            s10 s11 t4 t5 t6 F fc m data ld pw w)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (i * wpl)) (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 3) a6 a7
             s2 s3 (Z_to_bv 64 data) (Z_to_bv 64 wpl) (Z_to_bv 64 n) s7 (Z_to_bv 64 pw) (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x961c4) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a6 a7 s2 s3 s7 s10 s11 t3 t4 t5 t6 F fc m
    data ld pw w wpl n bs HK HI HK1 NB WR W4 WPLB NL LD D0 D8 DHI DSH DSEG PWA UA UAL ACC MI PWC.
  { lia. }
  assert (QL : i * wpl + wpl <= ld).
  { clear - HK HI WPLB NL. pose proof (Z.mul_le_mono_nonneg_r (i + 1) n wpl ltac:(lia) ltac:(lia)) as N. rewrite Z.mul_add_distr_r in N. lia. }
  assert (Q0 : 0 <= i * wpl) by (clear - HI WPLB; apply Z.mul_nonneg_nonneg; lia).
  unfold SHB in *.
  lwalk [0x961f8].
  lstep. rewrite ?(sx32_small w) by lia.
  lwalk [0x96210].
  eapply evt_cut.
  { eapply (bsb_fill1 (Z.to_nat w) 0) with (q := i * wpl) (wpl := wpl) (ld := ld) (w := w) (bs := bs); try eassumption; try lia.
    all: rewrite ?Z.add_0_r, ?(Z.mod_small (i * wpl)) by lia; lia. }
  intros ms' PO. unfold bsb_fill1_exit in PO.
  destruct PO as (x1 & x2 & x3 & x4 & x5 & x6 & m' & bs' & -> & MU' & WM' & MI' & UA' & UAL' & ACC' & PWC').
  unfold SHB in *.
  lwalk [0x961c0].
  rewrite ?(bv_swrap_small 32 (i + 1)), ?(bv_swrap_small 32 (i * wpl + wpl)) by (change (bv_half_modulus 32) with (2^31); lia).
  replace (i * wpl + wpl) with ((i + 1) * wpl) by lia.
  lstep.
  destruct k as [|k].
  - replace (i + 1) with n by lia. brT.
    apply evt_done. unfold bsb_rows1_exit. do 9 eexists. exists m', bs'. split; [reflexivity|].
    split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact UA'|]. split; [exact UAL'|]. split; [exact ACC'| exact PWC'].
  - brF.
    eapply evt_cut.
    + eapply (IH (i + 1)) with (bs := bs') (wpl := wpl) (ld := ld) (w := w) (n := n); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold bsb_rows1_exit in PO |- *.
      destruct PO as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & m'' & bs'' & E & MU'' & WM'' & R).
      do 11 eexists.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU' MU'')|]. split; [exact (wmono_trans asegs _ _ _ WM' WM'')| exact R].
Qed.

(* [comment removed for export] *)
Definition bsb_rows2_exit (ra sp gp tp t0 t1 s0 s1 a0 a2 a3 a4 a6 a7 s3 s4 s5 s7 s8 s9 s10 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (data ld pw w : Z) : machine_state -> Prop :=
  fun ms' => exists (t2' a1' a5' s2' s6' s11' t3' t4' t5' t6' : word) (m' : mem) (bs' : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2' s0 s1 a0 a1' a2 a3 a4 a5' a6 a7 s2' s3 s4 s5 s6' s7 s8 s9 s10 s11' t3' t4' t5' t6')
             F (Z_to_bv 64 0x96764) fc None m' (seg_rom asegs)
    /\ munch (SBV_W data ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' data bs' /\ Z.of_nat (length bs') = 4 * ld /\ acc asegs m' data (4 * ld)
    /\ rw_cells asegs m' pw [C4 (Z_to_bv 64 w)].

Lemma bsb_rows2 : forall (k : nat) (i : Z)
    (ra sp gp tp t2 s0 s1 a1 s2 s3 s7 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (data ld pw w wpl n nl rj pr pr2 : Z) (bs : list byte),
  pr = data + rj -> pr2 = data + rj ->
  Z.of_nat k = n - i -> 0 <= i -> (1 <= k)%nat -> n <= 20000 -> 0 < w <= 20000 -> w <= 4 * wpl -> 0 < wpl <= 5001 -> n * wpl <= ld -> ld <= 2^24 ->
  0 < nl <= w -> 0 <= rj < w ->
  0 < data -> data mod 8 = 0 -> data + 4 * ld <= 2^47 -> (data + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= data) ->
  (data + 4 * ld <= 0x10000 \/ SEGTOP_A <= data) ->
  (pw + 4 <= data \/ data + 4 * ld <= pw) ->
  u8arr asegs m data bs -> Z.of_nat (length bs) = 4 * ld -> acc asegs m data (4 * ld) -> mem_inv asegs m ->
  rw_cells asegs m pw [C4 (Z_to_bv 64 w)] ->
  evt asegs (bsb_rows2_exit ra sp gp tp (Z_to_bv 64 1) (Z_to_bv 64 3) s0 s1 (Z_to_bv 64 nl) (Z_to_bv 64 n) (Z_to_bv 64 rj) (Z_to_bv 64 nl) (Z_to_bv 64 pr) (Z_to_bv 64 pr2)
                            s3 (Z_to_bv 64 data) (Z_to_bv 64 wpl) s7 (Z_to_bv 64 pw) (Z_to_bv 64 SHB) s10 F fc m data ld pw w)
    (MS (mkR ra sp gp tp (Z_to_bv 64 1) (Z_to_bv 64 3) t2 s0 s1 (Z_to_bv 64 nl) a1 (Z_to_bv 64 n) (Z_to_bv 64 rj) (Z_to_bv 64 nl) (Z_to_bv 64 (i * wpl))
             (Z_to_bv 64 pr) (Z_to_bv 64 pr2)
             s2 s3 (Z_to_bv 64 data) (Z_to_bv 64 wpl) (Z_to_bv 64 i) s7 (Z_to_bv 64 pw) (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9664c) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra sp gp tp t2 s0 s1 a1 s2 s3 s7 s10 s11 t3 t4 t5 t6 F fc m
    data ld pw w wpl n nl rj pr pr2 bs PR PR2 HK HI HK1 NB WR W4 WPLB NL LD NLB RJB D0 D8 DHI DSH DSEG PWA UA UAL ACC MI PWC.
  { lia. }
  assert (QL : i * wpl + wpl <= ld).
  { clear - HK HI WPLB NL. pose proof (Z.mul_le_mono_nonneg_r (i + 1) n wpl ltac:(lia) ltac:(lia)) as N. rewrite Z.mul_add_distr_r in N. lia. }
  assert (Q0 : 0 <= i * wpl) by (clear - HI WPLB; apply Z.mul_nonneg_nonneg; lia).
  unfold SHB in *.
  lwalk [0x96694].
  eapply evt_cut.
  { eapply (bsb_left (Z.to_nat nl) 0) with (q := i * wpl) (wpl := wpl) (ld := ld) (w := w) (n := nl) (c := nl) (bs := bs); try eassumption; try lia.
    all: rewrite ?Z.add_0_r, ?(Z.mod_small (i * wpl)) by lia; lia. }
  intros ms' PO. unfold bsb_left_exit in PO.
  destruct PO as (x1 & x2 & x3 & x4 & x5 & x6 & m' & bs' & -> & MU' & WM' & MI' & UA' & UAL' & ACC' & PWC').
  unfold SHB in *.
  lstep. rewrite ?(sx32_small w) by lia.
  lwalk [0x966f4].
  eapply evt_cut.
  { eapply (bsb_right (Z.to_nat (w - rj)) rj) with (q := i * wpl) (wpl := wpl) (ld := ld) (w := w) (bs := bs'); try eassumption; try lia.
    all: rewrite ?Z.add_0_r, ?(Z.mod_small (i * wpl)) by lia; lia. }
  intros ms' PO. unfold bsb_right_exit in PO.
  destruct PO as (y1 & y2 & y3 & y4 & y5 & y6 & m'' & bs'' & -> & MU'' & WM'' & MI'' & UA'' & UAL'' & ACC'' & PWC'').
  unfold SHB in *.
  pose proof (munch_trans _ _ _ _ MU' MU'') as MU2. pose proof (wmono_trans asegs _ _ _ WM' WM'') as WM2.
  lwalk [0x96760].
  rewrite ?(bv_swrap_small 32 (i + 1)), ?(bv_swrap_small 32 (i * wpl + wpl)) by (change (bv_half_modulus 32) with (2^31); lia).
  replace (i * wpl + wpl) with ((i + 1) * wpl) by lia.
  lstep.
  destruct k as [|k].
  - brF.
    apply evt_done. unfold bsb_rows2_exit. do 10 eexists. exists m'', bs''. split; [reflexivity|].
    split; [exact MU2|]. split; [exact WM2|]. split; [exact MI''|]. split; [exact UA''|]. split; [exact UAL''|]. split; [exact ACC''| exact PWC''].
  - brT.
    eapply evt_cut.
    + eapply (IH (i + 1)) with (bs := bs'') (wpl := wpl) (ld := ld) (w := w) (n := n) (nl := nl) (rj := rj) (pr := pr) (pr2 := pr2); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold bsb_rows2_exit in PO |- *.
      destruct PO as (z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & m3 & bs3 & E & MU3 & WM3 & R).
      do 12 eexists.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU2 MU3)|]. split; [exact (wmono_trans asegs _ _ _ WM2 WM3)| exact R].
Qed.

(* [comment removed for export] *)
Definition bsb_rows3_exit (ra sp gp tp s0 s1 a0 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (data ld pw w ph h : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a6' a7' t3' : word) (m' : mem) (bs' : list byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4 a5 a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
             F (Z_to_bv 64 0x96a84) fc None m' (seg_rom asegs)
    /\ munch (SBV_W data ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' data bs' /\ Z.of_nat (length bs') = 4 * ld /\ acc asegs m' data (4 * ld)
    /\ rw_cells asegs m' pw [C4 (Z_to_bv 64 w)] /\ rw_cells asegs m' ph [C4 (Z_to_bv 64 h)].

Lemma bsb_rows3 : forall (k : nat) (i : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a6 a7 s2 s3 s6 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (data ld pw w ph h wpl : Z) (bs : list byte),
  Z.of_nat k = h - i -> 0 <= i -> (1 <= k)%nat -> 0 < h <= 20000 -> 0 < w <= 20000 -> w <= 4 * wpl -> 0 < wpl <= 5001 -> h * wpl <= ld -> ld <= 2^24 ->
  0 < data -> data mod 8 = 0 -> data + 4 * ld <= 2^47 -> (data + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= data) ->
  (data + 4 * ld <= 0x10000 \/ SEGTOP_A <= data) ->
  (pw + 4 <= data \/ data + 4 * ld <= pw) -> (ph + 4 <= data \/ data + 4 * ld <= ph) ->
  u8arr asegs m data bs -> Z.of_nat (length bs) = 4 * ld -> acc asegs m data (4 * ld) -> mem_inv asegs m ->
  rw_cells asegs m pw [C4 (Z_to_bv 64 w)] -> rw_cells asegs m ph [C4 (Z_to_bv 64 h)] ->
  evt asegs (bsb_rows3_exit ra sp gp tp s0 s1 a0 (Z_to_bv 64 1) (Z_to_bv 64 3) s2 s3 (Z_to_bv 64 data) (Z_to_bv 64 wpl) s6 (Z_to_bv 64 ph) (Z_to_bv 64 pw) (Z_to_bv 64 SHB)
                            s10 s11 t4 t5 t6 F fc m data ld pw w ph h)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 i) (Z_to_bv 64 (i * wpl)) (Z_to_bv 64 1) (Z_to_bv 64 3) a6 a7
             s2 s3 (Z_to_bv 64 data) (Z_to_bv 64 wpl) s6 (Z_to_bv 64 ph) (Z_to_bv 64 pw) (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x96778) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a6 a7 s2 s3 s6 s10 s11 t3 t4 t5 t6 F fc m
    data ld pw w ph h wpl bs HK HI HK1 HB WR W4 WPLB NL LD D0 D8 DHI DSH DSEG PWA PHA UA UAL ACC MI PWC PHC.
  { lia. }
  assert (QL : i * wpl + wpl <= ld).
  { clear - HK HI WPLB NL. pose proof (Z.mul_le_mono_nonneg_r (i + 1) h wpl ltac:(lia) ltac:(lia)) as N. rewrite Z.mul_add_distr_r in N. lia. }
  assert (Q0 : 0 <= i * wpl) by (clear - HI WPLB; apply Z.mul_nonneg_nonneg; lia).
  unfold SHB in *.
  lwalk [0x967ac].
  lstep. rewrite ?(sx32_small w) by lia.
  lwalk [0x967c4].
  eapply evt_cut.
  { eapply (bsb_fill3 (Z.to_nat w) 0) with (q := i * wpl) (wpl := wpl) (ld := ld) (w := w) (bs := bs); try eassumption; try lia.
    all: rewrite ?Z.add_0_r, ?(Z.mod_small (i * wpl)) by lia; lia. }
  intros ms' PO. unfold bsb_fill3_exit in PO.
  destruct PO as (x1 & x2 & x3 & x4 & x5 & x6 & m' & bs' & -> & MU' & WM' & MI' & UA' & UAL' & ACC' & PWC').
  unfold SHB in *.
  assert (PHC' : rw_cells asegs m' ph [C4 (Z_to_bv 64 h)]).
  { apply (rw_cells_transport asegs (SBV_W data ld) m m' ph _ PHC MU' WM'). cbn [disjoint_from cells_size csize Nat.add]. split; [lia| exact I]. }
  lwalk [0x9681c].
  lstep. rewrite ?(sx32_small h) by lia.
  lwalk [0x96828].
  rewrite ?(bv_swrap_small 32 (i + 1)), ?(bv_swrap_small 32 (i * wpl + wpl)) by (change (bv_half_modulus 32) with (2^31); lia).
  replace (i * wpl + wpl) with ((i + 1) * wpl) by lia.
  lstep.
  destruct k as [|k].
  - brF. lwalk [0x96a84].
    apply evt_done. unfold bsb_rows3_exit. do 9 eexists. exists m', bs'. split; [reflexivity|].
    split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact UA'|]. split; [exact UAL'|]. split; [exact ACC'|]. split; [exact PWC'| exact PHC'].
  - brT.
    eapply evt_cut.
    + eapply (IH (i + 1)) with (bs := bs') (wpl := wpl) (ld := ld) (w := w) (h := h); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold bsb_rows3_exit in PO |- *.
      destruct PO as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & m'' & bs'' & E & MU'' & WM'' & R).
      do 11 eexists.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU' MU'')|]. split; [exact (wmono_trans asegs _ _ _ WM' WM'')| exact R].
Qed.
