(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import ImageA.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import Layout.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.A08 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.



(* [comment removed for export] *)
Definition gmax_rowend (sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s9 s10 t3 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (ra' a1' s6' s7' s8' t4' t5' t6' : word),
    ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6' s7' s8' s9 s10 (Z_to_bv 64 SHB) t3 t4' t5' t6')
             F (Z_to_bv 64 0x9243c) fc None m (seg_rom asegs).

Lemma gmax8 : forall (k : nat) (j : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 : word) F fc (m : mem)
    (data n line w c : Z) (bs : list byte),
  Z.of_nat k = w - j -> c = w - j -> 0 <= j -> (1 <= k)%nat ->
  data <= line -> line mod 4 = 0 -> line + 4 * ((w + 3) / 4) <= data + n -> 0 < data -> data mod 8 = 0 -> data + n <= 2^47 ->
  (data + n <= 0x7fff7000 \/ 0x10007fff8000 <= data) ->
  bytes_at asegs m data bs -> Z.of_nat (length bs) = n -> acc asegs m data n -> mem_inv asegs m ->
  evt asegs (gmax_rowend sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s9 s10 t3 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 SHB) t3 t4
             (Z_to_bv 64 c) (Z_to_bv 64 (line + j)))
        F (Z_to_bv 64 0x92324) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 F fc m
    data n line w c bs HK -> HJ HK1 DL L4 LN D0 D8 DHI DSH HB HBL ACC MI.
  { lia. }
  pose proof (lxor3_eq (line + j)) as LX.
  lwalk (@nil Z).
  destruct (bytes_at_read1 m data bs (Z.lxor (line + j) 3 - data) HB ltac:(lia)) as (bv & R).
  replace (data + (Z.lxor (line + j) 3 - data)) with (Z.lxor (line + j) 3) in R by lia.
  lstep. clear R.
  (* [comment removed for export] *)
  assert (STEP : forall (a1' s6' s7' t4' : word),
    evt asegs (gmax_rowend sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s9 s10 t3 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6' s7' s8 s9 s10 (Z_to_bv 64 SHB) t3 t4'
               (Z_to_bv 64 (w - j)) (Z_to_bv 64 (line + j)))
          F (Z_to_bv 64 0x92318) fc None m (seg_rom asegs))).
  { intros. lwalk [0x92324; 0x9243c].
    replace (w - j + -1) with (w - (j + 1)) by lia. replace (line + j + 1) with (line + (j + 1)) by lia.
    destruct k as [|k].
    - assert (EJ : j + 1 = w) by lia. rewrite EJ in *. rewrite Z.sub_diag.
      brT. apply evt_done. unfold gmax_rowend. do 8 eexists. reflexivity.
    - brF. eapply (IH (j + 1)) with (bs := bs) (n := n) (data := data) (w := w); try eassumption; try reflexivity; try lia. }
  lwalk (@nil Z).
  brfork LT.
  - lwalk [0x92318]. apply STEP.
  - lwalk [0x92318]. apply STEP.
Qed.

(* [comment removed for export] *)
Lemma gmax4 : forall (k : nat) (j : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 t3 t4 : word) F fc (m : mem)
    (data n line w : Z) (bs : list byte),
  Z.of_nat k = w - j -> 0 <= j -> (1 <= k)%nat -> w <= 2^20 ->
  data <= line -> line mod 4 = 0 -> line + 4 * ((w + 7) / 8) <= data + n -> 0 < data -> data mod 8 = 0 -> data + n <= 2^47 ->
  (data + n <= 0x7fff7000 \/ 0x10007fff8000 <= data) ->
  bytes_at asegs m data bs -> Z.of_nat (length bs) = n -> acc asegs m data n -> mem_inv asegs m ->
  evt asegs (gmax_rowend sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s9 s10 t3 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (4 * j)) (Z_to_bv 64 j) s8 s9 s10 (Z_to_bv 64 SHB) t3 t4
             (Z_to_bv 64 line) (Z_to_bv 64 w))
        F (Z_to_bv 64 0x9237c) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 t3 t4 F fc m
    data n line w bs HK HJ HK1 HW DL L4 LN D0 D8 DHI DSH HB HBL ACC MI.
  { lia. }
  (* [comment removed for export] *)
  assert (STEP : forall (ra' a1' s8' t4' : word),
    evt asegs (gmax_rowend sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s9 s10 t3 F fc m)
      (MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (4 * j)) (Z_to_bv 64 j) s8' s9 s10 (Z_to_bv 64 SHB) t3 t4'
               (Z_to_bv 64 line) (Z_to_bv 64 w))
          F (Z_to_bv 64 0x9236c) fc None m (seg_rom asegs))).
  { intros. lwalk [0x9237c; 0x9243c]. swrap32_fix.
    replace (4 * j + 4) with (4 * (j + 1)) by lia.
    destruct k as [|k].
    - assert (EJ : j + 1 = w) by lia. rewrite EJ in *.
      brT. apply evt_done. unfold gmax_rowend. do 8 eexists. reflexivity.
    - brF. eapply (IH (j + 1)) with (bs := bs) (n := n) (data := data) (w := w); try eassumption; try lia. }
  lwalk [0x92388].
  rewrite (srliw_idx j 8) by lia.
  replace (line + j / 8 * 4) with (line + 4 * (j / 8)) by lia.
  lwalk (@nil Z).
  destruct (bytes_at_read4w m data bs (line + 4 * (j / 8) - data) HB ltac:(lia) ltac:(lia)) as (wv & R).
  replace (data + (line + 4 * (j / 8) - data)) with (line + 4 * (j / 8)) in R by lia.
  lstep. clear R.
  lwalk (@nil Z).
  brfork LT.
  - lwalk [0x9236c]. apply STEP.
  - lwalk [0x9236c]. apply STEP.
Qed.

(* [comment removed for export] *)
Lemma gmax2 : forall (k : nat) (j : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 t3 t4 : word) F fc (m : mem)
    (data n line w : Z) (bs : list byte),
  Z.of_nat k = w - j -> 0 <= j -> (1 <= k)%nat -> w <= 2^20 ->
  data <= line -> line mod 4 = 0 -> line + 4 * ((w + 15) / 16) <= data + n -> 0 < data -> data mod 8 = 0 -> data + n <= 2^47 ->
  (data + n <= 0x7fff7000 \/ 0x10007fff8000 <= data) ->
  bytes_at asegs m data bs -> Z.of_nat (length bs) = n -> acc asegs m data n -> mem_inv asegs m ->
  evt asegs (gmax_rowend sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s9 s10 t3 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (2 * j)) (Z_to_bv 64 j) s8 s9 s10 (Z_to_bv 64 SHB) t3 t4
             (Z_to_bv 64 line) (Z_to_bv 64 w))
        F (Z_to_bv 64 0x923f0) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 t3 t4 F fc m
    data n line w bs HK HJ HK1 HW DL L4 LN D0 D8 DHI DSH HB HBL ACC MI.
  { lia. }
  (* [comment removed for export] *)
  assert (STEP : forall (ra' a1' s8' t4' : word),
    evt asegs (gmax_rowend sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s9 s10 t3 F fc m)
      (MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (2 * j)) (Z_to_bv 64 j) s8' s9 s10 (Z_to_bv 64 SHB) t3 t4'
               (Z_to_bv 64 line) (Z_to_bv 64 w))
          F (Z_to_bv 64 0x923e0) fc None m (seg_rom asegs))).
  { intros. lwalk [0x923f0; 0x9243c]. swrap32_fix.
    replace (2 * j + 2) with (2 * (j + 1)) by lia.
    destruct k as [|k].
    - assert (EJ : j + 1 = w) by lia. rewrite EJ in *.
      brT. apply evt_done. unfold gmax_rowend. do 8 eexists. reflexivity.
    - brF. eapply (IH (j + 1)) with (bs := bs) (n := n) (data := data) (w := w); try eassumption; try lia. }
  lwalk [0x923fc].
  rewrite (srliw_idx j 16) by lia.
  replace (line + j / 16 * 4) with (line + 4 * (j / 16)) by lia.
  lwalk (@nil Z).
  destruct (bytes_at_read4w m data bs (line + 4 * (j / 16) - data) HB ltac:(lia) ltac:(lia)) as (wv & R).
  replace (data + (line + 4 * (j / 16) - data)) with (line + 4 * (j / 16)) in R by lia.
  lstep. clear R.
  lwalk (@nil Z).
  brfork LT.
  - lwalk [0x923e0]. apply STEP.
  - lwalk [0x923e0]. apply STEP.
Qed.

(* [comment removed for export] *)
Definition gmax_exit (sp gp tp s0 s1 s2 s3 s4 s5 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s7' s8' t3' t4' t5' t6' : word),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6' s7' s8' s9 s10 (Z_to_bv 64 SHB) t3' t4' t5' t6')
             F (Z_to_bv 64 0x924a0) fc None m (seg_rom asegs).

Lemma gmax_rows : forall (k : nat) (i : Z)
    (ra sp gp tp t1 s0 s1 a1 a7 s2 s3 s6 s7 s8 s9 s10 t4 t5 t6 : word) F fc (m : mem)
    (data wpl h w d wa : Z) (bs : list byte),
  Z.of_nat k = h - i -> 0 <= i -> (1 <= k)%nat ->
  (d = 2 \/ d = 4 \/ d = 8) -> 0 < w <= 2^20 -> (w * d + 31) / 32 <= wpl -> 0 < wpl <= 2^20 -> 0 < h <= 2^20 -> wpl * h <= 2^24 ->
  0 < data -> data mod 8 = 0 -> data + 4 * (wpl * h) <= 2^47 -> (data + 4 * (wpl * h) <= 0x7fff7000 \/ 0x10007fff8000 <= data) ->
  bytes_at asegs m data bs -> Z.of_nat (length bs) = 4 * (wpl * h) -> acc asegs m data (4 * (wpl * h)) ->
  rw_cells asegs m wa [C4 (Z_to_bv 64 w)] -> mem_inv asegs m ->
  evt asegs (gmax_exit sp gp tp s0 s1 s2 s3 (Z_to_bv 64 wa) (Z_to_bv 64 wpl) s9 s10 F fc m)
    (MS (mkR ra sp gp tp (Z_to_bv 64 4) t1 (Z_to_bv 64 8) s0 s1 (Z_to_bv 64 data) a1 (Z_to_bv 64 h) (Z_to_bv 64 i) (Z_to_bv 64 d)
             (Z_to_bv 64 (wpl * 4)) (Z_to_bv 64 2) a7 s2 s3 (Z_to_bv 64 wa) (Z_to_bv 64 wpl) s6 s7 s8 s9 s10 (Z_to_bv 64 SHB)
             (Z_to_bv 64 (data + 4 * (i * wpl))) t4 t5 t6)
        F (Z_to_bv 64 0x922f0) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra sp gp tp t1 s0 s1 a1 a7 s2 s3 s6 s7 s8 s9 s10 t4 t5 t6 F fc m data wpl h w d wa bs
    HK HI HK1 HD HW HWPL WPL HH WH D0 D8 DHI DSH HB HBL ACC WC MI.
  { lia. }
  assert (NL : i * wpl + wpl <= wpl * h) by nia.
  assert (NL0 : 0 <= i * wpl) by nia.
  (* [comment removed for export] *)
  assert (ROWEND : forall ms', gmax_rowend sp gp tp (Z_to_bv 64 4) t1 (Z_to_bv 64 8) s0 s1 (Z_to_bv 64 data) (Z_to_bv 64 h) (Z_to_bv 64 i) (Z_to_bv 64 d)
                                 (Z_to_bv 64 (wpl * 4)) (Z_to_bv 64 2) a7 s2 s3 (Z_to_bv 64 wa) (Z_to_bv 64 wpl) s9 s10
                                 (Z_to_bv 64 (data + 4 * (i * wpl))) F fc m ms' ->
                       evt asegs (gmax_exit sp gp tp s0 s1 s2 s3 (Z_to_bv 64 wa) (Z_to_bv 64 wpl) s9 s10 F fc m) ms').
  { intros ms' (ra' & a1' & s6' & s7' & s8' & t4' & t5' & t6' & ->).
    lwalk (@nil Z).
    brfork MAXED.
    - (* [comment removed for export] *)
      apply evt_done. unfold gmax_exit. do 19 eexists. reflexivity.
    - lwalk [0x922f0; 0x924a0].
      replace (data + 4 * (i * wpl) + wpl * 4) with (data + 4 * ((i + 1) * wpl)) by lia.
      destruct k as [|k].
      + assert (EI : i + 1 = h) by lia. rewrite EI in *.
        brF. lwalk [0x924a0]. apply evt_done. unfold gmax_exit. do 19 eexists. reflexivity.
      + brT. eapply (IH (i + 1)) with (bs := bs) (w := w); try eassumption; try lia. }
  lwalk [0x922fc].
  replace (data + i * wpl * 4) with (data + 4 * (i * wpl)) by lia.
  set (line := data + 4 * (i * wpl)) in *.
  assert (LR : data <= line /\ line mod 4 = 0 /\ line + 4 * wpl <= data + 4 * (wpl * h)) by (unfold line; repeat split; [lia| Z.div_mod_to_equations; lia| lia]).
  destruct LR as (L1 & L2 & L3).
  destruct HD as [-> | [-> | ->]].
  - (* [comment removed for export] *)
    lwalk [0x923f0]. sx32_fix. lwalk [0x923f0].
    eapply evt_cut; [| exact ROWEND].
    eapply (gmax2 (Z.to_nat w) 0) with (bs := bs) (n := 4 * (wpl * h)) (data := data) (w := w); try eassumption; try lia.
  - (* [comment removed for export] *)
    lwalk [0x9237c]. sx32_fix. lwalk [0x9237c].
    eapply evt_cut; [| exact ROWEND].
    eapply (gmax4 (Z.to_nat w) 0) with (bs := bs) (n := 4 * (wpl * h)) (data := data) (w := w); try eassumption; try lia.
  - (* [comment removed for export] *)
    lwalk [0x92324]. sx32_fix. lwalk [0x92324].
    replace (Z_to_bv 64 line) with (Z_to_bv 64 (line + 0)) by (f_equal; lia).
    eapply evt_cut.
    + eapply (gmax8 (Z.to_nat w) 0) with (bs := bs) (n := 4 * (wpl * h)) (data := data) (w := w); try eassumption; try lia.
    + replace (Z_to_bv 64 (line + 0)) with (Z_to_bv 64 line) by (f_equal; lia). exact ROWEND.
Qed.
