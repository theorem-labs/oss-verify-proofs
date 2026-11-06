(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptB_guard LeptL_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition gmax_rowend (sp gp tp t0 t1 t3 s0 s1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (data : Z)
    : machine_state -> Prop :=
  fun ms' => exists (ra' a0' a1' s6' s7' s8' t5' t6' : word),
    ms' = MS (mkR ra' sp gp tp t0 t1 (Z_to_bv 64 data) s0 s1 a0' a1' a2 a3 a4 a5 (Z_to_bv 64 1) a7 s2 s3 s4 s5 s6' s7' s8' s9 s10 (Z_to_bv 64 SHB)
                  t3 (Z_to_bv 64 3) t5' t6')
             F (Z_to_bv 64 0x909a8) fc None m (seg_rom asegs).

(* [comment removed for export] *)
Lemma gmax8 : forall (k : nat) (j : Z)
    (ra sp gp tp t0 t1 t3 s0 s1 a0 a1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s9 s10 t6 : word) F fc (m : mem)
    (data n line w c p : Z) (bs : list byte),
  Z.of_nat k = w - j -> c = w - j -> p = line + j -> 0 <= j -> (1 <= k)%nat -> w <= 2^20 ->
  data <= line -> line mod 4 = 0 -> line + 4 * ((w + 3) / 4) <= data + n -> 0 < data -> data mod 8 = 0 -> data + n <= 2^47 ->
  (data + n <= 0x7fff7000 \/ 0x10007fff8000 <= data) ->
  bytes_at asegs m data bs -> Z.of_nat (length bs) = n -> acc asegs m data n -> mem_inv asegs m ->
  evt asegs (gmax_rowend sp gp tp t0 t1 t3 s0 s1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s9 s10 F fc m data)
    (MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 data) s0 s1 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 1) a7 s2 s3 s4 s5
             (Z_to_bv 64 c) (Z_to_bv 64 p) (Z_to_bv 64 p) s9 s10 (Z_to_bv 64 SHB)
             t3 (Z_to_bv 64 3) (Z_to_bv 64 line) t6)
        F (Z_to_bv 64 0x90844) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t0 t1 t3 s0 s1 a0 a1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s9 s10 t6 F fc m
    data n line w c p bs HK -> -> HJ HK1 HW DL L4 LN D0 D8 DHI DSH HB HBL ACC MI.
  { lia. }
  pose proof (lxor3_eq (line + j)) as LX.
  assert (STEP : forall (ra' a0' a1' t6' : word),
    evt asegs (gmax_rowend sp gp tp t0 t1 t3 s0 s1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s9 s10 F fc m data)
      (MS (mkR ra' sp gp tp t0 t1 (Z_to_bv 64 data) s0 s1 a0' a1' a2 a3 a4 a5 (Z_to_bv 64 1) a7 s2 s3 s4 s5
               (Z_to_bv 64 (w - j)) (Z_to_bv 64 (line + j)) (Z_to_bv 64 (line + j)) s9 s10 (Z_to_bv 64 SHB)
               t3 (Z_to_bv 64 3) (Z_to_bv 64 line) t6')
          F (Z_to_bv 64 0x90834) fc None m (seg_rom asegs))).
  { intros. gwalk [0x90844; 0x909a8].
    replace (w - j + -1) with (w - (j + 1)) by lia. replace (line + j + 1) with (line + (j + 1)) by lia.
    destruct k as [|k].
    - assert (EJ : j + 1 = w) by lia. rewrite EJ in *. rewrite Z.sub_diag.
      brT. apply evt_done. unfold gmax_rowend. do 8 eexists. reflexivity.
    - brF. eapply (IH (j + 1)) with (bs := bs) (n := n) (w := w); try eassumption; try reflexivity; try lia. }
  gwalk (@nil Z).
  destruct (bytes_at_read1 m data bs (Z.lxor (line + j) 3 - data) HB ltac:(lia)) as (bv & R).
  replace (data + (Z.lxor (line + j) 3 - data)) with (Z.lxor (line + j) 3) in R by lia.
  lstep. clear R.
  gwalk (@nil Z).
  brfork LT.
  - gwalk [0x90834]. apply STEP.
  - gwalk [0x90834]. apply STEP.
Qed.

(* [comment removed for export] *)
Lemma gmax4 : forall (k : nat) (j : Z)
    (ra sp gp tp t0 t1 t3 s0 s1 a0 a1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s9 s10 t6 : word) F fc (m : mem)
    (data n line w : Z) (bs : list byte),
  Z.of_nat k = w - j -> 0 <= j -> (1 <= k)%nat -> w <= 2^20 ->
  data <= line -> line mod 4 = 0 -> line + 4 * ((w + 7) / 8) <= data + n -> 0 < data -> data mod 8 = 0 -> data + n <= 2^47 ->
  (data + n <= 0x7fff7000 \/ 0x10007fff8000 <= data) ->
  bytes_at asegs m data bs -> Z.of_nat (length bs) = n -> acc asegs m data n -> mem_inv asegs m ->
  evt asegs (gmax_rowend sp gp tp t0 t1 t3 s0 s1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s9 s10 F fc m data)
    (MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 data) s0 s1 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 1) a7 s2 s3 s4 s5
             (Z_to_bv 64 w) (Z_to_bv 64 (4 * j)) (Z_to_bv 64 j) s9 s10 (Z_to_bv 64 SHB)
             t3 (Z_to_bv 64 3) (Z_to_bv 64 line) t6)
        F (Z_to_bv 64 0x908b0) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t0 t1 t3 s0 s1 a0 a1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s9 s10 t6 F fc m
    data n line w bs HK HJ HK1 HW DL L4 LN D0 D8 DHI DSH HB HBL ACC MI.
  { lia. }
  assert (STEP : forall (ra' a0' a1' t6' : word),
    evt asegs (gmax_rowend sp gp tp t0 t1 t3 s0 s1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s9 s10 F fc m data)
      (MS (mkR ra' sp gp tp t0 t1 (Z_to_bv 64 data) s0 s1 a0' a1' a2 a3 a4 a5 (Z_to_bv 64 1) a7 s2 s3 s4 s5
               (Z_to_bv 64 w) (Z_to_bv 64 (4 * j)) (Z_to_bv 64 j) s9 s10 (Z_to_bv 64 SHB)
               t3 (Z_to_bv 64 3) (Z_to_bv 64 line) t6')
          F (Z_to_bv 64 0x908a0) fc None m (seg_rom asegs))).
  { intros. gwalk [0x908b0; 0x909a8]. swrap_fix.
    replace (4 * j + 4) with (4 * (j + 1)) by lia.
    destruct k as [|k].
    - assert (EJ : j + 1 = w) by lia. rewrite EJ in *.
      brT. apply evt_done. unfold gmax_rowend. do 8 eexists. reflexivity.
    - brF. eapply (IH (j + 1)) with (bs := bs) (n := n) (w := w); try eassumption; try lia. }
  gwalk [0x908bc].
  rewrite (srliw_idx j 8) by lia.
  replace (line + j / 8 * 4) with (line + 4 * (j / 8)) by lia.
  gwalk (@nil Z).
  destruct (bytes_at_read4w m data bs (line + 4 * (j / 8) - data) HB ltac:(lia) ltac:(lia)) as (wv & R).
  replace (data + (line + 4 * (j / 8) - data)) with (line + 4 * (j / 8)) in R by lia.
  lstep. clear R.
  gwalk (@nil Z).
  brfork LT.
  - gwalk [0x908a0]. apply STEP.
  - gwalk [0x908a0]. apply STEP.
Qed.

(* [comment removed for export] *)
Lemma gmax2 : forall (k : nat) (j : Z)
    (ra sp gp tp t0 t1 t3 s0 s1 a0 a1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s9 s10 t6 : word) F fc (m : mem)
    (data n line w : Z) (bs : list byte),
  Z.of_nat k = w - j -> 0 <= j -> (1 <= k)%nat -> w <= 2^20 ->
  data <= line -> line mod 4 = 0 -> line + 4 * ((w + 15) / 16) <= data + n -> 0 < data -> data mod 8 = 0 -> data + n <= 2^47 ->
  (data + n <= 0x7fff7000 \/ 0x10007fff8000 <= data) ->
  bytes_at asegs m data bs -> Z.of_nat (length bs) = n -> acc asegs m data n -> mem_inv asegs m ->
  evt asegs (gmax_rowend sp gp tp t0 t1 t3 s0 s1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s9 s10 F fc m data)
    (MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 data) s0 s1 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 1) a7 s2 s3 s4 s5
             (Z_to_bv 64 w) (Z_to_bv 64 (2 * j)) (Z_to_bv 64 j) s9 s10 (Z_to_bv 64 SHB)
             t3 (Z_to_bv 64 3) (Z_to_bv 64 line) t6)
        F (Z_to_bv 64 0x90940) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t0 t1 t3 s0 s1 a0 a1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s9 s10 t6 F fc m
    data n line w bs HK HJ HK1 HW DL L4 LN D0 D8 DHI DSH HB HBL ACC MI.
  { lia. }
  assert (STEP : forall (ra' a0' a1' t6' : word),
    evt asegs (gmax_rowend sp gp tp t0 t1 t3 s0 s1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s9 s10 F fc m data)
      (MS (mkR ra' sp gp tp t0 t1 (Z_to_bv 64 data) s0 s1 a0' a1' a2 a3 a4 a5 (Z_to_bv 64 1) a7 s2 s3 s4 s5
               (Z_to_bv 64 w) (Z_to_bv 64 (2 * j)) (Z_to_bv 64 j) s9 s10 (Z_to_bv 64 SHB)
               t3 (Z_to_bv 64 3) (Z_to_bv 64 line) t6')
          F (Z_to_bv 64 0x90930) fc None m (seg_rom asegs))).
  { intros. gwalk [0x90940; 0x909a8]. swrap_fix.
    replace (2 * j + 2) with (2 * (j + 1)) by lia.
    destruct k as [|k].
    - assert (EJ : j + 1 = w) by lia. rewrite EJ in *.
      brT. apply evt_done. unfold gmax_rowend. do 8 eexists. reflexivity.
    - brF. eapply (IH (j + 1)) with (bs := bs) (n := n) (w := w); try eassumption; try lia. }
  gwalk [0x9094c].
  rewrite (srliw_idx j 16) by lia.
  replace (line + j / 16 * 4) with (line + 4 * (j / 16)) by lia.
  gwalk (@nil Z).
  destruct (bytes_at_read4w m data bs (line + 4 * (j / 16) - data) HB ltac:(lia) ltac:(lia)) as (wv & R).
  replace (data + (line + 4 * (j / 16) - data)) with (line + 4 * (j / 16)) in R by lia.
  lstep. clear R.
  gwalk (@nil Z).
  brfork LT.
  - gwalk [0x90930]. apply STEP.
  - gwalk [0x90930]. apply STEP.
Qed.

(* [comment removed for export] *)
Definition gmax_exit (sp gp tp s0 s1 s2 s3 s4 s5 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s7' s8' t3' t4' t5' t6' : word),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6' s7' s8' s9 s10 (Z_to_bv 64 SHB) t3' t4' t5' t6')
             F (Z_to_bv 64 0x90a0c) fc None m (seg_rom asegs).

Lemma gmax_rows : forall (k : nat) (i : Z)
    (ra sp gp tp t0 t3 s0 s1 a0 a1 s2 s3 s6 s7 s8 s9 s10 t5 t6 : word) F fc (m : mem)
    (data wpl h w d wa : Z) (bs : list byte),
  Z.of_nat k = h - i -> 0 <= i -> (1 <= k)%nat ->
  (d = 2 \/ d = 4 \/ d = 8) -> 0 < w <= 2^20 -> (w * d + 31) / 32 <= wpl -> 0 < wpl <= 2^20 -> 0 < h <= 2^20 -> wpl * h <= 2^24 ->
  0 < data -> data mod 8 = 0 -> data + 4 * (wpl * h) <= 2^47 -> (data + 4 * (wpl * h) <= 0x7fff7000 \/ 0x10007fff8000 <= data) ->
  bytes_at asegs m data bs -> Z.of_nat (length bs) = 4 * (wpl * h) -> acc asegs m data (4 * (wpl * h)) ->
  rw_cells asegs m wa [C4 (Z_to_bv 64 w)] -> mem_inv asegs m ->
  evt asegs (gmax_exit sp gp tp s0 s1 s2 s3 (Z_to_bv 64 wa) (Z_to_bv 64 wpl) s9 s10 F fc m)
    (MS (mkR ra sp gp tp t0 (Z_to_bv 64 4) (Z_to_bv 64 data) s0 s1 a0 a1 (Z_to_bv 64 d) (Z_to_bv 64 h) (Z_to_bv 64 (i * wpl)) (Z_to_bv 64 i)
             (Z_to_bv 64 1) (Z_to_bv 64 2) s2 s3 (Z_to_bv 64 wa) (Z_to_bv 64 wpl) s6 s7 s8 s9 s10 (Z_to_bv 64 SHB)
             t3 (Z_to_bv 64 3) t5 t6)
        F (Z_to_bv 64 0x907d8) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra sp gp tp t0 t3 s0 s1 a0 a1 s2 s3 s6 s7 s8 s9 s10 t5 t6 F fc m data wpl h w d wa bs
    HK HI HK1 HD HW HWPL WPL HH WH D0 D8 DHI DSH HB HBL ACC WC MI.
  { lia. }
  assert (NL : i * wpl + wpl <= wpl * h) by nia.
  assert (NL0 : 0 <= i * wpl) by nia.
  assert (ROWEND : forall ms', gmax_rowend sp gp tp t0 (Z_to_bv 64 4) t3 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 h) (Z_to_bv 64 (i * wpl)) (Z_to_bv 64 i)
                                 (Z_to_bv 64 2) s2 s3 (Z_to_bv 64 wa) (Z_to_bv 64 wpl) s9 s10 F fc m data ms' ->
                       evt asegs (gmax_exit sp gp tp s0 s1 s2 s3 (Z_to_bv 64 wa) (Z_to_bv 64 wpl) s9 s10 F fc m) ms').
  { intros ms' (ra' & a0' & a1' & s6' & s7' & s8' & t5' & t6' & ->).
    gwalk (@nil Z).
    brfork MAXED.
    - apply evt_done. unfold gmax_exit. do 19 eexists. reflexivity.
    - gwalk [0x907d8; 0x90a0c]. swrap_fix.
      replace (i * wpl + wpl) with ((i + 1) * wpl) by lia.
      destruct k as [|k].
      + assert (EI : i + 1 = h) by lia. rewrite EI in *.
        brF. gwalk [0x90a0c]. apply evt_done. unfold gmax_exit. do 19 eexists. reflexivity.
      + brT. eapply (IH (i + 1)) with (bs := bs) (w := w); try eassumption; try lia. }
  gwalk [0x9080c].
  replace (data + (i * wpl + 0) mod 18446744073709551616 * 4) with (data + 4 * (i * wpl)) by (rewrite Z.mod_small by nia; lia).
  set (line := data + 4 * (i * wpl)) in *.
  assert (LR : data <= line /\ line mod 4 = 0 /\ line + 4 * wpl <= data + 4 * (wpl * h)) by (unfold line; repeat split; [lia| Z.div_mod_to_equations; lia| lia]).
  destruct LR as (L1 & L2 & L3).
  destruct HD as [-> | [-> | ->]].
  - (* [comment removed for export] *)
    gwalk [0x90940]. sx32_fix. gwalk [0x90940].
    eapply evt_cut; [| exact ROWEND].
    eapply (gmax2 (Z.to_nat w) 0) with (bs := bs) (n := 4 * (wpl * h)) (w := w); try eassumption; try lia.
  - (* [comment removed for export] *)
    gwalk [0x908b0]. sx32_fix. gwalk [0x908b0].
    eapply evt_cut; [| exact ROWEND].
    eapply (gmax4 (Z.to_nat w) 0) with (bs := bs) (n := 4 * (wpl * h)) (w := w); try eassumption; try lia.
  - (* [comment removed for export] *)
    gwalk [0x90844]. sx32_fix. gwalk [0x90844].
    replace (data + i * wpl * 4) with line by (unfold line; lia).
    eapply evt_cut; [| exact ROWEND].
    eapply (gmax8 (Z.to_nat w) 0) with (bs := bs) (n := 4 * (wpl * h)) (w := w) (line := line); try eassumption; try lia.
Qed.
