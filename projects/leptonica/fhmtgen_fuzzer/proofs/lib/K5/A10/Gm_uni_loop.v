(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Gm_ropkit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation PW_W datad ld := [(datad, datad + 4 * ld)]%Z (only parsing).

(* [comment removed for export] *)
Definition pw_mem (m m' : mem) (datad ld : Z) (ws' : list word) : Prop :=
  munch (PW_W datad ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ u32arr asegs m' datad ws' /\ Z.of_nat (length ws') = ld.

(* [comment removed for export] *)
Definition pw1s_exit (ra sp gp tp t0 t1 t2 s0 s1 a5 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mask : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (datad ld wpl : Z) : machine_state -> Prop :=
  fun ms' => exists (a0' c' p' t' u' : word) (m' : mem) (ws' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 (wpl * 4)) c' p' mask a5 t' u' s2 (Z_to_bv 64 SHB) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xa0b90) fc None m' (seg_rom asegs)
    /\ munch (PW_W datad ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ u32arr asegs m' datad ws' /\ Z.of_nat (length ws') = ld.
Lemma pw1s_rows : forall (k : nat) (q c : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mask : word) F fc (m : mem)
    (datad ld wpl : Z) (ws : list word),
    c = Z.of_nat k -> (1 <= k)%nat -> 0 < wpl <= 5001 -> 0 <= q -> q + (Z.of_nat k - 1) * wpl < ld -> ld <= 2^24 ->
    0 < datad -> datad mod 8 = 0 -> datad + 4 * ld <= 2^47 -> (datad + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
    (datad + 4 * ld <= 0x10000 \/ SEGTOP_A <= datad) ->
    u32arr asegs m datad ws -> Z.of_nat (length ws) = ld -> acc asegs m datad (4 * ld) -> mem_inv asegs m ->
  evt asegs (pw1s_exit ra sp gp tp t0 t1 t2 s0 s1 a5 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mask F fc m datad ld wpl)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (datad + 4 * q)) (Z_to_bv 64 (wpl * 4)) (Z_to_bv 64 c) (Z_to_bv 64 (datad + 4 * q)) mask a5 a6 a7
             s2 (Z_to_bv 64 SHB) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa0b50) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros q c ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mask F fc m
    datad ld wpl ws HC HK1 WPL Q0 QB LD D0 D8 DHI DSH DSEG UA UAL ACC MI.
  { lia. }
  unfold SEGTOP_A, SHB in *. subst c.
  assert (PQ : 0 <= Z.of_nat k * wpl) by (apply Z.mul_nonneg_nonneg; lia).
  pose proof (munch_refl (PW_W datad ld) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0xa0b60].
  destruct (u32arr_nth ws q ltac:(lia)) as (wv & NTH).
  pose proof (u32arr_read asegs m datad ws q wv _ UA NTH ltac:(lia) eq_refl) as R.
  lstep. clear R NTH.
  lwalk [0xa0b70].
  arr_sw datad q (datad + 4 * q).
  lwalk [0xa0b78].
  rewrite (bv_swrap_small 32 (Z.of_nat (S k) + -1)) by (change (bv_half_modulus 32) with (2^31); lia).
  replace (Z.of_nat (S k) + -1) with (Z.of_nat k) by lia.
  replace (datad + 4 * q + wpl * 4) with (datad + 4 * (q + wpl)) by lia.
  lstep.
  destruct k as [|k].
  - brF. lwalk [0xa0b90].
    apply evt_done. unfold pw1s_exit. do 5 eexists. exists m0, aws. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UA| exact UAL].
  - brT.
    eapply evt_cut.
    + eapply (IH (q + wpl)) with (ws := aws) (ld := ld); try eassumption; try reflexivity; try lia.
    + intros ms' PO. apply evt_done. unfold pw1s_exit in PO |- *.
      destruct PO as (x1 & x2 & x3 & x4 & x5 & m' & ws' & E & MU' & WM' & R).
      exists x1, x2, x3, x4, x5, m', ws'.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Definition pw1c_exit (ra sp gp tp t0 t1 t2 s0 s1 a5 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mask : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (datad ld wpl : Z) : machine_state -> Prop :=
  fun ms' => exists (a0' c' p' t' u' : word) (m' : mem) (ws' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' mask (Z_to_bv 64 (wpl * 4)) p' c' a5 t' u' s2 (Z_to_bv 64 SHB) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xa0e18) fc None m' (seg_rom asegs)
    /\ munch (PW_W datad ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ u32arr asegs m' datad ws' /\ Z.of_nat (length ws') = ld.
Lemma pw1c_rows : forall (k : nat) (q c : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mask : word) F fc (m : mem)
    (datad ld wpl : Z) (ws : list word),
    c = Z.of_nat k -> (1 <= k)%nat -> 0 < wpl <= 5001 -> 0 <= q -> q + (Z.of_nat k - 1) * wpl < ld -> ld <= 2^24 ->
    0 < datad -> datad mod 8 = 0 -> datad + 4 * ld <= 2^47 -> (datad + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
    (datad + 4 * ld <= 0x10000 \/ SEGTOP_A <= datad) ->
    u32arr asegs m datad ws -> Z.of_nat (length ws) = ld -> acc asegs m datad (4 * ld) -> mem_inv asegs m ->
  evt asegs (pw1c_exit ra sp gp tp t0 t1 t2 s0 s1 a5 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mask F fc m datad ld wpl)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (datad + 4 * q)) mask (Z_to_bv 64 (wpl * 4)) (Z_to_bv 64 (datad + 4 * q)) (Z_to_bv 64 c) a5 a6 a7
             s2 (Z_to_bv 64 SHB) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa0cf4) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros q c ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mask F fc m
    datad ld wpl ws HC HK1 WPL Q0 QB LD D0 D8 DHI DSH DSEG UA UAL ACC MI.
  { lia. }
  unfold SEGTOP_A, SHB in *. subst c.
  assert (PQ : 0 <= Z.of_nat k * wpl) by (apply Z.mul_nonneg_nonneg; lia).
  pose proof (munch_refl (PW_W datad ld) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0xa0d04].
  destruct (u32arr_nth ws q ltac:(lia)) as (wv & NTH).
  pose proof (u32arr_read asegs m datad ws q wv _ UA NTH ltac:(lia) eq_refl) as R.
  lstep. clear R NTH.
  lwalk [0xa0d14].
  arr_sw datad q (datad + 4 * q).
  lwalk [0xa0d1c].
  rewrite (bv_swrap_small 32 (Z.of_nat (S k) + -1)) by (change (bv_half_modulus 32) with (2^31); lia).
  replace (Z.of_nat (S k) + -1) with (Z.of_nat k) by lia.
  replace (datad + 4 * q + wpl * 4) with (datad + 4 * (q + wpl)) by lia.
  lstep.
  destruct k as [|k].
  - brF. lwalk [0xa0e18].
    apply evt_done. unfold pw1c_exit. do 5 eexists. exists m0, aws. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UA| exact UAL].
  - brT.
    eapply evt_cut.
    + eapply (IH (q + wpl)) with (ws := aws) (ld := ld); try eassumption; try reflexivity; try lia.
    + intros ms' PO. apply evt_done. unfold pw1c_exit in PO |- *.
      destruct PO as (x1 & x2 & x3 & x4 & x5 & m' & ws' & E & MU' & WM' & R).
      exists x1, x2, x3, x4, x5, m', ws'.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Definition pw3s_exit (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s7 s8 s9 s10 s11 t3 t4 t5 t6 mask : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (datad ld wpl : Z) : machine_state -> Prop :=
  fun ms' => exists (a0' c' p' t' u' : word) (m' : mem) (ws' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 (wpl * 4)) t' u' a4 a5 a6 a7 s2 (Z_to_bv 64 SHB) c' p' mask s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xa0e24) fc None m' (seg_rom asegs)
    /\ munch (PW_W datad ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ u32arr asegs m' datad ws' /\ Z.of_nat (length ws') = ld.
Lemma pw3s_rows : forall (k : nat) (q c : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mask : word) F fc (m : mem)
    (datad ld wpl : Z) (ws : list word),
    c = Z.of_nat k -> (1 <= k)%nat -> 0 < wpl <= 5001 -> 0 <= q -> q + (Z.of_nat k - 1) * wpl < ld -> ld <= 2^24 ->
    0 < datad -> datad mod 8 = 0 -> datad + 4 * ld <= 2^47 -> (datad + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
    (datad + 4 * ld <= 0x10000 \/ SEGTOP_A <= datad) ->
    u32arr asegs m datad ws -> Z.of_nat (length ws) = ld -> acc asegs m datad (4 * ld) -> mem_inv asegs m ->
  evt asegs (pw3s_exit ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s7 s8 s9 s10 s11 t3 t4 t5 t6 mask F fc m datad ld wpl)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (datad + 4 * q)) (Z_to_bv 64 (wpl * 4)) a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 SHB) (Z_to_bv 64 c) (Z_to_bv 64 (datad + 4 * q)) mask s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa0ba0) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros q c ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mask F fc m
    datad ld wpl ws HC HK1 WPL Q0 QB LD D0 D8 DHI DSH DSEG UA UAL ACC MI.
  { lia. }
  unfold SEGTOP_A, SHB in *. subst c.
  assert (PQ : 0 <= Z.of_nat k * wpl) by (apply Z.mul_nonneg_nonneg; lia).
  pose proof (munch_refl (PW_W datad ld) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0xa0bb0].
  destruct (u32arr_nth ws q ltac:(lia)) as (wv & NTH).
  pose proof (u32arr_read asegs m datad ws q wv _ UA NTH ltac:(lia) eq_refl) as R.
  lstep. clear R NTH.
  lwalk [0xa0bc0].
  arr_sw datad q (datad + 4 * q).
  lwalk [0xa0bc8].
  rewrite (bv_swrap_small 32 (Z.of_nat (S k) + -1)) by (change (bv_half_modulus 32) with (2^31); lia).
  replace (Z.of_nat (S k) + -1) with (Z.of_nat k) by lia.
  replace (datad + 4 * q + wpl * 4) with (datad + 4 * (q + wpl)) by lia.
  lstep.
  destruct k as [|k].
  - brF. lwalk [0xa0e24].
    apply evt_done. unfold pw3s_exit. do 5 eexists. exists m0, aws. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UA| exact UAL].
  - brT.
    eapply evt_cut.
    + eapply (IH (q + wpl)) with (ws := aws) (ld := ld); try eassumption; try reflexivity; try lia.
    + intros ms' PO. apply evt_done. unfold pw3s_exit in PO |- *.
      destruct PO as (x1 & x2 & x3 & x4 & x5 & m' & ws' & E & MU' & WM' & R).
      exists x1, x2, x3, x4, x5, m', ws'.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Definition pw3c_exit (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mask : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (datad ld wpl : Z) : machine_state -> Prop :=
  fun ms' => exists (a0' c' p' t' u' : word) (m' : mem) (ws' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' mask t' u' a4 a5 a6 a7 (Z_to_bv 64 (wpl * 4)) (Z_to_bv 64 SHB) c' p' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xa0e24) fc None m' (seg_rom asegs)
    /\ munch (PW_W datad ld) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ u32arr asegs m' datad ws' /\ Z.of_nat (length ws') = ld.
Lemma pw3c_rows : forall (k : nat) (q c : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mask : word) F fc (m : mem)
    (datad ld wpl : Z) (ws : list word),
    c = Z.of_nat k -> (1 <= k)%nat -> 0 < wpl <= 5001 -> 0 <= q -> q + (Z.of_nat k - 1) * wpl < ld -> ld <= 2^24 ->
    0 < datad -> datad mod 8 = 0 -> datad + 4 * ld <= 2^47 -> (datad + 4 * ld <= 0x7fff7000 \/ 0x10007fff8000 <= datad) ->
    (datad + 4 * ld <= 0x10000 \/ SEGTOP_A <= datad) ->
    u32arr asegs m datad ws -> Z.of_nat (length ws) = ld -> acc asegs m datad (4 * ld) -> mem_inv asegs m ->
  evt asegs (pw3c_exit ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mask F fc m datad ld wpl)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (datad + 4 * q)) mask a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (wpl * 4)) (Z_to_bv 64 SHB) (Z_to_bv 64 c) (Z_to_bv 64 (datad + 4 * q)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa1098) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros q c ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mask F fc m
    datad ld wpl ws HC HK1 WPL Q0 QB LD D0 D8 DHI DSH DSEG UA UAL ACC MI.
  { lia. }
  unfold SEGTOP_A, SHB in *. subst c.
  assert (PQ : 0 <= Z.of_nat k * wpl) by (apply Z.mul_nonneg_nonneg; lia).
  pose proof (munch_refl (PW_W datad ld) m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0xa10a8].
  destruct (u32arr_nth ws q ltac:(lia)) as (wv & NTH).
  pose proof (u32arr_read asegs m datad ws q wv _ UA NTH ltac:(lia) eq_refl) as R.
  lstep. clear R NTH.
  lwalk [0xa10b8].
  arr_sw datad q (datad + 4 * q).
  lwalk [0xa10c0].
  rewrite (bv_swrap_small 32 (Z.of_nat (S k) + -1)) by (change (bv_half_modulus 32) with (2^31); lia).
  replace (Z.of_nat (S k) + -1) with (Z.of_nat k) by lia.
  replace (datad + 4 * q + wpl * 4) with (datad + 4 * (q + wpl)) by lia.
  lstep.
  destruct k as [|k].
  - brF. lwalk [0xa0e24].
    apply evt_done. unfold pw3c_exit. do 5 eexists. exists m0, aws. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact UA| exact UAL].
  - brT.
    eapply evt_cut.
    + eapply (IH (q + wpl)) with (ws := aws) (ld := ld); try eassumption; try reflexivity; try lia.
    + intros ms' PO. apply evt_done. unfold pw3c_exit in PO |- *.
      destruct PO as (x1 & x2 & x3 & x4 & x5 & m' & ws' & E & MU' & WM' & R).
      exists x1, x2, x3, x4, x5, m', ws'.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.
