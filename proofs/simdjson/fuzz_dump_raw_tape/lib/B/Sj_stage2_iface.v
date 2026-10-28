(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjTape SjTapeInv SjTapeTile SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_iface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition S2A_ENTRY : Z := 0xb6bec.

Definition S2A_STACK : Z := 448 + NUMA_STACK.

Definition S2A_FRAMES : nat := S NUMA_FRAMES.

Definition S2A_COST (len : Z) : Z := 1 + NUMA_CREDIT * (len + 2) + mcost (len + 64).

Definition s2a_impl_cells (vptr : word) (n IDX : Z) (capv : word) (OC IA BUF len : Z) (nxt docv : word) (p12 p28 p50 : list byte) : list cell :=
  [C8 vptr; C4 (wz n); CB 4 p12; C8 (wz IDX); C4 nxt; CB 4 p28; C8 capv; C8 (wz 1024);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 p50; C8 (wz OC); C8 (wz IA); C8 (wz BUF); C8 (wz len); C8 docv].

Definition s2a_X (THIS TAPE SBUF OC IA tcap scap : Z) : list (Z * Z) :=
  [(THIS, THIS + 96); (TAPE, TAPE + 8 * tcap); (SBUF, SBUF + scap); (OC, OC + 8192); (IA, IA + 1024)].

Definition ivl_disj (a b : Z * Z) : Prop := fst a + snd a <= fst b \/ fst b + snd b <= fst a.
Fixpoint pairwise_disj (l : list (Z * Z)) : Prop :=
  match l with [] => True | x :: r => Forall (ivl_disj x) r /\ pairwise_disj r end.

Section S2Iface.
Variable RT : rt_sig.

Definition live_reg (Σ : rts RT) (X size : Z) : Prop :=
  exists p n, In (p, n) (rt_live RT Σ) /\ p mod 8 = 0 /\ p <= X /\ X + size <= p + n.

Definition stage2a_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z)
         (THIS DOC IDX BUF TAPE SBUF OC IA : Z) (bs idxs : list Z) (iws : list word) (tcap scap : Z)
         (vptr capv nxt docv dcap : word) (p12 p28 p50 : list byte),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0x6abde8 -> frm0 fc ->

  S1OUT bs idxs -> bytes_ok bs -> blen bs <= 1048512 ->
  firstn (length idxs + 3) iws = map (Z_to_bv 64) (idxs ++ [blen bs; blen bs; 0]) ->

  blen bs + 3 <= tcap -> tcap <= 2^40 -> 5 * blen bs + 5 <= 3 * scap -> scap <= 2^40 -> scap mod 8 = 0 ->
  blen bs + 4 <= Z.of_nat (length iws) -> Z.of_nat (length iws) < 2^40 ->

  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + S2A_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  (length (rt_frames RT Σ) + S2A_FRAMES <= FRAMES_MAX)%nat -> S2A_COST (blen bs) <= rt_credit RT Σ ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX ->

  live_reg Σ THIS 96 -> live_reg Σ IDX (4 * Z.of_nat (length iws)) -> live_reg Σ BUF (blen bs + 64) ->
  live_reg Σ TAPE (8 * tcap) -> live_reg Σ SBUF scap -> live_reg Σ OC 8192 -> live_reg Σ IA 1024 ->
  THIS mod 8 = 0 -> IDX mod 8 = 0 -> TAPE mod 8 = 0 -> SBUF mod 8 = 0 -> OC mod 8 = 0 -> IA mod 8 = 0 ->
  pairwise_disj [(THIS, 96); (IDX, 4 * Z.of_nat (length iws)); (BUF, blen bs + 64); (TAPE, 8 * tcap); (SBUF, scap); (OC, 8192); (IA, 1024)] ->
  fobj RT Σ m DOC 24 ->
  rw_cells bsegs m THIS (s2a_impl_cells vptr (Z.of_nat (length idxs)) IDX capv OC IA BUF (blen bs) nxt docv p12 p28 p50) ->
  rw_cells bsegs m DOC [C8 (wz TAPE); C8 (wz SBUF); C8 dcap] ->
  u32arr bsegs m IDX iws ->
  bytes_at bsegs m BUF (padded_bytes bs) ->
  (exists ocs, u32arr bsegs m OC ocs /\ length ocs = 2048%nat) ->
  (exists ias, u8arr bsegs m IA ias /\ length ias = 1024%nat) ->
  cps_f
    (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 (wz THIS) (wz DOC) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                 t3 t4 t5 t6 F fc S2A_ENTRY m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m' (v nxt' : word),
           ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ bv_unsigned v < 64
         /\ frm0 (ms_fcsr ms)
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (s2a_X THIS TAPE SBUF OC IA tcap scap) m m'
         /\ rw_cells bsegs m' THIS (s2a_impl_cells vptr (Z.of_nat (length idxs)) IDX capv OC IA BUF (blen bs) nxt' (wz DOC) p12 p28 p50)) c
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - S2A_COST (blen bs) <= rt_credit RT Σ').

Definition s2a_okres (TAPE SBUF tcap scap : Z) (a0 : word) (m' : mem) : Prop :=
  (1 <= bv_unsigned a0 < 64) \/
  (a0 = wz 0 /\ exists tws sbs : list Z,
     bytes_at bsegs m' TAPE (u64s (map (Z_to_bv 64) tws)) /\ bytes_at bsegs m' SBUF (map (Z_to_bv 8) sbs) /\
     tape_wfS (Tf tws) (Tf sbs) (Z.of_nat (length sbs)) ck_any (Z.of_nat (length tws)) /\
     Forall (fun c => 0 <= c < 256) sbs /\
     Z.of_nat (length tws) <= tcap /\ Z.of_nat (length sbs) <= scap).

Definition stage2at_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z)
         (THIS DOC IDX BUF TAPE SBUF OC IA : Z) (bs idxs : list Z) (iws : list word) (tcap scap : Z)
         (vptr capv nxt docv dcap : word) (p12 p28 p50 : list byte),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0x6abde8 -> frm0 fc ->

  S1OUT bs idxs -> bytes_ok bs -> blen bs <= 1048512 ->
  firstn (length idxs + 3) iws = map (Z_to_bv 64) (idxs ++ [blen bs; blen bs; 0]) ->

  blen bs + 3 <= tcap -> tcap <= 2^40 -> 5 * blen bs + 5 <= 3 * scap -> scap <= 2^40 -> scap mod 8 = 0 ->
  blen bs + 4 <= Z.of_nat (length iws) -> Z.of_nat (length iws) < 2^40 ->

  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + S2A_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  (length (rt_frames RT Σ) + S2A_FRAMES <= FRAMES_MAX)%nat -> S2A_COST (blen bs) <= rt_credit RT Σ ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX ->

  live_reg Σ THIS 96 -> live_reg Σ IDX (4 * Z.of_nat (length iws)) -> live_reg Σ BUF (blen bs + 64) ->
  live_reg Σ TAPE (8 * tcap) -> live_reg Σ SBUF scap -> live_reg Σ OC 8192 -> live_reg Σ IA 1024 ->
  THIS mod 8 = 0 -> IDX mod 8 = 0 -> TAPE mod 8 = 0 -> SBUF mod 8 = 0 -> OC mod 8 = 0 -> IA mod 8 = 0 ->
  pairwise_disj [(THIS, 96); (IDX, 4 * Z.of_nat (length iws)); (BUF, blen bs + 64); (TAPE, 8 * tcap); (SBUF, scap); (OC, 8192); (IA, 1024)] ->
  fobj RT Σ m DOC 24 ->
  rw_cells bsegs m THIS (s2a_impl_cells vptr (Z.of_nat (length idxs)) IDX capv OC IA BUF (blen bs) nxt docv p12 p28 p50) ->
  rw_cells bsegs m DOC [C8 (wz TAPE); C8 (wz SBUF); C8 dcap] ->
  u32arr bsegs m IDX iws ->
  bytes_at bsegs m BUF (padded_bytes bs) ->
  (exists ocs, u32arr bsegs m OC ocs /\ length ocs = 2048%nat) ->
  (exists ias, u8arr bsegs m IA ias /\ length ias = 1024%nat) ->
  cps_f
    (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 (wz THIS) (wz DOC) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                 t3 t4 t5 t6 F fc S2A_ENTRY m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m' (v nxt' : word),
           ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ bv_unsigned v < 64
         /\ s2a_okres TAPE SBUF tcap scap v m'
         /\ frm0 (ms_fcsr ms)
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (s2a_X THIS TAPE SBUF OC IA tcap scap) m m'
         /\ rw_cells bsegs m' THIS (s2a_impl_cells vptr (Z.of_nat (length idxs)) IDX capv OC IA BUF (blen bs) nxt' (wz DOC) p12 p28 p50)) c
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - S2A_COST (blen bs) <= rt_credit RT Σ').

Lemma stage2a_of_stage2at : stage2at_cps -> stage2a_cps.
Proof.
  unfold stage2at_cps, stage2a_cps. intros H. intros.
  eapply cps_conseq; [eapply H; eassumption | intros c Hc; exact Hc |].
  cbv beta. intros c [(Σ' & HA & REST) CF]. split; [| exact CF]. exists Σ'. split; [| exact REST].
  eapply AST_conseq; [exact HA | | intros mo HM; exact HM].
  cbv beta. intros ms (m' & v & nxt' & Q1 & Q2 & _ & Q3). exists m', v, nxt'. exact (conj Q1 (conj Q2 Q3)).
Qed.

End S2Iface.

