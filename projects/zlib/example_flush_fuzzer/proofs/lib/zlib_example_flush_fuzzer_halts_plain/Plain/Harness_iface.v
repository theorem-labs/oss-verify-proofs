(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP CTree.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import ExFlushIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Plain Require Import PImg StdioFiles F_syscalls Stdio_iface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Plain Require Export Stdio_iface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Plain Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Spec Require Import Prelim Malloc Monad CMonad Stdio HarnessC Prog ProgC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Plain Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.
Definition PFUZZ_ENTRY : Z := 0x1612c.
Definition PEMPTY : Z := 0x3a660.
Definition HDATA : Z := 0x3a680.
Definition HDATA_N : Z := 16.
Definition PRELRO_LO : Z := 0x29000.
Definition PRELRO_HI : Z := 0x293d8.

Definition HARNESS_STACK : Z := 16384.

Definition harness_cells (m : mem) : Prop :=
  forall a, PRELRO_LO <= a < PRELRO_HI -> m (Z_to_bv 64 a) = None.

Definition stderr_file0 (m : mem) : Prop :=
  rw_cells psegs m RSTDERR (file_cells (Z_to_bv 64 5) 0 0 0 F_STDIO_WRITE RSTDERR_BUF 0 2 (wz 0) 0xffffffff (repeat (Z_to_bv 8 0) 80)).

Lemma stderr_file0_wfile0 : forall m, stderr_file0 m -> stderr_wfile0 m.
Proof.
  intros m H. exists (Z_to_bv 64 5), (wz 0), 0, 0, (repeat (Z_to_bv 8 0) 80). split; [exact H|].
  split; [rewrite unsigned_lit by lia; reflexivity|]. split; [left; reflexivity| lia].
Qed.

Definition hown_addr (a : Z) : Prop := (HDATA <= a < HDATA + HDATA_N) \/ (RSTDERR <= a < RSTDERR + 232).

Definition harness_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> ~ hown_addr a ->
    m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None).


Lemma harness_pres_trans : forall LB SP m1 m2 m3, harness_pres LB SP m1 m2 -> harness_pres LB SP m2 m3 -> harness_pres LB SP m1 m3.
Proof.
  intros LB SP m1 m2 m3 H1 H2 a Ha Hc Hx. destruct (H1 a Ha Hc Hx) as [E1 W1]. destruct (H2 a Ha Hc Hx) as [E2 W2].
  split; [congruence| auto].
Qed.

Lemma harness_pres_of_heap : forall LB SP m m', rheap_pres LB SP m m' -> harness_pres LB SP m m'.
Proof. intros LB SP m m' H a Ha Hc _. apply H; assumption. Qed.

Lemma harness_pres_weaken : forall LB LB' SP SP' m m',
  harness_pres LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> harness_pres LB' SP' m m'.
Proof.
  intros LB LB' SP SP' m m' H HS HL a Ha Hc Hx. apply H; [exact Ha| | exact Hx].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

Lemma harness_pres_bytes_at : forall LB SP m m' A bs,
  harness_pres LB SP m m' -> bytes_at psegs m A bs -> rclient_range LB SP A (Z.of_nat (length bs)) ->
  (forall a, A <= a < A + Z.of_nat (length bs) -> ~ hown_addr a) ->
  bytes_at psegs m' A bs.
Proof.
  intros LB SP m m' A bs HP (H0 & H1 & HB) HR HX. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia]) ltac:(apply HX; lia)) as [E _].
  rewrite E. reflexivity.
Qed.

Lemma harness_pres_wr_at : forall LB SP m m' A n,
  harness_pres LB SP m m' -> wr_at psegs m A n -> rclient_range LB SP A n -> (forall a, A <= a < A + n -> ~ hown_addr a) -> wr_at psegs m' A n.
Proof.
  intros LB SP m m' A n HP (H0 & H1 & HW) HR HX. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia]) ltac:(apply HX; lia)) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

Lemma harness_pres_rw_cells : forall LB SP m m' A cs,
  harness_pres LB SP m m' -> rw_cells psegs m A cs -> rclient_range LB SP A (Z.of_nat (cells_size cs)) ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ hown_addr a) ->
  rw_cells psegs m' A cs.
Proof.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HR HX. split; [split; [exact Hwf|]|].
  - eapply harness_pres_bytes_at; eauto; rewrite cells_bytes_length by assumption; assumption.
  - eapply harness_pres_wr_at; eauto.
Qed.


Section FuzzOne.
  Variable FM : flush_model.

  Definition leak_ok (LK : list block) : Prop :=
    (length LK <= 2)%nat /\ Forall (fun b => blk_size b = ISTATE_N \/ blk_size b = WIN_N) LK.

  Definition fuzz_one_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (s : PState) (LB : list block) (AB lo : Z) (m : mem)
      (r : Z) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (errv' : word) (LK : list block),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom psegs)
      /\ -2^31 <= r < 2^31
      /\ mem_inv psegs m' /\ frm0 fc'
      /\ stk psegs m' lo (bv_unsigned sp)
      /\ rw_cells psegs m' (errno_addr tp) [C4 errv']
      /\ rauxv_ok m' AB
      /\ harness_pres LB (bv_unsigned sp) m m'
      /\ RHEAP s' (LK ++ LB) m' /\ leak_ok LK
      /\ harness_cells m' /\ stderr_wfile0 m'
      /\ ps_so s' = ps_so s.

  Definition fuzz_one_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem)
           (s : PState) (LB : list block) (D : Z) (payload : list Z) (AB lo : Z) (errv : word),
      RHEAP s LB m ->
      bytes_at psegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload ->
      wr_at psegs m D (zlength payload) ->
      rclient_range LB (bv_unsigned sp) D (zlength payload) ->
      D mod 16 = 0 -> 0 < D -> D + zlength payload <= ATOP -> zlength payload < 2^26 ->
      harness_cells m -> stderr_wfile0 m ->
      rauxv_ok m AB -> bv_unsigned sp <= AB ->
      stk psegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - HARNESS_STACK ->
      rw_cells psegs m (errno_addr tp) [C4 errv] ->
      mem_inv psegs m -> frm0 fc ->
      tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
      a0 = wz D -> a1 = wz (zlength payload) ->
      bv_unsigned ra mod 2 = 0 ->
      bv_unsigned sp <= 2^47 ->
      ((zlength payload = 0 /\ D = PEMPTY) \/ exists b, In b LB /\ blk_addr b <= D /\ D + zlength payload <= blk_addr b + blk_size b) ->
      implMC psegs (ProgC.fuzz_oneC FM payload) s
            (fuzz_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (wz PFUZZ_ENTRY) fc None m (seg_rom psegs)).
End FuzzOne.
End CANSEC1.
