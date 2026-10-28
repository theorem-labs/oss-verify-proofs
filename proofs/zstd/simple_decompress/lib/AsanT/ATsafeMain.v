(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import BackingAlgebra MainExport MainFactsAsan MainEntryAsan.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad STree Stdio Harness Adapter Driver ProgA
  AsanCtrl AsanCtrlProps SizeHist AsanEmbed AsanProgDeps AsanInv AsanTotal AsanOK RSimProg AsanHandoff Prog.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ATsafeCore ATsafeEv ATsafeAlloc ATsafeOps ATsafeProg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition VMAX : Z := MAIN_COST.
(* [comment removed for export] *)
Definition K0 : Z := 600959 + (2^22 + 2) + (2^8 + 2).
Definition NMAXZ : Z := K0 + VMAX / 1024.
Definition NMAX : nat := Z.to_nat NMAXZ.

Lemma NMAX_Z : Z.of_nat NMAX = NMAXZ.
Proof. unfold NMAX. apply Z2Nat.id. vm_compute. discriminate. Qed.

(* [comment removed for export] *)
Definition ash_pages (V : nat -> Z) : list word :=
  range_pages (shad (a_space_beg0 V)) (shlen K_SPACE_SIZE) ++ range_pages (shad (a_ptr_array0 V)) (shlen K_PTRARR_RESERVE).

(* [comment removed for export] *)
Definition Ahand (V : nat -> Z) : alw := fun p => bv_unsigned p mod 4096 = 0 /\ aallowed (allow_of ASHOFF V both_vis) p.

Definition A0 (V : nat -> Z) : alw := aunion (Ahand V) (ash_pages V).

Theorem A0_init : forall V (p : word), bv_unsigned p mod 4096 = 0 -> aallowed (allow_of ASHOFF V both_vis) p -> A0 V p.
Proof. intros V p Hal Ha. left. split; assumption. Qed.

(* [comment removed for export] *)
Theorem A0_ash : forall V (p : word), bv_unsigned p mod 4096 = 0 ->
  shad (a_space_beg0 V) <= bv_unsigned p < shad (a_space_beg0 V) + 17179869184 -> 0 <= shad (a_space_beg0 V) -> A0 V p.
Proof.
  intros V p Hal Hp Hs. right. unfold ash_pages. apply in_app_iff. left.
  rewrite <- (ATsafeAlloc.page_base_of_self 0%nat p Hal). apply range_pages_spec; [exact Hs|].
  replace (shlen K_SPACE_SIZE) with 17179869184 by reflexivity. exact Hp.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma HLIM : NLK0 + Z.of_nat NMAX * 4096 <= LIMIT.
Proof. rewrite NMAX_Z. vm_compute. discriminate. Qed.

Lemma shlen_vals : shlen K_SPACE_SIZE = 2^34 /\ shlen K_PTRARR_RESERVE = 2^20.
Proof. split; reflexivity. Qed.

Section V.
  Variable V : nat -> Z.
  Hypothesis HP : Forall (pfact_ok V) both_pure_facts.
  (* [comment removed for export] *)
  Hypothesis HAT : a_usp0 V - 8388608 = ATOP.
  Local Notation SB := (a_space_beg0 V).
  Local Notation PA := (a_ptr_array0 V).

  Lemma HSB : 0 <= SB /\ SB + K_SPACE_SIZE <= ATOP.
  Proof. pose proof (placement_facts V HP) as (H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold a_space_beg0, K_SPACE_SIZE, PRIM_SZ, a_usp0 in *. lia. Qed.

  Lemma HPA : 0 <= PA /\ PA + K_PTRARR_RESERVE <= ATOP.
  Proof. pose proof (placement_facts V HP) as (H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold a_ptr_array0, K_PTRARR_RESERVE, PTR_SZ, a_usp0 in *. lia. Qed.

  Lemma SB_al : SB mod 4096 = 0.
  Proof. pose proof (space_beg0_facts V HP) as (H1 & _). apply (Z.mod_divide _ 65536) in H1; [|lia]. destruct H1 as [q Hq]. rewrite Hq.
         replace (q * 65536) with ((q * 16) * 4096) by lia. apply Z.mod_mul. lia. Qed.

  Lemma PA_al : PA mod 4096 = 0.
  Proof. pose proof (space_beg0_facts V HP) as (_ & _ & H & _). exact H. Qed.

  Lemma ABASE_SH : forall z',
    (shad SB <= z' < shad (SB + K_SPACE_SIZE) \/ shad PA <= z' < shad (PA + K_PTRARR_RESERVE)) -> A0 V (page_base_of z').
  Proof.
    intros z' Hz. right. unfold ash_pages. apply in_or_app.
    pose proof HSB as [S1 S2]. pose proof HPA as [P1 P2].
    pose proof (shad_bounds 0%nat SB ltac:(unfold K_SPACE_SIZE in *; lia)) as SH1.
    pose proof (shad_bounds 0%nat PA ltac:(unfold K_PTRARR_RESERVE in *; lia)) as SH2.
    destruct Hz as [Hz|Hz]; [left|right]; apply range_pages_spec; try lia.
    - rewrite (shad8 0%nat SB K_SPACE_SIZE SB_al) in Hz. lia.
    - rewrite (shad8 0%nat PA K_PTRARR_RESERVE PA_al) in Hz. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma A0_abud : forall sp fs mo, bmodel V sp fs mo -> abud (A0 V) K0.
  Proof.
    intros sp fs mo HM. unfold A0, K0.
    pose proof HSB as [S1 S2]. pose proof HPA as [P1 P2]. pose proof shlen_vals as [E1 E2].
    pose proof (shad_bounds 0%nat SB ltac:(unfold K_SPACE_SIZE in *; lia)) as SH1.
    pose proof (shad_bounds 0%nat PA ltac:(unfold K_PTRARR_RESERVE in *; lia)) as SH2.
    assert (HL : Z.of_nat (length (ash_pages V)) <= (2^22 + 2) + (2^8 + 2)).
    { unfold ash_pages. rewrite length_app, Nat2Z.inj_add.
      pose proof (range_pages_length (shad SB) (shlen K_SPACE_SIZE) ltac:(lia) ltac:(rewrite E1; lia)).
      pose proof (range_pages_length (shad PA) (shlen K_PTRARR_RESERVE) ltac:(lia) ltac:(rewrite E2; lia)).
      rewrite E1, E2 in *. change (2^34 / 4096) with (2^22) in *. change (2^20 / 4096) with (2^8) in *. lia. }
    apply (abud_mono _ (600959 + Z.of_nat (length (ash_pages V)))); [apply abud_union| lia].
    destruct (aallowed_fin (allow_of ASHOFF V both_vis) (bm_allow_wf _ _ _ _ HM)) as (L & ND & HLL & HIN).
    exists L. split; [exact ND|]. split; [| intros p [Hal Ha]; apply HIN; assumption].
    pose proof (bm_abytes _ _ _ _ HM) as AB. unfold both_abytes in AB. change MainEntryAsan.ASHOFF with ASHOFF in AB.
    pose proof (Z.div_le_mono _ _ 4096 ltac:(lia) AB) as AB'. change (2460940288 / 4096) with 600815 in AB'. lia.   (* [comment removed for export] *)
  Qed.
End V.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Main.
  Variable V : nat -> Z.
  Hypothesis HP : Forall (pfact_ok V) both_pure_facts.
  Hypothesis HAT : a_usp0 V - 8388608 = ATOP.
  Variable sp : word.                          (* [comment removed for export] *)
  Hypothesis HSP : atop_of sp = ATOP.
  Local Notation SB := (a_space_beg0 V).
  Local Notation PA := (a_ptr_array0 V).

  (* [comment removed for export] *)
  Definition J : list (AsanCtrl.aptr * Z) -> Z -> preT (St:=APS) := JJ NMAX SB PA (A0 V).

  Lemma J_acct : forall Y v RNG A s mo, J Y v RNG A s mo -> acct_ok NMAX RNG A mo.
  Proof. exact (JJ_acct NMAX SB PA (A0 V) HLIM). Qed.
  Lemma J_perm : forall Y Y' v RNG A s mo, Permutation Y Y' -> J Y v RNG A s mo -> J Y' v RNG A s mo.
  Proof. exact (JJ_perm NMAX SB PA (A0 V)). Qed.
  Lemma J_credit : forall Y v v' RNG A s mo, 0 <= v' <= v -> J Y v RNG A s mo -> J Y v' RNG A s mo.
  Proof. exact (JJ_credit NMAX SB PA (A0 V)). Qed.
  Lemma J_nonneg : forall Y v RNG A s mo, J Y v RNG A s mo -> 0 <= v.
  Proof. intros Y v RNG A s mo (_ & _ & _ & _ & _ & Hv & _). exact Hv. Qed.
  Lemma J_io : forall n Y v RNG A s mo rsp mo' evs, io_node n -> nstep n mo rsp mo' evs -> J Y v RNG A s mo -> J Y v RNG A s mo'.
  Proof. exact (JJ_io NMAX SB PA (A0 V) (HSB V HP HAT) (HPA V HP HAT)). Qed.
  Lemma J_so : forall Y v RNG A s mo w, J Y v RNG A s mo -> J Y v RNG A (aset_so w s) mo.
  Proof. exact (JJ_so NMAX SB PA (A0 V)). Qed.

  Local Notation TSM := (TSM NMAX (St:=APS)).

  Lemma Jm : forall Y v n, 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) ->
    TSM (fun RNG A s mo => J Y v RNG A s mo /\ n <= v) (amalloc_M n)
        (fun r RNG A s mo => exists q, r = Some q /\ J ((q, n) :: Y) (v - n) RNG A s mo /\ n < 2^63).
  Proof. exact (U_malloc NMAX SB PA (A0 V) HLIM (ABASE_SH V HP HAT)). Qed.
  Lemma Jf : forall Y v p n, TSM (J ((p, n) :: Y) v) (afree_M p) (fun _ => J Y v).
  Proof. exact (U_free NMAX SB PA (A0 V) HLIM (ABASE_SH V HP HAT)). Qed.
  Lemma Ja : forall Y v q cap old new, In (q, cap) Y -> 0 <= old <= cap -> 0 <= new <= cap -> (old = 0 \/ new = 0) ->
    TSM (J Y v) (aannot_M q cap old new) (fun _ => J Y v).
  Proof. exact (U_annot NMAX SB PA (A0 V) HLIM (ABASE_SH V HP HAT)). Qed.

  Ltac jx := first [ exact J_acct | exact J_perm | exact J_credit | exact J_nonneg | exact J_io | exact J_so | exact Jm | exact Jf ].

  Lemma Jnh : forall Y v (Q : postM (St:=APS) Empty_set), TSM (J Y v) (new_handlerA AAllocAsan) Q.
  Proof. intros Y v Q. unfold new_handlerA. apply TSM_munr. apply J_acct. Qed.

  Lemma Jemit : forall Y v z, TSJ NMAX J Y v (io_emit (ioA AAllocAsan) z).
  Proof. intros Y v z. cbn [io_emit ioA io_S]. eapply s_emit_ok; jx. Qed.

  (* [comment removed for export] *)

  Lemma Jrun : forall X cfg payload v, (length X <= 1)%nat -> zlength payload <= MAX_INPUT -> RUN_COST <= v ->
    TSM (J X v) (runA AAllocAsan cfg payload) (fun _ => J X (v - RUN_COST)).
  Proof.
    intros X cfg payload v HX Hp Hv. unfold runA, fuzz_oneA. cbn [amalloc afree AAllocAsan].
    eapply target_run_ok; try jx; first [apply Jnh| apply Jemit| exact HX| exact Hp| exact Hv].
  Qed.

  Lemma Jdiag : forall Y v d, TSJ NMAX J Y v (io_diag (ioA AAllocAsan) d).
  Proof. intros. cbn [io_diag ioA io_S]. eapply s_diag_ok; jx. Qed.
  Lemma Jioexit : forall Y v, TSJ NMAX J Y v (io_exit (ioA AAllocAsan)).
  Proof. intros. cbn [io_exit ioA io_S]. eapply stdout_exit_flush_ok; jx. Qed.
  Lemma Jinit : forall Y v bm, TSJ NMAX J Y v (alloc_initA AAllocAsan bm).
  Proof. intros. unfold alloc_initA, target_alloc_init. eapply TSJ_ret; jx. Qed.
  Lemma Jcount : forall Y v, TSJ NMAX J Y v (alloc_countA AAllocAsan).
  Proof. intros. unfold alloc_countA, target_alloc_count. eapply TSJ_ret; jx. Qed.

  (* [comment removed for export] *)
  Lemma progA_main_ok : forall rs argv v (Q : postM (St:=APS) Empty_set), MAIN_COST <= v ->
    TSM (J [] v) (progA_main AAllocAsan rs argv) Q.
  Proof.
    intros rs argv v Q Hv. unfold progA_main. cbn [amalloc afree aptr_addr AAllocAsan].
    eapply main_exit_ok; try jx; first [apply Jdiag| apply Jinit| apply Jcount| apply Jrun| apply Jioexit| exact Hv].
  Qed.

  (* [comment removed for export] *)
  Lemma J_init : forall fs mo, bmodel V sp fs mo ->
    J [] VMAX (fp_ok (m_vm_lazy (MX mo [])) (A0 V)) (A0 V) (aps_init SB PA (resv_of V) (atop_of sp)) (MX mo []).
  Proof.
    intros fs mo HM. destruct (AI_init V sp fs mo HM HP) as (HAI & _).
    unfold J, JJ. split; [exact HAI|]. split; [exact HSP|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [unfold VMAX, MAIN_COST, READ_COST, RUN_COST, FUZZ_COST, PRODUCER_SIZE, DCTX_SIZE, BUFF_MAX, MAX_INPUT; lia|].
    exists [], K0. split; [unfold QOK; cbn [aps_m aps_init]; rewrite all_chunks_ainit; constructor|].
    split; [apply alw_le_refl|]. split; [apply GA_nil|]. split; [eapply A0_abud; [exact HP| exact HAT| exact HM]|].
    split; [unfold K0; lia|]. rewrite NMAX_Z. unfold NMAXZ. lia.
  Qed.

  Theorem progA_tsafe : forall rs inp mo, bmodel V sp (in_fs inp) mo ->
    tsafeA nstepA (nsafeA NMAX) fstepS NMAX (fp_ok (m_vm_lazy (MX mo [])) (A0 V)) (A0 V)
           (progA_tree AAllocAsan (aps_init SB PA (resv_of V) (atop_of sp)) rs (argv_Z (in_argv inp))) (MX mo []).
  Proof.
    intros rs inp mo HM.
    apply (TS_tsafeA NMAX _ _ _ _ (EQ (fun (_ : unit) _ _ _ => True))).
    unfold progA_tree. eapply TS_ebind.
    - exact (progA_main_ok rs (argv_Z (in_argv inp)) VMAX (fun _ _ _ _ _ => True) ltac:(unfold VMAX; lia) _ _ _ _ (J_init _ _ HM)).
    - intros [[] s] RNG' A' mo' _ _.
  Qed.
End Main.

(* [comment removed for export] *)
Corollary progA_tsafe_open : forall rs V sp inp mo,
  Forall (pfact_ok V) both_pure_facts -> a_usp0 V - 8388608 = ATOP -> atop_of sp = ATOP -> bmodel V sp (in_fs inp) mo ->
  tsafeA nstepA (nsafeA NMAX) fstepS NMAX (fp_ok (m_vm_lazy (MX mo [])) (A0 V)) (A0 V)
         (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rs (argv_Z (in_argv inp))) (MX mo []).
Proof. intros rs V sp inp mo HP HAT HSP HM. exact (progA_tsafe V HP HAT sp HSP rs inp mo HM). Qed.
End CANSEC1.
