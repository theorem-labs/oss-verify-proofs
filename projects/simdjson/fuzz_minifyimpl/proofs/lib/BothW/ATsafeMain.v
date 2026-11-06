(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import BackingAlgebra MainExport MainFactsBoth MainEntryBoth.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree Stdio Adapter Driver ProgA
  AsanCtrl AsanCtrlProps SizeHist AsanEmbed AsanProgDeps AsanInv AsanTotal AsanNodeSem AsanOK RSim RSimProg AsanHandoffBoth Prog.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg AProto ATsafeCore ATsafeEv ATsafeAlloc ATsafeOps ATsafeProg ATsafeClient.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition RUNC : Z := RUN_COST COSTF FUZZ_COST PAYMAX.
Definition VMAX : Z := MAIN_COST COSTM COSTF RUNC.
(* [comment removed for export] *)
Definition mf0 : Z -> Z := fun _ => 0.
Definition CBM0 : Z := CBM mf0.
(* [comment removed for export] *)
Definition NLK : Z := EAGER0 + CBM0 + CHMAX + VMAX / 8 + 1.
(* [comment removed for export] *)
Definition K0 : Z := both_abytes / 4096 + 1 + 124.
Definition NMAXZ : Z := K0 + (cpot CBM0 + VMAX) / 4096 + 1.
Definition NMAX : nat := Z.to_nat NMAXZ.

(* [comment removed for export] *)
Lemma COSTF_nonneg : 0 <= COSTF. Proof. vm_compute. discriminate. Qed.
Lemma FUZZ_COST_nonneg : 0 <= FUZZ_COST. Proof. vm_compute. discriminate. Qed.
Lemma RUNC_nonneg : 0 <= RUNC. Proof. vm_compute. discriminate. Qed.
Lemma VMAX_nonneg : 0 <= VMAX. Proof. vm_compute. discriminate. Qed.
Lemma CBM0_nonneg : 0 <= CBM0. Proof. vm_compute. discriminate. Qed.
Lemma K0_nonneg : 0 <= K0. Proof. vm_compute. discriminate. Qed.
Lemma NMAXZ_nonneg : 0 <= NMAXZ. Proof. vm_compute. discriminate. Qed.
Lemma NMAX_Z : Z.of_nat NMAX = NMAXZ.
Proof. unfold NMAX. apply Z2Nat.id. exact NMAXZ_nonneg. Qed.

(* [comment removed for export] *)
Lemma HLIM : NLK + Z.of_nat NMAX * 4096 <= LIMIT.
Proof. rewrite NMAX_Z. vm_compute. discriminate. Qed.
Lemma HNLK : 0 <= NLK.
Proof. vm_compute. discriminate. Qed.

(* [comment removed for export] *)
Definition win0 (V : nat -> Z) : list word :=
  flat_map (fun c : nat => range_pages (shad (a_space_beg0 V + Z.of_nat c * K_REGION) - 4096) 8192) (seq 1 31).

(* [comment removed for export] *)
Definition Ahand (V : nat -> Z) : alw := fun p => bv_unsigned p mod 4096 = 0 /\ aallowed (allow_of ASHOFF V both_vis) p.

Definition A0 (V : nat -> Z) : alw := aunion (Ahand V) (win0 V).

Theorem A0_init : forall V (p : word), bv_unsigned p mod 4096 = 0 -> aallowed (allow_of ASHOFF V both_vis) p -> A0 V p.
Proof. intros V p Hal Ha. left. split; assumption. Qed.

Lemma shad_ge : forall a, 0 <= a -> 2147450880 <= shad a.
Proof. intros a Ha. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.div_pos a (2^3) Ha ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Theorem A0_win0 : forall V (c : Z) (p : word), 1 <= c < K_NUM_CLASSES -> 0 <= a_space_beg0 V -> bv_unsigned p mod 4096 = 0 ->
  shad (a_space_beg0 V + c * K_REGION) - 4096 <= bv_unsigned p < shad (a_space_beg0 V + c * K_REGION) + 4096 -> A0 V p.
Proof.
  intros V c p Hc HSB0 Hal Hp. right. unfold win0. apply in_flat_map. exists (Z.to_nat c).
  split; [apply in_seq; unfold K_NUM_CLASSES in Hc; lia|]. rewrite Z2Nat.id by lia.
  rewrite <- (ATsafeAlloc.page_base_of_self 0%nat p Hal). apply range_pages_spec; [| lia].
  pose proof (shad_ge (a_space_beg0 V + c * K_REGION) ltac:(unfold K_REGION; lia)). lia.
Qed.

Lemma win0_length : forall V, 0 <= a_space_beg0 V -> Z.of_nat (length (win0 V)) <= 124.
Proof.
  intros V HSB0. unfold win0.
  assert (G : forall l, Forall (fun c : nat => (1 <= c)%nat) l ->
    Z.of_nat (length (flat_map (fun c : nat => range_pages (shad (a_space_beg0 V + Z.of_nat c * K_REGION) - 4096) 8192) l)) <= 4 * Z.of_nat (length l)).
  { induction l as [|c l IH]; intros HF; [cbn; lia|]. inversion HF; subst. cbn [flat_map]. rewrite length_app, Nat2Z.inj_add.
    pose proof (shad_ge (a_space_beg0 V + Z.of_nat c * K_REGION) ltac:(unfold K_REGION; lia)).
    pose proof (range_pages_length (shad (a_space_beg0 V + Z.of_nat c * K_REGION) - 4096) 8192 ltac:(lia) ltac:(lia)).
    change (8192 / 4096) with 2 in *. specialize (IH ltac:(assumption)). cbn [length]. lia. }
  etransitivity; [apply G|]; [| rewrite length_seq; lia].
  apply Forall_forall. intros c Hc. apply in_seq in Hc. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

  (* [comment removed for export] *)
  Lemma A0_abud : forall L sp fs mo, bmodelL L V sp fs mo -> abud (A0 V) K0.
  Proof.
    intros L sp fs mo HM. unfold A0, K0.
    pose proof HSB as [S1 S2]. pose proof (win0_length V S1) as HL.
    apply (abud_mono _ ((both_abytes / 4096 + 1) + Z.of_nat (length (win0 V)))); [apply abud_union| lia].
    destruct (aallowed_fin (allow_of ASHOFF V both_vis) (bm_allow_wf _ _ _ _ HM)) as (LL & ND & HLL & HIN).
    exists LL. split; [exact ND|]. split; [| intros p [Hal Ha]; apply HIN; assumption].
    pose proof (bm_abytes _ _ _ _ HM) as AB. change MainEntryBoth.ASHOFF with ASHOFF in AB.
    pose proof (Z.div_le_mono _ _ 4096 ltac:(lia) AB). lia.
  Qed.
End V.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Main.
  (* [comment removed for export] *)
  Variable L : Z.
  Hypothesis HL : LIMIT <= L.
  Variable V : nat -> Z.
  Hypothesis HP : Forall (pfact_ok V) both_pure_facts.
  Hypothesis HAT : a_usp0 V - 8388608 = ATOP.
  Variable sp : word.                          (* [comment removed for export] *)
  Hypothesis HSP : atop_of sp = ATOP.
  Local Notation SB := (a_space_beg0 V).
  Local Notation PA := (a_ptr_array0 V).

  (* [comment removed for export] *)
  Definition J : list (AsanCtrl.aptr * Z) -> Z -> preT (St:=APS) := JC NMAX SB PA (A0 V) NLK.

  Lemma J_acct : forall Y v RNG A s mo, J Y v RNG A s mo -> acct_ok NMAX RNG A mo.
  Proof. exact (JC_acct NMAX SB PA (A0 V) NLK HLIM). Qed.
  Lemma J_perm : forall Y Y' v RNG A s mo, Permutation Y Y' -> J Y v RNG A s mo -> J Y' v RNG A s mo.
  Proof. exact (JC_perm NMAX SB PA (A0 V) NLK). Qed.
  Lemma J_credit : forall Y v v' RNG A s mo, 0 <= v' <= v -> J Y v RNG A s mo -> J Y v' RNG A s mo.
  Proof. exact (JC_credit NMAX SB PA (A0 V) NLK). Qed.
  Lemma J_nonneg : forall Y v RNG A s mo, J Y v RNG A s mo -> 0 <= v.
  Proof. exact (JC_nonneg NMAX SB PA (A0 V) NLK). Qed.
  Lemma J_io : forall n Y v RNG A s mo rsp mo' evs, io_node n -> nstep n mo rsp mo' evs -> J Y v RNG A s mo -> J Y v RNG A s mo'.
  Proof. exact (JC_io NMAX SB PA (A0 V) NLK (HSB V HP HAT) (HPA V HP HAT)). Qed.
  Lemma J_so : forall Y v RNG A s mo w, J Y v RNG A s mo -> J Y v RNG A (aset_so w s) mo.
  Proof. exact (JC_so NMAX SB PA (A0 V) NLK). Qed.

  Local Notation TSM := (TSM NMAX (St:=APS)).

  Lemma Jm : forall Y v n, 0 <= n <= REQMAX -> (length Y <= 2)%nat -> HISTOK (n :: map snd Y) ->
    TSM (fun RNG A s mo => J Y v RNG A s mo /\ COSTM n <= v) (amalloc_M n)
        (fun r RNG A s mo => exists q, r = Some q /\ J ((q, n) :: Y) (v - COSTM n) RNG A s mo /\ n < 2^63).
  Proof. exact (UC_malloc NMAX SB PA (A0 V) NLK HLIM). Qed.
  Lemma Jf : forall Y v p n, TSM (fun RNG A s mo => J ((p, n) :: Y) v RNG A s mo /\ COSTF <= v) (afree_M p) (fun _ => J Y (v - COSTF)).
  Proof. exact (UC_free NMAX SB PA (A0 V) NLK HLIM). Qed.

  Ltac jx := first [ exact J_acct | exact J_perm | exact J_credit | exact J_nonneg | exact J_io | exact J_so | exact Jm | exact Jf ].

  Lemma Jemit : forall Y v z, TSJ NMAX J Y v (io_emit (ioA AAllocAsan) z).
  Proof. intros Y v z. cbn [io_emit ioA io_S]. eapply s_emit_ok; jx. Qed.

  Lemma Jfuzz : forall X v data, (length X <= 2)%nat -> zlength data <= MAX_INPUT -> FUZZ_COST <= v ->
    TSM (J X v) (fuzz_oneA AAllocAsan data) (fun _ => J X (v - FUZZ_COST)).
  Proof. exact (UC_fuzz NMAX SB PA (A0 V) NLK HLIM). Qed.

  Lemma Jrun : forall X cfg payload v, (length X <= 1)%nat -> zlength payload <= MAX_INPUT -> RUNC <= v ->
    TSM (J X v) (runA AAllocAsan cfg payload) (fun _ => J X (v - RUNC)).
  Proof.
    intros X cfg payload v HX Hp Hv. unfold runA. cbn [amalloc afree AAllocAsan].
    exact (@target_run_ok APS NMAX AsanCtrl.aptr J J_acct J_credit J_nonneg COSTM COSTF COSTM_nonneg COSTF_nonneg
             amalloc_M afree_M (io_emit (ioA AAllocAsan)) (fuzz_oneA AAllocAsan) Jm Jf Jemit FUZZ_COST PAYMAX FUZZ_COST_nonneg PAYMAX_ok Jfuzz
             X cfg payload v HX Hp Hv).
  Qed.

  Lemma Jclexit : forall Y v, TSM (J Y v) (client_exitA AAllocAsan) (fun _ RNG A s mo => exists X' v', J X' v' RNG A s mo).
  Proof.
    intros Y v. eapply TSM_post; [apply (UC_cexit NMAX SB PA (A0 V) NLK HLIM)|].
    intros [] RNG A s mo _ H. exists Y, v. exact H.
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
  Lemma progA_main_ok : forall rs argv v (Q : postM (St:=APS) Empty_set), VMAX <= v ->
    TSM (J [] v) (progA_main AAllocAsan rs argv) Q.
  Proof.
    intros rs argv v Q Hv. unfold progA_main. cbn [amalloc afree aptr_addr AAllocAsan].
    exact (@main_exit_ok APS NMAX AsanCtrl.aptr J J_acct J_perm J_credit J_io COSTM COSTF COSTM_nonneg COSTF_nonneg
             (ioA AAllocAsan) amalloc_M afree_M rs (alloc_initA AAllocAsan) (runA AAllocAsan) (alloc_countA AAllocAsan)
             Jm Jf Jdiag Jinit Jcount RUNC RUNC_nonneg Jrun Jioexit (client_exitA AAllocAsan) Jclexit argv v Q Hv).
  Qed.

  (* [comment removed for export] *)
  Lemma J_init : forall fs mo, bmodelL L V sp fs mo ->
    J [] VMAX (fp_ok (m_vm_lazy (MX mo [])) (A0 V)) (A0 V) (aps_init SB PA (resv_of V) (atop_of sp)) (MX mo []).
  Proof.
    intros fs mo HM. destruct (AI_initL L HL V sp fs mo HM HP) as (HAI & _).
    unfold J. apply (JC_init NMAX SB PA (A0 V) NLK); [reflexivity| exact VMAX_nonneg|].      (* [comment removed for export] *)
    unfold JJ. cbn [aps_init aps_m aps_atop]. split; [exact HAI|]. split; [exact HSP|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact VMAX_nonneg|].
    exists [], K0, mf0. split; [unfold QOK; cbn [aps_m aps_init]; rewrite all_chunks_ainit; constructor|].
    split; [apply alw_le_refl|]. split; [apply GA_nil|]. split; [eapply A0_abud; [exact HP| exact HAT| exact HM]|].
    split; [exact K0_nonneg|].
    split.
    { (* [comment removed for export] *)
      intros c Hc. unfold mf0. rewrite all_chunks_ainit, get_cls_ainit. change (qbatches [] (ainit SB PA)) with (@nil abatch).
      rewrite cntP_nil. unfold nbatch. change (zlen (@nil abatch)) with 0.
      pose proof (SLK_nonneg c Hc). pose proof (size_of_class_pos c Hc). cbn [c_allocated_user aclass0].
      split; [lia|]. split; [destruct (c =? K_BATCH_CLASS); lia| nia]. }
    split.
    { fold CBM0. unfold NLK. pose proof (Z.div_mod VMAX 8 ltac:(lia)). pose proof (Z.mod_pos_bound VMAX 8 ltac:(lia)). lia. }
    unfold PHI. cbn [aps_m aps_init]. rewrite commit_bytes_ainit, Z.sub_0_r. fold CBM0.
    rewrite NMAX_Z. unfold NMAXZ. pose proof (Z.div_mod (cpot CBM0 + VMAX) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (cpot CBM0 + VMAX) 4096 ltac:(lia)).
    lia.
  Qed.

  (* [comment removed for export] *)
  Theorem progA_TS : forall rs inp mo, bmodelL L V sp (in_fs inp) mo ->
    TS NMAX (fp_ok (m_vm_lazy (MX mo [])) (A0 V)) (A0 V)
       (progA_tree AAllocAsan (aps_init SB PA (resv_of V) (atop_of sp)) rs (argv_Z (in_argv inp))) (MX mo []) (EQ (fun (_ : unit) _ _ _ => True)).
  Proof.
    intros rs inp mo HM.
    unfold progA_tree. eapply TS_ebind.
    - exact (progA_main_ok rs (argv_Z (in_argv inp)) VMAX (fun _ _ _ _ _ => True) ltac:(lia) _ _ _ _ (J_init _ _ HM)).
    - intros [[] s] RNG' A' mo' _ _.
  Qed.

  Theorem progA_tsafe : forall rs inp mo, bmodelL L V sp (in_fs inp) mo ->
    tsafeA nstepA (nsafeA NMAX) fstepS NMAX (fp_ok (m_vm_lazy (MX mo [])) (A0 V)) (A0 V)
           (progA_tree AAllocAsan (aps_init SB PA (resv_of V) (atop_of sp)) rs (argv_Z (in_argv inp))) (MX mo []).
  Proof. intros rs inp mo HM. exact (TS_tsafeA NMAX _ _ _ _ _ (progA_TS rs inp mo HM)). Qed.

  (* [comment removed for export] *)
  Theorem progA_tglob : forall rs inp mo, bmodelL L V sp (in_fs inp) mo ->
    tglob nstepA PhiB (progA_tree AAllocAsan (aps_init SB PA (resv_of V) (atop_of sp)) rs (argv_Z (in_argv inp))) (MX mo []).
  Proof. intros rs inp mo HM. exact (TS_tglob NMAX _ _ _ _ _ (progA_TS rs inp mo HM)). Qed.
End Main.

(* [comment removed for export] *)
Corollary progA_tsafe_openL : forall L, LIMIT <= L -> forall rs V sp inp mo,
  Forall (pfact_ok V) both_pure_facts -> a_usp0 V - 8388608 = ATOP -> atop_of sp = ATOP -> bmodelL L V sp (in_fs inp) mo ->
  tsafeA nstepA (nsafeA NMAX) fstepS NMAX (fp_ok (m_vm_lazy (MX mo [])) (A0 V)) (A0 V)
         (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rs (argv_Z (in_argv inp))) (MX mo [])
  /\ tglob nstepA PhiB (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rs (argv_Z (in_argv inp))) (MX mo []).
Proof.
  intros L HL rs V sp inp mo HP HAT HSP HM.
  exact (conj (progA_tsafe L HL V HP HAT sp HSP rs inp mo HM) (progA_tglob L HL V HP HAT sp HSP rs inp mo HM)).
Qed.

(* [comment removed for export] *)
Corollary progA_tsafe_open : forall rs V sp inp mo,
  Forall (pfact_ok V) both_pure_facts -> a_usp0 V - 8388608 = ATOP -> atop_of sp = ATOP -> bmodel V sp (in_fs inp) mo ->
  tsafeA nstepA (nsafeA NMAX) fstepS NMAX (fp_ok (m_vm_lazy (MX mo [])) (A0 V)) (A0 V)
         (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rs (argv_Z (in_argv inp))) (MX mo [])
  /\ tglob nstepA PhiB (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rs (argv_Z (in_argv inp))) (MX mo []).
Proof. exact (progA_tsafe_openL target_alloc_limit LIMIT_le_target). Qed.
End CANSEC1.
