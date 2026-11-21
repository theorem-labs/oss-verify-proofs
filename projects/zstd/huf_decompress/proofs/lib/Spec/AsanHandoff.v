(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the main entry's pure facts as kept (APKN) and its computed total (ATOTSZ); AMI_init_L reads amodelL's channel-reader fact, its reserved ledger with the vDSO pair and the mappings' clearance from it, and proves AMI's new fact that the mappings miss the reserved ledger (new lemmas region_free_of_disj, fold_uns2_sizes, live_bytes_app_sizes); 28 recorded proofs replaced by written proofs (ivs_sep_seps, live_bytes_ivs_sum, ivs_sum_app and 25 more); AHAND_init and AHAND_init_L state this unit's main-phase budget (AIW at MAIN_OPS); minv_fds3 takes the channel-reader conjunct, discharged in AI_init_L from amodelL's reader field; AMI_init_L also proves this unit's noacc_clear; ported by content from zstd_frame_info's file of the same role, with this binary's addresses and names). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem ITree Nodes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import AcctCore ModelX NodesA.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import BackingAlgebra MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Stdio AsanCtrl AsanCtrlProps SizeHist AsanProgDeps
  AsanInv AsanBudget AsanOK RSim RSimProg Prog ProgA EquivPA.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ITreeA.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition a_space_beg0 (V : nat -> Z) : Z := 4096 * V 208%nat - 4096 * V 209%nat + 65536.
Definition a_ptr_array0 (V : nat -> Z) : Z := 4096 * V 226%nat.
(* [comment removed for export] *)
Definition atop_of (sp : word) : Z := bv_unsigned sp - 8388608.
(* [comment removed for export] *)
Definition a_usp0 (V : nat -> Z) : Z := 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ivs_sep_seps : forall l, ivs_sep l -> seps l.
Proof.
  induction l as [|p l IH]; intros H; [constructor|]. constructor.
  - apply Forall_forall. intros q Hq. apply In_nth_error in Hq as [j Hj].
    destruct (H 0%nat (Datatypes.S j) p q ltac:(lia) eq_refl Hj) as [A|B]; unfold wsep; [left; exact A| right; exact B].
  - apply IH. intros i j p' q' Hij Hi Hj. apply (H (Datatypes.S i) (Datatypes.S j) p' q'); [lia| exact Hi| exact Hj].
Qed.

Lemma live_bytes_ivs_sum : forall l, live_bytes l = ivs_sum l.
Proof. induction l as [|[a n] l IH]; [reflexivity|]. cbn [ivs_sum snd]. rewrite <- IH. reflexivity. Qed.

Lemma ivs_sum_app : forall l1 l2, ivs_sum (l1 ++ l2) = ivs_sum l1 + ivs_sum l2.
Proof. induction l1 as [|e l1 IH]; intros; cbn [ivs_sum app]; [lia|]. rewrite IH. lia. Qed.

Lemma ivs_sum_nonneg : forall l, 0 <= ivs_sum l.
Proof. induction l as [|e l IH]; cbn [ivs_sum]; [lia|]. pose proof (bv_unsigned_in_range _ (snd e)). lia. Qed.

Lemma ledger_den_In : forall V l maps, ledger_den V l maps ->
  forall b n k, In (LMap b n k) l -> In (wa (zv V b), wa n) maps.
Proof.
  induction l as [|[b n k|n] l IH]; intros maps HD b' n' k' Hin; cbn [ledger_den] in HD.
  - contradiction.
  - destruct HD as (maps' & -> & HD'). destruct Hin as [E|Hin].
    + injection E as -> -> ->. left. reflexivity.
    + right. eapply IH; eauto.
  - destruct Hin as [E|Hin]; [discriminate|].
    destruct HD as [HD'|(iv & maps' & -> & _ & HD')]; [eapply IH; eauto| right; eapply IH; eauto].
Qed.

Lemma ledger_den_length : forall V l maps, ledger_den V l maps -> (length maps <= length l)%nat.
Proof.
  induction l as [|[b n k|n] l IH]; intros maps HD; cbn [ledger_den] in HD.
  - subst maps. cbn. lia.
  - destruct HD as (maps' & -> & HD'). cbn. pose proof (IH _ HD'). lia.
  - destruct HD as [HD'|(iv & maps' & -> & _ & HD')]; cbn; pose proof (IH _ HD'); lia.
Qed.

(* [comment removed for export] *)
Lemma pfact_In : forall V f, Forall (pfact_ok V) APKN -> In f APKN -> pfact_ok V f.
Proof. intros V f H Hin. rewrite Forall_forall in H. apply H, Hin. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma live_chunks_ainit : forall sb pa, live_chunks (ainit sb pa) = [].
Proof. intros. unfold live_chunks, ainit. cbn [a_live]. rewrite map_to_list_empty. reflexivity. Qed.

Lemma get_cls_ainit : forall sb pa c, get_cls (ainit sb pa) c = aclass0.
Proof. intros. unfold get_cls, ainit. cbn [a_cls]. rewrite lookup_empty. reflexivity. Qed.

Lemma all_chunks_ainit : forall sb pa, all_chunks [] [] (ainit sb pa) = [].
Proof. intros. unfold all_chunks. rewrite live_chunks_ainit. reflexivity. Qed.

Lemma CH_ainit : forall sb pa, CH [] [] (ainit sb pa) = [].
Proof. intros. unfold CH. rewrite all_chunks_ainit. reflexivity. Qed.

Lemma commit_bytes_ainit : forall sb pa, commit_bytes (ainit sb pa) = 0.
Proof. intros. reflexivity. Qed.

Lemma AINV_init : forall ATOP sb pa, sb mod 65536 = 0 -> 0 < sb -> pa mod 4096 = 0 -> 0 < pa -> AINV ATOP [] [] (ainit sb pa).
Proof.
  intros ATOP sb pa H1 H2 H3 H4. unfold AINV.
  rewrite all_chunks_ainit, CH_ainit. change (qbatches [] (ainit sb pa)) with (@nil abatch).
  split.
  { intros c Hc. unfold cls_inv. rewrite get_cls_ainit, all_chunks_ainit. change (qbatches [] (ainit sb pa)) with (@nil abatch).
    unfold max_count, ainit. cbn [a_cinit c_allocated_user c_mapped_user c_mapped_free_array c_num_freed c_count aclass0 cntP zlen List.filter length Z.of_nat].
    unfold nbatch. unfold K_FREEARR_OFF, K_USER_MAP, K_FREEARR_MAX, K_FREEARR_MAP. cbn [zlen length Z.of_nat].
    destruct (c =? K_BATCH_CLASS); rewrite Z.mul_0_r; repeat split; cbn; try lia; reflexivity. }
  split; [constructor|]. split; [constructor|].
  unfold ainit. cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array bsum zlen length Z.of_nat].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [left; reflexivity|].
  split; [intros id ch Hl; rewrite lookup_empty in Hl; discriminate|].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  change (live_budget (ainit sb pa)). unfold live_budget. rewrite live_chunks_ainit. unfold AsanInv.cntP, AsanInv.zlen. cbn [secs secbytes flat_map List.filter length Z.of_nat].
  split; [| split; [unfold SMAX, HB; cbn; lia| unfold LSBYTES, HB; lia]].
  intros c Hc. rewrite Z.mul_0_r. unfold LMAX, HB. destruct (c =? 1); [lia|]. destruct (c =? 2); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition pfact_eqb (f g : pfact) : bool :=
  match f, g with
  | PVar n lo hi, PVar n' lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
  | PRange e lo hi, PRange e' lo' hi' => zexp_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | PDisj a1 n1 a2 n2, PDisj a1' n1' a2' n2' => zexp_eqb a1 a1' && Z.eqb n1 n1' && zexp_eqb a2 a2' && Z.eqb n2 n2'
  | PDisjS a1 n1 a2 n2, PDisjS a1' n1' a2' n2' => zexp_eqb a1 a1' && zexp_eqb n1 n1' && zexp_eqb a2 a2' && zexp_eqb n2 n2'
  | _, _ => false
  end.

Lemma pfact_eqb_eq : forall f g, pfact_eqb f g = true -> f = g.
Proof.
  intros [n lo hi|e lo hi|a1 n1 a2 n2|a1 n1 a2 n2] [n' lo' hi'|e' lo' hi'|a1' n1' a2' n2'|a1' n1' a2' n2'] H; cbn in H; try discriminate.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst. reflexivity.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply zexp_eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst. reflexivity.
  - apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply zexp_eqb_eq in H1. apply Z.eqb_eq in H2. apply zexp_eqb_eq in H3. apply Z.eqb_eq in H4. subst. reflexivity.
  - apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply zexp_eqb_eq in H1. apply zexp_eqb_eq in H2. apply zexp_eqb_eq in H3. apply zexp_eqb_eq in H4. subst. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pfact_find : forall V f, Forall (pfact_ok V) APKN -> existsb (pfact_eqb f) APKN = true -> pfact_ok V f.
Proof.
  intros V f HF HE. apply existsb_exists in HE as (g & Hin & Hg). apply pfact_eqb_eq in Hg. subst g.
  exact (proj1 (Forall_forall _ _) HF f Hin).
Qed.

Definition uns2 (p : word * word) : Z * Z := (bv_unsigned (fst p), bv_unsigned (snd p)).
Lemma reserved_eval : map uns2 (segments_reserved asegs) = [(65536, 131072); (196608, 520192); (716800, 8192); (724992, 5619712)].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition resv_entries (V : nat -> Z) : list (word * word) :=
  flat_map (fun e => match e with LMap b n _ => [(wa (zv V b), wa n)] | LFog _ => [] end) asan_ledger
  ++ segments_reserved asegs.
Definition iv_of (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (fst e) + bv_unsigned (snd e)).
Definition resv_of (V : nat -> Z) : list (Z * Z) := map iv_of (resv_entries V).
Lemma live_bytes_uns2 : forall l, live_bytes l = fold_right (fun q acc => snd q + acc) 0 (map uns2 l).
Proof. induction l as [|[a n] l IH]; [reflexivity|]. cbn [map fold_right uns2 fst snd]. rewrite <- IH. reflexivity. Qed.
Lemma Forall_uns2 : forall (P : Z * Z -> Prop) l, Forall P (map uns2 l) -> Forall (fun e => P (uns2 e)) l.
Proof. induction l as [|e l IH]; intros H; [constructor|]. cbn [map] in H. apply Forall_cons_iff in H as [H1 H2]. constructor; auto. Qed.
Lemma reserved_facts :
  Forall (fun e => bv_unsigned (fst e) + bv_unsigned (snd e) <= RES_HI) (segments_reserved asegs)
  /\ zlen (segments_reserved asegs) <= LEN0 /\ live_bytes (segments_reserved asegs) <= RTOT0
  /\ Forall (fun e => 65536 <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= 6344704) (segments_reserved asegs).
Proof.
  pose proof reserved_eval as E. split; [|split; [|split]].
  - apply (Forall_uns2 (fun q => fst q + snd q <= RES_HI)). rewrite E. unfold RES_HI. repeat constructor; cbn; lia.
  - unfold AsanInv.zlen. rewrite <- (length_map uns2), E. unfold LEN0. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  - rewrite live_bytes_uns2, E. unfold RTOT0. cbn -[Z.le Z.pow]. lia.
  - apply (Forall_uns2 (fun q => 65536 <= fst q /\ fst q + snd q <= 6344704)). rewrite E. repeat constructor; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma region_free_of_hull : forall l (g G : Z), 0 <= g -> 0 <= G -> g + G < 2^64 ->
  Forall (fun e => 65536 <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= 6344704) l ->
  (g + G <= 65536 \/ 6344704 <= g) ->
  region_free l (Z_to_bv 64 g) (Z_to_bv 64 G) = true.
Proof.
  induction l as [|[a sz] l IH]; intros g G Hg HG Hhi HF HD; [reflexivity|].
  apply Forall_cons_iff in HF as [H1 HF]. cbn [fst snd] in H1.
  cbn [region_free]. rewrite (IH g G Hg HG Hhi HF HD), andb_true_r.
  unfold iv_overlap. rewrite !unsigned_lit by lia.
  apply negb_true_iff. apply andb_false_iff.
  destruct HD as [HD|HD]; [right| left]; apply Z.ltb_ge; lia.
Qed.

(* [comment removed for export] *)
Lemma placement_facts : forall V, Forall (pfact_ok V) APKN ->
  4295491576 <= V 208%nat <= 34326181871 /\ 0 <= V 209%nat <= 15 /\ 1549 <= V 226%nat <= 34359734272
  /\ (4096 * V 208%nat) mod 65536 = 4096 * V 209%nat
  /\ (0 <= V 6%nat <= 255 /\ 0 <= V 10%nat <= 7 /\ 4294901760 <= V 0%nat <= 4294967295)
  /\ 4096 * V 208%nat + PRIM_SZ <= 32768 * V 0%nat + 4096 * V 10%nat - 8388608
  /\ 4096 * V 226%nat + PTR_SZ <= 32768 * V 0%nat + 4096 * V 10%nat - 8388608.
Proof.
  intros V HP.
  pose proof (pfact_find V (PVar 208 4295491576 34326181871) HP ltac:(vm_compute; reflexivity)) as H1; cbn in H1.
  pose proof (pfact_find V (PVar 209 0 15) HP ltac:(vm_compute; reflexivity)) as H2; cbn in H2.
  pose proof (pfact_find V (PVar 226 1549 34359734272) HP ltac:(vm_compute; reflexivity)) as H3; cbn in H3.
  pose proof (pfact_find V (PRange (ZAdd (ZMul (ZLit (-4096)) (ZV 209)) (ZAnd (ZMul (ZLit 4096) (ZV 208)) (ZLit 65535))) 0 0) HP
                ltac:(vm_compute; reflexivity)) as H4.
  cbn -[Z.mul Z.add Z.land Z.modulo Z.le] in H4.
  pose proof (pfact_find V (PVar 6 0 255) HP ltac:(vm_compute; reflexivity)) as H6; cbn in H6.
  pose proof (pfact_find V (PVar 10 0 7) HP ltac:(vm_compute; reflexivity)) as H10; cbn in H10.
  pose proof (pfact_find V (PVar 0 4294901760 4294967295) HP ltac:(vm_compute; reflexivity)) as H0; cbn in H0.
  pose proof (pfact_find V (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) HP
                ltac:(vm_compute; reflexivity)) as D1. cbn -[Z.mul Z.add Z.le] in D1.
  pose proof (pfact_find V (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) HP
                ltac:(vm_compute; reflexivity)) as D2. cbn -[Z.mul Z.add Z.le] in D2.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split.
  { change 65535 with (Z.ones 16) in H4.
rewrite Z.land_ones in H4 by lia. change (2^16) with 65536 in H4.
    pose proof (Z.mod_pos_bound (4096 * V 208%nat) 65536 ltac:(lia)) as B.
    set (u := (4096 * V 208%nat) mod 65536) in *.
    assert (Hv : (-4096 * V 209%nat + u) mod two64 = 0) by lia.
    apply Z.mod_divide in Hv; [| unfold two64; lia]. destruct Hv as [k Hk]. unfold two64 in Hk. lia. }
  split; [lia|]. unfold PRIM_SZ, PTR_SZ. lia.
Qed.

Lemma ivs_wf_of_bounds : forall l K, K <= 2^64 ->
  Forall (fun iv : word * word => bv_unsigned (fst iv) + bv_unsigned (snd iv) <= K) l -> ivs_wf l.
Proof. intros l K HK H q Hq. rewrite Forall_forall in H. unfold iv_wf, B, BackingAlgebra.S. pose proof (H q Hq). lia. Qed.
(* LPS 727298f3: a mapping disjoint from every reserved entry misses the reserved ledger *)
Lemma region_free_of_disj : forall R (a n : word),
  Forall (fun q : word * word => bv_unsigned a + bv_unsigned n <= bv_unsigned (fst q)
                                 \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned a) R ->
  region_free R a n = true.
Proof.
  induction R as [|[b s] R IH]; intros a n H; [reflexivity|].
  apply Forall_cons_iff in H as [H0 H]. cbn [fst snd] in H0.
  cbn [region_free]. rewrite (IH a n H), andb_true_r.
  unfold iv_overlap. apply negb_true_iff. apply andb_false_iff.
  destruct H0 as [H0|H0]; first [left; apply Z.ltb_ge; lia | right; apply Z.ltb_ge; lia].
Qed.
(* LPS 727298f3: the bytes of a reserved ledger that ends with the vDSO pair *)
Lemma fold_uns2_sizes : forall l, fold_right (fun q acc => snd q + acc) 0 (map uns2 l) = AsanPlanSound.APS.sum_sizes l.
Proof. induction l as [|[a s] l IH]; [reflexivity|]. cbn [map fold_right uns2 fst snd AsanPlanSound.APS.sum_sizes]. rewrite IH. reflexivity. Qed.
Lemma live_bytes_app_sizes : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + AsanPlanSound.APS.sum_sizes l2.
Proof.
  intros l1 l2. rewrite !live_bytes_uns2, <- fold_uns2_sizes, map_app, fold_right_app.
  generalize (fold_right (fun q acc => snd q + acc) 0 (map uns2 l2)) as c. generalize (map uns2 l1) as m.
  induction m as [|q m IH]; intros c; cbn [fold_right]; [lia| rewrite IH; lia].
Qed.

(* [comment removed for export] *)
Lemma AMI_init_L : forall lim V sp fs mo, LIMIT34 <= lim ->
  amodelL lim V sp fs mo -> Forall (pfact_ok V) APKN ->
  AMI (resv_of V) (atop_of sp) [] (ainit (a_space_beg0 V) (a_ptr_array0 V)) (MX mo []).
Proof.
  intros lim V sp fs mo HLIM HM HP. destruct (placement_facts V HP) as (F208 & F209 & F226 & FR & _ & _ & _).
  destruct HM as [Hh Hrdr Hfds Hfs Hres Hlim Hbrk Hsbrk Htop Husp Hmaps Hkinds Hsep Hbnd Hlzb Hnawf Hnasub Hnapos Htot Hnl Hab Hbud Halw Hnd Hmat Hmres].   (* [comment removed for export] *)
  (* LPS 727298f3: the reserved ledger is the image's and the vDSO pair ([amL_reserved], AsanPlanSound.co_res) *)
  destruct Hres as (rx & Hres & Hrx & Hrxn & Hrxb).
  unfold AMI. rewrite m_vm_materialized_MX, m_vmmaps_MX, m_vm_lazy_MX. change (Pm (MX mo [])) with (Pm mo).
  destruct reserved_facts as (R1 & R2 & R3 & R4).
  set (ATOP := atop_of sp). assert (EA : ATOP = bv_unsigned sp - 8388608) by reflexivity. clearbody ATOP.
  assert (W1 : ivs_wf (vm_maps (m_vmmaps mo))).
  {
apply (ivs_wf_of_bounds _ ATOP ltac:(lia)). eapply Forall_impl; [|exact Hbnd]. cbv beta. intros iv (_ & _ & _ & _ & _ & H). lia. }
  assert (W2 : ivs_wf (vm_noaccess (m_vmmaps mo))) by (apply (ivs_wf_of_bounds _ (2^64) ltac:(lia)); exact Hnawf).
  assert (W3 : ivs_wf (m_vm_lazy mo)).
  { apply (ivs_wf_of_bounds _ ATOP ltac:(lia)). eapply Forall_impl; [|exact Hlzb]. cbv beta. intros iv [_ H]. lia. }
  (* [comment removed for export] *)
  assert (END : forall b n, In (b, n) (vm_maps (m_vmmaps mo)) -> bv_unsigned b + bv_unsigned n <= ATOP
                             /\ (bv_unsigned b + bv_unsigned n <= 65536 \/ 6344704 <= bv_unsigned b)).
  { intros b n Hin. rewrite Forall_forall in Hbnd. destruct (Hbnd _ Hin) as (_ & _ & _ & _ & A5 & A6). cbn [fst snd] in A5, A6.
    unfold MainEntry.AIMG_LO, MainEntry.AIMG_HI in A5. lia. }
  (* LPS 727298f3: AMI's new fact: the mappings miss the reserved ledger, the vDSO pair included ([amL_mres]) *)
  assert (NEWC : forall e, In e (vm_maps (m_vmmaps mo)) -> region_free (vm_reserved (m_vmmaps mo)) (fst e) (snd e) = true).
  { intros [b n] Hin. cbn [fst snd]. apply region_free_of_disj. rewrite Forall_forall in Hmres. exact (Hmres _ Hin). }
  split; [reflexivity|].
  split; [rewrite Hlim; exact HLIM|].   (* [comment removed for export] *)
  split; [exact NEWC|].
  rewrite Hres. split.
  { (* the image's four entries and at most n_resx entries for the vDSO pair *)
    unfold AsanInv.zlen in *. rewrite length_app, Nat2Z.inj_add.
    pose proof (f_equal (@length _) reserved_eval) as LE. rewrite length_map in LE. cbn [length] in LE. rewrite LE.
    assert (NR : (AsanPlan.AP.n_resx AsanPlan.AP.ASAN <= 28)%nat) by (vm_compute; lia).
    unfold LEN0. lia. }
  split.
  { (* the image's reserved bytes and the vDSO pair's, at most resx_bytes *)
    rewrite live_bytes_app_sizes, live_bytes_uns2, reserved_eval. cbn [fold_right fst snd].
    assert (RB : AsanPlan.AP.resx_bytes AsanPlan.AP.ASAN <= 2^29) by (vm_compute; discriminate).
    unfold RTOT0. lia. }
  split. { eapply Forall_impl; [|exact Hbnd]. cbv beta. intros iv (A1 & A2 & A3 & A4 & A5 & A6). unfold entry_ok. repeat split; try assumption. lia. }
  split; [exact W2|]. split; [exact W3|]. split; [apply ivs_sep_seps; exact Hsep|].
  split. { split; [unfold atop_ok, ACEIL, AsanInv.ATOP_MAX; lia|]. unfold alloc_top, stack_max_size. rewrite Htop. lia. }
  split.
  { unfold noacc_clear.
    assert (KO : forall b n, In (LMap (ZLit b) n AsanPlan.AP.KRWLAZY) asan_ledger -> forall iv x, In iv (vm_noaccess (m_vmmaps mo)) ->
                 b <= x < b + n -> 0 <= x < 2^64 -> ~ (bv_unsigned (fst iv) <= x < bv_unsigned (fst iv) + bv_unsigned (snd iv))).
    { intros b n Hin iv x Hiv Hx Hr Hc. rewrite Forall_forall in Hkinds. pose proof (Hkinds _ Hin) as K. cbn [lentry_kind_ok zv] in K.
      assert (U : bv_unsigned (wa x) = x) by (apply wa_unsigned; lia).
      destruct (K (wa x) ltac:(rewrite U; lia)) as [NA _]. apply NA. rewrite U. exists iv. split; assumption. }
    split; apply region_free_of_bytes; try (unfold LS_LO, LS_SZ, HS_LO, HS_SZ; lia); try exact Hnapos.
    - intros iv x Hiv Hx. apply (KO 0x7fff7000 0x10000000); [cbn [In asan_ledger]; tauto | exact Hiv | unfold LS_LO, LS_SZ in Hx; lia | unfold LS_LO, LS_SZ in Hx; lia].
    - intros iv x Hiv Hx. apply (KO 0x2008fff7000 0xdfff0001000); [cbn [In asan_ledger]; tauto | exact Hiv | unfold HS_LO, HS_SZ in Hx; lia | unfold HS_LO, HS_SZ in Hx; lia]. }
  exists (vm_maps (m_vmmaps mo)). split; [rewrite app_nil_r; reflexivity|]. split.
  - (* [comment removed for export] *)
    cbn [ledger_den asan_ledger] in Hmaps.
    pose proof (ledger_den_In V asan_ledger _ Hmaps) as HIN. pose proof (ledger_den_length V asan_ledger _ Hmaps) as HLEN.
    unfold START, ainit. cbn [a_space_beg a_ptr_array].
    assert (INL : forall b n k, In (LMap b n k) asan_ledger -> In (went (zv V b, n)) (vm_maps (m_vmmaps mo))).
    { intros b n k H. exact (HIN b n k H). }
    Ltac inled := cbn [In asan_ledger]; repeat (try (left; reflexivity); right).
    assert (INP : In (went (4096 * V 208%nat, PRIM_SZ)) (vm_maps (m_vmmaps mo))).
    { apply (INL (ZMul (ZLit 4096) (ZV 208)) _ AsanPlan.AP.KRW); inled. }
    assert (INQ : In (went (4096 * V 226%nat, PTR_SZ)) (vm_maps (m_vmmaps mo))).
    { apply (INL (ZMul (ZLit 4096) (ZV 226)) _ AsanPlan.AP.KNONELAZY); inled. }
    pose proof (END _ _ INP) as [EP _]. pose proof (END _ _ INQ) as [EQ HQ]. cbn [fst snd] in EP, EQ, HQ.
    rewrite !unsigned_lit in EP by (unfold PRIM_SZ; lia). rewrite !unsigned_lit in EQ by (unfold PTR_SZ; lia).
    rewrite !unsigned_lit in HQ by (unfold PTR_SZ; lia).
    split.
    { exists (4096 * V 208%nat). split; [exact INP|]. unfold a_space_beg0, PRIM_SZ, KHIGH in *. lia. }
    split; [exact INQ|].
    split; [unfold a_ptr_array0; lia|].
    split. { (* LPS 727298f3: the pointer array is a mapping, so it misses the reserved ledger *)
             pose proof (NEWC _ INQ) as RQ. rewrite Hres in RQ. unfold a_ptr_array0. exact RQ. }
    split; [apply (INL (ZLit LS_LO) _ AsanPlan.AP.KRWLAZY); inled|].
    split; [apply (INL (ZLit GAP_LO) _ AsanPlan.AP.KNONELAZY); inled|].
    split; [apply (INL (ZLit HS_LO) _ AsanPlan.AP.KRWLAZY); inled|].
    split; [unfold AsanInv.zlen, LEN0; cbn [length asan_ledger] in HLEN; lia|].
    split. { rewrite live_bytes_ivs_sum. rewrite ivs_sum_app in Htot. pose proof (ivs_sum_nonneg (vm_reserved (m_vmmaps mo))).
             unfold TOT0. unfold ATOTSZ in Htot. lia. }
    (* [comment removed for export] *)
    unfold resv_of, resv_entries. rewrite map_app. apply Forall_app. split.
    + apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (e & <- & He). apply in_flat_map in He as (le & Hle & He).
      destruct le as [b n k|n]; [|destruct He]. destruct He as [<-|[]].
      exists (wa (zv V b), wa n). split; [apply in_app_iff; right; exact (INL b n k Hle)|]. unfold iv_of. cbn [fst snd]. lia.
    + apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (e & <- & He).
      exists e. split; [apply in_app_iff; left; apply in_app_iff; left; exact He|]. unfold iv_of. cbn [fst snd]. lia.
  - rewrite commit_bytes_ainit, Z.add_0_r.
    assert (W4 : AsanCeil.init_sp_ok (m_vmmaps mo)) by (unfold AsanCeil.init_sp_ok, sp_window_lo; rewrite Htop; lia).
    rewrite <- (nonlazy_sum_count (MX mo []) eq_refl ltac:(split; [exact W1| split; [exact W2| split; [exact W3| rewrite m_vmmaps_MX; exact W4]]])).
    rewrite (same_but_mat_nonlazy mo (MX mo []) (same_but_mat_MX mo [])). unfold EAGER0. unfold asan_eager in Hnl. lia.
Qed.

Lemma AMI_init : forall V sp fs mo,
  amodel V sp fs mo -> Forall (pfact_ok V) APKN ->
  AMI (resv_of V) (atop_of sp) [] (ainit (a_space_beg0 V) (a_ptr_array0 V)) (MX mo []).
Proof.
  intros V sp fs mo HM HP. apply (AMI_init_L target_alloc_limit V sp fs mo); [| apply amodel_amodelL; exact HM| exact HP].
  rewrite <- LIMIT_eq. apply LIMIT34_le_LIMIT.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma minv_fds3 : forall mo,
  m_fds mo = init_fds -> m_tid mo = Some (Z_to_bv 64 1) -> m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  sp_window_lo <= bv_unsigned (vm_init_sp (m_vmmaps mo)) <= sp_window_hi -> m_channel_reader mo = true -> minv mo.
Proof.
  intros mo Hf Ht Hl Hm Hsp Hrdr. unfold minv. rewrite Hf, Ht, Hl, Hm. unfold init_fds. cbn [fd_lookup].
  repeat split; try exact Hrdr; try reflexivity; try (intros; discriminate); try lia.
  - intros k c H.
    destruct (bv_eqb (Z_to_bv 64 0) k) eqn:E0. { apply bv_eqb_eq in E0. subst k. vm_compute. reflexivity. }
    destruct (bv_eqb (Z_to_bv 64 1) k) eqn:E1. { apply bv_eqb_eq in E1. subst k. vm_compute. reflexivity. }
    destruct (bv_eqb (Z_to_bv 64 2) k) eqn:E2. { apply bv_eqb_eq in E2. subst k. vm_compute. reflexivity. }
    discriminate.
  - intros k p off H.
    destruct (bv_eqb (Z_to_bv 64 0) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 2) k); discriminate.
  - intros k e H.
    destruct (bv_eqb (Z_to_bv 64 0) k); [inversion H; exact I|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [inversion H; exact I|].
    destruct (bv_eqb (Z_to_bv 64 2) k); [inversion H; exact I|discriminate].
  - match goal with H : Some _ = Some _ |- _ => injection H as <- end. vm_compute. reflexivity.
  - match goal with H : Some _ = Some _ |- _ => injection H as <- end. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma space_beg0_facts : forall V, Forall (pfact_ok V) APKN ->
  a_space_beg0 V mod 65536 = 0 /\ 0 < a_space_beg0 V /\ a_ptr_array0 V mod 4096 = 0 /\ 0 < a_ptr_array0 V.
Proof.
  intros V HP. destruct (placement_facts V HP) as (F208 & F209 & F226 & FR & _). unfold a_space_beg0, a_ptr_array0.
pose proof (Z.div_mod (4096 * V 208%nat) 65536 ltac:(lia)) as E. rewrite FR in E.
  split; [| split; [lia| split; [rewrite Z.mul_comm; apply Z_mod_mult| lia]]].
  replace (4096 * V 208%nat - 4096 * V 209%nat + 65536) with ((4096 * V 208%nat / 65536 + 1) * 65536) by lia.
  apply Z_mod_mult.
Qed.

Theorem AI_init_L : forall lim V sp fs mo, LIMIT34 <= lim ->
  amodelL lim V sp fs mo -> Forall (pfact_ok V) APKN ->
  AsanOK.AI [] (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) (MX mo [])
  /\ aps_so (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) = stdout_init
  /\ m_fds (MX mo []) = init_fds /\ m_fs (MX mo []) = fs /\ m_halted (MX mo []) = None.
Proof.
  intros lim V sp fs mo HLIM HM HP. destruct (space_beg0_facts V HP) as (S1 & S2 & S3 & S4).
  pose proof (AMI_init_L lim V sp fs mo HLIM HM HP) as HAMI. pose proof (amL_halted _ _ _ _ _ HM) as Hh. pose proof (amL_fds _ _ _ _ _ HM) as Hfds. pose proof (amL_fs _ _ _ _ _ HM) as Hfs.
  pose proof (amL_top _ _ _ _ _ HM) as Htop'. pose proof (amL_usp _ _ _ _ _ HM) as Husp'.
  split; [| split; [reflexivity| split; [rewrite m_fds_MX; exact Hfds| split; [rewrite m_fs_MX; exact Hfs| rewrite m_halted_MX; exact Hh]]]].
  unfold AsanOK.AI, aps_init. cbn [aps_m aps_resv aps_atop]. split.
  2:{ (* [comment removed for export] *)
      split. { intros c Hc. unfold ainit, get_cls. cbn. rewrite lookup_empty. cbn. unfold K_FREEARR_MAP.
lia. }
      split. { unfold ainit, NOPS. cbn. lia. }
      unfold AsanOK.VCB, VC0, VC, csum, ainit, get_cls. cbn [a_cls a_nres a_next fold_right CLASSES map seq Z.of_nat length].
      rewrite !lookup_empty. cbn. unfold vc_cls. cbn. replace (0 / 8) with 0 by reflexivity. unfold K_FREEARR_MAP. lia. }
  split.
  { split; [apply AINV_init; assumption|]. rewrite CH_ainit. exact HAMI. }
  split. { unfold live_pairs, ainit. cbn [a_live]. rewrite map_to_list_empty. reflexivity. }
  split; [unfold Q_CACHE; cbn; lia|]. split; [unfold Q_MAX; cbn; lia|].
  split; [| rewrite m_halted_MX; exact Hh].
  rewrite strip_MX. apply minv_fds3.
  - rewrite m_fds_strip. exact Hfds.
  - apply m_tid_strip.
  - reflexivity.
  - reflexivity.
  - change (m_vmmaps (strip mo)) with (m_vmmaps mo). rewrite Htop'. unfold sp_window_lo, sp_window_hi. lia.
  - change (m_channel_reader (strip mo)) with (m_channel_reader mo). exact (amL_reader _ _ _ _ _ HM).
Qed.

Theorem AI_init : forall V sp fs mo,
  amodel V sp fs mo -> Forall (pfact_ok V) APKN ->
  AsanOK.AI [] (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) (MX mo [])
  /\ aps_so (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) = stdout_init
  /\ m_fds (MX mo []) = init_fds /\ m_fs (MX mo []) = fs /\ m_halted (MX mo []) = None.
Proof.
  intros V sp fs mo HM HP. apply (AI_init_L target_alloc_limit V sp fs mo); [| apply amodel_amodelL; exact HM| exact HP].
  rewrite <- LIMIT_eq. apply LIMIT34_le_LIMIT.
Qed.

(* [comment removed for export] *)
Corollary AHAND_init : forall rsA V sp inp mo,
  amodel V sp (in_fs inp) mo -> Forall (pfact_ok V) APKN ->
  AHAND AAllocAsan nstepA PhiA minvA rsA AAllocAsanOK inp (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) (MX mo []).
Proof.
  intros rsA V sp inp mo HM HP. destruct (AI_init V sp (in_fs inp) mo HM HP) as (H1 & H2 & H3 & H4 & _).
  unfold AHAND. split.
  { split; [exact H1|]. unfold aps_init, ainit; cbn [aps_m a_next]. unfold MAIN_OPS, READ_OPS, RUN_OPS, FUZZ_OPS, NOPS. lia. }
  split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  apply tglob_trivial. intros; exact I.
Qed.

(* [comment removed for export] *)
Corollary equiv_PA_asan : forall rsP rsA V sp enP inp mo,
  valid_entry (mkImage psegs p_init_pc p_phdrs) enP inp -> valid_input_either inp ->
  amodel V sp (in_fs inp) mo -> Forall (pfact_ok V) APKN ->
  trace_equiv (tree_traces (prog psegs rsP inp enP) (mo0 psegs source_alloc_limit enP inp))
              (ptraces nstepA nexit (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []))
  /\ (forall tr r mo', ~ tpath nstepA (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []) tr r mo').
Proof.
  intros rsP rsA V sp enP inp mo He Hi HM HP. apply (equiv_PA _ _ _ _ rsP rsA AAllocAsanOK enP inp _ _ He Hi). apply AHAND_init; assumption.
Qed.

(* [comment removed for export] *)
Corollary equiv_PA_asan_toP_L : forall LS, 2^31 <= LS -> forall rsP rsA V sp segsX pcX phX enX inp mo,
  valid_entry (mkImage segsX pcX phX) enX inp -> valid_input_either inp ->
  amodel V sp (in_fs inp) mo -> Forall (pfact_ok V) APKN ->
  trace_equiv (tree_traces (prog psegs rsP inp (toP enX)) (mo0 psegs LS (toP enX) inp))
              (ptraces nstepA nexit (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []))
  /\ (forall tr r mo', ~ tpath nstepA (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []) tr r mo').
Proof.
  intros LS HLS rsP rsA V sp segsX pcX phX enX inp mo He Hi HM HP.
  apply (equiv_PA_toP_L _ _ _ _ rsP rsA AAllocAsanOK LS HLS segsX pcX phX enX inp _ _ He Hi). apply AHAND_init; assumption.
Qed.

(* [comment removed for export] *)
Corollary equiv_PA_asan_toP : forall rsP rsA V sp segsX pcX phX enX inp mo,
  valid_entry (mkImage segsX pcX phX) enX inp -> valid_input_either inp ->
  amodel V sp (in_fs inp) mo -> Forall (pfact_ok V) APKN ->
  trace_equiv (tree_traces (prog psegs rsP inp (toP enX)) (mo0 psegs source_alloc_limit (toP enX) inp))
              (ptraces nstepA nexit (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []))
  /\ (forall tr r mo', ~ tpath nstepA (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []) tr r mo').
Proof.
  intros rsP rsA V sp segsX pcX phX enX inp mo He Hi HM HP.
  apply (equiv_PA_toP _ _ _ _ rsP rsA AAllocAsanOK segsX pcX phX enX inp _ _ He Hi). apply AHAND_init; assumption.
Qed.

(* [comment removed for export] *)
Corollary AHAND_init_L : forall lim rsA V sp inp mo, LIMIT34 <= lim ->
  amodelL lim V sp (in_fs inp) mo -> Forall (pfact_ok V) APKN ->
  AHAND AAllocAsan nstepA PhiA minvA rsA AAllocAsanOK inp (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) (MX mo []).
Proof.
  intros lim rsA V sp inp mo HL HM HP. destruct (AI_init_L lim V sp (in_fs inp) mo HL HM HP) as (H1 & H2 & H3 & H4 & _).
  unfold AHAND. split.
  { split; [exact H1|]. unfold aps_init, ainit; cbn [aps_m a_next]. unfold MAIN_OPS, READ_OPS, RUN_OPS, FUZZ_OPS, NOPS. lia. }
  split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  apply tglob_trivial. intros; exact I.
Qed.

Corollary equiv_PA_asan_toP_LL : forall lim, LIMIT34 <= lim -> forall LS, 2^31 <= LS -> forall rsP rsA V sp segsX pcX phX enX inp mo,
  valid_entry (mkImage segsX pcX phX) enX inp -> valid_input_either inp ->
  amodelL lim V sp (in_fs inp) mo -> Forall (pfact_ok V) APKN ->
  trace_equiv (tree_traces (prog psegs rsP inp (toP enX)) (mo0 psegs LS (toP enX) inp))
              (ptraces nstepA nexit (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []))
  /\ (forall tr r mo', ~ tpath nstepA (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []) tr r mo').
Proof.
  intros lim HL LS HLS rsP rsA V sp segsX pcX phX enX inp mo He Hi HM HP.
  apply (equiv_PA_toP_L _ _ _ _ rsP rsA AAllocAsanOK LS HLS segsX pcX phX enX inp _ _ He Hi). apply (AHAND_init_L lim); assumption.
Qed.
