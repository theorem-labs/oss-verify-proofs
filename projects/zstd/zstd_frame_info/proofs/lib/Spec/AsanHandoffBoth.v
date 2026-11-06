(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem ITree Nodes.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import AcctCore ModelX NodesA.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import BackingAlgebra MainExport MainFactsBoth MainEntryBoth.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree Stdio AsanCtrl AsanCtrlProps SizeHist AsanProgDeps
  AsanInv AsanBudget AsanOK RSim Prog ProgA EquivPA.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ITreeA.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Plain Require Import PImg.
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
    Local Ltac2 Set LiaHints.tbl := fun () => "0020=2112218831.7 4740421781.11000001006SS3Hij".
destruct (H 0%nat (Datatypes.S j) p q ltac:(lia) eq_refl Hj) as [A|B]; unfold wsep; [left; exact A| right; exact B].
  - apply IH. intros i j p' q' Hij Hi Hj. apply (H (Datatypes.S i) (Datatypes.S j) p' q'); [lia| exact Hi| exact Hj].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma live_bytes_ivs_sum : forall l, live_bytes l = ivs_sum l.
Proof. induction l as [|[a n] l IH]; [reflexivity|]. cbn [ivs_sum snd]. rewrite <- IH. reflexivity. Qed.

Lemma ivs_sum_app : forall l1 l2, ivs_sum (l1 ++ l2) = ivs_sum l1 + ivs_sum l2.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0020=48499164402.454478046303.1000001002SS".
induction l1 as [|e l1 IH]; intros; cbn [ivs_sum app]; [lia|]. rewrite IH. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma ivs_sum_nonneg : forall l, 0 <= ivs_sum l.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0020=25608536147.439280637297.0000006007S2IH1HS".
induction l as [|e l IH]; cbn [ivs_sum]; [lia|]. pose proof (bv_unsigned_in_range _ (snd e)). lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

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
  - subst maps. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "0040=16856810389.816856810389.919080499823.148766883239.700000300600700:S1HS1HSS1H".
lia.
  - destruct HD as (maps' & -> & HD'). cbn. pose proof (IH _ HD'). lia.
  - destruct HD as [HD'|(iv & maps' & -> & _ & HD')]; cbn; pose proof (IH _ HD'); lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Lemma pfact_In : forall V f, Forall (pfact_ok V) both_pure_facts -> In f both_pure_facts -> pfact_ok V f.
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
Lemma pfact_find : forall V f, Forall (pfact_ok V) both_pure_facts -> existsb (pfact_eqb f) both_pure_facts = true -> pfact_ok V f.
Proof.
  intros V f HF HE. apply existsb_exists in HE as (g & Hin & Hg). apply pfact_eqb_eq in Hg. subst g.
  exact (proj1 (Forall_forall _ _) HF f Hin).
Qed.

Definition uns2 (p : word * word) : Z * Z := (bv_unsigned (fst p), bv_unsigned (snd p)).
Lemma reserved_eval : map uns2 (segments_reserved bsegs) = [(65536, 126976); (192512, 430080); (622592, 8192); (630784, 5619712)].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition resv_entries (V : nat -> Z) : list (word * word) :=
  flat_map (fun e => match e with LMap b n _ => [(wa (zv V b), wa n)] | LFog _ => [] end) both_ledger
  ++ segments_reserved bsegs.
Definition iv_of (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (fst e) + bv_unsigned (snd e)).
Definition resv_of (V : nat -> Z) : list (Z * Z) := map iv_of (resv_entries V).
Lemma live_bytes_uns2 : forall l, live_bytes l = fold_right (fun q acc => snd q + acc) 0 (map uns2 l).
Proof. induction l as [|[a n] l IH]; [reflexivity|]. cbn [map fold_right uns2 fst snd]. rewrite <- IH. reflexivity. Qed.
Lemma Forall_uns2 : forall (P : Z * Z -> Prop) l, Forall P (map uns2 l) -> Forall (fun e => P (uns2 e)) l.
Proof. induction l as [|e l IH]; intros H; [constructor|]. cbn [map] in H. apply Forall_cons_iff in H as [H1 H2]. constructor; auto. Qed.
Lemma reserved_facts :
  Forall (fun e => bv_unsigned (fst e) + bv_unsigned (snd e) <= RES_HI) (segments_reserved bsegs)
  /\ zlen (segments_reserved bsegs) <= LEN0 /\ live_bytes (segments_reserved bsegs) <= RTOT0
  /\ Forall (fun e => 65536 <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= 6250496) (segments_reserved bsegs).
Proof.
  pose proof reserved_eval as E. split; [|split; [|split]].
  - apply (Forall_uns2 (fun q => fst q + snd q <= RES_HI)). rewrite E. unfold RES_HI. Local Ltac2 Set LiaHints.tbl := fun () => "0040=17732104373.119757885786.151855111613.164046605800.1000001002003004SSSS".
repeat constructor; cbn; lia.
  - unfold AsanInv.zlen. rewrite <- (length_map uns2), E. unfold LEN0. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  - rewrite live_bytes_uns2, E. unfold RTOT0. cbn -[Z.le Z.pow]. lia.
  - apply (Forall_uns2 (fun q => 65536 <= fst q /\ fst q + snd q <= 6250496)). rewrite E. repeat constructor; cbn; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Lemma region_free_of_hull : forall l (g G : Z), 0 <= g -> 0 <= G -> g + G < 2^64 ->
  Forall (fun e => 65536 <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= 6250496) l ->
  (g + G <= 65536 \/ 6250496 <= g) ->
  region_free l (Z_to_bv 64 g) (Z_to_bv 64 G) = true.
Proof.
  induction l as [|[a sz] l IH]; intros g G Hg HG Hhi HF HD; [reflexivity|].
  apply Forall_cons_iff in HF as [H1 HF]. cbn [fst snd] in H1.
  cbn [region_free]. rewrite (IH g G Hg HG Hhi HF HD), andb_true_r.
  unfold iv_overlap. Local Ltac2 Set LiaHints.tbl := fun () => "0040>13741074330.1239074007783.1244936829850.1260321788253.1200000;00B00M00TS2Hg2HG3HhiS2H12HDS2Hg2HG3HhiS2H12HD".
rewrite !unsigned_lit by lia.
  apply negb_true_iff. apply andb_false_iff.
  destruct HD as [HD|HD]; [right| left]; apply Z.ltb_ge; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Lemma placement_facts : forall V, Forall (pfact_ok V) both_pure_facts ->
  4295491576 <= V 208%nat <= 34326181871 /\ 0 <= V 209%nat <= 15 /\ 1526 <= V 226%nat <= 34359734272
  /\ (4096 * V 208%nat) mod 65536 = 4096 * V 209%nat
  /\ (0 <= V 6%nat <= 255 /\ 0 <= V 10%nat <= 7 /\ 4294901760 <= V 0%nat <= 4294967295)
  /\ 4096 * V 208%nat + PRIM_SZ <= 32768 * V 0%nat + 4096 * V 10%nat - 8388608
  /\ 4096 * V 226%nat + PTR_SZ <= 32768 * V 0%nat + 4096 * V 10%nat - 8388608.
Proof.
  intros V HP.
  pose proof (pfact_find V (PVar 208 4295491576 34326181871) HP ltac:(vm_compute; reflexivity)) as H1; cbn in H1.
  pose proof (pfact_find V (PVar 209 0 15) HP ltac:(vm_compute; reflexivity)) as H2; cbn in H2.
  pose proof (pfact_find V (PVar 226 1526 34359734272) HP ltac:(vm_compute; reflexivity)) as H3; cbn in H3.
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
  { change 65535 with (Z.ones 16) in H4. Local Ltac2 Set LiaHints.tbl := fun () => "0070>11607912823.1518928648876.1125048079645.1131033709721.1536871115161.1365502219180.117375802461.11 00000100200F00O00S00T00_SSS2H12H33H102H02D12D2S2H21B2HkS2H4SS2H63H102H0".
rewrite Z.land_ones in H4 by lia. change (2^16) with 65536 in H4.
    pose proof (Z.mod_pos_bound (4096 * V 208%nat) 65536 ltac:(lia)) as B.
    set (u := (4096 * V 208%nat) mod 65536) in *.
    assert (Hv : (-4096 * V 209%nat + u) mod two64 = 0) by lia.
    apply Z.mod_divide in Hv; [| unfold two64; lia]. destruct Hv as [k Hk]. unfold two64 in Hk. lia. }
  split; [lia|]. unfold PRIM_SZ, PTR_SZ. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Lemma ivs_wf_of_bounds : forall l K, K <= 2^64 ->
  Forall (fun iv : word * word => bv_unsigned (fst iv) + bv_unsigned (snd iv) <= K) l -> ivs_wf l.
Proof. intros l K HK H q Hq. rewrite Forall_forall in H. unfold iv_wf, B, BackingAlgebra.S. pose proof (H q Hq). Local Ltac2 Set LiaHints.tbl := fun () => "0010=13423404452.7000007S2HK2H0".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Lemma AMI_init_L : forall lim V sp fs mo, LIMIT34 <= lim ->
  bmodelL lim V sp fs mo -> Forall (pfact_ok V) both_pure_facts ->
  AMI (resv_of V) (atop_of sp) [] (ainit (a_space_beg0 V) (a_ptr_array0 V)) (MX mo []).
Proof.
  intros lim V sp fs mo HLIM HM HP. destruct (placement_facts V HP) as (F208 & F209 & F226 & FR & _ & _ & _).
  destruct HM as [Hh Hfds Hfs Hres Hlim Hbrk Hsbrk Htop Husp Hmaps Hkinds Hsep Hbnd Hlzb Hnawf Hnasub Hnapos Htot Hnl Hab Hbud Halw Hnd Hmat].   (* [comment removed for export] *)
  unfold AMI. rewrite m_vm_materialized_MX, m_vmmaps_MX, m_vm_lazy_MX. change (Pm (MX mo [])) with (Pm mo).
  destruct reserved_facts as (R1 & R2 & R3 & R4).
  set (ATOP := atop_of sp). assert (EA : ATOP = bv_unsigned sp - 8388608) by reflexivity. clearbody ATOP.
  assert (W1 : ivs_wf (vm_maps (m_vmmaps mo))).
  { Local Ltac2 Set LiaHints.tbl := fun () => "00F0>18928857613.5324703179242.452620329599.49 26475966898.4632311040764.5333411160211.4235249985747.5338201735985.5440450650589.5240456785635.4340456785635.4541668039791.4341668275422.4145591436171.5346277875787.4548148967579.5350984776647.5358251332947.455871293818.53 59576967441.539656812506.57 9658910298.55 00000600:00N00S00^00_01201?01F01L01R01[01d01j02002A02Q02Z02c02i02o035S4HLENS2EAS4Husp4F2082EA2A52A6S3HnlS4F2264HLENSS4F2084F2094HLEN2EPS4Htot4HLEN1HS2EA2A6S2EA1HS2EA1HS4Husp2EAS4Husp2EAS4HLENS4HuspS4Husp2EA4HLEN2EQS4F2084HLEN4F226S4Husp2EAS4HLEN2EQS4HLENS4HLENS4HLEN".
apply (ivs_wf_of_bounds _ ATOP ltac:(lia)). eapply Forall_impl; [|exact Hbnd]. cbv beta. intros iv (_ & _ & _ & _ & _ & H). lia. }
  assert (W2 : ivs_wf (vm_noaccess (m_vmmaps mo))) by (apply (ivs_wf_of_bounds _ (2^64) ltac:(lia)); exact Hnawf).
  assert (W3 : ivs_wf (m_vm_lazy mo)).
  { apply (ivs_wf_of_bounds _ ATOP ltac:(lia)). eapply Forall_impl; [|exact Hlzb]. cbv beta. intros iv [_ H]. lia. }
  (* [comment removed for export] *)
  assert (END : forall b n, In (b, n) (vm_maps (m_vmmaps mo)) -> bv_unsigned b + bv_unsigned n <= ATOP
                             /\ (bv_unsigned b + bv_unsigned n <= 65536 \/ 6250496 <= bv_unsigned b)).
  { intros b n Hin. rewrite Forall_forall in Hbnd. destruct (Hbnd _ Hin) as (_ & _ & _ & _ & A5 & A6). cbn [fst snd] in A5, A6.
    unfold MainEntryBoth.BIMG_LO, MainEntryBoth.BIMG_HI in A5. lia. }
  split; [reflexivity|].
  split; [rewrite Hlim; exact HLIM|].   (* [comment removed for export] *)
  rewrite Hres. split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
  split. { eapply Forall_impl; [|exact Hbnd]. cbv beta. intros iv (A1 & A2 & A3 & A4 & A5 & A6). unfold entry_ok. repeat split; try assumption. lia. }
  split; [exact W2|]. split; [exact W3|]. split; [apply ivs_sep_seps; exact Hsep|].
  split. { split; [unfold atop_ok, ACEIL, AsanInv.ATOP_MAX; lia|]. unfold alloc_top, stack_max_size. rewrite Htop. lia. }
  exists (vm_maps (m_vmmaps mo)). split; [rewrite app_nil_r; reflexivity|]. split.
  - (* [comment removed for export] *)
    cbn [ledger_den both_ledger] in Hmaps.
    pose proof (ledger_den_In V both_ledger _ Hmaps) as HIN. pose proof (ledger_den_length V both_ledger _ Hmaps) as HLEN.
    unfold START, ainit. cbn [a_space_beg a_ptr_array].
    assert (INL : forall b n k, In (LMap b n k) both_ledger -> In (went (zv V b, n)) (vm_maps (m_vmmaps mo))).
    { intros b n k H. exact (HIN b n k H). }
    Ltac inled := cbn [In both_ledger]; repeat (try (left; reflexivity); right).
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
    split. { unfold a_ptr_array0. apply region_free_of_hull; [lia| unfold PTR_SZ; lia| unfold PTR_SZ in *; lia| exact R4| exact HQ]. }
    split; [apply (INL (ZLit LS_LO) _ AsanPlan.AP.KRWLAZY); inled|].
    split; [apply (INL (ZLit GAP_LO) _ AsanPlan.AP.KNONELAZY); inled|].
    split; [apply (INL (ZLit HS_LO) _ AsanPlan.AP.KRWLAZY); inled|].
    split; [unfold AsanInv.zlen, LEN0; cbn [length both_ledger] in HLEN; lia|].
    split. { rewrite live_bytes_ivs_sum. rewrite ivs_sum_app in Htot. pose proof (ivs_sum_nonneg (vm_reserved (m_vmmaps mo))).
             unfold TOT0. unfold both_totsz in Htot. lia. }
    (* [comment removed for export] *)
    unfold resv_of, resv_entries. rewrite map_app. apply Forall_app. split.
    + apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (e & <- & He). apply in_flat_map in He as (le & Hle & He).
      destruct le as [b n k|n]; [|destruct He]. destruct He as [<-|[]].
      exists (wa (zv V b), wa n). split; [apply in_app_iff; right; exact (INL b n k Hle)|]. unfold iv_of. cbn [fst snd]. lia.
    + apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (e & <- & He).
      exists e. split; [apply in_app_iff; left; exact He|]. unfold iv_of. cbn [fst snd]. lia.
  - rewrite commit_bytes_ainit, Z.add_0_r.
    assert (W4 : AsanCeil.init_sp_ok (m_vmmaps mo)) by (unfold AsanCeil.init_sp_ok, sp_window_lo; rewrite Htop; lia).
    rewrite <- (nonlazy_sum_count (MX mo []) eq_refl ltac:(split; [exact W1| split; [exact W2| split; [exact W3| rewrite m_vmmaps_MX; exact W4]]])).
    rewrite (same_but_mat_nonlazy mo (MX mo []) (same_but_mat_MX mo [])). unfold EAGER0. unfold both_eager in Hnl. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma AMI_init : forall V sp fs mo,
  bmodel V sp fs mo -> Forall (pfact_ok V) both_pure_facts ->
  AMI (resv_of V) (atop_of sp) [] (ainit (a_space_beg0 V) (a_ptr_array0 V)) (MX mo []).
Proof.
  intros V sp fs mo HM HP. apply (AMI_init_L target_alloc_limit V sp fs mo); [| apply bmodel_bmodelL; exact HM| exact HP].
  rewrite <- LIMIT_eq. apply LIMIT34_le_LIMIT.
Qed.

Lemma minv_fds3 : forall mo,
  m_fds mo = init_fds -> m_tid mo = Some (Z_to_bv 64 1) -> m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  sp_window_lo <= bv_unsigned (vm_init_sp (m_vmmaps mo)) <= sp_window_hi -> minv mo.
Proof.
  intros mo Hf Ht Hl Hm Hsp. unfold minv. rewrite Hf, Ht, Hl, Hm. unfold init_fds. cbn [fd_lookup].
  Local Ltac2 Set LiaHints.tbl := fun () => "0070=19565405918.619613117664.649602658903.851043007538.654707272175.860826458291.6721811629.6  00000100200300400500:00?FFFFFS3HspS3Hsp".
repeat split; try reflexivity; try (intros; discriminate); try lia.
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
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma space_beg0_facts : forall V, Forall (pfact_ok V) both_pure_facts ->
  a_space_beg0 V mod 65536 = 0 /\ 0 < a_space_beg0 V /\ a_ptr_array0 V mod 4096 = 0 /\ 0 < a_ptr_array0 V.
Proof.
  intros V HP. destruct (placement_facts V HP) as (F208 & F209 & F226 & FR & _). unfold a_space_beg0, a_ptr_array0.
  Local Ltac2 Set LiaHints.tbl := fun () => "0040=18926591958.632304533736.763643686531.764685162927.700000100700B00ESS4F226S4F2084F209S1E".
pose proof (Z.div_mod (4096 * V 208%nat) 65536 ltac:(lia)) as E. rewrite FR in E.
  split; [| split; [lia| split; [rewrite Z.mul_comm; apply Z_mod_mult| lia]]].
  replace (4096 * V 208%nat - 4096 * V 209%nat + 65536) with ((4096 * V 208%nat / 65536 + 1) * 65536) by lia.
  apply Z_mod_mult.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Theorem AI_init_L : forall lim V sp fs mo, LIMIT34 <= lim ->
  bmodelL lim V sp fs mo -> Forall (pfact_ok V) both_pure_facts ->
  AsanOK.AI0 [] (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) (MX mo [])
  /\ aps_so (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) = stdout_init
  /\ m_fds (MX mo []) = init_fds /\ m_fs (MX mo []) = fs /\ m_halted (MX mo []) = None.
Proof.
  intros lim V sp fs mo HLIM HM HP. destruct (space_beg0_facts V HP) as (S1 & S2 & S3 & S4).
  pose proof (AMI_init_L lim V sp fs mo HLIM HM HP) as HAMI. pose proof (bmL_halted _ _ _ _ _ HM) as Hh. pose proof (bmL_fds _ _ _ _ _ HM) as Hfds. pose proof (bmL_fs _ _ _ _ _ HM) as Hfs.
  pose proof (bmL_top _ _ _ _ _ HM) as Htop'. pose proof (bmL_usp _ _ _ _ _ HM) as Husp'.
  split; [| split; [reflexivity| split; [rewrite m_fds_MX; exact Hfds| split; [rewrite m_fs_MX; exact Hfs| rewrite m_halted_MX; exact Hh]]]].
  unfold AsanOK.AI0, aps_init. cbn [aps_m aps_resv aps_atop]. split.
  2:{ (* [comment removed for export] *)
      split. { intros c Hc. unfold ainit, get_cls. cbn. rewrite lookup_empty. cbn. unfold K_FREEARR_MAP. Local Ltac2 Set LiaHints.tbl := fun () => "0050>18939339063.1828142476801.1833026175975.2036702770032.1852557572407.1800000100200900@00ASSS5Husp'S5Husp'S".
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
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Theorem AI_init : forall V sp fs mo,
  bmodel V sp fs mo -> Forall (pfact_ok V) both_pure_facts ->
  AsanOK.AI0 [] (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) (MX mo [])
  /\ aps_so (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) = stdout_init
  /\ m_fds (MX mo []) = init_fds /\ m_fs (MX mo []) = fs /\ m_halted (MX mo []) = None.
Proof.
  intros V sp fs mo HM HP. apply (AI_init_L target_alloc_limit V sp fs mo); [| apply bmodel_bmodelL; exact HM| exact HP].
  rewrite <- LIMIT_eq. apply LIMIT34_le_LIMIT.
Qed.

(* [comment removed for export] *)
Corollary AHAND_init : forall rsA V sp inp mo,
  bmodel V sp (in_fs inp) mo -> Forall (pfact_ok V) both_pure_facts ->
  AHAND AAllocAsan nstepA PhiA minvA rsA AAllocAsanOK inp (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) (MX mo []).
Proof.
  intros rsA V sp inp mo HM HP. destruct (AI_init V sp (in_fs inp) mo HM HP) as (H1 & H2 & H3 & H4 & _).
  unfold AHAND. split; [exact (AI_of_AI0 _ _ _ H1 eq_refl eq_refl eq_refl (conj (proj1 MAIN_QCOST_ok) (Z.le_refl _)))|].   (* [comment removed for export] *)
  split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  apply tglob_trivial. intros; exact I.
Qed.

(* [comment removed for export] *)
Corollary equiv_PA_both : forall rsP rsA V sp enP inp mo,
  valid_entry (mkImage psegs p_init_pc p_phdrs) enP inp -> valid_input_either inp ->
  bmodel V sp (in_fs inp) mo -> Forall (pfact_ok V) both_pure_facts ->
  trace_equiv (tree_traces (prog psegs rsP inp enP) (mo0 psegs source_alloc_limit enP inp))
              (ptraces nstepA nexit (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []))
  /\ (forall tr r mo', ~ tpath nstepA (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []) tr r mo').
Proof.
  intros rsP rsA V sp enP inp mo He Hi HM HP. apply (equiv_PA _ _ _ _ rsP rsA AAllocAsanOK enP inp _ _ He Hi). apply AHAND_init; assumption.
Qed.

(* [comment removed for export] *)
Corollary equiv_PA_both_toP_L : forall LS, 2^31 <= LS -> forall rsP rsA V sp segsX pcX phX enX inp mo,
  valid_entry (mkImage segsX pcX phX) enX inp -> valid_input_either inp ->
  bmodel V sp (in_fs inp) mo -> Forall (pfact_ok V) both_pure_facts ->
  trace_equiv (tree_traces (prog psegs rsP inp (toP enX)) (mo0 psegs LS (toP enX) inp))
              (ptraces nstepA nexit (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []))
  /\ (forall tr r mo', ~ tpath nstepA (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []) tr r mo').
Proof.
  intros LS HLS rsP rsA V sp segsX pcX phX enX inp mo He Hi HM HP.
  apply (equiv_PA_toP_L _ _ _ _ rsP rsA AAllocAsanOK LS HLS segsX pcX phX enX inp _ _ He Hi). apply AHAND_init; assumption.
Qed.

(* [comment removed for export] *)
Corollary AHAND_init_L : forall lim rsA V sp inp mo, LIMIT34 <= lim ->
  bmodelL lim V sp (in_fs inp) mo -> Forall (pfact_ok V) both_pure_facts ->
  AHAND AAllocAsan nstepA PhiA minvA rsA AAllocAsanOK inp (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) (MX mo []).
Proof.
  intros lim rsA V sp inp mo HL HM HP. destruct (AI_init_L lim V sp (in_fs inp) mo HL HM HP) as (H1 & H2 & H3 & H4 & _).
  unfold AHAND. split; [exact (AI_of_AI0 _ _ _ H1 eq_refl eq_refl eq_refl (conj (proj1 MAIN_QCOST_ok) (Z.le_refl _)))|].
  split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  apply tglob_trivial. intros; exact I.
Qed.

Corollary equiv_PA_both_toP_LL : forall lim, LIMIT34 <= lim -> forall LS, 2^31 <= LS -> forall rsP rsA V sp segsX pcX phX enX inp mo,
  valid_entry (mkImage segsX pcX phX) enX inp -> valid_input_either inp ->
  bmodelL lim V sp (in_fs inp) mo -> Forall (pfact_ok V) both_pure_facts ->
  trace_equiv (tree_traces (prog psegs rsP inp (toP enX)) (mo0 psegs LS (toP enX) inp))
              (ptraces nstepA nexit (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []))
  /\ (forall tr r mo', ~ tpath nstepA (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []) tr r mo').
Proof.
  intros lim HL LS HLS rsP rsA V sp segsX pcX phX enX inp mo He Hi HM HP.
  apply (equiv_PA_toP_L _ _ _ _ rsP rsA AAllocAsanOK LS HLS segsX pcX phX enX inp _ _ He Hi). apply (AHAND_init_L lim); assumption.
Qed.

(* [comment removed for export] *)
Corollary equiv_PA_both_toP : forall rsP rsA V sp segsX pcX phX enX inp mo,
  valid_entry (mkImage segsX pcX phX) enX inp -> valid_input_either inp ->
  bmodel V sp (in_fs inp) mo -> Forall (pfact_ok V) both_pure_facts ->
  trace_equiv (tree_traces (prog psegs rsP inp (toP enX)) (mo0 psegs source_alloc_limit (toP enX) inp))
              (ptraces nstepA nexit (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []))
  /\ (forall tr r mo', ~ tpath nstepA (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rsA (argv_Z (in_argv inp))) (MX mo []) tr r mo').
Proof.
  intros rsP rsA V sp segsX pcX phX enX inp mo He Hi HM HP.
  apply (equiv_PA_toP _ _ _ _ rsP rsA AAllocAsanOK segsX pcX phX enX inp _ _ He Hi). apply AHAND_init; assumption.
Qed.
