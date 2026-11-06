(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require Import AsanPlanCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require RelSpec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad MSafe Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AcctCore ExecF ITreeA ModelX NodesA RunConst RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainExport. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainExport.TwB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.BS Require Import MainFactsAsan. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require MainEntry__AS. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS Require PrimaryShadow0. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReady.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.PrimaryShadow0.TwB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCeil.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require BackingAlgebra AsanCtrl AsanEmbed AsanCtrlProps AsanInv AsanBudget. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require ATsafeCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require ATsafeAlloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require SizeHist. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.BackingAlgebra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrlProps OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanBudget OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanTotal OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.ATsafeCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.ATsafeEv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.ATsafeAlloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.SizeHist.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require MSafeX USimX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface ATsafeX AIface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UDriverX__EquivA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.MSafeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.USimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.DecodeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapIface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.ATsafeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.AIface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UDriverX__EquivA.HeapI_A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition a_space_beg0 (V : nat -> Z) : Z := 4096 * V 208%nat - 4096 * V 209%nat + 65536.
Definition a_ptr_array0 (V : nat -> Z) : Z := 4096 * V 226%nat.
Definition atop_of (sp : word) : Z := bv_unsigned sp - 8388608.
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

Lemma ledger_den_length : forall V l maps, ledger_den V l maps -> (length maps <= length l)%nat.
Proof.
  induction l as [|[b n k|n] l IH]; intros maps HD; cbn [ledger_den] in HD.
  - subst maps. cbn. lia.
  - destruct HD as (maps' & -> & HD'). cbn. pose proof (IH _ HD'). lia.
  - destruct HD as [HD'|(iv & maps' & -> & _ & HD')]; cbn; pose proof (IH _ HD'); lia.
Qed.

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
Definition uns2 (p : word * word) : Z * Z := (bv_unsigned (fst p), bv_unsigned (snd p)).
Lemma reserved_eval : map uns2 (segments_reserved SEGS) = [(65536, 139264); (204800, 471040); (675840, 8192); (684032, 5623808)].   (* [comment removed for export] *)
Proof. vm_compute. reflexivity. Qed.

Definition resv_entries (V : nat -> Z) : list (word * word) :=
  flat_map (fun e => match e with LMap b n _ => [(wa (zv V b), wa n)] | LFog _ => [] end) asan_ledger
  ++ segments_reserved SEGS.
Definition iv_of (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (fst e) + bv_unsigned (snd e)).
Definition resv_of (V : nat -> Z) : list (Z * Z) := map iv_of (resv_entries V).

Lemma live_bytes_uns2 : forall l, live_bytes l = fold_right (fun q acc => snd q + acc) 0 (map uns2 l).
Proof. induction l as [|[a n] l IH]; [reflexivity|]. cbn [map fold_right uns2 fst snd]. rewrite <- IH. reflexivity. Qed.
Lemma Forall_uns2 : forall (P : Z * Z -> Prop) l, Forall P (map uns2 l) -> Forall (fun e => P (uns2 e)) l.
Proof. induction l as [|e l IH]; intros H; [constructor|]. cbn [map] in H. apply Forall_cons_iff in H as [H1 H2]. constructor; auto. Qed.
Lemma reserved_facts :
  Forall (fun e => bv_unsigned (fst e) + bv_unsigned (snd e) <= RES_HI) (segments_reserved SEGS)
  /\ zlen (segments_reserved SEGS) <= LEN0 /\ live_bytes (segments_reserved SEGS) <= RTOT0
  /\ Forall (fun e => 65536 <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= 6307840) (segments_reserved SEGS).
Proof.
  pose proof reserved_eval as E. split; [|split; [|split]].
  - apply (Forall_uns2 (fun q => fst q + snd q <= RES_HI)). rewrite E. unfold RES_HI. repeat constructor; cbn; lia.
  - unfold AsanInv.zlen. rewrite <- (length_map uns2), E. unfold LEN0. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
  - rewrite live_bytes_uns2, E. unfold RTOT0. cbn -[Z.le Z.pow]. lia.
  - apply (Forall_uns2 (fun q => 65536 <= fst q /\ fst q + snd q <= 6307840)). rewrite E. repeat constructor; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma region_free_of_hull : forall l (g G : Z), 0 <= g -> 0 <= G -> g + G < 2^64 ->
  Forall (fun e => 65536 <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= 6307840) l ->
  (g + G <= 65536 \/ 6307840 <= g) ->
  region_free l (Z_to_bv 64 g) (Z_to_bv 64 G) = true.
Proof.
  induction l as [|[a sz] l IH]; intros g G Hg HG Hhi HF HD; [reflexivity|].
  apply Forall_cons_iff in HF as [H1 HF]. cbn [fst snd] in H1.
  cbn [region_free]. rewrite (IH g G Hg HG Hhi HF HD), andb_true_r.
  unfold iv_overlap. rewrite !unsigned_lit by lia.
  apply negb_true_iff. apply andb_false_iff.
  destruct HD as [HD|HD]; [right| left]; apply Z.ltb_ge; lia.
Qed.

Local Ltac pf V HP f H := pose proof (pfact_find V _ f HP ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok zv] in H.

(* [comment removed for export] *)
Lemma placement_facts : forall V, Forall (pfact_ok V) asan_pure_facts ->
  4295491576 <= V 208%nat <= 34326181871 /\ 0 <= V 209%nat <= 15 /\ 1 <= V 226%nat <= 34359734272
  /\ (0 <= V 6%nat <= 255 /\ 0 <= V 10%nat <= 7 /\ 4294901760 <= V 0%nat <= 4294967295)
  /\ 4096 * V 208%nat + PRIM_SZ <= 32768 * V 0%nat + 4096 * V 10%nat - 8388608
  /\ 4096 * V 226%nat + PTR_SZ <= 32768 * V 0%nat + 4096 * V 10%nat - 8388608.
Proof.
  intros V HP.
  pf V HP (PVar 208 4295491576 34326181871) H1. pf V HP (PVar 209 0 15) H2. pf V HP (PVar 226 1 34359734272) H3.
  pf V HP (PVar 6 0 255) H6. pf V HP (PVar 10 0 7) H10. pf V HP (PVar 0 4294901760 4294967295) H0.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) D1.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) D2.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [split; [exact H6| split; [exact H10| exact H0]]|].
  unfold PRIM_SZ, PTR_SZ. clear HP. split.
  - destruct D1 as [D1|D1]; [lia| exfalso; lia].
  - destruct D2 as [D2|D2]; [lia| exfalso; lia].
Qed.


Lemma ivs_wf_of_bounds : forall l K, K <= 2^64 ->
  Forall (fun iv : word * word => bv_unsigned (fst iv) + bv_unsigned (snd iv) <= K) l -> ivs_wf l.
Proof. intros l K HK H q Hq. rewrite Forall_forall in H. unfold iv_wf, B, BackingAlgebra.S. pose proof (H q Hq). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section AtMain.
Context {rc : runConstT}.
Variables (V : nat -> Z) (en : ExecEntry) (inp : ProcInput) (mo_ : Model).
Hypothesis HM : amodel V en inp LIMIT mo_.
Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
Hypothesis HAT : ATOP = page_round_down_Z (bv_unsigned (en_sp en) - 8388608).
Hypothesis HUSP : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = bv_unsigned (en_sp en).
Hypothesis HVR : forall n, 0 <= V n < 2 ^ 64.
(* [comment removed for export] *)
#[using="HP HVR"] Lemma HAL : (4096 * V 208%nat) mod 65536 = 4096 * V 209%nat.
Proof. exact (proj1 (sb_align V HVR HP)). Qed.

Local Notation SB := (a_space_beg0 V).
Local Notation PA := (a_ptr_array0 V).
Local Notation RESV := (resv_of V).
Local Notation moA := (MX mo_ []).

#[using="en HP HAT HUSP"] Lemma ATOP_digits : ATOP = 32768 * V 0%nat + 4096 * V 10%nat - 8388608.
Proof.
  destruct (placement_facts V HP) as (_ & _ & _ & (F6 & F10 & F0) & _). rewrite HAT, <- HUSP.
  unfold page_round_down_Z, page_size.
  replace (32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608) with ((8 * V 0%nat + V 10%nat - 2048) * 4096 + 16 * V 6%nat) by lia.
  rewrite Z.div_add_l by lia. rewrite (Z.div_small (16 * V 6%nat) 4096) by lia. lia.
Qed.

#[using="HAT"] Lemma end_le_ATOP : forall a n, a mod 4096 = 0 -> n mod 4096 = 0 -> a + n <= bv_unsigned (en_sp en) - 8388608 -> a + n <= ATOP.
Proof.
  intros a n Ha Hn H. rewrite HAT. apply page_round_down_Z_ge_aligned; [| exact H].
  rewrite Z.add_mod by lia. rewrite Ha, Hn. reflexivity.
Qed.

#[using="en inp HM HP HAT HUSP"] Lemma AMI_init : AMI RESV ATOP [] (ainit SB PA) moA.
Proof.
  destruct (placement_facts V HP) as (F208 & F209 & F226 & (F6 & F10 & F0) & FP1 & FP2).
  pose proof ATOP_digits as EA.
  pose proof (am_reserved _ _ _ _ _ HM) as Hres. pose proof (am_limit _ _ _ _ _ HM) as Hlim. pose proof (am_top _ _ _ _ _ HM) as Htop.
  pose proof (am_usp _ _ _ _ _ HM) as Husp. pose proof (am_maps _ _ _ _ _ HM) as Hmaps. pose proof (am_sep _ _ _ _ _ HM) as Hsep.
  pose proof (am_bounds _ _ _ _ _ HM) as Hbnd. pose proof (am_lazy_bounds _ _ _ _ _ HM) as Hlzb. pose proof (am_noaccess_wf _ _ _ _ _ HM) as Hnawf.
  pose proof (am_totsz _ _ _ _ _ HM) as Htot. pose proof (am_nonlazy _ _ _ _ _ HM) as Hnl.
  unfold AMI. rewrite m_vm_materialized_MX, m_vmmaps_MX, m_vm_lazy_MX. change (Pm moA) with (Pm mo_).
  destruct reserved_facts as (R1 & R2 & R3 & R4).
  pose proof (@ATOP_lo rc) as AL. pose proof (@ATOP_hi rc) as AH.
  assert (W1 : ivs_wf (vm_maps (m_vmmaps mo_))).
  { apply (ivs_wf_of_bounds _ (bv_unsigned (en_sp en)) ltac:(lia)). eapply Forall_impl; [|exact Hbnd]. cbv beta. intros iv (_ & _ & _ & _ & _ & H). lia. }
  assert (W2 : ivs_wf (vm_noaccess (m_vmmaps mo_))) by (apply (ivs_wf_of_bounds _ (2^64) ltac:(lia)); exact Hnawf).
  assert (W3 : ivs_wf (m_vm_lazy mo_)).
  { apply (ivs_wf_of_bounds _ (bv_unsigned (en_sp en)) ltac:(lia)). eapply Forall_impl; [|exact Hlzb]. cbv beta. intros iv [_ H]. lia. }
  assert (END : forall b n, In (b, n) (vm_maps (m_vmmaps mo_)) -> bv_unsigned b + bv_unsigned n <= ATOP
                             /\ (bv_unsigned b + bv_unsigned n <= 65536 \/ 6307840 <= bv_unsigned b)).
  { intros b n Hin. rewrite Forall_forall in Hbnd. destruct (Hbnd _ Hin) as (_ & A2 & A3 & _ & A5 & A6). cbn [fst snd] in A2, A3, A5, A6.
    split; [apply end_le_ATOP; assumption| exact A5]. }
  split; [reflexivity|].
  split; [exact Hlim|].
  rewrite Hres. split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
  split. { rewrite Forall_forall. intros [b n] Hin. rewrite Forall_forall in Hbnd. destruct (Hbnd _ Hin) as (A1 & A2 & A3 & _). unfold entry_ok. cbn [fst snd] in *.
           repeat split; try assumption. exact (proj1 (END b n Hin)). }
  split; [exact W2|]. split; [exact W3|]. split; [apply ivs_sep_seps; exact Hsep|].
  split. { split; [unfold atop_ok, ACEIL, AsanInv.ATOP_MAX; lia|]. unfold alloc_top. rewrite Htop. rewrite HAT. unfold stack_max_size. reflexivity. }
  exists (vm_maps (m_vmmaps mo_)). split; [rewrite app_nil_r; reflexivity|]. split.
  - (* [comment removed for export] *)
    pose proof (fun b n k => ledger_den_In V asan_ledger _ b n k Hmaps) as HIN. pose proof (ledger_den_length V asan_ledger _ Hmaps) as HLEN.
    unfold START, ainit. cbn [a_space_beg a_ptr_array].
    assert (INL : forall b n k, In (LMap b n k) asan_ledger -> In (went (zv V b, n)) (vm_maps (m_vmmaps mo_))).
    { intros b n k H. exact (HIN b n k H). }
    assert (INP : In (went (4096 * V 208%nat, PRIM_SZ)) (vm_maps (m_vmmaps mo_))).
    { apply (INL (ZMul (ZLit 4096) (ZV 208)) _ KNONELAZY). cbn [In asan_ledger]. repeat (try (left; reflexivity); right). }
    assert (INQ : In (went (4096 * V 226%nat, PTR_SZ)) (vm_maps (m_vmmaps mo_))).
    { apply (INL (ZMul (ZLit 4096) (ZV 226)) _ KNONELAZY). cbn [In asan_ledger]. repeat (try (left; reflexivity); right). }
    pose proof (END _ _ INP) as [EP _]. pose proof (END _ _ INQ) as [EQ HQ]. cbn [fst snd] in EP, EQ, HQ.
    rewrite !unsigned_lit in EP by (unfold PRIM_SZ; lia). rewrite !unsigned_lit in EQ by (unfold PTR_SZ; lia).
    rewrite !unsigned_lit in HQ by (unfold PTR_SZ; lia).
    split.
    { exists (4096 * V 208%nat). split; [exact INP|]. unfold a_space_beg0, PRIM_SZ, KHIGH in *. lia. }
    split; [exact INQ|].
    split; [unfold a_ptr_array0; lia|].
    split. { unfold a_ptr_array0. apply region_free_of_hull; [lia| unfold PTR_SZ; lia| unfold PTR_SZ in *; lia| exact R4| exact HQ]. }
    split; [apply (INL (ZLit LS_LO) _ KRWLAZY); cbn [In asan_ledger]; repeat (try (left; reflexivity); right)|].
    split; [apply (INL (ZLit GAP_LO) _ KNONELAZY); cbn [In asan_ledger]; repeat (try (left; reflexivity); right)|].
    split; [apply (INL (ZLit HS_LO) _ KRWLAZY); cbn [In asan_ledger]; repeat (try (left; reflexivity); right)|].
    split; [unfold AsanInv.zlen, LEN0; cbn [length asan_ledger] in HLEN; lia|].
    split. { rewrite live_bytes_ivs_sum. rewrite ivs_sum_app in Htot. pose proof (ivs_sum_nonneg (vm_reserved (m_vmmaps mo_))).
             unfold TOT0. unfold asan_totsz in Htot. lia. }
    unfold resv_of, resv_entries. rewrite map_app. apply Forall_app. split.
    + apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (e & <- & He). apply in_flat_map in He as (le & Hle & He).
      destruct le as [b n k|n]; [|destruct He]. destruct He as [<-|[]].
      exists (wa (zv V b), wa n). split; [apply in_app_iff; right; exact (INL b n k Hle)|]. unfold iv_of. cbn [fst snd]. lia.
    + apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (e & <- & He).
      exists e. split; [apply in_app_iff; left; exact He|]. unfold iv_of. cbn [fst snd]. lia.
  - rewrite commit_bytes_ainit, Z.add_0_r.
    assert (W4 : AsanCeil.init_sp_ok (m_vmmaps mo_)) by (unfold AsanCeil.init_sp_ok, sp_window_lo; rewrite Htop; lia).
    rewrite <- (nonlazy_sum_count moA eq_refl ltac:(split; [exact W1| split; [exact W2| split; [exact W3| rewrite m_vmmaps_MX; exact W4]]])).
    rewrite (same_but_mat_nonlazy mo_ moA (same_but_mat_MX mo_ [])). unfold EAGER0. unfold asan_eager in Hnl. change (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct.eager_used mo_) with (nonlazy_bytes mo_) in Hnl. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="rc HP HVR"] Lemma space_beg0_facts : SB mod 65536 = 0 /\ 0 < SB /\ PA mod 4096 = 0 /\ 0 < PA.
Proof.
  destruct (placement_facts V HP) as (F208 & F209 & F226 & _). unfold a_space_beg0, a_ptr_array0.
  pose proof (Z.div_mod (4096 * V 208%nat) 65536 ltac:(lia)) as E. rewrite HAL in E.
  split; [| split; [lia| split; [rewrite Z.mul_comm; apply Z_mod_mult| lia]]].
  replace (4096 * V 208%nat - 4096 * V 209%nat + 65536) with ((4096 * V 208%nat / 65536 + 1) * 65536) by lia.
  apply Z_mod_mult.
Qed.

#[using="en HP HAT HUSP"] Lemma HSB_A : 0 <= SB /\ SB + K_SPACE_SIZE <= ATOP.
Proof.
  destruct (placement_facts V HP) as (F208 & F209 & F226 & _ & FP1 & FP2). rewrite ATOP_digits.
  unfold a_space_beg0, K_SPACE_SIZE, PRIM_SZ in *. lia.
Qed.
#[using="en HP HAT HUSP"] Lemma HPA_A : 0 <= PA /\ PA + K_PTRARR_RESERVE <= ATOP.
Proof.
  destruct (placement_facts V HP) as (F208 & F209 & F226 & _ & FP1 & FP2). rewrite ATOP_digits.
  unfold a_ptr_array0, K_PTRARR_RESERVE, PTR_SZ in *. lia.
Qed.
#[using="rc HP HVR"] Lemma SB_al : SB mod 4096 = 0.
Proof.
  pose proof space_beg0_facts as (H1 & _). apply (Z.mod_divide _ 65536) in H1; [|lia]. destruct H1 as [q Hq]. rewrite Hq.
  replace (q * 65536) with ((q * 16) * 4096) by lia. apply Z.mod_mul. lia.
Qed.
#[using="rc HP HVR"] Lemma PA_al : PA mod 4096 = 0.
Proof. pose proof space_beg0_facts as (_ & _ & H & _). exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition K0 : Z := 2^20 + (2^22 + 2) + (2^8 + 2).
Definition NMAXZ_A : Z := 2^24.
Definition NMAX_A : nat := Z.to_nat NMAXZ_A.
#[using="rc"] Lemma NMAX_A_Z : Z.of_nat NMAX_A = NMAXZ_A.
Proof. unfold NMAX_A. apply Z2Nat.id. unfold NMAXZ_A. lia. Qed.
Global Opaque NMAX_A.

Definition ash_pages : list word :=
  range_pages (shad SB) (shlen K_SPACE_SIZE) ++ range_pages (shad PA) (shlen K_PTRARR_RESERVE).
Definition Ahand : alw := fun p => bv_unsigned p mod 4096 = 0 /\ aallowed (allow_of OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReadyA.TwB.ASHOFF V asan_vis) p.
Definition A0 : alw := aunion Ahand ash_pages.

#[using="Type"] Theorem A0_init : forall (p : word), bv_unsigned p mod 4096 = 0 -> aallowed (allow_of OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReadyA.TwB.ASHOFF V asan_vis) p -> A0 p.
Proof. intros p Hal Ha. left. split; assumption. Qed.

#[using="rc"] Lemma HLIM_A : NLK0 + Z.of_nat NMAX_A * 4096 <= LIMIT.
Proof. rewrite NMAX_A_Z. vm_compute. discriminate. Qed.

#[using="Type"] Lemma shlen_vals : shlen K_SPACE_SIZE = 2^34 /\ shlen K_PTRARR_RESERVE = 2^20.
Proof. split; reflexivity. Qed.

#[using="rc en HP HAT HUSP HVR"] Lemma ABASE_SH_A : forall z',
  (shad SB <= z' < shad (SB + K_SPACE_SIZE) \/ shad PA <= z' < shad (PA + K_PTRARR_RESERVE)) -> A0 (page_base_of z').
Proof.
  intros z' Hz. right. unfold ash_pages. apply in_or_app.
  pose proof HSB_A as [S1 S2]. pose proof HPA_A as [P1 P2]. pose proof (@ATOP_hi rc) as AH.
  pose proof (shad_bounds 0%nat SB ltac:(unfold K_SPACE_SIZE in *; lia)) as SH1.
  pose proof (shad_bounds 0%nat PA ltac:(unfold K_PTRARR_RESERVE in *; lia)) as SH2.
  destruct Hz as [Hz|Hz]; [left|right]; apply range_pages_spec; try lia.
  - rewrite (shad8 0%nat SB K_SPACE_SIZE SB_al) in Hz. lia.
  - rewrite (shad8 0%nat PA K_PTRARR_RESERVE PA_al) in Hz. lia.
Qed.

(* [comment removed for export] *)
#[using="rc en HP HAT HUSP HVR"] Lemma A0_primary_shadow : forall p : word, bv_unsigned p mod 4096 = 0 -> shad SB <= bv_unsigned p < shad SB + 2^34 -> A0 p.
Proof.
  intros p Hal Hp. rewrite <- (page_base_of_self 0%nat p Hal). apply ABASE_SH_A. left.
  rewrite (shad8 0%nat SB K_SPACE_SIZE SB_al). rewrite (proj1 shlen_vals). exact Hp.
Qed.
#[using="rc en HP HAT HUSP HVR"] Lemma A0_ptrarr_shadow : forall p : word, bv_unsigned p mod 4096 = 0 -> shad PA <= bv_unsigned p < shad PA + 2^20 -> A0 p.
Proof.
  intros p Hal Hp. rewrite <- (page_base_of_self 0%nat p Hal). apply ABASE_SH_A. right.
  rewrite (shad8 0%nat PA K_PTRARR_RESERVE PA_al). rewrite (proj2 shlen_vals). exact Hp.
Qed.

#[using="rc en inp mo_ HM HP HAT HUSP"] Lemma A0_abud : abud A0 K0.
Proof.
  unfold A0, K0.
  pose proof HSB_A as [S1 S2]. pose proof HPA_A as [P1 P2]. pose proof shlen_vals as [E1 E2]. pose proof (@ATOP_hi rc) as AH.
  pose proof (shad_bounds 0%nat SB ltac:(unfold K_SPACE_SIZE in *; lia)) as SH1.
  pose proof (shad_bounds 0%nat PA ltac:(unfold K_PTRARR_RESERVE in *; lia)) as SH2.
  assert (HL : Z.of_nat (length ash_pages) <= (2^22 + 2) + (2^8 + 2)).
  { unfold ash_pages. rewrite length_app, Nat2Z.inj_add.
    pose proof (range_pages_length (shad SB) (shlen K_SPACE_SIZE) ltac:(lia) ltac:(rewrite E1; lia)).
    pose proof (range_pages_length (shad PA) (shlen K_PTRARR_RESERVE) ltac:(lia) ltac:(rewrite E2; lia)).
    rewrite E1, E2 in *. change (2^34 / 4096) with (2^22) in *. change (2^20 / 4096) with (2^8) in *. lia. }
  apply (abud_mono _ (2^20 + Z.of_nat (length ash_pages))); [apply abud_union| lia].
  destruct (aallowed_fin (allow_of OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.AS.MainEntry__AS.MainReadyA.TwB.ASHOFF V asan_vis) (am_allow_wf _ _ _ _ _ HM)) as (L & ND & HLL & HIN).
  exists L. split; [exact ND|]. split; [| intros p [Hal Ha]; apply HIN; assumption].
  pose proof (am_abytes _ _ _ _ _ HM) as AB. unfold asan_abytes in AB.
  pose proof (Z.div_le_mono _ _ 4096 ltac:(lia) AB) as AB'. change (4294967296 / 4096) with (2^20) in AB'. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="V en inp HM"] Lemma minv_lf_main : minv (lf moA).
Proof.
  pose proof (am_fds _ _ _ _ _ HM) as Hf. pose proof (am_tid _ _ _ _ _ HM) as Ht. pose proof (am_noabs _ _ _ _ _ HM) as Hn.
  unfold minv. rewrite lf_MX. rewrite m_fds_lf, m_fs_lf, Hf. cbn [fd_lookup].
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split.
  { intros k e H.
    destruct (bv_eqb (Z_to_bv 64 0) k) eqn:E0. { apply bv_eqb_eq in E0. subst k. injection H as <-. vm_compute. reflexivity. }
    destruct (bv_eqb (Z_to_bv 64 1) k) eqn:E1. { apply bv_eqb_eq in E1. subst k. injection H as <-. vm_compute. reflexivity. }
    destruct (bv_eqb (Z_to_bv 64 2) k) eqn:E2. { apply bv_eqb_eq in E2. subst k. injection H as <-. vm_compute. reflexivity. }
    discriminate. }
  split; [exact Ht|]. split; [split; reflexivity| exact Hn].
Qed.

#[using="V en inp HM"] Lemma minvA_main : minvA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanNodeSem.ASHM0 moA.
Proof.
  split; [exact minv_lf_main|]. split; [reflexivity|].
  unfold shinv, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanNodeSem.ASHM0. rewrite m_vmmaps_MX. constructor; [exact (am_sh_lo _ _ _ _ _ HM)|]. constructor; [exact (am_sh_hi _ _ _ _ _ HM)| constructor].
Qed.

#[using="en inp HM"] Lemma mrel_main : mrel A0 moA mo_.
Proof.
  unfold mrel. split.
  { unfold same_but_mat, MX. destruct mo_ as [fd [mp lzz mt] io fs pr lm tm]. reflexivity. }
  split; [reflexivity|]. split; [exact (am_mat_nodup _ _ _ _ _ HM)|].
  intros p Hp. destruct (am_mat _ _ _ _ _ HM p Hp) as (Hal & _ & Ha). apply A0_init; assumption.
Qed.

#[using="en inp HM HP HAT HUSP HVR"] Lemma INV_main : INV RESV ATOP [] [] (ainit SB PA) moA.
Proof.
  destruct space_beg0_facts as (S1 & S2 & S3 & S4).
  split; [apply AINV_init; assumption|]. rewrite CH_ainit. exact AMI_init.
Qed.

#[using="en inp HM HP HAT HUSP HVR"] Theorem AJ_main : forall lc of tls,
  AJ NMAX_A SB PA A0 RESV ∅ 0%N 0 A0 (mkPS (aheap_init SB PA RESV) lc of tls) moA.
Proof.
  intros lc of tls. unfold AJ. cbv zeta. cbn [ps_heap aheap_init ah_st ah_resv ah_addr ah_frames].
  split; [exact INV_main|]. split; [reflexivity|].
  split; [unfold ainit, Q_CACHE; cbn; lia|]. split; [unfold ainit, Q_MAX; cbn; lia|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [unfold ainit; cbn [a_live]; rewrite fmap_empty; reflexivity|]. split; [reflexivity|].
  split; [unfold pot_ok, VOLMAX; lia|].
  split.
  { exists [], K0. split; [unfold QOK; rewrite all_chunks_ainit; constructor|]. split; [apply alw_le_refl|]. split; [apply GA_nil|].
    split; [exact A0_abud|]. rewrite NMAX_A_Z. unfold K0, NMAXZ_A, VOLMAX. split; [lia|]. vm_compute. discriminate. }
  split; [intros k a H; rewrite lookup_empty in H; discriminate| constructor].
Qed.

#[using="V en HM"] Lemma fds_main : m_fds moA = m_fds mo_ /\ m_fs moA = in_fs inp /\ m_halted moA = None.
Proof.
  split; [reflexivity|]. split; [rewrite m_fs_MX; exact (am_fs _ _ _ _ _ HM)| rewrite m_halted_MX; exact (am_halted _ _ _ _ _ HM)].
Qed.
End AtMain.
