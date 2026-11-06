(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import AcctCore.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import BackingAlgebra.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanCtrlProps SizeHist Gap AsanInv AsanBudget AsanTotalCore AsanNodeSem AsanPlace.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithResv.
Context {RESV : list (Z * Z)} {ATOP : Z}.
(* [comment removed for export] *)
Context {SBc PAc : Z}.
Local Notation INV := (AsanInv.INV RESV ATOP).
Local Notation AMI := (AsanInv.AMI RESV ATOP).
Local Notation AINV := (AsanInv.AINV ATOP).
Local Notation aok := (AsanNodeSem.aok ATOP).
Local Notation apost := (AsanNodeSem.apost ATOP).
Local Notation chunk_wf := (AsanInv.chunk_wf ATOP).

(* [comment removed for export] *)
Definition room34 (e : aev) (mo : Model) : Prop :=
  match e with
  | AMmap a len _ flags => vm_backing_used mo + mmap_len len + RESERVE34 <= LIMIT34
                          /\ (flags = F_FIXED -> inW SBc PAc a (mmap_len len))
  | _ => True
  end.
Definition aok34 (e : aev) (mo : Model) : Prop := aok e mo /\ room34 e mo.
Local Notation atot := (atotal aok34 apost).

#[using="Type"] Lemma atot34_atot : forall {R} (t : AM R) mo P, atotal aok34 apost t mo P -> atotal aok apost t mo P.
Proof.
  intros R t. induction t as [r|e k IH]; intros mo P H; cbn in *; [exact H|].
  destruct H as [[Hok _] Hk]. split; [exact Hok|]. intros z mo' Hp. apply IH. exact (Hk z mo' Hp).
Qed.

#[using="Type"] Lemma INV_atop : forall pc pb st mo, INV pc pb st mo -> atop_ok ATOP /\ alloc_top (m_vmmaps mo) = ATOP.
Proof. intros pc pb st mo [_ HM]. exact (AMI_atop _ _ _ HM). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma region_free_sub : forall l (a n a' n' : Z),
  region_free l (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  0 <= a -> a <= a' -> 0 <= n' -> a' + n' <= a + n -> a + n < 2^64 ->
  region_free l (Z_to_bv 64 a') (Z_to_bv 64 n') = true.
Proof.
  induction l as [|[b sz] l IH]; intros a n a' n' H Ha Haa Hn Hsub Htop; [reflexivity|].
  cbn [region_free] in H |- *. apply andb_prop in H as [H1 H2]. rewrite (IH _ _ _ _ H2 Ha Haa Hn Hsub Htop), andb_true_r.
  unfold iv_overlap in *. Local Ltac2 Set LiaHints.tbl := fun () => "0060>28868884486.1954271249774.1956769863422.1961701819758.1961933949010.197509357152.19 00000900N00c01801M01US2H14HsubS2Ha3Haa2Hn4Hsub4HtopS2Ha3Haa2Hn4Hsub4HtopS2Ha3Haa2Hn4Hsub4HtopS2Ha3Haa2Hn4Hsub4HtopS2H13Haa".
rewrite !unsigned_lit in H1 |- * by lia.
  apply negb_true_iff in H1. apply negb_true_iff. apply andb_false_iff in H1. apply andb_false_iff.
  destruct H1 as [H1|H1]; apply Z.ltb_ge in H1; [left|right]; apply Z.ltb_ge; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition same_but (c : Z) (st st' : astate) : Prop :=
  a_space_beg st' = a_space_beg st /\ a_ptr_array st' = a_ptr_array st /\ a_nres st' = a_nres st /\ a_nsec st' = a_nsec st
  /\ a_cinit st' = a_cinit st /\ a_live st' = a_live st /\ a_next st' = a_next st
  /\ a_qloc st' = a_qloc st /\ a_qloc_bytes st' = a_qloc_bytes st /\ a_qglob st' = a_qglob st /\ a_qglob_bytes st' = a_qglob_bytes st
  /\ (forall c', c' <> c -> get_cls st' c' = get_cls st c').

#[using="Type"] Lemma same_but_refl : forall c st, same_but c st st.
Proof. intros. unfold same_but. repeat split; reflexivity. Qed.
#[using="Type"] Lemma same_but_put : forall c st r, same_but c st (put_cls c r st).
Proof. intros. unfold same_but. repeat split; try reflexivity. intros c' Hc'. apply get_put_ne. congruence. Qed.
#[using="Type"] Lemma same_but_trans : forall c st1 st2 st3, same_but c st1 st2 -> same_but c st2 st3 -> same_but c st1 st3.
Proof.
  intros c st1 st2 st3 A B. unfold same_but in *.
  destruct A as (?&?&?&?&?&?&?&?&?&?&?&HA). destruct B as (?&?&?&?&?&?&?&?&?&?&?&HB).
  repeat split; try congruence. intros c' Hc'. rewrite HB, HA; auto.
Qed.

(* [comment removed for export] *)
Definition CLSOK (pc : list achunk) (pb : list abatch) (st : astate) (c : Z) (r : aclass) : Prop :=
  0 <= c_allocated_user r /\ c_allocated_user r <= c_mapped_user r /\ c_mapped_user r <= K_FREEARR_OFF
  /\ c_mapped_user r - c_allocated_user r <= 2 * K_USER_MAP
  /\ c_mapped_user r mod K_USER_MAP = 0
  /\ 0 <= c_mapped_free_array r <= K_FREEARR_MAX /\ c_mapped_free_array r mod K_FREEARR_MAP = 0
  /\ 0 <= c_num_freed r /\ 0 <= c_count r <= max_count st c
  /\ c_allocated_user r = size_of_class c * (cntP c (all_chunks pc pb st) + nbatch c (qbatches pb st) + c_count r + c_num_freed r).

#[using="Type"] Lemma AINV_cls : forall pc pb st c, AINV pc pb st -> 1 <= c <= 31 -> CLSOK pc pb st c (get_cls st c).
Proof. intros pc pb st c (H & _) Hc. exact (H c Hc). Qed.

#[using="Type"] Lemma AINV_put_cls : forall pc pb st c r, AINV pc pb st -> 1 <= c <= 31 -> CLSOK pc pb st c r -> AINV pc pb (put_cls c r st).
Proof.
  intros pc pb st c r H Hc HR. unfold AINV in *. rewrite !all_chunks_put, !qbatches_put, !CH_put.
  destruct H as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9). cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array put_cls set_cls] in *.
  split; [| repeat (split; [assumption|]); assumption].
  intros c' Hc'. unfold cls_inv. rewrite max_count_put, all_chunks_put, qbatches_put.
  destruct (Z.eq_dec c' c) as [->|Hne].
  - rewrite get_put_eq. exact HR.
  - rewrite get_put_ne by congruence. exact (HC c' Hc').
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma csum_bound : forall f st b, (forall c, 1 <= c <= 31 -> f (get_cls st c) <= b) -> csum f st <= 31 * b.
Proof.
  intros f st b H. unfold csum.
  assert (G : forall l, (forall c, In c l -> 1 <= c <= 31) -> fold_right (fun c acc => f (get_cls st c) + acc) 0 l <= zlen l * b).
  { Local Ltac2 Set LiaHints.tbl := fun () => "0020>11230286681.9 31327788433.13000001008SS2IH2H0".
induction l as [|c l IH]; intros Hl; unfold zlen in *; cbn [fold_right length]; [lia|]. rewrite Nat2Z.inj_succ.
    pose proof (H c (Hl c (or_introl eq_refl))). specialize (IH ltac:(intros; apply Hl; right; assumption)). lia. }
  specialize (G CLASSES ltac:(intros c Hc; apply In_CLASSES; exact Hc)). change (zlen CLASSES) with 31 in G. exact G.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma csum_nonneg : forall f st, (forall c, 1 <= c <= 31 -> 0 <= f (get_cls st c)) -> 0 <= csum f st.
Proof.
  intros f st H. unfold csum.
  assert (G : forall l, (forall c, In c l -> 1 <= c <= 31) -> 0 <= fold_right (fun c acc => f (get_cls st c) + acc) 0 l).
  { Local Ltac2 Set LiaHints.tbl := fun () => "0020>12190443548.1215045126238.8 000007008S2IH2H0S".
induction l as [|c l IH]; intros Hl; cbn [fold_right]; [lia|].
    pose proof (H c (Hl c (or_introl eq_refl))). specialize (IH ltac:(intros; apply Hl; right; assumption)). lia. }
  apply G. intros c Hc; apply In_CLASSES; exact Hc.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Definition CBMAX : Z := 31 * (K_FREEARR_OFF + K_FREEARR_MAX) + 8 * K_CHUNKS_BLOCK.
#[using="Type"] Lemma commit_bytes_bound : forall pc pb st, AINV pc pb st -> 0 <= commit_bytes st <= CBMAX.
Proof.
  intros pc pb st H. pose proof H as (HC & _ & _ & _ & _ & _ & Hres & _).
  unfold commit_bytes, CBMAX.
  pose proof (csum_bound cls_mapped_bytes' st (K_FREEARR_OFF + K_FREEARR_MAX)) as B1.
  pose proof (csum_nonneg cls_mapped_bytes' st) as B0.
  assert (A : forall c, 1 <= c <= 31 -> 0 <= cls_mapped_bytes' (get_cls st c) <= K_FREEARR_OFF + K_FREEARR_MAX).
  { intros c Hc. destruct (HC c Hc) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10). unfold cls_mapped_bytes'. Local Ltac2 Set LiaHints.tbl := fun () => "0020>2263976551.12 49835009122.2400000700DS2B12B0S2A12A22A32A6".
lia. }
  specialize (B1 ltac:(intros c Hc; apply A; exact Hc)). specialize (B0 ltac:(intros c Hc; apply A; exact Hc)).
  unfold K_CHUNKS_BLOCK in *. destruct Hres as [-> | ->]; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_len_id : forall l, 0 <= l -> l mod 4096 = 0 -> mmap_len l = l.
Proof.
  intros l Hl Hm. unfold mmap_len, page_round_up_Z, page_size.
  Local Ltac2 Set LiaHints.tbl := fun () => "0040=16311315874.818926747947.718933043916.857009198274.8000003004005008S1HSSS1H".
pose proof (Z.div_mod l 4096 ltac:(lia)). rewrite Hm in H.
  replace (l + 4096 - 1) with (l / 4096 * 4096 + 4095) by lia.
  rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma region_free_above : forall l (a n : Z) R,
  Forall (fun e => bv_unsigned (fst e) + bv_unsigned (snd e) <= R) l -> R <= a -> 0 <= a -> a + n < 2^64 -> 0 <= n ->
  region_free l (Z_to_bv 64 a) (Z_to_bv 64 n) = true.
Proof.
  induction l as [|[b s] l IH]; intros a n R Hf HR Ha Han Hn; [reflexivity|].
  apply Forall_cons_iff in Hf as [H1 Hf]. cbn [region_free]. rewrite (IH a n R Hf HR Ha Han Hn).
  unfold iv_overlap. Local Ltac2 Set LiaHints.tbl := fun () => "0030>21441432937.1756765665632.1761929758668.1700000700B00MS2H12HRS2Ha3Han2HnS2Ha3Han2Hn".
rewrite !unsigned_lit by lia. cbn [fst snd] in H1.
  replace (a <? bv_unsigned b + bv_unsigned s) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma CH_wf : forall pc pb st, AINV pc pb st -> Forall (fun e => 0 <= snd e < 2^64) (CH pc pb st).
Proof.
  intros pc pb st (_ & Hwf & _). unfold CH. induction (all_chunks pc pb st) as [|ch l IH]; [constructor|].
  apply Forall_cons_iff in Hwf as [H1 Hwf]. rewrite secs_cons. apply Forall_app. split; [|apply IH; exact Hwf].
  destruct ch as [c n|mb ms n]; cbn [sec_of]; [constructor|]. constructor; [|constructor]. cbn [snd].
  cbn [chunk_wf] in H1. destruct H1 as (Hn & -> & _). Local Ltac2 Set LiaHints.tbl := fun () => "0020>39934119984.1447473501062.1300000600:S2Hn1HS2Hn".
pose proof (sec_map_size_bounds n ltac:(lia)). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma INV_backing_bound : forall pc pb st mo, INV pc pb st mo ->
  vm_backing_used mo <= EAGER0 + CBMAX + zsum2 (CH pc pb st).
Proof.
  intros pc pb st mo [HA HM]. pose proof (AMI_nonlazy_bound _ _ _ HM (CH_wf _ _ _ HA)).
  pose proof (commit_bytes_bound _ _ _ HA). rewrite vm_backing_used_split. destruct HM as (-> & _). cbn [length Z.of_nat]. Local Ltac2 Set LiaHints.tbl := fun () => "0010>68272069675.11000006S1H2H0".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma INV_backing_bound2 : forall pc pb st mo, INV pc pb st mo ->
  vm_backing_used mo <= EAGER0 + commit_bytes st + zsum2 (CH pc pb st).
Proof.
  intros pc pb st mo [HA HM]. pose proof (AMI_nonlazy_bound _ _ _ HM (CH_wf _ _ _ HA)).
  rewrite vm_backing_used_split. destruct HM as (-> & _). cbn [length Z.of_nat]. Local Ltac2 Set LiaHints.tbl := fun () => "0010=2543782937.10000003S1H".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma VCMAX_CBROOM : VCMAX + 2^30 <= CBROOM /\ 0 <= VC0 /\ VCMAX <= 2^28.
Proof. unfold VCMAX, CBROOM, VC0, NOPS. Local Ltac2 Set LiaHints.tbl := fun () => "0010=44092437757.4000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma csum_ge_cls : forall f st c, 1 <= c <= 31 -> (forall c', 1 <= c' <= 31 -> 0 <= f (get_cls st c')) -> f (get_cls st c) <= csum f st.
Proof.
  intros f st c Hc Hf. unfold csum.
  assert (G : forall l, (forall c', In c' l -> 1 <= c' <= 31) -> List.NoDup l ->
            fold_right (fun c0 acc => f (get_cls st c0) + acc) 0 l >= (if existsb (Z.eqb c) l then f (get_cls st c) else 0)).
  { Local Ltac2 Set LiaHints.tbl := fun () => "0040>15045229622.1137874022404.1055195811623.1661691847039.1800000100400800>SS1GS2IHS2IH1H".
induction l as [|c0 l IH]; intros Hl ND; cbn [fold_right existsb]; [lia|].
    inversion ND; subst. specialize (IH ltac:(intros; apply Hl; right; assumption) ltac:(assumption)).
    pose proof (Hf c0 (Hl c0 (or_introl eq_refl))).
    destruct (Z.eqb_spec c c0) as [<-|NE]; cbn [orb].
    - replace (existsb (Z.eqb c) l) with false in IH; [lia|]. symmetry. apply existsb_Forall_false || idtac.
      destruct (existsb (Z.eqb c) l) eqn:E; [|reflexivity]. exfalso. apply existsb_exists in E as (x & Hx & Ex). apply Z.eqb_eq in Ex. subst x. contradiction.
    - lia. }
  specialize (G CLASSES ltac:(intros c' Hc'; apply In_CLASSES; exact Hc') CLASSES_nodup).
  replace (existsb (Z.eqb c) CLASSES) with true in G; [lia|]. symmetry. apply existsb_exists. exists c. split; [apply In_CLASSES; exact Hc| apply Z.eqb_refl].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma VC_set_next : forall x st, VC (set_next x st) = VC st. Proof. reflexivity. Qed.
#[using="Type"] Lemma VC_set_live : forall x st, VC (set_live x st) = VC st. Proof. reflexivity. Qed.
#[using="Type"] Lemma VC_set_nsec : forall x st, VC (set_nsec x st) = VC st. Proof. reflexivity. Qed.
#[using="Type"] Lemma VC_set_qloc : forall x y st, VC (set_qloc x y st) = VC st. Proof. reflexivity. Qed.
#[using="Type"] Lemma VC_set_qglob : forall x y st, VC (set_qglob x y st) = VC st. Proof. reflexivity. Qed.
#[using="Type"] Lemma FAINV_frame : forall st st', (forall c, get_cls st' c = get_cls st c) -> FAINV st -> FAINV st'.
Proof. intros st st' E H c Hc. rewrite E. apply H. exact Hc. Qed.
Ltac fainv_frame H := apply (FAINV_frame _ _ ltac:(intros; reflexivity) H).

(* [comment removed for export] *)
#[using="Type"] Lemma INV_limit : forall pc pb st mo, INV pc pb st mo -> LIMIT34 <= vm_limit (m_vmmaps mo).
Proof. intros pc pb st mo [_ HM]. destruct HM as (_ & M2 & _). exact M2. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma INV_fixed_aok : forall pc pb st mo E a len,
  INV pc pb st mo -> In E (vm_maps (m_vmmaps mo)) -> B E <= a -> a + len <= B E + S E ->
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 len) = true -> 0 < a ->
  a mod 4096 = 0 -> len mod 4096 = 0 -> 0 < len <= 2^30 -> zsum2 (CH pc pb st) <= SECM ->
  commit_bytes st + len <= CBROOM -> inW SBc PAc a len ->         (* [comment removed for export] *)
  aok34 (AMmap a len PROT_RW F_FIXED) mo.
Proof.
  intros pc pb st mo E a len HI HinE HE1 HE2 HR Ha0 Hal Hll Hlen HSB HCB HW.
  pose proof HI as [HA HM]. pose proof (AMI_ivs_wf _ _ _ HM) as Hwf.
  pose proof (INV_backing_bound2 _ _ _ _ HI) as HBB.
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & [[T1 T2] T3] & _).
  assert (HEok : bv_unsigned (fst E) + bv_unsigned (snd E) <= ATOP) by (destruct (proj1 (Forall_forall _ _) M6 E HinE) as (_ & _ & _ & ?); assumption).
  unfold RES_HI, ACEIL, ATOP_MAX in *. unfold B, S in *. pose proof (bv_unsigned_in_range 64 (fst E)) as HE0.
  Local Ltac2 Set LiaHints.tbl := fun () => "00>0>10828928558.4218065082425.4218761076320.4124341999539.4226983531493.4228322901527.4143072187067.4243470990928.4251688505431.4256765579266.4258220513317.4261211478416.4263347168513.4365121124526.4200000600;00A00F00K00P00U00Z00g01=01C01M01\01bS4HlenS3HE1S4HlenS3Ha0S3Ha0S3HllS3HE2S3HalS3HSB3HCB3HBBS3HE23Ha04Hlen2T24HEokS4HlenS3HE24HEokS3HSB3HCB3HBB1HS4Hlen".
assert (ML : mmap_len len = len) by (apply mmap_len_id; lia).
  split. 2:{ cbn [room34]. rewrite ML. split; [| intros _; exact HW]. unfold EAGER0, SECM, CBROOM, RESERVE34, LIMIT34 in *. lia. }
  cbn [AsanNodeSem.aok]. split; [reflexivity|]. split; [lia|]. split; [exact T3|].
  replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite ML. split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [|split].
  - exact HR.
  - apply (map_contains_In _ E); auto; rewrite !unsigned_lit by lia; lia.
  - apply mmap_fixed_rw_budget_ok_commit_intro; [reflexivity| exact Hwf|].
    rewrite !unsigned_lit by lia. eapply Z.le_trans; [| exact M2].
    pose proof (overlap_sum_contained (vm_maps (m_vmmaps mo)) E a (a + len) M9 HinE ltac:(unfold B; lia) ltac:(unfold B, S; lia) ltac:(lia)).
    unfold EAGER0, SECM, CBROOM, RESERVE34, LIMIT34 in *. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma INV_resv_hi : forall pc pb st mo, INV pc pb st mo ->
  Forall (fun e => bv_unsigned (fst e) + bv_unsigned (snd e) <= RES_HI) (vm_reserved (m_vmmaps mo)).
Proof. intros pc pb st mo [_ HM]. destruct HM as (_ & _ & M3 & _). exact M3. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma INV_fixed_aok_high : forall pc pb st mo E a len,
  INV pc pb st mo -> In E (vm_maps (m_vmmaps mo)) -> B E <= a -> a + len <= B E + S E -> RES_HI <= a ->
  a mod 4096 = 0 -> len mod 4096 = 0 -> 0 < len <= 2^30 -> zsum2 (CH pc pb st) <= SECM ->
  commit_bytes st + len <= CBROOM -> inW SBc PAc a len ->         (* [comment removed for export] *)
  aok34 (AMmap a len PROT_RW F_FIXED) mo.
Proof.
  intros pc pb st mo E a len HI HinE HE1 HE2 HR Hal Hll Hlen HSB HCB HW.
  pose proof HI as [HA HM]. pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & [[T1 T2] T3] & _).
  assert (HEok : bv_unsigned (fst E) + bv_unsigned (snd E) <= ATOP) by (destruct (proj1 (Forall_forall _ _) M6 E HinE) as (_ & _ & _ & ?); assumption).
  unfold ACEIL, ATOP_MAX in T1, T2. unfold B, S in HE1, HE2. unfold RES_HI in HR.
  Local Ltac2 Set LiaHints.tbl := fun () => "0050>18611135974.3718771563837.3726987814148.373839127040.37 50805312270.3700000100700;00?00LFS4HlenS2HRS2HRS3HE22T24HEok".
apply (INV_fixed_aok pc pb st mo E a len HI HinE); unfold B, S; auto; try lia.
  apply (region_free_above _ a len RES_HI M3); unfold RES_HI in *; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma INV_recommit_aok : forall pc pb st mo E a len,
  INV pc pb st mo -> In E (vm_maps (m_vmmaps mo)) -> B E <= a -> a + len <= B E + S E -> RES_HI <= a ->
  a mod 4096 = 0 -> len mod 4096 = 0 -> 0 < len <= 2^30 -> zsum2 (CH pc pb st) <= SECM ->
  commit_bytes st + len <= CBROOM ->                              (* [comment removed for export] *)
  aok34 (AMmap a len PROT_RW F_FIXNORES) mo.
Proof.
  intros pc pb st mo E a len HI HinE HE1 HE2 HR Hal Hll Hlen HSB HCB.
  pose proof (INV_backing_bound2 _ _ _ _ HI) as HBB.
  pose proof HI as [HA HM]. pose proof (AMI_ivs_wf _ _ _ HM) as Hwf.
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & [[T1 T2] T3] & _).
  assert (HEok : bv_unsigned (fst E) + bv_unsigned (snd E) <= ATOP) by (destruct (proj1 (Forall_forall _ _) M6 E HinE) as (_ & _ & _ & ?); assumption).
  unfold RES_HI, ACEIL, ATOP_MAX in *. unfold B, S in *. pose proof (bv_unsigned_in_range 64 (fst E)) as HE0.
  Local Ltac2 Set LiaHints.tbl := fun () => "00A0>10828928558.4010891467118.4018065082425.4018758896604.4018761076320.392004842709.40 24341999539.4026983531493.4028320754603.4028322901527.3943072187067.4043470990928.4050817848815.4051688505431.4056765579266.4061211478416.4065121124526.4000000600700<00B00H00Z00^00b00g00l01101601C01P01e01o025S4HlenFS3HE1S4HlenS4HlenS4Hlen3HSB3HCB3HBBS2HRS2HRS3HllS3HllS3HE2S3HalS3HE22T24HEokS3HSB3HCB3HBBS3HE22HR4Hlen2T24HEokS3HE24HEokS4Hlen".
assert (ML : mmap_len len = len) by (apply mmap_len_id; lia).
  split. 2:{ cbn [room34]. rewrite ML. split; [| intros EF; exfalso; revert EF; cbv; discriminate]. unfold EAGER0, SECM, CBROOM, RESERVE34, LIMIT34 in *. lia. }
  cbn [AsanNodeSem.aok]. split; [reflexivity|]. split; [lia|]. split; [exact T3|].
  replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite ML. split; [right; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [|split].
  - apply (region_free_above _ a len 0x7fff7000); auto; try lia.
  - apply (map_contains_In _ E); auto; rewrite !unsigned_lit by lia; lia.
  - apply mmap_fixed_rw_budget_ok_recommit_intro; [reflexivity| exact Hwf| | | | |];
      rewrite ?unsigned_lit by lia; unfold page_size; try lia.
    eapply Z.le_trans; [| exact M2]. unfold EAGER0, SECM, CBROOM, RESERVE34, LIMIT34 in *. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma INV_munmap_aok : forall pc pb st mo mb ms,
  INV pc pb st mo -> In (mb, ms) (CH pc pb st) ->
  0 < mb -> mb mod 4096 = 0 -> 0 < ms <= 2^31 -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  aok34 (AMunmap mb ms) mo.
Proof.
  intros pc pb st mo mb ms [HA HM] Hin Hmb Hal Hms Hml Hce.
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & L0 & HP & HS & HB).
  Local Ltac2 Set LiaHints.tbl := fun () => "0060>15329956303.3321067900100.3334328632197.324411324016.33 44983671738.338648278204.32 00000500:00?00D00I00NS3HalS3HceS3HmsS3HmbS3HmsS3Hml".
assert (ML : mmap_len ms = ms) by (apply mmap_len_id; lia).
  split; [| exact I].
  cbn [AsanNodeSem.aok]. rewrite ML. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  apply map_has_In. eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. right.
  change (Z_to_bv 64 mb, Z_to_bv 64 ms) with (went (mb, ms)). apply in_map. exact Hin.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma live_bytes_perm' : forall l l', Permutation l l' -> live_bytes l = live_bytes l'.
Proof. intros. rewrite !live_bytes_sum_count. apply sum_count_perm. assumption. Qed.
#[using="Type"] Lemma live_bytes_app' : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. intros. apply BackingAlgebra.live_bytes_app. Qed.

#[using="Type"] Lemma INV_grant_aok : forall pc pb st mo n,
  INV pc pb st mo -> 64512 < n <= 2^30 -> zsum2 (CH pc pb st) <= SECM -> zlen (CH pc pb st) <= 16000 ->
  commit_bytes st + sec_map_size n <= CBROOM ->                   (* [comment removed for export] *)
  aok34 (AMmap 0 (sec_map_size n) PROT_RW F_ANON) mo.
Proof.
  intros pc pb st mo n HI Hn HSB HSL HROOM. unfold SECM in HSB.
  pose proof (INV_backing_bound2 _ _ _ _ HI) as HBB.
  pose proof HI as [HA HM]. pose proof (AMI_ivs_wf _ _ _ HM) as Hwf.
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & [[T1 T2] T3] & L0 & HP & HS & HB).
  Local Ltac2 Set LiaHints.tbl := fun () => "00:0>19107843036.3521969064372.3622519483176.3625211184093.3635548252350.3638186290114.3647473518220.3460022630902.3661402543077.366646706282.35 00000100800G00V00a00b00f00m01801?SS2Hn2SBS3HSB5HROOM3HBBS3HSB5HROOM3HBBS3HSL2M42HLSS2HnS2Hn2SBS3HSB2M52HTS2Hn2SB".
pose proof (sec_map_size_bounds n ltac:(lia)) as SB.
  assert (ML : mmap_len (sec_map_size n) = sec_map_size n).
  { apply mmap_len_id; [lia|]. unfold sec_map_size, rup, PG.
    match goal with |- ?x mod 4096 = 0 => replace x with ((((needed_size n + 4096 - 1) / 4096) + 1) * 4096) by lia end.
    apply Z_mod_mult. }
  split. 2:{ cbn [room34]. rewrite ML. split; [| intros EF; exfalso; revert EF; cbv; discriminate]. unfold EAGER0, SECM, CBROOM, RESERVE34, LIMIT34 in *. lia. }
  cbn [AsanNodeSem.aok]. rewrite Z.eqb_refl. rewrite ML. split; [reflexivity|]. split; [lia|]. split; [exact T3|]. split; [reflexivity|]. split.
  - eapply Z.le_trans; [| exact M2]. unfold EAGER0, SECM, CBROOM, RESERVE34, LIMIT34 in *. lia.
  - apply (vm_gap_available_intro_N _ _ (LEN0 + LEN0 + 16000) (2^30 + 2^20) (RTOT0 + TOT0 + 2^35)); [lia| | | |].
    + (* [comment removed for export] *) rewrite T3. unfold ACEIL in T1. rewrite CEIL_val. exact T1.
    + eapply Z.le_trans. { apply inj_le. apply length_filter_le. }
      rewrite length_app, Nat2Z.inj_add. fold (zlen (vm_reserved (m_vmmaps mo))). fold (zlen (vm_maps (m_vmmaps mo))).
      unfold zlen at 2. rewrite (Permutation_length HP). fold (zlen (L0 ++ map went (CH pc pb st))). rewrite zlen_app.
      unfold zlen at 3. rewrite length_map. fold (zlen (CH pc pb st)). destruct HS as (_ & _ & _ & _ & _ & _ & _ & HL & _). lia.
    + rewrite live_bytes_app'. rewrite (live_bytes_perm' _ _ HP).
      rewrite live_bytes_app', (live_bytes_went _ (CH_wf _ _ _ HA)). destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HT & _). lia.
    + rewrite CEIL_val, FLOOR_val. unfold LEN0, RTOT0, TOT0. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma INV_prim : forall pc pb st mo, INV pc pb st mo ->
  exists pb0, In (went (pb0, PRIM_SZ)) (vm_maps (m_vmmaps mo)) /\ pb0 <= a_space_beg st /\ a_space_beg st + 2^37 + 2^12 <= pb0 + PRIM_SZ
              /\ KHIGH <= pb0 /\ pb0 + PRIM_SZ <= ATOP.
Proof.
  intros pc pb st mo [_ HM]. destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L0 & HP & HS & _).
  destruct HS as ((pb0 & Hin & H1 & H2 & H3 & H4) & _). exists pb0. split; [|repeat split; assumption].
  eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. left. exact Hin.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma INV_ptr : forall pc pb st mo, INV pc pb st mo ->
  In (went (a_ptr_array st, PTR_SZ)) (vm_maps (m_vmmaps mo)) /\ a_ptr_array st + PTR_SZ <= ATOP
  /\ region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 (a_ptr_array st)) (Z_to_bv 64 PTR_SZ) = true.
Proof.
  intros pc pb st mo [_ HM]. destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L0 & HP & HS & _).
  destruct HS as (_ & Hin & H1 & H2 & _). split; [|split; assumption].
  eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. left. exact Hin.
Qed.
#[using="Type"] Lemma INV_shadows : forall pc pb st mo, INV pc pb st mo ->
  In (went (LS_LO, LS_SZ)) (vm_maps (m_vmmaps mo)) /\ In (went (GAP_LO, GAP_SZ)) (vm_maps (m_vmmaps mo)) /\ In (went (HS_LO, HS_SZ)) (vm_maps (m_vmmaps mo)).
Proof.
  intros pc pb st mo [_ HM]. destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L0 & HP & HS & _).
  destruct HS as (_ & _ & _ & _ & H1 & H2 & H3 & _).
  repeat split; (eapply Permutation_in; [apply Permutation_sym; exact HP|]; apply in_app_iff; left; assumption).
Qed.

#[using="Type"] Lemma AINV_geom : forall pc pb st, AINV pc pb st -> a_space_beg st mod 65536 = 0 /\ 0 < a_space_beg st /\ a_ptr_array st mod 4096 = 0 /\ 0 < a_ptr_array st.
Proof. intros pc pb st H. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _). auto. Qed.

#[using="Type"] Lemma rup_mod : forall x a, 0 < a -> rup x a mod a = 0.
Proof. intros. unfold rup. apply Z_mod_mult. Qed.
#[using="Type"] Lemma rup_ge' : forall x a, 0 < a -> x <= rup x a. Proof. exact rup_ge. Qed.

#[using="Type"] Lemma is_err_small : forall a, 0 <= a <= TWO64 - 4096 -> is_err a = false.
Proof. intros. unfold is_err. apply Z.ltb_ge. Local Ltac2 Set LiaHints.tbl := fun () => "0010=15515774862.6000003S1H".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".


(* [comment removed for export] *)
#[using="Type"] Lemma mod0_divide : forall x m, 0 < m -> x mod m = 0 -> (m | x).
Proof. intros. apply Z.mod_divide; lia. Qed.
#[using="Type"] Lemma divide_mod0 : forall x m, 0 < m -> (m | x) -> x mod m = 0.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "0010=44347528579.8000003S1H".
apply Z.mod_divide; [lia| assumption]. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma div4096_of_mod : forall x m, (4096 | m) -> 0 < m -> x mod m = 0 -> (4096 | x).
Proof. intros x m Hm Hp Hx. eapply Z.divide_trans; [exact Hm|]. apply mod0_divide; assumption. Qed.
#[using="Type"] Lemma div_65536 : (4096 | 65536). Proof. exists 16. reflexivity. Qed.
#[using="Type"] Lemma div_262144 : (4096 | 262144). Proof. exists 64. reflexivity. Qed.
#[using="Type"] Lemma div_lit : forall k, (4096 | k * 4096). Proof. intros. exists k. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ensure_ok : forall R (P : R -> Model -> Prop) pc pb st c nf (k : astate -> bool -> AM R) mo,
  INV pc pb st mo -> 1 <= c <= 31 -> 0 <= nf ->
  4 * nf + K_FREEARR_MAP <= K_FREEARR_MAX ->
  zsum2 (CH pc pb st) <= SECM ->
  FAINV st -> VC st <= VCMAX -> 32 * nf <= c_mapped_user (get_cls st c) ->     (* [comment removed for export] *)
  a_space_beg st = SBc /\ a_ptr_array st = PAc ->                         (* [comment removed for export] *)
  (forall st' mo', INV pc pb st' mo' -> same_but c st st' ->
     c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
     c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
     c_num_freed (get_cls st' c) = c_num_freed (get_cls st c) ->
     c_count (get_cls st' c) = c_count (get_cls st c) ->
     nf * 4 <= c_mapped_free_array (get_cls st' c) ->
     FAINV st' -> VC st' = VC st ->                                       (* [comment removed for export] *)
     atot (k st' true) mo' P) ->
  atot (ensure_free_array st c nf k) mo P.
Proof.
  intros R P pc pb st c nf k mo HI Hc Hnf Hroom HSB HFA HVC Hcarved [HSB0 HPA0] Hk.
  pose proof (HFA c Hc) as [[FA0 FA1] FA2]. pose proof VCMAX_CBROOM as (HVX1 & HVX2 & HVX3).
  pose proof HI as [HA HM]. pose proof (AINV_cls _ _ _ _ HA Hc) as HC.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  destruct (AINV_geom _ _ _ HA) as (G1 & G2 & G3 & G4).
  destruct (INV_prim _ _ _ _ HI) as (pb0 & HinP & P1 & P2 & P3 & P4).
  unfold ensure_free_array. cbv zeta.
  destruct (Z.leb_spec (nf * 4) (c_mapped_free_array (get_cls st c))) as [Hle|Hgt].
  { apply (Hk st mo HI (same_but_refl c st)); auto. }
  Local Ltac2 Set LiaHints.tbl := fun () => "00d0>11020495281.8114612672018.7615656914361.8118758896604.8118771565226.8018926559612.6718926759409.6818926759786.5618928485036.5918941239406.6618941241597.6518941438064.6418941438118.5820747562570.6923048041013.6823816479106.8124327237963.8228333390557.8028710283280.7828796538237.1131115717610.8033156016402.8134758882852.6138014520046.793826547316.79 42468566582.6942983857264.7243942243845.7149352206568.8150099302702.8150656892572.5 52194364407.8152489881114.8152490400959.7555256198613.7256921541626.8158075715624.8159579067184.7261003989902.816268212727.4  63368578604.8363643767052.8466215796179.8167232910279.8167232956754.7967324217557.7567777338572.8168277421931.7968277472766.8168388327544.697268758710.70 9137851601.63 00000400500900?00E00F00G00H00I00J00K00L00M00Q00R00V00^00c01B01W02402802G02H02P02Q02\02n03203703@03E03O03T03U03Y03i03j03k04004104704804U04b05305705@05I05M05Y05mS2C5SS2R1S4HlenS4HlenSSSSSSSSS2HcSS2C3S2P33HE1S3HlmS3HVC3FA03FA24HVX12G22G44Hlen1XS3HVC4Hnf82R22CG4HresS3AT22P32P44Hlen3HE13HE24HanzS2R3S5Hroom2R24HbigFS2P33HE1SS3AT22P32P4S5Hroom2P22R24Hc32S2C2S3HokS7HcarvedS3C10S2C12C82C9S3FA2SS2C4S2C63Hgt2R14HlenSFS3FA0SS2X21HSS2G22P24Hlen3HE23HB13HS14HanzS3HE23HB13HS1S2C64Hnf82R24HlenS2C9S3HE13HB1S3HE13HB1S2HcS2C62P14Hc32S5Hroom2C63Hgt2R12R2".
pose proof (rup_ge (nf * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia)) as R1.
  assert (Hnf8 : nf * 4 <= c_mapped_user (get_cls st c) / 8) by (clear -Hcarved Hnf; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  pose proof (rup_le (nf * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia)) as R2.
  pose proof (rup_mod (nf * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia)) as R3.
  destruct (Z.ltb_spec K_FREEARR_MAX (rup (nf * 4) K_FREEARR_MAP)) as [Hbig|Hok]; [lia|].
  set (len := rup (nf * 4) K_FREEARR_MAP - c_mapped_free_array (get_cls st c)).
  set (a := region_beg st c + K_FREEARR_OFF + c_mapped_free_array (get_cls st c)).
  assert (Hlen : 0 < len <= 2^30) by (unfold len, K_FREEARR_MAX in *; lia).
  assert (Dmfa : (4096 | c_mapped_free_array (get_cls st c))) by (apply (div4096_of_mod _ 262144); [apply div_262144| lia| unfold K_FREEARR_MAP in C7; exact C7]).
  assert (Drup : (4096 | rup (nf * 4) K_FREEARR_MAP)) by (apply (div4096_of_mod _ 262144); [apply div_262144| lia| unfold K_FREEARR_MAP in *; exact R3]).
  assert (Dsb : (4096 | a_space_beg st)) by (apply (div4096_of_mod _ 65536); [apply div_65536| lia| exact G1]).
  assert (Hlm : len mod 4096 = 0).
  { apply divide_mod0; [lia|]. unfold len. apply Z.divide_sub_r; assumption. }
  assert (Ham : a mod 4096 = 0).
  { apply divide_mod0; [lia|]. unfold a, region_beg, K_REGION, K_FREEARR_OFF.
    apply Z.divide_add_r; [|exact Dmfa]. apply Z.divide_add_r; [| exists 917504; reflexivity].
    apply Z.divide_add_r; [exact Dsb|]. replace (c * 2 ^ 32) with ((c * 2^20) * 4096) by lia. apply div_lit. }
  assert (Hc32 : 0 <= c * 2^32 <= 31 * 2^32) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
  assert (HE1 : pb0 <= a) by (unfold a, region_beg, K_REGION, K_FREEARR_OFF; lia).
  assert (HE2 : a + len <= pb0 + PRIM_SZ).
  { unfold a, len, region_beg, K_REGION, K_FREEARR_OFF, K_FREEARR_MAX, PRIM_SZ in *. lia. }
  assert (HBS : B (went (pb0, PRIM_SZ)) = pb0 /\ S (went (pb0, PRIM_SZ)) = PRIM_SZ).
  { unfold B, S, went. cbn [fst snd]. unfold ACEIL, PRIM_SZ, KHIGH in *. rewrite !unsigned_lit by lia. lia. }
  destruct HBS as [HB1 HS1].
  pose (r' := cls_set_mapped_free_array (rup (nf * 4) K_FREEARR_MAP) (get_cls st c)).
  assert (HFA' : FAINV (put_cls c r' st)).
  { apply FAINV_put; [exact Hc| exact HFA| |]; unfold r'; cbn [c_mapped_free_array c_mapped_user cls_set_mapped_free_array]; unfold K_FREEARR_MAP in *; lia. }
  assert (HVC' : VC (put_cls c r' st) = VC st) by (rewrite VC_put by exact Hc; unfold r', vc_cls; cbn [c_mapped_user cls_set_mapped_free_array]; lia).
  assert (HlenF : commit_bytes st + len <= CBROOM).
  { pose proof (commit_le_VC _ HFA') as X. rewrite commit_bytes_put in X by exact Hc. rewrite HVC' in X.
    unfold r', cls_mapped_bytes' in X. cbn [c_mapped_user c_mapped_free_array cls_set_mapped_free_array] in X. unfold len. lia. }
  (* [comment removed for export] *)
  assert (HW : inW SBc PAc a len).
  { left. exists c. split; [exact Hc|]. right.
    pose proof (csum_ge_cls vc_cls st c Hc ltac:(intros c' Hc'; pose proof (HFA c' Hc') as [[X0 X1] X2]; unfold vc_cls; pose proof (Z.div_pos _ 8 X2 ltac:(lia)); unfold K_FREEARR_MAP; lia)) as CG.
    pose proof HA as (_ & _ & _ & _ & _ & _ & Hres & _). unfold K_CHUNKS_BLOCK in Hres.
    unfold a, len, region_beg. rewrite HSB0.
    unfold VC, vc_cls in HVC, CG. unfold VCMAX, VC0, NOPS, FWIN, K_FREEARR_MAP in HVC, CG, R2 |- *.
    split; [clear -FA0; lia|]. clear -Hnf8 HVC CG Hres R2 FA0 Hgt. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  unfold ev. apply atotal_vis.
  - apply (INV_fixed_aok_high pc pb st mo (went (pb0, PRIM_SZ))); auto; try lia. unfold RES_HI, KHIGH in *. lia.
  - intros z mo' Hpost. cbn [apost] in Hpost.
    assert (Hanz : (a =? 0) = false) by (apply Z.eqb_neq; unfold KHIGH in *; lia).
    rewrite Hanz in Hpost. destruct Hpost as [-> ->].
    rewrite fixed_answer_ok_self. cbn [negb].
    rewrite is_err_small by (unfold TWO64, ACEIL, KHIGH, PRIM_SZ in *; lia).
    assert (ML : mmap_len len = len) by (apply mmap_len_id; lia). rewrite ML.
    apply Hk.
    + split.
      * apply AINV_put_cls; [exact HA| exact Hc|]. unfold CLSOK. cbn [c_allocated_user c_mapped_user c_mapped_free_array c_num_freed c_count cls_set_mapped_free_array].
        unfold K_FREEARR_MAP in *. repeat split; try lia.
      * rewrite CH_put. apply (AMI_commit _ st _ _ (went (pb0, PRIM_SZ))); auto; try lia; try reflexivity.
        rewrite commit_bytes_put by exact Hc. unfold cls_mapped_bytes'. cbn [c_mapped_user c_mapped_free_array cls_set_mapped_free_array]. unfold len. lia.
    + apply same_but_put.
    + rewrite get_put_eq. reflexivity.
    + rewrite get_put_eq. reflexivity.
    + rewrite get_put_eq. reflexivity.
    + rewrite get_put_eq. reflexivity.
    + rewrite get_put_eq. cbn [c_mapped_free_array cls_set_mapped_free_array]. lia.
    + exact HFA'.
    + unfold r' in HVC'. exact HVC'.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Local Ltac cproj := cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count
                         cls_set_allocated_user cls_set_num_freed cls_set_mapped_free_array cls_set_mapped_user cls_set_count negb].

(* [comment removed for export] *)
#[using="Type"] Lemma populate_ok : forall R (P : R -> Model -> Prop) pc pb st c req (k : astate -> bool -> AM R) mo,
  INV pc pb st mo -> 1 <= c <= 31 -> 32 <= size_of_class c <= 65536 -> 0 < req -> req * size_of_class c <= K_USER_MAP ->
  c_allocated_user (get_cls st c) + 2^20 <= K_FREEARR_OFF ->
  zsum2 (CH pc pb st) <= SECM ->
  FAINV st -> VC st + 2^19 <= VCMAX ->                                  (* [comment removed for export] *)
  a_space_beg st = SBc /\ a_ptr_array st = PAc ->                         (* [comment removed for export] *)
  (forall st' mo', INV pc pb st' mo' -> same_but c st st' ->
     c_count (get_cls st' c) = c_count (get_cls st c) ->
     c_num_freed (get_cls st c) + req <= c_num_freed (get_cls st' c) ->
     FAINV st' -> VC st' <= VC st + 2^19 ->                               (* [comment removed for export] *)
     atot (k st' true) mo' P) ->
  atot (populate_free_array st c req k) mo P.
Proof.
  intros R P pc pb st c req k mo HI Hc Hsz Hreq Hrs Hroom HSB HFA HVC [HSB0 HPA0] Hk.
  pose proof (HFA c Hc) as [[FA0 FA1] FA2]. pose proof (commit_le_VC _ HFA) as HCV. pose proof VCMAX_CBROOM as (HVX1 & HVX2 & HVX3).
  pose proof HI as [HA HM]. pose proof (AINV_cls _ _ _ _ HA Hc) as HC.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  destruct (AINV_geom _ _ _ HA) as (G1 & G2 & G3 & G4).
  destruct (INV_prim _ _ _ _ HI) as (pb0 & HinP & P1 & P2 & P3 & P4).
  remember (size_of_class c) as size eqn:Hsize.
  (* [comment removed for export] *)
  assert (TAIL : forall st1 mo1,
    INV pc pb st1 mo1 -> same_but c st st1 -> c_count (get_cls st1 c) = c_count (get_cls st c) -> c_num_freed (get_cls st1 c) = c_num_freed (get_cls st c) ->
    c_allocated_user (get_cls st1 c) = c_allocated_user (get_cls st c) ->
    c_allocated_user (get_cls st c) + req * size <= c_mapped_user (get_cls st1 c) -> zsum2 (CH pc pb st1) <= SECM ->
    FAINV st1 -> VC st1 <= VC st + 2^19 ->
    atot (let r1 := get_cls st1 c in
          let new_cnt := (c_mapped_user r1 - c_allocated_user r1) / size in
          let total_freed := c_num_freed r1 + new_cnt in
          ensure_free_array st1 c total_freed (fun st2 ok =>
            if negb ok then k st2 false else
            k (put_cls c (cls_set_allocated_user (c_allocated_user (get_cls st2 c) + new_cnt * size) (cls_set_num_freed total_freed (get_cls st2 c))) st2) true)) mo1 P).
  { intros st1 mo1 HI1 HSB1 Hcnt1 Hnf1 Hal1 Hen1 HSB2 HFA1 HVC1. cbv zeta.
    pose proof HI1 as [HA1 HM1]. pose proof (AINV_cls _ _ _ _ HA1 Hc) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10). rewrite <- Hsize in D10.
    Local Ltac2 Set LiaHints.tbl := fun () => "01H0?10505834565.85 10779800640.92 11021645198.76 11642265061.68 12097305485.76 12123263146.11112154260023.9  12512718907.61 13520091660.73 1360772030.118 1362639805.90  1362639805.92  1373111101.93  14612841004.11816552207075.10816556287065.79 17009567016.10817974216545.85 17974592421.89 17978731813.82 17978787427.91 18926559612.66 18926562409.67 18941428012.65 18941438574.61 2046366968.90  2046366968.92  20752166470.64 22002929394.73 22120480663.89 22124673617.91 22838298031.76 23048106925.67 23819271613.76 24327237963.76 2591163542.4   29142838618.89 29551403532.69 29952099896.11130118906781.11830912565273.82 31115717610.74 32267100381.78 33159066925.76 3499453841.108 35717397626.78 38014520046.73 3826547316.73  40165922261.63 42464749114.64 42983857264.70 44426309457.11844593437643.85 45324012092.91 47428125589.91 48982438153.76 49921749401.11850085544763.73 51315834423.76 52487919909.78 52488280613.76 53435715958.73 53438220252.76 53745173806.78 53745534510.76 55256198613.70 57680026763.2  57680241216.78 59088369762.76 59579067184.70 59815762754.61 63368578604.77 63370208813.78 63392349154.90 63392349154.92 63643767052.78 64453457451.73 66712510475.90 66779871364.76 67259060466.90 67620280735.89 67779395827.76 68206413930.76 68275409345.76 68277421931.73 68384542836.64 8575035729.5   909199213.85   00000;00?00C00N00O00S00`00m01I01P01`01g01n02302>02A02N02S02X02]02b02c02d02e02f02m03403803903C03M03N03O03S03[03e03f04>04E04T04X05005105S05T05l05m06506I06J06U06Y06]06a06f06g07607707X07]07k08808E08F08J08K08L08T08Y08Z08[08\08]08b08g08m08n09509:09@09C09G09Q09Z09c09g09n0:4S4Hal14Hen1S2H1S2C7S2Hc3FA22P1FS2X2S3HVC2CG4HresS3Hrs2C24HmapS3HVC3FA03FA23HCV4HVX12G22G4S2Q02F8S4Hreq2D86HcarveS2D82Q0S2D82Q0S3QcvS4HVC14HVC2S1HS4Hnf16HcarveS3HszS3HszS3HszS3HszSSSSS3Qcv1HS3Qcv1HS2HcFS2D95Hcnt0S2D95Hcnt0FSS2C6S2P33HE1S3HVC4HVC1SS3Hrs5Hroom2P24Hmap4Hc32S2X02X1S3Hsz2Q03Hcv2F1S2D2S3AT22P32P43HE13HE24HanzSS3FA03FA22C52C72G22G43Dsb3Dmu4HanzSS3Hsz4Hreq3Hrs3FA22C12C2FS2P33HE1S3Hrs5Hroom4Hmap3HexSS3AT22P32P4S2D3S2D1S2H2S3HcvSS3Hsz2Q03Hcv2F4SS3Hsz4Hreq3Hrs3FA03FA22G22G44HanzS3FA0S2C13FA02C82C9S3HE23HB13HS1S3HE23HB13HS1SS2C2SSS3Hrs2C2S3C10SSSSS3HszS3HszS2X21HFS2D32H1S3HokS1H2H0S1HS2C9S3Hrs4HmapS3HE13HB1S3HE13HB1S2HcS2C12C2S4Hreq".
pose proof (carve_facts (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) size ltac:(lia) ltac:(lia)) as (Q0 & Qcv & Qrest).
    pose proof (carve_enough_nomap (c_mapped_user (get_cls st1 c)) (c_allocated_user (get_cls st1 c)) size req ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hcarve.
    set (q := (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) / size) in *. set (cv := q * size) in *.
    assert (Hcnt0 : 0 <= cntP c (all_chunks pc pb st1) + nbatch c (qbatches pb st1)).
    { pose proof (cntP_nonneg c (all_chunks pc pb st1)). unfold nbatch. destruct (c =? K_BATCH_CLASS); [pose proof (zlen_nonneg (qbatches pb st1))|]; lia. }
    (* [comment removed for export] *)
    assert (Hnf' : 4 * (c_num_freed (get_cls st1 c) + q) + K_FREEARR_MAP <= K_FREEARR_MAX).
    { assert (H1 : size * (c_num_freed (get_cls st1 c) + q) <= c_mapped_user (get_cls st1 c)).
      { rewrite Z.mul_add_distr_l. replace (size * q) with cv by (unfold cv; lia).
        assert (size * c_num_freed (get_cls st1 c) <= c_allocated_user (get_cls st1 c)); [|lia].
        rewrite D10. apply Z.mul_le_mono_nonneg_l; lia. }
      assert (H2 : 32 * (c_num_freed (get_cls st1 c) + q) <= K_FREEARR_OFF).
      { apply Z.le_trans with (size * (c_num_freed (get_cls st1 c) + q)); [apply Z.mul_le_mono_nonneg_r; lia| lia]. }
      unfold K_FREEARR_OFF, K_FREEARR_MAP, K_FREEARR_MAX in *. lia. }
    assert (Hcv : cv = q * size) by reflexivity. clearbody cv q.
    assert (Hcarved : 32 * (c_num_freed (get_cls st1 c) + q) <= c_mapped_user (get_cls st1 c)).
    { assert (H1 : size * (c_num_freed (get_cls st1 c) + q) <= c_mapped_user (get_cls st1 c)).
      { rewrite Z.mul_add_distr_l. replace (size * q) with cv by lia.
        assert (size * c_num_freed (get_cls st1 c) <= c_allocated_user (get_cls st1 c)); [|lia].
        rewrite D10. apply Z.mul_le_mono_nonneg_l; lia. }
      apply Z.le_trans with (size * (c_num_freed (get_cls st1 c) + q)); [apply Z.mul_le_mono_nonneg_r; lia| lia]. }
    assert (HSBP1 : a_space_beg st1 = SBc /\ a_ptr_array st1 = PAc) by (destruct HSB1 as (Es & Ep & _); rewrite Es, Ep; split; assumption).
    apply (ensure_ok R P pc pb st1 c (c_num_freed (get_cls st1 c) + q) _ mo1 HI1 Hc ltac:(lia) Hnf' HSB2 HFA1 ltac:(clear -HVC HVC1; lia) Hcarved HSBP1).
    intros st2 mo2 HI2 HSB12 E1 E2 E3 E4 E5 HFA2 HVC2. cproj.
    pose proof HI2 as [HA2 HM2].
    assert (AC : all_chunks pc pb st2 = all_chunks pc pb st1 /\ qbatches pb st2 = qbatches pb st1).
    { destruct HSB12 as (_&_&_&_&_&Hl&_&Hq1&_&Hq2&_&_). unfold all_chunks, qbatches, live_chunks. rewrite Hl, Hq1, Hq2. split; reflexivity. }
    destruct AC as [AC1 AC2].
    apply Hk.
    - split.
      + apply AINV_put_cls; [exact HA2| exact Hc|].
        pose proof (AINV_cls _ _ _ _ HA2 Hc) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
        unfold CLSOK. cproj. rewrite <- Hsize. rewrite AC1, AC2. rewrite E1, E2, E3, E4 in *.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact D5|]. split; [exact F6|]. split; [exact F7|].
        split; [lia|]. split; [exact F9|]. rewrite <- Hsize in F10. rewrite AC1, AC2 in F10. rewrite F10, Hcv. ring.
      + rewrite CH_put. apply (AMI_mono _ st2); auto. rewrite commit_bytes_put by exact Hc. unfold cls_mapped_bytes'. cproj. lia.
    - eapply same_but_trans; [exact HSB1|]. eapply same_but_trans; [exact HSB12| apply same_but_put].
    - rewrite get_put_eq. cproj. congruence.
    - rewrite get_put_eq. cproj. lia.
    - apply FAINV_put; [exact Hc| exact HFA2| |]; cproj; pose proof (HFA2 c Hc) as [[X0 X1] X2]; lia.
    - rewrite VC_put by exact Hc. unfold vc_cls. cproj. lia. }
  unfold populate_free_array. rewrite <- Hsize. cbv zeta.
  destruct (Z.leb_spec (c_allocated_user (get_cls st c) + req * size) (c_mapped_user (get_cls st c))) as [Hen|Hmap].
  { apply (TAIL st mo HI (same_but_refl c st)); auto. lia. }
  (* [comment removed for export] *)
  assert (Hums : rup (c_allocated_user (get_cls st c) + req * size - c_mapped_user (get_cls st c)) K_USER_MAP = K_USER_MAP).
  { apply rup_small; unfold K_USER_MAP in *; lia. }
  rewrite Hums.
  destruct (Z.ltb_spec K_FREEARR_OFF (c_mapped_user (get_cls st c) + K_USER_MAP)) as [Hex|Hok]; [unfold K_USER_MAP, K_FREEARR_OFF in *; lia|].
  set (a := region_beg st c + c_mapped_user (get_cls st c)).
  assert (Hc32 : 0 <= c * 2^32 <= 31 * 2^32) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
  assert (Dsb : (4096 | a_space_beg st)) by (apply (div4096_of_mod _ 65536); [apply div_65536| lia| exact G1]).
  assert (Dmu : (4096 | c_mapped_user (get_cls st c))) by (apply (div4096_of_mod _ 262144); [apply div_262144| lia| unfold K_USER_MAP in C5; exact C5]).
  assert (Ham : a mod 4096 = 0).
  { apply divide_mod0; [lia|]. unfold a, region_beg, K_REGION. apply Z.divide_add_r; [|exact Dmu]. apply Z.divide_add_r; [exact Dsb|].
    replace (c * 2 ^ 32) with ((c * 2^20) * 4096) by lia. apply div_lit. }
  assert (HE1 : pb0 <= a) by (unfold a, region_beg, K_REGION; lia).
  assert (HE2 : a + K_USER_MAP <= pb0 + PRIM_SZ) by (unfold a, region_beg, K_REGION, K_FREEARR_OFF, K_USER_MAP, PRIM_SZ in *; lia).
  assert (HBS : B (went (pb0, PRIM_SZ)) = pb0 /\ S (went (pb0, PRIM_SZ)) = PRIM_SZ).
  { unfold B, S, went. cbn [fst snd]. unfold ACEIL, PRIM_SZ, KHIGH in *. rewrite !unsigned_lit by lia. lia. }
  destruct HBS as [HB1 HS1].
  (* [comment removed for export] *)
  assert (HW : inW SBc PAc a K_USER_MAP).
  { left. exists c. split; [exact Hc|]. left.
    pose proof (csum_ge_cls vc_cls st c Hc ltac:(intros c' Hc'; pose proof (HFA c' Hc') as [[X0 X1] X2]; unfold vc_cls; pose proof (Z.div_pos _ 8 X2 ltac:(lia)); unfold K_FREEARR_MAP; lia)) as CG.
    pose proof HA as (_ & _ & _ & _ & _ & _ & Hres & _). unfold K_CHUNKS_BLOCK in Hres.
    unfold a, region_beg. rewrite HSB0.
    unfold VC, vc_cls in HVC, CG. unfold UWIN, VCMAX, VC0, NOPS, K_FREEARR_MAP, K_USER_MAP in HVC, CG |- *.
    split; [clear -C1 C2; lia|]. clear -C1 C2 HVC CG Hres FA0. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  unfold ev. apply atotal_vis.
  - apply (INV_fixed_aok_high pc pb st mo (went (pb0, PRIM_SZ))); auto; try lia; first [unfold RES_HI, KHIGH in *; lia| unfold K_USER_MAP in *; lia].
  - intros z mo' Hpost. cbn [apost] in Hpost.
    assert (Hanz : (a =? 0) = false) by (apply Z.eqb_neq; unfold KHIGH in *; lia).
    rewrite Hanz in Hpost. destruct Hpost as [-> ->].
    rewrite fixed_answer_ok_self. cbn [negb].
    rewrite is_err_small by (unfold TWO64, ACEIL, KHIGH, PRIM_SZ, K_USER_MAP in *; lia).
    assert (ML : mmap_len K_USER_MAP = K_USER_MAP) by reflexivity. rewrite ML.
    set (st1 := put_cls c (cls_set_mapped_user (c_mapped_user (get_cls st c) + K_USER_MAP) (get_cls st c)) st).
    assert (HI1 : INV pc pb st1 (fixed_model mo F_FIXED a K_USER_MAP)).
    { split.
      + apply AINV_put_cls; [exact HA| exact Hc|]. unfold CLSOK. cproj. rewrite <- Hsize. repeat split; try (unfold K_USER_MAP in *; lia).
        all: unfold K_USER_MAP in *; rewrite <- Zplus_mod_idemp_l, C5; reflexivity.
      + unfold st1. rewrite CH_put. apply (AMI_commit _ st _ _ (went (pb0, PRIM_SZ))); auto; try lia; try reflexivity.
        all: try (unfold K_USER_MAP; lia).
        all: rewrite commit_bytes_put by exact Hc; unfold cls_mapped_bytes'; cproj; unfold K_USER_MAP; lia. }
    assert (Er1 : get_cls st1 c = cls_set_mapped_user (c_mapped_user (get_cls st c) + K_USER_MAP) (get_cls st c)) by (unfold st1; apply get_put_eq).
    apply (TAIL st1 (fixed_model mo F_FIXED a K_USER_MAP) HI1); try (rewrite Er1; cproj; lia).
    + unfold st1. apply same_but_put.
    + unfold st1. rewrite CH_put. exact HSB.
    + unfold st1. apply FAINV_put; [exact Hc| exact HFA| |]; cproj; [| lia].
      split; [lia|]. eapply Z.le_trans; [exact FA1|]. apply Z.add_le_mono_r. apply Z.div_le_mono; unfold K_USER_MAP; lia.
    + unfold st1. rewrite VC_put by exact Hc. unfold vc_cls. cproj. unfold K_USER_MAP.
      assert ((c_mapped_user (get_cls st c) + 262144) / 8 = c_mapped_user (get_cls st c) / 8 + 32768) by (clear; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma max_count_same_but : forall c st1 st2 c', same_but c st1 st2 -> max_count st2 c' = max_count st1 c'.
Proof. intros c st1 st2 c' H. destruct H as (_&_&_&_&Hci&_). unfold max_count. rewrite Hci. reflexivity. Qed.

#[using="Type"] Lemma all_chunks_cons : forall ch pc pb st, all_chunks (ch :: pc) pb st = ch :: all_chunks pc pb st. Proof. reflexivity. Qed.
#[using="Type"] Lemma qbatches_cons : forall b pb st, qbatches (b :: pb) st = b :: qbatches pb st. Proof. reflexivity. Qed.
#[using="Type"] Lemma CH_cons : forall ch pc pb st, CH (ch :: pc) pb st = sec_of ch ++ CH pc pb st. Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma CH_repc : forall pc pc' pb st, secs pc' = secs pc -> CH pc' pb st = CH pc pb st.
Proof. intros. unfold CH, all_chunks. rewrite !secs_app, H. reflexivity. Qed.

#[using="Type"] Lemma AINV_repc : forall pc pc' pb st c r',
  AINV pc pb st -> 1 <= c <= 31 ->
  Forall chunk_wf pc' ->
  (forall c', 1 <= c' <= 31 -> c' <> c -> cntP c' pc' = cntP c' pc) -> secs pc' = secs pc ->
  CLSOK pc' pb st c r' -> AINV pc' pb (put_cls c r' st).
Proof.
  intros pc pc' pb st c r' H Hc Hwf Hcnt Hsec HR. unfold AINV in *.
  destruct H as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array put_cls set_cls] in *.
  rewrite (CH_put pc' pb c r' st), (CH_repc pc pc' pb st Hsec).
  split.
  { intros c' Hc'. unfold cls_inv. rewrite max_count_put, all_chunks_put, qbatches_put.
    destruct (Z.eq_dec c' c) as [->|Hne].
    - rewrite get_put_eq. exact HR.
    - rewrite get_put_ne by congruence. pose proof (HC c' Hc') as X. unfold cls_inv in X.
      unfold all_chunks in *. rewrite !cntP_app in *. rewrite (Hcnt c' Hc' Hne). exact X. }
  split.
  { rewrite all_chunks_put. unfold all_chunks in *. apply Forall_app in H2 as [_ H2]. apply Forall_app. split; assumption. }
  rewrite qbatches_put. repeat (split; [assumption|]). assumption.
Qed.

#[using="Type"] Lemma INV_repc : forall pc pc' pb st c r' mo,
  INV pc pb st mo -> 1 <= c <= 31 ->
  Forall chunk_wf pc' ->
  (forall c', 1 <= c' <= 31 -> c' <> c -> cntP c' pc' = cntP c' pc) -> secs pc' = secs pc ->
  CLSOK pc' pb st c r' -> cls_mapped_bytes' (get_cls st c) <= cls_mapped_bytes' r' ->
  INV pc' pb (put_cls c r' st) mo.
Proof.
  intros pc pc' pb st c r' mo [HA HM] Hc Hwf Hcnt Hsec HR Hmono. split.
  - apply AINV_repc with (pc := pc); assumption.
  - rewrite CH_put, (CH_repc pc pc' pb st Hsec). apply (AMI_mono _ st); auto. rewrite commit_bytes_put by exact Hc. Local Ltac2 Set LiaHints.tbl := fun () => "0010>28762277056.19000007S5Hmono".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma AINV_init_cache : forall pc pb st, AINV pc pb st -> AINV pc pb (init_cache st).
Proof.
  intros pc pb st H. unfold init_cache. destruct (a_cinit st) eqn:E; [exact H|].
  unfold AINV in *. destruct H as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array set_cinit a_cinit] in *.
  split; [| repeat (split; [assumption|]); assumption].
  intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. unfold max_count in *. cbn [a_cinit set_cinit] in *. rewrite E in X.
  unfold get_cls in *. cbn [a_cls set_cinit] in *.
  unfold all_chunks, qbatches, live_chunks in *. cbn [a_live a_qloc a_qglob set_cinit] in *.
  Local Ltac2 Set LiaHints.tbl := fun () => "0030>15043293738.2038413893372.2039057523418.21000001002007SSS1X1H".
pose proof (primary_class_facts 0 ltac:(lia) eq_refl) as _.
  assert (0 <= max_cached c) by (unfold max_cached; lia). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma INV_init_cache : forall pc pb st mo, INV pc pb st mo -> INV pc pb (init_cache st) mo.
Proof.
  intros pc pb st mo [HA HM]. split; [apply AINV_init_cache; exact HA|].
  rewrite CH_init_cache. apply (AMI_mono _ st); auto.
  - unfold init_cache; destruct (a_cinit st); reflexivity.
  - unfold init_cache; destruct (a_cinit st); reflexivity.
  - rewrite commit_bytes_init_cache. Local Ltac2 Set LiaHints.tbl := fun () => "0010<131755091.10000001S".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma same_but_init_cache : forall c st, same_but c (init_cache st) st \/ True. Proof. intros. right. exact I. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cache_alloc_ok : forall R (P : R -> Model -> Prop) pc pb st c n (k : astate -> bool -> AM R) mo,
  INV pc pb st mo -> 0 <= n -> is_primary n = true -> c = class_id (needed_size n) ->
  size_of_class c * (cntP c (all_chunks pc pb st) + nbatch c (qbatches pb st) + 8) + 2^20 <= K_FREEARR_OFF ->
  zsum2 (CH pc pb st) <= SECM ->
  FAINV st -> VC st + 2^19 <= VCMAX ->                                  (* [comment removed for export] *)
  a_space_beg st = SBc /\ a_ptr_array st = PAc ->                         (* [comment removed for export] *)
  (forall st' mo', INV (CPrim c n :: pc) pb st' mo' -> (same_but c st st' \/ same_but c (init_cache st) st') ->
     FAINV st' -> VC st' <= VC st + 2^19 ->                               (* [comment removed for export] *)
     atot (k st' true) mo' P) ->
  atot (cache_alloc st c k) mo P.
Proof.
  intros R P pc pb st c n k mo HI Hn Hp Hcl Hroom HSB HFA HVC HSBP Hk.
  pose proof (primary_class_facts n Hn Hp) as F. cbv zeta in F. rewrite <- Hcl in F. destruct F as (F1 & F2 & F3 & F4 & F5 & F6).
  Local Ltac2 Set LiaHints.tbl := fun () => "00i0>11007833928.5011008937556.7711013015790.5511018316725.5511022396687.7711150147091.5511441570271.7712123263146.8012125481770.7715047100290.4716550000804.5016552207075.7716556287065.5517335321746.7718282679257.5518286759267.7719325000345.5423812374395.5023822852998.552427052486.34 25456238144.5026150867738.5526154948000.772752579220.50 29950278402.5529952099896.8029956564991.5031430507630.5831430507630.8032215297534.7733564258739.5438039080066.6341415984900.5045183276031.5448099046125.2949348064785.5049358547692.5552200704499.5552206998798.5052470929832.5452485773539.5052492059678.5553839682712.5554239174649.5854239174649.8054609482672.5056262690272.5456802589952.5056908879107.5056919362046.5556923705156.7760722348050.7760728793685.5065348543218.5066099141931.556720987780.35 9733684111.54 00000700>00E00L00S00T00g00k01201301401:01;01?01I01S01W01^01e01i01j01o02402802A02H02Q02R02S02Z02^02e02f02j02n03203603D03I03N03]03i04004F04h04l05:05>05B05F05J05K05L05R05Y05a05eS2C52C7S5HhalfS5HhalfS2C52C7S2D52D7FS2F32C92Hz4Ecnt3D10S2X2S2D12D6SSS4HVC2SS2D2S2F45HhalfS2F45HhalfS2F3S2C32C6S2C32C6S2HnFS3HenS3EnfS2F4S3FA03FA1S2D62X1S3FA03FA1SSS2D32D6S2C8S3Enf1HSS2F3S2F1S2C2S2C2S2F32C93C102HzS3C10S3HltS3FA22C13FA02C8S3FA22C13FA0S2C92HzS2F43FA03FA22C52C73HneS2F32F53FA03FA25Hhalf2D52D62D73HneS2C9S2F45Hhalf3HltS2F4S2C4S2C4S2D4SSS4HposS3Hen1HS3FA22n0S2F5".
assert (Hc : 1 <= c <= 31) by lia.
  pose proof (HFA c Hc) as [[FA0 FA1] FA2]. pose proof (commit_le_VC _ HFA) as HCV.
  assert (Hwf : chunk_wf (CPrim c n)).
  { cbn. split; [|exact Hcl]. split; [lia|]. destruct (Z_lt_dec 64512 n) as [Hlt|]; [|lia]. rewrite (large_not_primary n Hlt) in Hp. discriminate. }
  pose proof HI as [HA HM]. pose proof (AINV_cls _ _ _ _ HA Hc) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  assert (Hcnt0 : 0 <= cntP c (all_chunks pc pb st) /\ 0 <= nbatch c (qbatches pb st)).
  { split; [apply cntP_nonneg|]. unfold nbatch. destruct (c =? K_BATCH_CLASS); [apply zlen_nonneg| lia]. }
  assert (REPC : forall st0 r', INV pc pb st0 mo -> all_chunks pc pb st0 = all_chunks pc pb st -> qbatches pb st0 = qbatches pb st ->
            CLSOK (CPrim c n :: pc) pb st0 c r' -> cls_mapped_bytes' (get_cls st0 c) <= cls_mapped_bytes' r' ->
            INV (CPrim c n :: pc) pb (put_cls c r' st0) mo).
  { intros st0 r' HI0 E1 E2 HR Hm. apply (INV_repc pc); auto.
    - constructor; [exact Hwf|]. destruct HA as (_ & Hall & _). unfold all_chunks in Hall. apply Forall_app in Hall as [Hpc _]. exact Hpc.
    - intros c' Hc' Hne. rewrite cntP_cons. cbn [is_prim_of]. replace (c =? c') with false by (symmetry; apply Z.eqb_neq; lia). lia. }
  unfold cache_alloc. cbv zeta.
  destruct (Z.ltb_spec 0 (c_count (get_cls st c))) as [Hpos|Hz].
  - (* [comment removed for export] *)
    apply Hk; [|left; apply same_but_put| apply FAINV_put; [exact Hc| exact HFA| cproj; lia| cproj; lia] | rewrite VC_put by exact Hc; unfold vc_cls; cproj; lia].
    apply REPC; auto. all: try (unfold cls_mapped_bytes'; cproj; lia).
    unfold CLSOK. cproj. rewrite all_chunks_cons, cntP_cons. cbn [is_prim_of]. rewrite Z.eqb_refl. repeat split; try lia.
  - rewrite max_count_init_cache, get_cls_init_cache.
    assert (Hhalf : 1 <= max_cached c / 2 <= 8 /\ 2 * (max_cached c / 2) <= max_cached c).
    { split. split; [apply Z.div_le_lower_bound|apply Z.div_le_upper_bound]; lia. apply Z.mul_div_le; lia. }
    set (m := max_cached c / 2) in *. clearbody m.
    pose proof (INV_init_cache _ _ _ _ HI) as HI1.
    destruct (Z.leb_spec m (c_num_freed (get_cls st c))) as [Hen|Hlt].
    + (* [comment removed for export] *)
      destruct (Z.ltb_spec (c_num_freed (get_cls st c)) m); [lia|].
      apply Hk; [|right; apply same_but_put
                 | apply FAINV_put; [exact Hc| apply FAINV_init_cache; exact HFA| cproj; rewrite ?get_cls_init_cache; lia| cproj; rewrite ?get_cls_init_cache; lia]
                 | rewrite VC_put by exact Hc; rewrite VC_init_cache; unfold vc_cls; cproj; rewrite ?get_cls_init_cache; lia].
      apply REPC; auto; rewrite ?all_chunks_init_cache, ?qbatches_init_cache, ?get_cls_init_cache; try reflexivity.
      all: try (unfold cls_mapped_bytes'; cproj; lia).
      unfold CLSOK. cproj. rewrite max_count_init_cache, all_chunks_init_cache, qbatches_init_cache, all_chunks_cons, cntP_cons. cbn [is_prim_of]. rewrite Z.eqb_refl. repeat split; try lia.
    + (* [comment removed for export] *)
      apply (populate_ok R P pc pb (init_cache st) c (m - c_num_freed (get_cls st c)) _ mo HI1 Hc ltac:(lia) ltac:(lia)).
      * rewrite get_cls_init_cache || idtac. apply Z.le_trans with (m * size_of_class c); [apply Z.mul_le_mono_nonneg_r; lia| lia].
      * rewrite get_cls_init_cache. rewrite C10.
        assert (size_of_class c * c_num_freed (get_cls st c) <= size_of_class c * 8) by (apply Z.mul_le_mono_nonneg_l; lia).
        assert (size_of_class c * c_count (get_cls st c) = 0) by (replace (c_count (get_cls st c)) with 0 by lia; ring).
        nia || lia.
      * rewrite CH_init_cache. exact HSB.
      * apply FAINV_init_cache. exact HFA.
      * rewrite VC_init_cache. exact HVC.
      * unfold init_cache. destruct (a_cinit st); exact HSBP.
      * intros st2 mo2 HI2 HSB2 Ecnt Enf HFA2 HVC2. rewrite get_cls_init_cache in Ecnt, Enf. rewrite VC_init_cache in HVC2.
        destruct (Z.ltb_spec (c_num_freed (get_cls st2 c)) m); [lia|].
        pose proof HI2 as [HA2 HM2]. pose proof (AINV_cls _ _ _ _ HA2 Hc) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
        assert (AC : all_chunks pc pb st2 = all_chunks pc pb st /\ qbatches pb st2 = qbatches pb st).
        { destruct HSB2 as (_&_&_&_&_&Hl&_&Hq1&_&Hq2&_&_). unfold all_chunks, qbatches, live_chunks. unfold init_cache in Hl, Hq1, Hq2.
          destruct (a_cinit st); cbn in Hl, Hq1, Hq2; rewrite Hl, Hq1, Hq2; split; reflexivity. }
        destruct AC as [AC1 AC2].
        apply Hk. 2:{ right. eapply same_but_trans; [exact HSB2| apply same_but_put]. }
        2:{ apply FAINV_put; [exact Hc| exact HFA2| |]; cproj; pose proof (HFA2 c Hc) as [[X0 X1] X2]; lia. }
        2:{ rewrite VC_put by exact Hc. unfold vc_cls. cproj. lia. }
        apply (INV_repc pc); auto.
        -- constructor; [exact Hwf|]. destruct HA as (_ & Hall & _). unfold all_chunks in Hall. apply Forall_app in Hall as [Hpc _]. exact Hpc.
        -- intros c' Hc' Hne. rewrite cntP_cons. cbn [is_prim_of]. replace (c =? c') with false by (symmetry; apply Z.eqb_neq; lia). lia.
        -- unfold CLSOK. cproj. rewrite all_chunks_cons, cntP_cons. cbn [is_prim_of]. rewrite Z.eqb_refl. rewrite AC1, AC2 in D10. rewrite AC1, AC2.
           rewrite (max_count_same_but _ _ _ c HSB2), max_count_init_cache in *. repeat split; try lia.
        -- unfold cls_mapped_bytes'. cproj. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma AMI_perm : forall ch ch' st mo, Permutation ch ch' -> AMI ch st mo -> AMI ch' st mo.
Proof.
  intros ch ch' st mo HP H. destruct H as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & L0 & HPm & HS & HB).
  unfold AsanInv.AMI. repeat (split; [assumption|]). exists L0. split; [|split; assumption].
  eapply Permutation_trans; [exact HPm|]. apply Permutation_app_head. apply Permutation_map. exact HP.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AINV_live_perm : forall pc pc' pb st lv nx,
  AINV pc pb st ->
  Permutation (all_chunks pc' pb (set_next nx (set_live lv st))) (all_chunks pc pb st) ->
  (forall id ch, lv !! id = Some ch -> (id < nx)%N) ->
  live_budget (set_next nx (set_live lv st)) ->
  AINV pc' pb (set_next nx (set_live lv st)).
Proof.
  intros pc pc' pb st lv nx H HP Hid HLB. unfold AINV in *.
  destruct H as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13).
  cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array set_next set_live a_cinit] in *.
  assert (Hq : qbatches pb (set_next nx (set_live lv st)) = qbatches pb st) by reflexivity.
  assert (HCH : zlen (CH pc' pb (set_next nx (set_live lv st))) = zlen (CH pc pb st)).
  { unfold CH, zlen. f_equal. apply Permutation_length. apply secs_perm. exact HP. }
  split.
  { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. unfold get_cls, max_count in *. cbn [a_cls a_cinit set_next set_live] in *.
    rewrite Hq, (cntP_perm c _ _ HP). exact X. }
  split. { eapply Permutation_Forall; [apply Permutation_sym; exact HP| exact H2]. }
  rewrite Hq, HCH. repeat (split; [assumption|]). exact HLB.
Qed.

#[using="Type"] Lemma INV_hand_to_live : forall ch pc pb st mo,
  INV (ch :: pc) pb st mo ->
  live_budget_list (ch :: live_chunks st) ->
  INV pc pb (set_next (N.succ (a_next st)) (set_live (<[a_next st := ch]> (a_live st)) st)) mo.
Proof.
  intros ch pc pb st mo [HA HM] HLB.
  assert (Hnone : (a_live st) !! (a_next st) = None).
  { destruct ((a_live st) !! (a_next st)) as [ch0|] eqn:E; [|reflexivity]. exfalso.
    destruct HA as (_ & _ & _ & _ & _ & _ & _ & Hid & _). specialize (Hid _ _ E). Local Ltac2 Set LiaHints.tbl := fun () => "00=0>150060430.24  15833096338.2324928553324.1730153722418.1733773570348.2233783453552.2036196656970.2250822906301.2357745617343.2459314955108.1466203049950.2366742810639.2468045168975.1900000100200300400500600700=00L00Q00R00X00]SSSSFFSS4IHP0S6IHP0_16IHP0_2S3HidSS4IHP0S3Hid".
lia. }
  pose proof (live_chunks_insert st (a_next st) ch Hnone) as HPl.
  assert (HP : Permutation (all_chunks pc pb (set_next (N.succ (a_next st)) (set_live (<[a_next st := ch]> (a_live st)) st))) (all_chunks (ch :: pc) pb st)).
  { unfold all_chunks. cbn [app]. unfold live_chunks in *. cbn [a_live set_next set_live] in *.
    change (qbatches pb (set_next (N.succ (a_next st)) (set_live (<[a_next st:=ch]> (a_live st)) st))) with (qbatches pb st).
    eapply Permutation_trans. { apply Permutation_app_head. apply Permutation_app_tail. exact HPl. }
    rewrite app_comm_cons. apply Permutation_sym. cbn. apply Permutation_middle. }
  split.
  - apply (AINV_live_perm (ch :: pc)); auto.
    + intros id ch0 Hl. destruct (N.eq_dec id (a_next st)) as [->|Hne]; [lia|].
      rewrite lookup_insert_ne in Hl by congruence. destruct HA as (_ & _ & _ & _ & _ & _ & _ & Hid & _). specialize (Hid _ _ Hl). lia.
    + apply live_budget_list_iff. unfold live_chunks. cbn [a_live set_next set_live]. unfold live_chunks in HPl. cbn [a_live set_live] in HPl.
      destruct HLB as (B1 & B2 & B3). split; [|split].
      * intros c Hc. rewrite (cntP_perm c _ _ HPl). apply B1. exact Hc.
      * unfold zlen in *. rewrite (Permutation_length (secs_perm _ _ HPl)). exact B2.
      * assert (E : forall l l', Permutation l l' -> secbytes l = secbytes l').
        { intros l l' P0. induction P0; cbn; try lia. - destruct x; lia. - destruct x, y; lia. }
        rewrite (E _ _ HPl). exact B3.
  - apply (AMI_perm (CH (ch :: pc) pb st)).
    + unfold CH. apply secs_perm. apply Permutation_sym. exact HP.
    + apply (AMI_mono _ st); auto. apply Z.le_refl || (unfold commit_bytes, csum, get_cls; cbn; lia).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_le : forall x a, 0 < a -> rdn x a <= x. Proof. intros. unfold rdn. rewrite Z.mul_comm. apply Z.mul_div_le. Local Ltac2 Set LiaHints.tbl := fun () => "0010=26981515745.7000003S1H".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rdn_mod : forall x a, 0 < a -> rdn x a mod a = 0. Proof. intros. unfold rdn. apply Z_mod_mult. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma poison0_ok : forall R (P : R -> Model -> Prop) pc pb st (k : AM R) mo a s,
  INV pc pb st mo -> 0 <= a -> 0 <= s <= 2^31 ->
  (a + s <= LS_LO \/ (KHIGH <= a /\ a + s <= ATOP)) ->
  zsum2 (CH pc pb st) <= SECM ->
  FAINV st -> VC st <= VCMAX ->                                        (* [comment removed for export] *)
  (forall mo', INV pc pb st mo' -> atot k mo' P) ->
  atot (poison0 a s k) mo P.
Proof.
  intros R P pc pb st k mo a s HI Ha Hs Hrange HSB HFA HVC Hk. pose proof (commit_le_VC _ HFA) as HCV. pose proof VCMAX_CBROOM as (HVX1 & HVX2 & HVX3).
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  unfold poison0. destruct (Z.eqb_spec s 0) as [->|Hs0]; [apply Hk; exact HI|]. cbv zeta.
  Local Ltac2 Set LiaHints.tbl := fun () => "00Z0>18524090079.5118926759402.3518928484651.3818928484909.3618928485036.3718928648749.3918941438064.4422163628883.4723979405855.4323983603056.5123985775366.5224720208327.492636308158.40 29786554462.293114124795.48 3120429507.46 3217586656.45 35208664165.4835902374983.4039240387253.4141338044100.4641698192603.4444095282829.4544841796876.4745890393773.4953376793749.5253378840875.495449336399.49 54513645875.4454873238660.4459589554278.4559589554278.4661026691409.4361028779636.4563368119852.4063368316460.4763368316589.4663374621462.4463374621462.4763380908026.4563380908026.46737093805.52  00000600700800900:00;00<00H00M00R00W00X00Y00Z00j01701=01A01B01F01K01O01_01h02002502:02Z02^02b02c02d02e02f02g02h02i02j02k02l02m035S4HmodSSSSSSS1H2H02H12H2S3HltS3HltS3HltFSSS2R12D13Hsb1H2H0S2R12D13Hsb1HS4HlowS2H3SS2HaS3Hh1S2HsS2R12D13Hsb1H2H0S3Hh23AT2S2R13HsbS3HE2S3HE2S2Ha3HVC3HCV4HVX13Hlt2R12R24HlenS2D2S2R3SSSSSSSSSSSS2R13Hsb".
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  set (sbeg := SHADOW_OFF + a / 8). set (send := SHADOW_OFF + (a + s - 8) / 8 + 1).
  destruct (Z.ltb_spec (send - sbeg) CLEAR_SHADOW_MMAP_THRESHOLD) as [|Hbig]; [apply Hk; exact HI|].
  set (pbeg := rup sbeg PG). set (pend := rdn send PG).
  destruct (Z.leb_spec pend pbeg) as [|Hlt]; [apply Hk; exact HI|].
  pose proof (rup_ge sbeg PG ltac:(unfold PG; lia)) as R1. pose proof (rup_le sbeg PG ltac:(unfold PG; lia)) as R2.
  pose proof (rup_mod sbeg PG ltac:(unfold PG; lia)) as R3. fold pbeg in R1, R2, R3.
  pose proof (rdn_le send PG ltac:(unfold PG; lia)) as D1. pose proof (rdn_mod send PG ltac:(unfold PG; lia)) as D2. fold pend in D1, D2.
  assert (Hsb : SHADOW_OFF <= sbeg /\ send <= SHADOW_OFF + (a + s) / 8 + 1 /\ SHADOW_OFF + a / 8 <= sbeg) by (unfold sbeg, send; split; [|split]; [pose proof (Z.div_pos a 8); lia| apply Z.add_le_mono_r; apply Z.add_le_mono_l; apply Z.div_le_mono; lia | lia]).
  destruct (INV_shadows _ _ _ _ HI) as (HinLS & _ & HinHS).
  assert (Hlen : 0 < pend - pbeg <= 2^30).
  { split; [lia|]. assert ((a + s) / 8 <= a / 8 + s / 8 + 1).
    { pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)). pose proof (Z.div_mod s 8 ltac:(lia)). pose proof (Z.mod_pos_bound s 8 ltac:(lia)).
      enough ((a + s) / 8 < a / 8 + s / 8 + 2) by lia. apply Z.div_lt_upper_bound; lia. }
    assert (s / 8 <= 2^28) by (apply Z.div_le_upper_bound; lia). lia. }
  assert (Hmod : (pend - pbeg) mod 4096 = 0).
  { apply divide_mod0; [lia|]. apply Z.divide_sub_r; apply mod0_divide; unfold PG in *; try lia; assumption. }
  (* [comment removed for export] *)
  assert (HE : exists E, In E (vm_maps (m_vmmaps mo)) /\ B E <= pbeg /\ pend <= B E + S E).
  { destruct Hrange as [Hlow | [Hh1 Hh2]].
    - exists (went (LS_LO, LS_SZ)). split; [exact HinLS|]. unfold B, S, went. cbn [fst snd]. unfold LS_LO, LS_SZ in *. rewrite !unsigned_lit by lia.
      unfold SHADOW_OFF in *. assert ((a + s) / 8 <= 268430848) by (apply Z.div_le_upper_bound; lia). lia.
    - exists (went (HS_LO, HS_SZ)). split; [exact HinHS|]. unfold B, S, went. cbn [fst snd]. unfold HS_LO, HS_SZ. rewrite !unsigned_lit by lia.
      unfold SHADOW_OFF, KHIGH in *.
      assert (2199291686912 <= a / 8) by (apply Z.div_le_lower_bound; lia).
      assert ((a + s) / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia). lia. }
  destruct HE as (E & HinE & HE1 & HE2).
  apply atotal_vis.
  - apply (INV_recommit_aok pc pb st mo E); auto; try lia; try (unfold PG in R3; exact R3). unfold RES_HI, SHADOW_OFF in *. lia.
  - intros z mo' Hpost. cbn [apost] in Hpost.
    assert (Hpz : (pbeg =? 0) = false) by (apply Z.eqb_neq; unfold SHADOW_OFF in *; lia). rewrite Hpz in Hpost.
    destruct Hpost as [-> ->]. rewrite Z.eqb_refl. apply Hk.
    destruct HI as [HA HM]. split; [exact HA|].
    assert (ML : mmap_len (pend - pbeg) = pend - pbeg) by (apply mmap_len_id; lia). rewrite ML.
    apply (AMI_recommit _ _ _ E); auto; try lia; try (unfold PG in R3; exact R3).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma grant_range : forall pc pb st mo z n,
  INV pc pb st mo -> 0 < z -> 0 < n -> z + n <= ATOP ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 n) = true ->
  z + n <= LS_LO \/ (KHIGH <= z /\ z + n <= ATOP).
Proof.
  intros pc pb st mo z n HI Hz Hn Hce Hrf.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  destruct (INV_shadows _ _ _ _ HI) as (HinLS & HinGAP & HinHS).
  rewrite region_free_app in Hrf. apply andb_true_iff in Hrf as [_ Hrf].
  pose proof (region_free_wsep _ _ _ Hrf) as HW. rewrite Forall_forall in HW.
  pose proof (HW _ HinLS) as W1. pose proof (HW _ HinGAP) as W2. pose proof (HW _ HinHS) as W3.
  unfold wsep, went in W1, W2, W3. cbn [fst snd] in W1, W2, W3.
  unfold ACEIL, LS_LO, LS_SZ, GAP_LO, GAP_SZ, HS_LO, HS_SZ, KHIGH in *. rewrite !unsigned_lit in W1, W2, W3 by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma filter_perm : forall {A} (f : A -> bool) l l', Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
  intros A f l l' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; cbn.
  - constructor.
  - destruct (f x); [apply perm_skip|]; exact IH.
  - destruct (f y), (f x); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.
#[using="Type"] Lemma zsizes_perm : forall l l', Permutation l l' -> zsizes l = zsizes l'.
Proof. intros l l' HP. induction HP; cbn; lia. Qed.
#[using="Type"] Lemma zsizes_filter_le : forall f l, Forall (fun e => 0 <= snd e) l -> zsizes (List.filter f l) <= zsizes l.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0030>15045131572.6 58251394933.1062508643622.1000000100800<SS2IH2HeS2IH".
induction l as [|e l IH]; intros HF; cbn; [lia|]. apply Forall_cons_iff in HF as [He HF]. specialize (IH HF). destruct (f e); cbn; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma filter_none : forall {A} (f : A -> bool) l, Forall (fun x => f x = false) l -> List.filter f l = [].
Proof. induction l as [|x l IH]; intros HF; cbn; [reflexivity|]. apply Forall_cons_iff in HF as [Hx HF]. rewrite Hx. apply IH. exact HF. Qed.
#[using="Type"] Lemma zsizes_zent_went : forall ch, Forall (fun e => 0 <= snd e < 2^64) ch -> Forall (fun e => 0 <= fst e < 2^64) ch ->
  zsizes (map zent (map went ch)) = zsum2 ch.
Proof.
  induction ch as [|[mb ms] ch IH]; intros H1 H2; cbn -[Z_to_bv bv_unsigned Z.pow]; [reflexivity|].
  apply Forall_cons_iff in H1 as [A1 H1]. apply Forall_cons_iff in H2 as [A2 H2]. cbn [fst snd] in A1, A2.
  Local Ltac2 Set LiaHints.tbl := fun () => "0010>48729667332.12000004S2A1".
rewrite unsigned_lit by lia. rewrite (IH H1 H2). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
(* [comment removed for export] *)

#[using="Type"] Lemma achunks_all_chunks : forall pc pb st ch, In ch (achunks st) -> In ch (all_chunks pc pb st).
Proof.
  intros pc pb st ch Hin. unfold achunks, all_chunks, live_chunks, qchunks, qbatches in *.
  apply in_app_iff. right. apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff; [left; exact Hin| right].
  apply in_flat_map in Hin as (b & Hb & Hin). apply in_flat_map. exists b. split; [|exact Hin]. apply in_app_iff. right. exact Hb.
Qed.

#[using="Type"] Lemma grant_avoids : forall pc pb st mo z len,
  INV pc pb st mo -> 0 < z -> 0 < len -> z + len <= ATOP ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 len) = true ->
  avoids_all z len (RESV ++ asec_ranges st) = true.
Proof.
  intros pc pb st mo z len HI Hz Hlen Hce Hrf.
  pose proof HI as [HA HM]. pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & L0 & HPm & HS & HB).
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HRC).
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  Local Ltac2 Set LiaHints.tbl := fun () => "00:0>26843016581.4738559449354.4045014629378.3547471426408.464770110496.44 48735947326.4751061282698.4752728673850.4765127107258.4066371604207.4400000300:00K00P00V00a00d01701@01FS1XS2Hz2ZLS2Hz4Hlen3Hce3AT2S3Hn'S1X2C1S3Hn'3Hms1HS1XS3AT23Hn'3Hms3Hwf1HS4Hlen2ZLS1X2C2".
assert (ZL : 0 <= z < 2^64 /\ 0 <= len < 2^64) by lia.
  assert (RF : forall e, In e (vm_reserved (m_vmmaps mo) ++ L0 ++ map went (CH pc pb st)) ->
               z + len <= bv_unsigned (fst e) \/ bv_unsigned (fst e) + bv_unsigned (snd e) <= z).
  { intros [b sz] He. pose proof (region_free_In _ _ _ b sz Hrf) as X. rewrite !unsigned_lit in X by lia. cbn [fst snd]. apply X.
    apply in_app_iff in He as [He|He]; apply in_app_iff; [left; exact He| right].
    eapply Permutation_in; [apply Permutation_sym; exact HPm| exact He]. }
  unfold avoids_all. apply forallb_forall. intros [lo hi] Hin. unfold iv_clear. cbn [fst snd].
  apply in_app_iff in Hin as [Hin|Hin].
  - (* [comment removed for export] *)
    destruct (proj1 (Forall_forall _ _) HRC _ Hin) as (e & He & C1 & C2). cbn [fst snd] in C1, C2.
    specialize (RF e ltac:(rewrite app_assoc; apply in_app_iff; left; exact He)).
    apply orb_true_iff. destruct RF as [X|X]; [left| right]; apply Z.leb_le; lia.
  - (* [comment removed for export] *)
    unfold asec_ranges in Hin. apply in_flat_map in Hin as (ch & Hch & Hin).
    destruct ch as [c n|mb ms n]; cbn in Hin; [destruct Hin|]. destruct Hin as [E|[]]. injection E as <- <-.
    pose proof (achunks_all_chunks pc pb st _ Hch) as Hall.
    assert (HinCH : In (mb, ms) (CH pc pb st)).
    { unfold CH, secs. apply in_flat_map. exists (CSec mb ms n). split; [exact Hall| cbn; left; reflexivity]. }
    destruct HA as (_ & HW & _). pose proof (proj1 (Forall_forall _ _) HW _ Hall) as Hwf. cbn in Hwf.
    destruct Hwf as (Hn' & Hms & Hwf). pose proof (sec_map_size_bounds n ltac:(lia)). unfold LS_LO, KHIGH, ACEIL in Hwf.
    specialize (RF (went (mb, ms)) ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_map; exact HinCH)).
    unfold went in RF. cbn [fst snd] in RF. rewrite !unsigned_lit in RF by lia.
    apply orb_true_iff. destruct RF as [X|X]; [left| right]; apply Z.leb_le; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma large_alloc_ok : forall R (P : R -> Model -> Prop) pc pb st n (k : astate -> option achunk -> AM R) mo,
  INV pc pb st mo -> 64512 < n <= 2^29 + 2^10 ->   (* [comment removed for export] *)
  zsum2 (CH pc pb st) + sec_map_size n <= SECM -> zlen (CH pc pb st) <= 5330 ->
  FAINV st -> VC st + 2^17 <= VCMAX ->                                  (* [comment removed for export] *)
  a_space_beg st = SBc /\ a_ptr_array st = PAc ->                         (* [comment removed for export] *)
  (forall st' mo' mb, INV (CSec mb (sec_map_size n) n :: pc) pb st' mo' ->
      (st' = set_nsec (a_nsec st + 1) st \/ st' = set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st)) ->
      FAINV st' -> VC st' <= VC st + 2^17 ->                              (* [comment removed for export] *)
      atot (k st' (Some (CSec mb (sec_map_size n) n))) mo' P) ->
  atot (large_alloc ATOP RESV st n k) mo P.
Proof.
  intros R P pc pb st n k mo HI Hn HSB HSL HFA HVC [HSB0 HPA0] Hk. unfold SECM in HSB. pose proof (commit_le_VC _ HFA) as HCB.
  pose proof VCMAX_CBROOM as (HVX1 & HVX2 & HVX3).
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  Local Ltac2 Set LiaHints.tbl := fun () => "00h0>12984872864.59133850924.59  13522188901.5913924115901.5618926670024.3618926681516.6218926748832.3718926761838.5919107843036.2920843864216.5623609569551.7024766699093.3724864325141.5125034627883.4725725635916.3728939092490.3729305750646.3030444272035.3335519699441.3839242955408.5241703946727.3745901840941.3046014686249.6246014738155.5946089670939.6246925835661.3047471537595.2848834522470.5949680308590.5949916425768.5150087641938.5951270680314.6051293226385.5051315663414.6254942571332.6055855987552.5857469534932.3757470079863.5158524806922.5958591475504.5958591526386.6259577176758.5661048359061.4364259623024.5964451360322.5965300158430.626644083547.43 6644459909.38 6654944783.39 6657042844.33 67416552890.5967416604536.6267537450058.5968242071252.517416399894.62 7816022499.30 00000800900M00N00O00P00Q00R00S00^00_00c00g00h00l01001D01I01Z01]01k01o02402902G02R02V02[02\02`02a02o03>03?03N03O03S03W03[03\03]03^03_03`03a03b03i04004704>04?04@04A04E04I04NS3AT22P2SS3HVC3HCB4HVX12Z22G4SSSSSSS3AT22P22G4SS2Z3S2H6SS2HdS2HdS2Hn3HVC3HCB4HVX12SBS3MSAS2Hn3AT22SB2Z22Z3S1XS2Hn3AT22SB2Z3S2HnS3HB1S3HB1S5Hres02G43HpzS2Hn3HSB2SBS2HnS3HSBFS2Z1SS5Hres02G43HpzS3HSL3Heq5HnsecFS3AT22P22G43HpzSS2Z2S2Z2S2G4SSSFFFFS2Hn2SBS2Hn2SBS2Hn2SBS2Hn2SBFFFS2HnS2G4S3HSL".
pose proof (sec_map_size_bounds n ltac:(lia)) as SB.
  assert (MSA : sec_map_size n mod 4096 = 0).
  { unfold sec_map_size, rup, PG. match goal with |- ?x mod 4096 = 0 => replace x with ((((needed_size n + 4096 - 1) / 4096) + 1) * 4096) by lia end. apply Z_mod_mult. }
  unfold large_alloc. unfold ev. apply atotal_vis.
  { apply (INV_grant_aok pc pb st mo n HI ltac:(lia)); unfold SECM; lia. }
  intros z mo' Hpost. cbn [apost] in Hpost. rewrite Z.eqb_refl in Hpost.
  assert (ML : mmap_len (sec_map_size n) = sec_map_size n) by (apply mmap_len_id; lia). rewrite ML in Hpost.
  destruct Hpost as (Z1 & Z2 & Z3 & Z4 & ->).
  assert (RUP : rup (sec_map_size n) PG = sec_map_size n).
  { unfold rup, PG. pose proof (Z.div_mod (sec_map_size n) 4096 ltac:(lia)) as Hd. rewrite MSA in Hd.
    replace (sec_map_size n + 4096 - 1) with (sec_map_size n / 4096 * 4096 + 4095) by lia. rewrite Z.div_add_l by lia. change (4095/4096) with 0. lia. }
  assert (Hok : mmap_answer_ok ATOP (sec_map_size n) z = true).
  { unfold mmap_answer_ok. rewrite RUP. apply orb_true_iff. right. unfold TWO64, PG.
    rewrite (proj2 (Z.ltb_lt 0 z)) by lia. rewrite Z1. cbn [Z.eqb andb]. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  rewrite Hok. cbn [negb]. rewrite is_err_small by (unfold TWO64; lia).
  pose proof (grant_range pc pb st mo z (sec_map_size n) HI Z2 ltac:(lia) Z3 Z4) as Hrange.
  (* [comment removed for export] *)
  pose proof (grant_avoids pc pb st mo z (sec_map_size n) HI Z2 ltac:(lia) Z3 Z4) as HAV.
  rewrite HAV. cbn [andb negb].
  (* [comment removed for export] *)
  set (ch := CSec z (sec_map_size n) n).
  set (st1 := set_nsec (a_nsec st + 1) st).
  assert (HI1 : INV (ch :: pc) pb st1 (grant_model mo z (sec_map_size n))).
  { destruct HI as [HA HM]. split.
    - unfold AINV in *. destruct HA as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
      unfold st1. cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array set_nsec a_cinit] in *.
      rewrite all_chunks_set_nsec, all_chunks_cons.
      change (qbatches pb (set_nsec (a_nsec st + 1) st)) with (qbatches pb st).
      change (CH (ch :: pc) pb (set_nsec (a_nsec st + 1) st)) with (sec_of ch ++ CH pc pb st).
      split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. unfold get_cls, max_count in *. cbn [a_cls a_cinit set_nsec] in *.
               rewrite all_chunks_set_nsec, all_chunks_cons, cntP_cons. cbn [is_prim_of]. change (qbatches pb (set_nsec (a_nsec st + 1) st)) with (qbatches pb st). rewrite Z.add_0_l. exact X. }
      split. { constructor; [|exact H2]. cbn. split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. exact Hrange. }
      split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
      split. { unfold ch. cbn [sec_of app]. rewrite zlen_cons. lia. }
      split; [exact H7|]. split; [exact H8|]. unfold live_budget, live_chunks in *. cbn [a_live set_nsec]. exact H9.
    - unfold st1. change (CH (ch :: pc) pb (set_nsec (a_nsec st + 1) st)) with ((z, sec_map_size n) :: CH pc pb st).
      apply (AMI_mono _ st); try reflexivity; try (unfold commit_bytes, csum, get_cls; cbn; lia).
      apply AMI_grant; auto; lia. }
  assert (CB1 : commit_bytes st1 = commit_bytes st) by reflexivity.
  assert (VC1 : VC st1 = VC st) by reflexivity.
  assert (FA1 : FAINV st1) by (eapply FAINV_frame; [| exact HFA]; intros; reflexivity).
  destruct (Z.eqb_spec (a_nsec st) (a_nres st)) as [Heq|Hne].
  2:{ apply Hk; [exact HI1| left; reflexivity| exact FA1| rewrite VC1; lia]. }
  (* [comment removed for export] *)
  destruct HI as [HA HM]. pose proof HA as (_ & _ & _ & _ & _ & Hnsec & Hres & _).
  assert (Hres0 : a_nres st = 0) by (destruct Hres as [?|E]; [assumption|]; rewrite E in Heq; unfold K_CHUNKS_BLOCK in Heq; lia).
  rewrite Hres0 in Hk |- *. destruct (Z.ltb_spec K_PTRARR_RESERVE (8 * (0 + K_CHUNKS_BLOCK))) as [X|_]; [unfold K_PTRARR_RESERVE, K_CHUNKS_BLOCK in X; lia|].
  destruct (INV_ptr _ _ _ _ HI1) as (HinP & P2 & PRF). unfold st1 in HinP, P2, PRF. cbn [a_ptr_array set_nsec] in HinP, P2, PRF.
  destruct (AINV_geom _ _ _ HA) as (_ & _ & G3 & G4).
  rewrite Z.mul_0_r, Z.add_0_r.
  assert (HBS : B (went (a_ptr_array st, PTR_SZ)) = a_ptr_array st /\ S (went (a_ptr_array st, PTR_SZ)) = PTR_SZ).
  { unfold B, S, went. cbn [fst snd]. unfold ACEIL, PTR_SZ, KHIGH in *. rewrite !unsigned_lit by lia. lia. }
  destruct HBS as [HB1 HS1].
  (* [comment removed for export] *)
  assert (HWp : inW SBc PAc (a_ptr_array st) K_PTRARR_COMMIT) by (right; rewrite <- HPA0; unfold K_PTRARR_COMMIT, K_PTRARR_RESERVE, K_CHUNKS_BLOCK; lia).
  apply atotal_vis.
  { apply (INV_fixed_aok _ _ _ _ (went (a_ptr_array st, PTR_SZ)) _ _ HI1); auto; try lia.
    - rewrite HB1, HS1. unfold K_PTRARR_COMMIT, PTR_SZ. lia.
    - (* [comment removed for export] *)
      apply (region_free_sub _ (a_ptr_array st) PTR_SZ); [exact PRF| | | | |]; unfold K_PTRARR_COMMIT, PTR_SZ in *; lia.
    - unfold K_PTRARR_COMMIT. lia.
    - change (CH (ch :: pc) pb st1) with ((z, sec_map_size n) :: CH pc pb st). cbn [zsum2 snd]. unfold SECM. lia.
    - rewrite CB1. unfold K_PTRARR_COMMIT. lia. }
  intros z2 mo2 Hpost2. cbn [apost] in Hpost2.
  assert (Hpz : (a_ptr_array st =? 0) = false) by (apply Z.eqb_neq; lia). rewrite Hpz in Hpost2. destruct Hpost2 as [-> ->].
  rewrite fixed_answer_ok_self. cbn [negb]. rewrite is_err_small by (unfold TWO64, ACEIL, KHIGH, PTR_SZ in *; lia).
  apply Hk; [| right; reflexivity
             | eapply FAINV_frame; [| exact HFA]; intros; reflexivity
             | unfold st1, VC, csum, get_cls; cbn; unfold K_CHUNKS_BLOCK; lia].
  assert (ML2 : mmap_len K_PTRARR_COMMIT = K_PTRARR_COMMIT) by reflexivity. rewrite ML2.
  destruct HI1 as [HA1 HM1]. split.
  - unfold AINV in *. destruct HA1 as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
    unfold st1 in *. cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array set_nsec set_nres a_cinit] in *.
    change (all_chunks (ch :: pc) pb (set_nres (0 + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st))) with (all_chunks (ch :: pc) pb (set_nsec (a_nsec st + 1) st)).
    change (qbatches pb (set_nres (0 + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st))) with (qbatches pb (set_nsec (a_nsec st + 1) st)).
    change (CH (ch :: pc) pb (set_nres (0 + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st))) with (CH (ch :: pc) pb (set_nsec (a_nsec st + 1) st)).
    split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. unfold get_cls, max_count in *. cbn [a_cls a_cinit set_nsec set_nres] in *. exact X. }
    repeat (split; [assumption|]). split; [right; lia|]. split; [exact H8|]. unfold live_budget, live_chunks in *. cbn [a_live set_nsec set_nres] in *. exact H9.
  - change (CH (ch :: pc) pb (set_nres (0 + K_CHUNKS_BLOCK) st1)) with (CH (ch :: pc) pb st1).
    apply (AMI_commit _ st1 _ _ (went (a_ptr_array st, PTR_SZ))); auto; try lia.
    + rewrite HB1, HS1. unfold K_PTRARR_COMMIT, PTR_SZ. lia.
    + unfold K_PTRARR_COMMIT. lia.
    + unfold st1, commit_bytes, csum, get_cls. cbn. unfold K_CHUNKS_BLOCK, K_PTRARR_COMMIT. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition mkch (n mb ms : Z) : achunk := if is_primary n then CPrim (class_id (needed_size n)) n else CSec mb ms n.

(* [comment removed for export] *)
Definition csig (ch : achunk) : Z + Z := match ch with CPrim c _ => inl c | CSec _ _ n => inr n end.
#[using="Type"] Lemma live_budget_list_sig : forall ch ch' L, csig ch = csig ch' -> live_budget_list (ch :: L) -> live_budget_list (ch' :: L).
Proof.
  intros ch ch' L Hs (B1 & B2 & B3). unfold live_budget_list.
  destruct ch as [c n|mb ms n], ch' as [c' n'|mb' ms' n']; cbn in Hs; try discriminate; injection Hs as E; subst.
  - split; [|split; assumption]. intros c Hc. specialize (B1 c Hc). rewrite cntP_cons in *. cbn [is_prim_of] in *. exact B1.
  - split; [|split]. { intros c Hc. specialize (B1 c Hc). rewrite cntP_cons in *. cbn [is_prim_of] in *. exact B1. }
    { rewrite secs_cons, zlen_app in *. cbn [sec_of] in *. unfold zlen in *. cbn [length] in *. Local Ltac2 Set LiaHints.tbl := fun () => "0020>15756743755.132041951049.13 000004008S2B2S2B3".
lia. }
    { cbn [secbytes] in *. lia. }
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma sec_map_size_ge : forall n, 64512 < n -> n + 8192 <= sec_map_size n.
Proof.
  intros n Hn. unfold sec_map_size, needed_size. Local Ltac2 Set LiaHints.tbl := fun () => "00:0=18930958230.836000985010.64354944178.6 52673924530.657455143858.660090944434.662248010674.663368324716.768481842591.99880878002.6 00000100500900=00A00E00I00J00S00WSS2HnS2HnS2HnS2HnS2HnS2HnSS2Hn1H2H0S2Hn".
rewrite large_not_primary by lia. unfold needed0, rounded_size.
  assert (Hr : rz_size n = 2048) by (unfold rz_size, rz_log; repeat (rewrite (proj2 (Z.leb_gt _ _)) by lia); reflexivity). rewrite Hr.
  pose proof (rup_ge (Z.max n 8) 8 ltac:(lia)). pose proof (rup_ge (rup (Z.max n 8) 8 + 2048 + 2048) PG ltac:(unfold PG; lia)). unfold PG in *. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma not_primary_large : forall n, 0 <= n -> is_primary n = false -> 64512 < n.
Proof.
  intros n Hn Hp. Local Ltac2 Set LiaHints.tbl := fun () => "0030=22314212875.857455559916.857461893808.800000700;00>S2Hn2n0S2HpS1l".
destruct (Z_lt_dec 64512 n); [lia|]. rewrite is_primary_iff in Hp by lia. apply Z.leb_gt in Hp. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma commit_bytes_set_next : forall x st, commit_bytes (set_next x st) = commit_bytes st. Proof. reflexivity. Qed.
#[using="Type"] Lemma commit_bytes_set_live : forall x st, commit_bytes (set_live x st) = commit_bytes st. Proof. reflexivity. Qed.
#[using="Type"] Lemma commit_bytes_set_nsec : forall x st, commit_bytes (set_nsec x st) = commit_bytes st. Proof. reflexivity. Qed.
#[using="Type"] Lemma commit_bytes_set_qloc : forall x y st, commit_bytes (set_qloc x y st) = commit_bytes st. Proof. reflexivity. Qed.
#[using="Type"] Lemma commit_bytes_set_qglob : forall x y st, commit_bytes (set_qglob x y st) = commit_bytes st. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition malloc_post (st : astate) (n : Z) (r : astate * option AsanCtrl.aptr) (mo' : Model) : Prop :=
  exists ch, snd r = Some (a_next st) /\ INV [] [] (fst r) mo' /\ a_live (fst r) = <[a_next st := ch]> (a_live st)
  /\ (a_live st) !! (a_next st) = None /\ chunk_size ch = n
  /\ a_qloc_bytes (fst r) = a_qloc_bytes st /\ a_qglob_bytes (fst r) = a_qglob_bytes st /\ a_qloc (fst r) = a_qloc st /\ a_qglob (fst r) = a_qglob st
  /\ FAINV (fst r) /\ VC (fst r) <= VC st + 2^19                         (* [comment removed for export] *)
  /\ a_next (fst r) = N.succ (a_next st).                                 (* [comment removed for export] *)

#[using="Type"] Theorem amalloc_core : forall st mo n,
  INV [] [] st mo -> a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX -> 0 <= n <= 2^29 ->
  (forall mb ms, live_budget_list (mkch n mb ms :: live_chunks st)) ->
  FAINV st -> VC st + 2^19 <= VCMAX ->                                   (* [comment removed for export] *)
  a_space_beg st = SBc /\ a_ptr_array st = PAc ->                         (* [comment removed for export] *)
  atot (amalloc ATOP RESV st n) mo (malloc_post st n).
Proof.
  intros st mo n HI Hql Hqg Hn HLB HFA HVC HSBP.
  pose proof HI as [HA HM].
  assert (Hnone : (a_live st) !! (a_next st) = None).
  { destruct ((a_live st) !! (a_next st)) as [ch0|] eqn:E; [|reflexivity]. exfalso.
    destruct HA as (_ & _ & _ & _ & _ & _ & _ & Hid & _). specialize (Hid _ _ E). Local Ltac2 Set LiaHints.tbl := fun () => "00b0>11813967142.2416151306471.4918552609514.4919327334363.3323028701879.212424961824.26 2424985702.33 256348879.33  26692122923.4927503406949.1929792849289.4729956161351.2231417995467.2933348508436.4935162304567.3335319830010.5135990497592.4840194002651.3341418081042.244352846392.48 44137518972.2144137520235.1944610714841.2545436084552.474661459657.19 47039558409.2947469326951.2748099046125.3348834525420.494968817449.49 52671826744.4856196621701.2957021571919.4957453047096.4859314955108.1960084653368.4860111104363.4962254302520.4862472898315.2462475008819.2563380912428.2265500326898.246644459524.24 68359971945.2168359974782.197387887892.33 751274010.48  908263505.25  9193714520.33 9866198328.48 00000500600;00?00@00D00H00I00a00f00g00j00o01901>01G01M01Q01R01X01Y01Z01c01d02502>02G02K02Y02f02l03703803>03C03I03U03[03a03i03j03k04004104204704804A04B04HS3HrlFS3HmbS2F3SS2HnS2HnSS2SG2E23Hmb6Hrange5HlandS3HQBSS1XS3HVCS2Hn5HlandS3HCSS4HVC'2E2S4HbigS2F3SS4HbigSSS2Hn1H2H0SS3Hql3Hqg3Hq13Hq2S2Hn4HbigS2Hn4HbigS2F1S2Hn3HCS2SB2E2S3HVC4HVC'2E2S4HbigS2Hn3HCS2SBFS4HbigS3HidS4HbigS4Hbig2H12H2S4HbigS2Hn1HS3Hns2H0SSS3HrlSSS3HVCSS2Hn1H2H0FS4Hbig".
lia. }
  assert (HQB : bsum (qbatches [] st) <= 2^28 + 2^22).
  { unfold qbatches. cbn [app]. rewrite bsum_app. destruct HA as (_ & _ & _ & Hq1 & Hq2 & _). unfold Q_CACHE, Q_MAX in *. lia. }
  destruct (CH_bounds [] [] st HA ltac:(lia) ltac:(unfold zlen; cbn; lia) ltac:(cbn; lia)) as [HCL HCS].
  assert (HCL2 : zlen (CH [] [] st) <= 5330).
  { destruct (CH_bounds_gen [] [] st (2^28 + 2^22) HA HQB ltac:(lia) ltac:(unfold zlen; cbn; lia) ltac:(cbn; lia)) as [X _]. lia. }
  assert (Hns : needed_size n <= 2^40).
  { unfold needed_size, needed0, rounded_size. pose proof (rup_le (Z.max n 8) 8 ltac:(lia)).
    pose proof (rz_log_range n) as Hrl.
    assert (0 <= rz_size n <= 2048).
    { unfold rz_size. rewrite Z.shiftl_mul_pow2 by lia. change 2048 with (16 * 2^7).
      split. apply Z.mul_nonneg_nonneg; [lia|apply Z.pow_nonneg; lia]. apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]. }
    destruct (is_primary n); lia. }
  unfold amalloc. destruct (Z.ltb_spec (2^40) n); [lia|]. destruct (Z.ltb_spec (2^40) (needed_size n)); [lia|]. cbn [orb].
  destruct (is_primary n) eqn:Hp.
  - (* [comment removed for export] *)
    pose proof (primary_class_facts n ltac:(lia) Hp) as F. cbv zeta in F. destruct F as (F1 & F2 & F3 & F4 & F5 & F6).
    set (c := class_id (needed_size n)) in *.
    apply (cache_alloc_ok _ _ [] [] st c n _ mo HI ltac:(lia) Hp eq_refl).
    + eapply room_of_AINV; eauto; try lia. unfold cntP, zlen. cbn. lia.
    + unfold SECM. lia.
    + exact HFA.
    + lia.
    + exact HSBP.
    + intros st' mo' HI' HSB' HFA' HVC'.
      assert (HF : a_live st' = a_live st /\ a_next st' = a_next st /\ a_qloc_bytes st' = a_qloc_bytes st /\ a_qglob_bytes st' = a_qglob_bytes st /\ a_qloc st' = a_qloc st /\ a_qglob st' = a_qglob st).
      { destruct HSB' as [X|X]; destruct X as (_&_&_&_&_&Hl&Hnx&Hq1&Hqb1&Hq2&Hqb2&_); [repeat split; assumption|].
        unfold init_cache in *; destruct (a_cinit st); cbn in *; repeat split; assumption. }
      destruct HF as (E1 & E2 & E3 & E4 & E5 & E6).
      cbv beta iota. apply atotal_ret. exists (CPrim c n). cbn [fst snd]. rewrite E2, E1.
      split; [reflexivity|]. split.
      { rewrite <- E1, <- E2. apply INV_hand_to_live; [exact HI'|]. unfold live_chunks. rewrite E1. specialize (HLB 0 0). unfold mkch in HLB. rewrite Hp in HLB. exact HLB. }
      repeat match goal with |- _ /\ _ => split end; auto.
      all: try (rewrite ?VC_set_next, ?VC_set_live; lia).
      all: try (eapply FAINV_frame; [| exact HFA']; intros; reflexivity).
      all: try (cbn [a_next set_next set_live]; rewrite E2; reflexivity).
  - (* [comment removed for export] *)
    pose proof (not_primary_large n ltac:(lia) Hp) as Hbig. pose proof (sec_map_size_bounds n ltac:(lia)) as SB. pose proof (sec_map_size_ge n Hbig) as SG.
    apply (large_alloc_ok _ _ [] [] st n _ mo HI ltac:(lia) ltac:(unfold SECM; lia) HCL2 HFA ltac:(lia) HSBP).
    intros st' mo' mb HI' Hst' HFA' HVC'.
    assert (HF : a_live st' = a_live st /\ a_next st' = a_next st /\ a_qloc_bytes st' = a_qloc_bytes st /\ a_qglob_bytes st' = a_qglob_bytes st /\ a_qloc st' = a_qloc st /\ a_qglob st' = a_qglob st).
    { destruct Hst' as [-> | ->]; repeat split; reflexivity. }
    destruct HF as (E1 & E2 & E3 & E4 & E5 & E6).
    cbv beta iota. cbn [chunk_user_beg].
    pose proof HI' as [HA' HM']. pose proof HA' as (_ & HW' & _). rewrite all_chunks_cons in HW'. apply Forall_cons_iff in HW' as [Hwf _].
    cbn in Hwf. destruct Hwf as (_ & _ & Hal & Hmb & Hrange).
    assert (Hland : 0 <= Z.land n (Z.lnot 7) <= n).
    { rewrite <- Z.ldiff_land. change 7 with (Z.ones 3). rewrite Z.ldiff_ones_r by lia.
      rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. pose proof (Z.div_mod n (2^3) ltac:(lia)). pose proof (Z.mod_pos_bound n (2^3) ltac:(lia)). lia. }
    assert (Hrz : rz_size n = 2048) by (unfold rz_size, rz_log; repeat (rewrite (proj2 (Z.leb_gt _ _)) by lia); reflexivity).
    rewrite Hrz. unfold PG.
    apply (poison0_ok _ _ [CSec mb (sec_map_size n) n] [] st' _ mo'); auto; try lia.
    + rewrite CH_cons. cbn [sec_of app zsum2 snd].
      replace (CH [] [] st') with (CH [] [] st) by (unfold CH, all_chunks, live_chunks, qbatches; rewrite E1, E5, E6; reflexivity). unfold SECM in *. lia.
    + intros mo'' HI''. apply atotal_ret. exists (CSec mb (sec_map_size n) n). cbn [fst snd]. rewrite E2, E1.
      split; [reflexivity|]. split.
      { rewrite <- E1, <- E2. apply INV_hand_to_live; [exact HI''|]. unfold live_chunks. rewrite E1. specialize (HLB mb (sec_map_size n)). unfold mkch in HLB. rewrite Hp in HLB. exact HLB. }
      repeat match goal with |- _ /\ _ => split end; auto.
      all: try (rewrite ?VC_set_next, ?VC_set_live; lia).
      all: try (eapply FAINV_frame; [| exact HFA']; intros; reflexivity).
      all: try (cbn [a_next set_next set_live]; rewrite E2; reflexivity).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

End WithResv.
