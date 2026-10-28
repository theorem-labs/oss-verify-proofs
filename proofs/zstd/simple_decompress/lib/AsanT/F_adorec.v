(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MM_syscalls WStr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase AKit AKit2 AKitQ AKitR ABytes AQConst AModelFacts ARep ARepKit ARepFrame ALayout AHeapP ASec
     ASecFacts ARepQ ARepQP ARepQR AFreeRep AFreeGeo AFreeRead ARecRep ARepQD ARefillP AFrameD ARepExt RT_stubs
     F_apoison F_acache F_aalloc3 F_ammap F_aensure F_apopulate F_agetfrom F_arefill F_amaybe F_areturn F_acdrain F_acdealloc F_arecyc1
     ASecRecycle_iface ARecyc1P ACdeallocP ARecGeo.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import LiaTier0U.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib.StoreFast.tlia ::= tlia_u.
Local Ltac OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib.StoreFast.lia3 ::= lia3_u.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition adorec_entry : Z := 0x35a1c.
Definition adorec_lout : Z := 0x35a94.     (* [comment removed for export] *)
Definition adorec_lin : Z := 0x35ad4.      (* [comment removed for export] *)
Definition adorec_after : Z := 0x35aec.    (* [comment removed for export] *)
Definition adorec_chk : Z := 0x35b18.      (* [comment removed for export] *)
End CANSEC1.
Notation DOREC_FRAME := 112 (only parsing).
Notation DOREC_STACK := 1136 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition ehdr (L : alayout) (e : achunk * Z) : word := Z_to_bv 64 (qhdr L (fst e) (snd e)).

Lemma qhdrs_rev_combine : forall L chs ks, length ks = length chs ->
  map (Z_to_bv 64) (qhdrs L chs ks) = map (ehdr L) (rev (combine chs ks)).
Proof.
  induction chs as [|ch chs IH]; intros [|k ks] LEN; cbn in *; try reflexivity; try lia.
  rewrite map_app, map_app, IH by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition esecs (es : list (achunk * Z)) : list achunk := List.filter is_sec (map fst es).
Lemma esecs_app : forall a b, esecs (a ++ b) = esecs a ++ esecs b.
Proof. intros. unfold esecs. rewrite map_app. apply List.filter_app. Qed.
Lemma esecs_cons_prim : forall c n k es, esecs ((CPrim c n, k) :: es) = esecs es.
Proof. reflexivity. Qed.
Lemma esecs_cons_sec : forall mb ms n k es, esecs ((CSec mb ms n, k) :: es) = CSec mb ms n :: esecs es.
Proof. reflexivity. Qed.
Lemma esecs_perm : forall a b, Permutation a b -> Permutation (esecs a) (esecs b).
Proof.
  intros a b P. unfold esecs. induction P; cbn; [constructor| | | eapply Permutation_trans; eassumption].
  - destruct (is_sec (fst x)); [apply perm_skip|]; assumption.
  - destruct (is_sec (fst x)), (is_sec (fst y)); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
Qed.

(* [comment removed for export] *)
Definition secsT (R : qrconc) : list achunk := esecs (qentries (map fst (qr_tmp R)) (map snd (qr_tmp R))).
Definition inflight (R : qrconc) : list achunk := secsT R ++ esecs (qr_pend R).
(* [comment removed for export] *)
Definition csx (st : astate) (R : qrconc) : list achunk := sec_chunks_of st ++ inflight R.

(* [comment removed for export] *)
Definition qr_popr (R : qrconc) (b : abatch) (q : qbatchc) (T : list (abatch * qbatchc)) : qrconc :=
  mkQR (qr_loc R) (qr_glob R) (qr_ia R) T [qb_slot q] (rev (combine (b_chunks b) (qb_ks q))) (qr_qpend R).

Lemma qcoupled_rec_popr : forall L st X R b q T,
  qcoupled_rec L st X R -> qr_tmp R = (b, q) :: T -> qr_pendb R = [] -> qr_pend R = [] ->
  qcoupled_rec L st X (qr_popr R b q T).
Proof.
  intros L st X R b q T CP ET EB EP. pose proof (qcoupled_rec_pop L st X R b q T CP ET EB EP) as CP1. pose proof CP1 as (LN1 & LN2 & _).
  eapply qcoupled_rec_perm; [exact CP1| exact LN1| exact LN2| | | reflexivity].
  - unfold qr_entries, qr_popr, qr_pop. cbn [qr_loc qr_glob qr_tmp qr_pend]. repeat apply Permutation_app_head. apply Permutation_sym. apply Permutation_rev.
  - unfold qr_bslots, qr_popr, qr_pop. cbn [qr_loc qr_glob qr_tmp qr_pendb]. apply Permutation_refl.
Qed.

Lemma inflight_popr : forall R b q T, qr_tmp R = (b, q) :: T -> qr_pend R = [] -> length (qb_ks q) = length (b_chunks b) ->
  Permutation (inflight (qr_popr R b q T)) (inflight R).
Proof.
  intros R b q T ET EP LEN. unfold inflight, secsT, qr_popr. cbn [qr_tmp qr_pend]. rewrite ET, EP. cbn [map fst snd qentries].
  rewrite esecs_app. replace (esecs []) with (@nil achunk) by reflexivity. rewrite app_nil_r.
  eapply Permutation_trans; [apply Permutation_app_comm|]. apply Permutation_app_tail. apply esecs_perm. apply Permutation_sym. apply Permutation_rev.
Qed.

(* [comment removed for export] *)
Lemma do_recycle_cons : forall {RT} st b bs (k : astate -> AM RT),
  do_recycle st (b :: bs) k = recycle_chunks st (rev (b_chunks b)) (fun st1 => cache_dealloc st1 K_BATCH_CLASS (fun st2 => do_recycle st2 bs k)).
Proof. reflexivity. Qed.
Lemma recycle_chunks_prim : forall {RT} st c n l (k : astate -> AM RT),
  recycle_chunks st (CPrim c n :: l) k = cache_dealloc st c (fun st1 => recycle_chunks st1 l k).
Proof. reflexivity. Qed.
Lemma recycle_chunks_sec : forall {RT} st mb ms n l (k : astate -> AM RT),
  recycle_chunks st (CSec mb ms n :: l) k = large_dealloc st mb ms (fun st1 => recycle_chunks st1 l k).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma AQdr_popr : forall R L st X m b q T,
  AQdr R 0 0 L st X m -> qr_tmp R = (b, q) :: T -> qr_pendb R = [] -> qr_pend R = [] ->
     AQdr (qr_popr R b q T) 0 0 L st X m
  /\ abatch_cells L m b q (qfirst L (map snd T))
  /\ Q_BATCH_BYTES <= b_size b /\ qnum_tmp (map fst T).
Proof.
  intros R L st X m b q T (QC & MX & TC & GL & TB & IA & CP & NUM & NT) ET EB EP.
  rewrite ET in TB, NT. cbn [map fst snd] in TB, NT. destruct TB as [BC TB']. pose proof (Forall_inv NT) as NB. pose proof (Forall_inv_tail NT) as NT'. cbn beta in NB.
  split; [| split; [exact BC| split; [exact NB| exact NT']]].
  unfold AQdr, qr_popr. cbn [qr_loc qr_glob qr_tmp qr_ia].
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact TB'|]. split; [exact IA|].
  split; [exact (qcoupled_rec_popr L st X R b q T CP ET EB EP)|]. split; [exact NUM| exact NT'].
Qed.

Lemma AQdr_drop_sec : forall R L st X m mb ms n kk pend',
  AQdr R 0 0 L st X m -> qr_pend R = (CSec mb ms n, kk) :: pend' -> AQdr (qr_drop R pend') 0 0 L st X m.
Proof.
  intros R L st X m mb ms n kk pend' (QC & MX & TC & GL & TB & IA & CP & NUM & NT) EP.
  unfold AQdr, qr_drop. cbn [qr_loc qr_glob qr_tmp qr_ia].
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact TB|]. split; [exact IA|].
  split; [exact (qcoupled_rec_drop_sec L st X R mb ms n kk pend' CP EP)|]. exact (conj NUM NT).
Qed.

(* [comment removed for export] *)
Lemma AQdr_set_nsec : forall R L st X m v, AQdr R 0 0 L st X m -> AQdr R 0 0 L (set_nsec v st) X m.
Proof.
  intros R L st X m v (QC & MX & TC & GL & TB & IA & CP & NUM & NT). unfold AQdr. cbn.
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact TB|]. split; [exact IA|].
  split; [| exact (conj NUM NT)].
  eapply qcoupled_rec_same; [exact CP|]. unfold quar_same. cbn. repeat (split; [reflexivity|]).
  split; intros b Hb; destruct (xb_st b); first [exact I| exact Hb].
Qed.

(* [comment removed for export] *)
Lemma tmp_head_geo : forall R L st X m b q T, alayout_ok L -> awf L st X -> AQdr R 0 0 L st X m -> qr_tmp R = (b, q) :: T ->
  17594333495296 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= ATOP.
Proof.
  intros R L st X m b q T ALO WF (_ & _ & _ & _ & _ & _ & CP & _) ET.
  destruct (qcoupled_rec_bslot_busy L st X R (qb_slot q) CP ltac:(apply In_qr_bslots; rewrite ET; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity)) as (bb & Hb & Sb & Cb & Kb).
  pose proof (busy_slot_geo L st X ALO WF bb Hb) as (_ & _ & _ & _ & _ & G4 & G5 & _).
  unfold xb_alloc in G4, G5. rewrite Cb, Kb in G4. rewrite Cb, Kb, size_of_class_24 in G5. unfold abatch_addr. exact (conj G4 G5).
Qed.

(* [comment removed for export] *)
Lemma live_sec_in' : forall st (p : aptr) mb ms n, (a_live st) !! p = Some (CSec mb ms n) -> In (CSec mb ms n) (sec_chunks_of st).
Proof.
  intros st p mb ms n Lp. unfold sec_chunks_of. apply List.filter_In. split; [| reflexivity].
  unfold achunks. apply in_or_app. left.
  pose proof (map_to_list_delete (a_live st) p _ Lp) as P. apply (Permutation_map snd) in P. cbn [map snd] in P.
  eapply Permutation_in; [exact P| left; reflexivity].
Qed.

Lemma achunk_eq_dec' : forall c1 c2 : achunk, {c1 = c2} + {c1 <> c2}.
Proof. decide equality; first [apply Z.eq_dec| apply N.eq_dec]. Qed.

(* [comment removed for export] *)
Lemma nodup_range_len : forall (l : list Z) (N : nat), List.NoDup l -> Forall (fun k => 0 <= k < Z.of_nat N) l -> (length l <= N)%nat.
Proof.
  intros l N ND HF. rewrite <- (length_seq N 0), <- (length_map Z.of_nat). apply NoDup_incl_length; [exact ND|].
  intros k Hk. pose proof (proj1 (Forall_forall _ _) HF k Hk) as R. cbn beta in R.
  apply in_map_iff. exists (Z.to_nat k). split; [lia|]. apply in_seq. lia.
Qed.

(* [comment removed for export] *)
Lemma tmp_len_bound : forall R L st X m, alayout_ok L -> awf L st X -> AQdr R 0 0 L st X m -> Z.of_nat (length (qr_tmp R)) < 2^32.
Proof.
  intros R L st X m ALO WF (_ & _ & _ & _ & _ & _ & CP & _). pose proof CP as (_ & _ & _ & _ & NDB & BS & _ & _).
  assert (LEN : (length (qr_bslots R) <= Z.to_nat 458752)%nat).
  { apply nodup_range_len; [exact NDB|]. apply Forall_forall. intros k Hk. destruct (proj1 (BS k) Hk) as (bb & Hb & Sb & Cb & Kb).
    pose proof (busy_slot_geo L st X ALO WF bb Hb) as (_ & KR & G1 & G2 & (_ & G3 & _) & _). unfold xb_alloc, aslot_addr in G1, G2. rewrite Cb, Kb, size_of_class_24 in *.
    unfold K_FREEARR_OFF in G3. rewrite Z2Nat.id by (clear; lia). clear -KR G1 G2 G3. lia. }
  unfold qr_bslots in LEN. rewrite length_app, length_map, !length_app, length_map in LEN. clear -LEN. lia.
Qed.

(* [comment removed for export] *)
Lemma AREP_reqs : forall AQ AQ' AS AS' ADp AFp L st X m,
  AREP (mkAHoles AQ AS ADp AFp) L st X m -> AQ' L st X m -> (AS L st X m -> AS' L st X m) -> AREP (mkAHoles AQ' AS' ADp AFp) L st X m.
Proof.
  intros AQ AQ' AS AS' ADp AFp L st X m (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12) HQ HS.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
  split; [exact HQ|]. split; [exact (HS A7)|]. split; [exact A8|]. split; [exact A9|]. split; [exact A10|]. split; [exact A11| exact A12].
Qed.

(* [comment removed for export] *)
Lemma high_fake : forall L iv, alayout_ok L -> ATOP <= fst iv ->
     (snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
  /\ (snd iv <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= fst iv)
  /\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
  /\ (snd iv <= 0xc90f0 \/ 0xc90f0 + 8 <= fst iv) /\ (snd iv <= 0x602ca8 \/ 0x602ca8 + 16 <= fst iv)
  /\ (snd iv <= 0x602cb8 \/ 0x602cb8 + 8 <= fst iv) /\ (snd iv <= 0x602cd8 \/ 0x602cd8 + 8 <= fst iv)
  /\ (snd iv <= 0x1618b1 \/ 0x1618b1 + 1 <= fst iv) /\ (snd iv <= 0x15f798 \/ 0x15f798 + 4 <= fst iv).
Proof.
  intros L iv ALO HI. pose proof (ao_fake L ALO) as OF. pose proof (ao_dtls L ALO) as OD. unfold aobj in *. pose proof atop_range as AR.   (* [comment removed for export] *)
  assert (SF : shad (al_fake L) + shlen 11571200 <= 17594332446720) by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -OF AR; Z.div_mod_to_equations; lia).
  clear -HI OF OD SF AR. repeat split; lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section DoRec.
Variables (ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop)
          (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop)
          (RSEC : list achunk -> footprint -> Prop).
Let AHr := ARecyc1P.AHr ASECc AD AF.
Hypothesis HL : forall R cs, ahole_laws (AHr R cs).
Hypothesis SREC : srec_stmt ASECc RSEC.
(* [comment removed for export] *)
Hypothesis ADD : forall L m m' W, AD L m -> munch W m m' ->
  Forall (fun iv => forall a, fst iv <= a < snd iv ->
     ~ (0x1a1bc8 <= a < 0x5f1c10) /\ ~ (al_nodes L <= a < al_nodes L + 1048576) /\ ~ (al_store L <= a < al_store L + 8388608)) W -> AD L m'.
Hypothesis AFD : forall L LB m m' W, AF L LB m -> munch W m m' -> fake_untouched L W ->
  Forall (fun iv => snd iv <= al_t L + 48 \/ al_t L + 64 <= fst iv) W -> AF L LB m'.     (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis ASECc_perm : forall cs cs' L st X m, Permutation cs cs' -> ASECc cs L st X m -> ASECc cs' L st X m.
Hypothesis ASECc_wf1 : forall cs L st X m, ASECc cs L st X m -> Forall (sec_wf1 L) cs.
Hypothesis ASECc_disj : forall cs L st X m, ASECc cs L st X m -> sec_disjoint cs.
Hypothesis ASECc_nres : forall cs L st X m, ASECc cs L st X m -> 0 <= a_nres st /\ 8 * a_nres st <= 8388608.
Hypothesis RSEC_app : forall a b RNG, RSEC (a ++ b) RNG <-> RSEC a RNG /\ RSEC b RNG.
Hypothesis RSEC_perm' : forall a b RNG, Permutation a b -> RSEC a RNG -> RSEC b RNG.
Hypothesis RSEC_mono' : forall a RNG RNG', fp_le RNG RNG' -> RSEC a RNG -> RSEC a RNG'.
Hypothesis RSEC_arng : forall L RNG st, arng L RNG st -> RSEC (sec_chunks_of st) RNG.

Lemma SHO : forall R, srec_holes_ok (AQdr R 0 0) AD.
Proof. intros R. split; [intros; eapply AQdr_frameD; eassumption| exact ADD]. Qed.

(* [comment removed for export] *)
Variables (L : alayout) (lo TMP HI : Z) (LB : list ablock) (cbs : word) (RNG0 : footprint) (m0 : amem) (st0 : astate).
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Let SP : Z := bv_unsigned sp + -112.
Hypothesis ALO : alayout_ok L.
Hypothesis CEIL : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - DOREC_STACK.
Hypothesis SP47 : bv_unsigned sp <= 2^47.
Hypothesis TMPLO : bv_unsigned sp <= TMP.
Hypothesis TMPHI : TMP + 32 <= 2^47.
Hypothesis HHI : TMP + 32 <= HI.
Hypothesis RSTK0 : rng RNG0 lo (bv_unsigned sp - lo).
Hypothesis RTMP0 : rng RNG0 TMP 32.

(* [comment removed for export] *)
Definition dr_frame (junk8 : list byte) : list cell :=
  [CB 8 junk8; C8 (Z_to_bv 64 (al_t L + 208)); C8 cbs; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition st_keep (st : astate) : Prop :=
     a_live st = a_live st0 /\ a_next st = a_next st0 /\ a_qloc st = a_qloc st0 /\ a_qloc_bytes st = a_qloc_bytes st0
  /\ a_qglob st = a_qglob st0 /\ a_qglob_bytes st = a_qglob_bytes st0 /\ a_nres st = a_nres st0 /\ a_ptr_array st = a_ptr_array st0
  /\ a_space_beg st = a_space_beg st0.

(* [comment removed for export] *)
Definition drinv (R : qrconc) (st : astate) (X : aconc) (RNG : footprint) (m : amem) : Prop :=
     arng L RNG st /\ AREP (AHr R (csx st R)) L st X m /\ ablocks L st X LB /\ AF L LB m
  /\ RSEC (inflight R) RNG /\ mem_inv bsegs m /\ stk bsegs m lo SP /\ fp_le RNG0 RNG
  /\ munch [(0, bv_unsigned sp); (TMP, TMP + 32)]%Z m0 m /\ cpres L HI LB m0 m /\ st_keep st.

Lemma drinv_rngs : forall R st X RNG m, drinv R st X RNG m -> rng RNG lo (bv_unsigned sp - lo) /\ rng RNG TMP 32.
Proof. intros R st X RNG m (_ & _ & _ & _ & _ & _ & _ & FLE & _). split; (eapply rng_fp_le; [exact FLE|]); assumption. Qed.

(* [comment removed for export] *)
Definition thdr (T : list (abatch * qbatchc)) (tb : word) : list cell :=
  [C8 (Z_to_bv 64 (Z.of_nat (length T))); C8 (Z_to_bv 64 (qfirst L (map snd T))); C8 (Z_to_bv 64 (qlast L (map snd T))); C8 tb].

(* [comment removed for export] *)
Definition ms_in (pc : Z) (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (B cnt i : Z) (m : amem) : machine_state :=
  MS (mkR rax (Z_to_bv 64 SP) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 TMP) (Z_to_bv 64 837272) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 837336) (Z_to_bv 64 837960) (Z_to_bv 64 B) (Z_to_bv 64 137438953472) (Z_to_bv 64 cnt)
          (Z_to_bv 64 (B + 152 + 8 * i)) (Z_to_bv 64 (16 + cnt)) (Z_to_bv 64 (16 + i)) s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

(* [comment removed for export] *)
Definition batch_ok (R : qrconc) (kb : Z) (all : list (achunk * Z)) (T : list (abatch * qbatchc)) : Prop :=
  qr_tmp R = T /\ qr_pendb R = [kb] /\ Z.of_nat (length all) <= Q_BATCH /\ 0 <= kb.

(* [comment removed for export] *)
Lemma live_vs_inflight : forall st L X m A Bk mb ms n,
  ASECc ((sec_chunks_of st ++ A) ++ CSec mb ms n :: Bk) L st X m ->
  forall p mb' ms' n', (a_live st) !! p = Some (CSec mb' ms' n') -> mb' + ms' <= mb \/ mb + ms <= mb'.
Proof.
  intros st L0 X m A Bk mb ms n HS p mb' ms' n' Lp. destruct (ASECc_disj _ _ _ _ _ HS) as [ND DJ].
  pose proof (live_sec_in' st p _ _ _ Lp) as INl.
  assert (IN1 : In (CSec mb' ms' n') ((sec_chunks_of st ++ A) ++ CSec mb ms n :: Bk)) by (apply in_app_iff; left; apply in_app_iff; left; exact INl).
  assert (IN2 : In (CSec mb ms n) ((sec_chunks_of st ++ A) ++ CSec mb ms n :: Bk)) by (apply in_app_iff; right; left; reflexivity).
  assert (NE : CSec mb' ms' n' <> CSec mb ms n).
  { intros E. rewrite E in INl. apply (List.NoDup_remove_2 _ _ _ ND). apply in_app_iff. left. apply in_app_iff. left. exact INl. }
  destruct (DJ _ _ IN1 IN2 NE) as [D|D]; cbn [sec_mb sec_ms] in D; [left| right]; exact D.
Qed.

Lemma live_vs_hl : forall st L X m A Bk mb ms n hl,
  ASECc ((sec_chunks_of st ++ A) ++ CSec mb ms n :: Bk) L st X m ->
  ((mb <= hl /\ hl + 8 <= mb + ms) \/ (exists lms ln, In (CSec (hl - 24) lms ln) ((sec_chunks_of st ++ A) ++ Bk) /\ sec_wf1 L (CSec (hl - 24) lms ln))) ->
  forall p mb' ms' n', (a_live st) !! p = Some (CSec mb' ms' n') -> hl + 8 <= mb' + SEC_UOFF \/ mb' + ms' <= hl.
Proof.
  intros st L0 X m A Bk mb ms n hl HS HIN p mb' ms' n' Lp. destruct (ASECc_disj _ _ _ _ _ HS) as [ND DJ].
  pose proof (live_sec_in' st p _ _ _ Lp) as INl.
  assert (IN1 : In (CSec mb' ms' n') ((sec_chunks_of st ++ A) ++ CSec mb ms n :: Bk)) by (apply in_app_iff; left; apply in_app_iff; left; exact INl).
  unfold SEC_UOFF. destruct HIN as [[H1 H2]|(lms & ln & INh & SWh)].
  - destruct (live_vs_inflight st L0 X m A Bk mb ms n HS p mb' ms' n' Lp) as [D|D]; [right; clear -D H1; lia| left; clear -D H2; lia].
  - assert (IN2 : In (CSec (hl - 24) lms ln) ((sec_chunks_of st ++ A) ++ CSec mb ms n :: Bk)).
    { apply in_app_iff in INh. apply in_app_iff. destruct INh as [H|H]; [left; exact H| right; right; exact H]. }
    destruct (achunk_eq_dec' (CSec mb' ms' n') (CSec (hl - 24) lms ln)) as [E|NE].
    + injection E as -> -> ->. left. clear. lia.
    + destruct SWh as (_ & _ & _ & MSE & NB & NPR & _).
      pose proof (sec_facts ln ltac:(unfold AREQMAX in *; clear -NB; lia) NPR) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MSB). rewrite <- MSE in MSB.
      destruct (DJ _ _ IN1 IN2 NE) as [D|D]; cbn [sec_mb sec_ms] in D; [right; clear -D; lia| left; clear -D MSB; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dr_inner : forall {RT} (Q : RT -> footprint -> machine_state -> Prop) (es : list (achunk * Z)) (K : astate -> AM RT)
    (R : qrconc) st X RNG m (kb : Z) (all : list (achunk * Z)) (T : list (abatch * qbatchc)) (i : Z) (tb : word) junk8
    rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  drinv R st X RNG m -> batch_ok R kb all T -> qr_pend R = es -> es = skipn (Z.to_nat i) all -> es <> [] -> 0 <= i ->
  rw_cells bsegs m SP (dr_frame junk8) -> rw_cells bsegs m TMP (thdr T tb) ->
  u64arr bsegs m (abatch_addr L kb + 24) (map (ehdr L) all) ->
  (forall st1 X1 RNG1 m1 junk8' rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     drinv (qr_drop R []) st1 X1 RNG1 m1 ->
     rw_cells bsegs m1 SP (dr_frame junk8') -> rw_cells bsegs m1 TMP (thdr T tb) ->
     implS bsegs RNG1 (aembed ATOP (K st1)) (epostF Q)
           (ms_in adorec_after rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (abatch_addr L kb) (Z.of_nat (length all)) (Z.of_nat (length all)) m1)) ->
  implS bsegs RNG (aembed ATOP (recycle_chunks st (map fst es) K)) (epostF Q)
        (ms_in adorec_lin rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (abatch_addr L kb) (Z.of_nat (length all)) i m).
Proof.
  intros RT Q es. induction es as [|e es IH]; intros K R st X RNG m kb all T i tb junk8 rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    INV BOK EP ES NE I0 FR TH ARR KONT; [congruence|].
  pose proof INV as (ARNG & AR & BL & HF & RS & MI & ST & FLE & MU0 & CP0 & SK). destruct (drinv_rngs _ _ _ _ _ INV) as [RSTK RTMP].
  destruct BOK as (ET & EB & ALLB & KB0).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. (try pose proof atop_range as ATR). unfold Q_BATCH in ALLB.
  assert (SPE : SP = bv_unsigned sp + -112) by reflexivity.
  assert (IL : i < Z.of_nat (length all)).
  { destruct (Z.lt_ge_cases i (Z.of_nat (length all))) as [H|H]; [exact H| exfalso]. rewrite skipn_all2 in ES by lia. discriminate. }
  assert (NTH : nth_error (map (ehdr L) all) (Z.to_nat i) = Some (ehdr L e)).
  { rewrite nth_error_map. replace (nth_error all (Z.to_nat i)) with (nth_error (skipn (Z.to_nat i) all) 0) by (rewrite nth_error_skipn, Nat.add_0_r; reflexivity).
    rewrite <- ES. reflexivity. }
  set (B := abatch_addr L kb) in *.
  (* [comment removed for export] *)
  pose proof AR as AR0. destruct AR0 as (WF & _).
  destruct (pendb_busy L st X R m kb ltac:(destruct AR as (_ & _ & _ & _ & _ & HQ & _); exact HQ) EB) as (nb & bb1 & bctx & bl1 & bl2 & XBB).
  pose proof (busy_slot_geo L st X ALO WF (bany BBatch K_BATCH_CLASS kb nb bb1 bctx) ltac:(rewrite XBB; apply in_app_iff; right; left; reflexivity)) as BG.
  unfold xb_alloc in BG. cbn [xb_class xb_slot bany] in BG. rewrite size_of_class_24 in BG. unfold abatch_addr in B. fold B in BG.
  destruct BG as (_ & _ & BG1 & BG2 & (BG3a & BG3 & BG3b) & BG4 & BG5 & BG6 & BG7).
  pose proof (u64arr_read bsegs m (B + 24) _ i (ehdr L e) (wa (B + 152 + 8 * i + -128)) ARR NTH I0 ltac:(f_equal; lia)) as RDV.
  assert (RB24 : rng RNG (B + 152 + 8 * i + -128) 8).
  { destruct ARNG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RCLS & _).
    destruct (RCLS K_BATCH_CLASS (K24)) as (R1 & _). eapply rng_sub; [exact R1| |]; clear -BG1 BG2 BG3 I0 IL ALLB; lia. }
  unfold ms_in, adorec_lin. iprefix.
  step.                                     (* [comment removed for export] *)
  clear RDV RB24.
  zstep.                                    (* [comment removed for export] *)
  step.                                     (* [comment removed for export] *)
  apply evtF_done.
  (* [comment removed for export] *)
  pose proof FR as CBC. unfold dr_frame in CBC. rw_split CBC 1%nat CB8 CBC. rw_split CBC 2%nat CBC CBR. clear CB8 CBR.
  (* [comment removed for export] *)
  assert (POSTK : forall stX X' RNG' m' (W : list (Z * Z)) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    fp_le RNG RNG' -> munch W m m' -> mem_inv bsegs m' -> stk bsegs m' lo SP ->
    (forall iv, In iv W -> (lo <= fst iv /\ snd iv <= SP) \/ (forall b, In b (x_busy X') -> xb_st b = BBatch -> xb_alloc L b + size_of_class (xb_class b) <= fst iv \/ snd iv <= xb_alloc L b) /\ 0 <= fst iv /\ snd iv <= ATOP) ->
    np_fp L HI LB W -> fake_untouched L W -> (AF L LB m -> AF L LB m') ->
    AREP (AHr (qr_drop R es) (csx stX (qr_drop R es))) L stX X' m' -> arng L RNG' stX ->
    (forall b, In b (x_busy X') -> In b (x_busy X)) -> (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')) ->
    a_live stX = a_live st -> a_next stX = a_next st -> a_qloc stX = a_qloc st -> a_qloc_bytes stX = a_qloc_bytes st ->
    a_qglob stX = a_qglob st -> a_qglob_bytes stX = a_qglob_bytes st -> a_nres stX = a_nres st -> a_ptr_array stX = a_ptr_array st -> a_space_beg stX = a_space_beg st ->
    RSEC (inflight (qr_drop R es)) RNG' ->
    implS bsegs RNG' (aembed ATOP (recycle_chunks stX (map fst es) K)) (epostF Q)
          (MS (mkR (Z_to_bv 64 219872) (Z_to_bv 64 SP) gp (Z_to_bv 64 ATP) t0' t1' t2' (Z_to_bv 64 TMP) (Z_to_bv 64 837272) a0' a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 837336) (Z_to_bv 64 837960) (Z_to_bv 64 B) (Z_to_bv 64 137438953472) (Z_to_bv 64 (Z.of_nat (length all)))
                   (Z_to_bv 64 (B + 152 + 8 * i)) (Z_to_bv 64 (16 + Z.of_nat (length all))) (Z_to_bv 64 (16 + i)) s10 s11 t3' t4' t5' t6')
              F (ret_pc (Z_to_bv 64 219872)) fc None m' (seg_rom bsegs))).
  { intros stX X' RNG' m' W t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'.
    intros FPLE MU MI' ST' WK NP FU HF' AR' ARNG' XS XL L1 L2 L3 L4 L5 L6 L8 L9 L10 RS'. (try pose proof atop_range as ATR).
    replace (ret_pc (Z_to_bv 64 219872)) with (Z_to_bv 64 219872 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    pose proof AR' as AR1. destruct AR1 as (WF' & _ & _ & _ & _ & HQ' & _). cbn [ah_quar AHr ARecyc1P.AHr] in HQ'.
    destruct (pendb_busy L stX X' (qr_drop R es) m' kb HQ' EB) as (nb' & bb1' & bctx' & bl1' & bl2' & XBB').
    assert (INB : In (bany BBatch K_BATCH_CLASS kb nb' bb1' bctx') (x_busy X')) by (rewrite XBB'; apply in_app_iff; right; left; reflexivity).
    (* [comment removed for export] *)
    assert (DJF : disjoint_from W SP 112).
    { apply ARepQP.disjoint_from_Forall. apply Forall_forall. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|(_ & _ & HI')]; [left; exact H2| left; clear -HI' CEIL LO SPE; lia]. }
    assert (DJT : disjoint_from W TMP 32).
    { apply ARepQP.disjoint_from_Forall. apply Forall_forall. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|(_ & _ & HI')]; [left; clear -H2 TMPLO SPE; lia| left; clear -HI' CEIL LO TMPLO SPE; lia]. }
    assert (DJB : disjoint_from W (B + 24) (8 * Z.of_nat (length (map (ehdr L) all)))).
    { rewrite length_map. apply ARepQP.disjoint_from_Forall. apply Forall_forall. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|(HB & _ & _)].
      - right. clear -H1 BG5 CEIL LO SPE ALLB. lia.
      - specialize (HB _ INB eq_refl). unfold xb_alloc in HB. cbn [xb_class xb_slot bany] in HB. rewrite size_of_class_24 in HB. fold B in HB.
        clear -HB ALLB. lia. }
    pose proof (cells_frameD _ _ _ _ _ FR MU DJF) as FR'. pose proof (cells_frameD _ _ _ _ _ TH MU DJT) as TH'. pose proof (u64arr_frameD _ _ _ _ _ ARR MU DJB) as ARR'.
    assert (INV' : drinv (qr_drop R es) stX X' RNG' m').
    { unfold drinv. split; [exact ARNG'|]. split; [exact AR'|].
      split; [eapply ablocks_mono; [exact BL| exact XL| intros p mb ms n Hp; rewrite L1; exact Hp]|].
      split; [exact (HF' HF)|]. split; [exact RS'|]. split; [exact MI'|]. split; [exact ST'|].
      split; [intros b j Hb; apply FPLE, FLE, Hb|].
      split. { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. unfold sub_fp. intros x Hx. cbn [outside] in Hx. destruct Hx as (Hx1 & Hx2 & _).
               apply outside_of_In. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|(_ & HZ & HI')]; [clear -Hx1 H1 H2 CEIL LO SPR SPE; lia| clear -Hx1 HZ HI' CEIL LO SPR SPE; lia]. }
      split; [eapply cpres_trans; [exact CP0| eapply cpres_of_munch; [exact MU| exact NP]]|].
      destruct SK as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9). unfold st_keep. rewrite L1, L2, L3, L4, L5, L6, L8, L9, L10.
      repeat (split; [assumption|]). exact K9. }
    iprefix.
    zstep. zstep.                           (* [comment removed for export] *)
    setreg 25%Z (Z_to_bv 64 (16 + (i + 1))) ltac:(f_equal; clear; lia).
    setreg 23%Z (Z_to_bv 64 (B + 152 + 8 * (i + 1))) ltac:(f_equal; clear; lia).
    step. if_cases KB; zify_cond KB.        (* [comment removed for export] *)
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KB by (clear -I0 IL ALLB; lia).
      assert (NE' : es <> []).
      { intros ->. apply KB. assert (LEN1 : length (skipn (Z.to_nat i) all) = 1%nat) by (rewrite <- ES; reflexivity). rewrite length_skipn in LEN1. clear -LEN1 IL I0. lia. }
      apply evtF_done.
      eapply (IH K (qr_drop R es) stX X' RNG' m' kb all T (i + 1) tb); try eassumption;
        try lazymatch goal with
        | |- batch_ok _ _ _ _ => unfold batch_ok; rewrite <- ET, <- EB; unfold qr_drop; cbn; repeat split; try reflexivity; assumption
        | |- qr_pend _ = _ => reflexivity
        | |- es = _ => replace (Z.to_nat (i + 1)) with (1 + Z.to_nat i)%nat by (clear -I0; lia); rewrite <- skipn_skipn, <- ES; reflexivity
        | |- 0 <= _ => clear -I0; lia
        end.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KB by (clear -I0 IL ALLB; lia).
      assert (E0 : es = []).
      { destruct es as [|e2 es2]; [reflexivity| exfalso].
        assert (LEN1 : (2 <= length (skipn (Z.to_nat i) all))%nat) by (rewrite <- ES; cbn; lia). rewrite length_skipn in LEN1. clear -LEN1 IL I0 KB. lia. }
      subst es. cbn [map recycle_chunks].
      apply evtF_done. replace (i + 1) with (Z.of_nat (length all)) by (clear -KB; lia).
      eapply KONT; [exact INV'| exact FR'| exact TH']. }
  (* [comment removed for export] *)
  destruct e as [ch kk]. destruct ch as [c n| mb ms n]; cbn [map fst]; [rewrite recycle_chunks_prim| rewrite recycle_chunks_sec].
  - (* [comment removed for export] *)
    eapply arecyc1; try lazymatch goal with
      | |- forall R0 cs0, ahole_laws _ => exact HL
      | |- alayout_ok _ => exact ALO
      | |- arng _ _ _ => exact ARNG
      | |- AREP _ _ _ _ _ => exact AR
      | |- qr_pend _ = _ => exact EP
      | |- mem_inv _ _ => exact MI
      | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); exact ST
      | |- ATOP <= _ => atop_facts; exact CEIL
      | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); clear -LO CEIL SPE; lia
      | |- rw_cells _ _ _ _ => exact CBC
      | |- bv_unsigned _ <= _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); clear; lia
      | |- _ + 16 <= _ => clear -SP47 CEIL LO SPE; lia
      | |- rng _ lo _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); eapply rng_sub; [exact RSTK| clear; lia| clear -CEIL LO SPE; lia]
      | |- rng _ _ 16 => eapply rng_sub; [exact RSTK| clear -CEIL LO SPE; lia| clear -CEIL LO SPE; lia]
      | |- @eq word _ _ => reflexivity
      end.
    intros stX X' RNG' ms' RET.
    destruct RET as (FPLE & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & mfa' & -> & MU & WM & MI' & ST' & MFB & AR' & ARNG' & CIN
                     & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & GC & MU1 & AU1 & XS & XL).
    rewrite unsigned_lit in MU, ST' by (clear -SPR CEIL LO; lia).
    pose proof AR as AR1. destruct AR1 as (WF0 & _).
    destruct (pend_head_busy L st X R m c n kk es ltac:(destruct AR as (_ & _ & _ & _ & _ & HQ & _); exact HQ) EP) as (b1 & ctx & l1 & l2 & XB).
    pose proof WF0 as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC c (proj1 (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF0))) as (_ & _ & _ & _ & A5 & A6 & _).
    eapply (POSTK stX X' RNG' m' _ t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6');
      [exact FPLE| exact MU| exact MI'| exact ST'| | | | | | exact ARNG'| exact XS| exact XL| exact L1| exact L2| exact L3| exact L4| exact L5| exact L6| exact L8| exact L9| exact L10|].
    + (* [comment removed for export] *)
      intros iv Hiv. destruct (rec_W_cases L st X SP c kk n b1 ctx l1 l2 _ _ mfa' iv ALO WF0 XB A5 (proj1 A6) ltac:(split; [exact (proj1 MFB)| exact (proj2 MFB)]) Hiv) as [E|[SL|LP]].
      * left. subst iv. cbn [fst snd]. clear -CEIL LO SPE. lia.
      * right. split; [| split; [destruct (busy_slot_geo L st X ALO WF0 _ ltac:(rewrite XB; apply in_app_iff; right; left; reflexivity)) as (_ & _ & _ & _ & _ & G4 & _); unfold xb_alloc in G4; cbn [xb_class xb_slot bany] in G4; clear -G4 SL; lia|]].
        -- intros b Hb Sb. pose proof (XS b Hb) as HbX.
           assert (NEQ : c <> xb_class b \/ kk <> xb_slot b).
           { destruct (Z.eq_dec c (xb_class b)) as [EC|NC]; [right| left; exact NC]. intros EK.
             apply (In_X_g X BQuar c kk n b1 ctx l1 l2 XB) in HbX. destruct HbX as [Hl| ->]; [| cbn in Sb; discriminate].
             exact (key_fresh_g L st X BQuar c kk n b1 ctx l1 l2 XB WF0 b Hl (eq_sym EC) (eq_sym EK)). }
           destruct (busy_slot_geo L st X ALO WF0 b (XS b Hb)) as (CLB & KBb & _).
           pose proof (slots_sep_any L st X c kk (xb_class b) (xb_slot b) ALO WF0 (proj1 (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF0)) CLB
                         (proj2 (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF0)) KBb NEQ) as D.
           unfold xb_alloc. clear -D SL. lia.
        -- destruct (busy_slot_geo L st X ALO WF0 _ ltac:(rewrite XB; apply in_app_iff; right; left; reflexivity)) as (_ & _ & _ & _ & _ & _ & G5 & _).
           unfold xb_alloc in G5. cbn [xb_class xb_slot bany] in G5. clear -G5 SL. lia.
      * right. split; [| exact (conj (proj1 LP) (proj1 (proj2 LP)))]. intros b Hb _. exact (lowpiece_vs_slot L st X c b iv ALO WF0 (proj1 (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF0)) (XS b Hb) LP).
    + (* [comment removed for export] *)
      eapply (np_rec_W L st X LB HI lo SP c kk n b1 ctx l1 l2); [exact ALO| exact WF0| exact BL| exact XB| exact A5| exact (proj1 A6)| clear -MFB; lia| atop_facts; exact CEIL| clear -LO SPE; lia| clear -HHI TMPLO SPE; lia].
    + eapply (rec_W_fake L st X lo); [exact ALO| exact WF0| exact XB| exact A5| exact (proj1 A6)| clear -MFB; lia| atop_facts; exact CEIL| clear -LO SPE; lia].
    + intros HF0. eapply (hf_frame _ (HL R (csx st R)) L LB m m'); [exact HF0| exact MU| exact WM|].
      eapply (rec_W_fake L st X lo); [exact ALO| exact WF0| exact XB| exact A5| exact (proj1 A6)| clear -MFB; lia| atop_facts; exact CEIL| clear -LO SPE; lia].
    + (* [comment removed for export] *)
      replace (csx stX (qr_drop R es)) with (csx st R); [exact AR'|].
      unfold csx, inflight, secsT, qr_drop. cbn [qr_tmp qr_pend]. rewrite EP, esecs_cons_prim, (sec_chunks_of_eq st stX L1 L3 L5). reflexivity.
    + unfold inflight, secsT, qr_drop in RS |- *. cbn [qr_tmp qr_pend] in RS |- *. rewrite EP, esecs_cons_prim in RS. eapply RSEC_mono'; [exact FPLE| exact RS].
  - (* [comment removed for export] *)
    pose proof AR as AR1. destruct AR1 as (WF0 & _ & _ & _ & _ & HQ0 & HS0 & _). cbn [ah_quar ah_sec AHr ARecyc1P.AHr] in HQ0, HS0.
    assert (CSE : csx st R = (sec_chunks_of st ++ secsT R) ++ CSec mb ms n :: esecs es).
    { unfold csx, inflight. rewrite EP, esecs_cons_sec, app_assoc. reflexivity. }
    pose proof (ASECc_wf1 _ _ _ _ _ HS0) as WF1. rewrite CSE in WF1. apply Forall_app in WF1. destruct WF1 as [_ WF1]. pose proof (Forall_inv WF1) as SW.
    pose proof (ASECc_nres _ _ _ _ _ HS0) as [NR0 NR1].
    rewrite CSE in AR, HS0.
    assert (RSC : RSEC ((sec_chunks_of st ++ secsT R) ++ CSec mb ms n :: esecs es) RNG).
    { apply (proj2 (RSEC_app _ _ _)). split; [apply (proj2 (RSEC_app _ _ _)); split; [exact (RSEC_arng _ _ _ ARNG)|]|];
        unfold inflight in RS; rewrite EP, esecs_cons_sec in RS; apply (proj1 (RSEC_app _ _ _)) in RS; destruct RS as [RS1 RS2]; [exact RS1|].
      exact RS2. }
    eapply (SREC (AQdr R 0 0) AD AF (sec_chunks_of st ++ secsT R) (esecs es) _ (fun st1 => recycle_chunks st1 (map fst es) K) Q L RNG);
      try lazymatch goal with
      | |- srec_holes_ok _ _ => exact (SHO R)
      | |- alayout_ok _ => exact ALO
      | |- arng _ _ _ => exact ARNG
      | |- RSEC _ _ => exact RSC
      | |- AREP _ _ _ _ _ => exact AR
      | |- mem_inv _ _ => exact MI
      | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); exact ST
      | |- ATOP <= _ => atop_facts; exact CEIL
      | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); clear -LO CEIL SPE; lia
      | |- bv_unsigned _ <= 2 ^ 47 => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); clear -SP47 SPE CEIL LO; lia
      | |- 4096 <= bv_unsigned _ => rewrite unsigned_lit by (clear; lia); clear; lia
      | |- rng _ lo _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); eapply rng_sub; [exact RSTK| clear; lia| clear -CEIL LO SPE; lia]
      | |- @eq word _ _ => reflexivity
      end.
    intros st' RNG' ms' SR. unfold srec_ret in SR.
    destruct SR as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & hl & -> & STE & HLOK & HLIN & MU & MI' & STK' & AR' & FS & ARNG' & RS').
    rewrite unsigned_lit in MU, STK' by (clear -SPR CEIL LO SPE; lia). subst st'.
    pose proof (fstepS_le _ _ _ _ FS) as FPLE.
    assert (AR'' : AREP (AHr (qr_drop R es) (csx (set_nsec (a_nsec st - 1) st) (qr_drop R es))) L (set_nsec (a_nsec st - 1) st) X m').
    { replace (csx (set_nsec (a_nsec st - 1) st) (qr_drop R es)) with ((sec_chunks_of st ++ secsT R) ++ esecs es).
      2:{ unfold csx, inflight, secsT, qr_drop. cbn [qr_tmp qr_pend]. rewrite (sec_chunks_of_eq st (set_nsec (a_nsec st - 1) st) eq_refl eq_refl eq_refl), app_assoc. reflexivity. }
      unfold AHr, ARecyc1P.AHr. eapply AREP_reqs; [exact AR'| | intros HS1; exact HS1].
      destruct AR' as (_ & _ & _ & _ & _ & HQ1 & _). cbn [ah_quar] in HQ1. eapply AQdr_drop_sec; [exact HQ1| exact EP]. }
    pose proof (live_vs_inflight st L X m _ _ mb ms n HS0) as DJ. pose proof (live_vs_hl st L X m _ _ mb ms n hl HS0 HLIN) as HLS.
    destruct HLOK as (HK1 & HK2 & HK3).
    eapply (POSTK (set_nsec (a_nsec st - 1) st) X RNG' m' _ t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6');
      [exact FPLE| exact MU| exact MI'| exact STK'| | | | | exact AR''| exact ARNG'| intros b Hb; exact Hb| intros b p Hb _; exact Hb
      | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity|].
    + intros iv Hiv. destruct (srec_W_pieces L st X lo SP mb ms n (a_nres st) hl iv ALO WF0 SW (conj HK1 (conj HK2 HK3)) NR0 NR1 ltac:(atop_facts; exact CEIL) ltac:(clear -LO SPE; lia) Hiv) as [WK _].
      destruct WK as [WK|(WB & WZ & WC)]; [left; exact WK| right]. split; [intros b Hb _; exact (WB b Hb)| exact (conj WZ WC)].
    + eapply (np_srec_W L st X LB HI lo SP mb ms n (a_nres st) hl); [exact ALO| exact WF0| exact BL| exact SW| exact DJ| exact HK1| exact HK2| exact HK3| exact HLS| exact NR0| exact NR1
        | atop_facts; exact CEIL| clear -LO SPE; lia| clear -HHI TMPLO SPE; lia].
    + apply fake_untouched_of. intros iv Hiv.
      exact (proj2 (srec_W_pieces L st X lo SP mb ms n (a_nres st) hl iv ALO WF0 SW (conj HK1 (conj HK2 HK3)) NR0 NR1 ltac:(atop_facts; exact CEIL) ltac:(clear -LO SPE; lia) Hiv)).
    + intros HF0. eapply AFD; [exact HF0| exact MU| |].
      * apply fake_untouched_of. intros iv Hiv.
        exact (proj2 (srec_W_pieces L st X lo SP mb ms n (a_nres st) hl iv ALO WF0 SW (conj HK1 (conj HK2 HK3)) NR0 NR1 ltac:(atop_facts; exact CEIL) ltac:(clear -LO SPE; lia) Hiv)).
      * apply Forall_forall. intros iv Hiv. exact (srec_W_t48 L st X lo SP mb ms n (a_nres st) hl iv ALO SW (conj HK1 (conj HK2 HK3)) NR0 NR1 ltac:(atop_facts; exact CEIL) ltac:(clear -LO SPE; lia) Hiv).
    + unfold inflight, secsT, qr_drop. cbn [qr_tmp qr_pend]. apply (proj1 (RSEC_app _ _ _)) in RS'. destruct RS' as [RS3 RS4].
      apply (proj1 (RSEC_app _ _ _)) in RS3. destruct RS3 as [_ RS3]. apply (proj2 (RSEC_app _ _ _)). split; [exact RS3| exact RS4].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ms_out (pc : Z) (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs4 xs6 xs7 xs8 xs9 t3 t4 t5 t6 : word) (m : amem) : machine_state :=
  MS (mkR rax (Z_to_bv 64 SP) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 TMP) (Z_to_bv 64 837272) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 837336) (Z_to_bv 64 837960) xs4 (Z_to_bv 64 137438953472) xs6 xs7 xs8 xs9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Lemma dr_after : forall {RT} (Q : RT -> footprint -> machine_state -> Prop) (KK : astate -> AM RT)
    (R : qrconc) st X RNG m (kb : Z) (T : list (abatch * qbatchc)) (tb : word) junk8
    rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 xs7 xs8 xs9 t3 t4 t5 t6,
  drinv R st X RNG m -> qr_tmp R = T -> qr_pendb R = [kb] -> qr_pend R = [] ->
  rw_cells bsegs m SP (dr_frame junk8) -> rw_cells bsegs m TMP (thdr T tb) ->
  (forall st1 X1 RNG1 m1 junk8' rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     drinv (qr_unbatch R) st1 X1 RNG1 m1 ->
     rw_cells bsegs m1 SP (dr_frame junk8') -> rw_cells bsegs m1 TMP (thdr T tb) ->
     implS bsegs RNG1 (aembed ATOP (KK st1)) (epostF Q)
           (ms_out adorec_chk rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (abatch_addr L kb)) xs6 xs7 xs8 xs9 t3' t4' t5' t6' m1)) ->
  implS bsegs RNG (aembed ATOP (cache_dealloc st K_BATCH_CLASS KK)) (epostF Q)
        (ms_out adorec_after rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (abatch_addr L kb)) xs6 xs7 xs8 xs9 t3 t4 t5 t6 m).
Proof.
  intros RT Q KK R st X RNG m kb T tb junk8 rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 xs6 xs7 xs8 xs9 t3 t4 t5 t6 INV ET EB EP FR TH KONT.
  pose proof INV as (ARNG & AR & BL & HF & RS & MI & ST & FLE & MU0 & CP0 & SK). destruct (drinv_rngs _ _ _ _ _ INV) as [RSTK RTMP].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. (try pose proof atop_range as ATR).
  assert (SPE : SP = bv_unsigned sp + -112) by reflexivity.
  pose proof AR as AR0. destruct AR0 as (WF & _ & INST & _). pose proof (proj1 INST) as ISB. change (AINSTANCE + 32) with 837304 in ISB.
  pose proof (alayout_space L ALO) as (SB1 & SB2 & _ & SB4).
  set (B := abatch_addr L kb) in *.
  (* [comment removed for export] *)
  destruct (pendb_busy L st X R m kb ltac:(destruct AR as (_ & _ & _ & _ & _ & HQ & _); exact HQ) EB) as (nb & bb1 & bctx & bl1 & bl2 & XBB).
  pose proof (busy_slot_geo L st X ALO WF (bany BBatch K_BATCH_CLASS kb nb bb1 bctx) ltac:(rewrite XBB; apply in_app_iff; right; left; reflexivity)) as BG.
  unfold xb_alloc in BG. cbn [xb_class xb_slot bany] in BG. rewrite size_of_class_24 in BG. unfold abatch_addr in B. fold B in BG.
  destruct BG as (_ & _ & BG1 & BG2 & (BG3a & BG3 & BG3b) & BG4 & BG5 & BG6 & BG7).
  assert (ER24 : aregion L K_BATCH_CLASS = al_space_beg L + 24 * 4294967296) by (unfold aregion, K_REGION, K_BATCH_CLASS; clear; lia).
  unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
  assert (RI8 : rng RNG 837304 8) by (destruct ARNG as (R1 & _); eapply rng_sub; [exact R1| clear; lia| clear; lia]).
  pose proof FR as CBC. unfold dr_frame in CBC. rw_split CBC 1%nat CB8 CBC. rw_split CBC 1%nat CBC CBR. clear CB8 CBR.
  unfold ms_out, adorec_after. iprefix.
  step.                                                    (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by (clear -BG4 BG5 SB4 CEIL; lia); [exfalso; clear -K1 BG1 BG3a; lia|].   (* [comment removed for export] *)
  zstep.                                                   (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear -BG4 BG5 SB1 SB2 SB4 CEIL; lia); [exfalso; clear -K2 BG2 BG3 BG3b; lia|].   (* [comment removed for export] *)
  step.                                                    (* [comment removed for export] *)
  zstep. zstep. zstep.                                     (* [comment removed for export] *)
  setreg 12 (Z_to_bv 64 K_BATCH_CLASS) ltac:(f_equal; replace (B - al_space_beg L) with (24 * 4294967296 + (B - aregion L K_BATCH_CLASS)) by (clear -ER24; lia);
                                          symmetry; unfold K_BATCH_CLASS in *; apply class_of_offset; [clear; lia| change (2^32) with 4294967296; clear -BG1 BG2 BG3; lia]).
  step. step.                                              (* [comment removed for export] *)
  step.                                                    (* [comment removed for export] *)
  apply evtF_done.
  eapply acdealloc24; try lazymatch goal with
      | |- forall R0 cs0, ahole_laws _ => exact HL
      | |- alayout_ok _ => exact ALO
      | |- arng _ _ _ => exact ARNG
      | |- AREP _ _ _ _ _ => exact AR
      | |- qr_pendb _ = _ => exact EB
      | |- qr_pend _ = _ => exact EP
      | |- mem_inv _ _ => exact MI
      | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); exact ST
      | |- ATOP <= _ => atop_facts; exact CEIL
      | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); clear -LO CEIL SPE; lia
      | |- rng _ lo _ => rewrite unsigned_lit by (clear -SPR CEIL LO SPE; lia); eapply rng_sub; [exact RSTK| clear; lia| clear -CEIL LO SPE; lia]
      | |- @eq word _ _ => reflexivity
      end.
  intros stX X' RNG' ms' RET.
  destruct RET as (FPLE & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & mfa' & -> & MU & WM & MI' & ST' & MFB & AR' & ARNG' & CIN
                   & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & GC & XS & XL).
  rewrite unsigned_lit in MU, ST' by (clear -SPR CEIL LO; lia). (try pose proof atop_range as ATR).
  replace (ret_pc (Z_to_bv 64 219928)) with (Z_to_bv 64 219928 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  pose proof WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC K_BATCH_CLASS (K24)) as (_ & _ & _ & _ & A5 & A6 & _).
  assert (WK : forall iv, In iv (cd_W L SP K_BATCH_CLASS (c_num_freed (get_cls st K_BATCH_CLASS)) (c_mapped_free_array (get_cls st K_BATCH_CLASS)) mfa') ->
                          (lo <= fst iv /\ snd iv <= SP) \/ (0 <= fst iv /\ snd iv <= ATOP)).
  { intros iv Hiv. destruct (cd_W_cases L SP K_BATCH_CLASS _ _ mfa' iv ALO (K24) A5 (proj1 A6) ltac:(split; [exact (proj1 MFB)| exact (proj2 MFB)]) Hiv) as [->|(P0 & P1 & _)];
      [left; cbn [fst snd]; clear -LO SPE; lia| right; exact (conj P0 P1)]. }
  assert (DJF : disjoint_from (cd_W L SP K_BATCH_CLASS (c_num_freed (get_cls st K_BATCH_CLASS)) (c_mapped_free_array (get_cls st K_BATCH_CLASS)) mfa') SP 112).
  { apply ARepQP.disjoint_from_Forall. apply Forall_forall. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|[_ H2]]; [left; exact H2| left; clear -H2 CEIL LO SPE; lia]. }
  assert (DJT : disjoint_from (cd_W L SP K_BATCH_CLASS (c_num_freed (get_cls st K_BATCH_CLASS)) (c_mapped_free_array (get_cls st K_BATCH_CLASS)) mfa') TMP 32).
  { apply ARepQP.disjoint_from_Forall. apply Forall_forall. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|[_ H2]]; [left; clear -H2 TMPLO SPE; lia| left; clear -H2 CEIL LO TMPLO SPE; lia]. }
  pose proof (cells_frameD _ _ _ _ _ FR MU DJF) as FR'. pose proof (cells_frameD _ _ _ _ _ TH MU DJT) as TH'.
  assert (INV' : drinv (qr_unbatch R) stX X' RNG' m').
  { unfold drinv. split; [exact ARNG'|].
    split. { replace (csx stX (qr_unbatch R)) with (csx st R); [exact AR'|].
             unfold csx, inflight, secsT, qr_unbatch. cbn [qr_tmp qr_pend]. rewrite EP, (sec_chunks_of_eq st stX L1 L3 L5). reflexivity. }
    split; [eapply ablocks_mono; [exact BL| exact XL| intros p mb ms n Hp; rewrite L1; exact Hp]|].
    split. { eapply (hf_frame _ (HL R (csx st R)) L LB m m'); [exact HF| exact MU| exact WM|].
             eapply (cd_W_fake L lo); [exact ALO| exact (K24)| exact A5| exact (proj1 A6)| clear -MFB; lia| atop_facts; exact CEIL| clear -LO SPE; lia]. }
    split. { unfold inflight, secsT, qr_unbatch in RS |- *. cbn [qr_tmp qr_pend] in RS |- *. rewrite EP in RS. eapply RSEC_mono'; [exact FPLE| exact RS]. }
    split; [exact MI'|]. split; [exact ST'|]. split; [intros b j Hb; apply FPLE, FLE, Hb|].
    split. { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. unfold sub_fp. intros x Hx. cbn [outside] in Hx. destruct Hx as (Hx1 & Hx2 & _).
             apply outside_of_In. intros iv Hiv. destruct (WK iv Hiv) as [[H1 H2]|[HZ H2]]; [clear -Hx1 H1 H2 CEIL LO SPR SPE; lia| clear -Hx1 HZ H2 CEIL LO SPR SPE; lia]. }
    split. { eapply cpres_trans; [exact CP0|]. eapply cpres_of_munch; [exact MU|].
             eapply (np_cd_W L st X LB HI lo SP); [exact ALO| exact WF| exact BL| exact (K24)| exact A5| exact (proj1 A6)| clear -MFB; lia| atop_facts; exact CEIL| clear -LO SPE; lia| clear -HHI TMPLO SPE; lia]. }
    destruct SK as (K1' & K2' & K3 & K4 & K5 & K6 & K7 & K8 & K9). unfold st_keep. rewrite L1, L2, L3, L4, L5, L6, L8, L9, L10.
    repeat (split; [assumption|]). exact K9. }
  iprefix. apply evtF_done.
  eapply KONT; [exact INV'| exact FR'| exact TH'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma map_fst_combine : forall {A B} (l : list A) (l' : list B), length l' = length l -> map fst (combine l l') = l.
Proof. induction l as [|x l IH]; intros [|y l'] LEN; cbn in *; try reflexivity; try lia. rewrite IH by lia. reflexivity. Qed.

Lemma qlast_cons_ne : forall q (qs : list qbatchc), qs <> [] -> qlast L (q :: qs) = qlast L qs.
Proof.
  intros q qs NE. unfold qlast, qaddrs. cbn [map]. destruct qs as [|q' qs']; [congruence|]. cbn [map]. 
  generalize (abatch_addr L (qb_slot q')) (map (fun q0 : qbatchc => abatch_addr L (qb_slot q0)) qs'). clear. intros a l. revert a. induction l; intros; reflexivity.
Qed.

Definition qr_done (R : qrconc) : qrconc := mkQR (qr_loc R) (qr_glob R) (qr_ia R) [] [] [] (qr_qpend R).

Lemma dr_outer : forall {RT} (Q : RT -> footprint -> machine_state -> Prop) (T : list (abatch * qbatchc)) (K : astate -> AM RT)
    (R : qrconc) st X RNG m (tb : word) junk8 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 xs4 xs6 xs7 xs8 xs9 t3 t4 t5 t6,
  drinv R st X RNG m -> qr_tmp R = T -> qr_pendb R = [] -> qr_pend R = [] -> T <> [] ->
  rw_cells bsegs m SP (dr_frame junk8) -> rw_cells bsegs m TMP (thdr T tb) ->
  (forall st1 X1 RNG1 m1 junk8' (tb' : word) rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' xs4' xs6' xs7' xs8' xs9' t3' t4' t5' t6',
     drinv (qr_done R) st1 X1 RNG1 m1 ->
     rw_cells bsegs m1 SP (dr_frame junk8') -> rw_cells bsegs m1 TMP (thdr [] tb') ->
     implS bsegs RNG1 (aembed ATOP (K st1)) (epostF Q)
           (ms_out 0x35b20 rax' t0' t1' t2' (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' xs4' xs6' xs7' xs8' xs9' t3' t4' t5' t6' m1)) ->
  implS bsegs RNG (aembed ATOP (do_recycle st (map fst T) K)) (epostF Q)
        (ms_out adorec_lout rax t0 t1 t2 (Z_to_bv 64 (Z.of_nat (length T))) a1 a2 a3 a4 a5 a6 a7 xs4 xs6 xs7 xs8 xs9 t3 t4 t5 t6 m).
Proof.
  intros RT Q T. induction T as [|[b q] T IH]; intros K R st X RNG m tb junk8 rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 xs4 xs6 xs7 xs8 xs9 t3 t4 t5 t6
    INV ET EB EP NE FR TH KONT; [congruence|].
  pose proof INV as (ARNG & AR & BL & HF & RS & MI & ST & FLE & MU0 & CP0 & SK). destruct (drinv_rngs _ _ _ _ _ INV) as [RSTK RTMP].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (SPE : SP = bv_unsigned sp + -112) by reflexivity.
  pose proof AR as AR0. destruct AR0 as (WF & _ & _ & _ & _ & HQ & HS & _). cbn [ah_quar ah_sec AHr ARecyc1P.AHr] in HQ, HS.
  (* [comment removed for export] *)
  destruct (AQdr_popr R L st X m b q T HQ ET EB EP) as (HQ1 & BC & SZB & NTT).
  destruct BC as (CC & EC & JC & CCNT & CLEN & CRNG).
  set (R1 := qr_popr R b q T) in *.
  set (B := abatch_addr L (qb_slot q)) in *.
  set (all := rev (combine (b_chunks b) (qb_ks q))).
  assert (LALL : Z.of_nat (length all) = b_count b) by (subst all; rewrite length_rev, length_combine, CLEN, Nat.min_id; lia).
  assert (MALL : map fst all = rev (b_chunks b)) by (subst all; rewrite map_rev, map_fst_combine by exact CLEN; reflexivity).
  rewrite (qhdrs_rev_combine L _ _ CLEN) in EC. fold all in EC.
  assert (PCS : Permutation (csx st R) (csx st R1)).
  { unfold csx. apply Permutation_app_head. apply Permutation_sym. subst R1. apply inflight_popr; [exact ET| exact EP| exact CLEN]. }
  assert (AR1 : AREP (AHr R1 (csx st R1)) L st X m).
  { unfold AHr, ARecyc1P.AHr. eapply AREP_reqs; [exact AR| exact HQ1| intros HS'; eapply ASECc_perm; [exact PCS| exact HS']]. }
  assert (INV1 : drinv R1 st X RNG m).
  { unfold drinv. split; [exact ARNG|]. split; [exact AR1|]. split; [exact BL|]. split; [exact HF|].
    split; [eapply RSEC_perm'; [| exact RS]; apply Permutation_sym; subst R1; apply inflight_popr; [exact ET| exact EP| exact CLEN]|].
    split; [exact MI|]. split; [exact ST|]. split; [exact FLE|]. split; [exact MU0|]. split; [exact CP0| exact SK]. }
  (* [comment removed for export] *)
  destruct (pendb_busy L st X R1 m (qb_slot q) HQ1 eq_refl) as (nb & bb1 & bctx & bl1 & bl2 & XBB).
  destruct (any_range L st X BBatch K_BATCH_CLASS (qb_slot q) nb bb1 bctx bl1 bl2 XBB WF) as [_ KQ].
  pose proof (busy_slot_geo L st X ALO WF (bany BBatch K_BATCH_CLASS (qb_slot q) nb bb1 bctx) ltac:(rewrite XBB; apply in_app_iff; right; left; reflexivity)) as BG.
  unfold xb_alloc in BG. cbn [xb_class xb_slot bany] in BG. rewrite size_of_class_24 in BG. unfold abatch_addr in B. fold B in BG.
  destruct BG as (_ & _ & BG1 & BG2 & (BG3a & BG3 & BG3b) & BG4 & BG5 & BG6 & BG7).
  assert (RB : rng RNG B 24).
  { destruct ARNG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RCLS & _). destruct (RCLS K_BATCH_CLASS (K24)) as (RR1 & _). eapply rng_sub; [exact RR1| |]; clear -BG1 BG2 BG3; unfold K_FREEARR_OFF; lia. }
  (try pose proof atop_range as ATR). unfold Q_BATCH in CRNG.
  pose proof (tmp_len_bound R1 L st X m ALO WF HQ1) as TLEN. subst R1. cbn [qr_tmp qr_popr] in TLEN. set (R1 := qr_popr R b q T) in *.
  (* [comment removed for export] *)
  assert (QF : (T = [] /\ qfirst L (map snd T) = 0) \/ (T <> [] /\ 17594333495296 <= qfirst L (map snd T) /\ qfirst L (map snd T) + 8192 <= ATOP)).   (* [comment removed for export] *)
  { destruct T as [|[b' q'] T']; [left; split; reflexivity| right]. split; [discriminate|].
    pose proof (tmp_head_geo R1 L st X m b' q' T' ALO WF HQ1 eq_refl) as G. (try pose proof atop_range as ATR). unfold qfirst, qaddrs. cbn [map hd]. exact G. }
  (* [comment removed for export] *)
  assert (REST : forall m2 rax2 (a1x : word),
    munch [(TMP, TMP + 32)]%Z m m2 -> wmono bsegs m m2 -> mem_inv bsegs m2 -> stk bsegs m2 lo SP -> munch [(0, bv_unsigned sp); (TMP, TMP + 32)]%Z m0 m2 ->
    rw_cells bsegs m2 SP (dr_frame junk8) ->
    rw_cells bsegs m2 TMP [C8 (Z_to_bv 64 (Z.of_nat (S (length T)))); C8 (Z_to_bv 64 (qfirst L (map snd T))); C8 (Z_to_bv 64 (qlast L (map snd T))); C8 tb] ->
    rw_cells bsegs m2 B [C8 (Z_to_bv 64 (qfirst L (map snd T))); C8 (Z_to_bv 64 (b_size b)); C8 (Z_to_bv 64 (b_count b))] ->
    evtF bsegs RNG (fun ms' => implS bsegs RNG (aembed ATOP (do_recycle st (b :: map fst T) K)) (epostF Q) ms')
         (MS (mkR rax2 (Z_to_bv 64 SP) gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 TMP) (Z_to_bv 64 837272) (Z_to_bv 64 (Z.of_nat (S (length T)))) a1x a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 837336) (Z_to_bv 64 837960) (Z_to_bv 64 B) (Z_to_bv 64 137438953472) xs6 xs7 xs8 xs9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x35aa8) fc None m2 (seg_rom bsegs))).
  { intros m2 rax2 a1x MUp WMp MI2 ST2 MU02 FR2 TH2 CC2. unfold dr_frame in FR2.
    zstep.                                                 (* [comment removed for export] *)
    setreg 10 (Z_to_bv 64 (Z.of_nat (length T))) ltac:(f_equal; clear; lia).
    step.                                                  (* [comment removed for export] *)
    step.                                                  (* [comment removed for export] *)
    step.                                                  (* [comment removed for export] *)
    step.                                                  (* [comment removed for export] *)
    step.                                                  (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (AR2 : AREP (AHr R1 (csx st R1)) L st X mx);
      [ eapply (AREP_frame_ext _ (HL R1 (csx st R1)) L st X m mx); [exact ALO| exact AR1| exact MUp| exact WMp|];
        constructor; [| constructor]; cbn [fst snd]; intros _; right; right; left; atop_facts; clear -CEIL LO TMPLO; lia |];
      assert (HF2 : AF L LB mx);
      [ eapply AFD; [exact HF| exact MUp| |]; [apply fake_untouched_of; intros iv [<-|[]]; apply high_fake; [exact ALO| cbn [fst]; atop_facts; clear -CEIL LO TMPLO; lia]
        | constructor; [| constructor]; cbn [fst snd]; right; pose proof (ao_t L ALO) as OT; unfold aobj in *; clear -OT CEIL LO TMPLO; lia] |];
      assert (CP2 : cpres L HI LB m0 mx);
      [ eapply cpres_trans; [exact CP0|]; eapply cpres_of_munch; [exact MUp|]; intros iv [<-|[]]; cbn [fst snd];
        eapply (np_high L st X LB HI); [exact ALO| exact WF| exact BL| atop_facts; clear -CEIL LO TMPLO; lia| exact HHI] |];
      assert (INV2 : drinv R1 st X RNG mx);
      [ unfold drinv; destruct INV1 as (_ & _ & _ & _ & RS1 & _); split; [exact ARNG|]; split; [exact AR2|]; split; [exact BL|]; split; [exact HF2|]; split; [exact RS1|];
        split; [assumption|]; split; [assumption|]; split; [exact FLE|]; split; [assumption|]; split; [exact CP2| exact SK] |];
      assert (EC2 : u64arr bsegs mx (B + 24) (map (ehdr L) all));
      [ eapply (u64arr_frameD _ _ _ _ _ EC MUp); rewrite length_map; cbn [disjoint_from fst snd]; split; [left; clear -LALL CRNG BG5 CEIL LO TMPLO; lia| exact I] |]
    end.
    step.                                                  (* [comment removed for export] *)
    rewrite do_recycle_cons, <- MALL.
    step. if_cases KC; zify_cond KC; rewrite ?unsigned_lit in KC by (clear -CRNG; lia).   (* [comment removed for export] *)
    - (* [comment removed for export] *)
      assert (E0 : all = []) by (destruct all; [reflexivity| exfalso; cbn [length] in LALL; clear -LALL KC; lia]).
      rewrite E0. cbn [map recycle_chunks].
      apply evtF_done.
      eapply (dr_after Q (fun st2 => do_recycle st2 (map fst T) K) R1 st X RNG _ (qb_slot q) T);
        [exact INV2| reflexivity| reflexivity| subst R1; unfold qr_popr; cbn [qr_pend]; fold all; exact E0| eassumption| eassumption|].
      intros st4 X4 RNG4 m4 junk8' rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' INV4 FR4 TH4.
      pose proof INV4 as (_ & _ & _ & _ & _ & MI4 & ST4 & FLE4 & MU04 & _). destruct (drinv_rngs _ _ _ _ _ INV4) as [RSTK4 RTMP4].
      unfold ms_out, adorec_chk. unfold thdr in TH4. iprefix.
      step.                                                (* [comment removed for export] *)
      step. if_cases KT; zify_cond KT.                     (* [comment removed for export] *)
      + destruct T as [|bq' T']; [exfalso; apply KT; reflexivity|].
        apply evtF_done. eapply (IH K (qr_unbatch (qr_drop R1 [])) st4 X4 RNG4 m4 _ junk8');
          [exact INV4| reflexivity| reflexivity| reflexivity| discriminate| exact FR4| exact TH4| exact KONT].
      + destruct T as [|bq' T']; [| exfalso; cbn [length] in KT, TLEN; first [rewrite Z.mod_small in KT by (clear -TLEN; lia)| rewrite unsigned_lit in KT by (clear -TLEN; lia)| idtac]; clear -KT; lia].
        apply evtF_done. eapply KONT; [exact INV4| exact FR4| exact TH4].
    - (* [comment removed for export] *)
      assert (NEA : all <> []) by (intros E0; apply KC; rewrite <- LALL, E0; reflexivity).
      zstep. zstep. zstep.                                 (* [comment removed for export] *)
      setreg 23 (Z_to_bv 64 (B + 152 + 8 * 0)) ltac:(f_equal; clear; lia).
      setreg 24 (Z_to_bv 64 (16 + Z.of_nat (length all))) ltac:(f_equal; clear -LALL; lia).
      setreg 25 (Z_to_bv 64 (16 + 0)) ltac:(f_equal; clear; lia).
      rewrite <- LALL.
      apply evtF_done.
      eapply (dr_inner Q all (fun st1 => cache_dealloc st1 K_BATCH_CLASS (fun st2 => do_recycle st2 (map fst T) K)) R1 st X RNG _ (qb_slot q) all T 0);
        [exact INV2| | reflexivity| reflexivity| exact NEA| clear; lia| eassumption| eassumption| eassumption|].
      { unfold batch_ok. subst R1. unfold qr_popr. cbn [qr_tmp qr_pendb]. split; [reflexivity|]. split; [reflexivity|]. unfold Q_BATCH. split; [clear -LALL CRNG; lia| clear -KQ; lia]. }
      intros st3 X3 RNG3 m3 junk8' rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' INV3 FR3 TH3.
      unfold ms_in.
      eapply (dr_after Q (fun st2 => do_recycle st2 (map fst T) K) (qr_drop R1 []) st3 X3 RNG3 m3 (qb_slot q) T);
        [exact INV3| reflexivity| reflexivity| reflexivity| exact FR3| exact TH3|].
      intros st4 X4 RNG4 m4 junk8'' rax'' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' INV4 FR4 TH4.
      pose proof INV4 as (_ & _ & _ & _ & _ & MI4 & ST4 & FLE4 & MU04 & _). destruct (drinv_rngs _ _ _ _ _ INV4) as [RSTK4 RTMP4].
      unfold ms_out, adorec_chk. unfold thdr in TH4. iprefix.
      step.                                                (* [comment removed for export] *)
      step. if_cases KT; zify_cond KT.                     (* [comment removed for export] *)
      + destruct T as [|bq' T']; [exfalso; apply KT; reflexivity|].
        apply evtF_done. eapply (IH K (qr_unbatch (qr_drop R1 [])) st4 X4 RNG4 m4 _ junk8'');
          [exact INV4| reflexivity| reflexivity| reflexivity| discriminate| exact FR4| exact TH4| exact KONT].
      + destruct T as [|bq' T']; [| exfalso; cbn [length] in KT, TLEN; first [rewrite Z.mod_small in KT by (clear -TLEN; lia)| rewrite unsigned_lit in KT by (clear -TLEN; lia)| idtac]; clear -KT; lia].
        apply evtF_done. eapply KONT; [exact INV4| exact FR4| exact TH4]. }
  (* [comment removed for export] *)
  unfold ms_out, adorec_lout. unfold thdr in TH. cbn [length map snd qfirst qaddrs hd] in TH. change (abatch_addr L (qb_slot q)) with B in TH.
  change (Z.of_nat (length ((b, q) :: T))) with (Z.of_nat (S (length T))).
  pose proof (munch_refl [(TMP, TMP + 32)]%Z m) as MUp. pose proof (wmono_refl bsegs m) as WMp. unfold dr_frame in FR.
  iprefix.
  step.                                       (* [comment removed for export] *)
  step.                                       (* [comment removed for export] *)
  step.                                       (* [comment removed for export] *)
  step. if_cases KN; zify_cond KN.            (* [comment removed for export] *)
  - (* [comment removed for export] *)
    destruct QF as [[-> QF0]|(TNE & QF1 & QF2)]; [exfalso; apply KN; rewrite QF0; reflexivity|].
    rewrite (qlast_cons_ne q (map snd T)) in * by (destruct T; [congruence| discriminate]).
    eapply REST; eassumption.
  - (* [comment removed for export] *)
    destruct QF as [[ET0 QF0]|(TNE & QF1 & QF2)]; [| exfalso; first [rewrite Z.mod_small in KN by (clear -QF1 QF2; lia)| rewrite unsigned_lit in KN by (clear -QF1 QF2; lia)| idtac]; clear -KN QF1; lia].
    step.                                     (* [comment removed for export] *)
    subst T. eapply REST; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma drinv_done : forall R st X RNG m, qr_tmp R = [] -> qr_pendb R = [] -> qr_pend R = [] -> drinv R st X RNG m -> drinv (qr_done R) st X RNG m.
Proof.
  intros R st X RNG m ET EB EP (ARNG & AR & BL & HF & RS & MI & ST & FLE & MU0 & CP0 & SK).
  assert (EI : inflight (qr_done R) = inflight R) by (unfold inflight, secsT, qr_done; cbn [qr_tmp qr_pend]; rewrite ET, EP; reflexivity).
  unfold drinv. rewrite (ltac:(unfold csx; rewrite EI; reflexivity) : csx st (qr_done R) = csx st R), EI.
  split; [exact ARNG|]. split; [| exact (conj BL (conj HF (conj RS (conj MI (conj ST (conj FLE (conj MU0 (conj CP0 SK))))))))].
  unfold AHr, ARecyc1P.AHr in AR |- *. eapply AREP_reqs; [exact AR| | intros HS'; exact HS'].
  destruct AR as (_ & _ & _ & _ & _ & HQ & _). cbn [ah_quar] in HQ. destruct HQ as (QC & MX & TC & GL & TB & IA & CP & NUM & NT).
  unfold AQdr, qr_done. cbn [qr_loc qr_glob qr_tmp qr_ia qr_pendb qr_pend map]. rewrite ET in NT. cbn [map] in NT.
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact I|]. split; [exact IA|]. split; [| exact (conj NUM NT)].
  eapply qcoupled_rec_perm; [exact CP| | | | | reflexivity].
  - exact (proj1 CP).
  - exact (proj1 (proj2 CP)).
  - unfold qr_entries. cbn [qr_loc qr_glob qr_tmp qr_pend]. rewrite ET, EP. cbn [map qentries app]. apply Permutation_refl.
  - unfold qr_bslots. cbn [qr_loc qr_glob qr_tmp qr_pendb]. rewrite ET, EB. cbn [map app]. apply Permutation_refl.
Qed.

Theorem adorec : forall {RT} (K : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
    (R : qrconc) (X : aconc) (T : list (abatch * qbatchc)) (tb : word) (t0 t1 t2 a0 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  arng L RNG0 st0 -> AREP (AHr R (csx st0 R)) L st0 X m0 -> ablocks L st0 X LB -> AF L LB m0 -> RSEC (inflight R) RNG0 ->
  qr_tmp R = T -> qr_pendb R = [] -> qr_pend R = [] ->
  mem_inv bsegs m0 -> stk bsegs m0 lo (bv_unsigned sp) ->
  rw_cells bsegs m0 TMP (thdr T tb) ->
  (forall st1 X1 RNG1 m1 (tb' : word) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     drinv (qr_done R) st1 X1 RNG1 m1 -> stk bsegs m1 lo (bv_unsigned sp) ->
     rw_cells bsegs m1 TMP (thdr [] tb') ->
     implS bsegs RNG1 (aembed ATOP (K st1)) (epostF Q)
           (MS (mkR ra sp gp (Z_to_bv 64 ATP) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m1 (seg_rom bsegs))) ->
  implS bsegs RNG0 (aembed ATOP (do_recycle st0 (map fst T) K)) (epostF Q)
        (MS (mkR ra sp gp (Z_to_bv 64 ATP) t0 t1 t2 s0 s1 a0 (Z_to_bv 64 TMP) (Z_to_bv 64 (al_t L + 208)) cbs a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 adorec_entry) fc None m0 (seg_rom bsegs)).
Proof.
  intros RT K Q R X T tb t0 t1 t2 a0 a4 a5 a6 a7 t3 t4 t5 t6 ARNG AR BL HF RS ET EB EP MI ST TH KONT.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. (try pose proof atop_range as ATR).
  assert (SPE : SP = bv_unsigned sp + -112) by reflexivity.
  pose proof AR as AR0. destruct AR0 as (WF & _ & _ & _ & _ & HQ & _). cbn [ah_quar AHr ARecyc1P.AHr] in HQ.
  pose proof (tmp_len_bound R L st0 X m0 ALO WF HQ) as TLEN. rewrite ET in TLEN.
  pose proof (munch_refl [(0, bv_unsigned sp); (TMP, TMP + 32)]%Z m0) as MU0. pose proof (munch_refl [(bv_unsigned sp + -112, bv_unsigned sp)]%Z m0) as MUf. pose proof (wmono_refl bsegs m0) as WM0.
  unfold adorec_entry. unfold thdr in TH.
  iprefix.
  carve_frame 112%nat ST.
  do 12 step.                                 (* [comment removed for export] *)
  step.                                       (* [comment removed for export] *)
  step. step.                                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (INV : drinv R st0 X RNG0 mx);
    [ unfold drinv; split; [exact ARNG|];
      split; [eapply (AREP_frame_ext _ (HL R (csx st0 R)) L st0 X m0 mx); [exact ALO| exact AR| exact MUf| exact WM0|];
              constructor; [| constructor]; cbn [fst snd]; intros _; right; right; left; atop_facts; clear -CEIL LO; lia |];
      split; [exact BL|];
      split; [eapply AFD; [exact HF| exact MUf| |]; [apply fake_untouched_of; intros iv [<-|[]]; apply high_fake; [exact ALO|]; cbn [fst]; atop_facts; clear -CEIL LO; lia
               | constructor; [| constructor]; cbn [fst snd]; right; pose proof (ao_t L ALO) as OT; unfold aobj in *; clear -OT CEIL LO; lia] |];
      split; [exact RS|]; split; [assumption|]; split; [rewrite SPE; assumption|]; split; [intros bb j Hb; exact Hb|]; split; [exact MU0|];
      split; [eapply cpres_of_munch; [exact MUf|]; intros iv [<-|[]]; cbn [fst snd]; eapply (np_high L st0 X LB HI); [exact ALO| exact WF| exact BL| atop_facts; clear -CEIL LO; lia| clear -TMPLO HHI; lia] |];
      unfold st_keep; repeat (split; [reflexivity|]); reflexivity |]
  end.
  (* [comment removed for export] *)
  assert (EPI : forall m1 st1 X1 RNG1 junk8' (tb' : word) rax' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 t3' t4' t5' t6',
    drinv (qr_done R) st1 X1 RNG1 m1 -> rw_cells bsegs m1 SP (dr_frame junk8') -> rw_cells bsegs m1 TMP (thdr [] tb') ->
    evtF bsegs RNG1 (fun ms' => implS bsegs RNG1 (aembed ATOP (K st1)) (epostF Q) ms')
         (MS (mkR rax' (Z_to_bv 64 SP) gp (Z_to_bv 64 ATP) t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x35b20) fc None m1 (seg_rom bsegs))).
  { intros m1 st1 X1 RNG1 junk8' tb' rax' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 t3' t4' t5' t6' INV1 FR1 TH1.
    pose proof INV1 as (_ & _ & _ & _ & _ & MI1 & ST1 & FLE1 & _). destruct (drinv_rngs _ _ _ _ _ INV1) as [RSTK1 RTMP1].
    unfold dr_frame in FR1.
    do 11 step.                               (* [comment removed for export] *)
    zstep.                                    (* [comment removed for export] *)
    setreg 2 sp ltac:(rewrite SPE; replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by (clear; lia); symmetry; apply Z_to_bv_bv_unsigned).
    step.                                     (* [comment removed for export] *)
    release_frame FR1 ST1 (bv_unsigned sp).
    apply evtF_done. eapply KONT; [exact INV1| exact ST1| exact TH1]. }
  step. if_cases K0; zify_cond K0.            (* [comment removed for export] *)
  - (* [comment removed for export] *)
    destruct T as [|bq T']; [| exfalso; cbn [length] in K0, TLEN; first [rewrite Z.mod_small in K0 by (clear -TLEN; lia)| rewrite unsigned_lit in K0 by (clear -TLEN; lia)| idtac]; clear -K0; lia].
    cbn [map do_recycle].
    eapply EPI; [apply drinv_done; [exact ET| exact EB| exact EP| exact INV]| exact FR| exact TH].
  - destruct T as [|bq T']; [exfalso; apply K0; reflexivity|].
    do 8 step.                                (* [comment removed for export] *)
    apply evtF_done.
    eapply (dr_outer Q (bq :: T') K R st0 X RNG0 _ tb); [exact INV| exact ET| exact EB| exact EP| discriminate| exact FR| exact TH|].
    intros st1 X1 RNG1 m1 junk8' tb' rax' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' xs4' xs6' xs7' xs8' xs9' t3' t4' t5' t6' INV1 FR1 TH1.
    unfold ms_out. iprefix. eapply EPI; [exact INV1| exact FR1| exact TH1].
Qed.
End DoRec.
End CANSEC2.
(* [comment removed for export] *)
