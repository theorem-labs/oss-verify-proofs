(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import ASecFacts AImg AProto ABase ABytes AQConst AMalloc_iface ADepot_iface ARep ARepQ ARepQP ALayout AHeapP ARepKit ARepFrame ARepStore
AKit AModelFacts AFreeModel AFreeRep AFreeGeo AFreeRead F_afree_tail F_afree_icpt F_afree_arep AFreeStoreK.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation Wf sp t UB gq nodes store lst eb gl :=
([(sp - 4096, sp); (0x9f188, 0x9f1b0); (0xa3680, 0x1246b0); (0x131f08, 0x131f0c); (ADEPOT_LO, ADEPOT_HI);
(t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792); (t + 2800, t + 3169);
(UB - 16, UB + 8); (shad UB, shad UB + gq);
(nodes, nodes + 1048576); (store, store + 8388608);
(lst, lst + qsz lst); (eb, eb + 8192); (gl, gl + 8)]%Z) (only parsing).
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
6254592 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
Local Ltac2 Set LiaHints.tbl := fun () => "0040>25807118408.1036002021247.103826536157.10 48752954456.1000000600:00D00MS2H21HS2H3S2H22H52HnS2H31H2H0".
split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
4096 <= a /\ a + 4096 <= ATOP
/\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
/\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6254592 * j <= a).
Proof.
intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
Local Ltac2 Set LiaHints.tbl := fun () => "0040=25807118408.836072040845.83826536157.8 48752954456.800000900=00A00MS2H21H2H5S2H3S2H2S2H31H2H02H5".
split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma aheap_pres_free : forall (CI : list (Z * Z)) sp t AB S UB gq nodes store res ctx lo grz ssz lst eb gl (LB : list ablock) m m',
kfactsF sp t AB S UB gq nodes store res ctx lo grz ssz lst eb gl ->
Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
/\ (snd iv <= 0x9f0f0 \/ 0x9f1b0 <= fst iv)
/\ (snd iv <= 0xa3680 \/ 0x1246b0 <= fst iv)
/\ (snd iv <= 0x131f08 \/ 0x131f0c <= fst iv)) CI ->
munch (Wf sp t UB gq nodes store lst eb gl) m m' -> wmono asegs m m' ->
(forall b, In b LB -> disjoint_from (Wf sp t UB gq nodes store lst eb gl) (ab_addr b) (ab_size b)) ->
(forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
disjoint_from (Wf sp t UB gq nodes store lst eb gl) (shad a') 1) ->
shad UB + gq <= shad ATOP ->
aheap_pres CI LB sp m m'.
Proof.
intros CI sp t AB S UB gq nodes store res ctx lo grz ssz lst eb gl LB m m' KF CIOK MU WM HBK HFK PSP a Ha CL.
split; [| intros Hw; apply WM; exact Hw].
apply MU. rewrite wa_unsigned by exact Ha.
pose proof KF as KF'. destruct KF' as (F_lo & F_t & F_res & F_slot & F_sh & F_ns & F_ctx & F_lst & F_eb & F_gl).
destruct CL as [ST | [CIa | [BLK | SH]]].
- Local Ltac2 Set LiaHints.tbl := fun () => "00B0>15861813533.3016181704211.1322480963918.3036952386489.503832836837.50 38558360336.1338558360606.3059361062673.4459361062673.4859361062673.4959928007069.426755918133.30 6755919419.13 6758013062.42 6758013062.50 68183228144.448130345098.42 8130345098.50 00000=00K00e01701=01K01[01\01]01^01b01c01d01e01f01i01j01kS2ST2SD2H42H5S1R2SD2Q31H2H0S3PSP2ST2SD3SDs1H2H02H42H5S1R2Q22Q32Q42Q52Q6S1R2Q1S1R2SD2Q11H2H0S2ST2SD2H42H52H9SSSS2STSSSSS1RSS".
eapply disjoint_outside; [eapply (KF_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); lia | lia].
- destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6). cbn [fst snd] in *.
eapply disjoint_outside; [eapply (KF_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); unfold AIMG_HI in *; lia | lia].
- destruct BLK as (b & Hb & R). eapply disjoint_outside; [exact (HBK b Hb) | lia].
- destruct SH as (a' & Ha' & ->).
pose proof (shad_div a') as SD. pose proof (shad_div ATOP) as SDs. unfold ASHOFF in *.
destruct Ha' as [ST | [CIa | FK]].
+ eapply disjoint_outside; [eapply (KF_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
all: atop_facts; clear -ST SD SDs F_sh F_lo PSP; Z.div_mod_to_equations; lia.
+ destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as (Q1 & Q2 & Q3 & _). cbn [fst snd] in *.
eapply disjoint_outside; [eapply (KF_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
all: unfold AIMG_HI in *; clear -R SD Q1 Q3; Z.div_mod_to_equations; lia.
+ destruct FK as (cls & FA & sz & Hin & R). eapply disjoint_outside; [exact (HFK cls FA sz Hin a' R) | lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma busy_slot_range : forall L st X b, awf L st X -> In b (x_busy X) ->
1 <= xb_class b < K_NUM_CLASSES /\ 0 <= xb_slot b < ndist st (xb_class b).
Proof.
intros L st X b WF Hb. pose proof WF as WF0. destruct WF0 as (_ & _ & _ & _ & _ & PERC & _ & BUSY & _).
destruct (BUSY b Hb) as [HC _]. split; [exact HC|].
destruct (PERC (xb_class b) HC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RANGE).
apply RANGE. apply in_or_app. right. apply in_or_app. right. unfold busy_slots. apply in_map. apply List.filter_In.
split; [exact Hb| apply Z.eqb_refl].
Qed.
Definition xfree (X : aconc) (app : bool) (c k n b1 ctx : Z) (l1 l2 : list xbusy) (k24 : Z) : aconc :=
if app then xquar X c k n b1 ctx l1 l2 else xbatch (xquar X c k n b1 ctx l1 l2) k24.
#[using="Type"] Lemma xfree_free : forall X app c k n b1 ctx l1 l2 k24 c', xc_free (x_cls (xfree X app c k n b1 ctx l1 l2 k24) c') = xc_free (x_cls X c').
Proof. intros. unfold xfree, xbatch, xquar. destruct app; cbn; [reflexivity|]. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma xfree_cache : forall X app c k n b1 ctx l1 l2 k24 c',
xc_cache (x_cls (xfree X app c k n b1 ctx l1 l2 k24) c') =
if (negb app) && (c' =? K_BATCH_CLASS) then removelast (xc_cache (x_cls X K_BATCH_CLASS)) else xc_cache (x_cls X c').
Proof.
intros. unfold xfree, xbatch, xquar. destruct app; cbn; [reflexivity|]. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [->|]; reflexivity.
Qed.
#[using="Type"] Lemma busy_of_xbatch' : forall X k24 c' k',
busy_of (xbatch X k24) c' k' = if (K_BATCH_CLASS =? c') && (k24 =? k') then Some (bbatch k24) else busy_of X c' k'.
Proof.
intros. unfold busy_of, xbatch. cbn [x_busy List.find xb_class xb_slot bbatch].
destruct ((K_BATCH_CLASS =? c') && (k24 =? k')); reflexivity.
Qed.
#[using="Type"] Lemma busy_of_xfree : forall L st X p c k n b1 ctx l1 l2 app k24 c' k',
x_busy X = l1 ++ bfreed p c k n b1 ctx :: l2 -> awf L st X ->
busy_of (xfree X app c k n b1 ctx l1 l2 k24) c' k' =
if (negb app) && (K_BATCH_CLASS =? c') && (k24 =? k') then Some (bbatch k24)
else if (c =? c') && (k =? k') then Some (bquar c k n b1 ctx) else busy_of X c' k'.
Proof.
intros L st X p c k n b1 ctx l1 l2 app k24 c' k' XB WF. unfold xfree. destruct app; cbn [negb andb].
- apply (busy_of_xquar L st X p c k n b1 ctx l1 l2 XB WF).
- rewrite busy_of_xbatch'. destruct ((K_BATCH_CLASS =? c') && (k24 =? k')); [reflexivity|].
apply (busy_of_xquar L st X p c k n b1 ctx l1 l2 XB WF).
Qed.
#[using="Type"] Lemma farr_vs_user : forall L c'' c0 A k P Psz,
aregion L c0 <= P -> P + Psz <= aregion L c0 + K_FREEARR_OFF ->
aregion L c'' + K_FREEARR_OFF <= A -> A + k <= aregion L c'' + K_REGION ->
A + k <= P \/ P + Psz <= A.
Proof.
intros L c'' c0 A k P Psz P1 P2 A1 A2. unfold aregion, K_FREEARR_OFF, K_REGION in *. change (2^32) with 4294967296 in *.
destruct (Z.lt_ge_cases c'' c0); [left| right]; nia.
Qed.
#[using="Type"] Lemma undist_vs_user : forall L c'' c0 A k P Psz alloc0,
aregion L c0 <= P -> P + Psz <= aregion L c0 + alloc0 -> alloc0 <= K_FREEARR_OFF ->
(c'' = c0 -> aregion L c0 + alloc0 <= A) ->
aregion L c'' <= A -> A + k <= aregion L c'' + K_FREEARR_OFF ->
A + k <= P \/ P + Psz <= A.
Proof.
intros L c'' c0 A k P Psz alloc0 P1 P2 AL E A1 A2. unfold aregion, K_FREEARR_OFF, K_REGION in *. change (2^32) with 4294967296 in *.
Local Ltac2 Set LiaHints.tbl := fun () => "0010>16723380833.14000006S2P21E".
destruct (Z.eq_dec c'' c0) as [->|NE]; [right; specialize (E eq_refl); lia|].
destruct (Z.lt_ge_cases c'' c0); [left| right]; nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma arng_core : forall L RNG s s', same_core s s' -> Permutation (sec_chunks_of s') (sec_chunks_of s) -> arng L RNG s -> arng L RNG s'.
Proof.
intros L RNG s s' (_ & _ & _ & _ & _ & NR & _ & GC & M1 & M2 & M3 & M4) P (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & RC & RPA & RSC & RPSH).
unfold arng. repeat (split; [assumption|]). split; [| split; [rewrite NR; exact RPA| split; [eapply RSEC_perm; [apply Permutation_sym; exact P| exact RSC]| exact RPSH]]].
intros c' Hc'. cbv zeta. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE].
- rewrite M1, M4. exact (RC K_BATCH_CLASS Hc').
- rewrite (GC c' NE). exact (RC c' Hc').
Qed.
Definition unbxF {P : Prop} (b : boxed P) : P := match b with Box _ p => p end.
#[using="Type"] Lemma busy_of_In_nodup : forall L st X y, awf L st X -> In y (x_busy X) -> busy_of X (xb_class y) (xb_slot y) = Some y.
Proof.
intros L st X y WF Hy.
destruct WF as (_ & _ & _ & _ & _ & PERC & _ & BUSY & _). destruct (BUSY y Hy) as [CL _].
destruct (PERC (xb_class y) CL) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _).
apply NoDup_app_l in ND. apply NoDup_app_l in ND. unfold busy_slots in ND. unfold busy_of.
remember (x_busy X) as bs eqn:E. clear E BUSY PERC. induction bs as [|b bs IH]; [destruct Hy|].
cbn [List.find]. cbn [List.filter] in ND. destruct Hy as [<-|Hy].
- rewrite !Z.eqb_refl. reflexivity.
- destruct (Z.eqb_spec (xb_class b) (xb_class y)) as [EC|NC]; cbn [andb].
+ cbn [map] in ND. inversion ND; subst.
destruct (Z.eqb_spec (xb_slot b) (xb_slot y)) as [EK|NK].
* exfalso. apply H1. rewrite EK. apply in_map. apply List.filter_In. split; [exact Hy| first [apply Z.eqb_refl| rewrite EC; apply Z.eqb_refl]].
* apply IH; [exact Hy| assumption].
+ apply IH; [exact Hy| exact ND].
Qed.
#[using="Type"] Lemma qaddrs_reslot : forall L ql qz ks, qaddrs L (ql ++ [mkQB (qb_slot qz) ks]) = qaddrs L (ql ++ [qz]).
Proof. intros. unfold qaddrs. rewrite !map_app. reflexivity. Qed.
#[using="Type"] Lemma qfirst_reslot : forall L ql qz ks, qfirst L (ql ++ [mkQB (qb_slot qz) ks]) = qfirst L (ql ++ [qz]).
Proof. intros. unfold qfirst. rewrite qaddrs_reslot. reflexivity. Qed.
#[using="Type"] Lemma qlast_reslot : forall L ql qz ks, qlast L (ql ++ [mkQB (qb_slot qz) ks]) = qlast L (ql ++ [qz]).
Proof. intros. unfold qlast. rewrite qaddrs_reslot. reflexivity. Qed.
#[using="Type"] Lemma qfirst_app_r : forall L qs q, qfirst L (qs ++ [q]) = match qs with [] => abatch_addr L (qb_slot q) | _ => qfirst L qs end.
Proof. intros L [|q0 qs] q; reflexivity. Qed.
#[using="Type"] Lemma hd_qaddrs : forall L d qs, qs <> [] -> hd d (qaddrs L qs) = qfirst L qs.
Proof. intros L d [|q qs] NE; [congruence| reflexivity]. Qed.
#[using="Type"] Lemma junk_nil : forall m A, 0 <= A -> A <= 2^64 -> junk_at m A 0.
Proof.
intros m A H0 H1. exists []. split; [split; [cbn; tauto|]|]; unfold bytes_at, wr_at; cbn; (split; [lia|]; split; [lia|]; intros i Hi; lia).
Qed.
#[using="Type"] Lemma junk_of_u64arr : forall m A ws, u64arr asegs m A ws -> junk_at m A (8 * Z.of_nat (length ws)).
Proof.
intros m A ws U. pose proof (junk_of_cells m A _ (rw_cells_of_u64arr m A ws U)) as J. cbn [cells_size csize] in J.
rewrite Nat.add_0_r, Nat2Z.inj_mul in J. exact J.
Qed.
#[using="Type"] Lemma rz_gt16 : forall n, 0 <= n -> 16 < rz_size n -> 32 <= rz_size n.
Proof. intros n Hn H. pose proof (rz_size_facts n Hn) as [_ M]. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>12660713976.12000008S1H1M2H0".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ek_pre_b_hi : forall ek RNG t nb lst n hm m, ek_pre ek RNG t nb lst n hm m -> 0x10007fff8000 <= ek_b ek lst.
Proof.
intros ek RNG t nb lst n hm m EK.
destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0]; cbn [ek_pre ek_b] in *.
- destruct EK as (NB1 & LB & CNT & BSZ & BSZN & NX & LA & LEN & LJ & L0 & L1 & DTL & DHL & CR' & STS' & RL). exact L0.
- destruct EK as (FULL & SB & CR & CH & LCH & CNT & NTH & IXS & STS & HB & BJ & SBP & B0 & BL1 & DTB & DTL & DBL & DHB & DHL & RB). exact B0.
Qed.
Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AHQ DI ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
/\ (snd iv <= 0x9f0f0 \/ 0x9f1b0 <= fst iv)
/\ (snd iv <= 0xa3680 \/ 0x1246b0 <= fst iv)
/\ (snd iv <= 0x131f08 \/ 0x131f0c <= fst iv)) CI.
#[using="HL CI_OK"] Theorem store_free : store_free_stmt DI ASEC AFK CI.
Proof.
unfold store_free_stmt. intros L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p c k n b1 ctx A lo k24 l1 l2 stj chunks.
cbv zeta. intros ALO ARNG AR AQ BL HFK XB HIN N1 NEWF NOREC EK DK CEIL LO ms' PM. unfold AFREE_STACK in LO.
set (st1 := set_live (delete p (a_live st)) st) in *.
set (st2 := st_enq st1 (CPrim c n)) in *.
set (ek := ek_of L st X Q n k24 stj chunks) in *.
set (g := g_of L st Q (ek_delta ek n)) in *.
pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & HRT2 & AVL & RT3).
cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD.
destruct THR as (T0 & T40 & CACHES & CSTATS & STATS0 & UNW).
destruct (freed_range L st X p c k n b1 ctx l1 l2 WF XB) as [HC KR].
pose proof (freed_live L st X p c k n b1 ctx l1 l2 XB WF) as (LIVE & N0 & FIT0 & B10 & AT0 & CTX0).
pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (HM16 & UB16 & ABUB & ABHM & HLO & UBS & ABCE & HHI & N65 & NQM & ABLO & RUP & RUP8 & S8).
pose proof (slot_geo L st X c k ALO WF HC KR) as (S16 & SM16 & AL16 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & R8 & M8).
pose proof (slot_sep_objects L st X c k ALO WF HC KR) as (DT & DC & DN & DSO & DF).
pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (SE & GR3 & GE & G0 & GFS & SHLO & SHHI & SHM1 & SHM2).
pose proof (rz_size_facts n (proj1 N0)) as [RZ1 RZ2].
pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
pose proof (ao_res L ALO) as RES. pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
pose proof (aobj4_int _ OT) as (_ & _ & [kT TBND] & [jT TIMG]).
Local Ltac2 Set LiaHints.tbl := fun () => "0;;0?10009323381.0  10119167673.20 10196145140.4  10317707088.1  103190523.25   10645443711.22 10645443711.23 10645443711.26 10645443711.27 10645443711.31 10704430631.2  10737170945.22 10788002338.3  10954123084.0  10998108614.21 11025993591.2  11050883795.4  11052638947.25 11069811988.25 11090977804.25 11097776055.20 1111870547.14  11219092194.2  11372765564.8  11888782229.1  11892977425.4  11907831911.2  12028886269.4  12038807697.4  12043002901.1  121405804.2    123507847.12   123507847.19   123507847.21   12408116592.3  12787929063.1  12866091207.8  12877090629.1  12877527575.11 128948940.0    12920915338.50 12920915338.6  12927645330.7  13097693076.25 13097809467.1  13296790518.22 13296790518.27 13296790518.31 13296790518.32 13544598300.2  13750976780.4  13795597223.12 13806945129.20 1400332343.2   14003737881.3  14043501308.8  1410655015.2   14128416780.2  14189489046.21 14246994288.25 14281919934.2  14297405530.8  14299800674.2  14505767745.7  14860407635.1  15061026666.5  15190840024.15 15257306992.15 15518689194.21 15518689194.25 15637857749.1  15714467111.23 15926558996.25 16056761287.32816114808228.1  16119001376.4  16215227464.7  1634525507.7   16368862892.32816432229618.6  16534157257.1  16644899888.3  16656649474.7  167655937.7    16779702664.24 1685717371.0   16884868271.2  16979872451.2  17026234542.8  17114851612.2  17308625397.0  17374653050.15 17406074582.21 1740686701.25  17520992186.2  17617125066.33117968768401.22 18156732106.2  18314443110.21 18583273217.4  18587466629.1  18589110649.26 18690336876.1  18703868551.33218777878251.7  18789044226.22 18930958230.24 18930958230.32718930958230.33118960964502.21 19169920231.24 19190814485.1  19348270325.0  19473647396.25 19553720766.0  19620385270.25 19665781680.3  19759569631.2  2009547599.14  20096121660.15 20415666024.24 20564444250.80 20564444368.83 20564444372.86 20733610741.0  20907259734.4  21022831700.25 21198318055.31 21198318055.32 21200416232.21 21212703638.21 21448922060.0  21486068519.1  21549609119.2  21661460857.26 21764233127.2  21896799131.1  21962168434.3  22078411937.22 22099768309.0  22111671476.2  22660696137.4  2269050772.25  2271563003.20  22802550082.22 22809127129.6  22812861019.80 22812861137.83 22812861141.86 23023850886.4  23512645862.21 2356004018.1   23816314298.4  23857893116.30 23860662149.4  23873330652.3  23915257205.0  2424855267.2   24293440807.2  24386447584.11 24721163744.30 24721163744.32 24748519873.7  24811082582.21 2485031828.25  24990232882.8  25010236118.21 25161805129.86 25161805133.83 25161805255.80 25293933061.1  25440935497.8  25638642921.20 25648145269.0  25745894988.0  26003370052.7  26238245128.0  26306678284.8  26492213457.4  26496408661.1  26537571606.7  26550245507.25 26656859592.7  26717002278.5  26719527035.20 26810173397.5  26826558778.5  26831418963.5  27032899823.3  27343840861.24 27845643961.26 27945449407.2  27963476936.7  28007945252.25 2818691164.16  28449663237.1  28465545090.22 28471690041.3  28657534629.9  28829791733.0  28849653061.1  2906878025.10  29279152639.8  29323123732.23 29351792731.86 29351792735.83 29351792853.80 29364186205.24 29429496342.21 29451311717.7  29717986733.21 29717986733.22 29717986733.23 29717986733.26 29717986733.27 29717986733.31 29885711188.25 30058057083.25 30334250540.1  3034238901.0   30465278057.0  30570389881.26 3063822754.8   30873323561.0  30874246759.2  30908703488.3  30965403367.2  3106347303.2   31191852883.1  31292898136.3  31529209730.1  31704681333.0  31714984960.30 31742247254.21 31854741868.30 31949742389.0  3212155662.0   32184223716.10 32238869922.2  32628667980.17 32776955779.13 32837901993.26 3286806506.21  3286806506.25  33437569397.0  33499265205.0  33566802644.7  33667104152.24 33802113362.2  33809143721.20 33836477841.3  33896070369.2  33967105548.25 34309623180.25 34340769570.2  34372620418.1  34486755092.25 34521219823.7  34677665110.39 34677665111.39 3470836019.24  34744144123.20 34839968747.20 34863236836.25 35092724124.2  35094583552.30 35094583552.32 35150722036.37235157163477.3  35309901728.11 35329065129.10 35329065129.11 35694103779.2  35760294982.4  35865225090.22 36066115532.21 36265926552.22436332208060.24 36395798256.3  36435850613.0  36449675461.1  36471260177.22 36586368003.5  36619215861.0  36714295519.2  36732773230.1  36802581109.0  36870532928.30 3690827047.2   36917578143.24 36958550341.1  37023218382.0  37027469036.30 37027469036.32 37150384489.26 37155632887.2  37384834303.4  37444447563.25 37558919954.2  37746960934.21 37803419920.2  38022564592.25 38046792571.25 38205014962.3  38211521123.1  38436634709.0  38464322519.2  384657662.3    38639113934.3  38763541244.13 38776846099.20 38776846099.22 38776846099.23 38776846099.26 38776846099.27 38776846099.31 38948636245.0  38971496011.15 39012636437.0  39076636629.0  39172636981.0  39188636933.0  39220637093.0  39268637205.0  39332637397.0  39340564468.2  39396637589.0  39412637669.0  39491769071.4  39494105461.0  39508862556.7  39543892502.21 39647592524.25 3969971402.2   39716638549.0  39807547359.25 39860835957.0  40038943072.11 40170518963.2  40192835119.2  40313319482.3  404410357.0    40530327484.8  40569190201.7  40795988219.20 40847487953.5  40945645650.86 40945645654.83 40945645788.80 4109668801.5   41107849968.3  41175950771.3  41356488980.25 41472054581.0  41487187274.2  4184269202.2   41891655969.3  42080551597.4  42303264487.2  4231187719.30  4231187719.32  42411609006.0  42455853923.1  4246766848.1   42469039429.1  42556226700.7  42593458068.25 42641743035.25 42876213008.2  42934358412.25 42984827339.15 43170783436.25 43195871047.25 43268453396.7  43332231982.1  43583853560.6  43593744991.2  43760733614.1  43899182423.13 4392527934.3   44180196223.7  44408639989.0  44610243722.2  45031825642.5  45082127349.0  45161700303.7  45205435247.30 45205435247.32 45738895041.7  4588927050.6   45966287030.21 46100613962.3  46133127305.8  46134670185.20 46178793218.2  46182202218.21 46182202218.25 46349192164.25 46452302936.13 46471473041.22 46626512713.0  46653515486.1  46754513097.0  4675475559.2   46780644473.9  46882513481.0  46910110034.22 46931042708.25 46968447212.8  46990720185.2  47007070456.7  47102472806.42347102472806.42747138514249.0  47144243152.11 47146100245.13 47163045076.25 47202514441.0  47266514633.0  47285056144.2  47330514825.0  47340565092.25 47586515593.0  47650515785.0  47717757129.1  47773651701.0  47826516409.0  47871145365.3  47872845720.3  48122452579.4  48142935555.25 48172209967.3  48182876821.1  48224221422.24 48226517513.0  48290517705.0  48293258432.30 48324593020.8  48487847622.6  48578630033.22 48742894451.13 48769709624.11 48863027762.3  49047162874.3  49058520009.0  49650661696.30 49698521929.0  49780429002.14 49828668885.0  50053598883.1  50066654292.25 50082523081.0  50146523273.0  50203955267.1  50338523849.0  50409833644.1  50410131434.7  50410511721.20 50462328133.1  50465378640.2  50495037576.7  50762176116.2  50850525385.0  50913014806.23 51015271797.0  51161183847.0  51234526537.0  5128303185.10  51461915500.1  51463334873.6  51696443892.2  51805966220.25 51939553626.80 51939553744.83 52002528841.0  52034529001.0  52075996467.8  52130529225.0  52169594139.5  52258529609.0  5228320519.24  52408087062.21 52555466551.13 52569147371.21 52569147371.22 52569147371.25 52569147371.26 52569147371.27 52569147371.30 52569147371.31 52569147371.32 52586510676.25 52861791446.21 52895507081.4  53025787526.21 53045873664.5  53091131576.1  53238998938.2  53282532681.0  53341058949.5  53410533065.0  53794534217.0  53841042975.2  53896456807.2  53969333446.21 54036352556.1  54139690073.5  54158656449.7  54275345606.22 54306535753.0  54704903414.25 54747134349.5  54758580605.22 54758580605.24 54758580605.26 54765217882.21 54765217882.25 54850238520.23 55162509369.7  55221209172.7  55458692139.7  55510709495.2  55743527830.21 55746441077.0  55839719569.2  55862880148.25 55929806325.0  55983921528.11 56023436187.1  56098541129.0  56137362799.8  56143417687.2  56350333127.4  56459855636.25 56482542281.0  56548018252.1  56552213704.4  56701989985.3  56866543433.0  57035045711.2  57207515515.25 57306259454.3  57342651816.15 57482534197.15 57482534197.3  57482540262.14 57484626142.10 57484626142.13 57484626142.20 57484626142.22 57506545353.0  57762546121.0  57798265135.9  5782921199.30  5782921199.32  57956428391.1  58018546889.0  5801860124.34  58267442245.0  58577517210.8  58618833126.21 588087689.1    58866391733.0  58927178452.25 59213864045.4  59294818037.0  59308659786.7  59314873579.10 59314873579.12 59314873579.50 59314873579.8  59321247737.3  5958468464.24  59668206885.5  5967452503.23  59793447252.10 60054245101.25 60066553033.0  60070176529.21 60070176529.22 60070176529.23 60070176529.26 60070176529.27 60070176529.31 60587646784.30 60618587276.24 6062036074.10  60660975605.0  60769994324.25 61048795540.25 61052072480.13 61090556105.0  61097659196.8  61334462965.0  61369996644.25 61442230268.22461492795596.25 61510416471.4  61671366165.0  61807763572.13 61840518374.21 62291000355.1  62305507400.2  62403059225.25 62404581666.2  62450295377.20 62450295377.21 62450295377.22 62450295377.23 62450295377.26 62450295377.27 62450295377.31 62842451974.21 6292008538.4   63217930114.22 63489174179.1  6364460655.14  63662649864.22 63662649864.26 63662649864.30 63662649864.31 63667885863.2  63738881361.22 63991198558.6  63991199562.6  63991200330.6  63991200458.6  64026752006.4  64190421863.3  64192377451.7  64630052639.2  64763960740.7  65022046004.14 65210676195.5  65250602667.7  65840305187.1  65892131939.23 65910180450.86 65910180454.83 65910180588.80 66048936517.1  66096616852.25 66106208361.3  66149329551.26 66151427713.21 66151427842.17 66151427842.18 66151427842.21 66225212860.8  66263364923.1  6628837655.21  6628837655.22  6628837655.23  6628837655.26  6628837655.27  6628837655.31  6644311669.0   66459511919.2  6654053634.3   66782670395.20 66875768390.21 66967764304.83 66967764308.86 66985451747.8  67012675239.2  67069264406.21 67244368949.28 67267607413.0  67377962076.2  67678377324.30 67678377324.32 67762809634.1  67847990550.21 67935952956.8  67943623792.30 68022559995.7  68152758485.0  6816330454.21  68429482256.8  68542397710.8  68595398618.1  68597495712.1  68692784329.1  7027200167.2   7087516254.4   7230249383.2   7358704019.237 7497496250.3   7514568804.25  7580465913.26  7712883093.20  7722623749.1   7730449252.25  7739443299.8   7821893894.21  7873644531.15  7895480116.8   8193834485.0   8196673018.3   8196913479.8   8298967469.3   8570339392.26  8590582695.2   8592593028.2   8880602072.23  8887631729.9   8936802302.2   8938650181.21  8938650181.25  8938650181.26  9059237865.0   9082387894.21  9161320822.3   9343680608.3   9933288150.7   00000100:00A00B00M00N00O00P00Q00R00S00n00o01001@01A01E01I01J01d02D02E02F02G02H02M02N02X02]02^02b02f02m03403503603D03E03Z03[03c03k04;04<04=04L04M04N04O04P04Q04a04j04k04l04m04n04o05505M05N05X05\05]05^05a06106=06E06F06G06K06L06b06c06h06i07107G07H07I07N07O07P07_07`07a07b08308408508>08D08L08R08i09D09E09K09P09Q09X09Y09o0:00:50:60:J0:^0:d0;@0;A0;B0;H0;I0;T0;U0;V0;W0<10<C0<G0<K0<O0<P0<U0<V0=60=Z0=l0>20>30>40>50><0>=0>>0>?0>d0>e0>f0?00?10?G0?L0?O0?Z0?n0@50@:0@@0@A0@H0@l0A00A60A70A;0A<0AH0AP0AX0AY0A_0A`0Al0B20BK0Bd0C=0C>0C?0CH0CI0CJ0CW0CX0CY0C^0C_0Cl0Cm0Cn0D10DG0DO0DT0D[0D\0Dk0E20E30E40E50EN0EO0ET0EU0EV0EW0EX0Ea0Eb0F80FC0FN0FY0Fi0Fo0G<0G=0Gc0Gd0Ge0Gf0Gg0Gh0H30H40H50H60H=0H>0H?0H@0HG0HH0HI0HJ0HO0HP0HQ0Hb0Hh0I>0I?0I@0IJ0IK0IZ0Id0J90JA0JB0JC0JD0JE0JF0JG0JP0JQ0JR0J\0K40K50K60K70KC0Ko0LN0Lj0M@0MV0MW0MX0Mm0NB0NV0N\0Nj0O30O?0O@0OD0OI0Oo0P;0P@0PA0PB0PC0P^0Pa0Pb0Pc0Pd0Pe0Q60Q70Q;0Q<0Q=0QU0Qg0Qn0Qo0R20R=0R>0RD0RE0R_0Rj0Rk0Rl0Rm0Rn0S40S50SL0Sm0Sn0So0T00T10T20T30TC0TD0TE0TF0TG0TH0TI0TJ0TK0TL0TM0TP0TQ0TY0T_0U70U80U90UQ0UR0U^0Uc0Ud0Ue0Uf0Ug0Uk0VA0VD0VL0VT0V[0V`0Vg0Vh0Vi0Vj0Vk0Vl0Vm0W20W30W80W=0W>0W?0W@0WA0WE0WF0WQ0WR0W\0Wa0Wk0X;0X<0X=0XJ0XK0XL0Xf0Xg0Xh0Xi0Xj0Xm0Xn0Y60YL0Yb0Yc0Yd0Z40Z50Z=0ZF0ZG0ZO0ZP0ZV0Za0[<0[=0[>0[?0[@0[A0[B0[G0[H0[I0[J0[K0[j0\W0\X0\_0\l0\m0\n0\o0]00]10]70]80]90]:0];0]<0]=0]B0]C0]D0]I0]J0]R0]S0]T0]e0]f0]k0^F0^`0^o0_00_10_20_C0_D0_O0_P0_Q0_R0_S0_T0_U0_V0_W0_c0_l0_m0_n0_o0`00`10`20`30`40`50`D0`E0`I0`J0`T0`X0`\0`]0`^0`_0``0`h0`i0aE0aK0aL0aM0aN0aO0aP0aQ0aR0aS0aT0aU0a[0a_0ao0b60b70b<0b=0bE0bF0bG0bH0bI0bO0bP0bV0bW0b]0b^0bf0bn0cC0c\0cm0d50d60dI0dU0dV0dW0dX0d^0d_0d`0da0db0e20e30e40e<0e@0eI0eJ0eK0eL0eQ0eU0eV0eW0eb0ec0f=0fS0fW0fc0fg0g10g;0gE0gF0gG0gH0gO0gV0gW0gX0h:0h;0hL0hR0hS0hT0hU0h[0h\0hf0i30i<0iE0iS0i\0i`0ia0ie0im0j:0j;0j<0j=0j>0j?0j@0jA0jR0jd0k10k20k30k40k@0kA0kB0kC0kD0kP0kj0ko0l00l:0l@0lA0lB0lG0lH0l`0la0lb0lc0ld0le0lf0m60m;0m@0mA0mB0mC0mD0mj0mk0ml0nG0nR0n]0nh0o30o80o90o:0o;0o<0oL0oT0oU0oV10310;10B10I10J10K10L10f11311A11O11]11^11_11`11a11b11c11d11e11f11g11h12>12D12K12S12`12a12g13B13C13D13K13R13S13Y13Z13k13l13m14314;14<14@14E14F14G14H14I15915:15@15G15U15V15W15d15j16B16C16D16H16V16W16k17017417517@17D17E17F17U17V17\17c17d17eSS3RHI3EBRS2Q52Q6SS4CEIL2LO1HFFFFFFS3RES3RHI3FKO3DTO4LSTR4GLRRSSS4TBND4SHF24SHF3FS2S8S2S8SS4ABUB2G53RES3RHI3RSP4SEPLS3RES3RHI3FKO3DTO4SHF24SHF34LSTRFFFSS3LCHFS3RSP4Hc''S3LCHSS2HaS2HaS2Z02HaS2Z22HaFFS3RHI3RSP4Hc''SS3RES3RHI3RSP2P54DW13SS3RHI2FFS3RES2F3S3GR32G03GFS3GE'SFS4FBND3SHB4DBNDFFFFSS2SE3GR32G04SHLOS3RHI3EBRFSFFFS4TIMGS2S82G53RES3RHI3RSP4SEPESS3RES2F41HS2Z0FSS1ES4ABUB2S83FIT2D9S3Gs33Gs42SFS3DTF2D1FSS2F3SS4LSJ'3LN13LN25ENEXT1HSS3LCHFS3RHI2F3S4LSJ'3LN13LN25ENEXT1HSSS3LCHFFS3RES3RHI2F32DLSFFS2Q12Q22Q52Q63RSPFSS2SE4SHHIS4TIMGS2G53RSPS4Hc''S4LSJ'3LN13LN25ENEXT2KKS3RES3RHI3FKO3DTO4LSTR4GLRRFS4TIMGS3LCHSS2Ni2SiSS4LSJ'3LN13LN25ENEXT1HFS3SHBSS4LSJ'3LN13LN25ENEXTS4LSJ'3LN13LN25ENEXTS4TIMGS2S82G53RES3RHI3RSP4SEPG3R32SSS4SHF2SS2S82G63RSPFFFS3RES3RHI3RSP3FIT2P52DL2DGS3RES3RHI2F32DL2DGS2S8S2S8S2S8SS3Hc'SS3RES3RI23RI33FA21H2H02H42H53H14S3RES3RI23RI33U0'1H2H02H42H53H143FA2S2P81H2H02H42H52H9S4TIMGSFFS2Ni2SiFSFS3RES3RHI3FKO3DTO4SHF24SHF34LSTR4GLRRSFS3RSP4Hc''SS3RES3RHI3FKO3DTO4LSTRS3SHBS1DS3RHI2Z02Z2S2H12H23RHI2H52H62Z2S2H12H2S3Hc'S4TIMGSS2G32G4S4ABUB2G53RSP5UB16'3Ha'2K31D1H2H02H4S2HpS4CNT'SS2N1FS3RHI2Q13RI4S3GLS2HAS3GLS2HAFS4TIMGSS4CEIL2LO2HaS4TIMGS3H343H283H323H223H263H38S3H303H243H283H183H223H34S3H263H203H243H143H183H30FFS3RHI3EBRSSS3A242F24Hc''SFS3LCHSS3A242F24Hc''SFS1ES3RES3RHI3FKO3DTO4LSTRS3A242F2S3LN2S2Q52Q6SS2S82G63RSP3R32S2Ni2SiSFSS2SE3GR32GE3GFS4SHLO4SHHIFS3SHBSFSFS3UBS3PC0FS3RES3RHI2F33GNZ2DL2DES2SE3GFS2GES2SE3GFS2GES2SE3GFS2GES4ABUB2S83RES2SQS4TIMGS3A244Hc''2F2FS3RES3RHI3FKO3FKi3DTO3DFR4LSTR4GLRR2D2FFFFSS4CEIL2LO1HSSSS2Ni2SiFSFS5POS''FFSS3LCHSSS4ABUB2G53RHI3RSPS4TIMGS4ABUB2G53RHI3RSP4SHF3SSS4ABUB3PC0FS2HC1H2H02H42H5S3RSP4Hc''S4NBND4SHF24SHF34SBNDS3DTF2D1FSSFSFS3RHI3EBRSFS3FKi4DIMGS2S82G53RES3RHI3RSP4SEPLFSSS2Q23RI23RI3S3UBS4RUP82G63RSP5UB16'3Ha'2K11D1H2H42H93H10S3UBS4RUP82G85UB16'1H2H42H93H10S2S82G53RES3RHI3RSP4SEPE3R32S3RES3RHI3FKO3DTO4LSTRS3RES3RHI3FKO3DTO4LSTRSFS3RES3RHI2F32DL2HA2HKS3RES3RHI2F32DL2HA2HKS4LSJ'3LN13LN25ENEXTS4CNT'S3UBS2G63RSP1DS3UBS3PC0S3UBS2G33PC0FS2NES3SHBS2SE3GR32GE3GFS4SHM14SHM24SHB14SHB22HaS2N13LN13LN2S3R32FSSS3RES3RHI3FKO3DTO4LSTR4GLRRS1DSFSSS4ABUB2G53RHI3RSPFS2F4SSS3RES3RHI2F32DL2DE2HA2HKS3RES3EEB2DE2HA2HKS2Ni2SiFS1ES4CEIL2LO1HFS4TIMGFS4ABUB2G53RES3RHI3RSP4SEPES4CEIL2LO1HFSSSS4CNT'SS3RES3RHI3RSP3FIT2P52DLS3RES3RHI3FKO3FKi3DTO3DFR4LSTR2D2FFFFFSS3Gs23Gs43Gs52SFSSSSSSSFSSS1ESS2GE3GFSS4TIMGS2S82G53RES3RHI3RSP4SEPGFSS4CEIL2LO3RES2OT3FKO3DTOSS3RHI2Q13RI4S3GR3FFSFS2Y6S3RES3RHI3FKO3DTO4LSTRS1ES3H142G6S3H102G6S2H62G6S3LN1S5POS''FSSFFFS3Hc'FS3KK0S3KK0SSSSS2SESS4CEIL2LO1HFS3FKi4DIMGS3Gs5S3FKi4DIMGS4CEIL2LO4SHF31HFSS3RI23RI33FA2FSS3RES3RHI3RSP2P54DW134DW15SFSFS1ESS2Q13RI4S4ABUB2S83RES2SQ2HA2HKS4ABUB2S83RES2SQ2HA2HKSSS4TBND4SHF24SHF3FS2SE3GR3S3RHI3EBRFS3DTF2D1FS4SHF2S4ABUB2S81DS3RES3RHI3FKO3DTO4LSTR4GLRRSSSFFSS3SHBSFFFS4LSJ'2Y53LN13LN25ENEXT3LQg3LNgS3LEN4LSJ'2Z52Y53LN13LN25ENEXT2LQ3LNl3LQg3LNgSS3UBS1DS4ABUB2S83DW9SSSFSS4SHF2SSSSSFS3FITSSS3LCHSS2G53RSPSSS4ABUB2G53RHI3RSPFS3NE1S3RES3RHI3FKO3DTO4LSTR4GLRRS3RES3RHI3RSP2P54DW134DW14S3RUP4RUP82N11HFFSS4ABUB2G53RHI3RSPSS4ABUB2S81DSSSSSSSFS3RSP3FIT2P5S3RHI3EBRFFFFSSSSSS4ABUB2G53RSP1DFS2Y6FS3FKi4DIMGS2Z0S2Z0SSSSS3RSP2P5SS2S82G53RES3RHI3RSP4SEPL3R32S4TIMGSFFFFFFFFSS4TIMGS2Q6S4TBND4SHF24SHF3S2Q12Q2FS3Gs5SS3RSP2P6SSFFS4TIMGFS4SHLOFS4SHF1SS2G63RSPS3A242F2S3RHI3RI13FA11H2H02P7S3RHI3RI42U01H2H03RI13FA1S3FKi3Ha'2K11H2H0S3DTF2D1FS3RES3RHI2F33GNZ2DLS3RSP3FIT2P6FFFS4TIMGSFSSS3FKi4FBND2K12K3SSS3RHI2F3S2Z0S3RI13FA1SSSS3LCHS2Q6SSS4CEIL2LO1HSS3RES3RHI3RSP3FIT2P52DL2DES4ABUB2S82G52G63RSP2HaS2HaS2F32F42Ha1HS2HaS2E32E42HaS2F32F42HaS2H32H42HaSSFS2F42HKS2F42HKFSS2HC2G44SPal1H2H02H42H52H93H103H14SS2Q12Q22Q52Q63RSPS4TIMGSSSS4CNT'SS3NE11E2E'S3RHI2Z01E2F3S2Z14EBNZS2Z14EBNZS3RHI2Z02B32NES2Z04EBNZS2F3SS2F4S3FKO2K3S4ABUB2G53RSPSFFFFFFS4ABUB2G53RHI3RSPS3RES3RHI2F32DL2DES2G12G22G32G4SSSS2S82G64Hc''SFSSS2N13LN13LN2S4ABUB2G53RES3RHI3RSP4SEPGS3EQASS3RSP4Hc''S4TIMGSSS3R32FS3RES3FKO3DTO3DFR3EBR2D2FFFFFFS4TBND4SHF24SHF3S3Hc'S3SHBSFFFS4ABUB2S82G52G63RES3RSP3FKO3DTO3DFR2D2FFS3RES3RHI3FKO3DTO4LSTR4GLRRS2K12K33DFRS2K12K33DNFS2K12K33DTFS2K12K33DSFS3Hc'FFFFS2GE2G03GFS4SHHIS3A242F2SSS4ABUB2S83RES3RHI2F34SEPG3GNZS3H132G5S2H92G5S2H52G5SSFS4RM''2AM1H2H02H42H92Q42Q7S3FKO1H2H02H4S4RM''1H2H02H4S4AL''1H2H02H4S4UB161H2H02H4FFFFFFFFSFFS3RES3RHI3FKO3DTO4LSTRS4TIMGS2H52H6S2H93H10S3RHI3RI43FA1FS4TIMGS3FKO3FKi3AR81H2H02H42H52H9SFS2F32HAS2F32HASS4TIMGFS4ABUB2G53RHI3RSPFSS4TIMGS2SE3GR3FS2LQS3LQgSFSFS3HLO4ABLO2S83S162G12G22G33RZ13SP13LN13LN22Q12Q2FS4SHF2S2Ni2SiS3RHI4SHF33EBRSSS3RHI3RI43FA1S4TIMGS3Gs43Gs52Ct2SF2Cr2Cn2CsFSS2Y6S3RHI3RSP4Hc''FS3FKO3Ha'2K31H2H02H9S3T16S2QSSS2SE3GR32G0S2X1FFS3DNF2D33DSF2D4SS4TIMGS5POS''FS".
pose proof (aobj_int _ _ OC ltac:(clear; lia)) as (Ci & _ & [kC CBND]). pose proof (aobj_int _ _ ON ltac:(clear; lia)) as (Ni & _ & [kN NBND]).
pose proof (aobj_int _ _ OS ltac:(clear; lia)) as (Si & _ & [kS SBND]). pose proof (ao_res_hi L ALO) as RHI.
unfold aobj in RES, OT, OC, ON, OS. pose proof (ao_space L ALO) as RSP.
pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X1; unfold adisj in X1; clear -X1; lia).
box DL7. box DL8. box DL9. box DL10. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t. box CL5.
box DT. box DC. box DN. box DSO. box DF.
word_range sp SPR.
set (S := size_of_class c) in *. set (AB := aslot_addr L c k) in *. set (UB := AB + rz_size n) in *.
assert (EAB : AB = aslot_addr L c k) by reflexivity. assert (EUB : UB = AB + rz_size n) by reflexivity. assert (ES : S = size_of_class c) by reflexivity.
assert (EHM : fhm L c k n = UB - 16) by (unfold fhm; subst AB UB; clear; lia).
assert (UB16' : UB mod 8 = 0) by (clear -UB16; Z.div_mod_to_equations; lia).
rewrite EHM in PM.
destruct (read_chunk L st X m p c k n b1 ctx l1 l2 ALO WF XB (conj (proj1 (proj2 (proj2 (CLS c HC)))) (proj2 (proj2 (proj2 (CLS c HC))))))
as (_ & _ & UJR & LH & SHA & _ & SHR).
fold AB in UJR, LH, SHA, SHR. fold UB in UJR, LH, SHR. fold S in UJR, SHR.
pose proof AQ as AQ0. destruct AQ0 as ([QK MX] & [QC ABL] & [GCQ ABG] & (FL & IAS & IAM) & CP & NUM).
pose proof NUM as NUM0. destruct NUM0 as (NB1 & NB2 & NF & NC & NM).
pose proof CP as CP0. destruct CP0 as (LN1 & LN2 & _ & _ & ND2 & BSI & _).
pose proof (st_enq_bytes st p (CPrim c n) L X Q k24 stj chunks) as SB. cbn [chunk_size] in SB.
assert (CNT : enq_app st1 (CPrim c n) = None -> 0 < c_count (get_cls st K_BATCH_CLASS)).
{ intros E. destruct (enq_is_app st) eqn:EA.
- exfalso. assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CPrim c n)) EA1) as [s Hs]. congruence.
- exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (NEWF eq_refl)))))))). }
specialize (SB CNT). fold st1 st2 ek in SB. destruct SB as (SB1 & SB2 & SB3).
assert (ED0 : 0 <= ek_delta ek n /\ ek_delta ek n <= n + 8192) by (subst ek; unfold ek_of; destruct (enq_is_app st); cbn [ek_delta]; lia).
assert (EBK : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q) \/ (enq_is_app st = false /\ ek_b ek (qlast L (q_loc Q)) = abatch_addr L k24)).
{ subst ek. unfold ek_of. destruct (enq_is_app st) eqn:EA; cbn [ek_b]; [left; reflexivity| right; split; reflexivity]. }
assert (EBB : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q)
\/ exists kk, ek_b ek (qlast L (q_loc Q)) = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q))).
{ destruct EBK as [E|[EA E]]; [left; exact E| right; exists k24]. destruct (NEWF EA) as (NK & NB & KK & NIB & _). split; [exact E|]. split; [exact KK| exact NIB]. }
destruct (read_dk (AHQ DI ASEC AFK) L st X Q m RNG (BLive p) c k n b1 ctx l1 l2 ALO ARNG AR AQ XB ltac:(discriminate) (ek_b ek (qlast L (q_loc Q))) (ek_delta ek n) ek
(proj1 ED0) EBB ltac:(rewrite <- SB1, <- SB2; exact NOREC) eq_refl) as (_ & _ & GL & GLST).
fold g in GL, GLST.
set (lst := qlast L (q_loc Q)) in *. set (eb := ek_b ek lst) in *. set (gl := dk_glst g lst) in *. set (gq := shlen (rup n 8)) in *.
assert (BGEO : forall q, In q (q_loc Q ++ q_glob Q) ->
aregion L K_BATCH_CLASS <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
/\ al_res L + 4096 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= al_res L + 137439023104).
{ intros q Hq. pose proof (slot_geo L st X K_BATCH_CLASS (qb_slot q) ALO WF (K24) (bslot_range L st X Q WF CP q Hq)) as (_ & _ & _ & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _).
rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
assert (A24 : c_allocated_user (get_cls st K_BATCH_CLASS) <= K_FREEARR_OFF).
{ destruct WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC K_BATCH_CLASS (K24)) as (Q1 & Q2 & _). lia. }
assert (LSTF : lst = 0 \/ ((exists q, In q (q_loc Q) /\ lst = abatch_addr L (qb_slot q))
/\ aregion L K_BATCH_CLASS <= lst /\ lst + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
/\ al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104)).
{ subst lst. destruct (qlast_cases L (q_loc Q)) as [E0|(q & Hq & Eq)]; [left; exact E0| right].
assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; exact Hq).
rewrite Eq. split; [exists q; split; [exact Hq| reflexivity]|]. exact (BGEO q INq). }
assert (GDR : g_drain g = (Q_CACHE <? a_qloc_bytes st + ek_delta ek n)) by reflexivity.
assert (GLF : (g_drain g = false /\ gl = lst)
\/ (g_drain g = true /\ gl = qlast L (q_glob Q)
/\ (gl = 0 \/ ((exists q, In q (q_glob Q) /\ gl = abatch_addr L (qb_slot q))
/\ aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
/\ al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104)))).
{ subst gl. rewrite GLST, GDR. destruct (Q_CACHE <? a_qloc_bytes st + ek_delta ek n); [right| left; split; reflexivity].
split; [reflexivity|]. split; [reflexivity|].
destruct (qlast_cases L (q_glob Q)) as [E0|(q & Hq & Eq)]; [left; exact E0| right].
assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
rewrite Eq. split; [exists q; split; [exact Hq| reflexivity]|]. exact (BGEO q INq). }
assert (EBF : eb = 0 \/ (aregion L K_BATCH_CLASS <= eb /\ eb + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
/\ al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104)).
{ subst eb. destruct EBK as [E|[EA E]].
- rewrite E. destruct LSTF as [Z0|(_ & FF)]; [left; exact Z0| right; exact FF].
- right. rewrite E. destruct (NEWF EA) as (_ & _ & KK & _). pose proof (slot_geo L st X K_BATCH_CLASS k24 ALO WF (K24) KK) as (_ & _ & _ & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _).
rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
destruct PM as (id & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & sj'
& -> & MU & WM & MI' & ST' & IDR & HDR' & FC' & SH' & QC' & EKP & DKP & STATS' & LSJ' & UW' & FL' & IAS' & IAM' & DEP').
fold lst in MU, QC', EKP, DKP, EBK. fold eb in MU, EBK. fold gl in MU. fold gq in MU, SH'.
replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
assert (ELST : lst = qlast L (q_loc Q)) by reflexivity. assert (EEB : eb = ek_b ek lst) by reflexivity.
assert (EGL : gl = dk_glst g lst) by reflexivity. assert (EGQ : gq = shlen (rup n 8)) by reflexivity.
clearbody lst eb gl gq.
assert (MUn : munch (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) m m').
{ eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
clear MU.
assert (EBNZ : 0x10007fff8000 <= eb) by (rewrite EEB; exact (ek_pre_b_hi _ _ _ _ _ _ _ _ EK)).
assert (KF : kfactsF (bv_unsigned sp) (al_t L) AB S UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo (shlen (rz_size n)) (shlen S) lst eb gl).
{ unfold kfactsF. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
assert (GQ1 : 1 <= gq) by (rewrite EGQ, shlen_div; generalize RUP RUP8 N1; clear; intros; Z.div_mod_to_equations; lia).
generalize CEIL LO OT OC ON OS RES RHI RSP G5 G6 ABUB UBS S8 RUP EUB SHLO SE GR3 GQ1 GFS GE SHHI LSTF EBF GLF EBNZ. clear. intros.
unfold iclr, AIMG_LO, AIMG_HI in *.
(destruct LSTF as [Z0|(_ & FF)]; [rewrite (qsz_eq0 lst Z0) | rewrite (qsz_pos lst) by (atop_facts; lia)]);
(destruct EBF as [Z1|FF1]; [exfalso; atop_facts; lia|]); destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & FF2)])];
repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; first [assumption | lia]. }
pose proof (KF_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
pose proof (KF_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
pose proof (KF_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
pose proof (KF_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
pose proof (KF_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_c_t) (unbxF D_c_res) (unbxF D_c_n) (unbxF D_c_s)) as Kctx.
pose proof (KF_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF DL7) (unbxF DL8)) as Kt.
pose proof (KF_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF D_n_res) (unbxF D_s_res)) as Kres.
pose proof (KF_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
assert (SC : same_core st1 (st_after st2) /\ a_cinit (st_after st2) = a_cinit st /\ a_live (st_after st2) = delete p (a_live st) /\ a_next (st_after st2) = a_next st
/\ a_space_beg (st_after st2) = a_space_beg st /\ a_ptr_array (st_after st2) = a_ptr_array st
/\ (enq_is_app st = true -> a_cls (st_after st2) = a_cls st)
/\ (enq_is_app st = false -> a_cls (st_after st2) = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
{ pose proof (st_after_core st2) as [SC2 CL2'].
assert (SC1 : same_core st1 st2 /\ (enq_is_app st = true -> a_cls st2 = a_cls st) /\ (enq_is_app st = false -> a_cls st2 = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
{ subst st2. unfold st_enq. destruct (enq_app st1 (CPrim c n)) as [sx|] eqn:EAPP.
- destruct (enq_app_Some st1 _ sx EAPP) as (l & bl & QL & NFz & ->). split; [repeat split; intros; reflexivity|].
split; [intros _; reflexivity|]. intros EA. exfalso.
assert (EA1 : enq_is_app st1 = true) by (apply (proj2 (enq_is_app_spec st1 (CPrim c n))); eexists; exact EAPP).
change (enq_is_app st1) with (enq_is_app st) in EA1. congruence.
- pose proof (enq_new_core (CPrim c n) st1) as (C1 & _ & _ & _ & _ & _ & C7). split; [exact C1|].
split; [| intros _; exact C7]. intros EA. exfalso.
assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CPrim c n)) EA1) as [s Hs]. congruence. }
destruct SC1 as (SC1 & CLa & CLb). pose proof (same_core_trans _ _ _ SC1 SC2) as SC3.
pose proof SC3 as SC0. destruct SC0 as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
split; [exact SC3|]. split; [exact F3|]. split; [exact F1|]. split; [exact F2|]. split; [exact F4|]. split; [exact F5|].
split; [intros EA; rewrite CL2'; exact (CLa EA)| intros EA; rewrite CL2'; exact (CLb EA)]. }
destruct SC as (SC & ECIN & ELIVE & ENEXT & ESB & EPA & CLa & CLb).
pose proof SC as SC0. destruct SC0 as (_ & _ & _ & _ & _ & ENRES & ENSEC & GCo & M24a & M24b & M24c & M24d).
set (st' := st_after st2) in *.
set (X' := xfree X (enq_is_app st) c k n b1 ctx l1 l2 k24).
assert (GC24 : get_cls st' K_BATCH_CLASS = (if enq_is_app st then get_cls st K_BATCH_CLASS else cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS))).
{ unfold get_cls at 1. destruct (enq_is_app st) eqn:EA; [rewrite (CLa eq_refl); reflexivity| rewrite (CLb eq_refl), lookup_insert_eq; reflexivity]. }
assert (GCo' : forall c', c' <> K_BATCH_CLASS -> get_cls st' c' = get_cls st c') by (intros c' NE; rewrite (GCo c' NE); reflexivity).
assert (NDS : forall c', ndist st' c' = ndist st c').
{ intros c'. unfold ndist. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE]; [rewrite M24b; reflexivity| rewrite (GCo' c' NE); reflexivity]. }
assert (MC' : forall c', max_count st' c' = max_count st c') by (intros c'; unfold max_count; rewrite ECIN; reflexivity).
assert (WF1 : awf L st1 (xquar X c k n b1 ctx l1 l2)) by (apply (awf_xquar L st X p c k n b1 ctx l1 l2 XB WF); reflexivity).
assert (WF' : awf L st' X').
{ subst X'. unfold xfree. destruct (enq_is_app st) eqn:EA.
- apply (awf_xquar L st X p c k n b1 ctx l1 l2 XB WF); [exact ESB| exact EPA| exact ECIN| exact (CLa eq_refl)| exact ELIVE| exact ENEXT].
- destruct (NEWF eq_refl) as (NK & NB & KK & NIB & JK & FSH & CIN & POS).
apply (awf_xbatch L st1 (xquar X c k n b1 ctx l1 l2) k24 (c_count (get_cls st K_BATCH_CLASS)) WF1 eq_refl POS NK).
+ exact ESB. + exact EPA. + exact ECIN. + rewrite ELIVE; reflexivity. + exact ENEXT.
+ intros c' NE. rewrite (GCo' c' NE). reflexivity.
+ rewrite GC24. reflexivity. }
assert (RT' : arep_rt L m').
{ eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
assert (INST' : ainstance L st' m').
{ eapply ainstance_frame; [exact MUn | exact WM | exact INST | exact ENRES | exact ENSEC | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
assert (HRO' : arelro m') by (eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]).
assert (HRT2' : arep_rt2 m') by (eapply arep_rt2_frame; [exact MUn | exact WM | exact HRT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia).
assert (RT3' : arep_rt3 m') by (eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil).
assert (THR' : athread L st' X' m').
{ unfold athread. split; [| split; [| split; [| split; [| split]]]].
- eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
- eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
- intros c' Hc'. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE].
+ destruct (CACHES K_BATCH_CLASS Hc') as [tail (CR & CH & LCH)]. unfold acache_cells. cbv zeta.
rewrite GC24, MC', ECIN. subst X'. rewrite xfree_cache, Z.eqb_refl, andb_true_r.
replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR, CH |- * by (unfold acache_addr, K_BATCH_CLASS; clear; lia).
subst ek. unfold ek_of in EKP. destruct (enq_is_app st) eqn:EA; cbn [ek_post negb] in EKP |- *.
* destruct EKP as (_ & _ & _ & CR' & _). exists tail. split; [exact CR'|]. split; [| exact LCH].
eapply u32arr_frame; [exact CH | exact MUn | exact WM |]. rewrite length_app, length_map. apply Kt; clear -LCH; lia.
* destruct EKP as (CR' & _). destruct (NEWF eq_refl) as (NK & NB & KK & NIB & JK & FSH & CIN & POS).
cbn [c_count cls_set_count]. exists (Z_to_bv 64 (acompact K_BATCH_CLASS k24) :: tail).
pose proof (cache24_split L st X k24 (c_count (get_cls st K_BATCH_CLASS)) WF eq_refl POS NK) as [CACHE LRL].
split; [exact CR'|]. split.
-- eapply u32arr_frame; [| exact MUn | exact WM |].
++ rewrite CACHE, map_app in CH. cbn [map] in CH. rewrite <- app_assoc in CH. cbn [app] in CH. exact CH.
++ rewrite length_app, length_map. cbn [length].
replace (length (removelast (xc_cache (x_cls X K_BATCH_CLASS))) + Datatypes.S (length tail))%nat with 16%nat
by (rewrite CACHE, length_app in LCH; cbn [length] in LCH; clear -LCH; lia).
apply Kt; clear; lia.
-- cbn [length]. rewrite CACHE, length_app in LCH. cbn [length] in LCH. clear -LCH. lia.
+ eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | rewrite (GCo' c' NE); reflexivity | exact ECIN | |].
* subst X'. rewrite xfree_cache. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [E|_]; [exfalso; exact (NE E)|]. rewrite andb_false_r. reflexivity.
* unfold acache_addr. unfold K_NUM_CLASSES, K_BATCH_CLASS in *. apply Kt; clear -Hc' NE; lia.
- apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
+ eapply junk_frame; [exact (proj1 (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia))) | exact MUn | exact WM | intros _; apply Kt; clear; lia].
+ apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
* replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia).
assert (STJ' : exists w : word, rw_cells asegs m' (al_t L + 2784) [C8 w]).
{ subst ek. unfold ek_of in EKP. destruct (enq_is_app st); cbn [ek_post] in EKP.
- destruct EKP as (_ & _ & _ & _ & STS'). exists stj. exact STS'.
- destruct EKP as (_ & STS' & _). exact STS'. }
destruct STJ' as [w STS']. pose proof (junk_of_cells m' _ _ STS') as J. cbn in J. exact J.
* replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) by (clear; lia).
eapply junk_frame; [| exact MUn | exact WM | intros _; apply Kt; clear; lia].
pose proof (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ CSb].
pose proof (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(clear; lia) ltac:(clear; lia)) as [_ CSc].
replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by (clear; lia). exact CSc.
- exists sj'. split; [exact STATS' | exact LSJ'].
- exact UW'. }
assert (SEPQ : forall q, In q (q_loc Q ++ q_glob Q) -> AB + S <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= AB).
{ intros q Hq. destruct (bslot_busy L st X Q CP q Hq) as (yq & Hyq & Syq & Cyq & Kyq).
pose proof (slots_sep_any L st X c k K_BATCH_CLASS (qb_slot q) ALO WF HC (K24) KR (bslot_range L st X Q WF CP q Hq)
ltac:(rewrite <- Cyq, <- Kyq; apply (other_key (AHQ DI ASEC AFK) L st X m (BLive p) c k n b1 ctx l1 l2 AR XB); [exact Hyq| rewrite Syq; discriminate])) as D.
rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
assert (SEPK : enq_is_app st = false -> AB + S <= abatch_addr L k24 \/ abatch_addr L k24 + 8192 <= AB).
{ intros EA. destruct (NEWF EA) as (NK & NB & KK & _).
pose proof (slots_sep_any L st X c k K_BATCH_CLASS k24 ALO WF HC (K24) KR KK
ltac:(destruct (Z.eq_dec c K_BATCH_CLASS) as [->|NE]; [right| left; exact NE]; intros ->;
pose proof (busy_of_X_self L st X p K_BATCH_CLASS k24 n b1 ctx l1 l2 XB WF) as E'; rewrite NB in E'; discriminate)) as D.
rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
assert (SEPL : lst = 0 \/ (AB + S <= lst \/ lst + 8192 <= AB)).
{ destruct LSTF as [Z0|((q & Hq & Eq) & _)]; [left; exact Z0| right; rewrite Eq; apply SEPQ; apply in_or_app; left; exact Hq]. }
assert (SEPE : eb = 0 \/ (AB + S <= eb \/ eb + 8192 <= AB)).
{ subst eb. destruct EBK as [E|[EA E]]; rewrite E; [exact SEPL| right; exact (SEPK EA)]. }
assert (SEPG : gl = 0 \/ (AB + S <= gl \/ gl + 8192 <= AB)).
{ destruct GLF as [[_ ->]|(_ & _ & [Z0|((q & Hq & Eq) & _)])]; [exact SEPL| left; exact Z0| right; rewrite Eq; apply SEPQ; apply in_or_app; right; exact Hq]. }
assert (BDIS : forall q1 q2, In q1 (q_loc Q ++ q_glob Q) -> In q2 (q_loc Q ++ q_glob Q) ->
abatch_addr L (qb_slot q1) = abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q1) + 8192 <= abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q2) + 8192 <= abatch_addr L (qb_slot q1)).
{ intros q1 q2 H1 H2. destruct (Z.eq_dec (qb_slot q1) (qb_slot q2)) as [E|NE]; [left; rewrite E; reflexivity| right].
pose proof (slots_disjoint L K_BATCH_CLASS (qb_slot q1) (qb_slot q2) ltac:(pose proof (bslot_range L st X Q WF CP q1 H1); lia)
ltac:(pose proof (bslot_range L st X Q WF CP q2 H2); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
assert (KDIS : forall q, In q (q_loc Q ++ q_glob Q) -> enq_is_app st = false ->
abatch_addr L k24 + 8192 <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= abatch_addr L k24).
{ intros q Hq EA. destruct (NEWF EA) as (NK & NB & KK & NIB & _).
assert (NE : k24 <> qb_slot q) by (intros ->; apply NIB; apply in_map; exact Hq).
pose proof (slots_disjoint L K_BATCH_CLASS k24 (qb_slot q) ltac:(lia) ltac:(pose proof (bslot_range L st X Q WF CP q Hq); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
aregion_cells L st' m' c'' /\ afreearray L st' X' m' c'' /\ aslots L st' X' m' c'' /\ aslot_shadow L st' X' m' c'').
{ intros c'' Hc''. destruct (CLS c'' Hc'') as (REG & FARR & SLOTS & SHADOW).
pose proof WF as WF0. destruct WF0 as (_ & _ & SAL & _ & _ & PERC & _).
destruct (PERC c'' Hc'') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
pose proof (aregion_mod L c'' SAL) as RM''.
assert (EC1 : c_num_freed (get_cls st' c'') = c_num_freed (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24c| rewrite (GCo' c'' NE); reflexivity]).
assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
assert (EC3 : c_allocated_user (get_cls st' c'') = c_allocated_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24b| rewrite (GCo' c'' NE); reflexivity]).
assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
unfold K_NUM_CLASSES in Hc''.
assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
/\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104 /\ al_res L + 4096 <= aregion L c'').
{ unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
destruct RI as (RI1 & RI2 & RI3 & RI4).
assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
split; [| split; [| split]].
- eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | exact EC1 | exact EC2 | exact EC3 | exact EC4 |].
unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
apply Kres; try (clear -Hc'' RSP G6 S8 EUB; lia).
+ destruct LSTF as [Z0|(_ & F1 & F2 & F3 & F4)]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
+ destruct EBF as [Z0|(F1 & F2 & F3 & F4)]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
+ assert (GLR : gl = 0 \/ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)).
{ destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; exact F2].
destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; exact F2]. }
destruct GLR as [Z0|F2]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
- eapply afreearray_frame; [exact MUn | exact WM | exact FARR | exact EC1 | exact EC2 | | exact QLENF | exact Q5 | | clear -Q6; lia |].
+ subst X'. apply xfree_free.
+ assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
{ unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
destruct FA1 as [FA1 FA2].
apply Kres; [clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia | clear -RI2 RI3 FA2; lia | clear -Q5 Q6; lia | | | |].
* pose proof (farr_vs_user L c'' c _ _ AB S (proj1 PC0) (proj1 (proj2 PC0)) FA1 FA2) as D. clear -D ABUB S8 EUB. lia.
* destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
exact (farr_vs_user L c'' K_BATCH_CLASS _ _ lst 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2).
* destruct EBF as [Z0|(F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
exact (farr_vs_user L c'' K_BATCH_CLASS _ _ eb 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2).
* assert (GLR : gl = 0 \/ (aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS))).
{ destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; split; [exact F1| exact F2]].
destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; split; [exact F1| exact F2]]. }
destruct GLR as [Z0|[F1 F2]]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
pose proof (farr_vs_user L c'' K_BATCH_CLASS _ _ gl 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2) as D. clear -D. lia.
+ assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
{ unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
destruct FA1 as [FA1 FA2].
apply Kshad.
* rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -RI1 FA1 RES RHI. Z.div_mod_to_equations. lia.
* rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -RI2 RI3 FA2 RES RHI. Z.div_mod_to_equations. lia.
* apply shlen_nonneg. clear -Q5 Q6. lia.
* pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
assert (AM : afreearr L c'' mod 8 = 0) by (unfold afreearr, K_FREEARR_OFF; clear -RM''; Z.div_mod_to_equations; lia).
rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| clear -UB16; Z.div_mod_to_equations; lia]].
-
eapply (aslots_update_gen L _ m m' MUn WM st st' X X' c''); [exact SLOTS | apply NDS | exact EC3 | exact EC4 | |].
+ intros k'' Hk''.
pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as (T16 & TM16 & TAL & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _).
assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
*
subst c'' k''. right.
subst X'. rewrite (busy_of_xfree L st X p c k n b1 ctx l1 l2 (enq_is_app st) k24 c k XB WF).
assert (NOK : (negb (enq_is_app st) && (K_BATCH_CLASS =? c) && (k24 =? k)) = false).
{ destruct (enq_is_app st) eqn:EA; [reflexivity|]. cbn [negb andb].
destruct (Z.eqb_spec K_BATCH_CLASS c) as [E1'|]; [| reflexivity]. destruct (Z.eqb_spec k24 k) as [E2'|]; [| reflexivity]. exfalso.
destruct (NEWF eq_refl) as (_ & NB & _). pose proof (busy_of_X_self L st X p c k n b1 ctx l1 l2 XB WF) as E'. rewrite <- E1', <- E2', NB in E'. discriminate. }
rewrite NOK, !Z.eqb_refl. cbn [andb].
unfold aslot_busy, bquar. cbn [xb_st xb_class xb_n xb_b1 xb_ctx xb_slot bstate_byte]. unfold xb_user, xb_hdr, xb_alloc. cbn [xb_class xb_slot xb_n].
rewrite <- EAB. fold S. rewrite <- EUB.
split; [| split].
-- intros R16. pose proof (rz_gt16 n (proj1 N0) R16) as R32. destruct (LH R16) as [LC LJ]. split.
++ eapply cells_frame; [exact LC | exact MUn | exact WM |]. cbn [cells_size csize Nat.add].
apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8 SEPL SEPE SEPG; unfold K_SPACE_SIZE in *; lia.
++ eapply junk_frame; [exact LJ | exact MUn | exact WM |]. intros Hp.
apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8 SEPL SEPE SEPG Hp; unfold K_SPACE_SIZE in *; lia.
-- exists 3. split; [reflexivity|]. exact HDR'.
-- replace (S - rz_size n) with (8 + (S - rz_size n - 8)) by (clear; lia).
apply (junk_merge m' UB 8 (S - rz_size n - 8)); [| | clear; lia | clear -S8; lia].
++ pose proof (junk_of_cells m' _ _ FC') as J. cbn in J. exact J.
++ eapply junk_frame; [exact UJR | exact MUn | exact WM |]. intros Hp.
apply Kres; clear -G5 G6 RSP RES RHI S16 EUB ABUB S8 SEPL SEPE SEPG Hp; unfold K_SPACE_SIZE in *; lia.
*
assert (T2 : (c =? c'') && (k =? k'') = false).
{ destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
assert (D2 : (enq_is_app st = false /\ c'' = K_BATCH_CLASS /\ k'' = k24) \/ (enq_is_app st = true \/ c'' <> K_BATCH_CLASS \/ k'' <> k24))
by (destruct (enq_is_app st); clear; lia).
destruct D2 as [(EA & E24 & EK24)|NE2].
--
subst c'' k''. right.
subst X'. rewrite (busy_of_xfree L st X p c k n b1 ctx l1 l2 (enq_is_app st) k24 K_BATCH_CLASS k24 XB WF), EA. cbn [negb andb]. rewrite !Z.eqb_refl. cbn [andb].
unfold aslot_busy, bbatch. cbn [xb_st xb_class xb_slot]. unfold xb_alloc. cbn [xb_class xb_slot]. rewrite size_of_class_24.
subst ek. unfold ek_of in EKP. rewrite EA in EKP. cbn [ek_post] in EKP. destruct EKP as (_ & _ & BC & BA & [bsb BJ] & _).
fold (abatch_addr L k24) in BC, BA, BJ |- *. change (aslot_addr L K_BATCH_CLASS k24) with (abatch_addr L k24).
replace 8192 with (24 + (8 * Z.of_nat (length [Z_to_bv 64 (UB - 16)]) + (8192 - 24 - 8 * 1))) by (cbn; lia).
apply junk_merge; [| | clear; lia| cbn; clear; lia].
++ pose proof (junk_of_cells m' _ _ BC) as J. cbn in J. exact J.
++ apply junk_merge; [apply junk_of_u64arr; exact BA | | cbn; clear; lia | clear; lia].
cbn [length Z.of_nat Pos.of_succ_nat]. eexists. exact BJ.
-- assert (T1 : negb (enq_is_app st) && (K_BATCH_CLASS =? c'') && (k24 =? k'') = false).
{ destruct (enq_is_app st); cbn [negb andb]; [reflexivity|].
destruct (Z.eqb_spec K_BATCH_CLASS c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k24 k'') as [E'|]; [| reflexivity]. exfalso.
destruct NE2 as [NE|[NE|NE]]; [discriminate| apply NE; symmetry; exact E| apply NE; symmetry; exact E']. }
assert (BX : busy_of X' c'' k'' = busy_of X c'' k'').
{ subst X'. rewrite (busy_of_xfree L st X p c k n b1 ctx l1 l2 (enq_is_app st) k24 c'' k'' XB WF), T1, T2. reflexivity. }
assert (BQ : forall q, In q (q_loc Q ++ q_glob Q) -> c'' = K_BATCH_CLASS -> aslot_addr L c'' k'' = abatch_addr L (qb_slot q) ->
exists yq, busy_of X c'' k'' = Some yq /\ xb_st yq = BBatch /\ xb_class yq = K_BATCH_CLASS /\ xb_slot yq = k''
/\ junk_at m (abatch_addr L (qb_slot q)) 8192 /\ k'' = qb_slot q).
{ intros q Hq -> EQA. destruct (bslot_busy L st X Q CP q Hq) as (yq & Hyq & Syq & Cyq & Kyq).
assert (EK' : k'' = qb_slot q) by (unfold abatch_addr, aslot_addr in EQA; rewrite size_of_class_24 in EQA; clear -EQA; lia). subst k''.
exists yq. pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq in BY.
split; [exact BY|]. split; [exact Syq|]. split; [exact Cyq|]. split; [exact Kyq|]. split; [| reflexivity].
destruct SLOTS as [SLK _]. specialize (SLK (qb_slot q) Hk''). rewrite BY in SLK. unfold aslot_busy in SLK. rewrite Syq in SLK.
unfold xb_alloc in SLK. rewrite Cyq, Kyq, size_of_class_24 in SLK. exact SLK. }
assert (D3 : (c'' = K_BATCH_CLASS /\ lst <> 0 /\ aslot_addr L c'' k'' = lst) \/ (c'' <> K_BATCH_CLASS \/ lst = 0 \/ aslot_addr L c'' k'' <> lst)) by (clear; lia).
destruct D3 as [(E24 & LNZ & EL)|NE3].
++
right. rewrite BX. destruct LSTF as [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)]; [exfalso; exact (LNZ Z0)|].
destruct (BQ q ltac:(apply in_or_app; left; exact Hq) E24 ltac:(rewrite EL; exact Eq)) as (yq & BY & Syq & Cyq & Kyq & JQ & EKQ).
rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EL.
assert (QNE : a_qloc st <> []) by (intros QL0; apply LNZ; rewrite ELST; replace (q_loc Q) with (@nil qbatchc) by (destruct (q_loc Q); [reflexivity| rewrite QL0 in LN1; cbn in LN1; discriminate]); reflexivity).
subst ek. unfold ek_of in EKP, EK. destruct (enq_is_app st) eqn:EA; cbn [ek_post ek_pre] in EKP, EK.
** destruct EKP as (LB' & LA' & [bs LJ'] & _). destruct EK as (_ & _ & CNT' & _ & _ & _ & _ & LEN & _).
rewrite ELST in LB', LA', LJ' |- *.
set (cnt := b_count (List.last (a_qloc st) dummy_batch)) in *.
replace 8192 with (24 + (8 * Z.of_nat (length (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb))) ++ [Z_to_bv 64 (UB - 16)])) + (8192 - 24 - 8 * (cnt + 1))))
by (rewrite length_app, LEN; cbn [length]; clear -CNT'; lia).
apply junk_merge; [| | clear; lia| rewrite length_app, LEN; cbn [length]; clear -CNT'; lia].
+++ pose proof (junk_of_cells m' _ _ LB') as J. cbn in J. exact J.
+++ apply junk_merge; [apply junk_of_u64arr; exact LA' | | rewrite length_app, LEN; cbn [length]; clear -CNT'; lia | clear -CNT'; lia].
rewrite length_app, LEN. cbn [length]. replace (8 * Z.of_nat (Z.to_nat cnt + 1)) with (8 * (cnt + 1)) by (clear -CNT'; lia). eexists. exact LJ'.
** destruct (a_qloc st) as [|b0 bs0] eqn:QL0; [exfalso; exact (QNE eq_refl)|]. rewrite <- QL0 in *.
destruct EKP as (_ & _ & _ & _ & _ & [LB' LA']). destruct EK as ((_ & _ & _ & _ & _ & _ & _ & LEN0 & _) & _).
rewrite ELST in LB', LA' |- *.
replace 8192 with (24 + 8 * Z.of_nat (length (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb))))))
by (rewrite LEN0; clear; lia).
apply junk_merge; [| apply junk_of_u64arr; exact LA' | clear; lia| rewrite LEN0; clear; lia].
pose proof (junk_of_cells m' _ _ LB') as J. cbn in J. exact J.
++ assert (D4 : (g_drain g = true /\ c'' = K_BATCH_CLASS /\ gl <> 0 /\ aslot_addr L c'' k'' = gl /\ gl <> lst)
\/ (g_drain g = false \/ c'' <> K_BATCH_CLASS \/ gl = 0 \/ aslot_addr L c'' k'' <> gl \/ gl = lst)) by (destruct (g_drain g); clear; lia).
destruct D4 as [(GD & E24 & GNZ & EG & GNL)|NE4].
**
right. rewrite BX. destruct GLF as [[GD' _]|(_ & GQL & [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)])]; [congruence| exfalso; exact (GNZ Z0)|].
destruct (BQ q ltac:(apply in_or_app; right; exact Hq) E24 ltac:(rewrite EG; exact Eq)) as (yq & BY & Syq & Cyq & Kyq & JQ & EKQ).
rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EG.
assert (GNE : a_qglob st <> []) by (intros QG0; destruct (q_glob Q) eqn:QQ0; [destruct Hq| rewrite QG0 in LN2; cbn in LN2; discriminate]).
unfold dk_post in DKP. rewrite GD in DKP. destruct DKP as (_ & _ & GLN).
assert (GF : g_full g = true) by (subst g; unfold g_of; cbn [g_full]; destruct (a_qglob st); [exfalso; exact (GNE eq_refl)| reflexivity]).
rewrite GF, GL, <- GQL in GLN.
replace 8192 with (8 + 8184) by (clear; lia). apply junk_merge; [| | clear; lia | clear; lia].
+++ pose proof (junk_of_cells m' _ _ GLN) as J. cbn in J. exact J.
+++ rewrite <- Eq in JQ. destruct (junk_split m gl 8 8184 JQ ltac:(clear; lia) ltac:(clear; lia)) as [_ J2].
eapply junk_frame; [exact J2 | exact MUn | exact WM |]. intros _.
assert (DL : lst = 0 \/ lst + 8192 <= gl \/ gl + 8192 <= lst).
{ destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql, Eq.
destruct (BDIS ql q ltac:(apply in_or_app; left; exact Hql) ltac:(apply in_or_app; right; exact Hq)) as [E|E]; [| exact E].
exfalso. apply GNL. rewrite Eq, Eql. symmetry. exact E. }
assert (DE : eb = lst \/ eb + 8192 <= gl \/ gl + 8192 <= eb).
{ destruct EBK as [E|[EA E]]; [left; exact E| right]. rewrite E, Eq. exact (KDIS q ltac:(apply in_or_app; right; exact Hq) EA). }
apply Kres; clear -F3 F4 RES RHI SEPG GNZ DL DE ABUB S8 EUB; lia.
**
left. split; [exact BX|]. split.
+++ assert (DW9 : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
{ pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
rewrite <- EAB, <- ES in D. exact D. }
assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> (c'' <> K_BATCH_CLASS \/ aslot_addr L c'' k'' <> abatch_addr L (qb_slot q)) ->
aslot_addr L c'' k'' + size_of_class c'' <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= aslot_addr L c'' k'').
{ intros q Hq NE. pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS (qb_slot q) ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk''
(bslot_range L st X Q WF CP q Hq) ltac:(destruct NE as [NE|NE]; [left; exact NE| destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NC']; [right| left; exact NC']];
intros EKK; apply NE; rewrite EKK; reflexivity)) as D.
rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
assert (DW13 : lst = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= lst \/ lst + 8192 <= aslot_addr L c'' k'').
{ destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql. apply DQ; [apply in_or_app; left; exact Hql|].
destruct NE3 as [NE|[Z0|NE]]; [left; exact NE| exfalso| right; rewrite <- Eql; exact NE].
rewrite Eql in Z0. destruct (BGEO ql ltac:(apply in_or_app; left; exact Hql)) as (_ & _ & B3 & _). clear -Z0 B3 RES RHI. lia. }
assert (DW14 : eb = lst \/ aslot_addr L c'' k'' + size_of_class c'' <= eb \/ eb + 8192 <= aslot_addr L c'' k'').
{ destruct EBK as [E|[EA E]]; [left; exact E| right]. rewrite E. destruct (NEWF EA) as (_ & _ & KK & _).
pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS k24 ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk'' KK
ltac:(destruct NE2 as [NE|[NE|NE]]; [rewrite EA in NE; discriminate| left; exact NE| right; exact NE])) as D.
rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
assert (DW15 : gl = lst \/ gl = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= gl \/ gl + 8192 <= aslot_addr L c'' k'').
{ destruct GLF as [[_ E]|(GD & GQL & [Z0|((q & Hq & Eq) & _)])]; [left; exact E| right; left; exact Z0| right; right].
rewrite Eq. apply DQ; [apply in_or_app; right; exact Hq|].
destruct NE4 as [NE|[NE|[NE|[NE|NE]]]]; [congruence| left; exact NE| | right; rewrite <- Eq; exact NE| ].
- exfalso. rewrite Eq in NE. destruct (BGEO q ltac:(apply in_or_app; right; exact Hq)) as (_ & _ & B3 & _). clear -NE B3 RES RHI. lia.
- rewrite NE in *. destruct NE3 as [NE'|[Z0|NE']]; [left; exact NE'| exfalso| right; rewrite <- Eq; exact NE'].
rewrite Eq in Z0. destruct (BGEO q ltac:(apply in_or_app; right; exact Hq)) as (_ & _ & B3 & _). clear -Z0 B3 RES RHI. lia. }
apply Kres; [clear -P5 RSP; lia | clear -P6 RSP; unfold K_SPACE_SIZE in *; lia | clear -T16; lia | clear -DW9 ABUB S8 EUB; lia
| clear -DW13 P5 RSP RES RHI; lia | clear -DW14 DW13 P5 RSP RES RHI; lia | clear -DW15 DW13 P5 RSP RES RHI; lia].
+++ intros b Hb. destruct (busy_of_Some_facts X c'' k'' b Hb) as (IB & CB' & KB'). split; [exact CB'|]. split; [exact KB'|]. exact (awf_fits L st X b WF IB).
+ intros POS''.
set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
destruct U0 as [U0 U0'].
assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
assert (U2 : c'' = K_BATCH_CLASS -> aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
idtac "UND1".
apply Kres; [clear -RI4 Q1 U0; lia | subst AU; clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia | clear -POS''; lia | | | |].
* pose proof (undist_vs_user L c'' c _ _ AB S (c_allocated_user (get_cls st c)) (proj1 PC0) (proj2 (proj2 PC0)) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
clear -D ABUB S8 EUB. lia.
* destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
exact (undist_vs_user L c'' K_BATCH_CLASS _ _ lst 8192 _ F1 F2 A24 U2 U0 U0').
* destruct EBF as [Z0|(F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
exact (undist_vs_user L c'' K_BATCH_CLASS _ _ eb 8192 _ F1 F2 A24 U2 U0 U0').
* assert (GLR : gl = 0 \/ (aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS))).
{ destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; split; [exact F1| exact F2]].
destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; split; [exact F1| exact F2]]. }
destruct GLR as [Z0|[F1 F2]]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
pose proof (undist_vs_user L c'' K_BATCH_CLASS _ _ gl 8192 _ F1 F2 A24 U2 U0 U0') as D. clear -D. lia.
-
eapply (aslot_shadow_update_gen L _ m m' MUn WM st st' X X' c''); [exact SHADOW | apply NDS | exact EC3 | exact EC4 | | | apply shlen_nonneg; clear -QS; lia].
+ intros k'' Hk''.
pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as (T16 & TM16 & TAL & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _).
assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
*
subst c'' k''. right.
subst X'. rewrite (busy_of_xfree L st X p c k n b1 ctx l1 l2 (enq_is_app st) k24 c k XB WF).
assert (NOK : (negb (enq_is_app st) && (K_BATCH_CLASS =? c) && (k24 =? k)) = false).
{ destruct (enq_is_app st) eqn:EA; [reflexivity|]. cbn [negb andb].
destruct (Z.eqb_spec K_BATCH_CLASS c) as [E1'|]; [| reflexivity]. destruct (Z.eqb_spec k24 k) as [E2'|]; [| reflexivity]. exfalso.
destruct (NEWF eq_refl) as (_ & NB & _). pose proof (busy_of_X_self L st X p c k n b1 ctx l1 l2 XB WF) as E'. rewrite <- E1', <- E2', NB in E'. discriminate. }
rewrite NOK, !Z.eqb_refl. cbn [andb].
unfold slot_shadow_bytes, bquar. cbn [xb_n xb_st]. rewrite <- EAB. fold S.
eapply cells_frame in SHA; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GR3; lia);
apply Kshad; [clear -SHLO; lia| clear -SHHI GR3 GFS SE G0 GE; lia| clear -GR3; lia| left; clear -SE; lia]].
eapply cells_frame in SHR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GFS GE GR3; unfold granules in *; lia);
apply Kshad; [clear -SHLO SE GR3 G0 EGQ; lia| clear -SHHI GR3 GFS SE G0 GE EGQ; lia| clear -GFS GE GR3; unfold granules in *; lia| right; clear -EGQ; lia]].
rewrite EGQ in SH'.
replace (shad UB) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n)))) in SH' by (clear -SE GR3; lia).
rewrite EGQ in SHR, G0.
replace (shad UB + shlen (rup n 8)) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n))) + Z.of_nat (Z.to_nat (shlen (rup n 8)))) in SHR by (clear -SE GR3 G0; lia).
pose proof (cb_app m' _ _ _ _ _ SHA (cb_app m' _ _ _ _ _ SH' SHR)) as FIN.
assert (GE' : shlen (rup n 8) = granules n) by (rewrite <- EGQ; exact GE). rewrite <- GE'.
replace (Z.to_nat (shlen (rz_size n)) + (Z.to_nat (shlen (rup n 8)) + Z.to_nat (shlen S - shlen (rz_size n) - shlen (rup n 8))))%nat with (Z.to_nat (shlen S)) in FIN
by (clear -GR3 G0 GE' GFS; unfold granules in *; lia).
rewrite <- ?app_assoc in FIN. rewrite <- ?app_assoc. exact FIN.
* left.
assert (T2 : (c =? c'') && (k =? k'') = false).
{ destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
split.
-- subst X'. rewrite (busy_of_xfree L st X p c k n b1 ctx l1 l2 (enq_is_app st) k24 c'' k'' XB WF), T2.
destruct (negb (enq_is_app st) && (K_BATCH_CLASS =? c'') && (k24 =? k'')) eqn:T1; [| reflexivity].
destruct (enq_is_app st) eqn:EA; [cbn in T1; discriminate|]. cbn [negb andb] in T1.
destruct (Z.eqb_spec K_BATCH_CLASS c'') as [<-|]; [| discriminate]. destruct (Z.eqb_spec k24 k'') as [<-|]; [| discriminate].
destruct (NEWF eq_refl) as (_ & NB & _). rewrite NB. rewrite size_of_class_24. rewrite slot_shadow_bbatch by (clear; change (shlen 8192) with 1024; lia).
reflexivity.
-- assert (DW : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
{ pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
rewrite <- EAB, <- ES in D. exact D. }
pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
apply Kshad.
++ rewrite shad_div. unfold ASHOFF. clear -P7 RES RHI. Z.div_mod_to_equations. lia.
++ rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. Z.div_mod_to_equations. lia.
++ apply shlen_nonneg. clear -T16; lia.
++ rewrite EGQ. destruct DW as [D|D].
** left. eapply Z.le_trans; [apply shad_sep; [exact D| clear -AL''; Z.div_mod_to_equations; lia]|]. clear -SE GR3; lia.
** right. apply shad_sep; [clear -D UBS; lia| exact UB16'].
+ intros POS''.
set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
destruct U0 as [U0 U0'].
assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_allocated_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
assert (AM : AU mod 8 = 0) by (subst AU; pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM''; Z.div_mod_to_equations; lia).
apply Kshad.
* rewrite shad_div. unfold ASHOFF. clear -U0 RI4 RES RHI. Z.div_mod_to_equations. lia.
* rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
* clear -POS''; lia.
* rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
}
assert (AVL' : forall c'', 1 <= c'' < K_NUM_CLASSES -> ashadow_avail L st' m' c'').
{ intros c'' Hc''. pose proof WF as WF0. destruct WF0 as (_ & _ & SAL & _ & _ & PERC & _).
destruct (PERC c'' Hc'') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _).
pose proof (size_of_class_facts c'' Hc'') as [QS QS16]. pose proof (aregion_mod L c'' SAL) as RM''.
assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
unfold K_NUM_CLASSES in Hc''.
assert (RI : al_res L + 4096 <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
{ unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
destruct RI as (RI1 & RI2 & RI3).
assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
eapply ashadow_avail_frame; [exact MUn | exact WM | exact (AVL c'' ltac:(unfold K_NUM_CLASSES; exact Hc'')) | exact EC4 | exact EC2 | |].
- intros POS''. set (AU := aregion L c'' + c_mapped_user (get_cls st c'')) in *.
assert (U0 : aregion L c'' <= AU /\ AU + (K_FREEARR_OFF - c_mapped_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
destruct U0 as [U0 U0'].
assert (U1 : c'' = c -> aregion L c + c_mapped_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_mapped_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS G3; lia) G4 U1 U0 U0') as D.
assert (AM : AU mod 8 = 0) by (subst AU; generalize Q4 RM''; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia).
apply Kshad.
+ rewrite shad_div. unfold ASHOFF. clear -U0 RI1 RES RHI. Z.div_mod_to_equations. lia.
+ rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
+ clear -POS''; lia.
+ rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
- intros POS''. set (AU := afreearr L c'' + c_mapped_free_array (get_cls st c'')) in *.
assert (FA : aregion L c'' + K_FREEARR_OFF <= AU /\ AU + (K_FREEARR_MAX - c_mapped_free_array (get_cls st c'')) <= aregion L c'' + K_REGION).
{ subst AU. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6. lia. }
destruct FA as [FA1 FA2].
pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
assert (AM : AU mod 8 = 0) by (subst AU; generalize Q7 RM''; clear; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAP; intros; Z.div_mod_to_equations; lia).
apply Kshad.
+ rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -FA1 RI1 RES RHI. Z.div_mod_to_equations. lia.
+ rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -FA2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
+ clear -POS''; lia.
+ rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']]. }
assert (HS' : ASEC L st' X' m').
{ eapply (hs_frame _ HL L st st' X X' m m'); [exact HS | exact MUn | exact WM | |].
- unfold sec_untouched, aknown. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
assert (SHB1 : shad (al_space_beg L) + 536870912 <= shad (aregion L c)).
{ rewrite !shad_div. unfold aregion, K_REGION, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *. clear -HC. Z.div_mod_to_equations. lia. }
assert (SHB2 : shad (aregion L c) + shlen (c_mapped_user (get_cls st c)) <= shad (al_space_beg L) + 17179869184).
{ pose proof (alayout_space L ALO) as (_ & _ & SPal & _). rewrite !shad_div, shlen_div. unfold aregion, K_REGION, K_ALIGN, K_FREEARR_OFF, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *.
clear -HC G4 SPal. Z.div_mod_to_equations. lia. }
apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
do 4 (apply Forall_cons; [cbn [fst snd]; intros a Ha; left; left; clear -Ha; unfold AIMG_HI, AINSTANCE; lia |]).
do 4 (apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha OT TBND TIMG; lia |]).
apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha G5 G6 ABUB S8 EUB RSP; lia |].
apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha SE GR3 GFS GE EGQ G0 SHM1 SHM2 SHB1 SHB2; lia |].
apply Forall_cons; [cbn [fst snd]; intros a Ha; do 8 right; left; clear -Ha; lia |].
apply Forall_cons; [cbn [fst snd]; intros a Ha; do 9 right; left; clear -Ha; lia |].
apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha RES RHI RSP LSTF; destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [rewrite Z0, qsz_0 in Ha; left; left; unfold AIMG_HI, AINSTANCE; lia| pose proof (qsz_bound lst); do 7 right; left; lia] |].
apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha RES RHI RSP EBF EBNZ; destruct EBF as [Z1|(_ & _ & E3 & E4)]; [exfalso; lia| do 7 right; left; lia] |].
apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha RES RHI RSP LSTF GLF; destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & _ & _ & H3 & H4)])];
[ subst gl; destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [left; left; unfold AIMG_HI, AINSTANCE; lia| do 7 right; left; lia] | left; left; unfold AIMG_HI, AINSTANCE; lia | do 7 right; left; lia] |].
apply Forall_nil.
- eapply (sec_same_free st p c n); [exact LIVE| exact SC| exact (st_after_enq_qfilt is_sec st1 (CPrim c n) eq_refl)]. }
assert (BL' : ablocks L st' X' (lb_remove p LB)).
{ subst X'. unfold xfree. destruct (enq_is_app st); [apply (ablocks_xquar L st X p c k n b1 ctx l1 l2 XB LB st' ELIVE BL)| apply (ablocks_xbatch L st X p c k n b1 ctx l1 l2 XB LB st' k24 ELIVE BL)]. }
assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
pose proof (ao_fake L ALO) as FKO. pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as (FKi & FKa & [kF FBND]). unfold aobj in FKO.
pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
assert (HFK' : AFK L (lb_remove p LB) m').
{ eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |] |].
- pose proof (ao_dtls L ALO) as DTO. pose proof (aobj4_int _ DTO) as (_ & _ & [kD DBND] & [jD DIMG]). unfold aobj in DTO.
pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
unfold adisj in D1, D2, D3, D4.
unfold fake_untouched. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ shad UB + gq <= shad (al_fake L))
/\ 2148232704 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).
{ split; [| rewrite shad_div, shlen_div; unfold ASHOFF; pose proof atop_range as AR8; clear -FKO FKi FBND AR8; Z.div_mod_to_equations; lia].
pose proof D_f_res as DFR. unbox DFR. rewrite EGQ. destruct DFR as [D|D].
- left. apply shad_sep; [| clear -FKO FKi FBND; Z.div_mod_to_equations; lia]. clear -D RSP G5 ABUB. lia.
- right. apply shad_sep; [| exact UB16']. clear -D RSP G6 UBS. lia. }
destruct SHF as (SHF1 & SHF2 & SHF3).
assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
assert (LSTR : (lst = 0 /\ qsz lst = 8) \/ (al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104 /\ qsz lst = 8192))
by (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [left; split; [exact Z0| apply qsz_eq0; exact Z0]| right; split; [exact F3| split; [exact F4| apply qsz_pos; clear -F3 RES; lia]]]).
assert (EBR : al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104) by (destruct EBF as [Z0|(_ & _ & F3 & F4)]; [exfalso; clear -Z0 EBNZ; lia| split; assumption]).
assert (GLRR : gl = lst \/ gl = 0 \/ (al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104))
by (destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & _ & _ & H3 & H4)])]; [left; exact Z2| right; left; exact Z2| right; right; split; assumption]).
do 16 (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [lia|]); lia]
| solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3; repeat (split; [lia|]); lia]
| solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3; repeat (split; [lia|]); lia]
| solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [lia|]); lia]
| solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [lia|]); lia]
| solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR; repeat (split; [lia|]); lia]
| solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR; repeat (split; [lia|]); lia]
| solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR; repeat (split; [lia|]); lia]
| match goal with |- ?G => idtac "FAKELEFT" G end ] |]).
apply Forall_nil.
- intros cls FA sz. rewrite (In_lb_remove p LB). cbn. split; [intros [Hin _]; exact Hin| intros Hin; split; [exact Hin| discriminate]]. }
assert (GNB : g_nb g = Z.of_nat (length (a_qglob st))) by reflexivity.
assert (GFST : g_fst g = qfirst L (q_glob Q)) by reflexivity.
assert (GQB : g_qb g = a_qglob_bytes st) by reflexivity.
assert (GFU : g_full g = match a_qglob st with [] => false | _ :: _ => true end) by reflexivity.
destruct DKP as [MX' DKP'].
pose proof (qnum_free st p (CPrim c n) NUM ltac:(cbn [chunk_size]; clear -N1; lia) NOREC) as (NUM' & NB2a & NB2b & NB2c & NF2).
fold st1 st2 st' in NUM', NB2a, NB2b, NB2c, NF2.
pose proof (st_after_q st2) as [DRN NDR]. fold st' in DRN, NDR.
assert (QK' : aquar_glob_const m').
{ split; [| exact MX']. eapply cells_frame; [exact QK | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kimg; clear; unfold AQ_MAX, AIMG_HI; lia. }
assert (IA' : aintal true m').
{ split; [exact FL'|]. split; [exact IAS'|]. intros _ j Hj. apply IAM'. revert Hj. clear. unfold AIA_MAP1_LEN. cbn. lia. }
assert (BLST : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst ->
abatch_addr L (qb_slot q) + 8192 <= lst \/ lst + 8192 <= abatch_addr L (qb_slot q) \/ lst = 0).
{ intros q Hq NE. destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [right; right; exact Z0|].
destruct (BDIS q ql Hq ltac:(apply in_or_app; left; exact Hql)) as [E|E]; [exfalso; apply NE; rewrite Eql; exact E| rewrite Eql].
destruct E as [E|E]; [left; exact E| right; left; exact E]. }
assert (BFR : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst -> abatch_addr L (qb_slot q) <> gl ->
disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (abatch_addr L (qb_slot q)) 8192).
{ intros q Hq NL NG. destruct (BGEO q Hq) as (_ & _ & F3 & F4). pose proof (SEPQ q Hq) as SQ. pose proof (BLST q Hq NL) as DL.
assert (DE : eb = lst \/ abatch_addr L (qb_slot q) + 8192 <= eb \/ eb + 8192 <= abatch_addr L (qb_slot q)).
{ destruct EBK as [E|[EA E]]; [left; exact E| right]. rewrite E.
destruct (KDIS q Hq EA) as [D|D]; [right; exact D| left; exact D]. }
assert (DG : gl = lst \/ gl = 0 \/ abatch_addr L (qb_slot q) + 8192 <= gl \/ gl + 8192 <= abatch_addr L (qb_slot q)).
{ destruct GLF as [[_ E]|(_ & _ & [Z0|((qg & Hqg & Eqg) & _)])]; [left; exact E| right; left; exact Z0| right; right].
destruct (BDIS q qg Hq ltac:(apply in_or_app; right; exact Hqg)) as [E|E]; [exfalso; apply NG; rewrite Eqg; exact E| rewrite Eqg; exact E]. }
apply Kres; clear -F3 F4 RES RHI SQ DL DE DG ABUB S8 EUB; lia. }
assert (HQ' : AQUAR L st' X' m').
{ subst ek. unfold ek_of in EKP, EK, QC', DKP', EEB, SB1, GDR, GL, GLST.
destruct (enq_is_app st) eqn:EA; cbn [ek_nb ek_fst ek_lst ek_delta ek_b ek_post ek_pre] in EKP, EK, QC', DKP', EEB, SB1, GDR, GL, GLST.
-
destruct EKP as (LB' & LA' & [bs LJ'] & _). destruct EK as (_ & _ & CNT' & _ & _ & _ & _ & LEN & _).
pose proof EA as EA0. unfold enq_is_app in EA0. destruct (rev (a_qloc st)) as [|blr rl] eqn:RV; [discriminate|].
assert (QL : a_qloc st = rev rl ++ [blr]) by (rewrite <- (rev_involutive (a_qloc st)), RV; reflexivity).
destruct (Z.eqb_spec (b_count blr) Q_BATCH) as [|NFULL]; [discriminate|]. clear EA0.
set (l := rev rl) in *. set (bl := blr) in *.
assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL, length_app; cbn; clear; lia).
assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]) by (apply app_removelast_last; destruct (q_loc Q); [cbn in LQ; clear -LQ; lia| discriminate]).
set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; clear -LN1; lia).
assert (LST : List.last (a_qloc st) dummy_batch = bl) by (rewrite QL; apply last_app1). rewrite LST in *.
assert (QLST : lst = abatch_addr L (qb_slot qz)) by (rewrite ELST, QQ; apply qlast_app1).
set (bl' := mkABatch (b_count bl + 1) (b_size bl + n) (CPrim c n :: b_chunks bl)) in *.
set (qz' := mkQB (qb_slot qz) (k :: qb_ks qz)) in *.
assert (EAPP : enq_app st1 (CPrim c n) = Some (set_qloc (l ++ [bl']) (a_qloc_bytes st1 + n) st1)).
{ unfold enq_app. change (a_qloc st1) with (a_qloc st). rewrite RV. fold bl. replace (b_count bl =? Q_BATCH) with false by (symmetry; apply Z.eqb_neq; exact NFULL).
cbn [chunk_size]. subst bl'. reflexivity. }
assert (Q2 : a_qloc st2 = l ++ [bl'] /\ a_qloc_bytes st2 = a_qloc_bytes st + n /\ a_qglob st2 = a_qglob st /\ a_qglob_bytes st2 = a_qglob_bytes st).
{ subst st2. unfold st_enq. rewrite EAPP. subst st1. cbn. repeat split; reflexivity. }
destruct Q2 as (QL2 & QB2 & QG2 & QGB2).
unfold abatches in ABL, ABG. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
assert (ABl' : abatches_to L m' l ql (hd 0 (qaddrs L [qz']))).
{ cbn [qaddrs map hd qz' qb_slot]. cbn [qaddrs map hd] in ABl. eapply abatches_to_frame; [exact MUn | exact WM | exact ABl |].
intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; left; exact Hq).
assert (NEq : abatch_addr L (qb_slot q) <> lst).
{ rewrite QLST. intros E. apply in_split in Hq. destruct Hq as (qs1 & qs2 & EQl).
apply (bslots_nodup_split L st X Q CP qs1 q qs2 qz (q_glob Q)); [rewrite QQ, EQl; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
apply BFR; [exact INq | exact NEq |].
destruct GLF as [[_ E]|(GD & GQL & [Z0|((qg & Hqg & Eqg) & _)])]; [rewrite E; exact NEq| rewrite Z0; destruct (BGEO q INq) as (_ & _ & F3 & _); clear -F3 RES RHI; lia|].
rewrite Eqg. intros E. apply in_split in Hq. destruct Hq as (qs1 & qs2 & EQl). apply in_split in Hqg. destruct Hqg as (gs1 & gs2 & EQg).
apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ [qz] ++ gs1) qg gs2); [rewrite QQ, EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qg ltac:(apply in_or_app; right; rewrite EQg; apply in_or_app; right; left; reflexivity)).
unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
assert (ABz' : abatch_cells L m' bl' qz' 0).
{ unfold abatch_cells. cbv zeta. cbn [qb_slot qb_ks b_size b_count b_chunks bl' qz']. rewrite <- QLST. rewrite qhdrs_cons, map_app. cbn [map qhdr]. rewrite <- EAB, <- EUB.
split; [exact LB'|]. split; [exact LA'|]. split; [| split; [cbn [length]; rewrite Z4; clear; lia| split; [cbn [length]; rewrite Z5; reflexivity| unfold Q_BATCH in *; clear -CNT' Z6; lia]]].
exists bs. unfold Q_BATCH_BYTES. exact LJ'. }
assert (ABL' : abatches_to L m' (l ++ [bl']) (ql ++ [qz']) 0).
{ apply abatches_to_app; [exact LNl|]. split; [exact ABl'|]. cbn. split; [exact ABz'| exact I]. }
assert (CP2 : qcoupled L st2 X' (mkQConc (ql ++ [qz']) (q_glob Q) true (q_pend Q))).
{ subst X'. unfold xfree. apply (qcoupled_app L st X Q p c k n b1 ctx l1 l2 XB WF CP st2 l bl ql qz true QL QQ QL2 QG2). }
subst qz'.
destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [DR|NDRN].
+
destruct (DRN DR) as (QL3 & QB3 & QG3 & QGB3).
assert (GD : g_drain g = true) by (rewrite GDR; apply Z.ltb_lt; rewrite <- QB2; exact DR).
unfold tcache_post in QC'. rewrite GD in DKP', QC'.
destruct DKP' as [GC' GLN].
exists (mkQConc [] (q_glob Q ++ (ql ++ [{| qb_slot := qb_slot qz; qb_ks := k :: qb_ks qz |}])) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
rewrite QL3, QB3, QG3, QGB3, QL2, QG2, QB2, QGB2.
split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
* split; [cbn [length qfirst qlast qaddrs map hd last Z.of_nat]; exact QC'| exact I].
* split.
-- rewrite length_app, Nat2Z.inj_add, <- GNB. rewrite length_app. cbn [length].
replace (Z.of_nat (length l + 1)) with (Z.of_nat (length (a_qloc st))) by (rewrite QL, length_app; cbn; reflexivity).
rewrite qlast_app by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite qlast_reslot, <- QQ, <- ELST.
assert (FE : qfirst L (q_glob Q ++ ql ++ [{| qb_slot := qb_slot qz; qb_ks := k :: qb_ks qz |}]) = (if g_full g then g_fst g else qfirst L (q_loc Q))).
{ rewrite GFU, GFST. destruct (a_qglob st) eqn:QG0.
- replace (q_glob Q) with (@nil qbatchc) by (destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). cbn [app]. rewrite qfirst_reslot, <- QQ. reflexivity.
- apply qfirst_app. destruct (q_glob Q); [cbn in LN2; discriminate| discriminate]. }
rewrite FE, <- GQB. exact GC'.
-- unfold abatches. apply abatches_to_app; [exact LN2|]. split.
++
rewrite hd_qaddrs by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite qfirst_reslot, <- QQ.
destruct (a_qglob st) as [|bg0 lg0] eqn:QG0.
** replace (q_glob Q) with (@nil qbatchc) by (destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). exact I.
** rewrite <- QG0 in *.
assert (GNE : a_qglob st <> []) by (rewrite QG0; discriminate).
assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
assert (LQg : (0 < length (q_glob Q))%nat) by (rewrite LN2, QG0; cbn; clear; lia).
assert (QQg : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]) by (apply app_removelast_last; destruct (q_glob Q); [cbn in LQg; clear -LQg; lia| discriminate]).
set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
assert (LNg : length qg = length lg) by (rewrite QQg, QG, !length_app in LN2; cbn in LN2; clear -LN2; lia).
rewrite QG, QQg in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [ABg ABgz].
cbn [abatches_to qaddrs map hd] in ABgz. destruct ABgz as [(Y1 & Y2 & Y3 & Y4 & Y5 & Y6) _].
assert (QGLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQg; apply qlast_app1).
rewrite GFU in GLN. rewrite ?QG0 in GLN. cbv iota beta in GLN. rewrite GL, QGLST in GLN.
rewrite QG, QQg. apply abatches_to_app; [exact LNg|]. split.
+++ cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABg |].
intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQg; apply in_or_app; left; exact Hq).
assert (NEg : abatch_addr L (qb_slot q) <> abatch_addr L (qb_slot qgz)).
{ intros E. apply in_split in Hq. destruct Hq as (gs1 & gs2 & EQg).
apply (bslots_nodup_split L st X Q CP (q_loc Q ++ gs1) q gs2 qgz []); [rewrite QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
apply BFR; [exact INq | | rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; exact NEg].
rewrite QLST. intros E. apply in_split in Hq. destruct Hq as (gs1 & gs2 & EQg).
apply (bslots_nodup_split L st X Q CP ql qz gs1 q (gs2 ++ [qgz])); [rewrite QQ, QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia.
+++ cbn [abatches_to]. split; [| exact I].
unfold abatch_cells. cbv zeta. change (hd (qfirst L (q_loc Q)) (qaddrs L [])) with (qfirst L (q_loc Q)).
assert (GLS : gl = abatch_addr L (qb_slot qgz)) by (rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; reflexivity).
assert (NGL : abatch_addr L (qb_slot qgz) <> lst).
{ rewrite QLST. intros E. apply (bslots_nodup_split L st X Q CP ql qz qg qgz []); [rewrite QQ, QQg; rewrite <- ?app_assoc; cbn [app]; reflexivity|].
pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
assert (INgz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity).
destruct (BGEO qgz INgz) as (_ & _ & F3 & F4). pose proof (SEPQ qgz INgz) as SQ. pose proof (BLST qgz INgz NGL) as DL.
assert (DE : eb = lst \/ abatch_addr L (qb_slot qgz) + 8192 <= eb \/ eb + 8192 <= abatch_addr L (qb_slot qgz)).
{ destruct EBK as [E|[EA' E]]; [left; exact E| discriminate]. }
assert (D8 : forall A8 kk, abatch_addr L (qb_slot qgz) + 8 <= A8 -> A8 + kk <= abatch_addr L (qb_slot qgz) + 8192 -> 0 <= kk ->
disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) A8 kk).
{ intros A8 kk HA HK KK0. apply Kres; clear -F3 F4 RES RHI SQ DL DE GLS ABUB S8 EUB HA HK KK0; lia. }
pose proof Y1 as Y1'. rw_split Y1' 1%nat YN YR.
eapply cells_frame in YR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; apply D8; clear; lia].
rw_join GLN YR YH.
split; [exact YH|]. split; [| split; [| split; [exact Y4| split; [exact Y5| exact Y6]]]].
--- eapply u64arr_frame; [exact Y2 | exact MUn | exact WM |]. rewrite length_map, qhdrs_length by exact Y5. rewrite <- Y4.
apply D8; unfold Q_BATCH in Y6; clear -Y6; lia.
--- eapply junk_frame; [exact Y3 | exact MUn | exact WM |]. intros Hp. apply D8; unfold Q_BATCH, Q_BATCH_BYTES in *; clear -Y6 Hp; lia.
++ exact ABL'.
* exact (qcoupled_drain L st2 st' X' (mkQConc (ql ++ [{| qb_slot := qb_slot qz; qb_ks := k :: qb_ks qz |}]) (q_glob Q) true (q_pend Q)) true CP2 QL3 QG3).
* exact NUM'.
+
pose proof (NDR NDRN) as EST.
assert (GD : g_drain g = false) by (rewrite GDR; apply Z.ltb_ge; rewrite <- QB2; exact NDRN).
unfold tcache_post in QC'. rewrite GD in DKP', QC'.
exists (mkQConc (ql ++ [{| qb_slot := qb_slot qz; qb_ks := k :: qb_ks qz |}]) (q_glob Q) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
rewrite EST, QL2, QG2, QB2, QGB2.
split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
* split; [| exact ABL'].
rewrite length_app, qfirst_reslot, qlast_reslot, <- QQ, <- ELST. cbn [length].
replace (Z.of_nat (length l + 1)) with (Z.of_nat (length (a_qloc st))) by (rewrite QL, length_app; cbn; reflexivity). exact QC'.
* split; [rewrite <- GNB, <- GFST, <- GL, <- GQB; exact DKP'|].
unfold abatches. eapply abatches_to_frame; [exact MUn | exact WM | exact ABG |].
intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
assert (NEq : abatch_addr L (qb_slot q) <> lst).
{ rewrite QLST. intros E. apply in_split in Hq. destruct Hq as (gs1 & gs2 & EQg).
apply (bslots_nodup_split L st X Q CP ql qz gs1 q gs2); [rewrite QQ, EQg; rewrite <- ?app_assoc; cbn [app]; reflexivity|].
pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
apply BFR; [exact INq | exact NEq | rewrite EGL; unfold dk_glst; rewrite GD; exact NEq].
* first [rewrite EST | idtac]. exact CP2.
* first [rewrite <- EST | idtac]. exact NUM'.
-
destruct (NEWF eq_refl) as (NK24 & NB24 & KK24 & NIB & JK & FK & CIN & POS).
destruct EKP as (C24' & [stj' SJ'] & NBc & NAc & [bs NJc] & OLDc).
assert (EAPP : enq_app st1 (CPrim c n) = None).
{ destruct (enq_app st1 (CPrim c n)) as [sx|] eqn:EAPP; [exfalso| reflexivity].
assert (EA1 : enq_is_app st1 = true) by (apply (proj2 (enq_is_app_spec st1 (CPrim c n))); eexists; exact EAPP).
change (enq_is_app st1) with (enq_is_app st) in EA1. congruence. }
set (nbt := mkABatch 1 (n + 8192) [CPrim c n]) in *.
set (qn := mkQB k24 [k]) in *.
assert (Q2 : a_qloc st2 = a_qloc st ++ [nbt] /\ a_qloc_bytes st2 = a_qloc_bytes st + (n + 8192) /\ a_qglob st2 = a_qglob st /\ a_qglob_bytes st2 = a_qglob_bytes st).
{ subst st2. unfold st_enq. rewrite EAPP. pose proof (enq_new_core (CPrim c n) st1) as (_ & E1 & E2 & _ & E3 & E4 & _).
rewrite E1, E2, E3, E4. subst st1 nbt. cbn [a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_live chunk_size]. unfold Q_BATCH_BYTES.
split; [reflexivity|]. split; [clear; lia|]. split; reflexivity. }
destruct Q2 as (QL2 & QB2 & QG2 & QGB2).
assert (FSTE : (if match a_qloc st with [] => false | _ :: _ => true end then qfirst L (q_loc Q) else abatch_addr L k24) = qfirst L (q_loc Q ++ [qn])).
{ rewrite qfirst_app_r. subst qn; cbn [qb_slot]. generalize LN1. clear. generalize (a_qloc st) (q_loc Q).
intros [|x1 r1] [|x2 r2] LL; cbn in LL; first [reflexivity | discriminate]. }
rewrite FSTE in QC'. rewrite FSTE in DKP'.
assert (QLST' : qlast L (q_loc Q ++ [qn]) = abatch_addr L k24) by (subst qn; apply qlast_app1).
assert (GNL : forall q, In q (q_glob Q) -> abatch_addr L (qb_slot q) <> lst).
{ intros q Hq E. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
destruct LSTF as [Z0|((q' & Hq' & Eq') & _)].
- destruct (BGEO q INq) as (_ & _ & F3 & _). clear -F3 RES RHI E Z0. lia.
- apply in_split in Hq. destruct Hq as (gs1 & gs2 & EQg). apply in_split in Hq'. destruct Hq' as (qs1 & qs2 & EQl).
apply (bslots_nodup_split L st X Q CP qs1 q' (qs2 ++ gs1) q gs2); [rewrite EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP q' ltac:(apply in_or_app; left; rewrite EQl; apply in_or_app; right; left; reflexivity)).
rewrite Eq' in E. unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
assert (ABO' : abatches_to L m' (a_qloc st) (q_loc Q) (abatch_addr L k24)).
{ destruct (a_qloc st) as [|b0 l0] eqn:QL0.
- replace (q_loc Q) with (@nil qbatchc) by (destruct (q_loc Q); [reflexivity| cbn in LN1; discriminate]). exact I.
- cbv iota beta in OLDc. destruct OLDc as [OLD1 OLD2]. rewrite <- QL0 in *.
assert (LNE : a_qloc st <> []) by (rewrite QL0; discriminate).
assert (QL : a_qloc st = removelast (a_qloc st) ++ [List.last (a_qloc st) dummy_batch]) by (apply app_removelast_last; exact LNE).
assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL0; cbn; clear; lia).
assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]) by (apply app_removelast_last; destruct (q_loc Q); [cbn in LQ; clear -LQ; lia| discriminate]).
set (l := removelast (a_qloc st)) in *. set (bl := List.last (a_qloc st) dummy_batch) in *.
set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; clear -LN1; lia).
assert (QLST : lst = abatch_addr L (qb_slot qz)) by (rewrite ELST, QQ; apply qlast_app1).
assert (FULL : b_count bl = Q_BATCH).
{ pose proof EA as EA0. unfold enq_is_app in EA0. rewrite QL, rev_unit in EA0. cbv iota beta in EA0.
revert EA0. destruct (Z.eqb_spec (b_count bl) Q_BATCH) as [E|NE]; intros EA0; [exact E| discriminate]. }
unfold abatches in ABL. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
rewrite QL, QQ. apply abatches_to_app; [exact LNl|]. split.
+ cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABl |].
intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; left; exact Hq).
assert (NEq : abatch_addr L (qb_slot q) <> lst).
{ rewrite QLST. intros E. apply in_split in Hq. destruct Hq as (qs1 & qs2 & EQl).
apply (bslots_nodup_split L st X Q CP qs1 q qs2 qz (q_glob Q)); [rewrite QQ, EQl; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
apply BFR; [exact INq | exact NEq |].
destruct GLF as [[_ E]|(GD & GQL & [Z0|((qg & Hqg & Eqg) & _)])]; [rewrite E; exact NEq| rewrite Z0; destruct (BGEO q INq) as (_ & _ & F3 & _); clear -F3 RES RHI; lia|].
rewrite Eqg. intros E. apply in_split in Hq. destruct Hq as (qs1 & qs2 & EQl). apply in_split in Hqg. destruct Hqg as (gs1 & gs2 & EQg).
apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ [qz] ++ gs1) qg gs2); [rewrite QQ, EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qg ltac:(apply in_or_app; right; rewrite EQg; apply in_or_app; right; left; reflexivity)).
unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia.
+ cbn [abatches_to]. split; [| exact I].
unfold abatch_cells. cbv zeta. change (hd (abatch_addr L k24) (qaddrs L [])) with (abatch_addr L k24). rewrite <- QLST.
split; [rewrite FULL; exact OLD1|]. split; [exact OLD2|]. split; [| split; [exact Z4| split; [exact Z5| exact Z6]]].
rewrite FULL. replace (Q_BATCH_BYTES - 24 - 8 * Q_BATCH) with 0 by reflexivity. unfold Q_BATCH. apply junk_nil; (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [clear -Z0; lia | atop_facts; clear -F3 F4 RES RHI; lia]). }
assert (ABN' : abatch_cells L m' nbt qn 0).
{ unfold abatch_cells. cbv zeta. subst nbt qn. cbn [qb_slot qb_ks b_size b_count b_chunks]. rewrite qhdrs_cons. cbn [qhdrs app map qhdr]. rewrite <- EAB, <- EUB.
split; [exact NBc|]. split; [exact NAc|]. split; [exists bs; unfold Q_BATCH_BYTES; exact NJc|]. split; [reflexivity|]. split; [reflexivity| unfold Q_BATCH; clear; lia]. }
assert (ABL' : abatches_to L m' (a_qloc st ++ [nbt]) (q_loc Q ++ [qn]) 0).
{ apply abatches_to_app; [exact LN1|]. split; [cbn [qaddrs map hd]; subst qn; cbn [qb_slot]; exact ABO'|]. cbn [abatches_to]. split; [exact ABN'| exact I]. }
assert (CP2 : qcoupled L st2 X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q))).
{ subst X' qn nbt. rewrite ?EA. unfold xfree. cbv iota beta.
apply (qcoupled_new L st X Q p c k n b1 ctx l1 l2 XB WF CP st2 k24 (c_count (get_cls st K_BATCH_CLASS)) (n + 8192) true eq_refl POS NK24 QL2 QG2). }
destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [DR|NDRN].
+
destruct (DRN DR) as (QL3 & QB3 & QG3 & QGB3).
assert (GD : g_drain g = true) by (rewrite GDR; apply Z.ltb_lt; rewrite <- QB2; exact DR).
unfold tcache_post in QC'. rewrite GD in DKP', QC'.
destruct DKP' as [GC' GLN].
exists (mkQConc [] (q_glob Q ++ (q_loc Q ++ [qn])) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
rewrite QL3, QB3, QG3, QGB3, QL2, QG2, QB2, QGB2.
split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
* split; [cbn [length qfirst qlast qaddrs map hd last Z.of_nat]; exact QC'| exact I].
* split.
-- rewrite length_app, Nat2Z.inj_add, <- GNB. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
rewrite qlast_app by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite QLST'.
assert (FE : qfirst L (q_glob Q ++ q_loc Q ++ [qn]) = (if g_full g then g_fst g else qfirst L (q_loc Q ++ [qn]))).
{ rewrite GFU, GFST. destruct (a_qglob st) eqn:QG0.
- replace (q_glob Q) with (@nil qbatchc) by (destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). reflexivity.
- apply qfirst_app. destruct (q_glob Q); [cbn in LN2; discriminate| discriminate]. }
rewrite FE, <- GQB. exact GC'.
-- unfold abatches. apply abatches_to_app; [exact LN2|]. split.
++
rewrite hd_qaddrs by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate).
destruct (a_qglob st) as [|bg0 lg0] eqn:QG0.
** replace (q_glob Q) with (@nil qbatchc) by (destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). exact I.
** rewrite <- QG0 in *.
assert (GNE : a_qglob st <> []) by (rewrite QG0; discriminate).
assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
assert (LQg : (0 < length (q_glob Q))%nat) by (rewrite LN2, QG0; cbn; clear; lia).
assert (QQg : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]) by (apply app_removelast_last; destruct (q_glob Q); [cbn in LQg; clear -LQg; lia| discriminate]).
set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
assert (LNg : length qg = length lg) by (rewrite QQg, QG, !length_app in LN2; cbn in LN2; clear -LN2; lia).
rewrite QG, QQg in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [ABg ABgz].
cbn [abatches_to qaddrs map hd] in ABgz. destruct ABgz as [(Y1 & Y2 & Y3 & Y4 & Y5 & Y6) _].
assert (QGLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQg; apply qlast_app1).
rewrite GFU in GLN. rewrite ?QG0 in GLN. cbv iota beta in GLN. rewrite GL, QGLST in GLN.
rewrite QG, QQg. apply abatches_to_app; [exact LNg|]. split.
+++ cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABg |].
intros q Hq. assert (INg : In q (q_glob Q)) by (rewrite QQg; apply in_or_app; left; exact Hq).
assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact INg).
assert (NEg : abatch_addr L (qb_slot q) <> abatch_addr L (qb_slot qgz)).
{ intros E. apply in_split in Hq. destruct Hq as (gs1 & gs2 & EQg).
apply (bslots_nodup_split L st X Q CP (q_loc Q ++ gs1) q gs2 qgz []); [rewrite QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
apply BFR; [exact INq | exact (GNL q INg) | rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; exact NEg].
+++ cbn [abatches_to]. split; [| exact I].
unfold abatch_cells. cbv zeta. change (hd (qfirst L (q_loc Q ++ [qn])) (qaddrs L [])) with (qfirst L (q_loc Q ++ [qn])).
assert (GLS : gl = abatch_addr L (qb_slot qgz)) by (rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; reflexivity).
assert (INgzg : In qgz (q_glob Q)) by (rewrite QQg; apply in_or_app; right; left; reflexivity).
assert (INgz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact INgzg).
pose proof (GNL qgz INgzg) as NGL.
destruct (BGEO qgz INgz) as (_ & _ & F3 & F4). pose proof (SEPQ qgz INgz) as SQ. pose proof (BLST qgz INgz NGL) as DL.
pose proof (KDIS qgz INgz eq_refl) as DE.
assert (D8 : forall A8 kk, abatch_addr L (qb_slot qgz) + 8 <= A8 -> A8 + kk <= abatch_addr L (qb_slot qgz) + 8192 -> 0 <= kk ->
disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) A8 kk).
{ intros A8 kk HA HK KK0. apply Kres; clear -F3 F4 RES RHI SQ DL DE EEB GLS ABUB S8 EUB HA HK KK0; lia. }
pose proof Y1 as Y1'. rw_split Y1' 1%nat YN YR.
eapply cells_frame in YR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; apply D8; clear; lia].
rw_join GLN YR YH.
split; [exact YH|]. split; [| split; [| split; [exact Y4| split; [exact Y5| exact Y6]]]].
--- eapply u64arr_frame; [exact Y2 | exact MUn | exact WM |]. rewrite length_map, qhdrs_length by exact Y5. rewrite <- Y4.
apply D8; unfold Q_BATCH in Y6; clear -Y6; lia.
--- eapply junk_frame; [exact Y3 | exact MUn | exact WM |]. intros Hp. apply D8; unfold Q_BATCH, Q_BATCH_BYTES in *; clear -Y6 Hp; lia.
++ exact ABL'.
* exact (qcoupled_drain L st2 st' X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q)) true CP2 QL3 QG3).
* exact NUM'.
+
pose proof (NDR NDRN) as EST.
assert (GD : g_drain g = false) by (rewrite GDR; apply Z.ltb_ge; rewrite <- QB2; exact NDRN).
unfold tcache_post in QC'. rewrite GD in DKP', QC'.
exists (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
rewrite EST, QL2, QG2, QB2, QGB2.
split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
* split; [| exact ABL'].
rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1. rewrite QLST'. exact QC'.
* split; [rewrite <- GNB, <- GFST, <- GL, <- GQB; exact DKP'|].
unfold abatches. eapply abatches_to_frame; [exact MUn | exact WM | exact ABG |].
intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
apply BFR; [exact INq | exact (GNL q Hq) | rewrite EGL; unfold dk_glst; rewrite GD; exact (GNL q Hq)].
* first [rewrite EST | idtac]. exact CP2.
* first [rewrite <- EST | idtac]. exact NUM'. }
idtac "CHECKPOINT-E".
assert (HBK : forall blk, In blk (lb_remove p LB) -> disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (ab_addr blk) (ab_size blk)).
{ intros [[q|cls] A' n'] Hin; cbn [ab_addr ab_size]; apply (proj1 (In_lb_remove p LB _)) in Hin; destruct Hin as [Hin NEp]; cbn [ab_kind] in NEp.
- destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & msz & Lp & EUA & Gs)].
+ assert (NEq : xb_st b <> BLive p) by (rewrite Sb; intros E; apply NEp; congruence).
pose proof (other_key (AHQ DI ASEC AFK) L st X m (BLive p) c k n b1 ctx l1 l2 AR XB b Hb NEq) as NE1.
destruct (busy_slot_range L st X b WF Hb) as [HCb HKb].
pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
pose proof (busy_of_In_nodup L st X b WF Hb) as BOF.
unfold xb_user, xb_alloc in Ub. subst A' n'.
set (cb := xb_class b) in *. set (kb := xb_slot b) in *.
pose proof (slot_geo L st X cb kb ALO WF HCb HKb) as (T16 & TM16 & TAL & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _).
pose proof (slots_sep_any L st X cb kb c k ALO WF HCb HC HKb KR ltac:(clear -NE1; lia)) as D9. rewrite <- EAB, <- ES in D9.
assert (DQ : forall q', In q' (q_loc Q ++ q_glob Q) ->
aslot_addr L cb kb + size_of_class cb <= abatch_addr L (qb_slot q') \/ abatch_addr L (qb_slot q') + 8192 <= aslot_addr L cb kb).
{ intros q' Hq'. destruct (bslot_busy L st X Q CP q' Hq') as (yq & Hyq & Syq & Cyq & Kyq).
assert (NE : cb <> K_BATCH_CLASS \/ kb <> qb_slot q').
{ destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2.
pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq, <- E1, <- E2, BOF in BY. injection BY as EE. subst yq. rewrite Sb in Syq. discriminate. }
pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS (qb_slot q') ALO WF HCb (K24) HKb (bslot_range L st X Q WF CP q' Hq') NE) as D.
rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
assert (DK24 : enq_is_app st = false -> aslot_addr L cb kb + size_of_class cb <= abatch_addr L k24 \/ abatch_addr L k24 + 8192 <= aslot_addr L cb kb).
{ intros EA. destruct (NEWF EA) as (_ & NB & KK & _).
assert (NE : cb <> K_BATCH_CLASS \/ kb <> k24).
{ destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2. rewrite <- E1, <- E2, BOF in NB. discriminate. }
pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS k24 ALO WF HCb (K24) HKb KK NE) as D.
rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
assert (DL : lst = 0 \/ aslot_addr L cb kb + size_of_class cb <= lst \/ lst + 8192 <= aslot_addr L cb kb).
{ destruct LSTF as [Z0|((q' & Hq' & Eq') & _)]; [left; exact Z0| right]. rewrite Eq'. apply DQ. apply in_or_app; left; exact Hq'. }
assert (DE : eb = lst \/ aslot_addr L cb kb + size_of_class cb <= eb \/ eb + 8192 <= aslot_addr L cb kb).
{ destruct EBK as [E|[EA E]]; [left; exact E| right]. rewrite E. exact (DK24 EA). }
assert (DG : gl = lst \/ gl = 0 \/ aslot_addr L cb kb + size_of_class cb <= gl \/ gl + 8192 <= aslot_addr L cb kb).
{ destruct GLF as [[_ E]|(_ & _ & [Z0|((q' & Hq' & Eq') & _)])]; [left; exact E| right; left; exact Z0| right; right].
rewrite Eq'. apply DQ. apply in_or_app; right; exact Hq'. }
apply Kres; [clear -P5 RSP FIT; lia | clear -P6 RSP FIT; unfold K_SPACE_SIZE in *; lia | clear -FIT; lia
| clear -D9 FIT ABUB S8 EUB; lia | clear -DL FIT P5 RSP RES RHI; lia | clear -DE DL FIT P5 RSP RES RHI; lia | clear -DG DL FIT P5 RSP RES RHI; lia].
+
cbn [sec_wf1] in Gs. destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM in *.
unfold ablk, KLS, AIMG_HI in Gs2.
apply Kobj; clear -Gs2 Gs3 Gs4 Gs5 SF Ct Cr Cn Cs; lia.
- destruct (FKD cls A' n' Hin) as (K1 & K2 & K3). atop_facts.
pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
| clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia]. }
assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) (lb_remove p LB) -> forall a', FA <= a' < FA + sz ->
disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
{ intros cls FA sz Hin a' Ha'. apply (proj1 (In_lb_remove p LB _)) in Hin. destruct Hin as [Hin _].
destruct (FKD cls FA sz Hin) as (K1 & K2 & K3). atop_facts.
apply Kshad; [rewrite shad_div; unfold ASHOFF; clear -K1 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia
| rewrite shad_div; unfold ASHOFF; clear -K3 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia | clear; lia |].
pose proof D_f_res as DFR; unbox DFR. destruct DFR as [D|D].
- left. rewrite (shad_div a'), (shad_div UB). clear -D Ha' K3 RSP G5 ABUB UB16'. Z.div_mod_to_equations. lia.
- right. rewrite EGQ, shlen_div, (shad_div a'), (shad_div UB). unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
clear -D Ha' K1 RSP G6 UBS RUP8 UB16'. Z.div_mod_to_equations. lia. }
assert (PSP : shad UB + gq <= shad ATOP).
{ rewrite EGQ, shlen_div, (shad_div UB), (shad_div ATOP). atop_facts. clear -UBS G8 ABCE CEIL LO RUP8 UB16'. Z.div_mod_to_equations. lia. }
split; [apply fp_le_refl|].
exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split.
{ eapply (aheap_pres_free CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact PSP]. }
split; [exact ALO|].
split. { apply (arng_core L RNG st1 st' SC).
- eapply Permutation_trans; [apply (sec_chunks_free st p c n st' LIVE ELIVE (st_after_enq_qfilt is_sec st1 (CPrim c n) eq_refl))|].
apply Permutation_sym. apply (sec_chunks_free st p c n st1 LIVE eq_refl (Permutation_refl _)).
- apply (arng_st L RNG st st1); [intros; reflexivity| reflexivity| apply (sec_chunks_free st p c n st1 LIVE eq_refl (Permutation_refl _))| exact ARNG]. }
split; [| exact HFK'].
exists X'. split; [| exact BL'].
split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3'].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition afree_fastP := afree_fast DI ASEC AFK CI store_free.
End S.
End CANSEC1.
