(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApInv ApErr ApParse ApPrim ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts HxpInit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition es_ids (st : ap_st bptr) : list bptr := map fst (st_blocks st).

(* [comment removed for export] *)
Definition mark_ok (sg : cnf_stage) (k : Z) : Prop := match sg with CnfInit => k = 0 | CnfMid => k = 0 \/ k = 1 end.
Definition marks_ok (sg : cnf_stage) (st : ap_st bptr) : Prop := Forall (mark_ok sg) (as_marks st).

(* [comment removed for export] *)
Definition ids_ok0 (E : ap_env) (st : ap_st bptr) : Prop :=
  List.NoDup (es_ids st ++ env_ids E) /\ (as_top st < ERR_NUM)%nat /\ (as_bottom st < ERR_NUM)%nat.
Definition ids_ok (E : ap_env) (st : ap_st bptr) : Prop :=
  List.NoDup (es_ids st ++ env_ids E) /\ (as_top st < ERR_NUM)%nat /\ (as_bottom st < ERR_NUM)%nat /\ marks_ok (e_stage E) st.

Lemma ids_ok_split : forall E st, ids_ok E st <-> ids_ok0 E st /\ marks_ok (e_stage E) st.
Proof. intros. unfold ids_ok, ids_ok0. tauto. Qed.
Lemma ids_ok_ids0 : forall E st, ids_ok E st -> ids_ok0 E st.
Proof. intros E st H. exact (proj1 (proj1 (ids_ok_split E st) H)). Qed.
Lemma ids_ok_marks : forall E st, ids_ok E st -> marks_ok (e_stage E) st.
Proof. intros E st H. exact (proj2 (proj1 (ids_ok_split E st) H)). Qed.
Lemma ids_ok_join : forall E st, ids_ok0 E st -> marks_ok (e_stage E) st -> ids_ok E st.
Proof. intros E st H M. exact (proj2 (ids_ok_split E st) (conj H M)). Qed.

Lemma mark_ok_cases : forall sg k, mark_ok sg k -> k = 0 \/ k = 1.
Proof. intros [|] k H; cbn in H; [left; exact H|exact H]. Qed.
Lemma mark_ok_0 : forall sg, mark_ok sg 0.
Proof. intros [|]; cbn; [reflexivity|left; reflexivity]. Qed.
Lemma mark_ok_init_any : forall sg k, mark_ok CnfInit k -> mark_ok sg k.
Proof. intros sg k H. cbn in H. subst k. apply mark_ok_0. Qed.
Lemma marks_ok_init_any : forall sg st, marks_ok CnfInit st -> marks_ok sg st.
Proof. intros sg st H. unfold marks_ok in *. eapply Forall_impl; [|exact H]. intros k Hk. apply mark_ok_init_any. exact Hk. Qed.
(* [comment removed for export] *)
Lemma marks_ok_get : forall sg st i, marks_ok sg st -> mark_ok sg (get_marks i st).
Proof.
  intros sg st i H. unfold get_marks, marks_ok in *. destruct (Nat.lt_ge_cases i (length (as_marks st))) as [Hi|Hi].
  - apply (proj1 (Forall_forall _ _) H). apply nth_In. exact Hi.
  - rewrite nth_overflow by exact Hi. apply mark_ok_0.
Qed.
(* [comment removed for export] *)
Lemma marks_ok_init_repeat : forall st, marks_ok CnfInit st -> as_marks st = repeat 0 (length (as_marks st)).
Proof.
  intros st H. unfold marks_ok in H. induction (as_marks st) as [|k l IH]; [reflexivity|]. cbn [length repeat].
  apply Forall_cons_iff in H. destruct H as [Hk H]. cbn in Hk. rewrite Hk, <- (IH H). reflexivity.
Qed.
Lemma marks_ok_of_repeat : forall sg (st : ap_st bptr) n, as_marks st = repeat 0 n -> marks_ok sg st.
Proof. intros sg st n H. unfold marks_ok. rewrite H. apply Forall_forall. intros k Hk. apply repeat_spec in Hk. subst k. apply mark_ok_0. Qed.

(* [comment removed for export] *)
Definition marks_sub (st' st : ap_st bptr) : Prop := forall k, In k (as_marks st') -> k = 0 \/ In k (as_marks st).
Lemma marks_sub_eq : forall st' st : ap_st bptr, as_marks st' = as_marks st -> marks_sub st' st.
Proof. intros st' st H k Hk. right. rewrite <- H. exact Hk. Qed.
Lemma marks_sub_refl : forall st : ap_st bptr, marks_sub st st.
Proof. intros st. apply marks_sub_eq. reflexivity. Qed.
Lemma in_lset_or : forall {X} (l : list X) i v x, In x (lset l i v) -> x = v \/ In x l.
Proof.
  induction l as [|y l IH]; intros [|i] v x H; cbn in H.
  - destruct H.
  - destruct H.
  - destruct H as [H|H]; [left; symmetry; exact H|right; right; exact H].
  - destruct H as [H|H]; [right; left; exact H|]. destruct (IH i v x H) as [H'|H']; [left; exact H'|right; right; exact H'].
Qed.
Lemma marks_sub_set0 : forall (st' st : ap_st bptr) i, as_marks st' = lset (as_marks st) i 0 -> marks_sub st' st.
Proof. intros st' st i H k Hk. rewrite H in Hk. exact (in_lset_or _ _ _ _ Hk). Qed.
Lemma marks_sub_trans : forall st3 st2 st1 : ap_st bptr, marks_sub st3 st2 -> marks_sub st2 st1 -> marks_sub st3 st1.
Proof. intros st3 st2 st1 H32 H21 k Hk. destruct (H32 k Hk) as [H|H]; [left; exact H|]. exact (H21 k H). Qed.
Lemma marks_ok_sub : forall sg st st', marks_sub st' st -> marks_ok sg st -> marks_ok sg st'.
Proof.
  intros sg st st' HS H. unfold marks_ok in *. apply Forall_forall. intros k Hk.
  destruct (HS k Hk) as [->|Hin]; [apply mark_ok_0|]. exact (proj1 (Forall_forall _ _) H k Hin).
Qed.

(* [comment removed for export] *)
Definition dflags_ok (st : ap_st bptr) : Prop :=
  forall i, get_data i st = None -> Z.land (get_dflags i st) ERR_TXT_MALLOCED = 0.

(* [comment removed for export] *)
Definition data_cells (m : mem) (OW : list block) (st : ap_st bptr) : Prop :=
  (forall i p n, get_data i st = Some (p, n) -> 1 <= n /\ exists junk, rw_cells ctusegs m (badr OW p) [CB (Z.to_nat n) junk])
  /\ dflags_ok st.

Lemma dflags_ok_of_ls : forall ls, dflags_ok (st_of_ls ls).
Proof.
  intros ls i H. unfold get_data, get_dflags in *. cbn [as_data as_dflags st_of_ls] in *.
  revert H. generalize (ls_data ls) i. clear ls. induction l as [|o l IH]; intros [|j] H; cbn in *; try reflexivity.
  - subst o. reflexivity.
  - apply IH. exact H.
Qed.

Lemma data_cells_ls0 : forall m OW, data_cells m OW (st_of_ls ap_ls0).
Proof.
  intros m OW. split; [|apply dflags_ok_of_ls].
  intros i p n H. unfold get_data in H. cbn in H. exfalso. revert H. generalize i. intros j. do 16 (destruct j as [|j]; [discriminate|]). cbn. destruct j; discriminate.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_func : forall m A (bs1 bs2 : list byte),
  bytes_at ctusegs m A bs1 -> bytes_at ctusegs m A bs2 -> length bs1 = length bs2 -> bs1 = bs2.
Proof.
  intros m A bs1 bs2 (_ & _ & H1) (_ & _ & H2) HL. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs1)) as [Hi|Hi].
  - rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs1 i) Hi), (proj2 (nth_error_None bs2 i) ltac:(lia)). reflexivity.
Qed.

Lemma nodup_id_inj : forall (L : list block) b1 b2, List.NoDup (map blk_id L) -> In b1 L -> In b2 L -> blk_id b1 = blk_id b2 -> b1 = b2.
Proof.
  induction L as [|b L IH]; intros b1 b2 ND H1 H2 E; [destruct H1|]. cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI ND].
  destruct H1 as [<-|H1], H2 as [<-|H2]; [reflexivity| | |apply IH; assumption].
  - exfalso. apply NI. rewrite E. apply in_map. exact H2.
  - exfalso. apply NI. rewrite <- E. apply in_map. exact H1.
Qed.

(* [comment removed for export] *)
Lemma env_ids_nodup : forall st m OW E bo, ap_state st m OW E bo -> List.NoDup (env_ids E).
Proof.
  intros st m OW E bo (HE & _ & _ & _ & HT & _ & HB & _).
  pose proof HE as (HF & ND & HP). unfold env_blocks in HF, HP.
  apply Forall_cons_iff in HF as [IES HF]. apply Forall_cons_iff in HF as [IMK HF].
  apply Forall_cons_iff in HF as [ISA HF]. apply Forall_cons_iff in HF as [IND HF]. apply Forall_cons_iff in HF as [IXL _].
  unfold BIO_SIZE, ES_SIZE, MUTEX_SIZE in *.
  assert (SZ : forall p A n A' n', In (p, A, n) OW -> In (p, A', n') OW -> A = A' /\ n = n').
  { intros p A n A' n' I1 I2. pose proof (nodup_id_inj OW _ _ ND I1 I2 eq_refl) as EQ. injection EQ as <- <-. split; reflexivity. }
  assert (D : forall p q A n A' n', In (p, A, n) OW -> In (q, A', n') OW -> n <> n' -> p <> q).
  { intros p q A n A' n' I1 I2 Hn EQ. subst q. destruct (SZ _ _ _ _ _ I1 I2) as [_ En]. exact (Hn En). }
  pose proof (D _ _ _ _ _ _ IES IMK ltac:(lia)) as N5. pose proof (D _ _ _ _ _ _ IES ISA ltac:(lia)) as N6.
  pose proof (D _ _ _ _ _ _ IES IND ltac:(lia)) as N7. pose proof (D _ _ _ _ _ _ IES IXL ltac:(lia)) as N8.
  pose proof (D _ _ _ _ _ _ IMK ISA ltac:(lia)) as N9. pose proof (D _ _ _ _ _ _ IMK IND ltac:(lia)) as N10.
  pose proof (D _ _ _ _ _ _ IMK IXL ltac:(lia)) as N11. pose proof (D _ _ _ _ _ _ ISA IND ltac:(lia)) as N12.
  pose proof (D _ _ _ _ _ _ ISA IXL ltac:(lia)) as N13. pose proof (D _ _ _ _ _ _ IND IXL ltac:(lia)) as N14.
  unfold env_ids, env_blocks. cbn [map blk_id fst snd].
  repeat (constructor; [cbn [In]; intuition congruence|]). constructor.
Qed.

Lemma ids_ok_of_ls0 : forall E, List.NoDup (env_ids E) -> ids_ok E (st_of_ls ap_ls0).
Proof.
  intros E H. apply ids_ok_join.
  - unfold ids_ok0, es_ids, st_blocks. cbn. split; [exact H|]. unfold ERR_NUM. split; lia.
  - apply (marks_ok_of_repeat _ _ ERR_NUM). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma marks_ok_st_of_ls : forall sg (ls : ap_ls bptr), marks_ok sg (st_of_ls ls).
Proof. intros sg ls. apply (marks_ok_of_repeat _ _ ERR_NUM). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ap_pre (s : PState) (st : ap_st bptr) (m : mem) (OW LB : list block) (E : ap_env) (bo : Z * Z)
    (sp : word) (lo B : Z) (errv canary : word) (stack : Z) : Prop :=
  RHEAP s (OW ++ LB) m /\ ap_state st m OW E bo /\ ids_ok E st /\ data_cells m OW st
  /\ rauxv_ok m B /\ bv_unsigned sp <= B /\ B < 2^63
  /\ stk ctusegs m lo (bv_unsigned sp) /\ alloc_ceiling <= lo /\ GLOBALS_TOP <= lo /\ lo <= bv_unsigned sp - stack
  /\ rw_cells ctusegs m (errno_addr (wz RATP)) [C4 errv] /\ ssp_cells m canary
  /\ mem_inv ctusegs m /\ bv_unsigned sp mod 16 = 0.

Lemma ap_pre_stack_le : forall s st m OW LB E bo sp lo B errv canary stack stack',
  ap_pre s st m OW LB E bo sp lo B errv canary stack -> stack' <= stack -> ap_pre s st m OW LB E bo sp lo B errv canary stack'.
Proof.
  intros until stack'. intros H Hle. unfold ap_pre in *.
  destruct H as (A1 & A2 & A2' & A2'' & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13). repeat (split; [assumption|]). split; [lia|]. repeat (split; [assumption|]). exact A13.
Qed.

(* [comment removed for export] *)
Definition ap_lib_inv2 (ls : ap_ls bptr) (m : mem) (OW : list block) : Prop :=
  exists E, ap_lib_state ls m OW E /\ ids_ok E (st_of_ls ls) /\ data_cells m OW (st_of_ls ls).

Lemma ap_lib_inv2_agree : forall ls OW m m',
  ap_lib_inv2 ls m OW -> agree_on (fun a => rin_ivs LIBW_HX a \/ in_block OW a) m m' -> ap_lib_inv2 ls m' OW.
Proof.
  intros ls OW m m' (E & (Hwf & HSG & nw & HS) & HI & [HD HDF]) AG. exists E. split; [|split; [exact HI|]]. { split; [exact Hwf|]. split; [exact HSG|]. exists nw.
  eapply ApRep.ap_state_agree; [exact HS|exact AG]. }
  split; [|exact HDF].
  intros i p n Hd. destruct (HD i p n Hd) as [Hn [junk HC]]. split; [exact Hn|]. exists junk.
  eapply rw_cells_agree; [exact AG|exact HC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. rewrite Nat.add_0_r in Ha.
  destruct HS as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & FD)).
  assert (HIn : In (Some (p, n)) (as_data (st_of_ls ls))).
  { unfold get_data in Hd. rewrite <- Hd. apply nth_In. destruct (Nat.lt_ge_cases i (length (as_data (st_of_ls ls)))) as [L|L]; [exact L|]. rewrite (nth_overflow _ None L) in Hd. discriminate. }
  pose proof (proj1 (Forall_forall _ _) FD _ HIn) as [HB _]. cbn in HB. right. exists (p, badr OW p, n). split; [exact HB|]. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma ap_lib_inv2_init : forall m OW, ap_lib_inv ap_ls0 m OW -> ap_lib_inv2 ap_ls0 m OW.
Proof.
  intros m OW (E & Hwf & HSG & nw & HS). exists E. split; [split; [exact Hwf|split; [exact HSG|exists nw; exact HS]]|].
  split; [|apply data_cells_ls0]. apply ids_ok_of_ls0. eapply env_ids_nodup. exact HS.
Qed.

(* [comment removed for export] *)
Definition blocks_kept (K : list block) (st' : ap_st bptr) (OW' : list block) (m m' : mem) : Prop :=
  (forall b, In b K -> In b OW') /\ (forall b, In b K -> ~ In (blk_id b) (es_ids st'))
  /\ (forall a, 0 <= a < 2^64 -> in_block K a -> m' (wa a) = m (wa a)).

(* [comment removed for export] *)
Definition ap_post {A : Type} (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (OW LB : list block) (E : ap_env) (lo B : Z) (canary : word) (m : mem) (K : list block)
    (RES : A * ap_st bptr -> list block -> mem -> word -> Z * Z -> Prop)
    (r : A * ap_st bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' (errv' : word) bo',
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctusegs)
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
    /\ ap_pre s' (snd r) m' OW' LB E bo' sp lo B errv' canary 0
    /\ lx_pres LB (bv_unsigned sp) LIBW_AP m m'
    /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s
    /\ blocks_kept K (snd r) OW' m m'
    /\ RES r OW' m' a0 bo'.

(* [comment removed for export] *)
Definition ap_stmt {A} (entry stack : Z)
    (ARGS : ap_st bptr -> list block -> mem -> word -> word -> word -> word -> word -> word -> Z * Z -> Prop)    (* [comment removed for export] *)
    (c : ap_st bptr -> aprog bptr (A * ap_st bptr))
    (RES : A * ap_st bptr -> list block -> mem -> word -> Z * Z -> Prop) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo B : Z) (errv canary : word) (K : list block),
    ap_pre s st m OW LB E bo sp lo B errv canary stack -> tp = wz RATP -> frm0 fc ->
    ARGS st OW m a0 a1 a2 a3 a4 a5 bo ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    implM ctusegs (interp (ap_embed (c st))) s
          (ap_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s OW LB E lo B canary m K RES)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz entry) fc None m (seg_rom ctusegs)).

(* [comment removed for export] *)
Definition ap_stmt_at {A} (sg : cnf_stage) (entry stack : Z)
    (ARGS : ap_st bptr -> list block -> mem -> word -> word -> word -> word -> word -> word -> Z * Z -> Prop)
    (c : ap_st bptr -> aprog bptr (A * ap_st bptr))
    (RES : A * ap_st bptr -> list block -> mem -> word -> Z * Z -> Prop) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo B : Z) (errv canary : word) (K : list block),
    ap_pre s st m OW LB E bo sp lo B errv canary stack -> e_stage E = sg -> tp = wz RATP -> frm0 fc ->
    ARGS st OW m a0 a1 a2 a3 a4 a5 bo ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    implM ctusegs (interp (ap_embed (c st))) s
          (ap_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s OW LB E lo B canary m K RES)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz entry) fc None m (seg_rom ctusegs)).

Lemma ap_stmt_any_at : forall {A} sg entry stack ARGS (c : ap_st bptr -> aprog bptr (A * ap_st bptr)) RES,
  ap_stmt entry stack ARGS c RES -> ap_stmt_at sg entry stack ARGS c RES.
Proof. intros A sg entry stack ARGS c RES H. unfold ap_stmt_at. intros. eapply H; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma implM_ap_lbind : forall {A B} (t : aprog bptr A) (f : A -> aprog bptr B) s Q ms,
  implM ctusegs (interp (lbind (ap_embed t) (fun a => ap_embed (f a)))) s Q ms ->
  implM ctusegs (interp (ap_embed (apbind t f))) s Q ms.
Proof.
  intros A B t f. induction t as [a| |n k IH|p k IH|p n k IH|p n k IH|o k IH|p n k IH]; intros s Q ms H; cbn [apbind ap_embed lbind interp] in *; try exact H.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [u s1] ms1 H1. cbn [fst snd] in *. apply (IH s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - (* [comment removed for export] *) unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
Qed.

Lemma implM_apbind : forall {A B} (t : aprog bptr A) (f : A -> aprog bptr B) s Q1 Q ms,
  implM ctusegs (interp (ap_embed t)) s Q1 ms ->
  (forall a s' ms', Q1 a s' ms' -> implM ctusegs (interp (ap_embed (f a))) s' Q ms') ->
  implM ctusegs (interp (ap_embed (apbind t f))) s Q ms.
Proof. intros A B t f s Q1 Q ms H1 H2. apply implM_ap_lbind. eapply implM_interp_bind; [exact H1|exact H2]. Qed.

(* [comment removed for export] *)
Lemma implM_abind : forall {A B} (m : AM A) (f : A -> AM B) (st : ap_st bptr) s Q1 Q ms,
  implM ctusegs (interp (ap_embed (m st))) s Q1 ms ->
  (forall r s' ms', Q1 r s' ms' -> implM ctusegs (interp (ap_embed (f (fst r) (snd r)))) s' Q ms') ->
  implM ctusegs (interp (ap_embed (abind m f st))) s Q ms.
Proof. intros A B m f st s Q1 Q ms H1 H2. unfold abind. eapply implM_apbind; [exact H1|]. intros [a st'] s' ms' H. apply (H2 (a, st')). exact H. Qed.

Lemma implM_aret : forall {A} (a : A) (st : ap_st bptr) s Q ms,
  evt ctusegs (Q (a, st) s) ms -> implM ctusegs (interp (ap_embed (aret a st))) s Q ms.
Proof. intros. unfold aret. cbn [ap_embed interp]. apply implM_ret. assumption. Qed.

Lemma implM_aunr : forall {A} (st : ap_st bptr) s (Q : A * ap_st bptr -> PState -> machine_state -> Prop) ms,
  implM ctusegs (interp (ap_embed (@aunr bptr A st))) s Q ms.
Proof. intros. unfold aunr. cbn [ap_embed interp]. apply implM_unr. Qed.

(* [comment removed for export] *)
Lemma implM_amodify : forall (g : ap_st bptr -> ap_st bptr) (st : ap_st bptr) s Q ms,
  evt ctusegs (Q (tt, g st) s) ms -> implM ctusegs (interp (ap_embed (amodify g st))) s Q ms.
Proof. intros. unfold amodify. cbn [ap_embed interp]. apply implM_ret. assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ERR_NEW : Z := 0xe7dc4.        Definition ERR_NEW_STACK : Z := 48 + 48 + 16 + 8192.      (* [comment removed for export] *)
Definition ERR_SET_DEBUG : Z := 0xe7f80.  Definition ERR_SET_DEBUG_STACK : Z := 80 + 48 + 8192.     (* [comment removed for export] *)
Definition ERR_SET_ERROR : Z := 0xe8124.  Definition ERR_SET_ERROR_STACK : Z := 80 + 96 + 48 + 8192. (* [comment removed for export] *)

Definition ERR_new_stmt : Prop :=
  ap_stmt ERR_NEW ERR_NEW_STACK (fun st OW m a0 a1 a2 a3 a4 a5 bo => True) (err_new)
          (fun r OW' m' a0' bo' => True).
(* [comment removed for export] *)
Definition ERR_set_debug_stmt (rs : rsite) (file func : Z) : Prop :=
  ap_stmt ERR_SET_DEBUG ERR_SET_DEBUG_STACK
          (fun st OW m a0 a1 a2 a3 a4 a5 bo => a0 = wz file /\ a1 = wz (rs_line rs) /\ a2 = wz func) (err_set_debug rs)
          (fun r OW' m' a0' bo' => True).
Definition ERR_set_error_stmt (rs : rsite) (lib reason : Z) : Prop :=
  ap_stmt ERR_SET_ERROR ERR_SET_ERROR_STACK
          (fun st OW m a0 a1 a2 a3 a4 a5 bo => a0 = wz lib /\ a1 = wz reason /\ a2 = wz 0 /\ rs_code rs = ERR_PACK lib reason) (err_set_error rs)
          (fun r OW' m' a0' bo' => True).
End WithCeiling0.
