(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApLogic ApInv ApErr ApParse ApPrim ApBridge ApOwner.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_libiface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA ImplA BnRepDefs BnRepA UnwindA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require ApIface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation es_ids := CtRepP.ApIface.es_ids.
Notation mark_ok := CtRepP.ApIface.mark_ok.
Notation marks_ok := CtRepP.ApIface.marks_ok.
Notation ids_ok0 := CtRepP.ApIface.ids_ok0.
Notation ids_ok := CtRepP.ApIface.ids_ok.
Notation marks_sub := CtRepP.ApIface.marks_sub.
Notation dflags_ok := CtRepP.ApIface.dflags_ok.
Notation blocks_kept := CtRepP.ApIface.blocks_kept.
Notation ids_ok_split := CtRepP.ApIface.ids_ok_split.
Notation ids_ok_ids0 := CtRepP.ApIface.ids_ok_ids0.
Notation ids_ok_marks := CtRepP.ApIface.ids_ok_marks.
Notation ids_ok_join := CtRepP.ApIface.ids_ok_join.
Notation marks_ok_get := CtRepP.ApIface.marks_ok_get.
Notation marks_ok_sub := CtRepP.ApIface.marks_ok_sub.
Notation marks_sub_refl := CtRepP.ApIface.marks_sub_refl.
Notation marks_sub_eq := CtRepP.ApIface.marks_sub_eq.
Notation marks_sub_set0 := CtRepP.ApIface.marks_sub_set0.
Notation marks_sub_trans := CtRepP.ApIface.marks_sub_trans.
Notation marks_ok_st_of_ls := CtRepP.ApIface.marks_ok_st_of_ls.
Notation ids_ok_of_ls0 := CtRepP.ApIface.ids_ok_of_ls0.
Notation nodup_id_inj := CtRepP.ApIface.nodup_id_inj.

(* [comment removed for export] *)
Definition ERR_DATA_MAX_A : Z := 64512.
Definition data_cells (m : mem) (OW : list block) (st : ap_st bptr) : Prop :=
  (forall i p n, get_data i st = Some (p, n) -> 1 <= n <= ERR_DATA_MAX_A /\ exists junk, rw_cells ctasegs m (badr OW p) [CB (Z.to_nat n) junk])
  /\ dflags_ok st.

Lemma data_cells_ls0 : forall m OW, data_cells m OW (st_of_ls ap_ls0).
Proof.
  intros m OW. split; [|apply CtRepP.ApIface.dflags_ok_of_ls].
  intros i p n H. unfold get_data in H. cbn in H. exfalso. revert H. generalize i. intros j. do 16 (destruct j as [|j]; [discriminate|]). cbn. destruct j; discriminate.
Qed.

Lemma data_cells_agree : forall m m' OW st, data_cells m OW st -> agree_on (lib_addr OW) m m' ->
  Forall (optb_ok OW) (as_data st) -> data_cells m' OW st.
Proof.
  intros m m' OW st [HD HDF] AG FD. split; [|exact HDF].
  intros i p n Hd. destruct (HD i p n Hd) as [Hn [junk HC]]. split; [exact Hn|]. exists junk.
  eapply rw_cells_agree; [exact AG|exact HC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. rewrite Nat.add_0_r in Ha.
  assert (HIn : In (Some (p, n)) (as_data st)).
  { unfold get_data in Hd. rewrite <- Hd. apply nth_In. destruct (Nat.lt_ge_cases i (length (as_data st))) as [L|L]; [exact L|]. rewrite (nth_overflow _ None L) in Hd. discriminate. }
  pose proof (proj1 (Forall_forall _ _) FD _ HIn) as [HB _]. cbn in HB. eapply lib_addr_block; [exact HB|]. lia.
Qed.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation FR := (@ar_FR AR).

(* [comment removed for export] *)
Lemma env_ids_nodup : forall st m OW E bo, ap_state st m OW E bo -> List.NoDup (env_ids E).
Proof.
  intros st m OW E bo (HE & _ & _ & HT & _ & HB & _).
  pose proof HE as (HF & ND & HP). unfold CtRepP.ApRepDefs.env_blocks in HF, HP.
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
  unfold CtRepP.ApRepDefs.env_ids, CtRepP.ApRepDefs.env_blocks. cbn [map blk_id fst snd].
  repeat (constructor; [cbn [In]; intuition congruence|]). constructor.
Qed.

(* [comment removed for export] *)
Definition ax_client (LB : list block) (SP : Z) (X : list (Z * Z)) (a : Z) : Prop := ~ rin_ivs X a /\ aclient_addr LB SP a.
Definition ax_pres (LB : list block) (SP : Z) (X : list (Z * Z)) (m m' : mem) : Prop := agree_on (ax_client LB SP X) m m'.

Lemma ax_pres_refl : forall LB SP X m, ax_pres LB SP X m m.
Proof. intros. apply agree_on_refl. Qed.
Lemma ax_pres_trans : forall LB SP X m1 m2 m3, ax_pres LB SP X m1 m2 -> ax_pres LB SP X m2 m3 -> ax_pres LB SP X m1 m3.
Proof. intros LB SP X m1 m2 m3. apply agree_on_trans. Qed.
Lemma ax_pres_weaken : forall LB LB' SP SP' X X' m m',
  ax_pres LB SP X m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> (forall a, rin_ivs X a -> rin_ivs X' a) -> ax_pres LB' SP' X' m m'.
Proof.
  intros LB LB' SP SP' X X' m m' H HS HL HX. eapply agree_on_mono; [exact H|]. intros a [H1 H2]. split; [intros Hx; apply H1; apply HX; exact Hx|].
  destruct H2 as [H2|[H2|(b & Hb & Hr)]]; [left; lia | right; left; exact H2 | right; right]. exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition apres (LB X : list block) (SP : Z) (m m' : mem) : Prop := agree_on (aclient_addr (X ++ LB) SP) m m'.

Lemma apres_refl : forall LB X SP m, apres LB X SP m m.
Proof. intros. apply agree_on_refl. Qed.
Lemma apres_trans : forall LB X SP m1 m2 m3, apres LB X SP m1 m2 -> apres LB X SP m2 m3 -> apres LB X SP m1 m3.
Proof. intros LB X SP m1 m2 m3. apply agree_on_trans. Qed.
Lemma apres_weaken : forall LB X X' SP SP' m m',
  apres LB X SP m m' -> SP <= SP' -> (forall b, In b X' -> In b X) -> apres LB X' SP' m m'.
Proof.
  intros LB X X' SP SP' m m' H HS HX. eapply agree_on_mono; [exact H|]. intros a [Ha|[Ha|(b & Hb & Hr)]]; [left; lia | right; left; exact Ha | right; right].
  exists b. split; [| exact Hr]. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply HX; exact Hb | right; exact Hb].
Qed.
Lemma agree_of_apres : forall LB X SP m m', apres LB X SP m m' -> agree_on (aclient_addr (X ++ LB) SP) m m'.
Proof. intros LB X SP m m' H. exact H. Qed.
(* [comment removed for export] *)
Lemma apres_of_munch : forall LB X SP W m m',
  munch W m m' -> (forall a, aclient_addr (X ++ LB) SP a -> outside W a) -> apres LB X SP m m'.
Proof. intros LB X SP W m m' MU HO. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]. intros a Ha. exact (HO a Ha). Qed.
(* [comment removed for export] *)
Lemma rw_cells_apres : forall LB X SP m m' A cs,
  apres LB X SP m m' -> rw_cells ctasegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> aclient_addr (X ++ LB) SP a) -> rw_cells ctasegs m' A cs.
Proof. intros LB X SP m m' A cs H HC HR. eapply rw_cells_agree; [exact H | exact HC | exact HR]. Qed.

(* [comment removed for export] *)
Lemma in_block_mono : forall (L1 L2 : list block) a, (forall b, In b L1 -> In b L2) -> in_block L1 a -> in_block L2 a.
Proof. intros L1 L2 a HI (b & Hb & Hr). exists b. split; [apply HI; exact Hb | exact Hr]. Qed.
Lemma in_block_app_remove : forall p (X LB : list block) a,
  (forall b, In b LB -> blk_id b <> p) -> in_block (lb_remove p X ++ LB) a -> in_block (lb_remove p (X ++ LB)) a.
Proof.
  intros p X LB a HLB (b & Hb & Hr). exists b. split; [| exact Hr]. apply in_app_iff in Hb. apply lb_remove_In. destruct Hb as [Hb|Hb].
  - apply lb_remove_In in Hb. destruct Hb as [Hb Hne]. split; [apply in_or_app; left; exact Hb | exact Hne].
  - split; [apply in_or_app; right; exact Hb | exact (HLB b Hb)].
Qed.
Lemma ids_disj : forall (OW LB : list block) p A n, List.NoDup (map blk_id (OW ++ LB)) -> In (p, A, n) OW -> forall b, In b LB -> blk_id b <> p.
Proof.
  intros OW LB p A n ND HIN b Hb E. revert ND HIN. induction OW as [|b0 OW IH]; intros ND HIN; [destruct HIN|].
  cbn in ND. apply NoDup_cons_iff in ND. destruct ND as [NI ND]. destruct HIN as [->|HIN]; [| exact (IH ND HIN)].
  apply NI. cbn. rewrite map_app. apply in_or_app. right. rewrite <- E. apply in_map. exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ap_preA (Σ : rts RT) (st : ap_st bptr) (m : mem) (OW LB : list block) (E : ap_env) (bo : Z * Z)
    (sp : word) (lo : Z) (stack cost frames : Z) : Prop :=
  AHEAP Σ OW LB m /\ ap_state st m OW E bo /\ ids_ok E st /\ data_cells m OW st
  /\ stk ctasegs m lo (bv_unsigned sp) /\ ACEIL <= lo /\ lo <= bv_unsigned sp - stack
  /\ bv_unsigned sp + 16 <= USTACK_TOP /\ bv_unsigned sp mod 16 = 0
  /\ mem_inv ctasegs m
  /\ 0 <= cost <= rt_credit RT Σ
  /\ 0 <= frames /\ Z.of_nat (length FR) + frames <= Z.of_nat FRAMES_MAX.
  (* [comment removed for export] *)

Lemma ap_preA_weaken : forall Σ st m OW LB E bo sp lo stack cost frames stack' cost' frames',
  ap_preA Σ st m OW LB E bo sp lo stack cost frames -> stack' <= stack -> 0 <= cost' <= cost -> 0 <= frames' <= frames ->
  ap_preA Σ st m OW LB E bo sp lo stack' cost' frames'.
Proof.
  intros until frames'. intros H Hs Hc Hf. unfold ap_preA in *.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [lia|].
  split; [exact A8|]. split; [exact A9|]. split; [exact A10|]. split; [lia|]. lia.
Qed.

(* [comment removed for export] *)
Definition ap_lib_inv2 (ls : ap_ls bptr) (m : mem) (OW : list block) : Prop :=
  exists E, ap_lib_state ls m OW E /\ ids_ok E (st_of_ls ls) /\ data_cells m OW (st_of_ls ls).

(* [comment removed for export] *)
Definition ap_postA {A : Type} (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (lo : Z) (m : mem) (K : list block) (cost : Z)
    (RES : A * ap_st bptr -> list block -> mem -> word -> Z * Z -> Prop)
    (r : A * ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' bo',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ ap_preA Σ' (snd r) m' OW' LB E bo' sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) LIBW_A m m'
    /\ rt_credit RT Σ - cost <= rt_credit RT Σ'
    /\ blocks_kept K (snd r) OW' m m'
    /\ RES r OW' m' a0 bo'.
  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ap_stmtA {A} (entry stack cost frames : Z)
    (ARGS : ap_st bptr -> list block -> mem -> word -> word -> word -> word -> word -> word -> Z * Z -> Prop)    (* [comment removed for export] *)
    (c : ap_st bptr -> aprog bptr (A * ap_st bptr))
    (RES : A * ap_st bptr -> list block -> mem -> word -> Z * Z -> Prop) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo : Z) (K : list block) (ras : list Z),
    ap_preA Σ st m OW LB E bo sp lo stack cost frames -> tp = wz TP_A ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx entry (bv_unsigned ra :: ras) -> ras <> nil ->      (* [comment removed for export] *)
    ARGS st OW m a0 a1 a2 a3 a4 a5 bo ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    implAp (c st) Σ
          (ap_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K cost RES)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz entry) fc None m (seg_rom ctasegs)).

Definition ap_stmtA_at {A} (sg : cnf_stage) (entry stack cost frames : Z)
    (ARGS : ap_st bptr -> list block -> mem -> word -> word -> word -> word -> word -> word -> Z * Z -> Prop)
    (c : ap_st bptr -> aprog bptr (A * ap_st bptr))
    (RES : A * ap_st bptr -> list block -> mem -> word -> Z * Z -> Prop) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo : Z) (K : list block) (ras : list Z),
    ap_preA Σ st m OW LB E bo sp lo stack cost frames -> e_stage E = sg -> tp = wz TP_A ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx entry (bv_unsigned ra :: ras) -> ras <> nil ->      (* [comment removed for export] *)
    ARGS st OW m a0 a1 a2 a3 a4 a5 bo ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    implAp (c st) Σ
          (ap_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K cost RES)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz entry) fc None m (seg_rom ctasegs)).

Lemma ap_stmtA_any_at : forall {A} sg entry stack cost frames ARGS (c : ap_st bptr -> aprog bptr (A * ap_st bptr)) RES,
  ap_stmtA entry stack cost frames ARGS c RES -> ap_stmtA_at sg entry stack cost frames ARGS c RES.
Proof. intros A sg entry stack cost frames ARGS c RES H. unfold ap_stmtA_at. intros. eapply H; eassumption. Qed.

(* [comment removed for export] *)
Lemma ap_stmtA_weaken : forall {A} entry stack cost frames stack' cost' frames' ARGS (c : ap_st bptr -> aprog bptr (A * ap_st bptr)) RES,
  ap_stmtA entry stack cost frames ARGS c RES -> stack <= stack' -> 0 <= cost <= cost' -> 0 <= frames <= frames' ->
  ap_stmtA entry stack' cost' frames' ARGS c RES.
Proof.
  intros A entry stack cost frames stack' cost' frames' ARGS c RES H Hs Hc Hf. unfold ap_stmtA. intros.
  eapply implAp_mono; [eapply H; try eassumption; eapply ap_preA_weaken; [eassumption| lia| lia| lia]|].
  intros [a st'] Σ' ms' PO. cbv beta in PO |- *.
  destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F2 & fc2 & m2 & OW2 & bo2 & E2 & PRE2 & AXP2 & CRED2 & KEPT2 & RES2).
  do 17 eexists. exists m2, OW2, bo2. repeat (split; [eassumption|]). split; [lia|]. split; [exact KEPT2| exact RES2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma implAp_abind : forall {A B} (ma : AM A) (f : A -> AM B) (st : ap_st bptr) Σ Q1 Q ms,
  implAp (ma st) Σ Q1 ms ->
  (forall r Σ' ms', Q1 r Σ' ms' -> implAp (f (fst r) (snd r)) Σ' Q ms') ->
  implAp (abind ma f st) Σ Q ms.
Proof. intros A B ma f st Σ Q1 Q ms H1 H2. unfold abind. eapply implAp_bind; [exact H1|]. intros [a st'] Σ' ms' H. apply (H2 (a, st')). exact H. Qed.

Lemma implAp_aret : forall {A} (a : A) (st : ap_st bptr) Σ (Q : A * ap_st bptr -> rts RT -> machine_state -> Prop) ms,
  Q (a, st) Σ ms -> implAp (aret a st) Σ Q ms.
Proof. intros. unfold aret. apply implAp_ret. assumption. Qed.

Lemma implAp_aret_evt : forall {A} (a : A) (st : ap_st bptr) Σ (Q : A * ap_st bptr -> rts RT -> machine_state -> Prop) ms,
  evt ctasegs (Q (a, st) Σ) ms -> implAp (aret a st) Σ Q ms.
Proof. intros. unfold aret. apply implAp_ret_evt. assumption. Qed.

Lemma implAp_aunr : forall {A} (st : ap_st bptr) Σ (Q : A * ap_st bptr -> rts RT -> machine_state -> Prop) ms,
  implAp (@aunr bptr A st) Σ Q ms.
Proof. intros. unfold aunr. apply implAp_unr. Qed.

Lemma implAp_amodify : forall (g : ap_st bptr -> ap_st bptr) (st : ap_st bptr) Σ Q ms,
  Q (tt, g st) Σ ms -> implAp (amodify g st) Σ Q ms.
Proof. intros. unfold amodify. apply implAp_ret. assumption. Qed.

(* [comment removed for export] *)
Lemma implAp_asys : forall (o : ApBase.sysop) (st : ap_st bptr) Σ (Q : Z * ap_st bptr -> rts RT -> machine_state -> Prop) ms
    (R : Z -> machine_state -> Prop),
  cps ctasegs (ASTA RT Σ PMc (eq ms)) (ASTA RT Σ PMc (fun ms' => exists r, R r ms')) ->
  (forall r ms', R r ms' -> Q (r, st) Σ ms') ->
  implAp (asys o st) Σ Q ms.
Proof.
  intros o st Σ Q ms R H1 H2. unfold asys. eapply implAp_sys; [exact H1|]. intros r ms' HR. apply implAp_ret. exact (H2 r ms' HR).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ERR_NEW : Z := 0x1fd52c.        Definition ERR_NEW_STACK : Z := 48 + 48 + 112 + 64 + RT_STACK.        Definition ERR_NEW_COST : Z := 4.        Definition ERR_NEW_FRAMES : Z := 4.
Definition ERR_SET_DEBUG : Z := 0x1fd844.  Definition ERR_SET_DEBUG_STACK : Z := 96 + 48 + 112 + 64 + RT_STACK.  Definition ERR_SET_DEBUG_COST : Z := 4.  Definition ERR_SET_DEBUG_FRAMES : Z := 4.
Definition ERR_VSET_ERROR : Z := 0x1fdc70. Definition ERR_VSET_ERROR_STACK : Z := 112 + 48 + 112 + 64 + RT_STACK. Definition ERR_VSET_ERROR_COST : Z := 4. Definition ERR_VSET_ERROR_FRAMES : Z := 4.
Definition ERR_VSET_ERROR_RA : Z := 0x1fdbd8.   (* [comment removed for export] *)
Definition ERR_SET_ERROR : Z := 0x1fdab8.  Definition ERR_SET_ERROR_STACK : Z := 144 + ERR_VSET_ERROR_STACK.      Definition ERR_SET_ERROR_COST : Z := 1 + ERR_VSET_ERROR_COST.
Definition ERR_SET_ERROR_FRAMES : Z := 1 + ERR_VSET_ERROR_FRAMES.
Definition ERR_FRAMES : Z := 4.   (* [comment removed for export] *)

Definition ERR_new_stmtA : Prop :=
  ap_stmtA ERR_NEW ERR_NEW_STACK ERR_NEW_COST ERR_NEW_FRAMES (fun st OW m a0 a1 a2 a3 a4 a5 bo => True) (err_new)
           (fun r OW' m' a0' bo' => True).
Definition ERR_set_debug_stmtA (rs : rsite) (file func : Z) : Prop :=
  ap_stmtA ERR_SET_DEBUG ERR_SET_DEBUG_STACK ERR_SET_DEBUG_COST ERR_SET_DEBUG_FRAMES
           (fun st OW m a0 a1 a2 a3 a4 a5 bo => a0 = wz file /\ a1 = wz (rs_line rs) /\ a2 = wz func) (err_set_debug rs)
           (fun r OW' m' a0' bo' => True).

(* [comment removed for export] *)
Definition ERR_set_error_specA (rs : rsite) (lib reason : Z) : Prop := forall bo0 : Z * Z,
  ap_stmtA ERR_SET_ERROR ERR_SET_ERROR_STACK ERR_SET_ERROR_COST ERR_SET_ERROR_FRAMES
           (fun st OW m a0 a1 a2 a3 a4 a5 bo => a0 = wz lib /\ a1 = wz reason /\ a2 = wz 0 /\ rs_code rs = ERR_PACK lib reason
                                                 /\ 0 <= lib < 256 /\ lib <> ERR_LIB_SYS /\ 0 <= reason < 8388608 /\ bo = bo0)
           (err_set_error rs)
           (fun r OW' m' a0' bo' => bo' = bo0).

(* [comment removed for export] *)
Definition ERR_vset_error_specA (rs : rsite) (lib reason : Z) : Prop := forall bo0 : Z * Z,
  ap_stmtA ERR_VSET_ERROR ERR_VSET_ERROR_STACK ERR_VSET_ERROR_COST ERR_VSET_ERROR_FRAMES
           (fun st OW m a0 a1 a2 a3 a4 a5 bo => a0 = wz lib /\ a1 = wz reason /\ a2 = wz 0 /\ rs_code rs = ERR_PACK lib reason
                                                 /\ 0 <= lib < 256 /\ lib <> ERR_LIB_SYS /\ 0 <= reason < 8388608 /\ bo = bo0)
           (err_set_error rs)
           (fun r OW' m' a0' bo' => bo' = bo0).

(* [comment removed for export] *)
Definition ERR_CLEAR_ERROR : Z := 0x1fe828.
Definition ERR_CLEAR_ERROR_STACK : Z := 96 + 48 + 112 + 64 + RT_STACK.  Definition ERR_CLEAR_ERROR_COST : Z := 8.  Definition ERR_CLEAR_ERROR_FRAMES : Z := 8.
Definition ERR_clear_error_specA : Prop := forall bo0 : Z * Z,
  ap_stmtA ERR_CLEAR_ERROR ERR_CLEAR_ERROR_STACK ERR_CLEAR_ERROR_COST ERR_CLEAR_ERROR_FRAMES
           (fun st OW m a0 a1 a2 a3 a4 a5 bo => bo = bo0) (fun st => err_clear_error st)
           (fun r OW' m' a0' bo' => bo' = bo0 /\ snd r = st_of_ls (ls_of_st (snd r))).

End WithRT.
