(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimPopLens APrimQ APrimFrame AFrameM
                        APrimDealloc APrimCover ASec ASecD AQuar AQuarM AHeap AFoot F_prim_refill F_prim_cdealloc F_poison F_quar_Ep F_quar_E F_quar_A AQuarR AQuarS AQuarP ATacFix
                        F_quar_M F_quar_DR F_quar_R F_quar_D F_sec_A F_sec_B F_quar_P AQuarT AQuarU F_gct F_depot F_depot_C F_quar_C F_prim_L0 F_hooks F_dealloc
                        F_ialloc F_unwind F_stacktrace F_free_icpt F_free_null F_alloc_env ALedger AHeap2 AHeapB AFreeF AFreeZ AFsEnv AFteF.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section FL8.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).
Notation L := (al_thread AL).
Notation D := (al_depot AL).
Notation THR := (at_thr (al_thread AL)).
Notation TQ := (at_thr (al_thread AL) + TQ_OFF).

#[using="Type"] Lemma held_ok_perm : forall P h1 h2, Permutation h1 h2 -> held_ok P h1 -> held_ok P h2.
Proof. intros P h1 h2 PM [ND FH]. split; [eapply Permutation_NoDup; eassumption| eapply Permutation_Forall; eassumption]. Qed.

#[using="Type"] Lemma dr_inv_hrest_perm : forall X H (m : mem) WB WC h1 h2, Permutation h1 h2 ->
  dr_inv AL E X H m WB WC h1 -> dr_inv AL E X H m WB WC h2.
Proof.
  intros X H m WB WC h1 h2 PM (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & REST).
  unfold dr_inv. repeat (split; [assumption|]). split; [| exact REST].
  eapply held_ok_perm; [| exact HOK]. apply Permutation_app_head. apply Permutation_app_head. exact PM.
Qed.

#[using="Type"] Lemma sec_nodup : forall S, sec_wf AL S -> List.NoDup (se_chunks S).
Proof.
  intros S (_ & _ & _ & _ & _ & COK & CSEP). induction CSEP as [|c l FA _ IH]; [constructor|].
  apply Forall_cons_iff in COK as [CK COK]. constructor; [| exact (IH COK)].
  intros Hin. pose proof (proj1 (Forall_forall _ _) FA c Hin) as AP. pose proof (chunk_ok_msize AL c CK) as [M1 _]. unfold apart_chunks in AP. lia.
Qed.

#[using="Type"] Lemma free_pre : forall s LB (m : mem) k A n,
  RHEAP_B AL E s LB m -> mem_inv asegs m -> In (k, A, n) LB ->
  exists ch l1 l2, bs_live s = l1 ++ (ch, n) :: l2 /\ A = qc_hdr AL ch + 16 /\ k = A
    /\ dr_inv AL E (bs_X s) (bs_H s) m (bs_gl s) (flat_map qb_chunks (bs_gl s)) (prim_of ch ++ flat_map prim_of (map fst (l1 ++ l2)))
    /\ held_kind (bs_X s) ch /\ qchunk_wf ch /\ lchunk_rep AL m ch
    /\ (forall sc, In sc (sec_of ch) -> ~ In sc (flat_map sec_of (flat_map qb_chunks (bs_gl s)))).
Proof.
  intros s LB m k A n (PLB & LOK & AO & INVB & QLG & GC & QCL & MTX & QE & QWF & RD & DOK & WFL & REPL & HKL & PSEC & COV & REST) MI HIN.
  pose proof (dr_inv_of_B AL E _ _ _ _ _ _ INVB MI) as INV.
  assert (HIN' : In (k, A, n) (map (blk_ofB AL) (bs_live s))) by (eapply Permutation_in; eassumption).
  apply in_map_iff in HIN' as ([ch cn] & EB & HL). unfold blk_ofB, lc_user in EB. cbn [fst snd] in EB. inversion EB; subst k A n. clear EB.
  apply in_split in HL as (l1 & l2 & EL). exists ch, l1, l2.
  assert (INC : In ch (live_chunks s)) by (unfold live_chunks; rewrite EL, map_app; apply in_or_app; right; left; reflexivity).
  split; [exact EL|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  { eapply dr_inv_hrest_perm; [| exact INV]. unfold heldB, live_chunks. rewrite EL, !map_app, !flat_map_app. cbn [map flat_map fst].
    apply Permutation_app_swap_app. }
  split; [exact (proj1 (Forall_forall _ _) HKL ch INC)|]. split; [exact (proj1 (Forall_forall _ _) WFL ch INC)|]. split; [exact (proj1 (Forall_forall _ _) REPL ch INC)|].
  intros sc Hsc HQ. destruct INV as (_ & _ & RS & _). destruct RS as (SWF & _). pose proof (sec_nodup _ SWF) as ND.
  eapply Permutation_NoDup in ND; [| exact PSEC]. apply NoDup_app_disj_s with (x := sc) in ND; [| exact HQ].
  apply ND. apply in_flat_map. exists ch. split; [exact INC| exact Hsc].
Qed.

Definition trace_chk (tr : list Z) : bool :=
  match tr with
  | pc0 :: r :: ras => (length ras <=? 28)%nat && forallb (fun x => negb (x =? pc0)) ras && (4096 <=? r) && negb (r =? pc0)
                       && forallb (fun x => (0 <=? x) && (x <? 2^64)) ras
  | [_] => true
  | _ => false
  end.
#[using="Type"] Lemma traces_chk : forall tr, In tr A0_TRACES -> trace_chk tr = true.
Proof. intros tr Hin. assert (FB : forallb trace_chk A0_TRACES = true) by (vm_compute; reflexivity). rewrite forallb_forall in FB. exact (FB tr Hin). Qed.
#[using="Type"] Lemma traces_ok : forall pc0 r ras, In (pc0 :: r :: ras) A0_TRACES ->
  (length ras <= 28)%nat /\ Forall (fun x => x <> pc0) ras /\ 4096 <= r /\ r <> pc0 /\ Forall (fun x => 0 <= x < 2^64) ras.
Proof.
  intros pc0 r ras Hin. pose proof (traces_chk _ Hin) as C. cbn [trace_chk] in C.
  apply andb_true_iff in C as [C C5]. apply andb_true_iff in C as [C C4]. apply andb_true_iff in C as [C C3]. apply andb_true_iff in C as [C1 C2].
  split; [apply Nat.leb_le; exact C1|].
  split. { apply Forall_forall. intros x Hx. rewrite forallb_forall in C2. specialize (C2 x Hx). apply negb_true_iff, Z.eqb_neq in C2. exact C2. }
  split; [apply Z.leb_le; exact C3|]. split; [apply negb_true_iff, Z.eqb_neq in C4; exact C4|].
  apply Forall_forall. intros x Hx. rewrite forallb_forall in C5. specialize (C5 x Hx). apply andb_true_iff in C5 as [A1 A2]. apply Z.leb_le in A1. apply Z.ltb_lt in A2. lia.
Qed.

#[using="Type"] Lemma depot_room : forall hs0 hs total (tr : list Z), depot_ok hs0 hs total -> (length tr <= 30)%nat -> 65536 <= SWIN D ->
  16 * (zlen hs + 2) <= 2^20 /\ 8 * (total + Z.of_nat (length tr) + 1) <= SWIN D /\ total + Z.of_nat (length tr) + 1 < 2^20.
Proof.
  intros hs0 hs total tr (ND & INC & TB & LH0) LT SW.
  assert (LH : (length hs <= 32)%nat).
  { pose proof (NoDup_incl_length ND INC) as LL. rewrite length_app, length_map, A0_TRACES_length in LL. lia. }
  unfold zlen in *. lia.
Qed.

Hypothesis SWIN_LO : 65536 <= SWIN D.

#[using="Type"] Lemma qbytes_len : forall l, Forall qbatch_wf l -> Z.of_nat (length l) * Q_BBYTES <= qbytes l.
Proof.
  induction l as [|b l IH]; intros FW; [cbn; lia|]. apply Forall_cons_iff in FW as [WB FW]. specialize (IH FW).
  cbn [length qbytes fold_right]. fold (qbytes l). destruct WB as (_ & _ & _ & SZ & FC).
  assert (S0 : 0 <= fold_right (fun ch acc => qc_n ch + acc) 0 (qb_chunks b)).
  { clear - FC. induction (qb_chunks b) as [|c r IHr]; [cbn; lia|]. apply Forall_cons_iff in FC as [(_ & _ & N1 & _) FR]. specialize (IHr FR). cbn [fold_right]. lia. }
  rewrite Nat2Z.inj_succ. lia.
Qed.

#[using="SWIN_LO"] Lemma free_walk : forall (gp s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (q lo : Z)
    (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) s LB (m : mem) k A n ras,
  RHEAP_B AL E s LB m -> mclean (bs_H s) m -> mem_inv asegs m -> In (k, A, n) LB ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 4096 -> q mod 16 = 0 -> q + 16 < at_top L ->
  fpchain m (at_top L) q (bv_unsigned s0) ras -> In (PC0_FREE :: bv_unsigned ra :: ras) A0_TRACES ->
  exists ch l1 l2, bs_live s = l1 ++ (ch, n) :: l2 /\ A = qc_hdr AL ch + 16 /\ k = A /\
    let X := bs_X s in let glob := q_glob (bs_quar s) in let loc := q_loc (bs_quar s) in
    let hrest := flat_map prim_of (map fst (l1 ++ l2)) in
    implA (bs_H s) (ebind (t_enq AL (fst X) loc) (fun _ => t_dorecycle AL (fst (enq_prim (fst X) loc), snd X) (put_todo (fst X) glob loc ch)))
      (ficpt_post AL E gp s6 s7 s8 s9 s10 s11 F_ fc q lo 262144 262728 ra s0 s1 s2 s3 s4 s5 X (bs_H s) m glob loc ch hrest (bs_depot s) (bs_dtotal s) (free_tr ra ras))
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz free_icpt_entry) fc None m (seg_rom asegs)).
Proof.
  intros gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 s LB m k A n ras HR MC MI HIN ST CLO LOQ Q16 QTOP CH TRIN.
  destruct (free_pre s LB m k A n HR MI HIN) as (ch & l1 & l2 & EL & EA & EK & INV & HK & WFC & LREP & NSC).
  exists ch, l1, l2. split; [exact EL|]. split; [exact EA|]. split; [exact EK|]. cbv zeta. subst A.
  pose proof (rheap_stats AL E s LB m HR) as (CA0 & CM0 & CM1). pose proof (rheap_refill_budget AL E s LB m HR K_BCLASS ltac:(lia)) as RB24.
  destruct HR as (PLB & LOK & AO & _ & QLG & GC & QCL & MTX & (CST & AFM) & (FWF & QBL & QBG) & RD & DOK & _ & _ & _ & _ & _ & TE2 & HKE & TRE & AENV & (inited & IA) & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  destruct (traces_ok _ _ _ TRIN) as (LRAS & NPC & RA4 & RANE & RNG).
  pose proof INV as (RP & _). destruct (clear_ctx AL (bs_X s) m RP ltac:(destruct INV as (_ & _ & RS & _); exact RS)) as (WF0 & _).
  assert (FWF' : Forall qbatch_wf (q_glob (bs_quar s) ++ q_loc (bs_quar s))) by (eapply Permutation_Forall; [apply Permutation_app_comm| exact FWF]).
  assert (LTR : (length (free_tr ra ras) <= 30)%nat) by (unfold free_tr; cbn [length]; lia).
  destruct (depot_room _ _ _ (free_tr ra ras) DOK LTR SWIN_LO) as (RN & RF & RT).
  eapply (free_icpt_spec AL E AO gp s6 s7 s8 s9 s10 s11 F_ fc q lo ltac:(lia) CLO ltac:(unfold FICPT_STACK; exact LOQ) QTOP Q16 262144 262728 eq_refl eq_refl
            ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 (bs_X s) (bs_H s) m (q_glob (bs_quar s)) (q_loc (bs_quar s)) ch _ (bs_dtotal s) (bs_depot s) ras inited);
    [ exact MC | exact ST | exact INV | exact HK | exact WFC | exact LREP | exact NSC | exact QLG | exact GC | exact QCL | exact MTX | exact CST | exact AFM | exact FWF'
    | rewrite qbytes_app; lia
    | exact RB24
    | exact CA0 | exact CM0 | exact CM1
    | apply Forall_app in FWF as [FWL _]; pose proof (qbytes_len _ FWL) as QL; lia
    | exact TE2 | exact HKE | exact TRE | exact IA | exact RD | exact CH | exact LRAS | exact NPC | exact RA4 | exact RANE | exact RNG | exact RN | exact RF | exact RT ].
Qed.

#[using="Type"] Lemma filter_perm : forall {T} (f : T -> bool) l l', Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
  intros T f l l' PM. induction PM as [|x l l' PM IH|x y l|l l' l'' P1 I1 P2 I2]; cbn [List.filter].
  - constructor.
  - destruct (f x); [apply perm_skip|]; exact IH.
  - destruct (f x), (f y); try apply Permutation_refl. apply perm_swap.
  - exact (Permutation_trans I1 I2).
Qed.
#[using="Type"] Lemma filter_all : forall {T} (f : T -> bool) l, (forall x, In x l -> f x = true) -> List.filter f l = l.
Proof. intros T f l. induction l as [|x l IH]; intros HA; [reflexivity|]. cbn [List.filter]. rewrite (HA x (or_introl eq_refl)), IH; [reflexivity|]. intros y Hy. apply HA. right. exact Hy. Qed.

#[using="Type"] Lemma lb_remove_filter : forall (p : Z) (LB : list (block Z)), lb_remove Z.eqb p LB = List.filter (fun b => negb (Z.eqb (blk_id b) p)) LB.
Proof.
  intros p LB. unfold lb_remove. induction LB as [|b l IH]; [reflexivity|]. rewrite list_basics.list.filter_cons. cbn [List.filter].
  match goal with |- context [decide ?P] => destruct (decide P) as [D|D] end; destruct (negb (blk_id b =? p)) eqn:EN; cbn in D; try contradiction; try (exfalso; apply D; exact I).
  - rewrite IH. reflexivity.
  - exact IH.
Qed.

#[using="Type"] Lemma lbrest_perm : forall (LB : list (block Z)) l1 r l2, Permutation LB (map (blk_ofB AL) (l1 ++ r :: l2)) -> List.NoDup (map (@blk_id Z) LB) ->
  Permutation (lb_remove Z.eqb (lc_user AL (fst r)) LB) (map (blk_ofB AL) (l1 ++ l2)).
Proof.
  intros LB l1 r l2 PM ND. rewrite lb_remove_filter.
  eapply Permutation_trans; [apply filter_perm; exact PM|].
  assert (ND' : List.NoDup (map (@blk_id Z) (map (blk_ofB AL) (l1 ++ r :: l2)))) by (eapply Permutation_NoDup; [apply Permutation_map; exact PM| exact ND]).
  rewrite !map_app in *. cbn [map] in *. rewrite List.filter_app. cbn [List.filter].
  assert (IDR : blk_id (blk_ofB AL r) = lc_user AL (fst r)) by reflexivity. rewrite IDR, Z.eqb_refl. cbn [negb].
  apply NoDup_remove_2 in ND'. rewrite IDR in ND'.
  rewrite !filter_all; [apply Permutation_refl| |].
  - intros x Hx. apply negb_true_iff, Z.eqb_neq. intros EQ. apply ND'. apply in_or_app. right. rewrite <- EQ. apply in_map. exact Hx.
  - intros x Hx. apply negb_true_iff, Z.eqb_neq. intros EQ. apply ND'. apply in_or_app. left. rewrite <- EQ. apply in_map. exact Hx.
Qed.

#[using="Type"] Lemma lbrest_desc : forall (LB : list (block Z)) l1 r l2, Permutation LB (map (blk_ofB AL) (l1 ++ r :: l2)) -> List.NoDup (map (@blk_id Z) LB) ->
  forall b, In b (lb_remove Z.eqb (lc_user AL (fst r)) LB) -> exists r', In r' (l1 ++ l2) /\ blk_addr b = lc_user AL (fst r') /\ blk_size b = snd r'.
Proof.
  intros LB l1 r l2 PM ND b Hb. pose proof (Permutation_in _ (lbrest_perm LB l1 r l2 PM ND) Hb) as Hb'.
  apply in_map_iff in Hb' as (r' & <- & Hr'). exists r'. split; [exact Hr'|]. split; reflexivity.
Qed.

#[using="Type"] Lemma live_rest_facts : forall s LB (m : mem) ch n l1 l2, RHEAP_B AL E s LB m -> mem_inv asegs m -> bs_live s = l1 ++ (ch, n) :: l2 ->
  forall r, In r (l1 ++ l2) ->
    lr_ok r /\ held_kind (bs_X s) (fst r) /\ qchunk_wf (fst r)
    /\ (forall cv, In cv (prim_of (fst r)) -> ~ In cv (tc_of (bs_gl s) ++ prim_of ch))
    /\ (forall sc, In sc (sec_of (fst r)) -> ~ In sc (tsc_of (bs_gl s) ++ sec_of ch))
    /\ (forall cv, In cv (prim_of (fst r)) -> In cv (flat_map prim_of (map fst (l1 ++ l2)))).
Proof.
  intros s LB m ch n l1 l2 HR MI EL r Hr. pose proof (rheap_held AL E s LB m HR) as [NDH _].
  destruct HR as (_ & LOK & _ & INVB & _ & _ & _ & _ & _ & _ & _ & _ & WFL & _ & HKL & PSEC & _).
  destruct INVB as (_ & _ & RS & _). destruct RS as (SWF & _). pose proof (sec_nodup _ SWF) as NDS. eapply Permutation_NoDup in NDS; [| exact PSEC].
  assert (INL : In r (bs_live s)) by (rewrite EL; apply in_app_or in Hr as [Hr|Hr]; apply in_or_app; [left| right; right]; exact Hr).
  assert (INC : In (fst r) (live_chunks s)) by (unfold live_chunks; apply in_map; exact INL).
  split; [exact (proj1 (Forall_forall _ _) LOK r INL)|]. split; [exact (proj1 (Forall_forall _ _) HKL _ INC)|]. split; [exact (proj1 (Forall_forall _ _) WFL _ INC)|].
  assert (INH : forall cv, In cv (prim_of (fst r)) -> In cv (flat_map prim_of (map fst (l1 ++ l2)))).
  { intros cv Hcv. apply in_flat_map. exists (fst r). split; [apply in_map; exact Hr| exact Hcv]. }
  assert (INS : forall sc, In sc (sec_of (fst r)) -> In sc (flat_map sec_of (map fst (l1 ++ l2)))).
  { intros sc Hsc. apply in_flat_map. exists (fst r). split; [apply in_map; exact Hr| exact Hsc]. }
  split; [| split; [| exact INH]].
  - intros cv Hcv HIN. specialize (INH cv Hcv).
    assert (PMH : Permutation (allheld s) ((tc_of (bs_gl s) ++ prim_of ch) ++ flat_map prim_of (map fst (l1 ++ l2)))).
    { unfold allheld, heldB, live_chunks. rewrite EL, !map_app, !flat_map_app. cbn [map flat_map fst]. rewrite <- !app_assoc.
      apply Permutation_app_head. apply Permutation_app_swap_app. }
    eapply Permutation_NoDup in NDH; [| exact PMH]. exact (NoDup_app_disj _ _ cv NDH HIN INH).
  - intros sc Hsc HIN. specialize (INS sc Hsc).
    assert (PMS : Permutation (flat_map sec_of (flat_map qb_chunks (bs_gl s)) ++ flat_map sec_of (live_chunks s))
                              ((tsc_of (bs_gl s) ++ sec_of ch) ++ flat_map sec_of (map fst (l1 ++ l2)))).
    { unfold tsc_of, live_chunks. rewrite EL, !map_app, !flat_map_app. cbn [map flat_map fst]. rewrite <- !app_assoc.
      apply Permutation_app_head. apply Permutation_app_swap_app. }
    eapply Permutation_NoDup in NDS; [| exact PMS]. exact (NoDup_app_disj _ _ sc NDS HIN INS).
Qed.

#[using="Type"] Lemma depot_ok_step : forall hs0 hs total (tr : list Z) hs' total', depot_ok hs0 hs total -> In tr A0_TRACES -> (length tr <= 30)%nat ->
  ((dfind hs (depot_hash tr) <> 0 /\ hs' = hs /\ total' = total)
   \/ (dfind hs (depot_hash tr) = 0 /\ hs' = hs ++ [depot_hash tr] /\ total' = total + Z.of_nat (length tr) + 1)) ->
  depot_ok hs0 hs' total'.
Proof.
  intros hs0 hs total tr hs' total' (ND & INC & TB & LH0) TIN LT [(_ & -> & ->)|(DF & -> & ->)]; [split; [exact ND| split; [exact INC| split; [exact TB| exact LH0]]]|].
  split; [| split; [| split; [| exact LH0]]].
  - eapply Permutation_NoDup; [apply Permutation_cons_append|]. constructor; [| exact ND]. intros HIN. exact (dfind_complete hs _ HIN DF).
  - intros x Hx. apply in_app_or in Hx as [Hx|[<-|[]]]; [exact (INC x Hx)| apply in_or_app; right; apply in_map; exact TIN].
  - unfold zlen in *. rewrite length_app. cbn [length]. lia.
Qed.

#[using="Type"] Lemma free_pre_at : forall s LB (m : mem) ch n l1 l2,
  RHEAP_B AL E s LB m -> mem_inv asegs m -> bs_live s = l1 ++ (ch, n) :: l2 ->
  dr_inv AL E (bs_X s) (bs_H s) m (bs_gl s) (flat_map qb_chunks (bs_gl s)) (prim_of ch ++ flat_map prim_of (map fst (l1 ++ l2)))
  /\ held_kind (bs_X s) ch /\ qchunk_wf ch /\ lchunk_rep AL m ch
  /\ (forall sc, In sc (sec_of ch) -> ~ In sc (flat_map sec_of (flat_map qb_chunks (bs_gl s))))
  /\ In (lc_user AL ch, lc_user AL ch, n) LB.
Proof.
  intros s LB m ch n l1 l2 (PLB & LOK & AO & INVB & QLG & GC & QCL & MTX & QE & QWF & RD & DOK & WFL & REPL & HKL & PSEC & COV & REST) MI EL.
  pose proof (dr_inv_of_B AL E _ _ _ _ _ _ INVB MI) as INV.
  assert (INC : In ch (live_chunks s)) by (unfold live_chunks; rewrite EL, map_app; apply in_or_app; right; left; reflexivity).
  split.
  { eapply dr_inv_hrest_perm; [| exact INV]. unfold heldB, live_chunks. rewrite EL, !map_app, !flat_map_app. cbn [map flat_map fst].
    apply Permutation_app_swap_app. }
  split; [exact (proj1 (Forall_forall _ _) HKL ch INC)|]. split; [exact (proj1 (Forall_forall _ _) WFL ch INC)|]. split; [exact (proj1 (Forall_forall _ _) REPL ch INC)|].
  split.
  { intros sc Hsc HQ. destruct INV as (_ & _ & RS & _). destruct RS as (SWF & _). pose proof (sec_nodup _ SWF) as ND.
    eapply Permutation_NoDup in ND; [| exact PSEC]. apply NoDup_app_disj_s with (x := sc) in ND; [| exact HQ].
    apply ND. apply in_flat_map. exists ch. split; [exact INC| exact Hsc]. }
  eapply Permutation_in; [apply Permutation_sym; exact PLB|]. rewrite EL, map_app. apply in_or_app. right. left. reflexivity.
Qed.

#[using="Type"] Lemma allheld_split : forall s ch n l1 l2, bs_live s = l1 ++ (ch, n) :: l2 ->
  Permutation (allheld s) (tc_of (bs_gl s) ++ prim_of ch ++ flat_map prim_of (map fst (l1 ++ l2)))
  /\ Permutation (flat_map sec_of (flat_map qb_chunks (bs_gl s)) ++ flat_map sec_of (live_chunks s))
                 (tsc_of (bs_gl s) ++ sec_of ch ++ flat_map sec_of (map fst (l1 ++ l2))).
Proof.
  intros s ch n l1 l2 EL. unfold allheld, heldB, tsc_of, live_chunks. rewrite EL, !map_app, !flat_map_app. cbn [map flat_map fst]. split.
  - apply Permutation_app_head. apply Permutation_app_swap_app.
  - apply Permutation_app_head. apply Permutation_app_swap_app.
Qed.

#[using="Type"] Lemma Forall_live_rest : forall (Pr : qchunk -> Prop) (l1 l2 : list (qchunk * Z)) x, Forall Pr (map fst (l1 ++ x :: l2)) -> Forall Pr (map fst (l1 ++ l2)).
Proof. intros Pr l1 l2 x FA. rewrite map_app in *. cbn [map] in FA. apply Forall_app in FA as [F1 F2]. apply Forall_cons_iff in F2 as [_ F2]. apply Forall_app. split; assumption. Qed.

#[using="Type"] Lemma cls_cnt_rest : forall c (l1 l2 : list (qchunk * Z)) x, cls_cnt c (map fst (l1 ++ l2)) <= cls_cnt c (map fst (l1 ++ x :: l2)).
Proof.
  intros c l1 l2 x. rewrite !map_app. cbn [map]. change (fst x :: map fst l2) with ([fst x] ++ map fst l2). rewrite !cls_cnt_app.
  pose proof (cls_cnt_nonneg c [fst x]). lia.
Qed.

#[using="Type"] Lemma pinv_put_mid : forall P S glob loc ch hrest secs,
  pinv AL (P, S) (tc_of (glob ++ loc) ++ prim_of ch ++ hrest) (tsc_of (glob ++ loc) ++ sec_of ch ++ secs) ->
  pclass_wf K_BCLASS (get_cls P K_BCLASS) -> (p_cnt (get_cls P K_BCLASS) = 0 -> refill_budget K_BCLASS (get_cls P K_BCLASS)) ->
  pinv AL (fst (enq_prim P loc), S)
       (map bpair (put_todo P glob loc ch) ++ flat_map prim_of (flat_map qb_chunks (put_todo P glob loc ch)) ++ (tc_of (put_glob P glob loc ch ++ put_loc P loc ch) ++ hrest))
       (flat_map sec_of (flat_map qb_chunks (put_todo P glob loc ch)) ++ (tsc_of (put_glob P glob loc ch ++ put_loc P loc ch) ++ secs)).
Proof.
  intros P S glob loc ch hrest secs PI WF BUD. pose proof (pinv_enq AL P S loc _ _ PI WF BUD) as P1.
  destruct (put_books P glob loc ch) as [B1 B2]. cbv zeta in B1.
  eapply pinv_perm; [| | exact P1].
  - pose proof (Permutation_app_tail hrest (Permutation_sym B1)) as B1'. unfold tc_of at 2 in B1'. rewrite <- !app_assoc in B1'. exact B1'.
  - pose proof (Permutation_app_tail secs (Permutation_sym B2)) as B2'. unfold tsc_of at 2 in B2'. rewrite <- !app_assoc in B2'. exact B2'.
Qed.

#[using="Type"] Lemma free_budget : forall s LB (m : mem) ch n l1 l2 H' hs' total',
  RHEAP_B AL E s LB m -> bs_live s = l1 ++ (ch, n) :: l2 ->
  let P := bs_prim s in let glob := q_glob (bs_quar s) in let loc := q_loc (bs_quar s) in
  let X' := dorecycle (fst (enq_prim P loc), bs_sec s) (put_todo P glob loc ch) in
  let s' := mkASB H' (bs_pages s) (fst X') (snd X') (mkAQ (put_loc P loc ch) (put_glob P glob loc ch)) hs' total' (bs_nsec s) (l1 ++ l2) (bs_depot0 s) in
  pinv AL X' (allheld s') (flat_map sec_of (flat_map qb_chunks (bs_gl s')) ++ flat_map sec_of (live_chunks s')) /\ budget_ok s'.
Proof.
  intros s LB m ch n l1 l2 H' hs' total' HR EL. cbv zeta.
  set (P := bs_prim s). set (glob := q_glob (bs_quar s)). set (loc := q_loc (bs_quar s)).
  set (hrest := flat_map prim_of (map fst (l1 ++ l2))). set (secsR := flat_map sec_of (map fst (l1 ++ l2))).
  pose proof (rheap_pinv AL E s LB m HR) as PI0. destruct (allheld_split s ch n l1 l2 EL) as [PH PS].
  pose proof (pinv_perm AL _ _ _ _ _ PH PS PI0) as PIa. clear PI0 PH PS.
  change (bs_gl s) with (glob ++ loc) in PIa. change (bs_X s) with (P, bs_sec s) in PIa. fold hrest secsR in PIa.
  pose proof (rheap_wf AL E s LB m HR K_BCLASS ltac:(lia)) as WF24. fold P in WF24.
  assert (BUD24 : p_cnt (get_cls P K_BCLASS) = 0 -> refill_budget K_BCLASS (get_cls P K_BCLASS)) by (intros _; exact (rheap_refill_budget AL E s LB m HR K_BCLASS ltac:(lia))).
  pose proof (pinv_put AL P (bs_sec s) glob loc ch hrest secsR PIa WF24 BUD24) as PI1.
  pose proof (pinv_put_mid P (bs_sec s) glob loc ch hrest secsR PIa WF24 BUD24) as PIm.
  pose proof (dorecycle_same_mu AL _ _ _ _ PIm) as [MU1 CM1]. cbn [fst] in MU1, CM1.
  pose proof PIa as (LEN & _). cbn [fst] in LEN. destruct (enq_mu P loc LEN) as (EO & E24 & ECM). cbv zeta in EO, E24, ECM.
  set (X' := dorecycle (fst (enq_prim P loc), bs_sec s) (put_todo P glob loc ch)) in *.
  split; [exact PI1|].
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (BMU & BLV & _ & CMP & SC0 & SB0 & NS0) & _).
  unfold budget_ok. cbn [bs_prim bs_live bs_quar]. unfold live_chunks. cbn [bs_live].
  assert (MU24 : p_mu (get_cls (fst (enq_prim P loc)) K_BCLASS) <= PM K_BCLASS).
  { rewrite E24. unfold enq_refills. destruct (need_batch loc); cbn [andb]; [| exact (BMU K_BCLASS ltac:(lia))].
    destruct (Z.eqb_spec (p_cnt (get_cls P K_BCLASS)) 0) as [C0|CN]; [| exact (BMU K_BCLASS ltac:(lia))].
    exact (rheap_refill_mu AL E s LB m HR K_BCLASS ltac:(lia) C0). }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - intros c Hc. rewrite (MU1 c Hc). destruct (Z.eq_dec c K_BCLASS) as [->|NE]; [exact MU24|]. rewrite (EO c Hc NE). exact (BMU c Hc).
  - intros c Hc. pose proof (cls_cnt_rest c l1 l2 (ch, n)) as CR. specialize (BLV c Hc). unfold live_chunks in BLV. rewrite EL in BLV.
    destruct (MH_facts c Hc) as (_ & _ & CS). pose proof (cls_cnt_nonneg c (map fst (l1 ++ l2))) as C0. clear - CR BLV CS C0. nia.
  - destruct PI1 as (_ & _ & _ & CAL & _). exact CAL.
  - rewrite CM1, ECM, (sum_mu_ext _ _ MU1).
    rewrite (sum_mu_upd P (fst (enq_prim P loc)) K_BCLASS (p_mu (get_cls (fst (enq_prim P loc)) K_BCLASS) - p_mu (get_cls P K_BCLASS)) ltac:(lia)
               ltac:(intros c' Hc' NE; rewrite (EO c' Hc' NE); reflexivity) ltac:(lia)).
    fold P in CMP. rewrite CMP. reflexivity.
  - pose proof HR as (_ & LOK & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WFL & _). unfold live_chunks in WFL. rewrite EL in LOK, WFL.
    pose proof (proj1 (Forall_forall _ _) LOK (ch, n) ltac:(apply in_or_app; right; left; reflexivity)) as LR1.
    pose proof (proj1 (Forall_forall _ _) WFL ch ltac:(rewrite map_app; apply in_or_app; right; left; reflexivity)) as WF1.
    destruct (sec_measures_rest l1 l2 (ch, n) LR1 WF1) as [M1 _]. unfold sec_live_cnt, live_chunks in SC0 |- *. cbn [bs_live]. rewrite EL in SC0. lia.
  - pose proof HR as (_ & LOK & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WFL & _). unfold live_chunks in WFL. rewrite EL in LOK, WFL.
    pose proof (proj1 (Forall_forall _ _) LOK (ch, n) ltac:(apply in_or_app; right; left; reflexivity)) as LR1.
    pose proof (proj1 (Forall_forall _ _) WFL ch ltac:(rewrite map_app; apply in_or_app; right; left; reflexivity)) as WF1.
    destruct (sec_measures_rest l1 l2 (ch, n) LR1 WF1) as [_ M2]. unfold sec_live_bytes in SB0 |- *. cbn [bs_live]. rewrite EL in SB0. lia.
  - cbn [bs_nsec]. exact NS0.
Qed.

Section CONV.
Variable FI : fs_if.
Variable AI : am_if FI.
Hypothesis FSBE : FSB FI = al_fsb AL.
Hypothesis STAT : forall lo' hi', am_static FI AI lo' hi' -> a0_static lo' hi'.

#[using="Type"] Lemma traces_rng : forall tr, In tr A0_TRACES -> (1 <= length tr <= 30)%nat /\ Forall (fun x => 0 <= x < 2^64) tr.
Proof.
  intros tr Hin.
  assert (FB : forallb (fun t => (1 <=? length t)%nat && (length t <=? 30)%nat && forallb (fun x => (0 <=? x) && (x <? 2^64)) t) A0_TRACES = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in FB. specialize (FB tr Hin). apply andb_true_iff in FB as [FB F3]. apply andb_true_iff in FB as [F1 F2].
  apply Nat.leb_le in F1, F2. split; [lia|]. apply Forall_forall. intros x Hx. rewrite forallb_forall in F3. specialize (F3 x Hx).
  apply andb_true_iff in F3 as [A1 A2]. apply Z.leb_le in A1. apply Z.ltb_lt in A2. lia.
Qed.

#[using="FSBE STAT"] Lemma free_post_core : forall (q lo : Z) s LB (m : mem) ch n l1 l2 (tr : list Z) (st : fsstate FI) H' (m' : mem) W hs' total',
  RHEAP_B AL E s LB m -> mem_inv asegs m -> asan_env asegs m -> RFAKE FI st m ->
  bs_live s = l1 ++ (ch, n) :: l2 -> List.NoDup (map (@blk_id Z) LB) ->
  alloc_ceiling <= lo -> lo <= q -> In tr A0_TRACES ->
  let X := bs_X s in let glob := q_glob (bs_quar s) in let loc := q_loc (bs_quar s) in
  let hrest := flat_map prim_of (map fst (l1 ++ l2)) in
  let P := fst X in let X1 := (fst (enq_prim P loc), snd X) in
  let todo := put_todo P glob loc ch in let gF := put_glob P glob loc ch in let lF := put_loc P loc ch in
  munch ((QUAR_MTX, QUAR_MTX + 4) :: (QUAR_GQ, QUAR_GQ + 32) :: (at_thr (al_thread AL) + TQ_OFF, at_thr (al_thread AL) + TQ_OFF + 32) :: W) m m' ->
  Forall (ftouch AL q lo X glob loc ch) W ->
  dr_inv AL E (dorecycle X1 todo) H' m' (gF ++ lF) (flat_map qb_chunks (gF ++ lF)) hrest ->
  qlist_rep AL m' gF 0 -> rw_cells asegs m' QUAR_GQ (qcells AL gF) -> qcache_rep AL m' (at_thr (al_thread AL) + TQ_OFF) lF ->
  rw_cells asegs m' QUAR_MTX [CB 4 [b8 0; b8 0; b8 0; b8 0]] ->
  (need_batch loc = true -> 0 <= snd (enq_prim P loc) /\ 16 * snd (enq_prim P loc) + Q_BBYTES <= FA_OFF) ->
  (need_batch loc = true -> held_ok (fst (enq_prim P loc)) ((K_BCLASS, snd (enq_prim P loc)) :: prim_of ch ++ hrest)
                               /\ (forall c, 1 <= c <= 31 -> pclass_wf c (get_cls (fst (enq_prim P loc)) c))) ->
  RDEPOT D hs' total' m' -> (exists inited, ia_cells 262144 262728 inited m') ->
  ((dfind (bs_depot s) (depot_hash tr) <> 0 /\ hs' = bs_depot s /\ total' = bs_dtotal s)
   \/ (dfind (bs_depot s) (depot_hash tr) = 0 /\ hs' = bs_depot s ++ [depot_hash tr] /\ total' = bs_dtotal s + Z.of_nat (length tr) + 1)) ->
  let s' := mkASB H' (bs_pages s) (fst (dorecycle X1 todo)) (snd (dorecycle X1 todo)) (mkAQ lF gF) hs' total' (bs_nsec s) (l1 ++ l2) (bs_depot0 s) in
  mem_inv asegs m' /\ asan_env asegs m' /\ RFAKE FI st m'
  /\ (forall LBk : list (block (am_K FI AI)),
        (forall b, In b LBk -> exists r, In r (l1 ++ l2) /\ blk_addr b = lc_user AL (fst r) /\ blk_size b = snd r) -> apres FI AI LBk q m m')
  /\ (forall r B cs, In r (l1 ++ l2) -> qc_blk AL (fst r) <= B -> B + Z.of_nat (cells_size cs) <= qc_blk AL (fst r) + qc_bsize (fst r) ->
                     rw_cells asegs m B cs -> rw_cells asegs m' B cs)
  /\ RHEAP_B AL E s' (lb_remove Z.eqb (lc_user AL ch) LB) m'.
Proof.
  intros q lo s LB m ch n l1 l2 tr st H' m' W hs' total' HR MI AE RF EL NDK CLO LQ TRIN X glob loc hrest P X1 todo gFx lFx MU FW INV' QLG' GC' QCL' MTX' VNG NBX RD' IA' DEP s'.
  subst s'. unfold gFx, lFx, todo, X1, P, hrest in *. clear gFx lFx todo X1 P hrest. unfold X, glob, loc in *. clear X glob loc.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (LOH : 0x10007fff8000 <= lo) by (clear - ACR CLO; lia).
  destruct (free_pre_at s LB m ch n l1 l2 HR MI EL) as (INV & HK & WFC & LREP & NSC & HINB).
  pose proof (live_rest_facts s LB m ch n l1 l2 HR MI EL) as LRF.
  set (X := bs_X s) in *. set (glob := q_glob (bs_quar s)) in *. set (loc := q_loc (bs_quar s)) in *.
  set (hrest := flat_map prim_of (map fst (l1 ++ l2))) in *.
  change (bs_gl s) with (glob ++ loc) in *.
  pose proof INV as (RP & _ & RS & _ & _ & _ & _ & _ & _ & _ & HOK & _).
  assert (TCH : Forall (held1 (fst X)) (tc_of (glob ++ loc) ++ prim_of ch)).
  { destruct HOK as [_ FH]. unfold tc_of. rewrite <- app_assoc. rewrite !app_assoc in FH. apply Forall_app in FH as [FH _]. rewrite <- !app_assoc in FH. exact FH. }
  assert (TSI : incl (tsc_of (glob ++ loc) ++ sec_of ch) (se_chunks (snd X))).
  { destruct (dr_inv_tc AL E X (bs_H s) m (glob ++ loc) (flat_map qb_chunks (glob ++ loc)) [] (prim_of ch ++ hrest) ltac:(rewrite app_nil_r; exact INV)) as [_ TSI0].
    apply incl_app; [exact TSI0|]. destruct ch as [[c v|sc] rz0 n0]; cbn [sec_of qc_kind]; intros d Hd; [destruct Hd|]. destruct Hd as [<-|[]]. exact HK. }
  destruct (dr_invB_of AL E _ _ _ _ _ _ INV') as [INVB' MI'].
  pose proof HR as (PLB & LOK & AO & _ & _ & _ & _ & _ & QE & (FWF & QBL & QBG) & _ & DOK & WFL & _ & _ & _ & _ & TE2 & HKE & TRE & AENV & _ & CCL & CCQ & SLK & _ & FTE).
  destruct (free_cells AL AO lo q X m m' glob loc ch W LOH CLO RP RS TCH TSI VNG MU FW TE2 HKE TRE QE) as (TE2' & HKE' & TRE' & QE').
  destruct (free_budget s LB m ch n l1 l2 H' hs' total' HR EL) as [PI1 BUD']. cbv zeta in PI1, BUD'. fold glob loc in PI1, BUD'.
  set (X' := dorecycle (fst (enq_prim (bs_prim s) loc), bs_sec s) (put_todo (bs_prim s) glob loc ch)) in *.
  set (gF := put_glob (bs_prim s) glob loc ch) in *. set (lF := put_loc (bs_prim s) loc ch) in *.
  split; [exact MI'|].
  split; [exact (free_asan_env AL AO lo q X m m' glob loc ch W LOH RP RS TCH TSI VNG MU FW AE)|].
  split; [exact (free_rfake AL AO FI FSBE lo q X m m' glob loc ch W LOH CLO RP RS TCH TSI VNG MU FW st RF)|].
  split; [intros LBk HB; exact (free_apres AL AO FI AI FSBE STAT lo q X m m' glob loc ch hrest W LOH CLO LQ RP RS TCH TSI VNG NBX MU FW (l1 ++ l2) LBk HB LRF)|].
  split.
  { intros r0 B cs Hr HB1 HB2 CS. destruct (LRF r0 Hr) as (_ & HK' & _ & NP & NS & INH).
    eapply rw_cells_transport_m; [exact CS| exact MU|].
    eapply disjoint_from_sub; [exact (hull_W_dj AL AO lo q X m glob loc ch hrest W LOH CLO RP RS TCH TSI VNG NBX FW (fst r0) _ _ HK' NP NS INH ltac:(left; split; reflexivity))| exact HB1| exact HB2]. }

  unfold RHEAP_B. cbv zeta. unfold bs_X, bs_gl, live_chunks, heldB. cbn [bs_H bs_prim bs_sec bs_quar bs_depot bs_dtotal bs_live bs_depot0 q_glob q_loc].
  split; [rewrite EL in PLB; exact (lbrest_perm LB l1 (ch, n) l2 PLB NDK)|].
  split; [rewrite EL in LOK; apply Forall_app in LOK as [L1 L2]; apply Forall_cons_iff in L2 as [_ L2]; apply Forall_app; split; assumption|].
  split; [exact AO|]. split; [exact INVB'|]. split; [exact QLG'|]. split; [exact GC'|]. split; [exact QCL'|]. split; [exact MTX'|]. split; [exact QE'|].
  split.
  { apply (put_quar_wf (bs_prim s) glob loc ch FWF QBG WFC). intros NB. destruct (NBX NB) as [[_ FHN] _]. apply Forall_cons_iff in FHN as [(_ & V0 & _ & VM & _) _].
    cbn [fst snd] in V0, VM. change (class_size K_BCLASS) with 8192 in VM. split; assumption. }
  split; [exact RD'|].
  split. { apply (depot_ok_step _ _ _ tr hs' total' DOK TRIN); [| exact DEP]. destruct (traces_rng tr TRIN) as [LTR _]. lia. }
  unfold live_chunks in WFL, CCL, SLK. rewrite EL in WFL, CCL, SLK.
  split; [exact (Forall_live_rest _ l1 l2 (ch, n) WFL)|].
  split.
  { apply Forall_forall. intros ch' Hch'. apply in_map_iff in Hch' as (r & <- & Hr). destruct (LRF r Hr) as (_ & HK' & WF' & NP & NS & INH).
    assert (REPLx : Forall (lchunk_rep AL m) (live_chunks s)) by (destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & REPL & _); exact REPL).
    pose proof (proj1 (Forall_forall _ _) REPLx (fst r)
                  ltac:(unfold live_chunks; rewrite EL; apply in_map; apply in_app_or in Hr as [Hr|Hr]; apply in_or_app; [left| right; right]; exact Hr)) as R.
    exact (live_other_frame AL AO lo q X m m' glob loc ch hrest W (fst r) LOH CLO RP RS TCH TSI HK' WF' NP NS INH VNG NBX MU FW R). }
  pose proof INV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [_ FH'] & _).
  pose proof PI1 as (_ & _ & COV' & _ & _ & _ & PSEC').
  unfold allheld, bs_gl, heldB, live_chunks in COV', PSEC'. cbn [bs_quar bs_live q_glob q_loc] in COV', PSEC'. cbn [snd] in PSEC'.
  split.
  { apply Forall_forall. intros ch' Hch'. apply in_map_iff in Hch' as (r & <- & Hr). destruct (LRF r Hr) as (_ & _ & _ & _ & _ & INH).
    unfold held_kind. destruct (qc_kind (fst r)) as [c v|sc] eqn:EK.
    - apply (proj1 (Forall_forall _ _) FH'). apply in_or_app. right. apply in_or_app. right. apply INH. unfold prim_of. rewrite EK. left. reflexivity.
    - cbn [snd]. eapply Permutation_in; [apply Permutation_sym; exact PSEC'|]. apply in_or_app. right.
      apply in_flat_map. exists (fst r). split; [apply in_map; exact Hr| unfold sec_of; rewrite EK; left; reflexivity]. }
  split; [exact PSEC'|]. split; [exact COV'|]. split; [exact TE2'|]. split; [exact HKE'|]. split; [exact TRE'|].
  split; [exact (free_aenv AL AO lo q X m m' glob loc ch W LOH CLO RP RS TCH TSI VNG MU FW AENV)|]. split; [exact IA'|].
  split; [exact (Forall_live_rest _ l1 l2 (ch, n) CCL)|].
  split.
  { pose proof (put_chunks (bs_prim s) glob loc ch) as PC. fold gF lF in PC. apply Forall_forall. intros c0 Hc0.
    assert (IN0 : In c0 (flat_map qb_chunks (glob ++ loc) ++ [ch])) by (eapply Permutation_in; [exact PC|]; apply in_or_app; right; exact Hc0).
    apply in_app_or in IN0 as [IN0|[<-|[]]]; [exact (proj1 (Forall_forall _ _) CCQ c0 IN0)|].
    apply (proj1 (Forall_forall _ _) CCL). rewrite map_app. apply in_or_app. right. left. reflexivity. }
  split; [exact (Forall_live_rest _ l1 l2 (ch, n) SLK)|]. split; [exact BUD'|].
  exact (free_fte AL AO lo q X m m' glob loc ch W LOH CLO RP RS TCH TSI VNG MU FW FTE).
Qed.

#[using="FSBE STAT"] Lemma free_post_conv : forall (gp s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (q lo : Z) (ra s0 s1 s2 s3 s4 s5 : word)
    s LB (m : mem) ch n l1 l2 ras (st : fsstate FI) H' ms',
  RHEAP_B AL E s LB m -> mem_inv asegs m -> asan_env asegs m -> RFAKE FI st m ->
  bs_live s = l1 ++ (ch, n) :: l2 -> List.NoDup (map (@blk_id Z) LB) ->
  alloc_ceiling <= lo -> lo <= q -> In (free_tr ra ras) A0_TRACES ->
  ficpt_post AL E gp s6 s7 s8 s9 s10 s11 F_ fc q lo 262144 262728 ra s0 s1 s2 s3 s4 s5 (bs_X s) (bs_H s) m (q_glob (bs_quar s)) (q_loc (bs_quar s)) ch
             (flat_map prim_of (map fst (l1 ++ l2))) (bs_depot s) (bs_dtotal s) (free_tr ra ras) tt H' ms' ->
  exists s' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ bs_ghost s' = (H', bs_pages s) /\ bs_nsec s' = bs_nsec s
    /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m' /\ RFAKE FI st m'
    /\ (forall LBk : list (block (am_K FI AI)),
          (forall b, In b LBk -> exists r, In r (l1 ++ l2) /\ blk_addr b = lc_user AL (fst r) /\ blk_size b = snd r) -> apres FI AI LBk q m m')
    /\ RHEAP_B AL E s' (lb_remove Z.eqb (lc_user AL ch) LB) m'.
Proof.
  intros gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra s0 s1 s2 s3 s4 s5 s LB m ch n l1 l2 ras st H' ms' HR MI AE RF EL NDK CLO LQ TRIN POST.
  destruct POST as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & W & hs' & total' & POST). cbv zeta in POST.
  destruct POST as (EMS & EH & MU & FW & INV' & XLE & STK' & QLG' & GC' & QCL' & MTX' & VNG & NBX & RD' & IA' & DEP).
  pose proof (free_post_core q lo s LB m ch n l1 l2 (free_tr ra ras) st H' m' W hs' total' HR MI AE RF EL NDK CLO LQ TRIN) as CORE. cbv zeta in CORE.
  destruct (CORE MU FW INV' QLG' GC' QCL' MTX' VNG NBX RD' (ex_intro _ true IA') DEP) as (MI' & AE' & RF' & AP' & _ & HR').
  eexists; exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
  split; [exact EMS|]. split; [| split; [| split; [exact MI'| split; [exact STK'| split; [exact AE'| split; [exact RF'| split; [exact AP'| exact HR']]]]]]]; reflexivity.
Qed.

End CONV.

Section CONVN.
Variable FI : fs_if.
Variable AI : am_if FI.
Hypothesis FSBE : FSB FI = al_fsb AL.
Hypothesis STAT : forall lo' hi', am_static FI AI lo' hi' -> a0_static lo' hi'.

#[using="FSBE STAT"] Lemma apres_of_czone : forall (lo q : Z) (X : pstate) (m m' : mem) W (live' : list (qchunk * Z)) (LBk : list (block (am_K FI AI))),
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  munch W m m' -> Forall (czone AL lo q (snd X)) W ->
  (forall A k, q <= A -> disjoint_from W A k) ->
  (forall b, In b LBk -> exists r, In r live' /\ blk_addr b = lc_user AL (fst r) /\ blk_size b = snd r) ->
  (forall r, In r live' -> lr_ok r /\ held_kind X (fst r) /\ qchunk_wf (fst r) /\ (forall A n, qc_hull AL (fst r) A n -> disjoint_from W A n)) ->
  apres FI AI LBk q m m'.
Proof.
  intros lo q X m m' W live' LBk AO LOH CLO RP RS MU FZ ABOVE HB HR a Ha AC.
  destruct (clear_ctx AL X m RP RS) as (_ & SOK & _).
  assert (DJ : disjoint_from W a 1).
  { destruct AC as [AC|[AC|[AC|[AC|[AC|AC]]]]].
    - exact (ABOVE a 1 AC).
    - destruct AC as (lo' & hi' & ST & RNG). apply STAT in ST. apply dj_of_Forall. eapply Forall_impl; [| exact FZ].
      intros iv CZ. pose proof (czone_static_dj AL AO lo q (snd X) LOH SOK iv lo' hi' CZ ST) as DD. clear - DD RNG. lia.
    - destruct AC as (b & Hb & RNG). destruct (HB b Hb) as ([ch' cn] & Hr & BA & BS). cbn [fst snd] in BA, BS.
      destruct (HR _ Hr) as (LR & HK & WF & HU). cbn [fst snd] in LR, HK, WF, HU.
      pose proof (HU (qc_blk AL ch') (qc_bsize ch') ltac:(left; split; reflexivity)) as DH.
      destruct WF as (RZ16 & RZM & NR & RZN & _). unfold lc_user, qc_hdr in BA. unfold rup8 in RZN.
      eapply dj_narrow; [exact DH| |].
      + clear - RNG BA RZ16. lia.
      + destruct LR as [LR|[LR _]]; cbn [fst snd] in LR; [| clear - RNG BS LR; lia]. clear - RNG BA BS LR RZN NR. Z.div_mod_to_equations. lia.
    - apply dj_of_Forall. eapply Forall_impl; [| exact FZ]. intros iv CZ.
      pose proof (czone_fs_dj AL AO lo q (snd X) LOH CLO SOK iv CZ) as [DD _]. rewrite FSBE in AC. clear - DD AC. lia.
    - apply dj_of_Forall. eapply Forall_impl; [| exact FZ]. intros iv CZ.
      pose proof (czone_fs_dj AL AO lo q (snd X) LOH CLO SOK iv CZ) as [_ DD]. rewrite FSBE in AC. clear - DD AC. lia.
    - destruct AC as (b & Hb & RNG). destruct (HB b Hb) as ([ch' cn] & Hr & BA & BS). cbn [fst snd] in BA, BS.
      destruct (HR _ Hr) as (LR & HK & WF & HU). cbn [fst snd] in LR, HK, WF, HU.
      pose proof (HU (sh (qc_blk AL ch')) (qc_bsize ch' / 8) ltac:(right; left; split; reflexivity)) as DH.
      destruct (pchunk_geo AL X m ch' AO RP RS HK) as (B8 & S8 & _).
      destruct WF as (RZ16 & RZM & NR & RZN & _). unfold lc_user, qc_hdr in BA. rewrite BA, BS in RNG.
      destruct LR as [LR|[LR _]]; cbn [fst snd] in LR; [| rewrite LR in RNG; change (Z.of_nat (length (block_shadow 0))) with 0 in RNG; clear - RNG; lia].
      rewrite LR in RNG. rewrite (block_shadow_len (qc_n ch') ltac:(clear - NR; lia)) in RNG.
      replace (qc_blk AL ch' + qc_rz ch' - 16 + 16) with (qc_blk AL ch' + qc_rz ch') in RNG by (clear; lia).
      rewrite (sh_add8 (qc_blk AL ch') (qc_rz ch') B8 ltac:(clear - RZM; Z.div_mod_to_equations; lia)) in RNG.
      eapply dj_narrow; [exact DH| |].
      + clear - RNG RZ16. Z.div_mod_to_equations. lia.
      + unfold rup8 in *. clear - RNG RZN RZM S8 NR. Z.div_mod_to_equations. lia. }
  assert (O : outside W (bv_unsigned (wa a))) by (eapply disjoint_outside; [exact DJ|]; rewrite wa_unsigned by lia; lia).
  split; [left; exact (MU _ O)|]. unfold wview. rewrite (MU _ O). exact (fun Hx => Hx).
Qed.

Notation WNL lo q := [(lo, q); (1323912, 1323912 + 4); (740096, 740096 + 8 + 262144); (1002304, 1268488 + 40); (THR + 3168, THR + 3169)].

#[using="FSBE STAT"] Lemma free_null_conv : forall (gp s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (q lo : Z) (ra s0 s1 s2 s3 s4 s5 : word)
    s LB (m : mem) (st : fsstate FI) ms',
  RHEAP_B AL E s LB m -> mem_inv asegs m -> asan_env asegs m -> RFAKE FI st m -> alloc_ceiling <= lo -> lo <= q ->
  fnull_post L gp s6 s7 s8 s9 s10 s11 F_ fc q lo 262144 262728 ra s0 s1 s2 s3 s4 s5 m ms' ->
  exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m' /\ RFAKE FI st m'
    /\ (forall LBk : list (block (am_K FI AI)),
          (forall b, In b LBk -> exists r, In r (bs_live s) /\ blk_addr b = lc_user AL (fst r) /\ blk_size b = snd r) -> apres FI AI LBk q m m')
    /\ wmono asegs m m' /\ RHEAP_B AL E s LB m'.
Proof.
  intros gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra s0 s1 s2 s3 s4 s5 s LB m st ms' HR MI AE RF CLO LQ POST.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (LOH : 0x10007fff8000 <= lo) by (clear - ACR CLO; lia).
  destruct POST as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MI' & STK' & TE' & IA').
  pose proof HR as (PLB & LOK & AO & INVB & QLG & GC & (TQC & QLL) & MTX & (CST & AFM) & QWF & RD & DOK & WFL & REPL & HKL & PSEC & COV & TE2 & HKE & (TR1 & TR2 & TR3) & AENV & _ & CCL & CCQ & SLK & BUD & FTE).
  pose proof (dr_inv_of_B AL E _ _ _ _ _ _ INVB MI) as INV. pose proof INV as (RP & _ & RS & _ & _ & _ & _ & _ & _ & _ & HOK & _).
  set (X := bs_X s) in *.
  pose proof AO as (_ & _ & _ & TLO & DLO & SWB). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & _).
  assert (FZ : Forall (izone AL lo) (WNL lo q)).
  { unfold izone, iastat. repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd];
      [left; clear; lia| right; left; right; clear; lia| right; left; left; clear; lia| right; left; left; clear; lia| right; right; reflexivity]. }
  assert (FC : Forall (czone AL lo q (snd X)) (WNL lo q)).
  { unfold czone, sub_iv, iastat. repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd];
      [left; clear - LQ; lia| do 3 right; left; right; clear; lia| do 3 right; left; left; clear; lia| do 3 right; left; left; clear; lia| do 7 right; left; clear; lia]. }
  destruct (clear_ctx AL X m RP RS) as (_ & SOK & _).
  layout_facts AO 5%nat LDN. destruct LDN as (N1d & N2d & _). layout_facts AO 6%nat LSS. destruct LSS as (S1d & S2d & _).
  layout_apart_fact AO 3%nat 5%nat A35. layout_apart_fact AO 3%nat 6%nat A36. layout_apart_fact AO 2%nat 3%nat A23.
  assert (DJT : forall A k, A + k <= lo -> (A + k <= 740096 \/ (1268528 <= A /\ (A + k <= 1323912 \/ 1323916 <= A))) -> (A + k <= THR + 3168 \/ THR + 3169 <= A) -> disjoint_from (WNL lo q) A k)
    by (intros A k D1 D2 D3; cbn [disjoint_from]; clear - D1 D2 D3; lia).
  assert (HBP : forall b, In b (bs_gl s) -> held1 (fst X) (bpair b)).
  { intros b Hb. destruct HOK as [_ FH]. apply (proj1 (Forall_forall _ _) FH). apply in_or_app. left. apply in_map. exact Hb. }
  exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
  split; [exact EMS|]. split; [exact MI'|]. split; [exact STK'|].
  split; [exact (asan_env_frame_m asegs m m' _ AE MU (czone_env_safe AL AO lo q (snd X) LOH SOK _ FC))|].
  split.
  { eapply (rfake_frame_m FI st m m' _ RF MU). eapply Forall_impl; [| exact FC]. intros iv CZ. left. rewrite FSBE. exact (czone_fs_dj AL AO lo q (snd X) LOH CLO SOK iv CZ). }
  assert (HULL : forall ch', held_kind X ch' -> forall A n, qc_hull AL ch' A n -> disjoint_from (WNL lo q) A n)
    by (intros ch' HK' A n HU; exact (hull_izone_dj AL X m lo _ ch' A n AO LOH CLO RP RS HK' FZ HU)).
  split.
  { intros LBk HB. apply (apres_of_czone lo q X m m' _ (bs_live s) LBk AO LOH CLO RP RS MU FC); [| exact HB|].
    - intros A k HA. cbn [disjoint_from]. clear - HA LQ LOH CLO T3 T4. lia.
    - intros r Hr. assert (INC : In (fst r) (live_chunks s)) by (unfold live_chunks; apply in_map; exact Hr).
      split; [exact (proj1 (Forall_forall _ _) LOK r Hr)|]. split; [exact (proj1 (Forall_forall _ _) HKL _ INC)|].
      split; [exact (proj1 (Forall_forall _ _) WFL _ INC)|]. exact (HULL _ (proj1 (Forall_forall _ _) HKL _ INC)). }
  split; [exact WM|].

  unfold RHEAP_B. cbv zeta. fold X.
  split; [exact PLB|]. split; [exact LOK|]. split; [exact AO|].
  split; [exact (proj1 (dr_invB_of AL E _ _ _ _ _ _ (dr_inv_frame_i AL E X (bs_H s) m m' _ _ _ lo _ AO LOH CLO INV MU WM MI' TE' FZ)))|].
  split. { eapply (qlist_rep_frame_i AL X m m' lo _ _ 0 AO LOH CLO RP RS FZ MU QLG). apply Forall_forall. intros b Hb. apply HBP. unfold bs_gl. apply in_or_app. left. exact Hb. }
  split; [eapply rw_cells_transport_m; [exact GC| exact MU| cbn [cells_size csize Nat.add qcells]; apply DJT; clear - LOH T3; lia]|].
  split.
  { split; [eapply rw_cells_transport_m; [exact TQC| exact MU| cbn [cells_size csize Nat.add]; apply DJT; clear - LOH CLO T3 T4; lia]|].
    eapply (qlist_rep_frame_i AL X m m' lo _ _ 0 AO LOH CLO RP RS FZ MU QLL). apply Forall_forall. intros b Hb. apply HBP. unfold bs_gl. apply in_or_app. right. exact Hb. }
  split; [eapply rw_cells_transport_m; [exact MTX| exact MU| cbn [cells_size csize Nat.add]; apply DJT; clear - LOH T3; lia]|].
  split; [split; (eapply rw_cells_transport_m; [eassumption| exact MU| cbn [cells_size csize Nat.add]; apply DJT; clear - LOH T3; lia])|].
  split; [exact QWF|].
  split; [eapply (RDEPOT_frame_m AL _ _ _ m m' DLO SWB RD MU); apply DJT; clear - LOH CLO N1d N2d S1d S2d A35 A36 T3; lia|].
  split; [exact DOK|]. split; [exact WFL|].
  split.
  { apply Forall_forall. intros ch' Hch'. pose proof (proj1 (Forall_forall _ _) HKL ch' Hch') as HK'.
    exact (lchunk_rep_hull AL X _ m m' ch' AO RP RS HK' (proj1 (Forall_forall _ _) REPL ch' Hch') (proj1 (Forall_forall _ _) WFL ch' Hch') MU (HULL ch' HK')). }
  split; [exact HKL|]. split; [exact PSEC|]. split; [exact COV|].
  split; [eapply (thread_env2_frame_m AL _ m m' TE2 MU); apply DJT; clear - LOH CLO T1 T2 T3 T4 T5 A23; lia|].
  split; [unfold hooks_env in *; eapply rw_cells_transport_m; [exact HKE| exact MU| cbn [cells_size csize Nat.add]; apply DJT; clear - LOH T3; lia]|].
  split; [unfold trace_env; split; [| split]; (eapply rw_cells_transport_m; [eassumption| exact MU| cbn [cells_size csize Nat.add]; apply DJT; clear - LOH T3; lia])|].
  split; [ae_split AENV; unfold alloc_env; repeat match goal with |- _ /\ _ => split end; (eapply rw_cells_transport_m; [eassumption| exact MU| cbn [cells_size csize Nat.add]; apply DJT; clear - LOH T3; lia])|].
  split; [exists true; exact IA'|]. split; [exact CCL|]. split; [exact CCQ|]. split; [exact SLK|]. split; [exact BUD|].
  eapply (fs_tls_env_frame_m _ _ _ _ _ _ m m' FTE MU). unfold fte_apart.
  layout_facts AO 7%nat LF7. destruct LF7 as ((DPL & _) & DCE & _). layout_apart_fact AO 3%nat 7%nat A37.
  repeat match goal with |- _ /\ _ => split end; apply DJT; clear - LOH CLO T1 T2 T3 T4 T5 A23 A37 DPL DCE; lia.
Qed.

End CONVN.

#[using="Type"] Lemma free_null_walk : forall (gp s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (q lo : Z)
    (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) s LB (m : mem) ras,
  RHEAP_B AL E s LB m -> mem_inv asegs m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 4096 -> q mod 16 = 0 -> q + 16 < at_top L ->
  fpchain m (at_top L) q (bv_unsigned s0) ras -> In (PC0_FREE :: bv_unsigned ra :: ras) A0_TRACES ->
  evt asegs (fnull_post L gp s6 s7 s8 s9 s10 s11 F_ fc q lo 262144 262728 ra s0 s1 s2 s3 s4 s5 m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz free_icpt_entry) fc None m (seg_rom asegs)).
Proof.
  intros gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 s LB m ras HR MI ST CLO LOQ Q16 QTOP CH TRIN.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  destruct (traces_ok _ _ _ TRIN) as (LRAS & NPC & RA4 & RANE & _).
  destruct HR as (_ & _ & AO & INVB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TRE & AENV & (inited & IA) & _).
  destruct INVB as (_ & _ & _ & _ & TE & _). pose proof AO as (_ & _ & _ & TLO & _).
  exact (free_null_icpt_spec L TLO gp s6 s7 s8 s9 s10 s11 F_ fc q lo ltac:(clear - ACR CLO; lia) CLO ltac:(unfold FICPT_STACK; exact LOQ) QTOP Q16 262144 262728 eq_refl eq_refl
           ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m ras inited ST MI TE TRE IA CH LRAS NPC RA4 RANE).
Qed.

End FL8.
