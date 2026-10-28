(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApInv ApErr ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts HxpInit HxpGetState.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApIface ApWalkTac ApErrKit ApErrKit2 F_strlen F_strcpy W_err_new ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 (Z_to_bv 64 ?z) => constr:(C1 (Z_to_bv 8 z))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac step := ub; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := ub; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.

(* [comment removed for export] *)
Ltac es_store WR :=
  let HS := fresh "HS" in let ESn := fresh "ESn" in
  destruct WR as [HS ESn]; unfold MallocRep.wz, ESO_FLAGS, ESO_MARKS, ESO_BUFFER, ESO_DATA, ESO_DSIZE, ESO_DFLAGS, ESO_FILE, ESO_LINE, ESO_FUNC, ESO_TOP in HS, ESn; step;
  lazymatch type of ESn with es_raw (write_to_mem ?m ?a ?bs) _ _ =>
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m ?a2 ?bs2) _) =>
      first [ constr_eq a a2; constr_eq bs bs2
            | replace (write_to_mem m a2 bs2) with (write_to_mem m a bs) by (unfold wa; f_equal; first [reflexivity | word_eq_tac | vm_compute; reflexivity]) ]
    end;
    try match goal with H : es_raw m _ _ |- _ => clear H end
  end;
  store_done; rename ESn into ES;
  (* [comment removed for export] *)
  try lazymatch goal with
  | ES : es_raw _ _ ?g, GL : g_len _ |- _ =>
      let GLn := fresh "GLn" in
      assert (GLn : g_len g)
        by (let H := fresh in pose proof GL as H; unfold g_len in H |- *;
            cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot set_g_fl set_g_ma set_g_bu set_g_da set_g_ds set_g_df set_g_fi set_g_li set_g_fu set_g_top set_g_bot] in H |- *;
            rewrite ?upd_length in H; rewrite ?upd_length; exact H);
      clear GL; rename GLn into GL
  end.

(* [comment removed for export] *)
Ltac post_call_es segs m ES GL :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO; destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ m ?m' =>
      eapply es_raw_transport in ES; [|exact GL|exact MUc|exact WMc|cbn; lia];
      transport_after_call segs m m' MUc WMc; clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end; try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition lit_ok (a : Z) (str slack : list byte) (n : Z) : Prop :=
  ro_bytes_b ctusegs a (str ++ Z_to_bv 8 0 :: slack) = true /\ ~ In (Z_to_bv 8 0) str /\ str <> []
  /\ (- (a + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack)
  /\ Z.of_nat (length str) + 1 = n
  /\ 0x10000 <= a /\ a + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= 0xcc000.

Definition ERR_set_debug_spec (rs : rsite) (file func : Z) : Prop :=
  forall (bo0 : Z * Z) (fstr fslack nstr nslack : list byte),
  lit_ok file fstr fslack (rs_flen rs) -> lit_ok func nstr nslack (rs_fnlen rs) ->
  ap_stmt ERR_SET_DEBUG ERR_SET_DEBUG_STACK
          (fun st OW m a0 a1 a2 a3 a4 a5 bo => a0 = wz file /\ a1 = wz (rs_line rs) /\ a2 = wz func /\ bo = bo0)
          (err_set_debug rs)
          (fun r OW' m' a0' bo' => bo' = bo0).

(* [comment removed for export] *)
Lemma lit_bytes_at : forall m a str slack n, mem_inv ctusegs m -> lit_ok a str slack n -> bytes_at ctusegs m a (str ++ Z_to_bv 8 0 :: slack).
Proof.
  intros m a str slack n MI (RO & _ & _ & _ & _ & LO & HI).
  pose proof (ro_cells_image ctusegs m a _ MI RO ltac:(lia) ltac:(rewrite length_app; cbn [length]; lia)) as RC.
  pose proof (ro_cells_bytes_at ctusegs m a _ RC) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Lemma lit_first : forall a str slack n, lit_ok a str slack n -> exists c str', str = c :: str' /\ bv_unsigned c <> 0.
Proof.
  intros a str slack n (_ & NN & NE & _). destruct str as [|c str']; [congruence|]. exists c, str'. split; [reflexivity|].
  intros Hc. apply NN. left. apply bv_eq. rewrite Hc. reflexivity.
Qed.

(* [comment removed for export] *)
Definition lit_auto (a n : Z) : bool :=
  match image_bytes ctusegs a (Z.to_nat (n - 1)), image_bytes ctusegs (a + n) 8 with
  | Some s, Some k =>
      ro_bytes_b ctusegs a (s ++ Z_to_bv 8 0 :: k) && forallb (fun b : byte => negb (bv_eqb b (Z_to_bv 8 0))) s
      && (2 <=? n) && (0x10000 <=? a) && (a + n + 8 <=? 0xcc000)
  | _, _ => false
  end.

Lemma lit_ok_auto : forall a n, lit_auto a n = true -> exists s k, lit_ok a s k n.
Proof.
  intros a n H. unfold lit_auto in H.
  destruct (image_bytes ctusegs a (Z.to_nat (n - 1))) as [s|] eqn:ES; [|discriminate].
  destruct (image_bytes ctusegs (a + n) 8) as [k|] eqn:EK; [|discriminate].
  apply andb_prop in H as [H R2]. apply andb_prop in H as [H R1]. apply andb_prop in H as [H N2]. apply andb_prop in H as [RO NN].
  apply Z.leb_le in R2. apply Z.leb_le in R1. apply Z.leb_le in N2.
  pose proof (image_bytes_length ctusegs _ _ _ ES) as LS. pose proof (image_bytes_length ctusegs _ _ _ EK) as LK.
  exists s, k. unfold lit_ok. rewrite LS, LK. split; [exact RO|]. split.
  { intros Hin. pose proof (proj1 (forallb_forall _ _) NN _ Hin) as X. cbn in X. unfold bv_eqb in X. rewrite Z.eqb_refl in X. discriminate. }
  split; [destruct s; [cbn in LS; lia|discriminate]|]. split; [pose proof (Z.mod_pos_bound (- (a + Z.of_nat (Z.to_nat (n - 1)) + 1)) 8 ltac:(lia)); lia|].
  split; [lia|]. split; lia.
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  (* [comment removed for export] *)
  Section Act.
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo0 : Z * Z) (lo B : Z) (canary : word).
  Variables (rs : rsite) (Lf Ln : Z) (fstr fslack nstr nslack : list byte).
  Hypothesis IDS : ids_ok E st.
  Hypothesis SPB : bv_unsigned sp <= B.
  Hypothesis B63 : B < 2 ^ 63.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : 3493888 <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - (80 + 48 + 8192).
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis FRM : frm0 fc.
  Hypothesis SH : es_shape st.
  Hypothesis IES : In (p_es E, e_es E, 904) OW.
  Hypothesis EESP : 0 < e_es E.
  Hypothesis EESC : e_es E + 904 <= alloc_ceiling.
  Hypothesis EESI : e_es E + 904 <= 65536 \/ 3493888 <= e_es E.
  Hypothesis EES16 : e_es E mod 16 = 0.
  Hypothesis OF : Forall (optb_ok OW) (as_file st).
  Hypothesis OFN : Forall (optb_ok OW) (as_func st).
  Hypothesis OD : Forall (optb_ok OW) (as_data st).
  Hypothesis AS0 : exists m0, ap_state st m0 OW E bo0.
  Hypothesis IDIN : ids_in E st OW.
  Hypothesis CAN : canary = rr_guard.
  Hypothesis EA : errno_addr (Z_to_bv 64 RATP) = 3355012.
  Hypothesis LITF : lit_ok Lf fstr fslack (rs_flen rs).
  Hypothesis LITN : lit_ok Ln nstr nslack (rs_fnlen rs).
  Variable K : list block.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).

  Let tn : nat := as_top st.
  Let line : Z := rs_line rs.
  Let flen : Z := rs_flen rs.
  Let fnlen : Z := rs_fnlen rs.
  (* [comment removed for export] *)
  Let st_a : ap_st bptr := set_file tn None st.
  Definition st_b (pf : bptr) : ap_st bptr := set_line tn line (set_file tn (Some (pf, flen)) st_a).
  Definition st_c (pf : bptr) : ap_st bptr := set_func tn None (st_b pf).
  Definition st_fin (pf pn : bptr) : ap_st bptr := set_func tn (Some (pn, fnlen)) (st_c pf).
  (* [comment removed for export] *)
  Local Notation W2 := ([(bv_unsigned sp - 8320, bv_unsigned sp); (e_es E, e_es E + 904)]%Z) (only parsing).
  Local Notation SB := (seg_base s m OW st E bo0 LB K (bv_unsigned sp) B) (only parsing).
  Let POST := ap_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s OW LB E lo B canary m K
                (fun (r : unit * ap_st bptr) (OW' : list block) (m' : mem) (a0' : word) (bo' : Z * Z) => bo' = bo0).
  (* [comment removed for export] *)
  Definition sd_frame (j0 : list byte) : list cell := [CB 8 j0; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma TNB : (tn < 16)%nat.
  Proof. pose proof (ids_ok_top _ _ IDS) as [T _]. exact T. Qed.

  (* [comment removed for export] *)
  Definition g1 (A1 : Z) : esg := set_g_fi (upd (g_fi (g_of st (badr OW))) tn (Z_to_bv 64 A1)) (g_of st (badr OW)).
  Definition g2 (A1 : Z) : esg := set_g_li (upd (g_li (g1 A1)) tn (Z_to_bv 64 line)) (g1 A1).
  Definition gfin (A1 A2 : Z) : esg := set_g_fu (upd (g_fu (g2 A1)) tn (Z_to_bv 64 A2)) (g2 A1).

  (* [comment removed for export] *)
  Definition REST3 : @AM bptr unit := abind (amalloc fnlen) (fun pn => amodify (set_func tn (Some (pn, fnlen)))).

  (* [comment removed for export] *)
  Lemma fin_pure : forall (pf : bptr) (A1 : Z) (pn : bptr) (A2 : Z),
    let OW1 := lremove (get_file tn st) OW in
    let OW2 := (pf, A1, flen) :: OW1 in
    let OW3 := lremove (get_func tn st) OW2 in
    let OW4 := (pn, A2, fnlen) :: OW3 in
    ~ In pf (map blk_id (OW1 ++ LB)) -> rblock_range A1 flen -> ~ In pn (map blk_id (OW3 ++ LB)) -> rblock_range A2 fnlen ->
    ids_ok E (st_fin pf pn) /\ ids_in E (st_fin pf pn) OW4
    /\ g_of (st_fin pf pn) (badr OW4) = gfin A1 A2
    /\ Forall (optb_ok OW4) (as_file (st_fin pf pn)) /\ Forall (optb_ok OW4) (as_func (st_fin pf pn)) /\ Forall (optb_ok OW4) (as_data (st_fin pf pn))
    /\ (forall mX, ap_rest mX OW E bo0 (as_cnf st) -> ap_rest mX OW4 E bo0 (as_cnf (st_fin pf pn)))
    /\ (forall i q k, get_data i st = Some (q, k) -> badr OW4 q = badr OW q)
    /\ (forall b, In b K -> ~ In (blk_id b) (es_ids (st_fin pf pn)))
    /\ es_shape (st_fin pf pn).
  Proof.
    intros pf A1 pn A2. cbn zeta. intros NI1 BR1 NI2 BR2.
    set (OW1 := lremove (get_file tn st) OW). set (OW2 := (pf, A1, flen) :: OW1). set (OW3 := lremove (get_func tn st) OW2). set (OW4 := (pn, A2, fnlen) :: OW3).
    pose proof TNB as TNB'. pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB].
    pose proof SH as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
    pose proof BR1 as (BP1 & BP2 & BP3 & BP4 & BP5). pose proof BR2 as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5).
    (* [comment removed for export] *)
    assert (QF : forall q n, get_file tn st = Some (q, n) -> In (q, badr OW q, n) OW /\ In q (es_ids st) /\ In q (map blk_id OW)).
    { intros q n GF. pose proof (proj1 (optb_ok_nth OW _ tn q n OF GF)) as HIn. split; [exact HIn|]. split; [eapply es_ids_file; exact GF|].
      change q with (blk_id (q, badr OW q, n)). apply in_map. exact HIn. }
    assert (QN : forall q n, get_func tn st = Some (q, n) -> In (q, badr OW q, n) OW1 /\ In q (es_ids st) /\ In q (map blk_id OW1)).
    { intros q n GN. pose proof (proj1 (optb_ok_nth OW _ tn q n OFN GN)) as HIn.
      assert (HIn1 : In (q, badr OW q, n) OW1).
      { subst OW1. apply lremove_keep; [exact HIn|]. intros q' n' GF. cbn. apply not_eq_sym. eapply ids_file_func_ne; [exact IDS|exact GF|exact GN]. }
      split; [exact HIn1|]. split; [eapply es_ids_func; exact GN|]. change q with (blk_id (q, badr OW q, n)). apply in_map. exact HIn1. }
    (* [comment removed for export] *)
    assert (PF1 : forall b, In b OW1 -> blk_id b <> pf).
    { intros b Hb EQ. apply NI1. rewrite <- EQ, map_app. apply in_app_iff. left. apply in_map. exact Hb. }
    assert (PFQN : forall q n, get_func tn st = Some (q, n) -> pf <> q).
    { intros q n GN ->. exact (PF1 _ (proj1 (QN q n GN)) eq_refl). }
    assert (IN3 : forall b, In b OW1 -> (forall q n, get_func tn st = Some (q, n) -> blk_id b <> q) -> In b OW3).
    { intros b Hb Hq. subst OW3 OW2. apply lremove_keep; [right; exact Hb|exact Hq]. }
    assert (PF3 : In (pf, A1, flen) OW3).
    { subst OW3 OW2. apply lremove_keep; [left; reflexivity|]. intros q n GN. cbn. eapply PFQN. exact GN. }
    assert (PN3 : forall b, In b OW3 -> blk_id b <> pn).
    { intros b Hb EQ. apply NI2. rewrite <- EQ, map_app. apply in_app_iff. left. apply in_map. exact Hb. }
    assert (NEP : pn <> pf) by (intros EQ; exact (PN3 _ PF3 (eq_sym EQ))).
    (* [comment removed for export] *)
    set (stc' := set_func tn None st_a).
    assert (LFa : (tn < length (as_file st))%nat) by (rewrite L5; exact TNB').
    assert (LNa : (tn < length (as_func st_a))%nat) by (unfold st_a; cbn [as_func set_file]; rewrite L7; exact TNB').
    pose proof (st_blocks_set_file tn None st LFa) as P1. cbn [optb] in P1. rewrite app_nil_l in P1 || idtac. fold st_a in P1.
    pose proof (st_blocks_set_func tn None st_a LNa) as P1'. cbn [optb] in P1'. rewrite app_nil_l in P1' || idtac. fold stc' in P1'.
    assert (GNa : get_func tn st_a = get_func tn st) by reflexivity. rewrite GNa in P1'.
    assert (PC : Permutation ((optb (get_file tn st) ++ optb (get_func tn st)) ++ st_blocks stc') (st_blocks st)).
    { rewrite <- app_assoc. eapply Permutation_trans; [|exact P1]. apply Permutation_app_head. exact P1'. }
    (* [comment removed for export] *)
    assert (NOT4 : forall p, In p (es_ids stc') ->
              (forall q n, get_file tn st = Some (q, n) -> p <> q) /\ (forall q n, get_func tn st = Some (q, n) -> p <> q) /\ In p (es_ids st)).
    { intros p Hp. pose proof (ids_pre_disjoint E st stc' _ p IDS PC Hp) as NI. rewrite !map_app, !in_app_iff in NI.
      split; [|split; [|eapply es_ids_sub_perm; [exact PC|exact Hp]]]; intros q n G ->; apply NI; rewrite G; cbn; tauto. }
    assert (SURV : forall p b, In p (es_ids stc') -> In b OW -> blk_id b = p -> In b OW4 /\ badr OW4 p = badr OW p /\ p <> pf /\ p <> pn).
    { intros p b Hp Hb Hid. destruct (NOT4 p Hp) as (N1 & N2 & N3).
      assert (Hb1 : In b OW1) by (subst OW1; apply lremove_keep; [exact Hb|]; intros q n G; rewrite Hid; exact (N1 q n G)).
      assert (Npf : p <> pf) by (rewrite <- Hid; exact (PF1 b Hb1)).
      assert (Hb3 : In b OW3) by (apply IN3; [exact Hb1|]; intros q n G; rewrite Hid; exact (N2 q n G)).
      assert (Npn : p <> pn) by (rewrite <- Hid; exact (PN3 b Hb3)).
      split; [right; exact Hb3|]. split; [|split; [exact Npf|exact Npn]].
      subst OW4 OW3 OW2 OW1. rewrite badr_cons, (bptr_eqb_neq pn p ltac:(congruence)).
      rewrite badr_lremove by (intros q n G; exact (N2 q n G)). rewrite badr_cons, (bptr_eqb_neq pf p ltac:(congruence)).
      rewrite badr_lremove by (intros q n G; exact (N1 q n G)). reflexivity. }
    (* [comment removed for export] *)
    assert (BPN : badr OW4 pn = A2) by (subst OW4; rewrite badr_cons, bptr_eqb_refl; reflexivity).
    assert (BPF : badr OW4 pf = A1).
    { subst OW4 OW3 OW2. rewrite badr_cons, (bptr_eqb_neq pn pf NEP). rewrite badr_lremove by (intros q n G; eapply PFQN; exact G).
      rewrite badr_cons, bptr_eqb_refl. reflexivity. }
    (* [comment removed for export] *)
    assert (GFa : get_file tn st_a = None) by (unfold st_a, get_file; cbn [as_file set_file]; apply nth_lset_same; rewrite L5; exact TNB').
    assert (LFa' : (tn < length (as_file st_a))%nat) by (unfold st_a; cbn [as_file set_file]; rewrite lset_length, L5; exact TNB').
    assert (P2 : Permutation (st_blocks (st_b pf)) ((pf, flen) :: st_blocks st_a)).
    { unfold st_b. rewrite st_blocks_set_line. pose proof (st_blocks_set_file tn (Some (pf, flen)) st_a LFa') as P. rewrite GFa in P. cbn [optb app] in P. exact P. }
    assert (GNb : get_func tn (st_b pf) = get_func tn st) by reflexivity.
    assert (LNb : (tn < length (as_func (st_b pf)))%nat) by (unfold st_b, st_a; cbn [as_func set_line set_file]; rewrite L7; exact TNB').
    pose proof (st_blocks_set_func tn None (st_b pf) LNb) as P3. rewrite GNb in P3. cbn [optb] in P3. rewrite app_nil_l in P3 || idtac.
    change (set_func tn None (st_b pf)) with (st_c pf) in P3.
    assert (GNc : get_func tn (st_c pf) = None) by (unfold st_c, get_func; cbn [as_func set_func]; apply nth_lset_same; exact LNb).
    assert (LNc : (tn < length (as_func (st_c pf)))%nat) by (unfold st_c; cbn [as_func set_func]; rewrite lset_length; exact LNb).
    assert (P4 : Permutation (st_blocks (st_fin pf pn)) ((pn, fnlen) :: st_blocks (st_c pf))).
    { unfold st_fin. pose proof (st_blocks_set_func tn (Some (pn, fnlen)) (st_c pf) LNc) as P. rewrite GNc in P. cbn [optb app] in P. exact P. }
    (* [comment removed for export] *)
    assert (IDINa : ids_in E st_a OW1).
    { subst OW1. destruct (get_file tn st) as [[qf nf]|] eqn:GF; cbn [lremove optb app] in P1 |- *.
      - eapply ids_in_remove; [exact IDS|exact P1|exact IDIN].
      - intros q Hq. apply IDIN. apply in_app_iff in Hq. apply in_app_iff. destruct Hq as [Hq|Hq]; [left|right; exact Hq].
        unfold es_ids in *. apply in_map_iff in Hq. destruct Hq as (b & <- & Hb). apply in_map. eapply Permutation_in; [exact P1|exact Hb]. }
    assert (IDSa : ids_ok E st_a) by (eapply ids_ok_sub; [exact P1|exact TNB'|exact BOTB|apply marks_sub_eq; reflexivity|exact IDS]).
    pose proof (fresh_not_ids E st_a OW1 LB pf IDINa NI1) as FRF.
    assert (IDSb : ids_ok E (st_b pf)) by (eapply ids_ok_add; [exact P2|exact FRF|exact TNB'|exact BOTB|apply marks_sub_eq; reflexivity|exact IDSa]).
    assert (IDINb : ids_in E (st_b pf) OW2) by (subst OW2; eapply ids_in_add; [exact P2|exact IDINa]).
    assert (IDINc : ids_in E (st_c pf) OW3).
    { subst OW3. destruct (get_func tn st) as [[qn nn]|] eqn:GN; cbn [lremove optb app] in P3 |- *.
      - eapply ids_in_remove; [exact IDSb|exact P3|exact IDINb].
      - intros q Hq. apply IDINb. apply in_app_iff in Hq. apply in_app_iff. destruct Hq as [Hq|Hq]; [left|right; exact Hq].
        unfold es_ids in *. apply in_map_iff in Hq. destruct Hq as (b & <- & Hb). apply in_map. eapply Permutation_in; [exact P3|exact Hb]. }
    assert (IDSc : ids_ok E (st_c pf)) by (eapply ids_ok_sub; [exact P3|exact TNB'|exact BOTB|apply marks_sub_eq; reflexivity|exact IDSb]).
    pose proof (fresh_not_ids E (st_c pf) OW3 LB pn IDINc NI2) as FRN.
    assert (IDSf : ids_ok E (st_fin pf pn)) by (eapply ids_ok_add; [exact P4|exact FRN|exact TNB'|exact BOTB|apply marks_sub_eq; reflexivity|exact IDSc]).
    assert (IDINf : ids_in E (st_fin pf pn) OW4) by (subst OW4; eapply ids_in_add; [exact P4|exact IDINc]).
    split; [exact IDSf|]. split; [exact IDINf|].
    (* [comment removed for export] *)
    assert (OFc : Forall (optb_ok OW) (as_file stc')) by (unfold stc', st_a; cbn [as_file set_func set_file]; apply optb_ok_lset_none; exact OF).
    assert (ONc : Forall (optb_ok OW) (as_func stc')) by (unfold stc', st_a; cbn [as_func set_func set_file]; apply optb_ok_lset_none; exact OFN).
    assert (ODc : Forall (optb_ok OW) (as_data stc')) by (unfold stc', st_a; cbn [as_data set_func set_file]; exact OD).
    assert (GEN : forall l, Forall (optb_ok OW) l -> (forall p n, In (Some (p, n)) l -> In p (es_ids stc')) ->
                  Forall (optb_ok OW4) l /\ (forall p n, In (Some (p, n)) l -> badr OW p = badr OW4 p)).
    { intros l Hl Hids.
      assert (ONE : forall p n, In (Some (p, n)) l -> In (p, badr OW p, n) OW4 /\ badr OW4 p = badr OW p /\ 0 < badr OW p).
      { intros p n Hin. pose proof (proj1 (Forall_forall _ _) Hl _ Hin) as [HIn Hpos]. cbn in HIn, Hpos.
        destruct (SURV p (p, badr OW p, n) (Hids p n Hin) HIn eq_refl) as (I4 & E4 & _). split; [exact I4|]. split; [exact E4|exact Hpos]. }
      split.
      - apply Forall_forall. intros [[p n]|] Hin; cbn -[badr]; [|exact I]. destruct (ONE p n Hin) as (I4 & E4 & Hpos). rewrite E4. split; [exact I4|exact Hpos].
      - intros p n Hin. symmetry. exact (proj1 (proj2 (ONE p n Hin))). }
    destruct (GEN (as_file stc') OFc ltac:(intros p n Hin; eapply es_ids_in; left; exact Hin)) as [OF4 EF4].
    destruct (GEN (as_func stc') ONc ltac:(intros p n Hin; eapply es_ids_in; right; left; exact Hin)) as [ON4 EN4].
    destruct (GEN (as_data stc') ODc ltac:(intros p n Hin; eapply es_ids_in; right; right; exact Hin)) as [OD4 ED4].
    (* [comment removed for export] *)
    split.
    { change (st_fin pf pn) with (set_func tn (Some (pn, fnlen)) (set_line tn line (set_file tn (Some (pf, flen)) stc'))).
      rewrite g_of_set_func, g_of_set_line, g_of_set_file.
      rewrite (g_of_adr_ext stc' (badr OW4) (badr OW)) by (intros p n Hin; symmetry; eauto).
      unfold stc', st_a. rewrite g_of_set_func, g_of_set_file. unfold gfin, g2, g1.
      cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot set_g_fi set_g_li set_g_fu as_file as_func set_func set_file set_line optr].
      unfold MallocRep.wz. rewrite BPN, BPF, !upd_upd_same. reflexivity. }
    (* [comment removed for export] *)
    split.
    { change (as_file (st_fin pf pn)) with (lset (as_file stc') tn (Some (pf, flen))). apply optb_ok_lset_some; [exact OF4| |rewrite BPF; exact BP1].
      rewrite BPF. subst OW4. right. exact PF3. }
    split.
    { change (as_func (st_fin pf pn)) with (lset (as_func stc') tn (Some (pn, fnlen))). apply optb_ok_lset_some; [exact ON4| |rewrite BPN; exact BQ1].
      rewrite BPN. subst OW4. left. reflexivity. }
    split; [change (as_data (st_fin pf pn)) with (as_data stc'); exact OD4|].
    (* [comment removed for export] *)
    split.
    { intros mX AR. change (as_cnf (st_fin pf pn)) with (as_cnf st). subst OW4. apply rest_OW_cons; [| |exact BQ1|lia|exact BQ2].
      - subst OW3. apply rest_lremove.
        + subst OW2. apply rest_OW_cons; [| |exact BP1|lia|exact BP2].
          * subst OW1. apply rest_lremove; [exact AR|]. intros q n GF. split; [eapply file_not_rest; [exact IDS|exact GF]|eapply ids_es_ne; [exact IDS|eapply es_ids_file; exact GF]].
          * intros Hin. apply NI1. rewrite map_app. apply in_app_iff. left. exact Hin.
        + intros q n GN. split; [eapply func_not_rest; [exact IDS|exact GN]|eapply ids_es_ne; [exact IDS|eapply es_ids_func; exact GN]].
      - intros Hin. apply NI2. rewrite map_app. apply in_app_iff. left. exact Hin. }
    (* [comment removed for export] *)
    split.
    { intros i q k Hd. symmetry. eapply (ED4 q k). unfold get_data in Hd. rewrite <- Hd. apply nth_In.
      destruct (Nat.lt_ge_cases i (length (as_data st))) as [Hl|Hl]; [exact Hl|]. rewrite (nth_overflow _ None Hl) in Hd. discriminate. }
    (* [comment removed for export] *)
    split.
    { intros b Hb Hin.
      assert (CASES : blk_id b = pn \/ blk_id b = pf \/ In (blk_id b) (es_ids st)).
      { unfold es_ids in Hin. apply in_map_iff in Hin. destruct Hin as (x & Ex & Hx).
        pose proof (Permutation_in _ P4 Hx) as [<-|Hx1]; [left; symmetry; exact Ex|].
        assert (Hx2 : In x (st_blocks (st_b pf))) by (eapply Permutation_in; [exact P3|]; apply in_app_iff; right; exact Hx1).
        pose proof (Permutation_in _ P2 Hx2) as [<-|Hx3]; [right; left; symmetry; exact Ex|].
        right. right. rewrite <- Ex. unfold es_ids. apply in_map. eapply Permutation_in; [exact P1|]. apply in_app_iff. right. exact Hx3. }
      pose proof (KIDS b Hb) as NK. rewrite in_app_iff in NK.
      assert (Hb1 : In b OW1).
      { subst OW1. apply lremove_keep; [apply KOW; exact Hb|]. intros q n GF EQ. apply NK. left. rewrite EQ. eapply es_ids_file. exact GF. }
      assert (Hb3 : In b OW3).
      { apply IN3; [exact Hb1|]. intros q n GN EQ. apply NK. left. rewrite EQ. eapply es_ids_func. exact GN. }
      destruct CASES as [C|[C|C]]; [exact (PN3 b Hb3 C)|exact (PF1 b Hb1 C)|apply NK; left; exact C]. }
    (* [comment removed for export] *)
    unfold st_fin, st_c, st_b, st_a. repeat apply es_shape_setters. exact SH.
  Qed.

  (* [comment removed for export] *)
  Lemma ERR_set_debug_finish : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (sE : PState) (mb m9 : mem) (errv' : word)
      (pf : bptr) (A1 : Z) (pn : bptr) (A2 : Z),
    SB sE ((pn, A2, fnlen) :: lremove (get_func tn st) ((pf, A1, flen) :: lremove (get_file tn st) OW)) mb ->
    ~ In pf (map blk_id (lremove (get_file tn st) OW ++ LB)) -> rblock_range A1 flen ->
    ~ In pn (map blk_id (lremove (get_func tn st) ((pf, A1, flen) :: lremove (get_file tn st) OW) ++ LB)) -> rblock_range A2 fnlen ->
    (forall OWd, seg_writable OW st E K OWd pn) ->
    munch [(bv_unsigned sp - 8320, bv_unsigned sp); (e_es E, e_es E + 904); (A2, A2 + fnlen)]%Z mb m9 -> wmono ctusegs mb m9 ->
    es_raw m9 (e_es E) (gfin A1 A2) -> stk ctusegs m9 lo (bv_unsigned sp) -> mem_inv ctusegs m9 ->
    rw_cells ctusegs m9 3355012 [C4 errv'] ->
    POST (tt, st_fin pf pn) sE
         (MS (mkR ra sp gp (wz RATP) x5 x6 x7 s0 s1 (Z_to_bv 64 A2) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m9 (seg_rom ctusegs)).
  Proof.
    intros until A2. intros SBc NI1 BR1 NI2 BR2 FW2 MU WM ES ST MI ERR.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    set (OW4 := (pn, A2, fnlen) :: lremove (get_func tn st) ((pf, A1, flen) :: lremove (get_file tn st) OW)) in *.
    (* [comment removed for export] *)
    assert (SB9 : SB sE OW4 m9).
    { eapply (seg_base_munch s m OW st E bo0 LB K (bv_unsigned sp) lo B CEIL); [unfold GLOBALS_TOP; lia|lia|exact SBc|exact MU|exact WM|].
      constructor; [left; cbn; lia|]. constructor; [|constructor; [|constructor]].
      - right. right. exists (p_es E), (e_es E), 904. split; [eapply seg_base_es; exact SBc|]. split; [apply (es_writable OW st E bo0 K IDS AS0 KIDS)|cbn; lia].
      - right. right. exists pn, A2, fnlen. split; [subst OW4; left; reflexivity|]. split; [apply FW2|cbn; lia]. }
    destruct SB9 as (HEAP9 & AUX9 & LX9 & AR9 & RB9 & DC9 & DIN9 & KP9 & KOW9 & IES9 & SO9 & FA9).
    destruct (fin_pure pf A1 pn A2 NI1 BR1 NI2 BR2) as (IDS' & IDIN' & GEQ & OF' & OFN' & OD' & REST' & BD' & KIDS' & SH').
    fold OW4 in IDIN', GEQ, OF', OFN', OD', REST', BD'.
    assert (AS9 : ap_state (st_fin pf pn) m9 OW4 E bo0).
    { apply ap_state_join; [apply REST'; exact AR9|exact SH'|rewrite GEQ; exact ES|exact OF'|exact OFN'|exact OD']. }
    assert (DC9' : data_cells m9 OW4 (st_fin pf pn)).
    { apply (data_cells_sub m9 OW4 st); [|intros i q k Hd; exists i; exact Hd|eapply dflags_ok_same; [reflexivity|reflexivity|eapply data_cells_dflags; exact DC9]].
      eapply data_cells_OW; [exact DC9|exact BD']. }
    unfold POST, ap_post.
    exists x5, x6, x7, (Z_to_bv 64 A2), x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, F, fc, m9, OW4, errv', bo0.
    split; [reflexivity|]. split; [exact FRM|]. split; [intros; reflexivity|].
    split; [|split; [exact LX9|split; [exact SO9|split; [exact FA9|split; [|reflexivity]]]]].
    2:{ split; [exact KOW9|]. split; [exact KIDS'|exact KP9]. }
    unfold ap_pre. split; [exact HEAP9|]. split; [exact AS9|]. split; [exact IDS'|]. split; [exact DC9'|]. split; [exact AUX9|]. split; [exact SPB|]. split; [exact B63|].
    split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; exact GLO|]. split; [lia|].
    split. { unfold MallocRep.wz. rewrite EA. exact ERR. } split. { rewrite CAN. eapply RHEAP_ssp. exact HEAP9. } split. { exact MI. } exact SP16.
  Qed.

  (* [comment removed for export] *)
  Lemma ERR_set_debug_tail : forall (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x28 x29 x30 x31 : word) (sE : PState) (mc : mem) (errv2 : word)
      (pf : bptr) (A1 : Z) (pn : bptr) (A2 : Z) (junk j0 : list byte),
    SB sE ((pn, A2, fnlen) :: lremove (get_func tn st) ((pf, A1, flen) :: lremove (get_file tn st) OW)) mc ->
    ~ In pf (map blk_id (lremove (get_file tn st) OW ++ LB)) -> rblock_range A1 flen -> (forall OWd, seg_writable OW st E K OWd pf) ->
    ~ In pn (map blk_id (lremove (get_func tn st) ((pf, A1, flen) :: lremove (get_file tn st) OW) ++ LB)) -> rblock_range A2 fnlen ->
    (forall OWd, seg_writable OW st E K OWd pn) -> In (p_es E, e_es E, 904) (lremove (get_func tn st) ((pf, A1, flen) :: lremove (get_file tn st) OW)) ->
    rw_cells ctusegs mc A2 [CB (Z.to_nat fnlen) junk] ->
    rw_cells ctusegs mc (bv_unsigned sp + -80) (sd_frame j0) ->
    rw_cells ctusegs mc 3355012 [C4 errv2] ->
    stk ctusegs mc lo (bv_unsigned sp + -80) -> mem_inv ctusegs mc ->
    es_raw mc (e_es E) (g2 A1) ->
    implM ctusegs (interp (ap_embed (ARet (tt, st_fin pf pn)))) sE POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 Ln) (Z_to_bv 64 A2) x11 x12 x13 x14 x15 x16 x17
              x18 (Z_to_bv 64 (e_es E + 768 + 8 * Z.of_nat tn)) x20 (Z_to_bv 64 (8 * Z.of_nat tn)) x22
              (Z_to_bv 64 (e_es E + 576 + 8 * Z.of_nat tn)) s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0xe80ac) fc None mc (seg_rom ctusegs)).
  Proof.
    intros until j0. intros SBc NI1 BR1 FW1 NI2 BR2 FW2 IES3 HBLK FR ERR2 ST MI ES.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof TNB as TNB'. pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB]. unfold ERR_NUM in TOPB, BOTB.
    pose proof LITN as (_ & NNN & _ & PADN & LENN & LNL & LNH).
    assert (GL : g_len (g2 A1)).
    { unfold g2, g1. pose proof (g_len_of st (badr OW) SH) as GL0.
      unfold g_len in GL0 |- *; cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot set_g_fi set_g_li] in GL0 |- *; rewrite ?upd_length; exact GL0. }
    pose proof (lit_bytes_at mc Ln nstr nslack fnlen MI LITN) as HS.
    pose proof (bytes_at_bound _ _ _ _ HS) as SBD. rewrite length_app in SBD. cbn [length] in SBD.
    pose proof BR2 as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5).
    unfold sd_frame in FR.
    assert (NEpn : pn <> p_es E).
    { intros EQ. apply NI2. rewrite EQ. rewrite map_app. apply in_app_iff. left. change (p_es E) with (blk_id (p_es E, e_es E, 904)). apply in_map. exact IES3. }
    pose proof (blk_disjoint _ _ _ pn A2 fnlen (p_es E) (e_es E) 904 (seg_base_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SBc)
                  ltac:(apply in_app_iff; left; left; reflexivity) ltac:(apply in_app_iff; left; right; exact IES3) NEpn) as DJ2.
    replace (Z.to_nat fnlen) with (length nstr + 1)%nat in HBLK by lia.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
    assert (EA2 : bv_unsigned (Z_to_bv 64 A2) = A2) by (apply unsigned_lit; lia).
    assert (LENN' : fnlen = Z.of_nat (length nstr) + 1) by (unfold fnlen; lia).
    pose proof (munch_refl [(bv_unsigned sp - 8320, bv_unsigned sp); (e_es E, e_es E + 904); (A2, A2 + fnlen)]%Z mc) as MU. pose proof (wmono_refl ctusegs mc) as WM.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    es_store (es_wr_fu mc (e_es E) _ tn (Z_to_bv 64 A2) ES GL TNB'). name_mem m1.
    step. if_cases KK; zify_cond KK; [exfalso; rewrite ?unsigned_lit in KK by lia; lia|]. clear KK.
    (* [comment removed for export] *)
    step. do 9 step. step. release_frame FR ST (bv_unsigned sp). step. step.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply strcpy_spec with (str := nstr) (slack := nslack) (junk := junk) (lo := lo);
        [exact MI| rewrite unsigned_lit by lia; exact HS| exact NNN| rewrite unsigned_lit by lia; exact PADN
        | rewrite unsigned_lit by lia; exact HBLK| exact ST| lia| lia
        | rewrite !unsigned_lit by lia; lia| rewrite !unsigned_lit by lia; lia| rewrite !unsigned_lit by lia; lia]. }
    intros ms' PO. unfold strcpy_post in PO. rewrite ?EA2 in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m9 & -> & MU9 & WM9 & MI9 & ST9 & DST9).
    eapply es_raw_transport in ES; [|exact GL|exact MU9|exact WM9|cbn; lia].
    eapply rw_cells_transport in ERR2; [|exact MU9|exact WM9|cbn; lia].
    lazymatch type of MU with munch ?W3 _ _ =>
      apply (munch_trans W3 mc m1 m9) in MU; [|eapply (munch_weaken _ W3 m1 m9); [|exact MU9]; unfold sub_fp; cbn [outside]; intros; lia] end.
    apply (wmono_trans ctusegs mc m1 m9) in WM; [|exact WM9].
    apply evt_done. cbn [ap_embed interp impl]. apply evt_done. unfold epost. cbn [fst snd].
    change (set_g_fu (upd (g_fu (g2 A1)) tn (Z_to_bv 64 A2)) (g2 A1)) with (gfin A1 A2) in ES.
    eapply (ERR_set_debug_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ sE mc m9 _ pf A1 pn A2);
      [exact SBc|exact NI1|exact BR1|exact NI2|exact BR2|exact FW2|exact MU|exact WM|exact ES|exact ST9|exact MI9|exact ERR2].
  Qed.

  (* [comment removed for export] *)
  Lemma ERR_set_debug_mid3 : forall (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x28 x29 x30 x31 : word) (sD : PState) (mc : mem) (errv2 : word)
      (pf : bptr) (A1 : Z) (j0 : list byte),
    SB sD (lremove (get_func tn st) ((pf, A1, flen) :: lremove (get_file tn st) OW)) mc ->
    ~ In pf (map blk_id (lremove (get_file tn st) OW ++ LB)) -> rblock_range A1 flen -> (forall OWd, seg_writable OW st E K OWd pf) ->
    rw_cells ctusegs mc (bv_unsigned sp + -80) (sd_frame j0) ->
    rw_cells ctusegs mc 3355012 [C4 errv2] ->
    stk ctusegs mc lo (bv_unsigned sp + -80) -> mem_inv ctusegs mc ->
    es_raw mc (e_es E) (g2 A1) ->
    implM ctusegs (interp (ap_embed (REST3 (st_c pf)))) sD POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 Ln) x10 x11 x12 x13 x14 x15 x16 x17
              x18 (Z_to_bv 64 (e_es E + 768 + 8 * Z.of_nat tn)) x20 (Z_to_bv 64 (8 * Z.of_nat tn)) x22
              (Z_to_bv 64 (e_es E + 576 + 8 * Z.of_nat tn)) s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0xe8084) fc None mc (seg_rom ctusegs)).
  Proof.
    intros until j0. intros SBc NI1 BR1 FW1 FR ERR2 ST MI ES.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof TNB as TNB'. pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB]. unfold ERR_NUM in TOPB, BOTB.
    pose proof LITN as (_ & NNN & _ & PADN & LENN & LNL & LNH).
    assert (GL : g_len (g2 A1)).
    { unfold g2, g1. pose proof (g_len_of st (badr OW) SH) as GL0.
      unfold g_len in GL0 |- *; cbn [g_fl g_ma g_bu g_da g_ds g_df g_fi g_li g_fu g_top g_bot set_g_fi set_g_li] in GL0 |- *; rewrite ?upd_length; exact GL0. }
    destruct (lit_first _ _ _ _ LITN) as (c0 & nstr' & EN & C0).
    pose proof (lit_bytes_at mc Ln nstr nslack fnlen MI LITN) as HS.
    pose proof (bytes_at_bound _ _ _ _ HS) as SBD. rewrite length_app in SBD. cbn [length] in SBD.
    unfold sd_frame in FR.
    pose proof (munch_refl [(bv_unsigned sp - 8320, bv_unsigned sp)]%Z mc) as MU. pose proof (wmono_refl ctusegs mc) as WM.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    step. if_cases KK; zify_cond KK; [exfalso; rewrite ?unsigned_lit in KK by lia; lia|]. clear KK.
    pose proof (u8ro_read ctusegs mc Ln _ 0 c0 (wa (Ln + 0)) HS ltac:(rewrite EN; reflexivity) ltac:(lia) eq_refl) as RD.
    step. clear RD.
    pose proof (bv_unsigned_in_range 8 c0) as C0R. unfold bv_modulus in C0R. cbn in C0R.
    step. if_cases KK; zify_cond KK; [exfalso; rewrite ?unsigned_lit in KK by lia; exact (C0 KK)|]. clear KK.
    (* [comment removed for export] *)
    step. step. step.
    name_mem m1. eapply evt_cut.
    { eapply strlen_spec with (str := nstr) (slack := nslack);
        [rewrite unsigned_lit by lia; exact HS| exact NNN| rewrite unsigned_lit by lia; exact PADN| eassumption]. }
    clear HS. post_call_es ctusegs m1 ES GL.
    match goal with H : bytes_at ctusegs _ _ _ |- _ => rename H into HS end. rewrite unsigned_lit in HS by lia.
    match goal with H : mem_inv ctusegs _ |- _ => rename H into MI0 end.
    (* [comment removed for export] *)
    step. step. step. step.
    setreg 10 (Z_to_bv 64 fnlen) ltac:(f_equal; lia).
    name_mem m2.
    match goal with H : munch _ m1 m2 |- _ => rename H into MU2 end. match goal with H : wmono ctusegs m1 m2 |- _ => rename H into WM2 end.
    assert (SBx : SB sD (lremove (get_func tn st) ((pf, A1, flen) :: lremove (get_file tn st) OW)) m2).
    { eapply (seg_base_munch s m OW st E bo0 LB K (bv_unsigned sp) lo B CEIL); [unfold GLOBALS_TOP; lia|lia|exact SBc|exact MU2|exact WM2|].
      constructor; [left; cbn; lia|constructor]. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
    clear MU2 WM2 SBc.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
      lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
    unfold REST3. unfold abind at 1. unfold amalloc at 1. cbn [apbind ap_embed].
    eapply (CRYPTO_malloc_walk HM) with (B := B) (lo := lo) (n := fnlen);
      [eapply seg_base_heap; exact SBx | eapply seg_base_aux; exact SBx | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia | unfold LX_ERRNO, RATP; exact ERR2 | exact MI0 | reflexivity
      | eapply seg_base_crypto_statics; exact SBx | reflexivity | lia | reflexivity | ].
    intros pn sE msE PO. unfold calloc_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m4 & A2 & errv4
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & BR4 & HEAP4 & (junk & HBLK)).
    replace (ret_pc (Z_to_bv 64 0xe80ac)) with (Z_to_bv 64 0xe80ac) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold LX_ERRNO, RATP in ERR4. change (3355176 - 164) with 3355012 in ERR4.
    cbn [apbind fst snd]. unfold amodify. change (set_func tn (Some (pn, fnlen)) (st_c pf)) with (st_fin pf pn).
    (* [comment removed for export] *)
    assert (SB4 : SB sE ((pn, A2, fnlen) :: lremove (get_func tn st) ((pf, A1, flen) :: lremove (get_file tn st) OW)) m4).
    { eapply (seg_base_malloc s m OW st E bo0 LB K (bv_unsigned sp) B); [exact SBx|exact HP4|lia|exact HEAP4|exact AUX4|exact SO4|exact FA4]. }
    pose proof (LH_nodup _ _ _ HEAP4) as ND4. cbn [map blk_id fst snd] in ND4. apply NoDup_cons_iff in ND4. destruct ND4 as [NI4 _].
    pose proof (fresh_writable s m OW st E bo0 LB K (bv_unsigned sp) B _ _ _ pn SBx NI4) as FW2.
    pose proof (agree_of_heap_pres _ _ _ _ HP4) as AG4.
    apply (rw_cells_agree _ _ _ _ _ AG4) in FR; [| intros a Ha; left; cbn in Ha; lia].
    eapply es_raw_agree in ES; [|exact GL|exact AG4|].
    2:{ intros a Ha. right. right. exists (p_es E, e_es E, 904). split; [|cbn; lia]. apply in_app_iff. left. eapply seg_base_es. exact SBx. }
    eapply (ERR_set_debug_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sE m4 _ pf A1 pn A2 junk j0);
      [exact SB4|exact NI1|exact BR1|exact FW1|exact NI4|exact BR4|exact FW2|eapply seg_base_es; exact SBx|unfold MallocRep.wz in HBLK; exact HBLK|exact FR|exact ERR4|exact ST4|exact MI4|exact ES].
  Qed.

  (* [comment removed for export] *)
  Definition REST2 (pf : bptr) : @AM bptr unit :=
    abind (amodify (fun s1 : ap_st bptr => set_line tn line (set_file tn (Some (pf, flen)) s1))) (fun _ =>
      abind (free_func_slot tn) (fun _ =>
        abind (amalloc fnlen) (fun pn => amodify (set_func tn (Some (pn, fnlen)))))).

  (* [comment removed for export] *)
  Lemma ERR_set_debug_mid2 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (sC : PState) (mc : mem) (errv2 : word)
      (pf : bptr) (A1 : Z) (junk j0 : list byte),
    SB sC ((pf, A1, flen) :: lremove (get_file tn st) OW) mc ->
    ~ In pf (map blk_id (lremove (get_file tn st) OW ++ LB)) -> rblock_range A1 flen -> (forall OWd, seg_writable OW st E K OWd pf) ->
    rw_cells ctusegs mc A1 [CB (Z.to_nat flen) junk] ->
    rw_cells ctusegs mc (bv_unsigned sp + -80) (sd_frame j0) ->
    rw_cells ctusegs mc 3355012 [C4 errv2] ->
    stk ctusegs mc lo (bv_unsigned sp + -80) -> mem_inv ctusegs mc ->
    es_raw mc (e_es E) (g_of st (badr OW)) ->
    implM ctusegs (interp (ap_embed (REST2 pf st_a))) sC POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp (Z_to_bv 64 Ln) (Z_to_bv 64 A1) x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 line) (Z_to_bv 64 (e_es E)) (Z_to_bv 64 Lf) (Z_to_bv 64 (8 * Z.of_nat tn)) (Z_to_bv 64 (Z.of_nat tn))
              (Z_to_bv 64 (e_es E + 576 + 8 * Z.of_nat tn)) s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0xe8028) fc None mc (seg_rom ctusegs)).
  Proof.
    intros until j0. intros SBc NI BR FW1 HBLK FR ERR2 ST MI ES.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof TNB as TNB'. pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB]. unfold ERR_NUM in TOPB, BOTB.
    pose proof LITF as (_ & NNF & _ & PADF & LENF & LFL & LFH).
    assert (GL : g_len (g_of st (badr OW))) by (apply g_len_of; exact SH).
    pose proof (lit_bytes_at mc Lf fstr fslack flen MI LITF) as HS.
    pose proof (bytes_at_bound _ _ _ _ HS) as SBD. rewrite length_app in SBD. cbn [length] in SBD.
    pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5).
    unfold sd_frame in FR.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
    (* [comment removed for export] *)
    assert (NI' : ~ In pf (map blk_id (((pf, A1, flen) :: lremove (get_file tn st) OW) ++ LB)) -> False) by (intros H; apply H; cbn; left; reflexivity).
    assert (NEpf : pf <> p_es E).
    { intros EQ. apply NI. rewrite EQ. rewrite map_app. apply in_app_iff. left. change (p_es E) with (blk_id (p_es E, e_es E, 904)). apply in_map.
      apply lremove_keep; [exact IES|]. intros q n GF. cbn. apply not_eq_sym. eapply ids_es_ne; [exact IDS|eapply es_ids_file; exact GF]. }
    pose proof (blk_disjoint _ _ _ pf A1 flen (p_es E) (e_es E) 904 (seg_base_heap _ _ _ _ _ _ _ _ _ _ _ _ _ SBc)
                  ltac:(apply in_app_iff; left; left; reflexivity) ltac:(apply in_app_iff; left; eapply seg_base_es; exact SBc) NEpf) as DJ1.
    replace (Z.to_nat flen) with (length fstr + 1)%nat in HBLK by lia.
    pose proof (munch_refl [(bv_unsigned sp - 8320, bv_unsigned sp); (e_es E, e_es E + 904); (A1, A1 + flen)]%Z mc) as MU. pose proof (wmono_refl ctusegs mc) as WM.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    es_store (es_wr_fi mc (e_es E) _ tn (Z_to_bv 64 A1) ES GL TNB'). name_mem m1.
    step. if_cases KK; zify_cond KK; [exfalso; rewrite ?unsigned_lit in KK by lia; lia|]. clear KK.
    (* [comment removed for export] *)
    step. step. step.
    name_mem m1'. eapply evt_cut.
    { eapply strcpy_spec with (str := fstr) (slack := fslack) (junk := junk) (lo := lo);
        [eassumption| rewrite unsigned_lit by lia; exact HS| exact NNF| rewrite unsigned_lit by lia; exact PADF
        | rewrite unsigned_lit by lia; exact HBLK| rewrite ESP; exact ST| lia| rewrite ESP; lia
        | rewrite !unsigned_lit by lia; lia| rewrite !unsigned_lit by lia; lia| rewrite !unsigned_lit by lia; lia]. }
    clear HS HBLK. unfold strcpy_post.
    assert (EA1 : bv_unsigned (Z_to_bv 64 A1) = A1) by (apply unsigned_lit; lia).
    assert (LENF' : flen = Z.of_nat (length fstr) + 1) by (unfold flen; lia).
    intros ms' PO; rewrite ?ESP, ?EA1 in PO; revert ms' PO; post_call_es ctusegs m1' ES GL.
    match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST end.
    match goal with H : mem_inv ctusegs _ |- _ => rename H into MI2 end.
    match goal with H : rw_cells ctusegs _ A1 _ |- _ => clear H end.
    name_mem m2.
    (* [comment removed for export] *)
    step.
    step. step. step. step. step. rewrite ?(unsigned_lit (Z.of_nat tn)) by lia. rewrite ?Z.shiftl_mul_pow2 by lia.
    setreg 10 (Z_to_bv 64 (e_es E + 4 * Z.of_nat tn + 704)) ltac:(f_equal; lia).
    es_store (es_wr_li m2 (e_es E) _ tn (Z_to_bv 64 line) ES GL TNB'). name_mem m3.
    setreg 19 (Z_to_bv 64 (e_es E + 768 + 8 * Z.of_nat tn)) ltac:(f_equal; lia).
    pose proof (es_rd_fu m3 (e_es E) _ tn (wa (e_es E + 768 + 8 * Z.of_nat tn)) ES GL TNB' eq_refl) as RD. step. clear RD.
    setreg 10 (wz (optr (badr OW) (get_func tn st))) ltac:(cbn [g_fu g_of set_g_fi set_g_li]; rewrite nth_wl_optr; reflexivity).
    (* [comment removed for export] *)
    step. step. step. step.
    (* [comment removed for export] *)
    assert (SB3 : SB sC ((pf, A1, flen) :: lremove (get_file tn st) OW) m3).
    { eapply (seg_base_munch s m OW st E bo0 LB K (bv_unsigned sp) lo B CEIL); [unfold GLOBALS_TOP; lia|lia|exact SBc|exact MU|exact WM|].
      constructor; [left; cbn; lia|]. constructor; [|constructor; [|constructor]].
      - right. right. exists (p_es E), (e_es E), 904. split; [eapply seg_base_es; exact SBc|]. split; [apply (es_writable OW st E bo0 K IDS AS0 KIDS)|cbn; lia].
      - right. right. exists pf, A1, flen. split; [left; reflexivity|]. split; [apply FW1|cbn; lia]. }
    clear MU WM.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
      lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
    unfold REST2. unfold abind at 1. unfold amodify. cbn [apbind fst snd].
    change (set_line tn line (set_file tn (Some (pf, flen)) st_a)) with (st_b pf).
    unfold abind at 1. rewrite free_func_slot_tree, apbind_ofree. cbn [apbind fst snd].
    change (get_func tn (st_b pf)) with (get_func tn st). change (set_func tn None (st_b pf)) with (st_c pf).
    change (abind (amalloc fnlen) _ (st_c pf)) with (REST3 (st_c pf)).
    rewrite (ap_embed_ofree (option_map fst (get_func tn st))).
    eapply (CRYPTO_free_opt_walk HF) with (B := B) (lo := lo) (od := get_func tn st) (adr := badr OW) (L := ((pf, A1, flen) :: lremove (get_file tn st) OW) ++ LB);
      [eapply seg_base_heap; exact SB3 | | eapply seg_base_aux; exact SB3 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR2 | exact MI2 | reflexivity
      | eapply seg_base_crypto_statics; exact SB3 | reflexivity | ].
    { destruct (get_func tn st) as [[qn nn]|] eqn:GN; [|exact I]. cbn [app]. right. apply in_app_iff. left.
      apply lremove_keep; [exact (proj1 (optb_ok_nth OW _ tn qn nn OFN GN))|].
      intros q n GF. cbn. apply not_eq_sym. eapply ids_file_func_ne; [exact IDS|exact GF|exact GN]. }
    intros sD msD PO. unfold ofree_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m4
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & HEAP4).
    replace (ret_pc (Z_to_bv 64 0xe8084)) with (Z_to_bv 64 0xe8084) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold LX_ERRNO, RATP in ERR4. change (3355176 - 164) with 3355012 in ERR4.
    (* [comment removed for export] *)
    assert (SB4 : SB sD (lremove (get_func tn st) ((pf, A1, flen) :: lremove (get_file tn st) OW)) m4).
    { eapply (seg_base_free s m OW st E bo0 LB K (bv_unsigned sp) B); [exact SB3| |exact HP4|lia|exact HEAP4|exact AUX4|exact SO4|exact FA4].
      intros q n GN. split; [|split].
      - cbn [map blk_id fst snd]. right. pose proof (proj1 (optb_ok_nth OW _ tn q n OFN GN)) as HIn. change q with (blk_id (q, badr OW q, n)). apply in_map.
        apply lremove_keep; [exact HIn|]. intros q' n' GF. cbn. apply not_eq_sym. eapply ids_file_func_ne; [exact IDS|exact GF|exact GN].
      - split; [eapply func_not_rest; [exact IDS|exact GN]|]. split; [intros i q' k Hd EQ; subst q'; exact (ids_func_data_ne E st tn i q n q k IDS GN Hd eq_refl)|].
        eapply K_not_es; [exact KIDS|eapply es_ids_func; exact GN].
      - eapply ids_es_ne; [exact IDS|eapply es_ids_func; exact GN]. }
    pose proof (agree_of_heap_pres _ _ _ _ HP4) as AG4.
    apply (rw_cells_agree _ _ _ _ _ AG4) in FR; [| intros a Ha; left; cbn in Ha; lia].
    eapply es_raw_agree in ES; [|exact GL|exact AG4|].
    2:{ intros a Ha. right. right. exists (p_es E, e_es E, 904). split; [|cbn; lia].
        apply lremove_keep; [apply in_app_iff; left; eapply seg_base_es; exact SB3|]. intros q n GN. cbn. apply not_eq_sym. eapply ids_es_ne; [exact IDS|eapply es_ids_func; exact GN]. }
    eapply (ERR_set_debug_mid3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sD m4 _ pf A1 j0);
      [exact SB4|exact NI|exact BR|exact FW1|exact FR|exact ERR4|exact ST4|exact MI4|exact ES].
  Qed.

  (* [comment removed for export] *)
  Definition REST1 : @AM bptr unit :=
    abind (amalloc flen) (fun pf =>
      abind (amodify (fun s1 : ap_st bptr => set_line tn line (set_file tn (Some (pf, flen)) s1))) (fun _ =>
        abind (free_func_slot tn) (fun _ =>
          abind (amalloc fnlen) (fun pn => amodify (set_func tn (Some (pn, fnlen))))))).

  (* [comment removed for export] *)
  Lemma ERR_set_debug_mid1 : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (sB : PState) (mc : mem) (errv2 : word) (j0 : list byte),
    SB sB (lremove (get_file tn st) OW) mc ->
    rw_cells ctusegs mc (bv_unsigned sp + -80) (sd_frame j0) ->
    rw_cells ctusegs mc 3355012 [C4 errv2] ->
    stk ctusegs mc lo (bv_unsigned sp + -80) -> mem_inv ctusegs mc ->
    es_raw mc (e_es E) (g_of st (badr OW)) ->
    implM ctusegs (interp (ap_embed (REST1 st_a))) sB POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (Z_to_bv 64 RATP) x5 x6 x7 sp (Z_to_bv 64 Ln) x10 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 line) (Z_to_bv 64 (e_es E)) (Z_to_bv 64 Lf) (Z_to_bv 64 (8 * Z.of_nat tn)) (Z_to_bv 64 (Z.of_nat tn))
              (Z_to_bv 64 (e_es E + 576 + 8 * Z.of_nat tn)) s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0xe8000) fc None mc (seg_rom ctusegs)).
  Proof.
    intros until j0. intros SBc FR ERR2 ST MI ES.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof TNB as TNB'. pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB]. unfold ERR_NUM in TOPB, BOTB.
    pose proof LITF as (_ & NNF & _ & PADF & LENF & LFL & LFH).
    assert (GL : g_len (g_of st (badr OW))) by (apply g_len_of; exact SH).
    destruct (lit_first _ _ _ _ LITF) as (c0 & fstr' & EF & C0).
    pose proof (lit_bytes_at mc Lf fstr fslack flen MI LITF) as HS.
    pose proof (bytes_at_bound _ _ _ _ HS) as SBD. rewrite length_app in SBD. cbn [length] in SBD.
    unfold sd_frame in FR.
    pose proof (munch_refl [(bv_unsigned sp - 8320, bv_unsigned sp)]%Z mc) as MU. pose proof (wmono_refl ctusegs mc) as WM.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    step. if_cases KK; zify_cond KK; [exfalso; rewrite ?unsigned_lit in KK by lia; lia|]. clear KK.
    pose proof (u8ro_read ctusegs mc Lf _ 0 c0 (wa (Lf + 0)) HS ltac:(rewrite EF; reflexivity) ltac:(lia) eq_refl) as RD.
    step. clear RD.
    pose proof (bv_unsigned_in_range 8 c0) as C0R. unfold bv_modulus in C0R. cbn in C0R.
    step. if_cases KK; zify_cond KK; [exfalso; rewrite ?unsigned_lit in KK by lia; exact (C0 KK)|]. clear KK.
    (* [comment removed for export] *)
    step. step. step.
    name_mem m1. eapply evt_cut.
    { eapply strlen_spec with (str := fstr) (slack := fslack);
        [rewrite unsigned_lit by lia; exact HS| exact NNF| rewrite unsigned_lit by lia; exact PADF| eassumption]. }
    clear HS. post_call ctusegs m1.
    match goal with H : bytes_at ctusegs _ _ _ |- _ => rename H into HS end. rewrite unsigned_lit in HS by lia.
    replace (ret_pc (Z_to_bv 64 0xe8018)) with (Z_to_bv 64 0xe8018) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    step. step. step. step.
    setreg 10 (Z_to_bv 64 flen) ltac:(f_equal; lia).
    name_mem m2.
    match goal with H : munch _ m1 m2 |- _ => rename H into MU2 end. match goal with H : wmono ctusegs m1 m2 |- _ => rename H into WM2 end.
    assert (SBx : SB sB (lremove (get_file tn st) OW) m2).
    { eapply (seg_base_munch s m OW st E bo0 LB K (bv_unsigned sp) lo B CEIL); [unfold GLOBALS_TOP; lia|lia|exact SBc|exact MU2|exact WM2|].
      constructor; [left; cbn; lia|constructor]. }
    eapply es_raw_transport in ES; [|exact GL|exact MU2|exact WM2|cbn; lia].
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
    clear MU2 WM2 SBc.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
      lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
    unfold REST1. unfold abind at 1. unfold amalloc at 1. cbn [apbind ap_embed].
    eapply (CRYPTO_malloc_walk HM) with (B := B) (lo := lo) (n := flen);
      [eapply seg_base_heap; exact SBx | eapply seg_base_aux; exact SBx | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia | unfold LX_ERRNO, RATP; exact ERR2 | exact MI0 | reflexivity
      | eapply seg_base_crypto_statics; exact SBx | reflexivity | lia | reflexivity | ].
    intros pf sC msC PO. unfold calloc_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m4 & A1 & errv4
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & BR4 & HEAP4 & (junk & HBLK)).
    replace (ret_pc (Z_to_bv 64 0xe8028)) with (Z_to_bv 64 0xe8028) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold LX_ERRNO, RATP in ERR4. change (3355176 - 164) with 3355012 in ERR4.
    cbn [apbind fst snd].
    (* [comment removed for export] *)
    assert (SB4 : SB sC ((pf, A1, flen) :: lremove (get_file tn st) OW) m4).
    { eapply (seg_base_malloc s m OW st E bo0 LB K (bv_unsigned sp) B); [exact SBx|exact HP4|lia|exact HEAP4|exact AUX4|exact SO4|exact FA4]. }
    pose proof (LH_nodup _ _ _ HEAP4) as ND4. cbn [map blk_id fst snd] in ND4. apply NoDup_cons_iff in ND4. destruct ND4 as [NI4 _].
    pose proof (fresh_writable s m OW st E bo0 LB K (bv_unsigned sp) B _ _ _ pf SBx NI4) as FW1.
    pose proof (agree_of_heap_pres _ _ _ _ HP4) as AG4.
    apply (rw_cells_agree _ _ _ _ _ AG4) in FR; [| intros a Ha; left; cbn in Ha; lia].
    eapply es_raw_agree in ES; [|exact GL|exact AG4|].
    2:{ intros a Ha. right. right. exists (p_es E, e_es E, 904). split; [|cbn; lia]. apply in_app_iff. left. eapply seg_base_es. exact SBx. }
    eapply (ERR_set_debug_mid2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sC m4 _ pf A1 junk j0);
      [exact SB4|exact NI4|exact BR4|exact FW1|unfold MallocRep.wz in HBLK; exact HBLK|exact FR|exact ERR4|exact ST4|exact MI4|exact ES].
  Qed.

  (* [comment removed for export] *)
  Lemma ERR_set_debug_act : forall (tp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (errv : word),
    RHEAP s (OW ++ LB) m -> ap_state st m OW E bo0 -> data_cells m OW st -> rauxv_ok m B ->
    stk ctusegs m lo (bv_unsigned sp) -> rw_cells ctusegs m 3355012 [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP ->
    implM ctusegs (interp (ap_embed (err_set_debug rs st))) s POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz Lf) (wz line) (wz Ln) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ERR_SET_DEBUG) fc None m (seg_rom ctusegs)).
  Proof.
    intros until errv. intros HEAP AS DC AUX ST ERR MI ->.
    unfold ERR_SET_DEBUG, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (munch_refl [(bv_unsigned sp - 80 - 1024, bv_unsigned sp); (3355012, 3355012 + 4)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    unfold err_set_debug. unfold abind at 1. unfold aget. cbn [apbind fst snd].
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 80%nat ST. do 10 step. do 5 step. step.
    name_mem m1.
    assert (AS1 : ap_state st m1 OW E bo0).
    { eapply (ap_state_of_munch st m m1); [exact AS|exact HEAP|exact INCL|exact MU|exact WM|exact CEIL|unfold GLOBALS_TOP; exact GLO|].
      constructor; [cbn; lia|]. constructor; [right; reflexivity|constructor]. }
    assert (HEAP1 : RHEAP s (OW ++ LB) m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [apply W_ok_errno|constructor]. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
    eapply evt_cut.
    { eapply (get_state_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 lo s (OW ++ LB) OW E st bo0 errv 1);
        [exact AS1|exact HEAP1|exact INCL|rewrite ESP; exact ST|exact CEIL|unfold GLOBALS_TOP; lia|rewrite ESP; lia|rewrite ESP; clear - SP16 SPR GLO LO;
         replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) by lia; rewrite Zminus_mod, SP16; reflexivity
        |exact ERR|exact MI|reflexivity|right; reflexivity|reflexivity]. }
    post_call_esp ESP m1.
    match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST end.
    match goal with H : rw_cells ctusegs _ 3355012 _ |- _ => rename H into ERR2 end.
    match goal with H : mem_inv ctusegs _ |- _ => rename H into MI2 end.
    name_mem m2. clear AS1 HEAP1.
    assert (AS2 : ap_state st m2 OW E bo0).
    { eapply (ap_state_of_munch st m m2); [exact AS|exact HEAP|exact INCL|exact MU|exact WM|exact CEIL|unfold GLOBALS_TOP; exact GLO|].
      constructor; [cbn; lia|]. constructor; [right; reflexivity|constructor]. }
    destruct (seg_close s OW LB _ m m2 lo (bv_unsigned sp) B HEAP AUX CEIL ltac:(unfold GLOBALS_TOP; lia) ltac:(lia) MU WM) as (HEAP2 & AUX2 & LX2).
    { constructor; [left; cbn; lia|]. constructor; [right; left; reflexivity|constructor]. }
    assert (DIN : forall i q k, get_data i st = Some (q, k) -> In (q, badr OW q, k) (OW ++ LB)).
    { intros i q k Hd. apply INCL. exact (proj1 (optb_ok_nth OW _ i q k OD Hd)). }
    assert (DC2 : data_cells m2 OW st).
    { eapply (data_cells_of_munch s (OW ++ LB) _ m m2); [exact DC|exact DIN|exact HEAP|exact CEIL|exact MU|exact WM|].
      constructor; [left; cbn; lia|]. constructor; [|constructor]. right. left. reflexivity. }
    assert (KP2 : kept K m m2).
    { eapply (kept_of_munch s (OW ++ LB) _ m m2 K lo); [exact HEAP|intros b Hb; apply INCL; apply KOW; exact Hb|exact CEIL|exact MU|].
      constructor; [left; cbn; lia|]. constructor; [|constructor]. right. left. reflexivity. }
    assert (SB2 : SB s OW m2).
    { eapply seg_base_intro; [exact HEAP2|exact AUX2|exact LX2|exact AS2|exact DC2|exact KP2|exact KOW]. }
    clear MU WM AS HEAP AUX DC m1 HEAP2 AUX2 LX2 DC2 KP2.
    pose proof (ap_state_es _ _ _ _ _ AS2) as (ES & GL & _).
    step. if_cases KK; zify_cond KK; [exfalso; rewrite ?unsigned_lit in KK by lia; lia|]. clear KK.
    (* [comment removed for export] *)
    step.
    pose proof (es_rd_top m2 (e_es E) _ _ ES eq_refl) as RD. unfold MallocRep.wz in RD |- *. step. clear RD.
    pose proof (ids_ok_top _ _ IDS) as [TOPB BOTB]. unfold ERR_NUM in TOPB, BOTB.
    cbn [g_top g_of]. rewrite !sx32_small by lia. fold tn.
    (* [comment removed for export] *)
    step. step. rewrite ?(unsigned_lit (Z.of_nat tn)) by lia. rewrite ?Z.shiftl_mul_pow2 by lia.
    pose proof TNB as TNB'.
    setreg 21 (Z_to_bv 64 (8 * Z.of_nat tn)) ltac:(f_equal; lia).
    ub.
    setreg 23 (Z_to_bv 64 (e_es E + 576 + 8 * Z.of_nat tn)) ltac:(f_equal; lia).
    pose proof (es_rd_fi m2 (e_es E) _ tn (wa (e_es E + 576 + 8 * Z.of_nat tn)) ES GL TNB' eq_refl) as RD. step. clear RD.
    setreg 10 (wz (optr (badr OW) (get_file tn st))) ltac:(cbn [g_fi g_of]; rewrite nth_wl_optr; reflexivity).
    (* [comment removed for export] *)
    step. step. step. step.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
      lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
    unfold abind at 1. rewrite free_file_slot_tree, apbind_ofree. cbn [apbind fst snd].
    change (abind (amalloc (rs_flen rs)) _ st_a) with (REST1 st_a).
    rewrite (ap_embed_ofree (option_map fst (get_file tn st))).
    eapply (CRYPTO_free_opt_walk HF) with (B := B) (lo := lo) (od := get_file tn st) (adr := badr OW) (L := OW ++ LB);
      [eapply seg_base_heap; exact SB2 | | destruct SB2 as (_ & AUX2 & _); exact AUX2 | rewrite ESP; lia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; lia
      | rewrite ESP; unfold CRYPTO_FREE_STACK, RFREE_STACK; lia | unfold LX_ERRNO, RATP; exact ERR2 | exact MI2 | reflexivity
      | eapply seg_base_crypto_statics; exact SB2 | reflexivity | ].
    { destruct (get_file tn st) as [[qf nf]|] eqn:GF; [|exact I]. apply INCL. exact (proj1 (optb_ok_nth OW _ tn qf nf OF GF)). }
    intros sB msB PO. unfold ofree_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP3 & FA3 & SO3 & HEAP3).
    replace (ret_pc (Z_to_bv 64 0xe8000)) with (Z_to_bv 64 0xe8000) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold LX_ERRNO, RATP in ERR3. change (3355176 - 164) with 3355012 in ERR3.
    (* [comment removed for export] *)
    assert (SB3 : SB sB (lremove (get_file tn st) OW) m3).
    { eapply (seg_base_free s m OW st E bo0 LB K (bv_unsigned sp) B); [exact SB2| |exact HP3|lia|exact HEAP3|exact AUX3|exact SO3|exact FA3].
      intros q n GF. split; [|split].
      - pose proof (proj1 (optb_ok_nth OW _ tn q n OF GF)) as HIn. change q with (blk_id (q, badr OW q, n)). apply in_map. exact HIn.
      - split; [eapply file_not_rest; [exact IDS|exact GF]|]. split; [intros i q' k Hd EQ; subst q'; exact (ids_file_data_ne E st tn i q n q k IDS GF Hd eq_refl)|].
        eapply K_not_es; [exact KIDS|eapply es_ids_file; exact GF].
      - eapply ids_es_ne; [exact IDS|eapply es_ids_file; exact GF]. }
    pose proof (agree_of_heap_pres _ _ _ _ HP3) as AG3.
    apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros a Ha; left; cbn in Ha; lia].
    eapply es_raw_agree in ES; [|exact GL|exact AG3|].
    2:{ intros a Ha. right. right. exists (p_es E, e_es E, 904). split; [|cbn; lia].
        apply lremove_keep; [apply in_app_iff; left; exact IES|]. intros q n GF. cbn. apply not_eq_sym. eapply ids_es_ne; [exact IDS|eapply es_ids_file; exact GF]. }
    eapply (ERR_set_debug_mid1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sB m3 _ _); [exact SB3|exact FR|exact ERR3|exact ST3|exact MI3|exact ES].
  Qed.
  End Act.

  (* [comment removed for export] *)
  Theorem ERR_set_debug_walk : forall rs file func, ERR_set_debug_spec rs file func.
  Proof using HF HM.
    intros rs file func bo0 fstr fslack nstr nslack LITF LITN. unfold ap_stmt. intros until K. intros PRE TP FRM (A0 & A1 & A2 & EBO) KOW KIDS. subst bo a0 a1 a2.
    destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & SSP & MI & SP16).
    unfold ERR_SET_DEBUG_STACK, GLOBALS_TOP in *.
    assert (EA : errno_addr (Z_to_bv 64 RATP) = 3355012) by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    pose proof ERR as ERR'. unfold MallocRep.wz in ERR'. rewrite EA in ERR'.
    pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & SH & IES & EESP & EESB & EES16 & OF & OFN & OD). unfold ES_SIZE in IES, EESB.
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    pose proof (blk_bounds _ _ _ _ _ _ HEAP (INCL _ IES)) as (_ & _ & EESC & EESI & _).
    pose proof (ssp_canary_0 _ _ _ _ HEAP SSP) as CAN.
    pose proof (ids_in_intro _ _ _ _ _ AS) as IDIN.
    eapply (ERR_set_debug_act ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s st OW LB E bo0 lo B canary rs file func fstr fslack nstr nslack);
      first [exact IDS|exact SPB|exact B63|exact CEIL|exact GLO|exact LO|exact SP16|exact FRM|exact SH|exact IES|exact EESP|exact EESC|exact EESI|exact EES16
            |exact OF|exact OFN|exact OD|exact (ex_intro _ m AS)|exact IDIN|exact CAN|unfold errno_addr in EA; exact EA|exact LITF|exact LITN
            |exact KOW|exact KIDS|exact HEAP|exact AS|exact DC|exact AUX|exact ST|exact ERR'|exact MI|exact TP].
  Qed.

  (* [comment removed for export] *)
  Lemma ERR_set_debug_spec_stmt : forall rs file func fstr fslack nstr nslack,
    lit_ok file fstr fslack (rs_flen rs) -> lit_ok func nstr nslack (rs_fnlen rs) ->
    ERR_set_debug_spec rs file func -> ERR_set_debug_stmt rs file func.
  Proof.
    intros rs file func fstr fslack nstr nslack LF LN H. unfold ERR_set_debug_stmt, ERR_set_debug_spec, ap_stmt in *. intros until K. intros PRE TP FRM (A0 & A1 & A2) KOW KIDS.
    eapply implM_mono; [eapply (H bo fstr fslack nstr nslack LF LN); [exact PRE|exact TP|exact FRM|repeat split; assumption|exact KOW|exact KIDS]|].
    intros r s' ms' PO. eapply W_err_new.ap_post_mono; [|exact PO]. intros; exact I.
  Qed.
End Proofs.
End WithCeiling0.
