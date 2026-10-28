(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AEvt HeapIface CellsX Cells Mem Step Frame Tac AStep Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_asn1_get_tag U_asn1_get_alg_A U_oid U_x509_get_name_A U_pkcs7_getsig U_pkcs7_signer.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import H3Tac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.
Open Scope Z_scope.
Set Printing Width 200.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac is_arith_goal :=
  lazymatch goal with
  | |- @eq Z _ _ => idtac | |- (_ <= _)%Z => idtac | |- (_ < _)%Z => idtac | |- (_ >= _)%Z => idtac | |- (_ > _)%Z => idtac
  | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- ~ _ => idtac | |- _ <> _ => idtac | |- False => idtac | |- True => idtac
  | |- @eq nat _ _ => idtac | |- (_ <= _)%nat => idtac | |- (_ < _)%nat => idtac | |- Z.divide _ _ => idtac
  end.
Ltac al8_close k := exfalso; rewrite ?unsigned_lit in k by lia; change 7 with (Z.ones 3) in k; rewrite Z.land_ones in k by lia; change (2 ^ 3) with 8 in k; lia.

Definition U_PKCS7_GETSIGNERS : Z := 0x1dfe8.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Facts.
  Variable segs : list Segment.
  Variable L : heap_layout.

  (* [comment removed for export] *)
  Fixpoint splink (m : mem) (LB : list blk) (a : Z) (l : list (Z * list Z)) (e : Z) {struct l} : Prop :=
    match l with
    | [] => a = e
    | (a', names) :: r => a = a' /\ In (a, SIGNER_SIZE) LB /\ a mod 16 = 0 /\ 0 < a
        /\ exists (inext nxt : Z) (j : signer_junk),
             rw_cells segs m a (signer_cells inext nxt j)
             /\ name_chain segs (fun _ => True) m LB inext names
             /\ splink m LB nxt r e
    end.

  #[using="Type"] Lemma splink_to_chain : forall m LB a l, splink m LB a l 0 -> signer_chain segs m LB a l.
  Proof.
    intros m LB a l. revert a. induction l as [|[a' ns] r IH]; cbn; intros a H; [exact H|].
    ddestruct H as (E & Hin & Hal & Hpos & inext & nxt & j & HR & HN & HC).
    refine (conj E (conj Hin (conj Hal (conj Hpos _)))). dexists inext, nxt, j. exact (conj HR (conj HN (IH _ HC))).
  Qed.

  #[using="Type"] Lemma splink_snoc : forall m LB a l e names inext nxt j,
    splink m LB a l e ->
    In (e, SIGNER_SIZE) LB -> e mod 16 = 0 -> 0 < e ->
    rw_cells segs m e (signer_cells inext nxt j) -> name_chain segs (fun _ => True) m LB inext names ->
    splink m LB a (l ++ [(e, names)]) nxt.
  Proof.
    intros m LB a l e names inext nxt j. revert a. induction l as [|[a' ns] r IH]; cbn; intros a H Hin Hal Hpos HR HN.
    - subst a. refine (conj eq_refl (conj Hin (conj Hal (conj Hpos _)))). dexists inext, nxt, j. exact (conj HR (conj HN eq_refl)).
    - ddestruct H as (E & Hin' & Hal' & Hpos' & inext' & nxt' & j' & HR' & HN' & HC').
      refine (conj E (conj Hin' (conj Hal' (conj Hpos' _)))). dexists inext', nxt', j'. exact (conj HR' (conj HN' (IH _ HC' Hin Hal Hpos HR HN))).
  Qed.

  #[using="Type"] Lemma splink_nodes_in : forall m LB a l e, splink m LB a l e -> forall x, In x (map fst l) -> In (x, SIGNER_SIZE) LB.
  Proof.
    intros m LB a l e. revert a. induction l as [|[a' ns] r IH]; cbn; intros a H x Hx; [destruct Hx|].
    ddestruct H as (-> & Hin & _ & _ & inext & nxt & j & _ & _ & HC). destruct Hx as [<-|Hx]; [exact Hin| exact (IH _ HC x Hx)].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma splink_mem : forall m m' LB LB' a l e,
    splink m LB a l e ->
    (forall x, In x (map fst l) -> In (x, SIGNER_SIZE) LB -> In (x, SIGNER_SIZE) LB') ->
    (forall x cs, In (x, SIGNER_SIZE) LB -> In x (map fst l) -> rw_cells segs m x cs -> Z.of_nat (cells_size cs) = SIGNER_SIZE -> rw_cells segs m' x cs) ->
    (forall inext names, In names (map snd l) -> name_chain segs (fun _ => True) m LB inext names -> name_chain segs (fun _ => True) m' LB' inext names) ->
    splink m' LB' a l e.
  Proof.
    intros m m' LB LB' a l e. revert a. induction l as [|[a' ns] r IH]; cbn; intros a H HL HM HN; [exact H|].
    ddestruct H as (-> & Hin & Hal & Hpos & inext & nxt & j & HR & HNc & HC).
    refine (conj eq_refl (conj (HL _ (or_introl eq_refl) Hin) (conj Hal (conj Hpos _)))). dexists inext, nxt, j.
    split; [apply HM; [exact Hin| left; reflexivity| exact HR| reflexivity] |].
    split; [apply HN; [left; reflexivity| exact HNc] |].
    apply IH; [exact HC| intros x Hl Hx; apply HL; [right; exact Hl| exact Hx] | intros x cs Hx Hl; apply HM; [exact Hx| right; exact Hl] | intros i n Hi; apply HN; right; exact Hi].
  Qed.

  (* [comment removed for export] *)
  Fixpoint sbl (l : list (Z * list Z)) : list blk :=
    match l with [] => [] | (a, ns) :: r => sbl r ++ SNAME (rev ns) ++ [(a, SIGNER_SIZE)] end.

  #[using="Type"] Lemma sbl_app : forall l1 l2, sbl (l1 ++ l2) = sbl l2 ++ sbl l1.
  Proof. induction l1 as [|[a ns] r IH]; intros l2; cbn; [rewrite app_nil_r; reflexivity|]. rewrite IH, <- !app_assoc. reflexivity. Qed.

  #[using="Type"] Lemma SNAME_app : forall l1 l2, SNAME (l1 ++ l2) = SNAME l1 ++ SNAME l2.
  Proof. intros. unfold SNAME. apply map_app. Qed.

  #[using="Type"] Lemma perm_SNAME_rev : forall ns, Permutation (SNAME (rev ns)) (SNAME ns).
  Proof. intros ns. unfold SNAME. apply Permutation_map. apply Permutation_sym. apply Permutation_rev. Qed.

  #[using="Type"] Lemma sbl_perm : forall l, Permutation (sbl l) (signer_blocks l).
  Proof.
    induction l as [|[a ns] r IH]; cbn; [apply Permutation_refl|].
    eapply Permutation_trans; [apply Permutation_app_comm|].
    apply Permutation_app; [| exact IH]. apply Permutation_app; [| apply Permutation_refl].
    unfold SNAME. apply Permutation_map. apply Permutation_sym. apply Permutation_rev.
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L18797602918.1500000;S1C1j1B1k1H". (* [comment removed for export] *)
  #[using="Type"] Lemma blocks_apart_neq : forall LB b1 b2,
    blocks_apart LB -> In b1 LB -> In b2 LB -> b1 <> b2 -> 0 < snd b1 -> 0 < snd b2 ->
    fst b1 + snd b1 <= fst b2 \/ fst b2 + snd b2 <= fst b1.
  Proof.
    induction LB as [|[C j] r IH]; cbn; intros b1 b2 HA H1 H2 HNE P1 P2; [destruct H1|].
    destruct HA as [HC Hr].
    destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
    - exfalso. apply HNE. congruence.
    - subst b1. destruct b2 as [B k]. cbn in *. exact (HC B k H2).
    - subst b2. destruct b1 as [B k]. cbn in *. destruct (HC B k H1); lia.
    - apply IH; assumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L14032635446.23L15232621741.23L35485063351.2300000400800<S2a'S2a'S2a'". (* [comment removed for export] *)
  #[using="Type"] Lemma signer_chain_free_other : forall m m' LB SP A a l,
    signer_chain segs m LB a l ->
    (forall b, In b (signer_blocks l) -> fst b <> A) ->
    heap_pres segs L (lb_remove A LB) SP m m' ->
    signer_chain segs m' (lb_remove A LB) a l.
  Proof.
    intros m m' LB SP A a l. revert a. induction l as [|[a' ns] r IH]; cbn; intros a H HNE HP; [exact H|].
    ddestruct H as (-> & Hin & Hal & Hpos & inext & nxt & j & HR & HN & HC).
    assert (HIN' : In (a', SIGNER_SIZE) (lb_remove A LB)).
    { apply In_lb_remove_keep'; [exact Hin|]. apply (HNE (a', SIGNER_SIZE)). apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
    refine (conj eq_refl (conj HIN' (conj Hal (conj Hpos _)))). dexists inext, nxt, j.
    split; [eapply heap_pres_rw_cells; [exact HP| exact HR| eapply client_range_block; [exact HIN'| lia| cbn; unfold SIGNER_SIZE; lia]] |].
    split; [eapply chain_free_other; [exact HN| | exact HP| unfold NAME_SIZE; lia] |].
    - intros x Hx ->. apply (HNE (A, NAME_SIZE)); [| reflexivity]. apply in_or_app. left. apply in_or_app. left. apply (in_map (fun a => (a, NAME_SIZE))). exact Hx.
    - apply IH; [exact HC| | exact HP]. intros b Hb. apply HNE. apply in_or_app. right. exact Hb.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="Type"] Lemma map_fst_SNAME : forall l, map fst (SNAME l) = l.
  Proof. intros l. unfold SNAME. rewrite map_map. cbn. apply map_id. Qed.

  #[using="Type"] Lemma nodup4 : forall (A B C D : list Z), List.NoDup (A ++ B ++ C ++ D) ->
    List.NoDup B /\ (forall x, In x B -> ~ In x A) /\ (forall x, In x B -> ~ In x C) /\ (forall x, In x C -> ~ In x A).
  Proof.
    intros A B C D N. split; [| split; [| split]].
    - apply NoDup_app_inv_r in N. apply NoDup_app_inv_l in N. exact N.
    - intros x Hx. eapply NoDup_app_notin_l; [exact N|]. apply in_or_app. left. exact Hx.
    - intros x Hx HC. apply NoDup_app_inv_r in N. exact (NoDup_app_notin_l B (C ++ D) x N ltac:(apply in_or_app; left; exact HC) Hx).
    - intros x Hx. eapply NoDup_app_notin_l; [exact N|]. apply in_or_app. right. apply in_or_app. left. exact Hx.
  Qed.

  #[using="Type"] Lemma PERMc : forall sg names0, Permutation (sbl sg ++ SNAME (rev names0)) (SNAME names0 ++ signer_blocks sg).
  Proof.
    intros sg names0. eapply Permutation_trans; [apply Permutation_app_comm|]. apply Permutation_app; [apply perm_SNAME_rev| apply sbl_perm].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma lb_remove_mid0 : forall x k (A B : list blk), ~ In x (map fst A) -> lb_remove x (A ++ (x, k) :: B) = A ++ B.
  Proof.
    intros x k A B HA. rewrite lb_remove_notfirst; [cbn; rewrite Z.eqb_refl; reflexivity|].
    intros k' Hk'. apply HA. replace x with (fst (x, k')) by reflexivity. apply in_map. exact Hk'.
  Qed.
  #[using="Type"] Lemma lb_remove_mid : forall x k (A B : list blk), ~ In x (map fst A) -> lb_remove x (A ++ (x, k) :: B) = A ++ B.
  Proof. exact lb_remove_mid0. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma rm_node : forall (A B : list blk) x rest, ~ In x (map fst A) -> ~ In x rest ->
    lb_remove x (A ++ SNAME (rev (x :: rest)) ++ B) = A ++ SNAME (rev rest) ++ B.
  Proof.
    intros A B x rest HA Hr. cbn [rev]. rewrite SNAME_app.
    replace (A ++ (SNAME (rev rest) ++ SNAME [x]) ++ B) with ((A ++ SNAME (rev rest)) ++ (x, NAME_SIZE) :: B) by (cbn; repeat rewrite <- app_assoc; reflexivity).
    rewrite lb_remove_mid0; [repeat rewrite <- app_assoc; reflexivity|].
    rewrite map_app, map_fst_SNAME. intros Hx. apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [exact (HA Hx)| apply Hr; apply in_rev; exact Hx].
  Qed.
  #[using="Type"] Lemma in_node : forall (A B : list blk) x rest, In x (map fst (A ++ SNAME (rev (x :: rest)) ++ B)).
  Proof. intros. rewrite !map_app. apply in_or_app. right. apply in_or_app. left. rewrite map_fst_SNAME, <- in_rev. left. reflexivity. Qed.
End Facts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = 0x3fa98.
  Hypothesis HCALLOC : hl_calloc L = 0x3f960.
  Hypothesis HMSF : const_at L U_MEMSET_FUNC 8.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  Hypothesis GETALG : asn1_get_alg_stmt usegs L U_ASN1_GET_ALG U_MEMSET_FUNC.

  Let SIGNER : pkcs7_signer_stmt usegs L HI U_PKCS7_SIGNER U_MEMSET_FUNC
    := U_pkcs7_signer_spec L HI HFREE HCALLOC HMSF HLS SW DIMG DHI GETALG.

  Section Body.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
              (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk) (PP P END BUF SIG DALG lo : Z) (bs : list byte)
              (dtg dpad : word) (dlen dq : Z) (sj : signer_junk).
    Hypothesis HH : HEAP usegs L HI h LB m mo.
    Hypothesis HPP : rw_cells usegs m PP [C8 (Z_to_bv 64 P)].
    Hypothesis ALP : PP mod 8 = 0.
    Hypothesis BY : bytes_at usegs m BUF bs.
    Hypothesis BIN : In (BUF, Z.of_nat (length bs)) LB.
    Hypothesis B1 : BUF <= P.  Hypothesis B2 : P <= END.  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
    Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.  Hypothesis B5 : 0 < BUF.
    Hypothesis B6 : Z.of_nat (length bs) < 2 ^ 30.
    Hypothesis HS : rw_cells usegs m SIG (signer_cells 0 0 sj).
    Hypothesis ALS : SIG mod 8 = 0.
    Hypothesis HDA : rw_cells usegs m DALG (buf_cells dtg dpad dlen dq).
    Hypothesis ALD : DALG mod 8 = 0.
    Hypothesis Q1 : BUF <= dq.  Hypothesis Q2 : 0 <= dlen.  Hypothesis Q3 : dq + dlen <= BUF + Z.of_nat (length bs).
    Hypothesis PP1 : bv_unsigned sp <= PP.  Hypothesis PP2 : PP + 8 <= heap_top usegs L HI h.
    Hypothesis SG1 : bv_unsigned sp <= SIG.  Hypothesis SG2 : SIG + SIGNER_SIZE <= heap_top usegs L HI h.
    Hypothesis DA1 : bv_unsigned sp <= DALG.  Hypothesis DA2 : DALG + 24 <= heap_top usegs L HI h.
    Hypothesis D1 : PP + 8 <= SIG \/ SIG + SIGNER_SIZE <= PP.
    Hypothesis D2 : PP + 8 <= DALG \/ DALG + 24 <= PP.
    Hypothesis D3 : DALG + 24 <= SIG \/ SIG + SIGNER_SIZE <= DALG.
    Hypothesis ST : stk usegs m lo (bv_unsigned sp).
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis SLO : lo <= bv_unsigned sp - PKCS7_GETSIGNERS_STACK - hl_stack L.
    Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
    Hypothesis SPTOP : bv_unsigned sp <= heap_top usegs L HI h.
    Hypothesis MI : mem_inv usegs m.
    Hypothesis SO : statics_ok usegs L m.
    Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
    Hypothesis SPR : 0 <= bv_unsigned sp < 2 ^ 64.

    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L24387678722.8300000TS1L3HLS2sp2PP3SIG4DALG2lo2bs3SLO3SPR". (* [comment removed for export] *)
    Let LOSP : lo <= bv_unsigned sp + -96. Proof. unfold PKCS7_GETSIGNERS_STACK in SLO. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L38152956027.8400000LS1L2sp2PP3SIG4DALG2lo2bs3SLO". (* [comment removed for export] *)
    Let SLO320 : lo <= bv_unsigned sp - 320 - hl_stack L. Proof. unfold PKCS7_GETSIGNERS_STACK in SLO. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Let BCE : BUF + Z.of_nat (length bs) <= alloc_ceiling.
    Proof.
      destruct (heap_blocks usegs L HI _ _ _ _ HH) as [BR _]. rewrite Forall_forall in BR.
      destruct (BR _ BIN) as (_ & _ & _ & Bce & _). exact Bce.
    Qed.

    Notation POST := (pkcs7_getsigners_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB PP P END SIG DALG lo dtg dpad dlen dq m mo).
    Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -96)).
    Notation X0 := [(PP, PP + 8); (SIG, SIG + 200)].
    Definition SAVED : list cell := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    Notation n := (Z.of_nat (length bs)).

    (* [comment removed for export] *)
    Definition gv (lw : word) (p : Z) (hcs : list cell) (Lc : list blk) (mc : mem) (moc : Model) (hc : HST usegs L HI) : Prop :=
      HEAP usegs L HI hc (Lc ++ LB) mc moc
      /\ heap_top usegs L HI hc = heap_top usegs L HI h
      /\ mo_frame mo moc
      /\ heap_presx usegs L LB (bv_unsigned sp) X0 m mc
      /\ (exists jk, rw_cells usegs mc (bv_unsigned sp + -96) (CB 8 jk :: C8 lw :: SAVED))
      /\ rw_cells usegs mc PP [C8 (Z_to_bv 64 p)] /\ P <= p <= END
      /\ rw_cells usegs mc SIG hcs /\ Z.of_nat (cells_size hcs) = 200
      /\ rw_cells usegs mc DALG (buf_cells dtg dpad dlen dq)
      /\ bytes_at usegs mc BUF bs
      /\ mem_inv usegs mc /\ statics_ok usegs L mc /\ stk usegs mc lo (bv_unsigned sp + -96).

    Ltac gv_open D := destruct D as (HHc & HTc & MFc & HPXc & (?jk & FR) & PPc & Hpc & CS & CSZ & DAc & BYc & MIc & SOc & STc).
    Ltac zofnat H := cbn [cells_size csize Nat.add length] in H;
      repeat match type of H with context [Z.of_nat (Datatypes.S ?k)] => let v := eval vm_compute in (Z.of_nat (Datatypes.S k)) in change (Z.of_nat (Datatypes.S k)) with v in H end;
      repeat match type of H with context [Z.add (Z.add ?a ?b) ?c] => is_Zlit b; is_Zlit c; let v := eval vm_compute in (Z.add b c) in replace (Z.add (Z.add a b) c) with (Z.add a v) in H by lia end.
    Ltac fix_ret pc := replace (ret_pc (Z_to_bv 64 pc)) with (Z_to_bv 64 pc : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    Ltac kz K := unfold SIGNER_SIZE, NAME_SIZE in *; first [ apply land64_zero in K; [| clear_disj; lia] | apply mod64_zero in K; [| clear_disj; lia]
                       | apply land64_nonzero in K; [| clear_disj; lia] | apply mod64_nonzero in K; [| clear_disj; lia]
                       | rewrite Z.mod_small in K by (clear_disj; lia)
                       | change 18446744073709551615 with (Z.ones 64) in K; rewrite Z.land_ones in K by (clear_disj; lia); rewrite Z.mod_small in K by (clear_disj; lia)
                       | idtac ].
    Ltac joinr H1 H2 :=
      lazymatch type of H1 with rw_cells ?sg ?mm ?A1 ?cs1 =>
      lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
        replace A2 with (A1 + Z.of_nat (cells_size cs1)) in H2 by (cbn; lia);
        let Hj := fresh "J" in
        pose proof (proj2 (rw_cells_app sg mm A1 cs1 cs2) (conj H1 H2)) as Hj; clear H1 H2; rename Hj into H1;
        cbn [app] in H1
      end end.
    (* [comment removed for export] *)
    Ltac spine_firstn k cs :=
      let k := eval cbv in k in
      lazymatch k with
      | Datatypes.O => eval lazy beta iota delta [firstn] in (firstn Datatypes.O cs)
      | Datatypes.S ?k' => lazymatch cs with
                 | ?c :: ?cs' => let r := spine_firstn k' cs' in constr:(c :: r)
                 | _ => eval cbv beta iota delta [firstn] in (firstn k cs)
                 end
      end.
    Ltac spine_skipn k cs :=
      let k := eval cbv in k in
      lazymatch k with
      | Datatypes.O => cs
      | Datatypes.S ?k' => lazymatch cs with
                 | _ :: ?cs' => spine_skipn k' cs'
                 | _ => eval cbv beta iota delta [skipn] in (skipn k cs)
                 end
      end.
    Ltac splitat H k H2 :=
      lazymatch type of H with rw_cells ?sg ?mm ?A0 ?cs =>
        let l1 := spine_firstn k cs in
        let l2 := spine_skipn k cs in
        change (rw_cells sg mm A0 (l1 ++ l2)) in H;
        let H1 := fresh "SP" in
        destruct (proj1 (rw_cells_app sg mm A0 l1 l2) H) as [H1 H2]; clear H; rename H1 into H; zofnat H2
      end.

    (* [comment removed for export] *)
    Definition wfp (Lc : list blk) (W : list ivl) : Prop :=
      forall a, ~ outside W a -> (PP <= a < PP + 8) \/ (SIG <= a < SIG + 200) \/ (lo <= a < bv_unsigned sp) \/ in_block Lc a.

    Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L54391985405.101L54391986042.101L54391986171.10100001E02\047S1L2HI3HLS2sp1h2PP3BUF3SIG4DALG2lo2bs2B53PP13PP23SG13DA13DA24CEIL3SPR6SLO3043BCE1a2H3S1L2HI3HLS2sp1h2PP3BUF3SIG4DALG2lo2bs2B53PP13SG13SG23DA12D24CEIL3SPR6SLO3043BCE1a2Ha2H2S1L2HI3HLS2sp1h2PP3BUF3SIG4DALG2lo2bs2B53PP13PP23SG13DA13DA22D24CEIL3SPR6SLO3043BCE1a2Ha2H1". (* [comment removed for export] *)
    #[using="HLS m mo BUF DALG bs HH BIN B5 PP1 PP2 SG1 SG2 DA1 DA2 D2 CEIL SLO SPR SLO320 BCE"] Lemma HEAPm : forall W Lc hc mA mB moc,
      HEAP usegs L HI hc (Lc ++ LB) mA moc -> heap_top usegs L HI hc = heap_top usegs L HI h ->
      munch W mA mB -> wmono usegs mA mB -> wfp Lc W -> HEAP usegs L HI hc (Lc ++ LB) mB moc.
    Proof.
      intros W Lc hc mA mB moc HHc HTc MU WM HW.
      eapply (HEAP_munch usegs L HI) with (SP := lo); [exact HHc | exact CEIL | exact MU | exact WM |].
      intros a Ha Hna. destruct (HW a Hna) as [H1|[H2|[H3|(b & Hb & Hr)]]].
      - left. rewrite HTc. lia.
      - left. rewrite HTc. unfold SIGNER_SIZE in SG2. lia.
      - left. rewrite HTc. lia.
      - right; right. exists b. split; [apply in_or_app; left; exact Hb| exact Hr].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Ltac2 Set LiaOrc.tbl := fun () => "00;0@L39535555329.113L55315056136.113L56759324319.101L59308579152.104L59308579281.104L59308579414.104L59310846468.107L59314873579.106L59314873579.114L59321333514.109L59321333514.11200001A02N02f03A03\04905B06H07W08P0:2S1L3HLS2sp2PP3BUF3SIG4DALG2lo2bs2B53PP13SG13DA14CEIL3SPR6SLO3043BCE1a2Ha1b2Hr3BceS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR6SLO3041a2b'3Hr'1b2Hr2Bp3BceS2sp2PP3SIG4DALG2bs1a2HaS2sp2PP3SIG4DALG2bs1a2Ho2H1S2sp2PP3SIG4DALG2bs1a2Ho2H2S2sp2PP3SIG4DALG2lo2bs1a1C2H3S1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR6SLO3041a2Ha1b2Hr2H33BceS1L3HLS3DHI2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR6SLO3041a2C12H31HS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR6SLO3041a2b'3Hr'1b2Hr2Bp3Bce1HS1L3HLS2sp2PP3SIG4DALG2lo2bs4CEIL3SPR6SLO3041a1C1b2Hr3BceS1L3HLS3DHI1l2l02sp2PP3SIG4DALG2lo2bs3ALP3ALS3ALD3PP13SG13DA12D24CEIL3SPR6SLO3041a2C11b2Hr2Bp4Bimg". (* [comment removed for export] *)
    #[using="HFREE HCALLOC HMSF HLS SW DIMG DHI HND GETALG m mo h BUF DALG bs HH ALP BIN B5 ALS ALD PP1 SG1 DA1 D2 CEIL SLO SPR SLO320 BCE"] Lemma HPXm : forall W Lc hc mA mB moc,
      HEAP usegs L HI hc (Lc ++ LB) mA moc -> munch W mA mB -> wmono usegs mA mB -> wfp Lc W ->
      heap_presx usegs L LB (bv_unsigned sp) X0 mA mB.
    Proof.
      intros W Lc hc mA mB moc HHc MU WM HW a Ha Hc Ho. split; [| apply WM].
      destruct (outside_dec W a) as [O|NO]; [apply MU; rewrite wa_unsigned by lia; exact O|]. exfalso.
      destruct (heap_blocks usegs L HI _ _ _ _ HHc) as [BR AP]. rewrite Forall_forall in BR.
      destruct (HW a NO) as [H1|[H2|[H3|(b & Hb & Hr)]]]; cbn [outside] in Ho; [lia| lia| |].
      - destruct Hc as [C|[[C1 C2]|(b & Hb & Hr)]]; [lia| pose proof alloc_ceiling_pos; lia|].
        destruct (BR b (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & Bce & _). lia.
      - destruct (BR b (in_or_app _ _ _ (or_introl Hb))) as (Bp & _ & _ & Bce & Bimg).
        destruct Hc as [C|[[C1 C2]|(b' & Hb' & Hr')]]; [lia| destruct DIMG; lia|].
        (* [comment removed for export] *)
        pose proof (HND _ _ _ _ HHc) as NDL. rewrite map_app in NDL.
        assert (NE : b <> b').
        { intros ->. apply (NoDup_app_notin_l _ _ (fst b') NDL); apply in_map; assumption. }
        destruct (blocks_apart_neq _ _ _ AP (in_or_app _ _ _ (or_introl Hb)) (in_or_app _ _ _ (or_intror Hb')) NE ltac:(lia) ltac:(lia)); lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Ltac2 Set LiaOrc.tbl := fun () => "0040@L59308579152.103L59308579281.103L59308579414.103L59321333514.11000001602<03B04\S1L3HLS3DHI2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR6SLO3041a2Ha1H2H1S1L3HLS3DHI2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR6SLO3041a2Ha1H2H2S1L3HLS3DHI2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR6SLO3041a2Ha1H2H3S1L3HLS1l2l02sp2PP3SIG4DALG2lo2bs3ALP3ALS3ALD3PP13SG13DA14CEIL3SPR6SLO3041a2Ha1H1b2Hr4Bimg". (* [comment removed for export] *)
    #[using="HFREE HCALLOC HMSF HLS SW DIMG DHI GETALG DALG bs ALP ALS ALD PP1 SG1 DA1 CEIL SLO SPR SLO320"] Lemma SOm : forall W Lc hc mA mB moc, HEAP usegs L HI hc (Lc ++ LB) mA moc ->
      statics_ok usegs L mA -> munch W mA mB -> wfp Lc W -> statics_ok usegs L mB.
    Proof.
      intros W Lc hc mA mB moc HHc SO0 MU HW. eapply statics_ok_munch; [exact SO0| exact MU|].
      intros a Ha Hnw. destruct (outside_dec W a) as [Ho|Hno]; [exact Ho|]. exfalso. pose proof alloc_ceiling_pos.
      destruct (heap_blocks usegs L HI _ _ _ _ HHc) as [BR _]. rewrite Forall_forall in BR.
      destruct (HW a Hno) as [H1|[H2|[H3|(b & Hb & Hr)]]]; [lia| lia| lia|].
      destruct (BR b (in_or_app _ _ _ (or_introl Hb))) as (Bp & _ & _ & Bce & Bimg). destruct DIMG. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00;0@L15302269400.141L22446743512.141L24383172793.143L34705680216.141L3949578456.141 L41843875160.141L51454941784.141L5699067096.141 L58591023192.141L59504824426.144L67280348888.14100000G00^01=01T01k02B02Y03003G03^045S2sp2PP3SIG4DALG2bs3hcsS2sp2PP3SIG4DALG2bs3hcsS2sp2PP3SIG4DALG2lo2bs4LOSP3hcsS2sp2PP3SIG4DALG2bs3hcsS2sp2PP3SIG4DALG2bs3hcsS2sp2PP3SIG4DALG2bs3hcsS2sp2PP3SIG4DALG2bs3hcsS2sp2PP3SIG4DALG2bs3hcsS2sp2PP3SIG4DALG2bs3hcsS2sp2PP3SIG4DALG2bs3hcsS2sp2PP3SIG4DALG2bs3hcs". (* [comment removed for export] *)
    #[using="HLS SLO SPR LOSP"] Lemma L_RET : forall lw p hcs Lc mc moc hc (r inext snext : Z) (sj' : signer_junk) (names0 : list Z) (sg : list (Z * list Z))
        (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word),
      gv lw p hcs Lc mc moc hc ->
      rw_cells usegs mc SIG (signer_cells inext snext sj') ->
      name_chain usegs (fun _ => True) mc (Lc ++ LB) inext names0 -> signer_chain usegs mc (Lc ++ LB) snext sg ->
      Permutation Lc (SNAME names0 ++ signer_blocks sg) ->
      -2^31 < r < 2^31 ->
      aevtM usegs moc POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 (Z_to_bv 64 r) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x1e044) fc None mc (seg_rom usegs)).
    Proof.
      intros lw p hcs Lc mc moc hc r inext snext sj' names0 sg x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31
             D CSS HNC HSC PERM Hr. gv_open D.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof LOSP as LOSP'.
      unfold SAVED in FR.
      zstep.                                   (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.  (* [comment removed for export] *)
      zstep.                                   (* [comment removed for export] *)
      zstep.                                   (* [comment removed for export] *)
      pose proof (stk_release usegs _ _ _ _ STc FR ltac:(lia)) as STf. cbn [cells_size csize Nat.add] in STf.
      replace (bv_unsigned sp + -96 + Z.of_nat 96) with (bv_unsigned sp) in STf by lia.
      apply aevtM_done. unfold pkcs7_getsigners_post.
      deexists 15. dexists mc, moc, hc, r, p, inext, snext, sj', names0, sg, Lc.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact Hr|]. split; [exact MIc|]. split; [exact SOc|]. split; [exact STf|].
      split; [exact MFc|]. split; [exact HTc|]. split; [exact PPc|]. split; [exact Hpc|].
      split; [exact CSS|]. split; [exact DAc|]. split; [exact HNC|]. split; [exact HSC|]. split; [exact PERM|]. split; [exact HHc|].
      unfold SIGNER_SIZE. exact HPXc.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


    (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0070@L10834139618.119L12490560002.119L12654660144.119L20323957863.119L32481125506.119L39360456046.119L6933890746.119 00000K00f01A01\02702N02eS2sp2PP3BUF3SIG4DALG2bs3hcsS2sp2PP3SIG4DALG2bs3DA13hcsS2sp2PP3BUF3SIG4DALG2bs3hcsS2sp2PP3SIG4DALG2bs3PP13hcsS2sp2PP3SIG4DALG2bs3SG13hcsS2sp2PP3SIG4DALG2bs3hcsS2sp2PP3SIG4DALG2bs3hcs". (* [comment removed for export] *)
    #[using="SW BIN PP1 SG1 DA1"] Lemma gv_free : forall lw p hcs Lc mc moc hc x m1 mo1 h1,
      gv lw p hcs Lc mc moc hc -> In x (map fst Lc) ->
      HEAP usegs L HI h1 (lb_remove x (Lc ++ LB)) m1 mo1 -> heap_top usegs L HI h1 = heap_top usegs L HI hc ->
      heap_pres usegs L (lb_remove x (Lc ++ LB)) (bv_unsigned sp + -96) mc m1 ->
      mo_frame moc mo1 -> mem_inv usegs m1 -> stk usegs m1 lo (bv_unsigned sp + -96) ->
      gv lw p hcs (lb_remove x Lc) m1 mo1 h1.
    Proof.
      intros lw p hcs Lc mc moc hc x m1 mo1 h1 D HIN HH1 HT1 HP1 MF1 MI1 ST1. gv_open D.
      rewrite (lb_remove_app_l x Lc LB HIN) in HH1, HP1.
      assert (SUB : forall b, In b LB -> In b (lb_remove x Lc ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
      split; [exact HH1|]. split; [congruence|]. split; [eapply mo_frame_trans; eassumption|].
      split; [eapply heap_presx_trans_pres; [exact HPXc| eapply heap_pres_sp_mono; [eapply heap_pres_sub; [exact HP1| exact SUB] | lia] | intros b Hb; exact Hb] |].
      split; [eexists; eapply heap_pres_rw_cells; [exact HP1| exact FR| apply client_range_stack; lia] |].
      split; [eapply heap_pres_rw_cells; [exact HP1| exact PPc| apply client_range_stack; lia] |]. split; [exact Hpc|].
      split; [eapply heap_pres_rw_cells; [exact HP1| exact CS| apply client_range_stack; lia] |]. split; [exact CSZ|].
      split; [eapply heap_pres_rw_cells; [exact HP1| exact DAc| apply client_range_stack; lia] |].
      split; [eapply heap_pres_bytes_at; [exact HP1| exact BYc| eapply client_range_block; [apply SUB; exact BIN| lia| lia]] |].
      split; [exact MI1|]. split; [eapply statics_ok_heap_pres'; [exact SOc| eapply heap_pres_sub; [exact HP1| exact SUB] | exact SW] | exact ST1].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0040@L5744940593.108 L59314873579.124L59323442506.119L59323442506.12000000H01n03J05AS2sp2PP3SIG4DALG2bs1x2HxS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA13SPR6SLO3041a1k3wlo3whi3Hhi1x1B1j2Hr3Hin2Bp2Bn3Bce5CEIL'1H3HloS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA13SPR6SLO3041a1k3wlo3whi3Hhi1x2Hs3Hin2Bp2Bn3Bce5CEIL'S1L3HLS3DHI3DI13DI22sp2PP3SIG4DALG2lo2bs3ALP3ALS3ALD3PP13SG13DA13SPR6SLO3041a1k3wlo3whi3Hlo3Hhi1x2Hx3Hd13Hin4Bimg5CEIL'". (* [comment removed for export] *)
    #[using="HFREE HCALLOC HMSF HLS SW DIMG DHI HND GETALG PP SIG DALG lo bs ALP ALS ALD PP1 SG1 DA1 CEIL SLO SPR LOSP SLO320"] Lemma hp_store_free : forall Lx hX mX moX mS m1 a k wlo whi,
      HEAP usegs L HI hX (Lx ++ LB) mX moX -> In (a, k) Lx -> a <= wlo -> whi <= a + k ->
      munch [(wlo, whi)] mX mS -> wmono usegs mX mS ->
      heap_pres usegs L (lb_remove a (Lx ++ LB)) (bv_unsigned sp + -96) mS m1 ->
      heap_pres usegs L (lb_remove a (Lx ++ LB)) (bv_unsigned sp + -96) mX m1.
    Proof.
      intros Lx hX mX moX mS m1 a k wlo whi HHx HIN Hlo Hhi MU WM HP x Hx Hc.
      destruct (HP x Hx Hc) as [E1 W1]. split; [| intros Hw; apply W1; apply WM; exact Hw].
      rewrite E1. apply MU. rewrite wa_unsigned by lia. cbn [outside]. split; [| exact I]. intros Hin.
      destruct (heap_blocks usegs L HI _ _ _ _ HHx) as [BR AP]. rewrite Forall_forall in BR.
      destruct (BR _ (in_or_app _ _ _ (or_introl HIN))) as (Bp & _ & Bn & Bce & Bimg). cbn [fst snd] in Bp, Bn, Bce, Bimg.
      pose proof LOSP as LOSP'. pose proof CEIL as CEIL'. destruct DIMG as [DI1 DI2].
      destruct Hc as [Hs|[[Hd1 Hd2]|(b & Hb & Hr)]]; [lia| lia|].
      pose proof (lb_remove_fst_neq _ _ _ (HND _ _ _ _ HHx) Hb) as NE. apply In_lb_remove in Hb. destruct b as [B j]. cbn [fst snd] in NE, Hr.
      destruct (blocks_apart_in2 _ _ _ _ _ AP (in_or_app _ _ _ (or_introl HIN)) Hb ltac:(intros E; exact (NE (eq_sym E)))); lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00:0@L26056399620.159L35497502253.187L46425563800.181L47028033785.157L54314225841.184L55472014661.160L59308633593.1  L59310680273.185L60385219197.160L65456873510.18200001F01m02X03?03f04Y04]05K06?06mS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR3cur3hcs7SLO304'3ACP4HPOS3pre2nx4postS2sp2PP3SIG4DALG2bs3cur3hcs3pre2nx4postS2sp2PP3SIG4DALG2bs3cur3hcs3pre2nx4post3NXBS2sp2PP3SIG4DALG2bs3cur3hcs3pre2nx4postS2sp2PP3SIG4DALG2bs3cur3hcs3pre2nx4postS1L2sp2PP3SIG4DALG2lo2bs6SLO3043cur3hcs3pre2nx4postS2KZS2sp2PP3SIG4DALG2bs2n23cur3hcs3pre4post2KZ3HP2S1L2HI2sp1h2PP3SIG4DALG2bs5SPTOP3cur3hcs3pre2nx4postS2sp2PP3SIG4DALG2bs2n23cur3hcs3pre4post3NXB2KZ". (* [comment removed for export] *)
    #[using="HFREE HLS SW BIN ALP ALS ALD PP1 SG1 DA1 CEIL SLO SPTOP TP SPR LOSP SLO320"] Lemma CL3 : forall (nodes : list Z) (cur : Z) lw p hcs (A B : list blk) (R : mem -> list blk -> Prop) mc moc hc
        (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word),
      nodes <> [] -> name_chain usegs (fun _ => True) mc ((A ++ SNAME (rev nodes) ++ B) ++ LB) cur nodes -> List.NoDup nodes ->
      (forall x, In x nodes -> ~ In x (map fst A)) ->
      gv lw p hcs (A ++ SNAME (rev nodes) ++ B) mc moc hc ->
      R mc (A ++ SNAME (rev nodes) ++ B) ->
      (forall mX mY (hX : HST usegs L HI) moX rest' x, R mX (A ++ SNAME (rev (x :: rest')) ++ B) -> In x nodes -> ~ In x rest' ->
          HEAP usegs L HI hX ((A ++ SNAME (rev (x :: rest')) ++ B) ++ LB) mX moX ->
          heap_pres usegs L (lb_remove x ((A ++ SNAME (rev (x :: rest')) ++ B) ++ LB)) (bv_unsigned sp + -96) mX mY ->
          R mY (A ++ SNAME (rev rest') ++ B)) ->
      (forall mc' moc' hc' (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y23 y28 y29 y30 y31 : word),
          gv lw p hcs (A ++ B) mc' moc' hc' -> R mc' (A ++ B) ->
          aevtM usegs moc' POST
            (MS (mkR y1 SP' gp tp y5 y6 y7 (Z_to_bv 64 SIG) x9 (Z_to_bv 64 0) y11 y12 y13 y14 y15 y16 y17 x18 x19 y20 y21 y22 y23 x24 s9 s10 s11 y28 y29 y30 y31)
                F (Z_to_bv 64 0x1e184) fc None mc' (seg_rom usegs))) ->
      aevtM usegs moc POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 (Z_to_bv 64 SIG) x9 (Z_to_bv 64 cur) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x1e1ac) fc None mc (seg_rom usegs)).
    Proof.
      intros nodes. induction nodes as [|n1 rest IH];
        intros cur lw p hcs A B R mc moc hc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 HNE HC HNDn HNA D HR RP K; [congruence|].
      pose proof D as D0. gv_open D.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof LOSP as LOSP'. pose proof SLO320 as SLO320'.
      pose proof alloc_ceiling_pos as ACP.
      destruct (chain_uncons usegs _ _ _ _ _ _ _ _ HC) as (<- & HIN & HAL & HPOS & pre & nx & post & Hsz1 & Hsz2 & HNODE & _ & HNX0 & HC').
      unfold NAME_NEXT in HNX0. unfold NAME_SIZE in Hsz2, HIN.
      pose proof (rw_cells_bound _ _ _ _ HNODE) as NB. rewrite Hsz2 in NB.
      pose proof (chain_addr_range usegs _ _ _ _ _ _ _ HC') as NXB.
      apply List.NoDup_cons_iff in HNDn. destruct HNDn as [Hn1 HNDr].
      clear HNODE.
      zstep. zstep; if_cases KAL; zify_cond KAL; [al8_close KAL|].
      zstep.                                   (* [comment removed for export] *)
      zstep.                                   (* [comment removed for export] *)
      replace (Z_to_bv 64 260760 : word) with (Z_to_bv 64 (hl_free L) : word) by (rewrite HFREE; reflexivity).
      pose proof (unsigned_lit (bv_unsigned sp + -96) ltac:(lia)) as USP.
      eapply aevtM_cut.
      { eapply (heap_free usegs L HI) with (A := cur) (n := 64) (lo := lo) (h := hc) (LB := (A ++ SNAME (rev (cur :: rest)) ++ B) ++ LB);
          [ exact HHc | exact HIN | rewrite USP; exact STc | exact CEIL | rewrite USP; lia | exact MIc | exact TP
          | rewrite USP, HTc; lia | reflexivity ]. }
      intros ms' mo'x PO. unfold call_post in PO.
      ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m1 & mo1
                      & E0 & MI1 & ST1 & MF1 & HP1 & h1 & HT1 & HH1).
      injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite USP in ST1, HP1. fix_ret 0x1e1bc.
      pose proof (in_node A B cur rest) as HINL.
      pose proof (rm_node A B cur rest (HNA cur (or_introl eq_refl)) Hn1) as ELc.
      pose proof (gv_free _ _ _ _ _ _ _ _ _ _ _ D0 HINL HH1 HT1 HP1 MF1 MI1 ST1) as G1. rewrite ELc in G1.
      assert (HC1 : name_chain usegs (fun _ => True) m1 ((A ++ SNAME (rev rest) ++ B) ++ LB) nx rest).
      { replace ((A ++ SNAME (rev rest) ++ B) ++ LB) with (lb_remove cur ((A ++ SNAME (rev (cur :: rest)) ++ B) ++ LB)).
        2:{ rewrite lb_remove_app_l by exact HINL. rewrite ELc. reflexivity. }
        eapply chain_free_other; [exact HC'| intros x Hx ->; exact (Hn1 Hx)| exact HP1 | unfold NAME_SIZE; lia]. }
      pose proof (RP _ _ _ _ rest cur HR (or_introl eq_refl) Hn1 HHc HP1) as HR1.
      clear HHc HPXc SOc STc MIc MK HP1 D0.
      pose proof G1 as G1'. destruct G1' as (HH1' & _). pose proof (heap_mok _ _ HI _ _ _ _ HH1') as MK.
      zstep.                                   (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ.
      - (* [comment removed for export] *)
        destruct rest as [|n2 r2]; [exfalso; cbn in HC'; subst nx; clear - KZ; cbv in KZ; lia|].
        eapply (IH nx lw p hcs A B R m1 mo1 h1); [congruence| exact HC1| exact HNDr| intros x Hx; apply HNA; right; exact Hx| exact G1| exact HR1| |].
        { intros mX mY hX moX rest' x HRx Hx Hnr HHx HPx. eapply RP; [exact HRx| right; exact Hx| exact Hnr| exact HHx| exact HPx]. }
        intros mc' moc' hc' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y23 y28 y29 y30 y31 D' R'. eapply K; [exact D'| exact R'].
      - (* [comment removed for export] *)
        destruct rest as [|n2 r2].
        2:{ exfalso. pose proof (chain_uncons usegs _ _ _ _ _ _ _ _ HC1) as (-> & _ & _ & HP2 & _). kz KZ; lia. }
        cbn in HC1. subst nx.
        zstep.                                 (* [comment removed for export] *)
        eapply K; [exact G1| exact HR1].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00:0@L26056399620.159L35497502253.187L46425563800.181L47028033785.157L55472014661.160L58859540273.184L59308633593.1  L59310680273.185L60385219197.160L65456873510.18200001F01m02X03?04204Y04]05K06?06mS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR3cur3hcs7SLO304'3ACP4HPOS3pre2nx4postS2sp2PP3SIG4DALG2bs3cur3hcs3pre2nx4postS2sp2PP3SIG4DALG2bs3cur3hcs3pre2nx4post3NXBS2sp2PP3SIG4DALG2bs3cur3hcs3pre2nx4postS1L2sp2PP3SIG4DALG2lo2bs6SLO3043cur3hcs3pre2nx4postS2sp2PP3SIG4DALG2bs3cur3hcs3pre2nx4postS2KZS2sp2PP3SIG4DALG2bs2n23cur3hcs3pre4post2KZ3HP2S1L2HI2sp1h2PP3SIG4DALG2bs5SPTOP3cur3hcs3pre2nx4postS2sp2PP3SIG4DALG2bs2n23cur3hcs3pre4post3NXB2KZ". (* [comment removed for export] *)
    #[using="HFREE HLS SW BIN ALP ALS ALD PP1 SG1 DA1 CEIL SLO SPTOP TP SPR LOSP SLO320"] Lemma CL1 : forall (nodes : list Z) (cur : Z) lw p hcs (A B : list blk) (R : mem -> list blk -> Prop) mc moc hc
        (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word),
      nodes <> [] -> name_chain usegs (fun _ => True) mc ((A ++ SNAME (rev nodes) ++ B) ++ LB) cur nodes -> List.NoDup nodes ->
      (forall x, In x nodes -> ~ In x (map fst A)) ->
      gv lw p hcs (A ++ SNAME (rev nodes) ++ B) mc moc hc ->
      R mc (A ++ SNAME (rev nodes) ++ B) ->
      (forall mX mY (hX : HST usegs L HI) moX rest' x, R mX (A ++ SNAME (rev (x :: rest')) ++ B) -> In x nodes -> ~ In x rest' ->
          HEAP usegs L HI hX ((A ++ SNAME (rev (x :: rest')) ++ B) ++ LB) mX moX ->
          heap_pres usegs L (lb_remove x ((A ++ SNAME (rev (x :: rest')) ++ B) ++ LB)) (bv_unsigned sp + -96) mX mY ->
          R mY (A ++ SNAME (rev rest') ++ B)) ->
      (forall mc' moc' hc' (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y28 y29 y30 y31 : word),
          gv lw p hcs (A ++ B) mc' moc' hc' -> R mc' (A ++ B) ->
          aevtM usegs moc' POST
            (MS (mkR y1 SP' gp tp y5 y6 y7 (Z_to_bv 64 SIG) x9 (Z_to_bv 64 0) y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 x24 s9 s10 s11 y28 y29 y30 y31)
                F (Z_to_bv 64 0x1e170) fc None mc' (seg_rom usegs))) ->
      aevtM usegs moc POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 (Z_to_bv 64 SIG) x9 (Z_to_bv 64 cur) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x1e158) fc None mc (seg_rom usegs)).
    Proof.
      intros nodes. induction nodes as [|n1 rest IH];
        intros cur lw p hcs A B R mc moc hc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 HNE HC HNDn HNA D HR RP K; [congruence|].
      pose proof D as D0. gv_open D.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof LOSP as LOSP'. pose proof SLO320 as SLO320'.
      pose proof alloc_ceiling_pos as ACP.
      destruct (chain_uncons usegs _ _ _ _ _ _ _ _ HC) as (<- & HIN & HAL & HPOS & pre & nx & post & Hsz1 & Hsz2 & HNODE & _ & HNX0 & HC').
      unfold NAME_NEXT in HNX0. unfold NAME_SIZE in Hsz2, HIN.
      pose proof (rw_cells_bound _ _ _ _ HNODE) as NB. rewrite Hsz2 in NB.
      pose proof (chain_addr_range usegs _ _ _ _ _ _ _ HC') as NXB.
      apply List.NoDup_cons_iff in HNDn. destruct HNDn as [Hn1 HNDr].
      clear HNODE.
      zstep. zstep; if_cases KAL; zify_cond KAL; [al8_close KAL|].
      zstep.                                   (* [comment removed for export] *)
      zstep.                                   (* [comment removed for export] *)
      replace (Z_to_bv 64 260760 : word) with (Z_to_bv 64 (hl_free L) : word) by (rewrite HFREE; reflexivity).
      pose proof (unsigned_lit (bv_unsigned sp + -96) ltac:(lia)) as USP.
      eapply aevtM_cut.
      { eapply (heap_free usegs L HI) with (A := cur) (n := 64) (lo := lo) (h := hc) (LB := (A ++ SNAME (rev (cur :: rest)) ++ B) ++ LB);
          [ exact HHc | exact HIN | rewrite USP; exact STc | exact CEIL | rewrite USP; lia | exact MIc | exact TP
          | rewrite USP, HTc; lia | reflexivity ]. }
      intros ms' mo'x PO. unfold call_post in PO.
      ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m1 & mo1
                      & E0 & MI1 & ST1 & MF1 & HP1 & h1 & HT1 & HH1).
      injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite USP in ST1, HP1. fix_ret 0x1e168.
      pose proof (in_node A B cur rest) as HINL.
      pose proof (rm_node A B cur rest (HNA cur (or_introl eq_refl)) Hn1) as ELc.
      pose proof (gv_free _ _ _ _ _ _ _ _ _ _ _ D0 HINL HH1 HT1 HP1 MF1 MI1 ST1) as G1. rewrite ELc in G1.
      assert (HC1 : name_chain usegs (fun _ => True) m1 ((A ++ SNAME (rev rest) ++ B) ++ LB) nx rest).
      { replace ((A ++ SNAME (rev rest) ++ B) ++ LB) with (lb_remove cur ((A ++ SNAME (rev (cur :: rest)) ++ B) ++ LB)).
        2:{ rewrite lb_remove_app_l by exact HINL. rewrite ELc. reflexivity. }
        eapply chain_free_other; [exact HC'| intros x Hx ->; exact (Hn1 Hx)| exact HP1 | unfold NAME_SIZE; lia]. }
      pose proof (RP _ _ _ _ rest cur HR (or_introl eq_refl) Hn1 HHc HP1) as HR1.
      clear HHc HPXc SOc STc MIc MK HP1 D0.
      pose proof G1 as G1'. destruct G1' as (HH1' & _). pose proof (heap_mok _ _ HI _ _ _ _ HH1') as MK.
      zstep.                                   (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ.
      - (* [comment removed for export] *)
        destruct rest as [|n2 r2]; [exfalso; cbn in HC'; subst nx; clear - KZ; cbv in KZ; lia|].
        eapply (IH nx lw p hcs A B R m1 mo1 h1); [congruence| exact HC1| exact HNDr| intros x Hx; apply HNA; right; exact Hx| exact G1| exact HR1| |].
        { intros mX mY hX moX rest' x HRx Hx Hnr HHx HPx. eapply RP; [exact HRx| right; exact Hx| exact Hnr| exact HHx| exact HPx]. }
        intros mc' moc' hc' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y28 y29 y30 y31 D' R'. eapply K; [exact D'| exact R'].
      - (* [comment removed for export] *)
        destruct rest as [|n2 r2].
        2:{ exfalso. pose proof (chain_uncons usegs _ _ _ _ _ _ _ _ HC1) as (-> & _ & _ & HP2 & _). kz KZ; lia. }
        cbn in HC1. subst nx.
        eapply K; [exact G1| exact HR1].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00;0@D11805467289.133D13112141392.135D21157640433.135D21172136973.133D67183863355.133D67186111175.135L11799358114.140L26295853967.142L35992031848.141L6139713783.136 L67011298662.14300000N01e02O02m03K04504T05205P06407@S2sp2PP3SIG4DALG2bs3snx3sjh2HBS1L3HLS3DHI2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR6SLO3043snx3sjh3ACP2HB5Ha_st5Hl_stS2sp2PP3SIG4DALG2bs3snx3sjh2HB5Ha_st5Hl_stS2sp2PP3SIG4DALG2bs3snx3sjh2HBS2sp2PP3SIG4DALG2bs3snx3sjh2HBS2sp2PP3SIG4DALG2bs3snx3sjh2HB5Ha_st5Hl_stS2sp2PP3SIG4DALG2bs3SG13snx3sjhS2sp2PP3SIG4DALG2bs2D33snx3sjhS2sp2PP3SIG4DALG2bs2D13snx3sjhS2sp2PP3SIG4DALG2lo2bs3snx3sjh1a3HnaS1L3HLS2sp2PP3BUF3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR6SLO3043BCE3snx3sjh3ACP". (* [comment removed for export] *)
    #[using="HFREE HCALLOC HMSF HLS SW DIMG DHI HND GETALG HH ALP BIN B5 ALS ALD PP1 PP2 SG1 SG2 DA1 DA2 D1 D2 D3 CEIL SLO SPR LOSP SLO320 BCE"] Lemma CL_END : forall lw p (snx : Z) sjh mc moc hc (r : Z)
        (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word),
      gv lw p (signer_cells 0 snx sjh) [] mc moc hc -> -2^31 < r < 2^31 ->
      aevtM usegs moc POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 (Z_to_bv 64 SIG) (Z_to_bv 64 r) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x1e17c) fc None mc (seg_rom usegs)).
    Proof.
      intros lw p snx sjh mc moc hc r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 D Hr. gv_open D.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof LOSP as LOSP'. pose proof alloc_ceiling_pos as ACP.
      unfold signer_cells in CS. cbn [sj0 sj_merged sj1 sj2] in CS.
      pose proof (conj HHc (conj FR (conj PPc (conj DAc (conj BYc I))))) as CBOX. clear FR PPc DAc BYc HHc.
      pose proof (munch_refl [(SIG + 192, SIG + 200)] mc) as MU1. pose proof (wmono_refl usegs mc) as WM1.
      zstep.                                   (* [comment removed for export] *)
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      ddestruct CBOX as (HHc & FR & PPc & DAc & BYc & _).
      assert (WF1 : wfp [] [(SIG + 192, SIG + 200)]) by (intros a Hna; cbn [outside] in Hna; first [clear_disj; lia | lia]).
      pose proof (HEAPm _ [] _ _ _ _ HHc HTc MU1 WM1 WF1) as HH1.
      pose proof (HPXm _ [] _ _ _ _ HHc MU1 WM1 WF1) as HPX01.
      lazymatch type of SOc with statics_ok _ _ m1 => rename SOc into SO1 | _ => pose proof (SOm _ [] _ _ _ _ HHc SOc MU1 WF1) as SO1; clear SOc end.
      pose proof (rw_cells_transport usegs _ mc m1 _ _ FR MU1 WM1 ltac:(cbn; lia)) as FR'.
      pose proof (rw_cells_transport usegs _ mc m1 _ _ PPc MU1 WM1 ltac:(cbn; unfold SIGNER_SIZE in D1; lia)) as PPc'.
      pose proof (rw_cells_transport usegs _ mc m1 _ _ DAc MU1 WM1 ltac:(cbn; unfold SIGNER_SIZE in D3; lia)) as DAc'.
      pose proof (bytes_at_transport usegs _ mc m1 _ _ BYc MU1 ltac:(cbn; lia)) as BYc'.
      clear HHc MU1 WM1 MK FR PPc DAc BYc. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
      zstep.                                   (* [comment removed for export] *)
      eapply (L_RET lw p _ [] m1 moc hc r 0 0 sjh [] []).
      - split; [exact HH1|]. split; [exact HTc|]. split; [exact MFc|]. split; [eapply heap_presx_trans; [exact HPXc| exact HPX01] |].
        split; [eexists; exact FR'|]. split; [exact PPc'|]. split; [exact Hpc|]. split; [exact CS|]. split; [reflexivity|].
        split; [exact DAc'|]. split; [exact BYc'|]. split; [assumption|]. split; [exact SO1| exact STc].
      - unfold signer_cells. cbn [sj0 sj_merged sj1 sj2]. exact CS.
      - apply chain_nil.
      - reflexivity.
      - apply Permutation_refl.
      - exact Hr.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00O0@D11805467289.184D49705053714.184D61272698277.184L11803635234.194L14014062319.158L14479818465.183L20654245805.161L23011543279.158L23011543279.180L24425350392.211L26058543499.190L26302364559.197L32700937324.216L33458987023.196L35992031848.195L41659498382.193L45756604495.180L50687127345.215L5455585400.183 L5455730760.219 L55276347018.160L55472014661.191L5736992481.219 L59308631400.1  L59308633593.1  L59308752027.220L59310680273.163L60385219197.191L6393052521.159 L67011298662.198L7579352030.160 00000L00h01I02V02o03H03a04:04S04T05\06i08O09\0:i0;H0;a0<:0<S0<l0=N0>30>L0>P0>T0?70?Z0@@0@b0AC0A\S2sp2PP3SIG4DALG2bs1a3hcs2HBS2sp2PP3SIG4DALG2bs1a3hcs2HBS2sp2PP3SIG4DALG2bs1a3hcs4HPOS2HBS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR1a3hcs7SLO304'3ACP4HPOS4BceaS2sp2PP3SIG4DALG2bs1a3hcsS2sp2PP3SIG4DALG2bs1a3hcsS2sp2PP3SIG4DALG2bs1a3hcsS2sp2PP3SIG4DALG2bs1a3hcsS2sp2PP3SIG4DALG2bs1a3hcsFS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR1a3hcs7SLO304'3ACP4HPOSS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR1a3hcs7SLO304'3ACP4HPOS4BceaS1L3HLS2sp2PP3SIG4DALG2lo2bs3ALP3ALS3ALD3PP13SG13DA14CEIL4SP163SPR2a21a3hcs7SLO304'3ACP4HPOS2KZ3HP22BxS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR1a3hcs7SLO304'3ACP4HPOS4BceaS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR1a3hcs7SLO304'3ACP4HPOS4BceaS2sp2PP3SIG4DALG2bs1a3hcs1x3HnxS2sp2PP3SIG4DALG2bs1a3hcsS2sp2PP3SIG4DALG2bs1a3hcsS2sp2PP3SIG4DALG2bs1a3hcsS2sp2PP3SIG4DALG2bs1a3hcsS2sp2PP3SIG4DALG2bs2n11a3hcs2KI2IBS1L2sp2PP3SIG4DALG2lo2bs6SLO3041a3hcsS2sp2PP3SIG4DALG2bs1a3hcsS2KIS2KZS2sp2PP3SIG4DALG2bs2a21a3hcs2KZ3HP2S2sp2PP3SIG4DALG2bs2n11a3hcs2KI3HP2S1L2HI2sp1h2PP3SIG4DALG2bs5SPTOP1a3hcsS2sp2PP3SIG4DALG2bs1a3hcs5inext2IBS2sp2PP3BUF3SIG4DALG2bs1a3hcs3DJBS2sp2PP3SIG4DALG2bs1a3hcs". (* [comment removed for export] *)
    #[using="HFREE HCALLOC HMSF HLS SW DIMG DHI HND GETALG HH ALP BIN B5 ALS ALD PP1 PP2 SG1 SG2 DA1 DA2 D2 CEIL SLO SP16 SPTOP TP SPR LOSP SLO320 BCE"] Lemma CL2 : forall (sg : list (Z * list Z)) (a : Z) lw p hcs mc moc hc
        (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word),
      sg <> [] -> signer_chain usegs mc (sbl sg ++ LB) a sg ->
      gv lw p hcs (sbl sg) mc moc hc ->
      (forall mc' moc' hc' (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y28 y29 y30 y31 : word),
          gv lw p hcs [] mc' moc' hc' ->
          aevtM usegs moc' POST
            (MS (mkR y1 SP' gp tp y5 y6 y7 (Z_to_bv 64 SIG) x9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 x24 s9 s10 s11 y28 y29 y30 y31)
                F (Z_to_bv 64 0x1e17c) fc None mc' (seg_rom usegs))) ->
      aevtM usegs moc POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 (Z_to_bv 64 SIG) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 a) x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x1e198) fc None mc (seg_rom usegs)).
    Proof.
      intros sg. induction sg as [|[a0' ns] r IH];
        intros a lw p hcs mc moc hc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 HNE HSC D K; [congruence|].
      pose proof D as D0. gv_open D.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof LOSP as LOSP'. pose proof SLO320 as SLO320'. pose proof alloc_ceiling_pos as ACP.
      destruct (signer_chain_uncons usegs _ _ _ _ _ _ HSC) as (<- & HIN & HAL & HPOS & inext & nxt & j & HNODE & HNC & HSC').
      pose proof (HND _ _ _ _ HHc) as NDL. cbn [sbl] in NDL. rewrite !map_app, map_fst_SNAME in NDL. cbn [map fst] in NDL. rewrite <- !app_assoc in NDL.
      destruct (nodup4 _ _ _ _ NDL) as (ND1 & ND2 & ND3 & ND4).
      destruct (heap_blocks usegs L HI _ _ _ _ HHc) as [BRc _]. pose proof BRc as BRc'. rewrite Forall_forall in BRc'.
      destruct (BRc' _ HIN) as (_ & _ & _ & Bce & _). cbn [fst snd] in Bce. unfold SIGNER_SIZE in Bce.
      (* [comment removed for export] *)
      pose proof HNODE as HNODE'. unfold signer_cells in HNODE'.
      change (rw_cells usegs mc a ([CB 80 (sj0 j)] ++ [C8 (Z_to_bv 64 inext)] ++ [C1 (sj_merged j); CB 7 (sj1 j); CB 96 (sj2 j); C8 (Z_to_bv 64 nxt)])) in HNODE'.
      destruct (rw_cells_split3 usegs mc a _ _ _ HNODE') as (_ & CIN & CR3). cbn [cells_size csize Nat.add length] in CIN, CR3.
      replace (a + Z.of_nat 80) with (a + 80) in CIN by lia.
      change (rw_cells usegs mc (a + Z.of_nat 80 + Z.of_nat 8) ([C1 (sj_merged j); CB 7 (sj1 j); CB 96 (sj2 j)] ++ [C8 (Z_to_bv 64 nxt)] ++ [])) in CR3.
      destruct (rw_cells_split3 usegs mc _ _ _ _ CR3) as (_ & CNX & _). cbn [cells_size csize Nat.add length] in CNX.
      replace (a + Z.of_nat 80 + Z.of_nat 8 + Z.of_nat 104) with (a + 192) in CNX by lia. clear CR3 HNODE'.
      pose proof (chain_addr_range usegs _ _ _ _ _ _ _ HNC) as IB.
      zstep. zstep; if_cases KAL; zify_cond KAL; [al8_close KAL|].
      zstep.                                   (* [comment removed for export] *)
      zstep.                                   (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (AT64 : forall mX moX hX (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y23 y28 y29 y30 y31 : word),
        gv lw p hcs (sbl r ++ [(a, SIGNER_SIZE)]) mX moX hX -> signer_chain usegs mX ((sbl r ++ [(a, SIGNER_SIZE)]) ++ LB) nxt r ->
        rw_cells usegs mX (a + 80) [C8 (Z_to_bv 64 inext)] ->
        aevtM usegs moX POST
          (MS (mkR y1 SP' gp tp y5 y6 y7 (Z_to_bv 64 SIG) x9 (Z_to_bv 64 0) y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 a) (Z_to_bv 64 nxt) y20 y21 y22 y23 x24 s9 s10 s11 y28 y29 y30 y31)
              F (Z_to_bv 64 0x1e184) fc None mX (seg_rom usegs))).
      { intros mX moX hX y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y23 y28 y29 y30 y31 G0 HSCr0 CINX.
        clear HHc HTc MFc HPXc FR PPc Hpc CS CSZ DAc BYc MIc SOc STc MK CIN CNX HNODE. pose proof G0 as G. gv_open G.
        pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK.
        assert (HINa : In (a, SIGNER_SIZE) (sbl r ++ [(a, SIGNER_SIZE)])) by (apply in_or_app; right; left; reflexivity).
        destruct (heap_blocks usegs L HI _ _ _ _ HHc) as [BRa APa]. pose proof BRa as BRa'. rewrite Forall_forall in BRa'.
        destruct (BRa' _ (in_or_app _ _ _ (or_introl HINa))) as (Bpa & _ & _ & Bcea & _). cbn [fst snd] in Bpa, Bcea. unfold SIGNER_SIZE in Bcea.
        assert (DJB : a + 200 <= BUF \/ BUF + n <= a).
        { pose proof (HND _ _ _ _ HHc) as NDx. rewrite map_app in NDx.
          assert (NEb : a <> BUF).
          { intros EQ. apply (NoDup_app_notin_l _ _ a NDx).
            - rewrite EQ. exact (in_map fst _ _ BIN).
            - exact (in_map fst _ _ HINa). }
          exact (blocks_apart_in2 _ _ _ _ _ APa (in_or_app _ _ _ (or_introl HINa)) (in_or_app _ _ _ (or_intror BIN)) NEb). }
        pose proof (conj HHc (conj FR (conj PPc (conj CS (conj DAc (conj BYc (conj HSCr0 (conj SOc I)))))))) as CBOX. clear FR PPc CS DAc BYc HHc HSCr0 G0 SOc.
        pose proof (munch_refl [(a + 80, a + 88)] mX) as MU1. pose proof (wmono_refl usegs mX) as WM1.
        zstep.                                 (* [comment removed for export] *)
        lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mS end.
        ddestruct CBOX as (HHc & FR & PPc & CS & DAc & BYc & HSCr0 & SOc & _).
        assert (WF1 : wfp (sbl r ++ [(a, SIGNER_SIZE)]) [(a + 80, a + 88)]).
        { intros x Hnx. cbn [outside] in Hnx. right; right; right. exists (a, SIGNER_SIZE). split; [exact HINa|]. cbn [fst snd]. unfold SIGNER_SIZE. lia. }
        pose proof (HEAPm _ _ _ _ _ _ HHc HTc MU1 WM1 WF1) as HH1s.
        pose proof (HPXm _ _ _ _ _ _ HHc MU1 WM1 WF1) as HPX01.
        lazymatch type of SOc with statics_ok _ _ mS => rename SOc into SO1 | _ => pose proof (SOm _ _ _ _ _ _ HHc SOc MU1 WF1) as SO1; clear SOc end.
        pose proof (rw_cells_transport usegs _ mX mS _ _ FR MU1 WM1 ltac:(cbn; lia)) as FR'.
        pose proof (rw_cells_transport usegs _ mX mS _ _ PPc MU1 WM1 ltac:(cbn; lia)) as PPc'.
        pose proof (rw_cells_transport usegs _ mX mS _ _ CS MU1 WM1 ltac:(cbn [disjoint_from]; rewrite CSZ; lia)) as CS'.
        pose proof (rw_cells_transport usegs _ mX mS _ _ DAc MU1 WM1 ltac:(cbn; lia)) as DAc'.
        pose proof (bytes_at_transport usegs _ mX mS _ _ BYc MU1 ltac:(cbn [disjoint_from]; lia)) as BYc'.
        assert (G : gv lw p hcs (sbl r ++ [(a, SIGNER_SIZE)]) mS moX hX).
        { split; [exact HH1s|]. split; [exact HTc|]. split; [exact MFc|]. split; [eapply heap_presx_trans; [exact HPXc| exact HPX01] |].
          split; [eexists; exact FR'|]. split; [exact PPc'|]. split; [exact Hpc|]. split; [exact CS'|]. split; [exact CSZ|].
          split; [exact DAc'|]. split; [exact BYc'|]. split; [assumption|]. split; [exact SO1| exact STc]. }
        pose proof HHc as HHX.
        clear HHc HTc MFc HPXc FR PPc Hpc CS CSZ DAc BYc MIc STc MK FR' PPc' CS' DAc' BYc' HH1s HPX01 SO1 WF1 BRa BRa' APa.
        pose proof G as G0. gv_open G. pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK.
        zstep.                                 (* [comment removed for export] *)
        zstep.                                 (* [comment removed for export] *)
        replace (Z_to_bv 64 260760 : word) with (Z_to_bv 64 (hl_free L) : word) by (rewrite HFREE; reflexivity).
        pose proof (unsigned_lit (bv_unsigned sp + -96) ltac:(lia)) as USP.
        eapply aevtM_cut.
        { eapply (heap_free usegs L HI) with (A := a) (n := SIGNER_SIZE) (lo := lo) (h := hX) (LB := (sbl r ++ [(a, SIGNER_SIZE)]) ++ LB);
            [ exact HHc | apply in_or_app; left; apply in_or_app; right; left; reflexivity | rewrite USP; exact STc | exact CEIL | rewrite USP; lia | exact MIc | exact TP
            | rewrite USP, HTc; lia | reflexivity ]. }
        intros ms' mo'x PO. unfold call_post in PO.
        ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m1 & mo1
                        & E0 & MI1 & ST1 & MF1 & HP1 & h1 & HT1 & HH1).
        injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite USP in ST1, HP1. fix_ret 0x1e190.
        pose proof (HND _ _ _ _ HHc) as ND0. rewrite !map_app in ND0. cbn [map fst] in ND0. apply NoDup_app_inv_l in ND0.
        assert (HINL : In a (map fst (sbl r ++ [(a, SIGNER_SIZE)]))) by (rewrite map_app; apply in_or_app; right; left; reflexivity).
        assert (ELc : lb_remove a (sbl r ++ [(a, SIGNER_SIZE)]) = sbl r).
        { change (sbl r ++ [(a, SIGNER_SIZE)]) with (sbl r ++ (a, SIGNER_SIZE) :: []). rewrite lb_remove_mid; [apply app_nil_r|].
          intros Hx. apply (NoDup_app_notin_l _ _ a ND0); [left; reflexivity| exact Hx]. }
        pose proof (gv_free _ _ _ _ _ _ _ _ _ _ _ G0 HINL HH1 HT1 HP1 MF1 MI1 ST1) as G1. rewrite ELc in G1.
        assert (HSC1 : signer_chain usegs m1 (sbl r ++ LB) nxt r).
        { replace (sbl r ++ LB) with (lb_remove a ((sbl r ++ [(a, SIGNER_SIZE)]) ++ LB)) by (rewrite lb_remove_app_l by exact HINL; rewrite ELc; reflexivity).
          eapply signer_chain_free_other; [exact HSCr0| | exact (hp_store_free _ _ _ _ _ _ _ _ (a + 80) (a + 88) HHX HINa ltac:(lia) ltac:(unfold SIGNER_SIZE; lia) MU1 WM1 HP1)].
          intros b Hb E. apply (NoDup_app_notin_l _ _ (fst b) ND0); [left; symmetry; exact E|].
          pose proof (sbl_perm r) as PB. apply (in_map fst). eapply Permutation_in; [apply Permutation_sym; exact PB| exact Hb]. }
        clear HHc HPXc SOc STc MIc MK HP1 G0. pose proof G1 as G1'. destruct G1' as (HH1' & _). pose proof (heap_mok _ _ HI _ _ _ _ HH1') as MK.
        zstep.                                 (* [comment removed for export] *)
        zstep. if_cases KZ; zify_cond KZ.
        - (* [comment removed for export] *)
          destruct r as [|[a2 ns2] r2].
          2:{ exfalso. pose proof (signer_chain_uncons usegs _ _ _ _ _ _ HSC1) as (-> & _ & _ & HP2 & _).
              destruct (heap_blocks usegs L HI _ _ _ _ HH1') as [BRx _]. rewrite Forall_forall in BRx.
              pose proof (signer_chain_uncons usegs _ _ _ _ _ _ HSC1) as (_ & HINx & _). destruct (BRx _ HINx) as (_ & _ & _ & Bx & _). cbn [fst snd] in Bx.
              kz KZ. lia. }
          cbn [sbl app] in G1. eapply K. exact G1.
        - (* [comment removed for export] *)
          destruct r as [|[a2 ns2] r2]; [exfalso; cbn in HSC1; subst nxt; clear - KZ; cbv in KZ; lia|].
          eapply (IH nxt lw p hcs m1 mo1 h1); [congruence| exact HSC1| exact G1| exact K]. }
      zstep. if_cases KI; zify_cond KI.
      - (* [comment removed for export] *)
        destruct ns as [|n1 rest].
        2:{ exfalso. pose proof (chain_uncons usegs _ _ _ _ _ _ _ _ HNC) as (-> & _ & _ & HP2 & _). kz KI; lia. }
        cbn [sbl rev SNAME map app] in D0, HSC'. cbn in HNC. subst inext.
        eapply AT64; [| first [exact HSC' | rewrite <- app_assoc in HSC'; exact HSC' | rewrite app_assoc in HSC'; exact HSC'] | exact CIN ]. exact D0.
      - destruct ns as [|n1 rest]; [exfalso; cbn in HNC; subst inext; clear - KI; cbv in KI; lia|].
        cbn [sbl] in D0, HSC', HNC.
        eapply (CL3 (n1 :: rest) inext lw p hcs (sbl r) [(a, SIGNER_SIZE)]
                  (fun mX Lx => signer_chain usegs mX (Lx ++ LB) nxt r /\ In (a, SIGNER_SIZE) Lx /\ rw_cells usegs mX (a + 80) [C8 (Z_to_bv 64 inext)]) mc moc hc);
          [congruence| exact HNC| | | exact D0| | |].
        + (* [comment removed for export] *)
          apply List.NoDup_rev in ND1. rewrite rev_involutive in ND1. exact ND1.
        + intros x Hx. apply ND2. apply (proj1 (in_rev _ _)). exact Hx.
        + split; [exact HSC'| split; [apply in_or_app; right; apply in_or_app; right; left; reflexivity| exact CIN]].
        + (intros mX mY hX moX rest' x dd_H; ddestruct dd_H as (R1 & R2 & R3); intros Hx Hnr HHx HPx).
          pose proof (HND _ _ _ _ HHx) as NDx. cbn [sbl] in NDx. rewrite !map_app, map_fst_SNAME in NDx. cbn [map fst] in NDx. rewrite <- !app_assoc in NDx.
          destruct (nodup4 _ _ _ _ NDx) as (NX1 & NX2 & NX3 & NX4).
          assert (XA : ~ In x (map fst (sbl r))) by (apply NX2; apply (proj1 (in_rev _ _)); left; reflexivity).
          assert (NA : x <> a) by (intros ->; apply (NX3 a); [apply (proj1 (in_rev _ _)); left; reflexivity| left; reflexivity]).
          rewrite <- (rm_node (sbl r) [(a, SIGNER_SIZE)] x rest' XA Hnr).
          split; [| split; [apply In_lb_remove_keep'; [exact R2| cbn; intros E; exact (NA (eq_sym E))] |
                             eapply heap_pres_rw_cells; [exact HPx| exact R3| eapply client_range_block;
                               [apply In_lb_remove_keep'; [apply in_or_app; left; exact R2| cbn; intros E; exact (NA (eq_sym E))]| lia| cbn [cells_size csize Nat.add]; unfold SIGNER_SIZE; lia]]]].
          rewrite <- (lb_remove_app_l x _ LB (in_node _ _ x rest')).
          eapply signer_chain_free_other; [exact R1| | exact HPx].
          intros b Hb E. apply XA. rewrite <- E. apply (in_map fst). eapply Permutation_in; [apply Permutation_sym; apply sbl_perm| exact Hb].
        + (intros mc' moc' hc' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y23 y28 y29 y30 y31 G dd_H; ddestruct dd_H as (R1 & R2 & R3)).
          eapply AT64; [exact G| exact R1| exact R3].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00B0@D11805467289.137D13112141392.139D21157640433.139D21172136973.137D67183863355.137D67186111175.139L11799358114.144L25764509176.141L26295853967.146L34192597267.149L35992031848.145L46961339658.150L53235813056.146L56401235646.149L59308633593.1  L59308752027.149L6139713783.140 L67011298662.14700000W02702j03Q04804k05S05T06;07H07o08W0:<0;I0;M0<50<e0>:S2sp2PP3SIG4DALG2bs6inext05snext3sjh2HBS1L3HLS3DHI2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR6SLO3046inext05snext3sjh3ACP2HB5Ha_st5Hl_stS2sp2PP3SIG4DALG2bs6inext05snext3sjh2HB5Ha_st5Hl_stS2sp2PP3SIG4DALG2bs6inext05snext3sjh2HBS2sp2PP3SIG4DALG2bs6inext05snext3sjh2HBS2sp2PP3SIG4DALG2bs6inext05snext3sjh2HB5Ha_st5Hl_stS2sp2PP3SIG4DALG2bs3SG16inext05snext3sjhFS2sp2PP3SIG4DALG2bs2D36inext05snext3sjhS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR6SLO3046inext05snext3sjh3ACPS2sp2PP3SIG4DALG2bs2D16inext05snext3sjhS1L2sp2PP3SIG4DALG2bs6inext05snext3sjh1aS1L3HLS2sp2PP3SIG4DALG2lo2bs3ALP3ALS3ALD3PP13SG13DA14CEIL4SP163SPR6SLO3046inext03sjh2a13ACP2KZ3HP22BxS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR6SLO3046inext05snext3sjh3ACPS2KZS2sp2PP3SIG4DALG2bs6inext03sjh2a12KZ3HP2S2sp2PP3SIG4DALG2lo2bs6inext05snext3sjh2sg1a3HnaS1L3HLS2sp2PP3BUF3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR6SLO3043BCE6inext05snext3sjh3ACP". (* [comment removed for export] *)
    #[using="HFREE HCALLOC HMSF HLS SW DIMG DHI HND GETALG HH ALP BIN B5 ALS ALD PP1 PP2 SG1 SG2 DA1 DA2 D1 D2 D3 CEIL SLO SP16 SPTOP TP SPR LOSP SLO320 BCE"] Lemma CL_50 : forall lw p (inext0 snext : Z) sjh (sg : list (Z * list Z)) mc moc hc (r : Z)
        (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word),
      gv lw p (signer_cells inext0 snext sjh) (sbl sg) mc moc hc ->
      signer_chain usegs mc (sbl sg ++ LB) snext sg -> -2^31 < r < 2^31 ->
      aevtM usegs moc POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 (Z_to_bv 64 SIG) (Z_to_bv 64 r) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x1e170) fc None mc (seg_rom usegs)).
    Proof.
      intros lw p inext0 snext sjh sg mc moc hc r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 D HSC Hr. gv_open D.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof LOSP as LOSP'. pose proof alloc_ceiling_pos as ACP.
      pose proof (signer_chain_nonnull usegs _ _ _ _ HSC) as HNN.
      unfold signer_cells in CS. cbn [sj0 sj_merged sj1 sj2] in CS.
      zstep.                                   (* [comment removed for export] *)
      pose proof (conj HHc (conj FR (conj PPc (conj DAc (conj BYc I))))) as CBOX. clear FR PPc DAc BYc HHc.
      pose proof (munch_refl [(SIG + 80, SIG + 88)] mc) as MU1. pose proof (wmono_refl usegs mc) as WM1.
      zstep.                                   (* [comment removed for export] *)
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      ddestruct CBOX as (HHc & FR & PPc & DAc & BYc & _).
      assert (WF1 : wfp (sbl sg) [(SIG + 80, SIG + 88)]) by (intros a Hna; cbn [outside] in Hna; first [clear_disj; lia | lia]).
      pose proof (HEAPm _ _ _ _ _ _ HHc HTc MU1 WM1 WF1) as HH1.
      pose proof (HPXm _ _ _ _ _ _ HHc MU1 WM1 WF1) as HPX01.
      lazymatch type of SOc with statics_ok _ _ m1 => rename SOc into SO1 | _ => pose proof (SOm _ _ _ _ _ _ HHc SOc MU1 WF1) as SO1; clear SOc end.
      pose proof (rw_cells_transport usegs _ mc m1 _ _ FR MU1 WM1 ltac:(cbn; lia)) as FR'.
      pose proof (rw_cells_transport usegs _ mc m1 _ _ PPc MU1 WM1 ltac:(cbn; unfold SIGNER_SIZE in D1; lia)) as PPc'.
      pose proof (rw_cells_transport usegs _ mc m1 _ _ DAc MU1 WM1 ltac:(cbn; unfold SIGNER_SIZE in D3; lia)) as DAc'.
      pose proof (bytes_at_transport usegs _ mc m1 _ _ BYc MU1 ltac:(cbn; lia)) as BYc'.
      (* [comment removed for export] *)
      assert (HSC1 : signer_chain usegs m1 (sbl sg ++ LB) snext sg).
      { destruct (heap_blocks usegs L HI _ _ _ _ HHc) as [BR _].
        eapply signer_chain_presx2 with (X := X0) (CE := alloc_ceiling) (Lp := sbl sg ++ LB) (SP := bv_unsigned sp);
          [exact HSC| eapply signer_blocks_in; exact HSC| eapply signer_blocks_in; exact HSC| | eapply blocks_below_of_HEAP; exact HHc| constructor; [cbn; lia| constructor; [cbn; lia| constructor]]].
        eapply heap_presx_of_frame_munch; [exact MU1| exact WM1| exact BR| exact DHI|]. intros a. cbn [outside]. lia. }
      assert (G1 : gv lw p (signer_cells 0 snext sjh) (sbl sg) m1 moc hc).
      { split; [exact HH1|]. split; [exact HTc|]. split; [exact MFc|]. split; [eapply heap_presx_trans; [exact HPXc| exact HPX01] |].
        split; [eexists; exact FR'|]. split; [exact PPc'|]. split; [exact Hpc|]. split; [unfold signer_cells; cbn [sj0 sj_merged sj1 sj2]; exact CS|]. split; [reflexivity|].
        split; [exact DAc'|]. split; [exact BYc'|]. split; [assumption|]. split; [exact SO1| exact STc]. }
      clear HHc MU1 WM1 MK FR PPc DAc BYc. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
      zstep. if_cases KZ; zify_cond KZ.
      - (* [comment removed for export] *)
        destruct sg as [|[a1 ns1] r1]; [exfalso; cbn in HSC1; subst snext; clear - KZ; cbv in KZ; lia|].
        eapply (CL2 ((a1, ns1) :: r1) snext lw p _ m1 moc hc); [congruence| exact HSC1| exact G1|].
        intros mc' moc' hc' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y28 y29 y30 y31 G'.
        eapply CL_END; [exact G'| exact Hr].
      - destruct sg as [|[a1 ns1] r1].
        2:{ exfalso. destruct (signer_chain_uncons usegs _ _ _ _ _ _ HSC1) as (-> & HINx & _ & HP2 & _).
            destruct (heap_blocks usegs L HI _ _ _ _ HH1) as [BRx _]. rewrite Forall_forall in BRx.
            destruct (BRx _ HINx) as (_ & _ & _ & Bx & _). cbn [fst snd] in Bx. kz KZ; lia. }
        cbn [sbl] in G1. eapply CL_END; [exact G1| exact Hr].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0060@L11939080819.141L48167901769.141L55276347018.142L55748194565.143L59308631400.1  L59310680273.14500000T01;01a02E02I030S2sp2PP3SIG4DALG2bs6inext05snext3sjhS2sp2PP3SIG4DALG2bs6inext05snext3sjh2IBS2sp2PP3SIG4DALG2bs5snext3sjh2n12IB2KIS2sp2PP3SIG4DALG2bs6inext05snext3sjhS2KIS2sp2PP3SIG4DALG2bs5snext3sjh2n12KI3HP2". (* [comment removed for export] *)
    #[using="HFREE HCALLOC HMSF HLS SW DIMG DHI HND GETALG HH ALP BIN B5 ALS ALD PP1 PP2 SG1 SG2 DA1 DA2 D1 D2 D3 CEIL SLO SP16 SPTOP TP SPR LOSP SLO320 BCE"] Lemma CLEAN : forall lw p (inext0 snext : Z) sjh (names0 : list Z) (sg : list (Z * list Z)) mc moc hc (r : Z)
        (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word),
      gv lw p (signer_cells inext0 snext sjh) (sbl sg ++ SNAME (rev names0)) mc moc hc ->
      name_chain usegs (fun _ => True) mc ((sbl sg ++ SNAME (rev names0)) ++ LB) inext0 names0 ->
      signer_chain usegs mc ((sbl sg ++ SNAME (rev names0)) ++ LB) snext sg -> -2^31 < r < 2^31 ->
      aevtM usegs moc POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 (Z_to_bv 64 SIG) (Z_to_bv 64 r) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x1e148) fc None mc (seg_rom usegs)).
    Proof.
      intros lw p inext0 snext sjh names0 sg mc moc hc r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 D HNC HSC Hr.
      pose proof D as D0. gv_open D.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof LOSP as LOSP'. pose proof alloc_ceiling_pos as ACP.
      pose proof (chain_addr_range usegs _ _ _ _ _ _ _ HNC) as IB.
      pose proof (HND _ _ _ _ HHc) as NDL. rewrite !map_app, map_fst_SNAME in NDL. rewrite <- !app_assoc in NDL.
      pose proof CS as CS'. unfold signer_cells in CS'. cbn [sj0 sj_merged sj1 sj2] in CS'.
      change (rw_cells usegs mc SIG ([CB 80 (sj0 sjh)] ++ [C8 (Z_to_bv 64 inext0)] ++ [C1 (sj_merged sjh); CB 7 (sj1 sjh); CB 96 (sj2 sjh); C8 (Z_to_bv 64 snext)])) in CS'.
      destruct (rw_cells_split3 usegs mc SIG _ _ _ CS') as (_ & CIN & _). clear CS'. cbn [cells_size csize Nat.add length] in CIN.
      replace (SIG + Z.of_nat 80) with (SIG + 80) in CIN by lia.
      zstep. zstep; if_cases KAL; zify_cond KAL; [al8_close KAL|].
      zstep.                                   (* [comment removed for export] *)
      zstep. if_cases KI; zify_cond KI.
      - (* [comment removed for export] *)
        destruct names0 as [|n1 rest].
        2:{ exfalso. destruct (chain_uncons usegs _ _ _ _ _ _ _ _ HNC) as (-> & _ & _ & HP2 & _). kz KI; lia. }
        cbn [rev SNAME map] in D0, HSC. rewrite app_nil_r in D0, HSC.
        eapply CL_50; [exact D0| exact HSC| exact Hr].
      - destruct names0 as [|n1 rest]; [exfalso; cbn in HNC; subst inext0; clear - KI; cbv in KI; lia|].
        eapply (CL1 (n1 :: rest) inext0 lw p _ (sbl sg) [] (fun mX Lx => signer_chain usegs mX (Lx ++ LB) snext sg) mc moc hc);
          [congruence| rewrite app_nil_r; exact HNC| | | rewrite app_nil_r; exact D0| rewrite app_nil_r; exact HSC| |].
        + apply NoDup_app_inv_r in NDL. apply NoDup_app_inv_l in NDL. apply List.NoDup_rev in NDL. rewrite rev_involutive in NDL. exact NDL.
        + intros x Hx. apply (NoDup_app_notin_l _ _ x NDL). apply in_or_app. left. apply (proj1 (in_rev _ _)). exact Hx.
        + intros mX mY hX moX rest' x R1 Hx Hnr HHx HPx.
          pose proof (HND _ _ _ _ HHx) as NDx. rewrite !map_app, map_fst_SNAME in NDx. rewrite <- !app_assoc in NDx.
          assert (XA : ~ In x (map fst (sbl sg))).
          { apply (NoDup_app_notin_l _ _ x NDx). apply in_or_app. left. apply (proj1 (in_rev _ _)). left. reflexivity. }
          rewrite <- (rm_node (sbl sg) [] x rest' XA Hnr). rewrite <- (lb_remove_app_l x _ LB (in_node _ _ x rest')).
          eapply signer_chain_free_other; [exact R1| | exact HPx].
          intros b Hb E. apply XA. rewrite <- E. apply (in_map fst). eapply Permutation_in; [apply Permutation_sym; apply sbl_perm| exact Hb].
        + intros mc' moc' hc' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y28 y29 y30 y31 G' R'.
          rewrite app_nil_r in G', R'. eapply CL_50; [exact G'| exact R'| exact Hr].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


    (* [comment removed for export] *)
    #[using="Type"] Lemma blk_disj : forall hc Lx mX moX b1 b2, HEAP usegs L HI hc Lx mX moX -> In b1 Lx -> In b2 Lx -> b1 <> b2 -> 0 < snd b1 -> 0 < snd b2 ->
      fst b1 + snd b1 <= fst b2 \/ fst b2 + snd b2 <= fst b1.
    Proof.
      intros hc Lx mX moX b1 b2 HHx H1 H2 NE P1 P2. destruct (heap_blocks usegs L HI _ _ _ _ HHx) as [_ AP].
      eapply blocks_apart_neq; eassumption.
    Qed.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L26394397344.102L35497646224.100L964115206.102  00000H00[017S2sp2PP3SIG4DALG2bs1x2csS2sp2PP3SIG4DALG2bsS2sp2PP3SIG4DALG2bs1x2cs3Hsz". (* [comment removed for export] *)
    #[using="sp PP SIG DALG bs"] Lemma splink_pres : forall mA mB L1 L2 SPx a l e,
      splink usegs mA L1 a l e -> (forall b, In b L1 -> In b L2) -> heap_pres usegs L L2 SPx mA mB -> splink usegs mB L2 a l e.
    Proof.
      intros mA mB L1 L2 SPx a l e HSL HL HP. eapply splink_mem; [exact HSL| intros x _ Hx; apply HL; exact Hx| |].
      - intros x cs Hx _ HR Hsz. eapply heap_pres_rw_cells; [exact HP| exact HR| eapply client_range_block; [apply HL; exact Hx| lia| lia]].
      - intros inext names _ HN. eapply chain_pres; [exact HN| intros x Hx; apply HL; eapply chain_nodes_in; [exact HN| exact Hx] | exact HP| unfold NAME_SIZE; lia].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L26394397344.104L35497646224.102L964115206.104  00000H00[017S2sp2PP3SIG4DALG2bs1x2csS2sp2PP3SIG4DALG2bsS2sp2PP3SIG4DALG2bs1x2cs3Hsz". (* [comment removed for export] *)
    #[using="sp PP SIG DALG bs"] Lemma splink_presx : forall mA mB L1 SPx X a l e,
      splink usegs mA L1 a l e -> heap_presx usegs L L1 SPx X mA mB ->
      (forall x, In (x, SIGNER_SIZE) L1 -> In x (map fst l) -> disjoint_from X x SIGNER_SIZE) ->
      (forall inext names x, In names (map snd l) -> name_chain usegs (fun _ => True) mA L1 inext names -> In x names -> disjoint_from X x NAME_SIZE) ->
      splink usegs mB L1 a l e.
    Proof.
      intros mA mB L1 SPx X a l e HSL HP HD1 HD2. eapply splink_mem; [exact HSL| intros x _ Hx; exact Hx| |].
      - intros x cs Hx Hl HR Hsz. eapply heap_presx_rw_cells; [exact HP| exact HR| eapply client_range_block; [exact Hx| lia| lia] | rewrite Hsz; apply HD1; assumption].
      - intros inext names Hn HN. eapply chain_presx; [exact HN| intros x Hx; eapply chain_nodes_in; [exact HN| exact Hx] | exact HP| unfold NAME_SIZE; lia|].
        intros x Hx. eapply HD2; eassumption.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0040@L38087551012.101L68102275306.104L68104379411.102L68104379411.10500000H02203:04PS2sp2PP3SIG4DALG2bs1a2HoS1L3HLS3DHI1l2l02sp2PP3SIG4DALG2lo2bs3ALP3ALS3ALD3PP13SG13DA12D12D22D34CEIL3SPR6SLO3042Sn2Bp3Bce4Bimg1a2C1S1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA12D14CEIL3SPR6SLO3042Sn3Bce1a1C1HS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA12D12D22D34CEIL3SPR6SLO3042Sn2Bp3Bce1a1B1k2Hr1H". (* [comment removed for export] *)
    #[using="HI HFREE HCALLOC HMSF HLS SW DIMG DHI GETALG DALG lo bs ALP ALS ALD PP1 SG1 DA1 D1 D2 D3 CEIL SLO SPR SLO320"] Lemma HPXcall : forall Lx mA mB Sn SPx,
      heap_presx usegs L (Lx ++ LB) SPx [(PP, PP + 8); (Sn, Sn + SIGNER_SIZE)] mA mB -> SPx <= bv_unsigned sp ->
      (forall B k, In (B, k) LB -> Sn + SIGNER_SIZE <= B \/ B + k <= Sn) -> block_range L Sn SIGNER_SIZE ->
      heap_presx usegs L LB (bv_unsigned sp) X0 mA mB.
    Proof.
      (intros Lx mA mB Sn SPx HP HSP HAP dd_H; ddestruct dd_H as (Bp & _ & _ & Bce & Bimg); intros a Ha Hc Ho).
      apply HP; [exact Ha| eapply client_addr_sub; [exact Hc| intros b Hb; apply in_or_app; right; exact Hb| exact HSP] |].
      cbn [outside] in Ho |- *. split; [lia|]. split; [| exact I].
      destruct Hc as [C|[[C1 C2]|(b & Hb & Hr)]]; [pose proof alloc_ceiling_pos; unfold SIGNER_SIZE in *; lia| destruct DIMG; unfold SIGNER_SIZE in *; lia|].
      destruct b as [B k]. cbn in Hr. destruct (HAP B k Hb); unfold SIGNER_SIZE in *; lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


    (* [comment removed for export] *)
    Definition OPEN (mc : mem) (Lc : list blk) (inext0 : Z) (names0 : list Z) (S1 : Z) (mid : list (Z * list Z))
        (prev pinext : Z) (pnames : list Z) (psj : signer_junk) : Prop :=
      name_chain usegs (fun _ => True) mc (Lc ++ LB) inext0 names0
      /\ splink usegs mc (Lc ++ LB) S1 mid prev
      /\ rw_cells usegs mc prev (signer_cells pinext 0 psj) /\ name_chain usegs (fun _ => True) mc (Lc ++ LB) pinext pnames
      /\ prev mod 16 = 0 /\ 0 < prev /\ In (prev, SIGNER_SIZE) Lc
      /\ (prev + SIGNER_SIZE <= BUF \/ BUF + n <= prev)
      /\ ~ In prev (map fst mid)
      /\ Lc = sbl (mid ++ [(prev, pnames)]) ++ SNAME (rev names0).

    #[using="Type"] Lemma CLOSE : forall mc Lc inext0 names0 S1 mid prev pinext pnames psj,
      OPEN mc Lc inext0 names0 S1 mid prev pinext pnames psj -> signer_chain usegs mc (Lc ++ LB) S1 (mid ++ [(prev, pnames)]).
    Proof.
      (intros mc Lc inext0 names0 S1 mid prev pinext pnames psj dd_H; ddestruct dd_H as (HN0 & HSP & PC & PN & PAL & PPOS & PIN & PVB & PNM & ELc)).
      apply splink_to_chain. eapply splink_snoc; [exact HSP| apply in_or_app; left; exact PIN| exact PAL| exact PPOS| exact PC| exact PN].
    Qed.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0210@D11805467289.233D42334553026.233D42340767550.235D44952082128.235D44958253612.233D47187829423.235L10258900290.194L10258900291.242L10258900292.262L10823794898.241L10823794899.193L10823794901.261L1107921941.243 L11799358116.243L12490298163.192L12490298165.260L12490346674.240L12660708096.241L12660708097.193L12660708103.261L12742724653.251L13350887686.229L13758561961.270L1386317440.229 L144322240.248  L18590715291.243L18938186279.188L20323745488.258L20323745494.190L20763674639.249L21522780934.249L21597088058.272L21618791845.249L23472204939.240L26014308813.241L26071143599.159L26302364563.246L26394397344.272L27850914432.242L27850914433.194L27850914439.262L30993653749.241L31094837846.249L3119769277.238 L32483077380.238L32495795635.191L32495795637.259L33458987027.245L35485062061.197L35485067181.198L35497640934.253L35499744614.246L35499744614.255L35499744614.268L35818434833.185L35992031860.244L36253174270.195L39360456046.189L39360717918.239L39360801497.257L39371603223.188L39416392300.233L39475339063.257L41202929119.231L41296042896.15 L41354231767.241L42152566795.20 L43069468223.249L4503812482.248 L46091134646.249L46143082231.164L46146881298.261L46148978534.253L46885407252.249L46887586699.266L46961339658.251L47187829423.230L48182046655.240L4909481499.242 L49988000865.254L49988000865.262L508271316.239  L51585051053.251L51585051053.254L52087469201.250L52087469201.253L53374987556.261L53646437001.238L53944934877.242L55469950663.233L55476132412.164L56724938549.247L56784471052.266L59308630630.1  L59308630630.194L59314873579.246L59314873579.248L59314873579.251L59314873579.254L59962356165.128L59980467797.242L60382958079.233L60397718788.164L60659831569.250L63090567536.239L65840203855.249L6670147970.18  L67011298682.247L6749227367.164 L6933890443.196 L6933890445.264 L6934137867.236 L7419122673.243 L7828152217.164 R12490559893.195R13587414117.195R18247033200.195R19572124799.195R20323958768.195R25585061457.195R34841085112.195R41293539632.195R43745324333.195R43871310534.195R53850979607.195R56729473832.195R57504388252.195R63261865041.195R64163405490.19500000f01\02^03e04`04a05Q06D07707n08b09Y0<00=d0>X0?O0@F0A=0B10Bh0C_0DY0ET0EU0FL0GA0Hh0I_0JS0LQ0NI0OA0QC0Rn0T;0UZ0WH0X@0Y30Yc0ZV0\E0]J0_80_o0`c0aZ0cH0d80dh0e[0fN0gA0h40hd0jR0kQ0lA0m40mg0nW0oJ10=11011113B13C15`18519019`1:S1;F1=T1?Y1@P1BM1CC1D<1E31Ej1GU1HL1IC1Jn1LY1LZ1MP1NP1OO1PK1QD1R>1RB1S<1Sl1Ta1UV1VK1YW1[B1\B1]?1^m1_d1`Y1`Z1aU1bE1c51ch1d[1fh1gX1hO1jL1l71n<1o320f22k22l22m23d25Y25Z27E29<2;3S2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn2HBS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn2HBS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn2HB5Ha_st5Hl_stS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk4PPOS2Sn2HB5Ha_st5Hl_stS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk4PPOS2Sn2HBFS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2HkS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3BUF3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3BUF3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2HkS2sp2PP3BUF3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2SnS1L3HLS2sp2PP1P3END3BUF3SIG4DALG2lo2bs2B12B32B42B53PP13SG13DA14CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk3Hp13HES4PPOS7SLO304'3ACP4BCE'2Sn3SnP2p24Hp2'5HprogS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA12D12D22D34CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk4PPOS7SLO304'3ACP4PVce2Sn3SnPS2sp2PP3SIG4DALG2bs3DA11k2ES1p6inext03sjh2S14prev2HkS2sp2PP3SIG4DALG2bs3DA11k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3SIG4DALG2bs3DA11k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3BUF3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3BUF3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2HkS2sp2PP3BUF3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn1x1HS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn2r23Hr2S2sp2LB2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Lc2Hk2Sn1xFS2sp2PP3SIG4DALG2bs1k2ES1p3cnt6inext03sjh2S14prev2Hk2SnS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn1HS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk4PPOS7SLO304'2Sn3SnP4SnCES2sp2PP3SIG4DALG2bs3PP11k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3SIG4DALG2bs3PP11k2ES1p6inext03sjh2S14prev2HkS1L3HLS2sp2PP1P3SIG4DALG2lo2bs3PP13SG13DA12D12D22D34CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk3Hp14PPOS7SLO304'3ACP2Sn3SnP2p25HprogS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA12D12D22D34CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk4PPOS7SLO304'3ACP2Sn3SnP2p25HprogS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn1x2csS1L3HLS2sp2PP1P3SIG4DALG2lo2bs3PP13SG13DA12D12D22D34CEIL3SPR1k2ES1p3cnt6inext03sjh2S14prev2Hk3Hc24PPOS7SLO304'3ACP2Sn3SnP2p25HprogS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk4PPOS7SLO304'3ACP2Sn3SnP4SnCES2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn3SnP2KC2r23Hr22A02kk2Y12Y2S1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk4PPOS7SLO304'3ACPS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA12D14CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk4PPOS7SLO304'3ACP4PVce2Sn3SnPS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn1x2csS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2HkS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2SnS1L3HLS2sp2PP3BUF3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk4PPOS7SLO304'3ACP4BCE'2Sn3SnPS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn3SnP2KC2p24Hp2'2KES1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA12D24CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk4PPOS7SLO304'3ACP2Sn3SnP4SnCES2sp2PP3SIG4DALG2bs3SG11k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3SIG4DALG2bs3SG11k2ES1p6inext03sjh2S14prev2HkS2sp2PP3SIG4DALG2bs3SG11k2ES1p6inext03sjh2S14prev2Hk2SnS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA12D24CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk4PPOS7SLO304'3ACP4PVce2Sn3SnPS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2HkS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2HkS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2HkS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA12D34CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk4PPOS7SLO304'3ACP4PVce2Sn3SnPS1L2sp2PP3SIG4DALG2lo2bs6SLO3041k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2HkS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2HkS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2SnFS1L3HLS2sp2PP1P3END3BUF3SIG4DALG2lo2bs2B12B32B52B63PP13SG13DA14CEIL3SPR1k2ES1p3cnt6inext03sjh2S14prev2Hk3Hp23HES3Hc13Hc24PPOS7SLO304'4BCE'2Sn3SnPFS1L3HLS2sp2PP1P3END3BUF3SIG4DALG2lo2bs2B12B32B53PP13SG13DA12D34CEIL3SPR1k2ES1p3cnt6inext03sjh2S14prev2Hk3HES3Hc13Hc24PPOS7SLO304'4BCE'2Sn3SnP2p25Hprog3B6'2KES1L3HLS2sp2PP1P3END3BUF3SIG4DALG2lo2bs2B12B32B53PP13SG13DA12D34CEIL3SPR1k2ES1p3cnt6inext03sjh2S14prev2Hk3Hp23HES3Hc13Hc24PPOS7SLO304'4BCE'2Sn3SnP3B6'S2sp2PP3SIG4DALG2bs1k2ES1p3cnt6inext03sjh2S14prev2Hk3Hc12SnS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2HkS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2SnS1L3HLS2sp2PP1P3END3SIG4DALG2lo2bs3PP13SG13DA12D12D22D34CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk3Hp13HES4PPOS7SLO304'3ACP2Sn3SnP2p24Hp2'5Hprog2KES1L3HLS2sp2PP1P3END3SIG4DALG2lo2bs3PP13SG13DA12D12D22D34CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk3Hp13HES4PPOS7SLO304'3ACP2Sn3SnP2p24Hp2'S1L2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn1aS1L3HLS4DIMG2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk4PPOS7SLO304'3ACP2HD2Sn3SnP2HB5Ha_st5Hl_stS2sp2PP3SIG4DALG2bs2D21k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3BUF3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn1HS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn1x1XS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn1x1XS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk4PPOS7SLO304'3ACP2Sn3SnP4SnCES2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn1x1HS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn1x1HS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk4PPOS7SLO304'3ACP2Sn3SnP1x2BxS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk4PPOS7SLO304'3ACP2Sn3SnP1x2BxFS2sp2PP3SIG4DALG2bs2D11k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn3SnP2KC1a3HnaS1L2sp2PP3SIG4DALG2lo2bs6SLO3041k2ES1p6inext03sjh2S14prev2Hk2SnS1L2sp2PP3SIG4DALG2lo2bs6SLO3041k2ES1p6inext03sjh2S14prev2HkS2sp2PP3BUF3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn1HS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn2r23Hr2S2KCS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn3SnP2KCS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S12Hk2Sn1HS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn1HS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn1HS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn1HS1L2HI2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m2mo1h2LB2PP1P3END3SIG4DALG2lo2bs3dtg4dpad4dlen2dq2ES1p3cnt4prev2mc3moc2x12x52x62x73x103x113x123x133x143x153x163x173x213x283x293x303x312Hk3Hp2S1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk4PPOS7SLO304'3ACP4PVce2Sn3SnPS1L2HI2sp1h2PP3SIG4DALG2bs5SPTOP1k2ES1p6inext03sjh2S14prev2Hk2SnS1L2HI2sp1h2PP3SIG4DALG2bs5SPTOP1k2ES1p6inext03sjh2S14prev2HkS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA12D34CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk4PPOS7SLO304'3ACP2Sn3SnP1x2BxS2sp2PP3SIG4DALG2bs3PP11k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2Sn1HFS2sp2PP3BUF3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk3PVB2SnS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2HkS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2HkS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2SnS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk2SnS1L3HLS2sp2PP1P3END3BUF3SIG4DALG2lo2bs2B12B32B42B53PP13SG13DA14CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk3Hp13Hp23HES4PPOS7SLO304'3ACP4BCE'2Sn3SnPS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2HkS2sp2PP3SIG4DALG2bs3DA11k2ES1p6inext03sjh2S14prev2Hk2SnS1L2HI3HLS2sp1h2PP3SIG4DALG2lo2bs3PP13SG13SG23DA14CEIL3SPR1k2ES1p6inext03sjh2S14prev2hc2Hk3HTc4PPOS7SLO304'3ACP2h13HT12Sn3SnPS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk4PPOS7SLO304'3ACP2Sn3SnP4SnCES1L2HI3HLS2sp1h2PP3SIG4DALG2lo2bs3PP13PP23SG13SG23DA13DA24CEIL3SPR1k2ES1p6inext03sjh2S14prev2hc2Hk3HTc4PPOS7SLO304'3ACP2h13HT12Sn3SnPS2sp2PP3SIG4DALG2bs3PP11k2ES1p6inext03sjh2S14prev2Hk2SnS1L3HLS2sp2PP1P3BUF3SIG4DALG2lo2bs2B13PP13SG13DA14CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk3Hp14PPOS7SLO304'3ACP2Sn3SnPS1L2HI3HLS2sp1h2PP3SIG4DALG2lo2bs3PP13PP23SG13SG23DA13DA24CEIL3SPR1k2ES1p6inext03sjh2S14prev2hc2Hk3HTc4PPOS7SLO304'3ACP2h13HT12Sn3SnPFFS2sp2PP3SIG4DALG2bs1k2ES1p6inext03sjh2S14prev2Hk3Hp22SnS1L3HLS2sp2PP3END3BUF3SIG4DALG2lo2bs2B33PP13SG13DA14CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk3HES4PPOS7SLO304'3ACP2Sn3SnPFS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk4PPOS7SLO304'3ACP2Sn3SnP4SnCES1L3HLS2sp2PP3SIG4DALG2lo2bs3ALP3ALS3ALD3PP13SG13DA14CEIL4SP163SPR1k2ES1p6inext03sjh2S14prev2Hk4PPOS7SLO304'3ACP2Sn3SnPS1L3HLS2sp2PP3SIG4DALG2lo2bs3ALP3ALS3ALD3PP13SG13DA14CEIL3SPR1k2ES1p6inext03sjh2S14prev2Hk4PPOS7SLO304'3ACP2Sn3SnP4SnAL". (* [comment removed for export] *)
    #[using="HFREE HCALLOC HMSF HLS SW DIMG DHI HND GETALG SIGNER HH ALP BIN B1 B3 B4 B5 B6 ALS ALD Q1 Q2 Q3 PP1 PP2 SG1 SG2 DA1 DA2 D1 D2 D3 CEIL SLO SP16 SPTOP TP SPR LOSP SLO320 BCE"] Lemma LOOP : forall (k : nat) (ES p cnt : Z) lw inext0 names0 sjh S1 mid prev pinext pnames psj Lc mc moc hc
        (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word),
      ES - p <= Z.of_nat k -> P < p -> p < ES -> ES <= END -> 1 <= cnt -> cnt <= p - P ->
      gv lw p (signer_cells inext0 S1 sjh) Lc mc moc hc -> OPEN mc Lc inext0 names0 S1 mid prev pinext pnames psj ->
      aevtM usegs moc POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 (Z_to_bv 64 SIG) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 DALG) (Z_to_bv 64 PP) (Z_to_bv 64 ES) x21
                  (Z_to_bv 64 (-22400)) (Z_to_bv 64 cnt) (Z_to_bv 64 prev) s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x1e0d0) fc None mc (seg_rom usegs)).
    Proof.
      induction k as [|k IH]; intros ES p cnt lw inext0 names0 sjh S1 mid prev pinext pnames psj Lc mc moc hc
        x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 Hk Hp1 Hp2 HES Hc1 Hc2 D OP; [lia|].
      pose proof D as D0. gv_open D. pose proof OP as OP0. ddestruct OP as (HN0 & HSP & PC & PN & PAL & PPOS & PIN & PVB & PNM & ELc).
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof LOSP as LOSP'. pose proof SLO320 as SLO320'. pose proof alloc_ceiling_pos as ACP. pose proof BCE as BCE'.
      pose proof (unsigned_lit (bv_unsigned sp + -96) ltac:(lia)) as USP.
      destruct (heap_blocks usegs L HI _ _ _ _ HHc) as [BRc _]. pose proof BRc as BRc'. rewrite Forall_forall in BRc'.
      destruct (BRc' _ (in_or_app _ _ _ (or_introl PIN))) as (_ & _ & _ & PVce & PVimg). cbn [fst snd] in PVce, PVimg. unfold SIGNER_SIZE in PVce, PVimg.
      (* [comment removed for export] *)
      zstep. zstep. zstep.                     (* [comment removed for export] *)
      replace (Z_to_bv 64 260448 : word) with (Z_to_bv 64 (hl_calloc L) : word) by (rewrite HCALLOC; reflexivity).
      eapply aevtM_cut.
      { eapply (heap_calloc usegs L HI) with (cnt := 1) (sz := 200) (lo := lo) (h := hc) (LB := Lc ++ LB);
          [ exact HHc | rewrite USP; exact STc | exact CEIL | rewrite USP; lia | exact MIc | exact TP | rewrite USP, HTc; lia
          | reflexivity | reflexivity | lia | lia | lia ]. }
      intros ms' mo'x PO. unfold call_post in PO.
      ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m1 & mo1
                      & E0 & MI1 & ST1 & MF1 & HP1 & h1 & HT1 & HRES).
      injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite USP in ST1, HP1. fix_ret 0x1e0dc.
      (* [comment removed for export] *)
      assert (SUB : forall b, In b LB -> In b (Lc ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
      pose proof (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP1 FR ltac:(apply client_range_stack; lia)) as FR1.
      pose proof (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP1 PPc ltac:(apply client_range_stack; lia)) as PPc1.
      pose proof (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP1 CS ltac:(apply client_range_stack; lia)) as CS1.
      pose proof (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP1 DAc ltac:(apply client_range_stack; lia)) as DAc1.
      pose proof (heap_pres_bytes_at usegs L _ _ _ _ _ _ HP1 BYc ltac:(eapply client_range_block; [apply SUB; exact BIN| lia| lia])) as BY1.
      pose proof (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP1 PC ltac:(eapply client_range_block; [apply in_or_app; left; exact PIN| lia| cbn; unfold SIGNER_SIZE; lia])) as PC1.
      pose proof (statics_ok_heap_pres' usegs L _ _ _ _ SOc HP1 SW) as SO1.
      assert (HPX1 : heap_presx usegs L LB (bv_unsigned sp) X0 m m1).
      { eapply heap_presx_trans_pres; [exact HPXc| eapply heap_pres_sp_mono; [eapply heap_pres_sub; [exact HP1| exact SUB] | lia] | intros b Hb; exact Hb]. }
      pose proof (chain_pres usegs L _ _ _ _ _ _ _ _ _ _ HN0 ltac:(intros x Hx; eapply chain_nodes_in; [exact HN0| exact Hx]) HP1 ltac:(unfold NAME_SIZE; lia)) as HN01.
      pose proof (chain_pres usegs L _ _ _ _ _ _ _ _ _ _ PN ltac:(intros x Hx; eapply chain_nodes_in; [exact PN| exact Hx]) HP1 ltac:(unfold NAME_SIZE; lia)) as PN1.
      pose proof (splink_pres _ _ _ _ _ _ _ _ HSP ltac:(intros b Hb; exact Hb) HP1) as HSP1.
      clear HPXc FR PPc CS DAc BYc PC SOc STc MIc MK HN0 PN HSP D0 OP0.
      destruct HRES as [[-> HH1] | (Sn & -> & BR & HH1 & RAWZ)].
      { (* [comment removed for export] *)
        pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
        zstep. if_cases KC; zify_cond KC; [| exfalso; clear - KC; cbv in KC; lia].
        zstep. zstep.                          (* [comment removed for export] *)
        eapply (CLEAN lw p inext0 S1 sjh names0 (mid ++ [(prev, pnames)]) m1 mo1 h1 (-22400)); [| | | lia].
        - rewrite <- ELc. split; [exact HH1|]. split; [congruence|]. split; [eapply mo_frame_trans; eassumption|]. split; [exact HPX1|].
          split; [eexists; exact FR1|]. split; [exact PPc1|]. split; [exact Hpc|]. split; [exact CS1|]. split; [exact CSZ|].
          split; [exact DAc1|]. split; [exact BY1|]. split; [exact MI1|]. split; [exact SO1| exact ST1].
        - rewrite <- ELc. exact HN01.
        - rewrite <- ELc. eapply CLOSE. split; [exact HN01|]. split; [exact HSP1|]. split; [exact PC1|]. split; [exact PN1|].
          split; [exact PAL|]. split; [exact PPOS|]. split; [exact PIN|]. split; [exact PVB|]. split; [exact PNM| exact ELc]. }
      (* [comment removed for export] *)
      pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
      pose proof BR as BR0. ddestruct BR as (SnP & SnAL & _ & SnCE & SnIMG). rewrite Z.mul_1_l in SnCE, SnIMG, HH1, RAWZ, BR0.
      destruct (heap_blocks usegs L HI _ _ _ _ HH1) as [BR1 AP1]. cbn [blocks_apart] in AP1. destruct AP1 as [APn _].
      change (Z.to_nat 200) with 200%nat in RAWZ.
      zstep. if_cases KC; zify_cond KC; [exfalso; rewrite ?unsigned_lit in KC by lia; lia|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
      pose proof SIGNER as SPS. unfold pkcs7_signer_stmt, U_PKCS7_SIGNER in SPS.
      eapply aevtM_cut.
      { eapply SPS with (PP := PP) (P := p) (END := ES) (BUF := BUF) (bs := bs) (S := Sn) (DALG := DALG) (lo := lo) (h := h1) (LB := (Sn, 200) :: Lc ++ LB)
                        (sj := SGJ (zeros 80) (Z_to_bv 8 0) (zeros 7) (zeros 96)) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
          try reflexivity; rewrite ?USP; try eassumption; try (is_arith_goal; unfold SIGNER_SIZE in *; plia);
          try (clear - SP16 SPR LOSP' CEIL ACP; Z.div_mod_to_equations; is_arith_goal; lia).
        - right. apply in_or_app. right. exact BIN.
        - eapply rw_cells_reshape; [exact RAWZ| cbn; repeat split; reflexivity| vm_compute; reflexivity].
        - right. left. reflexivity.
        - apply APn. apply in_or_app. right. exact BIN.
        - unfold PKCS7_SIGNER_STACK. lia. }
      intros ms' mo'x PO.
      ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & mo2 & h2 & r2 & p2 & inext2 & sjn & nodes2
                      & E0 & -> & Hr2 & MI2 & SO2 & ST2 & MF2 & HT2 & PPc2 & Hp2' & Hprog & CSn2 & HNn2 & HND2 & HAP2 & HH2 & HPX2 & HRn).
      injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite ?USP in ST2. rewrite ?USP in HPX2. fix_ret 0x1e0f8. clear SPS.
      set (L1 := (Sn, 200) :: Lc ++ LB) in *.
      assert (APLB : forall B kk, In (B, kk) LB -> Sn + SIGNER_SIZE <= B \/ B + kk <= Sn).
      { intros B kk Hb. unfold SIGNER_SIZE. apply APn. apply in_or_app. right. exact Hb. }
      assert (APLc : forall B kk, In (B, kk) Lc -> Sn + 200 <= B \/ B + kk <= Sn).
      { intros B kk Hb. apply APn. apply in_or_app. left. exact Hb. }
      pose proof (blocks_below_of_HEAP usegs L HI _ _ _ _ HH1) as BB1.
      (* [comment removed for export] *)
      assert (HPXA2 : heap_presx usegs L LB (bv_unsigned sp) X0 m m2).
      { eapply heap_presx_trans; [exact HPX1|]. eapply (HPXcall ((Sn, 200) :: Lc) m1 m2 Sn); [exact HPX2| lia| exact APLB| exact BR0]. }
      assert (XD : forall A0 kk, (A0 + kk <= PP \/ PP + 8 <= A0) -> (A0 + kk <= Sn \/ Sn + 200 <= A0) -> disjoint_from [(PP, PP + 8); (Sn, Sn + SIGNER_SIZE)] A0 kk)
        by (intros A0 kk Y1 Y2; cbn; unfold SIGNER_SIZE; lia).
      pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX2 CS1 ltac:(apply client_range_stack; lia) ltac:(apply XD; cbn [cells_size csize Nat.add signer_cells length]; unfold SIGNER_SIZE in *; lia)) as CS2.
      pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX2 FR1 ltac:(apply client_range_stack; lia) ltac:(apply XD; cbn; lia)) as FR2.
      pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX2 DAc1 ltac:(apply client_range_stack; lia) ltac:(apply XD; cbn; lia)) as DAc2.
      pose proof (heap_presx_bytes_at usegs L _ _ _ _ _ _ _ HPX2 BY1 ltac:(eapply client_range_block; [right; apply in_or_app; right; exact BIN| lia| lia]) ltac:(apply XD; [lia| destruct (APLB _ _ BIN); unfold SIGNER_SIZE in *; lia])) as BY2.
      pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX2 PC1 ltac:(eapply client_range_block; [right; apply in_or_app; left; exact PIN| lia| cbn; unfold SIGNER_SIZE; lia])
                    ltac:(apply XD; cbn [cells_size csize Nat.add signer_cells length]; [lia| destruct (APLc prev SIGNER_SIZE PIN); unfold SIGNER_SIZE in *; lia])) as PC2.
      assert (NDX : forall a' ns', name_chain usegs (fun _ => True) m1 (Lc ++ LB) a' ns' -> name_chain usegs (fun _ => True) m2 L1 a' ns').
      { intros a' ns' HCx. eapply chain_presx; [exact HCx| intros x Hx; right; eapply chain_nodes_in; [exact HCx| exact Hx] | exact HPX2| unfold NAME_SIZE; lia|].
        intros x Hx. pose proof (chain_nodes_in usegs _ _ _ _ _ _ _ HCx x Hx) as HINx. destruct (BB1 _ (or_intror HINx)) as [_ Bx]. cbn [fst snd] in Bx.
        apply XD; [unfold NAME_SIZE in *; lia| destruct (APn _ _ HINx); unfold NAME_SIZE in *; lia]. }
      pose proof (NDX _ _ HN01) as HN02. pose proof (NDX _ _ PN1) as PN2.
      assert (HSP2 : splink usegs m2 L1 S1 mid prev).
      { eapply splink_presx; [eapply splink_mem; [exact HSP1| intros x _ Hb; right; exact Hb| intros x cs _ _ HR _; exact HR| intros i ns _ HN; eapply chain_mem; [exact HN| intros x Hx; right; eapply chain_nodes_in; [exact HN| exact Hx] | intros x cs _ HR _; exact HR]] | exact HPX2| |].
        - intros x Hx Hl. destruct (BB1 _ Hx) as [_ Bx]. cbn [fst snd] in Bx.
          destruct Hx as [Ex|Hx]; [assert (x = Sn) by congruence; subst x; exfalso| apply XD; [unfold SIGNER_SIZE in *; lia| destruct (APn _ _ Hx); unfold SIGNER_SIZE in *; lia]].
          pose proof (splink_nodes_in _ _ _ _ _ _ HSP1 _ Hl) as HSn. destruct (APn _ _ HSn); unfold SIGNER_SIZE in *; lia.
        - intros i ns x _ HN Hx. pose proof (chain_nodes_in usegs _ _ _ _ _ _ _ HN x Hx) as HINx. destruct (BB1 _ HINx) as [_ Bx]. cbn [fst snd] in Bx.
          destruct HINx as [Ex|HINx]; [exfalso; assert (NAME_SIZE = 200) by congruence; unfold NAME_SIZE in *; lia|]. apply XD; [unfold NAME_SIZE in *; lia| destruct (APn _ _ HINx); unfold NAME_SIZE in *; lia]. }
      pose proof (splink_nodes_in _ _ _ _ _ _ HSP1) as MIDIN.
      assert (L1tail : forall y kk, In (y, kk) L1 -> (kk = 200 -> In (y, 200) (Lc ++ LB)) -> In (y, kk) (Lc ++ LB)).
      { intros y kk [E|Hy] Hkk; [| exact Hy]. assert (kk = 200) as -> by congruence. assert (y = Sn) as -> by congruence.
        exfalso. destruct (APn _ _ (Hkk eq_refl)); lia. }
      clear HH1 HPX1 FR1 PPc1 CS1 DAc1 BY1 PC1 SO1 ST1 MI1 HN01 PN1 HSP1 MK NDX. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
      zstep. if_cases KR; zify_cond KR.
      { (* [comment removed for export] *)
        kz KR. specialize (HRn KR). subst nodes2. cbn [rev SNAME map app] in HH2, HNn2.
        zstep. zstep. zstep.                   (* [comment removed for export] *)
        replace (Z_to_bv 64 260760 : word) with (Z_to_bv 64 (hl_free L) : word) by (rewrite HFREE; reflexivity).
        eapply aevtM_cut.
        { eapply (heap_free usegs L HI) with (A := Sn) (n := 200) (lo := lo) (h := h2) (LB := L1);
            [ exact HH2 | left; reflexivity | rewrite USP; exact ST2 | exact CEIL | rewrite USP; lia | exact MI2 | exact TP
            | rewrite USP, HT2, HT1, HTc; lia | reflexivity ]. }
        intros ms' mo'x PO. unfold call_post in PO.
        ddestruct PO as (z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m3 & mo3
                        & E0 & MI3 & ST3 & MF3 & HP3 & h3 & HT3 & HH3).
        injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite USP in ST3, HP3. fix_ret 0x1e148.
        replace (lb_remove Sn L1) with (Lc ++ LB) in HH3, HP3 by (unfold L1; cbn; rewrite Z.eqb_refl; reflexivity).
        pose proof (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP3 FR2 ltac:(apply client_range_stack; lia)) as FR3.
        pose proof (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP3 PPc2 ltac:(apply client_range_stack; lia)) as PPc3.
        pose proof (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP3 CS2 ltac:(apply client_range_stack; lia)) as CS3.
        pose proof (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP3 DAc2 ltac:(apply client_range_stack; lia)) as DAc3.
        pose proof (heap_pres_bytes_at usegs L _ _ _ _ _ _ HP3 BY2 ltac:(eapply client_range_block; [apply SUB; exact BIN| lia| lia])) as BY3.
        pose proof (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP3 PC2 ltac:(eapply client_range_block; [apply in_or_app; left; exact PIN| lia| cbn; unfold SIGNER_SIZE; lia])) as PC3.
        pose proof (statics_ok_heap_pres' usegs L _ _ _ _ SO2 HP3 SW) as SO3.
        assert (HPXA3 : heap_presx usegs L LB (bv_unsigned sp) X0 m m3).
        { eapply heap_presx_trans_pres; [exact HPXA2| eapply heap_pres_sp_mono; [eapply heap_pres_sub; [exact HP3| exact SUB] | lia] | intros b Hb; exact Hb]. }
        assert (NDX : forall a' ns', name_chain usegs (fun _ => True) m2 L1 a' ns' -> name_chain usegs (fun _ => True) m3 (Lc ++ LB) a' ns').
        { intros a' ns' HCx. eapply chain_pres; [exact HCx| | exact HP3| unfold NAME_SIZE; lia].
          intros x Hx. apply L1tail; [eapply chain_nodes_in; [exact HCx| exact Hx] | unfold NAME_SIZE; lia]. }
        eapply (CLEAN lw p2 inext0 S1 sjh names0 (mid ++ [(prev, pnames)]) m3 mo3 h3 r2); [| | | lia].
        - rewrite <- ELc. split; [exact HH3|]. split; [congruence|]. split; [eapply mo_frame_trans; [| exact MF3]; eapply mo_frame_trans; [| exact MF2]; eapply mo_frame_trans; eassumption|]. split; [exact HPXA3|].
          split; [eexists; exact FR3|]. split; [exact PPc3|]. split; [lia|]. split; [exact CS3|]. split; [exact CSZ|].
          split; [exact DAc3|]. split; [exact BY3|]. split; [exact MI3|]. split; [exact SO3| exact ST3].
        - rewrite <- ELc. apply NDX. exact HN02.
        - rewrite <- ELc. eapply CLOSE. split; [apply NDX; exact HN02|]. split.
          { eapply splink_mem; [exact HSP2| intros x Hl Hx; apply L1tail; [exact Hx| intros _; apply MIDIN; exact Hl] | |].
            - intros x cs Hx Hl HR Hsz. eapply heap_pres_rw_cells; [exact HP3| exact HR| eapply client_range_block; [apply MIDIN; exact Hl| lia| ]]. rewrite Hsz. unfold SIGNER_SIZE. lia.
            - intros i ns _ HN. apply NDX. exact HN. }
          split; [exact PC3|]. split; [apply NDX; exact PN2|].
          split; [exact PAL|]. split; [exact PPOS|]. split; [exact PIN|]. split; [exact PVB|]. split; [exact PNM| exact ELc]. }
      (* [comment removed for export] *)
      kz KR. subst r2. specialize (Hprog eq_refl).
      set (Lc2 := SNAME (rev nodes2) ++ (Sn, 200) :: Lc).
      assert (EL2 : SNAME (rev nodes2) ++ L1 = Lc2 ++ LB) by (unfold L1, Lc2; rewrite <- app_assoc; reflexivity).
      rewrite EL2 in HH2, HNn2.
      pose proof (HND _ _ _ _ HH2) as ND2.
      zstep. zstep; if_cases KAL; zify_cond KAL; [al8_close KAL|]. zstep.  (* [comment removed for export] *)
      pose proof B6 as B6'.
      match goal with |- context [bv_swrap 32 ?e] => replace (bv_swrap 32 e) with (cnt + 1) end.
      2:{ symmetry. first [rewrite Z.mod_small by lia | change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia | idtac].
          unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 `div` 2) with 2147483648.
          rewrite Z.mod_small by lia. lia. }
      pose proof (conj HH2 (conj FR2 (conj PPc2 (conj CS2 (conj DAc2 (conj BY2 (conj CSn2 I))))))) as CBOX. clear HH2 FR2 PPc2 CS2 DAc2 BY2 CSn2.
      pose proof (munch_refl [(prev + 192, prev + 200)] m2) as MU3. pose proof (wmono_refl usegs m2) as WM3.
      unfold signer_cells in PC2. cbn [sj0 sj_merged sj1 sj2] in PC2.
      zstep.                                   (* [comment removed for export] *)
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      change (rw_cells usegs m3 prev (signer_cells pinext Sn psj)) in PC2. rename PC2 into PC3.
      ddestruct CBOX as (HH2 & FR2 & PPc2 & CS2 & DAc2 & BY2 & CSn2 & _).
      assert (PIN2 : In (prev, 200) Lc2) by (unfold Lc2; apply in_or_app; right; right; exact PIN).
      assert (WF3 : wfp Lc2 [(prev + 192, prev + 200)]).
      { intros a Hna. cbn [outside] in Hna. right; right; right. exists (prev, 200). split; [exact PIN2| cbn; lia]. }
      pose proof (HEAPm _ _ _ _ _ _ HH2 ltac:(rewrite HT2, HT1; exact HTc) MU3 WM3 WF3) as HH3.
      pose proof (HPXm _ _ _ _ _ _ HH2 MU3 WM3 WF3) as HPX23.
      lazymatch type of SO2 with statics_ok _ _ m3 => rename SO2 into SO3 | _ => pose proof (SOm _ _ _ _ _ _ HH2 SO2 MU3 WF3) as SO3; clear SO2 end.
      pose proof (rw_cells_transport usegs _ m2 m3 _ _ FR2 MU3 WM3 ltac:(cbn; lia)) as FR3.
      pose proof (rw_cells_transport usegs _ m2 m3 _ _ PPc2 MU3 WM3 ltac:(cbn; lia)) as PPc3.
      pose proof (rw_cells_transport usegs _ m2 m3 _ _ CS2 MU3 WM3 ltac:(cbn [cells_size csize Nat.add signer_cells length disjoint_from]; lia)) as CS3.
      pose proof (rw_cells_transport usegs _ m2 m3 _ _ DAc2 MU3 WM3 ltac:(cbn; lia)) as DAc3.
      pose proof (bytes_at_transport usegs _ m2 m3 _ _ BY2 MU3 ltac:(cbn; unfold SIGNER_SIZE in *; lia)) as BY3.
      pose proof (rw_cells_transport usegs _ m2 m3 _ _ CSn2 MU3 WM3 ltac:(cbn [cells_size csize Nat.add signer_cells length disjoint_from]; destruct (APLc _ _ PIN); lia)) as CSn3.
      (* [comment removed for export] *)
      destruct (heap_blocks usegs L HI _ _ _ _ HH2) as [BR2 _].
      assert (HPXb : heap_presx usegs L (Lc2 ++ LB) (bv_unsigned sp) [(prev + 192, prev + 200)] m2 m3).
      { eapply heap_presx_of_frame_munch; [exact MU3| exact WM3| exact BR2| exact DHI|]. intros a. cbn [outside]. lia. }
      assert (NDJ : forall x, In (x, NAME_SIZE) (Lc2 ++ LB) -> disjoint_from [(prev + 192, prev + 200)] x NAME_SIZE).
      { intros x Hx. destruct (blk_disj _ _ _ _ (x, NAME_SIZE) (prev, 200) HH2 Hx (in_or_app _ _ _ (or_introl PIN2)) ltac:(unfold NAME_SIZE; congruence) ltac:(cbn; unfold NAME_SIZE; lia) ltac:(cbn; lia)) as [X|X];
          cbn in X |- *; unfold NAME_SIZE in *; lia. }
      assert (CHb : forall a' ns', name_chain usegs (fun _ => True) m2 (Lc2 ++ LB) a' ns' -> name_chain usegs (fun _ => True) m3 (Lc2 ++ LB) a' ns').
      { intros a' ns' HCx. eapply chain_presx; [exact HCx| intros x Hx; eapply chain_nodes_in; [exact HCx| exact Hx] | exact HPXb| unfold NAME_SIZE; lia|].
        intros x Hx. apply NDJ. eapply chain_nodes_in; [exact HCx| exact Hx]. }
      assert (SUB2 : forall b, In b L1 -> In b (Lc2 ++ LB)) by (intros b Hb; rewrite <- EL2; apply in_or_app; right; exact Hb).
      assert (HN03 : name_chain usegs (fun _ => True) m3 (Lc2 ++ LB) inext0 names0).
      { apply CHb. eapply chain_mem; [exact HN02| intros x Hx; apply SUB2; eapply chain_nodes_in; [exact HN02| exact Hx] | intros x cs _ HR _; exact HR]. }
      assert (PN3 : name_chain usegs (fun _ => True) m3 (Lc2 ++ LB) pinext pnames).
      { apply CHb. eapply chain_mem; [exact PN2| intros x Hx; apply SUB2; eapply chain_nodes_in; [exact PN2| exact Hx] | intros x cs _ HR _; exact HR]. }
      pose proof (CHb _ _ HNn2) as HNn3.
      assert (HSP3 : splink usegs m3 (Lc2 ++ LB) S1 mid prev).
      { eapply splink_presx; [eapply splink_mem; [exact HSP2| intros x _ Hx; apply SUB2; exact Hx| intros x cs _ _ HR _; exact HR
                                | intros i ns _ HN; eapply chain_mem; [exact HN| intros x Hx; apply SUB2; eapply chain_nodes_in; [exact HN| exact Hx] | intros x cs _ HR _; exact HR]]
          | exact HPXb| |].
        - intros x Hx Hl. pose proof (MIDIN _ Hl) as HxL.
          destruct (blk_disj _ _ _ _ (x, SIGNER_SIZE) (prev, 200) HH2 Hx (in_or_app _ _ _ (or_introl PIN2))) as [X|X]; try (cbn; unfold SIGNER_SIZE; is_arith_goal; lia).
          + intros E. assert (x = prev) as -> by congruence. exact (PNM Hl).
          + cbn in X |- *. unfold SIGNER_SIZE in *. lia.
          + cbn in X |- *. unfold SIGNER_SIZE in *. lia.
        - intros i ns x _ HN Hx. apply NDJ. eapply chain_nodes_in; [exact HN| exact Hx]. }
      clear HH2 FR2 PPc2 CS2 DAc2 BY2 CSn2 HN02 PN2 HNn2 HSP2 MU3 WM3 MK HPX2. pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK.
      assert (HPXA3 : heap_presx usegs L LB (bv_unsigned sp) X0 m m3).
      { eapply heap_presx_trans; [exact HPXA2| exact HPX23]. }
      (* [comment removed for export] *)
      assert (ELc2 : Lc2 = sbl ((mid ++ [(prev, pnames)]) ++ [(Sn, nodes2)]) ++ SNAME (rev names0)).
      { unfold Lc2. rewrite ELc. rewrite (sbl_app (mid ++ [(prev, pnames)]) [(Sn, nodes2)]). cbn [sbl]. repeat rewrite <- app_assoc. reflexivity. }
      assert (OP3 : OPEN m3 Lc2 inext0 names0 S1 (mid ++ [(prev, pnames)]) Sn inext2 nodes2 sjn).
      { split; [exact HN03|]. split.
        { eapply splink_snoc; [exact HSP3| apply in_or_app; left; exact PIN2| exact PAL| exact PPOS| exact PC3| exact PN3]. }
        split; [exact CSn3|]. split; [exact HNn3|]. split; [exact SnAL|]. split; [exact SnP|].
        split; [unfold Lc2; apply in_or_app; right; left; reflexivity|].
        split; [destruct (APLB _ _ BIN); unfold SIGNER_SIZE in *; lia|].
        split; [| exact ELc2].
        rewrite map_app. cbn [map fst]. intros Hin. apply in_app_or in Hin. destruct Hin as [Hin|[Hin|[]]].
        - destruct (APn _ _ (MIDIN _ Hin)); lia.
        - subst prev. destruct (APLc _ _ PIN); lia. }
      zstep; if_cases KW; zify_cond KW; [exfalso; rewrite ?signed_lit64 in KW by lia; lia|]. zstep.  (* [comment removed for export] *)
      zstep. zstep.                            (* [comment removed for export] *)
      zstep. if_cases KE; zify_cond KE; rewrite ?unsigned_lit in KE by lia.
      - (* [comment removed for export] *)
        eapply (IH ES p2 (cnt + 1) lw inext0 names0 sjh S1 (mid ++ [(prev, pnames)]) Sn inext2 nodes2 sjn Lc2 m3 mo2 h2); [lia| lia| lia| exact HES| lia| lia| | exact OP3].
        split; [exact HH3|]. split; [rewrite HT2, HT1; exact HTc|]. split; [eapply mo_frame_trans; [| exact MF2]; eapply mo_frame_trans; eassumption|]. split; [exact HPXA3|].
        split; [eexists; exact FR3|]. split; [exact PPc3|]. split; [lia|]. split; [exact CS3|]. split; [exact CSZ|].
        split; [exact DAc3|]. split; [exact BY3|]. split; [assumption|]. split; [exact SO3| exact ST2].
      - (* [comment removed for export] *)
        zstep.                                 (* [comment removed for export] *)
        eapply (L_RET lw p2 _ Lc2 m3 mo2 h2 (cnt + 1) inext0 S1 sjh names0 ((mid ++ [(prev, pnames)]) ++ [(Sn, nodes2)])).
        + split; [exact HH3|]. split; [rewrite HT2, HT1; exact HTc|]. split; [eapply mo_frame_trans; [| exact MF2]; eapply mo_frame_trans; eassumption|]. split; [exact HPXA3|].
          split; [eexists; exact FR3|]. split; [exact PPc3|]. split; [lia|]. split; [exact CS3|]. split; [exact CSZ|].
          split; [exact DAc3|]. split; [exact BY3|]. split; [assumption|]. split; [exact SO3| exact ST2].
        + exact CS3.
        + exact HN03.
        + eapply CLOSE. exact OP3.
        + rewrite ELc2. apply PERMc.
        + lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "01T0@D11805467289.206D13112141392.208D21157640433.208D21172136973.206D67183863355.206D67186111175.208L10823794898.215L10823794899.167L10823794901.234L1107921941.216 L11799358116.214L12490298163.166L12490298165.233L12490346674.214L12660708096.215L12660708097.167L12660708103.234L13350887686.204L13758561961.239L1386317440.204 L18727432851.220L18938186279.165L20323745488.231L20323745494.164L20763674639.220L23472204939.214L26014308813.215L26071143599.136L26295853971.216L30993653749.215L31094837846.220L3119769277.212 L32483077380.212L32495795635.165L32495795637.232L35485062061.170L35487159211.237L35499744614.219L35499744614.225L35818434833.160L35992031860.215L36253174270.170L39360456046.163L39360717918.213L39360801497.230L39371603223.162L39416392300.208L39475339063.230L41202929119.205L41296042896.15 L42152566795.21 L46147228046.138L46881206694.238L46885407252.220L46961339658.222L48182046655.214L4909481499.216 L49994189825.228L508271316.213  L51585051053.224L52087469201.223L53646437001.212L55469950663.206L55472014661.138L56724938549.218L56782487073.238L59308630630.1  L59308630630.169L59314873579.221L60382958079.206L60385219197.138L6139713783.209 L63090567536.213L65836106226.218L6670147970.18  L67011298682.217L6753375774.138 L67572053276.220L6933890443.169 L6933890445.236 L6934137867.210 L7296048127.220 L7419122673.216 L7824031968.138 L9538458573.220 R12490559893.170R13587414117.170R18247033200.170R19572124799.170R20323958768.170R25585061457.170R34841085112.170R41293539632.170R43745324333.170R43871310534.170R53850979607.170R56729473832.170R57504388252.170R63261865041.170R64163405490.17000000T02602f03J03n04^05C05e06J08O09409V0:;0:`0;E0;g0<L0=40=]0=^0>?0?O0@40@V0B?0CS0DN0EV0F:0GR0HJ0Ia0JF0Jh0KM0Kk0LL0Lm0MN0Ml0NP0O=0O[0P<0P]0Q;0Q\0R=0R^0R_0R`0S>0U10Vm0WR0X60X]0Z40[H0[m0]A0]e0^R0_<0_c0`K0`O0a70aZ0bH0c30ch0dM0ed0ee0g@0g^0iG0ie0jF0jg0lE0n@0n^0o?0od11J12^14L15116O18=18>18?18i1:J1:K1;_1=?1>_S2sp2PP3SIG4DALG2bs6inext03sjh2Sn2HBS1L3HLS3DHI2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR6inext03sjh7SLO304'3ACP2Sn3SnP2HB5Ha_st5Hl_stS2sp2PP3SIG4DALG2bs6inext03sjh2Sn2HB5Ha_st5Hl_stS2sp2PP3SIG4DALG2bs6inext03sjh2Sn2HBS2sp2PP3SIG4DALG2bs6inext03sjh2Sn2HBS2sp2PP3SIG4DALG2bs6inext03sjh2Sn2HB5Ha_st5Hl_stS2sp2PP3BUF3SIG4DALG2bs6inext03sjh2SnS2sp2PP3BUF3SIG4DALG2bs6inext03sjhS2sp2PP3BUF3SIG4DALG2bs6inext03sjh2SnS1L3HLS2sp2PP1P3END3BUF3SIG4DALG2lo2bs2B12B32B42B53PP13SG13DA14CEIL3SPR2ES1p6inext03sjh3Hp13HES7SLO304'3ACP4BCE'2Sn3SnP2p24Hp2'5HprogS2sp2PP3SIG4DALG2bs3SG16inext03sjh2SnS2sp2PP3SIG4DALG2bs3DA16inext03sjhS2sp2PP3SIG4DALG2bs3DA16inext03sjh2SnS2sp2PP3SIG4DALG2bs3DA16inext03sjh2SnS2sp2PP3BUF3SIG4DALG2bs6inext03sjh2SnS2sp2PP3BUF3SIG4DALG2bs6inext03sjhS2sp2PP3BUF3SIG4DALG2bs6inext03sjh2SnS2sp2PP3SIG4DALG2bs6inext03sjh2Sn2r23Hr2S2sp2LB2PP3SIG4DALG2bs6inext03sjh2Lc2Sn1xFS2sp2PP3SIG4DALG2bs6inext03sjh2SnS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR6inext03sjh7SLO304'2Sn3SnP4SnCES2sp2PP3SIG4DALG2bs3PP16inext03sjh2SnS2sp2PP3SIG4DALG2bs3PP16inext03sjhS1L3HLS2sp2PP1P3SIG4DALG2lo2bs3PP13SG13DA12D12D22D34CEIL3SPR1p6inext03sjh3Hp17SLO304'3ACP2Sn3SnP2p25HprogS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR6inext03sjh7SLO304'3ACP2Sn3SnP4SnCES2sp2PP3SIG4DALG2bs6inext03sjh2Sn3SnP2KC2r23Hr22A02kk2Y12Y2S1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR6inext03sjh7SLO304'3ACPS2sp2PP3SIG4DALG2bs2D36inext03sjh2SnS1L3HLS2sp2PP3BUF3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR6inext03sjh7SLO304'3ACP4BCE'2Sn3SnPS2sp2PP3SIG4DALG2bs2ES1p6inext03sjh2Sn3SnP2KC2p24Hp2'2KES1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA12D24CEIL3SPR6inext03sjh7SLO304'3ACP2Sn3SnP4SnCES2sp2PP3SIG4DALG2bs3SG16inext03sjh2SnS2sp2PP3SIG4DALG2bs3SG16inext03sjhS2sp2PP3SIG4DALG2bs3SG16inext03sjh2SnS2sp2PP3SIG4DALG2bs6inext03sjhS2sp2PP3SIG4DALG2bs6inext03sjh2SnS2sp2PP3SIG4DALG2bs6inext03sjh2SnS2sp2PP3SIG4DALG2bs6inext03sjh2SnS2sp2PP3SIG4DALG2bs6inext03sjhS2sp2PP3SIG4DALG2bs2D16inext03sjh2SnS1L2sp2PP3SIG4DALG2lo2bs6SLO3046inext03sjh2SnS2sp2PP3SIG4DALG2bs6inext03sjhS2sp2PP3SIG4DALG2bs6inext03sjh2SnS2sp2PP3SIG4DALG2bs6inext03sjh2SnS2sp2PP3SIG4DALG2bs6inext03sjhS2sp2PP3SIG4DALG2bs6inext03sjh2SnS2sp2PP3SIG4DALG2bs6inext03sjh2SnS2sp2PP3SIG4DALG2bs6inext03sjh2SnFFS2sp2PP3SIG4DALG2bs6inext03sjhS1L3HLS2sp2PP1P3END3SIG4DALG2lo2bs3PP13SG13DA12D12D22D34CEIL3SPR2ES1p6inext03sjh3Hp13HES7SLO304'3ACP2Sn3SnP2p24Hp2'S1L3HLS2sp2PP1P3END3SIG4DALG2lo2bs3PP13SG13DA12D12D22D34CEIL3SPR2ES1p6inext03sjh3Hp13HES7SLO304'3ACP2Sn3SnP2p24Hp2'5Hprog2KES1L2sp2PP3SIG4DALG2bs6inext03sjh2Sn1aS2sp2PP3SIG4DALG2bs2D26inext03sjh2SnS2sp2PP3BUF3SIG4DALG2bs6inext03sjh2Sn1HS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA12D24CEIL3SPR6inext03sjh7SLO304'3ACP2Sn3SnP1x2BxS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR6inext03sjh7SLO304'3ACP2Sn3SnP4SnCES2sp2PP3SIG4DALG2bs6inext03sjh2Sn1x1HS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR6inext03sjh7SLO304'3ACP2Sn3SnP1x2BxS2sp2PP3SIG4DALG2bs2D16inext03sjh2SnS1L2sp2PP3SIG4DALG2lo2bs6SLO3046inext03sjh2SnS1L2sp2PP3SIG4DALG2lo2bs6SLO3046inext03sjhS2sp2PP3BUF3SIG4DALG2bs6inext03sjh2Sn1HS2sp2PP3SIG4DALG2bs6inext03sjh2Sn2r23Hr2S2KCS2sp2PP3SIG4DALG2bs6inext03sjh2Sn3SnP2KCS2sp2PP3SIG4DALG2bs6inext03sjh2Sn1HS1L2HI2sp1h2PP3SIG4DALG2bs5SPTOP6inext03sjh2SnS1L2HI2sp1h2PP3SIG4DALG2bs5SPTOP6inext03sjhS2sp2PP3SIG4DALG2lo2bs6inext03sjh2Sn3SnP2KC3Lc21a3HnaS2sp2PP3SIG4DALG2bs3PP16inext03sjh2SnS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA12D24CEIL3SPR6inext03sjh7SLO304'3ACP2Sn3SnP4SnCEFS1L3HLS2sp2PP3BUF3SIG4DALG2lo2bs3PP13SG13DA12D24CEIL3SPR6inext03sjh7SLO304'3ACP4BCE'2Sn3SnPS2sp2PP3SIG4DALG2bs6inext03sjhS1L3HLS2sp2PP1P3SIG4DALG2lo2bs3PP13SG13DA12D12D22D34CEIL3SPR1p6inext03sjh3Hp17SLO304'3ACP2Sn3SnP2p25HprogS2sp2PP3SIG4DALG2bs6inext03sjhS2sp2PP3SIG4DALG2bs6inext03sjh2SnS2sp2PP3SIG4DALG2bs6inext03sjh2SnS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA12D12D22D34CEIL3SPR2ES6inext03sjh7SLO304'3ACP2Sn3SnP2p2S1L3HLS2sp2PP1P3END3BUF3SIG4DALG2lo2bs2B12B32B42B53PP13SG13DA14CEIL3SPR2ES1p6inext03sjh3Hp13Hp23HES7SLO304'3ACP4BCE'2Sn3SnPS2sp2PP3SIG4DALG2bs6inext03sjhS2sp2PP3SIG4DALG2bs6inext03sjh2SnS2sp2PP3SIG4DALG2bs3DA16inext03sjh2SnS1L2HI3HLS2sp1h2PP3SIG4DALG2lo2bs3PP13SG13SG23DA14CEIL3SPR6inext03sjh2hc3HTc7SLO304'3ACP2h13HT12Sn3SnPS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR6inext03sjh7SLO304'3ACP2Sn3SnP4SnCES1L2HI3HLS2sp1h2PP3SIG4DALG2lo2bs3PP13PP23SG13SG23DA13DA24CEIL3SPR6inext03sjh2hc3HTc7SLO304'3ACP2h13HT12Sn3SnPS2sp2PP3SIG4DALG2bs3PP16inext03sjh2SnS1L3HLS2sp2PP1P3BUF3SIG4DALG2lo2bs2B13PP13SG13DA14CEIL3SPR1p6inext03sjh3Hp17SLO304'3ACP2Sn3SnPS1L2HI3HLS2sp1h2PP3SIG4DALG2lo2bs3PP13PP23SG13SG23DA13DA24CEIL3SPR6inext03sjh2hc3HTc7SLO304'3ACP2h13HT12Sn3SnPFFS2sp2PP3SIG4DALG2bs2ES1p6inext03sjh3Hp22SnS1L3HLS2sp2PP3END3BUF3SIG4DALG2lo2bs2B33PP13SG13DA14CEIL3SPR2ES6inext03sjh3HES7SLO304'3ACP2Sn3SnPFS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR6inext03sjh7SLO304'3ACP2Sn3SnP4SnCES1L3HLS2sp2PP3SIG4DALG2lo2bs3ALP3ALS3ALD3PP13SG13DA14CEIL4SP163SPR6inext03sjh7SLO304'3ACP2Sn3SnPS1L3HLS2sp2PP3SIG4DALG2lo2bs3ALP3ALS3ALD3PP13SG13DA14CEIL3SPR6inext03sjh7SLO304'3ACP2Sn3SnP4SnAL". (* [comment removed for export] *)
    #[using="HFREE HCALLOC HMSF HLS SW DIMG DHI HND GETALG SIGNER HH ALP BIN B1 B3 B4 B5 B6 ALS ALD Q1 Q2 Q3 PP1 PP2 SG1 SG2 DA1 DA2 D1 D2 D3 CEIL SLO SP16 SPTOP TP SPR LOSP SLO320 BCE"] Lemma LOOP0 : forall (ES p : Z) lw inext0 names0 sjh mc moc hc
        (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 : word),
      P < p -> p < ES -> ES <= END ->
      gv lw p (signer_cells inext0 0 sjh) (SNAME (rev names0)) mc moc hc ->
      name_chain usegs (fun _ => True) mc (SNAME (rev names0) ++ LB) inext0 names0 ->
      aevtM usegs moc POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 (Z_to_bv 64 SIG) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 DALG) (Z_to_bv 64 PP) (Z_to_bv 64 ES) x21
                  (Z_to_bv 64 (-22400)) (Z_to_bv 64 1) (Z_to_bv 64 SIG) s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x1e0d0) fc None mc (seg_rom usegs)).
    Proof.
      intros ES p lw inext0 names0 sjh mc moc hc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31 Hp1 Hp2 HES D HN0.
      pose proof D as D0. gv_open D.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof LOSP as LOSP'. pose proof SLO320 as SLO320'. pose proof alloc_ceiling_pos as ACP. pose proof BCE as BCE'.
      pose proof (unsigned_lit (bv_unsigned sp + -96) ltac:(lia)) as USP.
      set (Lc := SNAME (rev names0)) in *.
      (* [comment removed for export] *)
      zstep. zstep. zstep.                     (* [comment removed for export] *)
      replace (Z_to_bv 64 260448 : word) with (Z_to_bv 64 (hl_calloc L) : word) by (rewrite HCALLOC; reflexivity).
      eapply aevtM_cut.
      { eapply (heap_calloc usegs L HI) with (cnt := 1) (sz := 200) (lo := lo) (h := hc) (LB := Lc ++ LB);
          [ exact HHc | rewrite USP; exact STc | exact CEIL | rewrite USP; lia | exact MIc | exact TP | rewrite USP, HTc; lia
          | reflexivity | reflexivity | lia | lia | lia ]. }
      intros ms' mo'x PO. unfold call_post in PO.
      ddestruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m1 & mo1
                      & E0 & MI1 & ST1 & MF1 & HP1 & h1 & HT1 & HRES).
      injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite USP in ST1, HP1. fix_ret 0x1e0dc.
      assert (SUB : forall b, In b LB -> In b (Lc ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
      pose proof (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP1 FR ltac:(apply client_range_stack; lia)) as FR1.
      pose proof (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP1 PPc ltac:(apply client_range_stack; lia)) as PPc1.
      pose proof (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP1 CS ltac:(apply client_range_stack; lia)) as CS1.
      pose proof (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP1 DAc ltac:(apply client_range_stack; lia)) as DAc1.
      pose proof (heap_pres_bytes_at usegs L _ _ _ _ _ _ HP1 BYc ltac:(eapply client_range_block; [apply SUB; exact BIN| lia| lia])) as BY1.
      pose proof (statics_ok_heap_pres' usegs L _ _ _ _ SOc HP1 SW) as SO1.
      assert (HPX1 : heap_presx usegs L LB (bv_unsigned sp) X0 m m1).
      { eapply heap_presx_trans_pres; [exact HPXc| eapply heap_pres_sp_mono; [eapply heap_pres_sub; [exact HP1| exact SUB] | lia] | intros b Hb; exact Hb]. }
      pose proof (chain_pres usegs L _ _ _ _ _ _ _ _ _ _ HN0 ltac:(intros x Hx; eapply chain_nodes_in; [exact HN0| exact Hx]) HP1 ltac:(unfold NAME_SIZE; lia)) as HN01.
      clear HPXc FR PPc CS DAc BYc SOc STc MIc MK HN0 D0.
      destruct HRES as [[-> HH1] | (Sn & -> & BR & HH1 & RAWZ)].
      { (* [comment removed for export] *)
        pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
        zstep. if_cases KC; zify_cond KC; [| exfalso; clear - KC; cbv in KC; lia].
        zstep. zstep.                          (* [comment removed for export] *)
        eapply (CLEAN lw p inext0 0 sjh names0 [] m1 mo1 h1 (-22400)); [| cbn [sbl app]; exact HN01| cbn; reflexivity| lia].
        cbn [sbl app]. split; [exact HH1|]. split; [congruence|]. split; [eapply mo_frame_trans; eassumption|]. split; [exact HPX1|].
        split; [eexists; exact FR1|]. split; [exact PPc1|]. split; [exact Hpc|]. split; [exact CS1|]. split; [exact CSZ|].
        split; [exact DAc1|]. split; [exact BY1|]. split; [exact MI1|]. split; [exact SO1| exact ST1]. }
      (* [comment removed for export] *)
      pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
      pose proof BR as BR0. ddestruct BR as (SnP & SnAL & _ & SnCE & SnIMG). rewrite Z.mul_1_l in SnCE, SnIMG, HH1, RAWZ, BR0.
      destruct (heap_blocks usegs L HI _ _ _ _ HH1) as [BR1 AP1]. cbn [blocks_apart] in AP1. destruct AP1 as [APn _].
      change (Z.to_nat 200) with 200%nat in RAWZ.
      zstep. if_cases KC; zify_cond KC; [exfalso; rewrite ?unsigned_lit in KC by lia; lia|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
      pose proof SIGNER as SPS. unfold pkcs7_signer_stmt, U_PKCS7_SIGNER in SPS.
      eapply aevtM_cut.
      { eapply SPS with (PP := PP) (P := p) (END := ES) (BUF := BUF) (bs := bs) (S := Sn) (DALG := DALG) (lo := lo) (h := h1) (LB := (Sn, 200) :: Lc ++ LB)
                        (sj := SGJ (zeros 80) (Z_to_bv 8 0) (zeros 7) (zeros 96)) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
          try reflexivity; rewrite ?USP; try eassumption; try (is_arith_goal; unfold SIGNER_SIZE in *; plia);
          try (clear - SP16 SPR LOSP' CEIL ACP; Z.div_mod_to_equations; is_arith_goal; lia).
        - right. apply in_or_app. right. exact BIN.
        - eapply rw_cells_reshape; [exact RAWZ| cbn; repeat split; reflexivity| vm_compute; reflexivity].
        - right. left. reflexivity.
        - apply APn. apply in_or_app. right. exact BIN.
        - unfold PKCS7_SIGNER_STACK. lia. }
      intros ms' mo'x PO.
      ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & mo2 & h2 & r2 & p2 & inext2 & sjn & nodes2
                      & E0 & -> & Hr2 & MI2 & SO2 & ST2 & MF2 & HT2 & PPc2 & Hp2' & Hprog & CSn2 & HNn2 & HND2 & HAP2 & HH2 & HPX2 & HRn).
      injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite ?USP in ST2. rewrite ?USP in HPX2. fix_ret 0x1e0f8. clear SPS.
      set (L1 := (Sn, 200) :: Lc ++ LB) in *.
      assert (APLB : forall B kk, In (B, kk) LB -> Sn + SIGNER_SIZE <= B \/ B + kk <= Sn).
      { intros B kk Hb. unfold SIGNER_SIZE. apply APn. apply in_or_app. right. exact Hb. }
      pose proof (blocks_below_of_HEAP usegs L HI _ _ _ _ HH1) as BB1.
      assert (HPXA2 : heap_presx usegs L LB (bv_unsigned sp) X0 m m2).
      { eapply heap_presx_trans; [exact HPX1|]. eapply (HPXcall ((Sn, 200) :: Lc) m1 m2 Sn); [exact HPX2| lia| exact APLB| exact BR0]. }
      assert (XD : forall A0 kk, (A0 + kk <= PP \/ PP + 8 <= A0) -> (A0 + kk <= Sn \/ Sn + 200 <= A0) -> disjoint_from [(PP, PP + 8); (Sn, Sn + SIGNER_SIZE)] A0 kk)
        by (intros A0 kk Y1 Y2; cbn; unfold SIGNER_SIZE; lia).
      pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX2 CS1 ltac:(apply client_range_stack; lia) ltac:(apply XD; cbn [cells_size csize Nat.add signer_cells length]; unfold SIGNER_SIZE in *; lia)) as CS2.
      pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX2 FR1 ltac:(apply client_range_stack; lia) ltac:(apply XD; cbn; lia)) as FR2.
      pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX2 DAc1 ltac:(apply client_range_stack; lia) ltac:(apply XD; cbn; lia)) as DAc2.
      pose proof (heap_presx_bytes_at usegs L _ _ _ _ _ _ _ HPX2 BY1 ltac:(eapply client_range_block; [right; apply in_or_app; right; exact BIN| lia| lia]) ltac:(apply XD; [lia| destruct (APLB _ _ BIN); unfold SIGNER_SIZE in *; lia])) as BY2.
      assert (NDX : forall a' ns', name_chain usegs (fun _ => True) m1 (Lc ++ LB) a' ns' -> name_chain usegs (fun _ => True) m2 L1 a' ns').
      { intros a' ns' HCx. eapply chain_presx; [exact HCx| intros x Hx; right; eapply chain_nodes_in; [exact HCx| exact Hx] | exact HPX2| unfold NAME_SIZE; lia|].
        intros x Hx. pose proof (chain_nodes_in usegs _ _ _ _ _ _ _ HCx x Hx) as HINx. destruct (BB1 _ (or_intror HINx)) as [_ Bx]. cbn [fst snd] in Bx.
        apply XD; [unfold NAME_SIZE in *; lia| destruct (APn _ _ HINx); unfold NAME_SIZE in *; lia]. }
      pose proof (NDX _ _ HN01) as HN02.
      assert (L1tail : forall y kk, In (y, kk) L1 -> (kk = 200 -> In (y, 200) (Lc ++ LB)) -> In (y, kk) (Lc ++ LB)).
      { intros y kk [E|Hy] Hkk; [| exact Hy]. assert (kk = 200) as -> by congruence. assert (y = Sn) as -> by congruence.
        exfalso. destruct (APn _ _ (Hkk eq_refl)); lia. }
      clear HH1 HPX1 FR1 PPc1 CS1 DAc1 BY1 SO1 ST1 MI1 HN01 MK NDX. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
      zstep. if_cases KR; zify_cond KR.
      { (* [comment removed for export] *)
        kz KR. specialize (HRn KR). subst nodes2. cbn [rev SNAME map app] in HH2, HNn2.
        zstep. zstep. zstep.                   (* [comment removed for export] *)
        replace (Z_to_bv 64 260760 : word) with (Z_to_bv 64 (hl_free L) : word) by (rewrite HFREE; reflexivity).
        eapply aevtM_cut.
        { eapply (heap_free usegs L HI) with (A := Sn) (n := 200) (lo := lo) (h := h2) (LB := L1);
            [ exact HH2 | left; reflexivity | rewrite USP; exact ST2 | exact CEIL | rewrite USP; lia | exact MI2 | exact TP
            | rewrite USP, HT2, HT1, HTc; lia | reflexivity ]. }
        intros ms' mo'x PO. unfold call_post in PO.
        ddestruct PO as (z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m3 & mo3
                        & E0 & MI3 & ST3 & MF3 & HP3 & h3 & HT3 & HH3).
        injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite USP in ST3, HP3. fix_ret 0x1e148.
        replace (lb_remove Sn L1) with (Lc ++ LB) in HH3, HP3 by (unfold L1; cbn; rewrite Z.eqb_refl; reflexivity).
        pose proof (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP3 FR2 ltac:(apply client_range_stack; lia)) as FR3.
        pose proof (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP3 PPc2 ltac:(apply client_range_stack; lia)) as PPc3.
        pose proof (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP3 CS2 ltac:(apply client_range_stack; lia)) as CS3.
        pose proof (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP3 DAc2 ltac:(apply client_range_stack; lia)) as DAc3.
        pose proof (heap_pres_bytes_at usegs L _ _ _ _ _ _ HP3 BY2 ltac:(eapply client_range_block; [apply SUB; exact BIN| lia| lia])) as BY3.
        pose proof (statics_ok_heap_pres' usegs L _ _ _ _ SO2 HP3 SW) as SO3.
        assert (HPXA3 : heap_presx usegs L LB (bv_unsigned sp) X0 m m3).
        { eapply heap_presx_trans_pres; [exact HPXA2| eapply heap_pres_sp_mono; [eapply heap_pres_sub; [exact HP3| exact SUB] | lia] | intros b Hb; exact Hb]. }
        assert (HN03 : name_chain usegs (fun _ => True) m3 (Lc ++ LB) inext0 names0).
        { eapply chain_pres; [exact HN02| | exact HP3| unfold NAME_SIZE; lia].
          intros x Hx. apply L1tail; [eapply chain_nodes_in; [exact HN02| exact Hx] | unfold NAME_SIZE; lia]. }
        eapply (CLEAN lw p2 inext0 0 sjh names0 [] m3 mo3 h3 r2); [| cbn [sbl app]; exact HN03| cbn; reflexivity| lia].
        cbn [sbl app]. split; [exact HH3|]. split; [congruence|]. split; [eapply mo_frame_trans; [| exact MF3]; eapply mo_frame_trans; [| exact MF2]; eapply mo_frame_trans; eassumption|]. split; [exact HPXA3|].
        split; [eexists; exact FR3|]. split; [exact PPc3|]. split; [lia|]. split; [exact CS3|]. split; [exact CSZ|].
        split; [exact DAc3|]. split; [exact BY3|]. split; [exact MI3|]. split; [exact SO3| exact ST3]. }
      (* [comment removed for export] *)
      kz KR. subst r2. specialize (Hprog eq_refl).
      set (Lc2 := SNAME (rev nodes2) ++ (Sn, 200) :: Lc).
      assert (EL2 : SNAME (rev nodes2) ++ L1 = Lc2 ++ LB) by (unfold L1, Lc2; rewrite <- app_assoc; reflexivity).
      rewrite EL2 in HH2, HNn2.
      zstep. zstep; if_cases KAL; zify_cond KAL; [al8_close KAL|]. zstep.  (* [comment removed for export] *)
      pose proof (conj HH2 (conj FR2 (conj PPc2 (conj DAc2 (conj BY2 (conj CSn2 I)))))) as CBOX. clear HH2 FR2 PPc2 DAc2 BY2 CSn2.
      pose proof (munch_refl [(SIG + 192, SIG + 200)] m2) as MU3. pose proof (wmono_refl usegs m2) as WM3.
      unfold signer_cells in CS2. cbn [sj0 sj_merged sj1 sj2] in CS2.
      zstep.                                   (* [comment removed for export] *)
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      change (rw_cells usegs m3 SIG (signer_cells inext0 Sn sjh)) in CS2. rename CS2 into CS3.
      ddestruct CBOX as (HH2 & FR2 & PPc2 & DAc2 & BY2 & CSn2 & _).
      assert (WF3 : wfp Lc2 [(SIG + 192, SIG + 200)]) by (intros a Hna; cbn [outside] in Hna; first [clear_disj; lia | lia]).
      pose proof (HEAPm _ _ _ _ _ _ HH2 ltac:(rewrite HT2, HT1; exact HTc) MU3 WM3 WF3) as HH3.
      pose proof (HPXm _ _ _ _ _ _ HH2 MU3 WM3 WF3) as HPX23.
      lazymatch type of SO2 with statics_ok _ _ m3 => rename SO2 into SO3 | _ => pose proof (SOm _ _ _ _ _ _ HH2 SO2 MU3 WF3) as SO3; clear SO2 end.
      pose proof (rw_cells_transport usegs _ m2 m3 _ _ FR2 MU3 WM3 ltac:(cbn; lia)) as FR3.
      pose proof (rw_cells_transport usegs _ m2 m3 _ _ PPc2 MU3 WM3 ltac:(cbn; unfold SIGNER_SIZE in *; lia)) as PPc3.
      pose proof (rw_cells_transport usegs _ m2 m3 _ _ DAc2 MU3 WM3 ltac:(cbn; unfold SIGNER_SIZE in *; lia)) as DAc3.
      pose proof (bytes_at_transport usegs _ m2 m3 _ _ BY2 MU3 ltac:(cbn; lia)) as BY3.
      pose proof (rw_cells_transport usegs _ m2 m3 _ _ CSn2 MU3 WM3 ltac:(cbn [cells_size csize Nat.add signer_cells length disjoint_from]; lia)) as CSn3.
      destruct (heap_blocks usegs L HI _ _ _ _ HH2) as [BR2 _].
      pose proof (blocks_below_of_HEAP usegs L HI _ _ _ _ HH2) as BB2.
      assert (HPXb : heap_presx usegs L (Lc2 ++ LB) (bv_unsigned sp) [(SIG + 192, SIG + 200)] m2 m3).
      { eapply heap_presx_of_frame_munch; [exact MU3| exact WM3| exact BR2| exact DHI|]. intros a. cbn [outside]. lia. }
      assert (CHb : forall a' ns', name_chain usegs (fun _ => True) m2 (Lc2 ++ LB) a' ns' -> name_chain usegs (fun _ => True) m3 (Lc2 ++ LB) a' ns').
      { intros a' ns' HCx. eapply chain_presx; [exact HCx| intros x Hx; eapply chain_nodes_in; [exact HCx| exact Hx] | exact HPXb| unfold NAME_SIZE; lia|].
        intros x Hx. destruct (BB2 _ (chain_nodes_in usegs _ _ _ _ _ _ _ HCx x Hx)) as [_ Bx]. cbn [fst snd] in Bx. cbn. unfold NAME_SIZE in *. lia. }
      assert (SUB2 : forall b, In b L1 -> In b (Lc2 ++ LB)) by (intros b Hb; rewrite <- EL2; apply in_or_app; right; exact Hb).
      assert (HN03 : name_chain usegs (fun _ => True) m3 (Lc2 ++ LB) inext0 names0).
      { apply CHb. eapply chain_mem; [exact HN02| intros x Hx; apply SUB2; eapply chain_nodes_in; [exact HN02| exact Hx] | intros x cs _ HR _; exact HR]. }
      pose proof (CHb _ _ HNn2) as HNn3.
      clear HH2 FR2 PPc2 DAc2 BY2 CSn2 HN02 HNn2 MU3 WM3 MK HPX2. pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK.
      assert (HPXA3 : heap_presx usegs L LB (bv_unsigned sp) X0 m m3).
      { eapply heap_presx_trans; [exact HPXA2| exact HPX23]. }
      assert (ELc2 : Lc2 = sbl ([] ++ [(Sn, nodes2)]) ++ SNAME (rev names0)) by (unfold Lc2, Lc; cbn [sbl app]; repeat rewrite <- app_assoc; reflexivity).
      assert (OP3 : OPEN m3 Lc2 inext0 names0 Sn [] Sn inext2 nodes2 sjn).
      { split; [exact HN03|]. split; [reflexivity|].
        split; [exact CSn3|]. split; [exact HNn3|]. split; [exact SnAL|]. split; [exact SnP|].
        split; [unfold Lc2; apply in_or_app; right; left; reflexivity|].
        split; [destruct (APLB _ _ BIN); unfold SIGNER_SIZE in *; lia|].
        split; [intros []| exact ELc2]. }
      pose proof B6 as B6'.
      zstep; if_cases KW; zify_cond KW; [exfalso; rewrite ?signed_lit64 in KW by lia; lia|]. zstep.  (* [comment removed for export] *)
      zstep. zstep.                            (* [comment removed for export] *)
      zstep. if_cases KE; zify_cond KE; rewrite ?unsigned_lit in KE by lia.
      - (* [comment removed for export] *)
        eapply (LOOP (Z.to_nat (ES - p2)) ES p2 2 lw inext0 names0 sjh Sn [] Sn inext2 nodes2 sjn Lc2 m3 mo2 h2); [lia| lia| lia| exact HES| lia| lia| | exact OP3].
        split; [exact HH3|]. split; [rewrite HT2, HT1; exact HTc|]. split; [eapply mo_frame_trans; [| exact MF2]; eapply mo_frame_trans; eassumption|]. split; [exact HPXA3|].
        split; [eexists; exact FR3|]. split; [exact PPc3|]. split; [lia|]. split; [exact CS3|]. split; [exact CSZ|].
        split; [exact DAc3|]. split; [exact BY3|]. split; [assumption|]. split; [exact SO3| exact ST2].
      - (* [comment removed for export] *)
        zstep.                                 (* [comment removed for export] *)
        eapply (L_RET lw p2 _ Lc2 m3 mo2 h2 2 inext0 Sn sjh names0 ([] ++ [(Sn, nodes2)])).
        + split; [exact HH3|]. split; [rewrite HT2, HT1; exact HTc|]. split; [eapply mo_frame_trans; [| exact MF2]; eapply mo_frame_trans; eassumption|]. split; [exact HPXA3|].
          split; [eexists; exact FR3|]. split; [exact PPc3|]. split; [lia|]. split; [exact CS3|]. split; [exact CSZ|].
          split; [exact DAc3|]. split; [exact BY3|]. split; [assumption|]. split; [exact SO3| exact ST2].
        + exact CS3.
        + exact HN03.
        + eapply CLOSE. exact OP3.
        + rewrite ELc2. apply PERMc.
        + lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00`0@L10823794898.181L1107921941.169 L11102322379.180L12490560178.180L12660708096.181L13350887686.170L1386317440.170 L16720171459.169L20763674639.172L2152427316.179 L26014308813.181L26071143599.134L27868060268.177L30993653749.181L3596415124.172 L36253174270.139L38292021890.178L39362637032.178L39708773790.172L41202929119.136L41202929119.169L41296042896.15 L46885441310.171L48181734847.180L50614076257.137L5218906992.179 L56786620166.171L57424674654.179L57818648392.138L57818681289.171L58046932881.181L61484463176.138L63088320966.178L64313980563.172L6933972054.176 L7632799155.135 R11327856486.139R12490559893.139R20323958768.139R2562390148.139 R29459104055.139R31088232667.139R33283891529.139R33977505726.139R41293539632.139R60236468947.139R63261865041.139R6427804194.139 00000J02A02Z03403N03k03l05c07>07X08K09K09a0:j0;X0<:0<T0<j0=N0=d0>:0>;0?W0@00@F0@`0A=0AS0Ai0B?0CH0C^0D80DN0Dd0E:0FJ0Fd0G>0H_0J40KD0L[0Md0Me0NE0OV0PmS2sp2PP3BUF3SIG4DALG2bs2sjS1L3HLS2sp2PP1P3END3BUF3SIG4DALG2lo2bs2sj2B12B32B42B53PP13SG13DA14CEIL3SPR2lw2p13Hp13HLW7SLO304'3ACP4BCE'2p24Hp2'5HprogS2sp2PP3SIG4DALG2bs2sj2D3S2sp2PP3SIG4DALG2bs2sj3DA1S2sp2PP3BUF3SIG4DALG2bs2sjS2sp2PP3SIG4DALG2bs2sj2r23Hr2FS1L3HLS2sp2PP1P3END3BUF3SIG4DALG2lo2bs2sj2B12B32B42B53PP13SG13DA14CEIL3SPR2lw2p13Hp13HLW7SLO304'3ACP4BCE'2p24Hp2'5HprogS1L3HLS2sp2PP1P3SIG4DALG2lo2bs2sj3PP13SG13DA12D12D22D34CEIL3SPR2p13Hp17SLO304'3ACP2p25HprogS2sp2PP3SIG4DALG2bs2sj3SG1S2sp2PP3SIG4DALG2bs2sj2lw3LWR2KL2r23Hr22A02kk2Y12Y2S1L3HLS2sp2PP3SIG4DALG2lo2bs2sj3PP13SG13DA14CEIL3SPR7SLO304'3ACPS2sp2PP3SIG4DALG2bs2sjS1L3HLS2sp2PP3BUF3SIG4DALG2lo2bs2sj3PP13SG13DA14CEIL3SPR7SLO304'3ACP4BCE'S2sp2PP3SIG4DALG2bs2sj2lw2p13LWR2KL2p24Hp2'2KES1L2sp2PP3SIG4DALG2lo2bs2sj6SLO304S2sp2PP3SIG4DALG2bs2sj3SG1S2sp2PP3SIG4DALG2bs2sjS2sp2PP3END3SIG4DALG2bs2sj2lw2p13HLWS2sp2PP3SIG4DALG2bs2sjS2sp2PP3SIG4DALG2bs2sjFS1L3HLS2sp2PP1P3END3SIG4DALG2lo2bs2sj3PP13SG13DA14CEIL3SPR2lw2p13Hp13HLW7SLO304'3ACP2p24Hp2'S2sp2PP3SIG4DALG2bs2sj2D2S2sp2PP3SIG4DALG2bs2sjS2sp2PP3SIG4DALG2bs2sj3PP1S2sp2PP3SIG4DALG2bs2sj2r23Hr2S2sp2PP3SIG4DALG2bs2sjS2sp2PP3SIG4DALG2bs2sjS2sp2PP3SIG4DALG2bs2sjS1L3HLS2sp2PP3BUF3SIG4DALG2lo2bs2sj3PP13SG13DA14CEIL3SPR7SLO304'3ACP4BCE'S2sp2PP3SIG4DALG2bs2sjS2sp2PP3SIG4DALG2bs2sj3PP1S2sp2PP3SIG4DALG2bs2sjS2sp2PP3SIG4DALG2bs2sjS2sp2PP3SIG4DALG2bs2sjS1L3HLS2sp2PP1P3BUF3SIG4DALG2lo2bs2sj2B13PP13SG13DA14CEIL3SPR2p13Hp17SLO304'3ACPS2sp2PP3SIG4DALG2bs2sj3DA1S2sp2PP3SIG4DALG2bs2sj3PP1S1L2HI3HLS2sp1h2LB2PP3SIG4DALG2lo2bs2sj3PP13PP23SG13SG23DA13DA22D12D34CEIL3SPR2hc3HTc7SLO304'3ACPS1L3HLS2sp2PP3END3BUF3SIG4DALG2lo2bs2sj2B33PP13SG13DA14CEIL3SPR2lw2p13HLW7SLO304'3ACPS1L2HI3HLS2sp1h2PP3SIG4DALG2lo2bs2sj3PP13SG13SG23DA14CEIL3SPR2hc3HTc7SLO304'3ACPS1L2HI3HLS2sp1h2PP3SIG4DALG2lo2bs2sj3PP23SG13SG23DA13DA22D24CEIL3SPR2hc3HTc7SLO304'3ACPS1L3HLS2sp2PP3BUF3SIG4DALG2lo2bs2sj3PP13SG13DA14CEIL3SPR7SLO304'3ACP4BCE'FS2sp2PP3SIG4DALG2bs2sj2lw2p13LWRS1L3HLS2sp2PP3SIG4DALG2lo2bs2sj3ALP3ALS3ALD3PP13SG13DA14CEIL4SP163SPR7SLO304'3ACPS1L2HI3HLS2sp1h2PP3SIG4DALG2lo2bs2sj3PP13PP23SG13SG23DA22D34CEIL3SPR2hc3HTc7SLO304'3ACP". (* [comment removed for export] *)
    #[using="HFREE HCALLOC HMSF HLS SW DIMG DHI HND GETALG SIGNER HH ALP BIN B1 B3 B4 B5 B6 ALS ALD Q1 Q2 Q3 PP1 PP2 SG1 SG2 DA1 DA2 D1 D2 D3 CEIL SLO SP16 SPTOP TP SPR LOSP SLO320 BCE"] Lemma HEAD : forall (lw : word) p1 mc moc hc
        (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31 : word),
      gv lw p1 (signer_cells 0 0 sj) [] mc moc hc ->
      P + 2 <= p1 -> bv_unsigned lw <= END - p1 ->
      aevtM usegs moc POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 (Z_to_bv 64 SIG) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 DALG) (Z_to_bv 64 PP) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x1e078) fc None mc (seg_rom usegs)).
    Proof.
      intros lw p1 mc moc hc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31 D Hp1 HLW. pose proof D as D0. gv_open D.
      pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof LOSP as LOSP'. pose proof SLO320 as SLO320'. pose proof alloc_ceiling_pos as ACP. pose proof BCE as BCE'.
      pose proof (unsigned_lit (bv_unsigned sp + -96) ltac:(lia)) as USP.
      pose proof (bv_unsigned_in_range 64 lw) as LWR. unfold bv_modulus in LWR. cbn in LWR.
      unfold SAVED in FR. splitat FR 2%nat SV.
      zstep.                                   (* [comment removed for export] *)
      zstep. if_cases KL; zify_cond KL.
      { (* [comment removed for export] *)
        zstep. zstep.
        eapply (L_RET lw p1 _ [] mc moc hc 0 0 0 sj [] []); [| exact CS| apply chain_nil| reflexivity| apply Permutation_refl| lia].
        unfold SAVED. joinr FR SV. exact D0. }
      zstep. zstep; if_cases KA0; zify_cond KA0; [al8_close KA0|].
      zstep. zstep.                            (* [comment removed for export] *)
      zstep; if_cases KW0; zify_cond KW0; [exfalso; rewrite ?unsigned_lit in KW0 by lia; lia|].
      zstep; if_cases KN0; zify_cond KN0; [exfalso; rewrite ?unsigned_lit in KN0 by lia; lia|].
      zstep; if_cases KN1; zify_cond KN1; [exfalso; rewrite ?unsigned_lit in KN1 by lia; lia|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.       (* [comment removed for export] *)
      pose proof SIGNER as SPS. unfold pkcs7_signer_stmt, U_PKCS7_SIGNER in SPS. cbn [app] in HHc.
      eapply aevtM_cut.
      { eapply SPS with (PP := PP) (P := p1) (END := p1 + bv_unsigned lw) (BUF := BUF) (bs := bs) (S := SIG) (DALG := DALG) (lo := lo) (h := hc) (LB := LB)
                        (sj := sj) (dtg := dtg) (dpad := dpad) (dlen := dlen) (dq := dq);
          try reflexivity; rewrite ?USP; try eassumption; try (is_arith_goal; unfold SIGNER_SIZE in *; plia);
          try (clear - SP16 SPR LOSP' CEIL ACP; Z.div_mod_to_equations; is_arith_goal; lia).
        unfold PKCS7_SIGNER_STACK. lia. }
      intros ms' mo'x PO.
      ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 & mo2 & h2 & r2 & p2 & inext2 & sjn & nodes2
                      & E0 & -> & Hr2 & MI2 & SO2 & ST2 & MF2 & HT2 & PPc2 & Hp2' & Hprog & CSn2 & HNn2 & HND2 & HAP2 & HH2 & HPX2 & HRn).
      injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite ?USP in ST2. rewrite ?USP in HPX2. fix_ret 0x1e0b0. clear SPS.
      assert (HPXA2 : heap_presx usegs L LB (bv_unsigned sp) X0 m m2).
      { eapply heap_presx_trans; [exact HPXc|]. eapply heap_presx_weaken; [exact HPX2| intros b Hb; exact Hb| lia| unfold SIGNER_SIZE; intros x Hx; exact Hx]. }
      assert (XD : forall A0 kk, (A0 + kk <= PP \/ PP + 8 <= A0) -> (A0 + kk <= SIG \/ SIG + 200 <= A0) -> disjoint_from [(PP, PP + 8); (SIG, SIG + SIGNER_SIZE)] A0 kk)
        by (intros A0 kk Y1 Y2; cbn; unfold SIGNER_SIZE; lia).
      pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX2 FR ltac:(apply client_range_stack; lia) ltac:(apply XD; cbn; lia)) as FR2.
      pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX2 SV ltac:(apply client_range_stack; lia) ltac:(apply XD; cbn; lia)) as SV2.
      pose proof (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX2 DAc ltac:(apply client_range_stack; lia) ltac:(apply XD; cbn; unfold SIGNER_SIZE in *; lia)) as DAc2.
      pose proof (heap_presx_bytes_at usegs L _ _ _ _ _ _ _ HPX2 BYc ltac:(eapply client_range_block; [exact BIN| lia| lia]) ltac:(apply XD; lia)) as BY2.
      clear HHc HPXc FR SV PPc CS DAc BYc SOc STc MIc MK. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK.
      assert (G2 : gv lw p2 (signer_cells inext2 0 sjn) (SNAME (rev nodes2)) m2 mo2 h2).
      { split; [exact HH2|]. split; [congruence|]. split; [eapply mo_frame_trans; eassumption|]. split; [exact HPXA2|].
        split; [unfold SAVED; joinr FR2 SV2; eexists; exact FR2|]. split; [exact PPc2|]. split; [lia|]. split; [exact CSn2|]. split; [reflexivity|].
        split; [exact DAc2|]. split; [exact BY2|]. split; [exact MI2|]. split; [exact SO2| exact ST2]. }
      zstep.                                   (* [comment removed for export] *)
      zstep. if_cases KR; zify_cond KR.
      { (* [comment removed for export] *)
        kz KR. specialize (HRn KR). subst nodes2. cbn [rev SNAME map app] in G2, HNn2.
        eapply (L_RET lw p2 _ [] m2 mo2 h2 r2 inext2 0 sjn [] []); [exact G2| exact CSn2| cbn; exact HNn2| reflexivity| apply Permutation_refl| lia]. }
      kz KR. subst r2. specialize (Hprog eq_refl).
      zstep.                                   (* [comment removed for export] *)
      zstep. if_cases KE; zify_cond KE; rewrite ?unsigned_lit in KE by lia.
      { (* [comment removed for export] *)
        zstep. zstep.
        eapply (L_RET lw p2 _ _ m2 mo2 h2 1 inext2 0 sjn nodes2 []); [exact G2| exact CSn2| exact HNn2| reflexivity| cbn [signer_blocks]; rewrite app_nil_r; apply perm_SNAME_rev| lia]. }
      zstep. zstep. zstep. zstep.              (* [comment removed for export] *)
      first [ match goal with |- context [Some (Z_to_bv 64 (bv_swrap 32 ?e))] =>
                replace (Z_to_bv 64 (bv_swrap 32 e) : word) with (Z_to_bv 64 (-22400) : word) by (apply bv_eq; vm_compute; reflexivity) end
            | replace (Z_to_bv 64 18446744073709529216 : word) with (Z_to_bv 64 (-22400) : word) by (apply bv_eq; vm_compute; reflexivity) ].
      eapply LOOP0; [ | | | exact G2| exact HNn2]; lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0110@D11805467289.116D11805467289.117D44622288685.118D44622288685.119D49698585326.118D49698585326.119D49705053714.116D49705053714.117D5285469359.118 D5285469359.119 D5300226131.116 D5300226131.117 D54126458602.117D54137119254.119L10940299790.156L15302269400.114L17439285167.155L22446743512.114L24111408389.146L25214214772.114L26071143599.102L26295990549.125L28561693403.148L29010569222.145L31225147636.114L31859309556.148L33460698767.123L34252222263.148L34705680216.114L35991933426.124L36897755907.114L37246946676.113L38344105949.154L3949578456.113 L40374333670.115L41843875160.114L43055402401.113L43090626337.148L43361664225.148L49283344500.114L50614076257.121L51454941784.114L52153385999.148L55310518004.114L5699067096.114 L57818693718.146L57818804596.114L58591023192.114L60761053398.153L61321319284.114L6139713783.119 L6139713783.146 L63829069812.114L67011106428.126L67280348888.114L67351568884.114L7632799155.114 L7641675350.152 L9446624768.145 R23097717474.122R25638420505.122R40794648064.122R48054497772.122R48708297805.122R5409152208.122 00000R01402C03g04\05f06L07207c08i09K09m0:O0;=0;c0<B0=Y0>80>e0?D0@A0@d0AQ0AR0B10BU0C80CW0D60DY0E80EW0F:0FY0G80GW0H>0Hb0IK0Ij0JI0Jh0KG0Kf0LE0Ld0MC0Mb0NH0Ng0Oi0Q00QO0RQ0S00SO0Sn0TT0U80VA0WO0XQ0Y40Z10[3S2sp2PP3SIG4DALG2bs3PPB3DAB3SGB2HBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGB2HBS1L3HLS3DHI2ra2sp2PP3SIG4DALG2lo2bs4CEIL3SPR7SLO304'3PPB3DAB3SGB2HB5Ha_st5Hl_stS1L3HLS3DHI2sp2s02PP3SIG4DALG2lo2bs4CEIL3SPR7SLO304'3PPB3DAB3SGB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2ra2sp2PP3SIG4DALG2bs3SPR3PPB3DAB3SGB2HB5Ha_st5Hl_stS2sp2s02PP3SIG4DALG2bs3SPR3PPB3DAB3SGB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2sp2PP3SIG4DALG2bs3SPR3PPB3DAB3SGB2HBS2sp2PP3SIG4DALG2bs3SPR3PPB3DAB3SGB2HBS2ra2sp2PP3SIG4DALG2bs3PPB3DAB3SGB2HB5Ha_st5Hl_stS2sp2s02PP3SIG4DALG2bs3PPB3DAB3SGB2HB5Ha_st5Hl_st2s12s22s32s42s52s62s7S2sp2PP3SIG4DALG2bs3PPB3DAB3SGB2HBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGB2HBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGB2HBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGB2HB5Ha_st5Hl_stS2sp2PP3SIG4DALG2lo2bs3PP13PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS1L3HLS2sp2PP3BUF3SIG4DALG2lo2bs3PP13SG13DA12D12D22D34CEIL3SPR7SLO304'4BCE'3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS2sp2PP1P3END3SIG4DALG2bs3PPB3DAB3SGB2p14Hp1'S2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR7SLO304'3ACPS2sp2PP3SIG4DALG2bs3DA13PPB3DAB3SGBS2sp2PP3END3SIG4DALG2bs3PPB3DAB3SGB2p12Lw3HLwFS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGB1r2HrS2sp2PP3SIG4DALG2bs3SG13PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PP13PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PP13PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS2sp2PP3SIG4DALG2lo2bs4LOSP3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGB1r2HrS2sp2PP1P3SIG4DALG2bs3PPB3DAB3SGB2p14Hp1aS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3DA12D23PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13SPR7SLO304'3PPB3DAB3SGB1a3HnaS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13SPR7SLO304'3PPB3DAB3SGB1r2Hr1a3HnaS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS1L3HLS2sp2PP3BUF3SIG4DALG2lo2bs4CEIL3SPR7SLO304'4BCE'3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3SG12D13PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PPB3DAB3SGB1r2HrS1L3HLS2sp2PP3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR7SLO304'3ACP3PPB3DAB3SGBS1L3HLS2sp2PP3BUF3SIG4DALG2lo2bs3PP13SG13DA14CEIL3SPR7SLO304'4BCE'3PPB3DAB3SGBS1L3HLS2sp2PP3BUF3SIG4DALG2lo2bs4CEIL3SPR7SLO304'4BCE'3PPB3DAB3SGBS2sp2PP3SIG4DALG2bs3PP13PPB3DAB3SGBS1L3HLS2sp2PP3SIG4DALG2lo2bs4CEIL3SPR7SLO304'3ACP3PPB3DAB3SGBS1L3HLS2sp2PP3SIG4DALG2lo2bs4CEIL4SP163SPR7SLO304'3ACP3PPB3DAB3SGB". (* [comment removed for export] *)
    #[using="HFREE HCALLOC HMSF HLS SW DIMG DHI HND GETALG SIGNER BUF bs sj HH HPP ALP BY BIN B1 B2 B3 B4 B5 B6 HS ALS HDA ALD Q1 Q2 Q3 PP1 PP2 SG1 SG2 DA1 DA2 D1 D2 D3 ST CEIL SLO SP16 SPTOP MI SO TP SPR LOSP SLO320 BCE"] Lemma ENTRY : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      aevtM usegs mo POST
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PP) (Z_to_bv 64 END) (Z_to_bv 64 SIG) (Z_to_bv 64 DALG) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1dfe8) fc None m (seg_rom usegs)).
    Proof.
      intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6.
      pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof LOSP as LOSP'. pose proof SLO320 as SLO320'. pose proof alloc_ceiling_pos as ACP. pose proof BCE as BCE'.
      pose proof (unsigned_lit (bv_unsigned sp + -96) ltac:(lia)) as USP.
      pose proof (rw_cells_bound usegs m PP _ HPP) as PPB. cbn [cells_size csize Nat.add] in PPB.
      pose proof (rw_cells_bound usegs m DALG _ HDA) as DAB. cbn [cells_size csize Nat.add buf_cells] in DAB.
      pose proof (rw_cells_bound usegs m SIG _ HS) as SGB. cbn [cells_size csize Nat.add signer_cells] in SGB.
      pose proof BY as BY0. pose proof HS as HS0. pose proof HPP as HPP0. pose proof HDA as HDA0. pose proof SO as SO0. pose proof ST as ST0. pose proof MI as MI0. pose proof HH as HH0.
      set (m_entry := m) in BY, HS, HPP, HDA, SO, ST, MI, HH.   (* [comment removed for export] *)
      pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl usegs m) as WM0.
      pose proof (conj HS0 (conj HPP0 (conj HDA0 (conj BY0 (conj HH0 I))))) as CBOX. clear HS0 HPP0 HDA0 BY0 HH0.
      zstep. carve_frame 96%nat ST0.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
      zstep. zstep. zstep.                     (* [comment removed for export] *)
      zstep.                                   (* [comment removed for export] *)
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
      ddestruct CBOX as (HS0 & HPP0 & HDA0 & BY0 & HH0 & _).
      assert (WF0 : wfp [] [(bv_unsigned sp - 96, bv_unsigned sp)]) by (intros a Hna; cbn [outside] in Hna; first [clear_disj; lia | lia]).
      pose proof (HEAPm _ [] _ _ _ _ HH0 eq_refl MU0 WM0 WF0) as HHm0.
      pose proof (HPXm _ [] _ _ _ _ HH0 MU0 WM0 WF0) as HPX0'.
      lazymatch type of SO0 with statics_ok _ _ m0 => rename SO0 into SO1 | _ => pose proof (SOm _ [] _ _ _ _ HH0 SO0 MU0 WF0) as SO1; clear SO0 end.
      pose proof (rw_cells_transport usegs _ m m0 _ _ HS0 MU0 WM0 ltac:(cbn [cells_size csize Nat.add signer_cells disjoint_from]; lia)) as HS1.
      pose proof (rw_cells_transport usegs _ m m0 _ _ HPP0 MU0 WM0 ltac:(cbn; lia)) as HPP1.
      pose proof (rw_cells_transport usegs _ m m0 _ _ HDA0 MU0 WM0 ltac:(cbn; lia)) as HDA1.
      pose proof (bytes_at_transport usegs _ m m0 _ _ BY0 MU0 ltac:(cbn; lia)) as BY1.
      clear HS0 HPP0 HDA0 BY0 MU0 WM0 MK HH0. pose proof (heap_mok _ _ HI _ _ _ _ HHm0) as MK.
      (* [comment removed for export] *)
      zstep. zstep. zstep.                     (* [comment removed for export] *)
      lazymatch goal with H : rw_cells usegs m0 (bv_unsigned sp + -96) _ |- _ => rename H into FR end.
      splitat FR 2%nat SV. splitat FR 1%nat LN.
      pose proof U_asn1_get_tag_spec as SPT. unfold asn1_get_tag_stmt, U_ASN1_GET_TAG in SPT.
      eapply aevtM_cut_evt; [exact MK | |].
      { eapply SPT with (PP := PP) (LENP := bv_unsigned sp + -88) (P := P) (END := END) (BUF := BUF) (bs := bs) (tag := 49);
          try eassumption; try reflexivity; rewrite ?USP; try eassumption; try (is_arith_goal; unfold SIGNER_SIZE in *; plia);
          try (clear - SP16 SPR LOSP' CEIL ACP; Z.div_mod_to_equations; is_arith_goal; lia). }
      intros ms' PO. ddestruct PO as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m1 & r & p1 & Lw
                                 & -> & MU1 & WM1 & MI1 & -> & Hr & PPc1 & LEN1 & Hp1' & HOK).
      rewrite ?USP in MU1. fix_ret 0x1e030. clear SPT.
      assert (WF1 : wfp [] [(PP, PP + 8); (bv_unsigned sp + -88, bv_unsigned sp + -88 + 8)]) by (intros a Hna; cbn [outside] in Hna; first [clear_disj; lia | lia]).
      pose proof (HEAPm _ [] _ _ _ _ HHm0 eq_refl MU1 WM1 WF1) as HH1.
      pose proof (HPXm _ [] _ _ _ _ HHm0 MU1 WM1 WF1) as HPX01.
      assert (HPX1 : heap_presx usegs L LB (bv_unsigned sp) X0 m m1) by (eapply heap_presx_trans; [exact HPX0'| exact HPX01]).
      pose proof (SOm _ [] _ _ _ _ HHm0 SO1 MU1 WF1) as SO2.
      pose proof (rw_cells_transport usegs _ m0 m1 _ _ HS1 MU1 WM1 ltac:(cbn [cells_size csize Nat.add signer_cells disjoint_from]; unfold SIGNER_SIZE in *; lia)) as HS2.
      pose proof (rw_cells_transport usegs _ m0 m1 _ _ HDA1 MU1 WM1 ltac:(cbn; unfold SIGNER_SIZE in *; lia)) as HDA2.
      pose proof (rw_cells_transport usegs _ m0 m1 _ _ SV MU1 WM1 ltac:(cbn; lia)) as SV2.
      pose proof (rw_cells_transport usegs _ m0 m1 _ _ FR MU1 WM1 ltac:(cbn; lia)) as FR2.
      pose proof (bytes_at_transport usegs _ m0 m1 _ _ BY1 MU1 ltac:(cbn; unfold SIGNER_SIZE in *; lia)) as BY2.
      lazymatch goal with H : stk usegs m0 _ _ |- _ => pose proof (stk_transport_disjoint usegs _ m0 m1 _ _ H MU1 WM1 ltac:(cbn; lia)) as ST2; clear H end.
      clear HHm0 HPX0' HPX01 SO1 MU1 WM1 MK HS1 HPP1 HDA1 BY1 SV FR. pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK.
      pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn in LR.
      assert (G1 : gv Lw p1 (signer_cells 0 0 sj) [] m1 mo h).
      { split; [exact HH1|]. split; [reflexivity|]. split; [apply mo_frame_refl|]. split; [exact HPX1|]. split; [unfold SAVED; joinr FR2 LEN1; joinr FR2 SV2; eexists; exact FR2|].
        split; [exact PPc1|]. split; [lia|]. split; [exact HS2|]. split; [reflexivity|]. split; [exact HDA2|]. split; [exact BY2|].
        split; [exact MI1|]. split; [exact SO2| exact ST2]. }
      zstep. if_cases KT; zify_cond KT.
      - (* [comment removed for export] *) kz KT. subst r. destruct (HOK eq_refl) as [Hp1a HLw].
        eapply HEAD; [exact G1| lia| lia].
      - (* [comment removed for export] *) kz KT.
        zstep. zstep. zstep.                   (* [comment removed for export] *)
        first [rewrite swrap32_land_errsum by lia | rewrite swrap32_errsum by lia].
        zstep; if_cases KC1; zify_cond KC1; [exfalso; rewrite ?signed_lit64 in KC1 by lia; lia|].
        eapply (L_RET Lw p1 _ [] m1 mo h (r + (18446744073709529472 - 2 ^ 64)) 0 0 sj [] []); [exact G1| exact HS2| apply chain_nil| reflexivity| apply Permutation_refl| lia].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Body.

  #[using="HFREE HCALLOC HMSF HLS SW DIMG DHI HND GETALG SIGNER"] Theorem U_pkcs7_getsigners_spec : pkcs7_getsigners_stmt usegs L HI U_PKCS7_GETSIGNERS U_MEMSET_FUNC.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB PP P END BUF SIG DALG lo bs dtg dpad dlen dq sj
           HH HPP ALP BY BIN B1 B2 B3 B4 B5 B6 HS ALS HDA ALD Q1 Q2 Q3 PP1 PP2 SG1 SG2 DA1 DA2 D1 D2 D3 ST CEIL SLO SP16 SPTOP DHI' MI SO MSF TP -> -> -> ->.
    unfold U_PKCS7_GETSIGNERS.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2 ^ 64) in SPR.
    eapply ENTRY; try eassumption.
  Qed.
End Walk.
