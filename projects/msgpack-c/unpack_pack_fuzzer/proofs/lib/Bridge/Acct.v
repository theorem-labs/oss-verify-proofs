(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Exec ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanCtrlProps AsanEmbed AsanInv AsanBudget AsanTotalCore AsanNodeSem AsanTotal AsanFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import BackingAlgebra.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AProto ABase AMalloc_iface AMalloc_iface2 AArenaLaw ATsafeCore ATsafeEv ATsafeAlloc ATsafeOps.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AEmbRep AEmbFrame APristLaw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AFake_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Adeq.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Unset Lia Cache.

Section Acct.
Context {rc : runConstT}.
Variable NMAX : nat.
Hypothesis HLIM : NLK0 + Z.of_nat NMAX * 4096 <= LIMIT.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAX) fstepS NMAX).

Lemma TS_twfS : forall {R} (t : itree node (exc R)) RNG A mo P, TS NMAX RNG A t mo P -> twfS RNG A t mo P.
Proof.
  intros R t. induction t as [[|r]|n k IH]; intros RNG A mo P H; cbn in H |- *.
  - exact H.
  - exact H.
  - destruct H as (HA & HS & HX & HK). split; [exact HA|]. split; [exact HS|]. split; [exact HX|].
    intros rsp mo' evs Hst. destruct (HK rsp mo' evs Hst) as (E & RNG' & A' & HF & HL & HT).
    split; [exact E|]. exists RNG', A'. split; [exact HF|]. split; [exact HL|]. apply IH. exact HT.
Qed.

Lemma canon_of_mrel : forall A moc mo, mrel A moc mo -> canon mo = moc.
Proof.
  intros A moc mo (SB & CAN & _). unfold same_but_mat in SB. rewrite SB. clear SB.
  destruct moc as [fd [mp lzz mt] io fs pr lm tm]. cbn in CAN. subst mt. reflexivity.
Qed.

Lemma canon_same_but_mat : forall mo mo', same_but_mat mo mo' -> canon mo' = canon mo.
Proof.
  intros mo mo' SB. unfold same_but_mat in SB. rewrite SB. clear SB.
  destruct mo as [fd [mp lzz mt] io fs pr lm tm]. reflexivity.
Qed.

Definition acct_rel (mo mo' : Model) : Prop := vmh (canon mo) (canon mo').
Lemma acct_rel_refl : forall mo, acct_rel mo mo. Proof. intros. apply vmh_refl. Qed.
Lemma acct_rel_mat : forall mo mo', same_but_mat mo mo' -> acct_rel mo mo'.
Proof. intros mo mo' SB. unfold acct_rel. rewrite (canon_same_but_mat _ _ SB). apply vmh_refl. Qed.

Variable MP : Model -> Prop.
Variable MINV : Model -> Prop.
Variable OTHER : Model -> Model -> Prop.
Hypothesis MP_rel : forall mo mo', MP mo -> acct_rel mo mo' -> MP mo'.
Hypothesis OTHER_rel : forall mo mo', acct_rel mo mo' -> OTHER mo mo'.

Definition C0A (a : Z) : Prop := (0x10000 <= a < ABase.AIMG_HI) \/ (ATOP <= a < 18446744073709551616).

Definition lazy_shapeA (C0 : Z -> Prop) (mo : Model) : Prop := forall z, C0 z -> page_in_ranges (page_base_of z) (m_vm_lazy mo) = false.
Hypothesis MINV_intro : forall mo, m_halted mo = None -> lazy_shapeA C0A mo -> MINV mo.

Lemma acct_rel_fs : forall mo mo', acct_rel mo mo' -> m_fs mo' = m_fs mo.
Proof.
  intros mo mo' ((_ & _ & FS & _) & _). destruct mo as [fd [mp lzz mt] io fs pr lm tm], mo' as [fd' [mp' lzz' mt'] io' fs' pr' lm' tm'].
  cbn in FS |- *. unfold m_fs. cbn. rewrite FS. reflexivity.
Qed.
Lemma acct_rel_fds : forall mo mo', acct_rel mo mo' -> m_fds mo' = m_fds mo.
Proof.
  intros mo mo' ((FD & _) & _). destruct mo as [fd [mp lzz mt] io fs pr lm tm], mo' as [fd' [mp' lzz' mt'] io' fs' pr' lm' tm'].
  cbn in FD |- *. unfold m_fds. cbn. rewrite FD. reflexivity.
Qed.
Lemma acct_rel_halted : forall mo mo', acct_rel mo mo' -> m_halted mo' = m_halted mo.
Proof.
  intros mo mo' ((_ & _ & _ & PR & _) & _). destruct mo as [fd [mp lzz mt] io fs pr lm tm], mo' as [fd' [mp' lzz' mt'] io' fs' pr' lm' tm'].
  cbn in PR |- *. unfold m_halted. cbn. rewrite PR. reflexivity.
Qed.
Lemma acct_rel_lazy : forall mo mo' p, acct_rel mo mo' -> page_in_ranges p (m_vm_lazy mo') = true -> page_in_ranges p (m_vm_lazy mo) = true.
Proof.
  intros mo mo' p (_ & _ & LZ) H. destruct mo as [fd [mp lzz mt] io fs pr lm tm], mo' as [fd' [mp' lzz' mt'] io' fs' pr' lm' tm'].
  cbn in LZ, H |- *. exact (LZ p H).
Qed.

Lemma asan_minv_rel : forall (C0 : Z -> Prop) mo mo', (m_halted mo = None /\ lazy_shapeA C0 mo) -> acct_rel mo mo' ->
  m_halted mo' = None /\ lazy_shapeA C0 mo'.
Proof.
  intros C0 mo mo' [HH LS] AR. split; [rewrite (acct_rel_halted _ _ AR); exact HH|].
  intros z Hz. destruct (page_in_ranges (page_base_of z) (m_vm_lazy mo')) eqn:E; [| reflexivity].
  specialize (LS z Hz). rewrite (acct_rel_lazy _ _ _ AR E) in LS. discriminate LS.
Qed.

Definition FPX (L : alayout) (RNG : footprint) : Prop :=
  rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)) /\ rng RNG 0x10000 0x61f000 /\ rng RNG 0x7fffa000 0xc4000
  /\ rng RNG (shad ATOP) (Shadow.KHIGH - shad ATOP) /\ afake_rng L RNG.
Lemma rng_fp_mono : forall R R' lo n, fp_le R R' -> rng R lo n -> rng R' lo n.
Proof. intros R R' lo n LE (R1 & R2 & R3). split; [exact R1|]. split; [exact R2|]. intros b j Hb Hj. apply LE. apply R3; assumption. Qed.
Lemma FPX_mono : forall L R R', fp_le R R' -> FPX L R -> FPX L R'.
Proof.
  intros L R R' LE (F1 & F2 & F3 & F4 & F5). repeat (split; [eapply rng_fp_mono; [exact LE|]; assumption|]). exact (afake_rng_mono L R R' LE F5).
Qed.

Definition TIE (st : astate) (LBa : list ablock) : Prop :=
  forall id ch, (a_live st) !! id = Some ch -> exists Aaddr, In (HB id Aaddr (chunk_size ch)) LBa.

Variable SHFIX : word -> Prop.

Definition FIXZ (L : alayout) (moc : Model) : Prop :=
  Forall (fun e : word * word => bv_unsigned (fst e) + bv_unsigned (snd e) <= ABase.AIMG_HI) (vm_reserved (m_vmmaps moc))
  /\ (forall z, al_fake L <= z < al_fake L + 11571200 -> page_in_ranges (page_base_of z) (m_vm_lazy moc) = false)
  /\ m_halted moc = None
  /\ lazy_shapeA C0A moc.
Lemma FIXZ_vmh : forall L mo mo', vmh mo mo' -> FIXZ L mo -> FIXZ L mo'.
Proof.
  intros L mo mo' ((_ & _ & _ & PR & _) & ER & LZ) (F1 & F2 & F3 & F4). split; [rewrite ER; exact F1|]. split; [| split].
  - intros z Hz. destruct (page_in_ranges (page_base_of z) (m_vm_lazy mo')) eqn:E; [| reflexivity].
    specialize (F2 z Hz). rewrite (LZ _ E) in F2. discriminate.
  - revert F3 PR. destruct mo as [fd [mp lzz mt] io fs pr lm tm], mo' as [fd' [mp' lzz' mt'] io' fs' pr' lm' tm'].
    unfold m_halted. cbn. intros F3 ->. exact F3.
  - intros z Hz. destruct (page_in_ranges (page_base_of z) (m_vm_lazy mo')) eqn:E; [| reflexivity].
    specialize (F4 z Hz). rewrite (LZ _ E) in F4. discriminate.
Qed.

Lemma MINV_of_FIXZ : forall L mo, FIXZ L (canon mo) -> MINV mo.
Proof.
  intros L mo (_ & _ & F3 & F4). apply MINV_intro.
  - revert F3. destruct mo as [fd [mp lzz mt] io fs pr lm tm]. exact (fun H => H).
  - revert F4. destruct mo as [fd [mp lzz mt] io fs pr lm tm]. exact (fun H => H).
Qed.

Definition ACCT (aw : word) (L : alayout) (RNG : footprint) (st : astate) (LBa : list ablock) (mo : Model) : Prop :=
  exists RESV A,
    aresv_ok L RESV
    /\ ACCTc NMAX RESV SHFIX (bv_unsigned aw) RNG A st (canon mo)
    /\ List.NoDup (m_vm_materialized mo) /\ (forall p, In p (m_vm_materialized mo) -> A p)
    /\ FPX L RNG
    /\ FIXZ L (canon mo)
    /\ TIE st LBa.

Definition COVPb (mo : Model) (p : word) : Prop := COVP (canon mo) p \/ SHFIX p.

Lemma ACCT_mrel : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo ->
  exists RESV A, aresv_ok L RESV /\ ACCTc NMAX RESV SHFIX (bv_unsigned aw) RNG A st (canon mo) /\ mrel A (canon mo) mo.
Proof.
  intros aw L RNG st LBa mo (RESV & A & RK & HC & ND & AL & _). exists RESV, A. split; [exact RK|]. split; [exact HC|].
  apply mrel_canon; assumption.
Qed.

Lemma ACCTc_acct_ok : forall RESV v RNG A st mo, ACCTc NMAX RESV SHFIX v RNG A st mo -> acct_ok NMAX RNG A mo.
Proof.
  intros RESV v RNG A st mo HC. destruct (KI_entry NMAX RESV SHFIX v RNG A st mo 0 HC ltac:(lia)) as (k & HK & HP & HL).
  pose proof HC as (_ & _ & _ & -> & Hv & _). pose proof (GP_nonneg st (LW_emb _ _ _ HL)).
  eapply KI_acct_ok; [exact HLIM| exact HK| lia].
Qed.

Theorem ACCT_led : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVPb mo p -> A p).
Proof.
  intros aw L RNG st LBa mo H. destruct (ACCT_mrel _ _ _ _ _ _ H) as (RESV & A & _ & HC & MR). exists A. split.
  - pose proof (mrel_ainv NMAX RNG A (canon mo) mo (ACCTc_acct_ok _ _ _ _ _ _ HC) MR) as X.
    unfold canon in X. rewrite m_vm_lazy_MX in X. exact X.
  - destruct HC as (_ & _ & _ & _ & _ & _ & k & HAB & HCV & _). intros p [Hp|Hp]; [exact (HCV p Hp)| apply HAB; right; exact Hp].
Qed.

Theorem ACCT_mat : forall aw L RNG st LBa mo mo', ACCT aw L RNG st LBa mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVPb mo p) ->
  ACCT aw L RNG st LBa mo'.
Proof.
  intros aw L RNG st LBa mo mo' (RESV & A & RK & HC & ND & AL & FX & FZ & TI) SB ND' SUB.
  assert (EC : canon mo' = canon mo) by (apply canon_same_but_mat; exact SB).
  exists RESV, A. rewrite EC. split; [exact RK|]. split; [exact HC|]. split; [exact ND'|]. split; [| split; [exact FX| split; [exact FZ| exact TI]]].
  intros p Hp. destruct (SUB p Hp) as [Hm|Hc]; [exact (AL p Hm)|].
  destruct HC as (_ & _ & _ & _ & _ & _ & k & HAB & HCV & _). destruct Hc as [Hc|Hc]; [exact (HCV p Hc)| apply HAB; right; exact Hc].
Qed.

Theorem ACCT_fds : forall aw L RNG st LBa mo f, ACCT aw L RNG st LBa mo -> ACCT aw L RNG st LBa (with_fds f mo).
Proof.
  intros aw L RNG st LBa mo f (RESV & A & RK & HC & ND & AL & FX & FZ & TI).
  assert (EC : canon (with_fds f mo) = with_fds f (canon mo)) by (destruct mo as [fd [mp lzz mt] io fs pr lm tm]; reflexivity).
  exists RESV, A. rewrite EC. split; [exact RK|]. split; [| split; [exact ND| split; [exact AL| split; [exact FX| split; [exact FZ| exact TI]]]]].
  destruct HC as ([HA HM] & Q1 & Q2 & ER & Hv & HCR & k & HAB & HCV & HBU & Hk & HP).
  split; [split; [exact HA| apply AMI_with_fds; exact HM]|]. split; [exact Q1|]. split; [exact Q2|]. split; [exact ER|]. split; [exact Hv|]. split; [exact HCR|].
  exists k. split; [exact HAB|]. split; [exact HCV|]. split; [exact HBU|]. split; [exact Hk| exact HP].
Qed.

Theorem ACCT_fpx : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> FPX L RNG.
Proof. intros aw L RNG st LBa mo (RESV & A & _ & _ & _ & _ & FX & _). exact FX. Qed.

Theorem ACCT_halted : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> m_halted mo = None.
Proof.
  intros aw L RNG st LBa mo (RESV & A & _ & _ & _ & _ & _ & (_ & _ & F3 & _) & _).
  revert F3. destruct mo as [fd [mp lzz mt] io fs pr lm tm]. exact (fun H => H).
Qed.
Theorem ACCT_lazy_shape : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> lazy_shapeA C0A mo.
Proof.
  intros aw L RNG st LBa mo (RESV & A & _ & _ & _ & _ & _ & (_ & _ & _ & F4) & _).
  revert F4. destruct mo as [fd [mp lzz mt] io fs pr lm tm]. exact (fun H => H).
Qed.
Theorem ACCT_minv : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> MINV mo.
Proof. intros aw L RNG st LBa mo H. pose proof H as (RESV & A & _ & _ & _ & _ & _ & FZ & _). exact (MINV_of_FIXZ _ _ FZ). Qed.
Lemma minvA_canon : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> minvA (canon mo).
Proof.
  intros aw L RNG st LBa mo (RESV & A & _ & ([_ HM] & _) & _).
  destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [AT1 AT2] & _).
  split; [| reflexivity]. unfold spwin. unfold alloc_top in AT2. unfold atop_ok, ACEIL, ATOP_MAX in AT1.
  unfold sp_window_lo, sp_window_hi. unfold stack_max_size in AT2. lia.
Qed.

Theorem ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Proof. intros aw L RNG st LBa mo H. exact (proj1 (ACCT_fpx _ _ _ _ _ _ H)). Qed.
Theorem ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG 0x10000 0x61f000.
Proof. intros aw L RNG st LBa mo H. exact (proj1 (proj2 (ACCT_fpx _ _ _ _ _ _ H))). Qed.
Theorem ACCT_rng_aimg_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG 0x7fffa000 0xc4000.
Proof. intros aw L RNG st LBa mo H. exact (proj1 (proj2 (proj2 (ACCT_fpx _ _ _ _ _ _ H)))). Qed.
Theorem ACCT_rng_stk_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (shad ATOP) (Shadow.KHIGH - shad ATOP).
Proof. intros aw L RNG st LBa mo H. exact (proj1 (proj2 (proj2 (proj2 (ACCT_fpx _ _ _ _ _ _ H))))). Qed.
Theorem ACCT_frng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> afake_rng L RNG.
Proof. intros aw L RNG st LBa mo H. exact (proj2 (proj2 (proj2 (proj2 (ACCT_fpx _ _ _ _ _ _ H))))). Qed.

Definition c24b (b : ablock) : bool :=
  match ab_kind b with ABHeap _ => (5881 <=? ab_size b) && (ab_size b <=? 7936) | ABFake _ => false end.
Definition c24count (LBa : list ablock) : Z := Z.of_nat (length (List.filter c24b LBa)).
Definition hb_id (b : ablock) : list aptr := match ab_kind b with ABHeap p => [p] | ABFake _ => [] end.

Lemma NoDup_fst_filter : forall {K V} (f : K * V -> bool) (l : list (K * V)), List.NoDup (map fst l) -> List.NoDup (map fst (List.filter f l)).
Proof.
  intros K V f l. induction l as [|x l IH]; intros H; cbn; [constructor|].
  cbn in H. apply List.NoDup_cons_iff in H as [H1 H2]. destruct (f x); cbn; [| exact (IH H2)].
  apply List.NoDup_cons_iff. split; [| exact (IH H2)].
  intros Hin. apply H1. apply in_map_iff in Hin as (y & Ey & Hy). apply filter_In in Hy as [Hy _]. apply in_map_iff. exists y. auto.
Qed.

Lemma filter_map_snd : forall {K V} (f : V -> bool) (l : list (K * V)),
  List.filter f (map snd l) = map snd (List.filter (fun kv => f (snd kv)) l).
Proof. intros K V f l. induction l as [|x l IH]; cbn; [reflexivity|]. destruct (f (snd x)); cbn; rewrite IH; reflexivity. Qed.

Lemma hb_id_len : forall l, (length (flat_map hb_id l) <= length l)%nat.
Proof. induction l as [|b l IH]; cbn; [lia|]. rewrite length_app. unfold hb_id at 1. destruct (ab_kind b); cbn; lia. Qed.

Lemma c24_live_le : forall RESV v RNG A st mo LBa,
  ACCTc NMAX RESV SHFIX v RNG A st mo -> TIE st LBa -> cntP K_BATCH_CLASS (live_chunks st) <= c24count LBa.
Proof.
  intros RESV v RNG A st mo LBa HC TI. destruct HC as ([HA _] & _).
  assert (HWl : Forall (chunk_wf ATOP) (live_chunks st)).
  { destruct HA as (_ & HW & _). unfold all_chunks in HW. cbn [app] in HW. apply Forall_app in HW as [HW _]. exact HW. }
  unfold cntP, zlen, c24count, live_chunks in *. rewrite filter_map_snd, length_map.
  set (M := map_to_list (a_live st)) in *.
  set (M24 := List.filter (fun kv : aptr * achunk => is_prim_of K_BATCH_CLASS (snd kv)) M).
  apply Nat2Z.inj_le. change (length M24 <= length (List.filter c24b LBa))%nat. rewrite <- (length_map fst M24).
  assert (ND : List.NoDup (map fst M24)).
  { apply NoDup_fst_filter. apply NoDup_ListNoDup. apply NoDup_fst_map_to_list. }
  set (IDS := flat_map hb_id (List.filter c24b LBa)).
  assert (LEN : (length IDS <= length (List.filter c24b LBa))%nat).
  { unfold IDS. apply hb_id_len. }
  assert (INC : incl (map fst M24) IDS).
  { intros id Hid. apply in_map_iff in Hid as ([id' ch] & <- & Hin). cbn [fst]. apply filter_In in Hin as [Hin Hp]. cbn [snd] in Hp.
    assert (Hl : (a_live st) !! id' = Some ch) by (apply elem_of_map_to_list; apply list_elem_of_In; exact Hin).
    assert (Hw : chunk_wf ATOP ch).
    { eapply (proj1 (Forall_forall _ _) HWl). apply in_map_iff. exists (id', ch). split; [reflexivity| exact Hin]. }
    destruct ch as [c n|mb ms n]; cbn [is_prim_of] in Hp; [| discriminate]. apply Z.eqb_eq in Hp. subst c.
    cbn in Hw. destruct Hw as [Hn Hc]. pose proof (c24_range n Hn (eq_sym (prim_cls_c24 _ _ Hc eq_refl))) as R24.
    destruct (TI id' _ Hl) as (Aaddr & HinB). cbn [chunk_size] in HinB.
    unfold IDS. apply in_flat_map. exists (HB id' Aaddr n). split; [| left; reflexivity].
    apply filter_In. split; [exact HinB|]. unfold c24b. cbn [ab_kind ab_size]. apply andb_true_intro. split; apply Z.leb_le; lia. }
  pose proof (List.NoDup_incl_length ND INC). lia.
Qed.

Definition c6ok (RESV : list (Z * Z)) (RNG : footprint) (st : astate) : Prop :=
  c6m RESV RNG st /\ (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23).
Lemma lazy_page_false : forall lz z, 0 <= z < 2^64 -> covered lz z = false -> page_in_ranges (page_base_of z) lz = false.
Proof.
  intros lz z Hz HC. destruct (page_in_ranges (page_base_of z) lz) eqn:E; [| reflexivity]. exfalso.
  unfold page_in_ranges in E. apply existsb_exists in E as (r & Hr & Hp). apply andb_prop in Hp as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  assert (PB : bv_unsigned (page_base_of z) = z / 4096 * 4096).
  { unfold page_base_of, page_size. apply Z_to_bv_small. unfold bv_modulus. Z.div_mod_to_equations. lia. }
  rewrite PB in H1, H2. unfold page_size in H2.
  assert (CV : covered lz z = true).
  { unfold covered. apply existsb_exists. exists r. split; [exact Hr|]. unfold in_iv, in_rng, B, S.
    apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; Z.div_mod_to_equations; lia. }
  congruence.
Qed.
Lemma ACCTc_c6 : forall RESV v RNG A st mo, ACCTc NMAX RESV SHFIX v RNG A st mo -> c6ok RESV RNG st.
Proof.
  intros RESV v RNG A st mo HC. pose proof HC as (HI & Q1 & Q2 & ER & _).
  pose proof (INV_emb_c6 (RESV:=RESV) (ATOP:=ATOP) st mo HI) as X. unfold c6ok, c6m, emb_rng, emb_clr.
  destruct (a_emb st) as [[d cap] sz]. destruct X as (X1 & X2 & X3).
  split; [| unfold EMB_MAX in X1; exact X1]. split; [| exact X2].
  destruct X3 as [->|(D0 & D1 & NL)]; [left; reflexivity| right].
  split; [exact D0|]. split; [exact D1|]. intros b j Hb Hj. rewrite ER. intros k Hk Hb64.
  left. apply lazy_page_false; [lia|]. apply NL. lia.
Qed.

Lemma leaf_actual : forall L mo A' moc' mo', vmh (canon mo) moc' -> mrel A' moc' mo' -> MP mo -> FIXZ L (canon mo) ->
  MP mo' /\ MINV mo' /\ OTHER mo mo' /\ canon mo' = moc'.
Proof.
  intros L mo A' moc' mo' HH MR HMP FZ. pose proof (canon_of_mrel _ _ _ MR) as EC.
  assert (AR : acct_rel mo mo') by (unfold acct_rel; rewrite EC; exact HH).
  split; [exact (MP_rel _ _ HMP AR)|]. split; [| split; [exact (OTHER_rel _ _ AR)| exact EC]].
  apply (MINV_of_FIXZ L). rewrite EC. exact (FIXZ_vmh _ _ _ HH FZ).
Qed.

Definition acct_leaf (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock) (n chg : Z)
    (r : astate * option aptr) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo' Aaddr, mrel A' moc' mo' ->
    MP mo' /\ MINV mo' /\ OTHER mo0 mo' /\
    match snd r with
    | Some p => ACCT (Z_to_bv 64 (bv_unsigned aw - chg)) L RNG' (fst r) (HB p Aaddr n :: LBa) mo'
    | None => ACCT (Z_to_bv 64 (bv_unsigned aw - C_EXH)) L RNG' (fst r) LBa mo'
    end
    /\ (64512 < n -> aprist st -> aprist (fst r)).
Lemma aprist_keep : forall n st st', 64512 < n -> (is_primary n = false -> cls_keep K_BATCH_CLASS st st') -> aprist st -> aprist st'.
Proof.
  intros n st st' Hn CK PR c Hc Hc24. destruct (CK (large_not_primary n Hn) c Hc24) as [E1 E2]. rewrite E1, E2. exact (PR c Hc Hc24).
Qed.

Theorem ACCT_malloc : forall aw L RNG st LBa mo n chg,
  ACCT aw L RNG st LBa mo -> MP mo -> MINV mo ->
  1 <= n <= AREQMAX -> ((chg = 0 /\ n <= 64512) \/ (chg = n /\ n <= bv_unsigned aw)) -> C_EXH <= bv_unsigned aw -> c24count LBa <= 255 ->
  exists RESV A moc, aresv_ok L RESV /\ c6ok RESV RNG st /\ mrel A moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A (aembed ATOP (amalloc ATOP RESV st n)) moc (acct_leaf mo aw L st LBa n chg).
Proof.
  intros aw L RNG st LBa mo n chg HACC HMP HMI Hn HCHG Hcx H24.
  assert (HNV : is_primary n = false -> n <= bv_unsigned aw).
  { intros NP. destruct HCHG as [[_ H]|[_ H]]; [| exact H]. rewrite is_primary_iff in NP by lia. apply Z.leb_gt in NP. lia. }
  pose proof HACC as (RESV & A & RK & HC & ND & AL & FX & FZ & TI).
  exists RESV, A, (canon mo). split; [exact RK|]. split; [exact (ACCTc_c6 _ _ _ _ _ _ HC)|]. split; [apply mrel_canon; assumption|].
  split; [exact (minvA_canon _ _ _ _ _ _ HACC)|]. split; [exact (proj1 (proj2 (proj2 FZ)))|].
  apply TS_twfS.
  assert (H24' : size_of_class K_BATCH_CLASS * (cntP K_BATCH_CLASS (live_chunks st) + 1) <= L24MAX).
  { pose proof (c24_live_le _ _ _ _ _ _ _ HC TI). assert (S24 : size_of_class K_BATCH_CLASS = 8192) by reflexivity. rewrite S24. unfold L24MAX. lia. }
  eapply TS_mono; [apply (U_malloc NMAX HLIM RESV SHFIX (bv_unsigned aw) RNG A st (canon mo) n HC Hn HNV Hcx H24')|].
  intros r RNG' A' moc' _ (HH & HFL & CK & HLEAF) mo' Aaddr MR.
  destruct (leaf_actual L mo A' moc' mo' HH MR HMP FZ) as (M1 & M2 & M3 & EC).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
  split. 2:{ intros Hn64 PR. exact (aprist_keep n st (fst r) Hn64 CK PR). }
  destruct MR as (_ & _ & ND' & AL').
  pose proof (bv_unsigned_in_range 64 aw) as RA. unfold bv_modulus in RA.
  destruct (snd r) as [p|] eqn:Esnd.
  - destruct HLEAF as (-> & FRESH & (ch & ELIVE & ESZ) & HC').
    assert (HC'' : ACCTc NMAX RESV SHFIX (bv_unsigned aw - chg) RNG' A' (fst r) moc').
    { destruct HCHG as [[-> H]|[-> H]].
      - rewrite is_primary_iff in HC' by lia. rewrite (proj2 (Z.leb_le n 64512) H) in HC'. exact HC'.
      - destruct (is_primary n); [| exact HC']. apply (ACCTc_weaken NMAX RESV SHFIX (bv_unsigned aw - 0)); [exact HC'| lia]. }
    assert (CB : 0 <= chg <= bv_unsigned aw) by (destruct HCHG as [[-> _]|[-> H]]; lia).
    exists RESV, A'. rewrite EC, Z_to_bv_unsigned, (bv_wrap_small 64 (bv_unsigned aw - chg)) by (unfold bv_modulus; lia).
    split; [exact RK|]. split; [exact HC''|]. split; [exact ND'|]. split; [exact AL'|]. split; [exact (FPX_mono _ _ _ HFL FX)|]. split; [exact (FIXZ_vmh _ _ _ HH FZ)|].
    intros id ch' Hl. rewrite ELIVE in Hl. apply lookup_insert_Some in Hl as [[<- <-]|[NE Hl]].
    + exists Aaddr. left. rewrite ESZ. reflexivity.
    + destruct (TI id ch' Hl) as (Ad & Hin). exists Ad. right. exact Hin.
  - destruct HLEAF as (ELIVE & _ & HC').
    exists RESV, A'. rewrite EC, Z_to_bv_unsigned, (bv_wrap_small 64 (bv_unsigned aw - C_EXH)) by (unfold bv_modulus, C_EXH in *; lia).
    split; [exact RK|]. split; [exact HC'|]. split; [exact ND'|]. split; [exact AL'|]. split; [exact (FPX_mono _ _ _ HFL FX)|]. split; [exact (FIXZ_vmh _ _ _ HH FZ)|].
    intros id ch' Hl. rewrite ELIVE in Hl. exact (TI id ch' Hl).
Qed.

Theorem ACCT_aligned16 : forall aw L RNG st LBa mo n chg,
  ACCT aw L RNG st LBa mo -> MP mo -> MINV mo ->
  16 <= n <= 4096 -> n mod 16 = 0 -> ((chg = 0 /\ n <= 64512) \/ (chg = n /\ n <= bv_unsigned aw)) -> C_EXH <= bv_unsigned aw ->
  exists RESV A moc, aresv_ok L RESV /\ c6ok RESV RNG st /\ mrel A moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A (aembed ATOP (aaligned16x ATOP RESV st n)) moc (acct_leaf mo aw L st LBa n chg).
Proof.
  intros aw L RNG st LBa mo n chg HACC HMP HMI Hn Hm HCHG Hcx.
  pose proof HACC as (RESV & A & RK & HC & ND & AL & FX & FZ & TI).
  exists RESV, A, (canon mo). split; [exact RK|]. split; [exact (ACCTc_c6 _ _ _ _ _ _ HC)|]. split; [apply mrel_canon; assumption|].
  split; [exact (minvA_canon _ _ _ _ _ _ HACC)|]. split; [exact (proj1 (proj2 (proj2 FZ)))|].
  apply TS_twfS.
  eapply TS_mono; [apply (U_aligned16 NMAX HLIM RESV SHFIX (bv_unsigned aw) RNG A st (canon mo) n HC Hn Hm Hcx)|].
  intros r RNG' A' moc' _ (HH & HFL & CK & HLEAF) mo' Aaddr MR.
  destruct (leaf_actual L mo A' moc' mo' HH MR HMP FZ) as (M1 & M2 & M3 & EC).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
  split. 2:{ intros Hn64 _. exfalso. lia. }
  destruct MR as (_ & _ & ND' & AL').
  pose proof (bv_unsigned_in_range 64 aw) as RA. unfold bv_modulus in RA.
  assert (EP : is_primary n = true) by (rewrite is_primary_iff by lia; apply Z.leb_le; lia).
  destruct (snd r) as [p|] eqn:Esnd.
  - destruct HLEAF as (-> & FRESH & (ch & ELIVE & ESZ) & HC'). rewrite EP in HC'.
    assert (CB : 0 <= chg <= bv_unsigned aw) by (destruct HCHG as [[-> _]|[-> H]]; lia).
    assert (HC'' : ACCTc NMAX RESV SHFIX (bv_unsigned aw - chg) RNG' A' (fst r) moc').
    { apply (ACCTc_weaken NMAX RESV SHFIX (bv_unsigned aw - 0)); [exact HC'| lia]. }
    exists RESV, A'. rewrite EC, Z_to_bv_unsigned, (bv_wrap_small 64 (bv_unsigned aw - chg)) by (unfold bv_modulus; lia).
    split; [exact RK|]. split; [exact HC''|]. split; [exact ND'|]. split; [exact AL'|]. split; [exact (FPX_mono _ _ _ HFL FX)|]. split; [exact (FIXZ_vmh _ _ _ HH FZ)|].
    intros id ch' Hl. rewrite ELIVE in Hl. apply lookup_insert_Some in Hl as [[<- <-]|[NE Hl]].
    + exists Aaddr. left. rewrite ESZ. reflexivity.
    + destruct (TI id ch' Hl) as (Ad & Hin). exists Ad. right. exact Hin.
  - destruct HLEAF as (ELIVE & _ & HC').
    exists RESV, A'. rewrite EC, Z_to_bv_unsigned, (bv_wrap_small 64 (bv_unsigned aw - C_EXH)) by (unfold bv_modulus, C_EXH in *; lia).
    split; [exact RK|]. split; [exact HC'|]. split; [exact ND'|]. split; [exact AL'|]. split; [exact (FPX_mono _ _ _ HFL FX)|]. split; [exact (FIXZ_vmh _ _ _ HH FZ)|].
    intros id ch' Hl. rewrite ELIVE in Hl. exact (TI id ch' Hl).
Qed.

Definition acct_leaf_some (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock) (n chg : Z)
    (r : astate * option aptr) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo' Aaddr, mrel A' moc' mo' ->
    MP mo' /\ MINV mo' /\ OTHER mo0 mo' /\
    (exists p, snd r = Some p /\ ACCT (Z_to_bv 64 (bv_unsigned aw - chg)) L RNG' (fst r) (HB p Aaddr n :: LBa) mo')
    /\ (64512 < n -> aprist st -> aprist (fst r)).

Lemma acct_some_leaf : forall mo aw L st LBa n chg RESV A r RNG' A' moc',
  MP mo ->
  aresv_ok L RESV -> FPX L (fp_ok (m_vm_lazy (canon mo)) A) -> FIXZ L (canon mo) -> TIE st LBa ->
  0 <= chg <= bv_unsigned aw ->
  (malloc_leaf NMAX RESV SHFIX (bv_unsigned aw) n st (canon mo) (fp_ok (m_vm_lazy (canon mo)) A) r RNG' A' moc' /\ snd r <> None) ->
  (forall p, snd r = Some p -> ACCTc NMAX RESV SHFIX (bv_unsigned aw - (if is_primary n then 0 else n)) RNG' A' (fst r) moc' ->
             ACCTc NMAX RESV SHFIX (bv_unsigned aw - chg) RNG' A' (fst r) moc') ->
  acct_leaf_some mo aw L st LBa n chg r RNG' A' moc'.
Proof.
  intros mo aw L st LBa n chg RESV A r RNG' A' moc' HMP RK FX FZ TI CB [(HH & HFL & CK & HLEAF) NN] WK mo' Aaddr MR.
  destruct (leaf_actual L mo A' moc' mo' HH MR HMP FZ) as (M1 & M2 & M3 & EC).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
  split. 2:{ intros Hn64 PR. exact (aprist_keep n st (fst r) Hn64 CK PR). }
  destruct MR as (_ & _ & ND' & AL').
  pose proof (bv_unsigned_in_range 64 aw) as RA. unfold bv_modulus in RA.
  destruct (snd r) as [p|] eqn:Esnd; [| exfalso; exact (NN eq_refl)].
  destruct HLEAF as (-> & FRESH & (ch & ELIVE & ESZ) & HC').
  exists (a_next st). split; [reflexivity|].
  exists RESV, A'. rewrite EC, Z_to_bv_unsigned, (bv_wrap_small 64 (bv_unsigned aw - chg)) by (unfold bv_modulus; lia).
  split; [exact RK|]. split; [exact (WK _ eq_refl HC')|]. split; [exact ND'|]. split; [exact AL'|]. split; [exact (FPX_mono _ _ _ HFL FX)|]. split; [exact (FIXZ_vmh _ _ _ HH FZ)|].
  intros id ch' Hl. rewrite ELIVE in Hl. apply lookup_insert_Some in Hl as [[<- <-]|[NE Hl]].
  + exists Aaddr. left. rewrite ESZ. reflexivity.
  + destruct (TI id ch' Hl) as (Ad & Hin). exists Ad. right. exact Hin.
Qed.

Theorem ACCT_malloc_some_sec : forall aw L RNG st LBa mo n,
  ACCT aw L RNG st LBa mo -> MP mo -> MINV mo ->
  64512 < n <= 2^28 -> n <= bv_unsigned aw -> CRED0 - 2^30 <= bv_unsigned aw -> c24count LBa <= 255 ->
  exists RESV A moc, aresv_ok L RESV /\ c6ok RESV RNG st /\ mrel A moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A (aembed ATOP (amalloc ATOP RESV st n)) moc (acct_leaf_some mo aw L st LBa n n).
Proof.
  intros aw L RNG st LBa mo n HACC HMP HMI Hn Hnv Hcl H24.
  pose proof HACC as (RESV & A & RK & HC & ND & AL & FX & FZ & TI).
  exists RESV, A, (canon mo). split; [exact RK|]. split; [exact (ACCTc_c6 _ _ _ _ _ _ HC)|]. split; [apply mrel_canon; assumption|].
  split; [exact (minvA_canon _ _ _ _ _ _ HACC)|]. split; [exact (proj1 (proj2 (proj2 FZ)))|].
  apply TS_twfS.
  assert (H24' : size_of_class K_BATCH_CLASS * (cntP K_BATCH_CLASS (live_chunks st) + 1) <= L24MAX).
  { pose proof (c24_live_le _ _ _ _ _ _ _ HC TI). assert (S24 : size_of_class K_BATCH_CLASS = 8192) by reflexivity. rewrite S24. unfold L24MAX. lia. }
  pose proof HC as (_ & _ & _ & ER & _).
  eapply TS_mono; [apply (U_malloc_nn_sec NMAX HLIM RESV SHFIX (bv_unsigned aw) RNG A st (canon mo) n HC Hn Hnv Hcl H24')|].
  intros r RNG' A' moc' _ HL. rewrite ER in FX, HL.
  apply (acct_some_leaf mo aw L st LBa n n RESV A r RNG' A' moc' HMP RK FX FZ TI ltac:(lia) HL).
  intros p Hp X. rewrite (large_not_primary n) in X by lia. exact X.
Qed.

Theorem ACCT_malloc_some_prim : forall aw L RNG st LBa mo n,
  ACCT aw L RNG st LBa mo -> MP mo -> MINV mo ->
  1 <= n <= 64512 -> C_EXH <= bv_unsigned aw -> c24count LBa <= 255 -> aprist st ->
  exists RESV A moc, aresv_ok L RESV /\ c6ok RESV RNG st /\ mrel A moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A (aembed ATOP (amalloc ATOP RESV st n)) moc (acct_leaf_some mo aw L st LBa n 0).
Proof.
  intros aw L RNG st LBa mo n HACC HMP HMI Hn Hcx H24 PR.
  pose proof HACC as (RESV & A & RK & HC & ND & AL & FX & FZ & TI).
  exists RESV, A, (canon mo). split; [exact RK|]. split; [exact (ACCTc_c6 _ _ _ _ _ _ HC)|]. split; [apply mrel_canon; assumption|].
  split; [exact (minvA_canon _ _ _ _ _ _ HACC)|]. split; [exact (proj1 (proj2 (proj2 FZ)))|].
  apply TS_twfS.
  assert (H24' : size_of_class K_BATCH_CLASS * (cntP K_BATCH_CLASS (live_chunks st) + 1) <= L24MAX).
  { pose proof (c24_live_le _ _ _ _ _ _ _ HC TI). assert (S24 : size_of_class K_BATCH_CLASS = 8192) by reflexivity. rewrite S24. unfold L24MAX. lia. }
  pose proof HC as (_ & _ & _ & ER & _).
  pose proof (bv_unsigned_in_range 64 aw) as RA. unfold bv_modulus in RA.
  eapply TS_mono; [apply (U_malloc_nn_prim NMAX HLIM RESV SHFIX (bv_unsigned aw) RNG A st (canon mo) n HC Hn Hcx H24')|].
  { intros c Hc Hc24. exact (proj2 (PR c ltac:(lia) Hc24)). }
  intros r RNG' A' moc' _ HL. rewrite ER in FX, HL.
  apply (acct_some_leaf mo aw L st LBa n 0 RESV A r RNG' A' moc' HMP RK FX FZ TI ltac:(lia) HL).
  intros p Hp X. assert (EP : is_primary n = true) by (rewrite is_primary_iff by lia; apply Z.leb_le; lia). rewrite EP in X.
  apply (ACCTc_weaken NMAX RESV SHFIX (bv_unsigned aw - 0)); [exact X| lia].
Qed.

Lemma In_lb_remove_ne : forall p LB b, In b LB -> ab_kind b <> ABHeap p -> In b (lb_remove p LB).
Proof.
  intros p LB b H1 H2. unfold lb_remove. apply list_elem_of_In. apply list_elem_of_filter. split; [| apply list_elem_of_In; exact H1].
  destruct (ab_kind b) as [q|c]; cbn; [| exact I]. destruct (N.eqb_spec q p) as [->|NE]; [exfalso; apply H2; reflexivity| exact I].
Qed.

Definition acct_leaf_free (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock) (p : aptr)
    (r : astate) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ MINV mo' /\ OTHER mo0 mo' /\ ACCT aw L RNG' r (lb_remove p LBa) mo'
    /\ (aprist st -> aprist r).

Theorem ACCT_free : forall aw L RNG st LBa mo p ch,
  ACCT aw L RNG st LBa mo -> MP mo -> MINV mo -> (a_live st) !! p = Some ch ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (aembed ATOP (afree st (Some p))) moc (acct_leaf_free mo aw L st LBa p).
Proof.
  intros aw L RNG st LBa mo p ch HACC HMP HMI Hl.
  pose proof HACC as (RESV & A & RK & HC & ND & AL & FX & FZ & TI).
  exists A, (canon mo). split; [apply mrel_canon; assumption|].
  split; [exact (minvA_canon _ _ _ _ _ _ HACC)|]. split; [exact (proj1 (proj2 (proj2 FZ)))|].
  apply TS_twfS.
  eapply TS_mono; [apply (U_free NMAX HLIM RESV SHFIX (bv_unsigned aw) RNG A st (canon mo) p ch HC Hl)|].
  intros st' RNG' A' moc' _ (HH & HFL & ELIVE & _ & CK & HC') mo' MR.
  destruct (leaf_actual L mo A' moc' mo' HH MR HMP FZ) as (M1 & M2 & M3 & EC).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
  split. 2:{ intros PR. exact (aprist_keep 64513 st st' ltac:(lia) (fun _ => CK) PR). }
  destruct MR as (_ & _ & ND' & AL').
  exists RESV, A'. rewrite EC. split; [exact RK|]. split; [exact HC'|]. split; [exact ND'|]. split; [exact AL'|]. split; [exact (FPX_mono _ _ _ HFL FX)|]. split; [exact (FIXZ_vmh _ _ _ HH FZ)|].
  intros id ch' Hl'. rewrite ELIVE in Hl'. apply lookup_delete_Some in Hl' as [NE Hl'].
  destruct (TI id ch' Hl') as (Ad & Hin). exists Ad. apply In_lb_remove_ne; [exact Hin|]. cbn [ab_kind]. congruence.
Qed.

Definition acct_leaf_realloc (mo0 : Model) (aw : word) (L : alayout) (LBa : list ablock) (p : aptr) (n chg : Z)
    (r : astate * option aptr) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo' Aaddr, mrel A' moc' mo' ->
    MP mo' /\ MINV mo' /\ OTHER mo0 mo' /\
    match snd r with
    | Some q => ACCT (Z_to_bv 64 (bv_unsigned aw - chg)) L RNG' (fst r) (HB q Aaddr n :: lb_remove p LBa) mo'
    | None => ACCT (Z_to_bv 64 (bv_unsigned aw - C_EXH)) L RNG' (fst r) LBa mo'
    end.

Theorem ACCT_realloc : forall aw L RNG st LBa mo p chp n chg,
  ACCT aw L RNG st LBa mo -> MP mo -> MINV mo -> (a_live st) !! p = Some chp ->
  1 <= n <= AREQMAX -> ((chg = 0 /\ n <= 64512) \/ (chg = n /\ n <= bv_unsigned aw)) -> C_EXH <= bv_unsigned aw -> c24count LBa <= 255 ->
  exists RESV A0 moc, aresv_ok L RESV /\ c6ok RESV RNG st /\ mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (aembed ATOP (arealloc_m RESV st p n)) moc (acct_leaf_realloc mo aw L LBa p n chg).
Proof.
  intros aw L RNG st LBa mo p chp n chg HACC HMP HMI Hp Hn HCHG Hcx H24.
  pose proof HACC as (RESV & A & RK & HC & ND & AL & FX & FZ & TI).
  assert (HNV : is_primary n = false -> n <= bv_unsigned aw).
  { intros NP. destruct HCHG as [[_ H]|[_ H]]; [| exact H]. rewrite is_primary_iff in NP by lia. apply Z.leb_gt in NP. lia. }
  exists RESV, A, (canon mo). split; [exact RK|]. split; [exact (ACCTc_c6 _ _ _ _ _ _ HC)|]. split; [apply mrel_canon; assumption|].
  split; [exact (minvA_canon _ _ _ _ _ _ HACC)|]. split; [exact (proj1 (proj2 (proj2 FZ)))|].
  apply TS_twfS.
  assert (H24' : size_of_class K_BATCH_CLASS * (cntP K_BATCH_CLASS (live_chunks st) + 1) <= L24MAX).
  { pose proof (c24_live_le _ _ _ _ _ _ _ HC TI). assert (S24 : size_of_class K_BATCH_CLASS = 8192) by reflexivity. rewrite S24. unfold L24MAX. lia. }
  eapply TS_mono; [apply (U_realloc NMAX HLIM RESV SHFIX (bv_unsigned aw) RNG A st (canon mo) p chp n HC Hp Hn HNV Hcx H24')|].
  intros r RNG' A' moc' _ (HH & HFL & HLEAF) mo' Aaddr MR.
  destruct (leaf_actual L mo A' moc' mo' HH MR HMP FZ) as (M1 & M2 & M3 & EC).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
  destruct MR as (_ & _ & ND' & AL').
  pose proof (bv_unsigned_in_range 64 aw) as RA. unfold bv_modulus in RA.
  destruct (snd r) as [q|] eqn:Esnd.
  - destruct HLEAF as (-> & FRESH & (ch & ELIVE & ESZ) & HC').
    assert (HC'' : ACCTc NMAX RESV SHFIX (bv_unsigned aw - chg) RNG' A' (fst r) moc').
    { destruct HCHG as [[-> H]|[-> H]].
      - rewrite is_primary_iff in HC' by lia. rewrite (proj2 (Z.leb_le n 64512) H) in HC'. exact HC'.
      - destruct (is_primary n); [| exact HC']. apply (ACCTc_weaken NMAX RESV SHFIX (bv_unsigned aw - 0)); [exact HC'| lia]. }
    assert (CB : 0 <= chg <= bv_unsigned aw) by (destruct HCHG as [[-> _]|[-> H]]; lia).
    exists RESV, A'. rewrite EC, Z_to_bv_unsigned, (bv_wrap_small 64 (bv_unsigned aw - chg)) by (unfold bv_modulus; lia).
    split; [exact RK|]. split; [exact HC''|]. split; [exact ND'|]. split; [exact AL'|]. split; [exact (FPX_mono _ _ _ HFL FX)|]. split; [exact (FIXZ_vmh _ _ _ HH FZ)|].
    intros id ch' Hl. rewrite ELIVE in Hl. apply lookup_delete_Some in Hl as [NEp Hl]. apply lookup_insert_Some in Hl as [[<- <-]|[NE Hl]].
    + exists Aaddr. left. rewrite ESZ. reflexivity.
    + destruct (TI id ch' Hl) as (Ad & Hin). exists Ad. right. apply In_lb_remove_ne; [exact Hin|]. cbn [ab_kind]. congruence.
  - destruct HLEAF as (ELIVE & HC').
    exists RESV, A'. rewrite EC, Z_to_bv_unsigned, (bv_wrap_small 64 (bv_unsigned aw - C_EXH)) by (unfold bv_modulus, C_EXH in *; lia).
    split; [exact RK|]. split; [exact HC'|]. split; [exact ND'|]. split; [exact AL'|]. split; [exact (FPX_mono _ _ _ HFL FX)|]. split; [exact (FIXZ_vmh _ _ _ HH FZ)|].
    intros id ch' Hl. rewrite ELIVE in Hl. exact (TI id ch' Hl).
Qed.

Definition acct_leaf_keep (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa' : list ablock)
    (_ : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ MINV mo' /\ OTHER mo0 mo' /\ ACCT aw L RNG' st LBa' mo'.

Theorem ACCT_keep : forall aw L RNG st LBa LBa' mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  (forall id Aaddr n, In (HB id Aaddr n) LBa -> In (HB id Aaddr n) LBa') ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Ok tt)) moc (acct_leaf_keep mo aw L st LBa').
Proof.
  intros aw L RNG st LBa LBa' mo HACC HMP SUB.
  pose proof HACC as (RESV & A & RK & HC & ND & AL & FX & FZ & TI).
  exists A, (canon mo). split; [apply mrel_canon; assumption|].
  split; [exact (minvA_canon _ _ _ _ _ _ HACC)|]. split; [exact (proj1 (proj2 (proj2 FZ)))|].
  cbn. split; [exact (ACCTc_acct_ok _ _ _ _ _ _ HC)|].
  intros mo' MR. destruct (leaf_actual L mo A (canon mo) mo' (vmh_refl _) MR HMP FZ) as (M1 & M2 & M3 & EC).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
  destruct MR as (_ & _ & ND' & AL').
  exists RESV, A. rewrite EC. split; [exact RK|]. split; [exact HC|]. split; [exact ND'|]. split; [exact AL'|]. split; [exact FX|]. split; [exact FZ|].
  intros id ch' Hl'. destruct (TI id ch' Hl') as (Ad & Hin). exists Ad. apply SUB. exact Hin.
Qed.

Definition acct_leaf_silent (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock)
    (r : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ MINV mo' /\ OTHER mo0 mo' /\ ACCT aw L RNG' st LBa mo'.
Theorem ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Ok tt)) moc (acct_leaf_silent mo aw L st LBa).
Proof. intros aw L RNG st LBa mo HACC HMP. exact (ACCT_keep aw L RNG st LBa LBa mo HACC HMP (fun _ _ _ H => H)). Qed.

Definition acct_leaf_frame_in (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock)
    (r : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ MINV mo' /\ OTHER mo0 mo' /\
    forall c F n LBk, (forall id Aaddr sz, In (HB id Aaddr sz) LBa -> In (HB id Aaddr sz) LBk) -> ACCT aw L RNG' st (mkABlock (ABFake c) F n :: LBk) mo'.
Theorem ACCT_frame_in : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Ok tt)) moc (acct_leaf_frame_in mo aw L st LBa).
Proof.
  intros aw L RNG st LBa mo HACC HMP.
  pose proof HACC as (RESV & A & RK & HC & ND & AL & FX & FZ & TI).
  exists A, (canon mo). split; [apply mrel_canon; assumption|].
  split; [exact (minvA_canon _ _ _ _ _ _ HACC)|]. split; [exact (proj1 (proj2 (proj2 FZ)))|].
  cbn. split; [exact (ACCTc_acct_ok _ _ _ _ _ _ HC)|].
  intros mo' MR. destruct (leaf_actual L mo A (canon mo) mo' (vmh_refl _) MR HMP FZ) as (M1 & M2 & M3 & EC).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. intros c F n LBk SUB.
  destruct MR as (_ & _ & ND' & AL').
  exists RESV, A. rewrite EC. split; [exact RK|]. split; [exact HC|]. split; [exact ND'|]. split; [exact AL'|]. split; [exact FX|]. split; [exact FZ|].
  intros id ch' Hl'. destruct (TI id ch' Hl') as (Ad & Hin). exists Ad. right. apply SUB. exact Hin.
Qed.

Definition acct_leaf_keep_any (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock)
    (r : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ MINV mo' /\ OTHER mo0 mo' /\
    forall LBk, (forall id Aaddr sz, In (HB id Aaddr sz) LBa -> In (HB id Aaddr sz) LBk) -> ACCT aw L RNG' st LBk mo'.
Theorem ACCT_keep_any : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Ok tt)) moc (acct_leaf_keep_any mo aw L st LBa).
Proof.
  intros aw L RNG st LBa mo HACC HMP.
  pose proof HACC as (RESV & A & RK & HC & ND & AL & FX & FZ & TI).
  exists A, (canon mo). split; [apply mrel_canon; assumption|].
  split; [exact (minvA_canon _ _ _ _ _ _ HACC)|]. split; [exact (proj1 (proj2 (proj2 FZ)))|].
  cbn. split; [exact (ACCTc_acct_ok _ _ _ _ _ _ HC)|].
  intros mo' MR. destruct (leaf_actual L mo A (canon mo) mo' (vmh_refl _) MR HMP FZ) as (M1 & M2 & M3 & EC).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. intros LBk SUB.
  destruct MR as (_ & _ & ND' & AL').
  exists RESV, A. rewrite EC. split; [exact RK|]. split; [exact HC|]. split; [exact ND'|]. split; [exact AL'|]. split; [exact FX|]. split; [exact FZ|].
  intros id ch' Hl'. destruct (TI id ch' Hl') as (Ad & Hin). exists Ad. apply SUB. exact Hin.
Qed.

Variable ISF : ablock -> Prop.
Variable DEL : ablock -> list ablock -> list ablock.
Hypothesis DEL_In : forall b LBa x, In x (DEL b LBa) <-> In x LBa /\ x <> b.
Hypothesis ISF_heap : forall id Aaddr sz, ~ ISF (HB id Aaddr sz).
Definition acct_leaf_frame_out (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock)
    (r : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ MINV mo' /\ OTHER mo0 mo' /\
    forall fb, In fb LBa -> ISF fb -> ACCT aw L RNG' st (DEL fb LBa) mo'.
Theorem ACCT_frame_out : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Ok tt)) moc (acct_leaf_frame_out mo aw L st LBa).
Proof.
  intros aw L RNG st LBa mo HACC HMP.
  destruct (ACCT_keep_any aw L RNG st LBa mo HACC HMP) as (A0 & moc & MR & MV & HH & TW). exists A0, moc.
  split; [exact MR|]. split; [exact MV|]. split; [exact HH|]. cbn in TW |- *. destruct TW as [ACC HL]. split; [exact ACC|].
  intros mo' MR'. destruct (HL mo' MR') as (M1 & M2 & M3 & HK). split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
  intros fb Hfb FK. apply HK. intros id Aaddr sz Hin. apply DEL_In. split; [exact Hin|].
  intros E. rewrite <- E in FK. exact (ISF_heap id Aaddr sz FK).
Qed.

Theorem ACCT_cov_sh : forall aw L RNG st LBa mo z, ACCT aw L RNG st LBa mo -> SHFIX (page_base_of z) ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVPb mo (page_base_of z).
Proof. intros. right. right. assumption. Qed.

Variable AI : AMallocIface2.

Hypothesis AI_arena : arena_law (AHEAP AI).

Hypothesis AI_fake_area : forall L RNG st LBa m c F n, AHEAP AI L RNG st LBa m -> In (mkABlock (ABFake c) F n) LBa ->
  al_fake L <= F /\ F + n <= al_fake L + 11571200 /\ F mod 8 = 0 /\ n mod 8 = 0 /\ ablk F (F + n).

Theorem ACCT_cov : forall aw L RNG st LBa m mo b z, ACCT aw L RNG st LBa mo -> AHEAP AI L RNG st LBa m -> In b LBa ->
  (ab_addr b <= z < ab_addr b + ab_size b \/ shad (ab_addr b) <= z < shad (ab_addr b) + shlen (ab_size b + 7)) ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVPb mo (page_base_of z).
Proof.
  intros aw L RNG st LBa m mo b z (RESV & A & RK & HC & ND & AL & FX & FZ & TI) AH Hb Hz.
  change (m_vm_lazy mo) with (m_vm_lazy (canon mo)).
  destruct HC as ([HA HM] & _). pose proof atop_range as ATR.
  pose proof (AMI_atop _ _ _ HM) as [[T1 T2] _]. unfold ACEIL, ATOP_MAX in T1, T2.

  assert (SHC : forall X len, (exists e, In e (vm_maps (m_vmmaps (canon mo))) /\ B e <= X /\ X + len <= B e + S e) ->
                 (X + len <= LS_LO \/ KHIGH <= X) -> X mod 8 = 0 -> 0 <= X -> 0 <= len ->
                 shad X <= z < shad X + shlen len -> COVP (canon mo) (page_base_of z)).
  { intros X len (e & He & E1 & E2) APP X8 X0 L0 Hzz. unfold shad, shlen in Hzz. rewrite !Z.shiftr_div_pow2 in Hzz by lia. change (2 ^ 3) with 8 in Hzz.
    exists e, (8 * (z - ASHOFF)). split; [exact He|].
    split; [Z.div_mod_to_equations; lia|]. split; [unfold appz; Z.div_mod_to_equations; lia|].
    f_equal. unfold shad. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
  destruct (AI_block_bounds AI L RNG st LBa m b AH Hb) as (BB1 & BB2 & BB3). unfold ABase.AIMG_HI in BB1.
  destruct b as [[p|c] Ab n]; cbn [ab_addr ab_size] in *.
  -
    destruct (AI_block AI L RNG st LBa m p Ab n AH Hb) as (N & BR & _ & _ & _ & _ & (ch & LV & SZ & SEC) & _).
    destruct BR as (BK & N0 & TOP & A16).
    pose proof HA as (HCLS & HW & _).
    assert (INL : In ch (live_chunks st)).
    { unfold live_chunks. apply in_map_iff. exists (p, ch). split; [reflexivity|]. apply list_elem_of_In. apply elem_of_map_to_list. exact LV. }
    assert (Hwf : chunk_wf ATOP ch).
    { unfold all_chunks in HW. cbn [app] in HW. apply Forall_app in HW as [HW _]. exact (proj1 (Forall_forall _ _) HW ch INL). }
    destruct (is_primary n) eqn:PR.
    +
      destruct (AI_arena L RNG st LBa m p Ab n AH Hb PR) as (c & Hc & R1 & R2).
      pose proof (HCLS c Hc) as (C1 & C2 & C3 & _). cbv zeta in C1, C2, C3.
      pose proof (AI_layout AI L RNG st LBa m AH) as (_ & _ & _ & _ & SBE & _).
      destruct Hz as [Hz|Hz].
      * left. apply lazy_page_false; [lia|]. apply (AMI_lazy_committed _ st (canon mo) z HM).
        exists c. split; [exact Hc|]. unfold region_beg. rewrite SBE. lia.
      * right. left. destruct (AMI_arena_entry _ st (canon mo) HM) as (e & He & E1 & E2 & E3).
        apply (SHC Ab (n + 7)); [| right; rewrite SBE in *; unfold K_REGION in *; lia| clear -A16; Z.div_mod_to_equations; lia| lia| lia| exact Hz].
        exists e. split; [exact He|]. rewrite SBE in *. unfold K_REGION, K_FREEARR_OFF in *. lia.
    +
      specialize (SEC eq_refl). destruct ch as [c0 n0|mb ms n0]; cbn [chunk_size] in SZ; subst n0.
      { exfalso. cbn in Hwf. destruct Hwf as [Hn _]. rewrite is_primary_iff in PR by lia. apply Z.leb_gt in PR. lia. }
      cbn in Hwf. destruct Hwf as (Hn & -> & MB4 & MB0 & PLACE). cbn [chunk_user_beg] in SEC.
      pose proof (sec_map_size_ge n ltac:(lia)) as SG.
      assert (RZ : rz_size n = 2048) by (unfold rz_size, rz_log; repeat (rewrite (proj2 (Z.leb_gt _ _)) by lia); reflexivity).
      unfold PG in SEC. rewrite RZ in SEC.
      assert (INC : In (mb, sec_map_size n) (CHX [] [] st)).
      { unfold CHX, CH, all_chunks. cbn [app]. apply in_or_app. left. rewrite secs_app. apply in_or_app. left. unfold secs. apply in_flat_map.
        exists (CSec mb (sec_map_size n) n). split; [exact INL| left; reflexivity]. }
      destruct Hz as [Hz|Hz].
      * left. apply lazy_page_false; [lia|]. apply (AMI_lazy_ch _ st (canon mo) mb (sec_map_size n) z HM INC); unfold LS_LO in *; lia.
      * right. left. apply (SHC Ab (n + 7)); [| unfold LS_LO, KHIGH in *; lia| clear -A16; Z.div_mod_to_equations; lia| lia| lia| exact Hz].
        exists (went (mb, sec_map_size n)). split; [exact (AMI_ch_entry _ st (canon mo) mb (sec_map_size n) HM INC)|].
        unfold went, B, S. cbn [fst snd]. unfold LS_LO in *. rewrite !unsigned_lit by lia. lia.
  -
    destruct (AI_fake_area L RNG st LBa m c Ab n AH Hb) as (F1 & F2 & F8 & N8 & BK).
    destruct FZ as (RLO & NLZ & _).
    destruct Hz as [Hz|Hz].
    + left. apply NLZ. lia.
    + right. left. destruct RK as (_ & _ & _ & _ & _ & _ & _ & _ & RFK & _).
      assert (BKL : Ab + n <= LS_LO \/ KHIGH <= Ab) by (unfold ablk, KLS, LS_LO, KHIGH in *; lia).

      unfold shad, shlen in Hz. rewrite !Z.shiftr_div_pow2 in Hz by lia. change (2 ^ 3) with 8 in Hz.
      set (x := 8 * (z - ASHOFF)).
      assert (Hx : Ab <= x < Ab + n) by (unfold x; Z.div_mod_to_equations; lia).
      destruct (RFK x ltac:(lia)) as (iv & Hiv & Hxi).
      destruct (AMI_resv_entry _ st (canon mo) iv HM Hiv) as [(e & He & E1 & E2)|(e & He & E1 & E2)].
      * exfalso. pose proof (proj1 (Forall_forall _ _) RLO e He) as X. cbv beta in X. unfold B, S, ABase.AIMG_HI in *. lia.
      * exists e, x. split; [exact He|]. split; [lia|]. split; [unfold appz; lia|].
        f_equal. unfold x, shad. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia.
Qed.

End Acct.

Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ModelX OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.MmXfer OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrlProps OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanInv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanBudget OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanTotalCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanNodeSem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanTotal OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanFree.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS.BackingAlgebra.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB AMalloc_iface2.TwinB AArenaLaw.TwinB ATsafeCore.TwinB ATsafeEv.TwinB ATsafeAlloc.TwinB ATsafeOps.TwinB.
Import AEmbRep.TwinB AEmbFrame.TwinB APristLaw.TwinB.
Import AFake_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import Adeq.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Unset Lia Cache.

Section Acct.
Context {rc : runConstT}.
Variable NMAX : nat.
Hypothesis HLIM : NLK0 + Z.of_nat NMAX * 4096 <= LIMIT.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAX) fstepS NMAX).

Lemma TS_twfS : forall {R} (t : itree node (exc R)) RNG A mo P, TS NMAX RNG A t mo P -> twfS RNG A t mo P.
Proof.
  intros R t. induction t as [[|r]|n k IH]; intros RNG A mo P H; cbn in H |- *.
  - exact H.
  - exact H.
  - destruct H as (HA & HS & HX & HK). split; [exact HA|]. split; [exact HS|]. split; [exact HX|].
    intros rsp mo' evs Hst. destruct (HK rsp mo' evs Hst) as (E & RNG' & A' & HF & HL & HT).
    split; [exact E|]. exists RNG', A'. split; [exact HF|]. split; [exact HL|]. apply IH. exact HT.
Qed.

Lemma canon_of_mrel : forall A moc mo, mrel A moc mo -> canon mo = moc.
Proof.
  intros A moc mo (SB & CAN & _). unfold same_but_mat in SB. rewrite SB. clear SB.
  destruct moc as [fd [mp lzz mt] io fs pr lm tm]. cbn in CAN. subst mt. reflexivity.
Qed.

Lemma canon_same_but_mat : forall mo mo', same_but_mat mo mo' -> canon mo' = canon mo.
Proof.
  intros mo mo' SB. unfold same_but_mat in SB. rewrite SB. clear SB.
  destruct mo as [fd [mp lzz mt] io fs pr lm tm]. reflexivity.
Qed.

Definition acct_rel (mo mo' : Model) : Prop := vmh (canon mo) (canon mo').
Lemma acct_rel_refl : forall mo, acct_rel mo mo. Proof. intros. apply vmh_refl. Qed.
Lemma acct_rel_mat : forall mo mo', same_but_mat mo mo' -> acct_rel mo mo'.
Proof. intros mo mo' SB. unfold acct_rel. rewrite (canon_same_but_mat _ _ SB). apply vmh_refl. Qed.

Variable MP : Model -> Prop.
Variable MINV : Model -> Prop.
Variable OTHER : Model -> Model -> Prop.
Hypothesis MP_rel : forall mo mo', MP mo -> acct_rel mo mo' -> MP mo'.
Hypothesis OTHER_rel : forall mo mo', acct_rel mo mo' -> OTHER mo mo'.

Definition C0A (a : Z) : Prop := (0x10000 <= a < ABase.TwinB.AIMG_HI) \/ (ATOP <= a < 18446744073709551616).

Definition lazy_shapeA (C0 : Z -> Prop) (mo : Model) : Prop := forall z, C0 z -> page_in_ranges (page_base_of z) (m_vm_lazy mo) = false.
Hypothesis MINV_intro : forall mo, m_halted mo = None -> lazy_shapeA C0A mo -> MINV mo.

Lemma acct_rel_fs : forall mo mo', acct_rel mo mo' -> m_fs mo' = m_fs mo.
Proof.
  intros mo mo' ((_ & _ & FS & _) & _). destruct mo as [fd [mp lzz mt] io fs pr lm tm], mo' as [fd' [mp' lzz' mt'] io' fs' pr' lm' tm'].
  cbn in FS |- *. unfold m_fs. cbn. rewrite FS. reflexivity.
Qed.
Lemma acct_rel_fds : forall mo mo', acct_rel mo mo' -> m_fds mo' = m_fds mo.
Proof.
  intros mo mo' ((FD & _) & _). destruct mo as [fd [mp lzz mt] io fs pr lm tm], mo' as [fd' [mp' lzz' mt'] io' fs' pr' lm' tm'].
  cbn in FD |- *. unfold m_fds. cbn. rewrite FD. reflexivity.
Qed.
Lemma acct_rel_halted : forall mo mo', acct_rel mo mo' -> m_halted mo' = m_halted mo.
Proof.
  intros mo mo' ((_ & _ & _ & PR & _) & _). destruct mo as [fd [mp lzz mt] io fs pr lm tm], mo' as [fd' [mp' lzz' mt'] io' fs' pr' lm' tm'].
  cbn in PR |- *. unfold m_halted. cbn. rewrite PR. reflexivity.
Qed.
Lemma acct_rel_lazy : forall mo mo' p, acct_rel mo mo' -> page_in_ranges p (m_vm_lazy mo') = true -> page_in_ranges p (m_vm_lazy mo) = true.
Proof.
  intros mo mo' p (_ & _ & LZ) H. destruct mo as [fd [mp lzz mt] io fs pr lm tm], mo' as [fd' [mp' lzz' mt'] io' fs' pr' lm' tm'].
  cbn in LZ, H |- *. exact (LZ p H).
Qed.

Lemma asan_minv_rel : forall (C0 : Z -> Prop) mo mo', (m_halted mo = None /\ lazy_shapeA C0 mo) -> acct_rel mo mo' ->
  m_halted mo' = None /\ lazy_shapeA C0 mo'.
Proof.
  intros C0 mo mo' [HH LS] AR. split; [rewrite (acct_rel_halted _ _ AR); exact HH|].
  intros z Hz. destruct (page_in_ranges (page_base_of z) (m_vm_lazy mo')) eqn:E; [| reflexivity].
  specialize (LS z Hz). rewrite (acct_rel_lazy _ _ _ AR E) in LS. discriminate LS.
Qed.

Definition FPX (L : alayout) (RNG : footprint) : Prop :=
  rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)) /\ rng RNG 0x10000 0x621000 /\ rng RNG 0x7fffa000 0xc5000
  /\ rng RNG (shad ATOP) (Shadow.KHIGH - shad ATOP) /\ afake_rng L RNG.
Lemma rng_fp_mono : forall R R' lo n, fp_le R R' -> rng R lo n -> rng R' lo n.
Proof. intros R R' lo n LE (R1 & R2 & R3). split; [exact R1|]. split; [exact R2|]. intros b j Hb Hj. apply LE. apply R3; assumption. Qed.
Lemma FPX_mono : forall L R R', fp_le R R' -> FPX L R -> FPX L R'.
Proof.
  intros L R R' LE (F1 & F2 & F3 & F4 & F5). repeat (split; [eapply rng_fp_mono; [exact LE|]; assumption|]). exact (afake_rng_mono L R R' LE F5).
Qed.

Definition TIE (st : astate) (LBa : list ablock) : Prop :=
  forall id ch, (a_live st) !! id = Some ch -> exists Aaddr, In (HB id Aaddr (chunk_size ch)) LBa.

Variable SHFIX : word -> Prop.

Definition FIXZ (L : alayout) (moc : Model) : Prop :=
  Forall (fun e : word * word => bv_unsigned (fst e) + bv_unsigned (snd e) <= ABase.TwinB.AIMG_HI) (vm_reserved (m_vmmaps moc))
  /\ (forall z, al_fake L <= z < al_fake L + 11571200 -> page_in_ranges (page_base_of z) (m_vm_lazy moc) = false)
  /\ m_halted moc = None
  /\ lazy_shapeA C0A moc.
Lemma FIXZ_vmh : forall L mo mo', vmh mo mo' -> FIXZ L mo -> FIXZ L mo'.
Proof.
  intros L mo mo' ((_ & _ & _ & PR & _) & ER & LZ) (F1 & F2 & F3 & F4). split; [rewrite ER; exact F1|]. split; [| split].
  - intros z Hz. destruct (page_in_ranges (page_base_of z) (m_vm_lazy mo')) eqn:E; [| reflexivity].
    specialize (F2 z Hz). rewrite (LZ _ E) in F2. discriminate.
  - revert F3 PR. destruct mo as [fd [mp lzz mt] io fs pr lm tm], mo' as [fd' [mp' lzz' mt'] io' fs' pr' lm' tm'].
    unfold m_halted. cbn. intros F3 ->. exact F3.
  - intros z Hz. destruct (page_in_ranges (page_base_of z) (m_vm_lazy mo')) eqn:E; [| reflexivity].
    specialize (F4 z Hz). rewrite (LZ _ E) in F4. discriminate.
Qed.

Lemma MINV_of_FIXZ : forall L mo, FIXZ L (canon mo) -> MINV mo.
Proof.
  intros L mo (_ & _ & F3 & F4). apply MINV_intro.
  - revert F3. destruct mo as [fd [mp lzz mt] io fs pr lm tm]. exact (fun H => H).
  - revert F4. destruct mo as [fd [mp lzz mt] io fs pr lm tm]. exact (fun H => H).
Qed.

Definition ACCT (aw : word) (L : alayout) (RNG : footprint) (st : astate) (LBa : list ablock) (mo : Model) : Prop :=
  exists RESV A,
    aresv_ok L RESV
    /\ ACCTc NMAX RESV SHFIX (bv_unsigned aw) RNG A st (canon mo)
    /\ List.NoDup (m_vm_materialized mo) /\ (forall p, In p (m_vm_materialized mo) -> A p)
    /\ FPX L RNG
    /\ FIXZ L (canon mo)
    /\ TIE st LBa.

Definition COVPb (mo : Model) (p : word) : Prop := COVP (canon mo) p \/ SHFIX p.

Lemma ACCT_mrel : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo ->
  exists RESV A, aresv_ok L RESV /\ ACCTc NMAX RESV SHFIX (bv_unsigned aw) RNG A st (canon mo) /\ mrel A (canon mo) mo.
Proof.
  intros aw L RNG st LBa mo (RESV & A & RK & HC & ND & AL & _). exists RESV, A. split; [exact RK|]. split; [exact HC|].
  apply mrel_canon; assumption.
Qed.

Lemma ACCTc_acct_ok : forall RESV v RNG A st mo, ACCTc NMAX RESV SHFIX v RNG A st mo -> acct_ok NMAX RNG A mo.
Proof.
  intros RESV v RNG A st mo HC. destruct (KI_entry NMAX RESV SHFIX v RNG A st mo 0 HC ltac:(lia)) as (k & HK & HP & HL).
  pose proof HC as (_ & _ & _ & -> & Hv & _). pose proof (GP_nonneg st (LW_emb _ _ _ HL)).
  eapply KI_acct_ok; [exact HLIM| exact HK| lia].
Qed.

Theorem ACCT_led : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo ->
  exists A : word -> Prop, ainv (m_vm_lazy mo) A NMAX mo /\ (forall p, COVPb mo p -> A p).
Proof.
  intros aw L RNG st LBa mo H. destruct (ACCT_mrel _ _ _ _ _ _ H) as (RESV & A & _ & HC & MR). exists A. split.
  - pose proof (mrel_ainv NMAX RNG A (canon mo) mo (ACCTc_acct_ok _ _ _ _ _ _ HC) MR) as X.
    unfold canon in X. rewrite m_vm_lazy_MX in X. exact X.
  - destruct HC as (_ & _ & _ & _ & _ & _ & k & HAB & HCV & _). intros p [Hp|Hp]; [exact (HCV p Hp)| apply HAB; right; exact Hp].
Qed.

Theorem ACCT_mat : forall aw L RNG st LBa mo mo', ACCT aw L RNG st LBa mo -> same_but_mat mo mo' ->
  List.NoDup (m_vm_materialized mo') ->
  (forall p, List.In p (m_vm_materialized mo') -> List.In p (m_vm_materialized mo) \/ COVPb mo p) ->
  ACCT aw L RNG st LBa mo'.
Proof.
  intros aw L RNG st LBa mo mo' (RESV & A & RK & HC & ND & AL & FX & FZ & TI) SB ND' SUB.
  assert (EC : canon mo' = canon mo) by (apply canon_same_but_mat; exact SB).
  exists RESV, A. rewrite EC. split; [exact RK|]. split; [exact HC|]. split; [exact ND'|]. split; [| split; [exact FX| split; [exact FZ| exact TI]]].
  intros p Hp. destruct (SUB p Hp) as [Hm|Hc]; [exact (AL p Hm)|].
  destruct HC as (_ & _ & _ & _ & _ & _ & k & HAB & HCV & _). destruct Hc as [Hc|Hc]; [exact (HCV p Hc)| apply HAB; right; exact Hc].
Qed.

Theorem ACCT_fds : forall aw L RNG st LBa mo f, ACCT aw L RNG st LBa mo -> ACCT aw L RNG st LBa (with_fds f mo).
Proof.
  intros aw L RNG st LBa mo f (RESV & A & RK & HC & ND & AL & FX & FZ & TI).
  assert (EC : canon (with_fds f mo) = with_fds f (canon mo)) by (destruct mo as [fd [mp lzz mt] io fs pr lm tm]; reflexivity).
  exists RESV, A. rewrite EC. split; [exact RK|]. split; [| split; [exact ND| split; [exact AL| split; [exact FX| split; [exact FZ| exact TI]]]]].
  destruct HC as ([HA HM] & Q1 & Q2 & ER & Hv & HCR & k & HAB & HCV & HBU & Hk & HP).
  split; [split; [exact HA| apply AMI_with_fds; exact HM]|]. split; [exact Q1|]. split; [exact Q2|]. split; [exact ER|]. split; [exact Hv|]. split; [exact HCR|].
  exists k. split; [exact HAB|]. split; [exact HCV|]. split; [exact HBU|]. split; [exact Hk| exact HP].
Qed.

Theorem ACCT_fpx : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> FPX L RNG.
Proof. intros aw L RNG st LBa mo (RESV & A & _ & _ & _ & _ & FX & _). exact FX. Qed.

Theorem ACCT_halted : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> m_halted mo = None.
Proof.
  intros aw L RNG st LBa mo (RESV & A & _ & _ & _ & _ & _ & (_ & _ & F3 & _) & _).
  revert F3. destruct mo as [fd [mp lzz mt] io fs pr lm tm]. exact (fun H => H).
Qed.
Theorem ACCT_lazy_shape : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> lazy_shapeA C0A mo.
Proof.
  intros aw L RNG st LBa mo (RESV & A & _ & _ & _ & _ & _ & (_ & _ & _ & F4) & _).
  revert F4. destruct mo as [fd [mp lzz mt] io fs pr lm tm]. exact (fun H => H).
Qed.
Theorem ACCT_minv : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> MINV mo.
Proof. intros aw L RNG st LBa mo H. pose proof H as (RESV & A & _ & _ & _ & _ & _ & FZ & _). exact (MINV_of_FIXZ _ _ FZ). Qed.
Lemma minvA_canon : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> minvA (canon mo).
Proof.
  intros aw L RNG st LBa mo (RESV & A & _ & ([_ HM] & _) & _).
  destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & [AT1 AT2] & _).
  split; [| reflexivity]. unfold spwin. unfold alloc_top in AT2. unfold atop_ok, ACEIL, ATOP_MAX in AT1.
  unfold sp_window_lo, sp_window_hi. unfold stack_max_size in AT2. lia.
Qed.

Theorem ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Proof. intros aw L RNG st LBa mo H. exact (proj1 (ACCT_fpx _ _ _ _ _ _ H)). Qed.
Theorem ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG 0x10000 0x621000.
Proof. intros aw L RNG st LBa mo H. exact (proj1 (proj2 (ACCT_fpx _ _ _ _ _ _ H))). Qed.
Theorem ACCT_rng_aimg_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG 0x7fffa000 0xc5000.
Proof. intros aw L RNG st LBa mo H. exact (proj1 (proj2 (proj2 (ACCT_fpx _ _ _ _ _ _ H)))). Qed.
Theorem ACCT_rng_stk_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (shad ATOP) (Shadow.KHIGH - shad ATOP).
Proof. intros aw L RNG st LBa mo H. exact (proj1 (proj2 (proj2 (proj2 (ACCT_fpx _ _ _ _ _ _ H))))). Qed.
Theorem ACCT_frng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> afake_rng L RNG.
Proof. intros aw L RNG st LBa mo H. exact (proj2 (proj2 (proj2 (proj2 (ACCT_fpx _ _ _ _ _ _ H))))). Qed.

Definition c24b (b : ablock) : bool :=
  match ab_kind b with ABHeap _ => (5881 <=? ab_size b) && (ab_size b <=? 7936) | ABFake _ => false end.
Definition c24count (LBa : list ablock) : Z := Z.of_nat (length (List.filter c24b LBa)).
Definition hb_id (b : ablock) : list aptr := match ab_kind b with ABHeap p => [p] | ABFake _ => [] end.

Lemma NoDup_fst_filter : forall {K V} (f : K * V -> bool) (l : list (K * V)), List.NoDup (map fst l) -> List.NoDup (map fst (List.filter f l)).
Proof.
  intros K V f l. induction l as [|x l IH]; intros H; cbn; [constructor|].
  cbn in H. apply List.NoDup_cons_iff in H as [H1 H2]. destruct (f x); cbn; [| exact (IH H2)].
  apply List.NoDup_cons_iff. split; [| exact (IH H2)].
  intros Hin. apply H1. apply in_map_iff in Hin as (y & Ey & Hy). apply filter_In in Hy as [Hy _]. apply in_map_iff. exists y. auto.
Qed.

Lemma filter_map_snd : forall {K V} (f : V -> bool) (l : list (K * V)),
  List.filter f (map snd l) = map snd (List.filter (fun kv => f (snd kv)) l).
Proof. intros K V f l. induction l as [|x l IH]; cbn; [reflexivity|]. destruct (f (snd x)); cbn; rewrite IH; reflexivity. Qed.

Lemma hb_id_len : forall l, (length (flat_map hb_id l) <= length l)%nat.
Proof. induction l as [|b l IH]; cbn; [lia|]. rewrite length_app. unfold hb_id at 1. destruct (ab_kind b); cbn; lia. Qed.

Lemma c24_live_le : forall RESV v RNG A st mo LBa,
  ACCTc NMAX RESV SHFIX v RNG A st mo -> TIE st LBa -> cntP K_BATCH_CLASS (live_chunks st) <= c24count LBa.
Proof.
  intros RESV v RNG A st mo LBa HC TI. destruct HC as ([HA _] & _).
  assert (HWl : Forall (chunk_wf ATOP) (live_chunks st)).
  { destruct HA as (_ & HW & _). unfold all_chunks in HW. cbn [app] in HW. apply Forall_app in HW as [HW _]. exact HW. }
  unfold cntP, zlen, c24count, live_chunks in *. rewrite filter_map_snd, length_map.
  set (M := map_to_list (a_live st)) in *.
  set (M24 := List.filter (fun kv : aptr * achunk => is_prim_of K_BATCH_CLASS (snd kv)) M).
  apply Nat2Z.inj_le. change (length M24 <= length (List.filter c24b LBa))%nat. rewrite <- (length_map fst M24).
  assert (ND : List.NoDup (map fst M24)).
  { apply NoDup_fst_filter. apply NoDup_ListNoDup. apply NoDup_fst_map_to_list. }
  set (IDS := flat_map hb_id (List.filter c24b LBa)).
  assert (LEN : (length IDS <= length (List.filter c24b LBa))%nat).
  { unfold IDS. apply hb_id_len. }
  assert (INC : incl (map fst M24) IDS).
  { intros id Hid. apply in_map_iff in Hid as ([id' ch] & <- & Hin). cbn [fst]. apply filter_In in Hin as [Hin Hp]. cbn [snd] in Hp.
    assert (Hl : (a_live st) !! id' = Some ch) by (apply elem_of_map_to_list; apply list_elem_of_In; exact Hin).
    assert (Hw : chunk_wf ATOP ch).
    { eapply (proj1 (Forall_forall _ _) HWl). apply in_map_iff. exists (id', ch). split; [reflexivity| exact Hin]. }
    destruct ch as [c n|mb ms n]; cbn [is_prim_of] in Hp; [| discriminate]. apply Z.eqb_eq in Hp. subst c.
    cbn in Hw. destruct Hw as [Hn Hc]. pose proof (c24_range n Hn (eq_sym (prim_cls_c24 _ _ Hc eq_refl))) as R24.
    destruct (TI id' _ Hl) as (Aaddr & HinB). cbn [chunk_size] in HinB.
    unfold IDS. apply in_flat_map. exists (HB id' Aaddr n). split; [| left; reflexivity].
    apply filter_In. split; [exact HinB|]. unfold c24b. cbn [ab_kind ab_size]. apply andb_true_intro. split; apply Z.leb_le; lia. }
  pose proof (List.NoDup_incl_length ND INC). lia.
Qed.

Definition c6ok (RESV : list (Z * Z)) (RNG : footprint) (st : astate) : Prop :=
  c6m RESV RNG st /\ (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23).
Lemma lazy_page_false : forall lz z, 0 <= z < 2^64 -> covered lz z = false -> page_in_ranges (page_base_of z) lz = false.
Proof.
  intros lz z Hz HC. destruct (page_in_ranges (page_base_of z) lz) eqn:E; [| reflexivity]. exfalso.
  unfold page_in_ranges in E. apply existsb_exists in E as (r & Hr & Hp). apply andb_prop in Hp as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  assert (PB : bv_unsigned (page_base_of z) = z / 4096 * 4096).
  { unfold page_base_of, page_size. apply Z_to_bv_small. unfold bv_modulus. Z.div_mod_to_equations. lia. }
  rewrite PB in H1, H2. unfold page_size in H2.
  assert (CV : covered lz z = true).
  { unfold covered. apply existsb_exists. exists r. split; [exact Hr|]. unfold in_iv, in_rng, B, S.
    apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; Z.div_mod_to_equations; lia. }
  congruence.
Qed.
Lemma ACCTc_c6 : forall RESV v RNG A st mo, ACCTc NMAX RESV SHFIX v RNG A st mo -> c6ok RESV RNG st.
Proof.
  intros RESV v RNG A st mo HC. pose proof HC as (HI & Q1 & Q2 & ER & _).
  pose proof (INV_emb_c6 (RESV:=RESV) (ATOP:=ATOP) st mo HI) as X. unfold c6ok, c6m, emb_rng, emb_clr.
  destruct (a_emb st) as [[d cap] sz]. destruct X as (X1 & X2 & X3).
  split; [| unfold EMB_MAX in X1; exact X1]. split; [| exact X2].
  destruct X3 as [->|(D0 & D1 & NL)]; [left; reflexivity| right].
  split; [exact D0|]. split; [exact D1|]. intros b j Hb Hj. rewrite ER. intros k Hk Hb64.
  left. apply lazy_page_false; [lia|]. apply NL. lia.
Qed.

Lemma leaf_actual : forall L mo A' moc' mo', vmh (canon mo) moc' -> mrel A' moc' mo' -> MP mo -> FIXZ L (canon mo) ->
  MP mo' /\ MINV mo' /\ OTHER mo mo' /\ canon mo' = moc'.
Proof.
  intros L mo A' moc' mo' HH MR HMP FZ. pose proof (canon_of_mrel _ _ _ MR) as EC.
  assert (AR : acct_rel mo mo') by (unfold acct_rel; rewrite EC; exact HH).
  split; [exact (MP_rel _ _ HMP AR)|]. split; [| split; [exact (OTHER_rel _ _ AR)| exact EC]].
  apply (MINV_of_FIXZ L). rewrite EC. exact (FIXZ_vmh _ _ _ HH FZ).
Qed.

Definition acct_leaf (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock) (n chg : Z)
    (r : astate * option aptr) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo' Aaddr, mrel A' moc' mo' ->
    MP mo' /\ MINV mo' /\ OTHER mo0 mo' /\
    match snd r with
    | Some p => ACCT (Z_to_bv 64 (bv_unsigned aw - chg)) L RNG' (fst r) (HB p Aaddr n :: LBa) mo'
    | None => ACCT (Z_to_bv 64 (bv_unsigned aw - C_EXH)) L RNG' (fst r) LBa mo'
    end
    /\ (64512 < n -> aprist st -> aprist (fst r)).
Lemma aprist_keep : forall n st st', 64512 < n -> (is_primary n = false -> cls_keep K_BATCH_CLASS st st') -> aprist st -> aprist st'.
Proof.
  intros n st st' Hn CK PR c Hc Hc24. destruct (CK (large_not_primary n Hn) c Hc24) as [E1 E2]. rewrite E1, E2. exact (PR c Hc Hc24).
Qed.

Theorem ACCT_malloc : forall aw L RNG st LBa mo n chg,
  ACCT aw L RNG st LBa mo -> MP mo -> MINV mo ->
  1 <= n <= AREQMAX -> ((chg = 0 /\ n <= 64512) \/ (chg = n /\ n <= bv_unsigned aw)) -> C_EXH <= bv_unsigned aw -> c24count LBa <= 255 ->
  exists RESV A moc, aresv_ok L RESV /\ c6ok RESV RNG st /\ mrel A moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A (aembed ATOP (amalloc ATOP RESV st n)) moc (acct_leaf mo aw L st LBa n chg).
Proof.
  intros aw L RNG st LBa mo n chg HACC HMP HMI Hn HCHG Hcx H24.
  assert (HNV : is_primary n = false -> n <= bv_unsigned aw).
  { intros NP. destruct HCHG as [[_ H]|[_ H]]; [| exact H]. rewrite is_primary_iff in NP by lia. apply Z.leb_gt in NP. lia. }
  pose proof HACC as (RESV & A & RK & HC & ND & AL & FX & FZ & TI).
  exists RESV, A, (canon mo). split; [exact RK|]. split; [exact (ACCTc_c6 _ _ _ _ _ _ HC)|]. split; [apply mrel_canon; assumption|].
  split; [exact (minvA_canon _ _ _ _ _ _ HACC)|]. split; [exact (proj1 (proj2 (proj2 FZ)))|].
  apply TS_twfS.
  assert (H24' : size_of_class K_BATCH_CLASS * (cntP K_BATCH_CLASS (live_chunks st) + 1) <= L24MAX).
  { pose proof (c24_live_le _ _ _ _ _ _ _ HC TI). assert (S24 : size_of_class K_BATCH_CLASS = 8192) by reflexivity. rewrite S24. unfold L24MAX. lia. }
  eapply TS_mono; [apply (U_malloc NMAX HLIM RESV SHFIX (bv_unsigned aw) RNG A st (canon mo) n HC Hn HNV Hcx H24')|].
  intros r RNG' A' moc' _ (HH & HFL & CK & HLEAF) mo' Aaddr MR.
  destruct (leaf_actual L mo A' moc' mo' HH MR HMP FZ) as (M1 & M2 & M3 & EC).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
  split. 2:{ intros Hn64 PR. exact (aprist_keep n st (fst r) Hn64 CK PR). }
  destruct MR as (_ & _ & ND' & AL').
  pose proof (bv_unsigned_in_range 64 aw) as RA. unfold bv_modulus in RA.
  destruct (snd r) as [p|] eqn:Esnd.
  - destruct HLEAF as (-> & FRESH & (ch & ELIVE & ESZ) & HC').
    assert (HC'' : ACCTc NMAX RESV SHFIX (bv_unsigned aw - chg) RNG' A' (fst r) moc').
    { destruct HCHG as [[-> H]|[-> H]].
      - rewrite is_primary_iff in HC' by lia. rewrite (proj2 (Z.leb_le n 64512) H) in HC'. exact HC'.
      - destruct (is_primary n); [| exact HC']. apply (ACCTc_weaken NMAX RESV SHFIX (bv_unsigned aw - 0)); [exact HC'| lia]. }
    assert (CB : 0 <= chg <= bv_unsigned aw) by (destruct HCHG as [[-> _]|[-> H]]; lia).
    exists RESV, A'. rewrite EC, Z_to_bv_unsigned, (bv_wrap_small 64 (bv_unsigned aw - chg)) by (unfold bv_modulus; lia).
    split; [exact RK|]. split; [exact HC''|]. split; [exact ND'|]. split; [exact AL'|]. split; [exact (FPX_mono _ _ _ HFL FX)|]. split; [exact (FIXZ_vmh _ _ _ HH FZ)|].
    intros id ch' Hl. rewrite ELIVE in Hl. apply lookup_insert_Some in Hl as [[<- <-]|[NE Hl]].
    + exists Aaddr. left. rewrite ESZ. reflexivity.
    + destruct (TI id ch' Hl) as (Ad & Hin). exists Ad. right. exact Hin.
  - destruct HLEAF as (ELIVE & _ & HC').
    exists RESV, A'. rewrite EC, Z_to_bv_unsigned, (bv_wrap_small 64 (bv_unsigned aw - C_EXH)) by (unfold bv_modulus, C_EXH in *; lia).
    split; [exact RK|]. split; [exact HC'|]. split; [exact ND'|]. split; [exact AL'|]. split; [exact (FPX_mono _ _ _ HFL FX)|]. split; [exact (FIXZ_vmh _ _ _ HH FZ)|].
    intros id ch' Hl. rewrite ELIVE in Hl. exact (TI id ch' Hl).
Qed.

Theorem ACCT_aligned16 : forall aw L RNG st LBa mo n chg,
  ACCT aw L RNG st LBa mo -> MP mo -> MINV mo ->
  16 <= n <= 4096 -> n mod 16 = 0 -> ((chg = 0 /\ n <= 64512) \/ (chg = n /\ n <= bv_unsigned aw)) -> C_EXH <= bv_unsigned aw ->
  exists RESV A moc, aresv_ok L RESV /\ c6ok RESV RNG st /\ mrel A moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A (aembed ATOP (aaligned16x ATOP RESV st n)) moc (acct_leaf mo aw L st LBa n chg).
Proof.
  intros aw L RNG st LBa mo n chg HACC HMP HMI Hn Hm HCHG Hcx.
  pose proof HACC as (RESV & A & RK & HC & ND & AL & FX & FZ & TI).
  exists RESV, A, (canon mo). split; [exact RK|]. split; [exact (ACCTc_c6 _ _ _ _ _ _ HC)|]. split; [apply mrel_canon; assumption|].
  split; [exact (minvA_canon _ _ _ _ _ _ HACC)|]. split; [exact (proj1 (proj2 (proj2 FZ)))|].
  apply TS_twfS.
  eapply TS_mono; [apply (U_aligned16 NMAX HLIM RESV SHFIX (bv_unsigned aw) RNG A st (canon mo) n HC Hn Hm Hcx)|].
  intros r RNG' A' moc' _ (HH & HFL & CK & HLEAF) mo' Aaddr MR.
  destruct (leaf_actual L mo A' moc' mo' HH MR HMP FZ) as (M1 & M2 & M3 & EC).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
  split. 2:{ intros Hn64 _. exfalso. lia. }
  destruct MR as (_ & _ & ND' & AL').
  pose proof (bv_unsigned_in_range 64 aw) as RA. unfold bv_modulus in RA.
  assert (EP : is_primary n = true) by (rewrite is_primary_iff by lia; apply Z.leb_le; lia).
  destruct (snd r) as [p|] eqn:Esnd.
  - destruct HLEAF as (-> & FRESH & (ch & ELIVE & ESZ) & HC'). rewrite EP in HC'.
    assert (CB : 0 <= chg <= bv_unsigned aw) by (destruct HCHG as [[-> _]|[-> H]]; lia).
    assert (HC'' : ACCTc NMAX RESV SHFIX (bv_unsigned aw - chg) RNG' A' (fst r) moc').
    { apply (ACCTc_weaken NMAX RESV SHFIX (bv_unsigned aw - 0)); [exact HC'| lia]. }
    exists RESV, A'. rewrite EC, Z_to_bv_unsigned, (bv_wrap_small 64 (bv_unsigned aw - chg)) by (unfold bv_modulus; lia).
    split; [exact RK|]. split; [exact HC''|]. split; [exact ND'|]. split; [exact AL'|]. split; [exact (FPX_mono _ _ _ HFL FX)|]. split; [exact (FIXZ_vmh _ _ _ HH FZ)|].
    intros id ch' Hl. rewrite ELIVE in Hl. apply lookup_insert_Some in Hl as [[<- <-]|[NE Hl]].
    + exists Aaddr. left. rewrite ESZ. reflexivity.
    + destruct (TI id ch' Hl) as (Ad & Hin). exists Ad. right. exact Hin.
  - destruct HLEAF as (ELIVE & _ & HC').
    exists RESV, A'. rewrite EC, Z_to_bv_unsigned, (bv_wrap_small 64 (bv_unsigned aw - C_EXH)) by (unfold bv_modulus, C_EXH in *; lia).
    split; [exact RK|]. split; [exact HC'|]. split; [exact ND'|]. split; [exact AL'|]. split; [exact (FPX_mono _ _ _ HFL FX)|]. split; [exact (FIXZ_vmh _ _ _ HH FZ)|].
    intros id ch' Hl. rewrite ELIVE in Hl. exact (TI id ch' Hl).
Qed.

Definition acct_leaf_some (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock) (n chg : Z)
    (r : astate * option aptr) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo' Aaddr, mrel A' moc' mo' ->
    MP mo' /\ MINV mo' /\ OTHER mo0 mo' /\
    (exists p, snd r = Some p /\ ACCT (Z_to_bv 64 (bv_unsigned aw - chg)) L RNG' (fst r) (HB p Aaddr n :: LBa) mo')
    /\ (64512 < n -> aprist st -> aprist (fst r)).

Lemma acct_some_leaf : forall mo aw L st LBa n chg RESV A r RNG' A' moc',
  MP mo ->
  aresv_ok L RESV -> FPX L (fp_ok (m_vm_lazy (canon mo)) A) -> FIXZ L (canon mo) -> TIE st LBa ->
  0 <= chg <= bv_unsigned aw ->
  (malloc_leaf NMAX RESV SHFIX (bv_unsigned aw) n st (canon mo) (fp_ok (m_vm_lazy (canon mo)) A) r RNG' A' moc' /\ snd r <> None) ->
  (forall p, snd r = Some p -> ACCTc NMAX RESV SHFIX (bv_unsigned aw - (if is_primary n then 0 else n)) RNG' A' (fst r) moc' ->
             ACCTc NMAX RESV SHFIX (bv_unsigned aw - chg) RNG' A' (fst r) moc') ->
  acct_leaf_some mo aw L st LBa n chg r RNG' A' moc'.
Proof.
  intros mo aw L st LBa n chg RESV A r RNG' A' moc' HMP RK FX FZ TI CB [(HH & HFL & CK & HLEAF) NN] WK mo' Aaddr MR.
  destruct (leaf_actual L mo A' moc' mo' HH MR HMP FZ) as (M1 & M2 & M3 & EC).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
  split. 2:{ intros Hn64 PR. exact (aprist_keep n st (fst r) Hn64 CK PR). }
  destruct MR as (_ & _ & ND' & AL').
  pose proof (bv_unsigned_in_range 64 aw) as RA. unfold bv_modulus in RA.
  destruct (snd r) as [p|] eqn:Esnd; [| exfalso; exact (NN eq_refl)].
  destruct HLEAF as (-> & FRESH & (ch & ELIVE & ESZ) & HC').
  exists (a_next st). split; [reflexivity|].
  exists RESV, A'. rewrite EC, Z_to_bv_unsigned, (bv_wrap_small 64 (bv_unsigned aw - chg)) by (unfold bv_modulus; lia).
  split; [exact RK|]. split; [exact (WK _ eq_refl HC')|]. split; [exact ND'|]. split; [exact AL'|]. split; [exact (FPX_mono _ _ _ HFL FX)|]. split; [exact (FIXZ_vmh _ _ _ HH FZ)|].
  intros id ch' Hl. rewrite ELIVE in Hl. apply lookup_insert_Some in Hl as [[<- <-]|[NE Hl]].
  + exists Aaddr. left. rewrite ESZ. reflexivity.
  + destruct (TI id ch' Hl) as (Ad & Hin). exists Ad. right. exact Hin.
Qed.

Theorem ACCT_malloc_some_sec : forall aw L RNG st LBa mo n,
  ACCT aw L RNG st LBa mo -> MP mo -> MINV mo ->
  64512 < n <= 2^28 -> n <= bv_unsigned aw -> CRED0 - 2^30 <= bv_unsigned aw -> c24count LBa <= 255 ->
  exists RESV A moc, aresv_ok L RESV /\ c6ok RESV RNG st /\ mrel A moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A (aembed ATOP (amalloc ATOP RESV st n)) moc (acct_leaf_some mo aw L st LBa n n).
Proof.
  intros aw L RNG st LBa mo n HACC HMP HMI Hn Hnv Hcl H24.
  pose proof HACC as (RESV & A & RK & HC & ND & AL & FX & FZ & TI).
  exists RESV, A, (canon mo). split; [exact RK|]. split; [exact (ACCTc_c6 _ _ _ _ _ _ HC)|]. split; [apply mrel_canon; assumption|].
  split; [exact (minvA_canon _ _ _ _ _ _ HACC)|]. split; [exact (proj1 (proj2 (proj2 FZ)))|].
  apply TS_twfS.
  assert (H24' : size_of_class K_BATCH_CLASS * (cntP K_BATCH_CLASS (live_chunks st) + 1) <= L24MAX).
  { pose proof (c24_live_le _ _ _ _ _ _ _ HC TI). assert (S24 : size_of_class K_BATCH_CLASS = 8192) by reflexivity. rewrite S24. unfold L24MAX. lia. }
  pose proof HC as (_ & _ & _ & ER & _).
  eapply TS_mono; [apply (U_malloc_nn_sec NMAX HLIM RESV SHFIX (bv_unsigned aw) RNG A st (canon mo) n HC Hn Hnv Hcl H24')|].
  intros r RNG' A' moc' _ HL. rewrite ER in FX, HL.
  apply (acct_some_leaf mo aw L st LBa n n RESV A r RNG' A' moc' HMP RK FX FZ TI ltac:(lia) HL).
  intros p Hp X. rewrite (large_not_primary n) in X by lia. exact X.
Qed.

Theorem ACCT_malloc_some_prim : forall aw L RNG st LBa mo n,
  ACCT aw L RNG st LBa mo -> MP mo -> MINV mo ->
  1 <= n <= 64512 -> C_EXH <= bv_unsigned aw -> c24count LBa <= 255 -> aprist st ->
  exists RESV A moc, aresv_ok L RESV /\ c6ok RESV RNG st /\ mrel A moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A (aembed ATOP (amalloc ATOP RESV st n)) moc (acct_leaf_some mo aw L st LBa n 0).
Proof.
  intros aw L RNG st LBa mo n HACC HMP HMI Hn Hcx H24 PR.
  pose proof HACC as (RESV & A & RK & HC & ND & AL & FX & FZ & TI).
  exists RESV, A, (canon mo). split; [exact RK|]. split; [exact (ACCTc_c6 _ _ _ _ _ _ HC)|]. split; [apply mrel_canon; assumption|].
  split; [exact (minvA_canon _ _ _ _ _ _ HACC)|]. split; [exact (proj1 (proj2 (proj2 FZ)))|].
  apply TS_twfS.
  assert (H24' : size_of_class K_BATCH_CLASS * (cntP K_BATCH_CLASS (live_chunks st) + 1) <= L24MAX).
  { pose proof (c24_live_le _ _ _ _ _ _ _ HC TI). assert (S24 : size_of_class K_BATCH_CLASS = 8192) by reflexivity. rewrite S24. unfold L24MAX. lia. }
  pose proof HC as (_ & _ & _ & ER & _).
  pose proof (bv_unsigned_in_range 64 aw) as RA. unfold bv_modulus in RA.
  eapply TS_mono; [apply (U_malloc_nn_prim NMAX HLIM RESV SHFIX (bv_unsigned aw) RNG A st (canon mo) n HC Hn Hcx H24')|].
  { intros c Hc Hc24. exact (proj2 (PR c ltac:(lia) Hc24)). }
  intros r RNG' A' moc' _ HL. rewrite ER in FX, HL.
  apply (acct_some_leaf mo aw L st LBa n 0 RESV A r RNG' A' moc' HMP RK FX FZ TI ltac:(lia) HL).
  intros p Hp X. assert (EP : is_primary n = true) by (rewrite is_primary_iff by lia; apply Z.leb_le; lia). rewrite EP in X.
  apply (ACCTc_weaken NMAX RESV SHFIX (bv_unsigned aw - 0)); [exact X| lia].
Qed.

Lemma In_lb_remove_ne : forall p LB b, In b LB -> ab_kind b <> ABHeap p -> In b (lb_remove p LB).
Proof.
  intros p LB b H1 H2. unfold lb_remove. apply list_elem_of_In. apply list_elem_of_filter. split; [| apply list_elem_of_In; exact H1].
  destruct (ab_kind b) as [q|c]; cbn; [| exact I]. destruct (N.eqb_spec q p) as [->|NE]; [exfalso; apply H2; reflexivity| exact I].
Qed.

Definition acct_leaf_free (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock) (p : aptr)
    (r : astate) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ MINV mo' /\ OTHER mo0 mo' /\ ACCT aw L RNG' r (lb_remove p LBa) mo'
    /\ (aprist st -> aprist r).

Theorem ACCT_free : forall aw L RNG st LBa mo p ch,
  ACCT aw L RNG st LBa mo -> MP mo -> MINV mo -> (a_live st) !! p = Some ch ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (aembed ATOP (afree st (Some p))) moc (acct_leaf_free mo aw L st LBa p).
Proof.
  intros aw L RNG st LBa mo p ch HACC HMP HMI Hl.
  pose proof HACC as (RESV & A & RK & HC & ND & AL & FX & FZ & TI).
  exists A, (canon mo). split; [apply mrel_canon; assumption|].
  split; [exact (minvA_canon _ _ _ _ _ _ HACC)|]. split; [exact (proj1 (proj2 (proj2 FZ)))|].
  apply TS_twfS.
  eapply TS_mono; [apply (U_free NMAX HLIM RESV SHFIX (bv_unsigned aw) RNG A st (canon mo) p ch HC Hl)|].
  intros st' RNG' A' moc' _ (HH & HFL & ELIVE & _ & CK & HC') mo' MR.
  destruct (leaf_actual L mo A' moc' mo' HH MR HMP FZ) as (M1 & M2 & M3 & EC).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
  split. 2:{ intros PR. exact (aprist_keep 64513 st st' ltac:(lia) (fun _ => CK) PR). }
  destruct MR as (_ & _ & ND' & AL').
  exists RESV, A'. rewrite EC. split; [exact RK|]. split; [exact HC'|]. split; [exact ND'|]. split; [exact AL'|]. split; [exact (FPX_mono _ _ _ HFL FX)|]. split; [exact (FIXZ_vmh _ _ _ HH FZ)|].
  intros id ch' Hl'. rewrite ELIVE in Hl'. apply lookup_delete_Some in Hl' as [NE Hl'].
  destruct (TI id ch' Hl') as (Ad & Hin). exists Ad. apply In_lb_remove_ne; [exact Hin|]. cbn [ab_kind]. congruence.
Qed.

Definition acct_leaf_realloc (mo0 : Model) (aw : word) (L : alayout) (LBa : list ablock) (p : aptr) (n chg : Z)
    (r : astate * option aptr) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo' Aaddr, mrel A' moc' mo' ->
    MP mo' /\ MINV mo' /\ OTHER mo0 mo' /\
    match snd r with
    | Some q => ACCT (Z_to_bv 64 (bv_unsigned aw - chg)) L RNG' (fst r) (HB q Aaddr n :: lb_remove p LBa) mo'
    | None => ACCT (Z_to_bv 64 (bv_unsigned aw - C_EXH)) L RNG' (fst r) LBa mo'
    end.

Theorem ACCT_realloc : forall aw L RNG st LBa mo p chp n chg,
  ACCT aw L RNG st LBa mo -> MP mo -> MINV mo -> (a_live st) !! p = Some chp ->
  1 <= n <= AREQMAX -> ((chg = 0 /\ n <= 64512) \/ (chg = n /\ n <= bv_unsigned aw)) -> C_EXH <= bv_unsigned aw -> c24count LBa <= 255 ->
  exists RESV A0 moc, aresv_ok L RESV /\ c6ok RESV RNG st /\ mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (aembed ATOP (arealloc_m RESV st p n)) moc (acct_leaf_realloc mo aw L LBa p n chg).
Proof.
  intros aw L RNG st LBa mo p chp n chg HACC HMP HMI Hp Hn HCHG Hcx H24.
  pose proof HACC as (RESV & A & RK & HC & ND & AL & FX & FZ & TI).
  assert (HNV : is_primary n = false -> n <= bv_unsigned aw).
  { intros NP. destruct HCHG as [[_ H]|[_ H]]; [| exact H]. rewrite is_primary_iff in NP by lia. apply Z.leb_gt in NP. lia. }
  exists RESV, A, (canon mo). split; [exact RK|]. split; [exact (ACCTc_c6 _ _ _ _ _ _ HC)|]. split; [apply mrel_canon; assumption|].
  split; [exact (minvA_canon _ _ _ _ _ _ HACC)|]. split; [exact (proj1 (proj2 (proj2 FZ)))|].
  apply TS_twfS.
  assert (H24' : size_of_class K_BATCH_CLASS * (cntP K_BATCH_CLASS (live_chunks st) + 1) <= L24MAX).
  { pose proof (c24_live_le _ _ _ _ _ _ _ HC TI). assert (S24 : size_of_class K_BATCH_CLASS = 8192) by reflexivity. rewrite S24. unfold L24MAX. lia. }
  eapply TS_mono; [apply (U_realloc NMAX HLIM RESV SHFIX (bv_unsigned aw) RNG A st (canon mo) p chp n HC Hp Hn HNV Hcx H24')|].
  intros r RNG' A' moc' _ (HH & HFL & HLEAF) mo' Aaddr MR.
  destruct (leaf_actual L mo A' moc' mo' HH MR HMP FZ) as (M1 & M2 & M3 & EC).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
  destruct MR as (_ & _ & ND' & AL').
  pose proof (bv_unsigned_in_range 64 aw) as RA. unfold bv_modulus in RA.
  destruct (snd r) as [q|] eqn:Esnd.
  - destruct HLEAF as (-> & FRESH & (ch & ELIVE & ESZ) & HC').
    assert (HC'' : ACCTc NMAX RESV SHFIX (bv_unsigned aw - chg) RNG' A' (fst r) moc').
    { destruct HCHG as [[-> H]|[-> H]].
      - rewrite is_primary_iff in HC' by lia. rewrite (proj2 (Z.leb_le n 64512) H) in HC'. exact HC'.
      - destruct (is_primary n); [| exact HC']. apply (ACCTc_weaken NMAX RESV SHFIX (bv_unsigned aw - 0)); [exact HC'| lia]. }
    assert (CB : 0 <= chg <= bv_unsigned aw) by (destruct HCHG as [[-> _]|[-> H]]; lia).
    exists RESV, A'. rewrite EC, Z_to_bv_unsigned, (bv_wrap_small 64 (bv_unsigned aw - chg)) by (unfold bv_modulus; lia).
    split; [exact RK|]. split; [exact HC''|]. split; [exact ND'|]. split; [exact AL'|]. split; [exact (FPX_mono _ _ _ HFL FX)|]. split; [exact (FIXZ_vmh _ _ _ HH FZ)|].
    intros id ch' Hl. rewrite ELIVE in Hl. apply lookup_delete_Some in Hl as [NEp Hl]. apply lookup_insert_Some in Hl as [[<- <-]|[NE Hl]].
    + exists Aaddr. left. rewrite ESZ. reflexivity.
    + destruct (TI id ch' Hl) as (Ad & Hin). exists Ad. right. apply In_lb_remove_ne; [exact Hin|]. cbn [ab_kind]. congruence.
  - destruct HLEAF as (ELIVE & HC').
    exists RESV, A'. rewrite EC, Z_to_bv_unsigned, (bv_wrap_small 64 (bv_unsigned aw - C_EXH)) by (unfold bv_modulus, C_EXH in *; lia).
    split; [exact RK|]. split; [exact HC'|]. split; [exact ND'|]. split; [exact AL'|]. split; [exact (FPX_mono _ _ _ HFL FX)|]. split; [exact (FIXZ_vmh _ _ _ HH FZ)|].
    intros id ch' Hl. rewrite ELIVE in Hl. exact (TI id ch' Hl).
Qed.

Definition acct_leaf_keep (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa' : list ablock)
    (_ : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ MINV mo' /\ OTHER mo0 mo' /\ ACCT aw L RNG' st LBa' mo'.

Theorem ACCT_keep : forall aw L RNG st LBa LBa' mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  (forall id Aaddr n, In (HB id Aaddr n) LBa -> In (HB id Aaddr n) LBa') ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Ok tt)) moc (acct_leaf_keep mo aw L st LBa').
Proof.
  intros aw L RNG st LBa LBa' mo HACC HMP SUB.
  pose proof HACC as (RESV & A & RK & HC & ND & AL & FX & FZ & TI).
  exists A, (canon mo). split; [apply mrel_canon; assumption|].
  split; [exact (minvA_canon _ _ _ _ _ _ HACC)|]. split; [exact (proj1 (proj2 (proj2 FZ)))|].
  cbn. split; [exact (ACCTc_acct_ok _ _ _ _ _ _ HC)|].
  intros mo' MR. destruct (leaf_actual L mo A (canon mo) mo' (vmh_refl _) MR HMP FZ) as (M1 & M2 & M3 & EC).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
  destruct MR as (_ & _ & ND' & AL').
  exists RESV, A. rewrite EC. split; [exact RK|]. split; [exact HC|]. split; [exact ND'|]. split; [exact AL'|]. split; [exact FX|]. split; [exact FZ|].
  intros id ch' Hl'. destruct (TI id ch' Hl') as (Ad & Hin). exists Ad. apply SUB. exact Hin.
Qed.

Definition acct_leaf_silent (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock)
    (r : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ MINV mo' /\ OTHER mo0 mo' /\ ACCT aw L RNG' st LBa mo'.
Theorem ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Ok tt)) moc (acct_leaf_silent mo aw L st LBa).
Proof. intros aw L RNG st LBa mo HACC HMP. exact (ACCT_keep aw L RNG st LBa LBa mo HACC HMP (fun _ _ _ H => H)). Qed.

Definition acct_leaf_frame_in (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock)
    (r : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ MINV mo' /\ OTHER mo0 mo' /\
    forall c F n LBk, (forall id Aaddr sz, In (HB id Aaddr sz) LBa -> In (HB id Aaddr sz) LBk) -> ACCT aw L RNG' st (mkABlock (ABFake c) F n :: LBk) mo'.
Theorem ACCT_frame_in : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Ok tt)) moc (acct_leaf_frame_in mo aw L st LBa).
Proof.
  intros aw L RNG st LBa mo HACC HMP.
  pose proof HACC as (RESV & A & RK & HC & ND & AL & FX & FZ & TI).
  exists A, (canon mo). split; [apply mrel_canon; assumption|].
  split; [exact (minvA_canon _ _ _ _ _ _ HACC)|]. split; [exact (proj1 (proj2 (proj2 FZ)))|].
  cbn. split; [exact (ACCTc_acct_ok _ _ _ _ _ _ HC)|].
  intros mo' MR. destruct (leaf_actual L mo A (canon mo) mo' (vmh_refl _) MR HMP FZ) as (M1 & M2 & M3 & EC).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. intros c F n LBk SUB.
  destruct MR as (_ & _ & ND' & AL').
  exists RESV, A. rewrite EC. split; [exact RK|]. split; [exact HC|]. split; [exact ND'|]. split; [exact AL'|]. split; [exact FX|]. split; [exact FZ|].
  intros id ch' Hl'. destruct (TI id ch' Hl') as (Ad & Hin). exists Ad. right. apply SUB. exact Hin.
Qed.

Definition acct_leaf_keep_any (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock)
    (r : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ MINV mo' /\ OTHER mo0 mo' /\
    forall LBk, (forall id Aaddr sz, In (HB id Aaddr sz) LBa -> In (HB id Aaddr sz) LBk) -> ACCT aw L RNG' st LBk mo'.
Theorem ACCT_keep_any : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Ok tt)) moc (acct_leaf_keep_any mo aw L st LBa).
Proof.
  intros aw L RNG st LBa mo HACC HMP.
  pose proof HACC as (RESV & A & RK & HC & ND & AL & FX & FZ & TI).
  exists A, (canon mo). split; [apply mrel_canon; assumption|].
  split; [exact (minvA_canon _ _ _ _ _ _ HACC)|]. split; [exact (proj1 (proj2 (proj2 FZ)))|].
  cbn. split; [exact (ACCTc_acct_ok _ _ _ _ _ _ HC)|].
  intros mo' MR. destruct (leaf_actual L mo A (canon mo) mo' (vmh_refl _) MR HMP FZ) as (M1 & M2 & M3 & EC).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. intros LBk SUB.
  destruct MR as (_ & _ & ND' & AL').
  exists RESV, A. rewrite EC. split; [exact RK|]. split; [exact HC|]. split; [exact ND'|]. split; [exact AL'|]. split; [exact FX|]. split; [exact FZ|].
  intros id ch' Hl'. destruct (TI id ch' Hl') as (Ad & Hin). exists Ad. apply SUB. exact Hin.
Qed.

Variable ISF : ablock -> Prop.
Variable DEL : ablock -> list ablock -> list ablock.
Hypothesis DEL_In : forall b LBa x, In x (DEL b LBa) <-> In x LBa /\ x <> b.
Hypothesis ISF_heap : forall id Aaddr sz, ~ ISF (HB id Aaddr sz).
Definition acct_leaf_frame_out (mo0 : Model) (aw : word) (L : alayout) (st : astate) (LBa : list ablock)
    (r : unit) (RNG' : footprint) (A' : alw) (moc' : Model) : Prop :=
  forall mo', mrel A' moc' mo' -> MP mo' /\ MINV mo' /\ OTHER mo0 mo' /\
    forall fb, In fb LBa -> ISF fb -> ACCT aw L RNG' st (DEL fb LBa) mo'.
Theorem ACCT_frame_out : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Ok tt)) moc (acct_leaf_frame_out mo aw L st LBa).
Proof.
  intros aw L RNG st LBa mo HACC HMP.
  destruct (ACCT_keep_any aw L RNG st LBa mo HACC HMP) as (A0 & moc & MR & MV & HH & TW). exists A0, moc.
  split; [exact MR|]. split; [exact MV|]. split; [exact HH|]. cbn in TW |- *. destruct TW as [ACC HL]. split; [exact ACC|].
  intros mo' MR'. destruct (HL mo' MR') as (M1 & M2 & M3 & HK). split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
  intros fb Hfb FK. apply HK. intros id Aaddr sz Hin. apply DEL_In. split; [exact Hin|].
  intros E. rewrite <- E in FK. exact (ISF_heap id Aaddr sz FK).
Qed.

Theorem ACCT_cov_sh : forall aw L RNG st LBa mo z, ACCT aw L RNG st LBa mo -> SHFIX (page_base_of z) ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVPb mo (page_base_of z).
Proof. intros. right. right. assumption. Qed.

Variable AI : AMallocIface2.

Hypothesis AI_arena : arena_law (AHEAP AI).

Hypothesis AI_fake_area : forall L RNG st LBa m c F n, AHEAP AI L RNG st LBa m -> In (mkABlock (ABFake c) F n) LBa ->
  al_fake L <= F /\ F + n <= al_fake L + 11571200 /\ F mod 8 = 0 /\ n mod 8 = 0 /\ ablk F (F + n).

Theorem ACCT_cov : forall aw L RNG st LBa m mo b z, ACCT aw L RNG st LBa mo -> AHEAP AI L RNG st LBa m -> In b LBa ->
  (ab_addr b <= z < ab_addr b + ab_size b \/ shad (ab_addr b) <= z < shad (ab_addr b) + shlen (ab_size b + 7)) ->
  page_in_ranges (page_base_of z) (m_vm_lazy mo) = false \/ COVPb mo (page_base_of z).
Proof.
  intros aw L RNG st LBa m mo b z (RESV & A & RK & HC & ND & AL & FX & FZ & TI) AH Hb Hz.
  change (m_vm_lazy mo) with (m_vm_lazy (canon mo)).
  destruct HC as ([HA HM] & _). pose proof atop_range as ATR.
  pose proof (AMI_atop _ _ _ HM) as [[T1 T2] _]. unfold ACEIL, ATOP_MAX in T1, T2.

  assert (SHC : forall X len, (exists e, In e (vm_maps (m_vmmaps (canon mo))) /\ B e <= X /\ X + len <= B e + S e) ->
                 (X + len <= LS_LO \/ KHIGH <= X) -> X mod 8 = 0 -> 0 <= X -> 0 <= len ->
                 shad X <= z < shad X + shlen len -> COVP (canon mo) (page_base_of z)).
  { intros X len (e & He & E1 & E2) APP X8 X0 L0 Hzz. unfold shad, shlen in Hzz. rewrite !Z.shiftr_div_pow2 in Hzz by lia. change (2 ^ 3) with 8 in Hzz.
    exists e, (8 * (z - ASHOFF)). split; [exact He|].
    split; [Z.div_mod_to_equations; lia|]. split; [unfold appz; Z.div_mod_to_equations; lia|].
    f_equal. unfold shad. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. }
  destruct (AI_block_bounds AI L RNG st LBa m b AH Hb) as (BB1 & BB2 & BB3). unfold ABase.TwinB.AIMG_HI in BB1.
  destruct b as [[p|c] Ab n]; cbn [ab_addr ab_size] in *.
  -
    destruct (AI_block AI L RNG st LBa m p Ab n AH Hb) as (N & BR & _ & _ & _ & _ & (ch & LV & SZ & SEC) & _).
    destruct BR as (BK & N0 & TOP & A16).
    pose proof HA as (HCLS & HW & _).
    assert (INL : In ch (live_chunks st)).
    { unfold live_chunks. apply in_map_iff. exists (p, ch). split; [reflexivity|]. apply list_elem_of_In. apply elem_of_map_to_list. exact LV. }
    assert (Hwf : chunk_wf ATOP ch).
    { unfold all_chunks in HW. cbn [app] in HW. apply Forall_app in HW as [HW _]. exact (proj1 (Forall_forall _ _) HW ch INL). }
    destruct (is_primary n) eqn:PR.
    +
      destruct (AI_arena L RNG st LBa m p Ab n AH Hb PR) as (c & Hc & R1 & R2).
      pose proof (HCLS c Hc) as (C1 & C2 & C3 & _). cbv zeta in C1, C2, C3.
      pose proof (AI_layout AI L RNG st LBa m AH) as (_ & _ & _ & _ & SBE & _).
      destruct Hz as [Hz|Hz].
      * left. apply lazy_page_false; [lia|]. apply (AMI_lazy_committed _ st (canon mo) z HM).
        exists c. split; [exact Hc|]. unfold region_beg. rewrite SBE. lia.
      * right. left. destruct (AMI_arena_entry _ st (canon mo) HM) as (e & He & E1 & E2 & E3).
        apply (SHC Ab (n + 7)); [| right; rewrite SBE in *; unfold K_REGION in *; lia| clear -A16; Z.div_mod_to_equations; lia| lia| lia| exact Hz].
        exists e. split; [exact He|]. rewrite SBE in *. unfold K_REGION, K_FREEARR_OFF in *. lia.
    +
      specialize (SEC eq_refl). destruct ch as [c0 n0|mb ms n0]; cbn [chunk_size] in SZ; subst n0.
      { exfalso. cbn in Hwf. destruct Hwf as [Hn _]. rewrite is_primary_iff in PR by lia. apply Z.leb_gt in PR. lia. }
      cbn in Hwf. destruct Hwf as (Hn & -> & MB4 & MB0 & PLACE). cbn [chunk_user_beg] in SEC.
      pose proof (sec_map_size_ge n ltac:(lia)) as SG.
      assert (RZ : rz_size n = 2048) by (unfold rz_size, rz_log; repeat (rewrite (proj2 (Z.leb_gt _ _)) by lia); reflexivity).
      unfold PG in SEC. rewrite RZ in SEC.
      assert (INC : In (mb, sec_map_size n) (CHX [] [] st)).
      { unfold CHX, CH, all_chunks. cbn [app]. apply in_or_app. left. rewrite secs_app. apply in_or_app. left. unfold secs. apply in_flat_map.
        exists (CSec mb (sec_map_size n) n). split; [exact INL| left; reflexivity]. }
      destruct Hz as [Hz|Hz].
      * left. apply lazy_page_false; [lia|]. apply (AMI_lazy_ch _ st (canon mo) mb (sec_map_size n) z HM INC); unfold LS_LO in *; lia.
      * right. left. apply (SHC Ab (n + 7)); [| unfold LS_LO, KHIGH in *; lia| clear -A16; Z.div_mod_to_equations; lia| lia| lia| exact Hz].
        exists (went (mb, sec_map_size n)). split; [exact (AMI_ch_entry _ st (canon mo) mb (sec_map_size n) HM INC)|].
        unfold went, B, S. cbn [fst snd]. unfold LS_LO in *. rewrite !unsigned_lit by lia. lia.
  -
    destruct (AI_fake_area L RNG st LBa m c Ab n AH Hb) as (F1 & F2 & F8 & N8 & BK).
    destruct FZ as (RLO & NLZ & _).
    destruct Hz as [Hz|Hz].
    + left. apply NLZ. lia.
    + right. left. destruct RK as (_ & _ & _ & _ & _ & _ & _ & _ & RFK & _).
      assert (BKL : Ab + n <= LS_LO \/ KHIGH <= Ab) by (unfold ablk, KLS, LS_LO, KHIGH in *; lia).

      unfold shad, shlen in Hz. rewrite !Z.shiftr_div_pow2 in Hz by lia. change (2 ^ 3) with 8 in Hz.
      set (x := 8 * (z - ASHOFF)).
      assert (Hx : Ab <= x < Ab + n) by (unfold x; Z.div_mod_to_equations; lia).
      destruct (RFK x ltac:(lia)) as (iv & Hiv & Hxi).
      destruct (AMI_resv_entry _ st (canon mo) iv HM Hiv) as [(e & He & E1 & E2)|(e & He & E1 & E2)].
      * exfalso. pose proof (proj1 (Forall_forall _ _) RLO e He) as X. cbv beta in X. unfold B, S, ABase.TwinB.AIMG_HI in *. lia.
      * exists e, x. split; [exact He|]. split; [lia|]. split; [unfold appz; lia|].
        f_equal. unfold x, shad. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia.
Qed.

End Acct.
End TwinB.
