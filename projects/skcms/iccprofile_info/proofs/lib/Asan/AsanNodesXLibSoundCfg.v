(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
(* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PropExec CatSim Hoare Frame FuzzContract.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsFuzzContract.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import PropExec CatExec CatSim SeqExec StoreOk StepTac ShapeAlg SpinAlg AgentLib Hoare
  AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import SpinAlgCfg AsanAcctShapeCfg AsanPlanSoundCfg AsanPlanSoundSumsCfg.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanNodesXLib AsanMainCfg.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import APSX. Import XLN.
Unset Lia Cache.
Open Scope Z_scope.

Module IP := OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec.
Module IC := OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim.
Module IH := OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare.
Module IF := OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma msteps_of_banked : forall segs a b, IC.msteps segs a b -> CatSim.msteps segs a b.
Proof.
  intros segs a b H. induction H as [ms | ms ms' ms'' Hp Hs _ IH].
  - apply CatSim.mst_refl.
  - eapply CatSim.mst_step; [exact Hp | exact Hs | exact IH].
Qed.

(* [comment removed for export] *)
Definition fp_to_info (FP : PropExec.FPState) (H : FPI FP) : IP.FPState :=
  IP.FPS (@PropExec.fp_regs FP) (@PropExec.fp_csr FP) (proj2 (Z.ltb_lt _ _) H).
Definition fp_of_info (fpi : IP.FPState) : PropExec.FPState := PropExec.mkFP (@IP.fp_regs fpi) (@IP.fp_csr fpi).
Lemma FPI_of_info : forall fpi, FPI (fp_of_info fpi).
Proof. intros fpi. unfold FPI, fp_of_info. cbn. apply Z.ltb_lt. exact (@IP.fp_csr_ok fpi). Qed.
Lemma mkst_to_info : forall FP (H : FPI FP) regs pc mem rom,
  @IP.mkst (fp_to_info FP H) regs pc mem rom = @PropExec.mkst FP regs pc mem rom.
Proof. reflexivity. Qed.
Lemma mkst_of_info : forall fpi regs pc mem rom,
  @IP.mkst fpi regs pc mem rom = @PropExec.mkst (fp_of_info fpi) regs pc mem rom.
Proof. reflexivity. Qed.

#[local] Notation SB := AsFuzzContract.AS_SB.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Tests.
  Variable segs : list Segment.
  Variable A : atable.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.

  Lemma elenZ_lit : forall E z, 0 <= z < 2 ^ 64 -> bv_unsigned (edenot E (ELit z)) = z.
  Proof. intros E z Hz. cbn [edenot]. apply u64_lit. exact Hz. Qed.
  Lemma elenZ_lit' : forall E z, 0 <= z < 2 ^ 64 -> elenZ E (ELit z) = z.
  Proof. intros E z Hz. unfold elenZ. apply elenZ_lit. exact Hz. Qed.

  (* [comment removed for export] *)
  Lemma cell_ok_sound : forall E M k a w v,
    know_ok segs E M k -> cell_ok segs k a w v = true ->
    0 <= a /\ a + w <= 2 ^ 64 /\ 1 <= w <= 8 /\ 0 <= v < 2 ^ (8 * w) /\
    rdn segs M (Z_to_bv 64 a) (Z.to_nat w) = Some (word_to_le_bytes (Z.to_nat w) (Z_to_bv 64 v)).
  Proof.
    intros E M k a w v HK H. unfold cell_ok in H.
    apply andb_prop in H as [H HL]. apply andb_prop in H as [H Hfl]. apply andb_prop in H as [H Hw8]. apply andb_prop in H as [H Hw1].
    apply andb_prop in H as [Hv0 Hvw].
    apply Z.leb_le in Hv0. apply Z.ltb_lt in Hvw. apply Z.leb_le in Hw1. apply Z.leb_le in Hw8.
    destruct (flat_x_sound segs E M k (ELit 0) a (ELit w) HK Hfl) as (F0 & F1 & F2).
    rewrite elenZ_lit in F1, F2 by lia.
    assert (Ha : estart E (SA (ELit 0) a) = a) by (unfold estart; cbn [a_base a_off edenot]; rewrite u64_lit by lia; lia). rewrite Ha in F0, F1.
    destruct (know_lookup segs k (ELit 0) a (Z.to_nat w) false [] []) as [e sc hs|sc hs|] eqn:HLk; try discriminate.
    destruct e; try discriminate. destruct sc; [|discriminate]. apply Z.eqb_eq in HL. subst z.
    destruct (lookup_piece segs E M k (ELit 0) a (Z.to_nat w) (ELit v) hs HK ltac:(lia) HLk
                ltac:(unfold flat; rewrite Ha; lia)) as (bs & Hrd & Hlen & Hbs).
    rewrite Ha in Hrd. cbn [edenot] in Hbs.
    repeat split; try lia. rewrite Hrd, <- Hbs. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rd8_ok_sound : forall E M k b off,
    know_ok segs E M k -> rd8_ok segs k b off = true ->
    0 <= estart E (SA b off) /\ estart E (SA b off) + 8 <= 2 ^ 64 /\
    exists w : word, rdn segs M (Z_to_bv 64 (estart E (SA b off))) 8 = Some (word_to_le_bytes 8 w).
  Proof.
    intros E M k b off HK H. unfold rd8_ok in H. apply andb_prop in H as [Hfl Hrd].
    destruct (flat_x_sound segs E M k b off (ELit 8) HK Hfl) as (F0 & F1 & _). rewrite elenZ_lit in F1 by lia.
    destruct (kn_readable_sound segs E M k M k b off 8 HK HK ltac:(lia) ltac:(lia) Hrd) as (_ & bs & Hrd' & Hlen).
    rewrite adenot_SA in Hrd'. repeat split; try lia.
    exists (Z_to_bv 64 (bytes_le_to_Z bs)). rewrite Hrd'. f_equal. symmetry. apply word_to_le_bytes_of_bytes_n; [exact Hlen | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma word_at_sound : forall E M k b off e,
    know_ok segs E M k -> word_at segs k b off = Some e ->
    0 <= estart E (SA b off) /\ estart E (SA b off) + 8 <= 2 ^ 64 /\
    rdn segs M (Z_to_bv 64 (estart E (SA b off))) 8 = Some (word_to_le_bytes 8 (edenot E e)).
  Proof.
    intros E M k b off e HK H. unfold word_at in H.
    destruct (flat_x k b off (ELit 8)) eqn:Hfl; [|discriminate].
    destruct (flat_x_sound segs E M k b off (ELit 8) HK Hfl) as (F0 & F1 & _). rewrite elenZ_lit in F1 by lia.
    destruct (know_lookup segs k b off 8 false [] []) as [e' sc hs|sc hs|] eqn:HLk; try discriminate.
    destruct sc; [|discriminate]. injection H as ->.
    destruct (lookup_piece segs E M k b off 8 e hs HK ltac:(lia) HLk ltac:(unfold flat; lia)) as (bs & Hrd & Hlen & Hbs).
    repeat split; try lia. rewrite Hrd, <- Hbs. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma wr_ok_sound : forall E M k b off n,
    know_ok segs E M k -> wr_ok k b off n = true ->
    0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64 /\ 0 < elenZ E n /\
    store_ok segs M (Z_to_bv 64 (estart E (SA b off))) (Z.to_nat (elenZ E n)) = true.
  Proof.
    intros E M k b off n HK H. unfold wr_ok in H. apply andb_prop in H as [Hfl Hwr].
    destruct (flat_x_sound segs E M k b off n HK Hfl) as (F0 & F1 & F2).
    destruct (kwritable_x_sound segs E M k k b off n HK HK Hwr) as (W & _ & _).
    unfold elenZ in *. repeat split; try lia. apply W. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kzero_ok_sound : forall E M k b off n,
    know_ok segs E M k -> kzero_x k k b off n = true ->
    0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64 /\
    forall i, 0 <= i < elenZ E n -> M (Z_to_bv 64 (estart E (SA b off) + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros E M k b off n HK H.
    destruct (kzero_x_sound segs E M k k b off n HK HK H) as (Z0 & F0 & F1).
    repeat split; try lia. exact Z0.
  Qed.

  (* [comment removed for export] *)
  Lemma xcover_sound : forall E M k rb rk ne,
    know_ok segs E M k -> xcover k rb rk ne = true ->
    (forall i, 0 <= i < elenZ E ne -> in_hull A (estart E (SA rb rk) + i) = false) ->
    0 <= estart E (SA rb rk) /\ estart E (SA rb rk) + elenZ E ne <= 2 ^ 64 /\
    forall i, 0 <= i < elenZ E ne -> exists b, M (Z_to_bv 64 (estart E (SA rb rk) + i)) = Some b.
  Proof.
    intros E M k rb rk ne HK H Hoff. unfold xcover in H.
    apply existsb_exists in H as (K & Hin & HKb).
    pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKok.
    destruct K as [ | [cb ck] len | [cb ck] len bk | | | | [cb ck] len | | [cb ck] len c | [cb ck] len | kinv_id kinv_args]; try discriminate;
      destruct (xinside_sound segs E M k rb rk ne cb ck len HK HKb) as [I1 I2]; cbn [kentry_ok] in HKok.
    - destruct HKok as [Hfl Hz]. unfold flat in Hfl. repeat split; try lia.
      intros i Hi. exists (Z_to_bv 8 0). replace (estart E (SA rb rk) + i) with (estart E (SA cb ck) + (estart E (SA rb rk) - estart E (SA cb ck) + i)) by lia.
      apply Hz. lia.
    - destruct HKok as (Hfl & Hlen & Hb). unfold flat in Hfl. repeat split; try lia.
      intros i Hi. eexists. replace (estart E (SA rb rk) + i) with (estart E (SA cb ck) + (estart E (SA rb rk) - estart E (SA cb ck) + i)) by lia.
      apply Hb. lia.
    - (* [comment removed for export] *)
      destruct HKok as [Hfl Hw]. unfold flat in Hfl. repeat split; try lia.
      intros i Hi.
      specialize (Hw (estart E (SA rb rk) - estart E (SA cb ck) + i) 1%nat ltac:(lia) ltac:(cbn [Z.of_nat]; lia)).
      replace (estart E (SA cb ck) + (estart E (SA rb rk) - estart E (SA cb ck) + i)) with (estart E (SA rb rk) + i) in Hw by lia.
      cbn [store_ok] in Hw. destruct (wview segs M (Z_to_bv 64 (estart E (SA rb rk) + i))) as [b|] eqn:Hv; [|discriminate].
      unfold wview in Hv. destruct (M (Z_to_bv 64 (estart E (SA rb rk) + i))) as [b0|] eqn:Hm; [exists b0; reflexivity|].
      rewrite (SEGS_in_hull (Z_to_bv 64 (estart E (SA rb rk) + i))) in Hv; [discriminate|].
      rewrite u64_lit by lia. apply Hoff. exact Hi.
    - destruct HKok as [Hfl Hz]. unfold flat in Hfl. repeat split; try lia.
      intros i Hi. eexists. replace (estart E (SA rb rk) + i) with (estart E (SA cb ck) + (estart E (SA rb rk) - estart E (SA cb ck) + i)) by lia.
      apply Hz. lia.
    - destruct HKok as [Hfl Hz]. unfold flat in Hfl. repeat split; try lia.
      intros i Hi. replace (estart E (SA rb rk) + i) with (estart E (SA cb ck) + (estart E (SA rb rk) - estart E (SA cb ck) + i)) by lia.
      destruct (M (Z_to_bv 64 (estart E (SA cb ck) + (estart E (SA rb rk) - estart E (SA cb ck) + i)))) as [b|] eqn:Hm; [exists b; reflexivity|].
      exfalso. apply (Hz (estart E (SA rb rk) - estart E (SA cb ck) + i)); [lia | exact Hm].
  Qed.

  (* [comment removed for export] *)
  Lemma rdn1_overlay_hull : forall M (a : word) b,
    in_hull A (bv_unsigned a) = false -> rdn segs M a 1 = Some [b] -> M a = Some b.
  Proof.
    intros M a b Hh H. cbn [rdn] in H.
    destruct (M a) as [b0|] eqn:Hm.
    - cbn in H. injection H as ->. reflexivity.
    - unfold seg_rom, memory_read in H. change (Z.of_N 1) with 1 in H. rewrite (SEGS_in_hull a Hh) in H. discriminate.
  Qed.

  Lemma word_to_le_bytes_1 : forall v, 0 <= v < 256 -> word_to_le_bytes 1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
  Proof.
    intros v Hv. unfold word_to_le_bytes. cbn [Z_to_le_bytes]. rewrite Z_to_bv_unsigned.
    rewrite (bv_wrap_small 64 v) by (change (bv_modulus 64) with (2 ^ 64); lia). reflexivity.
  Qed.

  Lemma shb_ok_sound : forall E M k a v,
    know_ok segs E M k -> shb_ok segs A k a v = true -> M (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
  Proof.
    intros E M k a v HK H. unfold shb_ok in H. apply andb_prop in H as [H Hc]. apply andb_prop in H as [Hh Ha0].
    apply negb_true_iff in Hh. apply Z.leb_le in Ha0.
    destruct (cell_ok_sound E M k a 1 v HK Hc) as (_ & Ha & _ & Hv & Hrd). change (2 ^ (8 * 1)) with 256 in Hv.
    change (Z.to_nat 1) with 1%nat in Hrd. rewrite word_to_le_bytes_1 in Hrd by lia.
    apply (rdn1_overlay_hull M (Z_to_bv 64 a) (Z_to_bv 8 v)); [|exact Hrd].
    rewrite u64_lit by lia. unfold in_hull. unfold in_hullb in Hh. exact Hh.
  Qed.

  (* [comment removed for export] *)
  Lemma kzx0_sound : forall E M k b off g,
    know_ok segs E M k -> flat_x k b off (ELit 1) = true -> kzx0 k b off g = true ->
    0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E g <= 2 ^ 64 /\
    forall i, 0 <= i < elenZ E g -> M (Z_to_bv 64 (estart E (SA b off) + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros E M k b off g HK Hf H. unfold kzx0 in H.
    assert (G : kzero_x k k b off g = true ->
              0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E g <= 2 ^ 64 /\
              forall i, 0 <= i < elenZ E g -> M (Z_to_bv 64 (estart E (SA b off) + i)) = Some (Z_to_bv 8 0))
      by (intros Hz; exact (kzero_ok_sound E M k b off g HK Hz)).
    destruct g as [z| | | | | | | ]; try exact (G H).
    destruct z as [|zp|zn]; try exact (G H).
    destruct (flat_x_sound segs E M k b off (ELit 1) HK Hf) as (F0 & F1 & _). rewrite elenZ_lit in F1 by lia.
    unfold elenZ. rewrite elenZ_lit by lia. split; [lia|]. split; [lia|]. intros i Hi. exfalso. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pg_cell_sound : forall E M k sdb sdk ne nlo nhi q8 pb pk,
    know_ok segs E M k -> bv_unsigned (edenot E (pg_count k ne nlo nhi)) = q8 -> pg_cell k sdb sdk ne nlo nhi = (pb, pk) ->
    0 <= sdk -> 0 <= q8 -> bv_unsigned (edenot E sdb) + sdk + q8 < 2 ^ 64 ->
    bv_unsigned (edenot E pb) + pk = bv_unsigned (edenot E sdb) + sdk + q8.
  Proof.
    intros E M k sdb sdk ne nlo nhi q8 pb pk HK Hg Hc Hsdk Hq8 Hb. unfold pg_cell in Hc.
    pose proof (u64_range (edenot E sdb)) as Rs.
    assert (GEN : forall g, bv_unsigned (edenot E g) = q8 -> (eadd sdb g, sdk) = (pb, pk) ->
              bv_unsigned (edenot E pb) + pk = bv_unsigned (edenot E sdb) + sdk + q8).
    { intros g Hg' Hc'. injection Hc' as <- <-. unfold eadd. rewrite mkAlu_denot, alu_add. unfold v_add. rewrite Hg'.
      rewrite u64_lit by lia. lia. }
    destruct (pg_count k ne nlo nhi) as [c| | | | | | | ] eqn:Hm; try exact (GEN _ Hg Hc).
    match type of Hc with (if ?g then _ else _) = _ => destruct g eqn:Hgd end; [|exact (GEN _ Hg Hc)].
    injection Hc as <- <-. cbn [edenot] in Hg. apply andb_prop in Hgd as [G0 G1]. apply Z.leb_le in G0. apply Z.ltb_lt in G1. unfold two64 in G1.
    rewrite u64_lit in Hg by lia. lia.
  Qed.
End Tests.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Place.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  #[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0) (only parsing).

  (* [comment removed for export] *)
  Lemma app_num_sound : forall E M k b off n, know_ok SEGS E M k -> app_num A k b off n = true ->
    4096 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 47
    /\ (estart E (SA b off) + elenZ E n <= AsFuzzContract.AS_LOWEND \/ AsFuzzContract.AS_HIGHBEG <= estart E (SA b off))
    /\ (estart E (SA b off) + elenZ E n <= AsFuzzContract.AS_IMGLO \/ XLN.XIMGHI A <= estart E (SA b off)).
  Proof.
    intros E M k b off n HK H. unfold app_num in H.
    destruct (xlo k b) as [lo|] eqn:Hlo; [|discriminate]. destruct (xhi k b) as [hi|] eqn:Hhi; [|discriminate].
    destruct (xhi k n) as [nh|] eqn:Hnh; [|discriminate].
    pose proof (xlo_sound SEGS E M k b lo HK Hlo) as L. pose proof (xhi_sound SEGS E M k b hi HK Hhi) as U.
    pose proof (xhi_sound SEGS E M k n nh HK Hnh) as N.
    (* [comment removed for export] *)
    assert (EH : estart E (SA b off) + elenZ E n <= XLN.app_end k b off n hi nh).
    { unfold XLN.app_end. unfold estart, elenZ. cbn [a_base a_off].
      destruct (base_range k b) as [[lo1 hi1]|] eqn:Hbr; [|lia].
      destruct (end_hi k b off n lo1 hi1 nh) as [e|] eqn:He; [|lia].
      pose proof (end_hi_sound SEGS E M k b off n lo1 hi1 nh e HK Hbr Hnh He) as HE.
      unfold estart, elenZ in HE. cbn [a_base a_off] in HE. lia. }
    cbv zeta in H. set (eh := XLN.app_end k b off n hi nh) in *.
    apply andb_prop in H as [H Himg]. apply andb_prop in H as [H Hsh]. apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [HA H1].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in HA.
    assert (HX1 : AsFuzzContract.AS_IMGHI <= XLN.XIMGHI A) by apply Z.le_max_l.
    assert (HX2 : XLN.XIMGHI A <= 2 ^ 47) by (unfold XLN.XIMGHI; apply Z.max_lub; [unfold AsFuzzContract.AS_IMGHI; lia | exact HA]).
    unfold estart, elenZ in EH |- *. cbn [a_base a_off] in EH |- *.
    split; [lia|]. split; [lia|]. split.
    - apply orb_prop in Hsh as [Hsh|Hsh]; [apply orb_prop in Hsh as [Hsh|Hsh]|].
      + apply Z.leb_le in Hsh. left. lia.
      + apply Z.leb_le in Hsh. right. lia.
      + pose proof (ranges_apart_x_sound SEGS E M k b off n (ELit 0) AsFuzzContract.AS_LOWEND
                      (ELit (AsFuzzContract.AS_HIGHBEG - AsFuzzContract.AS_LOWEND)) HK Hsh) as X.
        unfold estart, elenZ in X. cbn [a_base a_off edenot] in X.
        unfold AsFuzzContract.AS_LOWEND, AsFuzzContract.AS_HIGHBEG in *. rewrite !u64_lit in X by lia. lia.
    - apply orb_prop in Himg as [Himg|Himg]; [apply orb_prop in Himg as [Himg|Himg]|].
      + apply Z.leb_le in Himg. left. lia.
      + apply Z.leb_le in Himg. right. lia.
      + pose proof (ranges_apart_x_sound SEGS E M k b off n (ELit 0) AsFuzzContract.AS_IMGLO
                      (ELit (XLN.XIMGHI A - AsFuzzContract.AS_IMGLO)) HK Himg) as X.
        unfold estart, elenZ in X. cbn [a_base a_off edenot] in X.
        unfold AsFuzzContract.AS_IMGLO, AsFuzzContract.AS_IMGHI in *. rewrite !u64_lit in X by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma in_maps_sound : forall E cs R FULL model b off n, CSOK E cs R FULL model -> in_maps cs b off n = true ->
    estart E (SA b off) + elenZ E n <= alloc_top (m_vmmaps model).
  Proof.
    intros E cs R FULL model b off n HC H. unfold in_maps in H.
    apply existsb_exists in H as (m & Hin & Hm). apply andb_prop in Hm as [Hnf Hx]. apply negb_true_iff in Hnf.
    pose proof (xinside_sound SEGS E (Mr A argH E cs model FULL) (kn cs) b off n (am_base m) 0 (am_len m)
                  (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hx) as [I1 I2].
    pose proof (maps_match_In E (a_maps cs) _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hin Hnf) as Hmv.
    pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) _ Hmv) as (B1 & B2 & B3 & B4 & B5).
    cbn [amap_den fst snd] in B1, B2, B3, B4, B5.
    unfold estart, elenZ in I1, I2 |- *. cbn [a_base a_off] in I1, I2 |- *. lia.
  Qed.

  Lemma app_ok_sound : forall E cs R FULL model b off n, CSOK E cs R FULL model -> app_ok A cs b off n = true ->
    AsFuzzContract.appm (estart E (SA b off)) (elenZ E n) /\ estart E (SA b off) + elenZ E n <= alloc_top (m_vmmaps model).
  Proof.
    intros E cs R FULL model b off n HC H. unfold app_ok in H. apply andb_prop in H as [Hn Hm].
    destruct (app_num_sound E _ (kn cs) b off n (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hn) as (N1 & N2 & N3 & N4).
    pose proof (in_maps_sound E cs R FULL model b off n HC Hm) as M1.
    pose proof (u64_range (edenot E n)) as Rn. unfold elenZ in *.
    pose proof (Z.le_max_l AsFuzzContract.AS_IMGHI (img_hi A)) as HXl. unfold XLN.XIMGHI in N4.
    split; [|exact M1]. unfold AsFuzzContract.appm. repeat split; try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma app_ok_hull : forall E cs R FULL model b off n, CSOK E cs R FULL model -> app_ok A cs b off n = true ->
    estart E (SA b off) + elenZ E n <= AsFuzzContract.AS_IMGLO \/ img_hi A <= estart E (SA b off).
  Proof.
    intros E cs R FULL model b off n HC H. unfold app_ok in H. apply andb_prop in H as [Hn Hm].
    destruct (app_num_sound E _ (kn cs) b off n (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hn) as (N1 & N2 & N3 & N4).
    pose proof (Z.le_max_r AsFuzzContract.AS_IMGHI (img_hi A)) as HXr. unfold XLN.XIMGHI in N4. lia.
  Qed.

  Lemma heapcell_ok_sound : forall E cs R FULL model cb coff fb fk, CSOK E cs R FULL model -> heapcell_ok A cs cb coff fb fk = true ->
    AsFuzzContract.appm (estart E (SA cb coff)) 8 /\ estart E (SA cb coff) + 8 <= alloc_top (m_vmmaps model)
    /\ (estart E (SA cb coff) + 8 <= estart E (SA fb fk) \/ estart E (SA fb fk) + AsFuzzContract.FS_SIZE <= estart E (SA cb coff)).
  Proof.
    intros E cs R FULL model cb coff fb fk HC H. unfold heapcell_ok in H. apply andb_prop in H as [Ha Hap].
    destruct (app_ok_sound E cs R FULL model cb coff (ELit 8) HC Ha) as [P1 P2]. rewrite elenZ_lit' in P1, P2 by lia.
    pose proof (ranges_apart_x_sound SEGS E (Mr A argH E cs model FULL) (kn cs) cb coff (ELit 8) fb fk (ELit AsFuzzContract.FS_SIZE)
                  (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hap) as D.
    rewrite !elenZ_lit' in D by (unfold AsFuzzContract.FS_SIZE; lia).
    split; [exact P1|]. split; [exact P2 | exact D].
  Qed.
End Place.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
  Hypothesis NX0_sp : nx0_sp_ok nx0.
  Variable FS0 : Fs.Fs.
  #[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0) (only parsing).

  Lemma call_core_fp_cfg : forall (FP FP' : PropExec.FPState) cs E E' R FULL model T (ret : Z) sr2 k' nx2 regs' MR',
    CSOK E cs R FULL model ->
    fresh_ok nx0 cs = true ->
    env_agree (nxt cs) E E' ->
    CatSim.msteps SEGS (@mkst FP R (Z_to_bv 64 (pc cs)) (Mr A argH E cs model FULL) (seg_rom SEGS))
                       (@mkst FP' regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
    regs_ok E' sr2 regs' ->
    know_ok SEGS E' MR' k' ->
    (forall R' FULL' model',
        CSOK E' (with_ss cs (mk_ss ret sr2 k' nx2)) R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes_cfg SEGS (@APSC.cfg_fp FP' SEGS R' ret FULL' model') T) ->
    srealizes_cfg SEGS (@APSC.cfg_fp FP SEGS R (pc cs) FULL model) T.
  Proof.
    intros FP FP' cs E E' R FULL model T ret sr2 k' nx2 regs' MR' HC Hfresh Hag Hms HR' HK' Hk.
    destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    set (H := hid A argH E cs model).
    unfold APSC.cfg_fp.
    apply (srz_cfg_msteps_restricted_T SEGS H
             (H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high E cs model) SEGS_wx (allowA A E cs)
             (@mkst FP R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)) (@mkst FP' regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) model T
             (lazy_cover_cs SEGS A LIMIT (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) SINV argH FS0 nx0
                E cs R FULL model HC)
             (A_wf_allowA A (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) nx0 E cs)
             (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ HC)).
    - rewrite restrict_mkst. exact Hms.
    - intros model' Hinv' Hsame Hclean.
      set (FULL' := munrestrict H FULL MR').
      change (unrestrict H (ms_mem (@mkst FP R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS))) (@mkst FP' regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)))
        with (@mkst FP' regs' (Z_to_bv 64 ret) FULL' (seg_rom SEGS)).
      apply (Hk regs' FULL' model').
      + pose proof (cs_ok_agree SEGS A nx0 LIMIT SINV argH argH_agree SINV_agree NX0_sp FS0 E E' cs R FULL model Hag Hfresh HC) as HC1.
        pose proof (hid_agree A nx0 argH argH_agree (nxt cs) E E' cs model Hag Fle Fallow) as HH.
        eapply (cs_ok_frame SEGS A LIMIT SINV argH SINV_frame FS0 E' cs R FULL model _ regs' FULL' model' HC1 Hsame).
        * rewrite (allowA_agree A (nxt cs) E E' cs Hag Fallow). exact Hinv'.
        * exact HR'.
        * reflexivity.
        * cbn [s_know mk_ss]. unfold Mr. rewrite HH.
          fold H. unfold FULL'. rewrite (mrestrict_munrestrict_clean H FULL MR') by (intros a Ha; exact (Hclean a Ha)).
          exact HK'.
        * intros a Ha. rewrite HH in Ha.
          unfold FULL', munrestrict. fold H in Ha. rewrite Ha. reflexivity.
      + apply (same_but_materialized_frame _ _ Hsame).
  Qed.
End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u_elit : forall E z, 0 <= z < 2 ^ 64 -> bv_unsigned (edenot E (ELit z)) = z.
Proof. intros E z Hz. cbn [edenot]. apply u64_lit. exact Hz. Qed.
Lemma u_elenZ : forall E z, 0 <= z < 2 ^ 64 -> elenZ E (ELit z) = z.
Proof. intros E z Hz. unfold elenZ. apply u_elit. exact Hz. Qed.
Lemma xt_den_1 : forall E e c, xt_den E [(e, c)] = bv_unsigned (edenot E e) + c.
Proof. intros. cbn [xt_den]. apply Z.add_0_r. Qed.
Lemma Zdiv_mul_l : forall a b, 0 < b -> b * a / b = a.
Proof. intros a b Hb. rewrite Z.mul_comm. apply Z.div_mul. lia. Qed.
Lemma land7_mod : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma u_and7 : forall x : word, bv_unsigned (alu64 ALU_AND x (Z_to_bv 64 7)) = bv_unsigned x mod 8.
Proof. intros x. rewrite u_and64, u64_lit by lia. apply land7_mod. pose proof (u64_range x). lia. Qed.

(* [comment removed for export] *)
Fixpoint outsideE (E : env) (x : Z) (rs : list xregion) : Prop :=
  match rs with
  | [] => True
  | (b, off, n) :: rs' => (x < estart E (SA b off) \/ estart E (SA b off) + elenZ E n <= x) /\ outsideE E x rs'
  end.
Fixpoint insideb (E : env) (x : Z) (rs : list xregion) : bool :=
  match rs with
  | [] => false
  | (b, off, n) :: rs' => ((estart E (SA b off) <=? x) && (x <? estart E (SA b off) + elenZ E n)) || insideb E x rs'
  end.
Lemma insideb_false : forall E x rs, insideb E x rs = false <-> outsideE E x rs.
Proof.
  intros E x rs. induction rs as [|[[b off] n] rs IH]; cbn [insideb outsideE]; [tauto|].
  rewrite orb_false_iff, andb_false_iff, Z.leb_gt, Z.ltb_ge, IH. tauto.
Qed.

Lemma nin_rng : forall (x : word) b l, 0 <= b -> b < 2 ^ 64 -> (bv_unsigned x < b \/ b + l <= bv_unsigned x) -> ~ IF.in_rng x (Z_to_bv 64 b) l.
Proof. intros x b l H0 H1 H. unfold IF.in_rng. rewrite u64_lit by lia. lia. Qed.

Lemma bytes_of_mem : forall (M : word -> option byte) (k : nat) (d : Z),
  (forall i, 0 <= i < Z.of_nat k -> exists b, M (Z_to_bv 64 (d + i)) = Some b) ->
  exists bs : list byte, length bs = k /\ forall i, 0 <= i < Z.of_nat k -> M (Z_to_bv 64 (d + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
Proof.
  intros M k. induction k as [|k IH]; intros d Hd.
  - exists []. split; [reflexivity|]. intros i Hi. cbn in Hi. lia.
  - destruct (Hd 0 ltac:(lia)) as [b0 Hb0]. rewrite Z.add_0_r in Hb0.
    destruct (IH (d + 1)) as (bs & Hlen & Hbs).
    { intros i Hi. replace (d + 1 + i) with (d + (1 + i)) by lia. apply Hd. lia. }
    exists (b0 :: bs). split; [cbn; lia|]. intros i Hi.
    destruct (Z.eq_dec i 0) as [->|Hi0]; [rewrite Z.add_0_r; exact Hb0|].
    replace (d + i) with (d + 1 + (i - 1)) by lia. rewrite (Hbs (i - 1)) by lia.
    replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. reflexivity.
Qed.

Lemma ashdata_of_facts : forall (M : word -> option byte) d n qd q8 r8 base,
  d = 16 * qd -> n = 8 * q8 + r8 -> 0 <= r8 < 8 -> 0 <= q8 ->
  (forall i, 0 <= i < q8 -> M (Z_to_bv 64 (base + i)) = Some (Z_to_bv 8 0)) ->
  base = AsFuzzContract.AS_SB + 2 * qd ->
  (r8 = 0 \/ M (Z_to_bv 64 (base + q8)) = Some (Z_to_bv 8 r8)) ->
  AsFuzzContract.ashdata M d n.
Proof.
  intros M d n qd q8 r8 base Hd Hn Hr8 Hq8 Hz Hb Hlast g Hg1 Hg2.
  assert (Hdg : d / 8 = 2 * qd) by (rewrite Hd; rewrite <- (Z.div_mul (2 * qd) 8) by lia; f_equal; lia).
  rewrite Hdg in Hg1.
  unfold AsFuzzContract.as_shad_byte. rewrite (Z.mul_comm 8 g), Z.div_mul by lia.
  replace (AsFuzzContract.AS_SB + g) with (base + (g - 2 * qd)) by lia.
  destruct (Z.leb_spec ((g + 1) * 8) (d + n)) as [Hle|Hgt].
  - apply Hz. lia.
  - assert (Hj : g - 2 * qd = q8) by lia. rewrite Hj.
    assert (Hm : (d + n) mod 8 = r8).
    { rewrite Hd, Hn. replace (16 * qd + (8 * q8 + r8)) with (r8 + (2 * qd + q8) * 8) by lia.
      rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
    rewrite Hm. destruct Hlast as [Hr0|Hl]; [exfalso; lia | exact Hl].
Qed.

(* [comment removed for export] *)
Lemma zx1_strip_bytes : forall E e, word_to_le_bytes 1 (edenot E (zx1_strip e)) = word_to_le_bytes 1 (edenot E e).
Proof.
  intros E e. destruct e as [z|v|op e1 e2|op e1 e2|op e1 e2|op e1 e2|sx lo w e1|sx bk bi bn]; try reflexivity.
  destruct sx; [reflexivity|]. destruct lo as [|lo]; [|reflexivity]. destruct w as [|[|w]]; try reflexivity.
  cbn [zx1_strip]. cbn [edenot]. unfold ext_val, ext_Z. cbn [Z.of_nat N.of_nat Z.mul Z.pow Z.pow_pos Pos.iter Pos.mul].
  pose proof (u64_range (edenot E e1)) as R. set (x := bv_unsigned (edenot E e1)) in *.
  unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. fold x. cbn [Z.of_nat Z.mul]. rewrite Z.pow_0_r, Z.div_1_r. change (2 ^ 8) with 256.
  unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64).
  pose proof (Z.mod_pos_bound x 256 ltac:(lia)).
  change (2 ^ (8 * Z.of_nat 1)) with 256.
  rewrite (Z.mod_small (x mod 256) (2 ^ 64)) by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Section Helpers.
  Variable SEGS : list Segment.
  Variable A : atable.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis RW_ok : forall m (x : word), rw_lo A <= bv_unsigned x < rw_lo A + rw_len A -> wview SEGS m x <> None.

  (* [comment removed for export] *)
  Lemma pg_val_sound : forall E M k ne nhi e1 n,
    know_ok SEGS E M k -> pg_val_ok k ne nhi e1 = true -> bv_unsigned (edenot E ne) = n -> n <= nhi -> n mod 8 <> 0 ->
    edenot E e1 = Z_to_bv 64 (n mod 8).
  Proof.
    intros E M k ne nhi e1 n HK H Hn Hhi Hnz. unfold pg_val_ok in H. pose proof (u64_range (edenot E ne)) as Rn.
    pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Hr8.
    assert (Hand : edenot E (EAlu ALU_AND ne (ELit 7)) = Z_to_bv 64 (n mod 8)).
    { cbn [edenot]. apply bv_eq. rewrite u_and7. rewrite Hn. rewrite u64_lit; [reflexivity|lia]. }
    apply orb_prop in H as [H|Hrs].
    - apply orb_prop in H as [H|H].
      + destruct e1 as [z|v|op a1 a2|op a1 a2|op a1 a2|op a1 a2|sx lo w a1|sx bk bi bn]; try discriminate; destruct op; try discriminate;
          destruct a2 as [z7|v2|op2 a3 a4|op2 a3 a4|op2 a3 a4|op2 a3 a4|sx2 lo2 w2 a3|sx2 bk2 bi2 bn2]; try discriminate.
        apply andb_prop in H as [Hz7 He]. apply Z.eqb_eq in Hz7. subst z7. apply expr_eqb_eq in He. subst a1. exact Hand.
      + apply andb_prop in H as [He Hh]. apply expr_eqb_eq in He. subst e1. apply Z.leb_le in Hh.
        apply bv_eq. rewrite Hn. rewrite Z.mod_small by lia. rewrite u64_lit by lia. reflexivity.
    - rewrite <- Hand. apply (respell_ok_sound SEGS E M (KRange (EAlu ALU_AND ne (ELit 7)) 1 7 :: k)); [|exact Hrs].
      constructor; [|exact HK]. cbn [kentry_ok]. rewrite Hand. rewrite u64_lit by lia. lia.
  Qed.

  Lemma pg_lookup_sound : forall E M k sdb sdk ne nlo nhi e1 q8 n,
    know_ok SEGS E M k -> pg_lookup SEGS k sdb sdk ne nlo nhi = Some e1 ->
    bv_unsigned (edenot E (pg_count k ne nlo nhi)) = q8 -> bv_unsigned (edenot E ne) = n -> n <= nhi ->
    0 <= sdk -> 0 <= q8 -> bv_unsigned (edenot E sdb) + sdk + q8 < 2 ^ 64 ->
    let c := pg_cell k sdb sdk ne nlo nhi in
    estart E (SA (fst c) (snd c)) = bv_unsigned (edenot E sdb) + sdk + q8
    /\ flat E (SA (fst c) (snd c)) 1
    /\ (n mod 8 <> 0 -> edenot E e1 = Z_to_bv 64 (n mod 8))
    /\ rdn SEGS M (Z_to_bv 64 (bv_unsigned (edenot E sdb) + sdk + q8)) 1 = Some (word_to_le_bytes 1 (edenot E e1)).
  Proof.
    intros E M k sdb sdk ne nlo nhi e1 q8 n HK H Hg Hn Hhi Hsdk Hq8 Hb. unfold pg_lookup in H.
    destruct (pg_cell k sdb sdk ne nlo nhi) as [pb pk] eqn:Hc. cbn [fst snd].
    destruct (flat_x k pb pk (ELit 1)) eqn:Hf; [|discriminate].
    destruct (know_lookup SEGS k pb pk 1 false [] []) as [e sc hs|sc hs|] eqn:HLk; try discriminate.
    destruct sc; [|discriminate]. destruct (pg_val_ok k ne nhi (zx1_strip e)) eqn:Hv; [|discriminate]. injection H as <-.
    pose proof (pg_cell_sound SEGS E M k sdb sdk ne nlo nhi q8 pb pk HK Hg Hc Hsdk Hq8 Hb) as Hcell.
    destruct (flat_x_sound SEGS E M k pb pk (ELit 1) HK Hf) as (P0 & P1 & _). rewrite u_elit in P1 by lia.
    pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Hr8.
    destruct (lookup_piece SEGS E M k pb pk 1 e hs HK ltac:(lia) HLk ltac:(unfold flat; lia)) as (bs1 & Hrd1 & Hlen1 & Hbs1).
    subst bs1. rewrite <- (zx1_strip_bytes E e) in Hrd1.
    unfold estart in Hrd1, P0, P1 |- *. cbn [a_base a_off] in Hrd1, P0, P1 |- *.
    split; [exact Hcell|]. split; [unfold flat, estart; cbn [a_base a_off]; clear -P0 P1; lia|].
    split; [intros Hnz; exact (pg_val_sound E M k ne nhi (zx1_strip e) n HK Hv Hn Hhi Hnz)|].
    rewrite <- Hcell. exact Hrd1.
  Qed.

  (* [comment removed for export] *)
  Lemma store_ok_rw : forall n M a,
    rw_lo A <= a -> a + Z.of_nat n <= rw_lo A + rw_len A -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    store_ok SEGS M (Z_to_bv 64 a) n = true.
  Proof.
    induction n as [|n IH]; intros M a H1 H2 H3 H4; [reflexivity|].
    cbn [store_ok]. destruct (wview SEGS M (Z_to_bv 64 a)) as [b|] eqn:Hw.
    - destruct n as [|n']; [reflexivity|].
      replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)); [apply IH; cbn [Z.of_nat] in *; lia|].
      apply bv_eq. rewrite u_add1 by (rewrite u64_lit by lia; cbn [Z.of_nat] in *; lia). rewrite !u64_lit by lia. reflexivity.
    - exfalso. apply (RW_ok M (Z_to_bv 64 a)); [rewrite u64_lit by lia; lia | exact Hw].
  Qed.

  (* [comment removed for export] *)
  Lemma store_ok_present : forall n M a,
    store_ok SEGS M (Z_to_bv 64 a) n = true -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    (forall i, 0 <= i < Z.of_nat n -> in_hull A (a + i) = false) ->
    forall i, 0 <= i < Z.of_nat n -> M (Z_to_bv 64 (a + i)) <> None.
  Proof.
    induction n as [|n IH]; intros M a Hs H0 H64 Hh i Hi; [cbn in Hi; lia|].
    cbn [store_ok] in Hs. destruct (wview SEGS M (Z_to_bv 64 a)) as [b|] eqn:Hw; [|discriminate].
    destruct (Z.eq_dec i 0) as [->|Hi0].
    - rewrite Z.add_0_r. unfold wview in Hw. destruct (M (Z_to_bv 64 a)) as [b0|] eqn:Hm; [congruence|].
      rewrite (SEGS_in_hull (Z_to_bv 64 a)) in Hw; [discriminate|]. rewrite u64_lit by (cbn [Z.of_nat] in *; lia).
      rewrite <- (Z.add_0_r a). apply Hh. cbn [Z.of_nat] in *; lia.
    - destruct n as [|n']; [cbn in Hi; lia|].
      replace (a + i) with ((a + 1) + (i - 1)) by lia.
      apply (IH M (a + 1)); [| lia | cbn [Z.of_nat] in *; lia | intros j Hj; replace (a + 1 + j) with (a + (1 + j)) by lia; apply Hh; cbn [Z.of_nat] in *; lia | cbn [Z.of_nat] in *; lia].
      replace (Z_to_bv 64 (a + 1)) with (Z_to_bv 64 a + 1)%bv; [exact Hs|].
      apply bv_eq. rewrite u_add1 by (rewrite u64_lit by lia; cbn [Z.of_nat] in *; lia). rewrite !u64_lit by (cbn [Z.of_nat] in *; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn1_ext : forall (M M' : word -> option byte) (a : word), M' a = M a -> rdn SEGS M' a 1 = rdn SEGS M a 1.
  Proof. intros M M' a H. cbn [rdn]. rewrite H. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma xl_havoc_sound : forall E rs M M' k,
    know_ok SEGS E M k ->
    (forall x : word, outsideE E (bv_unsigned x) rs -> M' x = M x) ->
    mem_grows M M' ->
    know_ok SEGS E M' (xl_havoc k rs).
  Proof.
    intros E rs. induction rs as [|[[b off] n] rs IH]; intros M M' k HK Hout Hg; cbn [xl_havoc].
    - replace M' with M; [exact HK|]. apply functional_extensionality. intros x. symmetry. apply Hout. exact I.
    - set (M1 := fun x : word => if insideb E (bv_unsigned x) rs then M x else M' x).
      apply (IH M1 M').
      + apply (w_know_ok_havoc SEGS E M M1 k b off n HK).
        * intros x Hx. unfold M1. destruct (insideb E (bv_unsigned x) rs) eqn:Hi; [reflexivity|].
          apply Hout. split; [exact Hx|]. apply insideb_false. exact Hi.
        * intros x Hx. unfold M1. destruct (insideb E (bv_unsigned x) rs); [exact Hx | apply Hg; exact Hx].
      + intros x Hx. unfold M1. rewrite (proj2 (insideb_false E (bv_unsigned x) rs) Hx). reflexivity.
      + intros x Hx. unfold M1 in Hx. destruct (insideb E (bv_unsigned x) rs); [apply Hg; exact Hx | exact Hx].
  Qed.
End Helpers.

(* [comment removed for export] *)
#[local] Ltac in_list := cbn [In]; repeat (first [left; (reflexivity || (apply bv_eq; reflexivity)) | right]).
Lemma kept_ok_of_fuzz_kept : forall regs regs',
  (forall r, In r OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FuzzContract.fuzz_kept -> getr regs' r = getr regs r) -> kept_ok regs regs'.
Proof.
  intros regs regs' Hk r Hr0 Hnin. apply Hk.
  pose proof (AX2S.ridx_range r) as Hrr.
  assert (Hr : AX2.ridx r <> 0%nat).
  { intros X. apply Hr0. rewrite (reg_of_ridx r 0 X). apply bv_eq. reflexivity. }
  unfold AP.caller_saved in Hnin. cbn [In] in Hnin.
  assert (E : exists k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat /\ AX2.ridx r = k).
  { exists (AX2.ridx r). split; [|reflexivity]. cbn [In]. lia. }
  destruct E as (k & Hink & Hrk). rewrite (reg_of_ridx r k Hrk).
  cbn [In] in Hink. unfold OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.FuzzContract.fuzz_kept.
  repeat (destruct Hink as [<-|Hink]; [in_list|]). destruct Hink.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Node.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis SEGS_wr : segs_wr_ok SEGS.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
  Hypothesis NX0_sp : nx0_sp_ok nx0.
  Variable FS0 : Fs.Fs.
  (* [comment removed for export] *)
  Hypothesis SEGS_end : Forall (fun seg => Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= img_hi A) SEGS.
  Hypothesis RW_ok : forall m (x : word), rw_lo A <= bv_unsigned x < rw_lo A + rw_len A -> wview SEGS m x <> None.
  (* [comment removed for export] *)
  Hypothesis HULL_as : AsFuzzContract.AS_IMGLO <= img_lo A.
  Variable B : AsFuzzContract.as_abi.
  Hypothesis LIB : AsFuzzContract.as_fuzz_contract SEGS B.
  #[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0) (only parsing).

  Theorem XLnode_sound_fp : forall (FP : PropExec.FPState), FPI FP ->
    forall args cs cs' E R FULL model T,
      CSOK E cs R FULL model -> XLnode B SEGS A nx0 true args cs = Some cs' ->
      APSC.cont_cfg SEGS A nx0 LIMIT SINV argH FS0 FPI cs cs' E model T ->
      srealizes_cfg SEGS (@APSC.cfg_fp FP SEGS R (pc cs) FULL model) T.
  Proof.
    intros FP HFP args cs cs' E R FULL model T HC Hn Hk.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HKN.
    set (M := Mr A argH E cs model FULL) in *.
    unfold XLnode in Hn.
    destruct (Z.eqb (pc cs) (AsFuzzContract.aa_entry B)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
    destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
    destruct (reg_lit cs 4) as [tpv|] eqn:Htp; [|discriminate].
    destruct (Z.eqb tpv (AsFuzzContract.aa_tp B)) eqn:Htpv; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Htpv. subst tpv.
    destruct (word_at SEGS (kn cs) (ELit 0) (AsFuzzContract.aa_tp B)) as [F|] eqn:HF; [|discriminate].
    destruct (split_lit (reg cs 2)) as [ub uk] eqn:Hsu.
    destruct (split_lit (reg cs 10)) as [db dk] eqn:Hsd.
    destruct (split_lit F) as [fb fk] eqn:Hsf.
    destruct (split_lit (shx (kn cs) F)) as [hb hk] eqn:Hsh.
    destruct (split_lit (shx (kn cs) ub)) as [sub suk] eqn:Hssu.
    destruct (split_lit (shx (kn cs) (reg cs 10))) as [sdb sdk] eqn:Hssd.
    cbn [negb orb] in Hn.
    destruct (xl_checks B SEGS A cs (reg cs 2) (reg cs 10) (reg cs 11) F ub uk db dk fb fk hb hk sub suk sdb sdk) eqn:HX; [|discriminate].
    unfold xl_checks in HX.
    destruct (xlo (kn cs) (reg cs 11)) as [nlo|] eqn:Hnlo; [|discriminate].
    destruct (xhi (kn cs) (reg cs 11)) as [nhi|] eqn:Hnhi; [|discriminate].
    destruct (xlo (kn cs) (reg cs 2)) as [ulo|] eqn:Hulo; [|discriminate].
    destruct (xhi (kn cs) (reg cs 2)) as [uhi|] eqn:Huhi; [|discriminate].
    apply andb_prop in HX as [HX Gfs]. apply andb_prop in HX as [HX Gch]. apply andb_prop in HX as [HX Gimg].
    apply andb_prop in HX as [HX Gst]. apply andb_prop in HX as [HX Gar]. apply andb_prop in HX as [Gnum Gdat].
    (* [comment removed for export] *)
    unfold xl_nums in Gnum.
    apply andb_prop in Gnum as [Gnum N22]. apply andb_prop in Gnum as [Gnum N21]. apply andb_prop in Gnum as [Gnum N20].
    apply andb_prop in Gnum as [Gnum N19]. apply andb_prop in Gnum as [Gnum N18]. apply andb_prop in Gnum as [Gnum N17].
    apply andb_prop in Gnum as [Gnum N16]. apply andb_prop in Gnum as [Gnum N15]. apply andb_prop in Gnum as [Gnum N14].
    apply andb_prop in Gnum as [Gnum N13]. apply andb_prop in Gnum as [Gnum N12]. apply andb_prop in Gnum as [Gnum N11].
    apply andb_prop in Gnum as [Gnum N10]. apply andb_prop in Gnum as [Gnum N9]. apply andb_prop in Gnum as [Gnum N8].
    apply andb_prop in Gnum as [Gnum N7]. apply andb_prop in Gnum as [Gnum N6]. apply andb_prop in Gnum as [Gnum N5].
    apply andb_prop in Gnum as [Gnum N4]. apply andb_prop in Gnum as [Gnum N3]. apply andb_prop in Gnum as [N1 N2].
    apply Z.leb_le in N1. apply Z.ltb_lt in N2. apply Z.leb_le in N3. apply Z.eqb_eq in N4. apply Z.leb_le in N5. apply Z.ltb_lt in N6.
    apply Z.leb_le in N7. apply Z.ltb_lt in N8. apply Z.leb_le in N9. apply Z.leb_le in N10. apply Z.ltb_lt in N14.
    apply Z.ltb_lt in N16. apply Z.leb_le in N17. apply Z.leb_le in N18. apply Z.leb_le in N19. apply Z.leb_le in N20. apply Z.leb_le in N21.
    apply Z.eqb_eq in N22.
    set (D := AsFuzzContract.aa_depth B) in *.
    unfold AsFuzzContract.AS_SB in N10.
    (* [comment removed for export] *)
    destruct (ret_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model ret HC Hret) as (R1 & Hrok & Hret0).
    pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 2 HC ltac:(lia)) as R2.
    destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 4 (AsFuzzContract.aa_tp B) HC ltac:(lia) Htp) as [R4 _].
    pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
    pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 11 HC ltac:(lia)) as R11.
    set (spw := edenot E (reg cs 2)) in *. set (sp := bv_unsigned spw).
    set (dw := edenot E (reg cs 10)) in *. set (d := bv_unsigned dw).
    set (nw := edenot E (reg cs 11)) in *. set (n := bv_unsigned nw).
    set (Fw := edenot E F). set (fs := bv_unsigned Fw).
    pose proof (u64_range spw) as Rsp. pose proof (u64_range dw) as Rd. pose proof (u64_range nw) as Rn. pose proof (u64_range Fw) as Rfs.
    fold sp in Rsp. fold d in Rd. fold n in Rn. fold fs in Rfs.
    (* [comment removed for export] *)
    pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Bnlo. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Bnhi.
    pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hulo) as Bulo. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Huhi) as Buhi.
    fold spw sp in Bulo, Buhi. fold nw n in Bnlo, Bnhi.
    (* [comment removed for export] *)
    set (ceil := alloc_top (m_vmmaps model)).
    assert (Hceil : ceil <= sp - D).
    { pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN N15) as X. rewrite !xt_den_1 in X. fold spw sp in X.
      pose proof (co_sp _ _ _ _ _ _ _ _ _ _ _ HC) as [S1 _]. unfold ceil, alloc_top, stack_max_size. unfold STK_OFF in X. unfold uE in S1. lia. }
    assert (Hstklo : AsFuzzContract.AS_STKLO <= ceil).
    { pose proof (alloc_top_bound SEGS A LIMIT SINV argH FS0 E cs R FULL model HC) as [X _]. unfold ceil. unfold CEIL in X. lia. }
    (* [comment removed for export] *)
    assert (ALIGN : forall e m, m <= ealign (kn cs) e -> 0 <= m -> exists q, bv_unsigned (edenot E e) = 2 ^ m * q).
    { intros e m Hm Hm0. destruct (ealign_sound SEGS E M (kn cs) e HKN) as [[He0 He64] [q Hq]].
      exists (2 ^ (ealign (kn cs) e - m) * q). rewrite Hq.
      replace (ealign (kn cs) e) with ((ealign (kn cs) e - m) + m) at 1 by lia. rewrite Z.pow_add_r by lia. clear; lia. }
    destruct (ALIGN (reg cs 2) 4 N18 ltac:(clear; lia)) as [qsp Asp]. fold spw sp in Asp. change (2 ^ 4) with 16 in Asp.
    destruct (ALIGN (reg cs 10) 4 N19 ltac:(clear; lia)) as [qd Ad]. fold dw d in Ad. change (2 ^ 4) with 16 in Ad.
    destruct (ALIGN F 12 N20 ltac:(clear; lia)) as [qf Afs]. fold Fw fs in Afs. change (2 ^ 12) with 4096 in Afs.
    destruct (ALIGN ub 3 N21 ltac:(clear; lia)) as [qu Aub]. change (2 ^ 3) with 8 in Aub.
    apply Z.mod_divide in N22; [|clear; lia]. destruct N22 as [quk Huk].
    apply Z.mod_divide in N4; [|clear; lia]. destruct N4 as [qD HqD].
    clear ALIGN.
    assert (HD8 : D / 8 = qD) by (rewrite HqD; apply Z.div_mul; clear; lia).
    assert (Huk8 : (uk - D) / 8 = quk) by (rewrite Huk; apply Z.div_mul; clear; lia).
    assert (Hf8 : fs / 8 = 512 * qf) by (rewrite Afs; replace (4096 * qf) with (8 * (512 * qf)) by (clear; lia); apply Zdiv_mul_l; clear; lia).
    assert (Hd8 : d / 8 = 2 * qd) by (rewrite Ad; replace (16 * qd) with (8 * (2 * qd)) by (clear; lia); apply Zdiv_mul_l; clear; lia).
    assert (Hu8 : bv_unsigned (edenot E ub) / 8 = qu) by (rewrite Aub; apply Zdiv_mul_l; clear; lia).
    (* [comment removed for export] *)
    pose proof (w_split_lit_denot E _ ub uk Hsu) as Esu. fold spw in Esu. apply (f_equal bv_unsigned) in Esu. rewrite u_lit64a in Esu. fold sp in Esu.
    pose proof (w_split_lit_denot E _ db dk Hsd) as Esd. fold dw in Esd. apply (f_equal bv_unsigned) in Esd. rewrite u_lit64a in Esd. fold d in Esd.
    pose proof (w_split_lit_denot E _ fb fk Hsf) as Esf. fold Fw in Esf. apply (f_equal bv_unsigned) in Esf. rewrite u_lit64a in Esf. fold fs in Esf.
    assert (SHX : forall e, bv_unsigned (edenot E (shx (kn cs) e)) = (2147450880 + bv_unsigned (edenot E e) / 8) mod 2 ^ 64).
    { intros e. unfold shx, eadd. rewrite mkAlu_denot, alu_add. unfold v_add.
      rewrite (mkSrl_denot SEGS E M (kn cs) e 3 (Z_to_bv 64 3) HKN ltac:(rewrite u64_lit by (clear; lia); reflexivity)).
      rewrite alu_srl. unfold v_srl. rewrite (u64_lit 3) by (clear; lia). rewrite Z.shiftr_div_pow2 by (clear; lia).
      replace (2 ^ (3 mod 64)) with 8 by reflexivity.
      rewrite u_lit64a. cbn [edenot]. unfold AsFuzzContract.AS_SB. rewrite (u64_lit 2147450880) by (clear; lia).
      pose proof (u64_range (edenot E e)) as He.
      assert (He8 : 0 <= bv_unsigned (edenot E e) / 8 <= bv_unsigned (edenot E e)).
      { split; [apply Z.div_pos; clear -He; lia | apply Z.div_le_upper_bound; clear -He; lia]. }
      rewrite (u64_lit (bv_unsigned (edenot E e) / 8)) by (clear -He He8; lia). reflexivity. }
    pose proof (w_split_lit_denot E _ hb hk Hsh) as Esh. apply (f_equal bv_unsigned) in Esh. rewrite SHX, u_lit64a in Esh. fold Fw fs in Esh. rewrite Hf8 in Esh.
    pose proof (w_split_lit_denot E _ sub suk Hssu) as Essu. apply (f_equal bv_unsigned) in Essu. rewrite SHX, u_lit64a in Essu. rewrite Hu8 in Essu.
    pose proof (w_split_lit_denot E _ sdb sdk Hssd) as Essd. apply (f_equal bv_unsigned) in Essd. rewrite SHX, u_lit64a in Essd. fold dw d in Essd. rewrite Hd8 in Essd.
    clear SHX.
    (* [comment removed for export] *)
    unfold xl_stack in Gst. apply andb_prop in Gst as [Gwr Gsz].
    destruct (wr_ok_sound SEGS E M (kn cs) ub (uk - D) (ELit D) HKN Gwr) as (Wu0 & Wu1 & Wu2 & Wust).
    rewrite u_elenZ in Wu1, Wu2, Wust by (clear -N2 N3; lia).
    unfold estart in Wu0, Wu1, Wust. cbn [a_base a_off] in Wu0, Wu1, Wust.
    assert (Hsp : bv_unsigned (edenot E ub) + uk = sp).
    { assert (X : 0 <= bv_unsigned (edenot E ub) + uk < 2 ^ 64 \/ bv_unsigned (edenot E ub) + uk = 2 ^ 64) by (clear -Wu0 Wu1 N2; lia).
      destruct X as [X|X]; [rewrite Z.mod_small in Esu by exact X; clear -Esu; lia|].
      exfalso. rewrite X, Z.mod_same in Esu by (clear; lia). clear -Esu Bulo N17 N2. lia. }
    replace (bv_unsigned (edenot E ub) + (uk - D)) with (sp - D) in Wust, Wu0, Wu1 by (clear -Hsp; lia).
    (* [comment removed for export] *)
    unfold xl_arena in Gar.
    destruct (app_ok_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model fb fk (ELit AsFuzzContract.FS_SIZE) HC Gar) as [Aapp Aceil].
    rewrite u_elenZ in Aapp, Aceil by (unfold AsFuzzContract.FS_SIZE; clear; lia). fold ceil in Aceil.
    unfold AsFuzzContract.appm in Aapp. destruct Aapp as (Af1 & Af2 & Af3 & Af4 & Af5).
    unfold estart in Af1, Af3, Af4, Af5, Aceil. cbn [a_base a_off] in Af1, Af3, Af4, Af5, Aceil.
    assert (Hfs : bv_unsigned (edenot E fb) + fk = fs).
    { rewrite Z.mod_small in Esf by (unfold AsFuzzContract.FS_SIZE in *; clear -Af1 Af3; lia). clear -Esf; lia. }
    assert (EF : forall off, estart E (SA fb (fk + off)) = fs + off) by (intros off; unfold estart; cbn [a_base a_off]; clear -Hfs; lia).
    rewrite Hfs in Af1, Af3, Af4, Af5, Aceil.
    pose proof (app_ok_hull SEGS A LIMIT SINV argH FS0 E cs R FULL model fb fk (ELit AsFuzzContract.FS_SIZE) HC Gar) as Ahull.
    rewrite u_elenZ in Ahull by (unfold AsFuzzContract.FS_SIZE; clear; lia). unfold estart in Ahull. cbn [a_base a_off] in Ahull. rewrite Hfs in Ahull.
    (* [comment removed for export] *)
    destruct (flat_x_sound SEGS E M (kn cs) hb hk (ELit 1) HKN N11) as (Fh0 & Fh1 & _). rewrite u_elit in Fh1 by (clear; lia).
    unfold estart in Fh0, Fh1. cbn [a_base a_off] in Fh0, Fh1.
    assert (Hhb : bv_unsigned (edenot E hb) + hk = 2147450880 + 512 * qf).
    { rewrite (Z.mod_small (bv_unsigned (edenot E hb) + hk)) in Esh by (clear -Fh0 Fh1; lia).
      rewrite Z.mod_small in Esh by (unfold AsFuzzContract.FS_SIZE in *; clear -Afs Af1 Af3; lia). clear -Esh; lia. }
    assert (EH : forall off, estart E (SA hb (hk + off)) = 2147450880 + fs / 8 + off).
    { intros off. unfold estart; cbn [a_base a_off]. rewrite Hf8. clear -Hhb; lia. }
    clear Fh0 Fh1 Esh.
    (* [comment removed for export] *)
    destruct (flat_x_sound SEGS E M (kn cs) sub suk (ELit 1) HKN N12) as (Fs0 & Fs1 & _). rewrite u_elit in Fs1 by (clear; lia).
    unfold estart in Fs0, Fs1. cbn [a_base a_off] in Fs0, Fs1.
    pose proof (u64_range (edenot E ub)) as Rub.
    assert (Hsub : bv_unsigned (edenot E sub) + suk = 2147450880 + qu).
    { rewrite (Z.mod_small (bv_unsigned (edenot E sub) + suk)) in Essu by (clear -Fs0 Fs1; lia).
      rewrite Z.mod_small in Essu by (clear -Aub Rub; lia). clear -Essu; lia. }
    clear Fs0 Fs1 Essu.
    (* [comment removed for export] *)
    pose proof (Z.div_mod n 8 ltac:(clear; lia)) as Hn8. pose proof (Z.mod_pos_bound n 8 ltac:(clear; lia)) as Hr8.
    set (q8 := n / 8) in *. set (r8 := n mod 8) in *.
    assert (Hsrl : elenZ E (mkSrl (kn cs) (reg cs 11) 3) = q8).
    { unfold elenZ. rewrite (mkSrl_denot SEGS E M (kn cs) (reg cs 11) 3 (Z_to_bv 64 3) HKN ltac:(rewrite u64_lit by (clear; lia); reflexivity)).
      rewrite alu_srl. unfold v_srl. rewrite (u64_lit 3) by (clear; lia). rewrite Z.shiftr_div_pow2 by (clear; lia).
      replace (2 ^ (3 mod 64)) with 8 by reflexivity. fold nw n. rewrite u64_lit; [reflexivity | clear -Rn Hn8 Hr8; lia]. }
    assert (Hcnt : elenZ E (pg_count (kn cs) (reg cs 11) nlo nhi) = q8).
    { unfold pg_count. match goal with |- context [if ?c then _ else _] => destruct c eqn:Hpgc end; [|exact Hsrl].
      apply andb_prop in Hpgc as [Hpc1 Hpc2]. apply Z.eqb_eq in Hpc1. apply Z.leb_le in Hpc2.
      pose proof (Z.div_le_mono nlo n 8 ltac:(clear; lia) Bnlo) as D1. pose proof (Z.div_le_mono n nhi 8 ltac:(clear; lia) Bnhi) as D2.
      pose proof (Z.div_pos nlo 8 Hpc2 ltac:(clear; lia)) as D0.
      assert (D3 : nhi / 8 < 2 ^ 64) by (apply Z.div_lt_upper_bound; [clear; lia | clear -N14 Bnhi Bnlo Hpc2; lia]).
      rewrite u_elenZ by (clear -D0 D3 Hpc1; lia). subst q8. clear -Hpc1 D1 D2. lia. }
    assert (DATA :
      (0 < n -> AsFuzzContract.appm d n /\ (d + n <= ceil /\ (d + n <= fs \/ fs + AsFuzzContract.FS_SIZE <= d)))
      /\ (exists bs : list byte, Z.of_nat (length bs) = n /\
            forall i, 0 <= i < n -> M (Z_to_bv 64 (d + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)))
      /\ AsFuzzContract.ashdata M d n).
    { unfold xl_data in Gdat. destruct (Z.eqb_spec nhi 0) as [Hn0|Hn0].
      - assert (Hnz : n = 0) by (clear -Hn0 Bnlo Bnhi N1; lia). split; [intros; exfalso; clear -Hnz H; lia|]. split.
        + exists []. split; [cbn; clear -Hnz; lia|]. intros; exfalso; clear -Hnz H; lia.
        + intros g Hg1 Hg2. exfalso. rewrite Hd8 in Hg1. clear -Hg1 Hg2 Ad Hnz. lia.
      - cbn [orb] in Gdat, N13.
        apply andb_prop in Gdat as [Gdat Gpg]. apply andb_prop in Gdat as [Gdat Gkz]. apply andb_prop in Gdat as [Gdat Gcov].
        apply andb_prop in Gdat as [Gapp Gap].
        destruct (app_ok_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model db dk (reg cs 11) HC Gapp) as [Dapp Dceil].
        unfold elenZ in Dapp, Dceil. fold nw n in Dapp, Dceil. fold ceil in Dceil.
        pose proof (app_ok_hull SEGS A LIMIT SINV argH FS0 E cs R FULL model db dk (reg cs 11) HC Gapp) as Dhull. unfold elenZ in Dhull. fold nw n in Dhull.
        destruct (xcover_sound SEGS A SEGS_in_hull E M (kn cs) db dk (reg cs 11) HKN Gcov) as (X0 & X1 & Xb).
        { intros i Hi. unfold elenZ in Hi. fold nw n in Hi. unfold in_hull. apply andb_false_iff.
          destruct Dhull as [Dx|Dx];
            [left; apply Z.leb_gt | right; apply Z.ltb_ge]; clear -Dx HULL_as Hi; unfold AsFuzzContract.AS_IMGLO in *; lia. }
        unfold elenZ in X1, Xb. fold nw n in X1, Xb.
        destruct (kzx0_sound SEGS E M (kn cs) sdb sdk _ HKN N13 Gkz) as (Z0 & Z1 & Zb). rewrite Hcnt in Z1, Zb.
        destruct (flat_x_sound SEGS E M (kn cs) sdb sdk (ELit 1) HKN N13) as (Fd0 & Fd1 & _). rewrite u_elit in Fd1 by (clear; lia).
        unfold estart in X0, X1, Xb, Z0, Z1, Zb, Fd0, Fd1, Dapp, Dceil. cbn [a_base a_off] in X0, X1, Xb, Z0, Z1, Zb, Fd0, Fd1, Dapp, Dceil.
        assert (Hsdb : bv_unsigned (edenot E sdb) + sdk = 2147450880 + 2 * qd).
        { rewrite (Z.mod_small (bv_unsigned (edenot E sdb) + sdk)) in Essd by (clear -Fd0 Fd1; lia).
          rewrite Z.mod_small in Essd by (clear -Ad Rd; lia). clear -Essd; lia. }
        assert (Hdd : bv_unsigned (edenot E db) + dk = d).
        { unfold AsFuzzContract.appm in Dapp. rewrite Z.mod_small in Esd by (clear -Dapp Rn; lia). clear -Esd; lia. }
        rewrite Hdd in Dapp, Dceil, Xb.
        split; [|split].
        + intros Hn1. split; [exact Dapp|]. split; [exact Dceil|].
          pose proof (ranges_apart_x_sound SEGS E M (kn cs) db dk (reg cs 11) fb fk (ELit AsFuzzContract.FS_SIZE) HKN Gap) as Dap.
          unfold estart, elenZ in Dap. cbn [a_base a_off] in Dap. fold nw n in Dap.
          rewrite (u_elit E AsFuzzContract.FS_SIZE) in Dap by (unfold AsFuzzContract.FS_SIZE; clear; lia). clear -Dap Hdd Hfs. lia.
        + destruct (Z.eq_dec n 0) as [Hz|Hz].
          { exists []. split; [cbn; clear -Hz; lia|]. intros; exfalso; clear -Hz H; lia. }
          destruct (bytes_of_mem M (Z.to_nat n) d) as (bs & Hlen & Hbs).
          { intros i Hi. apply Xb. clear -Hi Rn; lia. }
          exists bs. split; [clear -Hlen Rn; lia|]. intros i Hi. apply Hbs. clear -Hi Rn; lia.
        + apply (ashdata_of_facts M d n qd q8 r8 (bv_unsigned (edenot E sdb) + sdk) Ad ltac:(clear -Hn8; lia) Hr8
                   ltac:(subst q8; apply Z.div_pos; clear -Rn; lia) Zb Hsdb).
          (* [comment removed for export] *)
          unfold pgran_ok in Gpg. apply orb_prop in Gpg as [Gpg|Hk1b]; [apply orb_prop in Gpg as [Gpg|Gpgp]; [apply orb_prop in Gpg as [Hal3|Hk1a]|]|].
          { left. apply Z.leb_le in Hal3. destruct (ealign_sound SEGS E M (kn cs) (reg cs 11) HKN) as [_ [qn Hqn]].
            fold nw n in Hqn.
            assert (exists q3, n = 8 * q3) as [q3 Hq3].
            { exists (2 ^ (ealign (kn cs) (reg cs 11) - 3) * qn). rewrite Hqn.
              replace (ealign (kn cs) (reg cs 11)) with ((ealign (kn cs) (reg cs 11) - 3) + 3) at 1 by (clear; lia).
              rewrite Z.pow_add_r by (clear -Hal3; lia). change (2 ^ 3) with 8. clear; lia. }
            subst r8. rewrite Hq3. rewrite Z.mul_comm. apply Z_mod_mult. }
          { left. destruct (xhi (kn cs) (EAlu ALU_AND (reg cs 11) (ELit 7))) as [h|] eqn:Hxh; [|discriminate].
            apply Z.eqb_eq in Hk1a. subst h. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hxh) as Bh. cbn [edenot] in Bh. fold nw in Bh.
            rewrite u_and7 in Bh. fold n in Bh. subst r8. clear -Bh Hr8. lia. }
          2:{ apply andb_prop in Hk1b as [Hsdk0 HLp]. apply Z.leb_le in Hsdk0.
            destruct (pg_lookup SEGS (kn cs) sdb sdk (reg cs 11) nlo nhi) as [e1|] eqn:HPL; [|discriminate].
            assert (Hq8r : 0 <= q8 <= n) by (subst q8; split; [apply Z.div_pos | apply Z.div_le_upper_bound]; clear -Rn; lia).
            pose proof (u64_range (edenot E sdb)) as Rsdb.
            destruct (pg_lookup_sound SEGS E M (kn cs) sdb sdk (reg cs 11) nlo nhi e1 q8 n HKN HPL
                        ltac:(unfold elenZ in Hcnt; exact Hcnt) ltac:(fold nw; fold n; reflexivity) Bnhi Hsdk0 ltac:(clear -Hq8r; lia)
                        ltac:(clear -Hsdb Hsdk0 Hq8r Rn Bnhi N14 Ad Rd Rsdb; lia))
              as (Hcell & Hflc & Hval & Hrd1).
            fold r8 in Hval, Hrd1.
            destruct (Z.eq_dec r8 0) as [Hr0|Hnz]; [left; exact Hr0|right].
            rewrite (Hval Hnz), (word_to_le_bytes_1 r8) in Hrd1 by (clear -Hr8; lia).
            apply (rdn1_overlay_hull SEGS A SEGS_in_hull M _ _); [|exact Hrd1].
            rewrite u64_lit by (clear -Hsdb Ad Rd Hq8r Rn Bnhi N14; lia).
            unfold in_hull. apply andb_false_iff. right. apply Z.ltb_ge. clear -Hsdb N10 Ad Rd Hq8r Bnhi N14. lia. }
          rename Gpgp into Gpg.
          apply andb_prop in Gpg as [Heq Gpg]. apply Z.eqb_eq in Heq. assert (Hnl : n = nlo) by (clear -Heq Bnlo Bnhi; lia).
          apply orb_prop in Gpg as [Hm0|Gpg].
          { left. apply Z.eqb_eq in Hm0. subst r8. rewrite Hnl. exact Hm0. }
          right. apply andb_prop in Gpg as [Hflp HLp].
          destruct (know_lookup SEGS (kn cs) sdb (sdk + nlo / 8) 1 false [] []) as [e sc hs|sc hs|] eqn:HLk; try discriminate.
          destruct e; try discriminate. destruct sc; [|discriminate]. apply Z.eqb_eq in HLp. subst z.
          destruct (flat_x_sound SEGS E M (kn cs) sdb (sdk + nlo / 8) (ELit 1) HKN Hflp) as (P0 & P1 & _). rewrite u_elit in P1 by (clear; lia).
          destruct (lookup_piece SEGS E M (kn cs) sdb (sdk + nlo / 8) 1 (ELit (nlo mod 8)) hs HKN ltac:(clear; lia) HLk ltac:(unfold flat; clear -P0 P1; lia))
            as (bs1 & Hrd1 & Hlen1 & Hbs1).
          cbn [edenot] in Hbs1. rewrite (word_to_le_bytes_1 (nlo mod 8)) in Hbs1 by (subst r8; rewrite <- Hnl; clear -Hr8; lia). subst bs1.
          unfold estart in Hrd1. cbn [a_base a_off] in Hrd1.
          replace (bv_unsigned (edenot E sdb) + (sdk + nlo / 8)) with (bv_unsigned (edenot E sdb) + sdk + q8) in Hrd1 by (subst q8; rewrite Hnl; clear; lia).
          subst r8. replace (n mod 8) with (nlo mod 8) by (rewrite Hnl; reflexivity).
          apply (rdn1_overlay_hull SEGS A SEGS_in_hull M _ _); [|exact Hrd1].
          assert (Hq8r : 0 <= q8 <= n) by (subst q8; split; [apply Z.div_pos | apply Z.div_le_upper_bound]; clear -Rn; lia).
          rewrite u64_lit by (clear -Hsdb Ad Rd Hq8r Rn Bnhi N14; lia).
          unfold in_hull. apply andb_false_iff. right. apply Z.ltb_ge. clear -Hsdb N10 Ad Rd Hq8r Bnhi N14. lia. }
    destruct DATA as (Dplace & (bs & Hbslen & Hbs) & Dsh).
    (* [comment removed for export] *)
    destruct (kzero_ok_sound SEGS E M (kn cs) sub (suk + (uk - D) / 8) (ELit (D / 8)) HKN Gsz) as (Sz0 & Sz1 & Szb).
    rewrite HD8 in Sz1, Szb. rewrite u_elenZ in Sz1, Szb by (clear -N2 N3 HqD; lia). rewrite Huk8 in Sz0, Sz1, Szb.
    assert (Hspd8 : (sp - D) / 8 = qu + quk).
    { replace (sp - D) with ((qu + quk) * 8) by (clear -Hsp Aub Huk; lia). apply Z.div_mul. clear; lia. }
    unfold estart in Sz0, Sz1, Szb. cbn [a_base a_off] in Sz0, Sz1, Szb.
    replace (bv_unsigned (edenot E sub) + (suk + quk)) with (2147450880 + (sp - D) / 8) in Szb by (clear -Hspd8 Hsub; lia).
    (* [comment removed for export] *)
    unfold xl_img in Gimg.
    apply andb_prop in Gimg as [Gimg I10]. apply andb_prop in Gimg as [Gimg I9]. apply andb_prop in Gimg as [Gimg I8].
    apply andb_prop in Gimg as [Gimg I7]. apply andb_prop in Gimg as [Gimg I6]. apply andb_prop in Gimg as [Gimg I5].
    apply andb_prop in Gimg as [Gimg I4]. apply andb_prop in Gimg as [Gimg I3]. apply andb_prop in Gimg as [I1 I2].
    apply Z.leb_le in I1. apply Z.leb_le in I2.
    unfold in_hullb in I4. apply andb_prop in I4 as [_ I4]. apply Z.ltb_lt in I4.
    assert (Hgw : store_ok SEGS M (Z_to_bv 64 (AsFuzzContract.aa_gfool B)) 4 = true).
    { apply (store_ok_rw SEGS A RW_ok); cbn [Z.of_nat]; clear -I1 I2 N9 N10 I4; lia. }
    destruct (store_ok_rdn SEGS SEGS_wr 4 M (Z_to_bv 64 (AsFuzzContract.aa_gfool B))) as (gbs & Hgrd & _);
      [rewrite u64_lit; cbn [Z.of_nat]; clear -N9 N10 I4; lia | exact Hgw |].
    (* [comment removed for export] *)
    assert (Hsegs : forall i, sp - D <= i < sp ->
              Forall (fun seg => i < Z.of_N (seg_base seg) \/ Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= i) SEGS).
    { intros i Hi. apply Forall_forall. intros seg Hin. right.
      pose proof (proj1 (Forall_forall _ _) SEGS_end seg Hin) as Hs. cbn beta in Hs.
      destruct HULL_ok as (_ & _ & _ & Hkhi). unfold KHI in Hkhi. clear -Hs Hkhi Hi Hceil Hstklo. lia. }
    (* [comment removed for export] *)
    assert (Hro : forall lo hi i, In (lo, hi) (AsFuzzContract.aa_ro B) -> lo <= i < hi -> M (Z_to_bv 64 i) = None).
    { intros lo hi i Hin Hi. pose proof (proj1 (forallb_forall _ _) I5 (lo, hi) Hin) as Hc. cbn [fst snd] in Hc.
      exact (img_cov_sound SEGS E M (kn cs) lo hi HKN Hc i Hi). }
    (* [comment removed for export] *)
    assert (Hc64 : forall a v, In (a, v) (AsFuzzContract.aa_c64 B) -> AsFuzzContract.acell SEGS M a 8 v).
    { intros a v Hin. pose proof (proj1 (forallb_forall _ _) I6 (a, v) Hin) as Hc. cbn [fst snd] in Hc.
      destruct (cell_ok_sound SEGS E M (kn cs) a 8 v HKN Hc) as (_ & _ & _ & _ & Hrd). exact Hrd. }
    assert (Hc32 : forall a v, In (a, v) (AsFuzzContract.aa_c32 B) -> AsFuzzContract.acell SEGS M a 4 v).
    { intros a v Hin. pose proof (proj1 (forallb_forall _ _) I7 (a, v) Hin) as Hc. cbn [fst snd] in Hc.
      destruct (cell_ok_sound SEGS E M (kn cs) a 4 v HKN Hc) as (_ & _ & _ & _ & Hrd). exact Hrd. }
    assert (Hc8 : forall a v, In (a, v) (AsFuzzContract.aa_c8 B) -> AsFuzzContract.acell SEGS M a 1 v).
    { intros a v Hin. pose proof (proj1 (forallb_forall _ _) I8 (a, v) Hin) as Hc. cbn [fst snd] in Hc.
      destruct (cell_ok_sound SEGS E M (kn cs) a 1 v HKN Hc) as (_ & _ & _ & _ & Hrd). exact Hrd. }
    assert (Hr64 : forall a, In a (AsFuzzContract.aa_r64 B) -> AsFuzzContract.areadable SEGS M a 8).
    { intros a Hin. pose proof (proj1 (forallb_forall _ _) I9 a Hin) as Hc.
      destruct (rd8_ok_sound SEGS E M (kn cs) (ELit 0) a HKN Hc) as (R0a & _ & w & Hrd).
      unfold estart in R0a, Hrd. cbn [a_base a_off edenot] in R0a, Hrd. rewrite (u64_lit 0) in R0a, Hrd by (clear; lia).
      rewrite Z.add_0_l in Hrd. exists (word_to_le_bytes 8 w). exact Hrd. }
    assert (Hshb : forall a v, In (a, v) (AsFuzzContract.aa_shb B) -> M (Z_to_bv 64 a) = Some (Z_to_bv 8 v)).
    { intros a v Hin. pose proof (proj1 (forallb_forall _ _) I10 (a, v) Hin) as Hc. cbn [fst snd] in Hc.
      exact (shb_ok_sound SEGS A SEGS_in_hull E M (kn cs) a v HKN Hc). }
    (* [comment removed for export] *)
    unfold xl_chains in Gch. apply andb_prop in Gch as [Gts Gdt].
    destruct (word_at SEGS (kn cs) (ELit 0) (AsFuzzContract.aa_tsdv B)) as [ctxe|] eqn:Hctx; [|discriminate].
    destruct (split_lit ctxe) as [cb ck] eqn:Hsc.
    apply andb_prop in Gts as [Hhc Gts].
    destruct (word_at SEGS (kn cs) cb (ck + 152)) as [thre|] eqn:Hthr; [|discriminate].
    destruct (split_lit thre) as [tb tk] eqn:Hst.
    apply andb_prop in Gts as [Gts Hr56]. apply andb_prop in Gts as [Gts Hr48]. apply andb_prop in Gts as [Hh48 Hh56].
    destruct (word_at SEGS (kn cs) (ELit 0) (AsFuzzContract.aa_tp B + 8)) as [dtlse|] eqn:Hdtls; [|discriminate].
    destruct (split_lit dtlse) as [eb ek] eqn:Hse.
    destruct (xlo (kn cs) dtlse) as [tlo|] eqn:Htlo; [|discriminate]. destruct (xhi (kn cs) dtlse) as [thi|] eqn:Hthi; [|discriminate].
    apply andb_prop in Gdt as [Gdt Hv24m]. apply andb_prop in Gdt as [Gdt Hh24]. apply andb_prop in Gdt as [Htlo' Hthi'].
    apply Z.ltb_lt in Htlo'. apply Z.ltb_lt in Hthi'.
    destruct (word_at SEGS (kn cs) eb (ek + 24)) as [v24e|] eqn:Hv24; [|discriminate].
    destruct (xlo (kn cs) v24e) as [vlo|] eqn:Hvlo; [|discriminate]. apply Z.ltb_lt in Hv24m.
    (* [comment removed for export] *)
    destruct (word_at_sound SEGS E M (kn cs) (ELit 0) (AsFuzzContract.aa_tsdv B) ctxe HKN Hctx) as (_ & _ & Wctx).
    unfold estart in Wctx. cbn [a_base a_off edenot] in Wctx. rewrite (u64_lit 0), Z.add_0_l in Wctx by (clear; lia).
    set (ctx := edenot E ctxe) in *.
    pose proof (w_split_lit_denot E _ cb ck Hsc) as Ectx. fold ctx in Ectx. apply (f_equal bv_unsigned) in Ectx. rewrite u_lit64a in Ectx.
    destruct (heapcell_ok_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model cb (ck + 152) fb fk HC Hhc) as (Hc1 & Hc2 & Hc3).
    unfold estart in Hc1, Hc2, Hc3. cbn [a_base a_off] in Hc1, Hc2, Hc3. fold ceil in Hc2. rewrite Hfs in Hc3.
    assert (Uctx : bv_unsigned (edenot E cb) + ck = bv_unsigned ctx).
    { unfold AsFuzzContract.appm in Hc1. rewrite Z.mod_small in Ectx by (clear -Hc1; lia). clear -Ectx; lia. }
    destruct (word_at_sound SEGS E M (kn cs) cb (ck + 152) thre HKN Hthr) as (_ & _ & Wthr).
    unfold estart in Wthr. cbn [a_base a_off] in Wthr.
    set (thr := edenot E thre) in *.
    pose proof (w_split_lit_denot E _ tb tk Hst) as Ethr. fold thr in Ethr. apply (f_equal bv_unsigned) in Ethr. rewrite u_lit64a in Ethr.
    destruct (heapcell_ok_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model tb (tk + 48) fb fk HC Hh48) as (Ht1 & Ht2 & Ht3).
    destruct (heapcell_ok_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model tb (tk + 56) fb fk HC Hh56) as (Ht4 & Ht5 & Ht6).
    unfold estart in Ht1, Ht2, Ht3, Ht4, Ht5, Ht6. cbn [a_base a_off] in Ht1, Ht2, Ht3, Ht4, Ht5, Ht6.
    fold ceil in Ht2, Ht5. rewrite Hfs in Ht3, Ht6.
    assert (Uthr : bv_unsigned (edenot E tb) + tk = bv_unsigned thr).
    { unfold AsFuzzContract.appm in Ht1. rewrite Z.mod_small in Ethr by (clear -Ht1; lia). clear -Ethr; lia. }
    destruct (rd8_ok_sound SEGS E M (kn cs) tb (tk + 48) HKN Hr48) as (_ & _ & t48 & W48).
    destruct (rd8_ok_sound SEGS E M (kn cs) tb (tk + 56) HKN Hr56) as (_ & _ & t56 & W56).
    unfold estart in W48, W56. cbn [a_base a_off] in W48, W56.
    (* [comment removed for export] *)
    destruct (word_at_sound SEGS E M (kn cs) (ELit 0) (AsFuzzContract.aa_tp B + 8) dtlse HKN Hdtls) as (_ & _ & Wdtls).
    unfold estart in Wdtls. cbn [a_base a_off edenot] in Wdtls. rewrite (u64_lit 0), Z.add_0_l in Wdtls by (clear; lia).
    set (dtls := edenot E dtlse) in *.
    pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Htlo) as Btlo. pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hthi) as Bthi. fold dtls in Btlo, Bthi.
    pose proof (w_split_lit_denot E _ eb ek Hse) as Edtls. fold dtls in Edtls. apply (f_equal bv_unsigned) in Edtls. rewrite u_lit64a in Edtls.
    destruct (heapcell_ok_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model eb (ek + 24) fb fk HC Hh24) as (He1 & He2 & He3).
    unfold estart in He1, He2, He3. cbn [a_base a_off] in He1, He2, He3. fold ceil in He2. rewrite Hfs in He3.
    assert (Udtls : bv_unsigned (edenot E eb) + ek = bv_unsigned dtls).
    { unfold AsFuzzContract.appm in He1. rewrite Z.mod_small in Edtls by (clear -He1; lia). clear -Edtls; lia. }
    destruct (word_at_sound SEGS E M (kn cs) eb (ek + 24) v24e HKN Hv24) as (_ & _ & Wv24).
    unfold estart in Wv24. cbn [a_base a_off] in Wv24.
    pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hvlo) as Bvlo.
    (* [comment removed for export] *)
    unfold xl_fs in Gfs.
    apply andb_prop in Gfs as [Gfs F16]. apply andb_prop in Gfs as [Gfs F15]. apply andb_prop in Gfs as [Gfs F14].
    apply andb_prop in Gfs as [Gfs F13]. apply andb_prop in Gfs as [Gfs F12]. apply andb_prop in Gfs as [Gfs F11].
    apply andb_prop in Gfs as [Gfs F10]. apply andb_prop in Gfs as [Gfs F9]. apply andb_prop in Gfs as [Gfs F8].
    apply andb_prop in Gfs as [Gfs F7]. apply andb_prop in Gfs as [Gfs F6]. apply andb_prop in Gfs as [Gfs F5].
    apply andb_prop in Gfs as [Gfs F4]. apply andb_prop in Gfs as [Gfs F3]. apply andb_prop in Gfs as [F1 F2].
    destruct (rd8_ok_sound SEGS E M (kn cs) fb (fk + AsFuzzContract.FS_HINT0) HKN F1) as (_ & _ & h0 & Wh0r). rewrite EF in Wh0r.
    destruct (rd8_ok_sound SEGS E M (kn cs) fb (fk + AsFuzzContract.FS_HINT5) HKN F2) as (_ & _ & h5 & Wh5r). rewrite EF in Wh5r.
    destruct (know_lookup SEGS (kn cs) fb (fk + AsFuzzContract.FS_SSL) 8 false [] []) as [se ssc shs|ssc shs|] eqn:HLssl; try discriminate.
    destruct se; try discriminate. destruct ssc; [|discriminate]. apply Z.eqb_eq in F3. subst z.
    destruct (flat_x_sound SEGS E M (kn cs) fb (fk + AsFuzzContract.FS_SSL) (ELit 8) HKN F4) as (Q0 & Q1 & _). rewrite u_elit in Q1 by (clear; lia).
    destruct (lookup_piece SEGS E M (kn cs) fb (fk + AsFuzzContract.FS_SSL) 8 (ELit 20) shs HKN ltac:(clear; lia) HLssl ltac:(unfold flat; clear -Q0 Q1; lia))
      as (bssl & Wssl & _ & Hbssl). rewrite EF in Wssl. cbn [edenot] in Hbssl. subst bssl.
    destruct (know_lookup SEGS (kn cs) fb (fk + AsFuzzContract.FS_NEEDSGC) 1 false [] []) as [ge gsc ghs|gsc ghs|] eqn:HLgc; try discriminate.
    destruct ge; try discriminate. destruct gsc; [|discriminate]. apply Z.eqb_eq in F5. subst z.
    destruct (flat_x_sound SEGS E M (kn cs) fb (fk + AsFuzzContract.FS_NEEDSGC) (ELit 1) HKN F6) as (G0 & G1 & _). rewrite u_elit in G1 by (clear; lia).
    destruct (lookup_piece SEGS E M (kn cs) fb (fk + AsFuzzContract.FS_NEEDSGC) 1 (ELit 0) ghs HKN ltac:(clear; lia) HLgc ltac:(unfold flat; clear -G0 G1; lia))
      as (bgc & Wgc & _ & Hbgc). rewrite EF in Wgc. cbn [edenot] in Hbgc. subst bgc.
    destruct (kzero_ok_sound SEGS E M (kn cs) fb (fk + AsFuzzContract.FS_FLAGS0) (ELit AsFuzzContract.FS_FLAGS0_LEN) HKN F7) as (_ & _ & Zf0). rewrite EF in Zf0.
    rewrite u_elenZ in Zf0 by (unfold AsFuzzContract.FS_FLAGS0_LEN; clear; lia).
    destruct (kzero_ok_sound SEGS E M (kn cs) fb (fk + AsFuzzContract.FS_FLAGS5) (ELit AsFuzzContract.FS_FLAGS5_LEN) HKN F8) as (_ & _ & Zf5). rewrite EF in Zf5.
    rewrite u_elenZ in Zf5 by (unfold AsFuzzContract.FS_FLAGS5_LEN; clear; lia).
    destruct (wr_ok_sound SEGS E M (kn cs) fb (fk + AsFuzzContract.FS_HINT0) (ELit 8) HKN F9) as (_ & _ & _ & Wr0). rewrite EF in Wr0. rewrite u_elenZ in Wr0 by (clear; lia).
    destruct (wr_ok_sound SEGS E M (kn cs) fb (fk + AsFuzzContract.FS_HINT5) (ELit 8) HKN F10) as (_ & _ & _ & Wr5). rewrite EF in Wr5. rewrite u_elenZ in Wr5 by (clear; lia).
    destruct (wr_ok_sound SEGS E M (kn cs) fb (fk + AsFuzzContract.FS_FLAGS0) (ELit AsFuzzContract.FS_FLAGS0_LEN) HKN F11) as (_ & _ & _ & Wrf0). rewrite EF in Wrf0.
    rewrite u_elenZ in Wrf0 by (unfold AsFuzzContract.FS_FLAGS0_LEN; clear; lia).
    destruct (wr_ok_sound SEGS E M (kn cs) fb (fk + AsFuzzContract.FS_FLAGS5) (ELit AsFuzzContract.FS_FLAGS5_LEN) HKN F12) as (_ & _ & _ & Wrf5). rewrite EF in Wrf5.
    rewrite u_elenZ in Wrf5 by (unfold AsFuzzContract.FS_FLAGS5_LEN; clear; lia).
    destruct (wr_ok_sound SEGS E M (kn cs) fb (fk + AsFuzzContract.FS_FRAMES0) (ELit AsFuzzContract.FS_FRAMES_LEN) HKN F13) as (_ & _ & _ & Wrr0). rewrite EF in Wrr0.
    rewrite u_elenZ in Wrr0 by (unfold AsFuzzContract.FS_FRAMES_LEN; clear; lia).
    destruct (wr_ok_sound SEGS E M (kn cs) fb (fk + AsFuzzContract.FS_FRAMES5) (ELit AsFuzzContract.FS_FRAMES_LEN) HKN F14) as (_ & _ & _ & Wrr5). rewrite EF in Wrr5.
    rewrite u_elenZ in Wrr5 by (unfold AsFuzzContract.FS_FRAMES_LEN; clear; lia).
    destruct (wr_ok_sound SEGS E M (kn cs) hb (hk + AsFuzzContract.FS_FRAMES0 / 8) (ELit AsFuzzContract.FS_SHFRAMES_LEN) HKN F15) as (_ & _ & _ & Wrs0). rewrite EH in Wrs0.
    rewrite u_elenZ in Wrs0 by (unfold AsFuzzContract.FS_SHFRAMES_LEN; clear; lia).
    destruct (wr_ok_sound SEGS E M (kn cs) hb (hk + AsFuzzContract.FS_FRAMES5 / 8) (ELit AsFuzzContract.FS_SHFRAMES_LEN) HKN F16) as (_ & _ & _ & Wrs5). rewrite EH in Wrs5.
    rewrite u_elenZ in Wrs5 by (unfold AsFuzzContract.FS_SHFRAMES_LEN; clear; lia).
    (* [comment removed for export] *)
    destruct (word_at_sound SEGS E M (kn cs) (ELit 0) (AsFuzzContract.aa_tp B) F HKN HF) as (_ & _ & WF).
    unfold estart in WF. cbn [a_base a_off edenot] in WF. rewrite (u64_lit 0), Z.add_0_l in WF by (clear; lia). fold Fw in WF.
    (* [comment removed for export] *)
    replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) in R2 by (apply bv_eq; vm_compute; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 4)) with (4%bv : bv 5) in R4 by (apply bv_eq; vm_compute; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in R10 by (apply bv_eq; vm_compute; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in R11 by (apply bv_eq; vm_compute; reflexivity).
    replace (Z_to_bv 5 1) with (1%bv : bv 5) in R1 by (apply bv_eq; vm_compute; reflexivity).
    rewrite <- (Z_to_bv_bv_unsigned 64 nw) in R11. fold n in R11.
    assert (Hfs8a : (fs + 36864) / 8 = fs / 8 + 4608).
    { rewrite Hf8, Afs. replace (4096 * qf + 36864) with (8 * (512 * qf + 4608)) by (clear; lia). apply Zdiv_mul_l. clear; lia. }
    assert (Hfs8b : (fs + 5279744) / 8 = fs / 8 + 659968).
    { rewrite Hf8, Afs. replace (4096 * qf + 5279744) with (8 * (512 * qf + 659968)) by (clear; lia). apply Zdiv_mul_l. clear; lia. }
    (* [comment removed for export] *)
    specialize (LIB (fp_to_info FP HFP) R M (seg_rom SEGS) (Z_to_bv 64 ret) spw dw n bs fs h0 h5 ctx thr t48 t56 dtls (edenot E v24e) ceil).
    cbn zeta in LIB. fold D in LIB.
    specialize (LIB R1 Hrok R2 R4 R10 R11).
    specialize (LIB ltac:(clear -Rn Bnhi N14; lia) Hbslen).
    specialize (LIB ltac:(fold sp; rewrite Asp, Z.mul_comm; apply Z_mod_mult) ltac:(fold d; rewrite Ad, Z.mul_comm; apply Z_mod_mult)).
    specialize (LIB Hstklo ltac:(fold sp; exact Hceil) ltac:(fold sp; clear -N16 Buhi; lia)).
    specialize (LIB ltac:(fold d; exact Dplace)).
    specialize (LIB ltac:(unfold AsFuzzContract.appm; clear -Af1 Af2 Af3 Af4 Af5; repeat split; assumption) Aceil
                    ltac:(rewrite Afs, Z.mul_comm; apply Z_mod_mult)).
    specialize (LIB ltac:(fold d; exact Hbs) ltac:(fold d; exact Dsh)).
    specialize (LIB ltac:(fold sp; exact Wust) ltac:(fold sp; exact Hsegs)).
    specialize (LIB ltac:(fold sp; intros i Hi; apply Szb; rewrite HD8 in Hi; exact Hi)).
    specialize (LIB Hgw ltac:(exists gbs; exact Hgrd) Hro Hc64 Hc32 Hc8 Hr64 Hshb).
    specialize (LIB Wctx ltac:(unfold AsFuzzContract.heap_cell_ok, AsFuzzContract.appm in *; rewrite <- Uctx; clear -Hc1 Hc2 Hc3; lia)).
    specialize (LIB ltac:(rewrite <- Uctx, <- Z.add_assoc; exact Wthr)).
    specialize (LIB ltac:(unfold AsFuzzContract.heap_cell_ok, AsFuzzContract.appm in *; rewrite <- Uthr; clear -Ht1 Ht2 Ht3; lia)
                    ltac:(unfold AsFuzzContract.heap_cell_ok, AsFuzzContract.appm in *; rewrite <- Uthr; clear -Ht4 Ht5 Ht6; lia)).
    specialize (LIB ltac:(rewrite <- Uthr, <- Z.add_assoc; exact W48) ltac:(rewrite <- Uthr, <- Z.add_assoc; exact W56)).
    specialize (LIB Wdtls ltac:(clear -Btlo Bthi Htlo' Hthi'; lia)).
    specialize (LIB ltac:(unfold AsFuzzContract.heap_cell_ok, AsFuzzContract.appm in *; rewrite <- Udtls; clear -He1 He2 He3; lia)).
    specialize (LIB ltac:(rewrite <- Udtls, <- Z.add_assoc; exact Wv24) ltac:(clear -Bvlo Hv24m; lia)).
    specialize (LIB ltac:(unfold AsFuzzContract.acell; rewrite Z.add_0_r; fold fs; unfold fs; rewrite (Z_to_bv_bv_unsigned 64 Fw); exact WF)).
    specialize (LIB Wh0r Wh5r Wssl Wgc Zf0 Zf5 Wr0 Wr5 Wrf0 Wrf5 Wrr0 Wrr5).
    replace (2147450880 + fs / 8 + AsFuzzContract.FS_FRAMES0 / 8) with (AsFuzzContract.AS_SB + (fs + AsFuzzContract.FS_FRAMES0) / 8) in Wrs0
      by (unfold AsFuzzContract.FS_FRAMES0, AsFuzzContract.AS_SB; change (36864 / 8) with 4608; rewrite Hfs8a; clear; lia).
    replace (2147450880 + fs / 8 + AsFuzzContract.FS_FRAMES5 / 8) with (AsFuzzContract.AS_SB + (fs + AsFuzzContract.FS_FRAMES5) / 8) in Wrs5
      by (unfold AsFuzzContract.FS_FRAMES5, AsFuzzContract.AS_SB; change (5279744 / 8) with 659968; rewrite Hfs8b; clear; lia).
    specialize (LIB Wrs0 Wrs5).
    destruct LIB as (fpi' & regs' & mem' & Hms & Ha0 & Hkept & Hfm & Hz0' & Hz5').
    (* [comment removed for export] *)
    destruct Hfm as [Hout Hgrow].
    assert (Bfs : 4096 <= fs /\ fs + 11571200 <= 2 ^ 47) by (unfold AsFuzzContract.FS_SIZE in *; clear -Af1 Af3; lia).
    assert (Bq : fs / 8 = 512 * qf /\ fs = 4096 * qf) by (clear -Hf8 Afs; split; assumption).
    assert (HOUT : forall x : word, outsideE E (bv_unsigned x) (xl_mods B ub uk fb fk hb hk) -> mem' x = M x).
    { intros x Hx. apply Hout.
      cbn [outsideE xl_mods] in Hx. destruct Hx as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & _).
      rewrite EF in O3, O4, O5, O6, O7, O8. rewrite EH in O9, O10.
      unfold estart in O1, O2. cbn [a_base a_off edenot] in O1, O2. rewrite (u64_lit 0), Z.add_0_l in O2 by (clear; lia).
      rewrite u_elenZ in O1 by (clear -N2 N3; lia). rewrite u_elenZ in O2 by (clear; lia).
      rewrite u_elenZ in O3 by (clear; lia). rewrite u_elenZ in O4 by (clear; lia).
      unfold AsFuzzContract.FS_HINT0, AsFuzzContract.FS_HINT5, AsFuzzContract.FS_FLAGS0, AsFuzzContract.FS_FLAGS0_LEN, AsFuzzContract.FS_FLAGS5,
        AsFuzzContract.FS_FLAGS5_LEN, AsFuzzContract.FS_FRAMES0, AsFuzzContract.FS_FRAMES5, AsFuzzContract.FS_FRAMES_LEN, AsFuzzContract.FS_SHFRAMES_LEN in *.
      rewrite u_elenZ in O5 by (clear; lia). rewrite u_elenZ in O6 by (clear; lia). rewrite u_elenZ in O7 by (clear; lia).
      rewrite u_elenZ in O8 by (clear; lia). rewrite u_elenZ in O9 by (clear; lia). rewrite u_elenZ in O10 by (clear; lia).
      change (36864 / 8) with 4608 in O9. change (5279744 / 8) with 659968 in O10.
      unfold AsFuzzContract.as_mod. fold D. unfold AsFuzzContract.FS_HINT0, AsFuzzContract.FS_HINT5, AsFuzzContract.FS_FLAGS0, AsFuzzContract.FS_FLAGS0_LEN,
        AsFuzzContract.FS_FLAGS5, AsFuzzContract.FS_FLAGS5_LEN, AsFuzzContract.FS_FRAMES0, AsFuzzContract.FS_FRAMES5, AsFuzzContract.FS_FRAMES_LEN,
        AsFuzzContract.FS_SHFRAMES_LEN, AsFuzzContract.AS_SB.
      rewrite Hfs8a, Hfs8b. fold sp. cbn [IF.outside].
      split; [apply nin_rng; clear -O1 Hsp Hceil Hstklo N16 Buhi N2 N3; lia|].
      split; [apply nin_rng; clear -O2 N9 N10 I4; lia|].
      split; [apply nin_rng; clear -O3 Bfs; lia|].
      split; [apply nin_rng; clear -O4 Bfs; lia|].
      split; [apply nin_rng; clear -O5 Bfs; lia|].
      split; [apply nin_rng; clear -O6 Bfs; lia|].
      split; [apply nin_rng; clear -O7 Bfs; lia|].
      split; [apply nin_rng; clear -O8 Bfs; lia|].
      split; [apply nin_rng; clear -O9 Bfs Bq; lia|].
      split; [apply nin_rng; clear -O10 Bfs Bq; lia|].
      exact I. }
    (* [comment removed for export] *)
    unfold after_call in Hn.
    match type of Hn with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
    apply andb_prop in Hc as [Hc Hrvv]. apply andb_prop in Hc as [Hfresh Hkv].
    injection Hn as <-.
    destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    set (E' := ext_call E (nxt cs) regs').
    pose proof (ext_call_agree E (nxt cs) regs') as Hag. fold E' in Hag.
    eapply (call_core_fp_cfg SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree NX0_sp FS0
              FP (fp_of_info fpi') cs E E' R FULL model T ret _ _ _ regs' mem' HC Hfresh Hag).
    - rewrite Hpc. rewrite <- (mkst_to_info FP HFP), <- (mkst_of_info fpi'). apply msteps_of_banked. exact Hms.
    - apply (regs_after_call E _ R regs' (nxt cs) (Some (ELit 0)) (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) Fsr (kept_ok_of_fuzz_kept R regs' Hkept)).
      split; [exact Hrvv | exact Ha0].
    - eapply know_ok_agree'; [exact Hag | exact Hkv |].
      (* [comment removed for export] *)
      assert (Hq8r : 0 <= q8 <= n) by (subst q8; split; [apply Z.div_pos | apply Z.div_le_upper_bound]; clear -Rn; lia).
      assert (Hin_arena : forall z, fs <= z < fs + AsFuzzContract.FS_SIZE -> in_hull A z = false).
      { intros z Hz. unfold in_hull. apply andb_false_iff.
        destruct Ahull as [X|X]; [left; apply Z.leb_gt | right; apply Z.ltb_ge];
          unfold AsFuzzContract.FS_SIZE, AsFuzzContract.AS_IMGLO in *; clear -X HULL_as Hz; lia. }
      unfold xl_post_kn. constructor; [|constructor; [|constructor; [|constructor; [|apply Forall_app; split]]]].
      + (* [comment removed for export] *)
        cbn [kentry_ok]. rewrite EF. rewrite u_elenZ by (unfold AsFuzzContract.FS_FLAGS0_LEN; clear; lia). split; [|exact Hz0'].
        unfold flat. rewrite EF. unfold AsFuzzContract.FS_FLAGS0, AsFuzzContract.FS_FLAGS0_LEN. clear -Bfs. lia.
      + (* [comment removed for export] *)
        cbn [kentry_ok]. rewrite EF. rewrite u_elenZ by (unfold AsFuzzContract.FS_FLAGS5_LEN; clear; lia). split; [|exact Hz5'].
        unfold flat. rewrite EF. unfold AsFuzzContract.FS_FLAGS5, AsFuzzContract.FS_FLAGS5_LEN. clear -Bfs. lia.
      + (* [comment removed for export] *)
        cbn [kentry_ok]. rewrite EF. rewrite u_elenZ by (clear; lia).
        split; [unfold flat; rewrite EF; unfold AsFuzzContract.FS_HINT0; clear -Bfs; lia|].
        intros i Hi. apply Hgrow.
        apply (store_ok_present SEGS A SEGS_in_hull 8 M (fs + AsFuzzContract.FS_HINT0) Wr0);
          [unfold AsFuzzContract.FS_HINT0; clear -Bfs; lia | unfold AsFuzzContract.FS_HINT0; cbn [Z.of_nat]; clear -Bfs; lia | | cbn [Z.of_nat]; exact Hi].
        intros j Hj. apply Hin_arena. unfold AsFuzzContract.FS_HINT0, AsFuzzContract.FS_SIZE. cbn [Z.of_nat] in Hj. clear -Hj Bfs. lia.
      + (* [comment removed for export] *)
        cbn [kentry_ok]. rewrite EF. rewrite u_elenZ by (clear; lia).
        split; [unfold flat; rewrite EF; unfold AsFuzzContract.FS_HINT5; clear -Bfs; lia|].
        intros i Hi. apply Hgrow.
        apply (store_ok_present SEGS A SEGS_in_hull 8 M (fs + AsFuzzContract.FS_HINT5) Wr5);
          [unfold AsFuzzContract.FS_HINT5; clear -Bfs; lia | unfold AsFuzzContract.FS_HINT5; cbn [Z.of_nat]; clear -Bfs; lia | | cbn [Z.of_nat]; exact Hi].
        intros j Hj. apply Hin_arena. unfold AsFuzzContract.FS_HINT5, AsFuzzContract.FS_SIZE. cbn [Z.of_nat] in Hj. clear -Hj Bfs. lia.
      + (* [comment removed for export] *)
        assert (Hdn8 : (d + n) / 8 = 2 * qd + q8).
        { symmetry. apply Z.div_unique with r8; [left; exact Hr8 | rewrite Ad, Hn8; clear; ring]. }
        assert (SHOUT : forall x : word, 0 < n -> 2147450880 + 2 * qd <= bv_unsigned x <= 2147450880 + 2 * qd + q8 -> mem' x = M x).
        { intros x Hn0 Hx. destruct (Dplace Hn0) as (Dap & Dhi & Dar). apply Hout.
          unfold AsFuzzContract.as_mod. fold D. unfold AsFuzzContract.FS_HINT0, AsFuzzContract.FS_HINT5, AsFuzzContract.FS_FLAGS0, AsFuzzContract.FS_FLAGS0_LEN,
            AsFuzzContract.FS_FLAGS5, AsFuzzContract.FS_FLAGS5_LEN, AsFuzzContract.FS_FRAMES0, AsFuzzContract.FS_FRAMES5, AsFuzzContract.FS_FRAMES_LEN,
            AsFuzzContract.FS_SHFRAMES_LEN, AsFuzzContract.AS_SB.
          rewrite Hfs8a, Hfs8b. fold sp. cbn [IF.outside].
          assert (X44 : 2 * qd + q8 < 2 ^ 44) by (clear -Dhi Hceil Buhi N16 Ad Hn8 Hr8 N2; lia).
          unfold AsFuzzContract.FS_SIZE, AsFuzzContract.AS_LOWEND, AsFuzzContract.AS_HIGHBEG in Af4, Dar.
          split; [apply nin_rng; clear -Ad Rd Hq8r Hx X44 Hceil Hstklo N2 Buhi N16; lia|].
          split; [apply nin_rng; clear -Ad Rd Hq8r Hx N9 N10 I4; lia|].
          split; [apply nin_rng; clear -Ad Rd Hq8r Hx X44 Bfs Af4; lia|].
          split; [apply nin_rng; clear -Ad Rd Hq8r Hx X44 Bfs Af4; lia|].
          split; [apply nin_rng; clear -Ad Rd Hq8r Hx X44 Bfs Af4; lia|].
          split; [apply nin_rng; clear -Ad Rd Hq8r Hx X44 Bfs Af4; lia|].
          split; [apply nin_rng; clear -Ad Rd Hq8r Hx X44 Bfs Af4; lia|].
          split; [apply nin_rng; clear -Ad Rd Hq8r Hx X44 Bfs Af4; lia|].
          split; [apply nin_rng; clear -Ad Rd Hq8r Hx Bfs Bq Dar Ad Hn8 Hr8 Rn Hdn8; lia|].
          split; [apply nin_rng; clear -Ad Rd Hq8r Hx Bfs Bq Dar Ad Hn8 Hr8 Rn Hdn8; lia|].
          exact I. }
        unfold xl_dre. destruct (Z.eqb_spec nhi 0) as [Hn0|Hn0]; [constructor|].
        unfold xl_data in Gdat. rewrite (proj2 (Z.eqb_neq nhi 0) Hn0) in Gdat. cbn [orb] in N13, Gdat.
        apply andb_prop in Gdat as [Gdat Gpg]. apply andb_prop in Gdat as [Gdat Gkz].
        destruct (kzx0_sound SEGS E M (kn cs) sdb sdk _ HKN N13 Gkz) as (Z0 & Z1 & Zb). rewrite Hcnt in Z1, Zb.
        destruct (flat_x_sound SEGS E M (kn cs) sdb sdk (ELit 1) HKN N13) as (Fd0 & Fd1 & _). rewrite u_elit in Fd1 by (clear; lia).
        unfold estart in Z0, Z1, Zb, Fd0, Fd1. cbn [a_base a_off] in Z0, Z1, Zb, Fd0, Fd1.
        assert (Hsdb : bv_unsigned (edenot E sdb) + sdk = 2147450880 + 2 * qd).
        { rewrite (Z.mod_small (bv_unsigned (edenot E sdb) + sdk)) in Essd by (clear -Fd0 Fd1; lia).
          rewrite Z.mod_small in Essd by (clear -Ad Rd; lia). clear -Essd; lia. }
        apply Forall_app. split.
        { (* [comment removed for export] *)
          lazymatch goal with |- Forall ?P _ => assert (ZG : P (KZero (SA sdb sdk) (pg_count (kn cs) (reg cs 11) nlo nhi))) end.
          { cbn [kentry_ok]. rewrite Hcnt. unfold estart. cbn [a_base a_off].
            split; [unfold flat; unfold estart; cbn [a_base a_off]; clear -Z0 Z1 Hq8r Fd0 Fd1; lia|].
            intros i Hi. rewrite (SHOUT (Z_to_bv 64 (bv_unsigned (edenot E sdb) + sdk + i))); [apply Zb; exact Hi | clear -Hi Hq8r; lia |].
            rewrite u64_lit by (clear -Z0 Z1 Hi; lia). clear -Hsdb Hi Hq8r. lia. }
          generalize ZG. generalize (pg_count (kn cs) (reg cs 11) nlo nhi). intros g ZG'.
          destruct g as [[|zp|zn]| | | | | | | ]; (constructor; [exact ZG' | constructor]) || constructor. }
        apply Forall_app. split.
        { (* [comment removed for export] *)
          match goal with |- Forall _ (if ?c then _ else _) => destruct c eqn:Hpl; [|constructor] end.
          apply andb_prop in Hpl as [Hpl HLp]. apply andb_prop in Hpl as [Hpl Hflp]. apply andb_prop in Hpl as [Heq Hm8].
          apply Z.eqb_eq in Heq. apply negb_true_iff in Hm8. apply Z.eqb_neq in Hm8.
          assert (Hnl : n = nlo) by (clear -Heq Bnlo Bnhi; lia).
          destruct (know_lookup SEGS (kn cs) sdb (sdk + nlo / 8) 1 false [] []) as [e sc hs|sc hs|] eqn:HLk; try discriminate.
          destruct e; try discriminate. destruct sc; [|discriminate]. apply Z.eqb_eq in HLp. subst z.
          destruct (flat_x_sound SEGS E M (kn cs) sdb (sdk + nlo / 8) (ELit 1) HKN Hflp) as (P0 & P1 & _). rewrite u_elit in P1 by (clear; lia).
          destruct (lookup_piece SEGS E M (kn cs) sdb (sdk + nlo / 8) 1 (ELit (nlo mod 8)) hs HKN ltac:(clear; lia) HLk ltac:(unfold flat; clear -P0 P1; lia))
            as (bs1 & Hrd1 & Hlen1 & Hbs1).
          constructor; [|constructor]. cbn [kentry_ok]. split; [clear; lia|]. split; [unfold flat; clear -P0 P1; cbn [Z.of_nat]; lia|].
          rewrite Hbs1, adenot_SA, <- Hrd1. apply rdn1_ext. apply SHOUT; [clear -Hnl Hm8 Hn8 Hr8 Rn Hq8r; subst; lia|].
          unfold estart in P0, P1 |- *. cbn [a_base a_off] in P0, P1 |- *.
          rewrite u64_lit by (clear -P0 P1; lia).
          replace (nlo / 8) with q8 by (subst q8; rewrite Hnl; reflexivity). clear -Hsdb Hq8r. lia. }
        { (* [comment removed for export] *)
          match goal with |- Forall _ (if ?c then _ else _) => destruct c eqn:Hps; [|constructor] end.
          apply andb_prop in Hps as [Hnpos Hsdk0]. apply Z.leb_le in Hsdk0.
          assert (Hn0' : 0 < n).
          { apply orb_prop in Hnpos as [Hnpos|Hnpos]; [apply Z.ltb_lt in Hnpos; clear -Hnpos Bnlo; lia|].
            destruct (xlo (kn cs) (EAlu ALU_AND (reg cs 11) (ELit 7))) as [lo7|] eqn:Hx7; [|discriminate]. apply Z.ltb_lt in Hnpos.
            pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hx7) as B7. cbn [edenot] in B7. fold nw in B7. rewrite u_and7 in B7. fold n in B7.
            clear -B7 Hnpos Hn8 Hr8 Rn. subst r8. lia. }
          clear Hnpos.
          destruct (pg_lookup SEGS (kn cs) sdb sdk (reg cs 11) nlo nhi) as [e1|] eqn:HPL; [|constructor].
          pose proof (u64_range (edenot E sdb)) as Rsdb.
          destruct (pg_lookup_sound SEGS E M (kn cs) sdb sdk (reg cs 11) nlo nhi e1 q8 n HKN HPL
                      ltac:(unfold elenZ in Hcnt; exact Hcnt) ltac:(fold nw; fold n; reflexivity) Bnhi Hsdk0 ltac:(clear -Hq8r; lia)
                      ltac:(clear -Hsdb Hsdk0 Hq8r Rn Bnhi N14 Ad Rd Rsdb; lia))
            as (Hcell & Hflc & Hval & Hrd1).
          constructor; [|constructor]. cbn [kentry_ok]. split; [clear; lia|]. split; [exact Hflc|].
          rewrite adenot_SA, Hcell. rewrite <- Hrd1. apply rdn1_ext. apply SHOUT; [exact Hn0'|].
          rewrite u64_lit by (clear -Hsdb Hsdk0 Hq8r Rn Bnhi N14 Ad Rd Rsdb; lia). clear -Hsdb Hq8r. lia. }
      + apply (xl_havoc_sound SEGS E _ M mem' (kn cs) HKN); [exact HOUT | exact Hgrow].
    - intros R' FULL' model' HC' Hfs'.
      apply (Hk (fp_of_info fpi') (FPI_of_info fpi') E' R' FULL' model'); [| exact HC' | exact Hfs'].
      split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
  Qed.
End Node.

(* [comment removed for export] *)
Section Hook.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis SEGS_wr : segs_wr_ok SEGS.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
  Hypothesis NX0_sp : nx0_sp_ok nx0.
  Variable FS0 : Fs.Fs.
  Hypothesis SEGS_end : Forall (fun seg => Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= img_hi A) SEGS.
  Hypothesis RW_ok : forall m (x : word), rw_lo A <= bv_unsigned x < rw_lo A + rw_len A -> wview SEGS m x <> None.
  Hypothesis HULL_as : AsFuzzContract.AS_IMGLO <= img_lo A.
  Variable B : AsFuzzContract.as_abi.
  Hypothesis LIB : AsFuzzContract.as_fuzz_contract SEGS B.

  Theorem xlib_xn_sound_cfg : forall id args,
    APSC.node1_stmt_cfg SEGS A nx0 LIMIT SINV argH FS0 FPI APS.always (XLN.xn B SEGS A nx0 id args).
  Proof.
    intros id args FP HFP cs cs' E R FULL model T HC _ Hn Hk.
    unfold XLN.xn in Hn. destruct (Nat.eqb id 110); [|discriminate Hn]. rewrite XLN.XLnodeB_eq in Hn.
    exact (XLnode_sound_fp SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SEGS_wr SINV argH argH_high argH_agree SINV_frame SINV_agree
             NX0_sp FS0 SEGS_end RW_ok HULL_as B LIB FP HFP args cs cs' E R FULL model T HC Hn Hk).
  Qed.
End Hook.
