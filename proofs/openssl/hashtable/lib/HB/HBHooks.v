(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib Hoare
  AsanAcct AsanAcctShape BackingAlgebra.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore CxPlan CxPlanSound CxPlanSound2 CxPlanSoundSums CxNodesAux HBPlanImage HBHooksC HBMaxVA.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxAcctShape CxNodesLibE.
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import DietTac.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation ASEGS := HBPlanImage.HASEGS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bv5_of_nat : forall n, (n < 32)%nat -> bv_unsigned (Z_to_bv 5 (Z.of_nat n)) = Z.of_nat n.
Proof. intros n Hn. apply reg_lit5. exact Hn. Qed.

Lemma existsb_bv_in : forall (r : bv 5) (l : list (bv 5)), existsb (bv_eqb r) l = true -> In r l.
Proof.
  intros r l H. apply existsb_exists in H as (x & Hin & Hx). unfold bv_eqb in Hx. apply Z.eqb_eq in Hx. apply bv_eq in Hx. subst x. exact Hin.
Qed.

Section Sound.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable ISP : Z.
  Variable FS0 : Fs.Fs.
  Hypothesis SEGS_wx : wx_segs_nowrap ASEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment ASEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
  Hypothesis NX0_spw : CAP.expr_vars_lt nx0 e_spw = true.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  #[local] Notation cs_ok := (CXS.cs_ok ASEGS A LIMIT SINV argH ISP FS0).
  #[local] Notation Hv := (CxNodesAux.Hv A).

  (* [comment removed for export] *)
  Lemma Mr_eq_hull : forall E cs model FULL (a : word),
    in_hull A (bv_unsigned a) = true -> Mr A argH E cs model FULL a = mrestrict (Hv E cs model) FULL a.
  Proof.
    intros E cs model FULL a Ha. unfold Mr, mrestrict, hid, CxNodesAux.Hv.
    destruct (argH E a) eqn:Hg; [|reflexivity].
    pose proof (argH_high _ _ Hg) as [Hc _]. pose proof HULL_ok as (_ & _ & _ & HU3).
    unfold in_hull in Ha. apply andb_prop in Ha as [_ Ha]. apply Z.ltb_lt in Ha. unfold CEIL, KHI in *. exfalso. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kreadZ8_hull : forall E cs R FULL model (a z : Z),
    cs_ok E cs R FULL model ->
    kreadZ ASEGS (kn cs) (ELit 0) a 8 = Some z ->
    img_lo A <= a -> a + 8 <= img_hi A ->
    rdn ASEGS (mrestrict (Hv E cs model) FULL) (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 z)).
  Proof.
    intros E cs R FULL model a z HC H Hlo Hhi.
    pose proof HULL_ok as (HU0 & HU1 & HU2 & HU3).
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK. unfold kreadZ in H.
    destruct (know_lookup ASEGS (kn cs) (ELit 0) a 8 false [] []) as [v scs hs|scs hs|] eqn:HL; try discriminate.
    destruct v as [z0| | | | | | |]; try discriminate. destruct scs; [|discriminate]. diet_injection H.
    pose proof (know_lookup_sound ASEGS E _ (kn cs) (ELit 0) a 8 false [] [] HK ltac:(lia) ltac:(lia)) as X.
    rewrite HL in X.
    assert (Hfl : flat E (SA (ELit 0) a) (Z.of_nat 8)).
    { unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia. unfold KHI in *. lia. }
    destruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hval).
    assert (Ha : adenot E (SA (ELit 0) a) = Z_to_bv 64 a).
    { apply bv_eq. rewrite (flat_u E _ _ Hfl). unfold estart. cbn [a_base a_off edenot]. rewrite !u64_lit by (unfold KHI in *; lia). lia. }
    rewrite Ha in Hrd.
    rewrite (rdn_ext ASEGS 8 (mrestrict (Hv E cs model) FULL) (Mr A argH E cs model FULL)).
    - rewrite Hrd. f_equal. cbn [edenot extz] in Hval.
      unfold word_to_le_bytes. apply (f_equal bv_unsigned) in Hval. rewrite !u_lit64 in Hval.
      pose proof (bytes_le_to_Z_bound bs) as Bb. rewrite Hlen in Bb. pose proof (bytes_le_to_Z_nonneg bs) as Bn.
      change (2 ^ (8 * Z.of_nat 8)) with two64 in Bb.
      rewrite (Z.mod_small (bytes_le_to_Z bs)) in Hval by lia.
      symmetry. rewrite u_lit64, <- Hval, <- Hlen, Z.mod_small by lia. apply Z_to_le_bytes_to_Z.
    - rewrite u64_lit by (unfold KHI in *; lia). change (Z.of_nat 8) with 8. unfold KHI in *; lia.
    - intros x Hx. rewrite u64_lit in Hx by (unfold KHI in *; lia). change (Z.of_nat 8) with 8 in Hx.
      symmetry. apply Mr_eq_hull. unfold in_hull. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kread8e_hull : forall E cs R FULL model (a : Z) ve,
    cs_ok E cs R FULL model ->
    kread8e ASEGS (kn cs) (ELit 0) a = Some ve ->
    img_lo A <= a -> a + 8 <= img_hi A ->
    rdn ASEGS (mrestrict (Hv E cs model) FULL) (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (edenot E ve)).
  Proof.
    intros E cs R FULL model a ve HC H Hlo Hhi.
    pose proof HULL_ok as (HU0 & HU1 & HU2 & HU3).
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK. unfold kread8e in H.
    destruct (know_lookup ASEGS (kn cs) (ELit 0) a 8 false [] []) as [v scs hs|scs hs|] eqn:HL; try discriminate.
    destruct scs; [|discriminate]. injection H as ->.
    pose proof (know_lookup_sound ASEGS E _ (kn cs) (ELit 0) a 8 false [] [] HK ltac:(lia) ltac:(lia)) as X.
    rewrite HL in X.
    assert (Hfl : flat E (SA (ELit 0) a) (Z.of_nat 8)).
    { unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia. unfold KHI in *. lia. }
    destruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hval).
    assert (Ha : adenot E (SA (ELit 0) a) = Z_to_bv 64 a).
    { apply bv_eq. rewrite (flat_u E _ _ Hfl). unfold estart. cbn [a_base a_off edenot]. rewrite !u64_lit by (unfold KHI in *; lia). lia. }
    rewrite Ha in Hrd.
    rewrite (rdn_ext ASEGS 8 (mrestrict (Hv E cs model) FULL) (Mr A argH E cs model FULL)).
    - rewrite Hrd. f_equal. cbn [extz] in Hval. rewrite <- Hval, <- Hlen. symmetry. apply APSX.word_to_le_bytes_of_bytes. lia.
    - rewrite u64_lit by (unfold KHI in *; lia). change (Z.of_nat 8) with 8. unfold KHI in *; lia.
    - intros x Hx. rewrite u64_lit in Hx by (unfold KHI in *; lia). change (Z.of_nat 8) with 8 in Hx.
      symmetry. apply Mr_eq_hull. unfold in_hull. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma wbytes2_out : forall (M : word -> option byte) (sp : word) bs1 bs2 (a : word),
    length bs1 = 8%nat -> length bs2 = 8%nat -> 16 <= bv_unsigned sp ->
    bv_unsigned a < bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a ->
    wbytes (wbytes M (Z_to_bv 64 (bv_unsigned sp - 8)) bs1) (Z_to_bv 64 (bv_unsigned sp - 16)) bs2 a = M a.
  Proof.
    intros M sp bs1 bs2 a L1 L2 Hsp Ha. pose proof (u64_range sp) as Rsp. pose proof (u64_range a) as Ra.
    destruct Ha as [Ha|Ha].
    - rewrite wbytes_below by (rewrite ?L2, u64_lit; lia). rewrite wbytes_below by (rewrite ?L1, u64_lit; lia). reflexivity.
    - rewrite wbytes_above by (rewrite L2, u64_lit; lia). rewrite wbytes_above by (rewrite L1, u64_lit; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Hypothesis CELLS : img_lo A <= MAXVA_GOT /\ MAXVA_PTRSLOT + 8 <= img_hi A /\ img_lo A <= MAXVA_PTRCELL /\ MAXVA_PTRCELL + 8 <= img_hi A
                     /\ MAXVA_GOT + 8 <= img_hi A /\ img_lo A <= MAXVA_PTRSLOT.

  Theorem node_maxva_sound : node1_stmt ASEGS A nx0 LIMIT SINV argH ISP FS0 always (node_maxva nx0).
  Proof.
    intros cs cs' E R FULL model T HC _ Hn Hk. unfold node_maxva in Hn. change HBHooksC.MAXVA with HBMaxVA.MAXVA in Hn. change HBHooksC.MAXVA_PTRCELL with HBMaxVA.MAXVA_PTRCELL in Hn.
    destruct (Z.eqb (pc cs) MAXVA_PC) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
    destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
    destruct (kreadZ ASEGS (kn cs) (ELit 0) MAXVA_GOT 8) as [g|] eqn:Hg; [|discriminate].
    destruct (kreadZ ASEGS (kn cs) (ELit 0) MAXVA_PTRSLOT 8) as [ptr|] eqn:Hptr; [|discriminate].
    destruct (kread8e ASEGS (kn cs) (ELit 0) MAXVA_PTRCELL) as [ve|] eqn:Hve; [|discriminate].
    destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsp.
    destruct (xlo (kn cs) ve) as [vlo|] eqn:Hvlo; [|discriminate].
    destruct (xhi (kn cs) ve) as [vhi|] eqn:Hvhi; [|discriminate].
    destruct (xlo (kn cs) (reg cs 2)) as [slo|] eqn:Hslo; [|discriminate].
    destruct (xhi (kn cs) (reg cs 2)) as [shi|] eqn:Hshi; [|discriminate].
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    apply (f_equal (fun o => match o with Some x => x | None => cs end)) in Hn. cbv beta iota in Hn. subst cs'.
    repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
    rename Hc into Hg1. apply Z.eqb_eq in Hg1. subst g.
    match goal with H : Z.eqb ptr _ = true |- _ => apply Z.eqb_eq in H; subst ptr end.
    match goal with H : fresh_ok nx0 cs = true |- _ => rename H into Hfresh end.
    match goal with H : kwritable (kn cs) (kn cs) spb (spk - 16) 8 = true |- _ => rename H into Hw16 end.
    match goal with H : kwritable (kn cs) (kn cs) spb (spk - 8) 8 = true |- _ => rename H into Hw8 end.
    match goal with H : Z.ltb shi _ = true |- _ => apply Z.ltb_lt in H; rename H into Hshi' end.
    match goal with H : Z.leb _ slo = true |- _ => apply Z.leb_le in H; rename H into Hslo' end.
    match goal with H : Z.ltb vhi _ = true |- _ => apply Z.ltb_lt in H; rename H into Hvhi' end.
    match goal with H : Z.leb _ vlo = true |- _ => apply Z.leb_le in H; rename H into Hvlo' end.
    pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (HU0 & HU1 & HU2 & HU3).
    pose proof CELLS as (C1 & C2 & C3 & C4 & C5 & C6).
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    (* [comment removed for export] *)
    pose proof (reg_sound ASEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 2 HC ltac:(lia)) as H2.
    replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) in H2 by (apply bv_eq; reflexivity).
    pose proof (reg_sound ASEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 8 HC ltac:(lia)) as H8.
    replace (Z_to_bv 5 (Z.of_nat 8)) with (8%bv : bv 5) in H8 by (apply bv_eq; reflexivity).
    pose proof (reg_sound ASEGS A LIMIT SINV argH ISP FS0 E cs R FULL model 1 HC ltac:(lia)) as H1.
    replace (Z_to_bv 5 (Z.of_nat 1)) with (1%bv : bv 5) in H1 by (apply bv_eq; reflexivity).
    assert (Hret' : reg cs 1 = ELit ret /\ ret mod 2 = 0 /\ 0 <= ret < two64).
    { unfold ret_lit in Hret. destruct (reg cs 1) as [r1| | | | | | |]; try discriminate.
      destruct (Z.eqb (r1 mod 2) 0 && Z.ltb r1 two64 && Z.leb 0 r1)%bool eqn:Hb; [|discriminate]. diet_injection Hret.
      apply andb_prop in Hb as [Hb Hb3]. apply andb_prop in Hb as [Hb1 Hb2].
      apply Z.eqb_eq in Hb1. apply Z.ltb_lt in Hb2. apply Z.leb_le in Hb3. repeat split; assumption || lia. }
    destruct Hret' as (Er1 & Heven & Hrr). rewrite Er1 in H1. rewrite edenot_lit in H1.
    set (sp := getr R 2%bv) in *. set (s0v := getr R 8%bv) in *.
    pose proof (xlo_sound ASEGS E _ (kn cs) (reg cs 2) slo HK Hslo) as Lslo. rewrite <- H2 in Lslo.
    pose proof (xhi_sound ASEGS E _ (kn cs) (reg cs 2) shi HK Hshi) as Lshi. rewrite <- H2 in Lshi.
    pose proof (xlo_sound ASEGS E _ (kn cs) ve vlo HK Hvlo) as Lvlo.
    pose proof (xhi_sound ASEGS E _ (kn cs) ve vhi HK Hvhi) as Lvhi.
    (* [comment removed for export] *)
    pose proof (u64_range sp) as Rsp.
    destruct (CxNodesAux.kwritable_sound ASEGS E _ (kn cs) (kn cs) spb (spk - 8) 8 HK HK Hw8 ltac:(lia)) as (SOK8 & B8a & B8b).
    destruct (CxNodesAux.kwritable_sound ASEGS E _ (kn cs) (kn cs) spb (spk - 16) 8 HK HK Hw16 ltac:(lia)) as (SOK16 & _ & _).
    unfold estart in SOK8, SOK16, B8a, B8b. cbn [a_base a_off] in SOK8, SOK16, B8a, B8b.
    assert (Hest : bv_unsigned (edenot E spb) + spk = bv_unsigned sp).
    { assert (Hu2 : bv_unsigned (edenot E (reg cs 2)) = (bv_unsigned (edenot E spb) + spk) mod 2 ^ 64).
      { rewrite (split_lit_denot E (reg cs 2) spb spk Hsp), Z_to_bv_unsigned, bv_wrap64_mod. reflexivity. }
      rewrite <- H2 in Hu2. unfold MAXVA_PTRCELL in *.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    replace (bv_unsigned (edenot E spb) + (spk - 8)) with (bv_unsigned sp - 8) in SOK8 by lia.
    replace (bv_unsigned (edenot E spb) + (spk - 16)) with (bv_unsigned sp - 16) in SOK16 by lia.
    change (Z.to_nat 8) with 8%nat in SOK8, SOK16.
    (* [comment removed for export] *)
    set (H2v := Hv E cs model).
    set (M0 := mrestrict H2v FULL).
    set (ms := mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom ASEGS)).
    assert (SOK8' : store_ok ASEGS M0 (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true).
    { eapply store_ok_mono; [apply CxNodesAux.Mr_grows_Hv | exact SOK8]. }
    assert (SOK16' : store_ok ASEGS M0 (Z_to_bv 64 (bv_unsigned sp - 16)) 8 = true).
    { eapply store_ok_mono; [apply CxNodesAux.Mr_grows_Hv | exact SOK16]. }
    pose proof (kreadZ8_hull E cs R FULL model MAXVA_GOT 1 HC Hg ltac:(lia) ltac:(lia)) as RD1.
    pose proof (kreadZ8_hull E cs R FULL model MAXVA_PTRSLOT MAXVA_PTRCELL HC Hptr ltac:(lia) ltac:(lia)) as RD2.
    pose proof (kread8e_hull E cs R FULL model MAXVA_PTRCELL ve HC Hve ltac:(lia) ltac:(lia)) as RD3.
    fold H2v M0 in RD1, RD2, RD3.
    (* [comment removed for export] *)
    assert (Hrr' : 0 <= ret < 2 ^ 64) by (unfold two64 in Hrr; exact Hrr).
    assert (Hretok : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_even; rewrite u64_lit by exact Hrr'; exact Heven).
    assert (Hsplo : MAXVA_PTRCELL + 8 + 16 <= bv_unsigned sp) by (unfold MAXVA_PTRCELL in *; lia).
    assert (Hsphi : bv_unsigned sp < 2 ^ 63) by lia.
    assert (Hvr : 2 ^ 46 <= bv_unsigned (edenot E ve) < 2 ^ 47) by lia.
    destruct (ha_maxva_run R M0 (seg_rom ASEGS) sp s0v (Z_to_bv 64 ret) (edenot E ve)
                Hsplo Hsphi eq_refl eq_refl H1 Hretok SOK8' SOK16' RD1 RD2 RD3 Hvr) as (R' & Hms & P10 & P2 & P8 & P1 & Pkept).
    unfold cfg_of. fold ms.
    set (M' := wbytes (wbytes M0 (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 (Z_to_bv 64 ret)))
                      (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0v)) in Hms.
    assert (Hms' : msteps ASEGS (restrict H2v ms) (mkst R' (Z_to_bv 64 ret) M' (seg_rom ASEGS))).
    { unfold ms. rewrite restrict_mkst, Hpc. fold M0.
      match type of Hms with msteps _ (mkst _ ?p _ _) _ => replace (Z_to_bv 64 MAXVA_PC) with p by (apply bv_eq; reflexivity) end.
      exact Hms. }
    apply (crz_msteps_restricted_T ASEGS H2v (CxNodesAux.H_off_segments_vis ASEGS A SEGS_in_hull E cs model) SEGS_wx (allowA A E cs)
             ms _ model T (CxNodesAux.lazy_cover_vis ASEGS A LIMIT SINV argH ISP FS0 HULL_ok E cs R FULL model HC) (A_wf_allowA' A E cs)
             (co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC) Hms').
    intros model' Hinv' Hsame Hclean.
    change (unrestrict H2v (ms_mem ms) (mkst R' (Z_to_bv 64 ret) M' (seg_rom ASEGS)))
      with (mkst R' (Z_to_bv 64 ret) (munrestrict H2v FULL M') (seg_rom ASEGS)).
    set (FULL' := munrestrict H2v FULL M').
    (* [comment removed for export] *)
    assert (NW8 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 8)) + Z.of_nat (length (word_to_le_bytes 8 (Z_to_bv 64 ret))) <= 2 ^ 64).
    { rewrite length_N_to_le_bytes, u64_lit by lia. lia. }
    assert (NW16 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 16)) + Z.of_nat (length (word_to_le_bytes 8 s0v)) <= 2 ^ 64).
    { rewrite length_N_to_le_bytes, u64_lit by lia. lia. }
    assert (HF : forall a : word, bv_unsigned a < bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a -> FULL' a = FULL a).
    { intros a Ha. unfold FULL', munrestrict. destruct (H2v a) eqn:H2a; [reflexivity|].
      unfold M'. rewrite (wbytes2_out M0 sp _ _ a ltac:(apply length_N_to_le_bytes) ltac:(apply length_N_to_le_bytes) ltac:(lia) Ha).
      unfold M0, mrestrict. rewrite H2a. reflexivity. }
    (* [comment removed for export] *)
    assert (VIS : forall x : word, bv_unsigned sp - 16 <= bv_unsigned x < bv_unsigned sp -> hid A argH E cs model x = false).
    { intros x Hx.
      assert (W : wview ASEGS (Mr A argH E cs model FULL) x <> None).
      { destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp - 8)) as [Hlt|Hge].
        - apply (store_ok_all ASEGS _ 8 (Z_to_bv 64 (bv_unsigned sp - 16))); [rewrite u64_lit by lia; change (Z.of_nat 8) with 8; lia | exact SOK16 | rewrite u64_lit by lia; change (Z.of_nat 8) with 8; lia].
        - apply (store_ok_all ASEGS _ 8 (Z_to_bv 64 (bv_unsigned sp - 8))); [rewrite u64_lit by lia; change (Z.of_nat 8) with 8; lia | exact SOK8 | rewrite u64_lit by lia; change (Z.of_nat 8) with 8; lia]. }
      unfold wview in W. unfold Mr, mrestrict in W.
      destruct (hid A argH E cs model x) eqn:Hh; [|reflexivity]. exfalso.
      destruct (find_segment ASEGS (bv_unsigned x) 1) as [seg|] eqn:Hfs; [|apply W; reflexivity].
      assert (Hin : in_hull A (bv_unsigned x) = true).
      { destruct (in_hull A (bv_unsigned x)) eqn:Hi; [reflexivity|]. rewrite (SEGS_in_hull x Hi) in Hfs. discriminate. }
      unfold hid in Hh. apply orb_prop in Hh as [Hh|Hh].
      + pose proof (argH_high _ _ Hh) as [Hc _]. unfold in_hull in Hin. apply andb_prop in Hin as [_ Hin]. apply Z.ltb_lt in Hin. unfold CEIL, KHI in *. lia.
      + apply negb_true_iff in Hh. unfold vis in Hh. rewrite Hin in Hh. discriminate. }
    (* [comment removed for export] *)
    set (v := nxt cs).
    set (E' := ext_list E v [getr R' 11%bv; getr R' 12%bv; getr R' 13%bv; getr R' 14%bv; getr R' 15%bv]).
    assert (Hag : env_agree v E E') by apply ext_list_agree.
    destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    pose proof (cs_ok_agree ASEGS A nx0 LIMIT NX0_spw SINV argH ISP argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hfresh HC) as HC'.
    pose proof (hid_agree A nx0 argH argH_agree v E E' cs model Hag Fle Fallow) as Hhid.
    assert (Hr2v : CAP.expr_vars_lt v (reg cs 2) = true) by (unfold reg; apply nth_sr_vars_lt; [exact Fsr | lia]).
    assert (Hr8v : CAP.expr_vars_lt v (reg cs 8) = true) by (unfold reg; apply nth_sr_vars_lt; [exact Fsr | lia]).
    assert (Hspbv : CAP.expr_vars_lt v spb = true) by (eapply APSX.split_lit_vars; [exact Hsp | exact Hr2v]).
    assert (Espb : edenot E' spb = edenot E spb) by (symmetry; eapply (edenot_agree' v); [exact Hag | exact Hspbv]).
    assert (E8 : edenot E' (reg cs 8) = s0v) by (rewrite <- (edenot_agree' v E E' _ Hag Hr8v), <- H8; reflexivity).
    specialize (Hk E' R' FULL' model' (conj (env_agree_le nx0 v E E' Hag Fle) Hag)).
    unfold cfg_of, pc in Hk. cbn [a_ss with_ss mk_ss s_pc] in Hk.
    apply Hk; [| apply (same_but_materialized_frame _ _ Hsame)].
    (* [comment removed for export] *)
    eapply cs_ok_frame; [exact SINV_frame | exact HC' | exact Hsame | | | reflexivity | |].
    - rewrite (allowA_agree A v E E' cs Hag Fallow). exact Hinv'.
    - (* [comment removed for export] *)
      cbn [s_regs mk_ss].
      pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC') as HR0.
      assert (EV : forall i, (i < 5)%nat -> edenot E' (EVar (v + i)%nat) = getr R' (Z_to_bv 5 (Z.of_nat (11 + i)))).
      { intros i Hi. cbn [edenot]. unfold E'. rewrite ext_list_at by (cbn; lia).
        destruct i as [|[|[|[|[|i]]]]]; try (cbn; lia);
          cbn [nth Nat.add]; f_equal; apply bv_eq; reflexivity. }
      pose proof (regs_ok_set_n E' _ _ 10 (ELit MAXVA) (Z_to_bv 64 MAXVA) HR0 ltac:(lia) (edenot_lit E' MAXVA)) as K0.
      pose proof (regs_ok_set_n E' _ _ 11 (EVar v) _ K0 ltac:(lia) (eq_trans (f_equal (fun i => edenot E' (EVar i)) (eq_sym (Nat.add_0_r v))) (EV 0%nat ltac:(lia)))) as K1.
      pose proof (regs_ok_set_n E' _ _ 12 (EVar (v + 1)%nat) _ K1 ltac:(lia) (EV 1%nat ltac:(lia))) as K2.
      pose proof (regs_ok_set_n E' _ _ 13 (EVar (v + 2)%nat) _ K2 ltac:(lia) (EV 2%nat ltac:(lia))) as K3.
      pose proof (regs_ok_set_n E' _ _ 14 (EVar (v + 3)%nat) _ K3 ltac:(lia) (EV 3%nat ltac:(lia))) as K4.
      pose proof (regs_ok_set_n E' _ _ 15 (EVar (v + 4)%nat) _ K4 ltac:(lia) (EV 4%nat ltac:(lia))) as K5.
      cbn [Nat.add] in K5.
      intros r. fold v. rewrite <- (K5 r). clear K0 K1 K2 K3 K4 K5.
      (* [comment removed for export] *)
      assert (NEQ : forall a b, (a < 32)%nat -> (b < 32)%nat -> a <> b -> Z_to_bv 5 (Z.of_nat a) <> Z_to_bv 5 (Z.of_nat b)).
      { intros a b Ha Hb Hab HH. apply (f_equal bv_unsigned) in HH. rewrite !reg_lit5 in HH by assumption. lia. }
      assert (NZ : forall a, (0 < a < 32)%nat -> Z_to_bv 5 (Z.of_nat a) <> 0%bv).
      { intros a Ha HH. apply (f_equal bv_unsigned) in HH. rewrite reg_lit5 in HH by lia. change (bv_unsigned (0%bv : bv 5)) with 0 in HH. lia. }
      rewrite <- (ridx_roundtrip r). pose proof (ridx_range r) as Hr. set (n := ridx r) in *. clearbody n.
      assert (P10' : getr R' (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 MAXVA) by (rewrite <- P10; f_equal; apply bv_eq; reflexivity).
      assert (KEEP : (n < 10 \/ 15 < n)%nat -> getr R' (Z_to_bv 5 (Z.of_nat n)) = getr R (Z_to_bv 5 (Z.of_nat n))).
      { intros Hn.
        destruct (Nat.eq_dec n 0) as [->|N0]; [unfold getr; cbn; reflexivity|].
        destruct (Nat.eq_dec n 1) as [->|N1]; [replace (Z_to_bv 5 (Z.of_nat 1)) with (1%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P1; symmetry; exact H1|].
        destruct (Nat.eq_dec n 2) as [->|N2]; [replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P2; reflexivity|].
        destruct (Nat.eq_dec n 8) as [->|N8]; [replace (Z_to_bv 5 (Z.of_nat 8)) with (8%bv : bv 5) by (apply bv_eq; reflexivity); rewrite P8; reflexivity|].
        apply Pkept. apply existsb_bv_in. unfold maxva_kept.
        do 32 (destruct n as [|n]; [first [lia | (vm_compute; reflexivity)] |]). lia. }
      destruct (Nat.lt_ge_cases n 10) as [Hlt|Hge].
      { rewrite !getr_other by (apply NEQ; lia). apply KEEP. lia. }
      destruct (Nat.lt_ge_cases 15 n) as [Hlt'|Hge'].
      { rewrite !getr_other by (apply NEQ; lia). apply KEEP. lia. }
      assert (CASES : (n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15)%nat) by lia.
      destruct CASES as [->|[->|[->|[->|[->| ->]]]]].
      + rewrite 5 getr_other by (apply NEQ; lia). rewrite getr_same by (apply NZ; lia). exact P10'.
      + rewrite 4 getr_other by (apply NEQ; lia). rewrite getr_same by (apply NZ; lia). reflexivity.
      + rewrite 3 getr_other by (apply NEQ; lia). rewrite getr_same by (apply NZ; lia). reflexivity.
      + rewrite 2 getr_other by (apply NEQ; lia). rewrite getr_same by (apply NZ; lia). reflexivity.
      + rewrite 1 getr_other by (apply NEQ; lia). rewrite getr_same by (apply NZ; lia). reflexivity.
      + rewrite getr_same by (apply NZ; lia). reflexivity.
    - (* [comment removed for export] *)
      cbn [s_know mk_ss]. unfold Mr. rewrite Hhid.
      set (MR := mrestrict (hid A argH E cs model) FULL).
      set (MR' := mrestrict (hid A argH E cs model) FULL').
      assert (L1 : length (word_to_le_bytes 8 (Z_to_bv 64 ret)) = 8%nat) by apply length_N_to_le_bytes.
      assert (L2 : length (word_to_le_bytes 8 s0v) = 8%nat) by apply length_N_to_le_bytes.
      assert (HV2 : forall x : word, bv_unsigned sp - 16 <= bv_unsigned x < bv_unsigned sp -> H2v x = false).
      { intros x Hx. unfold H2v, CxNodesAux.Hv. apply negb_false_iff.
        pose proof (VIS x Hx) as Hh. unfold hid in Hh. apply orb_false_iff in Hh as [_ Hh]. apply negb_false_iff in Hh. exact Hh. }
      assert (HMR' : forall x : word, bv_unsigned sp - 16 <= bv_unsigned x < bv_unsigned sp -> MR' x = M' x).
      { intros x Hx. unfold MR', mrestrict. rewrite (VIS x Hx). unfold FULL', munrestrict. rewrite (HV2 x Hx). reflexivity. }
      assert (HMRout : forall x : word, bv_unsigned x < bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned x -> MR' x = MR x).
      { intros x Hx. unfold MR', MR, mrestrict. rewrite (HF x Hx). reflexivity. }
      assert (KW : forall (o : Z) (val : expr) (w : word),
                o = spk - 8 \/ o = spk - 16 -> edenot E' val = w ->
                rdn ASEGS M' (Z_to_bv 64 (bv_unsigned sp + (o - spk))) 8 = Some (word_to_le_bytes 8 w) ->
                kentry_ok ASEGS E' MR' (KWord (SA spb o) 8 val)).
      { intros o val w Ho Hval Hrd. cbn [kentry_ok]. split; [lia|].
        assert (Hfl : flat E' (SA spb o) (Z.of_nat 8)).
        { unfold flat, estart. cbn [a_base a_off]. rewrite Espb. change (Z.of_nat 8) with 8. lia. }
        split; [exact Hfl|].
        assert (Had : adenot E' (SA spb o) = Z_to_bv 64 (bv_unsigned sp + (o - spk))).
        { apply bv_eq. rewrite (flat_u E' _ _ Hfl). unfold estart. cbn [a_base a_off]. rewrite Espb, u64_lit by lia. lia. }
        rewrite Had, Hval.
        rewrite (rdn_ext ASEGS 8 MR' M'); [exact Hrd | rewrite u64_lit by lia; change (Z.of_nat 8) with 8; lia |].
        intros x Hx. rewrite u64_lit in Hx by lia. change (Z.of_nat 8) with 8 in Hx. apply HMR'. lia. }
      constructor.
      { apply (KW (spk - 8) (reg cs 1) (Z_to_bv 64 ret)); [left; reflexivity | rewrite Er1; apply edenot_lit |].
        replace (bv_unsigned sp + (spk - 8 - spk)) with (bv_unsigned sp - 8) by lia.
        unfold M'. rewrite rdn_wbytes_out; [ | rewrite L2, !u64_lit by lia; change (Z.of_nat 8) with 8; lia
                                          | rewrite u64_lit by lia; change (Z.of_nat 8) with 8; lia
                                          | rewrite L2, u64_lit by lia; lia ].
        apply rdn_wbytes_hit8. rewrite u64_lit by lia. lia. }
      constructor.
      { apply (KW (spk - 16) (reg cs 8) s0v); [right; reflexivity | exact E8 |].
        replace (bv_unsigned sp + (spk - 16 - spk)) with (bv_unsigned sp - 16) by lia.
        unfold M'. apply rdn_wbytes_hit8. rewrite u64_lit by lia. lia. }
      apply (know_ok_havoc ASEGS E' MR MR' (kn cs) spb (spk - 16) (ELit 16)).
      + pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC') as HK'. unfold Mr in HK'. rewrite Hhid in HK'. exact HK'.
      + intros x Hx. apply HMRout. unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx. rewrite Espb, u64_lit in Hx by lia. lia.
      + intros x Hx. unfold MR, MR', mrestrict in Hx |- *. destruct (hid A argH E cs model x) eqn:Hh; [exact Hx|].
        unfold FULL', munrestrict. destruct (H2v x) eqn:H2x; [exact Hx|].
        destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp - 16)) as [Hlt|Hge].
        { unfold M'. rewrite (wbytes2_out M0 sp _ _ x L1 L2 ltac:(lia) ltac:(left; exact Hlt)). unfold M0, mrestrict. rewrite H2x. exact Hx. }
        destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp)) as [Hlt'|Hge'].
        2: { unfold M'. rewrite (wbytes2_out M0 sp _ _ x L1 L2 ltac:(lia) ltac:(right; lia)). unfold M0, mrestrict. rewrite H2x. exact Hx. }
        (* [comment removed for export] *)
        pose proof (u64_range x) as Rx.
        assert (U16 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 16)) = bv_unsigned sp - 16) by (apply u64_lit; lia).
        assert (U8 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 8)) = bv_unsigned sp - 8) by (apply u64_lit; lia).
        unfold M'. destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp - 8)) as [Hl8|Hg8].
        * replace x with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 16)) + Z.of_nat (Z.to_nat (bv_unsigned x - (bv_unsigned sp - 16))))).
          2: { apply bv_eq. rewrite U16, Z2Nat.id by lia. rewrite u64_lit by lia. lia. }
          apply APSX.wbytes_defined; [rewrite L2, U16; lia | rewrite L2; lia].
        * rewrite wbytes_above by (rewrite L2, U16; lia).
          replace x with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 8)) + Z.of_nat (Z.to_nat (bv_unsigned x - (bv_unsigned sp - 8))))).
          2: { apply bv_eq. rewrite U8, Z2Nat.id by lia. rewrite u64_lit by lia. lia. }
          apply APSX.wbytes_defined; [rewrite L1, U8; lia | rewrite L1; lia].
    - (* [comment removed for export] *) intros a Ha. rewrite Hhid in Ha. apply HF.
      destruct (Z_lt_ge_dec (bv_unsigned a) (bv_unsigned sp - 16)) as [Hlt|Hge]; [left; exact Hlt|].
      destruct (Z_lt_ge_dec (bv_unsigned a) (bv_unsigned sp)) as [Hlt|Hge']; [|right; lia].
      exfalso. rewrite (VIS a ltac:(lia)) in Ha. discriminate.
  Qed.

  (* [comment removed for export] *)
  Theorem ha_xn_sound : ext_stmt ASEGS A nx0 LIMIT (ha_xn nx0) SINV argH ISP FS0.
  Proof.
    intros id args cs cs' E R FULL model T HC Hpre Hn Hk. unfold ha_xn in Hn.
    destruct (Nat.eqb id 50); [|discriminate].
    exact (node_maxva_sound cs cs' E R FULL model T HC Hpre Hn Hk).
  Qed.
End Sound.
