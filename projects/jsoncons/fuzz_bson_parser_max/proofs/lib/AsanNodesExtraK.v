(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg DivergeSim SpinAlg AgentLib AsanAcct AsanAcctShape AsanPlacement BackingAlgebra Hoare.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanK AsanPlanSoundK AsanPlanSound2K.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanNodesAuxK AsanPlanSoundSumsK AsanPlanCoreK AsanNodesExtraDefsK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Import AX2K. Import AX2SK. Import APK. Import APSK.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition aim_clob : list (bv 5) := [5; 6; 7; 11; 14; 15; 16; 17; 28]%bv.
Definition aim_spec (SEGS : list Segment) (prm : aim_params) : Prop :=
  forall (mem rom : word -> option byte) (regs : bvmap 5 word) (a sz : word) (bs1 bs2 bs3 bs4 bs5 bs6 : list byte),
  getr regs 10 = a -> getr regs 11 = sz ->
  getr regs 9 = Z_to_bv 64 0x7fff8000 -> getr regs 14 = Z_to_bv 64 0x7fff7fff ->
  rdn SEGS mem (Z_to_bv 64 (aim_got1 prm)) 8 = Some bs1 -> bytes_le_to_Z bs1 = aim_g1 prm ->
  rdn SEGS mem (Z_to_bv 64 (aim_got2 prm)) 8 = Some bs2 -> bytes_le_to_Z bs2 = aim_g2 prm ->
  rdn SEGS mem (Z_to_bv 64 (aim_got3 prm)) 8 = Some bs3 -> bytes_le_to_Z bs3 = aim_g3 prm ->
  rdn SEGS mem (Z_to_bv 64 (aim_g1 prm)) 8 = Some bs4 -> bytes_le_to_Z bs4 = 0%Z ->
  rdn SEGS mem (Z_to_bv 64 (aim_g2 prm)) 8 = Some bs5 -> bytes_le_to_Z bs5 = 0%Z ->
  rdn SEGS mem (Z_to_bv 64 (aim_g3 prm)) 8 = Some bs6 -> bytes_le_to_Z bs6 = (2^47 - 1)%Z ->
  (8 <= bv_unsigned sz)%Z -> (bv_unsigned sz mod 8 = 0)%Z ->
  ((bv_unsigned a + bv_unsigned sz <= 0x7fff7000)%Z
   \/ (0x10007fff8000 <= bv_unsigned a /\ bv_unsigned a + bv_unsigned sz <= 2^47)%Z) ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 (aim_entry prm)) mem rom) (mkst regs' (Z_to_bv 64 (aim_entry prm + 0x22c)) mem rom)
    /\ getr regs' 11 = Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - 8)
    /\ regs_agree (fun r => In r aim_clob) regs regs'.


Section NodesX.
  Variable SEGS : list Segment.
  Variable scfg : SpuriousCfg.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.
  Hypothesis e_sp0_init : expr_vars_lt nx0 e_sp0 = true.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
  (* [comment removed for export] *)
  Hypothesis SEGS_wr : APSXK.segs_wr_ok SEGS.

  #[local] Notation Hv := (AsanNodesAuxK.Hv A).
  #[local] Notation lazy_cover_vis := (AsanNodesAuxK.lazy_cover_vis SEGS A LIMIT SINV argH FS0 HULL_ok).
  #[local] Notation H_off_segments_vis := (AsanNodesAuxK.H_off_segments_vis SEGS A SEGS_in_hull).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma absbytes_sound : forall E cs R FULL model b off n cs',
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model -> node_absbytes SEGS nx0 cs b off n = Some cs' ->
    exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok SEGS A LIMIT SINV argH FS0 E' cs' R FULL model /\ pc cs' = pc cs.
  Proof.
    intros E cs R FULL model b off n cs' HC H. unfold node_absbytes in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection H as <-.
    apply andb_prop in Hc as [Hc Hrd]. apply andb_prop in Hc as [Hc Hn8]. apply andb_prop in Hc as [Hc Hn1]. apply andb_prop in Hc as [Hfr Hvb].
    apply Nat.leb_le in Hn1. apply Nat.leb_le in Hn8.
    destruct (fresh_ok_parts nx0 cs Hfr) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    assert (RD : flat E (SA b off) (Z.of_nat n) /\ exists bs, rdn SEGS (Mr A argH E cs model FULL) (adenot E (SA b off)) n = Some bs /\ length bs = n).
    { apply orb_prop in Hrd as [Hrd|Hwr].
      - exact (kn_readable_sound SEGS E _ (kn cs) _ (kn cs) b off n HK HK Hn1 Hn8 Hrd).
      - destruct (AsanNodesAuxK.kwritable_sound SEGS E _ (kn cs) (kn cs) b off (Z.of_nat n) HK HK Hwr ltac:(lia)) as (Hst & B1 & B2).
        assert (Hfl : flat E (SA b off) (Z.of_nat n)) by (unfold flat; lia).
        split; [exact Hfl|]. rewrite Nat2Z.id in Hst.
        assert (Ea : adenot E (SA b off) = Z_to_bv 64 (estart E (SA b off))) by (apply bv_eq; rewrite (flat_u E _ _ Hfl), u64_lit; unfold two64; lia).
        rewrite Ea. apply (APSXK.store_ok_rdn SEGS SEGS_wr); [rewrite u64_lit; unfold two64; lia | exact Hst]. }
    destruct RD as [Hfl (bs & Hrd' & Hlen)].
    set (w := Z_to_bv 64 (bytes_le_to_Z bs)).
    set (v := nxt cs). set (E' := ext1 E v w).
    assert (Hag : env_agree v E E') by apply ext1_agree.
    pose proof (cs_ok_agree SEGS A nx0 LIMIT SINV argH e_sp0_init argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hfr HC) as HC'.
    exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
    pose proof (bytes_le_to_Z_bound bs) as Hbnd. rewrite Hlen in Hbnd.
    assert (Hw : bv_unsigned w = bytes_le_to_Z bs).
    { unfold w. rewrite u_lit64. unfold two64. apply Z.mod_small.
      assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia. }
    match goal with |- cs_ok _ _ _ _ _ _ E' ?csx R FULL model =>
      replace csx with (set_kn (bump cs 1) (KWord (SA b off) n (EVar v) :: KRange (EVar v) 0 (2 ^ (8 * Z.of_nat n) - 1) :: kn cs))
        by (unfold set_kn, bump, with_ss; cbn; rewrite Nat.add_1_r; reflexivity) end.
    apply cs_ok_set_kn.
    - destruct HC'; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset a_hna a_hlz];
        try assumption; reflexivity.
    - pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC') as HK'. change (Mr A argH E' (bump cs 1) model FULL) with (Mr A argH E' cs model FULL).
      assert (Hv : edenot E' (EVar v) = w) by (cbn [edenot ev E' ext1]; rewrite Nat.eqb_refl; reflexivity).
      assert (HMr : Mr A argH E' cs model FULL = Mr A argH E cs model FULL).
      { unfold Mr. rewrite (hid_agree A nx0 argH e_sp0_init argH_agree v E E' cs model Hag Fle Fallow). reflexivity. }
      assert (Had : adenot E' (SA b off) = adenot E (SA b off)).
      { symmetry. eapply (adenot_agree v); [exact Hag | exact Hvb]. }
      constructor; [| constructor; [| exact HK']].
      + cbn [kentry_ok]. split; [exact Hn8|]. split.
        * apply (proj1 (flat_agree v E E' (SA b off) (Z.of_nat n) Hag Hvb)). exact Hfl.
        * rewrite HMr, Had, Hrd', Hv. f_equal. unfold word_to_le_bytes. rewrite Hw, <- Hlen. symmetry. apply Z_to_le_bytes_to_Z.
      + cbn [kentry_ok]. rewrite Hv, Hw. lia.
  Qed.

  Theorem xn_absbytes_sound : forall args, node1_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 always (xn_absbytes SEGS nx0 args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold xn_absbytes in Hn.
    destruct args as [|b [|[zo| | | | | | |] [|[zn| | | | | | |] [|]]]]; try discriminate.
    destruct (Z.leb 0 zn); [|discriminate].
    destruct (absbytes_sound E cs R FULL model b zo (Z.to_nat zn) cs' HC Hn) as (E' & Hag & HC1 & Hpc).
    rewrite <- Hpc. exact (Hk E' R FULL model Hag HC1 eq_refl).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[local] Notation munrestrict_mrestrict := (AsanNodesAuxK.munrestrict_mrestrict).

  Lemma regs_ok_transfer : forall E sr R1 R2,
    (forall r, getr R2 r = getr R1 r) -> regs_ok E sr R1 -> regs_ok E sr R2.
  Proof. intros E sr R1 R2 Heq HR r. rewrite Heq. apply HR. Qed.

  Section Smear.
    (* [comment removed for export] *)
    Variable mbase : word.
    Hypothesis SMEAR : forall (mem rom : word -> option byte) regs (x : word),
      getr regs 10 = x -> (2 ^ 46 <= bv_unsigned x < 2 ^ 47)%Z ->
      exists regs',
        msteps SEGS (mkst regs (at_ mbase 0) mem rom) (mkst regs' (at_ mbase 180) mem rom)
        /\ getr regs' 10 = Z_to_bv 64 (2 ^ 47 - 1)
        /\ getr regs' 11 = Z_to_bv 64 18446744073709551615 /\ getr regs' 12 = Z_to_bv 64 3689348814741910323
        /\ getr regs' 13 = Z_to_bv 64 1085102592571150095 /\ getr regs' 14 = Z_to_bv 64 72340172838076673
        /\ getr regs' 15 = Z_to_bv 64 9223301668110598144
        /\ regs_agree (fun r : bv 5 => In r ([10; 11; 12; 13; 14; 15]%bv : list (bv 5))) regs regs'.

    Theorem xn_smearva_sound : forall args, node1_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 always (xn_smearva (bv_unsigned mbase) args).
    Proof.
      intros args cs cs' E R FULL model T HC _ Hn Hk. unfold xn_smearva in Hn. destruct args; [|discriminate].
      unfold node_smearva in Hn.
      destruct (xlo (kn cs) (reg cs 10)) as [lo|] eqn:Hlo; [|discriminate].
      destruct (xhi (kn cs) (reg cs 10)) as [hi|] eqn:Hhi; [|discriminate].
      match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection Hn as <-.
      apply andb_prop in Hc as [Hc Hhi']. apply andb_prop in Hc as [Hpc Hlo']. apply Z.eqb_eq in Hpc. apply Z.leb_le in Hlo'. apply Z.ltb_lt in Hhi'.
      pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
      pose proof (xlo_sound SEGS E _ (kn cs) (reg cs 10) lo HK Hlo) as L1.
      pose proof (xhi_sound SEGS E _ (kn cs) (reg cs 10) hi HK Hhi) as L2.
      pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as H10.
      replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in H10 by (apply bv_eq; reflexivity).
      pose proof (u64_range mbase) as Rmb.
      set (H2 := Hv E cs model).
      set (ms := mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)).
      destruct (SMEAR (mrestrict H2 FULL) (seg_rom SEGS) R (getr R 10%bv) eq_refl ltac:(rewrite H10; lia))
        as (R' & Hms & G10 & G11 & G12 & G13 & G14 & G15 & Hag).
      assert (E0 : at_ mbase 0 = Z_to_bv 64 (pc cs)) by (unfold at_; rewrite Hpc, Z.add_0_r; reflexivity).
      assert (E180 : at_ mbase 180 = Z_to_bv 64 (bv_unsigned mbase + 180)) by reflexivity.
      rewrite E0, E180 in Hms.
      unfold cfg_of. fold ms.
      assert (Hms' : msteps SEGS (restrict H2 ms) (mkst R' (Z_to_bv 64 (bv_unsigned mbase + 180)) (mrestrict H2 FULL) (seg_rom SEGS))).
      { unfold ms. rewrite restrict_mkst. exact Hms. }
      apply (srz_msteps_restricted_T SEGS scfg H2 (H_off_segments_vis E cs model) SEGS_wx (allowA A E cs)
               ms _ model T (lazy_cover_vis E cs R FULL model HC) (A_wf_allowA' A E cs)
               (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) Hms').
      intros model' Hinv' Hsame Hclean.
      change (unrestrict H2 (ms_mem ms) (mkst R' (Z_to_bv 64 (bv_unsigned mbase + 180)) (mrestrict H2 FULL) (seg_rom SEGS)))
        with (mkst R' (Z_to_bv 64 (bv_unsigned mbase + 180)) (munrestrict H2 FULL (mrestrict H2 FULL)) (seg_rom SEGS)).
      rewrite munrestrict_mrestrict.
      specialize (Hk E R' FULL model' (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
      unfold cfg_of, pc in Hk. cbn [set_pc set_reg with_ss a_ss mk_ss s_pc] in Hk.
      apply Hk; [| apply (same_but_materialized_frame _ _ Hsame)].
      unfold set_pc, set_reg. rewrite !a_ss_with_ss, !with_ss_idem. cbn [s_regs s_know s_next].
      eapply cs_ok_frame; [exact SINV_frame | exact HC | exact Hsame | exact Hinv' | | reflexivity | exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | intros; reflexivity].
      cbn [s_regs].
      (* [comment removed for export] *)
      set (Rc := regupd (regupd (regupd (regupd (regupd (regupd R
                   (Z_to_bv 5 (Z.of_nat 10)) (Z_to_bv 64 140737488355327))
                   (Z_to_bv 5 (Z.of_nat 11)) (Z_to_bv 64 18446744073709551615))
                   (Z_to_bv 5 (Z.of_nat 12)) (Z_to_bv 64 3689348814741910323))
                   (Z_to_bv 5 (Z.of_nat 13)) (Z_to_bv 64 1085102592571150095))
                   (Z_to_bv 5 (Z.of_nat 14)) (Z_to_bv 64 72340172838076673))
                   (Z_to_bv 5 (Z.of_nat 15)) (Z_to_bv 64 9223301668110598144)).
      assert (L10 : Z_to_bv 5 (Z.of_nat 10) = (10%bv : bv 5)) by (apply bv_eq; reflexivity).
      assert (L11 : Z_to_bv 5 (Z.of_nat 11) = (11%bv : bv 5)) by (apply bv_eq; reflexivity).
      assert (L12 : Z_to_bv 5 (Z.of_nat 12) = (12%bv : bv 5)) by (apply bv_eq; reflexivity).
      assert (L13 : Z_to_bv 5 (Z.of_nat 13) = (13%bv : bv 5)) by (apply bv_eq; reflexivity).
      assert (L14 : Z_to_bv 5 (Z.of_nat 14) = (14%bv : bv 5)) by (apply bv_eq; reflexivity).
      assert (L15 : Z_to_bv 5 (Z.of_nat 15) = (15%bv : bv 5)) by (apply bv_eq; reflexivity).
      assert (NE : forall a b : bv 5, bv_eqb a b = false -> a <> b) by (intros a b Hab Heq; subst; rewrite bv_eqb_refl in Hab; discriminate).
      apply (regs_ok_transfer E _ Rc R').
      - intros r. unfold Rc. rewrite L10, L11, L12, L13, L14, L15.
        pose proof (Hag r) as HA. cbn [In] in HA.
        destruct (bv_eqb r 15%bv) eqn:E15; [apply bv_eqb_eq in E15; subst r; rewrite G15, getr_same by (apply NE; reflexivity); reflexivity|].
        rewrite (getr_other _ 15%bv _ r (NE _ _ E15)).
        destruct (bv_eqb r 14%bv) eqn:E14; [apply bv_eqb_eq in E14; subst r; rewrite G14, getr_same by (apply NE; reflexivity); reflexivity|].
        rewrite (getr_other _ 14%bv _ r (NE _ _ E14)).
        destruct (bv_eqb r 13%bv) eqn:E13; [apply bv_eqb_eq in E13; subst r; rewrite G13, getr_same by (apply NE; reflexivity); reflexivity|].
        rewrite (getr_other _ 13%bv _ r (NE _ _ E13)).
        destruct (bv_eqb r 12%bv) eqn:E12; [apply bv_eqb_eq in E12; subst r; rewrite G12, getr_same by (apply NE; reflexivity); reflexivity|].
        rewrite (getr_other _ 12%bv _ r (NE _ _ E12)).
        destruct (bv_eqb r 11%bv) eqn:E11; [apply bv_eqb_eq in E11; subst r; rewrite G11, getr_same by (apply NE; reflexivity); reflexivity|].
        rewrite (getr_other _ 11%bv _ r (NE _ _ E11)).
        destruct (bv_eqb r 10%bv) eqn:E10; [apply bv_eqb_eq in E10; subst r; rewrite G10, getr_same by (apply NE; reflexivity); apply bv_eq; reflexivity|].
        rewrite (getr_other _ 10%bv _ r (NE _ _ E10)).
        apply HA. intros [X|[X|[X|[X|[X|[X|[]]]]]]]; subst r;
          first [rewrite bv_eqb_refl in E10 | rewrite bv_eqb_refl in E11 | rewrite bv_eqb_refl in E12
                | rewrite bv_eqb_refl in E13 | rewrite bv_eqb_refl in E14 | rewrite bv_eqb_refl in E15]; discriminate.
      - unfold Rc. cbn [smearva_vals nth].
        repeat (apply regs_ok_set_n; [| lia | rewrite edenot_lit; reflexivity]).
        exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC).
    Qed.
  End Smear.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma regs_ok_sr_fresh_clob : forall rs E sr R R' nx,
    regs_ok E sr R -> APK.sr_vars_lt nx sr = true -> Forall (fun r => 0 < r < 32)%nat rs ->
    (forall q : bv 5, (forall n, In n rs -> q <> Z_to_bv 5 (Z.of_nat n)) -> getr R' q = getr R q) ->
    regs_ok (ext_list E nx (map (fun r => getr R' (Z_to_bv 5 (Z.of_nat r))) rs)) (sr_fresh sr rs nx) R'.
  Proof.
    induction rs as [|r rest IH]; intros E sr R R' nx HR Hsr Hrs Hagr; cbn [sr_fresh map ext_list].
    - apply (regs_ok_transfer E sr R R'); [|exact HR]. intros q. apply Hagr. intros n [].
    - apply Forall_cons_iff in Hrs as [Hr Hrest].
      set (v := getr R' (Z_to_bv 5 (Z.of_nat r))).
      apply (IH (ext1 E nx v) (sr_upd sr r (EVar nx)) (regupd R (Z_to_bv 5 (Z.of_nat r)) v) R' (Datatypes.S nx)).
      + apply regs_ok_set_n; [| exact Hr | apply ext1_at].
        eapply regs_ok_agree'; [apply ext1_agree | exact Hsr | exact HR].
      + apply sr_vars_lt_upd; [eapply sr_vars_lt_mono; [exact Hsr | lia] |]. cbn [APK.expr_vars_lt]. apply Nat.ltb_lt. lia.
      + exact Hrest.
      + intros q Hq.
        assert (NZ : Z_to_bv 5 (Z.of_nat r) <> (0%bv : bv 5)).
        { intros Hz. apply (f_equal bv_unsigned) in Hz. rewrite Z_to_bv_unsigned in Hz. unfold bv_wrap in Hz.
          change (bv_modulus 5) with 32%Z in Hz. rewrite Z.mod_small in Hz by lia.
          replace (bv_unsigned (0%bv : bv 5)) with 0%Z in Hz by reflexivity. lia. }
        destruct (bv_eqb q (Z_to_bv 5 (Z.of_nat r))) eqn:Eq.
        * apply (proj1 (bv_eqb_eq _ _)) in Eq. subst q. rewrite getr_same by exact NZ. reflexivity.
        * assert (Hne : q <> Z_to_bv 5 (Z.of_nat r)) by (intros ->; rewrite bv_eqb_refl in Eq; discriminate).
          rewrite (getr_other _ _ _ _ Hne). apply Hagr. intros n [<-|Hn]; [exact Hne | apply Hq; exact Hn].
  Qed.

  Lemma havoc_clob_sound : forall E cs R R' FULL model rs cs',
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model -> node_havoc nx0 cs rs = Some cs' ->
    (forall q : bv 5, (forall n, In n rs -> q <> Z_to_bv 5 (Z.of_nat n)) -> getr R' q = getr R q) ->
    exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E')
               /\ cs_ok SEGS A LIMIT SINV argH FS0 E' cs' R' FULL model /\ pc cs' = pc cs /\ kn cs' = kn cs
               /\ a_vis cs' = a_vis cs /\ a_ghost cs' = a_ghost cs.
  Proof.
    intros E cs R R' FULL model rs cs' HC H Hagr. unfold node_havoc in H.
    destruct (fresh_ok nx0 cs && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) rs)%bool eqn:Hc; [|discriminate].
    injection H as <-. apply andb_prop in Hc as [Hf Hrs].
    destruct (fresh_ok_parts nx0 cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    set (E' := ext_list E (nxt cs) (map (fun r => getr R' (Z_to_bv 5 (Z.of_nat r))) rs)).
    assert (Hag : env_agree (nxt cs) E E') by apply ext_list_agree.
    exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|repeat split; reflexivity].
    pose proof (cs_ok_agree SEGS A nx0 LIMIT SINV argH e_sp0_init argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hf HC) as HC'.
    destruct HC'; constructor; cbn [with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset a_hna a_hlz]; try assumption; [|reflexivity].
    apply (regs_ok_sr_fresh_clob rs E _ R R'); [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | exact Fsr | | exact Hagr].
    apply Forall_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) Hrs r Hr) as Hb.
    apply andb_prop in Hb as [H1 H2]. apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma aim_cell_sound : forall E M k c v,
    know_ok SEGS E M k -> aim_cell SEGS k c v = true ->
    exists bs, rdn SEGS M (Z_to_bv 64 c) 8 = Some bs /\ bytes_le_to_Z bs = v.
  Proof.
    intros E M k c v HK H. unfold aim_cell in H. apply andb_prop in H as [H Hz]. apply andb_prop in H as [Hc0 Hc8].
    apply Z.leb_le in Hc0. apply Z.ltb_lt in Hc8. unfold two64 in Hc8.
    unfold kreadZ in Hz.
    destruct (know_lookup SEGS k (ELit 0) c 8 false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
    destruct v' as [z0| | | | | | |]; try discriminate. destruct scs; [|discriminate]. apply Z.eqb_eq in Hz.
    pose proof (know_lookup_sound SEGS E M k (ELit 0) c 8 false [] [] HK ltac:(lia) ltac:(lia)) as X.
    rewrite HL in X.
    assert (Hst : estart E (SA (ELit 0) c) = c).
    { rewrite estart_SA. cbn [edenot]. rewrite u64_lit by (unfold two64; lia). lia. }
    assert (Hfl : flat E (SA (ELit 0) c) 8) by (unfold flat; rewrite Hst; lia).
    destruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hv).
    exists bs. split.
    - rewrite <- Hrd. rewrite APSXK.adenot_SA, Hst. reflexivity.
    - cbn [edenot] in Hv. unfold extz in Hv. apply (f_equal bv_unsigned) in Hv. rewrite !u_lit64 in Hv.
      pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hlen in Hb. change (2 ^ (8 * Z.of_nat 8))%Z with two64 in Hb.
      rewrite (Z.mod_small (bytes_le_to_Z bs)) in Hv by (unfold two64 in *; lia). rewrite Hv. exact Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_Mr_Hv : forall E cs model FULL (a : word) n bs,
    rdn SEGS (Mr A argH E cs model FULL) a n = Some bs -> (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
    rdn SEGS (mrestrict (Hv E cs model) FULL) a n = Some bs.
  Proof.
    intros E cs model FULL a n bs Hrd Hnw. rewrite <- Hrd. unfold Mr. apply rdn_ext; [exact Hnw|].
    intros x Hx. pose proof (rdn_visible SEGS _ FULL a n bs (H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high E cs model) Hrd x Hx) as Hh.
    unfold mrestrict. rewrite Hh. destruct (AsanNodesAuxK.Hv A E cs model x) eqn:Ev; [|reflexivity].
    pose proof (AsanNodesAuxK.Hv_hid A argH E cs model x Ev). congruence.
  Qed.

  Section AIM.
    Variable prm : aim_params.
    (* [comment removed for export] *)
    Hypothesis AIMW : aim_spec SEGS prm.

    Theorem xn_addrisinmem_sound : forall args, node1_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 always (xn_addrisinmem SEGS nx0 prm args).
    Proof.
      intros args cs cs' E R FULL model T HC _ Hn Hk. unfold xn_addrisinmem in Hn. destruct args; [|discriminate].
      unfold node_addrisinmem in Hn.
      destruct (split_lit (reg cs 10)) as [b off] eqn:Hsp.
      destruct (reg cs 11) as [n| | | | | | |] eqn:R11e; try discriminate.
      destruct (reg cs 9) as [s1| | | | | | |] eqn:R9e; try discriminate.
      destruct (reg cs 14) as [a4| | | | | | |] eqn:R14e; try discriminate.
      destruct (base_range (kn cs) b) as [[lo hi]|] eqn:Hbr; [|discriminate].
      match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
      destruct (node_havoc nx0 (set_reg cs 11 (eaddz (eadd (reg cs 10) (ELit n)) (-8))) aim_regs) as [cs1|] eqn:Hhv; [|discriminate].
      injection Hn as <-.
      apply andb_prop in Hc as [Hc C6]. apply andb_prop in Hc as [Hc C5]. apply andb_prop in Hc as [Hc C4].
      apply andb_prop in Hc as [Hc C3]. apply andb_prop in Hc as [Hc C2]. apply andb_prop in Hc as [Hc C1].
      apply andb_prop in Hc as [Hc Hapart]. apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hc Hlo0].
      apply andb_prop in Hc as [Hc Hnal]. apply andb_prop in Hc as [Hc Hn64]. apply andb_prop in Hc as [Hc Hn8].
      apply andb_prop in Hc as [Hc Ha4]. apply andb_prop in Hc as [Hpc Hs1].
      apply Z.eqb_eq in Hpc. apply Z.eqb_eq in Hs1. apply Z.eqb_eq in Ha4. apply Z.leb_le in Hn8. apply Z.ltb_lt in Hn64.
      apply Z.eqb_eq in Hnal. apply Z.leb_le in Hlo0. apply Z.leb_le in Hhi. subst s1 a4. unfold two64 in Hn64.
      pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
      (* [comment removed for export] *)
      pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as H10.
      pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 11 HC ltac:(lia)) as H11.
      pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 9 HC ltac:(lia)) as H9.
      pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 14 HC ltac:(lia)) as H14.
      rewrite R9e in H9. rewrite R14e in H14. cbn [edenot] in H9, H14.
      replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in H10 by (apply bv_eq; reflexivity).
      replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in H11 by (apply bv_eq; reflexivity).
      replace (Z_to_bv 5 (Z.of_nat 9)) with (9%bv : bv 5) in H9 by (apply bv_eq; reflexivity).
      replace (Z_to_bv 5 (Z.of_nat 14)) with (14%bv : bv 5) in H14 by (apply bv_eq; reflexivity).
      set (a := getr R 10%bv) in *. set (sz := getr R 11%bv) in *.
      assert (Usz : bv_unsigned sz = n) by (rewrite H11, R11e; cbn [edenot]; apply u64_lit; lia).
      pose proof (base_range_sound SEGS E _ (kn cs) b lo hi HK Hbr) as [B1 B2].
      assert (Hest : estart E (SA b off) = bv_unsigned (edenot E b) + off) by apply estart_SA.
      assert (Ua : bv_unsigned a = estart E (SA b off)).
      { rewrite H10. apply (u_of_split E (reg cs 10) b off Hsp). rewrite Hest. lia. }
      pose proof (ranges_apart_sound SEGS E _ (kn cs) b off n (ELit 0) 0x7fff7000 0x100000001000 HK Hapart) as CASES.
      rewrite (estart_SA E (ELit 0)) in CASES. cbn [edenot] in CASES.
      replace (bv_unsigned (Z_to_bv 64 0)) with 0%Z in CASES by reflexivity.
      assert (Hcase : (bv_unsigned a + bv_unsigned sz <= 0x7fff7000)%Z
                      \/ (0x10007fff8000 <= bv_unsigned a /\ bv_unsigned a + bv_unsigned sz <= 2^47)%Z) by (rewrite Ua, Usz; lia).
      (* [comment removed for export] *)
      set (H2 := Hv E cs model).
      assert (CELL : forall c v, aim_cell SEGS (kn cs) c v = true ->
                exists bs, rdn SEGS (mrestrict H2 FULL) (Z_to_bv 64 c) 8 = Some bs /\ bytes_le_to_Z bs = v).
      { intros c v Hcv. destruct (aim_cell_sound E _ (kn cs) c v HK Hcv) as (bs & Hrd & Hbv).
        exists bs. split; [|exact Hbv]. apply rdn_Mr_Hv; [exact Hrd|].
        unfold aim_cell in Hcv. apply andb_prop in Hcv as [Hcv _]. apply andb_prop in Hcv as [Hc0 Hc8].
        apply Z.leb_le in Hc0. apply Z.ltb_lt in Hc8. unfold two64 in Hc8. rewrite u64_lit by (unfold two64; lia). cbn [Z.of_nat]. lia. }
      destruct (CELL _ _ C1) as (bs1 & RD1 & V1). destruct (CELL _ _ C2) as (bs2 & RD2 & V2). destruct (CELL _ _ C3) as (bs3 & RD3 & V3).
      destruct (CELL _ _ C4) as (bs4 & RD4 & V4). destruct (CELL _ _ C5) as (bs5 & RD5 & V5). destruct (CELL _ _ C6) as (bs6 & RD6 & V6).
      (* [comment removed for export] *)
      set (ms := mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)).
      destruct (AIMW (mrestrict H2 FULL) (seg_rom SEGS) R a sz bs1 bs2 bs3 bs4 bs5 bs6 eq_refl eq_refl H9 H14
                  RD1 V1 RD2 V2 RD3 V3 RD4 V4 RD5 V5 RD6 V6 ltac:(lia) ltac:(rewrite Usz; exact Hnal) Hcase)
        as (R' & Hms & G11 & Hagr).
      rewrite <- Hpc in Hms.
      unfold cfg_of. fold ms.
      assert (Hms' : msteps SEGS (restrict H2 ms) (mkst R' (Z_to_bv 64 (pc cs + 0x22c)) (mrestrict H2 FULL) (seg_rom SEGS))).
      { unfold ms. rewrite restrict_mkst. exact Hms. }
      pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt.
      (* [comment removed for export] *)
      set (cs0 := set_reg cs 11 (eaddz (eadd (reg cs 10) (ELit n)) (-8))) in *.
      set (R1 := regupd R (Z_to_bv 5 (Z.of_nat 11)) (getr R' 11%bv)).
      assert (Hv11 : edenot E (eaddz (eadd (reg cs 10) (ELit n)) (-8)) = getr R' 11%bv).
      { rewrite G11. apply bv_eq. unfold eaddz, eadd. rewrite !mkAlu_denot, !edenot_lit.
        rewrite !u_add64. rewrite <- H10. pose proof (u64_range a) as Ra.
        rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
        rewrite (Z.mod_small n) by lia. rewrite (Z.mod_small (bv_unsigned a + n)) by lia.
        replace ((-8) mod 2 ^ 64)%Z with (2 ^ 64 - 8)%Z by reflexivity.
        replace (bv_unsigned a + n + (2 ^ 64 - 8))%Z with ((bv_unsigned a + bv_unsigned sz - 8) + 1 * 2 ^ 64)%Z by lia.
        rewrite Z.mod_add by lia. reflexivity. }
      assert (HC0 : cs_ok SEGS A LIMIT SINV argH FS0 E cs0 R1 FULL model).
      { unfold cs0, set_reg, R1. destruct HC; constructor;
          cbn [with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset a_hna a_hlz]; try assumption; [|reflexivity].
        apply regs_ok_set_n; [assumption | lia | exact Hv11]. }
      assert (Hagr' : forall q : bv 5, (forall m, In m aim_regs -> q <> Z_to_bv 5 (Z.of_nat m)) -> getr R' q = getr R1 q).
      { intros q Hq. unfold R1.
        replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) by (apply bv_eq; reflexivity).
        destruct (bv_eqb q 11%bv) eqn:E11.
        - apply (proj1 (bv_eqb_eq _ _)) in E11. subst q. rewrite getr_same by (intros HH; discriminate HH). reflexivity.
        - assert (Hne : q <> 11%bv) by (intros ->; rewrite bv_eqb_refl in E11; discriminate).
          rewrite (getr_other _ _ _ _ Hne). apply Hagr. unfold aim_clob. cbn [In].
          intros [X|[X|[X|[X|[X|[X|[X|[X|[X|[]]]]]]]]]]; subst q;
            first [ exact (Hne eq_refl)
                  | refine (Hq 5%nat _ _); [cbn; tauto | apply bv_eq; reflexivity]
                  | refine (Hq 6%nat _ _); [cbn; tauto | apply bv_eq; reflexivity]
                  | refine (Hq 7%nat _ _); [cbn; tauto | apply bv_eq; reflexivity]
                  | refine (Hq 14%nat _ _); [cbn; tauto | apply bv_eq; reflexivity]
                  | refine (Hq 15%nat _ _); [cbn; tauto | apply bv_eq; reflexivity]
                  | refine (Hq 16%nat _ _); [cbn; tauto | apply bv_eq; reflexivity]
                  | refine (Hq 17%nat _ _); [cbn; tauto | apply bv_eq; reflexivity]
                  | refine (Hq 28%nat _ _); [cbn; tauto | apply bv_eq; reflexivity] ]. }
      destruct (havoc_clob_sound E cs0 R1 R' FULL model aim_regs cs1 HC0 Hhv Hagr') as (E' & Hag & HC1 & Hpc1 & Hkn1 & Hvis1 & Hgh1).
      (* [comment removed for export] *)
      apply (srz_msteps_restricted_T SEGS scfg H2 (H_off_segments_vis E cs model) SEGS_wx (allowA A E cs)
               ms _ model T (lazy_cover_vis E cs R FULL model HC) (A_wf_allowA' A E cs)
               (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) Hhalt Hms').
      intros model' Hinv' Hsame Hclean.
      change (unrestrict H2 (ms_mem ms) (mkst R' (Z_to_bv 64 (pc cs + 0x22c)) (mrestrict H2 FULL) (seg_rom SEGS)))
        with (mkst R' (Z_to_bv 64 (pc cs + 0x22c)) (munrestrict H2 FULL (mrestrict H2 FULL)) (seg_rom SEGS)).
      rewrite munrestrict_mrestrict.
      assert (Hag2 : env_agree nx0 E E' /\ env_agree (nxt cs) E E') by exact Hag.
      specialize (Hk E' R' FULL model' Hag2).
      unfold cfg_of, set_pc, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk. rewrite Hpc.
      apply Hk; [| apply (same_but_materialized_frame _ _ Hsame)].
      eapply cs_ok_frame; [exact SINV_frame | exact HC1 | exact Hsame | | | reflexivity | exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC1) | intros; reflexivity].
      - (* [comment removed for export] *)
        destruct (fresh_ok_parts nx0 cs0 ltac:(unfold node_havoc in Hhv; destruct (fresh_ok nx0 cs0) eqn:Hf0; [reflexivity | discriminate]))
          as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
        replace (allowA A E' cs1) with (allowA A E cs); [exact Hinv'|].
        unfold allowA. rewrite Hvis1, Hgh1. change (flat_map (allow1 A E') (a_vis cs0 ++ a_ghost cs0)) with (allowA A E' cs).
        symmetry. eapply allowA_agree; [exact (proj2 Hag) | exact Fallow].
      - cbn [s_regs]. exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC1).
    Qed.
  End AIM.

End NodesX.
