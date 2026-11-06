(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VAbs VAbsSound VAbsSound2 VAbsSound3 VStep VStepMem VStepSound VStepMemSound VStepMemSound2.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import SeqExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VState2 VStepMem2 VGamma2 VStepMem2SoundA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Section B.
  Variable SEGS : list Segment.
  Variable P : vparams2.
  Variable E : venv2.
  Variable mem0 : word -> option byte.
  Let P1 := p1 P.
  Let E1 := ev1 E.
  Hypothesis PO2 : params_ok2 SEGS P.

  Notation gamma2P := (gamma2 SEGS P E mem0).

  Lemma PO1' : params_ok SEGS P1.
  Proof. exact (proj1 PO2). Qed.

  Lemma gamma2_lgamma A nu regs mem : gamma2P A nu regs mem -> lgamma (v1 A) nu.
  Proof. intros H. eapply gamma_lgamma. exact (proj1 H). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma base_syms_single A addr B :
    base_syms A addr = [B] -> In B (lsyms addr) /\ is_base A B = true.
  Proof.
    unfold base_syms. intros H.
    assert (In B (List.filter (is_base A) (lsyms addr))) by (rewrite H; left; reflexivity).
    apply filter_In in H0. exact H0.
  Qed.

  Lemma is_base_rgn A B : is_base A B = true -> exists r, rgn_get (vs_rgn A) B = Some r.
  Proof.
    unfold is_base, rgn_bases. rewrite existsb_exists. intros (s & Hs & Hb). apply Pos.eqb_eq in Hb. subst s.
    apply in_map_iff in Hs as (r & Hr & Hin). subst B.
    induction (vs_rgn A) as [|x t IH]; [destruct Hin|]. simpl.
    destruct (Pos.eqb_spec (vr_base x) (vr_base r)); [eauto|].
    destruct Hin as [->|Hin]; [congruence|]. exact (IH Hin).
  Qed.

  (* [comment removed for export] *)
  Lemma eval_off nu addr r :
    eval nu (laddc (lsub addr (lsym (vr_base r))) (- vr_disp r)) = eval nu addr - rbase nu r.
  Proof. rewrite eval_laddc, eval_lsub, eval_lsym. unfold rbase. lia. Qed.

  #[using="Type"] Lemma classify_rgn_sound A nu r addr n st r' off lo hi :
    lgamma (v1 A) nu -> 0 < n ->
    classify_rgn A r addr n st = C2Rgn r' off lo hi ->
    r' = r /\ off = laddc (lsub addr (lsym (vr_base r))) (- vr_disp r)
    /\ eval nu addr = rbase nu r + eval nu off
    /\ (is_data_shadow r = false ->
          lo <= eval nu off <= hi /\ vr_lo r <= eval nu off /\ eval nu off + n <= vr_hi r
          /\ (st = true -> in_ranges (vr_w r) lo (hi - lo + n) = true))
    /\ (is_data_shadow r = true -> st = false /\ n = 1 /\ -16 <= 8 * eval nu off /\ 8 * eval nu off - nu SIZE <= 15 /\ 1 <= nu SIZE).
  Proof.
    intros HL Hn. unfold classify_rgn, is_data_shadow.
    set (off0 := laddc (lsub addr (lsym (vr_base r))) (- vr_disp r)).
    assert (EO : eval nu addr = rbase nu r + eval nu off0) by (unfold off0; rewrite eval_off; lia).
    assert (GEN : forall lo hi,
      (if negb (qge (v1 A) off0 (vr_lo r)) then (if bnd_dead (v1 A) off0 then C2Dead else C2Fail "region access below its extent")
       else if negb (qle (v1 A) (laddc off0 n) (vr_hi r)) then (if bnd_dead (v1 A) off0 then C2Dead else C2Fail "region access above its extent")
       else match bnd (v1 A) off0 with
            | (Some lo1, Some hi1) =>
                if itv_empty (Some lo1, Some hi1) then C2Dead
                else if st && negb (in_ranges (vr_w r) lo1 (hi1 - lo1 + n)) then C2Fail "store outside the region's writable ranges"
                else C2Rgn r off0 lo1 hi1
            | _ => C2Fail "region offset unbounded"
            end) = C2Rgn r' off lo hi ->
      r' = r /\ off = off0 /\ lo <= eval nu off <= hi /\ vr_lo r <= eval nu off /\ eval nu off + n <= vr_hi r
      /\ (st = true -> in_ranges (vr_w r) lo (hi - lo + n) = true)).
    { intros lo1 hi1 Hc.
      destruct (qge (v1 A) off0 (vr_lo r)) eqn:Q1; simpl in Hc; [|destruct (bnd_dead (v1 A) off0); discriminate].
      destruct (qle (v1 A) (laddc off0 n) (vr_hi r)) eqn:Q2; simpl in Hc; [|destruct (bnd_dead (v1 A) off0); discriminate].
      pose proof (bnd_sound (v1 A) nu off0 HL) as HB.
      destruct (bnd (v1 A) off0) as [[l1|] [h1|]]; try discriminate.
      destruct (itv_empty (Some l1, Some h1)); [discriminate|].
      destruct (st && negb (in_ranges (vr_w r) l1 (h1 - l1 + n))) eqn:SW; [discriminate|].
      injection Hc as <- <- <- <-.
      pose proof (qge_sound _ _ _ _ HL Q1) as G1. pose proof (qle_sound _ _ _ _ HL Q2) as G2. rewrite eval_laddc in G2.
      destruct HB as [HB1 HB2]. simpl in HB1, HB2.
      repeat split; try lia. intros ->. simpl in SW. destruct (in_ranges (vr_w r) l1 (h1 - l1 + n)); [reflexivity|discriminate]. }
    destruct (vr_kind r) as [cid fl| |owner|s|] eqn:K;
      try (intros Hc; destruct (GEN _ _ Hc) as (-> & -> & R3 & R4 & R5 & R6); repeat split; auto; try (ltac2:(LK.k [@R3; @H]); lia); intros; discriminate).
    destruct (Pos.eqb_spec s DATA) as [->|NE].
    - destruct st; [discriminate|]. destruct (Z.eqb_spec n 1) as [->|]; simpl; [|discriminate].
      rewrite ?if_andb.
      destruct (qge (v1 A) (lscale 8 off0) (-16) && qle (v1 A) (lsub (lscale 8 off0) (lsym SIZE)) 15 && qge (v1 A) (lsym SIZE) 1) eqn:Q.
      + apply andb_prop in Q as [Q Q3]. apply andb_prop in Q as [Q1 Q2].
        pose proof (qge_sound _ _ _ _ HL Q1) as G1. pose proof (qle_sound _ _ _ _ HL Q2) as G2. pose proof (qge_sound _ _ _ _ HL Q3) as G3.
        rewrite eval_lscale in G1. rewrite eval_lsub, eval_lscale, eval_lsym in G2. rewrite eval_lsym in G3.
        intros Hc. assert (r' = r /\ off = off0) as [-> ->].
        { destruct (bnd (v1 A) off0) as [[l1|] [h1|]]; injection Hc; auto. }
        repeat split; auto; try lia; intros; try discriminate.
      + destruct (bnd_dead (v1 A) off0); discriminate.
    - intros Hc. destruct (GEN _ _ Hc) as (-> & -> & R3 & R4 & R5 & R6).
      repeat split; auto; try lia; try (intros HH; discriminate).
  Qed.

  Lemma classify_rgn_not_dead A nu r addr n st :
    lgamma (v1 A) nu -> classify_rgn A r addr n st = C2Dead -> False.
  Proof.
    intros HL. unfold classify_rgn.
    set (off0 := laddc (lsub addr (lsym (vr_base r))) (- vr_disp r)).
    pose proof (bnd_dead_sound (v1 A) nu off0 HL) as ND.
    pose proof (bnd_sound (v1 A) nu off0 HL) as HB.
    assert (NE : forall l1 h1, bnd (v1 A) off0 = (Some l1, Some h1) -> itv_empty (Some l1, Some h1) = false).
    { intros l1 h1 Hb. rewrite Hb in HB. destruct (itv_empty (Some l1, Some h1)) eqn:EE; [|reflexivity].
      exfalso. exact (itv_empty_sound _ _ EE HB). }
    rewrite !ND.
    assert (GEN :
      (if negb (qge (v1 A) off0 (vr_lo r)) then C2Fail "region access below its extent"
       else if negb (qle (v1 A) (laddc off0 n) (vr_hi r)) then C2Fail "region access above its extent"
       else match bnd (v1 A) off0 with
            | (Some lo1, Some hi1) =>
                if itv_empty (Some lo1, Some hi1) then C2Dead
                else if st && negb (in_ranges (vr_w r) lo1 (hi1 - lo1 + n)) then C2Fail "store outside the region's writable ranges"
                else C2Rgn r off0 lo1 hi1
            | _ => C2Fail "region offset unbounded"
            end) = C2Dead -> False).
    { destruct (qge (v1 A) off0 (vr_lo r)); simpl; [|discriminate].
      destruct (qle (v1 A) (laddc off0 n) (vr_hi r)); simpl; [|discriminate].
      destruct (bnd (v1 A) off0) as [[l1|] [h1|]] eqn:Hb; try discriminate.
      rewrite (NE _ _ eq_refl). destruct (st && _); discriminate. }
    destruct (vr_kind r) as [cid fl| |owner|s|]; try exact GEN.
    destruct (Pos.eqb s DATA); [|exact GEN].
    destruct st; [discriminate|]. destruct (Z.eqb n 1); simpl; [|discriminate].
    rewrite ?if_andb.
    destruct (qge _ _ _ && qle _ _ _ && qge _ _ _); [destruct (bnd (v1 A) off0) as [[?|] [?|]]; discriminate|discriminate].
  Qed.

  Lemma classify2_rgn A addr n st r off lo hi :
    classify2 A addr n st = Some (C2Rgn r off lo hi) ->
    exists B r0, base_syms A addr = [B] /\ lcoef addr B = 1 /\ rgn_get (vs_rgn A) B = Some r0 /\
                 classify_rgn A r0 addr n st = C2Rgn r off lo hi.
  Proof.
    unfold classify2. destruct (base_syms A addr) as [|B [|]]; try discriminate.
    destruct (Z.eqb_spec (lcoef addr B) 1); simpl; [|discriminate].
    destruct (Z.eqb (lcoef addr SP0) 0 && Z.eqb (lcoef addr DATA) 0); simpl; [|discriminate].
    destruct (rgn_get (vs_rgn A) B) as [r0|] eqn:G; [|discriminate].
    intros H. injection H as H. exists B, r0. repeat split; auto.
  Qed.

  Lemma classify2_dead A nu addr n st :
    lgamma (v1 A) nu -> classify2 A addr n st = Some C2Dead -> False.
  Proof.
    intros HL. unfold classify2. destruct (base_syms A addr) as [|B [|]]; try discriminate.
    destruct (Z.eqb (lcoef addr B) 1); simpl; [|discriminate].
    destruct (Z.eqb (lcoef addr SP0) 0 && Z.eqb (lcoef addr DATA) 0); simpl; [|discriminate].
    destruct (rgn_get (vs_rgn A) B) as [r0|]; [|discriminate].
    intros H. injection H as H. eapply classify_rgn_not_dead; eauto.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma lift1_next_inv A r succs :
    lift1 A r = VR2_next succs -> exists l, r = VR_next l /\ succs = map (with_v1 A) l.
  Proof. destruct r; simpl; intros H; [injection H as <-; eauto|discriminate]. Qed.

  Lemma step_post2_mono A nu l1 l2 regs mem pc rom :
    step_post2 SEGS P E mem0 A nu l1 regs mem pc rom -> (forall x, In x l1 -> In x l2) ->
    step_post2 SEGS P E mem0 A nu l2 regs mem pc rom.
  Proof.
    intros (regs' & pc' & mem' & A' & nu' & H1 & H2 & REST) Hsub.
    exists regs', pc', mem', A', nu'. split; [exact H1|]. split; [apply Hsub; exact H2|exact REST].
  Qed.

  Lemma with_v1_idem A B C : with_v1 (with_v1 A B) C = with_v1 A C.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma globs_finish_aext A0 A1 nu nu1 rd v :
    aext A0 A1 nu nu1 -> vs_globs (finish A1 rd v) = vs_globs A0.
  Proof.
    intros (_ & _ & SH). destruct SH as (_ & _ & SG & _).
    unfold finish, set_reg. destruct (Z.eqb rd 0); cbn; destruct v; cbn; exact SG.
  Qed.

  Lemma globs_same A (B : vstate) nu regs mem :
    gamma2P A nu regs mem -> vs_globs B = vs_globs (v1 A) -> globs_ok2 P (with_v1 A B).
  Proof.
    intros HG2 EG. pose proof HG2 as (_ & _ & _ & _ & _ & _ & _ & _ & GL & _).
    unfold globs_ok2 in *. cbn [v1 with_v1]. rewrite EG. exact GL.
  Qed.

  (* [comment removed for export] *)
  Lemma finish2_post A nu regs mem pc rom (rd : reg) (wl : word) v A1v :
    gamma2P A nu regs mem -> vs2_pc A = bv_unsigned pc -> rz rd <> 0 ->
    res_word (v1 A) nu (v, A1v) (bv_unsigned wl) ->
    RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd wl) (v_addi pc 4) mem rom) ->
    step_post2 SEGS P E mem0 A nu [finish2 (with_v1 A A1v) (rz rd) v] regs mem pc rom.
  Proof.
    intros HG2 Hpc Hrd HR ST.
    pose proof (step_post_value SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem pc rom rd wl (v, A1v)
                  (proj1 HG2) Hpc Hrd HR ST) as SP.
    refine (step_post_lift SEGS P E mem0 PO2 A nu _ regs mem pc rom HG2 _ _ SP).
    - intros x [<-|[]]. eapply globs_same; [exact HG2|]. destruct HR as [nu1 (X1 & _)]. exact (globs_finish_aext _ _ _ _ _ _ X1).
    - intros regs' pc' mem' ST'. left. rewrite ST in ST'. injection ST'; auto.
  Qed.

  (* [comment removed for export] *)
  Lemma load_machine A nu regs mem pc rom w sz sg (rd rs1 : reg) (imm : bv 12) addr a bs :
    gamma2P A nu regs mem ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Load sz sg rd rs1 imm, 4) ->
    (sz = SZ8 -> sg = true) ->
    addr_of (v1 A) (rz rs1) (bv_signed imm) = Some addr -> eval nu addr = a ->
    rdn SEGS mem (wordZ a) (Z.to_nat (msize_z sz)) = Some bs ->
    exists wl : word,
      bv_unsigned wl = ldval sg (msize_z sz) (bytes_le_to_Z bs) /\
      RiscvSemantics.step SEGS (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd wl) (v_addi pc 4) mem rom).
  Proof.
    intros HG2 Hf He Hd Hsz Ha Ea Hrd.
    destruct (addr_of_sound SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem rs1 (bv_signed imm) addr (proj1 HG2) Ha) as [Ba Hva].
    eapply step_load_any; eauto. replace (v_addi (getr regs rs1) (bv_signed imm)) with (wordZ a); [exact Hrd|].
    apply bv_eq. rewrite Hva, Ea. unfold wordZ. rewrite u_Z_to_bv64. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma rgn_in A B r : rgn_get (vs_rgn A) B = Some r -> In r (vs_rgn A).
  Proof. intros H. exact (proj1 (rgn_get_in _ _ _ H)). Qed.

  Lemma region_bytes A nu regs mem r o k :
    gamma2P A nu regs mem -> In r (vs_rgn A) -> is_data_shadow r = false ->
    vr_lo r <= o -> o + Z.of_nat k <= vr_hi r ->
    exists bs, rdn SEGS mem (wordZ (rbase nu r + o)) k = Some bs /\ length bs = k.
  Proof.
    intros HG2 Hr ND H1 H2. pose proof HG2 as (_ & _ & _ & _ & _ & RGN & _).
    destruct (RGN r Hr) as (B1 & B2 & B3 & _ & _ & PERM & _). destruct (PERM ND) as [RD _].
    apply rdn_bytes; [lia|lia|]. intros j Hj.
    replace (rbase nu r + o + j) with (rbase nu r + (o + j)) by lia.
    destruct (RD (o + j)) as [_ X]; [lia|exact X].
  Qed.

  Lemma load_cells_sound A nu regs mem r off lo hi n sg :
    gamma2P A nu regs mem -> In r (vs_rgn A) -> is_shadow r = false ->
    0 < n <= 8 -> lo <= eval nu off <= hi -> vr_lo r <= eval nu off -> eval nu off + n <= vr_hi r ->
    exists bs,
      rdn SEGS mem (wordZ (rbase nu r + eval nu off)) (Z.to_nat n) = Some bs /\
      res_word (v1 A) nu (load_cells (v1 A) (vr_cells r) off lo hi n sg) (ldval sg n (bytes_le_to_Z bs)).
  Proof.
    intros HG2 Hr NS Hn Hlh H1 H2.
    pose proof (gamma2_lgamma _ _ _ _ HG2) as HL.
    pose proof HG2 as (G1 & _ & _ & _ & _ & RGN & _ & BEL2 & _ & _).
    assert (ND : is_data_shadow r = false).
    { unfold is_data_shadow. unfold is_shadow in NS. destruct (vr_kind r); auto; discriminate. }
    destruct (RGN r Hr) as (B1 & B2 & B3 & _ & CELLS & PERM & _ & _).
    assert (Hkn : Z.of_nat (Z.to_nat n) = n) by lia.
    destruct (region_bytes A nu regs mem r (eval nu off) (Z.to_nat n) HG2 Hr ND ltac:(lia) ltac:(lia)) as [bs [Hbs Hlen]].
    assert (FRESH : forall bs0, length bs0 = Z.to_nat n ->
              res_word (v1 A) nu (fresh_loaded (v1 A) n sg) (ldval sg n (bytes_le_to_Z bs0))).
    { intros bs0 Hl0. apply fresh_loaded_sound; [exact HL|lia|].
      pose proof (bytes_le_to_Z_bound bs0) as X. rewrite Hl0, Hkn in X. pose proof (bytes_le_to_Z_nonneg bs0). lia. }
    assert (CH : forall o w v, In (o, (w, v)) (vr_cells r) -> cell_holds SEGS nu mem (rbase nu r + o) w v).
    { intros o w v Hin. destruct (CELLS _ _ _ Hin) as (_ & _ & _ & RC). unfold rcell_holds in RC. rewrite NS in RC.
      destruct v; [exact RC|exact I]. }
    unfold load_cells.
    destruct (Z.eqb_spec lo hi) as [Elh|Nlh]; [|exists bs; split; [exact Hbs|apply FRESH; exact Hlen]].
    assert (Eo : eval nu off = lo) by lia. rewrite Eo in *.
    destruct (cm_get (vr_cells r) lo) as [[w [v|]]|] eqn:Ecm.
    - apply cm_get_in in Ecm. pose proof (CH _ _ _ Ecm) as X. cbn [cell_holds] in X. destruct X as [bs' [Hbs' Hval]].
      destruct BEL2 as (_ & BR & _). destruct (BR r Hr) as (_ & Bc & _). pose proof (Bc _ _ _ Ecm) as Bv.
      pose proof (rdn_length _ _ _ _ _ Hbs') as Hlen'.
      destruct (Z.eqb_spec w n) as [->|Nw].
      + exists bs'. split; [exact Hbs'|]. apply areinterp_sound; auto.
      + destruct (Z.ltb_spec n w).
        * exists (firstn (Z.to_nat n) bs'). split; [eapply rdn_firstn; [exact Hbs'|lia]|].
          apply atruncate_sound; auto. rewrite bytes_le_firstn by lia. rewrite Hkn, Hval.
          change (zwrap (8 * w) (eval nu v) mod 2 ^ (8 * n)) with (zwrap (8 * n) (zwrap (8 * w) (eval nu v))).
          apply zwrap_zwrap. lia.
        * exists bs. split; [exact Hbs|apply FRESH; exact Hlen].
    - destruct (const_cover (vr_cells r) lo n) as [c|] eqn:Ecc; [|exists bs; split; [exact Hbs|apply FRESH; exact Hlen]].
      destruct (const_cover_sound SEGS (vr_cells r) nu mem (rbase nu r) lo n c CH ltac:(lia) Ecc) as [bs' (Hbs' & Hl' & Hv' & Hc)].
      exists bs'. split; [exact Hbs'|]. rewrite Hv'. rewrite ldval_sign_adjust by lia.
      apply res_word_same; [exact HL|now rewrite eval_lconst|apply lin_below_lconst].
    - destruct (const_cover (vr_cells r) lo n) as [c|] eqn:Ecc; [|exists bs; split; [exact Hbs|apply FRESH; exact Hlen]].
      destruct (const_cover_sound SEGS (vr_cells r) nu mem (rbase nu r) lo n c CH ltac:(lia) Ecc) as [bs' (Hbs' & Hl' & Hv' & Hc)].
      exists bs'. split; [exact Hbs'|]. rewrite Hv'. rewrite ldval_sign_adjust by lia.
      apply res_word_same; [exact HL|now rewrite eval_lconst|apply lin_below_lconst].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma sh_cover_in m o k w v : sh_cover m o = Some (k, (w, v)) -> In (k, (w, v)) m /\ k <= o < k + w.
  Proof.
    unfold sh_cover. intros H. apply find_some in H as [Hin Hb].
    apply cm_overlapping_in in Hin. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. auto.
  Qed.

  Lemma sh_load_sound A nu regs mem r o sg c :
    gamma2P A nu regs mem -> In r (vs_rgn A) -> is_shadow r = true -> is_data_shadow r = false ->
    vr_lo r <= o < vr_hi r -> sh_cover (vr_cells r) o = Some c ->
    exists b : byte,
      rdn SEGS mem (wordZ (rbase nu r + o)) 1 = Some [b] /\
      res_word (v1 A) nu (sh_load (v1 A) r o sg) (ldval sg 1 (bv_unsigned b)).
  Proof.
    intros HG2 Hr SH ND Ho Hc.
    pose proof (gamma2_lgamma _ _ _ _ HG2) as HL.
    pose proof HG2 as (G1 & _ & _ & _ & _ & RGN & _ & BEL2 & _ & _).
    destruct (RGN r Hr) as (B1 & B2 & B3 & _ & CELLS & PERM & _ & _).
    destruct (PERM ND) as [RD _]. destruct (RD o Ho) as [_ [b Hb]]. exists b. split; [exact Hb|].
    pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. simpl in Rb.
    unfold sh_load. rewrite Hc. destruct c as [k [w [e|]]].
    2:{ apply (fresh_loaded_sound (v1 A) nu 1 sg (bv_unsigned b)); [exact HL|lia|simpl; lia]. }
    destruct (sh_cover_in _ _ _ _ _ Hc) as [Hin Hk].
    destruct (CELLS _ _ _ Hin) as (L1 & L2 & L3 & RC). unfold rcell_holds in RC. rewrite SH in RC. simpl in RC.
    destruct (lin_is_const e) eqn:EC.
    - (* [comment removed for export] *)
      destruct (RC (o - k) ltac:(lia)) as (kb & Hkb & Hv).
      replace (rbase nu r + k + (o - k)) with (rbase nu r + o) in Hkb by lia.
      rewrite Hb in Hkb. injection Hkb as <-.
      rewrite ldval_sign_adjust by (simpl; lia). rewrite Hv.
      apply res_word_same; [exact HL|now rewrite eval_lconst|apply lin_below_lconst].
    - destruct (Z.eqb_spec w 1) as [->|Nw].
      + assert (k = o) by lia. subst k. cbn [cell_holds] in RC. destruct RC as (bs & Hbs & Hval).
        change (Z.to_nat 1) with 1%nat in Hbs. rewrite Hb in Hbs. injection Hbs as <-.
        destruct BEL2 as (_ & BR & _). destruct (BR r Hr) as (_ & Bc & _).
        apply areinterp_sound; [exact HL|lia|exact (Bc _ _ _ Hin)|].
        cbn [bytes_le_to_Z] in Hval. rewrite Z.shiftl_0_l, Z.lor_0_r in Hval. exact Hval.
      + apply (fresh_loaded_sound (v1 A) nu 1 sg (bv_unsigned b)); [exact HL|lia|simpl; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma sh_run_cover_sound pm b : forall fuel pos stop,
    sh_run_cover pm pos stop b fuel = true ->
    forall p, pos <= p < stop ->
      exists k' w' e', In (k', (w', Some e')) pm /\ k' <= p < k' + w' /\ lin_is_const e' = true /\ lc e' = b.
  Proof.
    induction fuel as [|f IH]; intros pos stop H p Hp; rewrite sh_run_cover_andb in H.
    - destruct (Z.leb_spec stop pos); [lia|discriminate].
    - destruct (Z.leb_spec stop pos); [lia|]. cbn [orb] in H.
      destruct (sh_cover pm pos) as [[k' [w' [e'|]]]|] eqn:SC; try discriminate.
      apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
      apply Z.eqb_eq in H2. apply Z.ltb_lt in H3. apply sh_cover_in in SC as [IN R].
      destruct (Z.lt_decidable p (k' + w')) as [LT|GE].
      + exists k', w', e'. repeat split; auto; lia.
      + eapply IH; [exact H4|lia].
  Qed.

  (* [comment removed for export] *)
  Lemma sh_uniform_sound A nu regs mem r lo hi o b :
    gamma2P A nu regs mem -> In r (vs_rgn A) -> is_shadow r = true -> is_data_shadow r = false ->
    vr_lo r <= o < vr_hi r -> lo <= o <= hi -> sh_uniform (vr_cells r) lo hi = Some b ->
    exists kb : byte,
      rdn SEGS mem (wordZ (rbase nu r + o)) 1 = Some [kb] /\ bv_unsigned kb = Z.land b 255.
  Proof.
    intros HG2 Hr SH ND Ho Hlh U.
    pose proof HG2 as (G1 & _ & _ & _ & _ & RGN & _ & BEL2 & _ & _).
    destruct (RGN r Hr) as (B1 & B2 & B3 & _ & CELLS & _ & _ & _).
    unfold sh_uniform in U. destruct (sh_cover (vr_cells r) lo) as [[k0 [w0 [e0|]]]|]; try discriminate.
    change (if lin_is_const e0 then sh_run_cover (vr_cells r) lo (hi + 1) (lc e0) (S (Datatypes.length (vr_cells r))) else false)
      with (lin_is_const e0 && sh_run_cover (vr_cells r) lo (hi + 1) (lc e0) (S (Datatypes.length (vr_cells r)))) in U.
    destruct (lin_is_const e0 && sh_run_cover (vr_cells r) lo (hi + 1) (lc e0) (S (Datatypes.length (vr_cells r)))) eqn:C; [|discriminate].
    injection U as <-. apply andb_prop in C as [_ C].
    destruct (sh_run_cover_sound _ _ _ _ _ C o ltac:(lia)) as (k' & w' & e' & IN & K12 & CE' & LCE).
    destruct (CELLS _ _ _ IN) as (L1 & L2 & L3 & RC). unfold rcell_holds in RC. rewrite SH, CE' in RC. cbn [andb] in RC.
    destruct (RC (o - k') ltac:(lia)) as (kb & Hkb & Hv). exists kb.
    replace (rbase nu r + k' + (o - k')) with (rbase nu r + o) in Hkb by lia. rewrite <- LCE. auto.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma nu_DATA8 A nu regs mem : gamma2P A nu regs mem -> nu DATA8 = e_data E1 / 8.
  Proof.
    intros HG2. pose proof (gamma2_fix _ _ _ _ _ _ _ _ HG2) as F. apply F.
    unfold fix_val2. replace (fix_val (ev1 E) DATA8) with (@None Z) by reflexivity. reflexivity.
  Qed.

  Lemma nu_SIZE2 A nu regs mem : gamma2P A nu regs mem -> nu SIZE = e_size E1.
  Proof.
    intros HG2. pose proof (gamma2_fix _ _ _ _ _ _ _ _ HG2) as F. apply F. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma data_granule A nu regs mem g :
    gamma2P A nu regs mem -> asan_mode P = true -> 8 <= vp_datal P -> 0 <= 8 * g < e_size E1 ->
    exists k : byte, rdn SEGS mem (wordZ (vp_shoff P + nu DATA8 + g)) 1 = Some [k]
      /\ (8 * g + 8 <= e_size E1 -> bv_unsigned k = 0)
      /\ (e_size E1 < 8 * g + 8 -> bv_unsigned k = e_size E1 - 8 * g).
  Proof.
    intros HG2 AM AL Hg. pose proof HG2 as (_ & _ & HMC2 & _). destruct HMC2 as (_ & _ & DS & _).
    unfold asan_mode in AM. destruct (DS AL ltac:(destruct (vp_fs P); [discriminate|congruence])) as [D1 _].
    rewrite (nu_DATA8 _ _ _ _ HG2). unfold shadow_byte in D1. exact (D1 g Hg).
  Qed.

  #[using="Type"] Lemma data_margin A nu regs mem g :
    gamma2P A nu regs mem -> asan_mode P = true -> 8 <= vp_datal P -> 0 < e_size E1 ->
    (-16 <= 8 * g /\ 8 * g <= e_size E1 + 15) ->
    exists b : byte, rdn SEGS mem (wordZ (vp_shoff P + nu DATA8 + g)) 1 = Some [b].
  Proof.
    intros HG2 AM AL Hsz Hg. pose proof HG2 as (_ & HE2 & HMC2 & _). destruct HMC2 as (_ & _ & DS & _).
    unfold asan_mode in AM. destruct (DS AL ltac:(destruct (vp_fs P); [discriminate|congruence])) as (_ & D2 & _).
    rewrite (nu_DATA8 _ _ _ _ HG2). apply D2; [|exact Hsz]. unfold shadow_byte.
    destruct HE2 as (HE1 & (DAL & DPOS & DAL8 & _) & _). specialize (DAL8 AL). unfold E1 in *.
    set (d := e_data (ev1 E)) in *. set (sz := e_size (ev1 E)) in *.
    set (q := d / 8).
    assert (E8 : d = q * 8) by (pose proof (Z.div_mod d 8 ltac:(lia)); lia).
    assert (H1 : (d + sz - 1) / 8 = q + (sz - 1) / 8).
    { replace (d + sz - 1) with (q * 8 + (sz - 1)) by lia. rewrite Z.div_add_l by lia. reflexivity. }
    assert (H2 : (sz - 1) / 8 + 2 = (sz + 15) / 8).
    { replace (sz + 15) with ((sz - 1) + 2 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (H3 : g <= (sz + 15) / 8) by (apply Z.div_le_lower_bound; (ltac2:(LK.k [@DPOS; @Hg]); lia)).
    assert (H4 : -2 <= g) by lia.
    rewrite H1. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma data_shadow_load_sound A nu regs mem (g : lin) sg :
    gamma2P A nu regs mem -> asan_mode P = true -> 8 <= vp_datal P ->
    lin_below g (vs_next (v1 A)) = true ->
    -16 <= 8 * eval nu g -> 8 * eval nu g - nu SIZE <= 15 -> 1 <= nu SIZE ->
    exists b : byte,
      rdn SEGS mem (wordZ (vp_shoff P + nu DATA8 + eval nu g)) 1 = Some [b] /\
      match data_shadow_load (v1 A) g sg with
      | DS_one v A1 => res_word (v1 A) nu (v, A1) (ldval sg 1 (bv_unsigned b))
      | DS_two A0 A1 vj => res_word (v1 A) nu (Some (lconst 0), A0) (ldval sg 1 (bv_unsigned b))
                           \/ res_word (v1 A) nu (vj, A1) (ldval sg 1 (bv_unsigned b))
      | DS_fail _ => True
      end.
  Proof.
    intros HG2 AM AL Bg G1 G2 G3.
    pose proof (gamma2_lgamma _ _ _ _ HG2) as HL.
    pose proof (nu_SIZE2 _ _ _ _ HG2) as ES. rewrite ES in G2, G3.
    destruct (data_margin A nu regs mem (eval nu g) HG2 AM AL ltac:(lia) ltac:(lia)) as [b Hb].
    exists b. split; [exact Hb|].
    pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. simpl in Rb.
    assert (LD0 : forall sg', ldval sg' 1 0 = zwrap 64 (eval nu (lconst 0))).
    { intros sg'. rewrite eval_lconst. unfold ldval. destruct sg'; reflexivity. }
    unfold data_shadow_load. rewrite ?if_andb, ?if_orb.
    destruct (qge (v1 A) (lscale 8 g) 0 && qle (v1 A) (lsub (laddc (lscale 8 g) 8) (lsym SIZE)) 0) eqn:C1.
    { (* [comment removed for export] *)
      apply andb_prop in C1 as [Q1 Q2]. pose proof (qge_sound _ _ _ _ HL Q1) as X1. pose proof (qle_sound _ _ _ _ HL Q2) as X2.
      rewrite eval_lscale in X1. rewrite eval_lsub, eval_laddc, eval_lscale, eval_lsym, ES in X2.
      destruct (data_granule A nu regs mem (eval nu g) HG2 AM AL ltac:(lia)) as (k & Hk & K0 & _).
      rewrite Hb in Hk. injection Hk as <-. rewrite (K0 ltac:(lia)), LD0.
      apply res_word_same; [exact HL|reflexivity|apply lin_below_lconst]. }
    destruct (qge (v1 A) (lscale 8 g) 0 && qle (v1 A) (lsub (laddc (lscale 8 g) 1) (lsym SIZE)) 0) eqn:C2.
    { (* [comment removed for export] *)
      apply andb_prop in C2 as [Q1 Q2]. pose proof (qge_sound _ _ _ _ HL Q1) as Y1. pose proof (qle_sound _ _ _ _ HL Q2) as Y2.
      rewrite eval_lscale in Y1. rewrite eval_lsub, eval_laddc, eval_lscale, eval_lsym, ES in Y2.
      destruct (data_granule A nu regs mem (eval nu g) HG2 AM AL ltac:(lia)) as (k & Hk & K0 & K1).
      rewrite Hb in Hk. injection Hk as <-.
      pose proof (afresh_sound (v1 A) nu (Some 1, Some 7)) as AF.
      destruct (afresh (v1 A) (Some 1, Some 7)) as [vj Aj] eqn:EAF.
      destruct (Z.le_gt_cases (8 * eval nu g + 8) (e_size E1)) as [IN|LAST].
      - (* [comment removed for export] *)
        rewrite (K0 IN).
        destruct vj as [ej|].
        + destruct (aassume Aj (lsub (ladd (lscale 8 g) ej) (lsym SIZE))) as [ok1 Aj1] eqn:E1'.
          destruct (aassume Aj1 (lneg (lsub (ladd (lscale 8 g) ej) (lsym SIZE)))) as [ok2 Aj2] eqn:E2'.
          destruct (ok1 && ok2).
          * left. rewrite LD0. apply res_word_same; [exact HL|reflexivity|apply lin_below_lconst].
          * rewrite LD0. apply res_word_same; [exact HL|reflexivity|apply lin_below_lconst].
        + exact I.
      - (* [comment removed for export] *)
        specialize (K1 LAST). set (x := e_size E1 - 8 * eval nu g) in *.
        assert (Hx : 1 <= x <= 7) by lia.
        specialize (AF x HL ltac:(split; simpl; lia)).
        destruct vj as [ej|]; [|destruct AF as [? (_ & _ & F)]; destruct F].
        destruct AF as [nu1 (X1' & L1 & Eej & Bej)].
        assert (Be : lin_below (lsub (ladd (lscale 8 g) ej) (lsym SIZE)) (vs_next Aj) = true).
        { apply lin_below_lsub; [apply lin_below_ladd; [apply lin_below_lscale|exact Bej]|apply lin_below_lsym].
          - eapply lin_below_mono; [|exact Bg]. exact (proj1 (proj2 X1')).
          - destruct L1 as (_ & _ & _ & _ & BB). destruct BB as [BF _]. unfold SIZE, LAST_FIXED in *. lia. }
        assert (Ee : eval nu1 (lsub (ladd (lscale 8 g) ej) (lsym SIZE)) = 0).
        { rewrite eval_lsub, eval_ladd, eval_lscale, eval_lsym, Eej.
          rewrite (eval_ext_below _ _ _ _ (proj1 X1') Bg).
          rewrite (proj1 X1'); [|unfold SIZE; destruct HL as (_ & _ & _ & _ & [BF _]); unfold LAST_FIXED in BF; lia].
          rewrite ES. lia. }
        pose proof (aassume_sound Aj nu1 _ L1 ltac:(rewrite Ee; lia) Be) as (F1 & L2 & X2).
        destruct (aassume Aj (lsub (ladd (lscale 8 g) ej) (lsym SIZE))) as [ok1 Aj1] eqn:E1'. simpl in F1, L2, X2. subst ok1.
        assert (Be2 : lin_below (lneg (lsub (ladd (lscale 8 g) ej) (lsym SIZE))) (vs_next Aj1) = true).
        { apply lin_below_lneg. eapply lin_below_mono; [|exact Be]. exact (proj1 (proj2 X2)). }
        pose proof (aassume_sound Aj1 nu1 _ L2 ltac:(rewrite eval_lneg, Ee; lia) Be2) as (F2 & L3 & X3).
        destruct (aassume Aj1 (lneg (lsub (ladd (lscale 8 g) ej) (lsym SIZE)))) as [ok2 Aj2] eqn:E2'. simpl in F2, L3, X3. subst ok2.
        simpl. right. exists nu1. split; [eapply aext_trans; [exact X1'|eapply aext_trans; [exact X2|exact X3]]|].
        split; [exact L3|]. split.
        + rewrite Eej, K1. unfold ldval, x. destruct sg; simpl.
          * rewrite zswrap_id by (simpl; lia). reflexivity.
          * symmetry. apply zwrap_id. lia.
        + eapply lin_below_mono; [|exact Bej]. pose proof (proj1 (proj2 X2)). pose proof (proj1 (proj2 X3)). lia. }
    destruct ((qge (v1 A) (lscale 8 g) (-16) && qle (v1 A) (laddc (lscale 8 g) 1) 0)
              || (qge (v1 A) (lsub (lscale 8 g) (lsym SIZE)) 0 && qle (v1 A) (lsub (lscale 8 g) (lsym SIZE)) 15)) eqn:C3.
    { destruct (fresh_loaded (v1 A) 1 sg) as [v A2] eqn:EF.
      pose proof (fresh_loaded_sound (v1 A) nu 1 sg (bv_unsigned b) HL ltac:(lia) ltac:(simpl; lia)) as R. rewrite EF in R. exact R. }
    exact I.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma kbyte_sound A nu regs mem a n v :
    gamma2P A nu regs mem -> 0 < n <= 8 -> kbyte_get P a n = Some v ->
    0 <= a /\ a + n <= 2 ^ 64 /\
    exists bs, rdn SEGS mem (wordZ a) (Z.to_nat n) = Some bs /\ bytes_le_to_Z bs = v /\ 0 <= v < 2 ^ (8 * n).
  Proof.
    intros HG2 Hn Hk. pose proof HG2 as (_ & HE2 & HMC2 & _). destruct HMC2 as (KC & _ & _ & _ & _ & KR).
    unfold kbyte_get in Hk.
    destruct (kcell_get (vp_kcells P) a n) as [v'|] eqn:K1.
    - injection Hk as <-. apply kcell_get_in in K1. destruct (KC _ _ _ K1) as (A0 & W0 & AW & bs & Hbs & Hv).
      split; [lia|]. split; [lia|]. exists bs. split; [exact Hbs|]. split; [exact Hv|].
      pose proof (rdn_length _ _ _ _ _ Hbs) as L. pose proof (bytes_le_to_Z_bound bs) as B. pose proof (bytes_le_to_Z_nonneg bs).
      rewrite L, Z2Nat.id in B by lia. lia.
    - destruct (Z.eqb_spec n 1) as [->|]; [|discriminate].
      destruct (krun_get (vp_kruns P) a) as [b|] eqn:K2; [|discriminate]. injection Hk as <-.
      destruct (krun_get_in _ _ _ K2) as (lo & hi & Hin & R).
      destruct (KR _ _ _ Hin) as (L0 & H64 & Hb). destruct (Hb a R) as (k & Hk' & Hv).
      split; [lia|]. split; [lia|]. exists [k]. split; [exact Hk'|].
      pose proof (bv_unsigned_in_range 8 k) as Rk. unfold bv_modulus in Rk. simpl in Rk.
      cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. split; [exact Hv|].
      pose proof (Z.land_nonneg b 255). assert (Z.land b 255 <= 255) by (rewrite <- Hv; lia). simpl. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fork_skip_actual A1 nu q : lgamma A1 nu -> fork_skip A1 q (nu q) = false.
  Proof.
    intros HL. unfold fork_skip. destruct (pm_get q (scong (vs_store A1))) as [[m r]|] eqn:G; [|reflexivity].
    destruct (Z.eqb_spec m 0) as [|NZ]; [reflexivity|]. cbn [negb andb].
    pose proof (sat_cong nu _ (proj1 HL) q m r G) as D.
    apply Z.mod_divide in D; [|exact NZ]. rewrite D. reflexivity.
  Qed.

  Lemma kfork_states_in A q c sg rd : forall k v l v0 b0,
    kfork_states P A q c sg rd v k = Some l -> v <= v0 < v + Z.of_nat k -> fork_skip (v1 A) q v0 = false ->
    kbyte_get P (c + v0) 1 = Some b0 ->
    In (finish2 (with_v1 A (asetbox (v1 A) q (Some v0, Some v0))) rd (Some (lconst (sign_adjust sg 1 b0)))) l.
  Proof.
    induction k as [|k IH]; simpl; intros v l v0 b0 H Hv NSK Hb; [lia|].
    destruct (fork_skip (v1 A) q v) eqn:SK.
    { destruct (Z.eq_dec v0 v) as [->|Nv]; [congruence|]. eapply IH; eauto. lia. }
    destruct (kbyte_get P (c + v) 1) as [b|] eqn:Kb; [|discriminate].
    destruct (kfork_states P A q c sg rd (v + 1) k) as [rest|] eqn:Kr; [|discriminate]. injection H as <-.
    destruct (Z.eq_dec v0 v) as [->|Nv].
    - left. rewrite Kb in Hb. injection Hb as <-. reflexivity.
    - right. eapply IH; eauto. lia.
  Qed.

  Lemma shfork_states_in A r q c sg rd : forall k v l v0 kk w e,
    shfork_states A r q c sg rd v k = Some l -> v <= v0 < v + Z.of_nat k -> fork_skip (v1 A) q v0 = false ->
    sh_cover (vr_cells r) (c + v0) = Some (kk, (w, Some e)) -> lin_is_const e = true ->
    In (finish2 (with_v1 A (asetbox (v1 A) q (Some v0, Some v0))) rd
                (Some (lconst (sign_adjust sg 1 (Z.land (lc e) 255))))) l.
  Proof.
    induction k as [|k IH]; simpl; intros v l v0 kk w e H Hv NSK Hc He; [lia|].
    destruct (fork_skip (v1 A) q v) eqn:SK.
    { destruct (Z.eq_dec v0 v) as [->|Nv]; [congruence|]. eapply IH; eauto. lia. }
    destruct (sh_cover (vr_cells r) (c + v)) as [[k1 [w1 [e1|]]]|] eqn:C1; try discriminate.
    destruct (shfork_states A r q c sg rd (v + 1) k) as [rest|] eqn:Kr; [|discriminate].
    destruct (lin_is_const e1) eqn:Ec1; [|discriminate]. injection H as <-.
    destruct (Z.eq_dec v0 v) as [->|Nv].
    - left. rewrite C1 in Hc. injection Hc as <- <- <-. reflexivity.
    - right. eapply IH; eauto. lia.
  Qed.

  Lemma shfork_states_cover A r q c sg rd : forall k v l v0,
    shfork_states A r q c sg rd v k = Some l -> v <= v0 < v + Z.of_nat k -> fork_skip (v1 A) q v0 = false ->
    exists kk w e, sh_cover (vr_cells r) (c + v0) = Some (kk, (w, Some e)) /\ lin_is_const e = true.
  Proof.
    induction k as [|k IH]; simpl; intros v l v0 H Hv NSK; [lia|].
    destruct (fork_skip (v1 A) q v) eqn:SK.
    { destruct (Z.eq_dec v0 v) as [->|Nv]; [congruence|]. eapply IH; eauto. lia. }
    destruct (sh_cover (vr_cells r) (c + v)) as [[k1 [w1 [e1|]]]|] eqn:C1; try discriminate.
    destruct (shfork_states A r q c sg rd (v + 1) k) as [rest|] eqn:Kr; [|discriminate].
    destruct (lin_is_const e1) eqn:Ec1; [|discriminate].
    destruct (Z.eq_dec v0 v) as [->|Nv]; [eauto 6|]. eapply IH; eauto. lia.
  Qed.

  Lemma kfork_states_byte A q c sg rd : forall k v l v0,
    kfork_states P A q c sg rd v k = Some l -> v <= v0 < v + Z.of_nat k -> fork_skip (v1 A) q v0 = false ->
    exists b0, kbyte_get P (c + v0) 1 = Some b0.
  Proof.
    induction k as [|k IH]; simpl; intros v l v0 H Hv NSK; [lia|].
    destruct (fork_skip (v1 A) q v) eqn:SK.
    { destruct (Z.eq_dec v0 v) as [->|Nv]; [congruence|]. eapply IH; eauto. lia. }
    destruct (kbyte_get P (c + v) 1) as [b|] eqn:Kb; [|discriminate].
    destruct (kfork_states P A q c sg rd (v + 1) k) as [rest|] eqn:Kr; [|discriminate].
    destruct (Z.eq_dec v0 v) as [->|Nv]; [eauto|]. eapply IH; eauto. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma point_box_post A nu regs mem pc rom (rd : reg) (q : sym) (wl : word) (c0 : Z) :
    gamma2P A nu regs mem -> vs2_pc A = bv_unsigned pc -> rz rd <> 0 -> (q < vs_next (v1 A))%positive ->
    bv_unsigned wl = zwrap 64 c0 ->
    RiscvSemantics.step SEGS (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd wl) (v_addi pc 4) mem rom) ->
    step_post2 SEGS P E mem0 A nu
      [finish2 (with_v1 A (asetbox (v1 A) q (Some (nu q), Some (nu q)))) (rz rd) (Some (lconst c0))] regs mem pc rom.
  Proof.
    intros HG2 Hpc Hrd Hq Hw ST.
    pose proof (gamma2_lgamma _ _ _ _ HG2) as HL.
    destruct (asetbox_sound (v1 A) nu q (Some (nu q), Some (nu q)) HL ltac:(split; simpl; lia) Hq) as [L1 X1].
    refine (step_post_lift SEGS P E mem0 PO2 A nu
              [finish (asetbox (v1 A) q (Some (nu q), Some (nu q))) (rz rd) (Some (lconst c0))] regs mem pc rom HG2 _ _ _).
    { intros x [<-|[]]. eapply globs_same; [exact HG2|]. apply (globs_finish_aext (v1 A) _ nu nu). exact X1. }
    { intros regs' pc' mem' ST'. left. rewrite ST in ST'. injection ST'; auto. }
    eapply (step_post_finish SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) _ nu nu); eauto.
    - exact (proj1 HG2).
    - split; [rewrite eval_lconst; exact Hw|apply lin_below_lconst].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition XSTACK_stmt : Prop :=
    forall A nu regs mem pc rom w sz sg (rd rs1 : reg) (imm : bv 12) addr off lo hi succs,
      gamma2P A nu regs mem -> vs2_pc A = bv_unsigned pc ->
      fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Load sz sg rd rs1 imm, 4) ->
      rz rd <> 0 -> addr_of (v1 A) (rz rs1) (bv_signed imm) = Some addr -> (sz = SZ8 -> sg = true) ->
      classify P1 (v1 A) addr (msize_z sz) false = COk (RStack off lo hi) ->
      x_load_stack P A addr off lo hi (msize_z sz) sg (rz rd) = VR2_next succs ->
      forallb (globs_in_fcells P) succs = true ->
      step_post2 SEGS P E mem0 A nu succs regs mem pc rom.

  (* [comment removed for export] *)
  Definition XINSTALL_stmt : Prop :=
    forall A nu regs mem pc rom w sz sg (rd rs1 : reg) (imm : bv 12) addr r off lo hi v A3 m',
      gamma2P A nu regs mem -> vs2_pc A = bv_unsigned pc ->
      fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Load sz sg rd rs1 imm, 4) ->
      rz rd <> 0 -> addr_of (v1 A) (rz rs1) (bv_signed imm) = Some addr ->
      classify2 A addr (msize_z sz) false = Some (C2Rgn r off lo hi) ->
      match vr_kind r with RK_fake _ _ | RK_arg => True | _ => False end ->
      install_ok (vr_cells r) lo hi (msize_z sz) = true ->
      load_install (v1 A) (vr_cells r) lo (msize_z sz) sg = Some (v, A3, m') ->
      globs_in_fcells P (finish2 (with_v1 (set_rgn A (rgn_upd (vs_rgn A) (set_cells r m'))) A3) (rz rd) v) = true ->
      step_post2 SEGS P E mem0 A nu [finish2 (with_v1 (set_rgn A (rgn_upd (vs_rgn A) (set_cells r m'))) A3) (rz rd) v] regs mem pc rom.

  Hypothesis XSTACK : XSTACK_stmt.
  Hypothesis XINSTALL : XINSTALL_stmt.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma lgamma_sat A nu : lgamma A nu -> sat nu (vs_store A).
  Proof. intros H; exact (proj1 H). Qed.

  Lemma eval_free_single A addr q c nu : free_single A addr = Some (q, c) -> eval nu addr = c + nu q.
  Proof.
    unfold free_single. destruct (lt addr) as [|[q' k] t] eqn:L; [discriminate|].
    destruct k as [|p|p]; try (destruct t; discriminate).
    destruct p; try (destruct t; discriminate). destruct t; [|discriminate].
    destruct (Pos.leb q' LAST_FIXED2 || has_base A (lsym q')); [discriminate|].
    intros H; injection H as <- <-. unfold eval. rewrite L. cbn [eval_terms]. lia.
  Qed.

  Lemma free_single_below A addr q c b : free_single A addr = Some (q, c) -> lin_below addr b = true -> (q < b)%positive.
  Proof.
    unfold free_single. destruct (lt addr) as [|[q' k] t] eqn:L; [discriminate|].
    destruct k as [|p|p]; try (destruct t; discriminate).
    destruct p; try (destruct t; discriminate). destruct t; [|discriminate].
    destruct (Pos.leb q' LAST_FIXED2 || has_base A (lsym q')); [discriminate|].
    intros H Hb; injection H as <- <-. apply (proj1 (lin_below_iff addr b) Hb). unfold lsyms. rewrite L. left; reflexivity.
  Qed.

  #[using="P1 E1 PO2 XSTACK XINSTALL"] Theorem x_load2_sound A nu regs mem pc rom w sz sg (rd rs1 : reg) (imm : bv 12) succs :
    gamma2P A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Load sz sg rd rs1 imm, 4) ->
    x_load2 P A sz sg (rz rd) (rz rs1) (bv_signed imm) = VR2_next succs ->
    forallb (globs_in_fcells P) succs = true ->
    step_post2 SEGS P E mem0 A nu succs regs mem pc rom.
  Proof.
    intros HG2 Hpc Hf He Hd Hx GLB. pose proof (gamma2_lgamma _ _ _ _ HG2) as HL.
    pose proof HG2 as (G1 & HE2 & HMC2 & FIX2 & DIV & RGN & LIVE & BEL2 & GL0 & FI2).
    assert (V1CASE : forall l, x_load P1 (v1 A) sz sg (rz rd) (rz rs1) (bv_signed imm) = VR_next l ->
                     succs = map (with_v1 A) l ->
                     step_post2 SEGS P E mem0 A nu (map (with_v1 A) l) regs mem pc rom).
    { intros l Hl El.
      assert (Hl' : vstep P1 (v1 A) (Load sz sg rd rs1 imm) = VR_next l) by (cbn [vstep vstep_core]; rewrite bvs_eq; exact Hl).   (* [comment removed for export] *)
      eapply lift1_sound; eauto; [|exact I]. intros x Hxl. rewrite forallb_forall in GLB. apply GLB. rewrite El. apply in_map. exact Hxl. }
    unfold x_load2 in Hx.
    assert (Hsz : sz = SZ8 -> sg = true) by (intros ->; destruct sg; [reflexivity|discriminate]).
    assert (Hn : 0 < msize_z sz <= 8) by (destruct sz; simpl; lia).
    assert (BODY :
      (if Z.eqb (rz rd) 0 then lift1 A (x_load (p1 P) (v1 A) sz sg (rz rd) (rz rs1) (bv_signed imm)) else
       match addr_of (v1 A) (rz rs1) (bv_signed imm) with
       | None => VR2_fail "load via Top address"
       | Some addr =>
           match (if lin_is_const addr then kbyte_get P (lc addr) (msize_z sz) else None) with
           | Some v => one2 (finish2 A (rz rd) (Some (lconst (sign_adjust sg (msize_z sz) v))))
           | None =>
               match (if Z.eqb (msize_z sz) 1 && asan_mode P then kfork P A addr sg (rz rd) else None) with
               | Some r => r
               | None =>
               match classify2 A addr (msize_z sz) false with
               | None =>
                   if asan_mode P then
                     match classify (p1 P) (v1 A) addr (msize_z sz) false with
                     | COk (RStack off lo hi) => x_load_stack P A addr off lo hi (msize_z sz) sg (rz rd)
                     | CDead => VR2_next []
                     | CFail m => VR2_fail m
                     | COk r => let '(v, A1) := load_val (p1 P) (v1 A) r addr (msize_z sz) sg in one2 (finish2 (with_v1 A A1) (rz rd) v)
                     end
                   else lift1 A (x_load (p1 P) (v1 A) sz sg (rz rd) (rz rs1) (bv_signed imm))
               | Some (C2Fail m) => VR2_fail m
               | Some C2Dead => VR2_next []
               | Some (C2Rgn r off lo hi) => x_load_rgn P A r off lo hi (msize_z sz) sg (rz rd)
               end end
           end
       end) = VR2_next succs).
    { destruct sz; destruct sg; try exact Hx. discriminate. }
    clear Hx. set (n := msize_z sz) in *.
    destruct (Z.eqb (rz rd) 0) eqn:Erd.
    { apply lift1_next_inv in BODY as (l & Hl & ->). apply V1CASE; [exact Hl|reflexivity]. }
    assert (Hrd : rz rd <> 0) by (intros X; rewrite X in Erd; discriminate).
    assert (Hbe : bv_eqb rd 0%bv = false) by (rewrite bv_eqb_rz; exact Erd).
    destruct (addr_of (v1 A) (rz rs1) (bv_signed imm)) as [addr|] eqn:Ha; [|discriminate].
    destruct (addr_of_sound SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem rs1 (bv_signed imm) addr G1 Ha) as [Baddr Hva].
    (* [comment removed for export] *)
    destruct (if lin_is_const addr then kbyte_get P (lc addr) n else None) as [v|] eqn:K.
    { destruct (lin_is_const addr) eqn:EC; [|discriminate].
      injection BODY as <-.
      destruct (kbyte_sound A nu regs mem (lc addr) n v HG2 Hn K) as (A0 & AW & bs & Hbs & Hv & Rv).
      destruct (load_machine A nu regs mem pc rom w sz sg rd rs1 imm addr (lc addr) bs HG2 Hf He Hd Hsz Ha
                  (eval_is_const nu addr EC) Hbs) as [wl [Hwl ST]].
      rewrite Hbe in ST.
      eapply (finish2_post A nu regs mem pc rom rd wl (Some (lconst (sign_adjust sg n v))) (v1 A)); eauto.
      apply res_word_same; [exact HL| |apply lin_below_lconst].
      rewrite Hwl, Hv, eval_lconst. apply ldval_sign_adjust; lia. }
    (* [comment removed for export] *)
    destruct (if Z.eqb n 1 && asan_mode P then kfork P A addr sg (rz rd) else None) as [r0|] eqn:KF.
    { subst r0. destruct (Z.eqb n 1 && asan_mode P) eqn:N1; [|discriminate]. apply andb_prop in N1 as [N1 _]. apply Z.eqb_eq in N1.
      unfold kfork in KF. destruct (base_syms A addr); [|discriminate]. cbn [negb] in KF.
      destruct (free_single A addr) as [[q c]|] eqn:FS; [|discriminate].
      destruct (lp_bounds (vs_store (v1 A)) (lsym q)) as [[lo|] [hi|]] eqn:LB; try discriminate.
      destruct (Z.ltb hi lo || Z.ltb 15 (hi - lo)) eqn:W; [discriminate|].
      destruct (kfork_states P A q c sg (rz rd) lo (S (Z.to_nat (hi - lo)))) as [l|] eqn:KS; [|discriminate].
      injection KF as <-.
      pose proof (lp_bounds_sound nu (vs_store (v1 A)) (lgamma_sat _ _ HL) (lsym q)) as QB.
      rewrite LB, eval_lsym in QB. destruct QB as [Q1 Q2]. simpl in Q1, Q2.
      apply orb_false_iff in W as [W1 W2]. apply Z.ltb_ge in W1. apply Z.ltb_ge in W2.
      pose proof (fork_skip_actual (v1 A) nu q HL) as NSK.
      destruct (kfork_states_byte A q c sg (rz rd) _ _ _ (nu q) KS ltac:(lia) NSK) as [b0 Hb0].
      pose proof (kfork_states_in A q c sg (rz rd) _ _ _ (nu q) b0 KS ltac:(lia) NSK Hb0) as IN.
      pose proof (eval_free_single A addr q c nu FS) as Eaddr.
      destruct (kbyte_sound A nu regs mem (c + nu q) 1 b0 HG2 ltac:(lia) Hb0) as (A0 & AW & bs & Hbs & Hv & Rv).
      subst n. destruct (load_machine A nu regs mem pc rom w sz sg rd rs1 imm addr (c + nu q) bs HG2 Hf He Hd Hsz Ha Eaddr
                  ltac:(rewrite N1; exact Hbs)) as [wl [Hwl ST]].
      rewrite Hbe in ST.
      eapply step_post2_mono.
      { eapply (point_box_post A nu regs mem pc rom rd q wl); [exact HG2|exact Hpc|exact Hrd| | |exact ST].
        - eapply free_single_below; eauto.
        - rewrite Hwl, Hv. apply ldval_sign_adjust; rewrite ?N1; simpl; lia. }
      intros x Hx. destruct Hx as [<-|[]]. rewrite N1. exact IN. }
    (* [comment removed for export] *)
    destruct (classify2 A addr n false) as [[r off lo hi| |m]|] eqn:CL.
    4:{ destruct (asan_mode P) eqn:AM.
        2:{ apply lift1_next_inv in BODY as (l & Hl & ->). apply V1CASE; [exact Hl|reflexivity]. }
        (* [comment removed for export] *)
        assert (XLD : x_load P1 (v1 A) sz sg (rz rd) (rz rs1) (bv_signed imm)
                      = match classify P1 (v1 A) addr n false with
                        | CDead => VR_next []
                        | CFail m => VR_fail m
                        | COk r => let '(v, A1) := load_val P1 (v1 A) r addr n sg in one (finish A1 (rz rd) v)
                        end).
        { unfold x_load. fold n. rewrite Ha. destruct sz; destruct sg; try reflexivity. exfalso. discriminate (Hsz eq_refl). }
        change (p1 P) with P1 in BODY.
        destruct (classify P1 (v1 A) addr n false) as [rg| |m] eqn:CV.
        - destruct rg as [off lo hi|dk|glo ghi].
          + eapply XSTACK; eauto.
          + destruct (load_val P1 (v1 A) (RData dk) addr n sg) as [v A1] eqn:LV. injection BODY as <-.
            apply (V1CASE [finish A1 (rz rd) v]); [rewrite XLD; reflexivity|reflexivity].
          + destruct (load_val P1 (v1 A) (RImg glo ghi) addr n sg) as [v A1] eqn:LV. injection BODY as <-.
            apply (V1CASE [finish A1 (rz rd) v]); [rewrite XLD; reflexivity|reflexivity].
        - injection BODY as <-. apply (V1CASE []); [rewrite XLD; reflexivity|reflexivity].
        - discriminate. }
    3:{ discriminate. }
    2:{ exfalso. eapply classify2_dead; eauto. }
    destruct (classify2_rgn A addr n false r off lo hi CL) as (B & r1 & HB & HC & HR1 & HCL).
    destruct (classify_rgn_sound A nu r1 addr n false r off lo hi HL ltac:(lia) HCL) as (-> & Eoff & Eaddr & NDS & DSH).
    pose proof (rgn_in _ _ _ HR1) as Hr.
    pose proof (RGN r1 Hr) as ROK. destruct ROK as (RB1 & RB2 & RB3 & RDS & CELLS & PERM & NUL & KIND).
    assert (Boff : lin_below off (vs_next (v1 A)) = true).
    { rewrite Eoff. apply lin_below_laddc, lin_below_lsub; [exact Baddr|apply lin_below_lsym].
      destruct BEL2 as (_ & BR & _). exact (proj1 (BR r1 Hr)). }
    unfold x_load_rgn in BODY. unfold kind_ok in KIND.
    destruct (vr_kind r1) as [cid fl| |owner|s|] eqn:K1; rewrite ?K1 in KIND.
    - (* [comment removed for export] *)
      destruct (install_ok (vr_cells r1) lo hi n) eqn:IOK.
      { destruct (load_install (v1 A) (vr_cells r1) lo n sg) as [[[v3 A3] m']|] eqn:INS.
        - injection BODY as <-. rewrite forallb_forall in GLB.
          eapply (XINSTALL A nu regs mem pc rom w sz sg rd rs1 imm addr r1 off lo hi v3 A3 m'); eauto; [rewrite K1; exact I|].
          apply GLB. left; reflexivity.
        - destruct (NDS ltac:(unfold is_data_shadow; rewrite K1; reflexivity)) as (R1 & R2 & R3 & _).
          destruct (load_cells_sound A nu regs mem r1 off lo hi n sg HG2 Hr ltac:(unfold is_shadow; rewrite K1; reflexivity)
                      Hn R1 R2 R3) as [bs [Hbs RW]].
          destruct (load_cells (v1 A) (vr_cells r1) off lo hi n sg) as [v A1] eqn:LC. injection BODY as <-.
          destruct (load_machine A nu regs mem pc rom w sz sg rd rs1 imm addr _ bs HG2 Hf He Hd Hsz Ha Eaddr Hbs) as [wl [Hwl ST]].
          rewrite Hbe in ST. eapply finish2_post; eauto. rewrite Hwl. exact RW. }
      destruct (NDS ltac:(unfold is_data_shadow; rewrite K1; reflexivity)) as (R1 & R2 & R3 & _).
      destruct (load_cells_sound A nu regs mem r1 off lo hi n sg HG2 Hr ltac:(unfold is_shadow; rewrite K1; reflexivity)
                  Hn R1 R2 R3) as [bs [Hbs RW]].
      destruct (load_cells (v1 A) (vr_cells r1) off lo hi n sg) as [v A1] eqn:LC. injection BODY as <-.
      destruct (load_machine A nu regs mem pc rom w sz sg rd rs1 imm addr _ bs HG2 Hf He Hd Hsz Ha Eaddr Hbs) as [wl [Hwl ST]].
      rewrite Hbe in ST. eapply finish2_post; eauto. rewrite Hwl. exact RW.
    - (* [comment removed for export] *)
      destruct (install_ok (vr_cells r1) lo hi n) eqn:IOK.
      { destruct (load_install (v1 A) (vr_cells r1) lo n sg) as [[[v3 A3] m']|] eqn:INS.
        - injection BODY as <-. rewrite forallb_forall in GLB.
          eapply (XINSTALL A nu regs mem pc rom w sz sg rd rs1 imm addr r1 off lo hi v3 A3 m'); eauto; [rewrite K1; exact I|].
          apply GLB. left; reflexivity.
        - destruct (NDS ltac:(unfold is_data_shadow; rewrite K1; reflexivity)) as (R1 & R2 & R3 & _).
          destruct (load_cells_sound A nu regs mem r1 off lo hi n sg HG2 Hr ltac:(unfold is_shadow; rewrite K1; reflexivity)
                      Hn R1 R2 R3) as [bs [Hbs RW]].
          destruct (load_cells (v1 A) (vr_cells r1) off lo hi n sg) as [v A1] eqn:LC. injection BODY as <-.
          destruct (load_machine A nu regs mem pc rom w sz sg rd rs1 imm addr _ bs HG2 Hf He Hd Hsz Ha Eaddr Hbs) as [wl [Hwl ST]].
          rewrite Hbe in ST. eapply finish2_post; eauto. rewrite Hwl. exact RW. }
      destruct (NDS ltac:(unfold is_data_shadow; rewrite K1; reflexivity)) as (R1 & R2 & R3 & _).
      destruct (load_cells_sound A nu regs mem r1 off lo hi n sg HG2 Hr ltac:(unfold is_shadow; rewrite K1; reflexivity)
                  Hn R1 R2 R3) as [bs [Hbs RW]].
      destruct (load_cells (v1 A) (vr_cells r1) off lo hi n sg) as [v A1] eqn:LC. injection BODY as <-.
      destruct (load_machine A nu regs mem pc rom w sz sg rd rs1 imm addr _ bs HG2 Hf He Hd Hsz Ha Eaddr Hbs) as [wl [Hwl ST]].
      rewrite Hbe in ST. eapply finish2_post; eauto. rewrite Hwl. exact RW.
    - (* [comment removed for export] *) discriminate.
    - (* [comment removed for export] *)
      destruct (Pos.eqb_spec s DATA) as [->|NS].
      + (* [comment removed for export] *)
        destruct (asan_mode P && Z.leb 8 (vp_datal P)) eqn:AM; cbn [negb] in BODY; [|discriminate].
        apply andb_prop in AM as [AM AL]. apply Z.leb_le in AL.
        destruct (DSH ltac:(unfold is_data_shadow; rewrite K1; reflexivity)) as (_ & N1 & G1' & G2' & G3').
        assert (EB : rbase nu r1 = vp_shoff P + nu DATA8).
        { unfold rbase. destruct KIND as (_ & KD & _ & KB & _). rewrite KD, (KB eq_refl). reflexivity. }
        destruct (data_shadow_load_sound A nu regs mem off sg HG2 AM AL Boff G1' G2' G3') as [b [Hb RES]].
        rewrite <- EB in Hb. replace (rbase nu r1 + eval nu off) with (eval nu addr) in Hb by lia.
        subst n.
        destruct (load_machine A nu regs mem pc rom w sz sg rd rs1 imm addr _ [b] HG2 Hf He Hd Hsz Ha eq_refl
                    ltac:(rewrite N1; exact Hb)) as [wl [Hwl ST]].
        rewrite Hbe in ST. rewrite N1 in Hwl. cbn [bytes_le_to_Z] in Hwl. rewrite Z.shiftl_0_l, Z.lor_0_r in Hwl.
        destruct (data_shadow_load (v1 A) off sg) as [v A1|A0 A1 vj|m]; try discriminate; injection BODY as <-.
        * eapply finish2_post; eauto. rewrite Hwl. exact RES.
        * destruct RES as [RES|RES].
          -- eapply step_post2_mono; [eapply finish2_post; eauto; rewrite Hwl; exact RES|]. intros x [<-|[]]. left; reflexivity.
          -- eapply step_post2_mono; [eapply finish2_post; eauto; rewrite Hwl; exact RES|]. intros x [<-|[]]. right; left; reflexivity.
      + (* [comment removed for export] *)
        destruct (Z.eqb_spec n 1) as [N1|]; cbn [negb] in BODY; [|discriminate].
        destruct (NDS ltac:(unfold is_data_shadow; rewrite K1; destruct (Pos.eqb_spec s DATA); [congruence|reflexivity])) as (R1 & R2 & R3 & _).
        assert (SH : is_shadow r1 = true) by (unfold is_shadow; rewrite K1; reflexivity).
        assert (ND : is_data_shadow r1 = false).
        { unfold is_data_shadow; rewrite K1. destruct (Pos.eqb_spec s DATA); [congruence|reflexivity]. }
        destruct (Z.eqb_spec lo hi) as [Elh|Nlh].
        * destruct (sh_cover (vr_cells r1) lo) as [c|] eqn:SC; [|discriminate].
          assert (Elo : eval nu off = lo) by (ltac2:(LK.k [@Erd; @Hrd; @NDS; @KIND; @NS; @R1; @ND; @Elh]); lia).
          destruct (sh_load_sound A nu regs mem r1 lo sg c HG2 Hr SH ND ltac:((ltac2:(LK.k [@Erd; @Hrd; @NDS; @KIND; @NS; @N1; @R2; @R3; @ND; @Elo]); lia)) SC) as [b [Hb RES]].
          destruct (sh_load (v1 A) r1 lo sg) as [v A1] eqn:SL. injection BODY as <-.
          subst n.
          destruct (load_machine A nu regs mem pc rom w sz sg rd rs1 imm addr _ [b] HG2 Hf He Hd Hsz Ha eq_refl
                      ltac:(rewrite N1, Eaddr, Elo; exact Hb)) as [wl [Hwl ST]].
          rewrite Hbe in ST. rewrite N1 in Hwl. cbn [bytes_le_to_Z] in Hwl. rewrite Z.shiftl_0_l, Z.lor_0_r in Hwl.
          eapply finish2_post; eauto. rewrite Hwl. exact RES.
        * (* [comment removed for export] *)
          destruct (sh_uniform (vr_cells r1) lo hi) as [bu|] eqn:UNI.
          { injection BODY as <-. subst n.
            destruct (sh_uniform_sound A nu regs mem r1 lo hi (eval nu off) bu HG2 Hr SH ND ltac:((ltac2:(LK.k [@Erd; @Hrd; @NDS; @KIND; @NS; @N1; @R3; @ND]); lia)) ltac:((ltac2:(LK.k [@Erd; @Hrd; @NDS; @KIND; @NS; @N1; @R3; @ND]); lia)) UNI) as (kb & Hkb & Hkv).
            destruct (load_machine A nu regs mem pc rom w sz sg rd rs1 imm addr _ [kb] HG2 Hf He Hd Hsz Ha eq_refl
                        ltac:(rewrite N1, Eaddr; exact Hkb)) as [wl [Hwl ST]].
            rewrite Hbe in ST. rewrite N1 in Hwl. cbn [bytes_le_to_Z] in Hwl. rewrite Z.shiftl_0_l, Z.lor_0_r in Hwl.
            eapply (finish2_post A nu regs mem pc rom rd wl _ (v1 A)); eauto.
            pose proof (bv_unsigned_in_range 8 kb) as Rb. unfold bv_modulus in Rb. simpl in Rb.
            apply res_word_same; [exact HL| |apply lin_below_lconst].
            rewrite Hwl, eval_lconst, ldval_sign_adjust by (simpl; (ltac2:(LK.k [@NDS; @KIND; @NS; @ND; @Rb; @Erd; @Hrd]); lia)). rewrite Hkv. reflexivity. }
          (* [comment removed for export] *)
          destruct (lin_single off) as [[q k]|] eqn:LS; [|discriminate].
          destruct k as [|p|p]; try discriminate. destruct p; try discriminate.
          destruct (Pos.leb q LAST_FIXED2 || Z.ltb 15 (hi - lo)) eqn:W; [discriminate|].
          destruct (shfork_states A r1 q (lc off) sg (rz rd) (lo - lc off) (S (Z.to_nat (hi - lo)))) as [l|] eqn:SF; [|discriminate].
          injection BODY as <-.
          pose proof (eval_single nu off q 1 LS) as Eo.
          pose proof (fork_skip_actual (v1 A) nu q HL) as NSK.
          destruct (shfork_states_cover A r1 q (lc off) sg (rz rd) _ _ _ (nu q) SF ltac:((ltac2:(LK.k [@Erd; @Hrd; @NDS; @KIND; @NS; @R1; @ND; @Nlh; @Eo]); lia)) NSK) as (kk & ww & e & SC & EC).
          pose proof (shfork_states_in A r1 q (lc off) sg (rz rd) _ _ _ (nu q) kk ww e SF ltac:((ltac2:(LK.k [@Erd; @Hrd; @NDS; @KIND; @NS; @R1; @ND; @Nlh; @Eo]); lia)) NSK SC EC) as IN.
          replace (lc off + nu q) with (eval nu off) in SC by (ltac2:(LK.k [@Erd; @Hrd; @NDS; @KIND; @NS; @ND; @Eo]); lia).
          destruct (sh_load_sound A nu regs mem r1 (eval nu off) sg _ HG2 Hr SH ND ltac:((ltac2:(LK.k [@Erd; @Hrd; @NDS; @KIND; @NS; @N1; @R3; @ND]); lia)) SC) as [b [Hb RES]].
          unfold sh_load in RES. rewrite SC, EC in RES.
          subst n.
          destruct (load_machine A nu regs mem pc rom w sz sg rd rs1 imm addr _ [b] HG2 Hf He Hd Hsz Ha eq_refl
                      ltac:(rewrite N1, Eaddr; exact Hb)) as [wl [Hwl ST]].
          rewrite Hbe in ST. rewrite N1 in Hwl. cbn [bytes_le_to_Z] in Hwl. rewrite Z.shiftl_0_l, Z.lor_0_r in Hwl.
          eapply step_post2_mono.
          { eapply (point_box_post A nu regs mem pc rom rd q wl); [exact HG2|exact Hpc|exact Hrd| | |exact ST].
            -- apply (proj1 (lin_below_iff off (vs_next (v1 A))) Boff). unfold lsyms.
               unfold lin_single in LS. destruct (lt off) as [|sk [|]]; try discriminate. injection LS as ->. left; reflexivity.
            -- destruct RES as [nu1 (X1 & L1 & E1' & _)]. rewrite Hwl, E1', eval_lconst. reflexivity. }
          intros x Hx. destruct Hx as [<-|[]]. exact IN.
    - (* [comment removed for export] *)
      destruct (NDS ltac:(unfold is_data_shadow; rewrite K1; reflexivity)) as (R1 & R2 & R3 & _).
      destruct (load_cells_sound A nu regs mem r1 off lo hi n sg HG2 Hr ltac:(unfold is_shadow; rewrite K1; reflexivity)
                  Hn R1 R2 R3) as [bs [Hbs RW]].
      destruct (load_cells (v1 A) (vr_cells r1) off lo hi n sg) as [v A1] eqn:LC. injection BODY as <-.
      destruct (load_machine A nu regs mem pc rom w sz sg rd rs1 imm addr _ bs HG2 Hf He Hd Hsz Ha Eaddr Hbs) as [wl [Hwl ST]].
      rewrite Hbe in ST. eapply finish2_post; eauto. rewrite Hwl. exact RW.
  Qed.
End B.
