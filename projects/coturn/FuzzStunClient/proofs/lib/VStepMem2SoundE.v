(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import SeqExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VWord VWord2 VLinalg VState VLogic VGamma VAbs VAbsSound VAbsSound2 VAbsSound3 VStep VStepMem VStepSound VStepMemSound VStepMemSound2 VState2 VStepMem2 VGamma2 VStepMem2SoundA VStepMem2SoundB VStepMem2SoundC VStepMem2SoundD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma terms_divm_eval nu l m :
  eval_terms nu (terms_divm l m) = fold_right (fun sk acc => (snd sk / m) * nu (fst sk) + acc) 0 l.
Proof.
  induction l as [|[s c] t IH]; cbn [terms_divm fold_right fst snd]; [reflexivity|].
  destruct (Z.eqb_spec (c / m) 0) as [Z0|NZ]; cbn [eval_terms]; rewrite IH; [rewrite Z0; lia|reflexivity].
Qed.

Lemma terms_divm_syms l m s : In s (map fst (terms_divm l m)) -> In s (map fst l).
Proof.
  induction l as [|[s' c] t IH]; cbn [terms_divm]; [tauto|].
  destruct (Z.eqb (c / m) 0); cbn [map fst]; intros H; [right; exact (IH H)|].
  destruct H as [<-|H]; [now left|right; exact (IH H)].
Qed.

Lemma lin_below_lnorm b : forall l c, (forall s, In s (map fst l) -> (s < b)%positive) -> lin_below (lnorm c l) b = true.
Proof.
  unfold lnorm. intros l c.
  assert (GEN : forall acc, lin_below acc b = true -> (forall s, In s (map fst l) -> (s < b)%positive) ->
                 lin_below (fold_left (fun acc sk => ladd acc (lterm (snd sk) (fst sk))) l acc) b = true).
  { induction l as [|[s k] t IH]; intros acc Hacc Hl; cbn [fold_left]; [exact Hacc|].
    apply IH; [|intros s' Hs'; apply Hl; right; exact Hs'].
    apply lin_below_ladd; [exact Hacc|]. apply lin_below_lterm. apply Hl. left; reflexivity. }
  intros Hl. apply GEN; [apply lin_below_lconst|exact Hl].
Qed.

(* [comment removed for export] *)
Lemma rgn_upd_replaced l r x :
  List.NoDup (map vr_base l) -> In (vr_base r) (map vr_base l) ->
  In x (rgn_upd l r) -> vr_base x = vr_base r -> x = r.
Proof.
  induction l as [|y t IH]; cbn [rgn_upd map]; [intros _ [] |].
  intros ND Hin Hx Bx. apply List.NoDup_cons_iff in ND as [Hy Ht].
  destruct (Pos.eqb_spec (vr_base y) (vr_base r)) as [EY|NY].
  - destruct Hx as [<-|Hx]; [reflexivity|]. exfalso. apply Hy. rewrite EY, <- Bx. apply in_map. exact Hx.
  - destruct Hx as [<-|Hx]; [congruence|]. apply IH; auto. destruct Hin as [H|H]; [congruence|exact H].
Qed.

Section E.
  Variable SEGS : list Segment.
  Variable P : vparams2.
  Variable E : venv2.
  Variable mem0 : word -> option byte.
  Let P1 := p1 P.
  Let E1 := ev1 E.
  Hypothesis PO2 : params_ok2 SEGS P.

  Notation gamma2P := (gamma2 SEGS P E mem0).

  (* [comment removed for export] *)
  #[using="Type"] Lemma split_sound A1 nu m e qa r :
    lgamma A1 nu -> 0 < m -> split A1 m e = Some (qa, r) ->
    eval nu qa = eval nu e / m /\ eval nu r = eval nu e mod m.
  Proof.
    intros HL Hm SP. unfold split in SP.
    set (q0 := lnorm 0 (terms_divm (lt e) m)) in SP.
    destruct (lin_is_const q0); [discriminate|].
    set (R := anorm A1 (lsub e (lscale m q0))) in SP.
    pose proof (lp_bounds_sound nu (vs_store A1) (proj1 HL) R) as HB.
    destruct (lp_bounds (vs_store A1) R) as [[lo|] [hi|]]; try discriminate.
    destruct (Z.eqb_spec (lo / m) (hi / m)) as [EJ|]; [|discriminate]. injection SP as <- <-.
    destruct HB as [HB1 HB2]. cbn [fst snd lo_le hi_ge] in HB1, HB2.
    assert (ER : eval nu R = eval nu e - m * eval nu q0).
    { unfold R. rewrite (anorm_sound _ _ _ HL), eval_lsub, eval_lscale. lia. }
    set (j := lo / m) in *. set (Q := eval nu q0) in *. set (X := eval nu e) in *.
    (* [comment removed for export] *)
    pose proof (Z.div_mod lo m ltac:(lia)) as D1. pose proof (Z.mod_pos_bound lo m Hm) as M1.
    pose proof (Z.div_mod hi m ltac:(lia)) as D2. pose proof (Z.mod_pos_bound hi m Hm) as M2.
    fold j in D1. rewrite <- EJ in D2.
    assert (RB : j * m <= eval nu R < (j + 1) * m) by lia.
    assert (XE : X = m * (Q + j) + (eval nu R - j * m)) by lia.
    assert (QE : Q + j = X / m) by (apply (Z.div_unique_pos X m (Q + j) (eval nu R - j * m)); lia).
    assert (ME : eval nu R - j * m = X mod m) by (apply (Z.mod_unique_pos X m (Q + j) (eval nu R - j * m)); lia).
    rewrite !(anorm_sound _ _ _ HL), !eval_laddc. fold Q. split; (ltac2:(LK.k [@Hm; @M1; @M2; @QE; @ME]); lia).
  Qed.

  Lemma split_below A1 m e qa r b :
    lin_below e b = true -> split A1 m e = Some (qa, r) -> lin_below qa b = true /\ lin_below r b = true.
  Proof.
    intros Hb SP. unfold split in SP.
    set (q0 := lnorm 0 (terms_divm (lt e) m)) in SP.
    destruct (lin_is_const q0); [discriminate|].
    destruct (lp_bounds (vs_store A1) (anorm A1 (lsub e (lscale m q0)))) as [[lo|] [hi|]]; try discriminate.
    destruct (Z.eqb (lo / m) (hi / m)); [|discriminate]. injection SP as <- <-.
    assert (B0 : lin_below q0 b = true).
    { unfold q0. apply lin_below_lnorm. intros s Hs. apply terms_divm_syms in Hs. exact (proj1 (lin_below_iff _ _) Hb s Hs). }
    split; apply anorm_below, lin_below_laddc; [exact B0|].
    apply anorm_below, lin_below_lsub; [exact Hb|apply lin_below_lscale; exact B0].
  Qed.

  (* [comment removed for export] *)
  Theorem x_srl_split_sound : XSPLIT_stmt SEGS P E mem0.
  Proof.
    intros A nu regs mem pc rom w rd rs1 sh r HG2 Hpc Hf He Hd Hrd HX succs ->.
    pose proof HG2 as (G1 & HE2 & HMC2 & FIX2 & DIV & RGN & LIVE & BEL2 & GL & FI2 & MEM2).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof (gamma_get_reg SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem rs1 G1) as [Wa Ba].
    assert (Hbe : bv_eqb rd 0%bv = false) by (rewrite bv_eqb_rz; destruct (Z.eqb_spec (rz rd) 0); [contradiction|reflexivity]).
    pose proof (bv_unsigned_in_range 6 sh) as Hsh. unfold bv_modulus in Hsh. simpl in Hsh.
    unfold x_srl_split, get_reg2 in HX.
    destruct (get_reg (v1 A) (rz rs1)) as [ea|] eqn:Hea; [|discriminate].
    pose proof (wval_some _ _ _ Wa) as Ua. cbn [vbelow] in Ba.
    set (k := bv_unsigned sh) in *.
    destruct (lin_is_const ea || Z.leb k 0 || Z.leb 64 k) eqn:C; [discriminate|].
    apply orb_false_iff in C as [C K2]. apply orb_false_iff in C as [_ K1]. apply Z.leb_gt in K1. apply Z.leb_gt in K2.
    pose proof (pow2_pos k ltac:(lia)) as Pk.
    destruct (if inU (v1 A) ea then split (v1 A) (2 ^ k) ea else None) as [[q rr]|] eqn:S4.
    - (* [comment removed for export] *)
      destruct (inU (v1 A) ea) eqn:IU; [|discriminate].
      pose proof (inU_sound _ _ _ HL IU) as EU.
      destruct (split_sound (v1 A) nu (2 ^ k) ea q rr HL Pk S4) as [Eq _].
      destruct (split_below (v1 A) (2 ^ k) ea q rr _ Ba S4) as [Bq _].
      injection HX as <-. rewrite finish2_eq.
      eapply (value_post2 SEGS P E mem0 PO2 A nu regs mem pc rom rd _ q (v1 A) (vs_divdef A) nu HG2 Hpc Hrd (aext_refl _ _) HL);
        [|exact Bq|apply dd_ext_refl|eapply step_srli_at; eauto].
      unfold v_srli. rewrite u_Z_to_bv64. f_equal. fold k.
      rewrite Z.shiftr_div_pow2 by lia. rewrite Eq, Ua, (zwrap_id 64 (eval nu ea)) by lia. reflexivity.
    - (* [comment removed for export] *)
      destruct (ldivisible ea (2 ^ k)) eqn:LD; cbn [negb] in HX; [|discriminate].
      set (q := lshiftr ea k) in HX.
      destruct (lin_is_const q); [discriminate|].
      destruct (itv_empty (lp_bounds (vs_store (v1 A)) q)); [discriminate|].
      destruct (match lp_bounds (vs_store (v1 A)) q with
                | (Some lo, Some hi) => (fdiv lo (2 ^ (64 - k)) =? fdiv hi (2 ^ (64 - k)))
                | _ => false end); [discriminate|].
      destruct (split (v1 A) (2 ^ (64 - k)) q) as [[qq r']|] eqn:S5; [|discriminate].
      injection HX as <-. rewrite finish2_eq.
      pose proof (pow2_pos (64 - k) ltac:(lia)) as Pk'.
      assert (Bq : lin_below q (vs_next (v1 A)) = true) by (unfold q; apply lin_below_lshiftr; exact Ba).
      destruct (split_sound (v1 A) nu (2 ^ (64 - k)) q qq r' HL Pk' S5) as [_ Er].
      destruct (split_below (v1 A) (2 ^ (64 - k)) q qq r' _ Bq S5) as [_ Br].
      pose proof (lshiftr_eval nu ea k ltac:(lia) LD) as EQ. fold q in EQ.
      eapply (value_post2 SEGS P E mem0 PO2 A nu regs mem pc rom rd _ r' (v1 A) (vs_divdef A) nu HG2 Hpc Hrd (aext_refl _ _) HL);
        [|exact Br|apply dd_ext_refl|eapply step_srli_at; eauto].
      unfold v_srli. rewrite u_Z_to_bv64. f_equal. fold k.
      rewrite Z.shiftr_div_pow2 by lia. rewrite Er, EQ, Ua, shiftr_zwrap64 by lia. unfold zwrap. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma gamma2_rgn_cells A A1' nu nu' regs regs' mem r m' :
    gamma2P A nu regs mem -> In r (vs_rgn A) -> is_data_shadow r = false ->
    match vr_kind r with RK_flag _ => False | _ => True end ->
    ext (vs_next (v1 A)) nu nu' -> (vs_next (v1 A) <= vs_next A1')%positive ->
    gamma SEGS P1 E1 (zpatch P E mem0 mem) A1' nu' regs' mem ->
    vs_globs A1' = vs_globs (v1 A) ->
    (forall off w v, In (off, (w, v)) m' ->
        vr_lo r <= off /\ 0 < w /\ off + w <= vr_hi r /\ rcell_holds SEGS (is_shadow r) nu' mem (rbase nu' r + off) w v
        /\ (forall e, v = Some e -> lin_below e (vs_next A1') = true)) ->
    gamma2P (mkVS2 A1' (rgn_upd (vs_rgn A) (set_cells r m')) (vs_live A) (vs_divdef A) (vs_memo A)) nu' regs' mem.
  Proof.
    intros HG2 Hr ND KNF X LE G1' EG HM'.
    pose proof HG2 as (G1 & HE2 & HMC2 & FIX2 & DIV & RGN & LIVE & BEL2 & GL & FI2 & MEM2).
    assert (GB : gamma2P (with_v1 A A1') nu' regs' mem).
    { eapply (gamma2_transfer SEGS P E mem0 PO2); eauto; [apply frame_mod_refl|].
      unfold globs_ok2. cbn [v1 with_v1]. rewrite EG. exact GL. }
    pose proof GB as (_ & _ & _ & FIXB & DIVB & RGNB & LIVEB & BELB & GLB & FIB & MEMB).
    set (l2 := rgn_upd (vs_rgn A) (set_cells r m')).
    pose proof LIVE as (_ & _ & _ & ND0).
    assert (INB : In (vr_base (set_cells r m')) (map vr_base (vs_rgn A))) by (apply in_map_iff; exists r; auto).
    assert (SM : shape_map (vs_rgn A) l2).
    { unfold l2. apply rgn_upd_shape; [|exact INB].
      intros x Hx Bx. cbn [set_cells vr_base] in Bx.
      assert (x = r) as -> by (apply (nodup_map_inj vr_base _ _ _ ND0 Hx Hr); exact Bx). apply rshape_set_cells. }
    assert (GET : forall s ro, rgn_get (vs_rgn (with_v1 A A1')) s = Some ro ->
                  exists ro', rgn_get l2 s = Some ro' /\ rshape ro ro').
    { intros s ro G. cbn [vs_rgn with_v1] in G. exact (shape_map_get _ _ _ _ SM G). }
    assert (REG : forall r', In r' l2 ->
              region_ok SEGS P E nu' (mkVS2 A1' l2 (vs_live A) (vs_divdef A) (vs_memo A)) mem r'
              /\ cells_syms_below (vr_cells r') (vs_next A1')).
    { intros r' Hr'. destruct (shape_map_in_back _ _ _ SM Hr') as (r0 & Hr0 & SH).
      pose proof (RGNB r0 Hr0) as R0. pose proof R0 as (_ & _ & _ & DS0 & CELLS0 & _ & NUL0 & KO0).
      destruct BELB as (_ & BRB & _). destruct (BRB r0 Hr0) as (_ & CB0 & _). cbn [v1 with_v1] in CB0.
      assert (LV' : match vr_kind r0 with RK_fake _ _ => In (vr_base r0) (vs_live A) | _ => True end).
      { unfold kind_ok in KO0. destruct (vr_kind r0); auto. destruct KO0 as (_ & _ & _ & _ & _ & pos & _ & _ & _ & _ & _ & LV). exact LV. }
      destruct (Pos.eq_dec (vr_base r') (vr_base r)) as [EB|NB].
      - (* [comment removed for export] *)
        assert (r' = set_cells r m') as -> by (apply (rgn_upd_replaced (vs_rgn A) (set_cells r m') r' ND0 INB Hr'); exact EB).
        assert (r0 = r) as ->.
        { apply (nodup_map_inj vr_base _ _ _ ND0 Hr0 Hr). destruct SH as (SB & _). cbn [set_cells vr_base] in SB. symmetry. exact SB. }
        split.
        + apply (region_ok_self SEGS P E (with_v1 A A1') _ nu' mem mem r (set_cells r m') HE2 R0 (rshape_set_cells r m') ND (mem_grows_refl _)).
          * destruct (vr_kind r); auto.
          * intros s ro G _ _. exact (GET s ro G).
          * exact LV'.
          * destruct (vr_kind r); auto. destruct KNF.
          * intros off w v Hin. cbn [set_cells vr_cells] in Hin. destruct (HM' _ _ _ Hin) as (Y1 & Y2 & Y3 & Y4 & _). auto.
          * intros lo hi Hin. cbn [set_cells vr_nul] in Hin. exact (NUL0 lo hi Hin).
        + intros off w e Hin. cbn [set_cells vr_cells] in Hin. destruct (HM' _ _ _ Hin) as (_ & _ & _ & _ & Y5). exact (Y5 e eq_refl).
      - (* [comment removed for export] *)
        assert (r' = r0) as ->.
        { unfold l2 in Hr'. apply rgn_upd_in in Hr' as [->|Hr'].
          - exfalso. apply NB. reflexivity.
          - apply (nodup_map_inj vr_base _ _ _ ND0 Hr' Hr0). destruct SH as (SB & _). exact SB. }
        split; [|exact CB0].
        destruct (is_data_shadow r0) eqn:D0.
        + (* [comment removed for export] *)
          pose proof R0 as (B1 & B2 & B3 & DS & CELLS & PERM & NUL & KIND).
          split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact DS|]. split; [exact CELLS|].
          split; [exact PERM|]. split; [exact NUL|].
          unfold kind_ok in KIND |- *. unfold is_data_shadow in D0.
          destruct (vr_kind r0) as [| | |sb|]; try discriminate. apply Pos.eqb_eq in D0. subst sb.
          destruct KIND as (F1 & F2 & F3 & F4 & F5 & F6). split; [exact F1|]. split; [exact F2|]. split; [exact F3|].
          split; [exact F4|]. split; [exact F5|]. intros N1 N2. exfalso. exact (N2 eq_refl).
        + apply (region_ok_self SEGS P E (with_v1 A A1') _ nu' mem mem r0 r0 HE2 R0 (rshape_refl r0) D0 (mem_grows_refl _)).
          * destruct (vr_kind r0); auto.
          * intros s ro G _ _. exact (GET s ro G).
          * exact LV'.
          * unfold kind_ok in KO0. destruct (vr_kind r0); auto. destruct KO0 as (_ & _ & _ & C0 & _). exact C0.
          * exact CELLS0.
          * exact NUL0. }
    split; [exact (proj1 GB)|]. split; [exact HE2|]. split; [exact (proj1 (proj2 (proj2 GB)))|]. split; [exact FIXB|]. split; [exact DIVB|].
    split; [intros r' Hr'; exact (proj1 (REG r' Hr'))|].
    split; [exact (live_ok_shape A A1' l2 nu' (vs_divdef A) (vs_memo A) LIVEB SM)|].
    split.
    { (* [comment removed for export] *)
      destruct BELB as (BF & BR & BL & BD & BM). cbn [v1 vs_rgn vs_live vs_divdef vs_memo with_v1] in BF, BR, BL, BD, BM |- *.
      split; [exact BF|]. split; [|split; [exact BL|split; [exact BD|exact BM]]].
      intros r' Hr'. destruct (shape_map_in_back _ _ _ SM Hr') as (r0 & Hr0 & SH). destruct SH as (SB & _ & SK & _).
      destruct (BR r0 Hr0) as (Y1 & Y2 & Y3). rewrite SB, SK. split; [exact Y1|]. split; [exact (proj2 (REG r' Hr'))|exact Y3]. }
    split; [unfold globs_ok2 in GLB |- *; cbn [v1 with_v1] in GLB |- *; exact GLB|].
    split; [|exact MEMB].
    intros Hfs c p Hc Hp NL NO. apply (FIB Hfs c p Hc Hp NL). change (own_flags (with_v1 A A1') nu') with (own_flags A nu').
    rewrite <- (own_flags_shape A A1' l2 nu' (vs_live A) (vs_divdef A) (vs_memo A) SM). exact NO.
  Qed.

  (* [comment removed for export] *)
  Lemma region_cells_ext A nu nu' regs mem r :
    gamma2P A nu regs mem -> In r (vs_rgn A) -> ext (vs_next (v1 A)) nu nu' ->
    forall off w v, In (off, (w, v)) (vr_cells r) ->
      vr_lo r <= off /\ 0 < w /\ off + w <= vr_hi r /\ rcell_holds SEGS (is_shadow r) nu' mem (rbase nu' r + off) w v.
  Proof.
    intros HG2 Hr X off w v Hin.
    pose proof HG2 as (_ & _ & _ & _ & _ & RGN & _ & BEL2 & _).
    destruct (RGN r Hr) as (_ & _ & _ & _ & CELLS & _). destruct (CELLS _ _ _ Hin) as (L1 & L2 & L3 & RC).
    destruct BEL2 as (_ & BR & _). destruct (BR r Hr) as (Bb & Bc & _).
    assert (RB : rbase nu' r = rbase nu r) by (unfold rbase; rewrite X by exact Bb; reflexivity). rewrite RB.
    split; [exact L1|]. split; [exact L2|]. split; [exact L3|].
    unfold rcell_holds in RC |- *. destruct v as [e|]; [|exact I].
    destruct (is_shadow r && lin_is_const e); [exact RC|].
    unfold cell_holds in RC |- *. rewrite (eval_ext_below _ _ _ _ X (Bc _ _ _ Hin)). exact RC.
  Qed.

  (* [comment removed for export] *)
  Theorem x_install_rgn_sound : XINSTALL_stmt SEGS P E mem0.
  Proof.
    intros A nu regs mem pc rom w sz sg rd rs1 imm addr r off lo hi v A3 m' HG2 Hpc Hf He Hd Hrd Ha CL KFA IOK INS GLB.
    pose proof HG2 as (G1 & HE2 & HMC2 & FIX2 & DIV & RGN & LIVE & BEL2 & GL & FI2 & MEM2).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    set (n := msize_z sz) in *.
    assert (Hn : 0 < n <= 8) by (unfold n; destruct sz; simpl; lia).
    assert (Hsz : sz = SZ8 -> sg = true).
    { intros ->. unfold install_ok in IOK. apply andb_prop in IOK as [IOK _]. apply andb_prop in IOK as [_ N8].
      apply Z.ltb_lt in N8. unfold n in N8. simpl in N8. lia. }
    assert (Hbe : bv_eqb rd 0%bv = false) by (rewrite bv_eqb_rz; destruct (Z.eqb_spec (rz rd) 0); [contradiction|reflexivity]).
    destruct (addr_of_sound SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem rs1 (bv_signed imm) addr G1 Ha) as [Baddr Hva].
    destruct (classify2_rgn A addr n false r off lo hi CL) as (B & r1 & HB & HC & HR1 & HCL).
    destruct (classify_rgn_sound A nu r1 addr n false r off lo hi HL ltac:(lia) HCL) as (-> & Eoff & Eaddr & NDS & DSH).
    pose proof (rgn_in _ _ _ HR1) as Hr.
    assert (ND : is_data_shadow r1 = false) by (unfold is_data_shadow; destruct (vr_kind r1); auto; destruct KFA).
    assert (NS : is_shadow r1 = false) by (unfold is_shadow; destruct (vr_kind r1); auto; destruct KFA).
    assert (KNF : match vr_kind r1 with RK_flag _ => False | _ => True end) by (destruct (vr_kind r1); auto).
    destruct (NDS ND) as (R1 & R2 & R3 & _).
    unfold install_ok in IOK. apply andb_prop in IOK as [IOK NOV]. apply andb_prop in IOK as [LH N8]. apply Z.eqb_eq in LH. apply Z.ltb_lt in N8. subst hi.
    assert (Elo : eval nu off = lo) by lia.
    (* [comment removed for export] *)
    destruct (region_bytes SEGS P E mem0 A nu regs mem r1 lo (Z.to_nat n) HG2 Hr ND ltac:(lia) ltac:(rewrite Z2Nat.id; lia)) as (bs & Hbs & Hlen).
    set (X := bytes_le_to_Z bs).
    pose proof (bytes_le_to_Z_bound bs) as XB. pose proof (bytes_le_to_Z_nonneg bs) as X0. rewrite Hlen, Z2Nat.id in XB by lia. fold X in XB, X0.
    (* [comment removed for export] *)
    unfold load_install in INS.
    pose proof (afresh_sound (v1 A) nu (urange n) X HL ltac:(unfold urange; split; cbn [fst snd lo_le hi_ge]; lia)) as AF.
    destruct (afresh (v1 A) (urange n)) as [[u|] A2]; [|discriminate].
    destruct AF as (nu1 & X1 & HL1 & Eu & Bu).
    pose proof (areinterp_sound A2 nu1 u n sg X HL1 Hn Bu ltac:(rewrite Eu; symmetry; apply zwrap_id; lia)) as AR.
    destruct (areinterp A2 u n sg) as [v' A3'] eqn:ARE. injection INS as -> -> EM'. subst m'.
    destruct AR as (nu2 & X2 & HL2 & DEN).
    pose proof (aext_trans _ _ _ _ _ _ X1 X2) as X02. pose proof X02 as (X02e & X02le & SH02).
    (* [comment removed for export] *)
    destruct (load_machine SEGS P E mem0 A nu regs mem pc rom w sz sg rd rs1 imm addr (rbase nu r1 + lo) bs HG2 Hf He Hd Hsz Ha
                ltac:(rewrite Eaddr, Elo; reflexivity) Hbs) as [wl [Hwl ST]].
    rewrite Hbe in ST.
    set (l2 := rgn_upd (vs_rgn A) (set_cells r1 (cm_set (vr_cells r1) lo (n, Some u)))).
    assert (EQA : finish2 (with_v1 (set_rgn A l2) A3) (rz rd) v = mkVS2 (finish A3 (rz rd) v) l2 (vs_live A) (vs_divdef A) (vs_memo A)) by reflexivity.
    rewrite EQA. clear EQA.
    exists (regupd regs rd wl), (v_addi pc 4), mem, (mkVS2 (finish A3 (rz rd) v) l2 (vs_live A) (vs_divdef A) (vs_memo A)), nu2.
    split; [exact ST|]. split; [left; reflexivity|].
    assert (SHP : vs_pc A3 = vs_pc (v1 A)) by (destruct SH02 as (_ & _ & _ & _ & SP & _); exact SP).
    split.
    { unfold vs2_pc, finish. cbn [v1]. unfold npc_of, v_addi. rewrite u_Z_to_bv64, wrap64_zwrap.
      unfold set_reg. destruct (Z.eqb (rz rd) 0); cbn [vs_pc set_pc]; rewrite SHP; unfold vs2_pc in Hpc; rewrite Hpc; reflexivity. }
    split; [exact X02e|]. split.
    { unfold vs2_next, finish. cbn [v1]. unfold set_reg. destruct (Z.eqb (rz rd) 0); cbn; exact X02le. }
    split; [apply frame_mod_refl|].
    pose proof LIVE as (_ & _ & _ & ND0).
    assert (SM : shape_map (vs_rgn A) l2).
    { unfold l2. apply rgn_upd_shape; [|apply in_map_iff; exists r1; auto].
      intros x Hx Bx. cbn [set_cells vr_base] in Bx.
      assert (x = r1) as -> by (apply (nodup_map_inj vr_base _ _ _ ND0 Hx Hr); exact Bx). apply rshape_set_cells. }
    split.
    { intros y Hy. left. split; [|reflexivity].
      rewrite (own_flags_shape A (finish A3 (rz rd) v) l2 nu2 (vs_live A) (vs_divdef A) (vs_memo A) SM).
      rewrite (own_flags_ext A nu nu2 X02e BEL2). tauto. }
    apply (gamma2_rgn_cells A (finish A3 (rz rd) v) nu nu2 regs (regupd regs rd wl) mem r1 _ HG2 Hr ND KNF X02e).
    - unfold finish, set_reg. destruct (Z.eqb (rz rd) 0); cbn; exact X02le.
    - unfold finish. eapply (gamma_upd SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) A3 nu nu2 regs mem rd wl v); eauto.
      destruct v as [e|]; [|exact I]. destruct DEN as [D1 D2]. split; [rewrite Hwl; exact D1|exact D2].
    - exact (globs_finish_aext (v1 A) A3 nu nu2 (rz rd) v X02).
    - intros off' w' v' Hin. apply cm_set_in in Hin as [Hin|Hin].
      + injection Hin as -> -> ->.
        assert (RB : rbase nu2 r1 = rbase nu r1).
        { unfold rbase. destruct BEL2 as (_ & BR & _). destruct (BR r1 Hr) as (Bb & _). rewrite X02e by exact Bb. reflexivity. }
        split; [lia|]. split; [lia|]. split; [lia|]. split.
        * unfold rcell_holds. rewrite NS. cbn [andb]. unfold cell_holds. exists bs. rewrite RB. split; [exact Hbs|].
          fold X. destruct X2 as (X2e & _). rewrite (eval_ext_below _ _ _ _ X2e Bu), Eu. symmetry. apply zwrap_id. lia.
        * intros e Hue. injection Hue as <-. unfold finish, set_reg. destruct X2 as (_ & L2 & _). destruct (Z.eqb (rz rd) 0); cbn; (eapply lin_below_mono; [exact L2|exact Bu]).
      + destruct (region_cells_ext A nu nu2 regs mem r1 HG2 Hr X02e off' w' v' Hin) as (Y1 & Y2 & Y3 & Y4).
        split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4|].
        intros e ->. destruct BEL2 as (_ & BR & _). destruct (BR r1 Hr) as (_ & Bc & _).
        unfold finish, set_reg. destruct (Z.eqb (rz rd) 0); cbn; (eapply lin_below_mono; [exact X02le|exact (Bc _ _ _ Hin)]).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma wordZ_zwrap z : wordZ (zwrap 64 z) = wordZ z.
  Proof. apply bv_eq. rewrite !u_Z_to_bv64. apply zwrap_zwrap. lia. Qed.

  Lemma memo_lookup_in A1 : forall l addr n v,
    memo_lookup A1 l addr n = Some v ->
    exists a', In (a', (n, v)) l /\ lin_is_const (anorm A1 (lsub addr a')) = true /\ lc (anorm A1 (lsub addr a')) = 0.
  Proof.
    induction l as [|[a' [n' v']] t IH]; cbn [memo_lookup]; intros addr n v H; [discriminate|].
    destruct (Z.eqb n' n && lin_is_const (anorm A1 (lsub addr a')) && Z.eqb (lc (anorm A1 (lsub addr a'))) 0) eqn:C.
    - injection H as <-. apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2]. apply Z.eqb_eq in C1. apply Z.eqb_eq in C3. subst n'.
      exists a'. split; [now left|auto].
    - destruct (IH _ _ _ H) as (a0 & Hin & X). exists a0. split; [now right|exact X].
  Qed.

  Lemma memo_push_in l e x : In x (memo_push l e) -> In x l \/ x = e.
  Proof.
    unfold memo_push. intros H.
    assert (H' : In x (l ++ [e])%list).
    { destruct (Nat.ltb 8 (Datatypes.length (l ++ [e])%list)); [|exact H]. destruct (l ++ [e])%list as [|y t]; [destruct H|right; exact H]. }
    apply in_app_iff in H' as [H'|[H'|[]]]; auto.
  Qed.

  (* [comment removed for export] *)
  Lemma gamma2_set_memo X m nu regs mem :
    gamma2P X nu regs mem ->
    (forall a n v, In (a, (n, v)) m ->
        (0 < n < 8 /\ cell_holds SEGS nu mem (zwrap 64 (eval nu a)) n (Some v))
        /\ lin_below a (vs_next (v1 X)) = true /\ lin_below v (vs_next (v1 X)) = true) ->
    gamma2P (set_memo X m) nu regs mem.
  Proof.
    intros (G1 & HE2 & HMC2 & FIX2 & DIV & RGN & LIVE & (BF & BR & BL & BD & BM) & GL & FI2 & MEM2) HM.
    split; [exact G1|]. split; [exact HE2|]. split; [exact HMC2|]. split; [exact FIX2|]. split; [exact DIV|].
    split; [exact RGN|]. split; [exact LIVE|]. split; [|split; [exact GL|split; [exact FI2|]]].
    - split; [exact BF|]. split; [exact BR|]. split; [exact BL|]. split; [exact BD|].
      intros a n v Hin. exact (proj2 (HM a n v Hin)).
    - intros a n v Hin. exact (proj1 (HM a n v Hin)).
  Qed.

  Lemma zwrap_small_of_64 k e X : 0 <= k <= 64 -> X = zwrap 64 e -> 0 <= X < 2 ^ k -> X = zwrap k e.
  Proof.
    intros Hk HX R. rewrite <- (zwrap_zwrap k 64 e) by lia. rewrite <- HX. symmetry. apply zwrap_id. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem x_load_stack_sound : XSTACK_stmt SEGS P E mem0.
  Proof.
    intros A nu regs mem pc rom w sz sg rd rs1 imm addr off lo hi succs HG2 Hpc Hf He Hd Hrd Ha Hsz CL HX GLB.
    pose proof HG2 as (G1 & HE2 & HMC2 & FIX2 & DIV & RGN & LIVE & BEL2 & GL & FI2 & MEM2).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    set (n := msize_z sz) in *.
    assert (Hn : 0 < n <= 8) by (unfold n; destruct sz; simpl; lia).
    assert (Hbe : bv_eqb rd 0%bv = false) by (rewrite bv_eqb_rz; destruct (Z.eqb_spec (rz rd) 0); [contradiction|reflexivity]).
    destruct (addr_of_sound SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem rs1 (bv_signed imm) addr G1 Ha) as [Baddr Hva].
    unfold x_load_stack in HX. change (p1 P) with P1 in HX.
    destruct (Z.ltb n 8 && negb (Z.eqb lo hi)) eqn:RNG.
    - (* [comment removed for export] *)
      apply andb_prop in RNG as [N8 _]. apply Z.ltb_lt in N8.
      destruct (memo_lookup (v1 A) (vs_memo A) addr n) as [mv|] eqn:ML.
      + (* [comment removed for export] *)
        destruct (memo_lookup_in _ _ _ _ _ ML) as (a' & Hin & C1 & C2).
        assert (EA : eval nu addr = eval nu a').
        { pose proof (anorm_sound _ nu (lsub addr a') HL) as EN. rewrite (eval_is_const nu _ C1), C2, eval_lsub in EN. lia. }
        destruct (MEM2 _ _ _ Hin) as [Nmv (bs & Hbs & Hval)].
        destruct BEL2 as (_ & _ & _ & _ & BM). destruct (BM _ _ _ Hin) as [_ Bmv].
        destruct (areinterp (v1 A) mv n sg) as [v' A2] eqn:ARE. injection HX as <-.
        pose proof (areinterp_sound (v1 A) nu mv n sg (bytes_le_to_Z bs) HL Hn Bmv Hval) as RW. rewrite ARE in RW.
        rewrite <- EA, wordZ_zwrap in Hbs.
        destruct (load_machine SEGS P E mem0 A nu regs mem pc rom w sz sg rd rs1 imm addr (eval nu addr) bs HG2 Hf He Hd Hsz Ha eq_refl Hbs) as [wl [Hwl ST]].
        rewrite Hbe in ST. eapply (finish2_post SEGS P E mem0 PO2); eauto. rewrite Hwl. exact RW.
      + (* [comment removed for export] *)
        destruct (load_val_sound SEGS P1 E1 (zpatch P E mem0 mem) (PO1 _ _ PO2) (v1 A) nu regs mem (RStack off lo hi) addr n false G1 Hn Baddr CL)
          as (bs & Hbs & RW).
        rewrite wordZ_zwrap in Hbs.
        destruct (load_val P1 (v1 A) (RStack off lo hi) addr n false) as [v A2] eqn:LV.
        destruct RW as (nu1 & X1 & HL1 & DEN1).
        pose proof (rdn_length _ _ _ _ _ Hbs) as Hlen.
        set (X := bytes_le_to_Z bs) in *.
        pose proof (bytes_le_to_Z_bound bs) as XB. pose proof (bytes_le_to_Z_nonneg bs) as X0. rewrite Hlen, Z2Nat.id in XB by lia. fold X in XB, X0.
        destruct (load_machine SEGS P E mem0 A nu regs mem pc rom w sz sg rd rs1 imm addr (eval nu addr) bs HG2 Hf He Hd Hsz Ha eq_refl Hbs) as [wl [Hwl ST]].
        rewrite Hbe in ST.
        destruct v as [ve|].
        * destruct DEN1 as [DX Bve]. unfold ldval in DX. cbn [andb] in DX.
          assert (DX' : X = zwrap (8 * n) (eval nu1 ve)) by (apply zwrap_small_of_64; lia).
          pose proof (areinterp_sound A2 nu1 ve n sg X HL1 Hn Bve DX') as RW2.
          destruct (areinterp A2 ve n sg) as [v' A3] eqn:ARE. injection HX as <-.
          destruct RW2 as (nu2 & X2 & HL2 & DEN2).
          pose proof (aext_trans _ _ _ _ _ _ X1 X2) as X02. pose proof X02 as (X02e & X02le & SH02).
          set (memo' := memo_push (vs_memo A) (addr, (n, ve))).
          assert (EQA : finish2 (set_memo (with_v1 A A3) memo') (rz rd) v' = set_memo (with_v1 A (finish A3 (rz rd) v')) memo') by reflexivity.
          rewrite EQA. clear EQA.
          exists (regupd regs rd wl), (v_addi pc 4), mem, (set_memo (with_v1 A (finish A3 (rz rd) v')) memo'), nu2.
          split; [exact ST|]. split; [left; reflexivity|].
          assert (SHP : vs_pc A3 = vs_pc (v1 A)) by (destruct SH02 as (_ & _ & _ & _ & SP & _); exact SP).
          split.
          { unfold vs2_pc, finish. cbn [v1 set_memo with_v1]. unfold npc_of, v_addi. rewrite u_Z_to_bv64, wrap64_zwrap.
            unfold set_reg. destruct (Z.eqb (rz rd) 0); cbn [vs_pc set_pc]; rewrite SHP; unfold vs2_pc in Hpc; rewrite Hpc; reflexivity. }
          split; [exact X02e|]. split.
          { unfold vs2_next, finish. cbn [v1 set_memo with_v1]. unfold set_reg. destruct (Z.eqb (rz rd) 0); cbn; exact X02le. }
          split; [apply frame_mod_refl|]. split.
          { intros y Hy. left. split; [|reflexivity].
            change (own_flags (set_memo (with_v1 A (finish A3 (rz rd) v')) memo') nu2) with (own_flags A nu2).
            rewrite (own_flags_ext A nu nu2 X02e BEL2). tauto. }
          apply gamma2_set_memo.
          { eapply (gamma2_transfer SEGS P E mem0 PO2 A (finish A3 (rz rd) v') nu nu2 regs (regupd regs rd wl) mem mem HG2 X02e).
            - unfold finish, set_reg. destruct (Z.eqb (rz rd) 0); cbn; exact X02le.
            - apply frame_mod_refl.
            - unfold finish. eapply (gamma_upd SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) A3 nu nu2 regs mem rd wl v'); eauto.
              destruct v' as [e|]; [|exact I]. destruct DEN2 as [D1 D2]. split; [rewrite Hwl; unfold ldval in D1 |- *; exact D1|exact D2].
            - unfold globs_ok2. cbn [v1 with_v1]. rewrite (globs_finish_aext (v1 A) A3 nu nu2 (rz rd) v' X02). exact GL.
            - left; reflexivity. }
          intros ma mn mvv Hin. cbn [v1 with_v1].
          assert (NXF : (vs_next (v1 A) <= vs_next (finish A3 (rz rd) v'))%positive).
          { unfold finish, set_reg. destruct (Z.eqb (rz rd) 0); cbn; exact X02le. }
          assert (NX3 : vs_next (finish A3 (rz rd) v') = vs_next A3).
          { unfold finish, set_reg. destruct (Z.eqb (rz rd) 0); reflexivity. }
          apply memo_push_in in Hin as [Hin|Hin].
          -- destruct (MEM2 _ _ _ Hin) as [N0 CH]. destruct BEL2 as (_ & _ & _ & _ & BM). destruct (BM _ _ _ Hin) as [Ba Bv].
             split; [|split; eapply lin_below_mono; eauto].
             split; [exact N0|]. unfold cell_holds in CH |- *. rewrite (eval_ext_below _ _ _ _ X02e Ba), (eval_ext_below _ _ _ _ X02e Bv). exact CH.
          -- injection Hin as -> -> ->. split; [|split; [eapply lin_below_mono; [exact NXF|exact Baddr]|rewrite NX3; destruct X2 as (_ & L2 & _); eapply lin_below_mono; [exact L2|exact Bve]]].
             split; [lia|]. unfold cell_holds. exists bs. rewrite (eval_ext_below _ _ _ _ X02e Baddr), wordZ_zwrap. split; [exact Hbs|].
             fold X. destruct X2 as (X2e & _). rewrite (eval_ext_below _ _ _ _ X2e Bve). exact DX'.
        * (* [comment removed for export] *)
          injection HX as <-. eapply (finish2_post SEGS P E mem0 PO2); eauto. exists nu1. split; [exact X1|]. split; [exact HL1|exact I].
    - (* [comment removed for export] *)
      destruct (if install_ok (vs_slots (v1 A)) lo hi n then load_install (v1 A) (vs_slots (v1 A)) lo n sg else None)
        as [[[v A3] m']|] eqn:INS.
      + (* [comment removed for export] *)
        destruct (install_ok (vs_slots (v1 A)) lo hi n) eqn:IOK; [|discriminate].
        unfold install_ok in IOK. apply andb_prop in IOK as [IOK NOV]. apply andb_prop in IOK as [LH N8]. apply Z.eqb_eq in LH. apply Z.ltb_lt in N8. subst hi.
        destruct (classify_stack_sound P1 E1 (v1 A) nu addr n false off lo lo HL (proj1 (proj2 (proj2 G1))) ltac:(lia) CL)
          as (Eoff & Eaddr & Hlohi & Flo & Fhi & _).
        assert (Elo : eval nu off = lo) by lia.
        pose proof G1 as (HE1 & HM1 & _).
        destruct (frame_bytes SEGS P1 E1 (zpatch P E mem0 mem) (PO1 _ _ PO2) mem (e_sp0 E1 + lo) (Z.to_nat n) HE1 HM1 ltac:(lia) ltac:(rewrite Z2Nat.id; lia))
          as (bs & Hbs & Hlen).
        set (X := bytes_le_to_Z bs).
        pose proof (bytes_le_to_Z_bound bs) as XB. pose proof (bytes_le_to_Z_nonneg bs) as X0. rewrite Hlen, Z2Nat.id in XB by lia. fold X in XB, X0.
        unfold load_install in INS.
        pose proof (afresh_sound (v1 A) nu (urange n) X HL ltac:(unfold urange; split; cbn [fst snd lo_le hi_ge]; lia)) as AF.
        destruct (afresh (v1 A) (urange n)) as [[u|] A2]; [|discriminate].
        destruct AF as (nu1 & X1 & HL1 & Eu & Bu).
        pose proof (areinterp_sound A2 nu1 u n sg X HL1 Hn Bu ltac:(rewrite Eu; symmetry; apply zwrap_id; lia)) as AR.
        destruct (areinterp A2 u n sg) as [v' A3'] eqn:ARE. injection INS as -> -> EM'. subst m'. injection HX as <-.
        destruct AR as (nu2 & X2 & HL2 & DEN).
        pose proof (aext_trans _ _ _ _ _ _ X1 X2) as X02. pose proof X02 as (X02e & X02le & SH02).
        destruct (load_machine SEGS P E mem0 A nu regs mem pc rom w sz sg rd rs1 imm addr (e_sp0 E1 + lo) bs HG2 Hf He Hd Hsz Ha
                    ltac:(rewrite Eaddr, Elo; reflexivity) Hbs) as [wl [Hwl ST]].
        rewrite Hbe in ST.
        set (B := finish (set_slots A3 (cm_set (vs_slots (v1 A)) lo (n, Some u))) (rz rd) v).
        change (finish2 (with_v1 A (set_slots A3 (cm_set (vs_slots (v1 A)) lo (n, Some u)))) (rz rd) v) with (with_v1 A B).
        (* [comment removed for export] *)
        assert (GUP : gamma SEGS P1 E1 (zpatch P E mem0 mem) (finish A3 (rz rd) v) nu2 (regupd regs rd wl) mem).
        { unfold finish. eapply (gamma_upd SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) A3 nu nu2 regs mem rd wl v); eauto.
          destruct v as [e|]; [|exact I]. destruct DEN as [D1 D2]. split; [rewrite Hwl; exact D1|exact D2]. }
        assert (SL3 : vs_slots A3 = vs_slots (v1 A)) by (destruct SH02 as (_ & SS & _); exact SS).
        assert (GB : gamma SEGS P1 E1 (zpatch P E mem0 mem) B nu2 (regupd regs rd wl) mem).
        { pose proof GUP as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HGl&HN&HB).
          assert (EQB : B = set_slots (finish A3 (rz rd) v) (cm_set (vs_slots (v1 A)) lo (n, Some u))).
          { unfold B, finish, set_reg, set_slots, set_pc. destruct (Z.eqb (rz rd) 0); [destruct A3; reflexivity|destruct v; destruct A3; reflexivity]. }
          rewrite EQB.
          split; [exact HE|]. split; [exact HM|]. split; [exact HF|]. split; [exact HS|]. split; [exact HC|]. split; [exact HMo|].
          split; [exact HV|]. split; [exact HR|]. split.
          { intros off' w' v' Hin. cbn [vs_slots set_slots] in Hin. apply cm_set_in in Hin as [Hin|Hin].
            - injection Hin as -> -> ->. split; [lia|]. unfold cell_holds. exists bs. split; [exact Hbs|].
              fold X. destruct X2 as (X2e & _). rewrite (eval_ext_below _ _ _ _ X2e Bu), Eu. symmetry. apply zwrap_id. lia.
            - apply HSl. unfold finish, set_reg, set_pc. destruct (Z.eqb (rz rd) 0); [|destruct v]; cbn; rewrite SL3; exact Hin. }
          split; [exact HGl|]. split; [exact HN|].
          destruct HB as (B0&B1&B2&B3&B4&B5). split; [exact B0|]. split; [exact B1|]. split; [exact B2|]. split; [|split; [exact B4|exact B5]].
          intros k' w' e' Hin. cbn [vs_slots set_slots vs_next] in Hin |- *. apply cm_set_in in Hin as [Hin|Hin].
          - injection Hin as -> -> ->. assert (NX3 : vs_next (finish A3 (rz rd) v) = vs_next A3) by (unfold finish, set_reg; destruct (Z.eqb (rz rd) 0); reflexivity).
            match goal with |- lin_below _ ?b = true => replace b with (vs_next A3) by (rewrite <- NX3; reflexivity) end.
            destruct X2 as (_ & L2 & _). eapply lin_below_mono; [exact L2|exact Bu].
          - apply (B3 k' w' e'). unfold finish, set_reg, set_pc. destruct (Z.eqb (rz rd) 0); [|destruct v]; cbn; rewrite SL3; exact Hin. }
        exists (regupd regs rd wl), (v_addi pc 4), mem, (with_v1 A B), nu2.
        split; [exact ST|]. split; [left; reflexivity|].
        assert (SHP : vs_pc A3 = vs_pc (v1 A)) by (destruct SH02 as (_ & _ & _ & _ & SP & _); exact SP).
        split.
        { unfold vs2_pc, B, finish. cbn [v1 with_v1]. unfold npc_of, v_addi. rewrite u_Z_to_bv64, wrap64_zwrap.
          unfold set_reg. destruct (Z.eqb (rz rd) 0); cbn [vs_pc set_pc set_slots]; rewrite SHP; unfold vs2_pc in Hpc; rewrite Hpc; reflexivity. }
        assert (NXB : (vs_next (v1 A) <= vs_next B)%positive).
        { unfold B, finish, set_reg. destruct (Z.eqb (rz rd) 0); cbn; exact X02le. }
        split; [exact X02e|]. split; [exact NXB|].
        destruct (gamma2_lift SEGS P E mem0 PO2 A B nu nu2 regs (regupd regs rd wl) mem mem HG2 GB X02e NXB (frame_mod_refl _ _)) as (G3 & FM3 & FS3).
        { unfold globs_ok2. cbn [v1 with_v1]. replace (vs_globs B) with (vs_globs (v1 A)); [exact GL|].
          unfold B, finish, set_reg, set_pc, set_slots. destruct SH02 as (_ & _ & SG & _). destruct (Z.eqb (rz rd) 0); [|destruct v]; cbn; symmetry; exact SG. }
        { left; reflexivity. }
        split; [exact FM3|]. split; [exact FS3|exact G3].
      + (* [comment removed for export] *)
        destruct (load_val_sound SEGS P1 E1 (zpatch P E mem0 mem) (PO1 _ _ PO2) (v1 A) nu regs mem (RStack off lo hi) addr n sg G1 Hn Baddr CL)
          as (bs & Hbs & RW).
        rewrite wordZ_zwrap in Hbs.
        destruct (load_val P1 (v1 A) (RStack off lo hi) addr n sg) as [v A2] eqn:LV. injection HX as <-.
        destruct (load_machine SEGS P E mem0 A nu regs mem pc rom w sz sg rd rs1 imm addr (eval nu addr) bs HG2 Hf He Hd Hsz Ha eq_refl Hbs) as [wl [Hwl ST]].
        rewrite Hbe in ST. eapply (finish2_post SEGS P E mem0 PO2); eauto. rewrite Hwl. exact RW.
  Qed.
End E.

(* [comment removed for export] *)
Theorem vstep2_sound_closed (SEGS : list Segment) :
  forall P E mem0 rom A i succs nu regs mem (pc : word) w,
    params_ok2 SEGS P ->
    vstep2 P A i = VR2_next succs ->
    gamma2 SEGS P E mem0 A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4) ->
    step_post2 SEGS P E mem0 A nu succs regs mem pc rom.
Proof.
  apply vstep2_sound_iface.
  - intros P E mem0 PO2. exact (x_load_stack_sound SEGS P E mem0 PO2).
  - intros P E mem0 PO2. exact (x_install_rgn_sound SEGS P E mem0 PO2).
  - intros P E mem0 PO2. exact (x_srl_split_sound SEGS P E mem0 PO2).
Qed.
