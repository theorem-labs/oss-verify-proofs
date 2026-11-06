(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import SeqExec Hoare ZStores RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import TolowerDefs.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VWord2 VState VLogic VAbs VAbsSound VAbsSound2 VAbsSound3 VStep VStepMem VGamma VStepSound VStepMemSound VStepMemSound2 VCert VContract.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_CALLER_SAVED_dec r : {In r CALLER_SAVED} + {~ In r CALLER_SAVED}.
Proof. apply in_dec. apply Z.eq_dec. Qed.

(* [comment removed for export] *)
Lemma set_tops_regs A l r e :
  pm_get (reg_key r) (vs_regs (set_tops A l)) = Some e ->
  pm_get (reg_key r) (vs_regs A) = Some e /\ (0 < r -> Forall (fun x => 0 < x) l -> ~ In r l).
Proof.
  revert A. induction l as [|x t IH]; intros A Hg; cbn [set_tops] in Hg.
  - split; [exact Hg|]. intros _ _ [].
  - destruct (IH _ Hg) as [Hg1 Hn]. unfold set_reg in Hg1.
    destruct (Z.eqb_spec x 0) as [->|Hx].
    + split; [exact Hg1|]. intros Hr HF Hin. inversion HF; subst. lia.
    + cbn [vs_regs set_regs] in Hg1. rewrite pm_get_remove in Hg1.
      destruct (Pos.eqb_spec (reg_key r) (reg_key x)) as [E|NE]; [discriminate|].
      split; [exact Hg1|]. intros Hr HF [->|Hin].
      * apply NE. reflexivity.
      * inversion HF; subst. exact (Hn Hr ltac:(assumption) Hin).
Qed.

Lemma set_tops_shape A l :
  vs_slots (set_tops A l) = vs_slots A /\ vs_globs (set_tops A l) = vs_globs A /\ vs_nul (set_tops A l) = vs_nul A /\
  vs_store (set_tops A l) = vs_store A /\ vs_next (set_tops A l) = vs_next A /\
  vs_conddef (set_tops A l) = vs_conddef A /\ vs_moddef (set_tops A l) = vs_moddef A /\ vs_valset (set_tops A l) = vs_valset A.
Proof.
  revert A. induction l as [|x t IH]; intros A; cbn [set_tops]; [repeat split; reflexivity|].
  destruct (IH (set_reg A x None)) as (S1&S2&S3&S4&S5&S6&S7&S8). rewrite S1, S2, S3, S4, S5, S6, S7, S8.
  unfold set_reg. destruct (Z.eqb x 0); repeat split; reflexivity.
Qed.

Lemma CALLER_SAVED_pos : Forall (fun x => 0 < x) CALLER_SAVED.
Proof. unfold CALLER_SAVED. repeat constructor. Qed.

(* [comment removed for export] *)
Lemma not_caller_saved_kept (r : reg) :
  bv_unsigned r <> 0 -> ~ In (bv_unsigned r) CALLER_SAVED -> In r callee_kept.
Proof.
  intros Hr Hn. pose proof (bv_unsigned_in_range 5 r) as R. unfold bv_modulus in R. cbn in R.
  unfold CALLER_SAVED in Hn. cbn [In] in Hn.
  assert (E : exists k, bv_unsigned r = k /\ 0 <= k < 32) by (exists (bv_unsigned r); lia).
  destruct E as [k [Ek Hk]]. rewrite Ek in Hn, Hr.
  assert (Hrk : r = Z_to_bv 5 k) by (apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_small by lia; lia).
  subst r. unfold callee_kept.
  assert (K : k = 2 \/ k = 3 \/ k = 4 \/ k = 8 \/ k = 9 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) by lia.
  cbn [In].
  destruct K as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
    repeat (try (left; apply bv_eq; reflexivity); right); left; apply bv_eq; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma regs_agree_CS (clob : list reg) regs regs' :
  forallb (fun r : reg => existsb (Z.eqb (bv_unsigned r)) CALLER_SAVED) clob = true ->
  regs_agree (fun r => In r clob) regs regs' ->
  forall r : reg, bv_unsigned r <> 0 -> ~ In (bv_unsigned r) CALLER_SAVED -> getr regs' r = getr regs r.
Proof.
  intros Hsub HA r Hr Hn. apply HA. intros Hin.
  pose proof (proj1 (forallb_forall _ _) Hsub r Hin) as X. cbn beta in X.
  apply existsb_exists in X as [z [Hz Ez]]. apply Z.eqb_eq in Ez. subst z. exact (Hn Hz).
Qed.

Lemma regs_agree_ra (clob : list reg) regs regs' :
  existsb (fun r : reg => Z.eqb (bv_unsigned r) 1) clob = false ->
  regs_agree (fun r => In r clob) regs regs' -> getr regs' 1%bv = getr regs 1%bv.
Proof.
  intros H HA. apply HA. intros Hin.
  assert (X : existsb (fun r : reg => Z.eqb (bv_unsigned r) 1) clob = true).
  { apply existsb_exists. exists 1%bv. split; [exact Hin|reflexivity]. }
  rewrite X in H. discriminate.
Qed.

(* [comment removed for export] *)
Section CS.
  Variable SEGS : list Segment.
  Variable P : vparams.
  Variable E : venv.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Hypothesis PO : params_ok SEGS P.

  Notation gammaP := (gamma SEGS P E mem0).
  Notation MCP := (MC SEGS P E mem0).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma reg_val A nu regs mem (r : reg) e :
    gammaP A nu regs mem -> bv_unsigned r <> 0 -> get_reg A (bv_unsigned r) = Some e ->
    bv_unsigned (getr regs r) = zwrap 64 (eval nu e) /\ lin_below e (vs_next A) = true.
  Proof.
    intros HGm Hr Hg. pose proof HGm as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB).
    unfold get_reg in Hg. destruct (Z.eqb_spec (bv_unsigned r) 0); [lia|].
    split; [exact (HR r e Hr Hg)|]. destruct HB as (_&_&RB&_). exact (RB _ _ Hg).
  Qed.

  Lemma reg_word A nu regs mem (r : reg) e x :
    gammaP A nu regs mem -> bv_unsigned r <> 0 -> get_reg A (bv_unsigned r) = Some e ->
    eval nu e = x -> 0 <= x < 2 ^ 64 -> getr regs r = wordZ x.
  Proof.
    intros HGm Hr Hg Ex Hx. apply wordZ_eq_u. rewrite (proj1 (reg_val A nu regs mem r e HGm Hr Hg)), Ex. apply zwrap_id. exact Hx.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma dead_lin_false A nu e : lgamma A nu -> dead_lin A e = true -> False.
  Proof.
    intros HL Hd. unfold dead_lin in Hd. exact (itv_empty_sound _ _ Hd (bnd_sound A nu e HL)).
  Qed.

  Lemma nonneg_len_sound A nu n mx lo hi :
    lgamma A nu -> nonneg_len A n mx = NR_ok lo hi ->
    exists e, n = Some e /\ 0 <= lo /\ lo <= eval nu e <= hi /\ hi <= mx.
  Proof.
    intros HL. unfold nonneg_len. destruct n as [e|]; [|discriminate].
    destruct (dead_lin A e); [discriminate|].
    pose proof (bnd_sound A nu e HL) as Hb. destruct (bnd A e) as [[l|] [h|]]; try discriminate.
    destruct (Z.ltb_spec l 0); destruct (Z.ltb_spec mx h); cbn [orb]; try discriminate.
    intros X; injection X as <- <-. destruct Hb as [H1 H2]; cbn [fst snd lo_le hi_ge] in H1, H2.
    exists e. repeat split; auto; lia.
  Qed.

  Lemma nonneg_len_dead A nu n mx : lgamma A nu -> nonneg_len A n mx = NR_dead -> False.
  Proof.
    intros HL. unfold nonneg_len. destruct n as [e|]; [|discriminate].
    destruct (dead_lin A e) eqn:Ed; [intros _; exact (dead_lin_false A nu e HL Ed)|].
    destruct (bnd A e) as [[l|] [h|]]; try discriminate. destruct (_ || _); discriminate.
  Qed.

  (* [comment removed for export] *)
  Lemma stack_range_sound A nu base n st off lo hi :
    lgamma A nu -> gamma_fix E nu ->
    stack_range P A base n st = RR_stack off lo hi ->
    off = lsub base (lsym SP0) /\ eval nu base = e_sp0 E + eval nu off /\
    lo <= eval nu off /\ eval nu off + eval nu n <= hi /\ - vp_frame P <= lo /\ hi <= 0 /\
    (st = true -> in_ranges (vp_wstack P) lo (hi - lo) = true).
  Proof.
    intros HL HF. unfold stack_range.
    destruct (is_sp_rel base); [|discriminate]. cbn [negb].
    destruct (dead_lin A (lsub base (lsym SP0)) || dead_lin A (ladd (lsub base (lsym SP0)) n)); [discriminate|].
    unfold lo_of, hi_of.
    pose proof (bnd_sound A nu (lsub base (lsym SP0)) HL) as B1.
    pose proof (bnd_sound A nu (ladd (lsub base (lsym SP0)) n) HL) as B2.
    destruct (bnd A (lsub base (lsym SP0))) as [[l1|] h1]; [|discriminate].
    destruct (bnd A (ladd (lsub base (lsym SP0)) n)) as [l2 [h2|]]; [|discriminate]. cbn [fst snd].
    destruct (Z.ltb_spec l1 (- vp_frame P)); [discriminate|].
    destruct (Z.ltb_spec 0 h2); [discriminate|].
    destruct (st && negb (in_ranges (vp_wstack P) l1 (h2 - l1))) eqn:Ew; [discriminate|].
    intros X; injection X as <- <- <-.
    destruct B1 as [B1 _]. destruct B2 as [_ B2]. cbn [fst snd lo_le hi_ge] in B1, B2.
    rewrite eval_ladd, eval_lsub, eval_lsym, (nu_SP0 E nu HF) in *. rewrite ?eval_lsub, ?eval_lsym, ?(nu_SP0 E nu HF).
    repeat split; try lia.
    intros ->. cbn [andb] in Ew. destruct (in_ranges _ _ _); [reflexivity|discriminate].
  Qed.

  Lemma stack_range_dead A nu base n st : lgamma A nu -> stack_range P A base n st = RR_dead -> False.
  Proof.
    intros HL. unfold stack_range. destruct (is_sp_rel base); [|discriminate]. cbn [negb].
    destruct (dead_lin A (lsub base (lsym SP0))) eqn:E1; [intros _; exact (dead_lin_false A nu _ HL E1)|].
    destruct (dead_lin A (ladd (lsub base (lsym SP0)) n)) eqn:E2; [intros _; exact (dead_lin_false A nu _ HL E2)|]. cbn [orb].
    destruct (lo_of A _); [|discriminate]. destruct (hi_of A _); [|discriminate].
    destruct (Z.ltb _ _); [discriminate|]. destruct (Z.ltb _ _); [discriminate|]. destruct (st && _); discriminate.
  Qed.

  Lemma stack_range_shape A base n st :
    match stack_range P A base n st with RR_data _ | RR_img _ _ => False | _ => True end.
  Proof.
    unfold stack_range. destruct (negb _); [exact I|]. destruct (_ || _); [exact I|].
    destruct (lo_of _ _); [|exact I]. destruct (hi_of _ _); [|exact I].
    destruct (Z.ltb _ _); [exact I|]. destruct (Z.ltb _ _); [exact I|]. destruct (st && _); exact I.
  Qed.

  (* [comment removed for export] *)
  Definition readable (mem : word -> option byte) (a n : Z) : Prop :=
    0 <= a /\ a + n < 2 ^ 64 /\ forall i, 0 <= i < n -> exists b, rdn SEGS mem (wordZ (a + i)) 1 = Some [b].

  Lemma readable_rdn mem a n : readable mem a n -> 0 <= n ->
    exists bs, rdn SEGS mem (wordZ a) (Z.to_nat n) = Some bs /\ length bs = Z.to_nat n.
  Proof.
    intros (H0&H1&Hb) Hn. apply rdn_bytes; [lia|lia|]. intros k Hk. apply Hb. lia.
  Qed.

  Lemma readable_range_sound A nu regs mem base n rr :
    gammaP A nu regs mem -> 0 <= eval nu n ->
    readable_range P A base n = rr ->
    match rr with
    | RR_fail _ => True
    | RR_dead => False
    | _ => readable mem (eval nu base) (eval nu n)
    end.
  Proof.
    intros HGm Hn <-. pose proof (gamma_lgamma _ _ _ _ _ _ _ _ HGm) as HL.
    pose proof HGm as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB).
    pose proof HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12). pose proof PO as (P0&P1&PS&PF&PW&PR&PP&PB).
    unfold readable_range.
    destruct (is_sp_rel base).
    - pose proof (stack_range_shape A base n false) as SH.
      destruct (stack_range P A base n false) as [off lo hi| | | |] eqn:Es; try exact I.
      + destruct (stack_range_sound A nu base n false off lo hi HL HF Es) as (_&Eb&H1&H2&H3&H4&_).
        split; [lia|]. split; [lia|]. intros i Hi.
        destruct (MC_frame_ok SEGS P E mem0 mem (eval nu base + i) HM) as [_ X]; [lia|exact X].
      + destruct SH.
      + destruct SH.
      + exact (stack_range_dead A nu base n false HL Es).
    - destruct (is_data_rel base).
      + destruct (dead_lin A (lsub base (lsym DATA))) eqn:Ed; [exact (dead_lin_false A nu _ HL Ed)|].
        unfold lo_of, hi_of.
        pose proof (bnd_sound A nu (lsub base (lsym DATA)) HL) as B1.
        destruct (bnd A (lsub base (lsym DATA))) as [[l1|] h1]; [|exact I]. cbn [fst].
        destruct (Z.ltb_spec l1 0); [exact I|].
        pose proof (bnd_sound A nu (lsub (ladd (lsub base (lsym DATA)) n) (lsym SIZE)) HL) as B2.
        destruct (bnd A (lsub (ladd (lsub base (lsym DATA)) n) (lsym SIZE))) as [l2 [h2|]]; [|exact I]. cbn [snd].
        destruct (Z.ltb_spec 0 h2); [exact I|].
        destruct B1 as [B1 _]. destruct B2 as [_ B2]. cbn [fst snd lo_le hi_ge] in B1, B2.
        rewrite !eval_lsub, ?eval_ladd, ?eval_lsub, !eval_lsym, (nu_DATA E nu HF) in B1.
        rewrite eval_lsub, eval_ladd, eval_lsub, !eval_lsym, (nu_DATA E nu HF), (nu_SIZE E nu HF) in B2.
        destruct HM as (MF&MD&MP&MFM).
        split; [lia|]. split; [lia|]. intros i Hi.
        replace (eval nu base + i) with (e_data E + (eval nu base - e_data E + i)) by lia. apply MD. lia.
      + destruct (negb _); [exact I|]. unfold lo_of, hi_of.
        pose proof (bnd_sound A nu base HL) as B1. pose proof (bnd_sound A nu (ladd base n) HL) as B2.
        destruct (bnd A base) as [[l1|] h1]; [|exact I]. destruct (bnd A (ladd base n)) as [l2 [h2|]]; [|exact I]. cbn [fst snd].
        destruct (in_ranges (vp_segs P) l1 (h2 - l1)) eqn:Er; [|exact I].
        destruct B1 as [B1 _]. destruct B2 as [_ B2]. cbn [fst snd lo_le hi_ge] in B1, B2. rewrite eval_ladd in B2.
        destruct (in_ranges_sound _ _ _ Er) as [slo [shi (Hin&Q1&Q2)]]. destruct (PS _ _ Hin) as (S0&S1&SB).
        split; [lia|]. split; [lia|]. intros i Hi. apply rdn1_any. apply SB. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition range_outside (R : list (word * Z)) (a w : Z) : Prop :=
    forall x, a <= x < a + w -> outside (wordZ x) R.

  Lemma rdn_unchanged mem mem' R a (w : nat) :
    (forall x, outside x R -> mem' x = mem x) -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
    range_outside R a (Z.of_nat w) -> rdn SEGS mem' (wordZ a) w = rdn SEGS mem (wordZ a) w.
  Proof.
    intros HR Ha Hw Hout. destruct w as [|w']; [reflexivity|].
    apply rdn_ext; [rewrite u_wordZ; lia|].
    intros x Hx. rewrite u_wordZ in Hx by lia. apply HR.
    rewrite <- (wordZ_u x). apply Hout. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="rom PO"] Lemma gamma_call_post A A' nu nu' regs regs' mem mem' (R : list (word * Z)) :
    gammaP A nu regs mem ->
    ext (vs_next A) nu nu' -> (vs_next A <= vs_next A')%positive -> lgamma A' nu' ->
    gamma_regs nu' A' regs' ->
    (forall off w v, In (off, (w, v)) (vs_slots A') ->
       (In (off, (w, v)) (vs_slots A) /\ range_outside R (e_sp0 E + off) w)
       \/ ((- vp_frame P <= off /\ 0 < w /\ off + w <= 0) /\ cell_holds SEGS nu' mem' (e_sp0 E + off) w v)) ->
    (forall a w v, In (a, (w, v)) (vs_globs A') -> In (a, (w, v)) (vs_globs A) /\ range_outside R a w) ->
    (forall lo hi, In (lo, hi) (vs_nul A') ->
       (In (lo, hi) (vs_nul A) /\ range_outside R (e_sp0 E + lo) (hi - lo + 1))
       \/ (exists off b, lo <= off <= hi /\ (- vp_frame P <= off < 0) /\
                         rdn SEGS mem' (wordZ (e_sp0 E + off)) 1 = Some [b] /\ bv_unsigned b = 0)) ->
    frame_mod mem mem' R ->
    (* [comment removed for export] *)
    (forall x, ~ outside x R ->
       ~ outside x (unit_regions P E) /\ ~ outside x (footprint P E) /\
       forall lo hi, In (lo, hi) (vp_pristine P) -> ~ (lo <= bv_unsigned x < hi)) ->
    gammaP A' nu' regs' mem' /\ frame_mod mem mem' (unit_regions P E).
  Proof.
    intros HGm HX HLe HL' HR' HSl' HG' HN' HFM HRok.
    pose proof HGm as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB).
    pose proof HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12). pose proof PO as (P0&P1&PS&PF&PW&PR&PP&PB).
    destruct HFM as [HRe HGr].
    assert (OUTdec : forall x, outside x R \/ ~ outside x R).
    { intros x. clear. induction R as [|[b len] t IH]; cbn [outside]; [left; exact I|].
      destruct IH as [IH|IH]; [|right; intros [_ X]; exact (IH X)]. unfold in_rng.
      destruct (Z_le_gt_dec (bv_unsigned b) (bv_unsigned x)); destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned b + len));
        first [left; split; [lia|exact IH] | right; intros [X _]; apply X; lia]. }
    split.
    - split; [exact HE|]. split.
      { (* [comment removed for export] *) destruct HM as (MF&MD&MP&MFM). split; [|split; [|split]].
        + intros a Ha. destruct (MF a Ha) as [S1 R1]. split; [eapply store_ok_mono; eauto|eapply rdn1_grows; eauto].
        + intros i Hi. eapply rdn1_grows; eauto.
        + intros lo hi a Hp Ha. rewrite <- (MP lo hi a Hp Ha). apply HRe.
          destruct (OUTdec (wordZ a)) as [X|X]; [exact X|]. exfalso. destruct (HRok _ X) as (_&_&NP).
          apply (NP lo hi Hp). destruct (PP _ _ Hp). rewrite u_wordZ by lia. exact Ha.
        + split; [|eapply mem_grows_trans; [apply (proj2 MFM)|exact HGr]].
          intros a Ha. destruct (OUTdec a) as [X|X].
          * rewrite (HRe a X). apply (proj1 MFM). exact Ha.
          * exfalso. exact (proj1 (proj2 (HRok _ X)) Ha). }
      split; [eapply gamma_fix_ext; [|exact HX|exact HF]; destruct HB; auto|].
      destruct HL' as (S1&C1&M1&V1&B1).
      split; [exact S1|]. split; [exact C1|]. split; [exact M1|]. split; [exact V1|].
      split; [exact HR'|]. split; [|split; [|split; [|exact B1]]].
      + intros off w v Hin. destruct (HSl' _ _ _ Hin) as [[Hold Hout]|NEW]; [|exact NEW]. destruct (HSl _ _ _ Hold) as [Hrg Hch].
        split; [exact Hrg|]. destruct v as [e|]; [|exact I]. cbn [cell_holds] in Hch |- *.
        rewrite (rdn_unchanged mem mem' R (e_sp0 E + off) (Z.to_nat w) HRe) by (try (ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @P0; @Hrg; @E2; @P1]); lia); rewrite Z2Nat.id by (ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @P0; @Hrg; @E2; @P1]); lia); try (ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @P0; @Hrg; @E2; @P1]); lia); exact Hout).
        rewrite (eval_ext_below (vs_next A) nu nu' e HX); [exact Hch|].
        destruct HB as (_&_&_&CB&_). exact (CB _ _ _ Hold).
      + intros a w v Hin. destruct (HG' _ _ _ Hin) as [Hold Hout]. destruct (HG _ _ _ Hold) as [Hrg Hch].
        split; [exact Hrg|]. destruct v as [e|]; [|exact I]. cbn [cell_holds] in Hch |- *.
        rewrite (rdn_unchanged mem mem' R a (Z.to_nat w) HRe) by (try (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hrg; @E1; @E2; @P0; @P1]); lia); rewrite Z2Nat.id by (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hrg; @E1; @E2; @P0; @P1]); lia); try (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hrg; @E1; @E2; @P0; @P1]); lia); exact Hout).
        rewrite (eval_ext_below (vs_next A) nu nu' e HX); [exact Hch|].
        destruct HB as (_&_&_&_&GB&_). exact (GB _ _ _ Hold).
      + intros lo hi Hin. destruct (HN' _ _ Hin) as [[Hold Hout]|NEW]; [|exact NEW]. destruct (HN _ _ Hold) as [off [b (Q1&Q2&Q3&Q4)]].
        exists off, b. split; [exact Q1|]. split; [exact Q2|]. split; [|exact Q4].
        rewrite <- Q3. apply (rdn_unchanged mem mem' R (e_sp0 E + off) 1 HRe); [(ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Q2; @E2; @P1]); lia)|(ltac2:(LK.k [@E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Q2; @E2; @P1]); lia)|].
        intros x Hx. apply Hout. lia.
    - split; [|exact HGr]. intros a Ha. destruct (OUTdec a) as [X|X]; [exact (HRe a X)|].
      exfalso. exact (proj1 (HRok _ X) Ha).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma kill_nul_None_shape A lo hi :
    let K := kill_nul A lo hi None in
    vs_slots K = vs_slots A /\ vs_globs K = vs_globs A /\ vs_store K = vs_store A /\ vs_next K = vs_next A /\
    vs_conddef K = vs_conddef A /\ vs_moddef K = vs_moddef A /\ vs_valset K = vs_valset A /\ vs_regs K = vs_regs A /\
    (forall f, In f (vs_nul K) -> In f (vs_nul A) /\ (snd f < lo \/ hi < fst f)).
  Proof.
    unfold kill_nul. cbn [is_zero_val].
    destruct (vs_nul A) as [|f0 t] eqn:EN.
    - cbn zeta. rewrite EN. repeat split; try reflexivity. all: destruct H.
    - cbn [set_nul vs_slots vs_globs vs_store vs_next vs_conddef vs_moddef vs_valset vs_regs vs_nul].
      repeat split; try reflexivity.
      + apply filter_In in H as [H _]. exact H.
      + apply filter_In in H as [_ H]. apply Bool.orb_prop in H as [H|H]; apply Z.ltb_lt in H; lia.
  Qed.

  Lemma contract_frame_shape c A1 spoff v :
    let CF := contract_frame c A1 spoff v in
    vs_slots CF = (if Z.eqb (contract_K c) 0 then vs_slots A1 else cm_kill (vs_slots A1) (spoff - contract_K c) spoff) /\
    vs_globs CF = vs_globs A1 /\
    (forall f, In f (vs_nul CF) -> In f (vs_nul A1) /\ (contract_K c = 0 \/ snd f < spoff - contract_K c \/ spoff - 1 < fst f)) /\
    vs_store CF = vs_store A1 /\ vs_next CF = vs_next A1 /\
    vs_conddef CF = vs_conddef A1 /\ vs_moddef CF = vs_moddef A1 /\ vs_valset CF = vs_valset A1 /\
    (forall r e, pm_get (reg_key r) (vs_regs CF) = Some e -> 0 < r ->
       (reg_key r = reg_key A0r /\ v = Some e) \/ (reg_key r <> reg_key A0r /\ ~ In r CALLER_SAVED /\ pm_get (reg_key r) (vs_regs A1) = Some e)).
  Proof.
    unfold contract_frame. cbn zeta.
    set (A2 := if contract_K c =? 0 then A1
               else kill_nul (set_slots A1 (cm_kill (vs_slots A1) (spoff - contract_K c) spoff)) (spoff - contract_K c) (spoff - 1) None).
    destruct (set_tops_shape A2 CALLER_SAVED) as (S1&S2&S3&S4&S5&S6&S7&S8).
    assert (A2f : vs_globs A2 = vs_globs A1 /\
                  (forall f, In f (vs_nul A2) -> In f (vs_nul A1) /\ (contract_K c = 0 \/ snd f < spoff - contract_K c \/ spoff - 1 < fst f)) /\
                  vs_store A2 = vs_store A1 /\ vs_next A2 = vs_next A1 /\
                  vs_conddef A2 = vs_conddef A1 /\ vs_moddef A2 = vs_moddef A1 /\ vs_valset A2 = vs_valset A1 /\ vs_regs A2 = vs_regs A1 /\
                  vs_slots A2 = (if Z.eqb (contract_K c) 0 then vs_slots A1 else cm_kill (vs_slots A1) (spoff - contract_K c) spoff)).
    { unfold A2. destruct (Z.eqb_spec (contract_K c) 0) as [K0|K1].
      - repeat split; try reflexivity; auto.
      - destruct (kill_nul_None_shape (set_slots A1 (cm_kill (vs_slots A1) (spoff - contract_K c) spoff)) (spoff - contract_K c) (spoff - 1))
          as (K1'&K2&K3&K4&K5&K6&K7&K8&KN).
        rewrite K1', K2, K3, K4, K5, K6, K7, K8. repeat split; try reflexivity.
        + exact (proj1 (KN _ H)).
        + right. exact (proj2 (KN _ H)). }
    destruct A2f as (T1&T2&T3&T4&T5&T6&T7&T8&T9).
    unfold set_reg. cbn [Z.eqb A0r].
    assert (GEN : forall m, let CF := set_regs (set_tops A2 CALLER_SAVED) m in
              vs_slots CF = vs_slots A2 /\ vs_globs CF = vs_globs A1 /\ vs_nul CF = vs_nul A2 /\ vs_store CF = vs_store A1 /\
              vs_next CF = vs_next A1 /\ vs_conddef CF = vs_conddef A1 /\ vs_moddef CF = vs_moddef A1 /\ vs_valset CF = vs_valset A1 /\ vs_regs CF = m).
    { intros m. cbn [set_regs vs_slots vs_globs vs_nul vs_store vs_next vs_conddef vs_moddef vs_valset vs_regs].
      rewrite S1, S2, S3, S4, S5, S6, S7, S8, T1, T3, T4, T5, T6, T7. repeat split; reflexivity. }
    destruct v as [e0|].
    - destruct (GEN (pm_set (reg_key A0r) e0 (vs_regs (set_tops A2 CALLER_SAVED)))) as (G1&G2&G3&G4&G5&G6&G7&G8&G9).
      rewrite G1, G2, G3, G4, G5, G6, G7, G8, G9, T9. repeat split; try reflexivity.
      + exact (proj1 (T2 _ H)).
      + exact (proj2 (T2 _ H)).
      + intros r e Hg Hr. rewrite pm_get_set in Hg. destruct (Pos.eqb_spec (reg_key r) (reg_key A0r)) as [EQ|NE].
        * left. injection Hg as <-. auto.
        * right. destruct (set_tops_regs A2 CALLER_SAVED r e Hg) as [Hg1 Hn]. rewrite T8 in Hg1.
          split; [exact NE|]. split; [apply Hn; [exact Hr|apply CALLER_SAVED_pos]|exact Hg1].
    - destruct (GEN (pm_remove (reg_key A0r) (vs_regs (set_tops A2 CALLER_SAVED)))) as (G1&G2&G3&G4&G5&G6&G7&G8&G9).
      rewrite G1, G2, G3, G4, G5, G6, G7, G8, G9, T9. repeat split; try reflexivity.
      + exact (proj1 (T2 _ H)).
      + exact (proj2 (T2 _ H)).
      + intros r e Hg Hr. rewrite pm_get_remove in Hg. destruct (Pos.eqb_spec (reg_key r) (reg_key A0r)) as [EQ|NE]; [discriminate|].
        right. destruct (set_tops_regs A2 CALLER_SAVED r e Hg) as [Hg1 Hn]. rewrite T8 in Hg1.
        split; [exact NE|]. split; [apply Hn; [exact Hr|apply CALLER_SAVED_pos]|exact Hg1].
  Qed.

  Lemma lgamma_contract_frame c A1 spoff v nu :
    lgamma A1 nu -> vbelow v (vs_next A1) -> lgamma (contract_frame c A1 spoff v) nu.
  Proof.
    intros (HS&HC&HM&HV&(B0&B1&B2&B3&B4&(C1&C2&C3))) Hv.
    destruct (contract_frame_shape c A1 spoff v) as (F1&F2&F3&F4&F5&F6&F7&F8&FR).
    set (CF := contract_frame c A1 spoff v) in *.
    split; [rewrite F4; exact HS|]. split; [intros b k x y Hg; rewrite F6 in Hg; exact (HC _ _ _ _ Hg)|].
    split; [intros r x m Hg; rewrite F7 in Hg; exact (HM _ _ _ Hg)|]. split; [intros s' vs Hg; rewrite F8 in Hg; exact (HV _ _ Hg)|].
    split; [rewrite F5; exact B0|]. split; [rewrite F4, F5; exact B1|]. split.
    { intros p e Hg. rewrite F5.
      destruct (FR (Z.pos p) e Hg ltac:(lia)) as [[_ ->]|(_&_&Hg1)]; [exact Hv|exact (B2 _ _ Hg1)]. }
    split; [rewrite F1, F5; destruct (contract_K c =? 0); [exact B3|intros k w e Hin; apply cm_kill_sub in Hin; exact (B3 _ _ _ Hin)]|].
    split; [rewrite F2, F5; exact B4|].
    split; [intros b k x y Hg; rewrite F6 in Hg; rewrite F5; exact (C1 _ _ _ _ Hg)|].
    split; [intros r x m Hg; rewrite F7 in Hg; rewrite F5; exact (C2 _ _ _ Hg)|].
    intros s' vs Hg; rewrite F8 in Hg; rewrite F5; exact (C3 _ _ Hg).
  Qed.

  (* [comment removed for export] *)
  Lemma gamma_regs_contract_frame c A A1 spoff v nu nu' regs regs' :
    gammaP A nu regs (fun _ => None) \/ gamma_regs nu A regs /\ regs_below A ->
    ext (vs_next A) nu nu' -> vs_regs A1 = vs_regs A ->
    (forall r : reg, bv_unsigned r <> 0 -> ~ In (bv_unsigned r) CALLER_SAVED -> getr regs' r = getr regs r) ->
    match v with Some e => bv_unsigned (getr regs' 10%bv) = zwrap 64 (eval nu' e) | None => True end ->
    gamma_regs nu' (contract_frame c A1 spoff v) regs'.
  Proof.
    intros HA HX ER HK Hv.
    assert (HR : gamma_regs nu A regs /\ regs_below A).
    { destruct HA as [HGm|HA]; [|exact HA]. pose proof HGm as (_&_&_&_&_&_&_&HR&_&_&_&HB). split; [exact HR|]. destruct HB as (_&_&RB&_); exact RB. }
    destruct HR as [HR RB].
    destruct (contract_frame_shape c A1 spoff v) as (F1&F2&F3&F4&F5&F6&F7&F8&FR).
    intros r e Hr Hg.
    pose proof (bv_unsigned_in_range 5 r) as R5.
    destruct (FR (bv_unsigned r) e Hg ltac:(lia)) as [[Ek Ev]|(Nk&Ncs&Hg1)].
    - assert (r = 10%bv).
      { apply bv_eq. unfold reg_key, A0r in Ek. apply (f_equal Z.pos) in Ek. rewrite Z2Pos.id in Ek by lia. cbn in Ek. rewrite Ek. reflexivity. }
      subst r. subst v. exact Hv.
    - rewrite ER in Hg1. rewrite (HK r Hr Ncs).
      rewrite (eval_ext_below (vs_next A) nu nu' e HX); [exact (HR r e Hr Hg1)|exact (RB _ _ Hg1)].
  Qed.
End CS.
