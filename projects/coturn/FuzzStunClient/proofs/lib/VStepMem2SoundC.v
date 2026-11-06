(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool String Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import SeqExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic VGamma VAbs VAbsSound VAbsSound2 VAbsSound3 VStep VStepMem VStepSound VStepMemSound VStepMemSound2 VState2 VStepMem2 VGamma2 VStepMem2SoundA VStepMem2SoundB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac liae := Z.to_euclidean_division_equations; lia.
Local Ltac niae := Z.to_euclidean_division_equations; nia.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rshape (r r' : vregion) : Prop :=
  vr_base r' = vr_base r /\ vr_disp r' = vr_disp r /\ vr_kind r' = vr_kind r /\
  vr_lo r' = vr_lo r /\ vr_hi r' = vr_hi r /\ vr_w r' = vr_w r /\ vr_b8 r' = vr_b8 r.

Lemma rshape_refl r : rshape r r.
Proof. repeat split; reflexivity. Qed.

Lemma rshape_sym a b : rshape a b -> rshape b a.
Proof. intros (?&?&?&?&?&?&?). repeat split; congruence. Qed.

Lemma rshape_trans a b c : rshape a b -> rshape b c -> rshape a c.
Proof. intros (?&?&?&?&?&?&?) (?&?&?&?&?&?&?). repeat split; congruence. Qed.

Lemma rshape_set_cells r m : rshape r (set_cells r m).
Proof. repeat split; reflexivity. Qed.

Lemma rshape_set_rnul r l : rshape r (set_rnul r l).
Proof. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Inductive shape_map : list vregion -> list vregion -> Prop :=
| SM_nil : shape_map [] []
| SM_cons r r' l l' : rshape r r' -> shape_map l l' -> shape_map (r :: l) (r' :: l').

Lemma shape_map_refl l : shape_map l l.
Proof. induction l; constructor; auto using rshape_refl. Qed.

Lemma shape_map_trans l1 l2 l3 : shape_map l1 l2 -> shape_map l2 l3 -> shape_map l1 l3.
Proof.
  intros H12. revert l3. induction H12 as [|x y t t' HS HT IH]; intros l3 H23; [inversion H23; constructor|].
  inversion H23; subst. constructor; [eapply rshape_trans; eauto|apply IH; assumption].
Qed.

Lemma shape_map_get l l' s r :
  shape_map l l' -> rgn_get l s = Some r -> exists r', rgn_get l' s = Some r' /\ rshape r r'.
Proof.
  intros SM. induction SM as [|x x' t t' HS HT IH]; simpl; [discriminate|].
  destruct HS as (HB & REST). rewrite HB.
  destruct (Pos.eqb (vr_base x) s); [|exact IH].
  intros H; injection H as <-. exists x'. split; [reflexivity|]. split; [exact HB|exact REST].
Qed.

Lemma shape_map_get_back l l' s r' :
  shape_map l l' -> rgn_get l' s = Some r' -> exists r, rgn_get l s = Some r /\ rshape r r'.
Proof.
  intros SM. induction SM as [|x x' t t' HS HT IH]; simpl; [discriminate|].
  destruct HS as (HB & REST). rewrite HB.
  destruct (Pos.eqb (vr_base x) s); [|exact IH].
  intros H; injection H as <-. exists x. split; [reflexivity|]. split; [exact HB|exact REST].
Qed.

Lemma shape_map_in_back l l' r' :
  shape_map l l' -> In r' l' -> exists r, In r l /\ rshape r r'.
Proof.
  intros SM. induction SM as [|x x' t t' HS HT IH]; simpl; [tauto|].
  intros [<-|H]; [exists x; auto|]. destruct (IH H) as (r & Hr & S). exists r; auto.
Qed.

Lemma shape_map_in l l' r :
  shape_map l l' -> In r l -> exists r', In r' l' /\ rshape r r'.
Proof.
  intros SM. induction SM as [|x x' t t' HS HT IH]; simpl; [tauto|].
  intros [<-|H]; [exists x'; auto|]. destruct (IH H) as (r' & Hr & S). exists r'; auto.
Qed.

Lemma shape_map_bases l l' : shape_map l l' -> map vr_base l' = map vr_base l.
Proof. intros SM; induction SM as [|x x' t t' (HB&_) HT IH]; simpl; congruence. Qed.

(* [comment removed for export] *)
Lemma rgn_upd_shape l r :
  (forall x, In x l -> vr_base x = vr_base r -> rshape x r) ->
  In (vr_base r) (map vr_base l) -> shape_map l (rgn_upd l r).
Proof.
  induction l as [|y t IH]; simpl; [tauto|].
  intros Hs Hin. destruct (Pos.eqb_spec (vr_base y) (vr_base r)).
  - constructor; [apply Hs; auto|apply shape_map_refl].
  - constructor; [apply rshape_refl|]. apply IH; [intros x Hx; apply Hs; auto|].
    destruct Hin as [H|H]; [congruence|exact H].
Qed.

Lemma rgn_upd_in_new l r : In (vr_base r) (map vr_base l) -> In r (rgn_upd l r).
Proof.
  induction l as [|y t IH]; simpl; [tauto|]. destruct (Pos.eqb_spec (vr_base y) (vr_base r)); simpl; [auto|].
  intros [H|H]; [congruence|auto].
Qed.

Lemma rgn_upd_other l r x :
  List.NoDup (map vr_base l) -> In (vr_base r) (map vr_base l) ->
  In x (rgn_upd l r) -> x = r \/ (In x l /\ vr_base x <> vr_base r).
Proof.
  induction l as [|y t IH]; simpl; [tauto|].
  intros ND Hin. apply List.NoDup_cons_iff in ND as [Hy Ht].
  destruct (Pos.eqb_spec (vr_base y) (vr_base r)) as [EQ|NE]; simpl.
  - intros [<-|H]; [auto|]. right. split; [auto|]. intros EB. apply Hy. rewrite EQ, <- EB. apply in_map. exact H.
  - intros [<-|H]; [right; auto|]. destruct Hin as [Hin|Hin]; [congruence|].
    destruct (IH Ht Hin H) as [->|[H1 H2]]; [auto|right; auto].
Qed.

Lemma rgn_upd_keep l r x : In x l -> vr_base x <> vr_base r -> In x (rgn_upd l r).
Proof.
  induction l as [|y t IH]; simpl; [tauto|].
  intros [<-|H] NE; destruct (Pos.eqb_spec (vr_base y) (vr_base r)); simpl; auto; congruence.
Qed.

(* [comment removed for export] *)
Definition havoc1 (b : sym) (r : vregion) : vregion :=
  match vr_kind r with
  | RK_arg => if Pos.eqb (vr_base r) b then r else set_rnul (set_cells r []) []
  | _ => r
  end.

Lemma havoc_other_args_map l b : havoc_other_args l b = map (havoc1 b) l.
Proof. reflexivity. Qed.

Lemma havoc1_shape b r : rshape r (havoc1 b r).
Proof.
  unfold havoc1. destruct (vr_kind r); try apply rshape_refl.
  destruct (Pos.eqb (vr_base r) b); [apply rshape_refl|]. repeat split; reflexivity.
Qed.

Lemma havoc1_cases b r :
  havoc1 b r = r \/ (vr_kind r = RK_arg /\ vr_base r <> b /\ vr_cells (havoc1 b r) = [] /\ vr_nul (havoc1 b r) = []).
Proof.
  unfold havoc1. destruct (vr_kind r) eqn:K; auto.
  destruct (Pos.eqb_spec (vr_base r) b); [auto|right; repeat split; auto].
Qed.

Lemma havoc1_spec b y :
  ((vr_kind y <> RK_arg \/ vr_base y = b) /\ havoc1 b y = y)
  \/ (vr_kind y = RK_arg /\ vr_base y <> b /\ havoc1 b y = set_rnul (set_cells y []) []).
Proof.
  unfold havoc1. destruct (vr_kind y) eqn:K; try (left; split; [left; congruence|reflexivity]).
  destruct (Pos.eqb_spec (vr_base y) b); [left; split; [right; assumption|reflexivity]|right; auto].
Qed.

Lemma havoc_shape l b : shape_map l (havoc_other_args l b).
Proof. rewrite havoc_other_args_map. induction l; constructor; auto using havoc1_shape. Qed.

(* [comment removed for export] *)
Lemma filter_sub {X} (f : X -> bool) l x : In x (List.filter f l) -> In x l /\ f x = true.
Proof. intros H. apply filter_In in H. exact H. Qed.

Lemma nodup_map_filter {X Y} (g : X -> Y) f l : List.NoDup (map g l) -> List.NoDup (map g (List.filter f l)).
Proof.
  induction l as [|x t IH]; simpl; [constructor|]. intros ND. apply List.NoDup_cons_iff in ND as [Hx Ht].
  destruct (f x); simpl; [|exact (IH Ht)]. constructor; [|exact (IH Ht)].
  intros Hin. apply Hx. apply in_map_iff in Hin as (y & Hy & Hin). apply filter_In in Hin as [Hin _].
  rewrite <- Hy. apply in_map. exact Hin.
Qed.

Lemma rgn_get_filter_base l f s r :
  rgn_get (List.filter f l) s = Some r -> In r l /\ vr_base r = s /\ f r = true.
Proof.
  intros H. destruct (rgn_get_in _ _ _ H) as [Hin Hb]. apply filter_In in Hin as [Hin Hf]. auto.
Qed.

Lemma rgn_get_some_nodup l r :
  List.NoDup (map vr_base l) -> In r l -> rgn_get l (vr_base r) = Some r.
Proof.
  induction l as [|y t IH]; simpl; [tauto|]. intros ND [<-|H]; apply List.NoDup_cons_iff in ND as [Hy Ht].
  - rewrite Pos.eqb_refl. reflexivity.
  - destruct (Pos.eqb_spec (vr_base y) (vr_base r)) as [EQ|NE]; [|exact (IH Ht H)].
    exfalso. apply Hy. rewrite EQ. apply in_map. exact H.
Qed.

Lemma rgn_get_filter_keep l f r :
  List.NoDup (map vr_base l) -> In r l -> f r = true -> rgn_get (List.filter f l) (vr_base r) = Some r.
Proof.
  intros ND Hin Hf. apply rgn_get_some_nodup; [apply nodup_map_filter; exact ND|]. apply filter_In. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive rdesc : Type :=
| DSlot (c p : Z)        (* [comment removed for export] *)
| DFlag (c p : Z)        (* [comment removed for export] *)
| DHints                 (* [comment removed for export] *)
| DShStack               (* [comment removed for export] *)
| DShSlot (c p : Z).     (* [comment removed for export] *)

Section Geometry.
  Variables (fs sp0 frame shoff : Z).

  Definition dvalid (d : rdesc) : Prop :=
    match d with
    | DSlot c p | DFlag c p | DShSlot c p => 0 <= c <= 4 /\ 0 <= p < fs_nframes c
    | _ => True
    end.

  Definition dbyte (d : rdesc) (y : Z) : Prop :=
    match d with
    | DSlot c p => frame_addr fs c p <= y < frame_addr fs c p + fake_size c
    | DFlag c p => y = flag_addr fs c p
    | DHints => fs <= y < fs + 88
    | DShStack => shoff + sp0 / 8 - frame / 8 - 8 <= y < shoff + sp0 / 8 + 1
    | DShSlot c p => shoff + frame_addr fs c p / 8 <= y < shoff + frame_addr fs c p / 8 + fake_size c / 8
    end.

  (* [comment removed for export] *)
  Definition layout_ok : Prop :=
    (0 <= fs /\ (fs + FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL <= LOW_MEM_TOP \/ HIGH_MEM_BEG <= fs))
    /\ fs + FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL <= HIGH_MEM_END /\ fs mod 4096 = 0
    /\ (fs + FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL + 4096 <= sp0 - frame \/ sp0 + 4096 <= fs)
    /\ HIGH_MEM_BEG <= sp0 - frame /\ sp0 + 16 <= HIGH_MEM_END /\ 0 <= frame
    /\ shoff = 0x7fff8000.

  Lemma slot_range c p : layout_ok -> 0 <= c <= 4 -> 0 <= p < fs_nframes c ->
    fs + FS_FRAMES <= frame_addr fs c p /\ frame_addr fs c p + fake_size c <= fs + FS_FRAMES + FS_NCLASSES * 2 ^ FS_SSL
    /\ frame_addr fs c p mod 8 = 0 /\ fake_size c mod 8 = 0 /\ 64 <= fake_size c.
  Proof using .
    intros ((L0 & L1) & L2 & L3 & _) Hc Hp.
    destruct (frame_in_class fs c p ltac:(lia) ltac:(lia) Hp) as [A B].
    pose proof (fake_size_bounds c Hc). unfold FS_NCLASSES, FS_SSL.
    assert (0 <= c * 2 ^ 20) by nia. assert ((c + 1) * 2 ^ 20 <= 5 * 2 ^ 20) by nia.
    split; [lia|]. split; [lia|]. split; [|split; [|lia]].
    - pose proof (frame_addr_mod64 fs c p L3 ltac:(lia)) as M.
      apply Z.mod_divide in M; [|lia]. apply Z.mod_divide; [lia|]. destruct M as [k Hk]. exists (k * 8). lia.
    - pose proof (fake_size_mod64 c ltac:(lia)) as M.
      apply Z.mod_divide in M; [|lia]. apply Z.mod_divide; [lia|]. destruct M as [k Hk]. exists (k * 8). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dbyte_side d y : layout_ok -> dvalid d -> dbyte d y ->
    match d with DShStack | DShSlot _ _ => LOW_MEM_TOP <= y < HIGH_MEM_BEG
               | _ => 0 <= y < HIGH_MEM_END /\ (y < LOW_MEM_TOP \/ HIGH_MEM_BEG <= y) end.
  Proof using .
    intros L V B. pose proof L as ((L0 & L1) & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    unfold LOW_MEM_TOP, HIGH_MEM_BEG, HIGH_MEM_END, FS_FRAMES, FS_NCLASSES, FS_SSL in *.
    destruct d as [c p|c p| | |c p]; cbn [dvalid dbyte] in V, B.
    - destruct (slot_range c p L ltac:(lia) ltac:(lia)) as (A1 & A2 & _). unfold FS_FRAMES, FS_NCLASSES, FS_SSL in *. lia.
    - pose proof (flag_addr_range fs c p ltac:(lia) ltac:(lia)). unfold FS_FLAGS, FS_FRAMES in *. lia.
    - lia.
    - pose proof (Z.div_mod sp0 8 ltac:(lia)). pose proof (Z.mod_pos_bound sp0 8 ltac:(lia)).
      pose proof (Z.div_mod frame 8 ltac:(lia)). pose proof (Z.mod_pos_bound frame 8 ltac:(lia)). lia.
    - destruct (slot_range c p L ltac:(lia) ltac:(lia)) as (A1 & A2 & _). unfold FS_FRAMES, FS_NCLASSES, FS_SSL in *.
      pose proof (Z.div_mod (frame_addr fs c p) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (frame_addr fs c p) 8 ltac:(lia)).
      pose proof (Z.div_mod (fake_size c) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (fake_size c) 8 ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dbyte_disjoint d1 d2 y :
    layout_ok -> dvalid d1 -> dvalid d2 -> dbyte d1 y -> dbyte d2 y -> d1 = d2.
  Proof using .
    intros L V1 V2 B1 B2.
    pose proof (dbyte_side d1 y L V1 B1) as S1. pose proof (dbyte_side d2 y L V2 B2) as S2.
    pose proof L as ((L0 & L1) & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    destruct d1 as [c p|c p| | |c p]; destruct d2 as [c' p'|c' p'| | |c' p']; cbn [dvalid dbyte] in V1, V2, B1, B2;
      try (exfalso; lia); try reflexivity.
    - (* [comment removed for export] *)
      destruct (Z.eq_dec c c') as [Ec|Nc]; [destruct (Z.eq_dec p p') as [Ep|Np]; [subst; reflexivity|]|];
        exfalso; (destruct (frames_disjoint fs c p c' p' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); lia).
    - (* [comment removed for export] *) exfalso. destruct (slot_range c p L ltac:(lia) ltac:(lia)) as (A1 & _).
      pose proof (flag_addr_range fs c' p' ltac:(lia) ltac:(lia)). lia.
    - (* [comment removed for export] *) exfalso. destruct (slot_range c p L ltac:(lia) ltac:(lia)) as (A1 & _). unfold FS_FRAMES in *. lia.
    - (* [comment removed for export] *) exfalso. destruct (slot_range c' p' L ltac:(lia) ltac:(lia)) as (A1 & _).
      pose proof (flag_addr_range fs c p ltac:(lia) ltac:(lia)). lia.
    - (* [comment removed for export] *) destruct (flag_addr_inj fs c p c' p' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)); subst; reflexivity.
    - (* [comment removed for export] *) exfalso. pose proof (flag_addr_range fs c p ltac:(lia) ltac:(lia)). unfold FS_FLAGS in *. lia.
    - (* [comment removed for export] *) exfalso. destruct (slot_range c' p' L ltac:(lia) ltac:(lia)) as (A1 & _). unfold FS_FRAMES in *. lia.
    - (* [comment removed for export] *) exfalso. pose proof (flag_addr_range fs c' p' ltac:(lia) ltac:(lia)). unfold FS_FLAGS in *. lia.
    - (* [comment removed for export] *) exfalso. destruct (slot_range c' p' L ltac:(lia) ltac:(lia)) as (A1 & A2 & M1 & M2 & SZ).
      unfold FS_FRAMES, FS_NCLASSES, FS_SSL in *.
      destruct L4 as [L4|L4].
      + (* [comment removed for export] *)
        assert ((frame_addr fs c' p' + fake_size c') / 8 <= (sp0 - frame - 4096) / 8) by (apply Z.div_le_mono; lia).
        assert (frame_addr fs c' p' / 8 + fake_size c' / 8 <= (frame_addr fs c' p' + fake_size c') / 8).
        { apply Z.div_le_lower_bound; [lia|].
          pose proof (Z.div_mod (frame_addr fs c' p') 8 ltac:(lia)). pose proof (Z.div_mod (fake_size c') 8 ltac:(lia)). lia. }
        pose proof (Z.div_mod sp0 8 ltac:(lia)). pose proof (Z.div_mod frame 8 ltac:(lia)).
        pose proof (Z.mod_pos_bound sp0 8 ltac:(lia)). pose proof (Z.mod_pos_bound frame 8 ltac:(lia)).
        pose proof (Z.div_mod (sp0 - frame - 4096) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (sp0 - frame - 4096) 8 ltac:(lia)).
        (ltac2:(LK.k [@B1; @B2; @S2; @L0; @L4; @L5; @L7; @L8; @A1; @SZ; @H; @H0; @H1; @H2; @H3; @H5]); lia).
      + (* [comment removed for export] *)
        assert (sp0 / 8 + 1 <= (fs - 4096) / 8 + 1) by (apply Z.add_le_mono_r; apply Z.div_le_mono; lia).
        assert ((fs - 4096) / 8 + 1 <= frame_addr fs c' p' / 8).
        { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.div_mod (fs - 4096) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (fs - 4096) 8 ltac:(lia)). lia. }
        lia.
    - (* [comment removed for export] *) exfalso. destruct (slot_range c p L ltac:(lia) ltac:(lia)) as (A1 & A2 & M1 & M2 & SZ).
      unfold FS_FRAMES, FS_NCLASSES, FS_SSL in *.
      destruct L4 as [L4|L4].
      + assert ((frame_addr fs c p + fake_size c) / 8 <= (sp0 - frame - 4096) / 8) by (apply Z.div_le_mono; lia).
        assert (frame_addr fs c p / 8 + fake_size c / 8 <= (frame_addr fs c p + fake_size c) / 8).
        { apply Z.div_le_lower_bound; [lia|].
          pose proof (Z.div_mod (frame_addr fs c p) 8 ltac:(lia)). pose proof (Z.div_mod (fake_size c) 8 ltac:(lia)). lia. }
        pose proof (Z.div_mod sp0 8 ltac:(lia)). pose proof (Z.div_mod frame 8 ltac:(lia)).
        pose proof (Z.mod_pos_bound sp0 8 ltac:(lia)). pose proof (Z.mod_pos_bound frame 8 ltac:(lia)).
        pose proof (Z.div_mod (sp0 - frame - 4096) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (sp0 - frame - 4096) 8 ltac:(lia)).
        (ltac2:(LK.k [@B1; @B2; @S2; @L0; @L4; @L5; @L7; @L8; @A1; @SZ; @H; @H0; @H1; @H2; @H3; @H5]); lia).
      + assert (sp0 / 8 + 1 <= (fs - 4096) / 8 + 1) by (apply Z.add_le_mono_r; apply Z.div_le_mono; lia).
        assert ((fs - 4096) / 8 + 1 <= frame_addr fs c p / 8).
        { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.div_mod (fs - 4096) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (fs - 4096) 8 ltac:(lia)). lia. }
        lia.
    - (* [comment removed for export] *)
      destruct (Z.eq_dec c c') as [Ec|Nc]; [destruct (Z.eq_dec p p') as [Ep|Np]; [subst; reflexivity|]|]; exfalso.
      + destruct (slot_range c p L ltac:(lia) ltac:(lia)) as (A1 & A2 & M1 & M2 & SZ).
        destruct (slot_range c' p' L ltac:(lia) ltac:(lia)) as (A1' & A2' & M1' & M2' & SZ').
        destruct (frames_disjoint fs c p c' p' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [D|D].
        * assert ((frame_addr fs c p + fake_size c) / 8 <= frame_addr fs c' p' / 8) by (apply Z.div_le_mono; lia).
          assert (frame_addr fs c p / 8 + fake_size c / 8 <= (frame_addr fs c p + fake_size c) / 8).
          { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.div_mod (frame_addr fs c p) 8 ltac:(lia)). pose proof (Z.div_mod (fake_size c) 8 ltac:(lia)). (ltac2:(LK.k [@B1; @B2; @L0; @M1; @M2; @SZ; @SZ'; @D; @H; @H0; @H1]); lia). }
          (ltac2:(LK.k [@B1; @B2; @L0; @SZ; @SZ'; @H; @H0]); lia).
        * assert ((frame_addr fs c' p' + fake_size c') / 8 <= frame_addr fs c p / 8) by (apply Z.div_le_mono; lia).
          assert (frame_addr fs c' p' / 8 + fake_size c' / 8 <= (frame_addr fs c' p' + fake_size c') / 8).
          { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.div_mod (frame_addr fs c' p') 8 ltac:(lia)). pose proof (Z.div_mod (fake_size c') 8 ltac:(lia)). (ltac2:(LK.k [@B1; @B2; @L0; @SZ; @M1'; @M2'; @SZ'; @D; @H; @H0; @H1]); lia). }
          (ltac2:(LK.k [@B1; @B2; @L0; @SZ; @SZ'; @H; @H0]); lia).
      + destruct (slot_range c p L ltac:(lia) ltac:(lia)) as (A1 & A2 & M1 & M2 & SZ).
        destruct (slot_range c' p' L ltac:(lia) ltac:(lia)) as (A1' & A2' & M1' & M2' & SZ').
        destruct (frames_disjoint fs c p c' p' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [D|D].
        * assert ((frame_addr fs c p + fake_size c) / 8 <= frame_addr fs c' p' / 8) by (apply Z.div_le_mono; lia).
          assert (frame_addr fs c p / 8 + fake_size c / 8 <= (frame_addr fs c p + fake_size c) / 8).
          { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.div_mod (frame_addr fs c p) 8 ltac:(lia)). pose proof (Z.div_mod (fake_size c) 8 ltac:(lia)). (ltac2:(LK.k [@B1; @B2; @L0; @M1; @M2; @SZ; @SZ'; @D; @H; @H0; @H1]); lia). }
          (ltac2:(LK.k [@B1; @B2; @L0; @SZ; @SZ'; @H; @H0]); lia).
        * assert ((frame_addr fs c' p' + fake_size c') / 8 <= frame_addr fs c p / 8) by (apply Z.div_le_mono; lia).
          assert (frame_addr fs c' p' / 8 + fake_size c' / 8 <= (frame_addr fs c' p' + fake_size c') / 8).
          { apply Z.div_le_lower_bound; [lia|]. pose proof (Z.div_mod (frame_addr fs c' p') 8 ltac:(lia)). pose proof (Z.div_mod (fake_size c') 8 ltac:(lia)). (ltac2:(LK.k [@B1; @B2; @L0; @SZ; @M1'; @M2'; @SZ'; @D; @H; @H0; @H1]); lia). }
          (ltac2:(LK.k [@B1; @B2; @L0; @SZ; @SZ'; @H; @H0]); lia).
  Qed.
End Geometry.

(* [comment removed for export] *)
Lemma dbyte_not_flags fs sp0 frame shoff d y :
  layout_ok fs sp0 frame shoff -> dvalid d -> dbyte fs sp0 frame shoff d y ->
  match d with DFlag _ _ => False | _ => True end -> ~ (fs + FS_FLAGS <= y < fs + FS_FRAMES).
Proof.
  intros L V B ND IN. pose proof (dbyte_side fs sp0 frame shoff d y L V B) as S. pose proof L as ((L0 & L1) & L2 & _).
  destruct d as [c p|c p| | |c p]; cbn [dvalid dbyte] in V, B; try contradiction;
    unfold LOW_MEM_TOP, HIGH_MEM_BEG, HIGH_MEM_END, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *.
  - destruct (slot_range fs sp0 frame shoff c p L ltac:(lia) ltac:(lia)) as (A1 & _). unfold FS_FRAMES in A1. lia.
  - lia.
  - lia.
  - lia.
Qed.

(* [comment removed for export] *)
Section C.
  Variable SEGS : list Segment.
  Variable P : vparams2.
  Variable E : venv2.
  Variable mem0 : word -> option byte.
  Let P1 := p1 P.
  Let E1 := ev1 E.
  Hypothesis PO2 : params_ok2 SEGS P.

  Notation gamma2P := (gamma2 SEGS P E mem0).
  Notation FS := (e_fs E).
  Notation SP0v := (e_sp0 (ev1 E)).
  Notation FRAME := (vp_frame (p1 P)).
  Notation SHOFF := (vp_shoff P).
  Notation dbyteP := (dbyte (e_fs E) (e_sp0 (ev1 E)) (vp_frame (p1 P)) (vp_shoff P)).
  Notation layoutP := (layout_ok (e_fs E) (e_sp0 (ev1 E)) (vp_frame (p1 P)) (vp_shoff P)).

  (* [comment removed for export] *)
  Lemma nu_SP8 A nu regs mem : gamma2P A nu regs mem -> nu SP8 = SP0v / 8.
  Proof using .
    intros HG2. pose proof (gamma2_fix _ _ _ _ _ _ _ _ HG2) as F. apply F.
    unfold fix_val2. replace (fix_val (ev1 E) SP8) with (@None Z) by reflexivity. reflexivity.
  Qed.

  Lemma nu_FSB A nu regs mem : gamma2P A nu regs mem -> nu FSB = FS.
  Proof using .
    intros HG2. pose proof (gamma2_fix _ _ _ _ _ _ _ _ HG2) as F. apply F.
    unfold fix_val2. replace (fix_val (ev1 E) FSB) with (@None Z) by reflexivity. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma layout_of_env : env_ok2 P E -> vp_fs P <> None -> layoutP.
  Proof using PO2.
    intros HE Hfs. pose proof HE as (HE1 & _ & HF & _). unfold env_fs in HF.
    destruct (vp_fs P) as [[len ssl]|] eqn:Efs; [|congruence].
    destruct HF as (Hssl & [Hf0 Hob] & Hhi & Hal & Hlen & _ & _ & Hsp & _ & _ & Hspf & _ & _ & Hsp47).
    destruct (PO2_fs _ _ PO2 ltac:(rewrite Efs; discriminate)) as [SH _].
    pose proof (proj1 (PO1 _ _ PO2)) as FR0.
    unfold layout_ok. subst ssl. unfold off_band, FS_NCLASSES, FS_SSL, FS_FRAMES in *.
    repeat split; try lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition desc_matches (A : vstate2) (nu : val) (r : vregion) (d : rdesc) : Prop :=
    match vr_kind r, d with
    | RK_fake c fl, DSlot c' p => c' = c /\ rbase nu r = frame_addr FS c p /\ nu fl = flag_addr FS c p /\ ~ In (c, p) (e_live E)
    | RK_arg, DSlot c p => In (c, p) (e_live E)
    | RK_flag owner, DFlag c p =>
        exists ro fl, rgn_get (vs_rgn A) owner = Some ro /\ vr_kind ro = RK_fake c fl /\ vr_base r = fl
                      /\ rbase nu ro = frame_addr FS c p /\ nu fl = flag_addr FS c p /\ ~ In (c, p) (e_live E)
    | RK_shadow s, DShStack => s = SP0 /\ vr_base r = SP8
    | RK_shadow s, DShSlot c p =>
        exists ro, rgn_get (vs_rgn A) s = Some ro /\ vr_b8 ro = Some (vr_base r) /\
          ((exists fl, vr_kind ro = RK_fake c fl /\ rbase nu ro = frame_addr FS c p /\ ~ In (c, p) (e_live E))
           \/ (vr_kind ro = RK_arg /\ vr_w r = [] /\ In (c, p) (e_live E)))
    | RK_fs, DHints => vr_base r = FSB
    | _, _ => False
    end.

  Lemma live_valid cp : env_ok2 P E -> vp_fs P <> None -> In cp (e_live E) -> 0 <= fst cp <= 4 /\ 0 <= snd cp < fs_nframes (fst cp).
  Proof using .
    intros HE Hfs Hin. pose proof HE as (_ & _ & HF & _). unfold env_fs in HF.
    destruct (vp_fs P) as [[len ssl]|]; [|congruence].
    destruct HF as (_ & _ & _ & _ & _ & HV & _). rewrite Forall_forall in HV. exact (HV cp Hin).
  Qed.

  Lemma div8_exact a : a mod 8 = 0 -> 8 * (a / 8) = a.
  Proof using . intros H. pose proof (Z.div_mod a 8 ltac:(lia)). lia. Qed.

  Lemma region_desc A nu regs mem r :
    gamma2P A nu regs mem -> In r (vs_rgn A) -> is_data_shadow r = false ->
    exists d, dvalid d /\ desc_matches A nu r d /\
              forall o, vr_lo r <= o < vr_hi r -> dbyteP d (rbase nu r + o).
  Proof using PO2.
    intros HG2 Hr ND.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & _).
    pose proof (RGN r Hr) as (RB1 & RB2 & RB3 & RDS & CELLS & PERM & NUL & KIND).
    unfold kind_ok in KIND. unfold desc_matches.
    destruct (vr_kind r) as [cid fl| |owner|s|] eqn:K.
    - (* [comment removed for export] *)
      destruct KIND as (Hfs & Hc & Hlo & Hhi & _ & pos & Hpos & Hbeta & Hfl & _ & Hnl & _).
      exists (DSlot cid pos). split; [cbn; lia|]. split; [repeat split; auto|].
      intros o Ho. cbn [dbyte]. rewrite Hbeta. lia.
    - (* [comment removed for export] *)
      destruct KIND as (Hfs & (cid & pos & Hin & G1 & G2) & _).
      exists (DSlot cid pos). split; [cbn; exact (live_valid _ HE Hfs Hin)|]. split; [exact Hin|].
      intros o Ho. cbn [dbyte]. lia.
    - (* [comment removed for export] *)
      destruct KIND as (Hlo & Hhi & Hdisp & Hcells & ro & cid & fl & Hget & Hk & Hbase).
      destruct (rgn_get_in _ _ _ Hget) as [Hro _].
      pose proof (RGN ro Hro) as (_ & _ & _ & _ & _ & _ & _ & KINDo). unfold kind_ok in KINDo. rewrite Hk in KINDo.
      destruct KINDo as (Hfs & Hc & _ & _ & _ & pos & Hpos & Hbeta & Hfl & _ & Hnl & _).
      exists (DFlag cid pos). split; [cbn; lia|]. split; [exists ro, fl; repeat split; auto|].
      intros o Ho. cbn [dbyte]. unfold rbase. rewrite Hdisp, Hbase, Hfl. lia.
    - (* [comment removed for export] *)
      destruct KIND as (Hfs & Hdisp & HSP & HDATA & HFSB & HOTHER).
      assert (NDATA : s <> DATA).
      { intros ->. unfold is_data_shadow in ND. rewrite K, Pos.eqb_refl in ND. discriminate. }
      destruct (Pos.eq_dec s SP0) as [->|NSP].
      + destruct (HSP eq_refl) as (HB & L1 & L2).
        exists DShStack. split; [exact I|]. split; [auto|].
        intros o Ho. cbn [dbyte]. unfold rbase. rewrite Hdisp, HB, (nu_SP8 _ _ _ _ HG2). unfold P1 in *. lia.
      + destruct (HOTHER NSP NDATA HFSB) as (ro & Hget & Hb8 & M).
        destruct (rgn_get_in _ _ _ Hget) as [Hro Hrob].
        pose proof (RGN ro Hro) as (_ & _ & _ & _ & _ & _ & _ & KINDo). unfold kind_ok in KINDo.
        pose proof (layout_of_env HE Hfs) as L.
        destruct (vr_kind ro) as [cid' fl'| |owner'|s'|] eqn:Ko; try (exfalso; exact M).
        * destruct M as (E8 & L1 & L2).
          destruct KINDo as (_ & Hc & _ & _ & _ & pos & Hpos & Hbeta & Hfl & _ & Hnl & _).
          exists (DShSlot cid' pos). split; [cbn; lia|]. split.
          { exists ro. split; [exact Hget|]. split; [exact Hb8|]. left. exists fl'. auto. }
          intros o Ho. cbn [dbyte]. unfold rbase at 1 2. rewrite Hdisp.
          destruct (slot_range FS SP0v FRAME SHOFF cid' pos L ltac:(lia) Hpos) as (_ & _ & M1 & M2 & SZ).
          rewrite Hbeta in E8. pose proof (div8_exact _ M1). pose proof (div8_exact _ M2).
          assert (nu (vr_base r) = frame_addr FS cid' pos / 8) by (ltac2:(LK.k [@HSP; @HDATA; @HFSB; @HOTHER; @NDATA; @NSP; @E8; @Hrob; @SZ; @H]); lia).
          assert (vr_hi r <= fake_size cid' / 8) by (ltac2:(LK.k [@HSP; @HDATA; @HFSB; @HOTHER; @NDATA; @NSP; @L2; @Hrob; @SZ; @H0]); lia). (ltac2:(LK.k [@HSP; @HDATA; @HFSB; @HOTHER; @NDATA; @NSP; @L1; @L2; @Hrob; @Ho; @SZ; @H; @H0; @H1]); lia).
        * destruct M as (E8 & W0 & cid & pos & Hin & G1 & G2).
          exists (DShSlot cid pos). split; [cbn; exact (live_valid _ HE Hfs Hin)|]. split.
          { exists ro. split; [exact Hget|]. split; [exact Hb8|]. right. auto. }
          intros o Ho. cbn [dbyte]. unfold rbase at 1 2. rewrite Hdisp.
          pose proof (live_valid _ HE Hfs Hin) as [Vc Vp]. cbn in Vc, Vp.
          destruct (slot_range FS SP0v FRAME SHOFF cid pos L Vc Vp) as (_ & _ & M1 & M2 & SZ).
          pose proof (div8_exact _ M1). pose proof (div8_exact _ M2). (ltac2:(LK.k [@HSP; @HDATA; @HFSB; @HOTHER; @NDATA; @NSP; @G1; @G2; @Hrob; @Ho; @SZ; @H; @H0]); lia).
    - (* [comment removed for export] *)
      destruct KIND as (Hfs & HB & Hdisp & Hlo & Hhi).
      exists DHints. split; [exact I|]. split; [exact HB|].
      intros o Ho. cbn [dbyte]. unfold rbase. rewrite Hdisp, HB, (nu_FSB _ _ _ _ HG2). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma desc_writer_unique A nu regs mem r1 r2 d :
    gamma2P A nu regs mem -> In r1 (vs_rgn A) -> In r2 (vs_rgn A) ->
    desc_matches A nu r1 d -> desc_matches A nu r2 d -> vr_w r1 <> [] ->
    r1 = r2 \/ (vr_kind r1 = RK_arg /\ vr_kind r2 = RK_arg).
  Proof using .
    intros HG2 H1 H2 M1 M2 W1.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & _).
    pose proof LIVE as (LV1 & LV2 & LV3 & LV4).
    assert (FF : forall a b, In a (vs_rgn A) -> In b (vs_rgn A) ->
              match vr_kind a with RK_fake _ _ => True | _ => False end ->
              match vr_kind b with RK_fake _ _ => True | _ => False end ->
              rbase nu a = rbase nu b -> a = b).
    { intros a b Ha Hb Ka Kb EQ. destruct (Pos.eq_dec (vr_base a) (vr_base b)) as [EB|NB].
      - exact (live_ok_base_inj nu A a b LIVE Ha Hb EB).
      - exfalso. specialize (LV3 a b Ha Hb). destruct (vr_kind a); try contradiction. destruct (vr_kind b); try contradiction.
        exact (LV3 NB EQ). }
    unfold desc_matches in M1, M2.
    destruct (vr_kind r1) as [c1 f1| |o1|s1|] eqn:K1; destruct d as [c p|c p| | |c p]; try contradiction;
    destruct (vr_kind r2) as [c2 f2| |o2|s2|] eqn:K2; try contradiction.
    - (* [comment removed for export] *)
      destruct M1 as (-> & B1 & _ & _). destruct M2 as (-> & B2 & _ & _).
      left. apply FF; auto; rewrite ?K1, ?K2; auto; congruence.
    - destruct M1 as (-> & _ & _ & N1). exfalso. exact (N1 M2).
    - destruct M2 as (-> & _ & _ & N2). exfalso. exact (N2 M1).
    - right; auto.
    - (* [comment removed for export] *)
      destruct M1 as (ro1 & fl1 & G1 & KO1 & B1 & RB1 & _). destruct M2 as (ro2 & fl2 & G2 & KO2 & B2 & RB2 & _).
      destruct (rgn_get_in _ _ _ G1) as [I1 _]. destruct (rgn_get_in _ _ _ G2) as [I2 _].
      assert (ro1 = ro2) by (apply FF; auto; rewrite ?KO1, ?KO2; auto; congruence). subst ro2.
      rewrite KO1 in KO2. injection KO2 as <-. left. eapply live_ok_base_inj; eauto. congruence.
    - (* [comment removed for export] *) destruct M1 as [_ B1]. destruct M2 as [_ B2]. left. eapply live_ok_base_inj; eauto. congruence.
    - (* [comment removed for export] *)
      destruct M1 as (ro1 & G1 & B81 & D1). destruct M2 as (ro2 & G2 & B82 & D2).
      destruct (rgn_get_in _ _ _ G1) as [I1 _]. destruct (rgn_get_in _ _ _ G2) as [I2 _].
      destruct D1 as [(fl1 & KO1 & RB1 & NL1)|(KO1 & W0 & L1)]; [|exfalso; exact (W1 W0)].
      destruct D2 as [(fl2 & KO2 & RB2 & NL2)|(KO2 & W2 & L2)]; [|exfalso; exact (NL1 L2)].
      assert (ro1 = ro2) by (apply FF; auto; rewrite ?KO1, ?KO2; auto; congruence). subst ro2.
      left. eapply live_ok_base_inj; eauto. congruence.
    - (* [comment removed for export] *) left. eapply live_ok_base_inj; eauto. congruence.
  Qed.

  (* [comment removed for export] *)
  Lemma desc_flag_owner A nu regs mem r1 r2 c p p2 :
    gamma2P A nu regs mem -> In r1 (vs_rgn A) -> In r2 (vs_rgn A) ->
    desc_matches A nu r1 (DFlag c p) -> desc_matches A nu r2 (DSlot c p2) ->
    match vr_kind r2 with RK_fake _ _ => True | _ => False end ->
    flag_addr FS c p = flag_addr FS c p2 -> 0 <= p < fs_nframes c -> 0 <= p2 < fs_nframes c -> 0 <= c <= 4 ->
    exists owner, vr_kind r1 = RK_flag owner /\ owner = vr_base r2.
  Proof using .
    intros HG2 H1 H2 M1 M2 KF EQ Hp Hp2 Hc.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & _).
    destruct (flag_addr_inj FS c p c p2 Hc Hp Hc Hp2 EQ) as [_ <-].
    unfold desc_matches in M1, M2.
    destruct (vr_kind r1) as [c1 f1| |o1|s1|] eqn:K1; try contradiction.
    destruct (vr_kind r2) as [c2 f2| |o2|s2|] eqn:K2; try contradiction.
    destruct M1 as (ro1 & fl1 & G1 & KO1 & B1 & RB1 & _). destruct M2 as (-> & RB2 & _).
    destruct (rgn_get_in _ _ _ G1) as [I1 Hb1].
    exists o1. split; [reflexivity|]. rewrite <- Hb1.
    assert (ro1 = r2); [|congruence].
    destruct (Pos.eq_dec (vr_base ro1) (vr_base r2)) as [EB|NB]; [exact (live_ok_base_inj nu A ro1 r2 LIVE I1 H2 EB)|].
    exfalso. pose proof LIVE as (_ & _ & LV3 & _). specialize (LV3 ro1 r2 I1 H2). rewrite KO1, K2 in LV3.
    apply (LV3 NB). congruence.
  Qed.

  (* [comment removed for export] *)
  Lemma desc_not_live_flag A nu r1 c p :
    desc_matches A nu r1 (DFlag c p) -> ~ In (c, p) (e_live E).
  Proof using .
    unfold desc_matches. destruct (vr_kind r1); try contradiction. intros (ro & fl & _ & _ & _ & _ & _ & N). exact N.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma rw_byte_apart x :
    env_ok2 P E -> in_rw_zones P E x = true ->
    ~ (SP0v - FRAME <= x < SP0v)
    /\ (forall c, In c (vp_fcells P1) -> ~ (fst c <= x < fst c + snd c))
    /\ ~ (e_data E1 <= x < e_data E1 + e_size E1)
    /\ (forall lo hi, In (lo, hi) (vp_pristine P1) -> ~ (lo <= x < hi))
    /\ 0 <= x < 2 ^ 64.
  Proof using .
    intros HE Hx. destruct (in_rw_zones_in _ _ _ Hx) as (z & Hz & Hrw & Hin).
    pose proof HE as (_ & _ & _ & [Zwf Zap] & _).
    destruct (Zwf z Hz) as (Z0 & Z1 & Z2). destruct (Zap z x Hz Hin) as (A1 & A2 & A3 & A4). specialize (A3 Hrw).
    unfold in_zone in Hin. unfold P1, E1. repeat split; auto. lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma wblock_byte mem a bs y :
    0 <= a < 2 ^ 64 -> a + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
    ~ (a <= y < a + Z.of_nat (length bs)) ->
    wbytes mem (wordZ a) bs (wordZ y) = mem (wordZ y).
  Proof using .
    intros Ha Hl Hy Hn. apply wbytes_outside; unfold in_rng; rewrite (u_wordZ a) by lia; [rewrite (u_wordZ y) by lia|]; lia.
  Qed.

  Lemma wblock_rdn mem a bs y n :
    0 <= a < 2 ^ 64 -> a + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= y -> y + Z.of_nat n <= 2 ^ 64 ->
    (y + Z.of_nat n <= a \/ a + Z.of_nat (length bs) <= y) ->
    rdn SEGS (wbytes mem (wordZ a) bs) (wordZ y) n = rdn SEGS mem (wordZ y) n.
  Proof using .
    intros Ha Hl Hy Hn Hd. destruct n as [|n']; [reflexivity|].
    apply rdn_wbytes_out; rewrite ?(u_wordZ a), ?(u_wordZ y); lia.
  Qed.

  Lemma cell_holds_same nu mem mem' c w v :
    rdn SEGS mem' (wordZ c) (Z.to_nat w) = rdn SEGS mem (wordZ c) (Z.to_nat w) ->
    cell_holds SEGS nu mem c w v -> cell_holds SEGS nu mem' c w v.
  Proof using . intros Hr. destruct v as [e|]; cbn [cell_holds]; [|auto]. rewrite Hr. auto. Qed.

  Lemma zone_write_v1 A1 nu regs mem a bs p :
    env_ok2 P E ->
    (forall g w v, In (g, (w, v)) (vs_globs A1) -> exists f, In f (vp_fcells P1) /\ fst f <= g /\ g + w <= fst f + snd f) ->
    gamma SEGS P1 E1 (zpatch P E mem0 mem) A1 nu regs mem ->
    0 <= a < 2 ^ 64 -> a + Z.of_nat (length bs) <= 2 ^ 64 -> 0 < Z.of_nat (length bs) ->
    (forall i, 0 <= i < Z.of_nat (length bs) -> in_rw_zones P E (a + i) = true) ->
    gamma SEGS P1 E1 (zpatch P E mem0 (wbytes mem (wordZ a) bs)) (set_pc A1 p) nu regs (wbytes mem (wordZ a) bs).
  Proof using PO2.
    intros HE GL HG Ha Hl Hlen HZ.
    set (mem' := wbytes mem (wordZ a) bs).
    pose proof HG as (HE1 & HM & HF & HS & HC & HMo & HV & HR & HSl & HGl & HN & HB).
    pose proof (wbytes_grows bs mem (wordZ a)) as GR. fold mem' in GR.
    (* [comment removed for export] *)
    assert (KEEP : forall y, 0 <= y < 2 ^ 64 ->
              (SP0v - FRAME <= y < SP0v \/ (exists c, In c (vp_fcells P1) /\ fst c <= y < fst c + snd c)
               \/ (exists lo hi, In (lo, hi) (vp_pristine P1) /\ lo <= y < hi)) ->
              ~ (a <= y < a + Z.of_nat (length bs))).
    { intros y Hy Hc Hin. specialize (HZ (y - a) ltac:(lia)). replace (a + (y - a)) with y in HZ by lia.
      destruct (rw_byte_apart y HE HZ) as (N1 & N2 & N3 & N4 & _).
      destruct Hc as [Hc|[(c & Hc & Hcy)|(lo & hi & Hp & Hlh)]]; [exact (N1 Hc)|exact (N2 c Hc Hcy)|exact (N4 lo hi Hp Hlh)]. }
    pose proof (PO1 _ _ PO2) as (POfr & POsphi & POsegs & POfc & POwc & POws & POpr & POrom).
    pose proof HE1 as (Esp16 & Esp & Esz & Ed0 & Edpos & Ed63 & Era & Etp & Egp & Esregs & Efrsp).
    assert (SPHI : SP0v < 2 ^ 64) by (unfold P1, E1 in *; lia).
    split; [exact HE1|]. split.
    { (* [comment removed for export] *)
      destruct HM as (MF & MD & MP & MFM). split; [|split; [|split]].
      - intros x Hx. destruct (MF x Hx) as [S1 R1]. split; [eapply store_ok_mono; eauto|eapply rdn1_grows; eauto].
      - intros i Hi. eapply rdn1_grows; eauto.
      - intros lo hi x Hp Hx. destruct (POpr _ _ Hp) as [L0 H0].
        unfold mem'. rewrite wblock_byte; [exact (MP lo hi x Hp Hx)|lia|lia|unfold P1 in *; lia|].
        apply KEEP; [unfold P1 in *; lia|]. right; right. exists lo, hi. auto.
      - split.
        + intros y Hout. unfold zpatch. destruct (in_rw_zones P E (bv_unsigned y)) eqn:ZY; [reflexivity|].
          pose proof (proj1 MFM y Hout) as OLD. unfold zpatch in OLD. rewrite ZY in OLD.
          rewrite <- OLD. rewrite <- (wordZ_u y). unfold mem'. apply wblock_byte; [lia|lia| |].
          * pose proof (u64_range y). unfold wordZ. lia.
          * intros IN. specialize (HZ (bv_unsigned y - a) ltac:(lia)). replace (a + (bv_unsigned y - a)) with (bv_unsigned y) in HZ by lia.
            rewrite HZ in ZY. discriminate.
        + intros y Hy. unfold zpatch in Hy. destruct (in_rw_zones P E (bv_unsigned y)) eqn:ZY; [exact Hy|].
          apply GR. apply (proj2 MFM y). unfold zpatch. rewrite ZY. exact Hy. }
    split; [exact HF|]. split; [exact HS|]. split; [exact HC|]. split; [exact HMo|]. split; [exact HV|].
    split; [|split; [|split; [|split; [|exact HB]]]].
    - intros r' e Hr' Hg. exact (HR r' e Hr' Hg).
    - (* [comment removed for export] *)
      intros off w v Hin. destruct (HSl off w v Hin) as [Hrg Hch]. split; [exact Hrg|].
      eapply cell_holds_same; [|exact Hch]. unfold mem'.
      apply wblock_rdn; try (unfold P1, E1 in *; lia).
      destruct (Z.le_gt_cases (SP0v + off + w) a) as [L|G]; [left; unfold E1 in *; lia|right].
      destruct (Z.le_gt_cases (a + Z.of_nat (length bs)) (SP0v + off)) as [L2|G2]; [unfold E1 in *; lia|exfalso].
      (* [comment removed for export] *)
      destruct (Z.le_gt_cases a (SP0v + off)).
      + apply (KEEP (SP0v + off)); [unfold P1, E1 in *; lia|left; unfold P1, E1 in *; lia|unfold E1 in *; lia].
      + apply (KEEP a); [lia|left; unfold P1, E1 in *; lia|lia].
    - (* [comment removed for export] *)
      intros g w v Hin. destruct (HGl g w v Hin) as [Hrg Hch]. split; [exact Hrg|].
      destruct (GL g w v Hin) as (f & Hf & F1 & F2). destruct (POfc f Hf) as (Q1 & Q2 & _).
      eapply cell_holds_same; [|exact Hch]. unfold mem'.
      apply wblock_rdn; try (unfold P1, E1 in *; lia).
      destruct (Z.le_gt_cases (g + w) a) as [L|G]; [left; lia|right].
      destruct (Z.le_gt_cases (a + Z.of_nat (length bs)) g) as [L2|G2]; [lia|exfalso].
      destruct (Z.le_gt_cases a g).
      + apply (KEEP g); [unfold P1 in *; lia|right; left; exists f; split; [exact Hf|lia]|lia].
      + apply (KEEP a); [lia|right; left; exists f; split; [exact Hf|lia]|lia].
    - (* [comment removed for export] *)
      intros lo hi Hin. destruct (HN lo hi Hin) as (off & b & R1 & R2 & R3 & R4). exists off, b.
      split; [exact R1|]. split; [exact R2|]. split; [|exact R4]. rewrite <- R3. unfold mem'.
      apply wblock_rdn; change (Z.of_nat 1) with 1; try (unfold P1, E1 in *; lia).
      destruct (Z.lt_ge_cases (SP0v + off) a); [left; unfold P1, E1 in *; lia|right].
      destruct (Z.le_gt_cases (a + Z.of_nat (length bs)) (SP0v + off)); [unfold P1, E1 in *; lia|exfalso].
      apply (KEEP (SP0v + off)); [unfold P1, E1 in *; lia|left; unfold P1, E1 in *; lia|lia].
  Qed.

  Lemma wblock_rdn1 mem a bs y :
    0 <= a < 2 ^ 64 -> a + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
    ~ (a <= y < a + Z.of_nat (length bs)) ->
    rdn SEGS (wbytes mem (wordZ a) bs) (wordZ y) 1 = rdn SEGS mem (wordZ y) 1.
  Proof using . intros. apply wblock_rdn; change (Z.of_nat 1) with 1; lia. Qed.

  Lemma MC2_zone_write mem a bs :
    env_ok2 P E -> MC2 SEGS P E mem0 mem ->
    0 <= a < 2 ^ 64 -> a + Z.of_nat (length bs) <= 2 ^ 64 -> 0 < Z.of_nat (length bs) ->
    (forall i, 0 <= i < Z.of_nat (length bs) -> in_rw_zones P E (a + i) = true) ->
    (forall cp y, In cp (e_live E) -> a <= y < a + Z.of_nat (length bs) -> y <> flag_addr FS (fst cp) (snd cp)) ->
    MC2 SEGS P E mem0 (wbytes mem (wordZ a) bs).
  Proof using PO2.
    intros HE (K & Zo & DS & LF & RT & KR) Ha Hl Hlen HZ HLF.
    set (mem' := wbytes mem (wordZ a) bs).
    pose proof (wbytes_grows bs mem (wordZ a)) as GR. fold mem' in GR.
    assert (NRW : forall y, 0 <= y < 2 ^ 64 -> in_rw_zones P E y = false -> ~ (a <= y < a + Z.of_nat (length bs))).
    { intros y Hy Hn Hin. specialize (HZ (y - a) ltac:(lia)). replace (a + (y - a)) with y in HZ by lia. congruence. }
    pose proof HE as (HE1 & HD2 & HF & HZN & [KC KRC]).
    (* [comment removed for export] *)
    assert (APART : forall k w, 0 <= k -> 0 < w -> k + w <= 2 ^ 64 -> (forall x, k <= x < k + w -> in_rw_zones P E x = false) ->
                    k + w <= a \/ a + Z.of_nat (length bs) <= k).
    { intros k w K0 W00 KW NZ.
      destruct (Z.le_gt_cases (k + w) a) as [L|G]; [left; lia|right].
      destruct (Z.le_gt_cases (a + Z.of_nat (length bs)) k) as [L2|G2]; [lia|exfalso].
      destruct (Z.le_gt_cases a k).
      + apply (NRW k); [lia| |lia]. apply NZ. lia.
      + apply (NRW a); [lia| |lia]. apply NZ. lia. }
    assert (RTC : forall k w v, rt_cell SEGS P E mem k w v -> rt_cell SEGS P E mem' k w v).
    { intros k w v (K0 & W0 & KW & RA & RD). split; [exact K0|]. split; [exact W0|]. split; [exact KW|]. split; [exact RA|].
      rewrite <- RD. unfold mem'. apply wblock_rdn; rewrite ?Z2Nat.id by lia; try lia.
      apply APART; [lia|lia|lia|]. intros x Hx. exact (proj1 (RA x Hx)). }
    assert (RTR : forall k w, rt_readable SEGS P E mem k w -> rt_readable SEGS P E mem' k w).
    { intros k w (K0 & KW & RA & RD). split; [exact K0|]. split; [exact KW|]. split; [exact RA|].
      intros i Hi. eapply rdn1_grows; [exact GR|exact (RD i Hi)]. }
    split; [|split; [|split; [|split; [|split]]]].
    - (* [comment removed for export] *)
      intros k w v Hin. destruct (K k w v Hin) as (K0 & W0 & KW & bs0 & Hr & Hv). split; [lia|]. split; [lia|]. split; [lia|].
      exists bs0. split; [|exact Hv]. rewrite <- Hr. unfold mem'. apply wblock_rdn; rewrite ?Z2Nat.id by lia; try lia.
      apply APART; [lia|lia|lia|]. intros x Hx. exact (proj1 (KC (k, (w, v)) x Hin ltac:(cbn; lia))).
    - (* [comment removed for export] *)
      intros z y Hz Hy. destruct (Zo z y Hz Hy) as [[b Hb] Hw]. split; [eapply rdn1_grows; eauto|].
      intros Hrw. eapply store_ok_mono; eauto.
    - (* [comment removed for export] *)
      intros Hal Hfs. destruct (DS Hal Hfs) as (D1 & D2 & D3).
      unfold env_fs in HF. destruct (vp_fs P) as [[len ssl]|] eqn:Efs; [|congruence].
      destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp & Hdat & Hnrw & _).
      destruct (PO2_fs _ _ PO2 ltac:(rewrite Efs; discriminate)) as [SH _].
      pose proof HE1 as (_ & _ & Hsz & _ & Hdpos & _).
      split.
      + intros g Hg. destruct (D1 g Hg) as (k & Hk & K1 & K2). exists k. split; [|auto]. rewrite <- Hk.
        destruct (Hdat ltac:(lia)) as [HD3 HD4]. unfold HIGH_MEM_BEG, HIGH_MEM_END in *.
        unfold shadow_byte in *. unfold mem'.
        pose proof (Z.div_mod (e_data E1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (e_data E1) 8 ltac:(lia)).
        pose proof (Z.div_mod (e_data E1 + e_size E1 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (e_data E1 + e_size E1 - 1) 8 ltac:(lia)).
        unfold E1 in *.
        apply wblock_rdn1; [lia|lia|lia|]. apply NRW; [lia|]. apply Hnrw; lia.
      + split.
        * intros y Hy Hpos. destruct (D2 y Hy Hpos) as [b Hb]. exists b. rewrite <- Hb.
          destruct (Hdat Hpos) as [HD3 HD4]. unfold HIGH_MEM_BEG, HIGH_MEM_END in *. unfold shadow_byte in *.
          pose proof (Z.div_mod (e_data E1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (e_data E1) 8 ltac:(lia)).
          pose proof (Z.div_mod (e_data E1 + e_size E1 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (e_data E1 + e_size E1 - 1) 8 ltac:(lia)).
          pose proof (PO2_shoff _ _ PO2). unfold E1 in *.
          unfold mem'. apply wblock_rdn1; [lia|lia|lia|]. apply NRW; [lia|]. apply Hnrw; lia.
        * intros Hpos y Hy. destruct (D3 Hpos y Hy) as [b Hb]. exists b. rewrite <- Hb.
          destruct (Hdat Hpos) as [HD3 HD4]. unfold HIGH_MEM_BEG, HIGH_MEM_END in *. unfold shadow_byte in *.
          pose proof (Z.div_mod (e_data E1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (e_data E1) 8 ltac:(lia)).
          pose proof (Z.div_mod (e_data E1 + e_size E1 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (e_data E1 + e_size E1 - 1) 8 ltac:(lia)).
          pose proof (Z.div_mod (vp_shoff P + e_data E1 / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (vp_shoff P + e_data E1 / 8) 8 ltac:(lia)).
          pose proof (Z.div_mod (vp_shoff P + (e_data E1 + e_size E1 - 1) / 8) 8 ltac:(lia)).
          pose proof (Z.mod_pos_bound (vp_shoff P + (e_data E1 + e_size E1 - 1) / 8) 8 ltac:(lia)).
          pose proof (PO2_shoff _ _ PO2). unfold E1 in *.
          unfold mem'. apply wblock_rdn1; [(ltac2:(LK.k [@Ha; @Hdpos; @Hl; @SH; @Hpos; @Hy; @HD3; @HD4; @H; @H0; @H1; @H2; @H3; @H4; @H5; @H6]); lia)|(ltac2:(LK.k [@Ha; @Hdpos; @Hl; @SH; @Hpos; @Hy; @HD3; @HD4; @H; @H0; @H1; @H2; @H3; @H4; @H5; @H6]); lia)|(ltac2:(LK.k [@Ha; @Hdpos; @Hl; @SH; @Hpos; @Hy; @HD3; @HD4; @H; @H0; @H1; @H2; @H3; @H4; @H5; @H6]); lia)|]. apply NRW; [(ltac2:(LK.k [@SH; @Hdpos; @Hpos; @Hy; @HD3; @HD4; @H; @H0; @H1; @H2; @H3; @H4; @H5; @H6]); lia)|]. apply Hnrw; (ltac2:(LK.k [@Hal; @Hdpos; @Hpos; @SH; @Hy; @HD3; @H; @H0; @H1; @H2; @H3; @H4; @H5]); lia).
    - (* [comment removed for export] *)
      intros cp Hcp. destruct (LF cp Hcp) as (b & Hb & Hb1). exists b. split; [|exact Hb1]. rewrite <- Hb.
      unfold env_fs in HF. destruct (vp_fs P) as [[len ssl]|] eqn:Efs.
      + destruct HF as (_ & Hlo & Hhi & _ & Hln & HV & _). rewrite Forall_forall in HV. destruct (HV cp Hcp) as [C1 C2].
        pose proof (flag_addr_range FS (fst cp) (snd cp) C1 C2). unfold HIGH_MEM_BEG, HIGH_MEM_END, FS_FLAGS, FS_FRAMES, FS_NCLASSES, FS_SSL in *.
        unfold mem'. apply wblock_rdn1; try lia. intros IN. exact (HLF cp _ Hcp IN eq_refl).
      + destruct HF as [HL _]. rewrite HL in Hcp. destruct Hcp.
    - (* [comment removed for export] *)
      unfold rtctx_ok in RT |- *. destruct (vp_fs P); [|exact I].
      destruct RT as (tsd & ctx & thr & db & beg & C1 & C2 & C3 & C4 & C5 & N5 & C6 & N6 & R7 & C8 & N8 & N8' & C9 & [N9 N9']).
      exists tsd, ctx, thr, db, beg.
      repeat match goal with |- _ /\ _ => split end; auto.
    - (* [comment removed for export] *)
      intros lo hi b Hin. destruct (KR lo hi b Hin) as (L0 & H64 & Hb). split; [lia|]. split; [lia|].
      intros y Hy. destruct (Hb y Hy) as (k & Hk & Hv). exists k. split; [|exact Hv]. rewrite <- Hk.
      unfold mem'. apply wblock_rdn1; try lia. apply NRW; [lia|].
      exact (proj1 (proj2 (KRC (lo, (hi, b)) y Hin ltac:(cbn; lia)))).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma intervals_disjoint c w a len :
    0 < w -> 0 < len -> (forall y, c <= y < c + w -> ~ (a <= y < a + len)) -> c + w <= a \/ a + len <= c.
  Proof using .
    intros Hw Hl H. destruct (Z.lt_ge_cases c a).
    - destruct (Z.le_gt_cases (c + w) a); [left; exact H1|]. exfalso. apply (H a); lia.
    - destruct (Z.le_gt_cases (a + len) c); [right; exact H1|]. exfalso. apply (H c); lia.
  Qed.

  Lemma rbase_shape nu r r' : rshape r r' -> rbase nu r' = rbase nu r.
  Proof using . intros (B & D & _). unfold rbase. rewrite B, D. reflexivity. Qed.

  Lemma region_ok_transport A A' nu mem a bs r r' :
    env_ok2 P E ->
    region_ok SEGS P E nu A mem r ->
    rshape r r' ->
    (* [comment removed for export] *)
    ((vr_cells r' = vr_cells r /\ vr_nul r' = vr_nul r /\
      (is_data_shadow r = false -> forall y, vr_lo r <= y - rbase nu r < vr_hi r -> ~ (a <= y < a + Z.of_nat (length bs))))
     \/ (vr_cells r' = [] /\ vr_nul r' = [])) ->
    0 <= a < 2 ^ 64 -> a + Z.of_nat (length bs) <= 2 ^ 64 -> 0 < Z.of_nat (length bs) ->
    (match vr_kind r with RK_fake _ fl => ~ (a <= nu fl < a + Z.of_nat (length bs)) | _ => True end) ->
    (forall s ro, rgn_get (vs_rgn A) s = Some ro ->
        match vr_kind ro with RK_fake _ _ | RK_arg => True | _ => False end ->
        match vr_kind r with RK_flag o => o = s | RK_shadow s' => s' = s | _ => False end ->
        exists ro', rgn_get (vs_rgn A') s = Some ro' /\ rshape ro ro') ->
    (match vr_kind r with RK_fake _ _ => In (vr_base r) (vs_live A') | _ => True end) ->
    region_ok SEGS P E nu A' (wbytes mem (wordZ a) bs) r'.
  Proof using PO2.
    intros HE ROK SH CN Ha Hl Hlen OUTF GET LIVE'.
    set (mem' := wbytes mem (wordZ a) bs).
    pose proof (wbytes_grows bs mem (wordZ a)) as GR. fold mem' in GR.
    pose proof ROK as (B1 & B2 & B3 & DS & CELLS & PERM & NUL & KIND).
    pose proof SH as (SB & SD & SK & SL & SHI & SW & S8).
    pose proof (rbase_shape nu r r' SH) as RB.
    assert (DSH : is_data_shadow r' = is_data_shadow r) by (unfold is_data_shadow; rewrite SK; reflexivity).
    assert (ISH : is_shadow r' = is_shadow r) by (unfold is_shadow; rewrite SK; reflexivity).
    assert (CSUB : forall c, In c (vr_cells r') -> In c (vr_cells r)).
    { intros c Hc. destruct CN as [(E0 & _ & _)|[E0 _]]; rewrite E0 in Hc; [exact Hc|destruct Hc]. }
    assert (NSUB : forall c, In c (vr_nul r') -> In c (vr_nul r)).
    { intros c Hc. destruct CN as [(_ & E0 & _)|[_ E0]]; rewrite E0 in Hc; [exact Hc|destruct Hc]. }
    (* [comment removed for export] *)
    assert (OUT : (vr_cells r' <> [] \/ vr_nul r' <> []) -> is_data_shadow r = false ->
             forall y, vr_lo r <= y - rbase nu r < vr_hi r -> ~ (a <= y < a + Z.of_nat (length bs))).
    { intros NE. destruct CN as [(_ & _ & O)|[C0 N0]]; [exact O|]. exfalso. destruct NE as [NE|NE]; apply NE; assumption. }
    (* [comment removed for export] *)
    assert (EXT1 : (vr_cells r' <> [] \/ vr_nul r' <> []) -> is_data_shadow r = false -> forall o, vr_lo r <= o < vr_hi r ->
              rdn SEGS mem' (wordZ (rbase nu r + o)) 1 = rdn SEGS mem (wordZ (rbase nu r + o)) 1).
    { intros NE ND o Ho. unfold mem'. apply wblock_rdn1; [lia|lia|lia|]. apply (OUT NE ND). lia. }
    assert (NEC : forall c, In c (vr_cells r') -> vr_cells r' <> [] \/ vr_nul r' <> []).
    { intros c Hc. left. intros E0. rewrite E0 in Hc. destruct Hc. }
    assert (NEN : forall c, In c (vr_nul r') -> vr_cells r' <> [] \/ vr_nul r' <> []).
    { intros c Hc. right. intros E0. rewrite E0 in Hc. destruct Hc. }
    unfold region_ok, region_cells_ok, region_perm_ok, region_nul_ok. rewrite !RB, !SL, !SHI, !DSH, !SW, !ISH.
    split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split.
    { intros HD. destruct (DS HD) as (C0 & W0 & N0). split; [|split; [exact W0|]].
      - destruct CN as [(-> & _ & _)|[-> _]]; [exact C0|reflexivity].
      - destruct CN as [(_ & -> & _)|[_ ->]]; [exact N0|reflexivity]. }
    split; [|split; [|split]].
    - (* [comment removed for export] *)
      intros off w v Hin. destruct (CELLS off w v (CSUB _ Hin)) as (L1 & L2 & L3 & RC).
      split; [lia|]. split; [lia|]. split; [lia|].
      destruct (is_data_shadow r) eqn:ND.
      { destruct (DS eq_refl) as [C0 _]. pose proof (CSUB _ Hin) as X. rewrite C0 in X. destruct X. }
      unfold rcell_holds in *. destruct v as [e|]; [|exact I].
      destruct (is_shadow r && lin_is_const e).
      + intros i Hi. destruct (RC i Hi) as (k & Hk & Hb). exists k. split; [|exact Hb].
        replace (rbase nu r + off + i) with (rbase nu r + (off + i)) by lia. rewrite (EXT1 (NEC _ Hin) eq_refl) by lia.
        replace (rbase nu r + (off + i)) with (rbase nu r + off + i) by lia. exact Hk.
      + eapply cell_holds_same; [|exact RC]. unfold mem'. apply wblock_rdn; rewrite ?Z2Nat.id by lia; try lia.
        apply intervals_disjoint; [lia|lia|]. intros y Hy. apply (OUT (NEC _ Hin) eq_refl). lia.
    - (* [comment removed for export] *)
      intros ND. destruct (PERM ND) as [RD WR]. split.
      + intros off Hoff. destruct (RD off Hoff) as [Z1 [b Hb]]. split; [exact Z1|]. eapply rdn1_grows; eauto.
      + intros lo hi off Hlh Hoff. destruct (WR lo hi off Hlh Hoff) as (W1 & W2 & W3 & W4).
        split; [exact W1|]. split; [exact W2|]. split; [eapply store_ok_mono; eauto|exact W4].
    - (* [comment removed for export] *)
      intros lo hi Hin. destruct (NUL lo hi (NSUB _ Hin)) as (off & b & R1 & R2 & R3 & R4).
      exists off, b. split; [exact R1|]. split; [exact R2|]. split; [|exact R4].
      destruct (is_data_shadow r) eqn:ND.
      { destruct (DS eq_refl) as (_ & _ & N0). pose proof (NSUB _ Hin) as X. rewrite N0 in X. destruct X. }
      rewrite (EXT1 (NEN _ Hin) eq_refl) by lia. exact R3.
    - (* [comment removed for export] *)
      unfold kind_ok in KIND |- *. rewrite SK, RB, SB, SD, SL, SHI, SW.
      destruct (vr_kind r) as [cid fl| |owner|sbase|] eqn:K.
      + destruct KIND as (F1 & F2 & F3 & F4 & F5 & pos & Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
        split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
        exists pos. split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [|split; [exact Q5|exact LIVE']].
        destruct Q4 as (b & Hb & Hb1). exists b. split; [|exact Hb1]. rewrite <- Hb. unfold mem'.
        apply wblock_rdn1; [lia|lia| |exact OUTF].
        destruct (vp_fs P) as [[len ssl]|] eqn:Efs; [|exfalso; exact (F1 eq_refl)].
        destruct (flag_byte_outside _ _ _ PO2 len ssl cid pos HE Efs F2 Q1) as [_ R]. rewrite Q3.
        pose proof HE as (_ & _ & HF & _). unfold env_fs in HF. rewrite Efs in HF. destruct HF as (_ & Hlo & Hhi & _).
        unfold HIGH_MEM_BEG, HIGH_MEM_END in *. lia.
      + destruct KIND as (F1 & F2 & i & Hi & Hb & HW). split; [exact F1|]. split; [exact F2|].
        exists i. split; [exact Hi|]. split; [exact Hb|]. exact HW.
      + destruct KIND as (F1 & F2 & F3 & F4 & ro & cid & fl & G & KO & HB).
        split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split.
        { destruct CN as [(-> & _ & _)|[-> _]]; [exact F4|reflexivity]. }
        destruct (GET _ _ G ltac:(rewrite KO; exact I) eq_refl) as (ro' & G' & SH'). exists ro', cid, fl. split; [exact G'|].
        destruct SH' as (_ & _ & SK' & _). rewrite SK'. auto.
      + destruct KIND as (F1 & F2 & F3 & F4 & F5 & F6).
        split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
        intros N1 N2 N3. destruct (F6 N1 N2 N3) as (ro & G & B8 & M).
        destruct (GET _ _ G ltac:(destruct (vr_kind ro); auto) eq_refl) as (ro' & G' & SH'). exists ro'. split; [exact G'|].
        pose proof SH' as (SB' & SD' & SK' & SL' & SHI' & SW' & S8'). rewrite S8', SK', (rbase_shape nu ro ro' SH').
        split; [exact B8|]. exact M.
      + exact KIND.
  Qed.

  (* [comment removed for export] *)
  Lemma region_ok_self A A' nu mem mem' r r' :
    env_ok2 P E ->
    region_ok SEGS P E nu A mem r ->
    rshape r r' -> is_data_shadow r = false ->
    mem_grows mem mem' ->
    (match vr_kind r with RK_fake _ fl => rdn SEGS mem' (wordZ (nu fl)) 1 = rdn SEGS mem (wordZ (nu fl)) 1 | _ => True end) ->
    (forall s ro, rgn_get (vs_rgn A) s = Some ro ->
        match vr_kind ro with RK_fake _ _ | RK_arg => True | _ => False end ->
        match vr_kind r with RK_flag o => o = s | RK_shadow s' => s' = s | _ => False end ->
        exists ro', rgn_get (vs_rgn A') s = Some ro' /\ rshape ro ro') ->
    (match vr_kind r with RK_fake _ _ => In (vr_base r) (vs_live A') | _ => True end) ->
    (match vr_kind r with RK_flag _ => vr_cells r' = [] | _ => True end) ->
    (forall off w v, In (off, (w, v)) (vr_cells r') ->
        vr_lo r <= off /\ 0 < w /\ off + w <= vr_hi r /\ rcell_holds SEGS (is_shadow r) nu mem' (rbase nu r + off) w v) ->
    (forall lo hi, In (lo, hi) (vr_nul r') ->
        exists off b, lo <= off <= hi /\ vr_lo r <= off < vr_hi r /\
                      rdn SEGS mem' (wordZ (rbase nu r + off)) 1 = Some [b] /\ bv_unsigned b = 0) ->
    region_ok SEGS P E nu A' mem' r'.
  Proof using .
    intros HE ROK SH ND GR FLG GET LIVE' FLC HCELLS HNUL.
    pose proof ROK as (B1 & B2 & B3 & DS & CELLS & PERM & NUL & KIND).
    pose proof SH as (SB & SD & SK & SL & SHI & SW & S8).
    pose proof (rbase_shape nu r r' SH) as RB.
    assert (DSH : is_data_shadow r' = is_data_shadow r) by (unfold is_data_shadow; rewrite SK; reflexivity).
    assert (ISH : is_shadow r' = is_shadow r) by (unfold is_shadow; rewrite SK; reflexivity).
    unfold region_ok, region_cells_ok, region_perm_ok, region_nul_ok. rewrite !RB, !SL, !SHI, !DSH, !SW, !ISH.
    split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [rewrite ND; intros; discriminate|].
    split; [exact HCELLS|]. split; [|split; [exact HNUL|]].
    - intros _. destruct (PERM ND) as [RD WR]. split.
      + intros off Hoff. destruct (RD off Hoff) as [Z1 [b Hb]]. split; [exact Z1|]. eapply rdn1_grows; eauto.
      + intros lo hi off Hlh Hoff. destruct (WR lo hi off Hlh Hoff) as (W1 & W2 & W3 & W4).
        split; [exact W1|]. split; [exact W2|]. split; [eapply store_ok_mono; eauto|exact W4].
    - unfold kind_ok in KIND |- *. rewrite SK, RB, SB, SD, SL, SHI, SW.
      destruct (vr_kind r) as [cid fl| |owner|sbase|] eqn:K.
      + destruct KIND as (F1 & F2 & F3 & F4 & F5 & pos & Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
        split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
        exists pos. split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [|split; [exact Q5|exact LIVE']].
        destruct Q4 as (b & Hb & Hb1). exists b. split; [|exact Hb1]. rewrite FLG. exact Hb.
      + destruct KIND as (F1 & F2 & i & Hi & Hb & HW). split; [exact F1|]. split; [exact F2|].
        exists i. split; [exact Hi|]. split; [exact Hb|]. exact HW.
      + destruct KIND as (F1 & F2 & F3 & F4 & ro & cid & fl & G & KO & HB).
        split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact FLC|].
        destruct (GET _ _ G ltac:(rewrite KO; exact I) eq_refl) as (ro' & G' & SH'). exists ro', cid, fl. split; [exact G'|].
        destruct SH' as (_ & _ & SK' & _). rewrite SK'. auto.
      + destruct KIND as (F1 & F2 & F3 & F4 & F5 & F6).
        split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
        intros N1 N2 N3. destruct (F6 N1 N2 N3) as (ro & G & B8 & M).
        destruct (GET _ _ G ltac:(destruct (vr_kind ro); auto) eq_refl) as (ro' & G' & SH'). exists ro'. split; [exact G'|].
        pose proof SH' as (SB' & SD' & SK' & SL' & SHI' & SW' & S8'). rewrite S8', SK', (rbase_shape nu ro ro' SH').
        split; [exact B8|]. exact M.
      + exact KIND.
  Qed.

  (* [comment removed for export] *)
  Lemma kept_cell nu mem a bs r off w v sh :
    0 <= a < 2 ^ 64 -> a + Z.of_nat (length bs) <= 2 ^ 64 -> 0 < Z.of_nat (length bs) ->
    0 <= rbase nu r + off -> rbase nu r + off + w <= 2 ^ 64 -> 0 < w ->
    (rbase nu r + off + w <= a \/ a + Z.of_nat (length bs) <= rbase nu r + off) ->
    rcell_holds SEGS sh nu mem (rbase nu r + off) w v ->
    rcell_holds SEGS sh nu (wbytes mem (wordZ a) bs) (rbase nu r + off) w v.
  Proof using .
    intros Ha Hl Hlen P0 P2 Pw DISJ RC. unfold rcell_holds in *. destruct v as [e|]; [|exact I].
    destruct (sh && lin_is_const e).
    - intros i Hi. destruct (RC i Hi) as (k & Hk & Hb). exists k. split; [|exact Hb]. rewrite <- Hk.
      apply wblock_rdn1; lia.
    - eapply cell_holds_same; [|exact RC]. apply wblock_rdn; rewrite ?Z2Nat.id by lia; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma nth_Z_to_le_bytes j : forall k z d, (j < k)%nat ->
    nth j (Z_to_le_bytes k z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat j)).
  Proof using .
    induction j as [|j IH]; intros k z d Hj.
    - destruct k; [lia|]. cbn [Z_to_le_bytes nth]. rewrite Z.shiftr_0_r. reflexivity.
    - destruct k as [|k]; [lia|]. cbn [Z_to_le_bytes nth]. rewrite IH by lia.
      rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
  Qed.

  Lemma block_byte mem a k (wv : word) j :
    0 <= a -> a + Z.of_nat k <= 2 ^ 64 -> (j < k)%nat ->
    rdn SEGS (wbytes mem (wordZ a) (word_to_le_bytes k wv)) (wordZ (a + Z.of_nat j)) 1
      = Some [Z_to_bv 8 (Z.shiftr (bv_unsigned wv) (8 * Z.of_nat j))]
    /\ bv_unsigned (Z_to_bv 8 (Z.shiftr (bv_unsigned wv) (8 * Z.of_nat j))) = Z.land (Z.shiftr (bv_unsigned wv) (8 * Z.of_nat j)) 255.
  Proof using mem0.
    intros Ha Hl Hj. split.
    - rewrite (rdn_wbytes_byte SEGS mem a (word_to_le_bytes k wv) j); rewrite ?length_N_to_le_bytes; try lia.
      unfold word_to_le_bytes. rewrite nth_Z_to_le_bytes by lia. reflexivity.
    - rewrite Z_to_bv_unsigned, bv_wrap8_mod.
      rewrite <- Z.land_ones by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma live_ok_shape A X l2 nu dd mm :
    live_ok nu A -> shape_map (vs_rgn A) l2 -> live_ok nu (mkVS2 X l2 (vs_live A) dd mm).
  Proof using .
    intros (LV1 & LV2 & LV3 & LV4) SM. cbn [vs_rgn vs_live]. split; [|split; [exact LV2|split]].
    - intros s. rewrite LV1. split.
      + intros (r & Hr & Hb & K). destruct (shape_map_in _ _ _ SM Hr) as (r' & Hr' & SH).
        pose proof SH as (SB & _ & SK & _). exists r'. rewrite SB, SK. auto.
      + intros (r' & Hr' & Hb & K). destruct (shape_map_in_back _ _ _ SM Hr') as (r & Hr & SH).
        pose proof SH as (SB & _ & SK & _). exists r. rewrite <- SB, <- SK. auto.
    - intros r1' r2' H1 H2.
      destruct (shape_map_in_back _ _ _ SM H1) as (r1 & Hr1 & SH1). destruct (shape_map_in_back _ _ _ SM H2) as (r2 & Hr2 & SH2).
      pose proof SH1 as (SB1 & _ & SK1 & _). pose proof SH2 as (SB2 & _ & SK2 & _).
      rewrite SK1, SK2, SB1, SB2, (rbase_shape nu _ _ SH1), (rbase_shape nu _ _ SH2). exact (LV3 r1 r2 Hr1 Hr2).
    - rewrite <- (shape_map_bases _ _ SM) in LV4. exact LV4.
  Qed.

  Lemma own_flags_shape A X l2 nu lv dd mm :
    shape_map (vs_rgn A) l2 -> own_flags (mkVS2 X l2 lv dd mm) nu = own_flags A nu.
  Proof using .
    unfold own_flags. cbn [vs_rgn]. intros SM. induction SM as [|x x' t t' (SB & _ & SK & _) HT IH]; [reflexivity|].
    cbn [flat_map]. rewrite SK, IH. reflexivity.
  Qed.

  Lemma state_below2_shape A l2 pc mm :
    state_below2 A -> shape_map (vs_rgn A) l2 ->
    (forall r', In r' l2 -> cells_syms_below (vr_cells r') (vs_next (v1 A))) ->
    incl mm (vs_memo A) ->
    state_below2 (mkVS2 (set_pc (v1 A) pc) l2 (vs_live A) (vs_divdef A) mm).
  Proof using .
    intros (BF & BR & BL & BD & BM) SM CB IM. cbn [v1 vs_rgn vs_live vs_divdef vs_memo].
    replace (vs_next (set_pc (v1 A) pc)) with (vs_next (v1 A)) by reflexivity.
    split; [exact BF|]. split; [|split; [exact BL|split; [exact BD|intros a n v Hin; exact (BM a n v (IM _ Hin))]]].
    intros r' Hr'. destruct (shape_map_in_back _ _ _ SM Hr') as (r & Hr & SH). pose proof SH as (SB & _ & SK & _).
    destruct (BR r Hr) as (X1 & X2 & X3). rewrite SB, SK. split; [exact X1|]. split; [exact (CB r' Hr')|exact X3].
  Qed.

  (* [comment removed for export] *)
  Lemma covered_not_outside l x : covered l x 1 -> 0 <= x < 2 ^ 64 -> ~ outside (wordZ x) l.
  Proof using mem0.
    intros (b & m & Hin & H1 & H2) Hx. induction l as [|[b' m'] t IH]; [destruct Hin|].
    cbn [outside]. intros [O1 O2]. destruct Hin as [Hin|Hin]; [|exact (IH Hin O2)].
    injection Hin as -> ->. apply O1. unfold in_rng. rewrite u_wordZ by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma store_machine A nu regs mem pc rom w sz (rs1 rs2 : reg) (imm : bv 12) addr a :
    gamma2P A nu regs mem ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Store sz rs1 rs2 imm, 4) ->
    addr_of (v1 A) (rz rs1) (bv_signed imm) = Some addr -> eval nu addr = a -> 0 <= a -> a + msize_z sz <= 2 ^ 64 ->
    (forall i, 0 <= i < msize_z sz -> store_ok SEGS mem (wordZ (a + i)) 1 = true) ->
    RiscvSemantics.step SEGS (mkst regs pc mem rom) =
    MachineOk (mkst regs (v_addi pc 4) (wbytes mem (wordZ a) (word_to_le_bytes (Z.to_nat (msize_z sz)) (getr regs rs2))) rom).
  Proof using .
    intros HG2 Hf He Hd Ha Ea H0 H1 HS.
    destruct (addr_of_sound SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem rs1 (bv_signed imm) addr (proj1 HG2) Ha) as [Ba Hva].
    assert (EW : v_addi (getr regs rs1) (bv_signed imm) = wordZ a).
    { apply bv_eq. rewrite Hva, Ea. unfold wordZ. rewrite u_Z_to_bv64. reflexivity. }
    rewrite <- EW. eapply step_store_any; [eassumption|eassumption|eassumption|]. rewrite EW. pose proof (msize_pos sz).
    apply store_ok_bytes; rewrite ?Z2Nat.id; try lia. intros k Hk. apply HS. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma asan_of_rw x : in_rw_zones P E x = true -> vp_fs P <> None.
  Proof using PO2.
    intros Hx Hn. pose proof (PO2_nozones _ _ PO2 Hn) as Z0.
    unfold in_rw_zones, rw_zones in Hx. rewrite Z0 in Hx. cbn in Hx. discriminate.
  Qed.

  Lemma rgn_store_sound A nu regs mem pc rom w sz (rs1 rs2 : reg) (imm : bv 12) addr r off lo hi l2 :
    gamma2P A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Store sz rs1 rs2 imm, 4) ->
    addr_of (v1 A) (rz rs1) (bv_signed imm) = Some addr ->
    In r (vs_rgn A) -> is_data_shadow r = false ->
    match vr_kind r with RK_flag _ => False | _ => True end ->
    eval nu addr = rbase nu r + eval nu off -> lo <= eval nu off <= hi ->
    in_ranges (vr_w r) lo (hi - lo + msize_z sz) = true ->
    let n := msize_z sz in
    let a := rbase nu r + eval nu off in
    let mem' := wbytes mem (wordZ a) (word_to_le_bytes (Z.to_nat n) (getr regs rs2)) in
    let A' := mkVS2 (set_pc (v1 A) (npc_of (v1 A))) l2 (vs_live A) (vs_divdef A) [] in
    shape_map (vs_rgn A) l2 ->
    (forall r2', In r2' l2 -> vr_base r2' <> vr_base r ->
        exists r2, In r2 (vs_rgn A) /\ rshape r2 r2' /\
          ((vr_cells r2' = vr_cells r2 /\ vr_nul r2' = vr_nul r2 /\ ~ (vr_kind r = RK_arg /\ vr_kind r2 = RK_arg))
           \/ (vr_cells r2' = [] /\ vr_nul r2' = []))) ->
    (forall r', In r' l2 -> vr_base r' = vr_base r ->
        region_ok SEGS P E nu A' mem' r' /\ cells_syms_below (vr_cells r') (vs_next (v1 A))) ->
    step_post2 SEGS P E mem0 A nu [A'] regs mem pc rom.
  Proof using PO2.
    intros HG2 Hpc Hf He Hd Ha Hr ND KNF Eaddr Hlohi HW n a mem' A' SM OTHER SELF.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & _).
    pose proof (RGN r Hr) as (RB1 & RB2 & RB3 & RDS & CELLS & PERM & NUL & KIND).
    pose proof (msize_pos sz) as Hn.
    set (k := Z.to_nat n) in *. set (wv := getr regs rs2) in *.
    assert (Hlen : length (word_to_le_bytes k wv) = k) by apply length_N_to_le_bytes.
    assert (Hkn : Z.of_nat k = n) by (unfold k; lia).
    (* [comment removed for export] *)
    apply in_ranges_sound in HW as (wlo & whi & HWin & W1 & W2).
    destruct (PERM ND) as [RD WR].
    assert (WB : forall i, 0 <= i < n ->
              vr_lo r <= eval nu off + i < vr_hi r
              /\ in_rw_zones P E (a + i) = true
              /\ store_ok SEGS mem (wordZ (a + i)) 1 = true
              /\ covered (unit_regions2 P E) (a + i) 1).
    { intros i Hi. destruct (WR wlo whi (eval nu off + i) HWin ltac:(lia)) as (X1 & X2 & X3 & X4).
      unfold a. rewrite <- Z.add_assoc. auto. }
    assert (Hab : 0 <= a < 2 ^ 64 /\ a + n <= 2 ^ 64).
    { destruct (WB 0 ltac:(lia)) as (X1 & _). destruct (WB (n - 1) ltac:(lia)) as (Y1 & _). unfold a. lia. }
    assert (FSnz : vp_fs P <> None) by (destruct (WB 0 ltac:(lia)) as (_ & X2 & _); exact (asan_of_rw _ X2)).
    pose proof (layout_of_env HE FSnz) as L.
    (* [comment removed for export] *)
    destruct (region_desc A nu regs mem r HG2 Hr ND) as (d1 & V1 & M1 & D1).
    assert (DB : forall y, a <= y < a + n -> dbyteP d1 y).
    { intros y Hy. destruct (WB (y - a) ltac:(lia)) as (X1 & _).
      replace y with (rbase nu r + (eval nu off + (y - a))) by (unfold a; lia). apply D1. exact X1. }
    assert (D1NF : match d1 with DFlag _ _ => False | _ => True end).
    { unfold desc_matches in M1. destruct (vr_kind r); destruct d1; auto. }
    assert (WNE : vr_w r <> []) by (intros W0; rewrite W0 in HWin; destruct HWin).
    (* [comment removed for export] *)
    pose proof (store_machine A nu regs mem pc rom w sz rs1 rs2 imm addr a HG2 Hf He Hd Ha
                  ltac:(unfold a; lia) ltac:(lia) ltac:(lia) ltac:(intros i Hi; exact (proj1 (proj2 (proj2 (WB i Hi)))))) as ST.
    fold k wv in ST. change (wbytes mem (wordZ a) (word_to_le_bytes k wv)) with mem' in ST.
    exists regs, (v_addi pc 4), mem', A', nu.
    split; [exact ST|]. split; [left; reflexivity|]. split.
    { unfold A', vs2_pc. cbn [v1]. unfold npc_of, v_addi. rewrite u_Z_to_bv64, wrap64_zwrap. unfold vs2_pc in Hpc. rewrite Hpc. reflexivity. }
    split; [apply ext_refl|]. split; [unfold A', vs2_next; cbn [v1]; apply Pos.le_refl|].
    assert (HlenZ : Z.of_nat (length (word_to_le_bytes k wv)) = n) by (rewrite Hlen; exact Hkn).
    split.
    { (* [comment removed for export] *)
      split; [|apply wbytes_grows]. intros z Hout. rewrite <- (wordZ_u z). unfold mem'.
      pose proof (u64_range z).
      apply wblock_byte; rewrite ?HlenZ; try lia. intros IN.
      destruct (WB (bv_unsigned z - a) ltac:(lia)) as (_ & _ & _ & COV).
      replace (a + (bv_unsigned z - a)) with (bv_unsigned z) in COV by lia.
      apply (covered_not_outside _ _ COV ltac:(lia)). rewrite wordZ_u. exact Hout. }
    assert (FSTEP : flags_step P E A A' nu nu mem mem').
    { (* [comment removed for export] *)
      intros y Hy. left. split; [unfold A'; rewrite (own_flags_shape A _ l2 nu (vs_live A) (vs_divdef A) [] SM); tauto|].
      unfold in_flags_zone in Hy. destruct (vp_fs P) as [[len ssl]|] eqn:Efs; [|destruct Hy].
      unfold mem'. pose proof L as (L1 & L2 & _). unfold HIGH_MEM_BEG, HIGH_MEM_END, FS_FRAMES, FS_NCLASSES, FS_SSL, FS_FLAGS in *.
      apply wblock_byte; rewrite ?HlenZ; try lia. intros IN.
      apply (dbyte_not_flags FS SP0v FRAME SHOFF d1 y L V1 (DB y IN) D1NF). unfold FS_FLAGS, FS_FRAMES. lia. }
    split; [exact FSTEP|].
    (* [comment removed for export] *)
    split.
    { (* [comment removed for export] *)
      unfold A'. cbn [v1]. unfold mem'. apply zone_write_v1; rewrite ?HlenZ; try lia; [exact HE| |exact HG1|].
      - intros g gw gv Hin. apply (GL2 ltac:(unfold asan_mode; destruct (vp_fs P); [reflexivity|exfalso; exact (FSnz eq_refl)]) g gw gv Hin).
      - intros i Hi. exact (proj1 (proj2 (WB i Hi))). }
    split; [exact HE|]. split.
    { unfold mem'. apply MC2_zone_write; rewrite ?HlenZ; try lia; [exact HE|exact HM| |].
      - intros i Hi. exact (proj1 (proj2 (WB i Hi))).
      - intros [c p] y Hcp Hy EQ. pose proof (live_valid _ HE FSnz Hcp) as [Vc Vp]. cbn in Vc, Vp, EQ.
        assert (d1 = DFlag c p).
        { apply (dbyte_disjoint FS SP0v FRAME SHOFF d1 (DFlag c p) y L V1 ltac:(cbn; lia) (DB y Hy)). cbn. exact EQ. }
        subst d1. exact (desc_not_live_flag A nu r _ _ M1 Hcp). }
    split; [exact HF2|]. split; [exact HDD|]. split.
    { (* [comment removed for export] *)
      intros r' Hr'. destruct (Pos.eq_dec (vr_base r') (vr_base r)) as [EB|NB]; [exact (proj1 (SELF r' Hr' EB))|].
      destruct (OTHER r' Hr' NB) as (r2 & Hr2 & SH2 & CN).
      pose proof SH2 as (SB2 & _ & SK2 & _).
      unfold mem'. apply (region_ok_transport A A' nu mem a _ r2 r' HE (RGN r2 Hr2) SH2); rewrite ?HlenZ; try lia.
      - destruct CN as [(C1 & C2 & NAA)|[C1 C2]]; [left|right; auto]. split; [exact C1|]. split; [exact C2|].
        intros ND2 y Hy IN.
        destruct (region_desc A nu regs mem r2 HG2 Hr2 ND2) as (d2 & V2 & M2 & D2).
        assert (B2y : dbyteP d2 y).
        { replace y with (rbase nu r2 + (y - rbase nu r2)) by lia. apply D2. lia. }
        pose proof (dbyte_disjoint FS SP0v FRAME SHOFF d1 d2 y L V1 V2 (DB y IN) B2y) as <-.
        destruct (desc_writer_unique A nu regs mem r r2 d1 HG2 Hr Hr2 M1 M2 WNE) as [<-|AA]; [|exact (NAA AA)].
        apply NB. exact SB2.
      - destruct (vr_kind r2) as [c2 fl2| | | |] eqn:K2; auto. intros IN.
        destruct (region_desc A nu regs mem r2 HG2 Hr2 ltac:(unfold is_data_shadow; rewrite K2; reflexivity)) as (d2 & V2 & M2 & D2).
        unfold desc_matches in M2. rewrite K2 in M2. destruct d2 as [c p| | | |]; try contradiction.
        destruct M2 as (Ec & RBf & FLf & NLf). cbn in V2. subst c.
        assert (d1 = DFlag c2 p).
        { apply (dbyte_disjoint FS SP0v FRAME SHOFF d1 (DFlag c2 p) (nu fl2) L V1 ltac:(cbn; lia) (DB _ IN)). cbn. exact FLf. }
        subst d1. exact D1NF.
      - intros s ro G _ _. unfold A'. cbn [vs_rgn]. exact (shape_map_get _ _ _ _ SM G).
      - destruct (vr_kind r2) eqn:K2; auto. unfold A'. cbn [vs_live].
        apply (proj2 (proj1 LIVE (vr_base r2))). exists r2. rewrite K2. auto. }
    split; [unfold A'; apply live_ok_shape; auto|]. split.
    { unfold A'. apply state_below2_shape; auto; [|intros mx []]. intros r' Hr'.
      destruct (Pos.eq_dec (vr_base r') (vr_base r)) as [EB|NB]; [exact (proj2 (SELF r' Hr' EB))|].
      destruct (OTHER r' Hr' NB) as (r2 & Hr2 & SH2 & CN).
      destruct CN as [(-> & _)|[-> _]]; [|intros kk ww e [] ].
      destruct BEL2 as (_ & BR & _). exact (proj1 (proj2 (BR r2 Hr2))). }
    split; [unfold globs_ok2, A'; cbn [v1]; exact GL2|].
    split; [exact (flags_inv_step P E A A' nu nu mem mem' FI2 FSTEP)|].
    intros ma mn mv [].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma rgn_write_sound A nu regs mem r o bs l2 :
    gamma2P A nu regs mem ->
    In r (vs_rgn A) -> is_data_shadow r = false ->
    match vr_kind r with RK_flag _ => False | _ => True end ->
    0 < Z.of_nat (length bs) -> in_ranges (vr_w r) o (Z.of_nat (length bs)) = true ->
    let a := rbase nu r + o in
    let mem' := wbytes mem (wordZ a) bs in
    let A' := mkVS2 (v1 A) l2 (vs_live A) (vs_divdef A) [] in
    shape_map (vs_rgn A) l2 ->
    (forall r2', In r2' l2 -> vr_base r2' <> vr_base r ->
        exists r2, In r2 (vs_rgn A) /\ rshape r2 r2' /\
          ((vr_cells r2' = vr_cells r2 /\ vr_nul r2' = vr_nul r2 /\ ~ (vr_kind r = RK_arg /\ vr_kind r2 = RK_arg))
           \/ (vr_cells r2' = [] /\ vr_nul r2' = []))) ->
    (forall r', In r' l2 -> vr_base r' = vr_base r ->
        region_ok SEGS P E nu A' mem' r' /\ cells_syms_below (vr_cells r') (vs_next (v1 A))) ->
    gamma2P A' nu regs mem'
    /\ frame_mod mem mem' (unit_regions2 P E)
    /\ flags_step P E A A' nu nu mem mem'
    /\ 0 <= a /\ a + Z.of_nat (length bs) <= 2 ^ 64
    /\ (forall i, 0 <= i < Z.of_nat (length bs) -> store_ok SEGS mem (wordZ (a + i)) 1 = true).
  Proof using PO2.
    intros HG2 Hr ND KNF Hlen HW a mem' A' SM OTHER SELF.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & _).
    pose proof (RGN r Hr) as (RB1 & RB2 & RB3 & RDS & CELLS & PERM & NUL & KIND).
    set (n := Z.of_nat (length bs)) in *.
    apply in_ranges_sound in HW as (wlo & whi & HWin & W1 & W2).
    destruct (PERM ND) as [RD WR].
    assert (WB : forall i, 0 <= i < n ->
              vr_lo r <= o + i < vr_hi r
              /\ in_rw_zones P E (a + i) = true
              /\ store_ok SEGS mem (wordZ (a + i)) 1 = true
              /\ covered (unit_regions2 P E) (a + i) 1).
    { intros i Hi. destruct (WR wlo whi (o + i) HWin ltac:(lia)) as (X1 & X2 & X3 & X4).
      unfold a. rewrite <- Z.add_assoc. auto. }
    assert (Hab : 0 <= a < 2 ^ 64 /\ a + n <= 2 ^ 64).
    { destruct (WB 0 ltac:(lia)) as (X1 & _). destruct (WB (n - 1) ltac:(lia)) as (Y1 & _). unfold a. lia. }
    assert (FSnz : vp_fs P <> None) by (destruct (WB 0 ltac:(lia)) as (_ & X2 & _); exact (asan_of_rw _ X2)).
    pose proof (layout_of_env HE FSnz) as L.
    destruct (region_desc A nu regs mem r HG2 Hr ND) as (d1 & V1 & M1 & D1).
    assert (DB : forall y, a <= y < a + n -> dbyteP d1 y).
    { intros y Hy. destruct (WB (y - a) ltac:(lia)) as (X1 & _).
      replace y with (rbase nu r + (o + (y - a))) by (unfold a; lia). apply D1. exact X1. }
    assert (D1NF : match d1 with DFlag _ _ => False | _ => True end).
    { unfold desc_matches in M1. destruct (vr_kind r); destruct d1; auto. }
    assert (WNE : vr_w r <> []) by (intros W0; rewrite W0 in HWin; destruct HWin).
    assert (FSTEP : flags_step P E A A' nu nu mem mem').
    { (* [comment removed for export] *)
      intros y Hy. left. split; [unfold A'; rewrite (own_flags_shape A _ l2 nu (vs_live A) (vs_divdef A) [] SM); tauto|].
      unfold in_flags_zone in Hy. destruct (vp_fs P) as [[len ssl]|] eqn:Efs; [|destruct Hy].
      unfold mem'. pose proof L as (L1 & L2 & _). unfold HIGH_MEM_BEG, HIGH_MEM_END, FS_FRAMES, FS_NCLASSES, FS_SSL, FS_FLAGS in *.
      apply wblock_byte; try lia. intros IN.
      apply (dbyte_not_flags FS SP0v FRAME SHOFF d1 y L V1 (DB y IN) D1NF). unfold FS_FLAGS, FS_FRAMES. lia. }
    split; [|split; [|split; [exact FSTEP|split; [unfold n in Hab; lia|split; [unfold n in Hab; lia|intros i Hi; exact (proj1 (proj2 (proj2 (WB i Hi))))]]]]].
    2:{ (* [comment removed for export] *)
      split; [|apply wbytes_grows]. intros z Hout. rewrite <- (wordZ_u z). unfold mem'.
      pose proof (u64_range z).
      apply wblock_byte; try lia. intros IN.
      destruct (WB (bv_unsigned z - a) ltac:(lia)) as (_ & _ & _ & COV).
      replace (a + (bv_unsigned z - a)) with (bv_unsigned z) in COV by lia.
      apply (covered_not_outside _ _ COV ltac:(lia)). rewrite wordZ_u. exact Hout. }
    (* [comment removed for export] *)
    split.
    { (* [comment removed for export] *)
      assert (G' : gamma SEGS P1 E1 (zpatch P E mem0 mem') (set_pc (v1 A) (vs_pc (v1 A))) nu regs mem').
      { unfold mem'. apply zone_write_v1; try lia; [exact HE| |exact HG1|].
        - intros g gw gv Hin. apply (GL2 ltac:(unfold asan_mode; destruct (vp_fs P); [reflexivity|exfalso; exact (FSnz eq_refl)]) g gw gv Hin).
        - intros i Hi. exact (proj1 (proj2 (WB i Hi))). }
      unfold A'. cbn [v1]. exact G'. }
    split; [exact HE|]. split.
    { unfold mem'. apply MC2_zone_write; try lia; [exact HE|exact HM| |].
      - intros i Hi. exact (proj1 (proj2 (WB i Hi))).
      - intros [c p] y Hcp Hy EQ. pose proof (live_valid _ HE FSnz Hcp) as [Vc Vp]. cbn in Vc, Vp, EQ.
        assert (d1 = DFlag c p).
        { apply (dbyte_disjoint FS SP0v FRAME SHOFF d1 (DFlag c p) y L V1 ltac:(cbn; lia) (DB y Hy)). cbn. exact EQ. }
        subst d1. exact (desc_not_live_flag A nu r _ _ M1 Hcp). }
    split; [exact HF2|]. split; [exact HDD|]. split.
    { (* [comment removed for export] *)
      intros r' Hr'. destruct (Pos.eq_dec (vr_base r') (vr_base r)) as [EB|NB]; [exact (proj1 (SELF r' Hr' EB))|].
      destruct (OTHER r' Hr' NB) as (r2 & Hr2 & SH2 & CN).
      pose proof SH2 as (SB2 & _ & SK2 & _).
      unfold mem'. apply (region_ok_transport A A' nu mem a _ r2 r' HE (RGN r2 Hr2) SH2); try lia.
      - destruct CN as [(C1 & C2 & NAA)|[C1 C2]]; [left|right; auto]. split; [exact C1|]. split; [exact C2|].
        intros ND2 y Hy IN.
        destruct (region_desc A nu regs mem r2 HG2 Hr2 ND2) as (d2 & V2 & M2 & D2).
        assert (B2y : dbyteP d2 y).
        { replace y with (rbase nu r2 + (y - rbase nu r2)) by lia. apply D2. lia. }
        pose proof (dbyte_disjoint FS SP0v FRAME SHOFF d1 d2 y L V1 V2 (DB y IN) B2y) as <-.
        destruct (desc_writer_unique A nu regs mem r r2 d1 HG2 Hr Hr2 M1 M2 WNE) as [<-|AA]; [|exact (NAA AA)].
        apply NB. exact SB2.
      - destruct (vr_kind r2) as [c2 fl2| | | |] eqn:K2; auto. intros IN.
        destruct (region_desc A nu regs mem r2 HG2 Hr2 ltac:(unfold is_data_shadow; rewrite K2; reflexivity)) as (d2 & V2 & M2 & D2).
        unfold desc_matches in M2. rewrite K2 in M2. destruct d2 as [c p| | | |]; try contradiction.
        destruct M2 as (Ec & RBf & FLf & NLf). cbn in V2. subst c.
        assert (d1 = DFlag c2 p).
        { apply (dbyte_disjoint FS SP0v FRAME SHOFF d1 (DFlag c2 p) (nu fl2) L V1 ltac:(cbn; lia) (DB _ IN)). cbn. exact FLf. }
        subst d1. exact D1NF.
      - intros s ro G _ _. unfold A'. cbn [vs_rgn]. exact (shape_map_get _ _ _ _ SM G).
      - destruct (vr_kind r2) eqn:K2; auto. unfold A'. cbn [vs_live].
        apply (proj2 (proj1 LIVE (vr_base r2))). exists r2. rewrite K2. auto. }
    split; [unfold A'; apply live_ok_shape; auto|]. split.
    { unfold A'.
      pose proof (state_below2_shape A l2 (vs_pc (v1 A)) [] BEL2 SM) as SB.
      assert (CB : forall r', In r' l2 -> cells_syms_below (vr_cells r') (vs_next (v1 A))).
      { intros r' Hr'.
        destruct (Pos.eq_dec (vr_base r') (vr_base r)) as [EB|NB]; [exact (proj2 (SELF r' Hr' EB))|].
        destruct (OTHER r' Hr' NB) as (r2 & Hr2 & SH2 & CN).
        destruct CN as [(-> & _)|[-> _]]; [|intros kk ww e [] ].
        destruct BEL2 as (_ & BR & _). exact (proj1 (proj2 (BR r2 Hr2))). }
      specialize (SB CB ltac:(intros mx [])). cbn [v1 vs_rgn vs_live vs_divdef vs_memo] in SB |- *. exact SB. }
    split; [unfold globs_ok2, A'; cbn [v1]; exact GL2|].
    split; [exact (flags_inv_step P E A A' nu nu mem mem' FI2 FSTEP)|].
    intros ma mn mv [].
  Qed.

  (* [comment removed for export] *)
  Lemma flags_step_then_same A1 A2 A3 nu1 nu2 nu3 m1 m2 m3 :
    flags_step P E A1 A2 nu1 nu2 m1 m2 ->
    (forall a, in_flags_zone P E a -> (In a (own_flags A2 nu2) <-> In a (own_flags A3 nu3)) /\ m3 (wordZ a) = m2 (wordZ a)) ->
    flags_step P E A1 A3 nu1 nu3 m1 m3.
  Proof using .
    intros F12 S23 a Ha. specialize (F12 a Ha). destruct (S23 a Ha) as [E23 M23].
    destruct F12 as [[E12 M12]|[(I2 & N1 & Z1)|(I1 & N2 & Z2)]].
    - left. split; [tauto|congruence].
    - right; left. split; [tauto|]. split; [exact N1|exact Z1].
    - right; right. split; [exact I1|]. split; [tauto|]. rewrite M23. exact Z2.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma rgn_kill_nul_shape A1 r lo hi v :
    vr_cells (rgn_kill_nul A1 r lo hi v) = vr_cells r /\ rshape r (rgn_kill_nul A1 r lo hi v)
    /\ forall f, In f (vr_nul (rgn_kill_nul A1 r lo hi v)) -> In f (vr_nul r) /\ (is_zero_val A1 v = true \/ snd f < lo \/ hi < fst f).
  Proof using .
    unfold rgn_kill_nul. destruct (vr_nul r) as [|f0 t] eqn:N.
    - split; [reflexivity|]. split; [apply rshape_refl|]. intros f Hf. rewrite N in Hf. destruct Hf.
    - destruct (is_zero_val A1 v) eqn:ZV.
      + split; [reflexivity|]. split; [apply rshape_refl|]. intros f Hf. rewrite N in Hf. auto.
      + split; [reflexivity|]. split; [apply rshape_set_rnul|]. cbn [vr_nul set_rnul]. intros f Hf.
        apply filter_In in Hf as [Hf Hb]. split; [exact Hf|]. right.
        rewrite orb_true_iff, !Z.ltb_lt in Hb. lia.
  Qed.

  Lemma rgn_add_nul_shape r lo hi :
    vr_cells (rgn_add_nul r lo hi) = vr_cells r /\ rshape r (rgn_add_nul r lo hi)
    /\ forall f, In f (vr_nul (rgn_add_nul r lo hi)) -> f = (lo, hi) \/ In f (vr_nul r).
  Proof using .
    unfold rgn_add_nul, nul_min. split; [reflexivity|]. split; [apply rshape_set_rnul|]. cbn [vr_nul set_rnul].
    intros f Hf. apply filter_In in Hf as [Hf _]. destruct Hf as [<-|Hf]; auto.
  Qed.

  Lemma store_generic_sound A nu regs mem pc rom w sz (rs1 rs2 : reg) (imm : bv 12) addr r off lo hi succs :
    gamma2P A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Store sz rs1 rs2 imm, 4) ->
    addr_of (v1 A) (rz rs1) (bv_signed imm) = Some addr ->
    classify2 A addr (msize_z sz) true = Some (C2Rgn r off lo hi) ->
    match vr_kind r with RK_fake _ _ | RK_arg | RK_fs => True | _ => False end ->
    store_rgn A r off lo hi (msize_z sz) (get_reg (v1 A) (rz rs2)) = VR2_next succs ->
    step_post2 SEGS P E mem0 A nu succs regs mem pc rom.
  Proof using PO2.
    intros HG2 Hpc Hf He Hd Ha CL KG ST.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & _).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof (msize_pos sz) as Hn. set (n := msize_z sz) in *.
    destruct (classify2_rgn A addr n true r off lo hi CL) as (B & r0 & HB & HC & HR0 & HCL).
    destruct (classify_rgn_sound A nu r0 addr n true r off lo hi HL ltac:(lia) HCL) as (-> & Eoff & Eaddr & NDS & DSH).
    pose proof (rgn_in _ _ _ HR0) as Hr.
    assert (ND : is_data_shadow r0 = false) by (unfold is_data_shadow; destruct (vr_kind r0); auto; contradiction).
    destruct (NDS ND) as (Hlohi & Hlo & Hhi & HW). specialize (HW eq_refl).
    pose proof (RGN r0 Hr) as ROK. pose proof ROK as (RB1 & RB2 & RB3 & RDS & CELLS & PERM & NUL & KIND).
    pose proof (gamma_get_reg SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem rs2 HG1) as [Wv Bv].
    set (val := get_reg (v1 A) (rz rs2)) in *. set (wv := getr regs rs2) in *.
    set (k := Z.to_nat n). assert (Hkn : Z.of_nat k = n) by (unfold k; lia).
    assert (Hlen : length (word_to_le_bytes k wv) = k) by apply length_N_to_le_bytes.
    set (a := rbase nu r0 + eval nu off).
    set (mem' := wbytes mem (wordZ a) (word_to_le_bytes k wv)).
    (* [comment removed for export] *)
    set (cells := if lo =? hi then
                    match val with Some e => cm_set (cm_kill (vr_cells r0) lo (lo + n)) lo (n, Some e)
                               | None => cm_kill (vr_cells r0) lo (lo + n) end
                  else cm_kill (vr_cells r0) lo (hi + n)).
    set (r1 := rgn_kill_nul (v1 A) (set_cells r0 cells) lo (hi + n - 1) val).
    set (r2 := if (n =? 1) && is_zero_byte (v1 A) val then rgn_add_nul r1 lo hi else r1).
    set (l1 := rgn_upd (vs_rgn A) r2).
    set (l2 := match vr_kind r0 with RK_arg => havoc_other_args l1 (vr_base r0) | _ => l1 end).
    assert (ES : succs = [mkVS2 (set_pc (v1 A) (npc_of (v1 A))) l2 (vs_live A) (vs_divdef A) []]).
    { unfold store_rgn in ST. destruct (vr_kind r0) eqn:K; try contradiction; injection ST as <-; reflexivity. }
    rewrite ES. clear ST ES.
    (* [comment removed for export] *)
    destruct (rgn_kill_nul_shape (v1 A) (set_cells r0 cells) lo (hi + n - 1) val) as (C1 & SH1 & N1).
    assert (SHr2 : rshape r0 r2 /\ vr_cells r2 = cells /\
                   forall f, In f (vr_nul r2) -> (f = (lo, hi) /\ n = 1 /\ is_zero_byte (v1 A) val = true)
                                               \/ (In f (vr_nul r0) /\ (is_zero_val (v1 A) val = true \/ snd f < lo \/ hi + n - 1 < fst f))).
    { unfold r2. destruct ((n =? 1) && is_zero_byte (v1 A) val) eqn:ZB.
      - apply andb_prop in ZB as [N1' ZB]. apply Z.eqb_eq in N1'.
        destruct (rgn_add_nul_shape r1 lo hi) as (C2 & SH2 & N2).
        split; [eapply rshape_trans; [eapply rshape_trans; [apply rshape_set_cells|exact SH1]|exact SH2]|].
        split; [rewrite C2; unfold r1; rewrite C1; reflexivity|].
        intros f Hnf. destruct (N2 f Hnf) as [->|Hf1]; [left; auto|]. right.
        destruct (N1 f Hf1) as [X Y]. cbn [vr_nul set_cells] in X. auto.
      - split; [eapply rshape_trans; [apply rshape_set_cells|exact SH1]|].
        split; [unfold r1; rewrite C1; reflexivity|].
        intros f Hnf. right. destruct (N1 f Hnf) as [X Y]. cbn [vr_nul set_cells] in X. auto. }
    destruct SHr2 as (SH2 & C2 & N2).
    pose proof SH2 as (SB2 & _).
    assert (INB : In (vr_base r2) (map vr_base (vs_rgn A))) by (rewrite SB2; apply in_map; exact Hr).
    assert (SM1 : shape_map (vs_rgn A) l1).
    { unfold l1. apply rgn_upd_shape; [|exact INB]. intros x Hx EB.
      rewrite (live_ok_base_inj nu A x r0 LIVE Hx Hr ltac:(rewrite EB; exact SB2)). exact SH2. }
    assert (SM2 : shape_map (vs_rgn A) l2).
    { unfold l2. destruct (vr_kind r0); try exact SM1. eapply shape_map_trans; [exact SM1|apply havoc_shape]. }
    pose proof LIVE as (_ & _ & _ & ND0).
    (* [comment removed for export] *)
    assert (MEM : forall x, In x l2 ->
              (x = r2) \/ (In x (vs_rgn A) /\ vr_base x <> vr_base r0 /\ ~ (vr_kind r0 = RK_arg /\ vr_kind x = RK_arg))
              \/ (exists y, In y (vs_rgn A) /\ vr_base y <> vr_base r0 /\ vr_kind r0 = RK_arg /\ vr_kind y = RK_arg
                               /\ x = set_rnul (set_cells y []) [])).
    { intros x Hx. unfold l2 in Hx.
      assert (L1C : forall y, In y l1 -> y = r2 \/ (In y (vs_rgn A) /\ vr_base y <> vr_base r0)).
      { intros y Hy. destruct (rgn_upd_other _ _ _ ND0 INB Hy) as [->|[Y1 Y2]]; [auto|right]. rewrite SB2 in Y2. auto. }
      destruct (vr_kind r0) eqn:K0;
        try (destruct (L1C x Hx) as [->|[X1 X2]]; [left; reflexivity|right; left; repeat split; auto; intros [X _]; discriminate]).
      rewrite havoc_other_args_map in Hx. apply in_map_iff in Hx as (y & <- & Hy).
      destruct (havoc1_spec (vr_base r0) y) as [[KB ->]|(KA & NB & ->)].
      - destruct (L1C y Hy) as [->|[Y1 Y2]]; [left; reflexivity|]. right; left. split; [exact Y1|]. split; [exact Y2|].
        intros [_ X]. destruct KB as [KB|KB]; [exact (KB X)|exact (Y2 KB)].
      - destruct (L1C y Hy) as [->|[Y1 Y2]]; [exfalso; apply NB; exact SB2|].
        right; right. exists y. repeat split; auto. }
    (* [comment removed for export] *)
    destruct (PERM ND) as [RD WR].
    pose proof HW as HW0. apply in_ranges_sound in HW as (wlo & whi & HWin & W1 & W2).
    assert (WB : forall i, 0 <= i < n -> vr_lo r0 <= eval nu off + i < vr_hi r0 /\ in_rw_zones P E (a + i) = true).
    { intros i Hi. destruct (WR wlo whi (eval nu off + i) HWin ltac:(lia)) as (X1 & X2 & _). unfold a. rewrite <- Z.add_assoc. auto. }
    assert (Hab : 0 <= a < 2 ^ 64 /\ a + n <= 2 ^ 64) by (unfold a; lia).
    assert (FSnz : vp_fs P <> None) by (destruct (WB 0 ltac:(lia)) as [_ X2]; exact (asan_of_rw _ X2)).
    pose proof (layout_of_env HE FSnz) as L.
    eapply (rgn_store_sound A nu regs mem pc rom w sz rs1 rs2 imm addr r0 off lo hi l2); eauto.
    { destruct (vr_kind r0); auto. }
    - (* [comment removed for export] *)
      intros r2' Hr2' NB. destruct (MEM r2' Hr2') as [->|[(X1 & X2 & X3)|(y & Y1 & Y2 & Y3 & Y4 & ->)]].
      + exfalso. apply NB. exact SB2.
      + exists r2'. split; [exact X1|]. split; [apply rshape_refl|]. left. auto.
      + exists y. split; [exact Y1|]. split; [|right; split; reflexivity].
        eapply rshape_trans; [apply rshape_set_cells|apply rshape_set_rnul].
    - (* [comment removed for export] *)
      intros r' Hr' EB.
      assert (ER : r' = r2).
      { destruct (MEM r' Hr') as [->|[(X1 & X2 & X3)|(y & Y1 & Y2 & Y3 & Y4 & ->)]]; [reflexivity|exfalso; exact (X2 EB)|].
        exfalso. apply Y2. exact EB. }
      subst r'.
      fold k wv. change (wbytes mem (wordZ (rbase nu r0 + eval nu off)) (word_to_le_bytes k wv)) with mem'.
      (* [comment removed for export] *)
      assert (BLK : forall c cw, vr_lo r0 <= c -> c + cw <= vr_hi r0 -> 0 < cw ->
                (c + cw <= lo \/ hi + n <= c) \/ (lo = hi /\ (c + cw <= lo \/ lo + n <= c)) ->
                rbase nu r0 + c + cw <= a \/ a + Z.of_nat (length (word_to_le_bytes k wv)) <= rbase nu r0 + c).
      { intros c cw H1 H2 H3 H4. rewrite Hlen, Hkn. unfold a. lia. }
      split.
      2:{ (* [comment removed for export] *)
        rewrite C2. intros kk ww e Hin. destruct BEL2 as (_ & BR & _). pose proof (proj1 (proj2 (BR r0 Hr))) as CB.
        unfold cells in Hin. destruct (lo =? hi).
        - destruct val as [ev|].
          + apply cm_set_in in Hin as [Hin|Hin]; [injection Hin as -> -> ->; exact Bv|]. exact (CB _ _ _ (cm_kill_sub _ _ _ _ Hin)).
          + exact (CB _ _ _ (cm_kill_sub _ _ _ _ Hin)).
        - exact (CB _ _ _ (cm_kill_sub _ _ _ _ Hin)). }
      eapply (region_ok_self A _ nu mem mem' r0 r2 HE ROK SH2 ND).
      + apply wbytes_grows.
      + (* [comment removed for export] *)
        destruct (vr_kind r0) as [cid fl| | | |] eqn:K0; auto.
        destruct (region_desc A nu regs mem r0 HG2 Hr ND) as (d1 & V1 & M1 & D1).
        unfold desc_matches in M1. rewrite K0 in M1. destruct d1 as [c p| | | |]; try contradiction.
        destruct M1 as (Ec & RBf & FLf & NLf). subst c. cbn in V1.
        unfold kind_ok in KIND. rewrite K0 in KIND. destruct KIND as (F1 & F2 & _ & _ & _ & pos & Q1 & Q2 & Q3 & _).
        destruct (vp_fs P) as [[len ssl]|] eqn:Efs; [|exfalso; exact (F1 eq_refl)].
        destruct (flag_byte_outside _ _ _ PO2 len ssl cid pos HE Efs F2 Q1) as [_ R].
        pose proof HE as (_ & _ & HF & _). unfold env_fs in HF. rewrite Efs in HF. destruct HF as (_ & Hflo & Hfhi & _).
        unfold HIGH_MEM_BEG, HIGH_MEM_END in *.
        unfold mem'. apply wblock_rdn1; rewrite ?Hlen, ?Hkn; try lia. intros IN.
        assert (DSlot cid p = DFlag cid p); [|discriminate].
        apply (dbyte_disjoint FS SP0v FRAME SHOFF (DSlot cid p) (DFlag cid p) (nu fl) L); cbn; try lia.
        destruct (WB (nu fl - a) ltac:(lia)) as [X1 _].
        replace (nu fl) with (rbase nu r0 + (eval nu off + (nu fl - a))) by (unfold a; lia). apply D1. exact X1.
      + intros s0 ro G _ _. cbn [vs_rgn]. exact (shape_map_get _ _ _ _ SM2 G).
      + destruct (vr_kind r0) eqn:K0; auto. cbn [vs_live]. apply (proj2 (proj1 LIVE (vr_base r0))). exists r0. rewrite K0. auto.
      + destruct (vr_kind r0); auto; contradiction.
      + (* [comment removed for export] *)
        rewrite C2. intros c cw cv Hin.
        assert (OLD : In (c, (cw, cv)) (vr_cells r0) ->
                  (c + cw <= lo \/ hi + n <= c) \/ (lo = hi /\ (c + cw <= lo \/ lo + n <= c)) ->
                  vr_lo r0 <= c /\ 0 < cw /\ c + cw <= vr_hi r0 /\ rcell_holds SEGS (is_shadow r0) nu mem' (rbase nu r0 + c) cw cv).
        { intros Hold DISJ. destruct (CELLS _ _ _ Hold) as (L1 & L2 & L3 & RC). split; [lia|]. split; [lia|]. split; [lia|].
          unfold mem'. apply kept_cell; rewrite ?Hlen, ?Hkn; try lia. exact RC. }
        unfold cells in Hin. destruct (Z.eqb_spec lo hi) as [Elh|Nlh].
        * assert (Eov : eval nu off = lo) by lia.
          destruct val as [ev|].
          -- apply cm_set_in in Hin as [Hin|Hin].
             ++ injection Hin as -> -> ->. split; [lia|]. split; [lia|]. split; [lia|].
                unfold rcell_holds. replace (is_shadow r0) with false by (unfold is_shadow; destruct (vr_kind r0); auto; contradiction).
                cbn [andb cell_holds]. exists (word_to_le_bytes k wv). split.
                ** unfold mem', a. rewrite Eov. replace (Z.to_nat n) with k by lia. rewrite <- Hlen at 2.
                   apply rdn_wbytes_hit. rewrite u_wordZ by lia. rewrite Hlen. lia.
                ** rewrite bytes_le_N, Hkn. rewrite (wval_some _ _ _ Wv). unfold zwrap.
                   apply Z.mod_mod_divide. exists (2 ^ (64 - 8 * n)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
             ++ apply OLD; [eapply cm_kill_sub; exact Hin|]. pose proof (cm_kill_disjoint _ _ _ _ _ _ Hin). right. lia.
          -- apply OLD; [eapply cm_kill_sub; exact Hin|]. pose proof (cm_kill_disjoint _ _ _ _ _ _ Hin). right. lia.
        * apply OLD; [eapply cm_kill_sub; exact Hin|]. pose proof (cm_kill_disjoint _ _ _ _ _ _ Hin). left. lia.
      + (* [comment removed for export] *)
        intros nlo nhi Hin.
        assert (ZB : forall j, (j < k)%nat -> bv_unsigned wv = 0 ->
                  rdn SEGS mem' (wordZ (a + Z.of_nat j)) 1 = Some [nth j (word_to_le_bytes k wv) (Z_to_bv 8 0)] /\
                  bv_unsigned (nth j (word_to_le_bytes k wv) (Z_to_bv 8 0)) = 0).
        { intros j Hj Hz. split.
          - unfold mem'. apply rdn_wbytes_byte; rewrite ?Hlen; lia.
          - apply bytes_zero; [|rewrite Hlen; exact Hj]. rewrite bytes_le_N, Hz. reflexivity. }
        destruct (N2 _ Hin) as [(Ef & En1 & Ezb)|(Hin1 & DISJ)].
        * (* [comment removed for export] *)
          injection Ef as -> ->. exists (eval nu off), (nth 0 (word_to_le_bytes k wv) (Z_to_bv 8 0)).
          assert (Hbz : bv_unsigned wv mod 256 = 0).
          { apply (is_zero_byte_sound mem0 (v1 A) nu val wv HL Ezb). subst val.
            destruct (get_reg (v1 A) (rz rs2)) as [ev|]; [exact (wval_some _ _ _ Wv)|].
            unfold is_zero_byte in Ezb. discriminate. }
          split; [lia|]. split; [lia|]. split.
          -- replace (rbase nu r0 + eval nu off) with (a + Z.of_nat 0) by (unfold a; lia).
             unfold mem'. apply rdn_wbytes_byte; rewrite ?Hlen; lia.
          -- assert (K1 : k = 1%nat) by lia. rewrite K1. cbn [word_to_le_bytes Z_to_le_bytes nth].
             rewrite Z_to_bv_unsigned, bv_wrap8_mod. exact Hbz.
        * destruct (NUL _ _ Hin1) as (o0 & b0 & R1 & R2 & R3 & R4).
          destruct (Z.lt_ge_cases o0 (eval nu off)) as [LT|GE].
          { exists o0, b0. repeat split; try lia; auto. rewrite <- R3. unfold mem'. apply wblock_rdn1; rewrite ?Hlen, ?Hkn; unfold a; lia. }
          destruct (Z.lt_ge_cases o0 (eval nu off + n)) as [LT2|GE2].
          2:{ exists o0, b0. repeat split; try lia; auto. rewrite <- R3. unfold mem'. apply wblock_rdn1; rewrite ?Hlen, ?Hkn; unfold a; lia. }
          (* [comment removed for export] *)
          destruct DISJ as [ZV|DISJ]; [|exfalso; cbn [fst snd] in DISJ; lia].
          assert (Hz : bv_unsigned wv = 0).
          { apply (is_zero_val_sound mem0 (v1 A) nu val wv HL ZV). subst val.
            destruct (get_reg (v1 A) (rz rs2)) as [ev|]; [exact (wval_some _ _ _ Wv)|]. unfold is_zero_val in ZV. discriminate. }
          destruct (ZB (Z.to_nat (o0 - eval nu off)) ltac:(lia) Hz) as [Z1 Z2].
          exists o0, (nth (Z.to_nat (o0 - eval nu off)) (word_to_le_bytes k wv) (Z_to_bv 8 0)).
          split; [lia|]. split; [lia|]. split; [|exact Z2].
          replace (rbase nu r0 + o0) with (a + Z.of_nat (Z.to_nat (o0 - eval nu off))) by (unfold a; lia). exact Z1.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma sh_cut_in m lo hi k w v :
    In (k, (w, v)) (sh_cut m lo hi) ->
    exists k0 w0, In (k0, (w0, v)) m /\ k0 <= k /\ k + w <= k0 + w0 /\ (k + w <= lo \/ hi <= k) /\
                  ((k, w) = (k0, w0) \/ (0 < w /\ exists e, v = Some e /\ lin_is_const e = true)).
  Proof using .
    induction m as [|[k0 [w0 v0]] t IH]; simpl; [tauto|]. rewrite ?if_andb.
    destruct (Z.ltb k0 hi && Z.ltb lo (k0 + w0)) eqn:OV.
    - apply andb_prop in OV as [O1 O2]. apply Z.ltb_lt in O1. apply Z.ltb_lt in O2.
      intros H. apply in_app_or in H as [H|H]; [|apply in_app_or in H as [H|H]].
      + destruct (Z.ltb_spec k0 lo); [|destruct H].
        destruct v0 as [e|]; [|destruct H]. destruct (lin_is_const e) eqn:CE; [|destruct H].
        destruct H as [H|[]]. injection H as <- <- <-. exists k0, w0. split; [auto|]. split; [lia|]. split; [lia|]. split; [lia|].
        right. split; [lia|]. exists e; auto.
      + destruct (Z.ltb_spec hi (k0 + w0)); [|destruct H].
        destruct v0 as [e|]; [|destruct H]. destruct (lin_is_const e) eqn:CE; [|destruct H].
        destruct H as [H|[]]. injection H as <- <- <-. exists k0, w0. split; [auto|]. split; [lia|]. split; [lia|]. split; [lia|].
        right. split; [lia|]. exists e; auto.
      + destruct (IH H) as (k1 & w1 & X). exists k1, w1. intuition.
    - rewrite andb_false_iff, !Z.ltb_ge in OV. intros [H|H].
      + injection H as <- <- <-. exists k0, w0. split; [auto|]. split; [lia|]. split; [lia|]. split; [lia|]. left; reflexivity.
      + destruct (IH H) as (k1 & w1 & X). exists k1, w1. intuition.
  Qed.

  (* [comment removed for export] *)
  Lemma sh_ins_r_in t k w e c cw cv :
    0 < w -> (forall k0 w0 v0, In (k0, (w0, v0)) t -> 0 < w0) ->
    In (c, (cw, cv)) (sh_ins_r t k w e) ->
    In (c, (cw, cv)) t \/
    (c = k /\ cv = Some e /\ 0 < cw /\
     forall p, k <= p < k + cw -> k <= p < k + w \/
       exists k0 w0 e0, In (k0, (w0, Some e0)) t /\ lin_is_const e0 = true /\ lc e0 = lc e /\ k0 <= p < k0 + w0).
  Proof using .
    intros Hw POS H. destruct t as [|[k2 [w2 v2]] t2]; cbn [sh_ins_r] in H.
    - destruct H as [H|[]]. injection H as <- <- <-. right. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hw|].
      intros p Hp. left. exact Hp.
    - destruct (Z.eqb_spec k2 (k + w)) as [E2|E2]; [destruct (sh_same v2 e) eqn:SM|].
      + pose proof (POS k2 w2 v2 (or_introl eq_refl)) as Hw2.
        destruct H as [H|H]; [|left; right; exact H].
        injection H as <- <- <-. right. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
        intros p Hp. destruct (Z.ltb_spec p (k + w)) as [L|L]; [left; lia|right].
        unfold sh_same in SM. destruct v2 as [e2|]; [|discriminate]. destruct (lin_is_const e2) eqn:CE2; [|discriminate].
        apply Z.eqb_eq in SM. exists k2, w2, e2. split; [left; reflexivity|]. split; [exact CE2|]. split; [exact SM|]. lia.
      + destruct H as [H|H]; [|left; exact H].
        injection H as <- <- <-. right. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hw|]. intros p Hp. left. exact Hp.
      + destruct H as [H|H]; [|left; exact H].
        injection H as <- <- <-. right. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hw|]. intros p Hp. left. exact Hp.
  Qed.

  Lemma sh_ins_in m o w e c cw cv :
    0 < w -> (forall k0 w0 v0, In (k0, (w0, v0)) m -> 0 < w0) ->
    In (c, (cw, cv)) (sh_ins m o w e) ->
    In (c, (cw, cv)) m \/
    (cv = Some e /\ 0 < cw /\
     forall p, c <= p < c + cw -> o <= p < o + w \/
       exists k0 w0 e0, In (k0, (w0, Some e0)) m /\ lin_is_const e0 = true /\ lc e0 = lc e /\ k0 <= p < k0 + w0).
  Proof using .
    intros Hw. induction m as [|[k [w' v']] t IH]; intros POS H; cbn [sh_ins] in H.
    - destruct H as [H|[]]. injection H as <- <- <-. right. split; [reflexivity|]. split; [exact Hw|]. intros p Hp. left. exact Hp.
    - pose proof (POS k w' v' (or_introl eq_refl)) as Hw'.
      assert (POSt : forall k0 w0 v0, In (k0, (w0, v0)) t -> 0 < w0) by (intros k0 w0 v0 X; exact (POS k0 w0 v0 (or_intror X))).
      destruct (Z.ltb_spec k o) as [Lk|Lk].
      + destruct (Z.eqb_spec (k + w') o) as [Ek|Ek]; [destruct (sh_same v' e) eqn:SM|].
        * destruct (sh_ins_r_in t k (w' + w) e c cw cv ltac:(lia) POSt H) as [X|(-> & -> & Hcw & COV)]; [left; right; exact X|].
          right. split; [reflexivity|]. split; [exact Hcw|]. intros p Hp.
          destruct (COV p Hp) as [X|(k0 & w0 & e0 & X1 & X2 & X3 & X4)].
          -- destruct (Z.ltb_spec p o) as [Lp|Lp]; [right|left; lia].
             unfold sh_same in SM. destruct v' as [e'|]; [|discriminate]. destruct (lin_is_const e') eqn:CE'; [|discriminate].
             apply Z.eqb_eq in SM. exists k, w', e'. split; [left; reflexivity|]. split; [exact CE'|]. split; [exact SM|]. lia.
          -- right. exists k0, w0, e0. split; [right; exact X1|]. auto.
        * destruct H as [H|H]; [left; left; exact H|].
          destruct (IH POSt H) as [X|(X1 & X2 & COV)]; [left; right; exact X|].
          right. split; [exact X1|]. split; [exact X2|]. intros p Hp. destruct (COV p Hp) as [Y|(k0 & w0 & e0 & Y1 & Y2)]; [left; exact Y|].
          right. exists k0, w0, e0. split; [right; exact Y1|exact Y2].
        * destruct H as [H|H]; [left; left; exact H|].
          destruct (IH POSt H) as [X|(X1 & X2 & COV)]; [left; right; exact X|].
          right. split; [exact X1|]. split; [exact X2|]. intros p Hp. destruct (COV p Hp) as [Y|(k0 & w0 & e0 & Y1 & Y2)]; [left; exact Y|].
          right. exists k0, w0, e0. split; [right; exact Y1|exact Y2].
      + destruct (sh_ins_r_in ((k, (w', v')) :: t) o w e c cw cv Hw POS H) as [X|(-> & -> & Hcw & COV)]; [left; exact X|].
        right. split; [reflexivity|]. split; [exact Hcw|]. exact COV.
  Qed.

  (* [comment removed for export] *)
  Lemma sh_ins_cells nu (mem' : word -> option byte) r0 lo n b0 m1 :
    0 < n -> vr_lo r0 <= lo -> lo + n <= vr_hi r0 ->
    (forall c cw cv, In (c, (cw, cv)) m1 ->
       vr_lo r0 <= c /\ 0 < cw /\ c + cw <= vr_hi r0 /\ rcell_holds SEGS true nu mem' (rbase nu r0 + c) cw cv) ->
    run_holds SEGS mem' (rbase nu r0 + lo) n b0 ->
    forall c cw cv, In (c, (cw, cv)) (sh_ins m1 lo n (lconst b0)) ->
      vr_lo r0 <= c /\ 0 < cw /\ c + cw <= vr_hi r0 /\ rcell_holds SEGS true nu mem' (rbase nu r0 + c) cw cv.
  Proof using .
    intros Hn Hlo Hhi OLD RUN c cw cv Hin.
    destruct (sh_ins_in m1 lo n (lconst b0) c cw cv Hn ltac:(intros k0 w0 v0 X; exact (proj1 (proj2 (OLD _ _ _ X)))) Hin)
      as [X|(-> & Hcw & COV)]; [exact (OLD _ _ _ X)|].
    assert (B1 : vr_lo r0 <= c).
    { destruct (COV c ltac:(lia)) as [X|(k0 & w0 & e0 & X1 & _ & _ & X4)]; [lia|].
      destruct (OLD _ _ _ X1) as (Y1 & _). lia. }
    assert (B2 : c + cw <= vr_hi r0).
    { destruct (COV (c + cw - 1) ltac:(lia)) as [X|(k0 & w0 & e0 & X1 & _ & _ & X4)]; [lia|].
      destruct (OLD _ _ _ X1) as (_ & _ & Y3 & _). lia. }
    split; [exact B1|]. split; [exact Hcw|]. split; [exact B2|].
    unfold rcell_holds. replace (lin_is_const (lconst b0)) with true by reflexivity. cbn [andb lc lconst].
    intros i Hi. destruct (COV (c + i) ltac:(lia)) as [X|(k0 & w0 & e0 & X1 & X2 & X3 & X4)].
    - destruct (RUN (c + i - lo) ltac:(lia)) as (kb & R1 & R2). exists kb. split; [|exact R2].
      replace (rbase nu r0 + c + i) with (rbase nu r0 + lo + (c + i - lo)) by lia. exact R1.
    - destruct (OLD _ _ _ X1) as (_ & _ & _ & RC). unfold rcell_holds in RC. rewrite X2 in RC. cbn [andb] in RC.
      destruct (RC (c + i - k0) ltac:(lia)) as (kb & R1 & R2). exists kb. split.
      + replace (rbase nu r0 + c + i) with (rbase nu r0 + k0 + (c + i - k0)) by lia. exact R1.
      + rewrite R2, X3. reflexivity.
  Qed.

  Lemma low_byte_wrap x j : 0 <= j -> j < 8 ->
    Z.land (Z.shiftr (zwrap 64 x) (8 * j)) 255 = Z.land (Z.shiftr x (8 * j)) 255.
  Proof using .
    intros H0 H8. unfold zwrap. apply Z.bits_inj'. intros i Hi.
    rewrite !Z.land_spec, !Z.shiftr_spec by lia.
    replace 255 with (Z.ones 8) by reflexivity. rewrite Z.testbit_ones_nonneg by lia.
    destruct (Z.ltb_spec i 8); [|now rewrite !andb_false_r].
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  Qed.

  Lemma store_shadow_sound A nu regs mem pc rom w sz (rs1 rs2 : reg) (imm : bv 12) addr r off lo hi succs sbase :
    gamma2P A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Store sz rs1 rs2 imm, 4) ->
    addr_of (v1 A) (rz rs1) (bv_signed imm) = Some addr ->
    classify2 A addr (msize_z sz) true = Some (C2Rgn r off lo hi) ->
    vr_kind r = RK_shadow sbase ->
    store_rgn A r off lo hi (msize_z sz) (get_reg (v1 A) (rz rs2)) = VR2_next succs ->
    step_post2 SEGS P E mem0 A nu succs regs mem pc rom.
  Proof using PO2.
    intros HG2 Hpc Hf He Hd Ha CL KS ST.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & _).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof (msize_pos sz) as Hn. set (n := msize_z sz) in *.
    destruct (classify2_rgn A addr n true r off lo hi CL) as (B & r0 & HB & HC & HR0 & HCL).
    destruct (classify_rgn_sound A nu r0 addr n true r off lo hi HL ltac:(lia) HCL) as (-> & Eoff & Eaddr & NDS & DSH).
    pose proof (rgn_in _ _ _ HR0) as Hr.
    assert (ND : is_data_shadow r0 = false).
    { destruct (is_data_shadow r0) eqn:X; [|reflexivity]. destruct (DSH eq_refl) as [X1 _]. discriminate. }
    destruct (NDS ND) as (Hlohi & Hlo & Hhi & HW). specialize (HW eq_refl).
    pose proof (RGN r0 Hr) as ROK. pose proof ROK as (RB1 & RB2 & RB3 & RDS & CELLS & PERM & NUL & KIND).
    pose proof (gamma_get_reg SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem rs2 HG1) as [Wv Bv].
    set (val := get_reg (v1 A) (rz rs2)) in *. set (wv := getr regs rs2) in *.
    set (k := Z.to_nat n). assert (Hkn : Z.of_nat k = n) by (unfold k; lia).
    assert (Hlen : length (word_to_le_bytes k wv) = k) by apply length_N_to_le_bytes.
    set (a := rbase nu r0 + eval nu off).
    set (mem' := wbytes mem (wordZ a) (word_to_le_bytes k wv)).
    (* [comment removed for export] *)
    unfold store_rgn in ST. rewrite KS in ST.
    destruct val as [e|] eqn:Eval; [|discriminate].
    destruct (lin_is_const e) eqn:CE; cbn [negb] in ST; [|discriminate].
    set (b0 := Z.land (lc e) 255) in *.
    destruct (forallb (fun j : Z => Z.land (Z.shiftr (lc e) (8 * j)) 255 =? b0) (zrange 0 (Z.to_nat n))) eqn:ALLB; cbn [negb] in ST; [|discriminate].
    set (cells := if lo =? hi then sh_write (vr_cells r0) lo n (Some (lconst b0)) else sh_cut (vr_cells r0) lo (hi + n)).
    set (r2 := set_rnul (set_cells r0 cells) []).
    set (l2 := rgn_upd (vs_rgn A) r2).
    assert (ES : succs = [mkVS2 (set_pc (v1 A) (npc_of (v1 A))) l2 (vs_live A) (vs_divdef A) []]).
    { unfold l2, r2, cells. destruct (lo =? hi); injection ST as <-; reflexivity. }
    rewrite ES. clear ST ES.
    assert (SH2 : rshape r0 r2) by (eapply rshape_trans; [apply rshape_set_cells|apply rshape_set_rnul]).
    pose proof SH2 as (SB2 & _).
    assert (INB : In (vr_base r2) (map vr_base (vs_rgn A))) by (rewrite SB2; apply in_map; exact Hr).
    assert (SM2 : shape_map (vs_rgn A) l2).
    { unfold l2. apply rgn_upd_shape; [|exact INB]. intros x Hx EB.
      rewrite (live_ok_base_inj nu A x r0 LIVE Hx Hr ltac:(rewrite EB; exact SB2)). exact SH2. }
    pose proof LIVE as (_ & _ & _ & ND0).
    assert (MEM : forall x, In x l2 -> x = r2 \/ (In x (vs_rgn A) /\ vr_base x <> vr_base r0)).
    { intros x Hx. destruct (rgn_upd_other _ _ _ ND0 INB Hx) as [->|[Y1 Y2]]; [auto|right]. rewrite SB2 in Y2. auto. }
    (* [comment removed for export] *)
    destruct (PERM ND) as [RD WR].
    pose proof HW as HW0. apply in_ranges_sound in HW as (wlo & whi & HWin & W1 & W2).
    assert (WB : forall i, 0 <= i < n -> vr_lo r0 <= eval nu off + i < vr_hi r0 /\ in_rw_zones P E (a + i) = true).
    { intros i Hi. destruct (WR wlo whi (eval nu off + i) HWin ltac:(lia)) as (X1 & X2 & _). unfold a. rewrite <- Z.add_assoc. auto. }
    assert (Hab : 0 <= a < 2 ^ 64 /\ a + n <= 2 ^ 64) by (unfold a; lia).
    eapply (rgn_store_sound A nu regs mem pc rom w sz rs1 rs2 imm addr r0 off lo hi l2); eauto.
    { rewrite KS. exact I. }
    - (* [comment removed for export] *)
      intros r2' Hr2' NB. destruct (MEM r2' Hr2') as [->|[X1 X2]]; [exfalso; apply NB; exact SB2|].
      exists r2'. split; [exact X1|]. split; [apply rshape_refl|]. left. split; [reflexivity|]. split; [reflexivity|].
      rewrite KS. intros [X _]. discriminate.
    - (* [comment removed for export] *)
      intros r' Hr' EB.
      assert (ER : r' = r2) by (destruct (MEM r' Hr') as [->|[X1 X2]]; [reflexivity|exfalso; exact (X2 EB)]). subst r'.
      fold k wv. change (wbytes mem (wordZ (rbase nu r0 + eval nu off)) (word_to_le_bytes k wv)) with mem'.
      assert (ISH : is_shadow r0 = true) by (unfold is_shadow; rewrite KS; reflexivity).
      (* [comment removed for export] *)
      assert (BYTE : forall j, (j < k)%nat ->
                exists kb : byte, rdn SEGS mem' (wordZ (a + Z.of_nat j)) 1 = Some [kb] /\ bv_unsigned kb = Z.land b0 255).
      { intros j Hj. destruct (block_byte mem a k wv j ltac:(lia) ltac:(lia) Hj) as [R1 R2].
        eexists. split; [exact R1|]. rewrite R2. rewrite (wval_some _ _ _ Wv), (eval_is_const nu e CE).
        rewrite low_byte_wrap by lia.
        rewrite forallb_forall in ALLB. specialize (ALLB (Z.of_nat j) ltac:(apply zrange_in; lia)). cbn beta in ALLB.
        apply Z.eqb_eq in ALLB. rewrite ALLB. unfold b0. rewrite <- Z.land_assoc. reflexivity. }
      (* [comment removed for export] *)
      assert (CUT : forall X c cw cv, X = lo + n \/ X = hi + n -> (X = lo + n -> lo = hi) ->
                In (c, (cw, cv)) (sh_cut (vr_cells r0) lo X) ->
                vr_lo r0 <= c /\ 0 < cw /\ c + cw <= vr_hi r0 /\ rcell_holds SEGS (is_shadow r0) nu mem' (rbase nu r0 + c) cw cv).
      { intros X c cw cv HX HXe Hin. apply sh_cut_in in Hin as (k0 & w0 & Hold & K1 & K2 & DISJ & PIECE).
        destruct (CELLS _ _ _ Hold) as (L1 & L2 & L3 & RC).
        assert (DB : rbase nu r0 + c + cw <= a \/ a + Z.of_nat (length (word_to_le_bytes k wv)) <= rbase nu r0 + c).
        { rewrite Hlen, Hkn. unfold a. destruct HX as [-> | ->]; [specialize (HXe eq_refl)|]; lia. }
        destruct PIECE as [EQ|(Hw & e1 & -> & CE1)].
        - injection EQ as -> ->. split; [lia|]. split; [lia|]. split; [lia|]. unfold mem'. apply kept_cell; rewrite ?Hlen, ?Hkn; try lia. exact RC.
        - split; [lia|]. split; [lia|]. split; [lia|]. unfold rcell_holds in RC |- *. rewrite ISH, CE1 in RC |- *. cbn [andb] in RC |- *.
          intros i Hi. destruct (RC (c - k0 + i) ltac:(lia)) as (kb & Hkb & Hb). exists kb. split; [|exact Hb].
          replace (rbase nu r0 + c + i) with (rbase nu r0 + k0 + (c - k0 + i)) by lia. rewrite <- Hkb.
          unfold mem'. apply wblock_rdn1; rewrite ?Hlen, ?Hkn; lia. }
      (* [comment removed for export] *)
      assert (POS : forall X k0 w0 v0, In (k0, (w0, v0)) (sh_cut (vr_cells r0) lo X) -> 0 < w0).
      { intros X k0 w0 v0 HX. apply sh_cut_in in HX as (k1 & w1 & Hold & K1 & K2 & _ & PIECE).
        destruct (CELLS _ _ _ Hold) as (_ & Pw0 & _). destruct PIECE as [EQ|(Hw & _)]; [injection EQ as -> ->; exact Pw0|exact Hw]. }
      split.
      2:{ (* [comment removed for export] *)
        cbn [vr_cells r2 set_rnul set_cells]. intros kk ww ee Hin. destruct BEL2 as (_ & BR & _). pose proof (proj1 (proj2 (BR r0 Hr))) as CB.
        unfold cells in Hin. destruct (lo =? hi).
        - unfold sh_write in Hin. replace (lin_is_const (lconst b0)) with true in Hin by reflexivity.
          destruct (sh_ins_in _ _ _ _ _ _ _ (proj1 Hn) (POS _) Hin) as [Hin'|(Hv & _)]; [|injection Hv as ->; apply lin_below_lconst].
          apply sh_cut_in in Hin' as (k0 & w0 & Hold & _). exact (CB _ _ _ Hold).
        - apply sh_cut_in in Hin as (k0 & w0 & Hold & _). exact (CB _ _ _ Hold). }
      eapply (region_ok_self A _ nu mem mem' r0 r2 HE ROK SH2 ND).
      + apply wbytes_grows.
      + rewrite KS. exact I.
      + intros s0 ro G _ _. cbn [vs_rgn]. exact (shape_map_get _ _ _ _ SM2 G).
      + rewrite KS. exact I.
      + rewrite KS. exact I.
      + (* [comment removed for export] *)
        cbn [vr_cells r2 set_rnul set_cells]. intros c cw cv Hin. unfold cells in Hin.
        destruct (Z.eqb_spec lo hi) as [Elh|Nlh].
        * unfold sh_write in Hin. replace (lin_is_const (lconst b0)) with true in Hin by reflexivity. rewrite ISH.
          refine (sh_ins_cells nu mem' r0 lo n b0 _ ltac:(lia) ltac:(lia) ltac:(lia) _ _ c cw cv Hin).
          -- intros c' cw' cv' X. pose proof (CUT _ c' cw' cv' (or_introl eq_refl) (fun _ => Elh) X) as Y. rewrite ISH in Y. exact Y.
          -- intros i Hi. destruct (BYTE (Z.to_nat i) ltac:(lia)) as (kb & R1 & R2). exists kb. split; [|exact R2].
             replace (rbase nu r0 + lo + i) with (a + Z.of_nat (Z.to_nat i)) by (unfold a; lia). exact R1.
        * eapply CUT; [right; reflexivity|intros X; lia|exact Hin].
      + (* [comment removed for export] *) cbn. intros ? ? [].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma wbytes1_at mem (a : word) (b : byte) : wbytes mem a [b] a = Some b.
  Proof using . cbn [wbytes]. rewrite bv_eqb_refl. reflexivity. Qed.

  Lemma store_flag_sound A nu regs mem pc rom w sz (rs1 rs2 : reg) (imm : bv 12) addr r off lo hi succs owner :
    gamma2P A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Store sz rs1 rs2 imm, 4) ->
    addr_of (v1 A) (rz rs1) (bv_signed imm) = Some addr ->
    classify2 A addr (msize_z sz) true = Some (C2Rgn r off lo hi) ->
    vr_kind r = RK_flag owner ->
    store_rgn A r off lo hi (msize_z sz) (get_reg (v1 A) (rz rs2)) = VR2_next succs ->
    step_post2 SEGS P E mem0 A nu succs regs mem pc rom.
  Proof using PO2.
    intros HG2 Hpc Hf He Hd Ha CL KF ST.
    pose proof HG2 as (HG1 & HE & HM & HF2 & HDD & RGN & LIVE & BEL2 & GL2 & FI2 & _).
    pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    pose proof (msize_pos sz) as Hn. set (n := msize_z sz) in *.
    destruct (classify2_rgn A addr n true r off lo hi CL) as (B & r0 & HB & HC & HR0 & HCL).
    destruct (classify_rgn_sound A nu r0 addr n true r off lo hi HL ltac:(lia) HCL) as (-> & Eoff & Eaddr & NDS & DSH).
    pose proof (rgn_in _ _ _ HR0) as Hr.
    assert (ND : is_data_shadow r0 = false) by (unfold is_data_shadow; rewrite KF; reflexivity).
    destruct (NDS ND) as (Hlohi & Hlo & Hhi & HW). specialize (HW eq_refl).
    pose proof (RGN r0 Hr) as ROK. pose proof ROK as (RB1 & RB2 & RB3 & RDS & CELLS & PERM & NUL & KIND).
    pose proof (gamma_get_reg SEGS P1 E1 (zpatch P E mem0 mem) (v1 A) nu regs mem rs2 HG1) as [Wv Bv].
    set (val := get_reg (v1 A) (rz rs2)) in *. set (wv := getr regs rs2) in *.
    (* [comment removed for export] *)
    unfold store_rgn in ST. rewrite KF in ST.
    destruct ((n =? 1) && (lo =? 0) && (hi =? 0) && is_zero_byte (v1 A) val) eqn:COND; [|discriminate].
    apply andb_prop in COND as [COND ZB]. apply andb_prop in COND as [COND H0]. apply andb_prop in COND as [N1 L0].
    apply Z.eqb_eq in N1. apply Z.eqb_eq in L0. apply Z.eqb_eq in H0.
    assert (EO : eval nu off = 0) by lia.
    set (keep := fun x : vregion => negb (Pos.eqb (vr_base x) owner)
                                     && negb (match vr_kind x with
                                              | RK_shadow s0 => Pos.eqb s0 owner
                                              | RK_flag o => Pos.eqb o owner
                                              | _ => false end)).
    set (l' := List.filter keep (vs_rgn A)).
    set (live' := List.filter (fun s0 => negb (Pos.eqb s0 owner)) (vs_live A)).
    set (A' := mkVS2 (set_pc (v1 A) (npc_of (v1 A))) l' live' (vs_divdef A) []).
    assert (ES : succs = [A']) by (injection ST as <-; reflexivity). rewrite ES. clear ST ES.
    set (a := rbase nu r0).
    set (mem' := wbytes mem (wordZ a) (word_to_le_bytes 1 wv)).
    (* [comment removed for export] *)
    destruct (region_desc A nu regs mem r0 HG2 Hr ND) as (d1 & V1 & M1 & D1).
    unfold desc_matches in M1. rewrite KF in M1. destruct d1 as [|c p| | |]; try contradiction.
    destruct M1 as (ro & fl & Gro & KO & Bfl & RBo & FLo & NLo). cbn in V1.
    destruct (rgn_get_in _ _ _ Gro) as [Hro Bro].
    assert (Ea : a = flag_addr FS c p).
    { unfold kind_ok in KIND. rewrite KF in KIND. destruct KIND as (_ & _ & Hdisp & _). unfold a, rbase. rewrite Hdisp, Bfl, FLo. lia. }
    (* [comment removed for export] *)
    destruct (PERM ND) as [RD WR].
    apply in_ranges_sound in HW as (wlo & whi & HWin & W1 & W2).
    destruct (WR wlo whi 0 HWin ltac:(lia)) as (X1 & X2 & X3 & X4). rewrite Z.add_0_r in X2, X3, X4. fold a in X2, X3, X4.
    assert (FSnz : vp_fs P <> None) by exact (asan_of_rw _ X2).
    pose proof (layout_of_env HE FSnz) as L.
    assert (Hab : 0 <= a < 2 ^ 64 /\ a + 1 <= 2 ^ 64).
    { pose proof (dbyte_side FS SP0v FRAME SHOFF (DFlag c p) a L ltac:(cbn; lia) ltac:(cbn; exact Ea)) as S. cbn in S.
      unfold HIGH_MEM_BEG, HIGH_MEM_END in S. lia. }
    assert (Hlen : length (word_to_le_bytes 1 wv) = 1%nat) by apply length_N_to_le_bytes.
    (* [comment removed for export] *)
    assert (Hbz : bv_unsigned wv mod 256 = 0).
    { apply (is_zero_byte_sound mem0 (v1 A) nu val wv HL ZB). subst val.
      destruct (get_reg (v1 A) (rz rs2)) as [ev|]; [exact (wval_some _ _ _ Wv)|]. unfold is_zero_byte in ZB. discriminate. }
    assert (MB : mem' (wordZ a) = Some (Z_to_bv 8 (bv_unsigned wv)) /\ bv_unsigned (Z_to_bv 8 (bv_unsigned wv)) = 0).
    { split; [unfold mem'; cbn [word_to_le_bytes Z_to_le_bytes]; apply wbytes1_at|].
      rewrite Z_to_bv_unsigned, bv_wrap8_mod. exact Hbz. }
    (* [comment removed for export] *)
    pose proof (store_machine A nu regs mem pc rom w sz rs1 rs2 imm addr a HG2 Hf He Hd Ha
                  ltac:(unfold a; lia) ltac:(lia) ltac:(lia) ltac:(intros i Hi; replace (a + i) with a by lia; exact X3)) as STEP.
    fold wv in STEP. replace (Z.to_nat (msize_z sz)) with 1%nat in STEP by lia.
    change (wbytes mem (wordZ a) (word_to_le_bytes 1 wv)) with mem' in STEP.
    (* [comment removed for export] *)
    pose proof LIVE as (LV1 & LV2 & LV3 & ND0).
    assert (INl' : forall x, In x l' <-> In x (vs_rgn A) /\ vr_base x <> owner /\
                     match vr_kind x with RK_shadow s0 => s0 <> owner | RK_flag o => o <> owner | _ => True end).
    { intros x. unfold l'. rewrite filter_In. unfold keep. rewrite andb_true_iff, !negb_true_iff.
      split.
      - intros (I1 & I2 & I3). split; [exact I1|]. split; [intros EQ; rewrite EQ, Pos.eqb_refl in I2; discriminate|].
        destruct (vr_kind x); auto; intros EQ; rewrite EQ, Pos.eqb_refl in I3; discriminate.
      - intros (I1 & I2 & I3). split; [exact I1|]. split; [destruct (Pos.eqb_spec (vr_base x) owner); [contradiction|reflexivity]|].
        destruct (vr_kind x) as [| |o3|s3|]; try reflexivity;
          [destruct (Pos.eqb_spec o3 owner); [contradiction|reflexivity]
          |destruct (Pos.eqb_spec s3 owner); [contradiction|reflexivity]]. }
    assert (RO : forall x, In x (vs_rgn A) -> match vr_kind x with RK_fake _ _ => True | _ => False end ->
                 rbase nu x = frame_addr FS c p -> x = ro).
    { intros x Hx Kx EQ. destruct (Pos.eq_dec (vr_base x) (vr_base ro)) as [EB|NB]; [exact (live_ok_base_inj nu A x ro LIVE Hx Hro EB)|].
      exfalso. specialize (LV3 x ro Hx Hro). rewrite KO in LV3. destruct (vr_kind x); try contradiction. apply (LV3 NB). congruence. }
    (* [comment removed for export] *)
    assert (OFA : forall y, In y (own_flags A' nu) <-> In y (own_flags A nu) /\ y <> a).
    { intros y. unfold own_flags, A'. cbn [vs_rgn]. rewrite !in_flat_map. split.
      - intros (x & Hx & Hy). apply INl' in Hx as (I1 & I2 & I3). split; [exists x; auto|].
        destruct (vr_kind x) as [cx fx| | | |] eqn:Kx; try (destruct Hy; fail). destruct Hy as [<-|[]].
        intros EQ.
        destruct (region_desc A nu regs mem x HG2 I1 ltac:(unfold is_data_shadow; rewrite Kx; reflexivity)) as (dx & Vx & Mx & Dx).
        unfold desc_matches in Mx. rewrite Kx in Mx. destruct dx as [cx' px| | | |]; try contradiction.
        destruct Mx as (Ecx & RBx & FLx & NLx). subst cx'. cbn in Vx.
        rewrite Ea, FLx in EQ. destruct (flag_addr_inj FS cx px c p ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) EQ) as [-> ->].
        apply I2. rewrite (RO x I1 ltac:(rewrite Kx; exact I) RBx). exact Bro.
      - intros [(x & Hx & Hy) NE]. exists x. split; [|exact Hy]. apply INl'. split; [exact Hx|].
        destruct (vr_kind x) as [cx fx| | | |] eqn:Kx; try (destruct Hy; fail). destruct Hy as [<-|[]].
        split; [|exact I]. intros EB. apply NE.
        rewrite (live_ok_base_inj nu A x ro LIVE Hx Hro ltac:(rewrite EB, Bro; reflexivity)) in Kx.
        rewrite KO in Kx. injection Kx as _ <-. unfold a, rbase.
        unfold kind_ok in KIND. rewrite KF in KIND. destruct KIND as (_ & _ & Hdisp & _). rewrite Hdisp, Bfl. lia. }
    exists regs, (v_addi pc 4), mem', A', nu.
    split; [exact STEP|]. split; [left; reflexivity|]. split.
    { unfold A', vs2_pc. cbn [v1]. unfold npc_of, v_addi. rewrite u_Z_to_bv64, wrap64_zwrap. unfold vs2_pc in Hpc. rewrite Hpc. reflexivity. }
    split; [apply ext_refl|]. split; [unfold A', vs2_next; cbn [v1]; apply Pos.le_refl|].
    split.
    { (* [comment removed for export] *)
      split; [|apply wbytes_grows]. intros z Hout. rewrite <- (wordZ_u z). unfold mem'.
      pose proof (u64_range z).
      apply wblock_byte; rewrite ?Hlen; try lia. intros IN.
      assert (EZ : bv_unsigned z = a) by lia.
      apply (covered_not_outside _ _ X4 ltac:(lia)). rewrite <- EZ, wordZ_u. exact Hout. }
    assert (FSTEP : flags_step P E A A' nu nu mem mem').
    { (* [comment removed for export] *)
      intros y Hy. destruct (Z.eq_dec y a) as [->|NE].
      - right; right. split; [|split; [intros IN; apply OFA in IN as [_ NE]; exact (NE eq_refl)|]].
        + unfold own_flags. rewrite in_flat_map. exists ro. split; [exact Hro|]. rewrite KO. left. rewrite Ea, FLo. reflexivity.
        + destruct MB as [MB1 MB2]. eexists. split; [exact MB1|exact MB2].
      - left. split; [rewrite OFA; tauto|].
        unfold in_flags_zone in Hy. destruct (vp_fs P) as [[len ssl]|] eqn:Efs; [|destruct Hy].
        pose proof L as (L1 & L2 & _). unfold HIGH_MEM_BEG, HIGH_MEM_END, FS_FRAMES, FS_NCLASSES, FS_SSL, FS_FLAGS in *.
        unfold mem'. apply wblock_byte; rewrite ?Hlen; lia. }
    split; [exact FSTEP|].
    (* [comment removed for export] *)
    split.
    { unfold A'. cbn [v1]. unfold mem'. apply zone_write_v1; rewrite ?Hlen; try lia; [exact HE| |exact HG1|].
      - intros g gw gv Hin. apply (GL2 ltac:(unfold asan_mode; destruct (vp_fs P); [reflexivity|exfalso; exact (FSnz eq_refl)]) g gw gv Hin).
      - intros i Hi. replace (a + i) with a by lia. exact X2. }
    split; [exact HE|]. split.
    { unfold mem'. apply MC2_zone_write; rewrite ?Hlen; try lia; [exact HE|exact HM| |].
      - intros i Hi. replace (a + i) with a by lia. exact X2.
      - intros [c' p'] y Hcp Hy EQ. cbn in EQ. pose proof (live_valid _ HE FSnz Hcp) as [Vc Vp]. cbn in Vc, Vp.
        assert (Hya : y = a) by lia. rewrite Hya, Ea in EQ.
        destruct (flag_addr_inj FS c p c' p' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) EQ) as [<- <-]. exact (NLo Hcp). }
    split; [exact HF2|]. split; [exact HDD|]. split.
    { (* [comment removed for export] *)
      intros r2 Hr2. pose proof Hr2 as Hr2'. apply INl' in Hr2 as (I1 & I2 & I3).
      unfold mem'. apply (region_ok_transport A A' nu mem a _ r2 r2 HE (RGN r2 I1) (rshape_refl r2)); rewrite ?Hlen; try lia.
      - left. split; [reflexivity|]. split; [reflexivity|]. intros ND2 y Hy IN.
        assert (Hya : y = a) by lia. rewrite Hya in Hy. clear IN Hya.
        destruct (region_desc A nu regs mem r2 HG2 I1 ND2) as (d2 & V2 & M2 & D2).
        assert (B2y : dbyteP d2 a) by (replace a with (rbase nu r2 + (a - rbase nu r2)) by lia; apply D2; lia).
        assert (ED : d2 = DFlag c p).
        { symmetry. apply (dbyte_disjoint FS SP0v FRAME SHOFF (DFlag c p) d2 a L ltac:(cbn; lia) V2 ltac:(cbn; exact Ea) B2y). }
        subst d2. unfold desc_matches in M2. destruct (vr_kind r2) as [| |o2| |] eqn:K2; try contradiction.
        destruct M2 as (ro2 & fl2 & G2 & KO2 & B2 & RBo2 & FL2 & NL2).
        destruct (rgn_get_in _ _ _ G2) as [Hro2 Bro2].
        apply I3. rewrite <- Bro2. rewrite (RO ro2 Hro2 ltac:(rewrite KO2; exact I) RBo2). exact Bro.
      - destruct (vr_kind r2) as [c2 fl2| | | |] eqn:K2; auto. intros IN. assert (EQ : nu fl2 = a) by lia.
        destruct (region_desc A nu regs mem r2 HG2 I1 ltac:(unfold is_data_shadow; rewrite K2; reflexivity)) as (d2 & V2 & M2 & D2).
        unfold desc_matches in M2. rewrite K2 in M2. destruct d2 as [c2' p2| | | |]; try contradiction.
        destruct M2 as (Ec2 & RBo2 & FL2 & NL2). subst c2'. cbn in V2.
        rewrite Ea, FL2 in EQ. destruct (flag_addr_inj FS c2 p2 c p ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) EQ) as [-> ->].
        apply I2. rewrite (RO r2 I1 ltac:(rewrite K2; exact I) RBo2). exact Bro.
      - intros s0 rx G Kx Ks. exists rx. split; [|apply rshape_refl].
        destruct (rgn_get_in _ _ _ G) as [Hrx Brx]. unfold A'. cbn [vs_rgn]. unfold l'. rewrite <- Brx.
        apply rgn_get_filter_keep; [exact ND0|exact Hrx|]. unfold keep.
        assert (NSO : s0 <> owner) by (destruct (vr_kind r2); try contradiction; subst; exact I3).
        rewrite Brx. destruct (Pos.eqb_spec s0 owner); [contradiction|]. destruct (vr_kind rx); try contradiction; reflexivity.
      - destruct (vr_kind r2) eqn:K2; auto. unfold A'. cbn [vs_live]. unfold live'. apply filter_In. split.
        + apply (proj2 (LV1 (vr_base r2))). exists r2. rewrite K2. auto.
        + destruct (Pos.eqb_spec (vr_base r2) owner); [contradiction|reflexivity]. }
    split.
    { (* [comment removed for export] *)
      unfold A'. split; [|split; [|split]]; cbn [vs_rgn vs_live].
      - intros s0. unfold live'. rewrite filter_In, LV1. split.
        + intros [(x & Hx & Bx & Kx) NB]. exists x. split; [|auto]. apply INl'. split; [exact Hx|].
          destruct (vr_kind x); try contradiction. split; [|exact I]. rewrite Bx.
          destruct (Pos.eqb_spec s0 owner); [discriminate|assumption].
        + intros (x & Hx & Bx & Kx). apply INl' in Hx as (I1 & I2 & I3). split; [exists x; auto|].
          rewrite <- Bx. destruct (Pos.eqb_spec (vr_base x) owner); [contradiction|reflexivity].
      - unfold live'. apply (proj2 (NoDup_ListNoDup _)). apply NoDup_filter. apply (proj1 (NoDup_ListNoDup _)). exact LV2.
      - intros r1 r2 H1 H2. apply INl' in H1 as (I1 & _). apply INl' in H2 as (I2 & _). exact (LV3 r1 r2 I1 I2).
      - unfold l'. apply nodup_map_filter. exact ND0. }
    split.
    { (* [comment removed for export] *)
      destruct BEL2 as (BF & BR & BL & BD & BM). unfold A'. cbn [v1 vs_rgn vs_live vs_divdef vs_memo].
      replace (vs_next (set_pc (v1 A) (npc_of (v1 A)))) with (vs_next (v1 A)) by reflexivity.
      split; [exact BF|]. split; [|split; [|split; [exact BD|intros ma mn mv []]]].
      - intros x Hx. apply INl' in Hx as (I1 & _). exact (BR x I1).
      - intros s0 Hs. unfold live' in Hs. apply filter_In in Hs as [Hs _]. exact (BL s0 Hs). }
    split; [unfold globs_ok2, A'; cbn [v1]; exact GL2|].
    split; [exact (flags_inv_step P E A A' nu nu mem mem' FI2 FSTEP)|].
    intros ma mn mv [].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem x_store2_sound A nu regs mem pc rom w sz (rs1 rs2 : reg) (imm : bv 12) succs :
    gamma2P A nu regs mem -> vs2_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false -> decode_any w = Some (Store sz rs1 rs2 imm, 4) ->
    x_store2 P A sz (rz rs1) (rz rs2) (bv_signed imm) = VR2_next succs ->
    forallb (globs_in_fcells P) succs = true ->
    step_post2 SEGS P E mem0 A nu succs regs mem pc rom.
  Proof using PO2.
    intros HG2 Hpc Hf He Hd Hx GLB. pose proof (gamma2_lgamma _ _ _ _ _ _ _ _ HG2) as HL.
    unfold x_store2 in Hx.
    destruct (addr_of (v1 A) (rz rs1) (bv_signed imm)) as [addr|] eqn:Ha; [|discriminate].
    destruct (classify2 A addr (msize_z sz) true) as [[r off lo hi| |m]|] eqn:CL.
    - destruct (vr_kind r) as [cid fl| |owner|sb|] eqn:K.
      + eapply store_generic_sound; eauto. rewrite K. exact I.
      + eapply store_generic_sound; eauto. rewrite K. exact I.
      + eapply store_flag_sound; eauto.
      + eapply store_shadow_sound; eauto.
      + eapply store_generic_sound; eauto. rewrite K. exact I.
    - exfalso. eapply classify2_dead; eauto.
    - discriminate.
    - assert (LI : exists l, x_store P1 (v1 A) sz (rz rs1) (rz rs2) (bv_signed imm) = VR_next l /\ succs = map (with_v1c A) l).
      { change (p1 P) with P1 in Hx. destruct (x_store P1 (v1 A) sz (rz rs1) (rz rs2) (bv_signed imm)) as [l0|m0]; cbn [lift1c] in Hx; [|discriminate].
        exists l0. split; [reflexivity|]. injection Hx as <-. reflexivity. }
      destruct LI as (l & Hl & ->).
      eapply (step_post_liftc SEGS P E mem0 PO2); [exact HG2| |].
      + intros x Hxl. apply globs_in_fcells_sound. rewrite forallb_forall in GLB.
        change (globs_in_fcells P (with_v1 A x)) with (globs_in_fcells P (with_v1c A x)). apply GLB. apply in_map. exact Hxl.
      + assert (Hl' : vstep P1 (v1 A) (Store sz rs1 rs2 imm) = VR_next l) by (cbn [vstep vstep_core]; rewrite bvs_eq; exact Hl).   (* [comment removed for export] *)
        eapply (vstep_sound SEGS P1 E1 (zpatch P E mem0 mem) (PO1 _ _ PO2)); eauto. exact (proj1 HG2).
  Qed.
End C.
