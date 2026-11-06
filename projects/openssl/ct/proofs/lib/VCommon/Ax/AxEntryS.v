(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import PrimString.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec FastWord.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AsanWEntry AsanWEb.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Cli Require Import CliVerdict.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxAcct AxMeasure.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxBytes AxImg AxMem AxZZ AxState AxSys AxEntryRel AxEntry.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxFd AxModelRel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition chk (c : PrimString.string) (x : int) : bool := match fimg_c c x with Some _ => true | None => false end.

(* [comment removed for export] *)
Fixpoint scanI (c : PrimString.string) (fuel : nat) (base n : int) : bool :=
  match fuel with
  | O => (n =? 0)%uint63
  | S f =>
      if (n =? 0)%uint63 then true
      else if (n =? 1)%uint63 then chk c base
      else let h := (n >> 1)%uint63 in scanI c f base h &&& scanI c f (base + h) (n - h)
  end.

Lemma scanI_sound (c : PrimString.string) (fuel : nat) : forall base n : int,
  to_Z base + to_Z n < 2 ^ 62 -> scanI c fuel base n = true ->
  forall i, 0 <= i < to_Z n -> fimg_c c (of_Z (to_Z base + i)) <> None.
Proof.
  induction fuel as [|f IH]; intros base n Hb H i Hi; cbn [scanI] in H.
  - apply Uint63.eqb_spec in H. subst n. change (to_Z 0%uint63) with 0 in Hi. lia.
  - pose proof (to_Z_bounded base) as Bb. pose proof (to_Z_bounded n) as Bn. change wB with (2 ^ 63) in *.
    destruct (n =? 0)%uint63 eqn:E0; [apply Uint63.eqb_spec in E0; subst n; change (to_Z 0%uint63) with 0 in Hi; lia|].
    destruct (n =? 1)%uint63 eqn:E1.
    + apply Uint63.eqb_spec in E1. subst n. change (to_Z 1%uint63) with 1 in Hi. replace i with 0 by lia.
      rewrite Z.add_0_r, of_to_Z. unfold chk in H. destruct (fimg_c c base); [discriminate | discriminate].
    + destruct (scanI c f base (n >> 1)) eqn:Ea; [|discriminate].
      assert (Hh : to_Z (n >> 1)%uint63 = to_Z n / 2).
      { rewrite lsr_spec. change (to_Z 1%uint63) with 1. change (2 ^ 1) with 2. reflexivity. }
      assert (Hh2 : 0 <= to_Z n / 2 <= to_Z n) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
      destruct (Z_lt_ge_dec i (to_Z n / 2)) as [L|L].
      * apply (IH base (n >> 1)%uint63); [rewrite Hh; lia | exact Ea | rewrite Hh; lia].
      * assert (Eb : to_Z (base + (n >> 1))%uint63 = to_Z base + to_Z n / 2)
          by (rewrite add_spec, Hh; change wB with (2 ^ 63); apply Z.mod_small; lia).
        assert (En : to_Z (n - (n >> 1))%uint63 = to_Z n - to_Z n / 2)
          by (rewrite sub_spec, Hh; change wB with (2 ^ 63); apply Z.mod_small; lia).
        specialize (IH (base + (n >> 1))%uint63 (n - (n >> 1))%uint63 ltac:(rewrite Eb, En; lia) H (i - to_Z n / 2) ltac:(rewrite En; lia)).
        rewrite Eb in IH. replace (to_Z base + to_Z n / 2 + (i - to_Z n / 2)) with (to_Z base + i) in IH by lia. exact IH.
Qed.

(* [comment removed for export] *)
Definition seg_ok1 (sg : Segment) : bool :=
  match seg_bytes sg with
  | [c] =>
      let n := Z.of_N (seg_size sg) in
      (0 <? n) &&& (n <? 1099511627776) &&& (Z.of_N (seg_base sg) + n <=? ls_beg) &&& seg_readable sg
      &&& (Z.of_N (seg_base sg) mod 4096 =? 0) &&& (n mod 4096 =? 0) &&& scanI c 64 0 (of_Z n)
  | _ => false
  end.

Definition seg_disj (a b : Segment) : bool :=
  (Z.of_N (seg_base a) + Z.of_N (seg_size a) <=? Z.of_N (seg_base b)) ||| (Z.of_N (seg_base b) + Z.of_N (seg_size b) <=? Z.of_N (seg_base a)).

Fixpoint segs_pw (segs : list Segment) : bool :=
  match segs with
  | [] => true
  | sg :: r => forallb (seg_disj sg) r &&& segs_pw r
  end.

Definition img_ok (segs : list Segment) (pc : N) : bool :=
  forallb seg_ok1 segs &&& segs_pw segs &&& (Z.of_N pc mod 4 =? 0) &&& (Z.of_N pc <? 67108864).

Lemma seg_ok1_facts (sg : Segment) : seg_ok1 sg = true ->
  exists c, seg_bytes sg = [c] /\ 0 < Z.of_N (seg_size sg) < 2 ^ 40 /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= ls_beg
            /\ seg_readable sg = true /\ Z.of_N (seg_base sg) mod 4096 = 0 /\ Z.of_N (seg_size sg) mod 4096 = 0
            /\ scanI c 64 0 (of_Z (Z.of_N (seg_size sg))) = true.
Proof.
  unfold seg_ok1. destruct (seg_bytes sg) as [|c [|c' r]]; try discriminate. cbv zeta. intros H. exists c.
  destruct (0 <? Z.of_N (seg_size sg)) eqn:E1; [|discriminate]. destruct (Z.of_N (seg_size sg) <? 1099511627776) eqn:E2; [|discriminate].
  destruct (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? ls_beg) eqn:E3; [|discriminate].
  destruct (seg_readable sg) eqn:E4; [|discriminate].
  destruct (Z.of_N (seg_base sg) mod 4096 =? 0) eqn:E5; [|discriminate]. destruct (Z.of_N (seg_size sg) mod 4096 =? 0) eqn:E6; [|discriminate].
  apply Z.ltb_lt in E1. apply Z.ltb_lt in E2. apply Z.leb_le in E3. apply Z.eqb_eq in E5. apply Z.eqb_eq in E6.
  change (2 ^ 40) with 1099511627776. repeat split; try assumption; lia.
Qed.

Lemma img_ok_parts (segs : list Segment) (pc : N) : img_ok segs pc = true ->
  forallb seg_ok1 segs = true /\ segs_pw segs = true /\ Z.of_N pc mod 4 = 0 /\ Z.of_N pc < 2 ^ 26.
Proof.
  unfold img_ok. intros H. destruct (forallb seg_ok1 segs); [|discriminate]. destruct (segs_pw segs); [|discriminate].
  destruct (Z.of_N pc mod 4 =? 0) eqn:E1; [|discriminate]. apply Z.eqb_eq in E1. apply Z.ltb_lt in H.
  change (2 ^ 26) with 67108864. repeat split; assumption.
Qed.

Lemma img_ok_seg (segs : list Segment) (pc : N) (sg : Segment) : img_ok segs pc = true -> In sg segs -> seg_ok1 sg = true.
Proof. intros H Hin. destruct (img_ok_parts segs pc H) as [Hf _]. rewrite forallb_forall in Hf. exact (Hf sg Hin). Qed.

Lemma img_low (segs : list Segment) (pc : N) : img_ok segs pc = true -> segs_low segs.
Proof. intros H sg Hin. destruct (seg_ok1_facts sg (img_ok_seg segs pc sg H Hin)) as (c & _ & _ & Hl & _). exact Hl. Qed.

(* [comment removed for export] *)
Lemma seg_disj_spec (a b : Segment) : seg_disj a b = true ->
  Z.of_N (seg_base a) + Z.of_N (seg_size a) <= Z.of_N (seg_base b) \/ Z.of_N (seg_base b) + Z.of_N (seg_size b) <= Z.of_N (seg_base a).
Proof.
  unfold seg_disj. destruct (Z.of_N (seg_base a) + Z.of_N (seg_size a) <=? Z.of_N (seg_base b)) eqn:E; [apply Z.leb_le in E; left; exact E|].
  intros H. apply Z.leb_le in H. right. exact H.
Qed.

Lemma find_seg_pw (segs : list Segment) : segs_pw segs = true -> forall (i : nat) (sg : Segment) (a : Z),
  nth_error segs i = Some sg -> Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg) ->
  find_segment segs a 1 = Some sg.
Proof.
  induction segs as [|s0 r IH]; intros Hpw i sg a Hn Ha; [destruct i; discriminate|].
  cbn [segs_pw] in Hpw. destruct (forallb (seg_disj s0) r) eqn:Ed; [|discriminate]. cbn [find_segment].
  destruct i as [|i]; cbn [nth_error] in Hn.
  - injection Hn as ->. replace (Z.leb (Z.of_N (seg_base sg)) a && Z.leb (a + 1) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) with true; [reflexivity|].
    symmetry. apply andb_true_iff. split; apply Z.leb_le; lia.
  - rewrite forallb_forall in Ed. pose proof (seg_disj_spec s0 sg (Ed sg (nth_error_In _ _ Hn))) as Hd.
    replace (Z.leb (Z.of_N (seg_base s0)) a && Z.leb (a + 1) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) with false;
      [exact (IH Hpw i sg a Hn Ha)|].
    symmetry. apply andb_false_iff. destruct Hd; [right | left]; apply Z.leb_gt; lia.
Qed.

(* [comment removed for export] *)
Lemma img_byte (segs : list Segment) (pc : N) (m : word -> option byte) (i : nat) (sg : Segment) (y : int) :
  img_ok segs pc = true -> nth_error segs i = Some sg -> to_Z y < Z.of_N (seg_size sg) ->
  m (wz (Z.of_N (seg_base sg) + to_Z y)) = None ->
  exists b, fimg_i segs i y = Some b /\ rv segs m (wz (Z.of_N (seg_base sg) + to_Z y)) = Some (Z_to_bv 8 (to_Z b)) /\ to_Z b < 256
            /\ (seg_writable sg = true -> wview segs m (wz (Z.of_N (seg_base sg) + to_Z y)) <> None).
Proof.
  intros Hok Hn Hy Hm. pose proof (to_Z_bounded y) as By.
  destruct (seg_ok1_facts sg (img_ok_seg segs pc sg Hok (nth_error_In _ _ Hn))) as (c & Hc & Hsz & Hl & Hr & _ & _ & Hscan).
  destruct (img_ok_parts segs pc Hok) as (_ & Hpw & _).
  assert (Hnz : to_Z (of_Z (Z.of_N (seg_size sg))) = Z.of_N (seg_size sg)) by (rewrite of_Z_spec; apply Z.mod_small; change wB with (2 ^ 63); lia).
  pose proof (scanI_sound c 64 0%uint63 _ ltac:(rewrite Hnz; change (to_Z 0%uint63) with 0; lia) Hscan (to_Z y) ltac:(rewrite Hnz; lia)) as Hb.
  change (to_Z 0%uint63) with 0 in Hb. rewrite Z.add_0_l, of_to_Z in Hb.
  destruct (fimg_c c y) as [b|] eqn:Eb; [|congruence]. exists b.
  assert (Ei : fimg_i segs i y = Some b) by (unfold fimg_i; rewrite Hn, Hc; exact Eb).
  pose proof (find_seg_pw segs Hpw i sg (Z.of_N (seg_base sg) + to_Z y) Hn ltac:(lia)) as Hf.
  unfold ls_beg in Hl.
  split; [exact Ei|]. split.
  - unfold rv. rewrite Hm. unfold wz. exact (fimg_i_rom segs i y b sg Hn Ei Hf Hr ltac:(lia)).
  - split; [exact (proj2 (fimg_i_spec segs i y b sg Hn Ei))|].
    intros Hw. unfold wz. exact (fimg_i_wview segs m i y b sg Hn Ei Hf Hw ltac:(lia)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma regions_ok_app (ρ : valuation) (A B : list region) :
  regions_ok ρ A -> regions_ok ρ B -> (forall R, In R A -> Forall (rdisj ρ R) B) -> regions_ok ρ (A ++ B).
Proof.
  induction A as [|R A IH]; intros HA HB HAB; [exact HB|]. cbn [app regions_ok] in *.
  destruct HA as (Hwf & Hd & HA). split; [exact Hwf|]. split.
  - apply Forall_app. split; [exact Hd | apply HAB; left; reflexivity].
  - apply IH; [exact HA | exact HB | intros R' HR'; apply HAB; right; exact HR'].
Qed.

Lemma to_Z_of_Z_n (z : Z) : 0 <= z < 2 ^ 62 -> to_Z (of_Z z) = z.
Proof. intros H. rewrite of_Z_spec. apply Z.mod_small. change wB with (2 ^ 63). lia. Qed.

Lemma rbase_img (ρ : valuation) (i : nat) (sg : Segment) : Z.of_N (seg_base sg) < two64 -> rbase ρ (img_region i sg) = Z.of_N (seg_base sg).
Proof.
  intros H. unfold rbase, img_region, smod. cbn [rg_ts rg_bo teval]. rewrite wZ_wofZ, Z.add_0_l, Z.mod_mod by (unfold two64; lia).
  apply Z.mod_small. lia.
Qed.

Section Geom.
Variables (segs : list Segment) (pc : N) (ρ : valuation).
Hypothesis Hok : img_ok segs pc = true.

Lemma img_region_facts (i : nat) (sg : Segment) : In sg segs ->
  rbase ρ (img_region i sg) = Z.of_N (seg_base sg) /\ to_Z (rg_n (img_region i sg)) = Z.of_N (seg_size sg)
  /\ region_wf ρ (img_region i sg) /\ 0 < Z.of_N (seg_size sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= ls_beg.
Proof.
  intros Hin. destruct (seg_ok1_facts sg (img_ok_seg segs pc sg Hok Hin)) as (c & _ & Hsz & Hl & _).
  unfold ls_beg in Hl.
  assert (Eb : rbase ρ (img_region i sg) = Z.of_N (seg_base sg)) by (apply rbase_img; unfold two64; lia).
  assert (En : to_Z (rg_n (img_region i sg)) = Z.of_N (seg_size sg)) by (cbn [img_region rg_n]; apply to_Z_of_Z_n; lia).
  split; [exact Eb|]. split; [exact En|]. split; [|unfold ls_beg; lia].
  unfold region_wf. rewrite Eb, En. destruct (depth_for_spec (Z.of_N (seg_size sg)) ltac:(lia)) as [D1 D2].
  split; [unfold two64; lia|]. split; [lia|]. split; [exact D2|]. split; [exact D1|]. intros w j _. reflexivity.
Qed.

Lemma disj_from (i : nat) (sg : Segment) : In sg segs -> forall (r : list Segment) (j : nat),
  (forall x, In x r -> In x segs) -> (forall x, In x r -> seg_disj sg x = true) ->
  Forall (rdisj ρ (img_region i sg)) (img_regions_from j r).
Proof.
  intros Hin. destruct (img_region_facts i sg Hin) as (Eb & En & _).
  induction r as [|s' r IH]; intros j Hall Ed; [constructor|]. cbn [img_regions_from]. constructor.
  - destruct (img_region_facts j s' (Hall s' (or_introl eq_refl))) as (Eb' & En' & _).
    unfold rdisj. rewrite Eb, En, Eb', En'. exact (seg_disj_spec sg s' (Ed s' (or_introl eq_refl))).
  - apply IH; [intros x Hx; apply Hall; right; exact Hx | intros x Hx; apply Ed; right; exact Hx].
Qed.

Lemma regions_ok_from (l : list Segment) : (forall sg, In sg l -> In sg segs) -> segs_pw l = true ->
  forall i, regions_ok ρ (img_regions_from i l).
Proof.
  induction l as [|sg r IH]; intros Hall Hpw i; [exact I|]. cbn [img_regions_from regions_ok].
  cbn [segs_pw] in Hpw. destruct (forallb (seg_disj sg) r) eqn:Ed; [|discriminate]. rewrite forallb_forall in Ed.
  destruct (img_region_facts i sg (Hall sg (or_introl eq_refl))) as (_ & _ & Hwf & _).
  split; [exact Hwf|]. split.
  - apply disj_from; [apply Hall; left; reflexivity | intros x Hx; apply Hall; right; exact Hx | exact Ed].
  - apply IH; [intros x Hx; apply Hall; right; exact Hx | exact Hpw].
Qed.

Lemma regions_ok_imgs : regions_ok ρ (img_regions segs).
Proof. destruct (img_ok_parts segs pc Hok) as (_ & Hpw & _). apply regions_ok_from; [intros sg H; exact H | exact Hpw]. Qed.

Lemma in_img_regions (R : region) : In R (img_regions segs) -> exists i sg, nth_error segs i = Some sg /\ R = img_region i sg.
Proof.
  unfold img_regions. intros H.
  assert (G : forall l k, In R (img_regions_from k l) -> exists i sg, nth_error l i = Some sg /\ R = img_region (k + i) sg).
  { induction l as [|s r IH]; intros k Hk; [destruct Hk|]. cbn [img_regions_from] in Hk. destruct Hk as [<-|Hk].
    - exists 0%nat, s. split; [reflexivity | rewrite Nat.add_0_r; reflexivity].
    - destruct (IH (S k) Hk) as (i & sg & Hn & E). exists (S i), sg. split; [exact Hn | rewrite E; f_equal; lia]. }
  destruct (G segs 0%nat H) as (i & sg & Hn & E). exists i, sg. split; [exact Hn | exact E].
Qed.

End Geom.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition enc_b (inp : ProcInput) (sp : word) (draw : EntryDraw) (brk0 : word) : valuation :=
  enc inp sp draw (fun v => if (v =? 4)%uint63 then bv_unsigned brk0 / 4096 else 0).

Lemma enc_b_vb (inp : ProcInput) (sp : word) (draw : EntryDraw) (brk0 : word) : enc_b inp sp draw brk0 v_b = bv_unsigned brk0 / 4096.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Mem.
Variables (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp brk0 : word) (draw : EntryDraw) (inp : ProcInput).
Hypothesis Hinp : valid_input inp.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Hypothesis Himg : img_ok segs pc = true.

Notation ρ := (enc_b inp sp draw brk0).
Notation ms0 := (init_machine_state segs pc ph sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)).
Notation M0 := (ms_mem ms0).
Notation SP := (bv_unsigned sp).

Lemma sp_rng : sp_window_lo <= SP <= sp_window_hi /\ SP mod 16 = 0.
Proof. destruct Hsp as (H1 & H2 & H3). repeat split; assumption. Qed.

Lemma spv : sp_val ρ = SP.
Proof. apply sp_val_enc. exact (proj2 sp_rng). Qed.

Lemma span_fits : SP + Z.of_nat (ROn (in_argv inp) (in_envp inp)) + 16 < 2 ^ 64.
Proof.
  destruct Hinp as (Ha & He & _). pose proof (ROn_span (in_argv inp) (in_envp inp)) as Hro.
  unfold entry_stack_fits, sp_window_hi in Hfit. lia.
Qed.

(* [comment removed for export] *)
Lemma M0_dom (a : word) : M0 a <> None -> SP - stk_max <= bv_unsigned a < sp_window_hi.
Proof.
  intros H. pose proof (E7_domain segs pc ph sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) a H) as [D1 D2].
  pose proof (entry_page_top_within_window ph sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) draw Hfit) as Ht.
  unfold stk_max. unfold stack_max_size in D1. lia.
Qed.

Lemma M0_below (z : Z) : 0 <= z < SP - stk_max -> M0 (wz z) = None.
Proof.
  intros Hz. destruct (M0 (wz z)) as [b|] eqn:E; [|reflexivity]. exfalso.
  assert (H : M0 (wz z) <> None) by (rewrite E; discriminate). apply M0_dom in H.
  pose proof sp_rng as [[S1 S2] _]. unfold sp_window_lo, sp_window_hi, stk_max in *.
  unfold wz in H. rewrite Z_to_bv_unsigned, bv_wrap_small in H by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.

Lemma rbase_stk : rbase ρ stk_region = SP - stk_max.
Proof.
  unfold rbase, stk_region, zero_rg, smod. cbn [rg_ts rg_bo]. fold (sp_val ρ). rewrite spv, wZ_wofZ.
  pose proof sp_rng as [[S1 S2] _]. unfold sp_window_lo, sp_window_hi, stk_max, two64 in *.
  rewrite Zplus_mod_idemp_r. replace (SP + -8388608) with (SP - 8388608) by lia. apply Z.mod_small. lia.
Qed.

Lemma rbase_eb : rbase ρ (eb_region ph) = SP.
Proof.
  unfold rbase, eb_region, smod. cbn [rg_ts rg_bo]. fold (sp_val ρ). rewrite spv. change (wZ w_zero) with 0. rewrite Z.add_0_r.
  pose proof sp_rng as [[S1 S2] _]. unfold sp_window_lo, sp_window_hi, two64 in *. apply Z.mod_small. lia.
Qed.

Lemma n_stk : to_Z (rg_n stk_region) = stk_max. Proof. reflexivity. Qed.
Lemma n_eb : to_Z (rg_n (eb_region ph)) = eb_size. Proof. reflexivity. Qed.

Lemma wf_stk : region_wf ρ stk_region.
Proof.
  unfold region_wf. rewrite rbase_stk, n_stk. pose proof sp_rng as [[S1 S2] _]. unfold sp_window_lo, sp_window_hi, stk_max, two64 in *.
  destruct (depth_for_spec 8388608 ltac:(lia)) as [D1 D2].
  split; [lia|]. split; [lia|]. split; [exact D2|]. split; [exact D1|]. intros w i H. discriminate H.
Qed.

Lemma wf_eb : region_wf ρ (eb_region ph).
Proof.
  unfold region_wf. rewrite rbase_eb, n_eb. pose proof sp_rng as [[S1 S2] _]. unfold sp_window_lo, sp_window_hi, eb_size, two64 in *.
  destruct (depth_for_spec 2238672 ltac:(lia)) as [D1 D2].
  split; [lia|]. split; [lia|]. split; [exact D2|]. split; [exact D1|]. intros w i H. discriminate H.
Qed.

Lemma entry_regions_ok : regions_ok ρ (entry_mem segs ph).
Proof.
  unfold entry_mem. apply regions_ok_app; [exact (regions_ok_imgs segs pc ρ Himg)| |].
  - cbn [regions_ok]. split; [exact wf_stk|]. split; [|split; [exact wf_eb | split; [constructor | exact I]]].
    constructor; [|constructor]. unfold rdisj. rewrite rbase_stk, n_stk, rbase_eb. left. lia.
  - intros R HR. destruct (in_img_regions segs R HR) as (i & sg & Hn & ->).
    destruct (img_region_facts segs pc ρ Himg i sg (nth_error_In _ _ Hn)) as (Eb & En & _ & _ & Hl).
    pose proof sp_rng as [[S1 S2] _]. unfold sp_window_lo, ls_beg, stk_max in *.
    constructor; [|constructor; [|constructor]]; unfold rdisj; rewrite Eb, En, ?rbase_stk, ?rbase_eb; left; unfold stk_max; lia.
Qed.

Lemma entry_RMem : RMem segs ρ (entry_mem segs ph) M0.
Proof.
  split; [exact entry_regions_ok|]. unfold entry_mem. apply Forall_app. split.
  - apply Forall_forall. intros R HR. destruct (in_img_regions segs R HR) as (i & sg & Hn & ->).
    destruct (img_region_facts segs pc ρ Himg i sg (nth_error_In _ _ Hn)) as (Eb & En & _ & Hpos & Hl).
    unfold RRegion. cbn [img_region rg_kind]. fold (img_region i sg). intros y Hy. rewrite Eb. rewrite En in Hy.
    pose proof (to_Z_bounded y) as By. pose proof sp_rng as [[S1 S2] _]. unfold sp_window_lo, ls_beg, stk_max in *.
    destruct (img_byte segs pc M0 i sg y Himg Hn Hy ltac:(apply M0_below; unfold stk_max; lia)) as (b & Ei & Hrv & Hb & Hw).
    split.
    + exists (Z_to_bv 8 (to_Z b)). split; [exact Hrv|].
      unfold xb_bv, rbyte, get_cell_opt. cbn [img_region rg_d rg_cells rg_kind]. rewrite iget_empty. cbn [default_byte]. rewrite Ei.
      cbn [xb_z]. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. pose proof (to_Z_bounded b). lia.
    + cbn [img_region rg_kind rk_writable]. exact Hw.
  - constructor; [|constructor; [|constructor]].
    + (* [comment removed for export] *)
      unfold RRegion. cbn [stk_region zero_rg rg_kind]. fold stk_region. intros y Hy. rewrite rbase_stk. rewrite n_stk in Hy.
      pose proof (to_Z_bounded y) as By. pose proof sp_rng as [[S1 S2] _]. unfold sp_window_lo, stk_max in *.
      pose proof (E7_window segs pc ph sp draw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) span_fits
                    ltac:(unfold stack_max_size; lia) (SP - 8388608 + to_Z y) ltac:(unfold stack_max_size; lia)) as Hz.
      split.
      * exists (Z_to_bv 8 0). split; [unfold rv, wz; rewrite Hz; reflexivity|].
        unfold xb_bv, rbyte, get_cell_opt. cbn [stk_region zero_rg rg_d rg_cells rg_kind]. rewrite iget_empty. reflexivity.
      * intros _. unfold wview, wz. rewrite Hz. discriminate.
    + (* [comment removed for export] *)
      unfold RRegion. cbn [eb_region rg_kind]. fold (eb_region ph). rewrite rbase_eb, n_eb.
      exact (eb_rel_init segs pc ph sp draw inp _ Hinp Hsp Hfit).
Qed.

Lemma entry_hs : hs_ok ρ (entry_mem segs ph) M0.
Proof.
  pose proof sp_rng as [[S1 S2] _]. unfold sp_window_lo, sp_window_hi in *.
  assert (Hnone : forall z, in_ss z -> M0 (wz z) = None).
  { intros z Hz. apply M0_below. unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi, stk_max in *. lia. }
  right. split; [|split; [intros z Hz _; left; exact (Hnone z Hz) | split; right; intros z Hz; apply Hnone; [left | right]; exact Hz]].
  intros R HR _ z Hz Hss. unfold entry_mem in HR. apply in_app_or in HR as [HR|[<-|[<-|[]]]].
  - destruct (in_img_regions segs R HR) as (i & sg & Hn & ->).
    destruct (img_region_facts segs pc ρ Himg i sg (nth_error_In _ _ Hn)) as (Eb & En & _ & _ & Hl).
    unfold in_rg in Hz. rewrite Eb, En in Hz. unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi in *. lia.
  - unfold in_rg in Hz. rewrite rbase_stk, n_stk in Hz. unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi, stk_max in *. lia.
  - unfold in_rg in Hz. rewrite rbase_eb, n_eb in Hz. unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi, eb_size in *. lia.
Qed.

Lemma entry_no_shadow (R : region) : In R (entry_mem segs ph) -> is_shadow R = false.
Proof.
  unfold entry_mem. intros HR. apply in_app_or in HR as [HR|[<-|[<-|[]]]]; [|reflexivity|reflexivity].
  destruct (in_img_regions segs R HR) as (i & sg & _ & ->). reflexivity.
Qed.

Lemma entry_regs_ok : RRegs ρ entry_regs ms0.
Proof.
  intros r. unfold entry_regs. change 2%uint63 with (ri 2%bv). rewrite aget_aset.
  assert (Hz : r <> 2%bv -> rg ms0 r = Z_to_bv 64 0).
  { intros N2. unfold rg. destruct (is_x0 r) eqn:E0; [reflexivity|]. unfold init_machine_state. cbn [ms_regs].
    unfold reg_get. rewrite bvmap_get_set_other by congruence.
    destruct (decide (r = 10%bv)) as [->|N10]; [rewrite bvmap_get_set_same; reflexivity|].
    rewrite bvmap_get_set_other by congruence. unfold bvmap_get, bvmap_empty. destruct (bv_key r); reflexivity. }
  destruct (bv_unsigned r =? 0) eqn:E0.
  - apply Z.eqb_eq in E0. rewrite Hz by (intros ->; discriminate E0). reflexivity.
  - destruct (bv_unsigned 2%bv =? bv_unsigned r) eqn:E2.
    + apply Z.eqb_eq in E2. apply bv_eq in E2. subst r. cbn [xv_val]. unfold smod. fold (sp_val ρ). rewrite spv. change (wZ w_zero) with 0.
      rewrite Z.add_0_r. pose proof sp_rng as [[S1 S2] _]. unfold sp_window_lo, sp_window_hi, two64 in *.
      rewrite Z.mod_small by lia.
      unfold rg. change (is_x0 2%bv) with false. cbv iota. unfold init_machine_state. cbn [ms_regs]. unfold reg_get.
      rewrite bvmap_get_set_same. reflexivity.
    + apply Z.eqb_neq in E2. rewrite Hz by (intros ->; apply E2; reflexivity).
      unfold aget. rewrite iget_empty. destruct (ri r =? 0)%uint63; reflexivity.
Qed.

End Mem.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Main.
Variables (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp brk0 mbase : word) (draw : EntryDraw) (LIM : Z) (inp : ProcInput) (s : store).
Hypothesis Hinp : valid_input inp.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk segs brk0.
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Hypothesis Himg : img_ok segs pc = true.
Hypothesis Hsat : sat (enc_b inp sp draw brk0) s.
Hypothesis Hgood : good_inp (in_fs inp) (enc_b inp sp draw brk0).

Notation ρ := (enc_b inp sp draw brk0).
Notation c0 := (init_config segs pc ph sp brk0 mbase draw LIM inp).
Notation model0 := (cfg_model c0).

Lemma init_vmmaps : m_vmmaps model0 = mkVmMapsFull (segments_reserved segs) [] [] brk0 brk0 LIM mbase sp.
Proof. reflexivity. Qed.

Lemma entry_MR : MR segs (in_fs inp) ρ entry_model model0.
Proof.
  pose proof (sp_rng sp Hsp) as [[S1 S2] S3]. unfold sp_window_lo, sp_window_hi in *.
  constructor; rewrite ?init_vmmaps; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk entry_model am_maps am_brk0 am_brk am_tid am_shadow
                                           am_atop am_exp am_fd map].
  - reflexivity.
  - reflexivity.
  - constructor.
  - unfold brk_form, leval. cbn [fst snd teval]. rewrite enc_b_vb. destruct Hbrk as (_ & _ & B3). unfold page_size in B3.
    pose proof (Z.div_mod (bv_unsigned brk0) 4096 ltac:(lia)). lia.
  - unfold brk_form, leval. cbn [fst snd teval]. rewrite enc_b_vb. destruct Hbrk as (_ & _ & B3). unfold page_size in B3.
    pose proof (Z.div_mod (bv_unsigned brk0) 4096 ltac:(lia)). lia.
  - unfold alloc_top. cbn [vm_init_sp]. unfold leval. cbn [fst snd]. fold (sp_val ρ). rewrite (spv sp brk0 draw inp Hsp).
    unfold stack_max_size, stk_max. lia.
  - reflexivity.
  - apply fd_rel_std; [exact Hgood | reflexivity].
  - reflexivity.
  - intros p Hp. destruct Hp.
  - intros H. discriminate H.
  - intros p q Hp. destruct Hp.
  - apply nowrap_nil.
  - intros l1 p l2 E. destruct l1; discriminate E.
  - intros e z He. destruct He.
  - intros z [p [Hp _]]. destruct Hp.
  - intros p Hp. destruct Hp.
  - intros H. discriminate H.
  - intros e He. destruct He.
  - intros p q Hp. destruct Hp.
  - exact (AxLz.LZr_nil ρ).
Qed.

Theorem entry_R : R segs amodel (MR segs (in_fs inp) ρ) LIM ρ (entry_state segs (Z.of_N pc) ph s) c0.
Proof.
  destruct (img_ok_parts segs pc Himg) as (_ & _ & Hpc4 & Hpc26).
  assert (Epc : wZ (wofZ (Z.of_N pc)) = Z.of_N pc) by (rewrite wZ_wofZ; apply Z.mod_small; unfold two64; lia).
  constructor; cbn [cfg_ms cfg_model entry_state a_pc a_regs a_resv a_mem a_facts a_model a_budget].
  - unfold wbv. rewrite Epc. reflexivity.
  - rewrite Epc. split; [exact Hpc4 | exact Hpc26].
  - reflexivity.
  - apply entry_regs_ok; assumption.
  - reflexivity.
  - reflexivity.
  - apply entry_RMem; assumption.
  - exact entry_MR.
  - reflexivity.
  - split; [|reflexivity]. apply Z.eq_le_incl. reflexivity.
  - exact Hsat.
  - apply entry_hs; assumption.
  - intros x Hx. right. left. unfold alloc_top. rewrite init_vmmaps. cbn [vm_init_sp].
    apply M0_dom in Hx; [|exact Hfit]. destruct Hx as [D1 _]. unfold stk_max in D1. unfold stack_max_size. lia.
  - intros R0 HR0 Hsh. rewrite (entry_no_shadow segs ph R0 HR0) in Hsh. discriminate Hsh.
  - unfold na_ok. rewrite init_vmmaps. cbn [vm_noaccess]. split; [|split].
    + intros x _ [p [Hp _]]. destruct Hp.
    + intros z _ [p [Hp _]]. destruct Hp.
    + intros R0 HR0 Hsh. rewrite (entry_no_shadow segs ph R0 HR0) in Hsh. discriminate Hsh.
Qed.

End Main.
