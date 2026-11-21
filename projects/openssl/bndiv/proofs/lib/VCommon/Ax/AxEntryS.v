(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the initial state is restated over valid_sp_va, entry_launch_ok_va, the cache words and min_sigframe_size; zero_window bounds stack_window_lo by a vendored mmap-base floor; the launch ledger holds the vDSO pair and the channel reader); internal commit ids in comments replaced by public commits or removed. *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import PrimString.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec FastWord.
(* BootLayout supplies length_bsb, which len_B rewrites with.  AsanWEb below REQUIRES
   BootLayout, so the module was always loaded; what was missing is the IMPORT that puts
   the name in scope here, and Require is transitive for loading while Import is not.
   length_bsb is the only one of BootLayout's 51 top-level names this file uses.  Placed
   inside the Require block at :5-17, above `Local Open Scope Z_scope` at :21 (shape 6). *)
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep BootLayout.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AsanWEntry AsanWEb.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Cli Require Import CliVerdict.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxAcct AxMeasure.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxBytes AxImg AxMem AxZZ AxState AxSys AxEntryRel AxEntry.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxFd AxModelRel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition chk (c : PrimString.string) (x : int) : bool := match fimg_c c x with Some _ => true | None => false end.

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

Definition enc_b (inp : ProcInput) (sp mbase pcw : word) (draw : EntryDraw) (brk0 : word) : valuation :=
  enc inp sp mbase pcw draw (fun v => if (v =? 4)%uint63 then bv_unsigned brk0 / 4096 else 0).

Lemma enc_b_vb (inp : ProcInput) (sp mbase pcw : word) (draw : EntryDraw) (brk0 : word) :
  enc_b inp sp mbase pcw draw brk0 v_b = bv_unsigned brk0 / 4096.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------
   The mmap-base floor, vendored.  Carried per hunk from openssl/bignum's copy of
   this file, which carries it per hunk from the in-corpus donor
   in an earlier repair's tree, projects/cgif/cgif_file_fuzzer/proofs/
   lib/YK1b.v:120-128, :129-160, :161-180, :192-219 (statement AND proof), itself the
   vendoring of LPS@75d69e00 theories/Common/StoreOk.v.

   Why vendored rather than required: zero_window below needs an upper bound on the
   SECOND arm of Run.stack_window_lo (Run.v:1379), the mmap base plus its guard gap.
   The model proves it in Common/StoreOk.v, and that theory is NOT requirable from
   here -- proofs/lib/dune lists `(theories ... LinuxProcessSemantics OSSVerify.Core
   ...)` and LinuxProcessSemantics.Common is a SEPARATE rocq.theory (lps
   theories/Common/dune:16) the generated dune file does not name.  No file in
   openssl, cgif or libpcap requires it (0 hits; control `From
   LinuxProcessSemantics.Riscv Require` fires in the same search), so every tree that
   needs these vendors them.  Every name used below is in LinuxProcessSem/{State,Run}.v,
   which this file already requires.

   stack_window_lo_valid itself is NOT carried: it needs launch_top_minus_sp from
   Common/StepTac.v, equally unrequirable, and inside Section Mem below len_B already
   bounds ed_top - sp, which is the only thing that lemma would supply.
   --------------------------------------------------------------------------- *)
Lemma page_round_up_Z_fixed : forall n,
  (n mod page_size = 0)%Z -> page_round_up_Z n = n.
Proof.
  intros n Hn. unfold page_round_up_Z, page_size in *.
  apply Z.mod_divide in Hn; [|lia]. destruct Hn as [k Hk]. subst n.
  replace (k * 4096 + 4096 - 1)%Z with (k * 4096 + 4095)%Z by lia.
  rewrite Z.div_add_l by lia.
  replace (4095 / 4096)%Z with 0%Z by reflexivity. lia.
Qed.

Lemma mmap_gap_sv48 : forall kb,
  mmap_gap Sv48 kb
  = (let g := (stack_max_size + (stack_guard_gap_bytes kb
                 + if kb_aslr kb then stack_rnd_max else 0))%Z in
     if (g <? mmap_min_gap)%Z then mmap_min_gap else g).
Proof.
  intros kb. pose proof (stack_guard_gap_bytes_bounds kb) as Hgg.
  unfold mmap_gap. cbv zeta.
  rewrite Z.mod_small
    by (unfold two_pow_64, stack_max_size, stack_rnd_max;
        destruct (kb_aslr kb); lia).
  assert (Hmax : mmap_max_gap Sv48 = 117281240296105%Z)
    by (vm_compute; reflexivity).
  rewrite !Hmax.
  unfold mmap_min_gap in *. rewrite !Z.gtb_ltb.
  destruct (kb_aslr kb); cbv beta iota delta [andb];
  [ destruct (stack_max_size
              <? stack_max_size + (stack_guard_gap_bytes kb + stack_rnd_max))%Z
      eqn:Ein
  | destruct (stack_max_size
              <? stack_max_size + (stack_guard_gap_bytes kb + 0))%Z
      eqn:Ein ];
  try apply Z.ltb_lt in Ein; try apply Z.ltb_ge in Ein;
  cbv beta iota delta [andb];
  repeat (match goal with
          | |- context [(?x <? ?y)%Z] =>
              let E := fresh "E" in destruct (x <? y)%Z eqn:E;
              [ apply Z.ltb_lt in E | apply Z.ltb_ge in E ]
          end;
          cbv beta iota delta [andb]);
  unfold stack_max_size, stack_rnd_max in *; lia.
Qed.

Lemma mmap_gap_sv48_mod : forall kb,
  (mmap_gap Sv48 kb mod page_size = 0)%Z.
Proof.
  intros kb.
  assert (H4096 : forall x : Z, ((4096 * x) mod 4096 = 0)%Z)
    by (intro x; rewrite Z.mul_comm; apply Z_mod_mult).
  rewrite mmap_gap_sv48. cbv zeta.
  unfold stack_guard_gap_bytes, mmap_min_gap, stack_max_size,
    stack_rnd_max, page_size.
  destruct (_ <? _)%Z;
    [ replace (128 * 1024 * 1024)%Z with (4096 * 32768)%Z by reflexivity;
      apply H4096 |].
  destruct (kb_aslr kb);
    [ replace (8 * 1024 * 1024
               + (4096 * stack_guard_gap_pages kb + 1073737728))%Z
        with (4096 * (264191 + stack_guard_gap_pages kb))%Z by lia
    | replace (8 * 1024 * 1024 + (4096 * stack_guard_gap_pages kb + 0))%Z
        with (4096 * (2048 + stack_guard_gap_pages kb))%Z by lia ];
    apply H4096.
Qed.

Lemma launch_base_gap_le : forall kb mbase,
  valid_launch_base Sv48 kb mbase ->
  (bv_unsigned mbase + stack_guard_gap_bytes kb
   <= va_stack_top Sv48
      - (if kb_aslr kb then 0x407ff000 else 8 * 1024 * 1024))%Z.
Proof.
  intros kb mbase (r & Hr & _ & _ & Heq).
  pose proof (stack_guard_gap_bytes_bounds kb) as Hgg.
  rewrite Heq. unfold mmap_base_of.
  assert (Hdiv : (page_size
                  | va_stack_top Sv48 - mmap_gap Sv48 kb - page_size * r)%Z).
  { apply Z.divide_sub_r; [apply Z.divide_sub_r|].
    - exists 34359738368%Z. vm_compute. reflexivity.
    - apply Z.mod_divide; [unfold page_size; lia|]. apply mmap_gap_sv48_mod.
    - exists r. unfold page_size. lia. }
  rewrite page_round_up_Z_fixed
    by (apply Z.mod_divide; [unfold page_size; lia | exact Hdiv]).
  rewrite mmap_gap_sv48. cbv zeta.
  unfold mmap_min_gap, va_stack_top, sp_window_hi, stack_max_size,
    stack_rnd_max, page_size in *.
  destruct (kb_aslr kb); cbv beta iota;
  repeat (match goal with
          | |- context [(?x <? ?y)%Z] =>
              let E := fresh "E" in destruct (x <? y)%Z eqn:E;
              [ apply Z.ltb_lt in E | apply Z.ltb_ge in E ]
          end;
          cbv beta iota);
  lia.
Qed.

Section Mem.
Variables (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp brk0 mbase : word) (draw : EntryDraw) (inp : ProcInput).
Hypothesis Hinp : valid_input inp.
Hypothesis Hcw : launch_cache_words (in_kernel inp) = launch_cache_words default_kernel.
Hypothesis Hmss : min_sigframe_size (in_kernel inp) (in_hwcap inp) = min_sigframe_size default_kernel (in_hwcap inp).
Hypothesis Hsp : valid_sp_va Sv48 sp.
Hypothesis Hmb : valid_mmap_base_va Sv48 mbase.
Hypothesis Hl : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase draw) inp.
Hypothesis Himg : img_ok segs pc = true.
Local Set Default Proof Using "All".

Notation pcw := (Z_to_bv 64 (Z.of_N pc)).
Notation ρ := (enc_b inp sp mbase pcw draw brk0).
Notation ms0 := (init_machine_state segs pc ph sp mbase draw inp).
Notation M0 := (ms_mem ms0).
Notation SP := (bv_unsigned sp).
Notation B := (entry_stack_image inp mbase ph pcw sp draw).
Let r := kb_rseq (in_kernel inp).
Notation TOP := (bv_unsigned (ed_top draw)).

Lemma sp_rng : sp_window_lo <= SP <= sp_window_hi /\ SP mod 16 = 0.
Proof.
  destruct Hsp as (H1 & H2 & H3).
  (* MEASURED, not inferred: with the original `cbn [va_sp_window_lo va_sp_window_hi
     va_stack_top] in *` an UNCLOSED-GOAL probe before `lia` printed
       PROBE-H1: (va_sp_window_lo Sv48 <= SP)      <- NOT reduced
       PROBE-H2: (SP <= 140737488355328)           <- reduced
     so cbn reduced the hi side and left the lo side folded, and `lia` had the goal's
     literal lower bound against an opaque atom: `Cannot find witness`.  The asymmetry is
     cbn's progress heuristic.  va_sp_window_hi v := va_stack_top v unfolds to a match
     that iota-reduces to sp_window_hi, which cbn counts as progress; va_sp_window_lo v
     := (va_stack_top v - 2*1024*1024*1024)%Z unfolds to a Z.sub application whose head
     cbn cannot reduce further with delta restricted to those three names, so cbn backs
     the unfolding out and restores the folded form.  `cbv` with the same delta list has
     no such heuristic and reduces both.  Widening the later `unfold ... in *` is NOT
     sufficient on its own and was tried first: it leaves va_sp_window_lo Sv48 standing.
     After cbv, H1 is sp_window_hi - 2*1024*1024*1024 <= SP, and the remaining step is
     arithmetic lia does itself: 0x800000000000 - 2*1024*1024*1024 = 0x7fff80000000.
     LPS@75d69e00 theories/LinuxProcessSem/State.v:160-161 (the two literals) and
     :494-503 (va_stack_top, va_sp_window_hi, va_sp_window_lo), Run.v:3169-3172
     (valid_sp_va) -- statements only, no proof taken.  All four are byte-identical at
     f1006fe8, 08b1429 and 75d69e00, so this is a defect entry-stack
     port, not a revision-#38 breakage.  Probe run in bignum; this tree's AxEntryS.v is
     byte-identical to bignum's outside the Require namespace. *)
  cbv [va_sp_window_lo va_sp_window_hi va_stack_top] in H1, H2.
  unfold sp_window_lo, sp_window_hi in *.
  lia.
Qed.

Lemma spv : sp_val ρ = SP.
Proof. unfold enc_b. exact (ei_spval inp sp mbase pcw brk0 draw _ Hinp Hcw Hl). Qed.

(** the block is exactly [top - sp] bytes, at most 2101782 *)
Lemma len_B : Z.of_nat (length B) = TOP - SP /\ TOP - SP <= 2101782 /\ TOP <= sp_window_hi.
Proof.
  pose proof (ei_pad inp sp mbase pcw brk0 draw (fun _ => 0) Hinp Hcw Hl) as EP.
  pose proof (ei_pad_lt inp sp mbase pcw brk0 draw (fun _ => 0) Hinp Hcw Hl) as EPl.
  pose proof Hinp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hlb) & _).
  pose proof Hl as Hl'. cbn [entry_launch_ok_va] in Hl'. destruct Hl' as ((_ & Htop & _) & _ & _). cbn [va_stack_top] in Htop.
  assert (Hhs : Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
                <= 512 + 8 * Z.of_nat (length (in_argv inp)) + 8 * Z.of_nat (length (in_envp inp))).
  { unfold block_head_size, block_items. cbv zeta.
    assert (Haux : (auxv_size (kb_rseq (in_kernel inp)) <= 464)%nat)
      by (destruct (kb_rseq (in_kernel inp)); [change (auxv_size true) with 464%nat | change (auxv_size false) with 432%nat]; lia).
    pose proof (Nat.mod_upper_bound (length (in_argv inp) + length (in_envp inp) + 3) 2 ltac:(lia)). lia. }
  unfold launch_bytes, e2big_limit in Hlb.
  rewrite entry_stack_image_block, length_bsb. cbn [la_rseq launch_auxv]. rewrite !Nat2Z.inj_add. rewrite EP.
  unfold sp_window_hi. split; [lia|]. split; [lia | exact Htop].
Qed.

Lemma spB : SP + Z.of_nat (length B) < 2 ^ 64.
Proof. pose proof len_B as (L & _ & T). unfold sp_window_hi in T. lia. Qed.

(** The zero window below sp, for EVERY kernel build.  [Run.stack_window_lo]
    (Run.v:1379-1382) is the max of two floors: [ed_top - stack_max_size], and the
    mmap base plus its guard gap.
    - First floor: [len_B] above bounds [ed_top - sp] by 2101782, and
      stack_max_size - stk_zero = 8388608 - 6144000 = 2244608, so it clears by 142826.
    - Second floor: [launch_base_gap_le] above, against the THIRD conjunct of
      [Run.entry_page_top_ok] (Run.v:3611-3615), which holds ed_top within
      stack_rnd_max + page_size of [va_stack_top Sv48] when the build randomises the
      stack and within page_size when it does not.  Slack 130538 bytes with ASLR
      (1082118144 against 1075843606 + 6144000) and 138730 without.
    No field of the kernel is fixed: both branches are discharged under
    [destruct (kb_aslr (in_kernel inp))], and the guard gap stays symbolic throughout
    -- [stack_guard_gap_bytes_bounds] inside launch_base_gap_le is the only thing said
    about it.  The old proof called Common/StoreOk's [stack_window_lo_valid], which
    this tree's dune cannot reach; see the vendoring note above Section Mem. *)
Lemma zero_window : stack_window_lo (in_kernel inp) mbase draw <= SP - stk_zero.
Proof.
  pose proof len_B as (_ & Hts & _).
  pose proof Hl as Hl'. cbn [entry_launch_ok_va] in Hl'.
  destruct Hl' as ((_ & _ & Hlo) & _ & Hbase).
  pose proof (launch_base_gap_le (in_kernel inp) mbase Hbase) as Hg.
  unfold stack_window_lo, stack_max_size, stk_zero in *.
  cbv [va_stack_top] in Hg, Hlo.
  unfold sp_window_hi, stack_rnd_max, page_size in *.
  destruct (kb_aslr (in_kernel inp)); cbv beta iota in Hg, Hlo;
    apply Z.max_lub; lia.
Qed.

(** the launch's mmap base, from below: [Run.valid_entry_va]'s own conjunct, for every kernel *)
Lemma launch_lo : mmap_base_min <= bv_unsigned mbase.
Proof. destruct Hmb as (H & _ & _). cbn [va_mmap_base_min] in H. exact H. Qed.

Lemma M0_dom (a : word) : M0 a <> None -> SP - stk_max <= bv_unsigned a < sp_window_hi.
Proof.
  intros H. pose proof (E7_domain segs pc ph sp mbase draw inp spB a H) as D. unfold stack_window_lo in D.
  pose proof len_B as (Hl1 & _ & Htop).
  pose proof (Z.le_max_l (TOP - stack_max_size) (bv_unsigned mbase + stack_guard_gap_bytes (in_kernel inp))) as Hmx.
  unfold stk_max, stack_max_size in *. lia.
Qed.

Lemma M0_below (z : Z) : 0 <= z < SP - stk_max -> M0 (wz z) = None.
Proof.
  intros Hz. destruct (M0 (wz z)) as [b|] eqn:E; [|reflexivity]. exfalso.
  assert (H : M0 (wz z) <> None) by (rewrite E; discriminate). apply M0_dom in H.
  pose proof sp_rng as [[S1 S2] _]. unfold sp_window_lo, sp_window_hi, stk_max in *.
  unfold wz in H. rewrite Z_to_bv_unsigned, bv_wrap_small in H by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.

Lemma rbase_stk : rbase ρ stk_region = SP - stk_zero.
Proof.
  unfold rbase, stk_region, zero_rg, smod. cbn [rg_ts rg_bo]. fold (sp_val ρ). rewrite spv, wZ_wofZ.
  pose proof sp_rng as [[S1 S2] _]. unfold sp_window_lo, sp_window_hi, stk_zero, two64 in *.
  rewrite Zplus_mod_idemp_r. replace (SP + -6270976) with (SP - 6270976) by lia. apply Z.mod_small. lia.
Qed.

Lemma rbase_eb : rbase ρ (eb_region r ph) = SP.
Proof.
  unfold rbase, eb_region, smod. cbn [rg_ts rg_bo]. fold (sp_val ρ). rewrite spv. change (wZ w_zero) with 0. rewrite Z.add_0_r.
  pose proof sp_rng as [[S1 S2] _]. unfold sp_window_lo, sp_window_hi, two64 in *. apply Z.mod_small. lia.
Qed.

Lemma n_stk : to_Z (rg_n stk_region) = stk_zero. Proof. reflexivity. Qed.
Lemma n_eb : to_Z (rg_n (eb_region r ph)) = eb_size. Proof. reflexivity. Qed.

Lemma wf_stk : region_wf ρ stk_region.
Proof.
  unfold region_wf. rewrite rbase_stk, n_stk. pose proof sp_rng as [[S1 S2] _]. unfold sp_window_lo, sp_window_hi, stk_zero, two64 in *.
  destruct (depth_for_spec 6270976 ltac:(lia)) as [D1 D2].
  split; [lia|]. split; [lia|]. split; [exact D2|]. split; [exact D1|]. intros w i H. discriminate H.
Qed.

Lemma wf_eb : region_wf ρ (eb_region r ph).
Proof.
  unfold region_wf. rewrite rbase_eb, n_eb. pose proof sp_rng as [[S1 S2] _]. unfold sp_window_lo, sp_window_hi, eb_size, two64 in *.
  destruct (depth_for_spec 2238672 ltac:(lia)) as [D1 D2].
  split; [lia|]. split; [lia|]. split; [exact D2|]. split; [exact D1|]. intros w i H. discriminate H.
Qed.

Lemma entry_regions_ok : regions_ok ρ (entry_mem r segs ph).
Proof.
  unfold entry_mem. apply regions_ok_app; [exact (regions_ok_imgs segs pc ρ Himg)| |].
  - cbn [regions_ok]. split; [exact wf_stk|]. split; [|split; [exact wf_eb | split; [constructor | exact I]]].
    constructor; [|constructor]. unfold rdisj. rewrite rbase_stk, n_stk, rbase_eb. left. lia.
  - intros R HR. destruct (in_img_regions segs R HR) as (i & sg & Hn & ->).
    destruct (img_region_facts segs pc ρ Himg i sg (nth_error_In _ _ Hn)) as (Eb & En & _ & _ & Hl0).
    pose proof sp_rng as [[S1 S2] _]. unfold sp_window_lo, ls_beg, stk_zero in *.
    constructor; [|constructor; [|constructor]]; unfold rdisj; rewrite Eb, En, ?rbase_stk, ?rbase_eb; left; unfold stk_zero; lia.
Qed.

Lemma entry_RMem : RMem segs ρ (entry_mem r segs ph) M0.
Proof.
  split; [exact entry_regions_ok|]. unfold entry_mem. apply Forall_app. split.
  - apply Forall_forall. intros R HR. destruct (in_img_regions segs R HR) as (i & sg & Hn & ->).
    destruct (img_region_facts segs pc ρ Himg i sg (nth_error_In _ _ Hn)) as (Eb & En & _ & Hpos & Hl0).
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
      pose proof (to_Z_bounded y) as By. pose proof sp_rng as [[S1 S2] _]. pose proof zero_window as ZW.
      unfold sp_window_lo, stk_zero in *.
      (* 6144000 is stk_zero (AxEntry.v:22), which the unfold above has just applied to
         the goal; the address is stk_region's base plus y, and rbase_stk gives that
         base as SP - stk_zero.  The literal here read 6270976, 31 pages LOWER than the
         region the two rewrites above put in the goal, so E7_window's window premise
         WLO <= addr was asked of an address below the window: zero_window gives
         WLO <= SP - 6144000 and nothing places SP - 6270976 above it. *)
      pose proof (E7_window segs pc ph sp mbase draw inp spB (SP - 6144000 + to_Z y) ltac:(lia) ltac:(lia)) as Hz.
      split.
      * exists (Z_to_bv 8 0). split; [unfold rv, wz; rewrite Hz; reflexivity|].
        unfold xb_bv, rbyte, get_cell_opt. cbn [stk_region zero_rg rg_d rg_cells rg_kind]. rewrite iget_empty. reflexivity.
      * intros _. unfold wview, wz. rewrite Hz. discriminate.
    +
      unfold RRegion. cbn [eb_region rg_kind]. fold (eb_region r ph). rewrite rbase_eb, n_eb.
      exact (eb_rel_init segs pc ph sp brk0 mbase draw inp _ Hinp Hcw Hmss Hsp Hl).
Qed.

Lemma entry_hs : hs_ok ρ (entry_mem r segs ph) M0.
Proof.
  pose proof sp_rng as [[S1 S2] _]. unfold sp_window_lo, sp_window_hi in *.
  assert (Hnone : forall z, in_ss z -> M0 (wz z) = None).
  { intros z Hz. apply M0_below. unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi, stk_max in *. lia. }
  right. split; [|split; [intros z Hz _; left; exact (Hnone z Hz) | split; right; intros z Hz; apply Hnone; [left | right]; exact Hz]].
  intros R HR _ z Hz Hss. unfold entry_mem in HR. apply in_app_or in HR as [HR|[<-|[<-|[]]]].
  - destruct (in_img_regions segs R HR) as (i & sg & Hn & ->).
    destruct (img_region_facts segs pc ρ Himg i sg (nth_error_In _ _ Hn)) as (Eb & En & _ & _ & Hl0).
    unfold in_rg in Hz. rewrite Eb, En in Hz. unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi in *. lia.
  - unfold in_rg in Hz. rewrite rbase_stk, n_stk in Hz. unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi, stk_zero in *. lia.
  - unfold in_rg in Hz. rewrite rbase_eb, n_eb in Hz. unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi, eb_size in *. lia.
Qed.

Lemma entry_no_shadow (R : region) : In R (entry_mem r segs ph) -> is_shadow R = false.
Proof.
  unfold entry_mem. intros HR. apply in_app_or in HR as [HR|[<-|[<-|[]]]]; [|reflexivity|reflexivity].
  destruct (in_img_regions segs R HR) as (i & sg & _ & ->). reflexivity.
Qed.

Lemma entry_regs_ok : RRegs ρ entry_regs ms0.
Proof.
  (* The register index was introduced as `r`, which Section Mem already binds as
     `Let r := kb_rseq (in_kernel inp)` -- "r is already used".  Renamed to `rr`
     throughout this proof and nowhere else; the statement is untouched. *)
  intros rr. unfold entry_regs. change 2%uint63 with (ri 2%bv). rewrite aget_aset.
  assert (Hz : rr <> 2%bv -> rg ms0 rr = Z_to_bv 64 0).
  { intros N2. unfold rg. destruct (is_x0 rr) eqn:E0; [reflexivity|]. unfold init_machine_state. cbn [ms_regs].
    unfold reg_get. rewrite bvmap_get_set_other by congruence.
    destruct (decide (rr = 10%bv)) as [->|N10]; [rewrite bvmap_get_set_same; reflexivity|].
    rewrite bvmap_get_set_other by congruence. unfold bvmap_get, bvmap_empty. destruct (bv_key rr); reflexivity. }
  destruct (bv_unsigned rr =? 0) eqn:E0.
  - apply Z.eqb_eq in E0. rewrite Hz by (intros ->; discriminate E0). reflexivity.
  - destruct (bv_unsigned 2%bv =? bv_unsigned rr) eqn:E2.
    + apply Z.eqb_eq in E2. apply bv_eq in E2. subst rr. cbn [xv_val]. unfold smod. fold (sp_val ρ). rewrite spv. change (wZ w_zero) with 0.
      rewrite Z.add_0_r. pose proof sp_rng as [[S1 S2] _]. unfold sp_window_lo, sp_window_hi, two64 in *.
      rewrite Z.mod_small by lia.
      unfold rg. change (is_x0 2%bv) with false. cbv iota. unfold init_machine_state. cbn [ms_regs]. unfold reg_get.
      rewrite bvmap_get_set_same. reflexivity.
    + apply Z.eqb_neq in E2. rewrite Hz by (intros ->; apply E2; reflexivity).
      unfold aget. rewrite iget_empty. destruct (ri rr =? 0)%uint63; reflexivity.
Qed.

End Mem.

Section Main.
Variables (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp brk0 mbase : word) (draw : EntryDraw) (LIM : Z) (inp : ProcInput) (s : store).
Hypothesis Hinp : valid_input inp.
Hypothesis Hcw : launch_cache_words (in_kernel inp) = launch_cache_words default_kernel.
Hypothesis Hmss : min_sigframe_size (in_kernel inp) (in_hwcap inp) = min_sigframe_size default_kernel (in_hwcap inp).
Hypothesis Hsp : valid_sp_va Sv48 sp.
Hypothesis Hmb : valid_mmap_base_va Sv48 mbase.
Hypothesis Hl : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase draw) inp.
Hypothesis Hbrk : valid_brk segs brk0.
Hypothesis Himg : img_ok segs pc = true.
Hypothesis Hsat : sat (enc_b inp sp mbase (Z_to_bv 64 (Z.of_N pc)) draw brk0) s.
Hypothesis Hgood : good_inp (in_fs inp) (enc_b inp sp mbase (Z_to_bv 64 (Z.of_N pc)) draw brk0).
Local Set Default Proof Using "All".

Notation ρ := (enc_b inp sp mbase (Z_to_bv 64 (Z.of_N pc)) draw brk0).
Notation c0 := (init_config segs pc ph sp brk0 mbase draw LIM inp).
Notation model0 := (cfg_model c0).
Let r := kb_rseq (in_kernel inp).

Lemma init_vmmaps : m_vmmaps model0 = mkVmMapsFull (init_reserved (segments_reserved segs) mbase sp (in_kernel inp)) [] [] brk0 brk0 LIM mbase sp.
Proof. reflexivity. Qed.

(** the launch's reserved ledger: the image's reservations, then the vDSO pair, high and small *)
Lemma init_res_ok : exists rx : list (word * word), vm_reserved (m_vmmaps model0) = segments_reserved segs ++ rx
  /\ (length rx <= 2)%nat /\ live_bytes rx <= 0x14000 /\ Forall (fun q => 0x154500000000 <= bas q) rx.
Proof.
  rewrite init_vmmaps. cbn [vm_reserved]. unfold init_reserved. eexists. split; [reflexivity|].
  pose proof (launch_lo segs pc ph sp brk0 mbase draw inp Hinp Hcw Hmss Hsp Hmb Hl Himg) as Hm.
  (* sp_rng is a Section Mem lemma under `Local Set Default Proof Using "All"`, so it is
     abstracted over all eight section variables and all seven hypotheses; Section Main
     binds different ones, so it cannot be used bare here.  Same argument list as
     launch_lo on the line above, which is the working form in this file. *)
  pose proof (sp_rng segs pc ph sp brk0 mbase draw inp Hinp Hcw Hmss Hsp Hmb Hl Himg) as [[Hs _] _].
  pose proof (vdso_len_bounds (in_kernel inp)) as VL. pose proof (vdso_text_pages_pos (in_kernel inp)) as T1.
  pose proof (vdso_text_pages_le (in_kernel inp)) as T2.
  pose proof (u64_range mbase). pose proof (u64_range sp).
  set (top := page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size))).
  assert (Htop : 0x154500000000 + 20 * 4096 <= top <= bv_unsigned mbase).
  { unfold top, page_round_down_Z, page_size, stack_max_size, mmap_base_min in *.
    unfold sp_window_lo in Hs.
    pose proof (Z.div_mod (Z.min (bv_unsigned mbase) (bv_unsigned sp - 8388608)) 4096 ltac:(lia)).
    pose proof (Z.mod_pos_bound (Z.min (bv_unsigned mbase) (bv_unsigned sp - 8388608)) 4096 ltac:(lia)). lia. }
  unfold vdso_reserved. destruct (top - vdso_len (in_kernel inp) <? page_size) eqn:E.
  - split; [cbn; lia|]. split; [cbn; lia | constructor].
  - apply Z.ltb_ge in E. unfold page_size, vdso_vvar_pages in *.
    cbn [length live_bytes]. unfold bas. cbn [fst snd]. rewrite !Z_to_bv_unsigned.
    rewrite !bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
    split; [lia|]. split; [lia|]. repeat constructor; cbn [fst]; rewrite Z_to_bv_unsigned, bv_wrap_small
      by (change (bv_modulus 64) with (2 ^ 64); lia); lia.
Qed.

Lemma init_rdr : m_channel_reader model0 = true.
Proof. transitivity (in_channel_reader inp); [reflexivity | exact (valid_input_channel_reader inp Hinp)]. Qed.

Lemma entry_MR : MR segs (in_fs inp) ρ entry_model model0.
Proof.
  pose proof (sp_rng segs pc ph sp brk0 mbase draw inp Hinp Hcw Hmss Hsp Hmb Hl Himg) as [[S1 S2] S3]. unfold sp_window_lo, sp_window_hi in *.
  constructor; rewrite ?init_vmmaps; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk entry_model am_maps am_brk0 am_brk am_tid am_shadow
                                           am_atop am_exp am_fd map].
  (* WAS: reflexivity.  The farm measured it at AxEntryS.v:654, "Cannot find a relation
     to rewrite" -- mr_res is an EXISTENTIAL now, so reflexivity has no relation to
     work on.  This is ported from bignum, which I had applied THERE and
     not here: the same first bullet, the same cause, and the port is why bndiv kept
     failing after bignum's entry_MR was closed.  The field is character for character
     init_res_ok's conclusion, proved above at :618 from the tree's own launch facts
     with no kernel field destructed, pinned or vm_computed. *)
  - exact init_res_ok.
  - reflexivity.
  - constructor.
  - unfold brk_form, leval. cbn [fst snd teval]. rewrite enc_b_vb. destruct Hbrk as (_ & _ & B3). unfold page_size in B3.
    pose proof (Z.div_mod (bv_unsigned brk0) 4096 ltac:(lia)). lia.
  - unfold brk_form, leval. cbn [fst snd teval]. rewrite enc_b_vb. destruct Hbrk as (_ & _ & B3). unfold page_size in B3.
    pose proof (Z.div_mod (bv_unsigned brk0) 4096 ltac:(lia)). lia.
  - unfold alloc_top. cbn [vm_init_sp]. unfold leval. cbn [fst snd]. fold (sp_val ρ). rewrite (spv segs pc ph sp brk0 mbase draw inp Hinp Hcw Hmss Hsp Hmb Hl Himg).
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
  (* mr_vdso, the launch case.  init_reserved is literally
     `segments_reserved segs ++ vdso_reserved (in_kernel inp) T` with
     T = page_round_down_Z (Z.min mbase (sp - stack_max_size))
     (LPS@75d69e00 State.v:7716-7722), and T IS vdso_top of the ledger this very
     constructor builds -- the model says so itself at State.v:7835-7843
     (vdso_top_init_model), whose proof is page_round_down_Z_min_r over
     mmap_top = Z.min vm_mmap_base (page_round_down_Z (alloc_top)).  So the pair is
     the tail of the append and incl is in_or_app.  No kernel field is named: the
     build stays `in_kernel inp`. *)
  (* The constructor's own `rewrite ?init_vmmaps` has already replaced
     m_vmmaps model0 by the literal ledger, so this goal is matched rather than
     named: `rewrite Et` on the folded form found no subterm
     (AxEntryS.v:698). *)
  - lazymatch goal with
    | |- incl (vdso_reserved _ ?T) _ =>
        let Et := fresh "Et" in
        assert (Et : T = page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)))
          by (unfold vdso_top, mmap_top, alloc_top; cbn [vm_mmap_base vm_init_sp];
              apply page_round_down_Z_min_r);
        rewrite Et
    end.
    unfold init_reserved. intros q Hq. apply in_or_app. right. exact Hq.
  (* mr_rdr, the launch case.  init_rdr (:646) is exactly this field, proved from
     valid_input_channel_reader against this tree's own input -- the bit is free in the
     Model (LPS@75d69e00 State.v:4921-4923) and enters the proof only here. *)
  - exact init_rdr.
Qed.

Theorem entry_R : R segs amodel (MR segs (in_fs inp) ρ) LIM ρ (entry_state r segs (Z.of_N pc) ph s) c0.
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
    pose proof (M0_dom segs pc ph sp brk0 mbase draw inp Hinp Hcw Hmss Hsp Hmb Hl Himg x Hx) as [D1 _]. unfold stk_max in D1. unfold stack_max_size. lia.
    (* entry_no_shadow is abstracted the same way; `segs ph R0 HR0` passed ph where pc
       belongs and stopped twelve arguments short.  PRE-EMPTIVE: no compile had reached
       this line yet, the fix is read off launch_lo's working call, and I am first
       suspect if anything moves here. *)
  - intros R0 HR0 Hsh. rewrite (entry_no_shadow segs pc ph sp brk0 mbase draw inp Hinp Hcw Hmss Hsp Hmb Hl Himg R0 HR0) in Hsh. discriminate Hsh.
  - unfold na_ok. rewrite init_vmmaps. cbn [vm_noaccess]. split; [|split].
    + intros x _ [p [Hp _]]. destruct Hp.
    + intros z _ [p [Hp _]]. destruct Hp.
    + intros R0 HR0 Hsh. rewrite (entry_no_shadow segs pc ph sp brk0 mbase draw inp Hinp Hcw Hmss Hsp Hmb Hl Himg R0 HR0) in Hsh. discriminate Hsh.
Qed.

End Main.
