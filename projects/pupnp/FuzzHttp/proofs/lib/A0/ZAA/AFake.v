(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts.
Import ListNotations.
Open Scope Z_scope.

Definition fk_N (k : Z) : Z :=
  match k with 0 => 16384 | 1 => 8192 | 2 => 4096 | 3 => 2048 | 4 => 1024 | 5 => 512 | 6 => 256 | 7 => 128 | 8 => 64 | 9 => 32 | _ => 16 end.
Definition fk_flags_off (k : Z) : Z :=
  match k with 0 => 0 | 1 => 16384 | 2 => 24576 | 3 => 28672 | 4 => 30720 | 5 => 31744 | 6 => 32256 | 7 => 32512 | 8 => 32640 | 9 => 32704 | _ => 32736 end.
Definition fk_frame (fsb k pos : Z) : Z := fsb + A0_FS_FRAMES + k * 1048576 + pos * FB_of k.
Definition fk_flag (fsb k pos : Z) : Z := fsb + 4096 + fk_flags_off k + pos.

Lemma fk_class_cases : forall k, 0 <= k <= 10 -> k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10.
Proof. intros k Hk. lia. Qed.

Lemma fk_geom : forall k, 0 <= k <= 10 ->
  fk_N k * FB_of k = 1048576 /\ 16 <= fk_N k /\ 64 <= FB_of k /\ FB_of k mod 64 = 0 /\ SB_of k * 8 = FB_of k
  /\ 0 <= fk_flags_off k /\ fk_flags_off k + fk_N k <= 32768 /\ 18446744073709551616 mod fk_N k = 0.
Proof. intros k Hk. destruct (fk_class_cases k Hk) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; cbn; repeat split; lia. Qed.

Lemma fk_flags_apart : forall k k', 0 <= k <= 10 -> 0 <= k' <= 10 -> k <> k' ->
  fk_flags_off k + fk_N k <= fk_flags_off k' \/ fk_flags_off k' + fk_N k' <= fk_flags_off k.
Proof.
  intros k k' Hk Hk' NE.
  destruct (fk_class_cases k Hk) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]];
  destruct (fk_class_cases k' Hk') as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; cbn; lia.
Qed.

Lemma fk_frame_range : forall fsb k pos, 0 <= k <= 10 -> 0 <= pos < fk_N k ->
  fsb + A0_FS_FRAMES + k * 1048576 <= fk_frame fsb k pos /\ fk_frame fsb k pos + FB_of k <= fsb + A0_FS_FRAMES + (k + 1) * 1048576.
Proof.
  intros fsb k pos Hk Hp. destruct (fk_geom k Hk) as (G1 & _ & G3 & _). unfold fk_frame.
  assert (0 <= pos * FB_of k /\ pos * FB_of k + FB_of k <= fk_N k * FB_of k) by nia. lia.
Qed.

Fixpoint fprobe (lp : list Z) (N h : Z) (fuel : nat) : Z :=
  match fuel with
  | O => h
  | S f => if existsb (Z.eqb (h mod N)) lp then fprobe lp N (h + 1) f else h
  end.

Lemma existsb_eqb_in : forall x l, existsb (Z.eqb x) l = true <-> In x l.
Proof.
  intros x l. rewrite existsb_exists. split; [intros (y & Hy & E); apply Z.eqb_eq in E; subst; exact Hy| intros H; exists x; split; [exact H| apply Z.eqb_refl]].
Qed.

Lemma fprobe_gen : forall fuel lp N h (seen : list Z), 0 < N ->
  List.NoDup seen -> incl seen lp -> (length lp < length seen + fuel)%nat -> (Z.of_nat (length seen + fuel) <= N) ->
  (forall x, In x seen -> exists i, 1 <= i <= Z.of_nat (length seen) /\ x = (h - i) mod N) ->
  let r := fprobe lp N h fuel in ~ In (r mod N) lp /\ h <= r <= h + Z.of_nat fuel.
Proof.
  induction fuel as [|f IH]; intros lp N h seen HN ND INC LEN LN SEEN; cbv zeta.
  - exfalso. pose proof (NoDup_incl_length ND INC). lia.
  - cbn [fprobe]. destruct (existsb (Z.eqb (h mod N)) lp) eqn:EX.
    + apply existsb_eqb_in in EX.
      assert (NI : ~ In (h mod N) seen).
      { intros HI. destruct (SEEN _ HI) as (i & Hi & EQ).
        assert (D : (h - (h - i)) mod N = 0) by (rewrite Zminus_mod, <- EQ, Z.sub_diag; apply Z.mod_0_l; lia).
        replace (h - (h - i)) with i in D by lia. rewrite Z.mod_small in D by lia. lia. }
      destruct (IH lp N (h + 1) ((h mod N) :: seen) HN) as [R1 R2].
      * constructor; assumption.
      * intros x [<-|Hx]; [exact EX| exact (INC x Hx)].
      * cbn [length]. lia.
      * cbn [length]. lia.
      * intros x [<-|Hx]; [exists 1; split; [cbn [length]; lia| f_equal; lia]|].
        destruct (SEEN x Hx) as (i & Hi & EQ). exists (i + 1). split; [cbn [length]; lia| rewrite EQ; f_equal; lia].
      * split; [exact R1| lia].
    + split; [| lia]. intros HI. apply existsb_eqb_in in HI. rewrite HI in EX. discriminate.
Qed.

Lemma fprobe_ok : forall lp N h, 0 < N -> Z.of_nat (length lp) < N ->
  let r := fprobe lp N h (S (length lp)) in ~ In (r mod N) lp /\ h <= r <= h + Z.of_nat (length lp) + 1.
Proof.
  intros lp N h HN LN. cbv zeta.
  destruct (fprobe_gen (S (length lp)) lp N h [] HN ltac:(constructor) ltac:(intros x []) ltac:(cbn [length]; lia) ltac:(cbn [length]; lia) ltac:(intros x [])) as [R1 R2].
  split; [exact R1| lia].
Qed.

Record fstate := mkFST { ft_hint : Z -> Z; ft_live : list (Z * Z) }.
Definition lpos (st : fstate) (k : Z) : list Z := map snd (List.filter (fun kp => fst kp =? k) (ft_live st)).
Definition ff_of (fsb : Z) (kp : Z * Z) : fframe := mkFF (fst kp) (fk_frame fsb (fst kp) (snd kp)) (fk_flag fsb (fst kp) (snd kp)).
Definition fst_live (fsb : Z) (st : fstate) : list fframe := map (ff_of fsb) (ft_live st).

Definition fst_probe (st : fstate) (k : Z) : Z := fprobe (lpos st k) (fk_N k) (ft_hint st k) (S (length (lpos st k))).
Definition fst_malloc (fsb : Z) (st : fstate) (k : Z) : fstate * fframe :=
  let h := fst_probe st k in let pos := h mod fk_N k in
  (mkFST (fun k' => if k' =? k then (h + 1) mod 2^64 else ft_hint st k') ((k, pos) :: ft_live st), ff_of fsb (k, pos)).
Definition fst_release (st : fstate) : fstate := mkFST (ft_hint st) (tl (ft_live st)).

Definition fst_wf (st : fstate) : Prop :=
  Forall (fun kp => 0 <= fst kp <= 10 /\ 0 <= snd kp < fk_N (fst kp)) (ft_live st)
  /\ List.NoDup (ft_live st) /\ (length (ft_live st) < 16)%nat
  /\ (forall k, 0 <= k <= 10 -> 0 <= ft_hint st k < 2^64).

Lemma lpos_len : forall st k, (length (lpos st k) <= length (ft_live st))%nat.
Proof. intros st k. unfold lpos. rewrite length_map. apply List.filter_length_le. Qed.
Lemma lpos_in : forall st k p, In p (lpos st k) <-> In (k, p) (ft_live st).
Proof.
  intros st k p. unfold lpos. rewrite in_map_iff. split.
  - intros ([k' p'] & E & Hin). cbn in E. subst p'. apply filter_In in Hin as [Hin EK]. cbn in EK. apply Z.eqb_eq in EK. subst k'. exact Hin.
  - intros Hin. exists (k, p). split; [reflexivity|]. apply filter_In. split; [exact Hin| cbn; apply Z.eqb_refl].
Qed.

Lemma fst_probe_ok : forall st k, fst_wf st -> 0 <= k <= 10 ->
  let h := fst_probe st k in ~ In (k, h mod fk_N k) (ft_live st) /\ 0 <= h mod fk_N k < fk_N k.
Proof.
  intros st k (FA & ND & LEN & HR) Hk. cbv zeta. destruct (fk_geom k Hk) as (_ & G2 & _).
  pose proof (lpos_len st k) as LL.
  destruct (fprobe_ok (lpos st k) (fk_N k) (ft_hint st k) ltac:(lia) ltac:(lia)) as [R1 _].
  split; [intros HI; apply R1; apply lpos_in; exact HI| apply Z.mod_pos_bound; lia].
Qed.

Section FK.
Variable fsb : Z.
Hypothesis FSB0 : 0 <= fsb.
Hypothesis FSBM : fsb mod 4096 = 0.

#[using="FSB0 FSBM"] Lemma ff_of_wf : forall kp, 0 <= fst kp <= 10 -> 0 <= snd kp < fk_N (fst kp) ->
  let g := ff_of fsb kp in
  0 <= ff_class g <= 10 /\ fsb + A0_FS_FRAMES <= ff_addr g /\ ff_addr g + ff_size g <= fsb + A0_FS_SIZE
  /\ ff_addr g mod 64 = 0 /\ fsb + 4096 <= ff_flag g /\ ff_flag g + 1 <= fsb + A0_FS_FRAMES.
Proof.
  intros [k p] Hk Hp. cbn [fst snd] in *. cbv zeta. unfold ff_of, ff_size. cbn [ff_class ff_addr ff_flag fst snd].
  destruct (fk_geom k Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _). destruct (fk_frame_range fsb k p Hk Hp) as [R1 R2].
  split; [exact Hk|]. split; [lia|]. split; [lia|].
  split. { unfold fk_frame. assert (E : exists j, FB_of k = 64 * j) by (exists (FB_of k / 64); Z.div_mod_to_equations; lia). destruct E as [j Ej]. rewrite Ej.
           replace (fsb + 36864 + k * 1048576 + p * (64 * j)) with (fsb + 64 * (576 + k * 16384 + p * j)) by lia. Z.div_mod_to_equations. lia. }
  unfold fk_flag. split; lia.
Qed.

#[using="FSB0 FSBM"] Lemma ff_of_apart : forall kp kp', 0 <= fst kp <= 10 -> 0 <= snd kp < fk_N (fst kp) -> 0 <= fst kp' <= 10 -> 0 <= snd kp' < fk_N (fst kp') ->
  kp <> kp' -> ff_apart (ff_of fsb kp) (ff_of fsb kp').
Proof.
  intros [k p] [k' p'] Hk Hp Hk' Hp' NE. cbn [fst snd] in *.
  destruct (ff_of_wf (k, p) Hk Hp) as (_ & A1 & A2 & A3 & _). destruct (ff_of_wf (k', p') Hk' Hp') as (_ & B1 & B2 & B3 & _). cbv zeta in *.
  unfold ff_apart, ff_of, ff_size, ff_shsize in *. cbn [ff_class ff_addr ff_flag fst snd] in *.
  destruct (fk_geom k Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _). destruct (fk_geom k' Hk') as (G1' & G2' & G3' & G4' & G5' & G6' & G7' & _).
  destruct (fk_frame_range fsb k p Hk Hp) as [R1 R2]. destruct (fk_frame_range fsb k' p' Hk' Hp') as [R1' R2'].
  assert (FR : fk_frame fsb k p + FB_of k <= fk_frame fsb k' p' \/ fk_frame fsb k' p' + FB_of k' <= fk_frame fsb k p).
  { destruct (Z.eq_dec k k') as [<-|NK]; [| clear - R1 R2 R1' R2' NK; lia].
    assert (NP : p <> p') by (intros ->; apply NE; reflexivity). unfold fk_frame. clear - NP G3. nia. }
  split; [exact FR|]. split.
  - unfold sh. rewrite <- G5, <- G5' in FR. clear - FR A3 B3. Z.div_mod_to_equations. lia.
  - unfold fk_flag. destruct (Z.eq_dec k k') as [<-|NK]; [assert (NP : p <> p') by (intros ->; apply NE; reflexivity); lia|].
    pose proof (fk_flags_apart k k' Hk Hk' NK). lia.
Qed.

#[using="FSB0 FSBM"] Lemma fst_live_wf : forall st, fst_wf st ->
  Forall (fun g => 0 <= ff_class g <= 10 /\ fsb + A0_FS_FRAMES <= ff_addr g /\ ff_addr g + ff_size g <= fsb + A0_FS_SIZE
                   /\ ff_addr g mod 64 = 0 /\ fsb + 4096 <= ff_flag g /\ ff_flag g + 1 <= fsb + A0_FS_FRAMES) (fst_live fsb st).
Proof.
  intros st (FA & _). unfold fst_live. apply Forall_map. eapply Forall_impl; [| exact FA]. intros kp [Hk Hp]. exact (ff_of_wf kp Hk Hp).
Qed.

#[using="FSB0 FSBM"] Lemma fst_new_facts : forall st k, fst_wf st -> 0 <= k <= 10 ->
  let g := snd (fst_malloc fsb st k) in
  ff_class g = k /\ fsb + A0_FS_FRAMES <= ff_addr g /\ ff_addr g + FB_of k <= fsb + A0_FS_SIZE /\ ff_addr g mod 64 = 0
  /\ fsb + 4096 <= ff_flag g /\ ff_flag g + 1 <= fsb + A0_FS_FRAMES
  /\ Forall (ff_apart g) (fst_live fsb st).
Proof.
  intros st k WF Hk. cbv zeta. unfold fst_malloc. cbv zeta. cbn [snd].
  destruct (fst_probe_ok st k WF Hk) as [NI PR]. cbv zeta in NI, PR. set (pos := fst_probe st k mod fk_N k) in *.
  destruct (ff_of_wf (k, pos) Hk PR) as (_ & A1 & A2 & A3 & A4 & A5). cbv zeta in *. unfold ff_size in A2. cbn [ff_of ff_class fst] in A2.
  split; [reflexivity|]. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
  destruct WF as (FA & _). unfold fst_live. apply Forall_map. apply Forall_forall. intros kp Hin.
  destruct (proj1 (Forall_forall _ _) FA kp Hin) as [Hk' Hp'].
  apply ff_of_apart; [exact Hk| exact PR| exact Hk'| exact Hp'|]. intros <-. exact (NI Hin).
Qed.

#[using="FSB0"] Lemma fst_malloc_wf : forall st k, fst_wf st -> 0 <= k <= 10 -> (length (ft_live st) < 15)%nat -> fst_wf (fst (fst_malloc fsb st k)).
Proof.
  intros st k WF Hk LEN. destruct (fst_probe_ok st k WF Hk) as [NI PR]. cbv zeta in NI, PR. destruct WF as (FA & ND & _ & HR).
  unfold fst_malloc. cbv zeta. cbn [fst]. unfold fst_wf. cbn [ft_live ft_hint].
  split; [constructor; [split; [exact Hk| exact PR]| exact FA]|]. split; [constructor; assumption|]. split; [cbn [length]; lia|].
  intros k' Hk'. destruct (k' =? k); [apply Z.mod_pos_bound; lia| exact (HR k' Hk')].
Qed.
#[using="fsb FSB0"] Lemma fst_release_wf : forall st, fst_wf st -> fst_wf (fst_release st).
Proof.
  intros st (FA & ND & LEN & HR). unfold fst_release, fst_wf. cbn [ft_live ft_hint]. destruct (ft_live st) as [|x l]; cbn [tl length] in *.
  - split; [constructor|]. split; [constructor|]. split; [lia| exact HR].
  - apply Forall_cons_iff in FA as [_ FA]. apply NoDup_cons_iff in ND as [_ ND]. split; [exact FA|]. split; [exact ND|]. split; [lia| exact HR].
Qed.

End FK.
