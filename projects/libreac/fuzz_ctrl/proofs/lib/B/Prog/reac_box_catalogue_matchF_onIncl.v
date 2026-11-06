(* lib/B/Prog/reac_box_catalogue_matchF_onIncl.v -- route (C), image B: the region-inclusion lemmas of
   reac_box_catalogue_match's `_on` run (lib/B/Prog/reac_box_catalogue_matchF_on.v, a Theorem Labs lane).  A Theorem Labs
   lane, 2026-10-29.

   R := reac_box_catalogue_match_shadow_R f len Sp FS (reac_box_catalogue_match_c.v, the route-(C) block) is the region
   the run carries as `shadow_rw_on R m`.  At each callee call the run feeds the callee its own region by
   shadow_rw_on_mono (ShadowRwOn.v), which needs `R_callee a -> R a` there; its own shadow stores need R to hold its
   frame's shadow.  Each lemma below is that inclusion, stated `<call-site facts> -> forall a, R_callee a -> R a`, so
   `cmOn_R_x <facts>` is the inclusion premise of shadow_rw_on_mono as it stands:
     cmOn_R_blk    the class-c side-stack block, c <= 2 (cm_cf_rd, reac_box_catalogue_matchF.v:2856);
     cmOn_R_malloc __asan_stack_malloc_2's region (asan_stack_malloc_c_on.v:33);
     cmOn_R_fr     the 32 shadow bytes of the class-2 frame fr (fk_facts F:386, the header, mark and release stores);
     cmOn_R_win    a callee window's shadow [shadow_addr lo, shadow_addr sp2) (cm_cf_rd, F:2859);
     cmOn_R_parse  reac_ctrl_parse's region at its call, f len (fr + 32) sp2 FS (F:4246);
     cmOn_R_mb     reac_box_model_block's region at its call, sp2 FS (CM_T + 296 i) 0 (fr + 112) row nb (F:3494);
     cmOn_R_bcmp   the bcmp wrapper's region at its call, (f + 18) (fr + 112) 32 (F:3625).
   The frame facts are ONE hypothesis, cmOn_fr_facts Sp FS fr sp2 jj nn: the accepted run's cmFK fr sp2 jj nn (F:339-341)
   with its CA (F:332, (Sp - 128) / 32 * 32) unfolded, so a run in a copy of Section MatchF passes its cmFK hypothesis
   as it is (the two are convertible).  No lemma needs an alignment of FS or of Sp: the real arm's pieces lie in the
   window's shadow (W) and the side arm's in the shadow of the side stack's class-0/1/2 blocks, which are contiguous.

   Region arithmetic over existing definitions only.  rule 24: no function proved. *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c asan_stack_malloc_c_on
  sh_word_on reac_ctrl_parse_c reac_box_model_block_c reac_box_model_block_c_on bcmp_wrap_c_on
  reac_box_catalogue_match_c.
Local Open Scope Z_scope.

(* ---- shadow_addr and the shadow word covers ---- *)

Lemma cmOn_sa_mono : forall x y, x <= y -> shadow_addr x <= shadow_addr y.
Proof. intros x y H. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma cmOn_sa_add : forall x k, shadow_addr (x + 8 * k) = shadow_addr x + k.
Proof. intros x k. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma cmOn_al8_lo : forall p, shadow_addr (p - 56) <= rng_asan.sh_al8_lo p.
Proof. intros p. unfold rng_asan.sh_al8_lo, shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma cmOn_al8_hi : forall p n, rng_asan.sh_al8_hi p n <= shadow_addr (p + n + 63).
Proof. intros p n. unfold rng_asan.sh_al8_hi, shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma cmOn_al8_mono : forall x y, x <= y -> shadow_addr x / 8 * 8 <= shadow_addr y / 8 * 8.
Proof. intros x y H. pose proof (cmOn_sa_mono x y H) as M. Z.div_mod_to_equations. lia. Qed.

(* The shadow word cover of the n bytes at p lies in the shadow of [p - 56, p + n + 63). *)
Lemma cmOn_sh_word_in : forall p n a, sh_word_on p n a -> shadow_addr (p - 56) <= a < shadow_addr (p + n + 63).
Proof.
  intros p n a H. unfold sh_word_on in H. destruct H as (_ & H1 & H2).
  pose proof (cmOn_al8_lo p). pose proof (cmOn_al8_hi p n). lia.
Qed.

(* The cover of a part of a range is part of the range's cover. *)
Lemma cmOn_sh_word_sub : forall p n p' n' a, p <= p' -> p' + n' <= p + n -> 0 < n' ->
  sh_word_on p' n' a -> sh_word_on p n a.
Proof.
  intros p n p' n' a H1 H2 H3 H. unfold sh_word_on, rng_asan.sh_al8_lo, rng_asan.sh_al8_hi in *.
  destruct H as (_ & H4 & H5).
  pose proof (cmOn_al8_mono p p' H1) as M1.
  pose proof (cmOn_al8_mono (p' + n' - 1) (p + n - 1) ltac:(lia)) as M2.
  split; [lia|]. lia.
Qed.

(* ---- the side stack's class-c frames ---- *)

Lemma cmOn_fs_base : forall FS c, fs_frame FS c 0 = FS + 36864 + 1048576 * Z.of_nat c.
Proof.
  intros FS c. unfold fs_frame.
  assert (E : 2 ^ 20 = 1048576) by reflexivity. rewrite E. lia.
Qed.

Lemma cmOn_fs_frame2 : forall FS jj, fs_frame FS 2 jj = FS + 2134016 + 256 * jj.
Proof.
  intros FS jj. unfold fs_frame.
  assert (E1 : Z.of_nat 2 * 2 ^ 20 = 2097152) by reflexivity.
  assert (E2 : fs_B 2 = 256) by reflexivity.
  rewrite E1, E2. lia.
Qed.

(* ---- the frame facts of both arms ---- *)

(* The accepted run's cmFK fr sp2 jj nn (reac_box_catalogue_matchF.v:339-341) with CA = (Sp - 128) / 32 * 32 (F:332)
   unfolded: the real arm (fr = sp2 = CA - 192) or the side arm (fr = fs_frame FS 2 jj, sp2 = CA). *)
Definition cmOn_fr_facts (Sp FS fr sp2 jj nn : Z) : Prop :=
  (fr = (Sp - 128) / 32 * 32 - 192 /\ sp2 = (Sp - 128) / 32 * 32 - 192 /\ jj = 0 /\ nn = 0) \/
  (0 <= jj < fs_M 2 /\ fr = fs_frame FS 2 jj /\ sp2 = (Sp - 128) / 32 * 32 /\ nn = 1).

(* sp2 lies just below Sp; the real frame lies in the window [Sp - 9136, Sp), a side frame in the class-2 block. *)
Lemma cmOn_fr_arms : forall Sp FS fr sp2 jj nn, cmOn_fr_facts Sp FS fr sp2 jj nn ->
  Sp - 351 <= sp2 <= Sp - 128 /\
  ((Sp - 351 <= fr /\ fr + 256 <= Sp) \/ (FS + 2134016 <= fr /\ fr + 256 <= FS + 3182592)).
Proof.
  intros Sp FS fr sp2 jj nn FK. unfold cmOn_fr_facts in FK.
  destruct FK as [(Ef & Es & _ & _) | (Hj & Ef & Es & _)].
  - subst fr sp2. split; [|left]; Z.div_mod_to_equations; lia.
  - rewrite cmOn_fs_frame2 in Ef.
    assert (EM : fs_M 2 = 4096) by reflexivity. rewrite EM in Hj.
    subst fr sp2. split; [|right]; Z.div_mod_to_equations; lia.
Qed.

(* ---- the pieces of R ---- *)

Lemma cmOn_R_blk : forall f len Sp FS (c : nat), (c <= 2)%nat ->
  forall a, asan_stack_malloc_shadow_R FS c a -> reac_box_catalogue_match_shadow_R f len Sp FS a.
Proof.
  intros f len Sp FS c Hc a Ha. unfold reac_box_catalogue_match_shadow_R. right; left.
  exists c. split; [exact Hc | exact Ha].
Qed.

Lemma cmOn_R_malloc : forall f len Sp FS a,
  asan_stack_malloc_shadow_R FS 2 a -> reac_box_catalogue_match_shadow_R f len Sp FS a.
Proof. intros f len Sp FS a Ha. exact (cmOn_R_blk f len Sp FS 2 ltac:(lia) a Ha). Qed.

(* (W): the shadow of a range inside the window [Sp - 9136, Sp). *)
Lemma cmOn_R_win : forall f len Sp FS lo sp2, Sp - 9136 <= lo -> sp2 <= Sp ->
  forall a, shadow_addr lo <= a < shadow_addr sp2 -> reac_box_catalogue_match_shadow_R f len Sp FS a.
Proof.
  intros f len Sp FS lo sp2 Hlo Hhi a Ha. unfold reac_box_catalogue_match_shadow_R, CM_K. left.
  pose proof (cmOn_sa_mono _ _ Hlo). pose proof (cmOn_sa_mono _ _ Hhi). lia.
Qed.

(* The shadow of a range inside the side stack's class-0/1/2 blocks [FS + 36864, FS + 36864 + 3 * 2^20): their
   three 131072-byte shadows are contiguous. *)
Lemma cmOn_R_area : forall f len Sp FS lo hi, FS + 36864 <= lo -> hi <= FS + 3182592 ->
  forall a, shadow_addr lo <= a < shadow_addr hi -> reac_box_catalogue_match_shadow_R f len Sp FS a.
Proof.
  intros f len Sp FS lo hi Hlo Hhi a Ha.
  pose proof (cmOn_sa_mono _ _ Hlo) as L. pose proof (cmOn_sa_mono _ _ Hhi) as H.
  assert (E : forall c : nat, shadow_addr (fs_frame FS c 0) = shadow_addr (FS + 36864) + 131072 * Z.of_nat c).
  { intros c. rewrite cmOn_fs_base. unfold shadow_addr. Z.div_mod_to_equations. lia. }
  assert (E3 : shadow_addr (FS + 3182592) = shadow_addr (FS + 36864) + 393216).
  { unfold shadow_addr. Z.div_mod_to_equations. lia. }
  unfold reac_box_catalogue_match_shadow_R. right; left.
  destruct (Z_lt_le_dec a (shadow_addr (FS + 36864) + 131072)) as [C0|C0].
  - exists 0%nat. split; [lia|]. unfold asan_stack_malloc_shadow_R. rewrite E. lia.
  - destruct (Z_lt_le_dec a (shadow_addr (FS + 36864) + 262144)) as [C1|C1].
    + exists 1%nat. split; [lia|]. unfold asan_stack_malloc_shadow_R. rewrite E. lia.
    + exists 2%nat. split; [lia|]. unfold asan_stack_malloc_shadow_R. rewrite E. lia.
Qed.

(* The shadow of a range around the class-2 frame, [fr - 56, fr + 256), on either arm. *)
Lemma cmOn_R_frw : forall f len Sp FS fr sp2 jj nn, cmOn_fr_facts Sp FS fr sp2 jj nn ->
  forall lo hi, fr - 56 <= lo -> hi <= fr + 256 ->
  forall a, shadow_addr lo <= a < shadow_addr hi -> reac_box_catalogue_match_shadow_R f len Sp FS a.
Proof.
  intros f len Sp FS fr sp2 jj nn FK lo hi Hlo Hhi a Ha.
  destruct (cmOn_fr_arms Sp FS fr sp2 jj nn FK) as (_ & [(F1 & F2) | (F1 & F2)]).
  - refine (cmOn_R_win f len Sp FS lo hi _ _ a Ha); lia.
  - refine (cmOn_R_area f len Sp FS lo hi _ _ a Ha); lia.
Qed.

(* ---- the run's own frame and the callees' regions at their calls ---- *)

(* The 32 shadow bytes of the class-2 frame (its 24 header bytes, the marks and the 32-byte release). *)
Lemma cmOn_R_fr : forall f len Sp FS fr sp2 jj nn, cmOn_fr_facts Sp FS fr sp2 jj nn ->
  forall a, shadow_addr fr <= a < shadow_addr fr + 32 -> reac_box_catalogue_match_shadow_R f len Sp FS a.
Proof.
  intros f len Sp FS fr sp2 jj nn FK a Ha.
  pose proof (cmOn_sa_add fr 32) as E.
  refine (cmOn_R_frw f len Sp FS fr sp2 jj nn FK fr (fr + 8 * 32) _ _ a _); lia.
Qed.

(* reac_ctrl_parse's region at its call (f, len, the box fr + 32, sp2, FS): its real frame lies in the window, its
   class-1 block is R's, the box's words lie around the frame, and the f and BC words carry R's own 50 <= len guard. *)
Lemma cmOn_R_parse : forall f len Sp FS fr sp2 jj nn, cmOn_fr_facts Sp FS fr sp2 jj nn ->
  forall a, reac_ctrl_parse_shadow_R f len (fr + 32) sp2 FS a -> reac_box_catalogue_match_shadow_R f len Sp FS a.
Proof.
  intros f len Sp FS fr sp2 jj nn FK a Ha.
  destruct (cmOn_fr_arms Sp FS fr sp2 jj nn FK) as (Hsp2 & _).
  unfold reac_ctrl_parse_shadow_R in Ha.
  destruct Ha as [Ha | [Ha | [(_ & Ha) | [(L & Ha) | (L & Ha)]]]].
  - assert (HX : Sp - 9136 <= (sp2 - 128) / 32 * 32 - 128 /\ (sp2 - 128) / 32 * 32 - 128 + 8 * 16 <= Sp)
      by (Z.div_mod_to_equations; lia).
    pose proof (cmOn_sa_add ((sp2 - 128) / 32 * 32 - 128) 16) as E.
    refine (cmOn_R_win f len Sp FS ((sp2 - 128) / 32 * 32 - 128) ((sp2 - 128) / 32 * 32 - 128 + 8 * 16) _ _ a _);
      lia.
  - exact (cmOn_R_blk f len Sp FS 1 ltac:(lia) a Ha).
  - apply cmOn_sh_word_in in Ha.
    refine (cmOn_R_frw f len Sp FS fr sp2 jj nn FK _ _ _ _ a Ha); lia.
  - unfold reac_box_catalogue_match_shadow_R. right; right. split; [exact L|]. left. exact Ha.
  - unfold reac_box_catalogue_match_shadow_R. right; right. split; [exact L|]. right; right. exact Ha.
Qed.

(* reac_box_model_block's region at the call of row i (sp2, FS, the row CM_T + 296 i, b = 0, the output fr + 112):
   its window cover lies in the window, its class-0 block is R's, the row's words lie in T's (i < 11, under
   50 <= len), the output's words lie around the frame, and the name and JOIN pieces are empty at b = 0. *)
Lemma cmOn_R_mb : forall f len Sp FS fr sp2 jj nn (i : nat) row nb, 50 <= len -> (i < 11)%nat ->
  cmOn_fr_facts Sp FS fr sp2 jj nn ->
  forall a, reac_box_model_block_shadow_R sp2 FS (CM_T + 296 * Z.of_nat i) 0 (fr + 112) row nb a ->
    reac_box_catalogue_match_shadow_R f len Sp FS a.
Proof.
  intros f len Sp FS fr sp2 jj nn i row nb L Hi FK a Ha.
  destruct (cmOn_fr_arms Sp FS fr sp2 jj nn FK) as (Hsp2 & _).
  unfold reac_box_model_block_shadow_R in Ha.
  destruct Ha as [Ha | [Ha | [(_ & Ha) | [(_ & Hb & _) | [(_ & Ha) | [(Hb & _) | (Hb & _)]]]]]].
  - apply cmOn_sh_word_in in Ha. unfold REAC_BOX_MODEL_BLOCK_K in Ha.
    refine (cmOn_R_win f len Sp FS _ _ _ _ a Ha); lia.
  - exact (cmOn_R_blk f len Sp FS 0 ltac:(lia) a Ha).
  - unfold reac_box_catalogue_match_shadow_R. right; right. split; [exact L|]. right; left.
    refine (cmOn_sh_word_sub CM_T 3256 (CM_T + 296 * Z.of_nat i) 296 a _ _ _ Ha); lia.
  - lia.
  - apply cmOn_sh_word_in in Ha.
    refine (cmOn_R_frw f len Sp FS fr sp2 jj nn FK _ _ _ _ a Ha); lia.
  - lia.
  - lia.
Qed.

(* The bcmp wrapper's region at its call ((f + 18), (fr + 112), 32): the left operand's words lie in f's (under
   50 <= len), the right operand's around the frame. *)
Lemma cmOn_R_bcmp : forall f len Sp FS fr sp2 jj nn, 50 <= len -> cmOn_fr_facts Sp FS fr sp2 jj nn ->
  forall a, bcmp_wrap_shadow_R (f + 18) (fr + 112) 32 a -> reac_box_catalogue_match_shadow_R f len Sp FS a.
Proof.
  intros f len Sp FS fr sp2 jj nn L FK a Ha.
  unfold bcmp_wrap_shadow_R in Ha. destruct Ha as [Ha | Ha].
  - unfold reac_box_catalogue_match_shadow_R. right; right. split; [exact L|]. left.
    refine (cmOn_sh_word_sub f 50 (f + 18) 32 a _ _ _ Ha); lia.
  - apply cmOn_sh_word_in in Ha.
    refine (cmOn_R_frw f len Sp FS fr sp2 jj nn FK _ _ _ _ a Ha); lia.
Qed.
