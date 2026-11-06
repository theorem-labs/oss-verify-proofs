(* lib/B/Prog/C_reac_ctrl_identity_replyCover.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0), route (C) phase 2:
   the REGION COVER of the reac_ctrl_identity_reply glue switch.

   The narrowed run reac_ctrl_identity_reply_holds_F_on (lib/B/Prog/reac_ctrl_identity_replyF_on.v), and so its
   decision-125 copy lib/B/Prog/reac_ctrl_identity_replyRB.v, takes
   `shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS) m` (lib/B/Prog/reac_ctrl_identity_reply_c_on.v)
   with FS = ly_F ly.  At a stretch base the glue HAS B.ACtlRtC.ctl_rt_C B ly S m, whose 2nd and 3rd conjuncts are
   `shadow_rw_on (cut_shadow B ly S) m` and `shadow_rw_on img_shadow m` (lib/B/ACtlRtC.v).  rrC_R_cover puts every byte
   of R in cut_shadow B ly S or in img_shadow; rrC_R_on is the corollary the glue calls (ShadowRwOn's union and mono).

   R's disjunct (rA = (S - 128) / 32 * 32)    covered by                       why
     the own real frame rA - 128, 16 bytes    (Z), the stack's zero shadow     [rA - 128, rA) lies in the window
                                                                               [S - 9072, S), inside the machine stack
     the class-1 block                        (FA), the frames area            [sh (FS + 1085440), + 131072) lies in
       (asan_stack_malloc_shadow_R FS 1)                                       [sh (FS + kFakeFramesOff),
                                                                               sh (FS + kFakeStackSize))
     parse on either arm (reply_args):
       parse's own real frame, 16 bytes       (Z)                              below the call's sp, in the window
       parse's class-1 block                  (FA)                             as above
       the record o: real arm rA - 96         (Z)                              [rA - 96, rA - 60) in the window
                     side arm fs_frame+32     (FA) via the class-1 block       its word cover lies in the frame's
                                                                               shadow (FS page-aligned, lo_F_al)
       the message fr (50 <= len)             (L), fr's live heap block        the spec's P10 (under reply_args):
                                                                               In (fr, nb) (ablocks ..), 50 <= req_size
       BC, 6 bytes (50 <= len)                img_shadow                       0x21200 with 64-byte image margins

   rule 24: no function proved (glue of the proved run; lookup of record
   lookup-reac_ctrl_identity_reply.txt (a working note, not in this delivery), CONFIRM in lookup-check.md (a working note, not in this delivery)).
   No Axiom, Parameter, Admitted, admit, Abort.  Nothing of image A is Required. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YM05 YG00 YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require AsanRT ShadowRwOn ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require CtrlRo rng_asan sh_word_on asan_stack_malloc_c
  asan_stack_malloc_c_on reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_ctrl_identity_reply_c_on.
Local Open Scope Z_scope.

(* ---- Arithmetic ---------------------------------------------------------------------------------------------- *)

(* The 8-aligned shadow word cover of [x, x + n) inside a 64-aligned zone [lo, lo + len) lies in the zone's shadow. *)
Lemma rrC_word_in : forall lo len x n a,
  lo mod 64 = 0 -> len mod 64 = 0 -> lo <= x -> x + n <= lo + len -> 0 <= n ->
  B.Prog.sh_word_on.sh_word_on x n a ->
  lib.Reusable.YG0f.SHADOW_OFF + lo / 8 <= a < lib.Reusable.YG0f.SHADOW_OFF + lo / 8 + len / 8.
Proof.
  intros lo len x n a Hlo Hlen H1 H2 H3 [Hn [Ha1 Ha2]].
  unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha1, Ha2.
  unfold lib.Reusable.YG0f.SHADOW_OFF.
  Z.div_mod_to_equations. lia.
Qed.

(* The k shadow bytes from shadow_addr x, for [x, x + 8 k) inside an 8-aligned zone [lo, lo + len). *)
Lemma rrC_sh_in : forall lo len x k a,
  lo mod 8 = 0 -> len mod 8 = 0 -> lo <= x -> x + 8 * k <= lo + len ->
  B.AsanRT.shadow_addr x <= a < B.AsanRT.shadow_addr x + k ->
  lib.Reusable.YG0f.SHADOW_OFF + lo / 8 <= a < lib.Reusable.YG0f.SHADOW_OFF + lo / 8 + len / 8.
Proof.
  intros lo len x k a Hlo Hlen H1 H2 [Ha1 Ha2].
  unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha1, Ha2. unfold lib.Reusable.YG0f.SHADOW_OFF.
  Z.div_mod_to_equations. lia.
Qed.

(* An image global with 64-byte margins: its word cover is image shadow. *)
Lemma rrC_img : forall x n a,
  B.Prog.CtrlRo.IMG_LO + 64 <= x -> x + n + 64 <= B.Prog.CtrlRo.IMG_HI -> 0 <= n ->
  B.Prog.sh_word_on.sh_word_on x n a -> B.ACtlRtC.img_shadow a.
Proof.
  intros x n a H1 H2 H3 [Hn [Ha1 Ha2]]. unfold B.ACtlRtC.img_shadow.
  exists (8 * (a - lib.Reusable.YG0f.SHADOW_OFF)).
  unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha1, Ha2.
  unfold B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI in *.
  unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
  split; [split|]; Z.div_mod_to_equations; lia.
Qed.

(* The record of the side arm, fs_frame FS 1 j + 32, 36 bytes: its word cover lies in the class-1 block's shadow. *)
Lemma rrC_side_box : forall FS j a, FS mod 64 = 0 -> 0 <= j < B.Prog.asan_stack_malloc_c.fs_M 1 ->
  B.Prog.sh_word_on.sh_word_on (B.Prog.asan_stack_malloc_c.fs_frame FS 1 j + 32) 36 a ->
  B.Prog.asan_stack_malloc_c_on.asan_stack_malloc_shadow_R FS 1 a.
Proof.
  intros FS j a HF Hj [_ [Ha1 Ha2]].
  unfold B.Prog.asan_stack_malloc_c_on.asan_stack_malloc_shadow_R.
  change (B.Prog.asan_stack_malloc_c.fs_M 1) with 8192 in Hj.
  assert (EF : forall i, B.Prog.asan_stack_malloc_c.fs_frame FS 1 i = FS + 1085440 + 128 * i).
  { intros i. unfold B.Prog.asan_stack_malloc_c.fs_frame, B.Prog.asan_stack_malloc_c.fs_B.
    change (Z.of_nat 1) with 1. change (2 ^ 20) with 1048576. change (2 ^ 1) with 2. lia. }
  rewrite EF in Ha1, Ha2 |- *.
  unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in *.
  assert (EQ : FS = 64 * (FS / 64)) by (pose proof (Z.div_mod FS 64 ltac:(lia)); lia).
  set (q := FS / 64) in EQ. clearbody q. subst FS.
  Z.div_mod_to_equations. lia.
Qed.

Section Cover.
Context {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

(* (Z): the machine stack, the first zero_shadow_ranges entry (lib/Reusable/YG0n.v:188-189). *)
Lemma rrC_stk_zone : forall ly S a,
  lib.Reusable.YG0f.layout_ok ly ->
  lib.Reusable.YG0f.SHADOW_OFF + lib.Reusable.YG0f.ly_stk_lo ly / 8 <= a <
  lib.Reusable.YG0f.SHADOW_OFF + lib.Reusable.YG0f.ly_stk_lo ly / 8 +
    (lib.Reusable.YG0f.ly_stk_hi ly - lib.Reusable.YG0f.ly_stk_lo ly) / 8 ->
  B.ACtlRtC.cut_shadow B ly S a.
Proof.
  intros ly S a LY Ha. unfold B.ACtlRtC.cut_shadow. right; right; left.
  exists (lib.Reusable.YG0f.ly_stk_lo ly, lib.Reusable.YG0f.ly_stk_hi ly - lib.Reusable.YG0f.ly_stk_lo ly).
  split; [unfold lib.Reusable.YG0n.zero_shadow_ranges; left; reflexivity|].
  unfold lib.Reusable.YG0v.shadow_of_addr. cbn [fst snd]. exact Ha.
Qed.

(* A word cover inside the machine stack is (Z). *)
Lemma rrC_stk_w : forall ly S x n a,
  lib.Reusable.YG0f.layout_ok ly ->
  lib.Reusable.YG0f.ly_stk_lo ly <= x -> x + n <= lib.Reusable.YG0f.ly_stk_hi ly -> 0 <= n ->
  B.Prog.sh_word_on.sh_word_on x n a -> B.ACtlRtC.cut_shadow B ly S a.
Proof.
  intros ly S x n a LY H1 H2 H3 Hsw. apply (rrC_stk_zone ly S a LY).
  pose proof (lib.Reusable.YG0f.lo_top _ LY) as (_ & _ & _ & _ & HALo & HAHi & _).
  unfold lib.Reusable.YG0f.page_aligned in HALo, HAHi.
  exact (rrC_word_in (lib.Reusable.YG0f.ly_stk_lo ly) (lib.Reusable.YG0f.ly_stk_hi ly - lib.Reusable.YG0f.ly_stk_lo ly)
           x n a ltac:(lia) ltac:(lia) H1 ltac:(lia) H3 Hsw).
Qed.

(* k shadow bytes of an 8 k-byte range inside the machine stack are (Z). *)
Lemma rrC_stk_s : forall ly S x k a,
  lib.Reusable.YG0f.layout_ok ly ->
  lib.Reusable.YG0f.ly_stk_lo ly <= x -> x + 8 * k <= lib.Reusable.YG0f.ly_stk_hi ly ->
  B.AsanRT.shadow_addr x <= a < B.AsanRT.shadow_addr x + k -> B.ACtlRtC.cut_shadow B ly S a.
Proof.
  intros ly S x k a LY H1 H2 Ha. apply (rrC_stk_zone ly S a LY).
  pose proof (lib.Reusable.YG0f.lo_top _ LY) as (_ & _ & _ & _ & HALo & HAHi & _).
  unfold lib.Reusable.YG0f.page_aligned in HALo, HAHi.
  exact (rrC_sh_in (lib.Reusable.YG0f.ly_stk_lo ly) (lib.Reusable.YG0f.ly_stk_hi ly - lib.Reusable.YG0f.ly_stk_lo ly)
           x k a ltac:(lia) ltac:(lia) H1 ltac:(lia) Ha).
Qed.

(* The class-1 block of the side stack is (FA), the frames area (the 4th disjunct). *)
Lemma rrC_fa : forall ly S a,
  B.Prog.asan_stack_malloc_c_on.asan_stack_malloc_shadow_R (lib.Reusable.YG0f.ly_F ly) 1 a ->
  B.ACtlRtC.cut_shadow B ly S a.
Proof.
  intros ly S a Ha. unfold B.ACtlRtC.cut_shadow. right; right; right.
  unfold B.Prog.asan_stack_malloc_c_on.asan_stack_malloc_shadow_R, B.Prog.asan_stack_malloc_c.fs_frame,
    B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha.
  change (Z.of_nat 1) with 1 in Ha. change (2 ^ 20) with 1048576 in Ha.
  unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF, lib.Reusable.YG0f.kFakeFramesOff,
    lib.Reusable.YG0f.kFakeStackSize.
  Z.div_mod_to_equations. lia.
Qed.

(* A live block's word cover is (L): fr's 50 bytes inside its block of request size at least 50. *)
Lemma rrC_heap : forall ly S p n x a,
  In (p, n) (lib.Reusable.YG0d.ablocks B ly S) -> x <= lib.Reusable.YG00.req_size n ->
  B.Prog.sh_word_on.sh_word_on p x a -> B.ACtlRtC.cut_shadow B ly S a.
Proof.
  intros ly S p n x a Hin Hx [Hn [Ha1 Ha2]].
  unfold B.ACtlRtC.cut_shadow. right; left. exists p, n. split; [exact Hin|].
  unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K in Ha1, Ha2.
  unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
  assert (M1 : (p + x - 1) / 8 <= (p + lib.Reusable.YG00.req_size n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (M2 : ((p + x - 1) / 8 + 2147450880) / 8 <=
               ((p + lib.Reusable.YG00.req_size n - 1) / 8 + 2147450880) / 8) by (apply Z.div_le_mono; lia).
  replace (2147450880 + p / 8) with (p / 8 + 2147450880) by ring.
  replace (2147450880 + (p + lib.Reusable.YG00.req_size n - 1) / 8)
    with ((p + lib.Reusable.YG00.req_size n - 1) / 8 + 2147450880) by ring.
  lia.
Qed.

(* reac_ctrl_parse's region at a call whose own frame lies in the machine stack, with the record o on the machine stack
   or in a class-1 frame, and fr's block live (under 50 <= len). *)
Lemma rrC_parse : forall ly S fr len o Sp a,
  lib.Reusable.YG0f.layout_ok ly ->
  lib.Reusable.YG0f.ly_stk_lo ly <= (Sp - 128) / 32 * 32 - 128 -> (Sp - 128) / 32 * 32 <= lib.Reusable.YG0f.ly_stk_hi ly ->
  (o <> 0 -> (lib.Reusable.YG0f.ly_stk_lo ly <= o /\ o + 36 <= lib.Reusable.YG0f.ly_stk_hi ly) \/
             (exists j, 0 <= j < B.Prog.asan_stack_malloc_c.fs_M 1 /\
                o = B.Prog.asan_stack_malloc_c.fs_frame (lib.Reusable.YG0f.ly_F ly) 1 j + 32)) ->
  (50 <= len -> exists nb, In (fr, nb) (lib.Reusable.YG0d.ablocks B ly S) /\ 50 <= lib.Reusable.YG00.req_size nb) ->
  B.Prog.reac_ctrl_parse_c.reac_ctrl_parse_shadow_R fr len o Sp (lib.Reusable.YG0f.ly_F ly) a ->
  B.ACtlRtC.cut_shadow B ly S a \/ B.ACtlRtC.img_shadow a.
Proof.
  intros ly S fr len o Sp a LY Hlo Hhi HO HFR HR.
  unfold B.Prog.reac_ctrl_parse_c.reac_ctrl_parse_shadow_R in HR.
  destruct HR as [F16 | [C1 | [[Ho Rw] | [[HL Rw] | [HL Rw]]]]].
  - (* parse's own real frame: (Z) *)
    left. exact (rrC_stk_s ly S _ 16 a LY Hlo ltac:(lia) F16).
  - (* the class-1 block: (FA) *)
    left. exact (rrC_fa ly S a C1).
  - (* the record: (Z) on the machine stack, (FA) in a class-1 frame *)
    left. destruct (HO Ho) as [(H1 & H2) | (j & Hj & ->)].
    + exact (rrC_stk_w ly S o 36 a LY H1 H2 ltac:(lia) Rw).
    + apply rrC_fa. apply (rrC_side_box _ j a); [|exact Hj | exact Rw].
      pose proof (lib.Reusable.YG0f.lo_F_al _ LY) as HF. unfold lib.Reusable.YG0f.page_aligned in HF.
      Z.div_mod_to_equations. lia.
  - (* the message: (L) *)
    left. destruct (HFR HL) as (nb & Hin & Hnb). exact (rrC_heap ly S fr nb 50 a Hin Hnb Rw).
  - (* BC: image *)
    right. refine (rrC_img _ 6 a _ _ ltac:(lia) Rw);
      unfold B.Prog.reac_ctrl_parse_c.REAC_CTRL_PARSE_BC, B.Prog.CtrlRo.IMG_LO, B.Prog.CtrlRo.IMG_HI; lia.
Qed.

(* THE COVER.  Facts, as the glue holds them at a stretch base (ly, S) of the S-B / S-C / tail stretches:
     LY      layout_ok ly                      AR at (ly, S): ARm's am_layout (lib/Reusable/YG0n.v)
     Hlo/Hhi the window inside the stack       the journal's astk_ok with the spec's P7 (rb_win / rsc_win)
     HFR     fr's live block, under reply_args the spec's P10 with the base's ablocks (HAB / HABb) *)
Lemma rrC_R_cover : forall ly S (fr len pa pp pn Sx : Z) a
  (LY : lib.Reusable.YG0f.layout_ok ly)
  (Hlo : lib.Reusable.YG0f.ly_stk_lo ly <= Sx - 9072) (Hhi : Sx <= lib.Reusable.YG0f.ly_stk_hi ly)
  (HFR : lib.Prog.RcReply.reply_args fr pa pp pn = true -> 50 <= len ->
         exists nb, In (fr, nb) (lib.Reusable.YG0d.ablocks B ly S) /\ 50 <= lib.Reusable.YG00.req_size nb),
  reac_ctrl_identity_reply_shadow_R fr len pa pp pn Sx (lib.Reusable.YG0f.ly_F ly) a ->
  B.ACtlRtC.cut_shadow B ly S a \/ B.ACtlRtC.img_shadow a.
Proof.
  intros ly S fr len pa pp pn Sx a LY Hlo Hhi HFR HR.
  unfold reac_ctrl_identity_reply_shadow_R in HR. cbv zeta in HR.
  assert (HA : Sx - 160 <= (Sx - 128) / 32 * 32 <= Sx - 128) by (Z.div_mod_to_equations; lia).
  assert (HA32 : ((Sx - 128) / 32 * 32) mod 32 = 0) by (rewrite Z.mod_mul; lia).
  set (rA := (Sx - 128) / 32 * 32) in *. clearbody rA.
  destruct HR as [F16 | [C1 | [(RA & P) | (RA & j & Hj & P)]]].
  - (* the own real frame rA - 128: (Z) *)
    left. exact (rrC_stk_s ly S (rA - 128) 16 a LY ltac:(lia) ltac:(lia) F16).
  - (* the class-1 block: (FA) *)
    left. exact (rrC_fa ly S a C1).
  - (* reac_ctrl_parse on the real stack: sp = rA - 128, o = rA - 96 *)
    apply (rrC_parse ly S fr len (rA - 96) (rA - 128) a LY); [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia
      | intros _; left; lia | exact (HFR RA) | exact P].
  - (* reac_ctrl_parse on the side stack: sp = rA, o = fs_frame FS 1 j + 32 *)
    apply (rrC_parse ly S fr len (B.Prog.asan_stack_malloc_c.fs_frame (lib.Reusable.YG0f.ly_F ly) 1 j + 32) rA a LY);
      [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | intros _; right; exists j; split; [exact Hj | reflexivity]
      | exact (HFR RA) | exact P].
Qed.

(* The corollary the glue calls: ctl_rt_C's 2nd and 3rd conjuncts give the run's narrowed premise. *)
Lemma rrC_R_on : forall ly S (fr len pa pp pn Sx : Z) (m : word -> option byte)
  (LY : lib.Reusable.YG0f.layout_ok ly)
  (Hlo : lib.Reusable.YG0f.ly_stk_lo ly <= Sx - 9072) (Hhi : Sx <= lib.Reusable.YG0f.ly_stk_hi ly)
  (HFR : lib.Prog.RcReply.reply_args fr pa pp pn = true -> 50 <= len ->
         exists nb, In (fr, nb) (lib.Reusable.YG0d.ablocks B ly S) /\ 50 <= lib.Reusable.YG00.req_size nb),
  B.ShadowRwOn.shadow_rw_on (B.ACtlRtC.cut_shadow B ly S) m ->
  B.ShadowRwOn.shadow_rw_on B.ACtlRtC.img_shadow m ->
  B.ShadowRwOn.shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn Sx (lib.Reusable.YG0f.ly_F ly)) m.
Proof.
  intros ly S fr len pa pp pn Sx m LY Hlo Hhi HFR HC HI.
  exact (B.ShadowRwOn.shadow_rw_on_mono _ _ m
           (fun a => rrC_R_cover ly S fr len pa pp pn Sx a LY Hlo Hhi HFR)
           (B.ShadowRwOn.shadow_rw_on_union _ _ m HC HI)).
Qed.

End Cover.
