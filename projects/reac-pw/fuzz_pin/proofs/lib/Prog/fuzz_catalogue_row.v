(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module names changed; 85 of its 151 lines of code are new or changed and 3787 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match_lib.v, with its module paths changed; 255 of its 299 lines of code are new or changed and 107 lines of the source are left out. *)
(** fuzz_catalogue_row (plain build, 0x12f9c): proof of [fuzz_catalogue_row_contract] (fuzz_catalogue_row_c.v) from
    the contracts of its two callees, strlen (strlen_c.v) and bcmp (bcmp_c.v).

    Shape: the prologue (12 instructions) saves ra, s0-s4 in the 48-byte frame and reaches the loop head 0x12fcc with
    s0 = &table[0], s4 = 11; [loop] walks the rows (induction on the rows left, as ctrl's
    reac_box_catalogue_match.v); [epi] is the shared exit at 0x13000. The image facts it needs are checked by
    computation: [row_ok] (row i of the table holds the token pointer of pin_spec's row i) and [tok_ok] (each token,
    its NUL and the slack to the next 8-byte boundary are read-only image bytes equal to pin_spec's token). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Image.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec strlen_c bcmp_c fuzz_catalogue_row_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Image bytes *)
Section WithSegs.
Variable segs : list Segment.

Lemma fcr_image_nth : forall n A bs, image_bytes segs A n = Some bs ->
  forall i, (i < n)%nat -> seg_rom segs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros A bs H i Hi; [lia|]. cbn in H.
  destruct (seg_rom segs (wa A)) as [b|] eqn:E; [|discriminate].
  destruct (image_bytes segs (A + 1) n) as [bs'|] eqn:E'; [|discriminate].
  inversion H; subst bs. destruct i as [|i].
  - rewrite Z.add_0_r. exact E.
  - cbn [nth_error]. rewrite <- (IH (A + 1) bs' E' i ltac:(lia)). f_equal. unfold wa. f_equal. lia.
Qed.

Lemma fcr_bytes_img : forall m A n bs, image_bytes segs A n = Some bs -> 0 <= A -> A + Z.of_nat n <= 2^64 ->
  (forall a, A <= a < A + Z.of_nat n -> mrd segs m (wa a) = seg_rom segs (wa a)) -> bytes_at segs m A bs.
Proof.
  intros m A n bs E H0 H1 H. pose proof (image_bytes_length segs n A bs E) as L.
  split; [lia|]. split; [lia|]. intros i Hi.
  rewrite H by lia. apply (fcr_image_nth n A bs E). lia.
Qed.

Lemma fcr_img_apart : forall A n bs lo hi, image_bytes segs A n = Some bs -> (0 < n)%nat -> lo < hi ->
  (forall a, lo <= a < hi -> seg_rom segs (wa a) = None) -> A + Z.of_nat n <= lo \/ hi <= A.
Proof.
  intros A n bs lo hi E Hn Hlh H.
  destruct (Z.le_gt_cases (A + Z.of_nat n) lo) as [L|L]; [left; exact L|].
  destruct (Z.le_gt_cases hi A) as [G|G]; [right; exact G|]. exfalso.
  pose proof (image_bytes_length segs n A bs E) as LB.
  set (x := Z.max A lo).
  assert (I : (Z.to_nat (x - A) < n)%nat) by lia.
  pose proof (fcr_image_nth n A bs E (Z.to_nat (x - A)) I) as R.
  replace (A + Z.of_nat (Z.to_nat (x - A))) with x in R by lia.
  rewrite (H x) in R by lia.
  symmetry in R. apply nth_error_None in R. lia.
Qed.

Lemma fcr_read_all : forall m a bs, bytes_at segs m a bs -> ov_read_bytes segs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read segs m a bs 0 (length bs) H ltac:(lia)) as R.
  cbn [skipn Z.of_nat] in R. rewrite Z.add_0_r, firstn_all in R. exact R.
Qed.

End WithSegs.

(** Row i of the table holds the token pointer of row i of pin_spec. *)
Definition row_ok (i : nat) : bool :=
  match image_bytes rsegs (FUZZ_CATALOGUE + 296 * Z.of_nat i) 8 with
  | Some l => bytes_eqb l (le8 (Z_to_bv 64 (tok_ptr i)))
  | None => false
  end.

Lemma row_ok_all : all_rows row_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma row_img : forall i, (i < CAT_N)%nat ->
  image_bytes rsegs (FUZZ_CATALOGUE + 296 * Z.of_nat i) 8 = Some (le8 (Z_to_bv 64 (tok_ptr i))).
Proof.
  intros i Hi. pose proof (all_rows_spec row_ok row_ok_all i Hi) as H. unfold row_ok in H.
  destruct (image_bytes rsegs (FUZZ_CATALOGUE + 296 * Z.of_nat i) 8) as [l|]; [|discriminate].
  apply bytes_eqb_eq in H. subst l. reflexivity.
Qed.

(** The token of row i, its NUL and the slack up to the next 8-byte boundary (strlen's premise) are read-only image
    bytes. *)
Definition tok_slack (i : nat) : list byte :=
  match image_bytes rsegs (tok_ptr i + Z.of_nat (length (tok_bytes i)) + 1)
          (Z.to_nat ((- (tok_ptr i + Z.of_nat (length (tok_bytes i)) + 1)) mod 8)) with
  | Some l => l
  | None => []
  end.

Definition tok_ok (i : nat) : bool :=
  ro_bytes_b rsegs (tok_ptr i) (tok_bytes i ++ Z_to_bv 8 0 :: tok_slack i) &&
  ((- (tok_ptr i + Z.of_nat (length (tok_bytes i)) + 1)) mod 8 <=? Z.of_nat (length (tok_slack i))) &&
  (0 <=? tok_ptr i) &&
  (tok_ptr i + Z.of_nat (length (tok_bytes i ++ Z_to_bv 8 0 :: tok_slack i)) <=? 2^64) &&
  (Nat.ltb (length (tok_bytes i)) 64).

Lemma tok_ok_all : all_rows tok_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tok_at : forall m i, mem_inv rsegs m -> (i < CAT_N)%nat ->
  bytes_at rsegs m (tok_ptr i) (tok_bytes i ++ Z_to_bv 8 0 :: tok_slack i) /\
  (- (tok_ptr i + Z.of_nat (length (tok_bytes i)) + 1)) mod 8 <= Z.of_nat (length (tok_slack i)) /\
  0 <= tok_ptr i /\ tok_ptr i + Z.of_nat (length (tok_bytes i)) + 1 <= 2^64 /\ (length (tok_bytes i) < 64)%nat.
Proof.
  intros m i MI Hi. pose proof (all_rows_spec tok_ok tok_ok_all i Hi) as H. unfold tok_ok in H.
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Nat.ltb_lt in H5.
  rewrite length_app in H4. cbn [length] in H4.
  split; [|split; [exact H2|split; [exact H3|split; [lia|exact H5]]]].
  apply (ro_bytes_at rsegs m); [exact MI | exact H3 | rewrite length_app; cbn [length]; lia |].
  apply ro_bytes_b_sound. exact H1.
Qed.

Lemma tok_nonul : forall i, (i < CAT_N)%nat -> ~ In (Z_to_bv 8 0) (tok_bytes i).
Proof. intros i Hi Hin. apply (tokens_no_nul i _ Hi Hin). reflexivity. Qed.

(** ** Arithmetic and the model *)
Lemma fcr_mm_spec : forall n l r v, length l = n -> length r = n -> memcmp_model l r n = Some v ->
  (v = 0 <-> l = r) /\ -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v Hl Hr H.
  - destruct l; [|discriminate]. destruct r; [|discriminate]. cbn in H. inversion H. split; [tauto|lia].
  - destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|]. cbn in Hl, Hr, H.
    pose proof (byte_range a). pose proof (byte_range b).
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct (IH l r v ltac:(lia) ltac:(lia) H) as [I1 I2]. split; [|exact I2].
      apply bv_eq in E. subst b. split.
      * intros Hv. f_equal. apply I1. exact Hv.
      * intros Hq. apply I1. injection Hq as Hq. exact Hq.
    + inversion H; subst v. split; [|lia]. split; [lia|]. intros Hq. injection Hq as Hab _. subst b. contradiction.
Qed.

Lemma fcr_eqb_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma fcr_eqb0 : forall v, -2^64 < v < 2^64 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [E|E]; [subst; reflexivity|]. apply Z.eqb_neq. intros E'.
  apply E. change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
Qed.

Lemma rp_hit : forall i sb, (i < CAT_N)%nat -> tok_bytes i = sb ->
  row_ptr FUZZ_CATALOGUE sb = FUZZ_CATALOGUE + 296 * Z.of_nat i.
Proof. intros i sb Hi E. unfold row_ptr. rewrite <- E, (row_of_token i Hi). reflexivity. Qed.

Lemma rp_none : forall sb, (forall j, (j < CAT_N)%nat -> tok_bytes j <> sb) -> row_ptr FUZZ_CATALOGUE sb = 0.
Proof.
  intros sb H. unfold row_ptr. destruct (row_of sb) as [i|] eqn:R; [|reflexivity].
  destruct (row_of_some _ _ R) as (Hi & E & _). exfalso. exact (H i Hi E).
Qed.

(** ** The walk *)
Section Row.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (sb : list byte) (sa Sp lo : Z).
Hypothesis HSL : strlen_contract.
Hypothesis HBC : bcmp_contract.
Hypothesis HB0 : bytes_at rsegs m0 sa sb.
Hypothesis Hsa : 0 <= sa < 2^64.
Hypothesis Hn : Z.of_nat (length sb) < 2^64.
Hypothesis Hlo : 0 <= lo.
Hypothesis HK : lo + 48 <= Sp.
Hypothesis HS : Sp < 2^64.
Hypothesis HD : sa + Z.of_nat (length sb) <= lo \/ Sp <= sa.
Hypothesis HW : forall a, lo <= a < Sp -> seg_rom rsegs (wa a) = None.
Hypothesis HT : forall a, FUZZ_CATALOGUE <= a < FUZZ_CATALOGUE + CAT_BYTES -> mrd rsegs m0 (wa a) = seg_rom rsegs (wa a).

Local Abbreviation Post := (fun ms' : machine_state =>
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (row_ptr FUZZ_CATALOGUE sb))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(Sp - 48, Sp)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo Sp).

(** The frame between the prologue and the epilogue. *)
Definition frm (m : word -> option byte) : Prop :=
  rw_cells rsegs m (Sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  stk rsegs m lo (Sp + -48) /\ munch [(Sp - 48, Sp)] m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m.

Lemma frm_mi : forall m, frm m -> mem_inv rsegs m.
Proof. intros m (_ & _ & _ & _ & MI). exact MI. Qed.

(** strlen and bcmp write nothing. *)
Lemma frm_call : forall m m', frm m -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> frm m'.
Proof.
  intros m m' (FR & ST & MU & WM & _) MU' WM' MI'.
  split; [eapply rw_cells_transport; [exact FR | exact MU' | exact WM' | exact I]|].
  split; [eapply stk_transport_disjoint; [exact ST | exact MU' | exact WM' | exact I]|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU']]; intros x _; exact I|].
  split; [exact (wmono_trans rsegs _ _ _ WM WM') | exact MI'].
Qed.

Lemma frm_sb : forall m, frm m -> bytes_at rsegs m sa sb.
Proof.
  intros m (_ & _ & MU & _ & _). eapply bytes_at_transport; [exact HB0 | exact MU |].
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

(** The token pointer of row i, read from the table. *)
Lemma row_at : forall m i, frm m -> (i < CAT_N)%nat ->
  ov_read_bytes rsegs m (wa (FUZZ_CATALOGUE + 296 * Z.of_nat i)) 8 = Some (le8 (Z_to_bv 64 (tok_ptr i))).
Proof.
  intros m i (_ & _ & MU & _ & _) Hi.
  pose proof (row_img i Hi) as E.
  assert (B0 : bytes_at rsegs m0 (FUZZ_CATALOGUE + 296 * Z.of_nat i) (le8 (Z_to_bv 64 (tok_ptr i)))).
  { apply (fcr_bytes_img rsegs m0 _ 8 _ E); [unfold FUZZ_CATALOGUE; lia | unfold FUZZ_CATALOGUE, CAT_N in *; lia |].
    intros a Ha. apply HT. unfold FUZZ_CATALOGUE, CAT_BYTES, CAT_N in *. lia. }
  pose proof (fcr_img_apart rsegs _ 8 _ lo Sp E ltac:(lia) ltac:(lia) HW) as AP.
  assert (B : bytes_at rsegs m (FUZZ_CATALOGUE + 296 * Z.of_nat i) (le8 (Z_to_bv 64 (tok_ptr i)))).
  { eapply bytes_at_transport; [exact B0 | exact MU |]. rewrite length_le8.
    cbn [disjoint_from]. split; [lia | exact I]. }
  pose proof (fcr_read_all rsegs m _ _ B) as R. rewrite length_le8 in R. exact R.
Qed.

(** The exit 0x13000: a0 = s0, restore ra and s0-s4, return. *)
Lemma epi : forall r m (x1 y0 y1 y2 w9 z0 z1 z2 z3 z4 z5 z6 z7 w18 w19 w20 u3 u4 u5 u6 : word),
  r = row_ptr FUZZ_CATALOGUE sb -> frm m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -48)) gp tp y0 y1 y2 (Z_to_bv 64 r) w9 z0 z1 z2 z3 z4 z5 z6 z7 w18 w19 w20
             s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x13000) fc None m (seg_rom rsegs)).
Proof.
  intros r m x1 y0 y1 y2 w9 z0 z1 z2 z3 z4 z5 z6 z7 w18 w19 w20 u3 u4 u5 u6 Er (FR & ST & MU & WM & MI).
  do 9 step.
  apply evt_done. exists y0, y1, y2, z1, z2, z3, z4, z5, z6, z7, u3, u4, u5, u6, m.
  split; [subst r; unfold mkR; repeat f_equal; lia|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  pose proof (stk_release rsegs m lo (Sp + -48) _ ST FR ltac:(lia)) as R. cbn [cells_size csize Nat.add] in R.
  replace (Sp + -48 + Z.of_nat 48) with Sp in R by lia. exact R.
Qed.

(** The loop head 0x12fcc with i rows done (none of them sb) and k = 11 - i left: s0 = &table[i], s4 = k. *)
Lemma loop : forall k i m (x1 y0 y1 y2 z0 z1 z2 z3 z4 z5 z6 z7 w19 u3 u4 u5 u6 w8 w20 : word),
  w8 = Z_to_bv 64 (FUZZ_CATALOGUE + 296 * Z.of_nat i) -> w20 = Z_to_bv 64 (Z.of_nat k) ->
  (i + k = 11)%nat -> (0 < k)%nat -> (forall j, (j < i)%nat -> tok_bytes j <> sb) -> frm m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -48)) gp tp y0 y1 y2 w8 (Z_to_bv 64 (Z.of_nat (length sb))) z0 z1 z2 z3 z4 z5 z6 z7
             (Z_to_bv 64 sa) w19 w20 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x12fcc) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH];
    intros i m x1 y0 y1 y2 z0 z1 z2 z3 z4 z5 z6 z7 w19 u3 u4 u5 u6 w8 w20 E8 E20 Hik Hk Hnd FRM; [lia|].
  subst w8 w20.
  assert (Hi : (i < CAT_N)%nat) by (unfold CAT_N; lia).
  (* 0x12ff0: the next row, or the end of the table. *)
  assert (NEXT : forall m' (x1' y0' y1' y2' z0' z1' z2' z3' z4' z5' z6' z7' u3' u4' u5' u6' : word),
    tok_bytes i <> sb -> frm m' ->
    evt rsegs Post
      (MS (mkR x1' (Z_to_bv 64 (Sp + -48)) gp tp y0' y1' y2' (Z_to_bv 64 (FUZZ_CATALOGUE + 296 * Z.of_nat i))
               (Z_to_bv 64 (Z.of_nat (length sb))) z0' z1' z2' z3' z4' z5' z6' z7'
               (Z_to_bv 64 sa) (Z_to_bv 64 (tok_ptr i)) (Z_to_bv 64 (Z.of_nat (S k)))
               s5 s6 s7 s8 s9 s10 s11 u3' u4' u5' u6')
          F (Z_to_bv 64 0x12ff0) fc None m' (seg_rom rsegs))).
  { intros m' x1' y0' y1' y2' z0' z1' z2' z3' z4' z5' z6' z7' u3' u4' u5' u6' Hne FRM'.
    assert (Hnd' : forall j, (j < S i)%nat -> tok_bytes j <> sb).
    { intros j Hj. destruct (Nat.eq_dec j i) as [->|Hji]; [exact Hne | apply Hnd; lia]. }
    step. step. step.
    rewrite fcr_eqb_lit by lia.
    destruct (Z.eqb_spec (Z.of_nat (S k) + -1) 0) as [K0|K0]; cbn [negb]; cbv iota.
    - assert (k = 0%nat) by lia. subst k.
      step.
      eapply epi; [|exact FRM'].
      symmetry. apply rp_none. intros j Hj. apply Hnd'. unfold CAT_N in Hj. lia.
    - eapply (IH (S i)); [f_equal; lia | f_equal; lia | lia | lia | exact Hnd' | exact FRM']. }
  pose proof (row_at m i FRM Hi) as RD.
  destruct (tok_at m i (frm_mi m FRM) Hi) as (TB & TS & T0 & TE & TL).
  step. step. step.
  eapply evt_cut.
  { eapply HSL with (str := tok_bytes i) (slack := tok_slack i); rewrite ?unsigned_lit by lia.
    - exact TB.
    - exact (tok_nonul i Hi).
    - exact TS.
    - exact (frm_mi m FRM). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
              MU1 & WM1 & MI1 & _).
  pose proof (frm_call m m1 FRM MU1 WM1 MI1) as FRM1.
  clear MU1 WM1 RD TB.
  rewrite ret_pc_even by (try lia; reflexivity).
  step.
  rewrite fcr_eqb_lit by lia.
  destruct (Z.eqb_spec (Z.of_nat (length (tok_bytes i))) (Z.of_nat (length sb))) as [EL|EL]; cbn [negb]; cbv iota.
  - (* the lengths agree: bcmp(token, s, n) *)
    apply Nat2Z.inj in EL.
    step. step. step. step.
    destruct (tok_at m1 i MI1 Hi) as (TB1 & _). apply bytes_at_app in TB1 as [TB1 _].
    pose proof (frm_sb m1 FRM1) as SB1.
    destruct (memcmp_model_total (tok_bytes i) sb (length sb) ltac:(lia) ltac:(lia)) as [v Hv].
    destruct (fcr_mm_spec (length sb) (tok_bytes i) sb v EL eq_refl Hv) as [MM VR].
    eapply evt_cut.
    { eapply HBC with (ls := tok_bytes i) (rs := sb) (v := v); rewrite ?unsigned_lit by lia.
      - exact TB1.
      - exact SB1.
      - rewrite Nat2Z.id. exact Hv.
      - exact MI1. }
    intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
                m2 & -> & MU2 & WM2 & MI2 & _ & _).
    pose proof (frm_call m1 m2 FRM1 MU2 WM2 MI2) as FRM2.
    clear MU2 WM2 TB1 SB1.
    rewrite ret_pc_even by (try lia; reflexivity).
    step.
    rewrite fcr_eqb0 by lia.
    destruct (Z.eqb_spec v 0) as [V0|V0]; cbv iota.
    + eapply epi; [|exact FRM2].
      symmetry. apply rp_hit; [exact Hi|]. apply MM. exact V0.
    + eapply NEXT; [|exact FRM2]. intros Hq. apply V0. apply MM. exact Hq.
  - (* the lengths differ: next row *)
    eapply NEXT; [|exact FRM1]. intros Hq. apply EL. rewrite Hq. reflexivity.
Qed.

(** The whole function from its entry. *)
Lemma body : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  stk rsegs m0 lo Sp -> mem_inv rsegs m0 ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sa) (Z_to_bv 64 (Z.of_nat (length sb)))
             a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FUZZ_CATALOGUE_ROW) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI.
  (* The prologue's stores transport (and so replace) the section hypothesis HB0 that [loop] needs: take [loop]
     first. *)
  pose proof (loop 11 0) as LP.
  pose proof (munch_refl [(Sp - 48, Sp)] m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  destruct (stk_carve rsegs m0 lo Sp 48 ST ltac:(lia)) as [ST1 [junk FR]]. clear ST.
  change (Z.of_nat 48) with 48 in ST1, FR.
  replace (Sp - 48) with (Sp + -48) in ST1, FR by lia.
  unfold FUZZ_CATALOGUE_ROW.
  do 12 step.
  eapply LP;
    [ first [reflexivity | (unfold FUZZ_CATALOGUE; f_equal; lia)] | reflexivity | lia | lia | intros j Hj; lia | ].
  refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption.
Qed.

End Row.

Theorem fuzz_catalogue_row_holds : strlen_contract -> bcmp_contract -> fuzz_catalogue_row_contract.
Proof.
  intros HSL HBC. unfold fuzz_catalogue_row_contract, FCR_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sb lo
    HB HA1 ST HK HW HD HT MI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1.
  change (bv_modulus 64) with (2^64) in Rsp, Ra0, Ra1.
  pose proof (proj1 ST) as Hlo.
  assert (Ea1 : a1 = Z_to_bv 64 (Z.of_nat (length sb))) by (rewrite <- HA1; symmetry; apply Z_to_bv_lit_self).
  rewrite HA1 in Ra1. subst a1. clear HA1.
  pose proof (Z_to_bv_lit_self sp) as Esp. pose proof (Z_to_bv_lit_self a0) as Ea0.
  set (Sp := bv_unsigned sp) in *. set (sa := bv_unsigned a0) in *.
  rewrite <- Esp, <- Ea0. clearbody Sp sa. clear Esp Ea0.
  eapply body; first [eassumption | lia].
Qed.
