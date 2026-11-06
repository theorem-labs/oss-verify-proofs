(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module names changed; 85 of its 151 lines of code are new or changed and 3787 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match_lib.v, with its module paths changed; 255 of its 299 lines of code are new or changed and 107 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/Prog/fuzz_catalogue_row.v, with its module names changed; 601 of its 675 lines of code are new or changed and 225 lines of the source are left out. *)
(** reac_box_pin_parse (plain image, 0x12e90, 67 instructions) against reac_box_pin_parse_contract
    (Prog/reac_box_pin_parse_c.v), with the contracts of its callees strcspn, reac_box_catalogue, strlen and strncmp as
    premises. The walk: prologue and the NULL / empty-spec refusals; strcspn(spec, ":") = colon_idx; the count from
    reac_box_catalogue; the row loop (an induction on the rows left, each row a strlen and, on a length match, a
    strncmp); on a hit the label choice and the two stores; the shared epilogue. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Cells Step Image.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import RcLib RcLeafLib.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec fuzz_catalogue_row_c.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import strcspn_c reac_box_catalogue_c strlen_c strncmp_c.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import reac_box_pin_parse_c.
Import ListNotations.
Open Scope Z_scope.

Ltac ret_lit := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.

(** Resolve the branch in the pc: the condition is proved true or false with rc_cond. *)
Ltac pp_go := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with true; [cbv iota | symmetry; rc_cond]
            | replace c with false; [cbv iota | symmetry; rc_cond]
            | idtac "PP_GO_FAIL" c; fail 1 ]
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PP_GO_NOIF" pc; fail 1
  end.

(** * Generic facts *)
Section WithSegs.
Variable segs : list Segment.

Lemma pp_image_nth : forall n A bs, image_bytes segs A n = Some bs ->
  forall i, (i < n)%nat -> seg_rom segs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros A bs H i Hi; [lia|]. cbn in H.
  destruct (seg_rom segs (wa A)) as [b|] eqn:E; [|discriminate].
  destruct (image_bytes segs (A + 1) n) as [bs'|] eqn:E'; [|discriminate].
  inversion H; subst bs. destruct i as [|i].
  - rewrite Z.add_0_r. exact E.
  - cbn [nth_error]. rewrite <- (IH (A + 1) bs' E' i ltac:(lia)). f_equal. unfold wa. f_equal. lia.
Qed.

Lemma pp_bytes_img : forall m A n bs, image_bytes segs A n = Some bs -> 0 <= A -> A + Z.of_nat n <= 2^64 ->
  (forall a, A <= a < A + Z.of_nat n -> mrd segs m (wa a) = seg_rom segs (wa a)) -> bytes_at segs m A bs.
Proof.
  intros m A n bs E H0 H1 H. pose proof (image_bytes_length segs n A bs E) as L.
  split; [lia|]. split; [lia|]. intros i Hi.
  rewrite H by lia. apply (pp_image_nth n A bs E). lia.
Qed.

Lemma pp_img_apart : forall A n bs lo hi, image_bytes segs A n = Some bs -> (0 < n)%nat -> lo < hi ->
  (forall a, lo <= a < hi -> seg_rom segs (wa a) = None) -> A + Z.of_nat n <= lo \/ hi <= A.
Proof.
  intros A n bs lo hi E Hn Hlh H.
  destruct (Z.le_gt_cases (A + Z.of_nat n) lo) as [L|L]; [left; exact L|].
  destruct (Z.le_gt_cases hi A) as [G|G]; [right; exact G|]. exfalso.
  pose proof (image_bytes_length segs n A bs E) as LB.
  set (x := Z.max A lo).
  assert (I : (Z.to_nat (x - A) < n)%nat) by lia.
  pose proof (pp_image_nth n A bs E (Z.to_nat (x - A)) I) as R.
  replace (A + Z.of_nat (Z.to_nat (x - A))) with x in R by lia.
  rewrite (H x) in R by lia.
  symmetry in R. apply nth_error_None in R. lia.
Qed.

Lemma pp_rw_split : forall m A cs1 cs2, rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] Hw]. apply cells_wf_app in Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [B1 B2].
  rewrite cells_size_app in Hw. destruct Hw as (Ha & Hn & Hw).
  rewrite (cells_bytes_length cs1 W1) in B2.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply Hw. lia.
Qed.

Lemma pp_rw_join : forall m A B cs1 cs2, rw_cells segs m A cs1 -> rw_cells segs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] (Ha & Hn1 & H1)] [[W2 B2] (Hb & Hn2 & H2)] ->.
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite (cells_bytes_length cs1 W1). exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))); [apply H1; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply H2. lia.
Qed.

Lemma pp_wr_of_rw : forall m A n bs, rw_cells segs m A [CB n bs] -> wr_at segs m A (Z.of_nat n).
Proof. intros m A n bs [_ HW]. cbn [cells_size csize] in HW. rewrite Nat.add_0_r in HW. exact HW. Qed.

Lemma pp_rw_c8 : forall m A v, bytes_at segs m A (le8 v) -> wr_at segs m A 8 -> rw_cells segs m A [C8 v].
Proof.
  intros m A v HB HW. split; [split|].
  - split; exact I.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - exact HW.
Qed.

End WithSegs.

Lemma pp_bytes_ext : forall l1 l2 : list byte, map (@bv_unsigned 8) l1 = map (@bv_unsigned 8) l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn [map] in H; try discriminate; [reflexivity|].
  injection H as Hxy Hl. f_equal; [apply bv_eq; exact Hxy | apply IH; exact Hl].
Qed.

Lemma eqb_nat : forall x y : nat, Z.of_nat x < 2^64 -> Z.of_nat y < 2^64 ->
  bv_eqb (Z_to_bv 64 (Z.of_nat x)) (Z_to_bv 64 (Z.of_nat y)) = Nat.eqb x y.
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia.
  destruct (Nat.eqb_spec x y) as [E|E]; [subst; apply Z.eqb_refl | apply Z.eqb_neq; lia].
Qed.

Lemma eqb_small : forall w, -256 < w < 256 -> bv_eqb (Z_to_bv 64 w) (Z_to_bv 64 0) = (w =? 0).
Proof.
  intros w Hw. unfold bv_eqb. rewrite (unsigned_lit 0) by lia. rewrite unsigned_lit_wrap.
  destruct (Z.eqb_spec w 0) as [->|E]; [reflexivity|]. apply Z.eqb_neq. intros C. apply E.
  Z.div_mod_to_equations. lia.
Qed.

Lemma eqb_nat0 : forall x : nat, Z.of_nat x < 2^64 ->
  bv_eqb (Z_to_bv 64 (Z.of_nat x)) (Z_to_bv 64 0) = Nat.eqb x 0.
Proof. intros x Hx. exact (eqb_nat x 0 Hx ltac:(lia)). Qed.

Lemma notin_nul_hd : forall (x : byte) l, ~ In NUL (x :: l) -> bv_unsigned x <> 0.
Proof. intros x l H E. apply H. left. apply bv_eq. rewrite E. reflexivity. Qed.

(** * strcspn with the set ":" is colon_idx *)
Lemma cspn_colon : forall s, cspn_len [Z_to_bv 8 58] s = colon_idx s.
Proof.
  induction s as [|x s IH]; [reflexivity|]. cbn [cspn_len colon_idx existsb].
  rewrite orb_false_r. change (bv_unsigned (Z_to_bv 8 58)) with 58. unfold COLON.
  rewrite Z.eqb_sym. destruct (bv_unsigned x =? 58); [reflexivity|]. f_equal. exact IH.
Qed.

(** * strncmp of the spec against a token of the same length as the spec's token *)
Lemma ncmp_walk : forall k (a b la lb : list byte), length a = S k -> length b = S k ->
  ~ In NUL a -> ~ In NUL b ->
  exists v, strncmp_walk (a ++ la) (b ++ lb) k = Some v /\ (v = 0 <-> a = b) /\ -256 < v < 256.
Proof.
  induction k as [|k IH]; intros a b la lb Ha Hb Na Nb.
  - destruct a as [|x a']; [discriminate|]. destruct a' as [|x' a'']; [|cbn [length] in Ha; lia].
    destruct b as [|y b']; [discriminate|]. destruct b' as [|y' b'']; [|cbn [length] in Hb; lia].
    pose proof (notin_nul_hd x [] Na) as Nx. pose proof (notin_nul_hd y [] Nb) as Ny.
    pose proof (byte_range x). pose proof (byte_range y).
    cbn [app strncmp_walk]. rewrite Nat.eqb_refl, orb_true_r. cbn [orb].
    exists (bv_unsigned x - bv_unsigned y). split; [reflexivity|]. split; [|lia].
    split; intros E.
    + f_equal. apply bv_eq. lia.
    + injection E as E. subst. lia.
  - destruct a as [|x a']; [discriminate|]. destruct b as [|y b']; [discriminate|].
    cbn [length] in Ha, Hb.
    pose proof (notin_nul_hd x a' Na) as Nx. pose proof (notin_nul_hd y b' Nb) as Ny.
    assert (Na' : ~ In NUL a') by (intros H; apply Na; right; exact H).
    assert (Nb' : ~ In NUL b') by (intros H; apply Nb; right; exact H).
    pose proof (byte_range x). pose proof (byte_range y).
    cbn [app strncmp_walk].
    rewrite (proj2 (Z.eqb_neq _ _) Nx), (proj2 (Z.eqb_neq _ _) Ny). cbn [orb Nat.eqb].
    destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)) as [E|E]; cbn [negb].
    + destruct (IH a' b' la lb ltac:(lia) ltac:(lia) Na' Nb') as (v & Hv & Hiff & Hr).
      exists v. split; [exact Hv|]. split; [|exact Hr].
      apply bv_eq in E. subst y. rewrite Hiff.
      split; [intros ->; reflexivity | intros H'; injection H' as H'; exact H'].
    + exists (bv_unsigned x - bv_unsigned y). split; [reflexivity|]. split; [|lia].
      split; intros H'; [lia | injection H' as H' _; subst; contradiction].
Qed.

Lemma ncmp_tok : forall (s sl t tl : list byte) n, ~ In NUL s -> ~ In NUL t -> (n <= length s)%nat ->
  length t = n -> (0 < n)%nat ->
  exists v, strncmp_model (s ++ NUL :: sl) (t ++ NUL :: tl) (Z.of_nat n) = Some v /\
    (v = 0 <-> t = firstn n s) /\ -256 < v < 256.
Proof.
  intros s sl t tl n Hs Ht Hn Hl Hp.
  destruct n as [|k]; [lia|].
  destruct (ncmp_walk k (firstn (S k) s) t (skipn (S k) s ++ NUL :: sl) (NUL :: tl)) as (v & Hv & Hiff & Hr).
  - rewrite length_firstn. lia.
  - exact Hl.
  - intros H. apply Hs. rewrite <- (firstn_skipn (S k) s). apply in_or_app. left. exact H.
  - exact Ht.
  - exists v. split; [|split; [|exact Hr]].
    + unfold strncmp_model. replace (Z.of_nat (S k) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (Z.to_nat (Z.of_nat (S k) - 1)) with k by lia.
      rewrite app_assoc, firstn_skipn in Hv. exact Hv.
    + rewrite Hiff. split; intros H; symmetry; exact H.
Qed.

(** * The image: the table, the tokens and the set ":" *)
Definition PB_TBL : list byte := match image_bytes rsegs 116528 3256 with Some l => l | None => [] end.

Lemma PB_TBL_eq : image_bytes rsegs 116528 3256 = Some PB_TBL.
Proof. vm_compute. reflexivity. Qed.

Lemma PB_TBL_len : length PB_TBL = 3256%nat.
Proof. exact (image_bytes_length rsegs 3256 116528 PB_TBL PB_TBL_eq). Qed.

(** Row i holds its token pointer at +0 and its display pointer at +8. *)
Lemma pp_row : forall i, (i < CAT_N)%nat ->
  firstn 8 (skipn (296 * i) PB_TBL) = le8 (Z_to_bv 64 (tok_ptr i)) /\
  firstn 8 (skipn (296 * i + 8) PB_TBL) = le8 (Z_to_bv 64 (disp_ptr i)).
Proof.
  intros i Hi. unfold CAT_N in Hi.
  do 11 (destruct i as [|i]; [split; apply pp_bytes_ext; vm_compute; reflexivity|]). lia.
Qed.

(** The bytes after each token's NUL up to the next 8-byte boundary (read from the image). *)
Definition tok_sls : list (list Z) :=
  [[115; 52; 48; 48; 48]; [78; 65; 78]; [47; 100; 101; 118; 47; 110]; [70; 114; 101; 101; 82];
   [0; 46; 0; 117; 115]; [83]; [105; 110; 102; 0]; [70; 114; 101; 101; 82; 69]; [83; 45]; [70]; [115; 52; 48]].
Definition tok_sl (i : nat) : list byte := map (Z_to_bv 8) (nth i tok_sls []).

Definition tok_ok (i : nat) : bool :=
  ro_bytes_b rsegs (tok_ptr i) (tok_bytes i ++ NUL :: tok_sl i) &&
  ((- (tok_ptr i + Z.of_nat (length (tok_bytes i)) + 1)) mod 8 <=? Z.of_nat (length (tok_sl i))) &&
  (0 <=? tok_ptr i) && (tok_ptr i + Z.of_nat (length (tok_bytes i ++ NUL :: tok_sl i)) <? 2^64).

Lemma tok_img : forall i, (i < CAT_N)%nat ->
  ro_bytes_b rsegs (tok_ptr i) (tok_bytes i ++ NUL :: tok_sl i) = true /\
  (- (tok_ptr i + Z.of_nat (length (tok_bytes i)) + 1)) mod 8 <= Z.of_nat (length (tok_sl i)) /\
  0 <= tok_ptr i /\ tok_ptr i + Z.of_nat (length (tok_bytes i ++ NUL :: tok_sl i)) < 2^64.
Proof.
  intros i Hi. pose proof (all_rows_spec tok_ok ltac:(vm_compute; reflexivity) i Hi) as H. unfold tok_ok in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4. tauto.
Qed.

Lemma tok_at : forall m i, mem_inv rsegs m -> (i < CAT_N)%nat ->
  bytes_at rsegs m (tok_ptr i) (tok_bytes i ++ NUL :: tok_sl i).
Proof.
  intros m i MI Hi. destruct (tok_img i Hi) as (H1 & _ & H3 & H4).
  apply ro_bytes_at; [exact MI | exact H3 | lia | apply ro_bytes_b_sound; exact H1].
Qed.

Lemma tok_rng : forall i, (i < CAT_N)%nat ->
  0 <= tok_ptr i /\ tok_ptr i + Z.of_nat (length (tok_bytes i)) + 1 < 2^64.
Proof.
  intros i Hi. destruct (tok_img i Hi) as (_ & _ & H3 & H4). rewrite length_app in H4. cbn [length] in H4. lia.
Qed.

Lemma tok_nul : forall i, (i < CAT_N)%nat -> ~ In NUL (tok_bytes i).
Proof. intros i Hi Hin. apply (tokens_no_nul i NUL Hi Hin). reflexivity. Qed.

Definition CSET : Z := 66469.

Lemma cset_at : forall m, mem_inv rsegs m -> bytes_at rsegs m CSET ([Z_to_bv 8 58] ++ [Z_to_bv 8 0]).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold CSET; lia | cbn [length app Z.of_nat Pos.of_succ_nat Pos.succ]; unfold CSET; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma cset_img : image_bytes rsegs CSET 2 = Some (match image_bytes rsegs CSET 2 with Some l => l | None => [] end).
Proof. vm_compute. reflexivity. Qed.

Lemma got_img : image_bytes rsegs 0x1d478 8 = Some (match image_bytes rsegs 0x1d478 8 with Some l => l | None => [] end).
Proof. vm_compute. reflexivity. Qed.

Lemma guard_img : image_bytes rsegs 0x4ea60 8 = Some (match image_bytes rsegs 0x4ea60 8 with Some l => l | None => [] end).
Proof. vm_compute. reflexivity. Qed.

Lemma cset_notin : ~ In (Z_to_bv 8 0) [Z_to_bv 8 58].
Proof. intros [H|H]; [|exact H]. apply (f_equal (@bv_unsigned 8)) in H. vm_compute in H. discriminate. Qed.

Lemma no_hit : forall t, (forall j, (j < CAT_N)%nat -> tok_bytes j <> t) -> row_of t = None.
Proof.
  intros t H. destruct (row_of t) as [j|] eqn:E; [|reflexivity].
  destruct (row_of_some t j E) as (Hj & Ht & _). exfalso. exact (H j Hj Ht).
Qed.

(** * The walk *)
Section W.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 : word) (F : bvmap 5 word) (fc : bv 32)
  (mi : word -> option byte) (str slack : list byte) (lo : Z).
Hypothesis HLO : lo + 176 <= bv_unsigned sp.
Hypothesis HLO0 : 0 <= lo.
Hypothesis HCSPN : strcspn_contract.
Hypothesis HRBC : reac_box_catalogue_contract.
Hypothesis HSLEN : strlen_contract.
Hypothesis HNCMP : strncmp_contract.

Definition OUT : option (Z * Z) := parse_out FUZZ_CATALOGUE (bv_unsigned a0) (parse_live a0 a1 a2) str.

Definition Post (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (parse_rc OUT)) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    wmono rsegs mi m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    parse_mem mi m' (bv_unsigned sp) (bv_unsigned a1) (bv_unsigned a2) OUT.

(** The epilogue from 0x12f6c: a0 = s2, the nine reloads, sp back, ret. *)
Lemma epi : forall m j r (x1 y0 y1 y2 w8 w9 z0 z1 z2 z3 z4 z5 z6 z7 w19 w20 w21 w22 w23 u3 u4 u5 u6 : word),
  r = parse_rc OUT ->
  rw_cells rsegs m (bv_unsigned sp + -80) [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp + -80) -> mem_inv rsegs m -> wmono rsegs mi m ->
  parse_mem mi m (bv_unsigned sp) (bv_unsigned a1) (bv_unsigned a2) OUT ->
  evt rsegs Post (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y0 y1 y2 w8 w9 z0 z1 z2 z3 z4 z5 z6 z7
                       (Z_to_bv 64 r) w19 w20 w21 w22 w23 s8 s9 s10 s11 u3 u4 u5 u6)
                  F (Z_to_bv 64 77676) fc None m (seg_rom rsegs)).
Proof.
  intros m j r x1 y0 y1 y2 w8 w9 z0 z1 z2 z3 z4 z5 z6 z7 w19 w20 w21 w22 w23 u3 u4 u5 u6 Er FR ST MI WM PM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  do 11 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  subst r.
  finish.
Qed.

(** What the caller supplies when the three arguments are non-NULL, with the table premise. *)
Definition live_pre : Prop :=
  parse_live a0 a1 a2 = true /\
  parse_args mi lo (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) str slack /\
  (forall a, FUZZ_CATALOGUE <= a < FUZZ_CATALOGUE + CAT_BYTES -> mrd rsegs mi (wa a) = seg_rom rsegs (wa a)) /\
  (116528 + 3256 <= lo \/ bv_unsigned sp <= 116528).

(** The frame from the loop on: saved registers, the stack below, memory changed only in [sp - 176, sp). *)
Definition frm (m : word -> option byte) : Prop :=
  (exists j, rw_cells rsegs m (bv_unsigned sp + -80) [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) /\
  stk rsegs m lo (bv_unsigned sp + -80) /\ munch [(bv_unsigned sp - 176, bv_unsigned sp)] mi m /\
  wmono rsegs mi m /\ mem_inv rsegs m.

Lemma frm_nil : forall m m', frm m -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> frm m'.
Proof.
  intros m m' ((j & FR) & ST & MU & WM & _) MU' WM' MI'.
  split; [exists j; eapply rw_cells_transport; [exact FR | exact MU' | exact WM' | exact I]|].
  split; [eapply stk_transport_disjoint; [exact ST | exact MU' | exact WM' | exact I]|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU']]; intros x _; exact I|].
  split; [exact (wmono_trans rsegs _ _ _ WM WM') | exact MI'].
Qed.

Lemma out_some : live_pre -> forall i, pin_row str = Some i ->
  OUT = Some (row_addr FUZZ_CATALOGUE i, label_addr (bv_unsigned a0) str i).
Proof. intros (HL & _) i H. unfold OUT, parse_out. rewrite HL, H. reflexivity. Qed.

Lemma out_none : live_pre -> pin_row str = None -> OUT = None.
Proof. intros (HL & _) H. unfold OUT, parse_out. rewrite HL, H. reflexivity. Qed.

Lemma out_dead : parse_live a0 a1 a2 = false -> OUT = None.
Proof. intros H. unfold OUT, parse_out. rewrite H. reflexivity. Qed.

Lemma spec_in : live_pre -> forall m, munch [(bv_unsigned sp - 176, bv_unsigned sp)] mi m ->
  bytes_at rsegs m (bv_unsigned a0) (str ++ NUL :: slack).
Proof.
  intros (_ & HA & _) m MU. pose proof HA as (HS & _ & _ & HSD & _).
  pose proof (bytes_at_bound rsegs _ _ _ HS) as HSB. rewrite length_app in HSB. cbn [length] in HSB.
  eapply bytes_at_transport; [exact HS | exact MU |]. cbn [disjoint_from]. rewrite length_app. cbn [length].
  split; [lia | exact I].
Qed.

Lemma tbl_in : live_pre -> forall m, munch [(bv_unsigned sp - 176, bv_unsigned sp)] mi m ->
  bytes_at rsegs m 116528 PB_TBL.
Proof.
  intros (_ & _ & HTB & HTD) m MU.
  assert (T0 : bytes_at rsegs mi 116528 PB_TBL).
  { apply (pp_bytes_img rsegs mi 116528 3256 PB_TBL PB_TBL_eq); try change (Z.of_nat 3256) with 3256; [lia | lia |].
    intros a Ha. apply HTB. unfold FUZZ_CATALOGUE, CAT_BYTES. lia. }
  eapply bytes_at_transport; [exact T0 | exact MU |]. cbn [disjoint_from]. rewrite PB_TBL_len.
  change (Z.of_nat 3256) with 3256. split; [lia | exact I].
Qed.

(** A store of 8 bytes to an out cell (outside the frame). *)
Lemma out_st : forall m W (A0 : Z) cs lo' hi' (o : Z) (v : word),
  wr_at rsegs m o 8 -> mem_inv rsegs m -> munch W mi m -> wmono rsegs mi m -> inside W o 8 ->
  rw_cells rsegs m A0 cs -> (A0 + Z.of_nat (cells_size cs) <= o \/ o + 8 <= A0) -> stk rsegs m lo' hi' ->
  bytes_at rsegs (write_to_mem m (wa o) (le8 v)) o (le8 v) /\ mem_inv rsegs (write_to_mem m (wa o) (le8 v)) /\
  munch W mi (write_to_mem m (wa o) (le8 v)) /\ wmono rsegs mi (write_to_mem m (wa o) (le8 v)) /\
  rw_cells rsegs (write_to_mem m (wa o) (le8 v)) A0 cs /\ stk rsegs (write_to_mem m (wa o) (le8 v)) lo' hi'.
Proof.
  intros m W A0 cs lo' hi' o v HW MI MU WM HIN FR HD ST.
  pose proof HW as (Ho0 & Ho8 & _).
  split; [apply bytes_at_write_same; rewrite ?length_le8; lia|].
  split; [apply mem_inv_store; [exact MI | rewrite length_le8; apply (rcl_store_ok rsegs m o 8 8 HW); lia]|].
  split; [apply munch_write; [exact MU | lia | rewrite length_le8; lia | rewrite length_le8; exact HIN]|].
  split; [apply wmono_write; exact WM|].
  split; [apply rw_cells_frame; [exact FR | lia | rewrite length_le8; lia | rewrite length_le8; lia]|].
  apply stk_write; [exact ST | lia | rewrite length_le8; lia].
Qed.

(** From 0x12f60 on a hit at row i: s2 = 0, *model = row, *label = lab, then the epilogue. *)
Lemma tail : live_pre -> forall i m lab (x1 y0 y1 y2 w10 w11 z2 z3 z4 z5 z6 z7 w21 w22 w23 u3 u4 u5 u6 : word),
  (i < CAT_N)%nat -> pin_row str = Some i -> lab = label_addr (bv_unsigned a0) str i -> frm m ->
  evt rsegs Post (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y0 y1 y2 a2 a1 w10 w11 z2 z3 z4 z5 z6 z7
                       (Z_to_bv 64 (-1)) (Z_to_bv 64 lab) (Z_to_bv 64 (116528 + 296 * Z.of_nat i)) w21 w22 w23
                       s8 s9 s10 s11 u3 u4 u5 u6)
                  F (Z_to_bv 64 77664) fc None m (seg_rom rsegs)).
Proof.
  intros LP i m lab x1 y0 y1 y2 w10 w11 z2 z3 z4 z5 z6 z7 w21 w22 w23 u3 u4 u5 u6 Hi Hrow Hlab FRM.
  pose proof (out_some LP i Hrow) as EO.
  pose proof LP as (_ & HA & _).
  pose proof HA as (_ & _ & _ & _ & HWM & HWL & HML & HMD & HLD).
  destruct FRM as ((j & FR) & ST & MU & WM & MI).
  replace a1 with (Z_to_bv 64 (bv_unsigned a1)) by (apply wa_of_var; reflexivity).
  replace a2 with (Z_to_bv 64 (bv_unsigned a2)) by (apply wa_of_var; reflexivity).
  remember (bv_unsigned a1) as mo eqn:Emo. remember (bv_unsigned a2) as lb eqn:Elb.
  try rewrite <- Emo in HWM. try rewrite <- Emo in HML. try rewrite <- Emo in HMD.
  try rewrite <- Elb in HWL. try rewrite <- Elb in HML. try rewrite <- Elb in HLD.
  pose proof (wr_at_transport rsegs mi m _ _ HWM WM) as WMo.
  pose proof (wr_at_transport rsegs mi m _ _ HWL WM) as WLb.
  pose proof WMo as (Mo0 & Mo8 & _). pose proof WLb as (Lb0 & Lb8 & _).
  pose proof (rcl_store_ok rsegs m mo 8 8 WMo ltac:(lia)) as SO1.
  assert (MU3 : munch [(bv_unsigned sp - 176, bv_unsigned sp); (mo, mo + 8); (lb, lb + 8)] mi m).
  { eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *. tauto. }
  clear MU HA HWM HWL.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m ?a ?bs) _) =>
    replace a with (wa mo) by (unfold wa; first [reflexivity | f_equal; lia]) end.
  destruct (out_st m _ _ _ lo (bv_unsigned sp + -80) mo (Z_to_bv 64 (116528 + 296 * Z.of_nat i)) WMo MI MU3 WM
              ltac:(cbn [inside]; lia) FR ltac:(cbn [cells_size csize Nat.add]; lia) ST)
    as (B1 & MI1 & MU4 & WM4 & FR4 & ST4).
  pose proof (wr_at_write rsegs m lb 8 (wa mo) (le8 (Z_to_bv 64 (116528 + 296 * Z.of_nat i))) WLb) as WLb1.
  set (m1 := write_to_mem m (wa mo) (le8 (Z_to_bv 64 (116528 + 296 * Z.of_nat i)))) in *.
  clearbody m1. clear FR ST MI MU3 WM SO1 WMo WLb.
  pose proof (rcl_store_ok rsegs m1 lb 8 8 WLb1 ltac:(lia)) as SO2.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?a ?bs) _) =>
    replace a with (wa lb) by (unfold wa; first [reflexivity | f_equal; lia]) end.
  destruct (out_st m1 _ _ _ lo (bv_unsigned sp + -80) lb (Z_to_bv 64 lab) WLb1 MI1 MU4 WM4
              ltac:(cbn [inside]; lia) FR4 ltac:(cbn [cells_size csize Nat.add]; lia) ST4)
    as (B2 & MI2 & MU5 & WM5 & FR5 & ST5).
  pose proof (bytes_at_write_other rsegs m1 lb (le8 (Z_to_bv 64 lab)) mo _ B1 ltac:(lia)
                ltac:(rewrite length_le8; lia) ltac:(rewrite !length_le8; lia)) as B1'.
  set (m2 := write_to_mem m1 (wa lb) (le8 (Z_to_bv 64 lab))) in *.
  clearbody m2.
  eapply epi with (r := 0); [rewrite EO; reflexivity | exact FR5 | exact ST5 | exact MI2 | exact WM5 |].
  rewrite EO. cbn [parse_mem]. rewrite <- Emo, <- Elb, <- Hlab.
  split; [exact MU5|]. split; [exact B1' | exact B2].
Qed.

(** From 0x12f3c on a hit at row i: the label is spec + toklen + 1 when spec[toklen] = ':' and spec[toklen + 1] <> 0,
    else the row's display pointer. *)
Lemma found : live_pre -> forall i m (x1 y0 y1 y2 z0 z1 z2 z3 z4 z5 z6 z7 w22 w23 u3 u4 u5 u6 : word),
  (i < CAT_N)%nat -> tok_bytes i = pin_token str -> frm m ->
  evt rsegs Post (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y0 y1 y2 a2 a1 z0 z1 z2 z3 z4 z5 z6 z7
                       (Z_to_bv 64 (-1)) a0 (Z_to_bv 64 (116528 + 296 * Z.of_nat i))
                       (Z_to_bv 64 (Z.of_nat (colon_idx str))) w22 w23 s8 s9 s10 s11 u3 u4 u5 u6)
                  F (Z_to_bv 64 77628) fc None m (seg_rom rsegs)).
Proof.
  intros LP i m x1 y0 y1 y2 z0 z1 z2 z3 z4 z5 z6 z7 w22 w23 u3 u4 u5 u6 Hi Htok FRM.
  assert (Hrow : pin_row str = Some i) by (unfold pin_row; rewrite <- Htok; apply row_of_token; exact Hi).
  pose proof LP as (_ & HA & _).
  pose proof HA as (HS & HSN & _ & _ & _).
  pose proof FRM as (_ & _ & MU & _ & _).
  pose proof (spec_in LP m MU) as HSm.
  pose proof (bytes_at_bound rsegs _ _ _ HS) as HSB. rewrite length_app in HSB. cbn [length] in HSB.
  pose proof (colon_idx_le str) as Hn.
  pose proof (tbl_in LP m MU) as T.
  destruct (pp_row i Hi) as [_ R8].
  pose proof (bytes_at_ov_read rsegs m 116528 PB_TBL (296 * i + 8) 8 T
                ltac:(rewrite PB_TBL_len; unfold CAT_N in Hi; lia)) as RD8.
  rewrite R8 in RD8. replace (116528 + Z.of_nat (296 * i + 8)) with (116528 + 296 * Z.of_nat i + 8) in RD8 by lia.
  clear HS T R8.
  replace a0 with (Z_to_bv 64 (bv_unsigned a0)) by (apply wa_of_var; reflexivity).
  remember (bv_unsigned a0) as sa eqn:Esa. try rewrite <- Esa in HSm. try rewrite <- Esa in HSB.
  remember (colon_idx str) as n eqn:En. try rewrite <- En in Hn.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  destruct (Nat.lt_ge_cases n (length str)) as [Hlt|Hge].
  - (* spec[toklen] = ':' *)
    destruct (colon_idx_at str ltac:(lia)) as (b & Hb & Hbc). rewrite <- En in Hb. unfold COLON in Hbc.
    assert (Hb' : nth_error (str ++ NUL :: slack) n = Some b) by (rewrite nth_error_app1 by lia; exact Hb).
    pose proof (rcl_rd rsegs m sa _ n b HSm Hb') as RDc.
    pose proof (byte_range b) as Rb.
    zstep. zstep. clear RDc. zstep. zstep.
    pp_go.
    destruct (Nat.lt_ge_cases (S n) (length str)) as [Hlt2|Hge2].
    + (* a label follows *)
      destruct (nth_error str (S n)) as [b2|] eqn:Hb2; [|apply nth_error_None in Hb2; lia].
      assert (Hb2' : nth_error (str ++ NUL :: slack) (S n) = Some b2) by (rewrite nth_error_app1 by lia; exact Hb2).
      assert (N2 : bv_unsigned b2 <> 0).
      { intros E. apply HSN. replace NUL with b2 by (apply bv_eq; rewrite E; reflexivity).
        apply nth_error_In with (S n). exact Hb2. }
      pose proof (byte_range b2) as Rb2.
      pose proof (rcl_rd rsegs m sa _ (S n) b2 HSm Hb2') as RD2.
      replace (sa + Z.of_nat (S n)) with (sa + Z.of_nat n + 1) in RD2 by lia.
      zstep. clear RD2. zstep.
      pp_go.
      zstep. zstep.
      eapply tail; [exact LP | exact Hi | exact Hrow | | exact FRM].
      unfold label_addr, pin_label_off. rewrite <- En. rewrite (proj2 (Nat.ltb_lt _ _) Hlt2). cbv iota beta. lia.
    + (* the label is empty: spec[toklen + 1] = NUL *)
      assert (Hb2' : nth_error (str ++ NUL :: slack) (S n) = Some (Z_to_bv 8 0)).
      { rewrite nth_error_app2 by lia. replace (S n - length str)%nat with O by lia. reflexivity. }
      pose proof (rcl_rd rsegs m sa _ (S n) _ HSm Hb2') as RD2.
      replace (sa + Z.of_nat (S n)) with (sa + Z.of_nat n + 1) in RD2 by lia.
      zstep. clear RD2. zstep.
      pp_go.
      zstep.
      eapply tail; [exact LP | exact Hi | exact Hrow | | exact FRM].
      unfold label_addr, pin_label_off. rewrite <- En. rewrite (proj2 (Nat.ltb_ge _ _) Hge2). reflexivity.
  - (* no ':' : spec[toklen] = NUL *)
    assert (Hb' : nth_error (str ++ NUL :: slack) n = Some (Z_to_bv 8 0)).
    { rewrite nth_error_app2 by lia. replace (n - length str)%nat with O by lia. reflexivity. }
    pose proof (rcl_rd rsegs m sa _ n _ HSm Hb') as RDc.
    zstep. zstep. clear RDc. zstep. zstep.
    pp_go.
    zstep.
    eapply tail; [exact LP | exact Hi | exact Hrow | | exact FRM].
    unfold label_addr, pin_label_off. rewrite <- En. rewrite (proj2 (Nat.ltb_ge (S n) (length str))) by lia.
    reflexivity.
Qed.

(** The row loop at 0x12f08: row i, k rows left, no earlier row matched. *)
Lemma loop : live_pre -> forall k i m (x1 y0 y1 y2 w8 w9 z0 z1 z2 z3 z4 z5 z6 z7 w18 w19 w20 w21 w22 w23 u3 u4 u5 u6 : word),
  w8 = a2 -> w9 = a1 -> w18 = Z_to_bv 64 (-1) -> w19 = a0 -> w20 = Z_to_bv 64 (116528 + 296 * Z.of_nat i) ->
  w21 = Z_to_bv 64 (Z.of_nat (colon_idx str)) -> w23 = Z_to_bv 64 (Z.of_nat k) ->
  (i + k = CAT_N)%nat -> (0 < k)%nat -> (forall j, (j < i)%nat -> tok_bytes j <> pin_token str) -> frm m ->
  evt rsegs Post (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y0 y1 y2 w8 w9 z0 z1 z2 z3 z4 z5 z6 z7
                       w18 w19 w20 w21 w22 w23 s8 s9 s10 s11 u3 u4 u5 u6)
                  F (Z_to_bv 64 77576) fc None m (seg_rom rsegs)).
Proof.
  intros LP. induction k as [|k IH];
    intros i m x1 y0 y1 y2 w8 w9 z0 z1 z2 z3 z4 z5 z6 z7 w18 w19 w20 w21 w22 w23 u3 u4 u5 u6
      E8 E9 E18 E19 E20 E21 E23 Hik Hk Hnd FRM; [lia|].
  unfold CAT_N in Hik.
  subst w8 w9 w18 w19 w20 w21 w23.
  assert (Hi : (i < CAT_N)%nat) by (unfold CAT_N in *; lia).
  pose proof LP as (_ & HA & _).
  pose proof HA as (HS & HSN & _ & _ & _).
  pose proof (bytes_at_bound rsegs _ _ _ HS) as HSB. rewrite length_app in HSB. cbn [length] in HSB.
  pose proof (colon_idx_le str) as Hn.
  pose proof (tok_rng i Hi) as TR.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  clear HS.
  (* the next row, from 0x12f2c, when row i does not match *)
  assert (NEXT : forall (x1' y0' y1' y2' z0' z1' z2' z3' z4' z5' z6' z7' w22' u3' u4' u5' u6' : word) m',
    tok_bytes i <> pin_token str -> frm m' ->
    evt rsegs Post (MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y0' y1' y2' a2 a1 z0' z1' z2' z3' z4' z5' z6' z7'
                         (Z_to_bv 64 (-1)) a0 (Z_to_bv 64 (116528 + 296 * Z.of_nat i))
                         (Z_to_bv 64 (Z.of_nat (colon_idx str))) w22' (Z_to_bv 64 (Z.of_nat (S k)))
                         s8 s9 s10 s11 u3' u4' u5' u6')
                    F (Z_to_bv 64 77612) fc None m' (seg_rom rsegs))).
  { intros x1' y0' y1' y2' z0' z1' z2' z3' z4' z5' z6' z7' w22' u3' u4' u5' u6' m' NE FRM'.
    destruct k as [|k'].
    - zstep. zstep. zstep. try pp_go. zstep.
      destruct FRM' as ((j' & FR') & ST' & MU' & WM' & MI').
      assert (EO : OUT = None).
      { apply (out_none LP). unfold pin_row. apply no_hit. intros j Hj.
        destruct (Nat.eq_dec j i) as [->|Hji]; [exact NE | apply Hnd; unfold CAT_N in *; lia]. }
      eapply epi with (r := -1); [rewrite EO; reflexivity | exact FR' | exact ST' | exact MI' | exact WM' |].
      rewrite EO. exact MU'.
    - zstep. zstep. zstep. pp_go.
      eapply (IH (S i) m'); [reflexivity | reflexivity | reflexivity | reflexivity | f_equal; lia | reflexivity
                             | f_equal; lia | unfold CAT_N; lia | lia | | exact FRM'].
      intros j Hj. destruct (Nat.eq_dec j i) as [->|Hji]; [exact NE | apply Hnd; lia]. }
  pose proof FRM as (_ & _ & MU & _ & MI).
  pose proof (tbl_in LP m MU) as T.
  destruct (pp_row i Hi) as [R0 _].
  pose proof (bytes_at_ov_read rsegs m 116528 PB_TBL (296 * i) 8 T
                ltac:(rewrite PB_TBL_len; unfold CAT_N in Hi; lia)) as RD.
  rewrite R0 in RD. replace (116528 + Z.of_nat (296 * i)) with (116528 + 296 * Z.of_nat i) in RD by lia.
  clear T R0.
  zstep. clear RD. zstep. zstep.
  eapply evt_cut.
  { eapply HSLEN with (str := tok_bytes i) (slack := tok_sl i).
    - rewrite unsigned_lit by lia. rewrite ?Z.add_0_r. exact (tok_at m i MI Hi).
    - exact (tok_nul i Hi).
    - rewrite unsigned_lit by lia. rewrite ?Z.add_0_r. exact (proj1 (proj2 (tok_img i Hi))).
    - exact MI. }
  intros ms' PO. unfold strlen_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
                  E & MU2 & WM2 & MI2 & _).
  subst ms'. ret_lit.
  pose proof (frm_nil m m2 FRM MU2 WM2 MI2) as FRM2. clear FRM MU2 WM2 MU MI.
  zstep.
  destruct (Nat.eqb_spec (length (tok_bytes i)) (colon_idx str)) as [EQ|NE]; pp_go.
  - zstep. zstep. zstep. zstep.
    pose proof (tokens_nonempty i Hi) as TP.
    destruct (ncmp_tok str slack (tok_bytes i) (tok_sl i) (colon_idx str) HSN (tok_nul i Hi) Hn EQ ltac:(lia))
      as (v & HV & HViff & HVr).
    pose proof FRM2 as (_ & _ & MU & _ & MI).
    eapply evt_cut.
    { eapply HNCMP with (ls := str ++ NUL :: slack) (rs := tok_bytes i ++ NUL :: tok_sl i) (v := v).
      - exact (spec_in LP m2 MU).
      - rewrite unsigned_lit by lia. rewrite ?Z.add_0_r. exact (tok_at m2 i MI Hi).
      - rewrite unsigned_lit by lia. rewrite ?Z.add_0_r. exact HV.
      - exact MI. }
    intros ms' PO. unfold strncmp_post in PO.
    destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
                    m3 & E3 & MU3 & WM3 & MI3 & _ & _).
    subst ms'. ret_lit.
    pose proof (frm_nil m2 m3 FRM2 MU3 WM3 MI3) as FRM3. clear FRM2 MU3 WM3 MU MI.
    zstep.
    rewrite eqb_small by exact HVr.
    destruct (Z.eqb_spec v 0) as [V0|V0]; cbv iota.
    + eapply found; [exact LP | exact Hi | | exact FRM3].
      unfold pin_token. apply HViff. exact V0.
    + eapply NEXT; [| exact FRM3].
      intros C. apply V0. apply HViff. rewrite C. reflexivity.
  - eapply NEXT; [| exact FRM2].
    intros C. apply NE. rewrite C. unfold pin_token. rewrite length_firstn. lia.
Qed.

(** The whole body from 0x12e90. *)
Lemma walk : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 can : word),
  (parse_live a0 a1 a2 = true ->
     parse_args mi lo (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) str slack) ->
  stk rsegs mi lo (bv_unsigned sp) -> bv_unsigned sp mod 16 = 0 ->
  (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
  (forall a, FUZZ_CATALOGUE <= a < FUZZ_CATALOGUE + CAT_BYTES -> mrd rsegs mi (wa a) = seg_rom rsegs (wa a)) ->
  bytes_at rsegs mi 0x1d478 (le8 (Z_to_bv 64 0x4ea60)) -> bytes_at rsegs mi 0x4ea60 (le8 can) ->
  mem_inv rsegs mi ->
  evt rsegs Post (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x12e90) fc None mi (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 can HPRE ST SP16 NOROM TBL GOT GUARD MI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (pp_img_apart rsegs _ _ _ lo (bv_unsigned sp) got_img ltac:(lia) ltac:(lia) NOROM) as GOTD.
  pose proof (pp_img_apart rsegs _ _ _ lo (bv_unsigned sp) guard_img ltac:(lia) ltac:(lia) NOROM) as GUARDD.
  pose proof (pp_img_apart rsegs _ _ _ lo (bv_unsigned sp) cset_img ltac:(lia) ltac:(lia) NOROM) as CSD.
  pose proof (pp_img_apart rsegs _ _ _ lo (bv_unsigned sp) PB_TBL_eq ltac:(lia) ltac:(lia) NOROM) as TBD.
  unfold CSET in CSD. change (Z.of_nat 8) with 8 in GOTD, GUARDD. change (Z.of_nat 2) with 2 in CSD.
  change (Z.of_nat 3256) with 3256 in TBD.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] mi) as MU.
  pose proof (wmono_refl rsegs mi) as WM.
  carve_frame 80%nat ST.
  do 11 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jj :: _) => set (j0 := jj) in FR; clearbody j0 end.
  pose proof HLO0 as LO0.
  destruct (Z.eqb_spec (bv_unsigned a0) 0) as [A0|A0].
  { zstep. pp_go.
    assert (EO : OUT = None).
    { apply out_dead. apply andb_false_iff; left; apply andb_false_iff; left. rewrite A0. reflexivity. }
    eapply epi with (r := -1); [rewrite EO; reflexivity | exact FR | exact ST | exact MI | exact WM |].
    rewrite EO. exact MU. }
  zstep. pp_go. zstep. zstep.
  destruct (Z.eqb_spec (bv_unsigned a2) 0) as [A2|A2].
  { pp_go.
    assert (EO : OUT = None).
    { apply out_dead. apply andb_false_iff; right. rewrite A2. reflexivity. }
    eapply epi with (r := -1); [rewrite EO; reflexivity | exact FR | exact ST | exact MI | exact WM |].
    rewrite EO. exact MU. }
  pp_go. zstep. zstep.
  destruct (Z.eqb_spec (bv_unsigned a1) 0) as [A1|A1].
  { pp_go.
    assert (EO : OUT = None).
    { apply out_dead. apply andb_false_iff; left; apply andb_false_iff; right. rewrite A1. reflexivity. }
    eapply epi with (r := -1); [rewrite EO; reflexivity | exact FR | exact ST | exact MI | exact WM |].
    rewrite EO. exact MU. }
  pp_go. zstep.
  assert (LV : parse_live a0 a1 a2 = true).
  { unfold parse_live. rewrite (proj2 (Z.eqb_neq _ _) A0), (proj2 (Z.eqb_neq _ _) A1), (proj2 (Z.eqb_neq _ _) A2).
    reflexivity. }
  pose proof (HPRE LV) as HA.
  assert (LP : live_pre).
  { split; [exact LV|]. split; [exact HA|]. split; [exact TBL | lia]. }
  pose proof HA as (HS & HSN & HSL & HSD & _).
  pose proof (bytes_at_bound rsegs _ _ _ HS) as HSB. rewrite length_app in HSB. cbn [length] in HSB.
  pose proof (spec_in LP m1 MU) as HSm.
  clear HS HPRE TBL.
  destruct (nth_error str 0) as [x|] eqn:E0.
  2:{ (* the empty spec *)
    apply nth_error_None in E0. assert (E0' : str = []) by (apply length_zero_iff_nil; lia).
    assert (H0 : nth_error (str ++ NUL :: slack) 0 = Some (Z_to_bv 8 0)) by (rewrite E0'; reflexivity).
    pose proof (rcl_rd rsegs m1 (bv_unsigned a0) _ 0 _ HSm H0) as RD0.
    change (Z.of_nat 0) with 0 in RD0. rewrite Z.add_0_r, (wa_of_var a0 _ eq_refl) in RD0.
    zstep. clear RD0. zstep.
    pp_go.
    assert (EO : OUT = None) by (apply (out_none LP); rewrite E0'; exact pin_row_nil).
    eapply epi with (r := -1); [rewrite EO; reflexivity | exact FR | exact ST | exact MI | exact WM |].
    rewrite EO. exact MU. }
  assert (H0 : nth_error (str ++ NUL :: slack) 0 = Some x).
  { rewrite nth_error_app1; [exact E0|]. apply nth_error_Some. congruence. }
  assert (Nx : bv_unsigned x <> 0).
  { intros E. apply HSN. replace NUL with x by (apply bv_eq; rewrite E; reflexivity).
    apply nth_error_In with 0%nat. exact E0. }
  pose proof (byte_range x) as Rx.
  pose proof (rcl_rd rsegs m1 (bv_unsigned a0) _ 0 x HSm H0) as RD0.
  change (Z.of_nat 0) with 0 in RD0. rewrite Z.add_0_r, (wa_of_var a0 _ eq_refl) in RD0.
  zstep. clear RD0. zstep.
  pp_go.
  zstep. zstep. zstep. zstep.
  eapply evt_cut.
  { eapply HCSPN with (str := str) (slack := slack) (set := [Z_to_bv 8 58]) (lo := lo) (can := can).
    - exact HSm.
    - exact HSN.
    - intros _. exact HSL.
    - rewrite unsigned_lit by lia. exact (cset_at m1 MI).
    - exact cset_notin.
    - exact GOT.
    - exact GUARD.
    - rewrite SPU. exact ST.
    - rewrite SPU. lia.
    - rewrite SPU. lia.
    - rewrite SPU. rewrite unsigned_lit by lia. cbn [length Z.of_nat Pos.of_succ_nat]. lia.
    - rewrite SPU. unfold CSPN_SSP_GOT. lia.
    - rewrite SPU. unfold CSPN_SSP_GUARD. lia.
    - exact MI. }
  intros ms' PO. unfold strcspn_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
                  E & MU2 & WM2 & MI2 & ST2).
  subst ms'. rewrite cspn_colon. ret_lit.
  rewrite SPU in MU2, ST2.
  pose proof (rw_cells_transport rsegs _ _ _ _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia | exact I]))
    as FR2.
  assert (MU2' : munch [(bv_unsigned sp - 176, bv_unsigned sp)] mi m2).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2].
    intros y Hy; cbn [outside] in Hy |- *; destruct Hy as [Hy _]; split; [lia | exact I]. }
  pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM2'.
  clear FR MU MU2 WM WM2 ST MI GOT GUARD HSm.
  zstep. zstep. zstep.
  destruct (pp_rw_split rsegs m2 _ [CB 8 j0] _ FR2) as [FR0 FRr].
  cbn [cells_size csize Nat.add] in FRr. change (Z.of_nat 8) with 8 in FRr.
  pose proof (pp_wr_of_rw rsegs _ _ _ _ FR0) as W0. change (Z.of_nat 8) with 8 in W0.
  eapply evt_cut.
  { eapply HRBC with (c := bv_unsigned sp + -80).
    - reflexivity.
    - right. split; [Z.div_mod_to_equations; lia | exact W0]. }
  intros ms' (a1'' & m3 & E3 & PO3). subst ms'.
  rewrite (proj2 (Z.eqb_neq (bv_unsigned sp + -80) 0) ltac:(lia)) in PO3. destruct PO3 as (B11 & MU3 & WM3 & MI3).
  pose proof (MI3 MI2) as MI3'. clear MI3.
  ret_lit.
  pose proof (wr_at_transport rsegs _ _ _ _ W0 WM3) as W3.
  pose proof (pp_rw_c8 rsegs _ _ _ B11 W3) as FR3a.
  pose proof (rw_cells_transport rsegs _ _ _ _ _ FRr MU3 WM3
                ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia | exact I])) as FR3b.
  pose proof (pp_rw_join rsegs m3 _ _ [C8 (Z_to_bv 64 11)] _ FR3a FR3b ltac:(cbn [cells_size csize Nat.add]; lia))
    as FR3.
  cbn [app] in FR3.
  pose proof (stk_transport_disjoint rsegs _ _ _ _ _ ST2 MU3 WM3 ltac:(cbn [disjoint_from]; split; [lia | exact I]))
    as ST3.
  assert (MU3' : munch [(bv_unsigned sp - 176, bv_unsigned sp)] mi m3).
  { eapply munch_trans; [exact MU2'|]. eapply munch_weaken; [|exact MU3].
    intros y Hy; cbn [outside] in Hy |- *; destruct Hy as [Hy _]; split; [lia | exact I]. }
  pose proof (wmono_trans rsegs _ _ _ WM2' WM3) as WM3'.
  clear FR2 FR0 FRr W0 W3 B11 FR3a FR3b ST2 MU2' WM2' MU3 WM3 MI2.
  zstep. zstep. zstep.
  try pp_go.
  zstep.
  apply (rw_cells_merge rsegs m3 _ [] [C8 (Z_to_bv 64 11)] _) in FR3.
  assert (FRM : frm m3).
  { split; [eexists; exact FR3|]. split; [exact ST3|]. split; [exact MU3'|]. split; [exact WM3' | exact MI3']. }
  eapply (loop LP 11 0 m3); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
                            | reflexivity | reflexivity | lia | intros j Hj; lia | exact FRM].
Qed.

End W.

Theorem reac_box_pin_parse_holds : strcspn_contract -> reac_box_catalogue_contract -> strlen_contract ->
  strncmp_contract -> reac_box_pin_parse_contract.
Proof.
  intros CSPN RBC SLEN NCMP. unfold reac_box_pin_parse_contract, PARSE_STACK, PARSE_SSP_GOT, PARSE_SSP_GUARD.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo
    can HPRE ST LO SP16 NOROM TBL GOT GUARD MI.
  pose proof (proj1 ST) as LO0.
  exact (walk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 F fc m str slack lo LO LO0 CSPN RBC SLEN NCMP
           t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 can HPRE ST SP16 NOROM TBL GOT GUARD MI).
Qed.
