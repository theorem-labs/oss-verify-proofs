From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec.
Import ListNotations.
Open Scope Z_scope.

Definition PS : Z := 0x16af4.
Definition PS_FRAME : Z := 144.
Definition PS_PUT : Z := 0x16278.
Definition PS_SNPRINTF : Z := 0x1a260.
Definition PS_STRLEN : Z := 0x21f9c.
Definition PS_Q1 : Z := 0x10394.
Definition PS_FMT_C : Z := 0x1042d.
Definition PS_FMT_U : Z := 0x10424.

Definition ps_fmt (c : Z) : Z := if (c =? 34) || (c =? 92) then PS_FMT_C else PS_FMT_U.

Definition ps_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition ps_lits : list cell :=
  [C8 (Z_to_bv 64 0x725c); C8 (Z_to_bv 64 PS_FMT_U); C8 (Z_to_bv 64 0x6e5c); C8 (Z_to_bv 64 0x745c)].

Definition ps_loop (pc : Z) (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
  (o s r i : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word) : machine_state :=
  MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - PS_FRAME)) gp tp x5 x6 x7 (Z_to_bv 64 o) (Z_to_bv 64 (s + r))
          x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 PS_FMT_C) (Z_to_bv 64 (s + i)) x20 (Z_to_bv 64 (s + i + 1))
          (Z_to_bv 64 32) (Z_to_bv 64 92) (Z_to_bv 64 34) (Z_to_bv 64 12) (Z_to_bv 64 9) (Z_to_bv 64 13)
          x28 x29 x30 x31)
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

Definition ps_next (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
  (o s r : Z) (bs : list Z) (ms : machine_state) : Prop :=
  (exists (j : Z) (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
     r <= j < Z.of_nat (length bs) /\ special (nth (Z.to_nat j) bs 0) = true /\
     (forall k, r <= k < j -> special (nth (Z.to_nat k) bs 0) = false) /\
     ms = ps_loop PS_PUT sp gp tp F fc m o s r j (Z_to_bv 64 0x16bc4) x5 x6 x7 (Z_to_bv 64 o) (Z_to_bv 64 (s + r))
            (Z_to_bv 64 (j - r)) x13 x14 x15 x16 x17 (Z_to_bv 64 (nth (Z.to_nat j) bs 0)) x28 x29 x30 x31) \/
  (exists (x5 x6 x7 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
     (forall k, r <= k < Z.of_nat (length bs) -> special (nth (Z.to_nat k) bs 0) = false) /\
     ms = MS (mkR (Z_to_bv 64 0x16c70) (Z_to_bv 64 (bv_unsigned sp - PS_FRAME)) gp tp x5 x6 x7
                  (Z_to_bv 64 o) (Z_to_bv 64 (s + r)) (Z_to_bv 64 o) (Z_to_bv 64 (s + r))
                  (Z_to_bv 64 (Z.of_nat (length bs) - r)) x13 x14 x15 x16 x17
                  x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             F (Z_to_bv 64 PS_PUT) fc None m (seg_rom rsegs)).

Lemma ps_land255 : forall x, 0 <= x < 256 -> Z.land x 255 = x.
Proof.
  intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 8) with 256. lia.
Qed.

Lemma ps_u8 : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x.
Proof. intros x Hx. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma ps_rd : forall m s bs i, bytes_at rsegs m s (map (Z_to_bv 8) (bs ++ [0])) -> 0 <= i <= Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (s + i)) 1 = Some [Z_to_bv 8 (nth (Z.to_nat i) (bs ++ [0]) 0)].
Proof.
  intros m s bs i H Hi.
  rewrite (bytes_at_read rsegs m s _ i 1 H) by (try rewrite length_map, length_app; cbn [length]; lia).
  assert (L : (Z.to_nat i < length (map (Z_to_bv 8) (bs ++ [0%Z])))%nat)
    by (rewrite length_map, length_app; cbn [length]; lia).
  remember (map (Z_to_bv 8) (bs ++ [0])) as l eqn:El.
  revert L. generalize (Z.to_nat i) as k. clear H Hi. intros k L.
  assert (E : firstn 1 (skipn k l) = [nth k l (Z_to_bv 8 0)]).
  { clear El. revert k L. induction l as [|a l IH]; intros [|k] L; cbn in *; try lia; [reflexivity|]. apply IH. lia. }
  rewrite E, El, map_nth. reflexivity.
Qed.

Lemma ps_nth_in : forall bs i, 0 <= i < Z.of_nat (length bs) -> nth (Z.to_nat i) (bs ++ [0]) 0 = nth (Z.to_nat i) bs 0.
Proof. intros bs i Hi. apply app_nth1. lia. Qed.

Lemma ps_nth_end : forall bs i, i = Z.of_nat (length bs) -> nth (Z.to_nat i) (bs ++ [0]) 0 = 0.
Proof. intros bs i ->. rewrite Nat2Z.id, app_nth2, Nat.sub_diag by lia. reflexivity. Qed.

Lemma ps_byte : forall bs i, bytes_ok bs -> no_zero bs -> 0 <= i < Z.of_nat (length bs) ->
  0 < nth (Z.to_nat i) bs 0 < 256.
Proof.
  intros bs i Hb Hz Hi. unfold bytes_ok, no_zero in *. rewrite Forall_forall in *.
  assert (I : In (nth (Z.to_nat i) bs 0) bs) by (apply nth_In; lia).
  specialize (Hb _ I). specialize (Hz _ I). cbv beta in *. lia.
Qed.

Lemma ps_special_true : forall c, c = 34 \/ c = 92 \/ c < 32 -> special c = true.
Proof.
  intros c [-> | [-> | H]]; [reflexivity | reflexivity |].
  unfold special. rewrite (proj2 (Z.ltb_lt c 32) H), !orb_true_r. reflexivity.
Qed.

Lemma ps_special_false : forall c, c <> 34 -> c <> 92 -> 32 <= c -> special c = false.
Proof.
  intros c H1 H2 H3. unfold special.
  rewrite (proj2 (Z.eqb_neq c 34) H1), (proj2 (Z.eqb_neq c 92) H2), (proj2 (Z.ltb_ge c 32) H3). reflexivity.
Qed.

Lemma ps_special_inv : forall c, special c = true -> c = 34 \/ c = 92 \/ c < 32.
Proof.
  intros c H. unfold special in H. apply orb_true_iff in H as [H | H]; [apply orb_true_iff in H as [H | H] |].
  - left. apply Z.eqb_eq. exact H.
  - right. left. apply Z.eqb_eq. exact H.
  - right. right. apply Z.ltb_lt. exact H.
Qed.

Lemma ps_sgn : forall c, 0 <= c < 2^63 -> bv_signed (Z_to_bv 64 c) = c.
Proof.
  intros c Hc. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2^63). change (bv_modulus 64) with (2^64).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma ps_fmt_u : forall c, c <> 34 -> c <> 92 -> ps_fmt c = PS_FMT_U.
Proof. intros c H1 H2. unfold ps_fmt. rewrite (proj2 (Z.eqb_neq c 34) H1), (proj2 (Z.eqb_neq c 92) H2). reflexivity. Qed.

Lemma ps_evt_eq : forall (Q : machine_state -> Prop) ms' ms, evt rsegs Q ms' -> ms = ms' -> evt rsegs Q ms.
Proof. intros Q ms' ms H ->. exact H. Qed.

Lemma ps_slot : forall m A (pre post : list cell) (v : word) (b : byte) (r bs : list byte),
  rw_cells rsegs m A (pre ++ [C2 v; C1 b; CB 5 r] ++ post) -> le2 v ++ b :: r = bs ->
  rw_cells rsegs m A (pre ++ CB 8 bs :: post).
Proof.
  intros m A pre post v b r bs H E.
  pose proof (rw_cells_merge rsegs m A pre [C2 v; C1 b; CB 5 r] post H) as H2.
  cbn [cells_size csize cells_bytes cbytes Nat.add app] in H2. rewrite app_nil_r, E in H2. exact H2.
Qed.

Lemma ps_le2 : forall z, 0 <= z < 65536 -> le2 (Z_to_bv 64 z) = [Z_to_bv 8 (z mod 256); Z_to_bv 8 (z / 256)].
Proof.
  intros z Hz. unfold le2. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  f_equal; [apply Z_to_bv8_mod | f_equal; apply Z_to_bv8_mod].
  - change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
  - rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma ps_slot9 : le2 (Z_to_bv 64 0x745c) ++ [Z_to_bv 8 0] = map (Z_to_bv 8) (esc 9 ++ [0]).
Proof. rewrite ps_le2 by lia. reflexivity. Qed.

Lemma ps_slot10 : le2 (Z_to_bv 64 0x6e5c) ++ [Z_to_bv 8 0] = map (Z_to_bv 8) (esc 10 ++ [0]).
Proof. rewrite ps_le2 by lia. reflexivity. Qed.

Lemma ps_slot13 : le2 (Z_to_bv 64 0x725c) ++ [Z_to_bv 8 0] = map (Z_to_bv 8) (esc 13 ++ [0]).
Proof. rewrite ps_le2 by lia. reflexivity. Qed.

Lemma ps_frame_forget : forall m A (e : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
  rw_cells rsegs m A (ps_lits ++ CB 8 e :: ps_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  exists junk, rw_cells rsegs m A (CB 40 junk :: ps_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Proof.
  intros m A e ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 H.
  exists (cells_bytes (ps_lits ++ [CB 8 e])).
  exact (rw_cells_merge rsegs m A [] (ps_lits ++ [CB 8 e]) (ps_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) H).
Qed.

Ltac ps_tree_eq :=
  lazymatch goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal; ps_tree_eq
  | |- Some _ = Some _ => f_equal; ps_tree_eq
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [ reflexivity | f_equal; lia | f_equal; cbn [length Z.of_nat]; lia ]
  | |- _ => reflexivity
  end.

Ltac ps_eq :=
  unfold ps_loop, PS_FRAME, PS_FMT_C, PS_FMT_U, PS_PUT, PS_SNPRINTF, PS_STRLEN, PS_Q1; cbv [mkR];
  lazymatch goal with |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal; ps_tree_eq end.

Theorem ps_entry :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo o s : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + PS_FRAME <= bv_unsigned sp -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (junk : list byte) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x16b48) (Z_to_bv 64 (bv_unsigned sp - PS_FRAME)) gp tp t0 t1 t2
                       (Z_to_bv 64 o) (Z_to_bv 64 s) (Z_to_bv 64 o) (Z_to_bv 64 PS_Q1) (Z_to_bv 64 1)
                       a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 PS_PUT) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - PS_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp - PS_FRAME) /\
         rw_cells rsegs m' (bv_unsigned sp - PS_FRAME) (CB 40 junk :: ps_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 s) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 PS) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo o s
    ST LO MI.
  unfold PS, PS_FRAME, PS_PUT, PS_Q1, ps_saved in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  carve_frame 144%nat ST.
  do 21 zstep.
  finish.
  exact FR.
Qed.

Section Scan.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o s : Z) (bs : list Z).
  Hypothesis SB : bytes_at rsegs m s (map (Z_to_bv 8) (bs ++ [0])).
  Hypothesis HB : bytes_ok bs.
  Hypothesis HZ : no_zero bs.

  Lemma ps_spec_exit : forall (i r : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    0 <= r <= i -> i < Z.of_nat (length bs) -> special (nth (Z.to_nat i) bs 0) = true ->
    (forall k, r <= k < i -> special (nth (Z.to_nat k) bs 0) = false) ->
    evt rsegs (ps_next sp gp tp F fc m o s r bs)
      (ps_loop 0x16bb4 sp gp tp F fc m o s r i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
         (Z_to_bv 64 (nth (Z.to_nat i) bs 0)) x28 x29 x30 x31).
  Proof using SB.
    intros i r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hr Hi SPc NS.
    pose proof (bytes_at_bound _ _ _ _ SB) as BS. rewrite length_map, length_app in BS. cbn [length] in BS.
    unfold ps_loop, PS_FRAME, PS_FMT_C.
    do 4 zstep.
    apply evt_done. unfold ps_next. left. exists i. do 12 eexists.
    split; [lia|]. split; [exact SPc|]. split; [exact NS|]. ps_eq.
  Qed.

  Lemma ps_adv : forall (i r : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word),
    0 <= i -> 0 <= r <= i + 1 -> i + 1 <= Z.of_nat (length bs) ->
    (forall k, r <= k < i + 1 -> special (nth (Z.to_nat k) bs 0) = false) ->
    (forall y11 : word, i + 1 < Z.of_nat (length bs) ->
       evt rsegs (ps_next sp gp tp F fc m o s r bs)
         (ps_loop 0x16ba4 sp gp tp F fc m o s r (i + 1) x1 x5 x6 x7 (Z_to_bv 64 (nth (Z.to_nat (i + 1)) bs 0))
            y11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31)) ->
    evt rsegs (ps_next sp gp tp F fc m o s r bs)
      (ps_loop 0x16c40 sp gp tp F fc m o s r i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31).
  Proof using SB HB HZ.
    intros i r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 Hi0 Hr Hi NS K.
    pose proof (bytes_at_bound _ _ _ _ SB) as BS. rewrite length_map, length_app in BS. cbn [length] in BS.
    unfold ps_loop, PS_FRAME, PS_FMT_C.
    destruct (Z.lt_ge_cases (i + 1) (Z.of_nat (length bs))) as [LT | GE].
    - pose proof (ps_byte bs (i + 1) HB HZ ltac:(lia)) as RC.
      pose proof (ps_rd m s bs (i + 1) SB ltac:(lia)) as RD. rewrite ps_nth_in in RD by lia.
      remember (nth (Z.to_nat (i + 1)) bs 0) as c eqn:Ec.
      zstep. cbv beta. rewrite (ps_u8 c) by lia.
      do 3 zstep. rewrite (ps_land255 c) by lia.
      zstep. if_cases BZ; zify_cond BZ; [| lia].
      eapply ps_evt_eq; [eapply K; exact LT |].
      subst c. ps_eq.
    - pose proof (ps_rd m s bs (i + 1) SB ltac:(lia)) as RD. rewrite ps_nth_end in RD by lia.
      zstep. cbv beta.
      do 4 zstep. if_false.
      do 6 zstep.
      apply evt_done. unfold ps_next. right. do 22 eexists. split.
      + intros k Hk. apply NS. lia.
      + ps_eq.
  Qed.

  Lemma ps_scan : forall (n : nat) (i r : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word),
    Z.to_nat (Z.of_nat (length bs) - i) = n -> 0 <= r <= i -> i < Z.of_nat (length bs) ->
    (forall k, r <= k < i -> special (nth (Z.to_nat k) bs 0) = false) ->
    evt rsegs (ps_next sp gp tp F fc m o s r bs)
      (ps_loop 0x16ba4 sp gp tp F fc m o s r i x1 x5 x6 x7 (Z_to_bv 64 (nth (Z.to_nat i) bs 0))
         x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31).
  Proof using SB HB HZ.
    induction n as [n IH] using lt_wf_ind.
    intros i r x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 En Hr Hi NS.
    pose proof (bytes_at_bound _ _ _ _ SB) as BS. rewrite length_map, length_app in BS. cbn [length] in BS.
    pose proof (ps_byte bs i HB HZ ltac:(lia)) as RC.
    unfold ps_loop at 1. unfold PS_FRAME, PS_FMT_C.
    remember (nth (Z.to_nat i) bs 0) as c eqn:Ec.
    zstep. rewrite (ps_land255 c) by lia.
    zstep. if_cases B1; zify_cond B1.
    - subst c. apply ps_spec_exit; [lia | lia | apply ps_special_true; lia | exact NS].
    - zstep. if_cases B2; zify_cond B2.
      + subst c. apply ps_spec_exit; [lia | lia | apply ps_special_true; lia | exact NS].
      + zstep. if_cases B3; zify_cond B3.
        * assert (NS' : forall k, r <= k < i + 1 -> special (nth (Z.to_nat k) bs 0) = false).
          { intros k Hk. destruct (Z.eq_dec k i) as [-> | Hne].
            - rewrite <- Ec. apply ps_special_false; lia.
            - apply NS. lia. }
          apply (ps_adv i r); [lia | lia | lia | exact NS' |].
          intros y11 LT.
          apply (IH (Z.to_nat (Z.of_nat (length bs) - (i + 1)))); [lia | reflexivity | lia | lia | exact NS'].
        * subst c. apply ps_spec_exit; [lia | lia | apply ps_special_true; lia | exact NS].
  Qed.

  Lemma ps_after_esc_s : forall (j r : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word),
    0 <= j < Z.of_nat (length bs) ->
    evt rsegs (ps_next sp gp tp F fc m o s (j + 1) bs)
      (ps_loop 0x16c3c sp gp tp F fc m o s r j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31).
  Proof using SB HB HZ.
    intros j r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 Hj.
    pose proof (bytes_at_bound _ _ _ _ SB) as BS. rewrite length_map, length_app in BS. cbn [length] in BS.
    unfold ps_loop at 1. unfold PS_FRAME, PS_FMT_C.
    zstep.
    eapply ps_evt_eq.
    - apply (ps_adv j (j + 1) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31);
        [lia | lia | lia | intros; lia |].
      intros y11 LT.
      apply (ps_scan (Z.to_nat (Z.of_nat (length bs) - (j + 1)))); [reflexivity | lia | lia | intros; lia].
    - ps_eq.
  Qed.
End Scan.

Theorem ps_after_open_empty :
  forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o s : Z)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    bytes_at rsegs m s [Z_to_bv 8 0] ->
    evt rsegs (ps_next sp gp tp F fc m o s 0 [])
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - PS_FRAME)) gp tp x5 x6 x7 (Z_to_bv 64 o) (Z_to_bv 64 s)
               x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x16b48) fc None m (seg_rom rsegs)).
Proof.
  intros sp gp tp F fc m o s x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 SB.
  pose proof (bytes_at_bound _ _ _ _ SB) as BS. cbn [length] in BS.
  assert (RD : ov_read_bytes rsegs m (wa (s + 0)) 1 = Some [Z_to_bv 8 0])
    by (rewrite (bytes_at_read rsegs m s _ 0 1 SB) by (cbn [length]; lia); reflexivity).
  rewrite Z.add_0_r in RD.
  unfold PS_FRAME.
  zstep. cbv beta. zstep. zstep. if_true.
  do 5 zstep.
  apply evt_done. unfold ps_next. right. do 22 eexists. split.
  - cbn [length Z.of_nat]. intros k Hk. lia.
  - ps_eq.
Qed.

Theorem ps_after_open :
  forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo o s : Z) (bs : list Z)
         (junk : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    bytes_at rsegs m s (map (Z_to_bv 8) (bs ++ [0])) -> bytes_ok bs -> no_zero bs -> bs <> [] ->
    rw_cells rsegs m (bv_unsigned sp - PS_FRAME) (CB 40 junk :: ps_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    stk rsegs m lo (bv_unsigned sp - PS_FRAME) -> mem_inv rsegs m ->
    (s + Z.of_nat (length bs) + 1 <= bv_unsigned sp - PS_FRAME \/ bv_unsigned sp - PS_FRAME + 32 <= s) ->
    evt rsegs
      (fun ms' => exists (e : list byte) (m' : word -> option byte),
         munch [(bv_unsigned sp - PS_FRAME, bv_unsigned sp - PS_FRAME + 32)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp - PS_FRAME) /\
         rw_cells rsegs m' (bv_unsigned sp - PS_FRAME) (ps_lits ++ CB 8 e :: ps_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
         bytes_at rsegs m' s (map (Z_to_bv 8) (bs ++ [0])) /\
         ps_next sp gp tp F fc m' o s 0 bs ms')
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - PS_FRAME)) gp tp x5 x6 x7 (Z_to_bv 64 o) (Z_to_bv 64 s)
               x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x16b48) fc None m (seg_rom rsegs)).
Proof.
  intros sp gp tp F fc m lo o s bs junk ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    SB HB HZ NE FR ST MI DS.
  unfold PS_FRAME in *. unfold ps_saved in FR.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (bytes_at_bound _ _ _ _ SB) as BS. rewrite length_map, length_app in BS. cbn [length] in BS.
  assert (NL : 0 < Z.of_nat (length bs)) by (destruct bs; [congruence | cbn [length]; lia]).
  assert (LSB : Z.of_nat (length (map (Z_to_bv 8) (bs ++ [0]))) = Z.of_nat (length bs) + 1)
    by (rewrite length_map, length_app; cbn [length]; lia).
  pose proof (ps_byte bs 0 HB HZ ltac:(lia)) as RC.
  pose proof (ps_rd m s bs 0 SB ltac:(lia)) as RD. rewrite ps_nth_in in RD by lia. rewrite Z.add_0_r in RD.
  remember (nth (Z.to_nat 0) bs 0) as c eqn:Ec.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp - 144 + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  zstep. cbv beta. rewrite (ps_u8 c) by lia.
  zstep. rewrite (ps_land255 c) by lia.
  zstep. if_cases BZ; zify_cond BZ; [lia |].
  do 20 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply ps_evt_eq;
      [ eapply (ps_scan sp gp tp F fc mm o s bs SB HB HZ _ 0 0); [reflexivity | lia | lia | intros; lia]
      | subst c; ps_eq ]
    | ];
    intros ms' HN; apply evt_done; exists (skipn 32 junk), mm
  end.
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [unfold ps_lits, ps_saved, PS_FMT_U; cbn [app]; exact FR|].
  split; [exact SB | exact HN].
Qed.

Theorem ps_after_run_store :
  forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo o s r j c : Z)
         (e : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    c = 9 \/ c = 10 \/ c = 13 -> PS_FRAME <= bv_unsigned sp ->
    rw_cells rsegs m (bv_unsigned sp - PS_FRAME) (ps_lits ++ CB 8 e :: ps_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    stk rsegs m lo (bv_unsigned sp - PS_FRAME) -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (m' : word -> option byte),
         ms' = ps_loop PS_STRLEN sp gp tp F fc m' o s r j (Z_to_bv 64 0x16c2c) x5 x6 x7
                 (Z_to_bv 64 (bv_unsigned sp - PS_FRAME + 32)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 c)
                 x28 x29 x30 x31 /\
         munch [(bv_unsigned sp - PS_FRAME + 32, bv_unsigned sp - PS_FRAME + 40)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp - PS_FRAME) /\
         rw_cells rsegs m' (bv_unsigned sp - PS_FRAME)
           (ps_lits ++ CB 8 (map (Z_to_bv 8) (esc c ++ [0]) ++ skipn 3 e)
              :: ps_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
      (ps_loop 0x16bc4 sp gp tp F fc m o s r j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 c)
         x28 x29 x30 x31).
Proof.
  intros sp gp tp F fc m lo o s r j c e ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HC SP FR ST MI.
  unfold PS_FRAME, PS_STRLEN in *. unfold ps_loop at 2. unfold PS_FRAME, PS_FMT_C.
  unfold ps_lits, ps_saved, PS_FMT_U in FR. cbn [app] in FR.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 144 + 32, bv_unsigned sp - 144 + 40)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct HC as [-> | [-> | ->]].
  - zstep. if_true. zstep. if_true.
    zstep. zstep. zstep.
    replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by reflexivity. mem_after_store.
    do 3 zstep.
    apply evt_done. eexists. split; [ps_eq|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    eapply ps_slot; [unfold ps_lits, ps_saved, PS_FMT_U; cbn [app]; exact FR |].
    rewrite skipn_skipn. rewrite <- ps_slot9. reflexivity.
  - zstep. if_true. zstep. if_false. zstep. zstep. if_false.
    zstep. zstep. zstep. zstep.
    replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by reflexivity. mem_after_store.
    do 3 zstep.
    apply evt_done. eexists. split; [ps_eq|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    eapply ps_slot; [unfold ps_lits, ps_saved, PS_FMT_U; cbn [app]; exact FR |].
    rewrite skipn_skipn. rewrite <- ps_slot10. reflexivity.
  - zstep. if_false. zstep. if_true.
    zstep. zstep. zstep. zstep.
    replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by reflexivity. mem_after_store.
    do 3 zstep.
    apply evt_done. eexists. split; [ps_eq|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    eapply ps_slot; [unfold ps_lits, ps_saved, PS_FMT_U; cbn [app]; exact FR |].
    rewrite skipn_skipn. rewrite <- ps_slot13. reflexivity.
Qed.

Theorem ps_after_run_fmt :
  forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o s r j c : Z)
         (e : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    special c = true -> 0 < c -> c <> 9 -> c <> 10 -> c <> 13 -> PS_FRAME <= bv_unsigned sp ->
    rw_cells rsegs m (bv_unsigned sp - PS_FRAME) (ps_lits ++ CB 8 e :: ps_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    evt rsegs
      (fun ms' => ms' = ps_loop PS_SNPRINTF sp gp tp F fc m o s r j (Z_to_bv 64 0x16c24) x5 x6 x7
                          (Z_to_bv 64 (bv_unsigned sp - PS_FRAME + 32)) (Z_to_bv 64 8) (Z_to_bv 64 (ps_fmt c))
                          (Z_to_bv 64 c) x14 x15 x16 x17 (Z_to_bv 64 c) x28 x29 x30 x31)
      (ps_loop 0x16bc4 sp gp tp F fc m o s r j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 c)
         x28 x29 x30 x31).
Proof.
  intros sp gp tp F fc m o s r j c e ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 SPc C0 C9 C10 C13 SP FR.
  pose proof (ps_special_inv c SPc) as HC.
  unfold ps_loop at 2. unfold PS_FRAME, PS_FMT_C.
  unfold ps_lits, ps_saved, PS_FRAME, PS_FMT_U in FR. cbn [app] in FR.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  zstep. if_cases B1; unfold bv_lts in B1; rewrite (ps_sgn c) in B1 by lia; zify_cond B1.
  - zstep. if_cases B2; zify_cond B2; [lia |].
    zstep. zstep. if_cases B3; zify_cond B3; [| lia].
    do 5 zstep.
    apply evt_done. cbv beta. rewrite ps_fmt_u by lia. ps_eq.
  - zstep. if_cases B2; zify_cond B2; [lia |].
    zstep. if_cases B3; zify_cond B3.
    + subst c. do 6 zstep. apply evt_done. cbv beta. ps_eq.
    + zstep. if_cases B4; zify_cond B4.
      * do 5 zstep. apply evt_done. cbv beta. rewrite ps_fmt_u by lia. ps_eq.
      * subst c. do 6 zstep. apply evt_done. cbv beta. ps_eq.
Qed.

Theorem ps_after_snprintf :
  forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o s r j : Z)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word),
    PS_FRAME <= bv_unsigned sp ->
    evt rsegs
      (fun ms' => ms' = ps_loop PS_STRLEN sp gp tp F fc m o s r j (Z_to_bv 64 0x16c2c) x5 x6 x7
                          (Z_to_bv 64 (bv_unsigned sp - PS_FRAME + 32)) x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31)
      (ps_loop 0x16c24 sp gp tp F fc m o s r j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31).
Proof.
  intros sp gp tp F fc m o s r j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 SP.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  unfold ps_loop at 2. unfold PS_FRAME, PS_FMT_C. unfold PS_FRAME in SP.
  do 2 zstep.
  apply evt_done. cbv beta. ps_eq.
Qed.

Theorem ps_after_strlen :
  forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o s r j : Z)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word),
    PS_FRAME <= bv_unsigned sp ->
    evt rsegs
      (fun ms' => ms' = ps_loop PS_PUT sp gp tp F fc m o s r j (Z_to_bv 64 0x16c3c) x5 x6 x7
                          (Z_to_bv 64 o) (Z_to_bv 64 (bv_unsigned sp - PS_FRAME + 32)) x10 x13 x14 x15 x16 x17 x20
                          x28 x29 x30 x31)
      (ps_loop 0x16c2c sp gp tp F fc m o s r j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31).
Proof.
  intros sp gp tp F fc m o s r j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 SP.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  unfold ps_loop at 2. unfold PS_FRAME, PS_FMT_C. unfold PS_FRAME in SP.
  do 4 zstep.
  apply evt_done. cbv beta. ps_eq.
Qed.

Theorem ps_after_esc :
  forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o s r j : Z) (bs : list Z)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word),
    bytes_at rsegs m s (map (Z_to_bv 8) (bs ++ [0])) -> bytes_ok bs -> no_zero bs ->
    0 <= j < Z.of_nat (length bs) ->
    evt rsegs (ps_next sp gp tp F fc m o s (j + 1) bs)
      (ps_loop 0x16c3c sp gp tp F fc m o s r j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31).
Proof.
  intros sp gp tp F fc m o s r j bs x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 SB HB HZ Hj.
  exact (ps_after_esc_s sp gp tp F fc m o s bs SB HB HZ j r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20
           x28 x29 x30 x31 Hj).
Qed.

Theorem ps_scan_loop :
  forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o s r i : Z) (bs : list Z)
         (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word),
    bytes_at rsegs m s (map (Z_to_bv 8) (bs ++ [0])) -> bytes_ok bs -> no_zero bs ->
    0 <= r <= i -> i < Z.of_nat (length bs) ->
    (forall k, r <= k < i -> special (nth (Z.to_nat k) bs 0) = false) ->
    evt rsegs (ps_next sp gp tp F fc m o s r bs)
      (ps_loop 0x16ba4 sp gp tp F fc m o s r i x1 x5 x6 x7 (Z_to_bv 64 (nth (Z.to_nat i) bs 0))
         x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31).
Proof.
  intros sp gp tp F fc m o s r i bs x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 SB HB HZ Hr Hi NS.
  exact (ps_scan sp gp tp F fc m o s bs SB HB HZ _ i r x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31
           eq_refl Hr Hi NS).
Qed.

Theorem ps_after_final :
  forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo o : Z) (junk : list byte)
         (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
         (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    rw_cells rsegs m (bv_unsigned sp - PS_FRAME) (CB 40 junk :: ps_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    stk rsegs m lo (bv_unsigned sp - PS_FRAME) -> lo + PS_FRAME <= bv_unsigned sp ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 PS_Q1) (Z_to_bv 64 1)
                                x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                           F (Z_to_bv 64 PS_PUT) fc None m (seg_rom rsegs) /\
                  stk rsegs m lo (bv_unsigned sp))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - PS_FRAME)) gp tp x5 x6 x7 (Z_to_bv 64 o) x9
               x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x16c70) fc None m (seg_rom rsegs)).
Proof.
  intros sp gp tp F fc m lo o junk ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 FR ST LO.
  unfold PS_FRAME, PS_PUT, PS_Q1, ps_saved in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (Hlo & _ & _).
  do 18 zstep.
  replace (bv_unsigned sp - 144 + 144) with (bv_unsigned sp) by lia.
  rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  apply evt_done. split; [reflexivity | exact ST].
Qed.
