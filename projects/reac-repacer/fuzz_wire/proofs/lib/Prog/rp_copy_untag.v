From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Tac Arr Bytes Step ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require Import FrameBytes memmove_c reac_frame_is_reac_c rp_copy_untag_c.
Import ListNotations.
Open Scope Z_scope.

(* rp_copy_untag at 0x13690 (39 words): a 32-byte frame (ra, s0, s1 at sp-8, sp-16, sp-24), is_tagged_reac inlined
   (0x136b0-0x136d8), `jal memmove` at 0x136e8, `jal reac_frame_is_reac` at 0x136f8, is_audio inlined (0x13700-0x1370c).
   Both callees are NAMED Section hypotheses, their own contracts:
   - memmove (0x1b6f8): lib/Prog/memmove_c.v (libreac/fuzz_pcap's released contract ported by path; its walk
     memmove_holds in lib/Prog/memmove.v);
   - reac_frame_is_reac (0x13860): lib/Prog/reac_frame_is_reac_c.v (the port of decode's released contract). *)


Lemma is_reac_result_eq : forall f n us, f <> 0 -> 14 <= n ->
  is_reac_result f n us = if (is_reac_byte us 12 =? 0x88) && (is_reac_byte us 13 =? 0x19) then 1 else 0.
Proof.
  intros f n us Hf Hn. unfold is_reac_result.
  rewrite (proj2 (Z.eqb_neq _ _) Hf), (proj2 (Z.ltb_ge _ _) Hn). reflexivity.
Qed.

(* stk survives a call that writes only [wl, wh), all of it inside a range the memory now holds bytes for *)
Lemma stk_moved : forall m1 m2 lo hi A us wl wh,
  stk rsegs m1 lo hi -> munch [(wl, wh)] m1 m2 -> wmono rsegs m1 m2 -> bytes_at rsegs m2 A us ->
  (forall x, lo <= x < hi -> (x < wl \/ wh <= x) \/ (A <= x < A + Z.of_nat (length us))) ->
  stk rsegs m2 lo hi.
Proof.
  intros m1 m2 lo hi A us wl wh (S1 & S2 & S3) MU WM (BA0 & BA1 & BA2) C. split; [lia|]. split; [lia|].
  intros x Hx. destruct (S3 x Hx) as [Hw [b Hb]]. split; [apply WM; exact Hw|].
  destruct (C x Hx) as [Ho | Hin].
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia|exact I].
  - pose proof (BA2 (Z.to_nat (x - A)) ltac:(lia)) as E. replace (A + Z.of_nat (Z.to_nat (x - A))) with x in E by lia.
    rewrite E. destruct (nth_error us (Z.to_nat (x - A))) eqn:N; [eexists; reflexivity|].
    apply nth_error_None in N. lia.
Qed.

Local Ltac zc H := zify_cond H; rewrite ?zxb_u in H.

Local Ltac dec :=
  repeat match goal with
  | |- context [Z.eqb ?x ?c] => destruct (Z.eqb_spec x c); try (exfalso; lia)
  | |- context [Z.leb ?x ?c] => destruct (Z.leb_spec x c); try (exfalso; lia)
  | |- context [Z.ltb ?x ?c] => destruct (Z.ltb_spec x c); try (exfalso; lia)
  end.

Local Ltac rw_bytes :=
  repeat match goal with Eb : ?b = nth ?i ?l ?d |- context [nth ?i ?l ?d] => rewrite <- Eb end.

Section W.
Hypothesis memmove_ok : memmove_contract.
Hypothesis reac_frame_is_reac_ok : reac_frame_is_reac_contract.

Section CU.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (bs : list byte) (lo : Z).

Local Notation SP := (bv_unsigned sp).
Local Notation N := (bv_unsigned a1).
Local Notation FA := (bv_unsigned a0).

Definition PostCU : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (copy_untag_result N bs))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo SP /\
    munch ((SP - 32, SP) :: cu_footprint FA N bs) m m' /\
    (50 <= N -> u8arr rsegs m' FA (cu_bytes N bs)).

(* 0x13714: a0 = s0; restore ra, s0, s1; return *)
Lemma cu_exit : forall (mk : word -> option byte) (j : list byte)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  rw_cells rsegs mk (SP + -32) [CB 8 j; C8 s1; C8 s0; C8 ra] ->
  stk rsegs mk lo (SP + -32) -> lo + 32 <= SP ->
  wmono rsegs m mk -> mem_inv rsegs mk ->
  munch ((SP - 32, SP) :: cu_footprint FA N bs) m mk ->
  (50 <= N -> u8arr rsegs mk FA (cu_bytes N bs)) ->
  x8 = Z_to_bv 64 (copy_untag_result N bs) ->
  evt rsegs PostCU
    (MS (mkR x1 (Z_to_bv 64 (SP + -32)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x13714) fc None mk (seg_rom rsegs)).
Proof.
  intros mk j x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FR ST LO WM MI MU UA E8.
  subst x8. pose proof (u64_range sp) as Rsp.
  do 6 step.
  apply evt_done. unfold PostCU.
  rewrite ?Z.add_0_r, ?Z_to_bv_lit_self.
  try (replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia; rewrite ?Z_to_bv_lit_self).
  exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, mk.
  split; [reflexivity|]. split; [exact WM|]. split; [exact MI|]. split.
  - pose proof (stk_release rsegs mk lo (SP + -32) _ ST FR ltac:(lia)) as ST2.
    cbn [cells_size csize Nat.add] in ST2. replace (SP + -32 + Z.of_nat 32) with SP in ST2 by lia. exact ST2.
  - split; [exact MU | exact UA].
Qed.

(* 0x136f0: the tag decision is made; s0 = n (or n - 4), s1 = f, the frame bytes are cu_bytes *)
Lemma cu_mid : forall (mk : word -> option byte) (j : list byte)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  rw_cells rsegs mk (SP + -32) [CB 8 j; C8 s1; C8 s0; C8 ra] ->
  stk rsegs mk lo (SP + -32) -> lo + 32 <= SP ->
  wmono rsegs m mk -> mem_inv rsegs mk ->
  munch ((SP - 32, SP) :: cu_footprint FA N bs) m mk ->
  50 <= N -> N <= Z.of_nat (length bs) -> 8 <= FA ->
  u8arr rsegs mk FA (cu_bytes N bs) ->
  bv_unsigned x8 = cu_len N bs -> bv_unsigned x9 = FA ->
  evt rsegs PostCU
    (MS (mkR x1 (Z_to_bv 64 (SP + -32)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x136f0) fc None mk (seg_rom rsegs)).
Proof.
  intros mk j x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FR ST LO WM MI MU BIG LN F8 UA E8 E9.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a1) as Ra1. pose proof (u64_range x8) as Rx8.
  assert (LU : length (cu_bytes N bs) = length bs).
  { unfold cu_bytes. destruct (cu_moves N bs); [|reflexivity].
    apply upd_bytes_length. rewrite firstn_length, skipn_length. lia. }
  assert (CL : N - 4 <= cu_len N bs <= N) by (unfold cu_len; destruct (cu_moves N bs); lia).
  pose proof (proj1 UA) as BA. pose proof BA as (B0 & B1 & _). rewrite LU in B1.
  pose proof (rd1 mk _ _ 16 BA ltac:(lia)) as R16. change (Z.of_nat 16) with 16 in R16.
  pose proof (rd1 mk _ _ 17 BA ltac:(lia)) as R17. change (Z.of_nat 17) with 17 in R17.
  remember (nth 16 (cu_bytes N bs) (Z_to_bv 8 0)) as b16 eqn:E16.
  remember (nth 17 (cu_bytes N bs) (Z_to_bv 8 0)) as b17 eqn:E17.
  step. step. step.
  eapply evt_cut.
  { eapply (reac_frame_is_reac_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mk (cu_bytes N bs)).
    intros _ _. split; [lia|]. rewrite ?unsigned_lit by lia. rewrite ?Z.add_0_r, ?E9. exact BA. }
  intros ms' (y1 & y2 & y3 & ->).
  replace (ret_pc (Z_to_bv 64 79612)) with (Z_to_bv 64 79612) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite is_reac_result_eq by (rewrite ?unsigned_lit by lia; lia).
  unfold is_reac_byte.
  remember (nth 12 (cu_bytes N bs) (Z_to_bv 8 0)) as b12 eqn:E12.
  remember (nth 13 (cu_bytes N bs) (Z_to_bv 8 0)) as b13 eqn:E13.
  assert (RES : forall r, r = copy_untag_result N bs ->
            ((bv_unsigned b12 = 0x88 /\ bv_unsigned b13 = 0x19 /\ bv_unsigned b16 = 0 /\ bv_unsigned b17 = 0)
             -> r = cu_len N bs) /\
            (~ (bv_unsigned b12 = 0x88 /\ bv_unsigned b13 = 0x19 /\ bv_unsigned b16 = 0 /\ bv_unsigned b17 = 0)
             -> r = 0)).
  { intros r ->. unfold copy_untag_result, cu_byte. rw_bytes.
    rewrite (proj2 (Z.ltb_ge _ _) BIG). split; intros H; dec; try reflexivity; exfalso; tauto. }
  destruct (Z.eqb_spec (bv_unsigned b12) 0x88) as [H12|H12];
  destruct (Z.eqb_spec (bv_unsigned b13) 0x19) as [H13|H13]; cbn [andb].
  2-4: (step; if_true; step;
        eapply (cu_exit mk j); first [eassumption | lia | (intros; eassumption) | idtac];
        rewrite (proj2 (RES _ eq_refl)) by tauto; reflexivity).
  step. if_false. step. step. if_cases H16.
  { zc H16. step. eapply (cu_exit mk j); first [eassumption | lia | (intros; eassumption) | idtac].
    rewrite (proj2 (RES _ eq_refl)) by tauto. reflexivity. }
  zc H16. step. step. if_cases H17.
  { zc H17. eapply (cu_exit mk j); first [eassumption | lia | (intros; eassumption) | idtac].
    rewrite (proj1 (RES _ eq_refl)) by tauto. rewrite <- E8. symmetry. apply Z_to_bv_lit_self. }
  zc H17. step. eapply (cu_exit mk j); first [eassumption | lia | (intros; eassumption) | idtac].
  rewrite (proj2 (RES _ eq_refl)) by tauto. reflexivity.
Qed.

End CU.

Theorem rp_copy_untag_holds : rp_copy_untag_contract.
Proof.
  unfold rp_copy_untag_contract, RP_COPY_UNTAG.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    ST LO MI HB.
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a0) as Ra0. pose proof (u64_range a1) as Ra1.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (Z.lt_ge_cases (bv_unsigned a1) 50) as [SMALL|BIG].
  - carve_frame 32%nat ST.
    do 4 step. step. step. step. if_true. step.
    eapply (cu_exit ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m bs lo);
      first [eassumption | lia | (intros; eassumption) | idtac].
    + unfold cu_footprint, cu_moves. rewrite (proj2 (Z.leb_gt _ _) SMALL). exact MU.
    + unfold copy_untag_result. rewrite (proj2 (Z.ltb_lt _ _) SMALL). reflexivity.
  - destruct (HB BIG) as (UA & LN & L62 & F8 & DISJ).
    carve_frame 32%nat ST.
    do 4 step.
    pose proof (proj1 UA) as BA. pose proof BA as (B0 & B1 & _).
    pose proof (rd1 _ _ bs 12 BA ltac:(lia)) as R12. change (Z.of_nat 12) with 12 in R12.
    pose proof (rd1 _ _ bs 13 BA ltac:(lia)) as R13. change (Z.of_nat 13) with 13 in R13.
    pose proof (rd1 _ _ bs 16 BA ltac:(lia)) as R16. change (Z.of_nat 16) with 16 in R16.
    pose proof (rd1 _ _ bs 17 BA ltac:(lia)) as R17. change (Z.of_nat 17) with 17 in R17.
    remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
    remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
    remember (nth 16 bs (Z_to_bv 8 0)) as b16 eqn:E16.
    remember (nth 17 bs (Z_to_bv 8 0)) as b17 eqn:E17.
    assert (LU : length (cu_bytes (bv_unsigned a1) bs) = length bs).
    { unfold cu_bytes. destruct (cu_moves (bv_unsigned a1) bs); [|reflexivity].
      apply upd_bytes_length. rewrite firstn_length, skipn_length. lia. }
    step. step. step. if_false.
    step. step. step. step. if_cases H81.
    1-2: zc H81.
    (* not tagged: f[12] != 0x81 *)
    { assert (NT : cu_moves (bv_unsigned a1) bs = false)
        by (unfold cu_moves, cu_tagged, cu_byte; rw_bytes; dec; reflexivity).
      eapply (cu_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m bs lo);
        first [eassumption | lia | idtac].
      all: try (unfold cu_footprint; rewrite NT; exact MU).
      all: try (unfold cu_bytes; rewrite NT; exact UA).
      all: unfold cu_len; rewrite ?NT; rewrite ?unsigned_lit by lia; lia. }
    step. step. if_cases H13.
    1-2: zc H13.
    { assert (NT : cu_moves (bv_unsigned a1) bs = false)
        by (unfold cu_moves, cu_tagged, cu_byte; rw_bytes; dec; reflexivity).
      eapply (cu_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m bs lo);
        first [eassumption | lia | idtac].
      all: try (unfold cu_footprint; rewrite NT; exact MU).
      all: try (unfold cu_bytes; rewrite NT; exact UA).
      all: unfold cu_len; rewrite ?NT; rewrite ?unsigned_lit by lia; lia. }
    step. step. step. if_cases H16.
    1-2: zc H16.
    { assert (NT : cu_moves (bv_unsigned a1) bs = false)
        by (unfold cu_moves, cu_tagged, cu_byte; rw_bytes; dec; reflexivity).
      eapply (cu_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m bs lo);
        first [eassumption | lia | idtac].
      all: try (unfold cu_footprint; rewrite NT; exact MU).
      all: try (unfold cu_bytes; rewrite NT; exact UA).
      all: unfold cu_len; rewrite ?NT; rewrite ?unsigned_lit by lia; lia. }
    step. step. step. if_cases H17.
    1-2: zc H17.
    { assert (NT : cu_moves (bv_unsigned a1) bs = false)
        by (unfold cu_moves, cu_tagged, cu_byte; rw_bytes; dec; reflexivity).
      eapply (cu_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m bs lo);
        first [eassumption | lia | idtac].
      all: try (unfold cu_footprint; rewrite NT; exact MU).
      all: try (unfold cu_bytes; rewrite NT; exact UA).
      all: unfold cu_len; rewrite ?NT; rewrite ?unsigned_lit by lia; lia. }
    (* tagged: memmove(f + 12, f + 16, n - 16) *)
    assert (TG : cu_moves (bv_unsigned a1) bs = true)
      by (unfold cu_moves, cu_tagged, cu_byte; rw_bytes; dec; reflexivity).
    step. step. step. step.
    eapply evt_cut.
    { eapply (memmove_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned a0) bs);
        first [exact UA | exact F8 | exact MI | (rewrite ?unsigned_lit by lia; lia)]. }
    intros ms' (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m2 & -> & MU2 & WM2 & MI2 & UA2).
    replace (ret_pc (Z_to_bv 64 79596)) with (Z_to_bv 64 79596) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite ?unsigned_lit in MU2 by lia.
    rewrite ?unsigned_lit in UA2 by lia.
    assert (UA3 : u8arr rsegs m2 (bv_unsigned a0) (cu_bytes (bv_unsigned a1) bs)).
    { unfold cu_bytes. rewrite TG. unfold mm_result, slice in UA2.
      match type of UA2 with u8arr _ _ _ (upd_bytes _ (Z.to_nat ?j) (firstn (Z.to_nat ?k) (skipn (Z.to_nat ?i) _))) =>
        replace (Z.to_nat j) with 12%nat in UA2 by lia; replace (Z.to_nat i) with 16%nat in UA2 by lia;
        replace (Z.to_nat k) with (Z.to_nat (bv_unsigned a1 - 16)) in UA2 by (f_equal; lia) end.
      exact UA2. }
    match type of MU2 with munch ?W _ _ =>
      apply (rw_cells_transport rsegs W _ m2) in FR; [ | exact MU2 | exact WM2 | cbn [disjoint_from]; simpl_sizes; slia ]
    end.
    match type of MU2 with munch [(?wl, ?wh)] _ _ =>
      apply (stk_moved _ m2 lo (bv_unsigned sp + -32) (bv_unsigned a0) (cu_bytes (bv_unsigned a1) bs) wl wh) in ST;
        [ | exact MU2 | exact WM2 | exact (proj1 UA3) | rewrite LU; intros x Hx; lia ]
    end.
    assert (MU3 : munch ((bv_unsigned sp - 32, bv_unsigned sp) :: cu_footprint (bv_unsigned a0) (bv_unsigned a1) bs) m m2).
    { unfold cu_footprint. rewrite TG.
      match type of MU with munch _ _ ?m0 =>
        apply (munch_trans _ _ m0); [eapply munch_weaken; [|exact MU] | eapply munch_weaken; [|exact MU2]];
        unfold sub_fp; intros x Hx; cbn [outside] in *; split; try exact I; lia
      end. }
    pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3.
    step.
    eapply (cu_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m bs lo);
      first [eassumption | lia | idtac].
    all: unfold cu_len; rewrite ?TG; rewrite ?unsigned_lit by lia; lia.
Qed.

End W.
