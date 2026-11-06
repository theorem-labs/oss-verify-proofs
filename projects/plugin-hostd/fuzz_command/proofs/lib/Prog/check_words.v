From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes FP ZBridge Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import CType StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CommandModel CommandFP CommandTac
  printf_facts_c atoi_c snprintf_c strcmp_c strspn_c strcspn_c check_words_c check_words_chain syntax_reply_matches
  check_words_add_c check_words_chain_c check_words_pin_set_c CwItems.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require MemNorm KindBGlue.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecFacts.
Import ListNotations.
Open Scope Z_scope.

(* check_words from its entry 0x14980 to the call of joined (0x149d4): the 176-byte frame holds the saved
   registers and W at sp+24; s1 = min(nwords, 64), a0 = W, a1 = sp+48. *)
Definition cw_mid1 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (W n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' j0 j1 j2 j4 j5 j6 j7,
    ms' = MS (mkR (Z_to_bv 64 0x149d8) (Z_to_bv 64 (bv_unsigned sp + -176)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (Z.min n 64))
                  (Z_to_bv 64 W) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x14fdc) fc None m' (seg_rom rsegs)
    /\ a1 = Z_to_bv 64 (bv_unsigned sp + -128)
    /\ munch [(bv_unsigned sp + -176, bv_unsigned sp)] m m' /\ wmono rsegs m m'
    /\ rw_cells rsegs m' (bv_unsigned sp + -176)
         [CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 W); CB 8 j4; CB 8 j5; CB 8 j6; CB 16 j7;
          C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma cw_run1 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo W n : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 176 <= bv_unsigned sp -> 0 <= n < 2 ^ 31 ->
  0 <= W -> bv_unsigned sp <= W + 16 -> W + 32 <= 2 ^ 64 ->
  bytes_at rsegs m (W + 24) (le4 (Z_to_bv 64 n)) ->
  evt rsegs (cw_mid1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W n m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 W) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14980) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo W n ST LO NR W0 W1 W2 HN.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  apply bytes_ro4 in HN.
  pose proof (munch_refl [(bv_unsigned sp + -176, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 176%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 176%nat junk []
           [8; 8; 8; 8; 8; 8; 8; 16; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 17 zstep.
  rewrite (sx32_lit n) by lia.
  zstep. if_cases Q.
  - zify_cond Q. rewrite ?signed_lit in Q by lia.
    zstep. zstep. zstep.
    apply evt_done. unfold cw_mid1. rewrite (Z.min_l n 64) by lia.
    do 22 eexists. split; [reflexivity|].
    split; [first [reflexivity | (f_equal; lia) | (f_equal; rewrite ?unsigned_lit by lia; lia)]|].
    split; [exact MU|]. split; [exact WM|]. exact FR.
  - zify_cond Q. rewrite ?signed_lit in Q by lia.
    zstep. zstep. zstep. zstep.
    apply evt_done. unfold cw_mid1. rewrite (Z.min_r n 64) by lia.
    do 22 eexists. split; [reflexivity|].
    split; [first [reflexivity | (f_equal; lia) | (f_equal; rewrite ?unsigned_lit by lia; lia)]|].
    split; [exact MU|]. split; [exact WM|]. exact FR.
Qed.

Definition fpr (F Fc : bvmap 5 word) : Prop := forall k : reg, bv_unsigned k <> 10 -> reg_get Fc k = reg_get F k.

(* The state at free's entry 0x188cc after check_words' epilogue: the caller's ra, sp and callee-saved
   registers, a0 = the joined line; memory changed only in [lo, sp). *)
Definition cw_body_post (gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o : word) (F : bvmap 5 word)
    (lo S0 : Z) (lp : word) (mr : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (Fc : bvmap 5 word) (fc : bv 32)
                    (m : word -> option byte),
    ms' = MS (mkR rao (Z_to_bv 64 S0) gp tp xt0 xt1 xt2 s0o s1o lp xa1 xa2 xa3 xa4 xa5 xa6 xa7
                  s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o xt3 xt4 xt5 xt6)
             Fc (Z_to_bv 64 0x188cc) fc None m (seg_rom rsegs) /\
    mem_inv rsegs m /\ munch [(lo, S0)] mr m /\ wmono rsegs mr m /\ stk rsegs m lo S0 /\ frm0 fc /\ fpr F Fc.

Lemma cw_release : forall m lo S cs0 lp j jb rg, stk rsegs m lo S -> lo <= S -> cells_size cs0 = 40%nat ->
  rw_cells rsegs m S (cs0 ++ [C8 lp]) -> rw_cells rsegs m (S + 48) [CB 8 j] -> rw_cells rsegs m (S + 56) [CB 16 jb] ->
  rw_cells rsegs m (S + 72) rg -> cells_size rg = 104%nat -> stk rsegs m lo (S + 176).
Proof.
  intros m lo S cs0 lp j jb rg ST HL CS F0 F1 F2 F3 CR.
  apply (stk_release rsegs m lo S _ ST) in F0; [|lia]. rewrite cells_size_app, CS in F0. cbn [cells_size csize Nat.add] in F0.
  replace (S + Z.of_nat 48) with (S + 48) in F0 by lia.
  apply (stk_release rsegs m lo _ _ F0) in F1; [|lia]. cbn [cells_size csize Nat.add] in F1.
  replace (S + 48 + Z.of_nat 8) with (S + 56) in F1 by lia.
  apply (stk_release rsegs m lo _ _ F1) in F2; [|lia]. cbn [cells_size csize Nat.add] in F2.
  replace (S + 56 + Z.of_nat 16) with (S + 72) in F2 by lia.
  apply (stk_release rsegs m lo _ _ F2) in F3; [|lia]. rewrite CR in F3.
  replace (S + 72 + Z.of_nat 104) with (S + 176) in F3 by lia. exact F3.
Qed.

(* 0x14bd4 to free's entry: a0 = the line, the saved registers back, sp + 176, tail jump to free. *)
Lemma cw_tail : forall gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o (F : bvmap 5 word) lo S lp mr
    cs0 j jb xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
    xt3 xt4 xt5 xt6 Fc fc mc,
  lo <= S -> S + 176 < 2 ^ 64 -> cells_size cs0 = 40%nat ->
  mem_inv rsegs mc -> munch [(lo, S + 176)] mr mc -> wmono rsegs mr mc -> stk rsegs mc lo S -> frm0 fc -> fpr F Fc ->
  rw_cells rsegs mc S (cs0 ++ [C8 lp]) -> rw_cells rsegs mc (S + 48) [CB 8 j] -> rw_cells rsegs mc (S + 56) [CB 16 jb] ->
  rw_cells rsegs mc (S + 72)
    [C8 s11o; C8 s10o; C8 s9o; C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  evt rsegs (cw_body_post gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o F lo (S + 176) lp mr)
    (MS (mkR xra (Z_to_bv 64 S) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
        Fc (Z_to_bv 64 0x14bd4) fc None mc (seg_rom rsegs)).
Proof.
  intros gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o F lo S lp mr
    cs0 j jb xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
    xt3 xt4 xt5 xt6 Fc fc mc HLS HS CS MI MU WM ST FRM FP F0 F1 F2 F3.
  pose proof (cw_release mc lo S cs0 lp j jb _ ST HLS CS F0 F1 F2 F3 eq_refl) as ST2.
  assert (F40 : rw_cells rsegs mc (S + 40) [C8 lp]).
  { apply rw_cells_app in F0. destruct F0 as [_ F0]. rewrite CS in F0. exact F0. }
  clear F0 F1 F2 ST.
  do 16 zstep.
  apply evt_done. unfold cw_body_post. do 17 eexists. split; [reflexivity|].
  split; [exact MI|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST2|]. split; [exact FRM | exact FP].
Qed.

Definition CW_GREC : Z := 0x33d48.

(* A pointer at A (below lo) to a C string s below lo. *)
Definition lowp (lo : Z) (m : word -> option byte) (A : Z) (p : word) (s : list byte) : Prop :=
  bytes_at rsegs m A (le8 p) /\ 0 <= A /\ A + 8 <= lo /\ bv_unsigned p <> 0 /\
  bytes_at rsegs m (bv_unsigned p) (s ++ [NUL]) /\ ~ In NUL s /\ bv_unsigned p + Z.of_nat (length s) + 1 <= lo.

(* The recorded call c at a (the record's calls[i]): fn, nargs and the argument strings. *)
Definition call_at_a (m : word -> option byte) (lo a : Z) (c : Z * list (list byte)) : Prop :=
  0 <= a /\ a + 56 <= lo /\
  bytes_at rsegs m a (le4 (Z_to_bv 64 (fst c))) /\
  bytes_at rsegs m (a + 4) (le4 (Z_to_bv 64 (Z.of_nat (length (snd c))))) /\
  0 <= fst c < 26 /\ (length (snd c) <= 6)%nat /\
  forall k s, nth_error (snd c) k = Some s -> exists p, lowp lo m (a + 8 + 8 * Z.of_nat k) p s.

Lemma disj_low : forall W lo A n, disjoint_from W 0 lo -> 0 <= A -> A + n <= lo -> 0 <= n -> disjoint_from W A n.
Proof.
  induction W as [|[a b] W IH]; cbn [disjoint_from]; intros lo A n H HA Hn H0; [exact I|].
  destruct H as [H1 H2]. split; [lia | exact (IH lo A n H2 HA Hn H0)].
Qed.

Lemma bytes_low : forall W m m' lo A bs, bytes_at rsegs m A bs -> munch W m m' -> disjoint_from W 0 lo ->
  A + Z.of_nat (length bs) <= lo -> bytes_at rsegs m' A bs.
Proof.
  intros W m m' lo A bs H MU D L. pose proof H as (H0 & _).
  eapply bytes_at_transport; [exact H | exact MU | apply (disj_low W lo); [exact D | lia | lia | lia]].
Qed.

Lemma lowp_tp : forall W m m' lo A p s, lowp lo m A p s -> munch W m m' -> disjoint_from W 0 lo -> lowp lo m' A p s.
Proof.
  intros W m m' lo A p s (H1 & H2 & H3 & H4 & H5 & H6 & H7) MU D.
  split; [apply (bytes_low W m m' lo A); [exact H1 | exact MU | exact D | rewrite length_le8; lia]|].
  split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [apply (bytes_low W m m' lo); [exact H5 | exact MU | exact D | rewrite length_app; cbn [length]; lia]|].
  split; [exact H6 | exact H7].
Qed.

Lemma call_tp : forall W m m' lo a c, call_at_a m lo a c -> munch W m m' -> disjoint_from W 0 lo -> call_at_a m' lo a c.
Proof.
  intros W m m' lo a c (H0 & H1 & H2 & H3 & H4 & H5 & H6) MU D.
  split; [exact H0|]. split; [exact H1|].
  split; [apply (bytes_low W m m' lo a); [exact H2 | exact MU | exact D | rewrite length_le4; lia]|].
  split; [apply (bytes_low W m m' lo); [exact H3 | exact MU | exact D | rewrite length_le4; lia]|].
  split; [exact H4|]. split; [exact H5|].
  intros k s E. destruct (H6 k s E) as (p & Hp). exists p. exact (lowp_tp W m m' lo _ p s Hp MU D).
Qed.

Lemma lowp_slot : forall lo S m A p s, lowp lo m A p s -> word_slot m lo S A p s.
Proof.
  intros lo S m A p s (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  split; [exact H1|]. split; [unfold outside_stack; cbn [disjoint_from]; split; [lia | exact I]|].
  split; [split; [exact H5 | exact H6]|]. unfold outside_stack; cbn [disjoint_from]; split; [lia | exact I].
Qed.

Lemma lowp_ptr : forall lo S m A p s, lowp lo m A p s -> lo <= S -> ptr_at m [(lo, S); (S + 56, S + 72)] A s.
Proof.
  intros lo S m A p s (H1 & H2 & H3 & H4 & H5 & H6 & H7) HS. exists p.
  split; [exact H1|]. split; [cbn [disjoint_from]; split; [lia | split; [lia | exact I]]|].
  split; [exact H4|]. split; [exact H5|]. cbn [disjoint_from]; split; [lia | split; [lia | exact I]].
Qed.

Lemma outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[a b] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto]. destruct (Z_le_gt_dec a x); destruct (Z_lt_ge_dec x b); tauto || (left; split; [lia | exact H]).
Qed.

Lemma task_mem_fw : forall W m m', MemNorm.task_mem rsegs m ->
  (forall x : word, ~ outside W (bv_unsigned x) -> wview rsegs m x <> None) -> munch W m m' -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' TM HW MU a b E.
  destruct (m a) as [b'|] eqn:Ea; [exact (TM a b' Ea)|].
  destruct (find_segment rsegs (bv_unsigned a) 1) as [sg|] eqn:Fs; [left; discriminate|].
  destruct (outside_dec W (bv_unsigned a)) as [Ho|Ho].
  - rewrite (MU a Ho), Ea in E. discriminate.
  - exfalso. apply (HW a Ho). unfold wview. rewrite Ea, Fs. reflexivity.
Qed.

Section Body.
Variables (gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o : word) (F : bvmap 5 word)
  (mL : word -> option byte) (lo S r : Z) (ws : list (list byte)) (wpw : list word)
  (W arr lp can : word) (calls : list (Z * list (list byte))) (j48 jb0 : list byte).

Local Notation FW := [(lo, S); (S + 56, S + 72)].

Hypothesis SSP : strspn_contract.
Hypothesis SCS : strcspn_contract.
Hypothesis ATOI : atoi_contract.
Hypothesis SNP : snprintf_contract.
Hypothesis SC : strcmp_contract.
Hypothesis ADD : check_words_add_contract.
Hypothesis CHAIN : check_words_chain_contract.
Hypothesis PIN : check_words_pin_set_contract.
Hypothesis LO : lo + 8272 <= S.
Hypothesis IE : 0x54cb8 <= lo.
Hypothesis SPH : S + 176 < 2 ^ 63.
Hypothesis RR : 0 <= r <= 64.
Hypothesis HOK : Forall (call_words_ok r ws) calls.
Hypothesis NCL : (length calls <= 16)%nat.
Hypothesis FR0 : rw_cells rsegs mL S
  [C8 (Z_to_bv 64 0x10828); C8 (Z_to_bv 64 CW_GREC); C8 (Z_to_bv 64 0x10a38); C8 W; C8 (Z_to_bv 64 0x1045f); C8 lp].
Hypothesis FR48 : rw_cells rsegs mL (S + 48) [CB 8 j48].
Hypothesis BUF0 : rw_cells rsegs mL (S + 56) [CB 16 jb0].
Hypothesis FRH : rw_cells rsegs mL (S + 72)
  [C8 s11o; C8 s10o; C8 s9o; C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao].
Hypothesis GG : rw_cells rsegs mL 0x22a68 [C8 (Z_to_bv 64 0x54450)].
Hypothesis GU : rw_cells rsegs mL 0x54450 [C8 can].
Hypothesis HNC : bytes_at rsegs mL (CW_GREC + 8) (le4 (Z_to_bv 64 (Z.of_nat (length calls)))).
Hypothesis HCA : forall i c, nth_error calls i = Some c -> call_at_a mL lo (CW_GREC + 16 + 56 * Z.of_nat i) c.
Hypothesis HWA : bytes_at rsegs mL (bv_unsigned W + 16) (le8 arr).
Hypothesis HWB : S + 176 <= bv_unsigned W + 16.
Hypothesis HWS : forall k, 0 <= k < r ->
  lowp lo mL (bv_unsigned arr + 8 * k) (nth (Z.to_nat k) wpw (Z_to_bv 64 0)) (nth (Z.to_nat k) ws []).
Hypothesis HL : bytes_at rsegs mL (bv_unsigned lp) (RecFacts.join_sp ws ++ [NUL]) /\ ~ In NUL (RecFacts.join_sp ws) /\
  bv_unsigned lp + Z.of_nat (length (RecFacts.join_sp ws)) + 1 <= lo.
Hypothesis TM : MemNorm.task_mem rsegs mL.
Hypothesis STL : stk rsegs mL lo S.

Lemma dFW : disjoint_from FW 0 lo.
Proof. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I]. Qed.

Lemma TMW : forall mc, munch FW mL mc -> MemNorm.task_mem rsegs mc.
Proof.
  intros mc MU. apply (task_mem_fw FW mL mc TM); [|exact MU].
  intros x Hx. cbn [outside] in Hx.
  assert (C : lo <= bv_unsigned x < S \/ S + 56 <= bv_unsigned x < S + 72) by tauto.
  destruct C as [C|C].
  - destruct STL as (_ & _ & H). destruct (H (bv_unsigned x) C) as [Hw _]. unfold wa in Hw.
    rewrite Z_to_bv_bv_unsigned in Hw. exact Hw.
  - destruct BUF0 as [_ (_ & _ & Hw)]. cbn [cells_size csize Nat.add] in Hw.
    pose proof (Hw (bv_unsigned x - (S + 56)) ltac:(lia)) as H. unfold wa in H.
    replace (S + 56 + (bv_unsigned x - (S + 56))) with (bv_unsigned x) in H by lia.
    rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.

Ltac tpc H MU WM := eapply rw_cells_transport; [exact H | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia].

Lemma fr_at : forall mc, munch FW mL mc -> wmono rsegs mL mc ->
  rw_cells rsegs mc S
    [C8 (Z_to_bv 64 0x10828); C8 (Z_to_bv 64 CW_GREC); C8 (Z_to_bv 64 0x10a38); C8 W; C8 (Z_to_bv 64 0x1045f); C8 lp] /\
  rw_cells rsegs mc (S + 48) [CB 8 j48] /\
  rw_cells rsegs mc (S + 72)
    [C8 s11o; C8 s10o; C8 s9o; C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] /\
  rw_cells rsegs mc 0x22a68 [C8 (Z_to_bv 64 0x54450)] /\ rw_cells rsegs mc 0x54450 [C8 can].
Proof.
  intros mc MU WM.
  split; [tpc FR0 MU WM|]. split; [tpc FR48 MU WM|]. split; [tpc FRH MU WM|]. split; [tpc GG MU WM | tpc GU MU WM].
Qed.

Definition oinv (m : word -> option byte) (Fc : bvmap 5 word) (fc : bv 32) : Prop :=
  mem_inv rsegs m /\ munch FW mL m /\ wmono rsegs mL m /\ stk rsegs m lo S /\
  (exists jb, rw_cells rsegs m (S + 56) [CB 16 jb]) /\ frm0 fc /\ fpr F Fc.

Abbreviation OS pc c xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs10 xt3 xt4 xt5 xt6 Fc fc m :=
  (MS (mkR xra (Z_to_bv 64 S) gp tp xt0 xt1 xt2 xs0 (Z_to_bv 64 r) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
         (Z_to_bv 64 CW_GREC) (Z_to_bv 64 0x1034c) (Z_to_bv 64 (CW_GREC + 24 + 56 * c)) xs5 xs6 xs7 xs8
         (Z_to_bv 64 c) xs10 (Z_to_bv 64 35) xt3 xt4 xt5 xt6) Fc (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Definition Qb : machine_state -> Prop :=
  cw_body_post gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o F lo (S + 176) lp mL.

(* 0x14bd4 from any register state with the loop invariant: the epilogue. *)
Lemma end_ok : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
    xt3 xt4 xt5 xt6 Fc fc mc,
  oinv mc Fc fc ->
  evt rsegs Qb (MS (mkR xra (Z_to_bv 64 S) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                   Fc (Z_to_bv 64 0x14bd4) fc None mc (seg_rom rsegs)).
Proof.
  intros xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
    xt3 xt4 xt5 xt6 Fc fc mc (MI & MU & WM & ST & (jb & BUF) & FRM & FP).
  destruct (fr_at mc MU WM) as (F0 & F1 & F2 & _).
  eapply (cw_tail gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o F lo S lp mL
            [C8 (Z_to_bv 64 0x10828); C8 (Z_to_bv 64 CW_GREC); C8 (Z_to_bv 64 0x10a38); C8 W; C8 (Z_to_bv 64 0x1045f)]);
    [lia | lia | reflexivity | exact MI | | exact WM | exact ST | exact FRM | exact FP | exact F0 | exact F1 | exact BUF
    | exact F2].
  eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. lia.
Qed.

Definition at_bc4 (c : Z) : machine_state -> Prop := fun ms' =>
  exists (xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs10 xt3 xt4 xt5 xt6 : word)
         (Fc : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ms' = OS 0x14bc4 c xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs10 xt3 xt4 xt5 xt6 Fc fc m /\
    oinv m Fc fc.

Lemma oinv_void : forall mc m' Fc fc, oinv mc Fc fc -> munch [(lo, S)] mc m' -> wmono rsegs mc m' ->
  mem_inv rsegs m' -> stk rsegs m' lo S -> oinv m' Fc fc.
Proof.
  intros mc m' Fc fc (MI & MU & WM & ST & (jb & BUF) & FRM & FP) MU2 WM2 MI2 ST2.
  split; [exact MI2|]. split.
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
  split; [exact (wmono_trans rsegs _ _ _ WM WM2)|]. split; [exact ST2|].
  split; [exists jb; tpc BUF MU2 WM2|]. split; [exact FRM | exact FP].
Qed.

Lemma call_of : forall c cl, nth_error calls (Z.to_nat c) = Some cl -> 0 <= c ->
  call_at_a mL lo (CW_GREC + 56 * c + 16) cl /\ call_words_ok r ws cl.
Proof.
  intros c cl Hc C0. split.
  - pose proof (HCA _ _ Hc) as H. rewrite Z2Nat.id in H by lia.
    replace (CW_GREC + 56 * c + 16) with (CW_GREC + 16 + 56 * c) by lia. exact H.
  - rewrite Forall_forall in HOK. apply HOK. exact (nth_error_In _ _ Hc).
Qed.

Lemma arg_slot : forall a cl mc k, call_at_a mL lo a cl -> munch FW mL mc -> (k < length (snd cl))%nat ->
  exists p, word_slot mc lo S (a + CALL_ARGS + 8 * Z.of_nat k) p (nth k (snd cl) []).
Proof.
  intros a cl mc k HA MU Hk. destruct HA as (_ & _ & _ & _ & _ & _ & H).
  destruct (H k (nth k (snd cl) []) (nth_error_nth' _ _ Hk)) as (p & Hp). exists p.
  apply lowp_slot. unfold CALL_ARGS. eapply lowp_tp; [exact Hp | exact MU | exact dFW].
Qed.

Lemma word_slot_at : forall mc k, munch FW mL mc -> 0 <= k < r ->
  word_slot mc lo S (bv_unsigned arr + 8 * k) (nth (Z.to_nat k) wpw (Z_to_bv 64 0)) (nth (Z.to_nat k) ws []).
Proof. intros mc k MU Hk. apply lowp_slot. eapply lowp_tp; [exact (HWS k Hk) | exact MU | exact dFW]. Qed.

Lemma arr_at : forall mc, munch FW mL mc -> ro_cells rsegs mc (bv_unsigned W + 16) [C8 arr].
Proof.
  intros mc MU. apply bytes_ro8. eapply bytes_at_transport; [exact HWA | exact MU |].
  rewrite length_le8. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma ncl_at : forall mc, munch FW mL mc -> ro_cells rsegs mc (CW_GREC + 8) [C4 (Z_to_bv 64 (Z.of_nat (length calls)))].
Proof.
  intros mc MU. apply bytes_ro4. eapply bytes_low; [exact HNC | exact MU | exact dFW |].
  rewrite length_le4. unfold CW_GREC. lia.
Qed.

Ltac zc H := zify_cond H; rewrite ?unsigned_lit in H by lia; rewrite ?Z.mod_small in H by lia.

(* 0x14b6c: the per-kind check of the call's verb (kinds 20, 17, 0), then the join point 0x14bc4. *)
Lemma kinds : forall c cl xra xt0 xt1 xt2 xs0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs8 xs10 xt3 xt4 xt5 xt6 Fc fc mc,
  nth_error calls (Z.to_nat c) = Some cl -> 0 <= c < 16 -> oinv mc Fc fc ->
  evt rsegs (at_bc4 c) (OS 0x14b6c c xra xt0 xt1 xt2 xs0 (Z_to_bv 64 (fst cl)) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                          (Z_to_bv 64 (CW_GREC + 56 * c + 16)) xs6 xs7 xs8 xs10 xt3 xt4 xt5 xt6 Fc fc mc).
Proof.
  intros c cl xra xt0 xt1 xt2 xs0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs8 xs10 xt3 xt4 xt5 xt6 Fc fc mc Hc C0 HI.
  destruct (call_of c cl Hc ltac:(lia)) as [HA HK].
  pose proof HA as (A0 & A1 & A2 & A3 & A4 & A5 & A6).
  pose proof HI as (MI & MU & WM & ST & (jb & BUF) & FRM & FP).
  destruct (fr_at mc MU WM) as (F0 & F1 & F2 & G1 & G2).
  pose proof (arr_at mc MU) as RA.
  destruct HK as (K1 & K2 & K3 & K4).
  assert (NA : bytes_at rsegs mc (CW_GREC + 56 * c + 16 + 4) (le4 (Z_to_bv 64 (Z.of_nat (length (snd cl)))))).
  { eapply bytes_low; [exact A3 | exact MU | exact dFW | rewrite length_le4; lia]. }
  assert (GREC : CW_GREC = 212296) by reflexivity.
  zstep. zstep. if_cases Q20.
  - zc Q20.
    assert (E20 : fst cl = 20) by lia.
    destruct (K4 E20) as (L4 & V4).
    destruct (arg_slot _ cl mc 3 HA MU ltac:(lia)) as (p3 & P3). change (8 * Z.of_nat 3) with 24 in P3.
    do 5 zstep.
    pose proof PIN as PC. unfold check_words_pin_set_contract, CHECK_WORDS_PIN_SET in PC.
    eapply evt_cut.
    { eapply PC with (lo := lo) (r := r) (nargs := 4) (p4 := nth 4 wpw (Z_to_bv 64 0)) (p3 := p3)
                     (w4 := nth 4 ws []) (x3 := nth 3 (snd cl) []).
      - exact MI.
      - rewrite !unsigned_lit by lia. exact ST.
      - rewrite !unsigned_lit by lia. unfold CHECK_WORDS_PIN_SET_K. lia.
      - unfold CommandModel.IMG_END. lia.
      - exact RR.
      - reflexivity.
      - intros H4. rewrite !unsigned_lit by lia.
        pose proof (word_slot_at mc 4 MU ltac:(lia)) as H. change (Z.to_nat 4) with 4%nat in H.
        replace (bv_unsigned arr + 32) with (bv_unsigned arr + 8 * 4) by lia. exact H.
      - lia.
      - rewrite !unsigned_lit by lia. try unfold CALL_NARGS. rewrite L4 in NA. exact NA.
      - rewrite !unsigned_lit by lia. unfold outside_stack; try unfold CALL_NARGS. cbn [disjoint_from]. split; [lia | exact I].
      - intros _. rewrite !unsigned_lit by lia. exact P3.
      - reflexivity.
      - exact V4. }
    intros ms' (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & E & MU2 & WM2 & MI2 & ST2).
    subst ms'. rewrite unsigned_lit in MU2, ST2 by lia. fix_ret.
    apply evt_done. unfold at_bc4. do 25 eexists. split; [reflexivity|].
    exact (oinv_void mc m' Fc fc HI MU2 WM2 MI2 ST2).
  - zc Q20.
    zstep. zstep. if_cases Q17.
    + zc Q17.
      assert (E17 : fst cl = 17) by lia.
      destruct (K3 E17) as (L3 & V1 & V2).
      destruct (arg_slot _ cl mc 1 HA MU ltac:(lia)) as (p1 & P1). change (8 * Z.of_nat 1) with 8 in P1.
      destruct (arg_slot _ cl mc 2 HA MU ltac:(lia)) as (p2 & P2). change (8 * Z.of_nat 2) with 16 in P2.
      do 5 zstep.
      pose proof CHAIN as PC. unfold check_words_chain_contract, CHECK_WORDS_CHAIN in PC.
      eapply evt_cut.
      { eapply PC with (lo := lo) (r := r) (nargs := 3) (wp := wpw) (ws := ws) (p1 := p1) (p2 := p2)
                       (x1 := nth 1 (snd cl) []) (x2 := nth 2 (snd cl) []) (can := can).
        - exact MI.
        - exact (TMW mc MU).
        - exact FRM.
        - rewrite !unsigned_lit by lia. exact ST.
        - rewrite !unsigned_lit by lia. unfold CHECK_WORDS_CHAIN_K. lia.
        - unfold CommandModel.IMG_END. lia.
        - rewrite !unsigned_lit by lia. lia.
        - exact G1.
        - exact G2.
        - exact RR.
        - reflexivity.
        - intros k Hk. rewrite !unsigned_lit by lia. exact (word_slot_at mc k MU ltac:(lia)).
        - lia.
        - rewrite !unsigned_lit by lia. try unfold CALL_NARGS. rewrite L3 in NA. exact NA.
        - rewrite !unsigned_lit by lia. unfold outside_stack; try unfold CALL_NARGS. cbn [disjoint_from]. split; [lia | exact I].
        - intros _. rewrite !unsigned_lit by lia. exact P1.
        - intros _. rewrite !unsigned_lit by lia. exact P2.
        - reflexivity.
        - exact V1.
        - exact V2. }
      intros ms' (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & Ft & fc' & m' &
                  E & MU2 & WM2 & MI2 & FRM2 & FP2 & ST2).
      subst ms'. rewrite unsigned_lit in MU2, ST2 by lia. fix_ret.
      zstep.
      apply evt_done. unfold at_bc4. do 25 eexists. split; [reflexivity|].
      pose proof (oinv_void mc m' Fc fc HI MU2 WM2 MI2 ST2) as (H1 & H2 & H3 & H4 & H5 & _ & H7).
      split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
      split; [exact FRM2|]. intros k Hk. rewrite (FP2 k Hk). exact (H7 k Hk).
    + zc Q17.
      zstep. if_cases Q0.
      * apply evt_done. unfold at_bc4. do 25 eexists. split; [reflexivity | exact HI].
      * zc Q0.
        assert (E0 : fst cl = 0) by lia.
        destruct (K2 E0) as (L4 & V2 & V3).
        destruct (arg_slot _ cl mc 2 HA MU ltac:(lia)) as (q2 & P2). change (8 * Z.of_nat 2) with 16 in P2.
        destruct (arg_slot _ cl mc 3 HA MU ltac:(lia)) as (q3 & P3). change (8 * Z.of_nat 3) with 24 in P3.
        do 5 zstep.
        pose proof ADD as PC. unfold check_words_add_contract, CHECK_WORDS_ADD in PC.
        eapply evt_cut.
        { eapply PC with (lo := lo) (r := r) (nargs := 4) (p3 := nth 3 wpw (Z_to_bv 64 0))
                         (p4 := nth 4 wpw (Z_to_bv 64 0)) (q2 := q2) (q3 := q3) (w3 := nth 3 ws []) (w4 := nth 4 ws [])
                         (x2 := nth 2 (snd cl) []) (x3 := nth 3 (snd cl) []).
          - exact MI.
          - rewrite !unsigned_lit by lia. exact ST.
          - rewrite !unsigned_lit by lia. unfold CHECK_WORDS_ADD_K. lia.
          - unfold CommandModel.IMG_END. lia.
          - exact RR.
          - reflexivity.
          - intros H3. rewrite !unsigned_lit by lia.
            pose proof (word_slot_at mc 3 MU ltac:(lia)) as H. change (Z.to_nat 3) with 3%nat in H.
            replace (bv_unsigned arr + 24) with (bv_unsigned arr + 8 * 3) by lia. exact H.
          - intros H4. rewrite !unsigned_lit by lia.
            pose proof (word_slot_at mc 4 MU ltac:(lia)) as H. change (Z.to_nat 4) with 4%nat in H.
            replace (bv_unsigned arr + 32) with (bv_unsigned arr + 8 * 4) by lia. exact H.
          - lia.
          - rewrite !unsigned_lit by lia. try unfold CALL_NARGS. rewrite L4 in NA. exact NA.
          - rewrite !unsigned_lit by lia. unfold outside_stack; try unfold CALL_NARGS. cbn [disjoint_from]. split; [lia | exact I].
          - intros _. rewrite !unsigned_lit by lia. exact P2.
          - intros _. rewrite !unsigned_lit by lia. exact P3.
          - reflexivity.
          - exact V2.
          - exact V3. }
        intros ms' (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & E & MU2 & WM2 & MI2 & ST2).
        subst ms'. rewrite unsigned_lit in MU2, ST2 by lia. fix_ret.
        zstep.
        apply evt_done. unfold at_bc4. do 25 eexists. split; [reflexivity|].
        exact (oinv_void mc m' Fc fc HI MU2 WM2 MI2 ST2).
Qed.

Lemma ro2 : forall m A u v, bytes_at rsegs m A (le4 u) -> bytes_at rsegs m (A + 4) (le4 v) ->
  ro_cells rsegs m A [C4 u; C4 v].
Proof.
  intros m A u v H1 H2. split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  apply bytes_at_app. split; [exact H1|]. rewrite length_le4. exact H2.
Qed.

Lemma rc_at : forall c cl mc, call_at_a mL lo (CW_GREC + 56 * c + 16) cl -> munch FW mL mc ->
  ro_cells rsegs mc (CW_GREC + 56 * c + 16)
    [C4 (Z_to_bv 64 (fst cl)); C4 (Z_to_bv 64 (Z.of_nat (length (snd cl))))].
Proof.
  intros c cl mc (A0 & A1 & A2 & A3 & _) MU. apply ro2.
  - eapply bytes_low; [exact A2 | exact MU | exact dFW | rewrite length_le4; lia].
  - eapply bytes_low; [exact A3 | exact MU | exact dFW | rewrite length_le4; lia].
Qed.

(* One call c: 0x14a28 (fields of calls[c]), the item loop when nargs > 0, the per-kind check, to 0x14bc4. *)
Lemma percall : forall c xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs10 xt3 xt4 xt5 xt6 Fc fc mc,
  0 <= c < Z.of_nat (length calls) -> oinv mc Fc fc ->
  evt rsegs (at_bc4 c) (OS 0x14a28 c xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs10 xt3 xt4 xt5 xt6 Fc fc mc).
Proof.
  intros c xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs10 xt3 xt4 xt5 xt6 Fc fc mc HC HI.
  assert (GREC : CW_GREC = 212296) by reflexivity.
  destruct (nth_error calls (Z.to_nat c)) as [cl|] eqn:Hc; [|apply nth_error_None in Hc; lia].
  assert (C16 : 0 <= c < 16) by lia.
  destruct (call_of c cl Hc ltac:(lia)) as [HA HK].
  pose proof HA as (A0 & A1 & A2 & A3 & A4 & A5 & A6).
  pose proof HI as (MI & MU & WM & ST & (jb & BUF) & FRM & FP).
  pose proof (rc_at c cl mc HA MU) as RC.
  zstep. zstep. zstep. zstep.
  match goal with |- context [Z_to_bv 64 (CW_GREC + ?e)] =>
    idtac "PERCALL_E" e;
    replace e with (56 * c)
      by (rewrite ?(unsigned_lit c) by lia; rewrite !Z.shiftl_mul_pow2 by lia;
          change (2 ^ 6) with 64; change (2 ^ 3) with 8; rewrite ?unsigned_lit by lia; rewrite ?Z.mod_small by lia; lia)
  end.
  zstep. zstep.
  rewrite (sx32_lit (Z.of_nat (length (snd cl)))) by lia. rewrite (sx32_lit (fst cl)) by lia.
  zstep. zstep. if_cases QZ.
  - eapply kinds; [exact Hc | lia | exact HI].
  - zc QZ.
    eapply evt_cut.
    { eapply (cw_items_loop SSP SCS ATOI SNP SC) with (m0 := mL) (lo := lo) (S := S) (r := r) (fn := fst cl)
        (nargs := Z.of_nat (length (snd cl))) (ws := ws) (W := W) (arr := arr) (lp := lp)
        (x8 := Z_to_bv 64 CW_GREC) (can := can) (jb := jb) (F := F)
        (s4 := Z_to_bv 64 (CW_GREC + 24 + 56 * c)) (s5 := Z_to_bv 64 (CW_GREC + 56 * c + 16)) (s9 := Z_to_bv 64 c).
      - lia.
      - exact IE.
      - lia.
      - exact RR.
      - lia.
      - exact A4.
      - exact FR0.
      - exact (rw_cells_c8_bytes _ _ _ GG).
      - exact (rw_cells_c8_bytes _ _ _ GU).
      - rewrite unsigned_lit by lia. exact A3.
      - rewrite unsigned_lit by lia. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
      - exact HWA.
      - cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
      - intros k Hk. pose proof (HWS k Hk) as Hl. split; [exact (lowp_ptr lo S mL _ _ _ Hl ltac:(lia))|].
        destruct Hl as (_ & _ & _ & _ & _ & HN & _). exact HN.
      - exact (proj1 HL).
      - exact (proj1 (proj2 HL)).
      - cbn [disjoint_from]. pose proof (proj2 (proj2 HL)). split; [lia|]. split; [lia | exact I].
      - intros a i Ha Hi y Hy.
        destruct HK as (K1 & _).
        assert (Ex : nth_error (snd cl) (Z.to_nat a) = Some (nth (Z.to_nat a) (snd cl) [])) by (apply nth_error_nth'; lia).
        pose proof (K1 _ _ _ Ex Hi y Hy) as Exy. rewrite <- Exy.
        destruct (A6 _ _ Ex) as (p & Hp). rewrite Z2Nat.id in Hp by lia. rewrite unsigned_lit by lia.
        replace (CW_GREC + 24 + 56 * c + 8 * a) with (CW_GREC + 56 * c + 16 + 8 + 8 * a) by lia.
        exact (lowp_ptr lo S mL _ _ _ Hp ltac:(lia)).
      - exact TMW.
      - exact MI.
      - exact MU.
      - exact WM.
      - exact ST.
      - exact BUF.
      - exact FRM.
      - exact FP. }
    intros ms' PO. unfold cw_items_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 &
                    y18 & y19 & y20 & Fc' & fc' & m' & jb' & E & MI2 & MU2 & WM2 & ST2 & BUF2 & FRM2 & FP2).
    subst ms'.
    pose proof (rc_at c cl m' HA MU2) as RC2.
    destruct (fr_at m' MU2 WM2) as (F0 & _).
    zstep. zstep.
    rewrite (sx32_lit (fst cl)) by lia.
    eapply kinds; [exact Hc | lia |].
    split; [exact MI2|]. split; [exact MU2|]. split; [exact WM2|]. split; [exact ST2|].
    split; [exists jb'; exact BUF2|]. split; [exact FRM2 | exact FP2].
Qed.

(* The loop over the recorded calls, 0x14a28 to free's entry. *)
Lemma oloop : forall n c xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs10 xt3 xt4 xt5 xt6 Fc fc mc,
  n = Z.to_nat (Z.of_nat (length calls) - c) -> 0 <= c < Z.of_nat (length calls) -> oinv mc Fc fc ->
  evt rsegs Qb (OS 0x14a28 c xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs10 xt3 xt4 xt5 xt6 Fc fc mc).
Proof.
  induction n as [|n IH];
    intros c xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs10 xt3 xt4 xt5 xt6 Fc fc mc HN HC HI;
    [lia|].
  assert (GREC : CW_GREC = 212296) by reflexivity.
  eapply evt_cut; [eapply percall; [exact HC | exact HI] |].
  intros ms' (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 &
              y18 & y19 & y20 & y21 & Fc' & fc' & m' & E & HI'). subst ms'.
  pose proof HI' as (MI' & MU' & WM' & _).
  pose proof (ncl_at m' MU') as NC.
  zstep.
  rewrite (sx32_lit (Z.of_nat (length calls))) by lia.
  zstep. zstep.
  replace (CW_GREC + 24 + 56 * c + 56) with (CW_GREC + 24 + 56 * (c + 1)) by lia.
  zstep. if_cases QL.
  - zc QL. rewrite ?signed_lit in QL by lia.
    eapply IH; [lia | lia | exact HI'].
  - eapply end_ok. exact HI'.
Qed.

(* The loop entry 0x14a28 with c = 0 (at least one recorded call). *)
Lemma loop_entry : forall xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs10 xt3 xt4 xt5 xt6 fc,
  mem_inv rsegs mL -> frm0 fc -> 0 < Z.of_nat (length calls) ->
  evt rsegs Qb (OS 0x14a28 0 xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs10 xt3 xt4 xt5 xt6 F fc mL).
Proof using SSP SCS ATOI SNP SC ADD CHAIN PIN LO IE SPH RR HOK NCL FR0 FR48 BUF0 FRH GG GU HNC HCA HWA HWB HWS HL TM STL.
  intros xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs10 xt3 xt4 xt5 xt6 fc MI FRM HC.
  eapply oloop; [reflexivity | lia |].
  split; [exact MI|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact STL|].
  split; [exists jb0; exact BUF0|]. split; [exact FRM | intros k _; reflexivity].
Qed.

End Body.

Lemma frame_wv : forall m S cs x, rw_cells rsegs m S cs -> ~ outside [(S, S + Z.of_nat (cells_size cs))] (bv_unsigned x) ->
  wview rsegs m x <> None.
Proof.
  intros m S cs x [_ (_ & _ & Hw)] Hx. cbn [outside] in Hx.
  pose proof (Hw (bv_unsigned x - S) ltac:(lia)) as H. unfold wa in H.
  replace (S + (bv_unsigned x - S)) with (bv_unsigned x) in H by lia. rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.

(* check_words from joined's return 0x149d8 (a0 = the line lp, s1 = r) to free's entry. *)
Theorem cw_body :
  strspn_contract -> strcspn_contract -> atoi_contract -> snprintf_contract -> strcmp_contract ->
  check_words_add_contract -> check_words_chain_contract -> check_words_pin_set_contract ->
  forall (gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o : word) (F : bvmap 5 word)
         (mJ : word -> option byte) (lo S r : Z) (ws : list (list byte)) (wpw : list word) (W arr lp can : word)
         (calls : list (Z * list (list byte))) (j0 j1 j2 j4 j5 j48 jb0 : list byte)
         (xra xt0 xt1 xt2 xs0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word)
         (fc : bv 32),
  lo + 8272 <= S -> 0x54cb8 <= lo -> S + 176 < 2 ^ 63 -> 0 <= r <= 64 ->
  Forall (call_words_ok r ws) calls -> (length calls <= 16)%nat ->
  rw_cells rsegs mJ S [CB 8 j0; CB 8 j1; CB 8 j2; C8 W; CB 8 j4; CB 8 j5] ->
  rw_cells rsegs mJ (S + 48) [CB 8 j48] -> rw_cells rsegs mJ (S + 56) [CB 16 jb0] ->
  rw_cells rsegs mJ (S + 72)
    [C8 s11o; C8 s10o; C8 s9o; C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  rw_cells rsegs mJ 0x22a68 [C8 (Z_to_bv 64 0x54450)] -> rw_cells rsegs mJ 0x54450 [C8 can] ->
  bytes_at rsegs mJ 0x22a20 (le8 (Z_to_bv 64 CW_GREC)) ->
  bytes_at rsegs mJ (CW_GREC + 8) (le4 (Z_to_bv 64 (Z.of_nat (length calls)))) ->
  (forall i c, nth_error calls i = Some c -> call_at_a mJ lo (CW_GREC + 16 + 56 * Z.of_nat i) c) ->
  bytes_at rsegs mJ (bv_unsigned W + 16) (le8 arr) -> S + 176 <= bv_unsigned W + 16 ->
  (forall k, 0 <= k < r ->
     lowp lo mJ (bv_unsigned arr + 8 * k) (nth (Z.to_nat k) wpw (Z_to_bv 64 0)) (nth (Z.to_nat k) ws [])) ->
  bytes_at rsegs mJ (bv_unsigned lp) (RecFacts.join_sp ws ++ [NUL]) -> ~ In NUL (RecFacts.join_sp ws) ->
  bv_unsigned lp + Z.of_nat (length (RecFacts.join_sp ws)) + 1 <= lo ->
  MemNorm.task_mem rsegs mJ -> stk rsegs mJ lo S -> mem_inv rsegs mJ -> frm0 fc ->
  evt rsegs (cw_body_post gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o F lo (S + 176) lp mJ)
    (MS (mkR xra (Z_to_bv 64 S) gp tp xt0 xt1 xt2 xs0 (Z_to_bv 64 r) lp xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 0x149d8) fc None mJ (seg_rom rsegs)).
Proof.
  intros SSP SCS ATOI SNP SC ADD CHAIN PIN gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o F
    mJ lo S r ws wpw W arr lp can calls j0 j1 j2 j4 j5 j48 jb0
    xra xt0 xt1 xt2 xs0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 fc
    LO IE SPH RR HOK NCL FR FR48 BUF0 FRH GG GU GOT HNC HCA HWA HWB HWS HL1 HL2 HL3 TM ST MI FRM.
  assert (GREC : CW_GREC = 212296) by reflexivity.
  pose proof (munch_refl [(S, S + 48)] mJ) as MU.
  pose proof (wmono_refl rsegs mJ) as WM.
  assert (D48 : disjoint_from [(S, S + 48)] 0 lo) by (cbn [disjoint_from]; split; [lia | exact I]).
  assert (WV48 : forall x : word, ~ outside [(S, S + 48)] (bv_unsigned x) -> wview rsegs mJ x <> None)
    by (intros x Hx; exact (frame_wv mJ S _ x FR Hx)).
  pose proof (bytes_ro8 _ _ _ GOT) as RGOT.
  pose proof (bytes_ro4 _ _ _ HNC) as RNC.
  zstep. zstep. zstep. zstep.
  rewrite (sx32_lit (Z.of_nat (length calls))) by lia.
  zstep. if_cases QN.
  - zify_cond QN. rewrite ?signed_lit in QN by lia.
    eapply (cw_tail gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o F lo S lp mJ
              [CB 8 j0; CB 8 j1; CB 8 j2; C8 W; CB 8 j4]);
      [lia | lia | reflexivity | eassumption | | eassumption | eassumption | exact FRM | intros k _; reflexivity
      | eassumption | eassumption | eassumption | eassumption].
    eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. lia.
  - zify_cond QN.
    repeat match goal with H : context [bv_signed (Z_to_bv 64 (Z.of_nat (length calls)))] |- _ =>
      rewrite signed_lit in H by lia end.
    do 15 zstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => set (mS := m1) in * end.
    clearbody mS.
    eapply evt_mono.
    { eapply (loop_entry gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o F mS lo S r ws wpw W arr lp can
                calls j48 jb0 SSP SCS ATOI SNP SC ADD CHAIN PIN LO IE SPH RR HOK NCL).
      - exact FR.
      - exact FR48.
      - exact BUF0.
      - exact FRH.
      - exact GG.
      - exact GU.
      - exact HNC.
      - intros i c E. exact (call_tp _ mJ mS lo _ c (HCA i c E) MU D48).
      - exact HWA.
      - exact HWB.
      - intros k Hk. exact (lowp_tp _ mJ mS lo _ _ _ (HWS k Hk) MU D48).
      - split; [exact HL1 | split; [exact HL2 | exact HL3]].
      - exact (task_mem_fw _ mJ mS TM WV48 MU).
      - exact ST.
      - exact MI.
      - exact FRM.
      - lia. }
    intros ms' Hq. unfold Qb, cw_body_post in Hq |- *.
    destruct Hq as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & Fq & fq & mq
      & E & MIq & MUq & WMq & STq & FRMq & FPq).
    exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, Fq, fq, mq.
    split; [exact E|]. split; [exact MIq|]. split.
    { apply (munch_trans _ mJ mS mq); [|exact MUq].
      eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    split; [exact (wmono_trans rsegs _ _ _ WM WMq)|]. split; [exact STq|]. split; [exact FRMq | exact FPq].
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL01 YL00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI06.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecModel RecInv RecInvP RecKindB RecAnsB
  RecAns joined_c.

Lemma cw_mbyte_mrd : forall segs m a, mbyte segs m a = mrd segs m (wa a).
Proof. reflexivity. Qed.

Lemma cw_hi_present : forall m a, 2 ^ 20 <= a < 2 ^ 64 -> mbyte rsegs m a <> None -> present m a.
Proof.
  intros m a Ha H. unfold mbyte, mrd, wa, present in *. destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [exists b; reflexivity|].
  exfalso. apply H. apply MemNorm.seg_rom_unmapped. rewrite unsigned_lit by lia.
  apply (find_segment_none_above rsegs (2 ^ 20) a 1 rsegs_top); lia.
Qed.

Lemma cw_ro_low : forall x, ro_addr rsegs x = true -> bv_unsigned x < 2 ^ 20.
Proof.
  intros x Hx. destruct (Z_lt_ge_dec (bv_unsigned x) (2 ^ 20)) as [H|H]; [exact H|].
  pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn in R.
  rewrite <- (Z_to_bv_bv_unsigned x) in Hx. rewrite ro_addr_hi in Hx by lia. discriminate.
Qed.

Lemma cw_ro_munch : forall W m m', MemNorm.ro_agree rsegs m -> munch W m m' ->
  (forall x, 0 <= x < 2 ^ 20 -> outside W x) -> MemNorm.ro_agree rsegs m'.
Proof.
  intros W m m' H HM HW x Hx. unfold mrd. rewrite (HM x); [exact (H x Hx)|].
  pose proof (cw_ro_low x Hx). pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn in R.
  apply HW. lia.
Qed.

Lemma cw_bytes_of_le : forall (B : malloc_syms) m a bs, ms_segs B = rsegs -> 0 <= a ->
  a + Z.of_nat (length bs) <= 2 ^ 64 -> VerbsB.le_at B m a bs -> bytes_at rsegs m a bs.
Proof.
  intros B0 m a bs HS H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold VerbsB.le_at, blk_data in H. cbv zeta in H. rewrite HS in H.
  pose proof (H (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. exact E.
Qed.

Lemma cw_le_of_bytes : forall (B : malloc_syms) m a bs, ms_segs B = rsegs -> bytes_at rsegs m a bs ->
  VerbsB.le_at B m a bs.
Proof.
  intros B0 m a bs HS (H0 & H1 & H2). unfold VerbsB.le_at, blk_data. cbv zeta. rewrite HS. intros i Hi.
  replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia.
  rewrite cw_mbyte_mrd. apply H2. lia.
Qed.

Lemma cw_le_keep : forall (B : malloc_syms) m m' a bs, VerbsB.le_at B m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte (ms_segs B) m' (a + i) = mbyte (ms_segs B) m (a + i)) ->
  VerbsB.le_at B m' a bs.
Proof.
  intros B0 m m' a bs H K. unfold VerbsB.le_at, blk_data in *. cbv zeta in *. intros i Hi.
  rewrite K by exact Hi. exact (H i Hi).
Qed.

Lemma cw_wv_keep : forall (B : malloc_syms) (L : layout) (A : astate) m m' W arr wp ws,
  words_view B m W arr wp ws -> words_place L A m arr wp ws ->
  (forall i, 0 <= i < 12 -> mbyte (ms_segs B) m' (W + 16 + i) = mbyte (ms_segs B) m (W + 16 + i)) ->
  (forall q k i, In (q, k) (blocks L A) -> 0 <= i < k -> mbyte (ms_segs B) m' (q + i) = mbyte (ms_segs B) m (q + i)) ->
  words_view B m' W arr wp ws.
Proof.
  intros B0 L A m m' W arr wp ws (WL & WN & W24 & W16 & WK) (PA & PK) K1 K2.
  split; [exact WL|]. split; [exact WN|].
  split.
  { apply (cw_le_keep B0 m); [exact W24|]. intros i Hi. rewrite Mem.length_le4 in Hi.
    replace (W + 24 + i) with (W + 16 + (8 + i)) by ring. apply K1. lia. }
  split.
  { apply (cw_le_keep B0 m); [exact W16|]. intros i Hi. rewrite Mem.length_le8 in Hi. apply K1. lia. }
  intros k Hk. destruct (WK k Hk) as [Hp [Hn Hs]]. split; [|split; [exact Hn|]].
  - apply (cw_le_keep B0 m); [exact Hp|]. intros i Hi. rewrite Mem.length_le8 in Hi.
    destruct PA as (q & n & Hq & H1 & H2).
    replace (arr + 8 * Z.of_nat k + i) with (q + (arr + 8 * Z.of_nat k + i - q)) by ring.
    apply (K2 q n); [exact Hq | lia].
  - apply (cw_le_keep B0 m); [exact Hs|]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    destruct (PK k Hk) as (q & n & Hq & H1 & H2).
    replace (nth k wp 0 + i) with (q + (nth k wp 0 + i - q)) by ring.
    apply (K2 q n); [exact Hq | lia].
Qed.

Lemma cw_join_no0 : forall ws, (forall w, In w ws -> ~ In NUL w) -> ~ In NUL (RecFacts.join_sp ws).
Proof.
  induction ws as [|w ws IH]; intros H.
  - cbn. intros [].
  - destruct ws as [|w2 ws'].
    + cbn [RecFacts.join_sp]. apply H. left. reflexivity.
    + change (RecFacts.join_sp (w :: w2 :: ws')) with (w ++ RecFacts.SPACE :: RecFacts.join_sp (w2 :: ws')).
      intros Hin. apply in_app_or in Hin as [Hin|[Hin|Hin]].
      * exact (H w (or_introl eq_refl) Hin).
      * unfold RecFacts.SPACE, NUL in Hin. apply (f_equal bv_unsigned) in Hin. vm_compute in Hin. discriminate.
      * exact (IH (fun w' Hw' => H w' (or_intror Hw')) Hin).
Qed.

Lemma cw_join_len : forall ws, Z.of_nat (length (RecFacts.join_sp ws)) <= join_need ws.
Proof.
  induction ws as [|w ws IH]; [cbn; lia|].
  destruct ws as [|w2 ws'].
  - cbn [RecFacts.join_sp]. unfold join_need. cbn [fold_right]. lia.
  - change (RecFacts.join_sp (w :: w2 :: ws')) with (w ++ RecFacts.SPACE :: RecFacts.join_sp (w2 :: ws')).
    rewrite length_app. cbn [length].
    change (join_need (w :: w2 :: ws')) with (Z.of_nat (length w) + 1 + join_need (w2 :: ws')). lia.
Qed.

Lemma cw_cells_bytes_app : forall l1 l2, cells_bytes (l1 ++ l2) = cells_bytes l1 ++ cells_bytes l2.
Proof.
  induction l1 as [|c l1 IH]; intros l2; cbn [app cells_bytes]; [reflexivity|].
  rewrite IH, app_assoc. reflexivity.
Qed.

Lemma cw_cells_wf_app : forall l1 l2, cells_wf (l1 ++ l2) -> cells_wf l1 /\ cells_wf l2.
Proof.
  induction l1 as [|c l1 IH]; intros l2 H; [split; [exact I | exact H]|].
  destruct H as [H1 H2]. destruct (IH l2 H2) as [H3 H4]. split; [split; [exact H1 | exact H3] | exact H4].
Qed.

Lemma cw_rw_sub : forall m X Y pre mid post, rw_cells rsegs m X (pre ++ mid ++ post) ->
  Y = X + Z.of_nat (cells_size pre) -> rw_cells rsegs m Y mid.
Proof.
  intros m X Y pre mid post [[Hwf Hb] (Hw0 & Hw1 & Hw)] ->.
  destruct (cw_cells_wf_app _ _ Hwf) as [Wp Wmp]. destruct (cw_cells_wf_app _ _ Wmp) as [Wm _].
  rewrite !cw_cells_bytes_app in Hb.
  apply bytes_at_app in Hb as [_ Hb]. apply bytes_at_app in Hb as [Hb _].
  rewrite (cells_bytes_length pre Wp) in Hb.
  rewrite !cells_size_app in Hw1, Hw.
  split; [split; [exact Wm | exact Hb]|].
  split; [lia|]. split; [lia|]. intros i Hi.
  replace (X + Z.of_nat (cells_size pre) + i) with (X + (Z.of_nat (cells_size pre) + i)) by ring.
  apply Hw. lia.
Qed.

Lemma cw_rw_move : forall m m' X cs, rw_cells rsegs m X cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> mbyte rsegs m' (X + i) = mbyte rsegs m (X + i) /\
     writable_at rsegs m' (X + i)) -> rw_cells rsegs m' X cs.
Proof.
  intros m m' X cs H K. apply (rw_cells_transfer rsegs m m' X cs H).
  intros i Hi. destruct (K i Hi) as [E Wr]. split; [exact E | intros _; exact Wr].
Qed.

Lemma cw_rw_bytes : forall m X cs, cells_wf cs -> bytes_at rsegs m X (cells_bytes cs) ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> writable_at rsegs m (X + i)) -> rw_cells rsegs m X cs.
Proof.
  intros m X cs Hwf Hb Hw. pose proof Hb as (H0 & H1 & _). rewrite (cells_bytes_length cs Hwf) in H1.
  split; [split; [exact Hwf | exact Hb]|]. split; [exact H0|]. split; [exact H1|].
  intros i Hi. exact (Hw i Hi).
Qed.

Lemma cw_mbyte_norm : forall m a, MemNorm.ro_agree rsegs m -> 0 <= a < TASK_SIZE ->
  mbyte rsegs (MemNorm.normalize_cj rsegs m) a = mbyte rsegs m a.
Proof.
  intros m a RO Ha. unfold TASK_SIZE in Ha. rewrite !cw_mbyte_mrd.
  apply (MemNorm.mrd_normalize_cj rsegs m (wa a) RO).
  right. right. unfold wa. rewrite unsigned_lit by lia. unfold TASK_SIZE. lia.
Qed.

Lemma cw_wr_norm : forall m a, MemNorm.ro_agree rsegs m -> 2 ^ 20 <= a < TASK_SIZE -> writable_at rsegs m a ->
  writable_at rsegs (MemNorm.normalize_cj rsegs m) a.
Proof.
  intros m a RO Ha H. unfold TASK_SIZE in Ha. unfold writable_at in *.
  rewrite (MemNorm.wview_rel_cj rsegs m (MemNorm.normalize_cj rsegs m) (Z_to_bv 64 a)
    (MemNorm.mem_rel_cj_normalize rsegs m RO)); [exact H|].
  apply MemNorm.cj_drop_false_intro; [apply ro_addr_hi; lia|].
  right. rewrite unsigned_lit by lia. unfold TASK_SIZE. lia.
Qed.

Lemma cw_mid_eq : forall {X : Type} (l1 l2 l3 l4 : list X) x, l1 ++ x :: l2 = l3 ++ x :: l4 ->
  ~ In x l1 -> ~ In x l3 -> l1 ++ l2 = l3 ++ l4.
Proof.
  intros X l1. induction l1 as [|y l1 IH]; intros l2 l3 l4 x E N1 N3.
  - destruct l3 as [|z l3]; cbn in E |- *.
    + injection E as E. exact E.
    + injection E as E1 E2. exfalso. apply N3. left. symmetry. exact E1.
  - destruct l3 as [|z l3]; cbn in E |- *.
    + injection E as E1 E2. exfalso. apply N1. left. exact E1.
    + injection E as E1 E2. subst z. f_equal.
      apply (IH l2 l3 l4 x E2); [intro H; apply N1; right; exact H | intro H; apply N3; right; exact H].
Qed.

Lemma cw_lle_trans : forall A A' L1 L2 L3, layout_le A L1 L2 -> layout_le A' L2 L3 ->
  (length (st_regions A) <= length (st_regions A'))%nat -> layout_le A L1 L3.
Proof.
  intros A A' L1 L2 L3 (H1 & H2 & H3 & H4) (G1 & G2 & G3 & G4) HL.
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  intros r Hr. rewrite (G4 r ltac:(lia)). exact (H4 r Hr).
Qed.

Lemma cw_bytes_of_image : forall segs m n A bs, image_bytes segs A n = Some bs ->
  (forall i, 0 <= i < Z.of_nat n -> mbyte segs m (A + i) = seg_rom segs (Z_to_bv 64 (A + i))) ->
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 -> bytes_at segs m A bs.
Proof.
  intros segs m n. induction n as [|n IH]; intros A bs HI HM H0 H1; cbn [image_bytes] in HI.
  - injection HI as <-. split; [exact H0|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (PropExec.seg_rom segs (wa A)) as [b0|] eqn:E0; [|discriminate].
    destruct (image_bytes segs (A + 1) n) as [bs'|] eqn:E1; [|discriminate].
    injection HI as <-.
    change (b0 :: bs') with ([b0] ++ bs'). apply bytes_at_app. split.
    + split; [exact H0|]. split; [cbn; lia|]. intros i Hi. cbn [length] in Hi.
      destruct i as [|i]; [|lia]. cbn [nth_error].
      replace (A + Z.of_nat 0) with A by lia. rewrite <- cw_mbyte_mrd.
      pose proof (HM 0 ltac:(lia)) as H. rewrite Z.add_0_r in H. rewrite H. exact E0.
    + replace (A + Z.of_nat (length [b0])) with (A + 1) by (cbn; lia).
      apply IH; [exact E1 | | lia | lia]. intros i Hi.
      replace (A + 1 + i) with (A + (1 + i)) by lia. apply HM. lia.
Qed.

Lemma cw_image_nth : forall segs n A bs i, image_bytes segs A n = Some bs -> (i < n)%nat ->
  PropExec.seg_rom segs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  intros segs n. induction n as [|n IH]; intros A bs i HI Hi; [lia|].
  cbn [image_bytes] in HI.
  destruct (PropExec.seg_rom segs (wa A)) as [b0|] eqn:E0; [|discriminate].
  destruct (image_bytes segs (A + 1) n) as [bs'|] eqn:E1; [|discriminate].
  injection HI as <-.
  destruct i as [|i]; cbn [nth_error].
  - rewrite Z.add_0_r. exact E0.
  - replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply IH; [exact E1 | lia].
Qed.

Lemma cw_img_res : forall (B : malloc_syms) k lo sz a, ms_segs B = rsegs ->
  nth_error (map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s))) (segments_reserved rsegs)) k = Some (lo, sz) ->
  lo <= a < lo + sz -> in_img B a.
Proof.
  intros B0 k lo sz a HS E Ha. unfold in_img. rewrite HS. split.
  - assert (L : length rsegs = 4%nat) by (vm_compute; reflexivity).
    intros H. rewrite H in L. discriminate.
  - rewrite nth_error_map in E. destruct (nth_error (segments_reserved rsegs) k) as [s|] eqn:E2; [|discriminate].
    cbv beta iota delta [option_map] in E. injection E as E3 E4.
    exists s. split; [exact (nth_error_In _ _ E2) | lia].
Qed.

Lemma cw_img_iv : forall (B : malloc_syms) a, ms_segs B = rsegs -> 0x10000 <= a < 0x55000 -> in_img B a.
Proof.
  intros B0 a HS Ha.
  destruct (Z_lt_ge_dec a 0x13000).
  { apply (cw_img_res B0 0 0x10000 0x3000); [exact HS | vm_compute; reflexivity | lia]. }
  destruct (Z_lt_ge_dec a 0x22000).
  { apply (cw_img_res B0 1 0x13000 0xF000); [exact HS | vm_compute; reflexivity | lia]. }
  destruct (Z_lt_ge_dec a 0x23000).
  { apply (cw_img_res B0 2 0x22000 0x1000); [exact HS | vm_compute; reflexivity | lia]. }
  apply (cw_img_res B0 3 0x23000 0x32000); [exact HS | vm_compute; reflexivity | lia].
Qed.

Lemma cw_relro_iv : forall a, in_globals frame_RELRO a -> 0x224a8 <= a < 0x23000.
Proof. intros a (lo & len & Hin & Hb). unfold frame_RELRO in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; lia. Qed.

Lemma cw_relro_of : forall a, 0x224a8 <= a < 0x22a68 -> in_globals frame_RELRO a.
Proof. intros a Ha. exists 140456, 1472. split; [left; reflexivity | lia]. Qed.

Lemma cw_g_iv : forall a, in_globals frame_G a -> 0x33d10 <= a < 0x3410c.
Proof. intros a (lo & len & Hin & Hb). unfold frame_G in Hin. destruct Hin as [E|[]]. injection E as <- <-. lia. Qed.

Lemma cw_g_of : forall a, 0x33d10 <= a < 0x3410c -> in_globals frame_G a.
Proof. intros a Ha. exists 212240, 1020. split; [left; reflexivity | lia]. Qed.

Lemma cw_got_rom_img : image_bytes rsegs 0x22a68 8 = Some (Mem.le8 (Z_to_bv 64 0x54450)).
Proof. vm_compute. repeat first [ reflexivity | apply bv_eq; reflexivity | f_equal ]. Qed.

Lemma cw_grec_img : image_bytes rsegs 0x22a20 8 = Some (Mem.le8 (Z_to_bv 64 CW_GREC)).
Proof. unfold CW_GREC. vm_compute. repeat first [ reflexivity | apply bv_eq; reflexivity | f_equal ]. Qed.

Lemma cw_got_rom : forall m a, word_mem rsegs m 0x22a68 0x54450 -> 0x22a68 <= a < 0x22a70 ->
  mbyte rsegs m a = seg_rom rsegs (Z_to_bv 64 a).
Proof.
  intros m a W Ha.
  pose proof (KindBGlue.word_mem_le8 rsegs m 0x22a68 0x54450 W ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & H).
  rewrite Mem.length_le8 in H.
  assert (Ei : a = 0x22a68 + Z.of_nat (Z.to_nat (a - 0x22a68))) by lia.
  rewrite Ei, cw_mbyte_mrd. rewrite (H (Z.to_nat (a - 0x22a68)) ltac:(lia)).
  symmetry. exact (cw_image_nth rsegs 8 _ _ (Z.to_nat (a - 0x22a68)) cw_got_rom_img ltac:(lia)).
Qed.

Lemma cw_guard_wr : forall m i, 0 <= i < 8 -> writable_at rsegs m (0x54450 + i).
Proof.
  intros m i Hi.
  assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  repeat (destruct C as [C|C];
    [subst i; unfold writable_at, wview; destruct (m _); [discriminate | vm_compute; discriminate]|]).
  subst i; unfold writable_at, wview; destruct (m _); [discriminate | vm_compute; discriminate].
Qed.

Lemma cw_call_a : forall bl m mJ lo a c P,
  call_at rsegs bl m a c P ->
  (forall pn, In pn bl -> 4096 <= fst pn /\ fst pn + snd pn <= lo) ->
  0 <= a -> a + 56 <= lo -> lo <= 2 ^ 64 ->
  (forall x, a <= x < a + 56 -> mbyte rsegs mJ x = mbyte rsegs m x) ->
  (forall pn x, In pn bl -> fst pn <= x < fst pn + snd pn -> mbyte rsegs mJ x = mbyte rsegs m x) ->
  call_at_a mJ lo a c.
Proof.
  intros bl m mJ lo a c P (C0 & C1 & C2 & C3 & C4 & _ & C6) HB A0 A1 ALo KA KB.
  unfold CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *. rewrite Z.add_0_r in C3.
  split; [exact A0|]. split; [exact A1|].
  split; [apply (bytes_at_transfer rsegs m); [exact C3 | intros i Hi; rewrite Mem.length_le4 in Hi; apply KA; lia]|].
  split; [apply (bytes_at_transfer rsegs m); [exact C4 | intros i Hi; rewrite Mem.length_le4 in Hi; apply KA; lia]|].
  split; [unfold RecFacts.REC_FN_COUNT in C0; lia|]. split; [exact C1|].
  intros k s Hs.
  assert (Hk : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Hs; discriminate).
  destruct (nth_error P k) as [pn|] eqn:Hp; [|apply nth_error_None in Hp; lia].
  destruct (C6 k s pn Hs Hp) as (D0 & D1 & D2 & D3 & D4 & D5).
  destruct (HB pn D2) as [B0 B1].
  exists (Z_to_bv 64 (fst pn)).
  assert (U : bv_unsigned (Z_to_bv 64 (fst pn)) = fst pn) by (apply unsigned_lit; lia).
  unfold lowp. rewrite U.
  split; [apply (bytes_at_transfer rsegs m); [exact D0 | intros i Hi; rewrite Mem.length_le8 in Hi; apply KA; lia]|].
  split; [lia|]. split; [lia|]. split; [lia|].
  split.
  { apply (bytes_at_transfer rsegs m); [exact D4|]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    apply (KB pn); [exact D2 | lia]. }
  split; [exact D5 | lia].
Qed.

Lemma cw_word_low : forall (B : malloc_syms) m lo (W arr : Z) wp ws k, ms_segs B = rsegs ->
  words_view B m W arr wp ws -> 0 <= arr -> arr + 8 * Z.of_nat (length ws) <= lo -> lo <= 2 ^ 64 ->
  (forall j, (j < length ws)%nat -> 1 <= nth j wp 0 /\ nth j wp 0 + Z.of_nat (length (nth j ws [])) + 1 <= lo) ->
  0 <= k < Z.of_nat (length ws) ->
  lowp lo m (bv_unsigned (Z_to_bv 64 arr) + 8 * k) (nth (Z.to_nat k) (map (Z_to_bv 64) wp) (Z_to_bv 64 0))
    (nth (Z.to_nat k) ws []).
Proof.
  intros B0 m lo W arr wp ws k HS (WL & WN & _ & _ & WK) A0 A1 HL HP Hk.
  assert (Hk' : (Z.to_nat k < length ws)%nat) by lia.
  destruct (WK (Z.to_nat k) Hk') as (E1 & E2 & E3).
  destruct (HP (Z.to_nat k) Hk') as [P0 P1].
  rewrite (map_nth (Z_to_bv 64) wp 0 (Z.to_nat k)).
  assert (UA : bv_unsigned (Z_to_bv 64 arr) = arr) by (apply unsigned_lit; lia).
  assert (UP : bv_unsigned (Z_to_bv 64 (nth (Z.to_nat k) wp 0)) = nth (Z.to_nat k) wp 0) by (apply unsigned_lit; lia).
  rewrite Z2Nat.id in E1 by lia.
  unfold lowp. rewrite UA, UP.
  split; [apply (cw_bytes_of_le B0 m _ _ HS); [lia | rewrite Mem.length_le8; lia | exact E1]|].
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [apply (cw_bytes_of_le B0 m _ _ HS); [lia | rewrite length_app; cbn [length]; lia | exact E3]|].
  split; [exact E2 | lia].
Qed.

Section CW.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis FREE_PC : ms_free B = 0x188cc.
Hypothesis TP_AT : ms_tp B = 0x341e0.
Hypothesis ERRNO_OFF : ms_errno_off B = -164.
Hypothesis GUARD_AT : ms_guard B = 0x54450.
Hypothesis GOT_AT : ms_got_guard B = 0x22a68.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTXO : ctx_owned B API.
Hypothesis G_STAT : forall a, in_globals frame_G a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RELRO_FREE : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_RELRO a ->
  ~ (ms_got_guard B <= a < ms_got_guard B + 8) -> ~ owned B L A a /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis HJOIN : joined_contract B API.
Hypothesis SSP : strspn_contract.
Hypothesis SCS : strcspn_contract.
Hypothesis ATOI : atoi_contract.
Hypothesis SNP : snprintf_contract.
Hypothesis SC : strcmp_contract.
Hypothesis ADD : check_words_add_contract.
Hypothesis CHAIN : check_words_chain_contract.
Hypothesis PIN : check_words_pin_set_contract.

Lemma cw_gnown : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Proof using AX G_STAT.
  intros L A mem md a HM Hg Ho. destruct (G_STAT a Hg) as (Hi & Hs & Hc & _).
  destruct Ho as [Hal|Hst]; [exact (Hc (ax_img AX L A mem md a HM Hi Hal)) | exact (Hs Hst)].
Qed.

Theorem check_words_holds : check_words_contract B API.
Proof using SEGS FREE_PC TP_AT ERRNO_OFF GUARD_AT GOT_AT AX CTXO G_STAT RELRO_FREE FREE HJOIN SSP SCS ATOI SNP SC
  ADD CHAIN PIN.
  unfold check_words_contract.
  intros L A regs mem md b W arr q wp ws R O _ PRE SPT CMD FRM QUIT0 QOUT A10 WV WP SPW WT JN REP NOWN RES ROOM WPR.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC. pose proof alloc_ceiling_lt as AC2.
  pose proof wx_apart_rsegs as WX.
  assert (EA : errno_addr B = 0x3413c) by (unfold errno_addr; rewrite TP_AT, ERRNO_OFF; reflexivity).
  assert (KV : CHECK_WORDS_K = 8448) by reflexivity.
  pose proof PRE as PRE0.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  rewrite KV in HCEIL, HWS.
  pose proof CMD as (RO & GIMG & _ & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold TASK_SIZE in SPT, WT.
  rewrite SEGS in HWS, HERR, RO, REP.
  assert (GIM : forall a, in_globals frame_RELRO a -> mbyte rsegs mem a = seg_rom rsegs (Z_to_bv 64 a)).
  { intros a Ha. rewrite <- SEGS. exact (GIMG a Ha). }
  pose proof WV as (WL & WN & W24 & W16 & WK).
  pose proof WP as ((pa & ka & Hpa & Hpa1 & Hpa2) & WPK).
  assert (NOH : forall a, alloc_ceiling <= a -> ~ owned B L A a).
  { intros a Ha Ho. destruct (mr_owned_low B _ LAWS _ _ _ _ _ HMR Ho). lia. }
  assert (NEH : forall a, alloc_ceiling <= a -> ~ (errno_addr B <= a < errno_addr B + 4)) by (intros a Ha; rewrite EA; lia).
  assert (BRNG : forall q0 k, In (q0, k) (blocks L A) -> 4096 <= q0 /\ q0 + k <= alloc_ceiling).
  { intros q0 k Hq. apply YI06.blocks_In in Hq as (p & <- & Hp). exact (mr_blocks_range B _ LAWS L A mem md p k HMR Hp). }
  pose proof (BRNG pa ka Hpa) as BPA.
  assert (ST : stk rsegs mem (bv_unsigned sp - 8448) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (Wa : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact Wa|].
    destruct (writable_hi_present mem a ltac:(lia) Wa) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    assert (R10 : reg_get regs 10 = Z_to_bv 64 W) by exact A10. rewrite R10. unfold CHECK_WORDS.
    eapply cw_run1 with (lo := bv_unsigned sp - 8448) (n := Z.of_nat (length ws));
      [exact ST | lia | lia | lia | lia | lia |].
    apply (cw_bytes_of_le B mem _ _ SEGS); [lia | rewrite Mem.length_le4; lia | exact W24]. }
  intros ms1 (can1 & Q1 & EQ1). unfold cw_mid1 in Q1.
  destruct Q1 as (u0 & u1 & u2 & a1v & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m1 & j0 & j1 & j2 & j4 & j5
    & j6 & j7 & -> & EA1 & MU1 & WM1 & FR1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x149d8) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp + -176))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_9 : getr R1 9 = Z_to_bv 64 (Z.min (Z.of_nat (length ws)) 64))
    by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 W) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_11 : getr R1 11 = Z_to_bv 64 (bv_unsigned sp + -128))
    by (rewrite (getr_of_eqv _ _ 11 X1 eq_refl); simp_regs; exact EA1).
  assert (K1 : forall r, callee_saved r -> r <> 2 -> r <> 9 -> getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr H2 H9. unfold callee_saved in Hr.
    assert (C : r = 3 \/ r = 4 \/ r = 8 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/
                r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct C as [C|C]; [subst r; rewrite (getr_of_eqv _ _ _ X1) by reflexivity; reflexivity|]).
    subst r; rewrite (getr_of_eqv _ _ _ X1) by reflexivity; reflexivity. }
  assert (SP1 : spZ R1 = bv_unsigned sp - 176) by (unfold spZ; rewrite E1_2; rewrite unsigned_lit by lia; lia).
  assert (RO1 : MemNorm.ro_agree rsegs m1).
  { apply (cw_ro_munch _ mem m1 RO MU1). intros x Hx. cbn. split; [lia | exact I]. }
  assert (WR1 : forall a, bv_unsigned sp - 8448 <= a < bv_unsigned sp -> writable_at rsegs m1 a).
  { intros a Ha. unfold writable_at. apply WM1. apply HWS. lia. }
  assert (PRE1 : call_pre_k B (aa_MR API) (ALLOC_STACK + JOINED_FRAME) L A R1 m1 md).
  { pose proof (KindBGlue.kb_pre_A B API CHECK_WORDS_K 176 (ALLOC_STACK + JOINED_FRAME) L A regs mem md R1 m1
      [(bv_unsigned sp + -176, bv_unsigned sp)] PRE0) as KPA.
    rewrite SEGS in KPA. change ALLOC_STACK with 8192 in *. unfold JOINED_FRAME in *. rewrite KV in KPA.
    apply KPA; clear KPA.
    - lia.
    - lia.
    - lia.
    - rewrite SP1. change (spZ regs) with (bv_unsigned sp). lia.
    - rewrite SP1. replace (bv_unsigned sp - 176) with (bv_unsigned sp + (-11) * 16) by ring.
      rewrite Z.mod_add by lia. exact HAL.
    - exact E1_4.
    - rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
    - exact MU1.
    - exact WM1.
    - intros x Hx Hs. change (spZ regs) with (bv_unsigned sp) in Hs. cbn. split; [lia | exact I].
    - intros x Hx _. cbn. split; [lia | exact I]. }
  pose proof HJOIN as JN0. unfold joined_contract, JOINED in JN0. rewrite SEGS in JN0.
  eapply SR_bind.
  { apply (JN0 L A R1 m1 md b W arr (bv_unsigned sp + -128) wp ws); clear JN0.
    - exact PRE1.
    - exact RO1.
    - exact E1_10.
    - exact E1_11.
    - apply (cw_wv_keep B L A mem m1 W arr wp ws WV WP).
      + intros i Hi. rewrite SEGS. apply (munch_mbyte _ _ _ _ _ MU1); [lia | cbn; split; [lia | exact I]].
      + intros p k i Hin Hi. rewrite SEGS. pose proof (BRNG p k Hin).
        apply (munch_mbyte _ _ _ _ _ MU1); [lia | cbn; split; [lia | exact I]].
    - exact WP.
    - rewrite SP1. lia.
    - lia.
    - exact JN.
    - rewrite SP1. lia.
    - lia.
    - left. lia.
    - intros i Hi. apply WR1. lia.
    - replace (bv_unsigned sp + -128) with (bv_unsigned sp mod 16 + 8 * (2 * (bv_unsigned sp / 16) - 16)) by
        (pose proof (Z.div_mod (bv_unsigned sp) 16 ltac:(lia)); lia).
      rewrite HAL, Z.add_0_l, Z.mul_comm. apply Z.mod_mul. lia.
    - intros i Hi. split.
      + apply NOH. lia.
      + unfold scratch_k, JOINED_FRAME. change ALLOC_STACK with 8192. rewrite SP1.
        intros [H|H]; [lia | rewrite EA in H; lia].
    - exact RES.
    - exact ROOM. }
  intros c2 RET.
  destruct RET as (L1 & A1 & R2 & m2 & md1 & res & -> & POST & A0' & NZ & FRESH & BLK & LEJ & LEO & KEPT & RO2 & UBK
    & INIT1 & RLEN1 & RES1).
  destruct POST as (HMR1 & HWF1 & HBD1 & HLE1 & HSTAB1 & HPRES1 & HVM1 & HFRAME1 & HBLKS1 & HSCR1).
  rewrite SEGS in HFRAME1, HSCR1.
  unfold blocks_kept in KEPT. rewrite ?SEGS in KEPT.
  destruct (mr_model _ _ LAWS _ _ _ _ HMR1) as (Hh1 & Hl1 & Hmat1).
  destruct BLK as (b1 & b2 & BLK1 & BLK2).
  destruct FRESH as (FR_lo & FR_hi & FR_img).
  pose proof (cw_join_len ws) as JLEN.
  assert (JNN : 0 <= join_need ws) by lia.
  assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp - 176))
    by exact (eq_trans (HPRES1 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (E2_3 : reg_get R2 3 = reg_get regs 3)
    by exact (eq_trans (HPRES1 3 ltac:(unfold callee_saved; lia)) (K1 3 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia))).
  assert (E2_4 : reg_get R2 4 = reg_get regs 4) by exact (eq_trans (HPRES1 4 ltac:(unfold callee_saved; lia)) E1_4).
  assert (E2_9 : reg_get R2 9 = Z_to_bv 64 (Z.min (Z.of_nat (length ws)) 64))
    by exact (eq_trans (HPRES1 9 ltac:(unfold callee_saved; lia)) E1_9).
  assert (E2_10 : reg_get R2 10 = Z_to_bv 64 res) by exact A0'.
  assert (F01 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 176 <= a < bv_unsigned sp) ->
             mbyte rsegs m1 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m1 a)).
  { intros a Ha Hx. assert (Ho : outside [(bv_unsigned sp + -176, bv_unsigned sp)] a) by (cbn; split; [lia | exact I]).
    split; [exact (munch_mbyte _ _ _ _ _ MU1 Ha Ho) | exact (munch_writable _ _ _ _ _ MU1 Ha Ho)]. }
  assert (F12 : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a ->
             ~ (bv_unsigned sp - 8448 <= a < bv_unsigned sp - 176) -> ~ (errno_addr B <= a < errno_addr B + 4) ->
             ~ (bv_unsigned sp - 128 <= a < bv_unsigned sp - 120) ->
             mbyte rsegs m2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs m2 a)).
  { intros a Hd N1 Hs He Ho.
    apply HFRAME1; [exact Hd | exact N1 | exact (not_owned_mid B _ LAWS AX CTXO L A mem md L1 A1 m2 md1 a HMR HMR1 Hd N1) | |].
    - unfold scratch_k, JOINED_FRAME. change ALLOC_STACK with 8192. rewrite SP1. intros [H|H]; [lia | exact (He H)].
    - unfold joined_writes. intros [H|H]; [|lia].
      destruct Hd as [Hd|Hd]; [lia|]. apply (FR_img (a - res)); [lia|]. replace (res + (a - res)) with a by ring. exact Hd. }
  assert (F02 : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a ->
             ~ (bv_unsigned sp - 8448 <= a < bv_unsigned sp) -> ~ (errno_addr B <= a < errno_addr B + 4) ->
             mbyte rsegs m2 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m2 a)).
  { intros a Hd N1 Hs He.
    assert (Ha : 0 <= a < 2 ^ 64) by (destruct Hd as [Hd|Hd]; [lia | pose proof (in_img_low B SEGS a Hd); lia]).
    destruct (F01 a Ha ltac:(lia)) as [E1 W1]. destruct (F12 a Hd N1 ltac:(lia) He ltac:(lia)) as [E2 W2].
    split; [congruence | tauto]. }
  assert (B02 : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m2 (a + i) = mbyte rsegs mem (a + i)).
  { intros a k i Hin Hi. pose proof (BRNG a k Hin).
    rewrite (KEPT a k i Hin (fun F => F) Hi). exact (proj1 (F01 (a + i) ltac:(lia) ltac:(lia))). }
  assert (LEB : bytes_at rsegs m2 (bv_unsigned sp + -128) (Mem.le8 (Z_to_bv 64 (Z.of_nat (length (RecFacts.join_sp ws)))))).
  { apply (cw_bytes_of_le B m2 _ _ SEGS); [lia | rewrite Mem.length_le8; lia | exact LEO]. }
  assert (WR2 : forall a, bv_unsigned sp - 8448 <= a < bv_unsigned sp -> writable_at rsegs m2 a).
  { intros a Ha.
    destruct (Z_lt_ge_dec a (bv_unsigned sp - 176)) as [H1|H1].
    { apply HSCR1. unfold scratch_k, JOINED_FRAME. change ALLOC_STACK with 8192. rewrite SP1. left. lia. }
    destruct (Z_lt_ge_dec a (bv_unsigned sp - 128)) as [H2|H2];
      [|destruct (Z_lt_ge_dec a (bv_unsigned sp - 120)) as [H3|H3]].
    - apply (proj2 (F12 a ltac:(left; lia) (NOH a ltac:(lia)) ltac:(lia) (NEH a ltac:(lia)) ltac:(lia))). apply WR1. lia.
    - pose proof LEB as (_ & _ & LB).
      assert (Hk : (Z.to_nat (a - (bv_unsigned sp + -128)) <
                    length (Mem.le8 (Z_to_bv 64 (Z.of_nat (length (RecFacts.join_sp ws))))))%nat)
        by (rewrite Mem.length_le8; lia).
      pose proof (LB _ Hk) as E.
      replace (bv_unsigned sp + -128 + Z.of_nat (Z.to_nat (a - (bv_unsigned sp + -128)))) with a in E by lia.
      apply present_writable. apply cw_hi_present; [lia|].
      rewrite cw_mbyte_mrd. rewrite E. apply nth_error_Some. exact Hk.
    - apply (proj2 (F12 a ltac:(left; lia) (NOH a ltac:(lia)) ltac:(lia) (NEH a ltac:(lia)) ltac:(lia))). apply WR1. lia. }
  assert (WRJ : forall a, bv_unsigned sp - 8448 <= a < bv_unsigned sp ->
             writable_at rsegs (MemNorm.normalize_cj rsegs m2) a).
  { intros a Ha. apply (cw_wr_norm m2 a RO2); [unfold TASK_SIZE; lia | exact (WR2 a Ha)]. }
  assert (MJ : forall a, 0 <= a -> a < bv_unsigned sp \/ a < W + 32 ->
             mbyte rsegs (MemNorm.normalize_cj rsegs m2) a = mbyte rsegs m2 a).
  { intros a H0 H1. apply (cw_mbyte_norm m2 a RO2). unfold TASK_SIZE. lia. }
  assert (GKJ : forall a, in_globals frame_G a -> mbyte rsegs (MemNorm.normalize_cj rsegs m2) a = mbyte rsegs mem a).
  { intros a Hg. pose proof (cw_g_iv a Hg) as Hr. destruct (G_STAT a Hg) as (Hi & _ & _ & He).
    rewrite MJ by lia.
    exact (proj1 (F02 a (or_intror Hi) (cw_gnown L A mem md a HMR Hg) ltac:(lia) He)). }
  assert (RKJ : forall a, in_globals frame_RELRO a -> ~ (0x22a68 <= a < 0x22a70) ->
             mbyte rsegs (MemNorm.normalize_cj rsegs m2) a = mbyte rsegs mem a).
  { intros a Ha Hg. pose proof (cw_relro_iv a Ha) as Hr.
    destruct (RELRO_FREE L A mem md a HMR Ha ltac:(rewrite GOT_AT; lia)) as [Ho He].
    rewrite MJ by lia.
    exact (proj1 (F02 a (or_intror (cw_img_iv B a SEGS ltac:(lia))) Ho ltac:(lia) He)). }
  assert (BKJ : forall q0 k x, In (q0, k) (blocks L A) -> q0 <= x < q0 + k ->
             mbyte rsegs (MemNorm.normalize_cj rsegs m2) x = mbyte rsegs mem x).
  { intros q0 k x Hb Hx. pose proof (BRNG q0 k Hb). rewrite MJ by lia.
    replace x with (q0 + (x - q0)) by ring. apply (B02 q0 k); [exact Hb | lia]. }
  assert (HKJ : forall a, bv_unsigned sp <= a < W + 32 ->
             mbyte rsegs (MemNorm.normalize_cj rsegs m2) a = mbyte rsegs mem a).
  { intros a Ha. rewrite MJ by lia.
    exact (proj1 (F02 a ltac:(left; lia) (NOH a ltac:(lia)) ltac:(lia) (NEH a ltac:(lia)))). }
  assert (MV : forall X cs, rw_cells rsegs m1 X cs -> bv_unsigned sp - 176 <= X ->
             X + Z.of_nat (cells_size cs) <= bv_unsigned sp ->
             (X + Z.of_nat (cells_size cs) <= bv_unsigned sp - 128 \/ bv_unsigned sp - 120 <= X) ->
             rw_cells rsegs (MemNorm.normalize_cj rsegs m2) X cs).
  { intros X cs H H1 H2 H3. apply (cw_rw_move m1 _ X cs H). intros i Hi. split.
    - rewrite MJ by lia.
      exact (proj1 (F12 (X + i) ltac:(left; lia) (NOH (X + i) ltac:(lia)) ltac:(lia) (NEH (X + i) ltac:(lia)) ltac:(lia))).
    - apply WRJ. lia. }
  assert (FA : rw_cells rsegs (MemNorm.normalize_cj rsegs m2) (bv_unsigned sp - 176)
                 [CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 W); CB 8 j4; CB 8 j5]).
  { apply MV; [| lia | cbn; lia | cbn; lia].
    eapply (cw_rw_sub m1 (bv_unsigned sp + -176) _ []); [exact FR1 | cbn; lia]. }
  assert (FJ7 : rw_cells rsegs (MemNorm.normalize_cj rsegs m2) (bv_unsigned sp - 176 + 56) [CB 16 j7]).
  { apply MV; [| lia | cbn; lia | cbn; lia].
    eapply (cw_rw_sub m1 (bv_unsigned sp + -176) _
      [CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 W); CB 8 j4; CB 8 j5; CB 8 j6]); [exact FR1 | cbn; lia]. }
  assert (FRS : rw_cells rsegs (MemNorm.normalize_cj rsegs m2) (bv_unsigned sp - 176 + 72)
                  [C8 (reg_get regs 27); C8 (reg_get regs 26); C8 (reg_get regs 25); C8 (reg_get regs 24);
                   C8 (reg_get regs 23); C8 (reg_get regs 22); C8 (reg_get regs 21); C8 (reg_get regs 20);
                   C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply MV; [| lia | cbn; lia | cbn; lia].
    eapply (cw_rw_sub m1 (bv_unsigned sp + -176) _
      [CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 W); CB 8 j4; CB 8 j5; CB 8 j6; CB 16 j7] _ []);
      [exact FR1 | cbn; lia]. }
  assert (FB48 : rw_cells rsegs (MemNorm.normalize_cj rsegs m2) (bv_unsigned sp - 176 + 48)
                   [CB 8 (Mem.le8 (Z_to_bv 64 (Z.of_nat (length (RecFacts.join_sp ws)))))]).
  { apply cw_rw_bytes.
    - cbn [cells_wf cell_wf]. split; [apply Mem.length_le8 | exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply (bytes_at_transfer rsegs m2);
        [replace (bv_unsigned sp - 176 + 48) with (bv_unsigned sp + -128) by lia; exact LEB|].
      intros i Hi. rewrite Mem.length_le8 in Hi. apply MJ; lia.
    - intros i Hi. cbn [cells_size csize Nat.add] in Hi. apply WRJ. lia. }
  destruct (ax_statics AX L1 A1 m2 md1 HMR1) as (WG2 & (g2 & Hg2 & WGG2) & _).
  rewrite SEGS, GOT_AT, GUARD_AT in WG2. rewrite SEGS, GUARD_AT in WGG2.
  assert (GGJ : rw_cells rsegs (MemNorm.normalize_cj rsegs m2) 0x22a68 [C8 (Z_to_bv 64 0x54450)]).
  { apply cw_rw_bytes; [cbn [cells_wf cell_wf]; tauto | |].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply (bytes_at_transfer rsegs m2);
        [exact (KindBGlue.word_mem_le8 rsegs m2 0x22a68 0x54450 WG2 ltac:(lia) ltac:(lia) ltac:(lia))|].
      intros i Hi. rewrite Mem.length_le8 in Hi. apply MJ; lia.
    - intros i Hi. cbn [cells_size csize Nat.add] in Hi.
      exact (proj1 (guard_wview (MemNorm.normalize_cj rsegs m2) i Hi)). }
  assert (GUJ : rw_cells rsegs (MemNorm.normalize_cj rsegs m2) 0x54450 [C8 (Z_to_bv 64 g2)]).
  { apply cw_rw_bytes; [cbn [cells_wf cell_wf]; tauto | |].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply (bytes_at_transfer rsegs m2);
        [exact (KindBGlue.word_mem_le8 rsegs m2 0x54450 g2 WGG2 Hg2 ltac:(lia) ltac:(lia))|].
      intros i Hi. rewrite Mem.length_le8 in Hi. apply MJ; lia.
    - intros i Hi. cbn [cells_size csize Nat.add] in Hi.
      exact (proj2 (guard_wview (MemNorm.normalize_cj rsegs m2) i Hi)). }
  assert (HGJ : bytes_at rsegs (MemNorm.normalize_cj rsegs m2) 0x22a20 (Mem.le8 (Z_to_bv 64 CW_GREC))).
  { apply (cw_bytes_of_image rsegs _ 8 _ _ cw_grec_img); [| lia | lia].
    intros i Hi. rewrite (RKJ (0x22a20 + i)); [| apply cw_relro_of; lia | lia]. apply GIM. apply cw_relro_of. lia. }
  pose proof REP as (Q & (RS & RC & _) & HQO).
  destruct RC as (C1 & C2 & C3 & C4 & _).
  assert (HNC : bytes_at rsegs (MemNorm.normalize_cj rsegs m2) (CW_GREC + 8)
                  (Mem.le4 (Z_to_bv 64 (Z.of_nat (length (r_calls R)))))).
  { apply (bytes_at_transfer rsegs mem); [exact C3|].
    intros i Hi. rewrite Mem.length_le4 in Hi. apply GKJ. apply cw_g_of. unfold CW_GREC. lia. }
  assert (HCA : forall i c, nth_error (r_calls R) i = Some c ->
             call_at_a (MemNorm.normalize_cj rsegs m2) (bv_unsigned sp - 8448) (CW_GREC + 16 + 56 * Z.of_nat i) c).
  { intros i c Hc.
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
    destruct (nth_error (l_calls Q) i) as [P|] eqn:HP; [|apply nth_error_None in HP; lia].
    destruct (C4 i c P Hc HP) as [CA _].
    apply (cw_call_a (blocks L A) mem _ _ _ c P).
    - exact CA.
    - intros [p k] Hb. cbn [fst snd]. pose proof (BRNG p k Hb). lia.
    - unfold CW_GREC. lia.
    - unfold CW_GREC. lia.
    - unfold CW_GREC. lia.
    - intros x Hx. apply GKJ. apply cw_g_of. unfold CW_GREC in Hx. lia.
    - intros [p k] x Hb Hx. cbn [fst snd] in Hx. apply (BKJ p k); [exact Hb | lia]. }
  assert (UW : bv_unsigned (Z_to_bv 64 W) = W) by (apply unsigned_lit; lia).
  assert (HWA : bytes_at rsegs (MemNorm.normalize_cj rsegs m2) (bv_unsigned (Z_to_bv 64 W) + 16)
                  (Mem.le8 (Z_to_bv 64 arr))).
  { rewrite UW. apply (bytes_at_transfer rsegs mem);
      [apply (cw_bytes_of_le B mem _ _ SEGS); [lia | rewrite Mem.length_le8; lia | exact W16]|].
    intros i Hi. rewrite Mem.length_le8 in Hi. apply HKJ. lia. }
  assert (WVJ : words_view B (MemNorm.normalize_cj rsegs m2) W arr wp ws).
  { apply (cw_wv_keep B L A mem _ W arr wp ws WV WP); rewrite SEGS.
    - intros i Hi. apply HKJ. lia.
    - intros p k i Hin Hi. apply (BKJ p k); [exact Hin | lia]. }
  assert (HWSJ : forall k, 0 <= k < Z.min (Z.of_nat (length ws)) 64 ->
             lowp (bv_unsigned sp - 8448) (MemNorm.normalize_cj rsegs m2) (bv_unsigned (Z_to_bv 64 arr) + 8 * k)
               (nth (Z.to_nat k) (map (Z_to_bv 64) wp) (Z_to_bv 64 0)) (nth (Z.to_nat k) ws [])).
  { intros k Hk. apply (cw_word_low B _ _ W arr wp ws k SEGS WVJ); [lia | lia | lia | | lia].
    intros j Hj. destruct (WPK j Hj) as (p & kk & Hb & H1 & H2). pose proof (BRNG p kk Hb). lia. }
  assert (UR : bv_unsigned (Z_to_bv 64 res) = res) by (apply unsigned_lit; lia).
  assert (HLJ : bytes_at rsegs (MemNorm.normalize_cj rsegs m2) (bv_unsigned (Z_to_bv 64 res))
                  (RecFacts.join_sp ws ++ [NUL])).
  { rewrite UR. apply (bytes_at_transfer rsegs m2);
      [apply (cw_bytes_of_le B m2 _ _ SEGS); [lia | rewrite length_app; cbn [length]; lia | exact LEJ]|].
    intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply MJ; lia. }
  assert (HL0 : ~ In NUL (RecFacts.join_sp ws)).
  { apply cw_join_no0. intros w Hw. apply (In_nth ws w []) in Hw as (k & Hk & <-).
    destruct (WK k Hk) as (_ & Hn & _). exact Hn. }
  assert (STJ : stk rsegs (MemNorm.normalize_cj rsegs m2) (bv_unsigned sp - 8448) (bv_unsigned sp - 176)).
  { apply stk_normalize_cj; [lia | unfold TASK_SIZE; lia | intros a Ha; apply WR2; lia]. }
  rewrite E1_1.
  eapply evt_SR_canon; [ | exact Hh1 | exact Hl1 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2_2, E2_3, E2_4, E2_9, E2_10.
    eapply (MemNorm.evt_normalize_cj rsegs); [exact WX | exact RO2 |].
    eapply (cw_body SSP SCS ATOI SNP SC ADD CHAIN PIN (reg_get regs 3) (reg_get regs 4) (reg_get regs 1)
      (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21)
      (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27)
      fp_regs (MemNorm.normalize_cj rsegs m2) (bv_unsigned sp - 8448) (bv_unsigned sp - 176)
      (Z.min (Z.of_nat (length ws)) 64) ws (map (Z_to_bv 64) wp) (Z_to_bv 64 W) (Z_to_bv 64 arr) (Z_to_bv 64 res)
      (Z_to_bv 64 g2) (r_calls R) j0 j1 j2 j4 j5 (Mem.le8 (Z_to_bv 64 (Z.of_nat (length (RecFacts.join_sp ws))))) j7).
    - lia.
    - lia.
    - lia.
    - lia.
    - unfold words_prop in WPR. exact WPR.
    - exact C1.
    - exact FA.
    - exact FB48.
    - exact FJ7.
    - exact FRS.
    - exact GGJ.
    - exact GUJ.
    - exact HGJ.
    - exact HNC.
    - exact HCA.
    - exact HWA.
    - rewrite UW. lia.
    - exact HWSJ.
    - exact HLJ.
    - exact HL0.
    - rewrite UR. lia.
    - exact (MemNorm.mem_inv_cj_task rsegs _ (MemNorm.mem_inv_cj_normalize rsegs m2)).
    - exact STJ.
    - exact (MemNorm.mem_inv_cj_inv rsegs _ (MemNorm.mem_inv_cj_normalize rsegs m2)).
    - exact FRM. }
  intros ms3 (can3 & (s3n & Q3 & REL3 & CJ3) & EQ3).
  unfold cw_body_post in Q3.
  destruct Q3 as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & Fc & fc & m3n & -> & MI3 & MU3n
    & WM3n & ST3n & FRM3 & FPR3).
  destruct (ms_rel_cj_MS _ _ _ _ _ _ _ _ REL3) as [EC3 MR3r].
  revert EC3 MR3r CJ3 EQ3. generalize (ms_mem can3) as m3. intros m3 EC3 MR3r CJ3 EQ3. subst can3.
  pose proof (MemNorm.munch_rel_cj rsegs _ _ _ _ _ (MemNorm.mem_rel_cj_normalize rsegs m2 RO2) MR3r CJ3 MU3n) as MU3.
  pose proof (MemNorm.ro_agree_same_cj rsegs _ _ RO2 CJ3) as RO3.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ3) as (R3 & -> & X3). clear EQ3.
  assert (E3_1 : getr R3 1 = reg_get regs 1) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 176 + 176))
    by (rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_4 : getr R3 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_10 : getr R3 10 = Z_to_bv 64 res) by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; reflexivity).
  assert (SP3 : spZ R3 = bv_unsigned sp) by (unfold spZ; rewrite E3_2, unsigned_lit by lia; ring).
  assert (OUT3 : forall a, ~ (bv_unsigned sp - 8448 <= a < bv_unsigned sp) ->
            outside [(bv_unsigned sp - 8448, bv_unsigned sp - 176 + 176)] a) by (intros a Ha; cbn; split; [lia | exact I]).
  assert (HMR3 : aa_MR API L1 A1 m3 md1).
  { apply (mr_frame B _ LAWS L1 A1 m2 m3 md1 md1 HMR1).
    - intros a Ho. destruct (mr_owned_low B _ LAWS _ _ _ _ a HMR1 Ho) as [Ha1 Ha2].
      apply (munch_mbyte _ _ _ _ _ MU3); [lia | apply OUT3; lia].
    - intros a Ho Hp. destruct (mr_owned_low B _ LAWS _ _ _ _ a HMR1 Ho) as [Ha1 Ha2].
      apply (munch_present _ _ _ a MU3); [lia | apply OUT3; lia | exact Hp].
    - intros p k i Hin Hi. destruct (mr_blocks B _ LAWS L1 A1 m2 md1 p k i HMR1 Hin Hi) as (Hp & H4 & Hc & _).
      apply (munch_present _ _ _ _ MU3); [lia | apply OUT3; lia | exact Hp].
    - reflexivity.
    - exact Hh1.
    - exact Hl1.
    - exact Hmat1. }
  assert (WR3 : forall a, bv_unsigned sp - 8448 <= a < bv_unsigned sp -> writable_at rsegs m3 a).
  { intros a Ha. destruct ST3n as (_ & _ & HS). destruct (HS a ltac:(lia)) as [Hw _].
    exact (MemNorm.writable_at_rel_cj rsegs m3 m3n a MR3r Hw). }
  assert (ERR3 : forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at rsegs m3 a).
  { intros a Ha. pose proof Ha as Ha'. rewrite EA in Ha'.
    apply (proj1 (munch_writable rsegs _ _ _ a MU3 ltac:(lia) (OUT3 a ltac:(lia)))).
    apply HSCR1. unfold scratch_k. right. exact Ha. }
  assert (INB : In (res, join_need ws + 1) (blocks L1 A1)) by (rewrite BLK1; apply in_or_app; right; left; reflexivity).
  pose proof INB as INB'. apply YI06.blocks_In in INB' as (pf & EPF & UPF).
  pose proof (FREE (mkFP Fc fc)) as FR0. unfold free_contract in FR0. rewrite SEGS, FREE_PC in FR0.
  eapply SR_bind.
  { apply (FR0 L1 A1 R3 m3 md1 pf (join_need ws + 1) (sb_malloc b (join_need ws + 1))); clear FR0.
    - split; [exact HMR3|]. split; [exact HWF1|]. split; [exact HBD1|].
      split; [rewrite E3_1; exact HRA|].
      split; [rewrite SP3; exact HAL|].
      split; [rewrite SP3; change ALLOC_STACK with 8192; lia|].
      split; [rewrite SP3; lia|].
      split; [intros a Ha; rewrite SP3 in Ha; change ALLOC_STACK with 8192 in Ha; rewrite SEGS; apply WR3; lia|].
      split; [rewrite E3_4; exact HTP|].
      split; [intros a Ha; rewrite SEGS; exact (ERR3 a Ha)|].
      intros HI. rewrite INIT1 in HI. discriminate.
    - exact RO3.
    - exact UPF.
    - rewrite E3_10, EPF. reflexivity.
    - exact RES1. }
  intros c4 RET4.
  destruct RET4 as (L2 & A2 & R4 & m4 & md2 & -> & CP4 & (d1 & d2 & BL2 & BL3) & KEPT4 & RO4 & GK4 & UB4 & INIT4
    & REG4 & RES4).
  destruct CP4 as (HMR2 & HWF2 & HBD2 & HLE2 & HSTAB2 & HP4 & HVM2 & HFR2 & HBLKS2 & HSCR2).
  rewrite SEGS in HFR2, HSCR2.
  unfold blocks_kept in KEPT4. rewrite SEGS in KEPT4.
  assert (F34 : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L1 A1 a ->
             ~ (bv_unsigned sp - 8192 <= a < bv_unsigned sp) -> ~ (errno_addr B <= a < errno_addr B + 4) ->
             ~ (res <= a < res + (join_need ws + 1)) ->
             mbyte rsegs m4 a = mbyte rsegs m3 a /\ (writable_at rsegs m3 a <-> writable_at rsegs m4 a)).
  { intros a Hd N1 Hs He Hr.
    apply HFR2; [exact Hd | exact N1 | exact (not_owned_mid B _ LAWS AX CTXO L1 A1 m2 md1 L2 A2 m4 md2 a HMR1 HMR2 Hd N1) | |].
    - unfold scratch. rewrite SP3. change ALLOC_STACK with 8192. intros [H|H]; [lia | exact (He H)].
    - cbv beta. rewrite EPF. exact Hr. }
  assert (F24 : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L1 A1 a ->
             ~ (bv_unsigned sp - 8448 <= a < bv_unsigned sp) -> ~ (errno_addr B <= a < errno_addr B + 4) ->
             ~ (res <= a < res + (join_need ws + 1)) ->
             mbyte rsegs m4 a = mbyte rsegs m2 a /\ (writable_at rsegs m2 a <-> writable_at rsegs m4 a)).
  { intros a Hd N1 Hs He Hr.
    assert (Ha : 0 <= a < 2 ^ 64) by (destruct Hd as [Hd|Hd]; [lia | pose proof (in_img_low B SEGS a Hd); lia]).
    pose proof (munch_mbyte rsegs _ _ _ _ MU3 Ha (OUT3 a Hs)) as E23.
    pose proof (munch_writable rsegs _ _ _ _ MU3 Ha (OUT3 a Hs)) as W23.
    destruct (F34 a Hd N1 ltac:(lia) He Hr) as [E34 W34].
    split; [congruence | tauto]. }
  assert (FALL : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a ->
             ~ (bv_unsigned sp - 8448 <= a < bv_unsigned sp) -> ~ (errno_addr B <= a < errno_addr B + 4) ->
             mbyte rsegs m4 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs m4 a)).
  { intros a Hd N1 Hs He.
    assert (Hr : ~ (res <= a < res + (join_need ws + 1))).
    { intros Hr. destruct Hd as [Hd|Hd]; [lia|]. apply (FR_img (a - res)); [lia|].
      replace (res + (a - res)) with a by ring. exact Hd. }
    destruct (F02 a Hd N1 Hs He) as [E1 W1].
    destruct (F24 a Hd (not_owned_mid B _ LAWS AX CTXO L A mem md L1 A1 m2 md1 a HMR HMR1 Hd N1) Hs He Hr) as [E2 W2].
    split; [congruence | tauto]. }
  assert (B24 : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m4 (a + i) = mbyte rsegs m2 (a + i)).
  { intros a k i Hin Hi. pose proof (BRNG a k Hin) as Rg.
    assert (Hin1 : In (a, k) (blocks L1 A1)) by (rewrite BLK1; rewrite BLK2 in Hin; apply in_mid_inv; exact Hin).
    assert (Hne : a <> ptr_addr L1 pf).
    { rewrite EPF. intros ->. rewrite BLK2 in Hin.
      destruct (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR1 BLK1 Hin); lia. }
    rewrite (KEPT4 a k i Hin1 Hne Hi).
    exact (munch_mbyte rsegs _ _ _ (a + i) MU3 ltac:(lia) (OUT3 (a + i) ltac:(lia))). }
  assert (BALL : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m4 (a + i) = mbyte rsegs mem (a + i)).
  { intros a k i Hin Hi. rewrite (B24 a k i Hin Hi). exact (B02 a k i Hin Hi). }
  assert (BL2' : blocks L1 A1 = d1 ++ (res, join_need ws + 1) :: d2) by (rewrite <- EPF; exact BL2).
  assert (BLEQ : blocks L2 A2 = blocks L A).
  { rewrite BL3, BLK2. symmetry. apply (cw_mid_eq b1 b2 d1 d2 (res, join_need ws + 1)).
    - rewrite <- BLK1. exact BL2'.
    - intros H. destruct (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR1 BLK1 (in_or_app _ _ _ (or_introl H)));
        lia.
    - intros H. destruct (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR1 BL2' (in_or_app _ _ _ (or_introl H)));
        lia. }
  apply SR_ret. cbv beta.
  exists (mkFP Fc fc), L2, A2, R4, m4, md2.
  split; [rewrite E3_1; reflexivity|].
  split; [exact FRM3|].
  split.
  { unfold call_post_k.
    split; [exact HMR2|]. split; [exact HWF2|]. split; [exact HBD2|].
    split; [exact (cw_lle_trans A A1 L L1 L2 HLE1 HLE2 RLEN1)|].
    split; [intros p k H1 H3; pose proof (UBK p k H1) as H2; rewrite (HSTAB2 p k H2 H3); exact (HSTAB1 p k H1 H2)|].
    split.
    { intros r Hr. rewrite (HP4 r Hr). unfold callee_saved in Hr.
      assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct C as [C|C].
      { subst r. rewrite (getr_of_eqv _ _ _ X3) by reflexivity. simp_regs.
        replace (bv_unsigned sp - 176 + 176) with (bv_unsigned sp) by ring. rewrite Z_to_bv_bv_unsigned. reflexivity. }
      repeat (destruct C as [C|C]; [subst r; rewrite (getr_of_eqv _ _ _ X3) by reflexivity; reflexivity|]).
      subst r; rewrite (getr_of_eqv _ _ _ X3) by reflexivity; reflexivity. }
    split; [destruct HVM1 as [vm1 ->]; destruct HVM2 as [vm2 ->]; exists vm2; apply with_vmmaps_twice'|].
    split.
    { intros a Hd N1 _ Hs _. rewrite SEGS. unfold scratch_k in Hs. rewrite KV in Hs.
      change (spZ regs) with (bv_unsigned sp) in Hs.
      exact (FALL a Hd N1 (fun H => Hs (or_introl H)) (fun H => Hs (or_intror H))). }
    split.
    { intros p k i H1 _ Hi. rewrite SEGS. apply (BALL (ptr_addr L p) k i); [|exact Hi].
      unfold blocks. exact (in_map (fun e => (ptr_addr L (fst e), snd e)) _ _ H1). }
    intros a Hs. rewrite SEGS. unfold scratch_k in Hs. rewrite KV in Hs. change (spZ regs) with (bv_unsigned sp) in Hs.
    destruct Hs as [Hs|He]; [|apply HSCR2; unfold scratch; right; exact He].
    destruct (Z_lt_ge_dec a (bv_unsigned sp - 8192)) as [Hl8|Hh8].
    - assert (N1 : ~ owned B L1 A1 a) by (intros Ho; destruct (mr_owned_low B _ LAWS _ _ _ _ _ HMR1 Ho); lia).
      apply (proj2 (F34 a ltac:(left; lia) N1 ltac:(lia) ltac:(rewrite EA; lia) ltac:(lia))).
      apply WR3. lia.
    - apply HSCR2. unfold scratch. rewrite SP3. change ALLOC_STACK with 8192. left. lia. }
  split; [exact BLEQ|].
  split; [unfold blocks_kept; rewrite SEGS; intros a k i Hin _ Hi; exact (BALL a k i Hin Hi)|].
  split; [intros _; exact (INIT4 INIT1)|].
  split; [lia|].
  split.
  { unfold CommandB.cmd_mem. rewrite SEGS.
    destruct (ax_statics AX L2 A2 m4 md2 HMR2) as (WG4 & (g4 & Hg4 & WGG4) & _).
    rewrite SEGS, GOT_AT, GUARD_AT in WG4. rewrite SEGS, GUARD_AT in WGG4.
    split; [exact RO4|].
    split.
    { unfold G_img_c. intros a Ha. rewrite SEGS. pose proof (cw_relro_iv a Ha) as Hr.
      destruct (Z_lt_ge_dec a 0x22a68) as [H1|H1]; [|destruct (Z_lt_ge_dec a 0x22a70) as [H2|H2]].
      - destruct (RELRO_FREE L A mem md a HMR Ha ltac:(rewrite GOT_AT; lia)) as [Ho He].
        rewrite <- (GIM a Ha). exact (proj1 (FALL a (or_intror (cw_img_iv B a SEGS ltac:(lia))) Ho ltac:(lia) He)).
      - exact (cw_got_rom m4 a WG4 ltac:(lia)).
      - destruct (RELRO_FREE L A mem md a HMR Ha ltac:(rewrite GOT_AT; lia)) as [Ho He].
        rewrite <- (GIM a Ha). exact (proj1 (FALL a (or_intror (cw_img_iv B a SEGS ltac:(lia))) Ho ltac:(lia) He)). }
    split.
    { exists (Z_to_bv 64 g4). apply (cw_le_of_bytes B m4 _ _ SEGS).
      exact (KindBGlue.word_mem_le8 rsegs m4 0x54450 g4 WGG4 Hg4 ltac:(lia) ltac:(lia)). }
    intros i Hi. exact (cw_guard_wr m4 i Hi). }
  split.
  { apply (cw_le_keep B mem); [exact QUIT0|]. rewrite SEGS. intros i Hi. rewrite Mem.length_le4 in Hi.
    destruct (QOUT i Hi) as [No Ns].
    unfold scratch_k in Ns. rewrite KV in Ns. change (spZ regs) with (bv_unsigned sp) in Ns.
    assert (Hg : in_globals frame_G (VerbsB.G_QUIT + i)) by (apply cw_g_of; unfold VerbsB.G_QUIT; lia).
    destruct (G_STAT _ Hg) as (Hi' & _ & _ & _).
    exact (proj1 (FALL _ (or_intror Hi') No (fun H => Ns (or_introl H)) (fun H => Ns (or_intror H)))). }
  split.
  { unfold g_rec_rep in REP |- *. apply (rec_rep_frame rsegs G_REC REC_SC L A mem R O L2 A2 m4 REP).
    - intros a Ha. assert (Hg : in_globals frame_G a) by (apply cw_g_of; unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha; lia).
      destruct (G_STAT a Hg) as (Hi & _ & _ & He). pose proof (cw_g_iv a Hg) as Hr.
      destruct (FALL a (or_intror Hi) (cw_gnown L A mem md a HMR Hg) ltac:(lia) He) as [E Wq].
      split; [exact E | apply Wq].
    - intros p k i Hin Hi. exact (BALL p k i (rec_rep_O_blocks _ _ _ _ _ _ _ _ _ REP Hin) Hi).
    - intros pn Hin. rewrite BLEQ. exact (rec_rep_O_blocks _ _ _ _ _ _ _ _ _ REP Hin). }
  split.
  { apply (cw_wv_keep B L A mem m4 W arr wp ws WV WP); rewrite SEGS.
    - intros i Hi.
      exact (proj1 (FALL (W + 16 + i) ltac:(left; lia) (NOH (W + 16 + i) ltac:(lia)) ltac:(lia) (NEH (W + 16 + i) ltac:(lia)))).
    - intros p k i Hin Hi. exact (BALL p k i Hin Hi). }
  exact RES4.
Qed.

End CW.
