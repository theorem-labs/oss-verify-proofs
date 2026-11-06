(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_worker_list.v, with its module paths, addresses and numbers changed; 1213 of its 1275 lines of code are new or changed and 486 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/send_message.v, with its module paths, module names, addresses and numbers changed; 524 of its 628 lines of code are new or changed and 1171 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/check_words.v; 745 of its 764 lines of code are new or changed and 609 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes FP ZBridge Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import CType StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandModel CommandFP CommandTac printf_facts_c atoi_c snprintf_c strcmp_c strspn_c strcspn_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import check_words_chain syntax_reply_matches check_words_add_c check_words_chain_c check_words_pin_set_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import CwItems.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Open Scope Z_scope.

(* check_words from its entry 0x14bac to the call of joined (0x14c0c): the 208-byte frame holds the saved
   registers at sp+104 and W at sp+64; s1 = min(nwords, 64), a0 = W, a1 = sp+80. *)
Definition cw_mid1 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (W n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' j0 j1 j2 j3 j4 j5 j6 j7 j9 j10 j11,
    ms' = MS (mkR (Z_to_bv 64 0x14c10) (Z_to_bv 64 (bv_unsigned sp + -208)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (Z.min n 64))
                  (Z_to_bv 64 W) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x15324) fc None m' (seg_rom rsegs)
    /\ a1 = Z_to_bv 64 (bv_unsigned sp + -128)
    /\ munch [(bv_unsigned sp + -208, bv_unsigned sp)] m m' /\ wmono rsegs m m'
    /\ rw_cells rsegs m' (bv_unsigned sp + -208)
         [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; C8 (Z_to_bv 64 W); CB 8 j9;
          CB 8 j10; CB 16 j11;
          C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma cw_land7 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma cw_run1 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo W n : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 208 <= bv_unsigned sp -> 0 <= n < 2 ^ 31 ->
  0 <= W -> bv_unsigned sp <= W + 16 -> W + 32 <= 2 ^ 64 -> W mod 8 = 0 ->
  bytes_at rsegs m (W + 24) (le4 (Z_to_bv 64 n)) ->
  evt rsegs (cw_mid1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W n m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 W) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14bac) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo W n ST LO NR W0 W1 W2 W8 HN.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  apply bytes_ro4 in HN.
  pose proof (munch_refl [(bv_unsigned sp + -208, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 208%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 208%nat junk []
           [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 16; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 16 zstep.
  rewrite ?(cw_land7 W) by lia. rewrite ?W8.
  zstep. if_cases Q0.
  { exfalso. zc Q0. rewrite ?(cw_land7 W) in Q0 by lia. rewrite ?W8 in Q0.
    first [lia | vm_compute in Q0; first [discriminate Q0 | lia | contradiction]]. }
  zstep. zstep.
  rewrite (sx32_lit n) by lia.
  zstep. zstep. if_cases Q.
  - zify_cond Q. rewrite ?signed_lit in Q by lia.
    zstep. zstep. zstep.
    apply evt_done. unfold cw_mid1. rewrite (Z.min_l n 64) by lia.
    do 26 eexists. split; [reflexivity|].
    split; [first [reflexivity | (f_equal; lia) | (f_equal; rewrite ?unsigned_lit by lia; lia)]|].
    split; [exact MU|]. split; [exact WM|]. exact FR.
  - zify_cond Q. rewrite ?signed_lit in Q by lia.
    zstep. zstep. zstep. zstep.
    apply evt_done. unfold cw_mid1. rewrite (Z.min_r n 64) by lia.
    do 26 eexists. split; [reflexivity|].
    split; [first [reflexivity | (f_equal; lia) | (f_equal; rewrite ?unsigned_lit by lia; lia)]|].
    split; [exact MU|]. split; [exact WM|]. exact FR.
Qed.

(* 0x14eb4 (free's return) to check_words' return: the saved registers back, sp + 208. *)
Lemma cw_epi :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o : word),
  rw_cells rsegs m (bv_unsigned sp + 104)
    [C8 s11o; C8 s10o; C8 s9o; C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  bv_unsigned sp + 208 < 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = MS (mkR rao (Z_to_bv 64 (bv_unsigned sp + 208)) gp tp t0 t1 t2 s0o s1o
                                     a0 a1 a2 a3 a4 a5 a6 a7 s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o t3 t4 t5 t6)
                                F (ret_pc rao) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14eb4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o FR SPR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 15 zstep.
  apply evt_done.
  first [reflexivity | f_equal; f_equal; rewrite ?unsigned_lit by lia; lia].
Qed.

Definition fpr (F Fc : bvmap 5 word) : Prop := forall k : reg, bv_unsigned k <> 10 -> reg_get Fc k = reg_get F k.

(* The state at free's entry 0x18ad0 (called from 0x14eb0): ra = 0x14eb4, sp the frame, a0 = the joined line;
   the saved registers at sp+104; memory changed only in [lo, sp+104). *)
Definition cw_body_post (gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o : word) (F : bvmap 5 word)
    (lo S : Z) (lp : word) (mr : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (xt0 xt1 xt2 xs0 xs1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
                     xt3 xt4 xt5 xt6 : word) (Fc : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x14eb4) (Z_to_bv 64 S) gp tp xt0 xt1 xt2 xs0 xs1 lp xa1 xa2 xa3 xa4 xa5 xa6 xa7
                  xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
             Fc (Z_to_bv 64 0x18ad0) fc None m (seg_rom rsegs) /\
    mem_inv rsegs m /\ munch [(lo, S + 104)] mr m /\ wmono rsegs mr m /\ stk rsegs m lo (S + 208) /\
    rw_cells rsegs m (S + 104)
      [C8 s11o; C8 s10o; C8 s9o; C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] /\
    frm0 fc /\ fpr F Fc.

Lemma cw_release : forall m lo S j0 cs8 j80 jb rg, stk rsegs m lo S -> lo <= S -> cells_size cs8 = 72%nat ->
  rw_cells rsegs m S [CB 8 j0] -> rw_cells rsegs m (S + 8) cs8 -> rw_cells rsegs m (S + 80) [CB 8 j80] ->
  rw_cells rsegs m (S + 88) [CB 16 jb] -> rw_cells rsegs m (S + 104) rg -> cells_size rg = 104%nat ->
  stk rsegs m lo (S + 208).
Proof.
  intros m lo S j0 cs8 j80 jb rg ST HL CS F0 F1 F2 F3 F4 CR.
  apply (stk_release rsegs m lo S _ ST) in F0; [|lia]. cbn [cells_size csize Nat.add] in F0.
  replace (S + Z.of_nat 8) with (S + 8) in F0 by lia.
  apply (stk_release rsegs m lo _ _ F0) in F1; [|lia]. rewrite CS in F1.
  replace (S + 8 + Z.of_nat 72) with (S + 80) in F1 by lia.
  apply (stk_release rsegs m lo _ _ F1) in F2; [|lia]. cbn [cells_size csize Nat.add] in F2.
  replace (S + 80 + Z.of_nat 8) with (S + 88) in F2 by lia.
  apply (stk_release rsegs m lo _ _ F2) in F3; [|lia]. cbn [cells_size csize Nat.add] in F3.
  replace (S + 88 + Z.of_nat 16) with (S + 104) in F3 by lia.
  apply (stk_release rsegs m lo _ _ F3) in F4; [|lia]. rewrite CR in F4.
  replace (S + 104 + Z.of_nat 104) with (S + 208) in F4 by lia. exact F4.
Qed.

(* 0x14eac to free's entry: a0 = the line (sp+72), call free. *)
Lemma cw_end : forall gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o (F : bvmap 5 word) lo S lp mr
    j0 cs8 j80 jb xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
    xt3 xt4 xt5 xt6 Fc fc mc,
  lo <= S -> S + 208 < 2 ^ 64 -> cells_size cs8 = 64%nat ->
  mem_inv rsegs mc -> munch [(lo, S + 104)] mr mc -> wmono rsegs mr mc -> stk rsegs mc lo S -> frm0 fc -> fpr F Fc ->
  rw_cells rsegs mc S [CB 8 j0] -> rw_cells rsegs mc (S + 8) (cs8 ++ [C8 lp]) ->
  rw_cells rsegs mc (S + 80) [CB 8 j80] -> rw_cells rsegs mc (S + 88) [CB 16 jb] ->
  rw_cells rsegs mc (S + 104)
    [C8 s11o; C8 s10o; C8 s9o; C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  evt rsegs (cw_body_post gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o F lo S lp mr)
    (MS (mkR xra (Z_to_bv 64 S) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
        Fc (Z_to_bv 64 0x14eac) fc None mc (seg_rom rsegs)).
Proof.
  intros gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o F lo S lp mr
    j0 cs8 j80 jb xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
    xt3 xt4 xt5 xt6 Fc fc mc HLS HS CS MI MU WM ST FRM FP F0 F1 F2 F3 F4.
  assert (CS2 : cells_size (cs8 ++ [C8 lp]) = 72%nat) by (rewrite cells_size_app, CS; reflexivity).
  pose proof (cw_release mc lo S j0 (cs8 ++ [C8 lp]) j80 jb _ ST HLS CS2 F0 F1 F2 F3 F4 eq_refl) as ST2.
  assert (F72 : rw_cells rsegs mc (S + 72) [C8 lp]).
  { apply rw_cells_app in F1. destruct F1 as [_ F1]. rewrite CS in F1.
    replace (S + 8 + Z.of_nat 64) with (S + 72) in F1 by lia. exact F1. }
  clear F0 F1 F2 F3 ST.
  zstep. zstep.
  apply evt_done. unfold cw_body_post. do 29 eexists. split; [reflexivity|].
  split; [exact MI|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST2|]. split; [exact F4|].
  split; [exact FRM | exact FP].
Qed.

Definition CW_GREC : Z := 0x34028.

(* The record pointer, the table and their complements as the code stores them at sp+8 .. sp+48, the row
   pointer of call c at sp+56, W and the line at sp+64, sp+72. *)
Definition frc (W lp : word) (c : Z) : list cell :=
  [C8 (Z_to_bv 64 CW_TBL); C8 (Z_to_bv 64 (18446744073709551615 - CW_TBL)); C8 (Z_to_bv 64 (CW_GREC + 16));
   C8 (Z_to_bv 64 (18446744073709551615 - (CW_GREC + 16))); C8 (Z_to_bv 64 CW_GREC); C8 (Z_to_bv 64 0x1045f);
   C8 (Z_to_bv 64 (CW_GREC + 24 + 56 * c)); C8 W; C8 lp].

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
  split; [apply (bytes_low W m m' lo); [exact H2 | exact MU | exact D | rewrite length_le4; lia]|].
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

Lemma lowp_ptr : forall lo S m A p s, lowp lo m A p s -> lo <= S -> ptr_at m [(lo, S); (S + 88, S + 104)] A s.
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

Lemma rw_wv : forall m A cs x, rw_cells rsegs m A cs -> A <= bv_unsigned x < A + Z.of_nat (cells_size cs) ->
  wview rsegs m x <> None.
Proof.
  intros m A cs x [_ (_ & _ & Hw)] Hx.
  pose proof (Hw (bv_unsigned x - A) ltac:(lia)) as H. unfold wa in H.
  replace (A + (bv_unsigned x - A)) with (bv_unsigned x) in H by lia. rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.

Ltac dj := cbn [disjoint_from]; repeat (split; [lia|]); exact I.

Section Body.
Variables (gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o : word) (F : bvmap 5 word)
  (mL : word -> option byte) (lo S r : Z) (ws : list (list byte)) (wpw : list word)
  (W arr lp can : word) (calls : list (Z * list (list byte))) (j0 j80 jb0 : list byte).

Local Notation FW := [(lo, S); (S + 56, S + 64); (S + 88, S + 104)].
Local Notation FI := [(lo, S); (S + 88, S + 104)].
Local Notation RG :=
  [C8 s11o; C8 s10o; C8 s9o; C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao].

Hypothesis SSP : strspn_contract.
Hypothesis SCS : strcspn_contract.
Hypothesis ATOI : atoi_contract.
Hypothesis SNP : snprintf_contract.
Hypothesis SC : strcmp_contract.
Hypothesis ADD : check_words_add_contract.
Hypothesis CHAIN : check_words_chain_contract.
Hypothesis PIN : check_words_pin_set_contract.
Hypothesis LO : lo + 8272 <= S.
Hypothesis IE : 0x54f98 <= lo.
Hypothesis SPH : S + 208 < 2 ^ 63.
Hypothesis RR : 0 <= r <= 64.
Hypothesis HOK : Forall (call_words_ok r ws) calls.
Hypothesis NCL : (length calls <= 16)%nat.
Hypothesis FRA : rw_cells rsegs mL S [CB 8 j0].
Hypothesis FR8 : rw_cells rsegs mL (S + 8) (frc W lp 0).
Hypothesis FRB : rw_cells rsegs mL (S + 80) [CB 8 j80].
Hypothesis BUF0 : rw_cells rsegs mL (S + 88) [CB 16 jb0].
Hypothesis FRH : rw_cells rsegs mL (S + 104) RG.
Hypothesis GG : rw_cells rsegs mL 0x22d40 [C8 (Z_to_bv 64 0x54730)].
Hypothesis GU : rw_cells rsegs mL 0x54730 [C8 can].
Hypothesis HTB : forall fn, 0 <= fn < 26 -> bytes_at rsegs mL (CW_TBL + 8 * fn) (le8 (Z_to_bv 64 (cw_tp fn))).
Hypothesis HNC : bytes_at rsegs mL (CW_GREC + 8) (le4 (Z_to_bv 64 (Z.of_nat (length calls)))).
Hypothesis HCA : forall i c, nth_error calls i = Some c -> call_at_a mL lo (CW_GREC + 16 + 56 * Z.of_nat i) c.
Hypothesis HWA : bytes_at rsegs mL (bv_unsigned W + 16) (le8 arr).
Hypothesis HWB : S + 208 <= bv_unsigned W + 16.
Hypothesis HA1 : 0 < r -> bv_unsigned arr <> 0 /\ bv_unsigned arr mod 8 = 0.
Hypothesis HWS : forall k, 0 <= k < r ->
  lowp lo mL (bv_unsigned arr + 8 * k) (nth (Z.to_nat k) wpw (Z_to_bv 64 0)) (nth (Z.to_nat k) ws []).
Hypothesis HL : bytes_at rsegs mL (bv_unsigned lp) (RecFacts.join_sp ws ++ [NUL]) /\ ~ In NUL (RecFacts.join_sp ws) /\
  bv_unsigned lp + Z.of_nat (length (RecFacts.join_sp ws)) + 1 <= lo.
Hypothesis HLnz : bv_unsigned lp <> 0.
Hypothesis TM : MemNorm.task_mem rsegs mL.
Hypothesis STL : stk rsegs mL lo S.

Lemma dFW : disjoint_from FW 0 lo.
Proof. dj. Qed.

Lemma dFI : disjoint_from FI 0 lo.
Proof. dj. Qed.

Lemma TMW : forall mc, munch FW mL mc -> MemNorm.task_mem rsegs mc.
Proof.
  intros mc MU. apply (task_mem_fw FW mL mc TM); [|exact MU].
  intros x Hx. cbn [outside] in Hx.
  assert (C : lo <= bv_unsigned x < S \/ S + 56 <= bv_unsigned x < S + 64 \/ S + 88 <= bv_unsigned x < S + 104) by tauto.
  destruct C as [C|[C|C]].
  - destruct STL as (_ & _ & H). destruct (H (bv_unsigned x) C) as [Hw _]. unfold wa in Hw.
    rewrite Z_to_bv_bv_unsigned in Hw. exact Hw.
  - apply (rw_wv mL (S + 8) _ x FR8). cbn [frc cells_size csize Nat.add]. lia.
  - apply (rw_wv mL (S + 88) _ x BUF0). cbn [cells_size csize Nat.add]. lia.
Qed.

Ltac tpc H MU WM := eapply rw_cells_transport; [exact H | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia].

Lemma bfr_at : forall mc, munch FW mL mc -> wmono rsegs mL mc ->
  rw_cells rsegs mc S [CB 8 j0] /\ rw_cells rsegs mc (S + 80) [CB 8 j80] /\ rw_cells rsegs mc (S + 104) RG /\
  rw_cells rsegs mc 0x22d40 [C8 (Z_to_bv 64 0x54730)] /\ rw_cells rsegs mc 0x54730 [C8 can].
Proof.
  intros mc MU WM.
  split; [tpc FRA MU WM|]. split; [tpc FRB MU WM|]. split; [tpc FRH MU WM|]. split; [tpc GG MU WM | tpc GU MU WM].
Qed.

Definition oinv (c : Z) (m : word -> option byte) (Fc : bvmap 5 word) (fc : bv 32) : Prop :=
  mem_inv rsegs m /\ munch FW mL m /\ wmono rsegs mL m /\ stk rsegs m lo S /\
  (exists jb, rw_cells rsegs m (S + 88) [CB 16 jb]) /\ rw_cells rsegs m (S + 8) (frc W lp c) /\ frm0 fc /\ fpr F Fc.

Abbreviation OS pc c xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6
    Fc fc m :=
  (MS (mkR xra (Z_to_bv 64 S) gp tp xt0 xt1 xt2 xs0 (Z_to_bv 64 r) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
         xs2 (Z_to_bv 64 0x1034c) xs4 xs5 xs6 xs7 xs8 (Z_to_bv 64 c) xs10 xs11 xt3 xt4 xt5 xt6)
      Fc (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Definition Qb : machine_state -> Prop :=
  cw_body_post gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o F lo S lp mL.

(* 0x14eac from any register state with the loop invariant: the line to free. *)
Lemma end_ok : forall c xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10
    xs11 xt3 xt4 xt5 xt6 Fc fc mc,
  oinv c mc Fc fc ->
  evt rsegs Qb (MS (mkR xra (Z_to_bv 64 S) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                   Fc (Z_to_bv 64 0x14eac) fc None mc (seg_rom rsegs)).
Proof.
  intros c xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
    xt3 xt4 xt5 xt6 Fc fc mc (MI & MU & WM & ST & (jb & BUF) & F8 & FRM & FP).
  destruct (bfr_at mc MU WM) as (F0 & F80 & FH & _).
  unfold frc in F8.
  eapply (cw_end gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o F lo S lp mL j0
            [C8 (Z_to_bv 64 CW_TBL); C8 (Z_to_bv 64 (18446744073709551615 - CW_TBL)); C8 (Z_to_bv 64 (CW_GREC + 16));
             C8 (Z_to_bv 64 (18446744073709551615 - (CW_GREC + 16))); C8 (Z_to_bv 64 CW_GREC);
             C8 (Z_to_bv 64 0x1045f); C8 (Z_to_bv 64 (CW_GREC + 24 + 56 * c)); C8 W]);
    [lia | lia | reflexivity | exact MI | | exact WM | exact ST | exact FRM | exact FP | exact F0 | exact F8 | exact F80
    | exact BUF | exact FH].
  eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. lia.
Qed.

Definition at_join (c : Z) : machine_state -> Prop := fun ms' =>
  exists (xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 : word)
         (Fc : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ms' = OS 0x14e90 c xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5
            xt6 Fc fc m /\
    oinv c m Fc fc.

Lemma oinv_gen : forall c mc m' Fc fc Fc' fc' jb', oinv c mc Fc fc -> mem_inv rsegs m' -> munch FI mc m' ->
  wmono rsegs mc m' -> stk rsegs m' lo S -> rw_cells rsegs m' (S + 88) [CB 16 jb'] -> frm0 fc' -> fpr F Fc' ->
  oinv c m' Fc' fc'.
Proof.
  intros c mc m' Fc fc Fc' fc' jb' (MI & MU & WM & ST & _ & F8 & _ & _) MI2 MU2 WM2 ST2 BUF2 FRM2 FP2.
  split; [exact MI2|]. split.
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
  split; [exact (wmono_trans rsegs _ _ _ WM WM2)|]. split; [exact ST2|].
  split; [exists jb'; exact BUF2|]. split; [|split; [exact FRM2 | exact FP2]].
  eapply rw_cells_transport; [exact F8 | exact MU2 | exact WM2 | cbn [frc disjoint_from cells_size csize Nat.add]; lia].
Qed.

Lemma oinv_void : forall c mc m' Fc fc, oinv c mc Fc fc -> munch [(lo, S)] mc m' -> wmono rsegs mc m' ->
  mem_inv rsegs m' -> stk rsegs m' lo S -> oinv c m' Fc fc.
Proof.
  intros c mc m' Fc fc HI MU2 WM2 MI2 ST2.
  pose proof HI as (_ & _ & _ & _ & (jb & BUF) & _ & FRM & FP).
  apply (oinv_gen c mc m' Fc fc Fc fc jb HI MI2); [| exact WM2 | exact ST2 | tpc BUF MU2 WM2 | exact FRM | exact FP].
  eapply munch_weaken; [|exact MU2]. unfold sub_fp. cbn [outside]. intros x Hx. lia.
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
  rewrite length_le8. dj.
Qed.

Lemma ncl_at : forall mc, munch FW mL mc -> ro_cells rsegs mc (CW_GREC + 8) [C4 (Z_to_bv 64 (Z.of_nat (length calls)))].
Proof.
  intros mc MU. apply bytes_ro4. eapply bytes_low; [exact HNC | exact MU | exact dFW |].
  rewrite length_le4. unfold CW_GREC. lia.
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

Lemma grec_al : forall c, 0 <= c < 17 ->
  bv_unsigned (Z_to_bv 64 (CW_GREC + 56 * c + 16)) <> 0 /\ bv_unsigned (Z_to_bv 64 (CW_GREC + 56 * c + 16)) mod 8 = 0.
Proof.
  intros c Hc. unfold CW_GREC. rewrite unsigned_lit by lia. split; [lia|].
  replace (213032 + 56 * c + 16) with ((26631 + 7 * c) * 8) by lia. apply Z.mod_mul. lia.
Qed.

(* 0x14e34: the per-kind check of the call's verb (kinds 20, 17, 0), then the join point 0x14e90. *)
Lemma kinds : forall c cl xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs10 xs11
    xt3 xt4 xt5 xt6 Fc fc mc,
  nth_error calls (Z.to_nat c) = Some cl -> 0 <= c < 16 -> oinv c mc Fc fc ->
  evt rsegs (at_join c) (OS 0x14e34 c xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2
                          (Z_to_bv 64 (CW_GREC + 56 * c + 16)) xs5 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 Fc fc mc).
Proof.
  intros c cl xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6
    Fc fc mc Hc C0 HI.
  destruct (call_of c cl Hc ltac:(lia)) as [HA HK].
  pose proof HA as (A0 & A1 & A2 & A3 & A4 & A5 & A6).
  pose proof HI as (MI & MU & WM & ST & (jb & BUF) & F8 & FRM & FP).
  destruct (bfr_at mc MU WM) as (F0 & F80 & FH & G1 & G2).
  pose proof (arr_at mc MU) as RA.
  pose proof (rc_at c cl mc HA MU) as RC.
  destruct HK as (K1 & K2 & K3 & K4).
  assert (NA : bytes_at rsegs mc (CW_GREC + 56 * c + 16 + 4) (le4 (Z_to_bv 64 (Z.of_nat (length (snd cl)))))).
  { eapply bytes_low; [exact A3 | exact MU | exact dFW | rewrite length_le4; lia]. }
  pose proof (grec_al c ltac:(lia)) as (AL1 & AL2).
  assert (GREC : CW_GREC = 213032) by reflexivity.
  unfold frc in F8.
  zstep. rewrite (sx32_lit (fst cl)) by lia.
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
      - intros H4. destruct (HA1 ltac:(lia)) as [N1 N2]. split; [exact N1|]. split; [exact N2|].
        destruct (HWS 4 ltac:(lia)) as (_ & _ & _ & Hp & _). exact Hp.
      - lia.
      - rewrite !unsigned_lit by lia. try unfold CALL_NARGS. rewrite L4 in NA. exact NA.
      - rewrite !unsigned_lit by lia. unfold outside_stack; try unfold CALL_NARGS. dj.
      - exact AL1.
      - exact AL2.
      - intros _. rewrite !unsigned_lit by lia. exact P3.
      - reflexivity.
      - exact V4. }
    intros ms' (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & E & MU2 & WM2 & MI2 & ST2).
    subst ms'. rewrite unsigned_lit in MU2, ST2 by lia. fix_ret.
    apply evt_done. unfold at_join. do 28 eexists. split; [reflexivity|].
    exact (oinv_void c mc m' Fc fc HI MU2 WM2 MI2 ST2).
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
        - intros H2. exact (HA1 ltac:(lia)).
        - lia.
        - rewrite !unsigned_lit by lia. try unfold CALL_NARGS. rewrite L3 in NA. exact NA.
        - rewrite !unsigned_lit by lia. unfold outside_stack; try unfold CALL_NARGS. dj.
        - exact AL1.
        - exact AL2.
        - intros _. rewrite !unsigned_lit by lia. exact P1.
        - intros _. rewrite !unsigned_lit by lia. exact P2.
        - reflexivity.
        - exact V1.
        - exact V2. }
      intros ms' (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & Ft & fc' & m' &
                  E & MU2 & WM2 & MI2 & FRM2 & FP2 & ST2).
      subst ms'. rewrite unsigned_lit in MU2, ST2 by lia. fix_ret.
      zstep.
      apply evt_done. unfold at_join. do 28 eexists. split; [reflexivity|].
      pose proof (oinv_void c mc m' Fc fc HI MU2 WM2 MI2 ST2) as (H1 & H2 & H3 & H4 & H5 & H6 & _ & H8).
      split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
      split; [exact H6|]. split; [exact FRM2|]. intros k Hk. rewrite (FP2 k Hk). exact (H8 k Hk).
    + zc Q17.
      zstep. if_cases Q0.
      * apply evt_done. unfold at_join. do 28 eexists. split; [reflexivity | exact HI].
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
          - intros H3. exact (HA1 ltac:(lia)).
          - lia.
          - rewrite !unsigned_lit by lia. try unfold CALL_NARGS. rewrite L4 in NA. exact NA.
          - rewrite !unsigned_lit by lia. unfold outside_stack; try unfold CALL_NARGS. dj.
          - exact AL1.
          - exact AL2.
          - intros _. rewrite !unsigned_lit by lia. exact P2.
          - intros _. rewrite !unsigned_lit by lia. exact P3.
          - reflexivity.
          - exact V2.
          - exact V3. }
        intros ms' (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & E & MU2 & WM2 & MI2
                    & ST2).
        subst ms'. rewrite unsigned_lit in MU2, ST2 by lia. fix_ret.
        zstep.
        apply evt_done. unfold at_join. do 28 eexists. split; [reflexivity|].
        exact (oinv_void c mc m' Fc fc HI MU2 WM2 MI2 ST2).
Qed.

(* One call c: 0x14c70 (the checks on c and on the fields of calls[c]), the item loop when nargs > 0, the
   per-kind check, to 0x14e90. *)
Lemma percall : forall c xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs10 xs11
    xt3 xt4 xt5 xt6 Fc fc mc,
  0 <= c < Z.of_nat (length calls) -> oinv c mc Fc fc ->
  evt rsegs (at_join c) (OS 0x14c70 c xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs10
                          xs11 xt3 xt4 xt5 xt6 Fc fc mc).
Proof.
  intros c xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6
    Fc fc mc HC HI.
  assert (GREC : CW_GREC = 213032) by reflexivity.
  assert (TBL : CW_TBL = 141520) by reflexivity.
  destruct (nth_error calls (Z.to_nat c)) as [cl|] eqn:Hc; [|apply nth_error_None in Hc; lia].
  assert (C16 : 0 <= c < 16) by lia.
  destruct (call_of c cl Hc ltac:(lia)) as [HA HK].
  pose proof HA as (A0 & A1 & A2 & A3 & A4 & A5 & A6).
  pose proof HI as (MI & MU & WM & ST & (jb & BUF) & F8 & FRM & FP).
  pose proof (rc_at c cl mc HA MU) as RC.
  unfold frc in F8.
  zstep. zstep. if_cases Q17.
  { exfalso. zc Q17. lia. }
  zstep. zstep. zstep.
  match goal with |- context [Z_to_bv 64 (?e1 mod 18446744073709551616 - ?e2 mod 18446744073709551616)] =>
    replace (e1 mod 18446744073709551616 - e2 mod 18446744073709551616) with (56 * c)
      by (rewrite !Z.shiftl_mul_pow2 by lia; change (2 ^ 6) with 64; change (2 ^ 3) with 8;
          rewrite !Z.mod_small by lia; lia)
  end.
  zstep. zstep. if_cases Q1.
  { exfalso. zc Q1. lia. }
  zstep. zstep.
  replace (CW_GREC + 16 + 56 * c) with (CW_GREC + 56 * c + 16) by lia.
  zstep.
  rewrite (sx32_lit (fst cl)) by lia.
  zstep. zstep. if_cases Q2.
  { exfalso. zc Q2. lia. }
  zstep.
  replace (Z.shiftl (fst cl) 3) with (8 * fst cl) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep. zstep. if_cases Q3.
  { exfalso. zc Q3. lia. }
  zstep.
  rewrite (sx32_lit (Z.of_nat (length (snd cl)))) by lia.
  zstep. if_cases QZ.
  - eapply kinds; [exact Hc | lia | exact HI].
  - zc QZ.
    eapply evt_cut.
    { eapply (cw_items_loop SSP SCS ATOI SNP SC) with (m0 := mc) (lo := lo) (S := S) (r := r) (fn := fst cl)
        (nargs := Z.of_nat (length (snd cl))) (ws := ws) (W := W) (arr := arr) (lp := lp)
        (x16 := Z_to_bv 64 (18446744073709551615 - CW_TBL)) (x24 := Z_to_bv 64 (CW_GREC + 16))
        (x32 := Z_to_bv 64 (18446744073709551615 - (CW_GREC + 16))) (x40 := Z_to_bv 64 CW_GREC)
        (can := can) (jb := jb) (F := F)
        (s4 := Z_to_bv 64 (CW_GREC + 56 * c + 16)) (s9 := Z_to_bv 64 c).
      - lia.
      - exact IE.
      - lia.
      - exact RR.
      - lia.
      - exact A4.
      - rewrite unsigned_lit by lia. lia.
      - rewrite unsigned_lit by lia. replace (CW_GREC + 56 * c + 16 + 8) with (CW_GREC + 24 + 56 * c) by lia. exact F8.
      - eapply bytes_low; [exact (HTB (fst cl) A4) | exact MU | exact dFW | rewrite length_le8; lia].
      - exact (rw_cells_c8_bytes _ _ _ (proj1 (proj2 (proj2 (proj2 (bfr_at mc MU WM)))))).
      - exact (rw_cells_c8_bytes _ _ _ (proj2 (proj2 (proj2 (proj2 (bfr_at mc MU WM)))))).
      - rewrite unsigned_lit by lia. eapply bytes_low; [exact A3 | exact MU | exact dFW | rewrite length_le4; lia].
      - rewrite unsigned_lit by lia. dj.
      - eapply bytes_at_transport; [exact HWA | exact MU | rewrite length_le8; dj].
      - dj.
      - exact HA1.
      - intros k Hk. pose proof (lowp_tp _ mL mc lo _ _ _ (HWS k Hk) MU dFW) as Hl.
        split; [exact (lowp_ptr lo S mc _ _ _ Hl ltac:(lia))|].
        destruct Hl as (_ & _ & _ & _ & _ & HN & _). exact HN.
      - eapply bytes_low; [exact (proj1 HL) | exact MU | exact dFW | rewrite length_app; cbn [length]; lia].
      - exact (proj1 (proj2 HL)).
      - pose proof (proj2 (proj2 HL)). dj.
      - exact HLnz.
      - intros a i Ha Hi y Hy.
        destruct HK as (K1 & _).
        assert (Ex : nth_error (snd cl) (Z.to_nat a) = Some (nth (Z.to_nat a) (snd cl) [])) by (apply nth_error_nth'; lia).
        pose proof (K1 _ _ _ Ex Hi y Hy) as Exy. rewrite <- Exy.
        destruct (A6 _ _ Ex) as (p & Hp). rewrite Z2Nat.id in Hp by lia. rewrite unsigned_lit by lia.
        exact (lowp_ptr lo S mc _ _ _ (lowp_tp _ mL mc lo _ _ _ Hp MU dFW) ltac:(lia)).
      - intros mc' MU'. apply TMW. eapply munch_trans; [exact MU|].
        eapply munch_weaken; [|exact MU']. unfold sub_fp. cbn [outside]. intros x Hx. lia.
      - exact MI.
      - apply munch_refl.
      - apply wmono_refl.
      - exact ST.
      - exact BUF.
      - exact FRM.
      - exact FP. }
    intros ms' PO. unfold cw_items_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 &
                    y18 & y19 & y20 & y21 & y22 & y23 & Fc' & fc' & m' & jb' & E & MI2 & MU2 & WM2 & ST2 & BUF2 & FRM2
                    & FP2).
    subst ms'.
    eapply kinds; [exact Hc | lia |].
    exact (oinv_gen c mc m' Fc fc Fc' fc' jb' HI MI2 MU2 WM2 ST2 BUF2 FRM2 FP2).
Qed.

(* The loop over the recorded calls, 0x14c70 to free's entry. *)
Lemma oloop : forall n c xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs10 xs11
    xt3 xt4 xt5 xt6 Fc fc mc,
  n = Z.to_nat (Z.of_nat (length calls) - c) -> 0 <= c < Z.of_nat (length calls) -> oinv c mc Fc fc ->
  evt rsegs Qb (OS 0x14c70 c xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs10 xs11
                 xt3 xt4 xt5 xt6 Fc fc mc).
Proof.
  induction n as [|n IH];
    intros c xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6
      Fc fc mc HN HC HI; [lia|].
  assert (GREC : CW_GREC = 213032) by reflexivity.
  eapply evt_cut; [eapply percall; [exact HC | exact HI] |].
  intros ms' (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 &
              y18 & y19 & y20 & y21 & y22 & y23 & y24 & Fc' & fc' & m' & E & HI'). subst ms'.
  destruct HI' as (MI' & MU' & WM' & ST' & (jb' & BUF') & F8' & FRM' & FP').
  pose proof (ncl_at m' MU') as NC.
  unfold frc in F8'.
  zstep. zstep.
  rewrite (sx32_lit (Z.of_nat (length calls))) by lia.
  zstep. zstep. zstep. zstep.
  replace (CW_GREC + 24 + 56 * c + 56) with (CW_GREC + 24 + 56 * (c + 1)) in F8' by lia.
  zstep. if_cases QL.
  - zc QL. rewrite ?signed_lit in QL by lia.
    eapply IH; [lia | lia |].
    split; [exact MI'|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact ST'|].
    split; [exists jb'; exact BUF'|]. split; [unfold frc; exact F8'|]. split; [exact FRM' | exact FP'].
  - eapply (end_ok (c + 1)).
    split; [exact MI'|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact ST'|].
    split; [exists jb'; exact BUF'|]. split; [unfold frc; exact F8'|]. split; [exact FRM' | exact FP'].
Qed.

(* The loop entry 0x14c70 with c = 0 (at least one recorded call). *)
Lemma loop_entry : forall xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs10 xs11
    xt3 xt4 xt5 xt6 fc,
  mem_inv rsegs mL -> frm0 fc -> 0 < Z.of_nat (length calls) ->
  evt rsegs Qb (OS 0x14c70 0 xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs10 xs11
                 xt3 xt4 xt5 xt6 F fc mL).
Proof using SSP SCS ATOI SNP SC ADD CHAIN PIN LO IE SPH RR HOK NCL FRA FR8 FRB BUF0 FRH GG GU HTB HNC HCA HWA HWB HA1
  HWS HL HLnz TM STL.
  intros xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 fc
    MI FRM HC.
  eapply oloop; [reflexivity | lia |].
  split; [exact MI|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact STL|].
  split; [exists jb0; exact BUF0|]. split; [exact FR8|]. split; [exact FRM | intros k _; reflexivity].
Qed.

End Body.

(* check_words from joined's return 0x14c10 (a0 = the line lp, s1 = r) to free's entry. *)
Theorem cw_body :
  strspn_contract -> strcspn_contract -> atoi_contract -> snprintf_contract -> strcmp_contract ->
  check_words_add_contract -> check_words_chain_contract -> check_words_pin_set_contract ->
  forall (gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o : word) (F : bvmap 5 word)
         (mJ : word -> option byte) (lo S r : Z) (ws : list (list byte)) (wpw : list word) (W arr lp can : word)
         (calls : list (Z * list (list byte))) (j0 j8 j16 j24 j32 j40 j48 j56 j72 j80 jb0 : list byte)
         (xra xt0 xt1 xt2 xs0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word)
         (fc : bv 32),
  lo + 8272 <= S -> 0x54f98 <= lo -> S + 208 < 2 ^ 63 -> 0 <= r <= 64 ->
  Forall (call_words_ok r ws) calls -> (length calls <= 16)%nat ->
  rw_cells rsegs mJ S [CB 8 j0] ->
  rw_cells rsegs mJ (S + 8) [CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; C8 W; CB 8 j72] ->
  rw_cells rsegs mJ (S + 80) [CB 8 j80] -> rw_cells rsegs mJ (S + 88) [CB 16 jb0] ->
  rw_cells rsegs mJ (S + 104)
    [C8 s11o; C8 s10o; C8 s9o; C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  rw_cells rsegs mJ 0x22d40 [C8 (Z_to_bv 64 0x54730)] -> rw_cells rsegs mJ 0x54730 [C8 can] ->
  bytes_at rsegs mJ 0x22cf8 (le8 (Z_to_bv 64 CW_GREC)) ->
  (forall fn, 0 <= fn < 26 -> bytes_at rsegs mJ (CW_TBL + 8 * fn) (le8 (Z_to_bv 64 (cw_tp fn)))) ->
  bytes_at rsegs mJ (CW_GREC + 8) (le4 (Z_to_bv 64 (Z.of_nat (length calls)))) ->
  (forall i c, nth_error calls i = Some c -> call_at_a mJ lo (CW_GREC + 16 + 56 * Z.of_nat i) c) ->
  bytes_at rsegs mJ (bv_unsigned W + 16) (le8 arr) -> S + 208 <= bv_unsigned W + 16 ->
  (0 < r -> bv_unsigned arr <> 0 /\ bv_unsigned arr mod 8 = 0) ->
  (forall k, 0 <= k < r ->
     lowp lo mJ (bv_unsigned arr + 8 * k) (nth (Z.to_nat k) wpw (Z_to_bv 64 0)) (nth (Z.to_nat k) ws [])) ->
  bytes_at rsegs mJ (bv_unsigned lp) (RecFacts.join_sp ws ++ [NUL]) -> ~ In NUL (RecFacts.join_sp ws) ->
  bv_unsigned lp + Z.of_nat (length (RecFacts.join_sp ws)) + 1 <= lo -> bv_unsigned lp <> 0 ->
  MemNorm.task_mem rsegs mJ -> stk rsegs mJ lo S -> mem_inv rsegs mJ -> frm0 fc ->
  evt rsegs (cw_body_post gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o F lo S lp mJ)
    (MS (mkR xra (Z_to_bv 64 S) gp tp xt0 xt1 xt2 xs0 (Z_to_bv 64 r) lp xa1 xa2 xa3 xa4 xa5 xa6 xa7
             xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 0x14c10) fc None mJ (seg_rom rsegs)).
Proof.
  intros SSP SCS ATOI SNP SC ADD CHAIN PIN gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o F
    mJ lo S r ws wpw W arr lp can calls j0 j8 j16 j24 j32 j40 j48 j56 j72 j80 jb0
    xra xt0 xt1 xt2 xs0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 fc
    LO IE SPH RR HOK NCL FA F8 FB BUF0 FRH GG GU GOT HTB HNC HCA HWA HWB HA1 HWS HL1 HL2 HL3 HLnz TM ST MI FRM.
  assert (GREC : CW_GREC = 213032) by reflexivity.
  pose proof (munch_refl [(S + 8, S + 80)] mJ) as MU.
  pose proof (wmono_refl rsegs mJ) as WM.
  assert (D8 : disjoint_from [(S + 8, S + 80)] 0 lo) by dj.
  assert (WV8 : forall x : word, ~ outside [(S + 8, S + 80)] (bv_unsigned x) -> wview rsegs mJ x <> None).
  { intros x Hx. cbn [outside] in Hx. apply (rw_wv mJ (S + 8) _ x F8). cbn [cells_size csize Nat.add]. lia. }
  pose proof (bytes_ro8 _ _ _ GOT) as RGOT.
  pose proof (bytes_ro4 _ _ _ HNC) as RNC.
  zstep. zstep. zstep. zstep.
  rewrite (sx32_lit (Z.of_nat (length calls))) by lia.
  zstep. zstep. if_cases QN.
  - zify_cond QN. rewrite ?signed_lit in QN by lia.
    eapply (cw_end gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o F lo S lp mJ j0
              [CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; C8 (Z_to_bv 64 CW_GREC); CB 8 j48; CB 8 j56; C8 W]);
      [lia | lia | reflexivity | eassumption | | eassumption | eassumption | exact FRM | intros k _; reflexivity
      | eassumption | exact F8 | eassumption | eassumption | eassumption].
    eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. lia.
  - zify_cond QN.
    repeat match goal with H : context [bv_signed (Z_to_bv 64 (Z.of_nat (length calls)))] |- _ =>
      rewrite signed_lit in H by lia end.
    do 18 zstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => set (mS := m1) in * end.
    clearbody mS.
    eapply evt_mono.
    { eapply (loop_entry gp tp rao s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o F mS lo S r ws wpw W arr lp can
                calls j0 j80 jb0 SSP SCS ATOI SNP SC ADD CHAIN PIN LO IE SPH RR HOK NCL).
      - exact FA.
      - exact F8.
      - exact FB.
      - exact BUF0.
      - exact FRH.
      - exact GG.
      - exact GU.
      - intros fn Hfn. eapply bytes_low; [exact (HTB fn Hfn) | exact MU | exact D8 | rewrite length_le8; unfold CW_TBL; lia].
      - exact HNC.
      - intros i c E. exact (call_tp _ mJ mS lo _ c (HCA i c E) MU D8).
      - exact HWA.
      - exact HWB.
      - exact HA1.
      - intros k Hk. exact (lowp_tp _ mJ mS lo _ _ _ (HWS k Hk) MU D8).
      - split; [exact HL1 | split; [exact HL2 | exact HL3]].
      - exact HLnz.
      - exact (task_mem_fw _ mJ mS TM WV8 MU).
      - exact ST.
      - exact MI.
      - exact FRM.
      - lia. }
    intros ms' Hq. unfold Qb, cw_body_post in Hq |- *.
    destruct Hq as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17
      & y18 & y19 & y20 & y21 & y22 & y23 & y24 & y25 & Fq & fq & mq & E & MIq & MUq & WMq & STq & FHq & FRMq & FPq).
    exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22,
      y23, y24, y25, Fq, fq, mq.
    split; [exact E|]. split; [exact MIq|]. split.
    { apply (munch_trans _ mJ mS mq); [|exact MUq].
      eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    split; [exact (wmono_trans rsegs _ _ _ WM WMq)|]. split; [exact STq|]. split; [exact FHq|].
    split; [exact FRMq | exact FPq].
Qed.
