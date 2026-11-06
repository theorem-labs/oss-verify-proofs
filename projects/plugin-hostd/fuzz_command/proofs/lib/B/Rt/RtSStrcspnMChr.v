(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the Section Strchrnul of lib/R_strchr.v (musl strchrnul with c <> 0) readdressed to plugin-hostd/fuzz_command's ASan image (rsegs := tfibsegs, strchrnul 0x9f0b4 = plain 0x20c84 + 0x7e430), without mem_inv: the two word-loop constants (0x10370, 0x10358) are ro_cells premises; the entry lemma states only the c <> 0 path, because on the ASan image c = 0 calls the strlen interceptor, which the strcspn walk steps through by its own contract. *)
(* Modified by Theorem Labs, 2026-10: moved from this harness's lib/A/Rt/RtSStrcspnMChr.v to plugin-hostd/fuzz_command's ASan+UBSan image (fuzz_command.asan-ubsan): module paths lib/A to lib/B, and the addresses by the name-keyed A-to-B address map, each re-read on that image: strchrnul 0x9ec10 (= plain 0x20c84 + 0x7df8c) and its inner addresses; the two word-loop constants stay at 0x10370 and 0x10358 with the same bytes; the proof text is unchanged. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import R_strlen R_memchr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import strchrnul_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtSStrcspnMImg.
(* [comment removed for export] *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Step.zstep ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Dieta54.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require AndN.   (* [comment removed for export] *)
Local Ltac lia ::= OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac chkp_cleanup :=
  repeat
    (repeat match goal with
       | [ H : (0 <= ?x < _)%Z |- _ ] =>
          destruct H;
          try (lazymatch type of H with (* [comment removed for export] *)
            | (0 <= x < _)%Z => clear H (* [comment removed for export] *)
          end)
          (* [comment removed for export] *)
       end;
     repeat match goal with
       | [ H : (?x <> ?x)%Z -> _ |- _ ] => clear H
       | [ H : (?x < ?x)%Z -> _ |- _ ] => clear H
       | [ H : ?T -> _, H' : ~?T |- _ ] => clear H
       | [ H : ~?T -> _, H' : ?T |- _ ] => clear H
       | [ H : ?A -> (?x <> ?x)%Z -> _ |- _ ] => clear H
       | [ H : ?A -> (?x < ?x)%Z -> _ |- _ ] => clear H
       | [ H : ?A -> ?B -> _, H' : ~?B |- _ ] => clear H
       | [ H : ?A -> ~?B -> _, H' : ?B |- _ ] => clear H
       | [ H : (0 < ?x)%Z -> _, H' : (?x < 0)%Z |- _ ] => clear H
       | [ H : (?x < 0)%Z -> _, H' : (0 < ?x)%Z |- _ ] => clear H
       | [ H : ?A -> (0 < ?x)%Z -> _, H' : (?x < 0)%Z |- _ ] => clear H
       | [ H : ?A -> (?x < 0)%Z -> _, H' : (0 < ?x)%Z |- _ ] => clear H
       | [ H : (0 <= ?x)%Z -> _, H' : (?x < 0)%Z |- _ ] => clear H
       | [ H : (?x <= 0)%Z -> _, H' : (0 < ?x)%Z |- _ ] => clear H
       | [ H : ?A -> (0 <= ?x)%Z -> _, H' : (?x < 0)%Z |- _ ] => clear H
       | [ H : ?A -> (?x <= 0)%Z -> _, H' : (0 < ?x)%Z |- _ ] => clear H
       | [ H : (0 < ?x)%Z -> _, H' : (?x <= 0)%Z |- _ ] => clear H
       | [ H : (?x < 0)%Z -> _, H' : (0 <= ?x)%Z |- _ ] => clear H
       | [ H : ?A -> (0 < ?x)%Z -> _, H' : (?x <= 0)%Z |- _ ] => clear H
       | [ H : ?A -> (?x < 0)%Z -> _, H' : (0 <= ?x)%Z |- _ ] => clear H
       | [ H : (?x < ?y)%Z -> _, H' : ?x = ?y |- _ ] => clear H
       | [ H : (?x < ?y)%Z -> _, H' : ?y = ?x |- _ ] => clear H
       | [ H : ?A -> (?x < ?y)%Z -> _, H' : ?x = ?y |- _ ] => clear H
       | [ H : ?A -> (?x < ?y)%Z -> _, H' : ?y = ?x |- _ ] => clear H
       | [ H : ?x = ?y -> _, H' : (?x < ?y)%Z |- _ ] => clear H
       | [ H : ?x = ?y -> _, H' : (?y < ?x)%Z |- _ ] => clear H
       | [ H : ?A -> ?x = ?y -> _, H' : (?x < ?y)%Z |- _ ] => clear H
       | [ H : ?A -> ?x = ?y -> _, H' : (?y < ?x)%Z |- _ ] => clear H
       end;
     repeat match goal with
       | [ H : ?x = ?x -> ?Q |- _ ] => specialize (H eq_refl)
       | [ H : ?T -> ?Q, H' : ?T |- _ ] => specialize (H H')
       | [ H : ?A -> ?x = ?x -> ?Q |- _ ] => specialize (fun a => H a eq_refl)
       | [ H : ?A -> ?B -> ?Q, H' : ?B |- _ ] => specialize (fun a => H a H')
       | [ H : (0 <= ?x)%Z -> ?Q, H' : (?x <= 0)%Z |- _ ] => specialize (fun pf => H (@Z.eq_le_incl 0 x (eq_sym pf)))
       | [ H : ?A -> (0 <= ?x)%Z -> ?Q, H' : (?x <= 0)%Z |- _ ] => specialize (fun a pf => H a (@Z.eq_le_incl 0 x (eq_sym pf)))
       | [ H : (?x <= 0)%Z -> ?Q, H' : (0 <= ?x)%Z |- _ ] => specialize (fun pf => H (@Z.eq_le_incl 0 x pf))
       | [ H : ?A -> (?x <= 0)%Z -> ?Q, H' : (0 <= ?x)%Z |- _ ] => specialize (fun a pf => H a (@Z.eq_le_incl x 0 pf))
       end).
Local Ltac nia := Zify.zify; chkp_cleanup; xnia zchecker.
Local Ltac liac := Zify.zify; chkp_cleanup; xlia zchecker.
Import ListNotations.
Open Scope bv_scope.


(* the post of strchrnul_c.strchrnul_post over the ASan+UBSan image, without mem_inv *)
Definition cnul_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (bv_unsigned a0 + strchrnul_off (bv_unsigned a1 mod 256) str))
                 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Section Strchrnul.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (str slack : list byte) (lo : Z).
  (* [comment removed for export] *)
  Hypothesis CK1 : ro_cells rsegs m 0x10370%Z [C8 (Z_to_bv 64 72340172838076672%Z)].
  Hypothesis CK2 : ro_cells rsegs m 0x10358%Z [C8 (Z_to_bv 64 9259542123273814144%Z)].
  Hypothesis STR : bytes_at rsegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -16) [C8 s0; C8 ra].
  Hypothesis STK : stk rsegs m lo (bv_unsigned sp + -16).
  Hypothesis MU : munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m0 m.
  Hypothesis WM : wmono rsegs m0 m.
  Hypothesis LO : (0 <= lo <= bv_unsigned sp - 16)%Z.
  Hypothesis CR : (0 < bv_unsigned a1 mod 256)%Z.

  Notation A := (bv_unsigned a0).
  Notation c := ((bv_unsigned a1) mod 256)%Z.
  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Notation r := (Z.of_nat (strchrnul_idx ((bv_unsigned a1) mod 256)%Z str)).
  Notation POST := (cnul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m0).
  (* [comment removed for export] *)
  Notation ST pc x10 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 x10 (Z_to_bv 64 c) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
  Notation CMAGIC := 72340172838076672%Z.      (* [comment removed for export] *)
  Notation HIGHS := 9259542123273814144%Z.     (* [comment removed for export] *)
  Notation ONES := 72340172838076673%Z.       (* [comment removed for export] *)

  #[using="a1 a0"] Lemma full_length : length full = (length str + S (length slack))%nat.
  Proof. rewrite length_app. cbn. lia. Qed.

  #[using="CR STR m"] Lemma A_bound : (0 <= A /\ A + len + 1 + Z.of_nat (length slack) <= 2^64 /\ 0 < c < 256)%Z.
  Proof.
    pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite full_length in B.
    pose proof (Z.mod_pos_bound (bv_unsigned a1) 256). lia.
  Qed.

  #[using="STK FR lo slack str m a1 a0 s0 ra"] Lemma sp_bound : (16 <= bv_unsigned sp /\ bv_unsigned sp < 2^64)%Z.
  Proof.
    pose proof (rw_cells_bound _ _ _ _ FR) as B. cbn in B. destruct STK as [? _].
    pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R. lia.
  Qed.

  #[using="slack a0"] Lemma r_le : (0 <= r <= len)%Z.
  Proof. pose proof (strchrnul_idx_le c str). lia. Qed.

  #[using="NONUL a1 a0"] Lemma full_nth_lt : forall i, (0 <= i < len)%Z ->
    exists b, nth_error full (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z /\ nth_error str (Z.to_nat i) = Some b.
  Proof.
    intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E.
    - exists b. split. { rewrite nth_error_app1 by lia. exact E. }
      split; [|reflexivity]. intros Hb. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.

  #[using="a1 a0"] Lemma full_nth_len : nth_error full (Z.to_nat len) = Some (Z_to_bv 8 0).
  Proof. rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="CR NONUL STR m a0"] Lemma byte_at : forall i, (0 <= i <= r)%Z ->
    exists b, nth_error full (Z.to_nat i) = Some b /\
      (bv_unsigned b = 0%Z <-> i = len) /\
      (i < r -> bv_unsigned b <> c)%Z /\
      (i = r -> r < len -> bv_unsigned b = c)%Z.
  Proof.
    intros i Hi. pose proof r_le as RL. pose proof A_bound as AB.
    destruct (Z.eq_dec i len) as [->|NE].
    - exists (Z_to_bv 8 0). split; [exact full_nth_len|]. split; [split; auto|]. split; [lia|]. intros; lia.
    - destruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hb & Hs). exists b. split; [exact Hn|].
      split. { split; intros; exfalso; [exact (Hb H)| lia]. }
      split. { intros Hir. eapply (strchrnul_idx_before c str (Z.to_nat i)); [lia| exact Hs]. }
      intros -> Hr. destruct (strchrnul_idx_at c str ltac:(lia)) as (b' & Hn' & Hc').
      rewrite Nat2Z.id in Hs. rewrite Hs in Hn'. injection Hn' as <-. exact Hc'.
  Qed.

  (* [comment removed for export] *)
  #[using="CR LO WM MU STK FR STR"] Lemma strchrnul_exit : forall x12 x13 x14 x15 x16 x17,
    evt rsegs POST (ST 0x9ece0 (Z_to_bv 64 (A + r)) x12 x13 x14 x15 x16 x17).
  Proof.
    intros. pose proof sp_bound as SB. pose proof A_bound as AB.
    zstep. zstep. zstep. zstep.
    pose proof (stk_release rsegs _ _ _ _ STK FR ltac:(lia)) as ST'. cbn [cells_size csize Nat.add] in ST'.
    replace (bv_unsigned sp + -16 + Z.of_nat 16)%Z with (bv_unsigned sp) in ST' by lia.
    apply evt_done. unfold cnul_post, strchrnul_off.
    replace (c =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    repeat (lazymatch goal with |- ex _ => eexists end); split; [reflexivity|].
    OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib.AndN.and_splits; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="CR LO WM MU STK FR NONUL STR"] Lemma strchrnul_tail : forall (k : nat) (j : Z) x12 x13 x14 x15 x16 x17,
    Z.to_nat (r - j) = k -> (0 <= j <= r)%Z ->
    evt rsegs POST (ST 0x9ecd0 (Z_to_bv 64 (A + j - 1)) x12 x13 x14 x15 x16 x17).
  Proof.
    induction k as [|k IH]; intros j x12 x13 x14 x15 x16 x17 Hk Hj; pose proof A_bound as AB; pose proof r_le as RL;
      destruct (byte_at j ltac:(lia)) as (b & Hn & Hz & Hlt & Heq); pose proof (byte_range b);
      pose proof (u8ro_read rsegs m A full j b (Z_to_bv 64 (A + j - 1 + 1)) STR Hn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    - (* [comment removed for export] *) assert (Ej : j = r) by lia.
      zstep. zstep. zstep. replace (A + j - 1 + 1)%Z with (A + r)%Z by lia.
      if_cases Kz; zify_cond Kz. { apply strchrnul_exit. }
      zstep. if_cases Kc; zify_cond Kc. { exfalso. apply Kc. apply Heq; [exact Ej|]. destruct (Z.eq_dec r len); [|lia]. exfalso. apply Kz, Hz. lia. }
      apply strchrnul_exit.
    - zstep. zstep. zstep. if_cases Kz; zify_cond Kz. { exfalso. apply Hz in Kz. lia. }
      zstep. if_cases Kc; zify_cond Kc.
      + replace (A + j - 1 + 1)%Z with (A + (j + 1) - 1)%Z by lia. apply (IH (j + 1)%Z); [lia|].
        destruct (Z.eq_dec j r) as [E|]; [|lia]. exfalso. apply Kc, Heq; [exact E|].
        destruct (Z.eq_dec r len); [|lia]. exfalso. assert (bv_unsigned b = 0%Z) by (apply Hz; lia). lia.
      + destruct (Z.eq_dec j r) as [E|NE]. { rewrite E. replace (A + r - 1 + 1)%Z with (A + r)%Z by lia. apply strchrnul_exit. }
        exfalso. exact (Hlt ltac:(lia) Kc).
  Qed.

  (* [comment removed for export] *)
  #[using="CR LO WM MU STK FR NONUL STR"] Lemma strchrnul_tail_entry : forall (i : Z) x10 x12 x13 x14 x15 x17, (0 <= i <= r)%Z ->
    evt rsegs POST (ST 0x9eccc x10 x12 x13 x14 x15 (Z_to_bv 64 (A + i)) x17).
  Proof.
    intros i x10 x12 x13 x14 x15 x17 Hi. pose proof A_bound as AB.
    zstep. replace (A + i + -1)%Z with (A + i - 1)%Z by lia.
    apply (strchrnul_tail (Z.to_nat (r - i)) i); lia.
  Qed.

  (* [comment removed for export] *)
  #[using="CR PAD STR m"] Lemma word_ok : forall i, (0 <= i <= r)%Z -> ((A + i) mod 8 = 0)%Z -> (Z.to_nat i + 8 <= length full)%nat.
  Proof. intros i Hi Hal. pose proof r_le. pose proof A_bound. rewrite full_length. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  #[using="CR NONUL STR m a0"] Lemma clean_word : forall i, (0 <= i <= r)%Z ->
    ~ In 0%Z (map bv_unsigned (firstn 8 (skipn (Z.to_nat i) full))) ->
    ~ In c (map bv_unsigned (firstn 8 (skipn (Z.to_nat i) full))) ->
    (Z.to_nat i + 8 <= length full)%nat ->
    (i + 8 <= r)%Z.
  Proof.
    intros i Hi NZ NC HW. pose proof r_le as RL.
    assert (IN : forall j b, (Z.to_nat i <= j < Z.to_nat i + 8)%nat -> nth_error full j = Some b ->
                 In (bv_unsigned b) (map bv_unsigned (firstn 8 (skipn (Z.to_nat i) full)))).
    { intros j b Hj Hn. apply in_map. apply nth_error_In with (n := (j - Z.to_nat i)%nat).
      rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
      rewrite nth_error_skipn, <- Hn. f_equal. lia. }
    destruct (Z.lt_ge_cases r (i + 8)) as [Hlt|]; [|assumption]. exfalso.
    destruct (byte_at r ltac:(lia)) as (b & Hn & Hz & _ & Heq).
    pose proof (IN (Z.to_nat r) b ltac:(lia) Hn) as HIN.
    destruct (Z.eq_dec r len) as [E|NE].
    - apply NZ. rewrite <- (proj2 Hz E) at 1. exact HIN.
    - apply NC. rewrite <- (Heq eq_refl ltac:(lia)). exact HIN.
  Qed.

  (* [comment removed for export] *)
  #[using="CR LO WM MU STK FR PAD NONUL STR"] Lemma strchrnul_words : forall (k : nat) (i : Z) (chunk : list byte) (w14 x15' x16 x17 : word),
    Z.to_nat (r - i) = k -> (0 <= i <= r)%Z -> ((A + i) mod 8 = 0)%Z ->
    chunk = firstn 8 (skipn (Z.to_nat i) full) -> length chunk = 8%nat ->
    ~ In 0%Z (map bv_unsigned chunk) ->
    bv_unsigned w14 = le_val (map bv_unsigned chunk) ->
    x15' = Z_to_bv 64 (c * ONES) ->
    evt rsegs POST (ST 0x9ec78 (Z_to_bv 64 (A + i)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS) w14 x15' x16 x17).
  Proof.
    induction k as [k IH] using lt_wf_ind; intros i chunk w14 x15' x16 x17 Hk Hi Hal Hch CL NZ Hw ->;
      pose proof A_bound as AB; pose proof r_le as RL.
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    pose proof (le_val_range _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia))) as XR. rewrite !length_map, CL in XR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in XR.
    zstep. rewrite Hw.
    replace (Z.lxor (le_val (map bv_unsigned chunk)) (c * ONES)) with (le_val (map (fun b => Z.lxor b c) (map bv_unsigned chunk))).
    2:{ change ONES with ONES64b. rewrite <- ones_8, <- CL, <- (length_map bv_unsigned). symmetry. apply le_val_xor_bcast; [apply bytes_ok_map| lia]. }
    zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      zstep. apply (strchrnul_tail_entry i); lia.
    - apply (haszero64_clang _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia)) ltac:(rewrite !length_map; exact CL)) in K.
      rewrite In0_xor in K.
      pose proof (word_ok i ltac:(lia) Hal) as HW0.
      pose proof (clean_word i ltac:(lia) ltac:(rewrite <- Hch; exact NZ) ltac:(rewrite <- Hch; exact K) HW0) as H8.
      (* [comment removed for export] *)
      assert (Hal8 : ((A + (i + 8)) mod 8 = 0)%Z) by (Z.div_mod_to_equations; lia).
      pose proof (word_ok (i + 8) ltac:(lia) Hal8) as HW.
      pose proof (bytes_at_read rsegs m A full (i + 8) 8 STR ltac:(lia) HW) as RD.
      set (chunk2 := firstn 8 (skipn (Z.to_nat (i + 8)) full)) in RD.
      assert (CL2 : length chunk2 = 8%nat). { subst chunk2. rewrite firstn_length, skipn_length. lia. }
      pose proof (le_val_range _ (bytes_ok_map chunk2)) as WR2. rewrite length_map, CL2 in WR2.
      change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR2.
      zstep. do 5 zstep. replace (A + i + 8)%Z with (A + (i + 8))%Z by lia. rewrite (load8_le_val chunk2 CL2).
      zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        apply (haszero64_clang _ (bytes_ok_map chunk2) ltac:(rewrite length_map; exact CL2)) in K2.
        apply (IH (Z.to_nat (r - (i + 8)))) with (chunk := chunk2); try lia; try reflexivity; try exact CL2; try exact K2.
        apply load8_le_val. exact CL2.
      + zstep. apply (strchrnul_tail_entry (i + 8)); lia.
  Qed.

  (* [comment removed for export] *)
  #[using="CR LO WM MU STK FR PAD NONUL STR CK1 CK2"] Lemma strchrnul_wentry : forall (i : Z) x12 x13 x14 x15 x16 x17,
    (0 <= i <= r)%Z -> ((A + i) mod 8 = 0)%Z ->
    evt rsegs POST (ST 0x9ec4c (Z_to_bv 64 (A + i)) x12 x13 x14 x15 x16 x17).
  Proof.
    intros i x12 x13 x14 x15 x16 x17 Hi Hal. pose proof A_bound as AB. pose proof r_le as RL.
    pose proof (word_ok i Hi Hal) as HW.
    pose proof (bytes_at_read rsegs m A full i 8 STR ltac:(lia) HW) as RD.
    set (chunk := firstn 8 (skipn (Z.to_nat i) full)) in RD.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite firstn_length, skipn_length. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    do 8 zstep. rewrite (load8_le_val chunk CL).
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *) zstep. apply (strchrnul_tail_entry i); lia.
    - apply (haszero64_clang _ (bytes_ok_map chunk) ltac:(rewrite length_map; exact CL)) in K.
      zstep. zstep.
      apply (strchrnul_words (Z.to_nat (r - i)) i chunk); try lia; try reflexivity; try exact CL; try exact K.
      apply load8_le_val. exact CL.
  Qed.

  (* [comment removed for export] *)
  #[using="CR LO WM MU STK FR PAD NONUL STR CK1 CK2"] Lemma strchrnul_head : forall (k : nat) (i : Z) x13 x14 x15 x16 x17,
    Z.to_nat (r - i) = k -> (0 <= i <= r)%Z ->
    evt rsegs POST (ST 0x9ec30 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + i + 1)) x13 x14 x15 x16 x17).
  Proof.
    induction k as [|k IH]; intros i x13 x14 x15 x16 x17 Hk Hi; pose proof A_bound as AB; pose proof r_le as RL;
      destruct (byte_at i ltac:(lia)) as (b & Hn & Hz & Hlt & Heq); pose proof (byte_range b);
      pose proof (u8ro_read rsegs m A full i b _ STR Hn ltac:(lia) eq_refl) as RD.
    - assert (Ei : i = r) by lia.
      zstep. zstep. if_cases Kz; zify_cond Kz. { rewrite Ei. apply strchrnul_exit. }
      zstep. if_cases Kc; zify_cond Kc. { rewrite Ei. apply strchrnul_exit. }
      exfalso. apply Kc, Heq; [exact Ei|]. destruct (Z.eq_dec r len); [|lia]. exfalso. apply Kz, Hz. lia.
    - zstep. zstep. if_cases Kz; zify_cond Kz. { exfalso. apply Hz in Kz. lia. }
      zstep. if_cases Kc; zify_cond Kc.
      { destruct (Z.eq_dec i r) as [E|NE]. { rewrite E. apply strchrnul_exit. } exfalso. exact (Hlt ltac:(lia) Kc). }
      assert (Hir : (i < r)%Z).
      { destruct (Z.eq_dec i r) as [E|]; [|lia]. exfalso. apply Kc, Heq; [exact E|].
        destruct (Z.eq_dec r len); [|lia]. exfalso. assert (bv_unsigned b = 0%Z) by (apply Hz; lia). lia. }
      zstep. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
      + replace (A + i + 2)%Z with (A + (i + 1) + 1)%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        apply (IH (i + 1)%Z); lia.
      + replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        apply (strchrnul_wentry (i + 1)); [lia|]. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="CR LO WM MU STK FR PAD NONUL STR CK1 CK2"] Lemma strchrnul_body : forall x12 x13 x14 x15 x16 x17,
    evt rsegs POST (ST 0x9ec24 a0 x12 x13 x14 x15 x16 x17).
  Proof.
    intros. pose proof A_bound as AB. pose proof r_le as RL.
    zstep. zstep. if_cases Kal; zify_cond Kal.
    - eapply evt_eq. 2:{ apply (strchrnul_wentry 0); [lia|]. revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
      unfold mkR. rewrite Z_to_bv_plus0. reflexivity.
    - zstep. eapply evt_eq. 2:{ apply (strchrnul_head (Z.to_nat r) 0); lia. }
      unfold mkR. rewrite ?Z.add_0_r, ?Z_to_bv_plus0, ?Z_to_bv_bv_unsigned. reflexivity.
  Qed.
End Strchrnul.

(* strchrnul with c <> 0 from its entry on the ASan+UBSan image: the frame of 16 bytes, then the body of the Section *)
Lemma cnul_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  bytes_at rsegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  ro_cells rsegs m 0x10370%Z [C8 (Z_to_bv 64 72340172838076672%Z)] ->
  ro_cells rsegs m 0x10358%Z [C8 (Z_to_bv 64 9259542123273814144%Z)] ->
  (0x606000 <= lo)%Z ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (0 < bv_unsigned a1 mod 256)%Z ->
  evt rsegs (cnul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CM_STRCHRNUL) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST STR NONUL PAD CK1 CK2 HLO LO SEP CR.
  unfold CM_STRCHRNUL.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (zr_word a1) as R1. unfold inr64 in R1.
  carve_frame 16%nat ST.
  zstep. zstep. zstep. zstep.
  replace (Z.land (bv_unsigned a1) 255) with ((bv_unsigned a1) mod 256)%Z.
  2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. }
  pose proof (Z.mod_pos_bound (bv_unsigned a1) 256 ltac:(lia)) as CB.
  zstep. if_cases Kc; zify_cond Kc.
  - exfalso. lia.
  - eapply strchrnul_body; try eassumption; lia.
Qed.
