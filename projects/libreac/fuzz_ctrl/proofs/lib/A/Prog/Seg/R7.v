(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 852 of its 1017 lines of code are new or changed and 2392 lines of the source are left out. *)
(* Segment R7 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): the cut 0x815ec (`beqz a0,8194c`, a0 = n_b the
   build_as result of turn b) and its three exits.
   - n_b != 0: the three validity checks of fuzz_dup (range 52..1492, (n_b-52) >= 36, (n_b-52) divisible by 36 via
     the reciprocal spill *(A+64) = 0xe38f0000) all pass and wrapper_malloc(n_b) is entered.  r7_evt runs the
     register/branch instructions [0x815ec, jal 0x5337c] to the malloc entry; seg_R7_malloc applies the heap-malloc
     contract (API.aa_malloc at as_malloc = 0x5337c, its precondition from SlotInv.fra_call_pre), moves FRA across
     the call with Tac_slot.sl_mid_perm, ENT with ent_call_perm and OUTA with Tac_slot.outa_call, and reaches the
     cut Inv_A81640_at b (its out[] window by Tac_slot.outa_rnb).
   - n_b = 0, b <= 5: the latch to the loop head 0x815cc of turn S b (seg_R7_latch).
   - n_b = 0, b = 6: the tail to the cuts 0x81ac0 / 0x81b10, Seg/R7tail.v's r7_tail_run. *)
(* libreac v1.9.0 (S_R7 IDENTICAL): pcs +0x58 (0x81594 -> 0x815ec; error paths +0xc0 / +0xc8), cut names per
   v190-cutnames-A.tsv, __wrap_malloc at 0x5337c, FRAME_BYTES / FRAME_SHADOW for the frame, the code cell and scratch
   at fr + 3040 / fr + 3056, [A + 208] -> [A + 192] and RXS's [A + 16 / 8 / 192] -> [A + 8 / 0 / 200]. Contract.v's
   errno / OOM flag / client blocks and FrameAPI's AG / RELRO ranges are read off those files, not restated.
   Contract's v1.9.0 malloc asks a per-class bound: Tac_cls.sl_malloc_cls gives it from ENT's 14th conjunct. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
Import ListNotations.
Open Scope Z_scope.

(* n_b = 52 + 36 u, 2 <= u <= 40: a check over each u by computation (ubsan u1_u_cases). *)
Lemma a_u_cases : forall (P : Z -> Prop) (f : Z -> bool), (forall u, f u = true -> P u) ->
  forallb f (map Z.of_nat (seq 2 39)) = true -> forall u, 2 <= u <= 40 -> P u.
Proof.
  intros P f HP Hall u Hu. apply HP. rewrite forallb_forall in Hall. apply Hall.
  apply in_map_iff. exists (Z.to_nat u). split; [lia|]. apply in_seq. lia.
Qed.

(* Goal c = false where c mentions n, with Hu : exists u, n = 52 + 36 u /\ 2 <= u <= 40. *)
Ltac a_by_u_f Hu :=
  let u := fresh "u" in let Hr := fresh "Hr" in
  destruct Hu as (u & -> & Hr); revert u Hr;
  lazymatch goal with
  | |- forall u, _ -> @?e u = false =>
      apply (a_u_cases (fun u => e u = false) (fun u => negb (e u)));
      [intros ? H; apply Bool.negb_true_iff in H; exact H | vm_compute; reflexivity]
  end.
(* Goal c = true (the divisibility test is taken). *)
Ltac a_by_u_t Hu :=
  let u := fresh "u" in let Hr := fresh "Hr" in
  destruct Hu as (u & -> & Hr); revert u Hr;
  lazymatch goal with
  | |- forall u, _ -> @?e u = true =>
      apply (a_u_cases (fun u => e u = true) (fun u => e u));
      [intros ? H; exact H | vm_compute; reflexivity]
  end.

Ltac a_if_false Hu :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false by (symmetry; a_by_u_f Hu)
  end; cbv iota.
Ltac a_if_true Hu :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true by (symmetry; a_by_u_t Hu)
  end; cbv iota.

Lemma r7_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A n : Z),
    s1 = Z_to_bv 64 A -> s8 = Z_to_bv 64 36 -> a0 = Z_to_bv 64 n ->
    ro_cells rsegs m (A + 64) [C8 (Z_to_bv 64 0xe38f0000)] -> 0 <= A -> A + 72 <= 2 ^ 64 ->
    (exists u, n = 52 + 36 * u /\ 2 <= u <= 40) ->
    evt rsegs
      (fun ms' => exists (a1' a2' : word),
         ms' = MS (mkR (Z_to_bv 64 0x81640) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 n) a1' a2' a3 a4 a5 a6 a7
                       (Z_to_bv 64 n) s3 s4 s5 s6 s7 (Z_to_bv 64 36) s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x5337c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815ec) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A n -> -> -> RW HA0 HA1 Hu.
  step. a_if_false Hu.                 (* 815ec beqz a0,8194c  (n != 0) *)
  step.                                (* 815f0 mv s2,a0 *)
  step.                                (* 815f4 addi a0,a0,-1493 *)
  step.                                (* 815f8 li a1,-1441 *)
  step. a_if_true Hu.                  (* 815fc bgeu a0,a1,81604 *)
  step.                                (* 81604 addi a0,s2,-52 *)
  step.                                (* 81608 slli a1,a0,0x30 *)
  step.                                (* 8160c srli a2,a1,0x30 *)
  step. a_if_true Hu.                  (* 81610 bgeu a2,s8,81618 *)
  step.                                (* 81618 ld a2,64(s1) *)
  step.                                (* 8161c mulhu a1,a1,a2 *)
  step.                                (* 81620 srli a1,a1,0x15 *)
  step.                                (* 81624 mul a1,a1,s8 *)
  step.                                (* 81628 sub a0,a0,a1 *)
  step.                                (* 8162c slli a0,a0,0x30 *)
  step. a_if_true Hu.                  (* 81630 beqz a0,81638  (divisible) *)
  step.                                (* 81638 mv a0,s2 *)
  step.                                (* 8163c jal 0x5337c wrapper_malloc *)
  apply evt_done. do 2 eexists. reflexivity.
Qed.

(* ===== the cut and its exits ===== *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_cls Tac_rt2_b2 Tac_rt_b2.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require R7tail.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcEmit RcEmitLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_box_model_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_stack_malloc_c.
From Stdlib Require Import Permutation.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.

(* bytes_at survives a memory change that keeps each byte of its range (mrd at wa x is mbyte at x). *)
Lemma r7_bkeep : forall (mem mem' : word -> option byte) a bs,
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte rsegs mem' x = mbyte rsegs mem x) ->
  bytes_at rsegs mem a bs -> bytes_at rsegs mem' a bs.
Proof.
  intros mem mem' a bs HK (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi).
  change (mbyte rsegs mem' (a + Z.of_nat i) = mbyte rsegs mem (a + Z.of_nat i)).
  apply HK. lia.
Qed.

(* n readable bytes from a are some n-byte list at a. *)
Lemma r7_bytes_ex : forall (m : word -> option byte) (n : nat) a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat n -> exists b, mbyte rsegs m x = Some b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = n.
Proof.
  induction n as [|n IH]; intros a Ha Hn Hrd.
  - exists []. split; [|reflexivity]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (Hrd a ltac:(lia)) as (b0 & Hb0).
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply Hrd; lia)) as (bs & Hbs & Hl).
    exists (b0 :: bs). split; [|cbn [length]; rewrite Hl; reflexivity].
    destruct Hbs as (_ & _ & Hbs). split; [lia|]. split; [cbn [length]; lia|].
    intros [|i] Hi.
    + cbn [nth_error]. replace (a + Z.of_nat 0) with a by lia. exact Hb0.
    + cbn [nth_error]. cbn [length] in Hi. rewrite <- (Hbs i ltac:(lia)). f_equal. f_equal. lia.
Qed.

(* A q64 word as a read-only cell (the load at 0x81618). *)
Lemma r7_q64_ro : forall m A v, q64 m A v -> ro_cells rsegs m A [C8 (Z_to_bv 64 v)].
Proof.
  intros m A v H. split; [split; [exact I | exact I] | cbn [cells_bytes]; rewrite app_nil_r; exact H].
Qed.

(* A spill read off register 9 is at the spill base A of the cut (both hold s1; the spill's base is in range). *)
Lemma r7_spill_at : forall regs mem A off v, rg regs 9 A -> 0 <= A < 2 ^ 47 -> 0 <= off <= 2 ^ 47 ->
  spill regs mem off v -> q64 mem (A + off) v.
Proof.
  intros regs mem A off v Hr HA Hoff (A1 & Hr1 & Hq).
  pose proof (rg_eq64 regs 9 A1 A Hr1 Hr) as Hm.
  pose proof Hq as Hb. unfold q64 in Hb. apply bytes_at_bound in Hb. rewrite length_le8 in Hb.
  assert (E : A1 = A).
  { revert Hm Hb HA Hoff. change (2 ^ 64) with 18446744073709551616. change (2 ^ 47) with 140737488355328.
    intros Hm Hb HA Hoff. Z.div_mod_to_equations. lia. }
  subst A1. exact Hq.
Qed.

(* The registered globals of frame_AG lie in the image's segments, and between r7_AG_LO (the lowest descriptor start,
   computed over FrameAPI's list) and Contract's RELRO_HI (the RELRO end): no address of them is written here. *)
Lemma r7_ag_img : forall a, in_globals AF.frame_AG a -> AC.a_in_img a.
Proof.
  intros a (lo & len & Hin & Hr).
  assert (Hall : forallb (fun p => existsb (fun s => (Z.of_N (seg_base s) <=? fst p) &&
                   (fst p + snd p <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs) AF.frame_AG = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall _ Hin). apply existsb_exists in Hall as (s & Hs & Hb).
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in H1, H2.
  exists s. split; [exact Hs | lia].
Qed.

Definition r7_AG_LO : Z := Eval vm_compute in fold_right (fun p m => Z.min (fst p) m) AC.RELRO_HI AF.frame_AG.

Lemma r7_ag_range : forall a, in_globals AF.frame_AG a -> r7_AG_LO <= a < AC.RELRO_HI.
Proof.
  intros a (lo & len & Hin & Hr).
  assert (Hall : forallb (fun p => (r7_AG_LO <=? fst p) && (fst p + snd p <=? AC.RELRO_HI)) AF.frame_AG = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall _ Hin).
  apply andb_true_iff in Hall as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in H1, H2. lia.
Qed.

(* Every GNU_RELRO block of FrameAPI lies in Contract's page-rounded RELRO range [RELRO_LO, RELRO_HI) (computed over
   the list). *)
Lemma r7_relro_range : forall lo len, In (lo, len) AF.frame_RELRO -> AC.RELRO_LO <= lo /\ lo + len <= AC.RELRO_HI.
Proof.
  intros lo len Hil.
  assert (HR : forallb (fun p => (AC.RELRO_LO <=? fst p) && (fst p + snd p <=? AC.RELRO_HI)) AF.frame_RELRO = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in HR. specialize (HR _ Hil). apply andb_true_iff in HR as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in H1, H2. lia.
Qed.

(* ===== the n_b = 0 latch ===== *)

Lemma r7_zxb_nz : forall h : byte, bv_unsigned h <> 0 -> negb (bv_eqb (zxb h) (Z_to_bv 64 0)) = true.
Proof.
  intros h H. unfold zxb, bv_eqb. pose proof (bv_unsigned_in_range 8 h) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. rewrite !MState.unsigned_lit by lia. apply negb_true_iff, Z.eqb_neq. exact H.
Qed.
Lemma r7_eqb_refl : forall x : word, bv_eqb x x = true.
Proof. intros x. unfold bv_eqb. apply Z.eqb_refl. Qed.

(* A branch whose condition is decided by computation, by reflexivity of bv_eqb (a comparison of a register with
   itself) or by a byte known to be non-zero. *)
Ltac r7_br := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with true by
                (symmetry; first [apply r7_eqb_refl | apply r7_zxb_nz; assumption | reflexivity]); cbv iota
            | replace c with false by (symmetry; reflexivity); cbv iota ]
  | _ => idtac end.
Ltac r7_st := step; r7_br.

(* The latch 0x815ec -> 0x8194c -> 0x815cc at turn S b (n_b = 0, b <= 5): `beqz a0,8194c` taken, then
   `addiw s7,s7,1 ; ld a0,128(s1) ; li a1,7 ; bne s7,a1,815cc`.  The turn index is a literal in each of the six
   cases, so the back branch is decided by computation. *)
Lemma r7_latch_evt : forall (bz : Z), 0 <= bz <= 5 ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A V : Z),
    s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 0 -> s7 = Z_to_bv 64 bz -> 0 <= A -> A + 416 <= 2 ^ 47 ->
    ro_cells rsegs m (A + 128) [C8 (Z_to_bv 64 V)] ->
    evt rsegs
      (fun ms' => exists (a1' a2' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 V) a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 (Z_to_bv 64 (bz + 1)) s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x815cc) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815ec) fc None m (seg_rom rsegs)).
Proof.
  intros bz Hb.
  assert (E : bz = 0 \/ bz = 1 \/ bz = 2 \/ bz = 3 \/ bz = 4 \/ bz = 5) by lia.
  destruct E as [->|[->|[->|[->|[->| ->]]]]];
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A V -> -> -> HA0 HA1 C128;
  (r7_st; r7_st; r7_st; r7_st; r7_st; apply evt_done; do 2 eexists; reflexivity).
Qed.

(* A turn that emits no frame does not move the round-trip state (SlotModel.rt_st: the n = 0 arm), so the identity
   and fragment records of turn S b are those of turn b. *)
Lemma r7_st_skip : forall inp (b : nat), rt_n inp (Z.of_nat b) = 0 -> rt_st inp (S b) = rt_st inp b.
Proof. intros inp b H. cbn [rt_st]. cbv zeta. rewrite H. reflexivity. Qed.

Lemma r7_rid_skip : forall inp (b : nat), rt_n inp (Z.of_nat b) = 0 ->
  RID inp (S b) = RID inp b /\ RFG inp (S b) = RFG inp b.
Proof. intros inp b H. unfold RID, RFG. rewrite (r7_st_skip inp b H). split; reflexivity. Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Local Notation API := (APIf rc).

(* The heap laws this file reads (Contract.a_laws), each taken apart once, here: a Theorem Labs lane's generations add conjuncts
   at every level, so a position of a law is read only in these lemmas. *)
Lemma r7_blocks : forall H mem md p n, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  4096 <= p /\ p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, p <= a < p + n -> app_mem a /\ ~ AC.a_in_img a /\ ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros H mem md p n HAH Hin. destruct (lw_blocks (APIf rc) H mem md p n HAH Hin) as [_ X1 X2 _ Y].
  split; [exact X1|]. split; [exact X2|].
  intros a Ha. destruct (Y a Ha) as (Y1 & _ & Y3 & _ & Y5). split; [exact Y1 | split; [exact Y3 | exact Y5]].
Qed.

Lemma r7_not_owned : forall H mem md a, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (AC.in_blocks H a \/ AC.in_slack H a \/ AC.a_in_fs AC.ASYMS mem a \/ AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END) ->
  ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a /\ ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md (shadow_addr a).
Proof.
  intros H mem md a HAH Ha. destruct (lw_not_owned (APIf rc) H mem md a HAH Ha) as [X Y].
  split; [exact X | exact Y].
Qed.

Lemma r7_client : forall H mem md a, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (AC.in_blocks AC.a_client a -> ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\ (AC.a_in_img a -> ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md (shadow_addr a)).
Proof.
  intros H mem md a HAH.
  decompose [and] (AC.a_laws_client _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md a HAH).
  split; assumption.
Qed.

Lemma r7_fs_present : forall H mem md FS, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  forall a, FS <= a < FS + AC.FS_SIZE -> exists b, mbyte rsegs mem a = Some b.
Proof.
  intros H mem md FS HAH Hw HFS a Ha.
  exact (proj2 (lw_fs_bytes mem FS (lw_fs_ok (APIf rc) H mem md FS HAH Hw HFS) a Ha)).
Qed.

Lemma r7_fs_place : forall H mem md b, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) b -> 0 <= b < 2 ^ 64 ->
  AC.GT <= b /\ b + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ (forall a, b <= a < b + AC.FS_SIZE -> app_mem a).
Proof.
  intros H mem md b HAH Hw Hb. destruct (lw_fs_place (APIf rc) H mem md b HAH Hw Hb) as [X1 X2 _ X4].
  split; [exact X1 | split; [exact X2 | exact X4]].
Qed.

(* Contract.a_new_block (amalloc_ret's new block), taken apart once, here. *)
Lemma r7_new_block : forall Bs owned stklo H q n mem' md', AC.a_new_block Bs owned stklo H q n mem' md' ->
  q <> 0 /\ (forall a, q <= a < q + n -> ~ AC.in_blocks H a) /\ addressable mem' q n.
Proof.
  intros Bs owned stklo H q n mem' md' (X1 & _ & _ & _ & _ & X6 & X7 & _).
  split; [exact X1|]. split; [intros a Ha; exact (proj1 (X6 a Ha)) | exact X7].
Qed.

Lemma r7_mat : forall H mem md md', AsanLift.mat_le md md' ->
  (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md') /\ AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md' = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem md md' Hm. destruct (lw_mat_le (APIf rc) H mem md md' Hm) as [X _ Y _].
  split; [exact X | exact Y].
Qed.

(* The allocator call at 0x8163c (__wrap_malloc 0x5337c, Contract.amalloc_at through the API's aa_malloc), in one
   place: its two per-class premises come from ENT through Tac_cls.sl_malloc_cls with Bc = Bc_of BE, so a later
   change of amalloc_at breaks only this lemma. *)
Lemma r7_malloc : forall g hb mem0 md0 regs mem md n,
  ENT APIf g hb mem0 md0 ->
  AC.a_call_pre AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT API) (AC.aa_stklo AC.ASYMS AsanRTInv.RT API) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT API) AC.AK_MALLOC (g_H g) regs mem md ->
  getr regs 10 = Z_to_bv 64 n -> 0 <= n <= AC.ANMAX ->
  AC.a_live_bytes (g_H g) + AC.a_size n <= AC.ALIVE_MAX -> AC.a_place_room (g_H g) (AC.a_size n) ->
  SR rsegs (mkCfg (mkst regs (Z_to_bv 64 (AC.as_malloc AC.ASYMS)) mem (seg_rom rsegs)) md)
    (AC.amalloc_ret AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT API) (AC.aa_owned AC.ASYMS AsanRTInv.RT API) (AC.aa_stklo AC.ASYMS AsanRTInv.RT API) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT API) AC.AK_MALLOC (g_H g) regs mem md n).
Proof.
  intros g hb mem0 md0 regs mem md n HENT Hpre Ea0 Hn Hlive Hroom.
  destruct (sl_malloc_cls APIf g hb mem0 md0 n HENT) as (BE & _ & _ & Hfit & Hcls & _).
  exact (AC.aa_malloc AC.ASYMS AsanRTInv.RT API (g_H g) regs mem md n (Bc_of BE) Hpre Ea0 Hn Hlive Hroom Hfit Hcls).
Qed.

(* ENT across a callee's a_call_post whose post heap H' is a permutation of hb' ++ g_H g (amalloc_ret's append
   order g_H g ++ [(q, n)], while ENT and the cut 0x81640 use prepend order). Tac_slot.ent_call copied with the
   heap steps changed: the frame clause and the not-owned laws are read on H' (an entry block is a
   block of H' by the permutation), and ENT's image clause, which names hb' ++ g_H g, meets the frame clause's H'
   through Tac_slot.ent_owned_img with the same memory and model on both sides (the AH of hb' ++ g_H g is
   a_laws_perm of the call's AH H'; the stack bottom and the 16 bytes at tp are equal by reflexivity). *)
Lemma ent_call_perm : forall g fr hb hb' H' regs mem md regs' mem' md' touched K,
  ENT APIf g hb mem md -> FRA B APIf ra g fr hb regs mem md ->
  AC.a_call_post AC.ASYMS AsanRTInv.RT
    (AC.aa_AH AC.ASYMS AsanRTInv.RT API) (AC.aa_owned AC.ASYMS AsanRTInv.RT API)
    (AC.aa_stklo AC.ASYMS AsanRTInv.RT API) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT API)
    K (hb ++ g_H g) regs mem md touched H' regs' mem' md' ->
  Permutation (hb' ++ g_H g) H' ->
  0 <= K <= FN_STACK ->
  (forall a, touched a -> app_mem a /\ a < g_S g /\ ~ AC.a_in_img a /\ ~ AC.in_blocks (g_H g) a) ->
  AC.a_errno_kept AC.ASYMS mem mem' ->
  ENT APIf g hb' mem' md'.
Proof.
  intros g fr hb hb' H' regs mem md regs' mem' md' touched K HENT HFRA Hcp Hperm HK Hto Hek.
  pose proof (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwlo & _).
  pose proof HENT as HE0.
  destruct HE0 as (Hasp & Hgtp & HTH & Hfs & Hfz & Hmdl & Hslo & Hshi & Hblk & Himg & Habv & Hshd & Hblks & Hcls).
  assert (HS0 : 0 <= g_S g) by (rewrite <- Hasp; apply (bv_unsigned_in_range 64)).
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API) (hb ++ g_H g) mem md HAH).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  unfold HIGHMEM_BEG in Hhigh.
  pose proof Hcp as Hah'; apply AC.a_call_post_ah in Hah'.
  assert (HahP : AC.aa_AH AC.ASYMS AsanRTInv.RT API (hb' ++ g_H g) mem' md')
    by exact (AC.a_laws_perm _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API) H' (hb' ++ g_H g) mem' md' Hah'
                (Permutation_sym Hperm)).
  pose proof Hcp as Hsk; apply AC.a_call_post_stklo in Hsk.
  pose proof Hcp as Hskh; apply AC.a_call_post_stkhi in Hskh.
  pose proof Hcp as Hoom; apply AC.a_call_post_oom in Hoom.
  assert (Htp : forall i, 0 <= i < 16 ->
            mbyte rsegs mem' (AC.as_tp AC.ASYMS + i) = mbyte rsegs mem (AC.as_tp AC.ASYMS + i))
    by (eapply AC.a_call_post_tp; exact Hcp).
  assert (Hfr : forall a, 0 <= a < 2 ^ 64 ->
            ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (hb ++ g_H g) mem md a ->
            ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API H' mem' md' a ->
            ~ AC.a_window K regs a -> ~ (AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4) ->
            a <> AC.as_oom AC.ASYMS -> ~ touched a ->
            mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a))
    by (eapply AC.a_call_post_frame; exact Hcp).
  (* the callee's window is inside the slot window, so it is below S *)
  assert (Hwin2 : forall a, AC.a_window K regs a ->
            AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < g_S g).
  { intros a Ha. unfold AC.a_window in Ha. unfold FN_STACK in Hwlo.
    rewrite Haspz in Ha. rewrite Haspz in Hwlo. lia. }
  assert (Hoomimg : AC.a_in_img (AC.as_oom AC.ASYMS)) by exact oom_in_img.
  split; [exact Hasp|]. split; [exact Hgtp|]. split; [exact HTH|]. split; [exact Hfs|]. split; [exact Hfz|].
  split.
  { destruct Hmdl as (lz & mt & vm0 & fds0 & pins0 & Hmd & Hfd).
    pose proof Hcp as Hmd'; apply AC.a_call_post_model in Hmd'. destruct Hmd' as (lz1 & mt1 & vm1 & Hmd1).
    exists lz1, mt1, vm1, fds0, pins0. split; [|exact Hfd].
    exact (md_shape_step (g_md g) md md' lz mt vm0 fds0 (m_fs (g_md g)) pins0 lz1 mt1 vm1 Hmd Hmd1). }
  split; [rewrite Hsk; exact Hslo|].
  split; [rewrite Hskh; exact Hshi|].
  split.
  { intros q k i Hin Hni Hi.
    destruct (r7_blocks (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin))) as (Hq4 & Hend & Hall).
    destruct (Hall (q + i) ltac:(lia)) as (Happq & Hnimg & _).
    assert (Hqr : 0 <= q + i < 2 ^ 64)
      by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happq; lia).
    assert (Hinb : AC.in_blocks (g_H g) (q + i)) by (exists q, k; split; [exact Hin | lia]).
    assert (Hinb1 : AC.in_blocks (hb ++ g_H g) (q + i))
      by (exists q, k; split; [apply in_or_app; right; exact Hin | lia]).
    assert (Hinb2 : AC.in_blocks H' (q + i))
      by (exists q, k; split; [apply (Permutation_in _ Hperm); apply in_or_app; right; exact Hin | lia]).
    assert (Hn1 : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (hb ++ g_H g) mem md (q + i))
      by exact (proj1 (r7_not_owned (hb ++ g_H g) mem md (q + i) HAH (or_introl Hinb1))).
    assert (Hn2 : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API H' mem' md' (q + i))
      by exact (proj1 (r7_not_owned H' mem' md' (q + i) Hah' (or_introl Hinb2))).
    assert (Hnw : ~ AC.a_window K regs (q + i)) by (intro Hw; pose proof (Hwin2 _ Hw); lia).
    assert (Hne : ~ (AC.a_errno AC.ASYMS <= q + i < AC.a_errno AC.ASYMS + 4))
      by (intro He; exact (Hnimg (errno_in_img (q + i) He))).
    assert (Hno : q + i <> AC.as_oom AC.ASYMS) by (intro He; apply Hnimg; rewrite He; exact Hoomimg).
    assert (Hnt : ~ touched (q + i)) by (intro Ht; exact (proj2 (proj2 (proj2 (Hto (q + i) Ht))) Hinb)).
    rewrite (proj1 (Hfr (q + i) Hqr Hn1 Hn2 Hnw Hne Hno Hnt)).
    exact (Hblk q k i Hin Hni Hi). }
  split.
  { intros a Hia Ho1 Ho2 Hg He.
    pose proof (img_below_GT a Hia) as Hag. unfold AC.GT in Hag.
    (* the two post lists own the same image bytes: same memory and model on both sides *)
    assert (Ho2h : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API H' mem' md' a)
      by (intro X; apply Ho2;
          exact (proj1 (ent_owned_img APIf H' (hb' ++ g_H g) mem' md' mem' md' a Hah' HahP eq_refl
                          (fun _ _ => eq_refl) Hia) X)).
    assert (Ho2' : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (hb ++ g_H g) mem md a)
      by (intro X; apply Ho2h;
          exact (proj1 (ent_owned_img APIf (hb ++ g_H g) H' mem md mem' md' a HAH Hah' Hsk Htp Hia) X)).
    destruct (Himg a Hia Ho1 Ho2' Hg He) as (Hm0 & Hw0).
    destruct (Z.eq_dec a (AC.as_oom AC.ASYMS)) as [Eo|Eo].
    - subst a. destruct Hek as (_ & Hoomb).
      split; [rewrite Hoomb; exact Hm0|].
      split; intro X; [exact (proj1 Hoom (proj1 Hw0 X)) | exact (proj2 Hw0 (proj2 Hoom X))].
    - destruct (Hfr a ltac:(lia) Ho2' Ho2h ltac:(intro Hw; pose proof (Hwin2 _ Hw); lia) He Eo
                  ltac:(intro Ht; exact (proj1 (proj2 (proj2 (Hto a Ht))) Hia))) as (Hm & Hw).
      split; [rewrite Hm; exact Hm0|].
      split; intro X; [exact (proj1 Hw (proj1 Hw0 X)) | exact (proj2 Hw0 (proj2 Hw X))]. }
  split.
  { intros a Ha.
    assert (Hst : AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < APPMEM_END) by lia.
    assert (Hst' : AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem' md' <= a < APPMEM_END)
      by (rewrite Hsk; lia).
    assert (Hno : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (hb ++ g_H g) mem md a)
      by exact (proj1 (r7_not_owned (hb ++ g_H g) mem md a HAH (or_intror (or_intror (or_intror Hst))))).
    assert (Hno' : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API H' mem' md' a)
      by exact (proj1 (r7_not_owned H' mem' md' a Hah' (or_intror (or_intror (or_intror Hst'))))).
    destruct (Hfr a ltac:(lia) Hno Hno' ltac:(intro Hw; pose proof (Hwin2 _ Hw); lia)
                ltac:(intro He; pose proof (img_below_GT _ (errno_in_img a He)) as X; unfold AC.GT in X; lia)
                ltac:(intro He; pose proof (img_below_GT _ Hoomimg) as X; unfold AC.GT in X; lia)
                ltac:(intro Ht; pose proof (proj1 (proj2 (Hto a Ht))); lia)) as (Hm & Hw).
    destruct (Habv a Ha) as (Hm0 & Hw0).
    split; [rewrite Hm; exact Hm0|].
    split; intro X; [exact (proj1 Hw (proj1 Hw0 X)) | exact (proj2 Hw0 (proj2 Hw X))]. }
  split.
  { intros a Hor.
    assert (Hb0 : 0 <= a)
      by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT a Hi) as X; unfold AC.GT in X|]; lia).
    assert (Hdiv : 0 <= a / 8 <= a) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (Hsh1 : in_shadow (shadow_addr a)).
    { apply shadow_of_app. destruct Hor as [Hi|Hr];
        [pose proof (img_below_GT a Hi) as X; unfold AC.GT, app_mem, LOWMEM_END in *; left; lia
        |unfold app_mem, HIGHMEM_BEG, APPMEM_END in *; right; lia]. }
    assert (Hsr : 0 <= shadow_addr a < 2 ^ 64)
      by (destruct (in_shadow_range (shadow_addr a) Hsh1) as (R1 & R2); lia).
    assert (Hno : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (hb ++ g_H g) mem md (shadow_addr a)).
    { destruct Hor as [Hi|Hr].
      - exact (proj2 (r7_client (hb ++ g_H g) mem md a HAH) Hi).
      - assert (Hst : AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < APPMEM_END) by lia.
        exact (proj2 (r7_not_owned (hb ++ g_H g) mem md a HAH (or_intror (or_intror (or_intror Hst))))). }
    assert (Hno' : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API H' mem' md' (shadow_addr a)).
    { destruct Hor as [Hi|Hr].
      - exact (proj2 (r7_client H' mem' md' a Hah') Hi).
      - assert (Hst' : AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem' md' <= a < APPMEM_END)
          by (rewrite Hsk; lia).
        exact (proj2 (r7_not_owned H' mem' md' a Hah' (or_intror (or_intror (or_intror Hst'))))). }
    destruct (in_shadow_range (shadow_addr a) Hsh1) as (R1 & R2).
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh1.
    destruct (Hfr (shadow_addr a) ltac:(lia) Hno Hno'
                ltac:(intro Hw; pose proof (Hwin2 _ Hw); lia)
                ltac:(intro He; pose proof (img_below_GT _ (errno_in_img _ He)) as X; unfold AC.GT in X; lia)
                ltac:(intro He; pose proof (img_below_GT _ Hoomimg) as X; unfold AC.GT in X;
                      rewrite <- He in X; lia)
                ltac:(intro Ht; pose proof (proj1 (Hto _ Ht)) as X;
                      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X; lia)) as (Hm & _).
    rewrite Hm. exact (Hshd a Hor). }
  split.
  { (* frame batch 2 (ENT's 13th conjunct, Tac_slot.ent_call's last block, on H'): a live block's byte AND its
       shadow byte are unowned before and after the call (a_laws_not_owned; the block is a block of H' by the
       permutation); the shadow byte is not app memory, so it is neither touched nor in the callee's window, and it
       is above the image, so it is neither errno nor the out-of-memory flag. The post's frame clause keeps it. *)
    intros q k i Hin Hni Hi.
    destruct (r7_blocks (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hall).
    destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _).
    assert (Hinb1 : AC.in_blocks (hb ++ g_H g) (q + i))
      by (exists q, k; split; [apply in_or_app; right; exact Hin | lia]).
    assert (Hinb2 : AC.in_blocks H' (q + i))
      by (exists q, k; split; [apply (Permutation_in _ Hperm); apply in_or_app; right; exact Hin | lia]).
    assert (Hsh1 : in_shadow (shadow_addr (q + i))) by exact (shadow_of_app (q + i) Happq).
    destruct (in_shadow_range (shadow_addr (q + i)) Hsh1) as (R1 & R2).
    pose proof Hsh1 as Hsh1'.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh1'.
    assert (Hn1 : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (hb ++ g_H g) mem md (shadow_addr (q + i)))
      by exact (proj2 (r7_not_owned (hb ++ g_H g) mem md (q + i) HAH (or_introl Hinb1))).
    assert (Hn2 : ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API H' mem' md' (shadow_addr (q + i)))
      by exact (proj2 (r7_not_owned H' mem' md' (q + i) Hah' (or_introl Hinb2))).
    destruct (Hfr (shadow_addr (q + i)) ltac:(lia) Hn1 Hn2
                ltac:(intro Hw; pose proof (Hwin2 _ Hw); lia)
                ltac:(intro He; pose proof (img_below_GT _ (errno_in_img _ He)) as X; unfold AC.GT in X; lia)
                ltac:(intro He; pose proof (img_below_GT _ Hoomimg) as X; unfold AC.GT in X;
                      rewrite <- He in X; lia)
                ltac:(intro Ht; pose proof (proj1 (Hto _ Ht)) as X;
                      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X; lia)) as (Hm & _).
    rewrite Hm. exact (Hblks q k i Hin Hni Hi). }
  (* #14 names only the ghost (the entry heap g_H g): the same witness. *)
  exact Hcls.
Qed.

(* Every frame byte is readable: on the real arm it is in the entry-anchored window [S - SLOT_STACK, S), on the side
   arm in FS, whose bytes a_fs_ok makes present. *)
Lemma r7_frame_rd : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  forall a, fr <= a < fr + FRAME_BYTES -> exists b, mbyte rsegs mem a = Some b.
Proof.
  intros g fr hb regs mem md HFRA a Ha.
  pose proof FRAME_BYTES_val as HFBv.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
  - unfold stk in Hwin. destruct Hwin as (_ & _ & Hw). destruct (Hw a ltac:(lia)) as (_ & bb & Hb).
    exists bb. exact Hb.
  - destruct (Hfs a Ha) as (FSa & HFSr & Hwm & Hlo & Hhi).
    exact (r7_fs_present (hb ++ g_H g) mem md FSa HAH Hwm HFSr a ltac:(lia)).
Qed.

(* Where a frame byte lies at 0x815ec (FRA's location disjunction made uniform): on the real stack at or above stklo,
   or in the side stack FS, which is above the image (GT) and below stklo. *)
Definition r7_loc (mem : word -> option byte) (md : Model) (a : Z) : Prop :=
  AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < APPMEM_END \/
  (AC.a_in_fs AC.ASYMS mem a /\ AC.GT <= a < AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md).

(* n_b != 0: r7_evt runs to the malloc entry 0x5337c (sl_run_lib); the heap-malloc contract (aa_malloc at
   as_malloc = 0x5337c, its a_call_pre from fra_call_pre on FRA and ENT after the run) returns to 0x81640 with the new
   block (q, n_b); FRA moves across the call by sl_mid_perm, ENT by ent_call_perm and OUTA by outa_call.  Every byte
   FRA and the exit cut read is kept by a_call_post's frame clause: it is not the allocator's before or after
   (a_laws_not_owned for the frame, its shadow, the saved registers, the spills, the slot window and its shadow, and
   the FakeStack record; a_laws_client for the sink cells and the Shadow of the registered globals; frame_facts for
   RELRO), so not in the new block either (the block's bytes were the allocator's), off errno and the OOM flag, and
   off the malloc window [sp - 4096, sp) (the frame by sl_frame_apart_win, the rest by position).  So the loop-body
   spills (in the caller's save area [A, A + 416), above sp, among them push 7's [A + 144] = fr + 2688 and
   [A + 192] = fr + 2768 and push 9's [A + 280] = fr + 3040 and [A + 240] = fr + 3056), the identity record's and
   our[]'s addressability (frame shadow bytes) and the frame ranges at fr + 2688 (38 bytes), fr + 2768 (72 bytes),
   fr + 3040 (1 byte) and fr + 3056 (32 bytes), readable and writable (frame bytes), are kept, s5 is callee-saved,
   and the out[] window [fr + 544, fr + 544 + n_b) is addressable by outa_rnb on the kept OUTA.  Push 10's X81640
   comes the same way: the turn-b identity record (38 bytes at fr + 2176) and fragment record (72 bytes at
   fr + 2256; both lengths by R7tail.r7t_RS_len) and out[]'s n_b bytes = rt_F at fr + 544 are frame bytes, and RXS's
   spills (save area) and the fragment record's addressability (frame shadow) are kept.  Push 13B / 14D's PRO (it
   replaces the cut's [A + 168] and our[]'s 6 bytes addressable): its twelve spills are in the save area (SPK), our[]'s
   addressability is frame shadow (ADK), and the input block is a live entry block (PRO's guard holds, 7 <= g_n g),
   whose bytes and shadow bytes are not the allocator's before or after and lie off the malloc window (BLK).
   v1.9.0 (a Theorem Labs lane's generation N.1b, Contract.amalloc_at): the call also asks a per-class bound Bc on the call heap
   g_H g with the request's slot and the room inequality; r7_malloc takes them from ENT's 14th conjunct
   (Tac_cls.sl_malloc_cls, Bc = Bc_of BE). *)
Lemma seg_R7_malloc : forall b, Hat B APIf ra (Inv_A81640_at B APIf ra) b ->
  forall g c, Inv_A815ec_at B APIf ra g b c -> rnb g b <> 0 ->
  SR (ms_segs B) c (Post B APIf ra g).
Proof.
  intros b Hexit g c HInv Hnz.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _ & _ & _ & _ & Hown & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT API) as ALAWS.
  destruct HInv as (regs & mem & md & fr & A & Ec & HFRA & HENT & Hgn & Hb6 & Hnb0 & Hsz & HA & Hr9 & Hr24 & Ha0 &
    Hm64 & H128 & HIDr & HFGr & HRTF & Hr23 & Hour & HOUTA & Hcur & H112 & HPRO & H104 & H96 & H144 & H192 & HIDB &
    HJNK & H280 & H240 & HJY & HSCR & H152 & Hr21 & HA2176 & HRXS).
  subst c.
  pose proof (a_rtn_u (g_in g) (Z.of_nat b) Hnz) as Hu.
  destruct (a_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & Hn124 & HLF).
  change (rt_n (g_in g) (Z.of_nat b)) with (rnb g b) in Hu, Hn124, HLF.
  pose proof (r7_frame_rd g fr [] regs mem md HFRA) as FRD.
  assert (Hapart0 : forall a, fr <= a < fr + FRAME_BYTES -> ~ (AC.aspZ regs - 4096 <= a < AC.aspZ regs))
    by exact (sl_frame_apart_win B APIf ra g fr [] regs mem md HFRA).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (Af & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9f & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAE : APPMEM_END = 0x800000000000) by reflexivity.
  assert (HGT : AC.GT = 0x5fe000) by reflexivity.
  assert (HFS : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  (* errno and the OOM flag, computed from Contract.v by name (no address is written here) *)
  assert (Eerr : AC.a_errno AC.ASYMS = ltac:(let v := eval vm_compute in (AC.a_errno AC.ASYMS) in exact v))
    by reflexivity.
  assert (Eoom : AC.as_oom AC.ASYMS = ltac:(let v := eval vm_compute in (AC.as_oom AC.ASYMS) in exact v))
    by reflexivity.
  assert (HK : ASAN_K = 0x7fff8000) by reflexivity.
  assert (Hsp0 : 0 <= sp < 2 ^ 64) by (rewrite <- Haspz; apply u64_range).
  assert (Hstkhi : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ ALAWS _ mem md HAH).
  assert (Hfrb : 0 <= fr /\ fr + 8 <= 2 ^ 64).
  { pose proof Hhdr1 as Hx. unfold q64 in Hx. apply bytes_at_bound in Hx. rewrite length_le8 in Hx. lia. }
  assert (EA : Af = A).
  { unfold rg in Hr9, Hr9f. rewrite Hr9f in Hr9.
    apply (f_equal (@bv_unsigned 64)) in Hr9. rewrite !MState.unsigned_lit in Hr9 by lia. exact Hr9. }
  subst Af.
  assert (HA72 : A + 72 <= 2 ^ 64) by lia.
  assert (Hapart : forall a, fr <= a < fr + FRAME_BYTES -> ~ (sp - 4096 <= a < sp))
    by (intros a Ha; rewrite <- Haspz; exact (Hapart0 a Ha)).
  assert (S64 : spill regs mem 64 0xe38f0000) by (exists A; split; [exact Hr9 | exact Hm64]).
  (* a side-stack byte lies above the image and below stklo *)
  assert (FSC : forall a, AC.a_in_fs AC.ASYMS mem a ->
             AC.GT <= a < AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md /\ app_mem a).
  { intros a (bb & Hbr & Hwm & Hb1 & Hb2).
    destruct (r7_fs_place _ mem md bb HAH Hwm Hbr) as (Hg & Hfsk & Hfa').
    split; [lia|]. apply Hfa'. lia. }
  (* every frame byte is located and application memory *)
  assert (FRAME : forall a, fr <= a < fr + FRAME_BYTES -> r7_loc mem md a /\ app_mem a).
  { intros a Ha. destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
    - pose proof (Hreal a Ha) as Hr. split; [left; exact Hr|]. unfold app_mem. right. lia.
    - destruct (FSC a (Hfs a Ha)) as (Ha1 & Ha2).
      split; [right; split; [exact (Hfs a Ha) | exact Ha1] | exact Ha2]. }
  rewrite SEGS.
  apply (sl_run_lib regs (Z_to_bv 64 0x815ec) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x5337c /\ mem' = mem /\ getr R 1 = Z_to_bv 64 0x81640 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 21 = getr regs 21 /\
       getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\ getr R 25 = getr regs 25 /\
       getr R 26 = getr regs 26 /\ getr R 10 = Z_to_bv 64 (rnb g b) /\ getr R 18 = Z_to_bv 64 (rnb g b))
    (Post B APIf ra g)).
  { exact Hhalt. }
  { unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    eapply evt_mono.
    - apply r7_evt with (A := A) (n := rnb g b); first [assumption | exact (r7_q64_ro _ _ _ Hm64) | lia].
    - intros ms' (a1' & a2' & ->). do 3 eexists. split; [reflexivity|].
      repeat (split; [first [reflexivity | symmetry; exact Hr9]|]). reflexivity. }
  intros R pc' mem' regs'' md'
    (Hpc & Hmem & K1 & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K23 & K25 & K26 & K10 & K18)
    Hreg Hmat.
  subst pc' mem'.
  assert (E1 : getr regs'' 1 = Z_to_bv 64 0x81640) by (rewrite Hreg; exact K1).
  assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
  assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
  assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
  assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
  assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
  assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
  assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
  assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
  assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
  assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
  assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
  assert (E10 : getr regs'' 10 = Z_to_bv 64 (rnb g b)) by (rewrite Hreg; exact K10).
  assert (E18 : getr regs'' 18 = Z_to_bv 64 (rnb g b)) by (rewrite Hreg; exact K18).
  assert (Hasp'' : AC.aspZ regs'' = sp) by (unfold AC.aspZ; rewrite E2; exact Haspz).
  assert (HFRA1 : FRA B APIf ra g fr [] regs'' mem md')
    by exact (sl_fra_move B APIf ra g fr [] regs regs'' mem md md' HFRA E2 E3 E4 E8 E9 E19 E26 Hmat).
  assert (HENT1 : ENT APIf g [] mem md') by (eapply ent_mat; [exact HENT | exact Hmat]).
  assert (HKm : 0 <= AC.AK_MALLOC <= FN_STACK) by (unfold AC.AK_MALLOC; lia).
  assert (Hpre1 : AC.a_call_pre AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT API)
      (AC.aa_stklo AC.ASYMS AsanRTInv.RT API) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT API) AC.AK_MALLOC (g_H g)
      regs'' mem md').
  { apply (fra_call_pre B APIf ra g fr [] regs'' mem md' AC.AK_MALLOC HFRA1 HENT1); [|exact HKm].
    rewrite E1. apply YK0s.ret_ok_even. rewrite MState.unsigned_lit by lia. reflexivity. }
  destruct (r7_mat ([] ++ g_H g) mem md md' Hmat) as (HAHm & Hstkeq).
  pose proof (HAHm HAH) as HAH1.
  eapply SR_bind.
  { apply (r7_malloc g [] mem md' regs'' mem md' (rnb g b) HENT1 Hpre1 E10).
    - unfold AC.ANMAX. lia.
    - unfold AC.ALIVE_MAX, AC.a_size. lia.
    - left. unfold AC.A_PRIMARY_MAX, AC.a_size. lia. }
  intros c' (regs' & mem' & md'' & q & Ec' & Hq & Hnb & Hcp & Herrk & Hownq).
  subst c'. rewrite E1.
  pose proof Hcp as HAH'; apply AC.a_call_post_ah in HAH'.
  pose proof Hcp as Hkept; apply AC.a_call_post_regs in Hkept.
  pose proof Hcp as Hsk'; apply AC.a_call_post_stklo in Hsk'.
  pose proof (AC.a_call_post_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcp) as Hfk.
  pose proof (AC.a_call_post_win_writable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcp) as Hwinw.
  pose proof (AC.a_call_post_win_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcp) as Hwinp.
  pose proof Hcp as Hmod; apply AC.a_call_post_model in Hmod.
  assert (Htp16 : forall i, 0 <= i < 16 ->
            mbyte rsegs mem' (AC.as_tp AC.ASYMS + i) = mbyte rsegs mem (AC.as_tp AC.ASYMS + i))
    by (eapply AC.a_call_post_tp; exact Hcp).
  assert (F2 : getr regs' 2 = getr regs'' 2) by exact (Hkept 2 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F3 : getr regs' 3 = getr regs'' 3) by exact (Hkept 3 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F4 : getr regs' 4 = getr regs'' 4) by exact (Hkept 4 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F8 : getr regs' 8 = getr regs'' 8) by exact (Hkept 8 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F9 : getr regs' 9 = getr regs'' 9) by exact (Hkept 9 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F18 : getr regs' 18 = getr regs'' 18) by exact (Hkept 18 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F19 : getr regs' 19 = getr regs'' 19) by exact (Hkept 19 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F21 : getr regs' 21 = getr regs'' 21) by exact (Hkept 21 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F22 : getr regs' 22 = getr regs'' 22) by exact (Hkept 22 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F23 : getr regs' 23 = getr regs'' 23) by exact (Hkept 23 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F25 : getr regs' 25 = getr regs'' 25) by exact (Hkept 25 ltac:(unfold AC.a_callee_saved; lia)).
  assert (F26 : getr regs' 26 = getr regs'' 26) by exact (Hkept 26 ltac:(unfold AC.a_callee_saved; lia)).
  (* the new block: a_size n_b = n_b, and the post heap is the cut's prepend list up to order *)
  assert (Esz : AC.a_size (rnb g b) = rnb g b) by (unfold AC.a_size; lia).
  assert (HPERM : Permutation (hb1 q (rnb g b) ++ g_H g) (g_H g ++ [(q, AC.a_size (rnb g b))])).
  { rewrite Esz. exact (Permutation_cons_append (g_H g) (q, rnb g b)). }
  (* the block's bytes are app memory below stklo (so below S), off the image and off every entry block *)
  assert (HTOUCH : forall a, q <= a < q + AC.a_size (rnb g b) ->
            app_mem a /\ a < g_S g /\ ~ AC.a_in_img a /\ ~ AC.in_blocks (g_H g) a).
  { intros a Ha.
    assert (Hinq : In (q, AC.a_size (rnb g b)) (g_H g ++ [(q, AC.a_size (rnb g b))]))
      by (apply in_or_app; right; left; reflexivity).
    destruct (r7_blocks _ mem' md'' q (AC.a_size (rnb g b)) HAH' Hinq) as (_ & Hend & Hall).
    destruct (Hall a Ha) as (Happ & Hnimg & _).
    pose proof (proj1 (proj2 (r7_new_block _ _ _ _ _ _ _ _ Hnb)) a Ha) as Hnib.
    split; [exact Happ|]. split; [lia|]. split; [exact Hnimg | exact Hnib]. }
  (* a byte that is not the allocator's before and after, off the malloc window, errno and the flag, is kept;
     not the allocator's before means not in the new block (whose bytes were) *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g) mem md' a ->
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g ++ [(q, AC.a_size (rnb g b))]) mem' md'' a ->
      ~ (sp - 4096 <= a < sp) -> ~ (AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4) ->
      a <> AC.as_oom AC.ASYMS ->
      mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a)).
  { intros a Ha Ho1 Ho2 Hw He Hoo. apply (Hfk a Ha Ho1 Ho2); [| exact He | exact Hoo |].
    - unfold AC.a_window, AC.AK_MALLOC. rewrite Hasp''. exact Hw.
    - cbv beta. intros Ht. apply Ho1. apply Hownq. left. exists q, (AC.a_size (rnb g b)).
      split; [left; reflexivity | exact Ht]. }
  assert (FSPOST : forall a, AC.a_in_fs AC.ASYMS mem a -> AC.a_in_fs AC.ASYMS mem' a).
  { intros a (bb & Hbr & Hwm & Hb). exists bb. split; [exact Hbr|]. split; [|exact Hb].
    intros k Hk. rewrite (Htp16 (Z.of_nat k) ltac:(lia)). exact (Hwm k Hk). }
  (* a located byte and its shadow are not the allocator's, before or after *)
  assert (LOC : forall a, r7_loc mem md a ->
      0 <= a < 2 ^ 64 /\ AC.GT <= a /\
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g) mem md' a /\
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g) mem md' (shadow_addr a) /\
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g ++ [(q, AC.a_size (rnb g b))]) mem' md'' a /\
      ~ AC.aa_owned AC.ASYMS AsanRTInv.RT API (g_H g ++ [(q, AC.a_size (rnb g b))]) mem' md'' (shadow_addr a)).
  { intros a Hl.
    assert (Hpl : AC.in_blocks ([] ++ g_H g) a \/ AC.in_slack ([] ++ g_H g) a \/ AC.a_in_fs AC.ASYMS mem a \/
                  AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md' <= a < APPMEM_END).
    { rewrite Hstkeq. destruct Hl as [Hs|[Hfs _]]; [right; right; right; exact Hs | right; right; left; exact Hfs]. }
    assert (Hql : AC.in_blocks (g_H g ++ [(q, AC.a_size (rnb g b))]) a \/
                  AC.in_slack (g_H g ++ [(q, AC.a_size (rnb g b))]) a \/ AC.a_in_fs AC.ASYMS mem' a \/
                  AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem' md'' <= a < APPMEM_END).
    { rewrite Hsk', Hstkeq. destruct Hl as [Hs|[Hfs _]];
        [right; right; right; exact Hs | right; right; left; exact (FSPOST a Hfs)]. }
    destruct (r7_not_owned _ mem md' a HAH1 Hpl) as (N1 & N2).
    destruct (r7_not_owned _ mem' md'' a HAH' Hql) as (N3 & N4).
    split; [destruct Hl as [Hs|[_ Hs]]; lia|].
    split; [destruct Hl as [Hs|[_ Hs]]; lia|].
    split; [exact N1|]. split; [exact N2|]. split; [exact N3 | exact N4]. }
  assert (KLOC : forall a, r7_loc mem md a -> ~ (sp - 4096 <= a < sp) ->
      mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a)).
  { intros a Hl Hw. destruct (LOC a Hl) as (Hr & Hg & N1 & _ & N3 & _).
    apply KEEP; [exact Hr | exact N1 | exact N3 | exact Hw | lia | lia]. }
  assert (KST : forall a, AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md <= a < APPMEM_END -> ~ (sp - 4096 <= a < sp) ->
      mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a)).
  { intros a Hs Hw. apply KLOC; [left; exact Hs | exact Hw]. }
  assert (KSH : forall a, r7_loc mem md a -> app_mem a ->
      mbyte rsegs mem' (shadow_addr a) = mbyte rsegs mem (shadow_addr a)).
  { intros a Hl Hap. destruct (LOC a Hl) as (_ & _ & _ & N2 & _ & N4).
    pose proof (shadow_of_app a Hap) as Hsh1. pose proof (in_shadow_range _ Hsh1) as Hsr.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in Hsh1.
    refine (proj1 (KEEP _ _ N2 N4 _ _ _)); lia. }
  assert (KFR : forall a, fr <= a < fr + FRAME_BYTES -> mbyte rsegs mem' a = mbyte rsegs mem a).
  { intros a Ha. destruct (FRAME a Ha) as (Hl & _). exact (proj1 (KLOC a Hl (Hapart a Ha))). }
  (* a side-stack byte is below stklo, so below the malloc window *)
  assert (KFS : forall a, AC.a_in_fs AC.ASYMS mem a -> mbyte rsegs mem' a = mbyte rsegs mem a).
  { intros a Hfs. destruct (FSC a Hfs) as (Hgt & _).
    assert (Hl : r7_loc mem md a) by (unfold r7_loc; right; split; [exact Hfs | exact Hgt]).
    exact (proj1 (KLOC a Hl ltac:(lia))). }
  assert (KCL : forall a, AC.a_errno AC.ASYMS + 4 <= a < 0x5fe000 -> AC.in_blocks AC.a_client a ->
      mbyte rsegs mem' a = mbyte rsegs mem a).
  { intros a Ha Hcl. refine (proj1 (KEEP a _ _ _ _ _ _)); [lia | | | lia | lia | lia].
    - exact (proj1 (r7_client _ mem md' a HAH1) Hcl).
    - exact (proj1 (r7_client _ mem' md'' a HAH') Hcl). }
  (* the Shadow byte of a registered global (an image byte) is not the allocator's, before or after *)
  assert (KAG : forall a, in_globals AF.frame_AG a ->
      mbyte rsegs mem' (shadow_addr a) = mbyte rsegs mem (shadow_addr a)).
  { intros a Hin. pose proof (r7_ag_img a Hin) as Himg. pose proof (r7_ag_range a Hin) as Hr.
    assert (ELO : r7_AG_LO / 8 = ltac:(let v := eval vm_compute in (r7_AG_LO / 8) in exact v)) by reflexivity.
    assert (EHI : AC.RELRO_HI / 8 = ltac:(let v := eval vm_compute in (AC.RELRO_HI / 8) in exact v)) by reflexivity.
    assert (Hsa : ASAN_K + r7_AG_LO / 8 <= shadow_addr a <= ASAN_K + AC.RELRO_HI / 8).
    { unfold shadow_addr.
      pose proof (Z.div_le_mono r7_AG_LO a 8 ltac:(lia) ltac:(lia)) as D1.
      pose proof (Z.div_le_mono a AC.RELRO_HI 8 ltac:(lia) ltac:(lia)) as D2. lia. }
    rewrite ELO, EHI, HK in Hsa.
    refine (proj1 (KEEP _ _ _ _ _ _ _)); [lia | | | lia | lia | lia].
    - exact (proj2 (r7_client _ mem md' a HAH1) Himg).
    - exact (proj2 (r7_client _ mem' md'' a HAH') Himg). }
  (* the side-arm FakeStack record: the tp word, the class-6 flag byte and the slot's last word are kept *)
  assert (HREC : FSREC fr mem -> FSREC fr mem').
  { intros (FS & j & Htpw & HFSr & Hj & Hfrj & Hflag & Htail).
    assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
    assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
    assert (Hfl : SMC.fs_flag FS 6 j = FS + 36352 + j) by (unfold SMC.fs_flag; cbn; lia).
    assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfrj; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
    rewrite HM6 in Hj.
    assert (KFS1 : forall x, FS <= x < FS + AC.FS_SIZE -> mbyte rsegs mem' x = mbyte rsegs mem x).
    { intros x Hx. apply KFS. exists FS. split; [exact HFSr|]. split; [exact Htpw | exact Hx]. }
    exists FS, j.
    split; [intros k Hk; rewrite (Htp16 (Z.of_nat k) ltac:(lia)); exact (Htpw k Hk)|].
    split; [exact HFSr|].
    split; [rewrite HM6; exact Hj|].
    split; [exact Hfrj|].
    split.
    - apply (r7_bkeep mem mem'); [|exact Hflag]. cbn [length]. intros x Hx. apply KFS1. lia.
    - apply (r7_bkeep mem mem'); [|exact Htail]. rewrite length_le8. intros x Hx. apply KFS1. lia. }
  (* a loop-body spill (in the save area [A, A + 416), above sp), a frame range's addressability (its shadow
     bytes) and a readable and writable frame range (push 7's records at fr + 2688 / fr + 2768, push 9's cells at
     fr + 3040 / fr + 3056) are kept; OUTA by outa_call *)
  assert (SPK : forall off v, 0 <= off <= 408 -> spill regs mem off v -> spill regs' mem' off v).
  { intros off v Hoff Hs. pose proof (r7_spill_at regs mem A off v Hr9 ltac:(lia) ltac:(lia) Hs) as Q.
    exists A. split; [unfold rg; rewrite F9, E9; exact Hr9|].
    unfold q64 in *. apply (r7_bkeep mem mem'); [|exact Q].
    rewrite length_le8. intros x Hx. exact (proj1 (KST x ltac:(lia) ltac:(lia))). }
  assert (ADK : forall a n, fr <= a /\ a + n <= fr + FRAME_BYTES -> addressable mem a n -> addressable mem' a n).
  { intros a n Han Ha. apply (addr_keep mem mem' a n Ha). intros i Hi.
    destruct (FRAME (a + i) ltac:(lia)) as (Hl & Hap). exact (KSH _ Hl Hap). }
  assert (RWK : forall X cs, fr <= X -> X + Z.of_nat (cells_size cs) <= fr + FRAME_BYTES ->
            rw_cells rsegs mem X cs -> rw_cells rsegs mem' X cs).
  { intros X cs H0 H1 ((Hwf & Hb) & (Hw0 & Hw1 & Hw)).
    split; [split; [exact Hwf|]|].
    - apply (r7_bkeep mem mem'); [|exact Hb]. rewrite (cells_bytes_length cs Hwf).
      intros x Hx. apply KFR. lia.
    - split; [lia|]. split; [lia|]. intros i Hi.
      destruct (FRAME (X + i) ltac:(lia)) as (Hl & _).
      exact (proj1 (proj2 (KLOC (X + i) Hl (Hapart (X + i) ltac:(lia)))) (Hw i Hi)). }
  assert (HOUTA' : OUTA fr mem')
    by exact (outa_call B APIf ra g fr [] (g_H g ++ [(q, AC.a_size (rnb g b))]) regs'' mem md' regs' mem' md''
                (fun a => q <= a < q + AC.a_size (rnb g b)) AC.AK_MALLOC HFRA1 Hcp HKm HTOUCH HOUTA).
  (* push 13B: PRO's input block (a live entry block, 7 <= g_n g) and its shadow are kept: its bytes lie below stklo,
     so below the malloc window, off the image (so off errno and the OOM flag), and are not the allocator's before
     or after (a_laws_not_owned on a block byte of either list); its shadow bytes likewise *)
  assert (BLK : forall x, In (g_p g, g_n g) (g_H g) -> g_p g <= x < g_p g + g_n g ->
            mbyte rsegs mem' x = mbyte rsegs mem x /\
            mbyte rsegs mem' (shadow_addr x) = mbyte rsegs mem (shadow_addr x)).
  { intros x Hin Hx.
    destruct (R7tail.r7t_blk_not_fr B APIf ra g fr [] regs mem md (g_p g) (g_n g) x HFRA Hin Hx)
      as (Hxa & Hnimg & Hxlo & _).
    assert (Hb1 : AC.in_blocks ([] ++ g_H g) x) by (exists (g_p g), (g_n g); split; [exact Hin | lia]).
    assert (Hb2 : AC.in_blocks (g_H g ++ [(q, AC.a_size (rnb g b))]) x)
      by (exists (g_p g), (g_n g); split; [apply in_or_app; left; exact Hin | lia]).
    destruct (r7_not_owned _ mem md' x HAH1 (or_introl Hb1)) as (N1 & N2).
    destruct (r7_not_owned _ mem' md'' x HAH' (or_introl Hb2)) as (N3 & N4).
    assert (Hx64 : 0 <= x < 2 ^ 64) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hxa; lia).
    split.
    - refine (proj1 (KEEP x Hx64 N1 N3 _ _ _)).
      + lia.
      + intro He. apply Hnimg. apply errno_in_img. rewrite Eerr. lia.
      + intro He. apply Hnimg. rewrite He. exact oom_in_img.
    - pose proof (shadow_of_app x Hxa) as Hsh1. pose proof (in_shadow_range _ Hsh1) as Hsr.
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in Hsh1.
      refine (proj1 (KEEP _ _ N2 N4 _ _ _)); lia. }
  rewrite <- SEGS. apply Hexit.
  exists q, regs', mem', md'', fr.
  split; [reflexivity|].
  split.
  { apply (sl_mid_perm B APIf ra g fr [] (hb1 q (rnb g b)) (g_H g ++ [(q, AC.a_size (rnb g b))]) regs'' mem md'
      regs' mem' md'' (fun a => q <= a < q + AC.a_size (rnb g b)) AC.AK_MALLOC HFRA1 Hcp HPERM).
    - cbn. lia.
    - destruct Hsn as ((Hthm & Hlkm) & Hhdm & Hfd).
      split; [split|split].
      + eapply YI14.val_mem_frame; [|exact Hthm]. intros x Hx. rewrite Hthr in Hx. cbn in Hx. rewrite SEGS.
        apply KCL; [lia|]. red. R7tail.r7t_blk AC.a_client.
      + eapply YI14.val_mem_frame; [|exact Hlkm]. intros x Hx. rewrite Hlock in Hx. cbn in Hx. rewrite SEGS.
        apply KCL; [lia|]. red. R7tail.r7t_blk AC.a_client.
      + intros k Hk. rewrite <- (Hhdm k Hk). rewrite SEGS, Hhead.
        apply KCL; [lia|]. red. R7tail.r7t_blk AC.a_client.
      + destruct Hmod as (lz & mt & vm' & Emd). rewrite Emd.
        change (m_fds (with_vm_backing lz mt (with_vmmaps vm' md'))) with (m_fds md').
        rewrite (sl_mat_fds md md' Hmat). exact Hfd.
    - intros a Hin. pose proof (Hgimg a Hin) as E. rewrite SEGS in E |- *. rewrite <- E.
      (* the RELRO blocks lie in Contract's page-rounded RELRO range *)
      assert (Har : AC.RELRO_LO <= a < AC.RELRO_HI).
      { destruct Hin as (lo & len & Hil & Hr). pose proof (r7_relro_range lo len Hil). lia. }
      assert (ERL : AC.RELRO_LO = ltac:(let v := eval vm_compute in AC.RELRO_LO in exact v)) by reflexivity.
      assert (ERH : AC.RELRO_HI = ltac:(let v := eval vm_compute in AC.RELRO_HI in exact v)) by reflexivity.
      rewrite ERL, ERH in Har.
      refine (proj1 (KEEP a _ _ _ _ _ _)); [lia | | | lia | lia | lia].
      + intros Ho. exact (proj2 (Hown rc _ _ _ _ Ho) Hin).
      + intros Ho. exact (proj2 (Hown rc _ _ _ _ Ho) Hin).
    - unfold q64 in *. apply (r7_bkeep mem mem'); [|exact Hhdr1].
      rewrite length_le8. intros x Hx. apply KFR. lia.
    - unfold q64 in *. apply (r7_bkeep mem mem'); [|exact Hhdr2].
      rewrite length_le8. intros x Hx. apply KFR. lia.
    - intros A0 HA0 HA0r.
      assert (EA0 : A0 = A).
      { rewrite E9 in HA0. unfold rg in Hr9. rewrite Hr9 in HA0.
        apply (f_equal (@bv_unsigned 64)) in HA0. rewrite !MState.unsigned_lit in HA0 by lia. lia. }
      subst A0. unfold q64 in *. apply (r7_bkeep mem mem'); [|exact Hspill].
      rewrite length_le8. intros x Hx. exact (proj1 (KST x ltac:(lia) ltac:(lia))).
    - intros A0 HA0 HA0r v Hv.
      assert (EA0 : A0 = A).
      { rewrite E9 in HA0. unfold rg in Hr9. rewrite Hr9 in HA0.
        apply (f_equal (@bv_unsigned 64)) in HA0. rewrite !MState.unsigned_lit in HA0 by lia. lia. }
      subst A0. unfold q64 in *. apply (r7_bkeep mem mem'); [|exact Hv].
      rewrite length_le8. intros x Hx. exact (proj1 (KST x ltac:(lia) ltac:(lia))).
    - intros A0 HA0 HA0r.
      assert (EA0 : A0 = A).
      { rewrite E9 in HA0. unfold rg in Hr9. rewrite Hr9 in HA0.
        apply (f_equal (@bv_unsigned 64)) in HA0. rewrite !MState.unsigned_lit in HA0 by lia. lia. }
      subst A0. unfold q64 in *. apply (r7_bkeep mem mem'); [|exact Hfr24].
      rewrite length_le8. intros x Hx. exact (proj1 (KST x ltac:(lia) ltac:(lia))).
    - destruct Hsh as (sh & Hshb & Hshl). exists sh. split; [|exact Hshl].
      apply (r7_bkeep mem mem'); [|exact Hshb]. rewrite Hshl. intros x Hx.
      assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
      { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
      assert (Ex : x = shadow_addr (fr + 8 * (x - Sfr fr))).
      { unfold shadow_addr at 1. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
      assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
      destruct (FRAME _ Hin) as (Hl & Hap).
      rewrite Ex. exact (KSH _ Hl Hap).
    - apply (r7_bkeep mem mem'); [|exact Hsaved]. intros x Hx.
      unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx.
      exact (proj1 (KST x ltac:(lia) ltac:(lia))).
    - unfold stk in Hwin |- *. destruct Hwin as (Hw0 & Hw1 & Hw).
      split; [exact Hw0|]. split; [exact Hw1|]. intros a Ha.
      destruct (Hw a Ha) as (Hwv & bb & Hbb).
      destruct (Z_lt_ge_dec a (sp - 4096)) as [Hlt|Hge]; [|destruct (Z_lt_ge_dec a sp) as [Hlt2|Hge2]].
      + destruct (KST a ltac:(lia) ltac:(lia)) as (Em & Ew).
        split; [exact (proj1 Ew Hwv)|]. exists bb. change (mbyte rsegs mem' a = Some bb). rewrite Em. exact Hbb.
      + assert (Hwa : AC.a_window AC.AK_MALLOC regs'' a) by (unfold AC.a_window, AC.AK_MALLOC; rewrite Hasp''; lia).
        split; [exact (Hwinw a Hwa)|]. exact (Hwinp a Hwa).
      + destruct (KST a ltac:(lia) ltac:(lia)) as (Em & Ew).
        split; [exact (proj1 Ew Hwv)|]. exists bb. change (mbyte rsegs mem' a = Some bb). rewrite Em. exact Hbb.
    - intros a Hin. destruct (HAG a Hin) as (Ha0' & Hn0 & Hend & Hb).
      split; [exact Ha0'|]. split; [exact Hn0|]. split; [exact Hend|].
      intros i Hi. destruct (Hb i Hi) as (Hap & bb & Hrd & Hok). split; [exact Hap|].
      exists bb. split; [|exact Hok].
      assert (Hin' : in_globals AF.frame_AG (a + i)) by (replace (a + i) with a by lia; exact Hin).
      change (mbyte rsegs mem' (shadow_addr (a + i)) = Some bb). rewrite (KAG _ Hin'). exact Hrd.
    - intros a Ha Hnf. apply (addr_keep mem mem' a 1 (HWA a Ha Hnf)). intros i Hi.
      assert (Hl : r7_loc mem md (a + i)) by (unfold r7_loc; left; lia).
      assert (Hap : app_mem (a + i)) by (unfold app_mem; right; lia).
      exact (KSH _ Hl Hap).
    - exact HREC.
    - exact F2.
    - exact F3.
    - exact F4.
    - exact F8.
    - exact F9.
    - exact F19.
    - exact F26. }
  split.
  { exact (ent_call_perm g fr [] (hb1 q (rnb g b)) (g_H g ++ [(q, AC.a_size (rnb g b))]) regs'' mem md'
             regs' mem' md'' (fun a => q <= a < q + AC.a_size (rnb g b)) AC.AK_MALLOC HENT1 HFRA1 Hcp HPERM
             HKm HTOUCH Herrk). }
  split.
  { split; [exact Hgn|].
  split; [exact Hb6|].
  split; [exact Hnz|].
  split; [exact Hq|].
  split.
  { destruct (r7_new_block _ _ _ _ _ _ _ _ Hnb) as (Hq0 & _ & Haddr). split; [exact Hq0 | exact Haddr]. }
  split; [unfold rg; rewrite F18, E18; reflexivity|].
  split; [exact (SPK 128 _ ltac:(lia) H128)|].
  split; [exact (outa_rnb g b fr mem' HOUTA' Hnz)|].
  split.
  { assert (Hrd : forall x, fr + 544 <= x < fr + 544 + Z.of_nat (Z.to_nat (rnb g b)) ->
              exists bb, mbyte rsegs mem' x = Some bb).
    { intros x Hx. rewrite Z2Nat.id in Hx by lia. rewrite (KFR x ltac:(lia)). exact (FRD x ltac:(lia)). }
    destruct (r7_bytes_ex mem' (Z.to_nat (rnb g b)) (fr + 544) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) Hrd)
      as (src & Hsrc & Hl).
    exists src. split; [exact Hsrc|]. rewrite Hl. apply Z2Nat.id. lia. }
  split; [unfold rg in *; rewrite F23, E23; exact Hr23|].
  split.
  { unfold OURb in *. apply (r7_bkeep mem mem'); [|exact Hour]. rewrite OUR_length. intros x Hx. apply KFR. lia. }
  split; [exact HOUTA'|].
  split.
  { destruct Hcur as (Hc0 & Hc22 & Hc25). unfold CUR, rg in *.
    split; [exact Hc0|]. split; [rewrite F22, E22; exact Hc22 | rewrite F25, E25; exact Hc25]. }
  split; [exact (SPK 112 _ ltac:(lia) H112)|].
  split.
  { (* push 13B: PRO - the spills by SPK, our[]'s addressability by ADK, the input block by BLK *)
    pose proof Hcur as (Hc7 & _ & _).
    pose proof HPRO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPI & _).
    destruct (HPI ltac:(lia)) as (Hin & _).
    apply (R7tail.r7t_pro_mk g fr regs mem regs' mem'); [exact SPK | | | | exact HPRO].
    - exact (ADK (fr + 2624) 6 ltac:(lia)).
    - intros HB. apply (r7_bkeep mem mem'); [|exact HB]. intros x Hx. rewrite <- g_n_len in Hx.
      exact (proj1 (BLK x Hin Hx)).
    - intros Hin' Had. apply (addr_keep mem mem' _ _ Had). intros i Hi.
      exact (proj2 (BLK (g_p g + i) Hin' ltac:(lia))). }
  split; [exact (SPK 104 _ ltac:(lia) H104)|].
  split; [exact (SPK 96 _ ltac:(lia) H96)|].
  split; [exact (SPK 64 _ ltac:(lia) S64)|].
  split; [exact (SPK 144 _ ltac:(lia) H144)|].
  split; [exact (SPK 192 _ ltac:(lia) H192)|].
  split; [destruct HIDB as (idb & Hidb); exists idb;
          exact (RWK (fr + 2688) [CB 38 idb] ltac:(lia) ltac:(cbn [cells_size csize]; lia) Hidb)|].
  split; [destruct HJNK as (junk & Hjk); exists junk;
          exact (RWK (fr + 2768) [CB 72 junk] ltac:(lia) ltac:(cbn [cells_size csize]; lia) Hjk)|].
  split; [exact (SPK 280 _ ltac:(lia) H280)|].
  split; [exact (SPK 240 _ ltac:(lia) H240)|].
  split; [destruct HJY as (jy & Hjy); exists jy;
          exact (RWK (fr + 3040) [CB 1 jy] ltac:(lia) ltac:(cbn [cells_size csize]; lia) Hjy)|].
  split; [destruct HSCR as (junk & Hsc); exists junk;
          exact (RWK (fr + 3056) [CB 32 junk] ltac:(lia) ltac:(cbn [cells_size csize]; lia) Hsc)|].
  split; [exact (SPK 152 _ ltac:(lia) H152)|].
  split; [unfold rg; rewrite F21, E21; exact Hr21|].
  exact (ADK (fr + 2176) 38 ltac:(lia) HA2176). }
  (* X81640: the turn-b records and out[]'s n_b bytes are frame bytes off the malloc window, RXS's spills are in
     the save area and its fragment-record addressability is frame shadow *)
  destruct (R7tail.r7t_RS_len (g_in g) b) as (LID & LFG).
  unfold X81640. unfold IDBr, FGBr in HIDr, HFGr |- *.
  split.
  { apply (r7_bkeep mem mem'); [|exact HIDr]. rewrite LID. intros x Hx. apply KFR. lia. }
  split.
  { apply (r7_bkeep mem mem'); [|exact HFGr]. rewrite LFG. intros x Hx. apply KFR. lia. }
  split.
  { (* out[] = rt_F: the cut's conjunct, unguarded (push 10) or behind `rnb g b <> 0 ->` (push 11) *)
    assert (HRTF' : bytes_at rsegs mem (fr + 544) (rt_F (g_in g) (Z.of_nat b)))
      by first [exact HRTF | exact (HRTF Hnz)].
    apply (r7_bkeep mem mem'); [|exact HRTF']. rewrite HLF, Z2Nat.id by lia. intros x Hx. apply KFR. lia. }
  destruct HRXS as (R48 & R56 & R88 & R80 & R72 & R8 & R0 & R200 & R216 & RA).
  unfold RXS.
  split; [exact (SPK 48 _ ltac:(lia) R48)|].
  split; [exact (SPK 56 _ ltac:(lia) R56)|].
  split; [exact (SPK 88 _ ltac:(lia) R88)|].
  split; [exact (SPK 80 _ ltac:(lia) R80)|].
  split; [exact (SPK 72 _ ltac:(lia) R72)|].
  split; [exact (SPK 8 _ ltac:(lia) R8)|].
  split; [exact (SPK 0 _ ltac:(lia) R0)|].
  split; [exact (SPK 200 _ ltac:(lia) R200)|].
  split; [exact (SPK 216 _ ltac:(lia) R216)|].
  exact (ADK (fr + 2256) 72 ltac:(lia) RA).
Qed.

(* n_b = 0 with b <= 5: the latch runs to the cut 0x815cc of the next turn.  Every fact of Inv_A815cc_at is the
   entry cut's (the run only loads): the turn state does not move (r7_rid_skip), so the cut's turn-b records are
   those of turn S b, the loop-body spills (push 10's RXS among them) are read off register 9, which the run keeps,
   as is s5, a0 is the out[] pointer the run loads from [A + 128], the memory (so OUTA, the addressability facts,
   push 7's two frame records and push 9's two frame cells) is unchanged, FRA moves by sl_fra_move and ENT by
   ent_mat. Push 13B's PRO is the entry cut's: its spills are read off register 9, its other parts are memory. *)
Lemma seg_R7_latch : forall b, (b <= 5)%nat -> Hat B APIf ra (Inv_A815cc_at B APIf ra) (S b) ->
  forall g c, Inv_A815ec_at B APIf ra g b c -> rnb g b = 0 -> SR (ms_segs B) c (Post B APIf ra g).
Proof.
  intros b Hb5 Hnext g c HInv Hz.
  pose proof FF as (SEGS & _).
  destruct HInv as (regs & mem & md & fr & A & Ec & HFRA & HENT & Hgn & Hb6 & Hnb0 & Hsz & HA & Hr9 & Hr24 & Ha0 &
    Hm64 & H128 & HID & HFG & _ & Hr23 & Hour & HOUTA & Hcur & H112 & HPRO & H104 & H96 & H144 & H192 & HIDB &
    HJNK & H280 & H240 & HJY & HSCR & H152 & Hr21 & HA2176 & HRXS).
  subst c.
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (Af & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9f & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HAE : APPMEM_END = 2 ^ 47) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (Hsp0 : 0 <= sp < 2 ^ 64) by (rewrite <- Haspz; apply u64_range).
  assert (HSb : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (unfold stk in Hwin; split; [apply (proj1 Hwin) | apply (proj1 (proj2 Hwin))]).
  assert (HAfb : 0 <= Af < 2 ^ 64) by lia.
  assert (EA : Af = A).
  { unfold rg in Hr9, Hr9f. rewrite Hr9f in Hr9.
    apply (f_equal (@bv_unsigned 64)) in Hr9. rewrite !MState.unsigned_lit in Hr9 by lia. exact Hr9. }
  subst Af.
  assert (HA47 : A + 416 <= 2 ^ 47) by lia.
  assert (Ha00 : getr regs 10 = Z_to_bv 64 0) by (unfold a0v, rg in Ha0; rewrite Hz in Ha0; exact Ha0).
  pose proof (r7_spill_at regs mem A 128 (fr + 544) Hr9 ltac:(lia) ltac:(lia) H128) as Q128.
  rewrite SEGS.
  apply (sl_run_lib regs (Z_to_bv 64 0x815ec) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x815cc /\ mem' = mem /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\ getr R 25 = getr regs 25 /\
       getr R 26 = getr regs 26 /\ getr R 10 = Z_to_bv 64 (fr + 544) /\ getr R 24 = getr regs 24 /\
       getr R 23 = Z_to_bv 64 (Z.of_nat b + 1))
    (Post B APIf ra g)).
  { exact Hhalt. }
  { unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    eapply evt_mono.
    - apply (r7_latch_evt (Z.of_nat b) ltac:(lia)) with (A := A) (V := fr + 544);
        first [exact Hr9 | exact Ha00 | exact Hr23 | exact (r7_q64_ro _ _ _ Q128) | lia].
    - intros ms' (a1' & a2' & ->). do 3 eexists. split; [reflexivity|].
      repeat (split; [first [reflexivity | symmetry; exact Hr9]|]). reflexivity. }
  intros R pc' mem' regs'' md'
    (Hpc & Hmem & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K25 & K26 & K10 & K24 & K23) Hreg Hmat.
  subst pc' mem'.
  assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
  assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
  assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
  assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
  assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
  assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
  assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
  assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
  assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
  assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
  assert (E23 : getr regs'' 23 = Z_to_bv 64 (Z.of_nat b + 1)) by (rewrite Hreg; exact K23).
  assert (E10 : getr regs'' 10 = Z_to_bv 64 (fr + 544)) by (rewrite Hreg; exact K10).
  assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact K24).
  assert (HFRA' : FRA B APIf ra g fr [] regs'' mem md')
    by exact (sl_fra_move B APIf ra g fr [] regs regs'' mem md md' HFRA E2 E3 E4 E8 E9 E19 E26 Hmat).
  assert (HENT' : ENT APIf g [] mem md') by (eapply ent_mat; [exact HENT | exact Hmat]).
  destruct (r7_rid_skip (g_in g) b Hz) as (EID & EFG).
  assert (Hsp9 : forall off v, spill regs mem off v -> spill regs'' mem off v).
  { intros off v (A1 & HA1' & Hq). exists A1. split; [unfold rg in *; rewrite E9; exact HA1' | exact Hq]. }
  rewrite <- SEGS. apply Hnext.
  exists regs'', mem, md', fr.
  split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
  split; [exact Hgn|].
  split.
  { unfold RS, RB. split; [lia|].
    split.
    { destruct Hcur as (Hc0 & Hc22 & Hc25). unfold CUR, rg in *.
      split; [exact Hc0|]. split; [rewrite E22; exact Hc22 | rewrite E25; exact Hc25]. }
    split; [exact Hour|].
    split; [unfold rg; rewrite E23; f_equal; lia|].
    unfold IDBr, FGBr in *. rewrite EID, EFG. split; [exact HID | exact HFG]. }
  split; [exact HOUTA|].
  split; [exact (Hsp9 _ _ H128)|].
  split.
  { (* push 13B: PRO - the run keeps s1 and the memory *)
    apply (R7tail.r7t_pro_mk g fr regs mem regs'' mem); [intros off v _ Hs; exact (Hsp9 _ _ Hs) | | | |
      exact HPRO]; auto. }
  split; [exact (Hsp9 _ _ H104)|]. split; [exact (Hsp9 _ _ H96)|].
  split; [unfold a0v, rg; exact E10|].
  split; [unfold rg in *; rewrite E24; exact Hr24|].
  split; [exists A; split; [unfold rg in *; rewrite E9; exact Hr9 | exact Hm64]|].
  split; [exact (Hsp9 _ _ H112)|].
  split; [unfold rg; rewrite E21; exact Hr21|].
  split; [exact (Hsp9 _ _ H152)|].
  split; [exact (Hsp9 _ _ H144)|].
  split; [exact HA2176|].
  split; [exact (Hsp9 _ _ H192)|].
  split; [exact HIDB|]. split; [exact HJNK|].
  split; [exact (Hsp9 _ _ H280)|]. split; [exact (Hsp9 _ _ H240)|].
  split; [exact HJY|]. split; [exact HSCR|].
  destruct HRXS as (R48 & R56 & R88 & R80 & R72 & R8 & R0 & R200 & R216 & RA).
  unfold RXS.
  split; [exact (Hsp9 _ _ R48)|]. split; [exact (Hsp9 _ _ R56)|]. split; [exact (Hsp9 _ _ R88)|].
  split; [exact (Hsp9 _ _ R80)|]. split; [exact (Hsp9 _ _ R72)|]. split; [exact (Hsp9 _ _ R8)|].
  split; [exact (Hsp9 _ _ R0)|]. split; [exact (Hsp9 _ _ R200)|]. split; [exact (Hsp9 _ _ R216)|].
  exact RA.
Qed.

(* seg_R7: the malloc exit (n_b != 0), the latch (n_b = 0, b <= 5) and the tail (n_6 = 0; the cut gives b <= 6). *)
Lemma seg_R7 : forall b : nat, Hat B APIf ra (Inv_A81640_at B APIf ra) b ->
  Hat B APIf ra (Inv_A815cc_at B APIf ra) (S b) -> Hcut B APIf ra (Inv_A81ac0 B APIf ra) ->
  Hcut B APIf ra (Inv_A81b10 B APIf ra) ->
  Hat B APIf ra (Inv_A815ec_at B APIf ra) b.
Proof.
  intros b H8 H74 Hp1 Hp2 g c HI.
  destruct (Z.eq_dec (rnb g b) 0) as [Hz|Hnz].
  - assert (Hb6 : (b <= 6)%nat)
      by (destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _); exact Hb).
    destruct (le_lt_dec b 5) as [Hb5|Hb6'].
    + exact (seg_R7_latch b Hb5 H74 g c HI Hz).
    + assert (Eb : b = 6%nat) by lia. subst b.
      exact (R7tail.r7_tail_run B APIf ra empty FF Hp1 Hp2 g c HI Hz).
  - exact (seg_R7_malloc b H8 g c HI Hnz).
Qed.

End S.
