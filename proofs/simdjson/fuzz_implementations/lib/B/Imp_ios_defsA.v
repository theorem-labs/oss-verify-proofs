(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import FX_Layout.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation bsegs := ImageA.bsegs.
Notation mem := (word -> option byte).
Notation z64 := (Z_to_bv 64 0).

Definition IOS : Z := 0x6bc488.
Definition IOS_LEN : Z := 1952.
Definition LOC_CVC : Z := 0x6bcf40.
Definition LOC_CVW : Z := 0x6bd0d0.
Definition VT_CVC : Z := 0x17e0b0.
Definition VT_CVW : Z := 0x17de00.
Definition CLOC : Z := 0x37998.
Definition LOC_IDC : Z := 0x6bcd70.
Definition LOC_IDW : Z := 0x6bcd80.
Definition LOC_FAC4 : Z := 0x6bd270.
Definition RSTDIN : Z := 0x184be0.
Definition RSTDIN_BUF : Z := 0x6dec08.
Definition F_STDIO_READ : Z := 0x167f90.
Definition F_STDIO_SEEK : Z := 0x1680a8.
Definition F_STDIO_CLOSE : Z := 0x167f64.

Definition ios_cells : list cell := [
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x101);
  C8 (Z_to_bv 64 0x17da38);
  C8 (Z_to_bv 64 0x6bd228);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x184cd0);
  C8 (Z_to_bv 64 0x6bcf40);
  C8 (Z_to_bv 64 0x6bc494);
  C8 (Z_to_bv 64 0x1);
  C8 (Z_to_bv 64 0x17da38);
  C8 (Z_to_bv 64 0x6bd228);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x184af0);
  C8 (Z_to_bv 64 0x6bcf40);
  C8 (Z_to_bv 64 0x6bc49c);
  C8 (Z_to_bv 64 0x1);
  C8 (Z_to_bv 64 0x17db68);
  C8 (Z_to_bv 64 0x6bd228);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x184cd0);
  C8 (Z_to_bv 64 0x6bd0d0);
  C8 (Z_to_bv 64 0x6bc4ac);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x17db68);
  C8 (Z_to_bv 64 0x6bd228);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x184af0);
  C8 (Z_to_bv 64 0x6bd0d0);
  C8 (Z_to_bv 64 0x6bc4b4);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x17d9a0);
  C8 (Z_to_bv 64 0x6bd228);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x184be0);
  C8 (Z_to_bv 64 0x6bcf40);
  C8 (Z_to_bv 64 0x6bc48c);
  C8 (Z_to_bv 64 0xffffffff00000001);
  C8 (Z_to_bv 64 0x100);
  C8 (Z_to_bv 64 0x17dad0);
  C8 (Z_to_bv 64 0x6bd228);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x184be0);
  C8 (Z_to_bv 64 0x6bd0d0);
  C8 (Z_to_bv 64 0x6bc4a4);
  C8 (Z_to_bv 64 0xffffffff00000001);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x17d5d8);
  C8 (Z_to_bv 64 0x17d600);
  C8 (Z_to_bv 64 0x1002);
  C8 (Z_to_bv 64 0x6);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x6bc4c8);
  C8 (Z_to_bv 64 0x6bd228);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0xffffffff);
  C8 (Z_to_bv 64 0x17d6f8);
  C8 (Z_to_bv 64 0x17d720);
  C8 (Z_to_bv 64 0x1002);
  C8 (Z_to_bv 64 0x6);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x6bc588);
  C8 (Z_to_bv 64 0x6bd228);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0xffffffff);
  C8 (Z_to_bv 64 0x17d5d8);
  C8 (Z_to_bv 64 0x17d600);
  C8 (Z_to_bv 64 0x3002);
  C8 (Z_to_bv 64 0x6);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x6bc528);
  C8 (Z_to_bv 64 0x6bd228);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x6bc718);
  C8 (Z_to_bv 64 0xffffffff);
  C8 (Z_to_bv 64 0x17d6f8);
  C8 (Z_to_bv 64 0x17d720);
  C8 (Z_to_bv 64 0x3002);
  C8 (Z_to_bv 64 0x6);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x6bc5e8);
  C8 (Z_to_bv 64 0x6bd228);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x6bc7b8);
  C8 (Z_to_bv 64 0xffffffff);
  C8 (Z_to_bv 64 0x17d5d8);
  C8 (Z_to_bv 64 0x17d600);
  C8 (Z_to_bv 64 0x1002);
  C8 (Z_to_bv 64 0x6);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x6bc528);
  C8 (Z_to_bv 64 0x6bd228);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0xffffffff);
  C8 (Z_to_bv 64 0x17d6f8);
  C8 (Z_to_bv 64 0x17d720);
  C8 (Z_to_bv 64 0x1002);
  C8 (Z_to_bv 64 0x6);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x6bc5e8);
  C8 (Z_to_bv 64 0x6bd228);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0xffffffff);
  C8 (Z_to_bv 64 0x17d588);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x17d5b0);
  C8 (Z_to_bv 64 0x1002);
  C8 (Z_to_bv 64 0x6);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x6bc648);
  C8 (Z_to_bv 64 0x6bd228);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x6bc718);
  C8 (Z_to_bv 64 0xffffffff);
  C8 (Z_to_bv 64 0x17d6a8);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x17d6d0);
  C8 (Z_to_bv 64 0x1002);
  C8 (Z_to_bv 64 0x6);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x6bc6b0);
  C8 (Z_to_bv 64 0x6bd228);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x0);
  C8 (Z_to_bv 64 0x6bc7b8);
  C8 (Z_to_bv 64 0xffffffff)
].
Definition ios_block (m : mem) : Prop := rw_cells bsegs m IOS ios_cells.

Lemma ios_cells_size : cells_size ios_cells = 1952%nat.
Proof. reflexivity. Qed.

Definition locx3 (m : mem) : Prop :=
  rw_cells bsegs m LOC_CVC [C8 (Z_to_bv 64 VT_CVC)]
  /\ rw_cells bsegs m LOC_CVW [C8 (Z_to_bv 64 VT_CVW)]
  /\ rw_cells bsegs m (LOC_CVW + 16) [C8 (Z_to_bv 64 CLOC)].
Definition locx (m : mem) : Prop :=
  locx3 m
  /\ rw_cells bsegs m LOC_IDC [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 5)]
  /\ rw_cells bsegs m LOC_IDW [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 6)]
  /\ rw_cells bsegs m LOC_FAC4 [C8 (Z_to_bv 64 LOC_CVC); C8 (Z_to_bv 64 LOC_CVW)].
Lemma locx_locx3 : forall m, locx m -> locx3 m.
Proof. intros m [H _]. exact H. Qed.

Definition imp_ios (m : mem) : Prop := ios_block m /\ locx3 m.
Definition imp_ios_addr (a : Z) : Prop :=
  (IOS <= a < IOS + IOS_LEN) \/ (LOC_CVC <= a < LOC_CVC + 8) \/ (LOC_CVW <= a < LOC_CVW + 24).

Lemma imp_ios_addr_bounds : forall a, imp_ios_addr a -> IOS <= a < 0x6bdad8.
Proof. intros a Ha. unfold imp_ios_addr, IOS, IOS_LEN, LOC_CVC, LOC_CVW in Ha. unfold IOS. lia. Qed.

Definition stdin_cells : list cell :=
  [C4 (Z_to_bv 64 9); C4 z64;
   C8 z64; C8 z64;
   C8 (Z_to_bv 64 F_STDIO_CLOSE);
   C8 z64; C8 z64; C8 z64; C8 z64;
   C8 (Z_to_bv 64 F_STDIO_READ); C8 z64; C8 (Z_to_bv 64 F_STDIO_SEEK);
   C8 (Z_to_bv 64 RSTDIN_BUF); C8 (Z_to_bv 64 1024);
   C8 z64; C8 z64;
   C4 z64; C4 z64;
   C8 z64;
   C4 z64; C4 (Z_to_bv 64 4294967295);
   C4 z64].
Definition stdin_file0 (m : mem) : Prop := rw_cells bsegs m RSTDIN stdin_cells.
Definition stdin_addr (a : Z) : Prop := RSTDIN <= a < RSTDIN + 148.
Lemma stdin_cells_size : cells_size stdin_cells = 148%nat.
Proof. reflexivity. Qed.

Definition agree_on' (P : Z -> Prop) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> P a -> m' (wa a) = m (wa a) /\ (wview bsegs m (wa a) <> None -> wview bsegs m' (wa a) <> None).

Lemma bytes_at_agree' : forall P m m' A bs,
  agree_on' P m m' -> bytes_at bsegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) ->
  bytes_at bsegs m' A bs.
Proof.
  intros P m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.

Lemma wr_at_agree' : forall P m m' A n,
  agree_on' P m m' -> wr_at bsegs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at bsegs m' A n.
Proof.
  intros P m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W. apply HW. exact Hi.
Qed.

Lemma rw_cells_agree' : forall P m m' A cs,
  agree_on' P m m' -> rw_cells bsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) ->
  rw_cells bsegs m' A cs.
Proof.
  intros P m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply bytes_at_agree'; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply wr_at_agree'; eauto.
Qed.

Lemma ios_block_agree : forall P m m', agree_on' P m m' -> (forall a, IOS <= a < IOS + IOS_LEN -> P a) -> ios_block m -> ios_block m'.
Proof. intros P m m' AG HP H. eapply rw_cells_agree'; [exact AG| exact H|]. rewrite ios_cells_size. intros a Ha. apply HP. unfold IOS_LEN. lia. Qed.

Lemma locx3_agree : forall P m m', agree_on' P m m' -> (forall a, (LOC_CVC <= a < LOC_CVC + 8) \/ (LOC_CVW <= a < LOC_CVW + 24) -> P a) -> locx3 m -> locx3 m'.
Proof.
  intros P m m' AG HP (H1 & H2 & H3).
  split; [eapply rw_cells_agree'; [exact AG| exact H1|]; intros a Ha; apply HP; cbn in Ha; lia|].
  split; [eapply rw_cells_agree'; [exact AG| exact H2|]; intros a Ha; apply HP; cbn in Ha; lia|].
  eapply rw_cells_agree'; [exact AG| exact H3|]; intros a Ha; apply HP; cbn in Ha; lia.
Qed.

Lemma imp_ios_agree : forall P m m', agree_on' P m m' -> (forall a, imp_ios_addr a -> P a) -> imp_ios m -> imp_ios m'.
Proof.
  intros P m m' AG HP [H1 H2]. split.
  - eapply ios_block_agree; [exact AG| | exact H1]. intros a Ha. apply HP. left. exact Ha.
  - eapply locx3_agree; [exact AG| | exact H2]. intros a Ha. apply HP. right. exact Ha.
Qed.

Lemma locx_agree : forall P m m', agree_on' P m m' ->
  (forall a, (LOC_CVC <= a < LOC_CVC + 8) \/ (LOC_CVW <= a < LOC_CVW + 24) \/ (LOC_IDC <= a < LOC_IDC + 12) \/ (LOC_IDW <= a < LOC_IDW + 12) \/ (LOC_FAC4 <= a < LOC_FAC4 + 16) -> P a) ->
  locx m -> locx m'.
Proof.
  intros P m m' AG HP (H3 & H4 & H5 & H6).
  split; [eapply locx3_agree; [exact AG| intros a Ha; apply HP; tauto| exact H3]|].
  split; [eapply rw_cells_agree'; [exact AG| exact H4|]; intros a Ha; apply HP; cbn in Ha; lia|].
  split; [eapply rw_cells_agree'; [exact AG| exact H5|]; intros a Ha; apply HP; cbn in Ha; lia|].
  eapply rw_cells_agree'; [exact AG| exact H6|]; intros a Ha; apply HP; cbn in Ha; lia.
Qed.

Lemma stdin_file0_agree : forall P m m', agree_on' P m m' -> (forall a, stdin_addr a -> P a) -> stdin_file0 m -> stdin_file0 m'.
Proof. intros P m m' AG HP H. eapply rw_cells_agree'; [exact AG| exact H|]. rewrite stdin_cells_size. intros a Ha. apply HP. unfold stdin_addr. lia. Qed.

Lemma agree_on'_of_munch : forall W m m', munch W m m' -> wmono bsegs m m' -> agree_on' (fun a => outside W a) m m'.
Proof.
  intros W m m' MU WM a Ha Ho. split; [| intros H; apply WM; exact H].
  apply MU. unfold wa. rewrite unsigned_lit by lia. exact Ho.
Qed.

Lemma imp_ios_transport : forall W m m', imp_ios m -> munch W m m' -> wmono bsegs m m' ->
  (forall a, imp_ios_addr a -> outside W a) -> imp_ios m'.
Proof. intros W m m' H MU WM HW. eapply imp_ios_agree; [apply (agree_on'_of_munch W m m' MU WM)| exact HW| exact H]. Qed.

Lemma ios_block_transport : forall W m m', ios_block m -> munch W m m' -> wmono bsegs m m' ->
  (forall a, IOS <= a < IOS + IOS_LEN -> outside W a) -> ios_block m'.
Proof. intros W m m' H MU WM HW. eapply ios_block_agree; [apply (agree_on'_of_munch W m m' MU WM)| exact HW| exact H]. Qed.

Lemma locx_transport : forall W m m', locx m -> munch W m m' -> wmono bsegs m m' ->
  (forall a, (LOC_CVC <= a < LOC_CVC + 8) \/ (LOC_CVW <= a < LOC_CVW + 24) \/ (LOC_IDC <= a < LOC_IDC + 12) \/ (LOC_IDW <= a < LOC_IDW + 12) \/ (LOC_FAC4 <= a < LOC_FAC4 + 16) -> outside W a) ->
  locx m'.
Proof. intros W m m' H MU WM HW. eapply locx_agree; [apply (agree_on'_of_munch W m m' MU WM)| exact HW| exact H]. Qed.

Lemma stdin_file0_transport : forall W m m', stdin_file0 m -> munch W m m' -> wmono bsegs m m' ->
  (forall a, stdin_addr a -> outside W a) -> stdin_file0 m'.
Proof. intros W m m' H MU WM HW. eapply stdin_file0_agree; [apply (agree_on'_of_munch W m m' MU WM)| exact HW| exact H]. Qed.
