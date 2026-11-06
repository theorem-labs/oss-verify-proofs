(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac Image ZBridge ITree Nodes Decode SysStep Arr FP Bytes InitMem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface F_syscalls StdioFiles Stdio_kit MonadF AIos_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Ltac pick_in := (left; reflexivity) + (right; pick_in).
Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition exit_img_ranges : list (Z * Z) :=
  [(0x6adba8, 0x6ae200);      (* [comment removed for export] *)
   (0x6ae660, 0x6ae668);      (* [comment removed for export] *)
   (0x6ae7f0, 0x6ae808);      (* [comment removed for export] *)
   (0x6afad8, 0x6afae0);      (* [comment removed for export] *)
   (0x178894, 0x178895);      (* [comment removed for export] *)
   (0x16bf18, 0x16bf28)].     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition exit_ci_need : list (Z * Z) :=
  [(0x6afa60, 0x6afa68); (0x6cfd78, 0x6cfd80); (0x6cfd98, 0x6cfda8); (0x6cfb58, 0x6cfd78); (0x6cfb48, 0x6cfb50);
   (0x20cf20, 0x20cf21); (0x177a10, 0x177a11); (0x173e60, 0x173e68);
   (0x6d01f8, 0x6d0b40); (0x176de8, 0x176df0); (0x176d00, 0x176d90); (0x176ed8, 0x176ee0); (0x176cf8, 0x176d00);
   (RSTDERR, RSTDERR + 232); (RSTDOUT, RSTDOUT + 232)] ++ exit_img_ranges.

Section Kit.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Hypothesis EXIT_CI : forall iv, In iv exit_ci_need -> In iv CI.

  (* [comment removed for export] *)
  Section Pres.
    Variables (P : Z -> Prop) (SP : Z) (m m' : mem).
    Hypothesis HP : magree bsegs P m m'.
    Hypothesis HPC : forall a, in_ranges CI a \/ (SP <= a < 2^47) -> ~ (0x6ad760 <= a < 0x6ad778) -> P a.

    Lemma xp_ci : forall A cs lo hi,
      rw_cells bsegs m A cs -> In (lo, hi) exit_ci_need -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
      A + Z.of_nat (cells_size cs) <= 0x6ad760 \/ 0x6ad778 <= A ->
      rw_cells bsegs m' A cs.
    Proof.
      intros A cs lo hi H HIN H1 H2 HV. eapply rw_cells_magree; [exact HP | exact H |].
      intros a Ha. apply HPC; [left; exists (lo, hi); split; [apply EXIT_CI; exact HIN | cbn [fst snd]; lia] | lia].
    Qed.

    Lemma xp_stack : forall A cs,
      rw_cells bsegs m A cs -> SP <= A -> A + Z.of_nat (cells_size cs) <= 2^47 -> 0x6ad778 <= A -> rw_cells bsegs m' A cs.
    Proof.
      intros A cs H H1 H2 HV. eapply rw_cells_magree; [exact HP | exact H |]. intros a Ha. apply HPC; [right; lia | lia].
    Qed.
  End Pres.

  (* [comment removed for export] *)
  Lemma relro_bytes : forall L RNG st LB m A bs cs,
    AHEAP AI L RNG st LB m -> ARELRO_LO <= A -> A + Z.of_nat (length bs) <= ARELRO_HI ->
    rw_bytes_b bsegs A bs = true -> cells_wf cs -> cells_bytes cs = bs -> cells_size cs = length bs ->
    rw_cells bsegs m A cs.
  Proof.
    intros L RNG st LB m A bs cs AH HLO HHI HB WF EB ES. pose proof (AI_relro AI L RNG st LB m AH) as R.
    eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m A bs);
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; lia
      | exact HB | unfold ARELRO_LO in *; lia | unfold ARELRO_HI in *; lia ]
      | exact WF | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact EB | cbn [cells_size csize]; rewrite Nat.add_0_r; exact ES].
  Qed.

  Ltac relro1 AH v := eapply (relro_bytes _ _ _ _ _ _ (le8 (Z_to_bv 64 v))); [exact AH | unfold ARELRO_LO; lia | rewrite length_le8; unfold ARELRO_HI; lia
                        | vm_compute; reflexivity | cbn; split; exact I | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity | rewrite length_le8; reflexivity].
  Ltac relro2 AH v w := eapply (relro_bytes _ _ _ _ _ _ (le8 (Z_to_bv 64 v) ++ le8 (Z_to_bv 64 w)));
                        [exact AH | unfold ARELRO_LO; lia | rewrite length_app, !length_le8; unfold ARELRO_HI; lia
                        | vm_compute; reflexivity | cbn; repeat split | cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity | rewrite length_app, !length_le8; reflexivity].

  Lemma exit_relro_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m ->
       rw_cells bsegs m 0x171ff0 [C8 (Z_to_bv 64 0x178878)]
    /\ rw_cells bsegs m 0x172e08 [C8 (Z_to_bv 64 0x16bf28); C8 (Z_to_bv 64 0x16bf18)]
    /\ rw_cells bsegs m 0x171fc8 [C8 (Z_to_bv 64 0x152b80); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)].
  Proof.
    intros L RNG st LB m AH. unfold got_ssp, ssp_guard.
    split; [relro1 AH 0x178878|]. split; [relro2 AH 0x16bf28 0x16bf18|]. split; [relro2 AH 0x152b80 0| relro1 AH 0x6cfb48].
  Qed.

  Section Pres2.
    Variables (P : Z -> Prop) (SP : Z) (m m' : mem).
    Hypothesis HP : magree bsegs P m m'.
    Hypothesis HPC : forall a, in_ranges CI a \/ (SP <= a < 2^47) -> ~ (0x6ad760 <= a < 0x6ad778) -> P a.

    (* [comment removed for export] *)
    Lemma ios_cells_pres : forall L RNG st LB', AHEAP AI L RNG st LB' m' -> ios_cells m -> ios_cells m'.
    Proof.
      intros L RNG st LB' AH IOS.
      assert (X : forall A cs lo hi, rw_cells bsegs m A cs -> In (lo, hi) exit_ci_need -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
                    A + Z.of_nat (cells_size cs) <= 0x6ad760 \/ 0x6ad778 <= A -> rw_cells bsegs m' A cs)
        by (intros A cs lo hi H HIN H1 H2 H3; eapply (xp_ci P SP m m' HP HPC); eauto).
      unfold ios_cells, ios_char_shared, ios_cout, ios_clog, ios_wide_shared, ios_wcout, ios_wclog in *.
      repeat match goal with H : _ /\ _ |- _ => destruct H end.
      repeat match goal with |- _ /\ _ => split end;
        first [ (eapply (X _ _ 0x6adba8 0x6ae200); [eassumption | unfold exit_ci_need, exit_img_ranges; cbn [app]; pick_in | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia])
              | (eapply (X _ _ 0x6ae660 0x6ae668); [eassumption | unfold exit_ci_need, exit_img_ranges; cbn [app]; pick_in | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia])
              | (eapply (X _ _ 0x6ae7f0 0x6ae808); [eassumption | unfold exit_ci_need, exit_img_ranges; cbn [app]; pick_in | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia])
              | (eapply (X _ _ 0x6afad8 0x6afae0); [eassumption | unfold exit_ci_need, exit_img_ranges; cbn [app]; pick_in | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia])
              | relro1 AH 8 | relro1 AH 0x114cc4 | relro1 AH 0x13c608 | relro1 AH 0x115428 | relro1 AH 0x13cdd4 ].
    Qed.

    Lemma stdout_file_pres : forall so, stdout_file m so -> stdout_file m' so.
    Proof.
      intros so (flags & mode & tail & bufbytes & F1 & F2 & F3 & F4 & F5 & F6).
      exists flags, mode, tail, bufbytes. split; [| split; [exact F2| split; [| split; [exact F4| split; [exact F5| exact F6]]]]].
      - eapply (xp_ci P SP m m' HP HPC _ _ RSTDOUT (RSTDOUT + 232)); [exact F1 | unfold exit_ci_need, exit_img_ranges; cbn [app]; pick_in | lia | unfold file_cells; cbn [cells_size csize Nat.add]; lia | unfold file_cells; cbn [cells_size csize Nat.add]; lia].
      - eapply (xp_ci P SP m m' HP HPC _ _ 0x6d01f8 0x6d0b40); [exact F3 | unfold exit_ci_need, exit_img_ranges; cbn [app]; pick_in | lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia].
    Qed.

    Lemma stderr_file_pres : stderr_file m -> stderr_file m'.
    Proof.
      intros (flags & mode & e & wend & tail & F1). exists flags, mode, e, wend, tail.
      eapply (xp_ci P SP m m' HP HPC _ _ RSTDERR (RSTDERR + 232)); [exact F1 | unfold exit_ci_need, exit_img_ranges; cbn [app]; pick_in | lia | unfold file_cells; cbn [cells_size csize Nat.add]; lia | unfold file_cells; cbn [cells_size csize Nat.add]; lia].
    Qed.
  End Pres2.

  (* [comment removed for export] *)
  Lemma aheap_pres_HPC : forall LB SP a, in_ranges CI a \/ (SP <= a < 2^47) -> ~ (0x6ad760 <= a < 0x6ad778) -> aclient_addr CI LB SP a.
  Proof. intros LB SP a [H|H] _; [right; left; exact H | left; exact H]. Qed.
  Lemma ios_cells_aheap_pres : forall L RNG st LB LB' SP m m',
    aheap_pres CI LB SP m m' -> AHEAP AI L RNG st LB' m' -> ios_cells m -> ios_cells m'.
  Proof. intros L RNG st LB LB' SP m m' HP AH IOS. eapply (ios_cells_pres (aclient_addr CI LB SP) SP m m' HP (aheap_pres_HPC LB SP)); eassumption. Qed.
End Kit.
End CANSEC1.

