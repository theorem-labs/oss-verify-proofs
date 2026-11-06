(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibDefsA PmCurDefs PmLibSpecsA PmCurSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeapA CutL5A.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMCSB.
Definition mem := (word -> option byte).

Definition h72 (M : mem) (a : Z) : Prop := byte_at M a 0 /\ exists k, 0 <= k < 128 /\ byte_at M (a + 1) (2 * k).

Definition STR_TRUE_B : Z := 0x25fc0.  Definition STR_FALSE_B : Z := 0x25fe0.  Definition STR_NULL_B : Z := 0x26000.
Section SpecsCB.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IC : PMLA.consts.
Definition opts_atB (vto vto2 vtf : Z) (M : mem) (O : Z) : Prop :=
  L5.defined M O 240 /\ PMLA.u64 (hl_segs L) M O vto /\ PMLA.u32 (hl_segs L) M (O + 8) 0x10100 /\ PMLA.u64 (hl_segs L) M (O + 16) vtf /\
  PMLA.u64 (hl_segs L) M (O + 48) (O + 16) /\ PMLA.u64 (hl_segs L) M (O + 64) vto2 /\ h72 M (O + 72) /\ PMCSA.zeros M (O + 80) 144 /\ PMLA.u32 (hl_segs L) M (O + 224) 1024.
Definition cursor_main_specB (pc vto vto2 vtf : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (C IS O E sp r kx bx : Z) (rep : PML.srep) (g : PML.ls_state),
    PMSA.cps_asan L ar HI pc r sp PMCSA.CCTOR_MAIN_SCR LB FF LK cr A PMCSA.CCTOR_MAIN_D
      (fun R M => PMSA.a0 R C /\ PMSA.a3 R IS /\ PMSA.a4 R O /\ PMCSA.a5 R E /\ PMCSA.cctor_preA L ar IC M FF cr LB C IS E sp PMCSA.CCTOR_MAIN_SCR kx bx rep g /\
                  opts_atB vto vto2 vtf M O /\ PMSA.fobj M FF O 240 /\ PMLA.apart C PMCSA.CURSOR_SIZE O 240 /\ PMLA.apart IS 272 O 240 /\ PMLA.apart E 16 O 240)
      (fun R M R' M' LB' cr' LBk W => PMCSA.cctor_postA L IC LB C IS E kx bx rep g M' LB' cr' LBk W).

Definition cstr_ctor_specB (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o src sp r : Z) (txt : list Z),
    PMSA.cps_asan L ar HI pc r sp (64 + PMSA.OPNEW_SCR) LB FF LK cr A 0
      (fun R M => PMSA.a0 R o /\ PMSA.a1 R src /\
                  In (src, txt) [(STR_NULL_B, [110; 117; 108; 108]); (STR_TRUE_B, [116; 114; 117; 101]); (STR_FALSE_B, [102; 97; 108; 115; 101])] /\
                  PMLA.img_ro IC M /\ shadow_blk M src (Z.of_nat (length txt) + 1) /\ PMSA.fobj M FF o 24 /\ L5.defined M o 24 /\ PMSA.stksh ar M sp (64 + PMSA.OPNEW_SCR))
      (fun R M R' M' LB' cr' LBk W => W = [(o, 24)] /\ LBk = LB /\ PMLA.str_at_w (hl_segs L) M' o (PML.SShort txt) /\ LB' = LB /\ cr' = cr).

Lemma opts_A_B : forall vto vto2 vtf M O, PMCSA.opts_atA L vto vto2 vtf M O -> opts_atB vto vto2 vtf M O.
Proof.
  intros vto vto2 vtf M O (D & A1 & A2 & A3 & A4 & A5 & Z72 & Z80 & A6). repeat (split; [assumption|]).
  split; [|split; assumption]. split; [pose proof (Z72 0 ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X|]. exists 0. split; [lia|]. exact (Z72 1 ltac:(lia)).
Qed.
Lemma main_B_A : forall pc vto vto2 vtf, cursor_main_specB pc vto vto2 vtf -> PMCSA.cursor_main_specA L ar HI IC pc vto vto2 vtf.
Proof.
  intros pc vto vto2 vtf H LB FF LK cr A C IS O E sp r kx bx rep g. unfold PMCSA.cursor_main_specA, PMSA.cps_asan in *.
  intros fx R M model K I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 HP HC.
  apply (H LB FF LK cr A C IS O E sp r kx bx rep g fx R M model K I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11); [|exact HC].
  destruct HP as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj (opts_A_B _ _ _ _ _ X6) (conj X7 (conj X8 (conj X9 X10))))))))).
Qed.
End SpecsCB.
End PMCSB.
