(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require PropExec CatSim SymExec3 SymExec3Sound.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BExec BLFrame BegsEquivM LbB_Bridge.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation getr := PropExec.getr.

Definition kv (sr : list SymExec3.SX2.expr) (r : reg) (x y : word) : word :=
  if SymExec3.SX2.expr_eqb (SymExec3.SX2.sr_get sr r) (SymExec3.SX2.EVar (Z.to_N (bv_unsigned r))) then x else y.

Lemma kv_ok : forall R vals sr R' (r : reg) x,
  SymExec3Sound.SX2S.regs_ok (HLib.Eseed R vals) sr R' -> getr R r = x -> getr R' r = kv sr r x (getr R' r).
Proof.
  intros R vals sr R' r x HR Hx. unfold kv.
  destruct (SymExec3.SX2.expr_eqb _ _) eqn:E; [|reflexivity].
  apply SymExec3Sound.SX2S.expr_eqb_eq in E. rewrite (HR r), E. cbn [SymExec3.SX2.edenot].
  rewrite <- Hx.
  rewrite HLib.Eseed_regZ. reflexivity.
Qed.

Lemma regs_keep_mkR : forall R vals sr R' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  R = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ->
  SymExec3Sound.SX2S.regs_ok (HLib.Eseed R vals) sr R' -> rfull R' ->
  R' = mkR (kv sr 1 x1 (getr R' 1)) (kv sr 2 x2 (getr R' 2)) (kv sr 3 x3 (getr R' 3)) (kv sr 4 x4 (getr R' 4))
           (kv sr 5 x5 (getr R' 5)) (kv sr 6 x6 (getr R' 6)) (kv sr 7 x7 (getr R' 7)) (kv sr 8 x8 (getr R' 8))
           (kv sr 9 x9 (getr R' 9)) (kv sr 10 x10 (getr R' 10)) (kv sr 11 x11 (getr R' 11)) (kv sr 12 x12 (getr R' 12))
           (kv sr 13 x13 (getr R' 13)) (kv sr 14 x14 (getr R' 14)) (kv sr 15 x15 (getr R' 15)) (kv sr 16 x16 (getr R' 16))
           (kv sr 17 x17 (getr R' 17)) (kv sr 18 x18 (getr R' 18)) (kv sr 19 x19 (getr R' 19)) (kv sr 20 x20 (getr R' 20))
           (kv sr 21 x21 (getr R' 21)) (kv sr 22 x22 (getr R' 22)) (kv sr 23 x23 (getr R' 23)) (kv sr 24 x24 (getr R' 24))
           (kv sr 25 x25 (getr R' 25)) (kv sr 26 x26 (getr R' 26)) (kv sr 27 x27 (getr R' 27)) (kv sr 28 x28 (getr R' 28))
           (kv sr 29 x29 (getr R' 29)) (kv sr 30 x30 (getr R' 30)) (kv sr 31 x31 (getr R' 31)).
Proof.
  intros R vals sr R' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    HRe HR HF.
  rewrite (rfull_eq R' HF) at 1. f_equal; (eapply kv_ok; [exact HR | subst R; reflexivity]).
Qed.

Ltac pick sr r x y :=
  let b := eval vm_compute in (SymExec3.SX2.expr_eqb (SymExec3.SX2.sr_get sr r) (SymExec3.SX2.EVar (Z.to_N (bv_unsigned r)))) in
  lazymatch b with true => x | false => y end.
Ltac readback HR' HF HRe H :=
  lazymatch type of HRe with
  | ?R = mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31 =>
    lazymatch type of HR' with
    | SymExec3Sound.SX2S.regs_ok _ ?sr ?R' =>
      let v1 := pick sr (1%bv : reg) x1 (getr R' (1%bv : reg)) in
      let v2 := pick sr (2%bv : reg) x2 (getr R' (2%bv : reg)) in
      let v3 := pick sr (3%bv : reg) x3 (getr R' (3%bv : reg)) in
      let v4 := pick sr (4%bv : reg) x4 (getr R' (4%bv : reg)) in
      let v5 := pick sr (5%bv : reg) x5 (getr R' (5%bv : reg)) in
      let v6 := pick sr (6%bv : reg) x6 (getr R' (6%bv : reg)) in
      let v7 := pick sr (7%bv : reg) x7 (getr R' (7%bv : reg)) in
      let v8 := pick sr (8%bv : reg) x8 (getr R' (8%bv : reg)) in
      let v9 := pick sr (9%bv : reg) x9 (getr R' (9%bv : reg)) in
      let v10 := pick sr (10%bv : reg) x10 (getr R' (10%bv : reg)) in
      let v11 := pick sr (11%bv : reg) x11 (getr R' (11%bv : reg)) in
      let v12 := pick sr (12%bv : reg) x12 (getr R' (12%bv : reg)) in
      let v13 := pick sr (13%bv : reg) x13 (getr R' (13%bv : reg)) in
      let v14 := pick sr (14%bv : reg) x14 (getr R' (14%bv : reg)) in
      let v15 := pick sr (15%bv : reg) x15 (getr R' (15%bv : reg)) in
      let v16 := pick sr (16%bv : reg) x16 (getr R' (16%bv : reg)) in
      let v17 := pick sr (17%bv : reg) x17 (getr R' (17%bv : reg)) in
      let v18 := pick sr (18%bv : reg) x18 (getr R' (18%bv : reg)) in
      let v19 := pick sr (19%bv : reg) x19 (getr R' (19%bv : reg)) in
      let v20 := pick sr (20%bv : reg) x20 (getr R' (20%bv : reg)) in
      let v21 := pick sr (21%bv : reg) x21 (getr R' (21%bv : reg)) in
      let v22 := pick sr (22%bv : reg) x22 (getr R' (22%bv : reg)) in
      let v23 := pick sr (23%bv : reg) x23 (getr R' (23%bv : reg)) in
      let v24 := pick sr (24%bv : reg) x24 (getr R' (24%bv : reg)) in
      let v25 := pick sr (25%bv : reg) x25 (getr R' (25%bv : reg)) in
      let v26 := pick sr (26%bv : reg) x26 (getr R' (26%bv : reg)) in
      let v27 := pick sr (27%bv : reg) x27 (getr R' (27%bv : reg)) in
      let v28 := pick sr (28%bv : reg) x28 (getr R' (28%bv : reg)) in
      let v29 := pick sr (29%bv : reg) x29 (getr R' (29%bv : reg)) in
      let v30 := pick sr (30%bv : reg) x30 (getr R' (30%bv : reg)) in
      let v31 := pick sr (31%bv : reg) x31 (getr R' (31%bv : reg)) in
      assert (H : R' = mkR v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31)
        by exact (regs_keep_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRe HR' HF)
    end
  end.

Ltac xrun_at fxg segs R pc M rom HR HK fuel stops scr nx :=
  lazymatch type of HR with
  | SymExec3Sound.SX2S.regs_ok ?E ?sr R =>
    lazymatch type of HK with
    | SymExec3Sound.SX2S.know_ok segs _ M ?kn =>
        let r := eval vm_compute in (SymExec3.SX2.sym_exec segs fuel true stops scr (SymExec3.SX2.SS pc sr [] kn nx) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
            let Hsc := fresh "Hsc" in
            assert (Hsc : SymExec3Sound.SX2S.scs_denot segs M E scs);
            [ | let R' := fresh "R'" in let HR' := fresh "HR'" in
                let Hlf := fresh "Hlf" in let Hms := fresh "Hms" in
                destruct (@SymRun3.run_sound fxg segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R
                           ltac:(vm_cast_no_check (@eq_refl _ (ss', scs, scr'))) HR HK Hsc)
                  as (R' & HR' & Hlf & Hms);
                clear Hsc; cbn [SymExec3.SX2.s_pc SymExec3.SX2.s_regs SymExec3.SX2.s_log SymExec3Sound.SX2S.mem_denot] in HR', Hlf, Hms ]
        end
    end
  end.

Lemma inb_In : forall (r : reg) (l : list reg), existsb (fun x => bv_eqb r x) l = true -> In r l.
Proof.
  intros r l. induction l as [|x l IH]; cbn [existsb]; [discriminate|].
  intros Hb. apply orb_true_iff in Hb as [Hb|Hb].
  - left. unfold bv_eqb in Hb. apply Z.eqb_eq in Hb. apply bv_eq in Hb. symmetry. exact Hb.
  - right. exact (IH Hb).
Qed.
Ltac inb := apply inb_In; vm_cast_no_check (@eq_refl bool true).

Section WithSegs.
Variable segs : list Segment.

Lemma blk_then : forall (Q : machine_state -> Prop) R0 F fc pc0 M0 ro R1 pc1 M1,
  CatSim.msteps segs (MS R0 F pc0 fc None M0 ro) (MS R1 F pc1 fc None M1 ro) ->
  rfull R0 ->
  (rfull R1 -> evt segs Q (MS R1 F pc1 fc None M1 ro)) ->
  evt segs Q (MS R0 F pc0 fc None M0 ro).
Proof.
  intros Q R0 F fc pc0 M0 ro R1 pc1 M1 ro' HF K.
  eapply evt_of_msteps; [exact ro' |]. apply K. exact (msteps_full segs _ _ ro' HF).
Qed.

Lemma MS_full_eq : forall R F pc fc m ro, rfull R ->
  MS R F pc fc None m ro =
  MS (mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
          (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
          (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
          (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)) F pc fc None m ro.
Proof. intros R F pc fc m ro HF. rewrite (rfull_eq R HF) at 1. reflexivity. Qed.
End WithSegs.

