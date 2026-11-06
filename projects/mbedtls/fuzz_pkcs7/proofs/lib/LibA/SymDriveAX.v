(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA Restrict RestrictLib SymDriveA.
Import ListNotations. Import SX2. Import SX2S.

(* [comment removed for export] *)
Ltac solve_kn_inD covtac :=
  lazymatch goal with
  | |- kn_inD ?D ?E ?kn =>
      let K := fresh "Ke" in let HK := fresh "HKe" in
      unfold kn_inD; apply Forall_forall; intros K HK;
      (* [comment removed for export] *)
      repeat (destruct HK as [<- | HK]; [cbn [kentry_inD]; covtac | ]);
      destruct HK
  end.

Ltac run_blockA_with RRUN HR HK fuel stops scr NX keep covtac :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- srealizesJ _ (mkCfg (mkst R (Z_to_bv 64 ?pc) M ?rom) ?model) ?T =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn NX) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
          let c := eval vm_compute in (carry (s_log ss') kn []) in
          lazymatch c with
          | (?kn', ?scs2, ?hs2) =>
            eapply (RRUN fuel stops scr pc sr kn NX ss' scs scr' kn' scs2 hs2 E M R model T);
            [ vm_cast_no_check (@eq_refl _ (ss', scs, scr'))
            | vm_cast_no_check (@eq_refl _ (kn', scs2, hs2))
            | exact HR | exact HK
            | try (solve_kn_inD covtac)
            | try (solve_kn_inD covtac)
            | split_foralls
            | split_foralls
            | try assumption
            | clear HR HK;
              let R' := fresh "R" in let M' := fresh "M" in let EQM := fresh "EQM" in let OUT := fresh "OUT" in
              let mo' := fresh "mo" in let HKM := fresh "HKmo" in let MM := fresh "MM" in
              intros R' M' mo' HR HK EQM OUT HKM MM; cbn [s_pc s_regs s_log] in HR, EQM |- *;
              lazymatch keep with
              | true => idtac
              | false => clear EQM; try clear R; try clear M;
                         try rename R' into R; try rename M' into M
              end ]
          end
        end
      end
    end
  end.

Tactic Notation "run_blockA" constr(RRUN) constr(fuel) constr(stops) constr(scr) constr(NX) constr(keep) tactic3(covtac) :=
  match goal with
  | HR : regs_ok _ _ _, HK : know_ok _ _ _ _ |- _ => run_blockA_with RRUN HR HK fuel stops scr NX keep covtac
  end.
