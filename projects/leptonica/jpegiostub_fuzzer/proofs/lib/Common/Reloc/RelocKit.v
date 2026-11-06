(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import PropExec SeqExec StepTac Hoare WalkTac.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Reloc Require Export Reloc RelocBlocks RelocCode CanonCode RelocSites CanonSites RelocImg CanonImg.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac rl_site_lo12 b ca c2 :=
  let r := eval vm_compute in (site_find canon_sites 0%nat c2) in
  lazymatch r with
  | Some (?i, _, SK_lo12 _ ?X ?t) =>
      let E := fresh "RLV" in
      assert (E : v_addi (rl_hi b ca) (bv_signed (rl_imm12 c2)) = rl (rl_delta X) t)
        by exact (rl_site_V i _ ca X t eq_refl eq_refl);
      rewrite E; clear E
  | _ => fail "rl_site_lo12: no lo12 site at" c2
  end.

(* [comment removed for export] *)
Ltac rl_site_jal b c :=
  let r := eval vm_compute in (site_find canon_sites 0%nat c) in
  lazymatch r with
  | Some (?i, _, SK_jal ?X ?t) =>
      let E := fresh "RLJ" in
      assert (E : btgt (rl (rl_delta b) c) (bv_signed (rl_imm21 c)) = rl (rl_delta X) t)
        by exact (rl_site_J i _ X t eq_refl eq_refl);
      rewrite E; clear E
  | _ => fail "rl_site_jal: no jal site at" c
  end.

(* [comment removed for export] *)
Ltac rl_val_s v :=
  lazymatch v with
  | v_auipc (rl (rl_delta ?b) ?c) (Z.shiftl (bv_signed (rl_imm20 ?c)) 12) =>
      change v with (rl_hi b c)
  | v_addi (rl_hi ?b ?ca) (bv_signed (rl_imm12 ?c2)) => rl_site_lo12 b ca c2
  | btgt (rl (rl_delta ?b) ?c) (bv_signed (rl_imm21 ?c)) => rl_site_jal b c
  | _ => rl_val v
  end.

Ltac rl_pc_s p :=
  lazymatch p with
  | btgt (rl (rl_delta ?b) ?c) (bv_signed (rl_imm21 ?c)) => rl_site_jal b c
  | _ => rl_pc p
  end.

#[export] Ltac norm_pc_state st ::=
  tryif has_evar st then idtac
  else lazymatch st with
       | mkst _ ?p _ _ => first [ rl_pc_s p | wlit p ]
       | _ => idtac
       end.

#[export] Ltac vals_lit ::=
  repeat match goal with
         | |- context [regupd _ _ ?v] => first [ val_lit v | rl_val_s v ]
         end.

(* [comment removed for export] *)
Ltac rl_norm_s :=
  repeat match goal with
         | |- context [v_auipc (rl ?d ?c) ?e] => rl_val_s (v_auipc (rl d c) e)
         | |- context [v_addi (rl_hi ?b ?ca) ?e] => rl_val_s (v_addi (rl_hi b ca) e)
         | |- context [v_addi (rl ?d ?c) ?e] => rl_val_s (v_addi (rl d c) e)
         | |- context [at_ (rl ?d ?c) ?e] => rl_val_s (at_ (rl d c) e)
         | |- context [btgt (rl ?d ?c) ?e] => rl_val_s (btgt (rl d c) e)
         end.

#[export] Ltac imm_norm ::=
  repeat match goal with
  | |- context [bv_signed ?b] =>
      lazymatch b with
      | @BV _ _ _ =>
          let v := eval vm_compute in (bv_signed b) in
          change (bv_signed b) with v
      end
  | |- context [bv_unsigned ?b] =>
      lazymatch b with
      | @BV _ _ _ =>
          let v := eval vm_compute in (bv_unsigned b) in
          change (bv_unsigned b) with v
      end
  end;
  rl_norm_s.
