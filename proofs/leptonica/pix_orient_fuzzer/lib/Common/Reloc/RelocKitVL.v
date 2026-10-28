(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec SeqExec StepTac Hoare WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Export RelocKit RelocBlocksVL CanonCodeVL CanonSitesVL.
Import ListNotations.
Open Scope bv_scope.

#[export] Ltac rl_site_lo12 b ca c2 ::=
  let r := eval vm_compute in (site_find canon_sites_VL 0%nat c2) in
  lazymatch r with
  | Some (?i, _, SK_lo12 _ ?X ?t) =>
      let E := fresh "RLV" in
      assert (E : v_addi (rl_hi b ca) (bv_signed (rl_imm12 c2)) = rl (rl_delta X) t)
        by exact (rl_site_V_VL i _ ca X t eq_refl eq_refl);
      rewrite E; clear E
  | _ =>
      let r2 := eval vm_compute in (site_find canon_sites 0%nat c2) in
      lazymatch r2 with
      | Some (?i, _, SK_lo12 _ ?X ?t) =>
          let E := fresh "RLV" in
          assert (E : v_addi (rl_hi b ca) (bv_signed (rl_imm12 c2)) = rl (rl_delta X) t)
            by exact (rl_site_V i _ ca X t eq_refl eq_refl);
          rewrite E; clear E
      | _ => fail "rl_site_lo12: no lo12 site at" c2
      end
  end.

#[export] Ltac rl_site_jal b c ::=
  let r := eval vm_compute in (site_find canon_sites_VL 0%nat c) in
  lazymatch r with
  | Some (?i, _, SK_jal ?X ?t) =>
      let E := fresh "RLJ" in
      assert (E : btgt (rl (rl_delta b) c) (bv_signed (rl_imm21 c)) = rl (rl_delta X) t)
        by exact (rl_site_J_VL i _ X t eq_refl eq_refl);
      rewrite E; clear E
  | _ =>
      let r2 := eval vm_compute in (site_find canon_sites 0%nat c) in
      lazymatch r2 with
      | Some (?i, _, SK_jal ?X ?t) =>
          let E := fresh "RLJ" in
          assert (E : btgt (rl (rl_delta b) c) (bv_signed (rl_imm21 c)) = rl (rl_delta X) t)
            by exact (rl_site_J i _ X t eq_refl eq_refl);
          rewrite E; clear E
      | _ => fail "rl_site_jal: no jal site at" c
      end
  end.
