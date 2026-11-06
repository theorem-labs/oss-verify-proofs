(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec AxSymExec3 AxSymExec3Sound MemSplit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost SegVC SegLin.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import SjVCPre.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SWARZ SLOWG NRMG SLOWV SLOWVA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Module SNVB.
Local Notation u := bv_unsigned.

(* [comment removed for export] *)
Lemma srl_mask_val : forall E v, u (ev E v) < 256 -> 68 <= u (ev E v) <= 131 ->
  u (edenot E (EAlu ALU_SRL (ELit 12884901891) (EAlu ALU_ADD (EExt false 0 1 (EVar v)) (ELit (-68))))) = 12884901891 / 2 ^ (u (ev E v) - 68).
Proof.
  intros E v H1 H2.
  assert (EX : u (edenot E (EAlu ALU_ADD (EExt false 0 1 (EVar v)) (ELit (-68)))) = u (ev E v) - 68).
  { change (edenot E (EAlu ALU_ADD (EExt false 0 1 (EVar v)) (ELit (-68))))
      with (alu64 ALU_ADD (edenot E (EExt false 0 1 (EVar v))) (Z_to_bv 64 (-68))).
    rewrite u_add64, (SNV.u_ext1_v E v H1), u_lit64a. rewrite Z.add_mod_idemp_r by lia. apply Z.mod_small. lia. }
  change (edenot E (EAlu ALU_SRL (ELit 12884901891) (EAlu ALU_ADD (EExt false 0 1 (EVar v)) (ELit (-68)))))
    with (alu64 ALU_SRL (Z_to_bv 64 12884901891) (edenot E (EAlu ALU_ADD (EExt false 0 1 (EVar v)) (ELit (-68))))).
  rewrite u_srl64, EX, u_lit64a. rewrite (Z.mod_small 12884901891 (2^64)) by lia. rewrite (Z.mod_small (u (ev E v) - 68) 64) by lia.
  reflexivity.
Qed.

Ltac snb_mask :=
  match goal with
  | H : Z.land ?X (1 mod 2 ^ 64) <= 0 |- _ =>
    lazymatch X with context [u (edenot ?E (EAlu ALU_SRL (ELit 12884901891) (EAlu ALU_ADD (EExt false 0 1 (EVar ?v)) (ELit (-68)))))] =>
      lazymatch goal with
      | H1 : 0 <= u (ev E v), H2 : u (ev E v) < 256, H3 : 69 <= u (ev E v) - 32 * ((u (ev E v) / 32) mod 2),
        H4 : u (ev E v) - 32 * ((u (ev E v) / 32) mod 2) <= 69 |- _ =>
          let Hc := fresh "Hc" in
          assert (u (ev E v) = 69 \/ u (ev E v) = 101) as [Hc|Hc] by (clear - H1 H2 H3 H4; Z.div_mod_to_equations; lia);
          rewrite (srl_mask_val E v H2 ltac:(rewrite Hc; lia)) in H; rewrite Hc in H;
          exfalso; revert H; vm_compute; intros H; apply H; reflexivity
      end
    end
  end.

(* [comment removed for export] *)
Ltac snb_hmods2 :=
  repeat match goal with H : context [?x mod 2 ^ 64] |- _ =>
    lazymatch x with context [_ mod _] => fail | _ => idtac end;
    rewrite (Z.mod_small x (2 ^ 64)) in H by SNVA.sna_lia_o end.

Ltac snb_solve :=
  SNV.sn_pre; SNVA.sna_sreads; SNV.sn_goal;
  lazymatch goal with HK : know_ok ?segs ?E ?m _ |- _ => SNV.sn_lin segs E m HK; SNV.sn_aluw; SNV.sn_lin segs E m HK end;
  SNVA.sna_ext; SNVA.sna_land; SNVA.sna_bats; SNV.sn_hyps; SNV.sn_clear; SNVA.sna_hmods; SNVA.sna_gmods;
  first [ snb_mask | (repeat split; solve [SNVA.sna_leaf]) ].

(* [comment removed for export] *)
Ltac snb_solve2 :=
  SNV.sn_pre; SNVA.sna_sreads; SNV.sn_goal;
  lazymatch goal with HK : know_ok ?segs ?E ?m _ |- _ => SNV.sn_lin segs E m HK; SNV.sn_aluw; SNV.sn_lin segs E m HK end;
  SNVA.sna_ext; SNVA.sna_land; SNVA.sna_bats; SNV.sn_hyps; SNV.sn_clear; SNVA.sna_hmods; SNVA.sna_gmods; snb_hmods2;
  first [ snb_mask | (repeat split; solve [SNVA.sna_leaf]) ].

End SNVB.
