(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame SysStep.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg ABase.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import PA2_kz.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA2 Require A2F_defs A2F_cert.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegProg SegLib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Local Notation M64 := 18446744073709551616.

Section S_T0F.
  Context {rc : runConstT}.
  Variables (zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 : Z)
            (T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG : Z) (RC : Z) (rest : list Z).
  Definition ZL_t0f : list Z :=
    [zra; SP16; zgp; ztp; zs0; zs1; zs2; zs3; zs4; zs5; zs6; zs7; zs8; zs9; zs10; zs11;
     T8; DOC8; B8; LEN; I8; N; TB8; CAPT; SB8; CAPS; OC8; IA8; F11; PB; FLAG; BO; BG; IG; SG; RC] ++ rest.
  Variable zsp : Z.
  Hypothesis E_SP : zsp = 16 * SP16.
  Variable m : word -> option byte.
  Hypothesis H_RC : 0 <= RC <= 63.
  Hypothesis H_SP : 0x7fff00000000 <= zsp <= 2 ^ 47.
  Hypothesis M_SAVED : forall k, 0 <= k < 13 ->
    bytes_at asegs m (zsp - 8 - 8 * k) (word_to_le_bytes 8 (Z_to_bv 64 (nth (Z.to_nat k) [zra; zs0; zs1; zs2; zs3; zs4; zs5; zs6; zs7; zs8; zs9; zs10; zs11] 0))).

  Lemma t0f_kn : know_ok asegs (mkEZ ZL_t0f) m A2F_defs.T0_kn.
  Proof.
    unfold A2F_defs.T0_kn.
    cbv [A2F_defs.vSP A2F_defs.vSP16 A2F_defs.vRA A2F_defs.vS0 A2F_defs.vS1 A2F_defs.vS2 A2F_defs.vS3 A2F_defs.vS4 A2F_defs.vS5
         A2F_defs.vS6 A2F_defs.vS7 A2F_defs.vS8 A2F_defs.vS9 A2F_defs.vS10 A2F_defs.vS11 A2F_defs.V A2F_defs.mul].
    repeat (apply Forall_cons; [
      lazymatch goal with
      | |- kentry_ok _ _ _ (KRange _ _ _) => apply kz_range; [reflexivity | cbn [zden nth ZL_t0f app]; zsolve]
      | |- kentry_ok _ _ _ (KWord (SA (EMd M_MUL (ELit 16) (EVar 1)) ?o) _ _) =>
          let k := eval vm_compute in ((- o - 8) / 8) in
          solve [ apply kz_word; [reflexivity | (clear_quant; lia) | cbn [zden nth ZL_t0f app]; zsolve |
                  cbn [zden nth ZL_t0f app]; rewrite <- ?E_SP; rewrite !(Z.mod_small _ M64) by (clear_quant; lia);
                  replace (zsp + _) with (zsp - 8 - 8 * k) by lia; exact (M_SAVED k ltac:(lia)) ] ]
      end |]).
    apply Forall_nil.
  Qed.
End S_T0F.

(* [comment removed for export] *)
Definition GP0a : nat -> list word -> (word -> option byte) -> Prop := fun _ _ _ => True.
Lemma GP0a_frame : SG.gp_frameP GP0a (fun _ _ => []). Proof. intros id args E M M' _ _. exact I. Qed.
Lemma GP0a_vc : forall c, (fun _ : SG.vc => false) c = true -> SG.vc_holds A2F_defs.SG GP0a c. Proof. intros c H. discriminate H. Qed.

Lemma a2f_run : forall E m rom R (F : bvmap 5 word) (fc : bv 32),
  SX.aw_genuine E (SP.p_A A2F_defs.A2F) -> rfull R -> regs_ok E A2F_defs.T0_regs R -> know_ok A2F_defs.SG E m A2F_defs.T0_kn ->
  mem_inv A2F_defs.SG m -> frm0 fc ->
  ExecF.evtF A2F_defs.SG (SX.fp_of (SP.p_A A2F_defs.A2F) E) (SLib.xpost A2F_defs.SG GP0a A2F_defs.A2F E m rom)
    (MS R F (Z_to_bv 64 0xa8500) fc None m rom).
Proof.
  intros E m rom R F fc HAG HF HR HK MI HZ.
  exact (SLib.prog_evt A2F_defs.SG GP0a (fun _ _ => []) (fun _ => false) GP0a_frame GP0a_vc A2F_defs.A2F A2F_defs.A2F_IT 200 false []
           A2F_defs.T0 A2F_cert.a2f_cert (SP.itab_ranges_sound A2F_defs.SG _) ltac:(intros TA []) ltac:(intros Sm [])
           ltac:(left; reflexivity) E m rom R F fc HAG HF HR HK (Forall_nil _) MI HZ).
Qed.
