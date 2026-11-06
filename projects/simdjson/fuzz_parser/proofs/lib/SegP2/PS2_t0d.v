(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec Mem Cells Step Frame SysStep.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry P2D_defs PS2_t0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Local Notation M64 := 18446744073709551616.
Notation ATOPM := 140737479966720%Z (only parsing).

Section T0DB.
  Variables (zra zsp zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 : Z)
            (THIS DOC BUF LEN IDX N TBASE CAPT SBASE CAPS OCB IAB RC TW : Z) (rest : list Z).
  (* [comment removed for export] *)
  Definition ZLD1 : list Z :=
    [zra; zsp; zgp; ztp; zs0; zs1; zs2; zs3; zs4; zs5; zs6; zs7; zs8; zs9; zs10; zs11;
     THIS; DOC; BUF; LEN; IDX; N; TBASE; CAPT; SBASE; CAPS; OCB; IAB; RC] ++ rest.
  Definition ZLD2 : list Z :=
    [zra; zsp; zgp; ztp; zs0; zs1; zs2; zs3; zs4; zs5; zs6; zs7; zs8; zs9; zs10; zs11;
     THIS; DOC; BUF; LEN; IDX; N; TBASE; CAPT; SBASE; CAPS; OCB; IAB; RC; TW] ++ rest.
  Variable m : word -> option byte.
  Variable lo : Z.
  Hypothesis H_N : 1 <= N <= 1048512.
  Hypothesis H_CAPT : N + 3 <= CAPT <= 16777216.
  Hypothesis H_TW : 8 <= TW <= 24 /\ TW mod 8 = 0.
  Hypothesis H_SP : 0x7fff00000000 <= zsp <= 2 ^ 47.
  Hypothesis H_SPa : zsp mod 16 = 0.
  Hypothesis H_DOC : zsp <= DOC /\ DOC + 16 <= 2 ^ 64 - 16 /\ DOC mod 8 = 0.
  Hypothesis H_THIS : 16 <= THIS /\ THIS mod 16 = 0 /\ THIS + 96 <= ATOPM /\ THIS + 96 + 2928 <= zsp.
  Hypothesis H_IDX : 16 <= IDX /\ IDX mod 16 = 0 /\ IDX + 4 * N + 12 <= ATOPM /\ IDX + 4 * N + 12 + 2928 <= zsp.
  Hypothesis H_TB : 16 <= TBASE /\ TBASE mod 16 = 0 /\ TBASE + 8 * CAPT <= ATOPM /\ TBASE + 8 * CAPT + 2928 <= zsp.
  Hypothesis HU_THIS : DJ 0x10000 0x99000 THIS 96.
  Hypothesis HU_IDX : DJ 0x10000 0x99000 IDX (4 * N + 12).
  Hypothesis HU_TB : DJ 0x10000 0x99000 TBASE (8 * CAPT).
  Hypothesis D2 : DJ THIS 96 IDX (4 * N + 12).
  Hypothesis D3 : DJ THIS 96 TBASE (8 * CAPT).
  Hypothesis D12 : DJ IDX (4 * N + 12) TBASE (8 * CAPT).
  Hypothesis M_O8 : rw_cells psegs m (THIS + 8) [C4 (Z_to_bv 64 N)].
  Hypothesis M_O16 : rw_cells psegs m (THIS + 16) [C8 (Z_to_bv 64 IDX)].
  Hypothesis M_O88 : bytes_at psegs m (THIS + 88) (word_to_le_bytes 8 (Z_to_bv 64 DOC)).
  Hypothesis M_DOC : rw_cells psegs m DOC [C8 (Z_to_bv 64 TBASE); C8 (Z_to_bv 64 SBASE)].
  Hypothesis M_W24 : wr_at psegs m (THIS + 24) 4.
  Hypothesis M_WTB : wr_at psegs m TBASE (8 * CAPT).
  Hypothesis M_F312 : bytes_at psegs m (zsp - 312) (word_to_le_bytes 8 (Z_to_bv 64 (TBASE + TW))).
  Hypothesis M_F320 : bytes_at psegs m (zsp - 320) (word_to_le_bytes 8 (Z_to_bv 64 (IDX + 4))).
  Hypothesis M_SAVED : forall k, 0 <= k < 13 ->
    bytes_at psegs m (zsp - 8 - 8 * k) (word_to_le_bytes 8 (Z_to_bv 64 (nth (Z.to_nat k) [zra; zs0; zs1; zs2; zs3; zs4; zs5; zs6; zs7; zs8; zs9; zs10; zs11] 0))).
  Hypothesis M_STK : stk psegs m lo zsp.
  Hypothesis M_LO : lo <= zsp - 2928.
  Hypothesis M_INV : mem_inv psegs m.

  Ltac dsolve ZL :=
    pose proof (stk_wr_at m lo zsp (zsp - 368) 368 M_STK ltac:(lia) ltac:(lia) ltac:(lia)) as W_FR;
    cbv [P2D_defs.vTHIS P2D_defs.vDOC P2D_defs.vIDX P2D_defs.vN P2D_defs.vTBASE P2D_defs.vCAPT P2D_defs.vSP
         P2D_defs.vRA P2D_defs.vS0 P2D_defs.vS1 P2D_defs.vS2 P2D_defs.vS3 P2D_defs.vS4 P2D_defs.vS5 P2D_defs.vS6 P2D_defs.vS7
         P2D_defs.vS8 P2D_defs.vS9 P2D_defs.vS10 P2D_defs.vS11 P2D_defs.V P2D_defs.add P2D_defs.sub P2D_defs.mul];
    repeat (apply Forall_cons; [
      lazymatch goal with
      | |- kentry_ok _ _ _ (KRange _ _ _) => apply kz_range; [reflexivity | cbn [zden nth ZL app]; zsolve]
      | |- kentry_ok _ _ _ (KAlign _ _) => apply kz_align; [reflexivity | (clear_quant; lia) | cbn [zden nth ZL app]; zsolve]
      | |- kentry_ok _ _ _ (KDisj (SA _ _) _ (SA _ _) _) => apply kz_disj; [reflexivity | cbn [zden nth ZL app]; djsolve]
      | |- kentry_ok _ _ _ (KWord (SA (EVar 17) _) _ _) =>
          solve [ unshelve eapply (kz_word_cells psegs ZL m _ _ _ _ _ _ 0%nat _ _ M_DOC); first [ reflexivity | (clear_quant; lia) | (cbn [zden nth ZL app]; zsolve) ] ]
      | |- kentry_ok _ _ _ (KWord (SA (EVar 1) (-312)) _ _) =>
          solve [ apply kz_word; [reflexivity | (clear_quant; lia) | cbn [zden nth ZL app]; zsolve | cbn [zden nth ZL app]; rewrite !(Z.mod_small _ M64) by (clear_quant; lia); exact M_F312 ] ]
      | |- kentry_ok _ _ _ (KWord (SA (EVar 1) (-320)) _ _) =>
          solve [ apply kz_word; [reflexivity | (clear_quant; lia) | cbn [zden nth ZL app]; zsolve | cbn [zden nth ZL app]; rewrite !(Z.mod_small _ M64) by (clear_quant; lia); exact M_F320 ] ]
      | |- kentry_ok _ _ _ (KWord (SA (EVar 1) ?o) _ _) =>
          let k := eval vm_compute in ((- o - 8) / 8) in
          solve [ apply kz_word; [reflexivity | (clear_quant; lia) | cbn [zden nth ZL app]; zsolve |
                  cbn [zden nth ZL app]; rewrite !(Z.mod_small _ M64) by (clear_quant; lia);
                  replace (zsp + _) with (zsp - 8 - 8 * k) by lia; exact (M_SAVED k ltac:(lia)) ] ]
      | |- kentry_ok _ _ _ (KWord (SA (EVar 16) 88) _ _) =>
          solve [ apply kz_word; [reflexivity | (clear_quant; lia) | cbn [zden nth ZL app]; zsolve | cbn [zden nth ZL app]; rewrite !(Z.mod_small _ M64) by (clear_quant; lia); exact M_O88 ] ]
      | |- kentry_ok _ _ _ (KWord _ _ _) =>
          first [ solve [ unshelve eapply (kz_word_cells psegs ZL m _ _ _ _ _ _ 0%nat _ _ M_O8); first [ reflexivity | (clear_quant; lia) | (cbn [zden nth ZL app]; zsolve) ] ]
                | solve [ unshelve eapply (kz_word_cells psegs ZL m _ _ _ _ _ _ 0%nat _ _ M_O16); first [ reflexivity | (clear_quant; lia) | (cbn [zden nth ZL app]; zsolve) ] ] ]
      | |- kentry_ok _ _ _ (KWr _ _) =>
          first [ solve [ unshelve eapply (kz_wr_sub psegs ZL m _ _ _ _ _ _ W_FR); first [ reflexivity | (cbn [zden nth ZL app]; zsolve) ] ]
                | solve [ unshelve eapply (kz_wr_sub psegs ZL m _ _ _ _ _ _ M_W24); first [ reflexivity | (cbn [zden nth ZL app]; zsolve) ] ]
                | solve [ unshelve eapply (kz_wr_sub psegs ZL m _ _ _ _ _ _ M_WTB); first [ reflexivity | (cbn [zden nth ZL app]; zsolve) ] ] ]
      | |- kentry_ok _ _ _ (KImg _ _) =>
          apply kz_img; [lia | lia | exact M_INV | intros a Ha; rewrite p_ro_addr; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; clear - Ha; lia]
      end |]); apply Forall_nil.

  Lemma d1_kn : know_ok psegs (mkEZ ZLD1) m P2D_defs.D1_kn.
  Proof. unfold P2D_defs.D1_kn. dsolve ZLD1. Qed.
  Lemma d2_kn : know_ok psegs (mkEZ ZLD2) m P2D_defs.D2_kn.
  Proof. unfold P2D_defs.D2_kn. dsolve ZLD2. Qed.
  Lemma d3_kn : know_ok psegs (mkEZ ZLD2) m P2D_defs.D3_kn.
  Proof. unfold P2D_defs.D3_kn. dsolve ZLD2. Qed.
End T0DB.
