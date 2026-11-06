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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry PS2_t0n P2N_defs PS2_t0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.
Local Notation M64 := 18446744073709551616.
Notation ATOPM := 140737479966720%Z (only parsing).

Section T0NB2.
  Variables (zra zsp zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 : Z)
            (THIS DOC BUF LEN IDX N TBASE CAPT SBASE CAPS OCB IAB V COPY : Z) (rest : list Z).
  (* [comment removed for export] *)
  Local Notation ZLN' := (ZLN zra zsp zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 THIS DOC BUF LEN IDX N TBASE CAPT SBASE CAPS OCB IAB V COPY rest).
  Variable m : word -> option byte.
  Variables (lo : Z) (jbuf jcp : list byte).
  Local Notation CL := (LEN - V).
  (* [comment removed for export] *)
  Hypothesis H_LEN : 1 <= LEN <= 1048512.
  Hypothesis H_N : 1 <= N <= LEN.
  Hypothesis H_CAPT : N + 3 <= CAPT <= 16777216.
  Hypothesis H_CAPS : LEN + 60 <= CAPS <= 16777216.
  Hypothesis H_CAPS3 : 5 * LEN + 182 <= 3 * CAPS.
  Hypothesis H_V : 0 <= V /\ V + 1 <= LEN.
  (* [comment removed for export] *)
  Hypothesis H_SP : 0x7fff00000000 <= zsp <= 2 ^ 47.
  Hypothesis H_SPa : zsp mod 16 = 0.
  Hypothesis H_DOC : zsp <= DOC /\ DOC + 16 <= 2 ^ 64 - 16 /\ DOC mod 8 = 0.
  (* [comment removed for export] *)
  Hypothesis H_THIS : 16 <= THIS /\ THIS mod 16 = 0 /\ THIS + 96 <= ATOPM /\ THIS + 96 + 2928 <= zsp.
  Hypothesis H_BUF : 16 <= BUF /\ BUF + LEN + 64 <= ATOPM /\ BUF + LEN + 64 + 2928 <= zsp.
  Hypothesis H_IDX : 16 <= IDX /\ IDX mod 16 = 0 /\ IDX + 4 * N + 12 <= ATOPM /\ IDX + 4 * N + 12 + 2928 <= zsp.
  Hypothesis H_TB : 16 <= TBASE /\ TBASE mod 16 = 0 /\ TBASE + 8 * CAPT <= ATOPM /\ TBASE + 8 * CAPT + 2928 <= zsp.
  Hypothesis H_SB : 16 <= SBASE /\ SBASE mod 16 = 0 /\ SBASE + CAPS <= ATOPM /\ SBASE + CAPS + 2928 <= zsp.
  Hypothesis H_OC : 16 <= OCB /\ OCB mod 16 = 0 /\ OCB + 8192 <= ATOPM /\ OCB + 8192 + 2928 <= zsp.
  Hypothesis H_IA : 16 <= IAB /\ IAB mod 16 = 0 /\ IAB + 1024 <= ATOPM /\ IAB + 1024 + 2928 <= zsp.
  Hypothesis H_CP : 16 <= COPY /\ COPY mod 16 = 0 /\ COPY + (CL + 64) <= ATOPM /\ COPY + (CL + 64) + 2928 <= zsp.
  Hypothesis HU_THIS : DJ 0x10000 0x99000 THIS 96.
  Hypothesis HU_BUF : DJ 0x10000 0x99000 BUF (LEN + 64).
  Hypothesis HU_IDX : DJ 0x10000 0x99000 IDX (4 * N + 12).
  Hypothesis HU_TB : DJ 0x10000 0x99000 TBASE (8 * CAPT).
  Hypothesis HU_SB : DJ 0x10000 0x99000 SBASE CAPS.
  Hypothesis HU_OC : DJ 0x10000 0x99000 OCB 8192.
  Hypothesis HU_IA : DJ 0x10000 0x99000 IAB 1024.
  Hypothesis HU_CP : DJ 0x10000 0x99000 COPY (CL + 64).
  Hypothesis D1 : DJ THIS 96 BUF (LEN + 64).
  Hypothesis D2 : DJ THIS 96 IDX (4 * N + 12).
  Hypothesis D3 : DJ THIS 96 TBASE (8 * CAPT).
  Hypothesis D4 : DJ THIS 96 SBASE CAPS.
  Hypothesis D5 : DJ THIS 96 OCB 8192.
  Hypothesis D6 : DJ THIS 96 IAB 1024.
  Hypothesis D7 : DJ BUF (LEN + 64) IDX (4 * N + 12).
  Hypothesis D8 : DJ BUF (LEN + 64) TBASE (8 * CAPT).
  Hypothesis D9 : DJ BUF (LEN + 64) SBASE CAPS.
  Hypothesis D10 : DJ BUF (LEN + 64) OCB 8192.
  Hypothesis D11 : DJ BUF (LEN + 64) IAB 1024.
  Hypothesis D12 : DJ IDX (4 * N + 12) TBASE (8 * CAPT).
  Hypothesis D13 : DJ IDX (4 * N + 12) SBASE CAPS.
  Hypothesis D14 : DJ IDX (4 * N + 12) OCB 8192.
  Hypothesis D15 : DJ IDX (4 * N + 12) IAB 1024.
  Hypothesis D16 : DJ TBASE (8 * CAPT) SBASE CAPS.
  Hypothesis D17 : DJ TBASE (8 * CAPT) OCB 8192.
  Hypothesis D18 : DJ TBASE (8 * CAPT) IAB 1024.
  Hypothesis D19 : DJ SBASE CAPS OCB 8192.
  Hypothesis D20 : DJ SBASE CAPS IAB 1024.
  Hypothesis D21 : DJ OCB 8192 IAB 1024.
  Hypothesis D22 : DJ THIS 96 COPY (CL + 64).
  Hypothesis D23 : DJ BUF (LEN + 64) COPY (CL + 64).
  Hypothesis D24 : DJ IDX (4 * N + 12) COPY (CL + 64).
  Hypothesis D25 : DJ TBASE (8 * CAPT) COPY (CL + 64).
  Hypothesis D26 : DJ SBASE CAPS COPY (CL + 64).
  Hypothesis D27 : DJ OCB 8192 COPY (CL + 64).
  Hypothesis D28 : DJ IAB 1024 COPY (CL + 64).
  (* [comment removed for export] *)
  Hypothesis M_O8 : rw_cells psegs m (THIS + 8) [C4 (Z_to_bv 64 N)].
  Hypothesis M_O16 : rw_cells psegs m (THIS + 16) [C8 (Z_to_bv 64 IDX)].
  Hypothesis M_O40 : rw_cells psegs m (THIS + 40) [C8 (Z_to_bv 64 1024); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Hypothesis M_O56 : rw_cells psegs m (THIS + 56) [C8 (Z_to_bv 64 OCB); C8 (Z_to_bv 64 IAB); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 LEN)].
  Hypothesis M_O88 : bytes_at psegs m (THIS + 88) (word_to_le_bytes 8 (Z_to_bv 64 DOC)).
  Hypothesis M_DOC : rw_cells psegs m DOC [C8 (Z_to_bv 64 TBASE); C8 (Z_to_bv 64 SBASE)].
  Hypothesis M_TB : wr_at psegs m TBASE (8 * CAPT).
  Hypothesis M_CP : rw_cells psegs m COPY [CB (Z.to_nat (CL + 64)) jcp].
  Hypothesis M_BUF : bytes_at psegs m BUF jbuf.
  Hypothesis M_BUFl : Z.of_nat (length jbuf) = LEN + 64.
  Hypothesis M_BUFz : forall i, 0 <= i < 64 -> nth_error jbuf (Z.to_nat (LEN + i)) = Some (Z_to_bv 8 0).
  Hypothesis M_FMIN : rw_cells psegs m 0x76ed0 [C4 (Z_to_bv 64 8388608)].
  Hypothesis M_GOT : rw_cells psegs m 0x75dc0 [C8 (Z_to_bv 64 0x1bbd0)].
  (* [comment removed for export] *)
  Hypothesis M_F312 : bytes_at psegs m (zsp - 312) (word_to_le_bytes 8 (Z_to_bv 64 (TBASE + 8))).
  Hypothesis M_F304 : bytes_at psegs m (zsp - 304) (word_to_le_bytes 8 (Z_to_bv 64 SBASE)).
  Hypothesis M_F320 : bytes_at psegs m (zsp - 320) (word_to_le_bytes 8 (Z_to_bv 64 (IDX + 4))).
  Hypothesis M_SAVED : forall k, 0 <= k < 13 ->
    bytes_at psegs m (zsp - 8 - 8 * k) (word_to_le_bytes 8 (Z_to_bv 64 (nth (Z.to_nat k) [zra; zs0; zs1; zs2; zs3; zs4; zs5; zs6; zs7; zs8; zs9; zs10; zs11] 0))).
  Hypothesis M_STK : stk psegs m lo zsp.
  Hypothesis M_LO : lo <= zsp - 2928.
  Hypothesis M_INV : mem_inv psegs m.

  Ltac kwc H k := solve [ unshelve eapply (kz_word_cells psegs ZLN' m _ _ _ _ _ _ k _ _ H); first [ reflexivity | (clear_quant; lia) | (cbn [zden nth ZLN app]; zsolve) ] ].
  Ltac kwb H := solve [ apply kz_word; [reflexivity | (clear_quant; lia) | cbn [zden nth ZLN app]; zsolve |
                         cbn [zden nth ZLN app]; rewrite !(Z.mod_small _ M64) by (clear_quant; lia); exact H ] ].
  Ltac kwsaved k := solve [ apply kz_word; [reflexivity | (clear_quant; lia) | cbn [zden nth ZLN app]; zsolve |
                         cbn [zden nth ZLN app]; rewrite !(Z.mod_small _ M64) by (clear_quant; lia);
                         replace (zsp + _) with (zsp - 8 - 8 * k) by lia; exact (M_SAVED k ltac:(lia)) ] ].
  Ltac kwr W := solve [ unshelve eapply (kz_wr_sub psegs ZLN' m _ _ _ _ _ _ W); first [ reflexivity | (cbn [zden nth ZLN app]; zsolve) ] ].
  Ltac kunk B R := solve [ unshelve eapply (kz_unk_bytes psegs ZLN' m _ _ _ _ _ _ B R); first [ reflexivity | (cbn [zden nth ZLN app]; zsolve) ] ].

  Lemma t0n_kn_b : know_ok psegs (mkEZ ZLN') m (skipn 64 P2N_defs.T0_kn).
  Proof.
    pose proof (stk_wr_at m lo zsp (zsp - 368) 368 M_STK ltac:(lia) ltac:(lia) ltac:(lia)) as W_FR.
    pose proof (stk_wr_at m lo zsp (zsp - 2928) 2560 M_STK ltac:(lia) ltac:(lia) ltac:(lia)) as W_FX.
    destruct (stk_split psegs m lo (zsp - 2928) zsp M_STK ltac:(lia)) as [_ STK_FX].
    destruct (cb_bytes m _ _ _ M_CP) as [B_CP L_CP].
    rewrite Z2Nat.id in L_CP by lia.
    pose proof M_TB as W_TB.
    pose proof (rw_cells_wr_at _ _ _ _ (CL + 64) M_CP ltac:(cbn; lia)) as W_CP.
    pose proof (seg_rom_heap BUF (LEN + 64) HU_BUF ltac:(lia) ltac:(lia)) as R_BUF.
    pose proof (seg_rom_heap COPY (CL + 64) HU_CP ltac:(lia) ltac:(lia)) as R_CP.
    assert (R_BUF' : forall i, 0 <= i < Z.of_nat (length jbuf) -> seg_rom psegs (Z_to_bv 64 (BUF + i)) = None)
      by (rewrite M_BUFl; exact R_BUF).
    assert (R_CP' : forall i, 0 <= i < Z.of_nat (length jcp) -> seg_rom psegs (Z_to_bv 64 (COPY + i)) = None)
      by (rewrite L_CP; exact R_CP).
    unfold P2N_defs.T0_kn; cbn [skipn]. cbv [P2N_defs.vTHIS P2N_defs.vDOC P2N_defs.vBUF P2N_defs.vLEN P2N_defs.vIDX P2N_defs.vN P2N_defs.vTBASE
      P2N_defs.vCAPT P2N_defs.vSBASE P2N_defs.vCAPS P2N_defs.vOCB P2N_defs.vIAB P2N_defs.vSP P2N_defs.vV P2N_defs.vCOPY
      P2N_defs.vRA P2N_defs.vS0 P2N_defs.vS1 P2N_defs.vS2 P2N_defs.vS3 P2N_defs.vS4 P2N_defs.vS5 P2N_defs.vS6 P2N_defs.vS7
      P2N_defs.vS8 P2N_defs.vS9 P2N_defs.vS10 P2N_defs.vS11 P2N_defs.V P2N_defs.add P2N_defs.sub P2N_defs.mul].
    repeat (apply Forall_cons; [
      lazymatch goal with
      | |- kentry_ok _ _ _ (KRange _ _ _) => apply kz_range; [reflexivity | cbn [zden nth ZLN app]; zsolve]
      | |- kentry_ok _ _ _ (KAlign _ _) => apply kz_align; [reflexivity | (clear_quant; lia) | cbn [zden nth ZLN app]; zsolve]
      | |- kentry_ok _ _ _ (KDisj (SA _ _) _ (SA _ _) _) => apply kz_disj; [reflexivity | cbn [zden nth ZLN app]; djsolve]
      | |- kentry_ok _ _ _ (KWord (SA (ELit 0) _) _ _) => first [ kwc M_FMIN 0%nat | kwc M_GOT 0%nat ]
      | |- kentry_ok _ _ _ (KWord (SA (EVar 17) _) _ _) => first [ kwc M_DOC 0%nat | kwc M_DOC 8%nat ]
      | |- kentry_ok _ _ _ (KWord (SA (EVar 1) (-312)) _ _) => kwb M_F312
      | |- kentry_ok _ _ _ (KWord (SA (EVar 1) (-304)) _ _) => kwb M_F304
      | |- kentry_ok _ _ _ (KWord (SA (EVar 1) (-320)) _ _) => kwb M_F320
      | |- kentry_ok _ _ _ (KWord (SA (EVar 1) ?o) _ _) => let k := eval vm_compute in ((- o - 8) / 8) in kwsaved k
      | |- kentry_ok _ _ _ (KWord (SA (EVar 16) 88) _ _) => kwb M_O88
      | |- kentry_ok _ _ _ (KWord _ _ _) =>
          first [ kwc M_O8 0%nat | kwc M_O16 0%nat | kwc M_O40 0%nat | kwc M_O40 8%nat | kwc M_O40 9%nat
                | kwc M_O56 0%nat | kwc M_O56 8%nat | kwc M_O56 16%nat | kwc M_O56 24%nat ]
      | |- kentry_ok _ _ _ (KWr _ _) => first [ kwr W_FR | kwr W_FX | kwr W_TB | kwr W_CP ]
      | |- kentry_ok _ _ _ (KUnk (SA (EVar 1) _) _) =>
          apply (stk_unk ZLN' m (zsp - 2928) zsp); [exact STK_FX | reflexivity | lia | lia | cbn [zden nth ZLN app]; zsolve | cbn [zden nth ZLN app]; zsolve]
      | |- kentry_ok _ _ _ (KUnk _ _) => first [ kunk M_BUF R_BUF' | kunk B_CP R_CP' ]
      | |- kentry_ok _ _ _ (KZero _ _) =>
          unshelve eapply (kz_zero_bytes psegs ZLN' m _ _ _ _ _ _ M_BUF R_BUF');
            [reflexivity | cbn [zden nth ZLN app]; zsolve | cbn [zden nth ZLN app]; zsolve | cbn [zden nth ZLN app]; zsolve |];
          cbn [zden nth ZLN app]; rewrite !(Z.mod_small _ M64) by lia; intros i Hi;
          replace (BUF + LEN + 0 - BUF + i) with (LEN + i) by lia; apply M_BUFz; lia
      | |- kentry_ok _ _ _ (KImg _ _) =>
          apply kz_img; [lia | lia | exact M_INV | intros a Ha; rewrite p_ro_addr; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; clear - Ha; lia]
      end |]).
    apply Forall_nil.
  Qed.
  Lemma t0n_kn : know_ok psegs (mkEZ ZLN') m P2N_defs.T0_kn.
  Proof.
    rewrite <- (firstn_skipn 64 P2N_defs.T0_kn). apply Forall_app. split; [eapply PS2_t0n.t0n_kn_a; eassumption | exact t0n_kn_b].
  Qed.
End T0NB2.
