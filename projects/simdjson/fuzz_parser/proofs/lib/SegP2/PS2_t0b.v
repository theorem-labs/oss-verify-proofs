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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry PS2_t0 P2_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.
Local Notation M64 := 18446744073709551616.

Section T0B2.
  Variables (zra zsp zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 : Z)
            (THIS DOC BUF LEN IDX N TBASE CAPT SBASE CAPS OCB IAB : Z)
            (zt0 zt1 zt2 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 : Z).
  Local Notation ZL0' := (ZL0 zra zsp zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 THIS DOC BUF LEN IDX N TBASE CAPT SBASE CAPS OCB IAB zt0 zt1 zt2 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6).
  Variable m : word -> option byte.
  Variables (lo : Z) (jbuf jidx jtp jsb joc jia : list byte) (x24 x88 : word).
  (* [comment removed for export] *)
  Hypothesis H_LEN : 1 <= LEN <= 1048512.
  Hypothesis H_N : 1 <= N <= LEN.
  Hypothesis H_CAPT : N + 3 <= CAPT <= 16777216.
  Hypothesis H_CAPS : LEN + 60 <= CAPS <= 16777216.
  Hypothesis H_CAPS3 : 5 * LEN + 182 <= 3 * CAPS.
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
  (* [comment removed for export] *)
  Hypothesis HU_THIS : DJ 0x10000 0x99000 THIS 96.
  Hypothesis HU_BUF : DJ 0x10000 0x99000 BUF (LEN + 64).
  Hypothesis HU_IDX : DJ 0x10000 0x99000 IDX (4 * N + 12).
  Hypothesis HU_TB : DJ 0x10000 0x99000 TBASE (8 * CAPT).
  Hypothesis HU_SB : DJ 0x10000 0x99000 SBASE CAPS.
  Hypothesis HU_OC : DJ 0x10000 0x99000 OCB 8192.
  Hypothesis HU_IA : DJ 0x10000 0x99000 IAB 1024.
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
  (* [comment removed for export] *)
  Hypothesis M_O8 : rw_cells psegs m (THIS + 8) [C4 (Z_to_bv 64 N)].
  Hypothesis M_O16 : rw_cells psegs m (THIS + 16) [C8 (Z_to_bv 64 IDX)].
  Hypothesis M_O24 : rw_cells psegs m (THIS + 24) [C4 x24].
  Hypothesis M_O40 : rw_cells psegs m (THIS + 40) [C8 (Z_to_bv 64 1024); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Hypothesis M_O56 : rw_cells psegs m (THIS + 56) [C8 (Z_to_bv 64 OCB); C8 (Z_to_bv 64 IAB); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 LEN); C8 x88].
  Hypothesis M_DOC : rw_cells psegs m DOC [C8 (Z_to_bv 64 TBASE); C8 (Z_to_bv 64 SBASE)].
  Hypothesis M_TB : rw_cells psegs m TBASE [CB (Z.to_nat (8 * CAPT)) jtp].
  Hypothesis M_SB : rw_cells psegs m SBASE [CB (Z.to_nat CAPS) jsb].
  Hypothesis M_OC : rw_cells psegs m OCB [CB 8192 joc].
  Hypothesis M_IA : rw_cells psegs m IAB [CB 1024 jia].
  Hypothesis M_IDX : rw_cells psegs m IDX [CB (Z.to_nat (4 * N + 12)) jidx].
  Hypothesis M_BUF : bytes_at psegs m BUF jbuf.
  Hypothesis M_BUFl : Z.of_nat (length jbuf) = LEN + 64.
  Hypothesis M_BUFz : forall i, 0 <= i < 64 -> nth_error jbuf (Z.to_nat (LEN + i)) = Some (Z_to_bv 8 0).
  Hypothesis M_FMIN : rw_cells psegs m 0x76ed0 [C4 (Z_to_bv 64 8388608)].
  Hypothesis M_GOT : rw_cells psegs m 0x75dc0 [C8 (Z_to_bv 64 0x1bbd0)].
  Hypothesis M_STK : stk psegs m lo zsp.
  Hypothesis M_LO : lo <= zsp - 2928.
  Hypothesis M_INV : mem_inv psegs m.

  Ltac kwc H k := solve [ unshelve eapply (kz_word_cells psegs ZL0' m _ _ _ _ _ _ k _ _ H); first [ reflexivity | (clear_quant; lia) | (cbn [zden nth ZL0]; zsolve) ] ].
  Ltac kwr W := solve [ unshelve eapply (kz_wr_sub psegs ZL0' m _ _ _ _ _ _ W); first [ reflexivity | (cbn [zden nth ZL0]; zsolve) ] ].
  Ltac kunk B R := solve [ unshelve eapply (kz_unk_bytes psegs ZL0' m _ _ _ _ _ _ B R); first [ reflexivity | (cbn [zden nth ZL0]; zsolve) ] ].

  Lemma t0_kn_b : know_ok psegs (mkEZ ZL0') m (skipn 52 T0_kn).
  Proof.
    pose proof (stk_wr_at m lo zsp (zsp - 368) 368 M_STK ltac:(lia) ltac:(lia) ltac:(lia)) as W_FR.
    pose proof (stk_wr_at m lo zsp (zsp - 2928) 2560 M_STK ltac:(lia) ltac:(lia) ltac:(lia)) as W_FX.
    destruct (stk_split psegs m lo (zsp - 2928) zsp M_STK ltac:(lia)) as [_ STK_FX].
    pose proof (rw_cells_wr_at _ _ _ _ 4 M_O24 ltac:(cbn; lia)) as W_O24.
    pose proof (rw_cells_wr_at _ _ _ _ 40 M_O56 ltac:(cbn; lia)) as W_O56.
    destruct (cb_bytes m _ _ _ M_TB) as [B_TB L_TB]. destruct (cb_bytes m _ _ _ M_SB) as [B_SB L_SB].
    destruct (cb_bytes m _ _ _ M_OC) as [B_OC L_OC]. destruct (cb_bytes m _ _ _ M_IA) as [B_IA L_IA].
    destruct (cb_bytes m _ _ _ M_IDX) as [B_IDX L_IDX].
    change (Z.of_nat 8192) with 8192 in L_OC. change (Z.of_nat 1024) with 1024 in L_IA. rewrite Z2Nat.id in L_IDX by lia.
    rewrite Z2Nat.id in L_TB by lia. rewrite Z2Nat.id in L_SB by lia.
    pose proof (rw_cells_wr_at _ _ _ _ (8 * CAPT) M_TB ltac:(cbn; lia)) as W_TB.
    pose proof (rw_cells_wr_at _ _ _ _ CAPS M_SB ltac:(cbn; lia)) as W_SB.
    pose proof (rw_cells_wr_at _ _ _ _ 8192 M_OC ltac:(cbn; lia)) as W_OC.
    pose proof (rw_cells_wr_at _ _ _ _ 1024 M_IA ltac:(cbn; lia)) as W_IA.
    pose proof (seg_rom_heap BUF (LEN + 64) HU_BUF ltac:(lia) ltac:(lia)) as R_BUF.
    pose proof (seg_rom_heap IDX (4 * N + 12) HU_IDX ltac:(lia) ltac:(lia)) as R_IDX.
    pose proof (seg_rom_heap OCB 8192 HU_OC ltac:(lia) ltac:(lia)) as R_OC.
    pose proof (seg_rom_heap IAB 1024 HU_IA ltac:(lia) ltac:(lia)) as R_IA.
    assert (R_BUF' : forall i, 0 <= i < Z.of_nat (length jbuf) -> seg_rom psegs (Z_to_bv 64 (BUF + i)) = None)
      by (rewrite M_BUFl; exact R_BUF).
    assert (R_IDX' : forall i, 0 <= i < Z.of_nat (length jidx) -> seg_rom psegs (Z_to_bv 64 (IDX + i)) = None)
      by (rewrite L_IDX; exact R_IDX).
    assert (R_OC' : forall i, 0 <= i < Z.of_nat (length joc) -> seg_rom psegs (Z_to_bv 64 (OCB + i)) = None)
      by (rewrite L_OC; exact R_OC).
    assert (R_IA' : forall i, 0 <= i < Z.of_nat (length jia) -> seg_rom psegs (Z_to_bv 64 (IAB + i)) = None)
      by (rewrite L_IA; exact R_IA).
    unfold T0_kn; cbn [skipn]. cbv [vTHIS vDOC vBUF vLEN vIDX vN vTBASE vCAPT vSBASE vCAPS vOCB vIAB vSP V add sub mul].
    repeat (apply Forall_cons; [
      lazymatch goal with
      | |- kentry_ok _ _ _ (KRange _ _ _) => apply kz_range; [reflexivity | cbn [zden nth ZL0]; zsolve]
      | |- kentry_ok _ _ _ (KAlign _ _) => apply kz_align; [reflexivity | (clear_quant; lia) | cbn [zden nth ZL0]; zsolve]
      | |- kentry_ok _ _ _ (KDisj (SA _ _) _ (SA _ _) _) => apply kz_disj; [reflexivity | cbn [zden nth ZL0]; djsolve]
      | |- kentry_ok _ _ _ (KWord (SA (ELit 0) _) _ _) => first [ kwc M_FMIN 0%nat | kwc M_GOT 0%nat ]
      | |- kentry_ok _ _ _ (KWord (SA (EVar 17) _) _ _) => first [ kwc M_DOC 0%nat | kwc M_DOC 8%nat ]
      | |- kentry_ok _ _ _ (KWord _ _ _) =>
          first [ kwc M_O8 0%nat | kwc M_O16 0%nat | kwc M_O40 0%nat | kwc M_O40 8%nat | kwc M_O40 9%nat
                | kwc M_O56 0%nat | kwc M_O56 8%nat | kwc M_O56 16%nat | kwc M_O56 24%nat ]
      | |- kentry_ok _ _ _ (KWr _ _) => first [ kwr W_FR | kwr W_FX | kwr W_O24 | kwr W_O56 | kwr W_TB | kwr W_SB | kwr W_OC | kwr W_IA ]
      | |- kentry_ok _ _ _ (KUnk (SA (EVar 1) _) _) =>
          apply (stk_unk ZL0' m (zsp - 2928) zsp); [exact STK_FX | reflexivity | lia | lia | cbn [zden nth ZL0 app]; zsolve | cbn [zden nth ZL0 app]; zsolve]
      | |- kentry_ok _ _ _ (KUnk _ _) =>
          first [ kunk M_BUF R_BUF' | kunk B_IDX R_IDX' | kunk B_OC R_OC' | kunk B_IA R_IA' ]
      | |- kentry_ok _ _ _ (KZero _ _) =>
          unshelve eapply (kz_zero_bytes psegs ZL0' m _ _ _ _ _ _ M_BUF R_BUF');
            [reflexivity | cbn [zden nth ZL0]; zsolve | cbn [zden nth ZL0]; zsolve | cbn [zden nth ZL0]; zsolve |];
          cbn [zden nth ZL0]; rewrite !(Z.mod_small _ M64) by lia; intros i Hi;
          replace (BUF + LEN + 0 - BUF + i) with (LEN + i) by lia; apply M_BUFz; lia
      | |- kentry_ok _ _ _ (KImg _ _) =>
          apply kz_img; [lia | lia | exact M_INV | intros a Ha; rewrite p_ro_addr; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; clear - Ha; lia]
      end |]).
    apply Forall_nil.
  Qed.
  Lemma t0_kn : know_ok psegs (mkEZ ZL0') m T0_kn.
  Proof.
    rewrite <- (firstn_skipn 52 T0_kn). apply Forall_app. split; [eapply PS2_t0.t0_kn_a; eassumption | exact t0_kn_b].
  Qed.
End T0B2.
