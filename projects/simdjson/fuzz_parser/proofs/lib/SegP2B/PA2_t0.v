(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec Mem Cells Step Frame SysStep.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg ABase.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2B Require Import PA2_kz.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegB2 Require B2_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Local Notation M64 := 18446744073709551616.
Local Notation SH := 2147450880%Z (only parsing).

Section S_T0.
  Context {rc : runConstT}.
  Variables (zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 : Z)
            (T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG : Z) (rest : list Z).
  Definition ZL_t0 : list Z :=
    [zra; SP16; zgp; ztp; zs0; zs1; zs2; zs3; zs4; zs5; zs6; zs7; zs8; zs9; zs10; zs11;
     T8; DOC8; B8; LEN; I8; N; TB8; CAPT; SB8; CAPS; OC8; IA8; F11; PB; FLAG; BO; BG; IG; SG] ++ rest.
  Variables (zsp THIS DOC BUF IDX TBASE SBASE OCB IAB F : Z).
  Hypothesis E_SP : zsp = 16 * SP16.
  Hypothesis E_T8 : THIS = 8 * T8.
  Hypothesis E_DOC8 : DOC = 8 * DOC8.
  Hypothesis E_B8 : BUF = 8 * B8 + BO.
  Hypothesis E_I8 : IDX = 8 * I8.
  Hypothesis E_TB8 : TBASE = 8 * TB8.
  Hypothesis E_SB8 : SBASE = 8 * SB8.
  Hypothesis E_OC8 : OCB = 8 * OC8.
  Hypothesis E_IA8 : IAB = 8 * IA8.
  Hypothesis E_F11 : F = 2048 * F11.
  Variable m : word -> option byte.
  Variables (lo : Z) (jbuf : list byte) (x24 x88 : word) (j0 j1 j2 : word) (jfr : list byte).
  Hypothesis H_LEN : 1 <= LEN <= 1048512.
  Hypothesis H_N : 1 <= N <= LEN.
  Hypothesis H_CAPT : N + 3 <= CAPT <= 16777216.
  Hypothesis H_CAPS : LEN + 60 <= CAPS <= 16777216.
  Hypothesis H_CAPS3 : 5 * LEN + 182 <= 3 * CAPS.
  Hypothesis H_SP : 0x7fff00000000 <= zsp <= 2 ^ 47.
  Hypothesis H_TP : ztp = 0x64e9f0.
  Hypothesis H_THIS : 0x671000 <= THIS /\ THIS + 96 <= ATOPM /\ THIS + 96 + 8640 <= zsp.
  Hypothesis H_DOC : 0x671000 <= DOC /\ DOC + 16 <= ATOPM /\ DOC + 16 + 8640 <= zsp.
  Hypothesis H_BUF : 0 <= BO <= 7 /\ 0x671000 <= BUF - BO /\ BUF + LEN + 64 <= ATOPM /\ BUF + LEN + 64 + 8640 <= zsp.
  Hypothesis H_IDX : 0x671000 <= IDX /\ IDX + 4 * N + 12 <= ATOPM /\ IDX + 4 * N + 12 + 8640 <= zsp.
  Hypothesis H_TBASE : 0x671000 <= TBASE /\ TBASE + (8 * CAPT) <= ATOPM /\ TBASE + (8 * CAPT) + 8640 <= zsp.
  Hypothesis H_SBASE : 0x671000 <= SBASE /\ SBASE + CAPS <= ATOPM /\ SBASE + CAPS + 8640 <= zsp.
  Hypothesis H_OCB : 0x671000 <= OCB /\ OCB + 8192 <= ATOPM /\ OCB + 8192 + 8640 <= zsp.
  Hypothesis H_IAB : 0x671000 <= IAB /\ IAB + 1024 <= ATOPM /\ IAB + 1024 + 8640 <= zsp.
  Hypothesis H_F : 0x671000 <= F /\ F + 2048 <= ATOPM /\ F + 2048 + 8640 <= zsp.
  Hypothesis HB_THIS : DJ 0x7fff7000 0x100000001000 THIS 96.
  Hypothesis HB_DOC : DJ 0x7fff7000 0x100000001000 DOC 16.
  Hypothesis HB_BUF : DJ 0x7fff7000 0x100000001000 BUF (LEN + 64).
  Hypothesis HB_IDX : DJ 0x7fff7000 0x100000001000 IDX (4 * N + 12).
  Hypothesis HB_TBASE : DJ 0x7fff7000 0x100000001000 TBASE (8 * CAPT).
  Hypothesis HB_SBASE : DJ 0x7fff7000 0x100000001000 SBASE CAPS.
  Hypothesis HB_OCB : DJ 0x7fff7000 0x100000001000 OCB 8192.
  Hypothesis HB_IAB : DJ 0x7fff7000 0x100000001000 IAB 1024.
  Hypothesis HB_F : DJ 0x7fff7000 0x100000001000 F 2048.
  Hypothesis D1 : DJ THIS 96 DOC 16.
  Hypothesis D2 : DJ THIS 96 BUF (LEN + 64).
  Hypothesis D3 : DJ THIS 96 IDX (4 * N + 12).
  Hypothesis D4 : DJ THIS 96 TBASE (8 * CAPT).
  Hypothesis D5 : DJ THIS 96 SBASE CAPS.
  Hypothesis D6 : DJ THIS 96 OCB 8192.
  Hypothesis D7 : DJ THIS 96 IAB 1024.
  Hypothesis D8 : DJ THIS 96 F 2048.
  Hypothesis D9 : DJ DOC 16 BUF (LEN + 64).
  Hypothesis D10 : DJ DOC 16 IDX (4 * N + 12).
  Hypothesis D11 : DJ DOC 16 TBASE (8 * CAPT).
  Hypothesis D12 : DJ DOC 16 SBASE CAPS.
  Hypothesis D13 : DJ DOC 16 OCB 8192.
  Hypothesis D14 : DJ DOC 16 IAB 1024.
  Hypothesis D15 : DJ DOC 16 F 2048.
  Hypothesis D16 : DJ BUF (LEN + 64) IDX (4 * N + 12).
  Hypothesis D17 : DJ BUF (LEN + 64) TBASE (8 * CAPT).
  Hypothesis D18 : DJ BUF (LEN + 64) SBASE CAPS.
  Hypothesis D19 : DJ BUF (LEN + 64) OCB 8192.
  Hypothesis D20 : DJ BUF (LEN + 64) IAB 1024.
  Hypothesis D21 : DJ BUF (LEN + 64) F 2048.
  Hypothesis D22 : DJ IDX (4 * N + 12) TBASE (8 * CAPT).
  Hypothesis D23 : DJ IDX (4 * N + 12) SBASE CAPS.
  Hypothesis D24 : DJ IDX (4 * N + 12) OCB 8192.
  Hypothesis D25 : DJ IDX (4 * N + 12) IAB 1024.
  Hypothesis D26 : DJ IDX (4 * N + 12) F 2048.
  Hypothesis D27 : DJ TBASE (8 * CAPT) SBASE CAPS.
  Hypothesis D28 : DJ TBASE (8 * CAPT) OCB 8192.
  Hypothesis D29 : DJ TBASE (8 * CAPT) IAB 1024.
  Hypothesis D30 : DJ TBASE (8 * CAPT) F 2048.
  Hypothesis D31 : DJ SBASE CAPS OCB 8192.
  Hypothesis D32 : DJ SBASE CAPS IAB 1024.
  Hypothesis D33 : DJ SBASE CAPS F 2048.
  Hypothesis D34 : DJ OCB 8192 IAB 1024.
  Hypothesis D35 : DJ OCB 8192 F 2048.
  Hypothesis D36 : DJ IAB 1024 F 2048.
  Hypothesis H_BG : 8 <= BG <= 131080 /\ 0 <= LEN + BO + 64 - 8 * BG <= 7.
  Hypothesis H_IG : 2 <= IG <= 0x200000 /\ 0 <= 8 * IG - (4 * N + 12) <= 7.
  Hypothesis H_SG : 7 <= SG <= 2097152 /\ 0 <= CAPS - 8 * SG <= 7.
  Hypothesis H_IGB : IDX + 8 * IG <= ATOPM.
  Hypothesis S_T8 : forall i, 0 <= i < 12 -> m (Z_to_bv 64 (SH + T8 + i)) = Some (Z_to_bv 8 0).
  Hypothesis S_DOC8 : forall i, 0 <= i < 2 -> m (Z_to_bv 64 (SH + DOC8 + i)) = Some (Z_to_bv 8 0).
  Hypothesis S_B8 : forall i, 0 <= i < BG -> m (Z_to_bv 64 (SH + B8 + i)) = Some (Z_to_bv 8 0).
  Hypothesis S_I8 : forall i, 0 <= i < IG -> m (Z_to_bv 64 (SH + I8 + i)) = Some (Z_to_bv 8 0).
  Hypothesis S_TB8 : forall i, 0 <= i < CAPT -> m (Z_to_bv 64 (SH + TB8 + i)) = Some (Z_to_bv 8 0).
  Hypothesis S_SB8 : forall i, 0 <= i < SG -> m (Z_to_bv 64 (SH + SB8 + i)) = Some (Z_to_bv 8 0).
  Hypothesis S_OC8 : forall i, 0 <= i < 1024 -> m (Z_to_bv 64 (SH + OC8 + i)) = Some (Z_to_bv 8 0).
  Hypothesis S_IA8 : forall i, 0 <= i < 128 -> m (Z_to_bv 64 (SH + IA8 + i)) = Some (Z_to_bv 8 0).
  Hypothesis S_F : forall i, 0 <= i < 256 -> m (Z_to_bv 64 (SH + 256 * F11 + i)) = Some (Z_to_bv 8 0).
  Hypothesis M_O8 : rw_cells bsegs m (THIS + 8) [C4 (Z_to_bv 64 N)].
  Hypothesis M_O16 : rw_cells bsegs m (THIS + 16) [C8 (Z_to_bv 64 IDX)].
  Hypothesis M_O24 : rw_cells bsegs m (THIS + 24) [C4 x24].
  Hypothesis M_O40 : rw_cells bsegs m (THIS + 40) [C8 (Z_to_bv 64 1024); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Hypothesis M_O56 : rw_cells bsegs m (THIS + 56) [C8 (Z_to_bv 64 OCB); C8 (Z_to_bv 64 IAB); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 LEN); C8 x88].
  Hypothesis M_DOC : rw_cells bsegs m DOC [C8 (Z_to_bv 64 TBASE); C8 (Z_to_bv 64 SBASE)].
  Hypothesis W_TB : wr_at bsegs m TBASE (8 * CAPT).
  Hypothesis W_SB : wr_at bsegs m SBASE CAPS.
  Hypothesis W_OC : wr_at bsegs m OCB 8192.
  Hypothesis W_IA : wr_at bsegs m IAB 1024.
  Hypothesis W_IDX : wr_at bsegs m IDX (4 * N + 12).
  Hypothesis M_BUF : bytes_at bsegs m BUF jbuf.
  Hypothesis M_BUFl : Z.of_nat (length jbuf) = LEN + 64.
  Hypothesis M_BUFz : forall i, 0 <= i < 64 -> nth_error jbuf (Z.to_nat (LEN + i)) = Some (Z_to_bv 8 0).
  Hypothesis M_GOT : rw_cells bsegs m 0x112a70 [C8 (Z_to_bv 64 0x1ad1a8); C8 (Z_to_bv 64 0x118e78); C8 (Z_to_bv 64 0x11b678);
                                              C8 (Z_to_bv 64 0x11c368); C8 (Z_to_bv 64 0x11c370); C8 (Z_to_bv 64 0x11c360)].
  Hypothesis M_SHB : rw_cells bsegs m 0x11b678 [C8 (Z_to_bv 64 0x7fff8000)].
  Hypothesis M_SUARG : rw_cells bsegs m 0x112ad8 [C8 (Z_to_bv 64 0x11b680)].
  Hypothesis M_SUAR : rw_cells bsegs m 0x11b680 [C4 (Z_to_bv 64 1)].
  Hypothesis M_NT : rw_cells bsegs m 0x113720 [C8 (Z_to_bv 64 0x2c870)].
  Hypothesis M_FMIN : rw_cells bsegs m 0x1174c0 [C4 (Z_to_bv 64 8388608)].
  Hypothesis M_F : rw_cells bsegs m F [C8 j0; C8 j1; C8 j2; CB 2016 jfr; C8 (Z_to_bv 64 FLAG)].
  Hypothesis M_SHF : wr_at bsegs m (SH + 256 * F11) 256.
  Hypothesis M_SAVED : forall k, 0 <= k < 13 ->
    bytes_at bsegs m (zsp - 8 - 8 * k) (word_to_le_bytes 8 (Z_to_bv 64 (nth (Z.to_nat k) [zra; zs0; zs1; zs2; zs3; zs4; zs5; zs6; zs7; zs8; zs9; zs10; zs11] 0))).
  Hypothesis M_Z416 : bytes_at bsegs m (zsp - 416) (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Hypothesis H_SPA : 0 <= PB <= 1 /\ (zsp - 416 - 16 * PB) mod 32 = 0.
  Hypothesis S_IMG : forall a n i, In (a, n) A2_IMGSH -> 0 <= i < n -> m (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).
  Hypothesis M_STK : stk bsegs m lo zsp.
  Hypothesis M_LO : 0x671000 <= lo <= zsp - 8640.
  Hypothesis S_STK : forall i, 0 <= i < 1080 -> m (Z_to_bv 64 (SH + 2 * SP16 - 1080 + i)) = Some (Z_to_bv 8 0).
  Hypothesis W_STKSH : wr_at bsegs m (SH + 2 * SP16 - 1080) 1080.
  Hypothesis M_INV : mem_inv bsegs m.

  Ltac kwc H k := solve [ unshelve eapply (kz_word_cells bsegs ZL_t0 m _ _ _ _ _ _ k _ _ H); first [ reflexivity | (clear_quant; lia) | (cbn [zden nth ZL_t0 app]; zsolve)
                         | (cbn [zden nth ZL_t0 app]; rewrite ?E_SP, ?E_T8, ?E_DOC8, ?E_B8, ?E_I8, ?E_TB8, ?E_SB8, ?E_OC8, ?E_IA8, ?E_F11; reflexivity) ] ].
  Ltac kwr W := solve [ unshelve eapply (kz_wr_sub bsegs ZL_t0 m _ _ _ _ _ _ W); first [ reflexivity | (cbn [zden nth ZL_t0 app]; zsolve) ] ].
  Ltac kunk B R := solve [ unshelve eapply (kz_unk_bytes bsegs ZL_t0 m _ _ _ _ _ _ B R); first [ reflexivity | (cbn [zden nth ZL_t0 app]; zsolve) ] ].
  Ltac kunkw W := solve [ unshelve eapply (kz_unk_wr ZL_t0 m _ _ _ _ _ _ W); first [ reflexivity | lia | (cbn [zden nth ZL_t0 app]; zsolve) ] ].
  Ltac ksh S := solve [ apply (kz_zero bsegs ZL_t0 m); [reflexivity | cbn [zden nth ZL_t0 app]; zsolve | cbn [zden nth ZL_t0 app]; zsolve
                                                      | cbn [zden nth ZL_t0 app]; zsolve |];
                        cbn [zden nth ZL_t0 app]; rewrite !(Z.mod_small _ M64) by lia; intros i Hi;
                        match goal with |- m (Z_to_bv 64 (?x + SH + i)) = _ => replace (x + SH + i) with (SH + x + i) by lia
                                      | |- m (Z_to_bv 64 (?x + SH + 0 + i)) = _ => replace (x + SH + 0 + i) with (SH + x + i) by lia end;
                        apply S; lia ].
  Ltac kwsaved k := solve [ apply kz_word; [reflexivity | (clear_quant; lia) | cbn [zden nth ZL_t0 app]; zsolve |
                         cbn [zden nth ZL_t0 app]; rewrite <- ?E_SP; rewrite !(Z.mod_small _ M64) by (clear_quant; lia);
                         replace (zsp + _) with (zsp - 8 - 8 * k) by lia; exact (M_SAVED k ltac:(lia)) ] ].

  Lemma t0_kn_0 : know_ok bsegs (mkEZ ZL_t0) m (firstn 50 (skipn 0 B2_defs.T0_kn)).
  Proof.
    pose proof (stk_wr_atA m lo zsp (zsp - 8640) 8640 M_STK ltac:(lia) ltac:(lia) ltac:(lia)) as W_FX;
    pose proof (rw_cells_wr_at _ _ _ _ 4 M_O24 ltac:(cbn; lia)) as W_O24;
    pose proof (rw_cells_wr_at _ _ _ _ 40 M_O56 ltac:(cbn; lia)) as W_O56;
    assert (R_BUF' : forall i, 0 <= i < Z.of_nat (length jbuf) -> seg_rom bsegs (Z_to_bv 64 (BUF + i)) = None) by (rewrite M_BUFl; apply seg_rom_blk; lia);
    pose proof (rw_cells_wr_at _ _ _ _ 2048 M_F ltac:(cbn; lia)) as W_F;
    pose proof (rw_cells_bytes_at _ _ _ _ M_F) as B_F;
    assert (L_F : Z.of_nat (length (cells_bytes [C8 j0; C8 j1; C8 j2; CB 2016 jfr; C8 (Z_to_bv 64 FLAG)])) = 2048) by (rewrite cells_bytes_length by (destruct M_F as [[Hw _] _]; exact Hw); reflexivity);
    assert (R_F' : forall i, 0 <= i < Z.of_nat (length (cells_bytes [C8 j0; C8 j1; C8 j2; CB 2016 jfr; C8 (Z_to_bv 64 FLAG)])) -> seg_rom bsegs (Z_to_bv 64 (F + i)) = None) by (rewrite L_F; apply seg_rom_blk; lia).
    unfold B2_defs.T0_kn; cbn [firstn skipn].
    cbv [B2_defs.vTHIS B2_defs.vDOC B2_defs.vBUF B2_defs.vLEN B2_defs.vIDX B2_defs.vN B2_defs.vTBASE B2_defs.vCAPT B2_defs.vSBASE B2_defs.vCAPS B2_defs.vOCB B2_defs.vIAB B2_defs.vSP B2_defs.vSP16 B2_defs.vT8 B2_defs.vDOC8 B2_defs.vB8 B2_defs.vI8 B2_defs.vTB8 B2_defs.vSB8 B2_defs.vOC8 B2_defs.vIA8 B2_defs.vBO B2_defs.vBG B2_defs.vIG B2_defs.vSG B2_defs.vF B2_defs.vF11 B2_defs.vSHF B2_defs.vSPA B2_defs.vFLAG B2_defs.vTP B2_defs.vGP B2_defs.vRA B2_defs.vS0 B2_defs.vS1 B2_defs.vS2 B2_defs.vS3 B2_defs.vS4 B2_defs.vS5 B2_defs.vS6 B2_defs.vS7 B2_defs.vS8 B2_defs.vS9 B2_defs.vS10 B2_defs.vS11 B2_defs.vPB B2_defs.V B2_defs.add B2_defs.sub B2_defs.mul].
    repeat (apply Forall_cons; [
    lazymatch goal with
    | |- kentry_ok _ _ _ (KDisj (SA (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit _)) _) _ (SA (EVar 16) _) _) =>
        apply kz_disj; [reflexivity | cbn [zden nth ZL_t0 app]; clear_quant; repeat (rewrite (Z.mod_small _ M64) by lia);
          unfold DJ in D8; solve [destruct D8 as [h|h]; [left; lia | right; lia] | destruct D8 as [h|h]; [right; lia | left; lia]]]
    | |- kentry_ok _ _ _ (KDisj (SA (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit _)) _) _ (SA (EVar 17) _) _) =>
        apply kz_disj; [reflexivity | cbn [zden nth ZL_t0 app]; clear_quant; repeat (rewrite (Z.mod_small _ M64) by lia);
          unfold DJ in D15; solve [destruct D15 as [h|h]; [left; lia | right; lia] | destruct D15 as [h|h]; [right; lia | left; lia]]]
    | |- kentry_ok _ _ _ (KDisj (SA (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit _)) _) _ (SA (EVar 18) _) _) =>
        apply kz_disj; [reflexivity | cbn [zden nth ZL_t0 app]; clear_quant; repeat (rewrite (Z.mod_small _ M64) by lia);
          unfold DJ in D21; solve [destruct D21 as [h|h]; [left; lia | right; lia] | destruct D21 as [h|h]; [right; lia | left; lia]]]
    | |- kentry_ok _ _ _ (KDisj (SA (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit _)) _) _ (SA (EVar 20) _) _) =>
        apply kz_disj; [reflexivity | cbn [zden nth ZL_t0 app]; clear_quant; repeat (rewrite (Z.mod_small _ M64) by lia);
          unfold DJ in D26; solve [destruct D26 as [h|h]; [left; lia | right; lia] | destruct D26 as [h|h]; [right; lia | left; lia]]]
    | |- kentry_ok _ _ _ (KDisj (SA (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit _)) _) _ (SA (EVar 22) _) _) =>
        apply kz_disj; [reflexivity | cbn [zden nth ZL_t0 app]; clear_quant; repeat (rewrite (Z.mod_small _ M64) by lia);
          unfold DJ in D30; solve [destruct D30 as [h|h]; [left; lia | right; lia] | destruct D30 as [h|h]; [right; lia | left; lia]]]
    | |- kentry_ok _ _ _ (KDisj (SA (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit _)) _) _ (SA (EVar 24) _) _) =>
        apply kz_disj; [reflexivity | cbn [zden nth ZL_t0 app]; clear_quant; repeat (rewrite (Z.mod_small _ M64) by lia);
          unfold DJ in D33; solve [destruct D33 as [h|h]; [left; lia | right; lia] | destruct D33 as [h|h]; [right; lia | left; lia]]]
    | |- kentry_ok _ _ _ (KDisj (SA (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit _)) _) _ (SA (EVar 26) _) _) =>
        apply kz_disj; [reflexivity | cbn [zden nth ZL_t0 app]; clear_quant; repeat (rewrite (Z.mod_small _ M64) by lia);
          unfold DJ in D35; solve [destruct D35 as [h|h]; [left; lia | right; lia] | destruct D35 as [h|h]; [right; lia | left; lia]]]
    | |- kentry_ok _ _ _ (KDisj (SA (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit _)) _) _ (SA (EVar 27) _) _) =>
        apply kz_disj; [reflexivity | cbn [zden nth ZL_t0 app]; clear_quant; repeat (rewrite (Z.mod_small _ M64) by lia);
          unfold DJ in D36; solve [destruct D36 as [h|h]; [left; lia | right; lia] | destruct D36 as [h|h]; [right; lia | left; lia]]]
    | |- kentry_ok _ _ _ (KRange _ _ _) => apply kz_range; [reflexivity | cbn [zden nth ZL_t0 app]; zsolve]
    | |- kentry_ok _ _ _ (KAlign _ _) => apply kz_align; [reflexivity | (clear_quant; lia) | cbn [zden nth ZL_t0 app]; zsolve]
    | |- kentry_ok _ _ _ (KDisj (SA _ _) _ (SA _ _) _) => apply kz_disj; [reflexivity | cbn [zden nth ZL_t0 app];
          rewrite <- ?E_SP, <- ?E_T8, <- ?E_DOC8, <- ?E_B8, <- ?E_I8, <- ?E_TB8, <- ?E_SB8, <- ?E_OC8, <- ?E_IA8, <- ?E_F11; first [djsolve | djsolve2]]
    | |- kentry_ok _ _ _ (KWord (SA (ELit 0) 0x112a80) _ _) => kwc M_GOT 16%nat
    | |- kentry_ok _ _ _ (KWord (SA (ELit 0) 0x11b678) _ _) => kwc M_SHB 0%nat
    | |- kentry_ok _ _ _ (KWord (SA (ELit 0) 0x112ad8) _ _) => kwc M_SUARG 0%nat
    | |- kentry_ok _ _ _ (KWord (SA (ELit 0) 0x11b680) _ _) => kwc M_SUAR 0%nat
    | |- kentry_ok _ _ _ (KWord (SA (ELit 0) 0x113720) _ _) => kwc M_NT 0%nat
    | |- kentry_ok _ _ _ (KWord (SA (ELit 0) 0x1174c0) _ _) => kwc M_FMIN 0%nat
    | |- kentry_ok _ _ _ (KWord (SA (EMd M_MUL (ELit 8) (EVar 17)) _) _ _) => first [ kwc M_DOC 0%nat | kwc M_DOC 8%nat ]
    | |- kentry_ok _ _ _ (KWord (SA (EMd M_MUL (ELit 2048) (EVar 28)) _) _ _) => kwc M_F 2040%nat
    | |- kentry_ok _ _ _ (KWord (SA (EMd M_MUL (ELit 16) (EVar 1)) (-416)) _ _) =>
        solve [ apply kz_word; [reflexivity | (clear_quant; lia) | cbn [zden nth ZL_t0 app]; zsolve |
                cbn [zden nth ZL_t0 app]; rewrite <- ?E_SP; rewrite !(Z.mod_small _ M64) by (clear_quant; lia); exact M_Z416 ] ]
    | |- kentry_ok _ _ _ (KWord (SA (EMd M_MUL (ELit 16) (EVar 1)) ?o) _ _) => let k := eval vm_compute in ((- o - 8) / 8) in kwsaved k
    | |- kentry_ok _ _ _ (KWord _ _ _) =>
        first [ kwc M_O8 0%nat | kwc M_O16 0%nat | kwc M_O40 0%nat | kwc M_O40 8%nat | kwc M_O40 9%nat
              | kwc M_O56 0%nat | kwc M_O56 8%nat | kwc M_O56 16%nat | kwc M_O56 24%nat ]
    | |- kentry_ok _ _ _ (KZero (SA (EMd M_MUL (ELit 2) (EVar 1)) _) _) =>
        solve [ apply (kz_zero bsegs ZL_t0 m); [reflexivity | cbn [zden nth ZL_t0 app]; zsolve | cbn [zden nth ZL_t0 app]; zsolve | cbn [zden nth ZL_t0 app]; zsolve |];
                cbn [zden nth ZL_t0 app]; rewrite !(Z.mod_small _ M64) by lia; intros i Hi;
                replace (2 * SP16 + 2147449800 + i) with (SH + 2 * SP16 - 1080 + i) by lia; apply S_STK; lia ]
    | |- kentry_ok _ _ _ (KZero (SA (EAlu ALU_SUB (EMd M_MUL (ELit 2) (EVar 1)) (EMd M_MUL (ELit 2) (EVar 29))) _) _) =>
        solve [ apply (kz_zero bsegs ZL_t0 m); [reflexivity | cbn [zden nth ZL_t0 app]; zsolve | cbn [zden nth ZL_t0 app]; zsolve | cbn [zden nth ZL_t0 app]; zsolve |];
                cbn [zden nth ZL_t0 app]; rewrite !(Z.mod_small _ M64) by (clear_quant; lia); intros i Hi;
                match goal with |- m (Z_to_bv 64 ?x) = _ => replace x with (SH + 2 * SP16 - 1080 + (x - (SH + 2 * SP16 - 1080))) by lia end;
                apply S_STK; clear_quant; lia ]
    | |- kentry_ok _ _ _ (KZero (SA (EVar 16) _) _) => ksh S_T8
    | |- kentry_ok _ _ _ (KZero (SA (EVar 17) _) _) => ksh S_DOC8
    | |- kentry_ok _ _ _ (KZero (SA (EVar 18) _) _) => ksh S_B8
    | |- kentry_ok _ _ _ (KZero (SA (EVar 20) _) _) => ksh S_I8
    | |- kentry_ok _ _ _ (KZero (SA (EVar 22) _) _) => ksh S_TB8
    | |- kentry_ok _ _ _ (KZero (SA (EVar 24) _) _) => ksh S_SB8
    | |- kentry_ok _ _ _ (KZero (SA (EVar 26) _) _) => ksh S_OC8
    | |- kentry_ok _ _ _ (KZero (SA (EVar 27) _) _) => ksh S_IA8
    | |- kentry_ok _ _ _ (KZero (SA (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit _)) _) _) =>
        solve [ apply (kz_zero bsegs ZL_t0 m); [reflexivity | cbn [zden nth ZL_t0 app]; zsolve | cbn [zden nth ZL_t0 app]; zsolve | cbn [zden nth ZL_t0 app]; zsolve |];
                cbn [zden nth ZL_t0 app]; rewrite !(Z.mod_small _ M64) by lia; intros i Hi;
                replace (256 * F11 + SH + 0 + i) with (SH + 256 * F11 + i) by lia; apply S_F; lia ]
    | |- kentry_ok _ _ _ (KZero (SA (ELit 0) ?a) (ELit ?n)) =>
        solve [ apply (kz_zero bsegs ZL_t0 m); [reflexivity | cbn [zden nth ZL_t0 app]; zsolve | cbn [zden nth ZL_t0 app]; zsolve | cbn [zden nth ZL_t0 app]; zsolve |];
                cbn [zden nth ZL_t0 app]; rewrite !(Z.mod_small _ M64) by lia; intros i Hi;
                replace (0 + a + i) with (a + i) by lia; apply (S_IMG a n i); [cbn [A2_IMGSH In]; tauto | lia] ]
    | |- kentry_ok _ _ _ (KZero _ _) =>
        unshelve eapply (kz_zero_bytes bsegs ZL_t0 m _ _ _ _ _ _ M_BUF R_BUF');
          [reflexivity | cbn [zden nth ZL_t0 app]; zsolve | cbn [zden nth ZL_t0 app]; zsolve | cbn [zden nth ZL_t0 app]; zsolve |];
        cbn [zden nth ZL_t0 app]; rewrite !(Z.mod_small _ M64) by lia; intros i Hi;
        replace (8 * B8 + BO + LEN + 0 - BUF + i) with (LEN + i) by lia; apply M_BUFz; lia
    | |- kentry_ok _ _ _ (KWr _ _) => first [ kwr W_FX | kwr W_O24 | kwr W_O56 | kwr W_TB | kwr W_SB | kwr W_OC | kwr W_IA | kwr W_F | kwr M_SHF | kwr W_STKSH ]
    | |- kentry_ok _ _ _ (KUnk (SA (EMd M_MUL (ELit 16) (EVar 1)) _) _) =>
        apply (stk_unkA ZL_t0 m lo zsp); [exact M_STK | reflexivity | lia | lia | cbn [zden nth ZL_t0 app]; zsolve | cbn [zden nth ZL_t0 app]; zsolve]
    | |- kentry_ok _ _ _ (KUnk _ _) =>
        first [ kunk M_BUF R_BUF' | kunkw W_IDX | kunkw W_OC | kunkw W_IA | kunk B_F R_F' ]
    | |- kentry_ok _ _ _ (KImg _ _) =>
        apply kz_img; [lia | lia | exact M_INV | intros a Ha; rewrite a_ro_addr; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; clear - Ha; lia]
    end |]). apply Forall_nil.
  Qed.
End S_T0.
