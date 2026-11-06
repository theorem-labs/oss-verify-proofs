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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg ABase.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import PA2_kz.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require A2N_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Local Notation M64 := 18446744073709551616.
Local Notation SH := 2147450880%Z (only parsing).

Section S_T0N1.
  Context {rc : runConstT}.
  Variables (zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 : Z)
            (T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG : Z) (V : Z) (CP8 : Z) (CGF : Z) (ZP : Z) (DG : Z) (SD : Z) (SRG : Z) (HC : Z) (HCE : Z) (HB : Z) (HBE : Z) (MD : Z) (rest : list Z).
  Definition ZL_t0n' : list Z :=
    [zra; SP16; zgp; ztp; zs0; zs1; zs2; zs3; zs4; zs5; zs6; zs7; zs8; zs9; zs10; zs11;
     T8; DOC8; B8; LEN; I8; N; TB8; CAPT; SB8; CAPS; OC8; IA8; F11; PB; FLAG; BO; BG; IG; SG; V; CP8; CGF; ZP; DG; SD; SRG; HC; HCE; HB; HBE; MD] ++ rest.
  Variables (zsp THIS DOC BUF IDX TBASE SBASE OCB IAB F COPY : Z).
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
  Hypothesis E_CP8 : COPY = 8 * CP8.
  Variable m : word -> option byte.
  Variables (lo : Z) (jbuf : list byte) (x24 x88 : word) (j0 j1 j2 : word) (jfr : list byte).
  Hypothesis H_LEN : 1 <= LEN <= 1048512.
  Hypothesis H_N : 1 <= N <= LEN.
  Hypothesis H_CAPT : N + 3 <= CAPT <= 16777216.
  Hypothesis H_CAPS : LEN + 60 <= CAPS <= 16777216.
  Hypothesis H_CAPS3 : 5 * LEN + 182 <= 3 * CAPS.
  Hypothesis H_SP : 0x7fff00000000 <= zsp <= 2 ^ 47.
  Hypothesis H_TP : ztp = 0x642e70.
  Hypothesis H_THIS : 0x665000 <= THIS /\ THIS + 96 <= ATOPM /\ THIS + 96 + 8608 <= zsp.
  Hypothesis H_DOC : 0x665000 <= DOC /\ DOC + 16 <= ATOPM /\ DOC + 16 + 8608 <= zsp.
  Hypothesis H_BUF : 0 <= BO <= 7 /\ 0x665000 <= BUF - BO /\ BUF + LEN + 64 <= ATOPM /\ BUF + LEN + 64 + 8608 <= zsp.
  Hypothesis H_IDX : 0x665000 <= IDX /\ IDX + 4 * N + 12 <= ATOPM /\ IDX + 4 * N + 12 + 8608 <= zsp.
  Hypothesis H_TBASE : 0x665000 <= TBASE /\ TBASE + (8 * CAPT) <= ATOPM /\ TBASE + (8 * CAPT) + 8608 <= zsp.
  Hypothesis H_SBASE : 0x665000 <= SBASE /\ SBASE + CAPS <= ATOPM /\ SBASE + CAPS + 8608 <= zsp.
  Hypothesis H_OCB : 0x665000 <= OCB /\ OCB + 8192 <= ATOPM /\ OCB + 8192 + 8608 <= zsp.
  Hypothesis H_IAB : 0x665000 <= IAB /\ IAB + 1024 <= ATOPM /\ IAB + 1024 + 8608 <= zsp.
  Hypothesis H_F : 0x665000 <= F /\ F + 2048 <= ATOPM /\ F + 2048 + 8608 <= zsp.
  Hypothesis H_COPY : 0x665000 <= COPY /\ COPY + LEN - V + 64 <= ATOPM /\ COPY + LEN - V + 64 + 8608 <= zsp.
  Hypothesis HB_THIS : DJ 0x7fff7000 0x100000001000 THIS 96.
  Hypothesis HB_DOC : DJ 0x7fff7000 0x100000001000 DOC 16.
  Hypothesis HB_BUF : DJ 0x7fff7000 0x100000001000 BUF (LEN + 64).
  Hypothesis HB_IDX : DJ 0x7fff7000 0x100000001000 IDX (4 * N + 12).
  Hypothesis HB_TBASE : DJ 0x7fff7000 0x100000001000 TBASE (8 * CAPT).
  Hypothesis HB_SBASE : DJ 0x7fff7000 0x100000001000 SBASE CAPS.
  Hypothesis HB_OCB : DJ 0x7fff7000 0x100000001000 OCB 8192.
  Hypothesis HB_IAB : DJ 0x7fff7000 0x100000001000 IAB 1024.
  Hypothesis HB_F : DJ 0x7fff7000 0x100000001000 F 2048.
  Hypothesis HB_COPY : DJ 0x7fff7000 0x100000001000 COPY (LEN - V + 64).
  Hypothesis D1 : DJ THIS 96 DOC 16.
  Hypothesis D2 : DJ THIS 96 BUF (LEN + 64).
  Hypothesis D3 : DJ THIS 96 IDX (4 * N + 12).
  Hypothesis D4 : DJ THIS 96 TBASE (8 * CAPT).
  Hypothesis D5 : DJ THIS 96 SBASE CAPS.
  Hypothesis D6 : DJ THIS 96 OCB 8192.
  Hypothesis D7 : DJ THIS 96 IAB 1024.
  Hypothesis D8 : DJ THIS 96 F 2048.
  Hypothesis D9 : DJ THIS 96 COPY (LEN - V + 64).
  Hypothesis D10 : DJ DOC 16 BUF (LEN + 64).
  Hypothesis D11 : DJ DOC 16 IDX (4 * N + 12).
  Hypothesis D12 : DJ DOC 16 TBASE (8 * CAPT).
  Hypothesis D13 : DJ DOC 16 SBASE CAPS.
  Hypothesis D14 : DJ DOC 16 OCB 8192.
  Hypothesis D15 : DJ DOC 16 IAB 1024.
  Hypothesis D16 : DJ DOC 16 F 2048.
  Hypothesis D17 : DJ DOC 16 COPY (LEN - V + 64).
  Hypothesis D18 : DJ BUF (LEN + 64) IDX (4 * N + 12).
  Hypothesis D19 : DJ BUF (LEN + 64) TBASE (8 * CAPT).
  Hypothesis D20 : DJ BUF (LEN + 64) SBASE CAPS.
  Hypothesis D21 : DJ BUF (LEN + 64) OCB 8192.
  Hypothesis D22 : DJ BUF (LEN + 64) IAB 1024.
  Hypothesis D23 : DJ BUF (LEN + 64) F 2048.
  Hypothesis D24 : DJ BUF (LEN + 64) COPY (LEN - V + 64).
  Hypothesis D25 : DJ IDX (4 * N + 12) TBASE (8 * CAPT).
  Hypothesis D26 : DJ IDX (4 * N + 12) SBASE CAPS.
  Hypothesis D27 : DJ IDX (4 * N + 12) OCB 8192.
  Hypothesis D28 : DJ IDX (4 * N + 12) IAB 1024.
  Hypothesis D29 : DJ IDX (4 * N + 12) F 2048.
  Hypothesis D30 : DJ IDX (4 * N + 12) COPY (LEN - V + 64).
  Hypothesis D31 : DJ TBASE (8 * CAPT) SBASE CAPS.
  Hypothesis D32 : DJ TBASE (8 * CAPT) OCB 8192.
  Hypothesis D33 : DJ TBASE (8 * CAPT) IAB 1024.
  Hypothesis D34 : DJ TBASE (8 * CAPT) F 2048.
  Hypothesis D35 : DJ TBASE (8 * CAPT) COPY (LEN - V + 64).
  Hypothesis D36 : DJ SBASE CAPS OCB 8192.
  Hypothesis D37 : DJ SBASE CAPS IAB 1024.
  Hypothesis D38 : DJ SBASE CAPS F 2048.
  Hypothesis D39 : DJ SBASE CAPS COPY (LEN - V + 64).
  Hypothesis D40 : DJ OCB 8192 IAB 1024.
  Hypothesis D41 : DJ OCB 8192 F 2048.
  Hypothesis D42 : DJ OCB 8192 COPY (LEN - V + 64).
  Hypothesis D43 : DJ IAB 1024 F 2048.
  Hypothesis D44 : DJ IAB 1024 COPY (LEN - V + 64).
  Hypothesis D45 : DJ F 2048 COPY (LEN - V + 64).
  Hypothesis H_BG : 8 <= BG <= 131080 /\ 0 <= LEN + BO + 64 - 8 * BG <= 7.
  Hypothesis H_IG : 2 <= IG <= 0x200000 /\ 0 <= 8 * IG - (4 * N + 12) <= 7.
  Hypothesis H_SG : 7 <= SG <= 2097152 /\ 0 <= CAPS - 8 * SG <= 7.
  Hypothesis H_IGB : IDX + 8 * IG <= ATOPM.
  Hypothesis H_V : 0 <= V /\ 1 <= LEN - V.
  Hypothesis H_CGF : 8 <= CGF <= 131080 /\ 0 <= LEN - V + 64 - 8 * CGF <= 7.
  Hypothesis H_ZP : 0 <= ZP <= 1 /\ 1 <= LEN - V + 64 - 8 * CGF + 8 * ZP <= 8.
  Hypothesis H_DG : 1 <= DG <= 131072 /\ 0 <= 8 * DG - (LEN - V) <= 7.
  Hypothesis H_SD : 0 <= SD <= 131072 /\ 0 <= BO + V - 8 * SD <= 7.
  Hypothesis H_SRG : 1 <= SRG <= 131080 /\ 0 <= 8 * SRG - (BO + LEN - 8 * SD) <= 7 /\ 0 <= BG - (SD + SRG) <= 131080.
  Hypothesis H_HC : 0x19940 <= HC <= 0x1ffffffe000 /\ 0 <= COPY - 64 * HC <= 63.
  Hypothesis H_HCE : 0x19940 <= HCE <= 0x1ffffffe000 /\ 0 <= 64 * HCE - (COPY + (LEN - V + 64)) <= 63.
  Hypothesis H_HB : 0x19940 <= HB <= 0x1ffffffe000 /\ 0 <= BUF + V - 64 * HB <= 63.
  Hypothesis H_HBE : 0x19940 <= HBE <= 0x1ffffffe000 /\ 0 <= 64 * HBE - (BUF + LEN) <= 63.
  Hypothesis H_MD : 0 <= MD <= 131072 /\ 0 <= (LEN - V) - 8 * MD <= 7.
  Hypothesis H_SE : B8 + BG <= 0xfffffff0000 /\ I8 + IG <= 0xfffffff0000 /\ TB8 + CAPT <= 0xfffffff0000 /\ SB8 + SG <= 0xfffffff0000 /\ CP8 + CGF <= 0xfffffff0000.
  Hypothesis S_T8 : forall i, 0 <= i < 12 -> m (Z_to_bv 64 (SH + T8 + i)) = Some (Z_to_bv 8 0).
  Hypothesis S_DOC8 : forall i, 0 <= i < 2 -> m (Z_to_bv 64 (SH + DOC8 + i)) = Some (Z_to_bv 8 0).
  Hypothesis S_B8 : forall i, 0 <= i < BG -> m (Z_to_bv 64 (SH + B8 + i)) = Some (Z_to_bv 8 0).
  Hypothesis S_I8 : forall i, 0 <= i < IG -> m (Z_to_bv 64 (SH + I8 + i)) = Some (Z_to_bv 8 0).
  Hypothesis S_TB8 : forall i, 0 <= i < CAPT -> m (Z_to_bv 64 (SH + TB8 + i)) = Some (Z_to_bv 8 0).
  Hypothesis S_SB8 : forall i, 0 <= i < SG -> m (Z_to_bv 64 (SH + SB8 + i)) = Some (Z_to_bv 8 0).
  Hypothesis S_OC8 : forall i, 0 <= i < 1024 -> m (Z_to_bv 64 (SH + OC8 + i)) = Some (Z_to_bv 8 0).
  Hypothesis S_IA8 : forall i, 0 <= i < 128 -> m (Z_to_bv 64 (SH + IA8 + i)) = Some (Z_to_bv 8 0).
  Hypothesis S_CP8 : forall i, 0 <= i < CGF -> m (Z_to_bv 64 (SH + CP8 + i)) = Some (Z_to_bv 8 0).
  Hypothesis S_F : forall i, 0 <= i < 256 -> m (Z_to_bv 64 (SH + 256 * F11 + i)) = Some (Z_to_bv 8 0).
  Hypothesis M_O8 : rw_cells asegs m (THIS + 8) [C4 (Z_to_bv 64 N)].
  Hypothesis M_O16 : rw_cells asegs m (THIS + 16) [C8 (Z_to_bv 64 IDX)].
  Hypothesis W_O24 : wr_at asegs m (THIS + 24) 4.
  Hypothesis M_O40 : rw_cells asegs m (THIS + 40) [C8 (Z_to_bv 64 1024); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Hypothesis M_O56 : rw_cells asegs m (THIS + 56) [C8 (Z_to_bv 64 OCB); C8 (Z_to_bv 64 IAB); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 LEN); C8 x88].
  Hypothesis M_DOC : rw_cells asegs m DOC [C8 (Z_to_bv 64 TBASE); C8 (Z_to_bv 64 SBASE)].
  Hypothesis M_O88 : rw_cells asegs m (THIS + 88) [C8 (Z_to_bv 64 DOC)].
  Hypothesis W_TB : wr_at asegs m TBASE (8 * CAPT).
  Hypothesis W_SB : wr_at asegs m SBASE CAPS.
  Hypothesis W_OC : wr_at asegs m OCB 8192.
  Hypothesis W_IA : wr_at asegs m IAB 1024.
  Hypothesis W_IDX : wr_at asegs m IDX (4 * N + 12).
  Hypothesis M_BUF : bytes_at asegs m BUF jbuf.
  Hypothesis M_BUFl : Z.of_nat (length jbuf) = LEN + 64.
  Hypothesis M_BUFz : forall i, 0 <= i < 64 -> nth_error jbuf (Z.to_nat (LEN + i)) = Some (Z_to_bv 8 0).
  Hypothesis M_GOT : rw_cells asegs m 0x1072f0 [C8 (Z_to_bv 64 0x1a1628); C8 (Z_to_bv 64 0x10d2f8); C8 (Z_to_bv 64 0x10faf8);
                                              C8 (Z_to_bv 64 0x1107e8); C8 (Z_to_bv 64 0x1107f0); C8 (Z_to_bv 64 0x1107e0)].
  Hypothesis M_SHB : rw_cells asegs m 0x10faf8 [C8 (Z_to_bv 64 0x7fff8000)].
  Hypothesis M_SUARG : rw_cells asegs m 0x107358 [C8 (Z_to_bv 64 0x10fb00)].
  Hypothesis M_SUAR : rw_cells asegs m 0x10fb00 [C4 (Z_to_bv 64 1)].
  Hypothesis M_NT : rw_cells asegs m 0x107fa0 [C8 (Z_to_bv 64 0x2cb90)].
  Hypothesis M_FMIN : rw_cells asegs m 0x10b978 [C4 (Z_to_bv 64 8388608)].
  Hypothesis M_LG : bytes_at asegs m (SH + CP8 + (CGF - ZP)) (word_to_le_bytes 1 (Z_to_bv 64 (LEN - V + 64 - 8 * (CGF - ZP) - 8 * ZP))).
  Hypothesis W_HC : wr_at asegs m (SH + 8 * HC) (8 * (HCE - HC)).
  Hypothesis W_HB : wr_at asegs m (SH + 8 * HB) (8 * (HBE - HB)).
  Hypothesis W_COPY : wr_at asegs m COPY (LEN - V + 64).
  Variable jcopy : list byte.
  Hypothesis M_COPY : bytes_at asegs m COPY jcopy.
  Hypothesis M_COPYl : Z.of_nat (length jcopy) = LEN - V + 64.
  Hypothesis M_IDX0 : rw_cells asegs m IDX [C4 (Z_to_bv 64 V)].
  Variable zspa : Z.
  Hypothesis E_SPA : zspa = zsp - 384 - 16 * PB.
  Hypothesis M_SPA152 : rw_cells asegs m (zspa + 152) [C8 (Z_to_bv 64 (T8 + SH + 7))].
  Hypothesis M_SPA160 : rw_cells asegs m (zspa + 160) [C8 (Z_to_bv 64 (THIS + 16))].
  Hypothesis M_SPA168 : rw_cells asegs m (zspa + 168) [C8 (Z_to_bv 64 (IDX + 4))].
  Hypothesis M_SPA176 : rw_cells asegs m (zspa + 176) [C8 (Z_to_bv 64 (TBASE + 8))].
  Hypothesis M_SPA184 : rw_cells asegs m (zspa + 184) [C8 (Z_to_bv 64 (THIS + 8))].
  Hypothesis M_SPA192 : rw_cells asegs m (zspa + 192) [C8 (Z_to_bv 64 (T8 + SH + 2))].
  Hypothesis M_SPA200 : rw_cells asegs m (zspa + 200) [C8 (Z_to_bv 64 (T8 + SH + 1))].
  Hypothesis M_SPA208 : rw_cells asegs m (zspa + 208) [C8 (Z_to_bv 64 (SBASE))].
  Hypothesis M_SPA216 : rw_cells asegs m (zspa + 216) [C8 (Z_to_bv 64 (THIS + 88))].
  Hypothesis M_SPA224 : rw_cells asegs m (zspa + 224) [C8 (Z_to_bv 64 (T8 + SH + 11))].
  Hypothesis M_SPA232 : rw_cells asegs m (zspa + 232) [C8 (Z_to_bv 64 (THIS))].
  Hypothesis M_SPA240 : rw_cells asegs m (zspa + 240) [C8 (Z_to_bv 64 (F))].
  Hypothesis M_SPA248 : rw_cells asegs m (zspa + 248) [C8 (Z_to_bv 64 (SH))].
  Hypothesis M_SPA264 : rw_cells asegs m (zspa + 264) [C8 (Z_to_bv 64 (F))].
  Hypothesis W_F : wr_at asegs m F 2048.
  Hypothesis M_FL : rw_cells asegs m (F + 2040) [C8 (Z_to_bv 64 FLAG)].
  Hypothesis M_SHF : wr_at asegs m (SH + 256 * F11) 256.
  Hypothesis M_SAVED : forall k, 0 <= k < 13 ->
    bytes_at asegs m (zsp - 8 - 8 * k) (word_to_le_bytes 8 (Z_to_bv 64 (nth (Z.to_nat k) [zra; zs0; zs1; zs2; zs3; zs4; zs5; zs6; zs7; zs8; zs9; zs10; zs11] 0))).
  Hypothesis M_Z384 : bytes_at asegs m (zsp - 384) (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Hypothesis H_SPA : 0 <= PB <= 1 /\ (zsp - 384 - 16 * PB) mod 32 = 0.
  Hypothesis S_IMG : forall a n i, In (a, n) A2_IMGSH -> 0 <= i < n -> m (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).
  Hypothesis M_STK : stk asegs m lo zsp.
  Hypothesis M_LO : 0x665000 <= lo <= zsp - 8608.
  Hypothesis S_STK : forall i, 0 <= i < 1076 -> m (Z_to_bv 64 (SH + 2 * SP16 - 1076 + i)) = Some (Z_to_bv 8 0).
  Hypothesis M_INV : mem_inv asegs m.
  Lemma ba_congr : forall (mm : amem) a a' bs bs', bytes_at asegs mm a bs -> a' = a -> bs' = bs -> bytes_at asegs mm a' bs'.
  Proof. intros mm a a' bs bs' H -> ->. exact H. Qed.

  Ltac kwc H k := solve [ unshelve eapply (kz_word_cells asegs ZL_t0n' m _ _ _ _ _ _ k _ _ H); first [ reflexivity | (clear_quant; lia) | (cbn [zden nth ZL_t0n' app]; zsolve)
                         | (cbn [zden nth ZL_t0n' app]; rewrite ?E_SP, ?E_T8, ?E_DOC8, ?E_B8, ?E_I8, ?E_TB8, ?E_SB8, ?E_OC8, ?E_IA8, ?E_F11, ?E_CP8; reflexivity) ] ].
  Ltac kwr W := solve [ unshelve eapply (kz_wr_sub asegs ZL_t0n' m _ _ _ _ _ _ W); first [ reflexivity | (cbn [zden nth ZL_t0n' app]; zsolve) ] ].
  Ltac kunk B R := solve [ unshelve eapply (kz_unk_bytes asegs ZL_t0n' m _ _ _ _ _ _ B R); first [ reflexivity | (cbn [zden nth ZL_t0n' app]; zsolve) ] ].
  Ltac kunkw W := solve [ unshelve eapply (kz_unk_wr ZL_t0n' m _ _ _ _ _ _ W); first [ reflexivity | lia | (cbn [zden nth ZL_t0n' app]; zsolve) ] ].
  Ltac ksh S := solve [ apply (kz_zero asegs ZL_t0n' m); [reflexivity | cbn [zden nth ZL_t0n' app]; zsolve | cbn [zden nth ZL_t0n' app]; zsolve
                                                      | cbn [zden nth ZL_t0n' app]; zsolve |];
                        cbn [zden nth ZL_t0n' app]; rewrite !(Z.mod_small _ M64) by lia; intros i Hi;
                        match goal with |- m (Z_to_bv 64 (?x + SH + i)) = _ => replace (x + SH + i) with (SH + x + i) by lia
                                      | |- m (Z_to_bv 64 (?x + SH + 0 + i)) = _ => replace (x + SH + 0 + i) with (SH + x + i) by lia end;
                        apply S; lia ].
  Ltac kwsaved k := solve [ apply kz_word; [reflexivity | (clear_quant; lia) | cbn [zden nth ZL_t0n' app]; zsolve |
                         cbn [zden nth ZL_t0n' app]; rewrite <- ?E_SP; rewrite !(Z.mod_small _ M64) by (clear_quant; lia);
                         replace (zsp + _) with (zsp - 8 - 8 * k) by lia; exact (M_SAVED k ltac:(lia)) ] ].

  Lemma t0n_kn_1 : know_ok asegs (mkEZ ZL_t0n') m (firstn 40 (skipn 40 A2N_defs.T0_kn)).
  Proof.
    pose proof (stk_wr_atA m lo zsp (zsp - 8608) 8608 M_STK ltac:(lia) ltac:(lia) ltac:(lia)) as W_FX;
    pose proof I as W_O24_;
    pose proof (rw_cells_wr_at _ _ _ _ 40 M_O56 ltac:(cbn; lia)) as W_O56;
    assert (R_BUF' : forall i, 0 <= i < Z.of_nat (length jbuf) -> seg_rom asegs (Z_to_bv 64 (BUF + i)) = None) by (rewrite M_BUFl; apply seg_rom_blk; lia);
    assert (R_COPY' : forall i, 0 <= i < Z.of_nat (length jcopy) -> seg_rom asegs (Z_to_bv 64 (COPY + i)) = None) by (rewrite M_COPYl; apply seg_rom_blk; lia).
    unfold A2N_defs.T0_kn; cbn [firstn skipn].
    cbv [A2N_defs.vTHIS A2N_defs.vDOC A2N_defs.vBUF A2N_defs.vLEN A2N_defs.vIDX A2N_defs.vN A2N_defs.vTBASE A2N_defs.vCAPT A2N_defs.vSBASE A2N_defs.vCAPS A2N_defs.vOCB A2N_defs.vIAB A2N_defs.vSP A2N_defs.vSP16 A2N_defs.vT8 A2N_defs.vDOC8 A2N_defs.vB8 A2N_defs.vI8 A2N_defs.vTB8 A2N_defs.vSB8 A2N_defs.vOC8 A2N_defs.vIA8 A2N_defs.vBO A2N_defs.vBG A2N_defs.vIG A2N_defs.vSG A2N_defs.vF A2N_defs.vF11 A2N_defs.vSHF A2N_defs.vSPA A2N_defs.vFLAG A2N_defs.vTP A2N_defs.vGP A2N_defs.vRA A2N_defs.vS0 A2N_defs.vS1 A2N_defs.vS2 A2N_defs.vS3 A2N_defs.vS4 A2N_defs.vS5 A2N_defs.vS6 A2N_defs.vS7 A2N_defs.vS8 A2N_defs.vS9 A2N_defs.vS10 A2N_defs.vS11 A2N_defs.vPB A2N_defs.V A2N_defs.add A2N_defs.sub A2N_defs.mul A2N_defs.vCOPY A2N_defs.vV A2N_defs.vC8 A2N_defs.vCGF A2N_defs.vZP A2N_defs.vDG A2N_defs.vSD A2N_defs.vSRG A2N_defs.vHC A2N_defs.vHCE A2N_defs.vHB A2N_defs.vHBE A2N_defs.vMD].
    repeat (apply Forall_cons; [
    lazymatch goal with
    | |- kentry_ok _ _ _ (KDisj (SA (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit _)) _) _ (SA (EVar 16) _) _) =>
        apply kz_disj; [reflexivity | cbn [zden nth ZL_t0n' app]; clear_quant; repeat (rewrite (Z.mod_small _ M64) by lia);
          unfold DJ in D8; solve [destruct D8 as [h|h]; [left; lia | right; lia] | destruct D8 as [h|h]; [right; lia | left; lia]]]
    | |- kentry_ok _ _ _ (KDisj (SA (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit _)) _) _ (SA (EVar 17) _) _) =>
        apply kz_disj; [reflexivity | cbn [zden nth ZL_t0n' app]; clear_quant; repeat (rewrite (Z.mod_small _ M64) by lia);
          unfold DJ in D16; solve [destruct D16 as [h|h]; [left; lia | right; lia] | destruct D16 as [h|h]; [right; lia | left; lia]]]
    | |- kentry_ok _ _ _ (KDisj (SA (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit _)) _) _ (SA (EVar 18) _) _) =>
        apply kz_disj; [reflexivity | cbn [zden nth ZL_t0n' app]; clear_quant; repeat (rewrite (Z.mod_small _ M64) by lia);
          unfold DJ in D23; solve [destruct D23 as [h|h]; [left; lia | right; lia] | destruct D23 as [h|h]; [right; lia | left; lia]]]
    | |- kentry_ok _ _ _ (KDisj (SA (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit _)) _) _ (SA (EVar 20) _) _) =>
        apply kz_disj; [reflexivity | cbn [zden nth ZL_t0n' app]; clear_quant; repeat (rewrite (Z.mod_small _ M64) by lia);
          unfold DJ in D29; solve [destruct D29 as [h|h]; [left; lia | right; lia] | destruct D29 as [h|h]; [right; lia | left; lia]]]
    | |- kentry_ok _ _ _ (KDisj (SA (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit _)) _) _ (SA (EVar 22) _) _) =>
        apply kz_disj; [reflexivity | cbn [zden nth ZL_t0n' app]; clear_quant; repeat (rewrite (Z.mod_small _ M64) by lia);
          unfold DJ in D34; solve [destruct D34 as [h|h]; [left; lia | right; lia] | destruct D34 as [h|h]; [right; lia | left; lia]]]
    | |- kentry_ok _ _ _ (KDisj (SA (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit _)) _) _ (SA (EVar 24) _) _) =>
        apply kz_disj; [reflexivity | cbn [zden nth ZL_t0n' app]; clear_quant; repeat (rewrite (Z.mod_small _ M64) by lia);
          unfold DJ in D38; solve [destruct D38 as [h|h]; [left; lia | right; lia] | destruct D38 as [h|h]; [right; lia | left; lia]]]
    | |- kentry_ok _ _ _ (KDisj (SA (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit _)) _) _ (SA (EVar 26) _) _) =>
        apply kz_disj; [reflexivity | cbn [zden nth ZL_t0n' app]; clear_quant; repeat (rewrite (Z.mod_small _ M64) by lia);
          unfold DJ in D41; solve [destruct D41 as [h|h]; [left; lia | right; lia] | destruct D41 as [h|h]; [right; lia | left; lia]]]
    | |- kentry_ok _ _ _ (KDisj (SA (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit _)) _) _ (SA (EVar 27) _) _) =>
        apply kz_disj; [reflexivity | cbn [zden nth ZL_t0n' app]; clear_quant; repeat (rewrite (Z.mod_small _ M64) by lia);
          unfold DJ in D43; solve [destruct D43 as [h|h]; [left; lia | right; lia] | destruct D43 as [h|h]; [right; lia | left; lia]]]
    | |- kentry_ok _ _ _ (KRange _ _ _) => apply kz_range; [reflexivity | cbn [zden nth ZL_t0n' app]; zsolve]
    | |- kentry_ok _ _ _ (KAlign _ _) => apply kz_align; [reflexivity | (clear_quant; lia) | cbn [zden nth ZL_t0n' app]; zsolve]
    | |- kentry_ok _ _ _ (KDisj (SA _ _) _ (SA _ _) _) => apply kz_disj; [reflexivity | cbn [zden nth ZL_t0n' app];
          rewrite <- ?E_SP, <- ?E_T8, <- ?E_DOC8, <- ?E_B8, <- ?E_I8, <- ?E_TB8, <- ?E_SB8, <- ?E_OC8, <- ?E_IA8, <- ?E_F11, <- ?E_CP8; first [djsolve | djsolve2]]
    | |- kentry_ok _ _ _ (KWord (SA (ELit 0) 0x107300) _ _) => kwc M_GOT 16%nat
    | |- kentry_ok _ _ _ (KWord (SA (ELit 0) 0x10faf8) _ _) => kwc M_SHB 0%nat
    | |- kentry_ok _ _ _ (KWord (SA (ELit 0) 0x107358) _ _) => kwc M_SUARG 0%nat
    | |- kentry_ok _ _ _ (KWord (SA (ELit 0) 0x10fb00) _ _) => kwc M_SUAR 0%nat
    | |- kentry_ok _ _ _ (KWord (SA (ELit 0) 0x107fa0) _ _) => kwc M_NT 0%nat
    | |- kentry_ok _ _ _ (KWord (SA (ELit 0) 0x10b978) _ _) => kwc M_FMIN 0%nat
    | |- kentry_ok _ _ _ (KWord (SA (EMd M_MUL (ELit 8) (EVar 17)) _) _ _) => first [ kwc M_DOC 0%nat | kwc M_DOC 8%nat ]
    | |- kentry_ok _ _ _ (KWord (SA (EMd M_MUL (ELit 8) (EVar 20)) 0) 4 _) => kwc M_IDX0 0%nat
    | |- kentry_ok _ _ _ (KWord (SA (EAlu ALU_ADD (EVar 36) _) _) 1 _) =>
        solve [ apply kz_word; [reflexivity | (clear_quant; lia) | cbn [zden nth ZL_t0n' app]; zsolve |];
                cbn [zden nth ZL_t0n' app]; eapply ba_congr; [exact M_LG | clear_quant; repeat (rewrite (Z.mod_small _ M64) by lia); lia |
                do 2 f_equal; clear_quant; lia] ]
    | |- kentry_ok _ _ _ (KWord (SA (EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 1)) (ELit (-384))) (EMd M_MUL (ELit 16) (EVar 29))) ?k) 8 _) =>
        lazymatch k with 152 => kwc M_SPA152 0%nat | 160 => kwc M_SPA160 0%nat | 168 => kwc M_SPA168 0%nat | 176 => kwc M_SPA176 0%nat | 184 => kwc M_SPA184 0%nat | 192 => kwc M_SPA192 0%nat | 200 => kwc M_SPA200 0%nat | 208 => kwc M_SPA208 0%nat | 216 => kwc M_SPA216 0%nat | 224 => kwc M_SPA224 0%nat | 232 => kwc M_SPA232 0%nat | 240 => kwc M_SPA240 0%nat | 248 => kwc M_SPA248 0%nat | 264 => kwc M_SPA264 0%nat end
    | |- kentry_ok _ _ _ (KWord (SA (EMd M_MUL (ELit 2048) (EVar 28)) _) _ _) => kwc M_FL 0%nat
    | |- kentry_ok _ _ _ (KWord (SA (EMd M_MUL (ELit 16) (EVar 1)) (-384)) _ _) =>
        solve [ apply kz_word; [reflexivity | (clear_quant; lia) | cbn [zden nth ZL_t0n' app]; zsolve |
                cbn [zden nth ZL_t0n' app]; rewrite <- ?E_SP; rewrite !(Z.mod_small _ M64) by (clear_quant; lia); exact M_Z384 ] ]
    | |- kentry_ok _ _ _ (KWord (SA (EMd M_MUL (ELit 16) (EVar 1)) ?o) _ _) => let k := eval vm_compute in ((- o - 8) / 8) in kwsaved k
    | |- kentry_ok _ _ _ (KWord _ _ _) =>
        first [ kwc M_O8 0%nat | kwc M_O16 0%nat | kwc M_O88 0%nat | kwc M_O40 0%nat | kwc M_O40 8%nat | kwc M_O40 9%nat
              | kwc M_O56 0%nat | kwc M_O56 8%nat | kwc M_O56 16%nat | kwc M_O56 24%nat ]
    | |- kentry_ok _ _ _ (KZero (SA (EMd M_MUL (ELit 2) (EVar 1)) _) _) =>
        solve [ apply (kz_zero asegs ZL_t0n' m); [reflexivity | cbn [zden nth ZL_t0n' app]; zsolve | cbn [zden nth ZL_t0n' app]; zsolve | cbn [zden nth ZL_t0n' app]; zsolve |];
                cbn [zden nth ZL_t0n' app]; rewrite !(Z.mod_small _ M64) by lia; intros i Hi;
                replace (2 * SP16 + 2147449804 + i) with (SH + 2 * SP16 - 1076 + i) by lia; apply S_STK; lia ]
    | |- kentry_ok _ _ _ (KZero (SA (EAlu ALU_SUB (EMd M_MUL (ELit 2) (EVar 1)) (EMd M_MUL (ELit 2) (EVar 29))) _) _) =>
        solve [ apply (kz_zero asegs ZL_t0n' m); [reflexivity | cbn [zden nth ZL_t0n' app]; zsolve | cbn [zden nth ZL_t0n' app]; zsolve | cbn [zden nth ZL_t0n' app]; zsolve |];
                cbn [zden nth ZL_t0n' app]; rewrite !(Z.mod_small _ M64) by (clear_quant; lia); intros i Hi;
                match goal with |- m (Z_to_bv 64 ?x) = _ => replace x with (SH + 2 * SP16 - 1076 + (x - (SH + 2 * SP16 - 1076))) by lia end;
                apply S_STK; clear_quant; lia ]
    | |- kentry_ok _ _ _ (KZero (SA (EVar 16) _) _) => ksh S_T8
    | |- kentry_ok _ _ _ (KZero (SA (EVar 17) _) _) => ksh S_DOC8
    | |- kentry_ok _ _ _ (KZero (SA (EVar 18) _) _) => ksh S_B8
    | |- kentry_ok _ _ _ (KZero (SA (EVar 20) _) _) => ksh S_I8
    | |- kentry_ok _ _ _ (KZero (SA (EVar 22) _) _) => ksh S_TB8
    | |- kentry_ok _ _ _ (KZero (SA (EVar 24) _) _) => ksh S_SB8
    | |- kentry_ok _ _ _ (KZero (SA (EVar 26) _) _) => ksh S_OC8
    | |- kentry_ok _ _ _ (KZero (SA (EVar 27) _) _) => ksh S_IA8
    | |- kentry_ok _ _ _ (KZero (SA (EVar 36) _) _) => ksh S_CP8
    | |- kentry_ok _ _ _ (KZero (SA (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit _)) _) _) =>
        solve [ apply (kz_zero asegs ZL_t0n' m); [reflexivity | cbn [zden nth ZL_t0n' app]; zsolve | cbn [zden nth ZL_t0n' app]; zsolve | cbn [zden nth ZL_t0n' app]; zsolve |];
                cbn [zden nth ZL_t0n' app]; rewrite !(Z.mod_small _ M64) by lia; intros i Hi;
                replace (256 * F11 + SH + 0 + i) with (SH + 256 * F11 + i) by lia; apply S_F; lia ]
    | |- kentry_ok _ _ _ (KZero (SA (ELit 0) ?a) (ELit ?n)) =>
        solve [ apply (kz_zero asegs ZL_t0n' m); [reflexivity | cbn [zden nth ZL_t0n' app]; zsolve | cbn [zden nth ZL_t0n' app]; zsolve | cbn [zden nth ZL_t0n' app]; zsolve |];
                cbn [zden nth ZL_t0n' app]; rewrite !(Z.mod_small _ M64) by lia; intros i Hi;
                replace (0 + a + i) with (a + i) by lia; apply (S_IMG a n i); [cbn [A2_IMGSH In]; tauto | lia] ]
    | |- kentry_ok _ _ _ (KZero _ _) =>
        unshelve eapply (kz_zero_bytes asegs ZL_t0n' m _ _ _ _ _ _ M_BUF R_BUF');
          [reflexivity | cbn [zden nth ZL_t0n' app]; zsolve | cbn [zden nth ZL_t0n' app]; zsolve | cbn [zden nth ZL_t0n' app]; zsolve |];
        cbn [zden nth ZL_t0n' app]; rewrite !(Z.mod_small _ M64) by lia; intros i Hi;
        replace (8 * B8 + BO + LEN + 0 - BUF + i) with (LEN + i) by lia; apply M_BUFz; lia
    | |- kentry_ok _ _ _ (KWr _ _) => first [ kwr W_FX | kwr W_O24 | kwr W_O56 | kwr W_TB | kwr W_SB | kwr W_OC | kwr W_IA | kwr W_F | kwr M_SHF | kwr W_COPY | kwr W_HC | kwr W_HB ]
    | |- kentry_ok _ _ _ (KUnk (SA (EMd M_MUL (ELit 16) (EVar 1)) _) _) =>
        apply (stk_unkA ZL_t0n' m lo zsp); [exact M_STK | reflexivity | lia | lia | cbn [zden nth ZL_t0n' app]; zsolve | cbn [zden nth ZL_t0n' app]; zsolve]
    | |- kentry_ok _ _ _ (KUnk _ _) =>
        first [ kunk M_BUF R_BUF' | kunkw W_IDX | kunkw W_OC | kunkw W_IA | kunkw W_F | kunk M_COPY R_COPY' ]
    | |- kentry_ok _ _ _ (KImg _ _) =>
        apply kz_img; [lia | lia | exact M_INV | intros a Ha; rewrite a_ro_addr; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; clear - Ha; lia]
    end |]). apply Forall_nil.
  Qed.
End S_T0N1.
