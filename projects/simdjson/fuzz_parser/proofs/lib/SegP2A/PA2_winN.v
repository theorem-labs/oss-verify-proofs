(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import A2Lib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require A2N_defs A2D_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Local Notation M64 := 18446744073709551616.
Local Notation SH := 2147450880%Z (only parsing).

Section WN.
  Variable RNG : footprint.
  Variables (zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 : Z)
            (T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG : Z)
            (V CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD : Z) (rest : list Z).
  Definition ZLwn : list Z :=
    [zra; SP16; zgp; ztp; zs0; zs1; zs2; zs3; zs4; zs5; zs6; zs7; zs8; zs9; zs10; zs11;
     T8; DOC8; B8; LEN; I8; N; TB8; CAPT; SB8; CAPS; OC8; IA8; F11; PB; FLAG; BO; BG; IG; SG;
     V; CP8; CGF; ZP; DG; SD; SRG; HC; HCE; HBG; HBGE; MD] ++ rest.
  Hypothesis H_SP : 8608 <= 16 * SP16 <= 2 ^ 47.
  Hypothesis H_SZ : 0 <= LEN < 2^40 /\ 0 <= N < 2^40 /\ 1 <= CAPT < 2^40 /\ 1 <= CAPS < 2^40 /\ 1 <= BG < 2^40 /\ 1 <= IG < 2^40
                    /\ 1 <= SG < 2^40 /\ 0 <= BO < 8.
  Hypothesis H_B8 : 0 <= T8 /\ 0 <= DOC8 /\ 0 <= B8 /\ 0 <= I8 /\ 0 <= TB8 /\ 0 <= SB8 /\ 0 <= OC8 /\ 0 <= IA8 /\ 0 <= F11.
  Hypothesis H_NZ : 0 <= V <= LEN /\ 0 <= CP8 < 2^44 /\ 0 <= CGF < 2^40 /\ 0 <= HC < 2^44 /\ 0 <= HCE - HC < 2^40
                    /\ 0 <= HBG < 2^44 /\ 0 <= HBGE - HBG < 2^40.
  Hypothesis R_STK : rng RNG (16 * SP16 - 8608) 8608.
  Hypothesis R_IMG : rng RNG 0x10000 0x655000.
  Hypothesis R_STKSH : rng RNG (2 * SP16 + SH - 1076) 1076.
  Hypothesis R_IMGSH : rng RNG 0x7fffa000 0xcaa00.
  Hypothesis R_T : rng RNG (8 * T8) 96.
  Hypothesis R_TS : rng RNG (T8 + SH) 12.
  Hypothesis R_D : rng RNG (8 * DOC8) 16.
  Hypothesis R_DS : rng RNG (DOC8 + SH) 2.
  Hypothesis R_B : rng RNG (8 * B8 + BO) (LEN + 64).
  Hypothesis R_BS : rng RNG (B8 + SH) BG.
  Hypothesis R_I : rng RNG (8 * I8) (4 * N + 12).
  Hypothesis R_IS : rng RNG (I8 + SH) IG.
  Hypothesis R_TB : rng RNG (8 * TB8) (8 * CAPT).
  Hypothesis R_TBS : rng RNG (TB8 + SH) CAPT.
  Hypothesis R_SB : rng RNG (8 * SB8) CAPS.
  Hypothesis R_SBS : rng RNG (SB8 + SH) SG.
  Hypothesis R_OC : rng RNG (8 * OC8) 8192.
  Hypothesis R_OCS : rng RNG (OC8 + SH) 1024.
  Hypothesis R_IA : rng RNG (8 * IA8) 1024.
  Hypothesis R_IAS : rng RNG (IA8 + SH) 128.
  Hypothesis R_F : rng RNG (2048 * F11) 2048.
  Hypothesis R_FS : rng RNG (256 * F11 + SH) 256.
  Hypothesis R_CP : rng RNG (8 * CP8) (LEN - V + 64).
  Hypothesis R_CPS : rng RNG (CP8 + SH) CGF.
  Hypothesis R_HC : rng RNG (8 * HC + SH) (8 * (HCE - HC)).
  Hypothesis R_HB : rng RNG (8 * HBG + SH) (8 * (HBGE - HBG)).

  Ltac wden := cbn [SX.awin_den fst snd]; rewrite ?u_zden by reflexivity; cbn [zden nth ZLwn app].
  Ltac wfin R := eapply rng_sub'; [exact R|]; pose proof (rng_bounds _ _ _ R);
                 rewrite ?(Z.mod_small _ M64) by lia; lia.
  Ltac winN :=
    lazymatch goal with
    | |- rng _ (fst (SX.awin_den _ (?b, ?off, _))) _ =>
      wden;
      lazymatch b with
      | EMd M_MUL (ELit 16) (EVar 1) => wfin R_STK
      | EMd M_MUL (ELit 2) (EVar 1) => wfin R_STKSH
      | ELit 0 => lazymatch off with 65536 => wfin R_IMG | _ => wfin R_IMGSH end
      | EMd M_MUL (ELit 8) (EVar 16) => wfin R_T
      | EVar 16 => wfin R_TS
      | EMd M_MUL (ELit 8) (EVar 17) => wfin R_D
      | EVar 17 => wfin R_DS
      | EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 18)) (EVar 31) => wfin R_B
      | EVar 18 => wfin R_BS
      | EMd M_MUL (ELit 8) (EVar 20) => wfin R_I
      | EVar 20 => wfin R_IS
      | EMd M_MUL (ELit 8) (EVar 22) => wfin R_TB
      | EVar 22 => wfin R_TBS
      | EMd M_MUL (ELit 8) (EVar 24) => wfin R_SB
      | EVar 24 => wfin R_SBS
      | EMd M_MUL (ELit 8) (EVar 26) => wfin R_OC
      | EVar 26 => wfin R_OCS
      | EMd M_MUL (ELit 8) (EVar 27) => wfin R_IA
      | EVar 27 => wfin R_IAS
      | EMd M_MUL (ELit 2048) (EVar 28) => wfin R_F
      | EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit 2147450880) => wfin R_FS
      | EMd M_MUL (ELit 8) (EVar 36) => wfin R_CP
      | EVar 36 => wfin R_CPS
      | EMd M_MUL (ELit 8) (EVar 42) => wfin R_HC
      | EMd M_MUL (ELit 8) (EVar 44) => wfin R_HB
      end
    end.

  Lemma a2n_wins : fp_le (SX.fp_of (SP.p_A A2N_defs.A2N) (mkEZ ZLwn)) RNG /\ SX.aw_genuine (mkEZ ZLwn) (SP.p_A A2N_defs.A2N).
  Proof using All.
    cbn [SP.p_A A2N_defs.A2N SP.PGCA SP.PGH SP.PGX].
    cbv [A2N_defs.vSP A2N_defs.vSP16 A2N_defs.vTHIS A2N_defs.vT8 A2N_defs.vDOC A2N_defs.vDOC8 A2N_defs.vBUF A2N_defs.vB8 A2N_defs.vBO
         A2N_defs.vLEN A2N_defs.vIDX A2N_defs.vI8 A2N_defs.vN A2N_defs.vTBASE A2N_defs.vTB8 A2N_defs.vCAPT A2N_defs.vSBASE A2N_defs.vSB8
         A2N_defs.vCAPS A2N_defs.vOCB A2N_defs.vOC8 A2N_defs.vIAB A2N_defs.vIA8 A2N_defs.vBG A2N_defs.vIG A2N_defs.vSG A2N_defs.vF
         A2N_defs.vF11 A2N_defs.vSHF A2N_defs.vCOPY A2N_defs.vC8 A2N_defs.vCGF A2N_defs.vV A2N_defs.vHC A2N_defs.vHCE A2N_defs.vHB
         A2N_defs.vHBE A2N_defs.V A2N_defs.mul A2N_defs.add A2N_defs.sub].
    match goal with |- fp_le (SX.fp_of (Some ?W) _) _ /\ _ =>
      assert (HW : Forall (fun w => rng RNG (fst (SX.awin_den (mkEZ ZLwn) w)) (snd (SX.awin_den (mkEZ ZLwn) w) - fst (SX.awin_den (mkEZ ZLwn) w))) W)
        by (repeat (apply Forall_cons; [winN|]); apply Forall_nil)
    end.
    split; [apply fp_of_le | apply (aw_genuine_of_rng _ _ RNG)]; exact HW.
  Qed.

  Lemma a2d_wins : fp_le (SX.fp_of (SP.p_A A2D_defs.A2D) (mkEZ ZLwn)) RNG /\ SX.aw_genuine (mkEZ ZLwn) (SP.p_A A2D_defs.A2D).
  Proof using All.
    cbn [SP.p_A A2D_defs.A2D SP.PGCA SP.PGH SP.PGX].
    cbv [A2D_defs.vSP A2D_defs.vSP16 A2D_defs.vTHIS A2D_defs.vT8 A2D_defs.vDOC A2D_defs.vDOC8 A2D_defs.vBUF A2D_defs.vB8 A2D_defs.vBO
         A2D_defs.vLEN A2D_defs.vIDX A2D_defs.vI8 A2D_defs.vN A2D_defs.vTBASE A2D_defs.vTB8 A2D_defs.vCAPT A2D_defs.vSBASE A2D_defs.vSB8
         A2D_defs.vCAPS A2D_defs.vOCB A2D_defs.vOC8 A2D_defs.vIAB A2D_defs.vIA8 A2D_defs.vBG A2D_defs.vIG A2D_defs.vSG A2D_defs.vF
         A2D_defs.vF11 A2D_defs.vSHF A2D_defs.V A2D_defs.mul A2D_defs.add].
    match goal with |- fp_le (SX.fp_of (Some ?W) _) _ /\ _ =>
      assert (HW : Forall (fun w => rng RNG (fst (SX.awin_den (mkEZ ZLwn) w)) (snd (SX.awin_den (mkEZ ZLwn) w) - fst (SX.awin_den (mkEZ ZLwn) w))) W)
        by (repeat (apply Forall_cons; [winN|]); apply Forall_nil)
    end.
    split; [apply fp_of_le | apply (aw_genuine_of_rng _ _ RNG)]; exact HW.
  Qed.
End WN.
