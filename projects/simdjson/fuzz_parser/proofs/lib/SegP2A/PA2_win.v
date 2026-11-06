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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA2 Require A2E_defs A2_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Local Notation M64 := 18446744073709551616.
Local Notation SH := 2147450880%Z (only parsing).

Section W.
  Variable RNG : footprint.
  Variables (zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 : Z)
            (T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG : Z) (rest : list Z).
  Definition ZLw : list Z :=
    [zra; SP16; zgp; ztp; zs0; zs1; zs2; zs3; zs4; zs5; zs6; zs7; zs8; zs9; zs10; zs11;
     T8; DOC8; B8; LEN; I8; N; TB8; CAPT; SB8; CAPS; OC8; IA8; F11; PB; FLAG; BO; BG; IG; SG] ++ rest.
  Hypothesis H_SP : 8608 <= 16 * SP16 <= 2 ^ 47.
  Hypothesis H_SZ : 0 <= LEN < 2^40 /\ 0 <= N < 2^40 /\ 1 <= CAPT < 2^40 /\ 1 <= CAPS < 2^40 /\ 1 <= BG < 2^40 /\ 1 <= IG < 2^40
                    /\ 1 <= SG < 2^40 /\ 0 <= BO < 8.
  Hypothesis H_B8 : 0 <= T8 /\ 0 <= DOC8 /\ 0 <= B8 /\ 0 <= I8 /\ 0 <= TB8 /\ 0 <= SB8 /\ 0 <= OC8 /\ 0 <= IA8 /\ 0 <= F11.
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

  (* [comment removed for export] *)
  Ltac wden := cbn [SX.awin_den fst snd]; rewrite ?u_zden by reflexivity; cbn [zden nth ZLw app].
  Ltac wfin R := eapply rng_sub'; [exact R|]; pose proof (rng_bounds _ _ _ R);
                 rewrite ?(Z.mod_small _ M64) by lia; lia.
  Ltac win1 :=
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
      end
    end.

  Lemma a2e_wins : fp_le (SX.fp_of (SP.p_A A2E_defs.A2E) (mkEZ ZLw)) RNG /\ SX.aw_genuine (mkEZ ZLw) (SP.p_A A2E_defs.A2E).
  Proof.
    cbn [SP.p_A A2E_defs.A2E SP.PGCA SP.PGX].
    cbv [A2E_defs.vSP A2E_defs.vSP16 A2E_defs.vTHIS A2E_defs.vT8 A2E_defs.vDOC A2E_defs.vDOC8 A2E_defs.vBUF A2E_defs.vB8 A2E_defs.vBO
         A2E_defs.vLEN A2E_defs.vIDX A2E_defs.vI8 A2E_defs.vN A2E_defs.vTBASE A2E_defs.vTB8 A2E_defs.vCAPT A2E_defs.vSBASE A2E_defs.vSB8
         A2E_defs.vCAPS A2E_defs.vOCB A2E_defs.vOC8 A2E_defs.vIAB A2E_defs.vIA8 A2E_defs.vBG A2E_defs.vIG A2E_defs.vSG
         A2E_defs.V A2E_defs.mul A2E_defs.add].
    match goal with |- fp_le (SX.fp_of (Some ?W) _) _ /\ _ =>
      assert (HW : Forall (fun w => rng RNG (fst (SX.awin_den (mkEZ ZLw) w)) (snd (SX.awin_den (mkEZ ZLw) w) - fst (SX.awin_den (mkEZ ZLw) w))) W)
        by (repeat (apply Forall_cons; [win1|]); apply Forall_nil)
    end.
    split; [apply fp_of_le | apply (aw_genuine_of_rng _ _ RNG)]; exact HW.
  Qed.

  (* [comment removed for export] *)
  Hypothesis R_F : rng RNG (2048 * F11) 2048.
  Hypothesis R_FS : rng RNG (256 * F11 + SH) 256.
  Ltac win2 :=
    lazymatch goal with
    | |- rng _ (fst (SX.awin_den _ (?b, _, _))) _ =>
      lazymatch b with
      | EMd M_MUL (ELit 2048) (EVar 28) => wden; wfin R_F
      | EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit 2147450880) => wden; wfin R_FS
      | _ => win1
      end
    end.

  Lemma a2_wins : fp_le (SX.fp_of (SP.p_A A2_defs.A2) (mkEZ ZLw)) RNG /\ SX.aw_genuine (mkEZ ZLw) (SP.p_A A2_defs.A2).
  Proof.
    cbn [SP.p_A A2_defs.A2 SP.PGCA SP.PGH SP.PGX].
    cbv [A2_defs.vSP A2_defs.vSP16 A2_defs.vTHIS A2_defs.vT8 A2_defs.vDOC A2_defs.vDOC8 A2_defs.vBUF A2_defs.vB8 A2_defs.vBO
         A2_defs.vLEN A2_defs.vIDX A2_defs.vI8 A2_defs.vN A2_defs.vTBASE A2_defs.vTB8 A2_defs.vCAPT A2_defs.vSBASE A2_defs.vSB8
         A2_defs.vCAPS A2_defs.vOCB A2_defs.vOC8 A2_defs.vIAB A2_defs.vIA8 A2_defs.vBG A2_defs.vIG A2_defs.vSG A2_defs.vF A2_defs.vF11
         A2_defs.vSHF A2_defs.V A2_defs.mul A2_defs.add].
    match goal with |- fp_le (SX.fp_of (Some ?W) _) _ /\ _ =>
      assert (HW : Forall (fun w => rng RNG (fst (SX.awin_den (mkEZ ZLw) w)) (snd (SX.awin_den (mkEZ ZLw) w) - fst (SX.awin_den (mkEZ ZLw) w))) W)
        by (repeat (apply Forall_cons; [win2|]); apply Forall_nil)
    end.
    split; [apply fp_of_le | apply (aw_genuine_of_rng _ _ RNG)]; exact HW.
  Qed.
End W.
