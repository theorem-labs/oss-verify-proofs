(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (10 recorded proofs replaced by written proofs (spaA_bounds, inv_shadowA, acc_shadowA and 7 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import FseRdKit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg ABase RtCells.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_fse_rd_base () := "C46Stdlib5Lists4List8map_consC47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib5AsanW>AF_fse_rd_base4a_SPC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc59OSSVerify5KrLib5AsanW>AF_fse_rd_base5a_SPAC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203i59OSSVerify5KrLib5AsanW>AF_fse_rd_base6rdctxA00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib5AsanW>AF_fse_rd_base6rd_okAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW>AF_fse_rd_base6rd_shAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW>AF_fse_rd_base3a_mC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW>AF_fse_rd_base4a_NCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW>AF_fse_rd_base6a_MSVPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW>AF_fse_rd_base5a_TLPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW>AF_fse_rd_base5a_BUFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW>AF_fse_rd_base5rd_WAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow:unpoisonedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW>AF_fse_rd_base5a_bufC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00c59OSSVerify5KrLib5AsanW>AF_fse_rd_base6a_msv0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW>AF_fse_rd_base4a_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW>AF_fse_rd_base4a_FFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase4ablkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase8ablk_linC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib5AsanW5ABase>ablk_disj_bandC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z3minC59OSSVerify5KrLib4LibA6Shadow7gran_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow@unpoisoned_munchC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega6VarMap1t01I47Corelib4Init5Logic2or00C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01c59OSSVerify5KrLib5AsanW>AF_fse_rd_base5a_rt0C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib4LibA6Shadow8shad_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow4KENDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW>AF_fse_rd_base:RDA_CALLEEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib5AsanW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase3KLSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW>AF_fse_rd_base;spaA_boundsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow5nshadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC59OSSVerify5KrLib4LibA5ExecF6acc_inC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib4LibA6Shadow9nshad_divC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7Z_to_bvK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW>AF_fse_rd_base7rd_invAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:FseWalkKit4u16sC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib6Common:FseWalkKit?u16arr_store_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib6Common:FseWalkKit<u16arr_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib3Lib3Arr3updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount8to_shortC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseNCount7upd_natC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8FseRdKit>u16s_upd_shortC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib4Spec9FseNCount4ZupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseLemmas>upd_nat_lengthC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3MemDbytes_at_write_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW>AF_fse_rd_base8FRA_mainC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3Lib5Frame9stk_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem=mem_inv_storeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC59OSSVerify5KrLib5AsanW4AImg5asegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepArw_cells_store_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init3Nat3mulC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib6Common:FseWalkKit;u16s_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr;u8arr_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib4LibA6ShadowCunpoisoned_check_rdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow4svalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow:sval_rangeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesc59OSSVerify5KrLib5AsanW>AF_fse_rd_base5chk1AC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib4Spec9FseNCount4ZnthC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z8max_specC47Corelib5Lists7ListDef3nthC46Stdlib5Lists4List9nth_errorC47Corelib4Init9Datatypes:option_mapC46Stdlib5Lists4List>nth_error_nth'C46Stdlib5Lists4List=nth_error_mapC59OSSVerify5KrLib3Lib3Arr9u8ro_readC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List6nth_InC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib4Spec9FseLemmas9all_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseLemmas@Forall_all_bytesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
Ltac brute_regF n r lo cnt g :=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e =>
      let F := eval pattern r in e in
      lazymatch F with
      | ?f r =>
          let H := fresh "BR" in
          assert (H : forall r0, lo <= r0 < lo + cnt -> (f r0 =? g r0) = true)
            by (apply (brute_range (fun r0 => f r0 =? g r0) lo cnt); vm_compute; reflexivity);
          replace e with (g r) by (symmetry; apply Z.eqb_eq; apply H; lia);
          clear H
      end
  | _ => fail "brute_regF: register" n "holds" w
  end.

(* [comment removed for export] *)
Record rdctxA : Type := mkRDA {
  a_gp : word; a_tp : word;
  a_F : bvmap 5 word; a_fc : bv 32;
  a_m : amem;                               (* [comment removed for export] *)
  a_SP : Z; a_FF : Z; a_NC : Z; a_MSVP : Z; a_TLP : Z; a_BUF : Z; a_lo : Z;
  a_rt0 : list Z; a_buf : list Z; a_msv0 : Z
}.

Definition a_SPA (C : rdctxA) : Z := (a_SP C - 160) - (a_SP C - 160) mod 32.
Lemma spaA_bounds : forall C, a_SP C mod 16 = 0 -> a_SP C - 176 <= a_SPA C <= a_SP C - 160 /\ a_SPA C mod 32 = 0.
Proof. intros C H. unfold a_SPA. Z.div_mod_to_equations. lia. Qed.
Definition RDA_CALLEE : Z := 2224.     (* [comment removed for export] *)
Definition ASHB : Z := 2147450880.      (* [comment removed for export] *)

Definition rd_WA (C : rdctxA) : list (Z * Z) :=
  [(a_NC C, a_NC C + 2 * zlen (a_rt0 C)); (a_MSVP C, a_MSVP C + 4); (a_TLP C, a_TLP C + 4); (a_SPA C - RDA_CALLEE, a_SPA C + 56)].

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition rd_okA (C : rdctxA) : Prop :=
  8 <= zlen (a_buf C) <= 65536 /\ Forall (fun c => 0 <= c < 256) (a_buf C)
  /\ 0 <= a_msv0 C <= 255 /\ a_msv0 C + 1 <= zlen (a_rt0 C) /\ zlen (a_rt0 C) <= 65536
  /\ a_SP C mod 16 = 0 /\ a_SP C + 16 < KEND /\ a_lo C <= a_SPA C - RDA_CALLEE /\ ATOP <= a_lo C
  /\ ablk (a_NC C) (a_NC C + 2 * zlen (a_rt0 C)) /\ a_NC C mod 8 = 0
  /\ ablk (a_MSVP C) (a_MSVP C + 4) /\ a_MSVP C mod 4 = 0
  /\ ablk (a_TLP C) (a_TLP C + 4) /\ a_TLP C mod 4 = 0
  /\ ablk (a_BUF C) (a_BUF C + zlen (a_buf C))
  /\ ablk (a_FF C) (a_FF C + 64) /\ a_FF C mod 64 = 0
  /\ (a_NC C + 2 * zlen (a_rt0 C) <= a_MSVP C \/ a_MSVP C + 4 <= a_NC C)
  /\ (a_NC C + 2 * zlen (a_rt0 C) <= a_TLP C \/ a_TLP C + 4 <= a_NC C)
  /\ (a_NC C + 2 * zlen (a_rt0 C) <= a_BUF C \/ a_BUF C + zlen (a_buf C) <= a_NC C)
  /\ (a_MSVP C + 4 <= a_TLP C \/ a_TLP C + 4 <= a_MSVP C)
  /\ (a_MSVP C + 4 <= a_BUF C \/ a_BUF C + zlen (a_buf C) <= a_MSVP C)
  /\ (a_TLP C + 4 <= a_BUF C \/ a_BUF C + zlen (a_buf C) <= a_TLP C)
  /\ 0 <= a_BUF C.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rd_shA (C : rdctxA) : Prop :=
  unpoisoned (a_m C) (a_NC C) (a_NC C + 2 * zlen (a_rt0 C)) /\ unpoisoned (a_m C) (a_MSVP C) (a_MSVP C + 4)
  /\ unpoisoned (a_m C) (a_TLP C) (a_TLP C + 4) /\ unpoisoned (a_m C) (a_BUF C) (a_BUF C + zlen (a_buf C)).

(* [comment removed for export] *)
Definition rd_rngA (C : rdctxA) (RNG : footprint) : Prop :=
  rng_aimg RNG /\ rng RNG (a_lo C) (a_SP C - a_lo C)
  /\ rng RNG (a_NC C) (2 * zlen (a_rt0 C)) /\ rng RNG (shad (a_NC C)) (nshad (2 * zlen (a_rt0 C)))
  /\ rng RNG (a_MSVP C) 4 /\ rng RNG (shad (a_MSVP C)) 1
  /\ rng RNG (a_TLP C) 4 /\ rng RNG (shad (a_TLP C)) 1
  /\ rng RNG (a_BUF C) (zlen (a_buf C)) /\ rng RNG (shad (a_BUF C)) (nshad (zlen (a_buf C) + a_BUF C mod 8)).

(* [comment removed for export] *)
Definition FRA_main (C : rdctxA) (j16 : list byte) : list cell :=
  [C8 (Z_to_bv 64 (a_BUF C + zlen (a_buf C) + -4)); C8 (Z_to_bv 64 (Z.shiftr (a_MSVP C) 3 + ASHB)); C8 (Z_to_bv 64 (a_MSVP C));
   C8 (Z_to_bv 64 1431655765); CB 16 j16; C8 (Z_to_bv 64 (a_FF C))].

(* [comment removed for export] *)
Definition rd_invA (C : rdctxA) (m1 : amem) (nc : list Z) (msvw tlw : word) : Prop :=
  u8arr asegs m1 (a_NC C) (u16s (map (Z_to_bv 64) nc)) /\ length nc = length (a_rt0 C)
  /\ bytes_at asegs m1 (a_BUF C) (map (Z_to_bv 8) (a_buf C))
  /\ rw_cells asegs m1 (a_MSVP C) [C4 msvw]
  /\ rw_cells asegs m1 (a_TLP C) [C4 tlw]
  /\ (exists j16, rw_cells asegs m1 (a_SPA C) (FRA_main C j16))
  /\ stk asegs m1 (a_lo C) (a_SPA C)
  /\ munch (rd_WA C) (a_m C) m1 /\ wmono asegs (a_m C) m1 /\ mem_inv asegs m1.

(* [comment removed for export] *)
Lemma inv_shadowA : forall C m1, rd_okA C -> rd_shA C -> munch (rd_WA C) (a_m C) m1 ->
  unpoisoned m1 (a_NC C) (a_NC C + 2 * zlen (a_rt0 C)) /\ unpoisoned m1 (a_MSVP C) (a_MSVP C + 4)
  /\ unpoisoned m1 (a_TLP C) (a_TLP C + 4) /\ unpoisoned m1 (a_BUF C) (a_BUF C + zlen (a_buf C)).
Proof.
  intros C m1 OK (U1 & U2 & U3 & U4) MU.
  destruct OK as (HH & _ & HM0 & HM1 & HN & SP16 & SPK & LO & LOA & BN & _ & BM & _ & BT & _ & BB & BF & _).
  pose proof (ablk_lin _ _ BN) as LN. pose proof (ablk_lin _ _ BM) as LM. pose proof (ablk_lin _ _ BT) as LT. pose proof (ablk_lin _ _ BB) as LB.
  pose proof (ablk_disj_band _ _ BN) as DN. pose proof (ablk_disj_band _ _ BM) as DM. pose proof (ablk_disj_band _ _ BT) as DT.
  pose proof atop_range as ATR.
  unfold rd_WA, RDA_CALLEE, a_SPA, KHIGH, KLS, KEND, AIMG_HI in *.
  repeat split; (eapply unpoisoned_munch; [eassumption| exact MU|]); rewrite !shad_div; unfold ASHOFF; cbn [disjoint_from];
    (split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia|];
     split; [Z.div_mod_to_equations; lia| exact I]).
Qed.


(* [comment removed for export] *)
Lemma okA_lin : forall C, rd_okA C ->
  8 <= zlen (a_buf C) <= 65536 /\ 0 <= a_msv0 C <= 255 /\ a_msv0 C + 1 <= zlen (a_rt0 C) /\ zlen (a_rt0 C) <= 65536
  /\ a_SP C mod 16 = 0 /\ a_SP C + 16 < KEND /\ a_lo C <= a_SPA C - RDA_CALLEE /\ ATOP <= a_lo C
  /\ a_SP C - 176 <= a_SPA C <= a_SP C - 160 /\ a_SPA C mod 32 = 0
  /\ AIMG_HI <= a_NC C /\ a_NC C + 2 * zlen (a_rt0 C) <= ATOP /\ a_NC C mod 8 = 0
  /\ AIMG_HI <= a_MSVP C /\ a_MSVP C + 4 <= ATOP /\ a_MSVP C mod 4 = 0
  /\ AIMG_HI <= a_TLP C /\ a_TLP C + 4 <= ATOP /\ a_TLP C mod 4 = 0
  /\ AIMG_HI <= a_BUF C /\ a_BUF C + zlen (a_buf C) <= ATOP /\ 0 <= a_BUF C
  /\ AIMG_HI <= a_FF C /\ a_FF C + 64 <= ATOP /\ a_FF C mod 64 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_fse_rd_base ()) ["CANSEC1"] "h01Hh12BBh22BFh32BMh42BNh52BTh64__p1h74__p2h84__p3h94__p4h:4__p5h;4__p6h<4__p7h=4__p8h>4__p9h?4__x1h@5__x10hA5__x11hB5__x12hC5__x13hD5__x14hE5__x15hF5__x16hG5__x17hH5__x18hI5__x19hJ4__x2hK5__x20hL4__x3hM4__x4hN4__x5hO4__x6hP4__x7hQ4__x8hR4__x9hS2B8hT1ChU3F64hV3FBYhW2HHhX3HM0hY3HM1hZ3HRTh[2LOh\3LOAh]2M4h^2N8h_2OKh`4SP16ha4SPA1hb4SPA2hc3SPKhd2T4he2_Hhf3_H0hg3_H1hh3_H2hi3_H3hj3_H4hk7__arithhl4__ffhm8__varmaphn5__witho1chp4cstrhq5cstr0p%0p&0p;1p;2p;3p;4p;7p;6p;8g00XNk10LTg001ij1FTg002Nj1UTg00b5j1kTg007bj27Tg007Fj2yTg00c4j3~Tg00cUj1@Tg003Lj1QTg006Bj21Tg000kj1;Tg00dUj1:Tg00eSk10aTg00[Kj16Tg00\Ij14Tg00]Ij13Tg00^Hj12Tg00fIj18Tg00H]j1BTg002lj2OTg00gGj3\Tg01@ck20_Tg0041j2bTg00h<j4}Tg00i5k20^Tg00jQk10]Tg010hk10ATg011Mj1dTg00:Lk10[Tg00:jk20ZTg00;Kj1rTg00<Sk20@Tg00>Tk10YTg00?Tk10XTg013bk10WTg00A0k10VTg00ANk10UTg00B9k20?Tg00B\k10TTg00Dgk308Tg00C>k20>Tg00Cak30RTg00JEk407Tg00EJk20PTg00Elk20OTg00FFk20NTg00G2j3TTg00GLk30STg00Gkk40MTg0170j2hTg008>R0j29Tg0161k10=Tg005ek205Tg014@j2sTg00;jk30iTg00I\k30hTg00=<k20gTg00?4k30fTg00@4k20eTg00@Rk40cTg00K0k70KTg00L\k70;Tg018Yk60bTg00DDk30dTg00L8k80<Tg00M@R1f0R2'h#dp>0k%F2#Fp>03%F2#F#F#F#F#F#F#Fp=vf2R3f1R4'7/92p=Zg00M^R5/74/92p=X%Q2#Q#Q#Qp=t&0=2,h1#dp=?20542,13p=Yf4R6f3R7'71734's1752'9p==17671734's/92p=0f6R8f5R9'O=T1517671734's/92'9p=Cf7R:?\8911349\67/92'9p=GA\9671O34=T15/92'9p=<17:8A\9671O34=T15/92'9'9p=V1167g01:ZR;'y%B4g01;OR<'b,73/92'9p=_17671O34=T15/92'9p>001734/92,97,96p=f%k2,h1#dp=D%F2#F#F#Fp=z1b42,73p=E1758g01>ER=/791167/731O42=T15'9'9'9p=L1O89=T1517=61173/74/92'9'9p=51O:8=T1517=920573,16/74/92'9'9p=J17891b67/73/94/92'9p=M1167/y;1b4<,73/92'9p=K11:8/7917671O34=T15/92'9'9p=H17:81796'917571734'9/92'9p=I1h12p>0J%d2,14p>0I17571734'9/92p>0H%k2,h1#d,14p=>1134/72p=N1O34=T15/92p>04&0=2,h1#d-054,13p=A1O42=T15p=W1142/y;p>0G1O89=T15A\673AT145/92'9'9p=x%B8/b<,7:1796A\734/92'9'9p>0F1b2<,74p>0E&0=2,h1p>0:%d2-054p>0D11429\73p=u11349\67/92p>0C1734/s2p=[1734,s7/92p>021752p=`1s341752'9p>0`1b67/73/94/92p>0B%Q2#Qp>0917=4/92p=|%k2,h1p>0\%r2#rp=^20@12p=qB0i142p=wB0h142p=pg00Tb-0g2p=mg00SWS00@0f42p=o20e12p=gP1P3P4P2H0cp=]20>12p=RP1P4g00N<P2H07p=nP4g00NcR=g00OBR>P>g00ObR?P2g00PBR@K0Kp=l20?12p=aP3P=P>P>P?P1P4g00QIP2H07P@K0Kp=PP3P=P>P>P?P4P2K0;p=iP4P=P>P>P?P2J0bp=eB0d142p=jP6P=P>P>P?P7P3P=P>P>P?P4P2K0;K0;p=SP7P=P>P>P?P3P4P2L0<p>0QP8P=P>P>P?P9P6P7P=P>P>P?P3P4P2L0<L0<p=cAT125p>0117671734/92'9p={AT145/92p>061189/761773AT145/92'9'9p>0jg00R0&0L2P2&0L4P0g00S2R=#FR@#FRA#FRB#URC%k3RD$0kRE%FBS01#FRF#FRG$03RH#v#URI,7E3Z%UH,y2,X2Xo1RH=~1D%@3RD%Q=S02#QS03#QS04#tS05#URJ,7D'X%U=RK,1D%?3RDPDPI%;3RLQ01#URMPLPM%:3RLP3p,2rcRN$0aROPLPN%63RL%U@RP=YLDRDPLPCPN%43RQ%UARR,1QRSPQPRPN%33RT11TRRUPTPRPN%23RV11VEREPN%83RWPW%UGRGPWPGPDPQPSPLPDPTPUPLPDPVPEPLPSPTPUPQPSPVPEPQPUPVPEPTPVD=D0D0D0D0FCGGE<E<GVD_I00DfPC%D7RVPVPI%@7RTPTPJPTPK%?7RTPTPI%;7REPMPEPM%:7RU%B7RQPOPUPE%Q@S06#QS07#z#URUPQQ06#FS08#FS09#F$03#URS9EQEPQ%UFRF%67RQPQPPPTPOPQPC%47RQPQPRPOPQPR%37RQPQPRPOPQPR%27RQPQPVPOPQ%87RQPQPGPOPQPGFLF5F5F5GJFMDKGHGIP2%D6RQ17QI5ZC%k9RQ9~1H%@9RV17VJ'X11VK%?9RVPVPI%;9RTPMPTPM%:9RTP9POPTPN%69RTAYTPVRVPTPCPN%49RE11ERRLPEPRPN%39RD11DRRWPDPRPN%29RX&0JQ-0IXRQPN%89RYPYPGPYPGPVPEPLPTPVPDPWPTPVPXPQPTPLPDPWPEPLPXPQPEPWPXPQPDPXD=D0D0D0D0FCGGE<E<GVD_I00DfP0%k8RX9~1H%@8RDPDPJPDPK%?8RDPDPI%;8RQPMPQPM%:8RQP8POPQPN%68RQAYQPDRDPQPCPN%48RW11WRREPWPRPN%38RL11LRRTPLPRPN%28RV&0JX-0IVRXPN%88RYPYPGPYPGPDPWPEPQPDPLPTPQPDPVPXPQPEPLPTPWPEPVPXPWPTPVPXPLPVD=D0D0D0D0FCGGE<E<GVD_GHH0HPC%D:RVPVPI%@:RLPLPJPLPK%?:RLPLPI%;:RXPMPXPM%::RT%B:RWPOPTPXPUPWAEWXSPWPF%6:RWPWPPPLPOPWPC%4:RWPWPRPOPWPR%3:RWPWPRPOPWPR%2:RWPWPVPOPW%8:RWPWPGPOPWPGFLF5F5F5GJFMDKGHGIP2f8RW#k9~1Hf9RH#@RVPVPJPVPK%?HRVPVPI%;HRLPMPLPM%:HRLPHPOPLPN%6HRLAYLPVRVPLPCPN%4HRX11XRRTPXPRPN%3HRE11ERRQPEPRPN%2HRD1>DHRYPN%8HRZPZPGPZPGPVPXPTPLPVPEPQPLPVPDPYPLPTPEPQPXPTPDPYPXPQPDPYPEPDD=D0D0D0D0FCGGE<E<GVD_GHH0HP0f:RD#@RE17EJ'XPEPK%?DREPEPI%;DRYPMPYPM%:DRYPDPOPYPN%6DRYAYYPEREPYPCPN%4DRQ11QRRXPQPRPN%3DRT11TRRLPTPRPN%2DRV1>VDRZPN%8DR[P[PGP[PGPEPQPXPYPEPTPLPYPEPVPZPYPXPTPLPQPXPVPZPQPLPVPZPTPVD=D0D0D0D0FCGGE<E<GVD_GHPCf;RV#DRTPTPI%@VRZPZPJPZPK%?VRZPZPI%;VRLPMPLPM%:VRQ%BVRXPOPQPLPUPXAEXLSPXPF%6VRXPXPPPZPOPXPC%4VRXPXPRPOPXPR%3VRXPXPRPOPXPR%2VRXPXPTPOPX%8VRXPXPGPOPXPGFLF5F5F5GJFMDKGHGIP2f<RX#@RT17TJ'Xf=RT#@PK%?TRZPZPI%;TRLPMPLPM%:TRLPTPOPLPN%6TRLAYLPZRZPLPCPN%4TRQ11QRRYPQPRPN%3TRE11ERR[PEPRPN%2TR\1>\TR]PN%8TR^P^PGP^PGPZPQPYPLPZPEP[PLPZP\P]PLPYPEP[PQPYP\P]PQP[P\P]PEP\D=D0D0D0D0FCGGE<E<GVD_GHP0f>R\#@%?\RE7NKPEPI%;\R]PMP]PM%:\R]P\POP]PN%6\R]AY]PEREP]PCPN%4\R[11[RRQP[PRPN%3\RY11YRRLPYPRPN%2\RZ1>Z\R^PN%8\R_P_PGP_PGPEP[PQP]PEPYPLP]PEPZP^P]PQPYPLP[PQPZP^P[PLPZP^PYPZD=D0D0D0D0FCGGE<E<GVD_I00PCf?RZ#DRYPYPI%@ZR^P^PJP^PK%?ZR^P^PI%;ZRLPMPLPM%:ZR[%BZRQPOP[PLPUPQAEQLSPQPF%6ZRQPQPPP^POPQPC%4ZRQPQPRPOPQPR%3ZRQPQPRPOPQPR%2ZRQPQPYPOPQ%8ZRQPQPGPOPQPGFLF5F5F5GJFMDKGHGIP2f@RQ#@%?Q7NKfARY#?R^PI%;YRLPMPLPM%:YRLPYPOPLPN%6YRLAYLP^R^PLPCPN%4YR[11[RR]P[PRPN%3YRE11ERR_PEPRPN%2YR`1>`YRaPN%8YRbPbPGPbPGP^P[P]PLP^PEP_PLP^P`PaPLP]PEP_P[P]P`PaP[P_P`PaPEP`D=D0D0D0D0FCGGE<E<GVD_I00P0fBR`#?RE/7I%;`RaPaPM%:`RaP`POPaPN%6`RaAYaPEREPaPCPN%4`R_11_RR[P_PRPN%3`R]11]RRLP]PRPN%2`R^1>^`RbPN%8`RcPcPGPcPGPEP_P[PaPEP]PLPaPEP^PbPaP[P]PLP_P[P^PbP_PLP^PbP]P^D=D0D0D0D0FCGGE<E<GVD_804MPCfCR^#DR]P]PI%@^RbPbPJPbPK%?^RbPbPI%;^RLPMPLPM%:^R_%B^R[POP_PLPUP[AE[LSP[PF%6^R[P[PPPbPOP[PC%4^R[P[PRPOP[PR%3^R[P[PRPOP[PR%2^R[P[P]POP[%8^R[P[PGPOP[PGFLF5F5F5GJFMDKGHGIP2fDR[#?/7IfER]#;RbPbPM%:]RbP]POPbPN%6]RbAAbP]RLPbPCPN%4]R_11_RRaP_PRPN%3]RE11ERRcPEPRPN%2]Rd1>d]RePN%8]RfPfPGPfPGPLP_PaPbPLPEPcPbPLPdPePbPaPEPcP_PaPdPeP_PcPdPePEPdD=D0D0D0D0FCGGE<E<GVD_804MP0fFRd#;RE/WMPEPM%:dREPdPOPEPN%6dREAAEPdRePEPCPN%4dRc11cRR_PcPRPN%3dRa11aRRbPaPRPN%2dRL1>LdRfPN%8dRgPgPGPgPGPePcP_PEPePaPbPEPePLPfPEP_PaPbPcP_PLPfPcPbPLPfPaPLD=D0D0D0D0FCGGE<E<GVD_PCfGRL#DRaPaPI%@LRfPfPJPfPK%?LRfPfPI%;LRbPMPbPM%:LRc%BLR_POPcPbPUP_AE_bSP_PF%6LR_P_PPPfPOP_PC%4LR_P_PRPOP_PR%3LR_P_PRPOP_PR%2LR_P_PaPOP_%8LR_P_PGPOP_PGFLF5F5F5GJFMDKGHGIP2fHR_#;/WMfIRa#;PM%:aRfPaPOPfPN%6aRfAAfPaRbPfPCPN%4aRc11cRREPcPRPN%3aRe11eRRgPePRPN%2aRh1>haRiPN%8aRjPjPGPjPGPbPcPEPfPbPePgPfPbPhPiPfPEPePgPcPEPhPiPcPgPhPiPePhD=D0D0D0D0FCGGE<E<GVD_P0fJRh#;00GM%:hRePhPOPePN%6hReAAePhRiPePCPN%4hRg11gRRc1OgRPN%3hRE11ERRfPEPRPN%2hRb1>bhRjPN%8hRkPkPGPkPGPiPgPcPePiPEPfPePiPbPjPePcPEPfPgPcPbPjPgPfPbPjPEPbD=D0D0D0D0FCGGE<FxL0FPCfKRb#DREPEPI%@bRjPjPJPjPK%?bRjPjPI%;bRfPMPfPM%:bRg%BbRcPOPgPfPUPcAEcfSPcPF%6bRcPcPPPjPOPcPC%4bRcPcPRPOPcPR%3bRcPcPRPOPcPR%2bRcPcPEPOPc%8bRcPcPGPOPcPGFLF5F5F5GJFMDKGHGIP2fLRc#;00GMfMRE#:RjPEPOPjPN%6ERjAAjPERfPjPCPN%4ERg11gRRe1OgRPN%3ERi11iRRkPiPRPN%2ERl1>lERmPN%8ERnPnPGPnPGPfPgPePjPfPiPkPjPfPlPmPjPePiPkPgPePlPmPgPkPlPmPiPlD=D0D0D0D0FCGGE<FxL0FP0fNRl#:Ri%Bl+0EPOPiPN%6lRiAAiPlRmPiPCPN%4lRk11kRRgPkPRPN%3lRe11eRRjPePRPN%2lRf1>flRnPN%8lRoPoPGPoPGPmPkPgPiPmPePjPiPmPfPnPiPgPePjPkPgPfPnPkPjPfPnPePfD=D0D0D0D0FCGGE<E<GVPCfORf#DRePePI%@fRnPnPJPnPK%?fRnPnPI%;fRjPMPjPM%:fRk%BfRgPOPkPjPUPgAEgjSPgPF%6fRgPgPPPnPOPgPC%4fRgPgPRPOPgPR%3fRgPgPRPOPgPR%2fRgPgPePOPg%8fRgPgPGPOPgPGFLF5F5F5GJFMDKGHGIP2fPRg#:%Bg+0EPOfQRe#:PN%6eRnAAnPeRjPnPCPN%4eRk11kRRiPkPRPN%3eRm11mRRoPmPRPN%2eRp1>peRqPN%8eRrPrPGPrPGPjPkPiPnPjPmPoPnPjPpPqPnPiPmPoPkPiPpPqPkPoPpPqPmPpD=D0D0D0D0FCGGE<E<GVP0fRRp#:,7OPN%6pRmAAmPpRqPmPCPN%4pRo11oRRkPoPRPN%3pRi11iRRnPiPRPN%2pRj1>jpRrPN%8pRsPsPGPsPGPqPoPkPmPqPiPnPmPqPjPrPmPkPiPnPoPkPjPrPoPnPjPrPiPjD=D0D0D0D0FCGGE<E<E<PCfSRj#DRiPiPI%@jRrPrPJPrPK%?jRrPrPI%;jRnPMPnPM%:jRo%BjRkPOPoPnPUPkAEknSPkPF%6jRkPkPPPrPOPkPC%4jRkPkPRPOPkPR%3jRkPkPRPOPkPR%2jRkPkPiPOPk%8jRkPkPGPOPkPGFLF5F5F5GJFMDKGHGIP2fTRk#:,7OPNfURi#6RrAArPiRnPrPCPN%4iRo11oRRmPoPRPN%3iRq11qRRsPqPRPN%2iRt1>tiRuPN%8iRvPvPGPvPGPnPoPmPrPnPqPsPrPnPtPuPrPmPqPsPoPmPtPuPoPsPtPuPqPtD=D0D0D0D0FCGGE<E<E<P0fVRt#6RqAAqPtRu5\NPqPCPN%4tRs11sRRo1OsRPN%3tRm11mRRrPmPRPN%2tRn1>ntRvPN%8tRwPwPGPwPGPuPsPoPqPuPmPrPqPuPnPvPqPoPmPrPsPoPnPvPsPrPnPvPmPnD=D0D0D0D0FCGGE<FxPCfWRn#DRmPmPI%@nRvPvPJPvPK%?nRvPvPI%;nRrPMPrPM%:nRs%BnRoPOPsPrPUPoAEorSPoPF%6nRoPoPPPvPOPoPC%4nRoPoPRPOPoPR%3nRoPoPRPOPoPR%2nRoPoPmPOPo%8nRoPoPGPOPoPGFLF5F5F5GJFMDKGHGIP2PNfXRo#6RmPm&0:o-0DPCufYRo#6RmPCPN%4oRv11vRRr1OvRPN%3oRs11sRRqPsPRPN%2oRu1>uoRwPN%8oRxPxPGPxPGAAmPoRxPvPrPmPxPsPqPmPxPuPwPmPrPsPqPvPrPuPwPvPqPuPwPsPuD=D0D0D0D0FCGGE<FxP0fZRu#6Rs/WCPN%4uRw11wRRqPwPRPN%3uRv11vRRrPvPRPN%2uRm1>muRxPN%8uRyPyPGPyPGAAsPuRuPwPqPsPuPvPrPsPuPmPxPsPqPvPrPwPqPmPxPwPrPmPxPvPmD=D0D0D0D0FCGGE<E<PCf[Rm#DRvPvPI%@mRxPxPJPxPK%?mRxPxPI%;mRrPMPrPM%:mRw%BmRqPOPwPrPUPqAEqrSPqPF%6mRqPqPPPxPOPqPC%4mRqPqPRPOPqPR%3mRqPqPRPOPqPR%2mRqPqPvPOPq%8mRmPmPGPOPmPGFLF5F5F5GJFMDKGHGIP2f\#6/WCPNf]Rm#4Rq11qRRvPqPRPN%3mRx11xRRrPxPRPN%2mRw1>wmRsPN%8mRuPuPGPuPG%6mRu?APmRmPqPvPuPmPxPrPuPmPwPsPuPvPxPrPqPvPwPsPqPrPwPsPxPwD=D0D0D0D0FCGGE<E<P0f^Rw#4Rx11xRRs5\NPxPRPN%3wRr11rRRq1OrRPN%2wRv1>vwRuPN%8wRmPmPGPmPG%6wRm?APwRwPxPsPmPwPrPqPmPwPvPuPmPsPrPqPxPsPvPuPxPqPvPuPrPvD=D0D0D0D0FCGGFxPCf_Rv#DRrPrPI%@vRuPuPJPuPK%?vRuPuPI%;vRqPMPqPM%:vRx%BvRsPOPxPqPUPsAEsqSPsPF%6vRsPsPPPuPOPsPC%4vRsPsPRPOPsPR%3vRsPsPRPOPsPR%2vRsPsPrPOPs%8vRvPvPGPOPvPGFLF5F5F5GJFMDKGHGIP2PNf`S0:#4RvPvPRCufaRv#4RsPRPN%3vRr11rRRu1OrRPN%2vRq1>qvRxPN%8vRmPmPGPmPG%6vRm?APvRvPs11sRRwPmPvPrPuPmPvPqPxPmPwPrPuPsPwPqPxPsPuPqPxPrPqD=D0D0D0D0FCGGFxP0fbRq#4Rr/WRPN%3qRx11xRRuPxPRPN%2qRs1>sqRwPN%8qRmPmPGPmPG%6qRm?APqRqPr11rRRvPmPqPxPuPmPqPsPwPmPvPxPuPrPvPsPwPrPuPsPwPxPsD=D0D0D0D0FCGGE<PCfcRs#DRxPxPI%@sRwPwPJPwPK%?sRwPwPI%;sRuPMPuPM%:sRr%BsRvPOPrPuPUPvAEvuSPvPF%6sRvPvPPPwPOPvPC%4sRvPvPRPOPvPR%3sRvPvPRPOPvPR%2sRvPvPxPOPv%8sRvPvPGPOPvPGFLF5F5F5GJFMDKGHGIP2fd#4/WRPNfeRv#3Rx11xRRwPxPRPN%2vRu1>uvRrPN%8vRmPmPGPmPG%6vRm?APvRq%4vRv11vRRyPmPqPxPwPmPqPuPrPmPyPxPwPvPyPuPrPvPwPuPrPxPuD=D0D0D0D0FCGGE<P0ffRu#3Rx11xRRr5\NPN%2uRw1>wuRvPN%8uRyPyPGPyPG%6uRy?APuRm%4uRu11uRRqPyPmPxPrPyPmPwPvPyPqPxPrPuPqPwPvPuPrPwPvPxPwD=D0D0D0D0FCGG:04xRPCfgRx#DRwPwPI%@xRvPvPJPvPK%?xRvPvPI%;xRrPMPrPM%:xRu%BxRqPOPuPrPUPqAEqrSPqPF%6xRqPqPPPvPOPqPC%4xRqPqPRPOPqPR%3xRqPqPRPOPqPR%2xRqPqPwPOPq%8xRqPqPGPOPqPGFLF5F5F5GJFMDKGHGIP2PNfh#3RqPqPRCufiRq#3RwPN%2qRv1>vqRrPN%8qRuPuPGPuPG%6qRu?APqRy%4qRq11qRRmPuPyPw11wRRzPuPyPvPrPuPmPwPzPqPmPvPrPqPzPvPrPwPvD=D0D0D0D0FCGG804RP0fjRv#3Rw/WRPN%2vRr1>rvRzPN%8vRqPqPGPqPG%6vRq?APvRm%4vRv11vRRuPqPmPw11wRRyPqPmPrPzPqPuPwPyPvPuPrPzPvPyPrPzPwPrD=D0D0D0D0FCGGPCfkRr#DRwPwPI%@rRzPzPJPzPK%?rRzPzPI%;rRyPMPyPM%:rRv%BrRuPOPvPyPUPuAEuySPuPF%6rRuPuPPPzPOPuPC%4rRuPuPRPOPuPR%3rRuPuPRPOPuPR%2rRuPuPwPOPu%8rRuPuPGPOPuPGFLF5F5F5GJFMDKGHGIP2fl#3/WRPNfmRu#2Rw1>wuRzPN%8uRyPyPGPyPG%6uRy?APuRv%4uRq11qRRmPyPv%3uRu11uRR{PyPvPwPzPyPmPuP{PqPmPwPzPqP{PwPzPuPwD=D0D0D0D0FCGGP0fnRw#2Ru1>uwRz5\NPN%8wR{P{PGP{PG%6wR{?APwRq%4wRm11mRRyP{Pq%3wRv11vRR|P{PqPuPzP{PyPvP|PmPyPuPzPmP|PuPzPvPuD=D0D0D0D0FCI0CPCfoRu#DRvPvPI%@uRzPzPJPzPK%?uRzPzPI%;uR|PMP|PM%:uRm%BuRyPOPmP|PUPyAEy|SPyPF%6uRyPyPPPzPOPyPC%4uRyPyPRPOPyPR%3uRyPyPRPOPyPR%2uRyPyPvPOPy%8uRuPuPGPOPuPGFLF5F5F5GJFMDKGHGIP2PNfpRu#2RyPy%DuCuPNfqRu#8RyPyPGPyPG%6uRy?APuRv%4uRz11zRR|PyPv%3uRm11mRR{PyPv%2uRv1>vuRuPyP|PmP{PzP|PvPuPzP{PvPuPmPvD=D0D0D0D0FCI0CP0PNfrRv#8RmPmPGCuPmPG%6vRm?APvRu%4vR{11{RRzPmPu%3vR|11|RRyPmPu%2vRu1>uvRvPmPzP|PyP{PzPuPvP{PyPuPvP|PuD=D0D0D0D0FCPCfsRu#DR|P|PI%@uRvPvPJPvPK%?uRvPvPI%;uRyPMPyPM%:uR{%BuRzPOP{PyPUPzAEzySPzPF%6uRzPzPPPvPOPzPC%4uRzPzPRPOPzPR%3uRzPzPRPOPzPR%2uRzPzP|POPz%8uRzPzPGPOPzPGFLF5F5F5GJFMDKGHGIP2PNft#8RzPzPGCufuRz#8PG%6zR|?APzRv%4zRy11yRR{P|Pv%3zRm11mRRqP|Pv%2zRv1>vzRzP|P{PmPqPyP{PvPzPyPqPvPzPmPvD=D0D0D0D0FCP0fvRv#8/WG%6vRm?APvRz%4vRq11qRRyPmPz%3vR{11{RR|PmPz%2vRz1>zvRvPmPyP{P|PqPyPzPvPqP|PzPvP{PzD=D0D0D0D0D0PCfwRz#DR{P{PI%@zRvPvPJPvPK%?zRvPvPI%;zR|PMP|PM%:zRq%BzRyPOPqP|PUPyAEy|SPyPF%6zRyPyPPPvPOPyPC%4zRyPyPRPOPyPR%3zRyPyPRPOPyPR%2zRyPyP{POPy%8zRzPzPGPOPzPGFLF5F5F5GJFMDKGHGIP2fx#8/WGfyRz#6Ry?APzR{%4zRv11vRR|PyP{%3zRq11qRRmPyP{%2zR{1>{zR}PyP|PqPmPvP|P{P}PvPmP{P}PqP{D=D0D0D0D0D0P0fzR{#6Rq?AP{R}%4{Rm11mRRv/7q3[P}%3{R|11|RRyPqP}%2{R}1>}{R{PqPvP|PyPmPvP}P{PmPyP}P{P|P}D=D0D0D0D0PCf{R}#DR|P|PI%@}R{P{PJP{PK%?}R{P{PI%;}RyPMPyPM%:}Rm%B}RvPOPmPyPUPvAEvySPvPF%6}RvPvPPP{POPvPC%4}RvPvPRPOPvPR%3}RvPvPRPOPvPR%2}RvPvP|POPv%8}RvPvPGPOPvPGFLF5F5F5GJFMDKGHGIP2f|Rv#6R|?APv%4vRvANvR|3[f}Rv#6R|?APvR{%3vRy11yRRmP|P{%2vR{1>{vRqP|%4vRv/1RR|PyPmPvP|P{PqPvPmP{PqPyP{D=D0D0D0D0P0f~R{#6Ry?AP{Rq%3{Rm11mRRv/7y3[Pq%2{Rq1>q{R|Py%4{R{/1RRyPmPvP{PyPqP|P{PvPqP|PmPqD=D0D0D0PCp+01@Rq#DRmPmPI%@qR|P|PJP|PK%?qR|P|PI%;qRvPMPvPM%:qR{%BqRyPOP{PvPUPyAEyvSPyPF%6qRyPyPPP|POPyPC%4qRyPyPRPOPyPR%3qRyPyPRPOPyPR%2qRyPyPmPOPy%8qRyPyPGPOPyPGFLF5F5F5GJFMDKGHGIP2p+01ARy#6Rm?APy%3yRyANyRm3[p+01BRy#6Rm&0:y-0DP%2yR|3N1>|yRvPm%4yRm/1RR{%3yRy11yRR~PmP{P|PvPmP~P|PvPyP|D=D0D0H02P0p+01CR|#6Ry?AP|%2|Rv1>v|R~/7y3[%4|Ry/1RRm%3|R|11|RR{PyPmPvP~PyP{PvP~P|PvD=D0D0PCp+01DRv#DR|P|PI%@vR~P~PJP~PK%?vR~P~PI%;vR{PMP{PM%:vRy%BvRmPOPyP{PUPmAEm{SPmPF%6vRmPmPPP~POPmPC%4vRmPmPRPOPmPR%3vRmPmPRPOPmPR%2vRmPmP|POPm%8vRmPmPGPOPmPGFLF5F5F5GJFMDKGHGIP2p+01ERm#6R|?APm%2mR~%Dm=N~|3[p+01FR~#4R|/1RRm%3~R{11{RRyP|Pm%2~Rm1>m~R~P|PyPmP~P{PmD=D0D0P0p+01GRm#4R{/1RR~%3mRy11yRR|/7{3[P~%2mR~1>~mRmP{P|P~PmPyP~D=D0PCp+01HR~#DRyPyPI%@~RmPmPJPmPK%?~RmPmPI%;~R|PMP|PM%:~S0;%B~R{POQ0;P|PUP{AE{|SP{PF%6~R{P{PPPmPOP{PC%4~R{P{PRPOP{PR%3~R{P{PRPOP{PR%2~R{P{PyPOP{%8~R{P{PGPOP{PGFLF5F5F5GJFMDKGHGIP2p+01IR{#4Ry/1R%3{R{AN{Ry3[p+01JR{#4Ry%2{Rm7NR1>m{R|Py%3{R{?NRmP|P{%`mH02H02P0p+01KRm#4R{/1R%2mR|1>|mRy/7{3[%3mRm?NR|PyPm%`|H02PCp+01LR|#DS0;Q0;PI%@|RmPmPJPmPK%?|RmPmPI%;|RyPMPyPM%:|S0<%B|R{POQ0<PyPUP{AE{ySP{PF%6|R{P{PPPmPOP{PC%4|R{P{PRPOP{PR%3|R{P{PRPOP{PR%2|R{P{Q0;POP{%8|R{P{PGPOP{PGFLF5F5F5GJFMDKGHGIP2p+01MR{#4Rm/1R%2{Ry%D{=Nym3[p+01NRy#3Rm%2yR{7NR%Dy=N{m<0`{P0p+01OR{#3Rm/1R%2{Ry%D{=Nym3[%`yPCp+01PRy#DS0;Q0;PI%@yRmPmPJPmPK%?yS0<Q0<PI%;yRmPMPmPM%:yS0=%ByR{POQ0=PmPUP{AE{mSP{PF%6yR{P{PPQ0<POP{PC%4yR{P{PRPOP{PR%3yR{P{PRPOP{PR%2yR{P{Q0;POP{%8yR{P{PGPOP{PGFLF5F5F5GJFMDKGHGIP2p+01QR{#3S0;/1R%2{Rm%D{Q0;5Nm3[p+01R#2#`p+01SRm00_z%;mRzPU%BmRmAEmzS1WmFI0BP0p+01TR0#;Rm/bU%B0RzAEzmS3Z1WzFPCp+01URz#DS0;Q0;PI%@zRmPmPJPmPK%?zS0<Q0<PI%;zRmPMPmPM%:zS0=%BzR{POQ0=PmPUP{AE{mSP{PF%6zR{P{PPQ0<POP{PC%4zR{P{PRPOP{PR%3zR{P{PRPOP{PR%2zR{P{Q0;POP{%8zRzPzPGPOPzPGFLF5F5F5GJFMDKGHGIP2p+01VRz#;R{/bU%BzRzAEz{S3Zp+01W#B/WFPNp+01XRz#6R{AA{PzRzPwC}Q07$09#U-0^PRw9NzC9ZzO,X{,|{PNp+01Y#4R{11{RRzPxC}ANzCw9ZzO,X{,|{PNp+01Z#3R{11{RRzQ0:C}ANzCw9ZzO,X{,|{PNp+01[R{#2Rz1>z{R{PoC}AN{Cw9Z{O,Xz,|zPNp+01\S0:#8Rz11zGR{PtC}AN{Cw9Z{O,Xz,|z&0]NQ05#Q$09#tRN#F#t#t#F$03#z#v#v#U%QN#t#t#F$03#z#v#v#U,7O7ZOp+01^$0\RN$0A%dN#`p+01_$0:RN$0A%dN#`p-0RN&0[=-0Z1Rzg00TCR{#r#^#^#^S05#^#^#^S0;#r#^Ro#r#^Rx#^#^#^Rm#q'w20@1{R{'p#m%qx,wz/p{#m%qo,wz/p{#mQ0;#q,wz/p{#m%rm#^#q,wz/p{#mQ05#q,wz/p{#mQ00$0Y'o'o'o'o'o'oQ00$0X%gQ&0W1RQ7]W%g[?]XQ7]6%g`?]DQ%g\7]87]3%gY?]HQ%gT7]9%g^?]VQ%gZ7]:7]77]4&0V1&0U1R7Q07#R20?15RQ'n,l7S07&0T>R>P7Q06#RRV%aU6081%RBR\5P7%aS:081V9P7\5i7S06P>P7Q09#R/nQ,l7S09P>P7P7%Q=#F#z$09#F#Q#z#v#UR{#aRz%QARm#Q#RRo5P7S00P71e7d%aG,joQ08#RRo5P7S081e7L5i7DSP>P7P7%Fm#RRx9P7zS05P7AP7QxS0;20>1=R=,jx=P7oS0<1e7_5i7DSP>P7%QB#R/nQ,l7S0=P>P7P7Q01#RRB9P7zS01P71e7a%aRRx,jB=P7oS0>1e7h5i7DSP>P7Q04#R/nQ,l7S04P>P7P7Q03#F#RRB9P7zS0?P71e7b1jBx=P7oS0@1e7c5i7DSP>P7Q02#FRB#Q#R/nQ,l7S0AP>P7P7%FB#RRx9P7zS0BP71e7E%aPQ02#RRz60R1,jx=P7oS021e7l5i7DSP>P7Q03#RRx9P7oRoP>P7%Rm:081\9P7xRxP>P7P1%aM,jVg00Pb%RBH07,l7RBP>P7%RA/nQ,l7RAP>P7%aIRV9P7zR\P>P7%R@R@%aK'j=P7zRzP>P7AP7Q@%aJ9P7@5i7R@P>P7%aC=P7=AP7=V5i7RVP>P7PVP7P@P7PzP7P\P7PAP7PBP7PxP7PoP7Q06P7Q07P7Q0BP7Q02P7Q0AP7Q0?P7Q0@P7Q04P7Q01P7Q0>P7Q0=P7Q05P7Q0<P7Q0;P7Q00P7Q08Q09DSDSDSDSDSDSDSDSDSDSDSDSH0QFcFcFcFcFcFcFcFcFc20P7?P2P3g00UNR7g00UnR?+0O20N23=T7?dB0S154H0MblbmbnX?1XJ1XL1XM1XN1XO1XP1XQ1XR1X@1XA1XB1XC1XD1XE1XF1XG1XH1XI1XK1X6NX7NX8NX9NX:NX;NX<NX=NW>&01D1b9UAEW9S7ZW&01]R517{]R?PL11]GPXP_DfP?%`]11]6PTPhDfP?PE11]RRTPZPlDfP?PePTPYPpDfP?PiAY]PXP^PtDf17[YAE`^[11YM/y`&01Y17YIANYK`17`J,X`17`I9ZC`PCP^P^PIP[P[PJP[PKP]P]PIPd11LM/y_AEahbPcPaPLPUPhAEhLSP{PlAYlP]PcP{Pg11gRPcP{Pp11pRPcP{Pk11k^PcP{Pi11iGPc&01tD{,XkD{-06jD{-06eD{-06fD{-06EI0BDfK0jGI[[[[[[[[[\5[\5[\5[[[[[^?1^J1^L1^M1^N1^O1^P1^Q1^R1^@1^A1^B1^C1^D1^E1^F1^G1^H1^I1^K1^6N^7N^8N^9N^:N^;N^<N^=N^>NP2p+01aRN#6R1%?NR57YP?NCw%`1%4NRE/1R?NCw%`E%3NRf/1R?NCw%`f%2NRe%DNRj'1?NCw%8NRk/1G?NCw%`k1OkGPkPe1OfRPf1OERPE1O1CP1%BNR1/OFPOP<P1%:NP;%;NR;1O;MP5%@NPjPHPDPnP6P9PsP8PrP:PuPWP}PqPvP~P|PyP0Q0:O`bkbqbpb0PCp+01]R0#DRyPyPI%@0R|P|PJP|PK%?0RKPKPI%;0RIPMPIPM%:0RM%B0R|POPMPIPUP|AE|ISP|PF%60RFPFPPPKPOPFPC%40RCPCPRPOPCPR%30RCPCPRPOPCPR%20RRPRPyPOPR%80R0P0PGPOP0PGFLF5F5F5GJFMDKGHGIeb2b1b5b3b4WbWaP4P2O2n2001000010121000000b0WSWjP4P2O2n2001000010121000000W0WiP4P2O2n2001000010121000000W0WhP4P2O2n2001000010121000000W0WgP4P2O2n2001000010121000000W0WfP4P2O2n2001000010121000000W0WeP4P2O2n2001000010121000000W0WUP4P2O2n2001000010121000000W0W2P4P2O2n2001000010121000000W0W1P4P2O2n2011000010121000000W0WdP4P2O2n2011000010121000000W0W5P4P2O2n2011000010121000000W0W]P4P2O2n2011000010121000000W0W3P4P2O2n2011000010121000000W0W^P4P2O2n2011000010121000000W0W4P4P2O2n2011000010121000000W0W\P4P2O2n2011000010121000000W0W[P4P2O2n2011000010121000000W0WcP4P2O2n2011000010121000000W0W`P4P2O2n2011000010121000000W0WZP4P2O2n2011000010121000000W0WYP4P2O2n2011000010121000000W0WXP4P2O2n2011000010121000000W0WVP4P2O2n2011000010121000000W0WWP4P2O2n2011000010121000000b0W_WTo"). Qed.

(* [comment removed for export] *)
Lemma acc_shadowA : forall RNG A len a, rng RNG (shad A) (nshad len) -> A mod 8 = 0 -> (0 <= A /\ A <= a /\ a < A + len /\ A + len + 8 <= 2^47) ->
  acc_in RNG (Z_to_bv 64 (Z.shiftr a 3 + 2147450880), 1%nat).
Proof.
  intros RNG A len a (H0 & H1 & H) A8 (HA & Ha1 & Ha2 & HL). unfold acc_in. cbn [fst snd].
  rewrite shad_div, nshad_div in *. unfold ASHOFF in *. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  rewrite unsigned_lit by (Z.div_mod_to_equations; lia).
  apply H; Z.div_mod_to_equations; lia.
Qed.
Lemma acc_shadow1 : forall RNG A a, rng RNG (shad A) 1 -> (0 <= A /\ A <= a /\ a < A - A mod 8 + 8 /\ A + 8 <= 2^47) ->
  acc_in RNG (Z_to_bv 64 (Z.shiftr a 3 + 2147450880), 1%nat).
Proof.
  intros RNG A a (H0 & H1 & H) (HA & Ha1 & Ha2 & HL). unfold acc_in. cbn [fst snd].
  rewrite shad_div in *. unfold ASHOFF in *. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  rewrite unsigned_lit by (Z.div_mod_to_equations; lia).
  apply H; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma acc_shadowU : forall RNG A len a, rng RNG (shad A) (nshad (len + A mod 8)) ->
  (0 <= A /\ A <= a /\ a < A + len /\ A + len + 8 <= 2^47) ->
  acc_in RNG (Z_to_bv 64 (Z.shiftr a 3 + 2147450880), 1%nat).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_fse_rd_base ()) ["CANSEC1"] "h02H2h11bh21jh31zh44__x1h54__x2h64__x3h74__x4h84__x5h92Hah:7__arithh;4__ffh<4__p1h=4__p2h>8__varmaph?5__with@4__x6hA1HhB2H1hC3H10hD3H11hE3H12hF3H13hG3H14hH3H15hI3H16hJ2H3hK2H4hL2H5hM2H6hN2H7hO2H8hP2H9hQ7__sat17hR7__sat18hS7__sat19hT7__sat20hU1qhV2q0hW2q1hX1rhY2r0hZ2r1h[2H0h\4__x7h]4__x8h^4__x9h_1Ah`2HAha2HLhb3Ha1hc3Ha2hd3RNGhe1ahf3lenp%0p&0p;1p;2p;3p;6p;4p;7p;8g00nOj18Tg001ij1ETg002Nj1BTg002lj22Tg01B^k30NTg00i5j2lTg007bj21Tg011Mk103Tg006Bj20Tg008>R0j2NTg007Fj24Tg003Lj1DTg00Vkj1xTg00WIk10@Tg01CQj2LTg00;Kj1JTg01D1j2TTg01Ahj1eTg005Hj23Tg019aj1qTg01Dgj6_Tg01ECj1yTg01F=j2cTg004Nj2PTg004ok100Tg006_j2[Tg008Yj2ZTg009@j2XTg009fj2QTg011mj2~Tg012Uj3}Tg00:Lk10MTg00:jk20LTg00;jj3|Tg0139k20KTg00<Sj2{Tg0180k30JTg00=<j2gTg00>Tk10GTg00?4j3fTg00?Tk10FTg013bk10ETg00A0k10DTg00ANk10CTg00B9j2wTg00B\k10?Tg00KTk60>Tg00Caj3pTg00C>j2uTg00EJk20=Tg00Elk20<Tg00FFk20;Tg00G2j3\Tg00GLk30:Tg00Gkk409Tg005ej2sTg01Fgj2tTg01GMj3rTg01H0k207Tg000Mj6vTg01Hlk306Tg01IUk305Tg01J2k30ATg017Pk404Tg00I\j3mTg00@4k20BTg00@Rk402Tg00JEj4nTg00K0j7zTg018Yk601Tg00L\k70HTg00DDk30ITg00L8j8`Tf1R1f0R2'0#ep=ag00M^R3/12p=7%E2#Ep=Af2R4/01/12p=51212,04p=b%e2,01p=h%D2#Dp=O1N12,N4p=]1131/N2p=:1012,t4p=IP4g01JOR5P1P2H04p=R1441/N2p=@g01<S/02p=?1041/02p=6g00M@R6?\23p=Kf3R71s41/025\6p=>1123p=YA\612p=C1{62p=MAm612p=oAm6129m64p=^20B62p=FP6P4P1P2H02p=;1w62p=VP6P1g00PbP2Cnp=SP1g00NcR8g00OBR9P9g00ObR:P2g00PBR;Fzp=<P1P8P9P9P:P2J01p=d1u62p=HP4P8P9P9P:P1P2K0Hp=UP6P1g00N<P2Cnp=WB0I612p=9P4P8P9P9P:P6P1g00QIP2CnP;Fzp=GP7P8P9P9P:P4P1P2G`p=if6R;P8P9P9P:f5R<P8P9P9P:f4R=P7P4G`P1P2G`p==1412,N4p=j10129\64p>08P;P8P9P9P:P<P=P7P8P9P9P:P4P1P2G`G`p=kg01Jn%84g00S2R>#ER?#ER@#ERA#BRB,24,a160N7P0%87RC#7127B,a4%B?RD%EA#ARE#BRF'lRG55C%8<RC/11&031,04RH%8;Ab<;B'hRI'1f8RJP7P4O2[[^25^16'N11=410=7RK,44%D?RL#D#OS00#BRM,lDRN95KB3],:=%xERE$0@RK%D>RO#BRP,L7%DORQ#D#O#O#O#O#O#O#E#A#A#A#A#A#A#A#BRR5IEg00TCRS#JRT3R,T;[P2%7C11IG%8J/11f9RI#8RCAbJIB'hRU,1Hf;RVP7P4O2[[^25^16'NP0f7RW#812WB,a;;5G11C1f:RC#8AbICB'h,1Hf<RXP7P4O2[[^25^1611J;10JWRY,4;A5YBN3],:J1LWP=IER=RKT,TC[P211UG%8X/11f=RU#8AbXUB'h,1Hf?RYP7P4O2[[^25^1611VI10VCRZ,4IA5ZBN3],:VP0%7XS0111XC10XVRZ,4CA5ZBN3]f>RZ1LVP=IER=RKT'TP2%7Z11YU10YZR[,4UA5[BN3]P0f@R[/1Z10[YR\A5\BN5@ZfBR\1LYP=IER=RKT'TP211\[fAS02fCR[/0\R]A5]BN3@P0fDR0/0[R],4\A5]BNfFR]1L[P=IER=RKT'TP2fE,0],40fG/0]?5BNP6fHR^#81141fKR_fLR`/2BS03'0Ra#eRb,07,1HfNRcP7P4O2[[^25^16X36PU13^B#?%q^E_fJRd/3B#?Re/1113_BRf#?Abd_BRg#eRh'0,1HfMRiP7P4O2[[^25^16P6fIRj#812dB,aj=52GX36PY13jB#?RY%qjE_12jB,a^=5YGP6%8d%72X36P0Pe%qdE_%7eP6Ph13cBRh#?Re/11fORd/3BS04#?/07,1HfQRYP7P4O2[[^25^16X36P4%BQRk,0g/3B%ygE_13iB#?Rg/1112cBRl=6ik/3B,0e,1HfPRHP7P4O2[[^25^16P6PbA5g2GX36P410ak/3BRg%yaE_13`BS05#??5gGP61lDP,3_PdAIE2R,cEPTO2X36P610fRRfPdP2PTO2X36P1PfPT1PiB%KBRg$00RaPcPBPhPlC>[1[cB143BRh12dBRb14bB':[1ZdB14B3Rb12HBRe%Ye5@B[1XHB13YB#K\g1QYBfRRm/2B/Cm\g13mBP6fSRn/2BRoP61PmBPnPB13nBPoC>\a1[nBfTRn/2BRo14oB':\h1ZnBfURo/2BS06Q06#Y5@B\b1XoBfVRm/3B#K\g1QmBfWRp/2BRq/Cp\g13pBP6fXRr/2BP6fZRs?6Wk/PBf[S07?6JkRtPB13tB12tBC>\a1[tBf\S08?6IkRt/2BRu14uB':\h1ZtBf]S09?6CkRt/2BRu%Yu5@B\b1XtBf^S0:?6VkRt/3B#K\g1QtBf_S0;?6XkRt/2B/Ct\g13tBP6f`S0<?6Uk/2BP61~DMS0=143DRt%7M143N[[S0>%7DRug01=MRvA}DM1UW9S0?%7N\v^9uS0@1~DFS0A%7F143G[\tS0BA}DF1VvX9uS0C%7G\v^9uS0Dp-0Rug00SWRv%JTRF#JRt#JRM#JS0E#MRw%MMS0F%MtS0G&0M>-0L6S0H%MFS0I5|6%MT20K6B1{6S60J6S0J'oS0K3^3^S0Lg00TbRS'g&0GvRF3f&0FvS0M%F;S0N&0E6Rt7;7?;4t%F=S0O%F<S0P7;;7;1&0D6S0Q&0C6RMPM1w63Rx%VBRy'S,<MRz&0?9R{1dMJ%HARA/Sy,<M5UMP{PMPMPMP8P9P9P:1Wyx,<MJ0>R9P{%HLRL%H?R?9p6y/9AS0R'W,<MP{PMPMPzP{%HQRQ9GMxR81dMI5UMP{PMPMP9P{%H@R|1u6>R}9p6y/9QS0S'W,<MP{PMAGM|LS0TP{%VRR~/9}19?~5GMCiF=F=F=F=20=M:S0UP2P4g00UNS0Vg00UnR:+0<Q0V20;24;\:dB0:631H09S0Vb;b>b?X46X56X66X76X86X@6X<uW=AjW;B\hg00VN\gR3P<PBP7PWC>[1:WC\h1sB=S0W>08;J\311;W10;RR:95R<[[[[[^46^56^66^76^86^@6^<u^=uP214[BS0XQ01PXP[feS01fgS0YPUP0Q02P\P^PjPnO=b:bQbRbSbTbZbWbIbHbGbFbEbYbVbDbCbPbObNbXbUbMbLbKbJb01P_BS02P`PBQ05Q03C>\aS031[`BS0512iBR`14`B':\hS0Z1ZiBS0[%Yl9@Bl\bS0\1XcBS0]Q04#K\gS041QdBS0^1CeH\gS0_13HBS0`P612YBS0aP61PnBS0bPoPB13oBQ06C>\aS061[oBS0c12mBRo14oB':\hS0d1ZmBS0e%Yq9@Bq\bS0f1XpBS0g13rB#K\gS0h1QrBS0ifYRp/2B/Cp\gS0j13pBS0kP612sBS0lP6A6s2k/PBS0mQ07?61kRsPB13sB12sBC>\aS071[sBRsQ08?64kRa/2BRp14pB':\hRp1ZaBRaQ09?67kRq/2BRm%Ym5@B\bRb1XqBRqQ0:?6=kRm/3B#K\gRo1QmBRmQ0;?6<kRY/2B/CY\gRg13YBRYP6Q0<?6;k/2BReP6Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0E#JRl#MRiQ0L'o/gS=fvFQ0M%FJ?;=tQ0N7;4%FI?;<t%FW7;77;1Q0QPMPMPzP{1dMV%D@#HR@/Sy,<M5UMP{PMPMP9P{%EO#HR`/9A%Vk'9%HORO9p6y/9@'W,<MP{PMPMP9P{Q0R,W|,<MP{PMPMPzP{1dMX9UM8P{PMPMP9P{Q0S,WL,<MCiR9P{PM19|`R`,SL,<MRLP{19}~R}%B>R>#V'919~?/9O5GMFkF=F=F=F=Q0UQ0Vb;b>b?X46X56X66X76X86X@6X\6X]6X^6X<uX=uAjCIB\hA6WIkQ0W/0CRk'C\31C;k\31:CZ\hPIPBP<PVC>\310JC,4IA6RWJ95:>[[[[[[^46^56^66^76^86^@6^\6^]6^^6^<u^=uP2Q0X%7<RuP<PXP[ffRXQ01Q0YP;PUP0PCPVP\P^PjPHOAb:bQbRbSbTbZbWbIbHbGbFbEbYbVbDbCbPbObNbXbUbMbLbKbJb0O41tEf,cEQ02Q03Q05Q0ZQ0[Q0\Q0]Q04Q0^Q0_Q0`P6Q0aP6Q0bQ06Q0cQ0dQ0eQ0fQ0gQ0hQ0iQ0jQ0kP6Q0lP6Q0mQ07PsPpPaPbPqPoPmPgPYP6PeP6Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0IQ0K'o9^iw/gS%Jl#MQ0H=|6wQ0FQ0GQ0J3^3^/gS=fvF5fvQ0M%F4Q0O7;<%F7Q0P7;<7;1Q0QPMPMPzP{1SQy,<M9UM8P{PMP9P{PM19`y%VDRDQ00#x5r65GMP{PMPLP{PMQ0TP{PMAGMx|P{AGMx}Ar6DE,S},<M5UMCiFkFkF=Q0UQ0Vb;b>b?X46X56X66X76X86Aju<B\hP=PBP4P;C>\3107<?5BN10=;,4<11<;%7;14:G,::[[[[[[^46^56^66^76^86P2P[PXQ01Q0YP0P^PjPdPHPnPrO;b:bQbRbSbTbZbWbIbHbGbFbEbYbVbDbCbPbObNbXbUbMbLbKbJb0-07fEv1L_PRfPFQ0MPtQ0Q%VP9GMxQ0UQ0Vb;b>b?%7PP2b::06_PEvPcAIEfR,cEPTO2ebBbAb[bBbAPj1L]P=IER=RKTRT:05K5,cEB0AK5TO2e1TjTeWaWcP1P2O2n2001000000121000000W0WbP1P2O2n2001000000121000000W0W`P1P2O2n2001000000121000000W0WAWBP1P2O2n2001000000121000000W0W[P1P2O2n2001000000121000000W0Xe6Xf6X_6Wdo"). Qed.

(* [comment removed for export] *)
Lemma rd_invA_store2 : forall C m1 nc msvw tlw cn v, rd_okA C -> rd_invA C m1 nc msvw tlw -> 0 <= cn < zlen (a_rt0 C) ->
  rd_invA C (write_to_mem m1 (wa (a_NC C + 2 * cn)) (le2 (Z_to_bv 64 v))) (Zupd cn (to_short v) nc) msvw tlw.
Proof.
  intros C m1 nc msvw tlw cn v OK (ARR & LNC & HBUF & HMSV & HTL & (j16 & FR) & ST & MU & WM & MI) Hcn.
  pose proof OK as (HH & FBY & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & BN & N8 & BM & M4 & BT & T4 & BB & BF & F64
                    & SNM & SNT & SNB & SMT & SMB & STB & B8).
  pose proof (spaA_bounds C SP16) as [[SPA1 SPA2] SPA3].
  apply ablk_lin in BN, BM, BT, BB, BF. pose proof atop_range as ATR. unfold AIMG_HI, RDA_CALLEE, FRA_main in *.
  assert (LWS : length (map (Z_to_bv 64) nc) = length (a_rt0 C)) by (rewrite length_map; exact LNC).
  pose proof (u16arr_store_ok asegs _ (a_NC C) _ cn (wa (a_NC C + 2 * cn)) ARR ltac:(rewrite LWS; lia) eq_refl) as SOK.
  pose proof (u16arr_write asegs _ (a_NC C) _ cn (Z_to_bv 64 v) ARR ltac:(rewrite LWS; lia)) as ARR2.
  rewrite u16s_upd_short in ARR2.
  assert (L2 : length (le2 (Z_to_bv 64 v)) = 2%nat) by reflexivity.
  unfold rd_invA. split; [exact ARR2|]. split; [unfold Zupd; rewrite upd_nat_length; exact LNC|].
  split; [apply bytes_at_write_other; [exact HBUF| lia| rewrite L2; lia| rewrite L2, length_map; lia]|].
  split; [apply rw_cells_frame; [exact HMSV| lia| rewrite L2; lia| rewrite L2; cbn; lia]|].
  split; [apply rw_cells_frame; [exact HTL| lia| rewrite L2; lia| rewrite L2; cbn; lia]|].
  split; [exists j16; apply rw_cells_frame; [exact FR| lia| rewrite L2; lia| rewrite L2; cbn; lia]|].
  split; [apply stk_write; [exact ST| lia| rewrite L2; lia]|].
  split; [apply munch_write; [exact MU| lia| rewrite L2; lia| unfold rd_WA; cbn [inside]; rewrite L2; lia]|].
  split; [apply wmono_write; exact WM|].
  apply mem_inv_store; [exact MI| rewrite L2; exact SOK].
Qed.

(* [comment removed for export] *)
Lemma rd_invA_storeM : forall C m1 nc msvw tlw v, rd_okA C -> rd_invA C m1 nc msvw tlw ->
  rd_invA C (write_to_mem m1 (wa (a_MSVP C)) (le4 (Z_to_bv 64 v))) nc (Z_to_bv 64 v) tlw.
Proof.
  intros C m1 nc msvw tlw v OK (ARR & LNC & HBUF & HMSV & HTL & (j16 & FR) & ST & MU & WM & MI).
  pose proof OK as (HH & FBY & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & BN & N8 & BM & M4 & BT & T4 & BB & BF & F64
                    & SNM & SNT & SNB & SMT & SMB & STB & B8).
  pose proof (spaA_bounds C SP16) as [[SPA1 SPA2] SPA3].
  apply ablk_lin in BN, BM, BT, BB, BF. pose proof atop_range as ATR. unfold AIMG_HI, RDA_CALLEE, FRA_main in *.
  assert (L4 : length (le4 (Z_to_bv 64 v)) = 4%nat) by reflexivity.
  pose proof (rw_cells_store_ok asegs m1 (a_MSVP C) [C4 msvw] 0 (C4 msvw) 4 HMSV eq_refl eq_refl) as SOK.
  cbn [Z.of_nat] in SOK. rewrite Z.add_0_r in SOK.
  unfold rd_invA. split; [apply u8arr_frame; [exact ARR| lia| rewrite L4; lia| rewrite L4, u16s_length, length_map; lia]|].
  split; [exact LNC|].
  split; [apply bytes_at_write_other; [exact HBUF| lia| rewrite L4; lia| rewrite L4, length_map; lia]|].
  split.
  { pose proof (rw_cells_write asegs m1 (a_MSVP C) [C4 msvw] 0 (C4 msvw) (C4 (Z_to_bv 64 v)) HMSV eq_refl eq_refl ltac:(cbn; auto)) as W.
    cbn [Z.of_nat] in W. rewrite Z.add_0_r in W. exact W. }
  split; [apply rw_cells_frame; [exact HTL| lia| rewrite L4; lia| rewrite L4; cbn; lia]|].
  split; [exists j16; apply rw_cells_frame; [exact FR| lia| rewrite L4; lia| rewrite L4; cbn; lia]|].
  split; [apply stk_write; [exact ST| lia| rewrite L4; lia]|].
  split; [apply munch_write; [exact MU| lia| rewrite L4; lia| unfold rd_WA; cbn [inside]; rewrite L4; lia]|].
  split; [apply wmono_write; exact WM|].
  apply mem_inv_store; [exact MI| rewrite L4; exact SOK].
Qed.

(* [comment removed for export] *)
Lemma chk1A : forall m1 A B a N, unpoisoned m1 A B -> A <= a -> a + N <= B -> 1 <= N -> a mod 8 + N <= 8 ->
  exists b, ov_read_bytes asegs m1 (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [b]
            /\ (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 + N - 1 < sval b)) /\ -128 <= sval b <= 127.
Proof.
  intros m1 A B a N U A0 A1 N1 N8.
  destruct (unpoisoned_check_rd asegs m1 A B a N U A0 A1 N1 N8) as (b & RDB & CK).
  exists b. unfold shad, ASHOFF in RDB. replace (2147450880 + Z.shiftr a 3) with (Z.shiftr a 3 + 2147450880) in RDB by lia.
  split; [exact RDB|]. split; [exact CK| apply sval_range].
Qed.

(* [comment removed for export] *)
Lemma chkB : forall m1 A B a, unpoisoned m1 A B -> A <= a -> a + 1 <= B ->
  exists b, ov_read_bytes asegs m1 (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [b]
            /\ (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 < sval b)) /\ -128 <= sval b <= 127.
Proof.
  intros m1 A B a U A0 A1. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as M8.
  destruct (chk1A m1 A B a 1 U A0 A1 ltac:(lia) ltac:(lia)) as (b & RDB & CK & SR).
  exists b. split; [exact RDB|]. split; [| exact SR]. destruct CK as [CK|CK]; [left; exact CK| right; lia].
Qed.

(* [comment removed for export] *)
Definition rd_lstA (C : rdctxA) (pc : Z) (m1 : amem) (x6 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x30 : word) : machine_state :=
  MS (mkR (Z_to_bv 64 16843009) (Z_to_bv 64 (a_SPA C)) (a_gp C) (a_tp C)
          (Z_to_bv 64 18446744071562067968) x6 (Z_to_bv 64 23)
          (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 (a_SPA C)) x10 x11 x12 x13 x14 x15 x16 x17
          (Z_to_bv 64 (a_FF C)) x19 (Z_to_bv 64 (a_BUF C)) (Z_to_bv 64 (a_NC C)) (Z_to_bv 64 252645135) x23
          (Z_to_bv 64 2147450880) (Z_to_bv 64 (a_FF C)) (Z_to_bv 64 (Z.shiftr (a_FF C) 3 + 2147450880)) (Z_to_bv 64 (a_msv0 C + 1))
          (Z_to_bv 64 (a_BUF C + zlen (a_buf C) + -7)) (Z_to_bv 64 125613361) x30 (Z_to_bv 64 858993459))
     (a_F C) (Z_to_bv 64 pc) (a_fc C) None m1 (seg_rom asegs).

(* [comment removed for export] *)
Definition rd_headA (C : rdctxA) (s : rstate) (m1 : amem) (x12 x14 x15 x19 x30 : word) : machine_state :=
  rd_lstA C (if r_previous0 s then 0x94c0c else 0x94d88) m1 (Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 (a_BUF C + r_ip s))
          (Z_to_bv 64 (bv_swrap 32 (r_bitStream s))) x12 (Z_to_bv 64 (r_charnum s)) x14 x15
          (Z_to_bv 64 (r_remaining s)) (Z_to_bv 64 (r_threshold s)) x19 (Z_to_bv 64 (r_nbBits s)) x30.

(* [comment removed for export] *)
Definition rd_cntA (C : rdctxA) (s : rstate) (m1 : amem) (x12 x14 x15 x19 x30 : word) : machine_state :=
  rd_lstA C 0x94d88 m1 (Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 (a_BUF C + r_ip s))
          (Z_to_bv 64 (bv_swrap 32 (r_bitStream s))) x12 (Z_to_bv 64 (r_charnum s)) x14 x15
          (Z_to_bv 64 (r_remaining s)) (Z_to_bv 64 (r_threshold s)) x19 (Z_to_bv 64 (r_nbBits s)) x30.

(* [comment removed for export] *)
Definition rd_exitA (C : rdctxA) (s : rstate) (m1 : amem) (x6 x11 x14 x15 x17 x19 x23 x30 : word) : machine_state :=
  rd_lstA C 0x94fbc m1 x6 (Z_to_bv 64 (a_BUF C + r_ip s)) x11 (Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 (r_charnum s)) x14 x15
          (Z_to_bv 64 (r_remaining s)) x17 x19 x23 x30.

(* [comment removed for export] *)
Definition rd_brk_okA (C : rdctxA) (s : rstate) : Prop :=
  0 <= r_remaining s < 2^31 /\ 0 <= r_bitCount s < 2^31 /\ 0 <= r_charnum s < 2^31 /\ 0 <= r_ip s /\ r_ip s + 4 <= zlen (a_buf C).

Section Base.
  Variable C : rdctxA.
  Hypothesis OK : rd_okA C.

  (* [comment removed for export] *)
  Lemma buf_rdA : forall m1 i, bytes_at asegs m1 (a_BUF C) (map (Z_to_bv 8) (a_buf C)) -> 0 <= i < zlen (a_buf C) ->
    ov_read_bytes asegs m1 (Z_to_bv 64 (a_BUF C + i)) 1 = Some [Z_to_bv 8 (Znth i (a_buf C))] /\ 0 <= Znth i (a_buf C) < 256.
  Proof.
    intros m1 i HB Hi. destruct OK as (_ & FB & _). unfold Znth.
    assert (L : (Z.to_nat i < length (a_buf C))%nat) by lia.
    split.
    - eapply (u8ro_read asegs m1 (a_BUF C) _ i); [exact HB| | lia| unfold wa; f_equal; lia].
      rewrite nth_error_map. rewrite (nth_error_nth' (a_buf C) 0 L). reflexivity.
    - apply (proj1 (Forall_forall _ _) FB). apply nth_In. exact L.
  Qed.

  Lemma buf_all_bytesA : all_bytes (a_buf C).
  Proof. destruct OK as (_ & FB & _). apply Forall_all_bytes. exact FB. Qed.
End Base.
End CANSEC1.

(* [comment removed for export] *)
Ltac rdA_acc_hint :=
  lazymatch goal with
  | |- acc_in ?R (Z_to_bv 64 (Z.shiftr ?a 3 + 2147450880), 1%nat) =>
      let X := leftmost a in
      match goal with
      | H : rng R (shad ?A) (nshad (?len + ?A' mod 8)) |- _ => constr_eq X A; constr_eq A A'; apply (acc_shadowU R A len a H); lia
      | H : rng R (shad ?A) (nshad ?len) |- _ => constr_eq X A; apply (acc_shadowA R A len a H); [lia| lia]
      | H : rng R (shad ?A) 1 |- _ => constr_eq X A; apply (acc_shadow1 R A a H); lia
      end
  | |- acc_in ?R (Z_to_bv 64 (a_SPA ?C + _), _) => match goal with H : rng R (a_lo C) _ |- _ => solve_acc_with H end
  | |- acc_in ?R (Z_to_bv 64 (a_SPA ?C), _) => match goal with H : rng R (a_lo C) _ |- _ => solve_acc_with H end
  end.
