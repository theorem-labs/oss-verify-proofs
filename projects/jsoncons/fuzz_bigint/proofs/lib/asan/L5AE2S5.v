(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ParseSpecsA L5OpmodSpecsA L5DivSpecsA L5UnwindSpecsA XIcptA XIcptAs0Kit L5AUnwK L5AUnwK2 L5AE1K L5AE2K L5AE2P1 L5AE2P2 L5AE2P3 L5AE2P4 L5AE2P5 L5AE2P6 L5AE2PP L5AUnwK3 L5AE2Pad.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Set Printing Width 100000. Set Printing Depth 100000.

Module L5AE2S5.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5AUK. Import L5AUK2.
Import L5AE2P1.L5AE2P1. Import L5AE2P2.L5AE2P2. Import L5AE2P3.L5AE2P3. Import L5AE2P4.L5AE2P4. Import L5AE2P5.L5AE2P5. Import L5AE2P6.L5AE2P6. Import L5AE2PP.L5AE2PP. Import L5AUK3.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Hypothesis UNWL : L5USA.as0_unw_layout L.

(* [comment removed for export] *)
Local Notation CALIGN := (cinv_aligned L ar C HI LY HIok UNWL _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Local Notation CMALLOC := (cinv_malloc L ar C HI LY HIok UNWL _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Local Notation CSTRLEN := (cinv_strlen L ar C IL HI LY ILY HIok ICok UNWL _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Local Notation CMEMCPY := (cinv_memcpy_at L ar C HI LY HIok UNWL _ _ _ _ _ _ _ _).
Local Notation CSTRERROR := (cinv_strerror L ar C IL HI LY ILY HIok ICok UNWL _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Local Notation CHNR := (cinv_hnr L ar C HI LY HIok UNWL _ _ _ _ _ _ _ _ _ _ _ _ _ _).
(* [comment removed for export] *)
Local Notation XW := [(6357456, 4); (6360113, 6)].
Local Notation XWIMG := (L5AE1K.xw2_img L UNWL).

Lemma e2_s5 :
  forall (R0 : bvmap 5 word) (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF : list fframe) (LK : list fframe) (LKt : list fframe) (cr : credit) (A : list (Z * Z)) (Sp : Z) (SCR : Z) (xo : Z) (bo : Z) (F1 : Z) (fl1 : Z) (F3 : Z) (fl3 : Z) (gd : bool) (av : Z) (uid : Z) (rnd : Z) (canary : Z) (hw : Z) (fden : Z) (v16 : Z) (v24 : Z) (errv : Z) (R1 : bvmap 5 word) (R2 : bvmap 5 word) (A2 : list (Z * Z)) (u : Z) (obj : Z) (R3 : bvmap 5 word) (R4 : bvmap 5 word) (R5 : bvmap 5 word) (R6 : bvmap 5 word) (R7 : bvmap 5 word) (A7 : list (Z * Z)) (ref : Z) (R8 : bvmap 5 word) (R9 : bvmap 5 word) (R10 : bvmap 5 word) (R11 : bvmap 5 word) (R12 : bvmap 5 word) (R13 : bvmap 5 word) (R14 : bvmap 5 word) (st : L5USA.XS) (R15 : bvmap 5 word) (M17 : word -> option byte) (R16 : bvmap 5 word) (fx17 : FPState) (R17 : bvmap 5 word) (model17 : Model),
    forall (Z2 : getr R (reg 2) = Z_to_bv 64 (Sp - 448)),
    forall (Z3 : getr R (reg 3) = Z_to_bv 64 67584),
    forall (Z4 : getr R (reg 4) = Z_to_bv 64 6360328),
    forall (Z10 : getr R 10 = Z_to_bv 64 16),
    forall (Z8 : getr R (reg 8) = Z_to_bv 64 (Sp - 96)),
    forall (Z9 : getr R (reg 9) = Z_to_bv 64 (Sp - 448)),
    forall (Z18 : getr R 18 = Z_to_bv 64 (F3 / 8 + SB)),
    forall (Z19 : getr R 19 = Z_to_bv 64 (F1 + 32)),
    forall (Z20 : getr R 20 = Z_to_bv 64 0),
    forall (Z21 : getr R 21 = Z_to_bv 64 fden),
    forall (Z22 : getr R 22 = Z_to_bv 64 1),
    forall (Z23 : getr R 23 = Z_to_bv 64 (F3 + 32)),
    forall (Z24 : getr R 24 = Z_to_bv 64 xo),
    forall (Z25 : getr R 25 = getr R0 25),
    forall (Z26 : getr R 26 = Z_to_bv 64 (F3 + 48)),
    forall (Z27 : getr R 27 = Z_to_bv 64 F3),
    forall (C392 : L5.u64_at RSEGS M17 (Sp - 392) F3),
    forall (C376 : L5.u64_at RSEGS M17 (Sp - 376) F3),
    forall (C288 : L5.u64_at RSEGS M17 (Sp - 288) F3),
    forall (C360 : L5.u64_at RSEGS M17 (Sp - 360) (F3 + 32)),
    forall (C352 : L5.u64_at RSEGS M17 (Sp - 352) xo),
    forall (C336 : L5.u64_at RSEGS M17 (Sp - 336) (F3 / 8 + SB)),
    forall (C296 : L5.u64_at RSEGS M17 (Sp - 296) SB),
    forall (BIGQ : L5.big_at RSEGS M (F1 + 32) {| L5.bo_fb := 0; L5.bo_len := 0; L5.bo_st := L5.BInl 0 0 |}),
    forall (BIGD : L5.big_at RSEGS M (F3 + 32) {| L5.bo_fb := fden; L5.bo_len := 0; L5.bo_st := L5.BInl v16 v24 |}),
    forall (SH1a : L5DSA.sh_run M F1 0 4 241),
    forall (SH1b : L5DSA.sh_run M F1 4 4 0),
    forall (SH1c : L5DSA.sh_run M F1 8 4 243),
    forall (SH1d : L5DSA.sh_run M F1 12 4 0),
    forall (SH3a : L5DSA.sh_run M F3 0 4 241),
    forall (SH3b : L5DSA.sh_run M F3 4 4 0),
    forall (SH3c : L5DSA.sh_run M F3 8 4 242),
    forall (SH3d : L5DSA.sh_run M F3 12 4 248),
    forall (SH3e : L5DSA.sh_run M F3 16 4 242),
    forall (SH3f : L5DSA.sh_run M F3 20 4 248),
    forall (SH3g : L5DSA.sh_run M F3 24 4 242),
    forall (SH3h : L5DSA.sh_run M F3 28 4 248),
    forall (SH3i : L5DSA.sh_run M F3 32 4 242),
    forall (SH3j : L5DSA.sh_run M F3 36 4 248),
    forall (SH3k : L5DSA.sh_run M F3 40 4 242),
    forall (SH3l : L5DSA.sh_run M F3 44 4 248),
    forall (SH3m : L5DSA.sh_run M F3 48 4 243),
    forall (SH3n : L5DSA.sh_run M F3 52 12 0),
    forall (FRL3 : L5DSA.fr_live L ar LB ((F1, 1, Sp - 64) :: FF) M 3 F3 fl3 (Sp - 416)),
    forall (FRL1 : L5DSA.fr_live L ar LB FF M 1 F1 fl1 (Sp - 64)),
    forall (AHP0 : ahpres L ar LB FF Sp SCR [] M0 M),
    forall (G1 : getr R0 1 = Z_to_bv 64 581760),
    forall (G2 : getr R0 2 = Z_to_bv 64 Sp),
    forall (G3 : getr R0 3 = Z_to_bv 64 67584),
    forall (G4 : getr R0 4 = Z_to_bv 64 6360328),
    forall (G9 : getr R0 9 = Z_to_bv 64 Sp),
    forall (S32 : Sp mod 32 = 0),
    forall (EC0 : L5.u64_at RSEGS M17 6357448 0),
    forall (GD0 : L5.u8_at RSEGS M17 6358000 (if gd then 1 else 0)),
    forall (GD1 : L5.u8_at RSEGS M17 6358001 (if gd then 1 else 0)),
    forall (TDL : L5.u64_at RSEGS M17 6360280 6492112),
    forall (MSG0 : L5.u64_at RSEGS M17 6492152 0),
    forall (ERR : L5.u32_at RSEGS M17 6360164 errv),
    forall (ERRR : 0 <= errv < 2 ^ 64),
    forall (CAN : L5.u64_at RSEGS M17 6491464 canary),
    forall (AUXP : L5.u64_at RSEGS M17 6492064 av),
    forall (AV8 : av mod 8 = 0),
    forall (AVLO : 2 ^ 40 <= av),
    forall (AVHI : av + 160 <= 2 ^ 47),
    forall (UIDR : 0 <= uid < 2 ^ 64),
    forall (RNDR : 0 <= rnd < 2 ^ 64),
    forall (CANR : 0 <= canary < 2 ^ 64),
    forall (HWR : 0 <= hw < 2 ^ 64),
    forall (AVS : ar_sptop ar <= av),
    forall (HH : ri_inv HI LB (L5DSA.ff_e2 FF Sp F1 F3) LKt cr A M (vml_of model)),
    forall (AM : amodel_ok A model),
    forall (HK : K []),
    forall (LKI : incl LKt LK),
    forall (STK : astk ar M Sp SCR),
    forall (HSCR : 69632 <= SCR),
    forall (SCR8 : SCR mod 8 = 0),
    forall (SH : L5OMA.stksh ar M (Sp - SCR)),
    forall (CRF : L5OMA.acredit_for L cr 2 (144 + 37)),
    forall (KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LK' : list fframe) (A' : list (Z * Z)), regs_preserved R0 R' -> L5USA.e2_landed L st LB FF LK cr Sp M' R' LB' cr' LK' -> ahpres L ar LB FF Sp SCR L5USA.xs_foot M M' -> model_rt model model' -> incl A A' -> amodel_ok A' model' -> ri_inv HI LB' FF LK' cr' A' M' (vml_of model') -> srealizes RSEGS SCFG (cfg (fx:=fx') R' 582452 M' model') K),
    forall (U01 : L5DSA.U R0 1 = 581760),
    forall (U09 : L5DSA.U R0 9 = Sp),
    forall (E8 : bv_unsigned (getr R (reg 8)) = Sp - 448 + 352),
    forall (E9 : bv_unsigned (getr R (reg 9)) = Sp - 448),
    forall (A16 : Sp mod 16 = 0),
    forall (SLO : ahl_ceil ar + 4096 + SCR <= Sp),
    forall (SHI : Sp <= ar_sptop ar),
    forall (SPT : 140735340871680 <= ar_sptop ar <= 2 ^ 47),
    forall (HS0 : 0 <= SCR),
    forall (ALS : (Sp - 448) mod 16 = 0),
    forall (ALS8 : (Sp - 448) mod 8 = 0),
    forall (SPR0 : 0 <= Sp - 448 < 2 ^ 64),
    forall (SPLO : 140735332552704 <= Sp - 448),
    forall (SPHI : Sp - 448 <= 140737488355264),
    forall (LY2 : as0_layout2 L),
    forall (HTP : hl_tp L = 6360328),
    forall (FN : numg (ar_fs ar <= F3 /\ F3 + 512 <= ar_fs ar + 11571200 /\ ar_fs ar <= F1 /\ F1 + 128 <= ar_fs ar + 11571200 /\ ar_fs ar <= fl1 < ar_fs ar + 11571200 /\ ar_fs ar <= fl3 < ar_fs ar + 11571200 /\ 6500352 <= ar_fs ar /\ ar_fs ar + 11571200 <= ahl_ceil ar /\ 0 <= F1 / 8 <= 2 ^ 44 /\ 0 <= F3 / 8 <= 2 ^ 44)),
    forall (F3A : F3 mod 512 = 0),
    forall (F1A : F1 mod 128 = 0),
    forall (DJF : ar_fs ar + 11571200 <= 2147446784 \/ 2147446784 + 17592186048512 <= ar_fs ar),
    forall (EX0 : forall x : nat, In x KS_ue2a1 -> getr R1 (reg x) = getr R (reg x)),
    forall (EX1 : getr R1 (reg 1) = Z_to_bv 64 723952),
    forall (EX2 : getr R1 (reg 2) = Z_to_bv 64 (Sp - 448 - 48)),
    forall (EX3 : getr R1 (reg 8) = Z_to_bv 64 144),
    forall (EX4 : getr R1 (reg 11) = Z_to_bv 64 144),
    forall (ACR1 : acredit_ok L cr 144),
    forall (CRF1 : L5OMA.acredit_for L (adebit L cr 144) 1 37),
    forall (RP2 : regs_preserved R1 R2),
    forall (EOBJ : obj = u + 128),
    forall (OB16 : obj mod 16 = 0),
    forall (OB8 : obj mod 8 = 0),
    forall (OBR0 : 0 <= obj < 2 ^ 64),
    forall (OBR : 17594333495424 <= obj <= 140737479966720),
    forall (OCEIL : obj + 16 <= ahl_ceil ar),
    forall (EX10 : forall x : nat, In x KS_ue2a2_mh -> getr R3 (reg x) = getr R2 (reg x)),
    forall (EX11 : getr R3 (reg 1) = Z_to_bv 64 601572),
    forall (EX12 : getr R3 (reg 2) = Z_to_bv 64 (Sp - 448)),
    forall (EX13 : getr R3 (reg 8) = Z_to_bv 64 (Sp - 448 + 352)),
    forall (EX14 : getr R3 (reg 9) = Z_to_bv 64 (Sp - 448)),
    forall (EX15 : getr R3 (reg 10) = Z_to_bv 64 obj),
    forall (EX16 : getr R3 (reg 11) = Z_to_bv 64 142208),
    forall (EX17 : getr R3 (reg 19) = Z_to_bv 64 obj),
    forall (Z72 : L5KA.zeros_at M17 (obj - 72) 4),
    forall (E10 : bv_unsigned (getr R3 (reg 10)) = obj),
    forall (EX5 : forall x : nat, In x KS_ue2c1 -> getr R4 (reg x) = getr R3 (reg x)),
    forall (EX6 : getr R4 (reg 1) = Z_to_bv 64 728508),
    forall (EX19 : getr R4 (reg 2) = Z_to_bv 64 (Sp - 448 - 48)),
    forall (EX20 : getr R4 (reg 8) = getr R3 (reg 10)),
    forall (EX21 : getr R4 (reg 9) = Z_to_bv 64 142208),
    forall (EX22 : getr R4 (reg 10) = Z_to_bv 64 142208),
    forall (EX23 : L5.u64_at RSEGS M17 obj 873376),
    forall (R4_8 : getr R4 (reg 8) = Z_to_bv 64 obj),
    forall (sR5 : getr R5 (reg 10) = Z_to_bv 64 12),
    forall (RP5 : regs_preserved R4 R5),
    forall (EX7 : forall x : nat, In x KS_ue2c2 -> getr R6 (reg x) = getr R5 (reg x)),
    forall (EX8 : getr R6 (reg 1) = Z_to_bv 64 856060),
    forall (EX9 : getr R6 (reg 2) = Z_to_bv 64 (Sp - 448 - 64)),
    forall (EX18 : getr R6 (reg 8) = Z_to_bv 64 37),
    forall (EX29 : getr R6 (reg 10) = Z_to_bv 64 37),
    forall (EX30 : getr R6 (reg 18) = Z_to_bv 64 12),
    forall (ACR2 : acredit_ok L (adebit L cr 144) 37),
    forall (mR7 : getr R7 (reg 10) = Z_to_bv 64 ref),
    forall (RP7 : regs_preserved R6 R7),
    forall (RF16 : ref mod 16 = 0),
    forall (EX33 : forall x : nat, In x KS_ue2c3 -> getr R8 (reg x) = getr R7 (reg x)),
    forall (EX34 : getr R8 (reg 1) = Z_to_bv 64 728552),
    forall (EX35 : getr R8 (reg 2) = Z_to_bv 64 (Sp - 448 - 48)),
    forall (EX36 : getr R8 (reg 8) = Z_to_bv 64 obj),
    forall (EX37 : getr R8 (reg 10) = Z_to_bv 64 (ref + 24)),
    forall (EX38 : getr R8 (reg 11) = Z_to_bv 64 142208),
    forall (EX39 : getr R8 (reg 12) = Z_to_bv 64 13),
    forall (EX40 : getr R8 (reg 19) = Z_to_bv 64 (ref + 24)),
    forall (EX41 : L5.u32_at RSEGS M17 (ref + 16) 0),
    forall (EX42 : L5.u64_at RSEGS M17 (ref + 8) 12),
    forall (EX43 : L5.u64_at RSEGS M17 ref 12),
    forall (HMC : amemcpy_spec_at L ar SCFG HI 385232 false),
    forall (mR9 : getr R9 (reg 10) = Z_to_bv 64 (ref + 24)),
    forall (RP9 : regs_preserved R8 R9),
    forall (EX31 : forall x : nat, In x KS_ue2c4 -> getr R10 (reg x) = getr R9 (reg x)),
    forall (EX32 : getr R10 (reg 1) = Z_to_bv 64 601596),
    forall (EX44 : getr R10 (reg 2) = Z_to_bv 64 (Sp - 448)),
    forall (EX45 : getr R10 (reg 8) = Z_to_bv 64 (Sp - 448 + 352)),
    forall (EX46 : getr R10 (reg 9) = Z_to_bv 64 (Sp - 448)),
    forall (EX47 : getr R10 (reg 18) = Z_to_bv 64 (F3 / 8 + SB)),
    forall (EX48 : getr R10 (reg 19) = Z_to_bv 64 obj),
    forall (EX49 : L5.u64_at RSEGS M17 (obj + 8) (ref + 24)),
    forall (RP11 : regs_preserved R10 R11),
    forall (EX24 : forall x : nat, In x KS_ue2c5 -> getr R12 (reg x) = getr R11 (reg x)),
    forall (EX25 : getr R12 (reg 10) = Z_to_bv 64 obj),
    forall (EX26 : getr R12 (reg 11) = Z_to_bv 64 873616),
    forall (EX : getr R12 (reg 12) = Z_to_bv 64 718724),
    forall (E12_10 : bv_unsigned (getr R12 (reg 10)) = obj),
    forall (EX28 : forall x : nat, In x KS_ue2t1 -> getr R13 (reg x) = getr R12 (reg x)),
    forall (EX50 : getr R13 (reg 1) = Z_to_bv 64 343324),
    forall (EX51 : getr R13 (reg 2) = Z_to_bv 64 (Sp - 448 - 64)),
    forall (EX52 : getr R13 (reg 8) = Z_to_bv 64 (obj - 32)),
    forall (EX53 : getr R13 (reg 9) = Z_to_bv 64 883976),
    forall (EX54 : getr R13 (reg 10) = Z_to_bv 64 (obj - 32)),
    forall (EX55 : getr R13 (reg 11) = Z_to_bv 64 743680),
    forall (EX56 : getr R13 (reg 12) = Z_to_bv 64 722532),
    forall (EX57 : getr R13 (reg 18) = getr R12 (reg 10)),
    forall (EX61 : L5.u64_at RSEGS M17 (obj - 120) 1),
    forall (EX64 : L5.u64_at RSEGS M17 (obj - 88) 607608),
    forall (EX65 : L5.u64_at RSEGS M17 (obj - 104) 718724),
    forall (EX66 : L5.u64_at RSEGS M17 (obj - 112) 873616),
    forall (EX67 : L5.u64_at RSEGS M17 (obj - 96) 607876),
    forall (EX69 : L5.u32_at RSEGS M17 6357456 1),
    forall (RP14 : regs_preserved R13 R14),
    forall (DJ0 : ref + 37 <= u \/ u + 144 <= ref),
    forall (AV8' : av mod 8 = 0),
    forall (STE : L5USA.xs_gd st = gd /\ L5USA.xs_av st = av /\ L5USA.xs_uid st = uid /\ L5USA.xs_rnd st = rnd /\ L5USA.xs_canary st = canary /\ L5USA.xs_hw st = hw),
    forall (EX74 : forall x : nat, In x KS_ue2t2_v1 -> getr R15 (reg x) = getr R14 (reg x)),
    forall (EX75 : getr R15 (reg 1) = Z_to_bv 64 602268),
    forall (EX76 : getr R15 (reg 2) = Z_to_bv 64 (Sp - 448)),
    forall (EX77 : getr R15 (reg 6) = Z_to_bv 64 743680),
    forall (EX78 : getr R15 (reg 8) = Z_to_bv 64 (Sp - 448 + 352)),
    forall (EX79 : getr R15 (reg 9) = Z_to_bv 64 (Sp - 448)),
    forall (EX80 : getr R15 (reg 10) = Z_to_bv 64 (obj - 32)),
    forall (EX81 : getr R15 (reg 11) = Z_to_bv 64 0),
    forall (EX82 : getr R15 (reg 18) = Z_to_bv 64 (F3 / 8 + SB)),
    forall (EX83 : L5.u64_at RSEGS M17 (obj - 8) (Sp - 448 + 448)),
    forall (EX84 : L5.u64_at RSEGS M17 (obj - 40) obj),
    forall (EX85 : L5.u64_at RSEGS M17 (obj - 48) 582452),
    forall (EX86 : L5.u64_at RSEGS M17 (obj - 56) 157040),
    forall (EX87 : L5.u64_at RSEGS M17 (obj - 64) 157179),
    forall (EX88 : L5.u32_at RSEGS M17 (obj - 68) 1),
    forall (EX89 : L5.u64_at RSEGS M17 (obj - 16) 0),
    forall (EX93 : L5.u64_at RSEGS M17 (obj - 32) 4849336966747728640),
    forall (EX94 : L5.u8_at RSEGS M17 6360113 1),
    forall (EX95 : L5.u8_at RSEGS M17 6360114 0),
    forall (EX96 : L5.u8_at RSEGS M17 6360115 1),
    forall (EX97 : L5.u8_at RSEGS M17 6360116 0),
    forall (EX98 : L5.u8_at RSEGS M17 6360117 1),
    forall (EX27 : L5.u8_at RSEGS M17 6360118 0),
    forall (R16_2 : getr R16 (reg 2) = Z_to_bv 64 (Sp - 448)),
    forall (R16_3 : getr R16 (reg 3) = Z_to_bv 64 67584),
    forall (R16_4 : getr R16 (reg 4) = Z_to_bv 64 6360328),
    forall (R16_8 : getr R16 (reg 8) = Z_to_bv 64 (Sp - 448 + 352)),
    forall (R16_10' : getr R16 (reg 10) = Z_to_bv 64 (obj - 32)),
    forall (NUM : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR) /\ (0 <= Sp - 448 < 2 ^ 64 /\ 140735332552704 <= Sp - 448 <= 140737488355264) /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47) /\ (obj = u + 128 /\ 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 16 <= ahl_ceil ar) /\ 17594333495296 <= ref /\ ref + 37 <= ahl_ceil ar)),
    forall (EX59 : forall x : nat, In x KS_ue2r1 -> getr R17 (reg x) = getr R16 (reg x)),
    forall (EX60 : getr R17 (reg 1) = Z_to_bv 64 598052),
    forall (EX62 : getr R17 (reg 2) = Z_to_bv 64 (Sp - 448 + 352)),
    forall (EX63 : getr R17 (reg 8) = Z_to_bv 64 (Sp - 448 + 448)),
    forall (EX68 : getr R17 (reg 9) = Z_to_bv 64 (Sp - 448 + 352)),
    forall (EX90 : getr R17 (reg 11) = Z_to_bv 64 0),
    forall (EX91 : getr R17 (reg 18) = Z_to_bv 64 F1),
    forall (EX92 : getr R17 (reg 19) = Z_to_bv 64 (nz xo)),
    forall (EX99 : getr R17 (reg 20) = Z_to_bv 64 (nz bo)),
    forall (EX100 : getr R17 (reg 21) = Z_to_bv 64 (F1 + 32)),
    forall (EX101 : getr R17 (reg 22) = Z_to_bv 64 (F1 / 8 + SB)),
    forall (EX102 : getr R17 (reg 23) = Z_to_bv 64 F1),
    forall (EX103 : getr R17 (reg 24) = Z_to_bv 64 L5DSA.RETIRE_MAGIC),
    forall (EX104 : getr R17 (reg 25) = Z_to_bv 64 (L5DSA.U R0 25)),
    forall (EX105 : getr R17 (reg 26) = Z_to_bv 64 (L5DSA.U R0 26)),
    forall (EX58 : getr R17 (reg 27) = Z_to_bv 64 (L5DSA.U R0 27)),
    forall (CI17 : cinv L ar HI M model A LB ((F1, 1, Sp - 64) :: FF) Sp SCR XW [(ref, 37); (u, 144)] M17 model17 LKt (adebit L (adebit L cr 144) 37) A7),
    forall (FRO : forall j : nat, (j < 11)%nat -> L5.u64_at RSEGS M17 (Sp - 88 + 8 * Z.of_nat j) (nth j [F1; L5DSA.U R0 24; L5DSA.U R0 23; L5DSA.U R0 22; L5DSA.U R0 21; L5DSA.U R0 20; L5DSA.U R0 19; L5DSA.U R0 18; Sp; L5DSA.U R0 8; 581760] 0)),
    forall (FRD : forall j : nat, (j < 13)%nat -> L5.u64_at RSEGS M17 (Sp - 200 + 8 * Z.of_nat j) (nth j [L5DSA.U R0 27; L5DSA.U R0 26; L5DSA.U R0 25; L5DSA.RETIRE_MAGIC; F1; F1 / 8 + SB; F1 + 32; nz bo; nz xo; F1; Sp - 96; Sp; L5DSA.DIV_RET_O] 0)),
    forall (AUXV : forall j : nat, (j < 20)%nat -> L5.u64_at RSEGS M17 (av + 8 * Z.of_nat j) (nth j (L5USA.auxv20A uid rnd hw) 0)),
    forall (IC3 : L5.img_clear M17 892784 (892784 + 8)),
    forall (IC2 : L5.img_clear M17 892736 892768),
    forall (IC1 : L5.img_clear M17 65536 880640),
  srealizes RSEGS SCFG (cfg (fx:=fx17) R17 598052 M17 model17) K.
Proof.
  intros.
  (* [comment removed for export] *)
  assert (Hk1 : In 1 [1; 2; 3]) by (left; reflexivity).
  pose proof CI17 as (HH17 & _).
  pose proof (L5DSA.frl_cell _ _ _ _ _ _ _ _ _ FRL1) as FLC0. pose proof (L5DSA.frl_fs _ _ _ _ _ _ _ _ _ FRL1) as FLP1.
  pose proof (L5DSA.frl_nc _ _ _ _ _ _ _ _ _ FRL1) as FLNC1. pose proof (L5DSA.frl_apart _ _ _ _ _ _ _ _ _ FRL1) as FLA1. change (ff_bytes 1) with 128 in FLA1.
  destruct (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ model17 F1 1 _ _ fl1 HH HH17 (or_intror (or_introl eq_refl)) (or_introl eq_refl) Hk1 FLC0) as [FLC17 _].
  assert (SHD0 : L5.defined M (F1 / 8 + SB) (ff_bytes 1 / 8)).
  { change (ff_bytes 1 / 8) with 16. intros i Hi.
    destruct (Z_lt_dec i 4) as [LT0|GE0]; [apply (shrun_def M F1 0 4 _ i SH1a); clear - Hi LT0 ; lia|].
    destruct (Z_lt_dec i 8) as [LT1|GE1]; [apply (shrun_def M F1 4 4 _ i SH1b); clear - Hi LT1 GE0; lia|].
    destruct (Z_lt_dec i 12) as [LT2|GE2]; [apply (shrun_def M F1 8 4 _ i SH1c); clear - Hi LT2 GE1; lia|].
    destruct (Z_lt_dec i 16) as [LT3|GE3]; [apply (shrun_def M F1 12 4 _ i SH1d); clear - Hi LT3 GE2; lia|].
    exfalso. clear - Hi GE3. lia. }
  pose proof (frame_shadow_defined L ar C HI LY HIok M model A LB FF Sp SCR XW F1 1 (Sp - 64) _ _ _ _ _ _ CI17 Hk1 SHD0) as SHD17.
  destruct (cv_frame L ar C HI LY HIok M model A LB FF Sp SCR XW F1 1 (Sp - 64) _ _ _ _ _ _ CI17 Hk1 fl1 FLC17 FLP1 SHD17) as (FDEFv & FWv & FSHWv & FLCv & FLWv & _ & _).
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *. replace (F1 + 128 - 8) with (F1 + 120) in FLCv by (clear; lia).
  (* [comment removed for export] *)
  pose proof BIGQ as (Q8 & QR & _ & QT & _). cbn [L5.bo_fb L5.bo_st] in Q8, QR, QT.
  assert (Q17 : L5.u8_at RSEGS (mrestrict (ahid A7 model17) M17) (F1 + 32) 0).
  { apply (cv_fs_u8 L ar C HI LY HIok M model A LB FF Sp SCR XW F1 1 (Sp - 64) _ _ _ _ _ _ CI17 Hk1). unfold numg in FN; clear - FN; lia. unfold FS_BYTES; unfold numg in FN; clear - FN; lia.
    apply (L5C.u8_at_agree RSEGS M M17 (F1 + 32) 0). 4: exact Q8. 2: unfold numg in FN; clear - FN; lia. 2: unfold numf in NUM; unfold numg in FN; clear - FN NUM; lia.
    apply (frame_agree L ar C HI LY HIok M model A LB FF Sp SCR XW F1 1 (Sp - 64) XWIMG _ _ _ _ _ _ (F1 + 32) 1 CI17 Hk1). clear; lia. change (ff_bytes 1) with 128; clear; lia. right; clear; lia. }
  assert (ICp : L5.img_clear M17 860160 880640) by (intros i Hi; apply IC1; clear - Hi; lia).
  assert (AL_E : aligned Sp 32) by exact S32.
  assert (AL_F : aligned F1 32). { unfold aligned. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - F1A. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  unfold FS_BYTES in FLP1.
  pose proof (L5AE2PD.pad2_run fx17 R17 (mrestrict (ahid A7 model17) M17) Sp F1 fl1 0) as P.
  feed P ltac:(first [ rk | asm | fd_mem CI17 | (unfold SB in *; gmem) | (unfold L5DSA.RETIRE_MAGIC, SB in *; rk) | reflexivity | (unfold numf in NUM; unfold numg in FN; clear - NUM FN DJF FLA1 FLP1; lia) ]).
  destruct P as (fx18 & R18 & M18v & MS18 & MG18 & FZ18 & FL018 & KS18).
  apply (cinv_retire L ar C HI LY HIok M model A LB FF Sp SCR XW F1 1 (Sp - 64) [(ref, 37); (u, 144)] M17 model17 LKt _ A7 fx17 fx18 R17 598052 R18 598248 M18v
           (Wpad F1 128 fl1) fl1 K CI17 HS0 Hk1 FLC17 ltac:(unfold FS_BYTES; exact FLP1) FLNC1 MS18 MG18 FZ18).
  { intros a Wa. unfold Wpad in Wa. change (ff_bytes 1 / 8) with 16. clear - Wa. tauto. }
  { intros a. apply Wpad_dec. }
  { exact FL018. }
  intros M18 model18 CI18 AH18 VIS18 FRM18.
  pose proof (pad_agree L ar C HI LY HIok M model A LB FF Sp SCR XW F1 1 (Sp - 64) _ _ _ _ _ _ fl1 M18 CI17 Hk1 ltac:(unfold FS_BYTES; exact FLP1) FRM18) as AG.
  carry M17 M18 AG ltac:(cvis_tac [(ref, 37); (u, 144)]). clear AG FRM18 VIS18 MS18 MG18 FZ18 FL018 FDEFv FWv FSHWv FLCv FLWv Q17 SHD17 FLC17 HH17 ICp.
  assert (R18_1 : getr R18 (reg 1) = Z_to_bv 64 598052) by (rewrite (KS18 1%nat) by in_tac; rk).
  assert (R18_2 : getr R18 (reg 2) = Z_to_bv 64 (Sp - 448 + 352)) by (rewrite (KS18 2%nat) by in_tac; rk).
  assert (R18_3 : getr R18 (reg 3) = Z_to_bv 64 67584) by (rewrite (KS18 3%nat) by in_tac; rk).
  assert (R18_4 : getr R18 (reg 4) = Z_to_bv 64 6360328) by (rewrite (KS18 4%nat) by in_tac; rk).
  assert (R18_8 : getr R18 (reg 8) = Z_to_bv 64 (Sp - 448 + 448)) by (rewrite (KS18 8%nat) by in_tac; rk).
  assert (R18_10 : getr R18 (reg 10) = Z_to_bv 64 (obj - 32)) by (rewrite (KS18 10%nat) by in_tac; rk).
  assert (R18_25 : getr R18 (reg 25) = Z_to_bv 64 (L5DSA.U R0 25)) by (rewrite (KS18 25%nat) by in_tac; rk).
  assert (R18_26 : getr R18 (reg 26) = Z_to_bv 64 (L5DSA.U R0 26)) by (rewrite (KS18 26%nat) by in_tac; rk).
  assert (R18_27 : getr R18 (reg 27) = Z_to_bv 64 (L5DSA.U R0 27)) by (rewrite (KS18 27%nat) by in_tac; rk).
  (* [comment removed for export] *)
  destruct (cv_tls L ar C IL HI LY ILY HIok ICok UNWL M model A LB FF Sp SCR XW _ _ _ _ _ _ CI18) as (ctx & th & tbv & tev & blk & TLSC & TLSR & TLSI & TLSP & TLSB).
  cbv zeta in TLSC. rewrite HTP in TLSC. change (6360328 + 8) with 6360336 in TLSC. destruct TLSC as (TC1 & TC2 & TC3 & TC4 & TC5 & TC6).
  pose proof (TLSB ref 37 ltac:(left; reflexivity)) as TB1. pose proof (TLSB u 144 ltac:(right; left; reflexivity)) as TB2. clear TLSB.
  assert (NUM4 : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR)
                      /\ (0 <= Sp - 448 < 2 ^ 64 /\ 140735332552704 <= Sp - 448 /\ Sp - 448 <= 140737488355264)
                      /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47)
                      /\ (obj = u + 128 /\ 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 16 <= ahl_ceil ar)
                      /\ (17594333495296 <= ref /\ ref + 37 <= ahl_ceil ar)
                      /\ (4096 <= ctx /\ ctx + 160 <= ahl_ceil ar /\ 4096 <= th /\ th + 64 <= ahl_ceil ar /\ 4096 <= blk /\ blk + 4096 <= ahl_ceil ar /\ 0 <= tbv < 2 ^ 64 /\ 0 <= tev < 2 ^ 64))).
  { unfold numf in *. clear - NUM TLSR. lia. }
  destruct TLSI as (DJ1 & DJ2 & DJ3). destruct TLSP as (DJ4 & DJ5 & DJ6). destruct TB1 as (DJ7 & DJ8 & DJ9). destruct TB2 as (DJ10 & DJ11 & DJ12).
  clear NUM. rename NUM4 into NUM. clear TLSR.
  expand_arr AUXV 20%nat. expand_arr FRO 11%nat.
  pose proof (ue2r2_conc HFILL HCOPY HTLS fx18 R18 (mrestrict (ahid A7 model18) M18)
                (fun j => match j with 2%nat => Sp - 448 | 10%nat => obj | 32%nat => av | 33%nat => canary | 34%nat => uid | 36%nat => rnd | 39%nat => hw
                                  | 40%nat => ctx | 41%nat => th | 42%nat => blk | 43%nat => tbv | 44%nat => tev
                                  | 45%nat => L5DSA.U R0 8 | 46%nat => L5DSA.U R0 18 | 47%nat => L5DSA.U R0 19 | 48%nat => L5DSA.U R0 20 | 49%nat => L5DSA.U R0 21
                                  | 50%nat => L5DSA.U R0 22 | 51%nat => L5DSA.U R0 23 | 52%nat => L5DSA.U R0 24 | _ => 0 end)) as P. cbn beta iota in P.
  feed_rng P ltac:(first [ apply nz_range | apply UR | apply BL.bvu_range | (unfold L5DSA.U; apply BL.bvu_range) | nlia ]).
  piece_step CI18 XWIMG P (fun a => Sp - 448 - 10560 <= a < Sp - 448 - 10560 + 10912) fx19 R19 M19 model19 CI19.
  (* [comment removed for export] *)
  destruct STE as (ST1 & ST2 & ST3 & ST4 & ST5 & ST6).
  destruct CI19 as (HH19 & AM19 & RT19 & IA19 & STK19 & SH19 & EK19 & DK19).
  assert (EU : u = obj - 128) by (unfold numf in NUM; clear - NUM; lia).
  apply (KONT fx19 R19 M19 model19 ((ref, 37) :: (obj - 128, 144) :: LB) (adebit L (adebit L cr 144) 37) LKt A7).
  - apply preserved_by_index. intros j Hj. unfold cs_all in Hj. cbn [In] in Hj.
    assert (UB : forall k : Z, Z_to_bv 64 (L5DSA.U R0 k) = getr R0 (Z_to_bv 5 k)) by (intros k; unfold L5DSA.U; apply Z_to_bv_bv_unsigned).
    assert (G2' : getr R0 (reg 2) = Z_to_bv 64 Sp) by (rewrite <- r2; exact G2).
    assert (G3' : getr R0 (reg 3) = Z_to_bv 64 67584) by (rewrite <- L5AE1K.r3; exact G3).
    assert (G4' : getr R0 (reg 4) = Z_to_bv 64 6360328) by (rewrite <- r4; exact G4).
    assert (G9' : getr R0 (reg 9) = Z_to_bv 64 Sp) by (rewrite <- L5AE1K.r9; exact G9).
    destruct Hj as [<-|Hj]. { rewrite G2'. rk. }
    destruct Hj as [<-|Hj]. { rewrite G3'. rk. }
    destruct Hj as [<-|Hj]. { rewrite G4'. rk. }
    destruct Hj as [<-|Hj]. { etransitivity. 2: exact (UB 8). rk. }
    destruct Hj as [<-|Hj]. { rewrite G9'. rk. }
    destruct Hj as [<-|Hj]. { etransitivity. 2: exact (UB 18). rk. }
    destruct Hj as [<-|Hj]. { etransitivity. 2: exact (UB 19). rk. }
    destruct Hj as [<-|Hj]. { etransitivity. 2: exact (UB 20). rk. }
    destruct Hj as [<-|Hj]. { etransitivity. 2: exact (UB 21). rk. }
    destruct Hj as [<-|Hj]. { etransitivity. 2: exact (UB 22). rk. }
    destruct Hj as [<-|Hj]. { etransitivity. 2: exact (UB 23). rk. }
    destruct Hj as [<-|Hj]. { etransitivity. 2: exact (UB 24). rk. }
    destruct Hj as [<-|Hj]. { etransitivity. 2: exact (UB 25). rk. }
    destruct Hj as [<-|Hj]. { etransitivity. 2: exact (UB 26). rk. }
    destruct Hj as [<-|Hj]. { etransitivity. 2: exact (UB 27). rk. }
    destruct Hj.
  - unfold L5USA.e2_landed. split. 2: split.
    + exists obj, ref. split. rewrite r10. rk. split. rewrite r11. rk. split. rewrite r2. rk.
      split. reflexivity.
      split. { unfold L5USA.exc_at, L5USA.EXC_CLASS, L5USA.DTOR_RUNTIME_ERROR. split. gmem. split. apply u32_of_zeros. exact Z72. unfold numf in NUM; clear - NUM; lia. unfold numf in NUM; clear - NUM; lia.
               split. gmem. split. gmem. split. gmem. split. gmem. gmem. }
      unfold L5USA.statics_landed. rewrite ST1, ST2, ST3, ST4, ST5, ST6.
      split. exact EC0. split. unfold L5USA.EH_UNCAUGHT; gmem. split. { unfold L5USA.syscat_guard, L5USA.SYSCAT_GUARD. split. exact GD0. exact GD1. }
      split. { unfold L5USA.uw_flags, L5USA.UW_FLAGS. repeat split; gmem. }
      unfold L5USA.statics_const, L5USA.TD_LOCALE, L5USA.GLOBAL_LOCALE, L5USA.LOCALE_MSGCAT, L5USA.ERRNO, L5USA.CANARY, L5USA.AUXVP, L5USA.SYSCAT_OBJ.
      split. exact TDL. split. exact MSG0. split. { exists errv. split. exact ERR. exact ERRR. } split. exact CAN. split. exact AUXP. split. exact AV8. split. exact AVLO. split. exact AVHI. split. exact AUXV.
      split. exact UIDR. split. exact RNDR. split. exact CANR. split. exact HWR. split. exact IC1. split. exact IC2. exact IC3.
    + unfold L5USA.EXC23_SZ, L5USA.REF2_SZ. rewrite <- !L5OMA.adebits_1, L5OMA.adebits_add. change (1 + 1) with 2. unfold credit_le. clear; lia.
    + exact LKI.
  - split. exact EK19. split. exact (astk_defined ar M19 Sp SCR (Sp - SCR) SCR STK19 ltac:(clear; lia) ltac:(clear; lia)). exact DK19.
  - exact RT19.
  - exact IA19.
  - exact AM19.
  - rewrite <- EU. exact HH19.
Qed.

End WithIface.
End SCFG_1.
End L5AE2S5.
