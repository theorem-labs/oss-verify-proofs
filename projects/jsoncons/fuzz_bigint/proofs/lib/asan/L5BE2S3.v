(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5ParseSpecsAB0 L5OpmodSpecsAB0 L5DivSpecsAB0 L5UnwindSpecsAB0 XIcptAB0 XIcptAs0KitB0 L5BUnwK L5BUnwK2 L5BE1K L5BE2K L5BE2P1 L5BE2P2 L5BE2P3 L5BE2P4 L5BE2P5 L5BE2P6 L5BE2PP L5BUnwK3 L5BE2S4.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Set Printing Width 100000. Set Printing Depth 100000.

Module L5BE2S3.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5AUK. Import L5AUK2.
Import L5BE2P1.L5BE2P1. Import L5BE2P2.L5BE2P2. Import L5BE2P3.L5BE2P3. Import L5BE2P4.L5BE2P4. Import L5BE2P5.L5BE2P5. Import L5BE2P6.L5BE2P6. Import L5BE2PP.L5BE2PP. Import L5AUK3.
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
Local Notation XW := [(6360528, 4); (6363185, 6)].
Local Notation XWIMG := (L5BE1K.xw2_img L UNWL).

Lemma e2_s3 :
  forall (R0 : bvmap 5 word) (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF : list fframe) (LK : list fframe) (LKt : list fframe) (cr : credit) (A : list (Z * Z)) (Sp : Z) (SCR : Z) (xo : Z) (bo : Z) (F1 : Z) (fl1 : Z) (F3 : Z) (fl3 : Z) (rt8 : Z) (gd : bool) (fl : bool) (av : Z) (uid : Z) (rnd : Z) (canary : Z) (hw : Z) (fden : Z) (v16 : Z) (v24 : Z) (errv : Z) (R1 : bvmap 5 word) (R2 : bvmap 5 word) (A2 : list (Z * Z)) (u : Z) (obj : Z) (R3 : bvmap 5 word) (R4 : bvmap 5 word) (R5 : bvmap 5 word) (R6 : bvmap 5 word) (R7 : bvmap 5 word) (A7 : list (Z * Z)) (ref : Z) (R8 : bvmap 5 word) (M14 : word -> option byte) (R9 : bvmap 5 word) (R10 : bvmap 5 word) (R11 : bvmap 5 word) (R12 : bvmap 5 word) (R13 : bvmap 5 word) (fx14 : FPState) (R14 : bvmap 5 word) (model14 : Model),
    forall (Z2 : getr R (reg 2) = Z_to_bv 64 (Sp - 496)),
    forall (Z3 : getr R (reg 3) = Z_to_bv 64 67584),
    forall (Z4 : getr R (reg 4) = Z_to_bv 64 6363400),
    forall (Z10 : getr R 10 = Z_to_bv 64 16),
    forall (Z8 : getr R (reg 8) = Z_to_bv 64 (Sp - 112)),
    forall (Z9 : getr R (reg 9) = Z_to_bv 64 (Sp - 496)),
    forall (Z18 : getr R 18 = Z_to_bv 64 (F3 / 8 + SB)),
    forall (Z19 : getr R 19 = Z_to_bv 64 xo),
    forall (Z20 : getr R 20 = Z_to_bv 64 fden),
    forall (Z21 : getr R 21 = Z_to_bv 64 bo),
    forall (Z22 : getr R 22 = Z_to_bv 64 F3),
    forall (Z23 : getr R 23 = Z_to_bv 64 SB),
    forall (Z24 : getr R 24 = Z_to_bv 64 (F3 + 32)),
    forall (Z25 : getr R 25 = Z_to_bv 64 1),
    forall (Z26 : getr R 26 = Z_to_bv 64 (F1 + 32)),
    forall (Z27 : getr R 27 = Z_to_bv 64 F3),
    forall (C472 : L5.u64_at RSEGS M14 (Sp - 472) F3),
    forall (C448 : L5.u64_at RSEGS M14 (Sp - 448) F3),
    forall (C368 : L5.u64_at RSEGS M14 (Sp - 368) F3),
    forall (C416 : L5.u64_at RSEGS M14 (Sp - 416) (F3 + 32)),
    forall (C400 : L5.u64_at RSEGS M14 (Sp - 400) xo),
    forall (C376 : L5.u64_at RSEGS M14 (Sp - 376) xo),
    forall (C232 : L5.u64_at RSEGS M14 (Sp - 232) (F3 + 48)),
    forall (C224 : L5.u64_at RSEGS M14 (Sp - 224) 0),
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
    forall (FRL3 : L5DSA.fr_live L ar LB ((F1, 1, Sp - 80) :: FF) M 3 F3 fl3 (Sp - 464)),
    forall (FRL1 : L5DSA.fr_live L ar LB FF M 1 F1 fl1 (Sp - 80)),
    forall (AHP0 : ahpres L ar LB FF Sp SCR [] M0 M),
    forall (G1 : getr R0 1 = Z_to_bv 64 584500),
    forall (G2 : getr R0 2 = Z_to_bv 64 Sp),
    forall (G3 : getr R0 3 = Z_to_bv 64 67584),
    forall (G4 : getr R0 4 = Z_to_bv 64 6363400),
    forall (G9 : getr R0 9 = Z_to_bv 64 (Sp + 16)),
    forall (S32 : Sp mod 32 = 16),
    forall (RT8 : L5.u64_at RSEGS M14 Sp (nz rt8)),
    forall (RTRA : L5.u64_at RSEGS M14 (Sp + 8) 582404),
    forall (EC0 : L5.u64_at RSEGS M14 6360520 0),
    forall (GD0 : L5.u8_at RSEGS M14 6361072 (if gd then 1 else 0)),
    forall (GD1 : L5.u8_at RSEGS M14 6361073 (if gd then 1 else 0)),
    forall (TDL : L5.u64_at RSEGS M14 6363352 6495184),
    forall (MSG0 : L5.u64_at RSEGS M14 6495224 0),
    forall (ERR : L5.u32_at RSEGS M14 6363236 errv),
    forall (ERRR : 0 <= errv < 2 ^ 64),
    forall (CAN : L5.u64_at RSEGS M14 6494536 canary),
    forall (AUXP : L5.u64_at RSEGS M14 6495136 av),
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
    forall (KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LK' : list fframe) (A' : list (Z * Z)), L5OMA.landed_regs R0 R' Sp rt8 -> L5USA.e2_landed L {| L5USA.xs_gd := gd; L5USA.xs_fl := fl; L5USA.xs_av := av; L5USA.xs_uid := uid; L5USA.xs_rnd := rnd; L5USA.xs_canary := canary; L5USA.xs_hw := hw |} LB FF LK cr (Sp + 16) M' R' LB' cr' LK' -> ahpres L ar LB FF Sp SCR L5USA.xs_foot M M' -> model_rt model model' -> incl A A' -> amodel_ok A' model' -> ri_inv HI LB' FF LK' cr' A' M' (vml_of model') -> srealizes RSEGS SCFG (cfg (fx:=fx') R' 583040 M' model') K),
    forall (U01 : L5DSA.U R0 1 = 584500),
    forall (U09 : L5DSA.U R0 9 = Sp + 16),
    forall (FRO1 : L5.u64_at RSEGS M14 (Sp - 104) F1),
    forall (E8 : bv_unsigned (getr R (reg 8)) = Sp - 496 + 384),
    forall (E9 : bv_unsigned (getr R (reg 9)) = Sp - 496),
    forall (FL0 : L5.u8_at RSEGS M14 6363185 (if fl then 1 else 0)),
    forall (FL2 : L5.u8_at RSEGS M14 6363187 (if fl then 1 else 0)),
    forall (FL4 : L5.u8_at RSEGS M14 6363189 (if fl then 1 else 0)),
    forall (A16 : Sp mod 16 = 0),
    forall (SLO : ahl_ceil ar + 4096 + SCR <= Sp),
    forall (SHI : Sp <= ar_sptop ar),
    forall (SPT : 140735340871680 <= ar_sptop ar <= 2 ^ 47),
    forall (AVT : Sp + 16 <= av),
    forall (HS0 : 0 <= SCR),
    forall (ALS : (Sp - 496) mod 16 = 0),
    forall (ALS8 : (Sp - 496) mod 8 = 0),
    forall (SPR0 : 0 <= Sp - 496 < 2 ^ 64),
    forall (SPLO : 140735332552704 <= Sp - 496),
    forall (SPHI : Sp - 496 <= 140737488355264),
    forall (LY2 : as0_layout2 L),
    forall (HTP : hl_tp L = 6363400),
    forall (FN : numg (ar_fs ar <= F3 /\ F3 + 512 <= ar_fs ar + 11571200 /\ ar_fs ar <= F1 /\ F1 + 128 <= ar_fs ar + 11571200 /\ ar_fs ar <= fl1 < ar_fs ar + 11571200 /\ ar_fs ar <= fl3 < ar_fs ar + 11571200 /\ 6504448 <= ar_fs ar /\ ar_fs ar + 11571200 <= ahl_ceil ar /\ 0 <= F1 / 8 <= 2 ^ 44 /\ 0 <= F3 / 8 <= 2 ^ 44)),
    forall (F3A : F3 mod 512 = 0),
    forall (F1A : F1 mod 128 = 0),
    forall (DJF : ar_fs ar + 11571200 <= 2147446784 \/ 2147446784 + 17592186048512 <= ar_fs ar),
    forall (EX0 : forall x : nat, In x KS_ue2a1 -> getr R1 (reg x) = getr R (reg x)),
    forall (EX1 : getr R1 (reg 1) = Z_to_bv 64 727044),
    forall (EX2 : getr R1 (reg 2) = Z_to_bv 64 (Sp - 496 - 48)),
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
    forall (EX11 : getr R3 (reg 1) = Z_to_bv 64 604308),
    forall (EX12 : getr R3 (reg 2) = Z_to_bv 64 (Sp - 496)),
    forall (EX13 : getr R3 (reg 8) = Z_to_bv 64 (Sp - 496 + 384)),
    forall (EX14 : getr R3 (reg 9) = Z_to_bv 64 (Sp - 496)),
    forall (EX15 : getr R3 (reg 10) = Z_to_bv 64 obj),
    forall (EX16 : getr R3 (reg 11) = Z_to_bv 64 142528),
    forall (EX17 : getr R3 (reg 19) = Z_to_bv 64 obj),
    forall (Z72 : L5KA.zeros_at M14 (obj - 72) 4),
    forall (E10 : bv_unsigned (getr R3 (reg 10)) = obj),
    forall (EX5 : forall x : nat, In x KS_ue2c1 -> getr R4 (reg x) = getr R3 (reg x)),
    forall (EX6 : getr R4 (reg 1) = Z_to_bv 64 731600),
    forall (EX19 : getr R4 (reg 2) = Z_to_bv 64 (Sp - 496 - 48)),
    forall (EX20 : getr R4 (reg 8) = getr R3 (reg 10)),
    forall (EX21 : getr R4 (reg 9) = Z_to_bv 64 142528),
    forall (EX22 : getr R4 (reg 10) = Z_to_bv 64 142528),
    forall (EX23 : L5.u64_at RSEGS M14 obj 876464),
    forall (R4_8 : getr R4 (reg 8) = Z_to_bv 64 obj),
    forall (sR5 : getr R5 (reg 10) = Z_to_bv 64 12),
    forall (RP5 : regs_preserved R4 R5),
    forall (EX7 : forall x : nat, In x KS_ue2c2 -> getr R6 (reg x) = getr R5 (reg x)),
    forall (EX8 : getr R6 (reg 1) = Z_to_bv 64 859152),
    forall (EX9 : getr R6 (reg 2) = Z_to_bv 64 (Sp - 496 - 64)),
    forall (EX18 : getr R6 (reg 8) = Z_to_bv 64 37),
    forall (EX29 : getr R6 (reg 10) = Z_to_bv 64 37),
    forall (EX30 : getr R6 (reg 18) = Z_to_bv 64 12),
    forall (ACR2 : acredit_ok L (adebit L cr 144) 37),
    forall (mR7 : getr R7 (reg 10) = Z_to_bv 64 ref),
    forall (RP7 : regs_preserved R6 R7),
    forall (RF16 : ref mod 16 = 0),
    forall (NUM : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR) /\ (0 <= Sp - 496 < 2 ^ 64 /\ 140735332552704 <= Sp - 496 <= 140737488355264) /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47 /\ Sp + 16 <= av) /\ (obj = u + 128 /\ 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 16 <= ahl_ceil ar) /\ 17594333495296 <= ref /\ ref + 37 <= ahl_ceil ar /\ (ref + 37 <= u \/ u + 144 <= ref))),
    forall (EX33 : forall x : nat, In x KS_ue2c3 -> getr R8 (reg x) = getr R7 (reg x)),
    forall (EX34 : getr R8 (reg 1) = Z_to_bv 64 731644),
    forall (EX35 : getr R8 (reg 2) = Z_to_bv 64 (Sp - 496 - 48)),
    forall (EX36 : getr R8 (reg 8) = Z_to_bv 64 obj),
    forall (EX37 : getr R8 (reg 10) = Z_to_bv 64 (ref + 24)),
    forall (EX38 : getr R8 (reg 11) = Z_to_bv 64 142528),
    forall (EX39 : getr R8 (reg 12) = Z_to_bv 64 13),
    forall (EX40 : getr R8 (reg 19) = Z_to_bv 64 (ref + 24)),
    forall (EX41 : L5.u32_at RSEGS M14 (ref + 16) 0),
    forall (EX42 : L5.u64_at RSEGS M14 (ref + 8) 12),
    forall (EX43 : L5.u64_at RSEGS M14 ref 12),
    forall (HMC : amemcpy_spec_at L ar SCFG HI 385872 false),
    forall (mR9 : getr R9 (reg 10) = Z_to_bv 64 (ref + 24)),
    forall (RP9 : regs_preserved R8 R9),
    forall (EX31 : forall x : nat, In x KS_ue2c4 -> getr R10 (reg x) = getr R9 (reg x)),
    forall (EX32 : getr R10 (reg 1) = Z_to_bv 64 604344),
    forall (EX44 : getr R10 (reg 2) = Z_to_bv 64 (Sp - 496)),
    forall (EX45 : getr R10 (reg 8) = Z_to_bv 64 (Sp - 496 + 384)),
    forall (EX46 : getr R10 (reg 9) = Z_to_bv 64 (Sp - 496)),
    forall (EX47 : getr R10 (reg 18) = Z_to_bv 64 (F3 / 8 + SB)),
    forall (EX48 : getr R10 (reg 19) = Z_to_bv 64 obj),
    forall (EX49 : L5.u64_at RSEGS M14 (obj + 8) (ref + 24)),
    forall (RP11 : regs_preserved R10 R11),
    forall (EX24 : forall x : nat, In x KS_ue2c5 -> getr R12 (reg x) = getr R11 (reg x)),
    forall (EX25 : getr R12 (reg 10) = Z_to_bv 64 obj),
    forall (EX26 : getr R12 (reg 11) = Z_to_bv 64 876704),
    forall (EX : getr R12 (reg 12) = Z_to_bv 64 721816),
    forall (E12_10 : bv_unsigned (getr R12 (reg 10)) = obj),
    forall (EX28 : forall x : nat, In x KS_ue2t1 -> getr R13 (reg x) = getr R12 (reg x)),
    forall (EX50 : getr R13 (reg 1) = Z_to_bv 64 343964),
    forall (EX51 : getr R13 (reg 2) = Z_to_bv 64 (Sp - 496 - 64)),
    forall (EX52 : getr R13 (reg 8) = Z_to_bv 64 (obj - 32)),
    forall (EX53 : getr R13 (reg 9) = Z_to_bv 64 884616),
    forall (EX54 : getr R13 (reg 10) = Z_to_bv 64 (obj - 32)),
    forall (EX55 : getr R13 (reg 11) = Z_to_bv 64 746772),
    forall (EX56 : getr R13 (reg 12) = Z_to_bv 64 725624),
    forall (EX57 : getr R13 (reg 18) = getr R12 (reg 10)),
    forall (EX58 : L5.u64_at RSEGS M14 (Sp - 496 - 56) 876704),
    forall (EX59 : L5.u64_at RSEGS M14 (Sp - 496 - 48) (obj - 128)),
    forall (EX60 : L5.u64_at RSEGS M14 (Sp - 496 - 40) 725808),
    forall (EX61 : L5.u64_at RSEGS M14 (obj - 120) 1),
    forall (EX62 : L5.u64_at RSEGS M14 (obj - 24) 725624),
    forall (EX63 : L5.u64_at RSEGS M14 (obj - 32) 4849336966747728640),
    forall (EX64 : L5.u64_at RSEGS M14 (obj - 88) 610700),
    forall (EX65 : L5.u64_at RSEGS M14 (obj - 104) 721816),
    forall (EX66 : L5.u64_at RSEGS M14 (obj - 112) 876704),
    forall (EX67 : L5.u64_at RSEGS M14 (obj - 96) 610968),
    forall (EX68 : L5.u64_at RSEGS M14 (Sp - 496 - 64) obj),
    forall (EX69 : L5.u32_at RSEGS M14 6360528 1),
    forall (EX70 : L5.u64_at RSEGS M14 (Sp - 496 - 32) (F3 / 8 + SB)),
    forall (EX71 : L5.u64_at RSEGS M14 (Sp - 496 - 24) (Sp - 496)),
    forall (EX72 : L5.u64_at RSEGS M14 (Sp - 496 - 16) (Sp - 496 + 384)),
    forall (EX73 : L5.u64_at RSEGS M14 (Sp - 496 - 8) 604368),
    forall (RP14 : regs_preserved R13 R14),
    forall (CI14 : cinv L ar HI M model A LB (L5DSA.ff_e2 FF Sp F1 F3) Sp SCR XW [(ref, 37); (u, 144)] M14 model14 LKt (adebit L (adebit L cr 144) 37) A7),
    forall (FL1 : fl = true -> L5.u8_at RSEGS M14 6363186 0),
    forall (FL3 : fl = true -> L5.u8_at RSEGS M14 6363188 0),
    forall (FL5 : fl = true -> L5.u8_at RSEGS M14 6363190 0),
    forall (AUXV : forall j : nat, (j < 20)%nat -> L5.u64_at RSEGS M14 (av + 8 * Z.of_nat j) (nth j (L5USA.auxv20A uid rnd hw) 0)),
    forall (FRD : forall j : nat, (j < 13)%nat -> L5.u64_at RSEGS M14 (Sp - 216 + 8 * Z.of_nat j) (nth j [L5DSA.U R0 27; L5DSA.U R0 26; L5DSA.U R0 25; L5DSA.RETIRE_MAGIC; F1; F1 / 8 + SB; F1 + 32; nz bo; nz xo; F1; Sp - 112; Sp; L5DSA.DIV_RET_O] 0)),
    forall (FRO : forall j : nat, (j < 10)%nat -> L5.u64_at RSEGS M14 (Sp - 80 + 8 * Z.of_nat j) (nth j [L5DSA.U R0 24; L5DSA.U R0 23; L5DSA.U R0 22; L5DSA.U R0 21; L5DSA.U R0 20; L5DSA.U R0 19; L5DSA.U R0 18; Sp + 16; L5DSA.U R0 8; 584500] 0)),
    forall (IC1 : L5.img_clear M14 65536 884736),
    forall (IC2 : L5.img_clear M14 895824 895856),
    forall (IC3 : L5.img_clear M14 895872 (895872 + 8)),
  srealizes RSEGS SCFG (cfg (fx:=fx14) R14 343964 M14 model14) K.
Proof.
  intros.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct (cv_tls L ar C IL HI LY ILY HIok ICok UNWL M model A LB (L5DSA.ff_e2 FF Sp F1 F3) Sp SCR XW _ _ _ _ _ _ CI14) as (ctx & th & tbv & tev & blk & TLSC & TLSR & TLSI & TLSP & TLSB).
  cbv zeta in TLSC. rewrite HTP in TLSC. change (6363400 + 8) with 6363408 in TLSC. destruct TLSC as (TC1 & TC2 & TC3 & TC4 & TC5 & TC6).
  pose proof (TLSB ref 37 ltac:(left; reflexivity)) as TB1. pose proof (TLSB u 144 ltac:(right; left; reflexivity)) as TB2. clear TLSB.
  assert (NUM4 : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR)
                      /\ (0 <= Sp - 496 < 2 ^ 64 /\ 140735332552704 <= Sp - 496 /\ Sp - 496 <= 140737488355264)
                      /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47 /\ Sp + 16 <= av)
                      /\ (obj = u + 128 /\ 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 16 <= ahl_ceil ar)
                      /\ (17594333495296 <= ref /\ ref + 37 <= ahl_ceil ar)
                      /\ (4096 <= ctx /\ ctx + 160 <= ahl_ceil ar /\ 4096 <= th /\ th + 64 <= ahl_ceil ar /\ 4096 <= blk /\ blk + 4096 <= ahl_ceil ar /\ 0 <= tbv < 2 ^ 64 /\ 0 <= tev < 2 ^ 64))).
  { unfold numf in *. clear - NUM TLSR. lia. }
  assert (DJ0 : ref + 37 <= u \/ u + 144 <= ref) by (unfold numf in NUM; clear - NUM; lia).
  destruct TLSI as (DJ1 & DJ2 & DJ3). destruct TLSP as (DJ4 & DJ5 & DJ6). destruct TB1 as (DJ7 & DJ8 & DJ9). destruct TB2 as (DJ10 & DJ11 & DJ12).
  clear NUM. rename NUM4 into NUM. clear TLSR.
  assert (AV8' : av mod 8 = 0) by exact AV8.
  (* [comment removed for export] *)
  expand_arr AUXV 20%nat. expand_arr FRD 13%nat. expand_arr FRO 10%nat.
  (* [comment removed for export] *)
  remember {| L5USA.xs_gd := gd; L5USA.xs_fl := fl; L5USA.xs_av := av; L5USA.xs_uid := uid; L5USA.xs_rnd := rnd; L5USA.xs_canary := canary; L5USA.xs_hw := hw |} as st eqn:Est in KONT.
  assert (STE : L5USA.xs_gd st = gd /\ L5USA.xs_av st = av /\ L5USA.xs_uid st = uid /\ L5USA.xs_rnd st = rnd /\ L5USA.xs_canary st = canary /\ L5USA.xs_hw st = hw) by (rewrite Est; repeat split; reflexivity).
  clear Est.
  destruct fl; cbv iota in FL0, FL2, FL4.
  - (* [comment removed for export] *)
    specialize (FL1 eq_refl). specialize (FL3 eq_refl). specialize (FL5 eq_refl).
    pose proof (ue2t2_v1_conc HFILL HCOPY HTLS fx14 R14 (mrestrict (ahid A7 model14) M14)
                  (fun j => match j with 2%nat => Sp - 496 | 10%nat => obj | 32%nat => av | 33%nat => canary | 34%nat => uid | 36%nat => rnd | 39%nat => hw | 40%nat => U R14 10
                                    | 41%nat => ctx | 42%nat => th | 43%nat => blk | 44%nat => tbv | 45%nat => tev | 46%nat => 876704 | 47%nat => F3 / 8 + SB
                                    | 48%nat => F1 | 49%nat => nz xo | 50%nat => nz bo | 51%nat => F1 + 32 | 52%nat => F1 / 8 + SB | 53%nat => F1 | 54%nat => L5DSA.RETIRE_MAGIC
                                    | 55%nat => L5DSA.U R0 25 | 56%nat => L5DSA.U R0 26 | 57%nat => L5DSA.U R0 27 | 58%nat => L5DSA.U R0 8
                                    | 59%nat => L5DSA.U R0 18 | 60%nat => L5DSA.U R0 19 | 61%nat => L5DSA.U R0 20 | 62%nat => L5DSA.U R0 21 | 63%nat => L5DSA.U R0 22
                                    | 64%nat => L5DSA.U R0 23 | 65%nat => L5DSA.U R0 24 | 66%nat => nz rt8 | _ => 0 end)) as P. cbn beta iota in P.
    feed_rng P ltac:(first [ apply nz_range | apply UR | apply BL.bvu_range | (unfold L5DSA.U; apply BL.bvu_range) | nlia | (unfold SB, L5DSA.RETIRE_MAGIC; unfold numg in FN; clear - FN; lia) ]).
    piece_step CI14 XWIMG P (fun a => Sp - 496 - 10608 <= a < Sp - 496 - 10608 + 10544 \/ obj - 68 <= a < obj - 68 + 68 \/ Sp - 496 - 64 <= a < Sp - 496 - 64 + 8 \/ Sp - 496 - 56 <= a < Sp - 496 - 56 + 8
                                       \/ Sp - 496 - 48 <= a < Sp - 496 - 48 + 8 \/ Sp - 496 - 40 <= a < Sp - 496 - 40 + 8 \/ 6363185 <= a < 6363185 + 6) fx15 R15 M15 model15 CI15.
    repeat match goal with H : L5.u64_at _ M15 (av + 8 * _) _ |- _ => clear H | H : L5.u64_at _ M15 (Sp - 216 + 8 * _) _ |- _ => clear H | H : L5.u64_at _ M15 (Sp - 80 + 8 * _) _ |- _ => clear H end.
    clear TC1 TC2 TC3 TC4 TC5 TC6 DJ1 DJ2 DJ3 DJ4 DJ5 DJ6 DJ7 DJ8 DJ9 DJ10 DJ11 DJ12.
    assert (NUM5 : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR)
                      /\ (0 <= Sp - 496 < 2 ^ 64 /\ 140735332552704 <= Sp - 496 /\ Sp - 496 <= 140737488355264)
                      /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47 /\ Sp + 16 <= av)
                      /\ (obj = u + 128 /\ 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 16 <= ahl_ceil ar)
                      /\ (17594333495296 <= ref /\ ref + 37 <= ahl_ceil ar))) by (unfold numf in *; clear - NUM; lia).
    clear NUM. rename NUM5 into NUM. clear ctx th tbv tev blk.
    tidy CI15.
    apply (L5BE2S4.e2_s4 L ar C IL HI LY ILY HIok ICok HFILL HCOPY HTLS UNWL R0 M0 R M model K LB FF LK LKt cr A Sp SCR xo bo F1 fl1 F3 fl3 rt8 gd av uid rnd canary hw fden v16 v24 errv R1 R2 A2 u obj R3 R4 R5 R6 R7 A7 ref R8 R9 R10 R11 R12 R13 R14 M15 st fx15 R15 model15); assumption.
  - (* [comment removed for export] *)
    clear FL1 FL3 FL5.
    pose proof (ue2t2_v0_conc HFILL HCOPY HTLS fx14 R14 (mrestrict (ahid A7 model14) M14)
                  (fun j => match j with 2%nat => Sp - 496 | 10%nat => obj | 32%nat => av | 33%nat => canary | 34%nat => uid | 36%nat => rnd | 39%nat => hw | 40%nat => U R14 10
                                    | 41%nat => ctx | 42%nat => th | 43%nat => blk | 44%nat => tbv | 45%nat => tev | 46%nat => 876704 | 47%nat => F3 / 8 + SB
                                    | 48%nat => F1 | 49%nat => nz xo | 50%nat => nz bo | 51%nat => F1 + 32 | 52%nat => F1 / 8 + SB | 53%nat => F1 | 54%nat => L5DSA.RETIRE_MAGIC
                                    | 55%nat => L5DSA.U R0 25 | 56%nat => L5DSA.U R0 26 | 57%nat => L5DSA.U R0 27 | 58%nat => L5DSA.U R0 8
                                    | 59%nat => L5DSA.U R0 18 | 60%nat => L5DSA.U R0 19 | 61%nat => L5DSA.U R0 20 | 62%nat => L5DSA.U R0 21 | 63%nat => L5DSA.U R0 22
                                    | 64%nat => L5DSA.U R0 23 | 65%nat => L5DSA.U R0 24 | 66%nat => nz rt8 | _ => 0 end)) as P. cbn beta iota in P.
    feed_rng P ltac:(first [ apply nz_range | apply UR | apply BL.bvu_range | (unfold L5DSA.U; apply BL.bvu_range) | nlia | (unfold SB, L5DSA.RETIRE_MAGIC; unfold numg in FN; clear - FN; lia) ]).
    piece_step CI14 XWIMG P (fun a => Sp - 496 - 10608 <= a < Sp - 496 - 10608 + 10544 \/ obj - 68 <= a < obj - 68 + 68 \/ Sp - 496 - 64 <= a < Sp - 496 - 64 + 8 \/ Sp - 496 - 56 <= a < Sp - 496 - 56 + 8
                                       \/ Sp - 496 - 48 <= a < Sp - 496 - 48 + 8 \/ Sp - 496 - 40 <= a < Sp - 496 - 40 + 8 \/ 6363185 <= a < 6363185 + 6) fx15 R15 M15 model15 CI15.
    repeat match goal with H : L5.u64_at _ M15 (av + 8 * _) _ |- _ => clear H | H : L5.u64_at _ M15 (Sp - 216 + 8 * _) _ |- _ => clear H | H : L5.u64_at _ M15 (Sp - 80 + 8 * _) _ |- _ => clear H end.
    clear TC1 TC2 TC3 TC4 TC5 TC6 DJ1 DJ2 DJ3 DJ4 DJ5 DJ6 DJ7 DJ8 DJ9 DJ10 DJ11 DJ12.
    assert (NUM5 : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR)
                      /\ (0 <= Sp - 496 < 2 ^ 64 /\ 140735332552704 <= Sp - 496 /\ Sp - 496 <= 140737488355264)
                      /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47 /\ Sp + 16 <= av)
                      /\ (obj = u + 128 /\ 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 16 <= ahl_ceil ar)
                      /\ (17594333495296 <= ref /\ ref + 37 <= ahl_ceil ar))) by (unfold numf in *; clear - NUM; lia).
    clear NUM. rename NUM5 into NUM. clear ctx th tbv tev blk.
    tidy CI15.
    apply (L5BE2S4.e2_s4 L ar C IL HI LY ILY HIok ICok HFILL HCOPY HTLS UNWL R0 M0 R M model K LB FF LK LKt cr A Sp SCR xo bo F1 fl1 F3 fl3 rt8 gd av uid rnd canary hw fden v16 v24 errv R1 R2 A2 u obj R3 R4 R5 R6 R7 A7 ref R8 R9 R10 R11 R12 R13 R14 M15 st fx15 R15 model15); assumption.
Qed.

End WithIface.
End SCFG_1.
End L5BE2S3.
