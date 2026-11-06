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
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ParseSpecsA L5OpmodSpecsA L5DivSpecsA L5UnwindSpecsA XIcptA XIcptAs0Kit L5AUnwK L5AUnwK2 L5AE1K L5AE1P1 L5AE1P2 L5AE1P3 L5AE1P4 L5AE1P5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Set Printing Width 100000. Set Printing Depth 100000.

Module L5AE1S5.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5AUK. Import L5AUK2.
Import L5AE1P1.L5AE1P1. Import L5AE1P2.L5AE1P2. Import L5AE1P3.L5AE1P3. Import L5AE1P4.L5AE1P4. Import L5AE1P5.L5AE1P5.
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
Local Notation XW := [(6357456, 4); (6360113, 6); (6358000, 8); (6360164, 4)].
Local Notation XWIMG := (L5AE1K.xw_img L UNWL).

Lemma e1_s5 :
  forall (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF : list fframe) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (Sp : Z) (SCR : Z) (s0v : Z) (s2v : Z) (gd : bool) (fl : bool) (av : Z) (uid : Z) (rnd : Z) (canary : Z) (hw : Z) (errv : Z) (R1 : bvmap 5 word) (R2 : bvmap 5 word) (A2 : list (Z * Z)) (u : Z) (obj : Z) (R3 : bvmap 5 word) (R4 : bvmap 5 word) (R5 : bvmap 5 word) (R6 : bvmap 5 word) (R7 : bvmap 5 word) (R8 : bvmap 5 word) (R9 : bvmap 5 word) (R10 : bvmap 5 word) (R11 : bvmap 5 word) (R12 : bvmap 5 word) (R13 : bvmap 5 word) (R14 : bvmap 5 word) (A14 : list (Z * Z)) (ref : Z) (R15 : bvmap 5 word) (R16 : bvmap 5 word) (R17 : bvmap 5 word) (R18 : bvmap 5 word) (R19 : bvmap 5 word) (M21 : word -> option byte) (R20 : bvmap 5 word) (fx21 : FPState) (R21 : bvmap 5 word) (model21 : Model),
    forall (G2 : getr R (reg 2) = Z_to_bv 64 (Sp - 32)),
    forall (G3 : getr R (reg 3) = Z_to_bv 64 67584),
    forall (G4 : getr R (reg 4) = Z_to_bv 64 6360328),
    forall (G9 : getr R (reg 9) = Z_to_bv 64 22),
    forall (G18 : getr R (reg 18) = Z_to_bv 64 SB),
    forall (S32 : Sp mod 32 = 0),
    forall (C8 : L5.u64_at RSEGS M21 (Sp - 8) 581732),
    forall (C16 : L5.u64_at RSEGS M21 (Sp - 16) s0v),
    forall (C24 : L5.u64_at RSEGS M21 (Sp - 24) Sp),
    forall (C32 : L5.u64_at RSEGS M21 (Sp - 32) s2v),
    forall (S0R : 0 <= s0v < 2 ^ 64),
    forall (S2R : 0 <= s2v < 2 ^ 64),
    forall (EC0 : L5.u64_at RSEGS M21 6357448 0),
    forall (TDL : L5.u64_at RSEGS M21 6360280 6492112),
    forall (MSG0 : L5.u64_at RSEGS M21 6492152 0),
    forall (ERRR : 0 <= errv < 2 ^ 64),
    forall (CAN : L5.u64_at RSEGS M21 6491464 canary),
    forall (AUXP : L5.u64_at RSEGS M21 6492064 av),
    forall (AV8 : av mod 8 = 0),
    forall (AVLO : 2 ^ 40 <= av),
    forall (AVHI : av + 160 <= 2 ^ 47),
    forall (UIDR : 0 <= uid < 2 ^ 64),
    forall (RNDR : 0 <= rnd < 2 ^ 64),
    forall (CANR : 0 <= canary < 2 ^ 64),
    forall (HWR : 0 <= hw < 2 ^ 64),
    forall (AVS : ar_sptop ar <= av),
    forall (HH : ri_inv HI LB FF LK cr A M (vml_of model)),
    forall (AM : amodel_ok A model),
    forall (HK : K []),
    forall (STK : astk ar M Sp SCR),
    forall (HSCR : 69632 <= SCR),
    forall (SCR8 : SCR mod 8 = 0),
    forall (SH : L5OMA.stksh ar M (Sp - SCR)),
    forall (CRF : L5OMA.acredit_for L cr 2 (160 + 41)),
    forall (KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LK' : list fframe) (A' : list (Z * Z)), getr R' 8 = Z_to_bv 64 s0v -> getr R' 9 = Z_to_bv 64 Sp -> getr R' 18 = Z_to_bv 64 s2v -> (forall i : nat, In i [3%nat; 4%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat] -> getr R' (reg i) = getr R (reg i)) -> L5USA.e1_landed L {| L5USA.xs_gd := gd; L5USA.xs_fl := fl; L5USA.xs_av := av; L5USA.xs_uid := uid; L5USA.xs_rnd := rnd; L5USA.xs_canary := canary; L5USA.xs_hw := hw |} LB FF LK cr Sp M' R' LB' cr' LK' -> ahpres L ar LB FF Sp SCR L5USA.xs_foot1 M M' -> model_rt model model' -> incl A A' -> amodel_ok A' model' -> ri_inv HI LB' FF LK' cr' A' M' (vml_of model') -> srealizes RSEGS SCFG (cfg (fx:=fx') R' 582360 M' model') K),
    forall (FL0 : L5.u8_at RSEGS M21 6360113 (if fl then 1 else 0)),
    forall (FL2 : L5.u8_at RSEGS M21 6360115 (if fl then 1 else 0)),
    forall (FL4 : L5.u8_at RSEGS M21 6360117 (if fl then 1 else 0)),
    forall (A16 : Sp mod 16 = 0),
    forall (SLO : ahl_ceil ar + 4096 + SCR <= Sp),
    forall (SHI : Sp <= ar_sptop ar),
    forall (SPT : 140735340871680 <= ar_sptop ar <= 2 ^ 47),
    forall (HS0 : 0 <= SCR),
    forall (ALS : (Sp - 32) mod 16 = 0),
    forall (ALS8 : (Sp - 32) mod 8 = 0),
    forall (SPR0 : 0 <= Sp - 32 < 2 ^ 64),
    forall (SPLO : 140735332552704 <= Sp - 32),
    forall (SPHI : Sp - 32 <= 140737488355264),
    forall (LY2 : as0_layout2 L),
    forall (HTP : hl_tp L = 6360328),
    forall (E9 : bv_unsigned (getr R (reg 9)) = 22),
    forall (EX0 : forall x : nat, In x KS_ue1a1 -> getr R1 (reg x) = getr R (reg x)),
    forall (EX1 : getr R1 (reg 1) = Z_to_bv 64 723952),
    forall (EX2 : getr R1 (reg 2) = Z_to_bv 64 (Sp - 32 - 48)),
    forall (EX3 : getr R1 (reg 8) = Z_to_bv 64 160),
    forall (EX4 : getr R1 (reg 10) = Z_to_bv 64 16),
    forall (EX5 : getr R1 (reg 11) = Z_to_bv 64 160),
    forall (ACR1 : acredit_ok L cr 160),
    forall (CRF1 : L5OMA.acredit_for L (adebit L cr 160) 1 41),
    forall (RP2 : regs_preserved R1 R2),
    forall (EOBJ : obj = u + 128),
    forall (OB16 : obj mod 16 = 0),
    forall (OB8 : obj mod 8 = 0),
    forall (OBR0 : 0 <= obj < 2 ^ 64),
    forall (OBR : 17594333495424 <= obj <= 140737479966720),
    forall (OCEIL : obj + 32 <= ahl_ceil ar),
    forall (EX11 : forall x : nat, In x KS_ue1a2_mh -> getr R3 (reg x) = getr R2 (reg x)),
    forall (EX12 : getr R3 (reg 1) = Z_to_bv 64 583704),
    forall (EX13 : getr R3 (reg 2) = Z_to_bv 64 (Sp - 32)),
    forall (EX14 : getr R3 (reg 8) = Z_to_bv 64 obj),
    forall (EX15 : getr R3 (reg 9) = Z_to_bv 64 22),
    forall (EX16 : getr R3 (reg 10) = Z_to_bv 64 obj),
    forall (Z72 : L5KA.zeros_at M21 (obj - 72) 4),
    forall (EX7 : getr R4 (reg 1) = Z_to_bv 64 583712),
    forall (EX18 : getr R4 (reg 10) = getr R3 (reg 8)),
    forall (EX19 : getr R4 (reg 11) = getr R3 (reg 9)),
    forall (EX20 : getr R4 (reg 12) = Z_to_bv 64 892784),
    forall (EX21 : L5.u8_at RSEGS M21 6358001 1),
    forall (EX : L5.u8_at RSEGS M21 6358000 1),
    forall (KS4 : forall x : nat, In x cs_all -> getr R4 (reg x) = getr R3 (reg x)),
    forall (R4_10 : getr R4 (reg 10) = Z_to_bv 64 obj),
    forall (R4_11 : getr R4 (reg 11) = Z_to_bv 64 22),
    forall (VPT : L5.u64_at RSEGS M21 892784 873976),
    forall (EX8 : forall x : nat, In x KS_ue1c1 -> getr R5 (reg x) = getr R4 (reg x)),
    forall (EX9 : getr R5 (reg 1) = Z_to_bv 64 728756),
    forall (EX10 : getr R5 (reg 2) = Z_to_bv 64 (Sp - 32 - 1184)),
    forall (EX22 : getr R5 (reg 8) = Z_to_bv 64 (Sp - 32 - 56)),
    forall (EX23 : getr R5 (reg 9) = Z_to_bv 64 (Sp - 32 - 1168)),
    forall (EX24 : getr R5 (reg 10) = Z_to_bv 64 22),
    forall (EX25 : getr R5 (reg 11) = Z_to_bv 64 (Sp - 32 - 1168)),
    forall (EX26 : getr R5 (reg 12) = Z_to_bv 64 1024),
    forall (EX27 : getr R5 (reg 13) = Z_to_bv 64 729140),
    forall (EX28 : getr R5 (reg 18) = Z_to_bv 64 6360164),
    forall (EX29 : getr R5 (reg 19) = Z_to_bv 64 22),
    forall (mR10 : getr R6 (reg 10) = Z_to_bv 64 0),
    forall (RP6 : regs_preserved R5 R6),
    forall (EX43 : forall x : nat, In x KS_ue1c2 -> getr R7 (reg x) = getr R6 (reg x)),
    forall (EX44 : getr R7 (reg 1) = Z_to_bv 64 728836),
    forall (EX45 : getr R7 (reg 10) = Z_to_bv 64 (Sp - 32 - 1168)),
    forall (EX6 : L5.u32_at RSEGS M21 6360164 (bv_unsigned (getr R6 (reg 20)))),
    forall (sR10 : getr R8 (reg 10) = Z_to_bv 64 16),
    forall (RP8 : regs_preserved R7 R8),
    forall (EX47 : forall x : nat, In x KS_ue1c3 -> getr R9 (reg x) = getr R8 (reg x)),
    forall (EX48 : getr R9 (reg 1) = Z_to_bv 64 728940),
    forall (EX49 : getr R9 (reg 10) = Z_to_bv 64 (Sp - 32 - 55)),
    forall (EX50 : getr R9 (reg 11) = Z_to_bv 64 (Sp - 32 - 1168)),
    forall (EX51 : getr R9 (reg 12) = Z_to_bv 64 16),
    forall (EX52 : getr R9 (reg 18) = Z_to_bv 64 16),
    forall (EX53 : getr R9 (reg 19) = Z_to_bv 64 (Sp - 32 - 55)),
    forall (HMM : amemcpy_spec_at L ar SCFG HI 385228 false),
    forall (mvR10 : getr R10 (reg 10) = Z_to_bv 64 (Sp - 32 - 55)),
    forall (RP10 : regs_preserved R9 R10),
    forall (EX55 : forall x : nat, In x KS_ue1c4 -> getr R11 (reg x) = getr R10 (reg x)),
    forall (EX56 : getr R11 (reg 1) = Z_to_bv 64 728356),
    forall (EX57 : getr R11 (reg 2) = Z_to_bv 64 (Sp - 32 - 112)),
    forall (EX58 : getr R11 (reg 8) = Z_to_bv 64 obj),
    forall (EX59 : getr R11 (reg 9) = Z_to_bv 64 (Sp - 32 - 55)),
    forall (EX60 : getr R11 (reg 10) = Z_to_bv 64 (Sp - 32 - 55)),
    forall (EX61 : getr R11 (reg 11) = Z_to_bv 64 (Sp - 32 - 56)),
    forall (EX62 : getr R11 (reg 18) = Z_to_bv 64 22),
    forall (EX63 : getr R11 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R4 (reg 19)))),
    forall (EX64 : getr R11 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R4 (reg 20)))),
    forall (sR12 : getr R12 (reg 10) = Z_to_bv 64 16),
    forall (RP12 : regs_preserved R11 R12),
    forall (EX30 : forall x : nat, In x KS_ue1c5 -> getr R13 (reg x) = getr R12 (reg x)),
    forall (EX31 : getr R13 (reg 1) = Z_to_bv 64 856060),
    forall (EX32 : getr R13 (reg 2) = Z_to_bv 64 (Sp - 32 - 128)),
    forall (EX33 : getr R13 (reg 8) = Z_to_bv 64 41),
    forall (EX35 : getr R13 (reg 10) = Z_to_bv 64 41),
    forall (EX36 : getr R13 (reg 18) = Z_to_bv 64 16),
    forall (ACR2 : acredit_ok L (adebit L cr 160) 41),
    forall (mR14 : getr R14 (reg 10) = Z_to_bv 64 ref),
    forall (RP14 : regs_preserved R13 R14),
    forall (RF16 : ref mod 16 = 0),
    forall (NUM : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR) /\ (0 <= Sp - 32 < 2 ^ 64 /\ 140735332552704 <= Sp - 32 <= 140737488355264) /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47) /\ (obj = u + 128 /\ 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 32 <= ahl_ceil ar) /\ 17594333495296 <= ref /\ ref + 41 <= ahl_ceil ar /\ (ref + 41 <= u \/ u + 160 <= ref))),
    forall (EX54 : forall x : nat, In x KS_ue1c6 -> getr R15 (reg x) = getr R14 (reg x)),
    forall (EX72 : getr R15 (reg 1) = Z_to_bv 64 728400),
    forall (EX73 : getr R15 (reg 2) = Z_to_bv 64 (Sp - 32 - 112)),
    forall (EX74 : getr R15 (reg 8) = Z_to_bv 64 obj),
    forall (EX75 : getr R15 (reg 10) = Z_to_bv 64 (ref + 24)),
    forall (EX76 : getr R15 (reg 11) = Z_to_bv 64 (Sp - 32 - 55)),
    forall (EX77 : getr R15 (reg 12) = Z_to_bv 64 17),
    forall (EX78 : getr R15 (reg 19) = Z_to_bv 64 (ref + 24)),
    forall (EX79 : L5.u32_at RSEGS M21 (ref + 16) 0),
    forall (EX80 : L5.u64_at RSEGS M21 (ref + 8) 16),
    forall (EX81 : L5.u64_at RSEGS M21 ref 16),
    forall (HMC : amemcpy_spec_at L ar SCFG HI 385232 false),
    forall (mR16 : getr R16 (reg 10) = Z_to_bv 64 (ref + 24)),
    forall (RP16 : regs_preserved R15 R16),
    forall (EX37 : forall x : nat, In x KS_ue1c7 -> getr R17 (reg x) = getr R16 (reg x)),
    forall (EX38 : getr R17 (reg 1) = Z_to_bv 64 583732),
    forall (EX82 : getr R17 (reg 2) = Z_to_bv 64 (Sp - 32)),
    forall (EX83 : getr R17 (reg 9) = Z_to_bv 64 22),
    forall (EX84 : getr R17 (reg 10) = Z_to_bv 64 874048),
    forall (EX85 : getr R17 (reg 18) = Z_to_bv 64 2147450880),
    forall (EX86 : getr R17 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R4 (reg 19)))),
    forall (EX87 : L5.u64_at RSEGS M21 (obj + 24) 892784),
    forall (EX88 : L5.u32_at RSEGS M21 (obj + 16) 22),
    forall (EX89 : L5.u64_at RSEGS M21 obj 874048),
    forall (EX90 : L5.u64_at RSEGS M21 (obj + 8) (ref + 24)),
    forall (RP18 : regs_preserved R17 R18),
    forall (EX34 : forall x : nat, In x KS_ue1c8 -> getr R19 (reg x) = getr R18 (reg x)),
    forall (EX39 : getr R19 (reg 10) = Z_to_bv 64 obj),
    forall (EX40 : getr R19 (reg 11) = Z_to_bv 64 874072),
    forall (EX17 : getr R19 (reg 12) = Z_to_bv 64 731988),
    forall (E10 : bv_unsigned (getr R19 (reg 10)) = obj),
    forall (EX42 : forall x : nat, In x KS_ue1t1 -> getr R20 (reg x) = getr R19 (reg x)),
    forall (EX46 : getr R20 (reg 1) = Z_to_bv 64 343324),
    forall (EX65 : getr R20 (reg 2) = Z_to_bv 64 (Sp - 32 - 64)),
    forall (EX66 : getr R20 (reg 8) = Z_to_bv 64 (obj - 32)),
    forall (EX67 : getr R20 (reg 9) = Z_to_bv 64 883976),
    forall (EX68 : getr R20 (reg 10) = Z_to_bv 64 (obj - 32)),
    forall (EX69 : getr R20 (reg 11) = Z_to_bv 64 743680),
    forall (EX70 : getr R20 (reg 12) = Z_to_bv 64 722532),
    forall (EX71 : getr R20 (reg 18) = getr R19 (reg 10)),
    forall (EX91 : L5.u64_at RSEGS M21 (Sp - 32 - 56) 874072),
    forall (EX92 : L5.u64_at RSEGS M21 (Sp - 32 - 48) (obj - 128)),
    forall (EX93 : L5.u64_at RSEGS M21 (Sp - 32 - 40) 722716),
    forall (EX94 : L5.u64_at RSEGS M21 (obj - 120) 1),
    forall (EX95 : L5.u64_at RSEGS M21 (obj - 24) 722532),
    forall (EX96 : L5.u64_at RSEGS M21 (obj - 32) 4849336966747728640),
    forall (EX97 : L5.u64_at RSEGS M21 (obj - 88) 607608),
    forall (EX98 : L5.u64_at RSEGS M21 (obj - 104) 731988),
    forall (EX99 : L5.u64_at RSEGS M21 (obj - 112) 874072),
    forall (EX100 : L5.u64_at RSEGS M21 (obj - 96) 607876),
    forall (EX101 : L5.u64_at RSEGS M21 (Sp - 32 - 64) obj),
    forall (EX102 : L5.u32_at RSEGS M21 6357456 1),
    forall (EX103 : L5.u64_at RSEGS M21 (Sp - 32 - 32) (bv_unsigned (getr R19 (reg 18)))),
    forall (EX104 : L5.u64_at RSEGS M21 (Sp - 32 - 24) (bv_unsigned (getr R19 (reg 9)))),
    forall (EX105 : L5.u64_at RSEGS M21 (Sp - 32 - 16) (bv_unsigned (getr R19 (reg 8)))),
    forall (EX106 : L5.u64_at RSEGS M21 (Sp - 32 - 8) 583756),
    forall (RP21 : regs_preserved R20 R21),
    forall (CI21 : cinv L ar HI M model A LB FF Sp SCR XW [(ref, 41); (u, 160)] M21 model21 LK (adebit L (adebit L cr 160) 41) A14),
    forall (FL5 : fl = true -> L5.u8_at RSEGS M21 6360118 0),
    forall (FL3 : fl = true -> L5.u8_at RSEGS M21 6360116 0),
    forall (FL1 : fl = true -> L5.u8_at RSEGS M21 6360114 0),
    forall (AUXV : forall j : nat, (j < 20)%nat -> L5.u64_at RSEGS M21 (av + 8 * Z.of_nat j) (nth j (L5USA.auxv20A uid rnd hw) 0)),
    forall (IC3 : L5.img_clear M21 892784 (892784 + 8)),
    forall (IC2 : L5.img_clear M21 892736 892768),
    forall (IC1 : L5.img_clear M21 65536 880640),
  srealizes RSEGS SCFG (cfg (fx:=fx21) R21 343324 M21 model21) K.
Proof.
  intros.
  (* [comment removed for export] *)
  assert (E8 : bv_unsigned (getr R19 (reg 8)) = obj). { apply (U_of R19 8). rk. unfold numf in NUM; clear - NUM; lia. }
  rewrite ?E8 in *. clear E8.
  (* [comment removed for export] *)
  destruct (cv_tls L ar C IL HI LY ILY HIok ICok UNWL M model A LB FF Sp SCR XW _ _ _ _ _ _ CI21) as (ctx & th & tbv & tev & blk & TLSC & TLSR & TLSI & TLSP & TLSB).
  cbv zeta in TLSC. rewrite HTP in TLSC. change (6360328 + 8) with 6360336 in TLSC. destruct TLSC as (TC1 & TC2 & TC3 & TC4 & TC5 & TC6).
  pose proof (TLSB ref 41 ltac:(left; reflexivity)) as TB1. pose proof (TLSB u 160 ltac:(right; left; reflexivity)) as TB2. clear TLSB.
  assert (NUM4 : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR)
                      /\ (0 <= Sp - 32 < 2 ^ 64 /\ 140735332552704 <= Sp - 32 /\ Sp - 32 <= 140737488355264)
                      /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47)
                      /\ (obj = u + 128 /\ 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 32 <= ahl_ceil ar)
                      /\ (17594333495296 <= ref /\ ref + 41 <= ahl_ceil ar)
                      /\ (4096 <= ctx /\ ctx + 160 <= ahl_ceil ar /\ 4096 <= th /\ th + 64 <= ahl_ceil ar /\ 4096 <= blk /\ blk + 4096 <= ahl_ceil ar /\ 0 <= tbv < 2 ^ 64 /\ 0 <= tev < 2 ^ 64))).
  { unfold numf in *. clear - NUM TLSR. lia. }
  (* [comment removed for export] *)
  assert (DJ0 : ref + 41 <= u \/ u + 160 <= ref) by (unfold numf in NUM; clear - NUM; lia).
  destruct TLSI as (DJ1 & DJ2 & DJ3). destruct TLSP as (DJ4 & DJ5 & DJ6). destruct TB1 as (DJ7 & DJ8 & DJ9). destruct TB2 as (DJ10 & DJ11 & DJ12).
  clear NUM. rename NUM4 into NUM. clear TLSR.
  assert (AV8' : av mod 8 = 0) by exact AV8.
  (* [comment removed for export] *)
  assert (LAND : forall (fx22 : FPState) (R22 : bvmap 5 word) (M22 : word -> option byte) (model22 : Model),
            cinv L ar HI M model A LB FF Sp SCR XW [(ref, 41); (u, 160)] M22 model22 LK (adebit L (adebit L cr 160) 41) A14 ->
            (forall x, In x [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R22 (reg x) = getr R21 (reg x)) ->
            getr R22 (reg 2) = Z_to_bv 64 (Sp - 32 + 32) -> getr R22 (reg 8) = Z_to_bv 64 s0v -> getr R22 (reg 9) = Z_to_bv 64 (Sp - 32 + 32) ->
            getr R22 (reg 10) = Z_to_bv 64 (obj - 32) -> getr R22 (reg 11) = Z_to_bv 64 1 -> getr R22 (reg 18) = Z_to_bv 64 s2v ->
            L5.u64_at RSEGS M22 (obj - 32) 4849336966747728640 -> L5KA.zeros_at M22 (obj - 72) 4 -> L5.u64_at RSEGS M22 (obj - 40) obj ->
            L5.u64_at RSEGS M22 (obj - 120) 1 -> L5.u64_at RSEGS M22 (obj - 104) 731988 -> L5.u64_at RSEGS M22 (obj + 8) (ref + 24) -> L5.u32_at RSEGS M22 (ref + 16) 0 ->
            L5.u64_at RSEGS M22 6357448 0 -> L5.u32_at RSEGS M22 6357456 1 -> L5.u8_at RSEGS M22 6358000 1 -> L5.u8_at RSEGS M22 6358001 1 ->
            L5.u8_at RSEGS M22 6360113 1 -> L5.u8_at RSEGS M22 6360114 0 -> L5.u8_at RSEGS M22 6360115 1 -> L5.u8_at RSEGS M22 6360116 0 ->
            L5.u8_at RSEGS M22 6360117 1 -> L5.u8_at RSEGS M22 6360118 0 ->
            L5.u64_at RSEGS M22 6360280 6492112 -> L5.u64_at RSEGS M22 6492152 0 -> (exists e, L5.u32_at RSEGS M22 6360164 e /\ 0 <= e < 2 ^ 64) ->
            L5.u64_at RSEGS M22 6491464 canary -> L5.u64_at RSEGS M22 6492064 av ->
            (forall j : nat, (j < 20)%nat -> L5.u64_at RSEGS M22 (av + 8 * Z.of_nat j) (nth j (L5USA.auxv20A uid rnd hw) 0)) ->
            L5.img_clear M22 65536 880640 -> L5.img_clear M22 892736 892768 -> L5.img_clear M22 892784 (892784 + 8) ->
            srealizes RSEGS SCFG (cfg (fx:=fx22) R22 582360 M22 model22) K).
  { intros fx22 R22 M22 model22 CI22 KS22 X2 X8 X9 X10 X11 X18 H32 H72 H40 H120 H104 H8 Hr16 HC HU HG0 HG1 F0 F1 F2 F3 F4 F5 HTD HMS HER HCA HAX HAV I1 I2 I3.
    destruct CI22 as (HH22 & AM22 & RT22 & IA22 & STK22 & SH22 & EK22 & DK22).
    assert (EU : u = obj - 128) by (unfold numf in NUM; clear - NUM; lia).
    apply (KONT fx22 R22 M22 model22 ((ref, 41) :: (obj - 128, 160) :: LB) (adebit L (adebit L cr 160) 41) LK A14).
    - rewrite L5AE1K.r8. exact X8.
    - rewrite L5AE1K.r9. rewrite X9. f_equal. clear; lia.
    - rewrite L5AE1K.r18. exact X18.
    - intros i Hi. rewrite (KS22 i Hi).
      assert (C19 : getr R21 (reg 19) = getr R4 (reg 19)). { etransitivity. 2: apply (Z_to_bv_bv_unsigned 64). rk. }
      assert (C20 : getr R21 (reg 20) = getr R4 (reg 20)). { etransitivity. 2: apply (Z_to_bv_bv_unsigned 64). rk. }
      cbn [In] in Hi. destruct Hi as [<-|[<-|[<-|[<-|Hi]]]].
      + rk. + rk. + rewrite C19. rk. + rewrite C20. rk.
      + destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; rk.
    - unfold L5USA.e1_landed. split. 2: split.
      + exists obj, ref. split. rewrite r10. exact X10. split. rewrite r11. exact X11. split. rewrite r2. rewrite X2. f_equal. clear; lia.
        split. reflexivity.
        split. { unfold L5USA.exc_at, L5USA.EXC_CLASS, L5USA.DTOR_SYSTEM_ERROR. split. exact H32. split. apply u32_of_zeros. exact H72. unfold numf in NUM; clear - NUM; lia. unfold numf in NUM; clear - NUM; lia.
                 split. exact H40. split. exact H120. split. exact H104. split. exact H8. exact Hr16. }
        unfold L5USA.statics_landed. cbn [L5USA.xs_av L5USA.xs_uid L5USA.xs_rnd L5USA.xs_canary L5USA.xs_hw].
        split. exact HC. split. exact HU. split. { unfold L5USA.syscat_guard, L5USA.SYSCAT_GUARD. split. exact HG0. exact HG1. }
        split. { unfold L5USA.uw_flags, L5USA.UW_FLAGS. repeat split; assumption. }
        unfold L5USA.statics_const, L5USA.TD_LOCALE, L5USA.GLOBAL_LOCALE, L5USA.LOCALE_MSGCAT, L5USA.ERRNO, L5USA.CANARY, L5USA.AUXVP, L5USA.SYSCAT_OBJ.
        split. exact HTD. split. exact HMS. split. exact HER. split. exact HCA. split. exact HAX. split. exact AV8. split. exact AVLO. split. exact AVHI. split. exact HAV.
        split. exact UIDR. split. exact RNDR. split. exact CANR. split. exact HWR. split. exact I1. split. exact I2. exact I3.
      + unfold L5USA.EXC1_SZ, L5USA.REF1_SZ. rewrite <- !L5OMA.adebits_1, L5OMA.adebits_add. change (1 + 1) with 2. unfold credit_le. clear; lia.
      + apply incl_refl.
    - split. exact EK22. split. exact (astk_defined ar M22 Sp SCR (Sp - SCR) SCR STK22 ltac:(clear; lia) ltac:(clear; lia)). exact DK22.
    - exact RT22.
    - exact IA22.
    - exact AM22.
    - rewrite <- EU. exact HH22. }
  (* [comment removed for export] *)
  pose proof (auxv_cell M21 av uid rnd hw AUXV 0%nat av 3 ltac:(clear; lia) ltac:(clear; lia) eq_refl) as AVC0.
  pose proof (auxv_cell M21 av uid rnd hw AUXV 1%nat (av + 8) 65600 ltac:(clear; lia) ltac:(clear; lia) eq_refl) as AVC1.
  pose proof (auxv_cell M21 av uid rnd hw AUXV 2%nat (av + 16) 4 ltac:(clear; lia) ltac:(clear; lia) eq_refl) as AVC2.
  pose proof (auxv_cell M21 av uid rnd hw AUXV 3%nat (av + 24) 56 ltac:(clear; lia) ltac:(clear; lia) eq_refl) as AVC3.
  pose proof (auxv_cell M21 av uid rnd hw AUXV 4%nat (av + 32) 5 ltac:(clear; lia) ltac:(clear; lia) eq_refl) as AVC4.
  pose proof (auxv_cell M21 av uid rnd hw AUXV 5%nat (av + 40) 11 ltac:(clear; lia) ltac:(clear; lia) eq_refl) as AVC5.
  pose proof (auxv_cell M21 av uid rnd hw AUXV 6%nat (av + 48) 16 ltac:(clear; lia) ltac:(clear; lia) eq_refl) as AVC6.
  pose proof (auxv_cell M21 av uid rnd hw AUXV 7%nat (av + 56) hw ltac:(clear; lia) ltac:(clear; lia) eq_refl) as AVC7.
  pose proof (auxv_cell M21 av uid rnd hw AUXV 8%nat (av + 64) 6 ltac:(clear; lia) ltac:(clear; lia) eq_refl) as AVC8.
  pose proof (auxv_cell M21 av uid rnd hw AUXV 9%nat (av + 72) 4096 ltac:(clear; lia) ltac:(clear; lia) eq_refl) as AVC9.
  pose proof (auxv_cell M21 av uid rnd hw AUXV 10%nat (av + 80) 11 ltac:(clear; lia) ltac:(clear; lia) eq_refl) as AVC10.
  pose proof (auxv_cell M21 av uid rnd hw AUXV 11%nat (av + 88) uid ltac:(clear; lia) ltac:(clear; lia) eq_refl) as AVC11.
  pose proof (auxv_cell M21 av uid rnd hw AUXV 12%nat (av + 96) 12 ltac:(clear; lia) ltac:(clear; lia) eq_refl) as AVC12.
  pose proof (auxv_cell M21 av uid rnd hw AUXV 13%nat (av + 104) uid ltac:(clear; lia) ltac:(clear; lia) eq_refl) as AVC13.
  pose proof (auxv_cell M21 av uid rnd hw AUXV 14%nat (av + 112) 23 ltac:(clear; lia) ltac:(clear; lia) eq_refl) as AVC14.
  pose proof (auxv_cell M21 av uid rnd hw AUXV 15%nat (av + 120) 0 ltac:(clear; lia) ltac:(clear; lia) eq_refl) as AVC15.
  pose proof (auxv_cell M21 av uid rnd hw AUXV 16%nat (av + 128) 25 ltac:(clear; lia) ltac:(clear; lia) eq_refl) as AVC16.
  pose proof (auxv_cell M21 av uid rnd hw AUXV 17%nat (av + 136) rnd ltac:(clear; lia) ltac:(clear; lia) eq_refl) as AVC17.
  pose proof (auxv_cell M21 av uid rnd hw AUXV 18%nat (av + 144) 0 ltac:(clear; lia) ltac:(clear; lia) eq_refl) as AVC18.
  pose proof (auxv_cell M21 av uid rnd hw AUXV 19%nat (av + 152) 0 ltac:(clear; lia) ltac:(clear; lia) eq_refl) as AVC19.
  destruct fl; cbv iota in FL0, FL2, FL4.
  - (* [comment removed for export] *)
    specialize (FL1 eq_refl). specialize (FL3 eq_refl). specialize (FL5 eq_refl).
    pose proof (ue1t2_v1_conc HFILL HCOPY HTLS fx21 R21 (mrestrict (ahid A14 model21) M21)
                  (fun j => match j with 2%nat => Sp - 32 | 10%nat => obj | 32%nat => av | 33%nat => canary | 34%nat => uid | 36%nat => rnd | 39%nat => hw | 40%nat => U R21 10
                                    | 41%nat => ctx | 42%nat => th | 43%nat => blk | 44%nat => tbv | 45%nat => tev | 46%nat => 874072
                                    | 47%nat => bv_unsigned (getr R19 (reg 9)) | 48%nat => bv_unsigned (getr R19 (reg 18)) | 49%nat => s0v | 50%nat => s2v | _ => 0 end)) as P. cbn beta iota in P.
    piece_step CI21 XWIMG P (fun a => Sp - 32 - 10608 <= a < Sp - 32 - 10608 + 10544 \/ obj - 68 <= a < obj - 68 + 68 \/ Sp - 32 - 64 <= a < Sp - 32 - 64 + 8 \/ Sp - 32 - 56 <= a < Sp - 32 - 56 + 8
                                       \/ Sp - 32 - 48 <= a < Sp - 32 - 48 + 8 \/ Sp - 32 - 40 <= a < Sp - 32 - 40 + 8 \/ 6360113 <= a < 6360113 + 6) fx22 R22 M22 model22 CI22.
    apply (LAND fx22 R22 M22 model22 CI22); try assumption; try rk.
    + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [rk|]). destruct Hx.
    + eexists. split. exact EX6. apply BL.bvu_range.
  - (* [comment removed for export] *)
    clear FL1 FL3 FL5.
    pose proof (ue1t2_v0_conc HFILL HCOPY HTLS fx21 R21 (mrestrict (ahid A14 model21) M21)
                  (fun j => match j with 2%nat => Sp - 32 | 10%nat => obj | 32%nat => av | 33%nat => canary | 34%nat => uid | 36%nat => rnd | 39%nat => hw | 40%nat => U R21 10
                                    | 41%nat => ctx | 42%nat => th | 43%nat => blk | 44%nat => tbv | 45%nat => tev | 46%nat => 874072
                                    | 47%nat => bv_unsigned (getr R19 (reg 9)) | 48%nat => bv_unsigned (getr R19 (reg 18)) | 49%nat => s0v | 50%nat => s2v | _ => 0 end)) as P. cbn beta iota in P.
    piece_step CI21 XWIMG P (fun a => Sp - 32 - 10608 <= a < Sp - 32 - 10608 + 10544 \/ obj - 68 <= a < obj - 68 + 68 \/ Sp - 32 - 64 <= a < Sp - 32 - 64 + 8 \/ Sp - 32 - 56 <= a < Sp - 32 - 56 + 8
                                       \/ Sp - 32 - 48 <= a < Sp - 32 - 48 + 8 \/ Sp - 32 - 40 <= a < Sp - 32 - 40 + 8 \/ 6360113 <= a < 6360113 + 6) fx22 R22 M22 model22 CI22.
    apply (LAND fx22 R22 M22 model22 CI22); try assumption; try rk.
    + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [rk|]). destruct Hx.
    + eexists. split. exact EX6. (* [comment removed for export] *) apply BL.bvu_range.
Qed.

End WithIface.
End SCFG_1.
End L5AE1S5.
