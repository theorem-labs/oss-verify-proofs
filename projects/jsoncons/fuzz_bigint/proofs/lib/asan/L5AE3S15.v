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
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ParseSpecsA L5OpmodSpecsA L5DivSpecsA L5UnwindSpecsA XIcptA XIcptAs0Kit L5AUnwK L5AUnwK2 L5AE1K L5AE2K L5AE3K L5AE2PP L5AE2Pad L5AE3P1 L5AE3P2 L5AE3P3 L5AE3P4 L5AE3P5 L5AE3P6 L5AE3P7 L5AE3P8 L5AE3P9 L5AE3P10 L5AE3P11 L5AE3PP L5AE3Pad L5AUnwK3 L5AUnwK4 L5DivInnerSpecsA L5AOpdel.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Set Printing Width 100000. Set Printing Depth 100000.

Module L5AE3S15.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5AUK. Import L5AUK2.
Import L5AE3P1.L5AE3P1. Import L5AE3P2.L5AE3P2. Import L5AE3P3.L5AE3P3. Import L5AE3P4.L5AE3P4. Import L5AE3P5.L5AE3P5. Import L5AE3P6.L5AE3P6. Import L5AE3P7.L5AE3P7. Import L5AE3P8.L5AE3P8. Import L5AE3P9.L5AE3P9. Import L5AE3P10.L5AE3P10. Import L5AE3P11.L5AE3P11. Import L5AE3PP.L5AE3PP. Import L5AUK3. Import L5AUK4.
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
Local Ltac ffeed P CI F tac := feed P ltac:(idtac; lazymatch goal with |- context [F] => first [ asm | assumption | rk | gmem | tac | fd_mem CI ] | |- _ => first [ asm | fdp CI ] end).
(* [comment removed for export] *)
Local Ltac flia := idtac; lazymatch goal with NUM : numf _, FN : numg _ |- _ =>
  first [ solve [clear - NUM FN; unfold numf in NUM; unfold numg in FN; lia]
        | match goal with D : (_ \/ _) |- _ => solve [clear - NUM FN D; unfold numf in NUM; unfold numg in FN; lia] end ] end.
(* [comment removed for export] *)
Local Ltac padfeed P CI tac := feed P ltac:(idtac; first [ rk | asm | assumption | apply BL.bvu_range | apply L5AUK.U_to | apply L5AUK.UR | (unfold SB in *; gmem) | (arith_goal; tac) | fd_mem CI ]).
(* [comment removed for export] *)
Local Ltac sd_calld := idtac; lazymatch goal with |- ccl _ _ _ _ => ccl_tac | |- _ => first [ nlia | dlia ] end.
(* [comment removed for export] *)
Local Notation XW := [(6357456, 4); (6360113, 6)].
Local Notation XWIMG := (L5AE1K.xw2_img L UNWL).

Lemma e3_s15 :
  forall (R0 : bvmap 5 word) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB1 : list (Z * Z)) (FF : list fframe) (LK : list fframe) (LKt : list fframe) (cr : credit) (A : list (Z * Z)) (Sp : Z) (SCR : Z) (xo : Z) (gd : bool) (av : Z) (uid : Z) (rnd : Z) (canary : Z) (hw : Z) (F1a : Z) (fl1a : Z) (F3a : Z) (fl3a : Z) (F1b : Z) (fl1b : Z) (F3b : Z) (fl3b : Z) (F1c : Z) (fl1c : Z) (F1d : Z) (fl1d : Z) (d1 : Z) (d2 : Z) (d3 : Z) (d4 : Z) (qx : Z) (bo : Z) (LB0 : list (Z * Z)) (lenX : nat) (w9 : Z) (w10 : Z) (xs : Z) (fbx : Z) (fd0N : Z) (fn0N : Z) (fnN : Z) (fdenN : Z) (w1 : Z) (fd0 : Z) (fn0 : Z) (fn : Z) (fden : Z) (v0 : Z) (v1 : Z) (v2 : Z) (v3 : Z) (nd0 : nat) (nn0 : nat) (nn : nat) (nd : nat) (M3 : word -> option byte) (errv : Z) (R1 : bvmap 5 word) (R2 : bvmap 5 word) (A2 : list (Z * Z)) (u : Z) (obj : Z) (R3 : bvmap 5 word) (model3 : Model) (R4 : bvmap 5 word) (R5 : bvmap 5 word) (R6 : bvmap 5 word) (R7 : bvmap 5 word) (A7 : list (Z * Z)) (msg : Z) (R8 : bvmap 5 word) (R9 : bvmap 5 word) (R10 : bvmap 5 word) (R11 : bvmap 5 word) (R12 : bvmap 5 word) (R13 : bvmap 5 word) (R14 : bvmap 5 word) (A14 : list (Z * Z)) (ref : Z) (R15 : bvmap 5 word) (R16 : bvmap 5 word) (R17 : bvmap 5 word) (R18 : bvmap 5 word) (R19 : bvmap 5 word) (R20 : bvmap 5 word) (R21 : bvmap 5 word) (st : L5USA.XS) (R22 : bvmap 5 word) (R23 : bvmap 5 word) (R24 : bvmap 5 word) (R25 : bvmap 5 word) (A25 : list (Z * Z)) (R26 : bvmap 5 word) (R27 : bvmap 5 word) (R28 : bvmap 5 word) (R29 : bvmap 5 word) (A29 : list (Z * Z)) (R30 : bvmap 5 word) (R31 : bvmap 5 word) (A31 : list (Z * Z)) (R32 : bvmap 5 word) (R33 : bvmap 5 word) (R34 : bvmap 5 word) (R35 : bvmap 5 word) (R36 : bvmap 5 word) (R37 : bvmap 5 word) (R38 : bvmap 5 word) (M42 : word -> option byte) (R39 : bvmap 5 word) (R40 : bvmap 5 word) (R41 : bvmap 5 word) (A41 : list (Z * Z)) (R42 : bvmap 5 word) (model42 : Model) (M46 : word -> option byte) (R43 : bvmap 5 word) (A43 : list (Z * Z)) (R44 : bvmap 5 word) (R45 : bvmap 5 word) (fx46 : FPState) (R46 : bvmap 5 word) (model46 : Model),
    forall (bq : L5.bigobj),
    forall (ELB1 : LB1 = (qx, 64) :: LB0),
    forall (Z2 : getr R (reg 2) = Z_to_bv 64 (Sp - 1216)),
    forall (Z3 : getr R (reg 3) = Z_to_bv 64 67584),
    forall (Z4 : getr R (reg 4) = Z_to_bv 64 6360328),
    forall (Z10 : getr R 10 = Z_to_bv 64 16),
    forall (Z8 : getr R (reg 8) = Z_to_bv 64 (Sp - 1088)),
    forall (Z9 : getr R (reg 9) = Z_to_bv 64 (Sp - 1216)),
    forall (Z18 : getr R 18 = Z_to_bv 64 F1d),
    forall (Z19 : getr R 19 = Z_to_bv 64 xo),
    forall (Z20 : getr R 20 = Z_to_bv 64 (F1d + 32)),
    forall (Z21 : getr R 21 = Z_to_bv 64 (xo + 8)),
    forall (Z22 : getr R 22 = Z_to_bv 64 (F1c / 8 + 2147450880)),
    forall (Z23 : getr R 23 = Z_to_bv 64 (F1d / 8 + 2147450880)),
    forall (Z24 : getr R 24 = Z_to_bv 64 F1d),
    forall (Z25 : getr R 25 = Z_to_bv 64 SB),
    forall (Z26 : getr R 26 = Z_to_bv 64 ((xo + 8) / 8 + 2147450880)),
    forall (Z27 : getr R 27 = Z_to_bv 64 0),
    forall (DEN0Nr : 0 <= fd0N < 256),
    forall (DEN0Nt : Z.testbit fd0N 0 = false),
    forall (NUM0Nr : 0 <= fn0N < 256),
    forall (NUM0Nt : Z.testbit fn0N 0 = true),
    forall (NUMN : L5.big_at RSEGS M (F3b + 96) {| L5.bo_fb := fnN; L5.bo_len := 0; L5.bo_st := L5.BDyn 8 d2 |}),
    forall (NUMNT : Z.testbit fnN 1 = false),
    forall (DENN : L5.big_at RSEGS M (F3b + 32) {| L5.bo_fb := fdenN; L5.bo_len := 1; L5.bo_st := L5.BInl L5DSA.MWORD w1 |}),
    forall (DENNT : Z.testbit fdenN 1 = false),
    forall (ZQ : L5DIA.zero_obj M (F1b + 32)),
    forall (o2 : L5.u64_at RSEGS M46 (Sp - 392) F3a),
    forall (o3 : L5.u64_at RSEGS M46 (Sp - 376) F3a),
    forall (o4 : L5.u64_at RSEGS M46 (Sp - 368) (F3a + 96)),
    forall (o5 : L5.u64_at RSEGS M46 (Sp - 360) (F3a + 32)),
    forall (o8 : L5.u64_at RSEGS M46 (Sp - 336) (S F3a)),
    forall (DEN0f : L5.u8_at RSEGS M46 (Sp - 264) fd0),
    forall (DEN0r : 0 <= fd0 < 256),
    forall (DEN0t : Z.testbit fd0 0 = false),
    forall (NUM0f : L5.u8_at RSEGS M46 (Sp - 232) fn0),
    forall (NUM0r : 0 <= fn0 < 256),
    forall (NUM0t : Z.testbit fn0 0 = false),
    forall (NUMO : L5.big_at RSEGS M (F3a + 96) {| L5.bo_fb := fn; L5.bo_len := nn; L5.bo_st := L5.BDyn 8 d3 |}),
    forall (DENO : L5.big_at RSEGS M (F3a + 32) {| L5.bo_fb := fden; L5.bo_len := nd; L5.bo_st := L5.BDyn 8 d4 |}),
    forall (BQ : L5.big_at RSEGS M (F1a + 32) bq),
    forall (BQD : L5.bo_dyn bq = false),
    forall (BX : L5.big_at RSEGS M xo {| L5.bo_fb := fbx; L5.bo_len := lenX; L5.bo_st := L5.BDyn 8 qx |}),
    forall (SHd : L5DIA.sh_rz M F1d),
    forall (SHc : L5DIA.sh_rz M F1c),
    forall (SH3b : L5DIA.sh_div M F3b 0 248 248 248 248),
    forall (SH1b : L5DIA.sh_op M F1b),
    forall (SH3a : L5DIA.sh_div M F3a 0 248 248 248 248),
    forall (SH1a : L5DIA.sh_op M F1a),
    forall (FRL1a : L5DSA.fr_live L ar ([(d1, 64); (d2, 64); (d3, 64); (d4, 64)] ++ LB1) FF M 1 F1a fl1a (Sp - 64)),
    forall (FRL3a : L5DSA.fr_live L ar ([(d1, 64); (d2, 64); (d3, 64); (d4, 64)] ++ LB1) ((F1a, 1, Sp - 64) :: FF) M 3 F3a fl3a (Sp - 416)),
    forall (FRL1b : L5DSA.fr_live L ar ([(d1, 64); (d2, 64); (d3, 64); (d4, 64)] ++ LB1) ((F3a, 3, Sp - 416) :: (F1a, 1, Sp - 64) :: FF) M 1 F1b fl1b (Sp - 576)),
    forall (FRL3b : L5DSA.fr_live L ar ([(d1, 64); (d2, 64); (d3, 64); (d4, 64)] ++ LB1) ((F1b, 1, Sp - 576) :: (F3a, 3, Sp - 416) :: (F1a, 1, Sp - 64) :: FF) M 3 F3b fl3b (Sp - 928)),
    forall (FRLc : L5DSA.fr_live L ar ([(d1, 64); (d2, 64); (d3, 64); (d4, 64)] ++ LB1) ((F3b, 3, Sp - 928) :: (F1b, 1, Sp - 576) :: (F3a, 3, Sp - 416) :: (F1a, 1, Sp - 64) :: FF) M 1 F1c fl1c (Sp - 1056)),
    forall (FRLd : L5DSA.fr_live L ar ([(d1, 64); (d2, 64); (d3, 64); (d4, 64)] ++ LB1) ((F1c, 1, Sp - 1056) :: (F3b, 3, Sp - 928) :: (F1b, 1, Sp - 576) :: (F3a, 3, Sp - 416) :: (F1a, 1, Sp - 64) :: FF) M 1 F1d fl1d (Sp - 1184)),
    forall (LFR : length [(F1a, fl1a); (F3a, fl3a); (F1b, fl1b); (F3b, fl3b); (F1c, fl1c); (F1d, fl1d)] = 6%nat),
    forall (G1 : getr R0 1 = Z_to_bv 64 581760),
    forall (G2 : getr R0 2 = Z_to_bv 64 Sp),
    forall (G3 : getr R0 3 = Z_to_bv 64 67584),
    forall (G4 : getr R0 4 = Z_to_bv 64 6360328),
    forall (G9 : getr R0 9 = Z_to_bv 64 Sp),
    forall (S32 : Sp mod 32 = 0),
    forall (EC0 : L5.u64_at RSEGS M46 6357448 0),
    forall (GD0 : L5.u8_at RSEGS M46 6358000 (if gd then 1 else 0)),
    forall (GD1 : L5.u8_at RSEGS M46 6358001 (if gd then 1 else 0)),
    forall (TDL : L5.u64_at RSEGS M46 6360280 6492112),
    forall (MSG0 : L5.u64_at RSEGS M46 6492152 0),
    forall (ERR : L5.u32_at RSEGS M46 6360164 errv),
    forall (ERRR : 0 <= errv < 2 ^ 64),
    forall (CAN : L5.u64_at RSEGS M46 6491464 canary),
    forall (AUXP : L5.u64_at RSEGS M46 6492064 av),
    forall (AV8 : av mod 8 = 0),
    forall (AVLO : 2 ^ 40 <= av),
    forall (AVHI : av + 160 <= 2 ^ 47),
    forall (UIDR : 0 <= uid < 2 ^ 64),
    forall (RNDR : 0 <= rnd < 2 ^ 64),
    forall (CANR : 0 <= canary < 2 ^ 64),
    forall (HWR : 0 <= hw < 2 ^ 64),
    forall (AVS : ar_sptop ar <= av),
    forall (HH : ri_inv HI ([(d1, 64); (d2, 64); (d3, 64); (d4, 64)] ++ LB1) (L5DSA.ff_e3 FF Sp F1a F3a F1b F3b F1c F1d) LKt cr A M (vml_of model)),
    forall (AM : amodel_ok A model),
    forall (HK : K []),
    forall (LKI : incl LKt LK),
    forall (STK : astk ar M Sp SCR),
    forall (HSCR : 69632 <= SCR),
    forall (SCR8 : SCR mod 8 = 0),
    forall (SH : L5OMA.stksh ar M (Sp - SCR)),
    forall (CRF : L5OMA.acredit_for L cr 3 (144 + 48 + 66)),
    forall (KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LK' : list fframe) (A' : list (Z * Z)), regs_preserved R0 R' -> L5USA.e3_landed L st LB1 FF LK cr Sp M' R' LB' cr' LK' -> ahpres L ar LB1 FF Sp SCR L5USA.xs_foot M M' -> model_rt model model' -> incl A A' -> amodel_ok A' model' -> ri_inv HI LB' FF LK' cr' A' M' (vml_of model') -> srealizes RSEGS SCFG (cfg (fx:=fx') R' 582452 M' model') K),
    forall (A16 : Sp mod 16 = 0),
    forall (SLO : ahl_ceil ar + 4096 + SCR <= Sp),
    forall (SHI : Sp <= ar_sptop ar),
    forall (SPT : 140735340871680 <= ar_sptop ar <= 2 ^ 47),
    forall (HS0 : 0 <= SCR),
    forall (ALS : (Sp - 1216) mod 16 = 0),
    forall (ALS8 : (Sp - 1216) mod 8 = 0),
    forall (SPR0 : 0 <= Sp - 1216 < 2 ^ 64),
    forall (SPLO : 140735332552704 <= Sp - 1216),
    forall (SPHI : Sp - 1216 <= 140737488355264),
    forall (LY2 : as0_layout2 L),
    forall (HTP : hl_tp L = 6360328),
    forall (FN : numg (6500352 <= ar_fs ar /\ ar_fs ar + 11571200 <= ahl_ceil ar /\ ar_fs ar <= F1d /\ F1d + 128 <= ar_fs ar + 11571200 /\ ar_fs ar <= F1c /\ F1c + 128 <= ar_fs ar + 11571200 /\ ar_fs ar <= F3b /\ F3b + 512 <= ar_fs ar + 11571200 /\ ar_fs ar <= F1b /\ F1b + 128 <= ar_fs ar + 11571200 /\ ar_fs ar <= F3a /\ F3a + 512 <= ar_fs ar + 11571200 /\ ar_fs ar <= F1a /\ F1a + 128 <= ar_fs ar + 11571200 /\ 0 <= F1d / 8 <= 2 ^ 44 /\ 0 <= F1c / 8 <= 2 ^ 44 /\ 0 <= F3b / 8 <= 2 ^ 44 /\ 0 <= F1b / 8 <= 2 ^ 44 /\ 0 <= F3a / 8 <= 2 ^ 44 /\ 0 <= F1a / 8 <= 2 ^ 44)),
    forall (FAL : F1d mod 128 = 0 /\ F1c mod 128 = 0 /\ F3b mod 512 = 0 /\ F1b mod 128 = 0 /\ F3a mod 512 = 0 /\ F1a mod 128 = 0),
    forall (DJF : ar_fs ar + 11571200 <= 2147446784 \/ 2147446784 + 17592186048512 <= ar_fs ar),
    forall (ACC0 : acc L ar M model A LB1 Sp SCR XW ((F1c, 1, Sp - 1056) :: (F3b, 3, Sp - 928) :: (F1b, 1, Sp - 576) :: (F3a, 3, Sp - 416) :: (F1a, 1, Sp - 64) :: FF) M model A),
    forall (E8 : bv_unsigned (getr R (reg 8)) = Sp - 1216 + 128),
    forall (E9 : bv_unsigned (getr R (reg 9)) = Sp - 1216),
    forall (EX0 : forall x : nat, In x KS_ue3a1 -> getr R1 (reg x) = getr R (reg x)),
    forall (EX1 : getr R1 (reg 1) = Z_to_bv 64 723952),
    forall (EX2 : getr R1 (reg 2) = Z_to_bv 64 (Sp - 1216 - 48)),
    forall (EX3 : getr R1 (reg 8) = Z_to_bv 64 144),
    forall (EX4 : getr R1 (reg 11) = Z_to_bv 64 144),
    forall (ACR1 : acredit_ok L cr 144),
    forall (CRF1 : L5OMA.acredit_for L (adebit L cr 144) 2 (48 + 66)),
    forall (RP2 : regs_preserved R1 R2),
    forall (EOBJ : obj = u + 128),
    forall (OB16 : obj mod 16 = 0),
    forall (OB8 : obj mod 8 = 0),
    forall (OBR0 : 0 <= obj < 2 ^ 64),
    forall (OBR : 17594333495424 <= obj <= 140737479966720),
    forall (OCEIL : obj + 16 <= ahl_ceil ar),
    forall (DJU : u + 144 <= ar_fs ar \/ ar_fs ar + 11571200 <= u),
    forall (R2_10 : getr R2 (reg 10) = Z_to_bv 64 (obj - 128)),
    forall (Hk1 : In 1 [1; 2; 3]),
    forall (FLCd0 : cell_is RSEGS M (F1d + 128 - 8) 8 fl1d),
    forall (FLPd : ar_fs ar <= fl1d < ar_fs ar + 11571200),
    forall (SHDd0 : L5.defined M (F1d / 8 + SB) 16),
    forall (FDN : ar_fs ar <= F1d /\ F1d + 128 <= ar_fs ar + 11571200),
    forall (FDA : F1d mod 128 = 0),
    forall (AL_Fd : aligned F1d 64),
    forall (EX10 : forall x : nat, In x KS_ue3a2_mh -> getr R3 (reg x) = getr R2 (reg x)),
    forall (EX11 : getr R3 (reg 1) = Z_to_bv 64 590548),
    forall (EX12 : getr R3 (reg 2) = Z_to_bv 64 (Sp - 1216)),
    forall (EX13 : getr R3 (reg 8) = Z_to_bv 64 (Sp - 1216 + 128)),
    forall (EX14 : getr R3 (reg 9) = Z_to_bv 64 (Sp - 1216)),
    forall (EX15 : getr R3 (reg 10) = Z_to_bv 64 (F1d + 32)),
    forall (EX16 : getr R3 (reg 11) = Z_to_bv 64 141920),
    forall (EX17 : getr R3 (reg 21) = Z_to_bv 64 obj),
    forall (ACC3 : acc L ar M model A LB1 Sp SCR XW ((F1c, 1, Sp - 1056) :: (F3b, 3, Sp - 928) :: (F1b, 1, Sp - 576) :: (F3a, 3, Sp - 416) :: (F1a, 1, Sp - 64) :: FF) M3 model3 A2),
    forall (EX5 : forall x : nat, In x KS_ue3s1 -> getr R4 (reg x) = getr R3 (reg x)),
    forall (EX6 : getr R4 (reg 1) = Z_to_bv 64 589468),
    forall (EX18 : getr R4 (reg 2) = Z_to_bv 64 (Sp - 1216 - 64)),
    forall (EX19 : getr R4 (reg 8) = Z_to_bv 64 141920),
    forall (EX20 : getr R4 (reg 10) = Z_to_bv 64 141920),
    forall (EX22 : getr R4 (reg 11) = Z_to_bv 64 908088),
    forall (EX23 : getr R4 (reg 18) = Z_to_bv 64 (F1d + 32)),
    forall (EX24 : getr R4 (reg 21) = Z_to_bv 64 2147450880),
    forall (sR5 : getr R5 (reg 10) = Z_to_bv 64 41),
    forall (RP5 : regs_preserved R4 R5),
    forall (EX8 : forall x : nat, In x KS_ue3s2_bh -> getr R6 (reg x) = getr R5 (reg x)),
    forall (EX9 : getr R6 (reg 1) = Z_to_bv 64 856060),
    forall (EX31 : getr R6 (reg 2) = Z_to_bv 64 (Sp - 1216 - 80)),
    forall (EX32 : getr R6 (reg 8) = Z_to_bv 64 48),
    forall (EX33 : getr R6 (reg 9) = Z_to_bv 64 41),
    forall (EX34 : getr R6 (reg 10) = Z_to_bv 64 48),
    forall (EX35 : getr R6 (reg 11) = Z_to_bv 64 18446744073709551608),
    forall (EX36 : getr R6 (reg 20) = Z_to_bv 64 48),
    forall (ACR2 : acredit_ok L (adebit L cr 144) 48),
    forall (CRF2 : L5OMA.acredit_for L (adebit L (adebit L cr 144) 48) 1 66),
    forall (mR7 : getr R7 (reg 10) = Z_to_bv 64 msg),
    forall (RP7 : regs_preserved R6 R7),
    forall (DJM : msg + 48 <= ar_fs ar \/ ar_fs ar + 11571200 <= msg),
    forall (APmu : msg + 48 <= u \/ u + 144 <= msg),
    forall (MS16 : msg mod 16 = 0),
    forall (Z72 : L5KA.zeros_at M46 (obj - 72) 4),
    forall (MS8 : msg mod 8 = 0),
    forall (EX38 : forall x : nat, In x KS_ue3s3 -> getr R8 (reg x) = getr R7 (reg x)),
    forall (EX39 : getr R8 (reg 1) = Z_to_bv 64 589644),
    forall (EX40 : getr R8 (reg 2) = Z_to_bv 64 (Sp - 1216 - 64)),
    forall (EX41 : getr R8 (reg 8) = Z_to_bv 64 141920),
    forall (EX42 : getr R8 (reg 11) = Z_to_bv 64 141920),
    forall (EX43 : getr R8 (reg 12) = Z_to_bv 64 41),
    forall (EX44 : getr R8 (reg 19) = Z_to_bv 64 msg),
    forall (EX45 : getr R8 (reg 20) = Z_to_bv 64 49),
    forall (HMV : amemcpy_spec_at L ar SCFG HI 386992 false),
    forall (R8_10 : getr R8 (reg 10) = Z_to_bv 64 msg),
    forall (mR9 : getr R9 (reg 10) = Z_to_bv 64 msg),
    forall (RP9 : regs_preserved R8 R9),
    forall (SHAP : obj / 8 + 2147450864 + 18 <= F1d / 8 + 2147450880 \/ F1d / 8 + 2147450880 + 16 <= obj / 8 + 2147450864),
    forall (SHAPM : msg / 8 + 2147450880 + 6 <= F1d / 8 + 2147450880 \/ F1d / 8 + 2147450880 + 16 <= msg / 8 + 2147450880),
    forall (E41 : (msg + 41) / 8 = msg / 8 + 5),
    forall (EX37 : forall x : nat, In x KS_ue3s4 -> getr R10 (reg x) = getr R9 (reg x)),
    forall (EX46 : getr R10 (reg 1) = Z_to_bv 64 590592),
    forall (EX47 : getr R10 (reg 2) = Z_to_bv 64 (Sp - 1216 - 32)),
    forall (EX48 : getr R10 (reg 8) = Z_to_bv 64 obj),
    forall (EX49 : getr R10 (reg 9) = Z_to_bv 64 2147450880),
    forall (EX50 : getr R10 (reg 10) = Z_to_bv 64 obj),
    forall (EX51 : getr R10 (reg 11) = Z_to_bv 64 (F1d + 32)),
    forall (EX52 : getr R10 (reg 12) = Z_to_bv 64 908088),
    forall (EX53 : getr R10 (reg 18) = Z_to_bv 64 F1d),
    forall (EX54 : getr R10 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R3 (reg 19)))),
    forall (EX55 : getr R10 (reg 20) = Z_to_bv 64 (F1d + 32)),
    forall (EX56 : getr R10 (reg 21) = Z_to_bv 64 obj),
    forall (E10 : bv_unsigned (getr R10 (reg 10)) = obj),
    forall (EX7 : forall x : nat, In x KS_ue3c1 -> getr R11 (reg x) = getr R10 (reg x)),
    forall (EX29 : getr R11 (reg 1) = Z_to_bv 64 728356),
    forall (EX30 : getr R11 (reg 2) = Z_to_bv 64 (Sp - 1216 - 80)),
    forall (EX61 : getr R11 (reg 8) = getr R10 (reg 10)),
    forall (EX62 : getr R11 (reg 9) = Z_to_bv 64 msg),
    forall (EX63 : getr R11 (reg 10) = Z_to_bv 64 msg),
    forall (R11_8 : getr R11 (reg 8) = Z_to_bv 64 obj),
    forall (sR12 : getr R12 (reg 10) = Z_to_bv 64 41),
    forall (RP12 : regs_preserved R11 R12),
    forall (EX21 : forall x : nat, In x KS_ue3c2 -> getr R13 (reg x) = getr R12 (reg x)),
    forall (EX25 : getr R13 (reg 1) = Z_to_bv 64 856060),
    forall (EX26 : getr R13 (reg 2) = Z_to_bv 64 (Sp - 1216 - 96)),
    forall (EX27 : getr R13 (reg 8) = Z_to_bv 64 66),
    forall (EX70 : getr R13 (reg 10) = Z_to_bv 64 66),
    forall (EX71 : getr R13 (reg 18) = Z_to_bv 64 41),
    forall (ACR3 : acredit_ok L (adebit L (adebit L cr 144) 48) 66),
    forall (mR14 : getr R14 (reg 10) = Z_to_bv 64 ref),
    forall (RP14 : regs_preserved R13 R14),
    forall (DJR : ref + 66 <= ar_fs ar \/ ar_fs ar + 11571200 <= ref),
    forall (APru : ref + 66 <= u \/ u + 144 <= ref),
    forall (APrm : ref + 66 <= msg \/ msg + 48 <= ref),
    forall (RF16 : ref mod 16 = 0),
    forall (EX74 : forall x : nat, In x KS_ue3c3 -> getr R15 (reg x) = getr R14 (reg x)),
    forall (EX75 : getr R15 (reg 1) = Z_to_bv 64 728400),
    forall (EX76 : getr R15 (reg 2) = Z_to_bv 64 (Sp - 1216 - 80)),
    forall (EX77 : getr R15 (reg 8) = Z_to_bv 64 obj),
    forall (EX78 : getr R15 (reg 10) = Z_to_bv 64 (ref + 24)),
    forall (EX79 : getr R15 (reg 11) = Z_to_bv 64 msg),
    forall (EX80 : getr R15 (reg 12) = Z_to_bv 64 42),
    forall (EX81 : getr R15 (reg 19) = Z_to_bv 64 (ref + 24)),
    forall (EX82 : L5.u32_at RSEGS M46 (ref + 16) 0),
    forall (EX83 : L5.u64_at RSEGS M46 (ref + 8) 41),
    forall (EX84 : L5.u64_at RSEGS M46 ref 41),
    forall (HMC : amemcpy_spec_at L ar SCFG HI 385232 false),
    forall (mR16 : getr R16 (reg 10) = Z_to_bv 64 (ref + 24)),
    forall (RP16 : regs_preserved R15 R16),
    forall (EX72 : forall x : nat, In x KS_ue3c4 -> getr R17 (reg x) = getr R16 (reg x)),
    forall (EX73 : getr R17 (reg 1) = Z_to_bv 64 590596),
    forall (EX85 : getr R17 (reg 2) = Z_to_bv 64 (Sp - 1216)),
    forall (EX86 : getr R17 (reg 8) = Z_to_bv 64 (Sp - 1216 + 128)),
    forall (EX87 : getr R17 (reg 9) = Z_to_bv 64 (Sp - 1216)),
    forall (EX88 : getr R17 (reg 10) = Z_to_bv 64 861504),
    forall (EX89 : getr R17 (reg 18) = Z_to_bv 64 F1d),
    forall (EX90 : getr R17 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R3 (reg 19)))),
    forall (EX91 : L5.u64_at RSEGS M46 obj 861504),
    forall (EX92 : L5.u64_at RSEGS M46 (obj + 8) (ref + 24)),
    forall (RP18 : regs_preserved R17 R18),
    forall (EX28 : forall x : nat, In x KS_ue3c5 -> getr R19 (reg x) = getr R18 (reg x)),
    forall (EX57 : getr R19 (reg 10) = Z_to_bv 64 obj),
    forall (EX58 : getr R19 (reg 11) = Z_to_bv 64 861464),
    forall (EX : getr R19 (reg 12) = Z_to_bv 64 718724),
    forall (E19_10 : bv_unsigned (getr R19 (reg 10)) = obj),
    forall (EX64 : forall x : nat, In x KS_ue3t1 -> getr R20 (reg x) = getr R19 (reg x)),
    forall (EX65 : getr R20 (reg 1) = Z_to_bv 64 343324),
    forall (EX66 : getr R20 (reg 2) = Z_to_bv 64 (Sp - 1216 - 64)),
    forall (EX67 : getr R20 (reg 8) = Z_to_bv 64 (obj - 32)),
    forall (EX68 : getr R20 (reg 9) = Z_to_bv 64 883976),
    forall (EX69 : getr R20 (reg 10) = Z_to_bv 64 (obj - 32)),
    forall (EX93 : getr R20 (reg 11) = Z_to_bv 64 743680),
    forall (EX94 : getr R20 (reg 12) = Z_to_bv 64 722532),
    forall (EX95 : getr R20 (reg 18) = getr R19 (reg 10)),
    forall (EX99 : L5.u64_at RSEGS M46 (obj - 120) 1),
    forall (EX102 : L5.u64_at RSEGS M46 (obj - 88) 607608),
    forall (EX103 : L5.u64_at RSEGS M46 (obj - 104) 718724),
    forall (EX104 : L5.u64_at RSEGS M46 (obj - 112) 861464),
    forall (EX105 : L5.u64_at RSEGS M46 (obj - 96) 607876),
    forall (EX107 : L5.u32_at RSEGS M46 6357456 1),
    forall (RP21 : regs_preserved R20 R21),
    forall (AV8' : av mod 8 = 0),
    forall (STE : L5USA.xs_gd st = gd /\ L5USA.xs_av st = av /\ L5USA.xs_uid st = uid /\ L5USA.xs_rnd st = rnd /\ L5USA.xs_canary st = canary /\ L5USA.xs_hw st = hw),
    forall (EX112 : forall x : nat, In x KS_ue3t2_v1 -> getr R22 (reg x) = getr R21 (reg x)),
    forall (EX113 : getr R22 (reg 1) = Z_to_bv 64 590676),
    forall (EX114 : getr R22 (reg 2) = Z_to_bv 64 (Sp - 1216)),
    forall (EX115 : getr R22 (reg 6) = Z_to_bv 64 743680),
    forall (EX116 : getr R22 (reg 8) = Z_to_bv 64 (Sp - 1216 + 128)),
    forall (EX117 : getr R22 (reg 9) = Z_to_bv 64 (Sp - 1216)),
    forall (EX118 : getr R22 (reg 10) = Z_to_bv 64 (obj - 32)),
    forall (EX119 : getr R22 (reg 11) = Z_to_bv 64 0),
    forall (EX120 : getr R22 (reg 18) = Z_to_bv 64 F1d),
    forall (EX121 : L5.u64_at RSEGS M46 (obj - 8) (Sp - 1216 + 1216)),
    forall (EX122 : L5.u64_at RSEGS M46 (obj - 40) obj),
    forall (EX123 : L5.u64_at RSEGS M46 (obj - 48) 582452),
    forall (EX124 : L5.u64_at RSEGS M46 (obj - 56) 157040),
    forall (EX125 : L5.u64_at RSEGS M46 (obj - 64) 157179),
    forall (EX126 : L5.u32_at RSEGS M46 (obj - 68) 1),
    forall (EX127 : L5.u64_at RSEGS M46 (obj - 16) 0),
    forall (EX131 : L5.u64_at RSEGS M46 (obj - 32) 4849336966747728640),
    forall (EX132 : L5.u8_at RSEGS M46 6360113 1),
    forall (EX133 : L5.u8_at RSEGS M46 6360114 0),
    forall (EX134 : L5.u8_at RSEGS M46 6360115 1),
    forall (EX135 : L5.u8_at RSEGS M46 6360116 0),
    forall (EX136 : L5.u8_at RSEGS M46 6360117 1),
    forall (EX59 : L5.u8_at RSEGS M46 6360118 0),
    forall (FLNCd : ~ aclient L ar ([(d1, 64); (d2, 64); (d3, 64); (d4, 64)] ++ LB1) ((F1d, 1, Sp - 1184) :: (F1c, 1, Sp - 1056) :: (F3b, 3, Sp - 928) :: (F1b, 1, Sp - 576) :: (F3a, 3, Sp - 416) :: (F1a, 1, Sp - 64) :: FF) 0 0 fl1d),
    forall (FLAd : F1d + 128 <= fl1d \/ fl1d + 1 <= F1d),
    forall (AL_E : aligned (Sp - 1216) 32),
    forall (AL_F : aligned F1d 32),
    forall (EX97 : forall x : nat, In x KS_ue3p1a -> getr R23 (reg x) = getr R22 (reg x)),
    forall (EX98 : getr R23 (reg 11) = Z_to_bv 64 1),
    forall (EX96 : getr R23 (reg 19) = getr R22 (reg 10)),
    forall (R23_19 : getr R23 (reg 19) = Z_to_bv 64 (obj - 32)),
    forall (EX101 : forall x : nat, In x KS_ue3p1b -> getr R24 (reg x) = getr R23 (reg x)),
    forall (EX106 : getr R24 (reg 1) = Z_to_bv 64 590708),
    forall (EX128 : getr R24 (reg 10) = Z_to_bv 64 msg),
    forall (EX100 : getr R24 (reg 11) = Z_to_bv 64 48),
    forall (RP25 : regs_preserved R24 R25),
    forall (KS26 : forall x : nat, In x KS_ue3p1c -> getr R26 (reg x) = getr R25 (reg x)),
    forall (R26_10' : getr R26 (reg 10) = Z_to_bv 64 (obj - 32)),
    forall (EX108 : forall x : nat, In x KS_ue3r1 -> getr R27 (reg x) = getr R26 (reg x)),
    forall (EX109 : getr R27 (reg 1) = Z_to_bv 64 602296),
    forall (EX110 : getr R27 (reg 2) = Z_to_bv 64 (Sp - 1216 + 256)),
    forall (EX111 : getr R27 (reg 8) = Z_to_bv 64 (Sp - 1216 + 608)),
    forall (EX129 : getr R27 (reg 9) = Z_to_bv 64 (Sp - 1216 + 256)),
    forall (EX130 : getr R27 (reg 11) = Z_to_bv 64 0),
    forall (EX137 : getr R27 (reg 18) = Z_to_bv 64 (S F3b)),
    forall (EX138 : getr R27 (reg 19) = Z_to_bv 64 (F3b + 32)),
    forall (EX139 : getr R27 (reg 20) = Z_to_bv 64 (F3b + 96)),
    forall (EX140 : getr R27 (reg 21) = Z_to_bv 64 SB),
    forall (EX141 : getr R27 (reg 22) = Z_to_bv 64 (nz xo)),
    forall (EX142 : getr R27 (reg 23) = Z_to_bv 64 (F1b + 32)),
    forall (EX143 : getr R27 (reg 24) = Z_to_bv 64 (nz xo)),
    forall (EX144 : getr R27 (reg 25) = Z_to_bv 64 (nz w9)),
    forall (EX60 : getr R27 (reg 26) = Z_to_bv 64 (F3b + 48)),
    forall (Hk3 : In 3 [1; 2; 3]),
    forall (AL_E2 : aligned (Sp - 608) 32),
    forall (EX146 : forall x : nat, In x KS_ue3p2a -> getr R28 (reg x) = getr R27 (reg x)),
    forall (EX147 : getr R28 (reg 1) = Z_to_bv 64 602364),
    forall (EX148 : getr R28 (reg 10) = Z_to_bv 64 d1),
    forall (EX149 : getr R28 (reg 11) = Z_to_bv 64 64),
    forall (EX145 : getr R28 (reg 24) = getr R27 (reg 10)),
    forall (R28_24 : getr R28 (reg 24) = Z_to_bv 64 (obj - 32)),
    forall (RP29 : regs_preserved R28 R29),
    forall (EX151 : forall x : nat, In x KS_ue3p2c -> getr R30 (reg x) = getr R29 (reg x)),
    forall (EX152 : getr R30 (reg 1) = Z_to_bv 64 602408),
    forall (EX153 : getr R30 (reg 10) = Z_to_bv 64 d2),
    forall (EX150 : getr R30 (reg 11) = Z_to_bv 64 64),
    forall (RP31 : regs_preserved R30 R31),
    forall (R33_10 : getr R33 (reg 10) = Z_to_bv 64 (obj - 32)),
    forall (R33_2 : getr R33 (reg 2) = Z_to_bv 64 (Sp - 960)),
    forall (R33_3 : getr R33 (reg 3) = Z_to_bv 64 67584),
    forall (R33_4 : getr R33 (reg 4) = Z_to_bv 64 6360328),
    forall (R33_8 : getr R33 (reg 8) = Z_to_bv 64 (Sp - 608)),
    forall (EX155 : forall x : nat, In x KS_ue3r2 -> getr R34 (reg x) = getr R33 (reg x)),
    forall (EX156 : getr R34 (reg 1) = Z_to_bv 64 606580),
    forall (EX157 : getr R34 (reg 2) = Z_to_bv 64 (Sp - 1216 + 608)),
    forall (EX158 : getr R34 (reg 8) = Z_to_bv 64 (Sp - 1216 + 704)),
    forall (EX159 : getr R34 (reg 9) = Z_to_bv 64 (Sp - 1216 + 608)),
    forall (EX160 : getr R34 (reg 11) = Z_to_bv 64 0),
    forall (EX161 : getr R34 (reg 18) = Z_to_bv 64 F1b),
    forall (EX162 : getr R34 (reg 19) = Z_to_bv 64 (nz xo)),
    forall (EX163 : getr R34 (reg 20) = Z_to_bv 64 (Sp - 1216 + 712)),
    forall (EX164 : getr R34 (reg 21) = Z_to_bv 64 (F1b + 32)),
    forall (EX165 : getr R34 (reg 22) = Z_to_bv 64 (S F1b)),
    forall (EX166 : getr R34 (reg 23) = Z_to_bv 64 F1b),
    forall (EX167 : getr R34 (reg 24) = Z_to_bv 64 L5DSA.RETIRE_MAGIC),
    forall (EX168 : getr R34 (reg 25) = Z_to_bv 64 (nz w9)),
    forall (EX169 : getr R34 (reg 26) = Z_to_bv 64 (nz w10)),
    forall (EX154 : getr R34 (reg 27) = Z_to_bv 64 F3a),
    forall (KS35 : forall x : nat, In x KS_ue3p3 -> getr R35 (reg x) = getr R34 (reg x)),
    forall (R35_19 : getr R35 (reg 19) = getr R34 (reg 10)),
    forall (EX171 : forall x : nat, In x KS_ue3r3 -> getr R36 (reg x) = getr R35 (reg x)),
    forall (EX172 : getr R36 (reg 1) = Z_to_bv 64 604348),
    forall (EX173 : getr R36 (reg 2) = Z_to_bv 64 (Sp - 1216 + 704)),
    forall (EX174 : getr R36 (reg 8) = Z_to_bv 64 (nz xo)),
    forall (EX175 : getr R36 (reg 9) = Z_to_bv 64 (nz xs)),
    forall (EX176 : getr R36 (reg 11) = Z_to_bv 64 0),
    forall (EX177 : getr R36 (reg 18) = Z_to_bv 64 (S F3a)),
    forall (EX178 : getr R36 (reg 19) = Z_to_bv 64 (nz xo)),
    forall (EX179 : getr R36 (reg 20) = Z_to_bv 64 (F3a + 32)),
    forall (EX180 : getr R36 (reg 21) = Z_to_bv 64 (F3a + 96)),
    forall (EX181 : getr R36 (reg 22) = Z_to_bv 64 (F1a + 32)),
    forall (EX182 : getr R36 (reg 23) = Z_to_bv 64 (nz (S xo))),
    forall (EX170 : getr R36 (reg 24) = Z_to_bv 64 F3a),
    forall (EX184 : forall x : nat, In x KS_ue3p4 -> getr R37 (reg x) = getr R36 (reg x)),
    forall (EX185 : getr R37 (reg 8) = getr R36 (reg 10)),
    forall (EX183 : getr R37 (reg 11) = Z_to_bv 64 0),
    forall (EX187 : forall x : nat, In x KS_ue3r4 -> getr R38 (reg x) = getr R37 (reg x)),
    forall (EX188 : getr R38 (reg 1) = Z_to_bv 64 602292),
    forall (EX189 : getr R38 (reg 2) = Z_to_bv 64 (Sp - 1216 + 768)),
    forall (EX190 : getr R38 (reg 8) = Z_to_bv 64 (Sp - 1216 + 1120)),
    forall (EX191 : getr R38 (reg 9) = Z_to_bv 64 (Sp - 1216 + 768)),
    forall (EX186 : getr R38 (reg 11) = Z_to_bv 64 0),
    forall (EX193 : forall x : nat, In x KS_ue3p5a -> getr R39 (reg x) = getr R38 (reg x)),
    forall (EX194 : getr R39 (reg 10) = Z_to_bv 64 0),
    forall (EX192 : getr R39 (reg 24) = getr R38 (reg 10)),
    forall (R39_24 : getr R39 (reg 24) = Z_to_bv 64 (obj - 32)),
    forall (EX196 : forall x : nat, In x KS_ue3p2c -> getr R40 (reg x) = getr R39 (reg x)),
    forall (EX197 : getr R40 (reg 1) = Z_to_bv 64 602408),
    forall (EX198 : getr R40 (reg 10) = Z_to_bv 64 d3),
    forall (EX195 : getr R40 (reg 11) = Z_to_bv 64 64),
    forall (RP41 : regs_preserved R40 R41),
    forall (EX199 : forall x : nat, In x KS_ue3p5d -> getr R42 (reg x) = getr R41 (reg x)),
    forall (EX200 : getr R42 (reg 1) = Z_to_bv 64 602488),
    forall (EX201 : getr R42 (reg 10) = Z_to_bv 64 d4),
    forall (EX202 : getr R42 (reg 11) = Z_to_bv 64 64),
    forall (ACC42 : acc L ar M model A LB1 Sp SCR XW ((F1a, 1, Sp - 64) :: FF) M42 model42 A41),
    forall (RP43 : regs_preserved R42 R43),
    forall (R45_10 : getr R45 (reg 10) = Z_to_bv 64 (obj - 32)),
    forall (R45_2 : getr R45 (reg 2) = Z_to_bv 64 (Sp - 448)),
    forall (R45_3 : getr R45 (reg 3) = Z_to_bv 64 67584),
    forall (R45_4 : getr R45 (reg 4) = Z_to_bv 64 6360328),
    forall (R45_8 : getr R45 (reg 8) = Z_to_bv 64 (Sp - 96)),
    forall (NUM : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR) /\ (0 <= Sp - 1216 < 2 ^ 64 /\ 140735332552704 <= Sp - 1216 <= 140737488355264) /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47) /\ (obj = u + 128 /\ 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 16 <= ahl_ceil ar) /\ (17594333495296 <= msg /\ msg + 48 <= ahl_ceil ar) /\ 17594333495296 <= ref /\ ref + 66 <= ahl_ceil ar)),
    forall (EX204 : forall x : nat, In x KS_ue3r5 -> getr R46 (reg x) = getr R45 (reg x)),
    forall (EX205 : getr R46 (reg 1) = Z_to_bv 64 598052),
    forall (EX206 : getr R46 (reg 2) = Z_to_bv 64 (Sp - 1216 + 1120)),
    forall (EX207 : getr R46 (reg 8) = Z_to_bv 64 (Sp - 1216 + 1216)),
    forall (EX208 : getr R46 (reg 9) = Z_to_bv 64 (Sp - 1216 + 1120)),
    forall (EX209 : getr R46 (reg 11) = Z_to_bv 64 0),
    forall (EX210 : getr R46 (reg 18) = Z_to_bv 64 F1a),
    forall (EX211 : getr R46 (reg 19) = Z_to_bv 64 (nz xo)),
    forall (EX212 : getr R46 (reg 20) = Z_to_bv 64 (nz bo)),
    forall (EX213 : getr R46 (reg 21) = Z_to_bv 64 (F1a + 32)),
    forall (EX214 : getr R46 (reg 22) = Z_to_bv 64 (F1a / 8 + SB)),
    forall (EX215 : getr R46 (reg 23) = Z_to_bv 64 F1a),
    forall (EX216 : getr R46 (reg 24) = Z_to_bv 64 L5DSA.RETIRE_MAGIC),
    forall (EX217 : getr R46 (reg 25) = Z_to_bv 64 (L5DSA.U R0 25)),
    forall (EX218 : getr R46 (reg 26) = Z_to_bv 64 (L5DSA.U R0 26)),
    forall (EX203 : getr R46 (reg 27) = Z_to_bv 64 (L5DSA.U R0 27)),
    forall (CI46 : cinv L ar HI M42 model42 A41 LB1 ((F1a, 1, Sp - 64) :: FF) Sp SCR XW [(ref, 66); (u, 144)] M46 model46 ((F1c, 1, Sp - 1056) :: LKt) (adebit L (adebit L (adebit L cr 144) 48) 66) A43),
    forall (FRO : forall j : nat, (j < 11)%nat -> L5.u64_at RSEGS M46 (Sp - 88 + 8 * Z.of_nat j) (nth j [F1a; L5DSA.U R0 24; L5DSA.U R0 23; L5DSA.U R0 22; L5DSA.U R0 21; L5DSA.U R0 20; L5DSA.U R0 19; L5DSA.U R0 18; Sp; L5DSA.U R0 8; 581760] 0)),
    forall (FRD : forall j : nat, (j < 13)%nat -> L5.u64_at RSEGS M46 (Sp - 200 + 8 * Z.of_nat j) (nth j [L5DSA.U R0 27; L5DSA.U R0 26; L5DSA.U R0 25; L5DSA.RETIRE_MAGIC; F1a; F1a / 8 + SB; F1a + 32; nz bo; nz xo; F1a; Sp - 96; Sp; L5DSA.DIV_RET_O] 0)),
    forall (AUXV : forall j : nat, (j < 20)%nat -> L5.u64_at RSEGS M46 (av + 8 * Z.of_nat j) (nth j (L5USA.auxv20A uid rnd hw) 0)),
    forall (IC3 : L5.img_clear M46 892784 (892784 + 8)),
    forall (IC2 : L5.img_clear M46 892736 892768),
    forall (IC1 : L5.img_clear M46 65536 880640),
  srealizes RSEGS SCFG (cfg (fx:=fx46) R46 598052 M46 model46) K.
Proof.
  intros.
  (* [comment removed for export] *)
  assert (HinO : In (F1a, 1, Sp - 64) ((F1a, 1, Sp - 64) :: FF)) by (left; reflexivity).
  pose proof (L5DSA.frl_cell _ _ _ _ _ _ _ _ _ FRL1a) as FLCo0. pose proof (L5DSA.frl_fs _ _ _ _ _ _ _ _ _ FRL1a) as FLPo. unfold FS_BYTES in FLPo.
  pose proof (L5DSA.frl_nc _ _ _ _ _ _ _ _ _ FRL1a) as FLNCo. pose proof (L5DSA.frl_apart _ _ _ _ _ _ _ _ _ FRL1a) as FLAo. change (ff_bytes 1) with 128 in FLAo, FLCo0.
  pose proof (sh_op_defined M F1a SH1a) as SHDo0.
  pose proof CI46 as (HH46 & _).
  destruct (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ model46 F1a 1 _ _ fl1a HH HH46 ltac:(unfold L5DSA.ff_e3; do 5 right; left; reflexivity) (or_introl eq_refl) Hk1 FLCo0) as [FLCo46 _].
  pose proof (acc_shadow_defined L ar C HI LY HIok M model A LB1 Sp SCR XW _ _ F1a 1 (Sp - 64) M42 model42 A41 _ M46 model46 _ _ A43 ACC42 (sufl_refl L ar LB1 _) CI46 Hk1 HinO SHDo0) as SHDo46.
  destruct (cv_frame L ar C HI LY HIok M42 model42 A41 LB1 _ Sp SCR XW F1a 1 (Sp - 64) _ _ _ _ _ _ CI46 Hk1 fl1a FLCo46 ltac:(unfold FS_BYTES; exact FLPo) SHDo46) as (FDEFv & FWv & FSHWv & FLCv & FLWv & _ & _).
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *. replace (F1a + 128 - 8) with (F1a + 120) in FLCv by (clear; lia).
  pose proof BQ as (Q8 & QR & _). unfold L5.bo_dyn in BQD.
  pose proof (acc_kept_u8 L ar C HI LY HIok M model A LB1 Sp SCR XW XWIMG _ _ F1a 1 (Sp - 64) M42 model42 A41 _ M46 model46 _ _ A43 ACC42 (sufl_refl L ar LB1 _) CI46 Hk1 HinO (F1a + 32) (L5.bo_fb bq) ltac:(clear; lia) ltac:(change (ff_bytes 1) with 128; clear; lia) Q8) as Q8v.
  assert (ICp : L5.img_clear M46 860160 880640) by (intros i Hi; apply IC1; clear - Hi; lia).
  assert (AL_E6 : aligned Sp 32) by exact S32.
  assert (AL_Fo : aligned F1a 32). { unfold aligned. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - FAL. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof (L5AE2PD.pad2_run fx46 R46 (mrestrict (ahid A43 model46) M46) Sp F1a fl1a (L5.bo_fb bq)) as P.
  feed P ltac:(first [ rk | asm | assumption | fd_mem CI46 | (unfold SB in *; gmem) | (unfold L5DSA.RETIRE_MAGIC, SB in *; rk) | reflexivity
                     | (unfold numf in NUM; unfold numg in FN; clear - NUM FN DJF FLAo FLPo QR; lia) ]).
  destruct P as (fx47 & R47 & M47v & MS47 & MG47 & FZ47 & FL047 & KS47).
  apply (cinv_retire L ar C HI LY HIok M42 model42 A41 LB1 FF Sp SCR XW F1a 1 (Sp - 64) [(ref, 66); (u, 144)] M46 model46 _ _ A43 fx46 fx47 R46 598052 R47 598248 M47v
           (Wpad F1a 128 fl1a) fl1a K CI46 HS0 Hk1 FLCo46 ltac:(unfold FS_BYTES; exact FLPo)
           (fun X => FLNCo (aclient_appb L ar LB1 _ _ 0 0 fl1a X)) MS47 MG47 FZ47).
  { intros a Wa. unfold Wpad in Wa. change (ff_bytes 1 / 8) with 16. change (128 / 8) with 16 in Wa. clear - Wa. destruct Wa as [X|[X|X]]; [left; exact X | right; left; exact X | right; right; left; exact X]. }
  { intros a. apply Wpad_dec. }
  { exact FL047. }
  intros M47 model47 CI47 AH47 VIS47 FRM47.
  pose proof (pad_agree L ar C HI LY HIok M42 model42 A41 LB1 FF Sp SCR XW F1a 1 (Sp - 64) _ _ _ _ _ _ fl1a M47 CI46 Hk1 ltac:(unfold FS_BYTES; exact FLPo) FRM47) as AG.
  carry M46 M47 AG ltac:(cvis_tac [(ref, 66); (u, 144)]). clear AG FRM47 VIS47 MS47 MG47 FZ47 FL047 FDEFv FWv FSHWv FLCv FLWv Q8 Q8v QR SHDo46 FLCo46 HH46 ICp.
  assert (R47_1 : getr R47 (reg 1) = Z_to_bv 64 598052) by (rewrite (KS47 1%nat) by in_tac; rk).
  assert (R47_2 : getr R47 (reg 2) = Z_to_bv 64 (Sp - 1216 + 1120)) by (rewrite (KS47 2%nat) by in_tac; rk).
  assert (R47_3 : getr R47 (reg 3) = Z_to_bv 64 67584) by (rewrite (KS47 3%nat) by in_tac; rk).
  assert (R47_4 : getr R47 (reg 4) = Z_to_bv 64 6360328) by (rewrite (KS47 4%nat) by in_tac; rk).
  assert (R47_8 : getr R47 (reg 8) = Z_to_bv 64 (Sp - 1216 + 1216)) by (rewrite (KS47 8%nat) by in_tac; rk).
  assert (R47_10 : getr R47 (reg 10) = Z_to_bv 64 (obj - 32)) by (rewrite (KS47 10%nat) by in_tac; rk).
  assert (R47_25 : getr R47 (reg 25) = Z_to_bv 64 (L5DSA.U R0 25)) by (rewrite (KS47 25%nat) by in_tac; rk).
  assert (R47_26 : getr R47 (reg 26) = Z_to_bv 64 (L5DSA.U R0 26)) by (rewrite (KS47 26%nat) by in_tac; rk).
  assert (R47_27 : getr R47 (reg 27) = Z_to_bv 64 (L5DSA.U R0 27)) by (rewrite (KS47 27%nat) by in_tac; rk).
  clear KS47.
  (* [comment removed for export] *)
  pose proof (acc_weaken L ar M model A LB1 Sp SCR XW _ FF M42 model42 A41 ACC42 (sufl_app L ar LB1 [(F1a, 1, Sp - 64)] _)) as ACCf. clear ACC42.
  clear FLCo0 FLPo FLNCo FLAo SHDo0 HinO AL_Fo AL_E6.
  tidy CI47.
  (* [comment removed for export] *)
  destruct (cv_tls L ar C IL HI LY ILY HIok ICok UNWL M42 model42 A41 LB1 _ Sp SCR XW _ _ _ _ _ _ CI47) as (ctx & th & tbv & tev & blk & TLSC & TLSR & TLSI & TLSP & TLSB).
  cbv zeta in TLSC. rewrite HTP in TLSC. change (6360328 + 8) with 6360336 in TLSC. destruct TLSC as (TC1 & TC2 & TC3 & TC4 & TC5 & TC6).
  pose proof (TLSB u 144 ltac:(right; left; reflexivity)) as TB2. clear TLSB.
  pose proof NUM as NUMB. change numf with numg in NUMB.
  assert (NUM4 : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR)
                      /\ (0 <= Sp - 1216 < 2 ^ 64 /\ 140735332552704 <= Sp - 1216 /\ Sp - 1216 <= 140737488355264)
                      /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47)
                      /\ (obj = u + 128 /\ 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 16 <= ahl_ceil ar)
                      /\ (17594333495296 <= msg /\ msg + 48 <= ahl_ceil ar)
                      /\ (17594333495296 <= ref /\ ref + 66 <= ahl_ceil ar)
                      /\ (4096 <= ctx /\ ctx + 160 <= ahl_ceil ar /\ 4096 <= th /\ th + 64 <= ahl_ceil ar /\ 4096 <= blk /\ blk + 4096 <= ahl_ceil ar /\ 0 <= tbv < 2 ^ 64 /\ 0 <= tev < 2 ^ 64))).
  { unfold numf in *. clear - NUM TLSR. lia. }
  destruct TLSI as (DJ1 & DJ2 & DJ3). destruct TLSP as (DJ4 & DJ5 & DJ6). destruct TB2 as (DJ10 & DJ11 & DJ12).
  clear NUM. rename NUM4 into NUM. clear TLSR.
  expand_arr_at AUXV 20%nat av 0. expand_arr_at FRO 11%nat (Sp - 1216) 1128.
  pose proof (ue3r6_conc HFILL HCOPY HTLS fx47 R47 (mrestrict (ahid A43 model47) M47)
                (fun j => match j with 2%nat => Sp - 1216 | 10%nat => obj | 32%nat => av | 33%nat => canary | 34%nat => uid | 36%nat => rnd | 39%nat => hw | 40%nat => ctx | 41%nat => th | 42%nat => blk | 43%nat => tbv | 44%nat => tev | 45%nat => L5DSA.U R0 8 | 46%nat => L5DSA.U R0 18 | 47%nat => L5DSA.U R0 19 | 48%nat => L5DSA.U R0 20 | 49%nat => L5DSA.U R0 21 | 50%nat => L5DSA.U R0 22 | 51%nat => L5DSA.U R0 23 | 52%nat => L5DSA.U R0 24 | _ => 0 end)) as P. cbn beta iota in P.
  feed_rng P ltac:(first [ apply nz_range | apply UR | apply BL.bvu_range | (unfold L5DSA.U; apply BL.bvu_range) | nlia | (unfold S, SB, L5DSA.RETIRE_MAGIC; unfold numg in FN; clear - FN; lia) ]).
  feed P ltac:(first [fcell CI47 | fdp CI47]).
  repeat match goal with H : L5.u64_at _ M47 (Sp - 1216 + _) _ |- _ => clear H | H : L5.u64_at _ M47 (av + _) _ |- _ => clear H | H : L5.u64_at _ M47 av _ |- _ => clear H end.
  piece_step CI47 XWIMG P (fun a => (Sp - 1216 - 10560) <= a < (Sp - 1216 - 10560) + 11680) fx48 R48 M48 model48 CI48.
  clear TC1 TC2 TC3 TC4 TC5 TC6 DJ1 DJ2 DJ3 DJ4 DJ5 DJ6 DJ10 DJ11 DJ12.
  clear NUM. rename NUMB into NUM. change numg with numf in NUM. clear ctx th tbv tev blk.
  (* [comment removed for export] *)
  destruct STE as (ST1 & ST2 & ST3 & ST4 & ST5 & ST6).
  destruct (acc_step L ar HI M model A LB1 Sp SCR XW FF FF M42 model42 A41 _ M48 model48 _ _ A43 ACCf (sufl_refl L ar LB1 FF) CI48) as (EKf & DKf & RTf & IAf).
  destruct CI48 as (HH48 & AM48 & _ & _ & STK48 & SH48 & _ & _).
  assert (EU : u = obj - 128) by (unfold numf in NUM; clear - NUM; lia).
  apply (KONT fx48 R48 M48 model48 ((ref, 66) :: (obj - 128, 144) :: LB1) (adebit L (adebit L (adebit L cr 144) 48) 66) ((F1c, 1, Sp - 1056) :: LKt) A43).
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
  - unfold L5USA.e3_landed. split. 2: split.
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
    + unfold L5USA.EXC23_SZ, L5USA.MSG3_SZ, L5USA.REF3_SZ. rewrite <- !L5OMA.adebits_1, !L5OMA.adebits_add. change (1 + (1 + 1)) with 3. change (144 + (48 + 66)) with (144 + 48 + 66). unfold credit_le. clear; lia.
    + exists (F1c, 1, Sp - 1056), LKt. split. reflexivity. split. reflexivity. exact LKI.
  - split. exact EKf. split. exact (astk_defined ar M48 Sp SCR (Sp - SCR) SCR STK48 ltac:(clear; lia) ltac:(clear; lia)). exact DKf.
  - exact RTf.
  - exact IAf.
  - exact AM48.
  - rewrite <- EU. exact HH48.
Qed.

End WithIface.
End SCFG_1.
End L5AE3S15.
