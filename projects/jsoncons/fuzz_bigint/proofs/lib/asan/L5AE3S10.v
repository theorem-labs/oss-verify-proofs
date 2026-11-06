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
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ParseSpecsA L5OpmodSpecsA L5DivSpecsA L5UnwindSpecsA XIcptA XIcptAs0Kit L5AUnwK L5AUnwK2 L5AE1K L5AE2K L5AE3K L5AE2PP L5AE2Pad L5AE3P1 L5AE3P2 L5AE3P3 L5AE3P4 L5AE3P5 L5AE3P6 L5AE3P7 L5AE3P8 L5AE3P9 L5AE3P10 L5AE3P11 L5AE3PP L5AE3Pad L5AUnwK3 L5AUnwK4 L5DivInnerSpecsA L5AOpdel L5AE3S11.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Set Printing Width 100000. Set Printing Depth 100000.

Module L5AE3S10.
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

Lemma e3_s10 :
  forall (R0 : bvmap 5 word) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB1 : list (Z * Z)) (FF : list fframe) (LK : list fframe) (LKt : list fframe) (cr : credit) (A : list (Z * Z)) (Sp : Z) (SCR : Z) (xo : Z) (gd : bool) (av : Z) (uid : Z) (rnd : Z) (canary : Z) (hw : Z) (F1a : Z) (fl1a : Z) (F3a : Z) (fl3a : Z) (F1b : Z) (fl1b : Z) (F3b : Z) (fl3b : Z) (F1c : Z) (fl1c : Z) (F1d : Z) (fl1d : Z) (d1 : Z) (d2 : Z) (d3 : Z) (d4 : Z) (qx : Z) (bo : Z) (LB0 : list (Z * Z)) (lenX : nat) (w9 : Z) (w10 : Z) (xs : Z) (fbx : Z) (fd0N : Z) (fn0N : Z) (fnN : Z) (fdenN : Z) (w1 : Z) (fd0 : Z) (fn0 : Z) (fn : Z) (fden : Z) (v0 : Z) (v1 : Z) (v2 : Z) (v3 : Z) (nd0 : nat) (nn0 : nat) (nn : nat) (nd : nat) (M3 : word -> option byte) (errv : Z) (R1 : bvmap 5 word) (R2 : bvmap 5 word) (A2 : list (Z * Z)) (u : Z) (obj : Z) (R3 : bvmap 5 word) (model3 : Model) (R4 : bvmap 5 word) (R5 : bvmap 5 word) (R6 : bvmap 5 word) (R7 : bvmap 5 word) (A7 : list (Z * Z)) (msg : Z) (M8 : word -> option byte) (R8 : bvmap 5 word) (model8 : Model) (R9 : bvmap 5 word) (R10 : bvmap 5 word) (R11 : bvmap 5 word) (R12 : bvmap 5 word) (R13 : bvmap 5 word) (R14 : bvmap 5 word) (A14 : list (Z * Z)) (ref : Z) (R15 : bvmap 5 word) (R16 : bvmap 5 word) (R17 : bvmap 5 word) (R18 : bvmap 5 word) (R19 : bvmap 5 word) (R20 : bvmap 5 word) (R21 : bvmap 5 word) (st : L5USA.XS) (R22 : bvmap 5 word) (R23 : bvmap 5 word) (R24 : bvmap 5 word) (R25 : bvmap 5 word) (A25 : list (Z * Z)) (R26 : bvmap 5 word) (M27 : word -> option byte) (fx27 : FPState) (R27 : bvmap 5 word) (model27 : Model),
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
    forall (m2 : L5.u64_at RSEGS M27 (Sp - 904) F3b),
    forall (m3 : L5.u64_at RSEGS M27 (Sp - 888) F3b),
    forall (m4 : L5.u64_at RSEGS M27 (Sp - 880) (F3b + 96)),
    forall (m5 : L5.u64_at RSEGS M27 (Sp - 872) (F3b + 32)),
    forall (m8 : L5.u64_at RSEGS M27 (Sp - 848) (S F3b)),
    forall (DEN0Nf : L5.u8_at RSEGS M27 (Sp - 776) fd0N),
    forall (DEN0Nr : 0 <= fd0N < 256),
    forall (DEN0Nt : Z.testbit fd0N 0 = false),
    forall (NUM0Nf : L5.u8_at RSEGS M27 (Sp - 744) fn0N),
    forall (NUM0Nr : 0 <= fn0N < 256),
    forall (NUM0Nt : Z.testbit fn0N 0 = true),
    forall (NUM0Nc : L5.u64_at RSEGS M27 (Sp - 744 + 16) 8),
    forall (NUM0Np : L5.u64_at RSEGS M27 (Sp - 744 + 24) d1),
    forall (NUMN : L5.big_at RSEGS M (F3b + 96) {| L5.bo_fb := fnN; L5.bo_len := 0; L5.bo_st := L5.BDyn 8 d2 |}),
    forall (NUMNT : Z.testbit fnN 1 = false),
    forall (DENN : L5.big_at RSEGS M (F3b + 32) {| L5.bo_fb := fdenN; L5.bo_len := 1; L5.bo_st := L5.BInl L5DSA.MWORD w1 |}),
    forall (DENNT : Z.testbit fdenN 1 = false),
    forall (ZQ : L5DIA.zero_obj M (F1b + 32)),
    forall (MWf : L5.u8_at RSEGS M27 (Sp - 504) 0),
    forall (o2 : L5.u64_at RSEGS M27 (Sp - 392) F3a),
    forall (o3 : L5.u64_at RSEGS M27 (Sp - 376) F3a),
    forall (o4 : L5.u64_at RSEGS M27 (Sp - 368) (F3a + 96)),
    forall (o5 : L5.u64_at RSEGS M27 (Sp - 360) (F3a + 32)),
    forall (o8 : L5.u64_at RSEGS M27 (Sp - 336) (S F3a)),
    forall (DEN0f : L5.u8_at RSEGS M27 (Sp - 264) fd0),
    forall (DEN0r : 0 <= fd0 < 256),
    forall (DEN0t : Z.testbit fd0 0 = false),
    forall (NUM0f : L5.u8_at RSEGS M27 (Sp - 232) fn0),
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
    forall (EC0 : L5.u64_at RSEGS M27 6357448 0),
    forall (GD0 : L5.u8_at RSEGS M27 6358000 (if gd then 1 else 0)),
    forall (GD1 : L5.u8_at RSEGS M27 6358001 (if gd then 1 else 0)),
    forall (TDL : L5.u64_at RSEGS M27 6360280 6492112),
    forall (MSG0 : L5.u64_at RSEGS M27 6492152 0),
    forall (ERR : L5.u32_at RSEGS M27 6360164 errv),
    forall (ERRR : 0 <= errv < 2 ^ 64),
    forall (CAN : L5.u64_at RSEGS M27 6491464 canary),
    forall (AUXP : L5.u64_at RSEGS M27 6492064 av),
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
    forall (Z72 : L5KA.zeros_at M27 (obj - 72) 4),
    forall (MS8 : msg mod 8 = 0),
    forall (EX38 : forall x : nat, In x KS_ue3s3 -> getr R8 (reg x) = getr R7 (reg x)),
    forall (EX39 : getr R8 (reg 1) = Z_to_bv 64 589644),
    forall (EX40 : getr R8 (reg 2) = Z_to_bv 64 (Sp - 1216 - 64)),
    forall (EX41 : getr R8 (reg 8) = Z_to_bv 64 141920),
    forall (EX42 : getr R8 (reg 11) = Z_to_bv 64 141920),
    forall (EX43 : getr R8 (reg 12) = Z_to_bv 64 41),
    forall (EX44 : getr R8 (reg 19) = Z_to_bv 64 msg),
    forall (EX45 : getr R8 (reg 20) = Z_to_bv 64 49),
    forall (KMSG : keep (L5.u64_at RSEGS M8 (F1d + 32) 49 /\ L5.u64_at RSEGS M8 (F1d + 40) 41 /\ L5.u64_at RSEGS M8 (F1d + 48) msg)),
    forall (SHDd8 : L5.defined M8 (F1d / 8 + SB) 16),
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
    forall (EX82 : L5.u32_at RSEGS M27 (ref + 16) 0),
    forall (EX83 : L5.u64_at RSEGS M27 (ref + 8) 41),
    forall (EX84 : L5.u64_at RSEGS M27 ref 41),
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
    forall (EX91 : L5.u64_at RSEGS M27 obj 861504),
    forall (EX92 : L5.u64_at RSEGS M27 (obj + 8) (ref + 24)),
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
    forall (EX99 : L5.u64_at RSEGS M27 (obj - 120) 1),
    forall (EX102 : L5.u64_at RSEGS M27 (obj - 88) 607608),
    forall (EX103 : L5.u64_at RSEGS M27 (obj - 104) 718724),
    forall (EX104 : L5.u64_at RSEGS M27 (obj - 112) 861464),
    forall (EX105 : L5.u64_at RSEGS M27 (obj - 96) 607876),
    forall (EX107 : L5.u32_at RSEGS M27 6357456 1),
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
    forall (EX121 : L5.u64_at RSEGS M27 (obj - 8) (Sp - 1216 + 1216)),
    forall (EX122 : L5.u64_at RSEGS M27 (obj - 40) obj),
    forall (EX123 : L5.u64_at RSEGS M27 (obj - 48) 582452),
    forall (EX124 : L5.u64_at RSEGS M27 (obj - 56) 157040),
    forall (EX125 : L5.u64_at RSEGS M27 (obj - 64) 157179),
    forall (EX126 : L5.u32_at RSEGS M27 (obj - 68) 1),
    forall (EX127 : L5.u64_at RSEGS M27 (obj - 16) 0),
    forall (EX131 : L5.u64_at RSEGS M27 (obj - 32) 4849336966747728640),
    forall (EX132 : L5.u8_at RSEGS M27 6360113 1),
    forall (EX133 : L5.u8_at RSEGS M27 6360114 0),
    forall (EX134 : L5.u8_at RSEGS M27 6360115 1),
    forall (EX135 : L5.u8_at RSEGS M27 6360116 0),
    forall (EX136 : L5.u8_at RSEGS M27 6360117 1),
    forall (EX59 : L5.u8_at RSEGS M27 6360118 0),
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
    forall (NUM : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR) /\ (0 <= Sp - 1216 < 2 ^ 64 /\ 140735332552704 <= Sp - 1216 <= 140737488355264) /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47) /\ (obj = u + 128 /\ 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 16 <= ahl_ceil ar) /\ (17594333495296 <= msg /\ msg + 48 <= ahl_ceil ar) /\ 17594333495296 <= ref /\ ref + 66 <= ahl_ceil ar)),
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
    forall (FRO : forall j : nat, (j < 11)%nat -> L5.u64_at RSEGS M27 (Sp - 88 + 8 * Z.of_nat j) (nth j [F1a; L5DSA.U R0 24; L5DSA.U R0 23; L5DSA.U R0 22; L5DSA.U R0 21; L5DSA.U R0 20; L5DSA.U R0 19; L5DSA.U R0 18; Sp; L5DSA.U R0 8; 581760] 0)),
    forall (FRD : forall j : nat, (j < 13)%nat -> L5.u64_at RSEGS M27 (Sp - 200 + 8 * Z.of_nat j) (nth j [L5DSA.U R0 27; L5DSA.U R0 26; L5DSA.U R0 25; L5DSA.RETIRE_MAGIC; F1a; F1a / 8 + SB; F1a + 32; nz bo; nz xo; F1a; Sp - 96; Sp; L5DSA.DIV_RET_O] 0)),
    forall (FRU : forall j : nat, (j < 3)%nat -> L5.u64_at RSEGS M27 (Sp - 472 + 8 * Z.of_nat j) (nth j [Sp - 448; Sp - 96; L5DSA.UNNORM_RET] 0)),
    forall (FRQ : forall j : nat, (j < 11)%nat -> L5.u64_at RSEGS M27 (Sp - 600 + 8 * Z.of_nat j) (nth j [F1b; F3a; nz (S xo); F1a + 32; F3a + 96; F3a + 32; nz xo; S F3a; nz xs; nz xo; L5DSA.DIVEQ_RET] 0)),
    forall (FRN : forall j : nat, (j < 13)%nat -> L5.u64_at RSEGS M27 (Sp - 712 + 8 * Z.of_nat j) (nth j [F3a; nz w10; nz w9; L5DSA.RETIRE_MAGIC; F1b; S F1b; F1b + 32; Sp - 504; nz xo; F1b; Sp - 608; Sp - 512; L5DSA.DIV_RET_N] 0)),
    forall (FRZ : forall j : nat, (j < 13)%nat -> L5.u64_at RSEGS M27 (Sp - 1064 + 8 * Z.of_nat j) (nth j [F1c; F3b + 48; nz w9; nz xo; F1b + 32; nz xo; SB; F3b + 96; F3b + 32; S F3b; Sp - 960; Sp - 608; L5DSA.RESIZE_RET_G] 0)),
    forall (FRA : forall j : nat, (j < 13)%nat -> L5.u64_at RSEGS M27 (Sp - 1192 + 8 * Z.of_nat j) (nth j [F1d; nz (S (xo + 8)); nz (Z.of_nat lenX); SB; F1c; S F1c; nz (xo + 8); nz xo; 2 ^ 64 - 1; F1c; Sp - 1088; Sp - 960; L5DSA.RESERVE_RET] 0)),
    forall (AUXV : forall j : nat, (j < 20)%nat -> L5.u64_at RSEGS M27 (av + 8 * Z.of_nat j) (nth j (L5USA.auxv20A uid rnd hw) 0)),
    forall (IC3 : L5.img_clear M27 892784 (892784 + 8)),
    forall (IC2 : L5.img_clear M27 892736 892768),
    forall (IC1 : L5.img_clear M27 65536 880640),
    forall (CI27' : cinv L ar HI M8 model8 A7 LB1 ((F3b, 3, Sp - 928) :: (F1b, 1, Sp - 576) :: (F3a, 3, Sp - 416) :: (F1a, 1, Sp - 64) :: FF) Sp SCR XW [(ref, 66); (u, 144); (d1, 64); (d2, 64); (d3, 64); (d4, 64)] M27 model27 ((F1c, 1, Sp - 1056) :: LKt) (adebit L (adebit L (adebit L cr 144) 48) 66) A25),
    forall (ACCb : acc L ar M model A LB1 Sp SCR XW ((F3b, 3, Sp - 928) :: (F1b, 1, Sp - 576) :: (F3a, 3, Sp - 416) :: (F1a, 1, Sp - 64) :: FF) M8 model8 A7),
  srealizes RSEGS SCFG (cfg (fx:=fx27) R27 602296 M27 model27) K.
Proof.
  intros.
  (* [comment removed for export] *)
  assert (Hk3 : In 3 [1; 2; 3]) by (right; right; left; reflexivity).
  assert (HinB : In (F3b, 3, Sp - 928) ((F3b, 3, Sp - 928) :: (F1b, 1, Sp - 576) :: (F3a, 3, Sp - 416) :: (F1a, 1, Sp - 64) :: FF)) by (left; reflexivity).
  pose proof (L5DSA.frl_cell _ _ _ _ _ _ _ _ _ FRL3b) as FLCb0. pose proof (L5DSA.frl_fs _ _ _ _ _ _ _ _ _ FRL3b) as FLPb. unfold FS_BYTES in FLPb.
  pose proof (L5DSA.frl_nc _ _ _ _ _ _ _ _ _ FRL3b) as FLNCb. pose proof (L5DSA.frl_apart _ _ _ _ _ _ _ _ _ FRL3b) as FLAb. change (ff_bytes 3) with 512 in FLAb, FLCb0.
  pose proof (sh_div_defined M F3b _ _ _ _ _ SH3b) as SHDb0.
  (* [comment removed for export] *)
  assert (InD1 : In (d1, 64) ([(ref, 66); (u, 144); (d1, 64); (d2, 64); (d3, 64); (d4, 64)] ++ LB1)) by (right; right; left; reflexivity).
  assert (InD2 : In (d2, 64) ([(ref, 66); (u, 144); (d1, 64); (d2, 64); (d3, 64); (d4, 64)] ++ LB1)) by (right; right; right; left; reflexivity).
  pose proof (cv_blk L ar C HI LY HIok M8 model8 A7 LB1 _ Sp SCR XW _ _ _ _ _ _ CI27' d1 64 InD1) as (BRd1 & _ & _).
  pose proof (cv_blk L ar C HI LY HIok M8 model8 A7 LB1 _ Sp SCR XW _ _ _ _ _ _ CI27' d2 64 InD2) as (BRd2 & _ & _).
  assert (DN : numg (4096 <= d1 /\ d1 + 64 <= 2 ^ 47 /\ 4096 <= d2 /\ d2 + 64 <= 2 ^ 47)) by (unfold numg; clear - BRd1 BRd2; lia).
  clear BRd1 BRd2.
  assert (ICp : L5.img_clear M27 860160 880640) by (intros i Hi; apply IC1; clear - Hi; lia).
  assert (AL_E2 : aligned (Sp - 608) 32). { unfold aligned. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - S32. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof (ue3p2a_conc fx27 R27 (mrestrict (ahid A25 model27) M27) (fun j => match j with 2%nat => Sp - 608 | 58%nat => 602296 | 60%nat => fn0N | 61%nat => d1 | 62%nat => 8 | 63%nat => fd0N | _ => 0 end)) as P. cbn beta iota in P.
  padfeed P CI27' ltac:(unfold numf in NUM; unfold numg in FN, DN; clear - NUM FN DN NUM0Nr DEN0Nr; lia).
  pure_step CI27' XWIMG P fx28 R28 model28 CI28.
  assert (R28_24 : getr R28 (reg 24) = Z_to_bv 64 (obj - 32)) by (match goal with H : getr R28 (reg 24) = getr R27 (reg 10) |- _ => rewrite H end; rk).
  change (8 * 8) with 64 in *.
  (* [comment removed for export] *)
  pose proof (cinv_num L ar HI M8 model8 A7 LB1 _ Sp SCR XW _ _ _ _ _ _ CI28) as (_ & SLO28 & SHI28 & SPT28).
  pose proof (cinv_nodup L ar C HI HIok _ _ _ _ _ _ _ _ _ _ _ _ _ _ CI28) as ND. cbn [app map fst] in ND.
  assert (NE1 : ref =? d1 = false) by (apply Z.eqb_neq; apply (nodup_neq _ _ _ ND); right; left; reflexivity).
  assert (NE2 : u =? d1 = false) by (apply Z.eqb_neq; apply (nodup_neq _ _ _ (nodup_tl _ _ ND)); left; reflexivity).
  assert (NE3 : ref =? d2 = false) by (apply Z.eqb_neq; apply (nodup_neq _ _ _ ND); right; right; left; reflexivity).
  assert (NE4 : u =? d2 = false) by (apply Z.eqb_neq; apply (nodup_neq _ _ _ (nodup_tl _ _ ND)); right; left; reflexivity).
  clear ND.
  apply (cinv_opdel L ar C HI HIok M8 model8 A7 LB1 _ Sp SCR XW _ M27 model28 _ _ A25 fx28 R28 d1 64 (Sp - 960) 602364 K (L5ADEL.opdel_sized_ok L ar C HI LY HIok) CI28 HK HS0);
    [ right; right; left; reflexivity | rk | rk | split; [clear; lia | reflexivity] | rk | rewrite HTP; rk | apply mod16_sub; [exact A16 | reflexivity]
    | unfold L5CSA.OPDEL_SCR, L5CSA.MALLOC_SCR; clear - HSCR; lia | clear; lia | ].
  intros fx29 R29 M29 model29 A29 RP29 CI29 PRES29.
  cbn [lb_remove fst] in CI29, PRES29. rewrite NE1, NE2, Z.eqb_refl in CI29, PRES29.
  pose proof (opdel_ag L ar C LY UNWL _ _ _ _ _ M27 M29 PRES29 ltac:(unfold L5CSA.OPDEL_SCR, L5CSA.MALLOC_SCR; clear - SLO28 HSCR; lia) ltac:(unfold L5CSA.OPDEL_SCR, L5CSA.MALLOC_SCR; clear; lia)) as AG.
  carry M27 M29 AG sd_call. clear AG PRES29 SLO28 SHI28 SPT28 NE1 NE2 ICp CI27' CI28.
  (* [comment removed for export] *)
  pose proof CI29 as (HH29 & _).
  destruct (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ model29 F3b 3 _ _ fl3b HH HH29 ltac:(unfold L5DSA.ff_e3; right; right; left; reflexivity) (or_introl eq_refl) Hk3 FLCb0) as [FLCb29 _].
  pose proof (acc_shadow_defined L ar C HI LY HIok M model A LB1 Sp SCR XW _ _ F3b 3 (Sp - 928) M8 model8 A7 _ M29 model29 _ _ A29 ACCb (sufl_refl L ar LB1 _) CI29 Hk3 HinB SHDb0) as SHDb29.
  destruct (cv_frame L ar C HI LY HIok M8 model8 A7 LB1 _ Sp SCR XW F3b 3 (Sp - 928) _ _ _ _ _ _ CI29 Hk3 fl3b FLCb29 ltac:(unfold FS_BYTES; exact FLPb) SHDb29) as (FDEFv & FWv & FSHWv & FLCv & FLWv & _ & _).
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *. replace (F3b + 512 - 8) with (F3b + 504) in FLCv by (clear; lia).
  pose proof NUMN as (NB8 & NBR & _ & NBT & NBC & NBP & _). cbn [L5.bo_fb L5.bo_st L5.bo_len] in NB8, NBR, NBT, NBC, NBP.
  replace (F3b + 96 + 16) with (F3b + 112) in NBC by (clear; lia). replace (F3b + 96 + 24) with (F3b + 120) in NBP by (clear; lia).
  pose proof (acc_kept_u8 L ar C HI LY HIok M model A LB1 Sp SCR XW XWIMG _ _ F3b 3 (Sp - 928) M8 model8 A7 _ M29 model29 _ _ A29 ACCb (sufl_refl L ar LB1 _) CI29 Hk3 HinB (F3b + 96) fnN
                ltac:(clear; lia) ltac:(change (ff_bytes 3) with 512; clear; lia) NB8) as NB8v.
  pose proof (acc_kept_u64 L ar C HI LY HIok M model A LB1 Sp SCR XW XWIMG _ _ F3b 3 (Sp - 928) M8 model8 A7 _ M29 model29 _ _ A29 ACCb (sufl_refl L ar LB1 _) CI29 Hk3 HinB (F3b + 112) 8
                ltac:(clear; lia) ltac:(change (ff_bytes 3) with 512; clear; lia) NBC) as NBCv.
  pose proof (acc_kept_u64 L ar C HI LY HIok M model A LB1 Sp SCR XW XWIMG _ _ F3b 3 (Sp - 928) M8 model8 A7 _ M29 model29 _ _ A29 ACCb (sufl_refl L ar LB1 _) CI29 Hk3 HinB (F3b + 120) d2
                ltac:(clear; lia) ltac:(change (ff_bytes 3) with 512; clear; lia) NBP) as NBPv.
  assert (ICp : L5.img_clear M29 860160 880640) by (intros i Hi; apply IC1; clear - Hi; lia).
  assert (AL_Fb : aligned F3b 32). { unfold aligned. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - FAL. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof (ue3p2c_conc fx29 R29 (mrestrict (ahid A29 model29) M29)
                (fun j => match j with 2%nat => Sp - 608 | 40%nat => F3b | 41%nat => fl3b | 58%nat => U R29 1 | 60%nat => fnN | 61%nat => d2 | 62%nat => 8 | _ => 0 end)) as P. cbn beta iota in P.
  padfeed P CI29 ltac:(unfold numf in NUM; unfold numg in FN, DN; clear - NUM FN DN DJF FLAb FLPb NBR; lia).
  pure_step CI29 XWIMG P fx30 R30 model30 CI30.
  change (8 * 8) with 64 in *.
  (* [comment removed for export] *)
  pose proof (cinv_num L ar HI M8 model8 A7 LB1 _ Sp SCR XW _ _ _ _ _ _ CI30) as (_ & SLO30 & SHI30 & SPT30).
  apply (cinv_opdel L ar C HI HIok M8 model8 A7 LB1 _ Sp SCR XW _ M29 model30 _ _ A29 fx30 R30 d2 64 (Sp - 960) 602408 K (L5ADEL.opdel_sized_ok L ar C HI LY HIok) CI30 HK HS0);
    [ right; right; left; reflexivity | rk | rk | split; [clear; lia | reflexivity] | rk | rewrite HTP; rk | apply mod16_sub; [exact A16 | reflexivity]
    | unfold L5CSA.OPDEL_SCR, L5CSA.MALLOC_SCR; clear - HSCR; lia | clear; lia | ].
  intros fx31 R31 M31 model31 A31 RP31 CI31 PRES31.
  cbn [lb_remove fst] in CI31, PRES31. rewrite NE3, NE4, Z.eqb_refl in CI31, PRES31.
  pose proof (opdel_ag L ar C LY UNWL _ _ _ _ _ M29 M31 PRES31 ltac:(unfold L5CSA.OPDEL_SCR, L5CSA.MALLOC_SCR; clear - SLO30 HSCR; lia) ltac:(unfold L5CSA.OPDEL_SCR, L5CSA.MALLOC_SCR; clear; lia)) as AG.
  carry M29 M31 AG sd_call. clear AG PRES31 SLO30 SHI30 SPT30 NE3 NE4 ICp CI29 CI30.
  clear FDEFv FWv FSHWv FLCv FLWv NB8v NBCv NBPv FLCb29 SHDb29 HH29 NB8 NBR NBT NBC NBP DN InD1 InD2.
  (* [comment removed for export] *)
  pose proof CI31 as (HH31 & _).
  destruct (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ model31 F3b 3 _ _ fl3b HH HH31 ltac:(unfold L5DSA.ff_e3; right; right; left; reflexivity) (or_introl eq_refl) Hk3 FLCb0) as [FLCb31 _].
  pose proof (acc_shadow_defined L ar C HI LY HIok M model A LB1 Sp SCR XW _ _ F3b 3 (Sp - 928) M8 model8 A7 _ M31 model31 _ _ A31 ACCb (sufl_refl L ar LB1 _) CI31 Hk3 HinB SHDb0) as SHDb31.
  destruct (cv_frame L ar C HI LY HIok M8 model8 A7 LB1 _ Sp SCR XW F3b 3 (Sp - 928) _ _ _ _ _ _ CI31 Hk3 fl3b FLCb31 ltac:(unfold FS_BYTES; exact FLPb) SHDb31) as (FDEFv & FWv & FSHWv & FLCv & FLWv & _ & _).
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *. replace (F3b + 512 - 8) with (F3b + 504) in FLCv by (clear; lia).
  pose proof DENN as (DB8 & DBR & _ & DBT & _). cbn [L5.bo_fb L5.bo_st L5.bo_len] in DB8, DBR, DBT.
  pose proof (acc_kept_u8 L ar C HI LY HIok M model A LB1 Sp SCR XW XWIMG _ _ F3b 3 (Sp - 928) M8 model8 A7 _ M31 model31 _ _ A31 ACCb (sufl_refl L ar LB1 _) CI31 Hk3 HinB (F3b + 32) fdenN
                ltac:(clear; lia) ltac:(change (ff_bytes 3) with 512; clear; lia) DB8) as DB8v.
  assert (ICp : L5.img_clear M31 860160 880640) by (intros i Hi; apply IC1; clear - Hi; lia).
  pose proof (ue3p2d_conc fx31 R31 (mrestrict (ahid A31 model31) M31)
                (fun j => match j with 2%nat => Sp - 608 | 40%nat => F3b | 41%nat => fl3b | 58%nat => U R31 1 | 60%nat => fdenN | _ => 0 end)) as P. cbn beta iota in P.
  padfeed P CI31 ltac:(unfold S, SB in *; unfold numf in NUM; unfold numg in FN; clear - NUM FN DJF FLAb FLPb DBR; lia).
  destruct P as (fx32 & R32 & M32v & MG32 & _ & FZ32 & (MS32 & KS32 & R32_1 & R32_10 & R32_11 & _)).
  pose proof (L5AE3PD.div_pad_tail fx31 fx32 R31 R32 (mrestrict (ahid A31 model31) M31) M32v (Sp - 608) F3b fl3b 602408 (Z_to_bv 64 (obj - 32)) MS32 MG32) as T.
  specialize (T ltac:(intros i Hi N1 N2; apply FZ32; [exact Hi | clear - N1; lia | clear - N2; lia | clear - N2; lia])).
  specialize (T ltac:(intros j Hj; apply KS32; revert j Hj; apply L5K.incl_b; vm_compute; reflexivity) R32_1 R32_10 R32_11 ltac:(rewrite (KS32 24%nat) by inl; rk)).
  padfeed T CI31 ltac:(unfold S, SB in *; unfold numf in NUM; unfold numg in FN; clear - NUM FN DJF FLAb FLPb; lia).
  destruct T as (fx33 & R33 & M33v & MS33 & MG33 & FZ33 & FL033 & R33_10 & KS33).
  apply (cinv_retire L ar C HI LY HIok M8 model8 A7 LB1 _ Sp SCR XW F3b 3 (Sp - 928) _ M31 model31 _ _ A31 fx31 fx33 R31 602408 R33 602780 M33v
           (Wpad F3b 512 fl3b) fl3b K CI31 HS0 Hk3 FLCb31 ltac:(unfold FS_BYTES; exact FLPb)
           (fun X => FLNCb (aclient_appb L ar LB1 _ _ 0 0 fl3b X)) MS33 MG33 FZ33).
  { intros a Wa. unfold Wpad in Wa. change (ff_bytes 3 / 8) with 64. change (512 / 8) with 64 in Wa. clear - Wa. destruct Wa as [X|[X|X]]; [left; exact X | right; left; exact X | right; right; left; exact X]. }
  { intros a. apply Wpad_dec. }
  { exact FL033. }
  intros M33 model33 CI33 AH33 VIS33 FRM33.
  pose proof (pad_agree L ar C HI LY HIok M8 model8 A7 LB1 _ Sp SCR XW F3b 3 (Sp - 928) _ _ _ _ _ _ fl3b M33 CI31 Hk3 ltac:(unfold FS_BYTES; exact FLPb) FRM33) as AG.
  carry M31 M33 AG ltac:(cvis_tac [(ref, 66); (u, 144); (d3, 64); (d4, 64)]).
  clear AG FRM33 VIS33 MS33 MG33 FZ33 FL033 FDEFv FWv FSHWv FLCv FLWv SHDb31 FLCb31 HH31 ICp DB8 DBR DBT DB8v MS32 MG32 FZ32 KS32 R32_1 R32_10 R32_11.
  assert (R33_2 : getr R33 (reg 2) = Z_to_bv 64 (Sp - 960)) by (rewrite (KS33 2%nat) by in_tac; rk).
  assert (R33_3 : getr R33 (reg 3) = Z_to_bv 64 67584) by (rewrite (KS33 3%nat) by in_tac; rk).
  assert (R33_4 : getr R33 (reg 4) = Z_to_bv 64 6360328) by (rewrite (KS33 4%nat) by in_tac; rk).
  assert (R33_8 : getr R33 (reg 8) = Z_to_bv 64 (Sp - 608)) by (rewrite (KS33 8%nat) by in_tac; rk).
  clear KS33.
  pose proof (acc_weaken L ar M model A LB1 Sp SCR XW _ ((F1b, 1, Sp - 576) :: (F3a, 3, Sp - 416) :: (F1a, 1, Sp - 64) :: FF) M8 model8 A7 ACCb
                (sufl_app L ar LB1 [(F3b, 3, Sp - 928)] _)) as ACCc. clear ACCb.
  clear FLCb0 FLPb FLNCb FLAb SHDb0 HinB AL_Fb.
  tidy CI33.
  exact (L5AE3S11.e3_s11 L ar C IL HI LY ILY HIok ICok HFILL HCOPY HTLS UNWL R0 R M model K LB1 FF LK LKt cr A Sp SCR xo gd av uid rnd canary hw F1a fl1a F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d d1 d2 d3 d4 qx bo LB0 lenX w9 w10 xs fbx fd0N fn0N fnN fdenN w1 fd0 fn0 fn fden v0 v1 v2 v3 nd0 nn0 nn nd M3 errv R1 R2 A2 u obj R3 model3 R4 R5 R6 R7 A7 msg M8 R8 model8 R9 R10 R11 R12 R13 R14 A14 ref R15 R16 R17 R18 R19 R20 R21 st R22 R23 R24 R25 A25 R26 R27 M33 R28 R29 A29 R30 R31 A31 R32 fx33 R33 model33 bq ELB1 Z2 Z3 Z4 Z10 Z8 Z9 Z18 Z19 Z20 Z21 Z22 Z23 Z24 Z25 Z26 Z27 m2 m3 m4 m5 m8 DEN0Nf DEN0Nr DEN0Nt NUM0Nf NUM0Nr NUM0Nt NUM0Nc NUM0Np NUMN NUMNT DENN DENNT ZQ MWf o2 o3 o4 o5 o8 DEN0f DEN0r DEN0t NUM0f NUM0r NUM0t NUMO DENO BQ BQD BX SHd SHc SH3b SH1b SH3a SH1a FRL1a FRL3a FRL1b FRL3b FRLc FRLd LFR G1 G2 G3 G4 G9 S32 EC0 GD0 GD1 TDL MSG0 ERR ERRR CAN AUXP AV8 AVLO AVHI UIDR RNDR CANR HWR AVS HH AM HK LKI STK HSCR SCR8 SH CRF KONT A16 SLO SHI SPT HS0 ALS ALS8 SPR0 SPLO SPHI LY2 HTP FN FAL DJF ACC0 E8 E9 EX0 EX1 EX2 EX3 EX4 ACR1 CRF1 RP2 EOBJ OB16 OB8 OBR0 OBR OCEIL DJU R2_10 Hk1 FLCd0 FLPd SHDd0 FDN FDA AL_Fd EX10 EX11 EX12 EX13 EX14 EX15 EX16 EX17 ACC3 EX5 EX6 EX18 EX19 EX20 EX22 EX23 EX24 sR5 RP5 EX8 EX9 EX31 EX32 EX33 EX34 EX35 EX36 ACR2 CRF2 mR7 RP7 DJM APmu MS16 Z72 MS8 EX38 EX39 EX40 EX41 EX42 EX43 EX44 EX45 KMSG SHDd8 HMV R8_10 mR9 RP9 SHAP SHAPM E41 EX37 EX46 EX47 EX48 EX49 EX50 EX51 EX52 EX53 EX54 EX55 EX56 E10 EX7 EX29 EX30 EX61 EX62 EX63 R11_8 sR12 RP12 EX21 EX25 EX26 EX27 EX70 EX71 ACR3 mR14 RP14 DJR APru APrm RF16 EX74 EX75 EX76 EX77 EX78 EX79 EX80 EX81 EX82 EX83 EX84 HMC mR16 RP16 EX72 EX73 EX85 EX86 EX87 EX88 EX89 EX90 EX91 EX92 RP18 EX28 EX57 EX58 EX E19_10 EX64 EX65 EX66 EX67 EX68 EX69 EX93 EX94 EX95 EX99 EX102 EX103 EX104 EX105 EX107 RP21 AV8' STE EX112 EX113 EX114 EX115 EX116 EX117 EX118 EX119 EX120 EX121 EX122 EX123 EX124 EX125 EX126 EX127 EX131 EX132 EX133 EX134 EX135 EX136 EX59 FLNCd FLAd AL_E AL_F EX97 EX98 EX96 R23_19 EX101 EX106 EX128 EX100 RP25 KS26 R26_10' NUM EX108 EX109 EX110 EX111 EX129 EX130 EX137 EX138 EX139 EX140 EX141 EX142 EX143 EX144 EX60 Hk3 AL_E2 EX146 EX147 EX148 EX149 EX145 R28_24 RP29 EX151 EX152 EX153 EX150 RP31 R33_10 CI33 AUXV FRN FRQ FRU FRD FRO IC1 IC2 IC3 R33_2 R33_3 R33_4 R33_8 ACCc).
Qed.

End WithIface.
End SCFG_1.
End L5AE3S10.
