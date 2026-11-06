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
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5ParseSpecsAB0 L5OpmodSpecsAB0 L5DivSpecsAB0 L5UnwindSpecsAB0 XIcptAB0 XIcptAs0KitB0 L5BUnwK L5BUnwK2 L5BE1K L5BE2K L5BE3K L5BE2PP L5BE2Pad L5BE3P1 L5BE3P2 L5BE3P3 L5BE3P4 L5BE3P5 L5BE3P6 L5BE3P7 L5BE3P8 L5BE3P9 L5BE3P10 L5BE3P11 L5BE3PP L5BE3Pad L5BUnwK3 L5BUnwK4 L5DivInnerSpecsAB0 L5BOpdel L5BE3S15.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Set Printing Width 100000. Set Printing Depth 100000.

Module L5BE3S14.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5AUK. Import L5AUK2.
Import L5BE3P1.L5BE3P1. Import L5BE3P2.L5BE3P2. Import L5BE3P3.L5BE3P3. Import L5BE3P4.L5BE3P4. Import L5BE3P5.L5BE3P5. Import L5BE3P6.L5BE3P6. Import L5BE3P7.L5BE3P7. Import L5BE3P8.L5BE3P8. Import L5BE3P9.L5BE3P9. Import L5BE3P10.L5BE3P10. Import L5BE3P11.L5BE3P11. Import L5BE3PP.L5BE3PP. Import L5AUK3. Import L5AUK4.
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
Local Notation XW := [(6360528, 4); (6363185, 6)].
Local Notation XWIMG := (L5BE1K.xw2_img L UNWL).

Lemma e3_s14 :
  forall (R0 : bvmap 5 word) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB1 : list (Z * Z)) (FF : list fframe) (LK : list fframe) (LKt : list fframe) (cr : credit) (A : list (Z * Z)) (Sp : Z) (SCR : Z) (xo : Z) (rt8 : Z) (gd : bool) (av : Z) (uid : Z) (rnd : Z) (canary : Z) (hw : Z) (F1a : Z) (fl1a : Z) (F3a : Z) (fl3a : Z) (F1b : Z) (fl1b : Z) (F3b : Z) (fl3b : Z) (F1c : Z) (fl1c : Z) (F1d : Z) (fl1d : Z) (d1 : Z) (d2 : Z) (d3 : Z) (d4 : Z) (qx : Z) (bo : Z) (LB0 : list (Z * Z)) (lenX : nat) (w5 : Z) (w10 : Z) (xs : Z) (fbx : Z) (fd0N : Z) (fn0N : Z) (fnN : Z) (fdenN : Z) (w1 : Z) (fd0 : Z) (fn0 : Z) (fn : Z) (fden : Z) (v0 : Z) (v1 : Z) (v2 : Z) (v3 : Z) (nd0 : nat) (nn0 : nat) (nn : nat) (nd : nat) (M3 : word -> option byte) (errv : Z) (R1 : bvmap 5 word) (R2 : bvmap 5 word) (A2 : list (Z * Z)) (u : Z) (obj : Z) (R3 : bvmap 5 word) (model3 : Model) (R4 : bvmap 5 word) (R5 : bvmap 5 word) (R6 : bvmap 5 word) (R7 : bvmap 5 word) (A7 : list (Z * Z)) (msg : Z) (R8 : bvmap 5 word) (R9 : bvmap 5 word) (R10 : bvmap 5 word) (R11 : bvmap 5 word) (R12 : bvmap 5 word) (R13 : bvmap 5 word) (R14 : bvmap 5 word) (A14 : list (Z * Z)) (ref : Z) (R15 : bvmap 5 word) (R16 : bvmap 5 word) (R17 : bvmap 5 word) (R18 : bvmap 5 word) (R19 : bvmap 5 word) (R20 : bvmap 5 word) (R21 : bvmap 5 word) (st : L5USA.XS) (R22 : bvmap 5 word) (R23 : bvmap 5 word) (R24 : bvmap 5 word) (R25 : bvmap 5 word) (A25 : list (Z * Z)) (R26 : bvmap 5 word) (R27 : bvmap 5 word) (R28 : bvmap 5 word) (R29 : bvmap 5 word) (A29 : list (Z * Z)) (R30 : bvmap 5 word) (R31 : bvmap 5 word) (A31 : list (Z * Z)) (R32 : bvmap 5 word) (R33 : bvmap 5 word) (R34 : bvmap 5 word) (R35 : bvmap 5 word) (R36 : bvmap 5 word) (R37 : bvmap 5 word) (R38 : bvmap 5 word) (M42 : word -> option byte) (R39 : bvmap 5 word) (R40 : bvmap 5 word) (R41 : bvmap 5 word) (A41 : list (Z * Z)) (fx42 : FPState) (R42 : bvmap 5 word) (model42 : Model),
    forall (bq : L5.bigobj),
    forall (ELB1 : LB1 = (qx, 64) :: LB0),
    forall (Z2 : getr R (reg 2) = Z_to_bv 64 (Sp - 1296)),
    forall (Z3 : getr R (reg 3) = Z_to_bv 64 67584),
    forall (Z4 : getr R (reg 4) = Z_to_bv 64 6363400),
    forall (Z10 : getr R 10 = Z_to_bv 64 16),
    forall (Z8 : getr R (reg 8) = Z_to_bv 64 (Sp - 1168)),
    forall (Z9 : getr R (reg 9) = Z_to_bv 64 (Sp - 1296)),
    forall (Z18 : getr R 18 = Z_to_bv 64 F1d),
    forall (Z19 : getr R 19 = Z_to_bv 64 xo),
    forall (Z20 : getr R 20 = Z_to_bv 64 (F1d + 32)),
    forall (Z21 : getr R 21 = Z_to_bv 64 (xo + 8)),
    forall (Z22 : getr R 22 = Z_to_bv 64 (F1c / 8 + 2147450880)),
    forall (Z23 : getr R 23 = Z_to_bv 64 (F1d / 8 + 2147450880)),
    forall (Z24 : getr R 24 = Z_to_bv 64 F1d),
    forall (Z25 : getr R 25 = Z_to_bv 64 SB),
    forall (Z26 : getr R 26 = Z_to_bv 64 ((xo + 8) / 8 + 2147450880)),
    forall (Z27 : getr R 27 = Z_to_bv 64 F3b),
    forall (DEN0Nr : 0 <= fd0N < 256),
    forall (DEN0Nt : Z.testbit fd0N 0 = false),
    forall (NUM0Nr : 0 <= fn0N < 256),
    forall (NUM0Nt : Z.testbit fn0N 0 = true),
    forall (NUMN : L5.big_at RSEGS M (F3b + 96) {| L5.bo_fb := fnN; L5.bo_len := 0; L5.bo_st := L5.BDyn 8 d2 |}),
    forall (NUMNT : Z.testbit fnN 1 = false),
    forall (DENN : L5.big_at RSEGS M (F3b + 32) {| L5.bo_fb := fdenN; L5.bo_len := 1; L5.bo_st := L5.BInl L5DSA.MWORD w1 |}),
    forall (DENNT : Z.testbit fdenN 1 = false),
    forall (ZQ : L5DIA.zero_obj M (F1b + 32)),
    forall (o2 : L5.u64_at RSEGS M42 (Sp - 472) F3a),
    forall (o3 : L5.u64_at RSEGS M42 (Sp - 448) F3a),
    forall (o4 : L5.u64_at RSEGS M42 (Sp - 392) (F3a + 96)),
    forall (o5 : L5.u64_at RSEGS M42 (Sp - 416) (F3a + 32)),
    forall (DEN0f : L5.u8_at RSEGS M42 (Sp - 328) fd0),
    forall (DEN0r : 0 <= fd0 < 256),
    forall (DEN0t : Z.testbit fd0 0 = false),
    forall (NUM0f : L5.u8_at RSEGS M42 (Sp - 296) fn0),
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
    forall (FRL1a : L5DSA.fr_live L ar ([(d1, 64); (d2, 64); (d3, 64); (d4, 64)] ++ LB1) FF M 1 F1a fl1a (Sp - 80)),
    forall (FRL3a : L5DSA.fr_live L ar ([(d1, 64); (d2, 64); (d3, 64); (d4, 64)] ++ LB1) ((F1a, 1, Sp - 80) :: FF) M 3 F3a fl3a (Sp - 464)),
    forall (FRL1b : L5DSA.fr_live L ar ([(d1, 64); (d2, 64); (d3, 64); (d4, 64)] ++ LB1) ((F3a, 3, Sp - 464) :: (F1a, 1, Sp - 80) :: FF) M 1 F1b fl1b (Sp - 624)),
    forall (FRL3b : L5DSA.fr_live L ar ([(d1, 64); (d2, 64); (d3, 64); (d4, 64)] ++ LB1) ((F1b, 1, Sp - 624) :: (F3a, 3, Sp - 464) :: (F1a, 1, Sp - 80) :: FF) M 3 F3b fl3b (Sp - 1008)),
    forall (FRLc : L5DSA.fr_live L ar ([(d1, 64); (d2, 64); (d3, 64); (d4, 64)] ++ LB1) ((F3b, 3, Sp - 1008) :: (F1b, 1, Sp - 624) :: (F3a, 3, Sp - 464) :: (F1a, 1, Sp - 80) :: FF) M 1 F1c fl1c (Sp - 1136)),
    forall (FRLd : L5DSA.fr_live L ar ([(d1, 64); (d2, 64); (d3, 64); (d4, 64)] ++ LB1) ((F1c, 1, Sp - 1136) :: (F3b, 3, Sp - 1008) :: (F1b, 1, Sp - 624) :: (F3a, 3, Sp - 464) :: (F1a, 1, Sp - 80) :: FF) M 1 F1d fl1d (Sp - 1264)),
    forall (LFR : length [(F1a, fl1a); (F3a, fl3a); (F1b, fl1b); (F3b, fl3b); (F1c, fl1c); (F1d, fl1d)] = 6%nat),
    forall (G1 : getr R0 1 = Z_to_bv 64 584500),
    forall (G2 : getr R0 2 = Z_to_bv 64 Sp),
    forall (G3 : getr R0 3 = Z_to_bv 64 67584),
    forall (G4 : getr R0 4 = Z_to_bv 64 6363400),
    forall (G9 : getr R0 9 = Z_to_bv 64 (Sp + 16)),
    forall (S32 : Sp mod 32 = 16),
    forall (RT8 : L5.u64_at RSEGS M42 Sp (nz rt8)),
    forall (RTRA : L5.u64_at RSEGS M42 (Sp + 8) 582404),
    forall (EC0 : L5.u64_at RSEGS M42 6360520 0),
    forall (GD0 : L5.u8_at RSEGS M42 6361072 (if gd then 1 else 0)),
    forall (GD1 : L5.u8_at RSEGS M42 6361073 (if gd then 1 else 0)),
    forall (TDL : L5.u64_at RSEGS M42 6363352 6495184),
    forall (MSG0 : L5.u64_at RSEGS M42 6495224 0),
    forall (ERR : L5.u32_at RSEGS M42 6363236 errv),
    forall (ERRR : 0 <= errv < 2 ^ 64),
    forall (CAN : L5.u64_at RSEGS M42 6494536 canary),
    forall (AUXP : L5.u64_at RSEGS M42 6495136 av),
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
    forall (KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LK' : list fframe) (A' : list (Z * Z)), L5OMA.landed_regs R0 R' Sp rt8 -> L5USA.e3_landed L st LB1 FF LK cr (Sp + 16) M' R' LB' cr' LK' -> ahpres L ar LB1 FF Sp SCR L5USA.xs_foot M M' -> model_rt model model' -> incl A A' -> amodel_ok A' model' -> ri_inv HI LB' FF LK' cr' A' M' (vml_of model') -> srealizes RSEGS SCFG (cfg (fx:=fx') R' 583040 M' model') K),
    forall (A16 : Sp mod 16 = 0),
    forall (SLO : ahl_ceil ar + 4096 + SCR <= Sp),
    forall (SHI : Sp <= ar_sptop ar),
    forall (SPT : 140735340871680 <= ar_sptop ar <= 2 ^ 47),
    forall (AVT : Sp + 16 <= av),
    forall (HS0 : 0 <= SCR),
    forall (ALS : (Sp - 1296) mod 16 = 0),
    forall (ALS8 : (Sp - 1296) mod 8 = 0),
    forall (SPR0 : 0 <= Sp - 1296 < 2 ^ 64),
    forall (SPLO : 140735332552704 <= Sp - 1296),
    forall (SPHI : Sp - 1296 <= 140737488355264),
    forall (LY2 : as0_layout2 L),
    forall (HTP : hl_tp L = 6363400),
    forall (FN : numg (6504448 <= ar_fs ar /\ ar_fs ar + 11571200 <= ahl_ceil ar /\ ar_fs ar <= F1d /\ F1d + 128 <= ar_fs ar + 11571200 /\ ar_fs ar <= F1c /\ F1c + 128 <= ar_fs ar + 11571200 /\ ar_fs ar <= F3b /\ F3b + 512 <= ar_fs ar + 11571200 /\ ar_fs ar <= F1b /\ F1b + 128 <= ar_fs ar + 11571200 /\ ar_fs ar <= F3a /\ F3a + 512 <= ar_fs ar + 11571200 /\ ar_fs ar <= F1a /\ F1a + 128 <= ar_fs ar + 11571200 /\ 0 <= F1d / 8 <= 2 ^ 44 /\ 0 <= F1c / 8 <= 2 ^ 44 /\ 0 <= F3b / 8 <= 2 ^ 44 /\ 0 <= F1b / 8 <= 2 ^ 44 /\ 0 <= F3a / 8 <= 2 ^ 44 /\ 0 <= F1a / 8 <= 2 ^ 44)),
    forall (FAL : F1d mod 128 = 0 /\ F1c mod 128 = 0 /\ F3b mod 512 = 0 /\ F1b mod 128 = 0 /\ F3a mod 512 = 0 /\ F1a mod 128 = 0),
    forall (DJF : ar_fs ar + 11571200 <= 2147446784 \/ 2147446784 + 17592186048512 <= ar_fs ar),
    forall (ACC0 : acc L ar M model A LB1 Sp SCR XW ((F1c, 1, Sp - 1136) :: (F3b, 3, Sp - 1008) :: (F1b, 1, Sp - 624) :: (F3a, 3, Sp - 464) :: (F1a, 1, Sp - 80) :: FF) M model A),
    forall (E8 : bv_unsigned (getr R (reg 8)) = Sp - 1296 + 128),
    forall (E9 : bv_unsigned (getr R (reg 9)) = Sp - 1296),
    forall (EX0 : forall x : nat, In x KS_ue3a1 -> getr R1 (reg x) = getr R (reg x)),
    forall (EX1 : getr R1 (reg 1) = Z_to_bv 64 727044),
    forall (EX2 : getr R1 (reg 2) = Z_to_bv 64 (Sp - 1296 - 48)),
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
    forall (EX11 : getr R3 (reg 1) = Z_to_bv 64 591860),
    forall (EX12 : getr R3 (reg 2) = Z_to_bv 64 (Sp - 1296)),
    forall (EX13 : getr R3 (reg 8) = Z_to_bv 64 (Sp - 1296 + 128)),
    forall (EX14 : getr R3 (reg 9) = Z_to_bv 64 (Sp - 1296)),
    forall (EX15 : getr R3 (reg 10) = Z_to_bv 64 (F1d + 32)),
    forall (EX16 : getr R3 (reg 11) = Z_to_bv 64 142240),
    forall (EX17 : getr R3 (reg 21) = Z_to_bv 64 obj),
    forall (ACC3 : acc L ar M model A LB1 Sp SCR XW ((F1c, 1, Sp - 1136) :: (F3b, 3, Sp - 1008) :: (F1b, 1, Sp - 624) :: (F3a, 3, Sp - 464) :: (F1a, 1, Sp - 80) :: FF) M3 model3 A2),
    forall (EX5 : forall x : nat, In x KS_ue3s1 -> getr R4 (reg x) = getr R3 (reg x)),
    forall (EX6 : getr R4 (reg 1) = Z_to_bv 64 590756),
    forall (EX18 : getr R4 (reg 2) = Z_to_bv 64 (Sp - 1296 - 64)),
    forall (EX19 : getr R4 (reg 8) = Z_to_bv 64 142240),
    forall (EX20 : getr R4 (reg 10) = Z_to_bv 64 142240),
    forall (EX22 : getr R4 (reg 11) = Z_to_bv 64 911160),
    forall (EX23 : getr R4 (reg 18) = Z_to_bv 64 (F1d + 32)),
    forall (EX24 : getr R4 (reg 21) = Z_to_bv 64 2147450880),
    forall (sR5 : getr R5 (reg 10) = Z_to_bv 64 41),
    forall (RP5 : regs_preserved R4 R5),
    forall (EX8 : forall x : nat, In x KS_ue3s2_bh -> getr R6 (reg x) = getr R5 (reg x)),
    forall (EX9 : getr R6 (reg 1) = Z_to_bv 64 859152),
    forall (EX31 : getr R6 (reg 2) = Z_to_bv 64 (Sp - 1296 - 80)),
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
    forall (Z72 : L5KA.zeros_at M42 (obj - 72) 4),
    forall (MS8 : msg mod 8 = 0),
    forall (EX38 : forall x : nat, In x KS_ue3s3 -> getr R8 (reg x) = getr R7 (reg x)),
    forall (EX39 : getr R8 (reg 1) = Z_to_bv 64 590936),
    forall (EX40 : getr R8 (reg 2) = Z_to_bv 64 (Sp - 1296 - 64)),
    forall (EX41 : getr R8 (reg 8) = Z_to_bv 64 142240),
    forall (EX42 : getr R8 (reg 11) = Z_to_bv 64 142240),
    forall (EX43 : getr R8 (reg 12) = Z_to_bv 64 41),
    forall (EX44 : getr R8 (reg 19) = Z_to_bv 64 msg),
    forall (EX45 : getr R8 (reg 20) = Z_to_bv 64 49),
    forall (HMV : amemcpy_spec_at L ar SCFG HI 387632 false),
    forall (R8_10 : getr R8 (reg 10) = Z_to_bv 64 msg),
    forall (mR9 : getr R9 (reg 10) = Z_to_bv 64 msg),
    forall (RP9 : regs_preserved R8 R9),
    forall (SHAP : obj / 8 + 2147450864 + 18 <= F1d / 8 + 2147450880 \/ F1d / 8 + 2147450880 + 16 <= obj / 8 + 2147450864),
    forall (SHAPM : msg / 8 + 2147450880 + 6 <= F1d / 8 + 2147450880 \/ F1d / 8 + 2147450880 + 16 <= msg / 8 + 2147450880),
    forall (E41 : (msg + 41) / 8 = msg / 8 + 5),
    forall (EX37 : forall x : nat, In x KS_ue3s4 -> getr R10 (reg x) = getr R9 (reg x)),
    forall (EX46 : getr R10 (reg 1) = Z_to_bv 64 591916),
    forall (EX47 : getr R10 (reg 2) = Z_to_bv 64 (Sp - 1296 - 32)),
    forall (EX48 : getr R10 (reg 8) = Z_to_bv 64 obj),
    forall (EX49 : getr R10 (reg 9) = Z_to_bv 64 2147450880),
    forall (EX50 : getr R10 (reg 10) = Z_to_bv 64 obj),
    forall (EX51 : getr R10 (reg 11) = Z_to_bv 64 (F1d + 32)),
    forall (EX52 : getr R10 (reg 12) = Z_to_bv 64 911160),
    forall (EX53 : getr R10 (reg 18) = Z_to_bv 64 F1d),
    forall (EX54 : getr R10 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R3 (reg 19)))),
    forall (EX55 : getr R10 (reg 20) = Z_to_bv 64 (F1d + 32)),
    forall (EX56 : getr R10 (reg 21) = Z_to_bv 64 obj),
    forall (E10 : bv_unsigned (getr R10 (reg 10)) = obj),
    forall (EX7 : forall x : nat, In x KS_ue3c1 -> getr R11 (reg x) = getr R10 (reg x)),
    forall (EX29 : getr R11 (reg 1) = Z_to_bv 64 731448),
    forall (EX30 : getr R11 (reg 2) = Z_to_bv 64 (Sp - 1296 - 80)),
    forall (EX61 : getr R11 (reg 8) = getr R10 (reg 10)),
    forall (EX62 : getr R11 (reg 9) = Z_to_bv 64 msg),
    forall (EX63 : getr R11 (reg 10) = Z_to_bv 64 msg),
    forall (R11_8 : getr R11 (reg 8) = Z_to_bv 64 obj),
    forall (sR12 : getr R12 (reg 10) = Z_to_bv 64 41),
    forall (RP12 : regs_preserved R11 R12),
    forall (EX21 : forall x : nat, In x KS_ue3c2 -> getr R13 (reg x) = getr R12 (reg x)),
    forall (EX25 : getr R13 (reg 1) = Z_to_bv 64 859152),
    forall (EX26 : getr R13 (reg 2) = Z_to_bv 64 (Sp - 1296 - 96)),
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
    forall (EX75 : getr R15 (reg 1) = Z_to_bv 64 731492),
    forall (EX76 : getr R15 (reg 2) = Z_to_bv 64 (Sp - 1296 - 80)),
    forall (EX77 : getr R15 (reg 8) = Z_to_bv 64 obj),
    forall (EX78 : getr R15 (reg 10) = Z_to_bv 64 (ref + 24)),
    forall (EX79 : getr R15 (reg 11) = Z_to_bv 64 msg),
    forall (EX80 : getr R15 (reg 12) = Z_to_bv 64 42),
    forall (EX81 : getr R15 (reg 19) = Z_to_bv 64 (ref + 24)),
    forall (EX82 : L5.u32_at RSEGS M42 (ref + 16) 0),
    forall (EX83 : L5.u64_at RSEGS M42 (ref + 8) 41),
    forall (EX84 : L5.u64_at RSEGS M42 ref 41),
    forall (HMC : amemcpy_spec_at L ar SCFG HI 385872 false),
    forall (mR16 : getr R16 (reg 10) = Z_to_bv 64 (ref + 24)),
    forall (RP16 : regs_preserved R15 R16),
    forall (EX72 : forall x : nat, In x KS_ue3c4 -> getr R17 (reg x) = getr R16 (reg x)),
    forall (EX73 : getr R17 (reg 1) = Z_to_bv 64 591920),
    forall (EX85 : getr R17 (reg 2) = Z_to_bv 64 (Sp - 1296)),
    forall (EX86 : getr R17 (reg 8) = Z_to_bv 64 (Sp - 1296 + 128)),
    forall (EX87 : getr R17 (reg 9) = Z_to_bv 64 (Sp - 1296)),
    forall (EX88 : getr R17 (reg 10) = Z_to_bv 64 864592),
    forall (EX89 : getr R17 (reg 18) = Z_to_bv 64 F1d),
    forall (EX90 : getr R17 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R3 (reg 19)))),
    forall (EX91 : L5.u64_at RSEGS M42 obj 864592),
    forall (EX92 : L5.u64_at RSEGS M42 (obj + 8) (ref + 24)),
    forall (RP18 : regs_preserved R17 R18),
    forall (EX28 : forall x : nat, In x KS_ue3c5 -> getr R19 (reg x) = getr R18 (reg x)),
    forall (EX57 : getr R19 (reg 10) = Z_to_bv 64 obj),
    forall (EX58 : getr R19 (reg 11) = Z_to_bv 64 864552),
    forall (EX : getr R19 (reg 12) = Z_to_bv 64 721816),
    forall (E19_10 : bv_unsigned (getr R19 (reg 10)) = obj),
    forall (EX64 : forall x : nat, In x KS_ue3t1 -> getr R20 (reg x) = getr R19 (reg x)),
    forall (EX65 : getr R20 (reg 1) = Z_to_bv 64 343964),
    forall (EX66 : getr R20 (reg 2) = Z_to_bv 64 (Sp - 1296 - 64)),
    forall (EX67 : getr R20 (reg 8) = Z_to_bv 64 (obj - 32)),
    forall (EX68 : getr R20 (reg 9) = Z_to_bv 64 884616),
    forall (EX69 : getr R20 (reg 10) = Z_to_bv 64 (obj - 32)),
    forall (EX93 : getr R20 (reg 11) = Z_to_bv 64 746772),
    forall (EX94 : getr R20 (reg 12) = Z_to_bv 64 725624),
    forall (EX95 : getr R20 (reg 18) = getr R19 (reg 10)),
    forall (EX99 : L5.u64_at RSEGS M42 (obj - 120) 1),
    forall (EX102 : L5.u64_at RSEGS M42 (obj - 88) 610700),
    forall (EX103 : L5.u64_at RSEGS M42 (obj - 104) 721816),
    forall (EX104 : L5.u64_at RSEGS M42 (obj - 112) 864552),
    forall (EX105 : L5.u64_at RSEGS M42 (obj - 96) 610968),
    forall (EX107 : L5.u32_at RSEGS M42 6360528 1),
    forall (RP21 : regs_preserved R20 R21),
    forall (AV8' : av mod 8 = 0),
    forall (STE : L5USA.xs_gd st = gd /\ L5USA.xs_av st = av /\ L5USA.xs_uid st = uid /\ L5USA.xs_rnd st = rnd /\ L5USA.xs_canary st = canary /\ L5USA.xs_hw st = hw),
    forall (EX112 : forall x : nat, In x KS_ue3t2_v0 -> getr R22 (reg x) = getr R21 (reg x)),
    forall (EX113 : getr R22 (reg 1) = Z_to_bv 64 591996),
    forall (EX114 : getr R22 (reg 2) = Z_to_bv 64 (Sp - 1296)),
    forall (EX115 : getr R22 (reg 6) = Z_to_bv 64 746772),
    forall (EX116 : getr R22 (reg 8) = Z_to_bv 64 (Sp - 1296 + 128)),
    forall (EX117 : getr R22 (reg 9) = Z_to_bv 64 (Sp - 1296)),
    forall (EX118 : getr R22 (reg 10) = Z_to_bv 64 (obj - 32)),
    forall (EX119 : getr R22 (reg 11) = Z_to_bv 64 0),
    forall (EX120 : getr R22 (reg 18) = Z_to_bv 64 F1d),
    forall (EX121 : L5.u64_at RSEGS M42 (obj - 8) (Sp - 1296 + 1312)),
    forall (EX122 : L5.u64_at RSEGS M42 (obj - 40) obj),
    forall (EX123 : L5.u64_at RSEGS M42 (obj - 48) 583040),
    forall (EX124 : L5.u64_at RSEGS M42 (obj - 56) 157360),
    forall (EX125 : L5.u64_at RSEGS M42 (obj - 64) 157499),
    forall (EX126 : L5.u32_at RSEGS M42 (obj - 68) 1),
    forall (EX127 : L5.u8_at RSEGS M42 6363188 0),
    forall (EX128 : L5.u8_at RSEGS M42 6363187 1),
    forall (EX129 : L5.u8_at RSEGS M42 6363190 0),
    forall (EX130 : L5.u8_at RSEGS M42 6363189 1),
    forall (EX131 : L5.u64_at RSEGS M42 (obj - 16) 0),
    forall (EX132 : L5.u8_at RSEGS M42 6363186 0),
    forall (EX133 : L5.u8_at RSEGS M42 6363185 1),
    forall (EX59 : L5.u64_at RSEGS M42 (obj - 32) 4849336966747728640),
    forall (FLNCd : ~ aclient L ar ([(d1, 64); (d2, 64); (d3, 64); (d4, 64)] ++ LB1) ((F1d, 1, Sp - 1264) :: (F1c, 1, Sp - 1136) :: (F3b, 3, Sp - 1008) :: (F1b, 1, Sp - 624) :: (F3a, 3, Sp - 464) :: (F1a, 1, Sp - 80) :: FF) 0 0 fl1d),
    forall (FLAd : F1d + 128 <= fl1d \/ fl1d + 1 <= F1d),
    forall (AL_E : aligned (Sp - 1296) 32),
    forall (AL_F : aligned F1d 32),
    forall (EX97 : forall x : nat, In x KS_ue3p1a -> getr R23 (reg x) = getr R22 (reg x)),
    forall (EX98 : getr R23 (reg 11) = Z_to_bv 64 1),
    forall (EX96 : getr R23 (reg 19) = getr R22 (reg 10)),
    forall (R23_19 : getr R23 (reg 19) = Z_to_bv 64 (obj - 32)),
    forall (EX101 : forall x : nat, In x KS_ue3p1b -> getr R24 (reg x) = getr R23 (reg x)),
    forall (EX106 : getr R24 (reg 1) = Z_to_bv 64 592028),
    forall (EX134 : getr R24 (reg 10) = Z_to_bv 64 msg),
    forall (EX100 : getr R24 (reg 11) = Z_to_bv 64 48),
    forall (RP25 : regs_preserved R24 R25),
    forall (KS26 : forall x : nat, In x KS_ue3p1c -> getr R26 (reg x) = getr R25 (reg x)),
    forall (R26_10' : getr R26 (reg 10) = Z_to_bv 64 (obj - 32)),
    forall (EX108 : forall x : nat, In x KS_ue3r1 -> getr R27 (reg x) = getr R26 (reg x)),
    forall (EX109 : getr R27 (reg 1) = Z_to_bv 64 605108),
    forall (EX110 : getr R27 (reg 2) = Z_to_bv 64 (Sp - 1296 + 256)),
    forall (EX111 : getr R27 (reg 8) = Z_to_bv 64 (Sp - 1296 + 640)),
    forall (EX135 : getr R27 (reg 9) = Z_to_bv 64 (Sp - 1296 + 256)),
    forall (EX136 : getr R27 (reg 11) = Z_to_bv 64 0),
    forall (EX137 : getr R27 (reg 18) = Z_to_bv 64 (S F3b)),
    forall (EX138 : getr R27 (reg 19) = Z_to_bv 64 (F3b + 32)),
    forall (EX139 : getr R27 (reg 20) = Z_to_bv 64 0),
    forall (EX140 : getr R27 (reg 21) = Z_to_bv 64 (nz xo)),
    forall (EX141 : getr R27 (reg 22) = Z_to_bv 64 F3b),
    forall (EX142 : getr R27 (reg 23) = Z_to_bv 64 SB),
    forall (EX143 : getr R27 (reg 24) = Z_to_bv 64 0),
    forall (EX144 : getr R27 (reg 25) = Z_to_bv 64 (F3b + 96)),
    forall (EX60 : getr R27 (reg 26) = Z_to_bv 64 (nz (xo + 8))),
    forall (Hk3 : In 3 [1; 2; 3]),
    forall (AL_E2 : aligned (Sp - 656) 32),
    forall (EX146 : forall x : nat, In x KS_ue3p2a -> getr R28 (reg x) = getr R27 (reg x)),
    forall (EX147 : getr R28 (reg 1) = Z_to_bv 64 605176),
    forall (EX148 : getr R28 (reg 10) = Z_to_bv 64 d1),
    forall (EX149 : getr R28 (reg 11) = Z_to_bv 64 64),
    forall (EX145 : getr R28 (reg 22) = getr R27 (reg 10)),
    forall (R28_24 : getr R28 (reg 22) = Z_to_bv 64 (obj - 32)),
    forall (RP29 : regs_preserved R28 R29),
    forall (EX151 : forall x : nat, In x KS_ue3p2c -> getr R30 (reg x) = getr R29 (reg x)),
    forall (EX152 : getr R30 (reg 1) = Z_to_bv 64 605220),
    forall (EX153 : getr R30 (reg 10) = Z_to_bv 64 d2),
    forall (EX150 : getr R30 (reg 11) = Z_to_bv 64 64),
    forall (RP31 : regs_preserved R30 R31),
    forall (R33_10 : getr R33 (reg 10) = Z_to_bv 64 (obj - 32)),
    forall (R33_2 : getr R33 (reg 2) = Z_to_bv 64 (Sp - 1040)),
    forall (R33_3 : getr R33 (reg 3) = Z_to_bv 64 67584),
    forall (R33_4 : getr R33 (reg 4) = Z_to_bv 64 6363400),
    forall (R33_8 : getr R33 (reg 8) = Z_to_bv 64 (Sp - 656)),
    forall (EX155 : forall x : nat, In x KS_ue3r2 -> getr R34 (reg x) = getr R33 (reg x)),
    forall (EX156 : getr R34 (reg 1) = Z_to_bv 64 609580),
    forall (EX157 : getr R34 (reg 2) = Z_to_bv 64 (Sp - 1296 + 640)),
    forall (EX158 : getr R34 (reg 8) = Z_to_bv 64 (Sp - 1296 + 736)),
    forall (EX159 : getr R34 (reg 9) = Z_to_bv 64 (Sp - 1296 + 640)),
    forall (EX160 : getr R34 (reg 11) = Z_to_bv 64 0),
    forall (EX161 : getr R34 (reg 18) = Z_to_bv 64 F1b),
    forall (EX162 : getr R34 (reg 19) = Z_to_bv 64 (nz xo)),
    forall (EX163 : getr R34 (reg 20) = Z_to_bv 64 (Sp - 1296 + 744)),
    forall (EX164 : getr R34 (reg 21) = Z_to_bv 64 (F1b + 32)),
    forall (EX165 : getr R34 (reg 22) = Z_to_bv 64 (S F1b)),
    forall (EX166 : getr R34 (reg 23) = Z_to_bv 64 F1b),
    forall (EX167 : getr R34 (reg 24) = Z_to_bv 64 L5DSA.RETIRE_MAGIC),
    forall (EX168 : getr R34 (reg 25) = Z_to_bv 64 (F3a + 96)),
    forall (EX169 : getr R34 (reg 26) = Z_to_bv 64 (nz w10)),
    forall (EX154 : getr R34 (reg 27) = Z_to_bv 64 F3a),
    forall (KS35 : forall x : nat, In x KS_ue3p3 -> getr R35 (reg x) = getr R34 (reg x)),
    forall (R35_19 : getr R35 (reg 19) = getr R34 (reg 10)),
    forall (EX171 : forall x : nat, In x KS_ue3r3 -> getr R36 (reg x) = getr R35 (reg x)),
    forall (EX172 : getr R36 (reg 1) = Z_to_bv 64 607380),
    forall (EX173 : getr R36 (reg 2) = Z_to_bv 64 (Sp - 1296 + 736)),
    forall (EX174 : getr R36 (reg 8) = Z_to_bv 64 (nz xo)),
    forall (EX175 : getr R36 (reg 9) = Z_to_bv 64 (nz xs)),
    forall (EX176 : getr R36 (reg 11) = Z_to_bv 64 0),
    forall (EX177 : getr R36 (reg 18) = Z_to_bv 64 (S F3a)),
    forall (EX178 : getr R36 (reg 19) = Z_to_bv 64 (nz xo)),
    forall (EX179 : getr R36 (reg 20) = Z_to_bv 64 (F1a + 32)),
    forall (EX180 : getr R36 (reg 21) = Z_to_bv 64 (nz w5)),
    forall (EX181 : getr R36 (reg 22) = Z_to_bv 64 F3a),
    forall (EX182 : getr R36 (reg 23) = Z_to_bv 64 SB),
    forall (EX170 : getr R36 (reg 24) = Z_to_bv 64 (F3a + 32)),
    forall (EX184 : forall x : nat, In x KS_ue3p4 -> getr R37 (reg x) = getr R36 (reg x)),
    forall (EX185 : getr R37 (reg 8) = getr R36 (reg 10)),
    forall (EX183 : getr R37 (reg 11) = Z_to_bv 64 0),
    forall (NUM : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR) /\ (0 <= Sp - 1296 < 2 ^ 64 /\ 140735332552704 <= Sp - 1296 <= 140737488355264) /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47 /\ Sp + 16 <= av) /\ (obj = u + 128 /\ 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 16 <= ahl_ceil ar) /\ (17594333495296 <= msg /\ msg + 48 <= ahl_ceil ar) /\ 17594333495296 <= ref /\ ref + 66 <= ahl_ceil ar)),
    forall (EX187 : forall x : nat, In x KS_ue3r4 -> getr R38 (reg x) = getr R37 (reg x)),
    forall (EX188 : getr R38 (reg 1) = Z_to_bv 64 605104),
    forall (EX189 : getr R38 (reg 2) = Z_to_bv 64 (Sp - 1296 + 800)),
    forall (EX190 : getr R38 (reg 8) = Z_to_bv 64 (Sp - 1296 + 1184)),
    forall (EX191 : getr R38 (reg 9) = Z_to_bv 64 (Sp - 1296 + 800)),
    forall (EX186 : getr R38 (reg 11) = Z_to_bv 64 0),
    forall (HinD : In (F3a, 3, Sp - 464) ((F3a, 3, Sp - 464) :: (F1a, 1, Sp - 80) :: FF)),
    forall (FLCa0 : cell_is RSEGS M (F3a + 512 - 8) 8 fl3a),
    forall (FLPa : ar_fs ar <= fl3a < ar_fs ar + 11571200),
    forall (FLNCa : ~ aclient L ar ([(d1, 64); (d2, 64); (d3, 64); (d4, 64)] ++ LB1) ((F3a, 3, Sp - 464) :: (F1a, 1, Sp - 80) :: FF) 0 0 fl3a),
    forall (FLAa : F3a + 512 <= fl3a \/ fl3a + 1 <= F3a),
    forall (SHDa0 : L5.defined M (F3a / 8 + SB) 64),
    forall (InD3 : In (d3, 64) ([(ref, 66); (u, 144); (d3, 64); (d4, 64)] ++ LB1)),
    forall (InD4 : In (d4, 64) ([(ref, 66); (u, 144); (d3, 64); (d4, 64)] ++ LB1)),
    forall (DN : numg (4096 <= d3 /\ d3 + 64 <= 2 ^ 47 /\ 4096 <= d4 /\ d4 + 64 <= 2 ^ 47)),
    forall (NE3 : (ref =? d4) = false),
    forall (NE4 : (u =? d4) = false),
    forall (AL_E5 : aligned (Sp - 112) 32),
    forall (AL_Fa : aligned F3a 32),
    forall (EX193 : forall x : nat, In x KS_ue3p5a -> getr R39 (reg x) = getr R38 (reg x)),
    forall (EX194 : getr R39 (reg 10) = Z_to_bv 64 0),
    forall (EX192 : getr R39 (reg 22) = getr R38 (reg 10)),
    forall (R39_24 : getr R39 (reg 22) = Z_to_bv 64 (obj - 32)),
    forall (EX196 : forall x : nat, In x KS_ue3p2c -> getr R40 (reg x) = getr R39 (reg x)),
    forall (EX197 : getr R40 (reg 1) = Z_to_bv 64 605220),
    forall (EX198 : getr R40 (reg 10) = Z_to_bv 64 d3),
    forall (EX195 : getr R40 (reg 11) = Z_to_bv 64 64),
    forall (RP41 : regs_preserved R40 R41),
    forall (EX199 : forall x : nat, In x KS_ue3p5d -> getr R42 (reg x) = getr R41 (reg x)),
    forall (EX200 : getr R42 (reg 1) = Z_to_bv 64 605300),
    forall (EX201 : getr R42 (reg 10) = Z_to_bv 64 d4),
    forall (EX202 : getr R42 (reg 11) = Z_to_bv 64 64),
    forall (ACC42 : acc L ar M model A LB1 Sp SCR XW ((F1a, 1, Sp - 80) :: FF) M42 model42 A41),
    forall (CI42 : cinv L ar HI M42 model42 A41 LB1 ((F3a, 3, Sp - 464) :: (F1a, 1, Sp - 80) :: FF) Sp SCR XW [(ref, 66); (u, 144); (d4, 64)] M42 model42 ((F1c, 1, Sp - 1136) :: LKt) (adebit L (adebit L (adebit L cr 144) 48) 66) A41),
    forall (AUXV : forall j : nat, (j < 20)%nat -> L5.u64_at RSEGS M42 (av + 8 * Z.of_nat j) (nth j (L5USA.auxv20A uid rnd hw) 0)),
    forall (FRD : forall j : nat, (j < 13)%nat -> L5.u64_at RSEGS M42 (Sp - 216 + 8 * Z.of_nat j) (nth j [L5DSA.U R0 27; L5DSA.U R0 26; L5DSA.U R0 25; L5DSA.RETIRE_MAGIC; F1a; F1a / 8 + SB; F1a + 32; nz bo; nz xo; F1a; Sp - 112; Sp; L5DSA.DIV_RET_O] 0)),
    forall (FRO : forall j : nat, (j < 10)%nat -> L5.u64_at RSEGS M42 (Sp - 80 + 8 * Z.of_nat j) (nth j [L5DSA.U R0 24; L5DSA.U R0 23; L5DSA.U R0 22; L5DSA.U R0 21; L5DSA.U R0 20; L5DSA.U R0 19; L5DSA.U R0 18; Sp + 16; L5DSA.U R0 8; 584500] 0)),
    forall (IC1 : L5.img_clear M42 65536 884736),
    forall (IC2 : L5.img_clear M42 895824 895856),
    forall (IC3 : L5.img_clear M42 895872 (895872 + 8)),
    forall (SHDa42 : L5.defined M42 (F3a / 8 + SB) 64),
  srealizes RSEGS SCFG (cfg (fx:=fx42) R42 725064 M42 model42) K.
Proof.
  intros.
  (* [comment removed for export] *)
  pose proof (cinv_num L ar HI M42 model42 A41 LB1 _ Sp SCR XW _ _ _ _ _ _ CI42) as (_ & SLO42 & SHI42 & SPT42).
  apply (cinv_opdel L ar C HI HIok M42 model42 A41 LB1 _ Sp SCR XW _ M42 model42 _ _ A41 fx42 R42 d4 64 (Sp - 496) 605300 K (L5ADEL.opdel_sized_ok L ar C HI LY HIok) CI42 HK HS0);
    [ right; right; left; reflexivity | rk | rk | split; [clear; lia | reflexivity] | rk | rewrite HTP; rk | apply mod16_sub; [exact A16 | reflexivity]
    | unfold L5CSA.OPDEL_SCR, L5CSA.MALLOC_SCR; clear - HSCR; lia | clear; lia | ].
  intros fx43 R43 M43 model43 A43 RP43 CI43 PRES43.
  cbn [lb_remove fst] in CI43, PRES43. rewrite NE3, NE4, Z.eqb_refl in CI43, PRES43.
  pose proof (opdel_ag L ar C LY UNWL _ _ _ _ _ M42 M43 PRES43 ltac:(unfold L5CSA.OPDEL_SCR, L5CSA.MALLOC_SCR; clear - SLO42 HSCR; lia) ltac:(unfold L5CSA.OPDEL_SCR, L5CSA.MALLOC_SCR; clear; lia)) as AG.
  carry M42 M43 AG sd_call. clear AG PRES43 SLO42 SHI42 SPT42 NE3 NE4 DN InD3 InD4.
  (* [comment removed for export] *)
  pose proof CI43 as (HH43 & _).
  destruct (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ model43 F3a 3 _ _ fl3a HH HH43 ltac:(unfold L5DSA.ff_e3; do 4 right; left; reflexivity) (or_introl eq_refl) Hk3 FLCa0) as [FLCa43 _].
  pose proof (frame_shadow_defined L ar C HI LY HIok M42 model42 A41 LB1 _ Sp SCR XW F3a 3 (Sp - 464) _ _ _ _ _ _ CI43 Hk3 SHDa42) as SHDa43.
  destruct (cv_frame L ar C HI LY HIok M42 model42 A41 LB1 _ Sp SCR XW F3a 3 (Sp - 464) _ _ _ _ _ _ CI43 Hk3 fl3a FLCa43 ltac:(unfold FS_BYTES; exact FLPa) SHDa43) as (FDEFv & FWv & FSHWv & FLCv & FLWv & _ & _).
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *. replace (F3a + 512 - 8) with (F3a + 504) in FLCv by (clear; lia).
  assert (ICp : L5.img_clear M43 860160 884736) by (intros i Hi; apply IC1; clear - Hi; lia).
  pose proof (ue3p5e_conc fx43 R43 (mrestrict (ahid A43 model43) M43)
                (fun j => match j with 2%nat => Sp - 112 | 40%nat => F3a | 41%nat => fl3a | 58%nat => U R43 1 | _ => 0 end)) as P. cbn beta iota in P.
  padfeed P CI43 ltac:(unfold S, SB in *; unfold numf in NUM; unfold numg in FN; clear - NUM FN DJF FLAa FLPa; lia).
  destruct P as (fx44 & R44 & M44v & MG44 & _ & FZ44 & (MS44 & KS44 & R44_1 & R44_10 & R44_11 & _)).
  pose proof (L5AE3PD.div_pad_tail fx43 fx44 R43 R44 (mrestrict (ahid A43 model43) M43) M44v (Sp - 112) F3a fl3a 605300 (Z_to_bv 64 (obj - 32)) MS44 MG44) as T.
  specialize (T ltac:(intros i Hi N1 N2; apply FZ44; [exact Hi | clear - N1; lia | clear - N2; lia])).
  specialize (T ltac:(intros j Hj; apply KS44; revert j Hj; apply L5K.incl_b; vm_compute; reflexivity) R44_1 R44_10 R44_11 ltac:(rewrite (KS44 22%nat) by inl; rk)).
  padfeed T CI43 ltac:(unfold S, SB in *; unfold numf in NUM; unfold numg in FN; clear - NUM FN DJF FLAa FLPa; lia).
  destruct T as (fx45 & R45 & M45v & MS45 & MG45 & FZ45 & FL045 & R45_10 & KS45).
  apply (cinv_retire L ar C HI LY HIok M42 model42 A41 LB1 _ Sp SCR XW F3a 3 (Sp - 464) _ M43 model43 _ _ A43 fx43 fx45 R43 605300 R45 605584 M45v
           (Wpad F3a 512 fl3a) fl3a K CI43 HS0 Hk3 FLCa43 ltac:(unfold FS_BYTES; exact FLPa)
           (fun X => FLNCa (aclient_appb L ar LB1 _ _ 0 0 fl3a X)) MS45 MG45 FZ45).
  { intros a Wa. unfold Wpad in Wa. change (ff_bytes 3 / 8) with 64. change (512 / 8) with 64 in Wa. clear - Wa. destruct Wa as [X|[X|X]]; [left; exact X | right; left; exact X | right; right; left; exact X]. }
  { intros a. apply Wpad_dec. }
  { exact FL045. }
  intros M45 model45 CI45 AH45 VIS45 FRM45.
  pose proof (pad_agree L ar C HI LY HIok M42 model42 A41 LB1 _ Sp SCR XW F3a 3 (Sp - 464) _ _ _ _ _ _ fl3a M45 CI43 Hk3 ltac:(unfold FS_BYTES; exact FLPa) FRM45) as AG.
  carry M43 M45 AG ltac:(cvis_tac [(ref, 66); (u, 144)]).
  clear AG FRM45 VIS45 MS45 MG45 FZ45 FL045 FDEFv FWv FSHWv FLCv FLWv SHDa43 FLCa43 HH43 ICp MS44 MG44 FZ44 KS44 R44_1 R44_10 R44_11.
  assert (R45_2 : getr R45 (reg 2) = Z_to_bv 64 (Sp - 496)) by (rewrite (KS45 2%nat) by in_tac; rk).
  assert (R45_3 : getr R45 (reg 3) = Z_to_bv 64 67584) by (rewrite (KS45 3%nat) by in_tac; rk).
  assert (R45_4 : getr R45 (reg 4) = Z_to_bv 64 6363400) by (rewrite (KS45 4%nat) by in_tac; rk).
  assert (R45_8 : getr R45 (reg 8) = Z_to_bv 64 (Sp - 112)) by (rewrite (KS45 8%nat) by in_tac; rk).
  clear KS45.
  clear FLCa0 FLPa FLNCa FLAa SHDa0 SHDa42 HinD AL_Fa AL_E5.
  tidy CI45.
  (* [comment removed for export] *)
  destruct (cv_tls L ar C IL HI LY ILY HIok ICok UNWL M42 model42 A41 LB1 _ Sp SCR XW _ _ _ _ _ _ CI45) as (ctx & th & tbv & tev & blk & TLSC & TLSR & TLSI & TLSP & TLSB).
  cbv zeta in TLSC. rewrite HTP in TLSC. change (6363400 + 8) with 6363408 in TLSC. destruct TLSC as (TC1 & TC2 & TC3 & TC4 & TC5 & TC6).
  pose proof (TLSB u 144 ltac:(right; left; reflexivity)) as TB2. clear TLSB.
  pose proof NUM as NUMB. change numf with numg in NUMB.
  assert (NUM4 : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR)
                      /\ (0 <= Sp - 1296 < 2 ^ 64 /\ 140735332552704 <= Sp - 1296 /\ Sp - 1296 <= 140737488355264)
                      /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47 /\ Sp + 16 <= av)
                      /\ (obj = u + 128 /\ 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 16 <= ahl_ceil ar)
                      /\ (17594333495296 <= msg /\ msg + 48 <= ahl_ceil ar)
                      /\ (17594333495296 <= ref /\ ref + 66 <= ahl_ceil ar)
                      /\ (4096 <= ctx /\ ctx + 160 <= ahl_ceil ar /\ 4096 <= th /\ th + 64 <= ahl_ceil ar /\ 4096 <= blk /\ blk + 4096 <= ahl_ceil ar /\ 0 <= tbv < 2 ^ 64 /\ 0 <= tev < 2 ^ 64))).
  { unfold numf in *. clear - NUM TLSR. lia. }
  destruct TLSI as (DJ1 & DJ2 & DJ3). destruct TLSP as (DJ4 & DJ5 & DJ6). destruct TB2 as (DJ10 & DJ11 & DJ12).
  clear NUM. rename NUM4 into NUM. clear TLSR.
  expand_arr_at AUXV 20%nat av 0. expand_arr_at FRD 13%nat (Sp - 1296) 1080.
  pose proof (ue3r5_conc HFILL HCOPY HTLS fx45 R45 (mrestrict (ahid A43 model45) M45)
                (fun j => match j with 2%nat => Sp - 1296 | 10%nat => obj | 32%nat => av | 33%nat => canary | 34%nat => uid | 36%nat => rnd | 39%nat => hw | 40%nat => ctx | 41%nat => th | 42%nat => blk | 43%nat => tbv | 44%nat => tev | 45%nat => F1a | 46%nat => nz xo | 47%nat => nz bo | 48%nat => F1a + 32 | 49%nat => F1a / 8 + SB | 50%nat => F1a | 51%nat => L5DSA.RETIRE_MAGIC | 52%nat => L5DSA.U R0 25 | 53%nat => L5DSA.U R0 26 | 54%nat => L5DSA.U R0 27 | _ => 0 end)) as P. cbn beta iota in P.
  feed_rng P ltac:(first [ apply nz_range | apply UR | apply BL.bvu_range | (unfold L5DSA.U; apply BL.bvu_range) | nlia | (unfold S, SB, L5DSA.RETIRE_MAGIC; unfold numg in FN; clear - FN; lia) ]).
  feed P ltac:(first [fcell CI45 | fdp CI45]).
  repeat match goal with H : L5.u64_at _ M45 (Sp - 1296 + _) _ |- _ => clear H | H : L5.u64_at _ M45 (av + _) _ |- _ => clear H | H : L5.u64_at _ M45 av _ |- _ => clear H end.
  piece_step CI45 XWIMG P (fun a => (Sp - 1296 - 10560) <= a < (Sp - 1296 - 10560) + 11360) fx46 R46 M46 model46 CI46.
  clear TC1 TC2 TC3 TC4 TC5 TC6 DJ1 DJ2 DJ3 DJ4 DJ5 DJ6 DJ10 DJ11 DJ12.
  clear NUM. rename NUMB into NUM. change numg with numf in NUM. clear ctx th tbv tev blk.
  tidy CI46.

  exact (L5BE3S15.e3_s15 L ar C IL HI LY ILY HIok ICok HFILL HCOPY HTLS UNWL R0 R M model K LB1 FF LK LKt cr A Sp SCR xo rt8 gd av uid rnd canary hw F1a fl1a F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d d1 d2 d3 d4 qx bo LB0 lenX w5 w10 xs fbx fd0N fn0N fnN fdenN w1 fd0 fn0 fn fden v0 v1 v2 v3 nd0 nn0 nn nd M3 errv R1 R2 A2 u obj R3 model3 R4 R5 R6 R7 A7 msg R8 R9 R10 R11 R12 R13 R14 A14 ref R15 R16 R17 R18 R19 R20 R21 st R22 R23 R24 R25 A25 R26 R27 R28 R29 A29 R30 R31 A31 R32 R33 R34 R35 R36 R37 R38 M42 R39 R40 R41 A41 R42 model42 M46 R43 A43 R44 R45 fx46 R46 model46 bq ELB1 Z2 Z3 Z4 Z10 Z8 Z9 Z18 Z19 Z20 Z21 Z22 Z23 Z24 Z25 Z26 Z27 DEN0Nr DEN0Nt NUM0Nr NUM0Nt NUMN NUMNT DENN DENNT ZQ o2 o3 o4 o5 DEN0f DEN0r DEN0t NUM0f NUM0r NUM0t NUMO DENO BQ BQD BX SHd SHc SH3b SH1b SH3a SH1a FRL1a FRL3a FRL1b FRL3b FRLc FRLd LFR G1 G2 G3 G4 G9 S32 RT8 RTRA EC0 GD0 GD1 TDL MSG0 ERR ERRR CAN AUXP AV8 AVLO AVHI UIDR RNDR CANR HWR AVS HH AM HK LKI STK HSCR SCR8 SH CRF KONT A16 SLO SHI SPT AVT HS0 ALS ALS8 SPR0 SPLO SPHI LY2 HTP FN FAL DJF ACC0 E8 E9 EX0 EX1 EX2 EX3 EX4 ACR1 CRF1 RP2 EOBJ OB16 OB8 OBR0 OBR OCEIL DJU R2_10 Hk1 FLCd0 FLPd SHDd0 FDN FDA AL_Fd EX10 EX11 EX12 EX13 EX14 EX15 EX16 EX17 ACC3 EX5 EX6 EX18 EX19 EX20 EX22 EX23 EX24 sR5 RP5 EX8 EX9 EX31 EX32 EX33 EX34 EX35 EX36 ACR2 CRF2 mR7 RP7 DJM APmu MS16 Z72 MS8 EX38 EX39 EX40 EX41 EX42 EX43 EX44 EX45 HMV R8_10 mR9 RP9 SHAP SHAPM E41 EX37 EX46 EX47 EX48 EX49 EX50 EX51 EX52 EX53 EX54 EX55 EX56 E10 EX7 EX29 EX30 EX61 EX62 EX63 R11_8 sR12 RP12 EX21 EX25 EX26 EX27 EX70 EX71 ACR3 mR14 RP14 DJR APru APrm RF16 EX74 EX75 EX76 EX77 EX78 EX79 EX80 EX81 EX82 EX83 EX84 HMC mR16 RP16 EX72 EX73 EX85 EX86 EX87 EX88 EX89 EX90 EX91 EX92 RP18 EX28 EX57 EX58 EX E19_10 EX64 EX65 EX66 EX67 EX68 EX69 EX93 EX94 EX95 EX99 EX102 EX103 EX104 EX105 EX107 RP21 AV8' STE EX112 EX113 EX114 EX115 EX116 EX117 EX118 EX119 EX120 EX121 EX122 EX123 EX124 EX125 EX126 EX127 EX128 EX129 EX130 EX131 EX132 EX133 EX59 FLNCd FLAd AL_E AL_F EX97 EX98 EX96 R23_19 EX101 EX106 EX134 EX100 RP25 KS26 R26_10' EX108 EX109 EX110 EX111 EX135 EX136 EX137 EX138 EX139 EX140 EX141 EX142 EX143 EX144 EX60 Hk3 AL_E2 EX146 EX147 EX148 EX149 EX145 R28_24 RP29 EX151 EX152 EX153 EX150 RP31 R33_10 R33_2 R33_3 R33_4 R33_8 EX155 EX156 EX157 EX158 EX159 EX160 EX161 EX162 EX163 EX164 EX165 EX166 EX167 EX168 EX169 EX154 KS35 R35_19 EX171 EX172 EX173 EX174 EX175 EX176 EX177 EX178 EX179 EX180 EX181 EX182 EX170 EX184 EX185 EX183 EX187 EX188 EX189 EX190 EX191 EX186 EX193 EX194 EX192 R39_24 EX196 EX197 EX198 EX195 RP41 EX199 EX200 EX201 EX202 ACC42 RP43 R45_10 R45_2 R45_3 R45_4 R45_8 NUM EX204 EX205 EX206 EX207 EX208 EX209 EX210 EX211 EX212 EX213 EX214 EX215 EX216 EX217 EX218 EX203 CI46 FRO FRD AUXV IC3 IC2 IC1).
Qed.

End WithIface.
End SCFG_1.
End L5BE3S14.
