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
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ParseSpecsA L5OpmodSpecsA L5DivSpecsA L5UnwindSpecsA XIcptA XIcptAs0Kit L5AUnwK L5AUnwK2 L5AE1K L5AE2K L5AE3K L5AE2PP L5AE2Pad L5AE3P1 L5AE3P2 L5AE3P3 L5AE3P4 L5AE3P5 L5AE3P6 L5AE3P7 L5AE3P8 L5AE3P9 L5AE3P10 L5AE3P11 L5AE3PP L5AE3Pad L5AUnwK3 L5AUnwK4 L5DivInnerSpecsA L5AOpdel L5AE3S4.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Set Printing Width 100000. Set Printing Depth 100000.

Module L5AE3S3.
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

Lemma e3_s3 :
  forall (R0 : bvmap 5 word) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB1 : list (Z * Z)) (FF : list fframe) (LK : list fframe) (LKt : list fframe) (cr : credit) (A : list (Z * Z)) (Sp : Z) (SCR : Z) (xo : Z) (gd : bool) (fl : bool) (av : Z) (uid : Z) (rnd : Z) (canary : Z) (hw : Z) (F1a : Z) (fl1a : Z) (F3a : Z) (fl3a : Z) (F1b : Z) (fl1b : Z) (F3b : Z) (fl3b : Z) (F1c : Z) (fl1c : Z) (F1d : Z) (fl1d : Z) (d1 : Z) (d2 : Z) (d3 : Z) (d4 : Z) (qx : Z) (bo : Z) (LB0 : list (Z * Z)) (lenX : nat) (w9 : Z) (w10 : Z) (xs : Z) (fbx : Z) (fd0N : Z) (fn0N : Z) (fnN : Z) (fdenN : Z) (w1 : Z) (fd0 : Z) (fn0 : Z) (fn : Z) (fden : Z) (v0 : Z) (v1 : Z) (v2 : Z) (v3 : Z) (nd0 : nat) (nn0 : nat) (nn : nat) (nd : nat) (M3 : word -> option byte) (errv : Z) (R1 : bvmap 5 word) (R2 : bvmap 5 word) (A2 : list (Z * Z)) (u : Z) (obj : Z) (R3 : bvmap 5 word) (model3 : Model) (R4 : bvmap 5 word) (M7 : word -> option byte) (R5 : bvmap 5 word) (R6 : bvmap 5 word) (fx7 : FPState) (R7 : bvmap 5 word) (model7 : Model) (A7 : list (Z * Z)) (msg : Z),
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
    forall (m2 : L5.u64_at RSEGS M7 (Sp - 904) F3b),
    forall (m3 : L5.u64_at RSEGS M7 (Sp - 888) F3b),
    forall (m4 : L5.u64_at RSEGS M7 (Sp - 880) (F3b + 96)),
    forall (m5 : L5.u64_at RSEGS M7 (Sp - 872) (F3b + 32)),
    forall (m8 : L5.u64_at RSEGS M7 (Sp - 848) (S F3b)),
    forall (DEN0Nf : L5.u8_at RSEGS M7 (Sp - 776) fd0N),
    forall (DEN0Nr : 0 <= fd0N < 256),
    forall (DEN0Nt : Z.testbit fd0N 0 = false),
    forall (NUM0Nf : L5.u8_at RSEGS M7 (Sp - 744) fn0N),
    forall (NUM0Nr : 0 <= fn0N < 256),
    forall (NUM0Nt : Z.testbit fn0N 0 = true),
    forall (NUM0Nc : L5.u64_at RSEGS M7 (Sp - 744 + 16) 8),
    forall (NUM0Np : L5.u64_at RSEGS M7 (Sp - 744 + 24) d1),
    forall (NUMN : L5.big_at RSEGS M (F3b + 96) {| L5.bo_fb := fnN; L5.bo_len := 0; L5.bo_st := L5.BDyn 8 d2 |}),
    forall (NUMNT : Z.testbit fnN 1 = false),
    forall (DENN : L5.big_at RSEGS M (F3b + 32) {| L5.bo_fb := fdenN; L5.bo_len := 1; L5.bo_st := L5.BInl L5DSA.MWORD w1 |}),
    forall (DENNT : Z.testbit fdenN 1 = false),
    forall (ZQ : L5DIA.zero_obj M (F1b + 32)),
    forall (MWf : L5.u8_at RSEGS M7 (Sp - 504) 0),
    forall (o2 : L5.u64_at RSEGS M7 (Sp - 392) F3a),
    forall (o3 : L5.u64_at RSEGS M7 (Sp - 376) F3a),
    forall (o4 : L5.u64_at RSEGS M7 (Sp - 368) (F3a + 96)),
    forall (o5 : L5.u64_at RSEGS M7 (Sp - 360) (F3a + 32)),
    forall (o8 : L5.u64_at RSEGS M7 (Sp - 336) (S F3a)),
    forall (DEN0f : L5.u8_at RSEGS M7 (Sp - 264) fd0),
    forall (DEN0r : 0 <= fd0 < 256),
    forall (DEN0t : Z.testbit fd0 0 = false),
    forall (NUM0f : L5.u8_at RSEGS M7 (Sp - 232) fn0),
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
    forall (EC0 : L5.u64_at RSEGS M7 6357448 0),
    forall (EU0 : L5.u32_at RSEGS M7 6357456 0),
    forall (GD0 : L5.u8_at RSEGS M7 6358000 (if gd then 1 else 0)),
    forall (GD1 : L5.u8_at RSEGS M7 6358001 (if gd then 1 else 0)),
    forall (TDL : L5.u64_at RSEGS M7 6360280 6492112),
    forall (MSG0 : L5.u64_at RSEGS M7 6492152 0),
    forall (ERR : L5.u32_at RSEGS M7 6360164 errv),
    forall (ERRR : 0 <= errv < 2 ^ 64),
    forall (CAN : L5.u64_at RSEGS M7 6491464 canary),
    forall (AUXP : L5.u64_at RSEGS M7 6492064 av),
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
    forall (KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LK' : list fframe) (A' : list (Z * Z)), regs_preserved R0 R' -> L5USA.e3_landed L {| L5USA.xs_gd := gd; L5USA.xs_fl := fl; L5USA.xs_av := av; L5USA.xs_uid := uid; L5USA.xs_rnd := rnd; L5USA.xs_canary := canary; L5USA.xs_hw := hw |} LB1 FF LK cr Sp M' R' LB' cr' LK' -> ahpres L ar LB1 FF Sp SCR L5USA.xs_foot M M' -> model_rt model model' -> incl A A' -> amodel_ok A' model' -> ri_inv HI LB' FF LK' cr' A' M' (vml_of model') -> srealizes RSEGS SCFG (cfg (fx:=fx') R' 582452 M' model') K),
    forall (FL0 : L5.u8_at RSEGS M7 6360113 (if fl then 1 else 0)),
    forall (FL2 : L5.u8_at RSEGS M7 6360115 (if fl then 1 else 0)),
    forall (FL4 : L5.u8_at RSEGS M7 6360117 (if fl then 1 else 0)),
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
    forall (FLPd : ar_fs ar <= fl1d < ar_fs ar + FS_BYTES),
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
    forall (EX21 : L5KA.zeros_at M7 (obj - 128) 144),
    forall (ACC3 : acc L ar M model A LB1 Sp SCR XW ((F1c, 1, Sp - 1056) :: (F3b, 3, Sp - 928) :: (F1b, 1, Sp - 576) :: (F3a, 3, Sp - 416) :: (F1a, 1, Sp - 64) :: FF) M3 model3 A2),
    forall (KSH : keep (L5.u8_at RSEGS M3 (F1d / 8 + 2147450884) 0 /\ L5.u8_at RSEGS M3 (F1d / 8 + 2147450885) 0 /\ L5.u8_at RSEGS M3 (F1d / 8 + 2147450886) 0)),
    forall (SHDd3 : L5.defined M3 (F1d / 8 + SB) 16),
    forall (EX5 : forall x : nat, In x KS_ue3s1 -> getr R4 (reg x) = getr R3 (reg x)),
    forall (EX6 : getr R4 (reg 1) = Z_to_bv 64 589468),
    forall (EX18 : getr R4 (reg 2) = Z_to_bv 64 (Sp - 1216 - 64)),
    forall (EX19 : getr R4 (reg 8) = Z_to_bv 64 141920),
    forall (EX20 : getr R4 (reg 10) = Z_to_bv 64 141920),
    forall (EX22 : getr R4 (reg 11) = Z_to_bv 64 908088),
    forall (EX23 : getr R4 (reg 18) = Z_to_bv 64 (F1d + 32)),
    forall (EX24 : getr R4 (reg 21) = Z_to_bv 64 2147450880),
    forall (EX25 : L5.u64_at RSEGS M7 (Sp - 1216 - 56) obj),
    forall (EX26 : L5.u64_at RSEGS M7 (Sp - 1216 - 48) (F1d + 32)),
    forall (EX27 : L5.u64_at RSEGS M7 (Sp - 1216 - 40) (bv_unsigned (getr R3 (reg 19)))),
    forall (EX28 : L5.u64_at RSEGS M7 (Sp - 1216 - 32) F1d),
    forall (EX29 : L5.u64_at RSEGS M7 (Sp - 1216 - 24) (Sp - 1216)),
    forall (EX30 : L5.u64_at RSEGS M7 (Sp - 1216 - 16) (Sp - 1216 + 128)),
    forall (EX : L5.u64_at RSEGS M7 (Sp - 1216 - 8) 590580),
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
    forall (EX37 : L5.u64_at RSEGS M7 (Sp - 1216 - 80) 141920),
    forall (EX7 : L5.u64_at RSEGS M7 (Sp - 1216 - 72) 589552),
    forall (ACR2 : acredit_ok L (adebit L cr 144) 48),
    forall (CRF2 : L5OMA.acredit_for L (adebit L (adebit L cr 144) 48) 1 66),
    forall (mR7 : getr R7 (reg 10) = Z_to_bv 64 msg),
    forall (RP7 : regs_preserved R6 R7),
    forall (CI7 : cinv L ar HI M3 model3 A2 LB1 ((F1d, 1, Sp - 1184) :: (F1c, 1, Sp - 1056) :: (F3b, 3, Sp - 928) :: (F1b, 1, Sp - 576) :: (F3a, 3, Sp - 416) :: (F1a, 1, Sp - 64) :: FF) Sp SCR XW [(msg, 48); (u, 144); (d1, 64); (d2, 64); (d3, 64); (d4, 64)] M7 model7 LKt (adebit L (adebit L cr 144) 48) A7),
    forall (FL5 : fl = true -> L5.u8_at RSEGS M7 6360118 0),
    forall (FL3 : fl = true -> L5.u8_at RSEGS M7 6360116 0),
    forall (FL1 : fl = true -> L5.u8_at RSEGS M7 6360114 0),
    forall (FRO : forall j : nat, (j < 11)%nat -> L5.u64_at RSEGS M7 (Sp - 88 + 8 * Z.of_nat j) (nth j [F1a; L5DSA.U R0 24; L5DSA.U R0 23; L5DSA.U R0 22; L5DSA.U R0 21; L5DSA.U R0 20; L5DSA.U R0 19; L5DSA.U R0 18; Sp; L5DSA.U R0 8; 581760] 0)),
    forall (FRD : forall j : nat, (j < 13)%nat -> L5.u64_at RSEGS M7 (Sp - 200 + 8 * Z.of_nat j) (nth j [L5DSA.U R0 27; L5DSA.U R0 26; L5DSA.U R0 25; L5DSA.RETIRE_MAGIC; F1a; F1a / 8 + SB; F1a + 32; nz bo; nz xo; F1a; Sp - 96; Sp; L5DSA.DIV_RET_O] 0)),
    forall (FRU : forall j : nat, (j < 3)%nat -> L5.u64_at RSEGS M7 (Sp - 472 + 8 * Z.of_nat j) (nth j [Sp - 448; Sp - 96; L5DSA.UNNORM_RET] 0)),
    forall (FRQ : forall j : nat, (j < 11)%nat -> L5.u64_at RSEGS M7 (Sp - 600 + 8 * Z.of_nat j) (nth j [F1b; F3a; nz (S xo); F1a + 32; F3a + 96; F3a + 32; nz xo; S F3a; nz xs; nz xo; L5DSA.DIVEQ_RET] 0)),
    forall (FRN : forall j : nat, (j < 13)%nat -> L5.u64_at RSEGS M7 (Sp - 712 + 8 * Z.of_nat j) (nth j [F3a; nz w10; nz w9; L5DSA.RETIRE_MAGIC; F1b; S F1b; F1b + 32; Sp - 504; nz xo; F1b; Sp - 608; Sp - 512; L5DSA.DIV_RET_N] 0)),
    forall (FRZ : forall j : nat, (j < 13)%nat -> L5.u64_at RSEGS M7 (Sp - 1064 + 8 * Z.of_nat j) (nth j [F1c; F3b + 48; nz w9; nz xo; F1b + 32; nz xo; SB; F3b + 96; F3b + 32; S F3b; Sp - 960; Sp - 608; L5DSA.RESIZE_RET_G] 0)),
    forall (FRA : forall j : nat, (j < 13)%nat -> L5.u64_at RSEGS M7 (Sp - 1192 + 8 * Z.of_nat j) (nth j [F1d; nz (S (xo + 8)); nz (Z.of_nat lenX); SB; F1c; S F1c; nz (xo + 8); nz xo; 2 ^ 64 - 1; F1c; Sp - 1088; Sp - 960; L5DSA.RESERVE_RET] 0)),
    forall (AUXV : forall j : nat, (j < 20)%nat -> L5.u64_at RSEGS M7 (av + 8 * Z.of_nat j) (nth j (L5USA.auxv20A uid rnd hw) 0)),
    forall (IC3 : L5.img_clear M7 892784 (892784 + 8)),
    forall (IC2 : L5.img_clear M7 892736 892768),
    forall (IC1 : L5.img_clear M7 65536 880640),
    forall (DJM : msg + 48 <= ar_fs ar \/ ar_fs ar + 11571200 <= msg),
    forall (APmu : msg + 48 <= u \/ u + 144 <= msg),
    forall (MS16 : msg mod 16 = 0),
    forall (NUM : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR) /\ (0 <= Sp - 1216 < 2 ^ 64 /\ 140735332552704 <= Sp - 1216 <= 140737488355264) /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47) /\ (obj = u + 128 /\ 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 16 <= ahl_ceil ar) /\ 17594333495296 <= msg /\ msg + 48 <= ahl_ceil ar)),
  srealizes RSEGS SCFG (cfg (fx:=fx7) R7 856060 M7 model7) K.
Proof.
  intros.
  (* [comment removed for export] *)
  match goal with H : L5KA.zeros_at M7 (obj - 128) 144 |- _ => pose proof (L5KA.zeros_at_sub M7 (obj - 128) 144 (obj - 72) 4 H ltac:(clear; lia) ltac:(clear; lia)) as Z72 end.
  (* [comment removed for export] *)
  assert (MS8 : msg mod 8 = 0) by (apply mod8_of_16; exact MS16).
  pose proof CI7 as (HH7 & _).
  destruct (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ model7 F1d 1 _ _ fl1d HH HH7 (or_introl eq_refl) (or_introl eq_refl) Hk1 FLCd0) as [FLCd7 _].
  pose proof (frame_shadow_defined L ar C HI LY HIok M3 model3 A2 LB1 _ Sp SCR XW F1d 1 (Sp - 1184) _ _ _ _ _ _ CI7 Hk1 SHDd3) as SHDd7.
  destruct (cv_frame L ar C HI LY HIok M3 model3 A2 LB1 _ Sp SCR XW F1d 1 (Sp - 1184) _ _ _ _ _ _ CI7 Hk1 fl1d FLCd7 FLPd SHDd7) as (FDEFv & FWv & FSHWv & _ & _ & _ & _).
  change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *. unfold SB in FSHWv.
  assert (ZM : L5KA.zeros_at (mrestrict (ahid A7 model7) M7) (msg / 8 + 2147450880) 6) by (fd_mem CI7).
  assert (E41 : (msg + 41) / 8 = msg / 8 + 5). { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - MS8. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (ZM41 : L5KA.zeros_at (mrestrict (ahid A7 model7) M7) ((msg + 41) / 8 + 2147450880) 1).
  { rewrite E41. apply (L5KA.zeros_at_sub _ (msg / 8 + 2147450880) 6 _ 1 ZM); clear; lia. }
  (* [comment removed for export] *)
  assert (ZSH : L5KA.zeros_at (mrestrict (ahid A7 model7) M7) (F1d / 8 + 2147450884) 3).
  { unfold keep in KSH. destruct KSH as (K4 & K5 & K6).
    apply (cv_fsh_zeros L ar C HI LY HIok M3 model3 A2 LB1 _ Sp SCR XW F1d 1 (Sp - 1184) _ _ _ _ _ _ CI7 Hk1). unfold SB; clear; lia. unfold SB; change (ff_bytes 1 / 8) with 16; clear; lia.
    assert (AGS : L5C.agree_on M3 M7 (F1d / 8 + 2147450884) 3).
    { apply (frame_shadow_agree L ar C HI LY HIok M3 model3 A2 LB1 _ Sp SCR XW F1d 1 (Sp - 1184) _ _ _ _ _ _ CI7 Hk1 XWIMG). unfold SB; clear; lia. unfold SB; change (ff_bytes 1 / 8) with 16; clear; lia. }
    apply zeros3_of_u8.
    - eapply L5.defined_sub. exact SHDd7. unfold SB; clear; lia. unfold SB; clear; lia.
    - apply (L5C.u8_at_agree RSEGS M3 M7 _ 0). 4: exact K4. intros i Hi; apply AGS; clear - Hi; lia. unfold numg in FN; clear - FN; lia. unfold numg in FN; clear - FN; lia.
    - apply (L5C.u8_at_agree RSEGS M3 M7 _ 0). 4: replace (F1d / 8 + 2147450884 + 1) with (F1d / 8 + 2147450885) by (clear; lia); exact K5. intros i Hi; apply AGS; clear - Hi; lia. unfold numg in FN; clear - FN; lia. unfold numg in FN; clear - FN; lia.
    - apply (L5C.u8_at_agree RSEGS M3 M7 _ 0). 4: replace (F1d / 8 + 2147450884 + 2) with (F1d / 8 + 2147450886) by (clear; lia); exact K6. intros i Hi; apply AGS; clear - Hi; lia. unfold numg in FN; clear - FN; lia. unfold numg in FN; clear - FN; lia. }
  pose proof (ue3s3_conc HFILL HCOPY HTLS fx7 R7 (mrestrict (ahid A7 model7) M7) (fun j => match j with 2%nat => Sp - 1216 | 10%nat => obj | 38%nat => msg | 40%nat => F1d | _ => 0 end)) as P. cbn beta iota in P.
  ffeed P CI7 F1d ltac:(flia).
  destruct P as (fx8 & R8 & Mv & MG & _ & FZ & (MS & EXP)).
  apply (cinv_piece_rebase L ar C HI LY HIok M model A LB1 Sp SCR XW XWIMG _ M3 model3 A2 F1d 1 (Sp - 1184) _ [(msg, 48); (u, 144); (d1, 64); (d2, 64); (d3, 64); (d4, 64)] M7 model7 LKt _ A7 _ fx8 _ _ R8 _ Mv
           (fun a => Sp - 1216 - 144 <= a < Sp - 1216 - 144 + 64 \/ F1d + 32 <= a < F1d + 32 + 24)
           K ACC3 (sufl_refl L ar LB1 _) CI7 HS0 Hk1 MS MG).
  { intros a Ha Hna. apply FZ; [exact Ha | cbv beta in Hna; clear - Hna; lia ..]. }
  { intros a Wa. cbv beta in Wa. destruct Wa as [Wa|Wa].
    - left. left. nlia.
    - right. left. change (ff_bytes 1) with 128. clear - Wa. lia. }
  intros M8 model8 ACC8 CI8 AH8 VIS8 MG8 FRM8. subst Mv. clear MS MG FZ.
  repeat (lazymatch type of EXP with _ /\ _ => let X := fresh "EX" in destruct EXP as [X EXP] end).
  (* [comment removed for export] *)
  assert (KMSG : keep (L5.u64_at RSEGS M8 (F1d + 32) 49 /\ L5.u64_at RSEGS M8 (F1d + 40) 41 /\ L5.u64_at RSEGS M8 (F1d + 48) msg)).
  { unfold keep. repeat split;
      (apply (cu_fs_u64 L ar C HI LY HIok M8 model8 A7 LB1 _ Sp SCR XW F1d 1 (Sp - 1184) _ _ _ _ _ _ CI8 Hk1); [unfold numg in FN; clear - FN; lia | unfold FS_BYTES; unfold numg in FN; clear - FN; lia | assumption]). }
  pose proof (rb_agree L ar C HI LY HIok M3 model3 A2 LB1 _ Sp SCR XW F1d 1 (Sp - 1184) _ _ _ _ _ _ CI7 Hk1 M8 _
                (fun a => Sp - 1216 - 144 <= a < Sp - 1216 - 144 + 64) FRM8) as AG.
  specialize (AG ltac:(intros a Wa; cbv beta in Wa; destruct Wa as [Wa|Wa]; [left; exact Wa | right; left; change (ff_bytes 1) with 128; clear - Wa; lia])).
  cbv beta in AG.
  lift_cells CI8.
  carry M7 M8 AG ltac:(idtac; lazymatch goal with |- L5AUK.cvis _ _ _ _ _ => cvis_tac [(msg, 48); (u, 144); (d1, 64); (d2, 64); (d3, 64); (d4, 64)] | |- _ => sd_piece end).
  assert (SHDd8 : L5.defined M8 (F1d / 8 + SB) 16) by (eapply L5.defined_grows; [exact MG8 | exact SHDd7]).
  clear AG FRM8 FDEFv FWv FSHWv SHDd7 FLCd7 HH7 MG8 SHDd3 ZM ZM41 E41 ZSH KSH.
  (* [comment removed for export] *)
  pose proof (cinv_num L ar HI M8 model8 A7 LB1 _ Sp SCR XW _ _ _ _ _ _ CI8) as (_ & SLO8 & SHI8 & SPT8).
  assert (HMV : amemcpy_spec_at L ar SCFG HI 0x5e7b0 false). { pose proof (aio_memmove _ _ _ _ _ HIok) as X. unfold amemmove_spec in X. rewrite (aly_memmove L C LY) in X. exact X. }
  assert (InM : In (msg, 48) ([(msg, 48); (u, 144); (d1, 64); (d2, 64); (d3, 64); (d4, 64)] ++ LB1)) by (left; reflexivity).
  assert (R8_10 : getr R8 (reg 10) = Z_to_bv 64 msg) by rk.
  apply (CMEMCPY 0x5e7b0 false _ _ _ _ _ _ fx8 R8 msg 141920 41 (firstn 41 L5AE3K.at_buf) (Sp - 1216 - 64) 589644 K HMV CI8 HK HS0);
    [ rk | rk | rk | clear; lia | rk | split; [clear; lia | reflexivity] | rk | rewrite HTP; rk | apply mod16_sub; [exact ALS | reflexivity] | clear - HSCR; lia | clear; lia
    | right; exists msg, 48; split; [left; reflexivity | clear; lia]
    | apply (aacc_xblk L ar C HI LY HIok M8 model8 A7 LB1 _ Sp SCR XW _ _ _ _ _ _ msg 48 _ _ CI8 InM); clear; lia
    | apply (app_rng_block L ar C HI HIok _ _ _ _ _ _ _ msg 48 _ _ (proj1 CI8) InM); clear; lia
    | apply (asrc_aacc L ar C IL HI ILY HIok ICok _ _ _ _ _ M8 _ 141920 41 (proj1 CI8)); right; right; left; exists 0x22a60, 42; split; [rewrite (aicl_globals IL ILY); in_tac | clear; lia]
    | clear; lia
    | apply app_rng_img; [clear - SPT8; lia | clear; lia | clear; lia]
    | right; left; clear; lia
    | exact (L5AE3K.at_rdnk M8 41 ltac:(clear; lia) IC1) | intros _; unfold numf in NUM; clear - NUM; lia | ].
  intros fx9 R9 M9 model9 mR9 RP9 CI9 BYTES AG.
  pose proof (rdn_of_copied M9 msg (firstn 41 L5AE3K.at_buf) BYTES ltac:(unfold numf in NUM; clear - NUM; lia)
                ltac:(change (Z.of_nat (length (firstn 41 L5AE3K.at_buf))) with 41; unfold numf in NUM; clear - NUM; lia)) as RDM.
  change (length (firstn 41 L5AE3K.at_buf)) with 41%nat in RDM.
  carry M8 M9 AG sd_calld. clear AG BYTES SLO8 SHI8 SPT8 InM.
  tidy CI9.
  exact (L5AE3S4.e3_s4 L ar C IL HI LY ILY HIok ICok HFILL HCOPY HTLS UNWL R0 R M model K LB1 FF LK LKt cr A Sp SCR xo gd fl av uid rnd canary hw F1a fl1a F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d d1 d2 d3 d4 qx bo LB0 lenX w9 w10 xs fbx fd0N fn0N fnN fdenN w1 fd0 fn0 fn fden v0 v1 v2 v3 nd0 nn0 nn nd M3 errv R1 R2 A2 u obj R3 model3 R4 R5 R6 R7 A7 msg M8 M9 R8 model8 fx9 R9 model9 bq ELB1 Z2 Z3 Z4 Z10 Z8 Z9 Z18 Z19 Z20 Z21 Z22 Z23 Z24 Z25 Z26 Z27 m2 m3 m4 m5 m8 DEN0Nf DEN0Nr DEN0Nt NUM0Nf NUM0Nr NUM0Nt NUM0Nc NUM0Np NUMN NUMNT DENN DENNT ZQ MWf o2 o3 o4 o5 o8 DEN0f DEN0r DEN0t NUM0f NUM0r NUM0t NUMO DENO BQ BQD BX SHd SHc SH3b SH1b SH3a SH1a FRL1a FRL3a FRL1b FRL3b FRLc FRLd LFR G1 G2 G3 G4 G9 S32 EC0 EU0 GD0 GD1 TDL MSG0 ERR ERRR CAN AUXP AV8 AVLO AVHI UIDR RNDR CANR HWR AVS HH AM HK LKI STK HSCR SCR8 SH CRF KONT FL0 FL2 FL4 A16 SLO SHI SPT HS0 ALS ALS8 SPR0 SPLO SPHI LY2 HTP FN FAL DJF ACC0 E8 E9 EX0 EX1 EX2 EX3 EX4 ACR1 CRF1 RP2 EOBJ OB16 OB8 OBR0 OBR OCEIL DJU R2_10 Hk1 FLCd0 FLPd SHDd0 FDN FDA AL_Fd EX10 EX11 EX12 EX13 EX14 EX15 EX16 EX17 EX21 ACC3 EX5 EX6 EX18 EX19 EX20 EX22 EX23 EX24 EX25 EX26 EX27 EX28 EX29 EX30 EX sR5 RP5 EX8 EX9 EX31 EX32 EX33 EX34 EX35 EX36 ACR2 CRF2 mR7 RP7 DJM APmu MS16 NUM Z72 MS8 EX38 EX39 EX40 EX41 EX42 EX43 EX44 EX45 ACC8 KMSG SHDd8 HMV R8_10 mR9 RP9 CI9 RDM FL5 FL3 FL1 FRO FRD FRU FRQ FRN FRZ FRA AUXV IC3 IC2 IC1).
Qed.

End WithIface.
End SCFG_1.
End L5AE3S3.
