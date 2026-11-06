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
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5ParseSpecsAB0 L5OpmodSpecsAB0 L5DivSpecsAB0 L5UnwindSpecsAB0 XIcptAB0 XIcptAs0KitB0 L5BUnwK L5BUnwK2 L5BE1K L5BE1P1 L5BE1P2 L5BE1P3 L5BE1P4 L5BE1P5 L5BE1S4.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Set Printing Width 100000. Set Printing Depth 100000.

Module L5BE1S3.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5AUK. Import L5AUK2.
Import L5BE1P1.L5BE1P1. Import L5BE1P2.L5BE1P2. Import L5BE1P3.L5BE1P3. Import L5BE1P4.L5BE1P4. Import L5BE1P5.L5BE1P5.
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
Local Notation XW := [(6360528, 4); (6363185, 6); (6361072, 8); (6363236, 4)].
Local Notation XWIMG := (L5BE1K.xw_img L UNWL).

Lemma e1_s3 :
  forall (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF : list fframe) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (Sp : Z) (SCR : Z) (s0v : Z) (s2v : Z) (gd : bool) (fl : bool) (av : Z) (uid : Z) (rnd : Z) (canary : Z) (hw : Z) (errv : Z) (R1 : bvmap 5 word) (R2 : bvmap 5 word) (A2 : list (Z * Z)) (u : Z) (obj : Z) (R3 : bvmap 5 word) (R4 : bvmap 5 word) (M11 : word -> option byte) (R5 : bvmap 5 word) (R6 : bvmap 5 word) (R7 : bvmap 5 word) (R8 : bvmap 5 word) (R9 : bvmap 5 word) (R10 : bvmap 5 word) (fx11 : FPState) (R11 : bvmap 5 word) (model11 : Model),
    forall (G2 : getr R (reg 2) = Z_to_bv 64 (Sp - 32)),
    forall (G3 : getr R (reg 3) = Z_to_bv 64 67584),
    forall (G4 : getr R (reg 4) = Z_to_bv 64 6363400),
    forall (G9 : getr R (reg 9) = Z_to_bv 64 22),
    forall (G18 : getr R (reg 18) = Z_to_bv 64 SB),
    forall (S32 : Sp mod 32 = 0),
    forall (C8 : L5.u64_at RSEGS M11 (Sp - 8) 582372),
    forall (C16 : L5.u64_at RSEGS M11 (Sp - 16) s0v),
    forall (C24 : L5.u64_at RSEGS M11 (Sp - 24) Sp),
    forall (C32 : L5.u64_at RSEGS M11 (Sp - 32) s2v),
    forall (S0R : 0 <= s0v < 2 ^ 64),
    forall (S2R : 0 <= s2v < 2 ^ 64),
    forall (EC0 : L5.u64_at RSEGS M11 6360520 0),
    forall (EU0 : L5.u32_at RSEGS M11 6360528 0),
    forall (TDL : L5.u64_at RSEGS M11 6363352 6495184),
    forall (MSG0 : L5.u64_at RSEGS M11 6495224 0),
    forall (ERRR : 0 <= errv < 2 ^ 64),
    forall (CAN : L5.u64_at RSEGS M11 6494536 canary),
    forall (AUXP : L5.u64_at RSEGS M11 6495136 av),
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
    forall (KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LK' : list fframe) (A' : list (Z * Z)), getr R' 8 = Z_to_bv 64 s0v -> getr R' 9 = Z_to_bv 64 Sp -> getr R' 18 = Z_to_bv 64 s2v -> (forall i : nat, In i [3%nat; 4%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat] -> getr R' (reg i) = getr R (reg i)) -> L5USA.e1_landed L {| L5USA.xs_gd := gd; L5USA.xs_fl := fl; L5USA.xs_av := av; L5USA.xs_uid := uid; L5USA.xs_rnd := rnd; L5USA.xs_canary := canary; L5USA.xs_hw := hw |} LB FF LK cr Sp M' R' LB' cr' LK' -> ahpres L ar LB FF Sp SCR L5USA.xs_foot1 M M' -> model_rt model model' -> incl A A' -> amodel_ok A' model' -> ri_inv HI LB' FF LK' cr' A' M' (vml_of model') -> srealizes RSEGS SCFG (cfg (fx:=fx') R' 583128 M' model') K),
    forall (FL0 : L5.u8_at RSEGS M11 6363185 (if fl then 1 else 0)),
    forall (FL2 : L5.u8_at RSEGS M11 6363187 (if fl then 1 else 0)),
    forall (FL4 : L5.u8_at RSEGS M11 6363189 (if fl then 1 else 0)),
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
    forall (HTP : hl_tp L = 6363400),
    forall (E9 : bv_unsigned (getr R (reg 9)) = 22),
    forall (EX0 : forall x : nat, In x KS_ue1a1 -> getr R1 (reg x) = getr R (reg x)),
    forall (EX1 : getr R1 (reg 1) = Z_to_bv 64 727044),
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
    forall (NUM : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR) /\ (0 <= Sp - 32 < 2 ^ 64 /\ 140735332552704 <= Sp - 32 <= 140737488355264) /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47) /\ obj = u + 128 /\ 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 32 <= ahl_ceil ar)),
    forall (EX11 : forall x : nat, In x KS_ue1a2_mh -> getr R3 (reg x) = getr R2 (reg x)),
    forall (EX12 : getr R3 (reg 1) = Z_to_bv 64 584360),
    forall (EX13 : getr R3 (reg 2) = Z_to_bv 64 (Sp - 32)),
    forall (EX14 : getr R3 (reg 8) = Z_to_bv 64 obj),
    forall (EX15 : getr R3 (reg 9) = Z_to_bv 64 22),
    forall (EX16 : getr R3 (reg 10) = Z_to_bv 64 0),
    forall (Z72 : L5KA.zeros_at M11 (obj - 72) 4),
    forall (EX7 : getr R4 (reg 1) = Z_to_bv 64 584380),
    forall (EX18 : getr R4 (reg 10) = getr R3 (reg 8)),
    forall (EX19 : getr R4 (reg 11) = getr R3 (reg 9)),
    forall (EX20 : getr R4 (reg 12) = Z_to_bv 64 895872),
    forall (EX21 : L5.u8_at RSEGS M11 6361073 1),
    forall (EX : L5.u8_at RSEGS M11 6361072 1),
    forall (KS4 : forall x : nat, In x cs_all -> getr R4 (reg x) = getr R3 (reg x)),
    forall (R4_10 : getr R4 (reg 10) = Z_to_bv 64 obj),
    forall (R4_11 : getr R4 (reg 11) = Z_to_bv 64 22),
    forall (VPT : L5.u64_at RSEGS M11 895872 877064),
    forall (EX8 : forall x : nat, In x KS_ue1c1 -> getr R5 (reg x) = getr R4 (reg x)),
    forall (EX9 : getr R5 (reg 1) = Z_to_bv 64 731848),
    forall (EX10 : getr R5 (reg 2) = Z_to_bv 64 (Sp - 32 - 1184)),
    forall (EX22 : getr R5 (reg 8) = Z_to_bv 64 (Sp - 32 - 56)),
    forall (EX23 : getr R5 (reg 9) = Z_to_bv 64 (Sp - 32 - 1168)),
    forall (EX24 : getr R5 (reg 10) = Z_to_bv 64 22),
    forall (EX25 : getr R5 (reg 11) = Z_to_bv 64 (Sp - 32 - 1168)),
    forall (EX26 : getr R5 (reg 12) = Z_to_bv 64 1024),
    forall (EX27 : getr R5 (reg 13) = Z_to_bv 64 732232),
    forall (EX28 : getr R5 (reg 18) = Z_to_bv 64 6363236),
    forall (EX29 : getr R5 (reg 19) = Z_to_bv 64 22),
    forall (EX30 : L5.u64_at RSEGS M11 (Sp - 32 - 144) (bv_unsigned (getr R4 (reg 20)))),
    forall (EX31 : L5.u64_at RSEGS M11 (Sp - 32 - 136) (bv_unsigned (getr R4 (reg 19)))),
    forall (EX32 : L5.u64_at RSEGS M11 (Sp - 32 - 128) 22),
    forall (EX33 : L5.u64_at RSEGS M11 (Sp - 32 - 120) obj),
    forall (EX34 : L5.u64_at RSEGS M11 (Sp - 32 - 112) 895872),
    forall (EX39 : L5.u64_at RSEGS M11 (Sp - 32 - 32) 2147450880),
    forall (EX40 : L5.u64_at RSEGS M11 (Sp - 32 - 24) 22),
    forall (EX41 : L5.u64_at RSEGS M11 (Sp - 32 - 16) obj),
    forall (EX42 : L5.u64_at RSEGS M11 (Sp - 32 - 8) 584396),
    forall (mR10 : getr R6 (reg 10) = Z_to_bv 64 0),
    forall (RP6 : regs_preserved R5 R6),
    forall (EX43 : forall x : nat, In x KS_ue1c2 -> getr R7 (reg x) = getr R6 (reg x)),
    forall (EX44 : getr R7 (reg 1) = Z_to_bv 64 731928),
    forall (EX45 : getr R7 (reg 10) = Z_to_bv 64 (Sp - 32 - 1168)),
    forall (EX6 : L5.u32_at RSEGS M11 6363236 (bv_unsigned (getr R6 (reg 20)))),
    forall (sR10 : getr R8 (reg 10) = Z_to_bv 64 16),
    forall (RP8 : regs_preserved R7 R8),
    forall (EX47 : forall x : nat, In x KS_ue1c3 -> getr R9 (reg x) = getr R8 (reg x)),
    forall (EX48 : getr R9 (reg 1) = Z_to_bv 64 732032),
    forall (EX49 : getr R9 (reg 10) = Z_to_bv 64 (Sp - 32 - 55)),
    forall (EX50 : getr R9 (reg 11) = Z_to_bv 64 (Sp - 32 - 1168)),
    forall (EX51 : getr R9 (reg 12) = Z_to_bv 64 16),
    forall (EX52 : getr R9 (reg 18) = Z_to_bv 64 16),
    forall (EX53 : getr R9 (reg 19) = Z_to_bv 64 (Sp - 32 - 55)),
    forall (EX46 : L5.u8_at RSEGS M11 (Sp - 32 - 56) 32),
    forall (HMM : amemcpy_spec_at L ar SCFG HI 385868 false),
    forall (mvR10 : getr R10 (reg 10) = Z_to_bv 64 (Sp - 32 - 55)),
    forall (RP10 : regs_preserved R9 R10),
    forall (EX55 : forall x : nat, In x KS_ue1c4 -> getr R11 (reg x) = getr R10 (reg x)),
    forall (EX56 : getr R11 (reg 1) = Z_to_bv 64 731448),
    forall (EX57 : getr R11 (reg 2) = Z_to_bv 64 (Sp - 32 - 112)),
    forall (EX58 : getr R11 (reg 8) = Z_to_bv 64 obj),
    forall (EX59 : getr R11 (reg 9) = Z_to_bv 64 (Sp - 32 - 55)),
    forall (EX60 : getr R11 (reg 10) = Z_to_bv 64 (Sp - 32 - 55)),
    forall (EX61 : getr R11 (reg 11) = Z_to_bv 64 (Sp - 32 - 56)),
    forall (EX62 : getr R11 (reg 18) = Z_to_bv 64 22),
    forall (EX63 : getr R11 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R4 (reg 19)))),
    forall (EX64 : getr R11 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R4 (reg 20)))),
    forall (EX65 : L5.u64_at RSEGS M11 obj 876464),
    forall (EX66 : L5.u64_at RSEGS M11 (Sp - 32 - 104) (bv_unsigned (getr R4 (reg 19)))),
    forall (EX67 : L5.u64_at RSEGS M11 (Sp - 32 - 96) 22),
    forall (EX68 : L5.u64_at RSEGS M11 (Sp - 32 - 88) obj),
    forall (EX69 : L5.u64_at RSEGS M11 (Sp - 32 - 80) 895872),
    forall (EX70 : L5.u64_at RSEGS M11 (Sp - 32 - 72) 734968),
    forall (EX71 : L5.u8_at RSEGS M11 (Sp - 32 - 39) 0),
    forall (CI11 : cinv L ar HI M model A LB FF Sp SCR XW [(u, 160)] M11 model11 LK (adebit L cr 160) A2),
    forall (FL5 : fl = true -> L5.u8_at RSEGS M11 6363190 0),
    forall (FL3 : fl = true -> L5.u8_at RSEGS M11 6363188 0),
    forall (FL1 : fl = true -> L5.u8_at RSEGS M11 6363186 0),
    forall (AUXV : forall j : nat, (j < 20)%nat -> L5.u64_at RSEGS M11 (av + 8 * Z.of_nat j) (nth j (L5USA.auxv20A uid rnd hw) 0)),
    forall (RDS : rdn RSEGS M11 (Z_to_bv 64 (Sp - 32 - 55)) 16 = Some (firstn 16 (map (Z_to_bv 8) EINVAL_MSG))),
    forall (IC3 : L5.img_clear M11 895872 (895872 + 8)),
    forall (IC2 : L5.img_clear M11 895824 895856),
    forall (IC1 : L5.img_clear M11 65536 884736),
  srealizes RSEGS SCFG (cfg (fx:=fx11) R11 319024 M11 model11) K.
Proof.
  intros.
  pose proof (cinv_num L ar HI M model A LB FF Sp SCR XW _ _ _ _ _ _ CI11) as (_ & SLO11 & SHI11 & SPT11).
  (* [comment removed for export] *)
  pose proof (rdn_snoc0 M11 (Sp - 32 - 55) (firstn 16 (map (Z_to_bv 8) EINVAL_MSG)) RDS) as RD17.
  change (Z.of_nat (length (firstn 16 (map (Z_to_bv 8) EINVAL_MSG)))) with 16 in RD17. replace (Sp - 32 - 55 + 16) with (Sp - 32 - 39) in RD17 by (clear; lia). match goal with H : L5.u8_at RSEGS M11 (Sp - 32 - 39) 0 |- _ => specialize (RD17 H) end.
  change (length (firstn 16 (map (Z_to_bv 8) EINVAL_MSG)) + 1)%nat with 17%nat in RD17.
  set (msg17 := firstn 16 (map (Z_to_bv 8) EINVAL_MSG) ++ [Z_to_bv 8 0]) in *.
  destruct (rdn_ext M11 (Sp - 32 - 55) msg17 6 RD17) as (rest & Lrest & RDB).
  { apply (astk_defined ar M11 Sp SCR). exact (proj1 (proj2 (proj2 (proj2 (proj2 CI11))))). change (Z.of_nat (length msg17)) with 17. clear - HSCR; lia. change (Z.of_nat (length msg17)) with 17. clear; lia. }
  { clear - SPLO; lia. } { change (Z.of_nat (length msg17)) with 17. clear - SPHI; lia. }
  assert (LB23 : Z.of_nat (length (msg17 ++ rest)) = 23) by (rewrite length_app, Lrest; reflexivity).
  apply (CSTRLEN fx11 R11 (Sp - 32 - 55) 16 (msg17 ++ rest) (Sp - 32 - 112) 731448 K CI11 HK HS0);
    [ rk | rk | split; [clear; lia | reflexivity] | rk | rewrite HTP; rk | apply mod16_sub; [exact ALS | reflexivity] | clear - HSCR; lia | clear; lia
    | clear - SPLO; lia | rewrite LB23; clear - SPHI; lia | clear; lia
    | replace (length (msg17 ++ rest)) with (length msg17 + 6)%nat by (rewrite length_app, Lrest; reflexivity); exact RDB
    | rewrite LB23 | reflexivity | | left; rewrite LB23; clear - SPHI; lia | exact IC1
    | apply (aacc_stack L ar C HI HIok M model A LB FF Sp SCR XW _ _ _ _ _ _ _ _ CI11 SCR8); [clear - HSCR; lia | clear - SHI11; lia]
    | apply app_rng_stack; [clear - SPT11; lia | clear - SLO11 HS0 HSCR; lia | clear - SHI11; lia] | ].
  { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - ALS. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  { intros j Hj. change (Z.to_nat 16) with 16%nat in Hj. do 16 (destruct j as [|j]; [intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate E|]). exfalso. clear - Hj. lia. }
  intros fx12 R12 M12 model12 sR12 RP12 CI12 AG.
  carry M11 M12 AG sd_call. clear AG rest Lrest LB23 SLO11 SHI11 SPT11.
  (* [comment removed for export] *)
  pose proof (ue1c5_conc HFILL HCOPY HTLS fx12 R12 (mrestrict (ahid A2 model12) M12) (fun j => match j with 2%nat => Sp - 32 | 10%nat => obj | _ => 0 end)) as P. cbn beta iota in P.
  piece_step CI12 XWIMG P (fun a => Sp - 32 - 192 <= a < Sp - 32 - 192 + 80) fx13 R13 M13 model13 CI13.
  destruct (L5OMA.acredit_for_take L (adebit L cr 160) 1 41 41 LY2 CRF1 ltac:(clear; lia) ltac:(clear; lia)) as (ACR2 & _).
  apply (CMALLOC fx13 R13 41 (Sp - 32 - 128) 859152 K CI13 HK HS0); [ rk | clear; lia | exact ACR2 | rk | split; [clear; lia | reflexivity] | rk | rewrite HTP; rk
    | apply mod16_sub; [exact ALS | reflexivity] | clear - HSCR; lia | clear; lia | ].
  intros fx14 R14 M14 model14 A14 ref mR14 RP14 CI14 AG.
  carry M13 M14 AG sd_call. clear AG.
  (* [comment removed for export] *)
  assert (InR : In (ref, 41) ([(ref, 41); (u, 160)] ++ LB)) by (left; reflexivity).
  pose proof (cv_blk L ar C HI LY HIok M model A LB FF Sp SCR XW _ _ _ _ _ _ CI14 ref 41 InR) as (BRr & _ & _).
  pose proof (aio_small_high _ _ _ _ _ HIok _ _ _ _ _ _ _ (proj1 CI14) (ref, 41) InR ltac:(cbn [snd]; clear; lia)) as HIGHr. cbn [fst] in HIGHr. unfold BIGSHADOW_HI in HIGHr.
  assert (APRT : ref + 41 <= u \/ u + 160 <= ref).
  { pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ (proj1 CI14)) as (WB & _). destruct (WB (ref, 41) InR) as (_ & _ & _ & _ & BA & _). cbn [fst snd] in BA.
    cbn [app lb_remove fst] in BA. rewrite Z.eqb_refl in BA. specialize (BA (u, 160) ltac:(left; reflexivity)). cbn [fst snd] in BA. clear - BA; lia. }
  assert (RF16 : ref mod 16 = 0) by exact (proj1 (proj2 (proj2 BRr))).
  assert (NUM3 : numf ((ahl_ceil ar + 4096 + SCR <= Sp /\ Sp <= ar_sptop ar /\ 140735340871680 <= ar_sptop ar <= 2 ^ 47 /\ 69632 <= SCR /\ 0 <= SCR)
                      /\ (0 <= Sp - 32 < 2 ^ 64 /\ 140735332552704 <= Sp - 32 /\ Sp - 32 <= 140737488355264)
                      /\ (ar_sptop ar <= av /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47)
                      /\ (obj = u + 128 /\ 0 <= obj < 2 ^ 64 /\ 17594333495424 <= obj <= 140737479966720 /\ obj + 32 <= ahl_ceil ar)
                      /\ (17594333495296 <= ref /\ ref + 41 <= ahl_ceil ar /\ (ref + 41 <= u \/ u + 160 <= ref)))).
  { unfold numf in *. clear - NUM BRr HIGHr APRT. lia. }
  clear NUM. rename NUM3 into NUM. clear BRr HIGHr APRT InR.
  (* [comment removed for export] *)
  pose proof (ue1c6_conc HFILL HCOPY HTLS fx14 R14 (mrestrict (ahid A14 model14) M14) (fun j => match j with 2%nat => Sp - 32 | 10%nat => obj | 37%nat => ref | _ => 0 end)) as P. cbn beta iota in P.
  piece_step CI14 XWIMG P (fun a => Sp - 32 - 192 <= a < Sp - 32 - 192 + 64 \/ ref + 0 <= a < ref + 0 + 20) fx15 R15 M15 model15 CI15.
  pose proof (cinv_num L ar HI M model A LB FF Sp SCR XW _ _ _ _ _ _ CI15) as (_ & SLO15 & SHI15 & SPT15).
  assert (HMC : amemcpy_spec_at L ar SCFG HI 0x5e350 false). { pose proof (aic_memcpy_libc _ _ _ _ _ ICok) as X. unfold amemcpy_libc_spec in X. rewrite (aicl_memcpy IL ILY) in X. exact X. }
  assert (InR : In (ref, 41) ([(ref, 41); (u, 160)] ++ LB)) by (left; reflexivity).
  apply (CMEMCPY 0x5e350 false _ _ _ _ _ _ fx15 R15 (ref + 24) (Sp - 32 - 55) 17 msg17 (Sp - 32 - 112) 731492 K HMC CI15 HK HS0);
    [ rk | rk | rk | clear; lia | rk | split; [clear; lia | reflexivity] | rk | rewrite HTP; rk | apply mod16_sub; [exact ALS | reflexivity] | clear - HSCR; lia | clear; lia
    | right; exists ref, 41; split; [left; reflexivity | clear; lia]
    | apply (aacc_xblk L ar C HI LY HIok M model A LB FF Sp SCR XW _ _ _ _ _ _ ref 41 _ _ CI15 InR); clear; lia
    | apply (app_rng_block L ar C HI HIok _ _ _ _ _ _ _ ref 41 _ _ (proj1 CI15) InR); clear; lia
    | apply (aacc_stack L ar C HI HIok M model A LB FF Sp SCR XW _ _ _ _ _ _ _ _ CI15 SCR8); [clear - HSCR; lia | clear - SHI15; lia]
    | clear - SPLO SPHI; lia
    | apply app_rng_stack; [clear - SPT15; lia | clear - SLO15 HS0 HSCR; lia | clear - SHI15; lia]
    | left; clear - SPLO SPHI; lia
    | exact RD17 | intros _; unfold numf in NUM; clear - NUM; lia | ].
  intros fx16 R16 M16 model16 mR16 RP16 CI16 BYTES AG.
  carry M15 M16 AG sd_call. clear AG BYTES SLO15 SHI15 SPT15 InR.
  (* [comment removed for export] *)
  pose proof (ue1c7_conc HFILL HCOPY HTLS fx16 R16 (mrestrict (ahid A14 model16) M16)
                (fun j => match j with 2%nat => Sp - 32 | 10%nat => obj | 37%nat => ref | 40%nat => U R16 10 | 41%nat => bv_unsigned (getr R4 (reg 19)) | _ => 0 end)) as P. cbn beta iota in P.
  piece_step CI16 XWIMG P (fun a => Sp - 32 - 176 <= a < Sp - 32 - 176 + 64 \/ obj + 0 <= a < obj + 0 + 32) fx17 R17 M17 model17 CI17.
  apply (CHNR fx17 R17 (Sp - 32) 584400 K CI17 HK HS0 SCR8); [ rk | split; [clear; lia | reflexivity] | rk | rewrite HTP; rk | exact ALS | clear - HSCR; lia | clear; lia | ].
  intros fx18 R18 M18 model18 RP18 CI18 AG.
  carry M17 M18 AG sd_call. clear AG.
  (* [comment removed for export] *)
  pose proof (ue1c8_conc HFILL HCOPY HTLS fx18 R18 (mrestrict (ahid A14 model18) M18) (fun j => match j with 2%nat => Sp - 32 | 10%nat => obj | 40%nat => U R18 10 | _ => 0 end)) as P. cbn beta iota in P.
  piece_step CI18 XWIMG P (fun a => Sp - 32 - 64 <= a < Sp - 32 - 64 + 64) fx19 R19 M19 model19 CI19.
  subst msg17. tidy CI19.
  apply (L5BE1S4.e1_s4 L ar C IL HI LY ILY HIok ICok HFILL HCOPY HTLS UNWL R M model K LB FF LK cr A Sp SCR s0v s2v gd fl av uid rnd canary hw errv R1 R2 A2 u obj R3 R4 R5 R6 R7 R8 R9 R10 R11 M19 R12 R13 R14 A14 ref R15 R16 R17 R18 fx19 R19 model19); assumption.
Qed.

End WithIface.
End SCFG_1.
End L5BE1S3.
