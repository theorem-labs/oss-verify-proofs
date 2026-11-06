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
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5ParseSpecsAB0 L5OpmodSpecsAB0 L5DivSpecsAB0 L5UnwindSpecsAB0 XIcptAB0 XIcptAs0KitB0 L5BUnwK L5BUnwK2 L5BE1K L5BE1P1 L5BE1P2 L5BE1P3 L5BE1P4 L5BE1P5 L5BE1S3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Set Printing Width 100000. Set Printing Depth 100000.

Module L5BE1S2.
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

Lemma e1_s2 :
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (FF : list fframe) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (Sp : Z) (SCR : Z) (s0v : Z) (s2v : Z) (gd : bool) (fl : bool) (av : Z) (uid : Z) (rnd : Z) (canary : Z) (hw : Z) (M1 : word -> option byte) (M2 : word -> option byte) (M3 : word -> option byte) (M4 : word -> option byte) (errv : Z) (fx1 : FPState) (R1 : bvmap 5 word) (model1 : Model) (fx2 : FPState) (R2 : bvmap 5 word) (model2 : Model) (A2 : list (Z * Z)) (u : Z) (obj : Z) (fx3 : FPState) (R3 : bvmap 5 word) (model3 : Model) (fx4 : FPState) (R4 : bvmap 5 word) (model4 : Model),
    forall (G2 : getr R (reg 2) = Z_to_bv 64 (Sp - 32)),
    forall (G3 : getr R (reg 3) = Z_to_bv 64 67584),
    forall (G4 : getr R (reg 4) = Z_to_bv 64 6363400),
    forall (G9 : getr R (reg 9) = Z_to_bv 64 22),
    forall (G18 : getr R (reg 18) = Z_to_bv 64 SB),
    forall (S32 : Sp mod 32 = 0),
    forall (C8 : L5.u64_at RSEGS M4 (Sp - 8) 582372),
    forall (C16 : L5.u64_at RSEGS M4 (Sp - 16) s0v),
    forall (C24 : L5.u64_at RSEGS M4 (Sp - 24) Sp),
    forall (C32 : L5.u64_at RSEGS M4 (Sp - 32) s2v),
    forall (S0R : 0 <= s0v < 2 ^ 64),
    forall (S2R : 0 <= s2v < 2 ^ 64),
    forall (EC0 : L5.u64_at RSEGS M4 6360520 0),
    forall (EU0 : L5.u32_at RSEGS M4 6360528 0),
    forall (TDL : L5.u64_at RSEGS M4 6363352 6495184),
    forall (MSG0 : L5.u64_at RSEGS M4 6495224 0),
    forall (ERR : L5.u32_at RSEGS M4 6363236 errv),
    forall (ERRR : 0 <= errv < 2 ^ 64),
    forall (CAN : L5.u64_at RSEGS M4 6494536 canary),
    forall (AUXP : L5.u64_at RSEGS M4 6495136 av),
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
    forall (FL0 : L5.u8_at RSEGS M4 6363185 (if fl then 1 else 0)),
    forall (FL2 : L5.u8_at RSEGS M4 6363187 (if fl then 1 else 0)),
    forall (FL4 : L5.u8_at RSEGS M4 6363189 (if fl then 1 else 0)),
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
    forall (CI0 : cinv L ar HI M model A LB FF Sp SCR XW [] M model LK cr A),
    forall (EX0 : forall x : nat, In x KS_ue1a1 -> getr R1 (reg x) = getr R (reg x)),
    forall (EX1 : getr R1 (reg 1) = Z_to_bv 64 727044),
    forall (EX2 : getr R1 (reg 2) = Z_to_bv 64 (Sp - 32 - 48)),
    forall (EX3 : getr R1 (reg 8) = Z_to_bv 64 160),
    forall (EX4 : getr R1 (reg 10) = Z_to_bv 64 16),
    forall (EX5 : getr R1 (reg 11) = Z_to_bv 64 160),
    forall (CI1 : cinv L ar HI M model A LB FF Sp SCR XW [] M1 model1 LK cr A),
    forall (AH : ahid A model1 = ahid A model),
    forall (ACR1 : acredit_ok L cr 160),
    forall (CRF1 : L5OMA.acredit_for L (adebit L cr 160) 1 41),
    forall (RP2 : regs_preserved R1 R2),
    forall (CI2 : cinv L ar HI M model A LB FF Sp SCR XW [(u, 160)] M2 model2 LK (adebit L cr 160) A2),
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
    forall (EX17 : L5KA.zeros_at M4 (obj - 128) 160),
    forall (CI3 : cinv L ar HI M model A LB FF Sp SCR XW [(u, 160)] M3 model3 LK (adebit L cr 160) A2),
    forall (AH0 : ahid A2 model3 = ahid A2 model2),
    forall (Z72 : L5KA.zeros_at M4 (obj - 72) 4),
    forall (EX7 : getr R4 (reg 1) = Z_to_bv 64 584380),
    forall (EX18 : getr R4 (reg 10) = getr R3 (reg 8)),
    forall (EX19 : getr R4 (reg 11) = getr R3 (reg 9)),
    forall (EX20 : getr R4 (reg 12) = Z_to_bv 64 895872),
    forall (EX21 : L5.u8_at RSEGS M4 6361073 1),
    forall (EX : L5.u8_at RSEGS M4 6361072 1),
    forall (CI4 : cinv L ar HI M model A LB FF Sp SCR XW [(u, 160)] M4 model4 LK (adebit L cr 160) A2),
    forall (AH1 : ahid A2 model4 = ahid A2 model3),
    forall (FL1 : fl = true -> L5.u8_at RSEGS M4 6363186 0),
    forall (FL3 : fl = true -> L5.u8_at RSEGS M4 6363188 0),
    forall (FL5 : fl = true -> L5.u8_at RSEGS M4 6363190 0),
    forall (AUXV : forall j : nat, (j < 20)%nat -> L5.u64_at RSEGS M4 (av + 8 * Z.of_nat j) (nth j (L5USA.auxv20A uid rnd hw) 0)),
    forall (IC1 : L5.img_clear M4 65536 884736),
    forall (IC2 : L5.img_clear M4 895824 895856),
    forall (IC3 : L5.img_clear M4 895872 (895872 + 8)),
    forall (KS4 : forall x : nat, In x cs_all -> getr R4 (reg x) = getr R3 (reg x)),
  srealizes RSEGS SCFG (cfg (fx:=fx4) R4 584392 M4 model4) K.
Proof.
  intros.
  assert (R4_10 : getr R4 (reg 10) = Z_to_bv 64 obj) by (match goal with H : getr R4 (reg 10) = getr R3 (reg 8) |- _ => rewrite H end; rk).
  assert (R4_11 : getr R4 (reg 11) = Z_to_bv 64 22) by (match goal with H : getr R4 (reg 11) = getr R3 (reg 9) |- _ => rewrite H end; rk).
  assert (E10 : bv_unsigned (getr R4 (reg 10)) = obj) by (rewrite R4_10; apply L5.unsigned_lit; exact OBR0).
  assert (VPT : L5.u64_at RSEGS M4 895872 877064).
  { unfold L5.u64_at. rewrite (rdn_img M4 895872 (895872 + 8) IC3 8 895872) by (clear; lia). vm_compute. f_equal. repeat (apply (f_equal2 cons); [apply bv_eq; reflexivity|]). reflexivity. }
  (* [comment removed for export] *)
  pose proof (ue1c1_conc HFILL HCOPY HTLS fx4 R4 (mrestrict (ahid A2 model4) M4) (fun j => match j with 2%nat => Sp - 32 | 35%nat => errv | _ => 0 end)) as P. cbn beta iota in P.
  rewrite ?E10 in P.
  piece_step CI4 XWIMG P (fun a => Sp - 32 - 1248 <= a < Sp - 32 - 1248 + 1248) fx5 R5 M5 model5 CI5.
  assert (E18 : bv_unsigned (getr R4 (reg 18)) = 2147450880). { apply (U_of R4 18). rk. clear; lia. }
  assert (E49 : bv_unsigned (getr R4 (reg 9)) = 22). { apply (U_of R4 9). rk. clear; lia. }
  assert (E48 : bv_unsigned (getr R4 (reg 8)) = obj). { apply (U_of R4 8). rk. exact OBR0. }
  rewrite ?E18, ?E49, ?E48 in *. clear E18 E49 E48 E10.
  (* [comment removed for export] *)
  apply (CSTRERROR fx5 R5 (Sp - 32 - 1184) 731848 K CI5 HK HS0 SCR8); [ rk | rk | rk | rk | split; [clear; lia | reflexivity] | rk | rewrite HTP; rk
    | apply mod16_sub; [exact ALS | reflexivity] | clear - HSCR; lia | clear; lia | exact TDL | exact MSG0 | exact IC1 | ].
  intros fx6 R6 M6 model6 mR10 RP6 CI6 RDN AG.
  carry M5 M6 AG sd_call. clear AG.
  assert (B0 : L5.u8_at RSEGS M6 (Sp - 32 - 1184 + 16) 73) by (exact (rdn_head M6 _ 16 _ _ RDN)).
  (* [comment removed for export] *)
  pose proof (ue1c2_conc HFILL HCOPY HTLS fx6 R6 (mrestrict (ahid A2 model6) M6) (fun j => match j with 2%nat => Sp - 32 | 10%nat => obj | _ => 0 end)) as P. cbn beta iota in P.
  piece_step CI6 XWIMG P (fun a => Sp - 32 - 1248 <= a < Sp - 32 - 1248 + 64 \/ 6363236 <= a < 6363236 + 4) fx7 R7 M7 model7 CI7.
  clear B0.
  (* [comment removed for export] *)
  pose proof (cinv_num L ar HI M model A LB FF Sp SCR XW _ _ _ _ _ _ CI7) as (_ & SLO7 & SHI7 & SPT7).
  destruct (rdn_ext M7 (Sp - 32 - 1184 + 16) (map (Z_to_bv 8) EINVAL_MSG) 7 RDN) as (rest & Lrest & RDB).
  { apply (astk_defined ar M7 Sp SCR). exact (proj1 (proj2 (proj2 (proj2 (proj2 CI7))))). cbn [length map EINVAL_MSG Z.of_nat Pos.of_succ_nat Pos.succ]. clear - HSCR; lia.
    cbn [length map EINVAL_MSG Z.of_nat Pos.of_succ_nat Pos.succ]. clear; lia. }
  { clear - SPLO; lia. } { cbn [length map EINVAL_MSG Z.of_nat Pos.of_succ_nat Pos.succ]. clear - SPHI; lia. }
  assert (LB24 : Z.of_nat (length (map (Z_to_bv 8) EINVAL_MSG ++ rest)) = 24) by (rewrite length_app, Lrest; reflexivity).
  apply (CSTRLEN fx7 R7 (Sp - 32 - 1184 + 16) 16 (map (Z_to_bv 8) EINVAL_MSG ++ rest) (Sp - 32 - 1184) 731928 K CI7 HK HS0);
    [ rk | rk | split; [clear; lia | reflexivity] | rk | rewrite HTP; rk | apply mod16_sub; [exact ALS | reflexivity] | clear - HSCR; lia | clear; lia
    | clear - SPLO; lia | rewrite LB24; clear - SPHI; lia | clear; lia
    | replace (length (map (Z_to_bv 8) EINVAL_MSG ++ rest)) with (length (map (Z_to_bv 8) EINVAL_MSG) + 7)%nat by (rewrite length_app, Lrest; reflexivity); exact RDB
    | rewrite LB24 | reflexivity | | left; rewrite LB24; clear - SPHI; lia | exact IC1
    | apply (aacc_stack L ar C HI HIok M model A LB FF Sp SCR XW _ _ _ _ _ _ _ _ CI7 SCR8); [clear - HSCR; lia | clear - SHI7; lia]
    | apply app_rng_stack; [clear - SPT7; lia | clear - SLO7 HS0 HSCR; lia | clear - SHI7; lia] | ].
  { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - ALS. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  { intros j Hj. change (Z.to_nat 16) with 16%nat in Hj. do 16 (destruct j as [|j]; [intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate E|]). exfalso. clear - Hj. lia. }
  intros fx8 R8 M8 model8 sR10 RP8 CI8 AG.
  carry M7 M8 AG sd_call. clear AG rest Lrest LB24 SLO7 SHI7 SPT7.
  (* [comment removed for export] *)
  pose proof (ue1c3_conc HFILL HCOPY HTLS fx8 R8 (mrestrict (ahid A2 model8) M8) (fun j => match j with 2%nat => Sp - 32 | 10%nat => obj | _ => 0 end)) as P. cbn beta iota in P.
  piece_step CI8 XWIMG P (fun a => Sp - 32 - 1248 <= a < Sp - 32 - 1248 + 64 \/ Sp - 32 - 56 <= a < Sp - 32 - 56 + 1) fx9 R9 M9 model9 CI9.
  pose proof (cinv_num L ar HI M model A LB FF Sp SCR XW _ _ _ _ _ _ CI9) as (_ & SLO9 & SHI9 & SPT9).
  pose proof (rdn_firstn M9 16 17 _ _ RDN ltac:(clear; lia)) as RD16.
  assert (HMM : amemcpy_spec_at L ar SCFG HI 0x5e34c false). { pose proof (aic_memmove_libc _ _ _ _ _ ICok) as X. unfold amemmove_libc_spec in X. rewrite (aicl_memmove IL ILY) in X. exact X. }
  apply (CMEMCPY 0x5e34c false _ _ _ _ _ _ fx9 R9 (Sp - 32 - 55) (Sp - 32 - 1184 + 16) 16 (firstn 16 (map (Z_to_bv 8) EINVAL_MSG)) (Sp - 32 - 1184) 732032 K HMM CI9 HK HS0);
    [ rk | rk | rk | clear; lia | rk | split; [clear; lia | reflexivity] | rk | rewrite HTP; rk | apply mod16_sub; [exact ALS | reflexivity] | clear - HSCR; lia | clear; lia
    | left; clear; lia
    | apply (aacc_stack L ar C HI HIok M model A LB FF Sp SCR XW _ _ _ _ _ _ _ _ CI9 SCR8); [clear - HSCR; lia | clear - SHI9; lia]
    | apply app_rng_stack; [clear - SPT9; lia | clear - SLO9 HS0 HSCR; lia | clear - SHI9; lia]
    | apply (aacc_stack L ar C HI HIok M model A LB FF Sp SCR XW _ _ _ _ _ _ _ _ CI9 SCR8); [clear - HSCR; lia | clear - SHI9; lia]
    | clear - SPLO SPHI; lia
    | apply app_rng_stack; [clear - SPT9; lia | clear - SLO9 HS0 HSCR; lia | clear - SHI9; lia]
    | left; clear - SPLO SPHI; lia
    | exact RD16 | intros _; clear; lia | ].
  intros fx10 R10 M10 model10 mvR10 RP10 CI10 BYTES AG.
  carry M9 M10 AG sd_call. clear AG.
  pose proof (rdn_of_copied M10 (Sp - 32 - 55) (firstn 16 (map (Z_to_bv 8) EINVAL_MSG)) BYTES ltac:(clear - SPLO; lia) ltac:(change (Z.of_nat (length (firstn 16 (map (Z_to_bv 8) EINVAL_MSG)))) with 16; clear - SPHI; lia)) as RDS.
  change (length (firstn 16 (map (Z_to_bv 8) EINVAL_MSG))) with 16%nat in RDS.
  clear BYTES RD16 SLO9 SHI9 SPT9.
  (* [comment removed for export] *)
  pose proof (ue1c4_conc HFILL HCOPY HTLS fx10 R10 (mrestrict (ahid A2 model10) M10)
                (fun j => match j with 2%nat => Sp - 32 | 10%nat => obj | 40%nat => U R10 10 | 41%nat => bv_unsigned (getr R4 (reg 19)) | 42%nat => bv_unsigned (getr R4 (reg 20)) | _ => 0 end)) as P. cbn beta iota in P.
  piece_step CI10 XWIMG P (fun a => Sp - 32 - 1248 <= a < Sp - 32 - 1248 + 64 \/ obj + 0 <= a < obj + 0 + 8 \/ Sp - 32 - 104 <= a < Sp - 32 - 104 + 8 \/ Sp - 32 - 96 <= a < Sp - 32 - 96 + 8
                                     \/ Sp - 32 - 88 <= a < Sp - 32 - 88 + 8 \/ Sp - 32 - 80 <= a < Sp - 32 - 80 + 8 \/ Sp - 32 - 72 <= a < Sp - 32 - 72 + 8 \/ Sp - 32 - 39 <= a < Sp - 32 - 39 + 1) fx11 R11 M11 model11 CI11.
  clear RDN. tidy CI11.
  apply (L5BE1S3.e1_s3 L ar C IL HI LY ILY HIok ICok HFILL HCOPY HTLS UNWL R M model K LB FF LK cr A Sp SCR s0v s2v gd fl av uid rnd canary hw errv R1 R2 A2 u obj R3 R4 M11 R5 R6 R7 R8 R9 R10 fx11 R11 model11); assumption.
Qed.

End WithIface.
End SCFG_1.
End L5BE1S2.
