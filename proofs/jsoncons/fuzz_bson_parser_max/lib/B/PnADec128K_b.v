(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnDecFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAXD_b PnADec128Defs_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADK.
Import L5A. Import L5CA. Import L5SAR.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation berr_ok := (PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN).
Abbreviation base_ok := (PMSTA.base_okA RSEGS PMA.AD).

(* [comment removed for export] *)
Definition SCR : Z := 18432.
Definition ocell (S : Z) (a : Z) : Prop := S - 104 <= a < S.
Definition own (S : Z) (R : bvmap 5 word) (r : Z) (M : mem) : Prop := PNADD.saves R S r M.
Lemma own_agree S R r M1 M1' : 0 <= S - 104 -> S <= 2 ^ 64 ->
  own S R r M1 -> (forall a, ocell S a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> own S R r M1'.
Proof.
  intros H1 H2 OW AG. unfold own, PNADD.saves, ocell in *.
  destruct OW as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
  repeat split; (eapply L5C.u64_at_agree; [| | | eassumption]); first [ (intros i Hi; apply AG; lia) | lia ].
Qed.

(* [comment removed for export] *)
Record dve : Type := DVE {
  vR : bvmap 5 word; vr : Z; vsp : Z; vfirst : Z; vvp : Z; vax : PNST.bax;
  vLB : list (Z * Z); vFF : list fframe; vLK : list fframe; vAw : list (Z * Z); vcr : credit; vmodel : Model; vM : mem; vK : TSet;
  vF : Z; vfl : Z; vLK2 : list fframe; vM2 : mem; vmodel2 : Model }.

(* [comment removed for export] *)
Definition Wmid (E : dve) (a : Z) : Prop :=
  (vsp E - 240 <= a < vsp E - 176) \/ (vsp E - 168 <= a < vsp E - 160) \/ (vsp E - 136 <= a < vsp E - 104) \/ (vF E + 32 <= a < vF E + 504) \/ (PNADD.SH (vF E) + 22 <= a < PNADD.SH (vF E) + 64)
  \/ (vfirst E <= a < vfirst E + 42).

(* [comment removed for export] *)
Definition Wg (E : dve) (a : Z) : Prop :=
  (vsp E - 240 <= a < vsp E - 176) \/ (vsp E - 168 <= a < vsp E - 160) \/ (vsp E - 136 <= a < vsp E - 104) \/ (vF E + 32 <= a < vF E + 504) \/ (PNADD.SH (vF E) + 4 <= a < PNADD.SH (vF E) + 64)
  \/ (vfirst E <= a < vfirst E + 42).
Lemma Wg_of_Wmid E a : Wmid E a -> Wg E a.
Proof. unfold Wmid, Wg. lia. Qed.

Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Definition W (E : dve) : list L5.range := (vfirst E, 42) :: (if PNST.bax_dec (vax E) then [] else PNST.dec_W PMA.AD PMA.AN).
Definition FF' (E : dve) : list fframe := (vF E, 3, vsp E - 256 + 32) :: vFF E.

(* [comment removed for export] *)
Definition kont (E : dve) : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (ptr : Z),
    regs_preserved (vR E) R' -> getr R' 10%bv = Z_to_bv 64 ptr -> vfirst E <= ptr <= vfirst E + 42 ->
    L5.defined M' (vfirst E) 42 -> berr_ok M' (PNST.bax_add_dec (vax E)) ->
    L5CA.ahpres L ar (vLB E) (vFF E) (vsp E) SCR (W E) (vM E) M' ->
    model_rt (vmodel E) model' -> incl LK' (vLK E) -> incl (vAw E) Aw' -> L5CA.amodel_ok Aw' model' ->
    ri_inv HI (vLB E) (vFF E) LK' (vcr E) Aw' M' (vml_of model') ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' (vr E) M' model') (vK E).

(* [comment removed for export] *)
Record dkc (E : dve) : Prop := DKC {
  c_GEOM : PNADD.geom (vsp E) (vfirst E) (vvp E) (vF E) (vfl E);
  c_G : PMAUK.gctx L ar HI (vLB E) (vFF E) (vLK E) (vAw E) (vsp E) SCR (vsp E - 256) (vsp E - 104) (vsp E) (ocell (vsp E))
          (own (vsp E) (vR E) (vr E)) (vF E) (vfl E) 3 (vLK2 E) (vM2 E) (vmodel2 E) (vcr E) [];
  c_HH : ri_inv HI (vLB E) (vFF E) (vLK E) (vcr E) (vAw E) (vM E) (vml_of (vmodel E));
  c_K0 : vK E [];
  c_Rra : getr (vR E) (reg 1) = Z_to_bv 64 (vr E);
  c_RA : L5.ra_ok (vr E);
  c_Rsp : getr (vR E) (reg 2) = Z_to_bv 64 (vsp E);
  c_Rgp : getr (vR E) (reg 3) = Z_to_bv 64 (pa_gp PMA.AD);
  c_Rtp : getr (vR E) (reg 4) = Z_to_bv 64 (hl_tp L);
  c_ASTK : L5CA.astk ar (vM E) (vsp E) SCR;
  c_STKSH : shadow_zero (vM E) (vsp E - SCR) (SCR / 8);      (* [comment removed for export] *)
  c_FRM : PGSA.ffroomB PNRA.FCB 3 (vFF E) (vLK E);
  c_FRS : PMSPA.ffrsA (vFF E) (vsp E);
  c_BLK : exists B m, In (B, m) (vLB E) /\ B <= vfirst E /\ vfirst E + 42 <= B + m;
  c_VST : vsp E <= vvp E /\ vvp E + 16 <= ar_sptop ar;      (* [comment removed for export] *)
  c_KONT : kont E
}.

(* [comment removed for export] *)
Definition dsg (E : dve) (axc : PNST.bax) (Mc : mem) (modelc : Model) (LKc : list fframe) (Ac : list (Z * Z)) : Prop :=
  PMAUK.binv L ar HI (vM E) (vmodel E) (vLB E) (vFF E) (vLK E) (vAw E) (vsp E) SCR (vsp E - 256) (own (vsp E) (vR E) (vr E)) (vF E) 3
    (W E) [] Mc modelc LKc (vcr E) Ac
  /\ L5.defined Mc (vfirst E) 42 /\ PMSPA.accA Mc (vfirst E) 48
  /\ L5.defined Mc (vvp E) 16 /\ PMSPA.accA Mc (vvp E) 16
  /\ base_ok Mc /\ berr_ok Mc axc
  /\ L5.u64_at RSEGS Mc (vsp E - 144) (vF E) /\ L5.u64_at RSEGS Mc (vsp E - 176) (vfirst E + 42).

(* [comment removed for export] *)
Definition dst (E : dve) (Mc : mem) (modelc : Model) (LKc : list fframe) (Ac : list (Z * Z)) : Prop :=
  PMAUK.binv L ar HI (vM E) (vmodel E) (vLB E) (vFF E) (vLK E) (vAw E) (vsp E) SCR (vsp E - 256) (own (vsp E) (vR E) (vr E)) (vF E) 3
    (W E) [] Mc modelc LKc (vcr E) Ac
  /\ L5.defined Mc (vfirst E) 42 /\ PMSPA.accA Mc (vfirst E) 48
  /\ L5.defined Mc (vvp E) 16 /\ PMSPA.accA Mc (vvp E) 16
  /\ base_ok Mc /\ berr_ok Mc (PNST.bax_add_dec (vax E))
  /\ L5.u64_at RSEGS Mc (vsp E - 144) (vF E) /\ L5.u64_at RSEGS Mc (vsp E - 176) (vfirst E + 42) /\ L5KA.zeros_at Mc (PNADD.SH (vF E) + 4) 18.

(* [comment removed for export] *)
Definition dmem (E : dve) (MV : mem) : Prop :=
  PNADD.MIA (vR E) (vsp E) (vfirst E) (vr E) (vF E) (vfl E) MV
  /\ (exists lo hi, 0 <= lo < 2 ^ 64 /\ 0 <= hi < 2 ^ 64 /\ PNADD.vp_at MV (vvp E) lo hi)
  /\ L5.img_clear MV 65536 1282048 /\ L5.u64_at RSEGS MV 1283280 1219844
  /\ L5.u8_at RSEGS MV 0x6722e0 1 /\ L5.u8_at RSEGS MV 0x672300 1
  /\ PNST.sso_lit RSEGS MV 0x6722c8 8 /\ PNST.sso_lit RSEGS MV 0x6722e8 3.

Lemma sh6_in_blk first Bq Bm i : first mod 8 = 0 -> 0 <= Bq -> Bq <= first -> first + 42 <= Bq + Bm -> 0 <= i < 6 ->
  Bq / 8 + 2147450880 <= first / 8 + 2147450880 + i <= (Bq + Bm - 1) / 8 + 2147450880.
Proof.
  intros F8 B0 B1 B2 Hi.
  assert (E8 : first = 8 * (first / 8)) by (pose proof (Z.div_mod first 8 ltac:(lia)); lia).
  assert (L1 : Bq / 8 <= first / 8) by (apply Z.div_le_mono; lia).
  assert (L2 : first / 8 + 5 <= (Bq + Bm - 1) / 8) by (apply Z.div_le_lower_bound; lia).
  lia.
Qed.

Lemma bax_dec_add ax : PNST.bax_dec (PNST.bax_add_dec ax) = true.
Proof. destruct ax; reflexivity. Qed.

(* [comment removed for export] *)
Lemma geom_rng E : dkc E ->
  0 <= vsp E - 256 /\ vsp E <= 2 ^ 47 /\ 0 <= vfirst E /\ vfirst E + 48 <= 2 ^ 47 /\ 0 <= vvp E /\ vvp E + 16 <= 2 ^ 47 /\ 0 <= vF E /\ vF E + 512 <= 2 ^ 47
  /\ 0 <= PNADD.SH (vF E) /\ PNADD.SH (vF E) + 64 <= 2 ^ 47 /\ 0 <= PNADD.SH (vfirst E) /\ PNADD.SH (vfirst E) + 6 <= 2 ^ 47
  /\ 0 <= PNADD.SH (vvp E) /\ PNADD.SH (vvp E) + 2 <= 2 ^ 47.
Proof.
  intros X. pose proof (c_GEOM E X) as G. unfold PNADD.geom in G.
  destruct G as (S1 & _ & F1 & _ & _ & _ & _ & V1 & _ & _ & _ & _ & FF1 & _).
  unfold PNADD.SH, PNADD.SBv.
  assert (0 <= vF E / 8) by (apply Z.div_pos; lia). assert (vF E / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; lia).
  assert (0 <= vfirst E / 8) by (apply Z.div_pos; lia). assert (vfirst E / 8 <= 17592186044410) by (apply Z.div_le_upper_bound; lia).
  assert (0 <= vvp E / 8) by (apply Z.div_pos; lia). assert (vvp E / 8 <= 17592186044414) by (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma dsg_of_dst E Mc modelc LKc Ac : dst E Mc modelc LKc Ac -> dsg E (PNST.bax_add_dec (vax E)) Mc modelc LKc Ac.
Proof. intros (BI & DF & AF & DV & AV & BASE & ERR & C128 & C176 & ZSIG). unfold dsg. tauto. Qed.
Lemma dst_of_dsg E Mc modelc LKc Ac : dsg E (PNST.bax_add_dec (vax E)) Mc modelc LKc Ac -> L5KA.zeros_at Mc (PNADD.SH (vF E) + 4) 18 -> dst E Mc modelc LKc Ac.
Proof. intros (BI & DF & AF & DV & AV & BASE & ERR & C128 & C176) ZSIG. unfold dst. tauto. Qed.

(* [comment removed for export] *)
Definition gmem (E : dve) (MV : mem) : Prop :=
  (L5.writable RSEGS MV (vsp E - 256) 256 /\ L5.writable RSEGS MV (vfirst E) 42 /\ L5.writable RSEGS MV (vF E) 512 /\ L5.writable RSEGS MV (PNADD.SH (vF E)) 64
   /\ L5.writable RSEGS MV (vfl E) 1
   /\ L5.img_clear MV 1249280 1282048 /\ L5.u64_at RSEGS MV 1309752 2147450880 /\ L5.u32_at RSEGS MV 1309760 1
   /\ PNADD.saves (vR E) (vsp E) (vr E) MV /\ L5.u64_at RSEGS MV (vsp E - 144) (vF E) /\ L5.u64_at RSEGS MV (vsp E - 176) (vfirst E + 42) /\ L5.u64_at RSEGS MV (vF E + 504) (vfl E)
   /\ L5KA.zeros_at MV (PNADD.SH (vfirst E)) 6)
  /\ (exists lo hi, 0 <= lo < 2 ^ 64 /\ 0 <= hi < 2 ^ 64 /\ PNADD.vp_at MV (vvp E) lo hi)
  /\ L5.img_clear MV 65536 1282048 /\ L5.u64_at RSEGS MV 1283280 1219844 /\ L5.defined MV (vF E) 512.
Definition gvis (E : dve) (H : word -> bool) : Prop :=
  L5A.avis H (vsp E - 256) 256 /\ L5A.avis H (vfirst E) 42 /\ L5A.avis H (vF E) 512 /\ L5A.avis H (PNADD.SH (vF E)) 64 /\ L5A.avis H (PNADD.SH (vfirst E)) 6
  /\ (forall a n, 65536 <= a -> a + n <= 6905856 -> L5A.avis H a n).

Lemma gmem_of E (X : dkc E) axc Mc modelc LKc Ac : dsg E axc Mc modelc LKc Ac -> gmem E (mrestrict (ahid Ac modelc) Mc) /\ gvis E (ahid Ac modelc).
Proof.
  intros (BI & DF & AF & DV & AV & BASE & ERR & C128 & C176).
  destruct (PMAUK.vis_facts L ar C HI LYa HIok (vM E) (vmodel E) (vLB E) (vFF E) (vLK E) (vAw E) (vsp E) SCR (vsp E - 256) (vsp E - 104) (vsp E) (ocell (vsp E))
              (own (vsp E) (vR E) (vr E)) (vF E) (vfl E) 3 (vLK2 E) (vM2 E) (vmodel2 E) (vcr E) [] (c_G E X)
              (W E) [] Mc modelc LKc (vcr E) Ac BI) as ((WS & IMGC & CSB & CUAR & RMS) & OWNv & (FD & FW & FSW & FLC & FLW) & (_ & _ & FV & SV & SHV)).
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *. replace (vsp E - (vsp E - 256)) with 256 in * by (clear; lia).
  replace (vF E + 512 - 8) with (vF E + 504) in FLC by (clear; lia).
  pose proof BI as (HHc & _). cbn [app] in HHc.
  pose proof (geom_rng E X) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14).
  pose proof (c_GEOM E X) as G. unfold PNADD.geom in G.
  destruct G as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  destruct (c_BLK E X) as (Bq & Bm & HB & HB1 & HB2).
  assert (BQ0 : 0 <= Bq) by (pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHc (Bq, Bm) HB) as (Y & _); exact Y).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ (FF' E) LKc (vcr E) Ac Mc modelc HHc) as (_ & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & _).
  set (H := ahid Ac modelc) in *. set (MV := mrestrict H Mc) in *.
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ _ LKc (vcr E) Ac Mc modelc HHc BASE) as (IMG0 & _ & _).
  (* [comment removed for export] *)
  assert (VF42 : L5A.avis H (vfirst E) 42) by (apply (VBLK Bq Bm); [exact HB| exact HB1| exact HB2]).
  assert (WF42 : L5.writable RSEGS MV (vfirst E) 42).
  { apply (L5C.writable_of_defined RSEGS); [| clear - R3; lia| clear - R4; lia]. apply (proj2 (L5A.defined_vis H Mc _ _ VF42)). exact DF. }
  assert (ZF6 : L5KA.zeros_at MV (PNADD.SH (vfirst E)) 6).
  { assert (VS : L5A.avis H (PNADD.SH (vfirst E)) 6).
    { apply (VBSH Bq Bm); [exact HB|]. intros i Hi. unfold in_shadow_of, S, PNADD.SH, PNADD.SBv, SB.
      exact (sh6_in_blk (vfirst E) Bq Bm i GF8 ltac:(clear - R3 HB1 BQ0; lia) HB1 HB2 Hi). }
    apply (proj2 (L5A.zeros_at_vis H Mc _ _ VS)). pose proof (PNSAXD.shadow6 Mc (vfirst E) GF8 AF) as Z6.
    intros i Hi. specialize (Z6 i Hi). unfold byte_at, S in Z6. unfold PNADD.SH, PNADD.SBv. unfold SB in Z6. exact Z6. }
  (* [comment removed for export] *)
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ (FF' E) LKc (vcr E) Ac Mc modelc HHc) as (_ & VISs & _ & _ & _ & _ & _ & VISsh).
  pose proof (c_G E X) as GX. destruct GX as [_ GSPT GSLO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. unfold SCR in GSLO.
  destruct (c_VST E X) as (VST1 & VST2).
  assert (VV16 : L5A.avis (ahid Ac modelc) (vvp E) 16) by (apply VISs; [clear - VST1 GSLO; lia| clear - VST2 GSPT; lia]).
  assert (VVS : L5A.avis (ahid Ac modelc) (vvp E / 8 + SB) (16 / 8)).
  { change (16 / 8) with 2. apply VISsh. intros i Hi. unfold in_shadow_of, S. pose proof (Z.div_le_mono (ahl_ceil ar) (vvp E) 8 ltac:(clear; lia) ltac:(clear - VST1 GSLO; lia)) as Q1.
    pose proof (Z.div_le_mono (vvp E + 8) (ahl_ceil ar + (ar_sptop ar - ahl_ceil ar) - 1) 8 ltac:(clear; lia) ltac:(clear - VST2; lia)) as Q2.
    replace (vvp E + 8) with (vvp E + 1 * 8) in Q2 by (clear; lia). rewrite Z.div_add in Q2 by (clear; lia). clear - Hi Q1 Q2. lia. }
  assert (VPAT : exists lo hi, 0 <= lo < 2 ^ 64 /\ 0 <= hi < 2 ^ 64 /\ PNADD.vp_at MV (vvp E) lo hi).
  { destruct (L5SAR.defined_word Mc (vvp E) ltac:(apply (L5.defined_sub Mc (vvp E) 16); [exact DV| clear; lia| clear; lia]) ltac:(clear - R5; lia) ltac:(clear - R6; lia)) as (lo & Hlo & Ulo).
    destruct (L5SAR.defined_word Mc (vvp E + 8) ltac:(apply (L5.defined_sub Mc (vvp E) 16); [exact DV| clear; lia| clear; lia]) ltac:(clear - R5; lia) ltac:(clear - R6; lia)) as (hi & Hhi & Uhi).
    exists lo, hi. split; [exact Hlo|]. split; [exact Hhi|]. unfold PNADD.vp_at.
    split; [apply (proj2 (L5A.u64_at_vis H Mc (vvp E) lo (L5A.avis_sub H _ _ (vvp E) 8 VV16 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - R5; lia) ltac:(clear - R6; lia))); exact Ulo|].
    split; [apply (proj2 (L5A.u64_at_vis H Mc (vvp E + 8) hi (L5A.avis_sub H _ _ (vvp E + 8) 8 VV16 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - R5; lia) ltac:(clear - R6; lia))); exact Uhi|].
    change (16 / 8) with 2 in VVS. apply (proj2 (L5A.zeros_at_vis H Mc _ _ VVS)).
    pose proof (PMKA.zeros_of_aacc Mc (vvp E) 16 AV GV8 ltac:(reflexivity) ltac:(clear; lia)) as Z2. change (16 / 8) with 2 in Z2. exact Z2. }
  assert (VS6 : L5A.avis H (PNADD.SH (vfirst E)) 6).
  { apply (VBSH Bq Bm); [exact HB|]. intros i Hi. unfold in_shadow_of, S, PNADD.SH, PNADD.SBv, SB.
    exact (sh6_in_blk (vfirst E) Bq Bm i GF8 ltac:(clear - R3 HB1 BQ0; lia) HB1 HB2 Hi). }
  split.
  - unfold gmem. split.
    { split; [exact WS|]. split; [exact WF42|]. split; [exact FW|]. split; [exact FSW|]. split; [exact FLW|]. split; [exact IMGC|]. split; [exact CSB|]. split; [exact CUAR|].
      split; [exact OWNv|].
      split; [apply (proj2 (L5A.u64_at_vis H Mc (vsp E - 144) (vF E) (L5A.avis_sub H _ _ (vsp E - 144) 8 SV ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - R1; lia) ltac:(clear - R2; lia))); exact C128|].
      split; [apply (proj2 (L5A.u64_at_vis H Mc (vsp E - 176) (vfirst E + 42) (L5A.avis_sub H _ _ (vsp E - 176) 8 SV ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - R1; lia) ltac:(clear - R2; lia))); exact C176|].
      split; [exact FLC| exact ZF6]. }
    split; [exact VPAT|]. split; [exact IMG0|]. split; [exact RMS| exact FD].
  - unfold gvis. split; [exact SV|]. split; [exact VF42|]. split; [exact FV|]. split; [exact SHV|]. split; [exact VS6|].
    intros a n Ha Hn. apply VIMG; clear - Ha Hn; lia.
Qed.

(* [comment removed for export] *)
Lemma dmem_of E (X : dkc E) Mc modelc LKc Ac : dst E Mc modelc LKc Ac -> dmem E (mrestrict (ahid Ac modelc) Mc).
Proof.
  intros ST. pose proof ST as (_ & _ & _ & _ & _ & _ & ERR & _ & _ & ZSIG).
  destruct (gmem_of E X _ Mc modelc LKc Ac (dsg_of_dst E _ _ _ _ ST)) as (((WS & WF42 & FW & FSW & FLW & IMGC & CSB & CUAR & OWNv & C128v & C176v & FLC & ZF6) & VPAT & IMG0 & RMS & FD) & (SV & VF42 & FV & SHV & VS6 & IV)).
  set (H := ahid Ac modelc) in *. set (MV := mrestrict H Mc) in *.
  pose proof ERR as (_ & DEC & _). rewrite bax_dec_add in DEC. cbn [PNST.bdec_ok PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj PMA.AN NADDR_A] in DEC.
  destruct DEC as (GI & GN & (SI1 & SI2) & (SN1 & SN2)).
  unfold dmem, PNADD.MIA.
  split.
  { split; [exact WS|]. split; [exact WF42|]. split; [exact FW|]. split; [exact FSW|]. split; [exact FLW|]. split; [exact IMGC|]. split; [exact CSB|]. split; [exact CUAR|].
    split; [exact OWNv|]. split; [exact C128v|]. split; [exact FLC|]. split; [exact ZF6|].
    apply (proj2 (L5A.zeros_at_vis H Mc (PNADD.SH (vF E) + 4) 18 (L5A.avis_sub H _ _ (PNADD.SH (vF E) + 4) 18 SHV ltac:(clear; lia) ltac:(clear; lia)))). exact ZSIG. }
  split; [exact VPAT|]. split; [exact IMG0|]. split; [exact RMS|].
  split; [apply (proj2 (L5A.u8_at_vis H Mc 0x6722e0 1 (IV 0x6722e0 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia) ltac:(clear; lia))); exact GI|].
  split; [apply (proj2 (L5A.u8_at_vis H Mc 0x672300 1 (IV 0x672300 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia) ltac:(clear; lia))); exact GN|].
  split.
  - split; [apply (proj2 (L5A.u8_at_vis H Mc 0x6722c8 (2 * 8) (IV 0x6722c8 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia) ltac:(clear; lia))); exact SI1|].
    apply (proj2 (L5A.defined_vis H Mc (0x6722c8 + 1) 8 (IV (0x6722c8 + 1) 8 ltac:(clear; lia) ltac:(clear; lia)))). exact SI2.
  - split; [apply (proj2 (L5A.u8_at_vis H Mc 0x6722e8 (2 * 3) (IV 0x6722e8 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear; lia) ltac:(clear; lia))); exact SN1|].
    apply (proj2 (L5A.defined_vis H Mc (0x6722e8 + 1) 3 (IV (0x6722e8 + 1) 3 ltac:(clear; lia) ltac:(clear; lia)))). exact SN2.
Qed.

(* [comment removed for export] *)
Lemma depA_img a : PNST.dep PMA.AD PMA.AN a -> 65536 <= a < 6905856.
Proof.
  intros [(iv & Hin & Hr)|[Hc|(iv & Hin & Hr)]].
  - unfold PNST.pn_foot in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + pose proof (PMASK.dep_img a (or_introl (ex_intro _ iv (conj Hin Hr)))). lia.
    + unfold PNL.pn_d128_foot in Hin. cbn [PNL.pn_inf_guard PNL.pn_inf_obj PNL.pn_nan_guard PNL.pn_nan_obj PMA.AN NADDR_A] in Hin.
      repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
  - pose proof (PMASK.dep_img a (or_intror (or_introl Hc))). lia.
  - pose proof (PMASK.dep_img a (or_intror (or_intror (ex_intro _ iv (conj Hin Hr))))). lia.
Qed.
Lemma base_agree (M M' : mem) : (forall a, 65536 <= a < 6905856 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> base_ok M -> base_ok M'.
Proof.
  intros AG (RO0 & (can & Hcan & CAN) & NL & LL).
  cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock PMA.AD ADDR_A] in *.
  split; [|split; [|split]]; cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock PMA.AD ADDR_A].
  - intros i Hi. rewrite AG by lia. apply RO0. exact Hi.
  - exists can. split; [exact Hcan|]. apply (L5C.u64_at_agree RSEGS M M'); [| lia| lia| exact CAN]. intros i Hi. apply AG. lia.
  - apply (L5C.u8_at_agree RSEGS M M'); [| lia| lia| exact NL]. intros i Hi. apply AG. lia.
  - unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M M' 4%nat); [exact LL| lia| cbn; lia|]. intros i Hi. apply AG. cbn in Hi. lia.
Qed.
Lemma berr_agree (M M' : mem) ax : (forall a, 65536 <= a < 6905856 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> berr_ok M ax -> berr_ok M' ax.
Proof.
  intros AG ERR. apply (PNSTA.berr_okA_frame RSEGS PMA.AD PMA.AAD PMA.AN PMA.addrs_wf_B M M'); [| exact ERR].
  intros a Ha D. apply AG. exact (depA_img a D).
Qed.
Lemma aacc_agree (M M' : mem) p n : (forall a, p <= a < p + n -> M' (Z_to_bv 64 (S a)) = M (Z_to_bv 64 (S a))) -> PMSPA.accA M p n -> PMSPA.accA M' p n.
Proof.
  intros AG ACC a Ha. unfold byte_at in *. rewrite (AG a Ha). exact (ACC a Ha).
Qed.
Lemma zeros_agree (M M' : mem) a n : (forall i, a <= i < a + n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> L5KA.zeros_at M a n -> L5KA.zeros_at M' a n.
Proof. intros AG Z i Hi. rewrite AG by lia. exact (Z i Hi). Qed.
(* [comment removed for export] *)
Lemma S_rng p n a : p mod 8 = 0 -> 0 <= n -> p <= a < p + n -> p / 8 + 2147450880 <= S a < p / 8 + 2147450880 + (n + 7) / 8.
Proof.
  intros P8 Hn Ha. unfold S, SB.
  assert (E8 : p = 8 * (p / 8)) by (pose proof (Z.div_mod p 8 ltac:(lia)); lia).
  assert (L1 : p / 8 <= a / 8) by (apply Z.div_le_mono; lia).
  assert (L2 : a / 8 < p / 8 + (n + 7) / 8).
  { apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). lia. }
  lia.
Qed.

(* [comment removed for export] *)
Lemma Wg_facts E (X : dkc E) a : Wg E a ->
  ~ ocell (vsp E) a /\ ~ (65536 <= a < 6905856) /\ ~ (PNADD.SH (vfirst E) <= a < PNADD.SH (vfirst E) + 6)
  /\ ~ (PNADD.SH (vvp E) <= a < PNADD.SH (vvp E) + 2)
  /\ ~ (vsp E - 144 <= a < vsp E - 136) /\ ~ (vsp E - 176 <= a < vsp E - 168) /\ ~ (vvp E <= a < vvp E + 16) /\ 0 <= a < 2 ^ 47.
Proof.
  intros WA. pose proof (c_GEOM E X) as G. unfold PNADD.geom in G.
  destruct G as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  unfold Wg, ocell, PNADD.SH, PNADD.SBv in *.
  assert (F8 : vF E mod 8 = 0). { clear - GFF32. pose proof (Z.div_mod (vF E) 32 ltac:(lia)) as D. rewrite GFF32, Z.add_0_r in D. rewrite D. replace (32 * (vF E / 32)) with ((4 * (vF E / 32)) * 8) by lia. apply Z_mod_mult. }
  assert (EF : vF E = 8 * (vF E / 8)) by (clear - F8; pose proof (Z.div_mod (vF E) 8 ltac:(lia)); lia).
  assert (Ef : vfirst E = 8 * (vfirst E / 8)) by (clear - GF8; pose proof (Z.div_mod (vfirst E) 8 ltac:(lia)); lia).
  assert (Ev : vvp E = 8 * (vvp E / 8)) by (clear - GV8; pose proof (Z.div_mod (vvp E) 8 ltac:(lia)); lia).
  set (f8 := vfirst E / 8) in *. set (v8 := vvp E / 8) in *. set (F8' := vF E / 8) in *.
  destruct WA as [Y|[Y|[Y|[Y|[Y|Y]]]]].
  1-3: clear - Y GS1 GF1 GV1 GFF1 GVS EF Ef Ev; lia.
  - repeat split.
    + clear - Y GFFS. lia.
    + clear - Y GFFI. lia.
    + clear - Y GFFSH GF1 Ef. lia.
    + clear - Y GFFSH GV1 Ev. lia.
    + clear - Y GFFS. lia.
    + clear - Y GFFS. lia.
    + clear - Y GFFv. lia.
    + clear - Y GFF1. lia.
    + clear - Y GFF1. lia.
  - repeat split.
    + clear - Y GS1 GFF1 EF. lia.
    + clear - Y GFF1 EF. lia.
    + clear - Y GFFf EF Ef. lia.
    + clear - Y GFFv EF Ev. lia.
    + clear - Y GS1 GFF1 EF. lia.
    + clear - Y GS1 GFF1 EF. lia.
    + clear - Y GVSH GFF1 EF. lia.
    + clear - Y GFF1 EF. lia.
    + clear - Y GFF1 EF. lia.
  - repeat split.
    + clear - Y GFS. lia.
    + clear - Y GFI. lia.
    + clear - Y GFSH GF1 Ef. lia.
    + clear - Y GFSH GV1 Ev. lia.
    + clear - Y GFS. lia.
    + clear - Y GFS. lia.
    + clear - Y GVF. lia.
    + clear - Y GF1. lia.
    + clear - Y GF1. lia.
Qed.

(* [comment removed for export] *)
Lemma dg_piece E (X : dkc E) axc (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) Mc modelc LKc Ac (M2v : mem) (Wp : Z -> Prop) :
  dsg E axc Mc modelc LKc Ac ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Ac modelc) Mc)) (st fx2 R2 pc2 M2v) ->
  mem_grows (mrestrict (ahid Ac modelc) Mc) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M2v (Z_to_bv 64 a) = mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 a)) ->
  (forall a, Wp a -> Wg E a) ->
  (forall (M3 : mem) model3,
      dsg E axc M3 model3 LKc Ac -> ahid Ac model3 = ahid Ac modelc -> mrestrict (ahid Ac modelc) M3 = M2v ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M3 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx2 R2 pc2 M3 model3) (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 pc1 Mc modelc) (vK E).
Proof.
  intros ST MS MG FRZ WP KR.
  pose proof ST as (BI & DF & AF & DV & AV & BASE & ERR & C128 & C176).
  pose proof BI as (HHc & AMc & _). cbn [app] in HHc.
  pose proof (c_G E X) as G'. destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  pose proof (c_GEOM E X) as G. unfold PNADD.geom in G.
  destruct G as (GS1 & GS32 & GF1 & GFA8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  destruct (c_BLK E X) as (Bq & Bm & HB & HB1 & HB2).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ (FF' E) LKc (vcr E) Ac Mc modelc fx1 fx2 R1 pc1 R2 pc2 M2v Wp (vK E) HHc AMc MS MG FRZ).
  { intros a Ha Wa. pose proof (Wg_facts E X a (WP a Wa)) as (_ & NI & _). split; [| clear - NI; lia].
    destruct (WP a Wa) as [Y|[Y|[Y|[Y|[Y|Y]]]]].
    1-3: unfold aclientw, aclient_g; right; left; split; [clear - Y GSLO GSPT GS1; unfold SCR in GSLO; lia| intros Z0; clear - Z0; lia].
    - apply (L5SAR.fframe_client L ar _ (FF' E) 0 0 (vF E) 3 (vsp E - 256 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512. clear - Y; lia.
    - apply (L5SAR.fframe_shadow_client L ar _ (FF' E) 0 0 (vF E) 3 (vsp E - 256 + 32)); [left; reflexivity|]. unfold in_shadow_of, S. change (ff_bytes 3) with 512.
      rewrite (proj1 (proj2 GF8)). unfold PNADD.SH, PNADD.SBv, SB in *. clear - Y; lia.
    - apply (L5SAR.block_client L ar _ (FF' E) 0 0 Bq Bm); [exact HB| clear - Y HB1 HB2; lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MG3 FR3 VV3.
  assert (AGN : forall a, 0 <= a < 2 ^ 47 -> ~ Wg E a -> M3 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros a Ha N. apply FR3; [clear - Ha; lia|]. intros Wa. exact (N (WP a Wa)). }
  pose proof (geom_rng E X) as (R1' & R2' & R3' & R4' & R5' & R6' & R7' & R8' & R9' & R10' & R11' & R12' & R13' & R14').
  apply (KR M3 model3); [| exact HID3| exact VIS3| exact FR3].
  split.
  { apply (PMAUK.binv_pieceW L ar HI (vM E) (vmodel E) (vLB E) (vFF E) (vLK E) (vAw E) (vsp E) SCR (vsp E - 256) (vsp E - 104) (vsp E) (ocell (vsp E))
             (own (vsp E) (vR E) (vr E)) (vF E) (vfl E) 3 (vLK2 E) (vM2 E) (vmodel2 E) (vcr E) [] (c_G E X)
             (W E) [] Mc modelc LKc (vcr E) Ac M3 model3 Wp BI HH3 AM3 MRT3 MG3 FR3).
    intros a Wa. pose proof (Wg_facts E X a (WP a Wa)) as (NO & _). split; [exact NO|].
    change (ff_bytes 3) with 512. change (512 / 8) with 64.
    destruct (WP a Wa) as [Y|[Y|[Y|[Y|[Y|Y]]]]].
    1-3: left; clear - Y; lia.
    - right; left. clear - Y; lia.
    - right; right; left. unfold PNADD.SH, PNADD.SBv, SB in *. clear - Y; lia.
    - right; right; right. intros O. apply (O (vfirst E, 42)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia]. }
  split; [exact (L5.defined_grows Mc M3 _ _ MG3 DF)|].
  split.
  { apply (aacc_agree Mc M3 _ _); [| exact AF]. intros a Ha. pose proof (S_rng (vfirst E) 48 a GFA8 ltac:(clear; lia) Ha) as SR. change ((48 + 7) / 8) with 6 in SR.
    apply AGN; [clear - SR R11' R12'; unfold PNADD.SH, PNADD.SBv in *; lia|]. intros Wa. pose proof (Wg_facts E X _ Wa) as (_ & _ & N & _). apply N.
    unfold PNADD.SH, PNADD.SBv. clear - SR; lia. }
  split; [exact (L5.defined_grows Mc M3 _ _ MG3 DV)|].
  split.
  { apply (aacc_agree Mc M3 _ _); [| exact AV]. intros a Ha. pose proof (S_rng (vvp E) 16 a GV8 ltac:(clear; lia) Ha) as SR. change ((16 + 7) / 8) with 2 in SR.
    apply AGN; [clear - SR R13' R14'; unfold PNADD.SH, PNADD.SBv in *; lia|]. intros Wa. pose proof (Wg_facts E X _ Wa) as (_ & _ & _ & N & _). apply N.
    unfold PNADD.SH, PNADD.SBv. clear - SR; lia. }
  assert (AGI : forall a, 65536 <= a < 6905856 -> M3 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros a Ha. apply AGN; [clear - Ha; lia|]. intros Wa. pose proof (Wg_facts E X _ Wa) as (_ & N & _). exact (N Ha). }
  split; [exact (base_agree Mc M3 AGI BASE)|].
  split; [exact (berr_agree Mc M3 _ AGI ERR)|].
  split.
  { apply (L5C.u64_at_agree RSEGS Mc M3); [| clear - R1'; lia| clear - R2'; lia| exact C128]. intros i Hi. apply AGN; [clear - Hi R1' R2'; lia|].
    intros Wa. pose proof (Wg_facts E X _ Wa) as (_ & _ & _ & _ & N & _). apply N. clear - Hi; lia. }
  apply (L5C.u64_at_agree RSEGS Mc M3); [| clear - R1'; lia| clear - R2'; lia| exact C176]. intros i Hi. apply AGN; [clear - Hi R1' R2'; lia|].
  intros Wa. pose proof (Wg_facts E X _ Wa) as (_ & _ & _ & _ & _ & N & _). apply N. clear - Hi; lia.
Qed.

Lemma dk_piece E (X : dkc E) (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) Mc modelc LKc Ac (M2v : mem) (Wp : Z -> Prop) :
  dst E Mc modelc LKc Ac ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Ac modelc) Mc)) (st fx2 R2 pc2 M2v) ->
  mem_grows (mrestrict (ahid Ac modelc) Mc) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M2v (Z_to_bv 64 a) = mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 a)) ->
  (forall a, Wp a -> Wmid E a) ->
  (forall (M3 : mem) model3,
      dst E M3 model3 LKc Ac -> ahid Ac model3 = ahid Ac modelc -> mrestrict (ahid Ac modelc) M3 = M2v ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx2 R2 pc2 M3 model3) (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 pc1 Mc modelc) (vK E).
Proof.
  intros ST MS MG FRZ WP KR. pose proof ST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ZSIG).
  apply (dg_piece E X _ fx1 fx2 R1 R2 pc1 pc2 Mc modelc LKc Ac M2v Wp (dsg_of_dst E _ _ _ _ ST) MS MG FRZ).
  { intros a Wa. exact (Wg_of_Wmid E a (WP a Wa)). }
  intros M3 model3 SG3 HID3 VIS3 FR3. apply (KR M3 model3); [| exact HID3| exact VIS3].
  apply (dst_of_dsg E _ _ _ _ SG3). apply (zeros_agree Mc M3 _ _); [| exact ZSIG].
  pose proof (geom_rng E X) as (_ & _ & _ & _ & _ & _ & _ & _ & R9' & R10' & _).
  intros i Hi. apply FR3; [clear - Hi R9' R10'; lia|]. intros Wa. pose proof (WP i Wa) as Y. unfold Wmid, PNADD.SH, PNADD.SBv in *.
  pose proof (c_GEOM E X) as G. unfold PNADD.geom in G.
  destruct G as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & _).
  assert (E0 : 0 <= vF E / 8 <= 17592186044352) by (clear - GFF1; split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
  destruct Y as [Y|[Y|[Y|[Y|[Y|Y]]]]].
  1-3: clear - Y Hi GS1 E0; lia.
  - clear - Y Hi GFFSH E0. lia.
  - clear - Y Hi. lia.
  - clear - Y Hi GFSH E0. lia.
Qed.

(* [comment removed for export] *)
Lemma dg_memcall E (X : dkc E) axc Mc modelc LKc Ac (M1 : mem) model1 (D : Z -> Prop) :
  dsg E axc Mc modelc LKc Ac ->
  ri_inv HI (vLB E) (FF' E) LKc (vcr E) Ac M1 (vml_of model1) -> L5CA.amodel_ok Ac model1 -> model_rt modelc model1 ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar (vLB E) (FF' E) (vsp E - 256) 2560 a -> ~ D a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
  (forall a, vsp E - 256 - 2560 <= a < vsp E - 256 -> M1 (Z_to_bv 64 a) <> None) ->
  (forall a, D a -> M1 (Z_to_bv 64 a) <> None) -> (forall a, D a \/ ~ D a) ->
  (forall a, D a -> (vF E + 32 <= a < vF E + 504) \/ (vfirst E <= a < vfirst E + 42)) ->
  dsg E axc M1 model1 LKc Ac /\ (L5KA.zeros_at Mc (PNADD.SH (vF E) + 4) 18 -> L5KA.zeros_at M1 (PNADD.SH (vF E) + 4) 18).
Proof.
  intros ST HH1 AM1 RT1 PRES SDEF DDEF DDEC DIN.
  pose proof ST as (BI & DF & AF & DV & AV & BASE & ERR & C128 & C176).
  pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10). cbn [app] in B1.
  pose proof (c_G E X) as G'. destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *. unfold SCR in *.
  pose proof (c_GEOM E X) as G. unfold PNADD.geom in G.
  destruct G as (GS1 & GS32 & GF1 & GFA8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  destruct (c_BLK E X) as (Bq & Bm & HB & HB1 & HB2).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ B1) as (WB & _).
  destruct (WB _ HB) as ((BB0 & _ & _ & _ & BBC & _) & _). cbn [fst snd] in BB0, BBC.
  pose proof (geom_rng E X) as (R1' & R2' & R3' & R4' & R5' & R6' & R7' & R8' & R9' & R10' & R11' & R12' & R13' & R14').
  pose proof (Wg_facts E X) as WGF.
  assert (DW : forall a, D a -> Wg E a) by (intros a Da; destruct (DIN a Da) as [Y|Y]; [do 3 right; left; exact Y| do 5 right; exact Y]).
  (* [comment removed for export] *)
  assert (AGST : forall a, 0 <= a < 2 ^ 64 -> ahl_ceil ar <= a < 2 ^ 47 -> ~ (vsp E - 256 - 2560 <= a < vsp E - 256) -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros a Ha Hs Hns. apply PRES; [exact Ha| apply L5SAR.stack_client; [exact Hs| exact Hns]|].
    intros Da. destruct (DIN a Da) as [Y|Y]; [clear - Y Hs GFCEIL; lia| clear - Y Hs HB2 BBC; lia]. }
  assert (PRESF : forall a, 0 <= a < 2 ^ 64 -> aclient L ar (vLB E) (vFF E) (vsp E - 256) 2560 a -> ~ D a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)).
  { intros a Ha Hc ND. apply PRES; [exact Ha| apply L5SAR.aclient_cons; exact Hc| exact ND]. }
  set (WD := [(vF E + 32, 472); (vfirst E, 42)] : list L5.range).
  assert (EKD : L5SAR.ek L ar (vLB E) (FF' E) (vsp E - 256) 2560 WD Mc M1).
  { intros a (Ha & Hc & Ho). apply PRES; [exact Ha| exact Hc|]. intros Da. destruct (DIN a Da) as [Y|Y].
    - apply (Ho (vF E + 32, 472)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia].
    - apply (Ho (vfirst E, 42)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia]. }
  assert (OUTI : forall a, 65536 <= a < 6905856 -> L5.outside WD a).
  { intros a Ha rr [<-|[<-|[]]] Hr; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; [clear - Ha Hr GFFI; lia| clear - Ha Hr GFI; lia]. }
  split; [| intros ZS; apply (zeros_agree Mc M1 _ _); [| exact ZS]; intros i Hi; apply PRES; [clear - Hi R9' R10'; lia| |]].
  2:{ apply (L5SAR.fframe_shadow_client L ar _ (FF' E) (vsp E - 256) 2560 (vF E) 3 (vsp E - 256 + 32)); [left; reflexivity|]. unfold in_shadow_of, S. change (ff_bytes 3) with 512.
      rewrite (proj1 (proj2 GF8)). unfold PNADD.SH, PNADD.SBv, SB in *. clear - Hi; lia. }
  2:{ intros Da. destruct (DIN i Da) as [Y|Y]; unfold PNADD.SH, PNADD.SBv in *.
      - assert (E0 : 0 <= vF E / 8 <= 17592186044352) by (clear - GFF1; split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]). clear - Y Hi GFFSH E0. lia.
      - assert (E0 : 0 <= vF E / 8 <= 17592186044352) by (clear - GFF1; split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]). clear - Y Hi GFSH E0. lia. }
  unfold dsg. split.
  { unfold PMAUK.binv. cbn [app]. split; [exact HH1|]. split; [exact AM1|]. split; [eapply L5LZ.model_rt_trans; [exact B3| exact RT1]|]. split; [exact B4|]. split; [exact B5|].
    split. { apply (L5SAR.astk_after_eq L ar C HI HIok (vLB E) (FF' E) LKc (vcr E) Ac Mc Mc M1 _ (vsp E) _ (vsp E - 256) 2560 B1 B6 (mem_grows_refl Mc) AGST SDEF); clear; lia. }
    split. { eapply L5SAR.ek_trans; [exact B7|]. apply (L5SAR.ek_mem L ar (vLB E) (vFF E) (vsp E) 18432 (vsp E - 256) 2560 D (W E) Mc M1 PRESF); [clear; lia| clear; lia|].
             intros a Hc Ho Da. destruct (DIN a Da) as [Y|Y].
             - apply (GNCF a); [left; clear - Y; lia| exact Hc].
             - apply (Ho (vfirst E, 42)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Y; lia]. }
    split. { eapply L5SAR.dk_trans; [exact B8|]. apply (L5SAR.dk_mem L ar (vLB E) (vFF E) (vsp E) 18432 (vsp E - 256) 2560 D Mc M1 PRESF SDEF DDEF DDEC); clear; lia. }
    split. { apply (GOWN Mc M1 B9). intros a Ha. pose proof (GOCR a Ha) as OC. apply AGST; [clear - OC R1' R2'; lia| clear - OC GSLO GSPT R2'; lia| clear - OC; lia]. }
    intros i Hi. rewrite PRES; [apply B10; exact Hi| | |]; change (ff_bytes 3) with 512 in Hi; change (512 / 8) with 64 in Hi.
    - clear - Hi R9' R10'; unfold PNADD.SH, PNADD.SBv, SB in *; lia.
    - apply (L5SAR.fframe_shadow_client L ar _ (FF' E) (vsp E - 256) 2560 (vF E) 3 (vsp E - 256 + 32)); [left; reflexivity|]. unfold in_shadow_of, S. change (ff_bytes 3) with 512.
      rewrite (proj1 (proj2 GF8)). clear - Hi; lia.
    - intros Da. assert (E0 : 0 <= vF E / 8 <= 17592186044352) by (clear - GFF1; split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
      destruct (DIN _ Da) as [Y|Y]; unfold SB in *; [clear - Y Hi GFFSH E0; lia| clear - Y Hi GFSH E0; lia]. }
  split.
  { intros i Hi. destruct (DDEC (vfirst E + i)) as [Da|ND]; [exact (DDEF _ Da)|]. rewrite PRES; [exact (DF i Hi)| clear - Hi R3' R4'; lia| | exact ND].
    apply (L5SAR.block_client L ar _ (FF' E) _ _ Bq Bm); [exact HB| clear - Hi HB1 HB2; lia]. }
  split.
  { apply (aacc_agree Mc M1 _ _); [| exact AF]. intros a Ha. pose proof (S_rng (vfirst E) 48 a GFA8 ltac:(clear; lia) Ha) as SR. change ((48 + 7) / 8) with 6 in SR.
    apply PRES; [clear - SR R11' R12'; unfold PNADD.SH, PNADD.SBv in *; lia| |].
    - unfold aclient, aclient_g. do 6 right. exists (Bq, Bm). split; [exact HB|]. cbn [fst snd]. unfold in_shadow_of.
      pose proof (sh6_in_blk (vfirst E) Bq Bm (S a - (vfirst E / 8 + 2147450880)) GFA8 ltac:(clear - BB0; lia) HB1 HB2 ltac:(clear - SR; lia)) as Y. unfold S, SB in *. clear - Y. lia.
    - intros Da. pose proof (WGF _ (DW _ Da)) as (_ & _ & N & _). apply N. unfold PNADD.SH, PNADD.SBv. clear - SR; lia. }
  destruct (c_VST E X) as (VST1 & VST2).
  assert (VCL : forall i, 0 <= i < 16 -> aclient L ar (vLB E) (FF' E) (vsp E - 256) 2560 (vvp E + i)).
  { intros i Hi. apply (L5SAR.stack_client L ar (vLB E) (FF' E) (vsp E - 256) 2560 (vvp E + i)); [clear - Hi VST1 VST2 GSLO GSPT; lia| clear - Hi VST1; lia]. }
  assert (VSCL : forall i, 0 <= i < 16 / 8 -> aclient L ar (vLB E) (FF' E) (vsp E - 256) 2560 (vvp E / 8 + SB + i)).
  { change (16 / 8) with 2. intros i Hi. apply (L5SAR.stk_shadow_client L ar (vLB E) (FF' E) (vsp E - 256) 2560 (vvp E / 8 + SB + i)); [| clear - GSPT; lia].
    revert i Hi. intros i Hi. unfold in_shadow_of, S. pose proof (Z.div_le_mono (ahl_ceil ar) (vvp E) 8 ltac:(clear; lia) ltac:(clear - VST1 GSLO; lia)) as Q1.
    pose proof (Z.div_le_mono (vvp E + 8) (ahl_ceil ar + (ar_sptop ar - ahl_ceil ar) - 1) 8 ltac:(clear; lia) ltac:(clear - VST2; lia)) as Q2.
    replace (vvp E + 8) with (vvp E + 1 * 8) in Q2 by (clear; lia). rewrite Z.div_add in Q2 by (clear; lia). clear - Hi Q1 Q2. lia. }
  change (16 / 8) with 2 in VSCL.
  split.
  { intros i Hi. rewrite PRES; [exact (DV i Hi)| clear - Hi R5' R6'; lia| exact (VCL i Hi)|].
    intros Da. pose proof (WGF _ (DW _ Da)) as (_ & _ & _ & _ & _ & _ & N & _). apply N. clear - Hi; lia. }
  split.
  { apply (aacc_agree Mc M1 _ _); [| exact AV]. intros a Ha. pose proof (S_rng (vvp E) 16 a GV8 ltac:(clear; lia) Ha) as SR. change ((16 + 7) / 8) with 2 in SR.
    apply PRES; [clear - SR R13' R14'; unfold PNADD.SH, PNADD.SBv in *; lia| |].
    - replace (S a) with (vvp E / 8 + SB + (S a - (vvp E / 8 + SB))) by (clear; lia). apply VSCL. unfold SB. clear - SR. lia.
    - intros Da. pose proof (WGF _ (DW _ Da)) as (_ & _ & _ & N & _). apply N. unfold PNADD.SH, PNADD.SBv. clear - SR; lia. }
  split; [apply (PMASK.base_keep L ar C LY (vLB E) (FF' E) (vsp E - 256) 2560 WD Mc M1 EKD); [intros a Ha; apply OUTI; clear - Ha; lia| exact BASE]|].
  split.
  { apply (PNSTA.berr_okA_frame RSEGS PMA.AD PMA.AAD PMA.AN PMA.addrs_wf_B Mc M1); [| exact ERR].
    intros a Ha Dp. apply EKD. split; [exact Ha|]. pose proof (depA_img a Dp) as DI. split; [| apply OUTI; exact DI].
    unfold aclient, aclient_g. right; right; left.
    rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia| exact (PMA.ly_static L C LY a Dp)]. }
  split; [apply (L5C.u64_at_agree RSEGS Mc M1); [| clear - R1'; lia| clear - R2'; lia| exact C128]| apply (L5C.u64_at_agree RSEGS Mc M1); [| clear - R1'; lia| clear - R2'; lia| exact C176]]; intros i Hi.
  all: apply AGST; [clear - Hi R1' R2'; lia| clear - Hi GSLO GSPT R2'; lia| clear - Hi; lia].
Qed.

(* [comment removed for export] *)
Lemma sp_rng E : dkc E -> 140735332487296 <= vsp E <= 140737488355328.
Proof.
  intros X. pose proof (c_G E X) as G'. destruct G' as [_ GSPT GSLO GSHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. unfold SCR in *. clear - GSPT GSLO GSHI. lia.
Qed.
Lemma rng64 E : dkc E ->
  0 <= vsp E < 2 ^ 64 /\ 0 <= vfirst E < 2 ^ 64 /\ 0 <= vvp E < 2 ^ 64 /\ 0 <= vF E < 2 ^ 64 /\ 0 <= vfl E < 2 ^ 64.
Proof.
  intros X. pose proof (c_GEOM E X) as G. unfold PNADD.geom in G.
  destruct G as (S1 & _ & F1 & _ & _ & _ & _ & V1 & _ & _ & _ & _ & FF1 & _ & _ & _ & _ & _ & _ & FL1 & _). clear - S1 F1 V1 FF1 FL1. lia.
Qed.

(* [comment removed for export] *)
Definition out_stmt : Prop :=
  forall (E : dve), dkc E ->
  forall (fx : FPState) (Rc : bvmap 5 word) (Mc : mem) (modelc : Model) (LKc : list fframe) (Ac : list (Z * Z)) (sigma e z sd : Z),
    dst E Mc modelc LKc Ac ->
    PNADD.out_pre (vR E) (vsp E) (vF E) (vfl E) (vfirst E) sigma e z sd (vr E) Rc (mrestrict (ahid Ac modelc) Mc) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (A' : list (Z * Z)) (ptr ec : Z),
        dst E M' model' LK' A' ->
        PNADD.out_post (vR E) (vsp E) (vF E) (vfl E) (vfirst E) (vr E) ptr ec R' (mrestrict (ahid A' model') M') ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' 0xb46b0 M' model') (vK E)) ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Rc 0xb4294 Mc modelc) (vK E).

End WithHeap.
End SCFG_1.

(* [comment removed for export] *)
Ltac dgeom L ar HI E X :=
  let G := fresh "G" in let SR := fresh "SR" in let RG := fresh "RG" in
  pose proof (c_GEOM L ar HI E X) as G; unfold PNADD.geom in G;
  destruct G as (?GS1 & ?GS32 & ?GF1 & ?GF8 & ?GFSH & ?GFS & ?GFI & ?GV1 & ?GV8 & ?GVSH & ?GVS & ?GVF & ?GFF1 & ?GFF32 & ?GFFSH & ?GFFS & ?GFFI & ?GFFf & ?GFFv
                 & ?GFL1 & ?GFLSH & ?GFLF & ?GFLS & ?GFLf & ?GFLv);
  pose proof (sp_rng L ar HI E X) as SR;
  pose proof (rng64 L ar HI E X) as RG; destruct RG as (?RGs & ?RGf & ?RGv & ?RGF & ?RGfl).
Ltac gfacts L ar C HI LY HIok E X ST :=
  let MEM := fresh "MEM" in
  pose proof (gmem_of L ar C HI LY HIok E X _ _ _ _ _ ST) as MEM; unfold gmem, gvis, PNADD.vp_at, PNADD.SH, PNADD.SBv in MEM;
  destruct MEM as (((?MWS & ?MWF & ?MFW & ?MFSW & ?MFLW & ?MIMGC & ?MCSB & ?MCUAR & ?MOWN & ?MC128 & ?MC176 & ?MFLC & ?MZF6) & (?lo & ?hi & ?Hlo & ?Hhi & ?MVlo & ?MVhi & ?MVZ) & ?MIMG0 & ?MRMS & ?MFD)
                  & (?VSV & ?VF42 & ?VFV & ?VSHV & ?VS6 & ?VIV));
  pose proof MOWN as (?MS8 & ?MS16 & ?MS24 & ?MS32 & ?MS40 & ?MS48 & ?MS56 & ?MS64 & ?MS72 & ?MS80 & ?MS88 & ?MS96 & ?MS104).
Ltac dfacts L ar C HI LY HIok E X ST :=
  let MEM := fresh "MEM" in
  pose proof (dmem_of L ar C HI LY HIok E X _ _ _ _ ST) as MEM; unfold dmem, PNADD.MIA, PNADD.vp_at, PNADD.SH, PNADD.SBv, PNST.sso_lit in MEM;
  destruct MEM as ((?MWS & ?MWF & ?MFW & ?MFSW & ?MFLW & ?MIMGC & ?MCSB & ?MCUAR & ?MOWN & ?MC128 & ?MFLC & ?MZF6 & ?MZSIG) & (?lo & ?hi & ?Hlo & ?Hhi & ?MVlo & ?MVhi & ?MVZ) & ?MIMG0 & ?MRMS
                  & ?MGI & ?MGN & (?MSI1 & ?MSI2) & (?MSN1 & ?MSN2));
  pose proof MOWN as (?MS8 & ?MS16 & ?MS24 & ?MS32 & ?MS40 & ?MS48 & ?MS56 & ?MS64 & ?MS72 & ?MS80 & ?MS88 & ?MS96 & ?MS104).
(* [comment removed for export] *)
Ltac eqaddr :=
  lazymatch goal with
  | |- L5.u64_at _ ?M ?a ?v => match goal with H : L5.u64_at _ M ?b v |- _ => replace a with b by (clear; lia); exact H end
  | |- L5.u32_at _ ?M ?a ?v => match goal with H : L5.u32_at _ M ?b v |- _ => replace a with b by (clear; lia); exact H end
  | |- L5.u8_at _ ?M ?a ?v => match goal with H : L5.u8_at _ M ?b v |- _ => replace a with b by (clear; lia); exact H end
  | |- L5.writable _ ?M ?a ?n => match goal with H : L5.writable _ M ?b n |- _ => replace a with b by (clear; lia); exact H end
  | |- L5.defined ?M ?a ?n => match goal with H : L5.defined M ?b n |- _ => replace a with b by (clear; lia); exact H end
  | |- L5KA.zeros_at ?M ?a ?n => match goal with H : L5KA.zeros_at M ?b n |- _ => replace a with b by (clear; lia); exact H end
  end.
Ltac dsc := first [ assumption | (hnf; assumption) | eqaddr ].
Ltac sub_in_tac := let H := fresh in intros ? H; revert H; apply L5K.incl_b; vm_compute; reflexivity.
End PNADK.
