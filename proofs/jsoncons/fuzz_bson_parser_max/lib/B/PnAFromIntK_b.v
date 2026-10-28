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
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNAFIK.
Import L5A. Import L5CA. Import L5SAR.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).
Abbreviation vstr_at := (PM.vstr_at RSEGS PMSPA.accA).

(* [comment removed for export] *)
Definition SCR : Z := 16384.
Definition SBv : Z := 2147450880.
Definition SH (a : Z) : Z := a / 8 + SBv.
Definition ocell (S : Z) (a : Z) : Prop := S - 96 <= a < S.
Definition saves (R0 : bvmap 5 word) (S r : Z) (M : mem) : Prop :=
  L5.u64_at RSEGS M (S - 8) r /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8))) /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9)))
  /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18))) /\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19)))
  /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20))) /\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21)))
  /\ L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22))) /\ L5.u64_at RSEGS M (S - 72) (bv_unsigned (getr R0 (reg 23)))
  /\ L5.u64_at RSEGS M (S - 80) (bv_unsigned (getr R0 (reg 24))) /\ L5.u64_at RSEGS M (S - 88) (bv_unsigned (getr R0 (reg 25)))
  /\ L5.u64_at RSEGS M (S - 96) (bv_unsigned (getr R0 (reg 26))).
Definition own (S : Z) (R : bvmap 5 word) (r : Z) (M : mem) : Prop := saves R S r M.
Lemma own_agree S R r M1 M1' : 0 <= S - 96 -> S <= 2 ^ 64 ->
  own S R r M1 -> (forall a, ocell S a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> own S R r M1'.
Proof.
  intros H1 H2 OW AG. unfold own, saves, ocell in *.
  destruct OW as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12).
  repeat split; (eapply L5C.u64_at_agree; [| | | eassumption]); first [ (intros i Hi; apply AG; lia) | lia ].
Qed.

(* [comment removed for export] *)
Record fve : Type := FVE {
  vR : bvmap 5 word; vr : Z; vsp : Z; vo : Z; vv : Z; vn : Z;
  vLB : list (Z * Z); vFF : list fframe; vLK : list fframe; vAw : list (Z * Z); vcr : credit; vmodel : Model; vM : mem; vK : TSet;
  vF : Z; vfl : Z; vLK2 : list fframe; vM2 : mem; vmodel2 : Model }.

(* [comment removed for export] *)
Definition geom (S o F fl : Z) : Prop :=
  140735332487296 <= S <= 140737488355328 /\ S mod 32 = 0
  /\ 6905856 <= o /\ o + 24 <= S - 16384 /\ o mod 8 = 0 /\ (2147446784 + 17592186048512 <= o \/ o + 24 <= 2147446784)
  /\ 6905856 <= F /\ F + 512 <= S - 16384 /\ F mod 32 = 0 /\ (2147446784 + 17592186048512 <= F \/ F + 512 <= 2147446784)
  /\ (o + 24 <= F \/ F + 512 <= o)
  /\ 6905856 <= fl /\ fl + 1 <= S - 16384 /\ (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784)
  /\ (F + 512 <= fl \/ fl + 1 <= F) /\ (o + 24 <= fl \/ fl + 1 <= o).

Lemma div8 x : x mod 8 = 0 -> 8 * (x / 8) = x.
Proof. intros H. pose proof (Z.div_mod x 8 ltac:(Lia.lia)) as D. rewrite H in D. Lia.lia. Qed.
Lemma mod32_8 x : x mod 32 = 0 -> x mod 8 = 0.
Proof. intros H. pose proof (Z.div_mod x 32 ltac:(Lia.lia)) as D. rewrite H, Z.add_0_r in D. rewrite D. replace (32 * (x / 32)) with ((4 * (x / 32)) * 8) by Lia.lia. apply Z_mod_mult. Qed.
Lemma mod32_16 x : x mod 32 = 0 -> x mod 16 = 0.
Proof. intros H. pose proof (Z.div_mod x 32 ltac:(Lia.lia)) as D. rewrite H, Z.add_0_r in D. rewrite D. replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by Lia.lia. apply Z_mod_mult. Qed.

(* [comment removed for export] *)
Lemma geom_rng S o F fl : geom S o F fl ->
  8 * (o / 8) = o /\ 8 * (F / 8) = F /\ 0 <= o / 8 /\ 0 <= F / 8 /\ o / 8 + 3 <= 17592186044416 /\ F / 8 + 64 <= 17592186044416
  /\ (o / 8 + 3 <= F / 8 \/ F / 8 + 64 <= o / 8).
Proof.
  intros (S1 & S32 & O1 & O2 & O8 & OB & F1 & F2 & F32 & FB & OF & _).
  pose proof (div8 o O8) as Eo. pose proof (div8 F (mod32_8 F F32)) as Ef.
  split; [exact Eo|]. split; [exact Ef|]. Lia.lia.
Qed.

Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Definition W (E : fve) : list L5.range := [(vo E, 24)].
Definition FF' (E : fve) : list fframe := (vF E, 3, vsp E - 128 + 32) :: vFF E.

(* [comment removed for export] *)
Definition kont (E : fve) : Prop :=
  forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (n' : Z),
    regs_preserved (vR E) R' -> vstr_at M' (vo E) (PM.VShort n') -> vn E + 1 <= n' <= vn E + 11 ->
    L5CA.ahpres L ar (vLB E) (vFF E) (vsp E) SCR (W E) (vM E) M' ->
    model_rt (vmodel E) model' -> incl LK' (vLK E) -> incl (vAw E) Aw' -> L5CA.amodel_ok Aw' model' ->
    ri_inv HI (vLB E) (vFF E) LK' (vcr E) Aw' M' (vml_of model') ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' (vr E) M' model') (vK E).

(* [comment removed for export] *)
Record fkc (E : fve) : Prop := FKC {
  c_GEOM : geom (vsp E) (vo E) (vF E) (vfl E);
  c_G : PMAUK.gctx L ar HI (vLB E) (vFF E) (vLK E) (vAw E) (vsp E) SCR (vsp E - 128) (vsp E - 96) (vsp E) (ocell (vsp E))
          (own (vsp E) (vR E) (vr E)) (vF E) (vfl E) 3 (vLK2 E) (vM2 E) (vmodel2 E) (vcr E) [];
  c_HH : ri_inv HI (vLB E) (vFF E) (vLK E) (vcr E) (vAw E) (vM E) (vml_of (vmodel E));
  c_K0 : vK E [];
  c_Rra : getr (vR E) (reg 1) = Z_to_bv 64 (vr E);
  c_RA : L5.ra_ok (vr E);
  c_Rsp : getr (vR E) (reg 2) = Z_to_bv 64 (vsp E);
  c_Rgp : getr (vR E) (reg 3) = Z_to_bv 64 (pa_gp PMA.AD);
  c_Rtp : getr (vR E) (reg 4) = Z_to_bv 64 (hl_tp L);
  c_ASTK : L5CA.astk ar (vM E) (vsp E) SCR;
  c_STKSH : shadow_zero (vM E) (vsp E - SCR) (SCR / 8);
  c_FRM : PGSA.ffroomB PNRA.FCB 2 (vFF E) (vLK E);
  c_FRS : PMSPA.ffrsA (vFF E) (vsp E);
  c_OBJ : PMSPA.aobjA (vFF E) (vo E) 24;
  c_N : 0 <= vn E <= 11;
  c_V : - 2 ^ 31 <= vv E < 2 ^ 31;
  c_KONT : kont E
}.

(* [comment removed for export] *)
Definition fis (E : fve) (k : Z) (Mc : mem) (modelc : Model) (LKc : list fframe) (Ac : list (Z * Z)) : Prop :=
  PMAUK.binv L ar HI (vM E) (vmodel E) (vLB E) (vFF E) (vLK E) (vAw E) (vsp E) SCR (vsp E - 128) (own (vsp E) (vR E) (vr E)) (vF E) 3
    (W E) [] Mc modelc LKc (vcr E) Ac
  /\ vstr_at Mc (vo E) (PM.VShort k)
  /\ L5KA.zeros_at Mc (SH (vF E) + 4) 2.

(* [comment removed for export] *)
Definition fmem (E : fve) (MV : mem) : Prop :=
  L5.writable RSEGS MV (vsp E - 128) 128 /\ L5.defined MV (vF E) 512 /\ L5.writable RSEGS MV (vF E) 512 /\ L5.writable RSEGS MV (SH (vF E)) 64
  /\ L5.u64_at RSEGS MV (vF E + 504) (vfl E) /\ L5.writable RSEGS MV (vfl E) 1
  /\ L5.img_clear MV 1249280 1282048 /\ L5.u64_at RSEGS MV 1309752 2147450880 /\ L5.u32_at RSEGS MV 1309760 1 /\ L5.u64_at RSEGS MV 1283280 1219844
  /\ saves (vR E) (vsp E) (vr E) MV /\ L5KA.zeros_at MV (SH (vF E) + 4) 2.

Lemma fmem_of E (X : fkc E) k Mc modelc LKc Ac : fis E k Mc modelc LKc Ac -> fmem E (mrestrict (ahid Ac modelc) Mc).
Proof.
  intros (BI & VS & ZS).
  destruct (PMAUK.vis_facts L ar C HI LYa HIok (vM E) (vmodel E) (vLB E) (vFF E) (vLK E) (vAw E) (vsp E) SCR (vsp E - 128) (vsp E - 96) (vsp E) (ocell (vsp E))
              (own (vsp E) (vR E) (vr E)) (vF E) (vfl E) 3 (vLK2 E) (vM2 E) (vmodel2 E) (vcr E) [] (c_G E X)
              (W E) [] Mc modelc LKc (vcr E) Ac BI) as ((WS & IMGC & CSB & CUAR & RMS) & OWNv & (FD & FW & FSW & FLC & FLW) & (_ & _ & FV & SV & SHV)).
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *. replace (vsp E - (vsp E - 128)) with 128 in * by (clear; lia).
  replace (vF E + 512 - 8) with (vF E + 504) in FLC by (clear; lia).
  unfold fmem. change (SH (vF E)) with (vF E / 8 + SB).
  split; [exact WS|]. split; [exact FD|]. split; [exact FW|]. split; [exact FSW|]. split; [exact FLC|]. split; [exact FLW|].
  split; [exact IMGC|]. split; [exact CSB|]. split; [exact CUAR|]. split; [exact RMS|]. split; [exact OWNv|].
  apply (proj2 (L5A.zeros_at_vis (ahid Ac modelc) Mc (vF E / 8 + SB + 4) 2 (L5A.avis_sub (ahid Ac modelc) _ _ (vF E / 8 + SB + 4) 2 SHV ltac:(clear; lia) ltac:(clear; lia)))). exact ZS.
Qed.

(* [comment removed for export] *)
Lemma fk_ro E (X : fkc E) k (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) Mc modelc LKc Ac :
  fis E k Mc modelc LKc Ac ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Ac modelc) Mc)) (st fx2 R2 pc2 (mrestrict (ahid Ac modelc) Mc)) ->
  (forall model3, fis E k Mc model3 LKc Ac -> ahid Ac model3 = ahid Ac modelc ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx2 R2 pc2 Mc model3) (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 pc1 Mc modelc) (vK E).
Proof.
  intros ST MS KR. pose proof ST as (BI & VS & ZS). pose proof BI as (HHc & AMc & _). cbn [app] in HHc.
  unfold PMSPA.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ (FF' E) LKc (vcr E) Ac Mc modelc fx1 fx2 R1 pc1 R2 pc2 (mrestrict (ahid Ac modelc) Mc) (vK E) HHc AMc MS).
  { intros x Hx. exact Hx. }
  { intros a Ha. reflexivity. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MG3 FR3.
  assert (EM : M3 = Mc) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
  apply (KR model3); [| exact HID3].
  split; [| split; [exact VS| exact ZS]].
  apply (PMAUK.binv_model L ar HI (vM E) (vmodel E) (vLB E) (vFF E) (vLK E) (vAw E) (vsp E) SCR (vsp E - 128) (own (vsp E) (vR E) (vr E)) (vF E) 3
           (W E) [] Mc modelc LKc (vcr E) Ac model3 BI HH3 AM3 MRT3).
Qed.

(* [comment removed for export] *)
Lemma fk_call_pb E (X : fkc E) k (fx1 : FPState) R1 Mc modelc LKc Ac (ra : Z) :
  PNRAa.str_push_back_short_spec L ar HI ->
  fis E k Mc modelc LKc Ac -> k <= 21 ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R1 (reg 2) = Z_to_bv 64 (vsp E - 128) ->
  getr R1 (reg 3) = Z_to_bv 64 (pa_gp PMA.AD) -> getr R1 (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr R1 (reg 10) = Z_to_bv 64 (vo E) ->
  (forall (fx2 : FPState) R2 (M3 : mem) model3 LK3 Aw3,
      regs_preserved R1 R2 -> fis E (k + 1) M3 model3 LK3 Aw3 ->
      srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx2 R2 ra M3 model3) (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 (PNL.pn_str_push_back PMA.AN) Mc modelc) (vK E).
Proof.
  intros PB ST Hk X1 RAok X2 X3 X4 X10 KR.
  pose proof ST as (BI & VS & ZS).
  pose proof BI as (HHc & AMc & MRTc & INCAc & INCLc & ASTKc & EKc & DKc & OWNc & DSHc). cbn [app] in HHc.
  pose proof (c_G E X) as G. pose proof G as G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *. unfold SCR in *.
  pose proof (c_GEOM E X) as GEO. pose proof (geom_rng _ _ _ _ GEO) as (Eo8 & EF8 & Qo0 & QF0 & Qo1 & QF1 & QoF).
  destruct GEO as (GS1 & GS32 & GO1 & GO2 & GO8 & GOB & GF1 & GF2 & GF32' & GFB & GOF & GL1 & GL2 & GLB & GFL & GOL).
  pose proof (c_ASTK E X) as ASTK. pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). unfold SCR in *.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND1 & NDF1 & _).
  assert (WAPP : PMKA.wapp (W E)).
  { apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct GOB as [Y|Y]; clear - Y; lia. }
  unfold PNRAa.str_push_back_short_spec, PNRA.str_push_back_short_spec in PB.
  apply (PB fx1 R1 Mc modelc (vK E) (vLB E) (FF' E) LKc Ac (vcr E) (vo E) (vsp E - 128) ra k HHc AMc (c_K0 E X)).
  { unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RAok|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
    change (PMSPA.pm_scr 1) with 14336. change (14336 / 8) with 1792.
    split; [apply (L5SAR.astk_sub ar Mc Mc (vsp E) 16384 128 14336 ASTKc (mem_grows_refl Mc)); [clear; lia| clear; lia| clear; lia| replace (vsp E - 128) with (vsp E + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply (PMKA.shadow_zero_sub Mc (vsp E - 16384) 2048); [| | clear; lia| clear; lia| clear; lia|].
    - apply PMKA.mod16_8'. replace (vsp E - 16384) with (vsp E + (-1024) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply PMKA.mod16_8'. replace (vsp E - 128 - 14336) with (vsp E + (-904) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
    - apply (PMKA.stksh_keepA L ar (vLB E) (vFF E) (vsp E) 16384 (W E) (vM E) Mc EKc WAPP (vsp E - 16384) 2048); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact (c_STKSH E X)].
      apply PMKA.mod16_8'. replace (vsp E - 16384) with (vsp E + (-1024) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffroomB_push PNRA.FCB 2 1 (vFF E) (vLK E) LKc _ (c_FRM E X) INCLc); [exact NDF1| clear; lia]. }
  { apply (PMAUAR.ffrsA_push (vFF E) (vsp E) (vsp E - 128) (vF E) 3 (vsp E - 128 + 32) (c_FRS E X)); clear; lia. }
  { rewrite L5K.rl10. exact X10. }
  { apply PMAUAR.aobjA_push. exact (c_OBJ E X). }
  { exact GO8. }
  { exact VS. } { exact Hk. }
  intros fx6 R6 M6 model6 LK6 Aw6 RP6 VS6 HP6 MRT6 INCL6 INCA6 AM6 HH6.
  change (PMSPA.pm_scr 1) with 14336 in HP6.
  set (Wc := [(vo E, 24)] : list L5.range) in HP6.
  assert (WcR : forall rr a, In rr Wc -> L5.in_rng rr a -> vo E <= a < vo E + 24).
  { intros rr a [<-|[]] Hr. exact Hr. }
  assert (WAV : forall rr a, In rr Wc -> L5.in_rng rr a -> ~ (vsp E - 128 <= a < vsp E) /\ ~ (vF E / 8 + SB <= a < vF E / 8 + SB + 64)).
  { intros rr a Hin Hr. pose proof (WcR rr a Hin Hr) as Y. unfold SB.
    split; [clear - Y GO2; lia| destruct GOB as [Z0|Z0]; clear - Y Z0 QF0 QF1; lia]. }
  apply (KR fx6 R6 M6 model6 LK6 Aw6 RP6).
  split.
  { apply (PMAUK.binv_callee L ar C HI HIok (vM E) (vmodel E) (vLB E) (vFF E) (vLK E) (vAw E) (vsp E) 16384 (vsp E - 128) (vsp E - 96) (vsp E) (ocell (vsp E)) (own (vsp E) (vR E) (vr E))
             (vF E) (vfl E) 3 (vLK2 E) (vM2 E) (vmodel2 E) (vcr E) [] G
             (W E) (W E) [] [] [] Mc modelc LKc (vcr E) Ac M6 model6 LK6 (vcr E) Aw6 14336 Wc BI HP6 HH6 AM6 MRT6 INCA6 INCL6);
      [clear; lia| clear; lia| intros rr a Hin Hr; destruct (WAV rr a Hin Hr) as (Y1 & Y2); split; [unfold ocell; clear - Y1; lia| exact Y2]
      | intros a _ Ho; exact Ho| intros a Y; exact Y]. }
  split; [exact VS6|].
  pose proof (proj1 HP6 : ek L ar (vLB E) (FF' E) (vsp E - 128) 14336 Wc Mc M6) as EK6.
  intros i Hi. rewrite (EK6 (SH (vF E) + 4 + i)); [exact (ZS i Hi)|]. unfold SH, SBv.
  split; [clear - Hi QF0 QF1; lia|]. split.
  - apply (L5SAR.fframe_shadow_client L ar _ (FF' E) (vsp E - 128) 14336 (vF E) 3 (vsp E - 128 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512.
    unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - Hi; lia.
  - intros rr Hin Hr. destruct (WAV rr _ Hin Hr) as (_ & Y). apply Y. unfold SB. clear - Hi; lia.
Qed.

End WithHeap.
End SCFG_1.
End PNAFIK.
