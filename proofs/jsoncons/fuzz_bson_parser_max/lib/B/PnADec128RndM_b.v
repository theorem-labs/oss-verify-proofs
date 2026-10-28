(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PnASrcReadK_b PmAUarK_b PmAUar_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnDecFacts PnMemW. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAXD_b PnADec128Defs_b PnADec128K_b PnADec128S_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnADec128Out2_b PnADec128RndC_b PnAEmbKit_b PnASrcReadK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADRNM.
Import L5A. Import L5CA. Import L5SAR. Import PNADK.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).

Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Lemma rnd_memcpy E (X : dkc L ar HI E) (fx : FPState) Ra Mc modelc LKc Ac (ra P0 P1 P2 P3 : Z) :
  dst L ar HI E Mc modelc LKc Ac ->
  L5.u32_at RSEGS (mrestrict (ahid Ac modelc) Mc) (vsp E - 120) P0 -> L5.u32_at RSEGS (mrestrict (ahid Ac modelc) Mc) (vsp E - 116) P1 ->
  L5.u32_at RSEGS (mrestrict (ahid Ac modelc) Mc) (vsp E - 112) P2 -> L5.u32_at RSEGS (mrestrict (ahid Ac modelc) Mc) (vsp E - 108) P3 ->
  getr Ra (reg 10) = Z_to_bv 64 (vsp E - 136) -> getr Ra (reg 11) = Z_to_bv 64 (vsp E - 120) -> getr Ra (reg 12) = Z_to_bv 64 16 ->
  getr Ra (reg 4) = Z_to_bv 64 (hl_tp L) -> getr Ra (reg 1) = Z_to_bv 64 ra -> ra mod 2 = 0 -> 0 <= ra < 2 ^ 64 ->
  getr Ra (reg 2) = Z_to_bv 64 (vsp E - 256) ->
  (forall (Rb : bvmap 5 word) (Mb : mem) (modelb : Model),
     regs_preserved Ra Rb -> dst L ar HI E Mb modelb LKc Ac ->
     L5.u32_at RSEGS (mrestrict (ahid Ac modelb) Mb) (vsp E - 136) P0 -> L5.u32_at RSEGS (mrestrict (ahid Ac modelb) Mb) (vsp E - 132) P1 ->
     L5.u32_at RSEGS (mrestrict (ahid Ac modelb) Mb) (vsp E - 128) P2 -> L5.u32_at RSEGS (mrestrict (ahid Ac modelb) Mb) (vsp E - 124) P3 ->
     (forall a, (vsp E - 256 <= a < vsp E \/ vF E <= a < vF E + 24 \/ vF E + 32 <= a < vF E + 504) -> ~ (vsp E - 136 <= a < vsp E - 120) ->
        mrestrict (ahid Ac modelb) Mb (Z_to_bv 64 a) = mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 a)) ->
     srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Rb ra Mb modelb) (vK E)) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx Ra 0x77c94 Mc modelc) (vK E).
Proof.
  intros DS U0 U1 U2 U3 Ra10 Ra11 Ra12 Ra4 Ra1 Hra Hra' Ra2 KC.
  pose proof (dsg_of_dst L ar HI E Mc modelc LKc Ac DS) as ST.
  pose proof DS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ZS).
  pose proof ST as (BI & DF & AF & _). pose proof BI as (HHc & AMc & MRTc & INCAc & INCLc & ASTKc & EKc & DKc & OWNc & DSHc). cbn [app] in HHc.
  pose proof (c_G L ar HI E X) as G'. destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. unfold PNADK.SCR in *.
  dgeom L ar HI E X.
  pose proof ASTKc as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (c_STKSH L ar HI E X) as STKSH0. unfold PNADK.SCR in STKSH0. change (18432 / 8) with 2304 in STKSH0.
  assert (SZc : shadow_zero Mc (vsp E - 18432) 2304).
  { apply (PMKA.stksh_keepA L ar (vLB E) (vFF E) (vsp E) 18432 (W E) (vM E) Mc EKc (PNADO2.wapp_W L ar HI E X) (vsp E - 18432) 2304);
      [clear - SR; lia| clear - SLO; lia| clear - SR; lia| | clear; lia| exact STKSH0].
    apply PMKA.mod16_8'. replace (vsp E - 18432) with (vsp E + (-1152) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  assert (ACCS : forall a n, vsp E - 18432 <= a -> a + n <= vsp E -> 0 <= n -> aacc Mc a n).
  { intros a n Y1 Y2 Y3. apply (L5CBR.aacc_of_zero Mc (vsp E - 18432) 2304 a n SZc);
      [apply PMKA.mod16_8'; replace (vsp E - 18432) with (vsp E + (-1152) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16| first [clear - SR; lia| clear - SLO; lia| lia]| clear - Y1; lia| clear - Y2; lia]. }
  assert (WRS : L5.writable RSEGS Mc (vsp E - 256) 256) by (apply (L5SAR.astk_writable ar Mc (vsp E) 18432); [exact ASTKc| clear; lia| clear; lia| clear; lia]).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ _ _ _ _ _ HHc) as (_ & VISc & _ & VFSc & _).
  assert (VS : forall a n, vsp E - 256 <= a -> a + n <= vsp E -> avis (ahid Ac modelc) a n) by (intros a n Y1 Y2; apply VISc; clear - Y1 Y2 SLO SR; lia).
  apply (proj1 (L5A.u32_at_vis (ahid Ac modelc) Mc (vsp E - 120) P0 (VS (vsp E - 120) 4 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - SR; lia) ltac:(clear - SR; lia))) in U0.
  apply (proj1 (L5A.u32_at_vis (ahid Ac modelc) Mc (vsp E - 116) P1 (VS (vsp E - 116) 4 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - SR; lia) ltac:(clear - SR; lia))) in U1.
  apply (proj1 (L5A.u32_at_vis (ahid Ac modelc) Mc (vsp E - 112) P2 (VS (vsp E - 112) 4 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - SR; lia) ltac:(clear - SR; lia))) in U2.
  apply (proj1 (L5A.u32_at_vis (ahid Ac modelc) Mc (vsp E - 108) P3 (VS (vsp E - 108) 4 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - SR; lia) ltac:(clear - SR; lia))) in U3.
  assert (SDc : forall i, 0 <= i < 16 -> Mc (Z_to_bv 64 (vsp E - 120 + i)) <> None).
  { intros i Hi. replace (vsp E - 120 + i) with (vsp E - 18432 + (18312 + i)) by (clear; lia). apply SDEF. clear - Hi. lia. }
  pose proof (HAJ.aior_memcpy _ _ _ _ _ HIok) as MS. unfold amemcpy_spec, amemcpy_spec_at, amem_pre, amem_post in MS.
  rewrite (L5A.aly_segs L C LYa), (L5A.aly_memcpy L C LYa), (L5A.aly_scr_mem L C LYa), (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in MS.
  assert (U2s : bv_unsigned (getr Ra 2%bv) = vsp E - 256) by (rewrite L5K.rl2, Ra2; apply L5.unsigned_lit; clear - SR; lia).
  destruct (PMASRK.rdn_of_defR Mc 16 (vsp E - 120) ltac:(clear - SR; lia) ltac:(clear - SR; lia) SDc) as (bs & RDN).
  unfold PMSPA.cfg. apply (MS fx Ra Mc modelc (vLB E) (PNADK.FF' E) LKc (vcr E) Ac (vsp E - 136) (vsp E - 120) 16 bs (vK E)); clear MS.
  - split; [exact HHc|]. split; [exact (proj1 AMc)|]. split; [exact (proj2 AMc)|].
    split; [rewrite L5K.rl10; exact Ra10|]. split; [rewrite L5K.rl12; exact Ra12|]. split; [clear; lia|].
    split; [rewrite L5K.rl4; exact Ra4|]. split; [rewrite L5K.rl1, Ra1; apply Hoare.ret_ok_even; rewrite L5.unsigned_lit by exact Hra'; exact Hra|].
    split. { rewrite U2s. apply (L5SAR.astack_ok_of_astk L ar C LYa Mc Mc (vsp E) 18432 256 2560 ASTKc (fun x Hx => Hx)); [clear; lia| clear; lia| clear; lia|].
             replace (vsp E - 256) with (vsp E + (-16) * 16) by (clear; lia). rewrite Z_mod_plus_full. clear - GS32.
             pose proof (Z.div_mod (vsp E) 32 ltac:(lia)) as D. rewrite GS32, Z.add_0_r in D. rewrite D. replace (32 * (vsp E / 32)) with ((2 * (vsp E / 32)) * 16) by lia. apply Z_mod_mult. }
    split; [apply ACCS; clear; lia|].
    split. { intros i Hi. rewrite U2s. apply L5SAR.stack_client; clear - Hi SLO SR; lia. }
    split. { intros i m Hi Hm. replace (vsp E - 136 + i) with (vsp E - 256 + (120 + i)) by (clear; lia). apply WRS; clear - Hi Hm; lia. }
    split; [exact (c_K0 L ar HI E X)|]. apply (L5SAR.app_rng_stack ar); clear - SPT SLO SHI SR; lia.
  - rewrite L5K.rl11. exact Ra11.
  - apply ACCS; clear; lia.
  - clear - SR; lia.
  - apply (L5SAR.app_rng_stack ar); clear - SPT SLO SHI SR; lia.
  - intros i Hi. right. rewrite U2s. apply L5SAR.stack_client; clear - Hi SLO SR; lia.
  - exact RDN.
  - intros _. left. clear; lia.
  - intros Rb Mb modelb Rb10 RPb BYTES PRES SDEFb RTb MIb HHb. rewrite U2s in PRES, SDEFb. rewrite L5K.rl1, Ra1.
    assert (AMb : L5CA.amodel_ok Ac modelb) by (split; [rewrite (L5LZ.model_rt_halted _ _ RTb); exact (proj1 AMc)| exact MIb]).
    destruct (PNADRNC.dg_memcall_fr L ar C HI LY HIok E X (PNST.bax_add_dec (vax E)) Mc modelc LKc Ac Mb modelb (fun a => vsp E - 136 <= a < vsp E - 136 + 16) ST HHb AMb RTb PRES SDEFb) as (STb & ZSb).
    + intros a Ha. destruct (BYTES (a - (vsp E - 136)) ltac:(clear - Ha; lia)) as (v & _ & Bv). unfold byte_at in Bv.
      replace (vsp E - 136 + (a - (vsp E - 136))) with a in Bv by (clear; lia). rewrite Bv. discriminate.
    + intros a. destruct (L5SAR.rng_dec a (vsp E - 136) (vsp E - 136 + 16)) as [Y|Y]; [left; exact Y| right; exact Y].
    + intros a Ha. clear - Ha. lia.
    + pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ _ _ _ _ _ _ HHb) as (_ & VISb & _ & VFSb & _).
      assert (CP : forall i, 0 <= i < 16 -> Mb (Z_to_bv 64 (vsp E - 136 + i)) = Mc (Z_to_bv 64 (vsp E - 120 + i))).
      { intros i Hi. destruct (BYTES i Hi) as (v & (Nv & _) & Bv). unfold byte_at in Bv. rewrite Bv.
        pose proof (PNAEK.rdn_nth RSEGS Mc 16 (vsp E - 120) bs RDN (Z.to_nat i) ltac:(clear - Hi; lia)) as RN.
        rewrite Z2Nat.id in RN by (clear - Hi; lia). rewrite (RN (SDc i Hi)). symmetry. exact Nv. }
      assert (CU : forall j v, 0 <= j <= 12 -> L5.u32_at RSEGS Mc (vsp E - 120 + j) v ->
                   L5.u32_at RSEGS (mrestrict (ahid Ac modelb) Mb) (vsp E - 136 + j) v).
      { intros j v Hj Uj. apply (proj2 (L5A.u32_at_vis (ahid Ac modelb) Mb (vsp E - 136 + j) v
          ltac:(apply VISb; clear - Hj SLO SR; lia) ltac:(clear - Hj SR; lia) ltac:(clear - Hj SR; lia))).
        unfold L5.u32_at in *. rewrite <- Uj. apply (PNAEK.rdn_shift RSEGS Mc Mb 4 (vsp E - 120 + j) (vsp E - 136 + j)).
        intros i Hi. split.
        - replace (vsp E - 120 + j + i) with (vsp E - 120 + (j + i)) by (clear; lia). apply SDc. clear - Hi Hj; lia.
        - replace (vsp E - 136 + j + i) with (vsp E - 136 + (j + i)) by (clear; lia). replace (vsp E - 120 + j + i) with (vsp E - 120 + (j + i)) by (clear; lia).
          apply CP. clear - Hi Hj; lia. }
      apply (KC Rb Mb modelb RPb (dst_of_dsg L ar HI E Mb modelb LKc Ac STb (ZSb ZS))).
      * replace (vsp E - 136) with (vsp E - 136 + 0) by (clear; lia). apply CU; [clear; lia|]. replace (vsp E - 120 + 0) with (vsp E - 120) by (clear; lia). exact U0.
      * replace (vsp E - 132) with (vsp E - 136 + 4) by (clear; lia). apply CU; [clear; lia|]. replace (vsp E - 120 + 4) with (vsp E - 116) by (clear; lia). exact U1.
      * replace (vsp E - 128) with (vsp E - 136 + 8) by (clear; lia). apply CU; [clear; lia|]. replace (vsp E - 120 + 8) with (vsp E - 112) by (clear; lia). exact U2.
      * replace (vsp E - 124) with (vsp E - 136 + 12) by (clear; lia). apply CU; [clear; lia|]. replace (vsp E - 120 + 12) with (vsp E - 108) by (clear; lia). exact U3.
      * intros a Ha N.
        assert (Hvc : ahid Ac modelc (Z_to_bv 64 a) = false /\ ahid Ac modelb (Z_to_bv 64 a) = false).
        { destruct Ha as [Ha|Ha].
          - pose proof (VISc a 1 ltac:(clear - Ha SLO SR; lia) ltac:(clear - Ha SR; lia) 0 ltac:(clear; lia)) as X1.
            pose proof (VISb a 1 ltac:(clear - Ha SLO SR; lia) ltac:(clear - Ha SR; lia) 0 ltac:(clear; lia)) as X2.
            rewrite Z.add_0_r in X1, X2. split; [exact X1| exact X2].
          - pose proof (VFSc a 1 ltac:(clear - Ha GFS1; lia) ltac:(clear - Ha GFS2; lia) 0 ltac:(clear; lia)) as X1.
            pose proof (VFSb a 1 ltac:(clear - Ha GFS1; lia) ltac:(clear - Ha GFS2; lia) 0 ltac:(clear; lia)) as X2.
            rewrite Z.add_0_r in X1, X2. split; [exact X1| exact X2]. }
        destruct Hvc as (Hvc & Hvb).
        rewrite (mrestrict_visible (ahid Ac modelb) Mb (Z_to_bv 64 a) Hvb), (mrestrict_visible (ahid Ac modelc) Mc (Z_to_bv 64 a) Hvc).
        apply PRES; [clear - Ha SR GFR; lia| | clear - N; lia].
        destruct Ha as [Ha|Ha].
        -- apply L5SAR.stack_client; clear - Ha SLO SR; lia.
        -- apply (L5SAR.fframe_client L ar _ (PNADK.FF' E) _ _ (vF E) 3 (vsp E - 256 + 32)); [left; reflexivity|]. change (ff_bytes 3) with 512. clear - Ha; lia.
Qed.
End WithHeap.
End SCFG_1.
End PNADRNM.
