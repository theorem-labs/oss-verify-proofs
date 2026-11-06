(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c8 cm bj ch co.

(* [comment removed for export] *)
Module DrainG2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "reg_sv"; "SLit"; "ss_objs"; "obj_range"; "ranges_disjoint"; "sprop"; "ss_facts"; "ss_next"; "smatch"; "ss_pc"; "sstate"; "sv_below"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "lt"; "pow"; "@Corelib.Init.Datatypes"; "list"; "prod"; "cons"; "app"; "bool"; "true"; "nil"; "pair"; "nat"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c8.DrainG1"; "JDg"; "entryG"; "mlinkG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "beg2"; "O_ri"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "ag_spacebeg"; "AA"; "ag_top"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cf.DrainG2"; "SKELG"; "gint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "F_sp_high"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "alloc_top"; "event"; "m_vmmaps"; "map_contains"; "region_free"; "vm_limit"; "vm_maps"; "vm_reserved"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "overlap_sum"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF"; "frozenD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "O_chkD"; "O_cntD"; "O_mcD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG"; "BASEG"; "O_stG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "kSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "AInvQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "commit_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9"; "O_piece"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue PrimCredit PrimCreditLaws SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.RebuildRM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.RebuildD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c8.DrainG1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition gint (G : ageom) (lo hi : Z) : Prop := ltac2:(tb__ "0|1|
S12S10S15S16S32VG;A1M0Z100000000A2Vlo;A2S15Vhi;S16G0Z2000000000A2A2A2S10S15Z7fff7000Vlo;A2S15Vhi;Z10007fff8000A2A2A2").

Definition SKELG (n : Z) (extra : list sobj) : list (sv * sv * sv) := ltac2:(tb__ "0|0|
S26S0S1bS1bS1S1A2S1A2S2cS1dS0S4eS1dS0S1cS0S4fS1cS0S4bVn;A1S1cS0S4dVn;A1S1cS0S4cZ0A1S1cS0S30S20S0A1A3A3A3A3A3Vextra;A3A3A4").

Section OBJS.
Variable n : Z.
Variables (A : AA) (c : Z) (rb : valuation) (tp0 : list word) (md0 : Model).
Hypothesis HE : ltac2:(tb__ "0|0|
S2aVn;VA;Vc;Vrb;Vtp0;Vmd0;A6").
Let G : ageom := aa_geom A.

Lemma g_objs_miss : ltac2:(tb__ "0|3|
SdS1aS0A1M0S2S1bS1aS3dA1S46A2S14S14S4aVrb;R4A2SbS25R5R7R4A4SfS1aS1bS1bS1S1A2S1A2M1A1M2S26S0G1S2cS5R8A1A4S38Vn;R7A2A3S35S8S3aS9R9A1A3S39VG;R6R5A3S11G0G0S11G0G0S10SfG0S5RdA1S1dS0R2R1A3A3S10SfG2S26S0G1S2cR1A4S26S0G1S2cRcA4A3S27S0S0S7S6RcR1A2S21S14S14RaR9A4A2Lo';R2A3A2A2Lox;A2Lob;A2F_;F_;F_;F_;F_;Fhi;Flo;Fw;Fr;Fextra;FS;").
Proof.
  intros S extra r w lo hi HFz Hsm HSK HXF HI.
  destruct (g_nums n A c rb tp0 md0 HE) as (C1 & _ & K1 & _ & T1 & T2 & TG & TI & S1 & S2 & TS & TB & _).
  destruct (g_evals n A c rb tp0 md0 HE r HFz) as (EB & ERI & _ & _ & _ & ET & _).
  fold G in T1, T2, TG, TI, S1, S2, TS, TB, EB, ERI, ET.
  pose proof HE as (HA & _ & Htop & (_ & E152 & _) & _). pose proof HA as (HG0 & _ & _ & _ & _ & HI3 & _). fold G in HG0, E152.
  pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (_ & _ & _ & _ & _ & _ & _ & G8 & G9 & _).
  pose proof (geom_bands _ HG0) as (_ & _ & CB & _ & _ & CI & _). unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in CB, CI.
  destruct (proj1 HI3) as (_ & PS2 & _). rewrite kSpaceSize_val in PS2. fold G in PS2.
  destruct HFz as [Fw _]. rewrite (Fw 152%positive) in E152 by lia.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa. pose proof (proj1 (Forall_forall _ _) HFa _ HXF) as Hhigh.
  unfold SKELG in HSK. rewrite app_assoc, map_app in HSK.
  destruct (map_eq_app _ _ _ _ HSK) as (ob & ox & EO & SKb & SKx).
  exists ob, ox. split; [exact EO|]. split; [exact SKx|].
  unfold gint in HI. fold G in HI.
  destruct ob as [|osw orest]; [cbn [map app BASEG] in SKb; exfalso; clear -SKb; discriminate SKb|].
  cbn [map app BASEG] in SKb.
  assert (SKsw : skel osw = (SVar 10, SVar V_DEPTH, SLit 0)) by exact (f_equal (hd (skel osw)) SKb).
  assert (SKrest : map skel orest = map skel ((A_globals ++ RTG) ++ [O_stG; O_chkD n; O_mcD n; O_cntD 0; O_ri])) by (rewrite map_app; exact (f_equal (@tl _) SKb)).
  destruct (sw_range_gen _ r _ _ osw Hsm ltac:(rewrite EO; left; reflexivity) SKsw Hhigh) as (SW1 & SW2 & SW3).
  assert (SW0 : topG G <= fst (obj_range r osw)).
  { rewrite (sw_lo_gen r osw SKsw). unfold top_high in Htop. fold G in Htop. rewrite <- (Fw 10%positive) by lia. rewrite <- (Fw V_DEPTH) by (unfold V_DEPTH; lia). exact Htop. }
  constructor.
  - unfold ranges_disjoint. cbn [fst snd]. clear -SW0 S2 HI S1. lia.
  - apply (Forall_ranges_skel r (fun rg => ranges_disjoint rg (lo, hi)) orest _ SKrest).
    apply Forall_app. split.
    + unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI, RTG,
             O_rt1a, O_rt1b, O_tsda, O_tsdb, O_tsdc, O_self_tsd, O_tsd0, O_ctx98, O_pgb, O_insta, O_insta2, O_cfb, O_cfc, O_rms.
      unfold carved, vCTX, vSB, vRIS. cbn [app].
      repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval];
        rewrite ?E152, ?u64_lit by (first [ clear -G8 G9 TG; lia | lia ]);
        (first [ clear -HI S1; lia | clear -HI G8 G9 CB CI PS2 S1 S2 TG; lia ]).
    + assert (RIv : region_info (ag_spacebeg G) c = ag_spacebeg G + 137438953472 + c * 128) by (unfold region_info, kRegionInfoStride; rewrite kSpaceSize_val; lia).
      unfold O_stG, O_chkD, O_mcD, O_cntD, O_ri.
      repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd];
        rewrite ?EB, ?ERI, ?ET, ?RIv; clear -HI C1 K1 T1 T2 TS TB S1 S2 TG; lia.
Qed.
End OBJS.

Lemma space_commit_modelG : ltac2:(tb__ "0|8|
S33S14S2S1aS2dQ40M0A1M1A1M2S3bS22G2S3bG1G1S52RaR8R7R6A4S2bRbRaR8R7R6R5R4A7S15S32S31RcA1A1S2eG0R4A2M3A2S15S16S2eG0R5A2M4G3A2S16S16S32S31RdA1A1S51A2Z1000A2A2S10SfS1eS40S43S3eR7A1M5A1R6R5A3S1fA3S10SfS1eS3fS42G5A1M6R6R5A3S1fA3S10S15S48G6S2eG0R6A2M7S16G7G4A2A3G4A2S10SfS14S3cG5A1S34S31ReA1A1A3SfS14S41G5A1S49A3A2A2A2A2F_;F_;F_;F_;Fn0;Fa0;Fmd;Ftp;Ff;Fmd0;Ftp0;Frb;Fc;FA;").
Proof.
  intros A c rb tp0 md0 f tp md a0 n0 HA HM H1 H2.
  unfold mlinkG in HM. cbn zeta in HM. destruct HM as (M1 & M2 & M3 & M4 & _). rewrite M1, M2, M3, M4.
  destruct HA as (_ & _ & _ & _ & HMI & _). destruct HMI as (VG & _ & LIM & _ & _ & _ & TOPm & LI).
  destruct VG as (_ & N2 & _). destruct LI as (_ & _ & L3 & _).
  destruct N2 as (e & He & B1 & B2).
  destruct (in_split _ _ He) as (l1 & l2 & EM). rewrite EM in L3.
  destruct (Rmaps_disjoint_pick _ _ _ _ L3) as [XR XM].
  assert (SUB : forall e', apartW e e' -> apartW (a0, n0) e') by (intros e' X; apply (RapartW_sub a0 n0 e e'); [lia | lia | exact X]).
  split; [apply Rregion_free_of_apart; intros e' He'; apply SUB; exact (XR e' He')|].
  split.
  { unfold map_contains. apply existsb_exists. exists e. split; [exact He|]. apply andb_true_intro. split; apply Z.leb_le; lia. }
  split; [rewrite EM; apply overlap_sum_split_le; apply Rregion_free_of_apart; intros e' He'; apply SUB; exact (XM e' He')|].
  split; [exact TOPm | exact LIM].
Qed.

Section COMMIT.
Variable n : Z.
Variables (A : AA) (Kc : KcA) (c : Z) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Hypothesis HE : ltac2:(tb__ "0|0|
S2aVn;VA;Vc;Vrb;Vtp0;Vmd0;A6").
Notation JDp := (JDg A Kc c rb tp0 md0).
Let B : Z := F0d A c.

Variable CX : axst.
Hypothesis SK_x : ltac2:(tb__ "0|1|
SfS1aS1bS1bS1S1A2S1A2M0A1S26S0G0S2cS5S13VCX;A1A1A4S38Vn;S20S0A1A2A3").
Hypothesis XF_x : ltac2:(tb__ "0|0|
S35S8S3aS9S13VCX;A1A1A3").
Hypothesis XX_x : ax_X CX = [].
Hypothesis NX_x : ltac2:(tb__ "0|0|
SfS1eS55Pf0SaS13VCX;A1A1A2S1fA3").
Hypothesis IC_x : ltac2:(tb__ "0|0|
SfS24S44A1S47S25ScS13VCX;A1A1A2S23S44S45A2A3").
Hypothesis R17_x : ltac2:(tb__ "0|0|
SfS1S3S13VCX;A1Z11A2S4ZdeA1A3").
Hypothesis R10_x : ltac2:(tb__ "0|0|
SfS1S3S13VCX;A1ZaA2S2fA3").
Hypothesis BEL_x : ltac2:(tb__ "0|0|
SfS1eSeSaS13VCX;A1A1S2fA2S1fA3").
Hypothesis R11_x : ltac2:(tb__ "0|0|
SfS1S3S13VCX;A1ZbA2S4Z40000A1A3").
Hypothesis R12_x : ltac2:(tb__ "0|0|
SfS1S3S13VCX;A1ZcA2S4Z3A1A3").
Hypothesis R13_x : ltac2:(tb__ "0|0|
SfS1S3S13VCX;A1ZdA2S4Z32A1A3").
Hypothesis R14_x : ltac2:(tb__ "0|0|
SfS1S3S13VCX;A1ZeA2S4ZffffffffffffffffA1A3").
Hypothesis R15_x : ltac2:(tb__ "0|0|
SfS1S3S13VCX;A1ZfA2S4Z0A1A3").

Lemma gint_piece : ltac2:(tb__ "0|0|
S39S31VA;A1VB;S16VB;Z40000A2A3").
Proof. destruct (g_piece n A c rb tp0 md0 HE) as (P1 & P2 & _). left. split; [exact P1 | exact P2]. Qed.

Lemma commit_objsG : ltac2:(tb__ "0|0|
S2S1aS2dQ40A1A1S36S28S25S29VA;VKc;Vc;Vrb;Vtp0;Vmd0;U0A7VCX;R3R2R1A6S0S35S0R1S5S13VCX;A1A1A3S7S6R6R2A2S21S14S14VB;S16VB;Z40000A2A4A2F_;Fo;F_;Fw;Ftp;Fr;").
Proof.
  intros r tp w [HsmA HJ]. pose proof HJ as (HFz & _).
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  destruct (g_objs_miss n A c rb tp0 md0 HE (ax_S CX) [] r _ B (B + 262144) HFz Hsm SK_x XF_x gint_piece) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|? ?]; [|cbn [map] in SKx; discriminate SKx]. rewrite app_nil_r in EO. rewrite EO.
  apply Forall_forall. exact BZ.
Qed.

Theorem g_commit : ltac2:(tb__ "0|0|
S2S1aS2dQ40A1A1S37VTR;S28S25S29VA;VKc;Vc;Vrb;Vtp0;Vmd0;U1A7S53VCX;S2fZ40000A3R3R2A5R1A2VTR;S28S25S29VA;VKc;Vc;Vrb;Vtp0;Vmd0;U0A7VCX;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HT.
  apply (tr_pure Kc TR KIT (forall o, In o (ss_objs (ax_S CX)) -> ranges_disjoint (obj_range r o) (B, B + 262144))).
  { intros w Hw. exact (commit_objsG r tp w Hw). }
  intros OBJD.
  apply (tr_commit Kc TR KIT (JDp 0%nat) (JDp 1%nat) CX r tp beg2 262144 Q (JDg_K A Kc c rb tp0 md0 0%nat)
           (JDg_stable A Kc c rb tp0 md0 0%nat _ HKc ltac:(apply Pos.leb_le; exact NX_x)) IC_x R17_x R10_x BEL_x R11_x R12_x R13_x R14_x R15_x eq_refl ltac:(clear; lia)); [|exact HT].
  intros tr ms md Hsp HJ. cbn zeta.
  pose proof HJ as (HFz & HK & HM & HR).
  destruct (g_evals n A c rb tp0 md0 HE r HFz) as (_ & _ & _ & _ & EB & _). fold B in EB.
  destruct (g_piece n A c rb tp0 md0 HE) as (HB1 & HB2 & HB3 & _). fold B in HB1, HB2, HB3.
  destruct (g_nums n A c rb tp0 md0 HE) as (_ & _ & _ & _ & _ & _ & TG & _ & S1 & S2 & _).
  pose proof HE as (HA & _).
  assert (Un : bv_unsigned (Z_to_bv 64 262144) = 262144) by (apply u64_lit; clear; lia).
  destruct (space_commit_modelG A c rb tp0 md0 0%nat tp md (eval r beg2) (Z_to_bv 64 262144) HA HM
              ltac:(rewrite EB; clear -HB1; lia) ltac:(rewrite EB, Un, kSpaceSize_val; clear -HB2; lia)) as (RF & MC & OV & ETOP & ELIM).
  rewrite Un in OV. rewrite EB in OV |- *.
  pose proof (smatch_pendingA_MI segs _ _ _ _ _ _ Hsp) as HMI.
  assert (HB4 : B mod 4096 = 0).
  { destruct (proj1 (Z.mod_divide B 65536 ltac:(clear; lia)) HB3) as [q Hq]. rewrite Hq. replace (q * 65536) with (q * 16 * 4096) by (clear; lia). apply Z_mod_mult. }
  split; [exact HB4|]. split; [clear -HB1 S1; lia|].
  split.
  { rewrite ETOP. destruct HA as (HG & _). rewrite <- (geom_top _ HG). clear -HB2 S2. lia. }
  split; [exact RF|]. split; [exact MC|]. split; [exact OV|].
  split; [pose proof (g_headroom n A c rb tp0 md0 HE 0%nat tp md HM) as X; unfold committed, revealedp in X; cbn [Nat.leb] in X; clear -X; lia|].
  split; [exact OBJD|].
  split.
  { intros x Hx. unfold ro_addr. rewrite find_segment_A_off; [reflexivity|]. clear -Hx HB1 S1. lia. }
  split; [intros rr y Hin; rewrite XX_x in Hin; destruct Hin|].

  pose proof (MI_ivs_wf segs _ _ HMI) as (Wm & Wn & Wl).
  split; [exact HFz|].
  split.
  { unfold vm_forget_range. rewrite with_vm_backing_with_vm. apply HKc.
    match goal with |- Kc _ (with_vmmaps ?h ?m) =>
      replace (with_vmmaps h m) with (with_vm (mkVmState h (m_vm_lazy m) (m_vm_materialized m)) m) by (destruct m; reflexivity) end.
    apply HKc. exact HK. }
  split; [|exact (rlinkG_01 A c rb r HR)].
  apply (mlinkG_commit A c tp0 md0 tp md _ HM); fold B.
  - rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity.
  - rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity.
  - rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity.
  - rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. reflexivity.
  - rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. cbn [mmap_fixed_rw_next vm_noaccess]. rewrite EB, Un. reflexivity.
  - rewrite m_vm_lazy_vm_forget_range, m_vm_lazy_with_vmmaps. reflexivity.
  -
    set (h' := mmap_fixed_rw_next (m_vmmaps md) (eval r beg2) (Z_to_bv 64 262144)). set (md1 := with_vmmaps h' md).
    assert (Hwf1 : ivs_wf (m_vm_lazy md1)) by (unfold md1; rewrite m_vm_lazy_with_vmmaps; exact Wl).
    pose proof (used_commit_le md h' (eval r beg2) (Z_to_bv 64 262144) (conj Wm (conj Wn Wl)) eq_refl eq_refl) as PU1. fold md1 in PU1. rewrite EB, Un in PU1.
    pose proof (unpaid_forget_le md1 B (B + 262144) tp Hwf1 (MI_nodupT segs _ _ HMI)) as PU2. apply Nat2Z.inj_le in PU2.
    assert (PU3 : unpaid md1 tp = unpaid md tp) by (unfold md1; apply unpaid_ext; reflexivity). rewrite PU3 in PU2.
    unfold paid. pose proof page_size_pos. fold md1. clear -PU1 PU2 OV H. nia.
Qed.
End COMMIT.

Section REVEAL.
Variable n : Z.
Variables (A : AA) (Kc : KcA) (c : Z) (rb : valuation) (tp0 : list word) (md0 : Model).
Hypothesis HE : ltac2:(tb__ "0|0|
S2aVn;VA;Vc;Vrb;Vtp0;Vmd0;A6").
Notation JDp := (JDg A Kc c rb tp0 md0).
Let B : Z := F0d A c.

Variable E : axst.
Hypothesis SK_m : ltac2:(tb__ "0|1|
SfS1aS1bS1bS1S1A2S1A2M0A1S26S0G0S2cS5S13VE;A1A1A4S38Vn;S1cS0S54S2fA1S20S0A1A3A2A3").
Hypothesis XF_m : ltac2:(tb__ "0|0|
S35S8S3aS9S13VE;A1A1A3").

Lemma piece_numsG : ltac2:(tb__ "0|2|
S10S15Z0M0VB;A2S10S18S16VB;Z40000A2S19Z2Z3eA2A2S10SfS14S17VB;Z10000A2G0A3S10SfS14S17S50VB;A1M1Z1000A2G0A3S10S15Z2008fff7000G1A2S15S16G1Z8000A2Z10007fff8000A2A2A2A2A2A2").
Proof.
  destruct (g_piece n A c rb tp0 md0 HE) as (HB1 & HB2 & HB3 & _). fold B in HB1, HB2, HB3.
  destruct (g_nums n A c rb tp0 md0 HE) as (_ & _ & _ & _ & _ & _ & TG & _ & S1 & S2 & _).
  destruct (sh_run_nums (ag_spacebeg (aa_geom A)) B S1 HB1 HB2 ltac:(clear -S2 TG; lia) HB3) as (Q1 & Q2 & Q3 & _).
  split; [clear -HB1 S1; lia|]. split; [clear -HB2 S2 TG; lia|]. split; [exact HB3|]. split; [exact Q1|]. split; [exact Q2 | exact Q3].
Qed.

Lemma reveal_objsG : ltac2:(tb__ "0|0|
S22S2S1aS2dQ40A1A1S36S14S14S28S25S29VA;VKc;Vc;Vrb;Vtp0;Vmd0;R6A7VE;R5R4R3A6S15Z7fff7000R3A2S15R3Z10007fff8000A2S27S0S0S7S6R9R1A2S21S14S14R6R5A4A2Lo;S5S13VE;A1A1A3F_;F_;F_;Fhi;Flo;Fw;Ftp;Fr;Ff;").
Proof.
  intros f r tp w lo hi [HsmA HJ] Hlo Hhi. pose proof HJ as (HFz & _).
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  destruct (g_objs_miss n A c rb tp0 md0 HE (ax_S E) [O_piece beg2] r _ lo hi HFz Hsm SK_m XF_m ltac:(right; split; [exact Hlo | exact Hhi])) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|opc [|? ?]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKp : skel opc = skel (O_piece beg2)) by (clear -SKx; congruence).
  destruct (g_evals n A c rb tp0 md0 HE r HFz) as (_ & _ & _ & _ & EB & _). fold B in EB.
  assert (RNp : obj_range r opc = (B, B + 262144)).
  { rewrite (obj_range_skel r opc (O_piece beg2) SKp). unfold O_piece. rewrite obj_range_mk by (clear; lia). rewrite EB. f_equal; clear; lia. }
  destruct (g_piece n A c rb tp0 md0 HE) as (HB1 & _). fold B in HB1.
  destruct (g_nums n A c rb tp0 md0 HE) as (_ & _ & _ & _ & _ & _ & _ & _ & S1 & _).
  rewrite EO. apply Forall_app. split; [exact BZ|].
  repeat apply Forall_cons; try apply Forall_nil. rewrite RNp. unfold ranges_disjoint. cbn [fst snd]. clear -Hhi HB1 S1. lia.
Qed.

Theorem g_reveal : ltac2:(tb__ "0|2|
S2S1aS2dQ40A1M0A1M1S36S28S25S29VA;VKc;Vc;Vrb;Vtp0;Vmd0;U1A7VE;R3R2R1A6S11G1G1S11S2S2S28S25S29VA;VKc;Vc;Vrb;Vtp0;Vmd0;U2A7VE;R1S1dG0R2R5A3R4A6Lr';A2Ltpn;A2F_;Fw;Ftp;Fr;").
Proof.
  intros r tp [tr [ms md]] Hsp.
  pose proof (proj2 Hsp) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ. pose proof HJ as (HFz & HK & HM & HR).
  destruct piece_numsG as (B0 & B1 & BM & Q1 & Q2 & Q3).
  destruct (g_piece n A c rb tp0 md0 HE) as (HB1 & HB2 & _). fold B in HB1, HB2.
  destruct (g_nums n A c rb tp0 md0 HE) as (_ & _ & _ & _ & _ & _ & _ & _ & S1 & _).
  set (q := Sh B) in *.
  pose proof HE as (HA & _ & _ & _ & _ & (Wm0 & Wn0 & Wl0) & _).
  pose proof HA as (HG & _ & _ & _ & HMI0 & HI3 & HBT0). destruct HMI0 as (VG & _). destruct VG as (_ & _ & _ & _ & _ & _ & _ & _ & N9).
  unfold mlinkG in HM. cbn zeta in HM. destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & M9 & M10). fold B in M5, M6, M8.
  assert (Etp1 : tp1 = []).
  { destruct tp1 as [|p tp1']; [reflexivity|]. exfalso. destruct (M8 p (or_introl eq_refl)) as [_ [X _]]. discriminate X. }
  assert (BAND : forall k, (k < 8)%nat ->
            page_in_ranges (pageZ q k) (m_vm_lazy md) = true /\ forall j, 0 <= j < PG -> covered (vm_noaccess (m_vmmaps md)) (bv_unsigned (pageZ q k) + j) = false).
  { intros k Hk. assert (UP : bv_unsigned (pageZ q k) = q + 4096 * Z.of_nat k) by (apply pageZ_u; clear -Hk Q2 Q3; lia).
    destruct (N9 (pageZ q k)) as [L1 L2].
    { rewrite UP. replace (q + 4096 * Z.of_nat k) with (q + Z.of_nat k * 4096) by (clear; lia). unfold PG. rewrite Z_mod_plus_full. exact Q1. }
    { right. rewrite UP. unfold HIGH_SHADOW_BEG, HIGH_SHADOW_END, PG. clear -Hk Q2 Q3. lia. }
    split.
    - apply page_in_ranges_spec in L1 as (r0 & Hr0 & Hpr). apply page_in_range_spec in Hpr as [X1 X2]. change page_size with 4096 in X2. rewrite UP in X1, X2.
      destruct (sub1_keeps (committed 1) B (B + 262144) (m_vm_lazy md0) r0 (q + 4096 * Z.of_nat k) (q + 4096 * Z.of_nat k + 4096) Wl0
                  ltac:(clear; lia) Hr0 X1 X2 ltac:(clear; lia) ltac:(left; clear -Hk Q3 HB1 S1; lia)) as (r1 & Hr1 & Y1 & Y2).
      rewrite M6. apply page_in_ranges_spec. exists r1. split; [exact Hr1|]. apply page_in_range_spec. change page_size with 4096. rewrite UP. clear -Y1 Y2. lia.
    - intros j Hj. rewrite M5. apply sub1_cov_false; [exact Wn0 | clear; lia | exact (L2 j Hj)]. }
  destruct (SPA_J_out segs _ E r tp _ Hsp) as [HJT _].
  assert (DISJ : Forall (fun o => ranges_disjoint (obj_range r o) (q, q + 4096 * Z.of_nat 8)) (ss_objs (ax_S E))).
  { apply (reveal_objsG 1%nat r tp _ q (q + 4096 * Z.of_nat 8) Hsp); [clear -Q2; lia | clear -Q3; lia]. }
  assert (HMl : mlinkG A c tp0 md0 1%nat tp md) by exact (proj1 (proj2 (proj2 HJ))).
  destruct (SPA_reveal_pages E q 8 r tp tr ms md HJT Q1 ltac:(clear -Q2; lia) ltac:(clear -Q3; lia)
              ltac:(intros k Hk; exact (proj1 (BAND k Hk)))
              ltac:(intros z Hz; destruct (page_base_run q 8 (Z_to_bv 64 z) Q1 ltac:(clear -Q2; lia) ltac:(clear -Q3; lia) ltac:(rewrite u64_lit by (clear -Hz Q2 Q3; lia); exact Hz)) as (k & Hk & Ek & Rk);
                    rewrite u64_lit in Rk by (clear -Hz Q2 Q3; lia);
                    pose proof (proj2 (BAND k Hk) (z - (q + 4096 * Z.of_nat k)) ltac:(unfold PG; clear -Rk; lia)) as X;
                    rewrite pageZ_u in X by (clear -Hk Q2 Q3; lia);
                    replace (q + 4096 * Z.of_nat k + (z - (q + 4096 * Z.of_nat k))) with z in X by (clear; lia); exact X)
              ltac:(pose proof (g_headroom n A c rb tp0 md0 HE 1%nat tp md HMl) as X; unfold committed, revealedp in X; cbn [Nat.leb] in X; clear -X; lia) DISJ) as (tpn & r1 & Hsp1 & HRV).
  pose proof HRV as (Rw & Rl & Rtp1 & Rlen & Rvis & Rz & Rk & Ro).
  exists tpn, r1. apply (SPA_J_in segs _ E r1 (tpn ++ tp) _ Hsp1). cbn [w_tr w_cfg cfg_model fst snd].
  assert (RUN : forall z, q <= z < q + 32768 -> 0 <= z < 2 ^ 64 /\ IMG_HI <= z /\ bv_unsigned (Z_to_bv 64 z) = z).
  { intros z Hz. assert (0 <= z < 2 ^ 64) by (clear -Hz Q2 Q3; lia). split; [exact H|]. split; [unfold IMG_HI; clear -Hz Q2; lia | apply u64_lit; exact H]. }
  split; [split; [intros i Hi; rewrite Rw; exact (proj1 HFz i Hi) | intros l; rewrite Rl; exact (proj2 HFz l)]|].
  split; [exact HK|].
  split.
  { apply (mlinkG_reveal A c tp0 md0 tp md tpn HMl).
    - intros x Hx. destruct (Rtp1 x Hx) as ((k & Hk & ->) & Hnin). split; [exact Hnin|]. exists (Z.of_nat k). split; [clear -Hk; lia|].
      fold B q. rewrite pageZ_u by (clear -Hk Q2 Q3; lia). reflexivity.
    - exact Rlen.
    - pose proof (revealed_paid q 8 r tp r1 tpn md HRV) as RP. clear -RP. lia. }
  destruct HR as [R1 R2].
  split.
  - intros a Ha. rewrite (Ro a); [apply R1; apply zoneG_1|]. intros X. apply Ha. apply (zoneG_2 A c). fold B q. clear -X. lia.
  - intros z Hz. apply (zoneG_2 A c) in Hz. fold B q in Hz.
    destruct (RUN z Hz) as (Hz64 & HzI & Uz).
    destruct (reveal_bytes segs q 8 r tp r1 tpn HRV ltac:(clear -Q2; lia) ltac:(clear -Q3; lia)) with (z := z) as [_ [x Hx]]; [|clear -Hz; lia|].
    2: { rewrite view_in by exact Hz64. rewrite Hx. discriminate. }

    intros a Ha Hpm. apply (proj1 (page_mem_In _ _)) in Hpm.
    assert (Ha64 : 0 <= bv_unsigned a < 2 ^ 64 /\ IMG_HI <= bv_unsigned a) by (unfold IMG_HI; clear -Ha Q2 Q3; lia).
    destruct (page_base_run q 8 a Q1 ltac:(clear -Q2; lia) ltac:(clear -Q3; lia) Ha) as (k & Hk & Ek & Rk2).
    assert (UP : bv_unsigned (pageZ q k) = q + 4096 * Z.of_nat k) by (apply pageZ_u; clear -Hk Q2 Q3; lia).
    rewrite Ek in Hpm. rewrite M7, Etp1 in Hpm. cbn [app] in Hpm.
    assert (BP : band_page (bv_unsigned (pageZ q k))).
    { rewrite UP. unfold band_page. right. unfold HIGH_SHADOW_BEG, HIGH_SHADOW_END, PG. clear -Hk Q2 Q3. lia. }
    destruct (HBT0 _ Hpm BP (bv_unsigned a) ltac:(rewrite UP; unfold PG; clear -Rk2; lia)) as [b0 Hb0].
    change InvLaws.segsA with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA in Hb0.
    rewrite (view_rm_hi (rm rb) (bv_unsigned a) (proj1 Ha64) (or_intror (proj2 Ha64))) in Hb0. rewrite Z_to_bv_bv_unsigned in Hb0.
    rewrite (R1 a (zoneG_1 A c _)). rewrite Hb0. discriminate.
Qed.
End REVEAL.
End DrainG2.

(* [comment removed for export] *)
Module SpineMallocSecOK0S.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI"; "st0"; "W0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "AE_A"; "JL_malloc_ok"; "L_malloc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "prod"; "false"; "pair"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@Corelib.Init.Logic"; "False"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3"; "JGsC"; "clsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "E_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.IfaceS"; "alloc_roomA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL"; "nx0"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec SpineMallocSec2 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ca.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cg.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SecRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SecLinks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c0.SpineMallocSecOK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineMallocSec5J OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineMallocSec6J OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cg.SpineMallocSec5JL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineMallocSec6JL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require IfaceS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require br.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.IfaceS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.br.SpineMallocSec2S OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineMallocSecOKP.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section OK0.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S16SeVCST;R1A2SeS27R2A2S1eF_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S16SeVCST;R1A2SeS2aR2A2S1eF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S16SeVCST;R1A2S1fS28R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Variable PF : ltac2:(tb__ "0|0|
S1S9S11S12S1aS1cA2A1F_;F_;").
Hypothesis HPF : ltac2:(tb__ "0|0|
S1S9S2dS12S1aS1cA2S14S1aS1cSdSbS3S2A3ScS26S0A1VCST;VXGL;R2R1A5A4VPF;R2R1A2A3FKc;FA;").

Theorem sec_ok_0h_S : ltac2:(tb__ "0|2|
S18OF_;S1S9S4S10Q40M0A1M1S11G1A1SaR4A1S8S0R7S6R5A1A3S1dS0R8S6R6A1A3S23S15SfG0R5A2S21SfG0S5R6PcA2A2A1A3S4S17S0RbS7S0S22U0S2S2bS1R1LX;RaR9R8R7A8S20S3S2Z2A3R1R6A5S1bS0S19R8R6VPF;RaR9A2A5A4FrhoX;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp HKc Hokl Hokpl HC rhoX.
  exact (sec_ok_chain_P 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.nx0 true CST XGL HCST HXGL HCSTS HCSTD PF (ES1g W0 st0 2)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.D2c SpineMallocSec4I.T4ac SpineMallocSec4I.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5I.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5I.C5bc
           sec_g12_0h sec_g3_0h sec_g41_0ha sec_g41_0hb (fun ok' A' Kc' rho0' rho' a' tp0' G2' => sec_tail_0ha_P CST XGL HCST HXGL HCSTM HCSTS ok' A' Kc' rho0' rho' a' tp0' G2' (PF A' Kc') (HPF A' Kc')) (fun ok' A' Kc' rho0' rho' a' tp0' G2' => sec_tail_0hb_P CST XGL HCST HXGL HCSTM HCSTS ok' A' Kc' rho0' rho' a' tp0' G2' (PF A' Kc') (HPF A' Kc'))
           ok A Kc rho a tp ltac:(intros E; discriminate E) (stopJ_stable_le _) HKc Hokl Hokpl HC rhoX).
Qed.

Theorem sec_ok_0l_S : ltac2:(tb__ "0|2|
S18OF_;S1S9S4S10Q40M0A1M1S11G1A1SaR4A1S8S0R7S6R5A1A3S1dS0R8S6R6A1A3S23S13SfG0R5A2S21SfG0S5R6PcA2A2A1A3S4S17S0RbS7S0S22U0S2S2cS1R1LX;RaR9R8R7A8S20S3S2Z2A3R1R6A5S1bS0S19R8R6VPF;RaR9A2A5A4FrhoX;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp HKc Hokl Hokpl HC rhoX.
  exact (sec_ok_chain_P 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL.nx0 false CST XGL HCST HXGL HCSTS HCSTD PF (ES1g W0 st0 2)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3IL.D2c SpineMallocSec4IL.T4ac SpineMallocSec4IL.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ca.SpineMallocSec5IL.C5bc
           sec_g12_0l sec_g3_0l sec_g41_0la sec_g41_0lb (fun ok' A' Kc' rho0' rho' a' tp0' G2' => sec_tail_0la_P CST XGL HCST HXGL HCSTM HCSTS ok' A' Kc' rho0' rho' a' tp0' G2' (PF A' Kc') (HPF A' Kc')) (fun ok' A' Kc' rho0' rho' a' tp0' G2' => sec_tail_0lb_P CST XGL HCST HXGL HCSTM HCSTS ok' A' Kc' rho0' rho' a' tp0' G2' (PF A' Kc') (HPF A' Kc'))
           ok A Kc rho a tp ltac:(intros E; discriminate E) (stopJ_stable_le _) HKc Hokl Hokpl HC rhoX).
Qed.

Theorem malloc_sec_ok_0_S : ltac2:(tb__ "0|1|
S18OF_;S1S9S4S11S10Q40M0A1A1SaR3A1S8Vsegs;R6S6R4A1A3S1dVsegs;R7S6R5A1A3S25R7SfG0S5R5PcA2A2A2S4S17Vsegs;RaS7Vsegs;S29S3S2R9R8R7A5S24S3S2Z2Z8A4R1R6A5S1bVsegs;S19R7R6VPF;R9R8A2A5A4FrhoE;F_;F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp HKc Hokl Hokpl HROOM rhoE.
  apply (sec_spine_S 0%nat st0 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.SWa_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.SDa_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.SWb_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.SFB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.CertS1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.WC1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.DC1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.NXC1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.IC1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.R17_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.R11_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.R10_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.R12_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.R13_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.R14_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.R15_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.NX1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.XC1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.SK1_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.FC1_0 ok A Kc
           (fun a => OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSec3.JGsC 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.nx0 (fun X : AA => X) A Kc rho a) rho tp _ ltac:(intros E; discriminate E) (stopJ_stable_le _) HKc Hokl Hokpl HROOM).
  - intros rhoX tr ms md a Hsp HJG Hpl. pose proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.NX1_0 as NX1'. unfold W0, st0 in NX1'. unfold W0, st0 in *. rewrite NX1'.
    exact (grant_Jo 0%nat st0 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.nx0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.Hnx_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.NXG_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.R11_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bt.SpineMallocSecI.FC1_0 A Kc rho rhoX tp tr ms md a (stopJ_stable_le _) HKc Hsp HJG Hpl).
  - intros rhoX a. unfold W0, st0 in *. rewrite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.Hnx_0.
    apply (cls_split 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bo.SpineMallocSec3I.nx0 ok A Kc rho a (ES1g W0 st0 2) _ tp).
    + intros HC. exact (sec_ok_0h_S ok A Kc rho a tp HKc Hokl Hokpl HC _).
    + intros HC. exact (sec_ok_0l_S ok A Kc rho a tp HKc Hokl Hokpl HC _).
Qed.
End OK0.
End SpineMallocSecOK0S.

(* [comment removed for export] *)
Module CallocHitTail0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "Wcan"; "KcA"; "Kc_ok"; "client_addrA"; "client_shadowA"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "SVar"; "SLit"; "SPUle"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "nil"; "pair"; "prod"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "prim_room"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "V_RZ"; "C9"; "C9p"; "E3p"; "C10a"; "C10b"; "C10pa"; "C10pb"; "C9ma"; "C9mb"; "C9mpa"; "C9mpb"; "E9ma"; "E9mb"; "E9mpa"; "E9mpb"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@Corelib.Init.Logic"; "not"; "eq"; "or"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "JLc_ok"; "Lc_ok"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5"; "JGb"; "depot_onlyK"; "hd_link"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9"; "s9c_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall"; "KEEPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocS9i"; "Cert10a_0"; "Cert10b_0"; "Cert10pa_0"; "Cert10pb_0"; "Cert9a_0"; "Cert9b_0"; "Cert9pa_0"; "Cert9pb_0"; "D9ma_0"; "D9mb_0"; "D9mpa_0"; "D9mpb_0"; "ENT10a_0"; "ENT10b_0"; "ENT10pa_0"; "ENT10pb_0"; "F10a_nf"; "F10b_nf"; "F10pa_nf"; "F10pb_nf"; "FBCma_0"; "FBCmb_0"; "FBCmpa_0"; "FBCmpb_0"; "FBTma_0"; "FBTmb_0"; "FBTmpa_0"; "FBTmpb_0"; "FH_a_0"; "FH_b_0"; "FH_pa_0"; "FH_pb_0"; "HCC9ma_0"; "HCC9mb_0"; "HCC9mpa_0"; "HCC9mpb_0"; "HTma_0"; "HTmb_0"; "HTmpa_0"; "HTmpb_0"; "Hchkma_0"; "Hchkmb_0"; "Hchkmpa_0"; "Hchkmpb_0"; "Hema_0"; "Hemb_0"; "Hempa_0"; "Hempb_0"; "NX9ma_0"; "NX9mb_0"; "NX9mpa_0"; "NX9mpb_0"; "NXCma_0"; "NXCmb_0"; "NXCmpa_0"; "NXCmpb_0"; "Rma_0"; "Rmb_0"; "Rmpa_0"; "Rmpb_0"; "SID10a_0"; "SID10b_0"; "SID10pa_0"; "SID10pb_0"; "T9a_0"; "T9b_0"; "T9pa_0"; "T9pb_0"; "W9ma_0"; "W9mb_0"; "W9mpa_0"; "W9mpb_0"; "hcells_a"; "hcells_b"; "hcells_pa";
"hcells_pb"; "scells_a"; "scells_b"; "scells_pa"; "scells_pb"; "sdma_0"; "sdmb_0"; "sdmpa_0"; "sdmpb_0"; "sf_a"; "sf_b"; "sf_pa"; "sf_pb"; "sma_0"; "smb_0"; "smpa_0"; "smpb_0"; "swc_a"; "swc_b"; "swc_pa"; "swc_pb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP RebuildM SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ch.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocS6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocS8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS5i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.SpineCallocS6i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS7i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS8i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocS9i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.CDepotCallW OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ch.CDepotCallH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineCallocS5t OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma HUS_shape : stopJ_stable (Wcan 0) UStopLe.
Proof. apply stopJ_stable_le. Qed.

Section ARMS.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
SeS3cVCST;R1A2S3cS49R2A2S38F_;F_;Fa;").
Let law_die : forall A rho tp md, AInvA segsA A rho tp md -> cell_ok (view segsA (rm rho)) (mkACell 0x182f1c 4 0) := AInvA_die.
Definition arm_a : ltac2:(tb__ "0|6|
S32OF_;S1aS1aS2S8S8SeOF_;SfS30Q40M0A1A1M1SfS14S17S18A2M2A1S3dG2S13S17S18S3aS1U0A1M3S0A2S39VCST;VXGL;R8R6A4A4R1A3S3fG3S0A2S45G3S0A2S3R9A1S1eSdRdS1cRaA1A3S41RdRcA2S42R9RbRaA3SeS37S4VCST;R10R1A3S5VCST;VXGL;R10R1A4A2RcR2A1F_;Fa;S46Z1S44RfS2fG0ScRcPcM4A2A2A2A2S1bR10A1S10OLpartial;S15S35S36SeS47S2fG0ScReG4A2A2Z8A2Z0A3M5A1G5X10x2S8G1S31SdR16S1dSdS40G3S0R14R13R11A5S3eS11S7SbSaZ20A1S9S1fA1A2S12S7A1A3S20G3S0Z2A3A2R2R1A5S19SdS34R12RfReA5A4FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;Fok;") := ltac2:(tb__ "0|3|
S43U0M0S0Z2M1VCST;VXGL;VHCST;VHXGL;VHCSTM;Vlaw_die;S15S11S7SbSaZ20A1S9S1fA1A2S12S7A1A3S20S1G0A1M2S0G1A3S2bG2S0G1A3S27G2S0G1A3S8dS23G2S0G1A3S5dS51S6dS91S55S7dSa5S9dS85S79S75S71S61S65S59S89S81S4dSa9S99S95Sa1S69A27").
Definition arm_b : ltac2:(tb__ "0|6|
S32OF_;S1aS1aS2S8S8SeOF_;SfS30Q40M0A1A1M1SfS14S17S18A2M2A1S3dG2S13S17S18S3aS1U0A1M3S0A2S39VCST;VXGL;R8R6A4A4R1A3S3fG3S0A2S45G3S0A2S3R9A1S1eSdRdS1cRaA1A3S41RdRcA2S42R9RbRaA3SeS37S4VCST;R10R1A3S5VCST;VXGL;R10R1A4A2RcR2A1F_;Fa;S46Z1S44RfS2fG0ScRcPcM4A2A2A2A2S1bR10A1S10OLpartial;S15S35S36SeS47S2fG0ScReG4A2A2Z8A2Z0A3M5A1G5X10x2S8G1S31SdR16S1dSdS40G3S0R14R13R11A5S3eS11S7SbS9S1fA1SaZ10A1A2S12S7A1A3S20G3S0Z2A3A2R2R1A5S19SdS34R12RfReA5A4FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;Fok;") := ltac2:(tb__ "0|3|
S43U0M0S0Z2M1VCST;VXGL;VHCST;VHXGL;VHCSTM;Vlaw_die;S15S11S7SbS9S1fA1SaZ10A1A2S12S7A1A3S20S1G0A1M2S0G1A3S2cG2S0G1A3S28G2S0G1A3S8eS24G2S0G1A3S5eS52S6eS92S56S7eSa6S9eS86S7aS76S72S62S66S5aS8aS82S4eSaaS9aS96Sa2S6aA27").
Definition arm_pa : ltac2:(tb__ "0|6|
S32OF_;S1aS1aS2S8S8SeOF_;SfS30Q40M0A1A1M1SfS14S17S18A2M2A1S3dG2S13S17S18S3aS1U0A1M3S0A2S39VCST;VXGL;R8R6A4A4R1A3S3fG3S0A2S45G3S0A2S3R9A1S1eSdRdS1cRaA1A3S41RdRcA2S42R9RbRaA3SeS37S4VCST;R10R1A3S5VCST;VXGL;R10R1A4A2RcR2A1F_;Fa;S46Z1S44RfS2fG0ScRcPcM4A2A2A2A2S1bR10A1S10OLpartial;S16S35S36SeS47S2fG0ScReG4A2A2Z8A2Z0A3M5A1G5X10x2S8G1S31SdR16S1dSdS40G3S0R14R13R11A5S3eS11S7SbSaZ20A1S9S1fA1A2S12S7A1A3S21G3S0Z2A3A2R2R1A5S19SdS34R12RfReA5A4FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;Fok;") := ltac2:(tb__ "0|3|
S43U0M0S0Z2M1VCST;VXGL;VHCST;VHXGL;VHCSTM;Vlaw_die;S16S11S7SbSaZ20A1S9S1fA1A2S12S7A1A3S21S1G0A1M2S0G1A3S2dG2S0G1A3S29G2S0G1A3S8fS25G2S0G1A3S5fS53S6fS93S57S7fSa7S9fS87S7bS77S73S63S67S5bS8bS83S4fSabS9bS97Sa3S6bA27").
Definition arm_pb : ltac2:(tb__ "0|6|
S32OF_;S1aS1aS2S8S8SeOF_;SfS30Q40M0A1A1M1SfS14S17S18A2M2A1S3dG2S13S17S18S3aS1U0A1M3S0A2S39VCST;VXGL;R8R6A4A4R1A3S3fG3S0A2S45G3S0A2S3R9A1S1eSdRdS1cRaA1A3S41RdRcA2S42R9RbRaA3SeS37S4VCST;R10R1A3S5VCST;VXGL;R10R1A4A2RcR2A1F_;Fa;S46Z1S44RfS2fG0ScRcPcM4A2A2A2A2S1bR10A1S10OLpartial;S16S35S36SeS47S2fG0ScReG4A2A2Z8A2Z0A3M5A1G5X10x2S8G1S31SdR16S1dSdS40G3S0R14R13R11A5S3eS11S7SbS9S1fA1SaZ10A1A2S12S7A1A3S21G3S0Z2A3A2R2R1A5S19SdS34R12RfReA5A4FtpX;FrhoX;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;Ftp0;Fkeep;Frho;Frho0;FKc;FA;FA0;Fok;") := ltac2:(tb__ "0|3|
S43U0M0S0Z2M1VCST;VXGL;VHCST;VHXGL;VHCSTM;Vlaw_die;S16S11S7SbS9S1fA1SaZ10A1A2S12S7A1A3S21S1G0A1M2S0G1A3S2eG2S0G1A3S2aG2S0G1A3S90S26G2S0G1A3S60S54S70S94S58S80Sa8Sa0S88S7cS78S74S64S68S5cS8cS84S50SacS9cS98Sa4S6cA27").
End ARMS.

Section HIT0T.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
SeS3cVCST;R1A2S3cS49R2A2S38F_;F_;Fa;").

Hypothesis HCSTD : ltac2:(tb__ "0|0|
SeS3cVCST;R1A2S35S4cR2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S6VAInv;VW;Vst;VA;VKc;S9PcA1A6").

Let law_die : forall A rho tp md, AInv A rho tp md -> cell_ok (view segs (rm rho)) (mkACell 0x182f1c 4 0) := AInvA_die.
Let law_inv3 : forall A rho tp md, AInv A rho tp md -> inv3 A := AInvA_inv3.
Let W0 : list ulink := Wcan 0.
Let st0 : ustop := UStopLe.

Definition KEEP (A : AA) (a : Z) : Prop := ltac2:(tb__ "0|0|
S4bVCST;VXGL;VA;Va;A4").

Theorem calloc_hit_tail_0_P : ltac2:(tb__ "0|1|
S32OF_;S1aS2S8SfS30Q40A1A1SfS14S17S18A2M0A1S19Vsegs;S34R3R2R1A5S33S3dG0S13S17S18S3aVW0;Vst0;A2S39VCST;VXGL;R6R5A4A4R2A3S3R6A1S1eVsegs;R9S1cR7A1A3S48Vsegs;RaS1cR8A1A3S8S31Vsegs;RcS1dVsegs;S4aVW0;Vst0;RbRaR9A5S22VW0;Vst0;Z2A3R1R8A5R6A4FrhoX;F_;F_;F_;F_;TQ;FPosts;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp Posts Q HPin HKc Hokl Hokpl.
  pose proof (depot_call_HD_0 CST XGL HCST HXGL HCSTD ok A Kc rho Q HKc Hokl Hokpl) as HD.
  assert (Hokf : forall A', ok_frameA segs ok (J W0 st0 A' Kc)).
  { intros A' r t tr ms md msv' HJ. apply (Hokl r t tr ms md msv'). destruct HJ as (_ & HK & _). exact HK. }
  assert (HUS : stopJ_stable W0 st0) by (exact HUS_shape).
  assert (HW : stopJ_w W0 st0) by (hw_discharge).
  set (nv := bv_unsigned (rw rho 12%positive)).

  apply (spine_s3p_tail 0%nat st0 2 SKY_0 YX_0 YF_0 YP_0 WY1_0 WY2_0 WY3_0 WY4_0 WY5_0 WY6_0 WY7_0 s3_0 ENT3_0 SID3_0 ok A Kc rho tp Q HW HUS HKc).
  intros Hcnt HSEP HPRM0 rhoE3.

  apply (spine_s4 0%nat st0 2 Cert4_0 (KEEP A) ok A Kc rho tp Q HUS HKc (Hokf A) HD).
  intros A' rho' rhoX5 tp' HDO HL.
  assert (Enu : bv_unsigned (rw rho' 12%positive) = nv) by (destruct HL as [HLw _]; rewrite (HLw 12%positive); reflexivity).
  assert (HPRM' : prim_room A') by exact (prim_room_same A A' (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HDO)))))) HPRM0).
  assert (Hcnt' : 1 <= cnt_of A' (bv_unsigned (rw rho' 12%positive))).
  { rewrite Enu. unfold cnt_of, cst_of. rewrite (proj1 (proj2 HDO)). exact Hcnt. }
  pose proof Hokl as HokA'.

  assert (K7 : forall tpY rhoY, triple segs ok (SPA segs (JGb W0 st0 A' Kc rho') (C7 W0 st0 2) rhoY tpY) Q).
  { intros tpY rhoY.
    apply (spine_s7 0%nat st0 2 Cert7_0 OV7a_0 OV7b_0 TAB7a_0 TAB7b_0 W7a_0 W7b_0 D7a_0 D7b_0 NX7a_0 NX7b_0 G7a_0 G7b_0 F7a_0 F7b_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS8i.s8a_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bj.SpineCallocS8i.s8b_0
             ENT8a_0 ENT8b_0 SID8a_0 SID8b_0 G7p_0 F7p_0 W7p_0 D7p_0 NX7p_0 F7an_0 F7bn_0 ok A' Kc rho' tpY Q HUS HKc HokA' Hcnt').
    - intros Hm0 rhoY8.
      apply (spine_s8c 0%nat st0 (C8 W0 st0 2) (C9 W0 st0 2) (E8n W0 st0 2) Cert8_0 s9e_0 ENT9e_0 SID9e_0 ok A' Kc rho' tpY Q HUS HKc HokA').
      intros rhoY9 tpY9.
      exact (spine_s9c_P 0%nat st0 CST XGL false (C9 W0 st0 2) NX9_0 FGC_0 (arm_a CST XGL HCST HXGL HCSTM) (arm_b CST XGL HCST HXGL HCSTM)
               ok A A' Kc rho rho' (KEEP A) tp Posts HPin HW HUS HKc HokA' HDO HL (fun a Ha => Ha) Hcnt' HPRM' Hm0 rhoY9 tpY9).
    - intros Hm8 rhoY7.
      apply (spine_s7p 0%nat st0 2 Cert7p_0 OV7c_0 OV7d_0 TAB7c_0 TAB7d_0 W7c_0 W7d_0 D7c_0 D7d_0 NX7c_0 NX7d_0 G7c_0 G7d_0 F7c_0 F7d_0 s8c_0 s8d_0
               ENT8c_0 ENT8d_0 SID8c_0 SID8d_0 ok A' Kc rho' tpY Q HUS HKc HokA').
      intros rhoY8.
      apply (spine_s8c 0%nat st0 (C8p W0 st0 2) (C9p W0 st0 2) (E8pn W0 st0 2) Cert8p_0 s9ep_0 ENT9ep_0 SID9ep_0 ok A' Kc rho' tpY Q HUS HKc HokA').
      intros rhoY9 tpY9.
      exact (spine_s9c_P 0%nat st0 CST XGL true (C9p W0 st0 2) NX9p_0 FGCp_0 (arm_pa CST XGL HCST HXGL HCSTM) (arm_pb CST XGL HCST HXGL HCSTM)
               ok A A' Kc rho rho' (KEEP A) tp Posts HPin HW HUS HKc HokA' HDO HL (fun a Ha => Ha) Hcnt' HPRM' Hm8 rhoY9 tpY9). }

  assert (K6 : forall tpY rhoY, triple segs ok (SPA segs (JGb W0 st0 A' Kc rho') (C6 W0 st0 2) rhoY tpY) Q).
  { intros tpY rhoY.
    apply (spine_s6 0%nat st0 2 Cert6_0 k6_0 NTH6s_0 ZC6s_0 s7s_0 ENT7s_0 SID7s_0 G6l_0 W6l_0 D6l_0 NX6l_0 ok A' Kc rho' tpY Q HUS HKc HokA' Hcnt'); [exact (K7 tpY)|].
    intros rhoY6l.
    apply (spine_s6l 0%nat st0 2 Cert6l_0 W6m_0 D6m_0 NX6m_0 s6_0 sd6_0 R6_0 T6_0 He6_0 Hchk6_0 HT6_0 FBC6_0 FBT6_0 ENT6_0 SID6_0 NXC6_0 ok A' Kc rho' tpY Q HUS HKc HokA').
    intros rhoY6b tpY6b.
    apply (spine_s6b 0%nat st0 2 Cert6b_0 s7j_0 ENT7j_0 SID7j_0 ok A' Kc rho' tpY6b Q HUS HKc HokA'). exact (K7 tpY6b). }

  apply (spine_s5 0%nat st0 2 Cert5_0 s6n_0 ENT6n_0 SID6n_0 W5b_0 D5b_0 NX5b_0 F5f64_0 ok A' Kc rho' tp' Q HUS HKc HokA' Hcnt'); [exact (K6 tp')|].
  intros rhoX5b.
  apply (spine_s5b 0%nat st0 2 Cert5b_0 OV1_0 OV2_0 TAB1_0 TAB2_0 W1'_0 W2'_0 D1'_0 D2'_0 NX1'_0 NX2'_0 F1gt_0 F2le_0 F1_64_0 F2_64_0 s1_0 s2_0 ENT1_0 ENT2_0 SID1_0 SID2_0
           ok A' Kc rho' tp' Q HUS HKc HokA').
  intros rhoX5c.
  apply (spine_s5c 0%nat st0 2 Cert5c_0 G5m1_0 W5m1_0 D5m1_0 NX5m1_0 s51_0 sd51_0 R51_0 T51_0 He51_0 Hchk51_0 HT51_0 FBC51_0 FBT51_0 ENT51_0 SID51_0 NXC51_0
           ok A' Kc rho' tp' Q HUS HKc HokA' Hcnt').
  intros rhoX5d tp5d.
  apply (spine_s5d 0%nat st0 2 Cert5d_0 G5m2_0 W5m2_0 D5m2_0 NX5m2_0 s52_0 sd52_0 R52_0 T52_0 He52_0 Hchk52_0 HT52_0 FBC52_0 FBT52_0 ENT52_0 SID52_0 NXC52_0
           ok A' Kc rho' tp5d Q HUS HKc HokA' Hcnt').
  intros rhoX5e tp5e.
  apply (spine_s5e 0%nat st0 2 Cert5e_0 s6j_0 ENT6j_0 SID6j_0 ok A' Kc rho' tp5e Q HUS HKc HokA'). exact (K6 tp5e).
Qed.

Theorem calloc_hit_tail_0 : ltac2:(tb__ "0|0|
S32OF_;S1aS2S8SfS30Q40A1A1S19Vsegs;S34R2R1S3bVCST;VXGL;VW0;Vst0;R4R3A6A5S33S3R4A1S1eVsegs;R7S1cR5A1A3S48Vsegs;R8S1cR6A1A3S8S31Vsegs;RaS1dVsegs;S4aVW0;Vst0;R9R8R7A5S22VW0;Vst0;Z2A3R1R6A5R5A4FrhoX;F_;F_;F_;TQ;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp. exact (calloc_hit_tail_0_P ok A Kc rho tp (PFc CST XGL W0 st0 A Kc) (or_intror (or_introl eq_refl))).
Qed.
End HIT0T.
End CallocHitTail0.

(* [comment removed for export] *)
Module SpineCallocSec5J.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sobj"; "obj_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "DG"; "aa_geom"; "ag_pab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I"; "nx0"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Logic"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5I"; "C5ac"; "C5bc"; "X5ac"; "X5bc"; "EXoa"; "EXob"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kPtrArrayReserve"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4I"; "T4ac"; "T4bc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cm.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx0.

Lemma EXZa_0 : ltac2:(tb__ "0|3|
S6S1aS2S10Q40A1M0S2S11G0A1S17S4S0SaS1SdU0Vst;SeS6S2aR1A1LX;R9R8R7R6A8S2dR5R4R3A6S1cS4R3S2fA3S1dS26S14S0S0S5R7R4A2M1A3R3A2S27R3S15S0S0G1A3A2A2S1eS1dS26S32R4A2S27R4S31A2A2S1dS26S9S8RcA1A1M2R4A2S27R4S28G2S33A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w o z Hw Ho Hz. pose proof (SPA_facts_hold segsA _ rhoE X5ac tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (proj1 (Forall_forall _ _) HF _ FXBa_0) as HBR.
  destruct Ho as [<-|[<-|[<-|[]]]].
  - left. exact (ex2_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z HJ Hz).
  - left. exact (ex1_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z HJ Hz).
  - right. exact (exblk_pab 0%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HBR Hz).
Qed.

Theorem depot_call_S_0ha : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU0M4Vst;SeS1fS6S2aR1A1LX;M5R6A2R10RfR5RdA8S2bR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S2dR2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem depot_call_SE_0ha : ltac2:(tb__ "0|6|
S6S1aS2S10Q40M0A1M1S17OF_;S21VW;Vst;A2S25VW;Vst;A2S1bR6A1S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RbA2S24SfG0S3RcPcA2A2A1A4A2F_;Fbn;S20R5RbR4A3S19S1SaS1SdU0M4Vst;SeS1fS6S2aR1A1LX;M5R6A2ReRdR5RbA8S2bR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S19S1SaS1SdG4Vst;SeG5RbRaR9R8A8S2dR2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem sec_g41_0ha : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU0M4Vst;SeS1fS6S2aR1A1LX;M5R6A2R10RfR5RdA8S2bR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S34R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) T4ac U4ac X5ac C5ac WU4a_0 DU4a_0 NXU4a_0 HU4a_0 Cert5a_0 depot_call_S_0ha).
Qed.

Lemma EXZb_0 : ltac2:(tb__ "0|3|
S6S1aS2S10Q40A1M0S2S11G0A1S17S4S0SaS1SdU0Vst;SeS6R1LX;R9R8R7R6A8S2eR5R4R3A6S1cS4R3S30A3S1dS26S14S0S0S5R7R4A2M1A3R3A2S27R3S15S0S0G1A3A2A2S1eS1dS26S32R4A2S27R4S31A2A2S1dS26S9S8RcA1A1M2R4A2S27R4S28G2S33A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w o z Hw Ho Hz. pose proof (SPA_facts_hold segsA _ rhoE X5bc tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (proj1 (Forall_forall _ _) HF _ FXBb_0) as HBR.
  destruct Ho as [<-|[<-|[<-|[]]]].
  - left. exact (ex2_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z HJ Hz).
  - left. exact (ex1_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z HJ Hz).
  - right. exact (exw_pab 0%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HBR Hz).
Qed.

Theorem depot_call_S_0hb : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU0M4Vst;SeS1fS6R1LX;M5R6A2R10RfR5RdA8S2cR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S2eR2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem depot_call_SE_0hb : ltac2:(tb__ "0|6|
S6S1aS2S10Q40M0A1M1S17OF_;S21VW;Vst;A2S25VW;Vst;A2S1bR6A1S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RbA2S24SfG0S3RcPcA2A2A1A4A2F_;Fbn;S20R5RbR4A3S19S1SaS1SdU0M4Vst;SeS1fS6R1LX;M5R6A2ReRdR5RbA8S2cR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S19S1SaS1SdG4Vst;SeG5RbRaR9R8A8S2eR2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem sec_g41_0hb : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU0M4Vst;SeS1fS6R1LX;M5R6A2R10RfR5RdA8S2cR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S35R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) T4bc U4bc X5bc C5bc WU4b_0 DU4b_0 NXU4b_0 HU4b_0 Cert5b_0 depot_call_S_0hb).
Qed.
End INST.
End SpineCallocSec5J.

(* [comment removed for export] *)
Module SpineCallocSec5JL.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sobj"; "obj_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "DG"; "aa_geom"; "ag_pab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IL"; "nx0"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Logic"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5IL"; "C5ac"; "C5bc"; "X5ac"; "X5bc"; "EXoa"; "EXob"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kPtrArrayReserve"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4IL"; "T4ac"; "T4bc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cm.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cm.SpineCallocSec5IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx0.

Lemma EXZa_0 : ltac2:(tb__ "0|3|
S6S1aS2S10Q40A1M0S2S11G0A1S17S4S0SaS1SdU0Vst;SeS6S2aR1A1LX;R9R8R7R6A8S2dR5R4R3A6S1cS4R3S2fA3S1dS26S14S0S0S5R7R4A2M1A3R3A2S27R3S15S0S0G1A3A2A2S1eS1dS26S32R4A2S27R4S31A2A2S1dS26S9S8RcA1A1M2R4A2S27R4S28G2S33A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w o z Hw Ho Hz. pose proof (SPA_facts_hold segsA _ rhoE X5ac tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (proj1 (Forall_forall _ _) HF _ FXBa_0) as HBR.
  destruct Ho as [<-|[<-|[<-|[]]]].
  - left. exact (ex2_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z HJ Hz).
  - left. exact (ex1_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z HJ Hz).
  - right. exact (exblk_pab 0%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HBR Hz).
Qed.

Theorem depot_call_S_0la : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU0M4Vst;SeS1fS6S2aR1A1LX;M5R6A2R10RfR5RdA8S2bR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S2dR2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem depot_call_SE_0la : ltac2:(tb__ "0|6|
S6S1aS2S10Q40M0A1M1S17OF_;S21VW;Vst;A2S25VW;Vst;A2S1bR6A1S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RbA2S24SfG0S3RcPcA2A2A1A4A2F_;Fbn;S20R5RbR4A3S19S1SaS1SdU0M4Vst;SeS1fS6S2aR1A1LX;M5R6A2ReRdR5RbA8S2bR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S19S1SaS1SdG4Vst;SeG5RbRaR9R8A8S2dR2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem sec_g41_0la : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU0M4Vst;SeS1fS6S2aR1A1LX;M5R6A2R10RfR5RdA8S2bR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S34R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) T4ac U4ac X5ac C5ac WU4a_0 DU4a_0 NXU4a_0 HU4a_0 Cert5a_0 depot_call_S_0la).
Qed.

Lemma EXZb_0 : ltac2:(tb__ "0|3|
S6S1aS2S10Q40A1M0S2S11G0A1S17S4S0SaS1SdU0Vst;SeS6R1LX;R9R8R7R6A8S2eR5R4R3A6S1cS4R3S30A3S1dS26S14S0S0S5R7R4A2M1A3R3A2S27R3S15S0S0G1A3A2A2S1eS1dS26S32R4A2S27R4S31A2A2S1dS26S9S8RcA1A1M2R4A2S27R4S28G2S33A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w o z Hw Ho Hz. pose proof (SPA_facts_hold segsA _ rhoE X5bc tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (proj1 (Forall_forall _ _) HF _ FXBb_0) as HBR.
  destruct Ho as [<-|[<-|[<-|[]]]].
  - left. exact (ex2_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z HJ Hz).
  - left. exact (ex1_band 0%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z HJ Hz).
  - right. exact (exw_pab 0%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HBR Hz).
Qed.

Theorem depot_call_S_0lb : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU0M4Vst;SeS1fS6R1LX;M5R6A2R10RfR5RdA8S2cR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S2eR2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem depot_call_SE_0lb : ltac2:(tb__ "0|6|
S6S1aS2S10Q40M0A1M1S17OF_;S21VW;Vst;A2S25VW;Vst;A2S1bR6A1S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RbA2S24SfG0S3RcPcA2A2A1A4A2F_;Fbn;S20R5RbR4A3S19S1SaS1SdU0M4Vst;SeS1fS6R1LX;M5R6A2ReRdR5RbA8S2cR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S19S1SaS1SdG4Vst;SeG5RbRaR9R8A8S2eR2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem sec_g41_0lb : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU0M4Vst;SeS1fS6R1LX;M5R6A2R10RfR5RdA8S2cR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S35R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 0%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) T4bc U4bc X5bc C5bc WU4b_0 DU4b_0 NXU4b_0 HU4b_0 Cert5b_0 depot_call_S_0lb).
Qed.
End INST.
End SpineCallocSec5JL.

(* [comment removed for export] *)
Module SpineCallocSec5JLW1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "sobj"; "obj_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "DG"; "aa_geom"; "ag_pab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3ILW1"; "nx0"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "assn"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Logic"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.co.SpineCallocSec5ILW1"; "C5ac"; "C5bc"; "X5ac"; "X5bc"; "EXoa"; "EXob"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kPtrArrayReserve"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4ILW1"; "T4ac"; "T4bc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec4ILW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require co.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aq.SpineCallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c1.SpineCallocSec3ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec4ILW1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.CertCallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.SpineCallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cc.SpineCallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.co.SpineCallocSec5ILW1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 1. Let st : ustop := UStopLeOrPc. Let tmax : Z := 3.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.GS nx0.

Lemma EXZa_0 : ltac2:(tb__ "0|3|
S6S1aS2S10Q40A1M0S2S11G0A1S17S4S0SaS1SdU1Vst;SeS6S2aR1A1LX;R9R8R7R6A8S2dR5R4R3A6S1cS4R3S2fA3S1dS26S14S0S0S5R7R4A2M1A3R3A2S27R3S15S0S0G1A3A2A2S1eS1dS26S32R4A2S27R4S31A2A2S1dS26S9S8RcA1A1M2R4A2S27R4S28G2S33A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w o z Hw Ho Hz. pose proof (SPA_facts_hold segsA _ rhoE X5ac tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (proj1 (Forall_forall _ _) HF _ FXBa_0) as HBR.
  destruct Ho as [<-|[<-|[<-|[]]]].
  - left. exact (ex2_band 1%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z HJ Hz).
  - left. exact (ex1_band 1%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z HJ Hz).
  - right. exact (exblk_pab 1%nat st tmax nx0 Hnx_0 (fun X : AA => bumpP X) A Kc rho a rhoE tp tr md z (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HBR Hz).
Qed.

Theorem depot_call_S_1la : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU1M4Vst;SeS1fS6S2aR1A1LX;M5R6A2R10RfR5RdA8S2bR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S2dR2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 1%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem depot_call_SE_1la : ltac2:(tb__ "0|6|
S6S1aS2S10Q40M0A1M1S17OF_;S21VW;Vst;A2S25VW;Vst;A2S1bR6A1S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RbA2S24SfG0S3RcPcA2A2A1A4A2F_;Fbn;S20R5RbR4A3S19S1SaS1SdU1M4Vst;SeS1fS6S2aR1A1LX;M5R6A2ReRdR5RbA8S2bR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S19S1SaS1SdG4Vst;SeG5RbRaR9R8A8S2dR2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 1%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5ac C5ac NXEa_0 FBEa_0 F192a_0 FDEPa_0 FUNWa_0 WX5ra_0 DX5ra_0 SPL1a_0 SPL2a_0 SPL3a_0 SPL4a_0
           s4a_i R4a_i T4a_i HERa_0 HT4a_0 XX4a_0 FBX4a_0 Hchk4a_0 NX4a_0 WG10a_0 WG15a_0 WG12a_0 EXoa FAM4a_0 EXZa_0 NEWOa_0 XPosta_0
           FBT4a_0 XT4a_0 RB1a_0 RB2a_0 nobja PERM_nda_0 PERM_lta_0 PERM_cova_0 PERM_lena_0 MRG1a_0 MRG2a_0 MRG3a_0 MRG4a_0 sda_i ENT5a_0 SID5a_0 R4cova_0).
Qed.

Theorem sec_g41_1la : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU1M4Vst;SeS1fS6S2aR1A1LX;M5R6A2R10RfR5RdA8S2bR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S34R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 1%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => bumpP X) T4ac U4ac X5ac C5ac WU4a_0 DU4a_0 NXU4a_0 HU4a_0 Cert5a_0 depot_call_S_1la).
Qed.

Lemma EXZb_0 : ltac2:(tb__ "0|3|
S6S1aS2S10Q40A1M0S2S11G0A1S17S4S0SaS1SdU1Vst;SeS6R1LX;R9R8R7R6A8S2eR5R4R3A6S1cS4R3S30A3S1dS26S14S0S0S5R7R4A2M1A3R3A2S27R3S15S0S0G1A3A2A2S1eS1dS26S32R4A2S27R4S31A2A2S1dS26S9S8RcA1A1M2R4A2S27R4S28G2S33A2A2A2A2F_;F_;F_;Fz;Fo;Fw;Ftp;FrhoE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a rhoE tp w o z Hw Ho Hz. pose proof (SPA_facts_hold segsA _ rhoE X5bc tp w Hw) as HF. destruct w as [tr [ms md]].
  pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof (proj1 (Forall_forall _ _) HF _ FXBb_0) as HBR.
  destruct Ho as [<-|[<-|[<-|[]]]].
  - left. exact (ex2_band 1%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z HJ Hz).
  - left. exact (ex1_band 1%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z HJ Hz).
  - right. exact (exw_pab 1%nat st tmax nx0 Hnx_0 (fun X : AA => X) A Kc rho a rhoE tp tr md z (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) HJ HBR Hz).
Qed.

Theorem depot_call_S_1lb : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU1M4Vst;SeS1fS6R1LX;M5R6A2R10RfR5RdA8S2cR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S2eR2R1A5R9A4Ftp;FrhoE;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (depot_call_S 1%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem depot_call_SE_1lb : ltac2:(tb__ "0|6|
S6S1aS2S10Q40M0A1M1S17OF_;S21VW;Vst;A2S25VW;Vst;A2S1bR6A1S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RbA2S24SfG0S3RcPcA2A2A1A4A2F_;Fbn;S20R5RbR4A3S19S1SaS1SdU1M4Vst;SeS1fS6R1LX;M5R6A2ReRdR5RbA8S2cR4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S19S1SaS1SdG4Vst;SeG5RbRaR9R8A8S2eR2R1A5R7A3Ftp;FrhoE;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Proof.
  exact (depot_call_SE 1%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl)
           Htmax_0 X5bc C5bc NXEb_0 FBEb_0 F192b_0 FDEPb_0 FUNWb_0 WX5rb_0 DX5rb_0 SPL1b_0 SPL2b_0 SPL3b_0 SPL4b_0
           s4b_i R4b_i T4b_i HERb_0 HT4b_0 XX4b_0 FBX4b_0 Hchk4b_0 NX4b_0 WG10b_0 WG15b_0 WG12b_0 EXob FAM4b_0 EXZb_0 NEWOb_0 XPostb_0
           FBT4b_0 XT4b_0 RB1b_0 RB2b_0 nobjb PERM_ndb_0 PERM_ltb_0 PERM_covb_0 PERM_lenb_0 MRG1b_0 MRG2b_0 MRG3b_0 MRG4b_0 sdb_i ENT5b_0 SID5b_0 R4covb_0).
Qed.

Theorem sec_g41_1lb : ltac2:(tb__ "0|6|
S17OF_;S6S1aS2S10Q40M0A1M1S18S21VW;Vst;A2S25VW;Vst;A2S1bR6A1ScS1R9SbR7A1A3S29S1RaSbR8A1A3S7S2S2S11G1A1M2S13S0S0A2M3S1cG3R1S23R5A1A3S22R2S12S0S0SfG0RdA2S24SfG0S3RePcA2A2A1A4A2F_;Fbn;S20R5RdR4A3S16S1R11SaS1SdU1M4Vst;SeS1fS6R1LX;M5R6A2R10RfR5RdA8S2cR4R3A5RcA4F_;F_;Ftp';FrhoX;Frho';FG2;S2G2S16S1ReSaS1SdG4Vst;SeG5RdRcRbRaA8S35R2R1A5R9A4FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;Fok;").
Proof.
  exact (sec_g41 1%nat st tmax nx0 Hnx_0 NXG_0 (fun X : AA => X) T4bc U4bc X5bc C5bc WU4b_0 DU4b_0 NXU4b_0 HU4b_0 Cert5b_0 depot_call_S_1lb).
Qed.
End INST.
End SpineCallocSec5JLW1.

