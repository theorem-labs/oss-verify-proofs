(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k2 k8.

(* [comment removed for export] *)
Module DrainG2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "reg_sv"; "SLit"; "ss_objs"; "obj_range"; "ranges_disjoint"; "sprop"; "ss_facts"; "ss_next"; "smatch"; "ss_pc"; "sstate"; "sv_below"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "lt"; "pow"; "@Corelib.Init.Datatypes"; "list"; "prod"; "cons"; "app"; "bool"; "true"; "nil"; "pair"; "nat"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k2.DrainG1"; "JDg"; "entryG"; "mlinkG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "beg2"; "O_ri"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "ag_spacebeg"; "AA"; "ag_top"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kd.DrainG2"; "SKELG"; "gint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "F_sp_high"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "alloc_top"; "event"; "m_vmmaps"; "map_contains"; "region_free"; "vm_limit"; "vm_maps"; "vm_reserved"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "overlap_sum"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF"; "frozenD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "O_chkD"; "O_cntD"; "O_mcD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG"; "BASEG"; "O_stG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "kSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "AInvQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "commit_post"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocR9"; "O_piece"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA MmapFixedA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SMGlue PrimCredit PrimCreditLaws SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ji.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SecReveal OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.RebuildRM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.SpineMallocR8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ji.SpineMallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.RebuildD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k2.DrainG1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

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
    change InvLaws.segsA with OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA in Hb0.
    rewrite (view_rm_hi (rm rb) (bv_unsigned a) (proj1 Ha64) (or_intror (proj2 Ha64))) in Hb0. rewrite Z_to_bv_bv_unsigned in Hb0.
    rewrite (R1 a (zoneG_1 A c _)). rewrite Hb0. discriminate.
Qed.
End REVEAL.
End DrainG2.

(* [comment removed for export] *)
Module SpineMallocSecOK0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI"; "st0"; "W0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "SPA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@Corelib.Init.Datatypes"; "list"; "false"; "prod"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "KcA"; "Kc_ok"; "Posts_malloc"; "@Corelib.Init.Logic"; "False"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "ES1g"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "JGsC"; "clsP"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "vm_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "E_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IL"; "nx0"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec SpineMallocSec2 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.CertMallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SecRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SecLinks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocSecOK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineMallocSec5J OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k8.SpineMallocSec6J OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec5JL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k8.SpineMallocSec6JL.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section OK0.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S10SdVCST;R1A2SdS27R2A2S1aF_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S10SdVCST;R1A2SdS2aR2A2S1aF_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
S10SdVCST;R1A2S1cS28R2A1A1F_;Fa;").
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Hypothesis law_res : ltac2:(tb__ "0|1|
S8S3S9SeQ40A1M0A1S23VAInv;R4R3R2R1A4S1bS9SbG0G0A2A1S25S24R2A1A1S22S0A1A3F_;Fmd;Ftp;Frho;FA;").

Theorem sec_ok_0h : ltac2:(tb__ "0|2|
S12OF_;S8S17S3SeQ40M0A1M1S9G1A1S18R4A1S7S0R7S5R5A1A3S15S0R8S5R6A1A3S21ScSfG0R5A2S1fSfG0S4R6PcA2A2A1A3S3S11S0RbS6S0S20U0S1S2bS8R1LX;RaR9R8R7A8S1dS2S1Z2A3R1R6A5S14S0S13R8R6S19S16S1eS0A1VCST;VXGL;S2S1RaR9A8A5A4FrhoX;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp HKc Hokl Hokpl HC rhoX.
  exact (sec_ok_chain 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I.nx0 true CST XGL HCST HXGL HCSTS HCSTD (ES1g W0 st0 2)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I.D2c SpineMallocSec4I.T4ac SpineMallocSec4I.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5I.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5I.C5bc
           sec_g12_0h sec_g3_0h sec_g41_0ha sec_g41_0hb (sec_tail_0ha CST XGL HCST HXGL HCSTM HCSTS) (sec_tail_0hb CST XGL HCST HXGL HCSTM HCSTS)
           ok A Kc rho a tp ltac:(intros E; discriminate E) (stopJ_stable_le _) HKc Hokl Hokpl HC rhoX).
Qed.

Theorem sec_ok_0l : ltac2:(tb__ "0|2|
S12OF_;S8S17S3SeQ40M0A1M1S9G1A1S18R4A1S7S0R7S5R5A1A3S15S0R8S5R6A1A3S21SaSfG0R5A2S1fSfG0S4R6PcA2A2A1A3S3S11S0RbS6S0S20U0S1S2cS8R1LX;RaR9R8R7A8S1dS2S1Z2A3R1R6A5S14S0S13R8R6S19S16S1eS0A1VCST;VXGL;S2S1RaR9A8A5A4FrhoX;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho a tp HKc Hokl Hokpl HC rhoX.
  exact (sec_ok_chain 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IL.nx0 false CST XGL HCST HXGL HCSTS HCSTD (ES1g W0 st0 2)
           OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IL.D2c SpineMallocSec4IL.T4ac SpineMallocSec4IL.T4bc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5IL.C5ac OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5IL.C5bc
           sec_g12_0l sec_g3_0l sec_g41_0la sec_g41_0lb (sec_tail_0la CST XGL HCST HXGL HCSTM HCSTS) (sec_tail_0lb CST XGL HCST HXGL HCSTM HCSTS)
           ok A Kc rho a tp ltac:(intros E; discriminate E) (stopJ_stable_le _) HKc Hokl Hokpl HC rhoX).
Qed.

Theorem malloc_sec_ok_0 : ltac2:(tb__ "0|0|
S12OF_;S8S17S3S9SeQ40A1A1S18R3A1S7Vsegs;R6S5R4A1A3S15Vsegs;R7S5R5A1A3S3S11Vsegs;R9S6Vsegs;S29S2S1R8R7R6A5S26S2S1Z2Z8A4R1R5A5S14Vsegs;S13R6R5S19S16VAInv;VCST;VXGL;S2S1R8R7A8A5A4FrhoE;F_;F_;F_;Ftp;Frho;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho tp HKc Hokl Hokpl rhoE.
  apply (malloc_sec_0 CST XGL HCST HXGL HCSTM HCSTS law_res ok A Kc
           (fun a => OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.JGsC 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I.nx0 (fun X : AA => X) A Kc rho a) rho tp HKc Hokl Hokpl).
  - intros rhoX tr ms md a Hsp HJG Hpl. rewrite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.NX1_0.
    exact (grant_Jo 0%nat st0 2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I.nx0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I.Hnx_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I.NXG_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.R11_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSecI.FC1_0 A Kc rho rhoX tp tr ms md a (stopJ_stable_le _) HKc Hsp HJG Hpl).
  - intros rhoX a. change (nxS W0 st0 2) with (nxS (Wcan 0) UStopLe 2). rewrite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I.Hnx_0.
    apply (cls_split 0%nat st0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I.nx0 ok A Kc rho a (ES1g W0 st0 2) _ tp).
    + intros HC. exact (sec_ok_0h ok A Kc rho a tp HKc Hokl Hokpl HC _).
    + intros HC. exact (sec_ok_0l ok A Kc rho a tp HKc Hokl Hokpl HC _).
Qed.
End OK0.
End SpineMallocSecOK0.

(* [comment removed for export] *)
Module SpineMallocSec6IE.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV"; "PGST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I"; "C5Aa"; "C5Ab"; "C5Ba"; "C5Bb"; "CO9pa"; "CO9pb"; "D9fa"; "D9fb"; "D9qa"; "D9qb"; "U7a"; "U7b"; "U8a"; "U8b"; "U9a"; "U9b"; "E9fa"; "E9fb"; "E9pa"; "E9pb"; "E9qa"; "E9qb"; "ET7a"; "ET7b"; "ET8a"; "ET8b"; "FFfa"; "FFfb"; "FFqa"; "FFqb"; "Y6Aa"; "Y6Ab"; "Y6Ba"; "Y6Bb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx0.

Lemma NXE6Aa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS10A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Aa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S10Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2eG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Aa 1 (SLit 0)] [mkVNA Y6Aa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run6Aa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run6Aa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE6Ba_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS12A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Ba_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S12Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S30G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Ba 1 (SLit 0)] [mkVNA Y6Ba 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run6Ba]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run6Ba__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE7a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1aA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert7a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S1aZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S26G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U7a 1 (SLit 0)] [mkVNA ET7a 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run7a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run7a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE8a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1cA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert8a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S1cZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S28G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U8a 1 (SLit 0)] [mkVNA ET8a 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run8a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run8a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1eA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS3S8SfS5S8A1A3A3VGS0;S3S0S1S1eZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S20G0G1A3S3S0S1S22G0G1A3G2A3A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [mkVNA U9a 1 (SLit 0)] [mkVNA E9fa 0 (SLit 0); mkVNA E9pa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run9a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run9a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9qa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS14A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9qa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S14Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S24G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA CO9pa 1 (SLit 0)] [mkVNA E9qa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run9qa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run9qa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFfa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS16A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFfa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S16Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2aG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9fa 1 (SLit 0)] [mkVNA FFfa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.runFfa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.runFfa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFqa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS18A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFqa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S18Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2cG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9qa 1 (SLit 0)] [mkVNA FFqa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.runFqa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.runFqa__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Lemma NXE6Ab_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS11A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Ab_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S11Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2fG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Ab 1 (SLit 0)] [mkVNA Y6Ab 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run6Ab]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run6Ab__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE6Bb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS13A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Bb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S13Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S31G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Bb 1 (SLit 0)] [mkVNA Y6Bb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run6Bb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run6Bb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE7b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1bA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert7b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S1bZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S27G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U7b 1 (SLit 0)] [mkVNA ET7b 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run7b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run7b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE8b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1dA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert8b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S1dZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S29G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U8b 1 (SLit 0)] [mkVNA ET8b 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run8b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run8b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1fA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS3S8SfS5S8A1A3A3VGS0;S3S0S1S1fZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S21G0G1A3S3S0S1S23G0G1A3G2A3A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [mkVNA U9b 1 (SLit 0)] [mkVNA E9fb 0 (SLit 0); mkVNA E9pb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run9b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run9b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9qb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS15A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9qb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S15Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S25G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA CO9pb 1 (SLit 0)] [mkVNA E9qb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run9qb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.run9qb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFfb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS17A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFfb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S17Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2bG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9fb 1 (SLit 0)] [mkVNA FFfb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.runFfb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.runFfb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFqb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS19A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFqb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S19Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2dG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9qb 1 (SLit 0)] [mkVNA FFqb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.runFqb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I.runFqb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
End INST.
End SpineMallocSec6IE.

(* [comment removed for export] *)
Module SpineMallocSec6JE.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "rw"; "valuation"; "rl"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "None"; "length"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "DG"; "aa_Km"; "aa_sec"; "sec_chunk"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "lt"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS"; "AXK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "KcA"; "Kc_ok"; "mem_keptA"; "JL_malloc_ok"; "L_malloc_ok"; "Posts_malloc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5I"; "C5ac"; "C5bc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2"; "IMG_S"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4I.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM SpineMallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6I OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k8.SpineMallocSec6J OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSecE2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSecE3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kd.SpineMallocSec6IE.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx0.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S0S30VCST;R1A2S30S39R2A2S6F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S0S30VCST;R1A2S30S3aR2A2S6F_;F_;Fa;").

Theorem esec_tail_0ha_P : ltac2:(tb__ "0|9|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12SbSdS22S24A2M3A1S1eG3ScS22S24S2cS27VW;Vst;A3S2bS2eS2A1VCST;VXGL;R8R7A5A4R1A3S33VW;Vst;A2S29R9A1S1S3G1S8R9R1A2S8RaR1A2A3Fi;S1S3SbS1bQ8A1M4A1SaRaR1A2SaRbR1A2A3Fl;S2aVCST;VXGL;RdRdS7RbA1S7RaA1A6S16S1aSfS15S14ReA1A2A1S13ReA1A2SdS0S0A2M5S1eG5R1S31RaA1A3S2fR2ScS0S0S1cG0RdA2M6S32S1cG0S8RePcA2A2A1M7A4A2F_;Fbn;S0S4S16S26G6A1M8R1A2S19R1S17G8S18G7Z8A2A2A2A2S5S3S10G4A1S7RfS1dG0R2A2A2SeG4A1A3A1F_;Fz;S9G2S1fS2S21S2S34U0Vst;S35S25S11S36R1A1LX;RdA2R13R12R10RfA8S37R2R1A5S23S2S20R11ReRcA5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => bumpP X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : st = UStopLeOrPc -> W = []) by (intros E; discriminate E).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  eapply esec_g43 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (C5 := C5ac) (C5A := C5Aa) (C5B := C5Ba) (Y6A := Y6Aa) (Y6B := Y6Ba) (E6 := E6a) (CT6 := CT6a) (CO6 := CO6a) (T6 := T6a) (sA := s6Aa) (sB := s6Ba) (s6 := s6a)
    (R6 := R6a) (HC5A := HC5Aa_0) (HC5B := HC5Ba_0) (FBA := FBAa_0) (FBB := FBBa_0) (Cert6A := Cert6Aa_0) (Cert6B := Cert6Ba_0) (E6A := E6Aa_0) (I6A := I6Aa_0)
    (E6B := E6Ba_0) (I6B := I6Ba_0) (WC6 := WC6a_0) (DF6 := DF6a_0) (NX6 := NX6a_0) (HC6 := HC6a_0) (SK6 := SK6a_0) (FC6 := FC6a_0) (FX6 := FX6a_0) (XC6 := XC6a_0)
    (HCO6 := HCO6a_0) (WCO6 := WCO6a_0) (He6 := He6a_0) (Hchk6 := Hchk6a_0) (HT6 := HT6a_0) (FBC6 := FBC6a_0) (FBT6 := FBT6a_0) (NXC6 := NXC6a_0)
    (NXE6A := NXE6Aa_0) (ECert6A := ECert6Aa_0) (NXE6B := NXE6Ba_0) (ECert6B := ECert6Ba_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY6 tY6. rewrite HD6a_0.
  eapply esec_g44 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D6 := D6a) (U7 := U7a) (ET7 := ET7a) (CT7 := CT7a) (CO7 := CO7a) (CR7 := CR7a) (CS7 := CS7a) (CM7 := CM7a) (T7 := T7a) (s7 := s7a) (R7 := R7a) (n7 := n7a)
    (WU7 := WU7a_0) (DU7 := DU7a_0) (NXU7 := NXU7a_0) (HU7 := HU7a_0) (Cert7 := Cert7a_0) (WC7 := WC7a_0) (DF7 := DF7a_0) (NX7 := NX7a_0) (HC7 := HC7a_0) (SK7 := SK7a_0)
    (FC7 := FC7a_0) (FX7 := FX7a_0) (XC7 := XC7a_0) (HCO7 := HCO7a_0) (WCO7 := WCO7a_0) (RB7 := RB7a_0) (HCR7 := HCR7a_0) (LEN7 := LEN7a_0) (PERM_nd7 := PERM_nd7a_0)
    (PERM_lt7 := PERM_lt7a_0) (PERM_cov7 := PERM_cov7a_0) (HCS7 := HCS7a_0) (MRG7 := MRG7a_0) (HCM7 := HCM7a_0) (He7 := He7a_0) (Hchk7 := Hchk7a_0) (HT7 := HT7a_0)
    (FBC7 := FBC7a_0) (FBT7 := FBT7a_0) (NXC7 := NXC7a_0)
    (NXE7 := NXE7a_0) (ECert7 := ECert7a_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY7 tY7. rewrite HD7a_0.
  eapply esec_g45 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D7 := D7a) (U8 := U8a) (ET8 := ET8a) (CT8 := CT8a) (CO8 := CO8a) (T8 := T8a) (s8 := s8a) (R8 := R8a) (WU8 := WU8a_0) (DU8 := DU8a_0) (NXU8 := NXU8a_0)
    (HU8 := HU8a_0) (Cert8 := Cert8a_0) (WC8 := WC8a_0) (DF8 := DF8a_0) (NX8 := NX8a_0) (HC8 := HC8a_0) (SK8 := SK8a_0) (FC8 := FC8a_0) (FX8 := FX8a_0) (XC8 := XC8a_0)
    (HCO8 := HCO8a_0) (WCO8 := WCO8a_0) (He8 := He8a_0) (Hchk8 := Hchk8a_0) (HT8 := HT8a_0) (FBC8 := FBC8a_0) (FBT8 := FBT8a_0) (NXC8 := NXC8a_0)
    (NXE8 := NXE8a_0) (ECert8 := ECert8a_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY8 tY8. rewrite HD8a_0.
  eapply esec_g46 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D8 := D8a) (U9 := U9a) (E9f := E9fa) (E9p := E9pa) (CO9p := CO9pa) (E9q := E9qa) (WU9 := WU9a_0) (DU9 := DU9a_0) (NXU9 := NXU9a_0) (HU9 := HU9a_0)
    (Cert9 := Cert9a_0) (SK9 := SK9a_0) (FC9 := FC9a_0) (FX9 := FX9a_0) (FP9 := FP9a_0) (XC9 := XC9a_0) (HCO9 := HCO9a_0) (WCO9 := WCO9a_0) (Cert9q := Cert9qa_0)
    (NXE9 := NXE9a_0) (ECert9 := ECert9a_0) (NXE9q := NXE9qa_0) (ECert9q := ECert9qa_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF | |].
  - intros rY9 tY9.
    eapply esec_g47 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (E := E9fa) (S9a := S9afa) (S9b := S9bfa) (T9 := T9fa) (iM := iMfa)
    (s9 := s9fa) (R9 := R9fa) (HS9a := HS9afa_0) (HS9b := HS9bfa_0) (He9 := He9fa_0) (Hchk9 := Hchk9fa_0) (HT9 := HT9fa_0) (FBC9 := FBC9fa_0) (FBT9 := FBT9fa_0)
    (NXC9 := NXC9fa_0);
      [exact HUS | exact HKc |].
    intros rZ tZ. rewrite HD9fa_0.
    eapply esec_g48_P with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXoka_0 G2)) (blk := 131072) (dpx := DZero) (NRESe := (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) (FXP := FXPa)
    (Hdpx := (or_intror eq_refl)) (HPATH := (HPATHa_0 G2)) (partial := false) (F := FFfa) (swc := swcfa) (c1 := c1fa) (c2 := c2fa) (c4 := c4fa) (c5 := c5fa) (mc := mcfa)
    (xc := xcfa) (tyb := tybfa) (SELF := SELFfa_0) (NDF := NDFfa_0) (BNDF := BNDFfa_0) (COVF := COVFfa_0) (XFn := XFnfa_0) (BFb := BFbfa_0) (FPF := FPFfa_0)
    (FXF := FXFfa_0) (FPAR := FPARfa_0) (Hc1 := Hc1fa_0) (Hmc := Hmcfa_0) (Htyb := Htybfa_0) (Hxc := Hxcfa_0) (WCU := WCUfa_0) (SELU := SELUfa_0) (NDU := NDUfa_0)
    (BNDU := BNDUfa_0) (COVU := COVUfa_0) (W9 := W9fa_0) (D9 := D9fa_0) (XB9 := XB9fa_0) (s9 := sFfa) (ENT9 := ENT9fa_0) (SID9 := SID9fa_0) (G110 := G110fa_0)
    (DF9 := D9fa) (CertF := CertFfa_0)
      (NXEF := NXEFfa_0) (ECertF := ECertFfa_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
  - intros rY9 tY9.
    eapply esec_g47 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (E := E9qa) (S9a := S9aqa) (S9b := S9bqa) (T9 := T9qa) (iM := iMqa)
    (s9 := s9qa) (R9 := R9qa) (HS9a := HS9aqa_0) (HS9b := HS9bqa_0) (He9 := He9qa_0) (Hchk9 := Hchk9qa_0) (HT9 := HT9qa_0) (FBC9 := FBC9qa_0) (FBT9 := FBT9qa_0)
    (NXC9 := NXC9qa_0);
      [exact HUS | exact HKc |].
    intros rZ tZ. rewrite HD9qa_0.
    eapply esec_g48_P with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXoka_0 G2)) (blk := 131072) (dpx := DZero) (NRESe := (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) (FXP := FXPa)
    (Hdpx := (or_intror eq_refl)) (HPATH := (HPATHa_0 G2)) (partial := true) (F := FFqa) (swc := swcqa) (c1 := c1qa) (c2 := c2qa) (c4 := c4qa) (c5 := c5qa) (mc := mcqa)
    (xc := xcqa) (tyb := tybqa) (SELF := SELFqa_0) (NDF := NDFqa_0) (BNDF := BNDFqa_0) (COVF := COVFqa_0) (XFn := XFnqa_0) (BFb := BFbqa_0) (FPF := FPFqa_0)
    (FXF := FXFqa_0) (FPAR := FPARqa_0) (Hc1 := Hc1qa_0) (Hmc := Hmcqa_0) (Htyb := Htybqa_0) (Hxc := Hxcqa_0) (WCU := WCUqa_0) (SELU := SELUqa_0) (NDU := NDUqa_0)
    (BNDU := BNDUqa_0) (COVU := COVUqa_0) (W9 := W9qa_0) (D9 := D9qa_0) (XB9 := XB9qa_0) (s9 := sFqa) (ENT9 := ENT9qa_0) (SID9 := SID9qa_0) (G110 := G110qa_0)
    (DF9 := D9qa) (CertF := CertFqa_0)
      (NXEF := NXEFqa_0) (ECertF := ECertFqa_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
Qed.

Theorem esec_tail_0ha : ltac2:(tb__ "0|8|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12S33VW;Vst;A2S29R7A1S1S3G1S8R7R1A2S8R8R1A2A3Fi;S1S3SbS1bQ8A1M3A1SaR8R1A2SaR9R1A2A3Fl;S2aVCST;VXGL;RbRbS7R9A1S7R8A1A6S16S1aSfS15S14RcA1A2A1S13RcA1A2SdS0S0A2M4S1eG4R1S31R8A1A3S2fR2ScS0S0S1cG0RbA2M5S32S1cG0S8RcPcA2A2A1M6A4A2F_;Fbn;S0S4S16S26G5A1M7R1A2S19R1S17G7S18G6Z8A2A2A2A2S5S3S10G3A1S7RdS1dG0R2A2A2SeG3A1A3A1F_;Fz;S9G2S1fS2S21S2S34U0Vst;S35S25S11S36R1A1LX;RbA2R11R10ReRdA8S37R2R1A5S23S2S20RfRcS2dS27S2eS2A1VCST;VXGL;VW;Vst;R11R10A8A5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2. exact (esec_tail_0ha_P A Kc rho0 rho a tp0 G2 (Posts_malloc AE_A (AInvA segsA) CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.

Theorem esec_tail_0hb_P : ltac2:(tb__ "0|9|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12SbSdS22S24A2M3A1S1eG3ScS22S24S2cS27VW;Vst;A3S2bS2eS2A1VCST;VXGL;R8R7A5A4R1A3S33VW;Vst;A2S29R9A1S1S3G1S8R9R1A2S8RaR1A2A3Fi;S1S3SbS1bQ8A1M4A1SaRaR1A2SaRbR1A2A3Fl;S2aVCST;VXGL;RdRdS7RbA1S7RaA1A6S16S1aSfS15S14ReA1A2A1S13ReA1A2SdS0S0A2M5S1eG5R1S31RaA1A3S2fR2ScS0S0S1cG0RdA2M6S32S1cG0S8RePcA2A2A1M7A4A2F_;Fbn;S0S4S16S26G6A1M8R1A2S19R1S17G8S18G7Z8A2A2A2A2S5S3S10G4A1S7RfS1dG0R2A2A2SeG4A1A3A1F_;Fz;S9G2S1fS2S21S2S34U0Vst;S35S25S11R1LX;RdA2R13R12R10RfA8S38R2R1A5S23S2S20R11ReRcA5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : st = UStopLeOrPc -> W = []) by (intros E; discriminate E).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  eapply esec_g43 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (C5 := C5bc) (C5A := C5Ab) (C5B := C5Bb) (Y6A := Y6Ab) (Y6B := Y6Bb) (E6 := E6b) (CT6 := CT6b) (CO6 := CO6b) (T6 := T6b) (sA := s6Ab) (sB := s6Bb) (s6 := s6b)
    (R6 := R6b) (HC5A := HC5Ab_0) (HC5B := HC5Bb_0) (FBA := FBAb_0) (FBB := FBBb_0) (Cert6A := Cert6Ab_0) (Cert6B := Cert6Bb_0) (E6A := E6Ab_0) (I6A := I6Ab_0)
    (E6B := E6Bb_0) (I6B := I6Bb_0) (WC6 := WC6b_0) (DF6 := DF6b_0) (NX6 := NX6b_0) (HC6 := HC6b_0) (SK6 := SK6b_0) (FC6 := FC6b_0) (FX6 := FX6b_0) (XC6 := XC6b_0)
    (HCO6 := HCO6b_0) (WCO6 := WCO6b_0) (He6 := He6b_0) (Hchk6 := Hchk6b_0) (HT6 := HT6b_0) (FBC6 := FBC6b_0) (FBT6 := FBT6b_0) (NXC6 := NXC6b_0)
    (NXE6A := NXE6Ab_0) (ECert6A := ECert6Ab_0) (NXE6B := NXE6Bb_0) (ECert6B := ECert6Bb_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY6 tY6. rewrite HD6b_0.
  eapply esec_g44 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D6 := D6b) (U7 := U7b) (ET7 := ET7b) (CT7 := CT7b) (CO7 := CO7b) (CR7 := CR7b) (CS7 := CS7b) (CM7 := CM7b) (T7 := T7b) (s7 := s7b) (R7 := R7b) (n7 := n7b)
    (WU7 := WU7b_0) (DU7 := DU7b_0) (NXU7 := NXU7b_0) (HU7 := HU7b_0) (Cert7 := Cert7b_0) (WC7 := WC7b_0) (DF7 := DF7b_0) (NX7 := NX7b_0) (HC7 := HC7b_0) (SK7 := SK7b_0)
    (FC7 := FC7b_0) (FX7 := FX7b_0) (XC7 := XC7b_0) (HCO7 := HCO7b_0) (WCO7 := WCO7b_0) (RB7 := RB7b_0) (HCR7 := HCR7b_0) (LEN7 := LEN7b_0) (PERM_nd7 := PERM_nd7b_0)
    (PERM_lt7 := PERM_lt7b_0) (PERM_cov7 := PERM_cov7b_0) (HCS7 := HCS7b_0) (MRG7 := MRG7b_0) (HCM7 := HCM7b_0) (He7 := He7b_0) (Hchk7 := Hchk7b_0) (HT7 := HT7b_0)
    (FBC7 := FBC7b_0) (FBT7 := FBT7b_0) (NXC7 := NXC7b_0)
    (NXE7 := NXE7b_0) (ECert7 := ECert7b_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY7 tY7. rewrite HD7b_0.
  eapply esec_g45 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D7 := D7b) (U8 := U8b) (ET8 := ET8b) (CT8 := CT8b) (CO8 := CO8b) (T8 := T8b) (s8 := s8b) (R8 := R8b) (WU8 := WU8b_0) (DU8 := DU8b_0) (NXU8 := NXU8b_0)
    (HU8 := HU8b_0) (Cert8 := Cert8b_0) (WC8 := WC8b_0) (DF8 := DF8b_0) (NX8 := NX8b_0) (HC8 := HC8b_0) (SK8 := SK8b_0) (FC8 := FC8b_0) (FX8 := FX8b_0) (XC8 := XC8b_0)
    (HCO8 := HCO8b_0) (WCO8 := WCO8b_0) (He8 := He8b_0) (Hchk8 := Hchk8b_0) (HT8 := HT8b_0) (FBC8 := FBC8b_0) (FBT8 := FBT8b_0) (NXC8 := NXC8b_0)
    (NXE8 := NXE8b_0) (ECert8 := ECert8b_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY8 tY8. rewrite HD8b_0.
  eapply esec_g46 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D8 := D8b) (U9 := U9b) (E9f := E9fb) (E9p := E9pb) (CO9p := CO9pb) (E9q := E9qb) (WU9 := WU9b_0) (DU9 := DU9b_0) (NXU9 := NXU9b_0) (HU9 := HU9b_0)
    (Cert9 := Cert9b_0) (SK9 := SK9b_0) (FC9 := FC9b_0) (FX9 := FX9b_0) (FP9 := FP9b_0) (XC9 := XC9b_0) (HCO9 := HCO9b_0) (WCO9 := WCO9b_0) (Cert9q := Cert9qb_0)
    (NXE9 := NXE9b_0) (ECert9 := ECert9b_0) (NXE9q := NXE9qb_0) (ECert9q := ECert9qb_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF | |].
  - intros rY9 tY9.
    eapply esec_g47 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (E := E9fb) (S9a := S9afb) (S9b := S9bfb) (T9 := T9fb) (iM := iMfb)
    (s9 := s9fb) (R9 := R9fb) (HS9a := HS9afb_0) (HS9b := HS9bfb_0) (He9 := He9fb_0) (Hchk9 := Hchk9fb_0) (HT9 := HT9fb_0) (FBC9 := FBC9fb_0) (FBT9 := FBT9fb_0)
    (NXC9 := NXC9fb_0);
      [exact HUS | exact HKc |].
    intros rZ tZ. rewrite HD9fb_0.
    eapply esec_g48_P with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXokb_0 G2)) (blk := 8) (dpx := DUnknown) (NRESe := (SVar V_NRES)) (FXP := FXPb) (Hdpx := (or_introl eq_refl))
    (HPATH := (HPATHb_0 G2)) (partial := false) (F := FFfb) (swc := swcfb) (c1 := c1fb) (c2 := c2fb) (c4 := c4fb) (c5 := c5fb) (mc := mcfb) (xc := xcfb) (tyb := tybfb)
    (SELF := SELFfb_0) (NDF := NDFfb_0) (BNDF := BNDFfb_0) (COVF := COVFfb_0) (XFn := XFnfb_0) (BFb := BFbfb_0) (FPF := FPFfb_0) (FXF := FXFfb_0) (FPAR := FPARfb_0)
    (Hc1 := Hc1fb_0) (Hmc := Hmcfb_0) (Htyb := Htybfb_0) (Hxc := Hxcfb_0) (WCU := WCUfb_0) (SELU := SELUfb_0) (NDU := NDUfb_0) (BNDU := BNDUfb_0) (COVU := COVUfb_0)
    (W9 := W9fb_0) (D9 := D9fb_0) (XB9 := XB9fb_0) (s9 := sFfb) (ENT9 := ENT9fb_0) (SID9 := SID9fb_0) (G110 := G110fb_0) (DF9 := D9fb) (CertF := CertFfb_0)
      (NXEF := NXEFfb_0) (ECertF := ECertFfb_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
  - intros rY9 tY9.
    eapply esec_g47 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (E := E9qb) (S9a := S9aqb) (S9b := S9bqb) (T9 := T9qb) (iM := iMqb)
    (s9 := s9qb) (R9 := R9qb) (HS9a := HS9aqb_0) (HS9b := HS9bqb_0) (He9 := He9qb_0) (Hchk9 := Hchk9qb_0) (HT9 := HT9qb_0) (FBC9 := FBC9qb_0) (FBT9 := FBT9qb_0)
    (NXC9 := NXC9qb_0);
      [exact HUS | exact HKc |].
    intros rZ tZ. rewrite HD9qb_0.
    eapply esec_g48_P with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXokb_0 G2)) (blk := 8) (dpx := DUnknown) (NRESe := (SVar V_NRES)) (FXP := FXPb) (Hdpx := (or_introl eq_refl))
    (HPATH := (HPATHb_0 G2)) (partial := true) (F := FFqb) (swc := swcqb) (c1 := c1qb) (c2 := c2qb) (c4 := c4qb) (c5 := c5qb) (mc := mcqb) (xc := xcqb) (tyb := tybqb)
    (SELF := SELFqb_0) (NDF := NDFqb_0) (BNDF := BNDFqb_0) (COVF := COVFqb_0) (XFn := XFnqb_0) (BFb := BFbqb_0) (FPF := FPFqb_0) (FXF := FXFqb_0) (FPAR := FPARqb_0)
    (Hc1 := Hc1qb_0) (Hmc := Hmcqb_0) (Htyb := Htybqb_0) (Hxc := Hxcqb_0) (WCU := WCUqb_0) (SELU := SELUqb_0) (NDU := NDUqb_0) (BNDU := BNDUqb_0) (COVU := COVUqb_0)
    (W9 := W9qb_0) (D9 := D9qb_0) (XB9 := XB9qb_0) (s9 := sFqb) (ENT9 := ENT9qb_0) (SID9 := SID9qb_0) (G110 := G110qb_0) (DF9 := D9qb) (CertF := CertFqb_0)
      (NXEF := NXEFqb_0) (ECertF := ECertFqb_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
Qed.

Theorem esec_tail_0hb : ltac2:(tb__ "0|8|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12S33VW;Vst;A2S29R7A1S1S3G1S8R7R1A2S8R8R1A2A3Fi;S1S3SbS1bQ8A1M3A1SaR8R1A2SaR9R1A2A3Fl;S2aVCST;VXGL;RbRbS7R9A1S7R8A1A6S16S1aSfS15S14RcA1A2A1S13RcA1A2SdS0S0A2M4S1eG4R1S31R8A1A3S2fR2ScS0S0S1cG0RbA2M5S32S1cG0S8RcPcA2A2A1M6A4A2F_;Fbn;S0S4S16S26G5A1M7R1A2S19R1S17G7S18G6Z8A2A2A2A2S5S3S10G3A1S7RdS1dG0R2A2A2SeG3A1A3A1F_;Fz;S9G2S1fS2S21S2S34U0Vst;S35S25S11R1LX;RbA2R11R10ReRdA8S38R2R1A5S23S2S20RfRcS2dS27S2eS2A1VCST;VXGL;VW;Vst;R11R10A8A5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2. exact (esec_tail_0hb_P A Kc rho0 rho a tp0 G2 (Posts_malloc AE_A (AInvA segsA) CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.
End INST.
End SpineMallocSec6JE.

(* [comment removed for export] *)
Module SpineMallocSec6IEL.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_ecfgA"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "MSENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV"; "PGST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL"; "C5Aa"; "C5Ab"; "CO9pa"; "CO9pb"; "D9fa"; "D9fb"; "D9qa"; "D9qb"; "U7a"; "U7b"; "U8a"; "U8b"; "U9a"; "U9b"; "E9fa"; "E9fb"; "E9pa"; "E9pb"; "E9qa"; "E9qb"; "ET7a"; "ET7b"; "ET8a"; "ET8b"; "FFfa"; "FFfb"; "FFqa"; "FFqb"; "Y6Aa"; "Y6Ab"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx0.

Lemma NXE6Aa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS10A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Aa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S10Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2cG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Aa 1 (SLit 0)] [mkVNA Y6Aa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.run6Aa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.run6Aa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE7a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS18A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert7a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S18Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S24G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U7a 1 (SLit 0)] [mkVNA ET7a 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.run7a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.run7a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE8a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1aA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert8a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S1aZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S26G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U8a 1 (SLit 0)] [mkVNA ET8a 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.run8a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.run8a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9a_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1cA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9a_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS3S8SfS5S8A1A3A3VGS0;S3S0S1S1cZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S1eG0G1A3S3S0S1S20G0G1A3G2A3A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [mkVNA U9a 1 (SLit 0)] [mkVNA E9fa 0 (SLit 0); mkVNA E9pa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.run9a]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.run9a__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9qa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS12A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9qa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S12Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S22G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA CO9pa 1 (SLit 0)] [mkVNA E9qa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.run9qa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.run9qa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFfa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS14A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFfa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S14Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S28G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9fa 1 (SLit 0)] [mkVNA FFfa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.runFfa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.runFfa__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFqa_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS16A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFqa_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S16Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2aG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9qa 1 (SLit 0)] [mkVNA FFqa 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.runFqa]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.runFqa__runeq | vm_cast_no_check (eq_refl true)]. Qed.

Lemma NXE6Ab_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS11A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert6Ab_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S11Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2dG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA C5Ab 1 (SLit 0)] [mkVNA Y6Ab 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.run6Ab]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.run6Ab__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE7b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS19A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert7b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S19Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S25G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U7b 1 (SLit 0)] [mkVNA ET7b 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.run7b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.run7b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE8b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1bA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert8b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S1bZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S27G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA U8b 1 (SLit 0)] [mkVNA ET8b 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.run8b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.run8b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9b_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS1dA1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9b_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS3S8SfS5S8A1A3A3VGS0;S3S0S1S1dZ1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S1fG0G1A3S3S0S1S21G0G1A3G2A3A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT; PGST] GS0 [mkVNA U9b 1 (SLit 0)] [mkVNA E9fb 0 (SLit 0); mkVNA E9pb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.run9b]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.run9b__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXE9qb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS13A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECert9qb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S3S8SeS5S8A1A3VGS0;S3S0S1S13Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S23G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [MSENT] GS0 [mkVNA CO9pb 1 (SLit 0)] [mkVNA E9qb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.run9qb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.run9qb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFfb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS15A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFfb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S15Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S29G0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9fb 1 (SLit 0)] [mkVNA FFfb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.runFfb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.runFfb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
Lemma NXEFqb_0 : ltac2:(tb__ "0|0|
S7S4SdVGS0;SaSbS17A1A1A2S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ECertFqb_0 : ltac2:(tb__ "0|3|
S7S4S2ScUfa0S5S8A1VGS0;S3S0S1S17Z1S9Z0M0A1M1A3S5S0A1M2A3S3S0S1S2bG0G1A3G2A3A6S6A3"). Proof. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CfgRunA.check_ecfgA_of_runs segsA 4000%nat [] GS0 [mkVNA D9qb 1 (SLit 0)] [mkVNA FFqb 0 (SLit 0)] [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.runFqb]); [exact OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL.runFqb__runeq | vm_cast_no_check (eq_refl true)]. Qed.
End INST.
End SpineMallocSec6IEL.

(* [comment removed for export] *)
Module SpineMallocSec6JEL.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "rw"; "valuation"; "rl"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "None"; "length"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "DG"; "aa_Km"; "aa_sec"; "sec_chunk"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "div"; "lt"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS"; "AXK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "KcA"; "Kc_ok"; "mem_keptA"; "JL_malloc_ok"; "L_malloc_ok"; "Posts_malloc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3"; "JGs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IL"; "nx0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5IL"; "C5ac"; "C5bc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM"; "IMG_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2"; "IMG_S"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA GlueZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocST.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocSec4IL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require js.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM SpineMallocSec2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegD_refl OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.SecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocST OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSec3IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineMallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec4IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertMallocSU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSec5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jn.DepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CertMallocSV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.js.SpineMallocSec6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec6L OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec5IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.SpineMallocSec7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSec6IL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k8.SpineMallocSec6JL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jm.SpineMallocSecE1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocSecE2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineMallocSecE3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kd.SpineMallocSec6IEL.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section INST.
Let W : list ulink := Wcan 0. Let st : ustop := UStopLe. Let tmax : Z := 2.
Let GS0 : positive := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.SpineMallocSec3.GS nx0.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTM : ltac2:(tb__ "0|0|
S0S30VCST;R1A2S30S39R2A2S6F_;F_;Fa;").
Hypothesis HCSTS : ltac2:(tb__ "0|0|
S0S30VCST;R1A2S30S3aR2A2S6F_;F_;Fa;").

Theorem esec_tail_0la_P : ltac2:(tb__ "0|9|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12SbSdS22S24A2M3A1S1eG3ScS22S24S2cS27VW;Vst;A3S2bS2eS2A1VCST;VXGL;R8R7A5A4R1A3S33VW;Vst;A2S29R9A1S1S3G1S8R9R1A2S8RaR1A2A3Fi;S1S3SbS1bQ8A1M4A1SaRaR1A2SaRbR1A2A3Fl;S2aVCST;VXGL;RdRdS7RbA1S7RaA1A6S16S1aSfS15S14ReA1A2A1S13ReA1A2SdS0S0A2M5S1eG5R1S31RaA1A3S2fR2ScS0S0S1cG0RdA2M6S32S1cG0S8RePcA2A2A1M7A4A2F_;Fbn;S0S4S16S26G6A1M8R1A2S19R1S17G8S18G7Z8A2A2A2A2S5S3S10G4A1S7RfS1dG0R2A2A2SeG4A1A3A1F_;Fz;S9G2S1fS2S21S2S34U0Vst;S35S25S11S36R1A1LX;RdA2R13R12R10RfA8S37R2R1A5S23S2S20R11ReRcA5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => bumpP X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : st = UStopLeOrPc -> W = []) by (intros E; discriminate E).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  eapply esec_g43_low with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (C5 := C5ac) (C5A := C5Aa) (Y6A := Y6Aa) (E6 := E6a) (CT6 := CT6a) (CO6 := CO6a) (T6 := T6a) (sA := s6Aa) (s6 := s6a) (R6 := R6a) (FLOW := FLOWa_0) (HC5A := HC5Aa_0)
    (FBA := FBAa_0) (Cert6A := Cert6Aa_0) (E6A := E6Aa_0) (I6A := I6Aa_0) (WC6 := WC6a_0) (DF6 := DF6a_0) (NX6 := NX6a_0) (HC6 := HC6a_0) (SK6 := SK6a_0) (FC6 := FC6a_0)
    (FX6 := FX6a_0) (XC6 := XC6a_0) (HCO6 := HCO6a_0) (WCO6 := WCO6a_0) (He6 := He6a_0) (Hchk6 := Hchk6a_0) (HT6 := HT6a_0) (FBC6 := FBC6a_0) (FBT6 := FBT6a_0)
    (NXC6 := NXC6a_0)
    (NXE6A := NXE6Aa_0) (ECert6A := ECert6Aa_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY6 tY6. rewrite HD6a_0.
  revert rY6 tY6. apply (hint_low_etriple 0%nat st nx0 BX D6a D6La (F_g7L nx0) WD6La_0 DD6La_0 NXD6La_0 HD6La_0 FLOW6a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g7L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY6 tY6.
  eapply esec_g44 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D6 := D6La) (U7 := U7a) (ET7 := ET7a) (CT7 := CT7a) (CO7 := CO7a) (CR7 := CR7a) (CS7 := CS7a) (CM7 := CM7a) (T7 := T7a) (s7 := s7a) (R7 := R7a) (n7 := n7a)
    (WU7 := WU7a_0) (DU7 := DU7a_0) (NXU7 := NXU7a_0) (HU7 := HU7a_0) (Cert7 := Cert7a_0) (WC7 := WC7a_0) (DF7 := DF7a_0) (NX7 := NX7a_0) (HC7 := HC7a_0) (SK7 := SK7a_0)
    (FC7 := FC7a_0) (FX7 := FX7a_0) (XC7 := XC7a_0) (HCO7 := HCO7a_0) (WCO7 := WCO7a_0) (RB7 := RB7a_0) (HCR7 := HCR7a_0) (LEN7 := LEN7a_0) (PERM_nd7 := PERM_nd7a_0)
    (PERM_lt7 := PERM_lt7a_0) (PERM_cov7 := PERM_cov7a_0) (HCS7 := HCS7a_0) (MRG7 := MRG7a_0) (HCM7 := HCM7a_0) (He7 := He7a_0) (Hchk7 := Hchk7a_0) (HT7 := HT7a_0)
    (FBC7 := FBC7a_0) (FBT7 := FBT7a_0) (NXC7 := NXC7a_0)
    (NXE7 := NXE7a_0) (ECert7 := ECert7a_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY7 tY7. rewrite HD7a_0.
  revert rY7 tY7. apply (hint_low_etriple 0%nat st nx0 BX D7a D7La (F_g8L nx0) WD7La_0 DD7La_0 NXD7La_0 HD7La_0 FLOW7a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g8L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY7 tY7.
  eapply esec_g45 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D7 := D7La) (U8 := U8a) (ET8 := ET8a) (CT8 := CT8a) (CO8 := CO8a) (T8 := T8a) (s8 := s8a) (R8 := R8a) (WU8 := WU8a_0) (DU8 := DU8a_0) (NXU8 := NXU8a_0)
    (HU8 := HU8a_0) (Cert8 := Cert8a_0) (WC8 := WC8a_0) (DF8 := DF8a_0) (NX8 := NX8a_0) (HC8 := HC8a_0) (SK8 := SK8a_0) (FC8 := FC8a_0) (FX8 := FX8a_0) (XC8 := XC8a_0)
    (HCO8 := HCO8a_0) (WCO8 := WCO8a_0) (He8 := He8a_0) (Hchk8 := Hchk8a_0) (HT8 := HT8a_0) (FBC8 := FBC8a_0) (FBT8 := FBT8a_0) (NXC8 := NXC8a_0)
    (NXE8 := NXE8a_0) (ECert8 := ECert8a_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY8 tY8. rewrite HD8a_0.
  revert rY8 tY8. apply (hint_low_etriple 0%nat st nx0 BX D8a D8La (F_g9L nx0) WD8La_0 DD8La_0 NXD8La_0 HD8La_0 FLOW8a_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g9L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY8 tY8.
  eapply esec_g46 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXa) (FXP := FXPa) (PX_noband := (PXnba_0 G2))
    (D8 := D8La) (U9 := U9a) (E9f := E9fa) (E9p := E9pa) (CO9p := CO9pa) (E9q := E9qa) (WU9 := WU9a_0) (DU9 := DU9a_0) (NXU9 := NXU9a_0) (HU9 := HU9a_0)
    (Cert9 := Cert9a_0) (SK9 := SK9a_0) (FC9 := FC9a_0) (FX9 := FX9a_0) (FP9 := FP9a_0) (XC9 := XC9a_0) (HCO9 := HCO9a_0) (WCO9 := WCO9a_0) (Cert9q := Cert9qa_0)
    (NXE9 := NXE9a_0) (ECert9 := ECert9a_0) (NXE9q := NXE9qa_0) (ECert9q := ECert9qa_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF | |].
  - intros rY9 tY9.
    eapply esec_g47 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (E := E9fa) (S9a := S9afa) (S9b := S9bfa) (T9 := T9fa) (iM := iMfa)
    (s9 := s9fa) (R9 := R9fa) (HS9a := HS9afa_0) (HS9b := HS9bfa_0) (He9 := He9fa_0) (Hchk9 := Hchk9fa_0) (HT9 := HT9fa_0) (FBC9 := FBC9fa_0) (FBT9 := FBT9fa_0)
    (NXC9 := NXC9fa_0);
      [exact HUS | exact HKc |].
    intros rZ tZ. rewrite HD9fa_0.
    eapply esec_g48_P with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXoka_0 G2)) (blk := 131072) (dpx := DZero) (NRESe := (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) (FXP := FXPa)
    (Hdpx := (or_intror eq_refl)) (HPATH := (HPATHa_0 G2)) (partial := false) (F := FFfa) (swc := swcfa) (c1 := c1fa) (c2 := c2fa) (c4 := c4fa) (c5 := c5fa) (mc := mcfa)
    (xc := xcfa) (tyb := tybfa) (SELF := SELFfa_0) (NDF := NDFfa_0) (BNDF := BNDFfa_0) (COVF := COVFfa_0) (XFn := XFnfa_0) (BFb := BFbfa_0) (FPF := FPFfa_0)
    (FXF := FXFfa_0) (FPAR := FPARfa_0) (Hc1 := Hc1fa_0) (Hmc := Hmcfa_0) (Htyb := Htybfa_0) (Hxc := Hxcfa_0) (WCU := WCUfa_0) (SELU := SELUfa_0) (NDU := NDUfa_0)
    (BNDU := BNDUfa_0) (COVU := COVUfa_0) (W9 := W9fa_0) (D9 := D9fa_0) (XB9 := XB9fa_0) (s9 := sFfa) (ENT9 := ENT9fa_0) (SID9 := SID9fa_0) (G110 := G110fa_0)
    (DF9 := D9fa) (CertF := CertFfa_0)
      (NXEF := NXEFfa_0) (ECertF := ECertFfa_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
  - intros rY9 tY9.
    eapply esec_g47 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (E := E9qa) (S9a := S9aqa) (S9b := S9bqa) (T9 := T9qa) (iM := iMqa)
    (s9 := s9qa) (R9 := R9qa) (HS9a := HS9aqa_0) (HS9b := HS9bqa_0) (He9 := He9qa_0) (Hchk9 := Hchk9qa_0) (HT9 := HT9qa_0) (FBC9 := FBC9qa_0) (FBT9 := FBT9qa_0)
    (NXC9 := NXC9qa_0);
      [exact HUS | exact HKc |].
    intros rZ tZ. rewrite HD9qa_0.
    eapply esec_g48_P with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXoka_0 G2)) (blk := 131072) (dpx := DZero) (NRESe := (SAlu ALU_ADD (SVar V_NRES) (SLit 16384))) (FXP := FXPa)
    (Hdpx := (or_intror eq_refl)) (HPATH := (HPATHa_0 G2)) (partial := true) (F := FFqa) (swc := swcqa) (c1 := c1qa) (c2 := c2qa) (c4 := c4qa) (c5 := c5qa) (mc := mcqa)
    (xc := xcqa) (tyb := tybqa) (SELF := SELFqa_0) (NDF := NDFqa_0) (BNDF := BNDFqa_0) (COVF := COVFqa_0) (XFn := XFnqa_0) (BFb := BFbqa_0) (FPF := FPFqa_0)
    (FXF := FXFqa_0) (FPAR := FPARqa_0) (Hc1 := Hc1qa_0) (Hmc := Hmcqa_0) (Htyb := Htybqa_0) (Hxc := Hxcqa_0) (WCU := WCUqa_0) (SELU := SELUqa_0) (NDU := NDUqa_0)
    (BNDU := BNDUqa_0) (COVU := COVUqa_0) (W9 := W9qa_0) (D9 := D9qa_0) (XB9 := XB9qa_0) (s9 := sFqa) (ENT9 := ENT9qa_0) (SID9 := SID9qa_0) (G110 := G110qa_0)
    (DF9 := D9qa) (CertF := CertFqa_0)
      (NXEF := NXEFqa_0) (ECertF := ECertFqa_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
Qed.

Theorem esec_tail_0la : ltac2:(tb__ "0|8|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12S33VW;Vst;A2S29R7A1S1S3G1S8R7R1A2S8R8R1A2A3Fi;S1S3SbS1bQ8A1M3A1SaR8R1A2SaR9R1A2A3Fl;S2aVCST;VXGL;RbRbS7R9A1S7R8A1A6S16S1aSfS15S14RcA1A2A1S13RcA1A2SdS0S0A2M4S1eG4R1S31R8A1A3S2fR2ScS0S0S1cG0RbA2M5S32S1cG0S8RcPcA2A2A1M6A4A2F_;Fbn;S0S4S16S26G5A1M7R1A2S19R1S17G7S18G6Z8A2A2A2A2S5S3S10G3A1S7RdS1dG0R2A2A2SeG3A1A3A1F_;Fz;S9G2S1fS2S21S2S34U0Vst;S35S25S11S36R1A1LX;RbA2R11R10ReRdA8S37R2R1A5S23S2S20RfRcS2dS27S2eS2A1VCST;VXGL;VW;Vst;R11R10A8A5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2. exact (esec_tail_0la_P A Kc rho0 rho a tp0 G2 (Posts_malloc AE_A (AInvA segsA) CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.

Theorem esec_tail_0lb_P : ltac2:(tb__ "0|9|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12SbSdS22S24A2M3A1S1eG3ScS22S24S2cS27VW;Vst;A3S2bS2eS2A1VCST;VXGL;R8R7A5A4R1A3S33VW;Vst;A2S29R9A1S1S3G1S8R9R1A2S8RaR1A2A3Fi;S1S3SbS1bQ8A1M4A1SaRaR1A2SaRbR1A2A3Fl;S2aVCST;VXGL;RdRdS7RbA1S7RaA1A6S16S1aSfS15S14ReA1A2A1S13ReA1A2SdS0S0A2M5S1eG5R1S31RaA1A3S2fR2ScS0S0S1cG0RdA2M6S32S1cG0S8RePcA2A2A1M7A4A2F_;Fbn;S0S4S16S26G6A1M8R1A2S19R1S17G8S18G7Z8A2A2A2A2S5S3S10G4A1S7RfS1dG0R2A2A2SeG4A1A3A1F_;Fz;S9G2S1fS2S21S2S34U0Vst;S35S25S11R1LX;RdA2R13R12R10RfA8S38R2R1A5S23S2S20R11ReRcA5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;F_;FPosts;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2 Posts HPin HUS HKc HLw HLl HKEPT HL9 HDB RUNDEF.
  set (BX := AXK (fun X : AA => X) G2). set (Q := LQPA segsA NF rho0 tp0 Posts).
  assert (HW : st = UStopLeOrPc -> W = []) by (intros E; discriminate E).
  assert (BXg : forall X, aa_geom (BX X) = aa_geom X) by (intros X; reflexivity).
  eapply esec_g43_low with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (C5 := C5bc) (C5A := C5Ab) (Y6A := Y6Ab) (E6 := E6b) (CT6 := CT6b) (CO6 := CO6b) (T6 := T6b) (sA := s6Ab) (s6 := s6b) (R6 := R6b) (FLOW := FLOWb_0) (HC5A := HC5Ab_0)
    (FBA := FBAb_0) (Cert6A := Cert6Ab_0) (E6A := E6Ab_0) (I6A := I6Ab_0) (WC6 := WC6b_0) (DF6 := DF6b_0) (NX6 := NX6b_0) (HC6 := HC6b_0) (SK6 := SK6b_0) (FC6 := FC6b_0)
    (FX6 := FX6b_0) (XC6 := XC6b_0) (HCO6 := HCO6b_0) (WCO6 := WCO6b_0) (He6 := He6b_0) (Hchk6 := Hchk6b_0) (HT6 := HT6b_0) (FBC6 := FBC6b_0) (FBT6 := FBT6b_0)
    (NXC6 := NXC6b_0)
    (NXE6A := NXE6Ab_0) (ECert6A := ECert6Ab_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY6 tY6. rewrite HD6b_0.
  revert rY6 tY6. apply (hint_low_etriple 0%nat st nx0 BX D6b D6Lb (F_g7L nx0) WD6Lb_0 DD6Lb_0 NXD6Lb_0 HD6Lb_0 FLOW6b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g7L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY6 tY6.
  eapply esec_g44 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D6 := D6Lb) (U7 := U7b) (ET7 := ET7b) (CT7 := CT7b) (CO7 := CO7b) (CR7 := CR7b) (CS7 := CS7b) (CM7 := CM7b) (T7 := T7b) (s7 := s7b) (R7 := R7b) (n7 := n7b)
    (WU7 := WU7b_0) (DU7 := DU7b_0) (NXU7 := NXU7b_0) (HU7 := HU7b_0) (Cert7 := Cert7b_0) (WC7 := WC7b_0) (DF7 := DF7b_0) (NX7 := NX7b_0) (HC7 := HC7b_0) (SK7 := SK7b_0)
    (FC7 := FC7b_0) (FX7 := FX7b_0) (XC7 := XC7b_0) (HCO7 := HCO7b_0) (WCO7 := WCO7b_0) (RB7 := RB7b_0) (HCR7 := HCR7b_0) (LEN7 := LEN7b_0) (PERM_nd7 := PERM_nd7b_0)
    (PERM_lt7 := PERM_lt7b_0) (PERM_cov7 := PERM_cov7b_0) (HCS7 := HCS7b_0) (MRG7 := MRG7b_0) (HCM7 := HCM7b_0) (He7 := He7b_0) (Hchk7 := Hchk7b_0) (HT7 := HT7b_0)
    (FBC7 := FBC7b_0) (FBT7 := FBT7b_0) (NXC7 := NXC7b_0)
    (NXE7 := NXE7b_0) (ECert7 := ECert7b_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY7 tY7. rewrite HD7b_0.
  revert rY7 tY7. apply (hint_low_etriple 0%nat st nx0 BX D7b D7Lb (F_g8L nx0) WD7Lb_0 DD7Lb_0 NXD7Lb_0 HD7Lb_0 FLOW7b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g8L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY7 tY7.
  eapply esec_g45 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D7 := D7Lb) (U8 := U8b) (ET8 := ET8b) (CT8 := CT8b) (CO8 := CO8b) (T8 := T8b) (s8 := s8b) (R8 := R8b) (WU8 := WU8b_0) (DU8 := DU8b_0) (NXU8 := NXU8b_0)
    (HU8 := HU8b_0) (Cert8 := Cert8b_0) (WC8 := WC8b_0) (DF8 := DF8b_0) (NX8 := NX8b_0) (HC8 := HC8b_0) (SK8 := SK8b_0) (FC8 := FC8b_0) (FX8 := FX8b_0) (XC8 := XC8b_0)
    (HCO8 := HCO8b_0) (WCO8 := WCO8b_0) (He8 := He8b_0) (Hchk8 := Hchk8b_0) (HT8 := HT8b_0) (FBC8 := FBC8b_0) (FBT8 := FBT8b_0) (NXC8 := NXC8b_0)
    (NXE8 := NXE8b_0) (ECert8 := ECert8b_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF |].
  intros rY8 tY8. rewrite HD8b_0.
  revert rY8 tY8. apply (hint_low_etriple 0%nat st nx0 BX D8b D8Lb (F_g9L nx0) WD8Lb_0 DD8Lb_0 NXD8Lb_0 HD8Lb_0 FLOW8b_0
           (fun A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1 => F_g9L_hold 0%nat st tmax nx0 Hnx_0 BX A0 Kc0 r0 a0 r1 t1 tr1 md1 HJ1 HL1) A Kc rho a Q). intros rY8 tY8.
  eapply esec_g46 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (BXg := BXg) (PX := PXb) (FXP := FXPb) (PX_noband := (PXnbb_0 G2))
    (D8 := D8Lb) (U9 := U9b) (E9f := E9fb) (E9p := E9pb) (CO9p := CO9pb) (E9q := E9qb) (WU9 := WU9b_0) (DU9 := DU9b_0) (NXU9 := NXU9b_0) (HU9 := HU9b_0)
    (Cert9 := Cert9b_0) (SK9 := SK9b_0) (FC9 := FC9b_0) (FX9 := FX9b_0) (FP9 := FP9b_0) (XC9 := XC9b_0) (HCO9 := HCO9b_0) (WCO9 := WCO9b_0) (Cert9q := Cert9qb_0)
    (NXE9 := NXE9b_0) (ECert9 := ECert9b_0) (NXE9q := NXE9qb_0) (ECert9q := ECert9qb_0);
    [exact HW | exact HUS | exact HKc | exact RUNDEF | |].
  - intros rY9 tY9.
    eapply esec_g47 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (E := E9fb) (S9a := S9afb) (S9b := S9bfb) (T9 := T9fb) (iM := iMfb)
    (s9 := s9fb) (R9 := R9fb) (HS9a := HS9afb_0) (HS9b := HS9bfb_0) (He9 := He9fb_0) (Hchk9 := Hchk9fb_0) (HT9 := HT9fb_0) (FBC9 := FBC9fb_0) (FBT9 := FBT9fb_0)
    (NXC9 := NXC9fb_0);
      [exact HUS | exact HKc |].
    intros rZ tZ. rewrite HD9fb_0.
    eapply esec_g48_P with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXokb_0 G2)) (blk := 8) (dpx := DUnknown) (NRESe := (SVar V_NRES)) (FXP := FXPb) (Hdpx := (or_introl eq_refl))
    (HPATH := (HPATHb_0 G2)) (partial := false) (F := FFfb) (swc := swcfb) (c1 := c1fb) (c2 := c2fb) (c4 := c4fb) (c5 := c5fb) (mc := mcfb) (xc := xcfb) (tyb := tybfb)
    (SELF := SELFfb_0) (NDF := NDFfb_0) (BNDF := BNDFfb_0) (COVF := COVFfb_0) (XFn := XFnfb_0) (BFb := BFbfb_0) (FPF := FPFfb_0) (FXF := FXFfb_0) (FPAR := FPARfb_0)
    (Hc1 := Hc1fb_0) (Hmc := Hmcfb_0) (Htyb := Htybfb_0) (Hxc := Hxcfb_0) (WCU := WCUfb_0) (SELU := SELUfb_0) (NDU := NDUfb_0) (BNDU := BNDUfb_0) (COVU := COVUfb_0)
    (W9 := W9fb_0) (D9 := D9fb_0) (XB9 := XB9fb_0) (s9 := sFfb) (ENT9 := ENT9fb_0) (SID9 := SID9fb_0) (G110 := G110fb_0) (DF9 := D9fb) (CertF := CertFfb_0)
      (NXEF := NXEFfb_0) (ECertF := ECertFfb_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
  - intros rY9 tY9.
    eapply esec_g47 with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (BX := BX) (E := E9qb) (S9a := S9aqb) (S9b := S9bqb) (T9 := T9qb) (iM := iMqb)
    (s9 := s9qb) (R9 := R9qb) (HS9a := HS9aqb_0) (HS9b := HS9bqb_0) (He9 := He9qb_0) (Hchk9 := Hchk9qb_0) (HT9 := HT9qb_0) (FBC9 := FBC9qb_0) (FBT9 := FBT9qb_0)
    (NXC9 := NXC9qb_0);
      [exact HUS | exact HKc |].
    intros rZ tZ. rewrite HD9qb_0.
    eapply esec_g48_P with
    (nW := 0%nat) (st := st) (tmax := tmax) (nx := nx0) (Hnx := Hnx_0) (NXG := NXG_0) (CST := CST) (XGL := XGL) (HCST := HCST) (HXGL := HXGL) (HCSTM := HCSTM)
    (HCSTS := HCSTS) (BX := BX) (BXok := (BXokb_0 G2)) (blk := 8) (dpx := DUnknown) (NRESe := (SVar V_NRES)) (FXP := FXPb) (Hdpx := (or_introl eq_refl))
    (HPATH := (HPATHb_0 G2)) (partial := true) (F := FFqb) (swc := swcqb) (c1 := c1qb) (c2 := c2qb) (c4 := c4qb) (c5 := c5qb) (mc := mcqb) (xc := xcqb) (tyb := tybqb)
    (SELF := SELFqb_0) (NDF := NDFqb_0) (BNDF := BNDFqb_0) (COVF := COVFqb_0) (XFn := XFnqb_0) (BFb := BFbqb_0) (FPF := FPFqb_0) (FXF := FXFqb_0) (FPAR := FPARqb_0)
    (Hc1 := Hc1qb_0) (Hmc := Hmcqb_0) (Htyb := Htybqb_0) (Hxc := Hxcqb_0) (WCU := WCUqb_0) (SELU := SELUqb_0) (NDU := NDUqb_0) (BNDU := BNDUqb_0) (COVU := COVUqb_0)
    (W9 := W9qb_0) (D9 := D9qb_0) (XB9 := XB9qb_0) (s9 := sFqb) (ENT9 := ENT9qb_0) (SID9 := SID9qb_0) (G110 := G110qb_0) (DF9 := D9qb) (CertF := CertFqb_0)
      (NXEF := NXEFqb_0) (ECertF := ECertFqb_0);
      [exact HPin | exact HW | exact HUS | exact HKc | exact HLw | exact HLl | exact HKEPT | exact HL9 | exact HDB].
Qed.

Theorem esec_tail_0lb : ltac2:(tb__ "0|8|
S11S28S9S9S1bQ40M0A1M1SbG1A1M2S12S33VW;Vst;A2S29R7A1S1S3G1S8R7R1A2S8R8R1A2A3Fi;S1S3SbS1bQ8A1M3A1SaR8R1A2SaR9R1A2A3Fl;S2aVCST;VXGL;RbRbS7R9A1S7R8A1A6S16S1aSfS15S14RcA1A2A1S13RcA1A2SdS0S0A2M4S1eG4R1S31R8A1A3S2fR2ScS0S0S1cG0RbA2M5S32S1cG0S8RcPcA2A2A1M6A4A2F_;Fbn;S0S4S16S26G5A1M7R1A2S19R1S17G7S18G6Z8A2A2A2A2S5S3S10G3A1S7RdS1dG0R2A2A2SeG3A1A3A1F_;Fz;S9G2S1fS2S21S2S34U0Vst;S35S25S11R1LX;RbA2R11R10ReRdA8S38R2R1A5S23S2S20RfRcS2dS27S2eS2A1VCST;VXGL;VW;Vst;R11R10A8A5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Proof.
  intros A Kc rho0 rho a tp0 G2. exact (esec_tail_0lb_P A Kc rho0 rho a tp0 G2 (Posts_malloc AE_A (AInvA segsA) CST XGL W st A Kc) (or_intror (or_introl eq_refl))).
Qed.
End INST.
End SpineMallocSec6JEL.

