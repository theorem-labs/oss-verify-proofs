(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "rw"; "sobj"; "ss_objs"; "rl"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "mul"; "pow"; "@Corelib.Init.Datatypes"; "list"; "option"; "cons"; "bool"; "nil"; "pair"; "prod"; "true"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "FdEntry"; "in_fs"; "m_fds"; "m_fs"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_frames"; "aa_geom"; "ag_tp"; "large_live"; "small_live"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA"; "KxA"; "erase_mat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "mkEntry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvInitH.Top"; "A0_factsA"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceM"; "S_M"; "S_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR"; "std_fds"; "SHR"; "SHR2"; "Uv"; "ZARG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartArgBytes"; "ARGC"; "argv0"; "argv1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartMain"; "B0"; "QMain"; "M1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartTop"; "Bmain"; "Mmain"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvInitH"; "BHAND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.InvInitH0"; "bo_ok"; "@Stdlib.Lists.List"; "forallb"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvM"; "P0M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init"; "imgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.MainJoin"; "P0U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7"; "out18"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartHandoff"; "sheet"; "tpF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "valid_entry48"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.IfaceEx"; "classes_fresh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.InvInitF"; "band_out"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Kernel.Fork.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundI SymSoundM SymFrame SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt StepA SoundA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface IfaceEx SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.IfaceEx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvInitP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.InvInitF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lp.InvInitG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lp.InvInitL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lp.InvInitV0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lw.InvInitA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.InvInitH0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Init Placement KxA StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartArgBytes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartArgBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartReshape.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Start8M.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require os.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartTop StartMain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require og.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Start6bStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.StartBD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start8M OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.os.Start8CallB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartTop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartMain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.og.StartMainFds.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartHandoffLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require og.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvIfaceR DrvIfaceM DrvIfaceT DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartHandoff StartHandoffFacts DrvM MainJoin.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.StartHandoffStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.StartHandoffApart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.og.StartHandoffBlocks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.StartHandoffBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8CallDefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartArgF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartHandoff OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartHandoffFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.MainJoin.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma SM_bo : ltac2:(tb__ "0|0|
S0S19S4cSaS4bS18S6P1S18S6P8S1aS6A1A3A3A1SbS36S3aA1A1A3S1dA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma SU_bo : ltac2:(tb__ "0|0|
S0S19S4cSaS4bS18S6P1S18S6P4S1aS6A1A3A3A1SbS36S3bA1A1A3S1dA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition BHAND : Z := ltac2:(tb__ "0|0|
S11S11S47S44A1Z4000A2S14Z1000Z161A2A2").

Section Top.
Variables (sp brk mb : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
Hypothesis Hent : ltac2:(tb__ "0|0|
S56S50S35Vsp;Vbrk;Vmb;Vdraw;A4Vinp;A3").
Hypothesis Hinp : valid_input_either inp.
Hypothesis Hlim : lim = LIMIT.

Local Notation U := bv_unsigned.

Definition A0_factsA (Mm : Model) (B : Z) (rhoM : valuation) (tpM : list word) (A0 : AA) : Prop := ltac2:(tb__ "0|5|
S1S1eS0S1eS31R1A1S31VMm;A1A3S10S55R2VtpM;A2VB;A2S58S2eVA0;VrhoM;VtpM;R3A5F_;F_;Fmd;S1S0S5SdQ40M0S9VrhoM;P18A2A2S2aS29VA0;A1M1A1A3S1S0S5S2dG1A1SdG0S9VrhoM;P1eA2A2A3S1S0S16S1cS5S5A2M2A1S28VA0;A1S1aG2A1A3S1S1S1S10Z0M3S27VA0;A1M4A2S10G4Z10000A2A2S1S0S5S26VA0;A1G3A3S0S5S25VA0;A1G3A3A2A2S1S57VA0;A1S1S0S5S2bVA0;A1G3A3S0S5S2cVA0;A1G3A3A2A2A2A2A2A2A2").

Lemma finish : ltac2:(tb__ "0|7|
S37SeQ40M0A1M1G1G1G1G1G1G1G1G1G1G1G1G1G1S5S52S19S7S7S7S7S16G1A1M2S16S23A1M3S4eS1eS48S46Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;R19A7R18R17R16R15R14R13R12R11R10RbRfRaReRdRcA10S1eS53Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;R1aR19R18R17R16R15R14R13R12R11R10RfReRdRcRbRaR9R8R7R6R5S1bG3S33R4S34R3R2A2A4A1dS32S2eS30R2S11S47S44A1Z4000A2A2R1cR7S54R6A1S1bG3S33R5S34R4R3A2A4A6S4dSaS59R8A1SbS36R1dA1A1A3S0S5SdG0S9R9P18A2A2Z621278A3S0S5SdG0S9RaP1eA2A2S13SdG0Vsp;A2Z800000A2M4A3S2S7S7S2G2G2S2S24S24S1S32S2eS30R9S4aA2R23R3R2S1bG3S33RcS34RbRaA2A4A6S1S6S0G1S9R4R1A2S9RfR1A2A3Fi;S1S6S0S16SeQ8A1M5A1ScR4R1A2ScRfR1A2A3Fl;S1G1S3S1S10Z800c1000SdG0R1A2M6A2S12G6S11S2fG4A1Z1000A2A2A2A1S0S17G5A1S8R5R2A2S8R10R2A2A3F_;Fa;S38R9S4aR3R2R1A5A2A2A2A2LA0;A2LtpX;A2LrhoX;A2F_;F_;F_;F_;F_;TMm;Fmd0;Fms;Ftr;Ftp;FrhoM;Frho1;Frho';Frho4;Fv;Fo;Fx;Fb14;Fb13;Fb12;Fb10;Fb9;Fb8;Fb7;Fb6;Fb5;Fb4;FP;Fa2;Fa1;Ftid;FA;").
Proof.
  intros A tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp tr ms md0 Mm HS Hsp Hbo E24 E30.
  pose proof HS as (Sfds & Sfs & Slim & SMI & _).
  pose proof (geo_main sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp _ HS)
    as (HTOP & HP0 & HSB & HgT & HgC & HgD & HgF & HgPAB & HgN & HgS & HSEP).
  destruct HgF as (F1 & F2 & F3 & F4 & F5). rewrite FS_total_val in F3, F4, F5.
  destruct (fs_range_arith (U b10) (U sp - 8388608) F1 ltac:(unfold IMG_LO, IMG_HI, PG in *; lia) F3 ltac:(lia)
              ltac:(unfold Geometry.SHADOW_BAND_LO, Geometry.SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in F5; exact F5))
    as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
  set (q := fsq (U b10)) in *. set (n := fsn (U b10)) in *.
  assert (QB : Geometry.SHADOW_BAND_LO <= q /\ q + 4096 * Z.of_nat n <= Geometry.SHADOW_BAND_HI).
  { unfold Geometry.SHADOW_BAND_LO, Geometry.SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END. clear - Q5 Q7. lia. }
  destruct (ensure_band_pages A Mm n (StartTop.Bmain StartMain.B0 + 16384) q rhoM (tpF tp) tr ms md0 Hsp Q1 (proj1 QB) (proj2 QB))
    as (rhoX & tpX & HspX & RWX & RLX & OUTX & DEFX & INCX & ORGX).
  -
    intros k Hk. assert (UP : U (pageZ q k) = q + 4096 * Z.of_nat k) by (apply pageZ_u; clear - Q5 Q7 Hk; lia).
    destruct Q7 as [Q7|[Q7 Q8]].
    + apply (mi_lzlow SMI); rewrite UP; unfold Placement.SHADOW_BAND_LO, Placement.SHADOW_RW_LO_END; clear - Q5 Q7 Hk; lia.
    + apply (HBL_main sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp _ HS); rewrite UP;
        unfold Placement.SHADOW_BAND_HI; clear - Q7 Q8 Hk; lia.
  -
    intros z Hz. destruct Q7 as [Q7|[Q7 Q8]].
    + apply (mi_acclow SMI). unfold Placement.SHADOW_BAND_LO, Placement.SHADOW_RW_LO_END. clear - Q5 Q7 Hz. lia.
    + apply (mi_acchigh SMI). unfold Placement.SHADOW_RW_HI_BEG, Placement.SHADOW_BAND_HI. clear - Q7 Q8 Hz. lia.
  -
    unfold Mm. rewrite Slim, Hlim. pose proof StartHandoff.Bmain_val as BV. unfold LIMIT. clear - BV Q4. lia.
  - exact Hbo.
  -
    intros p Hp Hr z Hz.
    apply (tpF_defined sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp _ HS p Hp); [|exact Hz].
    unfold StartHandoffFacts.band_page, Geometry.LOW_SHADOW_BEG, Geometry.SHADOW_GAP_BEG, Geometry.HIGH_SHADOW_BEG, Geometry.HIGH_SHADOW_END, Geometry.PG.
    destruct (tpF_pages sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp _ HS p Hp) as [Zp|[Ep|[Ep|[Ep|Bp]]]].
    + unfold ZPAGES, PA0, PR0 in Zp. clear - Zp. lia.
    + subst p. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8CallDefs.PGB. rewrite u64_of_lit by lia. lia.
    + subst p. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8CallDefs.PGA. rewrite u64_of_lit by lia. lia.
    +   exfalso. subst p. destruct HgS as (_ & _ & _ & _ & S5). unfold FBSZ in S5.
      unfold Geometry.SHADOW_BAND_LO, Geometry.SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in S5. clear - S5 Hr Q5 Q7. lia.
    +
      destruct Hsp as [(_ & HMI & _) _]. cbn [snd cfg_model] in HMI.
      pose proof (proj1 (MI_tp_in_maps segsA _ _ HMI p Hp)) as AL. unfold page_size in AL.
      pose proof (Z.div_mod (U p) 4096 ltac:(lia)) as DP. rewrite AL, Z.add_0_r in DP.
      pose proof (Z.div_mod q 4096 ltac:(lia)) as DQ. rewrite Q1, Z.add_0_r in DQ.
      unfold Placement.SHADOW_BAND_HI in Bp. destruct Q7 as [Q7|[Q7 Q8]]; [left | right]; clear - Bp Hr Q7 DP DQ; lia.
  -
    exists rhoX, tpX, (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lw.InvInitA.A0 sp P b4 b5 b6 b8 b10 b12 b13 v rho1).
    split.
    { destruct HspX as [HsmX (HtrX & HemX & HpaidX)]. split; [exact HsmX|]. cbn [w_tr w_cfg cfg_model fst snd] in *.
      split; [exact HtrX|]. split; [exact HemX|]. unfold BHAND. clear - HpaidX Q4. lia. }
    split; [exact RWX|]. split; [exact RLX|].
    split; [intros a Ha; apply OUTX; clear - Ha Q5 Q6; fold q n in Q6; lia|].
    unfold A0_factsA.
    destruct (A0_pure (U P) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lw.InvInitA.SBz P) (U b5) (U b6) (U b8) (U b10) (U b4) (U b12) (U b13) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lw.InvInitA.STOPz rho1) (U sp) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lw.InvInitA.TOPz sp) (f0V v) 0 (repeat 0 11) HTOP)
      as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
    split.
    { intros md HMD HPD.
      apply (AInvA_X sp brk mb draw lim inp Hent Hinp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp _ HS
               rhoX q n OUTX DEFX QB); [| exact INCX | exact ORGX | exact HMD | | exact Hlim].
      - rewrite FS_frames_off_val, FS_total_val. split; [exact Q2 | exact Q3].
      - unfold BHAND in HPD. clear - HPD. lia. }
    split; [rewrite RWX, E24; exact (eq_sym P1)|].
    split; [rewrite RWX, E30; exact P2|].
    split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6 | exact P7].
Qed.

Lemma rm_keep : ltac2:(tb__ "0|6|
S7S7SeQ40M0A1S3S1S10Z800c1000M1SdG0R1A2M2A2S12G2S11S2fS13SdG0Vsp;A2Z800000A2A1Z1000A2M3A2A2A1S0S17SeQ8A1A1M4S8R3R2A2S8R4R2A2A3F_;Fa;S5S1S10Z0R1A2S12R1S15Z2Z40A2A2A2S4S12R2G1A2S10G3R2A2A2S0G4S8R5SfG0R3A2M5A2S8R6G5A2A3F_;F_;Fz;F_;FrhoX;FrhoM;").
Proof. intros rhoM rhoX OUT z Hz Hd. apply OUT. rewrite u64_of_lit by exact Hz. lia. Qed.

Lemma SHR_keep : ltac2:(tb__ "0|6|
S7S7SeQ40M0A1M1S3S1S10Z800c1000SdG0R1A2M2A2S12G2S11S2fS13SdG0Vsp;A2Z800000A2M3A1Z1000A2A2A2A1S0S17SeQ8A1A1S8R3R2A2S8R4R2A2A3F_;Fa;S0G1S9R2P1eM4A2S9R3G4A2A3S0S5SdG0S9R4G4A2A2G3A3S3dR5A1M5G5F_;F_;F_;F_;FrhoX;FrhoM;").
Proof.
  intros rhoM rhoX OUT E30 V30 [[S1 [S2 S4]] S3].
  assert (S4X : OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAP.STKP Code.segs rhoX).
  { pose proof (StartMain.sp_facts sp brk mb draw inp Hent Hinp) as (_ & Hspr & _). destruct S4 as [S4a S4b]. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAP.STKP, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol.HB in *.
    change (rw rhoX Iface.V_TOP) with (rw rhoX 30%positive). change (rw rhoM Iface.V_TOP) with (rw rhoM 30%positive) in S4a, S4b. rewrite E30. split; [exact S4a|].
    intros z Hz. specialize (S4b z Hz). unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAP.STK_LO in Hz. unfold Glue.wok_of, Glue.rd_of in *.
    rewrite (OUT (Z_to_bv 64 z)); [exact S4b|]. pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAP.HBz_le_47 _ S4a) as H47.
    rewrite u64_of_lit by lia. unfold Sh, SHADOW_OFF. pose proof (Z.div_mod (U sp - 8388608) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (U sp - 8388608) 8 ltac:(lia)). lia. }
  split; [split; [|split; [|exact S4X]]|].
  - intros a Ha. rewrite (rm_keep rhoM rhoX OUT a) by lia. exact (S1 a Ha).
  - intros a Ha. rewrite (rm_keep rhoM rhoX OUT a) by lia. exact (S2 a Ha).
  - intros z Hz. rewrite (rm_keep rhoM rhoX OUT z); [exact (S3 z Hz) | |]; unfold SHRZ, Geometry.Sh, Geometry.SHADOW_OFF in Hz; cbn in Hz; lia.
Qed.
Lemma SHR2_keep : ltac2:(tb__ "0|3|
S7S7SeQ40M0A1S3S1S10Z800c1000SdG0R1A2M1A2S12G1S11S2fS13SdG0Vsp;A2Z800000A2A1Z1000A2A2A2A1S0S17SeQ8A1A1S8R3R2A2S8R4R2A2A3F_;Fa;S3eR3A1M2G2F_;F_;FrhoX;FrhoM;").
Proof.
  intros rhoM rhoX OUT S3 z Hz. rewrite (rm_keep rhoM rhoX OUT z); [exact (S3 z Hz) | |]; unfold SHRZ2, Geometry.Sh, Geometry.SHADOW_OFF in Hz; cbn in Hz; lia.
Qed.
Lemma ZARG_keep : ltac2:(tb__ "0|5|
S7S7SeQ40M0A1M1S3S1S10Z800c1000SdG0R1A2M2A2S12G2S11S2fS13SdG0Vsp;A2M3Z800000A2A1Z1000A2A2A2A1S0S17SeQ8A1A1S8R3R2A2S8R4R2A2A3F_;Fa;S6S0G1S9R3R1A2S9R4R1A2A3Fi;S0S5S3fR4P1A2G3A3S40R5A1M4G4F_;F_;F_;F_;FrhoX;FrhoM;").
Proof.
  intros rhoM rhoX OUT RW E1 (Z1 & Z2 & Z3). unfold ZARG, Uv in *. rewrite !RW. split; [exact Z1|]. split; [exact Z2|].
  intros z Hz. rewrite (rm_keep rhoM rhoX OUT z); [exact (Z3 z Hz) | |].
  - rewrite E1 in *. unfold Geometry.Sh, Geometry.SHADOW_OFF in Hz.
    pose proof (Z.div_le_mono _ _ 8 ltac:(lia) (proj2 (conj Z1 Z2))) as D. clear - Hz Z1 Z2.
    assert (0 <= (U sp / 8 + 2147450880) / 8 * 8) by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos; [apply Z.add_nonneg_nonneg; [apply Z.div_pos|]|]|]; lia).
    assert ((U sp + bv_unsigned (rw rhoM 11%positive) - 1) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    change (2 ^ 47 / 8) with 17592186044416 in *.
    assert (((U sp + bv_unsigned (rw rhoM 11%positive) - 1) / 8 + 2147450880) / 8 * 8 <= (U sp + bv_unsigned (rw rhoM 11%positive) - 1) / 8 + 2147450880)
      by (pose proof (Z.mul_div_le ((U sp + bv_unsigned (rw rhoM 11%positive) - 1) / 8 + 2147450880) 8 ltac:(lia)); lia).
    lia.
  - right. rewrite E1 in *. unfold Geometry.Sh, Geometry.SHADOW_OFF in *.
    assert (D1 : (U sp - 8388608) / 8 = U sp / 8 - 1048576) by (replace (U sp - 8388608) with (U sp + (-1048576) * 8) by lia; rewrite Z.div_add by lia; lia).
    rewrite D1. pose proof (Z.div_mod (U sp / 8 + 2147450880) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (U sp / 8 + 2147450880) 8 ltac:(lia)) as MB.
    clear - Hz DM MB. lia.
Qed.

Theorem handoff_M_A : ltac2:(tb__ "0|2|
S49S0S5S41Vinp;A1Z2A3S45Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;R2A7S2S1eS1eS2S5S5S2S7S7S2S16SeQ40A1M0A1M1G1S2S24S24S1S32S2eS30R5R4A2S3aR3R2R8A6S1S4fS43Vinp;A1R3A2S1S0S16S1cG0S1fA2A1S21R5A1S3cA3S1S0S39S22R5A1S20Vinp;A1A3S38R5R4R3R2R1A5A2A2A2A2LA0;A2LtpM;A2LrhoM;A2LB;A2LMm;A2F_;F_;Fw;").
Proof.
  intros w HARGC HQ.
  destruct (main_handoff_M sp brk mb draw lim inp Hent Hinp ltac:(rewrite Hlim; unfold LIMIT; lia) w HARGC HQ)
    as (tid & a1 & a2 & P & b4 & b5 & b6 & b7 & b8 & b9 & b10 & b12 & b13 & b14 & x & o & v & rho4 & rho' & rho1 & tp & H).
  cbv zeta in H. destruct H as (HSPA & HP0 & U24 & U1 & U8 & U9 & U10 & U11 & U30 & RL3 & RL2 & Hsheet).
  destruct w as [tr [ms md0]].
  match type of HSPA with SPA _ _ _ ?r _ _ => set (rhoM := r) in * end.
  pose proof (StartMain.sp_facts sp brk mb draw inp Hent Hinp) as (_ & Hspr & _).
  destruct (finish S_M tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp tr ms md0 Hsheet HSPA) as (rhoX & tpX & A0' & HX & RWX & RLX & OUTX & HA0).
  - apply Forall_forall. intros ob Hob. apply (bo_ok_sound rhoM [1%positive; 8%positive]); [|exact (proj1 (forallb_forall _ _) SM_bo ob Hob)].
    intros i [<-|[<-|[]]]; unfold Uv in U1, U8; [rewrite U1; lia | rewrite U8; unfold StartArgBytes.A1o, StartArgBytes.STRo; lia].
  - unfold Uv, DrvIfaceT.TAddr.TP in U24. exact U24.
  - exact U30.
  - pose proof (Mm_fds sp brk mb draw lim inp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp _ Hsheet) as (Hfds & Hfs & _).
    eexists _, BHAND, rhoX, tpX, A0'. split; [exact HX|]. split; [|split; [exact Hfds | split; [exact Hfs | exact HA0]]].
    destruct HP0 as (P1 & P2 & P3 & (P4 & P5) & P6). unfold DrvM.P0M.
    split; [exact (SHR_keep rhoM rhoX OUTX (RWX _) U30 P1)|]. split; [rewrite RLX; exact P2|]. split; [unfold Uv in *; rewrite RWX; exact P3|].
    split; [split; [exact (ZARG_keep rhoM rhoX OUTX RWX U1 P4) | exact (SHR2_keep rhoM rhoX OUTX P5)]|].
    unfold SLK1, Uv in *. rewrite !RWX. exact P6.
Qed.

Theorem handoff_U_A : ltac2:(tb__ "0|2|
S49S3S0S5S41Vinp;A1Z2A3A1S45Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;R2A7S2S1eS1eS2S5S5S2S7S7S2S16SeQ40A1M0A1M1G1S2S24S24S1S32S2eS30R5R4A2S3bR3R2R8A6S1S51S42Vinp;A1R3A2S1S0S16S1cG0S1fA2A1S21R5A1S3cA3S1S0S39S22R5A1S20Vinp;A1A3S38R5R4R3R2R1A5A2A2A2A2LA0;A2LtpM;A2LrhoM;A2LB;A2LMm;A2F_;F_;Fw;").
Proof.
  intros w HARGC HQ.
  destruct (main_handoff_U sp brk mb draw lim inp Hent Hinp ltac:(rewrite Hlim; unfold LIMIT; lia) w HARGC HQ)
    as (tid & a1 & a2 & P & b4 & b5 & b6 & b7 & b8 & b9 & b10 & b12 & b13 & b14 & x & o & v & rho4 & rho' & rho1 & tp & H).
  cbv zeta in H. destruct H as (HSPA & HP0 & U24 & U1 & U2 & U4 & U5 & U12 & U11 & U30 & RW11 & RL2 & RL3 & Hsheet).
  destruct w as [tr [ms md0]].
  match type of HSPA with SPA _ _ _ ?r _ _ => set (rhoM := r) in * end.
  pose proof (StartMain.sp_facts sp brk mb draw inp Hent Hinp) as (_ & Hspr & _).
  destruct (finish S_U tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp tr ms md0 Hsheet HSPA) as (rhoX & tpX & A0' & HX & RWX & RLX & OUTX & HA0).
  - apply Forall_forall. intros ob Hob. apply (bo_ok_sound rhoM [1%positive; 4%positive]); [|exact (proj1 (forallb_forall _ _) SU_bo ob Hob)].
    intros i [<-|[<-|[]]]; unfold Uv in U1, U4; [rewrite U1; lia | rewrite U4; unfold StartArgBytes.STRo; lia].
  - unfold Uv, DrvIfaceT.TAddr.TP in U24. exact U24.
  - exact U30.
  - pose proof (Mm_fds sp brk mb draw lim inp tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 x o v rho4 rho' rho1 rhoM tp _ Hsheet) as (Hfds & Hfs & _).
    eexists _, BHAND, rhoX, tpX, A0'. split; [exact HX|]. split; [|split; [exact Hfds | split; [exact Hfs | exact HA0]]].
    destruct HP0 as (P0' & P1 & P2 & P3 & (P4 & P5) & P6 & P7). unfold MainJoin.P0U.
    split; [unfold Uv in *; rewrite RWX; exact P0'|].
    split; [exact (SHR_keep rhoM rhoX OUTX (RWX _) U30 P1)|]. split; [rewrite RLX; exact P2|]. split; [unfold Uv in *; rewrite RWX; exact P3|].
    split; [split; [exact (ZARG_keep rhoM rhoX OUTX RWX U1 P4) | exact (SHR2_keep rhoM rhoX OUTX P5)]|].
    split; [rewrite !RLX; exact P6|]. unfold SLK0, Uv in *. rewrite !RWX. exact P7.
Qed.
End Top.
