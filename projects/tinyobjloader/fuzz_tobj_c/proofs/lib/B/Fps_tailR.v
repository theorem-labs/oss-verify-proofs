(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "option"; "nat"; "bool"; "list"; "Some"; "length"; "negb"; "nil"; "false"; "true"; "andb"; "orb"; "pair"; "None"; "app"; "prod"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Fps_tailR"; "rcall_out"; "rcall"; "tailR_out"; "rc_Tm"; "sR1"; "sR2"; "splitsR"; "tailAR"; "RCO"; "TRO"; "XR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "la_state"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "ss_next"; "valuation"; "sstate"; "ss_lenient"; "sv"; "SLit"; "holds"; "agree_below"; "sprop_below"; "rl"; "SAlu"; "SVar"; "sobj"; "ss_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre"; "BASEF"; "runp"; "D_FPS"; "facts_fps"; "fs_ok"; "set_facts"; "zvar"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail"; "FA5"; "tailA_out"; "FA6"; "FQA"; "FA1"; "Posts_fps"; "T8"; "tailA_post"; "blA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXMerge"; "AXRebase"; "AXSelect"; "AXUnbase"; "apply_axforms"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full"; "Pre_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Stdlib.ZArith.BinInt.Z"; "add"; "of_nat"; "eqb"; "opp"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@Stdlib.Lists.List"; "forallb"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "FdEntry"; "FdChannel"; "fd_lookup"; "m_fds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@Stdlib.PArith.BinPos.Pos"; "le"; "leb"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvFw"; "ch2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates"; "obindW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_run"; "FsBelow"; "FsHold"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA"; "Kf"; "Kwr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "vXL8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "P_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region.RegionAddr"; "rip_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof"; "Posts_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "beval"; "bexp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundV SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymBytes SymObj SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform StrBytes MuslWL ListObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform MuslWLA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Musl_wl_err.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvFw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Icpt_memchr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nc.Str_strnlenA_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Icpt_strnlen_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Icpt_strnlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_istrlen OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Musl_wl_err OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFwStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvFw OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.DrvFpIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.DrvFpStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Fps_pre OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_run OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations. Import MCHAddr. Import RegionAddr. Import ISLAddr.
Close Scope bv_scope. Open Scope Z_scope.

Definition splitsR (S : sstate) : option sstate := ltac2:(tb__ "0|1|
S6fS28S28S6dVS;U0M0S2bN8b0A1A3S28S6dR1G0S2bN900A1A3LS1;A4").

Definition XR : list axform := ltac2:(tb__ "0|2|
S0S4cS4eU0M0A1S0S4cS50G0N400A2S0S4cS4fS0S2U4S0S2G0S0S2U5S0S2U6S0S2U7S0S2U1S0S2U8S0S2U9S0S2UaS0S2U2S0S2U3S0S2UbS0S2UcS0S2UdS0S2UeS0S2UfS0S2U10S8S2A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S0S4cS4dG0A1M1S0S4cG1S8S4cA1A3A3A3A3A3").

Definition sR1 (a : Z) (ES : sstate) : wsub := ltac2:(tb__ "0|0|
S0S10S3cS2aA2SdS3cS2aP10S74A4S6cPaVES;S1fS55A1A3A3").
Definition sR2 (a : Z) (ES : sstate) : wsub := ltac2:(tb__ "0|2|
SfS10S3cS2aA2M0S0G0SdS3cS2aPfS30S6eS31PaM1A1S2bS5aS36A1A1A3A4S0G0SdS3cS2aP10S2bS36A1A4S0G0SdS3cS2aP11S2bS57S5bS36Z1d0A2Va;A2A1A4S8G0A1A3A3A3S6cG1VES;S1fS55A1A3A3").

Record rcall_out := RCO { rc_E : axst; rc_ES : sstate; rc_s : wsub; rc_R : list sobj; rc_T : axst; rc_Tm : axst }.

Definition rcall (F : list sprop) (mks : sstate -> wsub) (A : axst) : option rcall_out := ltac2:(tb__ "0|a|
S1S20A1S1S14A1M0Lx;M1S35S0S4S25A1M2VF;S8G2A1A3VA;A2S20S3G0L_;M3S7SbSbS59S33S1fR1A1M4A1S76A2S7S29G4A1M5A1A2S69S26S1fVA;A1A1M6S26G4A1M7A2A2A1SeS14A1M8S1S28A1G0Lx;S1aG4A1S28S21R2R1A2S20Vmks;R2A1S5cS1S4S32A1M9A1G0Lx;S7bR2S55R1A3G9G3S7SbS7aR3S55R2R1S53S23S20S22S77A4A5S6aS26R4A1S26S1fR5A1A1A2A2A1G8S7cR2S55S75R3R1A5S20G3ScScG5S7S69S26S1fR6A1A1G7A2A1A2S7S5dS25S2eG6A1VF;A3A1A2G8G1S51S39R1VF;A2S1eA2S20G3ScG5S7S6aG7S26S1fR2A1A1A2A1A2G8S5S14S1cR7R6R4R3R2R1A6A2X3x2LTm;G8X1x2X3x2TT;X3x2LR;G8X1x2Ts;TC;LES;G8X1x2X3x2LE;G8X1x2").

Record tailR_out := TRO { tr_M4 : axst; tr_c1 : rcall_out; tr_c2 : rcall_out; tr_W0 : axst; tr_o : tailA_out }.
Definition tailAR (pre suf : list Z) (a n r : Z) (cls : list sprop) (T7 : axst) : option tailR_out := ltac2:(tb__ "0|b|
S49Va;Vn;Vr;Vcls;VT7;A5S20S3aVT7;A1S3cS57S57S58S6S3dVpre;A2A1M0Vn;A2S58S6S3dVsuf;A2A1A2S3dS3S1S16A1M1L_;M2S7SbS59Va;G0A2S38S0S4S25A1M3S47R2Vn;A2M4S0G3S34S0G3S43R2Vn;A2S0G3S45R2Vn;Vr;A3S0G3S37S8G3A1M5A3A3A3A3A3S1fR3A1A2A2A1SeS16A1M6S1S20A1G1Lx;M7S35S0G3G4S0G3S34S0G3S34S0G3S34G5A3A3A3A3R3A2S20G2ScS29S1fR1A1M8A1S7S69S26S1fR4A1A1S26G8A1A2A1A2G6S1S14A1G1Lx;M9S15S43R3Vn;A2S18Va;A1R1A3S14G9S15S43R4Vn;A2S19Va;A1S17R1A1MaA3S14G7S35S0G3S43R5Vn;A2S46Vn;Vr;VT7;A3A3GaA2S20S1S44A1G1Lx;S4aVpre;Vsuf;Vn;R5R7R1A6S44S5S16S1dR5R4R3R2R1A5A2Lo;G6X1x2LW0;G6X1x2Lc2;G6X1x2Lc1;G6X1x2X3x2LM4;G6X1x2X3x2Tlen;Tv;TT8;").
Definition tailAR_ok (pre suf : list Z) (a n r : Z) (cls : list sprop) (T7 : axst) : bool := ltac2:(tb__ "0|0|
S1S16A1S3Lx;S1bVpre;Vsuf;Va;Vn;Vr;Vcls;VT7;A7S16SaLt;S9X1x2").

Local Opaque FUEL_T.

Lemma splitsR_SPA : ltac2:(tb__ "0|0|
S40S20S28S27S4S3bQ40A1A1S66S11S1S28A1S1aS1fR5A1A1S5S28R4A2A3S3eS24R7R6R4R3R2A6S3eS24R8S21R7R6A2R5R4R3A6F_;F_;Fw;Ftp;Frho;FS2;FA;FJ;").
Proof.
  intros J A S2 rho tp w H Hsp. unfold splitsR, obindW in H.
  destruct (split_obj_at (ax_S A) 0 (SLit (-2224))) as [S1|] eqn:E1; [|discriminate].
  pose proof (SPA_split segs J rho A 0 (SLit (-2224)) S1 tp w E1 Hsp) as H1.
  pose proof (SPA_split segs J rho (ax_setS A S1) 0 (SLit (-2304)) S2 tp w H H1) as H2.
  rewrite ax_setS_setS in H2. exact H2.
Qed.

Section TailR.
Variable ok : world -> Prop.
Variable J0 : jpredA.
Variables pre suf : list Z.
Variable str : list byte.
Let MSGb : list byte := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.MSGb pre suf str.
Let Kwr : nat -> jpredA := ltac2:(tb__ "0|0|
S73VJ0;Vpre;Vsuf;Vstr;A4").
Hypothesis Hst0 : stableA segs NF J0.
Hypothesis Hfd2 : ltac2:(tb__ "0|0|
S27S4S3bQ40A1A1S4S5fA1S5eVJ0;R4R3R2R1A4S11S1S60A1S62S63R2A1S6bA2S5S60S61S6bA1A2A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HokK : ltac2:(tb__ "0|0|
S2S41S24Vok;VKwr;R1A1A3Fk;").
Hypothesis HokP : ltac2:(tb__ "0|0|
S2S7dS24Vok;VKwr;R1A1A3Fk;").
Variable rho : valuation.
Variable tp : list word.
Hypothesis Hstr : ltac2:(tb__ "0|1|
S11S4S3bQ8A1M0A1S54G0S6G0Vstr;A2S2fVrho;P3A2A3Vstr;A3").
Variables n len : Z.
Hypothesis Hn : n = Z.of_nat (length str).
Hypothesis Hlen_eq : ltac2:(tb__ "0|0|
S11S3dVlen;S57S57S58S6S3dVpre;A2A1Vn;A2S58S6S3dVsuf;A2A1A2A3").
Hypothesis Hlen : len <= 80.
Hypothesis Hpre1 : (1 <= length pre)%nat.
Let Kf : nat -> jpredA := ltac2:(tb__ "0|0|
S72VJ0;Vpre;Vsuf;Vstr;Vrho;Vtp;A6").
Let Jc : jpredA := Kf 0.
Lemma HJst : ltac2:(tb__ "0|0|
S3cS42S24R1VJc;A3Flvl;"). Proof. intros lvl. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.Kf_stable J0 pre suf str Hst0 rho tp 0 lvl). Qed.
Lemma HJok : ok_frameA segs ok Jc. Proof. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.Kf_okK ok J0 pre suf str HokK rho tp 0). Qed.
Lemma HJinv : ltac2:(tb__ "0|0|
S27S27S4S3bQ40A1A1S4S5fA1S5eVJc;R5R3R2R1A4VJc;R5R4R3R2A4F_;Fmd;Ftr;Ft;Fr2;Fr1;"). Proof. intros r1 r2 t tr md H. exact H. Qed.
Lemma HJtp : ltac2:(tb__ "0|1|
S27S4S3bQ40A1A1M0S4S5fA1S5eVJc;R4R3R2R1A4S11G0R4Vtp;A3F_;Fmd;Ftr;Ft;Fr1;"). Proof. intros r1 t tr md [H _]. exact H. Qed.

Lemma rcall_sound : ltac2:(tb__ "0|0|
S4S25A1S28S5cF_;S20S14S27S67S11S1S14A1S15R6R5R4A3S5S14R3A2A3S11S3S29S1fR5A1A1S9A3S52S25S2cR4A1R8A3S27S2dS26S1fR8A1A1R6R1A3S65S24Vok;S3eS24VJc;S17R8A1R2Vtp;A5R6A4F_;FrhoT;S65S24Vok;S3eS24VJc;R8R6Vtp;A5R5A4F_;F_;F_;F_;FQ;FrhoA;Fc;FA;Fmks;FF;").
Proof.
  intros F mks A c rhoA Q Hc HlA HF Hk. unfold rcall in Hc.
  destruct (runp [F] A) as [E|] eqn:ErunE; [|discriminate].
  destruct ((ss_pc (ax_S E) =? rip_entry) && negb (ss_lenient (ax_S E)) && (ss_next (ax_S A) <=? ss_next (ax_S E))%positive) eqn:B1; [|discriminate]. cbn [negb] in Hc.
  apply andb_prop in B1 as [B1 HnAE]. apply andb_prop in B1 as [HpcE HlE]. apply Pos.leb_le in HnAE. apply Bool.negb_true_iff in HlE.
  destruct (splitsR (ax_S E)) as [ES|] eqn:EES; [|discriminate].
  destruct (entails_frA (ax_setS E ES) Pre_rip (mks ES)) as [R|] eqn:Efr; [|discriminate].
  destruct (call_checkA (ax_setS E ES) Pre_rip (mks ES) R (map la_state Posts_rip) && (ss_next ES =? ss_next (ax_S E))%positive) eqn:B2; [|discriminate]. cbn [negb] in Hc.
  apply andb_prop in B2 as [Hchk HnES]. apply Pos.eqb_eq in HnES.
  match type of Hc with (if ?b then None else _) = _ => destruct b eqn:B3; [discriminate|] end.
  apply Bool.orb_false_iff in B3 as [B3 HbF]. apply Bool.orb_false_iff in B3 as [HlT HnET]. apply Bool.negb_false_iff in HnET. apply Pos.leb_le in HnET.
  apply Bool.negb_false_iff in HbF.
  match type of Hc with (match apply_axforms ?x ?y with _ => _ end) = _ => destruct (apply_axforms x y) as [Tm|] eqn:ETm; [|discriminate] end.
  match type of Hc with (if ?b then None else _) = _ => destruct b eqn:B4; [discriminate|] end.
  injection Hc as <-. cbn [rc_Tm].

  eapply (runp_tr ok Jc HJst [F] A E rhoA tp); [exact ErunE | exact HlA | exact HJok | constructor; [exact HF | constructor] | unfold FsBelow; cbn [forallb]; rewrite HbF; reflexivity |].
  intros rhoE HagE.

  eapply triple_conseq with (P := SPA segs Jc (ax_setS E ES) rhoE tp); [intros w Hw; exact (splitsR_SPA Jc E ES rhoE tp w EES Hw) | intros w Hw; exact Hw |].
  apply (call_soundA segs ok Jc Jc Jc Jc (ax_setS E ES) Pre_rip (mks ES) R Posts_rip _ rhoE tp Efr Hchk).
  - intros rhoc tpc. exact (region_sum ok Jc rhoc tpc HJok (HJst NF)).
  - intros tr ms md Hsm HJ. eapply HJinv; exact HJ.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HJ'. eapply HJinv; exact HJ'.
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. cbn [ax_S ax_setS] in Hag'. rewrite HnES in Hag'.
    apply (triple_pre ok _ (tpL = tp)); [intros w [Hsm HJ]; exact (HJtp _ _ _ _ HJ) | intros ->].
    assert (HagAT : agree_below (ss_next (ax_S A)) rhoA rho').
    { eapply agree_below_trans; [exact HagE | exact (agree_below_le _ _ _ _ HnAE Hag')]. }
    assert (HF' : Forall (holds rho') F) by (eapply Forall_holds_agree; [exact HagAT | exact HbF | exact HF]).
    eapply triple_conseq with (P := SPA segs Jc Tm rho' tp); [ | intros w Hw; exact Hw | exact (Hk rho' HagAT)].
    intros w Hw. apply (SPA_axforms segs Jc XR rho' _ Tm tp w ETm). apply (SPA_set_facts Jc _ F rho' tp w HF'); [|exact Hw].
    eapply forallb_below_mono; [|exact HbF]. eapply Pos.le_trans; [exact HnAE | exact HnET].
Qed.

Lemma rcall_sound_ex : ltac2:(tb__ "0|0|
S4S25A1S28S5cF_;S20S14S27S66OF_;S11S1S14A1S15R6R5R4A3S5S14R3A2A3S11S3S29S1fR5A1A1S9A3S52S25S2cR4A1R8A3S27S2dS26S1fR8A1A1R6R1A3S64S24S3eS24VJc;S17R8A1R2Vtp;A5R6A3F_;FrhoT;S64S24S3eS24VJc;R8R6Vtp;A5R5A3F_;F_;F_;F_;FQ;FrhoA;Fc;FA;Fmks;FF;").
Proof.
  intros F mks A c rhoA Q Hc HlA HF Hk. unfold rcall in Hc.
  destruct (runp [F] A) as [E|] eqn:ErunE; [|discriminate].
  destruct ((ss_pc (ax_S E) =? rip_entry) && negb (ss_lenient (ax_S E)) && (ss_next (ax_S A) <=? ss_next (ax_S E))%positive) eqn:B1; [|discriminate]. cbn [negb] in Hc.
  apply andb_prop in B1 as [B1 HnAE]. apply andb_prop in B1 as [HpcE HlE]. apply Pos.leb_le in HnAE. apply Bool.negb_true_iff in HlE.
  destruct (splitsR (ax_S E)) as [ES|] eqn:EES; [|discriminate].
  destruct (entails_frA (ax_setS E ES) Pre_rip (mks ES)) as [R|] eqn:Efr; [|discriminate].
  destruct (call_checkA (ax_setS E ES) Pre_rip (mks ES) R (map la_state Posts_rip) && (ss_next ES =? ss_next (ax_S E))%positive) eqn:B2; [|discriminate]. cbn [negb] in Hc.
  apply andb_prop in B2 as [Hchk HnES]. apply Pos.eqb_eq in HnES.
  match type of Hc with (if ?b then None else _) = _ => destruct b eqn:B3; [discriminate|] end.
  apply Bool.orb_false_iff in B3 as [B3 HbF]. apply Bool.orb_false_iff in B3 as [HlT HnET]. apply Bool.negb_false_iff in HnET. apply Pos.leb_le in HnET.
  apply Bool.negb_false_iff in HbF.
  match type of Hc with (match apply_axforms ?x ?y with _ => _ end) = _ => destruct (apply_axforms x y) as [Tm|] eqn:ETm; [|discriminate] end.
  match type of Hc with (if ?b then None else _) = _ => destruct b eqn:B4; [discriminate|] end.
  injection Hc as <-. cbn [rc_Tm].
  eapply (runp_etr Jc HJst [F] A E rhoA tp); [exact ErunE | exact HlA | constructor; [exact HF | constructor] | unfold FsBelow; cbn [forallb]; rewrite HbF; reflexivity |].
  intros rhoE HagE.
  eapply etriple_conseq with (P := SPA segs Jc (ax_setS E ES) rhoE tp); [intros w Hw; exact (splitsR_SPA Jc E ES rhoE tp w EES Hw) | intros w Hw; exact Hw |].
  apply (call_completeA segs Jc Jc Jc Jc (ax_setS E ES) Pre_rip (mks ES) R Posts_rip _ rhoE tp Efr Hchk).
  - intros rhoc tpc. exact (region_sum_ex Jc rhoc tpc (HJst NF)).
  - intros tr ms md Hsm HJ. eapply HJinv; exact HJ.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm HJ HLK HJ'. eapply HJinv; exact HJ'.
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. cbn [ax_S ax_setS] in Hag'. rewrite HnES in Hag'.
    apply (etriple_pre _ (tpL = tp)); [intros w [Hsm HJ]; exact (HJtp _ _ _ _ HJ) | intros ->].
    assert (HagAT : agree_below (ss_next (ax_S A)) rhoA rho').
    { eapply agree_below_trans; [exact HagE | exact (agree_below_le _ _ _ _ HnAE Hag')]. }
    assert (HF' : Forall (holds rho') F) by (eapply Forall_holds_agree; [exact HagAT | exact HbF | exact HF]).
    eapply etriple_conseq with (P := SPA segs Jc Tm rho' tp); [ | intros w Hw; exact Hw | exact (Hk rho' HagAT)].
    intros w Hw. apply (SPA_axforms segs Jc XR rho' _ Tm tp w ETm). apply (SPA_set_facts Jc _ F rho' tp w HF'); [|exact Hw].
    eapply forallb_below_mono; [|exact HbF]. eapply Pos.le_trans; [exact HnAE | exact HnET].
Qed.

Lemma rcall_shape : ltac2:(tb__ "0|1|
S4S25A1S28S5cF_;S20S14S11S1S14A1S15R4R3R2A3S5S14R1A2A3S12S11S3S29S1fS17R2A1A1M0A1S9A3S68S26S1fR3A1A1S26G0A1A2A2F_;Fc;FA;Fmks;FF;").
Proof.
  intros F mks A c Hc. unfold rcall in Hc.
  destruct (runp [F] A) as [E|] eqn:ErunE; [|discriminate].
  destruct ((ss_pc (ax_S E) =? rip_entry) && negb (ss_lenient (ax_S E)) && (ss_next (ax_S A) <=? ss_next (ax_S E))%positive) eqn:B1; [|discriminate]. cbn [negb] in Hc.
  apply andb_prop in B1 as [B1 HnAE]. apply Pos.leb_le in HnAE.
  destruct (splitsR (ax_S E)) as [ES|] eqn:EES; [|discriminate].
  destruct (entails_frA (ax_setS E ES) Pre_rip (mks ES)) as [R|] eqn:Efr; [|discriminate].
  destruct (call_checkA (ax_setS E ES) Pre_rip (mks ES) R (map la_state Posts_rip) && (ss_next ES =? ss_next (ax_S E))%positive) eqn:B2; [|discriminate]. cbn [negb] in Hc.
  match type of Hc with (if ?b then None else _) = _ => destruct b eqn:B3; [discriminate|] end.
  apply Bool.orb_false_iff in B3 as [B3 HbF]. apply Bool.orb_false_iff in B3 as [HlT HnET]. apply Bool.negb_false_iff in HnET. apply Pos.leb_le in HnET.
  match type of Hc with (match apply_axforms ?x ?y with _ => _ end) = _ => destruct (apply_axforms x y) as [Tm|] eqn:ETm; [|discriminate] end.
  match type of Hc with (if ?b then None else _) = _ => destruct b eqn:B4; [discriminate|] end.
  apply Bool.orb_false_iff in B4 as [HlTm HnTm]. apply Bool.negb_false_iff in HnTm. apply Pos.eqb_eq in HnTm.
  injection Hc as <-. cbn [rc_Tm]. split; [exact HlTm | rewrite HnTm; exact (Pos.le_trans _ _ _ HnAE HnET)].
Qed.

Section InstR.
Variables a r : Z.
Variable cls : list sprop.
Variable T7 : axst.
Variable o : tailR_out.
Hypothesis Hcert : ltac2:(tb__ "0|0|
S11S1S16A1S1bVpre;Vsuf;Va;Vn;Vr;Vcls;VT7;A7S5S16Vo;A2A3").
Let T8 : axst := ltac2:(tb__ "0|0|
S49Va;Vn;Vr;Vcls;VT7;A5").
Hypothesis HlT8 : ltac2:(tb__ "0|0|
S11S3S29S1fVT8;A1A1S9A3").
Hypothesis HnT8 : ltac2:(tb__ "0|0|
S68S56S26S1fVT8;A1A1A2").
Let v : positive := zvar T7.

Lemma certR : ltac2:(tb__ "0|8|
S13S20S20S13S14S14S13S14S14S13S20S20S13S44S44S12S11S3S38S0S4S25A1M0S47Vv;Vn;A2M1S0G0S34S0G0S43Vv;Vn;A2M2S0G0S45Vv;Vn;Vr;A3S0G0S37S8G0A1M3A3A3A3A3A3S1fVT8;A1M4A2SaA3S12S11S1S20A1M5S35S0G0G1S0G0S34S0G0S34S0G0S34G3A3A3A3A3VT8;A2S5S20R5A2A3S12S11S3S29S1fR5A1M6A1S9A3S12S68S26G4A1S26G6A1A2S12S11S1S14A1M7S15G2S18Va;A1R5A3S5S14R4A2A3S12S11G7S15G2S19Va;A1S17R4A1A3S5S14R3A2A3S12S11G5S35S0G0G2S46Vn;Vr;VT7;A3A3S17R3A1A2S5S20R2A2A3S11S1S44A1S4aVpre;Vsuf;Vn;Vlen;VT8;R2A6S5S44R1A2A3A2A2A2A2A2A2A2LoA;A2LW0;A2Lc2;A2Lc1;A2LM4;A2").
Proof.
  pose proof Hcert as H. unfold tailAR in H. fold v T8 in H. rewrite <- Hlen_eq in H.
  destruct ((a =? Z.of_nat (length pre)) && fs_ok [FA1 v n; BASEF; FA5 v n; FA6 v n r; facts_fps] (ax_S T8)) eqn:B0; [|discriminate]. cbn [negb] in H.
  apply andb_prop in B0 as [_ Hfs].
  destruct (runp [FA1 v n; BASEF; BASEF; BASEF] T8) as [M4|] eqn:EM4; [|discriminate].
  destruct (ss_lenient (ax_S M4) || negb (ss_next (ax_S T8) <=? ss_next (ax_S M4))%positive) eqn:B1; [discriminate|].
  apply Bool.orb_false_iff in B1 as [HlM4 HnM4]. apply Bool.negb_false_iff in HnM4. apply Pos.leb_le in HnM4.
  destruct (rcall (FA5 v n) (sR1 a) M4) as [c1|] eqn:Ec1; [|discriminate].
  destruct (rcall (FA5 v n) (sR2 a) (rc_Tm c1)) as [c2|] eqn:Ec2; [|discriminate].
  destruct (runp (FA5 v n :: FQA n r T7) (rc_Tm c2)) as [W0|] eqn:EW0; [|discriminate].
  destruct (tailA_post pre suf n len T8 W0) as [oA|] eqn:EoA; [|discriminate].
  exists M4, c1, c2, W0, oA. repeat split; assumption.
Qed.

Lemma HM0 : ltac2:(tb__ "0|1|
S11S4S3bQ8A1M0A1VMSGb;SfG0S8G0A1VMSGb;A3A3"). Proof. reflexivity. Qed.
Lemma HlenM : ltac2:(tb__ "0|0|
S11S3dVlen;S58S6S3bQ8A1VMSGb;A2A1A3"). Proof. unfold MSGb. rewrite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.MSGb_len, Hlen_eq, Hn. lia. Qed.
Lemma Hlen80 : 1 <= len <= 80. Proof. pose proof Hlen. rewrite Hlen_eq, Hn in *. lia. Qed.
Lemma Hbl0 : ltac2:(tb__ "0|3|
S27S11S4S3bQ8A1M0A1M1S2fR1P3M2A2S2fVrho;G2A2A3S11G1S53S79G0S78R2A1S4bVpre;Vn;Vsuf;A3A4VMSGb;A3F_;Fr0;").
Proof. intros r0 Hr3. rewrite Hn. unfold MSGb, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.MSGb. apply blA_val. rewrite Hr3. exact Hstr. Qed.

Lemma FQA_hold : ltac2:(tb__ "0|1|
S27S52S25S2cR1A1S43Vv;Vn;A2M0A3S52S25S2cR2A1S45Vv;Vn;Vr;A3A3S52S25S2cR3A1S34A3S71R4S0S4S25A1G0S46Vn;Vr;VT7;A3A3A2F_;F_;F_;Fr0;").
Proof. intros r0 H5 H6 HB. unfold FQA. fold v. repeat (constructor; [assumption|]). constructor. Qed.
Lemma FQA_below : ltac2:(tb__ "0|1|
S3cS11S3S5dS25S2eR1A1S43Vv;Vn;A2M0A3SaA3S11S3S5dS25S2eR2A1S45Vv;Vn;Vr;A3A3SaA3S11S3S5dS25S2eR3A1S34A3SaA3S11S3S70R4S0S4S25A1G0S46Vn;Vr;VT7;A3A3A2SaA3F_;F_;F_;Fm;").
Proof. intros m H5 H6 HB. unfold FsBelow, FQA. fold v. cbn [forallb]. rewrite H5, H6, HB. reflexivity. Qed.

Theorem tailAR_sound : ltac2:(tb__ "0|0|
S27S2dS56Vrho;R1A3S65S24Vok;S3eS24VKf;U0A1VT8;R2Vtp;A5S3fS24VKwr;S6S3bQ8A1VMSGb;A2A1S56Vrho;Vtp;S48A6A4F_;Frho7;").
Proof.
  intros rho7 Hag7. destruct certR as (M4 & c1 & c2 & W0 & oA & Hfs & EM4 & HlM4 & HnM4 & Ec1 & Ec2 & EW0 & HP).
  destruct (rcall_shape _ _ _ _ Ec1) as [HlT1 HnT1]. destruct (rcall_shape _ _ _ _ Ec2) as [HlT2 HnT2].
  apply (triple_pre ok _ (FsHold rho7 [FA1 v n; BASEF; FA5 v n; FA6 v n r; facts_fps] /\ FsBelow (ss_next (ax_S T8)) [FA1 v n; BASEF; FA5 v n; FA6 v n r; facts_fps] = true));
    [intros w Hw; exact (fs_ok_sound _ _ T8 rho7 tp w Hfs Hw) | intros [HF0 HLb]].
  pose proof (Forall_inv HF0) as H1. pose proof (Forall_inv (Forall_inv_tail HF0)) as HB.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HF0))) as H5. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HF0)))) as H6.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HF0))))) as HFf.
  unfold FsBelow in HLb. cbn [forallb] in HLb.
  apply andb_prop in HLb as [B1 HLb]. apply andb_prop in HLb as [BB HLb]. apply andb_prop in HLb as [B5 HLb]. apply andb_prop in HLb as [B6 HLb]. apply andb_prop in HLb as [Bf _].
  eapply (runp_tr ok (Kf 0) HJst [FA1 v n; BASEF; BASEF; BASEF] T8 M4 rho7 tp);
    [exact EM4 | exact HlT8 | exact HJok | repeat (constructor; [assumption|]); constructor | unfold FsBelow; cbn [forallb]; rewrite B1, BB; reflexivity |].
  intros rhoM HagM.
  apply (rcall_sound (FA5 v n) (sR1 a) M4 c1 rhoM _ Ec1 HlM4); [exact (Forall_holds_agree _ _ _ _ HagM B5 H5) |].
  intros rhoT HagT.
  assert (HagMT : agree_below (ss_next (ax_S T8)) rho7 rhoT) by (eapply agree_below_trans; [exact HagM | exact (agree_below_le _ _ _ _ HnM4 HagT)]).
  apply (rcall_sound (FA5 v n) (sR2 a) (rc_Tm c1) c2 rhoT _ Ec2 HlT1); [exact (Forall_holds_agree _ _ _ _ HagMT B5 H5) |].
  intros rhoU HagU.
  assert (HagMU : agree_below (ss_next (ax_S T8)) rho7 rhoU) by (eapply agree_below_trans; [exact HagMT | exact (agree_below_le _ _ _ _ (Pos.le_trans _ _ _ HnM4 HnT1) HagU)]).
  eapply (runp_tr ok (Kf 0) HJst (FA5 v n :: FQA n r T7) (rc_Tm c2) W0 rhoU tp);
    [exact EW0 | exact HlT2 | exact HJok
    | apply FQA_hold; [exact (Forall_holds_agree _ _ _ _ HagMU B5 H5) | exact (Forall_holds_agree _ _ _ _ HagMU B6 H6) | exact (Forall_holds_agree _ _ _ _ HagMU BB HB)]
    | apply FQA_below; (apply (forallb_below_mono _ _ _ (Pos.le_trans _ _ _ HnM4 (Pos.le_trans _ _ _ HnT1 HnT2))); assumption) |].
  intros rhoW HagW.
  assert (HagMW : agree_below (ss_next (ax_S T8)) rho7 rhoW) by (eapply agree_below_trans; [exact HagMU | exact (agree_below_le _ _ _ _ (Pos.le_trans _ _ _ HnM4 (Pos.le_trans _ _ _ HnT1 HnT2)) HagW)]).
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.post_sound ok J0 pre suf str Hst0 Hfd2 HokK HokP rho tp 0 [] MSGb len pre suf n HM0 eq_refl HlenM Hlen80 Hbl0 T8 W0 oA HP HnT8 rhoW).
  - eapply agree_below_trans; [exact Hag7 | exact (agree_below_le _ _ _ _ HnT8 HagMW)].
  - exact (Forall_holds_agree _ _ _ _ HagMW Bf HFf).
Qed.

Theorem tailAR_sound_ex : ltac2:(tb__ "0|0|
S27S2dS56Vrho;R1A3S64S24S3eS24VKf;U0A1VT8;R2Vtp;A5S3fS24VKwr;S6S3bQ8A1VMSGb;A2A1S56Vrho;Vtp;S48A6A3F_;Frho7;").
Proof.
  intros rho7 Hag7. destruct certR as (M4 & c1 & c2 & W0 & oA & Hfs & EM4 & HlM4 & HnM4 & Ec1 & Ec2 & EW0 & HP).
  destruct (rcall_shape _ _ _ _ Ec1) as [HlT1 HnT1]. destruct (rcall_shape _ _ _ _ Ec2) as [HlT2 HnT2].
  apply (etriple_pre _ (FsHold rho7 [FA1 v n; BASEF; FA5 v n; FA6 v n r; facts_fps] /\ FsBelow (ss_next (ax_S T8)) [FA1 v n; BASEF; FA5 v n; FA6 v n r; facts_fps] = true));
    [intros w Hw; exact (fs_ok_sound _ _ T8 rho7 tp w Hfs Hw) | intros [HF0 HLb]].
  pose proof (Forall_inv HF0) as H1. pose proof (Forall_inv (Forall_inv_tail HF0)) as HB.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HF0))) as H5. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HF0)))) as H6.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HF0))))) as HFf.
  unfold FsBelow in HLb. cbn [forallb] in HLb.
  apply andb_prop in HLb as [B1 HLb]. apply andb_prop in HLb as [BB HLb]. apply andb_prop in HLb as [B5 HLb]. apply andb_prop in HLb as [B6 HLb]. apply andb_prop in HLb as [Bf _].
  eapply (runp_etr (Kf 0) HJst [FA1 v n; BASEF; BASEF; BASEF] T8 M4 rho7 tp);
    [exact EM4 | exact HlT8 | repeat (constructor; [assumption|]); constructor | unfold FsBelow; cbn [forallb]; rewrite B1, BB; reflexivity |].
  intros rhoM HagM.
  apply (rcall_sound_ex (FA5 v n) (sR1 a) M4 c1 rhoM _ Ec1 HlM4); [exact (Forall_holds_agree _ _ _ _ HagM B5 H5) |].
  intros rhoT HagT.
  assert (HagMT : agree_below (ss_next (ax_S T8)) rho7 rhoT) by (eapply agree_below_trans; [exact HagM | exact (agree_below_le _ _ _ _ HnM4 HagT)]).
  apply (rcall_sound_ex (FA5 v n) (sR2 a) (rc_Tm c1) c2 rhoT _ Ec2 HlT1); [exact (Forall_holds_agree _ _ _ _ HagMT B5 H5) |].
  intros rhoU HagU.
  assert (HagMU : agree_below (ss_next (ax_S T8)) rho7 rhoU) by (eapply agree_below_trans; [exact HagMT | exact (agree_below_le _ _ _ _ (Pos.le_trans _ _ _ HnM4 HnT1) HagU)]).
  eapply (runp_etr (Kf 0) HJst (FA5 v n :: FQA n r T7) (rc_Tm c2) W0 rhoU tp);
    [exact EW0 | exact HlT2
    | apply FQA_hold; [exact (Forall_holds_agree _ _ _ _ HagMU B5 H5) | exact (Forall_holds_agree _ _ _ _ HagMU B6 H6) | exact (Forall_holds_agree _ _ _ _ HagMU BB HB)]
    | apply FQA_below; (apply (forallb_below_mono _ _ _ (Pos.le_trans _ _ _ HnM4 (Pos.le_trans _ _ _ HnT1 HnT2))); assumption) |].
  intros rhoW HagW.
  assert (HagMW : agree_below (ss_next (ax_S T8)) rho7 rhoW) by (eapply agree_below_trans; [exact HagMU | exact (agree_below_le _ _ _ _ (Pos.le_trans _ _ _ HnM4 (Pos.le_trans _ _ _ HnT1 HnT2)) HagW)]).
  apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA.post_sound_ex J0 pre suf str Hst0 Hfd2 rho tp 0 [] MSGb len pre suf n HM0 eq_refl HlenM Hlen80 Hbl0 T8 W0 oA HP HnT8 rhoW).
  - eapply agree_below_trans; [exact Hag7 | exact (agree_below_le _ _ _ _ HnT8 HagMW)].
  - exact (Forall_holds_agree _ _ _ _ HagMW Bf HFf).
Qed.
End InstR.
End TailR.
