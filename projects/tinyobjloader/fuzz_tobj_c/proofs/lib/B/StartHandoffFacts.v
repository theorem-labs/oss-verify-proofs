(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "ex"; "True"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "sub"; "modulo"; "of_nat"; "max"; "to_nat"; "mul"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "list"; "prod"; "option"; "bool"; "Some"; "app"; "true"; "None"; "negb"; "nil"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "rm"; "sv"; "ss_objs"; "eval"; "SLit"; "image_byte"; "rl"; "SAlu"; "SVar"; "enc_bytes"; "holds"; "smatch"; "sprop"; "ss_facts"; "sstate"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "gw_sizes"; "band_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartMain"; "M1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8"; "MAIN_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "vm_limit"; "alloc_top"; "vm_init_sp"; "vm_maps"; "vm_reserved"; "FdEntry"; "Model"; "event"; "in_fs"; "m_fds"; "m_fs"; "vm_noaccess"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartReshape"; "byte_info"; "binfo_eqb"; "BNone"; "zseq"; "binfo"; "BLit"; "@Stdlib.Lists.List"; "In"; "forallb"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartTop"; "Mmain"; "Lmain"; "mS"; "GPe"; "HSe"; "LWe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "present"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartHandoff"; "ZPAGES"; "tpF"; "PA0"; "PR0"; "sheet"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "hwN"; "hwS"; "ledger"; "live_hi"; "maps_disjoint"; "ranges_apart"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "config"; "mkCfg"; "mkEntry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4"; "bandav"; "spacebeg"; "n7"; "n9"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6"; "q12x"; "n17"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "pages_rev"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start7"; "Q18"; "Wz"; "kHighMemBeg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8CallDefs"; "PGA"; "PGB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out"; "X18"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartArgBytes"; "RNDo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartHandoffFacts.Facts"; "band_page"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "init_sp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "@Corelib.Init.Peano"; "lt"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR"; "std_fds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init"; "imgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States"; "shRI_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Start8M"; "ranges_apart";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.StartHandoffApart"; "GMe"; "ZLOW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.StartHandoffBytes"; "cell_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MadviseA"; "ivs_pos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "valid_entry48"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "HIGH_SHADOW_BEG"; "HIGH_SHADOW_END"; "LOW_SHADOW_BEG"; "PG"; "SHADOW_GAP_BEG"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Kernel.Fork.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundI SymSoundM SymFrame SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvIfaceR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartHandoff.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.StartHandoffStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.StartHandoffApart OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.og.StartHandoffBlocks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.StartHandoffBytes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8CallDefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartArgF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartHandoff.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma gw_sizes_app : ltac2:(tb__ "0|3|
S17S18S13Q40A1M0G0A2M1A1M2G2S1S10S36S1cG1R2R1A3A1S7S36R2A1S36R1A1A2A3Fl2;Fl1;").
Proof. induction l1 as [|e l1 IH]; intros l2; cbn -[Z.add]; [reflexivity | rewrite IH; lia]. Qed.
Lemma gw_sizes_nonneg : ltac2:(tb__ "0|1|
S17S18S13Q40A1M0G0A2A1S6Z0S36R1A1A2Fl;").
Proof. induction l as [|e l IH]; cbn -[Z.add]; [lia|]. pose proof (urange (snd e)). lia. Qed.
Lemma gw_sizes_filter_le : ltac2:(tb__ "0|2|
S18S13Q40A1M0G0A2M1S1aF_;S17G1A1S6S36S51G1R2R1A3A1S36R1A1A2Fl;Ff;").
Proof.
  intros f l. induction l as [|e l IH]; cbn -[Z.add]; [lia|]. pose proof (urange (snd e)).
  destruct (f e); cbn -[Z.add]; lia.
Qed.
Lemma length_filter_le : forall {A} (f : A -> bool) l, (length (List.filter f l) <= length l)%nat.
Proof. intros A f l. induction l as [|e l IH]; cbn; [lia|]. destruct (f e); cbn; lia. Qed.
Lemma hwN_app : ltac2:(tb__ "0|3|
S17S18S13Q40A1M0G0A2M1A1M2G2S1S10S5fS1cG1R2R1A3A1S7S5fR2A1S5fR1A1A2A3Fl2;Fl1;").
Proof. intros l1 l2. unfold hwN. rewrite live_hi_app, length_app. lia. Qed.
Lemma hwS_app : ltac2:(tb__ "0|3|
S17S18S13Q40A1M0G0A2M1A1M2G2S1S10S60S1cG1R2R1A3A1S7S60R2A1S60R1A1A2A3Fl2;Fl1;").
Proof. intros l1 l2. unfold hwS. rewrite live_hi_app. apply gw_sizes_app. Qed.
Lemma hwN_le_length : ltac2:(tb__ "0|2|
S17S18S13Q40A1M0G0A2M1A1S6S5fR1A1ScS21G1R1A2A1A2Fl;").
Proof. intros l. unfold hwN, live_hi. pose proof (length_filter_le (live_at GAPF) l). lia. Qed.
Lemma hwS_le_sizes : ltac2:(tb__ "0|1|
S17S18S13Q40A1M0G0A2A1S6S60R1A1S36R1A1A2Fl;").
Proof. intros l. unfold hwS, live_hi. apply gw_sizes_filter_le. Qed.

Lemma ranges_apart_conv : ltac2:(tb__ "0|1|
S17S18S13Q40A1M0G0A2A1S84R1A1S64R2A1F_;Fl;").
Proof.
  induction l as [|e l IH]; cbn; intros H; [exact I|]. destruct H as [F R]. split; [|exact (IH R)].
  apply Forall_forall. intros e' He'. exact (proj1 (Forall_forall _ _) F e' He').
Qed.

Lemma live_hi_image : ltac2:(tb__ "0|2|
S1S17S18S13Q40A1M0G0A2M1A1S62S65S38A1A1S20G1A1A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma live_hi_band : ltac2:(tb__ "0|3|
S1S17S18S13Q40A1M0G0A2M1A1S62S15G1S56S15G1S55S15G1S57S20G1A1M2A3A3A3A1G2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sizes_image : gw_sizes (segments_reserved segsA) <= 0x700000.
Proof. vm_compute. discriminate. Qed.

Section Facts.
Variables (sp brk mb : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput).
Hypothesis Hent : ltac2:(tb__ "0|0|
S89S82S68Vsp;Vbrk;Vmb;Vdraw;A4Vinp;A3").
Hypothesis Hinp : valid_input_either inp.
Variables (tid a1 a2 P b4 b5 b6 b7 b8 b9 b10 b12 b13 b14 : word) (x : Z) (o : out18) (v : bool) (rho4 rho' rho1 rhoM : valuation) (tp : list word) (w : world).
Hypothesis HS : ltac2:(tb__ "0|0|
S5eVsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;Vtid;Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vb10;Vb12;Vb13;Vb14;Vx;Vo;Vv;Vrho4;Vrho';Vrho1;VrhoM;Vtp;Vw;A1d").

Local Notation m1 := (StartMain.M1 sp brk mb draw lim inp tid).
Local Notation Mm := (StartTop.Mmain m1 a1 a2 P b4 b5 b6 b7 b8 b9 x b10 o b12 b13 b14).
Local Notation Lm := (StartTop.Lmain m1 a1 a2 P b4 b5 b6 b7 b8 b9 x b10 o b12 b13 b14).
Local Notation mS1 := (StartTop.mS m1 a1 a2).
Local Notation objsS := (ss_objs (ax_S (MAIN_of v))).
Local Notation vms_ := (cfg_ms (snd (virt (tpF tp) w))).

Ltac dsheet :=
  pose proof HS as (Sfds & Sfs & Slim & SMI & Stid & Sx & G2 & G3 & HPL & HPL4 & HPL5 & HPL6 & HPL7 & HPL8 & HPL9 & HPL10 & Ho & HPL12 & HPL13 & HPL14
                    & W12 & W13 & W14 & SJ & V25 & Lr & ROK & RW1 & RL1 & H27 & H28 & H29 & H30 & H31 & H32 & H33 & H34 & H36 & H77 & H78 & H83
                    & H159 & H160 & H161 & Etp & Hsm1 & RMo & RMi & Z1 & O1 & RM & ZX & BD & V16).

Lemma mS1_facts : ltac2:(tb__ "0|d|
S0S1S17S18S13Q40M0A1M1G1A2M2A1M3S41S3cS54S39Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;Vtid;A7Va1;Va2;A3A1M4A1S65S38A1A3S0S1G3S40G4A1S15G2S16G1G1Va2;S14G0Z38e000M5A2A4S15G2S16G1G1Va1;S14G0Z10000M6A2A4S15G2S16G1G1S14G0Z2008fff7000A2S14G0Zdfff0001000A2A4S15G2S16G1G1S14G0Z8fff7000A2S14G0Z20000000000A2A4S15G2S16G1G1S14G0Z7fff7000A2S14G0Z10000000A2A4S20G2A1A3A3A3A3A3A3S0S78G4A1S0S0S6Z643000M7S12G0Va1;A2M8A2S0S2S6S7G8G6A2M9S35A2S6S34G8A2A2S6G9S3eG4A1MaA2A2A2S0S0S6G7S12G0Va2;A2MbA2S0S2S6S7GbG5A2McS35A2S6S34GbA2A2S6GcGaA2A2A2S0S0S6Z7fff80000000Vx;A2S6Vx;S9Z2Z2fA2A2A2S0S1S10SbVx;Z10A2Z0A3S0S1S10GaSaVx;Z800000A2A3S0S1S10Vx;S12G0Vsp;A2A3S0S1S10S3dG4A1Vlim;A3S1G1S3fG4A1Vsp;A3A2A2A2A2A2A2A2A2A2A2").
Proof.
  dsheet. pose proof (StartMain.M1_fields sp brk mb draw lim inp tid) as (Fh & Flz & Fmt & Fres & Fmaps & Fna & Flim & Fsb & Fbrk & Fisp & Fused & Ftid & Ffds & Ffs & _).
  pose proof (StartMain.sp_facts sp brk mb draw inp Hent Hinp) as (Hwin & Hspr & Hsp16).
  assert (Htop : init_sp_ok (m_vmmaps m1)) by (unfold init_sp_ok; rewrite Fisp; exact Hwin).
  pose proof (mS_fields m1 Flz Fmaps Fna a1 a2) as (RS & MS & NS & LS & LMS & IS & KS & SKS).
  pose proof (a1_facts m1 Fres Fmaps Fna Htop a1 G2) as (F1lo & F1band & F1top & F1al & F1free).
  pose proof (a2_facts m1 Fres Fmaps Fna Htop a1 a2 G3) as (F2lo & F2band & F2top & F2al & F2free).
  split; [rewrite RS; exact Fres|]. split; [rewrite MS; reflexivity|].
  split; [clear - Htop IS; unfold init_sp_ok in *; rewrite IS; exact Htop|].
  split; [unfold alloc_top in *; rewrite IS; repeat split; assumption|].
  split; [unfold alloc_top in *; rewrite IS; repeat split; assumption|].
  split; [lia|]. split; [rewrite Sx; exact Hsp16|]. split; [unfold alloc_top; rewrite IS, Fisp, stack_max_size_val; lia|].
  split; [exact Sx|]. split; [rewrite LMS; exact Flim | rewrite IS; exact Fisp].
Qed.

Lemma Mm_fds : ltac2:(tb__ "0|5|
S0S1S17S18S13Q40A1M0S42A2A1S46S52S39Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;Vtid;A7M1Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;Vb12;Vb13;Vb14;A10M2A1S81A3S0S1S7dS47G2A1S45Vinp;A1A3S0S1S10S3dS3cG2A1M3A1Vlim;A3S0S1G0S3fG3A1Vsp;A3S0S1S17S18G0G0A2A1M4S41G3A1S65S38A1A3S1G4S40G3A1S53G1Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;Vb12;Vb13;Vb14;A10A3A2A2A2A2A2").
Proof.
  dsheet. split; [exact Sfds|]. split; [exact Sfs|]. split; [exact Slim|]. split; [exact (mi_isp SMI)|]. split; [exact (mi_res SMI) | exact (mi_maps SMI)].
Qed.

Lemma Lmain_explicit : ltac2:(tb__ "0|7|
S1S17S18S13Q40M0A1M1G1A2M2A1S53S39Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;Vtid;A7M3Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;Vb12;Vb13;Vb14;A10S1cG2S15G2S16G1G1Vb14;S14G0Z1000A2M4A4S15G2S16G1G1Vb13;S14G0Z800000A2A4S15G2S16G1G1Vb12;S14G0Z100000A2A4S20G2A1M5A3A3A3S1cG2S75S54G3Va1;Va2;A3VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;AbS1cG2S15G2S16G1G1Vb10;S14G0S6eA2A4S15G2S16G1G1Vb8;G4A4S15G2S16G1G1Vb7;G4A4S15G2S16G1G1Vb6;S14G0Z10000A2M6A4S15G2S16G1G1Vb5;G4A4S15G2S16G1G1Vb4;S6cA4S15G2S16G1G1VP;S6bA4G5A3A3A3A3A3A3A3S15G2S16G1G1Va2;S14G0Z38e000A2A4S15G2S16G1G1Va1;G6A4S15G2S56S15G2S55S15G2S57G5A3A3A3A3A3A3A3A3A3").
Proof.
  pose proof mS1_facts as (SRES & SMAPS & _).
  unfold StartTop.Lmain, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.L24, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.L23, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.L22, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.L18, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.LmE. rewrite SMAPS. reflexivity.
Qed.

Lemma ledger_main : ltac2:(tb__ "0|3|
S1S17S18S13Q40A1M0G0A2M1A1S61S3cS52S39Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;Vtid;A7M2Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;Vb12;Vb13;Vb14;A10A1A1S1cG1S65S38A1S53G2Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;Vb12;Vb13;Vb14;A10A3A3").
Proof. pose proof Mm_fds as (_ & _ & _ & _ & R & M). unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger.ledger. rewrite R, M. reflexivity. Qed.

Lemma noaccess_pos_main : ltac2:(tb__ "0|0|
S88S48S3cS52S39Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;Vtid;A7Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;Vb12;Vb13;Vb14;A10A1A1A1").
Proof. dsheet. exact (mi_posn SMI). Qed.

Lemma maps_disjoint_main : ltac2:(tb__ "0|0|
S63S61S3cS52S39Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;Vtid;A7Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;Vb12;Vb13;Vb14;A10A1A1A1").
Proof. dsheet. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger.maps_disjoint. rewrite ledger_main. apply ranges_apart_conv. exact (mi_apart SMI). Qed.

Lemma band_main : ltac2:(tb__ "0|0|
S37S61S3cS52S39Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;Vtid;A7Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;Vb12;Vb13;Vb14;A10A1A1S35S34A3").
Proof. dsheet. rewrite ledger_main. exact (mi_band SMI). Qed.

Lemma limit_main : ltac2:(tb__ "0|1|
S0S1S10S3dS3cS52S39Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;Vtid;A7Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;Vb12;Vb13;Vb14;A10A1M0A1Vlim;A3S0S1S10S3eG0A1SaS12Q40Vsp;A2Z800000A2A3S78G0A1A2A2").
Proof.
  dsheet. split; [exact Slim|]. split; [unfold alloc_top; rewrite (mi_isp SMI), stack_max_size_val; reflexivity | exact (mi_top SMI)].
Qed.

Lemma X18_small : ltac2:(tb__ "0|8|
S0S6ScS21S18S13Q40M0A1M1G1A2M2S75S54S39Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;Vtid;A7Va1;Va2;A3VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;AbM3A2A1Z2A2S0S6S36G3A1Z4000A2G1G1S4fG2S16G1G1R2R1A4G3A3S0S2S1S10S12G0R2A2M4Z2000A3S1S10G4Z1000M5A3A2S0S6G5S12G0R3A2M6A2S0S6S7G6G4A2M7SaVx;Z800000A2A2S2S6G7S35A2S6S34G6A2A2A2A2A2F_;Fs;Fb;A2A2").
Proof.
  dsheet. pose proof mS1_facts as (SRES & SMAPS & STOP & SA1 & SA2 & Hx & H16 & Hxtop & Sx' & SLIM & SISP).
  pose proof (StartMain.M1_fields sp brk mb draw lim inp tid) as (Fh & Flz & Fmt & Fres & Fmaps & Fna & Flim & Fsb & Fbrk & Fisp & Fused & _).
  pose proof (StartMain.brk_facts sp brk mb draw inp Hent) as [Hbrk Hbal].
  pose proof (mS_fields m1 Flz Fmaps Fna a1 a2) as (RS & MS & NS & LS & LMS & IS & KS & SKS).
  assert (SNA : vm_noaccess (m_vmmaps mS1) = [(Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000)]) by (rewrite NS; reflexivity).
  assert (SBRK : 0x643000 <= bv_unsigned (vm_brk (m_vmmaps mS1)) <= 0x80643000) by (rewrite KS, Fbrk; exact Hbrk).
  assert (XF := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.X18_facts mS1 a1 a2 SRES SMAPS SNA LS STOP SA1 SA2 SBRK P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx H16 Hxtop HPL10
                 (StartTop.apart_S m1 Flz Fres Fmaps Fna ltac:(clear - STOP IS; unfold init_sp_ok in *; rewrite <- IS; exact STOP) a1 a2 G2 G3) o).
  assert (GEN : forall l, (forall b s, In (b, s) l -> bv_unsigned s = 8192 \/ bv_unsigned s = 4096) -> gw_sizes l <= 8192 * Z.of_nat (length l)).
  { clear. induction l as [|[b s] l IH]; intros H; cbn -[Z.mul Z.add Z.of_nat]; [lia|].
    rewrite Nat2Z.inj_succ. cbn [snd]. specialize (IH ltac:(intros b' s' H'; apply (H b' s'); right; exact H')).
    destruct (H b s ltac:(left; reflexivity)); lia. }
  assert (LEN2 : Z.of_nat (length (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.X18 mS1 P b4 b5 b6 b7 b8 b9 x b10 o)) <= 2).
  { clear. destruct o as [[]|[]|[] g]; cbn; lia. }
  split; [exact LEN2|]. split.
  - pose proof (GEN _ ltac:(intros b s Hin; exact (proj1 (XF b s Ho Hin)))) as G. lia.
  - intros b s Hin. destruct (XF b s Ho Hin) as (S1 & S2 & S3 & S4 & S5). unfold Start7.TOPz in S3. repeat split; try assumption.
Qed.

Lemma hwN_main : ltac2:(tb__ "0|0|
S6S5fS61S3cS52S39Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;Vtid;A7Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;Vb12;Vb13;Vb14;A10A1A1A1Z28A2").
Proof.
  rewrite ledger_main, Lmain_explicit. pose proof X18_small as (L2 & _ & _).
  rewrite !hwN_app. unfold hwN at 1. rewrite live_hi_image.
  pose proof (hwN_le_length [(b14, Z_to_bv 64 4096); (b13, Z_to_bv 64 8388608); (b12, Z_to_bv 64 1048576)]).
  pose proof (hwN_le_length (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.X18 mS1 P b4 b5 b6 b7 b8 b9 x b10 o)).
  pose proof (hwN_le_length [(b10, Z_to_bv 64 n17); (b8, Z_to_bv 64 4096); (b7, Z_to_bv 64 4096); (b6, Z_to_bv 64 65536); (b5, Z_to_bv 64 4096); (b4, n9); (P, n7)]).
  pose proof (hwN_le_length [(a2, Z_to_bv 64 0x38e000); (a1, Z_to_bv 64 0x10000); HSe; GPe; LWe]).
  cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in *. lia.
Qed.

Lemma hwS_main : ltac2:(tb__ "0|0|
S6S60S61S3cS52S39Vsp;Vbrk;Vmb;Vdraw;Vlim;Vinp;Vtid;A7Va1;Va2;VP;Vb4;Vb5;Vb6;Vb7;Vb8;Vb9;Vx;Vb10;Vo;Vb12;Vb13;Vb14;A10A1A1A1S9Z2Z26A2A2").
Proof.
  rewrite ledger_main, Lmain_explicit. pose proof X18_small as (_ & S2 & _).
  replace ([(a2, Z_to_bv 64 0x38e000); (a1, Z_to_bv 64 0x10000); HSe; GPe; LWe]) with ([(a2, Z_to_bv 64 0x38e000); (a1, Z_to_bv 64 0x10000)] ++ [HSe; GPe; LWe]) by reflexivity.
  rewrite !hwS_app. unfold hwS at 1. rewrite live_hi_image. unfold hwS at 5. rewrite live_hi_band.
  pose proof (hwS_le_sizes [(b14, Z_to_bv 64 4096); (b13, Z_to_bv 64 8388608); (b12, Z_to_bv 64 1048576)]) as A1.
  pose proof (hwS_le_sizes (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8Out.X18 mS1 P b4 b5 b6 b7 b8 b9 x b10 o)) as A2.
  pose proof (hwS_le_sizes [(b10, Z_to_bv 64 n17); (b8, Z_to_bv 64 4096); (b7, Z_to_bv 64 4096); (b6, Z_to_bv 64 65536); (b5, Z_to_bv 64 4096); (b4, n9); (P, n7)]) as A3.
  pose proof (hwS_le_sizes [(a2, Z_to_bv 64 0x38e000); (a1, Z_to_bv 64 0x10000)]) as A4.
  assert (E3 : gw_sizes [(b10, Z_to_bv 64 n17); (b8, Z_to_bv 64 4096); (b7, Z_to_bv 64 4096); (b6, Z_to_bv 64 65536); (b5, Z_to_bv 64 4096); (b4, n9); (P, n7)]
               = n17 + 4096 + 4096 + 65536 + 4096 + bv_unsigned n9 + bv_unsigned n7).
  { cbn -[Z.add bv_unsigned Z_to_bv n17]. rewrite !u64_of_lit by (unfold n17; lia). lia. }
  assert (E1 : gw_sizes [(b14, Z_to_bv 64 4096); (b13, Z_to_bv 64 8388608); (b12, Z_to_bv 64 1048576)] = 4096 + 8388608 + 1048576).
  { cbn -[Z.add bv_unsigned Z_to_bv]. rewrite !u64_of_lit by lia. lia. }
  assert (E4 : gw_sizes [(a2, Z_to_bv 64 0x38e000); (a1, Z_to_bv 64 0x10000)] = 0x38e000 + 0x10000).
  { cbn -[Z.add bv_unsigned Z_to_bv]. rewrite !u64_of_lit by lia. lia. }
  assert (N9 : bv_unsigned n9 = 0x800000) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). assert (N7 : bv_unsigned n7 = 0x2000011000) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof sizes_image. unfold n17 in *. cbn [gw_sizes] in *. lia.
Qed.

Lemma grants_main : ltac2:(tb__ "0|19|
SaS12Q40M0Vsp;A2Z800000M1A2S10S0S0S6Z643000M2S12G0Va1;A2M3A2S0S2S6S7G3Z10000M4A2M5S35A2S6S34G3A2A2S6G5R1A2A2A2S0S0S6G2S12G0Va2;A2M6A2S0S2S6S7G6Z38e000A2M7S35A2S6S34G6A2A2S6G7R1A2A2A2S0S0S1S10SbS12G0VP;A2M8Z1000M9A2Z0A3S0S6S34G8A2S6S7G8Z2000011000A2R1A2A2A2S0S1S10S12G0S6aVP;A1A2SaS7G8G4A2SbG8G4A2A2A3S0S0S6G2S12G0Vb4;A2MaA2S0S2S6S7GaG1A2MbS35A2S6S34GaA2A2S6GbR1A2A2A2S0S0S6G9S12G0Vb5;A2McA2S0S2S6S7GcG9A2MdS35A2S6S34GcA2A2S6GdR1A2A2A2S0S0S6G2S12G0Vb6;A2MeA2S0S69GeG4A2S6S7GeG4A2R1A2A2A2S0S0S6G9S12G0Vb7;A2MfA2S0S69GfG9A2S6S7GfG9A2R1A2A2A2S0S0S6G9S12G0Vb8;A2M10A2S0S69G10G9A2S6S7G10G9A2R1A2A2A2S0S0S6G2S12G0Vb10;A2M11A2S0S2S6S7G11S6eA2M12S35A2S6S34G11A2A2S6G12R1A2A2A2S0S0S2S6S7S12G0Vb12;A2M13Z100000A2M14S35A2S6S34G13A2A2S6G14R1A2A2S0S0S2S6S7S12G0Vb13;A2M15G1A2M16S35A2S6S34G15A2A2S6G16R1A2A2S0S2S6S7S12G0Vb14;A2M17G9A2M18S35A2S6S34G17A2A2S6G18R1A2A2A2A2A2A2A2A2A2A2A2A2A2A2Ttop;").
Proof.
  dsheet. pose proof mS1_facts as (SRES & SMAPS & STOP & SA1 & SA2 & Hx & H16 & Hxtop & Sx' & SLIM & SISP). cbv zeta.
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.P_facts mS1 a1 a2 SRES SMAPS STOP P HPL) as (Pal & Pceil & _ & PLB & _).
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.SB_val mS1 a1 a2 SRES SMAPS STOP P HPL) as SB.
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.b4_facts mS1 a1 a2 SRES SMAPS STOP P HPL b4 HPL4) as (C4a & C4b & C4c & _).
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.b5_facts mS1 a1 a2 SRES SMAPS STOP P HPL b4 HPL4 b5 HPL5) as (C5a & _ & C5b & C5c & _).
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.b6_facts mS1 a1 a2 SRES SMAPS STOP P HPL b4 HPL4 b5 HPL5 b6 HPL6) as (C6a & C6b & C6c & _).
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5.b7_facts mS1 a1 a2 SRES SMAPS STOP P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 HPL7) as (C7a & C7b & C7c & _).
  pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start5.b8_facts mS1 a1 a2 SRES SMAPS STOP P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 HPL7 b8 HPL8) as (C8a & C8b & C8c & _).
  pose proof (Start7.b10_facts mS1 a1 a2 SRES SMAPS STOP P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hxtop HPL10) as (CXa & CXb & CXc & _).
  unfold Start7.TOPz in CXc. rewrite Hxtop in *. rewrite <- Sx'.
  destruct SA1 as (S1a & S1b & S1c). destruct SA2 as (S2a & S2b & S2c).
  repeat match goal with |- _ /\ _ => split end; try assumption; lia.
Qed.

Lemma rho1_vals : ltac2:(tb__ "0|3|
S0S11S1S13Q40M0A1M1S23Vrho1;R1A2S23Vrho';R1A2A3Fi;S0S11S1S17S13Q8A1A1S2aVrho1;R1A2S2aVrho';R1A2A3Fl;S0S1G1S23Vrho1;P1A2Vsp;A3S0S1G1S23Vrho1;P1bA2Va1;A3S0S1G1S23Vrho1;P1cA2Va2;A3S0S1G1S23Vrho1;P1dA2VP;A3S0S1G1S23Vrho1;P1eA2S6aVP;A1M2A3S0S1S10SfZ8S12G0S23Vrho1;P1fA2A2A2S12G0G2A2A3S0S1G1S23Vrho1;P20A2Vb4;A3S0S1G1S23Vrho1;P21A2Vb5;A3S0S1G1S23Vrho1;P22A2Vb6;A3S0S1G1S23Vrho1;P24A2Vb7;A3S0S1G1S23Vrho1;P4dA2Vb8;A3S0S1G1S23Vrho1;P4eA2Vb9;A3S0S1G1S23Vrho1;P53A2Vb10;A3S0S1G1S23Vrho1;P9fA2Vb12;A3S0S1G1S23Vrho1;Pa0A2Vb13;A3S1G1S23Vrho1;Pa1A2Vb14;A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  dsheet. split; [exact RW1|]. split; [exact RL1|].
  split; [rewrite RW1, (V25 1%positive) by lia; exact (ji_sp _ _ _ _ _ _ _ SJ)|].
  rewrite !RW1. repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma main_view : ltac2:(tb__ "0|7|
S25S10S3S1S4dS49S26S3bS3aVv;A1A1A1M0R2R1A3S4bA3A1S7S12Q40M1S27Vrho1;R3A2A2R2A2S10S0S0S6Z0R1A2S8R1S9Z2Z40A2A2A2S0S4S13Q8M2A1M3G3S1S19G3A1M4S58S38S24VrhoM;A1R2A3M5S1bG3R1A2M6A3Lb;A2S4dOLx;S49G0R4R3A3S5S5S10S1G4G5S1bG3S14G2R1A2A2A3Lb;S0S1G4S24VrhoM;S14G1R1A2A2S1eG3A1A3S4G3G3S1G4S29S38S14G1R2A2A2G6A3Lb;A2A2X4dx4A2A2Tz;F_;Foff;Fbase;").
Proof.
  dsheet. intros base off Hbi. destruct w as [tr [ms md]]. rewrite virt_unfold in Hsm1, RMi. cbn [snd cfg_ms] in RMi.
  exact (handoff_view rho1 rhoM (ax_S (MAIN_of v)) tr _ _ base off Hsm1 RMi Hbi).
Qed.

Lemma main_view_zero_range : ltac2:(tb__ "0|3|
S25S17S10A1S1S1aS50S10S10S4aS49S26S3bS3aVv;A1A1A1R3R1A3S4eZ0M0A1A2Loff;R1A3S1dA3S10S4fS10R1R3A3S1S19S13Q8M1A1M2A1S58S38S24VrhoM;A1S7S12Q40S27Vrho1;R5A2A2R2A2A3S1bG2S14G1G0A2A2A3F_;Foff;F_;Foffs;Fbase;").
Proof.
  dsheet. intros base offs Hall off Hin. destruct w as [tr [ms md]]. rewrite virt_unfold in Hsm1, RMi. cbn [snd cfg_ms] in RMi.
  exact (handoff_view_zero_range rho1 rhoM (ax_S (MAIN_of v)) tr _ _ base offs Hsm1 RMi Hall off Hin).
Qed.

Lemma main_view_present_range : ltac2:(tb__ "0|1|
S25S17S10A1S1S1aS50S10S10S1fS4aS49S26S3bS3aVv;A1A1A1R3R1A3S4bA2A1Loff;R1A3S1dA3S10S4fS10R1R3A3S4S13Q8A1M0G0S1S19G0A1S58S38S24VrhoM;A1S7S12Q40S27Vrho1;R6A2A2R3A2A3S1bG0R1A2A3Lb;A2F_;Foff;F_;Foffs;Fbase;").
Proof.
  dsheet. intros base offs Hall off Hin. destruct w as [tr [ms md]]. rewrite virt_unfold in Hsm1, RMi. cbn [snd cfg_ms] in RMi.
  exact (handoff_view_present_range rho1 rhoM (ax_S (MAIN_of v)) tr _ _ base offs Hsm1 RMi Hall off Hin).
Qed.

Lemma main_cell : ltac2:(tb__ "0|5|
S25S10S10S25S1S19S18S10S25A2M0A1S87S26S3bS3aVv;A1A1A1R4R3A3S1bG0S16S10S25R2R1A4A2A3S7S12Q40S27Vrho1;R5A2M1A2R4A2S10S0S6Z0M2R1A2S0S6S7R1R4A2S9Z2Z40A2A2S22S7aR1SeR5A1A2S1S19S13Q8M3A1M4A1S58S38S24VrhoM;A1S7R3ScR2A1A2A3S1bG4S7cG4R2S2dSeR6A1G1A2S14G3G2A2A4A2A3F_;Fj;A2A2Tz;F_;Fe;Fwd;Foff;Fbase;").
Proof.
  dsheet. intros base off wd e Hci. destruct w as [tr [ms md]]. rewrite virt_unfold in Hsm1, RMi. cbn [snd cfg_ms] in RMi.
  exact (handoff_cell rho1 rhoM (ax_S (MAIN_of v)) tr _ _ base off wd e Hsm1 RMi Hci).
Qed.

Lemma main_frame : ltac2:(tb__ "0|6|
S0S13Q40M0A1M1S3S79Vrho1;S26S3bS3aVv;A1A1A1R1A3A1S1S19S13Q8M2A1M3A1M4S24VrhoM;R2A2S24Vrho1;R2A2M5A3F_;Fa;S0S10S5aR1A1S1G4S24Vrho1;S14G0R2A2A2S1bG3S14G2Z0A2A2A3F_;Fa;G1S3S5aS12G0R1A2A1A1S1G4G5S24Vrho';R2A2A3F_;Fa;A2A2").
Proof. dsheet. split; [exact RMo|]. split; [exact Z1 | exact O1]. Qed.

Lemma RI_zero_check : ltac2:(tb__ "0|1|
S1aS1S1aS50S10S10S4aS49S26S3bS3aR2A1A1A1S2bS80S2cP1eA1S28Z2000000000A1A3R1A3S4eZ0M0A1A2Loff;S4cG0U1000A2A3S1dA3Fv';").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma RI_page_zero : ltac2:(tb__ "0|3|
S10S0S6Z0M0R1A2S8R1Z1000A2A2S1S19S13Q8M1A1M2A1S58S38S24VrhoM;A1S7S7S12Q40S6aVP;A1A2S9Z2Z25A2A2R2A2A3S1bG2S14G1G0A2A2A3F_;Foff;").
Proof.
  intros off Hoff. pose proof rho1_vals as (_ & _ & _ & _ & _ & _ & H30 & _). pose proof grants_main as GM. cbv zeta in GM. destruct GM as (_ & _ & (_ & PLB & Ptop) & SB & _).
  pose proof (main_view_zero_range (SAlu ALU_ADD (SVar 30%positive) (SLit 137438953472)) (zseq 0 4096) (RI_zero_check v) off ltac:(apply In_zseq; simpl Z.of_nat; lia)) as X.
  cbn [eval] in X. rewrite H30 in X. pose proof (urange sp). pose proof (Z.mod_pos_bound (bv_unsigned P) 65536 ltac:(lia)).
  rewrite U_add_small in X by (unfold SHADOW_BAND_HI in PLB; lia). change (2 ^ 37) with 137438953472. exact X.
Qed.

Lemma tpF_pages : ltac2:(tb__ "0|3|
S13Q40M0A1M1S4fG1R1S5bVtp;A1A3S2S5aS12G0R2A2M2A1S2S1G1R2S74A3S2S1G1R2S73A3S2S1G1R2Vb13;A3S0S6Z800bc000G2A2S6S7G2Z1000A2S34A2A2A2A2A2A2F_;Fp;").
Proof.
  dsheet. pose proof mS1_facts as (SRES & SMAPS & STOP & SA1 & SA2 & Hx & H16 & Hxtop & _).
  intros p Hp. unfold tpF in Hp. rewrite Etp in Hp. apply in_app_iff in Hp as [Hp|Hp]; [|apply in_app_iff in Hp as [Hp|Hp]].
  - left. apply In_pages_rev in Hp as (k & Hk & ->). unfold pageZ, ZPAGES, PA0, PR0. rewrite u64_of_lit by lia. lia.
  - left. apply In_pages_rev in Hp as (k & Hk & ->). unfold pageZ, ZPAGES, PA0, PR0. rewrite u64_of_lit by lia. lia.
  - unfold TPmain in Hp. destruct Hp as [<-|[<-|[<-|Hp]]]; [right; left; reflexivity | right; right; left; reflexivity | right; right; right; left; reflexivity |].
    right; right; right; right. exact (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.TP18_facts mS1 a1 a2 SRES SMAPS STOP P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 x b10 Hx H16 rho' ROK p Hp).
Qed.

Definition band_page (z : Z) : Prop := ltac2:(tb__ "0|1|
S2S0S6S8cVz;A2S6S7Vz;S8dA2M0S8eA2A2S0S6S8aVz;A2S6G0S8bA2A2A2").

Lemma GM1 : ltac2:(tb__ "0|3|
S0S25S10S4fS18S25S10A2S16S25S10R2R1A4S85A3M0S10S86R1A1S3S0S6S12Q40S27Vrho1;R5A2A2M1R2A2S8R2S7G1R4A2A2A2A1M2F_;Fy;F_;Fsz;Fe;S0S25S10G0S10S0S6S6dVx;A1R1A2S8R1S72A2A2G2F_;Fy;F_;Fsz;Fe;S0S25S10G0S10S0S6Vx;R1A2S8R1S9Z2Z2fA2A2A2G2F_;Fy;F_;Fsz;Fe;S7bS30S2eVrho1;A1S31S3bS3aVv;A1A1A1A3A2A2A2").
Proof.
  dsheet. pose proof mS1_facts as (SRES & SMAPS & STOP & SA1 & SA2 & Hx & H16 & Hxtop & Sx' & SLIM & SISP).
  pose proof W12 as [W12b W12t]. pose proof W13 as [W13b W13t]. pose proof W14 as [W14b W14t].
  assert (HROK1 : OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.rhoOK mS1 a1 a2 P b4 b5 b6 b7 b8 b9 x b10 rho1).
  { apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.rhoOK_agree mS1 a1 a2 P b4 b5 b6 b7 b8 b9 x b10 200%positive rho' rho1); [lia | exact ROK | intros i Hi; apply RW1]. }
  assert (E159 : rw rho1 159%positive = b12) by (rewrite RW1; exact H159).
  assert (E160 : rw rho1 160%positive = b13) by (rewrite RW1; exact H160).
  assert (E161 : rw rho1 161%positive = b14) by (rewrite RW1; exact H161).
  split; [|split; [|split]].
  - exact (GM_low mS1 a1 a2 SRES SMAPS STOP SA1 SA2 P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx Hxtop HPL10 rho1 b12 b13 b14 HROK1 E159 E160 E161
             (conj W12b W12t) (conj W13b W13t) (conj W14b W14t)).
  - exact (GM_high mS1 a1 a2 SRES SMAPS STOP SA1 SA2 P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx Hxtop HPL10 rho1 b12 b13 b14 HROK1 E159 E160 E161
             (conj W12b W12t) (conj W13b W13t) (conj W14b W14t)).
  - exact (GM_argf mS1 a1 a2 SRES SMAPS STOP SA1 SA2 P b4 b5 b6 HPL HPL4 HPL5 HPL6 b7 b8 b9 HPL7 HPL8 HPL9 x b10 Hx Hxtop HPL10 rho1 b12 b13 b14 HROK1 E159 E160 E161
             (conj W12b W12t) (conj W13b W13t) (conj W14b W14t)).
  - destruct w as [tr [ms md]]. exact (smatch_facts segsA _ _ _ Hsm1).
Qed.

Lemma ZPAGES_zero : ltac2:(tb__ "0|2|
S10S5aR1A1S1S19S13Q8M0A1M1A1S24VrhoM;S14Q40R2A2A2S1bG1S14G0Z0A2A2A3F_;Fa;").
Proof.
  dsheet. pose proof GM1 as (HGlow1 & _ & _ & HF1). intros a Ha.
  rewrite (RMo (Z_to_bv 64 a)); [exact (Z1 a Ha)|].
  apply (main_apart_low v rho1 HF1 HGlow1). rewrite u64_of_lit by (clear -Ha; unfold ZPAGES, PA0, PR0 in Ha; lia). apply ZPAGES_ZLOW. exact Ha.
Qed.

Lemma stackshadow_zero_main : ltac2:(tb__ "0|3|
S10S0S6S6dVx;A1R1A2S8R1SdS70Vx;A1S71S7S12Q40M0Vsp;A2S76Vinp;A1A2A1A2A2A2S1S19S13Q8M1A1M2A1S24VrhoM;S14G0R2A2A2S1bG2S14G1Z0A2A2A3F_;Fa;").
Proof.
  dsheet. pose proof GM1 as (_ & HGhigh1 & _ & HF1). pose proof mS1_facts as (SRES & SMAPS & STOP & SA1 & SA2 & Hx & H16 & Hxtop & Sx' & _).
  pose proof (StartArgBytes.arg_nums sp brk mb draw inp Hent Hinp) as (Nsp & Nfit & N16 & Nargc & Nstr & Nstr8 & NA1 & NA1b & Nrnd & Npad & Nrnd8 & Nlen & Nlenb & Nlen0 & Ntab1 & Ntab2).
  pose proof (Zle_0_nat (tab (in_argv inp))) as T0. pose proof (Zle_0_nat (tab (in_envp inp))) as T1. pose proof (Zle_0_nat (pad_len (in_argv inp) (in_envp inp))) as T2.
  pose proof (Start7.arith18 x Hx H16 (bv_unsigned sp + StartArgBytes.RNDo inp) ltac:(clear -Sx' Nrnd Nstr Nargc T0 T1 T2; lia) ltac:(clear -Sx' Nfit Nlen; lia) ltac:(clear -Sx' Nlenb Nlen Nsp; lia)) as AR.
  destruct AR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24).
  pose proof (q12x_lo x Hx) as [Q1 Q2].
  intros a Ha.
  assert (Ha64 : 0 <= a < 2 ^ 64) by (clear -Ha Q1 A14 A18; unfold kHighMemBeg in *; lia).
  assert (HaP : ~ ZPAGES a) by (clear -Ha Q1; unfold ZPAGES, PA0, PR0; lia).
  rewrite (RMo (Z_to_bv 64 a)).
  - rewrite O1 by (rewrite u64_of_lit by exact Ha64; exact HaP). exact (ZX a Ha).
  - apply (main_apart_band v rho1 HF1 (q12x x) ltac:(clear -Q1 Q2; unfold kHighMemBeg in *; lia) HGhigh1). rewrite u64_of_lit by exact Ha64.
    clear -Ha A14 A18. unfold kHighMemBeg in *. lia.
Qed.

Lemma regglob_pages_check : ltac2:(tb__ "0|2|
S1aS0S1S1aS50S10S10S1fS4aS49S26S3bS3aR2A1A1A1M0S28Z7fffc000A1R1A3S4bA2A1Loff;S4cZ0U1000A2M1A3S1dA3S1S1aS50S10S10S1fS4aS49G0S28Z80015000A1R1A3S4bA2A1Loff;G1A3S1dA3A2Fv';").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma regglob_pages_present : ltac2:(tb__ "0|4|
S10S2S0S6Z7fffc000M0R1A2S8R1S7G0Z1000M1A2A2A2S0S6Z80015000M2R1A2S8R1S7G2G1A2A2A2A2S3S1S19S13Q8A1M3A1S24VrhoM;S14Q40R2A2A2S1eG3A1A3A1F_;Fa;").
Proof.
  intros a Ha. pose proof (regglob_pages_check v) as [CKA CKB]. destruct Ha as [Ha|Ha].
  - destruct (main_view_present_range (SLit 0x7fffc000) (zseq 0 4096) CKA (a - 0x7fffc000) ltac:(clear -Ha; apply In_zseq; simpl Z.of_nat; lia)) as [b X].
    cbn [eval] in X. rewrite u64_of_lit in X by (clear; lia). replace (0x7fffc000 + (a - 0x7fffc000)) with a in X by (clear; lia).
    rewrite (view_rm _ a _ ltac:(clear -Ha; lia) X). discriminate.
  - destruct (main_view_present_range (SLit 0x80015000) (zseq 0 4096) CKB (a - 0x80015000) ltac:(clear -Ha; apply In_zseq; simpl Z.of_nat; lia)) as [b X].
    cbn [eval] in X. rewrite u64_of_lit in X by (clear; lia). replace (0x80015000 + (a - 0x80015000)) with a in X by (clear; lia).
    rewrite (view_rm _ a _ ltac:(clear -Ha; lia) X). discriminate.
Qed.

Lemma tpF_defined_partial : ltac2:(tb__ "0|7|
S13Q40M0A1M1S4fG1R1S5bVtp;A1A3S2S4fG1R2S1cG1S6fS5dU2M2A2S6fS5cG2A2A3A3S2S1G1R2S74A3S2S1G1R2S73A3S0S6S6dVx;A1S12G0R2A2M3A2S6S7G3Z1000M4A2SdS70Vx;A1S71S7S12G0Vsp;A2S76Vinp;A1A2A1A2A2A2A2A2A2S10S0S6S12G0R4A2M5R1A2S8R1S7G5G4A2A2A2S3S1S19S13Q8A1M6A1S24VrhoM;S14G0R2A2A2S1eG6A1A3A1F_;Fa;F_;F_;Fp;").
Proof.
  intros p _ Hcase a Ha. destruct Hcase as [HZ|[->|[->|[H1 H2]]]].
  - rewrite (ZPAGES_zero a); [discriminate|]. apply in_app_iff in HZ as [HZ|HZ]; apply In_pages_rev in HZ as (k & Hk & ->);
      unfold pageZ, PR0, PA0 in Ha; rewrite u64_of_lit in Ha by lia; unfold ZPAGES, PA0, PR0; lia.
  - apply regglob_pages_present. right. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8CallDefs.PGB in Ha. rewrite u64_of_lit in Ha by (clear; lia). exact Ha.
  - apply regglob_pages_present. left. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8CallDefs.PGA in Ha. rewrite u64_of_lit in Ha by (clear; lia). exact Ha.
  - rewrite (stackshadow_zero_main a); [discriminate|]. clear -H1 H2 Ha. lia.
Qed.

Lemma RIH_check : ltac2:(tb__ "0|0|
S1aS1S1aS50S10S10S1fS4aS49S26S3bS3aR2A1A1A1S83R1A3S4bA2A1Loff;S4cZ0U200A2A3S1dA3Fv';").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TLSP_check : forall v' : bool,
  forallb (fun off => negb (binfo_eqb (byte_info (ss_objs (ax_S (MAIN_of v'))) (SLit 0x800bc000) off) BNone)) (zseq 0 (Z.to_nat 0x4600)) = true.
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma smatch_inranges_present : ltac2:(tb__ "0|4|
S33S32S17S44A1M0S7eS43S13Q40A1S2fS38R6R5S16G0S66R4S67R3R2A2A4A4S79R7S26R6A1R2A3S1S19S13Q8A1M1A1M2S29S38R3A2S1eG1A1M3A3S3S1G2S7fR6R4A2G3A3A1F_;F_;F_;Fa;Fmd;Fms;Ftr;FS;Frho;").
Proof.
  clear. intros rho S tr ms md a Hsm Hin Himg.
  pose proof Hsm as (WF & _ & _ & _ & ROM & _). cbn [snd cfg_ms cfg_model] in ROM.
  pose proof (proj1 (smatch_mm segsA _ _ _ _ _ Hsm)) as HOL.
  destruct Hin as (o & Ho & Hr). unfold obj_range in Hr. cbn [fst snd] in Hr.
  pose proof (proj1 (Forall_forall _ _) HOL o Ho) as OH.
  unfold swf in WF. apply andb_true_iff in WF as [WF _]. apply andb_true_iff in WF as [_ WFO].
  rewrite forallb_forall in WFO. specialize (WFO o Ho).
  destruct (obj_byte_readable segsA rho ms o (bv_unsigned a - bv_unsigned (eval rho (ob_base o))) (ss_next S) ROM WFO OH ltac:(lia)) as [b Hb].
  replace (bv_unsigned (eval rho (ob_base o)) + (bv_unsigned a - bv_unsigned (eval rho (ob_base o)))) with (bv_unsigned a) in Hb by lia.
  rewrite Z_to_bv_bv_unsigned in Hb. unfold rd, ms_read_byte in Hb. intros X. rewrite X, ROM, Himg in Hb. discriminate.
Qed.

Lemma ZPAGES_dec : ltac2:(tb__ "0|1|
S10S2S5aR1A1M0S3G0A1A2Fa;").
Proof. clear. intros a. unfold ZPAGES, PA0, PR0. lia. Qed.

Local Ltac bandlia := unfold band_page, Geometry.LOW_SHADOW_BEG, Geometry.PG, Geometry.SHADOW_GAP_BEG, Geometry.HIGH_SHADOW_BEG, Geometry.HIGH_SHADOW_END,
  Placement.SHADOW_BAND_LO, Placement.SHADOW_BAND_HI, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States.LOWPG in *; lia.

Theorem tpF_defined : ltac2:(tb__ "0|4|
S13Q40M0A1M1S4fG1R1S5bVtp;A1A3S77S12G0R2A2A1S10S0S6S12G0R4A2M2R1A2S8R1S7G2Z1000A2A2A2S3S1S19S13Q8A1M3A1S24VrhoM;S14G0R2A2A2S1eG3A1A3A1F_;Fa;F_;F_;Fp;").
Proof.
  intros p Hp Hb a Ha.
  assert (H64 : 0 <= a < 2 ^ 64) by (clear -Hb Ha; pose proof (urange p); bandlia).
  dsheet. pose proof mS1_facts as (SRES & SMAPS & STOP & SA1 & SA2 & Hx & H16 & Hxtop & Sx' & _).
  unfold tpF in Hp. rewrite Etp in Hp. apply in_app_iff in Hp as [Hp|Hp]; [|apply in_app_iff in Hp as [Hp|Hp]].
  - apply In_pages_rev in Hp as (k & Hk & ->). rewrite (ZPAGES_zero a); [discriminate|].
    unfold pageZ, PR0, PA0 in Ha. rewrite u64_of_lit in Ha by (clear -Hk; lia). unfold ZPAGES, PA0, PR0. clear -Ha Hk. lia.
  - apply In_pages_rev in Hp as (k & Hk & ->). rewrite (ZPAGES_zero a); [discriminate|].
    unfold pageZ, PR0, PA0 in Ha. rewrite u64_of_lit in Ha by (clear -Hk; lia). unfold ZPAGES, PA0, PR0. clear -Ha Hk. lia.
  - unfold TPmain in Hp. destruct Hp as [<-|[<-|[<-|Hp]]].
    + apply regglob_pages_present. right. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8CallDefs.PGB in Ha. rewrite u64_of_lit in Ha by (clear; lia). exact Ha.
    + apply regglob_pages_present. left. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Start8CallDefs.PGA in Ha. rewrite u64_of_lit in Ha by (clear; lia). exact Ha.
    +
      exfalso. clear -Hb W13. pose proof W13 as [W _]. bandlia.
    +
      assert (HROK1 : OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.rhoOK mS1 a1 a2 P b4 b5 b6 b7 b8 b9 x b10 rho1).
      { apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Start8.rhoOK_agree mS1 a1 a2 P b4 b5 b6 b7 b8 b9 x b10 200%positive rho' rho1); [lia | exact ROK | intros i Hi; apply RW1]. }
      pose proof (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.Start6.Upri mS1 a1 a2 P b4 b5 b6 rho1 (proj1 HROK1)) as UP1.
      assert (EP : OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ rho1 = OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ rho') by (apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ_ext; apply RW1).
      destruct w as [tr [msv mdv]]. rewrite virt_unfold in Hsm1, RMi. cbn [snd cfg_ms] in RMi.

      assert (FRAME : ~ (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ rho' <= a < OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ rho' + 512) -> ~ (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States.LOWPG <= a < OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States.LOWPG + 0x4600) ->
                      rm rhoM (Z_to_bv 64 a) <> None).
      { intros N1 N2. pose proof (BD p a Hp Ha (proj2 H64) N1 N2) as D.
        destruct (in_ranges_dec rho1 (ss_objs (ax_S (MAIN_of v))) (Z_to_bv 64 a)) as [IN|OUT].
        - rewrite (RMi _ IN).
          exact (smatch_inranges_present rho1 (ax_S (MAIN_of v)) tr _ _ (Z_to_bv 64 a) Hsm1 IN ltac:(apply image_byte_none_A; rewrite u64_of_lit by exact H64; clear -Hb Ha; bandlia)).
        - rewrite (RMo _ OUT). destruct (ZPAGES_dec a) as [ZP|NZ]; [rewrite (Z1 a ZP); discriminate|].
          rewrite (O1 (Z_to_bv 64 a)) by (rewrite u64_of_lit by exact H64; exact NZ). exact D. }
      destruct (Z.le_gt_cases (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ rho') a) as [C1|C1]; [destruct (Z.lt_ge_cases a (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ rho' + 512)) as [C2|C2]|].
      *
        destruct (handoff_view_present_range rho1 rhoM (ax_S (MAIN_of v)) tr _ _ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States.shRI_base _ Hsm1 RMi (RIH_check v) (a - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ rho')
                    ltac:(clear -C1 C2; apply In_zseq; simpl Z.of_nat; lia)) as [b X].
        change (eval rho1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States.shRI_base) with (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.pRI rho1) in X. rewrite UP1, EP in X.
        replace (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ rho' + (a - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Start4.priZ rho')) with a in X by (clear; lia).
        rewrite (view_rm _ a _ ltac:(clear -Hb Ha H64; bandlia) X). discriminate.
      * destruct (Z.le_gt_cases OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States.LOWPG a) as [C3|C3]; [destruct (Z.lt_ge_cases a (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States.LOWPG + 0x4600)) as [C4|C4]|].
        --
           destruct (handoff_view_present_range rho1 rhoM (ax_S (MAIN_of v)) tr _ _ (SLit 0x800bc000) _ Hsm1 RMi (TLSP_check v) (a - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States.LOWPG)
                      ltac:(clear -C3 C4; apply In_zseq; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States.LOWPG in *; rewrite Z2Nat.id by lia; lia)) as [b X].
           cbn [eval] in X. rewrite u64_of_lit in X by (clear; lia). unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States.LOWPG in X.
           replace (0x800bc000 + (a - 0x800bc000)) with a in X by (clear; lia).
           rewrite (view_rm _ a _ ltac:(clear -Hb Ha H64; bandlia) X). discriminate.
        -- apply FRAME; [clear -C2; lia | clear -C4; lia].
        -- apply FRAME; [clear -C2; lia | clear -C3; lia].
      * destruct (Z.le_gt_cases OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States.LOWPG a) as [C3|C3]; [destruct (Z.lt_ge_cases a (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States.LOWPG + 0x4600)) as [C4|C4]|].
        -- destruct (handoff_view_present_range rho1 rhoM (ax_S (MAIN_of v)) tr _ _ (SLit 0x800bc000) _ Hsm1 RMi (TLSP_check v) (a - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States.LOWPG)
                      ltac:(clear -C3 C4; apply In_zseq; unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States.LOWPG in *; rewrite Z2Nat.id by lia; lia)) as [b X].
           cbn [eval] in X. rewrite u64_of_lit in X by (clear; lia). unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States.LOWPG in X.
           replace (0x800bc000 + (a - 0x800bc000)) with a in X by (clear; lia).
           rewrite (view_rm _ a _ ltac:(clear -Hb Ha H64; bandlia) X). discriminate.
        -- apply FRAME; [clear -C1; lia | clear -C4; lia].
        -- apply FRAME; [clear -C1; lia | clear -C3; lia].
Qed.

Corollary tpF_present : ltac2:(tb__ "0|3|
S13Q40M0A1M1S4fG1R1S5bVtp;A1A3S77S12G0R2A2A1S59S58S38S24VrhoM;A1A2S12G0R3A2M2S7G2Z1000A2A3F_;F_;Fp;").
Proof.
  intros p Hp Hb z Hz. pose proof (tpF_defined p Hp Hb z Hz) as D.
  rewrite view_in by (clear -Hb Hz; pose proof (urange p); bandlia). unfold rd_of.
  destruct (rm rhoM (Z_to_bv 64 z)) as [b|]; [exists b; reflexivity | exfalso; exact (D eq_refl)].
Qed.
End Facts.
