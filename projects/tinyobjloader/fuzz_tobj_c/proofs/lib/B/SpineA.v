(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "False"; "not"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "FdEntry"; "Model"; "fd_lookup"; "FdChannel"; "WriteEv"; "m_fs"; "ExitEv"; "FdFile"; "VmState"; "fd_insert"; "FdDir"; "fd_remove"; "m_fds"; "with_fds"; "@Corelib.Init.Datatypes"; "list"; "option"; "bool"; "nil"; "Some"; "app"; "prod"; "true"; "cons"; "length"; "false"; "negb"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "bv_add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.SpineA.SPINEA"; "argv1"; "PAx"; "FDS"; "MDT"; "SpecT"; "JMx"; "small_file"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "w_tr"; "tcons"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvFw"; "ch2"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "path_eqb"; "fs_lookup"; "Fs"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi"; "dot_path"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.DrvExit"; "ch1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR"; "std_fds"; "FD3"; "KcG"; "P0Z"; "CST_drv2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "of_nat"; "ltb"; "pow"; "sub"; "land"; "modulo"; "ones"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "cls_keptA"; "cls_kept_freeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvM_states"; "nd_M"; "E_copen"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA"; "MSGb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT"; "clen_of"; "S_T"; "calls_of"; "nd_T"; "flags_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail"; "SUF_NL"; "PRE_C"; "PRE_D"; "PRE_U"; "SUF_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "KcA"; "Kc_ok"; "with_vm"; "alloc_contractsA"; "alloc_contractsA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceM"; "S_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.DriverSpec"; "calls"; "MAX_INPUT"; "msg_cannot_open"; "msg_read_error"; "open_may_succeed"; "wr"; "zeros"; "PATH_MAX"; "config_len"; "counting"; "die"; "ex"; "file_traces"; "msg_usage"; "payload_len"; "spec_traces"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvR"; "BXk"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvR_dstates"; "D_rde"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvR_facts"; "nd_Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvTLXa"; "JT"; "CST_drv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "JA"; "PTrue"; "ndesc"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.IfaceEx"; "classes_fresh"; "classes_fresh_but_batch"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei"; "dotdot_path";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface"; "PEND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvM"; "JM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.DrvTLX"; "EVk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_iface2"; "fuzz_one_sumE"; "fuzz_one_sumT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.IfaceS"; "malloc_contractA_strong"; "malloc_contractA_strong_ex"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess Uapi Syscall.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymSummary SymEntail SymCFG SymExit SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface IfaceEx IfaceS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SysA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec SpecTop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Code Lib_fuzz_iface2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvFw DrvIfaceT DrvIfaceR DrvIfaceM DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ob.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvR_facts DrvR_dstates DrvR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvM_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oe.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require op.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_iface2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.DrvExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvFw OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.DrvTLX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oo.DrvTLXi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oq.DrvTLXie OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ob.DrvRGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.DrvR_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.DrvR_tstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvR_facts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvR_dstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.DrvRe OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvM_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oe.DrvM_tstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nj.Fps_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Fps_tailA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.op.FpsSite.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma land_ones_mod : ltac2:(tb__ "0|1|
S2bS2bS42Z0R2A2M0G0S0S2bS49R4S4bR3A1A2S4aR4S47Z2R3A2A2A3F_;F_;Fn;Fa;").
Proof. intros a n Ha Hn. apply Z.land_ones. exact Hn. Qed.

Lemma clen_config : ltac2:(tb__ "0|0|
S13S1fQ8A1A1S0S2bS54R1A1S6dR1A1A3FF;").
Proof.
  intros F. unfold clen_of, config_len, cfg_word, fbyte, CFG_COUNT_BIT, b8.
  set (b0 := bv_unsigned (nth 0 F (Z_to_bv 8 0))). set (b1 := bv_unsigned (nth 1 F (Z_to_bv 8 0))).
  assert (H0 : 0 <= b0 < 256) by (pose proof (bv_unsigned_in_range 8 (nth 0 F (Z_to_bv 8 0))) as X; change (bv_modulus 8) with 256 in X; subst b0; lia).
  assert (H1 : 0 <= b1 < 256) by (pose proof (bv_unsigned_in_range 8 (nth 1 F (Z_to_bv 8 0))) as X; change (bv_modulus 8) with 256 in X; subst b1; lia).
  change 127 with (Z.ones 7). rewrite land_ones_mod by lia. change (2 ^ 7) with 128.
  pose proof (Z.mod_pos_bound b1 128 ltac:(lia)) as HB. pose proof (Z.div_mod b1 128 ltac:(lia)) as HD.
  replace (b0 + 256 * b1) with ((b0 + 256 * (b1 mod 128)) + (b1 / 128) * 32768) by lia.
  rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia.
Qed.

Lemma calls_eq : ltac2:(tb__ "0|0|
S13S1fQ8A1A1S0S2bS56R1A1S65R1A1A3FF;").
Proof.
  intros F. unfold calls_of, calls, fbyte, b8. rewrite clen_config. pose proof (config_len_range F) as HC.
  set (b2 := bv_unsigned (nth 2 F (Z_to_bv 8 0))).
  assert (H2 : 0 <= b2 < 256) by (pose proof (bv_unsigned_in_range 8 (nth 2 F (Z_to_bv 8 0))) as X; change (bv_modulus 8) with 256 in X; subst b2; lia).
  change 3 with (Z.ones 2). rewrite land_ones_mod by lia. change (2 ^ 2) with 4.
  destruct (Z.eqb_spec (config_len F) 0) as [E|NE]; destruct (Z.ltb_spec 0 (config_len F)); lia.
Qed.

Lemma counting_flags : ltac2:(tb__ "0|0|
S13S1fQ8A1A1S0S15S6eR1A1S1eS46S58R1A1Z80A2A1A3FF;").
Proof.
  intros F. rewrite counting_bytes. unfold flags_of, fbyte, b8.
  destruct (Z.leb_spec 128 (bv_unsigned (nth 1 F (Z_to_bv 8 0)))); destruct (Z.ltb_spec (bv_unsigned (nth 1 F (Z_to_bv 8 0))) 128); try reflexivity; lia.
Qed.

Lemma payload_eq : ltac2:(tb__ "0|1|
S13S1fQ8A1M0A1S0S2bS73R1A1S48S48S45S1cG0R1A2A1Z6A2S54R1A1A2A3FF;").
Proof. intros F. unfold payload_len, HDR_MIN. rewrite clen_config. lia. Qed.

Lemma trace_normal : ltac2:(tb__ "0|1|
S13S1fQ8A1M0A1S0S13S4A1S18S4S88U1A1S4cG0S4S9S39A1S86S56R1A1A1A4A3S6aZ1S6bS65R1A1A1A2A3FF;").
Proof.
  intros F. rewrite calls_eq. pose proof (calls_range F) as HR.
  assert (H : calls F = 1 \/ calls F = 2 \/ calls F = 3 \/ calls F = 4) by lia.
  destruct H as [-> |[-> |[-> | ->]]]; reflexivity.
Qed.

Lemma die_eq : ltac2:(tb__ "0|1|
S37S13S1fQ8A1M0A1S0S13S4A1S18S4S4cG0S4S9S34A1R1A4S1bS4SbS20Q40Z2A2R2A2S16S4A1A3A3S6fR2R1A2A3Fmsg;Ffs;").
Proof. intros fs msg. reflexivity. Qed.

Lemma MSGb_C : ltac2:(tb__ "0|1|
S13S1fQ8A1A1M0S0G0S53S5aS59R1A3S67R1A1A3Fp;"). Proof. intros p. reflexivity. Qed.
Lemma MSGb_D : ltac2:(tb__ "0|1|
S13S1fQ8A1A1M0S0G0S53S5bS59R1A3S68R1A1A3Fp;"). Proof. intros p. reflexivity. Qed.
Lemma MSGb_U : ltac2:(tb__ "0|1|
S13S1fQ8A1A1M0S0G0S53S5cS5dR1A3S72R1A1A3Fp;"). Proof. intros p. reflexivity. Qed.

Section SPINEA.

Variable AInv : ltac2:(tb__ "0|0|
S4dS2cS13S1fQ40A1A1S6OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
S2bS50VCST;R1A2S1S42Z0R2A2S44R2S80A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S2bS50VXGL;R1A2S1S42Z0R2A2S44R2S80A2A2F_;Fa;").
Hypothesis HLV : law_view_stmt AInv.
Hypothesis HLF : law_fds_stmt AInv.
Hypothesis HCSTok : cst_ok CST.
Hypothesis HCSTdrv : ltac2:(tb__ "0|0|
S2bS50S7aR1A2S50VCST;R2A2F_;Fz;").
Hypothesis HLPP : law_pp_stmt AInv CST.
Hypothesis HCSTdrv2 : ltac2:(tb__ "0|0|
S2bS50S3eR1A2S50VCST;R2A2F_;Fz;").

Variable argv : list (list byte).
Variable FS0 : Fs.
Hypothesis Hargc : length argv = 2%nat.
Definition argv1 : list byte := nth 1 argv [].
Hypothesis Hnonul : ~ In (Z_to_bv 8 0) argv1.

Hypothesis Hndd : ltac2:(tb__ "0|0|
S0S15S35S23S85A2S1dA3").
Hypothesis Hnsl : path_has_slash argv1 = false.

Variable MDX : Model -> Prop.
Hypothesis HMDXvm : ltac2:(tb__ "0|0|
S6SdVMDX;R2A1VMDX;S61R2R3A2A1F_;Fv;Fmd;").
Hypothesis HMDXfds : ltac2:(tb__ "0|0|
S6S13S19S1fQ40A1S5A2A1VMDX;R2A1VMDX;S12R2R3A2A1F_;Ff;Fmd;").
Hypothesis HMDXfs : ltac2:(tb__ "0|0|
S6VMDX;R1A1S0S37SaR2A1VFS0;A3F_;Fmd;").

Variable rhoM : valuation.

Definition SpecT (t : list event) : Prop := ltac2:(tb__ "0|0|
S83S13S4A1Vt;S74Vargv;VFS0;A2A3").

Definition small_file : bool := ltac2:(tb__ "0|2|
S14S13S1fQ8A1M0A1M1A1S15Lx;S36VFS0;S23A2G1S46S45S1cG0R1A2A1Z10000A2LF;S1aX14x2").
Definition PAx (A : AA) : Prop := ltac2:(tb__ "0|0|
S15OL_;S29S81VA;A1S82VA;A1X15x2").
Lemma PAx_init : ltac2:(tb__ "0|0|
S4dS81R1A1S24R2A1F_;FA;").
Proof. intros A H. unfold PAx. destruct small_file; [exact H|]. intros c Hc _. exact (H c Hc). Qed.
Lemma PAx_m : ltac2:(tb__ "0|0|
S4dS4dS2bS42Zfc01R1A2S24R4A1S4eR5R4R3A3S24R5A1F_;F_;F_;Fn;FA';FA;").
Proof.
  intros A A' n Hn HP HK. unfold PAx in *. destruct small_file;
    [exact (fresh_kept_malloc_big A A' n Hn HK HP) | exact (fresh_but_batch_kept_malloc_big A A' n Hn HK HP)].
Qed.
Lemma PAx_f : ltac2:(tb__ "0|2|
S13S1fQ8A1M0A1M1S0S14G1A1S36VFS0;S23A2S17G1R1A2A3S42Z10000S45S1cG0R2A2A1A2S4dS4dS24R2A1S4fR3R2A2S24R3A1F_;F_;FA';FA;F_;F_;FF;").
Proof.
  intros F HF HL A A' HP HK. unfold PAx, small_file in *. rewrite HF in HP |- *.
  destruct (Z.ltb_spec (Z.of_nat (length F)) 65536); [lia|]. exact (fresh_but_batch_kept_free A A' HK HP).
Qed.

Definition JMx : ltac2:(tb__ "0|0|
S13S19S1fQ40A1S5A2A1S7eS40Fnd;Ffds;") := ltac2:(tb__ "0|0|
S87VAInv;VCST;VXGL;VrhoM;S23S16S4A1VMDX;S24A8").

Lemma HtopM_of : ltac2:(tb__ "0|1|
S2cS13S1fQ40M0A1A1S2eS3fS2aS28S3aS51A2S64R3R2R1A6S0S2bS43S21G0S2dVrhoM;P1eA2A2Z800000A2S21G0S2dVrhoM;P1A2A2A3F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w [Hsm HJ].
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  destruct (DrvM.JM_P0 AInv CST XGL rhoM argv1 [] MDX PAx _ _ _ _ _ _ HJ) as [_ [Hv _]].
  pose proof (sp0_facts_sound rho _ HF ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as [Hsp H30].
  rewrite (Hv 30%positive ltac:(unfold NF; lia)), (Hv 1%positive ltac:(unfold NF; lia)). lia.
Qed.
Lemma triple_preM : ltac2:(tb__ "0|1|
S2eOF_;S31S31OS2eR4R1A1R3F_;Fw;R2S30S2aR6R5R4A4M0F_;G0F_;F_;FX;FQ;FP;Fok;").
Proof. intros ok P Q X H1 H2 n Hg w Hw. exact (H2 (H1 w Hw) n Hg w Hw). Qed.
Lemma etriple_preM : ltac2:(tb__ "0|1|
S31S2eOF_;OS2eR4R1A1R3F_;Fw;R2S2fS2aR5R4A3M0F_;G0F_;F_;FX;FQ;FP;").
Proof. intros P Q X H1 H2 w Hw. exact (H2 (H1 w Hw) w Hw). Qed.

Definition FDS (off : Z) : list (word * FdEntry) := ltac2:(tb__ "0|1|
SeS3aS20Q40M0Z3A2ScS23S20G0Voff;A2A2A3").
Lemma HFDS1 : ltac2:(tb__ "0|0|
S2bS0S14S5A1S7S25R1A1S39A2S17S5S8S39A1A2A3Foff;"). Proof. intros off. reflexivity. Qed.
Lemma HFDS2 : ltac2:(tb__ "0|0|
S2bS0S14S5A1S7S25R1A1S34A2S17S5S8S34A1A2A3Foff;"). Proof. intros off. reflexivity. Qed.
Lemma HFDS3 : ltac2:(tb__ "0|1|
S2bS0S14S5A1S7S25R1A1S20Q40M0Z3A2A2S17S5ScS23S20G0R1A2A2A2A3Foff;"). Proof. intros off. reflexivity. Qed.
Lemma HFDSstep : ltac2:(tb__ "0|2|
S2bS2bS42Z0R2A2M0G0S44S43R4R3A2S47Z2Z40A2A2S0S13S19S1fQ40M1A1S5A2A1SeS25R5A1S20G1Z3A2ScS23S22G1S20G1R5A2S20G1R4A2A3A2A3S25S43R5R4A2A1A3F_;F_;F_;Fn;Foff;").
Proof.
  intros off n Ho Hn Hs. unfold FDS. cbn. repeat f_equal. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  rewrite !bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); rewrite ?bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia); lia). reflexivity.
Qed.
Lemma HFDC : ltac2:(tb__ "0|1|
S2bS0S13S19S1fQ40M0A1S5A2A1S10S25R1A1S20G0Z3A2A2S3aA3Foff;"). Proof. intros off. reflexivity. Qed.
Lemma HFDC1 : ltac2:(tb__ "0|0|
S0S14S5A1S7S3aS39A2S17S5S8S39A1A2A3"). Proof. reflexivity. Qed.
Lemma HFDC2 : ltac2:(tb__ "0|0|
S0S14S5A1S7S3aS34A2S17S5S8S34A1A2A3"). Proof. reflexivity. Qed.
Lemma FD3_file : ltac2:(tb__ "0|0|
S0S15S35S23S38A2S1dA3S0S13S19S1fQ40A1S5A2A1S3bS23A1S25Z0A1A3F_;").
Proof. intros Hd. unfold FD3, open_entry, FDS. rewrite Hd. reflexivity. Qed.
Lemma FD3_dir : ltac2:(tb__ "0|0|
S0S15S35S23S38A2S1aA3S0S14S5A1S7S3bS23A1S20Q40Z3A2A2S17S5SfA2A3F_;").
Proof. intros Hd. unfold FD3, open_entry. rewrite Hd. reflexivity. Qed.
Lemma FD3_dir1 : ltac2:(tb__ "0|0|
S0S15S35S23S38A2S1aA3S0S14S5A1S7S3bS23A1S39A2S17S5S8S39A1A2A3F_;").
Proof. intros Hd. unfold FD3, open_entry. rewrite Hd. reflexivity. Qed.
Lemma FD3_dir2 : ltac2:(tb__ "0|0|
S0S15S35S23S38A2S1aA3S0S14S5A1S7S3bS23A1S34A2S17S5S8S34A1A2A3F_;").
Proof. intros Hd. unfold FD3, open_entry. rewrite Hd. reflexivity. Qed.

Definition MDT : Model -> Prop := DrvR.MDT std_fds MDX.
Lemma MDT_vm : ltac2:(tb__ "0|0|
S6SdS26R2A1S26S61R2R3A2A1F_;Fv;Fmd;").
Proof. intros md v [H1 H2]. split; [rewrite m_fds_with_vm; exact H1 | apply HMDXvm; exact H2]. Qed.
Lemma MDT_fd1 : ltac2:(tb__ "0|0|
S6S26R1A1S0S14S5A1S7S11R2A1S39A2S17S5S8S39A1A2A3F_;Fmd;").
Proof. intros md [H1 _]. rewrite H1. reflexivity. Qed.
Lemma MDT_fs : ltac2:(tb__ "0|0|
S6S26R1A1S0S37SaR2A1VFS0;A3F_;Fmd;").
Proof. intros md [_ H2]. exact (HMDXfs md H2). Qed.

Lemma omsb : ltac2:(tb__ "0|1|
S69S23VFS0;A2S1S84S1cS1fQ8A1M0S23A2S6cA2S3S0S13G0A1S23S16G0A1A3A1A2F_;").
Proof. intros (H1 & H2 & _). split; assumption. Qed.

Section FileSpec.
Variable F : list byte.
Hypothesis Ho : open_may_succeed argv1 FS0.
Hypothesis Hd : ltac2:(tb__ "0|0|
S0S15S35S23S38A2S1dA3").
Hypothesis HF : ltac2:(tb__ "0|1|
S0S14S13S1fQ8A1A1M0A1S36VFS0;S23A2S17G0VF;A2A3").
Lemma Hnd : argv1 <> dot_path.
Proof. intros E. rewrite E, path_eqb_refl in Hd. discriminate. Qed.
Lemma spec_fileT : ltac2:(tb__ "0|1|
S13S4A1M0S83G0R1S71VFS0;VF;A2A3S27R2A1F_;Ft;").
Proof.
  intros t Ht. unfold SpecT. destruct omsb as [H1 H2]; [exact Ho|].
  exact (spec_file argv FS0 F t Hargc H1 H2 Hnd HF Ht).
Qed.
End FileSpec.

Section Safe.
Variable ok : world -> Prop.
Hypothesis HOKJ : ltac2:(tb__ "0|0|
S40S2cS13S1fQ40A1A1S13S4A1S6R5R4R3R2R1A4S33S27R3A2F_;Fmd;Ftr;Ftp;Frho;S41S2aVok;R2A3F_;FJ;").
Hypothesis HOKP : ltac2:(tb__ "0|0|
S40S2cS13S1fQ40A1A1S13S4A1S6R5R4R3R2R1A4S33S27R3A2F_;Fmd;Ftr;Ftp;Frho;S8bS2aVok;R2A3F_;FJ;").
Hypothesis Hokh : ok_halted ok SpecT.
Hypothesis AC : ltac2:(tb__ "0|0|
S62S2aS5eVAInv;VCST;VXGL;A5").

Hypothesis MS : ltac2:(tb__ "0|0|
S8cS2aS5eVAInv;VCST;VXGL;A5").

Hypothesis HFZ : ltac2:(tb__ "0|0|
S5fS2eOF_;S60R2A1S7fS2aR3R2A3S8aVAInv;VCST;VXGL;R4R3A5F_;F_;Fok';FKc;").
Lemma HtcT0 : tcons SpecT [].
Proof. exists (die FS0 (msg_cannot_open argv1)). split; [unfold SpecT; apply spec_cannot_open; exact Hargc | apply is_prefix_nil]. Qed.

Lemma HSPEC_C : ltac2:(tb__ "0|1|
S6VMDX;R1A1S27S18S4S16S4A1M0S18S4G0S18S4S4cS1fQ8A1S4S9S34A1S53S5aS59S23A3A4S1bS4SbS20Q40Z2A2SaR2A1A2G0A3A3A3A3A1F_;Fmd;").
Proof. intros md Hmd. rewrite (HMDXfs md Hmd). cbn [app]. rewrite MSGb_C, die_eq. unfold SpecT. apply spec_cannot_open. exact Hargc. Qed.
Lemma HSPEC_D : ltac2:(tb__ "0|1|
S0S15S35S23S38A2S1aA3S6VMDX;R1A1S27S18S4S16S4A1M0S18S4G0S18S4S4cS1fQ8A1S4S9S34A1S53S5bS59S23A3A4S1bS4SbS20Q40Z2A2SaR2A1A2G0A3A3A3A3A1F_;Fmd;F_;").
Proof.
  intros Hd md Hmd. rewrite (HMDXfs md Hmd). cbn [app]. rewrite MSGb_D, die_eq. unfold SpecT. apply spec_read_error; [exact Hargc|].
  apply path_eqb_eq. exact Hd.
Qed.
Lemma Hcopen : ltac2:(tb__ "0|0|
S2cS13S1fQ40A1A1S30S2aVok;S3fS2aS28S3aS51A2S52R2R1A5S2eS2L_;A4Ftp;Frho;").
Proof.
  exact (copen_tail_safe AInv CST XGL ALA HLV HCSTok HCSTdrv HLPP HCSTdrv2 ok SpecT HOKJ HOKP Hokh [] MDX HMDXvm std_fds HFDC1 HFDC2 rhoM (DrvM.P0M argv1) PAx
           argv1 Hnonul (fun r H => H) HSPEC_C).
Qed.
Lemma HTrderr : ltac2:(tb__ "0|2|
S0S15S35S23S38A2S1aA3S2cS2cOF_;S2cS13S1fQ40A1A1S2cR4R1A1S3dS23R2A2F_;Fr;S30S2aVok;S3fS2aS7cVAInv;VCST;VXGL;S7bS3cS16S4A1M0VMDX;S3bS23A1G0A4R5R4S16S19S2bS2bA2M1A1S16S19G1S2bA2A1S75S76A1S24S78AcS77R3R2A5S2eS2L_;A4F_;Ftp;Frho;FP0;Frho0;F_;").
Proof.
  intros Hd rho0 P0 rho tp HP0.
  exact (rderr_tail_safe AInv CST XGL ALA HLV HCSTok HCSTdrv HLPP HCSTdrv2 ok SpecT HOKJ HOKP Hokh [] MDX HMDXvm (FD3 argv1) (FD3_dir1 Hd) (FD3_dir2 Hd) rho0 P0 PAx
           argv1 Hd Hnonul HP0 (HSPEC_D Hd) rho tp).
Qed.

Lemma HT_safe : ltac2:(tb__ "0|3|
S13S1fQ8A1M0A1M1S69S23VFS0;A2S0S15S35S23S38A2S1dA3S0S14G1A1S36VFS0;S23A2S17G1R3A2A3S1S42S43Z6S54R4A1A2S45S1cG0R4A2A1M2A2S44G2S66A2A2S2cS2cS13S1fQ40A1A1S30S2aVok;S3fS2aS79VAInv;VCST;VXGL;R3R8S16S4A1S26S7dU0S57AaS55R2R1A5S2eS2L_;A4Ftp;Frho;FrhoT;F_;F_;F_;F_;FF;").
Proof.
  intros F Ho Hd HF HL rhoT rho tp.
  pose proof (clen_config F) as HCC. pose proof (config_len_range F) as HCR.
  assert (HN : SpecT (wr 1 (zeros (calls F)) ++ [ex FS0 0])).
  { apply (spec_fileT F Ho Hd HF). apply file_traces_normal. unfold HDR_MIN, DriverSpec.MAX_INPUT, Budget.MAX_INPUT in *. lia. }
  apply (tlx_safe AInv CST XGL ALA HCST HXGL HLV HCSTok HCSTdrv HLPP ok SpecT HOKJ HOKP Hokh AC MS rhoT F [] MDT MDT_vm MDT_fd1).
  -
    intros [|k]; [cbn [app OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.DrvTLX.EVk]; apply HtcT0|].
    exists (wr 1 (zeros (calls F)) ++ [ex FS0 0]). split; [exact HN|].
    cbn [app]. rewrite <- trace_normal. change (EVk (S k)) with (EVk 1%nat). rewrite <- app_assoc. apply is_prefix_app.
  - intros ok' Hok'. apply HFZ; [apply (Kc_okT [] MDT MDT_vm) | exact Hok'].
  - intros ok' Hok'. apply HFZ; [apply (Kc_okT [] MDT MDT_vm) | exact Hok'].
  -
    intros md Hmd. rewrite (MDT_fs md Hmd). cbn [app]. rewrite app_assoc, trace_normal. exact HN.
Qed.

Theorem spine_safe_A : ltac2:(tb__ "0|0|
S2cS13S1fQ40A1A1S30S2aVok;S3fS2aS28S3aS51A2S64R2R1A5S2eS2L_;A4Ftp;Frho;").
Proof.
  intros rho tp. apply (triple_preM ok _ _ _ (HtopM_of rho tp)). intros HtopM.
  apply (m_safe AInv CST XGL ALA HCST HXGL HLF HCSTdrv HCSTdrv2 ok SpecT HOKJ HOKP MS rhoM HtopM argv1 [] MDX FS0 HMDXvm HMDXfds HMDXfs Hnonul Hndd Hnsl HtcT0 PAx PAx_m).
  - exact Hcopen.
  -
    intros Ho rho' tp'. destruct (Sumbool.sumbool_of_bool (path_eqb argv1 dot_path)) as [Hd|Hd].
    +
      apply (r_dir_safe AInv CST XGL ALA HLV HCSTok HCSTdrv HLPP ok SpecT HOKJ HOKP [] argv1 [] MDX HMDXvm HtcT0 PAx (FD3 argv1) (FD3_dir Hd)).
      exact (HTrderr Hd).
    +
      destruct (fs_lookup FS0 argv1) as [F|] eqn:HF.
      2:{ exfalso. destruct Ho as (_ & _ & [E|E]); [apply path_eqb_eq in E; congruence | exact (E HF)]. }
      rewrite (FD3_file Hd).
      assert (HMDXfsF : forall md, MDX md -> fs_lookup (m_fs md) argv1 = Some F) by (intros md Hmd; rewrite (HMDXfs md Hmd); exact HF).
      apply (r_file_safe AInv CST XGL ALA HCST HXGL HLV HLF HCSTok HCSTdrv HLPP HCSTdrv2 ok SpecT HOKJ HOKP Hokh AC MS F argv1 [] FDS std_fds MDX
               HFDS1 HFDS2 HFDS3 HFDSstep HFDC HFDC1 HFDC2 HMDXvm HMDXfds HMDXfsF HtcT0 PAx PAx_m (PAx_f F HF)).
      * intros HL md Hmd. rewrite (HMDXfs md Hmd). cbn [app]. rewrite die_eq. apply (spec_fileT F Ho Hd HF).
        apply file_traces_refused. unfold DriverSpec.MAX_INPUT, Budget.MAX_INPUT in *. lia.
      * intros HL md Hmd. rewrite (HMDXfs md Hmd). cbn [app]. rewrite die_eq. apply (spec_fileT F Ho Hd HF).
        apply file_traces_short. unfold HDR_MIN. lia.
      * intros HL md Hmd. rewrite (HMDXfs md Hmd). cbn [app]. rewrite die_eq. apply (spec_fileT F Ho Hd HF).
        pose proof (clen_config F). pose proof (config_len_range F).
        apply file_traces_overrun; unfold HDR_MIN, DriverSpec.MAX_INPUT, Budget.MAX_INPUT, CFG_COUNT_BIT in *; lia.
      * intros HL. apply (HT_safe F Ho Hd HF). exact HL.
Qed.
End Safe.

Section Ex.
Hypothesis ACX : ltac2:(tb__ "0|0|
S63S2aS5eVAInv;VCST;VXGL;A5").
Hypothesis MSX : ltac2:(tb__ "0|0|
S8dS2aS5eVAInv;VCST;VXGL;A5").
Hypothesis HFZX : ltac2:(tb__ "0|0|
S5fS60R1A1S89VAInv;VCST;VXGL;R2A4F_;FKc;").

Lemma Hcopen_ex : ltac2:(tb__ "0|2|
S2eOF_;S2eS6VMDX;R1A1S0S13S4A1S32R3A1S18S4S16S4A1M0S18S4S4cS1fQ8A1S4S9S34A1S67S23A1A4S1bS4SbS20Q40M1Z2A2SaR2A1A2G0A3A3A3A3R5R4A1F_;F_;Fmd;Fw;S2cS13S1fG1A1A1S2fS2aS3fS2aS28S3aS51A2S52R2R1A5R4A3Ftp;Frho;F_;FQ;").
Proof.
  intros Q HQ.
  apply (copen_tail_ex AInv CST XGL ALA HLV HCSTok HCSTdrv HLPP HCSTdrv2 SpecT [] MDX HMDXvm std_fds HFDC1 HFDC2 rhoM (DrvM.P0M argv1) PAx
           argv1 Hnonul (fun r H => H) HSPEC_C).
  intros w md Hmd Hw. apply (HQ w md Hmd). rewrite Hw, MSGb_C. reflexivity.
Qed.
Lemma HTrderr_ex : ltac2:(tb__ "0|3|
S0S15S35S23S38A2S1aA3S2eOF_;S2eS6VMDX;R1A1S0S13S4A1S32R3A1S18S4S16S4A1M0S18S4S4cS1fQ8A1S4S9S34A1S68S23A1A4S1bS4SbS20Q40M1Z2A2SaR2A1A2G0A3A3A3A3R5R4A1F_;F_;Fmd;Fw;S2cS2cOF_;S2cS13S1fG1A1A1S2cR4R1A1S3dS23R2A2F_;Fr;S2fS2aS3fS2aS7cVAInv;VCST;VXGL;S7bS3cG0VMDX;S3bS23A1G0A4R5R4S16S19S2bS2bA2M2A1S16S19G2S2bA2A1S75S76A1S24S78AcS77R3R2A5R7A3F_;Ftp;Frho;FP0;Frho0;F_;FQ;F_;").
Proof.
  intros Hd Q HQ rho0 P0 rho tp HP0.
  apply (rderr_tail_ex AInv CST XGL ALA HLV HCSTok HCSTdrv HLPP HCSTdrv2 SpecT [] MDX HMDXvm (FD3 argv1) (FD3_dir1 Hd) (FD3_dir2 Hd) rho0 P0 PAx
           argv1 Hd Hnonul HP0 (HSPEC_D Hd)).
  intros w md Hmd Hw. apply (HQ w md Hmd). rewrite Hw, MSGb_D. reflexivity.
Qed.

Let QT (t : list event) : world -> Prop := fun w => w_tr w = t.

Lemma HT_ex_normal : ltac2:(tb__ "0|4|
S13S1fQ8A1M0A1M1S0S14G1A1S36VFS0;S23A2S17G1R1A2A3S1S42S43Z6S54R2A1A2S45S1cG0R2A2A1M2A2S44G2S66A2A2S2cS2cS13S1fQ40A1A1S2fS2aS3fS2aS79VAInv;VCST;VXGL;R3R6S16S4A1M3S26S24U0S57AaS55R2R1A5VQT;S18S4S6aZ1S6bS65R6A1A1A2S1bS4S70VFS0;Z0A2G3A3A3A1A3Ftp;Frho;FrhoT;F_;F_;FF;").
Proof.
  intros F HF HL rhoT rho tp.
  apply (tlx_ex_ok AInv CST XGL ALA HCST HXGL HLV HCSTok HCSTdrv HLPP ACX MSX (QT (wr 1 (zeros (calls F)) ++ [ex FS0 0])) rhoT F [] MDT MDT_vm MDT_fd1 PAx).
  - apply HFZX. apply (Kc_okT [] MDT MDT_vm).
  - apply HFZX. apply (Kc_okT [] MDT MDT_vm).
  - intros w md Hmd Hw. unfold QT. rewrite Hw, (MDT_fs md Hmd). cbn [app]. rewrite app_assoc, trace_normal. reflexivity.
Qed.

Theorem spine_ex_A : ltac2:(tb__ "0|1|
S13S4A1M0S27R1A1S2cS13S1fQ40A1A1S2fS2aS3fS2aS28S3aS51A2S64R2R1A5S2eS0G0S32R1A1R5A3Lw;A3Ftp;Frho;F_;Ft;").
Proof.
  intros t Ht rho tp. apply (etriple_preM _ _ _ (HtopM_of rho tp)). intros HtopM.
  unfold SpecT in Ht. rewrite (spec_traces_argc2 argv FS0 Hargc) in Ht. fold argv1 in Ht.
  destruct Ht as [<-|Ht].
  {
    apply (m_ex_copen AInv CST XGL ALA rhoM argv1 [] MDX HMDXvm Hnonul Hndd Hnsl PAx).
    apply Hcopen_ex. intros w md Hmd Hw. cbn beta. rewrite Hw, (HMDXfs md Hmd). reflexivity. }
  destruct (open_may_succeed_b argv1 FS0) eqn:Hob; [|destruct Ht].
  apply open_may_succeed_b_iff in Hob. rename Hob into Ho.

  apply (m_ex_R AInv CST XGL ALA HCST HXGL HLF HCSTdrv HCSTdrv2 rhoM HtopM argv1 [] MDX FS0 HMDXvm HMDXfds HMDXfs Hnonul Hndd Hnsl PAx PAx_m MSX _ Ho).
  intros rho' tp'. unfold post_open_traces, is_dot in Ht. destruct (Sumbool.sumbool_of_bool (path_eqb argv1 dot_path)) as [Hd|Hd]; rewrite Hd in Ht.
  -
    destruct Ht as [<-|[]].
    apply (r_dir_ex AInv CST XGL ALA HLV HCSTok HCSTdrv HLPP _ [] argv1 [] MDX HMDXvm PAx (FD3 argv1) (FD3_dir Hd)).
    apply (HTrderr_ex Hd). intros w md Hmd Hw. cbn beta. rewrite Hw, (HMDXfs md Hmd). reflexivity.
  -
    destruct (fs_lookup FS0 argv1) as [F|] eqn:HF; [|destruct Ht].
    rewrite (FD3_file Hd).
    assert (HMDXfsF : forall md, MDX md -> fs_lookup (m_fs md) argv1 = Some F) by (intros md Hmd; rewrite (HMDXfs md Hmd); exact HF).
    pose proof (clen_config F) as HCC. pose proof (config_len_range F) as HCR.
    apply (r_file_ex AInv CST XGL ALA HCST HXGL HLV HLF HCSTok HCSTdrv HLPP HCSTdrv2 ACX MSX _ F argv1 [] FDS std_fds MDX
             HFDS1 HFDS2 HFDS3 HFDSstep HFDC HFDC1 HFDC2 HMDXvm HMDXfds HMDXfsF PAx PAx_m (PAx_f F HF));
      apply file_traces_inv in Ht; cbn zeta in Ht; unfold DriverSpec.MAX_INPUT, Budget.MAX_INPUT, HDR_MIN, CFG_COUNT_BIT in *.
    + intros HL w md Hmd Hw. cbn beta. rewrite Hw, (HMDXfs md Hmd). cbn [app]. rewrite die_eq.
      destruct Ht as [[? ->]|[[? ->]|[(? & ? & ->)|(? & ->)]]]; try reflexivity; exfalso; lia.
    + intros HL w md Hmd Hw. cbn beta. rewrite Hw, (HMDXfs md Hmd). cbn [app]. rewrite die_eq.
      destruct Ht as [[? ->]|[[? ->]|[(? & ? & ->)|(? & ->)]]]; try reflexivity; exfalso; lia.
    + intros HL w md Hmd Hw. cbn beta. rewrite Hw, (HMDXfs md Hmd). cbn [app]. rewrite die_eq.
      destruct Ht as [[? ->]|[[? ->]|[(? & ? & ->)|(? & ->)]]]; try reflexivity; exfalso; lia.
    + intros HL rhoT rhoX tpX.
      destruct Ht as [[? ->]|[[? ->]|[(? & ? & ->)|(? & ->)]]]; try (exfalso; lia).
      apply (HT_ex_normal F HF HL).
Qed.
End Ex.

End SPINEA.
