(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_AsanNodesIfaceK () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK5cs_ok00C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK;is_ecall_atC13~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK:node_mmap2C13~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AxSymRun3K9env_agreeC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK3nxtC13~~~I47Corelib4Init5Logic3and00C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK2pcC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>AsanPlanSoundK4APSK6cfg_ofC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~K47Corelib4Init5Logic3and01C47Corelib4Init5Logic3iffI47Corelib4Init9Datatypes4bool00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9AsanPlanK3APK3acs00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;AxSymExec3K4AX2K3env00C13~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~K47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode;bm_off_instC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?AsanNodesIfaceK9OBL_mmap2C13~~~".
Import ListNotations.
Import AX2K.
Unset Nia Cache. Unset Nra Cache. Import AX2SK. Import APK. Import APSK.
Open Scope Z_scope.

Section Iface.
Variable SEGS : list Segment.
Variable scfg : SpuriousCfg.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.

(* [comment removed for export] *)
Definition OBL_mmap2 : Prop := forall split : bool, mm2_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 (node_mmap2 A nx0 LIMIT split).   (* [comment removed for export] *)
Definition OBL_mmapin : Prop := forall hole : bool, mm3_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 (node_mmapin A LIMIT hole).   (* [comment removed for export] *)
Definition OBL_mprotect2 : Prop := mm2_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 (node_mprotect2 A LIMIT).
Definition OBL_brk2 : Prop := brk2_stmt SEGS scfg A nx0 LIMIT SINV argH FS0.
Definition OBL_sys : Prop := forall y : snode, sys_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 y.
Definition OBL_exit : Prop := exit_stmt SEGS scfg A LIMIT SINV argH FS0.

(* [comment removed for export] *)
Definition OBL_all : Prop := OBL_mmap2 /\ OBL_mmapin /\ OBL_mprotect2 /\ OBL_brk2 /\ OBL_sys /\ OBL_exit.

(* [comment removed for export] *)
Lemma OBL_mmap2_unfold :
  OBL_mmap2 <->
  forall split cs csa csb E R FULL model TB,
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model ->
    is_ecall_at SEGS cs = true ->
    node_mmap2 A nx0 LIMIT split cs = Some (csa, csb) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
        cs_ok SEGS A LIMIT SINV argH FS0 E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS scfg (cfg_of SEGS R' (pc csa) FULL' model') TB) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
        cs_ok SEGS A LIMIT SINV argH FS0 E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS scfg (cfg_of SEGS R' (pc csb) FULL' model') TB) ->
    srealizes SEGS scfg (cfg_of SEGS R (pc cs) FULL model) TB.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesIfaceK ()) ["Iface"] "h02E'h15FULL'h22R'h36model'h41Eh54FULLh61Hh71Rh82TBh92csh:3csah;3csbh<5modelh=5splitp;1p;2p;;p;3p;5p;4g0000j10Tg000Uj1ETg001:j13Tg001Xj16Tg002;j2DTg002gj1:Tg003Il;9Tg004_j2ATg0063j31Tg006Mj2@Tg006mj5?Tg008@j4>Tg008`j2=Tg009Bj32Tg00:Qj1<Tg00;]j2;Tg00<8j14Tg00<kj17Tg00>6j58Tg00?Kj55Tg00@Wj4CTg00A2j2BTg00AKR0g00AkR1g00C9R2g00DJ#0R3#E#3%03#0R3#0#0#0#3#6R4'DR5%33#6#:\4R4g00DoR3g00Eep,4SEGSR6p,1AR7p,5LIMITR8p,4SINVR9p,4argHR:p,3FS0R;f4R<f7R=f3R>f2R?f1R@M;9f8RA,A6g00Fm5101@11R0#:P7p,3nx0RBP8f:RCf9D?P1P1PAP=C>,=031f;R0=2B>f>RD#<?20>';P6P7P8P9P:P;P<PDP>P?P@M;9R@g00GMRD%4?R?%4C31g00H;R;P6p,4scfgR:P6f5R9f@#7P<P>D8R<PCD5[[[^33^14^25^02f<RC=2B>f?#<?2C>';%4091D?P;P6P:P<P0D5[\@[^33^14^25^02P;P6P:P6PA%7CP=f6D8P9D5[[[[[]8]<]5]7]4^;1^:1]9]=R1P1[R9P9f0X61R9P9CCg00IG/B1eo"). Qed.
End Iface.
