(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_AsanNodesIface () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I79OSSVerify5KrLib2K52AS=AsanPlanSound3APS5cs_ok00C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS8AsanPlan2AP;is_ecall_atC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00C79OSSVerify5KrLib2K52AS8AsanPlan2AP:node_mmap2C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2K52AS9AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS8AsanPlan2AP3nxtC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC79OSSVerify5KrLib2K52AS8AsanPlan2AP2pcC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanSound3APS6cfg_ofC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS7SpinAlg9srealizes00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init5Logic3iffI79OSSVerify5KrLib2K52AS8AsanPlan2AP3acs00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C69OSSVerify5KrLib2K52AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics?LinuxProcessSem2Fs2Fsc69OSSVerify5KrLib2K52AS>AsanNodesIface9OBL_mmap2C1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section Iface.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.

(* [comment removed for export] *)
Definition OBL_mmap2 : Prop := mm2_stmt SEGS A nx0 LIMIT SINV argH FS0 (node_mmap2 A nx0 LIMIT).
Definition OBL_mmapin : Prop := forall hole : bool, mm3_stmt SEGS A nx0 LIMIT SINV argH FS0 (node_mmapin A LIMIT hole).   (* [comment removed for export] *)
Definition OBL_mprotect2 : Prop := mm2_stmt SEGS A nx0 LIMIT SINV argH FS0 (node_mprotect2 A LIMIT).
Definition OBL_brk2 : Prop := brk2_stmt SEGS A nx0 LIMIT SINV argH FS0.
Definition OBL_sys : Prop := forall y : snode, sys_stmt SEGS A nx0 LIMIT SINV argH FS0 y.
Definition OBL_exit : Prop := exit_stmt SEGS A nx0 LIMIT SINV argH FS0.

(* [comment removed for export] *)
Definition OBL_all : Prop := OBL_mmap2 /\ OBL_mmapin /\ OBL_mprotect2 /\ OBL_brk2 /\ OBL_sys /\ OBL_exit.

(* [comment removed for export] *)
Lemma OBL_mmap2_unfold :
  OBL_mmap2 <->
  forall cs csa csb E R FULL model TB,
    cs_ok SEGS A nx0 LIMIT SINV argH FS0 E cs R FULL model ->
    is_ecall_at SEGS cs = true ->
    node_mmap2 A nx0 LIMIT cs = Some (csa, csb) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
        cs_ok SEGS A nx0 LIMIT SINV argH FS0 E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg_of SEGS R' (pc csb) FULL' model') TB) ->
    srealizes SEGS (cfg_of SEGS R (pc cs) FULL model) TB.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesIface ()) ["Iface"] "h01Eh12E'h24FULLh35FULL'h41Hh51Rh62R'h72TBh82csh93csah:3csbh;5modelh<6model'p;1p;2p;<p;3p;4p;5g0000j10Tg000Uj1ETg001:j11Tg001Xj13Tg002;j2DTg002gj18Tg003Il<6Tg004Mj2?Tg005Oj32Tg005ij2>Tg006Ij4=Tg007Jj4<Tg007jj2;Tg008Lj3:Tg009Jj1CTg00:Dj2BTg00:_j14Tg00;Rj17Tg00<Kj55Tg00=Nj39Tg00>Lj4@Tg00>gj2ATg00?@R0g00@<R1g00A;#0R2#E#1%02#0R2#0#0#0#1#3R3'DR4%12#3#8\3R3g00A`R2g00BVp,4SEGSR5p,1AR6p,3nx0R7p,5LIMITR8p,4SINVR9p,4argHR:p,3FS0R;f4R<f7R=f3R>f2R?f1R@M<6g00CNf8RA,?5g00Cn321>00RB#8P6P7P8f9C=P0P0PAP=C<,;B32f;RB=:7>f>#C?:B>'BP5P6P7P8P9P:P;P<f=P>P?P@M<6g00DN%4?f:R?#432P5f5R@f?#7P<P>D5=95?[[[^<2^33^64^11P5P=%7Bf6P@D5=95<[[[[]7];]2]5]0^:0^90]8R0P0[R<P<f0X40R<P<C@g00E</A0eo"). Qed.
End Iface.
