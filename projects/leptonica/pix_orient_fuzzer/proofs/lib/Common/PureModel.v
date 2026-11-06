(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_PureModel () := "i59OSSVerify5KrLib6Common9PureModel7md_pure00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK47Corelib4Init9Datatypes4list01C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC4ELinuxProcessSemantics?LinuxProcessSem5State4m_vmC4ELinuxProcessSemantics?LinuxProcessSem5State9vmst_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAvmst_materializedk59OSSVerify5KrLib6Common9PureModel7md_pure01C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib7Numbers7BinNums8positive03C4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedC4ELinuxProcessSemantics?LinuxProcessSem5StateIm_killed_of_m_halted_none".
Import ListNotations.

Record md_pure (md : Model) : Prop := MD_PURE {
  mp_halted : m_halted md = None;
  mp_lazy   : m_vm_lazy md = [];
  mp_mat    : m_vm_materialized md = []
}.

Lemma md_pure_with_vmmaps : forall h md, md_pure md -> md_pure (with_vmmaps h md).
Proof.
ltac2:(KReplay.run1 (kr_t_PureModel ()) [] "p'0h01Hh12H1h22H2h32H3h41hh52mdi009mp_haltedi017mp_lazyi026mp_matp;1p;2p;3p;4g0000R0j14Tg000oj25Tg001ij11Tg002Nj18Tg002lj1ATg003Oj1<Tg0041j1;Tg004hj1:Tg005Jj30Tg005dj29Tg006Dj12Tg006dj13Tg007\j16Tg008<j17Tg009<j1@Tg009oj1?Tg00:gj1=Tg00;gj4>Tg00<fg00=]f0R1#4P0f1R0f3f2R2'5#4P1g00>S#1#1#1#1#1#1#8#AR3#<f4#;%:3301933R4#2R5f5#3%64R430%23R6f6#7%63R330f8f7'5R7P2P0%@7R8#?=054e%37=054eP1%=8=063e%77=063eC>W3W2W1P2P0P1O3n101000000131100101102W0W5W4o"). Qed.

Lemma md_pure_killed_none : forall md, md_pure md -> m_killed md = None.
Proof.
ltac2:(KReplay.run1 (kr_t_PureModel ()) [] "p'0h01Hh12H0h22_Hh33_H0h42mdi009mp_haltedi017mp_lazyi026mp_matp;1p;3p;2g0000R0j1>Tg001ij10Tg002Nj15Tg002lj14Tg003Oj1=Tg00?8j1:Tg004hj19Tg005Jj31Tg0041j16Tg005dj27Tg006Dj12Tg006dj18Tg007\j13Tg008<j1<Tg00?oj2;Tg00=]f0R1#>P0f1R0g00>S#0#0#0#0#0#0#5#4R2#=R3f2R4#:%92R531P1f4#6=1351722R5#2f5#8%3531%22f6#<%3231f7/;4W3W2W0P4P0P1O3n101000000130100101102W1W4o"). Qed.
