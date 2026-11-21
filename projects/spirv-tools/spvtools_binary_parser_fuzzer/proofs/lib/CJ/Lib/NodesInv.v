(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (munmap cuts both ledgers: a frame lemma proved as text in place of its recorded proof). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import ITree Nodes NodesMM Exec.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_NodesInv () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitI47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedK47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03c69OSSVerify5KrLib2CJ3Lib8NodesInv8vm_constC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transI47Corelib4Init5Logic3and00C69OSSVerify5KrLib2CJ3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC69OSSVerify5KrLib2CJ3Lib5Nodes4eff0C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4andbC69OSSVerify5KrLib2CJ3Lib5Nodes6efferrC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C69OSSVerify5KrLib2CJ3Lib5Nodes?knoaccess_modelC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retK47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib2CJ3Lib5Nodes=kmunmap_modelC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectBmprotect_budget_okC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC69OSSVerify5KrLib2CJ3Lib5Nodes?kbrk_grow_modelC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5Nodes;kmmap_modelC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5Nodes<kfixna_modelC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5Nodes>kfixlost_modelC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5Nodes?kmprotect_modelC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ3Lib8NodesInv=vm_const_reflC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC69OSSVerify5KrLib2CJ3Lib5Nodes<kbrk_grow_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3subC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC56Stdlib6ZArith6BinInt1Z3addC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01I47Corelib4Init5Logic2ex00K47Corelib4Init9Datatypes4list02C4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_forget_rangeC4ELinuxProcessSemantics?LinuxProcessSem5State:map_removeC46Stdlib5Lists4List2InC69OSSVerify5KrLib2CJ3Lib5Nodes9kgrant_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5Nodes<kgrant_ok_naC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib2CJ3Lib5ITree4respC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_errnosC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8Mprotect?mprotect_errnosI69OSSVerify5KrLib2CJ3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I47Corelib4Init5Logic5False00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib2CJ3Lib5Nodes=MAP_ANON_PRIVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5Nodes9PROT_RW_ZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5NodesCMAP_ANON_PRIV_FIXEDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree5tpathC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ3Lib8NodesInv>nstep_vm_constC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ3Lib8NodesInv>vm_const_transC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib2CJ3Lib5ITree4implC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib4Exec3evtC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ3Lib4Exec6msteps00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2CJ3Lib5ITree4nretC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Definition vm_const (mo mo' : Model) : Prop :=
  vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo) /\ vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo).

Lemma vm_const_refl mo : vm_const mo mo.
Proof.
ltac2:(KReplay.run1 (kr_t_NodesInv ()) ["AC_1"] "h02mop;1p;3p;2p;4p10000p4p70p1000`p4p710R0p8p1001>p4p70P0p8p1001lp4p70P0p8g002bj1:Tg003Yj19Tg004Pj31Tg004jj10Tg005Oj18Tg005mj17Tg006Pj26Tg0070j14Tg007Pj15Tg008Jj22Tg008dj43Tg009?g00:5R0f0#:R1#9R2;12g00:S#0#0#0#0#0#0#8#7R3/63#4R3%51R1;1112021231C3W0o"). Qed.
Lemma vm_const_trans a b c : vm_const a b -> vm_const b c -> vm_const a c.
Proof.
ltac2:(KReplay.run1 (kr_t_NodesInv ()) ["AC_1"] "h01Hh12A1h22A2h32B1h42B2h51ah61bh71cp;2p;1p;3p;6p;4g00;8j25Tg002bj11Tg003Yj10Tg004Pj32Tg004jj14Tg005Oj1;Tg005mj1:Tg006Pj29Tg0070j18Tg007Pj13Tg00<5j66Tg008dj47Tg009?R0f2R1f1R2'5g00<SR3g00:5R4%11R5#0f3R6#1R7#032g00:S#4#4#4#4#4#4#;#:R8/98#8R8%35%37321561f5R1/56[f0R6f4#1#0%11R7#0524%37f6R7#1R5#3R95281571P3%05f7R5#1R3#0524%339289f9R9/55P6f8#1#0%19R9#0524%39f:#1R9#3R5528%09R9f<#1R3#0R:524%33R39285P4P9f;#1R9#0P:P2P7E6P8P5%39P3P6P1E6C7W4W3P2P6O2n2001000000120000000W0W2W1P2P6O2n2001000000121000000W0X70X60W5o"). Qed.

(* PLAIN TEXT, not a replay.  [Nodes.kmunmap_model] changed at the
   revision (the exact munmap arm cuts BOTH ledgers through
   [Mmap.mmap_fixed_destroyed_next]), so the serialised proof of this
   lemma no longer replays.  Neither field this lemma speaks about --
   [vm_limit] and [vm_reserved] -- is touched by any arm. *)
Lemma nstep_vm_const : forall n mo rsp mo' evs, nstep n mo rsp mo' evs -> vm_const mo mo'.
Proof.
  intros n mo rsp mo' evs [_ Hn]. unfold vm_const.
  assert (Gid : vm_limit (m_vmmaps mo) = vm_limit (m_vmmaps mo)
                /\ vm_reserved (m_vmmaps mo) = vm_reserved (m_vmmaps mo))
    by (split; reflexivity).
  destruct n; cbv zeta in Hn; try (exfalso; exact Hn).
  - destruct (req =? 0)%Z.
    + destruct Hn as [_ ->]. exact Gid.
    + destruct Hn as [[_ ->] | (_ & _ & ->)];
        [exact Gid | unfold kbrk_grow_model, with_vmmaps; split; reflexivity].
  - destruct ((flags =? MAP_ANON_PRIV) && (prot =? PROT_RW_Z))%Z.
    { destruct Hn as [(e & _ & _ & ->) | (a & _ & _ & ->)];
        [exact Gid | unfold kmmap_model, with_vmmaps; split; reflexivity]. }
    destruct ((flags =? MAP_ANON_PRIV) && (prot =? 0))%Z.
    { destruct Hn as [(e & _ & _ & ->) | (a & _ & _ & ->)];
        [exact Gid | unfold knoaccess_model, with_vmmaps; split; reflexivity]. }
    destruct ((flags =? MAP_ANON_PRIV_FIXED) && (prot =? 0))%Z; [| exfalso; exact Hn].
    (* [vm_forget_range] rewrites only the backing ledgers, so the
       [m_vmmaps] of each post-state is the record built inside it, by
       conversion (the model's [VmMapsDisjoint.vmm_forget_range] is
       [reflexivity] too) *)
    destruct Hn as [(e & _ & _ & ->) | [(_ & ->) | (e & _ & _ & ->)]];
      [exact Gid
      | unfold kfixna_model, vm_forget_range, with_vm_backing, with_vmmaps
      | unfold kfixlost_model, vm_forget_range, with_vm_backing, with_vmmaps];
      split; reflexivity.
  - destruct Hn as [_ ->].
    unfold kmunmap_model, with_mmap_destroyed, vm_forget_range, with_vm_backing,
      mmap_fixed_destroyed_next, with_vmmaps.
    split; reflexivity.
  - destruct Hn as [(e & _ & _ & ->) | (_ & _ & ->)];
      [exact Gid | unfold kmprotect_model, with_vmmaps; split; reflexivity].
Qed.

(* No arm moves the initial stack pointer, so [alloc_top] (which reads it
   only) is the same after every node.  [Path.NI_child] carries
   [alloc_top = alloc_ceiling] across a node with this: at the revision the
   fresh-grant arm's address is [Mmap.linux_place]'s, whose window is
   bounded by [alloc_top]. *)
Lemma nstep_init_sp : forall n mo rsp mo' evs, nstep n mo rsp mo' evs ->
  vm_init_sp (m_vmmaps mo') = vm_init_sp (m_vmmaps mo).
Proof.
  intros n mo rsp mo' evs [_ Hn].
  destruct n; cbv zeta in Hn; try (exfalso; exact Hn).
  - destruct (req =? 0)%Z.
    + destruct Hn as [_ ->]. reflexivity.
    + destruct Hn as [[_ ->] | (_ & _ & ->)];
        [reflexivity | unfold kbrk_grow_model, with_vmmaps; reflexivity].
  - destruct ((flags =? MAP_ANON_PRIV) && (prot =? PROT_RW_Z))%Z.
    { destruct Hn as [(e & _ & _ & ->) | (a & _ & _ & ->)];
        [reflexivity | unfold kmmap_model, with_vmmaps; reflexivity]. }
    destruct ((flags =? MAP_ANON_PRIV) && (prot =? 0))%Z.
    { destruct Hn as [(e & _ & _ & ->) | (a & _ & _ & ->)];
        [reflexivity | unfold knoaccess_model, with_vmmaps; reflexivity]. }
    destruct ((flags =? MAP_ANON_PRIV_FIXED) && (prot =? 0))%Z; [| exfalso; exact Hn].
    destruct Hn as [(e & _ & _ & ->) | [(_ & ->) | (e & _ & _ & ->)]];
      [reflexivity
      | unfold kfixna_model, vm_forget_range, with_vm_backing, with_vmmaps
      | unfold kfixlost_model, vm_forget_range, with_vm_backing, with_vmmaps];
      reflexivity.
  - destruct Hn as [_ ->].
    unfold kmunmap_model, with_mmap_destroyed, vm_forget_range, with_vm_backing,
      mmap_fixed_destroyed_next, with_vmmaps.
    reflexivity.
  - destruct Hn as [(e & _ & _ & ->) | (_ & _ & ->)];
      [reflexivity | unfold kmprotect_model, with_vmmaps; reflexivity].
Qed.

Lemma tpath_vm_const {R} : forall (t : itree node R) mo tr r mo', tpath nstep t mo tr r mo' -> vm_const mo mo'.
Proof.
ltac2:(KReplay.run1 (kr_t_NodesInv ()) ["AC_1"] "p'0h03tr'h11Hh23evsh33mo'h42moh53mo1h61rh72trh82Hph92_Hh:1th;2Hnh<2IHh=1Rh>3_H0h?3effh@1khA1nhB2r0hC3rspi001xp;2p;1p;3p;6p;4p;5p;8p200R0g00jCR1p4p7210p8P0g00k>R2p4p73110p8g00l5j28Tg0070j1FTg00<nj1@j69Tg00;8j24Tg00lnj3ETg004Pj30Tg00=ej1?Tg00N_j1>Tg000`j6=Tg00mgj4<Tg00XRR3j21Tg00n`j6DTg00ocj5CTP1j6ATP2j8;Tg00<SR2j27Tg010fj3BTg00bkR1f6R4f5R5f4R6f3R7f2R8f1R9f0R:G;p=6A089:,77p=:g00ccR;?B9:p=5P1f7R<P4P5P6P7P8P9G;/7:p=2P4P5P6P7P8P9E9/7:p=3181:P1P91819g009?R=%F;R>p,5ACEILR?#@R@P4P6P7P8P9P:F61469RA[^3=^66]7]4W:P@P4AE146P7P8P9P:F6P2A0<58A0=96P>P7%?;R;C:1458RBP:f9RC?0<6A0=6<P>P4P;C:P2f8RD90=5A0><;14C4REP:f:RF90=<P=f;RGA0>G;f=RH/49[X3=A0>F;f<R;#>W>PDP:E=W1P9P:O2n2001000000120000000W1W9P9P:O2n2001000000120000000W8X3=X66X7>X4=XB9g00^mRI1817[P@PDP5P6O1P7P8P9P:F6PA[^3=^64^7>^4=\IP@PDP1PDP4P5C<P7P8P9P:F6P3PIP?PGPDP7P8P9P@PHPFP7O1P8P:P4P5159:RA90><G2F3X0>,1>X2>,1>X5=,1=XCIPBP:P?PHPFP7P8P9P@f?RBP;P7O1P8P:PDP<A0>CAG2F3X0>,1>X2>,1>X5=,1=P3P=P?f>RJPGP6P8P9P@f@RKPHP6O1P8P:PCPDA0>FAG2F3X0>,1>X2>,1>X5=PEP:P?PKPHP4P8P9P@fBREPBP4O1P8P:PGPFA0>;AG2F3X0>,1>X2>,1>P3P>P?fARLPJP<P7P9P@fCRMPKP<O1P7P:P;PGA0>HAG2F3X0>,1>X2>14HFP:P?PMPKPCP5P9P@fER7PEPCO1P5P:PJPHA0>BAG2F3X0>,1>P3P>P?fDR3PLPFP4P8P@fFRAPMPFO1P4P:PBPJ158:90>KG2F3X0>14LJP:P?PAPMP;PDP6P@fHRJP7P;O1PDP:PLPK156:90>EG2F3P2P?fGR8P3PHPCP5E9P@fIRFPAPHO1PCP9PEPL155990>MG2147EP:P?PFPAPBPGP<E9P@fLRGPFPKO1P;P6P7P315D690>AG2P2P@fMR2fJR6PLO1PHP5PAP7F615C590>814FAP:P@fOR@PGPMO1PBP<PJP8F615;D90>6PGPLPFP@PGP7PLPHP5EDP2P7PLPCP6PFP9O6DCW9W8P9P:O2n2001000000120000000W1W;P9P:O2n2001000000120000000W1X0>P9P:O2n2001000000120100000W1X2>P9P:O2n2001000000121100000W1X5=P9P:O2n2001000000121100000W1X?IP9P:O2n2001000000121100000W8X3=X64X7>X4=W<W@XA1P:EAW:X=0o"). Qed.

Section IMPL.
Variable segs : list Segment.
Lemma impl_tpath_leaf {R} : forall (t : itree node R) (Q : R -> machine_state -> Prop) ms mo tr r mo',
  impl segs (at_node segs) t Q ms -> tpath nstep t mo tr r mo' -> exists ms', Q r ms'.
Proof.
ltac2:(KReplay.run1 (kr_t_NodesInv ()) ["AC_1"; "IMPL"] "p'0h03ms'h11Hh23tr'h33rsph43evsh52Hih61Qh72_Hh82moh93mo'h:3mo1h;2msh<1rh=2trh>2Hph?2r0h@1thA2HQhB2HkhC2HnhD2IHhE1RhF3_H0hG3effhH1khI3ms1hJ1ni001xp;2p;1p;3p;4p;7p;6p;8p200R0g00jCR1p4p7210p8P0g000`R2p4p710p8P0g011CR3p4p741110p8P0g00k>R4p4p73110p8g00l5j2>Tg0070j1LTg0129j1Fj39Tg00<nj1Kj6=Tg00lnj3@Tg004Pj30Tg00=ej1DTg0132j3?Tg013fj37Tg00<SR5j25Tg014_j4JTP2j7ITg00mgj4ATg00XRR2j21Tg0159j2:TP1j6ETP3j7GTP4j8CTg010fj3HTg00bkR4f5R3f4R1f3R6f2R7f1R8f0R9FGp=4P4f6R:P3P1P6P7P8P9GCp=;g015oR;/19p=2A0789,56p=<g00ccR<?H89p=8P4f7R=P:P3P1P6P7P8GC/59p=3P:P3P1P6P7P8E=/59p=61589,57p=B1>49P4P81>48p-0\;R>\7R?g009?R@%L<RAp,4segsRB%FBRCf8RDP:P3P1E4p,5ACEILRE#KRFf9RGP=P1P6P7P8F;PDP1P9O2X0;#2RH[[^9@^<:]=]8^;;]6W@PBPCPDA@4D:P3P1E4PFPGA@4G=P1P6P7P8F;P5f:RI?0D6A0@73PAP1%D<R<C<PGP3P9O2X0;#2RJP9f<RK?0I3f=RLP:f;RMP9O1=?BIA0@=IPAPGP<C<f>RNPIP9O2X0;#2RO[]5X?LPIP:O1=?BGA0@:GPAPDP<C<P2P;A7BK9PLPGP9O2R<'5X0;POP8A7BN9f?ROPMP9O2'5P5A7BO8f@RPPKP8O2fBRQPNP9O2X0;#2P9fARR=7B6fCRSPOP1O2P;fERTPRP9O2X0;RUP3P9CJWAW7P8P9O2n2001000000120000000W1X0;P8P9O2n2001000000120100000W7W5PMP9P1FIW1P8P9O2n2001000000120000000W>W5X9@X<:X=AX8@X;;X6?X?8g00^mR?1>46[P>\1R>PBPCPIP=P:O1P3P1E4PFPMPDP=O1P1P6P7P8F;PH[[^9@^<D^=A^8@^;;]6\?PBPCPIP4PIPDP=CAP3P1E4PFPMP4PMPGPDCAP1P6P7P8F;P2P?PEPNPGP6P7P8PFPPPLP6O1P7P9P=P:1889RH90ADG3F6X2A,1AX4A,1AX:@,1@X3?PJP9PEPPPMP6P7P8PFPQPOP6O1P7P9PGPDA0AIHG3F6X2A,1AX4A,1AX:@,1@P2P@PEPRPKP1P7P8PFPSPPP1O1P7P9PIPGA0AMHG3F6X2A,1AX4A,1AX:@P<X0;#2P9PEPSPNP:P7P8PFPTPQP:O1P7P9PKPMA0ALHG3F6X2A,1AX4A,1AP2PAPEfDR<POP=P6P8PFfFRJPSP=O1P6P9PLPKA0ANHG3F6X2A,1AX4APRPLP9O2X0;#2P9PEPJPRPGP3P8PFfHRVPTPGO1P3P9POPNA0APHG3F6X2A,1AP2PAPEfGRHPQPIP:P7PFfIRNPJPIO1P:P9PPPO187990ARG3F6X2A%2UP9PEPNP<PKPDP1PFfKRUPVPKO1PDP9PQPR181990ASG3F6P5PEfJPTPLPGP3E=PFfLRIPNPLO1PGP8PSPQ183890A<G3PNPTP9O2X0;#2P9PEPIPHPOPMP=E=PFfORMPIPPO1PKP1PJPT18D190AHG3P5PFfPfMRPPRO1PLP3PHPJF;18G390AVPPPNP9O2X0;#2P9PFfRRFPMPSO1POP=PNPVF;18KD90AUP2P;A7BM9fSRM=9B9PBPCfVR2PMP9O1fQRU1:89RKE4^3?3BX0;PUPPP9O2X0;#2PNA7BU9fURN=9B9PBPCfXRVPNP9O1PMPKE4^3?3BP5A7BF8A9B28PBPCfYRFP2P9O1fTRK1:79E4^3?'5PNPUP9O2X0;#2P9A7BK6A9BF1PBPCf\R1PFP9O1fWRK1:39E4^3?'5P5fZR5=9B3PBPCf]R3P5P9O1PV1::9E4^3?PFPNP9O2X0;#2P9A9B1=PBPCf`P3P9O1f[R31:G9E4^3?P1PUP31:GUPPPTPKP2P9PUO1PLO9WBWFP8P9O2n2001000000120000000W1W7P8P9O2n2001000000120000000W1XI;P8P9O2n2001000000120100000W7W>P8P9O2n2001000000120000000W1WCP8P9O2n2001000000121000000W1X2AP8P9O2n2001000000121100000W1X4AP8P9O2n2001000000121100000W1X:@P8P9O2n2001000000121100000W1XG?P8P9O2n2001000000121100000W>W5X9@X<DX=AX8@X;;X6>WDWHXJ4P9EEW@XE0o"). Qed.
End IMPL.

End AC_1.
