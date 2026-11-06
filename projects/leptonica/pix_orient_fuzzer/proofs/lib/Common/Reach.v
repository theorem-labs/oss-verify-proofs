(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim WallSim StreamSim DrainSim StepTac ShapeAlg PureModel.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Reach () := "I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01c59OSSVerify5KrLib6Common5Reach5reachC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K59OSSVerify5KrLib6Common6CatSim6msteps02C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic2ex00K59OSSVerify5KrLib6Common6CatSim6msteps01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6CatSim<msteps_transC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common9PureModel7md_pure00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9PureModel9mp_haltedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9PureModel7mp_lazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg9rz_mstepsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~".

Definition reach (segs : list Segment) (st : machine_state) (P : machine_state -> Prop) : Prop :=
  exists fin, msteps segs st fin /\ P fin.

Lemma reach_step : forall segs ms ms' (P : machine_state -> Prop),
  ms_svc_pending ms = None -> RiscvSemantics.step segs ms = MachineOk ms' -> reach segs ms' P -> reach segs ms P.
Proof.
ltac2:(KReplay.run1 (kr_t_Reach ()) [] "p'0h03finh11Hh22H1h32H2h42H3h52HPh61Ph72msh83ms'h94segsi001xp;1p;3p;2p;7p;4g0000j1@Tg000Pj10Tg0015j19Tg001Sj15Tg0026j1?Tg002Xj1;Tg003^j1:Tg004@j34Tg004Zj18Tg005bj26Tg006^j27Tg007fj32Tg008]j31Tg009XR0j23Tg00:3j7>Tg00:nj4=Tg00;Ij4<Tg00;c#@g00<bR1p-0\1g00=i#0#0#0#0#0#0#9#5R2#?f2R3#;%:234%81f4R2f3R4'6171334f5R5?243g00>NP1f7R3f0R6715P2P6O1'3X01f6R7=232P6f9R8?136P7P6O1'3P0f:R0f8R7f1R931P3P9O1f;R3?207P6f<R7?104P0P2O1P1f?f>R2;16P7P6O1'3X01P5f=R4=125P3P5O1P2P4P7P5P0P8P9F>P6C=C<W5W4P9P6O2n2001000000120000000W1X01P9P6O2n2001000000120100000W1W3W2W6X81W7W9o"). Qed.

Lemma reach_done : forall segs ms (P : machine_state -> Prop), P ms -> reach segs ms P.
Proof.
ltac2:(KReplay.run1 (kr_t_Reach ()) [] "h02HPh11Ph23finh32msh44segsp;1p;3p;2p;4g0000j15Tg008]j30Tg009Xj22Tg00>hj21Tg00:nj44Tg00;Ij43Tg00;c#5g00<bR0p-0\0f0R1f1R2O1P0f4f3R3;01f2R4P1O1'2X20P4A0344P2P4O11134P1C4C3W0W1W3W4o"). Qed.

Lemma reach_msteps : forall segs ms ms' (P : machine_state -> Prop), msteps segs ms ms' -> reach segs ms' P -> reach segs ms P.
Proof.
ltac2:(KReplay.run1 (kr_t_Reach ()) [] "p'0h03finh11Hh22H1h32H2h42HPh51Ph62msh73ms'h84segsi001xp;1p;3p;2p;6p;4g0000j16Tg008]j30Tg007fj32Tg009XR0j21Tg00?cj65Tg00:nj44Tg00;Ij43Tg00;c#6g00<bR1p-0\1f3R2f2R3f1R430f4R5?234g00>NP1f6R3f0R6705P2P6O1'1X01f5R7=232P6f8?036P7P6O1'1P0f9R0f7R8;04P3P4O1f:R3?208P6f;R8?002P0P5O1P1f>f=R5;06P8P6O1'1X01P7f<R2=057P3P7O1P5P2P8P7P0P4E5P6C4C3W4W3P4P6O2n2001000000120000000W1X01P4P6O2n2001000000120100000W1W2W5X71W6W8o"). Qed.

Lemma reach_weaken : forall segs ms (P Q : machine_state -> Prop), (forall fin, P fin -> Q fin) -> reach segs ms P -> reach segs ms Q.
Proof.
ltac2:(KReplay.run1 (kr_t_Reach ()) [] "p'0h03finh12H0h21Hh32HPh43HPQh51Ph61Qh72msh84segsi001xp;1p;3p;2p;4g0000j15Tg007fj32Tg008]j30Tg009XR0j21Tg00:nj44Tg00;Ij43Tg00;c#5g00<bR1p-0\1R2f2R3f0R4O1P3f1R5O1[^01f4R6f3R7;23g00>NP1f6R3f5R8;04P6P4O1'1X01A2387P4f8R9f7R:;04P3P4O1'1P0f9R0?095P:P5O1f:R9?20:P4f;R:?097P9P6O1P1f>f=R6;04P:P4O1'1X01P8f<=068P9P8O1P5P0P8P4O2C4C3W3W2P5P4O2n2001000000120000000W1X01P5P4O2n2001000000120100000W1W4X62W5W7W8o"). Qed.

(* [comment removed for export] *)
Lemma reach_bind : forall segs ms (P Q : machine_state -> Prop), reach segs ms P -> (forall fin, P fin -> reach segs fin Q) -> reach segs ms Q.
Proof.
ltac2:(KReplay.run1 (kr_t_Reach ()) [] "p'0h03finh11Hh22H1h32H2h42HFh52HPh62HQh71Ph81Qh93midh:2msh;1rh<4segsi001xp;1p;3p;2p;6p;4g0000j17Tg007fj31Tg008]j30Tg009XR0j22Tg00>NR1j26Tg00?cj65Tg00:nj44Tg00;Ij43Tg00;c#7g00<bR2p-0\2R3f3R4f2f1R531P1P2f5R6f4R7f0R830P4P8O1'2X02P7P8O1f7R9?157[^02f6R:?164[P8A09:8P6P8O1'2P0f8R;?095P:P5O1P;P8O1f;R<?15;[^02f:R=f9R>;19[P8A0=>4P>P7O1P<P8O1R>f>R??15<[^02P8P:P5O2A0?98/2>X02,62P1P2f?R1?0;8f<R;P8O1'2X02A11?;P8fA?0=8P?P8O1'2P0fBR0?0<5P1P5O1fCR?f@710P8fDR=f=;04P0P7O1P2fGfFR7;08P=P8O1'2X02P6fER==076P?P6O1P7P=P1P6P<P5E5P8C4C3W4W3P5P8O2n2001000000120000000W1X02P5P8O2n2001000000120100000b;W6W5W2P5P8O2n2001000000120000000W1X92P5P8O2n2001000000120100000W1X83W7W:W<o"). Qed.

(* [comment removed for export] *)
Lemma rz_reach : forall segs ms md (P : machine_state -> Prop) T,
  md_pure md -> reach segs ms P -> (forall fin, P fin -> realizes segs (mkCfg fin md) T) -> realizes segs (mkCfg ms md) T.
Proof.
ltac2:(KReplay.run1 (kr_t_Reach ()) [] "p'0h03finh11Hh22HFh32HKh42HPh53Hmsh61Ph71Th82mdh92msh:4segsi001xp;1p;3p;2p;9g0000j19Tg00@bj18Tg007fj34Tg008]j32Tg009XR0j23Tg00Aaj20Tg00BVj31Tg00CUj25Tg00DTj26Tg00EQl97Tg00;c#9g00<bR1g00FOp-0\1g00GEf2R2#8f5R3f4R4;42g00>NP1f7R5f6R6f0R732P4P7O1'3X01P3P7O1f9R8f1R9/05;13[^01f8R31056;14[P7A2837P6P7O1'3P0f:R0?289P5P9O1P8P7O1f=R5f;R:,09;18[^01f<R810:0;13[P7f3928:P0P4O1P8P7O1f@f>R4,09;18[^01f?P4P6P5P:15501650P2P7P6P9O2M97W3W2W5P9P7O2n2001000000120000000W1X01P9P7O2n2001000000120100000W1W4W7W6W8W9W:o"). Qed.

(* [comment removed for export] *)
Ltac chain_step ::=
  first [ eapply reach_step
        | eapply mst_step
        | eapply tw_step
        | eapply twm_step
        | eapply MmapSim.twmt_step
        | eapply tmw_step
        | eapply StreamSim.twr_step
        | eapply StreamSim.trd_step
        | eapply WallSim.twt_step
        | eapply WallSim.twe_step
        | eapply DrainSim.tout_step
        | eapply DrainSim.trd_step
        | eapply te_step ].

(* [comment removed for export] *)
Ltac norm_pc ::=
  try lazymatch goal with
  | |- reach _ ?st _ => norm_pc_state st
  | |- msteps _ ?st _ => norm_pc_state st
  | |- to_wexit _ ?st _ _ => norm_pc_state st
  | |- twm _ ?st _ _ _ => norm_pc_state st
  | |- MmapSim.twm_pend _ ?st _ _ _ _ => norm_pc_state st
  | |- MmapSim.twm_tail _ ?st _ _ _ _ => norm_pc_state st
  | |- tmw _ ?st _ _ _ _ _ => norm_pc_state st
  | |- StreamSim.to_wr _ _ _ ?st => norm_pc_state st
  | |- StreamSim.to_rd _ _ _ ?st => norm_pc_state st
  | |- WallSim.to_wall _ _ ?st _ _ => norm_pc_state st
  | |- WallSim.to_wall_tail _ _ ?st _ _ => norm_pc_state st
  | |- WallSim.to_wallexit _ _ _ _ ?st => norm_pc_state st
  | |- to_exit _ _ ?st => norm_pc_state st
  | |- DrainSim.to_out _ _ ?st => norm_pc_state st
  | |- DrainSim.to_rd _ _ _ _ _ _ _ ?st => norm_pc_state st
  end.
