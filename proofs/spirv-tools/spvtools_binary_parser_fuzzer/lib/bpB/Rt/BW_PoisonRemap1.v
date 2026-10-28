(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BStrFun.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsAtomics BsDepotInv B_memset BllocWalkKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BW_Leaves BW_PoisonShadow BW_SysconfPg BllocTacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BW_PoisonRemap1 () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00i6ARocqVerifyHarness?AgentSubmission3bpB2Rt?BW_PoisonRemap14RENV00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5munchC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame5wmonoK47Corelib7Numbers7BinNums8positive01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame=disjoint_fromK47Corelib7Numbers7BinNums1Z02C47Corelib5Lists7ListDef3mapC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BacX2wzK47Corelib4Init9Datatypes4list01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BacX2b8K7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell04k6ARocqVerifyHarness?AgentSubmission3bpB2Rt?BW_PoisonRemap14RENV01K7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell01C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep8rw_cellsK47Corelib4Init9Datatypes4list02C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells:cells_sizeC56Stdlib6ZArith6BinInt1Z6of_natC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrameBrw_cells_transportC6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsI7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BsShadow3memC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3ivlC6ARocqVerifyHarness?AgentSubmission3bpB2Rt8BllocRep9AGOT_VALSK47Corelib7Numbers7BinNums1Z01".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

Record RENV (g : word) (b244 : byte) (m : mem) : Prop := mkRENV {
  re_got  : rw_cells asegs m 1593472 (map (fun v => C8 (wz v)) AGOT_VALS);
  re_shb  : rw_cells asegs m 1642552 [C8 (wz 2147450880)];
  re_hme  : rw_cells asegs m 1645856 [C8 (wz 140737488355327); C8 (wz 0); C8 (wz 0)];
  re_thresh : rw_cells asegs m 2239456 [C8 (wz 0xffffffffffffffff)];
  re_mlim : rw_cells asegs m 2239480 [C8 (wz 0)];
  re_dd   : rw_cells asegs m 2239555 [C1 (b8 1)];
  re_madv : rw_cells asegs m 2239580 [C1 b244];
  re_rms  : rw_cells asegs m 1601864 [C8 (wz 1535652)];
  re_psc  : rw_cells asegs m 2231008 [C8 (wz 4096)];
  re_lpg  : rw_cells asegs m 7232280 [C8 (wz 4096)];
  re_ssp  : rw_cells asegs m 1597136 [C8 (wz 7231640)];
  re_grd  : rw_cells asegs m 7231640 [C8 g]
}.

End HCW.

Ltac open_renv E :=
  destruct E as [Rgot Rshb Rhme Rthresh Rmlim Rdd Rmadv Rrms Rpsc Rlpg Rssp Rgrd]; unfold AGOT_VALS in Rgot; cbn [map] in Rgot.

Ltac split_frame FR sizes :=
  lazymatch type of FR with rw_cells _ _ _ [CB ?n ?j] =>
    let J := fresh "J" in remember j as J in FR;
    match goal with E : J = j |- _ => clear E end;
    apply (rw_cells_split_CB asegs _ _ [] n J [] sizes) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR;
    repeat match type of FR with context [CB _ (take ?k ?l)] => let K := fresh "jk" in remember (take k l) as K in FR end;
    repeat match type of FR with context [CB _ (drop ?k ?l)] => let K := fresh "jk" in remember (drop k l) as K in FR end;
    repeat match goal with H : _ = take _ _ |- _ => clear H | H : _ = drop _ _ |- _ => clear H end
  end.

Section HCW2.
  Context {HCEIL : HeapCeil}.

Lemma renv_transport : forall g b m m' W,
  RENV g b m -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W 1593472 120 -> disjoint_from W 1642552 8 -> disjoint_from W 1645856 24 -> disjoint_from W 2239456 8 ->
  disjoint_from W 2239480 8 -> disjoint_from W 2239555 1 -> disjoint_from W 2239580 1 -> disjoint_from W 1601864 8 ->
  disjoint_from W 2231008 8 -> disjoint_from W 7232280 8 -> disjoint_from W 1597136 8 -> disjoint_from W 7231640 8 ->
  RENV g b m'.
Proof.
ltac2:(KReplay.run1 (kr_t_BW_PoisonRemap1 ()) ["HCW2"] "p'0h01Eh12MUh21Wh32WMh41bh51gh61mh72m'h86re_dd0h97re_got0h:7re_grd0h;7re_hme0h<7re_lpg0h=8re_madv0h>8re_mlim0h?7re_psc0h@7re_rms0hA7re_shb0hB7re_ssp0hC:re_thresh0hD1vi005re_ddi016re_goti026re_grdi036re_hmei046re_lpgi057re_madvi067re_mlimi076re_psci086re_rmsi096re_shbi0:6re_sspi0;9re_threshp;1p;3p;4p;?p;:g0000j11Tg000Uj1VTg0013j1RTg001Vj1cTg0028j1_Tg002XR0j3WTg003Zj3]Tg004Wj3\Tg005Tj10Tg0069j33Tg007>j1ATg007\j4TTg0088j1CTg008oj1STg009Oj1[Tg00:Fj1OTg00;Cl?aTg00<Ej1ZTg00=Bj4`Tg00>@j3KTg00>`j1XTg00?aj1YTg00@Al:^Tf0R1#1#1p=:%11#1#1#1p=9%01#1#0#1p=E%11#1#1#0p=?%11#1#1#Ap=2%01#0p=Q%11#1#0#1p=4%11#0#0#0p=;%11#1#0#0p=<%11#0#1#1p=@%11#0#1#0p=B%01#0#1#1p=J%01#0#0#0p=M%01#1p=I%01#0#0#1p=L%11#Ap=P%01#1#1#1p=7%11#0p==%01#1#0#0p=H%C1#Zp=Ug00AKR2f2R3f1R4P1C`p=5%01#0#0#0#0#0#0#0p=Fg00BBR5%Z4;K1p=>AK541p=Gg00C?R6%A4;K1p=DAK6419K63p=N%X1#Y9334p=8P2P1P4P3f3R7f4R8f5R9f6R:f7R;f8R<M:^p=6%X1#Yp=bg00C]R=#1#:R>#1#:R?#V#RR@%V>#RRAg00DB%cA\@g00E:#_AW873A]473A\287%0=#9#E#?#9#2R2%0=R@#QRA#2537%0=#4#4#9#;#2RB%A>R>538%0=#4#<#E#@#2RC%2@539%:=#@#B#;#J#2R@=3:>%:=#@#B#;#M#2RD=3;>%1=#4#4#J#@#<#ARE%A=RF53<f9RG%:=#@#B#I#4#L#PRH;3Ff:RI%0=#:#<#7#E#=#2RJ;3>f;RK%:=#@#?#B#J#2RL;3>f<%0=#=#J#H#=#I#<#2RM;3>f=%0=#:#4#M#=#E#2RN;3>f>RO%0=#=#J#H#?#<#2RP;3>P0fCR0fBfAR>fD?W0>POfMROP6P5%U1XD6R>g00F5CTR0752fNRQ%MA#FRA#9#9#9#2#C%S5RR'>RS75BfORT%0A#Q#M#F#F#FRA#A#Cg00G3#URU1GURRU'G'>RV75CfPRW%0A#F#F#A#C/>RRA75@fQRX?5DUfRRY%[F#O/GRRZ75EfSR[fTR\#O/GR75H%1=#Q#H#;#B#4#P#C/>RR]95\JfUR^%1?#:#2#C/>RR?75LfV?5M?fWR_%CP/>RR`75NfXRafZRb/>R75Pf[RcPbPaP_fYRdPaP2P0PKP^P\P[P6P5P>%0=#9#L#<#9#2%1=#4#4#H#=#I#7%7=#L#7#<#7%0=#4#<#E#B#2%I=#@#;#=#<#9%7=#;#?#@#9%7=#;#?#;#7%7=#;#?#I#=#9%?=#?#B#E#L#P%1=#:#7#4#H#=#7%S6'D5NF'D'D'D9NCJ'D5NB'D'D5NLCT98_2eA8_20eM96P_PdPaPBPSPIP^P\PYA8_BSRSePSeM96P_PdPaPCPVPGP^P\PXA8_CVRVePVeM96P_PdPaP@PAP<P^P\PWA8_@ARAePAeM96P_PdPaPDPUP;P^P\PTA8_DURUePUeM96P_PdPaPEPZP:P^P\PQA8_EZRZePZeM96P_PdPaPH%Ob/GRRbP9P^P\POA8_HbRbePbeM96P_PdPaPJP]P8P^P\fLA8_J]R]eP]eM96P_PdPaPLP?P7P^P\fK%b?R]93_LRLePLeM96P_PdPaPMP?P3P^P\fJA3_M]R]eP]eM96P_PdPaPNP`P4P^P\fIA8_N`R`eP`eM96P_PdPaPP1>cRRcP1P^P\fHA8_PcRcePceM96M?aW:WBW<W?W@W=W8W>WCW;WAW9PKPIPGP<P;P:P9P8P7P3P4P1O<n300010000001<110110910310;10610010510810710410:102UUUUUUUUUUUUW3W1W0W2W7W6W4W5o"). Qed.

End HCW2.

Ltac renv_at E MU WM E' :=
  lazymatch type of MU with munch ?W ?m ?m' =>
    lazymatch type of E with RENV ?g ?b m =>
      region_table; region_hull_memo W;
      assert (E' : RENV g b m');
      [ apply (renv_transport g b m m' W E MU WM); cbn [disjoint_from]; region_decide | ]
    end end.

Section HCW3.
  Context {HCEIL : HeapCeil}.

Definition prm_pb (addr : Z) : Z := round_up (sh addr) 4096.
Definition prm_pe (addr size : Z) : Z := round_down (sh addr + size / 8) 4096.

End HCW3.
