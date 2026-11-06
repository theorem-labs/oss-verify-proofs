(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HImage HZBridge HSysStep HSFModel CellsX HArr TacX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HStrFun.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AsDepotInv F_memset AllocWalkKit.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AW_Leaves AW_PoisonShadow AW_SysconfPg AllocTacX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_AW_PoisonRemap1 () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00i69OSSVerify5KrLib3bpA2Rt?AW_PoisonRemap14RENV00C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib7HLFrame5munchC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib7HLFrame5wmonoC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C79OSSVerify5KrLib3bpA2HF3Lib7HLFrame=disjoint_fromC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C47Corelib5Lists7ListDef3mapC79OSSVerify5KrLib3bpA2HF3Lib4TacX2wzC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C79OSSVerify5KrLib3bpA2HF3Lib4TacX2b8C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF3Lib6HCells4cell04C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib3bpA2Rt?AW_PoisonRemap14RENV01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF3Lib6HCells4cell01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib5HStep8rw_cellsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C79OSSVerify5KrLib3bpA2HF3Lib6HCells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC79OSSVerify5KrLib3bpA2HF3Lib7HLFrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt5ASegs5asegsC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib3bpA2HF3Lib6HCells4cell00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib3bpA2Rt8AsShadow3memC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib7HLFrame3ivlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt8AllocRep9AGOT_VALSC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

Record RENV (g : word) (b244 : byte) (m : mem) : Prop := mkRENV {
  re_got  : rw_cells asegs m 1586880 (map (fun v => C8 (wz v)) AGOT_VALS);
  re_shb  : rw_cells asegs m 1636088 [C8 (wz 2147450880)];
  re_hme  : rw_cells asegs m 1639392 [C8 (wz 140737488355327); C8 (wz 0); C8 (wz 0)];
  re_thresh : rw_cells asegs m 2232992 [C8 (wz 0xffffffffffffffff)];
  re_mlim : rw_cells asegs m 2233016 [C8 (wz 0)];
  re_dd   : rw_cells asegs m 2233091 [C1 (b8 1)];
  re_madv : rw_cells asegs m 2233116 [C1 b244];
  re_rms  : rw_cells asegs m 1595272 [C8 (wz 1529088)];
  re_psc  : rw_cells asegs m 2224544 [C8 (wz 4096)];
  re_lpg  : rw_cells asegs m 7225816 [C8 (wz 4096)];
  re_ssp  : rw_cells asegs m 1590544 [C8 (wz 7225176)];
  re_grd  : rw_cells asegs m 7225176 [C8 g]
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
  disjoint_from W 1586880 120 -> disjoint_from W 1636088 8 -> disjoint_from W 1639392 24 -> disjoint_from W 2232992 8 ->
  disjoint_from W 2233016 8 -> disjoint_from W 2233091 1 -> disjoint_from W 2233116 1 -> disjoint_from W 1595272 8 ->
  disjoint_from W 2224544 8 -> disjoint_from W 7225816 8 -> disjoint_from W 1590544 8 -> disjoint_from W 7225176 8 ->
  RENV g b m'.
Proof.
ltac2:(KReplay.run1 (kr_t_AW_PoisonRemap1 ()) ["HCW2"] "p'0h01Eh12MUh21Wh32WMh41bh51gh61mh72m'h86re_dd0h97re_got0h:7re_grd0h;7re_hme0h<7re_lpg0h=8re_madv0h>8re_mlim0h?7re_psc0h@7re_rms0hA7re_shb0hB7re_ssp0hC:re_thresh0hD1vi005re_ddi016re_goti026re_grdi036re_hmei046re_lpgi057re_madvi067re_mlimi076re_psci086re_rmsi096re_shbi0:6re_sspi0;9re_threshp;1p;3p;4p;?p;:g0000j11Tg000Uj1LTg0013j1ITg001Vj1ZTg0028j1XTg002XR0j3OTg003Zj3WTg004Wj3VTg005Tj10Tg0069j34Tg007>j1<Tg007\j4KTg0088j1>Tg008oj1JTg009Oj1UTg00:Fj1GTg00;Cl?STg00<Ej1HTg00=Bj4RTg00>@j3ETg00>`j1QTg00?aj1PTg00@Al:YTf0R1#1#1p=5%11#0p=9%01#1p=2%01#0p=6%01#1#1#1p=@%11#1#1#<p=3%01#0#0#0p=A%11#1#1#1p=;%01#0#0#1p=C%11#<p=N%>1#Hp=Mg00AKR2f2R3f1R4P1CRp=7%01#0#0#0#0#0#0#0p=Bg00BBR5%H4;E1p==AE541p=Dg00C?R6%<4;E1p=?AE6419E63p=F%Q1#P9434p=:P2P1P4P3f3R7f4R8f5R9f6R:f7R;f8R<M:Yp=8%Q1#Pp=Tg00C]R=#1#5R>#1R?#5R@#L#IRA%L>#IRBg00DB%ZB\Ag00E:#XAO873AW473AV287%0=R2#5RA#1RB#1RC#9#2#6#9#@#3RD%62R2#3547%6BRE#0#2#6#9#A#3RF%<>RG548%2A#;#9#ARA#1RH#1#3RI%<B549%0>#;#2#9R>#1RB#0#9RJ#5#3RK=4:G%6J#3RJ=4;G%@>R>#1#5#6#<RL%<=RM54<f9RN%C>#NR>;4Mf:RO%2CRC#2#ARP#1RQ#5RR#0#3RS;4Gf;RT%0?#A#5#9#2R?#0#5#3RU;4Gf<%0=#9#6#5#2#;#C#6#3RV;4Gf=%5C#2#@#2#3RC;4Gf>RW%0=#9#6#5#9#6#C#2#6#3RX;4GP0fCR0fBfARGfD?O0GPWfMRWP6P5%M1XD6RGg00F5CKR077DfNRY%A2#BR2#;#;#;#3#>%J5RZ'=R[77FfOR\%02#6#A#B#B#BR2#<#>g00G3#MR]1D]ZR]'D'=R^77IfPR_%02#B#B#<#>/=ZR277KfQR`?7J]fRRa%UM#G/DZRb77LfSRcfTRd#G/DZ77>%1=#C#2#2#2#2#;#3#>/=ZR=97dSfURe%1@#5#3#>/=ZR@77UfV?7V@fWRf%>X/=ZRg77CfXRhfZRi/=Z77Xf[RjPiPhPffYRkPhPDP0PTPePdPcP6P5PG%2PRP#5#3%5BRB#2#@%5E#C#A#@%0H#3%0A#;%;R%6Q#@%0P#;%1B#C#N%9?#@%J6'?5FM'?'?'?9FIS'?5FF'?'?5FUCK9:fDeA:fD0eM98PfPkPhPFP[POPePdPaA:fF[R[eP[eM98PfPkPhPIP^PNPePdP`A:fI^R^eP^eM98PfPkPhPKP2P<PePdP_A:fK2R2eP2eM98PfPkPhPJP]P;PePdP\A:fJ]R]eP]eM98PfPkPhPLPbP:PePdPYA:fLbRbePbeM98PfPkPhP>%Gi/DZRiP9PePdPWA:f>iRiePieM98PfPkPhPSP=P8PePdfLA:fS=R=eP=eM98PfPkPhPUP@P7PePdfK%T@R=94fURUePUeM98PfPkPhPVP@P3PePdfJA4fV=R=eP=eM98PfPkPhPCPgP4PePdfIA:fCgRgePgeM98PfPkPhPX1=jZRjP1PePdfHA:fXjRjePjeM98M?SW:WBW<W?W@W=W8W>WCW;WAW9PTPOPNP<P;P:P9P8P7P3P4P1O<n300010000001<110110910310;10610010510810710410:102UUUUUUUUUUUUW3W1W0W2W7W6W4W5o"). Qed.

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
