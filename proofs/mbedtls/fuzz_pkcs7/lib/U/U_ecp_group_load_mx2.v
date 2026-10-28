(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface Image.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_platform_zeroize U_platform_zeroize_proof U_mpi_free U_mpi_init U_mpi_addsub U_mpi_lset U_mpi_grow U_mpi_core_bitlen U_mpi_bitlen U_ecp_group_init U_ecp_group_free U_ecp_defs U_ecp_statics U_ecp_group_load U_ecp_group_load_mx.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac glia := lazymatch goal with
  | |- @eq Z _ _ => lia | |- not (@eq Z _ _) => lia | |- Z.le _ _ => lia | |- Z.lt _ _ => lia | |- Z.ge _ _ => lia | |- Z.gt _ _ => lia
  | |- _ <= _ <= _ => lia | |- _ <= _ < _ => lia | |- _ < _ <= _ => lia | |- _ < _ < _ => lia | |- _ \/ _ => lia | |- _ /\ _ => lia | |- False => lia end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0c61aeb5f736e735 2 35 1 1 8 3 1 1 48 1 49 1 6 0 1 35 1 40 1 47 1 50 1 51 8 1 1 8 3 2 1 47 1 50 1 4 0 2 48 2 49 2 51 16P13254a1333a09613 2 35 1 1 8 3 1 1 48 1 49 1 6 0 1 35 1 40 1 47 1 50 1 51 8 1 1 8 3 2 1 47 1 50 1 4 0 2 48 2 49 2 51 16P193eef61640b1712 2 35 1 1 8 3 1 1 48 1 49 1 6 0 1 35 1 40 1 47 1 50 1 51 8 1 1 8 3 2 1 47 1 50 1 4 0 2 48 2 49 2 51 16P1c1a40011cf9da0f 2 35 1 1 8 3 1 1 48 1 49 1 6 0 1 35 1 40 1 47 1 50 1 51 8 1 1 8 3 2 1 47 1 50 1 4 0 2 48 2 49 2 51 16P31f14f6b1e91b9d5 2 35 1 1 8 3 1 1 48 1 49 1 6 0 1 35 1 40 1 47 1 50 1 51 8 1 1 8 3 2 1 47 1 50 1 4 0 2 48 2 49 2 51 16P360b94e46f60b089 2 35 1 1 8 3 1 1 48 1 49 1 6 0 1 35 1 40 1 47 1 50 1 51 8 1 1 8 3 2 1 47 1 50 1 4 0 2 48 2 49 2 51 16P37c4d0e48e8c171c 2 35 1 1 8 3 1 1 48 1 49 1 6 0 1 35 1 40 1 47 1 50 1 51 8 1 1 8 3 2 1 47 1 50 1 4 0 2 48 2 49 2 51 16P3e64d11f8a7ee658 2 35 1 1 8 3 1 1 48 1 49 1 6 0 1 35 1 40 1 47 1 50 1 51 8 1 1 8 3 2 1 47 1 50 1 4 0 2 48 2 49 2 51 16"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_ecp_group_load_mx2 () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_group_free.grp_free_LB"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.mpds_apart"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.U.U_platform_zeroize.U_MEMSET_FUNC"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_group_load.ecp_group_load_post"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_MT"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_CA"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_defs.U_ONE"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Section MX.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).
  (* [comment removed for export] *)
  Ltac spine_firstn k cs :=
    let k := eval cbv in k in
    lazymatch k with
    | Datatypes.O => eval lazy beta iota delta [firstn] in (firstn Datatypes.O cs)
    | Datatypes.S ?k' => lazymatch cs with
               | ?c :: ?cs' => let r := spine_firstn k' cs' in constr:(c :: r)
               | _ => eval cbv beta iota delta [firstn] in (firstn k cs)
               end
    end.
  Ltac spine_skipn k cs :=
    let k := eval cbv in k in
    lazymatch k with
    | Datatypes.O => cs
    | Datatypes.S ?k' => lazymatch cs with
               | _ :: ?cs' => spine_skipn k' cs'
               | _ => eval cbv beta iota delta [skipn] in (skipn k cs)
               end
    end.
  Ltac zofnat H := cbn [cells_size csize Nat.add length] in H;
    repeat match type of H with context [Z.of_nat (Datatypes.S ?k)] => let v := eval vm_compute in (Z.of_nat (Datatypes.S k)) in change (Z.of_nat (Datatypes.S k)) with v in H end;
    repeat match type of H with context [Z.add (Z.add ?a ?b) ?c] => is_Zlit b; is_Zlit c; let v := eval vm_compute in (Z.add b c) in replace (Z.add (Z.add a b) c) with (Z.add a v) in H by lia end.
  Ltac splitat H k H2 :=
    lazymatch type of H with rw_cells ?sg ?mm ?A0 ?cs =>
      let l1 := spine_firstn k cs in
      let l2 := spine_skipn k cs in
      change (rw_cells sg mm A0 (l1 ++ l2)) in H;
      let H1 := fresh "SP" in
      (flat constr:((proj1 (rw_cells_app sg mm A0 l1 l2) H)) 2%nat; intros H1 H2); clear H; rename H1 into H; zofnat H2
    end.


  (* [comment removed for export] *)
  Ltac cells_upto cs n :=
    lazymatch n with
    | 0%nat => constr:(0%nat)
    | _ => lazymatch cs with ?c :: ?cs' => let k := eval cbn in (n - csize c)%nat in let r := cells_upto cs' k in constr:(S r) end
    end.
  Ltac cutsz mx A0 n :=
    try (match goal with H : rw_cells _ mx ?A1 ?cs |- _ =>
      unify A1 A0;
      let tot := eval cbn in (cells_size cs) in
      lazymatch eval compute in (Nat.ltb n tot) with
      | true => let k := cells_upto cs n in let H2 := fresh "FX" in splitat H k H2
      | false => idtac end end).
  (* [comment removed for export] *)
  Ltac grp_recut mx A :=
    cutsz mx A 8%nat; cutsz mx (A + 8) 16%nat; cutsz mx (A + 24) 16%nat; cutsz mx (A + 40) 16%nat; cutsz mx (A + 56) 16%nat;
    cutsz mx (A + 72) 16%nat; cutsz mx (A + 88) 16%nat; cutsz mx (A + 104) 16%nat.


  Let mx_fail := mx_fail L HI HFREE HLS SW DIMG HND.
  Let mx_third := mx_third L HI HFREE HCALLOC HLS SW DIMG HND.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0390@L10307170927.173L10311321839.203L10311321964.161L10311464784.132L10313333060.218L10375287788.208L1040637867.219 L1040637868.177 L10675939592.166L10679955253.208L11551101741.173L11554870802.132L11799439267.208L11801536418.166L11805421443.208L11805647263.166L11805647263.208L11805648021.166L11805648021.208L11805648787.166L11805648787.208L11805649545.166L11805649674.166L11805649674.208L11805649803.166L11805649803.208L11805650053.166L11805650053.208L1237715698.173 L13179991696.162L13593976533.161L13593976662.203L13595913981.218L1386329633.202 L14607797347.115L14733777283.111L16075584073.203L16075584458.161L16093348261.218L19039446859.177L19039446860.219L19516240983.161L19516241364.203L19518227583.218L22217840259.209L22219853880.166L22219853880.208L22219855154.166L22219855154.208L22219855412.166L22219855412.208L22219856428.166L22219856428.208L22219856557.166L22219856557.208L22219856686.166L22219857186.166L22219857186.208L22219857702.166L22219857702.208L22220086820.166L22220086820.208L22220296506.132L22222394884.208L22224065541.173L22224492037.166L22575505139.218L22577442523.161L22577442648.203L22718433583.166L22718434849.208L22933989008.203L2480168487.173 L24931847738.203L24931848121.161L24934055825.218L25226297771.126L2550837553.173 L2563377714.161 L26640543246.132L28379260716.166L28379262393.208L28769331635.132L28769772971.208L29010565666.161L29428322499.218L29430522091.161L29430522216.203L3033030940.218 L3035287735.203 L3035287860.161 L31241273096.173L31253836192.166L32389730453.102L34063620708.107L34754565024.208L34754566453.166L35204911806.132L35204930595.153L35204930595.194L35209533313.173L35502191104.136L35502191104.137L35508388771.136L35866124555.132L37071212080.208L37071244090.166L37308923393.161L37308923778.203L37311106601.218L37708112016.208L37708341650.166L3814376778.173 L3818552905.161 L3818553290.203 L3818668149.132 L3820539489.218 L38675379992.132L3965196495.208 L3965426125.166 L40829474283.219L40829474284.177L40903670935.161L40903671060.203L40905919679.218L41071284954.161L41071285081.203L41073287922.218L42554579729.166L42558922028.208L43231491457.113L43231491457.129L43289959203.166L43290189353.208L44279828714.166L44279992808.208L45122522212.218L45124533324.161L45124533711.203L46020896534.114L46020896534.130L46795174945.166L46795175993.208L47197307954.161L47197308337.203L48221062715.218L48447946862.203L48447947245.161L48965534006.166L48965535288.208L49715713783.203L49715713908.161L50535093229.161L50547714286.173L52101693566.11 L52101695852.135L52101802921.139L52108543731.135L52108543731.136L52108543731.137L52624743377.132L52969527648.135L53029170644.114L53029170644.130L53681354684.115L54085936342.161L54349233536.112L54873198704.208L54873199478.166L55330452535.132L55330568239.208L56039687843.168L56039687843.210L59089799552.128L59246863747.127L59308585607.135L59308585607.176L59633215254.130L60185141813.218L62128664966.114L62128664966.130L64525774630.166L64540896272.208L64631255072.208L64631258168.166L64727658498.203L64729842089.218L6701995239.132 L6706614744.173 L67367210815.166L67368963081.208L6739893627.11  L6741498870.135 L6741498870.136 L6741498870.137 L68123783969.0  L7828284825.168 L7828284825.211 L838138809.166  L9311709836.173 R59308579027.13700000J00d01601H01k02C02`03403@03T04H05405H05T05h06406H06T07F08008D08P08\09009<09P09\0:00:f0;20;F0;b0<G0<H0<X0<d0=;0=J0=k0>W0?L0?X0?l0@I0@]0@i0A=0AI0A]0Ai0B=0BI0B]0Bi0C=0CI0CU0Ci0D50DI0DU0Di0E50EI0E]0Ei0FN0Fb0G>0GJ0G^0H20HF0H^0Hn0IO0I[0J30JC0JS0J_0K30K?0KS0KT0L80LK0Lf0MH0Ma0N20NF0NR0N^0Nj0O>0OJ0P20PZ0QJ0R:0Rl0S^0TH0To0UC0UO0Uh0VI0W30WG0WS0X00XE0Xb0Y70Y]0Yi0Z=0ZI0Zf0[:0[L0[f0\I0\`0]B0^10^=0^Q0^]0^i0_50_I0_U0_i0`Q0`h0aG0aS0a_0ak0b?0bO0bg0bh0cG0c^0cj0d>0dR0d^0e50eT0f10ff0gV0gi0h?0hR0hi0i=0iI0iU0il0jU0ja0jb0jc0jo0kC0kV0l10l=0lI0m<0n70nC0nd0o00o<0oH0o\10010<11712?12S12o13;13O13\13m14A14R14S14f15A15M15a15mS1L2ra2sp1A3DHI2TB2dA1r2PAS1L2ra2sp1A3DHI2TB2dA1r2PAS1L2ra2sp1A3DHI2TBS1L2ra2sp1A3DHI2TBS1L2ra2sp1A3DHI2TB2dA1r2PA2dX2r22PXS2ra2sp1A2TB2dA1r2PA3APAS2ra2sp1A2TB2dA1r2PA2dX2r22PXS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS1L3HLS2ra2sp1A2lo3POS2LO3ACL3SPA3ACP3SPB2TB2dA1r2PAS1L3HLS2ra2sp1A2lo3POS2LO3ACL3SPA3ACP3SPB2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS1L3HLS2ra2sp1A2lo2AL3POS2LO2SX3SPA3SPB2TB2dA1r2PAS1L3HLS2ra2sp1A2lo2AL3POS2LO2SX3SPA3SPB2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS1L2HI2ra2sp2h01h1A3HTQ3POS4HTOP3SPB2TB2h22dA1r3HT22PAS2ra2sp1A2TBS2ra2sp1A3SPA3SPB2TBS2ra2sp1A3SPA3SPB2TB2dA1r2PAS2ra2sp1A3SPA3SPB2TB2dA1r2PA2dX2r22PXFS2ra2sp1A3POS2TBS2ra2sp1A2TBS2ra2sp1A2TB2MB2dA1r2PAS2ra2sp1A2TB2MBS2ra2sp1A2TB2dA1r2PA2dX2r22PX3APXS1L3HLS2ra2sp1A2lo3POS2LO3ACL3SPB2TB2dA1r2PAS1L3HLS2ra2sp1A2lo3POS2LO3ACL3SPB2TB2dA1r2PA2dX2r22PXS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TB2dA1r2PA2dX2r22PXS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS1L2ra2sp1A2lo2LO2TB2dA1r2PA2dX2r22PXS1L2ra2sp1A2lo2LO2TBS1L2ra2sp1A2lo2LO2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TB2dA1r2PAS2ra2sp1A3POS2TB2dA1r2PAS2ra2sp1A3POS2TBS2ra2sp1A3POS2TB2dA1r2PA2dX2r22PXS2ra2sp1A2TBS2ra2sp1A3POS2TB2dA1r2PAS2ra2sp1A3POS2TBS2ra2sp1A3POS2TBS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAFS2ra2sp1A2lo3LO02TB2dA1r2PA2dX2r22PXS2ra2sp1A2lo3LO02TBS2ra2sp1A2lo3LO02TB2dA1r2PAS1L2ra2sp1A2ND2TB2dA1r2PA2dX2r22PXS1L2ra2sp1A2ND2TB2dA1r2PAS1L2ra2sp1A2ND2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS1L3HLS2ra2sp1A2lo3POS2LO3ACL3ACP3SPB2TBS1L3HLS2ra2sp1A2lo3POS2LO3ACL3ACP3SPB2TBS1L3HLS2ra2sp1A2lo3POS2LO3ACL3ACP3SPB2TB2dA1r2PAS1L3HLS2ra2sp1A2lo3POS2LO3ACL3ACP3SPB2TB2dA1r2PAS1L2HI3HLS2ra2sp2h01A2lo3POS2LO4HTOP3SPB2TB1a1l2l0S1L2HI3HLS2ra2sp2h01A2lo3POS2LO4HTOP3SPB2TB1a1l2l0S1L2HI3HLS2ra2sp2h01A2lo3POS2LO3SPB2TB1a1QS1L2HI2ra2sp2h01h1A3HTQ3POS4HTOP3SPB2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS1L2HI2ra2sp2h01A4HTOP2TBS1L2HI2ra2sp2h01A4HTOP2TB2dA1r2PAS1L2HI2ra2sp2h01A4HTOP2TB2dA1r2PA2dX2r22PXS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS1L2ra2sp1A2lo3ACL2TB2dA1r2PAS1L2ra2sp1A2lo3ACL2TBS1L2ra2sp1A2lo3ACL2TB2dA1r2PAS1L2ra2sp1A2lo3ACL2TBS1L2ra2sp1A2lo3ACL2TB2dA1r2PA2dX2r22PXS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PA2dX2r22PXS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2lo2SX2TBS2ra2sp1A2lo2SX2TB2dA1r2PAS2ra2sp1A2lo2SX2TB2dA1r2PA2dX2r22PXS2ra2sp1A3POS2RA3SPB2TBS2ra2sp1A3POS2RA3SPB2TB2dA1r2PA2ErS2ra2sp1A3POS2RA3SPB2TB2dA1r2PA2Er2dX2r22PX3Er2S2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2AL3POS3SPB2TB2dA1r2PA2dX2r22PXS2ra2sp1A2AL3POS3SPB2TBS2ra2sp1A2AL3POS3SPB2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A3POS2TBS2ra2sp1A3POS2TB2dA1r2PAFS2ra2sp1A2AL3POS3SPB2TB2dA1r2PAS2ra2sp1A2AL3POS3SPB2TBS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2AL3POS3SPB2TBS2ra2sp1A2AL3POS3SPB2TB2dA1r2PAS1L3HLS2sp2lo2LO3ACL3DHI1a2HaS2ra2sp1A2TB1a1C1L3HLS2lo3POS2LO2SX2ND3ACL3DHI3SPB2HoS1L3HLS2ra2sp1A2lo3POS2LO3ACL3SPB2TB1a1b2kk1C2B4S2ra2sp1A2TB1a2C11nS2ra2sp1A2TB1a2C21n2C1S2ra2sp1A2TB1a2C21nS2ra2sp1A2AL3POS3SPB2TBS2ra2sp1A2TB1a2C12C2S2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2AL3POS3SPB2TBS1L2HI2ra2sp2h01h1A3HTQ3POS3SPB2TB2h23HT2S2ra2sp1A2TBFFS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TB2xx3HxxS2ra2sp1A2TB2dA1r2PA2xx3HxxS2ra2sp1A2TBS2ra2sp1A2TBS1L3HLS2ra2sp1A2lo3POS2LO2ND3ACL3DHI3SPB2TB1a2Ha2HdS1L3HLS2ra2sp1A2lo3POS2LO2ND3ACL3DHI3SPB2TB2dA1r2PA1a2Ha2HdS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PA3APA2dX2r22PXS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS1L2HI2ra2sp2h01h1A3HTQ3POS3SPB2TB2h22dA1r3HT22PA2Er2h33HT3S1L2HI2ra2sp2h01h1A3HTQ3POS3SPB2TB2h22dA1r3HT22PA2Er2h32dX2r23HT32PX3Er2S1L2ra2sp1A2lo2LO2TBS1L2ra2sp1A2lo2LO2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS1L1A2ND1a2HaS2ra2sp1A2TB1a2C1S2ra2sp1A2TB1a2C22C1S2ra2sp1A2TB1a2C2SS2ra2sp1A2TB2xx3HxxS2ra2sp1A2TB2dA1r2PA2xx3HxxS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TB". (* [comment removed for export] *)
  Lemma case9 : ltac2:(CDefT.buildp (gd_tbl_P_ecp_group_load_mx2 ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pxa0,(0.&40.)Pxa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(2.(0.&8.))Pm,P,(0.&40.)(2.(0.&8.))Pmo0,$3.Pmo,$3.Ph0,(4.$5.VL,VHI,)Ph,(4.$5.VL,VHI,)PLB,(6.$7.)PA,$8.Pg,$9.Plo,$8.Pidpad,(0.&40.)PpP,(0.&40.)PpA,(0.&40.)PpB,(0.&40.)PpX,(0.&40.)PpY,(0.&40.)PpZ,(0.&40.)PpN,(0.&40.)Phpad,(0.&40.)Pxra,(0.&40.)Pfj,(6.(0.&8.))ZLBf,(6.$7.)(:.R=.R?.)P,(;.$5.VL,VHI,R11.R1.R15.R13.)P,(<.$8.(=.$5.VL,VHI,R12.)(=.$5.VL,VHI,R13.))P,(>.R16.R15.)P,(?.$5.VL,R4.(10.&40.R39.)(11.(12.$8.$8.)(13.$8.$8.R12.(14.R12.+<0.))(15.(12.$8.$8.)))R19.R18.)P,(16.$5.R19.R13.(11.$17.(18.(19.&40.+9.))(11.$17.(18.R10.)(15.$17.))))P,(<.$8.(1:.R14.+8.)=)P,(1;.=R15.)P,(16.$5.R1<.(14.R16.+8.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R1=.(14.R17.+18.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R1>.(14.R18.+28.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R1?.(14.R19.+38.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R20.(14.R1:.+48.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R21.(14.R1;.+58.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R22.(14.R1<.+68.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R23.(14.R1=.+78.)(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.=))(11.$17.(18.R12.)(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(15.$17.))))))))))))P,(16.$5.R24.(1=.(10.&40.R45.)+20.)(11.$17.(1>.#8.R11.)(11.$17.(1<.R3>.)(11.$17.(1<.R3?.)(11.$17.(1<.R46.)(15.$17.))))))P,(1?.$5.R25.R1=.(1=.(10.&40.R46.)+20.))P,(20.=R1>.)P,(20.R1?.(1=.(1=.(10.&40.R48.)+70.)(21.VL,)))P,(22.(20.(14.R22.+<0.)R20.)(20.(10.&40.R49.)R22.))P,(23.VL,R15.(10.&40.R4:.)(=.$5.VL,VHI,R26.)R23.+<0.)P,(22.(20.(14.R24.+<0.)(24.VL,))(20.(25.VL,)R24.))P,(20.(26.VL,)R23.)P,(20.(10.&40.R4=.)(=.$5.VL,VHI,R29.))P,(20.(25.VL,)(26.VL,))P,(27.$5.R2>.)P,(28.$5.VL,R2?.)P,(<.$8.(1:.(10.&40.R52.)+2.)=)P,(29.(2:.R2:.))P,(<.(0.&40.)R51.(19.&40.(2;.VL,)))P,(2<.VL,$2=.+8.)P,(<.$8.(1:.(10.&40.R55.)+10.)=)(2>.$5.R33.(2?.$5.VL,VHI,$30.$31.$32.R57.R56.R55.R54.R50.R4?.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R38.R37.R32.R30.R2?.R2>.+9.R2=.R36.R34.)(33.(34.R23.(19.&40.(1=.(10.&40.R56.)+20.))R55.R54.R53.R52.R51.(19.&40.R2?.)(19.&40.+9.)R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.)R38.(19.&40.+3<3<<.)R37.(35.(0.&40.))R35.(36.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros until fj. cbv zeta. intros HH HTQ MF PXA HD AL POS HP HA HB HX HY HZ HN HT FR ST LO0 LO SX CW ND ACL HTOP DHI MI SOK RA DIS TP CA SPA.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP. flat constr:(DIMG) 2%nat. intros DI1 DI2.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (rw_cells_bound _ _ _ _ HT) as TB. cbn [cells_size csize Nat.add length] in TB.
    pose proof (U_curve_statics m 9 MI ltac:(lia)) as CS. flat constr:(CS) 5%nat. intros STP _ _ STN _. pose proof (lock MI) as MI00.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBRf _.
    assert (MPB : 0 <= ca_modp (U_CA 9) < 2^64 /\ In (ca_modp (U_CA 9), (ca_P (U_CA 9), cP 9)) U_MT) by (cbn -[c9_P c13_P]; split; [lia| auto 20]).
    flat constr:(MPB) 2%nat. flclear MPB. intros MB MODP.
    pose proof (munch_refl [(A, A + 192); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (conj HH I) as HH0. clear HH.
    pose proof SOK as SOKm.
    clear HCALLOC HFREE || idtac.
    (* [comment removed for export] *)
    try clear LXSUMS. assert (LXSUMS : forall AL', Forall (summary_okG usegs AL' []) (@nil summary)) by (intros AL'; constructor).
    rewrite ?TP. apply (lxp_aevtM_of_evt usegs mo _ _ MK).
    lx_run_tac (PLANS [0x1fb64] [] 60%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- ?TP.
    clear HD HP HA HB HX HY HZ HN HT FR ST. try clear MU. try clear WM.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with Hm : munch _ m mx, Hw : wmono _ m mx, Hg : rw_cells _ mx A _, Hf : rw_cells _ mx _ [CB 8 fj; _; _; _], Hs : stk _ mx _ _, Hi : mem_inv _ mx |- _ =>
        rename Hm into MU; rename Hw into WM; rename Hf into FR; rename Hs into ST; rename Hg into HD;
        pose proof (statics_ok_munch usegs L _ _ _ SOKm MU ltac:(intros a Ha NW; cbn; repeat split; try exact I; clear -Ha ND DHI ACL LO HLS; lia)) as SOK'; clear SOK; try clear MI; rename SOK' into SOK; rename Hi into MI
      end end.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => grp_recut mx A;
      lazymatch goal with H0 : rw_cells _ mx A _, H1 : rw_cells _ mx (A + 8) _, H2 : rw_cells _ mx (A + 24) _, H3 : rw_cells _ mx (A + 40) _, H4 : rw_cells _ mx (A + 56) _,
                          H5 : rw_cells _ mx (A + 72) _, H6 : rw_cells _ mx (A + 88) _, H7 : rw_cells _ mx (A + 104) _, H8 : rw_cells _ mx (A + 120) _ |- _ =>
        rename H0 into HD; rename H1 into HP; rename H2 into HA; rename H3 into HB; rename H4 into HX; rename H5 into HY; rename H6 into HZ; rename H7 into HN; rename H8 into HT end end.
    replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) in FR, ST by lia. try replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia.
    lazymatch type of MU with munch _ m ?mx => change (munch [(A, A + 192); (bv_unsigned sp - 32, bv_unsigned sp)] m mx) in MU end.
    apply mpi_cells_of_sn in HP; [| lia]. change (524289 mod 2 ^ 16) with 1 in HP. change (524289 / 2 ^ 16) with 8 in HP.
    (* [comment removed for export] *)
    pose proof U_mpi_bitlen_spec as SPB_. unfold mpi_bitlen_stmt in SPB_.
    eapply aevtM_cut_evt; [exact MK| eapply SPB_ with (dX := smpd (A + 8) (ca_P (U_CA 9)) (cP 9) pP) (LB := grp_free_LB g LB);
      [ eapply smpd_mpd_at; [exact HP| lia| lia| eapply static_limbs_any_mem; [exact STP| exact (unlock _ MI00)| assumption]]
      | cbn; discriminate | assumption | reflexivity ] |].
    clear SPB_. unfold mpi_query_post. match goal with H : mem_inv usegs ?mc |- _ => post_call usegs mc end.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    unfold mpi_cells in HP.
    clear HCALLOC HFREE || idtac.
    (* [comment removed for export] *)
    try clear LXSUMS. assert (LXSUMS : forall AL', Forall (summary_okG usegs AL' []) (@nil summary)) by (intros AL'; constructor).
    rewrite ?TP. apply (lxp_aevtM_of_evt usegs mo _ _ MK).
    lx_run_tac (PLANS [0x1f808] [] 60%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- ?TP.
    clear HD HP HA HB HX HY HZ HN HT FR ST. try clear MU. try clear WM.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with Hm : munch _ m mx, Hw : wmono _ m mx, Hg : rw_cells _ mx A _, Hf : rw_cells _ mx _ [CB 8 fj; _; _; _], Hs : stk _ mx _ _, Hi : mem_inv _ mx |- _ =>
        rename Hm into MU; rename Hw into WM; rename Hf into FR; rename Hs into ST; rename Hg into HD;
        pose proof (statics_ok_munch usegs L _ _ _ SOKm MU ltac:(intros a Ha NW; cbn; repeat split; try exact I; clear -Ha ND DHI ACL LO HLS; lia)) as SOK'; clear SOK; try clear MI; rename SOK' into SOK; rename Hi into MI
      end end.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => grp_recut mx A;
      lazymatch goal with H0 : rw_cells _ mx A _, H1 : rw_cells _ mx (A + 8) _, H2 : rw_cells _ mx (A + 24) _, H3 : rw_cells _ mx (A + 40) _, H4 : rw_cells _ mx (A + 56) _,
                          H5 : rw_cells _ mx (A + 72) _, H6 : rw_cells _ mx (A + 88) _, H7 : rw_cells _ mx (A + 104) _, H8 : rw_cells _ mx (A + 120) _ |- _ =>
        rename H0 into HD; rename H1 into HP; rename H2 into HA; rename H3 into HB; rename H4 into HX; rename H5 into HY; rename H6 into HZ; rename H7 into HN; rename H8 into HT end end.
    replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) in FR, ST by lia. try replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia.
    lazymatch type of MU with munch _ m ?mx => change (munch [(A, A + 192); (bv_unsigned sp - 32, bv_unsigned sp)] m mx) in MU end.
    lazymatch type of HP with rw_cells _ ?mq _ [C8 (Z_to_bv 64 ?p); C2 (Z_to_bv 64 ?sg); C2 (Z_to_bv 64 ?nn); C4 ?pd] => change (rw_cells usegs mq (A + 8) (mpi_cells p (Z_to_bv 64 sg) nn pd)) in HP end.
    apply mpi_cells_of_sn in HN; [| lia]. change (524289 mod 2 ^ 16) with 1 in HN. change (524289 / 2 ^ 16) with 8 in HN.
    apply mpi_cells_of_sn in HA; [| lia]. apply mpi_cells_of_sn in HB; [| lia]. apply mpi_cells_of_sn in HX; [| lia]. apply mpi_cells_of_sn in HY; [| lia]. apply mpi_cells_of_sn in HZ; [| lia].
    change (1 mod 2 ^ 16) with 1 in HA, HB, HX, HY, HZ. change (1 / 2 ^ 16) with 0 in HA, HB, HX, HY, HZ.
    (* [comment removed for export] *)
    flat constr:(HH0) 2%nat. flclear HH0. intros HHo _.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HH : HEAP usegs L HI h (grp_free_LB g LB) m1 mo).
    { apply (@HEAP_munch usegs L HI h _ m m1 mo _ lo HHo MU WM ACL).
      intros a Ha NO. cbn in NO. rewrite HTQ.
      destruct (Z_le_dec A a) as [C1|C1]; [destruct (Z_lt_dec a (A + 192)) as [C2|C2]|].
      - destruct (CW a ltac:(lia)) as [Q|[Q|Q]]; [left; lia| right; left; exact Q| right; right; exact Q].
      - left. destruct (Z_le_dec (bv_unsigned sp - 32) a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; repeat split; try exact I; lia..].
      - left. destruct (Z_le_dec (bv_unsigned sp - 32) a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; repeat split; try exact I; lia..]. }
    assert (PX1 : heap_presx usegs L (grp_free_LB g LB) (bv_unsigned sp) [(A, A + 192)] m0 m1).
    { eapply heap_presx_trans; [exact PXA|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. cbn in Ho |- *. flat constr:(Ho) 2%nat. flclear Ho. intros Ho _. split; [exact Ho|]. split; [| exact I].
      destruct Hc as [C|[C|([b kk] & Hb & C)]]; [lia| lia|]. cbn in C. flat constr:((proj1 (Forall_forall _ _) HBRf _ Hb)) 5%nat. intros _ _ _ B4 _. cbn in B4. lia. }
    clear HHo PXA MU WM MK. pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    assert (SUBr : forall b : blk, In b (grp_free_LB g LB) -> In b (grp_free_LB g LB)) by (intros b Hb; exact Hb).
    (* [comment removed for export] *)
    pose proof (U_mpi_lset_spec L HI HCALLOC HLS SW DIMG HND) as SL. unfold mpi_lset_stmt, U_MPI_LSET in SL.
    eapply aevtM_cut.
    { eapply SL with (lo := lo) (h := h) (LB := grp_free_LB g LB) (dX := mpd_init (A + 24) pA) (z := 121666); rewrite ?(unsigned_lit (bv_unsigned sp - 32)) by lia;
        first [ exact HH | exact TP | exact SOK | exact CA | reflexivity
              | apply mpd_of_mpdr; [apply mpdr_at_init; [exact HA| lia| lia]| left; reflexivity]
              | cbn; discriminate
              | split; [rewrite HTQ; eapply (client_wrange_weak L); [exact CW| exact SUBr| lia| cbn; lia| cbn; lia]| split; [intros a Ha Hd; exfalso; cbn in Ha; lia| cbn; discriminate]]
              | match goal with |- stk _ _ _ _ => eassumption end
              | match goal with |- mem_inv _ _ => assumption end
              | lia
              | first [reflexivity| apply bv_eq; vm_compute; reflexivity]
              | match goal with |- ?gg => idtac "LSET1LEFT" gg end ]. }
    cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    flat constr:(PO) 22%nat. flclear PO. intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 m2 mo2 h2 LB1 dA r E PO. injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp - 32)) in PO by lia.
    flat constr:(PO) 10%nat. flclear PO. intros MI2 ST2 MF2 HT2 HH2 MA2 OUT PXl SOK2 LR.
    replace (ret_pc (Z_to_bv 64 0x3c42c)) with (Z_to_bv 64 0x3c42c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    cbn [mpd_ivs md_addr md_own mpd_init] in PXl.
    flat constr:(OUT) 5%nat. flclear OUT. intros EAa OA OUT1 OUT2 OUT3. cbn [md_addr mpd_init mpd_blk md_own] in EAa, OUT1, OUT2, OUT3.
    assert (SUB1 : forall b, In b (grp_free_LB g LB) -> In b LB1) by (intros b Hb; apply OUT2; [exact Hb| intros []]).
    clear HA. presx_all usegs L PXl CW SUBr.
    assert (PX2 : heap_presx usegs L (grp_free_LB g LB) (bv_unsigned sp) [(A, A + 192)] m0 m2).
    { eapply heap_presx_trans; [exact PX1|]. eapply (heap_presx_weak usegs L); [exact PXl| exact SUBr| lia|]. intros xx Hxx. cbn in Hxx |- *. split; [lia| exact I]. }
    match goal with STo : stk usegs m1 _ _, MIo : mem_inv usegs m1 |- _ => clear STo MIo end. clear PX1 SOK MK HH MU WM.
    pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK. pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      destruct LR as ([(Er & _) | [Er EdA]] & _ & FRA); [exfalso; subst r; apply K0; reflexivity|]. subst r. subst dA.
      eapply (mx_fail) with (dA := mpd_init (A + 24) pA) (dX := mpd_init (A + 56) pX) (dZ := mpd_init (A + 88) pZ)
                            (idpad := idpad) (pP := pP) (pB := pB) (pY := pY) (pN := pN) (hpad := hpad);
        first [ glia| reflexivity| exact HH2| rewrite HT2; exact HTQ| exact (mo_frame_trans _ _ _ MF MF2)| exact PX2| exact FR| exact ST2| exact CW| exact ND| exact MI2| exact SOK2| exact TP| exact CA
              | eapply grp_mxi_at; first [glia| exact MODP| exact MB| exact HD| exact HP| exact HB| exact HY| exact HN| exact HT| exact (mpdr_of_mpd _ _ _ _ MA2)
                                         | exact (mpdr_at_init _ _ _ _ _ HX ltac:(lia) ltac:(lia))| exact (mpdr_at_init _ _ _ _ _ HZ ltac:(lia) ltac:(lia))
                                         | apply mx_field_init
                                         | eapply curve_statics_any_mem; [exact CS| exact (unlock _ MI00)| exact MI2]
                                         | match goal with |- ?gg => idtac "GMXI1" gg end ]
              | apply grp_mxi_apart; [apply mx_field_init| apply mx_field_init| apply mx_field_init| cbn; intros; discriminate..]
              | intros b; split; [intros Hb; destruct (OUT1 b Hb) as [Hc|Hz]; [right; exact Hc| cbn in Hz; destruct Hz]| intros [Hb|Hb]; [cbn in Hb; destruct Hb| apply SUB1; exact Hb]]
              | intros b Hb; cbn in Hb; destruct Hb
              | match goal with |- ?gg => idtac "TOFAIL1" gg end]. }
    (* [comment removed for export] *)
    destruct LR as ([(Er & An & Ao & Al & As & Apd) | [Er EdA]] & _ & FRA); [| exfalso; subst r; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K0; cbv in K0; discriminate].
    cbn [md_n mpd_init md_addr] in An, EAa. change (if 121666 <? 0 then -1 else 1) with 1 in As.
    flat constr:((lset_heap1 dA (A + 24) An Ao Al As EAa)) 2%nat. intros wA EdA.
    rewrite EdA in MA2. set (PA := md_p dA) in *. set (pdA := md_pad dA) in *.
    assert (INA : In (PA, 4) LB1) by (pose proof MA2 as [[_ (_ & _ & _ & _ & (_ & IN & _))] _]; exact IN).
    assert (FPA : ~ In (PA, 4) (grp_free_LB g LB)).
    { intros C. destruct (FRA (PA, 4)) as [[]|NI]; [| exact (NI C)]. rewrite EdA. cbn. left. reflexivity. }
    assert (APA : A + 192 <= PA \/ PA + 4 <= A).
    { flat constr:((heap_blocks _ _ HI _ _ _ _ HH2)) 2%nat. intros HBR2 HAP2.
      eapply (client_apart_block L (grp_free_LB g LB) LB1); [exact CW| exact SUB1| exact HBR2| exact HAP2| exact INA| exact FPA| lia| lia| exact DHI| lia| exact DI1| exact DI2]. }
    assert (IFF1 : forall b, In b LB1 <-> In b [(PA, 4)] \/ In b (grp_free_LB g LB)).
    { intros b. split.
      - intros Hb. destruct (OUT1 b Hb) as [Hc|Hz]; [right; exact Hc| left]. rewrite EdA in Hz. cbn in Hz |- *. exact Hz.
      - intros [[<-|[]]|Hb]; [exact INA| apply SUB1; exact Hb]. }
    clear OUT1 OUT2 OUT3 FRA.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    eapply aevtM_cut.
    { eapply SL with (lo := lo) (h := h2) (LB := LB1) (dX := mpd_init (A + 56) pX) (z := 9); rewrite ?(unsigned_lit (bv_unsigned sp - 32)) by lia;
        first [ exact HH2 | exact TP | exact SOK2 | exact CA | reflexivity
              | apply mpd_of_mpdr; [apply mpdr_at_init; [exact HX| lia| lia]| left; reflexivity]
              | cbn; discriminate
              | split; [rewrite HT2, HTQ; eapply (client_wrange_weak L); [exact CW| exact SUB1| lia| cbn; lia| cbn; lia]| split; [intros a Ha Hd; exfalso; cbn in Ha; lia| cbn; discriminate]]
              | match goal with |- stk _ _ _ _ => eassumption end
              | match goal with |- mem_inv _ _ => assumption end
              | lia
              | match goal with |- ?gg => idtac "LSET2LEFT" gg end ]. }
    cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    flat constr:(PO) 22%nat. flclear PO. intros z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 m3 mo3 h3 LB2 dX r2 E PO. injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp - 32)) in PO by lia.
    flat constr:(PO) 10%nat. flclear PO. intros MI3 ST3 MF3 HT3 HH3 MX3 OUT PXl2 SOK3 LR.
    replace (ret_pc (Z_to_bv 64 0x3c43c)) with (Z_to_bv 64 0x3c43c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    cbn [mpd_ivs md_addr md_own mpd_init] in PXl2.
    flat constr:(OUT) 5%nat. flclear OUT. intros EXa OX OUT1 OUT2 OUT3. cbn [md_addr mpd_init mpd_blk md_own] in EXa, OUT1, OUT2, OUT3.
    assert (SUB2 : forall b, In b LB1 -> In b LB2) by (intros b Hb; apply OUT2; [exact Hb| intros []]).
    assert (SUBf2 : forall b, In b (grp_free_LB g LB) -> In b LB2) by (intros b Hb; apply SUB2, SUB1, Hb).
    clear HX. presx_all usegs L PXl2 CW SUB1.
    assert (MA3 : mpd_at usegs m3 LB2 (heap1 (A + 24) PA wA pdA)).
    { apply mpd_of_mpdr; [| left; reflexivity]. eapply mpdr_at_LB_mono; [| exact SUB2].
      eapply (mpdr_at_presx usegs L m2 m3); [exact (mpdr_of_mpd _ _ _ _ MA2)| exact PXl2| exact MI2| exact MI3| | cbn; lia|].
      - cbn. eapply (client_range_of_wrange L); [exact CW| exact SUB1| lia| lia| lia].
      - cbn. intros _. split; [exact INA| lia]. }
    assert (PX3 : heap_presx usegs L (grp_free_LB g LB) (bv_unsigned sp) [(A, A + 192)] m0 m3).
    { eapply heap_presx_trans; [exact PX2|]. eapply (heap_presx_weak usegs L); [exact PXl2| exact SUB1| lia|]. intros xx Hxx. cbn in Hxx |- *. split; [lia| exact I]. }
    clear MA2 PX2 ST2 MI2 SOK2 MK HH2 MU WM.
    pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK. pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      destruct LR as ([(Er2 & _) | [Er2 EdX]] & _ & FRX); [exfalso; subst r2; apply K1; reflexivity|]. subst r2. subst dX.
      eapply (mx_fail) with (dA := heap1 (A + 24) PA wA pdA) (dX := mpd_init (A + 56) pX) (dZ := mpd_init (A + 88) pZ)
                            (idpad := idpad) (pP := pP) (pB := pB) (pY := pY) (pN := pN) (hpad := hpad);
        first [ glia| reflexivity| exact HH3| rewrite HT3, HT2; exact HTQ| exact (mo_frame_trans _ _ _ MF (mo_frame_trans _ _ _ MF2 MF3))| exact PX3| exact FR| exact ST3| exact CW| exact ND| exact MI3| exact SOK3| exact TP| exact CA
              | eapply grp_mxi_at; first [glia| exact MODP| exact MB| exact HD| exact HP| exact HB| exact HY| exact HN| exact HT| exact (mpdr_of_mpd _ _ _ _ MA3)| exact (mpdr_of_mpd _ _ _ _ MX3)
                                         | exact (mpdr_at_init _ _ _ _ _ HZ ltac:(lia) ltac:(lia))
                                         | apply mx_field_init| apply mx_field_heap1
                                         | eapply curve_statics_any_mem; [exact CS| exact (unlock _ MI00)| exact MI3]
                                         | match goal with |- ?gg => idtac "GMXI2" gg end ]
              | apply grp_mxi_apart; [apply mx_field_heap1| apply mx_field_init| apply mx_field_init| cbn; intros; discriminate..]
              | intros b; split; [intros Hb; destruct (OUT1 b Hb) as [Hc|Hz]; [exact (proj1 (IFF1 b) Hc)| cbn in Hz; destruct Hz]| intros Hb; apply SUB2; exact (proj2 (IFF1 b) Hb)]
              | intros b [<-|[]]; exact FPA
              | match goal with |- ?gg => idtac "TOFAIL2" gg end]. }
    (* [comment removed for export] *)
    destruct LR as ([(Er2 & Xn & Xo & Xl & Xs & Xpd) | [Er2 EdX]] & _ & FRX); [| exfalso; subst r2; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K1; cbv in K1; discriminate].
    cbn [md_n mpd_init md_addr] in Xn, EXa. change (if 9 <? 0 then -1 else 1) with 1 in Xs.
    flat constr:((lset_heap1 dX (A + 56) Xn Xo Xl Xs EXa)) 2%nat. intros wX EdX.
    rewrite EdX in MX3. set (PX := md_p dX) in *. set (pdX := md_pad dX) in *.
    assert (INX : In (PX, 4) LB2) by (pose proof MX3 as [[_ (_ & _ & _ & _ & (_ & IN & _))] _]; exact IN).
    assert (FPX1 : ~ In (PX, 4) LB1).
    { intros C. destruct (FRX (PX, 4)) as [[]|NI]; [| exact (NI C)]. rewrite EdX. cbn. left. reflexivity. }
    assert (APX : A + 192 <= PX \/ PX + 4 <= A).
    { flat constr:((heap_blocks _ _ HI _ _ _ _ HH3)) 2%nat. intros HBR3 HAP3.
      eapply (client_apart_block L (grp_free_LB g LB) LB2); [exact CW| exact SUBf2| exact HBR3| exact HAP3| exact INX| intros C; apply FPX1, SUB1, C| lia| lia| exact DHI| lia| exact DI1| exact DI2]. }
    
    eapply (mx_third) with (PA := PA) (PX := PX);
      first [ glia| exact HH3| rewrite HT3, HT2; exact HTQ| exact (mo_frame_trans _ _ _ MF (mo_frame_trans _ _ _ MF2 MF3))| exact PX3
            | exact HD| exact HP| exact MA3| exact HB| exact MX3| exact HY| exact HZ| exact HN| exact HT| exact FR| exact ST3| exact CW| exact ND| exact MI3| exact SOK3| exact TP| exact CA| exact APA| exact APX
            | intros C; apply FPX1, SUB1, C
            | intros E; apply FPX1; rewrite <- E; exact INA
            | intros b; split; [intros Hb; destruct (OUT1 b Hb) as [Hc|Hz]; [destruct (proj1 (IFF1 b) Hc) as [H1|H1]; [left; cbn in H1 |- *; clear -H1; tauto| right; exact H1]| rewrite EdX in Hz; cbn in Hz; left; cbn; clear -Hz; tauto]
                               | intros [[<-|[<-|[]]]|Hb]; [apply SUB2; exact INA| exact INX| apply SUBf2; exact Hb]]
            | exact FPA
            | lia
            | match goal with |- ?gg => idtac "TOTHIRD" gg end].
  all: fail.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0390@L10307170927.173L10311321839.203L10311321964.161L10311464784.132L10313333060.218L10375287788.208L1040637867.219 L1040637868.177 L10675939592.166L10679955253.208L11551101741.173L11554870802.132L11799439267.208L11801536418.166L11805421443.208L11805647263.166L11805647263.208L11805648021.166L11805648021.208L11805648787.166L11805648787.208L11805649545.166L11805649674.166L11805649674.208L11805649803.166L11805649803.208L11805650053.166L11805650053.208L1237715698.173 L13593976533.161L13593976662.203L13595913981.218L1386329633.202 L14607797347.115L14733777283.111L16075584073.203L16075584458.161L16093348261.218L19039446859.177L19039446860.219L22217840259.209L22219853880.166L22219853880.208L22219855154.166L22219855154.208L22219855412.166L22219855412.208L22219856428.166L22219856428.208L22219856557.166L22219856557.208L22219856686.166L22219857186.166L22219857186.208L22219857702.166L22219857702.208L22220086820.166L22220086820.208L22220296506.132L22222394884.208L22224065541.173L22224492037.166L22550459135.218L22552642263.161L22552642388.203L22575505139.218L22577442523.161L22577442648.203L22718433583.166L22718434849.208L24931847738.203L24931848121.161L24934055825.218L25226297771.126L2550837553.173 L2563377714.161 L26518757927.173L26640543246.132L28379260716.166L28379262393.208L28769331635.132L28769772971.208L29010565666.161L29428322499.218L29430522091.161L29430522216.203L3033030940.218 L3035287735.203 L3035287860.161 L31241273096.173L31253836192.166L34754565024.208L34754566453.166L35204911806.132L35204930595.153L35204930595.194L35209533313.173L35502191104.136L35502191104.137L35508388771.136L35866124555.132L37071212080.208L37071244090.166L37308923393.161L37308923778.203L37311106601.218L37708112016.208L37708341650.166L37764338192.203L3814376778.173 L3818552905.161 L3818553290.203 L3818668149.132 L3820539489.218 L3965196495.208 L3965426125.166 L39723389345.0  L40829474283.219L40829474284.177L40903670935.161L40903671060.203L40905919679.218L41071284954.161L41071285081.203L41073287922.218L42554579729.166L42558922028.208L43231491457.113L43231491457.129L43289959203.166L43290189353.208L44279828714.166L44279992808.208L45122522212.218L45124533324.161L45124533711.203L46020896534.114L46020896534.130L46795174945.166L46795175993.208L47197307954.161L47197308337.203L48221062715.218L48447946862.203L48447947245.161L48965534006.166L48965535288.208L49715713783.203L49715713908.161L50535093229.161L50547714286.173L51517596260.107L52101693566.11 L52101695852.135L52101802921.139L52108543731.135L52108543731.136L52108543731.137L52624743377.132L52969527648.135L53029170644.114L53029170644.130L53681354684.115L54085936342.161L54349233536.112L54873198704.208L54873199478.166L55330452535.132L55330568239.208L56039687843.168L56039687843.210L58151914261.102L59089799552.128L59246863747.127L59308585607.135L59308585607.176L59633215254.130L60185141813.218L62128664966.114L62128664966.130L64525774630.166L64540896272.208L64631255072.208L64631258168.166L64727658498.203L64729842089.218L65199301136.162L65764933400.132L6701995239.132 L6706614744.173 L67367210815.166L67368963081.208L6739893627.11  L6741498870.135 L6741498870.136 L6741498870.137 L7828284825.168 L7828284825.211 L838138809.166  L9311709836.173 R59308579027.13700000J00d01601H01k02C02`03403@03T04H05405H05T05h06406H06T07F08008D08P08\09009<09P09\0:00:f0;:0;V0<;0<<0<L0<X0<o0=>0=_0>K0?@0?T0?`0@40@@0@T0@`0A40A@0AT0A`0B40B@0BL0B`0Bl0C@0CL0C`0Cl0D@0DT0D`0E=0EI0E]0FB0FV0G20G>0GR0Gj0H:0H[0Hg0I?0IO0Ic0J30J?0JS0J_0K30K40KX0Kk0LF0Lh0MA0MR0Mf0N20NF0NR0O:0Ob0PR0QB0R40Rf0SP0T70TK0TW0U00UQ0V;0VO0V[0Vo0WL0Wa0X>0XS0Y90YM0YY0YZ0Z70ZK0Z]0[70[Z0\10\S0]B0]N0]b0]n0^:0^F0^Z0^f0_:0_b0`90`X0`d0a00a<0aP0a`0b80b90bX0bo0c;0cO0cc0co0dF0de0e10eN0fC0g30gF0g\0go0hF0hZ0hf0i20iI0j20j>0j?0j@0jL0j`0k30kN0kZ0kf0l20le0m`0ml0nM0nY0ne0o10oE0oY0oe10`11h12412@12T13013<13P13]13n14B14S14f15A15M15a15mS1L2ra2sp1A3DHI2TB2dA1r2PAS1L2ra2sp1A3DHI2TB2dA1r2PAS1L2ra2sp1A3DHI2TBS1L2ra2sp1A3DHI2TBS1L2ra2sp1A3DHI2TB2dA1r2PA2dX2r22PXS2ra2sp1A2TB2dA1r2PA3APAS2ra2sp1A2TB2dA1r2PA2dX2r22PXS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS1L3HLS2ra2sp1A2lo3POS2LO3ACL3SPA3ACP3SPB2TB2dA1r2PAS1L3HLS2ra2sp1A2lo3POS2LO3ACL3SPA3ACP3SPB2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS1L3HLS2ra2sp1A2lo2AL3POS2LO2SX3SPA3SPB2TB2dA1r2PAS1L3HLS2ra2sp1A2lo2AL3POS2LO2SX3SPA3SPB2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS1L2HI2ra2sp2h01h1A3HTQ3POS4HTOP3SPB2TB2h22dA1r3HT22PAS2ra2sp1A3SPA3SPB2TBS2ra2sp1A3SPA3SPB2TB2dA1r2PAS2ra2sp1A3SPA3SPB2TB2dA1r2PA2dX2r22PXFS2ra2sp1A3POS2TBS2ra2sp1A2TBS2ra2sp1A2TB2MB2dA1r2PAS2ra2sp1A2TB2MBS2ra2sp1A2TB2dA1r2PA2dX2r22PX3APXS1L3HLS2ra2sp1A2lo3POS2LO3ACL3SPB2TB2dA1r2PAS1L3HLS2ra2sp1A2lo3POS2LO3ACL3SPB2TB2dA1r2PA2dX2r22PXS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PA2dX2r22PXS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS1L2ra2sp1A2lo2LO2TB2dA1r2PA2dX2r22PXS1L2ra2sp1A2lo2LO2TBS1L2ra2sp1A2lo2LO2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A3POS2TB2dA1r2PAS2ra2sp1A3POS2TBS2ra2sp1A3POS2TB2dA1r2PA2dX2r22PXS2ra2sp1A2TBS2ra2sp1A3POS2TB2dA1r2PAS2ra2sp1A3POS2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A3POS2TBS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAFS2ra2sp1A2lo3LO02TB2dA1r2PA2dX2r22PXS2ra2sp1A2lo3LO02TBS2ra2sp1A2lo3LO02TB2dA1r2PAS1L2ra2sp1A2ND2TB2dA1r2PA2dX2r22PXS1L2ra2sp1A2ND2TB2dA1r2PAS1L2ra2sp1A2ND2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS1L3HLS2ra2sp1A2lo3POS2LO3ACL3ACP3SPB2TBS1L3HLS2ra2sp1A2lo3POS2LO3ACL3ACP3SPB2TBS1L3HLS2ra2sp1A2lo3POS2LO3ACL3ACP3SPB2TB2dA1r2PAS1L3HLS2ra2sp1A2lo3POS2LO3ACL3ACP3SPB2TB2dA1r2PAS1L2HI3HLS2ra2sp2h01A2lo3POS2LO4HTOP3SPB2TB1a1l2l0S1L2HI3HLS2ra2sp2h01A2lo3POS2LO4HTOP3SPB2TB1a1l2l0S1L2HI3HLS2ra2sp2h01A2lo3POS2LO3SPB2TB1a1QS1L2HI2ra2sp2h01h1A3HTQ3POS4HTOP3SPB2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS1L2HI2ra2sp2h01A4HTOP2TBS1L2HI2ra2sp2h01A4HTOP2TB2dA1r2PAS1L2HI2ra2sp2h01A4HTOP2TB2dA1r2PA2dX2r22PXS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS1L2ra2sp1A2lo3ACL2TB2dA1r2PAS1L2ra2sp1A2lo3ACL2TBS1L2ra2sp1A2lo3ACL2TB2dA1r2PAS1L2ra2sp1A2lo3ACL2TBS1L2ra2sp1A2lo3ACL2TB2dA1r2PA2dX2r22PXS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBSS2ra2sp1A2TB2dA1r2PA2dX2r22PXS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2lo2SX2TBS2ra2sp1A2lo2SX2TB2dA1r2PAS2ra2sp1A2lo2SX2TB2dA1r2PA2dX2r22PXS2ra2sp1A3POS2RA3SPB2TBS2ra2sp1A3POS2RA3SPB2TB2dA1r2PA2ErS2ra2sp1A3POS2RA3SPB2TB2dA1r2PA2Er2dX2r22PX3Er2S2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2AL3POS3SPB2TB2dA1r2PA2dX2r22PXS2ra2sp1A2AL3POS3SPB2TBS2ra2sp1A2AL3POS3SPB2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A3POS2TBS2ra2sp1A3POS2TB2dA1r2PAFS2ra2sp1A2AL3POS3SPB2TB2dA1r2PAS2ra2sp1A2AL3POS3SPB2TBS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2AL3POS3SPB2TBS2ra2sp1A2AL3POS3SPB2TB2dA1r2PAS2ra2sp1A2TBS1L3HLS2sp2lo2LO3ACL3DHI1a2HaS2ra2sp1A2TB1a1C1L3HLS2lo3POS2LO2SX2ND3ACL3DHI3SPB2HoS1L3HLS2ra2sp1A2lo3POS2LO3ACL3SPB2TB1a1b2kk1C2B4S2ra2sp1A2TB1a2C11nS2ra2sp1A2TB1a2C21n2C1S2ra2sp1A2TB1a2C21nS2ra2sp1A2AL3POS3SPB2TBS2ra2sp1A2TB1a2C12C2S2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2AL3POS3SPB2TBS1L2HI2ra2sp2h01h1A3HTQ3POS3SPB2TB2h23HT2S2ra2sp1A2TBFFS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TB2xx3HxxS2ra2sp1A2TB2dA1r2PA2xx3HxxS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS1L3HLS2ra2sp1A2lo3POS2LO2ND3ACL3DHI3SPB2TB1a2Ha2HdS1L3HLS2ra2sp1A2lo3POS2LO2ND3ACL3DHI3SPB2TB2dA1r2PA1a2Ha2HdS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PA3APA2dX2r22PXS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TBS1L2HI2ra2sp2h01h1A3HTQ3POS3SPB2TB2h22dA1r3HT22PA2Er2h33HT3S1L2HI2ra2sp2h01h1A3HTQ3POS3SPB2TB2h22dA1r3HT22PA2Er2h32dX2r23HT32PX3Er2S2ra2sp1A2TBS2ra2sp1A2TBS1L2ra2sp1A2lo2LO2TBS1L2ra2sp1A2lo2LO2TB2dA1r2PAS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS1L1A2ND1a2HaS2ra2sp1A2TB1a2C1S2ra2sp1A2TB1a2C22C1S2ra2sp1A2TB1a2C2S2ra2sp1A2TB2xx3HxxS2ra2sp1A2TB2dA1r2PA2xx3HxxS2ra2sp1A2TBS2ra2sp1A2TB2dA1r2PAS2ra2sp1A2TB". (* [comment removed for export] *)
  Lemma case13 : ltac2:(CDefT.buildp (gd_tbl_P_ecp_group_load_mx2 ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pxa0,(0.&40.)Pxa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(2.(0.&8.))Pm,P,(0.&40.)(2.(0.&8.))Pmo0,$3.Pmo,$3.Ph0,(4.$5.VL,VHI,)Ph,(4.$5.VL,VHI,)PLB,(6.$7.)PA,$8.Pg,$9.Plo,$8.Pidpad,(0.&40.)PpP,(0.&40.)PpA,(0.&40.)PpB,(0.&40.)PpX,(0.&40.)PpY,(0.&40.)PpZ,(0.&40.)PpN,(0.&40.)Phpad,(0.&40.)Pxra,(0.&40.)Pfj,(6.(0.&8.))ZLBf,(6.$7.)(:.R=.R?.)P,(;.$5.VL,VHI,R11.R1.R15.R13.)P,(<.$8.(=.$5.VL,VHI,R12.)(=.$5.VL,VHI,R13.))P,(>.R16.R15.)P,(?.$5.VL,R4.(10.&40.R39.)(11.(12.$8.$8.)(13.$8.$8.R12.(14.R12.+<0.))(15.(12.$8.$8.)))R19.R18.)P,(16.$5.R19.R13.(11.$17.(18.(19.&40.+=.))(11.$17.(18.R10.)(15.$17.))))P,(<.$8.(1:.R14.+8.)=)P,(1;.=R15.)P,(16.$5.R1<.(14.R16.+8.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R1=.(14.R17.+18.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R1>.(14.R18.+28.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R1?.(14.R19.+38.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R20.(14.R1:.+48.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R21.(14.R1;.+58.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R22.(14.R1<.+68.)(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.+1.))(11.$17.(18.R12.)(15.$17.)))))P,(16.$5.R23.(14.R1=.+78.)(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(18.(19.&40.=))(11.$17.(18.R12.)(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(11.$17.(1<.(19.&40.=))(15.$17.))))))))))))P,(16.$5.R24.(1=.(10.&40.R45.)+20.)(11.$17.(1>.#8.R11.)(11.$17.(1<.R3>.)(11.$17.(1<.R3?.)(11.$17.(1<.R46.)(15.$17.))))))P,(1?.$5.R25.R1=.(1=.(10.&40.R46.)+20.))P,(20.=R1>.)P,(20.R1?.(1=.(1=.(10.&40.R48.)+70.)(21.VL,)))P,(22.(20.(14.R22.+<0.)R20.)(20.(10.&40.R49.)R22.))P,(23.VL,R15.(10.&40.R4:.)(=.$5.VL,VHI,R26.)R23.+<0.)P,(22.(20.(14.R24.+<0.)(24.VL,))(20.(25.VL,)R24.))P,(20.(26.VL,)R23.)P,(20.(10.&40.R4=.)(=.$5.VL,VHI,R29.))P,(20.(25.VL,)(26.VL,))P,(27.$5.R2>.)P,(28.$5.VL,R2?.)P,(<.$8.(1:.(10.&40.R52.)+2.)=)P,(29.(2:.R2:.))P,(<.(0.&40.)R51.(19.&40.(2;.VL,)))P,(2<.VL,$2=.+8.)P,(<.$8.(1:.(10.&40.R55.)+10.)=)(2>.$5.R33.(2?.$5.VL,VHI,$30.$31.$32.R57.R56.R55.R54.R50.R4?.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R38.R37.R32.R30.R2?.R2>.+=.R2=.R36.R34.)(33.(34.R23.(19.&40.(1=.(10.&40.R56.)+20.))R55.R54.R53.R52.R51.(19.&40.R2?.)(19.&40.+=.)R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.)R38.(19.&40.+3;=88.)R37.(35.(0.&40.))R35.(36.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros until fj. cbv zeta. intros HH HTQ MF PXA HD AL POS HP HA HB HX HY HZ HN HT FR ST LO0 LO SX CW ND ACL HTOP DHI MI SOK RA DIS TP CA SPA.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP. flat constr:(DIMG) 2%nat. intros DI1 DI2.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (rw_cells_bound _ _ _ _ HT) as TB. cbn [cells_size csize Nat.add length] in TB.
    pose proof (U_curve_statics m 13 MI ltac:(lia)) as CS. flat constr:(CS) 5%nat. intros STP _ _ STN _. pose proof (lock MI) as MI00.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBRf _.
    assert (MPB : 0 <= ca_modp (U_CA 13) < 2^64 /\ In (ca_modp (U_CA 13), (ca_P (U_CA 13), cP 13)) U_MT) by (cbn -[c9_P c13_P]; split; [lia| auto 20]).
    flat constr:(MPB) 2%nat. flclear MPB. intros MB MODP.
    pose proof (munch_refl [(A, A + 192); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (conj HH I) as HH0. clear HH.
    pose proof SOK as SOKm.
    clear HCALLOC HFREE || idtac.
    (* [comment removed for export] *)
    try clear LXSUMS. assert (LXSUMS : forall AL', Forall (summary_okG usegs AL' []) (@nil summary)) by (intros AL'; constructor).
    rewrite ?TP. apply (lxp_aevtM_of_evt usegs mo _ _ MK).
    lx_run_tac (PLANS [0x1fb64] [] 60%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- ?TP.
    clear HD HP HA HB HX HY HZ HN HT FR ST. try clear MU. try clear WM.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with Hm : munch _ m mx, Hw : wmono _ m mx, Hg : rw_cells _ mx A _, Hf : rw_cells _ mx _ [CB 8 fj; _; _; _], Hs : stk _ mx _ _, Hi : mem_inv _ mx |- _ =>
        rename Hm into MU; rename Hw into WM; rename Hf into FR; rename Hs into ST; rename Hg into HD;
        pose proof (statics_ok_munch usegs L _ _ _ SOKm MU ltac:(intros a Ha NW; cbn; repeat split; try exact I; clear -Ha ND DHI ACL LO HLS; lia)) as SOK'; clear SOK; try clear MI; rename SOK' into SOK; rename Hi into MI
      end end.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => grp_recut mx A;
      lazymatch goal with H0 : rw_cells _ mx A _, H1 : rw_cells _ mx (A + 8) _, H2 : rw_cells _ mx (A + 24) _, H3 : rw_cells _ mx (A + 40) _, H4 : rw_cells _ mx (A + 56) _,
                          H5 : rw_cells _ mx (A + 72) _, H6 : rw_cells _ mx (A + 88) _, H7 : rw_cells _ mx (A + 104) _, H8 : rw_cells _ mx (A + 120) _ |- _ =>
        rename H0 into HD; rename H1 into HP; rename H2 into HA; rename H3 into HB; rename H4 into HX; rename H5 into HY; rename H6 into HZ; rename H7 into HN; rename H8 into HT end end.
    replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) in FR, ST by lia. try replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia.
    lazymatch type of MU with munch _ m ?mx => change (munch [(A, A + 192); (bv_unsigned sp - 32, bv_unsigned sp)] m mx) in MU end.
    apply mpi_cells_of_sn in HP; [| lia]. change (1048577 mod 2 ^ 16) with 1 in HP. change (1048577 / 2 ^ 16) with 16 in HP.
    (* [comment removed for export] *)
    pose proof U_mpi_bitlen_spec as SPB_. unfold mpi_bitlen_stmt in SPB_.
    eapply aevtM_cut_evt; [exact MK| eapply SPB_ with (dX := smpd (A + 8) (ca_P (U_CA 13)) (cP 13) pP) (LB := grp_free_LB g LB);
      [ eapply smpd_mpd_at; [exact HP| lia| lia| eapply static_limbs_any_mem; [exact STP| exact (unlock _ MI00)| assumption]]
      | cbn; discriminate | assumption | reflexivity ] |].
    clear SPB_. unfold mpi_query_post. match goal with H : mem_inv usegs ?mc |- _ => post_call usegs mc end.
    match goal with H : ?r = core_bitlen _ _ |- _ => subst r end.
    unfold mpi_cells in HP.
    clear HCALLOC HFREE || idtac.
    (* [comment removed for export] *)
    try clear LXSUMS. assert (LXSUMS : forall AL', Forall (summary_okG usegs AL' []) (@nil summary)) by (intros AL'; constructor).
    rewrite ?TP. apply (lxp_aevtM_of_evt usegs mo _ _ MK).
    lx_run_tac (PLANS [0x1f808] [] 60%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- ?TP.
    clear HD HP HA HB HX HY HZ HN HT FR ST. try clear MU. try clear WM.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with Hm : munch _ m mx, Hw : wmono _ m mx, Hg : rw_cells _ mx A _, Hf : rw_cells _ mx _ [CB 8 fj; _; _; _], Hs : stk _ mx _ _, Hi : mem_inv _ mx |- _ =>
        rename Hm into MU; rename Hw into WM; rename Hf into FR; rename Hs into ST; rename Hg into HD;
        pose proof (statics_ok_munch usegs L _ _ _ SOKm MU ltac:(intros a Ha NW; cbn; repeat split; try exact I; clear -Ha ND DHI ACL LO HLS; lia)) as SOK'; clear SOK; try clear MI; rename SOK' into SOK; rename Hi into MI
      end end.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => grp_recut mx A;
      lazymatch goal with H0 : rw_cells _ mx A _, H1 : rw_cells _ mx (A + 8) _, H2 : rw_cells _ mx (A + 24) _, H3 : rw_cells _ mx (A + 40) _, H4 : rw_cells _ mx (A + 56) _,
                          H5 : rw_cells _ mx (A + 72) _, H6 : rw_cells _ mx (A + 88) _, H7 : rw_cells _ mx (A + 104) _, H8 : rw_cells _ mx (A + 120) _ |- _ =>
        rename H0 into HD; rename H1 into HP; rename H2 into HA; rename H3 into HB; rename H4 into HX; rename H5 into HY; rename H6 into HZ; rename H7 into HN; rename H8 into HT end end.
    replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) in FR, ST by lia. try replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia.
    lazymatch type of MU with munch _ m ?mx => change (munch [(A, A + 192); (bv_unsigned sp - 32, bv_unsigned sp)] m mx) in MU end.
    lazymatch type of HP with rw_cells _ ?mq _ [C8 (Z_to_bv 64 ?p); C2 (Z_to_bv 64 ?sg); C2 (Z_to_bv 64 ?nn); C4 ?pd] => change (rw_cells usegs mq (A + 8) (mpi_cells p (Z_to_bv 64 sg) nn pd)) in HP end.
    apply mpi_cells_of_sn in HN; [| lia]. change (1048577 mod 2 ^ 16) with 1 in HN. change (1048577 / 2 ^ 16) with 16 in HN.
    apply mpi_cells_of_sn in HA; [| lia]. apply mpi_cells_of_sn in HB; [| lia]. apply mpi_cells_of_sn in HX; [| lia]. apply mpi_cells_of_sn in HY; [| lia]. apply mpi_cells_of_sn in HZ; [| lia].
    change (1 mod 2 ^ 16) with 1 in HA, HB, HX, HY, HZ. change (1 / 2 ^ 16) with 0 in HA, HB, HX, HY, HZ.
    (* [comment removed for export] *)
    flat constr:(HH0) 2%nat. flclear HH0. intros HHo _.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HH : HEAP usegs L HI h (grp_free_LB g LB) m1 mo).
    { apply (@HEAP_munch usegs L HI h _ m m1 mo _ lo HHo MU WM ACL).
      intros a Ha NO. cbn in NO. rewrite HTQ.
      destruct (Z_le_dec A a) as [C1|C1]; [destruct (Z_lt_dec a (A + 192)) as [C2|C2]|].
      - destruct (CW a ltac:(lia)) as [Q|[Q|Q]]; [left; lia| right; left; exact Q| right; right; exact Q].
      - left. destruct (Z_le_dec (bv_unsigned sp - 32) a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; repeat split; try exact I; lia..].
      - left. destruct (Z_le_dec (bv_unsigned sp - 32) a); [destruct (Z_lt_dec a (bv_unsigned sp))|]; [lia| exfalso; apply NO; repeat split; try exact I; lia..]. }
    assert (PX1 : heap_presx usegs L (grp_free_LB g LB) (bv_unsigned sp) [(A, A + 192)] m0 m1).
    { eapply heap_presx_trans; [exact PXA|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. cbn in Ho |- *. flat constr:(Ho) 2%nat. flclear Ho. intros Ho _. split; [exact Ho|]. split; [| exact I].
      destruct Hc as [C|[C|([b kk] & Hb & C)]]; [lia| lia|]. cbn in C. flat constr:((proj1 (Forall_forall _ _) HBRf _ Hb)) 5%nat. intros _ _ _ B4 _. cbn in B4. lia. }
    clear HHo PXA MU WM MK. pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    assert (SUBr : forall b : blk, In b (grp_free_LB g LB) -> In b (grp_free_LB g LB)) by (intros b Hb; exact Hb).
    (* [comment removed for export] *)
    pose proof (U_mpi_lset_spec L HI HCALLOC HLS SW DIMG HND) as SL. unfold mpi_lset_stmt, U_MPI_LSET in SL.
    eapply aevtM_cut.
    { eapply SL with (lo := lo) (h := h) (LB := grp_free_LB g LB) (dX := mpd_init (A + 24) pA) (z := 39082); rewrite ?(unsigned_lit (bv_unsigned sp - 32)) by lia;
        first [ exact HH | exact TP | exact SOK | exact CA | reflexivity
              | apply mpd_of_mpdr; [apply mpdr_at_init; [exact HA| lia| lia]| left; reflexivity]
              | cbn; discriminate
              | split; [rewrite HTQ; eapply (client_wrange_weak L); [exact CW| exact SUBr| lia| cbn; lia| cbn; lia]| split; [intros a Ha Hd; exfalso; cbn in Ha; lia| cbn; discriminate]]
              | match goal with |- stk _ _ _ _ => eassumption end
              | match goal with |- mem_inv _ _ => assumption end
              | lia
              | first [reflexivity| apply bv_eq; vm_compute; reflexivity]
              | match goal with |- ?gg => idtac "LSET1LEFT" gg end ]. }
    cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    flat constr:(PO) 22%nat. flclear PO. intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 m2 mo2 h2 LB1 dA r E PO. injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp - 32)) in PO by lia.
    flat constr:(PO) 10%nat. flclear PO. intros MI2 ST2 MF2 HT2 HH2 MA2 OUT PXl SOK2 LR.
    replace (ret_pc (Z_to_bv 64 0x3bde8)) with (Z_to_bv 64 0x3bde8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    cbn [mpd_ivs md_addr md_own mpd_init] in PXl.
    flat constr:(OUT) 5%nat. flclear OUT. intros EAa OA OUT1 OUT2 OUT3. cbn [md_addr mpd_init mpd_blk md_own] in EAa, OUT1, OUT2, OUT3.
    assert (SUB1 : forall b, In b (grp_free_LB g LB) -> In b LB1) by (intros b Hb; apply OUT2; [exact Hb| intros []]).
    clear HA. presx_all usegs L PXl CW SUBr.
    assert (PX2 : heap_presx usegs L (grp_free_LB g LB) (bv_unsigned sp) [(A, A + 192)] m0 m2).
    { eapply heap_presx_trans; [exact PX1|]. eapply (heap_presx_weak usegs L); [exact PXl| exact SUBr| lia|]. intros xx Hxx. cbn in Hxx |- *. split; [lia| exact I]. }
    match goal with STo : stk usegs m1 _ _, MIo : mem_inv usegs m1 |- _ => clear STo MIo end. clear PX1 SOK MK HH MU WM.
    pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK. pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      destruct LR as ([(Er & _) | [Er EdA]] & _ & FRA); [exfalso; subst r; apply K0; reflexivity|]. subst r. subst dA.
      eapply (mx_fail) with (dA := mpd_init (A + 24) pA) (dX := mpd_init (A + 56) pX) (dZ := mpd_init (A + 88) pZ)
                            (idpad := idpad) (pP := pP) (pB := pB) (pY := pY) (pN := pN) (hpad := hpad);
        first [ glia| reflexivity| exact HH2| rewrite HT2; exact HTQ| exact (mo_frame_trans _ _ _ MF MF2)| exact PX2| exact FR| exact ST2| exact CW| exact ND| exact MI2| exact SOK2| exact TP| exact CA
              | eapply grp_mxi_at; first [glia| exact MODP| exact MB| exact HD| exact HP| exact HB| exact HY| exact HN| exact HT| exact (mpdr_of_mpd _ _ _ _ MA2)
                                         | exact (mpdr_at_init _ _ _ _ _ HX ltac:(lia) ltac:(lia))| exact (mpdr_at_init _ _ _ _ _ HZ ltac:(lia) ltac:(lia))
                                         | apply mx_field_init
                                         | eapply curve_statics_any_mem; [exact CS| exact (unlock _ MI00)| exact MI2]
                                         | match goal with |- ?gg => idtac "GMXI1" gg end ]
              | apply grp_mxi_apart; [apply mx_field_init| apply mx_field_init| apply mx_field_init| cbn; intros; discriminate..]
              | intros b; split; [intros Hb; destruct (OUT1 b Hb) as [Hc|Hz]; [right; exact Hc| cbn in Hz; destruct Hz]| intros [Hb|Hb]; [cbn in Hb; destruct Hb| apply SUB1; exact Hb]]
              | intros b Hb; cbn in Hb; destruct Hb
              | match goal with |- ?gg => idtac "TOFAIL1" gg end]. }
    (* [comment removed for export] *)
    destruct LR as ([(Er & An & Ao & Al & As & Apd) | [Er EdA]] & _ & FRA); [| exfalso; subst r; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K0; cbv in K0; discriminate].
    cbn [md_n mpd_init md_addr] in An, EAa. change (if 39082 <? 0 then -1 else 1) with 1 in As.
    flat constr:((lset_heap1 dA (A + 24) An Ao Al As EAa)) 2%nat. intros wA EdA.
    rewrite EdA in MA2. set (PA := md_p dA) in *. set (pdA := md_pad dA) in *.
    assert (INA : In (PA, 4) LB1) by (pose proof MA2 as [[_ (_ & _ & _ & _ & (_ & IN & _))] _]; exact IN).
    assert (FPA : ~ In (PA, 4) (grp_free_LB g LB)).
    { intros C. destruct (FRA (PA, 4)) as [[]|NI]; [| exact (NI C)]. rewrite EdA. cbn. left. reflexivity. }
    assert (APA : A + 192 <= PA \/ PA + 4 <= A).
    { flat constr:((heap_blocks _ _ HI _ _ _ _ HH2)) 2%nat. intros HBR2 HAP2.
      eapply (client_apart_block L (grp_free_LB g LB) LB1); [exact CW| exact SUB1| exact HBR2| exact HAP2| exact INA| exact FPA| lia| lia| exact DHI| lia| exact DI1| exact DI2]. }
    assert (IFF1 : forall b, In b LB1 <-> In b [(PA, 4)] \/ In b (grp_free_LB g LB)).
    { intros b. split.
      - intros Hb. destruct (OUT1 b Hb) as [Hc|Hz]; [right; exact Hc| left]. rewrite EdA in Hz. cbn in Hz |- *. exact Hz.
      - intros [[<-|[]]|Hb]; [exact INA| apply SUB1; exact Hb]. }
    clear OUT1 OUT2 OUT3 FRA.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    eapply aevtM_cut.
    { eapply SL with (lo := lo) (h := h2) (LB := LB1) (dX := mpd_init (A + 56) pX) (z := 5); rewrite ?(unsigned_lit (bv_unsigned sp - 32)) by lia;
        first [ exact HH2 | exact TP | exact SOK2 | exact CA | reflexivity
              | apply mpd_of_mpdr; [apply mpdr_at_init; [exact HX| lia| lia]| left; reflexivity]
              | cbn; discriminate
              | split; [rewrite HT2, HTQ; eapply (client_wrange_weak L); [exact CW| exact SUB1| lia| cbn; lia| cbn; lia]| split; [intros a Ha Hd; exfalso; cbn in Ha; lia| cbn; discriminate]]
              | match goal with |- stk _ _ _ _ => eassumption end
              | match goal with |- mem_inv _ _ => assumption end
              | lia
              | match goal with |- ?gg => idtac "LSET2LEFT" gg end ]. }
    cbv beta. intros ms' mo' PO. unfold mpi_binop_post in PO.
    flat constr:(PO) 22%nat. flclear PO. intros z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 m3 mo3 h3 LB2 dX r2 E PO. injection E as -> ->.
    rewrite ?(unsigned_lit (bv_unsigned sp - 32)) in PO by lia.
    flat constr:(PO) 10%nat. flclear PO. intros MI3 ST3 MF3 HT3 HH3 MX3 OUT PXl2 SOK3 LR.
    replace (ret_pc (Z_to_bv 64 0x3bdf8)) with (Z_to_bv 64 0x3bdf8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    cbn [mpd_ivs md_addr md_own mpd_init] in PXl2.
    flat constr:(OUT) 5%nat. flclear OUT. intros EXa OX OUT1 OUT2 OUT3. cbn [md_addr mpd_init mpd_blk md_own] in EXa, OUT1, OUT2, OUT3.
    assert (SUB2 : forall b, In b LB1 -> In b LB2) by (intros b Hb; apply OUT2; [exact Hb| intros []]).
    assert (SUBf2 : forall b, In b (grp_free_LB g LB) -> In b LB2) by (intros b Hb; apply SUB2, SUB1, Hb).
    clear HX. presx_all usegs L PXl2 CW SUB1.
    assert (MA3 : mpd_at usegs m3 LB2 (heap1 (A + 24) PA wA pdA)).
    { apply mpd_of_mpdr; [| left; reflexivity]. eapply mpdr_at_LB_mono; [| exact SUB2].
      eapply (mpdr_at_presx usegs L m2 m3); [exact (mpdr_of_mpd _ _ _ _ MA2)| exact PXl2| exact MI2| exact MI3| | cbn; lia|].
      - cbn. eapply (client_range_of_wrange L); [exact CW| exact SUB1| lia| lia| lia].
      - cbn. intros _. split; [exact INA| lia]. }
    assert (PX3 : heap_presx usegs L (grp_free_LB g LB) (bv_unsigned sp) [(A, A + 192)] m0 m3).
    { eapply heap_presx_trans; [exact PX2|]. eapply (heap_presx_weak usegs L); [exact PXl2| exact SUB1| lia|]. intros xx Hxx. cbn in Hxx |- *. split; [lia| exact I]. }
    clear MA2 PX2 ST2 MI2 SOK2 MK HH2 MU WM.
    pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK. pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      destruct LR as ([(Er2 & _) | [Er2 EdX]] & _ & FRX); [exfalso; subst r2; apply K1; reflexivity|]. subst r2. subst dX.
      eapply (mx_fail) with (dA := heap1 (A + 24) PA wA pdA) (dX := mpd_init (A + 56) pX) (dZ := mpd_init (A + 88) pZ)
                            (idpad := idpad) (pP := pP) (pB := pB) (pY := pY) (pN := pN) (hpad := hpad);
        first [ glia| reflexivity| exact HH3| rewrite HT3, HT2; exact HTQ| exact (mo_frame_trans _ _ _ MF (mo_frame_trans _ _ _ MF2 MF3))| exact PX3| exact FR| exact ST3| exact CW| exact ND| exact MI3| exact SOK3| exact TP| exact CA
              | eapply grp_mxi_at; first [glia| exact MODP| exact MB| exact HD| exact HP| exact HB| exact HY| exact HN| exact HT| exact (mpdr_of_mpd _ _ _ _ MA3)| exact (mpdr_of_mpd _ _ _ _ MX3)
                                         | exact (mpdr_at_init _ _ _ _ _ HZ ltac:(lia) ltac:(lia))
                                         | apply mx_field_init| apply mx_field_heap1
                                         | eapply curve_statics_any_mem; [exact CS| exact (unlock _ MI00)| exact MI3]
                                         | match goal with |- ?gg => idtac "GMXI2" gg end ]
              | apply grp_mxi_apart; [apply mx_field_heap1| apply mx_field_init| apply mx_field_init| cbn; intros; discriminate..]
              | intros b; split; [intros Hb; destruct (OUT1 b Hb) as [Hc|Hz]; [exact (proj1 (IFF1 b) Hc)| cbn in Hz; destruct Hz]| intros Hb; apply SUB2; exact (proj2 (IFF1 b) Hb)]
              | intros b [<-|[]]; exact FPA
              | match goal with |- ?gg => idtac "TOFAIL2" gg end]. }
    (* [comment removed for export] *)
    destruct LR as ([(Er2 & Xn & Xo & Xl & Xs & Xpd) | [Er2 EdX]] & _ & FRX); [| exfalso; subst r2; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in K1; cbv in K1; discriminate].
    cbn [md_n mpd_init md_addr] in Xn, EXa. change (if 5 <? 0 then -1 else 1) with 1 in Xs.
    flat constr:((lset_heap1 dX (A + 56) Xn Xo Xl Xs EXa)) 2%nat. intros wX EdX.
    rewrite EdX in MX3. set (PX := md_p dX) in *. set (pdX := md_pad dX) in *.
    assert (INX : In (PX, 4) LB2) by (pose proof MX3 as [[_ (_ & _ & _ & _ & (_ & IN & _))] _]; exact IN).
    assert (FPX1 : ~ In (PX, 4) LB1).
    { intros C. destruct (FRX (PX, 4)) as [[]|NI]; [| exact (NI C)]. rewrite EdX. cbn. left. reflexivity. }
    assert (APX : A + 192 <= PX \/ PX + 4 <= A).
    { flat constr:((heap_blocks _ _ HI _ _ _ _ HH3)) 2%nat. intros HBR3 HAP3.
      eapply (client_apart_block L (grp_free_LB g LB) LB2); [exact CW| exact SUBf2| exact HBR3| exact HAP3| exact INX| intros C; apply FPX1, SUB1, C| lia| lia| exact DHI| lia| exact DI1| exact DI2]. }
    zstep.
    eapply (mx_third) with (PA := PA) (PX := PX);
      first [ glia| exact HH3| rewrite HT3, HT2; exact HTQ| exact (mo_frame_trans _ _ _ MF (mo_frame_trans _ _ _ MF2 MF3))| exact PX3
            | exact HD| exact HP| exact MA3| exact HB| exact MX3| exact HY| exact HZ| exact HN| exact HT| exact FR| exact ST3| exact CW| exact ND| exact MI3| exact SOK3| exact TP| exact CA| exact APA| exact APX
            | intros C; apply FPX1, SUB1, C
            | intros E; apply FPX1; rewrite <- E; exact INA
            | intros b; split; [intros Hb; destruct (OUT1 b Hb) as [Hc|Hz]; [destruct (proj1 (IFF1 b) Hc) as [H1|H1]; [left; cbn in H1 |- *; clear -H1; tauto| right; exact H1]| rewrite EdX in Hz; cbn in Hz; left; cbn; clear -Hz; tauto]
                               | intros [[<-|[<-|[]]]|Hb]; [apply SUB2; exact INA| exact INX| apply SUBf2; exact Hb]]
            | exact FPA
            | lia
            | match goal with |- ?gg => idtac "TOTHIRD" gg end].
  all: fail.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End MX.
