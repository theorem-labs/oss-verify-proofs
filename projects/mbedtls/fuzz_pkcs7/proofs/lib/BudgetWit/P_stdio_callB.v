(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-11: made from P/P_stdio_call.v for the budget-premise witness: the same proofs over BudgetWit.Rzb.realizes, the released Shape.realizes with a no-allocation-call check at each node; only the module names change. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 as P/P_stdio_call.v was (stdio_call_sound_fr and stdio_call_sound written out in plain text from their encoded (CDefT) form, with the new premise Hrdr, the channel reader writev reads, after the fd one; the plain-text statements over BudgetWit.Rzb.realizes). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import Plain.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StoreOk ShapeX AgentLib SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame Hoare.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_exit_base P_stdio_defs P_stdio_write.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_stdio_call.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BudgetWit Require Import Rzb ShapeXB AgentNodesB NodesB SysNodesB SymDriveB P_stdio_writeB.
Ltac2 gd_tbl_P_stdio_callB () : Init.string Init.list := ["OSSVerify.KrLib.BB.SymExec2.SX2.env"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.BB.SymExec2.SX2.kentry"; "OSSVerify.KrLib.BB.SymExec2.SX2.expr"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.BB.SymExec2Sound.SX2S.know_ok"; "OSSVerify.KrSpec.Problems.Src_mbedtls_fuzz_pkcs7_repro.M.loaded_segments"; "OSSVerify.KrLib.BB.SymExec2Sound.SX2S.flat"; "OSSVerify.KrLib.BB.SymExec2.SX2.SA"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.BB.SymExec2Sound.SX2S.estart"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.BB.StoreOk.mem_grows"; "OSSVerify.KrLib.BB.LibKnowFrame.kn_frame"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.BB.SymExec2.SX2.ELit"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.BB.SymDriveX.kindex"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.ex"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Nat.sub"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Peano.le"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "stdio_res"; "OSSVerify.KrLib.Lib.Shape.TSet"; "OSSVerify.KrLib.BB.SymExec2.SX2.Env"; "OSSVerify.KrLib.BB.SymRun.vals_ev"; "OSSVerify.KrLib.BB.SymExec2Sound.SX2S.regs_ok"; "stdio_call"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.BB.SymExec2.SX2.edenot"; "sc_wb"; "sc_wp"; "sc_s"; "sc_l"; "sc_sp"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Lib.PropExec.rdn"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "sc_fd"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "OSSVerify.KrLib.P.P_stdio_defs.sw_post"; "sc_f"; "sc_bufp"; "sc_bufsz"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.BB.SymDrive.junk_vals"; "sc_sr"; "sc_kn"; "OSSVerify.KrLib.BudgetWit.Rzb.realizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.Lib.PropExec.mkst"; "OSSVerify.KrLib.Lib.PropExec.fx0"; "sc_ret"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Shape.t_emit"; "Corelib.Lists.ListDef.map"; "LinuxProcessSemantics.LinuxProcessSem.State.WriteEv"].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "01G0@L10147336370.122L11800017315.122L1269136438.100 L13497582825.94 L14382054636.97 L19802039715.130L19804219060.129L22032974447.92 L22035172350.130L2431328725.95  L25271909867.91 L25272066322.130L25274328837.94 L25274328855.93 L25274329219.92 L25274329358.97 L25278521367.95 L25280620701.96 L26853587145.73 L28043634281.129L28045256062.130L28341091363.130L28343402292.129L30300022934.92 L30302216455.130L31288797821.129L31327315070.95 L31814543760.100L31883569636.96 L32767907856.94 L33658348128.95 L33660447466.96 L33668932453.130L33669037980.91 L33670931808.93 L33670931826.94 L33670933236.92 L33670933369.97 L33800618370.95 L34301857074.133L3829630897.95  L4004592180.126 L41048590717.129L41403848445.88 L41810303230.91 L42365245083.133L4504975677.95  L46771001897.100L48654120105.98 L52210688097.100L5221991938.93  L5224251399.130 L52651124876.73 L54438946866.123L54438949041.122L54441047219.124L54495773355.100L55847319119.100L56729402047.100L57591098531.130L58141926407.91 L5926593349.91  L5929023021.92  L5929023392.97  L5929023915.94  L5929023929.93  L5933219513.95  L5935314483.96  L61379100552.89 L61905624951.97 L62000869932.129L63370209020.129L63482897878.100L64018718057.75 L64018718058.77 L64020815210.74 L64020815339.76 L64160619826.122L64724293782.80 L65047624831.96 L65500146556.129L65922976903.130L6645866793.98  L7493038203.95  L9996218345.129 L9996593915.93  L9998527742.130 00000o01n03P04U05T06[07b08g09l0:o0;n0<m0=l0>k0?j0@i0Ah0Bg0Co0E40F90G@0HG0IN0JU0K\0Lk0N00No0P60Q50R40S30T20U10V00Vo0Wn0Y50Z>0[E0\S0]Z0^h0_o0aB0bG0ci0d_0ei0g00h70i30j20k10l30m:0n<0oA10H11M12L13K14J15I16H17G18F19T1:S1<91=81>=1?91@51A11Am1Bl1DL1EK1FJ1GQ1HG1IL1JQ1KV1L[S2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg2qb2k03blo3bhi5Hfd126Hsplo'6Hlen322wb2wp2sp2su5Hretv4Hqbr2HqS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg3Hf05Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg3Hf05Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg3Hf05Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2su1n1BS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret3Hb13Hb23Hb32fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg3Hf05Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg3Hf05Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2su5Hretv3off1n1B1CS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2su5HretvS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2su1x2N22N3S2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2su3off1n1CS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2su5Hretv1i2Hi3HneS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg2k05Hfd126Hlen322wb2wp2sp2su2ck4clen3Hc2S2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg2qb2k05Hfd126Hlen322wb2wp2sp2su5Hretv2Hq1x2N1S2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2su3off1AS2sr7pending5extra1E3ret2fd3wpe3wbe2cg2qb2k03blo3bhi5Hfd126Hsphi'6Hlen322wb2wp2sp2su5Hretv4Hqbr2HqS2sr7pending5extra1E3ret3wpe3wbe2cg6Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp5Hwbwp2sp2su4HwbrS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2su2HiS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2su2TwS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2su5HretvS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg3Hf05Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg2qb2k05Hfd126Hlen322wb2wp2sp2su5Hretv2HqS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg2qb2k03blo3bhi5Hfd126Hsplo'6Hsphi'6Hlen322wb2wp2sp2su5Hretv4HqbrS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg3Hf05Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg2qb2k03blo3bhi5Hfd126Hsplo'6Hsphi'6Hlen322wb2wp5Hretv4HqbrS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret3wpe3wbe2cg6Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg3Hf05Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg3Hf05Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg3Hf05Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg3Hf05Hfd126Hlen322wb2wp2sp2su". (* [comment removed for export] *)
Theorem stdio_call_sound_fr :
  (* plain text: new premise [Hrdr] after the fd one, the channel reader the revision's writev reads (recipes/channel-reader-premise.md) *)
  (forall vals : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 64%N)), (forall ebs : (forall x_ : (@Corelib.Init.Datatypes.nat), (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))), (forall sr : (@Corelib.Init.Datatypes.list (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.expr)), (forall kn : (@Corelib.Init.Datatypes.list (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.kentry)), (forall R : (@LinuxProcessSemantics.Riscv.Prelude.bvmap 5%N (@stdpp.bitvector.definitions.bv 64%N)), (forall M : (forall x_ : (@stdpp.bitvector.definitions.bv 64%N), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 8%N))), (forall model : (@LinuxProcessSemantics.LinuxProcessSem.State.Model), (forall res : (@stdio_res), (forall pending : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), (forall extra : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), (forall K : (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Shape.TSet), (let E : (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.env) := (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.Env (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymRun.vals_ev vals) ebs) in (forall x_ : (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2Sound.SX2S.regs_ok E sr R), (forall x_1 : (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2Sound.SX2S.know_ok (@OSSVerify.mbedtls.fuzz_pkcs7.images.Plain.M.loaded_segments) E M kn), (forall x_2 : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@stdio_res)) (@stdio_call (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 64%N) vals) sr kn) (@Corelib.Init.Datatypes.Some (@stdio_res) res)), (let wb : (@Corelib.Numbers.BinNums.Z) := (@stdpp.bitvector.definitions.bv_unsigned 64%N (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.edenot E (@sc_wb res))) in (let wp : (@Corelib.Numbers.BinNums.Z) := (@stdpp.bitvector.definitions.bv_unsigned 64%N (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.edenot E (@sc_wp res))) in (let s : (@stdpp.bitvector.definitions.bv 64%N) := (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.edenot E (@sc_s res)) in (let l : (@stdpp.bitvector.definitions.bv 64%N) := (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.edenot E (@sc_l res)) in (let su : (@Corelib.Numbers.BinNums.Z) := (@stdpp.bitvector.definitions.bv_unsigned 64%N (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.edenot E (@sc_sp res))) in (forall x_3 : (@Stdlib.ZArith.BinInt.Z.le wb wp), (forall x_4 : (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) (@Stdlib.ZArith.BinInt.Z.sub wp wb) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) pending))), (forall x_5 : (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) (@stdpp.bitvector.definitions.bv_unsigned 64%N l) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) extra))), (forall x_6 : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) pending)) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) extra))) (@Stdlib.ZArith.BinInt.Z.pow 2%Z 30%Z)), (forall x_7 : (@Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le wp (@Stdlib.ZArith.BinInt.Z.sub su 112%Z)) (@Stdlib.ZArith.BinInt.Z.le su wb)), (forall x_8 : (@Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N s) (@stdpp.bitvector.definitions.bv_unsigned 64%N l)) (@Stdlib.ZArith.BinInt.Z.sub su 112%Z)) (@Stdlib.ZArith.BinInt.Z.le su (@stdpp.bitvector.definitions.bv_unsigned 64%N s))), (forall x_9 : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N s) (@stdpp.bitvector.definitions.bv_unsigned 64%N l)) (@Stdlib.ZArith.BinInt.Z.pow 2%Z 64%Z)), (forall x_10 : (@Stdlib.ZArith.BinInt.Z.le wp 140737488355328%Z), (forall x_11 : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N s) (@stdpp.bitvector.definitions.bv_unsigned 64%N l)) 140737488355328%Z), (forall x_12 : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.rdn (@OSSVerify.mbedtls.fuzz_pkcs7.images.Plain.M.loaded_segments) M (@stdpp.bitvector.definitions.Z_to_bv 64%N wb) (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) pending)) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) pending)), (forall x_13 : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.rdn (@OSSVerify.mbedtls.fuzz_pkcs7.images.Plain.M.loaded_segments) M s (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) extra)) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) extra)), (forall x_14 : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@LinuxProcessSemantics.LinuxProcessSem.State.FdEntry)) (@LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup (@LinuxProcessSemantics.LinuxProcessSem.State.m_fds model) (@stdpp.bitvector.definitions.Z_to_bv 64%N (@sc_fd res))) (@Corelib.Init.Datatypes.Some (@LinuxProcessSemantics.LinuxProcessSem.State.FdEntry) (@LinuxProcessSemantics.LinuxProcessSem.State.FdChannel (@stdpp.bitvector.definitions.Z_to_bv 64%N (@sc_fd res))))), (forall Hrdr : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.bool) (@LinuxProcessSemantics.LinuxProcessSem.State.m_channel_reader model) (@Corelib.Init.Datatypes.true)), (forall x_15 : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 64%N)) (@LinuxProcessSemantics.LinuxProcessSem.State.m_halted model) (@Corelib.Init.Datatypes.None (@stdpp.bitvector.definitions.bv 64%N))), (forall x_16 : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.list (@Corelib.Init.Datatypes.prod (@stdpp.bitvector.definitions.bv 64%N) (@stdpp.bitvector.definitions.bv 64%N))) (@LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy model) (@Corelib.Init.Datatypes.nil (@Corelib.Init.Datatypes.prod (@stdpp.bitvector.definitions.bv 64%N) (@stdpp.bitvector.definitions.bv 64%N)))), (forall x_17 : (K (@Corelib.Init.Datatypes.nil (@LinuxProcessSemantics.LinuxProcessSem.State.event))), (forall x_18 : (forall R' : (@LinuxProcessSemantics.Riscv.Prelude.bvmap 5%N (@stdpp.bitvector.definitions.bv 64%N)), (forall M' : (forall x_18 : (@stdpp.bitvector.definitions.bv 64%N), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 8%N))), (forall x_18 : (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P.P_stdio_defs.sw_post M su (@sc_f res) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.edenot E (@sc_bufp res)) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.edenot E (@sc_bufsz res)) M'), (forall x_19 : (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2Sound.SX2S.regs_ok (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.Env (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymRun.vals_ev (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 64%N) vals (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymDrive.junk_vals R'))) ebs) (@sc_sr res) R'), (forall x_20 : (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2Sound.SX2S.know_ok (@OSSVerify.mbedtls.fuzz_pkcs7.images.Plain.M.loaded_segments) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.Env (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymRun.vals_ev (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 64%N) vals (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymDrive.junk_vals R'))) ebs) M' (@sc_kn res)), (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BudgetWit.Rzb.realizes (@OSSVerify.mbedtls.fuzz_pkcs7.images.Plain.M.loaded_segments) (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.mkst (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.fx0) R' (@stdpp.bitvector.definitions.Z_to_bv 64%N (@sc_ret res)) M' (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom (@OSSVerify.mbedtls.fuzz_pkcs7.images.Plain.M.loaded_segments))) model) K)))))), (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BudgetWit.Rzb.realizes (@OSSVerify.mbedtls.fuzz_pkcs7.images.Plain.M.loaded_segments) (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.mkst (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.fx0) R (@stdpp.bitvector.definitions.Z_to_bv 64%N 254780%Z) M (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom (@OSSVerify.mbedtls.fuzz_pkcs7.images.Plain.M.loaded_segments))) model) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Shape.t_emit (@Corelib.Lists.ListDef.map (@stdpp.bitvector.definitions.bv 8%N) (@LinuxProcessSemantics.LinuxProcessSem.State.event) (@LinuxProcessSemantics.LinuxProcessSem.State.WriteEv (@stdpp.bitvector.definitions.Z_to_bv 64%N (@sc_fd res))) (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N) pending extra)) K)))))))))))))))))))))))))))))))))))))))
(* [comment removed for export] *).
Proof.
  intros vals ebs sr kn R M model res pending extra K E HR HK Hc.
  cbv beta delta [stdio_call] in Hc. cbv zeta in Hc.
  destruct (nth 10 sr (ELit 0)) as [f| | | | | | |] eqn:H10; try discriminate.
  destruct (lit_even_ret (nth 1 sr (ELit 0))) as [ret|] eqn:Hret; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 120) 4) as [[fd| | | | | | |]|] eqn:Hfd; try discriminate.
  destruct (kread RSEGS kn (ELit 0) (f + 40) 8) as [wpe|] eqn:Hwp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 56) 8) as [wbe|] eqn:Hwb; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 88) 8) as [bufp|] eqn:Hbufp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 96) 8) as [bufsz|] eqn:Hbufsz; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) 0x485e0 8) as [[cg| | | | | | |]|] eqn:Hcg; try discriminate.
  destruct (kread RSEGS kn (ELit 0) 0x79c30 8) as [canv|] eqn:Hcan; [|discriminate].
  destruct (split_lit (nth 2 sr (ELit 0))) as [qb k0] eqn:Hsq.
  destruct (kindex (is_kwr_cov qb (k0 - 112) 112) kn 0) as [j|] eqn:Hki; [|discriminate].
  destruct (base_range kn qb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
  match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  lazymatch type of Hc with Some ?x = Some _ => assert (Eres : res = x) by congruence end. clear Hc. subst res.
  cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn].
  intros Hwbwp Hlenp Hlene H30 Dw Ds Hsl Tw Ts Rpend Rextra Hfdlk Hrdr Hh Hlz HKnil HCONT.
  set (wb := bv_unsigned (edenot E wbe)) in *. set (wp := bv_unsigned (edenot E wpe)) in *.
  set (s := edenot E (nth 11 sr (ELit 0))) in *. set (l := edenot E (nth 12 sr (ELit 0))) in *.
  set (su := bv_unsigned (edenot E (nth 2 sr (ELit 0)))) in *.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hlen32]. apply andb_prop in Hcond as [Hcond Hkv]. apply andb_prop in Hcond as [Hcond Hsv].
  apply andb_prop in Hcond as [Hcond Vbufsz]. apply andb_prop in Hcond as [Hcond Vbufp].
  apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
  apply andb_prop in Hcond as [Hcond Hcgv]. apply andb_prop in Hcond as [Hcond Hfd12].
  apply andb_prop in Hcond as [Hf0 Hf232].
  apply Z.leb_le in Hf0. apply Z.leb_le in Hf232. apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'.
  apply Z.eqb_eq in Hcgv. apply Nat.eqb_eq in Hlen32.
  (* [comment removed for export] *)
  assert (Hretv : (ret mod 2 = 0 /\ 0 <= ret < two64)%Z).
  { unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
    destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool eqn:Hb; [|discriminate]. injection Hret as ->.
    apply andb_prop in Hb as [Hb Hb3]. apply andb_prop in Hb as [Hb1 Hb2].
    apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2. apply Z.ltb_lt in Hb3. lia. }
  assert (RG : forall n, (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (nth n sr (ELit 0))).
  { intros n Hn. rewrite (HR (Z_to_bv 5 (Z.of_nat n))), sr_get_nat by exact Hn. reflexivity. }
  assert (R1 : getr R 1 = Z_to_bv 64 ret).
  { replace (1%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 1)) by (apply bv_eq; reflexivity). rewrite RG by lia.
    unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
    destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool; [|discriminate]. injection Hret as ->. reflexivity. }
  assert (R10 : getr R 10 = Z_to_bv 64 f).
  { replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite RG by lia.
    rewrite H10. reflexivity. }
  assert (R2 : getr R 2 = edenot E (nth 2 sr (ELit 0))).
  { replace (2%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity). apply RG. lia. }
  assert (R11 : getr R 11 = s).
  { replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity). apply RG. lia. }
  assert (R12 : getr R 12 = l).
  { replace (12%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 12)) by (apply bv_eq; reflexivity). apply RG. lia. }
  set (sp := edenot E (nth 2 sr (ELit 0))) in *.
  pose proof (base_range_sound RSEGS E M kn qb blo bhi HK Hbr) as Hqbr.
  pose proof (split_lit_denot E (nth 2 sr (ELit 0)) qb k0 Hsq) as Hsqd. fold sp in Hsqd.
  assert (Hq : su = (bv_unsigned (edenot E qb) + k0)%Z).
  { subst su. rewrite Hsqd. apply u64_lit. lia. }
  pose proof (u64_range sp) as Hspr2. fold su in Hspr2.
  (* [comment removed for export] *)
  destruct (kindex_some _ _ _ _ Hki) as (KW & Hnth & HKW & _).
  destruct KW as [| | | | | |[cb ck] clen|]; try discriminate. cbn [is_kwr_cov] in HKW.
  apply andb_prop in HKW as [HKW Hc2]. apply andb_prop in HKW as [Hcb Hc1].
  apply expr_eqb_eq in Hcb. subst cb. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
  pose proof (kwr_store_ok RSEGS E M kn _ qb ck clen (k0 - 112) 112%nat HK Hnth Hc1 ltac:(cbn; lia)) as Wst.
  assert (Wst' : store_ok RSEGS M (Z_to_bv 64 (su - 112)) 112 = true).
  { unfold adenot, v_addi in Wst. cbn [a_base a_off] in Wst.
    replace (bv_unsigned (edenot E qb) + (k0 - 112))%Z with (su - 112)%Z in Wst by lia. exact Wst. }
  (* [comment removed for export] *)
  assert (FL : forall off n, (0 <= off)%Z -> (0 < n)%Z -> (off + n <= 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
  { intros off n A B C. apply flat_abs0; lia. }
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 120) 4 (ELit fd) HK Hfd ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rfd.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 40) 8 wpe HK Hwp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwp.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 56) 8 wbe HK Hwb ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwb.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 88) 8 bufp HK Hbufp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufp.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 96) 8 bufsz HK Hbufsz ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufsz.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x485e0 8 (ELit cg) HK Hcg ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcg.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x79c30 8 canv HK Hcan ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcan.
  rewrite adenot_lit0 in Rfd, Rwp, Rwb, Rbufp, Rbufsz, Rcg, Rcan.
  pose proof (u64_range (edenot E wpe)) as Hwpr. pose proof (u64_range (edenot E wbe)) as Hwbr.
  fold wp in Hwpr. fold wb in Hwbr.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0x3e33c) with (0x3e33c%bv : word) by (apply bv_eq; reflexivity).
  eapply (ref_stdio_write R M model su f wb wp fd s l (edenot E bufp) (edenot E bufsz) (edenot E canv) (Z_to_bv 64 ret)
            pending extra K).
  - rewrite R2. symmetry. apply Z_to_bv_bv_unsigned.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact R1.
  - lia.
  - lia.
  - exact Wst'.
  - lia.
  - lia.
  - constructor.
    + rewrite Rwp. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite Rwb. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite Rfd. cbn [edenot]. reflexivity.
    + exact Rbufp.
    + exact Rbufsz.
  - split; [|exact Rcan]. rewrite Rcg. cbn [edenot]. f_equal. f_equal. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64 in Hcgv. rewrite Hcgv. reflexivity.
  - apply orb_prop in Hfd12 as [H|H]; apply Z.eqb_eq in H; subst fd; lia.
  - exact Hfdlk.
  - exact Hrdr.
  - exact Hh.
  - exact Hlz.
  - lia.
  - lia.
  - exact Hlenp.
  - exact Hlene.
  - exact H30.
  - exact Dw.
  - exact Ds.
  - exact Hsl.
  - exact Tw.
  - exact Ts.
  - exact Rpend.
  - exact Rextra.
  - apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hretv; lia). lia.
  - exact HKnil.
  - (* [comment removed for export] *)
    intros R' M' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST.
    set (E' := Env (vals_ev (vals ++ junk_vals R')) ebs).
    assert (Hag : env_agree (length vals) E E') by apply vals_app_agree.
    apply HCONT; [exact HPOST| |].
    + (* [comment removed for export] *)
      assert (HRj : regs_ok E' (sr_after_call_j sr SC_KEPT (length vals)) R').
      { apply (regs_after_call vals ebs sr R R' SC_KEPT Hsv HR).
        - intros i Hi. unfold SC_KEPT in Hi. cbn [In] in Hi.
          destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
            (split; [lia|]);
            lazymatch goal with |- getr R' (Z_to_bv 5 (Z.of_nat ?kk)) = _ =>
              first [ replace (Z_to_bv 5 (Z.of_nat kk)) with (1%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G1, R1; reflexivity
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G2, R2; apply Z_to_bv_bv_unsigned
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact G3
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact G4
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (8%bv : bv 5) by (apply bv_eq; reflexivity); exact G8
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (9%bv : bv 5) by (apply bv_eq; reflexivity); exact G9
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (18%bv : bv 5) by (apply bv_eq; reflexivity); exact G18
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (19%bv : bv 5) by (apply bv_eq; reflexivity); exact G19
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (20%bv : bv 5) by (apply bv_eq; reflexivity); exact G20
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (21%bv : bv 5) by (apply bv_eq; reflexivity); exact G21
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (22%bv : bv 5) by (apply bv_eq; reflexivity); exact G22
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (23%bv : bv 5) by (apply bv_eq; reflexivity); exact G23
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (24%bv : bv 5) by (apply bv_eq; reflexivity); exact G24
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (25%bv : bv 5) by (apply bv_eq; reflexivity); exact G25
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (26%bv : bv 5) by (apply bv_eq; reflexivity); exact G26
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (27%bv : bv 5) by (apply bv_eq; reflexivity); exact G27 ]
            end.
        - unfold SC_KEPT. cbn [In]. lia. }
      apply (regs_ok_ext E' (sr_after_call_j sr SC_KEPT (length vals)) _ R');
        [ rewrite length_sr_upd by (rewrite length_sr_after_call_j; lia); reflexivity | | exact HRj ].
      intros i Hi. rewrite length_sr_after_call_j in Hi.
      destruct (Nat.eq_dec i 10) as [->|Hne].
      * rewrite nth_sr_upd_same by (rewrite length_sr_after_call_j; lia).
        unfold sr_after_call_j. rewrite nth_map_seq by lia. cbn [existsb SC_KEPT Nat.eqb orb].
        change (edenot E' (EVar (length vals + 10))) with (vals_ev (vals ++ junk_vals R') (length vals + 10)).
        rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite (nth_map_seq (fun i => getr R' (Z_to_bv 5 (Z.of_nat i)))) by lia.
        replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10.
        apply (edenot_agree (length vals)); [exact Hag|]. apply sr_vars_lt_nth. exact Hsv.
      * rewrite nth_sr_upd_other by lia. reflexivity.
    + (* [comment removed for export] *)
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      assert (HK' : know_ok RSEGS E' M kn) by (apply env_app_know; [exact Hkv | exact HK]).
      assert (HK0 : know_ok RSEGS E' M (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8)) by (apply kimg_cut_sound, kimg_cut_sound, HK').
      assert (HK3 : know_ok RSEGS E' M'
                (kn_frame (kn_frame (kn_frame (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8) qb (k0 - 112) 112)
                   (ELit 0) (f + 32) 16) (ELit 0) (f + 56) 8)).
      { assert (Eqb : edenot E' qb = edenot E qb).
        { symmetry. apply (edenot_agree (length vals)); [exact Hag|].
          apply (split_lit_vars (length vals) (nth 2 sr (ELit 0)) qb k0 Hsq). apply sr_vars_lt_nth. exact Hsv. }
        apply (know_ok_frame3 E' M M'); [exact HK0 | | apply flat_abs0; lia | apply flat_abs0; lia | | exact Pgrows].
        - unfold flat, estart. cbn [a_base a_off]. rewrite Eqb. lia.
        - intros x N1 N2 N3. apply Pagree.
          + unfold estart in N1. cbn [a_base a_off] in N1. rewrite Eqb in N1. lia.
          + unfold estart in N2. cbn [a_base a_off] in N2. rewrite u_lit0 in N2. lia.
          + unfold estart in N3. cbn [a_base a_off] in N3. rewrite u_lit0 in N3. lia. }
      assert (Xb : edenot E' bufp = edenot E bufp) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufp]).
      assert (Xs : edenot E' bufsz = edenot E bufsz) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufsz]).
      subst E'.
      repeat apply Forall_cons; [ | | | exact HK3]; cbn [kentry_ok]; (split; [lia|]); (split; [apply flat_abs0; lia|]); rewrite adenot_lit0.
      * rewrite mkAlu_denot. cbn [edenot]. fold E. rewrite alu_add, Xb, Xs. exact Pwend.
      * rewrite Xb. exact Pwpos.
      * rewrite Xb. exact Pwbase.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Theorem stdio_call_sound :
  (* plain text: new premise [Hrdr] after the fd one, the channel reader the revision's writev reads (recipes/channel-reader-premise.md) *)
  (forall vals : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 64%N)), (forall ebs : (forall x_ : (@Corelib.Init.Datatypes.nat), (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))), (forall sr : (@Corelib.Init.Datatypes.list (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.expr)), (forall kn : (@Corelib.Init.Datatypes.list (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.kentry)), (forall R : (@LinuxProcessSemantics.Riscv.Prelude.bvmap 5%N (@stdpp.bitvector.definitions.bv 64%N)), (forall M : (forall x_ : (@stdpp.bitvector.definitions.bv 64%N), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 8%N))), (forall model : (@LinuxProcessSemantics.LinuxProcessSem.State.Model), (forall res : (@stdio_res), (forall pending : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), (forall extra : (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)), (forall K : (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Shape.TSet), (let E : (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.env) := (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.Env (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymRun.vals_ev vals) ebs) in (forall x_ : (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2Sound.SX2S.regs_ok E sr R), (forall x_1 : (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2Sound.SX2S.know_ok (@OSSVerify.mbedtls.fuzz_pkcs7.images.Plain.M.loaded_segments) E M kn), (forall x_2 : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@stdio_res)) (@stdio_call (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 64%N) vals) sr kn) (@Corelib.Init.Datatypes.Some (@stdio_res) res)), (let wb : (@Corelib.Numbers.BinNums.Z) := (@stdpp.bitvector.definitions.bv_unsigned 64%N (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.edenot E (@sc_wb res))) in (let wp : (@Corelib.Numbers.BinNums.Z) := (@stdpp.bitvector.definitions.bv_unsigned 64%N (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.edenot E (@sc_wp res))) in (let s : (@stdpp.bitvector.definitions.bv 64%N) := (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.edenot E (@sc_s res)) in (let l : (@stdpp.bitvector.definitions.bv 64%N) := (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.edenot E (@sc_l res)) in (let su : (@Corelib.Numbers.BinNums.Z) := (@stdpp.bitvector.definitions.bv_unsigned 64%N (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.edenot E (@sc_sp res))) in (forall x_3 : (@Stdlib.ZArith.BinInt.Z.le wb wp), (forall x_4 : (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) (@Stdlib.ZArith.BinInt.Z.sub wp wb) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) pending))), (forall x_5 : (@Corelib.Init.Logic.eq (@Corelib.Numbers.BinNums.Z) (@stdpp.bitvector.definitions.bv_unsigned 64%N l) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) extra))), (forall x_6 : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) pending)) (@Stdlib.ZArith.BinInt.Z.of_nat (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) extra))) (@Stdlib.ZArith.BinInt.Z.pow 2%Z 30%Z)), (forall x_7 : (@Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le wp (@Stdlib.ZArith.BinInt.Z.sub su 112%Z)) (@Stdlib.ZArith.BinInt.Z.le su wb)), (forall x_8 : (@Corelib.Init.Logic.or (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N s) (@stdpp.bitvector.definitions.bv_unsigned 64%N l)) (@Stdlib.ZArith.BinInt.Z.sub su 112%Z)) (@Stdlib.ZArith.BinInt.Z.le su (@stdpp.bitvector.definitions.bv_unsigned 64%N s))), (forall x_9 : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N s) (@stdpp.bitvector.definitions.bv_unsigned 64%N l)) (@Stdlib.ZArith.BinInt.Z.pow 2%Z 64%Z)), (forall x_10 : (@Stdlib.ZArith.BinInt.Z.le wp 140737488355328%Z), (forall x_11 : (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.add (@stdpp.bitvector.definitions.bv_unsigned 64%N s) (@stdpp.bitvector.definitions.bv_unsigned 64%N l)) 140737488355328%Z), (forall x_12 : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.rdn (@OSSVerify.mbedtls.fuzz_pkcs7.images.Plain.M.loaded_segments) M (@stdpp.bitvector.definitions.Z_to_bv 64%N wb) (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) pending)) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) pending)), (forall x_13 : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N))) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.rdn (@OSSVerify.mbedtls.fuzz_pkcs7.images.Plain.M.loaded_segments) M s (@Corelib.Init.Datatypes.length (@stdpp.bitvector.definitions.bv 8%N) extra)) (@Corelib.Init.Datatypes.Some (@Corelib.Init.Datatypes.list (@stdpp.bitvector.definitions.bv 8%N)) extra)), (forall x_14 : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@LinuxProcessSemantics.LinuxProcessSem.State.FdEntry)) (@LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup (@LinuxProcessSemantics.LinuxProcessSem.State.m_fds model) (@stdpp.bitvector.definitions.Z_to_bv 64%N (@sc_fd res))) (@Corelib.Init.Datatypes.Some (@LinuxProcessSemantics.LinuxProcessSem.State.FdEntry) (@LinuxProcessSemantics.LinuxProcessSem.State.FdChannel (@stdpp.bitvector.definitions.Z_to_bv 64%N (@sc_fd res))))), (forall Hrdr : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.bool) (@LinuxProcessSemantics.LinuxProcessSem.State.m_channel_reader model) (@Corelib.Init.Datatypes.true)), (forall x_15 : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 64%N)) (@LinuxProcessSemantics.LinuxProcessSem.State.m_halted model) (@Corelib.Init.Datatypes.None (@stdpp.bitvector.definitions.bv 64%N))), (forall x_16 : (@Corelib.Init.Logic.eq (@Corelib.Init.Datatypes.list (@Corelib.Init.Datatypes.prod (@stdpp.bitvector.definitions.bv 64%N) (@stdpp.bitvector.definitions.bv 64%N))) (@LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy model) (@Corelib.Init.Datatypes.nil (@Corelib.Init.Datatypes.prod (@stdpp.bitvector.definitions.bv 64%N) (@stdpp.bitvector.definitions.bv 64%N)))), (forall x_17 : (K (@Corelib.Init.Datatypes.nil (@LinuxProcessSemantics.LinuxProcessSem.State.event))), (forall x_18 : (forall R' : (@LinuxProcessSemantics.Riscv.Prelude.bvmap 5%N (@stdpp.bitvector.definitions.bv 64%N)), (forall M' : (forall x_18 : (@stdpp.bitvector.definitions.bv 64%N), (@Corelib.Init.Datatypes.option (@stdpp.bitvector.definitions.bv 8%N))), (forall x_18 : (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2Sound.SX2S.regs_ok (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.Env (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymRun.vals_ev (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 64%N) vals (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymDrive.junk_vals R'))) ebs) (@sc_sr res) R'), (forall x_19 : (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2Sound.SX2S.know_ok (@OSSVerify.mbedtls.fuzz_pkcs7.images.Plain.M.loaded_segments) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymExec2.SX2.Env (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymRun.vals_ev (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 64%N) vals (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB.SymDrive.junk_vals R'))) ebs) M' (@sc_kn res)), (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BudgetWit.Rzb.realizes (@OSSVerify.mbedtls.fuzz_pkcs7.images.Plain.M.loaded_segments) (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.mkst (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.fx0) R' (@stdpp.bitvector.definitions.Z_to_bv 64%N (@sc_ret res)) M' (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom (@OSSVerify.mbedtls.fuzz_pkcs7.images.Plain.M.loaded_segments))) model) K))))), (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BudgetWit.Rzb.realizes (@OSSVerify.mbedtls.fuzz_pkcs7.images.Plain.M.loaded_segments) (@LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.mkst (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.fx0) R (@stdpp.bitvector.definitions.Z_to_bv 64%N 254780%Z) M (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom (@OSSVerify.mbedtls.fuzz_pkcs7.images.Plain.M.loaded_segments))) model) (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.Shape.t_emit (@Corelib.Lists.ListDef.map (@stdpp.bitvector.definitions.bv 8%N) (@LinuxProcessSemantics.LinuxProcessSem.State.event) (@LinuxProcessSemantics.LinuxProcessSem.State.WriteEv (@stdpp.bitvector.definitions.Z_to_bv 64%N (@sc_fd res))) (@Corelib.Init.Datatypes.app (@stdpp.bitvector.definitions.bv 8%N) pending extra)) K)))))))))))))))))))))))))))))))))))))))
(* [comment removed for export] *).
Proof.
  intros vals ebs sr kn R M model res pending extra K E HR HK Hc wb wp s l su.
  intros H1 H2 H3 H5 H6 H7 H8 H8a H8b H9 H10 H11 Hrdr H12 H13 H14 HCONT.
  eapply (stdio_call_sound_fr vals ebs sr kn R M model res pending extra K HR HK Hc); try eassumption.
  intros R' M' _ HR' HK'. apply HCONT; assumption.
Qed.
