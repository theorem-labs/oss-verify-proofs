(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK.
Import ListNotations.
Import AX2K.
Unset Nia Cache. Unset Nra Cache. Import AX2SK. Import APK. Import APSK.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanNodesIfaceK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanNodesIfaceK.Iface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymRun3K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "stdpp.bitvector.definitions."], [["0A"; "1Some"; "1bool"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2iff"; "0E"; "0E'"; "0FS0"; "0FULL"; "0FULL'"; "0LIMIT"]; ["3Fs"; "4Model"; "4m_fs"; "5bvmap"; "0R"; "0R'"; "6OBL_mmap2"; "7acs"; "7is_ecall_at"; "7node_mmap2"; "7nxt"; "7pc"; "8cfg_of"; "8cs_ok"; "9env"; ":env_agree"]; [";TSet"; "<srealizes"; "0SEGS"; "0SINV"; "0TB"; "0argH"; "0cs"; "0csa"; "0csb"; "0model"; "0model'"; "0nx0"; "0scfg"; "0split"; "=bv"]]).
Section Iface.
Variable SEGS : list Segment.
Variable scfg : SpuriousCfg.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Definition OBL_mmap2 : Prop := forall split : bool, mm2_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 (node_mmap2 A nx0 LIMIT split).
Definition OBL_mmapin : Prop := forall hole : bool, mm3_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 (node_mmapin A LIMIT hole).
Definition OBL_mprotect2 : Prop := mm2_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 (node_mprotect2 A LIMIT).
Definition OBL_brk2 : Prop := brk2_stmt SEGS scfg A nx0 LIMIT SINV argH FS0.
Definition OBL_sys : Prop := forall y : snode, sys_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 y.
Definition OBL_exit : Prop := exit_stmt SEGS scfg A LIMIT SINV argH FS0.
Definition OBL_all : Prop := OBL_mmap2 /\ OBL_mmapin /\ OBL_mprotect2 /\ OBL_brk2 /\ OBL_sys /\ OBL_exit.
Lemma OBL_mmap2_unfold : ltac2:(TCodec.tc2 tcn__AsanNodesIfaceK "SD&9&F'2'G'N&Cy5'Q>yR0%211%5241'3y8%611%311p061'A&Q0'MvQ2v0v?vQ3vQ5v<r5r8r4r3r2%<;;:987654321'8&Hr9%22?1(6%53Q221'5%12Q3Q3%L11&IvQ;r;r:%45H3G21(1(4%14Q<Q<>E%32:1%B3:51'7&Or<%23<1J&Jr?%211%6315N%8251%Q9;Q8Q7Q6Q5Q4Q3Q24Q0ON&@&B%11Q2%21E%Q13421'Q1vQ<&Lr6&KrA%211%55QE41Q?Q=%84QF71Op0:1p0@1p0B1pRFQM1pNQO1pQ<R51pHR<1r=%O3Q91QGr@%N11%Q2314QJ%Q4241%J1Q3%QI3LJ1%H4R6GAQ5p021p0Q01p061pRFR=1pNR?1pQ<RE1pHRL1%L1@r7%Q05R@R22R91%Q34RAQ21Q0p051p0F1p0QF1p0R41p0R;1pR:RI1pRDRK1pLRM1pQ:S31pFS:1pRBS<1pR@S=1pR>S>1pRLS@1%SC2SB1").
Proof. unfold OBL_mmap2, mm2_stmt. tauto. Qed.
End Iface.
