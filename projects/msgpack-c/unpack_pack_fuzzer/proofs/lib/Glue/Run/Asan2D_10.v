(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan Notation PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgAsan ItabAsan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.AsanU Require UnivAsan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2D Require Import T_Asan2D B_00.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StdioWrite DrvShape DrvLib DrvEdges.
Import ListNotations W64 Val Mem FI St Step Plan PlanS SW DrvShape DrvLib DrvEdges.
Unset Lia Cache.

Definition LAY : layout := Layout X22 [X19].
Definition CDFLT : swcert := SWC T_DRV2 0%uint63 0 [] [].
Ltac sw_explore := repeat (apply Forall_cons || apply Forall_nil); (split; [|split]); try (vm_compute; reflexivity);
  intros HH; vm_compute in HH; try discriminate HH; vm_compute; reflexivity.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Import Asan2D_1 Asan2D_2 Asan2D_3 Asan2D_4 Asan2D_5 Asan2D_6 Asan2D_7 Asan2D_8 Asan2D_9.
Unset Nia Cache. Unset Nra Cache.

Lemma N_T_OPEN_ (R : drun) (H : hyps R) : NODE SEGS R (t_st T_OPEN_) (DR R (SALT (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)) (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD.
  apply (node_open_dir SEGS R FAMD (t_st T_OPEN_) _ (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))) T_Asan2D.FORK_OPEN_ ltac:(vm_compute; reflexivity)).
  - exact (N_R_OPEN__0 R H).
  - apply Forall_cons; [exact (N_R_OPEN__1 R H)|]; apply Forall_cons; [exact (N_R_OPEN__2 R H)|]; apply Forall_cons; [exact (N_R_OPEN__3 R H)|]; apply Forall_cons; [exact (N_R_OPEN__4 R H)|]; apply Forall_nil.
Qed.

Lemma N_T_DRV2 (R : drun) (H : hyps R) : NODE SEGS R T_DRV2 (DR R (SALT (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)) (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD.
  apply (node_cert SEGS R C_DRV.CTX C_DRV.PLAN T_DRV2 C_DRV.OBLS (DR R (SALT (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)) (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)))) [(100%uint63, T_OPEN_)] [] C_DRV.WF ITAB_ok (contracts_ok_of SEGS R C_DRV.CTX HC) C_DRV.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_OPEN_ R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

