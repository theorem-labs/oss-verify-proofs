(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the point inside segment LH of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530) where the three header cases join (0x866bc), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s22.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (a segment statement: from a point of the function to its return, under the entry's context). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep
  CmdObj CmdRo CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* 0x866bc: the header of the pass's message is read (the cases r = 1, r = 2 and r >= 3, 0x86658 .. 0x866b8 and the
   out-of-line 0x86888 .. 0x868b0, 0x86a64 .. 0x86a78, join here); next UBSan's test of p + len, the three shadow
   cells of g_rec's words, g_rec.state and g_rec.host_settings, g_rec.refuse, rec_ncodes, g_rec.code and the call of
   send_message *)
Definition LO_M1 : Z := 0x18c.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* a1 = the flags byte, s3 = the message's first byte, s4 = its length, s6 = the bytes left after the header; the
   rest as at the head of the pass (LT_LH_stmt with r > 0) *)
Definition LH_M1_stmt (m : nat) : Prop :=
  forall cx ly S W regs mem md k acc (r : Z) (R : rstate) (O : list (Z * Z)) (q : Z),
  lt_base B MT cx -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 -> lt_body B cx ly S W regs mem md k m ->
  0 < r <= x_n cx ->
  getr regs 11 = w64 (SlotSpec.hbyte (lt_hdr (x_pl cx) (x_n cx) r) 0) ->
  getr regs 19 = w64 (x_p cx + (x_n cx - r) + SlotSpec.hdr_n r) ->
  getr regs 20 = w64 (lt_len (x_pl cx) (x_n cx) r) ->
  getr regs 22 = w64 (r - SlotSpec.hdr_n r) ->
  lt_rec B cx ly S W mem R O q [] ->
  lt_bud MT cx S k acc (ev_from (32 - m) R (x_rest cx r)) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + LO_M1)) mem (seg_rom SEGS)) md) (lt_post B MT cx).

End e.
End f.
End d.
