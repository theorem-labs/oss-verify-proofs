(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel DSLayout BitsLib BuildTreeLib TreesRod.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees TreeModel SendModel GenBitlenModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6 DS6 TreesRod6 Callee6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

End FXG.
Abbreviation BR6 := (BR s6_segs 168672 168704 168736).
Abbreviation BRx6 := (BRx s6_segs 168672 168704 168736).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition call_frame (F : franges) (mem : word -> option byte) (S PB PBL sp K : Z) : Prop :=
  K <= sp <= 2 ^ 63 /\ sub_franges F (sp - K) K /\ mapped mem (sp - K) K
  /\ (S + dsl_SIZE <= sp - K \/ sp <= S) /\ (PB + PBL <= sp - K \/ sp <= PB).


Definition BT_CLOB : list reg := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition BT_FRAME : Z := 144.
Definition A6_BUILD_TREE : Z := 0x1b94c.

Definition build_tree_run6 (SAFE : deflate_state -> tree_id -> Prop) : Prop :=
  forall (F : franges) (mem0 mem : word -> option byte) (S : Z) (p : ds_ptrs) (PBL : Z)
         (ds : deflate_state) (ra : word) (sp : Z) (t : tree_id) (regs : bvmap 5 word),
    memset_run6 ->
    BRH F S p PBL -> sub_franges F S dsl_SIZE -> ret_ok ra ->
    BR6 F mem0 S p PBL mem ds -> trees_rod_clear6 mem -> SAFE ds t ->
    call_frame F mem S (p_pending_buf p) PBL sp BT_FRAME ->
    getr regs 10 = zw S -> getr regs 11 = zw (S + dsc_off t) -> getr regs 2 = zw sp -> getr regs 1 = ra ->
    exists R m',
      msteps s6_segs (mkst regs (zw A6_BUILD_TREE) mem s6_rom) (mkst R ra m' s6_rom)
      /\ BR6 F mem0 S p PBL m' (build_tree ds t)
      /\ trees_rod_clear6 m'
      /\ getr R 2 = getr regs 2
      /\ (forall r : reg, reg_in r BT_CLOB = false -> getr R r = getr regs r).


Definition FB_CLOB : list reg := [10; 11; 12; 13; 14; 15]%bv.
Definition A6_TR_FLUSH_BITS : Z := 0x1ad94.

Definition tr_flush_bits_run6 : Prop :=
  forall (F : franges) (mem0 mem : word -> option byte) (S : Z) (p : ds_ptrs) (PBL : Z)
         (ds : deflate_state) (ra : word) (regs : bvmap 5 word),
    BRH F S p PBL -> ret_ok ra -> BR6 F mem0 S p PBL mem ds -> BINV PBL ds ->
    ds_pending (tr_flush_bits ds) <= PBL ->
    getr regs 10 = zw S -> getr regs 1 = ra ->
    exists R m',
      msteps s6_segs (mkst regs (zw A6_TR_FLUSH_BITS) mem s6_rom) (mkst R ra m' s6_rom)
      /\ BR6 F mem0 S p PBL m' (tr_flush_bits ds)
      /\ (forall r : reg, reg_in r FB_CLOB = false -> getr R r = getr regs r).


Definition TFB_CLOB : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.

Definition TFB_FRAME : Z := 208.
Definition A6_TR_FLUSH_BLOCK : Z := 0x1af98.

Definition fb_src (F : franges) (mem : word -> option byte) (p : ds_ptrs) (ds : deflate_state)
           (buf : option Z) (bufp stored_len : Z) : Prop :=
  match buf with
  | None => bufp = 0
  | Some off =>
      bufp = p_window p + off /\ 0 < bufp < 2 ^ 64
      /\ (stored_len <> 0 ->
          0 <= off /\ off + stored_len <= arr_len (ds_window ds)
          /\ cells s6_segs mem (p_window p) 1 1 (arr_len (ds_window ds)) (arr_get (ds_window ds))
          /\ (forall j, off <= j < off + stored_len -> 0 <= arr_get (ds_window ds) j < 256)
          /\ 0 <= p_window p /\ p_window p + arr_len (ds_window ds) <= 2 ^ 63
          /\ disj_franges F (p_window p) (arr_len (ds_window ds)))
  end.

Definition fb_strm (F : franges) (mem : word -> option byte) (S : Z) (p : ds_ptrs) (PBL sp : Z)
           (ds : deflate_state) : Prop :=
  cell s6_segs mem (p_strm p + 88) 4 (cs_data_type (ds_strm ds))
  /\ 0 <= p_strm p /\ p_strm p + 112 <= 2 ^ 63
  /\ sub_franges F (p_strm p + 88) 4 /\ mapped mem (p_strm p + 88) 4
  /\ (S + dsl_SIZE <= p_strm p + 88 \/ p_strm p + 92 <= S)
  /\ (p_pending_buf p + PBL <= p_strm p + 88 \/ p_strm p + 92 <= p_pending_buf p)
  /\ (sp <= p_strm p + 88 \/ p_strm p + 92 <= sp - TFB_FRAME).

Definition tr_flush_block_run6
           (SAFE : deflate_state -> option Z -> Z -> Z -> Prop) : Prop :=
  forall (F : franges) (mem0 mem : word -> option byte) (S : Z) (p : ds_ptrs) (PBL : Z)
         (ds : deflate_state) (ra : word) (regs : bvmap 5 word)
         (sp : Z) (buf : option Z) (bufp stored_len last : Z),
    memset_run6 -> memcpy_run6 ->
    BRH F S p PBL -> sub_franges F S dsl_SIZE -> ret_ok ra ->
    BR6 F mem0 S p PBL mem ds -> BINV PBL ds -> trees_rod_clear6 mem ->
    SAFE ds buf stored_len last ->
    0 <= last <= 1 -> 0 <= stored_len < 2 ^ 32 ->
    call_frame F mem S (p_pending_buf p) PBL sp TFB_FRAME ->
    fb_src F mem p ds buf bufp stored_len -> fb_strm F mem S p PBL sp ds ->
    getr regs 10 = zw S -> getr regs 11 = zw bufp -> getr regs 12 = zw stored_len ->
    getr regs 13 = zw last -> getr regs 2 = zw sp -> getr regs 1 = ra ->
    exists R m',
      msteps s6_segs (mkst regs (zw A6_TR_FLUSH_BLOCK) mem s6_rom) (mkst R ra m' s6_rom)
      /\ BR6 F mem0 S p PBL m' (tr_flush_block ds buf stored_len last)
      /\ cell s6_segs m' (p_strm p + 88) 4 (cs_data_type (ds_strm (tr_flush_block ds buf stored_len last)))
      /\ trees_rod_clear6 m'
      /\ (forall r : reg, reg_in r TFB_CLOB = false -> getr R r = getr regs r).
End FXG.
