(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel DSLayout BitsLib BuildTreeLib TreesRod.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees TreeModel SendModel GenBitlenModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u DS6u TreesRod6u Callee6u TreesApi6u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Record UBT (S : Z) (p : ds_ptrs) : Prop := UBT_ {
  ubt_S8 : S mod 8 = 0;
  ubt_S1 : 0 < S;
  ubt_pb1 : 0 < p_pending_buf p;
  ubt_win1 : 0 < p_window p;
  ubt_strm1 : 0 < p_strm p;
  ubt_strm8 : p_strm p mod 8 = 0 }.

End FXG.
Ltac open_ubt H :=
  pose proof (ubt_S8 _ _ H) as US8; pose proof (ubt_S1 _ _ H) as US1;
  pose proof (ubt_pb1 _ _ H) as UPB1; pose proof (ubt_win1 _ _ H) as UWIN1;
  pose proof (ubt_strm1 _ _ H) as USTRM1; pose proof (ubt_strm8 _ _ H) as USTRM8.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Definition FB_CLOB6u : list reg := [10; 11; 12; 13; 14; 15; 16]%bv.
Definition A6U_TR_FLUSH_BITS : Z := 0x1bd28.
Definition tr_flush_bits_run6u : Prop :=
  forall (F : franges) (mem0 mem : word -> option byte) (S : Z) (p : ds_ptrs) (PBL : Z)
         (ds : deflate_state) (ra : word) (regs : bvmap 5 word),
    BRH F S p PBL -> ret_ok ra -> BR6u F mem0 S p PBL mem ds -> BINV PBL ds ->
    ds_pending (tr_flush_bits ds) <= PBL -> UBT S p ->
    getr regs 10 = zw S -> getr regs 1 = ra ->
    exists R m',
      msteps s6u_segs (mkst regs (zw A6U_TR_FLUSH_BITS) mem s6u_rom) (mkst R ra m' s6u_rom)
      /\ BR6u F mem0 S p PBL m' (tr_flush_bits ds)
      /\ (forall r : reg, reg_in r FB_CLOB6u = false -> getr R r = getr regs r).


Definition IB_CLOB6u : list reg := [10; 11; 12; 13; 14; 15; 16; 17]%bv.
Definition TI_CLOB6u : list reg := [10; 11; 12; 13; 14; 15; 16; 17]%bv.
Definition A6U_INIT_BLOCK : Z := 0x1b73c.
Definition A6U_TR_INIT : Z := 0x1b6d0.

End FXG.
Abbreviation dsR_vals6u := (dsl_vals 180992 181024 181056).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition dvals6u (ds : deflate_state) (p : ds_ptrs) (S : Z) (d : Z * Z * Z * Z * Z * Z) : list Z :=
  let '(d1, d2, d3, d4, d5, d6) := d in
  list_upd (list_upd (list_upd (list_upd (list_upd (list_upd (dsR_vals6u ds p S) 37 d1) 39 d2) 40 d3) 42 d4) 43 d5) 45 d6.

Definition BRi6u (F : franges) (mem0 : word -> option byte) (S : Z) (p : ds_ptrs) (PBL : Z)
           (m : word -> option byte) (s : deflate_state) : Prop :=
  (exists d, fields s6u_segs m S dsl_layout (dvals6u s p S d))
  /\ dsl_arrays s6u_segs m S s
  /\ tree_lens s
  /\ cells s6u_segs m (p_pending_buf p) 1 1 PBL (arr_get (ds_pending_buf s))
  /\ arr_len (ds_pending_buf s) = PBL
  /\ agree_out F mem0 m
  /\ mapped m S dsl_SIZE /\ mapped m (p_pending_buf p) PBL
  /\ (forall x, mem0 x <> None -> m x <> None).


Definition init_block_run6u : Prop :=
  forall (F : franges) (mem0 mem : word -> option byte) (S : Z) (p : ds_ptrs) (PBL : Z)
         (ds : deflate_state) (ra : word) (regs : bvmap 5 word),
    BRH F S p PBL -> sub_franges F S dsl_SIZE -> ret_ok ra -> BR6u F mem0 S p PBL mem ds -> UBT S p ->
    getr regs 10 = zw S -> getr regs 1 = ra ->
    exists R m',
      msteps s6u_segs (mkst regs (zw A6U_INIT_BLOCK) mem s6u_rom) (mkst R ra m' s6u_rom)
      /\ BR6u F mem0 S p PBL m' (init_block ds)
      /\ (forall r : reg, reg_in r IB_CLOB6u = false -> getr R r = getr regs r).

Definition tr_init_run6u : Prop :=
  forall (F : franges) (mem0 mem : word -> option byte) (S : Z) (p : ds_ptrs) (PBL : Z)
         (ds : deflate_state) (ra : word) (regs : bvmap 5 word),
    BRH F S p PBL -> sub_franges F S dsl_SIZE -> ret_ok ra -> BRi6u F mem0 S p PBL mem ds -> UBT S p ->
    getr regs 10 = zw S -> getr regs 1 = ra ->
    exists R m',
      msteps s6u_segs (mkst regs (zw A6U_TR_INIT) mem s6u_rom) (mkst R ra m' s6u_rom)
      /\ BR6u F mem0 S p PBL m' (tr_init ds)
      /\ (forall r : reg, reg_in r TI_CLOB6u = false -> getr R r = getr regs r).


Definition SB_CLOB6u : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition SB_FRAME6u : Z := 48.
Definition A6U_TR_STORED_BLOCK : Z := 0x1b9e4.
Definition tsb_src6u (F : franges) (mem : word -> option byte) (p : ds_ptrs) (ds : deflate_state)
           (buf : option Z) (bufp stored_len : Z) : Prop :=
  stored_len <> 0 ->
  exists off, buf = Some off /\ bufp = p_window p + off /\ 0 <= off
    /\ off + stored_len <= arr_len (ds_window ds)
    /\ cells s6u_segs mem (p_window p) 1 1 (arr_len (ds_window ds)) (arr_get (ds_window ds))
    /\ (forall j, off <= j < off + stored_len -> 0 <= arr_get (ds_window ds) j < 256)
    /\ 0 <= p_window p /\ p_window p + arr_len (ds_window ds) <= 2 ^ 63
    /\ disj_franges F (p_window p) (arr_len (ds_window ds)).

Definition tr_stored_block_run6u : Prop :=
  forall (F : franges) (mem0 mem : word -> option byte) (S : Z) (p : ds_ptrs) (PBL : Z)
         (ds : deflate_state) (ra : word) (regs : bvmap 5 word)
         (sp : Z) (buf : option Z) (bufp stored_len last : Z),
    memcpy_run6u ->
    BRH F S p PBL -> sub_franges F (S + 5944) 4 -> ret_ok ra -> BR6u F mem0 S p PBL mem ds -> BINV PBL ds ->
    ds_pending (tr_stored_block ds buf stored_len last) <= PBL ->
    0 <= last <= 1 -> 0 <= stored_len < 2 ^ 32 ->
    call_frame F mem S (p_pending_buf p) PBL sp SB_FRAME6u ->
    tsb_src6u F mem p ds buf bufp stored_len -> UBT S p ->
    getr regs 10 = zw S -> getr regs 11 = zw bufp -> getr regs 12 = zw stored_len ->
    getr regs 13 = zw last -> getr regs 2 = zw sp -> getr regs 1 = ra ->
    exists R m',
      msteps s6u_segs (mkst regs (zw A6U_TR_STORED_BLOCK) mem s6u_rom) (mkst R ra m' s6u_rom)
      /\ BR6u F mem0 S p PBL m' (tr_stored_block ds buf stored_len last)
      /\ (forall r : reg, reg_in r SB_CLOB6u = false -> getr R r = getr regs r).


Definition TFB_CLOB6u : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.

Definition TFB_FRAME6u : Z := 336.
Definition A6U_TR_FLUSH_BLOCK : Z := 0x1bff0.
Definition fb_src6u (F : franges) (mem : word -> option byte) (p : ds_ptrs) (ds : deflate_state)
           (buf : option Z) (bufp stored_len : Z) : Prop :=
  match buf with
  | None => bufp = 0
  | Some off =>
      bufp = p_window p + off /\ 0 < bufp < 2 ^ 64
      /\ (stored_len <> 0 ->
          0 <= off /\ off + stored_len <= arr_len (ds_window ds)
          /\ cells s6u_segs mem (p_window p) 1 1 (arr_len (ds_window ds)) (arr_get (ds_window ds))
          /\ (forall j, off <= j < off + stored_len -> 0 <= arr_get (ds_window ds) j < 256)
          /\ 0 <= p_window p /\ p_window p + arr_len (ds_window ds) <= 2 ^ 63
          /\ disj_franges F (p_window p) (arr_len (ds_window ds)))
  end.

Definition fb_strm6u (F : franges) (mem : word -> option byte) (S : Z) (p : ds_ptrs) (PBL sp : Z)
           (ds : deflate_state) : Prop :=
  cell s6u_segs mem (p_strm p + 88) 4 (cs_data_type (ds_strm ds))
  /\ 0 <= p_strm p /\ p_strm p + 112 <= 2 ^ 63
  /\ sub_franges F (p_strm p + 88) 4 /\ mapped mem (p_strm p + 88) 4
  /\ (S + dsl_SIZE <= p_strm p + 88 \/ p_strm p + 92 <= S)
  /\ (p_pending_buf p + PBL <= p_strm p + 88 \/ p_strm p + 92 <= p_pending_buf p)
  /\ (sp <= p_strm p + 88 \/ p_strm p + 92 <= sp - TFB_FRAME6u).

Definition tr_flush_block_run6u
           (SAFE : deflate_state -> option Z -> Z -> Z -> Prop) : Prop :=
  forall (F : franges) (mem0 mem : word -> option byte) (S : Z) (p : ds_ptrs) (PBL : Z)
         (ds : deflate_state) (ra : word) (regs : bvmap 5 word)
         (sp : Z) (buf : option Z) (bufp stored_len last : Z),
    memset_run6u -> memcpy_run6u ->
    BRH F S p PBL -> sub_franges F S dsl_SIZE -> ret_ok ra ->
    BR6u F mem0 S p PBL mem ds -> BINV PBL ds -> trees_rod_clear6u mem ->
    SAFE ds buf stored_len last ->
    0 <= last <= 1 -> 0 <= stored_len < 2 ^ 32 ->
    call_frame F mem S (p_pending_buf p) PBL sp TFB_FRAME6u ->
    fb_src6u F mem p ds buf bufp stored_len -> fb_strm6u F mem S p PBL sp ds -> UBT S p ->
    getr regs 10 = zw S -> getr regs 11 = zw bufp -> getr regs 12 = zw stored_len ->
    getr regs 13 = zw last -> getr regs 2 = zw sp -> getr regs 1 = ra ->
    exists R m',
      msteps s6u_segs (mkst regs (zw A6U_TR_FLUSH_BLOCK) mem s6u_rom) (mkst R ra m' s6u_rom)
      /\ BR6u F mem0 S p PBL m' (tr_flush_block ds buf stored_len last)
      /\ cell s6u_segs m' (p_strm p + 88) 4 (cs_data_type (ds_strm (tr_flush_block ds buf stored_len last)))
      /\ trees_rod_clear6u m'
      /\ (forall r : reg, reg_in r TFB_CLOB6u = false -> getr R r = getr regs r).
End FXG.
