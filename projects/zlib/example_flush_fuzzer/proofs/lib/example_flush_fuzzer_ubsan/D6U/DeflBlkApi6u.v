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
  SymEx2Expr SymEx2 SymEx2Tac MemRel DSLayout ZSLayout FillWinMem RomRead TreesRod.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees TreeModel DeflateLz DeflateBlk FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6 DS6 Callee6 TreesRod6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Export DeflBlkApi6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u DS6u Callee6u TreesRod6u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Definition zsl_outA6u (mem : word -> option byte) (zp : zs_ptrs) (st : cstrm) : Prop :=
  cells s6u_segs mem (zp_out zp) 1 1 (Z.of_nat (length (cs_out_rev st)))
        (fun i => nth (Z.to_nat i) (cs_output st) 0).

Definition ZR6u (mem : word -> option byte) (S : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) : Prop :=
  ds6u_scalars mem S p ds /\ ds6u_arrays mem S ds /\ tree_lens ds
  /\ ds6u_windowA mem p ds /\ ds6u_prevA mem p ds /\ ds6u_headA mem p ds /\ ds6u_pendA mem p ds
  /\ zsl_scalars s6u_segs mem (p_strm p) zp S (ds_strm ds)
  /\ zsl_input s6u_segs mem zp (ds_strm ds)
  /\ zsl_outA6u mem zp (ds_strm ds).

Definition got6u_clear (mem : word -> option byte) : Prop := rom_clear mem 0x2c2b0 0x2c3c8.
(* 1.4 UBSan: deflate_slow takes _length_code / _dist_code by auipc + add, so the 1.3.1 GOT pair at 0x2c260
   (and its chk_rom lemma got6u_ok) is gone; got6u_clear is kept as a harmless read-only range of the image *)

Definition rod6u (mem : word -> option byte) : Prop := trees_rod_clear6u mem /\ got6u_clear mem.

Record ZRH6u (K : Z) (mem : word -> option byte) (S sp : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) : Prop := {
  zrh_sp : K <= sp <= 2 ^ 63;
  zrh_rng : Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) (zr_regions K S sp p zp ds);
  zrh_in : zp_in zp + arr_len (cs_input (ds_strm ds)) < 2 ^ 63;
  zrh_W : 0 < p_window p;
  zrh_HD : 2 <= p_head p;
  zrh_PV : 2 <= p_prev p;
  zrh_map : Forall (fun r => mapped mem (fst r) (snd r)) (ZRF K S sp p zp ds);
  zrh_apart : apart_all (zr_regions K S sp p zp ds);
  zrh_rod : rod6u mem;
  zrh_img : forall x, in_franges (ZRF K S sp p zp ds) x -> IMG6U_LO <= x < IMG6U_HI -> False;
  zrh_O : 0 < zp_out zp;
  zrh_S8 : S mod 8 = 0;
  zrh_S1 : 0 < S;
  zrh_strm1 : 0 < p_strm p;
  zrh_strm8 : p_strm p mod 8 = 0;
  zrh_HD2 : p_head p mod 2 = 0;
  zrh_PV2 : p_prev p mod 2 = 0;
  zrh_PB1 : 0 < p_pending_buf p;
  zrh_I : 0 < zp_in zp }.

Definition DSLOW_FRAME6u : Z := 464.
Definition DSLOW_FR6u : Z := 128.


Definition lz_contract6u (ROM : (word -> option byte) -> Prop) (entry K : Z)
           (f : deflate_state -> Z -> deflate_state * block_state)
           (SAFE : deflate_state -> Z -> Prop) : Prop :=
  forall (mem : word -> option byte) (S : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state)
         (flush : Z) (ra : word) (sp : Z) (regs : bvmap 5 word),
    ZRH6u K mem S sp p zp ds -> ret_ok ra -> ZR6u mem S p zp ds -> ROM mem -> SAFE ds flush ->
    0 <= flush <= 5 ->
    getr regs 10 = zw S -> getr regs 11 = zw flush -> getr regs 2 = zw sp -> getr regs 1 = ra ->
    exists R m',
      msteps s6u_segs (mkst regs (zw entry) mem s6u_rom) (mkst R ra m' s6u_rom)
      /\ ZR6u m' S p zp (fst (f ds flush))
      /\ getr R 10 = zw (bs_code (snd (f ds flush)))
      /\ getr R 2 = zw sp
      /\ (forall r : reg, reg_in r LZ_CLOB = false -> getr R r = getr regs r)
      /\ agree_out (ZRFo K S sp p zp ds (Z.of_nat (length (cs_out_rev (ds_strm (fst (f ds flush))))))) mem m'
      /\ rod6u m'
      /\ ROM m'
      /\ (forall x, mem x <> None -> m' x <> None)
      /\ lzk ds (fst (f ds flush)).

Definition A6U_DEFLATE_SLOW : Z := 0x19cf0.

Definition deflate_slow_run6u (ROM : (word -> option byte) -> Prop) (SAFE : deflate_state -> Z -> Prop) : Prop :=
  lz_contract6u ROM A6U_DEFLATE_SLOW DSLOW_FRAME6u deflate_slow SAFE.

Lemma cell_write_same_at : forall M a b (w : nat) v,
  b = a -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  cell s6u_segs (wbytes M (zw b) (Z_to_le_bytes w v)) a w v.
Proof. intros M a b w v -> Ha Hw. apply cell_write_same; assumption. Qed.


End FXG.
