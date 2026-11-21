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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Definition zsl_outA (mem : word -> option byte) (zp : zs_ptrs) (st : cstrm) : Prop :=
  cells s6_segs mem (zp_out zp) 1 1 (Z.of_nat (length (cs_out_rev st)))
        (fun i => nth (Z.to_nat i) (cs_output st) 0).

Definition ZR6 (mem : word -> option byte) (S : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) : Prop :=
  ds6_scalars mem S p ds /\ ds6_arrays mem S ds /\ tree_lens ds
  /\ ds6_windowA mem p ds /\ ds6_prevA mem p ds /\ ds6_headA mem p ds /\ ds6_pendA mem p ds
  /\ zsl_scalars s6_segs mem (p_strm p) zp S (ds_strm ds)
  /\ zsl_input s6_segs mem zp (ds_strm ds)
  /\ zsl_outA mem zp (ds_strm ds).

Definition zr_regions (K S sp : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) : list (Z * Z) :=
  [(sp - K, K); (S, ds6_SIZE); (p_window p, 2 * ds_w_size ds); (p_prev p, 2 * ds_w_size ds);
   (p_head p, 2 * ds_hash_size ds); (p_pending_buf p, ds_lit_bufsize ds * 4); (p_strm p, zsl_SIZE);
   (zp_out zp, Z.of_nat (length (cs_out_rev (ds_strm ds))) + cs_avail_out (ds_strm ds));
   (zp_in zp, arr_len (cs_input (ds_strm ds)))].

Definition ZRF (K S sp : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) : franges :=
  [(sp - K, K); (S, ds6_SIZE); (p_window p, 2 * ds_w_size ds); (p_prev p, 2 * ds_w_size ds);
   (p_head p, 2 * ds_hash_size ds); (p_pending_buf p, ds_lit_bufsize ds * 4); (p_strm p, zsl_SIZE);
   (zp_out zp, Z.of_nat (length (cs_out_rev (ds_strm ds))) + cs_avail_out (ds_strm ds))].

Definition ZRFo (K S sp : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) (olen' : Z) : franges :=
  [(sp - K, K); (S, ds6_SIZE); (p_window p, 2 * ds_w_size ds); (p_prev p, 2 * ds_w_size ds);
   (p_head p, 2 * ds_hash_size ds); (p_pending_buf p, ds_lit_bufsize ds * 4); (p_strm p, zsl_SIZE);
   (zp_out zp, olen')].

Definition got6_clear (mem : word -> option byte) : Prop := rom_clear mem 0x292c8 0x293a8.

(* zlib 1.4: _length_code (0x11ce0) / _dist_code (0x11ae0) are file-static and reached pc-relatively (auipc + addi),
   so the two GOT slots at 0x29270 hold other words now (0x104bb, 0x10592). This is the 1.4 content; the deflate_slow
   blocks that read the tables through these slots (DeflSlow6_5 / 5b) move to the pc-relative form in their unit. *)
Lemma got6_ok : chk_rom s6_segs 0x292c8 (tab64_byte (fun i => if i =? 0 then 0x104bb else 0x10592)) 16 = true.
Proof. vm_compute. reflexivity. Qed.

Definition rod6 (mem : word -> option byte) : Prop := trees_rod_clear6 mem /\ got6_clear mem.

Record ZRH6 (K : Z) (mem : word -> option byte) (S sp : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) : Prop := {
  zrh_sp : K <= sp <= 2 ^ 63;
  zrh_rng : Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) (zr_regions K S sp p zp ds);
  zrh_in : zp_in zp + arr_len (cs_input (ds_strm ds)) < 2 ^ 63;
  zrh_W : 0 < p_window p;
  zrh_HD : 2 <= p_head p;
  zrh_PV : 2 <= p_prev p;
  zrh_map : Forall (fun r => mapped mem (fst r) (snd r)) (ZRF K S sp p zp ds);
  zrh_apart : apart_all (zr_regions K S sp p zp ds);
  zrh_rod : rod6 mem;
  zrh_img : forall x, in_franges (ZRF K S sp p zp ds) x -> IMG6_LO <= x < IMG6_HI -> False;
  zrh_O : 0 < zp_out zp }.

Definition bs_code (b : block_state) : Z :=
  match b with need_more => 0 | block_done => 1 | finish_started => 2 | finish_done => 3 end.

Definition LZ_CLOB : list reg := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.

Definition DSLOW_FRAME6 : Z := 336.

Definition lzk (ds X : deflate_state) : Prop :=
  ds_w_size X = ds_w_size ds /\ ds_hash_size X = ds_hash_size ds /\ ds_lit_bufsize X = ds_lit_bufsize ds
  /\ arr_len (ds_window X) = 2 * ds_w_size ds /\ arr_len (ds_prev X) = ds_w_size ds /\ arr_len (ds_head X) = ds_hash_size ds
  /\ arr_len (ds_pending_buf X) = ds_lit_bufsize ds * 4
  /\ cs_input (ds_strm X) = cs_input (ds_strm ds)
  /\ Z.of_nat (length (cs_out_rev (ds_strm X))) + cs_avail_out (ds_strm X)
     = Z.of_nat (length (cs_out_rev (ds_strm ds))) + cs_avail_out (ds_strm ds)
  /\ 0 <= cs_avail_out (ds_strm X)
  /\ Z.of_nat (length (cs_out_rev (ds_strm ds))) <= Z.of_nat (length (cs_out_rev (ds_strm X))).


Definition lz_contract6 (ROM : (word -> option byte) -> Prop) (entry K : Z)
           (f : deflate_state -> Z -> deflate_state * block_state)
           (SAFE : deflate_state -> Z -> Prop) : Prop :=
  forall (mem : word -> option byte) (S : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state)
         (flush : Z) (ra : word) (sp : Z) (regs : bvmap 5 word),
    ZRH6 K mem S sp p zp ds -> ret_ok ra -> ZR6 mem S p zp ds -> ROM mem -> SAFE ds flush ->
    0 <= flush <= 5 ->
    getr regs 10 = zw S -> getr regs 11 = zw flush -> getr regs 2 = zw sp -> getr regs 1 = ra ->
    exists R m',
      msteps s6_segs (mkst regs (zw entry) mem s6_rom) (mkst R ra m' s6_rom)
      /\ ZR6 m' S p zp (fst (f ds flush))
      /\ getr R 10 = zw (bs_code (snd (f ds flush)))
      /\ getr R 2 = zw sp
      /\ (forall r : reg, reg_in r LZ_CLOB = false -> getr R r = getr regs r)
      /\ agree_out (ZRFo K S sp p zp ds (Z.of_nat (length (cs_out_rev (ds_strm (fst (f ds flush))))))) mem m'
      /\ rod6 m'
      /\ ROM m'
      /\ (forall x, mem x <> None -> m' x <> None)
      /\ lzk ds (fst (f ds flush)).

Definition A6_DEFLATE_SLOW : Z := 0x19558.

Definition deflate_slow_run6 (ROM : (word -> option byte) -> Prop) (SAFE : deflate_state -> Z -> Prop) : Prop :=
  lz_contract6 ROM A6_DEFLATE_SLOW DSLOW_FRAME6 deflate_slow SAFE.


End FXG.
