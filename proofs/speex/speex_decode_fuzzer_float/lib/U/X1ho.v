(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Definition A_nb_decode : Z := 0x20b08.
Definition A_speex_bits_remaining : Z := 0x1ce94.
Definition A_speex_bits_unpack_unsigned : Z := 0x1cc58.
Definition A_speex_bits_advance : Z := 0x1ce10.
Definition A_speex_inband_handler : Z := 0x2a0a4.
Definition A_speex_default_user_handler : Z := 0x2a1a4.
Definition A_speex_std_stereo_request_handler : Z := 0x1d280.
Definition A_lsp_unquant_lbr : Z := 0x2b174.
Definition A_lsp_unquant_nb : Z := 0x2aaac.
Definition A_lsp_unquant_high : Z := 0x2b6c0.
Definition A_pitch_unquant_3tap : Z := 0x26a40.
Definition A_forced_pitch_unquant : Z := 0x27230.
Definition A_split_cb_shape_sign_unquant : Z := 0x29c74.
Definition A_noise_codebook_unquant : Z := 0x29fec.
Definition A_multicomb : Z := 0x246ac.
Definition A_lsp_interpolate : Z := 0x27f0c.
Definition A_lsp_to_lpc : Z := 0x27bb8.
Definition A_bw_lpc : Z := 0x22bec.
Definition A_sanitize_values32 : Z := 0x22c7c.
Definition A_highpass : Z := 0x22cfc.
Definition A_signal_mul : Z := 0x22ea8.
Definition A_compute_rms16 : Z := 0x23044.
Definition A_iir_mem16 : Z := 0x232bc.
Definition A_exp : Z := 0x339b0.
Definition A_fprintf : Z := 0x34aac.
Definition A_memcpy : Z := 0x39c5c.
Definition A_memmove : Z := 0x3a060.
Definition A_memset : Z := 0x3a1dc.

Definition NB_MODE_PTR : Z := 0x3b7c8.
Definition NB_MODE_STRUCT : Z := 0x3b6f8.
Definition NB_SUBMODES_PTR : Z := 0x3b718.
Definition NB_RSTDERR : Z := 0x3d110.
Definition NB_GOT_STDERR : Z := 0x3c020.
Definition NB_GOT_LSP_HIGH : Z := 0x3c040.
Definition NB_GOT_LSP_NB : Z := 0x3c060.
Definition NB_STDERR_VAR : Z := 0x3bfd0.
Definition NB_FMT_notify : Z := 0x103f0.
Definition A_MSG_INVALID_MODE : Z := 0x1038c.
Definition A_MSG_MORE_THAN_TWO_WB : Z := 0x10491.
Definition A_wb_skip_table : Z := 0x10cb0.
Definition NB_GLOBALS_TOP : Z := 0x6e000.
Definition NB_FPRINTF_DEPTH : Z := 5632.
Definition NB_GOT_SSP : Z := 0x3c0d0.
Definition NB_SSP_GUARD : Z := 0x6d6b8.

Definition LSPQ_DEPTH : Z := 128.
Definition LTP_DEPTH : Z := 256.
Definition INNOV_DEPTH : Z := 4352.
Definition INBAND_DEPTH : Z := 256.
Definition USERH_DEPTH : Z := 128.
Definition MULTICOMB_DEPTH : Z := 4352.
Definition LSP2LPC_DEPTH : Z := 4352.
Definition EXP_DEPTH : Z := 16.
Definition LSPI_DEPTH : Z := 32.
Definition HIGHPASS_DEPTH : Z := 176.
Definition IIR_DEPTH : Z := 96.

Definition NB_FRAME : Z := 912.
Definition NB_DECODE_DEPTH : Z := NB_FRAME + NB_FPRINTF_DEPTH.

Record iclob := ICL { c_t0 : word; c_t1 : word; c_t2 : word; c_a1 : word; c_a2 : word; c_a3 : word; c_a4 : word;
c_a5 : word; c_a6 : word; c_a7 : word; c_t3 : word; c_t4 : word; c_t5 : word; c_t6 : word }.
Definition callR (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 : word) (k : iclob) : bvmap 5 word :=
mkR ra sp gp tp (c_t0 k) (c_t1 k) (c_t2 k) s0 s1 a0 (c_a1 k) (c_a2 k) (c_a3 k) (c_a4 k) (c_a5 k) (c_a6 k) (c_a7 k)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (c_t3 k) (c_t4 k) (c_t5 k) (c_t6 k).

Definition fs_regs : list Z := [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition fs_kept (F F' : bvmap 5 word) : Prop :=
forall r, In r fs_regs -> reg_get F' (Z_to_bv 5 r) = reg_get F (Z_to_bv 5 r).

Definition apart (p n q k : Z) : Prop := p + n <= q \/ q + k <= p.

Definition lsp_entry (k : lsp_kind) : Z :=
match k with LspUnquantLbr => A_lsp_unquant_lbr | LspUnquantNb => A_lsp_unquant_nb | LspUnquantHigh => A_lsp_unquant_high end.
Definition lsp_order (k : lsp_kind) : Z := match k with LspUnquantHigh => 8 | _ => 10 end.
Definition ltp_entry (k : ltp_kind) : Z :=
match k with LtpForcedPitchUnquant => A_forced_pitch_unquant | LtpPitchUnquant3tap _ => A_pitch_unquant_3tap end.
Definition innov_entry (k : innov_kind) : Z :=
match k with InnovNoiseCodebookUnquant => A_noise_codebook_unquant | InnovSplitCbShapeSignUnquant _ => A_split_cb_shape_sign_unquant end.
Definition gain_cdbk_addr (g : gain_cdbk_id) : Z := match g with GainCdbkNb => 0x12588 | GainCdbkLbr => 0x11f28 end.
Definition shape_cb_addr (t : shape_cb_id) : Z :=
match t with
| Exc_5_256_table => 0x128c8 | Exc_5_64_table => 0x12788 | Exc_8_128_table => 0x12188 | Exc_10_32_table => 0x12048
| Exc_10_16_table => 0x11fa8 | Exc_20_32_table => 0x12dc8 | Hexc_table => 0x134ec | Hexc_10_32_table => 0x133ac
end.

Definition ltp_par_cells (p : ltp_params) : list cell :=
[C8 (Z_to_bv 64 (gain_cdbk_addr (ltp_gain_cdbk p))); C4 (Z_to_bv 64 (ltp_gain_bits p)); C4 (Z_to_bv 64 (ltp_pitch_bits p))].

Definition scb_par_cells (p : split_cb_params) : list cell :=
[C4 (Z_to_bv 64 (scb_subvect_size p)); C4 (Z_to_bv 64 (scb_nb_subvect p)); C8 (Z_to_bv 64 (shape_cb_addr (scb_shape_cb p)));
C4 (Z_to_bv 64 (scb_shape_bits p)); C4 (Z_to_bv 64 (scb_have_sign p))].

Record smrec := SMR {
smr_sm : submode;
smr_ptr : Z;
smr_lsp_quant : Z; smr_ltp_quant : Z; smr_innov_quant : Z;
smr_ltp_par : Z;
smr_innov_par : Z;
smr_comb_gain : Z }.
Definition smrec_cells (r : smrec) : list cell :=
let sm := smr_sm r in
[C4 (Z_to_bv 64 (sm_lbr_pitch sm)); C4 (Z_to_bv 64 (sm_forced_pitch_gain sm));
C4 (Z_to_bv 64 (sm_have_subframe_gain sm)); C4 (Z_to_bv 64 (sm_double_codebook sm));
C8 (Z_to_bv 64 (smr_lsp_quant r)); C8 (Z_to_bv 64 (lsp_entry (sm_lsp_unquant sm)));
C8 (Z_to_bv 64 (smr_ltp_quant r));
C8 (Z_to_bv 64 (match sm_ltp_unquant sm with Some k => ltp_entry k | None => 0 end));
C8 (Z_to_bv 64 (smr_ltp_par r));
C8 (Z_to_bv 64 (smr_innov_quant r));
C8 (Z_to_bv 64 (match sm_innovation_unquant sm with Some k => innov_entry k | None => 0 end));
C8 (Z_to_bv 64 (smr_innov_par r));
C4 (Z_to_bv 64 (smr_comb_gain r)); C4 (Z_to_bv 64 (sm_bits_per_frame sm))].

Definition nb_smrec1 := SMR nb_submode1 0x3b828 0x2ae98 0x26f34 0x29ee4 0       0       0xbf800000.
Definition nb_smrec2 := SMR nb_submode2 0x3b880 0x2ae98 0x25734 0x280ec 0x3bae8 0x3baf8 0x3f19999a.
Definition nb_smrec3 := SMR nb_submode3 0x3b8d8 0x2ae98 0x25734 0x280ec 0x3bb10 0x3bb20 0x3f0ccccd.
Definition nb_smrec4 := SMR nb_submode4 0x3b930 0x2ae98 0x25734 0x280ec 0x3bb38 0x3bb48 0x3ee66666.
Definition nb_smrec5 := SMR nb_submode5 0x3b988 0x2a1f4 0x25734 0x280ec 0x3bb60 0x3bb70 0x3e800000.
Definition nb_smrec6 := SMR nb_submode6 0x3b9e0 0x2a1f4 0x25734 0x280ec 0x3bb60 0x3bb88 0x3e19999a.
Definition nb_smrec7 := SMR nb_submode7 0x3ba38 0x2a1f4 0x25734 0x280ec 0x3bb60 0x3bb70 0x3d4ccccd.
Definition nb_smrec8 := SMR nb_submode8 0x3ba90 0x2ae98 0x26f34 0x280ec 0       0x3bba0 0x3f000000.
Definition nb_smrecs : list smrec := [nb_smrec1; nb_smrec2; nb_smrec3; nb_smrec4; nb_smrec5; nb_smrec6; nb_smrec7; nb_smrec8].

Definition nb_submode_ptrs : list Z := 0 :: map smr_ptr nb_smrecs ++ [0; 0; 0; 0; 0; 0; 0].
Definition smrec_at (m : Z) : option smrec := if m <? 1 then None else nth_error nb_smrecs (Z.to_nat (m - 1)).

Definition lsp_cdbk_got (m : mem) : Prop :=
ro_cells rsegs m NB_GOT_LSP_HIGH [C8 (Z_to_bv 64 0x11b28); C8 (Z_to_bv 64 0x11d28)]
/\ ro_cells rsegs m NB_GOT_LSP_NB [C8 (Z_to_bv 64 0x113a8); C8 (Z_to_bv 64 0x11628); C8 (Z_to_bv 64 0x11768);
C8 (Z_to_bv 64 0x118a8); C8 (Z_to_bv 64 0x119e8)].

Definition nb_tables (m : mem) : Prop :=
u8ro rsegs m NB_SUBMODES_PTR (u64s (map (Z_to_bv 64) nb_submode_ptrs))
/\ (forall r, In r nb_smrecs -> ro_cells rsegs m (smr_ptr r) (smrec_cells r))
/\ (forall r p, In r nb_smrecs -> sm_ltp_unquant (smr_sm r) = Some (LtpPitchUnquant3tap p) ->
ro_cells rsegs m (smr_ltp_par r) (ltp_par_cells p))
/\ (forall r p, In r nb_smrecs -> sm_innovation_unquant (smr_sm r) = Some (InnovSplitCbShapeSignUnquant p) ->
ro_cells rsegs m (smr_innov_par r) (scb_par_cells p))
/\ ro_cells rsegs m NB_GOT_STDERR [C8 (Z_to_bv 64 NB_STDERR_VAR)]
/\ ro_cells rsegs m NB_STDERR_VAR [C8 (Z_to_bv 64 NB_RSTDERR)]
/\ lsp_cdbk_got m.

Definition NB_TABLES_LO : Z := 0x3b6f8.
Definition NB_TABLES_HI : Z := 0x3c088.

Section Pure.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.
Definition ub b (n : Z) : bits_st ptr := snd (speex_bits_unpack_unsigned b n).
Definition uv b (n : Z) : Z := fst (speex_bits_unpack_unsigned b n).

Definition user_handler_bits b : bits_st ptr := speex_bits_advance (ub b 4) (5 + 8 * uv b 4).
Definition stereo_handler_bits b : bits_st ptr := ub (ub (ub b 1) 5) 2.
Definition inband_bits (stereo_cb : bool) b : bits_st ptr :=
let id := uv b 4 in let b1 := ub b 4 in
if stereo_cb && (id =? SPEEX_INBAND_STEREO) then stereo_handler_bits b1
else speex_bits_advance b1 (inband_skip_bits id).
Definition lsp_bits (k : lsp_kind) b : bits_st ptr :=
match k with
| LspUnquantLbr => ub (ub (ub b 6) 6) 6
| LspUnquantNb => ub (ub (ub (ub (ub b 6) 6) 6) 6) 6
| LspUnquantHigh => ub (ub b 6) 6
end.

Definition ltp3_pitch (p : ltp_params) (start : Z) b : Z := uv b (ltp_pitch_bits p) + start.
Definition ltp3_gain_index (p : ltp_params) b : Z := uv (ub b (ltp_pitch_bits p)) (ltp_gain_bits p).
Definition ltp3_bits (p : ltp_params) b : bits_st ptr := ub (ub b (ltp_pitch_bits p)) (ltp_gain_bits p).
Definition ltp_bits (k : ltp_kind) b : bits_st ptr :=
match k with LtpForcedPitchUnquant => b | LtpPitchUnquant3tap p => ltp3_bits p b end.
Definition ltp_pitch (k : ltp_kind) (start : Z) b : Z :=
match k with LtpForcedPitchUnquant => start | LtpPitchUnquant3tap p => ltp3_pitch p start b end.

Definition ltp_pitch_span (k : ltp_kind) : Z :=
match k with LtpForcedPitchUnquant => 0 | LtpPitchUnquant3tap p => 2 ^ ltp_pitch_bits p - 1 end.
Fixpoint scb_bits (n : nat) (have_sign shape_bits : Z) b : bits_st ptr :=
match n with
| O => b
| S n' => let b1 := if negb (have_sign =? 0) then ub b 1 else b in
scb_bits n' have_sign shape_bits (ub b1 shape_bits)
end.
Definition innov_bits (k : innov_kind) b : bits_st ptr :=
match k with
| InnovNoiseCodebookUnquant => b
| InnovSplitCbShapeSignUnquant p => scb_bits (Z.to_nat (scb_nb_subvect p)) (scb_have_sign p) (scb_shape_bits p) b
end.
End Pure.

Section Stmts.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

Definition mm_bytes (bs : list byte) (i j n : nat) : list byte :=
firstn i bs ++ firstn n (skipn j bs) ++ skipn (i + n) bs.
Definition memmove_post (B : Z) (bs : list byte) (d s n : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
fun ms' => exists (k : iclob) (m' : mem),
ms' = MS (callR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) k) F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(d, d + n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' B [CB (length bs) (mm_bytes bs (Z.to_nat (d - B)) (Z.to_nat (s - B)) (Z.to_nat n))].
Definition memmove_stmt : Prop :=
forall (B : Z) (bs : list byte) (d s n : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells rsegs m B [CB (length bs) bs] ->
B <= d -> d + n <= B + Z.of_nat (length bs) -> B <= s -> s + n <= B + Z.of_nat (length bs) -> 0 <= n ->
d <= s ->
B + Z.of_nat (length bs) < 2^63 ->
a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 n ->
mem_inv rsegs m ->
evt rsegs (memmove_post B bs d s n ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_memmove) fc None m (seg_rom rsegs)).

Definition exp_post (lo : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (rv : word) (k : iclob) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (callR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv k) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp).
Definition exp_stmt : Prop :=
forall (lo : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
stk rsegs m lo (bv_unsigned sp) -> lo + EXP_DEPTH <= bv_unsigned sp ->
mem_inv rsegs m -> frm0 fc ->
evt rsegs (exp_post lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_exp) fc None m (seg_rom rsegs)).

Definition lsp_unquant_post (k : lsp_kind) (A D : Z) b (qlsp lo : Z)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (rv : word) (kk : iclob) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ws : list word),
ms' = MS (callR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv kk) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (qlsp, qlsp + 4 * lsp_order k); (A, A + BITS_SIZEOF)] m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' qlsp (f32 ws) /\ length ws = Z.to_nat (lsp_order k)
/\ bits_rep rsegs m' A D (lsp_bits k b) /\ bits_ok (lsp_bits k b).
Definition lsp_unquant_stmt (k : lsp_kind) : Prop :=
forall (A D : Z) b (qlsp : Z) (old : list word) (lo : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
bits_rep rsegs m A D b -> bits_ok b -> lsp_cdbk_got m ->
rw_cells rsegs m qlsp (f32 old) -> length old = Z.to_nat (lsp_order k) ->
stk rsegs m lo (bv_unsigned sp) -> lo + LSPQ_DEPTH <= bv_unsigned sp -> NB_GLOBALS_TOP <= lo ->
NB_GLOBALS_TOP <= qlsp -> NB_GLOBALS_TOP <= A ->
apart qlsp (4 * lsp_order k) lo (bv_unsigned sp - lo) ->
apart A BITS_SIZEOF lo (bv_unsigned sp - lo) -> apart D (sb_buf_size b) lo (bv_unsigned sp - lo) ->
apart qlsp (4 * lsp_order k) A BITS_SIZEOF -> apart qlsp (4 * lsp_order k) D (sb_buf_size b) ->
a0 = Z_to_bv 64 qlsp -> a1 = Z_to_bv 64 (lsp_order k) -> a2 = Z_to_bv 64 A ->
mem_inv rsegs m -> frm0 fc ->
0 < qlsp -> qlsp mod 4 = 0 ->
evt rsegs (lsp_unquant_post k A D b qlsp lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (lsp_entry k)) fc None m (seg_rom rsegs)).

Definition ltp_unquant_post (k : ltp_kind) (A D : Z) b (EB exc e32 pv pg start lo : Z) (neb : nat)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (rv : word) (kk : iclob) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (eb' e32' pg' : list word),
ms' = MS (callR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv kk) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (exc, exc + 160); (e32, e32 + 160); (pv, pv + 4); (pg, pg + 12); (A, A + BITS_SIZEOF)] m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' EB (f32 eb') /\ length eb' = neb
/\ rw_cells rsegs m' e32 (f32 e32') /\ length e32' = 40%nat
/\ rw_cells rsegs m' pv [C4 (Z_to_bv 64 (ltp_pitch k start b))]
/\ rw_cells rsegs m' pg (f32 pg') /\ length pg' = 3%nat
/\ bits_rep rsegs m' A D (ltp_bits k b) /\ bits_ok (ltp_bits k b).
Definition ltp_unquant_stmt (k : ltp_kind) : Prop :=
forall (A D : Z) b (EB exc e32 pv pg start fin PAR off lo : Z) (eb e32s pgs : list word) (opv stk8 : word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
bits_rep rsegs m A D b -> bits_ok b ->
rw_cells rsegs m EB (f32 eb) -> EB + 4 * 290 <= exc -> exc + 160 <= EB + 4 * Z.of_nat (length eb) -> (exc - EB) mod 4 = 0 ->
rw_cells rsegs m e32 (f32 e32s) -> length e32s = 40%nat ->
rw_cells rsegs m pv [C4 opv] ->
rw_cells rsegs m pg (f32 pgs) -> length pgs = 3%nat ->
(match k with LtpPitchUnquant3tap p => ro_cells rsegs m PAR (ltp_par_cells p) | LtpForcedPitchUnquant => True end) ->
PAR + 16 <= NB_GLOBALS_TOP -> NB_GLOBALS_TOP <= A ->
rw_cells rsegs m (bv_unsigned sp) [C8 (Z_to_bv 64 A); C8 stk8; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 off); C8 (Z_to_bv 64 0)] ->
17 <= start -> start + ltp_pitch_span k <= 144 -> start <= fin <= 144 -> 0 <= off <= 120 ->
stk rsegs m lo (bv_unsigned sp) -> lo + LTP_DEPTH <= bv_unsigned sp -> NB_GLOBALS_TOP <= lo ->

apart EB (4 * Z.of_nat (length eb)) lo (bv_unsigned sp - lo) -> apart e32 160 lo (bv_unsigned sp - lo) ->
apart pv 4 lo (bv_unsigned sp - lo) -> apart pg 12 lo (bv_unsigned sp - lo) ->
apart A BITS_SIZEOF lo (bv_unsigned sp - lo) -> apart D (sb_buf_size b) lo (bv_unsigned sp - lo) ->
apart EB (4 * Z.of_nat (length eb)) e32 160 -> apart EB (4 * Z.of_nat (length eb)) pv 4 -> apart EB (4 * Z.of_nat (length eb)) pg 12 ->
apart EB (4 * Z.of_nat (length eb)) A BITS_SIZEOF -> apart EB (4 * Z.of_nat (length eb)) D (sb_buf_size b) ->
apart e32 160 pv 4 -> apart e32 160 pg 12 -> apart e32 160 A BITS_SIZEOF -> apart e32 160 D (sb_buf_size b) ->
apart pv 4 pg 12 -> apart pv 4 A BITS_SIZEOF -> apart pv 4 D (sb_buf_size b) ->
apart pg 12 A BITS_SIZEOF -> apart pg 12 D (sb_buf_size b) ->
exc mod 4 = 0 -> e32 mod 4 = 0 -> 0 < e32 -> pv mod 4 = 0 -> 0 < pv -> pg mod 4 = 0 -> 0 < pg ->
(match k with LtpPitchUnquant3tap _ => PAR mod 8 = 0 /\ 0 < PAR /\ apart A BITS_SIZEOF (bv_unsigned sp) 40 | LtpForcedPitchUnquant => True end) ->
a0 = Z_to_bv 64 exc -> a1 = Z_to_bv 64 e32 -> a2 = Z_to_bv 64 start -> a3 = Z_to_bv 64 fin ->
a4 = Z_to_bv 64 PAR -> a5 = Z_to_bv 64 40 -> a6 = Z_to_bv 64 pv -> a7 = Z_to_bv 64 pg ->
mem_inv rsegs m -> frm0 fc ->
evt rsegs (ltp_unquant_post k A D b EB exc e32 pv pg start lo (length eb) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (ltp_entry k)) fc None m (seg_rom rsegs)).

Definition innov_unquant_post (k : innov_kind) (A D : Z) b (inn seedp lo : Z)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (rv : word) (kk : iclob) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (is' : list word) (seed' : word),
ms' = MS (callR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv kk) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (inn, inn + 160); (seedp, seedp + 4); (A, A + BITS_SIZEOF)] m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' inn (f32 is') /\ length is' = 40%nat
/\ rw_cells rsegs m' seedp [C4 seed']
/\ bits_rep rsegs m' A D (innov_bits k b) /\ bits_ok (innov_bits k b).
Definition innov_unquant_stmt (k : innov_kind) : Prop :=
forall (A D : Z) b (inn seedp PAR lo : Z) (is0 : list word) (seed0 stk8 : word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
bits_rep rsegs m A D b -> bits_ok b ->
rw_cells rsegs m inn (f32 is0) -> length is0 = 40%nat ->
rw_cells rsegs m seedp [C4 seed0] ->
(match k with InnovSplitCbShapeSignUnquant p => ro_cells rsegs m PAR (scb_par_cells p) | InnovNoiseCodebookUnquant => True end) ->
PAR + 24 <= NB_GLOBALS_TOP -> NB_GLOBALS_TOP <= A ->
stk rsegs m lo (bv_unsigned sp) -> lo + INNOV_DEPTH <= bv_unsigned sp -> NB_GLOBALS_TOP <= lo -> bv_unsigned sp < 2^63 ->
apart inn 160 lo (bv_unsigned sp - lo) -> apart seedp 4 lo (bv_unsigned sp - lo) ->
apart A BITS_SIZEOF lo (bv_unsigned sp - lo) -> apart D (sb_buf_size b) lo (bv_unsigned sp - lo) ->
apart inn 160 seedp 4 -> apart inn 160 A BITS_SIZEOF -> apart inn 160 D (sb_buf_size b) ->
apart seedp 4 A BITS_SIZEOF -> apart seedp 4 D (sb_buf_size b) ->
inn mod 4 = 0 -> 0 < inn ->
(match k with InnovNoiseCodebookUnquant => seedp mod 4 = 0 /\ 0 < seedp | InnovSplitCbShapeSignUnquant _ => PAR mod 8 = 0 /\ 0 < PAR end) ->
a0 = Z_to_bv 64 inn -> a1 = Z_to_bv 64 PAR -> a2 = Z_to_bv 64 40 -> a3 = Z_to_bv 64 A -> a4 = stk8 -> a5 = Z_to_bv 64 seedp ->
mem_inv rsegs m -> frm0 fc ->
evt rsegs (innov_unquant_post k A D b inn seedp lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (innov_entry k)) fc None m (seg_rom rsegs)).

Definition inband_post (sc : bool) (A D : Z) b (STEREO lo : Z)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (kk : iclob) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (sws' : list word),
ms' = MS (callR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) kk) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (A, A + BITS_SIZEOF); (STEREO, STEREO + 8)] m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' STEREO (f32 sws') /\ length sws' = 2%nat
/\ bits_rep rsegs m' A D (inband_bits sc b) /\ bits_ok (inband_bits sc b).
Definition inband_handler_stmt : Prop :=
forall (sc : bool) (A D : Z) b (CBA ST STEREO lo : Z) (js : list (list byte * list byte)) (sws : list word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
bits_rep rsegs m A D b -> bits_ok b ->
rw_cells rsegs m CBA (cbs_cells 16 A_speex_std_stereo_request_handler STEREO sc js) ->
length js = 16%nat -> Forall (fun p => length (fst p) = 8%nat /\ length (snd p) = 16%nat) js ->
rw_cells rsegs m STEREO (f32 sws) -> length sws = 2%nat ->
stk rsegs m lo (bv_unsigned sp) -> lo + INBAND_DEPTH <= bv_unsigned sp -> NB_GLOBALS_TOP <= lo ->
apart CBA 640 lo (bv_unsigned sp - lo) -> apart STEREO 8 lo (bv_unsigned sp - lo) ->
apart A BITS_SIZEOF lo (bv_unsigned sp - lo) -> apart D (sb_buf_size b) lo (bv_unsigned sp - lo) ->
apart CBA 640 A BITS_SIZEOF -> apart CBA 640 STEREO 8 -> apart STEREO 8 A BITS_SIZEOF -> apart STEREO 8 D (sb_buf_size b) ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 CBA -> a2 = Z_to_bv 64 ST ->
mem_inv rsegs m -> frm0 fc ->
0 < CBA -> CBA mod 8 = 0 -> 0 < STEREO -> STEREO mod 4 = 0 ->
evt rsegs (inband_post sc A D b STEREO lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_inband_handler) fc None m (seg_rom rsegs)).

Definition user_handler_post (A D : Z) b (lo : Z)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (kk : iclob) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (callR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) kk) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (A, A + BITS_SIZEOF)] m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp)
/\ bits_rep rsegs m' A D (user_handler_bits b) /\ bits_ok (user_handler_bits b).
Definition user_handler_stmt : Prop :=
forall (A D : Z) b (ST lo : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
bits_rep rsegs m A D b -> bits_ok b ->
stk rsegs m lo (bv_unsigned sp) -> lo + USERH_DEPTH <= bv_unsigned sp -> NB_GLOBALS_TOP <= lo ->
apart A BITS_SIZEOF lo (bv_unsigned sp - lo) -> apart D (sb_buf_size b) lo (bv_unsigned sp - lo) ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 ST -> a2 = Z_to_bv 64 0 ->
mem_inv rsegs m -> frm0 fc ->
evt rsegs (user_handler_post A D b lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_default_user_handler) fc None m (seg_rom rsegs)).

Definition multicomb_post (ne lo : Z)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (rv : word) (kk : iclob) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ns' : list word),
ms' = MS (callR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv kk) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (ne, ne + 320)] m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' ne (f32 ns') /\ length ns' = 80%nat.
Definition multicomb_stmt : Prop :=
forall (EB eoff ne AK pitch lo : Z) (eb ns ak : list word) (stk8 : word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells rsegs m EB (f32 eb) -> length eb = 500%nat -> (eoff = 294 \/ eoff = 374) ->
rw_cells rsegs m ne (f32 ns) -> length ns = 80%nat ->
rw_cells rsegs m AK (f32 ak) -> length ak = 10%nat ->
17 <= pitch <= 144 ->
stk rsegs m lo (bv_unsigned sp) -> lo + MULTICOMB_DEPTH <= bv_unsigned sp -> NB_GLOBALS_TOP <= lo -> bv_unsigned sp < 2^63 ->
apart EB 2000 lo (bv_unsigned sp - lo) -> apart ne 320 lo (bv_unsigned sp - lo) -> apart AK 40 lo (bv_unsigned sp - lo) ->
apart ne 320 EB 2000 -> apart ne 320 AK 40 ->
0 < EB -> EB mod 4 = 0 -> ne mod 4 = 0 -> 0 < ne -> bv_unsigned sp mod 16 = 0 ->
a0 = Z_to_bv 64 (EB + 4 * eoff) -> a1 = Z_to_bv 64 ne -> a2 = Z_to_bv 64 AK -> a3 = Z_to_bv 64 10 ->
a4 = Z_to_bv 64 80 -> a5 = Z_to_bv 64 pitch -> a6 = Z_to_bv 64 40 -> a7 = stk8 ->
mem_inv rsegs m -> frm0 fc ->
evt rsegs (multicomb_post ne lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_multicomb) fc None m (seg_rom rsegs)).

Definition lsp_interpolate_post (IQ lo : Z)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (rv : word) (kk : iclob) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (qs' : list word),
ms' = MS (callR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv kk) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (IQ, IQ + 40)] m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' IQ (f32 qs') /\ length qs' = 10%nat.
Definition lsp_interpolate_stmt : Prop :=
forall (OLD NEW IQ sub lo : Z) (os ns qs : list word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells rsegs m OLD (f32 os) -> length os = 10%nat ->
rw_cells rsegs m NEW (f32 ns) -> length ns = 10%nat ->
rw_cells rsegs m IQ (f32 qs) -> length qs = 10%nat ->
apart IQ 40 OLD 40 -> apart IQ 40 NEW 40 -> 0 <= sub < 4 ->
a0 = Z_to_bv 64 OLD -> a1 = Z_to_bv 64 NEW -> a2 = Z_to_bv 64 IQ -> a3 = Z_to_bv 64 10 ->
a4 = Z_to_bv 64 sub -> a5 = Z_to_bv 64 4 ->
mem_inv rsegs m -> frm0 fc ->
stk rsegs m lo (bv_unsigned sp) -> lo + LSPI_DEPTH <= bv_unsigned sp -> NB_GLOBALS_TOP <= lo -> bv_unsigned sp < 2^63 ->
apart OLD 40 lo (bv_unsigned sp - lo) -> apart NEW 40 lo (bv_unsigned sp - lo) -> apart IQ 40 lo (bv_unsigned sp - lo) ->
0 < OLD -> OLD mod 4 = 0 -> 0 < NEW -> NEW mod 4 = 0 -> 0 < IQ -> IQ mod 4 = 0 ->
evt rsegs (lsp_interpolate_post IQ lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_lsp_interpolate) fc None m (seg_rom rsegs)).

Definition lsp_to_lpc_post (AK lo : Z)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (rv : word) (kk : iclob) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (aks' : list word),
ms' = MS (callR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv kk) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (AK, AK + 40)] m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' AK (f32 aks') /\ length aks' = 10%nat.
Definition lsp_to_lpc_stmt : Prop :=
forall (IQ AK lo : Z) (qs aks : list word) (stk8 : word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells rsegs m IQ (f32 qs) -> length qs = 10%nat ->
rw_cells rsegs m AK (f32 aks) -> length aks = 10%nat ->
stk rsegs m lo (bv_unsigned sp) -> lo + LSP2LPC_DEPTH <= bv_unsigned sp -> NB_GLOBALS_TOP <= lo -> bv_unsigned sp < 2^63 ->
apart IQ 40 lo (bv_unsigned sp - lo) -> apart AK 40 lo (bv_unsigned sp - lo) -> apart AK 40 IQ 40 ->
a0 = Z_to_bv 64 IQ -> a1 = Z_to_bv 64 AK -> a2 = Z_to_bv 64 10 -> a3 = stk8 ->
mem_inv rsegs m -> frm0 fc ->
0 < IQ -> IQ mod 4 = 0 -> 0 < AK -> AK mod 4 = 0 -> bv_unsigned sp mod 16 = 0 ->
evt rsegs (lsp_to_lpc_post AK lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_lsp_to_lpc) fc None m (seg_rom rsegs)).

Definition farr_post (W : list (Z * Z)) (P : Z) (n : nat)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (rv : word) (kk : iclob) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ws' : list word),
ms' = MS (callR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv kk) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ rw_cells rsegs m' P (f32 ws') /\ length ws' = n.

Definition farr2_post (W : list (Z * Z)) (P : Z) (n : nat) (Q : Z) (k : nat)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (rv : word) (kk : iclob) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ws' vs' : list word),
ms' = MS (callR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv kk) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ rw_cells rsegs m' P (f32 ws') /\ length ws' = n
/\ rw_cells rsegs m' Q (f32 vs') /\ length vs' = k.

Definition farr2s_post (W : list (Z * Z)) (P : Z) (n : nat) (Q : Z) (k : nat) (lo : Z)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (rv : word) (kk : iclob) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ws' vs' : list word),
ms' = MS (callR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv kk) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch ((lo, bv_unsigned sp) :: W) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' P (f32 ws') /\ length ws' = n
/\ rw_cells rsegs m' Q (f32 vs') /\ length vs' = k.

Definition bw_lpc_w_stmt : Prop :=
forall (PI PO : Z) (xs ys : list word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells rsegs m PI (f32 xs) -> length xs = 10%nat -> rw_cells rsegs m PO (f32 ys) -> length ys = 10%nat ->
apart PI 40 PO 40 ->
0 < PI -> PI mod 4 = 0 -> 0 < PO -> PO mod 4 = 0 ->
a0 = Z_to_bv 64 PI -> a1 = Z_to_bv 64 PO -> a2 = Z_to_bv 64 10 ->
mem_inv rsegs m -> frm0 fc ->
evt rsegs (farr_post [(PO, PO + 40)] PO 10%nat ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_bw_lpc) fc None m (seg_rom rsegs)).

Definition compute_rms16_w_stmt : Prop :=
forall (PX n : Z) (xs : list word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells rsegs m PX (f32 xs) -> length xs = Z.to_nat n -> 1 <= n < 2^31 ->
0 < PX -> PX mod 4 = 0 ->
a0 = Z_to_bv 64 PX -> a1 = Z_to_bv 64 n ->
mem_inv rsegs m -> frm0 fc ->
evt rsegs (farr_post [] PX (Z.to_nat n) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_compute_rms16) fc None m (seg_rom rsegs)).

Definition signal_mul_w_stmt : Prop :=
forall (PX : Z) (xs : list word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells rsegs m PX (f32 xs) -> length xs = 40%nat ->
0 < PX -> PX mod 4 = 0 ->
a0 = Z_to_bv 64 PX -> a1 = Z_to_bv 64 PX -> a2 = Z_to_bv 64 40 ->
mem_inv rsegs m -> frm0 fc ->
evt rsegs (farr_post [(PX, PX + 160)] PX 40%nat ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_signal_mul) fc None m (seg_rom rsegs)).

Definition sanitize_values32_w_stmt : Prop :=
forall (PX : Z) (xs : list word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells rsegs m PX (f32 xs) -> length xs = 40%nat ->
0 < PX -> PX mod 4 = 0 ->
a0 = Z_to_bv 64 PX -> a1 = Z_to_bv 64 40 ->
mem_inv rsegs m -> frm0 fc ->
evt rsegs (farr_post [(PX, PX + 160)] PX 40%nat ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_sanitize_values32) fc None m (seg_rom rsegs)).

Definition iir_mem16_w_stmt : Prop :=
forall (PX PD PY PM N lo : Z) (xs den ys mem0 : list word) (stk8 : word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells rsegs m PX (f32 xs) -> length xs = Z.to_nat N ->
rw_cells rsegs m PD (f32 den) -> length den = 10%nat ->
rw_cells rsegs m PM (f32 mem0) -> length mem0 = 10%nat ->
(PY = PX /\ ys = xs \/ apart PY (4 * N) PX (4 * N) /\ rw_cells rsegs m PY (f32 ys) /\ length ys = Z.to_nat N) ->
1 <= N <= 160 ->
apart PY (4 * N) PD 40 -> apart PY (4 * N) PM 40 -> apart PM 40 PD 40 -> apart PM 40 PX (4 * N) ->
0 < PX -> PX mod 4 = 0 -> 0 < PD -> PD mod 4 = 0 -> 0 < PY -> PY mod 4 = 0 -> 0 < PM -> PM mod 4 = 0 ->
stk rsegs m lo (bv_unsigned sp) -> lo + IIR_DEPTH <= bv_unsigned sp -> NB_GLOBALS_TOP <= lo -> bv_unsigned sp < 2^63 ->
apart PX (4 * N) lo (bv_unsigned sp - lo) -> apart PY (4 * N) lo (bv_unsigned sp - lo) ->
apart PD 40 lo (bv_unsigned sp - lo) -> apart PM 40 lo (bv_unsigned sp - lo) ->
a0 = Z_to_bv 64 PX -> a1 = Z_to_bv 64 PD -> a2 = Z_to_bv 64 PY -> a3 = Z_to_bv 64 N -> a4 = Z_to_bv 64 10 ->
a5 = Z_to_bv 64 PM -> a6 = stk8 ->
mem_inv rsegs m -> frm0 fc ->
evt rsegs (farr2s_post [(PY, PY + 4 * N); (PM, PM + 40)] PY (Z.to_nat N) PM 10%nat lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_iir_mem16) fc None m (seg_rom rsegs)).

Definition highpass_w_stmt : Prop :=
forall (PX PM fid lo : Z) (xs mem0 : list word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells rsegs m PX (f32 xs) -> length xs = 160%nat ->
rw_cells rsegs m PM (f32 mem0) -> length mem0 = 2%nat ->
(fid = 1 \/ fid = 3) -> apart PX 640 PM 8 ->
0 < PX -> PX mod 4 = 0 -> 0 < PM -> PM mod 4 = 0 ->
stk rsegs m lo (bv_unsigned sp) -> lo + HIGHPASS_DEPTH <= bv_unsigned sp -> NB_GLOBALS_TOP <= lo -> bv_unsigned sp < 2^63 ->
apart PX 640 lo (bv_unsigned sp - lo) -> apart PM 8 lo (bv_unsigned sp - lo) ->
a0 = Z_to_bv 64 PX -> a1 = Z_to_bv 64 PX -> a2 = Z_to_bv 64 160 -> a3 = Z_to_bv 64 fid -> a4 = Z_to_bv 64 PM ->
mem_inv rsegs m -> frm0 fc ->
evt rsegs (farr2s_post [(PX, PX + 640); (PM, PM + 8)] PX 160%nat PM 2%nat lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_highpass) fc None m (seg_rom rsegs)).
End Stmts.

Section Notify.
Context {RCEIL : RunCeiling}.
Variables (notify : list Z -> X1qx.M PState unit).
Variable stderr_ok : mem -> Prop.
Variable sspc : mem -> word -> Prop.
Variable STR_TOP : Z.

Definition nb_zb (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.
Definition nb_cstr_arg (m : mem) (w : word) (s : list Z) (lo sp : Z) : Prop :=
exists slack : list byte,
bytes_at rsegs m (bv_unsigned w) (nb_zb s ++ Z_to_bv 8 0 :: slack)
/\ Forall (fun c => 0 < c < 256) s
/\ ((- (bv_unsigned w + zlength s + 1)) mod 8 <= zlength slack)
/\ (zlength s < 2147483647 - 256)
/\ (0 < bv_unsigned w)
/\ (bv_unsigned w + zlength s + 1 + zlength slack <= lo \/ sp <= bv_unsigned w)
/\ (NB_GLOBALS_TOP <= bv_unsigned w \/ bv_unsigned w + zlength s + 1 + zlength slack <= STR_TOP).

Definition nb_fprintf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(lo : Z) (canary : word) (m : mem) (st : PState) : unit -> PState -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (NB_RSTDERR, NB_RSTDERR + 232)] m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ (forall k : bv 5, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk rsegs m' lo (bv_unsigned sp)
/\ stderr_ok m'
/\ sspc m' canary
/\ st' = st.

Definition nb_notify_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (s : list Z) (lo : Z) (canary : word),
a0 = Z_to_bv 64 NB_RSTDERR -> a1 = Z_to_bv 64 NB_FMT_notify -> nb_cstr_arg m a2 s lo (bv_unsigned sp) ->
stderr_ok m ->
stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - NB_FPRINTF_DEPTH) -> (NB_GLOBALS_TOP <= lo) ->
(bv_unsigned sp < 2^63) ->
sspc m canary -> mem_inv rsegs m -> frm0 fc ->
X1qx.implM rsegs (notify s) st
(nb_fprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_fprintf) fc None m (seg_rom rsegs)).

Definition stderr_ok_frame_stmt : Prop :=
forall m m' W, stderr_ok m -> munch W m m' -> wmono rsegs m m' ->
disjoint_from W NB_RSTDERR 232 -> stderr_ok m'.
Definition sspc_frame_stmt : Prop :=
forall m m' W c, sspc m c -> munch W m m' -> wmono rsegs m m' ->
disjoint_from W NB_GOT_SSP 8 -> disjoint_from W NB_SSP_GUARD 8 -> sspc m' c.
End Notify.

Section Iface.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Variables (notify : list Z -> X1qx.M PState unit) (stderr_ok : mem -> Prop) (sspc : mem -> word -> Prop).

Local Notation NBREP := (nbstate_rep rsegs NB_MODE_PTR NB_SUBMODES_PTR A_speex_default_user_handler A_speex_std_stereo_request_handler).

Definition nb_W (ST OUT A STEREO ISV lo usp : Z) : list (Z * Z) :=
[(lo, usp); (ST, ST + NBSTATE_SIZEOF); (OUT, OUT + 640); (ISV, ISV + 640); (A, A + BITS_SIZEOF);
(STEREO, STEREO + 8); (NB_RSTDERR, NB_RSTDERR + 232)].

Definition nb_win (X n : Z) : Prop := 0 < X /\ (X + n <= 0x10000 \/ NB_GLOBALS_TOP <= X).
Definition nb_layout (ST OUT A D DSZ STEREO ISV lo usp : Z) : Prop :=
NB_GLOBALS_TOP <= lo /\ nb_win ST NBSTATE_SIZEOF /\ NB_GLOBALS_TOP <= OUT /\ NB_GLOBALS_TOP <= A /\
nb_win D DSZ /\ NB_GLOBALS_TOP <= STEREO /\ NB_GLOBALS_TOP <= ISV /\
apart ST NBSTATE_SIZEOF lo (usp - lo) /\ apart OUT 640 lo (usp - lo) /\ apart ISV 640 lo (usp - lo) /\
apart A BITS_SIZEOF lo (usp - lo) /\ apart D DSZ lo (usp - lo) /\ apart STEREO 8 lo (usp - lo) /\
apart ST NBSTATE_SIZEOF OUT 640 /\ apart ST NBSTATE_SIZEOF ISV 640 /\ apart ST NBSTATE_SIZEOF A BITS_SIZEOF /\
apart ST NBSTATE_SIZEOF D DSZ /\ apart ST NBSTATE_SIZEOF STEREO 8 /\
apart OUT 640 ISV 640 /\ apart OUT 640 A BITS_SIZEOF /\ apart OUT 640 D DSZ /\ apart OUT 640 STEREO 8 /\
apart ISV 640 A BITS_SIZEOF /\ apart ISV 640 D DSZ /\ apart ISV 640 STEREO 8 /\
apart A BITS_SIZEOF STEREO 8 /\ apart D DSZ STEREO 8.

Definition nb_decode_post (ST OUT A D STEREO ISV : Z) (lo : Z) (canary : word)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (m : mem) (s : PState)
: (Z * nb_state ptr * bits_st ptr) -> PState -> machine_state -> Prop :=
fun res s' ms' =>
let '(r, st', b') := res in
exists (kk : iclob) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ows iws sws : list word),
ms' = MS (callR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 r) kk) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch (nb_W ST OUT A STEREO ISV lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ fs_kept F F'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ NBREP m' ST OUT STEREO st'
/\ rw_cells rsegs m' (ST + 2032) [C8 (Z_to_bv 64 (ST + NB_EXC_OFF))]
/\ bits_rep rsegs m' A D b' /\ bits_ok b'
/\ rw_cells rsegs m' OUT (f32 ows) /\ length ows = 160%nat
/\ rw_cells rsegs m' ISV (f32 iws) /\ length iws = 160%nat
/\ rw_cells rsegs m' STEREO (f32 sws) /\ length sws = 2%nat
/\ nb_tables m' /\ stderr_ok m' /\ sspc m' canary /\ s' = s.

Definition nb_decode_stmt : Prop :=
forall (ST OUT A D STEREO ISV : Z) (st : nb_state ptr) (b : bits_st ptr) (ows iws sws : list word)
(lo : Z) (canary : word) (s : PState)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
NBREP m ST OUT STEREO st ->
match nb_innov_save st with None => True | Some k => ISV = OUT + 4 * k end ->
bits_rep rsegs m A D b -> bits_ok b ->
rw_cells rsegs m OUT (f32 ows) -> length ows = 160%nat ->
rw_cells rsegs m ISV (f32 iws) -> length iws = 160%nat ->
rw_cells rsegs m STEREO (f32 sws) -> length sws = 2%nat ->
nb_tables m -> stderr_ok m -> sspc m canary ->
stk rsegs m lo (bv_unsigned sp) -> lo + NB_DECODE_DEPTH <= bv_unsigned sp -> bv_unsigned sp < 2^63 ->
nb_layout ST OUT A D (sb_buf_size b) STEREO ISV lo (bv_unsigned sp) -> ST + NBSTATE_SIZEOF < 2^63 ->
OUT mod 4 = 0 -> STEREO mod 4 = 0 -> bv_unsigned sp mod 16 = 0 ->
a0 = Z_to_bv 64 ST -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 OUT ->
mem_inv rsegs m -> frm0 fc ->
X1qx.implM rsegs
(nb_decode notify bits_unpack_unsigned_M bits_advance_M bits_remaining_M st b) s
(nb_decode_post ST OUT A D STEREO ISV lo canary ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m s)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_nb_decode) fc None m (seg_rom rsegs)).
End Iface.
