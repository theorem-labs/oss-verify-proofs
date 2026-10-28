(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bs X1c2 X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7 X1go.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1ho. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nr.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1nt X1rh X1re X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Definition A_speex_decode_native : Z := 0x1cf98.
Definition A_speex_bits_peek : Z := 0x1cd68.
Definition A_qmf_synth : Z := 0x24100.
Definition A_sb_decode_lost : Z := 0x2fcf8.
Definition A_h0 : Z := 0x131ec.
Definition A_gc_quant_bound : Z := 0x1336c.
Definition QMF_ORDER : Z := 64.
Definition SB_SUBMODE_BITS : Z := 3.

Definition SB_FRAME : Z := 304.

Definition SB_LOCAL_DEPTH : Z := 24576.
Definition QMF_DEPTH : Z := 8192.
Definition SBLOST_DEPTH : Z := 12288.

Fixpoint rdec_depth (d : dec_state bptr) : Z :=
match d with
| DecNB _ => NB_DECODE_DEPTH
| DecSB _ low => SB_LOCAL_DEPTH + rdec_depth low
end.

Definition sbW (lo usp BITS OUT STEREO : Z) (LBD : list block) : list (Z * Z) :=
(lo, usp) :: (BITS, BITS + BITS_SIZEOF) :: (OUT, OUT + HOUT_BYTES) :: (STEREO, STEREO + 24)
:: (RSTDERR, RSTDERR + 232) :: blocks_ivs LBD.

Definition isave_ok {ptr : Type} (d : dec_state ptr) : Prop :=
match d with
| DecNB st => match nb_innov_save st with None => True | Some k => 160 <= k /\ 4 * (k + 160) <= HOUT_BYTES end
| DecSB s _ => match sbd_innov_save s with None => True | Some k => k = 2 * sbd_frame_size s end
end.

Fixpoint dec_nested {ptr : Type} (d : dec_state ptr) : Prop :=
match d with
| DecNB _ => True
| DecSB s low => dec_mode low = sbm_nb_mode (sbd_mode s) /\ dec_nested low
end.

Definition rdec_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(st : PState) (OUT STEREO S : Z) (d : dec_state bptr) (LBD : list block) (b : bits_st bptr)
(BITS Dc lo : Z) (canary : word) (m : mem)
(r : Z * dec_state bptr * bits_st bptr) (st' : PState) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem)
(outb stb : list byte),
let '(ret, d', b') := r in
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ret) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ -2 <= ret <= 0 /\ dec_depth d' = dec_depth d /\ dec_mode d' = dec_mode d /\ dec_nested d'
/\ frm0 fc'
/\ munch (sbW lo (bv_unsigned sp) BITS OUT STEREO LBD) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ DREP OUT STEREO m' S d' LBD /\ EXCREADY m' S d'
/\ bits_rep rsegs m' BITS Dc b' /\ bits_ok b'
/\ sb_owner b' = sb_owner b /\ sb_chars b' = sb_chars b /\ sb_buf_size b' = sb_buf_size b
/\ u8arr rsegs m' OUT outb /\ Z.of_nat (length outb) = HOUT_BYTES
/\ rw_cells rsegs m' STEREO [CB 24 stb]
/\ stderr_wfile m' /\ ssp_cells m' canary
/\ st' = st.

Definition rdec_layout {RCEIL : RunCeiling} (BITS OUT STEREO lo usp : Z) : Prop :=
alloc_ceiling <= BITS /\ alloc_ceiling <= OUT /\ alloc_ceiling <= STEREO /\ alloc_ceiling <= lo /\
apart BITS BITS_SIZEOF OUT HOUT_BYTES /\ apart BITS BITS_SIZEOF STEREO 24 /\ apart OUT HOUT_BYTES STEREO 24 /\
apart BITS BITS_SIZEOF lo (usp - lo) /\ apart OUT HOUT_BYTES lo (usp - lo) /\ apart STEREO 24 lo (usp - lo).

Definition rdec_at {RCEIL : RunCeiling} (ENTRY : Z) (d : dec_state bptr) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(st : PState) (OUT STEREO S : Z) (LBD : list block) (b : bits_st bptr) (BITS Dc lo : Z)
(outb stb : list byte) (canary : word),
DREP OUT STEREO m S d LBD -> (dec_depth d <= 3)%nat -> isave_ok d -> dec_nested d ->
List.NoDup (map blk_id LBD) -> lbd_apart LBD -> (forall x, In x LBD -> rblock_range (blk_addr x) (blk_size x)) ->
bits_rep rsegs m BITS Dc b -> bits_ok b -> sb_owner b = 1 ->
rblock_range Dc (sb_buf_size b) -> (forall x, In x LBD -> apart Dc (sb_buf_size b) (blk_addr x) (blk_size x)) ->
u8arr rsegs m OUT outb -> Z.of_nat (length outb) = HOUT_BYTES -> OUT mod 4 = 0 ->
rw_cells rsegs m STEREO [CB 24 stb] -> STEREO mod 4 = 0 ->
rtables_pristine m -> stderr_wfile m -> ssp_cells m canary ->
rdec_layout BITS OUT STEREO lo (bv_unsigned sp) ->
stk rsegs m lo (bv_unsigned sp) -> lo + rdec_depth d <= bv_unsigned sp -> bv_unsigned sp < 2^63 ->
bv_unsigned sp mod 16 = 0 ->
mem_inv rsegs m -> frm0 fc ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 BITS -> a2 = Z_to_bv 64 OUT ->
implM rsegs (speex_decode io_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M d b 0) st
(rdec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 st OUT STEREO S d LBD b BITS Dc lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ENTRY) fc None m (seg_rom rsegs)).

Definition rctl_isave_at {RCEIL : RunCeiling} (d : dec_state bptr) : Prop :=
forall (OUTL OUT STEREO S : Z) (LBD : list block) (off P lo : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
DREP OUTL STEREO m S d LBD -> (dec_depth d <= 3)%nat -> creq_ok OUT P (CtlSetInnovationSave off) -> rtables_pristine m ->
(forall b, In b LBD -> rblock_range (blk_addr b) (blk_size b)) -> List.NoDup (map blk_id LBD) -> lbd_apart LBD ->
(P + 0 <= lo \/ bv_unsigned sp <= P) ->
(forall b, In b LBD -> P + 0 <= blk_addr b \/ blk_addr b + blk_size b <= P) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ctl_depth d ->
mem_inv rsegs m -> frm0 fc ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (ctl_req_code (CtlSetInnovationSave off)) -> a2 = Z_to_bv 64 P ->
evt rsegs (rctl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 OUT STEREO S d LBD (CtlSetInnovationSave off) P lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_ctl) fc None m (seg_rom rsegs)).

Section Leaves8.
Context {RCEIL : RunCeiling}.

Definition lsp_interpolate8_post (IQ lo : Z)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (rv : word) (kk : iclob) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (qs' : list word),
ms' = MS (callR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv kk) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (IQ, IQ + 32)] m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' IQ (f32 qs') /\ length qs' = 8%nat.
Definition lsp_interpolate8_stmt : Prop :=
forall (OLD NEW IQ sub lo : Z) (os ns qs : list word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells rsegs m OLD (f32 os) -> length os = 8%nat ->
rw_cells rsegs m NEW (f32 ns) -> length ns = 8%nat ->
rw_cells rsegs m IQ (f32 qs) -> length qs = 8%nat ->
apart IQ 32 OLD 32 -> apart IQ 32 NEW 32 -> 0 <= sub < 4 ->
a0 = Z_to_bv 64 OLD -> a1 = Z_to_bv 64 NEW -> a2 = Z_to_bv 64 IQ -> a3 = Z_to_bv 64 8 ->
a4 = Z_to_bv 64 sub -> a5 = Z_to_bv 64 4 ->
mem_inv rsegs m -> frm0 fc ->
stk rsegs m lo (bv_unsigned sp) -> lo + LSPI_DEPTH <= bv_unsigned sp -> NB_GLOBALS_TOP <= lo -> bv_unsigned sp < 2^63 ->
apart OLD 32 lo (bv_unsigned sp - lo) -> apart NEW 32 lo (bv_unsigned sp - lo) -> apart IQ 32 lo (bv_unsigned sp - lo) ->
0 < OLD -> OLD mod 4 = 0 -> 0 < NEW -> NEW mod 4 = 0 -> 0 < IQ -> IQ mod 4 = 0 ->
evt rsegs (lsp_interpolate8_post IQ lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_lsp_interpolate) fc None m (seg_rom rsegs)).

Definition lsp_to_lpc8_post (AK lo : Z)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (rv : word) (kk : iclob) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (aks' : list word),
ms' = MS (callR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv kk) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (AK, AK + 32)] m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' AK (f32 aks') /\ length aks' = 8%nat.
Definition lsp_to_lpc8_stmt : Prop :=
forall (IQ AK lo : Z) (qs aks : list word) (stk8 : word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells rsegs m IQ (f32 qs) -> length qs = 8%nat ->
rw_cells rsegs m AK (f32 aks) -> length aks = 8%nat ->
stk rsegs m lo (bv_unsigned sp) -> lo + LSP2LPC_DEPTH <= bv_unsigned sp -> NB_GLOBALS_TOP <= lo -> bv_unsigned sp < 2^63 ->
apart IQ 32 lo (bv_unsigned sp - lo) -> apart AK 32 lo (bv_unsigned sp - lo) -> apart AK 32 IQ 32 ->
a0 = Z_to_bv 64 IQ -> a1 = Z_to_bv 64 AK -> a2 = Z_to_bv 64 8 -> a3 = stk8 ->
mem_inv rsegs m -> frm0 fc ->
0 < IQ -> IQ mod 4 = 0 -> 0 < AK -> AK mod 4 = 0 -> bv_unsigned sp mod 16 = 0 ->
evt rsegs (lsp_to_lpc8_post AK lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_lsp_to_lpc) fc None m (seg_rom rsegs)).

Definition iir_mem16_8_stmt : Prop :=
forall (PX PD PY PM N lo : Z) (xs den ys mem0 : list word) (stk8 : word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells rsegs m PX (f32 xs) -> length xs = Z.to_nat N ->
rw_cells rsegs m PD (f32 den) -> length den = 8%nat ->
rw_cells rsegs m PM (f32 mem0) -> length mem0 = 8%nat ->
(PY = PX /\ ys = xs \/ apart PY (4 * N) PX (4 * N) /\ rw_cells rsegs m PY (f32 ys) /\ length ys = Z.to_nat N) ->
1 <= N <= 320 ->
apart PY (4 * N) PD 32 -> apart PY (4 * N) PM 32 -> apart PM 32 PD 32 -> apart PM 32 PX (4 * N) ->
0 < PX -> PX mod 4 = 0 -> 0 < PD -> PD mod 4 = 0 -> 0 < PY -> PY mod 4 = 0 -> 0 < PM -> PM mod 4 = 0 ->
stk rsegs m lo (bv_unsigned sp) -> lo + IIR_DEPTH <= bv_unsigned sp -> NB_GLOBALS_TOP <= lo -> bv_unsigned sp < 2^63 ->
apart PX (4 * N) lo (bv_unsigned sp - lo) -> apart PY (4 * N) lo (bv_unsigned sp - lo) ->
apart PD 32 lo (bv_unsigned sp - lo) -> apart PM 32 lo (bv_unsigned sp - lo) ->
a0 = Z_to_bv 64 PX -> a1 = Z_to_bv 64 PD -> a2 = Z_to_bv 64 PY -> a3 = Z_to_bv 64 N -> a4 = Z_to_bv 64 8 ->
a5 = Z_to_bv 64 PM -> a6 = stk8 ->
mem_inv rsegs m -> frm0 fc ->
evt rsegs (farr2s_post [(PY, PY + 4 * N); (PM, PM + 32)] PY (Z.to_nat N) PM 8%nat lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_iir_mem16) fc None m (seg_rom rsegs)).
End Leaves8.

Section SbLeavesProposal.
Context {RCEIL : RunCeiling}.

Definition qmf_synth_post (Y N G0 G1 lo : Z)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (rv : word) (kk : iclob) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ys' g0' g1' : list word),
ms' = MS (callR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv kk) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (Y, Y + 4 * N); (G0, G0 + 256); (G1, G1 + 256)] m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' Y (f32 ys') /\ length ys' = Z.to_nat N
/\ rw_cells rsegs m' G0 (f32 g0') /\ length g0' = 64%nat
/\ rw_cells rsegs m' G1 (f32 g1') /\ length g1' = 64%nat.
Definition qmf_synth_stmt : Prop :=
forall (Y N G0 G1 lo : Z) (ys g0 g1 : list word) (stk8 : word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells rsegs m Y (f32 ys) -> length ys = Z.to_nat N -> (N = 320 \/ N = 640) ->
rw_cells rsegs m G0 (f32 g0) -> length g0 = 64%nat -> rw_cells rsegs m G1 (f32 g1) -> length g1 = 64%nat ->
rw_cells rsegs m (bv_unsigned sp) [C8 stk8] ->
stk rsegs m lo (bv_unsigned sp) -> lo + QMF_DEPTH <= bv_unsigned sp -> NB_GLOBALS_TOP <= lo -> bv_unsigned sp < 2^63 ->
NB_GLOBALS_TOP <= Y -> (G0 + 256 <= 0x10000 \/ NB_GLOBALS_TOP <= G0) -> (G1 + 256 <= 0x10000 \/ NB_GLOBALS_TOP <= G1) ->
apart Y (4 * N) lo (bv_unsigned sp - lo) -> apart G0 256 lo (bv_unsigned sp - lo) -> apart G1 256 lo (bv_unsigned sp - lo) ->
apart Y (4 * N) G0 256 -> apart Y (4 * N) G1 256 -> apart G0 256 G1 256 ->
a0 = Z_to_bv 64 Y -> a1 = Z_to_bv 64 (Y + 2 * N) -> a2 = Z_to_bv 64 A_h0 -> a3 = Z_to_bv 64 Y ->
a4 = Z_to_bv 64 N -> a5 = Z_to_bv 64 QMF_ORDER -> a6 = Z_to_bv 64 G0 -> a7 = Z_to_bv 64 G1 ->
mem_inv rsegs m -> frm0 fc ->
Y mod 4 = 0 -> 0 < G0 -> G0 mod 4 = 0 -> 0 < G1 -> G1 mod 4 = 0 ->
evt rsegs (qmf_synth_post Y N G0 G1 lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_qmf_synth) fc None m (seg_rom rsegs)).

Definition sb_decode_lost_post (S OUT : Z) (s : sbd_state bptr) (a : sb_addrs) (lo : Z)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (rv : word) (kk : iclob) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (j' : sb_junk) (outb' : list byte),
ms' = MS (callR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv kk) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch ((lo, bv_unsigned sp) :: (OUT, OUT + HOUT_BYTES) :: blocks_ivs (sb_blocks s S a)) m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' S (SBCELLS (set_sbd_first s 1) a OUT j') /\ sb_junk_ok (set_sbd_first s 1) j' /\ sb_bufs rsegs m' a j'
/\ u8arr rsegs m' OUT outb' /\ Z.of_nat (length outb') = HOUT_BYTES.
Definition sb_decode_lost_stmt : Prop :=
forall (S OUT : Z) (s : sbd_state bptr) (a : sb_addrs) (j : sb_junk) (outb : list byte) (lo : Z) (stk8 : word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells rsegs m S (SBCELLS s a OUT j) -> sb_junk_ok s j -> sb_inv s -> sb_bufs rsegs m a j ->
u8arr rsegs m OUT outb -> Z.of_nat (length outb) = HOUT_BYTES ->
lbd_apart (sb_blocks s S a) -> List.NoDup (map blk_id (sb_blocks s S a)) ->
(forall x, In x (sb_blocks s S a) -> rblock_range (blk_addr x) (blk_size x)) ->
alloc_ceiling <= OUT -> alloc_ceiling <= lo -> apart OUT HOUT_BYTES lo (bv_unsigned sp - lo) ->
stk rsegs m lo (bv_unsigned sp) -> lo + SBLOST_DEPTH <= bv_unsigned sp -> bv_unsigned sp < 2^63 ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 OUT -> a2 = Z_to_bv 64 1 -> a3 = stk8 ->
mem_inv rsegs m -> frm0 fc ->
OUT mod 4 = 0 ->
evt rsegs (sb_decode_lost_post S OUT s a lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_sb_decode_lost) fc None m (seg_rom rsegs)).
End SbLeavesProposal.

Definition SB_STR_TOP : Z := 0x10500.

Record sb_hyps {RCEIL : RunCeiling} (k : nat) : Prop := SBH {
h_native : forall d, (dec_depth d <= k)%nat -> rdec_at A_speex_decode_native d;
h_ctl    : forall d, (dec_depth d <= k)%nat -> rctl_at d;
h_ctli   : forall d, (dec_depth d <= k)%nat -> rctl_isave_at d;
h_lspq   : @lsp_unquant_stmt bptr LspUnquantHigh;
h_innov  : forall p, scb_params_ok p -> @innov_unquant_stmt bptr (InnovSplitCbShapeSignUnquant p);
h_lspi   : lsp_interpolate8_stmt;
h_l2l    : lsp_to_lpc8_stmt;
h_iir    : iir_mem16_8_stmt;
h_rms    : compute_rms16_w_stmt;
h_smul   : signal_mul_w_stmt;
h_exp    : exp_stmt;
h_qmf    : qmf_synth_stmt;
h_lost   : sb_decode_lost_stmt;
h_notify : nb_notify_stmt io_notify stderr_wfile ssp_cells SB_STR_TOP;
h_stderr_frame : stderr_ok_frame_stmt stderr_wfile;
h_sspc_frame : sspc_frame_stmt ssp_cells }.

Definition sb_decode_goal {RCEIL : RunCeiling} : Prop :=
forall k, sb_hyps k -> forall (s : sbd_state bptr) (low : dec_state bptr), (dec_depth low <= k)%nat -> rdec_at A_sb_decode (DecSB s low).
