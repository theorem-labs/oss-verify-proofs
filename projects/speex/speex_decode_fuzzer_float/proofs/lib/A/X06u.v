(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1nu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1qy.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1nt X1rg X1rh X1re X1od X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X00c X07z X05o X05s
X0ae X09u X09x X0af X09p X09l X0a4 X0a5 X05l X05e X05c X05m X06d X069 X068
X071 X06v X06y.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Notation PM := (X1qy.M pst).
Definition hP_chunk_loop (fuel : nat) (payload : list Z) (h : hstate unit) : PM (outcome unit) :=
chunk_loop p_malloc p_calloc p_realloc p_free p_notify p_warning bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M fuel payload h.
Definition hP_page_loop (fuel : nat) (h : hstate unit) : PM (outcome unit) :=
page_loop p_malloc p_calloc p_realloc p_free p_notify p_warning bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M fuel h.
Definition hP_packet_loop (fuel : nat) (h : hstate unit) (packet_no : Z) : PM (outcome unit) :=
packet_loop p_calloc p_realloc p_free p_notify p_warning bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M fuel h packet_no.
Definition hP_decode_loop (n : nat) (st : dec_state unit) (b : bits_st unit) : PM (dec_state unit * bits_st unit) :=
decode_loop p_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M n st b.
Definition hP_process_header (h : hstate unit) (pdata : list Z) (bytes : Z) : PM (option (hstate unit)) :=
process_header p_calloc p_free p_notify h pdata bytes.
Definition hP_cleanup (h : hstate unit) : PM unit := cleanup p_free h.

Definition H_LIVE : Z := 25.

Definition H_STACK : Z := 0x20000.

Record hinv := HI {
x_usp : Z;
x_S1 : Z;
x_lo : Z;
x_gp : word;
x_F : Z;
x_d : Z; x_bs : list byte;
x_live : list (Z * Z);
x_sp0 : Z; x_cr0 : Z;
x_m0 : mem;
x_mR : mem;
x_ra : word; x_s0 : word; x_s1 : word; x_s2 : word; x_s3 : word; x_s4 : word; x_s5 : word; x_s6 : word; x_s7 : word; x_s8 : word;
x_s9 : word; x_s10 : word; x_s11 : word
}.
Definition x_sf (X : hinv) : Z := Z.shiftr (x_F X) 3 + SHB.
Definition x_size (X : hinv) : Z := Z.of_nat (length (x_bs X)).
Definition x_payload (X : hinv) : list Z := map bv_unsigned (x_bs X).

Section Ctx.
Variable RT : rt_sig.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable X : hinv.
Local Notation usp := (x_usp X). Local Notation S1 := (x_S1 X). Local Notation lo := (x_lo X). Local Notation F := (x_F X).
Local Notation sf := (x_sf X). Local Notation mR := (x_mR X).

Record hinv_ok : Prop := HIOK {
hi_usp : usp mod 16 = 0 /\ 336 <= usp /\ usp + 16 <= USTACK_TOP;
hi_S1 : S1 = Z.land (usp + -320) 18446744073709551584 /\ S1 mod 32 = 0 /\ usp - 336 <= S1 <= usp - 320;
hi_lo : x_sp0 X - STACK_WIN <= lo /\ lo + RT_STACK + H_STACK <= S1 /\ SH_HI <= lo;
hi_F : 0 < F /\ F mod 64 = 0 /\ F + fs_size 8 <= lo /\ (F + fs_size 8 <= SH_LO \/ SH_HI <= F) /\ IMG_TOP <= F;
hi_pay : 0 < x_d X < 2^64 /\ x_size X <= MAX_FUZZ_SIZE /\ bytes_at asegs mR (x_d X) (x_bs X)
/\ ((exists p n, In (p, n) (x_live X) /\ p <= x_d X /\ x_d X + x_size X <= p + n) \/ x_bs X = []);
hi_live : (forall p n, In (p, n) (x_live X) -> 0 < n) /\ Z.of_nat (length (x_live X)) + H_LIVE <= LIVE_MAX;
hi_cr : FUZZ_COST <= x_cr0 X;
hi_shr : rw_cells asegs mR (sf + 16) [CB 1144 HSH_R];
hi_hdr : rw_cells asegs mR F [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x227f8); C8 (Z_to_bv 64 0x96668)];
hi_saves : rw_cells asegs mR (usp + -104) (h_saves (x_s11 X) (x_s10 X) (x_s9 X) (x_s8 X) (x_s7 X) (x_s6 X) (x_s5 X) (x_s4 X) (x_s3 X) (x_s2 X) (x_s1 X) (x_s0 X) (x_ra X));
hi_gap : exists jg, rw_cells asegs mR (S1 + 216) [CB (Z.to_nat (usp - 320 - S1)) jg];
hi_ra : x_ra X = Z_to_bv 64 0x96564;
hi_s0 : bv_unsigned (x_s0 X) <= usp - 16 \/ bv_unsigned (x_s0 X) mod 8 <> 0 \/ 2^63 <= bv_unsigned (x_s0 X);
hi_pf0 : rt_pres_fp (x_live X) [] usp IO_FP (x_m0 X) mR;
hi_out : forall so, OUT_rep so (x_m0 X) -> OUT_rep so mR;
hi_naf : forall a, aclient (x_live X) [] usp a -> ~ (F <= a < F + 16384) /\ ~ (sf <= a < sf + 2048);
hi_live_geo : forall p n, In (p, n) (x_live X) -> p + n <= lo /\ (p + n <= SH_LO \/ SH_HI <= p) /\ (p + n <= 0x10000 \/ SEGTOP_A <= p)
}.

Definition h_init : hstate unit := mkH ogg_sync_init stream_zero bits_fresh None 0 0 0 0 2 0 (-1) 0 0 (-1) 0 0 (x_size X).

Definition h_WL : list (Z * Z) := (S1, S1 + 216) :: (sf, sf + 16) :: (F + 32, F + 9252) :: IO_FP.

Record haux := HA {
a_Dsy : Z; a_sybytes : list byte;
a_Bd : Z; a_L : Z; a_G : Z; a_shdr : list byte;
a_body : list byte; a_lws : list word; a_gws : list word;
a_Dc : Z;
a_S : Z; a_LBD : list block;
a_P : list (Z * Z)
}.
Definition h_own (a : haux) (h : hstate unit) : list (Z * Z) :=
(match h_st h with Some _ => blocks_live (a_LBD a) | None => [] end)
++ [(a_Dc a, sb_buf_size (h_bits h))]
++ (if h_stream_init h =? 0 then [] else [(a_Bd a, os_body_storage (h_os h)); (a_L a, 4 * os_lacing_storage (h_os h)); (a_G a, 8 * os_lacing_storage (h_os h))])
++ (match sy_data (h_oy h) with Some _ => [(a_Dsy a, sy_storage (h_oy h))] | None => [] end).

Definition H_DEC_CREDIT : Z := 16.
Definition H_HDR_CREDIT : Z := 64.
Definition h_cost (h : hstate unit) : Z := 1 + H_HDR_CREDIT + 10 * H_DEC_CREDIT * (1 + h_packet_count h).
Definition hsig (Σ1 : rts RT) (a : haux) (h : hstate unit) : Prop :=
rt_live RT Σ1 = a_P a ++ x_live X /\ List.NoDup (map fst (a_P a)) /\ Permutation (a_P a) (h_own a h)
/\ rt_frames RT Σ1 = [(F, 8%nat)] /\ rt_sp0 RT Σ1 = x_sp0 X /\ rt_pois RT Σ1 = []
/\ x_cr0 X - h_cost h <= rt_credit RT Σ1.

Definition h_os_rep (m : mem) (a : haux) (h : hstate unit) : Prop :=
if h_stream_init h =? 0 then (exists jos, rw_cells asegs m (F + HO_OS) [CB 408 jos]) /\ h_os h = stream_zero
else rw_cells asegs m (F + HO_OS) (stream_cells (a_Bd a) (a_L a) (a_G a) (a_shdr a) (h_os h)) /\ length (a_shdr a) = 284%nat
/\ stream_arrays m (h_os h) (a_Bd a) (a_L a) (a_G a) (a_body a) (a_lws a) (a_gws a)
/\ stream_fields_ok (h_os h) /\ stream_inv (h_os h) /\ body_inv (h_os h) /\ lacing_vals_ok (os_lacing (h_os h))
/\ length (os_granules (h_os h)) = length (os_lacing (h_os h))
/\ os_body_data (h_os h) <> None /\ os_lacing_vals (h_os h) <> None /\ os_granule_vals (h_os h) <> None
/\ 0 < os_lacing_storage (h_os h) /\ 0 < os_body_storage (h_os h)
/\ a_Bd a <> a_L a /\ a_Bd a <> a_G a /\ a_L a <> a_G a.

Definition h_dec_rep (m : mem) (a : haux) (h : hstate unit) : Prop :=
match h_st h with
| None => a_S a = 0 /\ a_LBD a = []
| Some d => DREP (F + HO_OUT) (F + HO_STEREO) m (a_S a) d (a_LBD a) /\ 0 < a_S a
/\ (dec_depth d <= 3)%nat /\ isave_ok d /\ dec_nestedR d /\ List.NoDup (map blk_id (a_LBD a)) /\ blocks_al8 (a_LBD a)
/\ (forall b, In b (a_LBD a) -> blk_addr b <> a_Dc a) /\ (length (a_LBD a) <= 19)%nat
end.

Definition h_pend (h : hstate unit) : Z := sy_fill (h_oy h) - sy_returned (h_oy h).
Definition h_consumed (h : hstate unit) : Z := (x_size X - h_bytes_remaining h) - h_pend h.
Definition hpure (h : hstate unit) : Prop :=
sync_inv2 (h_oy h) /\ sync_inv (h_oy h) /\ 0 <= sy_storage (h_oy h) <= 64512 /\ (sy_data (h_oy h) = None <-> sy_storage (h_oy h) = 0)
/\ bits_ok (h_bits h) /\ sb_owner (h_bits h) = 1 /\ 2000 <= sb_buf_size (h_bits h) <= 64512
/\ 0 <= h_frame_size h <= 640 /\ h_granule_frame_size h = h_frame_size h
/\ 1 <= h_nframes h <= 10 /\ -2^31 <= h_channels h < 2^31 /\ -2^31 <= h_rate h < 2^31
/\ -2^31 <= h_extra_headers h < 2^31 - 1 /\ -2^31 <= h_speex_serialno h < 2^31
/\ 0 <= h_packet_count h < 2^31 - 1 /\ -1 <= h_last_granule h < 2^63
/\ (h_stream_init h = 0 \/ h_stream_init h = 1) /\ (h_eos h = 0 \/ h_eos h = 1)
/\ 0 <= h_bytes_remaining h <= x_size X
/\ match h_st h with Some _ => h_packet_count h <> 0 | None => h_packet_count h = 0 end

/\ 0 <= h_pend h /\ 0 <= h_consumed h
/\ os_lacing_fill (h_os h) <= h_consumed h /\ os_body_fill (h_os h) <= h_consumed h
/\ os_lacing_storage (h_os h) <= 1568 + h_consumed h /\ os_body_storage (h_os h) <= 17408 + 2 * h_consumed h
/\ h_packet_count h <= 162 * h_consumed h
/\ h_packet_count h + (os_lacing_fill (h_os h) - os_lacing_returned (h_os h)) <= 162 * h_consumed h.

Definition h_spill (v80 v88 v144 v176 j0 j192 j200 : word) (h : hstate unit) : list cell :=
hsp j0 (Z_to_bv 64 (F + 64)) (Z_to_bv 64 (F + 48)) (Z_to_bv 64 (sf + 16)) (Z_to_bv 64 F) (Z_to_bv 64 F) (Z_to_bv 64 (F + HO_LOOK)) (Z_to_bv 64 (F + HO_RATE))
(Z_to_bv 64 (F + HO_ENH)) (Z_to_bv 64 (x_d X)) v80 v88 (Z_to_bv 64 SHB) (Z_to_bv 64 (h_granule_frame_size h)) (Z_to_bv 64 (h_extra_headers h))
(Z_to_bv 64 (F + HO_OY)) (Z_to_bv 64 (h_eos h)) (Z_to_bv 64 (h_nframes h)) v144 (Z_to_bv 64 (F + HO_OS)) (Z_to_bv 64 (F + HO_STEREO))
(Z_to_bv 64 (F + HO_FSZ)) v176 (Z_to_bv 64 (h_channels h)) j192 j200 (Z_to_bv 64 F).

Definition hrep (Σ1 : rts RT) (m : mem) (a : haux) (h : hstate unit) (spill : list cell) (ogc opc : list cell) : Prop :=
ART RT Σ1 m /\ mem_inv asegs m /\ stk asegs m lo S1
/\ rt_pres_fp (x_live X) [(F, 8%nat)] S1 h_WL mR m
/\ ERR_rep m /\ (forall so, OUT_rep so mR -> OUT_rep so m) /\ io_ssp m
/\ rw_cells asegs m S1 spill
/\ rw_cells asegs m sf [CB 16 HSH_P1]
/\ (exists je, rw_cells asegs m (F + HO_ENH) [CB 56 je])
/\ (exists ows, rw_cells asegs m (F + HO_OUT) (f32 ows) /\ length ows = 2000%nat)
/\ rw_cells asegs m (F + HO_FSZ) [C4 (Z_to_bv 64 (h_frame_size h))]
/\ bits_rep asegs m (F + HO_BITS) (a_Dc a) (h_bits h)
/\ sync_rep m (F + HO_OY) (a_Dsy a) (h_oy h) (a_sybytes a)
/\ rw_cells asegs m (F + HO_OG) ogc
/\ rw_cells asegs m (F + HO_OP) opc
/\ h_os_rep m a h
/\ (exists stb, rw_cells asegs m (F + HO_STEREO) [CB 24 stb])
/\ rw_cells asegs m (F + HO_RATE) [C4 (Z_to_bv 64 (h_rate h))]
/\ (exists wl, rw_cells asegs m (F + HO_LOOK) [C4 wl])
/\ h_dec_rep m a h
/\ hpure h.

Definition og_junk (ogc : list cell) : Prop := exists j0 j1 j2 j3, ogc = [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3].
Definition op_junk (opc : list cell) : Prop := exists k0 k1 k2 k3 k4 k5, opc = [CB 8 k0; CB 8 k1; CB 8 k2; CB 8 k3; CB 8 k4; CB 8 k5].

Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.
Local Notation PMh := (PMfd F0 fs0).
Local Notation tpv := (Z_to_bv 64 0x630458).
Local Notation Z64 := (Z_to_bv 64).

Definition h_regs (h : hstate unit) (a : haux) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r5 r7 r8 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR ra (Z64 S1) (x_gp X) tpv t0 t1 t2 (Z64 usp) (Z64 S1) a0 a1 a2 a3 a4 a5 a6 a7
(Z64 (F + HO_OP)) (Z64 sf) (Z64 (F + HO_OUT)) r5 (Z64 (h_packet_count h)) r7 r8 (Z64 (a_S a)) (Z64 (F + HO_OG)) (Z64 (F + HO_BITS)) t3 t4 t5 t6.

Definition at_CH (h : hstate unit) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (a : haux) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (ra t0 t1 t2 a1 a4 a5 a6 a7 r5 r7 t3 t4 t5 t6 : word)
(v80 v88 v144 v176 j0 j192 j200 : word) (ogc opc : list cell),
ASTA RT Σ1 PMh (eq (MS (h_regs h a ra t0 t1 t2 (Z64 (h_bytes_remaining h)) a1 (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) a4 a5 a6 a7
r5 r7 (Z64 (h_stream_init h)) t3 t4 t5 t6) Fx (Z64 A_CH) fc None m (seg_rom asegs))) c
/\ X1cn.frm0 fc /\ hsig Σ1 a h
/\ hrep Σ1 m a h (h_spill v80 v88 v144 v176 j0 j192 j200 h) ogc opc /\ og_junk ogc /\ op_junk opc.

Definition h_iter (h : hstate unit) (nbr brem0 : Z) : Prop :=
brem0 - nbr = h_bytes_remaining h /\ 0 <= nbr <= CHUNK /\ nbr <= brem0 <= x_size X.

Definition h_page_budget (h : hstate unit) (og : page) : Prop :=
exists cold, 0 <= cold /\ os_lacing_fill (h_os h) <= cold /\ os_body_fill (h_os h) <= cold
/\ os_lacing_storage (h_os h) <= 1568 + cold /\ os_body_storage (h_os h) <= 17408 + 2 * cold
/\ cold + pg_header_len og + pg_body_len og <= h_consumed h
/\ h_packet_count h <= 162 * cold
/\ h_packet_count h + (os_lacing_fill (h_os h) - os_lacing_returned (h_os h)) <= 162 * cold.

Definition at_PB (h : hstate unit) (og : page) (nbr brem0 : Z) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (a : haux) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (ra t0 t1 t2 a0 a3 a4 a5 a6 a7 r5 r8 t3 t4 t5 t6 : word)
(j0 j192 j200 : word) (opc : list cell),
ASTA RT Σ1 PMh (eq (MS (h_regs h a ra t0 t1 t2 a0 (Z64 (if h_stream_init h =? 0 then 1 else 0)) (Z64 (h_last_granule h)) a3 a4 a5 a6 a7
r5 (Z64 (F + HO_OS)) r8 t3 t4 t5 t6) Fx (Z64 A_PB) fc None m (seg_rom asegs))) c
/\ X1cn.frm0 fc /\ hsig Σ1 a h /\ h_iter h nbr brem0
/\ hrep Σ1 m a h (h_spill (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200 h) (page_cells (a_Dsy a) og) opc
/\ op_junk opc
/\ page_ok (h_oy h) og
/\ h_page_budget h og.

Definition at_PN (h : hstate unit) (nbr brem0 : Z) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (a : haux) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r5 r8 t3 t4 t5 t6 : word)
(j0 j192 j200 : word) (ogc opc : list cell),
ASTA RT Σ1 PMh (eq (MS (h_regs h a ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r5 (Z64 (F + HO_OS)) r8 t3 t4 t5 t6) Fx (Z64 A_PN) fc None m (seg_rom asegs))) c
/\ X1cn.frm0 fc /\ hsig Σ1 a h /\ h_iter h nbr brem0 /\ h_stream_init h = 1
/\ hrep Σ1 m a h (h_spill (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200 h) ogc opc /\ og_junk ogc /\ op_junk opc.
Definition at_PX (h : hstate unit) (nbr brem0 : Z) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (a : haux) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 r5 t3 t4 t5 t6 : word)
(j0 j192 j200 : word) (ogc opc : list cell),
ASTA RT Σ1 PMh (eq (MS (h_regs h a ra t0 t1 t2 a0 a1 (Z64 (h_last_granule h)) a3 a4 a5 a6 a7 r5 (Z64 (F + HO_OS)) (Z64 (h_stream_init h)) t3 t4 t5 t6)
Fx (Z64 A_PX) fc None m (seg_rom asegs))) c
/\ X1cn.frm0 fc /\ hsig Σ1 a h /\ h_iter h nbr brem0
/\ hrep Σ1 m a h (h_spill (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200 h) ogc opc /\ og_junk ogc /\ op_junk opc.

Definition at_KH (h : hstate unit) (packet_no nbr brem0 : Z) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (a : haux) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r5 r7 t3 t4 t5 t6 : word)
(j0 j192 j200 : word) (ogc opc : list cell),
ASTA RT Σ1 PMh (eq (MS (h_regs h a ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r5 r7 (Z64 (1 + h_extra_headers h)) t3 t4 t5 t6) Fx (Z64 A_KH) fc None m (seg_rom asegs))) c
/\ X1cn.frm0 fc /\ hsig Σ1 a h /\ h_iter h nbr brem0 /\ h_stream_init h = 1 /\ h_eos h = 0 /\ 0 <= packet_no
/\ hrep Σ1 m a h (h_spill (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200 h) ogc opc /\ og_junk ogc /\ op_junk opc.

Definition at_DH (h : hstate unit) (st : dec_state unit) (b : bits_st unit) (n : nat) (eosf packet_no nbr brem0 : Z) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (a : haux) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(j0 j192 j200 : word) (ogc opc : list cell),
ASTA RT Σ1 PMh (eq (MS (mkR ra (Z64 S1) (x_gp X) tpv t0 t1 t2 (Z64 usp) (Z64 S1) a0 a1 a2 a3 a4 a5 a6 a7
(Z64 (F + HO_OP)) (Z64 sf) (Z64 (F + HO_OUT)) (Z64 (F + HO_OG)) (Z64 (h_packet_count h)) (Z64 eosf) (Z64 (1 + h_extra_headers h))
(Z64 (a_S a)) (Z64 (Z.of_nat n)) (Z64 (F + HO_BITS)) t3 t4 t5 t6) Fx (Z64 A_DH) fc None m (seg_rom asegs))) c
/\ X1cn.frm0 fc /\ (1 <= n)%nat /\ (eosf = 0 \/ eosf = 1) /\ h_st h <> None
/\ hsig Σ1 a (set_bits_st h b (Some st) (h_eos h)) /\ h_iter h nbr brem0 /\ h_stream_init h = 1
/\ hrep Σ1 m a (set_bits_st h b (Some st) (h_eos h)) (h_spill (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200 h) ogc opc
/\ og_junk ogc /\ op_junk opc.

Definition at_CL (h : hstate unit) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (a : haux) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (ra t0 t1 t2 a3 a4 a5 a6 a7 r5 r8 t3 t4 t5 t6 : word)
(v80 v88 v144 v176 j0 j192 j200 : word) (ogc opc : list cell),
ASTA RT Σ1 PMh (eq (MS (h_regs h a ra t0 t1 t2 (Z64 (a_S a)) (Z64 (F + HO_BITS)) (Z64 (h_stream_init h)) a3 a4 a5 a6 a7 r5 (Z64 (F + HO_OS)) r8 t3 t4 t5 t6)
Fx (Z64 A_CL) fc None m (seg_rom asegs))) c
/\ X1cn.frm0 fc /\ hsig Σ1 a h
/\ hrep Σ1 m a h (h_spill v80 v88 v144 v176 j0 j192 j200 h) ogc opc /\ og_junk ogc /\ op_junk opc.

Definition at_XT : config -> Prop :=
fun c => exists (Σ1 : rts RT) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(w0 w8 w16 w48 w56 w64 w80 w88 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 : word),
ASTA RT Σ1 PMh (eq (MS (mkR ra (Z64 S1) (x_gp X) tpv t0 t1 t2 (Z64 usp) (Z64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z64 sf) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fx (Z64 A_XT) fc None m (seg_rom asegs))) c
/\ X1cn.frm0 fc
/\ rt_live RT Σ1 = x_live X /\ rt_frames RT Σ1 = [(F, 8%nat)] /\ rt_sp0 RT Σ1 = x_sp0 X /\ rt_pois RT Σ1 = [] /\ x_cr0 X - FUZZ_COST + 1 <= rt_credit RT Σ1
/\ ART RT Σ1 m /\ mem_inv asegs m /\ stk asegs m lo S1
/\ rt_pres_fp (x_live X) [(F, 8%nat)] S1 h_WL mR m
/\ ERR_rep m /\ (forall so, OUT_rep so mR -> OUT_rep so m)
/\ rw_cells asegs m S1 (hsp w0 w8 w16 (Z64 (sf + 16)) (Z64 F) (Z64 F) w48 w56 w64 (Z64 (x_d X)) w80 w88 (Z64 SHB) w104 w112 w120 w128 w136 w144 w152 w160 w168
w176 w184 w192 w200 (Z64 F))
/\ rw_cells asegs m sf [CB 16 HSH_P1].

Definition at_EP : config -> Prop :=
fun c => exists (Σ1 : rts RT) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 h0 : word)
(c0 c1 jg : list byte),
ASTA RT Σ1 PMh (eq (MS (mkR ra (Z64 S1) (x_gp X) tpv t0 t1 t2 (Z64 usp) (Z64 S1) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z64 sf) (Z64 F) (Z64 F) (Z64 (-8)) (Z64 (sf + 16)) s8 s9 s10 s11 t3 t4 t5 t6) Fx (Z64 0x9720c) fc None m (seg_rom asegs))) c
/\ X1cn.frm0 fc
/\ rt_live RT Σ1 = x_live X /\ rt_frames RT Σ1 = [(F, 8%nat)] /\ rt_sp0 RT Σ1 = x_sp0 X /\ rt_pois RT Σ1 = [] /\ x_cr0 X - FUZZ_COST <= rt_credit RT Σ1
/\ ART RT Σ1 m /\ mem_inv asegs m /\ stk asegs m lo S1
/\ rw_cells asegs m (sf + 1016) [CB 144 c0] /\ rw_cells asegs m (sf + 16) [CB 1000 c1] /\ rw_cells asegs m F [C8 h0]
/\ rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208)
/\ rw_cells asegs m (S1 + 216) [CB (Z.to_nat (usp - 320 - S1)) jg]
/\ rw_cells asegs m (usp + -104) (h_saves (x_s11 X) (x_s10 X) (x_s9 X) (x_s8 X) (x_s7 X) (x_s6 X) (x_s5 X) (x_s4 X) (x_s3 X) (x_s2 X) (x_s1 X) (x_s0 X) (x_ra X))
/\ rt_pres_fp (x_live X) [] usp IO_FP (x_m0 X) m
/\ (forall a, aclient (x_live X) [] usp a -> ~ (F <= a < F + 16384) /\ ~ (sf <= a < sf + 2048))
/\ ERR_rep m /\ (forall so, OUT_rep so (x_m0 X) -> OUT_rep so m).

Definition h_final (Σ : rts RT) (LIB : mem -> Prop) (fc0 : bv 32) : config -> Prop :=
fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMh (fun ms => exists m', ret_stR fc0 (x_ra X) (Z64 usp) (x_gp X) tpv (x_s0 X) (x_s1 X) (x_s2 X) (x_s3 X) (x_s4 X) (x_s5 X) (x_s6 X) (x_s7 X)
(x_s8 X) (x_s9 X) (x_s10 X) (x_s11 X) (Z64 0) m' ms
/\ rt_after_f RT Σ' usp lo (x_m0 X) m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp (LIB_FP ++ IO_FP) (x_m0 X) m'
/\ LIB m' /\ ERR_rep m' /\ (forall so, OUT_rep so (x_m0 X) -> OUT_rep so m')) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σ'.

Definition ch_nbr (h : hstate unit) : Z := if CHUNK <? h_bytes_remaining h then CHUNK else h_bytes_remaining h.
Definition ch_h1 (h : hstate unit) : hstate unit :=
let nbr := ch_nbr h in
let '(data, oy) := sync_buffer_res (h_oy h) nbr in
let h1 := set_ogg h oy (h_os h) in
let oy := match data with Some (_, off) => sync_write oy off (ztake nbr (x_payload X)) | None => oy end in
let '(_, oy) := ogg_sync_wrote oy nbr in
set_bytes_remaining h1 oy (h_bytes_remaining h1 - nbr).

Definition pb_pre (h : hstate unit) (og : page) : PM (hstate unit) :=
let hdr := page_header (h_oy h) og in
let body := page_body (h_oy h) og in
let serial := ogg_page_serialno hdr in
X1qy.mbind (if h_stream_init h =? 0 then X1qy.mbind (ogg_stream_init p_malloc p_free serial) (fun ro => X1qy.mret (set_stream_init h (snd ro))) else X1qy.mret h) (fun h =>
let h := (if negb (serial =? os_serialno (h_os h)) then let '(r, os) := ogg_stream_reset_serialno (h_os h) serial in set_ogg h (h_oy h) os else h) in
X1qy.mbind (ogg_stream_pagein p_realloc p_free (h_os h) hdr body) (fun ro => X1qy.mret (set_ogg h (h_oy h) (snd ro)))).

Definition h_after_pageout (h : hstate unit) (nbr brem0 : Z) (c : config) : Prop :=
exists r oog oy2, ogg_sync_pageout (h_oy h) = Some ((r, oog), oy2) /\
((r = 1 /\ exists og, oog = Some og /\ at_PB (set_ogg h oy2 (h_os h)) og nbr brem0 c)
\/ (r <> 1 /\ at_PX (set_ogg h oy2 (h_os h)) nbr brem0 c)).

Definition h_chunk_cps : Prop := hinv_ok -> forall h : hstate unit,
0 < h_bytes_remaining h ->
cps asegs (at_CH h) (h_after_pageout (ch_h1 h) (ch_nbr h) (h_bytes_remaining h)).

Definition h_pnext_cps : Prop := hinv_ok -> forall (h : hstate unit) (nbr brem0 : Z),
cps asegs (at_PN h nbr brem0) (h_after_pageout h nbr brem0).

Definition h_pexit_cps : Prop := hinv_ok -> forall (h : hstate unit) (nbr brem0 : Z),
cps asegs (at_PX h nbr brem0) (fun c => (0 < h_bytes_remaining h /\ at_CH h c) \/ (h_bytes_remaining h <= 0 /\ at_CL h c)).

Definition h_page_cps : Prop := hinv_ok -> forall (h : hstate unit) (og : page) (nbr brem0 : Z) (q q3 : pst) (h3 : hstate unit),
prun (pb_pre h og) q = Some (h3, q3) ->
cps asegs (at_PB h og nbr brem0) (fun c => q3 = q /\
match granule_step h3 (page_header (h_oy h) og) with
| None => at_XT c
| Some skip => let h4 := set_granule h3 (ogg_page_granulepos (page_header (h_oy h) og)) skip in
(h_eos h4 = 0 /\ at_KH h4 0 nbr brem0 c) \/ (h_eos h4 <> 0 /\ at_PN h4 nbr brem0 c)
end).

Definition h_clean_cps : Prop := hinv_ok -> forall h : hstate unit,
cps asegs (at_CL h) at_XT.

Definition h_pkt_cps : Prop := hinv_ok -> forall (fuel : nat) (h : hstate unit) (pno nbr brem0 : Z) (q q' : pst) (o : outcome unit),
prun (hP_packet_loop (S fuel) h pno) q = Some (o, q') ->
exists bs, cpsE asegs (at_KH h pno nbr brem0) (Spec.X1nu.evw 2 bs) (fun c => exists q1, p_err q1 = p_err q ++ bs /\
( (o = Returned /\ q1 = q' /\ at_XT c)
\/ (exists h1, o = Cont h1 /\ q1 = q' /\ at_PN h1 nbr brem0 c)
\/ (exists h1 pno1, h_eos h1 = 0 /\ prun (hP_packet_loop fuel h1 pno1) q1 = Some (o, q') /\ at_KH h1 pno1 nbr brem0 c))).

End Ctx.
