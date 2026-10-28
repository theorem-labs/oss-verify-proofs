(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bq X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qp X0pv X0pt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1nt X1rg X1rh X1re X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Notation rsegs := X1gj.rsegs.

Definition A_speex_packet_to_header : Z := 0x1da58.
Definition A_speex_lib_get_mode : Z := 0x2b9bc.
Definition A_speex_decoder_init : Z := 0x1cf08.
Definition A_speex_decoder_destroy : Z := 0x1cf48.
Definition A_speex_decode : Z := 0x1cfe8.
Definition A_speex_decoder_ctl : Z := 0x1d010.
Definition A_speex_decode_stereo : Z := 0x1d114.
Definition A_speex_std_stereo_request_handler : Z := 0x1d280.
Definition A_bcmp : Z := 0x39b5c.
Definition A_memcmp : Z := 0x39c2c.
Definition A_cleanup : Z := 0x1c7e0.

Definition A_speex_nb_mode : Z := 0x3b7c8.
Definition A_speex_wb_mode : Z := 0x3bbb8.
Definition A_speex_uwb_mode : Z := 0x3bc18.
Definition A_speex_mode_list : Z := 0x3bc78.
Definition GOT_speex_nb_mode : Z := 0x3c088.
Definition GOT_stereo_handler : Z := 0x3c050.
Definition mode_addr (mo : spx_mode) : Z :=
match mo with ModeNB => A_speex_nb_mode | ModeWB => A_speex_wb_mode | ModeUWB => A_speex_uwb_mode end.

Definition SPEEX_SET_ENH : Z := 0.
Definition SPEEX_GET_FRAME_SIZE : Z := 3.
Definition SPEEX_SET_HANDLER : Z := 20.
Definition SPEEX_SET_SAMPLING_RATE : Z := 24.
Definition SPEEX_GET_LOOKAHEAD : Z := 39.

Definition DEC_INIT_STACK : Z := 65536.
Definition DEC_DESTROY_STACK : Z := 16384.
Definition DEC_CTL_STACK : Z := 1024.
Definition DECODE_STACK : Z := 262144.
Definition DECODE_STEREO_STACK : Z := 1024.
Definition PKT2HDR_STACK : Z := 16384.

Section Stmts.
Context {RCEIL : RunCeiling}.
Variable dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop.

Definition dec_rep_frame_stmt : Prop :=
forall STEREO m m' S d LBD,
dec_rep STEREO m S d LBD ->
(forall a, 0 <= a < 2^64 -> in_block LBD a ->
m' (wa a) = m (wa a) /\ (wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None)) ->
dec_rep STEREO m' S d LBD.

Definition rspx_decoder_init_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(s : PState) (LB : list block) (AB lo : Z) (mo : spx_mode) (m : mem)
(r : option (dec_state bptr)) (s' : PState) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ frm0 fc'
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' AB
/\ rheap_pres LB (bv_unsigned sp) m m'
/\ ps_so s' = ps_so s
/\ match r with
| None => a0 = wz 0 /\ RHEAP s' LB m'
| Some d => exists S LBD, a0 = wz S /\ 0 < S < 2^63 /\ RHEAP s' (LBD ++ LB) m'
/\ (forall STEREO, dec_rep STEREO m' S d LBD)
/\ dec_mode d = mo
end.

Definition rspx_decoder_init_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (mo : spx_mode) (AB lo : Z) (errv : word),
RHEAP s LB m -> rtables_pristine m ->
rauxv_ok m AB -> bv_unsigned sp <= AB -> AB < 2^62 ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - DEC_INIT_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m -> frm0 fc ->
tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
a0 = wz (mode_addr mo) ->
implM rsegs (speex_decoder_init raw_calloc raw_free mo) s
(rspx_decoder_init_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo mo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz A_speex_decoder_init) fc None m (seg_rom rsegs)).

Definition rspx_decoder_destroy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(s : PState) (LBr : list block) (AB lo : Z) (m : mem)
(r : unit) (s' : PState) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ frm0 fc'
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' AB
/\ rheap_pres LBr (bv_unsigned sp) m m'
/\ ps_so s' = ps_so s
/\ RHEAP s' LBr m'.

Definition rspx_decoder_destroy_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB LBD LBr : list block) (STEREO S : Z) (d : dec_state bptr) (AB lo : Z) (errv : word),
RHEAP s LB m -> Permutation LB (LBD ++ LBr) -> dec_rep STEREO m S d LBD -> rtables_pristine m ->
rauxv_ok m AB -> bv_unsigned sp <= AB -> AB < 2^62 ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - DEC_DESTROY_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m -> frm0 fc ->
tp = wz RATP ->
a0 = wz S ->
implM rsegs (speex_decoder_destroy raw_free d) s
(rspx_decoder_destroy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LBr AB lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz A_speex_decoder_destroy) fc None m (seg_rom rsegs)).

Inductive ctl_arg : Type :=
| ArgIntIn (v : Z)
| ArgIntOut
| ArgCallback.

Definition ctl_req_of (code : Z) (arg : ctl_arg) : option ctl_req :=
match arg with
| ArgIntIn v => if code =? SPEEX_SET_ENH then Some (CtlSetEnh v)
else if code =? SPEEX_SET_SAMPLING_RATE then Some (CtlSetSamplingRate v) else None
| ArgIntOut => if code =? SPEEX_GET_FRAME_SIZE then Some CtlGetFrameSize
else if code =? SPEEX_GET_LOOKAHEAD then Some CtlGetLookahead else None
| ArgCallback => if code =? SPEEX_SET_HANDLER then Some CtlSetHandlerStereo else None
end.

Definition ctl_arg_pre (STEREO : Z) (m : mem) (P : Z) (arg : ctl_arg) : Prop :=
match arg with
| ArgIntIn v => exists w : word, rw_cells rsegs m P [C4 w] /\ bv_unsigned w mod 2^32 = v mod 2^32 /\ -2^31 <= v < 2^31
| ArgIntOut => exists bs : list byte, rw_cells rsegs m P [CB 4 bs]
| ArgCallback => exists pad : list byte,
rw_cells rsegs m P [C4 (wz SPEEX_INBAND_STEREO); CB 4 pad; C8 (wz A_speex_std_stereo_request_handler); C8 (wz STEREO)]
end.
Definition ctl_arg_post (STEREO : Z) (m : mem) (P : Z) (arg : ctl_arg) (v : Z) : Prop :=
match arg with
| ArgIntIn v0 => exists w : word, rw_cells rsegs m P [C4 w] /\ bv_unsigned w mod 2^32 = v0 mod 2^32
| ArgIntOut => rw_cells rsegs m P [C4 (wz v)] /\ -2^31 <= v < 2^31
| ArgCallback => exists pad : list byte,
rw_cells rsegs m P [C4 (wz SPEEX_INBAND_STEREO); CB 4 pad; C8 (wz A_speex_std_stereo_request_handler); C8 (wz STEREO)]
end.
Definition ctl_arg_size (arg : ctl_arg) : Z := match arg with ArgCallback => 24 | _ => 4 end.
Definition ctl_arg_ptr_ok (P : Z) (arg : ctl_arg) : Prop :=
match arg with ArgCallback => 0 < P /\ P mod 8 = 0 | _ => 0 < P /\ P mod 4 = 0 end.

Definition ctl_req_fits (r : ctl_req) : Prop := match r with CtlSetEnh v => v = 0 \/ v = 1 | _ => True end.

Definition rspx_decoder_ctl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(STEREO S : Z) (d : dec_state bptr) (LBD : list block) (code P : Z) (arg : ctl_arg) (lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (req : ctl_req),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ ctl_req_of code arg = Some req
/\ munch ((lo, bv_unsigned sp) :: (P, P + ctl_arg_size arg) :: map (fun b => (blk_addr b, blk_addr b + blk_size b)) LBD) m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ a0 = wz 0
/\ dec_rep STEREO m' S (snd (speex_decoder_ctl d req)) LBD
/\ ctl_arg_post STEREO m' P arg (fst (speex_decoder_ctl d req)).

Definition rspx_decoder_ctl_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(STEREO S : Z) (d : dec_state bptr) (LBD : list block) (code P : Z) (arg : ctl_arg) (req : ctl_req) (lo : Z),
dec_rep STEREO m S d LBD -> ctl_req_of code arg = Some req -> ctl_req_fits req -> ctl_arg_pre STEREO m P arg -> ctl_arg_ptr_ok P arg -> bv_unsigned sp mod 16 = 0 -> rtables_pristine m ->
(forall b, In b LBD -> rblock_range (blk_addr b) (blk_size b)) ->
(P + ctl_arg_size arg <= lo \/ bv_unsigned sp <= P) -> (forall b, In b LBD -> P + ctl_arg_size arg <= blk_addr b \/ blk_addr b + blk_size b <= P) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - DEC_CTL_STACK ->
mem_inv rsegs m -> frm0 fc ->
a0 = wz S -> a1 = wz code -> a2 = wz P ->
evt rsegs (rspx_decoder_ctl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 STEREO S d LBD code P arg lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz A_speex_decoder_ctl) fc None m (seg_rom rsegs)).

Definition HOUT_BYTES : Z := 8000.

Definition rspx_decode_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(st : PState) (STEREO S : Z) (LBD : list block) (b : bits_st bptr) (BITS Dc OUT lo : Z) (m : mem)
(r : Z * dec_state bptr * bits_st bptr) (st' : PState) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (outb stb : list byte),
let '(ret, d', b') := r in
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz ret) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ -2 <= ret <= 0
/\ frm0 fc'
/\ munch ((lo, bv_unsigned sp) :: (BITS, BITS + 48) :: (OUT, OUT + HOUT_BYTES) :: (STEREO, STEREO + 24)
:: (RSTDERR, RSTDERR + 232) :: map (fun b => (blk_addr b, blk_addr b + blk_size b)) LBD) m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ dec_rep STEREO m' S d' LBD
/\ bits_rep rsegs m' BITS Dc b' /\ bits_ok b'
/\ sb_owner b' = sb_owner b /\ sb_chars b' = sb_chars b /\ sb_buf_size b' = sb_buf_size b
/\ u8arr rsegs m' OUT outb /\ Z.of_nat (length outb) = HOUT_BYTES
/\ rw_cells rsegs m' STEREO [CB 24 stb]
/\ stderr_wfile m'
/\ st' = st.

Definition rspx_decode_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(st : PState) (LB : list block) (STEREO S : Z) (d : dec_state bptr) (LBD : list block) (b : bits_st bptr) (BITS Dc OUT lo : Z)
(outb stb : list byte) (canary : word),
dec_rep STEREO m S d LBD -> RHEAP st LB m -> (forall x, In x LBD -> In x LB) ->
bits_rep rsegs m BITS Dc b -> bits_ok b -> sb_owner b = 1 -> In (sb_chars b, Dc, sb_buf_size b) LB ->
(forall x, In x LBD -> blk_id x <> sb_chars b) ->
u8arr rsegs m OUT outb -> Z.of_nat (length outb) = HOUT_BYTES -> rw_cells rsegs m STEREO [CB 24 stb] ->
rtables_pristine m -> stderr_wfile m -> ssp_cells m canary ->

(BITS + 48 <= OUT \/ OUT + HOUT_BYTES <= BITS) -> (BITS + 48 <= STEREO \/ STEREO + 24 <= BITS) ->
(OUT + HOUT_BYTES <= STEREO \/ STEREO + 24 <= OUT) ->
(BITS + 48 <= lo \/ bv_unsigned sp <= BITS) -> (OUT + HOUT_BYTES <= lo \/ bv_unsigned sp <= OUT) ->
(STEREO + 24 <= lo \/ bv_unsigned sp <= STEREO) ->
alloc_ceiling <= BITS -> alloc_ceiling <= OUT -> alloc_ceiling <= STEREO ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - DECODE_STACK ->
(bv_unsigned sp < 2^63) ->
bv_unsigned sp mod 16 = 0 -> OUT mod 4 = 0 -> STEREO mod 4 = 0 ->
mem_inv rsegs m -> frm0 fc ->
tp = wz RATP ->
a0 = wz S -> a1 = wz BITS -> a2 = wz OUT ->
implM rsegs (speex_decode io_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M d b 0) st
(rspx_decode_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 st STEREO S LBD b BITS Dc OUT lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz A_speex_decode) fc None m (seg_rom rsegs)).

Definition rspx_decode_stereo_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(OUT STEREO lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem)
(outb : list byte) (stb : list byte),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ frm0 fc'
/\ munch [(lo, bv_unsigned sp); (OUT, OUT + HOUT_BYTES); (STEREO, STEREO + 24)] m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ u8arr rsegs m' OUT outb /\ Z.of_nat (length outb) = HOUT_BYTES
/\ rw_cells rsegs m' STEREO [CB 24 stb].

Definition rspx_decode_stereo_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(OUT STEREO lo frame_size : Z) (outb stb : list byte),
u8arr rsegs m OUT outb -> Z.of_nat (length outb) = HOUT_BYTES -> rw_cells rsegs m STEREO [CB 24 stb] ->
0 <= frame_size <= 640 ->
(OUT + HOUT_BYTES <= STEREO \/ STEREO + 24 <= OUT) ->
(OUT + HOUT_BYTES <= lo \/ bv_unsigned sp <= OUT) -> (STEREO + 24 <= lo \/ bv_unsigned sp <= STEREO) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - DECODE_STEREO_STACK ->
mem_inv rsegs m -> frm0 fc ->
a0 = wz OUT -> a1 = wz frame_size -> a2 = wz STEREO ->
0 < OUT -> OUT mod 4 = 0 -> 0 < STEREO -> STEREO mod 4 = 0 ->
evt rsegs (rspx_decode_stereo_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 OUT STEREO lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz A_speex_decode_stereo) fc None m (seg_rom rsegs)).
End Stmts.

Definition SIZEOF_SPEEX_HEADER_Z : Z := 80.
Definition spx_header_cells (junk28 : list byte) (hd : spx_header) (bitrate_w fsz_w vbr_w r1 r2 : word) : list cell :=
[CB 28 junk28;
C4 (wz (hd_speex_version_id hd)); C4 (wz (hd_header_size hd)); C4 (wz (hd_rate hd)); C4 (wz (hd_mode hd));
C4 (wz (hd_mode_bitstream_version hd)); C4 (wz (hd_nb_channels hd));
C4 bitrate_w; C4 fsz_w; C4 vbr_w;
C4 (wz (hd_frames_per_packet hd)); C4 (wz (hd_extra_headers hd)); C4 r1; C4 r2].

Definition rspx_packet_to_header_post {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(s : PState) (LB : list block) (AB lo : Z) (canary : word) (m : mem)
(r : option (bptr * spx_header)) (s' : PState) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem) (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ frm0 fc'
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' AB
/\ pres_except rsegs (rclient_addr LB (bv_unsigned sp)) [(RSTDERR, RSTDERR + 232)] m m'
/\ stderr_wfile m' /\ ssp_cells m' canary
/\ ps_so s' = ps_so s
/\ match r with
| None => a0 = wz 0 /\ RHEAP s' LB m'
| Some (blk, hd) => exists HB junk28 w1 w2 w3 r1 r2,
a0 = wz HB /\ rblock_range HB SIZEOF_SPEEX_HEADER_Z
/\ RHEAP s' ((blk, HB, SIZEOF_SPEEX_HEADER_Z) :: LB) m'
/\ rw_cells rsegs m' HB (spx_header_cells junk28 hd w1 w2 w3 r1 r2)
/\ -2^31 <= hd_speex_version_id hd < 2^31 /\ -2^31 <= hd_rate hd < 2^31 /\ 0 <= hd_mode hd < SPEEX_NB_MODES
/\ -2^31 <= hd_mode_bitstream_version hd < 2^31 /\ -2^31 <= hd_nb_channels hd < 2^31
/\ -2^31 <= hd_frames_per_packet hd < 2^31 /\ -2^31 <= hd_extra_headers hd < 2^31
end.

Definition rspx_packet_to_header_stmt {RCEIL : RunCeiling} : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (pblk : block) (P size : Z) (pbytes : list byte) (AB lo : Z) (errv canary : word),
RHEAP s LB m -> In pblk LB -> blk_addr pblk <= P -> P + Z.of_nat (length pbytes) <= blk_addr pblk + blk_size pblk ->
u8ro rsegs m P pbytes -> 0 <= size <= Z.of_nat (length pbytes) -> size < 2^31 ->
rtables_pristine m -> stderr_wfile m -> ssp_cells m canary ->
rauxv_ok m AB -> bv_unsigned sp <= AB -> AB < 2^62 ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - PKT2HDR_STACK ->
(bv_unsigned sp < 2^63) ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m -> frm0 fc ->
tp = wz RATP ->
a0 = wz P -> a1 = wz size ->
P mod 4 = 0 ->
implM rsegs (speex_packet_to_header raw_calloc raw_free io_notify (map bv_unsigned pbytes) size) s
(rspx_packet_to_header_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz A_speex_packet_to_header) fc None m (seg_rom rsegs)).

Lemma align_of_usp : forall (u k a : Z), u mod 16 = 0 -> (a = 4 \/ a = 8 \/ a = 16) -> k mod a = 0 -> (u + k) mod a = 0.
Proof. intros u k a U Ha K. destruct Ha as [-> | [-> | ->]]; Z.div_mod_to_equations; lia. Qed.
