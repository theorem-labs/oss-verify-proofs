(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_fuzz : Z := 0x9635c.             (* [comment removed for export] *)
Definition e_devnull : Z := 0x96630.          (* [comment removed for export] *)
Definition e_returnErrorInt : Z := 0x9666c.
Definition e_lept_stderr : Z := 0x966a0.
Definition e_returnErrorPtr : Z := 0x968d0.
Definition e_setStderrHandler : Z := 0x9695c.
Definition e_pixCreate : Z := 0x99174.
Definition e_pixCreateNoInit : Z := 0x992a0.
Definition e_pixCreateHeader : Z := 0x9964c.
Definition e_pixGetWpl : Z := 0x99c18.
Definition e_pixDestroy : Z := 0x99cc8.
Definition e_pixGetDimensions : Z := 0x9a4cc.
Definition e_pixSetColormap : Z := 0x9b020.
Definition e_pixGetHeight : Z := 0x9ba10.
Definition e_pixGetDepth : Z := 0x9c2ec.
Definition e_pixGetData : Z := 0x9c5cc.
Definition e_pixGetWidth : Z := 0x9c714.
Definition e_pixSetSpecial : Z := 0x8dc10.
Definition e_pixSetPadBits : Z := 0x9e60c.
Definition e_pixcmapIsValid : Z := 0xa1660.
Definition e_pixcmapDestroy : Z := 0xa1d80.
Definition e_pixcmapDeserialize : Z := 0xa3aec.
Definition e_pixGetMaxColorIndex : Z := 0xa4990.
Definition e_pixZero : Z := 0xaf234.
Definition e_pixSetChromaSampling : Z := 0x8f590.
Definition e_pixReadMemSpix : Z := 0xbe900.   (* [comment removed for export] *)
Definition e_pixDeserialize : Z := 0xbe904.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition g_LeptMsgSeverity : Z := 0x102120.   (* [comment removed for export] *)
Definition g_stderr_handler : Z := 0x102140.    (* [comment removed for export] *)
Definition g_pix_alloc : Z := 0x102160.         (* [comment removed for export] *)
Definition g_pix_dealloc : Z := 0x102180.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition LIB0 (m : mem) : Prop :=
  rw_cells asegs m g_LeptMsgSeverity [C4 (Z_to_bv 64 3)]
  /\ rw_cells asegs m g_pix_alloc [C8 (Z_to_bv 64 e_malloc)] /\ rw_cells asegs m g_pix_dealloc [C8 (Z_to_bv 64 e_free)].
Definition LIB (m : mem) : Prop := LIB0 m /\ exists h : word, rw_cells asegs m g_stderr_handler [C8 h].
Definition LIBH (m : mem) : Prop := LIB0 m /\ rw_cells asegs m g_stderr_handler [C8 (Z_to_bv 64 e_devnull)].
Definition LIB_FP : list (Z * Z) := [(g_stderr_handler, g_stderr_handler + 8)].

(* [comment removed for export] *)
Fixpoint lept_args_lit (kinds : list bool) (ws : list word) : Prop :=
  match kinds, ws with
  | [], _ => True
  | true :: ks, w :: ws' => (exists l, In (bv_unsigned w, l) LEPT_LITS) /\ lept_args_lit ks ws'
  | false :: ks, _ :: ws' => lept_args_lit ks ws'
  | _ :: _, [] => False
  end.

(* [comment removed for export] *)
Definition lit_pad (r : Z * Z) : Z := (- (fst r + snd r)) mod 8.
Definition lit_ok (r : Z * Z) : bool :=
  match image_bytes asegs (fst r) (Z.to_nat (snd r + lit_pad r)) with
  | Some bs => ro_bytes_b asegs (fst r) bs
               && match rev (firstn (Z.to_nat (snd r)) bs) with
                  | z :: str => Z.eqb (bv_unsigned z) 0 && forallb (fun b => negb (Z.eqb (bv_unsigned b) 0)) str
                  | [] => false
                  end
               && Z.leb 0x10000 (fst r) && Z.leb (fst r + snd r + lit_pad r) 0x2e67c && Z.ltb (snd r) 97 && Z.ltb 0 (snd r)
  | None => false
  end.
Lemma lept_lits_ok : forallb lit_ok LEPT_LITS = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LSTK (k : Z) : Z := RT_STACK + 1024 * k.
Definition STDERR_STACK : Z := RT_STACK + 256.

Section Iface.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition lept_stderr_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (fmt : Z) (kinds : list bool) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 fmt -> tp = Z_to_bv 64 TP_A ->
  In (fmt, kinds) LEPT_FMTS -> lept_args_lit kinds [a1; a2; a3; a4; a5; a6; a7] ->
  LIBH m -> io_ssp m -> ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + STDERR_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_lept_stderr m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists v m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
          /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
          /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m' /\ LIBH m' /\ io_ssp m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ
       /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ - 1).

(* [comment removed for export] *)
Definition lenv (Σ : rts RT) (m : mem) (sp : word) (lo need : Z) : Prop :=
  LIBH m /\ io_ssp m /\ ART RT Σ m /\ mem_inv asegs m /\ stk asegs m lo (bv_unsigned sp)
  /\ rt_sp0 RT Σ - STACK_WIN <= lo /\ lo + need <= bv_unsigned sp
  /\ bv_unsigned sp + 16 <= USTACK_TOP /\ bv_unsigned sp mod 16 = 0 /\ bv_unsigned sp <= rt_sp0 RT Σ.
(* [comment removed for export] *)
Definition lpost (Σ Σ' : rts RT) (m m' : mem) (sp : word) (lo : Z) : Prop :=
  rt_after RT Σ' (bv_unsigned sp) lo m m' /\ LIBH m' /\ io_ssp m'.
(* [comment removed for export] *)
Definition lpost_f (Σ Σ' : rts RT) (m m' : mem) (sp : word) (lo : Z) : Prop :=
  rt_after_f RT Σ' (bv_unsigned sp) lo m m' /\ LIBH m' /\ io_ssp m'.

(* [comment removed for export] *)
Definition returnError_cps (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  (exists l, In (bv_unsigned a0, l) LEPT_LITS) -> (exists l, In (bv_unsigned a1, l) LEPT_LITS) ->
  lenv Σ m sp lo (LSTK 2) ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc entry m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 m' ms
          /\ lpost Σ Σ' m m' sp lo
          /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ
       /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ - 1).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record pixv : Type := mkPixv { p_w : Z; p_h : Z; p_d : Z; p_spp : Z; p_wpl : Z; p_xres : Z; p_yres : Z; p_inf : Z; p_spec : Z;
                               p_cmap : Z; p_data : Z }.
Definition pix_cells (v : pixv) : list cell :=
  [C4 (Z_to_bv 64 (p_w v)); C4 (Z_to_bv 64 (p_h v)); C4 (Z_to_bv 64 (p_d v)); C4 (Z_to_bv 64 (p_spp v)); C4 (Z_to_bv 64 (p_wpl v));
   C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 (p_xres v)); C4 (Z_to_bv 64 (p_yres v)); C4 (Z_to_bv 64 (p_inf v)); C4 (Z_to_bv 64 (p_spec v));
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (p_cmap v)); C8 (Z_to_bv 64 (p_data v))].
(* [comment removed for export] *)
Definition pix_hdr_ok (v : pixv) : Prop :=
  In (p_d v) [1; 2; 4; 8; 16; 24; 32] /\ 0 < p_w v <= 20000 /\ 0 < p_h v <= 20000
  /\ p_wpl v = (p_w v * p_d v + 31) / 32 /\ 0 < 4 * (p_wpl v * p_h v) <= 0x4000000.
Definition rsize (v : pixv) : Z := 4 * (p_wpl v * p_h v).

(* [comment removed for export] *)
Record cmapv : Type := mkCmapv { c_arr : Z; c_depth : Z; c_nalloc : Z; c_n : Z }.
Definition cmap_cells (cv : cmapv) (pad : list byte) : list cell :=
  [C8 (Z_to_bv 64 (c_arr cv)); C4 (Z_to_bv 64 (c_depth cv)); C4 (Z_to_bv 64 (c_nalloc cv)); C4 (Z_to_bv 64 (c_n cv)); CB 4 pad].
Definition cmap_ok (cv : cmapv) : Prop := In (c_depth cv) [1; 2; 4; 8] /\ c_nalloc cv = 2 ^ c_depth cv /\ 0 <= c_n cv <= c_nalloc cv.

(* [comment removed for export] *)
Definition chunk (live : list (Z * Z)) (p n : Z) : Prop := In (p, n) live /\ 0 < p /\ p mod 16 = 0 /\ 0 < n.

(* [comment removed for export] *)
Definition cmap_obj (live : list (Z * Z)) (m : mem) (cmap : Z) (cv : cmapv) : Prop :=
  (exists pad, rw_cells asegs m cmap (cmap_cells cv pad)) /\ chunk live cmap 24 /\ chunk live (c_arr cv) (4 * c_nalloc cv)
  /\ cmap_ok cv /\ c_arr cv <> cmap.
(* [comment removed for export] *)
Definition pix_obj (live : list (Z * Z)) (m : mem) (pix : Z) (v : pixv) (cv : cmapv) : Prop :=
  rw_cells asegs m pix (pix_cells v) /\ chunk live pix 64 /\ pix_hdr_ok v
  /\ (p_data v = 0 \/ (chunk live (p_data v) (rsize v) /\ p_data v <> pix))
  /\ (p_cmap v = 0 \/ (cmap_obj live m (p_cmap v) cv /\ p_cmap v <> pix /\ c_arr cv <> pix
                        /\ p_cmap v <> p_data v /\ c_arr cv <> p_data v)).

(* [comment removed for export] *)
Definition rm_opt (p : Z) (live : list (Z * Z)) : list (Z * Z) := if p =? 0 then live else live_remove p live.
Definition live_destroy (pix : Z) (v : pixv) (cv : cmapv) (live : list (Z * Z)) : list (Z * Z) :=
  live_remove pix (rm_opt (p_cmap v) (rm_opt (if p_cmap v =? 0 then 0 else c_arr cv) (rm_opt (p_data v) live))).

(* [comment removed for export] *)
Definition uctx (m : mem) (sp s0 : word) (ras : list Z) : Prop := chain_ok m (bv_unsigned sp) (bv_unsigned s0) ras.

(* [comment removed for export] *)
Definition lres (Σ : rts RT) (frames chunks cost : Z) : Prop :=
  Z.of_nat (length (rt_frames RT Σ)) + frames <= Z.of_nat FRAMES_MAX
  /\ Z.of_nat (length (rt_live RT Σ)) + chunks <= LIVE_MAX /\ cost <= rt_credit RT Σ
  /\ (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n).

(* [comment removed for export] *)
Definition keepsL (live : list (Z * Z)) (Σ : rts RT) (sp : word) (W : list (Z * Z)) (m m' : mem) : Prop :=
  rt_pres_fp live (rt_frames RT Σ) (bv_unsigned sp) W m m'.
(* [comment removed for export] *)
Definition keeps (Σ Σ' : rts RT) (sp : word) (W : list (Z * Z)) (m m' : mem) : Prop := keepsL (rt_live RT Σ') Σ sp W m m'.

(* [comment removed for export] *)
Definition s32 (w : word) (z : Z) : Prop := - 2^31 <= z < 2^31 /\ w = Z_to_bv 64 z.
(* [comment removed for export] *)
Definition optrL (live : list (Z * Z)) (Σ : rts RT) (m : mem) (p n : Z) : Prop :=
  accok live (rt_frames RT Σ) m p n /\ 0 < p /\ p mod 8 = 0
  /\ (p + n <= 0x7fff7000 \/ 0x10007fff8000 <= p) /\ (p + n <= 0x10000 \/ SEGTOP_A <= p).
Definition optr (Σ : rts RT) (m : mem) (p n : Z) : Prop := optrL (rt_live RT Σ) Σ m p n.
(* [comment removed for export] *)
Definition optrF (Σ : rts RT) (m : mem) (p n : Z) : Prop :=
  own_frame (rt_frames RT Σ) m p n /\ 0 < p /\ p mod 8 = 0
  /\ (p + n <= 0x7fff7000 \/ 0x10007fff8000 <= p) /\ (p + n <= 0x10000 \/ SEGTOP_A <= p).

Definition RASTER_COST : Z := 2 * 0x4000000 + 16384.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pixCreateHeader_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (w h d : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  s32 a0 w -> s32 a1 h -> s32 a2 d ->
  lenv Σ m sp lo (LSTK 3) -> lres Σ 1 1 2 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreateHeader m)))
    (fun c => exists (Σ' : rts RT) (pix : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) m' ms
          /\ lpost Σ Σ' m m' sp lo /\ keepsL (rt_live RT Σ) Σ sp [] m m'
          /\ (pix = 0 \/ (pix_obj (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) /\ p_w v = w /\ p_h v = h /\ p_d v = d /\ p_data v = 0 /\ p_cmap v = 0))) c
       /\ rt_live RT Σ' = (if pix =? 0 then rt_live RT Σ else (pix, 64) :: rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixCreate_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (w h d : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  s32 a0 w -> s32 a1 h -> s32 a2 d ->
  lenv Σ m sp lo (LSTK 5) -> lres Σ 3 2 (RASTER_COST + 8) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixCreate m)))
    (fun c => exists (Σ' : rts RT) (pix : Z) (v : pixv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) m' ms
          /\ lpost Σ Σ' m m' sp lo /\ keepsL (rt_live RT Σ) Σ sp [] m m'
          /\ (pix = 0 \/ (pix_obj (rt_live RT Σ') m' pix v (mkCmapv 0 0 0 0) /\ p_w v = w /\ p_h v = h /\ p_d v = d /\ p_data v <> 0 /\ p_cmap v = 0))) c
       /\ rt_live RT Σ' = (if pix =? 0 then rt_live RT Σ else (p_data v, rsize v) :: (pix, 64) :: rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 8) <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixDestroy_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pp pix : Z) (v : pixv) (cv : cmapv) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pp -> optrL (live_destroy pix v cv (rt_live RT Σ)) Σ m pp 8 -> rw_cells asegs m pp [C8 (Z_to_bv 64 pix)] ->
  pix_obj (rt_live RT Σ) m pix v cv ->
  uctx m sp s0 ras -> Forall (fun f => In (f :: bv_unsigned ra :: ras) CLIENT_TRACES) DESTROY_FREE_RAS ->
  lenv Σ m sp lo (LSTK 4) -> lres Σ 1 0 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost_f Σ Σ' m m' sp lo /\ keeps Σ Σ' sp [(pp, pp + 8)] m m' /\ rw_cells asegs m' pp [C8 (Z_to_bv 64 0)]) c
       /\ rt_live RT Σ' = live_destroy pix v cv (rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixcmapDestroy_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pc cmap : Z) (cv : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pc -> optrL (live_remove cmap (live_remove (c_arr cv) (rt_live RT Σ))) Σ m pc 8 ->
  rw_cells asegs m pc [C8 (Z_to_bv 64 cmap)] -> cmap_obj (rt_live RT Σ) m cmap cv ->
  lenv Σ m sp lo (LSTK 2) -> lres Σ 0 0 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixcmapDestroy m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost_f Σ Σ' m m' sp lo /\ keeps Σ Σ' sp [(pc, pc + 8)] m m' /\ rw_cells asegs m' pc [C8 (Z_to_bv 64 0)]) c
       /\ rt_live RT Σ' = live_remove cmap (live_remove (c_arr cv) (rt_live RT Σ))
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 0 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixcmapDeserialize_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (dp ncolors : Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 dp -> a1 = Z_to_bv 64 4 -> a2 = Z_to_bv 64 ncolors -> 0 < ncolors <= 256 -> dp mod 4 = 0 ->
  own_live (rt_live RT Σ) dp (4 * ncolors) ->
  lenv Σ m sp lo (LSTK 3) -> lres Σ 0 2 2 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixcmapDeserialize m)))
    (fun c => exists (Σ' : rts RT) (cmap : Z) (cv : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 cmap) m' ms
          /\ lpost Σ Σ' m m' sp lo /\ keepsL (rt_live RT Σ) Σ sp [] m m' /\ (cmap = 0 \/ (cmap_obj (rt_live RT Σ') m' cmap cv /\ c_n cv = ncolors))) c
       /\ rt_live RT Σ' = (if cmap =? 0 then rt_live RT Σ else (c_arr cv, 4 * c_nalloc cv) :: (cmap, 24) :: rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixcmapIsValid_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (cmap pix pv : Z) (cv : cmapv) (v : pixv) (x : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 cmap -> a1 = Z_to_bv 64 pix -> a2 = Z_to_bv 64 pv -> cmap_obj (rt_live RT Σ) m cmap cv ->
  (pix = 0 \/ (pix_obj (rt_live RT Σ) m pix v cv /\ p_data v <> 0 /\ p_cmap v = cmap)) -> optrF Σ m pv 4 -> rw_cells asegs m pv [C4 x] ->
  lenv Σ m sp lo (LSTK 5) -> lres Σ 2 0 4 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixcmapIsValid m)))
    (fun c => exists (Σ' : rts RT) (rv y : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost Σ Σ' m m' sp lo /\ keeps Σ Σ' sp [(pv, pv + 4)] m m' /\ rw_cells asegs m' pv [C4 y]) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 4 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixSetColormap_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix cmap : Z) (v : pixv) (cv : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 cmap -> pix_obj (rt_live RT Σ) m pix v cv -> p_cmap v = 0 -> p_data v <> 0 ->
  cmap_obj (rt_live RT Σ) m cmap cv -> cmap <> pix -> c_arr cv <> pix -> cmap <> p_data v -> c_arr cv <> p_data v ->
  lenv Σ m sp lo (LSTK 6) -> lres Σ 3 0 6 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixSetColormap m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost Σ Σ' m m' sp lo /\ keeps Σ Σ' sp [(pix + 48, pix + 56)] m m'
          /\ rw_cells asegs m' pix (pix_cells (mkPixv (p_w v) (p_h v) (p_d v) (p_spp v) (p_wpl v) (p_xres v) (p_yres v) (p_inf v) (p_spec v) cmap (p_data v)))) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 6 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixSetPadBits_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix : Z) (v : pixv) (cv : cmapv),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 0 -> pix_obj (rt_live RT Σ) m pix v cv -> p_data v <> 0 ->
  lenv Σ m sp lo (LSTK 3) -> lres Σ 2 0 3 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixSetPadBits m)))
    (fun c => exists (Σ' : rts RT) (rv : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost Σ Σ' m m' sp lo /\ keeps Σ Σ' sp [(p_data v, p_data v + rsize v)] m m') c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 3 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixZero_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix pe : Z) (v : pixv) (cv : cmapv) (x : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 pe -> pix_obj (rt_live RT Σ) m pix v cv -> p_data v <> 0 -> optrF Σ m pe 4 ->
  rw_cells asegs m pe [C4 x] ->
  lenv Σ m sp lo (LSTK 3) -> lres Σ 0 0 0 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixZero m)))
    (fun c => exists (Σ' : rts RT) (rv y : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost Σ Σ' m m' sp lo /\ keeps Σ Σ' sp [(pe, pe + 4)] m m' /\ rw_cells asegs m' pe [C4 y]) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 0 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixGetMaxColorIndex_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix pmax : Z) (v : pixv) (cv : cmapv) (x : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 pmax -> pix_obj (rt_live RT Σ) m pix v cv -> p_data v <> 0 -> p_d v <= 8 -> optrF Σ m pmax 4 ->
  rw_cells asegs m pmax [C4 x] ->
  lenv Σ m sp lo (LSTK 4) -> lres Σ 1 0 2 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixGetMaxColorIndex m)))
    (fun c => exists (Σ' : rts RT) (rv y : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost Σ Σ' m m' sp lo /\ keeps Σ Σ' sp [(pmax, pmax + 4)] m m' /\ rw_cells asegs m' pmax [C4 y]) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 2 <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition pixDeserialize_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (dp n : Z) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 dp -> a1 = Z_to_bv 64 n -> 0 <= n < 2^26 -> 0 < dp -> (n < 28 \/ (dp mod 8 = 0 /\ own_live (rt_live RT Σ) dp n)) ->
  uctx m sp s0 ras ->
  Forall (fun r => Forall (fun f => In (f :: r :: bv_unsigned ra :: ras) CLIENT_TRACES) DESTROY_FREE_RAS) DESER_DESTROY_RAS ->
  lenv Σ m sp lo (LSTK 8) -> lres Σ 6 5 (RASTER_COST + 64) ->
  sec_bytes (rt_live RT Σ) + 0x4000000 <= SEC_BYTES ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixDeserialize m)))
    (fun c => exists (Σ' : rts RT) (pix : Z) (v : pixv) (cv : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pix) m' ms
          /\ lpost_f Σ Σ' m m' sp lo /\ keepsL (rt_live RT Σ) Σ sp [] m m' /\ (pix = 0 \/ (pix_obj (rt_live RT Σ') m' pix v cv /\ p_data v <> 0))) c
       /\ (pix = 0 -> rt_live RT Σ' = rt_live RT Σ)
       /\ (pix <> 0 -> live_destroy pix v cv (rt_live RT Σ') = rt_live RT Σ)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - (RASTER_COST + 64) <= rt_credit RT Σ'
       /\ (forall p n, In (p, n) (rt_live RT Σ') -> 0 < n) /\ Z.of_nat (length (rt_live RT Σ')) <= Z.of_nat (length (rt_live RT Σ)) + 4).


(* [comment removed for export] *)
Definition FUZZ_COST : Z := 2^31.
Definition FUZZ_LIVE : Z := 16.
Definition FUZZ_STACK : Z := 0x40000.
Definition fuzz_one_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> tp = Z_to_bv 64 TP_A -> bv_unsigned ra = RA_TOP ->
  0 < d -> Z.of_nat (length bs) < 2^26 -> bytes_at asegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n /\ d mod 8 = 0) \/ bs = []) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ ->
  (bv_unsigned s0 < bv_unsigned sp \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  LIB m -> io_ssp m -> ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_fuzz m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) LIB_FP m m' /\ LIB m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σ').

End Iface.
