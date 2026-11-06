(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Spec Require Import Prelim.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface RT_traces D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_calloc : Z := 0x67b90.          (* [comment removed for export] *)
Definition e_stack_free_6 : Z := 0x51c44.    (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition link_invalid (lo f : Z) : Prop := f <= lo \/ f mod 8 <> 0 \/ 2^63 <= f.

Fixpoint chain_ok (m : mem) (lo f : Z) (ras : list Z) : Prop :=
  match ras with
  | [] => link_invalid lo f
  | ra1 :: ras' =>
      lo + 16 <= f /\ f mod 8 = 0 /\ f + 16 <= USTACK_TOP /\ 4096 <= ra1 < 2^64
      /\ exists fp1 : Z, 0 <= fp1 < 2^64 /\ rw_cells asegs m (f + -16) [C8 (Z_to_bv 64 fp1); C8 (Z_to_bv 64 ra1)]
                         /\ chain_ok m f fp1 ras'
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition unwind_okC (m : mem) (ra s0 sp : word) : Prop :=
  exists ras : list Z, chain_ok m (bv_unsigned sp) (bv_unsigned s0) ras /\ In (bv_unsigned ra :: ras) CLIENT_TRACES.

Lemma unwind_okC_of_ok : forall m ra s0 sp, In [bv_unsigned ra] CLIENT_TRACES ->
  (bv_unsigned s0 < bv_unsigned sp \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) -> unwind_okC m ra s0 sp.
Proof. intros m ra s0 sp H1 H2. exists []. split; [| exact H1]. cbn. unfold link_invalid. lia. Qed.

Section Gaps.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition malloc_contractC : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  1 <= n <= 0x4000000 -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 TP_A ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
  (64512 < n -> sec_bytes (rt_live RT Σ) + n <= SEC_BYTES) (* [comment removed for export] *) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_okC m ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_malloc m)))
            (malloc_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m).

Definition free_contractC : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  In (p, n) (rt_live RT Σ) -> a0 = Z_to_bv 64 p -> tp = Z_to_bv 64 TP_A ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_okC m ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (free_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m).

(* [comment removed for export] *)
Definition CALLOC_MAX : Z := 64512.
Definition calloc_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (nmemb size lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  0 < nmemb -> 0 < size -> nmemb * size <= CALLOC_MAX -> a0 = Z_to_bv 64 nmemb -> a1 = Z_to_bv 64 size -> tp = Z_to_bv 64 TP_A ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_okC m ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_calloc m)))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ rw_cells asegs m' p [CB (Z.to_nat (nmemb * size)) (repeat (Z_to_bv 8 0) (Z.to_nat (nmemb * size)))]
         /\ acc asegs m' p (nmemb * size)) c
       /\ rt_live RT Σ' = (p, nmemb * size) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ /\ 0 < p /\ p mod 16 = 0 /\ p + nmemb * size < USTACK_TOP).

(* [comment removed for export] *)
Definition CALLOCK_MAX : Z := 0x4000000.
Definition calloc_contractK : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (nmemb size lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  0 < nmemb -> 0 < size -> nmemb * size <= CALLOCK_MAX -> a0 = Z_to_bv 64 nmemb -> a1 = Z_to_bv 64 size -> tp = Z_to_bv 64 TP_A ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX ->
  (64512 < nmemb * size -> sec_bytes (rt_live RT Σ) + nmemb * size <= SEC_BYTES) -> mcost (nmemb * size) <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_okC m ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_calloc m)))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at asegs m' p (nmemb * size) /\ acc asegs m' p (nmemb * size)) c
       /\ rt_live RT Σ' = (p, nmemb * size) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost (nmemb * size) /\ 0 < p /\ p mod 16 = 0 /\ p + nmemb * size < USTACK_TOP).

(* [comment removed for export] *)
Definition stack_malloc_contract' (k : nat) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> (k = 0 \/ k = 1 \/ k = 6)%nat -> tp = Z_to_bv 64 TP_A ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc (e_stack_malloc k) m)))
    (fun c => exists (Σ' : rts RT) (f : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 f) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at asegs m' f (fs_size k - 8) /\ wr_at asegs m' (shad f) (fs_size k / 8)) c
       /\ rt_frames RT Σ' = (f, k) :: rt_frames RT Σ /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ 0 < f /\ f mod 64 = 0 /\ f + fs_size k < USTACK_TOP).

(* [comment removed for export] *)
Definition stack_free_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (f : Z) (fr : list (Z * nat)) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 f -> rt_frames RT Σ = (f, 6%nat) :: fr ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_stack_free_6 m)))
    (fun c => exists (Σ' : rts RT) (v : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) fr (bv_unsigned sp) m m') c
       /\ rt_frames RT Σ' = fr /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition LEPT_FMTS : list (Z * list bool) :=
  [ (0x24640, [true; true])                    (* [comment removed for export] *)
  ; (0x25420, [true; false; false; false])     (* [comment removed for export] *)
  ; (0x254e0, [true]); (0x25540, [true]); (0x255a0, [true])   (* [comment removed for export] *)
  ; (0x25620, [true]); (0x26b40, [true])       (* [comment removed for export] *)
  ; (0x26120, [true])                          (* [comment removed for export] *)
  ; (0x26ca0, [true; false])                   (* [comment removed for export] *)
  ; (0x26d00, [true; false; false])            (* [comment removed for export] *)
  ; (0x26d60, [true; false; false])            (* [comment removed for export] *)
  ; (0x26dc0, [true; false])                   (* [comment removed for export] *)
  ; (0x26e00, [true; false; false])            (* [comment removed for export] *)
  ; (0x26e60, [true])                          (* [comment removed for export] *)
  ; (0x26ec0, [true; false; false])            (* [comment removed for export] *)
  ; (0x26f20, [true; false; false])            (* [comment removed for export] *)
  ; (0x29be0, [true; false])                   (* [comment removed for export] *)
  ; (0x29d40, [true; false; false; false])
  ; (0x2aa60, [true; false; false; false])    (* [comment removed for export] *)
  ; (0x2ae00, [true; false; false; false; false])    (* [comment removed for export] *) ].  (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint lept_args (Σ : rts RT) (m : mem) (sp : word) (lo D : Z) (kinds : list bool) (ws : list word) : Prop :=
  match kinds, ws with
  | [], _ => True
  | true :: ks, w :: ws' =>
      (exists str, vsn_str RT Σ m sp lo D 2000 (bv_unsigned w) str /\ Z.of_nat (length str) < 96) /\ lept_args Σ m sp lo D ks ws'
  | false :: ks, _ :: ws' => lept_args Σ m sp lo D ks ws'
  | _ :: _, [] => False
  end.

Definition vsnprintf_lept_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (D ap fmt : Z) (kinds : list bool) (w1 w2 w3 w4 w5 w6 w7 : word) (junk : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 2000 -> a2 = Z_to_bv 64 fmt -> a3 = Z_to_bv 64 ap -> tp = Z_to_bv 64 TP_A ->
  In (fmt, kinds) LEPT_FMTS ->
  rw_cells asegs m ap [C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7] (* [comment removed for export] *) ->
  bv_unsigned sp <= ap -> ap + 56 <= USTACK_TOP - 16 ->
  lept_args Σ m sp lo D kinds [w1; w2; w3; w4; w5; w6; w7] ->
  rw_cells asegs m D [CB 2000 junk] -> checked_dst RT Σ m sp D 2000 -> SEGTOP_A <= D -> D + 2000 <= lo ->
  (D + 2000 <= ap \/ ap + 56 <= D) ->
  io_ssp m -> ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_vsnprintf m)))
    (fun c => exists v : word,
       icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo D 2000 m
                 (fun m' => exists junk', rw_cells asegs m' D [CB 2000 junk']) c).

(* [comment removed for export] *)
Definition LEPT_LITS : list (Z * Z) :=
  [(0x251c0, 14); (0x251e0, 10); (0x25200, 16); (0x25220, 29); (0x25320, 39); (0x25380, 16); (0x253a0, 18);
   (0x253e0, 19); (0x25480, 12); (0x254a0, 24); (0x25680, 11); (0x25820, 16); (0x25840, 12); (0x258c0, 13);
   (0x25920, 12); (0x25980, 17); (0x25a40, 10); (0x2a9c0, 13); (0x25ba0, 15); (0x25bc0, 22); (0x25c40, 11);
   (0x25ea0, 16); (0x26100, 14); (0x26ba0, 15); (0x26bc0, 19); (0x26c00, 15); (0x26c20, 17); (0x26c60, 23);
   (0x26fc0, 22); (0x27000, 15); (0x27380, 17); (0x27440, 15); (0x27460, 29); (0x274a0, 11); (0x274c0, 14);
   (0x27520, 17); (0x276e0, 22); (0x27720, 20); (0x27760, 37); (0x289e0, 19); (0x28a20, 8); (0x28a40, 16);
   (0x2a980, 28); (0x2a9e0, 21); (0x29b40, 13); (0x29b60, 17); (0x29ba0, 25); (0x29c40, 18); (0x29c80, 14);
   (0x29ca0, 15); (0x29cc0, 15); (0x29ce0, 16); (0x29d00, 22); (0x29dc0, 14); (0x29de0, 18); (0x29e20, 25);
   (* [comment removed for export] *)
   (0x24880, 21); (0x248c0, 11); (0x248e0, 37); (0x24940, 12); (0x24960, 17); (0x249a0, 17); (0x249e0, 11); (0x24a00, 16); (0x24a20, 14); (0x24a40, 17); (0x24be0, 13); (0x24c00, 11); (0x24c20, 16); (0x24c40, 33); (0x24ca0, 15); (0x24cc0, 19); (0x24d00, 21); (0x24d40, 18); (0x24d80, 16); (0x24da0, 15); (0x24dc0, 20); (0x24e00, 16); (0x24e20, 24); (0x24e60, 17); (0x24ee0, 37); (0x24f60, 19); (0x24fa0, 11); (0x25000, 12); (0x25260, 17); (0x252a0, 18); (0x25740, 17); (0x25a60, 18); (0x25c60, 15); (0x25c80, 15); (0x25f40, 17); (0x262e0, 14); (0x26300, 20); (0x26340, 23); (0x26380, 21); (0x263c0, 17); (0x26400, 16); (0x26420, 17); (0x26460, 18); (0x264a0, 17); (0x264e0, 17); (0x26520, 24); (0x26560, 20); (0x265a0, 21); (0x265e0, 19); (0x26620, 16); (0x26640, 13); (0x26660, 17); (0x266a0, 19); (0x266e0, 15); (0x26700, 39); (0x27560, 29); (0x275a0, 21); (0x275e0, 19); (0x27620, 13); (0x27640, 31); (0x27680, 33); (0x28aa0, 17); (0x28ae0, 12); (0x28b00, 17); (0x28b40, 31); (0x2a580, 17); (0x2a5e0, 14); (0x2a600, 19); (0x2a6c0, 16); (0x2a720, 20); (0x2a760, 16); (0x2a800, 13); (0x2a8e0, 13); (0x2a900, 19); (0x2aa20, 18); (0x2aa60, 77); (0x2aae0, 13); (0x2ab00, 19); (0x2ab40, 25); (0x2ab80, 29); (0x2abc0, 17); (0x2ac00, 20); (0x2ac40, 13); (0x2ac60, 17); (0x2aca0, 18); (0x2ace0, 16); (0x2ad00, 23); (0x2ad40, 22); (0x2ad80, 18); (0x2adc0, 24); (0x2ae00, 86); (0x2ae80, 23); (0x2aec0, 14); (0x2aee0, 23); (0x2af20, 22); (0x2af60, 20); (0x2afa0, 19); (0x2afe0, 16); (0x2b000, 13); (0x2b020, 14); (0x2b040, 16); (0x2b060, 15); (0x2b080, 15); (0x2b0a0, 24); (0x2b0e0, 14); (0x252e0, 24); (0x259e0, 10); (0x25a00, 17); (0x256a0, 8); (0x25780, 16); (0x257e0, 15); (0x25800, 15); (0x26b00, 12); (0x26b20, 13); (0x26fa0, 16)].

(* [comment removed for export] *)
Definition LEPT_GLOBALS : list (Z * Z) := [(0x102120, 4); (0x102140, 8); (0x102160, 8); (0x102180, 8)].
(* [comment removed for export] *)
Definition LEPT_RMASK32 : Z := 0x26160.
(* [comment removed for export] *)
Definition g_GOT_LeptMsgSeverity : Z := 0xfe788.

Record rt_gaps : Prop := mkGaps {
  gp_malloc : malloc_contractC;
  gp_free : free_contractC;
  gp_calloc : calloc_contract;
  gp_stack_malloc_0 : stack_malloc_contract' 0;
  gp_stack_malloc_1 : stack_malloc_contract' 1;
  gp_stack_malloc_6 : stack_malloc_contract' 6;
  gp_stack_free_6 : stack_free_contract;
  gp_vsnprintf : vsnprintf_lept_icontract;
  (* [comment removed for export] *)
  gp_acc_lits : forall Σ m, ART RT Σ m -> Forall (fun r => acc asegs m (fst r) (snd r)) LEPT_LITS;
  gp_acc_globals : forall Σ m, ART RT Σ m -> Forall (fun r => acc asegs m (fst r) (snd r)) LEPT_GLOBALS;
  gp_globals_client : forall a, in_ranges (map (fun r => (fst r, fst r + snd r)) LEPT_GLOBALS) a -> client_static a;
  gp_got_lib : forall Σ m, ART RT Σ m -> ro_cells asegs m g_GOT_LeptMsgSeverity [C8 (Z_to_bv 64 0x102120)];
  (* [comment removed for export] *)
  gp_ssp_keep : forall Σ' (m m' : mem), io_ssp m -> ART RT Σ' m' -> (forall a : word, client_static (bv_unsigned a) -> m' a = m a) ->
    io_ssp m';
  (* [comment removed for export] *)
  gp_live_hi : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> p + n <= 0x7fff7000 \/ 0x10007fff8000 <= p;
  (* [comment removed for export] *)
  gp_acc_rmask : forall Σ m, ART RT Σ m -> acc asegs m LEPT_RMASK32 132
}.

End Gaps.
