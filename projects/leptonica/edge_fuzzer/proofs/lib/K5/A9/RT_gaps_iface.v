(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Spec Require Import Prelim.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import RT_iface RT_traces D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_calloc : Z := 0xb85e8.          (* [comment removed for export] *)
Definition e_stack_free_6 : Z := 0x9d480.    (* [comment removed for export] *)
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
Definition stack_malloc_contract' (k : nat) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> (k <= 10)%nat -> tp = Z_to_bv 64 TP_A ->
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
  [ (0x2dec0, [true; true])                    (* [comment removed for export] *)
  ; (0x31060, [true; false; false; false])     (* [comment removed for export] *)
  ; (0x31120, [true]); (0x31180, [true]); (0x311e0, [true])   (* [comment removed for export] *)
  ; (0x31260, [true]); (0x32360, [true])       (* [comment removed for export] *)
  ; (0x31c80, [true])                          (* [comment removed for export] *)
  ; (0x324c0, [true; false])                   (* [comment removed for export] *)
  ; (0x32520, [true; false; false])            (* [comment removed for export] *)
  ; (0x32580, [true; false; false])            (* [comment removed for export] *)
  ; (0x325e0, [true; false])                   (* [comment removed for export] *)
  ; (0x32620, [true; false; false])            (* [comment removed for export] *)
  ; (0x32680, [true])                          (* [comment removed for export] *)
  ; (0x326e0, [true; false; false])            (* [comment removed for export] *)
  ; (0x32740, [true; false; false])            (* [comment removed for export] *)
  ; (0x36ea0, [true; false])                   (* [comment removed for export] *)
  ; (0x37000, [true; false; false; false]) ].  (* [comment removed for export] *)

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
  [(0x30e00, 14); (0x30e20, 10); (0x30e40, 16); (0x30e60, 29); (0x30f60, 39); (0x30fc0, 16); (0x30fe0, 18);
   (0x31020, 19); (0x310c0, 12); (0x310e0, 24); (0x312c0, 11); (0x31460, 16); (0x31480, 12); (0x31500, 13);
   (0x31560, 12); (0x315c0, 17); (0x31680, 10); (0x317e0, 15); (0x31800, 22); (0x31880, 11);
   (0x31a80, 16); (0x31c60, 14); (0x323c0, 15); (0x323e0, 19); (0x32420, 15); (0x32440, 17); (0x32480, 23);
   (0x327e0, 22); (0x32820, 15); (0x32b40, 17); (0x32cc0, 15); (0x32ce0, 29); (0x32d20, 11); (0x32d40, 14);
   (0x32e20, 17); (0x32f20, 22); (0x32f60, 20); (0x32fa0, 37); (0x33b00, 19); (0x33b40, 8); (0x33b60, 16);
   (0x36c20, 13); (0x36c40, 17); (0x36e60, 25); (0x36f00, 18); (0x36f40, 14);
   (0x36f60, 15); (0x36f80, 15); (0x36fa0, 16); (0x36fc0, 22); (0x37080, 14); (0x370a0, 18); (0x370e0, 25); (0x2dec0, 17); (0x2df00, 31); (0x2df40, 18); (0x2df80, 22); (0x2dfc0, 19); (0x2e000, 20); (0x2e040, 18); (0x2e080, 19); (0x2e0c0, 13); (0x2e0e0, 13); (0x2e140, 32); (0x2e180, 10); (0x2e1a0, 14); (0x2e1c0, 17); (0x2e200, 11); (0x2e220, 18); (0x2e260, 14); (0x2e280, 20); (0x2e2c0, 13); (0x2e2e0, 46); (0x2e340, 10); (0x2e360, 24); (0x2e3a0, 26); (0x2e3e0, 17); (0x2e420, 11); (0x2e440, 21); (0x2e480, 15); (0x2e4a0, 33); (0x2e500, 18); (0x2e540, 31); (0x2e580, 23); (0x2e5c0, 11); (0x2e5e0, 17); (0x2e620, 20); (0x2e660, 13); (0x2e680, 21); (0x2e6c0, 23); (0x2e700, 20); (0x2e740, 19); (0x2e780, 15); (0x2e7a0, 35); (0x2e800, 19); (0x2e840, 25); (0x2e880, 19); (0x2e8c0, 46); (0x2e920, 21); (0x2e960, 49); (0x2e9c0, 18); (0x2ea00, 16); (0x2ea20, 14); (0x2ea40, 26); (0x2ea80, 14); (0x2eaa0, 18); (0x2eae0, 13); (0x2eb00, 16); (0x2eb20, 18); (0x2eb60, 3); (0x2eb80, 65); (0x2ec00, 15); (0x2ec20, 17); (0x2ec60, 34); (0x2ecc0, 2); (0x2ece0, 5); (0x2ed00, 28); (0x2ed40, 12); (0x2ed60, 1); (0x2ed80, 21); (0x2edc0, 9); (0x2ede0, 23); (0x2ee20, 17); (0x2ee60, 22); (0x2eea0, 9); (0x2eec0, 12); (0x2eee0, 21); (0x2ef20, 17); (0x2ef60, 17); (0x2efa0, 19); (0x2efe0, 16); (0x2f000, 46); (0x2f060, 23); (0x2f0a0, 19); (0x2f0e0, 13); (0x2f100, 15); (0x2f160, 22); (0x2f1a0, 12); (0x2f1c0, 36); (0x2f220, 13); (0x2f240, 15); (0x2f260, 15); (0x2f280, 17); (0x2f2c0, 14); (0x2f2e0, 27); (0x2f320, 17); (0x2f360, 15); (0x2f380, 16); (0x2f3a0, 18); (0x2f3e0, 15); (0x2f400, 15); (0x2f420, 15); (0x2f440, 17); (0x2f480, 33); (0x2f520, 20); (0x2f560, 14); (0x2f580, 36); (0x2f5e0, 15); (0x2f600, 26); (0x2f640, 32); (0x2f680, 41); (0x2f6e0, 15); (0x2f700, 12); (0x2f720, 16); (0x2f740, 17); (0x2f780, 17); (0x2f7c0, 19); (0x2f800, 27); (0x2f840, 13); (0x2f860, 17); (0x2f8a0, 28); (0x2f8e0, 18); (0x2f960, 19); (0x2f9a0, 13); (0x2f9c0, 37); (0x2fa20, 14); (0x2fa40, 15); (0x2fa60, 16); (0x2fa80, 19); (0x2fac0, 17); (0x2fb00, 17); (0x2fb40, 15); (0x2fb60, 16); (0x2fb80, 16); (0x2fba0, 15); (0x2fbc0, 20); (0x2fc00, 18); (0x2fc40, 1); (0x2fc60, 2); (0x2fc80, 2); (0x2fca0, 2); (0x2fcc0, 16); (0x2fce0, 14); (0x2fd00, 14); (0x2fd20, 18); (0x2fd60, 16); (0x2fd80, 23); (0x2fdc0, 18); (0x2fe00, 37); (0x2fe60, 27); (0x2fee0, 16); (0x2ff00, 16); (0x2ff20, 10); (0x2ff80, 22); (0x2ffc0, 11); (0x2ffe0, 36); (0x30040, 12); (0x30060, 15); (0x30080, 14); (0x300a0, 17); (0x300e0, 13); (0x30100, 27); (0x30140, 17); (0x30180, 14); (0x301a0, 16); (0x301c0, 18); (0x30200, 14); (0x30220, 16); (0x30240, 21); (0x30280, 28); (0x30340, 16); (0x30360, 9); (0x30380, 18); (0x303c0, 4); (0x303e0, 18); (0x30420, 26); (0x30460, 19); (0x304a0, 15); (0x304c0, 15); (0x30520, 22); (0x30560, 10); (0x30580, 24); (0x305c0, 24); (0x30600, 16); (0x30620, 37); (0x30680, 11); (0x306a0, 15); (0x306c0, 15); (0x30720, 36); (0x30780, 11); (0x307a0, 19); (0x307e0, 36); (0x30840, 12); (0x30860, 58); (0x308c0, 15); (0x308e0, 8); (0x30900, 17); (0x30940, 18); (0x30980, 11); (0x309a0, 26); (0x309e0, 17); (0x30a20, 30); (0x30a60, 16); (0x30a80, 27); (0x30b00, 29); (0x30b40, 10); (0x30b60, 37); (0x30bc0, 11); (0x30be0, 16); (0x30c00, 9); (0x30c20, 17); (0x30c60, 9); (0x30c80, 14); (0x30ca0, 9); (0x30cc0, 16); (0x30ce0, 34); (0x30d40, 25); (0x30d80, 25); (0x30ea0, 17); (0x30ee0, 18); (0x30f20, 24); (0x31060, 47); (0x31120, 48); (0x31180, 52); (0x311e0, 53); (0x31240, 9); (0x31260, 37); (0x312e0, 8); (0x31300, 28); (0x31340, 19); (0x31380, 17); (0x313c0, 16); (0x313e0, 31); (0x31420, 15); (0x31440, 15); (0x314a0, 12); (0x314c0, 19); (0x31520, 13); (0x31540, 15); (0x31580, 12); (0x315a0, 15); (0x31600, 10); (0x31620, 10); (0x31640, 17); (0x316a0, 11); (0x316c0, 11); (0x316e0, 18); (0x31720, 18); (0x31760, 19); (0x317a0, 11); (0x317c0, 15); (0x31840, 19); (0x31a20, 17); (0x31a60, 12); (0x31aa0, 37); (0x31b00, 12); (0x31b20, 17); (0x31b60, 19); (0x31ba0, 56); (0x31c00, 64); (0x31c80, 27); (0x31d80, 14); (0x31da0, 19); (0x31de0, 16); (0x31e00, 13); (0x31e20, 23); (0x31e60, 17); (0x31ea0, 29); (0x31ee0, 17); (0x31f20, 19); (0x31f60, 16); (0x31f80, 17); (0x31fc0, 21); (0x32000, 18); (0x32040, 24); (0x32080, 35); (0x320e0, 17); (0x32120, 29); (0x32160, 19); (0x321e0, 23); (0x32220, 14); (0x32240, 22); (0x32280, 20); (0x322c0, 16); (0x322e0, 18); (0x32320, 12); (0x32340, 13); (0x32360, 37); (0x324c0, 37); (0x32520, 47); (0x32580, 46); (0x325e0, 31); (0x32620, 51); (0x32680, 56); (0x326e0, 58); (0x32740, 77); (0x327c0, 16); (0x32840, 16); (0x32860, 36); (0x328c0, 16); (0x328e0, 20); (0x32920, 15); (0x32940, 19); (0x32980, 16); (0x329a0, 20); (0x329e0, 16); (0x32a00, 27); (0x32a40, 24); (0x32a80, 23); (0x32ac0, 18); (0x32b00, 21); (0x32b80, 18); (0x32bc0, 36); (0x32c20, 16); (0x32c40, 25); (0x32c80, 21); (0x32d60, 20); (0x32da0, 10); (0x32dc0, 5); (0x32e60, 21); (0x32ea0, 24); (0x32ee0, 31); (0x331e0, 17); (0x33220, 15); (0x33240, 14); (0x33260, 18); (0x332a0, 54); (0x33300, 27); (0x33340, 32); (0x33380, 25); (0x333c0, 55); (0x33420, 28); (0x33460, 42); (0x334c0, 30); (0x33500, 20); (0x33540, 13); (0x33560, 23); (0x335a0, 20); (0x335e0, 16); (0x33600, 59); (0x33660, 16); (0x33680, 16); (0x336a0, 15); (0x336c0, 18); (0x33700, 16); (0x33720, 16); (0x33740, 19); (0x33780, 15); (0x337a0, 15); (0x337c0, 15); (0x337e0, 15); (0x33800, 15); (0x33820, 15); (0x33840, 29); (0x33880, 14); (0x338a0, 15); (0x338c0, 33); (0x33920, 16); (0x33940, 17); (0x33980, 16); (0x339a0, 20); (0x339e0, 34); (0x33a80, 17); (0x33ac0, 10); (0x33ae0, 14); (0x33bc0, 17); (0x33c00, 12); (0x33c20, 17); (0x33c60, 31); (0x33f00, 34); (0x33f60, 22); (0x33fa0, 22); (0x34020, 18); (0x34060, 18); (0x340a0, 17); (0x340e0, 21); (0x34120, 24); (0x34160, 15); (0x34180, 25); (0x341c0, 29); (0x34200, 16); (0x34220, 21); (0x34260, 50); (0x34300, 21); (0x34340, 20); (0x34380, 15); (0x343a0, 15); (0x343c0, 14); (0x34460, 19); (0x344a0, 13); (0x344c0, 37); (0x34520, 6); (0x34540, 33); (0x345e0, 19); (0x34620, 20); (0x34660, 21); (0x346a0, 15); (0x346c0, 38); (0x34720, 21); (0x34760, 24); (0x347e0, 17); (0x348e0, 21); (0x34920, 19); (0x34960, 2); (0x34980, 15); (0x349a0, 16); (0x349c0, 2); (0x349e0, 21); (0x34a20, 43); (0x34a80, 72); (0x34b00, 16); (0x34b20, 18); (0x34b60, 3); (0x34b80, 22); (0x34bc0, 13); (0x34be0, 15); (0x34c00, 45); (0x34c60, 33); (0x34cc0, 18); (0x34d00, 22); (0x34d40, 20); (0x34d80, 18); (0x34dc0, 22); (0x34e00, 20); (0x34e40, 25); (0x34e80, 26); (0x34ec0, 16); (0x34ee0, 17); (0x34f20, 28); (0x34f60, 34); (0x34fc0, 41); (0x35020, 19); (0x35060, 21); (0x350a0, 55); (0x35100, 61); (0x35160, 53); (0x351c0, 37); (0x35220, 24); (0x35260, 20); (0x352a0, 23); (0x352e0, 25); (0x35320, 25); (0x35360, 6); (0x35380, 9); (0x353a0, 57); (0x35400, 12); (0x35420, 9); (0x35440, 3); (0x35460, 23); (0x354a0, 26); (0x354e0, 9); (0x35500, 8); (0x35520, 3); (0x35540, 10); (0x35560, 4); (0x35580, 18); (0x355c0, 6); (0x355e0, 17); (0x35620, 33); (0x35680, 24); (0x356c0, 38); (0x35720, 10); (0x35740, 23); (0x35780, 11); (0x357a0, 9); (0x35860, 21); (0x358a0, 18); (0x35920, 21); (0x35960, 13); (0x35980, 19); (0x35a00, 21); (0x35a40, 21); (0x35a80, 20); (0x35ac0, 15); (0x35ae0, 21); (0x35b20, 19); (0x35b60, 16); (0x35b80, 26); (0x35bc0, 33); (0x35c20, 19); (0x35c60, 18); (0x35ca0, 16); (0x35cc0, 13); (0x35ce0, 4); (0x35d00, 26); (0x35d40, 16); (0x35d60, 19); (0x35da0, 17); (0x35de0, 50); (0x35e40, 69); (0x35ec0, 41); (0x35f20, 13); (0x35f40, 53); (0x35fa0, 26); (0x36020, 21); (0x36060, 19); (0x360e0, 19); (0x36120, 18); (0x36160, 16); (0x36180, 51); (0x361e0, 12); (0x36200, 19); (0x36240, 15); (0x36260, 19); (0x362a0, 17); (0x362e0, 22); (0x36320, 35); (0x36380, 63); (0x363e0, 24); (0x36460, 7); (0x36480, 17); (0x364c0, 18); (0x36500, 19); (0x36540, 22); (0x36580, 16); (0x365a0, 16); (0x365c0, 18); (0x36600, 14); (0x366e0, 15); (0x36700, 18); (0x36740, 16); (0x36760, 28); (0x367a0, 66); (0x36820, 69); (0x368a0, 70); (0x36920, 17); (0x36960, 18); (0x369a0, 66); (0x36a20, 10); (0x36a40, 11); (0x36a60, 10); (0x36a80, 11); (0x36aa0, 24); (0x36ae0, 20); (0x36b20, 14); (0x36b40, 20); (0x36b80, 8); (0x36be0, 19); (0x36c80, 19); (0x36cc0, 16); (0x36ce0, 31); (0x36d20, 35); (0x36d80, 21); (0x36dc0, 17); (0x36e00, 19); (0x36e40, 14); (0x36ea0, 35); (0x37000, 84); (0x37160, 21); (0x371a0, 15); (0x371c0, 21); (0x37200, 16); (0x37220, 13); (0x37240, 17); (0x37280, 18); (0x372c0, 10); (0x372e0, 13); (0x37300, 5); (0x37320, 27); (0x37360, 25); (0x373a0, 25); (0x373e0, 28); (0x37420, 25); (0x37460, 20); (0x374a0, 18); (0x374e0, 19); (0x37520, 33); (0x37580, 22); (0x375c0, 43); (0x37620, 60); (0x37680, 48); (0x376e0, 46); (0x37800, 18); (0x37840, 18); (0x37880, 25); (0x378c0, 16); (0x378e0, 23); (0x37920, 18); (0x37960, 18); (0x379a0, 35); (0x37a00, 15); (0x37a60, 18); (0x37aa0, 20); (0x37ae0, 20); (0x37b20, 16); (0x37b40, 16); (0x37b60, 13); (0x37b80, 13); (0x37ba0, 20); (0x37be0, 17); (0x37c20, 14); (0x37c40, 18); (0x37c80, 16); (0x37ca0, 52); (0x37d00, 55); (0x37d60, 55); (0x37dc0, 19); (0x37e00, 19); (0x37e40, 17); (0x37e80, 20); (0x37ec0, 18); (0x37f00, 18); (0x37f40, 19); (0x37f80, 19); (0x37fc0, 18); (0x38000, 19); (0x38040, 16); (0x38060, 17); (0x380a0, 63); (0x38100, 23); (0x38140, 18); (0x38180, 17); (0x381c0, 15); (0x381e0, 18); (0x38220, 49); (0x38280, 19); (0x382c0, 18); (0x38300, 21); (0x38340, 18); (0x38380, 18); (0x383c0, 20); (0x38400, 18); (0x38440, 25); (0x38480, 43); (0x384e0, 20); (0x38520, 21); (0x38560, 18); (0x385a0, 15); (0x385c0, 14); (0x385e0, 16); (0x38600, 10); (0x38620, 50); (0x38680, 12); (0x386a0, 22); (0x386e0, 27); (0x38720, 23); (0x38760, 11); (0x38780, 40); (0x387e0, 24); (0x38820, 11); (0x38840, 53); (0x388a0, 19); (0x388e0, 6); (0x38900, 5); (0x38920, 2); (0x38940, 20); (0x38980, 22); (0x389c0, 16); (0x389e0, 14); (0x38ac0, 25); (0x38b00, 47); (0x38b60, 14); (0x38b80, 52); (0x38be0, 14); (0x38c00, 23); (0x38c40, 40); (0x38ca0, 24); (0x38ce0, 38); (0x38d40, 5); (0x38d60, 6); (0x38d80, 74); (0x38e00, 23); (0x38e40, 24); (0x38e80, 40); (0x38ee0, 20); (0x38f20, 19); (0x38f60, 44); (0x38fc0, 19); (0x39000, 19); (0x39040, 38); (0x390a0, 43); (0x39100, 21); (0x39140, 21); (0x39180, 86); (0x39200, 1); (0x39220, 83); (0x392a0, 14); (0x392c0, 20); (0x39300, 27); (0x39340, 47); (0x393a0, 22); (0x393e0, 21); (0x39420, 18); (0x39460, 21); (0x394a0, 31); (0x394e0, 16); (0x39500, 69); (0x395c0, 18); (0x39600, 14); (0x39620, 37); (0x39680, 15); (0x396a0, 15); (0x396c0, 18); (0x39700, 16); (0x39720, 17); (0x39760, 20); (0x397a0, 16); (0x397c0, 25); (0x39800, 21); (0x39840, 23); (0x39880, 42); (0x398e0, 23); (0x39960, 16); (0x39980, 15); (0x399a0, 16); (0x399c0, 20); (0x39a00, 15); (0x39a20, 17); (0x39a60, 20); (0x39aa0, 22); (0x39ae0, 14); (0x39b40, 68); (0x39bc0, 13); (0x39be0, 50); (0x39c40, 17); (0x39c80, 37); (0x39ce0, 14); (0x39d00, 17); (0x39d40, 13); (0x39d60, 11); (0x39d80, 13); (0x39da0, 27); (0x39e20, 17); (0x39e60, 21); (0x39ea0, 13); (0x39ec0, 23); (0x39f00, 60); (0x39fa0, 20); (0x39fe0, 25); (0x3a020, 30); (0x3a060, 13); (0x3a080, 30); (0x3a0c0, 34); (0x3a120, 22); (0x3a160, 28); (0x3a1a0, 18); (0x3a1e0, 24); (0x3a220, 23); (0x3a2a0, 16); (0x3a2c0, 17); (0x3a300, 16); (0x3a320, 14); (0x3a340, 16); (0x3a360, 17); (0x3a3a0, 17); (0x3a3e0, 13); (0x3a400, 17); (0x3a440, 20); (0x3a480, 23); (0x3a4c0, 11); (0x3a4e0, 41); (0x3a540, 6); (0x3a560, 43); (0x3a5c0, 45); (0x3a620, 56); (0x3a680, 54); (0x3a6e0, 54); (0x3a740, 57); (0x3a7a0, 42); (0x3a800, 55); (0x3a860, 47); (0x3a8c0, 60); (0x3a920, 10); (0x3a940, 10); (0x3a960, 30); (0x3a9a0, 68); (0x3aa20, 22); (0x3aa60, 37); (0x3aac0, 38); (0x3ab20, 39); (0x3ab80, 37)].

(* [comment removed for export] *)
Definition LEPT_GLOBALS : list (Z * Z) := [(0x1c8420, 4); (0x1c8440, 8); (0x1c8480, 8); (0x1c84a0, 8)].
(* [comment removed for export] *)
Definition LEPT_RMASK32 : Z := 0x31cc0.
(* [comment removed for export] *)
Definition g_GOT_LeptMsgSeverity : Z := 0x1c4868.

Record rt_gaps : Prop := mkGaps {
  gp_malloc : malloc_contractC;
  gp_free : free_contractC;
  gp_calloc : calloc_contract;
  gp_stack_malloc_0 : stack_malloc_contract' 0;
  gp_stack_malloc_1 : stack_malloc_contract' 1;
  gp_stack_malloc_4 : stack_malloc_contract' 4;
  gp_stack_malloc_6 : stack_malloc_contract' 6;
  gp_stack_free_6 : stack_free_contract;
  gp_vsnprintf : vsnprintf_lept_icontract;
  (* [comment removed for export] *)
  gp_acc_lits : forall Σ m, ART RT Σ m -> Forall (fun r => acc asegs m (fst r) (snd r)) LEPT_LITS;
  gp_acc_globals : forall Σ m, ART RT Σ m -> Forall (fun r => acc asegs m (fst r) (snd r)) LEPT_GLOBALS;
  gp_globals_client : forall a, in_ranges (map (fun r => (fst r, fst r + snd r)) LEPT_GLOBALS) a -> client_static a;
  gp_got_lib : forall Σ m, ART RT Σ m -> ro_cells asegs m g_GOT_LeptMsgSeverity [C8 (Z_to_bv 64 0x1c8420)];
  (* [comment removed for export] *)
  gp_ssp_keep : forall Σ' (m m' : mem), io_ssp m -> ART RT Σ' m' -> (forall a : word, client_static (bv_unsigned a) -> m' a = m a) ->
    io_ssp m';
  (* [comment removed for export] *)
  gp_live_hi : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> p + n <= 0x7fff7000 \/ 0x10007fff8000 <= p;
  (* [comment removed for export] *)
  gp_acc_rmask : forall Σ m, ART RT Σ m -> acc asegs m LEPT_RMASK32 132
}.

End Gaps.
