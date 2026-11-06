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
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Spec Require Import Prelim.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import RT_iface RT_traces D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_calloc : Z := 0xb87fc.          (* [comment removed for export] *)
Definition e_stack_free_6 : Z := 0x9d694.    (* [comment removed for export] *)
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
  [ (0x2dca0, [true; true])                    (* [comment removed for export] *)
  ; (0x30f40, [true; false; false; false])     (* [comment removed for export] *)
  ; (0x31000, [true]); (0x31060, [true]); (0x310c0, [true])   (* [comment removed for export] *)
  ; (0x31140, [true]); (0x32240, [true])       (* [comment removed for export] *)
  ; (0x31b60, [true])                          (* [comment removed for export] *)
  ; (0x323a0, [true; false])                   (* [comment removed for export] *)
  ; (0x32400, [true; false; false])            (* [comment removed for export] *)
  ; (0x32460, [true; false; false])            (* [comment removed for export] *)
  ; (0x324c0, [true; false])                   (* [comment removed for export] *)
  ; (0x32500, [true; false; false])            (* [comment removed for export] *)
  ; (0x32560, [true])                          (* [comment removed for export] *)
  ; (0x325c0, [true; false; false])            (* [comment removed for export] *)
  ; (0x32620, [true; false; false])            (* [comment removed for export] *)
  ; (0x36e20, [true; false])                   (* [comment removed for export] *)
  ; (0x36f80, [true; false; false; false]) ].  (* [comment removed for export] *)

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
  [(0x30ce0, 14); (0x30d00, 10); (0x30d20, 16); (0x30d40, 29); (0x30e40, 39); (0x30ea0, 16); (0x30ec0, 18);
   (0x30f00, 19); (0x30fa0, 12); (0x30fc0, 24); (0x311a0, 11); (0x31340, 16); (0x31360, 12); (0x313e0, 13);
   (0x31440, 12); (0x314a0, 17); (0x31560, 10); (0x316c0, 15); (0x316e0, 22); (0x31760, 11);
   (0x31960, 16); (0x31b40, 14); (0x322a0, 15); (0x322c0, 19); (0x32300, 15); (0x32320, 17); (0x32360, 23);
   (0x326c0, 22); (0x32700, 15); (0x32ac0, 17); (0x32c40, 15); (0x32c60, 29); (0x32ca0, 11); (0x32cc0, 14);
   (0x32da0, 17); (0x32ea0, 22); (0x32ee0, 20); (0x32f20, 37); (0x33a80, 19); (0x33ac0, 8); (0x33ae0, 16);
   (0x36ba0, 13); (0x36bc0, 17); (0x36de0, 25); (0x36e80, 18); (0x36ec0, 14);
   (0x36ee0, 15); (0x36f00, 15); (0x36f20, 16); (0x36f40, 22); (0x37000, 14); (0x37020, 18); (0x37060, 25); (0x2dca0, 17); (0x2dce0, 31); (0x2dd20, 18); (0x2dd60, 22); (0x2dda0, 19); (0x2dde0, 20); (0x2de20, 18); (0x2de60, 13); (0x2de80, 14); (0x2dea0, 19); (0x2dee0, 13); (0x2df00, 13); (0x2df60, 32); (0x2dfa0, 10); (0x2dfc0, 14); (0x2dfe0, 17); (0x2e020, 11); (0x2e040, 18); (0x2e080, 14); (0x2e0a0, 20); (0x2e0e0, 13); (0x2e100, 46); (0x2e160, 10); (0x2e180, 24); (0x2e1c0, 26); (0x2e200, 17); (0x2e240, 11); (0x2e260, 21); (0x2e2a0, 15); (0x2e2c0, 33); (0x2e320, 18); (0x2e360, 31); (0x2e3a0, 23); (0x2e3e0, 11); (0x2e400, 17); (0x2e440, 20); (0x2e480, 13); (0x2e4a0, 21); (0x2e4e0, 23); (0x2e520, 20); (0x2e560, 19); (0x2e5a0, 15); (0x2e5c0, 35); (0x2e620, 19); (0x2e660, 25); (0x2e6a0, 19); (0x2e6e0, 46); (0x2e740, 21); (0x2e780, 49); (0x2e7e0, 18); (0x2e820, 16); (0x2e840, 14); (0x2e860, 26); (0x2e8a0, 14); (0x2e8c0, 18); (0x2e900, 13); (0x2e920, 16); (0x2e940, 18); (0x2e980, 3); (0x2e9a0, 65); (0x2ea20, 15); (0x2ea40, 17); (0x2ea80, 34); (0x2eae0, 2); (0x2eb00, 5); (0x2eb20, 28); (0x2eb60, 12); (0x2eb80, 28); (0x2ebc0, 21); (0x2ec00, 21); (0x2ec40, 1); (0x2ec60, 21); (0x2eca0, 9); (0x2ecc0, 23); (0x2ed00, 17); (0x2ed40, 22); (0x2ed80, 9); (0x2eda0, 12); (0x2edc0, 21); (0x2ee00, 17); (0x2ee40, 17); (0x2ee80, 19); (0x2eec0, 16); (0x2eee0, 46); (0x2ef40, 23); (0x2ef80, 19); (0x2efc0, 13); (0x2efe0, 15); (0x2f040, 22); (0x2f080, 12); (0x2f0a0, 36); (0x2f100, 13); (0x2f120, 15); (0x2f140, 15); (0x2f160, 17); (0x2f1a0, 14); (0x2f1c0, 27); (0x2f200, 17); (0x2f240, 15); (0x2f260, 16); (0x2f280, 18); (0x2f2c0, 15); (0x2f2e0, 15); (0x2f300, 15); (0x2f320, 17); (0x2f360, 33); (0x2f400, 20); (0x2f440, 14); (0x2f460, 36); (0x2f4c0, 15); (0x2f4e0, 26); (0x2f520, 32); (0x2f560, 41); (0x2f5c0, 15); (0x2f5e0, 12); (0x2f600, 16); (0x2f620, 17); (0x2f660, 17); (0x2f6a0, 19); (0x2f6e0, 27); (0x2f720, 13); (0x2f740, 17); (0x2f780, 28); (0x2f7c0, 18); (0x2f840, 19); (0x2f880, 13); (0x2f8a0, 37); (0x2f900, 14); (0x2f920, 15); (0x2f940, 16); (0x2f960, 19); (0x2f9a0, 17); (0x2f9e0, 17); (0x2fa20, 15); (0x2fa40, 16); (0x2fa60, 16); (0x2fa80, 15); (0x2faa0, 20); (0x2fae0, 18); (0x2fb20, 1); (0x2fb40, 2); (0x2fb60, 2); (0x2fb80, 2); (0x2fba0, 16); (0x2fbc0, 14); (0x2fbe0, 14); (0x2fc00, 18); (0x2fc40, 16); (0x2fc60, 23); (0x2fca0, 18); (0x2fce0, 37); (0x2fd40, 27); (0x2fdc0, 16); (0x2fde0, 16); (0x2fe00, 10); (0x2fe60, 22); (0x2fea0, 11); (0x2fec0, 36); (0x2ff20, 12); (0x2ff40, 15); (0x2ff60, 14); (0x2ff80, 17); (0x2ffc0, 13); (0x2ffe0, 27); (0x30020, 17); (0x30060, 14); (0x30080, 16); (0x300a0, 18); (0x300e0, 14); (0x30100, 16); (0x30120, 21); (0x30160, 28); (0x30220, 16); (0x30240, 9); (0x30260, 18); (0x302a0, 4); (0x302c0, 18); (0x30300, 26); (0x30340, 19); (0x30380, 15); (0x303a0, 15); (0x30400, 22); (0x30440, 10); (0x30460, 24); (0x304a0, 24); (0x304e0, 16); (0x30500, 37); (0x30560, 11); (0x30580, 15); (0x305a0, 15); (0x30600, 36); (0x30660, 11); (0x30680, 19); (0x306c0, 36); (0x30720, 12); (0x30740, 58); (0x307a0, 15); (0x307c0, 8); (0x307e0, 17); (0x30820, 18); (0x30860, 11); (0x30880, 26); (0x308c0, 17); (0x30900, 30); (0x30940, 16); (0x30960, 27); (0x309e0, 29); (0x30a20, 10); (0x30a40, 37); (0x30aa0, 11); (0x30ac0, 16); (0x30ae0, 9); (0x30b00, 17); (0x30b40, 9); (0x30b60, 14); (0x30b80, 9); (0x30ba0, 16); (0x30bc0, 34); (0x30c20, 25); (0x30c60, 25); (0x30d80, 17); (0x30dc0, 18); (0x30e00, 24); (0x30f40, 47); (0x31000, 48); (0x31060, 52); (0x310c0, 53); (0x31120, 9); (0x31140, 37); (0x311c0, 8); (0x311e0, 28); (0x31220, 19); (0x31260, 17); (0x312a0, 16); (0x312c0, 31); (0x31300, 15); (0x31320, 15); (0x31380, 12); (0x313a0, 19); (0x31400, 13); (0x31420, 15); (0x31460, 12); (0x31480, 15); (0x314e0, 10); (0x31500, 10); (0x31520, 17); (0x31580, 11); (0x315a0, 11); (0x315c0, 18); (0x31600, 18); (0x31640, 19); (0x31680, 11); (0x316a0, 15); (0x31720, 19); (0x31900, 17); (0x31940, 12); (0x31980, 37); (0x319e0, 12); (0x31a00, 17); (0x31a40, 19); (0x31a80, 56); (0x31ae0, 64); (0x31b60, 27); (0x31c60, 14); (0x31c80, 19); (0x31cc0, 16); (0x31ce0, 13); (0x31d00, 23); (0x31d40, 17); (0x31d80, 29); (0x31dc0, 17); (0x31e00, 19); (0x31e40, 16); (0x31e60, 17); (0x31ea0, 21); (0x31ee0, 18); (0x31f20, 24); (0x31f60, 35); (0x31fc0, 17); (0x32000, 29); (0x32040, 19); (0x320c0, 23); (0x32100, 14); (0x32120, 22); (0x32160, 20); (0x321a0, 16); (0x321c0, 18); (0x32200, 12); (0x32220, 13); (0x32240, 37); (0x323a0, 37); (0x32400, 47); (0x32460, 46); (0x324c0, 31); (0x32500, 51); (0x32560, 56); (0x325c0, 58); (0x32620, 77); (0x326a0, 16); (0x32720, 16); (0x32740, 36); (0x327a0, 16); (0x327c0, 20); (0x32800, 43); (0x32860, 15); (0x32880, 19); (0x328c0, 16); (0x328e0, 25); (0x32920, 20); (0x32960, 16); (0x32980, 27); (0x329c0, 24); (0x32a00, 23); (0x32a40, 18); (0x32a80, 21); (0x32b00, 18); (0x32b40, 36); (0x32ba0, 16); (0x32bc0, 25); (0x32c00, 21); (0x32ce0, 20); (0x32d20, 10); (0x32d40, 5); (0x32de0, 21); (0x32e20, 24); (0x32e60, 31); (0x33160, 17); (0x331a0, 15); (0x331c0, 14); (0x331e0, 18); (0x33220, 54); (0x33280, 27); (0x332c0, 32); (0x33300, 25); (0x33340, 55); (0x333a0, 28); (0x333e0, 42); (0x33440, 30); (0x33480, 20); (0x334c0, 13); (0x334e0, 23); (0x33520, 20); (0x33560, 16); (0x33580, 59); (0x335e0, 16); (0x33600, 16); (0x33620, 15); (0x33640, 18); (0x33680, 16); (0x336a0, 16); (0x336c0, 19); (0x33700, 15); (0x33720, 15); (0x33740, 15); (0x33760, 15); (0x33780, 15); (0x337a0, 15); (0x337c0, 29); (0x33800, 14); (0x33820, 15); (0x33840, 33); (0x338a0, 16); (0x338c0, 17); (0x33900, 16); (0x33920, 20); (0x33960, 34); (0x33a00, 17); (0x33a40, 10); (0x33a60, 14); (0x33b40, 17); (0x33b80, 12); (0x33ba0, 17); (0x33be0, 31); (0x33e80, 34); (0x33ee0, 22); (0x33f20, 22); (0x33fa0, 18); (0x33fe0, 18); (0x34020, 17); (0x34060, 21); (0x340a0, 24); (0x340e0, 15); (0x34100, 25); (0x34140, 29); (0x34180, 16); (0x341a0, 21); (0x341e0, 50); (0x34280, 21); (0x342c0, 20); (0x34300, 15); (0x34320, 15); (0x34340, 14); (0x343e0, 19); (0x34420, 13); (0x34440, 37); (0x344a0, 6); (0x344c0, 33); (0x34560, 19); (0x345a0, 20); (0x345e0, 21); (0x34620, 15); (0x34640, 38); (0x346a0, 21); (0x346e0, 24); (0x34760, 17); (0x34860, 21); (0x348a0, 19); (0x348e0, 2); (0x34900, 15); (0x34920, 16); (0x34940, 2); (0x34960, 21); (0x349a0, 43); (0x34a00, 72); (0x34a80, 16); (0x34aa0, 18); (0x34ae0, 3); (0x34b00, 22); (0x34b40, 13); (0x34b60, 15); (0x34b80, 45); (0x34be0, 33); (0x34c40, 18); (0x34c80, 22); (0x34cc0, 20); (0x34d00, 18); (0x34d40, 22); (0x34d80, 20); (0x34dc0, 25); (0x34e00, 26); (0x34e40, 16); (0x34e60, 17); (0x34ea0, 28); (0x34ee0, 34); (0x34f40, 41); (0x34fa0, 19); (0x34fe0, 21); (0x35020, 55); (0x35080, 61); (0x350e0, 53); (0x35140, 37); (0x351a0, 24); (0x351e0, 20); (0x35220, 23); (0x35260, 25); (0x352a0, 25); (0x352e0, 6); (0x35300, 9); (0x35320, 57); (0x35380, 12); (0x353a0, 9); (0x353c0, 3); (0x353e0, 23); (0x35420, 26); (0x35460, 9); (0x35480, 8); (0x354a0, 3); (0x354c0, 10); (0x354e0, 4); (0x35500, 18); (0x35540, 6); (0x35560, 17); (0x355a0, 33); (0x35600, 24); (0x35640, 38); (0x356a0, 10); (0x356c0, 23); (0x35700, 11); (0x35720, 9); (0x357e0, 21); (0x35820, 18); (0x358a0, 21); (0x358e0, 13); (0x35900, 19); (0x35980, 21); (0x359c0, 21); (0x35a00, 20); (0x35a40, 15); (0x35a60, 21); (0x35aa0, 19); (0x35ae0, 16); (0x35b00, 26); (0x35b40, 33); (0x35ba0, 19); (0x35be0, 18); (0x35c20, 16); (0x35c40, 13); (0x35c60, 4); (0x35c80, 26); (0x35cc0, 16); (0x35ce0, 19); (0x35d20, 17); (0x35d60, 50); (0x35dc0, 69); (0x35e40, 41); (0x35ea0, 13); (0x35ec0, 53); (0x35f20, 26); (0x35fa0, 21); (0x35fe0, 19); (0x36060, 19); (0x360a0, 18); (0x360e0, 16); (0x36100, 51); (0x36160, 12); (0x36180, 19); (0x361c0, 15); (0x361e0, 19); (0x36220, 17); (0x36260, 22); (0x362a0, 35); (0x36300, 63); (0x36360, 24); (0x363e0, 7); (0x36400, 17); (0x36440, 18); (0x36480, 19); (0x364c0, 22); (0x36500, 16); (0x36520, 16); (0x36540, 18); (0x36580, 14); (0x36660, 15); (0x36680, 18); (0x366c0, 16); (0x366e0, 28); (0x36720, 66); (0x367a0, 69); (0x36820, 70); (0x368a0, 17); (0x368e0, 18); (0x36920, 66); (0x369a0, 10); (0x369c0, 11); (0x369e0, 10); (0x36a00, 11); (0x36a20, 24); (0x36a60, 20); (0x36aa0, 14); (0x36ac0, 20); (0x36b00, 8); (0x36b60, 19); (0x36c00, 19); (0x36c40, 16); (0x36c60, 31); (0x36ca0, 35); (0x36d00, 21); (0x36d40, 17); (0x36d80, 19); (0x36dc0, 14); (0x36e20, 35); (0x36f80, 84); (0x370e0, 21); (0x37120, 15); (0x37140, 21); (0x37180, 16); (0x371a0, 13); (0x371c0, 17); (0x37200, 18); (0x37240, 10); (0x37260, 13); (0x37280, 5); (0x372a0, 27); (0x372e0, 25); (0x37320, 25); (0x37360, 28); (0x373a0, 25); (0x373e0, 20); (0x37420, 18); (0x37460, 19); (0x374a0, 33); (0x37500, 22); (0x37540, 43); (0x375a0, 60); (0x37600, 48); (0x37660, 46); (0x37780, 18); (0x377c0, 18); (0x37800, 25); (0x37840, 16); (0x37860, 23); (0x378a0, 18); (0x378e0, 18); (0x37920, 35); (0x37980, 15); (0x379e0, 18); (0x37a20, 20); (0x37a60, 20); (0x37aa0, 16); (0x37ac0, 16); (0x37ae0, 13); (0x37b00, 20); (0x37b40, 17); (0x37b80, 14); (0x37ba0, 18); (0x37be0, 16); (0x37c00, 52); (0x37c60, 55); (0x37cc0, 55); (0x37d20, 19); (0x37d60, 19); (0x37da0, 17); (0x37de0, 20); (0x37e20, 18); (0x37e60, 18); (0x37ea0, 19); (0x37ee0, 19); (0x37f20, 18); (0x37f60, 19); (0x37fa0, 16); (0x37fc0, 17); (0x38000, 63); (0x38060, 23); (0x380a0, 18); (0x380e0, 17); (0x38120, 15); (0x38140, 18); (0x38180, 49); (0x381e0, 37); (0x38240, 16); (0x38260, 19); (0x382a0, 18); (0x382e0, 21); (0x38320, 18); (0x38360, 18); (0x383a0, 20); (0x383e0, 18); (0x38420, 25); (0x38460, 43); (0x384c0, 20); (0x38500, 21); (0x38540, 18); (0x38580, 15); (0x385a0, 14); (0x385c0, 16); (0x385e0, 10); (0x38600, 50); (0x38660, 12); (0x38680, 22); (0x386c0, 27); (0x38700, 23); (0x38740, 11); (0x38760, 40); (0x387c0, 24); (0x38800, 11); (0x38820, 53); (0x38880, 19); (0x388c0, 6); (0x388e0, 5); (0x38900, 2); (0x38920, 20); (0x38960, 22); (0x389a0, 16); (0x389c0, 14); (0x38aa0, 25); (0x38ae0, 47); (0x38b40, 14); (0x38b60, 52); (0x38bc0, 14); (0x38be0, 23); (0x38c20, 40); (0x38c80, 24); (0x38cc0, 38); (0x38d20, 5); (0x38d40, 6); (0x38d60, 74); (0x38de0, 23); (0x38e20, 24); (0x38e60, 40); (0x38ec0, 20); (0x38f00, 19); (0x38f40, 44); (0x38fa0, 19); (0x38fe0, 19); (0x39020, 38); (0x39080, 43); (0x390e0, 21); (0x39120, 21); (0x39160, 86); (0x391e0, 1); (0x39200, 83); (0x39280, 14); (0x392a0, 20); (0x392e0, 27); (0x39320, 47); (0x39380, 22); (0x393c0, 21); (0x39400, 18); (0x39440, 21); (0x39480, 31); (0x394c0, 16); (0x394e0, 69); (0x395a0, 18); (0x395e0, 14); (0x39600, 37); (0x39660, 15); (0x39680, 15); (0x396a0, 18); (0x396e0, 16); (0x39700, 17); (0x39740, 20); (0x39780, 16); (0x397a0, 25); (0x397e0, 21); (0x39820, 23); (0x39860, 42); (0x398c0, 23); (0x39940, 16); (0x39960, 15); (0x39980, 16); (0x399a0, 20); (0x399e0, 15); (0x39a00, 17); (0x39a40, 20); (0x39a80, 22); (0x39ac0, 14); (0x39b20, 68); (0x39ba0, 13); (0x39bc0, 50); (0x39c20, 17); (0x39c60, 37); (0x39cc0, 14); (0x39ce0, 17); (0x39d20, 13); (0x39d40, 11); (0x39d60, 13); (0x39d80, 27); (0x39e00, 17); (0x39e40, 21); (0x39e80, 13); (0x39ea0, 23); (0x39ee0, 60); (0x39f80, 20); (0x39fc0, 25); (0x3a000, 30); (0x3a040, 13); (0x3a060, 30); (0x3a0a0, 34); (0x3a100, 22); (0x3a140, 28); (0x3a180, 18); (0x3a1c0, 17); (0x3a200, 24); (0x3a240, 23); (0x3a2c0, 16); (0x3a2e0, 17); (0x3a320, 16); (0x3a340, 14); (0x3a360, 16); (0x3a380, 17); (0x3a3c0, 17); (0x3a400, 13); (0x3a420, 17); (0x3a460, 20); (0x3a4a0, 23); (0x3a4e0, 11); (0x3a500, 41); (0x3a560, 6); (0x3a580, 43); (0x3a5e0, 45); (0x3a640, 56); (0x3a6a0, 54); (0x3a700, 54); (0x3a760, 57); (0x3a7c0, 42); (0x3a820, 55); (0x3a880, 47); (0x3a8e0, 60); (0x3a940, 10); (0x3a960, 10); (0x3a980, 30); (0x3a9c0, 68); (0x3aa40, 22); (0x3aa80, 37); (0x3aae0, 38); (0x3ab40, 39); (0x3aba0, 37)].

(* [comment removed for export] *)
Definition LEPT_GLOBALS : list (Z * Z) := [(0x1d3c40, 4); (0x1d3c60, 8); (0x1d3ca0, 8); (0x1d3cc0, 8)].
(* [comment removed for export] *)
Definition LEPT_RMASK32 : Z := 0x31ba0.
(* [comment removed for export] *)
Definition g_GOT_LeptMsgSeverity : Z := 0x1d0088.

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
  gp_got_lib : forall Σ m, ART RT Σ m -> ro_cells asegs m g_GOT_LeptMsgSeverity [C8 (Z_to_bv 64 0x1d3c40)];
  (* [comment removed for export] *)
  gp_ssp_keep : forall Σ' (m m' : mem), io_ssp m -> ART RT Σ' m' -> (forall a : word, client_static (bv_unsigned a) -> m' a = m a) ->
    io_ssp m';
  (* [comment removed for export] *)
  gp_live_hi : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> p + n <= 0x7fff7000 \/ 0x10007fff8000 <= p;
  (* [comment removed for export] *)
  gp_acc_rmask : forall Σ m, ART RT Σ m -> acc asegs m LEPT_RMASK32 132
}.

End Gaps.
