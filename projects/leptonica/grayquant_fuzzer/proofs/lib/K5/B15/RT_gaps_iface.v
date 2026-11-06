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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Spec Require Import Prelim.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_calloc : Z := 0x6219c.          (* [comment removed for export] *)
Definition e_stack_free_6 : Z := 0x4c250.    (* [comment removed for export] *)
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
  [ (0x236a0, [true; true])                    (* [comment removed for export] *)
  ; (0x242a0, [true; false; false; false])     (* [comment removed for export] *)
  ; (0x24360, [true]); (0x243c0, [true]); (0x24420, [true])   (* [comment removed for export] *)
  ; (0x244a0, [true]); (0x24e00, [true])       (* [comment removed for export] *)
  ; (0x24aa0, [true])                          (* [comment removed for export] *)
  ; (0x24f60, [true; false])                   (* [comment removed for export] *)
  ; (0x24fc0, [true; false; false])            (* [comment removed for export] *)
  ; (0x25020, [true; false; false])            (* [comment removed for export] *)
  ; (0x25080, [true; false])                   (* [comment removed for export] *)
  ; (0x250c0, [true; false; false])            (* [comment removed for export] *)
  ; (0x25120, [true])                          (* [comment removed for export] *)
  ; (0x25180, [true; false; false])            (* [comment removed for export] *)
  ; (0x251e0, [true; false; false])            (* [comment removed for export] *)
  ; (0x26c60, [true; false])                   (* [comment removed for export] *)
  ; (0x26dc0, [true; false; false; false]) ].  (* [comment removed for export] *)

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
  [(0x24040, 14); (0x24060, 10); (0x24080, 16); (0x240a0, 29); (0x241a0, 39); (0x24200, 16); (0x24220, 18);
   (0x24260, 19); (0x24300, 12); (0x24320, 24); (0x24500, 11); (0x246a0, 16); (0x246c0, 12); (0x24740, 13);
   (0x247a0, 12); (0x24800, 17); (0x248a0, 10); (0x24960, 15); (0x24980, 22); (0x24a00, 11);
   (0x24a60, 16); (0x24a80, 14); (0x24e60, 15); (0x24e80, 19); (0x24ec0, 15); (0x24ee0, 17); (0x24f20, 23);
   (0x25280, 22); (0x252c0, 15); (0x25680, 17); (0x25740, 15); (0x25760, 29); (0x257a0, 11); (0x257c0, 14);
   (0x25820, 17); (0x25860, 22); (0x258a0, 20); (0x258e0, 37); (0x266a0, 19); (0x266e0, 8); (0x26700, 16);
   (0x26bc0, 13); (0x26be0, 17); (0x26c20, 25); (0x26cc0, 18); (0x26d00, 14);
   (0x26d20, 15); (0x26d40, 15); (0x26d60, 16); (0x26d80, 22); (0x26e40, 14); (0x26e60, 18); (0x26ea0, 25); (0x23620, 14); (0x236a0, 17); (0x23720, 32); (0x23760, 10); (0x23780, 14); (0x237a0, 17); (0x237e0, 11); (0x23800, 18); (0x23840, 14); (0x23860, 17); (0x238a0, 11); (0x238c0, 21); (0x23900, 23); (0x23940, 11); (0x23960, 17); (0x23a00, 22); (0x23a40, 11); (0x23a60, 36); (0x23ac0, 12); (0x23ae0, 15); (0x23b00, 9); (0x23b20, 13); (0x23b40, 14); (0x23b60, 17); (0x23ba0, 13); (0x23bc0, 27); (0x23c00, 16); (0x23c20, 18); (0x23c60, 14); (0x23c80, 12); (0x23ca0, 15); (0x23cc0, 14); (0x23ce0, 16); (0x23d00, 21); (0x23d40, 28); (0x23dc0, 15); (0x23de0, 28); (0x23e20, 19); (0x23e60, 17); (0x23ea0, 9); (0x23ec0, 22); (0x23f00, 31); (0x23f40, 17); (0x23f80, 18); (0x23fc0, 15); (0x23fe0, 16); (0x240e0, 17); (0x24120, 18); (0x24160, 24); (0x242a0, 47); (0x24360, 48); (0x243c0, 52); (0x24420, 53); (0x24480, 9); (0x244a0, 37); (0x24520, 8); (0x24540, 28); (0x24580, 19); (0x245c0, 17); (0x24600, 16); (0x24620, 31); (0x24660, 15); (0x24680, 15); (0x246e0, 12); (0x24700, 19); (0x24760, 13); (0x24780, 15); (0x247c0, 12); (0x247e0, 15); (0x24840, 10); (0x24860, 17); (0x248c0, 18); (0x24900, 19); (0x24940, 15); (0x249c0, 19); (0x24aa0, 27); (0x24ba0, 19); (0x24be0, 16); (0x24c00, 17); (0x24c80, 23); (0x24cc0, 14); (0x24ce0, 22); (0x24d20, 20); (0x24d60, 16); (0x24d80, 18); (0x24dc0, 12); (0x24de0, 13); (0x24e00, 37); (0x24f60, 37); (0x24fc0, 47); (0x25020, 46); (0x25080, 31); (0x250c0, 51); (0x25120, 56); (0x25180, 58); (0x251e0, 77); (0x25260, 16); (0x252e0, 19); (0x25320, 24); (0x25360, 16); (0x25380, 36); (0x253e0, 16); (0x25400, 20); (0x25440, 18); (0x25480, 19); (0x254c0, 16); (0x254e0, 25); (0x25520, 20); (0x25560, 16); (0x25580, 24); (0x255c0, 23); (0x25600, 24); (0x25640, 29); (0x256c0, 36); (0x25720, 16); (0x25980, 17); (0x259c0, 18); (0x25a00, 54); (0x25a60, 27); (0x25aa0, 32); (0x25ae0, 25); (0x25b20, 55); (0x25b80, 28); (0x25bc0, 42); (0x25c60, 17); (0x25ca0, 18); (0x25ce0, 28); (0x25d20, 22); (0x25d60, 28); (0x25da0, 28); (0x25de0, 14); (0x25e00, 14); (0x25e20, 27); (0x25e60, 18); (0x25ea0, 22); (0x25ee0, 28); (0x25f20, 23); (0x25f60, 22); (0x25fa0, 21); (0x25fe0, 16); (0x26000, 20); (0x26040, 15); (0x26060, 20); (0x260a0, 21); (0x260e0, 17); (0x26120, 5); (0x26140, 21); (0x26180, 53); (0x261e0, 17); (0x26220, 22); (0x26260, 18); (0x262a0, 15); (0x262c0, 27); (0x26300, 14); (0x26320, 24); (0x26360, 11); (0x26380, 27); (0x263c0, 29); (0x26400, 75); (0x26480, 25); (0x264c0, 17); (0x26500, 25); (0x26540, 16); (0x26560, 25); (0x265a0, 23); (0x26620, 17); (0x26660, 10); (0x26680, 14); (0x26760, 17); (0x267a0, 12); (0x267c0, 17); (0x26800, 31); (0x26aa0, 34); (0x26b00, 22); (0x26b40, 22); (0x26c60, 35); (0x26dc0, 84); (0x26f20, 16); (0x26f40, 22)].

(* [comment removed for export] *)
Definition LEPT_GLOBALS : list (Z * Z) := [(0xf0000, 4); (0xf0020, 8); (0xf0040, 8); (0xf0060, 8)].
(* [comment removed for export] *)
Definition LEPT_RMASK32 : Z := 0x24ae0.
(* [comment removed for export] *)
Definition g_GOT_LeptMsgSeverity : Z := 0xec658.

Record rt_gaps : Prop := mkGaps {
  gp_malloc : malloc_contractC;
  gp_free : free_contractC;
  gp_calloc : calloc_contract;
  gp_stack_malloc_0 : stack_malloc_contract' 0;
  gp_stack_malloc_1 : stack_malloc_contract' 1;
  gp_stack_malloc_2 : stack_malloc_contract' 2;
  gp_stack_malloc_3 : stack_malloc_contract' 3;
  gp_stack_malloc_6 : stack_malloc_contract' 6;
  gp_stack_free_6 : stack_free_contract;
  gp_vsnprintf : vsnprintf_lept_icontract;
  (* [comment removed for export] *)
  gp_acc_lits : forall Σ m, ART RT Σ m -> Forall (fun r => acc asegs m (fst r) (snd r)) LEPT_LITS;
  gp_acc_globals : forall Σ m, ART RT Σ m -> Forall (fun r => acc asegs m (fst r) (snd r)) LEPT_GLOBALS;
  gp_globals_client : forall a, in_ranges (map (fun r => (fst r, fst r + snd r)) LEPT_GLOBALS) a -> client_static a;
  gp_got_lib : forall Σ m, ART RT Σ m -> ro_cells asegs m g_GOT_LeptMsgSeverity [C8 (Z_to_bv 64 0xf0000)];
  (* [comment removed for export] *)
  gp_ssp_keep : forall Σ' (m m' : mem), io_ssp m -> ART RT Σ' m' -> (forall a : word, client_static (bv_unsigned a) -> m' a = m a) ->
    io_ssp m';
  (* [comment removed for export] *)
  gp_live_hi : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> p + n <= 0x7fff7000 \/ 0x10007fff8000 <= p;
  (* [comment removed for export] *)
  gp_acc_rmask : forall Σ m, ART RT Σ m -> acc asegs m LEPT_RMASK32 132
}.

End Gaps.
