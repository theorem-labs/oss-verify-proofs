(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface D_iface D_defs D_kit D_libiface D_clx D_rlkit X_atexit D_trpro D_trwalk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition tr_live (plen owned buf cap : Z) : list (Z * Z) := (if plen =? 0 then [] else [(owned, plen)]) ++ [(buf, cap)].

Lemma zeros_out_snoc : forall k, zeros_out k ++ [48; 10] = zeros_out (S k).
Proof.
  intros k. unfold zeros_out. induction k as [|k IH]; [reflexivity|].
  change (concat (repeat [48; 10] (S k))) with ([48; 10] ++ concat (repeat [48; 10] k)).
  change (concat (repeat [48; 10] (S (S k)))) with ([48; 10] ++ concat (repeat [48; 10] (S k))).
  rewrite <- app_assoc, IH. reflexivity.
Qed.

Lemma emit0_next_lines : forall j, emit0_next (so_lines j) = so_lines (S j).
Proof. intros j. unfold emit0_next, so_lines. cbn. f_equal. apply zeros_out_snoc. Qed.

Lemma emit0_out_lines : forall j, emit0_out (so_lines j) = [].
Proof. reflexivity. Qed.

Section TrDefs.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable XENV1 : mem -> Prop.
Variable LIB : mem -> Prop.
Variable fs : Fs.

(* [comment removed for export] *)
Definition TCTX (Σ : rts RT) (so : stdout_st) (f : Z) (usp buf cap plen d owned : Z) (payload : list byte)
    (c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 : word) (m : mem) : Prop :=
  ART RT Σ m /\ mem_inv asegs m /\ CLX OUT_rep ERR_rep XENV1 LIB so m
  /\ main_frame m usp c0 c1 c2 c3 c4 c5 c6 c7 /\ tr_frame m (usp - 80) (Z_to_bv 64 0x90b1c) x0 x1 x2 x3 x4 x5 x6 x7
  /\ stk asegs m (rt_sp0 RT Σ - STACK_WIN) (usp - 160)
  /\ usp mod 16 = 0 /\ rt_sp0 RT Σ - STACK_WIN + 0x100000 <= usp /\ usp <= rt_sp0 RT Σ /\ 0x7fff80000000 <= rt_sp0 RT Σ
  /\ rt_live RT Σ = tr_live plen owned buf cap /\ rt_frames RT Σ = []
  /\ plen = Z.of_nat (length payload) /\ plen < 2^26 /\ bytes_at asegs m d payload
  /\ (plen = 0 -> d = TR_EMPTY /\ owned = 0) /\ (0 < plen -> d = owned) /\ 0 < cap /\ usp + 16 <= USTACK_TOP
  /\ rw_cells asegs m TR_INIT [C1 (Z_to_bv 8 f)].

(* [comment removed for export] *)
Definition TLOOP (k : Z) (so : stdout_st) (usp buf cap : Z) (x0 x1 x2 x3 x4 x5 x6 x7 : word) (c : config) : Prop :=
  exists (Σ : rts RT) (plen d owned : Z) (payload : list byte)
         (gp t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (c0 c1 c2 c3 c4 c5 c6 c7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    ASTA RT Σ (PMfd fds0 fs)
      (eq (entry_st (Z_to_bv 64 0x90d44) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen) (Z_to_bv 64 d)
             (Z_to_bv 64 d) (Z_to_bv 64 plen) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) s3 (Z_to_bv 64 TR_BASE) (Z_to_bv 64 k)
             (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fuzz m)) c
    /\ TCTX Σ so 1 usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m
    /\ 1 <= k <= 4 /\ k * FUZZ_COST <= rt_credit RT Σ.

(* [comment removed for export] *)
Definition TFREE (so : stdout_st) (usp buf cap : Z) (x0 x1 x2 x3 x4 x5 x6 x7 : word) (c : config) : Prop :=
  exists (Σ : rts RT) (plen d owned : Z) (payload : list byte)
         (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (c0 c1 c2 c3 c4 c5 c6 c7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    ASTA RT Σ (PMfd fds0 fs)
      (eq (entry_st (Z_to_bv 64 0x90d70) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen) (Z_to_bv 64 d)
             (Z_to_bv 64 owned) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 owned) s3 (Z_to_bv 64 TR_BASE) (Z_to_bv 64 0)
             (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6 F fc e_free m)) c
    /\ TCTX Σ so 0 usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m.

(* [comment removed for export] *)
Definition TRET (so : stdout_st) (usp buf cap : Z) (x0 x1 x2 x3 x4 x5 x6 x7 : word) (c : config) : Prop :=
  exists (Σ : rts RT) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (c0 c1 c2 c3 c4 c5 c6 c7 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    ASTA RT Σ (PMfd fds0 fs)
      (eq (MS (mkR (Z_to_bv 64 0x90b1c) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 x0 x1 (Z_to_bv 64 0)
                   a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x90b1c) fc None m (seg_rom asegs))) c
    /\ ART RT Σ m /\ mem_inv asegs m /\ CLX OUT_rep ERR_rep XENV1 LIB so m
    /\ main_frame m usp c0 c1 c2 c3 c4 c5 c6 c7 /\ stk asegs m (rt_sp0 RT Σ - STACK_WIN) (usp - 80)
    /\ usp mod 16 = 0 /\ rt_sp0 RT Σ - STACK_WIN + 0x100000 <= usp /\ usp <= rt_sp0 RT Σ /\ 0x7fff80000000 <= rt_sp0 RT Σ
    /\ rt_live RT Σ = [(buf, cap)] /\ rt_frames RT Σ = [] /\ usp + 16 <= USTACK_TOP
    /\ rw_cells asegs m TR_INIT [C1 (Z_to_bv 8 0)].

End TrDefs.

Section TrTransport.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable XENV1 : mem -> Prop.
Variable LIB : mem -> Prop.
Hypothesis AF : art_facts RT.

Lemma tr_frame_agree : forall m m' sp ra x0 x1 x2 x3 x4 x5 x6 x7, tr_frame m sp ra x0 x1 x2 x3 x4 x5 x6 x7 ->
  agree_on (fun x => sp - 80 <= x < sp) m m' -> wmono asegs m m' -> tr_frame m' sp ra x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  intros m m' sp ra x0 x1 x2 x3 x4 x5 x6 x7 (junk & FR) AG WM. exists junk.
  apply (rw_cells_agree asegs m m' _ _ FR); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx.
  cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
Qed.

Lemma tr_frame_agree_nw : forall m m' sp ra x0 x1 x2 x3 x4 x5 x6 x7, tr_frame m sp ra x0 x1 x2 x3 x4 x5 x6 x7 ->
  agree_on (fun x => sp - 80 <= x < sp) m m' -> tr_frame m' sp ra x0 x1 x2 x3 x4 x5 x6 x7.
Proof.
  intros m m' sp ra x0 x1 x2 x3 x4 x5 x6 x7 (junk & FR) AG. exists junk.
  apply (rw_cells_agree_nw asegs m m' _ _ FR). eapply agree_sub; [exact AG|]. intros x Hx.
  cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
Qed.

(* [comment removed for export] *)
Lemma TCTX_agree : forall Σ Σ' so so' f f' usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m m',
  TCTX RT OUT_rep ERR_rep XENV1 LIB Σ so f usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m ->
  ART RT Σ' m' -> mem_inv asegs m' -> wmono asegs m m' -> stk asegs m' (rt_sp0 RT Σ - STACK_WIN) (usp - 160) ->
  rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = [] ->
  CLX OUT_rep ERR_rep XENV1 LIB so' m' ->
  agree_on (fun x => usp - 160 <= x < USTACK_TOP) m m' ->
  agree_on (fun x => d <= x < d + plen) m m' ->
  rw_cells asegs m' TR_INIT [C1 (Z_to_bv 8 f')] ->
  TCTX RT OUT_rep ERR_rep XENV1 LIB Σ' so' f' usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m'.
Proof using AF.
  intros Σ Σ' so so' f f' usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m m'
    (ART0 & MI0 & CLX0 & FR0 & TF0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & PL & PB & BD & P0 & P1 & CAP0 & UT0 & FL0)
    ART1 MI1 WM ST1 ESP ELV EFR CLX1 AGS AGD FL1.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  split; [exact ART1|]. split; [exact MI1|]. split; [exact CLX1|].
  split; [apply (main_frame_agree m m' usp _ _ _ _ _ _ _ _ FR0); [eapply agree_sub; [exact AGS|]; intros x Hx; cbv beta in *;
          unfold USTACK_TOP in *; lia| exact WM]|].
  split; [apply (tr_frame_agree m m' _ _ _ _ _ _ _ _ _ _ TF0); [eapply agree_sub; [exact AGS|]; intros x Hx; cbv beta in *;
          unfold USTACK_TOP in *; lia| exact WM]|].
  rewrite ESP, ELV, EFR. split; [exact ST1|].
  split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|]. split; [exact LV|]. split; [reflexivity|].
  split; [exact PL|]. split; [exact PB|].
  split; [apply (bytes_at_agree asegs m m' _ _ BD); rewrite <- PL; exact AGD|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| exact FL1].
Qed.

Lemma TCTX_agree_nw : forall Σ Σ' so so' f f' usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m m',
  TCTX RT OUT_rep ERR_rep XENV1 LIB Σ so f usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m ->
  ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' (rt_sp0 RT Σ - STACK_WIN) (usp - 160) ->
  rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = [] ->
  CLX OUT_rep ERR_rep XENV1 LIB so' m' ->
  agree_on (fun x => usp - 160 <= x < USTACK_TOP) m m' ->
  agree_on (fun x => d <= x < d + plen) m m' ->
  rw_cells asegs m' TR_INIT [C1 (Z_to_bv 8 f')] ->
  TCTX RT OUT_rep ERR_rep XENV1 LIB Σ' so' f' usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m'.
Proof using AF.
  intros Σ Σ' so so' f f' usp buf cap plen d owned payload c0 c1 c2 c3 c4 c5 c6 c7 x0 x1 x2 x3 x4 x5 x6 x7 m m'
    (ART0 & MI0 & CLX0 & FR0 & TF0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & PL & PB & BD & P0 & P1 & CAP0 & UT0 & FL0)
    ART1 MI1 ST1 ESP ELV EFR CLX1 AGS AGD FL1.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  split; [exact ART1|]. split; [exact MI1|]. split; [exact CLX1|].
  split; [apply (main_frame_agree_nw m m' usp _ _ _ _ _ _ _ _ FR0); eapply agree_sub; [exact AGS|]; intros x Hx; cbv beta in *;
          unfold USTACK_TOP in *; lia|].
  split; [apply (tr_frame_agree_nw m m' _ _ _ _ _ _ _ _ _ _ TF0); eapply agree_sub; [exact AGS|]; intros x Hx; cbv beta in *;
          unfold USTACK_TOP in *; lia|].
  rewrite ESP, ELV, EFR. split; [exact ST1|].
  split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|]. split; [exact LV|]. split; [reflexivity|].
  split; [exact PL|]. split; [exact PB|].
  split; [apply (bytes_at_agree asegs m m' _ _ BD); rewrite <- PL; exact AGD|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| exact FL1].
Qed.

End TrTransport.
