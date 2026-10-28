(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.U Require Import Sj_num_kitn.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_iface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition B_TP : Z := 0x6be3e8.
Definition B_PWFF : Z := 0xc0b68.
Definition B_FROMCHARS : Z := 0xf6840.
Definition B_PM : Z := 0xf8f88.
Definition B_PDC : Z := 0xfadcc.
Definition B_NDC : Z := 0xfaff8.
Definition B_HI64 : Z := 0xfb790.
Definition B_POW5 : Z := 0xfbb10.
Definition B_LM : Z := 0xfbdbc.
Definition B_LAF : Z := 0xfccac.
Definition B_SHL : Z := 0xfcfe0.
Definition B_P5LARGE : Z := 0x2f9e0.

Definition LAFB_STACK : Z := 80.
Definition HI64B_STACK : Z := 16.
Definition SHLB_STACK : Z := 64 + RT_STACK.
Definition LMB_STACK : Z := 224 + 32 + RT_STACK.
Definition P5B_STACK : Z := 48 + LMB_STACK.
Definition PDCB_STACK : Z := 48 + P5B_STACK.
Definition NDCB_STACK : Z := 160 + 32 + P5B_STACK.
Definition PMB_STACK : Z := 176.
Definition SPB_STACK : Z := 256 + 32 + NDCB_STACK.
Definition FFB_STACK : Z := 128 + SPB_STACK.
Definition FFB_FRAMES : nat := 3.
Definition FFB_CREDIT : Z := 16.

Definition PMB_NORM_DG : Z := 500.
Definition pmb_export (bs' : list byte) (len' dg' : Z) : Prop :=
  0 <= dg' <= 770 /\ 19 * len' <= 2 * dg' + 76 /\ (dg' < PMB_NORM_DG -> bignorm_b bs' len').

Lemma pmb_export_pdc : forall bs' len' dg', pmb_export bs' len' dg' -> dg' <= 328 -> bignorm_b bs' len' /\ len' + 21 <= 62.
Proof. intros bs' len' dg' (D & C & N) H. unfold PMB_NORM_DG in N. split; [apply N; lia| lia]. Qed.

Definition NDCB_RANGE : Z := 1048576.

Section BDefs.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.

Definition bbig (Σ : rts RT) (m : mem) (X : Z) (bs : list byte) (len : Z) : Prop :=
  fobj RT Σ m X 504 /\ length bs = 496%nat /\ u8arr bsegs m X bs
  /\ rw_cells bsegs m (X + 496) [C2 (Z_to_bv 64 len)] /\ 0 <= len <= 62.

Definition abig (Σ : rts RT) (m : mem) (X : Z) : Prop :=
  fobj RT Σ m X 504
  /\ (exists bs, length bs = 496%nat /\ u8arr bsegs m X bs)
  /\ (exists len, rw_cells bsegs m (X + 496) [C2 (Z_to_bv 64 len)] /\ 0 <= len <= 62).

Lemma bbig_abig : forall Σ m X bs len, bbig Σ m X bs len -> abig Σ m X.
Proof. intros Σ m X bs len (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exists bs; split; assumption| exists len; split; assumption]. Qed.

Lemma abig_bbig : forall Σ m X, abig Σ m X -> exists bs len, bbig Σ m X bs len.
Proof. intros Σ m X (H1 & (bs & H2 & H3) & (len & H4 & H5)). exists bs, len. repeat (split; [assumption|]). assumption. Qed.

Definition big_k (Σ : rts RT) (K : config -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (X lo cr : Z)
    (G : word -> list byte -> Z -> Prop) : Prop :=
  forall (Σ' : rts RT) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' bs' len', frm0 fc' ->
     rt_after RT Σ' (bv_unsigned sp) lo m m' -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(X, X + 504)] m m' ->
     bbig Σ' m' X bs' len' -> G a0' bs' len' ->
     rt_frames RT Σ' = rt_frames RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - cr <= rt_credit RT Σ' ->
     aevt RT PMc Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F' (ret_pc ra) fc' None m' (seg_rom bsegs)).

Definition lmb_G (len : Z) : word -> list byte -> Z -> Prop :=
  fun a0 bs' len' => len + 6 <= 62 -> a0 = Z_to_bv 64 1 /\ bignorm_b bs' len' /\ len' <= len + 6.
Definition lmb_stmt : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (X lo : Z) bs len,
  tp = Z_to_bv 64 B_TP -> frm0 fc ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + LMB_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  bbig Σ m X bs len ->
  big_k Σ K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m X lo 1 (lmb_G len) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 B_P5LARGE) (Z_to_bv 64 5) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 B_LM) fc None m (seg_rom bsegs)).

Definition p5b_G (bs : list byte) (len e : Z) : word -> list byte -> Z -> Prop :=
  fun a0 bs' len' => bignorm_b bs len -> len + 15 <= 62 -> e <= 328 -> a0 = Z_to_bv 64 1 /\ bignorm_b bs' len' /\ len' <= len + 15.
Definition p5b_stmt : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (X e cr lo : Z) bs len,
  tp = Z_to_bv 64 B_TP -> frm0 fc ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 0 <= e < 135 * (cr + 1) -> 0 <= cr -> e < 2147483648 -> cr <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + P5B_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  bbig Σ m X bs len ->
  big_k Σ K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m X lo cr (p5b_G bs len e) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 B_POW5) fc None m (seg_rom bsegs)).

Definition shlb_G (bs : list byte) (len n : Z) : word -> list byte -> Z -> Prop :=
  fun a0 bs' len' => bignorm_b bs len -> len + n / 64 + 1 <= 62 -> a0 = Z_to_bv 64 1 /\ bignorm_b bs' len' /\ len' <= len + n / 64 + 1.
Definition shlb_stmt : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (X n lo : Z) bs len,
  tp = Z_to_bv 64 B_TP -> frm0 fc -> 0 <= n < 18446744073709551616 ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + SHLB_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  bbig Σ m X bs len ->
  big_k Σ K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m X lo 0 (shlb_G bs len n) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 B_SHL) fc None m (seg_rom bsegs)).

Definition dc_k (Σ : rts RT) (K : config -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (X lo cr : Z) : Prop :=
  forall (Σ' : rts RT) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     rt_after RT Σ' (bv_unsigned sp) lo m m' -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(X, X + 504)] m m' ->
     abig Σ' m' X ->
     rt_frames RT Σ' = rt_frames RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - cr <= rt_credit RT Σ' ->
     aevt RT PMc Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F' (ret_pc ra) fc' None m' (seg_rom bsegs)).

Definition pdcb_stmt : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (X e cr lo : Z) bs len,
  tp = Z_to_bv 64 B_TP -> frm0 fc ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 0 <= e < 135 * (cr + 1) -> 0 <= cr -> e <= 328 -> cr <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + PDCB_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  bbig Σ m X bs len -> bignorm_b bs len -> len + 21 <= 62 ->
  dc_k Σ K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m X lo cr ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 B_PDC) fc None m (seg_rom bsegs)).

Definition ndcb_stmt : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (X p2 e cr lo : Z),
  tp = Z_to_bv 64 B_TP -> frm0 fc ->
  (length (rt_frames RT Σ) + 2 <= FRAMES_MAX)%nat -> 0 <= e < 135 * (cr + 1) -> 0 <= cr -> e <= NDCB_RANGE -> cr + 1 <= rt_credit RT Σ ->
  - NDCB_RANGE <= p2 <= NDCB_RANGE ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + NDCB_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  abig Σ m X ->
  dc_k Σ K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m X lo (cr + 1) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) a1 (Z_to_bv 64 (p2 mod 4294967296)) (Z_to_bv 64 (- e)) a4 a5 a6 a7
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 B_NDC) fc None m (seg_rom bsegs)).

Definition ffb_stmt : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (A FIRST LAST lo p n : Z) (txt : list byte),
  tp = Z_to_bv 64 B_TP -> frm0 fc ->
  (length (rt_frames RT Σ) + FFB_FRAMES <= FRAMES_MAX)%nat -> rt_frames RT Σ <> [] -> FFB_CREDIT <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FFB_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  In (p, n) (rt_live RT Σ) -> p mod 8 = 0 -> p <= A -> LAST + 8 <= p + n -> A + Z.of_nat (length txt) <= p + n ->
  bytes_at bsegs m A txt -> Z.of_nat (length txt) < 2147483648 -> A <= FIRST <= LAST -> LAST <= A + Z.of_nat (length txt) ->
  (forall (Σ' : rts RT) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     rt_after RT Σ' (bv_unsigned sp) lo m m' -> rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m' ->
     rt_frames RT Σ' = rt_frames RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - FFB_CREDIT <= rt_credit RT Σ' ->
     aevt RT PMc Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 B_PWFF) fc None m (seg_rom bsegs)).

End BDefs.
