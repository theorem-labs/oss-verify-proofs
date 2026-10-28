(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record drest := DREST {
  r_unz : list word; r_cfc : list word; r_inUse : list byte; r_in16 : list byte; r_s2u : list byte;
  r_mtfa : list byte; r_mtfb : list word; r_sel : list byte; r_selm : list byte; r_len : list byte;
  r_lim : list word; r_base : list word; r_perm : list word; r_minl : list word }.

Section WithSegs.
  Variable segs : list Segment.

  Definition drest_at (m : word -> option byte) (S : Z) (r : drest) : Prop :=
    (u32arr segs m (S + 68) (r_unz r) /\ Z.of_nat (length (r_unz r)) = 256%Z) /\
    (u32arr segs m (S + 2124) (r_cfc r) /\ Z.of_nat (length (r_cfc r)) = 257%Z) /\
    (u8arr segs m (S + 3196) (r_inUse r) /\ Z.of_nat (length (r_inUse r)) = 256%Z) /\
    (u8arr segs m (S + 3452) (r_in16 r) /\ Z.of_nat (length (r_in16 r)) = 16%Z) /\
    (u8arr segs m (S + 3468) (r_s2u r) /\ Z.of_nat (length (r_s2u r)) = 256%Z) /\
    (u8arr segs m (S + 3724) (r_mtfa r) /\ Z.of_nat (length (r_mtfa r)) = 4096%Z) /\
    (u32arr segs m (S + 7820) (r_mtfb r) /\ Z.of_nat (length (r_mtfb r)) = 16%Z) /\
    (u8arr segs m (S + 7884) (r_sel r) /\ Z.of_nat (length (r_sel r)) = 18002%Z) /\
    (u8arr segs m (S + 25886) (r_selm r) /\ Z.of_nat (length (r_selm r)) = 18002%Z) /\
    (u8arr segs m (S + 43888) (r_len r) /\ Z.of_nat (length (r_len r)) = 1548%Z) /\
    (u32arr segs m (S + 45436) (r_lim r) /\ Z.of_nat (length (r_lim r)) = 1548%Z) /\
    (u32arr segs m (S + 51628) (r_base r) /\ Z.of_nat (length (r_base r)) = 1548%Z) /\
    (u32arr segs m (S + 57820) (r_perm r) /\ Z.of_nat (length (r_perm r)) = 1548%Z) /\
    (u32arr segs m (S + 64012) (r_minl r) /\ Z.of_nat (length (r_minl r)) = 6%Z).

  (* [comment removed for export] *)
  Lemma drest_transport : forall W m m' S r,
    drest_at m S r -> munch W m m' -> wmono segs m m' ->
    disjoint_from W (S + 68) (4 * 256) -> disjoint_from W (S + 2124) 1028 -> disjoint_from W (S + 3196) 60840 ->
    drest_at m' S r.
  Proof.
    intros W m m' S r D MU WM D1 D2' D2.
    assert (SUB : forall a n, ((S + 3196 <= a)%Z /\ (a + n <= S + 64036)%Z) \/ (a = S + 2124 /\ n <= 1028)%Z -> (0 <= n)%Z -> disjoint_from W a n).
    { intros a n H12 H3. clear -D2 D2' H12 H3. induction W as [|[lo hi] W IH]; cbn in *; [exact I|].
      destruct D2 as [A B]. destruct D2' as [A' B']. split; [lia| apply IH; [exact B'| exact B]]. }
    cps_destruct D as ((A1&L1)&(A2&L2)&(A3&L3)&(A4&L4)&(A5&L5)&(A6&L6)&(A7&L7)&(A8&L8)&(A9&L9)&(A10&L10)&(A11&L11)&(A12&L12)&(A13&L13)&(A14&L14)).
    Ltac tr32 A L SUB MU WM D1 := split; [eapply u32arr_transport; [exact A| exact MU| exact WM| rewrite L; first [exact D1 | apply SUB; lia]] | exact L].
    Ltac tr8 A L SUB MU WM D1 := split; [eapply u8arr_transport; [exact A| exact MU| exact WM| rewrite L; first [exact D1 | apply SUB; lia]] | exact L].
    split; [tr32 A1 L1 SUB MU WM D1|]. split; [tr32 A2 L2 SUB MU WM D1|]. split; [tr8 A3 L3 SUB MU WM D1|]. split; [tr8 A4 L4 SUB MU WM D1|].
    split; [tr8 A5 L5 SUB MU WM D1|]. split; [tr8 A6 L6 SUB MU WM D1|]. split; [tr32 A7 L7 SUB MU WM D1|]. split; [tr8 A8 L8 SUB MU WM D1|].
    split; [tr8 A9 L9 SUB MU WM D1|]. split; [tr8 A10 L10 SUB MU WM D1|]. split; [tr32 A11 L11 SUB MU WM D1|]. split; [tr32 A12 L12 SUB MU WM D1|].
    split; [tr32 A13 L13 SUB MU WM D1| tr32 A14 L14 SUB MU WM D1].
  Qed.

  (* [comment removed for export] *)
  Inductive blk := BlkF (ttw : list word) | BlkS (l16 l4 : list byte).
  Definition blk_at (m : word -> option byte) (cx : bctx) (k : blk) : Prop :=
    match k with
    | BlkF ttw => b_small cx = 0%Z /\ u32arr segs m (b_tt cx) ttw /\ Z.of_nat (length ttw) = (100000 * b_n cx)%Z
    | BlkS l16 l4 => b_small cx = 1%Z /\ u8arr segs m (b_ll16 cx) l16 /\ Z.of_nat (length l16) = (200000 * b_n cx)%Z /\
                     u8arr segs m (b_ll4 cx) l4 /\ Z.of_nat (length l4) = (50000 * b_n cx)%Z
    end.
  Definition blk_ivls (cx : bctx) : list ivl :=
    if (b_small cx =? 0)%Z then [(b_tt cx, b_tt cx + 400000 * b_n cx)%Z]
    else [(b_ll16 cx, b_ll16 cx + 200000 * b_n cx)%Z; (b_ll4 cx, b_ll4 cx + 50000 * b_n cx)%Z].
End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record dimg := DIMG {
  di_segs : list Segment;
  di_dec : Z;        (* [comment removed for export] *)
  di_got : Z;        (* [comment removed for export] *)
  di_stderrp : Z;
  di_crc : Z;
  di_rnums : Z
}.

(* [comment removed for export] *)
Definition D14 : Z := 1024.

(* [comment removed for export] *)
Definition W14 (I : dimg) (cx : bctx) (sp : Z) : list ivl :=
  [(b_s cx, b_s cx + DSTATE_SIZE)%Z; (b_strm cx, b_strm cx + 20)%Z; (sp - D14, sp)%Z] ++ blk_ivls cx.

(* [comment removed for export] *)
Definition w1_view (h : dsh) : Z * Z * Z * Z := (sh_bsBuff h, sh_bsLive h, sh_cbn h, sh_origPtr h).

Section Contract.
  Variable I : dimg.
  Let segs := di_segs I.
  Variable w1_inv : Z * Z * Z * Z -> bzs -> drest -> list word -> Prop.

  Definition decompress14_post
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (cx : bctx) (h : dsh) (b : bzs) (lo : Z) (g1 sv : word) (payload : list byte)
      (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
        (h' : dsh) (nbu' : Z) (cf' : list word) (d' : dsm) (j1' j2' : list byte) (snb' : Z) (r' : drest)
        (ai' : Z) (til' tih' : word) (k' : blk),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom segs)
      /\ munch (W14 I cx (bv_unsigned sp)) m m' /\ wmono segs m m' /\ mem_inv segs m'
      /\ let b' := BZS (bs_src b) (bs_len b) ai' til' tih' (bs_q1 b) (bs_dst b) (bs_dlen b) (bs_av b)
                       (bs_tol b) (bs_toh b) (bs_q2 b) (bs_S b) (bs_bzalloc b) (bs_bzfree b) (bs_opaque b) in
         rw_cells segs m' (b_s cx) (HEAD_CELLS h')
      /\ rw_cells segs m' (b_s cx + 1092) [C4 (Z_to_bv 64 nbu')]
      /\ (u32arr segs m' (b_s cx + 1096) cf' /\ length cf' = 257%nat)
      /\ rw_cells segs m' (b_s cx + 3152) (MID_CELLS d')
      /\ rw_cells segs m' (b_s cx + 64036) (SAVE_CELLS j1' snb' j2')
      /\ drest_at segs m' (b_s cx) r'
      /\ rw_cells segs m' (b_strm cx) (STRM_CELLS b')
      /\ blk_at segs m' cx k'
      /\ bytes_at segs m' (b_src cx) payload
      /\ rw_cells segs m' (di_got I) [C8 (Z_to_bv 64 (di_stderrp I)); C8 g1; C8 (Z_to_bv 64 (di_stderrp I + 8)); C8 (Z_to_bv 64 (di_crc I)); C8 (Z_to_bv 64 (di_rnums I))]
      /\ rw_cells segs m' (di_stderrp I) [C8 sv]
      /\ u32arr segs m' (di_rnums I) rnums_words
      /\ stk segs m' lo (bv_unsigned sp)
      (* [comment removed for export] *)
      /\ dsh_wf h' /\ sh_strm h' = sh_strm h /\ sh_n h' = sh_n h /\ sh_small h' = sh_small h /\ sh_verb h' = 0%Z
      /\ sm_tt d' = b_tt cx /\ sm_ll16 d' = b_ll16 cx /\ sm_ll4 d' = b_ll4 cx
      /\ length j1' = 44%nat /\ length j2' = 60%nat /\ (0 <= snb' <= 900000)%Z /\ (0 <= nbu')%Z
      /\ bzs_wf b' /\ (0 <= ai' <= bs_ai b)%Z
      /\ w1_inv (w1_view h') b' r' cf'
      /\ (sh_state h' = 2%Z ->
            nbu' = 1%Z /\ sh_solen h' = 0%Z /\ (1 <= snb')%Z /\ rand_inv h' /\
            (in_bits b' h' < in_bits b h)%Z).

  (* [comment removed for export] *)
End Contract.
End ACeilS1.


(* [comment removed for export] *)
Section ACeilS2. Context {ACEIL__ : ACeil}.


End ACeilS2.
