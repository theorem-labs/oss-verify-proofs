(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzDefs BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 DecCut S0_bzd_out.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecTacF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacF.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaA RelLia.
Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition set8 (d : dst) (oc ol nu k0 tp rn rt cb : Z) : dst :=
  d_set_cbcrc (d_set_rTPos (d_set_rNToGo (d_set_tPos (d_set_k0 (d_set_nused (d_set_out_len (d_set_out_ch d oc) ol) nu) k0) tp) rn) rt) cb.
(* [comment removed for export] *)
Definition smod (s : dstrm) (out : list Z) (av tout : Z) : dstrm := DSTRM (s_in s) out av (s_tin s) tout.
(* [comment removed for export] *)
Definition jk_set_o (J : jk) (tol toh : word) : jk :=
  JK (j_p1 J) (j_p2 J) (j_p3 J) (j_s1 J) (j_s2 J) (j_til J) (j_tih J) (j_q1 J) tol toh (j_q2 J) (j_bzalloc J) (j_bzfree J) (j_opaque J).

Lemma set8_id : forall d,
  set8 d (d_out_ch d) (d_out_len d) (d_nused d) (d_k0 d) (d_tPos d) (d_rNToGo d) (d_rTPos d) (d_cbcrc d) = d.
Proof. intros d. destruct d. reflexivity. Qed.
Lemma smod_id : forall s, smod s (s_out s) (s_avail_out s) (s_tout s) = s.
Proof. intros s. destruct s. reflexivity. Qed.
Lemma jk_set_o_id : forall J, jk_set_o J (j_tol J) (j_toh J) = J.
Proof. intros J. destruct J. reflexivity. Qed.
(* [comment removed for export] *)
Lemma dcommit_set8 : forall d c,
  dcommit d c = set8 d (c_ch c) (c_len c) (c_nused c) (c_k0 c) (c_tPos c) (d_rNToGo d) (d_rTPos d) (c_crc c).
Proof. intros d c. destruct d. reflexivity. Qed.
Lemma scommit_smod : forall s c,
  scommit s c = smod s (c_out c ++ s_out s) (c_avail c) (s_tout s + (s_avail_out s - c_avail c)).
Proof. intros s c. destruct s. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record foctx := FOC {
  o_cx : bctx; o_J : jk; o_d : dst; o_s : dstrm;     (* [comment removed for export] *)
  o_g1 : word; o_s1v : word; o_SP : word; o_gp : word; o_tp : word;
  o_F : bvmap 5 word; o_fc : bv 32;
  o_KQ : Z * dst * dstrm -> machine_state -> Prop;   (* [comment removed for export] *)
  o_m0 : word -> option byte }.

Section Ctx.
  Variable c : foctx.
  Notation cx := (o_cx c). Notation J := (o_J c). Notation d0 := (o_d c). Notation s0 := (o_s c).
  Notation S := (b_s (o_cx c)). Notation STRM := (b_strm (o_cx c)). Notation DST := (b_dst (o_cx c)). Notation dlen := (b_dlen (o_cx c)).
  Notation n := (b_n (o_cx c)). Notation TT := (b_tt (o_cx c)). Notation L16 := (b_ll16 (o_cx c)). Notation L4 := (b_ll4 (o_cx c)).
  Notation snb := (sv_nblock (d_sv (o_d c))). Notation av0 := (s_avail_out (o_s c)).

  (* [comment removed for export] *)
  Definition oent : Prop :=
    d_bs100k d0 = n /\ (1 <= n <= 9)%Z /\ d_small d0 = b_small cx /\ (0 <= snb <= 900000)%Z /\ (1 <= snb)%Z /\
    (0 <= av0 <= dlen)%Z /\ Z.of_nat (length (s_out s0)) = (dlen - av0)%Z /\
    d_out_len d0 = 0%Z /\ (0 <= d_tPos d0 < 4294967296)%Z /\
    ((d_nused d0 = 1%Z /\ (0 <= d_k0 d0 < 256)%Z) \/ (d_nused d0 = 0%Z /\ (100000 * d_bs100k d0 <= d_tPos d0)%Z)) /\
    (0 <= d_cbcrc d0 < 4294967296)%Z /\ (0 <= d_out_ch d0 < 256)%Z /\
    (d_rand d0 = 0%Z \/ d_rand d0 = 1%Z) /\
    (d_rand d0 = 1%Z -> (0 <= d_rNToGo d0 < 2147483648)%Z /\ (0 <= d_rTPos d0 < 512)%Z) /\
    (d_small d0 <> 0%Z -> forall i, (0 <= i < 257)%Z -> (0 <= zget (d_cftab d0) i <= snb)%Z) /\
    (forall i, 0 <= zget (d_tt d0) i < 4294967296)%Z /\ (forall i, 0 <= zget (d_ll16 d0) i < 65536)%Z /\
    (forall i, 0 <= zget (d_ll4 d0) i < 256)%Z.

  (* [comment removed for export] *)
  Definition foctx_ok : Prop :=
    (0 < S /\ S + 64144 <= alloc_ceiling)%Z /\
    (alloc_ceiling <= STRM /\ STRM + 80 <= 2^47)%Z /\
    (0 < DST /\ DST + dlen <= alloc_ceiling)%Z /\ (0 <= dlen < 2^27)%Z /\
    (S + 64144 <= DST \/ DST + dlen <= S)%Z /\
    (S + 64144 <= 65536 \/ 0x34000 <= S)%Z /\ (DST + dlen <= 65536 \/ 0x34000 <= DST)%Z /\
    jk_wf J /\ oent.
  (* [comment removed for export] *)
  Definition foctx_okF : Prop :=
    b_small cx = 0%Z /\
    (0 < TT /\ TT + 400000 * n <= alloc_ceiling)%Z /\
    (S + 64144 <= TT \/ TT + 400000 * n <= S)%Z /\ (DST + dlen <= TT \/ TT + 400000 * n <= DST)%Z.
  (* [comment removed for export] *)
  Definition foctx_okS : Prop :=
    b_small cx = 1%Z /\
    (0 < L16 /\ L16 + 200000 * n <= alloc_ceiling)%Z /\
    (0 < L4 /\ L4 + 50000 * n <= alloc_ceiling)%Z /\
    (S + 64144 <= L16 \/ L16 + 200000 * n <= S)%Z /\ (DST + dlen <= L16 \/ L16 + 200000 * n <= DST)%Z /\
    (S + 64144 <= L4 \/ L4 + 50000 * n <= S)%Z /\ (DST + dlen <= L4 \/ L4 + 50000 * n <= DST)%Z /\
    (L16 + 200000 * n <= L4 \/ L4 + 50000 * n <= L16)%Z.
  Definition foctx_al : Prop := ctx_al cx /\ (STRM mod 16 = 0)%Z.

  (* [comment removed for export] *)
  Definition FWB : list ivl :=
    [(S, S + 68); (S + 1092, S + 1096); (S + 3152, S + 3196); (STRM, STRM + 44); (DST, DST + dlen)]%Z.

  (* [comment removed for export] *)
  Definition FGOT (m : word -> option byte) : Prop :=
    rw_cells s0segs m 0x320e8 [C8 (Z_to_bv 64 0x32098); C8 (o_g1 c); C8 (Z_to_bv 64 0x320a0); C8 (Z_to_bv 64 0x33178); C8 (Z_to_bv 64 0x335b0)].
  Definition FROf (m : word -> option byte) : Prop :=
    rw_cells s0segs m (S + 64036) (SAVE_CELLS (j_s1 J) snb (j_s2 J)) /\
    u32arr s0segs m TT (zw32 (d_tt d0) (100000 * n)) /\ u32arr s0segs m 0x33178 crc_words /\ u32arr s0segs m 0x335b0 rnums_words /\
    FGOT m /\ mem_inv s0segs m.
  Definition FROs (m : word -> option byte) : Prop :=
    rw_cells s0segs m (S + 64036) (SAVE_CELLS (j_s1 J) snb (j_s2 J)) /\
    u8arr s0segs m L16 (zh16 (d_ll16 d0) (200000 * n)) /\ u8arr s0segs m L4 (zb8 (d_ll4 d0) (50000 * n)) /\
    u32arr s0segs m (S + 1096) (zw32 (d_cftab d0) 257) /\
    u32arr s0segs m 0x33178 crc_words /\ u32arr s0segs m 0x335b0 rnums_words /\ FGOT m /\ mem_inv s0segs m.

  (* [comment removed for export] *)
  Definition DSg (m : word -> option byte) (Jx : jk) (d : dst) (s : dstrm) : Prop :=
    rw_cells s0segs m S (HEAD_CELLS (hd_of cx Jx d)) /\ rw_cells s0segs m (S + 1092) [C4 (Z_to_bv 64 (d_nused d))] /\
    rw_cells s0segs m (S + 3152) (MID_CELLS (mid_of cx d)) /\ rw_cells s0segs m STRM (STRM_CELLS (bs_of cx Jx s)).
  (* [comment removed for export] *)
  Definition DESTg (m : word -> option byte) (s : dstrm) (dbytes rest : list byte) : Prop :=
    u8arr s0segs m DST dbytes /\ Z.of_nat (length dbytes) = dlen /\
    dbytes = map (Z_to_bv 8) (rev (s_out s)) ++ rest /\ Z.of_nat (length (s_out s)) = (dlen - s_avail_out s)%Z.

  (* [comment removed for export] *)
  Definition oexit (d : dst) (s : dstrm) : Prop := (0 <= d_nused d)%Z /\ (0 <= s_avail_out s <= av0)%Z.
  (* [comment removed for export] *)
  Definition ojoin (d : dst) (s : dstrm) : Prop :=
    (0 <= d_nused d <= snb + 2)%Z /\ (0 <= d_cbcrc d < 4294967296)%Z /\ (0 <= d_out_len d <= 260)%Z /\
    (0 <= d_out_ch d < 256)%Z /\
    ((0 <= d_k0 d < 256)%Z \/ (d_nused d = 0%Z /\ (100000 * n <= d_tPos d)%Z)) /\   (* [comment removed for export] *)
    (0 <= d_tPos d < 4294967296)%Z /\
    (d_rand d = 1%Z -> (0 <= d_rNToGo d < 2147483648)%Z /\ (0 <= d_rTPos d < 512)%Z) /\
    (0 <= s_avail_out s <= av0)%Z.
End Ctx.
End ACeilS1.

(* [comment removed for export] *)
Notation FRR c ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 :=
  (mkR ra (o_SP c) (o_gp c) (o_tp c) t0 t1 t2 (Z_to_bv 64 (b_s (o_cx c))) s1 a0 a1 a2 a3 a4 a5 a6 a7
       (Z_to_bv 64 (b_s (o_cx c) + 1096)) s3 (Z_to_bv 64 (b_s (o_cx c) + 2047))
       (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 (-1)) s8 (Z_to_bv 64 100000) (Z_to_bv 64 (b_s (o_cx c) + 64080)) (Z_to_bv 64 10) t3 t4 t5 t6) (only parsing).
Section ACeilS2. Context {ACEIL__ : ACeil}.

Section Conts.
  Variable c : foctx.
  Variable RO : (word -> option byte) -> Prop.    (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition FKjoin : Prop :=
    forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 : word) (m : word -> option byte)
           (oc ol nu k0 tp rn rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (dbytes rest : list byte),
      let d' := set8 (o_d c) oc ol nu k0 tp rn rt cb in let s' := smod (o_s c) out av tout in
      DSg c m (jk_set_o (o_J c) tol toh) d' s' -> DESTg c m s' dbytes rest ->
      RO m -> munch (FWB c) (o_m0 c) m -> wmono s0segs (o_m0 c) m ->
      ojoin c d' s' ->
      evt s0segs (o_KQ c (0%Z, d', s')) (MS (FRR c ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6)
                       (o_F c) (Z_to_bv 64 0x15c1c) (o_fc c) None m (seg_rom s0segs)).
  (* [comment removed for export] *)
  Definition FKexit : Prop :=
    forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s8 t3 t4 t5 t6 : word) (m : word -> option byte)
           (oc ol nu k0 tp rn rt cb : Z) (out : list Z) (av tout : Z) (tol toh : word) (dbytes rest : list byte),
      let d' := set8 (o_d c) oc ol nu k0 tp rn rt cb in let s' := smod (o_s c) out av tout in
      DSg c m (jk_set_o (o_J c) tol toh) d' s' -> DESTg c m s' dbytes rest ->
      RO m -> munch (FWB c) (o_m0 c) m -> wmono s0segs (o_m0 c) m ->
      oexit c d' s' ->
      evt s0segs (o_KQ c (1%Z, d', s')) (MS (FRR c ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 (Z_to_bv 64 (-4)) s8 t3 t4 t5 t6)
                       (o_F c) (Z_to_bv 64 0x15cd4) (o_fc c) None m (seg_rom s0segs)).
End Conts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sextw_ge : forall u k, (0 <= u)%Z -> (0 <= k < 2^31)%Z ->
  (k <= bv_swrap 32 (u + 0) mod 18446744073709551616)%Z -> (k <= u mod 2^32)%Z.
Proof.
  intros u k Hu Hk H. rewrite Z.add_0_r in H. rewrite <- swrap32_mod in H.
  pose proof (Z.mod_pos_bound u (2^32) ltac:(lia)) as M.
  destruct (Z_lt_le_dec (u mod 2^32) (2^31)); [| lia].
  rewrite swrap32_small in H by lia. rewrite Z.mod_small in H; lia.
Qed.
Lemma sextw_lt : forall u k, (0 <= u)%Z -> (0 <= k < 2^31)%Z ->
  (bv_swrap 32 (u + 0) mod 18446744073709551616 < k)%Z ->
  (u mod 2^32 < k)%Z /\ (bv_swrap 32 (u + 0) mod 18446744073709551616 = u mod 2^32)%Z.
Proof.
  intros u k Hu Hk H. rewrite Z.add_0_r in *. rewrite <- swrap32_mod in *.
  pose proof (Z.mod_pos_bound u (2^32) ltac:(lia)) as M. pose proof (swrap32_range (u mod 2^32)) as R.
  destruct (Z_lt_le_dec (u mod 2^32) (2^31)).
  - rewrite swrap32_small in * by lia. rewrite Z.mod_small in * by lia. lia.
  - exfalso.
    assert (E : bv_swrap 32 (u mod 2 ^ 32) = (u mod 2^32 - 2^32)%Z).
    { pose proof (swrap32_high (u mod 2^32 - 2^32 + 2^64)%Z ltac:(lia)) as X.
      replace ((u mod 2 ^ 32 - 2 ^ 32 + 2 ^ 64))%Z with (u mod 2^32 + 4294967295 * 2^32)%Z in X by lia.
      rewrite <- swrap32_mod, Z.add_mod, Z.mod_mul, Z.add_0_r, Z.mod_mod, swrap32_mod in X by lia. lia. }
    rewrite E in H. replace ((u mod 2 ^ 32 - 2 ^ 32) mod 18446744073709551616)%Z with (u mod 2^32 - 2^32 + 2^64)%Z in H; [lia|].
    apply (Z.mod_unique _ _ (-1)%Z); lia.
Qed.
(* [comment removed for export] *)
Lemma sx32_land255 : forall w, (0 <= w < 4294967296)%Z -> Z.land (bv_unsigned (sx32 (Z_to_bv 64 w))) 255 = Z.land w 255.
Proof.
  intros w Hw. rewrite !land255_mod. pose proof (sx32_mod32 w ltac:(lia)) as E. rewrite <- E at 2.
  change 4294967296%Z with (2^32)%Z. rewrite CmpMem.mod_pow2_mod256 by lia. reflexivity.
Qed.
Lemma land255_small : forall k, (0 <= k < 256)%Z -> Z.land k 255 = k.
Proof. intros k Hk. rewrite land255_mod. apply Z.mod_small. lia. Qed.
(* [comment removed for export] *)
Lemma crc_words_model' : map bv_unsigned crc_words = crc32_table.
Proof. vm_compute. reflexivity. Qed.
Lemma crc_words_tbl : forall i, (0 <= i < 256)%Z -> wnth crc_words i = Z_to_bv 64 (crc32_tbl i).
Proof.
  intros i Hi. unfold crc32_tbl. rewrite <- crc_words_model'. unfold wnth.
  rewrite <- (Z_to_bv_bv_unsigned (nth (Z.to_nat i) crc_words (Z_to_bv 64 0))). f_equal.
  change 0%Z with (bv_unsigned (Z_to_bv 64 0)) at 2. rewrite map_nth. reflexivity.
Qed.
Lemma crc_words_nth : forall i, (0 <= i < 256)%Z -> nth_error crc_words (Z.to_nat i) = Some (Z_to_bv 64 (crc32_tbl i)).
Proof.
  intros i Hi. rewrite <- crc_words_tbl by lia. apply nth_error_wnth; [lia|]. rewrite crc_words_length. lia.
Qed.
(* [comment removed for export] *)
Lemma crc_step_rel : forall (w : word) crc ch, (bv_unsigned w mod 4294967296 = crc)%Z -> (0 <= crc < 4294967296)%Z -> (0 <= ch < 256)%Z ->
  (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (sx32 (Z_to_bv 64 (crc32_tbl (Z.lxor (crc / 16777216) ch))))) ((bv_unsigned w * 256) mod 18446744073709551616)))
     mod 4294967296 = crc_update crc ch)%Z.
Proof.
  intros w crc ch Hw Hc Hch.
  assert (Hidx : (0 <= Z.lxor (crc / 16777216) ch < 256)%Z).
  { apply lxor_byte; [|lia]. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  pose proof (crc32_tbl_range (Z.lxor (crc / 16777216) ch)) as TR.
  rewrite Z.lxor_comm. rewrite (low32_crc_step' w crc _ Hw TR).
  unfold crc_update. rewrite land255_mod, (Z.mod_small ch 256), shiftr_div24 by lia. reflexivity.
Qed.
Lemma crc_idx_byte : forall crc ch, (0 <= crc < 4294967296)%Z -> (0 <= ch < 256)%Z -> (0 <= Z.lxor (crc / 16777216) ch < 256)%Z.
Proof. intros crc ch Hc Hch. apply lxor_byte; [|lia]. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. Qed.
(* [comment removed for export] *)
Lemma C4_recell : forall segs m A cs1 (w : word) v cs2,
  rw_cells segs m A (cs1 ++ C4 w :: cs2) -> (bv_unsigned w mod 4294967296 = v mod 4294967296)%Z ->
  rw_cells segs m A (cs1 ++ C4 (Z_to_bv 64 v) :: cs2).
Proof.
  intros segs m A cs1 w v cs2 H E. change 4294967296%Z with (2^32)%Z in E. eapply rw_cells_same_bytes; [| | | exact H].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite (le4_lit_mod32 w v E). reflexivity.
  - rewrite !cells_size_app. reflexivity.
  - apply cells_wf_app. split; [exact (proj1 (proj1 (cells_wf_app _ _) (proj1 (proj1 H))))|].
    cbn. split; [exact I|]. exact (proj2 (proj2 (proj1 (cells_wf_app _ _) (proj1 (proj1 H))))).
Qed.
(* [comment removed for export] *)
Lemma upd_app_len : forall {X} (pre post : list X) (y x : X), upd (pre ++ y :: post) (length pre) x = pre ++ x :: post.
Proof. intros X pre. induction pre as [|z pre IH]; intros post y x; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma dest_snoc : forall (outr : list Z) (rest : list byte) (b : Z) r0 rest',
  rest = r0 :: rest' ->
  upd (map (Z_to_bv 8) (rev outr) ++ rest) (length outr) (Z_to_bv 8 b) = map (Z_to_bv 8) (rev (b :: outr)) ++ rest'.
Proof.
  intros outr rest b r0 rest' ->. cbn [rev]. rewrite map_app. cbn [map]. rewrite <- app_assoc. cbn [app].
  rewrite <- (length_rev outr), <- (length_map (Z_to_bv 8)). apply upd_app_len.
Qed.
(* [comment removed for export] *)
Lemma destc_snoc : forall (pre : list byte) (out : list Z) (rest dbytes : list byte) (i : nat) (b : Z) av,
  dbytes = pre ++ map (Z_to_bv 8) (rev out) ++ rest ->
  (length pre + length out = i)%nat -> Z.of_nat (length rest) = av -> (1 <= av)%Z ->
  exists rest', upd dbytes i (Z_to_bv 8 b) = pre ++ map (Z_to_bv 8) (rev (b :: out)) ++ rest' /\ Z.of_nat (length rest') = (av - 1)%Z.
Proof.
  intros pre out rest dbytes i b av -> Hi Hr Hav.
  destruct rest as [|r0 rest']; [cbn in Hr; lia|]. exists rest'. split; [| cbn [length] in Hr; lia].
  cbn [rev]. rewrite map_app. cbn [map].
  transitivity (upd ((pre ++ map (Z_to_bv 8) (rev out)) ++ r0 :: rest') (length (pre ++ map (Z_to_bv 8) (rev out))) (Z_to_bv 8 b)).
  - rewrite <- app_assoc, length_app, length_map, length_rev, Hi. reflexivity.
  - rewrite upd_app_len. rewrite <- !app_assoc. reflexivity.
Qed.
End ACeilS2.

(* [comment removed for export] *)
Ltac focbn0 := cbn [cget set8 smod jk_set_o dcommit scommit c0_of
       c_crc c_ch c_len c_nused c_k0 c_tPos c_out c_avail c_set_len c_set_k0 c_set_ch c_inc c_write
       dvF hd_of mid_of bs_of dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k
       sh_strm sh_state sh_soch sh_p1 sh_solen sh_brand sh_p2 sh_rNToGo sh_rTPos sh_bsBuff sh_bsLive sh_n sh_small sh_p3
       sh_cbn sh_verb sh_origPtr sh_tPos sh_k0 sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse
       bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque
       j_p1 j_p2 j_p3 j_s1 j_s2 j_til j_tih j_q1 j_tol j_toh j_q2 j_bzalloc j_bzfree j_opaque jk_set_t jk_set_s
       d_state d_out_ch d_out_len d_rand d_rNToGo d_rTPos d_bsBuff d_bsLive d_bs100k d_small d_blockNo d_verb d_origPtr
       d_tPos d_k0 d_unzftab d_nused d_cftab d_cftabCopy d_tt d_ll16 d_ll4 d_tt_al d_ll_al d_sbcrc d_sccrc d_cbcrc d_cccrc
       d_nInUse d_inUse d_inUse16 d_s2u d_mtfa d_mtfbase d_sel d_selMtf d_len d_limit d_base d_perm d_minLens d_sv
       d_set_state d_set_out_ch d_set_out_len d_set_rand d_set_rNToGo d_set_rTPos d_set_bsBuff d_set_bsLive d_set_bs100k
       d_set_small d_set_blockNo d_set_verb d_set_origPtr d_set_tPos d_set_k0 d_set_unzftab d_set_nused d_set_cftab
       d_set_cftabCopy d_set_tt d_set_ll16 d_set_ll4 d_set_tt_al d_set_ll_al d_set_sbcrc d_set_sccrc d_set_cbcrc d_set_cccrc
       d_set_nInUse d_set_inUse d_set_inUse16 d_set_s2u d_set_mtfa d_set_mtfbase d_set_sel d_set_selMtf d_set_len d_set_limit
       d_set_base d_set_perm d_set_minLens d_set_sv
       sv_i sv_j sv_t sv_alphaSize sv_nGroups sv_nSelectors sv_EOB sv_groupNo sv_groupPos sv_nextSym sv_nblockMAX sv_nblock
       sv_es sv_N sv_curr sv_zt sv_zn sv_zvec sv_zj sv_gSel sv_gMinlen sv_gPtr
       sv_set_i sv_set_j sv_set_t sv_set_alphaSize sv_set_nGroups sv_set_nSelectors sv_set_EOB sv_set_groupNo sv_set_groupPos
       sv_set_nextSym sv_set_nblockMAX sv_set_nblock sv_set_es sv_set_N sv_set_curr sv_set_zt sv_set_zn sv_set_zvec sv_set_zj
       sv_set_gSel sv_set_gMinlen sv_set_gPtr
       s_in s_out s_avail_out s_tin s_tout s_set_in s_set_out s_set_avail_out s_set_tin s_set_tout].
Ltac focbn0_in H := cbn [cget set8 smod jk_set_o dcommit scommit c0_of
       c_crc c_ch c_len c_nused c_k0 c_tPos c_out c_avail c_set_len c_set_k0 c_set_ch c_inc c_write
       dvF hd_of mid_of bs_of dv_h dv_nbu dv_cf dv_d dv_j1 dv_snb dv_j2 dv_r dv_b dv_k
       sh_strm sh_state sh_soch sh_p1 sh_solen sh_brand sh_p2 sh_rNToGo sh_rTPos sh_bsBuff sh_bsLive sh_n sh_small sh_p3
       sh_cbn sh_verb sh_origPtr sh_tPos sh_k0 sm_tt sm_ll16 sm_ll4 sm_sbcrc sm_sccrc sm_cbcrc sm_cccrc sm_nInUse
       bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque
       j_p1 j_p2 j_p3 j_s1 j_s2 j_til j_tih j_q1 j_tol j_toh j_q2 j_bzalloc j_bzfree j_opaque jk_set_t jk_set_s
       d_state d_out_ch d_out_len d_rand d_rNToGo d_rTPos d_bsBuff d_bsLive d_bs100k d_small d_blockNo d_verb d_origPtr
       d_tPos d_k0 d_unzftab d_nused d_cftab d_cftabCopy d_tt d_ll16 d_ll4 d_tt_al d_ll_al d_sbcrc d_sccrc d_cbcrc d_cccrc
       d_nInUse d_inUse d_inUse16 d_s2u d_mtfa d_mtfbase d_sel d_selMtf d_len d_limit d_base d_perm d_minLens d_sv
       d_set_state d_set_out_ch d_set_out_len d_set_rand d_set_rNToGo d_set_rTPos d_set_bsBuff d_set_bsLive d_set_bs100k
       d_set_small d_set_blockNo d_set_verb d_set_origPtr d_set_tPos d_set_k0 d_set_unzftab d_set_nused d_set_cftab
       d_set_cftabCopy d_set_tt d_set_ll16 d_set_ll4 d_set_tt_al d_set_ll_al d_set_sbcrc d_set_sccrc d_set_cbcrc d_set_cccrc
       d_set_nInUse d_set_inUse d_set_inUse16 d_set_s2u d_set_mtfa d_set_mtfbase d_set_sel d_set_selMtf d_set_len d_set_limit
       d_set_base d_set_perm d_set_minLens d_set_sv
       sv_i sv_j sv_t sv_alphaSize sv_nGroups sv_nSelectors sv_EOB sv_groupNo sv_groupPos sv_nextSym sv_nblockMAX sv_nblock
       sv_es sv_N sv_curr sv_zt sv_zn sv_zvec sv_zj sv_gSel sv_gMinlen sv_gPtr
       sv_set_i sv_set_j sv_set_t sv_set_alphaSize sv_set_nGroups sv_set_nSelectors sv_set_EOB sv_set_groupNo sv_set_groupPos
       sv_set_nextSym sv_set_nblockMAX sv_set_nblock sv_set_es sv_set_N sv_set_curr sv_set_zt sv_set_zn sv_set_zvec sv_set_zj
       sv_set_gSel sv_set_gMinlen sv_set_gPtr
       s_in s_out s_avail_out s_tin s_tout s_set_in s_set_out s_set_avail_out s_set_tin s_set_tout] in H.
Ltac focbn := focbn0; repeat (progress unfold ttw; focbn0).
(* [comment removed for export] *)
Ltac ccbv := cbv beta iota zeta delta [c0_of cget ttw c_set_len c_set_k0 c_set_ch c_inc c_write c_crc c_ch c_len c_nused c_k0 c_tPos c_out c_avail].
Ltac ccbv_in H := cbv beta iota zeta delta [c0_of cget ttw c_set_len c_set_k0 c_set_ch c_inc c_write c_crc c_ch c_len c_nused c_k0 c_tPos c_out c_avail] in H.
Ltac focbn_in H := focbn0_in H; repeat (progress unfold ttw in H; focbn0_in H).
