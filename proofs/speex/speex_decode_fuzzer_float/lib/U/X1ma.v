(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2 X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7 X1go X1hk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1ho X1hm X1hu X1ht. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nr. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1mc X1mv X1mb.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1nt X1rh X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Section Pieces.
Context {RCEIL : RunCeiling}.
Implicit Types (s : sbd_state bptr).
Local Notation MODEP mo := (sb_mode_ptr NB_MODE_PTR A_speex_wb_mode A_speex_uwb_mode mo).
Local Notation SUBP mo := (sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR mo).
Local Notation ISAVE OUT s := (sb_isave_ptr OUT s).

Definition sbp_hdr s (a : sb_addrs) : list cell :=
[C8 (Z_to_bv 64 (MODEP (sbd_mode s))); C8 (Z_to_bv 64 (a_low a));
C4 (Z_to_bv 64 (sbd_full_frame_size s)); C4 (Z_to_bv 64 (sbd_frame_size s));
C4 (Z_to_bv 64 (sbd_subframeSize s)); C4 (Z_to_bv 64 (sbd_nbSubframes s)); C4 (Z_to_bv 64 (sbd_lpcSize s))].

Definition sbp_ptrs s (a : sb_addrs) (OUT : Z) : list cell :=
[C4 (Z_to_bv 64 (sbd_sampling_rate s)); C4 (Z_to_bv 64 (sbd_lpc_enh_enabled s)); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 (a_g0 a)); C8 (Z_to_bv 64 (a_g1 a)); C8 (Z_to_bv 64 (a_exc a));
C8 (Z_to_bv 64 (a_oq a)); C8 (Z_to_bv 64 (a_iq a)); C8 (Z_to_bv 64 (a_msp a));
C8 (Z_to_bv 64 (a_pg a)); C8 (Z_to_bv 64 (a_er a)); C8 (Z_to_bv 64 (ISAVE OUT s))].

Definition sbp_cfg s (pad1 : list byte) : list cell :=
[C4 (Z_to_bv 64 (sbd_encode_submode s)); CB 4 pad1; C8 (Z_to_bv 64 (SUBP (sbd_mode s)))].

Definition sb_pieces (m : mem) (S : Z) s (a : sb_addrs) (OUT : Z) (j : sb_junk) : Prop :=
rw_cells rsegs m S (sbp_hdr s a)
/\ rw_cells rsegs m (S + 36) [C4 (Z_to_bv 64 (sbd_first s))]
/\ rw_cells rsegs m (S + 40) (sbp_ptrs s a OUT)
/\ rw_cells rsegs m (S + 128) [C4 (sj_last_ener j)]
/\ rw_cells rsegs m (S + 132) [C4 (sj_seed j)]
/\ rw_cells rsegs m (S + 136) (sbp_cfg s (sj_pad1 j))
/\ rw_cells rsegs m (S + 152) [C4 (Z_to_bv 64 (sbd_submodeID s))]
/\ rw_cells rsegs m (S + 156) [CB 4 (sj_pad2 j)].

#[using="Type"] Lemma cells_size_sbp_hdr : forall s a, cells_size (sbp_hdr s a) = 36%nat. Proof. reflexivity. Qed.
#[using="Type"] Lemma cells_size_sbp_ptrs : forall s a OUT, cells_size (sbp_ptrs s a OUT) = 88%nat. Proof. reflexivity. Qed.
#[using="Type"] Lemma cells_size_sbp_cfg : forall s p, cells_size (sbp_cfg s p) = 16%nat. Proof. reflexivity. Qed.

#[using="Type"] Lemma sb_cells_app : forall s a OUT j,
SBCELLS s a OUT j = sbp_hdr s a ++ [C4 (Z_to_bv 64 (sbd_first s))] ++ sbp_ptrs s a OUT ++ [C4 (sj_last_ener j)] ++ [C4 (sj_seed j)]
++ sbp_cfg s (sj_pad1 j) ++ [C4 (Z_to_bv 64 (sbd_submodeID s))] ++ [CB 4 (sj_pad2 j)].
Proof. intros. reflexivity. Qed.

#[using="Type"] Lemma sb_pieces_iff : forall m S s a OUT j,
rw_cells rsegs m S (SBCELLS s a OUT j) <-> sb_pieces m S s a OUT j.
Proof.
intros m S s a OUT j. rewrite sb_cells_app. unfold sb_pieces.
repeat rewrite rw_cells_app. cbn [cells_size csize Nat.add length app].
rewrite <- !Z.add_assoc.
repeat match goal with |- context [Z.of_nat ?n] => let v := eval cbv in (Z.of_nat n) in change (Z.of_nat n) with v end.
repeat match goal with |- context [(?a + ?b)%Z] => is_Zlit_zb a; is_Zlit_zb b; let v := eval cbv in (a + b)%Z in change (a + b)%Z with v end.
tauto.
Qed.
End Pieces.
#[export] Hint Rewrite cells_size_sbp_hdr cells_size_sbp_ptrs cells_size_sbp_cfg : chunk_sizes.

Lemma u8arr_as_f32 : forall m A bs (n : nat), u8arr rsegs m A bs -> length bs = (4 * n)%nat ->
exists ws, length ws = n /\ rw_cells rsegs m A (f32 ws).
Proof.
intros m A bs n U L. apply (rw_cells_CB_f32 rsegs m A n bs).
destruct U as [B W]. split; [split; [cbn; split; [exact L| exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B] |].
cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, <- L. exact W.
Qed.
Lemma f32_as_u8arr : forall m A ws, rw_cells rsegs m A (f32 ws) ->
u8arr rsegs m A (cells_bytes (f32 ws)) /\ length (cells_bytes (f32 ws)) = (4 * length ws)%nat.
Proof.
intros m A ws H. pose proof (rw_cells_f32_CB _ _ _ _ H) as [[_ B] W]. split; [| apply f32_bytes_length].
unfold u8arr. rewrite f32_bytes_length.
split; [cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; exact B|].
cbn [cells_size csize Nat.add] in W. rewrite Nat.add_0_r in W. exact W.
Qed.

Record sbinv := SBI {
x_S : Z; x_out : Z; x_A : Z; x_D : Z; x_stereo : Z; x_lo : Z; x_canary : word;
x_s : sbd_state bptr;
x_a : sb_addrs; x_LBL : list block;
x_b0 : bits_st bptr;
x_RD : Z;
x_dk : nat;
x_st : PState;
x_ra : word; x_sp : word; x_gp : word; x_tp : word;
x_s0 : word; x_s1 : word; x_s2 : word; x_s3 : word; x_s4 : word; x_s5 : word;
x_s6 : word; x_s7 : word; x_s8 : word; x_s9 : word; x_s10 : word; x_s11 : word;
x_F : bvmap 5 word; x_m0 : mem }.

Record sframe := SFR {
f_0 : word; f_8 : word; f_16 : word; f_24 : word; f_32 : word; f_40 : word; f_48 : word; f_56 : word;
f_64 : word; f_72 : word; f_80 : word; f_88 : word; f_96 : word; f_104 : word; f_112 : word; f_120 : word;
f_128 : word; f_136 : word; f_144 : word; f_152 : word; f_160 : word; f_168 : word; f_176 : word; f_184 : word;
f_192 : word; f_200 : word; f_208 : word; f_216 : word;
f_224 : word; f_dtx : word }.
Definition sframe_cells (fr : sframe) : list cell :=
[C8 (f_0 fr); C8 (f_8 fr); C8 (f_16 fr); C8 (f_24 fr); C8 (f_32 fr); C8 (f_40 fr); C8 (f_48 fr); C8 (f_56 fr);
C8 (f_64 fr); C8 (f_72 fr); C8 (f_80 fr); C8 (f_88 fr); C8 (f_96 fr); C8 (f_104 fr); C8 (f_112 fr); C8 (f_120 fr);
C8 (f_128 fr); C8 (f_136 fr); C8 (f_144 fr); C8 (f_152 fr); C8 (f_160 fr); C8 (f_168 fr); C8 (f_176 fr); C8 (f_184 fr);
C8 (f_192 fr); C8 (f_200 fr); C8 (f_208 fr); C8 (f_216 fr);
C4 (f_224 fr); C4 (f_dtx fr)].

Lemma cells_size_sframe : forall fr, cells_size (sframe_cells fr) = 232%nat. Proof. reflexivity. Qed.
#[export] Hint Rewrite cells_size_sframe : chunk_sizes.

Section Ctx.
Context {RCEIL : RunCeiling}.
Variable X : sbinv.
Local Notation S := (x_S X). Local Notation OUT := (x_out X). Local Notation A := (x_A X). Local Notation D := (x_D X).
Local Notation STEREO := (x_stereo X). Local Notation lo := (x_lo X). Local Notation a := (x_a X). Local Notation LBL := (x_LBL X).
Local Notation s0 := (x_s X).
Local Notation usp := (bv_unsigned (x_sp X)).
Local Notation FS := (sbd_subframeSize (x_s X)).

Definition sbWX : list (Z * Z) :=
(lo, usp) :: (A, A + BITS_SIZEOF) :: (OUT, OUT + HOUT_BYTES) :: (STEREO, STEREO + 24) :: (RSTDERR, RSTDERR + 232)
:: (S, S + SBSTATE_SIZEOF) :: (a_g0 a, a_g0 a + 256) :: (a_g1 a, a_g1 a + 256) :: (a_exc a, a_exc a + 4 * FS)
:: (a_oq a, a_oq a + 32) :: (a_iq a, a_iq a + 32) :: (a_pg a, a_pg a + 16) :: (a_er a, a_er a + 16) :: (a_msp a, a_msp a + 64)
:: blocks_ivs LBL.

#[using="Type"] Lemma sbWX_eq : sbWX = sbW lo usp A OUT STEREO (sb_blocks s0 S a ++ LBL).
Proof. unfold sbWX, sbW, blocks_ivs, sb_blocks. rewrite map_app. cbn [map blk_addr blk_size fst snd app]. reflexivity. Qed.

Definition fr_saves : list cell :=
let F0 := x_F X in
[C8 (reg_get F0 (Z_to_bv 5 21)); C8 (reg_get F0 (Z_to_bv 5 20));
C8 (reg_get F0 (Z_to_bv 5 19)); C8 (reg_get F0 (Z_to_bv 5 18)); C8 (reg_get F0 (Z_to_bv 5 9)); C8 (reg_get F0 (Z_to_bv 5 8));
C8 (x_s11 X); C8 (x_s10 X); C8 (x_s9 X); C8 (x_s8 X); C8 (x_s7 X); C8 (x_s6 X); C8 (x_s5 X); C8 (x_s4 X);
C8 (x_s3 X); C8 (x_s2 X); C8 (x_s1 X); C8 (x_s0 X); C8 (x_ra X)].

#[using="Type"] Lemma cells_size_fr_saves : cells_size fr_saves = 152%nat. Proof. reflexivity. Qed.

Definition frame_at (m : mem) (fr : sframe) : Prop :=
rw_cells rsegs m (usp + -384) (sframe_cells fr) /\ rw_cells rsegs m (usp + -152) fr_saves.

Definition bits_keep (b : bits_st bptr) : Prop :=
sb_owner b = sb_owner (x_b0 X) /\ sb_chars b = sb_chars (x_b0 X) /\ sb_buf_size b = sb_buf_size (x_b0 X).

Definition sbctx (xr : bool) (m : mem) (s : sbd_state bptr) (low : dec_state bptr) (b : bits_st bptr) (j : sb_junk)
(ows : list word) (stb : list byte) : Prop :=
munch sbWX (x_m0 X) m /\ wmono rsegs (x_m0 X) m /\ mem_inv rsegs m
/\ sb_pieces m S s a OUT j /\ sb_junk_ok s j /\ sb_bufs rsegs m a j /\ sb_inv s
/\ sbd_mode s = sbd_mode s0 /\ sbd_subframeSize s = FS /\ sbd_frame_size s = sbd_frame_size s0 /\ sbd_innov_save s = sbd_innov_save s0
/\ sb_blocks s S a = sb_blocks s0 S a
/\ DREP OUT STEREO m (a_low a) low LBL /\ dec_depth low = x_dk X /\ (if xr then EXCREADY m (a_low a) low else True)
/\ dec_mode low = sbm_nb_mode (sbd_mode s0) /\ dec_nested low
/\ bits_rep rsegs m A D b /\ bits_ok b /\ bits_keep b
/\ rw_cells rsegs m OUT (f32 ows) /\ length ows = 2000%nat
/\ rw_cells rsegs m STEREO [CB 24 stb]
/\ rtables_pristine m /\ stderr_wfile m /\ ssp_cells m (x_canary X).

Definition sbctx0 (OUTL : Z) (m : mem) (s : sbd_state bptr) (low : dec_state bptr) (b : bits_st bptr) (j : sb_junk)
(ows : list word) (stb : list byte) : Prop :=
munch sbWX (x_m0 X) m /\ wmono rsegs (x_m0 X) m /\ mem_inv rsegs m
/\ sb_pieces m S s a OUT j /\ sb_junk_ok s j /\ sb_bufs rsegs m a j /\ sb_inv s
/\ sbd_mode s = sbd_mode s0 /\ sbd_subframeSize s = FS /\ sbd_frame_size s = sbd_frame_size s0 /\ sbd_innov_save s = sbd_innov_save s0
/\ sb_blocks s S a = sb_blocks s0 S a
/\ DREP OUTL STEREO m (a_low a) low LBL /\ dec_depth low = x_dk X /\ True
/\ dec_mode low = sbm_nb_mode (sbd_mode s0) /\ dec_nested low
/\ bits_rep rsegs m A D b /\ bits_ok b /\ bits_keep b
/\ rw_cells rsegs m OUT (f32 ows) /\ length ows = 2000%nat
/\ rw_cells rsegs m STEREO [CB 24 stb]
/\ rtables_pristine m /\ stderr_wfile m /\ ssp_cells m (x_canary X).
End Ctx.
#[export] Hint Rewrite cells_size_fr_saves : chunk_sizes.

Record sb_ihyps {RCEIL : RunCeiling} (k : nat) (X : sbinv) : Prop := SBIH {
ih_lay : sb_layout (x_S X) (x_out X) (x_A X) (x_D X) (sb_buf_size (x_b0 X)) (x_stereo X)
(a_g0 (x_a X)) (a_g1 (x_a X)) (a_exc (x_a X)) (4 * sbd_subframeSize (x_s X))
(a_oq (x_a X)) (a_iq (x_a X)) (a_msp (x_a X)) (a_pg (x_a X)) (a_er (x_a X))
(x_lo X) (bv_unsigned (x_sp X)) (x_LBL X);
ih_lo : x_lo X + SB_LOCAL_DEPTH + x_RD X <= bv_unsigned (x_sp X);
ih_RD : 0 <= x_RD X;
ih_RDd : forall d : dec_state bptr, dec_depth d = x_dk X -> rdec_depth d = x_RD X;
ih_dk : (x_dk X <= k)%nat /\ (x_dk X <= 2)%nat;
ih_spx : bv_unsigned (x_sp X) < 2^63;
ih_hi : x_A X + 48 <= 2^64 /\ x_out X + 8000 <= 2^64 /\ x_stereo X + 24 <= 2^64;
ih_sp16 : bv_unsigned (x_sp X) mod 16 = 0;
ih_Sal : x_S X mod 8 = 0;
ih_out4 : x_out X mod 4 = 0;
ih_ster4 : x_stereo X mod 4 = 0;
ih_inv0 : sb_inv (x_s X);
ih_isave : match sbd_innov_save (x_s X) with None => True | Some k => k = 8 * sbd_subframeSize (x_s X) end;
ih_nodup : List.NoDup (map blk_id (sb_blocks (x_s X) (x_S X) (x_a X) ++ x_LBL X));
ih_apart : lbd_apart (sb_blocks (x_s X) (x_S X) (x_a X) ++ x_LBL X);
ih_range : forall x, In x (sb_blocks (x_s X) (x_S X) (x_a X) ++ x_LBL X) -> rblock_range (blk_addr x) (blk_size x);
ih_Drange : rblock_range (x_D X) (sb_buf_size (x_b0 X));
ih_Dapart : forall x, In x (sb_blocks (x_s X) (x_S X) (x_a X) ++ x_LBL X) -> apart (x_D X) (sb_buf_size (x_b0 X)) (blk_addr x) (blk_size x);
ih_rlay : rdec_layout (x_A X) (x_out X) (x_stereo X) (x_lo X) (bv_unsigned (x_sp X));
ih_owner : sb_owner (x_b0 X) = 1;
ih_hyps : sb_hyps k }.
