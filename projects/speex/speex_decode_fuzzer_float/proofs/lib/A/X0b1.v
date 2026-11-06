(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cp X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X081 X05l X05m X09f X06d X069 X082 X08y.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0ys X0x2 X0yt X0zq.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).

Definition A_sb_decode_lost : Z := 0xc0bd8.
Definition A_gc_quant_bound : Z := 0x271e0.
Definition SB_LA_PC : Z := 0xbf0bc.
Definition SB_TA_PC : Z := 0xc0280.
Definition SB_FRAME : Z := 736.
Definition SB_VLA_AREA : Z := 480.
Definition SB_SUBMODE_BITS : Z := 3.

Definition sbmode_struct (mo : spx_mode) : Z := match mo with ModeUWB => A_sb_uwb_mode | _ => A_sb_wb_mode end.

Definition sb_sub_addr (i : Z) : Z :=
if i =? 1 then A_wb_submode1 else if i =? 2 then A_wb_submode2 else if i =? 3 then A_wb_submode3 else if i =? 4 then A_wb_submode4 else 0.
Lemma sb_submode_cases : forall mo i sm, (mo = ModeWB \/ mo = ModeUWB) -> 0 <= i <= 7 -> submode_at (sbm_submodes mo) i = Some sm ->
(mo = ModeWB /\ ((i = 1 /\ sm = wb_submode1) \/ (i = 2 /\ sm = wb_submode2) \/ (i = 3 /\ sm = wb_submode3) \/ (i = 4 /\ sm = wb_submode4)))
\/ (mo = ModeUWB /\ i = 1 /\ sm = wb_submode1).
Proof.
intros mo i sm Hmo Hi H.
assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
destruct Hmo as [-> | ->]; destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]; cbn in H; try discriminate H; injection H as <-; tauto.
Qed.

Definition sb_exc_hull (mo : spx_mode) : Z := match mo with ModeUWB => 384 | _ => 224 end.
Definition sb_top_stale (usp : Z) (mo : spx_mode) (sm : submode) : Z :=
usp + -1216 - sb_exc_hull mo - (if sm_double_codebook sm =? 0 then 0 else 224).

Section Pure.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

Definition sbw_wb b : Z * bits_st ptr := if 0 <? speex_bits_remaining b then speex_bits_peek b else (0, b).
Definition sbw_id b : Z := let '(wideband, b1) := sbw_wb b in if negb (wideband =? 0) then uv (ub b1 1) SB_SUBMODE_BITS else 0.
Definition sbw_bits b : bits_st ptr := let '(wideband, b1) := sbw_wb b in if negb (wideband =? 0) then ub (ub b1 1) SB_SUBMODE_BITS else b1.

Definition sbsub_bits (sm : submode) b : bits_st ptr :=
match sm_innovation_unquant sm with
| None => ub b 5
| Some k => let b1 := innov_bits k (ub b 4) in if negb (sm_double_codebook sm =? 0) then innov_bits k b1 else b1
end.
Fixpoint sbsubs_bits (n : nat) (sm : submode) b : bits_st ptr :=
match n with O => b | S n' => sbsubs_bits n' sm (sbsub_bits sm b) end.
End Pure.

Section Pieces.
Implicit Types (s : sbd_state bptr).
Local Notation MODEP mo := (sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode mo).
Local Notation SUBP mo := (sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR mo).

Definition sbp_hdr s (a : sb_addrs) : list cell :=
[C8 (Z_to_bv 64 (MODEP (sbd_mode s))); C8 (Z_to_bv 64 (a_low a));
C4 (Z_to_bv 64 (sbd_full_frame_size s)); C4 (Z_to_bv 64 (sbd_frame_size s));
C4 (Z_to_bv 64 (sbd_subframeSize s)); C4 (Z_to_bv 64 (sbd_nbSubframes s)); C4 (Z_to_bv 64 (sbd_lpcSize s))].

Definition sbp_ptrs s (a : sb_addrs) (OUT : Z) : list cell :=
[C4 (Z_to_bv 64 (sbd_sampling_rate s)); C4 (Z_to_bv 64 (sbd_lpc_enh_enabled s)); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 (a_g0 a)); C8 (Z_to_bv 64 (a_g1 a)); C8 (Z_to_bv 64 (a_exc a));
C8 (Z_to_bv 64 (a_oq a)); C8 (Z_to_bv 64 (a_iq a)); C8 (Z_to_bv 64 (a_msp a));
C8 (Z_to_bv 64 (a_pg a)); C8 (Z_to_bv 64 (a_er a)); C8 (Z_to_bv 64 (sb_isave_ptr OUT s))].

Definition sbp_cfg s (pad1 : list byte) : list cell :=
[C4 (Z_to_bv 64 (sbd_encode_submode s)); CB 4 pad1; C8 (Z_to_bv 64 (SUBP (sbd_mode s)))].

Definition sb_pieces (m : mem) (S : Z) s (a : sb_addrs) (OUT : Z) (le seed : word) (pad1 pad2 : list byte) : Prop :=
rw_cells bsegs m S (sbp_hdr s a)
/\ rw_cells bsegs m (S + 36) [C4 (Z_to_bv 64 (sbd_first s))]
/\ rw_cells bsegs m (S + 40) (sbp_ptrs s a OUT)
/\ rw_cells bsegs m (S + 128) [C4 le]
/\ rw_cells bsegs m (S + 132) [C4 seed]
/\ rw_cells bsegs m (S + 136) (sbp_cfg s pad1)
/\ rw_cells bsegs m (S + 152) [C4 (Z_to_bv 64 (sbd_submodeID s))]
/\ rw_cells bsegs m (S + 156) [CB 4 pad2].

Lemma cells_size_sbp_hdr : forall s a, cells_size (sbp_hdr s a) = 36%nat. Proof. reflexivity. Qed.
Lemma cells_size_sbp_ptrs : forall s a OUT, cells_size (sbp_ptrs s a OUT) = 88%nat. Proof. reflexivity. Qed.
Lemma cells_size_sbp_cfg : forall s p, cells_size (sbp_cfg s p) = 16%nat. Proof. reflexivity. Qed.

Lemma sb_cells_app : forall s a OUT j,
SBCELLS s a OUT j = sbp_hdr s a ++ [C4 (Z_to_bv 64 (sbd_first s))] ++ sbp_ptrs s a OUT ++ [C4 (sj_last_ener j)] ++ [C4 (sj_seed j)]
++ sbp_cfg s (sj_pad1 j) ++ [C4 (Z_to_bv 64 (sbd_submodeID s))] ++ [CB 4 (sj_pad2 j)].
Proof. intros. reflexivity. Qed.

Lemma sb_pieces_iff : forall m S s a OUT j,
rw_cells bsegs m S (SBCELLS s a OUT j) <-> sb_pieces m S s a OUT (sj_last_ener j) (sj_seed j) (sj_pad1 j) (sj_pad2 j).
Proof.
intros m S s a OUT j. rewrite sb_cells_app. unfold sb_pieces.
repeat rewrite rw_cells_app. cbn [cells_size csize Nat.add length app sbp_hdr sbp_ptrs sbp_cfg].
rewrite <- !Z.add_assoc.
change (Z.of_nat 36) with 36. change (Z.of_nat 4) with 4. change (Z.of_nat 88) with 88. change (Z.of_nat 16) with 16.
change (36 + 4) with 40. change (36 + (4 + 88)) with 128. change (36 + (4 + (88 + 4))) with 132. change (36 + (4 + (88 + (4 + 4)))) with 136.
change (36 + (4 + (88 + (4 + (4 + 16))))) with 152. change (36 + (4 + (88 + (4 + (4 + (16 + 4)))))) with 156.
tauto.
Qed.
End Pieces.
#[export] Hint Rewrite cells_size_sbp_hdr cells_size_sbp_ptrs cells_size_sbp_cfg : chunk_sizes.

Definition sha (x : Z) : Z := Z.shiftr x 3 + SHB.
Record sb_vslots := SBV {
v_8 : word; v_144 : word; v_280 : word; v_288 : word; v_392 : word; v_456 : word; v_480 : word;
v_512 : word; v_520 : word; v_528 : word; v_544 : word; v_552 : word; v_560 : word; v_568 : word }.
Definition sb_slots (usp S OUT A f sf MODE fsz : Z) (v : sb_vslots) : list cell :=
[C8 (Z_to_bv 64 0); C8 (v_8 v); C8 (Z_to_bv 64 7); C8 (Z_to_bv 64 7);
C8 (Z_to_bv 64 3); C8 (Z_to_bv 64 3); C8 (Z_to_bv 64 (Z.shiftr (S + 80) 3)); C8 (Z_to_bv 64 (sha (S + 36)));
C8 (Z_to_bv 64 (S + 36)); C8 (Z_to_bv 64 (usp + -736)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (MODE + 32));
C8 (Z_to_bv 64 (18446744073709551615 - (usp + -896))); C8 (Z_to_bv 64 sf); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 4);
C8 (Z_to_bv 64 (OUT + 4 * fsz)); C8 (Z_to_bv 64 (usp + -896)); C8 (v_144 v); C8 (Z_to_bv 64 f);
C8 (Z_to_bv 64 2147483647); C8 (Z_to_bv 64 (S + 112)); C8 (Z_to_bv 64 (S + 96)); C8 (Z_to_bv 64 (18446744073709551615 - (usp + -800)));
C8 (Z_to_bv 64 (sha (S + 80))); C8 (Z_to_bv 64 (usp + -1180)); C8 (Z_to_bv 64 (S + 104)); C8 (Z_to_bv 64 (S + 132));
C8 (Z_to_bv 64 32); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 (usp + -1088)); C8 (Z_to_bv 64 4);
C8 (Z_to_bv 64 (usp + -800)); C8 (Z_to_bv 64 (sha (S + 20))); C8 (Z_to_bv 64 (S + 20)); C8 (v_280 v);
C8 (v_288 v); C8 (Z_to_bv 64 (sha (S + 120))); C8 (Z_to_bv 64 (S + 120)); C8 (Z_to_bv 64 (18446744073709551615 - (usp + -992)));
C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 32); C8 (Z_to_bv 64 (S + 88)); C8 (Z_to_bv 64 (S + 72));
C8 (Z_to_bv 64 (sha (S + 152))); C8 (Z_to_bv 64 (sha (S + 144))); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (S + 144));
C8 (Z_to_bv 64 (S + 152)); C8 (v_392 v); C8 (Z_to_bv 64 (S + 80)); C8 (Z_to_bv 64 (sha (S + 28)));
C8 (Z_to_bv 64 (S + 28)); C8 (Z_to_bv 64 (usp + -992)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (sha (S + 32)));
C8 (Z_to_bv 64 (S + 32)); C8 (v_456 v); C8 (Z_to_bv 64 (sha (S + 24))); C8 (Z_to_bv 64 (S + 24));
C8 (v_480 v); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 OUT); C8 (Z_to_bv 64 4294967296);
C8 (v_512 v); C8 (v_520 v); C8 (v_528 v); C8 (Z_to_bv 64 f);
C8 (v_544 v); C8 (v_552 v); C8 (v_560 v); C8 (v_568 v)].
Lemma cells_size_sb_slots : forall usp S OUT A f sf MODE fsz v, cells_size (sb_slots usp S OUT A f sf MODE fsz v) = 576%nat.
Proof. reflexivity. Qed.

Definition sb_saves (F0 : bvmap 5 word) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
[C8 (reg_get F0 (Z_to_bv 5 22)); C8 (reg_get F0 (Z_to_bv 5 21)); C8 (reg_get F0 (Z_to_bv 5 20)); C8 (reg_get F0 (Z_to_bv 5 19));
C8 (reg_get F0 (Z_to_bv 5 18)); C8 (reg_get F0 (Z_to_bv 5 9)); C8 (reg_get F0 (Z_to_bv 5 8));
C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Lemma cells_size_sb_saves : forall F0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11, cells_size (sb_saves F0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) = 160%nat.
Proof. reflexivity. Qed.
#[export] Hint Rewrite cells_size_sb_slots cells_size_sb_saves : chunk_sizes.

Definition sb_fhdr (j24 : list byte) (dtx : word) (j36 : list byte) : list cell :=
[C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x10d9a); C8 (Z_to_bv 64 0xbe6c0); CB 8 j24; C4 dtx; CB 20 j36].
Definition sb_fshadow : list cell :=
[C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 4);
C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))].
Lemma cells_size_sb_fhdr : forall j24 dtx j36, cells_size (sb_fhdr j24 dtx j36) = 56%nat. Proof. reflexivity. Qed.

Record sb_rjunk := SBRJ {
j_ra : word; j_t0 : word; j_t1 : word; j_t2 : word; j_a0 : word; j_a1 : word; j_a2 : word; j_a3 : word; j_a4 : word; j_a5 : word; j_a6 : word; j_a7 : word;
j_s2 : word; j_s3 : word; j_s4 : word; j_s5 : word; j_s7 : word; j_s8 : word; j_s9 : word; j_s10 : word; j_s11 : word; j_t3 : word; j_t4 : word; j_t5 : word; j_t6 : word }.
Definition R_LA (usp S OUT MODE sub : Z) (gp tp : word) (k : sb_rjunk) : bvmap 5 word :=
mkR (j_ra k) (Z_to_bv 64 (usp + -1216)) gp tp (Z_to_bv 64 (sha (S + 24))) (j_t1 k) (j_t2 k) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736))
(Z_to_bv 64 (S + 24)) (j_a1 k) (j_a2 k) (j_a3 k) (j_a4 k) (j_a5 k) (j_a6 k) (j_a7 k)
(j_s2 k) (j_s3 k) (j_s4 k) (j_s5 k) (Z_to_bv 64 SHB) (Z_to_bv 64 (18446744073709551615 - (usp + -1184))) (j_s8 k)
(j_s9 k) (j_s10 k) (Z_to_bv 64 (usp + -1184)) (j_t3 k) (j_t4 k) (j_t5 k) (j_t6 k).
Definition R_TA (usp S OUT : Z) (gp tp : word) (k : sb_rjunk) : bvmap 5 word :=
mkR (j_ra k) (Z_to_bv 64 (usp + -1216)) gp tp (j_t0 k) (j_t1 k) (j_t2 k) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -736))
(j_a0 k) (j_a1 k) (j_a2 k) (j_a3 k) (j_a4 k) (j_a5 k) (j_a6 k) (j_a7 k)
(j_s2 k) (j_s3 k) (j_s4 k) (j_s5 k) (Z_to_bv 64 SHB) (j_s7 k) (j_s8 k)
(j_s9 k) (j_s10 k) (j_s11 k) (j_t3 k) (j_t4 k) (j_t5 k) (j_t6 k).
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).

Definition A_sb_decode_lost : Z := 0xb85b8.
Definition A_gc_quant_bound : Z := 0x271e0.
Definition SB_LA_PC : Z := 0xb6fd0.
Definition SB_TA_PC : Z := 0xb7d50.
Definition SB_FRAME : Z := 608.
Definition SB_VLA_AREA : Z := 480.
Definition SB_SUBMODE_BITS : Z := 3.

Definition sbmode_struct (mo : spx_mode) : Z := match mo with ModeUWB => A_sb_uwb_mode | _ => A_sb_wb_mode end.

Definition sb_sub_addr (i : Z) : Z :=
if i =? 1 then A_wb_submode1 else if i =? 2 then A_wb_submode2 else if i =? 3 then A_wb_submode3 else if i =? 4 then A_wb_submode4 else 0.
Lemma sb_submode_cases : forall mo i sm, (mo = ModeWB \/ mo = ModeUWB) -> 0 <= i <= 7 -> submode_at (sbm_submodes mo) i = Some sm ->
(mo = ModeWB /\ ((i = 1 /\ sm = wb_submode1) \/ (i = 2 /\ sm = wb_submode2) \/ (i = 3 /\ sm = wb_submode3) \/ (i = 4 /\ sm = wb_submode4)))
\/ (mo = ModeUWB /\ i = 1 /\ sm = wb_submode1).
Proof.
intros mo i sm Hmo Hi H.
assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
destruct Hmo as [-> | ->]; destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]; cbn in H; try discriminate H; injection H as <-; tauto.
Qed.

Definition sb_exc_hull (mo : spx_mode) : Z := match mo with ModeUWB => 384 | _ => 224 end.
Definition sb_top_stale (usp : Z) (mo : spx_mode) (sm : submode) : Z :=
usp + -1088 - sb_exc_hull mo - (if sm_double_codebook sm =? 0 then 0 else 224).

Section Pure.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

Definition sbw_wb b : Z * bits_st ptr := if 0 <? speex_bits_remaining b then speex_bits_peek b else (0, b).
Definition sbw_id b : Z := let '(wideband, b1) := sbw_wb b in if negb (wideband =? 0) then uv (ub b1 1) SB_SUBMODE_BITS else 0.
Definition sbw_bits b : bits_st ptr := let '(wideband, b1) := sbw_wb b in if negb (wideband =? 0) then ub (ub b1 1) SB_SUBMODE_BITS else b1.

Definition sbsub_bits (sm : submode) b : bits_st ptr :=
match sm_innovation_unquant sm with
| None => ub b 5
| Some k => let b1 := innov_bits k (ub b 4) in if negb (sm_double_codebook sm =? 0) then innov_bits k b1 else b1
end.
Fixpoint sbsubs_bits (n : nat) (sm : submode) b : bits_st ptr :=
match n with O => b | S n' => sbsubs_bits n' sm (sbsub_bits sm b) end.
End Pure.

Section Pieces.
Implicit Types (s : sbd_state bptr).
Local Notation MODEP mo := (sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode mo).
Local Notation SUBP mo := (sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR mo).

Definition sbp_hdr s (a : sb_addrs) : list cell :=
[C8 (Z_to_bv 64 (MODEP (sbd_mode s))); C8 (Z_to_bv 64 (a_low a));
C4 (Z_to_bv 64 (sbd_full_frame_size s)); C4 (Z_to_bv 64 (sbd_frame_size s));
C4 (Z_to_bv 64 (sbd_subframeSize s)); C4 (Z_to_bv 64 (sbd_nbSubframes s)); C4 (Z_to_bv 64 (sbd_lpcSize s))].

Definition sbp_ptrs s (a : sb_addrs) (OUT : Z) : list cell :=
[C4 (Z_to_bv 64 (sbd_sampling_rate s)); C4 (Z_to_bv 64 (sbd_lpc_enh_enabled s)); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 (a_g0 a)); C8 (Z_to_bv 64 (a_g1 a)); C8 (Z_to_bv 64 (a_exc a));
C8 (Z_to_bv 64 (a_oq a)); C8 (Z_to_bv 64 (a_iq a)); C8 (Z_to_bv 64 (a_msp a));
C8 (Z_to_bv 64 (a_pg a)); C8 (Z_to_bv 64 (a_er a)); C8 (Z_to_bv 64 (sb_isave_ptr OUT s))].

Definition sbp_cfg s (pad1 : list byte) : list cell :=
[C4 (Z_to_bv 64 (sbd_encode_submode s)); CB 4 pad1; C8 (Z_to_bv 64 (SUBP (sbd_mode s)))].

Definition sb_pieces (m : mem) (S : Z) s (a : sb_addrs) (OUT : Z) (le seed : word) (pad1 pad2 : list byte) : Prop :=
rw_cells asegs m S (sbp_hdr s a)
/\ rw_cells asegs m (S + 36) [C4 (Z_to_bv 64 (sbd_first s))]
/\ rw_cells asegs m (S + 40) (sbp_ptrs s a OUT)
/\ rw_cells asegs m (S + 128) [C4 le]
/\ rw_cells asegs m (S + 132) [C4 seed]
/\ rw_cells asegs m (S + 136) (sbp_cfg s pad1)
/\ rw_cells asegs m (S + 152) [C4 (Z_to_bv 64 (sbd_submodeID s))]
/\ rw_cells asegs m (S + 156) [CB 4 pad2].

Lemma cells_size_sbp_hdr : forall s a, cells_size (sbp_hdr s a) = 36%nat. Proof. reflexivity. Qed.
Lemma cells_size_sbp_ptrs : forall s a OUT, cells_size (sbp_ptrs s a OUT) = 88%nat. Proof. reflexivity. Qed.
Lemma cells_size_sbp_cfg : forall s p, cells_size (sbp_cfg s p) = 16%nat. Proof. reflexivity. Qed.

Lemma sb_cells_app : forall s a OUT j,
SBCELLS s a OUT j = sbp_hdr s a ++ [C4 (Z_to_bv 64 (sbd_first s))] ++ sbp_ptrs s a OUT ++ [C4 (sj_last_ener j)] ++ [C4 (sj_seed j)]
++ sbp_cfg s (sj_pad1 j) ++ [C4 (Z_to_bv 64 (sbd_submodeID s))] ++ [CB 4 (sj_pad2 j)].
Proof. intros. reflexivity. Qed.

Lemma sb_pieces_iff : forall m S s a OUT j,
rw_cells asegs m S (SBCELLS s a OUT j) <-> sb_pieces m S s a OUT (sj_last_ener j) (sj_seed j) (sj_pad1 j) (sj_pad2 j).
Proof.
intros m S s a OUT j. rewrite sb_cells_app. unfold sb_pieces.
repeat rewrite rw_cells_app. cbn [cells_size csize Nat.add length app sbp_hdr sbp_ptrs sbp_cfg].
rewrite <- !Z.add_assoc.
change (Z.of_nat 36) with 36. change (Z.of_nat 4) with 4. change (Z.of_nat 88) with 88. change (Z.of_nat 16) with 16.
change (36 + 4) with 40. change (36 + (4 + 88)) with 128. change (36 + (4 + (88 + 4))) with 132. change (36 + (4 + (88 + (4 + 4)))) with 136.
change (36 + (4 + (88 + (4 + (4 + 16))))) with 152. change (36 + (4 + (88 + (4 + (4 + (16 + 4)))))) with 156.
tauto.
Qed.
End Pieces.
#[export] Hint Rewrite cells_size_sbp_hdr cells_size_sbp_ptrs cells_size_sbp_cfg : chunk_sizes.

Definition sha (x : Z) : Z := Z.shiftr x 3 + SHB.
Record sb_vslots := SBV {
v_8 : word; v_120 : word; v_248 : word; v_256 : word; v_264 : word; v_296 : word; v_384 : word; v_392 : word; v_400 : word;
v_416 : word; v_424 : word; v_432 : word; v_440 : word }.
Definition sb_slots (usp S OUT A f sf MODE fsz : Z) (v : sb_vslots) : list cell :=
[C8 (Z_to_bv 64 0); C8 (v_8 v); C8 (Z_to_bv 64 7); C8 (Z_to_bv 64 3);
C8 (Z_to_bv 64 (sha (S + 36))); C8 (Z_to_bv 64 (S + 36)); C8 (Z_to_bv 64 (usp + -608)); C8 (Z_to_bv 64 f);
C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 (OUT + 4 * fsz + 4)); C8 (Z_to_bv 64 (OUT + 4 * fsz)); C8 (Z_to_bv 64 (sha (usp + -1052)));
C8 (Z_to_bv 64 (usp + -1052)); C8 (Z_to_bv 64 sf); C8 (Z_to_bv 64 (usp + -768)); C8 (v_120 v);
C8 (Z_to_bv 64 (MODE + 32)); C8 (Z_to_bv 64 (S + 112)); C8 (Z_to_bv 64 (S + 96)); C8 (Z_to_bv 64 (S + 104));
C8 (Z_to_bv 64 (usp + -960)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 OUT); C8 (Z_to_bv 64 (S + 132));
C8 (Z_to_bv 64 (usp + -672)); C8 (Z_to_bv 64 (usp + -864)); C8 (Z_to_bv 64 (S + 20)); C8 (Z_to_bv 64 (sha (S + 20)));
C8 (Z_to_bv 64 (2^36 - 16)); C8 (Z_to_bv 64 (S + 88)); C8 (Z_to_bv 64 (S + 80)); C8 (v_248 v);
C8 (v_256 v); C8 (v_264 v); C8 (Z_to_bv 64 (S + 120)); C8 (Z_to_bv 64 (S + 28));
C8 (Z_to_bv 64 (sha (S + 28))); C8 (v_296 v); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (usp + -1056));
C8 (Z_to_bv 64 (S + 32)); C8 (Z_to_bv 64 (sha (S + 152))); C8 (Z_to_bv 64 (sha (S + 144))); C8 (Z_to_bv 64 (S + 152));
C8 (Z_to_bv 64 (S + 144)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (S + 72)); C8 (Z_to_bv 64 (sha (S + 32)));
C8 (v_384 v); C8 (v_392 v); C8 (v_400 v); C8 (Z_to_bv 64 f);
C8 (v_416 v); C8 (v_424 v); C8 (v_432 v); C8 (v_440 v)].
Lemma cells_size_sb_slots : forall usp S OUT A f sf MODE fsz v, cells_size (sb_slots usp S OUT A f sf MODE fsz v) = 448%nat.
Proof. reflexivity. Qed.

Definition sb_saves (F0 : bvmap 5 word) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
[C8 (reg_get F0 (Z_to_bv 5 22)); C8 (reg_get F0 (Z_to_bv 5 21)); C8 (reg_get F0 (Z_to_bv 5 20)); C8 (reg_get F0 (Z_to_bv 5 19));
C8 (reg_get F0 (Z_to_bv 5 18)); C8 (reg_get F0 (Z_to_bv 5 9)); C8 (reg_get F0 (Z_to_bv 5 8));
C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Lemma cells_size_sb_saves : forall F0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11, cells_size (sb_saves F0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) = 160%nat.
Proof. reflexivity. Qed.
#[export] Hint Rewrite cells_size_sb_slots cells_size_sb_saves : chunk_sizes.

Definition sb_fhdr (j24 : list byte) (dtx : word) (j36 : list byte) : list cell :=
[C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x10d82); C8 (Z_to_bv 64 0xb67bc); CB 8 j24; C4 dtx; CB 20 j36].
Definition sb_fshadow : list cell :=
[C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 4);
C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))].
Lemma cells_size_sb_fhdr : forall j24 dtx j36, cells_size (sb_fhdr j24 dtx j36) = 56%nat. Proof. reflexivity. Qed.

Record sb_rjunk := SBRJ {
j_ra : word; j_t0 : word; j_t1 : word; j_t2 : word; j_a0 : word; j_a1 : word; j_a2 : word; j_a3 : word; j_a4 : word; j_a5 : word; j_a6 : word; j_a7 : word;
j_s2 : word; j_s3 : word; j_s4 : word; j_s5 : word; j_s6 : word; j_s7 : word; j_s8 : word; j_s11 : word; j_t3 : word; j_t4 : word; j_t5 : word; j_t6 : word }.
Definition R_LA (usp S OUT MODE sub : Z) (gp tp : word) (k : sb_rjunk) : bvmap 5 word :=
mkR (j_ra k) (Z_to_bv 64 (usp + -1088)) gp tp (j_t0 k) (j_t1 k) (j_t2 k) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608))
(j_a0 k) (j_a1 k) (j_a2 k) (j_a3 k) (j_a4 k) (j_a5 k) (Z_to_bv 64 4096) (j_a7 k)
(Z_to_bv 64 (sha (S + 24))) (j_s3 k) (Z_to_bv 64 (S + 28)) (Z_to_bv 64 sub) (Z_to_bv 64 (S + 24)) (j_s7 k) (Z_to_bv 64 (MODE + 32))
(Z_to_bv 64 SHB) (Z_to_bv 64 OUT) (j_s11 k) (j_t3 k) (j_t4 k) (j_t5 k) (j_t6 k).
Definition R_TA (usp S OUT : Z) (gp tp : word) (k : sb_rjunk) : bvmap 5 word :=
mkR (j_ra k) (Z_to_bv 64 (usp + -1088)) gp tp (j_t0 k) (j_t1 k) (j_t2 k) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -608))
(j_a0 k) (j_a1 k) (j_a2 k) (j_a3 k) (j_a4 k) (j_a5 k) (j_a6 k) (j_a7 k)
(j_s2 k) (j_s3 k) (j_s4 k) (j_s5 k) (j_s6 k) (j_s7 k) (j_s8 k)
(Z_to_bv 64 SHB) (Z_to_bv 64 OUT) (Z_to_bv 64 S) (j_t3 k) (j_t4 k) (j_t5 k) (j_t6 k).
