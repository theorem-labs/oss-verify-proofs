(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1nu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05s X05u
X081 X05l X05m X09f X06d X069 X082 X08y X0b1 X0b0.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0wl X0wn X0ys X0x2 X0yt X0zq X11l X11k.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11k.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition NBDEC_FRAMES : nat := 2.
Definition NBDEC_CREDIT : Z := 8.
Definition NBDEC_STACK : Z := 8768.

Definition SB_OWN_STACK : Z := 1216 + SB_LOOP_STACK.
Fixpoint dec_frames (d : dec_state bptr) : nat := match d with DecNB _ => NBDEC_FRAMES | DecSB _ low => S (dec_frames low) end.
Fixpoint dec_stack (d : dec_state bptr) : Z := match d with DecNB _ => NBDEC_STACK | DecSB _ low => SB_OWN_STACK + dec_stack low end.

Fixpoint dec_credit (d : dec_state bptr) : Z :=
match d with DecNB _ => NBDEC_CREDIT | DecSB _ low => 1 + 4 * (Z.of_nat (dec_depth low) - 1) + dec_credit low end.

Lemma dec_depth_le_frames : forall d : dec_state bptr, (dec_depth d <= dec_frames d)%nat.
Proof. induction d as [st | s low IH]; cbn [dec_depth dec_frames]; [unfold NBDEC_FRAMES; lia | lia]. Qed.
Lemma dec_credit_pos : forall d : dec_state bptr, 1 <= dec_credit d.
Proof.
induction d as [st | s low IH]; cbn [dec_credit]; [unfold NBDEC_CREDIT; lia |].
pose proof (dec_depth_pos low). lia.
Qed.

Definition isave_ok (d : dec_state bptr) : Prop :=
match d with
| DecNB st => match nb_innov_save st with None => True | Some k => 160 <= k /\ 4 * (k + 160) <= 8000 end
| DecSB s _ => match sbd_innov_save s with None => True | Some k => k = 2 * sbd_frame_size s end
end.

Definition blocks_al8 (LBD : list block) : Prop := forall x, In x LBD -> blk_addr x mod 8 = 0.

Section DecCPS.
Variable RT : rt_sig.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).

Definition dec_W (A OUT STEREO : Z) (LBD : list block) : list (Z * Z) :=
(A, A + BITS_SIZEOF) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP.

Definition dec_cps_at (ENTRY : Z) (d : dec_state bptr) : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (OUT STEREO S A D : Z) (LBD : list block) (b : bits_st bptr) (lo fh PD ND : Z) (kh : nat)
(ows : list word) (stb : list byte) (q q' : pst) (ret : Z) (d' : dec_state bptr) (b' : bits_st bptr),
prun (speex_decode (St := pst) p_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M d b 0) q = Some ((ret, d', b'), q') ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 OUT -> tp = Z_to_bv 64 0x638c98 ->

DREP OUT STEREO m S d LBD -> (dec_depth d <= 3)%nat -> isave_ok d -> dec_nestedR d -> List.NoDup (map blk_id LBD) ->
blocks_al8 LBD ->
(forall x, In x LBD -> In (blk_addr x, blk_size x) (rt_live RT Σ)) ->

bits_rep bsegs m A D b -> bits_ok b ->
In (PD, ND) (rt_live RT Σ) -> PD <= D -> D + sb_buf_size b <= PD + ND -> (forall x, In x LBD -> blk_addr x <> PD) ->

rw_cells bsegs m OUT (f32 ows) -> length ows = 2000%nat -> rw_cells bsegs m STEREO [CB 24 stb] ->
In (fh, kh) (rt_frames RT Σ) ->
in_frame_obj RT Σ m fh kh A BITS_SIZEOF -> in_frame_obj RT Σ m fh kh OUT 8000 -> in_frame_obj RT Σ m fh kh STEREO 24 ->
hidp (A + BITS_SIZEOF <= OUT \/ OUT + 8000 <= A) -> hidp (A + BITS_SIZEOF <= STEREO \/ STEREO + 24 <= A) -> hidp (OUT + 8000 <= STEREO \/ STEREO + 24 <= OUT) ->

fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> ERR_rep m -> io_ssp m ->

(length (rt_frames RT Σ) + dec_frames d <= FRAMES_MAX)%nat -> dec_credit d <= rt_credit RT Σ ->
pois_above (rt_pois RT Σ) (bv_unsigned sp) ->
ART RT Σ m -> mem_inv bsegs m -> X1cn.frm0 fc ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + dec_stack d <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 ->
exists bs, p_err q' = p_err q ++ bs /\
cpsE bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc ENTRY m)))
(Spec.X1nu.evw 2 bs)
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' (PMfd F0 fs0) (fun ms => exists m' (ows' : list word) (stb' : list byte),
ret_stL (fun _ fc' => X1cn.frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 ret) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (dec_W A OUT STEREO LBD) m m'
/\ DREP OUT STEREO m' S d' LBD /\ (ret = 0 -> EXCREADY m' S d')
/\ bits_rep bsegs m' A D b' /\ bits_ok b'
/\ rw_cells bsegs m' OUT (f32 ows') /\ length ows' = 2000%nat /\ rw_cells bsegs m' STEREO [CB 24 stb']
/\ acc bsegs m' A BITS_SIZEOF /\ acc bsegs m' OUT 8000 /\ acc bsegs m' STEREO 24
/\ ERR_rep m' /\ (forall so, OUT_rep so m -> OUT_rep so m')) c
/\ -2 <= ret <= 0 /\ dec_depth d' = dec_depth d /\ dec_mode d' = dec_mode d /\ dec_nestedR d'
/\ sb_owner b' = sb_owner b /\ sb_chars b' = sb_chars b /\ sb_buf_size b' = sb_buf_size b
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ - dec_credit d <= rt_credit RT Σ' <= rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).
End DecCPS.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition NBDEC_FRAMES : nat := 2.
Definition NBDEC_CREDIT : Z := 8.
Definition NBDEC_STACK : Z := 8736.

Definition SB_OWN_STACK : Z := 1088 + SB_LOOP_STACK.
Fixpoint dec_frames (d : dec_state bptr) : nat := match d with DecNB _ => NBDEC_FRAMES | DecSB _ low => S (dec_frames low) end.
Fixpoint dec_stack (d : dec_state bptr) : Z := match d with DecNB _ => NBDEC_STACK | DecSB _ low => SB_OWN_STACK + dec_stack low end.

Fixpoint dec_credit (d : dec_state bptr) : Z :=
match d with DecNB _ => NBDEC_CREDIT | DecSB _ low => 1 + 4 * (Z.of_nat (dec_depth low) - 1) + dec_credit low end.

Lemma dec_depth_le_frames : forall d : dec_state bptr, (dec_depth d <= dec_frames d)%nat.
Proof. induction d as [st | s low IH]; cbn [dec_depth dec_frames]; [unfold NBDEC_FRAMES; lia | lia]. Qed.
Lemma dec_credit_pos : forall d : dec_state bptr, 1 <= dec_credit d.
Proof.
induction d as [st | s low IH]; cbn [dec_credit]; [unfold NBDEC_CREDIT; lia |].
pose proof (dec_depth_pos low). lia.
Qed.

Definition isave_ok (d : dec_state bptr) : Prop :=
match d with
| DecNB st => match nb_innov_save st with None => True | Some k => 160 <= k /\ 4 * (k + 160) <= 8000 end
| DecSB s _ => match sbd_innov_save s with None => True | Some k => k = 2 * sbd_frame_size s end
end.

Definition blocks_al8 (LBD : list block) : Prop := forall x, In x LBD -> blk_addr x mod 8 = 0.

Section DecCPS.
Variable RT : rt_sig.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).

Definition dec_W (A OUT STEREO : Z) (LBD : list block) : list (Z * Z) :=
(A, A + BITS_SIZEOF) :: (OUT, OUT + 8000) :: (STEREO, STEREO + 24) :: blocks_ivs LBD ++ IO_FP.

Definition dec_cps_at (ENTRY : Z) (d : dec_state bptr) : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (OUT STEREO S A D : Z) (LBD : list block) (b : bits_st bptr) (lo fh PD ND : Z) (kh : nat)
(ows : list word) (stb : list byte) (q q' : pst) (ret : Z) (d' : dec_state bptr) (b' : bits_st bptr),
prun (speex_decode (St := pst) p_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M d b 0) q = Some ((ret, d', b'), q') ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 OUT -> tp = Z_to_bv 64 0x630458 ->

DREP OUT STEREO m S d LBD -> (dec_depth d <= 3)%nat -> isave_ok d -> dec_nestedR d -> List.NoDup (map blk_id LBD) ->
blocks_al8 LBD ->
(forall x, In x LBD -> In (blk_addr x, blk_size x) (rt_live RT Σ)) ->

bits_rep asegs m A D b -> bits_ok b ->
In (PD, ND) (rt_live RT Σ) -> PD <= D -> D + sb_buf_size b <= PD + ND -> (forall x, In x LBD -> blk_addr x <> PD) ->

rw_cells asegs m OUT (f32 ows) -> length ows = 2000%nat -> rw_cells asegs m STEREO [CB 24 stb] ->
In (fh, kh) (rt_frames RT Σ) ->
in_frame_obj RT Σ m fh kh A BITS_SIZEOF -> in_frame_obj RT Σ m fh kh OUT 8000 -> in_frame_obj RT Σ m fh kh STEREO 24 ->
hidp (A + BITS_SIZEOF <= OUT \/ OUT + 8000 <= A) -> hidp (A + BITS_SIZEOF <= STEREO \/ STEREO + 24 <= A) -> hidp (OUT + 8000 <= STEREO \/ STEREO + 24 <= OUT) ->

fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> ERR_rep m -> io_ssp m ->

(length (rt_frames RT Σ) + dec_frames d <= FRAMES_MAX)%nat -> dec_credit d <= rt_credit RT Σ ->
pois_above (rt_pois RT Σ) (bv_unsigned sp) ->
ART RT Σ m -> mem_inv asegs m -> X1cn.frm0 fc ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + dec_stack d <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 ->
exists bs, p_err q' = p_err q ++ bs /\
cpsE asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc ENTRY m)))
(Spec.X1nu.evw 2 bs)
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' (PMfd F0 fs0) (fun ms => exists m' (ows' : list word) (stb' : list byte),
ret_stL (fun _ fc' => X1cn.frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 ret) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (dec_W A OUT STEREO LBD) m m'
/\ DREP OUT STEREO m' S d' LBD /\ (ret = 0 -> EXCREADY m' S d')
/\ bits_rep asegs m' A D b' /\ bits_ok b'
/\ rw_cells asegs m' OUT (f32 ows') /\ length ows' = 2000%nat /\ rw_cells asegs m' STEREO [CB 24 stb']
/\ acc asegs m' A BITS_SIZEOF /\ acc asegs m' OUT 8000 /\ acc asegs m' STEREO 24
/\ ERR_rep m' /\ (forall so, OUT_rep so m -> OUT_rep so m')) c
/\ -2 <= ret <= 0 /\ dec_depth d' = dec_depth d /\ dec_mode d' = dec_mode d /\ dec_nestedR d'
/\ sb_owner b' = sb_owner b /\ sb_chars b' = sb_chars b /\ sb_buf_size b' = sb_buf_size b
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ - dec_credit d <= rt_credit RT Σ' <= rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).
End DecCPS.
