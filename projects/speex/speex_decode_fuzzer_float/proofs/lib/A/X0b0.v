(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05s X05u
X081 X05l X05m X09f X06d X069 X082 X08y X0b1.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0wl X0wn X0ys X0x2 X0yt X0zq X11l.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11l.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition SB_LOOP_STACK : Z := 608 + 4096 + INNOV_STACK.

Record sbinv := SBI {
x_usp : Z;
x_lo : Z;
x_gp : word;
x_S : Z; x_OUT : Z; x_A : Z; x_D : Z;
x_s : sbd_state bptr;
x_a : sb_addrs;
x_bsz : Z;
x_f : Z; x_sf : Z;
x_fh : Z; x_kh : nat;
x_PD : Z; x_ND : Z;
x_live : list (Z * Z); x_frames : list (Z * nat); x_sp0 : Z; x_cr : Z; x_pois : list (Z * Z)
}.

Definition sb_addrs_al (a : sb_addrs) : Prop :=
a_g0 a mod 8 = 0 /\ a_g1 a mod 8 = 0 /\ a_exc a mod 8 = 0 /\ a_oq a mod 8 = 0 /\ a_iq a mod 8 = 0 /\ a_msp a mod 8 = 0 /\ a_pg a mod 8 = 0 /\ a_er a mod 8 = 0.
Lemma sb_addrs_al_of_blocks : forall (s : sbd_state bptr) S a, (forall b, In b (sb_blocks s S a) -> blk_addr b mod 8 = 0) -> sb_addrs_al a.
Proof.
intros s S a H. unfold sb_addrs_al.
repeat split; match goal with |- ?x mod 8 = 0 => first
[ exact (H (sbd_g0_mem s, x, 256) ltac:(cbn [sb_blocks In]; tauto)) | exact (H (sbd_g1_mem s, x, 256) ltac:(cbn [sb_blocks In]; tauto))
| exact (H (sbd_excBuf s, x, 4 * sbd_subframeSize s) ltac:(cbn [sb_blocks In]; tauto)) | exact (H (sbd_old_qlsp s, x, 32) ltac:(cbn [sb_blocks In]; tauto))
| exact (H (sbd_interp_qlpc s, x, 32) ltac:(cbn [sb_blocks In]; tauto)) | exact (H (sbd_mem_sp s, x, 64) ltac:(cbn [sb_blocks In]; tauto))
| exact (H (sbd_pi_gain s, x, 16) ltac:(cbn [sb_blocks In]; tauto)) | exact (H (sbd_exc_rms s, x, 16) ltac:(cbn [sb_blocks In]; tauto)) ] end.
Qed.

Section Ctx.
Variable RT : rt_sig.
Variable X : sbinv.
Local Notation usp := (x_usp X). Local Notation lo := (x_lo X). Local Notation S := (x_S X). Local Notation OUT := (x_OUT X).
Local Notation A := (x_A X). Local Notation D := (x_D X). Local Notation s := (x_s X). Local Notation a := (x_a X).
Local Notation f := (x_f X). Local Notation sf := (x_sf X).
Local Notation mo := (sbd_mode (x_s X)).
Local Notation FS := (sbd_subframeSize (x_s X)).

Definition sb_pois : list (Z * Z) := [(usp + -1184, 32); (usp + -1088, 32); (usp + -992, 32); (usp + -896, 16); (usp + -800, 16)].

Record sb_ihyps : Prop := SBIH {
ih_usp32 : usp mod 32 = 0;
ih_top : usp + 16 <= USTACK_TOP;
ih_low : x_sp0 X - STACK_WIN <= lo;
ih_room : lo + RT_STACK + SB_LOOP_STACK <= usp + -1216;
ih_Spos : 0 < S;
ih_Sal : S mod 8 = 0;
ih_inv : sb_inv s;
ih_isave : match sbd_innov_save s with None => True | Some k => k = 2 * sbd_frame_size s end;
ih_blocks : forall b, In b (sb_blocks s S a) -> In (blk_addr b, blk_size b) (x_live X);
ih_nodup : List.NoDup (map blk_id (sb_blocks s S a));
ih_fh : In (x_fh X, x_kh X) (x_frames X);
ih_A : x_fh X <= A /\ A + BITS_SIZEOF <= x_fh X + fs_size (x_kh X) - 8 /\ A mod 4 = 0;
ih_OUT : x_fh X <= OUT /\ OUT + 8000 <= x_fh X + fs_size (x_kh X) - 8 /\ OUT mod 4 = 0;
ih_AOUT : hidp (A + BITS_SIZEOF <= OUT \/ OUT + 8000 <= A);
ih_D : In (x_PD X, x_ND X) (x_live X) /\ x_PD X <= D /\ D + x_bsz X <= x_PD X + x_ND X;
ih_Dblk : forall b, In b (sb_blocks s S a) -> blk_addr b <> x_PD X;
ih_pois : pois_above (x_pois X) usp;
ih_sf : sf = Z.shiftr f 3 + SHB;
ih_al : sb_addrs_al a }.

Definition sb_sigma (Σ1 : rts RT) : Prop :=
rt_live RT Σ1 = x_live X /\ rt_frames RT Σ1 = (f, 0%nat) :: x_frames X /\ rt_sp0 RT Σ1 = x_sp0 X
/\ rt_credit RT Σ1 = x_cr X /\ rt_pois RT Σ1 = sb_pois ++ x_pois X.

Definition sb_WL : list (Z * Z) :=
[(usp + -736, usp + -160); (usp + -1088, usp + -1056); (usp + -1184, usp + -1152); (S + 132, S + 136);
(a_exc a, a_exc a + 4 * FS); (a_iq a, a_iq a + 32); (a_msp a, a_msp a + 64); (a_pg a, a_pg a + 16); (a_er a, a_er a + 16);
(OUT, OUT + 8000); (A, A + BITS_SIZEOF)].

Definition sb_loopmem (mR : mem) (Σ1 : rts RT) (m : mem) (b : bits_st bptr) (v : sb_vslots) : Prop :=
exists (le seed : word) (pad1 pad2 : list byte) (lpi ler lq liq lak : list word) (vexc voq viq vmsp vpg ver : list word) (ows : list word),
ART RT Σ1 m /\ mem_inv bsegs m /\ stk bsegs m lo (usp + -1216)
/\ rt_pres_fp (x_live X) ((f, 0%nat) :: x_frames X) (usp + -1216) sb_WL mR m /\ wmono bsegs mR m

/\ rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf (sbmode_struct mo) (sbd_frame_size s) v)

/\ rw_cells bsegs m (usp + -800) (f32 lpi) /\ length lpi = 4%nat
/\ rw_cells bsegs m (usp + -896) (f32 ler) /\ length ler = 4%nat
/\ rw_cells bsegs m (usp + -992) (f32 lq) /\ length lq = 8%nat
/\ rw_cells bsegs m (usp + -1088) (f32 liq) /\ length liq = 8%nat
/\ rw_cells bsegs m (usp + -1184) (f32 lak) /\ length lak = 8%nat

/\ sb_pieces m S s a OUT le seed pad1 pad2 /\ length pad1 = 4%nat /\ length pad2 = 4%nat
/\ rw_cells bsegs m (a_exc a) (f32 vexc) /\ Z.of_nat (length vexc) = FS
/\ rw_cells bsegs m (a_oq a) (f32 voq) /\ length voq = 8%nat
/\ rw_cells bsegs m (a_iq a) (f32 viq) /\ length viq = 8%nat
/\ rw_cells bsegs m (a_msp a) (f32 vmsp) /\ length vmsp = 16%nat
/\ rw_cells bsegs m (a_pg a) (f32 vpg) /\ length vpg = 4%nat
/\ rw_cells bsegs m (a_er a) (f32 ver) /\ length ver = 4%nat

/\ rw_cells bsegs m OUT (f32 ows) /\ length ows = 2000%nat
/\ bits_rep bsegs m A D b /\ bits_ok b /\ sb_buf_size b = x_bsz X
/\ acc bsegs m A BITS_SIZEOF /\ acc bsegs m OUT 8000.

Variable PMc : Model -> Prop.

Definition at_LA (mR : mem) (sub : Z) (b : bits_st bptr) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : sb_rjunk) (v : sb_vslots),
ASTA RT Σ1 PMc (eq (MS (R_LA usp S OUT (sbmode_struct mo) sub (x_gp X) (Z_to_bv 64 0x638c98) k) Fx (Z_to_bv 64 SB_LA_PC) fc None m (seg_rom bsegs))) c
/\ X1cn.frm0 fc /\ sb_sigma Σ1 /\ sb_loopmem mR Σ1 m b v /\ v_480 v = Z_to_bv 64 sub.

Definition at_TA (mR : mem) (sm : submode) (b : bits_st bptr) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : sb_rjunk) (v : sb_vslots),
ASTA RT Σ1 PMc (eq (MS (R_TA usp S OUT (x_gp X) (Z_to_bv 64 0x638c98) k) Fx (Z_to_bv 64 SB_TA_PC) fc None m (seg_rom bsegs))) c
/\ X1cn.frm0 fc /\ sb_sigma Σ1 /\ sb_loopmem mR Σ1 m b v /\ v_544 v = Z_to_bv 64 (sb_top_stale usp mo sm).
End Ctx.

Definition sb_subframe_cps (RT : rt_sig) : Prop :=
forall (X : sbinv) (PMc : Model -> Prop) (mR : mem) (sub : Z) (b : bits_st bptr) (sm : submode),
fdfs_only PMc -> mat_stable PMc -> sb_ihyps X -> 0 <= sub < 4 ->
submode_at (sbm_submodes (sbd_mode (x_s X))) (sbd_submodeID (x_s X)) = Some sm ->
cps bsegs (at_LA RT X PMc mR sub b)
(fun c => (sub < 3 /\ at_LA RT X PMc mR (sub + 1) (sbsub_bits sm b) c) \/ (sub = 3 /\ at_TA RT X PMc mR sm (sbsub_bits sm b) c)).
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition SB_LOOP_STACK : Z := 608 + 4096 + INNOV_STACK.

Record sbinv := SBI {
x_usp : Z;
x_lo : Z;
x_gp : word;
x_S : Z; x_OUT : Z; x_A : Z; x_D : Z;
x_s : sbd_state bptr;
x_a : sb_addrs;
x_bsz : Z;
x_f : Z; x_sf : Z;
x_fh : Z; x_kh : nat;
x_PD : Z; x_ND : Z;
x_live : list (Z * Z); x_frames : list (Z * nat); x_sp0 : Z; x_cr : Z; x_pois : list (Z * Z)
}.

Definition sb_addrs_al (a : sb_addrs) : Prop :=
a_g0 a mod 8 = 0 /\ a_g1 a mod 8 = 0 /\ a_exc a mod 8 = 0 /\ a_oq a mod 8 = 0 /\ a_iq a mod 8 = 0 /\ a_msp a mod 8 = 0 /\ a_pg a mod 8 = 0 /\ a_er a mod 8 = 0.
Lemma sb_addrs_al_of_blocks : forall (s : sbd_state bptr) S a, (forall b, In b (sb_blocks s S a) -> blk_addr b mod 8 = 0) -> sb_addrs_al a.
Proof.
intros s S a H. unfold sb_addrs_al.
repeat split; match goal with |- ?x mod 8 = 0 => first
[ exact (H (sbd_g0_mem s, x, 256) ltac:(cbn [sb_blocks In]; tauto)) | exact (H (sbd_g1_mem s, x, 256) ltac:(cbn [sb_blocks In]; tauto))
| exact (H (sbd_excBuf s, x, 4 * sbd_subframeSize s) ltac:(cbn [sb_blocks In]; tauto)) | exact (H (sbd_old_qlsp s, x, 32) ltac:(cbn [sb_blocks In]; tauto))
| exact (H (sbd_interp_qlpc s, x, 32) ltac:(cbn [sb_blocks In]; tauto)) | exact (H (sbd_mem_sp s, x, 64) ltac:(cbn [sb_blocks In]; tauto))
| exact (H (sbd_pi_gain s, x, 16) ltac:(cbn [sb_blocks In]; tauto)) | exact (H (sbd_exc_rms s, x, 16) ltac:(cbn [sb_blocks In]; tauto)) ] end.
Qed.

Section Ctx.
Variable RT : rt_sig.
Variable X : sbinv.
Local Notation usp := (x_usp X). Local Notation lo := (x_lo X). Local Notation S := (x_S X). Local Notation OUT := (x_OUT X).
Local Notation A := (x_A X). Local Notation D := (x_D X). Local Notation s := (x_s X). Local Notation a := (x_a X).
Local Notation f := (x_f X). Local Notation sf := (x_sf X).
Local Notation mo := (sbd_mode (x_s X)).
Local Notation FS := (sbd_subframeSize (x_s X)).

Definition sb_pois : list (Z * Z) := [(usp + -1056, 32); (usp + -960, 32); (usp + -864, 32); (usp + -768, 16); (usp + -672, 16)].

Record sb_ihyps : Prop := SBIH {
ih_usp32 : usp mod 32 = 0;
ih_top : usp + 16 <= USTACK_TOP;
ih_low : x_sp0 X - STACK_WIN <= lo;
ih_room : lo + RT_STACK + SB_LOOP_STACK <= usp + -1088;
ih_Spos : 0 < S;
ih_Sal : S mod 8 = 0;
ih_inv : sb_inv s;
ih_isave : match sbd_innov_save s with None => True | Some k => k = 2 * sbd_frame_size s end;
ih_blocks : forall b, In b (sb_blocks s S a) -> In (blk_addr b, blk_size b) (x_live X);
ih_nodup : List.NoDup (map blk_id (sb_blocks s S a));
ih_fh : In (x_fh X, x_kh X) (x_frames X);
ih_A : x_fh X <= A /\ A + BITS_SIZEOF <= x_fh X + fs_size (x_kh X) - 8 /\ A mod 4 = 0;
ih_OUT : x_fh X <= OUT /\ OUT + 8000 <= x_fh X + fs_size (x_kh X) - 8 /\ OUT mod 4 = 0;
ih_AOUT : hidp (A + BITS_SIZEOF <= OUT \/ OUT + 8000 <= A);
ih_D : In (x_PD X, x_ND X) (x_live X) /\ x_PD X <= D /\ D + x_bsz X <= x_PD X + x_ND X;
ih_Dblk : forall b, In b (sb_blocks s S a) -> blk_addr b <> x_PD X;
ih_pois : pois_above (x_pois X) usp;
ih_sf : sf = Z.shiftr f 3 + SHB;
ih_al : sb_addrs_al a }.

Definition sb_sigma (Σ1 : rts RT) : Prop :=
rt_live RT Σ1 = x_live X /\ rt_frames RT Σ1 = (f, 0%nat) :: x_frames X /\ rt_sp0 RT Σ1 = x_sp0 X
/\ rt_credit RT Σ1 = x_cr X /\ rt_pois RT Σ1 = sb_pois ++ x_pois X.

Definition sb_WL : list (Z * Z) :=
[(usp + -608, usp + -160); (usp + -960, usp + -928); (usp + -1056, usp + -1024); (S + 132, S + 136);
(a_exc a, a_exc a + 4 * FS); (a_iq a, a_iq a + 32); (a_msp a, a_msp a + 64); (a_pg a, a_pg a + 16); (a_er a, a_er a + 16);
(OUT, OUT + 8000); (A, A + BITS_SIZEOF)].

Definition sb_loopmem (mR : mem) (Σ1 : rts RT) (m : mem) (b : bits_st bptr) (v : sb_vslots) : Prop :=
exists (le seed : word) (pad1 pad2 : list byte) (lpi ler lq liq lak : list word) (vexc voq viq vmsp vpg ver : list word) (ows : list word),
ART RT Σ1 m /\ mem_inv asegs m /\ stk asegs m lo (usp + -1088)
/\ rt_pres_fp (x_live X) ((f, 0%nat) :: x_frames X) (usp + -1088) sb_WL mR m /\ wmono asegs mR m

/\ rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf (sbmode_struct mo) (sbd_frame_size s) v)

/\ rw_cells asegs m (usp + -672) (f32 lpi) /\ length lpi = 4%nat
/\ rw_cells asegs m (usp + -768) (f32 ler) /\ length ler = 4%nat
/\ rw_cells asegs m (usp + -864) (f32 lq) /\ length lq = 8%nat
/\ rw_cells asegs m (usp + -960) (f32 liq) /\ length liq = 8%nat
/\ rw_cells asegs m (usp + -1056) (f32 lak) /\ length lak = 8%nat

/\ sb_pieces m S s a OUT le seed pad1 pad2 /\ length pad1 = 4%nat /\ length pad2 = 4%nat
/\ rw_cells asegs m (a_exc a) (f32 vexc) /\ Z.of_nat (length vexc) = FS
/\ rw_cells asegs m (a_oq a) (f32 voq) /\ length voq = 8%nat
/\ rw_cells asegs m (a_iq a) (f32 viq) /\ length viq = 8%nat
/\ rw_cells asegs m (a_msp a) (f32 vmsp) /\ length vmsp = 16%nat
/\ rw_cells asegs m (a_pg a) (f32 vpg) /\ length vpg = 4%nat
/\ rw_cells asegs m (a_er a) (f32 ver) /\ length ver = 4%nat

/\ rw_cells asegs m OUT (f32 ows) /\ length ows = 2000%nat
/\ bits_rep asegs m A D b /\ bits_ok b /\ sb_buf_size b = x_bsz X
/\ acc asegs m A BITS_SIZEOF /\ acc asegs m OUT 8000.

Variable PMc : Model -> Prop.

Definition at_LA (mR : mem) (sub : Z) (b : bits_st bptr) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : sb_rjunk) (v : sb_vslots),
ASTA RT Σ1 PMc (eq (MS (R_LA usp S OUT (sbmode_struct mo) sub (x_gp X) (Z_to_bv 64 0x630458) k) Fx (Z_to_bv 64 SB_LA_PC) fc None m (seg_rom asegs))) c
/\ X1cn.frm0 fc /\ sb_sigma Σ1 /\ sb_loopmem mR Σ1 m b v /\ v_296 v = Z_to_bv 64 sub.

Definition at_TA (mR : mem) (sm : submode) (b : bits_st bptr) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (k : sb_rjunk) (v : sb_vslots),
ASTA RT Σ1 PMc (eq (MS (R_TA usp S OUT (x_gp X) (Z_to_bv 64 0x630458) k) Fx (Z_to_bv 64 SB_TA_PC) fc None m (seg_rom asegs))) c
/\ X1cn.frm0 fc /\ sb_sigma Σ1 /\ sb_loopmem mR Σ1 m b v /\ v_416 v = Z_to_bv 64 (sb_top_stale usp mo sm).
End Ctx.

Definition sb_subframe_cps (RT : rt_sig) : Prop :=
forall (X : sbinv) (PMc : Model -> Prop) (mR : mem) (sub : Z) (b : bits_st bptr) (sm : submode),
fdfs_only PMc -> mat_stable PMc -> sb_ihyps X -> 0 <= sub < 4 ->
submode_at (sbm_submodes (sbd_mode (x_s X))) (sbd_submodeID (x_s X)) = Some sm ->
cps asegs (at_LA RT X PMc mR sub b)
(fun c => (sub < 3 /\ at_LA RT X PMc mR (sub + 1) (sbsub_bits sm b) c) \/ (sub = 3 /\ at_TA RT X PMc mR sm (sbsub_bits sm b) c)).
