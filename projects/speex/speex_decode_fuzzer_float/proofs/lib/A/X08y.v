(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05s X05l X09e X082.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0wl X0yt.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition A_pitch_unquant_3tap : Z := 0xac9c4.
Definition A_forced_pitch_unquant : Z := 0xad5dc.
Definition A_split_cb_shape_sign_unquant : Z := 0xb22a8.
Definition A_noise_codebook_unquant : Z := 0xb29a8.
Definition ltp_entryA (k : ltp_kind) : Z := match k with LtpForcedPitchUnquant => A_forced_pitch_unquant | LtpPitchUnquant3tap _ => A_pitch_unquant_3tap end.
Definition innov_entryA (k : innov_kind) : Z :=
match k with InnovNoiseCodebookUnquant => A_noise_codebook_unquant | InnovSplitCbShapeSignUnquant _ => A_split_cb_shape_sign_unquant end.

Definition LTP_STACK : Z := 192.
Definition INNOV_STACK : Z := 4608.

Definition ltp_par_cellsA (G gbits pbits : Z) : list cell := [C8 (Z_to_bv 64 G); C4 (Z_to_bv 64 gbits); C4 (Z_to_bv 64 pbits)].

Definition gain_cdbk_addrA (g : gain_cdbk_id) : Z := match g with GainCdbkNb => 0x25f40 | GainCdbkLbr => 0x256e0 end.

Definition shape_cb_addrA (t : shape_cb_id) : Z :=
match t with
| Exc_5_256_table => 0x26380 | Exc_5_64_table => 0x261e0 | Exc_8_128_table => 0x25a20 | Exc_10_32_table => 0x25880
| Exc_10_16_table => 0x257a0 | Exc_20_32_table => 0x269e0 | Hexc_table => 0x274c0 | Hexc_10_32_table => 0x27320
end.
Definition scb_par_cellsA (p : split_cb_params) : list cell :=
[C4 (Z_to_bv 64 (scb_subvect_size p)); C4 (Z_to_bv 64 (scb_nb_subvect p)); C8 (Z_to_bv 64 (shape_cb_addrA (scb_shape_cb p)));
C4 (Z_to_bv 64 (scb_shape_bits p)); C4 (Z_to_bv 64 (scb_have_sign p))].

Definition scb_params_ok (p : split_cb_params) : Prop :=
1 <= scb_subvect_size p <= 20 /\ In (scb_nb_subvect p) [2; 4; 5; 8] /\ scb_subvect_size p * scb_nb_subvect p = 40
/\ 1 <= scb_shape_bits p <= 8 /\ 0 <= scb_have_sign p <= 1
/\ shape_cb_size (scb_shape_cb p) = 2 ^ scb_shape_bits p * scb_subvect_size p.
Lemma scb_params_ok_all : Forall scb_params_ok
[split_cb_nb_vlbr; split_cb_nb_ulbr; split_cb_nb_lbr; split_cb_nb; split_cb_nb_med; split_cb_sb; split_cb_high; split_cb_high_lbr].
Proof.
repeat (apply Forall_cons; [unfold scb_params_ok; cbn -[Z.pow Z.mul]; repeat (split; [first [lia | reflexivity]|]); reflexivity|]). apply Forall_nil.
Qed.
Definition shape_tab_bytes (t : shape_cb_id) : list byte :=
match image_bytes bsegs (shape_cb_addrA t) (Z.to_nat (shape_cb_size t)) with Some bs => bs | None => [] end.
Lemma shape_tab_len : forall t, Z.of_nat (length (shape_tab_bytes t)) = shape_cb_size t.
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma shape_tab_ro : forall t (m : mem), mem_inv bsegs m -> X1cg.u8ro bsegs m (shape_cb_addrA t) (shape_tab_bytes t).
Proof.
intros t m MI. assert (H : ro_cells bsegs m (shape_cb_addrA t) [CB (length (shape_tab_bytes t)) (shape_tab_bytes t)]).
{ apply (ro_cells_image bsegs m); [exact MI | destruct t; vm_compute; reflexivity | destruct t; cbn; lia | pose proof (shape_tab_len t); destruct t; cbn in *; lia]. }
destruct H as [_ H]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.
Lemma shape_tab_lit : forall t, In (shape_cb_addrA t, shape_cb_size t) ACC_LITS.
Proof. intros []; cbn [shape_cb_addrA shape_cb_size In ACC_LITS]; repeat (first [left; reflexivity | right]). Qed.

Definition ltp_params_ok (p : ltp_params) : Prop :=
0 <= ltp_pitch_bits p <= 7 /\ 0 <= ltp_gain_bits p <= 7 /\ gain_cdbk_size (ltp_gain_cdbk p) = 4 * 2 ^ ltp_gain_bits p.
Lemma ltp_params_ok_all : Forall ltp_params_ok [ltp_params_nb; ltp_params_vlbr; ltp_params_lbr; ltp_params_med].
Proof. repeat constructor; cbn; lia. Qed.
Definition gain_tab_bytes (g : gain_cdbk_id) : list byte :=
match image_bytes bsegs (gain_cdbk_addrA g) (Z.to_nat (gain_cdbk_size g)) with Some bs => bs | None => [] end.
Lemma gain_tab_len : forall g, Z.of_nat (length (gain_tab_bytes g)) = gain_cdbk_size g.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma gain_tab_ro : forall g (m : mem), mem_inv bsegs m -> X1cg.u8ro bsegs m (gain_cdbk_addrA g) (gain_tab_bytes g).
Proof.
intros g m MI. assert (H : ro_cells bsegs m (gain_cdbk_addrA g) [CB (length (gain_tab_bytes g)) (gain_tab_bytes g)]).
{ apply (ro_cells_image bsegs m); [exact MI | destruct g; vm_compute; reflexivity | destruct g; cbn; lia | pose proof (gain_tab_len g); destruct g; cbn in *; lia]. }
destruct H as [_ H]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.
Lemma gain_tab_lit : forall g, In (gain_cdbk_addrA g, gain_cdbk_size g) ACC_LITS.
Proof. intros [|]; cbn [gain_cdbk_addrA gain_cdbk_size In ACC_LITS]; repeat (first [left; reflexivity | right]). Qed.

Section Pure.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

Definition ltp3_pitch (p : ltp_params) (start : Z) b : Z := uv b (ltp_pitch_bits p) + start.
Definition ltp3_bits (p : ltp_params) b : bits_st ptr := ub (ub b (ltp_pitch_bits p)) (ltp_gain_bits p).
Definition ltp_bits (k : ltp_kind) b : bits_st ptr := match k with LtpForcedPitchUnquant => b | LtpPitchUnquant3tap p => ltp3_bits p b end.
Definition ltp_pitch (k : ltp_kind) (start : Z) b : Z := match k with LtpForcedPitchUnquant => start | LtpPitchUnquant3tap p => ltp3_pitch p start b end.
Definition ltp_pitch_span (k : ltp_kind) : Z := match k with LtpForcedPitchUnquant => 0 | LtpPitchUnquant3tap p => 2 ^ ltp_pitch_bits p - 1 end.

Fixpoint scb_bits (n : nat) (have_sign shape_bits : Z) b : bits_st ptr :=
match n with
| O => b
| S n' => let b1 := if negb (have_sign =? 0) then ub b 1 else b in scb_bits n' have_sign shape_bits (ub b1 shape_bits)
end.
Definition innov_bits (k : innov_kind) b : bits_st ptr :=
match k with
| InnovNoiseCodebookUnquant => b
| InnovSplitCbShapeSignUnquant p => scb_bits (Z.to_nat (scb_nb_subvect p)) (scb_have_sign p) (scb_shape_bits p) b
end.
End Pure.

Lemma acc_agree : forall (m m' : mem) o n, acc bsegs m o n ->
agree_on (fun x => exists i, 0 <= i < n /\ x = shad (o + i)) m m' -> acc bsegs m' o n.
Proof.
intros m m' o n H HA i Hi. destruct (H i Hi) as (b & Hb & Hok). exists b. split; [| exact Hok].
apply (bytes_at_agree bsegs m m' _ _ Hb). eapply agree_sub; [exact HA|]. intros x Hx. cbn [length] in Hx. exists i. split; [exact Hi| lia].
Qed.

Lemma frame_shadow_client : forall live frames sp f k o n i, In (f, k) frames -> f mod 8 = 0 -> fs_size k mod 8 = 0 -> 0 <= f ->
f <= o -> o + n <= f + fs_size k -> 0 <= i < n -> aclient live frames sp (shad (o + i)).
Proof.
intros live frames sp f k o n i Hin F8 S8 F0 Ho Hn Hi. right; right; right; right. exists f, k. split; [exact Hin|].
unfold shad. split.
- apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
- apply Z.add_lt_mono_r. apply Z.div_lt_upper_bound; [lia|].
assert (E : f + fs_size k = 8 * ((f + fs_size k) / 8)) by (pose proof (Z.div_mod (f + fs_size k) 8 ltac:(lia)) as X; rewrite Zplus_mod, F8, S8 in X; cbn in X; lia).
lia.
Qed.

Lemma acc_pres_frame : forall live frames sp (m m' : mem) f k o n, rt_pres live frames sp m m' ->
In (f, k) frames -> f mod 8 = 0 -> fs_size k mod 8 = 0 -> 0 <= f -> f <= o -> o + n <= f + fs_size k ->
acc bsegs m o n -> acc bsegs m' o n.
Proof.
intros live frames sp m m' f k o n PRES Hin F8 S8 F0 Ho Hn H. apply (acc_agree m m' o n H).
apply (agree_of_pres live frames sp m m' _ PRES). intros x (i & Hi & ->). exact (frame_shadow_client live frames sp f k o n i Hin F8 S8 F0 Ho Hn Hi).
Qed.

Lemma fs_size_mod8 : forall k, fs_size k mod 8 = 0.
Proof.
intros k. unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. replace (64 * 2 ^ Z.of_nat k) with ((8 * 2 ^ Z.of_nat k) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma fs_size_ge64 : forall k, 64 <= fs_size k.
Proof. intros k. unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)). lia. Qed.
Lemma mod64_mod8 : forall f, f mod 64 = 0 -> f mod 8 = 0.
Proof. intros f H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->]. replace (q * 64) with ((q * 8) * 8) by lia. apply Z_mod_mult. Qed.

Lemma acc_pres_ex_frame : forall live frames sp d n (m m' : mem) f k o no, rt_pres_ex live frames sp d n m m' ->
In (f, k) frames -> f mod 8 = 0 -> fs_size k mod 8 = 0 -> 0 <= f -> f <= o -> o + no <= f + fs_size k -> o + no <= APP_TOP ->
(d + n <= SH_LO \/ SH_HI <= d) ->
acc bsegs m o no -> acc bsegs m' o no.
Proof.
intros live frames sp d n m m' f k o no PRES Hin F8 S8 F0 Ho Hn HT HD H. apply (acc_agree m m' o no H).
apply (agree_of_pres_ex live frames sp d n m m' _ PRES). intros x (i & Hi & ->).
split; [exact (frame_shadow_client live frames sp f k o no i Hin F8 S8 F0 Ho Hn Hi)|].
unfold shad, SHB, SH_LO, SH_HI, APP_TOP in *. assert (0 <= (o + i) / 8 < 17592186044416) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia.
Qed.

Section Kinds.
Variable RT : rt_sig.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

Definition ltp_args_cells (A : Z) (stk8 : word) (off : Z) : list cell :=
[C8 (Z_to_bv 64 A); C8 stk8; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 off); C8 (Z_to_bv 64 0)].

Definition in_frame_obj (Σ : rts RT) (m : mem) (f : Z) (k : nat) (o n : Z) : Prop :=
f <= o /\ o + n <= f + fs_size k - 8 /\ acc bsegs m o n /\ o mod 4 = 0.

Definition dst_obj (Σ : rts RT) (m : mem) (o n : Z) : Prop :=
(exists f k, In (f, k) (rt_frames RT Σ) /\ in_frame_obj Σ m f k o n) \/ In (o, n) (rt_pois RT Σ).

Definition ltp_unquant_cps (k : ltp_kind) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A D : Z) b (EB e0 e32 pv pg start fin PAR off lo P0 N0 PD ND fq fa : Z) (kq ka : nat)
(eb e32s pgs : list word) (opv stk8 : word),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 (EB + 4 * e0) -> a1 = Z_to_bv 64 e32 -> a2 = Z_to_bv 64 start -> a3 = Z_to_bv 64 fin -> a4 = Z_to_bv 64 PAR ->
a5 = Z_to_bv 64 40 -> a6 = Z_to_bv 64 pv -> a7 = Z_to_bv 64 pg -> tp = Z_to_bv 64 0x638c98 ->

bits_rep bsegs m A D b -> bits_ok b ->
17 <= start -> start + ltp_pitch_span k <= 144 -> start <= fin <= 144 -> 0 <= off <= 120 ->
match k with LtpPitchUnquant3tap p => ro_cells bsegs m PAR (ltp_par_cellsA (gain_cdbk_addrA (ltp_gain_cdbk p)) (ltp_gain_bits p) (ltp_pitch_bits p))
/\ PAR mod 8 = 0 /\ 0x10000 <= PAR /\ PAR + 16 <= IMG_TOP /\ In (PAR, 16) ACC_LITS
| LtpForcedPitchUnquant => True end ->

rw_cells bsegs m EB (f32 eb) -> 290 <= e0 -> e0 + 40 <= Z.of_nat (length eb) -> EB mod 4 = 0 ->
In (P0, N0) (rt_live RT Σ) -> P0 <= EB -> EB + 4 * Z.of_nat (length eb) <= P0 + N0 ->

rw_cells bsegs m e32 (f32 e32s) -> length e32s = 40%nat -> rw_cells bsegs m pv [C4 opv] -> rw_cells bsegs m pg (f32 pgs) -> length pgs = 3%nat ->
In (fq, kq) (rt_frames RT Σ) -> in_frame_obj Σ m fq kq e32 160 -> in_frame_obj Σ m fq kq pv 4 -> in_frame_obj Σ m fq kq pg 12 ->
hidp (e32 + 160 <= pv \/ pv + 4 <= e32) -> hidp (e32 + 160 <= pg \/ pg + 12 <= e32) -> hidp (pv + 4 <= pg \/ pg + 12 <= pv) ->

In (fa, ka) (rt_frames RT Σ) -> in_frame_obj Σ m fa ka A BITS_SIZEOF -> In (PD, ND) (rt_live RT Σ) -> PD <= D -> D + sb_buf_size b <= PD + ND ->
hidp (PD + ND <= P0 \/ P0 + N0 <= PD) ->
hidp (A + BITS_SIZEOF <= e32 \/ e32 + 160 <= A) -> hidp (A + BITS_SIZEOF <= pv \/ pv + 4 <= A) -> hidp (A + BITS_SIZEOF <= pg \/ pg + 12 <= A) ->

rw_cells bsegs m (bv_unsigned sp) (ltp_args_cells A stk8 off) ->
ART RT Σ m -> mem_inv bsegs m -> X1cn.frm0 fc ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + LTP_STACK <= bv_unsigned sp ->
bv_unsigned sp + 40 + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc (ltp_entryA k) m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists v m' (eb' e32' pg' : list word),
ret_stL (fun _ fc' => X1cn.frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp)
[(EB + 4 * e0, EB + 4 * e0 + 160); (e32, e32 + 160); (pv, pv + 4); (pg, pg + 12); (A, A + BITS_SIZEOF)] m m'
/\ rw_cells bsegs m' EB (f32 eb') /\ length eb' = length eb
/\ rw_cells bsegs m' e32 (f32 e32') /\ length e32' = 40%nat
/\ rw_cells bsegs m' pv [C4 (Z_to_bv 64 (ltp_pitch k start b))]
/\ rw_cells bsegs m' pg (f32 pg') /\ length pg' = 3%nat
/\ bits_rep bsegs m' A D (ltp_bits k b) /\ bits_ok (ltp_bits k b)
/\ rw_cells bsegs m' (bv_unsigned sp) (ltp_args_cells A stk8 off)
/\ acc bsegs m' e32 160 /\ acc bsegs m' pv 4 /\ acc bsegs m' pg 12 /\ acc bsegs m' A BITS_SIZEOF) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Definition innov_unquant_cps (k : innov_kind) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A D : Z) b (inn seedp PAR lo P0 N0 PD ND fa : Z) (ka : nat) (is0 : list word) (seed0 stk8 : word),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 inn -> a1 = Z_to_bv 64 PAR -> a2 = Z_to_bv 64 40 -> a3 = Z_to_bv 64 A -> a4 = stk8 -> a5 = Z_to_bv 64 seedp -> tp = Z_to_bv 64 0x638c98 ->
bits_rep bsegs m A D b -> bits_ok b ->
match k with InnovSplitCbShapeSignUnquant p => ro_cells bsegs m PAR (scb_par_cellsA p) /\ PAR mod 8 = 0 /\ 0x10000 <= PAR /\ PAR + 24 <= IMG_TOP /\ In (PAR, 24) ACC_LITS
| InnovNoiseCodebookUnquant => True end ->

rw_cells bsegs m inn (f32 is0) -> length is0 = 40%nat -> dst_obj Σ m inn 160 ->

rw_cells bsegs m seedp [C4 seed0] -> In (P0, N0) (rt_live RT Σ) -> P0 <= seedp -> seedp + 4 <= P0 + N0 -> seedp mod 4 = 0 ->

In (fa, ka) (rt_frames RT Σ) -> in_frame_obj Σ m fa ka A BITS_SIZEOF -> In (PD, ND) (rt_live RT Σ) -> PD <= D -> D + sb_buf_size b <= PD + ND ->
hidp (PD + ND <= P0 \/ P0 + N0 <= PD) -> hidp (A + BITS_SIZEOF <= inn \/ inn + 160 <= A) ->
ART RT Σ m -> mem_inv bsegs m -> X1cn.frm0 fc ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + INNOV_STACK <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 -> pois_above (rt_pois RT Σ) (bv_unsigned sp) ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc (innov_entryA k) m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists v m' (is' : list word) (seed' : word),
ret_stL (fun _ fc' => X1cn.frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(inn, inn + 160); (seedp, seedp + 4); (A, A + BITS_SIZEOF)] m m'
/\ rw_cells bsegs m' inn (f32 is') /\ length is' = 40%nat
/\ rw_cells bsegs m' seedp [C4 seed']
/\ bits_rep bsegs m' A D (innov_bits k b) /\ bits_ok (innov_bits k b)
/\ acc bsegs m' inn 160 /\ acc bsegs m' A BITS_SIZEOF) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).
End Kinds.

Section DstFacts.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Lemma dst_obj_facts : forall (Σ : rts RT) (m : mem) o n lo usp,
ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo <= usp -> usp + 16 <= USTACK_TOP -> pois_above (rt_pois RT Σ) usp -> 0 < n ->
dst_obj RT Σ m o n ->
acc bsegs m o n /\ 0 < o /\ o + n <= APP_TOP /\ (o + n <= SH_LO \/ SH_HI <= o) /\ (o + n <= lo \/ usp <= o) /\ IMG_TOP <= o /\ o mod 4 = 0
/\ (forall i, 0 <= i < n -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp (o + i))
/\ rng_class RT Σ o n
/\ (forall p k, In (p, k) (rt_live RT Σ) -> p + k <= o \/ o + n <= p).
Proof using AF.
intros Σ m o n lo usp ART0 LOW LU UT POA N0 [(f & k & INF & (O1 & O2 & O3 & O4)) | INP].
- pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & _ & FI & _ & FS & _).
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (FB & _ & _).
pose proof (fs_size_ge64 k) as FSZ.
split; [exact O3|]. split; [lia|]. split; [unfold APP_TOP, USTACK_TOP in *; lia|]. split; [unfold SH_LO, SH_HI; lia|]. split; [left; lia|].
split; [unfold IMG_TOP, SEGTOP_A in *; lia|]. split; [exact O4|].
split; [intros i Hi; right; right; right; left; exists f, k; split; [exact INF| lia]|].
split; [right; left; exists f, k; split; [exact INF| split; [exact O1| exact O2]]|].
intros p kk INL. destruct (frame_live_apart RT AF Σ m f k p kk ART0 INF INL) as (FLA & _). lia.
- pose proof (af_pois_range RT AF Σ m o n ART0 INP) as (A32 & _ & R1 & R2).
pose proof (POA (o, n) INP) as PA. unfold pz_lo in PA. cbn [fst] in PA.
pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
assert (RR : o + n <= alloca_rr o n) by (unfold alloca_rr; Z.div_mod_to_equations; lia).
split; [exact (af_acc_pois RT AF Σ m o n ART0 INP)|].
unfold STACK_WIN, USTACK_TOP, APP_TOP, SH_LO, SH_HI, IMG_TOP in *.
split; [lia|]. split; [lia|]. split; [right; lia|]. split; [right; lia|]. split; [lia|].
split; [clear - A32; Z.div_mod_to_equations; lia|].
split; [intros i Hi; left; unfold USTACK_TOP; lia|].
split; [right; right; left; unfold STACK_WIN, USTACK_TOP; lia|].
intros p kk INL. destruct (live_below_lo RT AF Σ m p kk lo ART0 INL LOW) as (_ & PL & _). left. lia.
Qed.
End DstFacts.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition A_pitch_unquant_3tap : Z := 0xa7ff4.
Definition A_forced_pitch_unquant : Z := 0xa88d8.
Definition A_split_cb_shape_sign_unquant : Z := 0xac694.
Definition A_noise_codebook_unquant : Z := 0xaccb4.
Definition ltp_entryA (k : ltp_kind) : Z := match k with LtpForcedPitchUnquant => A_forced_pitch_unquant | LtpPitchUnquant3tap _ => A_pitch_unquant_3tap end.
Definition innov_entryA (k : innov_kind) : Z :=
match k with InnovNoiseCodebookUnquant => A_noise_codebook_unquant | InnovSplitCbShapeSignUnquant _ => A_split_cb_shape_sign_unquant end.

Definition LTP_STACK : Z := 160.
Definition INNOV_STACK : Z := 4608.

Definition ltp_par_cellsA (G gbits pbits : Z) : list cell := [C8 (Z_to_bv 64 G); C4 (Z_to_bv 64 gbits); C4 (Z_to_bv 64 pbits)].

Definition gain_cdbk_addrA (g : gain_cdbk_id) : Z := match g with GainCdbkNb => 0x25f40 | GainCdbkLbr => 0x256e0 end.

Definition shape_cb_addrA (t : shape_cb_id) : Z :=
match t with
| Exc_5_256_table => 0x26380 | Exc_5_64_table => 0x261e0 | Exc_8_128_table => 0x25a20 | Exc_10_32_table => 0x25880
| Exc_10_16_table => 0x257a0 | Exc_20_32_table => 0x269e0 | Hexc_table => 0x274c0 | Hexc_10_32_table => 0x27320
end.
Definition scb_par_cellsA (p : split_cb_params) : list cell :=
[C4 (Z_to_bv 64 (scb_subvect_size p)); C4 (Z_to_bv 64 (scb_nb_subvect p)); C8 (Z_to_bv 64 (shape_cb_addrA (scb_shape_cb p)));
C4 (Z_to_bv 64 (scb_shape_bits p)); C4 (Z_to_bv 64 (scb_have_sign p))].

Definition scb_params_ok (p : split_cb_params) : Prop :=
1 <= scb_subvect_size p <= 20 /\ In (scb_nb_subvect p) [2; 4; 5; 8] /\ scb_subvect_size p * scb_nb_subvect p = 40
/\ 1 <= scb_shape_bits p <= 8 /\ 0 <= scb_have_sign p <= 1
/\ shape_cb_size (scb_shape_cb p) = 2 ^ scb_shape_bits p * scb_subvect_size p.
Lemma scb_params_ok_all : Forall scb_params_ok
[split_cb_nb_vlbr; split_cb_nb_ulbr; split_cb_nb_lbr; split_cb_nb; split_cb_nb_med; split_cb_sb; split_cb_high; split_cb_high_lbr].
Proof.
repeat (apply Forall_cons; [unfold scb_params_ok; cbn -[Z.pow Z.mul]; repeat (split; [first [lia | reflexivity]|]); reflexivity|]). apply Forall_nil.
Qed.
Definition shape_tab_bytes (t : shape_cb_id) : list byte :=
match image_bytes asegs (shape_cb_addrA t) (Z.to_nat (shape_cb_size t)) with Some bs => bs | None => [] end.
Lemma shape_tab_len : forall t, Z.of_nat (length (shape_tab_bytes t)) = shape_cb_size t.
Proof. intros []; vm_compute; reflexivity. Qed.
Lemma shape_tab_ro : forall t (m : mem), mem_inv asegs m -> X1cg.u8ro asegs m (shape_cb_addrA t) (shape_tab_bytes t).
Proof.
intros t m MI. assert (H : ro_cells asegs m (shape_cb_addrA t) [CB (length (shape_tab_bytes t)) (shape_tab_bytes t)]).
{ apply (ro_cells_image asegs m); [exact MI | destruct t; vm_compute; reflexivity | destruct t; cbn; lia | pose proof (shape_tab_len t); destruct t; cbn in *; lia]. }
destruct H as [_ H]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.
Lemma shape_tab_lit : forall t, In (shape_cb_addrA t, shape_cb_size t) ACC_LITS.
Proof. intros []; cbn [shape_cb_addrA shape_cb_size In ACC_LITS]; repeat (first [left; reflexivity | right]). Qed.

Definition ltp_params_ok (p : ltp_params) : Prop :=
0 <= ltp_pitch_bits p <= 7 /\ 0 <= ltp_gain_bits p <= 7 /\ gain_cdbk_size (ltp_gain_cdbk p) = 4 * 2 ^ ltp_gain_bits p.
Lemma ltp_params_ok_all : Forall ltp_params_ok [ltp_params_nb; ltp_params_vlbr; ltp_params_lbr; ltp_params_med].
Proof. repeat constructor; cbn; lia. Qed.
Definition gain_tab_bytes (g : gain_cdbk_id) : list byte :=
match image_bytes asegs (gain_cdbk_addrA g) (Z.to_nat (gain_cdbk_size g)) with Some bs => bs | None => [] end.
Lemma gain_tab_len : forall g, Z.of_nat (length (gain_tab_bytes g)) = gain_cdbk_size g.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma gain_tab_ro : forall g (m : mem), mem_inv asegs m -> X1cg.u8ro asegs m (gain_cdbk_addrA g) (gain_tab_bytes g).
Proof.
intros g m MI. assert (H : ro_cells asegs m (gain_cdbk_addrA g) [CB (length (gain_tab_bytes g)) (gain_tab_bytes g)]).
{ apply (ro_cells_image asegs m); [exact MI | destruct g; vm_compute; reflexivity | destruct g; cbn; lia | pose proof (gain_tab_len g); destruct g; cbn in *; lia]. }
destruct H as [_ H]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.
Lemma gain_tab_lit : forall g, In (gain_cdbk_addrA g, gain_cdbk_size g) ACC_LITS.
Proof. intros [|]; cbn [gain_cdbk_addrA gain_cdbk_size In ACC_LITS]; repeat (first [left; reflexivity | right]). Qed.

Section Pure.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

Definition ltp3_pitch (p : ltp_params) (start : Z) b : Z := uv b (ltp_pitch_bits p) + start.
Definition ltp3_bits (p : ltp_params) b : bits_st ptr := ub (ub b (ltp_pitch_bits p)) (ltp_gain_bits p).
Definition ltp_bits (k : ltp_kind) b : bits_st ptr := match k with LtpForcedPitchUnquant => b | LtpPitchUnquant3tap p => ltp3_bits p b end.
Definition ltp_pitch (k : ltp_kind) (start : Z) b : Z := match k with LtpForcedPitchUnquant => start | LtpPitchUnquant3tap p => ltp3_pitch p start b end.
Definition ltp_pitch_span (k : ltp_kind) : Z := match k with LtpForcedPitchUnquant => 0 | LtpPitchUnquant3tap p => 2 ^ ltp_pitch_bits p - 1 end.

Fixpoint scb_bits (n : nat) (have_sign shape_bits : Z) b : bits_st ptr :=
match n with
| O => b
| S n' => let b1 := if negb (have_sign =? 0) then ub b 1 else b in scb_bits n' have_sign shape_bits (ub b1 shape_bits)
end.
Definition innov_bits (k : innov_kind) b : bits_st ptr :=
match k with
| InnovNoiseCodebookUnquant => b
| InnovSplitCbShapeSignUnquant p => scb_bits (Z.to_nat (scb_nb_subvect p)) (scb_have_sign p) (scb_shape_bits p) b
end.
End Pure.

Lemma acc_agree : forall (m m' : mem) o n, acc asegs m o n ->
agree_on (fun x => exists i, 0 <= i < n /\ x = shad (o + i)) m m' -> acc asegs m' o n.
Proof.
intros m m' o n H HA i Hi. destruct (H i Hi) as (b & Hb & Hok). exists b. split; [| exact Hok].
apply (bytes_at_agree asegs m m' _ _ Hb). eapply agree_sub; [exact HA|]. intros x Hx. cbn [length] in Hx. exists i. split; [exact Hi| lia].
Qed.

Lemma frame_shadow_client : forall live frames sp f k o n i, In (f, k) frames -> f mod 8 = 0 -> fs_size k mod 8 = 0 -> 0 <= f ->
f <= o -> o + n <= f + fs_size k -> 0 <= i < n -> aclient live frames sp (shad (o + i)).
Proof.
intros live frames sp f k o n i Hin F8 S8 F0 Ho Hn Hi. right; right; right; right. exists f, k. split; [exact Hin|].
unfold shad. split.
- apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
- apply Z.add_lt_mono_r. apply Z.div_lt_upper_bound; [lia|].
assert (E : f + fs_size k = 8 * ((f + fs_size k) / 8)) by (pose proof (Z.div_mod (f + fs_size k) 8 ltac:(lia)) as X; rewrite Zplus_mod, F8, S8 in X; cbn in X; lia).
lia.
Qed.

Lemma acc_pres_frame : forall live frames sp (m m' : mem) f k o n, rt_pres live frames sp m m' ->
In (f, k) frames -> f mod 8 = 0 -> fs_size k mod 8 = 0 -> 0 <= f -> f <= o -> o + n <= f + fs_size k ->
acc asegs m o n -> acc asegs m' o n.
Proof.
intros live frames sp m m' f k o n PRES Hin F8 S8 F0 Ho Hn H. apply (acc_agree m m' o n H).
apply (agree_of_pres live frames sp m m' _ PRES). intros x (i & Hi & ->). exact (frame_shadow_client live frames sp f k o n i Hin F8 S8 F0 Ho Hn Hi).
Qed.

Lemma fs_size_mod8 : forall k, fs_size k mod 8 = 0.
Proof.
intros k. unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. replace (64 * 2 ^ Z.of_nat k) with ((8 * 2 ^ Z.of_nat k) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma fs_size_ge64 : forall k, 64 <= fs_size k.
Proof. intros k. unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)). lia. Qed.
Lemma mod64_mod8 : forall f, f mod 64 = 0 -> f mod 8 = 0.
Proof. intros f H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->]. replace (q * 64) with ((q * 8) * 8) by lia. apply Z_mod_mult. Qed.

Lemma acc_pres_ex_frame : forall live frames sp d n (m m' : mem) f k o no, rt_pres_ex live frames sp d n m m' ->
In (f, k) frames -> f mod 8 = 0 -> fs_size k mod 8 = 0 -> 0 <= f -> f <= o -> o + no <= f + fs_size k -> o + no <= APP_TOP ->
(d + n <= SH_LO \/ SH_HI <= d) ->
acc asegs m o no -> acc asegs m' o no.
Proof.
intros live frames sp d n m m' f k o no PRES Hin F8 S8 F0 Ho Hn HT HD H. apply (acc_agree m m' o no H).
apply (agree_of_pres_ex live frames sp d n m m' _ PRES). intros x (i & Hi & ->).
split; [exact (frame_shadow_client live frames sp f k o no i Hin F8 S8 F0 Ho Hn Hi)|].
unfold shad, SHB, SH_LO, SH_HI, APP_TOP in *. assert (0 <= (o + i) / 8 < 17592186044416) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia.
Qed.

Section Kinds.
Variable RT : rt_sig.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

Definition ltp_args_cells (A : Z) (stk8 : word) (off : Z) : list cell :=
[C8 (Z_to_bv 64 A); C8 stk8; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 off); C8 (Z_to_bv 64 0)].

Definition in_frame_obj (Σ : rts RT) (m : mem) (f : Z) (k : nat) (o n : Z) : Prop :=
f <= o /\ o + n <= f + fs_size k - 8 /\ acc asegs m o n /\ o mod 4 = 0.

Definition dst_obj (Σ : rts RT) (m : mem) (o n : Z) : Prop :=
(exists f k, In (f, k) (rt_frames RT Σ) /\ in_frame_obj Σ m f k o n) \/ In (o, n) (rt_pois RT Σ).

Definition ltp_unquant_cps (k : ltp_kind) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A D : Z) b (EB e0 e32 pv pg start fin PAR off lo P0 N0 PD ND fq fa : Z) (kq ka : nat)
(eb e32s pgs : list word) (opv stk8 : word),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 (EB + 4 * e0) -> a1 = Z_to_bv 64 e32 -> a2 = Z_to_bv 64 start -> a3 = Z_to_bv 64 fin -> a4 = Z_to_bv 64 PAR ->
a5 = Z_to_bv 64 40 -> a6 = Z_to_bv 64 pv -> a7 = Z_to_bv 64 pg -> tp = Z_to_bv 64 0x630458 ->

bits_rep asegs m A D b -> bits_ok b ->
17 <= start -> start + ltp_pitch_span k <= 144 -> start <= fin <= 144 -> 0 <= off <= 120 ->
match k with LtpPitchUnquant3tap p => ro_cells asegs m PAR (ltp_par_cellsA (gain_cdbk_addrA (ltp_gain_cdbk p)) (ltp_gain_bits p) (ltp_pitch_bits p))
/\ PAR mod 8 = 0 /\ 0x10000 <= PAR /\ PAR + 16 <= IMG_TOP /\ In (PAR, 16) ACC_LITS
| LtpForcedPitchUnquant => True end ->

rw_cells asegs m EB (f32 eb) -> 290 <= e0 -> e0 + 40 <= Z.of_nat (length eb) -> EB mod 4 = 0 ->
In (P0, N0) (rt_live RT Σ) -> P0 <= EB -> EB + 4 * Z.of_nat (length eb) <= P0 + N0 ->

rw_cells asegs m e32 (f32 e32s) -> length e32s = 40%nat -> rw_cells asegs m pv [C4 opv] -> rw_cells asegs m pg (f32 pgs) -> length pgs = 3%nat ->
In (fq, kq) (rt_frames RT Σ) -> in_frame_obj Σ m fq kq e32 160 -> in_frame_obj Σ m fq kq pv 4 -> in_frame_obj Σ m fq kq pg 12 ->
hidp (e32 + 160 <= pv \/ pv + 4 <= e32) -> hidp (e32 + 160 <= pg \/ pg + 12 <= e32) -> hidp (pv + 4 <= pg \/ pg + 12 <= pv) ->

In (fa, ka) (rt_frames RT Σ) -> in_frame_obj Σ m fa ka A BITS_SIZEOF -> In (PD, ND) (rt_live RT Σ) -> PD <= D -> D + sb_buf_size b <= PD + ND ->
hidp (PD + ND <= P0 \/ P0 + N0 <= PD) ->
hidp (A + BITS_SIZEOF <= e32 \/ e32 + 160 <= A) -> hidp (A + BITS_SIZEOF <= pv \/ pv + 4 <= A) -> hidp (A + BITS_SIZEOF <= pg \/ pg + 12 <= A) ->

rw_cells asegs m (bv_unsigned sp) (ltp_args_cells A stk8 off) ->
ART RT Σ m -> mem_inv asegs m -> X1cn.frm0 fc ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + LTP_STACK <= bv_unsigned sp ->
bv_unsigned sp + 40 + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc (ltp_entryA k) m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists v m' (eb' e32' pg' : list word),
ret_stL (fun _ fc' => X1cn.frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp)
[(EB + 4 * e0, EB + 4 * e0 + 160); (e32, e32 + 160); (pv, pv + 4); (pg, pg + 12); (A, A + BITS_SIZEOF)] m m'
/\ rw_cells asegs m' EB (f32 eb') /\ length eb' = length eb
/\ rw_cells asegs m' e32 (f32 e32') /\ length e32' = 40%nat
/\ rw_cells asegs m' pv [C4 (Z_to_bv 64 (ltp_pitch k start b))]
/\ rw_cells asegs m' pg (f32 pg') /\ length pg' = 3%nat
/\ bits_rep asegs m' A D (ltp_bits k b) /\ bits_ok (ltp_bits k b)
/\ rw_cells asegs m' (bv_unsigned sp) (ltp_args_cells A stk8 off)
/\ acc asegs m' e32 160 /\ acc asegs m' pv 4 /\ acc asegs m' pg 12 /\ acc asegs m' A BITS_SIZEOF) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Definition innov_unquant_cps (k : innov_kind) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A D : Z) b (inn seedp PAR lo P0 N0 PD ND fa : Z) (ka : nat) (is0 : list word) (seed0 stk8 : word),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 inn -> a1 = Z_to_bv 64 PAR -> a2 = Z_to_bv 64 40 -> a3 = Z_to_bv 64 A -> a4 = stk8 -> a5 = Z_to_bv 64 seedp -> tp = Z_to_bv 64 0x630458 ->
bits_rep asegs m A D b -> bits_ok b ->
match k with InnovSplitCbShapeSignUnquant p => ro_cells asegs m PAR (scb_par_cellsA p) /\ PAR mod 8 = 0 /\ 0x10000 <= PAR /\ PAR + 24 <= IMG_TOP /\ In (PAR, 24) ACC_LITS
| InnovNoiseCodebookUnquant => True end ->

rw_cells asegs m inn (f32 is0) -> length is0 = 40%nat -> dst_obj Σ m inn 160 ->

rw_cells asegs m seedp [C4 seed0] -> In (P0, N0) (rt_live RT Σ) -> P0 <= seedp -> seedp + 4 <= P0 + N0 -> seedp mod 4 = 0 ->

In (fa, ka) (rt_frames RT Σ) -> in_frame_obj Σ m fa ka A BITS_SIZEOF -> In (PD, ND) (rt_live RT Σ) -> PD <= D -> D + sb_buf_size b <= PD + ND ->
hidp (PD + ND <= P0 \/ P0 + N0 <= PD) -> hidp (A + BITS_SIZEOF <= inn \/ inn + 160 <= A) ->
ART RT Σ m -> mem_inv asegs m -> X1cn.frm0 fc ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + INNOV_STACK <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 -> pois_above (rt_pois RT Σ) (bv_unsigned sp) ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc (innov_entryA k) m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists v m' (is' : list word) (seed' : word),
ret_stL (fun _ fc' => X1cn.frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(inn, inn + 160); (seedp, seedp + 4); (A, A + BITS_SIZEOF)] m m'
/\ rw_cells asegs m' inn (f32 is') /\ length is' = 40%nat
/\ rw_cells asegs m' seedp [C4 seed']
/\ bits_rep asegs m' A D (innov_bits k b) /\ bits_ok (innov_bits k b)
/\ acc asegs m' inn 160 /\ acc asegs m' A BITS_SIZEOF) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).
End Kinds.

Section DstFacts.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Lemma dst_obj_facts : forall (Σ : rts RT) (m : mem) o n lo usp,
ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo <= usp -> usp + 16 <= USTACK_TOP -> pois_above (rt_pois RT Σ) usp -> 0 < n ->
dst_obj RT Σ m o n ->
acc asegs m o n /\ 0 < o /\ o + n <= APP_TOP /\ (o + n <= SH_LO \/ SH_HI <= o) /\ (o + n <= lo \/ usp <= o) /\ IMG_TOP <= o /\ o mod 4 = 0
/\ (forall i, 0 <= i < n -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp (o + i))
/\ rng_class RT Σ o n
/\ (forall p k, In (p, k) (rt_live RT Σ) -> p + k <= o \/ o + n <= p).
Proof using AF.
intros Σ m o n lo usp ART0 LOW LU UT POA N0 [(f & k & INF & (O1 & O2 & O3 & O4)) | INP].
- pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & _ & FI & _ & FS & _).
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (FB & _ & _).
pose proof (fs_size_ge64 k) as FSZ.
split; [exact O3|]. split; [lia|]. split; [unfold APP_TOP, USTACK_TOP in *; lia|]. split; [unfold SH_LO, SH_HI; lia|]. split; [left; lia|].
split; [unfold IMG_TOP, SEGTOP_A in *; lia|]. split; [exact O4|].
split; [intros i Hi; right; right; right; left; exists f, k; split; [exact INF| lia]|].
split; [right; left; exists f, k; split; [exact INF| split; [exact O1| exact O2]]|].
intros p kk INL. destruct (frame_live_apart RT AF Σ m f k p kk ART0 INF INL) as (FLA & _). lia.
- pose proof (af_pois_range RT AF Σ m o n ART0 INP) as (A32 & _ & R1 & R2).
pose proof (POA (o, n) INP) as PA. unfold pz_lo in PA. cbn [fst] in PA.
pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
assert (RR : o + n <= alloca_rr o n) by (unfold alloca_rr; Z.div_mod_to_equations; lia).
split; [exact (af_acc_pois RT AF Σ m o n ART0 INP)|].
unfold STACK_WIN, USTACK_TOP, APP_TOP, SH_LO, SH_HI, IMG_TOP in *.
split; [lia|]. split; [lia|]. split; [right; lia|]. split; [right; lia|]. split; [lia|].
split; [clear - A32; Z.div_mod_to_equations; lia|].
split; [intros i Hi; left; unfold USTACK_TOP; lia|].
split; [right; right; left; unfold STACK_WIN, USTACK_TOP; lia|].
intros p kk INL. destruct (live_below_lo RT AF Σ m p kk lo ART0 INL LOW) as (_ & PL & _). left. lia.
Qed.
End DstFacts.
