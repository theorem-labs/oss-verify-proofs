(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cq X1d0 X1cl X1dh X1cs X1da X1d1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require X1cn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1rw X1rv X1s9 X1rn X1ry X1rx X1s0.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e0 X1dx.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X0hi X03z X04v X0ec X00a X001 X00b X000
X0jh X0ji X047 X048 X01z X03c X0bs X03f X026 X03e X021
X04r X04l X04q X04o X057 X043 X040 X055 X022 X01y X02e X02d X0jo X04w X041 X04p.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require X01t X00u.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X183 X0ux X0vt X14x X0r9 X0r0 X0ra X0qz X0v5 X0v6 X0sy X0ub X12d X0ue X0t5 X0ud X0t0 X0vp X0vj X0vo X0vm X0w5 X0v1 X0uy X0w3 X0t1 X0sx X0td X0tc X1a3 X0vu X0uz X0vn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0ss X0rt.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ux OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v6 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0sy OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ub OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12d OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ue OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0t5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ud OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0t0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vj OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vo OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0uy OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w3 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0t1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0sx OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0td OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0tc OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X1a3 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vu OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0uz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vn.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Import X1cq.Exc.
Open Scope Z_scope.

Lemma frm0_dec : forall fc : bv 32, {X1cn.frm0 fc} + {~ X1cn.frm0 fc}.
Proof. intros fc. unfold X1cn.frm0. apply Z.eq_dec. Qed.

Definition fp_QfinR (fc : bv 32) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo : Z) (m : mem) (x : unit * unit)
(ms' : machine_state) : Prop :=
exists (m3 : mem),
(exists (v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 v a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m3 (seg_rom bsegs)
/\ (X1cn.frm0 fc -> X1cn.frm0 fc'))
/\ munch [(lo, usp); (0x1007b0, 0x1007b0 + 232)] m m3 /\ wmono bsegs m m3
/\ mem_inv bsegs m3 /\ stk bsegs m3 lo usp /\ stderr_wfile0 m3.

Section TailR.
Hypothesis RIP : rip_stmt.

Lemma fp_tail_frm : forall (m m2 : mem) (usp lo : Z) (g : word) (A : Z) (fmt : list Z) (args : list parg) (ps : list (list Z)) (r : Z)
(a2v a3v a4v a5v a6v a7v : word) (junk : list byte)
ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) fc,
X1cn.frm0 fc ->
munch [(usp - 2432, usp)] m m2 -> wmono bsegs m m2 -> mem_inv bsegs m2 ->
stk bsegs m2 lo (usp + -112) -> 0x7fff7f800000 <= lo -> lo + 0x10000 <= usp -> usp <= 2^47 ->
rw_cells bsegs m2 (usp + -112) (fpfr usp junk ra s0 s1 s2) ->
rw_cells bsegs m2 (usp + -48) [C8 a2v; C8 a3v; C8 a4v; C8 a5v; C8 a6v; C8 a7v] ->
stderr_wfile0 m2 -> ssp_cells m2 g -> ictx m2 -> (forall p n, lo + 64 <= p -> p + n <= usp + -112 -> chkr m2 p n) ->
chkr m2 A (zlength fmt) -> rod_chk m2 ->
bytes_at bsegs m2 A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
args_ok RSTDERR (usp + -112 - 352) 80 m2 lo (usp + -112) (usp + -112 - VF_FRAME) [a2v; a3v; a4v; a5v; a6v; a7v] args ->
printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
65536 <= A -> A + zlength fmt <= STATIC_SPLIT -> Forall (fun p => zlength p <= OUT_MAX) ps ->
impl bsegs (at_node bsegs) (stderr_prog [] ps tt) (epost (fp_QfinR fc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m))
(MS (mkR (Z_to_bv 64 0x5a5ac) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 0x1007b0)
(Z_to_bv 64 0x1007b0) (Z_to_bv 64 A) (Z_to_bv 64 (usp + -48)) a3 a4 a5 a6 a7 (Z_to_bv 64 (usp + -48))
s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xedf30) fc None m2 (seg_rom bsegs)).
Proof using RIP.
intros until fc. intros FRM MU2 WM2 MI2 ST2 LO0 LOR L3 FRp1 FRva ERR2 SSP2 IC2 STKC FMTC ROD BY HF P1 AOK PP FPC HA0 HA1 SZ.
assert (EU112 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; lia).
pose proof (stk_split bsegs m2 lo (lo + 64) (usp + -112) ST2 ltac:(lia)) as (ST2a & ST2b).
pose proof (X0rt.vfprintf_stderr_proof (St := unit)
(fwritex_stderr_proof RIP (fun St => @stdio_write_proof St))
(stdio_write_flush_proof (fun St => @stdio_write_proof St)) RIP) as VF.
unfold X0rt.vfprintf_stderr_stmt in VF. cbv zeta in VF.
pose proof (VF (Z_to_bv 64 0x5a5ac) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 0x1007b0)
(Z_to_bv 64 0x1007b0) (Z_to_bv 64 A) (Z_to_bv 64 (usp + -48)) a3 a4 a5 a6 a7 (Z_to_bv 64 (usp + -48))
s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 tt A (usp + -48) fmt [a2v; a3v; a4v; a5v; a6v; a7v] args ps r (lo + 64) g) as IM.
clear VF. unfold X1rv.implM in IM.
eapply impl_post_evt''.
{ apply (stderr_bridge bsegs ps [] tt (fun st' ms' => X0rt.vfprintf_stderr_post (Z_to_bv 64 0x5a5ac) (Z_to_bv 64 (usp + -112)) gp tp
(Z_to_bv 64 A) (Z_to_bv 64 0x1007b0) (Z_to_bv 64 (usp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 F (lo + 64) g m2 st' ms')); [exact SZ|].
apply IM; clear IM; rewrite ?EU112.
- reflexivity.
- reflexivity.
- reflexivity.
- exact (stderr_wfile0_wfile m2 ERR2).
- exact BY.
- exact HF.
- exact P1.
- exact (proj2 (proj1 FRva)).
- exact (args_ok_lo_mono _ _ _ _ lo (lo + 64) _ _ _ _ AOK ltac:(lia)).
- exact PP.
- exact FPC.
- exact ST2b.
- unfold X0ss.VF_DEPTH; lia.
- unfold GLOBALS_TOP; lia.
- lia.
- exact SSP2.
- exact MI2.
- exact FRM.
- exact HA0.
- exact HA1.
- lia.
- unfold zlength; cbn; lia.
- unfold kHighShadowEnd; lia.
- exact IC2.
- exact STKC.
- exact FMTC.
- exact ROD. }
intros [|[xr st']] ms3 H3; [apply evt_done; exact I|].
cbn [epost fst snd] in H3 |- *.
destruct H3 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc3 & m3 & -> & MU3 & WM3 & MI3
& FRM3 & _ & ST3 & ERR3 & SSP3).
rewrite EU112 in MU3, ST3.
rewrite (ret_pc_even 0x5a5ac) by lia.
assert (AG3 : agree_on (fun x => usp + -112 <= x) m2 m3).
{ apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn. split; [lia|]. split; [lia| exact I]. }
unfold fpfr in FRp1.
pose proof (rw_cells_agree bsegs m2 m3 _ _ FRp1 ltac:(apply (agree_sub _ _ _ _ AG3); intros x Hx; cbn in Hx; lia) WM3) as FRp3.
pose proof (rw_cells_agree bsegs m2 m3 _ _ FRva ltac:(apply (agree_sub _ _ _ _ AG3); intros x Hx; cbn in Hx; lia) WM3) as FRva3.
eapply evt_mono.
{ apply (fprintf_walkB usp (lo + 64) junk a2v a3v a4v a5v a6v a7v (Z_to_bv 64 0x5a5ac) ra gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 A)
(Z_to_bv 64 0x1007b0) b0 b1 b2 b3 b4 b5 b6 b7 s2 (Z_to_bv 64 (usp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 Ft fc3 m3
ST3 ltac:(lia) L3 FRp3 FRva3 MI3). }
intros ms4 ((w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & RS4) & ST4).
exists m3. split.
{ rewrite RS4. do 17 eexists. split; [reflexivity|]. intros _. exact FRM3. }
split.
{ apply (munch_merge [(usp - 2432, usp)] [(lo + 64, usp + -112); (0x1007b0, 0x1007b0 + 232)] _ m m2 m3 MU2 MU3).
intros x Hx. cbn in Hx |- *. intuition lia. }
split; [exact (wmono_trans bsegs m m2 m3 WM2 WM3)|]. split; [exact MI3|]. split; [| exact ERR3].
apply (stk_merge bsegs m3 lo (lo + 64) usp); [| exact ST4| lia].
exact (stk_transport_disjoint bsegs _ _ _ _ _ ST2a MU3 WM3 ltac:(cbn [disjoint_from]; lia)).
Qed.

Lemma fp_tail_R : forall (m m2 : mem) (usp lo : Z) (g : word) (A : Z) (fmt : list Z) (args : list parg) (ps : list (list Z)) (r : Z)
(a2v a3v a4v a5v a6v a7v : word) (junk : list byte)
ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) fc,
munch [(usp - 2432, usp)] m m2 -> wmono bsegs m m2 -> mem_inv bsegs m2 ->
stk bsegs m2 lo (usp + -112) -> 0x7fff7f800000 <= lo -> lo + 0x10000 <= usp -> usp <= 2^47 ->
rw_cells bsegs m2 (usp + -112) (fpfr usp junk ra s0 s1 s2) ->
rw_cells bsegs m2 (usp + -48) [C8 a2v; C8 a3v; C8 a4v; C8 a5v; C8 a6v; C8 a7v] ->
stderr_wfile0 m2 -> ssp_cells m2 g -> ictx m2 -> (forall p n, lo + 64 <= p -> p + n <= usp + -112 -> chkr m2 p n) ->
chkr m2 A (zlength fmt) -> rod_chk m2 ->
bytes_at bsegs m2 A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
args_ok RSTDERR (usp + -112 - 352) 80 m2 lo (usp + -112) (usp + -112 - VF_FRAME) [a2v; a3v; a4v; a5v; a6v; a7v] args ->
printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
65536 <= A -> A + zlength fmt <= STATIC_SPLIT -> Forall (fun p => zlength p <= OUT_MAX) ps ->
impl bsegs (at_node bsegs) (stderr_prog [] ps tt) (epost (fp_QfinR fc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m))
(MS (mkR (Z_to_bv 64 0x5a5ac) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 0x1007b0)
(Z_to_bv 64 0x1007b0) (Z_to_bv 64 A) (Z_to_bv 64 (usp + -48)) a3 a4 a5 a6 a7 (Z_to_bv 64 (usp + -48))
s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xedf30) fc None m2 (seg_rom bsegs)).
Proof using RIP.
intros until fc. intros MU2 WM2 MI2 ST2 LO0 LOR L3 FRp1 FRva ERR2 SSP2 IC2 STKC FMTC ROD BY HF P1 AOK PP FPC HA0 HA1 SZ.
destruct (frm0_dec fc) as [FRM|NFRM].
- exact (fp_tail_frm m m2 usp lo g A fmt args ps r a2v a3v a4v a5v a6v a7v junk ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc FRM MU2 WM2 MI2 ST2 LO0 LOR L3 FRp1 FRva ERR2 SSP2 IC2 STKC FMTC ROD BY HF P1 AOK PP FPC HA0 HA1 SZ).
- eapply impl_mono.
+ exact (fp_tail RIP m m2 usp lo g A fmt args ps r a2v a3v a4v a5v a6v a7v junk ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc MU2 WM2 MI2 ST2 LO0 LOR L3 FRp1 FRva ERR2 SSP2 IC2 STKC FMTC ROD BY HF P1 AOK PP FPC HA0 HA1 SZ).
+ intros [|[xr st']] ms' H; [exact H|]. cbn [epost fst snd] in H |- *.
destruct H as (m3 & (v & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & ->) & REST).
exists m3. split; [| exact REST]. do 17 eexists. split; [reflexivity|]. intros X. contradiction.
Qed.
End TailR.

Lemma tail_pieces_pfx1 : forall cnt p c body, 0 <= cnt -> 1 <= zlength body -> p <= zlength body -> cnt + 1 + zlength body <= INT_MAX ->
tail_pieces cnt 0 0 p [c] body = Some ([[c]; body], cnt + (1 + zlength body)).
Proof.
intros cnt p c body Hc Hb Hp HI. unfold tail_pieces. cbv zeta. change (zlength [c]) with 1.
replace (Z.max p (zlength body)) with (zlength body) by lia.
replace (INT_MAX - 1 <? zlength body) with false by (symmetry; apply Z.ltb_ge; lia).
replace (Z.max 0 (1 + zlength body)) with (1 + zlength body) by lia.
replace (INT_MAX - cnt <? 1 + zlength body) with false by (symmetry; apply Z.ltb_ge; lia).
unfold pad_pieces.
rewrite !Z.leb_refl. cbn [orb negb Z.land Z.lxor Z.lor Z.eqb Z.lnot ZERO_PAD LEFT_ADJ]. reflexivity.
Qed.

Definition int_ps (v : Z) : list (list Z) := if v =? 0 then [[]; [48]; []] else if v <? 0 then [[45]; dec_digits (- v)] else [[]; dec_digits v].
Definition int_len (v : Z) : Z := if v =? 0 then 1 else if v <? 0 then 1 + zlength (dec_digits (- v)) else zlength (dec_digits v).

Lemma conv_pieces_i : forall cnt v, 0 <= cnt -> - 2^31 <= v < 2^31 -> cnt + 21 <= INT_MAX ->
conv_pieces cnt {| d_fl := 0; d_w := 0; d_p := -1; d_xp := false; d_t := 100; d_ty := T_INT |} (PA_i v) = Some (int_ps v, cnt + int_len v).
Proof.
intros cnt v Hc Hv HI. unfold int_ps, int_len.
unfold conv_pieces. cbn [d_fl d_w d_p d_xp d_t d_ty].
change (Z.land 0 LEFT_ADJ =? 0) with true. cbv iota.
change (negb (T_INT =? T_INT)) with false. cbv iota.
change (negb (Z.land 0 MARK_POS =? 0)) with false. change (negb (Z.land 0 PAD_POS =? 0)) with false. cbv iota.
destruct (Z.eqb_spec v 0) as [->|NZ].
- change (0 mod 2 ^ 64) with 0. change (INTMAX_MAX <? 0) with false. cbv iota beta zeta.
unfold int_pieces. cbn [andb Z.eqb]. rewrite dec_digits_0. change (zlength (@nil Z)) with 0.
change (Z.max (-1) (0 + 1)) with 1. apply tail_pieces_zero1; lia.
- destruct (Z.ltb_spec v 0) as [NEG|POS].
+ replace (v mod 2^64) with (2^64 + v) by (symmetry; rewrite <- (Z.mod_small (2^64 + v) (2^64)) by lia; rewrite <- Z.add_mod_idemp_l, Z.mod_same by lia; reflexivity).
replace (INTMAX_MAX <? 2 ^ 64 + v) with true by (symmetry; apply Z.ltb_lt; unfold INTMAX_MAX; lia).
cbv iota beta zeta.
replace ((- (2 ^ 64 + v)) mod 2 ^ 64) with (- v).
2:{ symmetry. replace (- (2^64 + v)) with (- v + (-1) * 2^64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
pose proof (dec_digits_zlength (- v)) as DL. pose proof (dec_digits_nz (- v) ltac:(lia)) as NE.
assert (L1 : 1 <= zlength (dec_digits (- v))) by (destruct (dec_digits (- v)); [contradiction | unfold zlength; cbn; lia]).
unfold int_pieces. cbn [andb]. replace (- v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. rewrite Z.add_0_r.
rewrite tail_pieces_pfx1 by lia. reflexivity.
+ rewrite (Z.mod_small v (2^64)) by lia.
replace (INTMAX_MAX <? v) with false by (symmetry; apply Z.ltb_ge; unfold INTMAX_MAX; lia).
cbv iota beta zeta.
pose proof (dec_digits_zlength v) as DL. pose proof (dec_digits_nz v ltac:(lia)) as NE.
assert (L1 : 1 <= zlength (dec_digits v)) by (destruct (dec_digits v); [contradiction | unfold zlength; cbn; lia]).
unfold int_pieces. cbn [andb]. replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. rewrite Z.add_0_r.
rewrite tail_pieces_plain by lia. reflexivity.
Qed.
Lemma int_len_range : forall v, 0 <= int_len v <= 21.
Proof.
intros v. unfold int_len. pose proof (dec_digits_zlength v). pose proof (dec_digits_zlength (- v)).
destruct (v =? 0); [lia|]. destruct (v <? 0); lia.
Qed.

Definition FZ_NOTIFY : list Z := L_NOTIFY1 ++ [37; 115; 10; 0].
Definition FZ_WARN : list Z := L_WARN1 ++ [37; 115; 10; 0].
Definition FZ_WARNINT : list Z := L_WARN1 ++ [37; 115; 32; 37; 100; 10; 0].
Definition pieces_notify (s : list Z) : list (list Z) := [L_NOTIFY1; []; []; s; [10]].
Definition pieces_warn (s : list Z) : list (list Z) := [L_WARN1; []; []; s; [10]].
Definition pieces_warnint (s : list Z) (v : Z) : list (list Z) := [L_WARN1; []; []; s; [32]; []] ++ int_ps v ++ [[10]].

Lemma printf_pieces_notify : forall s, zlength s < INT_MAX - 256 ->
printf_pieces FZ_NOTIFY [PA_s s] = Some (pieces_notify s, 15 + zlength s).
Proof.
intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
change (Datatypes.length FZ_NOTIFY) with 18%nat.
ppl_step. ppl_step. rewrite conv_pieces_s by lia.
rewrite (ppl_noargs_shift 16 [10; 0] (14 + zlength s) [[10]] 1 ltac:(vm_compute; reflexivity)) by lia.
unfold pieces_notify. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.
Lemma printf_pieces_warn : forall s, zlength s < INT_MAX - 256 ->
printf_pieces FZ_WARN [PA_s s] = Some (pieces_warn s, 10 + zlength s).
Proof.
intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
change (Datatypes.length FZ_WARN) with 13%nat.
ppl_step. ppl_step. rewrite conv_pieces_s by lia.
rewrite (ppl_noargs_shift 11 [10; 0] (9 + zlength s) [[10]] 1 ltac:(vm_compute; reflexivity)) by lia.
unfold pieces_warn. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.
Lemma printf_pieces_warnint : forall s v, zlength s < 2^20 -> - 2^31 <= v < 2^31 ->
printf_pieces FZ_WARNINT [PA_s s; PA_i v] = Some (pieces_warnint s v, 9 + zlength s + 1 + int_len v + 1).
Proof.
intros s v Hs Hv. pose proof (zlength_nonneg' s) as H0. pose proof (int_len_range v) as IL. unfold printf_pieces.
change (Datatypes.length FZ_WARNINT) with 16%nat.
ppl_step. ppl_step. rewrite conv_pieces_s by (unfold INT_MAX; lia).
change [32; 37; 100; 10; 0] with ([32] ++ 37 :: [100; 10; 0]).
rewrite ppl_lit_cons; [ | discriminate | repeat (constructor; [lia|]); apply Forall_nil | right; split; [reflexivity | cbn; lia] | change (zlength [32]) with 1; unfold INT_MAX; lia ].
change (zlength [32]) with 1.
remember (9 + zlength s + 1) as c1 eqn:Ec1.
ppl_step. pose proof (conv_pieces_i c1 v ltac:(lia) Hv ltac:(unfold INT_MAX; lia)) as C2. cbv delta [T_INT] in C2. rewrite C2. clear C2.
rewrite (ppl_noargs_shift 12 [10; 0] (c1 + int_len v) [[10]] 1 ltac:(vm_compute; reflexivity)) by (unfold INT_MAX; lia).
unfold pieces_warnint. subst c1. cbn [app]. f_equal.
Qed.

Definition fpl_fmtz (k : fpl_kind) : list Z := match k with FLnotify => FZ_NOTIFY | FLwarn => FZ_WARN | FLwarn_int => FZ_WARNINT end.
Definition fpl_args (k : fpl_kind) (s : list Z) (v : Z) : list parg := match k with FLwarn_int => [PA_s s; PA_i v] | _ => [PA_s s] end.
Definition fpl_ps (k : fpl_kind) (s : list Z) (v : Z) : list (list Z) :=
match k with FLnotify => pieces_notify s | FLwarn => pieces_warn s | FLwarn_int => pieces_warnint s v end.
Definition fpl_r (k : fpl_kind) (s : list Z) (v : Z) : Z :=
match k with FLnotify => 15 + zlength s | FLwarn => 10 + zlength s | FLwarn_int => 9 + zlength s + 1 + int_len v + 1 end.

Lemma fpl_pieces : forall k s v, zlength s < 2^20 -> (k = FLwarn_int -> - 2^31 <= v < 2^31) ->
printf_pieces (fpl_fmtz k) (fpl_args k s v) = Some (fpl_ps k s v, fpl_r k s v).
Proof.
intros [| |] s v Hs Hv; cbn [fpl_fmtz fpl_args fpl_ps fpl_r].
- apply printf_pieces_notify. unfold INT_MAX. lia.
- apply printf_pieces_warn. unfold INT_MAX. lia.
- apply printf_pieces_warnint; [exact Hs | exact (Hv eq_refl)].
Qed.
Lemma fpl_pass1 : forall k, pass1_ok (fpl_fmtz k) = true. Proof. intros [| |]; vm_compute; reflexivity. Qed.
Lemma fpl_fp_calls : forall k s v, fp_calls (length (fpl_fmtz k)) (fpl_fmtz k) (fpl_args k s v) = [].
Proof. intros [| |] s v; vm_compute; reflexivity. Qed.
Lemma fpl_fmtz_bytes : forall k, Forall (fun c => 0 <= c < 256) (fpl_fmtz k).
Proof. intros [| |]; apply Forall_byte_of_forallb; vm_compute; reflexivity. Qed.
Lemma concat_int_ps : forall v, concat (int_ps v) = fpl_int v.
Proof. intros v. unfold int_ps, fpl_int. destruct (v =? 0); [reflexivity|]. destruct (v <? 0); cbn [concat app]; rewrite ?app_nil_r; reflexivity. Qed.
Lemma concat_fpl_ps : forall k (str : list byte) v, concat (fpl_ps k (map bv_unsigned str) v) = fpl_msg k str v.
Proof.
intros [| |] str v; cbn [fpl_ps fpl_msg]; unfold pieces_notify, pieces_warn, pieces_warnint.
- cbn [concat app]. rewrite ?app_nil_r. reflexivity.
- cbn [concat app]. rewrite ?app_nil_r. reflexivity.
- rewrite !concat_app. rewrite concat_int_ps. cbn [concat app]. rewrite ?app_nil_r.
unfold FPL_WARN, L_WARN1. cbn [app]. rewrite <- ?app_assoc. reflexivity.
Qed.
Lemma fpl_ps_small : forall k s v, zlength s <= 2^20 -> Forall (fun p => zlength p <= OUT_MAX) (fpl_ps k s v).
Proof.
intros k s v Hs. pose proof (dec_digits_zlength v) as D1. pose proof (dec_digits_zlength (- v)) as D2.
assert (HI : Forall (fun p => zlength p <= OUT_MAX) (int_ps v)).
{ unfold int_ps. destruct (v =? 0); [| destruct (v <? 0)]; repeat constructor; unfold OUT_MAX, zlength in *; cbn [length]; lia. }
destruct k; cbn [fpl_ps]; unfold pieces_notify, pieces_warn, pieces_warnint.
- repeat constructor; unfold OUT_MAX, zlength in *; cbn; lia.
- repeat constructor; unfold OUT_MAX, zlength in *; cbn; lia.
- apply Forall_app. split; [repeat constructor; unfold OUT_MAX, zlength in *; cbn; lia|].
apply Forall_app. split; [exact HI|]. repeat constructor; unfold OUT_MAX, zlength; cbn; lia.
Qed.
Lemma fpl_msg_len : forall k (str : list byte) v, zlength (fpl_msg k str v) <= Z.of_nat (length str) + 64.
Proof.
intros k str v. rewrite <- concat_fpl_ps.
pose proof (dec_digits_zlength v) as D1. pose proof (dec_digits_zlength (- v)) as D2.
assert (HI : zlength (concat (int_ps v)) <= 21).
{ unfold int_ps. destruct (v =? 0); [| destruct (v <? 0)]; cbn [concat app]; rewrite ?app_nil_r; unfold zlength in *; cbn [length]; lia. }
destruct k; cbn [fpl_ps]; unfold pieces_notify, pieces_warn, pieces_warnint.
- cbn [concat app]. unfold zlength. rewrite ?length_app, ?length_map. cbn [length L_NOTIFY1]. lia.
- cbn [concat app]. unfold zlength. rewrite ?length_app, ?length_map. cbn [length L_WARN1]. lia.
- rewrite !concat_app. unfold zlength in *. rewrite ?length_app. cbn [concat app length L_WARN1]. rewrite ?length_app, ?length_map. cbn [length]. lia.
Qed.

Fixpoint img_ok_b (A : Z) (n : nat) : bool :=
match n with
| O => true
| S n' => match seg_rom bsegs (wa A) with Some _ => img_ok_b (A + 1) n' | None => false end
end.
Lemma img_ok_b_sound : forall n A (m : mem), 0 <= A -> A + Z.of_nat n <= 2^64 -> img_ok_b A n = true -> exists bs, length bs = n /\ bytes_at bsegs m A bs.
Proof.
induction n as [|n IH]; intros A m HA HB H; cbn [img_ok_b] in H.
- exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
- destruct (seg_rom bsegs (wa A)) as [b0|] eqn:E; [| discriminate].
destruct (IH (A + 1) m ltac:(lia) ltac:(lia) H) as (bs & L & BY).
assert (RD : exists b, mrd bsegs m (wa A) = Some b) by (unfold mrd; destruct (m (wa A)) as [b1|]; [exists b1; reflexivity | exists b0; exact E]).
destruct RD as (b & RD). exists (b :: bs). split; [cbn; lia|].
change (b :: bs) with ([b] ++ bs). apply (proj2 (bytes_at_app bsegs m A [b] bs)). split; [| exact BY].
split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. assert (i = 0%nat) by lia. subst i. rewrite Z.add_0_r. exact RD.
Qed.

Definition lit_ok_b (r : Z * Z) : bool :=
(0x232a0 <=? fst r) && (fst r + snd r <=? 0xf9098) && (0 <? snd r) && (snd r <=? 1280) && img_ok_b (fst r) (Z.to_nat (snd r) + 7).
Lemma acc_lits_ok : forallb lit_ok_b ACC_LITS = true.
Proof. vm_compute. reflexivity. Qed.

Lemma acc_lits_range : forall sa n, In (sa, n) ACC_LITS -> 0x232a0 <= sa /\ sa + n <= 0xf9098 /\ 0 < n <= 1280.
Proof.
intros sa n H. pose proof (proj1 (forallb_forall _ _) acc_lits_ok _ H) as B. unfold lit_ok_b in B. cbn [fst snd] in B.
repeat (apply andb_prop in B; destruct B as [B ?]). lia.
Qed.

Lemma acc_lits_slack : forall m sa n o, mem_inv bsegs m -> In (sa, n) ACC_LITS -> 0 <= o <= n ->
exists slack, bytes_at bsegs m (sa + o) slack /\ (- (sa + o)) mod 8 <= Z.of_nat (length slack) /\ Z.of_nat (length slack) <= 7.
Proof.
intros m sa n o MI H Ho. pose proof (acc_lits_range sa n H) as R.
pose proof (proj1 (forallb_forall _ _) acc_lits_ok _ H) as B. unfold lit_ok_b in B. cbn [fst snd] in B.
apply andb_prop in B. destruct B as [_ B]. destruct (img_ok_b_sound (Z.to_nat n + 7) sa m ltac:(lia) ltac:(lia) B) as (bs & L & BY).
pose proof (Z.mod_pos_bound (- (sa + o)) 8 ltac:(lia)) as K.
exists (firstn (Z.to_nat ((- (sa + o)) mod 8)) (skipn (Z.to_nat o) bs)).
assert (LS : length (firstn (Z.to_nat ((- (sa + o)) mod 8)) (skipn (Z.to_nat o) bs)) = Z.to_nat ((- (sa + o)) mod 8)).
{ rewrite firstn_length, skipn_length, L. lia. }
split; [| rewrite LS; lia].
replace (sa + o) with (sa + Z.of_nat (Z.to_nat o)) at 1 by lia. apply bytes_at_sub'; [exact BY | rewrite L; lia].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Lemma pcom_lib_spec : forall (k : fpl_kind) (A : Z), In A (fpl_fmts k) ->
forall (lo : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (ap S : Z) (str : list byte),
a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 ap ->
ro_cells bsegs m ap [C8 (Z_to_bv 64 S)] -> bv_unsigned sp <= ap -> ap + 16 < 2^63 ->
cstr_at m S str -> 0 < S -> (S + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= S) -> S + Z.of_nat (length str) + 1 < 2^47 ->
chk_ok m S (Z.of_nat (length str) + 1) ->
stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp <= 2^47 ->
bv_unsigned sp mod 16 = 0 -> chk_ok m A (zlength (fpl_fmtz k)) -> pctx m -> mem_inv bsegs m ->
evt bsegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x59658) fc None m (seg_rom bsegs)).
Proof using RIP.
intros k A HA. intros until str. intros E1 E2 SLOT QAP APH CSS S0 SSEP SH CHKS ST LO LOLO SPH S16 CHK PCX MI.
destruct k; cbn [fpl_fmts fpl_fmtz] in HA, CHK.
- eapply (pcom_notify_spec RIP A HA); try eassumption. lia.
- destruct HA as [<-|[]]. eapply (pcom_warn_spec RIP); try eassumption. lia.
- assert (HR : 0 <= A < 2^20) by (destruct HA as [<-|[<-|[<-|[<-|[]]]]]; lia).
eapply (pcom_fstrint_spec RIP A L_WARN1 ap S str lo); try eassumption.
+ reflexivity.
+ exact (cstr_f_warnint A HA m MI).
+ unfold kHighShadowEnd in LOLO. cbn [length L_WARN1 Z.of_nat]. lia.
Qed.
End WithRIP.

Section XFprintfLib.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.
Hypothesis AF_PF : forall Σ m, ART RT Σ m -> pf_consts m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.

Lemma fpl_fmt_lit : forall k fmt, In fmt (fpl_fmts k) -> In (fmt, zlength (fpl_fmtz k)) ACC_LITS /\ 0x23580 <= fmt <= 0x272c0.
Proof.
intros [| |] fmt H; cbn [fpl_fmts fpl_fmtz] in *.
- destruct H as [<-|[<-|[<-|[<-|[]]]]]; (split; [unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | lia]).
- destruct H as [<-|[]]; (split; [unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | lia]).
- destruct H as [<-|[<-|[<-|[<-|[]]]]]; (split; [unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | lia]).
Qed.
Lemma fpl_fmt_bytes : forall k fmt m, In fmt (fpl_fmts k) -> mem_inv bsegs m -> bytes_at bsegs m fmt (zb (fpl_fmtz k)).
Proof.
intros [| |] fmt m H MI; cbn [fpl_fmts fpl_fmtz] in *.
- destruct H as [<-|[<-|[<-|[<-|[]]]]]; (apply img_bytes; [assumption | lia | cbn; lia | vm_compute; reflexivity]).
- destruct H as [<-|[]]; (apply img_bytes; [assumption | lia | cbn; lia | vm_compute; reflexivity]).
- destruct H as [<-|[<-|[<-|[<-|[]]]]]; (apply img_bytes; [assumption | lia | cbn; lia | vm_compute; reflexivity]).
Qed.
Lemma fpl_fmtz_len : forall k, 13 <= zlength (fpl_fmtz k) <= 18. Proof. intros [| |]; vm_compute; split; discriminate. Qed.

Theorem fprintf_lib_ok : fprintf_lib_icontract RT OUT_repA ERR_repA IO_FPA.
Proof using AF RIP AF_SHW AF_PF.
intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m k fmt sa v str errp lo
Ha0 Ha1 Ha2 Ha3 Herrp HFMT (n & HLIT & HLEN) BYs NZ HFD ERR0 (g & SG1 & SG2) ART0 MI0 CALL POIS.
subst a0 a1 a2 errp. intros T c' Hc Hk.
pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
destruct CALL as (ST & LOW & LOR & SPT & SPA).
set (usp := bv_unsigned sp) in *.
pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
rewrite ESP in Hc.
destruct (AF_PF Σ m ART0) as (PFC & IC & ACCF & ACCP & ACCX & ACCN & ACCU & ACCO & ACCR & ACCT).
assert (LO0 : 0x7fff7f800000 <= lo) by ul.
assert (L3 : usp <= 2^47) by ul.
assert (PCX : pctx m).
{ destruct IC as ((G2 & G1 & RM & SHC & RI) & _ & _ & M2S). split; [exact M2S| split; assumption]. }

pose proof (acc_lits_range sa n HLIT) as RS.
destruct (fpl_fmt_lit k fmt HFMT) as (FLIT & RF). pose proof (fpl_fmtz_len k) as FZL.
pose proof (af_acc_lits RT AF Σ m ART0) as ACL. rewrite Forall_forall in ACL.
pose proof (ACL _ HLIT) as ACS. pose proof (ACL _ FLIT) as ACFM. cbn [fst snd] in ACS, ACFM. clear ACL.
set (len := Z.of_nat (length str)) in *.
assert (LEN0 : 0 <= len) by (unfold len; lia).
assert (ACS1 : acc bsegs m sa (len + 1)) by (apply (acc_sub bsegs m sa n sa (len + 1) ACS); lia).
assert (CHKS : chk_ok m sa (len + 1)).
{ apply (chk_ok_of RT AF_SHW Σ m _ _ ART0); [lia|]. intros _. split; [exact ACS1|]. right; right; right. ul. }
assert (CHKF : chk_ok m fmt (zlength (fpl_fmtz k))).
{ apply (chk_ok_of RT AF_SHW Σ m _ _ ART0); [lia|]. intros _. split; [exact ACFM|]. right; right; right. ul. }
destruct (acc_lits_slack m sa n (len + 1) MI0 HLIT ltac:(lia)) as (slack & SLK & SLKM & SLK7).
set (sZ := map bv_unsigned str).
assert (EZL : zlength sZ = len) by (unfold zlength, sZ, len; rewrite length_map; reflexivity).

set (Qfin := fp_QfinR fc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m).
assert (IMPL : impl bsegs (at_node bsegs) (stderr_prog [] (fpl_ps k sZ v) tt) (epost Qfin)
(entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STDERR_FILE) (Z_to_bv 64 fmt)
(Z_to_bv 64 sa) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fprintf m)).
{ eapply impl_evt with (P := fun ms' => impl bsegs (at_node bsegs) (stderr_prog [] (fpl_ps k sZ v) tt) (epost Qfin) ms');
[| intros ms' H; exact H].
eapply evt_cut; [exact (fprintf_walkA1 usp lo ra gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STDERR_FILE) (Z_to_bv 64 fmt)
(Z_to_bv 64 sa) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
ST ltac:(ul) ltac:(ul) L3 PFC MI0)|].
intros ms1 (m1 & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & junk & -> & MU1 & WM1 & MI1 & ST1 & FRp1 & FRva).
assert (AG1 : agree_on (fun x => x < usp - 128 \/ usp <= x) m m1).
{ apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn. split; [lia| exact I]. }
assert (EU112 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; ul).
assert (PCX1 : pctx m1) by (apply (pctx_munch _ m m1 PCX MU1 WM1); intros ?x ?Hx; unfold in_PCR in Hx; cbn [outside]; ul).
assert (CHM : forall p n, chk_ok m p n -> 0 <= p -> p + n <= 2^47 -> chk_ok m1 p n).
{ intros p n0 H Hp1 Hp2. apply (chk_ok_agree m m1 p n0 H Hp1 Hp2). apply (agree_sub _ _ _ _ AG1). intros x Hx. ul. }
pose proof (munch_weaken [(usp - 128, usp)] [(usp - 2432, usp)] m m1 ltac:(unfold sub_fp; cbn [outside]; intros; lia) MU1) as MUacc.
clear MU1.
assert (ERR1 : stderr_wfile0 m1) by (apply (stderr_wfile0_agree m m1); [apply (agree_sub _ _ _ _ AG1); intros x Hx; ul| exact WM1| exact ERR0]).
assert (SSP1 : ssp_cells m1 g).
{ split.
- apply (ro_cells_agree bsegs m m1 _ _ SG1). apply (agree_sub _ _ _ _ AG1). intros x Hx. cbn in Hx. ul.
- apply (ro_cells_agree bsegs m m1 _ _ SG2). apply (agree_sub _ _ _ _ AG1). intros x Hx. cbn in Hx. ul. }
assert (IC1 : ictx m1) by (apply (ictx_munch _ m m1 IC MUacc WM1); intros ?x ?Hx; cbn [in_rl ICR outside] in *; ul).
assert (PFC1 : pfcells m1) by (apply (pfcells_munch _ m m1 PFC MUacc WM1); intros ?x ?Hx; unfold in_PFR in Hx; cbn [outside]; ul).
pose proof (bytes_at_bound _ _ _ _ BYs) as BYB. rewrite length_app in BYB. cbn [length] in BYB.
assert (CS1 : cstr_at m1 sa str).
{ split; [| exact NZ]. apply (bytes_at_agree bsegs m m1 _ _ BYs). apply (agree_sub _ _ _ _ AG1). intros x Hx.
rewrite length_app in Hx; cbn [length] in Hx. ul. }
assert (SLOT1 : ro_cells bsegs m1 (usp + -48) [C8 (Z_to_bv 64 sa)]).
{ pose proof (proj1 (X0t2.rw_cells_app bsegs _ _ [_] _) FRva) as (H & _). exact (proj1 H). }
call (pcom_lib_spec RIP k fmt HFMT lo);
[ reflexivity | reflexivity | exact SLOT1 | rewrite EU112; lia | ul | exact CS1 | ul | left; fold len; ul | fold len; ul
| apply CHM; [exact CHKS| lia| ul] | rewrite EU112; exact ST1 | rewrite EU112; ul | unfold kHighShadowEnd; ul
| rewrite EU112; ul | rewrite EU112; Z.div_mod_to_equations; lia
| apply CHM; [exact CHKF| lia| ul]
| exact PCX1 | exact MI1 | ].
rename POST into ST2. rewrite EU112 in ST2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (PFC2 : pfcells mm) by (apply (pfcells_munch _ m mm PFC MUacc ltac:(assumption)); intros ?x ?Hx; unfold in_PFR in Hx; cbn [outside]; ul) end.
destruct PFC2 as (_ & _ & _ & _ & RVF2).
eapply evt_cut; [apply (fprintf_walkA2 usp junk ra s0 s1 s2); [exact FRp1| exact RVF2| exact L3| ul| assumption]|].
intros ms2 (a3'' & ->).
apply evt_done.
lazymatch goal with |- impl _ _ _ _ (MS _ _ _ _ _ ?mm _) => set (m2 := mm) in * end.
assert (CHR : forall p n, chkr m p n -> chkr m2 p n).
{ intros p n0 H. apply (chkr_munch _ m m2 p n0 H MUacc). intros y Hy. cbn [outside]. unfold SHADOW_LO, SHADOW_HI in Hy. ul. }
assert (AG2 : agree_on (fun x => x < usp - 2432 \/ usp <= x) m m2).
{ apply (agree_of_munch _ _ _ _ MUacc). intros y Hy. cbn. split; [lia| exact I]. }
eapply (fp_tail_R RIP m m2 usp lo g fmt (fpl_fmtz k) (fpl_args k sZ v) (fpl_ps k sZ v) (fpl_r k sZ v)).
+ exact MUacc.
+ assumption.
+ assumption.
+ exact ST2.
+ exact LO0.
+ ul.
+ exact L3.
+ exact FRp1.
+ exact FRva.
+ apply (stderr_wfile0_agree m m2); [apply (agree_sub _ _ _ _ AG2); intros y Hy; ul| assumption| exact ERR0].
+ split.
* apply (ro_cells_agree bsegs m m2 _ _ SG1). apply (agree_sub _ _ _ _ AG2). intros y Hy. cbn in Hy. ul.
* apply (ro_cells_agree bsegs m m2 _ _ SG2). apply (agree_sub _ _ _ _ AG2). intros y Hy. cbn in Hy. ul.
+ apply (ictx_munch _ m m2 IC MUacc ltac:(assumption)); intros ?y ?Hy; cbn [in_rl ICR outside] in *; ul.
+ intros p n0 H1 H2. apply CHR. destruct (Z_lt_le_dec 0 n0) as [NP|NN].
* apply (chkr_of RT AF_SHW Σ m p n0 ART0); [ul| | ].
-- apply (af_acc_stack RT AF Σ m p n0 ART0); [ul | ul | apply (pois_apart_above _ _ _ _ POIS); ul].
-- right; right; left. ul.
* split; [intros i Hi; lia| split; [intros i Hi; lia|]]. split; [| lia]. unfold region_in_mem, kLowMemEnd, kHighMemEnd. right. ul.
+ apply CHR. apply (chkr_of RT AF_SHW Σ m _ _ ART0); [lia| exact ACFM| right; right; right; ul].
+ split; [| split]; apply CHR; (apply (chkr_of RT AF_SHW Σ m _ _ ART0); [lia| assumption| right; right; right; unfold PFX_A, XDIG_A, NULLS_A; ul]).
+ apply (bytes_at_agree bsegs m m2 _ _ (fpl_fmt_bytes k fmt m HFMT MI0)). apply (agree_sub _ _ _ _ AG2). intros y Hy.
unfold zb in Hy. rewrite length_map in Hy. unfold zlength in FZL. ul.
+ exact (fpl_fmtz_bytes k).
+ exact (fpl_pass1 k).
+ assert (AS : arg_ok RSTDERR (usp + -112 - 352) 80 m2 lo (usp + -112) (usp + -112 - VF_FRAME) (Z_to_bv 64 sa) (PA_s sZ)).
{ cbn [arg_ok]. exists slack. rewrite (unsigned_lit sa) by ul. unfold sZ at 1. rewrite map_to_bytes_unsigned'. rewrite EZL.
split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
* apply (proj2 (bytes_at_app bsegs m2 sa str (Z_to_bv 8 0 :: slack))). split.
-- apply (bytes_at_agree bsegs m m2 _ _ (proj1 (proj1 (bytes_at_app bsegs m sa str [Z_to_bv 8 0]) BYs))).
apply (agree_sub _ _ _ _ AG2). intros y Hy. fold len in Hy. ul.
-- apply (proj2 (bytes_at_app bsegs m2 _ [Z_to_bv 8 0] slack)). split.
++ apply (bytes_at_agree bsegs m m2 _ _ (proj2 (proj1 (bytes_at_app bsegs m sa str [Z_to_bv 8 0]) BYs))).
apply (agree_sub _ _ _ _ AG2). intros y Hy. cbn [length] in Hy. fold len in Hy. ul.
++ cbn [length]. fold len. replace (sa + len + Z.of_nat 1) with (sa + (len + 1)) by lia.
apply (bytes_at_agree bsegs m m2 _ _ SLK). apply (agree_sub _ _ _ _ AG2). intros y Hy. ul.
* apply Forall_forall. intros zc Hzc. apply in_map_iff in Hzc. destruct Hzc as (b & <- & Hb).
pose proof (bv_unsigned_in_range 8 b) as RB. unfold bv_modulus in RB. change (2 ^ Z.of_N 8) with 256 in RB.
split; [| lia]. destruct (Z.eq_dec (bv_unsigned b) 0) as [E0|E0]; [| lia].
exfalso. apply NZ. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity.
* unfold zlength. replace (sa + len + 1) with (sa + (len + 1)) by lia. exact SLKM.
* ul.
* left. unfold zlength. ul.
* left. unfold zlength. ul.
* left. unfold zlength. ul.
* left. unfold zlength, VF_FRAME. ul.
* apply CHR. apply (chkr_of RT AF_SHW Σ m _ _ ART0); [ul| exact ACS1 | right; right; right; ul]. }
destruct k; cbn [fpl_args args_ok]; (split; [exact AS|]); try exact I.
split; [| exact I]. destruct (Ha3 eq_refl) as (-> & RV). cbn [arg_ok]. split; [exact RV|].
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). Z.div_mod_to_equations. lia.
+ apply fpl_pieces; [rewrite EZL; lia|]. intros ->. exact (proj2 (Ha3 eq_refl)).
+ apply fpl_fp_calls.
+ lia.
+ unfold STATIC_SPLIT. lia.
+ apply fpl_ps_small. rewrite EZL. lia. }
assert (MSGB : zlength (fpl_msg k str v) <= 2^26).
{ pose proof (fpl_msg_len k str v). fold len in H. lia. }
assert (TOK : tok [2] (stderr_prog [] (fpl_ps k sZ v) tt)).
{ apply tok_stderr_fprintf. cbn [app]. unfold sZ. rewrite concat_fpl_ps. exact MSGB. }
assert (RZ : realizes bsegs c' (TT (stderr_prog [] (fpl_ps k sZ v) tt) (fun _ => t_emit [] T))).
{ apply (impl_realizes bsegs SEGTOP_A asegs_wx asegs_below [2] _ (rt_allow RT Σ) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo)
Qfin (fun _ => t_emit [] T)
(entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STDERR_FILE) (Z_to_bv 64 fmt)
(Z_to_bv 64 sa) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fprintf m) c'
(ASTA_PM_mat_stable RT AF Σ F0 fs0)); [| exact TOK| exact Hc| exact IMPL|].
- intros mo fd (HAR & HF & _) Hin. cbn in Hin. destruct Hin as [<-|[]]. rewrite HF. exact HFD.
- intros x ms' c2 HQ Hc2.
assert (R : realizes bsegs c2 T).
{ apply Hk. eapply ASTA_conseq; [exact Hc2|]. intros ms <-.
destruct HQ as (m3 & (r & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & -> & FRMK)
& MU3 & WM3 & MI3 & ST3 & ERR3).
exists r, m3. split.
{ rewrite ESP. do 16 eexists. split; [reflexivity | exact FRMK]. }
split; [split; [| split; [exact MI3| split; [exact WM3| exact ST3]]]|].
- apply (af_frame RT AF Σ m m3 lo ART0); [ul| | exact WM3].
intros a Ha. apply MU3. cbn. split; [intros Hin; apply Ha; left; ul|].
split; [intros Hin; apply Ha; right; left; apply client_static_intro; lia| exact I].
- split; [| split].
+ intros a Ha Hout. apply MU3. cbn in Hout |- *. destruct Hout as (O1 & O2 & O3 & _). split; [| split; [lia| exact I]].
destruct (aclient_split RT AF Σ m usp _ ART0 Ha); ul.
+ exact ERR3.
+ intros so OUT0. apply (stdout_file_agree so m m3); [| exact WM3| exact OUT0].
apply (agree_of_munch _ _ _ _ MU3). intros y Hy. cbn. split; [ul| split; [lia| exact I]]. }
eapply rz_conseq; [exact R|]. apply t_eq_sym, t_emit_nil_eq. exact (realizes_nonempty bsegs _ _ R). }
eapply rz_conseq; [exact RZ|].
eapply t_eq_trans; [apply (TT_stderr_fprintf (fpl_ps k sZ v) [] tt (fun _ => t_emit [] T)); [cbn [app]; unfold sZ; rewrite concat_fpl_ps; exact MSGB| apply t_emit_has_nil]|].
cbn [app]. unfold sZ. rewrite concat_fpl_ps.
eapply t_eq_trans; [apply t_eq_sym, t_emit_app|]. rewrite app_nil_r. apply t_eq_refl.
Qed.
End XFprintfLib.
End B_TWIN.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Import X1cq.Exc.
Open Scope Z_scope.

Lemma frm0_dec : forall fc : bv 32, {X1cn.frm0 fc} + {~ X1cn.frm0 fc}.
Proof. intros fc. unfold X1cn.frm0. apply Z.eq_dec. Qed.

Definition fp_QfinR (fc : bv 32) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp lo : Z) (m : mem) (x : unit * unit)
(ms' : machine_state) : Prop :=
exists (m3 : mem),
(exists (v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 v a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m3 (seg_rom asegs)
/\ (X1cn.frm0 fc -> X1cn.frm0 fc'))
/\ munch [(lo, usp); (0xf7f30, 0xf7f30 + 232)] m m3 /\ wmono asegs m m3
/\ mem_inv asegs m3 /\ stk asegs m3 lo usp /\ stderr_wfile0 m3.

Section TailR.
Hypothesis RIP : rip_stmt.

Lemma fp_tail_frm : forall (m m2 : mem) (usp lo : Z) (g : word) (A : Z) (fmt : list Z) (args : list parg) (ps : list (list Z)) (r : Z)
(a2v a3v a4v a5v a6v a7v : word) (junk : list byte)
ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) fc,
X1cn.frm0 fc ->
munch [(usp - 2432, usp)] m m2 -> wmono asegs m m2 -> mem_inv asegs m2 ->
stk asegs m2 lo (usp + -112) -> 0x7fff7f800000 <= lo -> lo + 0x10000 <= usp -> usp <= 2^47 ->
rw_cells asegs m2 (usp + -112) (fpfr usp junk ra s0 s1 s2) ->
rw_cells asegs m2 (usp + -48) [C8 a2v; C8 a3v; C8 a4v; C8 a5v; C8 a6v; C8 a7v] ->
stderr_wfile0 m2 -> ssp_cells m2 g -> ictx m2 -> (forall p n, lo + 64 <= p -> p + n <= usp + -112 -> chkr m2 p n) ->
chkr m2 A (zlength fmt) -> rod_chk m2 ->
bytes_at asegs m2 A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
args_ok RSTDERR (usp + -112 - 352) 80 m2 lo (usp + -112) (usp + -112 - VF_FRAME) [a2v; a3v; a4v; a5v; a6v; a7v] args ->
printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
65536 <= A -> A + zlength fmt <= STATIC_SPLIT -> Forall (fun p => zlength p <= OUT_MAX) ps ->
impl asegs (at_node asegs) (stderr_prog [] ps tt) (epost (fp_QfinR fc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m))
(MS (mkR (Z_to_bv 64 0x5a4c0) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 0xf7f30)
(Z_to_bv 64 0xf7f30) (Z_to_bv 64 A) (Z_to_bv 64 (usp + -48)) a3 a4 a5 a6 a7 (Z_to_bv 64 (usp + -48))
s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xe56bc) fc None m2 (seg_rom asegs)).
Proof using RIP.
intros until fc. intros FRM MU2 WM2 MI2 ST2 LO0 LOR L3 FRp1 FRva ERR2 SSP2 IC2 STKC FMTC ROD BY HF P1 AOK PP FPC HA0 HA1 SZ.
assert (EU112 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; lia).
pose proof (stk_split asegs m2 lo (lo + 64) (usp + -112) ST2 ltac:(lia)) as (ST2a & ST2b).
pose proof (X00u.vfprintf_stderr_proof (St := unit)
(fwritex_stderr_proof RIP (fun St => @stdio_write_proof St))
(stdio_write_flush_proof (fun St => @stdio_write_proof St)) RIP) as VF.
unfold X00u.vfprintf_stderr_stmt in VF. cbv zeta in VF.
pose proof (VF (Z_to_bv 64 0x5a4c0) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 0xf7f30)
(Z_to_bv 64 0xf7f30) (Z_to_bv 64 A) (Z_to_bv 64 (usp + -48)) a3 a4 a5 a6 a7 (Z_to_bv 64 (usp + -48))
s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 tt A (usp + -48) fmt [a2v; a3v; a4v; a5v; a6v; a7v] args ps r (lo + 64) g) as IM.
clear VF. unfold X1rv.implM in IM.
eapply impl_post_evt''.
{ apply (stderr_bridge asegs ps [] tt (fun st' ms' => X00u.vfprintf_stderr_post (Z_to_bv 64 0x5a4c0) (Z_to_bv 64 (usp + -112)) gp tp
(Z_to_bv 64 A) (Z_to_bv 64 0xf7f30) (Z_to_bv 64 (usp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 F (lo + 64) g m2 st' ms')); [exact SZ|].
apply IM; clear IM; rewrite ?EU112.
- reflexivity.
- reflexivity.
- reflexivity.
- exact (stderr_wfile0_wfile m2 ERR2).
- exact BY.
- exact HF.
- exact P1.
- exact (proj2 (proj1 FRva)).
- exact (args_ok_lo_mono _ _ _ _ lo (lo + 64) _ _ _ _ AOK ltac:(lia)).
- exact PP.
- exact FPC.
- exact ST2b.
- unfold X01t.VF_DEPTH; lia.
- unfold GLOBALS_TOP; lia.
- lia.
- exact SSP2.
- exact MI2.
- exact FRM.
- exact HA0.
- exact HA1.
- lia.
- unfold zlength; cbn; lia.
- unfold kHighShadowEnd; lia.
- exact IC2.
- exact STKC.
- exact FMTC.
- exact ROD. }
intros [|[xr st']] ms3 H3; [apply evt_done; exact I|].
cbn [epost fst snd] in H3 |- *.
destruct H3 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc3 & m3 & -> & MU3 & WM3 & MI3
& FRM3 & _ & ST3 & ERR3 & SSP3).
rewrite EU112 in MU3, ST3.
rewrite (ret_pc_even 0x5a4c0) by lia.
assert (AG3 : agree_on (fun x => usp + -112 <= x) m2 m3).
{ apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn. split; [lia|]. split; [lia| exact I]. }
unfold fpfr in FRp1.
pose proof (rw_cells_agree asegs m2 m3 _ _ FRp1 ltac:(apply (agree_sub _ _ _ _ AG3); intros x Hx; cbn in Hx; lia) WM3) as FRp3.
pose proof (rw_cells_agree asegs m2 m3 _ _ FRva ltac:(apply (agree_sub _ _ _ _ AG3); intros x Hx; cbn in Hx; lia) WM3) as FRva3.
eapply evt_mono.
{ apply (fprintf_walkB usp (lo + 64) junk a2v a3v a4v a5v a6v a7v (Z_to_bv 64 0x5a4c0) ra gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 A)
(Z_to_bv 64 0xf7f30) b0 b1 b2 b3 b4 b5 b6 b7 s2 (Z_to_bv 64 (usp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 Ft fc3 m3
ST3 ltac:(lia) L3 FRp3 FRva3 MI3). }
intros ms4 ((w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & RS4) & ST4).
exists m3. split.
{ rewrite RS4. do 17 eexists. split; [reflexivity|]. intros _. exact FRM3. }
split.
{ apply (munch_merge [(usp - 2432, usp)] [(lo + 64, usp + -112); (0xf7f30, 0xf7f30 + 232)] _ m m2 m3 MU2 MU3).
intros x Hx. cbn in Hx |- *. intuition lia. }
split; [exact (wmono_trans asegs m m2 m3 WM2 WM3)|]. split; [exact MI3|]. split; [| exact ERR3].
apply (stk_merge asegs m3 lo (lo + 64) usp); [| exact ST4| lia].
exact (stk_transport_disjoint asegs _ _ _ _ _ ST2a MU3 WM3 ltac:(cbn [disjoint_from]; lia)).
Qed.

Lemma fp_tail_R : forall (m m2 : mem) (usp lo : Z) (g : word) (A : Z) (fmt : list Z) (args : list parg) (ps : list (list Z)) (r : Z)
(a2v a3v a4v a5v a6v a7v : word) (junk : list byte)
ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) fc,
munch [(usp - 2432, usp)] m m2 -> wmono asegs m m2 -> mem_inv asegs m2 ->
stk asegs m2 lo (usp + -112) -> 0x7fff7f800000 <= lo -> lo + 0x10000 <= usp -> usp <= 2^47 ->
rw_cells asegs m2 (usp + -112) (fpfr usp junk ra s0 s1 s2) ->
rw_cells asegs m2 (usp + -48) [C8 a2v; C8 a3v; C8 a4v; C8 a5v; C8 a6v; C8 a7v] ->
stderr_wfile0 m2 -> ssp_cells m2 g -> ictx m2 -> (forall p n, lo + 64 <= p -> p + n <= usp + -112 -> chkr m2 p n) ->
chkr m2 A (zlength fmt) -> rod_chk m2 ->
bytes_at asegs m2 A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
args_ok RSTDERR (usp + -112 - 352) 80 m2 lo (usp + -112) (usp + -112 - VF_FRAME) [a2v; a3v; a4v; a5v; a6v; a7v] args ->
printf_pieces fmt args = Some (ps, r) -> fp_calls (length fmt) fmt args = [] ->
65536 <= A -> A + zlength fmt <= STATIC_SPLIT -> Forall (fun p => zlength p <= OUT_MAX) ps ->
impl asegs (at_node asegs) (stderr_prog [] ps tt) (epost (fp_QfinR fc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m))
(MS (mkR (Z_to_bv 64 0x5a4c0) (Z_to_bv 64 (usp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 0xf7f30)
(Z_to_bv 64 0xf7f30) (Z_to_bv 64 A) (Z_to_bv 64 (usp + -48)) a3 a4 a5 a6 a7 (Z_to_bv 64 (usp + -48))
s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xe56bc) fc None m2 (seg_rom asegs)).
Proof using RIP.
intros until fc. intros MU2 WM2 MI2 ST2 LO0 LOR L3 FRp1 FRva ERR2 SSP2 IC2 STKC FMTC ROD BY HF P1 AOK PP FPC HA0 HA1 SZ.
destruct (frm0_dec fc) as [FRM|NFRM].
- exact (fp_tail_frm m m2 usp lo g A fmt args ps r a2v a3v a4v a5v a6v a7v junk ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc FRM MU2 WM2 MI2 ST2 LO0 LOR L3 FRp1 FRva ERR2 SSP2 IC2 STKC FMTC ROD BY HF P1 AOK PP FPC HA0 HA1 SZ).
- eapply impl_mono.
+ exact (fp_tail RIP m m2 usp lo g A fmt args ps r a2v a3v a4v a5v a6v a7v junk ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc MU2 WM2 MI2 ST2 LO0 LOR L3 FRp1 FRva ERR2 SSP2 IC2 STKC FMTC ROD BY HF P1 AOK PP FPC HA0 HA1 SZ).
+ intros [|[xr st']] ms' H; [exact H|]. cbn [epost fst snd] in H |- *.
destruct H as (m3 & (v & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & ->) & REST).
exists m3. split; [| exact REST]. do 17 eexists. split; [reflexivity|]. intros X. contradiction.
Qed.
End TailR.

Lemma tail_pieces_pfx1 : forall cnt p c body, 0 <= cnt -> 1 <= zlength body -> p <= zlength body -> cnt + 1 + zlength body <= INT_MAX ->
tail_pieces cnt 0 0 p [c] body = Some ([[c]; body], cnt + (1 + zlength body)).
Proof.
intros cnt p c body Hc Hb Hp HI. unfold tail_pieces. cbv zeta. change (zlength [c]) with 1.
replace (Z.max p (zlength body)) with (zlength body) by lia.
replace (INT_MAX - 1 <? zlength body) with false by (symmetry; apply Z.ltb_ge; lia).
replace (Z.max 0 (1 + zlength body)) with (1 + zlength body) by lia.
replace (INT_MAX - cnt <? 1 + zlength body) with false by (symmetry; apply Z.ltb_ge; lia).
unfold pad_pieces.
rewrite !Z.leb_refl. cbn [orb negb Z.land Z.lxor Z.lor Z.eqb Z.lnot ZERO_PAD LEFT_ADJ]. reflexivity.
Qed.

Definition int_ps (v : Z) : list (list Z) := if v =? 0 then [[]; [48]; []] else if v <? 0 then [[45]; dec_digits (- v)] else [[]; dec_digits v].
Definition int_len (v : Z) : Z := if v =? 0 then 1 else if v <? 0 then 1 + zlength (dec_digits (- v)) else zlength (dec_digits v).

Lemma conv_pieces_i : forall cnt v, 0 <= cnt -> - 2^31 <= v < 2^31 -> cnt + 21 <= INT_MAX ->
conv_pieces cnt {| d_fl := 0; d_w := 0; d_p := -1; d_xp := false; d_t := 100; d_ty := T_INT |} (PA_i v) = Some (int_ps v, cnt + int_len v).
Proof.
intros cnt v Hc Hv HI. unfold int_ps, int_len.
unfold conv_pieces. cbn [d_fl d_w d_p d_xp d_t d_ty].
change (Z.land 0 LEFT_ADJ =? 0) with true. cbv iota.
change (negb (T_INT =? T_INT)) with false. cbv iota.
change (negb (Z.land 0 MARK_POS =? 0)) with false. change (negb (Z.land 0 PAD_POS =? 0)) with false. cbv iota.
destruct (Z.eqb_spec v 0) as [->|NZ].
- change (0 mod 2 ^ 64) with 0. change (INTMAX_MAX <? 0) with false. cbv iota beta zeta.
unfold int_pieces. cbn [andb Z.eqb]. rewrite dec_digits_0. change (zlength (@nil Z)) with 0.
change (Z.max (-1) (0 + 1)) with 1. apply tail_pieces_zero1; lia.
- destruct (Z.ltb_spec v 0) as [NEG|POS].
+ replace (v mod 2^64) with (2^64 + v) by (symmetry; rewrite <- (Z.mod_small (2^64 + v) (2^64)) by lia; rewrite <- Z.add_mod_idemp_l, Z.mod_same by lia; reflexivity).
replace (INTMAX_MAX <? 2 ^ 64 + v) with true by (symmetry; apply Z.ltb_lt; unfold INTMAX_MAX; lia).
cbv iota beta zeta.
replace ((- (2 ^ 64 + v)) mod 2 ^ 64) with (- v).
2:{ symmetry. replace (- (2^64 + v)) with (- v + (-1) * 2^64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
pose proof (dec_digits_zlength (- v)) as DL. pose proof (dec_digits_nz (- v) ltac:(lia)) as NE.
assert (L1 : 1 <= zlength (dec_digits (- v))) by (destruct (dec_digits (- v)); [contradiction | unfold zlength; cbn; lia]).
unfold int_pieces. cbn [andb]. replace (- v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. rewrite Z.add_0_r.
rewrite tail_pieces_pfx1 by lia. reflexivity.
+ rewrite (Z.mod_small v (2^64)) by lia.
replace (INTMAX_MAX <? v) with false by (symmetry; apply Z.ltb_ge; unfold INTMAX_MAX; lia).
cbv iota beta zeta.
pose proof (dec_digits_zlength v) as DL. pose proof (dec_digits_nz v ltac:(lia)) as NE.
assert (L1 : 1 <= zlength (dec_digits v)) by (destruct (dec_digits v); [contradiction | unfold zlength; cbn; lia]).
unfold int_pieces. cbn [andb]. replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. rewrite Z.add_0_r.
rewrite tail_pieces_plain by lia. reflexivity.
Qed.
Lemma int_len_range : forall v, 0 <= int_len v <= 21.
Proof.
intros v. unfold int_len. pose proof (dec_digits_zlength v). pose proof (dec_digits_zlength (- v)).
destruct (v =? 0); [lia|]. destruct (v <? 0); lia.
Qed.

Definition FZ_NOTIFY : list Z := L_NOTIFY1 ++ [37; 115; 10; 0].
Definition FZ_WARN : list Z := L_WARN1 ++ [37; 115; 10; 0].
Definition FZ_WARNINT : list Z := L_WARN1 ++ [37; 115; 32; 37; 100; 10; 0].
Definition pieces_notify (s : list Z) : list (list Z) := [L_NOTIFY1; []; []; s; [10]].
Definition pieces_warn (s : list Z) : list (list Z) := [L_WARN1; []; []; s; [10]].
Definition pieces_warnint (s : list Z) (v : Z) : list (list Z) := [L_WARN1; []; []; s; [32]; []] ++ int_ps v ++ [[10]].

Lemma printf_pieces_notify : forall s, zlength s < INT_MAX - 256 ->
printf_pieces FZ_NOTIFY [PA_s s] = Some (pieces_notify s, 15 + zlength s).
Proof.
intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
change (Datatypes.length FZ_NOTIFY) with 18%nat.
ppl_step. ppl_step. rewrite conv_pieces_s by lia.
rewrite (ppl_noargs_shift 16 [10; 0] (14 + zlength s) [[10]] 1 ltac:(vm_compute; reflexivity)) by lia.
unfold pieces_notify. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.
Lemma printf_pieces_warn : forall s, zlength s < INT_MAX - 256 ->
printf_pieces FZ_WARN [PA_s s] = Some (pieces_warn s, 10 + zlength s).
Proof.
intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
change (Datatypes.length FZ_WARN) with 13%nat.
ppl_step. ppl_step. rewrite conv_pieces_s by lia.
rewrite (ppl_noargs_shift 11 [10; 0] (9 + zlength s) [[10]] 1 ltac:(vm_compute; reflexivity)) by lia.
unfold pieces_warn. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.
Lemma printf_pieces_warnint : forall s v, zlength s < 2^20 -> - 2^31 <= v < 2^31 ->
printf_pieces FZ_WARNINT [PA_s s; PA_i v] = Some (pieces_warnint s v, 9 + zlength s + 1 + int_len v + 1).
Proof.
intros s v Hs Hv. pose proof (zlength_nonneg' s) as H0. pose proof (int_len_range v) as IL. unfold printf_pieces.
change (Datatypes.length FZ_WARNINT) with 16%nat.
ppl_step. ppl_step. rewrite conv_pieces_s by (unfold INT_MAX; lia).
change [32; 37; 100; 10; 0] with ([32] ++ 37 :: [100; 10; 0]).
rewrite ppl_lit_cons; [ | discriminate | repeat (constructor; [lia|]); apply Forall_nil | right; split; [reflexivity | cbn; lia] | change (zlength [32]) with 1; unfold INT_MAX; lia ].
change (zlength [32]) with 1.
remember (9 + zlength s + 1) as c1 eqn:Ec1.
ppl_step. pose proof (conv_pieces_i c1 v ltac:(lia) Hv ltac:(unfold INT_MAX; lia)) as C2. cbv delta [T_INT] in C2. rewrite C2. clear C2.
rewrite (ppl_noargs_shift 12 [10; 0] (c1 + int_len v) [[10]] 1 ltac:(vm_compute; reflexivity)) by (unfold INT_MAX; lia).
unfold pieces_warnint. subst c1. cbn [app]. f_equal.
Qed.

Definition fpl_fmtz (k : fpl_kind) : list Z := match k with FLnotify => FZ_NOTIFY | FLwarn => FZ_WARN | FLwarn_int => FZ_WARNINT end.
Definition fpl_args (k : fpl_kind) (s : list Z) (v : Z) : list parg := match k with FLwarn_int => [PA_s s; PA_i v] | _ => [PA_s s] end.
Definition fpl_ps (k : fpl_kind) (s : list Z) (v : Z) : list (list Z) :=
match k with FLnotify => pieces_notify s | FLwarn => pieces_warn s | FLwarn_int => pieces_warnint s v end.
Definition fpl_r (k : fpl_kind) (s : list Z) (v : Z) : Z :=
match k with FLnotify => 15 + zlength s | FLwarn => 10 + zlength s | FLwarn_int => 9 + zlength s + 1 + int_len v + 1 end.

Lemma fpl_pieces : forall k s v, zlength s < 2^20 -> (k = FLwarn_int -> - 2^31 <= v < 2^31) ->
printf_pieces (fpl_fmtz k) (fpl_args k s v) = Some (fpl_ps k s v, fpl_r k s v).
Proof.
intros [| |] s v Hs Hv; cbn [fpl_fmtz fpl_args fpl_ps fpl_r].
- apply printf_pieces_notify. unfold INT_MAX. lia.
- apply printf_pieces_warn. unfold INT_MAX. lia.
- apply printf_pieces_warnint; [exact Hs | exact (Hv eq_refl)].
Qed.
Lemma fpl_pass1 : forall k, pass1_ok (fpl_fmtz k) = true. Proof. intros [| |]; vm_compute; reflexivity. Qed.
Lemma fpl_fp_calls : forall k s v, fp_calls (length (fpl_fmtz k)) (fpl_fmtz k) (fpl_args k s v) = [].
Proof. intros [| |] s v; vm_compute; reflexivity. Qed.
Lemma fpl_fmtz_bytes : forall k, Forall (fun c => 0 <= c < 256) (fpl_fmtz k).
Proof. intros [| |]; apply Forall_byte_of_forallb; vm_compute; reflexivity. Qed.
Lemma concat_int_ps : forall v, concat (int_ps v) = fpl_int v.
Proof. intros v. unfold int_ps, fpl_int. destruct (v =? 0); [reflexivity|]. destruct (v <? 0); cbn [concat app]; rewrite ?app_nil_r; reflexivity. Qed.
Lemma concat_fpl_ps : forall k (str : list byte) v, concat (fpl_ps k (map bv_unsigned str) v) = fpl_msg k str v.
Proof.
intros [| |] str v; cbn [fpl_ps fpl_msg]; unfold pieces_notify, pieces_warn, pieces_warnint.
- cbn [concat app]. rewrite ?app_nil_r. reflexivity.
- cbn [concat app]. rewrite ?app_nil_r. reflexivity.
- rewrite !concat_app. rewrite concat_int_ps. cbn [concat app]. rewrite ?app_nil_r.
unfold FPL_WARN, L_WARN1. cbn [app]. rewrite <- ?app_assoc. reflexivity.
Qed.
Lemma fpl_ps_small : forall k s v, zlength s <= 2^20 -> Forall (fun p => zlength p <= OUT_MAX) (fpl_ps k s v).
Proof.
intros k s v Hs. pose proof (dec_digits_zlength v) as D1. pose proof (dec_digits_zlength (- v)) as D2.
assert (HI : Forall (fun p => zlength p <= OUT_MAX) (int_ps v)).
{ unfold int_ps. destruct (v =? 0); [| destruct (v <? 0)]; repeat constructor; unfold OUT_MAX, zlength in *; cbn [length]; lia. }
destruct k; cbn [fpl_ps]; unfold pieces_notify, pieces_warn, pieces_warnint.
- repeat constructor; unfold OUT_MAX, zlength in *; cbn; lia.
- repeat constructor; unfold OUT_MAX, zlength in *; cbn; lia.
- apply Forall_app. split; [repeat constructor; unfold OUT_MAX, zlength in *; cbn; lia|].
apply Forall_app. split; [exact HI|]. repeat constructor; unfold OUT_MAX, zlength; cbn; lia.
Qed.
Lemma fpl_msg_len : forall k (str : list byte) v, zlength (fpl_msg k str v) <= Z.of_nat (length str) + 64.
Proof.
intros k str v. rewrite <- concat_fpl_ps.
pose proof (dec_digits_zlength v) as D1. pose proof (dec_digits_zlength (- v)) as D2.
assert (HI : zlength (concat (int_ps v)) <= 21).
{ unfold int_ps. destruct (v =? 0); [| destruct (v <? 0)]; cbn [concat app]; rewrite ?app_nil_r; unfold zlength in *; cbn [length]; lia. }
destruct k; cbn [fpl_ps]; unfold pieces_notify, pieces_warn, pieces_warnint.
- cbn [concat app]. unfold zlength. rewrite ?length_app, ?length_map. cbn [length L_NOTIFY1]. lia.
- cbn [concat app]. unfold zlength. rewrite ?length_app, ?length_map. cbn [length L_WARN1]. lia.
- rewrite !concat_app. unfold zlength in *. rewrite ?length_app. cbn [concat app length L_WARN1]. rewrite ?length_app, ?length_map. cbn [length]. lia.
Qed.

Fixpoint img_ok_b (A : Z) (n : nat) : bool :=
match n with
| O => true
| S n' => match seg_rom asegs (wa A) with Some _ => img_ok_b (A + 1) n' | None => false end
end.
Lemma img_ok_b_sound : forall n A (m : mem), 0 <= A -> A + Z.of_nat n <= 2^64 -> img_ok_b A n = true -> exists bs, length bs = n /\ bytes_at asegs m A bs.
Proof.
induction n as [|n IH]; intros A m HA HB H; cbn [img_ok_b] in H.
- exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
- destruct (seg_rom asegs (wa A)) as [b0|] eqn:E; [| discriminate].
destruct (IH (A + 1) m ltac:(lia) ltac:(lia) H) as (bs & L & BY).
assert (RD : exists b, mrd asegs m (wa A) = Some b) by (unfold mrd; destruct (m (wa A)) as [b1|]; [exists b1; reflexivity | exists b0; exact E]).
destruct RD as (b & RD). exists (b :: bs). split; [cbn; lia|].
change (b :: bs) with ([b] ++ bs). apply (proj2 (bytes_at_app asegs m A [b] bs)). split; [| exact BY].
split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. assert (i = 0%nat) by lia. subst i. rewrite Z.add_0_r. exact RD.
Qed.

Definition lit_ok_b (r : Z * Z) : bool :=
(0x23260 <=? fst r) && (fst r + snd r <=? 0xf0818) && (0 <? snd r) && (snd r <=? 1280) && img_ok_b (fst r) (Z.to_nat (snd r) + 7).
Lemma acc_lits_ok : forallb lit_ok_b ACC_LITS = true.
Proof. vm_compute. reflexivity. Qed.

Lemma acc_lits_range : forall sa n, In (sa, n) ACC_LITS -> 0x23260 <= sa /\ sa + n <= 0xf0818 /\ 0 < n <= 1280.
Proof.
intros sa n H. pose proof (proj1 (forallb_forall _ _) acc_lits_ok _ H) as B. unfold lit_ok_b in B. cbn [fst snd] in B.
repeat (apply andb_prop in B; destruct B as [B ?]). lia.
Qed.

Lemma acc_lits_slack : forall m sa n o, mem_inv asegs m -> In (sa, n) ACC_LITS -> 0 <= o <= n ->
exists slack, bytes_at asegs m (sa + o) slack /\ (- (sa + o)) mod 8 <= Z.of_nat (length slack) /\ Z.of_nat (length slack) <= 7.
Proof.
intros m sa n o MI H Ho. pose proof (acc_lits_range sa n H) as R.
pose proof (proj1 (forallb_forall _ _) acc_lits_ok _ H) as B. unfold lit_ok_b in B. cbn [fst snd] in B.
apply andb_prop in B. destruct B as [_ B]. destruct (img_ok_b_sound (Z.to_nat n + 7) sa m ltac:(lia) ltac:(lia) B) as (bs & L & BY).
pose proof (Z.mod_pos_bound (- (sa + o)) 8 ltac:(lia)) as K.
exists (firstn (Z.to_nat ((- (sa + o)) mod 8)) (skipn (Z.to_nat o) bs)).
assert (LS : length (firstn (Z.to_nat ((- (sa + o)) mod 8)) (skipn (Z.to_nat o) bs)) = Z.to_nat ((- (sa + o)) mod 8)).
{ rewrite firstn_length, skipn_length, L. lia. }
split; [| rewrite LS; lia].
replace (sa + o) with (sa + Z.of_nat (Z.to_nat o)) at 1 by lia. apply bytes_at_sub'; [exact BY | rewrite L; lia].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Lemma pcom_lib_spec : forall (k : fpl_kind) (A : Z), In A (fpl_fmts k) ->
forall (lo : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (ap S : Z) (str : list byte),
a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 ap ->
ro_cells asegs m ap [C8 (Z_to_bv 64 S)] -> bv_unsigned sp <= ap -> ap + 16 < 2^63 ->
cstr_at m S str -> 0 < S -> (S + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= S) -> S + Z.of_nat (length str) + 1 < 2^47 ->
chk_ok m S (Z.of_nat (length str) + 1) ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp <= 2^47 ->
bv_unsigned sp mod 16 = 0 -> chk_ok m A (zlength (fpl_fmtz k)) -> pctx m -> mem_inv asegs m ->
evt asegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x5956c) fc None m (seg_rom asegs)).
Proof using RIP.
intros k A HA. intros until str. intros E1 E2 SLOT QAP APH CSS S0 SSEP SH CHKS ST LO LOLO SPH S16 CHK PCX MI.
destruct k; cbn [fpl_fmts fpl_fmtz] in HA, CHK.
- eapply (pcom_notify_spec RIP A HA); try eassumption. lia.
- destruct HA as [<-|[]]. eapply (pcom_warn_spec RIP); try eassumption. lia.
- assert (HR : 0 <= A < 2^20) by (destruct HA as [<-|[<-|[<-|[<-|[]]]]]; lia).
eapply (pcom_fstrint_spec RIP A L_WARN1 ap S str lo); try eassumption.
+ reflexivity.
+ exact (cstr_f_warnint A HA m MI).
+ unfold kHighShadowEnd in LOLO. cbn [length L_WARN1 Z.of_nat]. lia.
Qed.
End WithRIP.

Section XFprintfLib.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.
Hypothesis AF_PF : forall Σ m, ART RT Σ m -> pf_consts m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.

Lemma fpl_fmt_lit : forall k fmt, In fmt (fpl_fmts k) -> In (fmt, zlength (fpl_fmtz k)) ACC_LITS /\ 0x23540 <= fmt <= 0x272c0.
Proof.
intros [| |] fmt H; cbn [fpl_fmts fpl_fmtz] in *.
- destruct H as [<-|[<-|[<-|[<-|[]]]]]; (split; [unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | lia]).
- destruct H as [<-|[]]; (split; [unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | lia]).
- destruct H as [<-|[<-|[<-|[<-|[]]]]]; (split; [unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | lia]).
Qed.
Lemma fpl_fmt_bytes : forall k fmt m, In fmt (fpl_fmts k) -> mem_inv asegs m -> bytes_at asegs m fmt (zb (fpl_fmtz k)).
Proof.
intros [| |] fmt m H MI; cbn [fpl_fmts fpl_fmtz] in *.
- destruct H as [<-|[<-|[<-|[<-|[]]]]]; (apply img_bytes; [assumption | lia | cbn; lia | vm_compute; reflexivity]).
- destruct H as [<-|[]]; (apply img_bytes; [assumption | lia | cbn; lia | vm_compute; reflexivity]).
- destruct H as [<-|[<-|[<-|[<-|[]]]]]; (apply img_bytes; [assumption | lia | cbn; lia | vm_compute; reflexivity]).
Qed.
Lemma fpl_fmtz_len : forall k, 13 <= zlength (fpl_fmtz k) <= 18. Proof. intros [| |]; vm_compute; split; discriminate. Qed.

Theorem fprintf_lib_ok : fprintf_lib_icontract RT OUT_repA ERR_repA IO_FPA.
Proof using AF RIP AF_SHW AF_PF.
intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m k fmt sa v str errp lo
Ha0 Ha1 Ha2 Ha3 Herrp HFMT (n & HLIT & HLEN) BYs NZ HFD ERR0 (g & SG1 & SG2) ART0 MI0 CALL POIS.
subst a0 a1 a2 errp. intros T c' Hc Hk.
pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
destruct CALL as (ST & LOW & LOR & SPT & SPA).
set (usp := bv_unsigned sp) in *.
pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
rewrite ESP in Hc.
destruct (AF_PF Σ m ART0) as (PFC & IC & ACCF & ACCP & ACCX & ACCN & ACCU & ACCO & ACCR & ACCT).
assert (LO0 : 0x7fff7f800000 <= lo) by ul.
assert (L3 : usp <= 2^47) by ul.
assert (PCX : pctx m).
{ destruct IC as ((G2 & G1 & RM & SHC & RI) & _ & _ & M2S). split; [exact M2S| split; assumption]. }

pose proof (acc_lits_range sa n HLIT) as RS.
destruct (fpl_fmt_lit k fmt HFMT) as (FLIT & RF). pose proof (fpl_fmtz_len k) as FZL.
pose proof (af_acc_lits RT AF Σ m ART0) as ACL. rewrite Forall_forall in ACL.
pose proof (ACL _ HLIT) as ACS. pose proof (ACL _ FLIT) as ACFM. cbn [fst snd] in ACS, ACFM. clear ACL.
set (len := Z.of_nat (length str)) in *.
assert (LEN0 : 0 <= len) by (unfold len; lia).
assert (ACS1 : acc asegs m sa (len + 1)) by (apply (acc_sub asegs m sa n sa (len + 1) ACS); lia).
assert (CHKS : chk_ok m sa (len + 1)).
{ apply (chk_ok_of RT AF_SHW Σ m _ _ ART0); [lia|]. intros _. split; [exact ACS1|]. right; right; right. ul. }
assert (CHKF : chk_ok m fmt (zlength (fpl_fmtz k))).
{ apply (chk_ok_of RT AF_SHW Σ m _ _ ART0); [lia|]. intros _. split; [exact ACFM|]. right; right; right. ul. }
destruct (acc_lits_slack m sa n (len + 1) MI0 HLIT ltac:(lia)) as (slack & SLK & SLKM & SLK7).
set (sZ := map bv_unsigned str).
assert (EZL : zlength sZ = len) by (unfold zlength, sZ, len; rewrite length_map; reflexivity).

set (Qfin := fp_QfinR fc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp lo m).
assert (IMPL : impl asegs (at_node asegs) (stderr_prog [] (fpl_ps k sZ v) tt) (epost Qfin)
(entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STDERR_FILE) (Z_to_bv 64 fmt)
(Z_to_bv 64 sa) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fprintf m)).
{ eapply impl_evt with (P := fun ms' => impl asegs (at_node asegs) (stderr_prog [] (fpl_ps k sZ v) tt) (epost Qfin) ms');
[| intros ms' H; exact H].
eapply evt_cut; [exact (fprintf_walkA1 usp lo ra gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STDERR_FILE) (Z_to_bv 64 fmt)
(Z_to_bv 64 sa) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
ST ltac:(ul) ltac:(ul) L3 PFC MI0)|].
intros ms1 (m1 & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & junk & -> & MU1 & WM1 & MI1 & ST1 & FRp1 & FRva).
assert (AG1 : agree_on (fun x => x < usp - 128 \/ usp <= x) m m1).
{ apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn. split; [lia| exact I]. }
assert (EU112 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; ul).
assert (PCX1 : pctx m1) by (apply (pctx_munch _ m m1 PCX MU1 WM1); intros ?x ?Hx; unfold in_PCR in Hx; cbn [outside]; ul).
assert (CHM : forall p n, chk_ok m p n -> 0 <= p -> p + n <= 2^47 -> chk_ok m1 p n).
{ intros p n0 H Hp1 Hp2. apply (chk_ok_agree m m1 p n0 H Hp1 Hp2). apply (agree_sub _ _ _ _ AG1). intros x Hx. ul. }
pose proof (munch_weaken [(usp - 128, usp)] [(usp - 2432, usp)] m m1 ltac:(unfold sub_fp; cbn [outside]; intros; lia) MU1) as MUacc.
clear MU1.
assert (ERR1 : stderr_wfile0 m1) by (apply (stderr_wfile0_agree m m1); [apply (agree_sub _ _ _ _ AG1); intros x Hx; ul| exact WM1| exact ERR0]).
assert (SSP1 : ssp_cells m1 g).
{ split.
- apply (ro_cells_agree asegs m m1 _ _ SG1). apply (agree_sub _ _ _ _ AG1). intros x Hx. cbn in Hx. ul.
- apply (ro_cells_agree asegs m m1 _ _ SG2). apply (agree_sub _ _ _ _ AG1). intros x Hx. cbn in Hx. ul. }
assert (IC1 : ictx m1) by (apply (ictx_munch _ m m1 IC MUacc WM1); intros ?x ?Hx; cbn [in_rl ICR outside] in *; ul).
assert (PFC1 : pfcells m1) by (apply (pfcells_munch _ m m1 PFC MUacc WM1); intros ?x ?Hx; unfold in_PFR in Hx; cbn [outside]; ul).
pose proof (bytes_at_bound _ _ _ _ BYs) as BYB. rewrite length_app in BYB. cbn [length] in BYB.
assert (CS1 : cstr_at m1 sa str).
{ split; [| exact NZ]. apply (bytes_at_agree asegs m m1 _ _ BYs). apply (agree_sub _ _ _ _ AG1). intros x Hx.
rewrite length_app in Hx; cbn [length] in Hx. ul. }
assert (SLOT1 : ro_cells asegs m1 (usp + -48) [C8 (Z_to_bv 64 sa)]).
{ pose proof (proj1 (X023.rw_cells_app asegs _ _ [_] _) FRva) as (H & _). exact (proj1 H). }
call (pcom_lib_spec RIP k fmt HFMT lo);
[ reflexivity | reflexivity | exact SLOT1 | rewrite EU112; lia | ul | exact CS1 | ul | left; fold len; ul | fold len; ul
| apply CHM; [exact CHKS| lia| ul] | rewrite EU112; exact ST1 | rewrite EU112; ul | unfold kHighShadowEnd; ul
| rewrite EU112; ul | rewrite EU112; Z.div_mod_to_equations; lia
| apply CHM; [exact CHKF| lia| ul]
| exact PCX1 | exact MI1 | ].
rename POST into ST2. rewrite EU112 in ST2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (PFC2 : pfcells mm) by (apply (pfcells_munch _ m mm PFC MUacc ltac:(assumption)); intros ?x ?Hx; unfold in_PFR in Hx; cbn [outside]; ul) end.
destruct PFC2 as (_ & _ & _ & _ & RVF2).
eapply evt_cut; [apply (fprintf_walkA2 usp junk ra s0 s1 s2); [exact FRp1| exact RVF2| exact L3| ul| assumption]|].
intros ms2 (a3'' & ->).
apply evt_done.
lazymatch goal with |- impl _ _ _ _ (MS _ _ _ _ _ ?mm _) => set (m2 := mm) in * end.
assert (CHR : forall p n, chkr m p n -> chkr m2 p n).
{ intros p n0 H. apply (chkr_munch _ m m2 p n0 H MUacc). intros y Hy. cbn [outside]. unfold SHADOW_LO, SHADOW_HI in Hy. ul. }
assert (AG2 : agree_on (fun x => x < usp - 2432 \/ usp <= x) m m2).
{ apply (agree_of_munch _ _ _ _ MUacc). intros y Hy. cbn. split; [lia| exact I]. }
eapply (fp_tail_R RIP m m2 usp lo g fmt (fpl_fmtz k) (fpl_args k sZ v) (fpl_ps k sZ v) (fpl_r k sZ v)).
+ exact MUacc.
+ assumption.
+ assumption.
+ exact ST2.
+ exact LO0.
+ ul.
+ exact L3.
+ exact FRp1.
+ exact FRva.
+ apply (stderr_wfile0_agree m m2); [apply (agree_sub _ _ _ _ AG2); intros y Hy; ul| assumption| exact ERR0].
+ split.
* apply (ro_cells_agree asegs m m2 _ _ SG1). apply (agree_sub _ _ _ _ AG2). intros y Hy. cbn in Hy. ul.
* apply (ro_cells_agree asegs m m2 _ _ SG2). apply (agree_sub _ _ _ _ AG2). intros y Hy. cbn in Hy. ul.
+ apply (ictx_munch _ m m2 IC MUacc ltac:(assumption)); intros ?y ?Hy; cbn [in_rl ICR outside] in *; ul.
+ intros p n0 H1 H2. apply CHR. destruct (Z_lt_le_dec 0 n0) as [NP|NN].
* apply (chkr_of RT AF_SHW Σ m p n0 ART0); [ul| | ].
-- apply (af_acc_stack RT AF Σ m p n0 ART0); [ul | ul | apply (pois_apart_above _ _ _ _ POIS); ul].
-- right; right; left. ul.
* split; [intros i Hi; lia| split; [intros i Hi; lia|]]. split; [| lia]. unfold region_in_mem, kLowMemEnd, kHighMemEnd. right. ul.
+ apply CHR. apply (chkr_of RT AF_SHW Σ m _ _ ART0); [lia| exact ACFM| right; right; right; ul].
+ split; [| split]; apply CHR; (apply (chkr_of RT AF_SHW Σ m _ _ ART0); [lia| assumption| right; right; right; unfold PFX_A, XDIG_A, NULLS_A; ul]).
+ apply (bytes_at_agree asegs m m2 _ _ (fpl_fmt_bytes k fmt m HFMT MI0)). apply (agree_sub _ _ _ _ AG2). intros y Hy.
unfold zb in Hy. rewrite length_map in Hy. unfold zlength in FZL. ul.
+ exact (fpl_fmtz_bytes k).
+ exact (fpl_pass1 k).
+ assert (AS : arg_ok RSTDERR (usp + -112 - 352) 80 m2 lo (usp + -112) (usp + -112 - VF_FRAME) (Z_to_bv 64 sa) (PA_s sZ)).
{ cbn [arg_ok]. exists slack. rewrite (unsigned_lit sa) by ul. unfold sZ at 1. rewrite map_to_bytes_unsigned'. rewrite EZL.
split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
* apply (proj2 (bytes_at_app asegs m2 sa str (Z_to_bv 8 0 :: slack))). split.
-- apply (bytes_at_agree asegs m m2 _ _ (proj1 (proj1 (bytes_at_app asegs m sa str [Z_to_bv 8 0]) BYs))).
apply (agree_sub _ _ _ _ AG2). intros y Hy. fold len in Hy. ul.
-- apply (proj2 (bytes_at_app asegs m2 _ [Z_to_bv 8 0] slack)). split.
++ apply (bytes_at_agree asegs m m2 _ _ (proj2 (proj1 (bytes_at_app asegs m sa str [Z_to_bv 8 0]) BYs))).
apply (agree_sub _ _ _ _ AG2). intros y Hy. cbn [length] in Hy. fold len in Hy. ul.
++ cbn [length]. fold len. replace (sa + len + Z.of_nat 1) with (sa + (len + 1)) by lia.
apply (bytes_at_agree asegs m m2 _ _ SLK). apply (agree_sub _ _ _ _ AG2). intros y Hy. ul.
* apply Forall_forall. intros zc Hzc. apply in_map_iff in Hzc. destruct Hzc as (b & <- & Hb).
pose proof (bv_unsigned_in_range 8 b) as RB. unfold bv_modulus in RB. change (2 ^ Z.of_N 8) with 256 in RB.
split; [| lia]. destruct (Z.eq_dec (bv_unsigned b) 0) as [E0|E0]; [| lia].
exfalso. apply NZ. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E0. reflexivity.
* unfold zlength. replace (sa + len + 1) with (sa + (len + 1)) by lia. exact SLKM.
* ul.
* left. unfold zlength. ul.
* left. unfold zlength. ul.
* left. unfold zlength. ul.
* left. unfold zlength, VF_FRAME. ul.
* apply CHR. apply (chkr_of RT AF_SHW Σ m _ _ ART0); [ul| exact ACS1 | right; right; right; ul]. }
destruct k; cbn [fpl_args args_ok]; (split; [exact AS|]); try exact I.
split; [| exact I]. destruct (Ha3 eq_refl) as (-> & RV). cbn [arg_ok]. split; [exact RV|].
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). Z.div_mod_to_equations. lia.
+ apply fpl_pieces; [rewrite EZL; lia|]. intros ->. exact (proj2 (Ha3 eq_refl)).
+ apply fpl_fp_calls.
+ lia.
+ unfold STATIC_SPLIT. lia.
+ apply fpl_ps_small. rewrite EZL. lia. }
assert (MSGB : zlength (fpl_msg k str v) <= 2^26).
{ pose proof (fpl_msg_len k str v). fold len in H. lia. }
assert (TOK : tok [2] (stderr_prog [] (fpl_ps k sZ v) tt)).
{ apply tok_stderr_fprintf. cbn [app]. unfold sZ. rewrite concat_fpl_ps. exact MSGB. }
assert (RZ : realizes asegs c' (TT (stderr_prog [] (fpl_ps k sZ v) tt) (fun _ => t_emit [] T))).
{ apply (impl_realizes asegs SEGTOP_A asegs_wx asegs_below [2] _ (rt_allow RT Σ) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo)
Qfin (fun _ => t_emit [] T)
(entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STDERR_FILE) (Z_to_bv 64 fmt)
(Z_to_bv 64 sa) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fprintf m) c'
(ASTA_PM_mat_stable RT AF Σ F0 fs0)); [| exact TOK| exact Hc| exact IMPL|].
- intros mo fd (HAR & HF & _) Hin. cbn in Hin. destruct Hin as [<-|[]]. rewrite HF. exact HFD.
- intros x ms' c2 HQ Hc2.
assert (R : realizes asegs c2 T).
{ apply Hk. eapply ASTA_conseq; [exact Hc2|]. intros ms <-.
destruct HQ as (m3 & (r & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & -> & FRMK)
& MU3 & WM3 & MI3 & ST3 & ERR3).
exists r, m3. split.
{ rewrite ESP. do 16 eexists. split; [reflexivity | exact FRMK]. }
split; [split; [| split; [exact MI3| split; [exact WM3| exact ST3]]]|].
- apply (af_frame RT AF Σ m m3 lo ART0); [ul| | exact WM3].
intros a Ha. apply MU3. cbn. split; [intros Hin; apply Ha; left; ul|].
split; [intros Hin; apply Ha; right; left; apply client_static_intro; lia| exact I].
- split; [| split].
+ intros a Ha Hout. apply MU3. cbn in Hout |- *. destruct Hout as (O1 & O2 & O3 & _). split; [| split; [lia| exact I]].
destruct (aclient_split RT AF Σ m usp _ ART0 Ha); ul.
+ exact ERR3.
+ intros so OUT0. apply (stdout_file_agree so m m3); [| exact WM3| exact OUT0].
apply (agree_of_munch _ _ _ _ MU3). intros y Hy. cbn. split; [ul| split; [lia| exact I]]. }
eapply rz_conseq; [exact R|]. apply t_eq_sym, t_emit_nil_eq. exact (realizes_nonempty asegs _ _ R). }
eapply rz_conseq; [exact RZ|].
eapply t_eq_trans; [apply (TT_stderr_fprintf (fpl_ps k sZ v) [] tt (fun _ => t_emit [] T)); [cbn [app]; unfold sZ; rewrite concat_fpl_ps; exact MSGB| apply t_emit_has_nil]|].
cbn [app]. unfold sZ. rewrite concat_fpl_ps.
eapply t_eq_trans; [apply t_eq_sym, t_emit_app|]. rewrite app_nil_r. apply t_eq_refl.
Qed.
End XFprintfLib.
