(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1sa.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s
X09u X0ae X09j X09m X09p X0ab X0a8 X0ad.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0wl X110 X106 X109 X10c X10x X10u X10z.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X106 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X109 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10u OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10z.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments skipn {A} n l : simpl nomatch.
#[local] Arguments firstn {A} n l : simpl nomatch.

Lemma memchr_chk_le : forall c n (buf : list byte), 0 <= n -> 0 <= X058.memchr_chk c n buf <= n.
Proof.
intros c n buf Hn. unfold X058.memchr_chk. destruct (X1sa.find_byte c (firstn (Z.to_nat n) buf)) as [i|] eqn:E; [| lia].
pose proof (X1sa.find_byte_Some _ _ _ E) as (Hi & _). rewrite length_firstn in Hi. lia.
Qed.

Section OggPageseekCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MCHR : memchr_icontract RT.

Definition ogg_sync_pageseek_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A G D f lo : Z) (k : nat) (sy : sync_st bptr) (bytes j0 j1 j2 j3 : list byte) r ogo (sy' : sync_st bptr),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 G -> tp = Z_to_bv 64 0x638c98 ->
sync_rep m A D sy bytes -> sync_inv2 sy -> 0 < A -> 0 < G -> sync_live RT Σ sy D ->
rw_cells bsegs m G [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3] ->
ogg_sync_pageseek sy = ((r, ogo), sy') ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 32 <= f + fs_size k - 8 -> f <= G -> G + 32 <= f + fs_size k - 8 -> (A + 32 <= G \/ G + 32 <= A) ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 128 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_ogg_sync_pageseek m)))
(ASTA RT Σ PMc (fun ms => exists m',
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz r) m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 32); (G, G + 32); (D, D + Z.of_nat (length bytes))] m m'
/\ sync_rep m' A D sy' bytes
/\ rw_cells bsegs m' G (og_cells D ogo [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3]))).

Theorem ogg_sync_pageseek_ok : ogg_sync_pageseek_cps.
Proof using AF MCHR.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A G D f lo k sy bytes j0 j1 j2 j3 r ogo sy'
FDO MST -> -> -> REP INV2 A0 G0 INL OG RES INF FA1 FA2 FG1 FG2 SEP_AG ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & F64 & FIMG & _ & _ & _ & _ & _ & _ & _).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
destruct REP as (SY & FOK & DAT & SEP).
pose proof (ogg_sync_pageseek_inv sy r ogo sy' (proj1 INV2) RES) as (INV' & EFILL & EBUF & EDATA & ESTO & _).
assert (SEPfA : A + 32 <= lo \/ usp <= A) by (left; clear - FA2 BF1; lia).
assert (SEPfG : G + 32 <= lo \/ usp <= G) by (left; clear - FG2 BF1; lia).
assert (LO128 : lo + 128 <= usp) by (clear - LOR; unfold RT_STACK in *; lia).
assert (EUSP : bv_unsigned sp = usp) by reflexivity.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
unfold sync_data in DAT. unfold sync_live in INL.
destruct (sy_data sy) as [p|] eqn:ED.
-
destruct DAT as (D0 & ARR & LEN & PRE1 & LE). specialize (INL ltac:(intros X; discriminate X)).
destruct (live_below_lo RT AF Σ m D (sy_storage sy) lo ART0 INL LOW) as (_ & BD1 & _).
destruct (frame_live_apart RT AF Σ m f k D (sy_storage sy) ART0 INF INL) as (FLD & _).
assert (DLO : D + Z.of_nat (length bytes) <= lo) by (rewrite LEN; exact BD1).
assert (SEP_AD : A + 32 <= D \/ D + Z.of_nat (length bytes) <= A) by (rewrite LEN; clear - FLD FA1 FA2; lia).
assert (SEP_GD : G + 32 <= D \/ D + Z.of_nat (length bytes) <= G) by (rewrite LEN; clear - FLD FG1 FG2; lia).
assert (TOPD : D + Z.of_nat (length bytes) < 2^63) by (clear - DLO LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (SEPfD : D + Z.of_nat (length bytes) <= lo \/ usp <= D) by (left; exact DLO).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(A, A + 32); (G, G + 32); (D, D + Z.of_nat (length bytes))] m) as PF.
refine (rz_evt RT AF Σ PMc _ _ T c MST Hc
(ogg_sync_pageseek_spec A G D lo bytes sy j0 j1 j2 j3 ra sp gp _ t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m r ogo sy' FOK INV2 (conj PRE1 LE) LEN ltac:(lia) TOPD A0 G0 LO128 SEPfA SEPfG SEPfD SEP_AG SEP_AD SEP_GD ST0 MI0 SY ARR OG RES eq_refl eq_refl) _).
intros ms1 c1 POST Hc1. clear Hc.
destruct POST as [FIN | (-> & CUT)].
+
destruct FIN as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1 & SY1 & FOK1 & ARR1 & OG1).
rewrite EUSP in MU1, ST1. replace (usp - 128) with (usp + -128) in MU1 by lia.
cps_norm.
clear SY OG ARR. cps_seg_post.
apply Hk.
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m1.
split; [unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split. { split; [assumption|]. split; [exact MI1|]. split; [exact WM1| exact ST1]. }
split; [exact PF|].
split; [| exact OG1].
split; [exact SY1|]. split; [exact FOK1|]. split; [| exact SEP].
unfold sync_data. rewrite EDATA, EBUF, ESTO. exact (conj D0 (conj ARR1 (conj LEN (conj PRE1 LE)))).
+
destruct CUT as (mc & loc & sy1 & x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & -> & MU1 & WM1 & MI1 & ST1 & SZ & FR & SYc & FOK1 & ARR1 & OG1 & EB & Hb & Hf & RESF).
fold usp in MU1, ST1, FR, Hc1. replace (usp - 128) with (usp + -128) in MU1 by lia.
set (ret1 := sy_returned sy1) in *. set (fill1 := sy_fill sy1) in *.
pose proof FOK1 as (Fs & Ff & Fr & Fu & Fh & Fbb). unfold int31 in Fs, Ff, Fr, Fu, Fh, Fbb. fold ret1 fill1 in Ff, Fr.
unfold zlength in Hf.
assert (BY1 : bytes_at bsegs mc D bytes) by exact (proj1 ARR1).
apply u8arr_rw_CB in ARR1.
set (n1 := fill1 - ret1 + -1) in *.
set (buf := firstn (Z.to_nat n1) (skipn (Z.to_nat (ret1 + 1)) bytes)).
assert (LBUF : Z.of_nat (length buf) = n1) by (unfold buf; rewrite firstn_length_le by (rewrite length_skipn; unfold n1; lia); unfold n1; lia).
pose proof (bytes_at_sub mc D bytes (Z.to_nat (ret1 + 1)) (Z.to_nat n1) BY1 ltac:(unfold n1; lia)) as BYS. fold buf in BYS.
replace (D + Z.of_nat (Z.to_nat (ret1 + 1))) with (D + ret1 + 1) in BYS by lia.
cps_norm.
clear SY OG ARR BY1. cps_seg_post.
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -96)) = usp + -96) by (apply unsigned_lit; ulc).
cps_rt (MCHR Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc (D + ret1 + 1) 79 n1 buf lo).
all: [> lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- memchr_ok _ _ _ _ => unfold memchr_ok; rewrite LBUF; destruct (X1sa.find_byte 79 (firstn (Z.to_nat n1) buf)); lia
| |- checked_src _ _ _ _ _ _ _ =>
pose proof (memchr_chk_le 79 n1 buf ltac:(unfold n1; lia)) as CHK;
apply (live_checked_src RT AF Σ mc _ lo D (sy_storage sy)); [exact ART| exact INL| lia| unfold n1 in *; lia| exact BD1]
| |- _ \/ _ => left; rewrite LBUF; unfold n1; lia
| |- _ => first [ exact BYS | unfold n1; lia ]
end .. | ].
intros kc2 Hc2. unfold icpt_postF in Hc2.
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & _).

assert (MODEL : exists next, ((memchr_res (D + ret1 + 1) 79 n1 buf = 0 /\ D + next = D + fill1) \/
(memchr_res (D + ret1 + 1) 79 n1 buf = D + next /\ D + ret1 < D + next < D + fill1))
/\ r = - (next - ret1)
/\ sy' = mkSync (sy_data sy1) (sy_buf sy) (sy_storage sy1) fill1 next (sy_unsynced sy1) 0 0).
{ unfold sync_fail in RESF. fold fill1 in RESF. rewrite EB in RESF.
rewrite (pre_zslice (sy_buf sy) bytes (ret1 + 1) (fill1 - ret1 - 1) (conj PRE1 LE)) in RESF by lia.
rewrite find_byte_bridge in RESF. change CHAR_O with 79 in RESF.
replace (fill1 - ret1 - 1) with n1 in RESF by (unfold n1; lia). fold buf in RESF.
unfold memchr_res. replace (firstn (Z.to_nat n1) buf) with buf by (unfold buf; rewrite firstn_firstn, Nat.min_id; reflexivity).
destruct (X1sa.find_byte 79 buf) as [j|] eqn:FBt.
- pose proof (X1sa.find_byte_Some _ _ _ FBt) as (Hj & _).
exists (ret1 + 1 + Z.of_nat j). injection RESF as <- <-. split; [right; split; [lia| unfold n1 in *; lia]|]. split; reflexivity.
- exists fill1. injection RESF as <- <-. split; [left; split; reflexivity|]. split; reflexivity. }
destruct MODEL as (next & CASE & -> & ->).
cps_hide.
cps_seg (ps_tail A G D (sy_storage sy1) fill1 ret1 (sy_unsynced sy1) (memchr_res (D + ret1 + 1) 79 n1 buf) (D + next) usp lo loc).
destruct POST as (m3 & a1' & -> & MU3 & WM3 & MI3 & ST3 & SY3).
clear SYc FR. cps_seg_post.
apply Hk.
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m3.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [unfold wz; do 3 f_equal; lia| split; reflexivity]|].
split. { split; [assumption|]. split; [exact MI3|]. split; [cps_wmono| exact ST3]. }
split; [exact PF|].
split; [| exact OG1].
split; [unfold sync_cells, wz; cbn [sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes]; replace next with (D + next - D) at 1 by lia; exact SY3|].
split; [unfold sync_fields_ok, int31; cbn [sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes]; destruct CASE as [(_ & C1)|(_ & C1)]; lia|].
split; [| exact SEP].
unfold sync_data. cbn [sy_data sy_buf sy_storage].
pose proof (ogg_sync_pageseek_inv sy _ _ _ (proj1 INV2) RES) as (_ & _ & EBUF' & EDATA' & ESTO' & _). cbn [sy_data sy_buf sy_storage] in EBUF', EDATA', ESTO'.
rewrite EDATA', ED, ESTO'. apply u8arr_rw_CB in ARR1. exact (conj D0 (conj ARR1 (conj LEN (conj PRE1 LE)))).
-
destruct DAT as (-> & -> & BUF0 & ST00).
assert (ARR : u8arr bsegs m 0 []).
{ split; [apply bytes_at_nil; lia|]. unfold wr_at. cbn [length Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi. lia. }
cbn [length Z.of_nat] in *.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(A, A + 32); (G, G + 32); (0, 0 + 0)] m) as PF.
refine (rz_evt RT AF Σ PMc _ _ T c MST Hc
(ogg_sync_pageseek_spec A G 0 lo [] sy j0 j1 j2 j3 ra sp gp _ t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m r ogo sy' FOK INV2 ltac:(rewrite BUF0; split; [reflexivity| cbn; lia]) ltac:(cbn [length Z.of_nat]; lia) ltac:(lia) ltac:(cbn [length Z.of_nat]; lia) A0 G0 LO128 SEPfA SEPfG
ltac:(left; cbn [length Z.of_nat]; clear - BF3; unfold SH_HI in *; lia) SEP_AG ltac:(right; cbn [length Z.of_nat]; lia) ltac:(right; cbn [length Z.of_nat]; lia) ST0 MI0 SY ARR OG RES eq_refl eq_refl) _).
intros ms1 c1 POST Hc1. clear Hc.
destruct POST as [FIN | (-> & CUT)].
+ cbn [length Z.of_nat] in FIN.
destruct FIN as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1 & SY1 & FOK1 & ARR1 & OG1).
rewrite EUSP in MU1, ST1. replace (usp - 128) with (usp + -128) in MU1 by lia.
apply (munch_weaken _ [(usp + -128, usp); (A, A + 32); (G, G + 32)]) in MU1; [| intros x Hx; cbn [outside length Z.of_nat] in *; repeat split; try tauto; lia].
cps_norm.
clear SY OG ARR. cps_seg_post.
apply Hk.
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m1.
split; [unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split. { split; [assumption|]. split; [exact MI1|]. split; [exact WM1| exact ST1]. }
split; [exact PF|].
split; [| exact OG1].
split; [exact SY1|]. split; [exact FOK1|]. split; [| exact SEP].
unfold sync_data. rewrite EDATA, EBUF, ESTO. repeat split; assumption.
+ exfalso. destruct CUT as (mc & loc & sy1 & x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & _ & _ & _ & _ & _ & _ & _ & _ & FOK1 & _ & _ & _ & Hb & Hf & _).
rewrite BUF0 in Hf. unfold zlength in Hf. cbn [length] in Hf. destruct FOK1 as (_ & _ & (R0 & _) & _). clear - Hb Hf R0. lia.
Qed.
End OggPageseekCPS.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments skipn {A} n l : simpl nomatch.
#[local] Arguments firstn {A} n l : simpl nomatch.

Lemma memchr_chk_le : forall c n (buf : list byte), 0 <= n -> 0 <= X058.memchr_chk c n buf <= n.
Proof.
intros c n buf Hn. unfold X058.memchr_chk. destruct (X1sa.find_byte c (firstn (Z.to_nat n) buf)) as [i|] eqn:E; [| lia].
pose proof (X1sa.find_byte_Some _ _ _ E) as (Hi & _). rewrite length_firstn in Hi. lia.
Qed.

Section OggPageseekCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MCHR : memchr_icontract RT.

Definition ogg_sync_pageseek_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A G D f lo : Z) (k : nat) (sy : sync_st bptr) (bytes j0 j1 j2 j3 : list byte) r ogo (sy' : sync_st bptr),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 G -> tp = Z_to_bv 64 0x630458 ->
sync_rep m A D sy bytes -> sync_inv2 sy -> 0 < A -> 0 < G -> sync_live RT Σ sy D ->
rw_cells asegs m G [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3] ->
ogg_sync_pageseek sy = ((r, ogo), sy') ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 32 <= f + fs_size k - 8 -> f <= G -> G + 32 <= f + fs_size k - 8 -> (A + 32 <= G \/ G + 32 <= A) ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 128 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_ogg_sync_pageseek m)))
(ASTA RT Σ PMc (fun ms => exists m',
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz r) m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 32); (G, G + 32); (D, D + Z.of_nat (length bytes))] m m'
/\ sync_rep m' A D sy' bytes
/\ rw_cells asegs m' G (og_cells D ogo [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3]))).

Theorem ogg_sync_pageseek_ok : ogg_sync_pageseek_cps.
Proof using AF MCHR.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A G D f lo k sy bytes j0 j1 j2 j3 r ogo sy'
FDO MST -> -> -> REP INV2 A0 G0 INL OG RES INF FA1 FA2 FG1 FG2 SEP_AG ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & F64 & FIMG & _ & _ & _ & _ & _ & _ & _).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
destruct REP as (SY & FOK & DAT & SEP).
pose proof (ogg_sync_pageseek_inv sy r ogo sy' (proj1 INV2) RES) as (INV' & EFILL & EBUF & EDATA & ESTO & _).
assert (SEPfA : A + 32 <= lo \/ usp <= A) by (left; clear - FA2 BF1; lia).
assert (SEPfG : G + 32 <= lo \/ usp <= G) by (left; clear - FG2 BF1; lia).
assert (LO128 : lo + 128 <= usp) by (clear - LOR; unfold RT_STACK in *; lia).
assert (EUSP : bv_unsigned sp = usp) by reflexivity.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
unfold sync_data in DAT. unfold sync_live in INL.
destruct (sy_data sy) as [p|] eqn:ED.
-
destruct DAT as (D0 & ARR & LEN & PRE1 & LE). specialize (INL ltac:(intros X; discriminate X)).
destruct (live_below_lo RT AF Σ m D (sy_storage sy) lo ART0 INL LOW) as (_ & BD1 & _).
destruct (frame_live_apart RT AF Σ m f k D (sy_storage sy) ART0 INF INL) as (FLD & _).
assert (DLO : D + Z.of_nat (length bytes) <= lo) by (rewrite LEN; exact BD1).
assert (SEP_AD : A + 32 <= D \/ D + Z.of_nat (length bytes) <= A) by (rewrite LEN; clear - FLD FA1 FA2; lia).
assert (SEP_GD : G + 32 <= D \/ D + Z.of_nat (length bytes) <= G) by (rewrite LEN; clear - FLD FG1 FG2; lia).
assert (TOPD : D + Z.of_nat (length bytes) < 2^63) by (clear - DLO LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (SEPfD : D + Z.of_nat (length bytes) <= lo \/ usp <= D) by (left; exact DLO).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(A, A + 32); (G, G + 32); (D, D + Z.of_nat (length bytes))] m) as PF.
refine (rz_evt RT AF Σ PMc _ _ T c MST Hc
(ogg_sync_pageseek_spec A G D lo bytes sy j0 j1 j2 j3 ra sp gp _ t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m r ogo sy' FOK INV2 (conj PRE1 LE) LEN ltac:(lia) TOPD A0 G0 LO128 SEPfA SEPfG SEPfD SEP_AG SEP_AD SEP_GD ST0 MI0 SY ARR OG RES eq_refl eq_refl) _).
intros ms1 c1 POST Hc1. clear Hc.
destruct POST as [FIN | (-> & CUT)].
+
destruct FIN as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1 & SY1 & FOK1 & ARR1 & OG1).
rewrite EUSP in MU1, ST1. replace (usp - 128) with (usp + -128) in MU1 by lia.
cps_norm.
clear SY OG ARR. cps_seg_post.
apply Hk.
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m1.
split; [unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split. { split; [assumption|]. split; [exact MI1|]. split; [exact WM1| exact ST1]. }
split; [exact PF|].
split; [| exact OG1].
split; [exact SY1|]. split; [exact FOK1|]. split; [| exact SEP].
unfold sync_data. rewrite EDATA, EBUF, ESTO. exact (conj D0 (conj ARR1 (conj LEN (conj PRE1 LE)))).
+
destruct CUT as (mc & loc & sy1 & x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & -> & MU1 & WM1 & MI1 & ST1 & SZ & FR & SYc & FOK1 & ARR1 & OG1 & EB & Hb & Hf & RESF).
fold usp in MU1, ST1, FR, Hc1. replace (usp - 128) with (usp + -128) in MU1 by lia.
set (ret1 := sy_returned sy1) in *. set (fill1 := sy_fill sy1) in *.
pose proof FOK1 as (Fs & Ff & Fr & Fu & Fh & Fbb). unfold int31 in Fs, Ff, Fr, Fu, Fh, Fbb. fold ret1 fill1 in Ff, Fr.
unfold zlength in Hf.
assert (BY1 : bytes_at asegs mc D bytes) by exact (proj1 ARR1).
apply u8arr_rw_CB in ARR1.
set (n1 := fill1 - ret1 + -1) in *.
set (buf := firstn (Z.to_nat n1) (skipn (Z.to_nat (ret1 + 1)) bytes)).
assert (LBUF : Z.of_nat (length buf) = n1) by (unfold buf; rewrite firstn_length_le by (rewrite length_skipn; unfold n1; lia); unfold n1; lia).
pose proof (bytes_at_sub mc D bytes (Z.to_nat (ret1 + 1)) (Z.to_nat n1) BY1 ltac:(unfold n1; lia)) as BYS. fold buf in BYS.
replace (D + Z.of_nat (Z.to_nat (ret1 + 1))) with (D + ret1 + 1) in BYS by lia.
cps_norm.
clear SY OG ARR BY1. cps_seg_post.
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -96)) = usp + -96) by (apply unsigned_lit; ulc).
cps_rt (MCHR Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc (D + ret1 + 1) 79 n1 buf lo).
all: [> lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- memchr_ok _ _ _ _ => unfold memchr_ok; rewrite LBUF; destruct (X1sa.find_byte 79 (firstn (Z.to_nat n1) buf)); lia
| |- checked_src _ _ _ _ _ _ _ =>
pose proof (memchr_chk_le 79 n1 buf ltac:(unfold n1; lia)) as CHK;
apply (live_checked_src RT AF Σ mc _ lo D (sy_storage sy)); [exact ART| exact INL| lia| unfold n1 in *; lia| exact BD1]
| |- _ \/ _ => left; rewrite LBUF; unfold n1; lia
| |- _ => first [ exact BYS | unfold n1; lia ]
end .. | ].
intros kc2 Hc2. unfold icpt_postF in Hc2.
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & _).

assert (MODEL : exists next, ((memchr_res (D + ret1 + 1) 79 n1 buf = 0 /\ D + next = D + fill1) \/
(memchr_res (D + ret1 + 1) 79 n1 buf = D + next /\ D + ret1 < D + next < D + fill1))
/\ r = - (next - ret1)
/\ sy' = mkSync (sy_data sy1) (sy_buf sy) (sy_storage sy1) fill1 next (sy_unsynced sy1) 0 0).
{ unfold sync_fail in RESF. fold fill1 in RESF. rewrite EB in RESF.
rewrite (pre_zslice (sy_buf sy) bytes (ret1 + 1) (fill1 - ret1 - 1) (conj PRE1 LE)) in RESF by lia.
rewrite find_byte_bridge in RESF. change CHAR_O with 79 in RESF.
replace (fill1 - ret1 - 1) with n1 in RESF by (unfold n1; lia). fold buf in RESF.
unfold memchr_res. replace (firstn (Z.to_nat n1) buf) with buf by (unfold buf; rewrite firstn_firstn, Nat.min_id; reflexivity).
destruct (X1sa.find_byte 79 buf) as [j|] eqn:FBt.
- pose proof (X1sa.find_byte_Some _ _ _ FBt) as (Hj & _).
exists (ret1 + 1 + Z.of_nat j). injection RESF as <- <-. split; [right; split; [lia| unfold n1 in *; lia]|]. split; reflexivity.
- exists fill1. injection RESF as <- <-. split; [left; split; reflexivity|]. split; reflexivity. }
destruct MODEL as (next & CASE & -> & ->).
cps_hide.
cps_seg (ps_tail A G D (sy_storage sy1) fill1 ret1 (sy_unsynced sy1) (memchr_res (D + ret1 + 1) 79 n1 buf) (D + next) usp lo loc).
destruct POST as (m3 & a1' & -> & MU3 & WM3 & MI3 & ST3 & SY3).
clear SYc FR. cps_seg_post.
apply Hk.
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m3.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [unfold wz; do 3 f_equal; lia| split; reflexivity]|].
split. { split; [assumption|]. split; [exact MI3|]. split; [cps_wmono| exact ST3]. }
split; [exact PF|].
split; [| exact OG1].
split; [unfold sync_cells, wz; cbn [sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes]; replace next with (D + next - D) at 1 by lia; exact SY3|].
split; [unfold sync_fields_ok, int31; cbn [sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes]; destruct CASE as [(_ & C1)|(_ & C1)]; lia|].
split; [| exact SEP].
unfold sync_data. cbn [sy_data sy_buf sy_storage].
pose proof (ogg_sync_pageseek_inv sy _ _ _ (proj1 INV2) RES) as (_ & _ & EBUF' & EDATA' & ESTO' & _). cbn [sy_data sy_buf sy_storage] in EBUF', EDATA', ESTO'.
rewrite EDATA', ED, ESTO'. apply u8arr_rw_CB in ARR1. exact (conj D0 (conj ARR1 (conj LEN (conj PRE1 LE)))).
-
destruct DAT as (-> & -> & BUF0 & ST00).
assert (ARR : u8arr asegs m 0 []).
{ split; [apply bytes_at_nil; lia|]. unfold wr_at. cbn [length Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi. lia. }
cbn [length Z.of_nat] in *.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(A, A + 32); (G, G + 32); (0, 0 + 0)] m) as PF.
refine (rz_evt RT AF Σ PMc _ _ T c MST Hc
(ogg_sync_pageseek_spec A G 0 lo [] sy j0 j1 j2 j3 ra sp gp _ t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m r ogo sy' FOK INV2 ltac:(rewrite BUF0; split; [reflexivity| cbn; lia]) ltac:(cbn [length Z.of_nat]; lia) ltac:(lia) ltac:(cbn [length Z.of_nat]; lia) A0 G0 LO128 SEPfA SEPfG
ltac:(left; cbn [length Z.of_nat]; clear - BF3; unfold SH_HI in *; lia) SEP_AG ltac:(right; cbn [length Z.of_nat]; lia) ltac:(right; cbn [length Z.of_nat]; lia) ST0 MI0 SY ARR OG RES eq_refl eq_refl) _).
intros ms1 c1 POST Hc1. clear Hc.
destruct POST as [FIN | (-> & CUT)].
+ cbn [length Z.of_nat] in FIN.
destruct FIN as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1 & SY1 & FOK1 & ARR1 & OG1).
rewrite EUSP in MU1, ST1. replace (usp - 128) with (usp + -128) in MU1 by lia.
apply (munch_weaken _ [(usp + -128, usp); (A, A + 32); (G, G + 32)]) in MU1; [| intros x Hx; cbn [outside length Z.of_nat] in *; repeat split; try tauto; lia].
cps_norm.
clear SY OG ARR. cps_seg_post.
apply Hk.
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m1.
split; [unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split. { split; [assumption|]. split; [exact MI1|]. split; [exact WM1| exact ST1]. }
split; [exact PF|].
split; [| exact OG1].
split; [exact SY1|]. split; [exact FOK1|]. split; [| exact SEP].
unfold sync_data. rewrite EDATA, EBUF, ESTO. repeat split; assumption.
+ exfalso. destruct CUT as (mc & loc & sy1 & x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & _ & _ & _ & _ & _ & _ & _ & _ & FOK1 & _ & _ & _ & Hb & Hf & _).
rewrite BUF0 in Hf. unfold zlength in Hf. cbn [length] in Hf. destruct FOK1 as (_ & _ & (R0 & _) & _). clear - Hb Hf R0. lia.
Qed.
End OggPageseekCPS.
