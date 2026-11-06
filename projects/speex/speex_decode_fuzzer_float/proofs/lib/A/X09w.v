(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s
X0ae X09m X09p X09n X09v.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0wl X110 X109 X10c X10a X10h.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X109 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10h.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma stream_init_prun : forall ser q r q', prun (ogg_stream_init (St := pst) p_malloc p_free ser) q = Some (r, q') ->
r = (0, init_os (Some tt) (Some tt) (Some tt) ser) /\ q' = q.
Proof.
intros ser q r q' H. unfold ogg_stream_init in H.
rewrite prun_bind, (prun_malloc_ok 16384) in H by reflexivity. cbn beta iota in H.
rewrite prun_bind, (prun_malloc_ok 4096) in H by reflexivity. cbn beta iota in H.
rewrite prun_bind, (prun_malloc_ok 8192) in H by reflexivity. cbn beta iota in H.
rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
Qed.

Section OggInitCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MAL : malloc_contract RT.
Hypothesis MSET : memset_icontract RT e_memset.

Definition ogg_stream_init_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A ser f lo : Z) (k : nat) (junk : list byte),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 ser -> tp = Z_to_bv 64 0x638c98 ->
rw_cells bsegs m A [CB 408 junk] -> 0 < A -> acc bsegs m A 408 ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 408 <= f + fs_size k - 8 ->
Z.of_nat (length (rt_live RT Σ)) + 3 <= LIVE_MAX -> 0 <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 48 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_ogg_stream_init m)))
(fun c => exists (Σ' : rts RT) (Bd L G : Z),
ASTA RT Σ' PMc (fun ms => exists m' (jb : list byte) (lws gws : list word),
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 408)] m m'
/\ rw_cells bsegs m' A (stream_cells Bd L G zero_hdr (init_os (Some tt) (Some tt) (Some tt) ser))
/\ u8arr bsegs m' Bd jb /\ Z.of_nat (length jb) = 16384
/\ u32arr bsegs m' L lws /\ Z.of_nat (length lws) = 1024 /\ u64arr bsegs m' G gws /\ Z.of_nat (length gws) = 1024) c
/\ rt_live RT Σ' = (G, 8192) :: (L, 4096) :: (Bd, 16384) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ
/\ stream_live RT Σ' (init_os (Some tt) (Some tt) (Some tt) ser) Bd L G
/\ Bd mod 16 = 0 /\ L mod 16 = 0 /\ G mod 16 = 0).

Local Ltac mal_side UWS LVM CR0 :=
lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- unwind_ch _ _ _ _ => apply UWS; cbn [In]; tauto
| |- Z.of_nat (length _) < _ => repeat match goal with E : rt_live _ _ = _ :: _ |- _ => rewrite E end; cbn [length]; clear - LVM; unfold LIVE_MAX in *; lia
| |- mcost _ <= _ => repeat match goal with E : rt_credit _ _ = _ |- _ => rewrite E end; cbn [mcost Z.leb Z.compare Pos.compare Pos.compare_cont]; clear - CR0; lia
| |- _ => lia
end.

Theorem ogg_stream_init_ok : ogg_stream_init_cps.
Proof using AF MAL MSET.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A ser f lo k junk
FDO MST -> -> -> OS A0 ACC INF FA1 FA2 LVM CR0 ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & F64 & FIMG & _ & _ & _ & SHF2 & _ & _ & FSELF).
assert (INF0 : id (In (f, k) (rt_frames RT Σ))) by exact INF.
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold RT_STACK in *; lia).
assert (AR : 0 < A < 2^64) by (clear - A0 FA2 BF1 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(A, A + 408)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
apply (rw_cells_split_CB bsegs _ _ [] 408 _ [] [16; 392]%nat) in OS; [| reflexivity]. cbn [mk_CB_cells app] in OS.
chunk_uncons OS as HD. replace (A + Z.of_nat (csize (CB 16 (firstn 16 junk)))) with (A + 16) in OS by reflexivity.
cps_norm.

cps_seg (stream_init_w1 A ser usp lo).
destruct POST as (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1). unfold init_frame in FR1.
cps_seg_post.
pose proof (proj2 OS) as WR1. cbn [cells_size csize Nat.add] in WR1. change (Z.of_nat 392) with 392 in WR1.
assert (ACC1 : acc bsegs m1 A 408).
{ apply (acc_frame_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp [(A, A + 408)] m m1 f k A 408 PF INF);
[clear - F64; Z.div_mod_to_equations; lia| apply fs_size_mod8| lia| exact FA1| lia| | exact ACC].
intros x Hx. cbn [outside]. split; [| exact I]. rewrite SHF2 in Hx. clear - Hx FSELF FA1 FA2. lia. }
cps_rt (MSET Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (A + 16) 392 (Z_to_bv 8 0) lo).
{ clear - A0 FA2 BF1 LOR SPT; lia. }
{ apply (frame_checked_dst RT Σ m1 _ f k (A + 16) 392); [exact INF| lia| lia| apply (acc_sub bsegs m1 A 408 (A + 16) 392 ACC1); lia| exact WR1]. }
{ cps_callok. }
intros kc2 Hc2. unfold icpt_postF in Hc2.
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BY2).
change (Z.to_nat 392) with 392%nat in BY2.
pose proof (ogg_ms_piece m1 m2 (A + 16) 392 _ WR1 WM2 BY2) as ZR. clear BY2.

cps_seg (stream_init_w2 A (firstn 16 junk)).
destruct POST as (m3 & j8 & -> & MU3 & WM3 & MI3 & OS3).
clear HD ZR. cps_seg_post.
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; ulc).
assert (UWS : forall (mm : mem) rr, In rr [RA_stream_init_malloc1; RA_stream_init_malloc2; RA_stream_init_malloc3] ->
unwind_ch mm (Z_to_bv 64 rr) (Z_to_bv 64 (-1)) (Z_to_bv 64 (usp + -48))).
{ intros mm rr Hr. apply unwind_ok_ch. unfold unwind_ok. split.
- unfold RA_stream_init_malloc1, RA_stream_init_malloc2, RA_stream_init_malloc3 in Hr.
destruct Hr as [<-|[<-|[<-|[]]]]; rewrite unsigned_lit by lia; unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right]).
- right; right. vm_compute. intros X; discriminate X. }
cps_rt (MAL Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 16384 lo).
all: [> mal_side UWS LVM CR0 .. | ].
intros kc4 (Σ1 & Bd & Hc4 & LV1 & FRS1 & SP1 & CR1 & B0 & B16 & BTOP & PO1).
cps_unpack Hc4 as (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & WRB & ACB).
cps_sigma LV1 FRS1 SP1.
destruct (live_below_lo RT AF Σ1 m4 Bd 16384 lo ART4 INL LOW) as (_ & BB1 & _).
destruct (frame_live_apart RT AF Σ1 m4 f k Bd 16384 ART4 INF INL) as (FLB & _).
assert (SEPB : Bd + 16384 <= A \/ A + 408 <= Bd) by (clear - FLB FA1 FA2; lia).
destruct (wr_at_rw_CB m4 Bd 16384 WRB ltac:(lia)) as (jb & BLKB).
pose proof BLKB as [[[LJB _] _] _]. cbn [cell_wf] in LJB. rewrite <- LJB in BLKB.
assert (LJBZ : Z.of_nat (length jb) = 16384) by (rewrite LJB; reflexivity).
cps_hide.

cps_seg (stream_init_w3 A Bd j8).
destruct POST as (m5 & -> & MU5 & WM5 & MI5 & OS5).
clear OS3. cps_seg_post.
cps_rt (MAL Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 4096 lo).
all: [> mal_side UWS LVM CR0 .. | ].
intros kc6 (Σ2 & L & Hc6 & LV2 & FRS2 & SP2 & CR2 & L0 & L16 & LTOP & PO2).
cps_unpack Hc6 as (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & WRL & ACL).
cps_sigma LV2 FRS2 SP2.
destruct (live_below_lo RT AF Σ2 m6 L 4096 lo ART6 INL0 LOW) as (_ & BL1 & _).
destruct (frame_live_apart RT AF Σ2 m6 f k L 4096 ART6 INF INL0) as (FLL & _).
assert (SEPL : L + 4096 <= A \/ A + 408 <= L) by (clear - FLL FA1 FA2; lia).
pose proof (af_live_disj RT AF Σ2 m6 L 4096 Bd 16384 [] _ ART6 LV2 ltac:(rewrite LV1; left; reflexivity)) as DBL.
destruct (wr_at_rw_CB m6 L 4096 WRL ltac:(lia)) as (jl & BLKL).
pose proof BLKL as [[[LJL _] _] _]. cbn [cell_wf] in LJL. rewrite <- LJL in BLKL.
assert (LJLZ : Z.of_nat (length jl) = 4096) by (rewrite LJL; reflexivity).
cps_hide.

cps_seg (stream_init_w4 A Bd L).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & OS7).
clear OS5. cps_seg_post.
cps_rt (MAL Σ2 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m7 8192 lo).
all: [> mal_side UWS LVM CR0 .. | ].
intros kc8 (Σ3 & G & Hc8 & LV3 & FRS3 & SP3 & CR3 & G0 & G16 & GTOP & PO3).
cps_unpack Hc8 as (m8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & WRG & ACG).
cps_sigma LV3 FRS3 SP3.
destruct (live_below_lo RT AF Σ3 m8 G 8192 lo ART8 INL1 LOW) as (_ & BG1 & _).
destruct (frame_live_apart RT AF Σ3 m8 f k G 8192 ART8 INF INL1) as (FLG & _).
assert (SEPG : G + 8192 <= A \/ A + 408 <= G) by (clear - FLG FA1 FA2; lia).
pose proof (af_live_disj RT AF Σ3 m8 G 8192 Bd 16384 [] _ ART8 LV3 ltac:(rewrite LV2, LV1; right; left; reflexivity)) as DBG.
pose proof (af_live_disj RT AF Σ3 m8 G 8192 L 4096 [] _ ART8 LV3 ltac:(rewrite LV2; left; reflexivity)) as DLG.
destruct (wr_at_rw_CB m8 G 8192 WRG ltac:(lia)) as (jg & BLKG).
pose proof BLKG as [[[LJG _] _] _]. cbn [cell_wf] in LJG. rewrite <- LJG in BLKG.
assert (LJGZ : Z.of_nat (length jg) = 8192) by (rewrite LJG; reflexivity).
assert (BR : 0 < Bd < 2^64) by (clear - B0 BB1 LOR SPT; lia).
assert (LR : 0 < L < 2^64) by (clear - L0 BL1 LOR SPT; lia).
assert (GR : 0 < G < 2^64) by (clear - G0 BG1 LOR SPT; lia).
cps_hide.

cps_seg (stream_init_w5 A Bd L G ser usp lo).
destruct POST as (m9 & -> & MU9 & WM9 & MI9 & ST9 & OS9).
clear OS7 FR1. cps_seg_post.
apply Hk. exists Σ3, Bd, L, G. split.
2:{ split; [rewrite LV3, LV2, LV1; reflexivity|]. split; [congruence|]. split; [congruence|].
split; [rewrite CR3, CR2, CR1; change (mcost 8192) with 0; change (mcost 4096) with 0; change (mcost 16384) with 0; lia|].
split; [congruence|]. split; [| tauto].
unfold stream_live, init_os. cbn [os_body_storage os_lacing_storage]. change (4 * 1024) with 4096. change (8 * 1024) with 8192.
split; [assumption|]. split; [assumption|]. split; [assumption|].
cps_unhide. clear - DBL DBG DLG. lia. }
eapply ASTA_conseq; [eassumption|]. intros ms <-.
apply u8arr_rw_CB in BLKB.
destruct (chunk_u32arr m9 L [] jl 1024 (length jl) ltac:(cbn [u32s app]; exact BLKL) ltac:(rewrite LJL; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (lws & ARL & LLW).
destruct (chunk_u64arr m9 G [] jg 1024 (length jg) ltac:(cbn [u64s app]; exact BLKG) ltac:(rewrite LJG; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (gws & ARG & LGW).
exists m9, jb, lws, gws.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split. { split; [assumption|]. split; [exact MI9|]. split; [cps_wmono| exact ST9]. }
split; [exact PF|]. split; [exact (OS9 _ _ _)|].
split; [exact BLKB|]. split; [exact LJBZ|]. split; [exact ARL|]. split; [exact LLW|]. split; [exact ARG| exact LGW].
Qed.
End OggInitCPS.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma stream_init_prun : forall ser q r q', prun (ogg_stream_init (St := pst) p_malloc p_free ser) q = Some (r, q') ->
r = (0, init_os (Some tt) (Some tt) (Some tt) ser) /\ q' = q.
Proof.
intros ser q r q' H. unfold ogg_stream_init in H.
rewrite prun_bind, (prun_malloc_ok 16384) in H by reflexivity. cbn beta iota in H.
rewrite prun_bind, (prun_malloc_ok 4096) in H by reflexivity. cbn beta iota in H.
rewrite prun_bind, (prun_malloc_ok 8192) in H by reflexivity. cbn beta iota in H.
rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
Qed.

Section OggInitCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MAL : malloc_contract RT.
Hypothesis MSET : memset_icontract RT e_memset.

Definition ogg_stream_init_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A ser f lo : Z) (k : nat) (junk : list byte),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 ser -> tp = Z_to_bv 64 0x630458 ->
rw_cells asegs m A [CB 408 junk] -> 0 < A -> acc asegs m A 408 ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 408 <= f + fs_size k - 8 ->
Z.of_nat (length (rt_live RT Σ)) + 3 <= LIVE_MAX -> 0 <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 48 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_ogg_stream_init m)))
(fun c => exists (Σ' : rts RT) (Bd L G : Z),
ASTA RT Σ' PMc (fun ms => exists m' (jb : list byte) (lws gws : list word),
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 408)] m m'
/\ rw_cells asegs m' A (stream_cells Bd L G zero_hdr (init_os (Some tt) (Some tt) (Some tt) ser))
/\ u8arr asegs m' Bd jb /\ Z.of_nat (length jb) = 16384
/\ u32arr asegs m' L lws /\ Z.of_nat (length lws) = 1024 /\ u64arr asegs m' G gws /\ Z.of_nat (length gws) = 1024) c
/\ rt_live RT Σ' = (G, 8192) :: (L, 4096) :: (Bd, 16384) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ
/\ stream_live RT Σ' (init_os (Some tt) (Some tt) (Some tt) ser) Bd L G
/\ Bd mod 16 = 0 /\ L mod 16 = 0 /\ G mod 16 = 0).

Local Ltac mal_side UWS LVM CR0 :=
lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- unwind_ch _ _ _ _ => apply UWS; cbn [In]; tauto
| |- Z.of_nat (length _) < _ => repeat match goal with E : rt_live _ _ = _ :: _ |- _ => rewrite E end; cbn [length]; clear - LVM; unfold LIVE_MAX in *; lia
| |- mcost _ <= _ => repeat match goal with E : rt_credit _ _ = _ |- _ => rewrite E end; cbn [mcost Z.leb Z.compare Pos.compare Pos.compare_cont]; clear - CR0; lia
| |- _ => lia
end.

Theorem ogg_stream_init_ok : ogg_stream_init_cps.
Proof using AF MAL MSET.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A ser f lo k junk
FDO MST -> -> -> OS A0 ACC INF FA1 FA2 LVM CR0 ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & F64 & FIMG & _ & _ & _ & SHF2 & _ & _ & FSELF).
assert (INF0 : id (In (f, k) (rt_frames RT Σ))) by exact INF.
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold RT_STACK in *; lia).
assert (AR : 0 < A < 2^64) by (clear - A0 FA2 BF1 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(A, A + 408)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
apply (rw_cells_split_CB asegs _ _ [] 408 _ [] [16; 392]%nat) in OS; [| reflexivity]. cbn [mk_CB_cells app] in OS.
chunk_uncons OS as HD. replace (A + Z.of_nat (csize (CB 16 (firstn 16 junk)))) with (A + 16) in OS by reflexivity.
cps_norm.

cps_seg (stream_init_w1 A ser usp lo).
destruct POST as (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1). unfold init_frame in FR1.
cps_seg_post.
pose proof (proj2 OS) as WR1. cbn [cells_size csize Nat.add] in WR1. change (Z.of_nat 392) with 392 in WR1.
assert (ACC1 : acc asegs m1 A 408).
{ apply (acc_frame_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp [(A, A + 408)] m m1 f k A 408 PF INF);
[clear - F64; Z.div_mod_to_equations; lia| apply fs_size_mod8| lia| exact FA1| lia| | exact ACC].
intros x Hx. cbn [outside]. split; [| exact I]. rewrite SHF2 in Hx. clear - Hx FSELF FA1 FA2. lia. }
cps_rt (MSET Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (A + 16) 392 (Z_to_bv 8 0) lo).
{ clear - A0 FA2 BF1 LOR SPT; lia. }
{ apply (frame_checked_dst RT Σ m1 _ f k (A + 16) 392); [exact INF| lia| lia| apply (acc_sub asegs m1 A 408 (A + 16) 392 ACC1); lia| exact WR1]. }
{ cps_callok. }
intros kc2 Hc2. unfold icpt_postF in Hc2.
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & BY2).
change (Z.to_nat 392) with 392%nat in BY2.
pose proof (ogg_ms_piece m1 m2 (A + 16) 392 _ WR1 WM2 BY2) as ZR. clear BY2.

cps_seg (stream_init_w2 A (firstn 16 junk)).
destruct POST as (m3 & j8 & -> & MU3 & WM3 & MI3 & OS3).
clear HD ZR. cps_seg_post.
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; ulc).
assert (UWS : forall (mm : mem) rr, In rr [RA_stream_init_malloc1; RA_stream_init_malloc2; RA_stream_init_malloc3] ->
unwind_ch mm (Z_to_bv 64 rr) (Z_to_bv 64 (-1)) (Z_to_bv 64 (usp + -48))).
{ intros mm rr Hr. apply unwind_ok_ch. unfold unwind_ok. split.
- unfold RA_stream_init_malloc1, RA_stream_init_malloc2, RA_stream_init_malloc3 in Hr.
destruct Hr as [<-|[<-|[<-|[]]]]; rewrite unsigned_lit by lia; unfold ALLOC_RAS; cbn [In]; repeat (first [left; reflexivity | right]).
- right; right. vm_compute. intros X; discriminate X. }
cps_rt (MAL Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 16384 lo).
all: [> mal_side UWS LVM CR0 .. | ].
intros kc4 (Σ1 & Bd & Hc4 & LV1 & FRS1 & SP1 & CR1 & B0 & B16 & BTOP & PO1).
cps_unpack Hc4 as (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & WRB & ACB).
cps_sigma LV1 FRS1 SP1.
destruct (live_below_lo RT AF Σ1 m4 Bd 16384 lo ART4 INL LOW) as (_ & BB1 & _).
destruct (frame_live_apart RT AF Σ1 m4 f k Bd 16384 ART4 INF INL) as (FLB & _).
assert (SEPB : Bd + 16384 <= A \/ A + 408 <= Bd) by (clear - FLB FA1 FA2; lia).
destruct (wr_at_rw_CB m4 Bd 16384 WRB ltac:(lia)) as (jb & BLKB).
pose proof BLKB as [[[LJB _] _] _]. cbn [cell_wf] in LJB. rewrite <- LJB in BLKB.
assert (LJBZ : Z.of_nat (length jb) = 16384) by (rewrite LJB; reflexivity).
cps_hide.

cps_seg (stream_init_w3 A Bd j8).
destruct POST as (m5 & -> & MU5 & WM5 & MI5 & OS5).
clear OS3. cps_seg_post.
cps_rt (MAL Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 4096 lo).
all: [> mal_side UWS LVM CR0 .. | ].
intros kc6 (Σ2 & L & Hc6 & LV2 & FRS2 & SP2 & CR2 & L0 & L16 & LTOP & PO2).
cps_unpack Hc6 as (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & WRL & ACL).
cps_sigma LV2 FRS2 SP2.
destruct (live_below_lo RT AF Σ2 m6 L 4096 lo ART6 INL0 LOW) as (_ & BL1 & _).
destruct (frame_live_apart RT AF Σ2 m6 f k L 4096 ART6 INF INL0) as (FLL & _).
assert (SEPL : L + 4096 <= A \/ A + 408 <= L) by (clear - FLL FA1 FA2; lia).
pose proof (af_live_disj RT AF Σ2 m6 L 4096 Bd 16384 [] _ ART6 LV2 ltac:(rewrite LV1; left; reflexivity)) as DBL.
destruct (wr_at_rw_CB m6 L 4096 WRL ltac:(lia)) as (jl & BLKL).
pose proof BLKL as [[[LJL _] _] _]. cbn [cell_wf] in LJL. rewrite <- LJL in BLKL.
assert (LJLZ : Z.of_nat (length jl) = 4096) by (rewrite LJL; reflexivity).
cps_hide.

cps_seg (stream_init_w4 A Bd L).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & OS7).
clear OS5. cps_seg_post.
cps_rt (MAL Σ2 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m7 8192 lo).
all: [> mal_side UWS LVM CR0 .. | ].
intros kc8 (Σ3 & G & Hc8 & LV3 & FRS3 & SP3 & CR3 & G0 & G16 & GTOP & PO3).
cps_unpack Hc8 as (m8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & WRG & ACG).
cps_sigma LV3 FRS3 SP3.
destruct (live_below_lo RT AF Σ3 m8 G 8192 lo ART8 INL1 LOW) as (_ & BG1 & _).
destruct (frame_live_apart RT AF Σ3 m8 f k G 8192 ART8 INF INL1) as (FLG & _).
assert (SEPG : G + 8192 <= A \/ A + 408 <= G) by (clear - FLG FA1 FA2; lia).
pose proof (af_live_disj RT AF Σ3 m8 G 8192 Bd 16384 [] _ ART8 LV3 ltac:(rewrite LV2, LV1; right; left; reflexivity)) as DBG.
pose proof (af_live_disj RT AF Σ3 m8 G 8192 L 4096 [] _ ART8 LV3 ltac:(rewrite LV2; left; reflexivity)) as DLG.
destruct (wr_at_rw_CB m8 G 8192 WRG ltac:(lia)) as (jg & BLKG).
pose proof BLKG as [[[LJG _] _] _]. cbn [cell_wf] in LJG. rewrite <- LJG in BLKG.
assert (LJGZ : Z.of_nat (length jg) = 8192) by (rewrite LJG; reflexivity).
assert (BR : 0 < Bd < 2^64) by (clear - B0 BB1 LOR SPT; lia).
assert (LR : 0 < L < 2^64) by (clear - L0 BL1 LOR SPT; lia).
assert (GR : 0 < G < 2^64) by (clear - G0 BG1 LOR SPT; lia).
cps_hide.

cps_seg (stream_init_w5 A Bd L G ser usp lo).
destruct POST as (m9 & -> & MU9 & WM9 & MI9 & ST9 & OS9).
clear OS7 FR1. cps_seg_post.
apply Hk. exists Σ3, Bd, L, G. split.
2:{ split; [rewrite LV3, LV2, LV1; reflexivity|]. split; [congruence|]. split; [congruence|].
split; [rewrite CR3, CR2, CR1; change (mcost 8192) with 0; change (mcost 4096) with 0; change (mcost 16384) with 0; lia|].
split; [congruence|]. split; [| tauto].
unfold stream_live, init_os. cbn [os_body_storage os_lacing_storage]. change (4 * 1024) with 4096. change (8 * 1024) with 8192.
split; [assumption|]. split; [assumption|]. split; [assumption|].
cps_unhide. clear - DBL DBG DLG. lia. }
eapply ASTA_conseq; [eassumption|]. intros ms <-.
apply u8arr_rw_CB in BLKB.
destruct (chunk_u32arr m9 L [] jl 1024 (length jl) ltac:(cbn [u32s app]; exact BLKL) ltac:(rewrite LJL; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (lws & ARL & LLW).
destruct (chunk_u64arr m9 G [] jg 1024 (length jg) ltac:(cbn [u64s app]; exact BLKG) ltac:(rewrite LJG; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (gws & ARG & LGW).
exists m9, jb, lws, gws.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split. { split; [assumption|]. split; [exact MI9|]. split; [cps_wmono| exact ST9]. }
split; [exact PF|]. split; [exact (OS9 _ _ _)|].
split; [exact BLKB|]. split; [exact LJBZ|]. split; [exact ARL|]. split; [exact LLW|]. split; [exact ARG| exact LGW].
Qed.
End OggInitCPS.
