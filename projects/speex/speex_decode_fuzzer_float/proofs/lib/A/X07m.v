(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j5 X0ec X001 X00b X000 X04b X07z X05o X05p X05s X08k X05u
X081 X05l X07y X05m X09f X06d X069 X05w X063 X05x X06e X07n X07o X07q X07p.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19o X14x X0r0 X0ra X0qz X0v9 X0yr X0wl X0zb X0wn X0ys X0yq X0x2 X0zo X0wp X0ww X0wq X0yf X0yg X0yi X0yh.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zo OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ww OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yf OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yg OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yi OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yh.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition sb_init_state (mo : spx_mode) (rate : Z) : sbd_state bptr :=
mkSBD tt mo (2 * sbm_frameSize mo) (sbm_frameSize mo) (sbm_subframeSize mo) (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo)) (sbm_lpcSize mo)
1 (rate * 2) 0 tt tt tt tt tt tt tt tt None 1 (sbm_defaultSubmode mo).
Definition sb_wrap (mo : spx_mode) (low : dec_state bptr) : dec_state bptr :=
DecSB (sb_init_state mo (fst (speex_decoder_ctl low CtlGetSamplingRate)))
(snd (speex_decoder_ctl (snd (speex_decoder_ctl low CtlGetSamplingRate)) (CtlSetWideband 1))).
Definition init_dec (mo : spx_mode) : dec_state bptr :=
match mo with
| ModeNB => DecNB (nb_init_state tt)
| ModeWB => sb_wrap ModeWB (DecNB (nb_init_state tt))
| ModeUWB => sb_wrap ModeUWB (sb_wrap ModeWB (DecNB (nb_init_state tt)))
end.

Definition low_mode (mo : spx_mode) : spx_mode := match mo with ModeUWB => ModeWB | _ => ModeNB end.

Lemma sb_init_prun : forall mo (low_init : X1qy.M pst (option (dec_state unit))) (low : dec_state unit) q r q',
(forall q0 r0 q0', prun low_init q0 = Some (r0, q0') -> r0 = Some low /\ q0' = q0) ->
prun (sb_decoder_init (St := pst) p_calloc p_free mo low_init) q = Some (r, q') -> r = Some (sb_wrap mo low) /\ q' = q.
Proof.
intros mo low_init low q r q' HL H. unfold sb_decoder_init in H.
rewrite prun_bind in H. rewrite (prun_calloc_ok SIZEOF_SBDECSTATE 1 q) in H by (unfold SIZEOF_SBDECSTATE; lia).
cbv beta iota in H. rewrite prun_bind in H.
destruct (prun low_init q) as [[r0 q0]|] eqn:EL in H; [| discriminate H]. cbv beta iota in H.
destruct (HL q r0 q0 EL) as [-> ->]. cbv beta iota in H.
destruct (speex_decoder_ctl low CtlGetSamplingRate) as [rate low1] eqn:E1.
destruct (speex_decoder_ctl low1 (CtlSetWideband 1)) as [v2 low2] eqn:E2.
assert (SZ : 0 <= sbm_subframeSize mo * 4 < 1000 /\ 0 <= sbm_lpcSize mo * 4 < 1000 /\ 0 <= Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4 < 1000
/\ 0 <= 2 * sbm_lpcSize mo * 4 < 1000) by (destruct mo; repeat split; vm_compute; first [reflexivity | (intro X; discriminate X)]).
destruct SZ as (Z1 & Z2 & Z3 & Z4).
rewrite prun_bind in H. rewrite (prun_calloc_ok (QMF_ORDER * 4) 1 q) in H by (unfold QMF_ORDER; lia). cbv beta iota in H.
rewrite prun_bind in H. rewrite (prun_calloc_ok (QMF_ORDER * 4) 1 q) in H by (unfold QMF_ORDER; lia). cbv beta iota in H.
rewrite prun_bind in H. rewrite (prun_calloc_ok (sbm_subframeSize mo * 4) 1 q) in H by lia. cbv beta iota in H.
rewrite prun_bind in H. rewrite (prun_calloc_ok (sbm_lpcSize mo * 4) 1 q) in H by lia. cbv beta iota in H.
rewrite prun_bind in H. rewrite (prun_calloc_ok (sbm_lpcSize mo * 4) 1 q) in H by lia. cbv beta iota in H.
rewrite prun_bind in H. rewrite (prun_calloc_ok (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4) 1 q) in H by lia. cbv beta iota in H.
rewrite prun_bind in H. rewrite (prun_calloc_ok (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4) 1 q) in H by lia. cbv beta iota in H.
rewrite prun_bind in H. rewrite (prun_calloc_ok (2 * sbm_lpcSize mo * 4) 1 q) in H by lia. cbv beta iota in H.
rewrite prun_ret in H. injection H as <- <-. split; [| reflexivity].
unfold sb_wrap, sb_init_state. unfold bptr. rewrite E1. cbn [fst snd]. rewrite E2. reflexivity.
Qed.

Lemma init_prun : forall mo q r q',
prun (speex_decoder_init (St := pst) p_calloc p_free mo) q = Some (r, q') -> r = Some (init_dec mo) /\ q' = q.
Proof.
intros mo q r q' H. destruct mo; cbn [speex_decoder_init init_dec] in *.
- exact (nb_init_prun q r q' H).
- exact (sb_init_prun ModeWB _ _ q r q' nb_init_prun H).
- refine (sb_init_prun ModeUWB _ _ q r q' _ H). intros q0 r0 q0'. exact (sb_init_prun ModeWB _ _ q0 r0 q0' nb_init_prun).
Qed.

Lemma init_dec_depth : forall mo, dec_depth (init_dec mo) = match mo with ModeNB => 1 | ModeWB => 2 | ModeUWB => 3 end%nat.
Proof. destruct mo; reflexivity. Qed.
Lemma ctl_gsr_snd : forall d : dec_state bptr, snd (speex_decoder_ctl d CtlGetSamplingRate) = d.
Proof. destruct d; reflexivity. Qed.
Lemma init_low_rate : forall mo, fst (speex_decoder_ctl (init_dec mo) CtlGetSamplingRate) = match mo with ModeNB => 8000 | ModeWB => 16000 | ModeUWB => 32000 end.
Proof. destruct mo; reflexivity. Qed.

Definition SBINIT_SITES : list Z := [0xbcd18; 0xbcf8c; 0xbcfb0; 0xbcfe0; 0xbd018; 0xbd048; 0xbd078; 0xbd0a8; 0xbd0e4].
Definition sb_traces (rae : Z) (ras : list Z) : Prop := forall site, In site SBINIT_SITES -> In (site :: rae :: ras) SITE_TRACES.

Definition init_traces (mo : spx_mode) (rae : Z) (ras : list Z) : Prop :=
match mo with
| ModeNB => In (RA_nbinit_calloc :: ras) SITE_TRACES
| ModeWB => sb_traces rae ras /\ In (RA_nbinit_calloc :: rae :: ras) SITE_TRACES
| ModeUWB => sb_traces rae ras /\ sb_traces RA_sbinit_low (rae :: ras) /\ In (RA_nbinit_calloc :: RA_sbinit_low :: rae :: ras) SITE_TRACES
end.

Definition uw_entry (m : mem) (s0 : word) (usp lo : Z) (ras : list Z) : Prop :=
match ras with [] => not_frame lo (bv_unsigned s0) | _ :: _ => uw_chain USTACK_TOP m usp (bv_unsigned s0) ras end.

Lemma init_traces_harness : forall mo, init_traces mo 0x971d0 [0x96650].
Proof.
assert (D : forall l, (if in_dec (list_eq_dec Z.eq_dec) l SITE_TRACES then True else False) -> In l SITE_TRACES)
by (intros l H; destruct (in_dec (list_eq_dec Z.eq_dec) l SITE_TRACES) as [i|]; [exact i| destruct H]).
assert (SB1 : sb_traces 0x971d0 [0x96650]).
{ intros site Hs. cbn [SBINIT_SITES In] in Hs. repeat (destruct Hs as [<-|Hs]; [apply D; vm_compute; exact I|]). destruct Hs. }
assert (SB2 : sb_traces RA_sbinit_low [0x971d0; 0x96650]).
{ intros site Hs. cbn [SBINIT_SITES In] in Hs. repeat (destruct Hs as [<-|Hs]; [apply D; vm_compute; exact I|]). destruct Hs. }
destruct mo; cbn [init_traces].
- apply D. vm_compute. exact I.
- split; [exact SB1| apply D; vm_compute; exact I].
- split; [exact SB1|]. split; [exact SB2| apply D; vm_compute; exact I].
Qed.

Lemma init_traces_low : forall mo rae ras, mo <> ModeNB -> init_traces mo rae ras -> sb_traces rae ras /\ init_traces (low_mode mo) RA_sbinit_low (rae :: ras).
Proof. intros mo rae ras NE H. destruct mo; [congruence| exact H| exact H]. Qed.

Lemma uw_chain_pres_i : forall live frames sp (m m' : mem) ras f fp,
rt_pres live frames sp m m' -> sp <= f -> uw_chain USTACK_TOP m f fp ras -> uw_chain USTACK_TOP m' f fp ras.
Proof.
intros live frames sp m m'. induction ras as [|r ras IHr]; intros f fp PR Hf H; cbn [uw_chain] in *; [exact H|].
destruct H as (H1 & H2 & H3 & fp' & H4 & H5 & H6).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. exists fp'. split; [exact H4|]. split.
- apply (rw_cells_agree_nw bsegs m m' _ _ H5). apply (agree_of_pres live frames sp m m' _ PR). intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. lia.
- apply (IHr fp fp' PR); [lia| exact H6].
Qed.

Lemma uw_entry_chain : forall live frames (m m' : mem) s0 usp lo ras f,
uw_entry m s0 usp lo ras -> rt_pres_fp live frames usp [] m m' -> lo <= f -> f <= usp ->
uw_chain USTACK_TOP m' f (bv_unsigned s0) ras.
Proof.
intros live frames m m' s0 usp lo ras f UE PF LF FU. destruct ras as [|r ras]; cbn [uw_entry] in UE.
- cbn [uw_chain]. exact (not_frame_stop lo _ f UE LF).
- apply (uw_chain_sp USTACK_TOP m' usp f _ r ras); [| exact FU].
apply (uw_chain_pres_i live frames usp m m' (r :: ras) usp _); [intros a Ha; exact (PF a Ha I)| lia| exact UE].
Qed.

Lemma sbinit_site_ch : forall live frames (m mk : mem) (s0 ra : word) usp lo ras site,
uw_entry m s0 usp lo ras -> rt_pres_fp live frames usp [] m mk ->
rw_cells bsegs mk (usp + -16) [C8 s0; C8 ra] ->
In (site :: bv_unsigned ra :: ras) SITE_TRACES ->
lo <= usp -> usp mod 8 = 0 -> usp <= USTACK_TOP -> 192 <= usp -> 0 <= site < 2^64 ->
unwind_ch mk (Z_to_bv 64 site) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)).
Proof.
intros live frames m mk s0 ra usp lo ras site UE PF REC TR LU U8 UT U192 SR.
exists (bv_unsigned ra :: ras). unfold USTACK_TOP in UT. rewrite !unsigned_lit by lia. split; [exact TR|].
apply (uw_chain_push USTACK_TOP mk (usp + -192) usp (bv_unsigned s0) (bv_unsigned ra) ras); [lia| exact U8| unfold USTACK_TOP; lia| apply bv_unsigned_in_range| |].
- rewrite !Z_to_bv_bv_unsigned. exact REC.
- exact (uw_entry_chain live frames m mk s0 usp lo ras usp UE PF LU ltac:(lia)).
Qed.

Lemma sbinit_low_entry : forall live frames (m mk : mem) (s0 ra : word) usp lo ras,
uw_entry m s0 usp lo ras -> rt_pres_fp live frames usp [] m mk ->
rw_cells bsegs mk (usp + -16) [C8 s0; C8 ra] ->
lo <= usp -> usp mod 8 = 0 -> usp <= USTACK_TOP -> 192 <= usp ->
uw_entry mk (Z_to_bv 64 usp) (usp + -192) lo (bv_unsigned ra :: ras).
Proof.
intros live frames m mk s0 ra usp lo ras UE PF REC LU U8 UT U192. cbn [uw_entry]. unfold USTACK_TOP in UT. rewrite unsigned_lit by lia.
apply (uw_chain_push USTACK_TOP mk (usp + -192) usp (bv_unsigned s0) (bv_unsigned ra) ras); [lia| exact U8| unfold USTACK_TOP; lia| apply bv_unsigned_in_range| |].
- rewrite !Z_to_bv_bv_unsigned. exact REC.
- exact (uw_entry_chain live frames m mk s0 usp lo ras usp UE PF LU ltac:(lia)).
Qed.

Section KitX.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Lemma flag_not_client_sub : forall (Σ Σ1 : rts RT) f k usp fl a,
rt_frames RT Σ1 = (f, k) :: rt_frames RT Σ -> (forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ1)) ->
~ aclient (rt_live RT Σ1) (rt_frames RT Σ1) USTACK_TOP fl -> fl < usp ->
aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> a <> fl.
Proof.
intros Σ Σ1 f k usp fl a FRS LV NAC FLU Ha E. subst a. apply NAC. rewrite FRS.
destruct Ha as [H|[H|[H|[H|H]]]]; [lia| right; left; exact H|
right; right; left; destruct H as (p & n & Hin & Hp); exists p, n; split; [exact (LV _ Hin)| exact Hp]|
right; right; right; left; destruct H as (f' & k' & Hin & Hf); exists f', k'; split; [right; exact Hin| exact Hf]|
right; right; right; right; destruct H as (f' & k' & Hin & Hf); exists f', k'; split; [right; exact Hin| exact Hf]].
Qed.

Lemma live_nodup : forall (Σ : rts RT) (m : mem) L pre rest, ART RT Σ m -> rt_live RT Σ = pre ++ L ++ rest ->
(forall e, In e L -> 0 < snd e) -> List.NoDup (map fst L).
Proof using AF.
intros Σ m L. induction L as [|[p n] L IH]; intros pre rest ART0 E POS; [constructor|].
cbn [map fst]. constructor.
- intros Hin. apply in_map_iff in Hin. destruct Hin as ([p2 n2] & E2 & Hin). cbn [fst] in E2. subst p2.
pose proof (POS (p, n) ltac:(left; reflexivity)) as P1. pose proof (POS (p, n2) ltac:(right; exact Hin)) as P2. cbn [snd] in P1, P2.
destruct (af_live_disj RT AF Σ m p n p n2 pre (L ++ rest) ART0 E ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hin)); lia.
- apply (IH (pre ++ [(p, n)]) rest ART0); [rewrite <- app_assoc; exact E| intros e He; apply POS; right; exact He].
Qed.
End KitX.

Ltac cps_release_intro_sub ARTc EF SUBL PREL Σ2 fl :=
lazymatch type of EF with
| rt_frames ?RT ?Σ1 = (?f, ?k) :: ?fr =>
lazymatch type of ARTc with
| ART RT Σ1 ?m =>
let fszb := eval vm_compute in (fs_size k - 8) in
let FLC := fresh "FLC" in let NAC := fresh "NAC" in let FL0 := fresh "FL0" in let FLW := fresh "FLW" in let FW := fresh "FW" in
let REL := fresh "REL" in
destruct (af_frame_release RT ltac:(eassumption) Σ1 m f k fr ARTc EF PREL) as (Σ2 & fl & FLC & NAC & FL0 & FLW & FW & REL);
change (fs_size k - 8) with fszb in FW; replace (f + fs_size k - 8) with (f + fszb) in FW by (change (fs_size k) with (fszb + 8); lia);
match goal with LO : rt_sp0 RT Σ1 - _ <= ?lo |- _ => let B := fresh "BFL" in assert (B : fl + 1 <= lo) by ulc end;
cps_norm;
lazymatch goal with
| PF : rt_pres_fp (rt_live RT ?Σ) (rt_frames RT ?Σ) ?U0 _ _ _ |- _ =>
let NFL := fresh "NFL" in
pose proof (fun a (Ha : aclient (rt_live RT Σ) (rt_frames RT Σ) U0 a) =>
flag_not_client_sub RT Σ Σ1 f k U0 fl a EF SUBL NAC ltac:(ulc) Ha) as NFL
| _ => idtac
end
end
end.

Lemma zbuf_recast : forall n m A, (n <= 80)%nat -> rw_cells bsegs m A [CB (4 * n) (zb (4 * n))] -> rw_cells bsegs m A (f32 (zw n)).
Proof.
intros n m A Hn X. apply (rw_cells_recast bsegs m A _ (f32 (zw n)) X); [apply cells_wf_f32|].
do 81 (destruct n as [|n]; [vm_compute; reflexivity|]). exfalso. lia.
Qed.

Lemma sbi_frame_rec : forall (m : mem) usp (c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 : cell) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word),
rw_cells bsegs m (usp + -192) [c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
cells_size [c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80] = 88%nat ->
rw_cells bsegs m (usp + -16) [C8 s0; C8 ra].
Proof.
intros m usp c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra X SZ.
change [c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
with (([c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80] ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1]) ++ [C8 s0; C8 ra]) in X.
apply (proj1 (rw_cells_app bsegs m _ _ _)) in X. destruct X as [_ X].
rewrite cells_size_app, SZ in X. cbn [cells_size csize Nat.add] in X.
replace (usp + -16) with (usp + -192 + Z.of_nat (88 + 88)) by lia. exact X.
Qed.

Definition init_stack (mo : spx_mode) : Z := match mo with ModeNB => 64 | ModeWB => 320 | ModeUWB => 512 end.
Definition init_nblocks (mo : spx_mode) : Z := match mo with ModeNB => 1 | ModeWB => 10 | ModeUWB => 19 end.

Definition init_credit (mo : spx_mode) : Z := match mo with ModeNB => 0 | ModeWB => 1 | ModeUWB => 4 end.
Definition mode_depth (mo : spx_mode) : nat := match mo with ModeNB => 1 | ModeWB => 2 | ModeUWB => 3 end.

Section InitCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis CAL : calloc_contract RT.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.

Definition init_cps_at (mo : spx_mode) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (lo : Z) (ras : list Z) (OUT STEREO : Z),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 (sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode mo) -> tp = Z_to_bv 64 0x638c98 ->
Z.of_nat (length (rt_live RT Σ)) + init_nblocks mo <= LIVE_MAX -> init_credit mo <= rt_credit RT Σ ->
(length (rt_frames RT Σ) + mode_depth mo <= FRAMES_MAX)%nat ->
init_traces mo (bv_unsigned ra) ras -> uw_entry m s0 (bv_unsigned sp) lo ras ->
ART RT Σ m -> mem_inv bsegs m -> frm0 fc ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + init_stack mo <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_decoder_init m)))
(fun c => exists (Σ' : rts RT) (D : Z) (LBD : list block) (NEW : list (Z * Z)),
ASTA RT Σ' PMc (fun ms => exists m',
ret_stL (fun _ fc' => frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 D) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [] m m'
/\ DREP OUT STEREO m' D (init_dec mo) LBD) c
/\ rt_live RT Σ' = NEW ++ rt_live RT Σ /\ Permutation NEW (blocks_live LBD) /\ List.NoDup (map blk_id LBD) /\ Z.of_nat (length NEW) = init_nblocks mo
/\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ - init_credit mo <= rt_credit RT Σ' <= rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ
/\ (forall x, In x LBD -> blk_addr x mod 8 = 0)).

Theorem init_cps_nb : init_cps_at ModeNB.
Proof using AF CAL MSET AF_LIB.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ras OUT STEREO
FDO MST E0 ETP LVM CR0 FRM TR UE ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
cbn [init_traces init_nblocks init_credit init_stack sb_mode_ptr] in *.
intros T c Hc Hk.
refine (nb_decoder_init_ok RT AF CAL MSET AF_LIB Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
FDO MST E0 ETP ltac:(lia) ltac:(lia) _ ART0 MI0 ST0 LOW LOR SPT ltac:(clear - SPA; Z.div_mod_to_equations; lia) T c Hc _).
{ exists ras. split; [exact TR| exact UE]. }
intros c' (Σ' & D & Hc' & LV & FRS & SP0 & CR & PO). apply Hk.
assert (D8 : D mod 8 = 0).
{ destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms & (m' & _ & _ & _ & REP) & _). specialize (REP OUT STEREO). cbn [decst_rep] in REP. destruct REP as (_ & AL & _). exact AL. }
exists Σ', D, [(tt, D, NBSTATE_SIZEOF)], [(D, NBSTATE_SIZEOF)].
split; [| split; [exact LV|]; split; [apply Permutation_refl|]; split; [repeat constructor; intros []|]; split; [reflexivity|]; split; [exact FRS|]; split; [exact SP0|];
split; [lia| split; [exact PO| intros x [<-|[]]; exact D8]]].
eapply ASTA_conseq; [exact Hc'|]. intros ms (m' & RS & AFT & PF & REP). exists m'.
split; [| split; [exact AFT|]; split; [exact PF| exact (REP OUT STEREO)]].
unfold ret_stL in *. destruct RS as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & F' & fc' & E & -> & ->).
do 16 eexists. split; [exact E| exact FRM0].
Qed.

Definition sb_sm_ptr (mo : spx_mode) : Z := match mo with ModeUWB => A_sb_uwb_mode | _ => A_sb_wb_mode end.
Lemma sb_mode_facts : forall mo (m : mem), mo <> ModeNB -> lib_consts m ->
exists (c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12 g1 g2 lf fg sm0 sm1 sm2 sm3 sm4 sm5 sm6 sm7 : word) (pad : list byte),
ro_cells bsegs m (sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode mo) (sbi_desc_cells (Z_to_bv 64 (sb_sm_ptr mo)) c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12)
/\ ro_cells bsegs m (sb_sm_ptr mo) (sbmode_cells (sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (low_mode mo)) (sbm_frameSize mo) (sbm_subframeSize mo) 8
g1 g2 lf fg pad sm0 sm1 sm2 sm3 sm4 sm5 sm6 sm7 (sbm_defaultSubmode mo))
/\ length pad = 4%nat.
Proof.
intros mo m NE LC. destruct mo; [congruence| |].
- pose proof (lib_const m A_speex_wb_mode LC_speex_wb_mode LC ltac:(lc_in)) as D.
pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as B.
rewrite <- (firstn_skipn 18 LC_sb_wb_mode) in B. apply (proj1 (ro_cells_app bsegs m _ _ _)) in B. destruct B as [B _].
unfold LC_sb_wb_mode in B. cbn [firstn] in B. unfold LC_speex_wb_mode in D.
do 24 eexists. cbn [sb_mode_ptr sb_sm_ptr low_mode sbm_frameSize sbm_subframeSize sbm_defaultSubmode].
split; [exact D|]. split; [exact B| reflexivity].
- pose proof (lib_const m A_speex_uwb_mode LC_speex_uwb_mode LC ltac:(lc_in)) as D.
pose proof (lib_const m A_sb_uwb_mode LC_sb_uwb_mode LC ltac:(lc_in)) as B.
rewrite <- (firstn_skipn 18 LC_sb_uwb_mode) in B. apply (proj1 (ro_cells_app bsegs m _ _ _)) in B. destruct B as [B _].
unfold LC_sb_uwb_mode in B. cbn [firstn] in B. unfold LC_speex_uwb_mode in D.
do 24 eexists. cbn [sb_mode_ptr sb_sm_ptr low_mode sbm_frameSize sbm_subframeSize sbm_defaultSubmode].
split; [exact D|]. split; [exact B| reflexivity].
Qed.
Lemma sb_mode_arith : forall mo, mo <> ModeNB ->
let MP := sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode mo in let SM := sb_sm_ptr mo in
MP mod 8 = 0 /\ 0x10000 <= MP /\ MP + 104 <= 0x65a180 /\ In (MP, 96) ACC_LITS
/\ SM mod 8 = 0 /\ 0x10000 <= SM /\ SM + 216 <= 0x65a180 /\ In (SM, 216) ACC_LITS
/\ SM + 40 = sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR mo
/\ ((sbm_frameSize mo = 160 /\ sbm_subframeSize mo = 40) \/ (sbm_frameSize mo = 320 /\ sbm_subframeSize mo = 80))
/\ - 2^31 <= sbm_defaultSubmode mo < 2^31.
Proof.
intros mo NE. destruct mo; [congruence| |]; cbn [sb_mode_ptr sb_sm_ptr sb_submodes_ptr sbm_frameSize sbm_subframeSize sbm_defaultSubmode];
unfold A_speex_wb_mode, A_speex_uwb_mode, A_sb_wb_mode, A_sb_uwb_mode, WB_SUBMODES_PTR, UWB_SUBMODES_PTR, A_sb_wb_mode, A_sb_uwb_mode, ACC_LITS; cbn [In];
(split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [repeat (first [left; reflexivity | right])|];
split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [repeat (first [left; reflexivity | right])|]; split; [reflexivity|]; split; [| lia]).
- left. split; reflexivity.
- right. split; reflexivity.
Qed.

Lemma newchunks_apart : forall (Σ Σ1 : rts RT) (m1 : mem) NEW L usp a p n,
ART RT Σ1 m1 -> rt_live RT Σ1 = NEW ++ L -> (forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT Σ1)) -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
rt_sp0 RT Σ - STACK_WIN <= usp -> In (p, n) NEW -> aclient L (rt_frames RT Σ) usp a -> ~ (p <= a < p + n).
Proof using AF.
intros Σ Σ1 m1 NEW L usp a p n ART1 LV FRS SP0 LU INN Ha Hin.
assert (INL : In (p, n) (rt_live RT Σ1)) by (rewrite LV; apply in_app_iff; left; exact INN).
pose proof (af_live_range RT AF Σ1 m1 p n ART1 INL) as (L0 & L1 & L2). rewrite SP0 in L1.
destruct Ha as [H|[H|[H|[H|H]]]].
- lia.
- pose proof (client_static_range a H). unfold SEGTOP_A in *. lia.
- destruct H as (p' & n' & Hin' & Hp').
destruct (in_split _ _ INN) as (n1 & n2 & EN). rewrite EN, <- app_assoc in LV. cbn [app] in LV.
destruct (af_live_disj RT AF Σ1 m1 p n p' n' n1 (n2 ++ L) ART1 LV ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hin')); lia.
- destruct H as (f & k & Hinf & Hf). apply FRS in Hinf.
pose proof (af_frames_range RT AF Σ1 m1 f k ART1 Hinf) as (_ & _ & _ & R3). destruct (R3 p n INL); lia.
- destruct H as (f & k & Hinf & Hf). apply FRS in Hinf.
pose proof (af_fshadow_apart RT AF Σ1 m1 f k ART1 Hinf) as (SL & _). destruct (SL p n INL); lia.
Qed.

Ltac sigma_app EL EF ES :=
lazymatch type of ES with
| rt_sp0 ?RT ?Σ' = rt_sp0 ?RT ?Σ =>
repeat match goal with
| H : In ?e0 (rt_live RT Σ) |- _ =>
let H' := fresh H in assert (H' : In e0 (rt_live RT Σ')) by (rewrite EL; apply in_app_iff; right; exact H); clear H; rename H' into H
end;
repeat match goal with H : rt_sp0 RT Σ - _ <= _ |- _ => rewrite <- ES in H end;
repeat match goal with H : In ?e0 (rt_frames RT Σ) |- _ => rewrite <- EF in H end
end.

Lemma drep_head : forall OUT STEREO (m : mem) S (d : dec_state bptr) LBD, DREP OUT STEREO m S d LBD -> exists n, In (tt, S, n) LBD /\ 0 < n /\ S mod 8 = 0.
Proof.
intros OUT STEREO m S d LBD H. destruct d as [st|s low]; cbn [decst_rep] in H.
- destruct H as [-> NB]. exists NBSTATE_SIZEOF. destruct (nb_blk st). split; [left; reflexivity|]. split; [unfold NBSTATE_SIZEOF; lia| exact (proj1 NB)].
- destruct H as (a & j & LBL & -> & S8 & _). exists SBSTATE_SIZEOF. destruct (sbd_blk s) eqn:E. split; [left; cbn [sb_blocks]; rewrite E; reflexivity|].
split; [unfold SBSTATE_SIZEOF; lia| exact S8].
Qed.
Lemma drep_sizes_pos : forall (d : dec_state bptr) OUT STEREO (m : mem) S LBD, DREP OUT STEREO m S d LBD -> forall b, In b LBD -> 0 < blk_size b.
Proof.
induction d as [st|s low IHd]; intros OUT STEREO m S LBD H b Hb; cbn [decst_rep] in H.
- destruct H as [-> _]. destruct Hb as [<-|[]]. unfold blk_size, NBSTATE_SIZEOF. cbn. lia.
- destruct H as (a & j & LBL & -> & _ & _ & INV & _ & _ & _ & OUTL & RL). apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| exact (IHd _ _ _ _ _ RL b Hb)].
destruct INV as (IM & _ & _ & ISF & _). assert (0 < sbd_subframeSize s) by (rewrite ISF; destruct IM as [E|E]; rewrite E; cbn; lia).
cbn [sb_blocks In] in Hb. unfold SBSTATE_SIZEOF in Hb.
repeat (destruct Hb as [<-|Hb]; [unfold blk_size; cbn [snd]; lia|]). destruct Hb.
Qed.

Lemma new_old_apart : forall (Σ : rts RT) (m : mem) NEW L p1 n1 p2 n2, ART RT Σ m -> rt_live RT Σ = NEW ++ L -> In (p1, n1) NEW -> In (p2, n2) L ->
p1 + n1 <= p2 \/ p2 + n2 <= p1.
Proof using AF.
intros Σ m NEW L p1 n1 p2 n2 ART0 LV H1 H2. destruct (in_split _ _ H1) as (l1 & l2 & E). rewrite E, <- app_assoc in LV. cbn [app] in LV.
apply (af_live_disj RT AF Σ m p1 n1 p2 n2 l1 (l2 ++ L) ART0 LV). apply in_app_iff. right. apply in_app_iff. right. exact H2.
Qed.

Lemma zero_chunk : forall (m : mem) B n, 0 <= n -> wr_at bsegs m B n -> bytes_at bsegs m B (repeat (Z_to_bv 8 0) (Z.to_nat n)) ->
rw_cells bsegs m B [CB (Z.to_nat n) (zb (Z.to_nat n))].
Proof.
intros m B n N0 WR BY. split; [split; [split; [unfold zb; apply repeat_length| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BY]|].
cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact WR.
Qed.
Definition zbufs (m : mem) (BL : list block) : Prop :=
forall b, In b BL -> 0 <= blk_size b /\ rw_cells bsegs m (blk_addr b) [CB (Z.to_nat (blk_size b)) (zb (Z.to_nat (blk_size b)))].
Lemma zbufs_nil : forall m, zbufs m []. Proof. intros m b []. Qed.
Lemma zbufs_cons : forall (m : mem) B n BL, 0 <= n -> rw_cells bsegs m B [CB (Z.to_nat n) (zb (Z.to_nat n))] -> zbufs m BL -> zbufs m ((tt, B, n) :: BL).
Proof. intros m B n BL N0 X Z b [<-|Hb]; [split; [exact N0| exact X]| exact (Z b Hb)]. Qed.
Lemma zbufs_agree : forall (m m' : mem) BL, zbufs m BL -> agree_blocks bsegs m m' BL -> zbufs m' BL.
Proof.
intros m m' BL Z AG b Hb. destruct (Z b Hb) as [N0 X]. split; [exact N0|].
apply (rw_cells_agree_at bsegs m m' _ _ X). apply (agree_blocks_at bsegs m m' BL b _ _ AG Hb X); [lia|].
cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. lia.
Qed.

Lemma rw_cells_pres_cl : forall live frames sp (m m' : mem) A cs, rt_pres live frames sp m m' -> wmono bsegs m m' -> rw_cells bsegs m A cs ->
(forall x, A <= x < A + Z.of_nat (cells_size cs) -> aclient live frames sp x) -> rw_cells bsegs m' A cs.
Proof. intros live frames sp m m' A cs PR WM X CL. apply (rw_cells_agree bsegs m m' A cs X); [apply (agree_of_pres live frames sp m m' _ PR); exact CL| exact WM]. Qed.
Lemma rw_cells_pres_stack : forall live frames sp (m m' : mem) A cs n, rt_pres live frames sp m m' -> wmono bsegs m m' -> rw_cells bsegs m A cs ->
Z.of_nat (cells_size cs) = n -> sp <= A -> A + n <= USTACK_TOP -> rw_cells bsegs m' A cs.
Proof. intros live frames sp m m' A cs n PR WM X E H1 H2. apply (rw_cells_pres_cl live frames sp m m' A cs PR WM X). intros x Hx. left. lia. Qed.
Lemma rw_cells_pres_live : forall live frames sp (m m' : mem) A cs n p k, rt_pres live frames sp m m' -> wmono bsegs m m' -> rw_cells bsegs m A cs ->
Z.of_nat (cells_size cs) = n -> In (p, k) live -> p <= A -> A + n <= p + k -> rw_cells bsegs m' A cs.
Proof. intros live frames sp m m' A cs n p k PR WM X E IN H1 H2. apply (rw_cells_pres_cl live frames sp m m' A cs PR WM X). intros x Hx. right; right; left. exists p, k. split; [exact IN| lia]. Qed.
Lemma rw_cells_pres_frame : forall live frames sp (m m' : mem) A cs n f k, rt_pres live frames sp m m' -> wmono bsegs m m' -> rw_cells bsegs m A cs ->
Z.of_nat (cells_size cs) = n -> In (f, k) frames -> f <= A -> A + n <= f + fs_size k - 8 -> rw_cells bsegs m' A cs.
Proof. intros live frames sp m m' A cs n f k PR WM X E IN H1 H2. apply (rw_cells_pres_cl live frames sp m m' A cs PR WM X). intros x Hx. right; right; right; left. exists f, k. split; [exact IN| lia]. Qed.
Lemma rw_cells_pres_fshadow : forall live frames sp (m m' : mem) A cs n f k, rt_pres live frames sp m m' -> wmono bsegs m m' -> rw_cells bsegs m A cs ->
Z.of_nat (cells_size cs) = n -> In (f, k) frames -> shad f <= A -> A + n <= shad (f + fs_size k) -> rw_cells bsegs m' A cs.
Proof. intros live frames sp m m' A cs n f k PR WM X E IN H1 H2. apply (rw_cells_pres_cl live frames sp m m' A cs PR WM X). intros x Hx. right; right; right; right. exists f, k. split; [exact IN| lia]. Qed.

Theorem init_cps_sb : forall mo, mo <> ModeNB -> init_cps_at (low_mode mo) -> init_cps_at mo.
Proof using AF CAL SM0 AF_LIB.
intros mo NENB IH Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ras OUT STEREO
FDO MST -> -> LVM CR0 FRM TR UE ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
destruct (init_traces_low mo _ _ NENB TR) as (TRS & TRL). clear TR.
assert (EDEC : init_dec mo = sb_wrap mo (init_dec (low_mode mo))) by (destruct mo; [congruence| reflexivity| reflexivity]).
assert (STK : init_stack mo = 192 + Z.max (init_stack (low_mode mo)) (ctl_stack (init_dec (low_mode mo)))) by (destruct mo; [congruence| reflexivity| reflexivity]).
assert (NBL : init_nblocks mo = 9 + init_nblocks (low_mode mo)) by (destruct mo; [congruence| reflexivity| reflexivity]).
assert (CRL : init_credit mo = 1 + init_credit (low_mode mo) + 2 * (Z.of_nat (mode_depth (low_mode mo)) - 1)) by (destruct mo; [congruence| reflexivity| reflexivity]).
assert (DPL : mode_depth mo = S (mode_depth (low_mode mo))) by (destruct mo; [congruence| reflexivity| reflexivity]).
assert (DDL : dec_depth (init_dec (low_mode mo)) = mode_depth (low_mode mo)) by (destruct mo; reflexivity).
assert (LST : 0 <= init_stack (low_mode mo)) by (destruct mo; cbn; lia).
assert (LNB : 1 <= init_nblocks (low_mode mo)) by (destruct mo; cbn; lia).
assert (LCR : 0 <= init_credit (low_mode mo)) by (destruct mo; cbn; lia).
assert (LDP : (1 <= mode_depth (low_mode mo) <= 2)%nat) by (destruct mo; cbn; lia).
rewrite STK in LOR. rewrite NBL in LVM. rewrite CRL in CR0. rewrite DPL in FRM.
set (lowmo := low_mode mo) in *. set (LSTK := init_stack lowmo) in *. set (CSTK := ctl_stack (init_dec lowmo)) in *.
set (LNBL := init_nblocks lowmo) in *. set (LCRD := init_credit lowmo) in *. set (LDEP := mode_depth lowmo) in *.
assert (CST : 0 <= CSTK) by (subst CSTK; generalize (init_dec lowmo); intros d; induction d; cbn [ctl_stack]; unfold NBCTL_STACK; lia).

destruct (sb_mode_arith mo NENB) as (MP8 & MPLO & MPHI & MPLIT & SM8 & SMLO & SMHI & SMLIT & ESUB & GEO & DSR).
pose proof (fun m (LC : lib_consts m) => sb_mode_facts mo m NENB LC) as MODEK. fold lowmo in MODEK.
set (MP := sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode mo) in *.
set (NBM := sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode lowmo) in *.
set (SM := sb_sm_ptr mo) in *. set (fs := sbm_frameSize mo) in *. set (sfs := sbm_subframeSize mo) in *. set (dsm := sbm_defaultSubmode mo) in *.
pose proof (eq_refl : MP = sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode mo) as EMP. clearbody MP.
pose proof (eq_refl : NBM = sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode lowmo) as ENBM. clearbody NBM.
pose proof (eq_refl : SM = sb_sm_ptr mo) as ESM. clearbody SM.
pose proof (eq_refl : fs = sbm_frameSize mo) as EFS. clearbody fs. pose proof (eq_refl : sfs = sbm_subframeSize mo) as ESFS. clearbody sfs.
pose proof (eq_refl : dsm = sbm_defaultSubmode mo) as EDSM. clearbody dsm.
destruct (MODEK m (AF_LIB Σ m ART0)) as (c1 & c2 & c3 & c4 & c5 & c6 & c7 & c9 & c10 & c11 & c12 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND0 & _ & _).
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
assert (OBM : aobj bsegs m MP 96) by (apply (aobj_lit RT AF Σ m MP 96 ART0 MPLIT); unfold APP_TOP; lia).
pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
assert (LOS : SH_HI <= lo) by (unfold SH_HI, STACK_WIN in *; lia).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [] m) as PF.
pose proof (fun E : rt_frames RT Σ = [] => af_pois_nil RT AF Σ m ART0 E) as PNIL.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
assert (LO192 : lo <= usp + -192) by (clear - LOR LST; unfold RT_STACK in LOR; lia).
cps_norm. cps_hide.

cps_seg (sbinit_w1 usp lo MP).
destruct POST as (m1 & j8 & j16 & j24 & j32 & j40 & j48 & j56 & j64 & j72 & j80 & xt1 & xa3 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
cps_seg_post.

cps_rt_sized SM0 0. { cbn; tauto. } { cps_callok. }
intros cc2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP & PO1).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS).
cps_new_frame ART2 FRS1 LV1 SP1 WRF WRS sf. cps_hide.

cps_seg (sbinit_w2 usp lo MP f sf).
destruct POST as (m3 & xa2 & xa3' & k24 & l32 & k36 & k40 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & FRB3 & FRS3).
clear FR1 FRB FRS.
cps_seg_post.
assert (SUBF1 : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT Σ1)) by (intros e He; rewrite FRS1; right; exact He).
assert (SUBL1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ1)) by (intros e He; rewrite LV1; exact He).

assert (UW3 : unwind_ch m3 (Z_to_bv 64 RA_sbinit_calloc0) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))).
{ apply (sbinit_site_ch (rt_live RT Σ) (rt_frames RT Σ) m m3 s0 ra usp lo ras RA_sbinit_calloc0 UE PF (sbi_frame_rec m3 usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR3 eq_refl));
[apply TRS; unfold SBINIT_SITES, RA_sbinit_calloc0; cbn [In]; tauto| ulc| clear - SPA; Z.div_mod_to_equations; lia| ulc| ulc| unfold RA_sbinit_calloc0; lia]. }
cps_rt CAL.
{ rewrite LV1. clear - LVM LNB. lia. } { change (mcost (160 * 1)) with 0. rewrite CR1. clear - CR0 LCR LDP. lia. } { cps_callok. }
intros cc4 (Σ2 & S & Hc4 & LV2 & FRS2 & SP2 & CR2 & SPOS & S16 & STOP & PO2).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
change (160 * 1) with 160 in *. change (mcost 160) with 0 in CR2. rewrite Z.sub_0_r in CR2. change (Z.to_nat 160) with 160%nat in *.
cps_unpack Hc4 as (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & WRS4 & ACS4 & BYS4).
assert (SUBF2 : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT Σ2)) by (intros e He; rewrite FRS2; exact (SUBF1 e He)).
assert (SUBL2 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ2)) by (intros e He; rewrite LV2; right; exact (SUBL1 e He)).
pose proof (fun a (Ha : aclient (rt_live RT Σ) (rt_frames RT Σ) usp a) =>
newchunks_apart Σ Σ2 m4 [(S, 160)] (rt_live RT Σ) usp a S 160 ART4 ltac:(rewrite LV2, LV1; reflexivity) SUBF2 ltac:(rewrite SP2; exact SP1)
ltac:(ulc) ltac:(left; reflexivity) Ha) as NAS.
cps_sigma LV2 FRS2 SP2.
destruct (live_below_lo RT AF Σ2 m4 S 160 lo ART4 INL LOW) as (_ & BS1 & _).
pose proof (live_facts RT AF Σ2 m4 S 160 ART4 INL) as (_ & _ & SIMG & SHI).
destruct (frame_live_apart RT AF Σ2 m4 f 0%nat S 160 ART4 INF INL) as (FLA1 & FLA2).
change (fs_size 0) with 64 in FLA1, FLA2. rewrite SHF0, <- SHF in FLA2.
assert (S8 : S mod 8 = 0) by (clear - S16; Z.div_mod_to_equations; lia).
assert (BLK : rw_cells bsegs m4 S [CB 160 (repeat (Z_to_bv 8 0) 160)]).
{ split; [split; [split; [vm_compute; reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BYS4]| exact WRS4]. }
apply sbst_zero_recast in BLK. clear BYS4 WRS4.
assert (OBS4 : aobj bsegs m4 S 160) by (split; [lia|]; split; [ulc| exact ACS4]).
assert (OBM4 : aobj bsegs m4 MP 96) by (apply (aobj_lit RT AF Σ2 m4 MP 96 ART4 MPLIT); ulc).
assert (OBSM4 : aobj bsegs m4 SM 216) by (apply (aobj_lit RT AF Σ2 m4 SM 216 ART4 SMLIT); ulc).
destruct (MODEK m4 (AF_LIB Σ2 m4 ART4)) as (d1 & d2 & d3 & d4 & d5 & d6 & d7 & d9 & d10 & d11 & d12 & g1 & g2 & lf & fg & sm0 & sm1 & sm2 & sm3 & sm4 & sm5 & sm6 & sm7 & pad & ND4 & NS4 & LPAD).
cps_hide.

cps_seg (sbinit_w3 usp S MP SM NBM f sf fs sfs 8 dsm).
destruct POST as (m5 & xa1 & -> & MU5 & WM5 & MI5 & X5).
clear BLK OBS4 OBM4 OBSM4 ND4 NS4.
cps_seg_post.

assert (UE5 : uw_entry m5 (Z_to_bv 64 usp) (usp + -192) lo (bv_unsigned ra :: ras)).
{ apply (sbinit_low_entry (rt_live RT Σ) (rt_frames RT Σ) m m5 s0 ra usp lo ras UE PF (sbi_frame_rec m5 usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR3 eq_refl));
[ulc| clear - SPA; Z.div_mod_to_equations; lia| ulc| ulc]. }
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end;
[ eapply (IH Σ2 PMc) with (lo := lo) (ras := bv_unsigned ra :: ras) (OUT := 0) (STEREO := STEREO); cps_auto | ].
{ rewrite ENBM. reflexivity. }
{ rewrite LV2, LV1. cbn [length]. fold LNBL. clear - LVM. lia. }
{ fold LCRD. rewrite CR2, CR1. clear - CR0 LDP. lia. }
{ rewrite FRS2, FRS1. cbn [length]. fold LDEP. clear - FRM. lia. }
{ rewrite unsigned_lit by ulc. exact UE5. }
{ rewrite unsigned_lit by ulc. eassumption. }
{ rewrite unsigned_lit by ulc. fold LSTK. pose proof (Z.le_max_l LSTK CSTK) as MX. unfold RT_STACK. clear - LOR MX. lia. }
{ rewrite unsigned_lit by ulc. ulc. }
{ rewrite unsigned_lit by ulc. clear - SPA. Z.div_mod_to_equations. lia. }
intros cc6 (Σ3 & AL & LBL & NEWL & Hc6 & LV3 & PERM3 & NDL & LENL & FRS3' & SP3 & CR3 & PO3 & AL8L).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
destruct (ASTA_unpack RT Σ3 PMc _ cc6 Hc6) as (ms6 & PO6 & Hc6'). clear Hc6. cbv beta in PO6.
destruct PO6 as (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & RL6).
destruct RS6 as (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & F6 & fc6 & -> & FRM6).
rewrite (unsigned_lit (usp + -192)) in * by ulc.
cps_unpack_tr PRES6 m5.
assert (SUBF3 : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT Σ3)) by (intros e He; rewrite FRS3'; exact (SUBF2 e He)).
assert (SUBL3 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ3)) by (intros e He; rewrite LV3; apply in_app_iff; right; exact (SUBL2 e He)).
assert (LIVEL : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT Σ3)).
{ intros b Hb. rewrite LV3. apply in_app_iff. left. apply (Permutation_in _ (Permutation_sym PERM3)). unfold blocks_live. apply (in_map (fun b => (blk_addr b, blk_size b))). exact Hb. }
assert (NAL : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> outside (blocks_ivs LBL) a).
{ intros a Ha. apply outside_blocks_ivs. intros b Hb.
apply (newchunks_apart Σ Σ3 m6 NEWL (rt_live RT Σ2) usp a (blk_addr b) (blk_size b) ART6 LV3 SUBF3 ltac:(rewrite SP3, SP2; exact SP1) ltac:(ulc)).
- apply (Permutation_in _ (Permutation_sym PERM3)). unfold blocks_live. apply (in_map (fun b => (blk_addr b, blk_size b))). exact Hb.
- apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) usp _ (rt_frames RT Σ) usp a Ha); [exact SUBL2| auto| lia]. }
sigma_app LV3 FRS3' SP3.
destruct (drep_head 0 STEREO m6 AL _ LBL RL6) as (nl & HAL & NLP & AL8).
pose proof (LIVEL _ HAL) as INAL. unfold blk_addr, blk_size in INAL. cbn [fst snd] in INAL.
destruct (live_below_lo RT AF Σ3 m6 AL nl lo ART6 INAL LOW) as (AL0 & AL1 & _).
destruct (af_acc_live RT AF Σ3 m6 S 160 ART6 INL) as (_ & ACS6).
assert (OBS6 : aobj bsegs m6 S 160) by (split; [lia|]; split; [ulc| exact ACS6]).
assert (OBSM6 : aobj bsegs m6 SM 216) by (apply (aobj_lit RT AF Σ3 m6 SM 216 ART6 SMLIT); ulc).
destruct (MODEK m6 (AF_LIB Σ3 m6 ART6)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & g1' & g2' & lf' & fg' & sm0' & sm1' & sm2' & sm3' & sm4' & sm5' & sm6' & sm7' & pad' & _ & NS6 & LPAD').
cps_hide.

cps_seg (sbinit_w4 usp lo S MP SM NBM AL f sf fs sfs dsm).
{ clear - AL0 AL1 NLP LO192 SPT. unfold USTACK_TOP in SPT. lia. }
destruct POST as (m7 & ya3 & ya4 & ya5 & ya6 & ya7 & -> & MU7 & WM7 & MI7 & ST7 & X7 & FR7).
assert (BOUTL : forall b x, In b LBL -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x Hb Hx. pose proof (LIVEL b Hb) as LB.
destruct (live_below_lo RT AF Σ3 m6 _ _ lo ART6 LB LOW) as (_ & B1 & _).
destruct (frame_live_apart RT AF Σ3 m6 f 0%nat _ _ ART6 INF LB) as (B2 & B3). change (fs_size 0) with 64 in B2, B3. rewrite SHF0, <- SHF in B3.
pose proof (new_old_apart Σ3 m6 NEWL (rt_live RT Σ2) _ _ S 160 ART6 LV3
ltac:(apply (Permutation_in _ (Permutation_sym PERM3)); unfold blocks_live; apply (in_map (fun b => (blk_addr b, blk_size b))); exact Hb)
ltac:(rewrite LV2; left; reflexivity)) as B4.
clear - B1 B2 B3 B4 Hx. lia. }
assert (SNL : ~ In S (map blk_id LBL)).
{ intros Hin. apply in_map_iff in Hin. destruct Hin as (b & Eb & Hb). unfold blk_id in Eb.
pose proof (drep_sizes_pos _ _ _ _ _ _ RL6 b Hb) as PB. destruct (BOUTL b (blk_addr b) Hb ltac:(lia)) as (_ & B & _). clear - B Eb. lia. }
pose proof (agree_blocks_of_munch bsegs _ m6 m7 LBL MU7 WM7
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1 LO192; cbn [outside]; repeat split; lia)) as AG7.
eapply decst_rep_agree in RL6; [| exact AG7]. clear AG7.
clear X5 FR3 OBS6 OBSM6 NS6 ACS6.
cps_seg_post.

apply (proj1 (rw_cells_app bsegs m7 S [_; _; _; _; _; _; _; _] (_ :: _))) in X7. destruct X7 as [XA X7].
change (Z.of_nat (cells_size _)) with 40 in X7. chunk_uncons X7 as XP. replace (S + 40 + 4) with (S + 44) in X7 by lia.
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end;
[ eapply (ctl_gsr_live_all RT AF SM0 AF_LIB (init_dec lowmo) Σ3 PMc) with (OUT := 0) (STEREO := STEREO) (LBD := LBL) (P := S + 40) (lo := lo) (pb := S) (nb := 160); cps_auto | ].
{ exists w0. exact XP. }
{ rewrite DDL, FRS3', FRS2, FRS1. cbn [length]. fold LDEP. clear - FRM. lia. }
{ rewrite DDL. fold LDEP. clear - CR3 CR2 CR1 CR0 LCR LDP. fold LCRD in CR3. lia. }
{ rewrite unsigned_lit by ulc. eassumption. }
{ rewrite unsigned_lit by ulc. fold CSTK. pose proof (Z.le_max_r LSTK CSTK) as MX. unfold RT_STACK. clear - LOR MX. lia. }
{ rewrite unsigned_lit by ulc. ulc. }
{ rewrite unsigned_lit by ulc. clear - SPA. Z.div_mod_to_equations. lia. }
intros cc8 (Σ4 & Hc8 & LV4 & FRS4 & SP4 & CR4 & PO4).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
destruct (ASTA_unpack RT Σ4 PMc _ cc8 Hc8) as (ms8 & PO8 & Hc8'). clear Hc8. cbv beta in PO8.
destruct PO8 as (m8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & RL8 & XP8 & RNG8).
destruct RS8 as (yt0 & yt1 & yt2 & yb1 & yb2 & yb3 & yb4 & yb5 & yb6 & yb7 & yt3 & yt4 & yt5 & yt6 & F8 & fc8 & -> & FRM8).
rewrite (unsigned_lit (usp + -192)) in * by ulc.
replace (S + 40 + 4) with (S + 44) in PRES8 by lia.
assert (OUTB : forall x, (lo <= x \/ (S <= x < S + 160) \/ (f <= x < f + 64) \/ (sf <= x < sf + 8)) -> outside (blocks_ivs LBL) x).
{ intros x Hx. apply outside_blocks_ivs. intros b Hb Hin. pose proof (BOUTL b x Hb Hin) as H1. clear - Hx H1. lia. }
xfp PRES8 WM8 OUTB XA. xfp PRES8 WM8 OUTB X7. xfp PRES8 WM8 OUTB FR7. xfp PRES8 WM8 OUTB FRB3. xfp PRES8 WM8 OUTB FRS3.
assert (PF8 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp [] m m8).
{ apply (pres_fp_trans _ _ _ _ m m7 m8 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ3) (rt_frames RT Σ3) (usp + -192) _ m7 m8 PRES8); [exact SUBL3| exact SUBF3| lia|].
intros x Hx _. cbn [outside]. split; [pose proof (NAS x Hx) as N; clear - N; cbn [fst snd]; lia| exact (NAL x Hx)]. }
clear PF PRES8 RL6 XP. rename PF8 into PF.
cps_sigma LV4 FRS4 SP4.
repeat match goal with A : X14x.ART RT _ m7 |- _ => clear A | A : mem_inv bsegs m7 |- _ => clear A | A : stk bsegs m7 _ _ |- _ => clear A end.
set (lr := fst (speex_decoder_ctl (init_dec lowmo) CtlGetSamplingRate)) in *.
assert (LRV : lr = match lowmo with ModeNB => 8000 | ModeWB => 16000 | ModeUWB => 32000 end) by (subst lr; apply init_low_rate).
assert (LRR : - 2^30 <= lr < 2^30) by (rewrite LRV; generalize lowmo; intros [| |]; split; vm_compute; first [reflexivity | (intro X; discriminate X)]).
assert (ALR : 0 < AL < 2^63) by (clear - AL0 AL1 NLP LO192 SPT; unfold USTACK_TOP in SPT; lia).
pose proof (rw_cells_join _ _ _ _ _ XA (rw_cells_join _ _ _ _ _ XP8 X7 ltac:(cbn; lia)) ltac:(cbn; lia)) as X8. cbn [app] in X8. clear XA XP8 X7.
destruct (af_acc_live RT AF Σ4 m8 S 160 ART8 INL) as (_ & ACS8).
assert (OBS8 : aobj bsegs m8 S 160) by (split; [lia|]; split; [ulc| exact ACS8]).
apply (proj1 (rw_cells_app bsegs m8 f [_; _; _; _] (_ :: _))) in FRB3. destruct FRB3 as [FB0 FB1].
change (Z.of_nat (cells_size _)) with 32 in FB1. chunk_uncons FB1 as TMP. replace (f + 32 + 4) with (f + 36) in FB1 by lia.
clear LPAD LPAD'. cps_hide.

cps_seg (sbinit_w5 usp S SM AL f sf lr).
{ reflexivity. } { reflexivity. }
destruct POST as (m9 & -> & MU9 & WM9 & MI9 & X9 & TMP9).
pose proof (agree_blocks_of_munch bsegs _ m8 m9 LBL MU9 WM9
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)) as AG9.
eapply decst_rep_agree in RL8; [| exact AG9]. clear AG9.
clear X8 TMP OBS8 ACS8.
cps_seg_post.

assert (F8' : f mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
assert (ACT : acc bsegs m9 (f + 32) 4).
{ apply (acc_ushadow bsegs m9 (f + 32) 4); [clear - F8'; Z.div_mod_to_equations; lia| lia| lia|].
replace (shad (f + 32)) with (sf + 4) by (rewrite SHF; unfold shad; clear - F8'; Z.div_mod_to_equations; lia).
destruct FRS3 as [[_ BY] _]. cbn [cells_bytes cbytes app] in BY.
change [Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 4; Z_to_bv 8 (-13); Z_to_bv 8 (-13); Z_to_bv 8 (-13)]
with ([Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-15)] ++ [Z_to_bv 8 4] ++ [Z_to_bv 8 (-13); Z_to_bv 8 (-13); Z_to_bv 8 (-13)]) in BY.
apply bytes_at_app in BY. destruct BY as [_ BY]. apply bytes_at_app in BY. destruct BY as [BY _]. exact BY. }
assert (PRE9 : creq_pre STEREO m9 AL (init_dec lowmo) (f + 32) (CtlSetWideband 1)).
{ cbn [creq_pre]. exists (Z_to_bv 64 1). split; [exact TMP9|]. split; [reflexivity| lia]. }
assert (M4f : (f + 32) mod 4 = 0) by (clear - F8'; Z.div_mod_to_equations; lia).
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end;
[ eapply (ctl_cps_all RT AF SM0 AF_LIB (init_dec lowmo) Σ4 PMc) with (OUT := 0) (STEREO := STEREO) (LBD := LBL) (r := CtlSetWideband 1) (P := f + 32) (lo := lo) (fp := f) (kp := 0%nat); cps_auto | ].
{ cbn [creq_ok]. right. reflexivity. }
{ intros b Hb. rewrite LV4. exact (LIVEL b Hb). }
{ cbn [creq_size]. change (fs_size 0) with 64. lia. }
{ rewrite DDL, FRS4, FRS3', FRS2, FRS1. cbn [length]. fold LDEP. clear - FRM. lia. }
{ rewrite DDL in CR4 |- *. fold LDEP in CR4 |- *. fold LCRD in CR3. clear - CR4 CR3 CR2 CR1 CR0 LCR LDP. lia. }
{ rewrite unsigned_lit by ulc. eassumption. }
{ rewrite unsigned_lit by ulc. fold CSTK. pose proof (Z.le_max_r LSTK CSTK) as MX. unfold RT_STACK. clear - LOR MX. lia. }
{ rewrite unsigned_lit by ulc. ulc. }
{ rewrite unsigned_lit by ulc. clear - SPA. Z.div_mod_to_equations. lia. }
intros cc10 (Σ5 & Hc10 & LV5 & FRS5 & SP5 & CR5 & PO5).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
destruct (ASTA_unpack RT Σ5 PMc _ cc10 Hc10) as (ms10 & PO10 & Hc10'). clear Hc10. cbv beta in PO10.
destruct PO10 as (m10 & RS10 & (ART10 & MI10 & WM10 & ST10) & PRES10 & RL10 & CP10 & ACP10).
destruct RS10 as (xt0 & xt1' & xt2 & xb1 & xb2 & xb3 & xb4 & xb5 & xb6 & xb7 & xt3 & xt4 & xt5 & xt6 & F10 & fc10 & -> & FRM10).
rewrite (unsigned_lit (usp + -192)) in * by ulc.
cbn [creq_ivs creq_size app] in PRES10. replace (f + 32 + 4) with (f + 36) in PRES10 by lia.
xfp PRES10 WM10 OUTB X9. xfp PRES10 WM10 OUTB FR7. xfp PRES10 WM10 OUTB FB0. xfp PRES10 WM10 OUTB FB1. xfp PRES10 WM10 OUTB FRS3.
assert (PF10 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp [] m m10).
{ apply (pres_fp_trans _ _ _ _ m m9 m10 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ4) (rt_frames RT Σ4) (usp + -192) _ m9 m10 PRES10);
[intros e He; rewrite LV4; exact (SUBL3 e He)| intros e He; rewrite FRS4; exact (SUBF3 e He)| lia|].
intros x Hx _. cbn [outside]. split; [pose proof (NAF x Hx) as (N & _); clear - N; cbn [fst snd]; lia| exact (NAL x Hx)]. }
clear PF PRES10 RL8 TMP9 PRE9. rename PF10 into PF.
cps_sigma LV5 FRS5 SP5.
repeat match goal with A : X14x.ART RT _ m9 |- _ => clear A | A : mem_inv bsegs m9 |- _ => clear A | A : stk bsegs m9 _ _ |- _ => clear A end.

destruct (af_acc_live RT AF Σ5 m10 S 160 ART10 INL) as (_ & ACS10).
assert (OBS10 : aobj bsegs m10 S 160) by (split; [lia|]; split; [ulc| exact ACS10]).
assert (OBSM10 : aobj bsegs m10 SM 216) by (apply (aobj_lit RT AF Σ5 m10 SM 216 ART10 SMLIT); ulc).
destruct (MODEK m10 (AF_LIB Σ5 m10 ART10)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & h1 & h2 & hlf & hfg & hm0 & hm1 & hm2 & hm3 & hm4 & hm5 & hm6 & hm7 & hpad & _ & NS10 & LPAD10).
cps_hide.
cps_seg (sbinit_w6 usp S SM NBM f sf fs sfs dsm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ zb4 zb4).
destruct POST as (m11 & za2' & za3' & -> & MU11 & WM11 & MI11 & X11).
pose proof (agree_blocks_of_munch bsegs _ m10 m11 LBL MU11 WM11
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)) as AG11.
eapply decst_rep_agree in RL10; [| exact AG11]. clear AG11.
clear X9 OBS10 OBSM10 NS10 ACS10 LPAD10.
cps_seg_post.
assert (LEN5 : Z.of_nat (length (rt_live RT Σ5)) = Z.of_nat (length (rt_live RT Σ)) + 1 + LNBL).
{ rewrite LV5, LV4, LV3, length_app, LV2, LV1. cbn [length]. fold LNBL in LENL. clear - LENL. lia. }
assert (GEO' : sfs = 40 \/ sfs = 80) by (clear - GEO; unfold hid in GEO; lia).
assert (SUBF5 : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT Σ5)) by (intros e He; rewrite FRS5, FRS4; exact (SUBF3 e He)).
assert (SUBL5 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ5)) by (intros e He; rewrite LV5, LV4; exact (SUBL3 e He)).
assert (LIVEL5 : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT Σ5)) by (intros b Hb; rewrite LV5, LV4; exact (LIVEL b Hb)).
assert (CRD5 : 0 <= rt_credit RT Σ5).
{ rewrite DDL in CR4, CR5. fold LDEP in CR4, CR5. fold LCRD in CR3. clear - CR5 CR4 CR3 CR2 CR1 CR0 LCR LDP. lia. }

set (N72 := if sfs =? 40 then 160 else 320) in *.
assert (N72R : 160 <= N72 <= 320) by (subst N72; destruct GEO' as [->| ->]; cbn; lia).
assert (N72E : N72 = 4 * sfs) by (subst N72; destruct GEO' as [->| ->]; reflexivity).
assert (MC256 : mcost 256 = 0) by reflexivity. assert (MC32 : mcost 32 = 0) by reflexivity. assert (MC16 : mcost 16 = 0) by reflexivity. assert (MC64 : mcost 64 = 0) by reflexivity.
assert (MC72 : mcost N72 = 0) by (unfold mcost; replace (N72 <=? 64512) with true by (symmetry; apply Z.leb_le; lia); reflexivity).
assert (WMT5 : wmono bsegs m m11) by cps_wmono. clear WM1 WM2 WM3 WM4 WM5 WM6 WM7 WM8 WM9 WM10 WM11.
assert (LVT5 : rt_live RT Σ5 = NEWL ++ (S, 160) :: rt_live RT Σ) by (rewrite LV5, LV4, LV3, LV2, LV1; reflexivity).
assert (FRT5 : rt_frames RT Σ5 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRS5, FRS4, FRS3', FRS2; exact FRS1).
assert (SPT5 : rt_sp0 RT Σ5 = rt_sp0 RT Σ) by (rewrite SP5, SP4, SP3, SP2; exact SP1).
assert (POT5 : rt_pois RT Σ5 = rt_pois RT Σ) by (rewrite PO5, PO4, PO3, PO2; exact PO1).
assert (CRT5 : rt_credit RT Σ - init_credit mo <= rt_credit RT Σ5 <= rt_credit RT Σ).
{ rewrite CRL. fold LCRD LDEP. rewrite DDL in CR4, CR5. fold LDEP in CR4, CR5. fold LCRD in CR3. clear - CR5 CR4 CR3 CR2 CR1 LCR LDP. lia. }
clear LV5 LV4 LV3 LV2 LV1 FRS5 FRS4 FRS3' FRS2 FRS1 SP5 SP4 SP3 SP2 SP1 PO5 PO4 PO3 PO2 PO1 CR5 CR4 CR3 CR2 CR1.
pose proof (zbufs_nil m11) as ZB5.
assert (LIVEB5 : blocks_in_live RT Σ5 []) by (intros b []).
assert (BOUT5 : forall b x, In b (@nil block) -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)) by (intros b x []).
clear FB1 CP10 ACP10.

assert (UWG0 : unwind_ch m11 (Z_to_bv 64 774028) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))).
{ apply (sbinit_site_ch (rt_live RT Σ) (rt_frames RT Σ) m m11 s0 ra usp lo ras 774028 UE PF (sbi_frame_rec m11 usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR7 eq_refl));
[apply TRS; unfold SBINIT_SITES; cbn [In]; tauto| ulc| clear - SPA; Z.div_mod_to_equations; lia| ulc| ulc| lia]. }
cps_rt CAL.
all: try (lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- Z.of_nat (length _) < LIVE_MAX => rewrite LEN5; clear - LVM LNB; lia
| |- mcost _ <= _ => replace (256 * 1) with 256 by lia; rewrite MC256; exact CRD5
| |- _ <= _ < _ => clear - N72R; lia
| |- _ <= _ <= _ => clear - N72R; lia
end).
intros ccG0 (ΣG0 & G0 & HccG0 & LVG0 & FRSG0 & SPG0 & CRG0 & POSG0 & AL16G0 & TOPG0 & POG0).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
replace (256 * 1) with 256 in * by lia. rewrite MC256 in CRG0. rewrite Z.sub_0_r in CRG0.
revert X11 FR7 FB0 FRS3.
cps_unpack HccG0 as (mG0 & RSG0 & (ARTG0 & MIG0 & WMG0 & STG0) & PRESG0 & WRG0 & ACG0 & BYG0).
intros X11 FR7 FB0 FRS3.
apply (rw_cells_pres_live _ _ _ m11 mG0 _ _ 160 S 160 PRESG0 WMG0) in X11; [| reflexivity| exact INL| lia| lia].
apply (rw_cells_pres_stack _ _ _ m11 mG0 _ _ 192 PRESG0 WMG0) in FR7; [| reflexivity| lia| clear - SPT; unfold USTACK_TOP; lia].
apply (rw_cells_pres_frame _ _ _ m11 mG0 _ _ 32 f 0%nat PRESG0 WMG0) in FB0; [| reflexivity| exact INF| lia| change (fs_size 0) with 64; lia].
apply (rw_cells_pres_fshadow _ _ _ m11 mG0 _ _ 8 f 0%nat PRESG0 WMG0) in FRS3; [| reflexivity| exact INF| rewrite <- SHF; lia| change (fs_size 0) with 64; rewrite SHF0; lia].
pose proof (agree_blocks_of_pres RT Σ5 (rt_frames RT Σ5) (usp + -192) m11 mG0 LBL PRESG0 WMG0 LIVEL5) as AGG0.
eapply decst_rep_agree in RL10; [| exact AGG0]. clear AGG0.
pose proof (zbufs_agree m11 mG0 [] ZB5 (agree_blocks_of_pres RT Σ5 (rt_frames RT Σ5) (usp + -192) m11 mG0 [] PRESG0 WMG0 LIVEB5)) as ZB0G0.
clear PRESG0 ZB5.
assert (SUBFG0 : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT ΣG0)) by (intros e He; rewrite FRSG0; exact (SUBF5 e He)).
assert (SUBLG0 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT ΣG0)) by (intros e He; rewrite LVG0; right; exact (SUBL5 e He)).
assert (LIVELG0 : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT ΣG0)) by (intros b Hb; rewrite LVG0; right; exact (LIVEL5 b Hb)).
assert (LIVEBG0 : blocks_in_live RT ΣG0 ((tt, G0, 256) :: [])) by (intros b [<-|Hb]; rewrite LVG0; [left; reflexivity| right; exact (LIVEB5 b Hb)]).
assert (LENG0 : Z.of_nat (length (rt_live RT ΣG0)) = Z.of_nat (length (rt_live RT Σ)) + 1 + LNBL + 1) by (rewrite LVG0; cbn [length]; rewrite Nat2Z.inj_succ, LEN5; lia).
assert (CRDG0 : 0 <= rt_credit RT ΣG0) by (rewrite CRG0; exact CRD5).
assert (ING0 : In (G0, 256) (rt_live RT ΣG0)) by (rewrite LVG0; left; reflexivity).
pose proof (new_old_apart ΣG0 mG0 [(G0, 256)] (rt_live RT Σ5) G0 256 S 160 ARTG0 LVG0 ltac:(left; reflexivity) INL) as APG0.
cps_sigma LVG0 FRSG0 SPG0.
destruct (live_below_lo RT AF ΣG0 mG0 G0 256 lo ARTG0 ING0 LOW) as (_ & LOG0 & _).
destruct (frame_live_apart RT AF ΣG0 mG0 f 0%nat G0 256 ARTG0 INF ING0) as (FA1G0 & FA2G0). change (fs_size 0) with 64 in FA1G0, FA2G0. rewrite SHF0, <- SHF in FA2G0.
assert (BOUTG0 : forall b x, In b ((tt, G0, 256) :: []) -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x [<-|Hb] Hx; [unfold blk_addr, blk_size in Hx; cbn [fst snd] in Hx; clear - Hx LOG0 APG0 FA1G0 FA2G0; lia| exact (BOUT5 b x Hb Hx)]. }
assert (BRG0 : 0 < G0 < 2^63) by (clear - POSG0 TOPG0 N72R; unfold USTACK_TOP in TOPG0; lia).
assert (LVTG0 : rt_live RT ΣG0 = blocks_live ((tt, G0, 256) :: []) ++ NEWL ++ (S, 160) :: rt_live RT Σ) by (rewrite LVG0, LVT5; reflexivity).
assert (FRTG0 : rt_frames RT ΣG0 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRSG0; exact FRT5).
assert (SPTG0 : rt_sp0 RT ΣG0 = rt_sp0 RT Σ) by (rewrite SPG0; exact SPT5).
assert (POTG0 : rt_pois RT ΣG0 = rt_pois RT Σ) by (rewrite POG0; exact POT5).
assert (CRTG0 : rt_credit RT Σ - init_credit mo <= rt_credit RT ΣG0 <= rt_credit RT Σ) by (rewrite CRG0; exact CRT5).
assert (AL8G0 : G0 mod 8 = 0) by (clear - AL16G0; Z.div_mod_to_equations; lia).
clear LVG0 FRSG0 SPG0 POG0 CRG0 LVT5 FRT5 SPT5 POT5 CRT5 POSG0 AL16G0 TOPG0 SUBF5 SUBL5 LIVEL5 LIVEB5 LEN5 CRD5 BOUT5.
pose proof (zbufs_cons mG0 G0 256 [] ltac:(clear - N72R; lia) (zero_chunk mG0 G0 256 ltac:(clear - N72R; lia) WRG0 BYG0) ZB0G0) as ZBG0.
clear WRG0 BYG0 ZB0G0 ING0 APG0 LOG0 FA1G0 FA2G0 ACG0.
repeat match goal with H : In (G0, _) (rt_live RT _) |- _ => clear H end.
destruct (af_acc_live RT AF ΣG0 mG0 S 160 ARTG0 INL) as (_ & ACSG0).
assert (OBSG0 : aobj bsegs mG0 S 160) by (split; [lia|]; split; [ulc| exact ACSG0]).
cps_hide.
cps_seg (sbinit_w7 usp lo S SM G0 f sf sfs). { reflexivity. } { reflexivity. }
destruct POST as (mcG0 & wa2G0 & wa3G0 & -> & MUG0 & WM'G0 & MI'G0 & XG0 & FRG0).
repeat match goal with H : context [if sfs =? 40 then ?a else ?a] |- _ => replace (if sfs =? 40 then a else a) with a in H by (destruct (sfs =? 40); reflexivity) end.
pose proof (agree_blocks_of_munch bsegs _ mG0 mcG0 LBL MUG0 WM'G0
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)) as AG'G0.
eapply decst_rep_agree in RL10; [| exact AG'G0]. clear AG'G0.
pose proof (zbufs_agree mG0 mcG0 _ ZBG0 (agree_blocks_of_munch bsegs _ mG0 mcG0 _ MUG0 WM'G0
ltac:(intros b x Hb Hx; pose proof (BOUTG0 b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia))) as ZCG0.
clear X11 FR7 OBSG0 ACSG0 UWG0 ZBG0 BRG0.
revert FB0 FRS3.
cps_seg_post.
intros FB0 FRS3.
eapply rw_cells_transport in FB0; [| exact MUG0| exact WM'G0| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 32; split; [clear - FLA1; unfold hid in FLA1; lia| exact I]].
eapply rw_cells_transport in FRS3; [| exact MUG0| exact WM'G0| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 8; split; [clear - FLA2; unfold hid in FLA2; lia| exact I]].
assert (WMTG0 : wmono bsegs m mcG0) by cps_wmono. clear WMG0 WM'G0 WMT5 MUG0.

assert (UWG1 : unwind_ch mcG0 (Z_to_bv 64 774064) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))).
{ apply (sbinit_site_ch (rt_live RT Σ) (rt_frames RT Σ) m mcG0 s0 ra usp lo ras 774064 UE PF (sbi_frame_rec mcG0 usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRG0 eq_refl));
[apply TRS; unfold SBINIT_SITES; cbn [In]; tauto| ulc| clear - SPA; Z.div_mod_to_equations; lia| ulc| ulc| lia]. }
cps_rt CAL.
all: try (lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- Z.of_nat (length _) < LIVE_MAX => rewrite LENG0; clear - LVM LNB; lia
| |- mcost _ <= _ => replace (256 * 1) with 256 by lia; rewrite MC256; exact CRDG0
| |- _ <= _ < _ => clear - N72R; lia
| |- _ <= _ <= _ => clear - N72R; lia
end).
intros ccG1 (ΣG1 & G1 & HccG1 & LVG1 & FRSG1 & SPG1 & CRG1 & POSG1 & AL16G1 & TOPG1 & POG1).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
replace (256 * 1) with 256 in * by lia. rewrite MC256 in CRG1. rewrite Z.sub_0_r in CRG1.
revert XG0 FRG0 FB0 FRS3.
cps_unpack HccG1 as (mG1 & RSG1 & (ARTG1 & MIG1 & WMG1 & STG1) & PRESG1 & WRG1 & ACG1 & BYG1).
intros XG0 FRG0 FB0 FRS3.
apply (rw_cells_pres_live _ _ _ mcG0 mG1 _ _ 160 S 160 PRESG1 WMG1) in XG0; [| reflexivity| exact INL| lia| lia].
apply (rw_cells_pres_stack _ _ _ mcG0 mG1 _ _ 192 PRESG1 WMG1) in FRG0; [| reflexivity| lia| clear - SPT; unfold USTACK_TOP; lia].
apply (rw_cells_pres_frame _ _ _ mcG0 mG1 _ _ 32 f 0%nat PRESG1 WMG1) in FB0; [| reflexivity| exact INF| lia| change (fs_size 0) with 64; lia].
apply (rw_cells_pres_fshadow _ _ _ mcG0 mG1 _ _ 8 f 0%nat PRESG1 WMG1) in FRS3; [| reflexivity| exact INF| rewrite <- SHF; lia| change (fs_size 0) with 64; rewrite SHF0; lia].
pose proof (agree_blocks_of_pres RT ΣG0 (rt_frames RT ΣG0) (usp + -192) mcG0 mG1 LBL PRESG1 WMG1 LIVELG0) as AGG1.
eapply decst_rep_agree in RL10; [| exact AGG1]. clear AGG1.
pose proof (zbufs_agree mcG0 mG1 ((tt, G0, 256) :: []) ZCG0 (agree_blocks_of_pres RT ΣG0 (rt_frames RT ΣG0) (usp + -192) mcG0 mG1 ((tt, G0, 256) :: []) PRESG1 WMG1 LIVEBG0)) as ZB0G1.
clear PRESG1 ZCG0.
assert (SUBFG1 : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT ΣG1)) by (intros e He; rewrite FRSG1; exact (SUBFG0 e He)).
assert (SUBLG1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT ΣG1)) by (intros e He; rewrite LVG1; right; exact (SUBLG0 e He)).
assert (LIVELG1 : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT ΣG1)) by (intros b Hb; rewrite LVG1; right; exact (LIVELG0 b Hb)).
assert (LIVEBG1 : blocks_in_live RT ΣG1 ((tt, G1, 256) :: ((tt, G0, 256) :: []))) by (intros b [<-|Hb]; rewrite LVG1; [left; reflexivity| right; exact (LIVEBG0 b Hb)]).
assert (LENG1 : Z.of_nat (length (rt_live RT ΣG1)) = Z.of_nat (length (rt_live RT Σ)) + 1 + LNBL + 2) by (rewrite LVG1; cbn [length]; rewrite Nat2Z.inj_succ, LENG0; lia).
assert (CRDG1 : 0 <= rt_credit RT ΣG1) by (rewrite CRG1; exact CRDG0).
assert (ING1 : In (G1, 256) (rt_live RT ΣG1)) by (rewrite LVG1; left; reflexivity).
pose proof (new_old_apart ΣG1 mG1 [(G1, 256)] (rt_live RT ΣG0) G1 256 S 160 ARTG1 LVG1 ltac:(left; reflexivity) INL) as APG1.
cps_sigma LVG1 FRSG1 SPG1.
destruct (live_below_lo RT AF ΣG1 mG1 G1 256 lo ARTG1 ING1 LOW) as (_ & LOG1 & _).
destruct (frame_live_apart RT AF ΣG1 mG1 f 0%nat G1 256 ARTG1 INF ING1) as (FA1G1 & FA2G1). change (fs_size 0) with 64 in FA1G1, FA2G1. rewrite SHF0, <- SHF in FA2G1.
assert (BOUTG1 : forall b x, In b ((tt, G1, 256) :: ((tt, G0, 256) :: [])) -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x [<-|Hb] Hx; [unfold blk_addr, blk_size in Hx; cbn [fst snd] in Hx; clear - Hx LOG1 APG1 FA1G1 FA2G1; lia| exact (BOUTG0 b x Hb Hx)]. }
assert (BRG1 : 0 < G1 < 2^63) by (clear - POSG1 TOPG1 N72R; unfold USTACK_TOP in TOPG1; lia).
assert (LVTG1 : rt_live RT ΣG1 = blocks_live ((tt, G1, 256) :: ((tt, G0, 256) :: [])) ++ NEWL ++ (S, 160) :: rt_live RT Σ) by (rewrite LVG1, LVTG0; reflexivity).
assert (FRTG1 : rt_frames RT ΣG1 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRSG1; exact FRTG0).
assert (SPTG1 : rt_sp0 RT ΣG1 = rt_sp0 RT Σ) by (rewrite SPG1; exact SPTG0).
assert (POTG1 : rt_pois RT ΣG1 = rt_pois RT Σ) by (rewrite POG1; exact POTG0).
assert (CRTG1 : rt_credit RT Σ - init_credit mo <= rt_credit RT ΣG1 <= rt_credit RT Σ) by (rewrite CRG1; exact CRTG0).
assert (AL8G1 : G1 mod 8 = 0) by (clear - AL16G1; Z.div_mod_to_equations; lia).
clear LVG1 FRSG1 SPG1 POG1 CRG1 LVTG0 FRTG0 SPTG0 POTG0 CRTG0 POSG1 AL16G1 TOPG1 SUBFG0 SUBLG0 LIVELG0 LIVEBG0 LENG0 CRDG0 BOUTG0.
pose proof (zbufs_cons mG1 G1 256 ((tt, G0, 256) :: []) ltac:(clear - N72R; lia) (zero_chunk mG1 G1 256 ltac:(clear - N72R; lia) WRG1 BYG1) ZB0G1) as ZBG1.
clear WRG1 BYG1 ZB0G1 ING1 APG1 LOG1 FA1G1 FA2G1 ACG1.
repeat match goal with H : In (G1, _) (rt_live RT _) |- _ => clear H end.
destruct (af_acc_live RT AF ΣG1 mG1 S 160 ARTG1 INL) as (_ & ACSG1).
assert (OBSG1 : aobj bsegs mG1 S 160) by (split; [lia|]; split; [ulc| exact ACSG1]).
cps_hide.
cps_seg (sbinit_w8 usp lo S SM G1 f sf sfs). { reflexivity. } { reflexivity. }
destruct POST as (mcG1 & wa2G1 & wa3G1 & -> & MUG1 & WM'G1 & MI'G1 & XG1 & FRG1).
repeat match goal with H : context [if sfs =? 40 then 160 else 320] |- _ => change (if sfs =? 40 then 160 else 320) with N72 in H end.
repeat match goal with H : context [if sfs =? 40 then ?a else ?a] |- _ => replace (if sfs =? 40 then a else a) with a in H by (destruct (sfs =? 40); reflexivity) end.
pose proof (agree_blocks_of_munch bsegs _ mG1 mcG1 LBL MUG1 WM'G1
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)) as AG'G1.
eapply decst_rep_agree in RL10; [| exact AG'G1]. clear AG'G1.
pose proof (zbufs_agree mG1 mcG1 _ ZBG1 (agree_blocks_of_munch bsegs _ mG1 mcG1 _ MUG1 WM'G1
ltac:(intros b x Hb Hx; pose proof (BOUTG1 b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia))) as ZCG1.
clear XG0 FRG0 OBSG1 ACSG1 UWG1 ZBG1 BRG1.
revert FB0 FRS3.
cps_seg_post.
intros FB0 FRS3.
eapply rw_cells_transport in FB0; [| exact MUG1| exact WM'G1| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 32; split; [clear - FLA1; unfold hid in FLA1; lia| exact I]].
eapply rw_cells_transport in FRS3; [| exact MUG1| exact WM'G1| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 8; split; [clear - FLA2; unfold hid in FLA2; lia| exact I]].
assert (WMTG1 : wmono bsegs m mcG1) by cps_wmono. clear WMG1 WM'G1 WMTG0 MUG1.

assert (UWEX : unwind_ch mcG1 (Z_to_bv 64 774112) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))).
{ apply (sbinit_site_ch (rt_live RT Σ) (rt_frames RT Σ) m mcG1 s0 ra usp lo ras 774112 UE PF (sbi_frame_rec mcG1 usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRG1 eq_refl));
[apply TRS; unfold SBINIT_SITES; cbn [In]; tauto| ulc| clear - SPA; Z.div_mod_to_equations; lia| ulc| ulc| lia]. }
cps_rt CAL.
all: try (lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- Z.of_nat (length _) < LIVE_MAX => rewrite LENG1; clear - LVM LNB; lia
| |- mcost _ <= _ => replace (N72 * 1) with N72 by lia; rewrite MC72; exact CRDG1
| |- _ <= _ < _ => clear - N72R; lia
| |- _ <= _ <= _ => clear - N72R; lia
end).
intros ccEX (ΣEX & EX & HccEX & LVEX & FRSEX & SPEX & CREX & POSEX & AL16EX & TOPEX & POEX).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
replace (N72 * 1) with N72 in * by lia. rewrite MC72 in CREX. rewrite Z.sub_0_r in CREX.
revert XG1 FRG1 FB0 FRS3.
cps_unpack HccEX as (mEX & RSEX & (ARTEX & MIEX & WMEX & STEX) & PRESEX & WREX & ACEX & BYEX).
intros XG1 FRG1 FB0 FRS3.
apply (rw_cells_pres_live _ _ _ mcG1 mEX _ _ 160 S 160 PRESEX WMEX) in XG1; [| reflexivity| exact INL| lia| lia].
apply (rw_cells_pres_stack _ _ _ mcG1 mEX _ _ 192 PRESEX WMEX) in FRG1; [| reflexivity| lia| clear - SPT; unfold USTACK_TOP; lia].
apply (rw_cells_pres_frame _ _ _ mcG1 mEX _ _ 32 f 0%nat PRESEX WMEX) in FB0; [| reflexivity| exact INF| lia| change (fs_size 0) with 64; lia].
apply (rw_cells_pres_fshadow _ _ _ mcG1 mEX _ _ 8 f 0%nat PRESEX WMEX) in FRS3; [| reflexivity| exact INF| rewrite <- SHF; lia| change (fs_size 0) with 64; rewrite SHF0; lia].
pose proof (agree_blocks_of_pres RT ΣG1 (rt_frames RT ΣG1) (usp + -192) mcG1 mEX LBL PRESEX WMEX LIVELG1) as AGEX.
eapply decst_rep_agree in RL10; [| exact AGEX]. clear AGEX.
pose proof (zbufs_agree mcG1 mEX ((tt, G1, 256) :: ((tt, G0, 256) :: [])) ZCG1 (agree_blocks_of_pres RT ΣG1 (rt_frames RT ΣG1) (usp + -192) mcG1 mEX ((tt, G1, 256) :: ((tt, G0, 256) :: [])) PRESEX WMEX LIVEBG1)) as ZB0EX.
clear PRESEX ZCG1.
assert (SUBFEX : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT ΣEX)) by (intros e He; rewrite FRSEX; exact (SUBFG1 e He)).
assert (SUBLEX : forall e, In e (rt_live RT Σ) -> In e (rt_live RT ΣEX)) by (intros e He; rewrite LVEX; right; exact (SUBLG1 e He)).
assert (LIVELEX : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT ΣEX)) by (intros b Hb; rewrite LVEX; right; exact (LIVELG1 b Hb)).
assert (LIVEBEX : blocks_in_live RT ΣEX ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))) by (intros b [<-|Hb]; rewrite LVEX; [left; reflexivity| right; exact (LIVEBG1 b Hb)]).
assert (LENEX : Z.of_nat (length (rt_live RT ΣEX)) = Z.of_nat (length (rt_live RT Σ)) + 1 + LNBL + 3) by (rewrite LVEX; cbn [length]; rewrite Nat2Z.inj_succ, LENG1; lia).
assert (CRDEX : 0 <= rt_credit RT ΣEX) by (rewrite CREX; exact CRDG1).
assert (INEX : In (EX, N72) (rt_live RT ΣEX)) by (rewrite LVEX; left; reflexivity).
pose proof (new_old_apart ΣEX mEX [(EX, N72)] (rt_live RT ΣG1) EX N72 S 160 ARTEX LVEX ltac:(left; reflexivity) INL) as APEX.
cps_sigma LVEX FRSEX SPEX.
destruct (live_below_lo RT AF ΣEX mEX EX N72 lo ARTEX INEX LOW) as (_ & LOEX & _).
destruct (frame_live_apart RT AF ΣEX mEX f 0%nat EX N72 ARTEX INF INEX) as (FA1EX & FA2EX). change (fs_size 0) with 64 in FA1EX, FA2EX. rewrite SHF0, <- SHF in FA2EX.
assert (BOUTEX : forall b x, In b ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))) -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x [<-|Hb] Hx; [unfold blk_addr, blk_size in Hx; cbn [fst snd] in Hx; clear - Hx LOEX APEX FA1EX FA2EX; lia| exact (BOUTG1 b x Hb Hx)]. }
assert (BREX : 0 < EX < 2^63) by (clear - POSEX TOPEX N72R; unfold USTACK_TOP in TOPEX; lia).
assert (LVTEX : rt_live RT ΣEX = blocks_live ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))) ++ NEWL ++ (S, 160) :: rt_live RT Σ) by (rewrite LVEX, LVTG1; reflexivity).
assert (FRTEX : rt_frames RT ΣEX = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRSEX; exact FRTG1).
assert (SPTEX : rt_sp0 RT ΣEX = rt_sp0 RT Σ) by (rewrite SPEX; exact SPTG1).
assert (POTEX : rt_pois RT ΣEX = rt_pois RT Σ) by (rewrite POEX; exact POTG1).
assert (CRTEX : rt_credit RT Σ - init_credit mo <= rt_credit RT ΣEX <= rt_credit RT Σ) by (rewrite CREX; exact CRTG1).
assert (AL8EX : EX mod 8 = 0) by (clear - AL16EX; Z.div_mod_to_equations; lia).
clear LVEX FRSEX SPEX POEX CREX LVTG1 FRTG1 SPTG1 POTG1 CRTG1 POSEX AL16EX TOPEX SUBFG1 SUBLG1 LIVELG1 LIVEBG1 LENG1 CRDG1 BOUTG1.
pose proof (zbufs_cons mEX EX N72 ((tt, G1, 256) :: ((tt, G0, 256) :: [])) ltac:(clear - N72R; lia) (zero_chunk mEX EX N72 ltac:(clear - N72R; lia) WREX BYEX) ZB0EX) as ZBEX.
clear WREX BYEX ZB0EX INEX APEX LOEX FA1EX FA2EX ACEX.
repeat match goal with H : In (EX, _) (rt_live RT _) |- _ => clear H end.
destruct (af_acc_live RT AF ΣEX mEX S 160 ARTEX INL) as (_ & ACSEX).
assert (OBSEX : aobj bsegs mEX S 160) by (split; [lia|]; split; [ulc| exact ACSEX]).
cps_hide.
cps_seg (sbinit_w9 usp lo S SM EX f sf sfs). { reflexivity. } { reflexivity. }
destruct POST as (mcEX & wa2EX & wa3EX & -> & MUEX & WM'EX & MI'EX & XEX & FREX).
repeat match goal with H : context [if sfs =? 40 then ?a else ?a] |- _ => replace (if sfs =? 40 then a else a) with a in H by (destruct (sfs =? 40); reflexivity) end.
pose proof (agree_blocks_of_munch bsegs _ mEX mcEX LBL MUEX WM'EX
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)) as AG'EX.
eapply decst_rep_agree in RL10; [| exact AG'EX]. clear AG'EX.
pose proof (zbufs_agree mEX mcEX _ ZBEX (agree_blocks_of_munch bsegs _ mEX mcEX _ MUEX WM'EX
ltac:(intros b x Hb Hx; pose proof (BOUTEX b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia))) as ZCEX.
clear XG1 FRG1 OBSEX ACSEX UWEX ZBEX BREX.
revert FB0 FRS3.
cps_seg_post.
intros FB0 FRS3.
eapply rw_cells_transport in FB0; [| exact MUEX| exact WM'EX| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 32; split; [clear - FLA1; unfold hid in FLA1; lia| exact I]].
eapply rw_cells_transport in FRS3; [| exact MUEX| exact WM'EX| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 8; split; [clear - FLA2; unfold hid in FLA2; lia| exact I]].
assert (WMTEX : wmono bsegs m mcEX) by cps_wmono. clear WMEX WM'EX WMTG1 MUEX.

assert (UWOQ : unwind_ch mcEX (Z_to_bv 64 774168) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))).
{ apply (sbinit_site_ch (rt_live RT Σ) (rt_frames RT Σ) m mcEX s0 ra usp lo ras 774168 UE PF (sbi_frame_rec mcEX usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FREX eq_refl));
[apply TRS; unfold SBINIT_SITES; cbn [In]; tauto| ulc| clear - SPA; Z.div_mod_to_equations; lia| ulc| ulc| lia]. }
cps_rt CAL.
all: try (lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- Z.of_nat (length _) < LIVE_MAX => rewrite LENEX; clear - LVM LNB; lia
| |- mcost _ <= _ => replace (32 * 1) with 32 by lia; rewrite MC32; exact CRDEX
| |- _ <= _ < _ => clear - N72R; lia
| |- _ <= _ <= _ => clear - N72R; lia
end).
intros ccOQ (ΣOQ & OQ & HccOQ & LVOQ & FRSOQ & SPOQ & CROQ & POSOQ & AL16OQ & TOPOQ & POOQ).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
replace (32 * 1) with 32 in * by lia. rewrite MC32 in CROQ. rewrite Z.sub_0_r in CROQ.
revert XEX FREX FB0 FRS3.
cps_unpack HccOQ as (mOQ & RSOQ & (ARTOQ & MIOQ & WMOQ & STOQ) & PRESOQ & WROQ & ACOQ & BYOQ).
intros XEX FREX FB0 FRS3.
apply (rw_cells_pres_live _ _ _ mcEX mOQ _ _ 160 S 160 PRESOQ WMOQ) in XEX; [| reflexivity| exact INL| lia| lia].
apply (rw_cells_pres_stack _ _ _ mcEX mOQ _ _ 192 PRESOQ WMOQ) in FREX; [| reflexivity| lia| clear - SPT; unfold USTACK_TOP; lia].
apply (rw_cells_pres_frame _ _ _ mcEX mOQ _ _ 32 f 0%nat PRESOQ WMOQ) in FB0; [| reflexivity| exact INF| lia| change (fs_size 0) with 64; lia].
apply (rw_cells_pres_fshadow _ _ _ mcEX mOQ _ _ 8 f 0%nat PRESOQ WMOQ) in FRS3; [| reflexivity| exact INF| rewrite <- SHF; lia| change (fs_size 0) with 64; rewrite SHF0; lia].
pose proof (agree_blocks_of_pres RT ΣEX (rt_frames RT ΣEX) (usp + -192) mcEX mOQ LBL PRESOQ WMOQ LIVELEX) as AGOQ.
eapply decst_rep_agree in RL10; [| exact AGOQ]. clear AGOQ.
pose proof (zbufs_agree mcEX mOQ ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))) ZCEX (agree_blocks_of_pres RT ΣEX (rt_frames RT ΣEX) (usp + -192) mcEX mOQ ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))) PRESOQ WMOQ LIVEBEX)) as ZB0OQ.
clear PRESOQ ZCEX.
assert (SUBFOQ : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT ΣOQ)) by (intros e He; rewrite FRSOQ; exact (SUBFEX e He)).
assert (SUBLOQ : forall e, In e (rt_live RT Σ) -> In e (rt_live RT ΣOQ)) by (intros e He; rewrite LVOQ; right; exact (SUBLEX e He)).
assert (LIVELOQ : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT ΣOQ)) by (intros b Hb; rewrite LVOQ; right; exact (LIVELEX b Hb)).
assert (LIVEBOQ : blocks_in_live RT ΣOQ ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))) by (intros b [<-|Hb]; rewrite LVOQ; [left; reflexivity| right; exact (LIVEBEX b Hb)]).
assert (LENOQ : Z.of_nat (length (rt_live RT ΣOQ)) = Z.of_nat (length (rt_live RT Σ)) + 1 + LNBL + 4) by (rewrite LVOQ; cbn [length]; rewrite Nat2Z.inj_succ, LENEX; lia).
assert (CRDOQ : 0 <= rt_credit RT ΣOQ) by (rewrite CROQ; exact CRDEX).
assert (INOQ : In (OQ, 32) (rt_live RT ΣOQ)) by (rewrite LVOQ; left; reflexivity).
pose proof (new_old_apart ΣOQ mOQ [(OQ, 32)] (rt_live RT ΣEX) OQ 32 S 160 ARTOQ LVOQ ltac:(left; reflexivity) INL) as APOQ.
cps_sigma LVOQ FRSOQ SPOQ.
destruct (live_below_lo RT AF ΣOQ mOQ OQ 32 lo ARTOQ INOQ LOW) as (_ & LOOQ & _).
destruct (frame_live_apart RT AF ΣOQ mOQ f 0%nat OQ 32 ARTOQ INF INOQ) as (FA1OQ & FA2OQ). change (fs_size 0) with 64 in FA1OQ, FA2OQ. rewrite SHF0, <- SHF in FA2OQ.
assert (BOUTOQ : forall b x, In b ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))) -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x [<-|Hb] Hx; [unfold blk_addr, blk_size in Hx; cbn [fst snd] in Hx; clear - Hx LOOQ APOQ FA1OQ FA2OQ; lia| exact (BOUTEX b x Hb Hx)]. }
assert (BROQ : 0 < OQ < 2^63) by (clear - POSOQ TOPOQ N72R; unfold USTACK_TOP in TOPOQ; lia).
assert (LVTOQ : rt_live RT ΣOQ = blocks_live ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))) ++ NEWL ++ (S, 160) :: rt_live RT Σ) by (rewrite LVOQ, LVTEX; reflexivity).
assert (FRTOQ : rt_frames RT ΣOQ = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRSOQ; exact FRTEX).
assert (SPTOQ : rt_sp0 RT ΣOQ = rt_sp0 RT Σ) by (rewrite SPOQ; exact SPTEX).
assert (POTOQ : rt_pois RT ΣOQ = rt_pois RT Σ) by (rewrite POOQ; exact POTEX).
assert (CRTOQ : rt_credit RT Σ - init_credit mo <= rt_credit RT ΣOQ <= rt_credit RT Σ) by (rewrite CROQ; exact CRTEX).
assert (AL8OQ : OQ mod 8 = 0) by (clear - AL16OQ; Z.div_mod_to_equations; lia).
clear LVOQ FRSOQ SPOQ POOQ CROQ LVTEX FRTEX SPTEX POTEX CRTEX POSOQ AL16OQ TOPOQ SUBFEX SUBLEX LIVELEX LIVEBEX LENEX CRDEX BOUTEX.
pose proof (zbufs_cons mOQ OQ 32 ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))) ltac:(clear - N72R; lia) (zero_chunk mOQ OQ 32 ltac:(clear - N72R; lia) WROQ BYOQ) ZB0OQ) as ZBOQ.
clear WROQ BYOQ ZB0OQ INOQ APOQ LOOQ FA1OQ FA2OQ ACOQ.
repeat match goal with H : In (OQ, _) (rt_live RT _) |- _ => clear H end.
destruct (af_acc_live RT AF ΣOQ mOQ S 160 ARTOQ INL) as (_ & ACSOQ).
assert (OBSOQ : aobj bsegs mOQ S 160) by (split; [lia|]; split; [ulc| exact ACSOQ]).
cps_hide.
cps_seg (sbinit_w10 usp lo S SM OQ f sf sfs). { reflexivity. } { reflexivity. }
destruct POST as (mcOQ & wa2OQ & wa3OQ & -> & MUOQ & WM'OQ & MI'OQ & XOQ & FROQ).
repeat match goal with H : context [if sfs =? 40 then ?a else ?a] |- _ => replace (if sfs =? 40 then a else a) with a in H by (destruct (sfs =? 40); reflexivity) end.
pose proof (agree_blocks_of_munch bsegs _ mOQ mcOQ LBL MUOQ WM'OQ
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)) as AG'OQ.
eapply decst_rep_agree in RL10; [| exact AG'OQ]. clear AG'OQ.
pose proof (zbufs_agree mOQ mcOQ _ ZBOQ (agree_blocks_of_munch bsegs _ mOQ mcOQ _ MUOQ WM'OQ
ltac:(intros b x Hb Hx; pose proof (BOUTOQ b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia))) as ZCOQ.
clear XEX FREX OBSOQ ACSOQ UWOQ ZBOQ BROQ.
revert FB0 FRS3.
cps_seg_post.
intros FB0 FRS3.
eapply rw_cells_transport in FB0; [| exact MUOQ| exact WM'OQ| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 32; split; [clear - FLA1; unfold hid in FLA1; lia| exact I]].
eapply rw_cells_transport in FRS3; [| exact MUOQ| exact WM'OQ| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 8; split; [clear - FLA2; unfold hid in FLA2; lia| exact I]].
assert (WMTOQ : wmono bsegs m mcOQ) by cps_wmono. clear WMOQ WM'OQ WMTEX MUOQ.

assert (UWIQ : unwind_ch mcOQ (Z_to_bv 64 774216) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))).
{ apply (sbinit_site_ch (rt_live RT Σ) (rt_frames RT Σ) m mcOQ s0 ra usp lo ras 774216 UE PF (sbi_frame_rec mcOQ usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FROQ eq_refl));
[apply TRS; unfold SBINIT_SITES; cbn [In]; tauto| ulc| clear - SPA; Z.div_mod_to_equations; lia| ulc| ulc| lia]. }
cps_rt CAL.
all: try (lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- Z.of_nat (length _) < LIVE_MAX => rewrite LENOQ; clear - LVM LNB; lia
| |- mcost _ <= _ => replace (32 * 1) with 32 by lia; rewrite MC32; exact CRDOQ
| |- _ <= _ < _ => clear - N72R; lia
| |- _ <= _ <= _ => clear - N72R; lia
end).
intros ccIQ (ΣIQ & IQ & HccIQ & LVIQ & FRSIQ & SPIQ & CRIQ & POSIQ & AL16IQ & TOPIQ & POIQ).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
replace (32 * 1) with 32 in * by lia. rewrite MC32 in CRIQ. rewrite Z.sub_0_r in CRIQ.
revert XOQ FROQ FB0 FRS3.
cps_unpack HccIQ as (mIQ & RSIQ & (ARTIQ & MIIQ & WMIQ & STIQ) & PRESIQ & WRIQ & ACIQ & BYIQ).
intros XOQ FROQ FB0 FRS3.
apply (rw_cells_pres_live _ _ _ mcOQ mIQ _ _ 160 S 160 PRESIQ WMIQ) in XOQ; [| reflexivity| exact INL| lia| lia].
apply (rw_cells_pres_stack _ _ _ mcOQ mIQ _ _ 192 PRESIQ WMIQ) in FROQ; [| reflexivity| lia| clear - SPT; unfold USTACK_TOP; lia].
apply (rw_cells_pres_frame _ _ _ mcOQ mIQ _ _ 32 f 0%nat PRESIQ WMIQ) in FB0; [| reflexivity| exact INF| lia| change (fs_size 0) with 64; lia].
apply (rw_cells_pres_fshadow _ _ _ mcOQ mIQ _ _ 8 f 0%nat PRESIQ WMIQ) in FRS3; [| reflexivity| exact INF| rewrite <- SHF; lia| change (fs_size 0) with 64; rewrite SHF0; lia].
pose proof (agree_blocks_of_pres RT ΣOQ (rt_frames RT ΣOQ) (usp + -192) mcOQ mIQ LBL PRESIQ WMIQ LIVELOQ) as AGIQ.
eapply decst_rep_agree in RL10; [| exact AGIQ]. clear AGIQ.
pose proof (zbufs_agree mcOQ mIQ ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))) ZCOQ (agree_blocks_of_pres RT ΣOQ (rt_frames RT ΣOQ) (usp + -192) mcOQ mIQ ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))) PRESIQ WMIQ LIVEBOQ)) as ZB0IQ.
clear PRESIQ ZCOQ.
assert (SUBFIQ : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT ΣIQ)) by (intros e He; rewrite FRSIQ; exact (SUBFOQ e He)).
assert (SUBLIQ : forall e, In e (rt_live RT Σ) -> In e (rt_live RT ΣIQ)) by (intros e He; rewrite LVIQ; right; exact (SUBLOQ e He)).
assert (LIVELIQ : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT ΣIQ)) by (intros b Hb; rewrite LVIQ; right; exact (LIVELOQ b Hb)).
assert (LIVEBIQ : blocks_in_live RT ΣIQ ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))))) by (intros b [<-|Hb]; rewrite LVIQ; [left; reflexivity| right; exact (LIVEBOQ b Hb)]).
assert (LENIQ : Z.of_nat (length (rt_live RT ΣIQ)) = Z.of_nat (length (rt_live RT Σ)) + 1 + LNBL + 5) by (rewrite LVIQ; cbn [length]; rewrite Nat2Z.inj_succ, LENOQ; lia).
assert (CRDIQ : 0 <= rt_credit RT ΣIQ) by (rewrite CRIQ; exact CRDOQ).
assert (INIQ : In (IQ, 32) (rt_live RT ΣIQ)) by (rewrite LVIQ; left; reflexivity).
pose proof (new_old_apart ΣIQ mIQ [(IQ, 32)] (rt_live RT ΣOQ) IQ 32 S 160 ARTIQ LVIQ ltac:(left; reflexivity) INL) as APIQ.
cps_sigma LVIQ FRSIQ SPIQ.
destruct (live_below_lo RT AF ΣIQ mIQ IQ 32 lo ARTIQ INIQ LOW) as (_ & LOIQ & _).
destruct (frame_live_apart RT AF ΣIQ mIQ f 0%nat IQ 32 ARTIQ INF INIQ) as (FA1IQ & FA2IQ). change (fs_size 0) with 64 in FA1IQ, FA2IQ. rewrite SHF0, <- SHF in FA2IQ.
assert (BOUTIQ : forall b x, In b ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))) -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x [<-|Hb] Hx; [unfold blk_addr, blk_size in Hx; cbn [fst snd] in Hx; clear - Hx LOIQ APIQ FA1IQ FA2IQ; lia| exact (BOUTOQ b x Hb Hx)]. }
assert (BRIQ : 0 < IQ < 2^63) by (clear - POSIQ TOPIQ N72R; unfold USTACK_TOP in TOPIQ; lia).
assert (LVTIQ : rt_live RT ΣIQ = blocks_live ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))) ++ NEWL ++ (S, 160) :: rt_live RT Σ) by (rewrite LVIQ, LVTOQ; reflexivity).
assert (FRTIQ : rt_frames RT ΣIQ = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRSIQ; exact FRTOQ).
assert (SPTIQ : rt_sp0 RT ΣIQ = rt_sp0 RT Σ) by (rewrite SPIQ; exact SPTOQ).
assert (POTIQ : rt_pois RT ΣIQ = rt_pois RT Σ) by (rewrite POIQ; exact POTOQ).
assert (CRTIQ : rt_credit RT Σ - init_credit mo <= rt_credit RT ΣIQ <= rt_credit RT Σ) by (rewrite CRIQ; exact CRTOQ).
assert (AL8IQ : IQ mod 8 = 0) by (clear - AL16IQ; Z.div_mod_to_equations; lia).
clear LVIQ FRSIQ SPIQ POIQ CRIQ LVTOQ FRTOQ SPTOQ POTOQ CRTOQ POSIQ AL16IQ TOPIQ SUBFOQ SUBLOQ LIVELOQ LIVEBOQ LENOQ CRDOQ BOUTOQ.
pose proof (zbufs_cons mIQ IQ 32 ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))) ltac:(clear - N72R; lia) (zero_chunk mIQ IQ 32 ltac:(clear - N72R; lia) WRIQ BYIQ) ZB0IQ) as ZBIQ.
clear WRIQ BYIQ ZB0IQ INIQ APIQ LOIQ FA1IQ FA2IQ ACIQ.
repeat match goal with H : In (IQ, _) (rt_live RT _) |- _ => clear H end.
destruct (af_acc_live RT AF ΣIQ mIQ S 160 ARTIQ INL) as (_ & ACSIQ).
assert (OBSIQ : aobj bsegs mIQ S 160) by (split; [lia|]; split; [ulc| exact ACSIQ]).
cps_hide.
cps_seg (sbinit_w11 usp lo S SM IQ f sf sfs). { reflexivity. } { reflexivity. }
destruct POST as (mcIQ & wa2IQ & wa3IQ & -> & MUIQ & WM'IQ & MI'IQ & XIQ & FRIQ).
repeat match goal with H : context [if sfs =? 40 then ?a else ?a] |- _ => replace (if sfs =? 40 then a else a) with a in H by (destruct (sfs =? 40); reflexivity) end.
pose proof (agree_blocks_of_munch bsegs _ mIQ mcIQ LBL MUIQ WM'IQ
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)) as AG'IQ.
eapply decst_rep_agree in RL10; [| exact AG'IQ]. clear AG'IQ.
pose proof (zbufs_agree mIQ mcIQ _ ZBIQ (agree_blocks_of_munch bsegs _ mIQ mcIQ _ MUIQ WM'IQ
ltac:(intros b x Hb Hx; pose proof (BOUTIQ b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia))) as ZCIQ.
clear XOQ FROQ OBSIQ ACSIQ UWIQ ZBIQ BRIQ.
revert FB0 FRS3.
cps_seg_post.
intros FB0 FRS3.
eapply rw_cells_transport in FB0; [| exact MUIQ| exact WM'IQ| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 32; split; [clear - FLA1; unfold hid in FLA1; lia| exact I]].
eapply rw_cells_transport in FRS3; [| exact MUIQ| exact WM'IQ| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 8; split; [clear - FLA2; unfold hid in FLA2; lia| exact I]].
assert (WMTIQ : wmono bsegs m mcIQ) by cps_wmono. clear WMIQ WM'IQ WMTOQ MUIQ.

assert (UWPG : unwind_ch mcIQ (Z_to_bv 64 774264) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))).
{ apply (sbinit_site_ch (rt_live RT Σ) (rt_frames RT Σ) m mcIQ s0 ra usp lo ras 774264 UE PF (sbi_frame_rec mcIQ usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRIQ eq_refl));
[apply TRS; unfold SBINIT_SITES; cbn [In]; tauto| ulc| clear - SPA; Z.div_mod_to_equations; lia| ulc| ulc| lia]. }
cps_rt CAL.
all: try (lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- Z.of_nat (length _) < LIVE_MAX => rewrite LENIQ; clear - LVM LNB; lia
| |- mcost _ <= _ => replace (16 * 1) with 16 by lia; rewrite MC16; exact CRDIQ
| |- _ <= _ < _ => clear - N72R; lia
| |- _ <= _ <= _ => clear - N72R; lia
end).
intros ccPG (ΣPG & PG & HccPG & LVPG & FRSPG & SPPG & CRPG & POSPG & AL16PG & TOPPG & POPG).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
replace (16 * 1) with 16 in * by lia. rewrite MC16 in CRPG. rewrite Z.sub_0_r in CRPG.
revert XIQ FRIQ FB0 FRS3.
cps_unpack HccPG as (mPG & RSPG & (ARTPG & MIPG & WMPG & STPG) & PRESPG & WRPG & ACPG & BYPG).
intros XIQ FRIQ FB0 FRS3.
apply (rw_cells_pres_live _ _ _ mcIQ mPG _ _ 160 S 160 PRESPG WMPG) in XIQ; [| reflexivity| exact INL| lia| lia].
apply (rw_cells_pres_stack _ _ _ mcIQ mPG _ _ 192 PRESPG WMPG) in FRIQ; [| reflexivity| lia| clear - SPT; unfold USTACK_TOP; lia].
apply (rw_cells_pres_frame _ _ _ mcIQ mPG _ _ 32 f 0%nat PRESPG WMPG) in FB0; [| reflexivity| exact INF| lia| change (fs_size 0) with 64; lia].
apply (rw_cells_pres_fshadow _ _ _ mcIQ mPG _ _ 8 f 0%nat PRESPG WMPG) in FRS3; [| reflexivity| exact INF| rewrite <- SHF; lia| change (fs_size 0) with 64; rewrite SHF0; lia].
pose proof (agree_blocks_of_pres RT ΣIQ (rt_frames RT ΣIQ) (usp + -192) mcIQ mPG LBL PRESPG WMPG LIVELIQ) as AGPG.
eapply decst_rep_agree in RL10; [| exact AGPG]. clear AGPG.
pose proof (zbufs_agree mcIQ mPG ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))) ZCIQ (agree_blocks_of_pres RT ΣIQ (rt_frames RT ΣIQ) (usp + -192) mcIQ mPG ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))) PRESPG WMPG LIVEBIQ)) as ZB0PG.
clear PRESPG ZCIQ.
assert (SUBFPG : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT ΣPG)) by (intros e He; rewrite FRSPG; exact (SUBFIQ e He)).
assert (SUBLPG : forall e, In e (rt_live RT Σ) -> In e (rt_live RT ΣPG)) by (intros e He; rewrite LVPG; right; exact (SUBLIQ e He)).
assert (LIVELPG : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT ΣPG)) by (intros b Hb; rewrite LVPG; right; exact (LIVELIQ b Hb)).
assert (LIVEBPG : blocks_in_live RT ΣPG ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))))) by (intros b [<-|Hb]; rewrite LVPG; [left; reflexivity| right; exact (LIVEBIQ b Hb)]).
assert (LENPG : Z.of_nat (length (rt_live RT ΣPG)) = Z.of_nat (length (rt_live RT Σ)) + 1 + LNBL + 6) by (rewrite LVPG; cbn [length]; rewrite Nat2Z.inj_succ, LENIQ; lia).
assert (CRDPG : 0 <= rt_credit RT ΣPG) by (rewrite CRPG; exact CRDIQ).
assert (INPG : In (PG, 16) (rt_live RT ΣPG)) by (rewrite LVPG; left; reflexivity).
pose proof (new_old_apart ΣPG mPG [(PG, 16)] (rt_live RT ΣIQ) PG 16 S 160 ARTPG LVPG ltac:(left; reflexivity) INL) as APPG.
cps_sigma LVPG FRSPG SPPG.
destruct (live_below_lo RT AF ΣPG mPG PG 16 lo ARTPG INPG LOW) as (_ & LOPG & _).
destruct (frame_live_apart RT AF ΣPG mPG f 0%nat PG 16 ARTPG INF INPG) as (FA1PG & FA2PG). change (fs_size 0) with 64 in FA1PG, FA2PG. rewrite SHF0, <- SHF in FA2PG.
assert (BOUTPG : forall b x, In b ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))))) -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x [<-|Hb] Hx; [unfold blk_addr, blk_size in Hx; cbn [fst snd] in Hx; clear - Hx LOPG APPG FA1PG FA2PG; lia| exact (BOUTIQ b x Hb Hx)]. }
assert (BRPG : 0 < PG < 2^63) by (clear - POSPG TOPPG N72R; unfold USTACK_TOP in TOPPG; lia).
assert (LVTPG : rt_live RT ΣPG = blocks_live ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))))) ++ NEWL ++ (S, 160) :: rt_live RT Σ) by (rewrite LVPG, LVTIQ; reflexivity).
assert (FRTPG : rt_frames RT ΣPG = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRSPG; exact FRTIQ).
assert (SPTPG : rt_sp0 RT ΣPG = rt_sp0 RT Σ) by (rewrite SPPG; exact SPTIQ).
assert (POTPG : rt_pois RT ΣPG = rt_pois RT Σ) by (rewrite POPG; exact POTIQ).
assert (CRTPG : rt_credit RT Σ - init_credit mo <= rt_credit RT ΣPG <= rt_credit RT Σ) by (rewrite CRPG; exact CRTIQ).
assert (AL8PG : PG mod 8 = 0) by (clear - AL16PG; Z.div_mod_to_equations; lia).
clear LVPG FRSPG SPPG POPG CRPG LVTIQ FRTIQ SPTIQ POTIQ CRTIQ POSPG AL16PG TOPPG SUBFIQ SUBLIQ LIVELIQ LIVEBIQ LENIQ CRDIQ BOUTIQ.
pose proof (zbufs_cons mPG PG 16 ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))) ltac:(clear - N72R; lia) (zero_chunk mPG PG 16 ltac:(clear - N72R; lia) WRPG BYPG) ZB0PG) as ZBPG.
clear WRPG BYPG ZB0PG INPG APPG LOPG FA1PG FA2PG ACPG.
repeat match goal with H : In (PG, _) (rt_live RT _) |- _ => clear H end.
destruct (af_acc_live RT AF ΣPG mPG S 160 ARTPG INL) as (_ & ACSPG).
assert (OBSPG : aobj bsegs mPG S 160) by (split; [lia|]; split; [ulc| exact ACSPG]).
cps_hide.
cps_seg (sbinit_w12 usp lo S SM PG f sf sfs). { reflexivity. } { reflexivity. }
destruct POST as (mcPG & wa2PG & wa3PG & -> & MUPG & WM'PG & MI'PG & XPG & FRPG).
repeat match goal with H : context [if sfs =? 40 then ?a else ?a] |- _ => replace (if sfs =? 40 then a else a) with a in H by (destruct (sfs =? 40); reflexivity) end.
pose proof (agree_blocks_of_munch bsegs _ mPG mcPG LBL MUPG WM'PG
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)) as AG'PG.
eapply decst_rep_agree in RL10; [| exact AG'PG]. clear AG'PG.
pose proof (zbufs_agree mPG mcPG _ ZBPG (agree_blocks_of_munch bsegs _ mPG mcPG _ MUPG WM'PG
ltac:(intros b x Hb Hx; pose proof (BOUTPG b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia))) as ZCPG.
clear XIQ FRIQ OBSPG ACSPG UWPG ZBPG BRPG.
revert FB0 FRS3.
cps_seg_post.
intros FB0 FRS3.
eapply rw_cells_transport in FB0; [| exact MUPG| exact WM'PG| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 32; split; [clear - FLA1; unfold hid in FLA1; lia| exact I]].
eapply rw_cells_transport in FRS3; [| exact MUPG| exact WM'PG| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 8; split; [clear - FLA2; unfold hid in FLA2; lia| exact I]].
assert (WMTPG : wmono bsegs m mcPG) by cps_wmono. clear WMPG WM'PG WMTIQ MUPG.

assert (UWER : unwind_ch mcPG (Z_to_bv 64 774312) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))).
{ apply (sbinit_site_ch (rt_live RT Σ) (rt_frames RT Σ) m mcPG s0 ra usp lo ras 774312 UE PF (sbi_frame_rec mcPG usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRPG eq_refl));
[apply TRS; unfold SBINIT_SITES; cbn [In]; tauto| ulc| clear - SPA; Z.div_mod_to_equations; lia| ulc| ulc| lia]. }
cps_rt CAL.
all: try (lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- Z.of_nat (length _) < LIVE_MAX => rewrite LENPG; clear - LVM LNB; lia
| |- mcost _ <= _ => replace (16 * 1) with 16 by lia; rewrite MC16; exact CRDPG
| |- _ <= _ < _ => clear - N72R; lia
| |- _ <= _ <= _ => clear - N72R; lia
end).
intros ccER (ΣER & ER & HccER & LVER & FRSER & SPER & CRER & POSER & AL16ER & TOPER & POER).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
replace (16 * 1) with 16 in * by lia. rewrite MC16 in CRER. rewrite Z.sub_0_r in CRER.
revert XPG FRPG FB0 FRS3.
cps_unpack HccER as (mER & RSER & (ARTER & MIER & WMER & STER) & PRESER & WRER & ACER & BYER).
intros XPG FRPG FB0 FRS3.
apply (rw_cells_pres_live _ _ _ mcPG mER _ _ 160 S 160 PRESER WMER) in XPG; [| reflexivity| exact INL| lia| lia].
apply (rw_cells_pres_stack _ _ _ mcPG mER _ _ 192 PRESER WMER) in FRPG; [| reflexivity| lia| clear - SPT; unfold USTACK_TOP; lia].
apply (rw_cells_pres_frame _ _ _ mcPG mER _ _ 32 f 0%nat PRESER WMER) in FB0; [| reflexivity| exact INF| lia| change (fs_size 0) with 64; lia].
apply (rw_cells_pres_fshadow _ _ _ mcPG mER _ _ 8 f 0%nat PRESER WMER) in FRS3; [| reflexivity| exact INF| rewrite <- SHF; lia| change (fs_size 0) with 64; rewrite SHF0; lia].
pose proof (agree_blocks_of_pres RT ΣPG (rt_frames RT ΣPG) (usp + -192) mcPG mER LBL PRESER WMER LIVELPG) as AGER.
eapply decst_rep_agree in RL10; [| exact AGER]. clear AGER.
pose proof (zbufs_agree mcPG mER ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))))) ZCPG (agree_blocks_of_pres RT ΣPG (rt_frames RT ΣPG) (usp + -192) mcPG mER ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))))) PRESER WMER LIVEBPG)) as ZB0ER.
clear PRESER ZCPG.
assert (SUBFER : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT ΣER)) by (intros e He; rewrite FRSER; exact (SUBFPG e He)).
assert (SUBLER : forall e, In e (rt_live RT Σ) -> In e (rt_live RT ΣER)) by (intros e He; rewrite LVER; right; exact (SUBLPG e He)).
assert (LIVELER : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT ΣER)) by (intros b Hb; rewrite LVER; right; exact (LIVELPG b Hb)).
assert (LIVEBER : blocks_in_live RT ΣER ((tt, ER, 16) :: ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))))))) by (intros b [<-|Hb]; rewrite LVER; [left; reflexivity| right; exact (LIVEBPG b Hb)]).
assert (LENER : Z.of_nat (length (rt_live RT ΣER)) = Z.of_nat (length (rt_live RT Σ)) + 1 + LNBL + 7) by (rewrite LVER; cbn [length]; rewrite Nat2Z.inj_succ, LENPG; lia).
assert (CRDER : 0 <= rt_credit RT ΣER) by (rewrite CRER; exact CRDPG).
assert (INER : In (ER, 16) (rt_live RT ΣER)) by (rewrite LVER; left; reflexivity).
pose proof (new_old_apart ΣER mER [(ER, 16)] (rt_live RT ΣPG) ER 16 S 160 ARTER LVER ltac:(left; reflexivity) INL) as APER.
cps_sigma LVER FRSER SPER.
destruct (live_below_lo RT AF ΣER mER ER 16 lo ARTER INER LOW) as (_ & LOER & _).
destruct (frame_live_apart RT AF ΣER mER f 0%nat ER 16 ARTER INF INER) as (FA1ER & FA2ER). change (fs_size 0) with 64 in FA1ER, FA2ER. rewrite SHF0, <- SHF in FA2ER.
assert (BOUTER : forall b x, In b ((tt, ER, 16) :: ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))))) -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x [<-|Hb] Hx; [unfold blk_addr, blk_size in Hx; cbn [fst snd] in Hx; clear - Hx LOER APER FA1ER FA2ER; lia| exact (BOUTPG b x Hb Hx)]. }
assert (BRER : 0 < ER < 2^63) by (clear - POSER TOPER N72R; unfold USTACK_TOP in TOPER; lia).
assert (LVTER : rt_live RT ΣER = blocks_live ((tt, ER, 16) :: ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))))) ++ NEWL ++ (S, 160) :: rt_live RT Σ) by (rewrite LVER, LVTPG; reflexivity).
assert (FRTER : rt_frames RT ΣER = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRSER; exact FRTPG).
assert (SPTER : rt_sp0 RT ΣER = rt_sp0 RT Σ) by (rewrite SPER; exact SPTPG).
assert (POTER : rt_pois RT ΣER = rt_pois RT Σ) by (rewrite POER; exact POTPG).
assert (CRTER : rt_credit RT Σ - init_credit mo <= rt_credit RT ΣER <= rt_credit RT Σ) by (rewrite CRER; exact CRTPG).
assert (AL8ER : ER mod 8 = 0) by (clear - AL16ER; Z.div_mod_to_equations; lia).
clear LVER FRSER SPER POER CRER LVTPG FRTPG SPTPG POTPG CRTPG POSER AL16ER TOPER SUBFPG SUBLPG LIVELPG LIVEBPG LENPG CRDPG BOUTPG.
pose proof (zbufs_cons mER ER 16 ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))))) ltac:(clear - N72R; lia) (zero_chunk mER ER 16 ltac:(clear - N72R; lia) WRER BYER) ZB0ER) as ZBER.
clear WRER BYER ZB0ER INER APER LOER FA1ER FA2ER ACER.
repeat match goal with H : In (ER, _) (rt_live RT _) |- _ => clear H end.
destruct (af_acc_live RT AF ΣER mER S 160 ARTER INL) as (_ & ACSER).
assert (OBSER : aobj bsegs mER S 160) by (split; [lia|]; split; [ulc| exact ACSER]).
cps_hide.
cps_seg (sbinit_w13 usp lo S SM ER f sf sfs). { reflexivity. } { reflexivity. }
destruct POST as (mcER & wa2ER & wa3ER & -> & MUER & WM'ER & MI'ER & XER & FRER).
repeat match goal with H : context [if sfs =? 40 then ?a else ?a] |- _ => replace (if sfs =? 40 then a else a) with a in H by (destruct (sfs =? 40); reflexivity) end.
pose proof (agree_blocks_of_munch bsegs _ mER mcER LBL MUER WM'ER
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)) as AG'ER.
eapply decst_rep_agree in RL10; [| exact AG'ER]. clear AG'ER.
pose proof (zbufs_agree mER mcER _ ZBER (agree_blocks_of_munch bsegs _ mER mcER _ MUER WM'ER
ltac:(intros b x Hb Hx; pose proof (BOUTER b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia))) as ZCER.
clear XPG FRPG OBSER ACSER UWER ZBER BRER.
revert FB0 FRS3.
cps_seg_post.
intros FB0 FRS3.
eapply rw_cells_transport in FB0; [| exact MUER| exact WM'ER| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 32; split; [clear - FLA1; unfold hid in FLA1; lia| exact I]].
eapply rw_cells_transport in FRS3; [| exact MUER| exact WM'ER| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 8; split; [clear - FLA2; unfold hid in FLA2; lia| exact I]].
assert (WMTER : wmono bsegs m mcER) by cps_wmono. clear WMER WM'ER WMTPG MUER.

assert (UWMS : unwind_ch mcER (Z_to_bv 64 774372) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))).
{ apply (sbinit_site_ch (rt_live RT Σ) (rt_frames RT Σ) m mcER s0 ra usp lo ras 774372 UE PF (sbi_frame_rec mcER usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRER eq_refl));
[apply TRS; unfold SBINIT_SITES; cbn [In]; tauto| ulc| clear - SPA; Z.div_mod_to_equations; lia| ulc| ulc| lia]. }
cps_rt CAL.
all: try (lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- Z.of_nat (length _) < LIVE_MAX => rewrite LENER; clear - LVM LNB; lia
| |- mcost _ <= _ => replace (64 * 1) with 64 by lia; rewrite MC64; exact CRDER
| |- _ <= _ < _ => clear - N72R; lia
| |- _ <= _ <= _ => clear - N72R; lia
end).
intros ccMS (ΣMS & MS & HccMS & LVMS & FRSMS & SPMS & CRMS & POSMS & AL16MS & TOPMS & POMS).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
replace (64 * 1) with 64 in * by lia. rewrite MC64 in CRMS. rewrite Z.sub_0_r in CRMS.
revert XER FRER FB0 FRS3.
cps_unpack HccMS as (mMS & RSMS & (ARTMS & MIMS & WMMS & STMS) & PRESMS & WRMS & ACMS & BYMS).
intros XER FRER FB0 FRS3.
apply (rw_cells_pres_live _ _ _ mcER mMS _ _ 160 S 160 PRESMS WMMS) in XER; [| reflexivity| exact INL| lia| lia].
apply (rw_cells_pres_stack _ _ _ mcER mMS _ _ 192 PRESMS WMMS) in FRER; [| reflexivity| lia| clear - SPT; unfold USTACK_TOP; lia].
apply (rw_cells_pres_frame _ _ _ mcER mMS _ _ 32 f 0%nat PRESMS WMMS) in FB0; [| reflexivity| exact INF| lia| change (fs_size 0) with 64; lia].
apply (rw_cells_pres_fshadow _ _ _ mcER mMS _ _ 8 f 0%nat PRESMS WMMS) in FRS3; [| reflexivity| exact INF| rewrite <- SHF; lia| change (fs_size 0) with 64; rewrite SHF0; lia].
pose proof (agree_blocks_of_pres RT ΣER (rt_frames RT ΣER) (usp + -192) mcER mMS LBL PRESMS WMMS LIVELER) as AGMS.
eapply decst_rep_agree in RL10; [| exact AGMS]. clear AGMS.
pose proof (zbufs_agree mcER mMS ((tt, ER, 16) :: ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))))) ZCER (agree_blocks_of_pres RT ΣER (rt_frames RT ΣER) (usp + -192) mcER mMS ((tt, ER, 16) :: ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))))) PRESMS WMMS LIVEBER)) as ZB0MS.
clear PRESMS ZCER.
assert (SUBFMS : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT ΣMS)) by (intros e He; rewrite FRSMS; exact (SUBFER e He)).
assert (SUBLMS : forall e, In e (rt_live RT Σ) -> In e (rt_live RT ΣMS)) by (intros e He; rewrite LVMS; right; exact (SUBLER e He)).
assert (LIVELMS : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT ΣMS)) by (intros b Hb; rewrite LVMS; right; exact (LIVELER b Hb)).
assert (LIVEBMS : blocks_in_live RT ΣMS ((tt, MS, 64) :: ((tt, ER, 16) :: ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))))))) by (intros b [<-|Hb]; rewrite LVMS; [left; reflexivity| right; exact (LIVEBER b Hb)]).
assert (LENMS : Z.of_nat (length (rt_live RT ΣMS)) = Z.of_nat (length (rt_live RT Σ)) + 1 + LNBL + 8) by (rewrite LVMS; cbn [length]; rewrite Nat2Z.inj_succ, LENER; lia).
assert (CRDMS : 0 <= rt_credit RT ΣMS) by (rewrite CRMS; exact CRDER).
assert (INMS : In (MS, 64) (rt_live RT ΣMS)) by (rewrite LVMS; left; reflexivity).
pose proof (new_old_apart ΣMS mMS [(MS, 64)] (rt_live RT ΣER) MS 64 S 160 ARTMS LVMS ltac:(left; reflexivity) INL) as APMS.
cps_sigma LVMS FRSMS SPMS.
destruct (live_below_lo RT AF ΣMS mMS MS 64 lo ARTMS INMS LOW) as (_ & LOMS & _).
destruct (frame_live_apart RT AF ΣMS mMS f 0%nat MS 64 ARTMS INF INMS) as (FA1MS & FA2MS). change (fs_size 0) with 64 in FA1MS, FA2MS. rewrite SHF0, <- SHF in FA2MS.
assert (BOUTMS : forall b x, In b ((tt, MS, 64) :: ((tt, ER, 16) :: ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))))))) -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x [<-|Hb] Hx; [unfold blk_addr, blk_size in Hx; cbn [fst snd] in Hx; clear - Hx LOMS APMS FA1MS FA2MS; lia| exact (BOUTER b x Hb Hx)]. }
assert (BRMS : 0 < MS < 2^63) by (clear - POSMS TOPMS N72R; unfold USTACK_TOP in TOPMS; lia).
assert (LVTMS : rt_live RT ΣMS = blocks_live ((tt, MS, 64) :: ((tt, ER, 16) :: ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))))))) ++ NEWL ++ (S, 160) :: rt_live RT Σ) by (rewrite LVMS, LVTER; reflexivity).
assert (FRTMS : rt_frames RT ΣMS = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRSMS; exact FRTER).
assert (SPTMS : rt_sp0 RT ΣMS = rt_sp0 RT Σ) by (rewrite SPMS; exact SPTER).
assert (POTMS : rt_pois RT ΣMS = rt_pois RT Σ) by (rewrite POMS; exact POTER).
assert (CRTMS : rt_credit RT Σ - init_credit mo <= rt_credit RT ΣMS <= rt_credit RT Σ) by (rewrite CRMS; exact CRTER).
assert (AL8MS : MS mod 8 = 0) by (clear - AL16MS; Z.div_mod_to_equations; lia).
clear LVMS FRSMS SPMS POMS CRMS LVTER FRTER SPTER POTER CRTER POSMS AL16MS TOPMS SUBFER SUBLER LIVELER LIVEBER LENER CRDER BOUTER.
pose proof (zbufs_cons mMS MS 64 ((tt, ER, 16) :: ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))))) ltac:(clear - N72R; lia) (zero_chunk mMS MS 64 ltac:(clear - N72R; lia) WRMS BYMS) ZB0MS) as ZBMS.
clear WRMS BYMS ZB0MS INMS APMS LOMS FA1MS FA2MS ACMS.
repeat match goal with H : In (MS, _) (rt_live RT _) |- _ => clear H end.
destruct (af_acc_live RT AF ΣMS mMS S 160 ARTMS INL) as (_ & ACSMS).
assert (OBSMS : aobj bsegs mMS S 160) by (split; [lia|]; split; [ulc| exact ACSMS]).
cps_hide.
cps_seg (sbinit_w14 usp lo S SM MS f sf). { reflexivity. } { reflexivity. }
destruct POST as (mcMS & wa0MS & wa1MS & wa2MS & -> & MUMS & WM'MS & MI'MS & XMS & FRMS).
repeat match goal with H : context [if sfs =? 40 then ?a else ?a] |- _ => replace (if sfs =? 40 then a else a) with a in H by (destruct (sfs =? 40); reflexivity) end.
pose proof (agree_blocks_of_munch bsegs _ mMS mcMS LBL MUMS WM'MS
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)) as AG'MS.
eapply decst_rep_agree in RL10; [| exact AG'MS]. clear AG'MS.
pose proof (zbufs_agree mMS mcMS _ ZBMS (agree_blocks_of_munch bsegs _ mMS mcMS _ MUMS WM'MS
ltac:(intros b x Hb Hx; pose proof (BOUTMS b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia))) as ZCMS.
clear XER FRER OBSMS ACSMS UWMS ZBMS BRMS.
revert FB0 FRS3.
cps_seg_post.
intros FB0 FRS3.
eapply rw_cells_transport in FB0; [| exact MUMS| exact WM'MS| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 32; split; [clear - FLA1; unfold hid in FLA1; lia| exact I]].
eapply rw_cells_transport in FRS3; [| exact MUMS| exact WM'MS| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 8; split; [clear - FLA2; unfold hid in FLA2; lia| exact I]].
assert (WMTMS : wmono bsegs m mcMS) by cps_wmono. clear WMMS WM'MS WMTER MUMS.

assert (FTOP' : f + 64 <= APP_TOP) by (clear - FTOP; unfold APP_TOP, USTACK_TOP in *; change (fs_size 0) with 64 in FTOP; lia).
chunk_uncons FB0 as HDF.
cps_hide.
cps_seg (sbinit_epi_a usp f sf).
destruct POST as (me1 & -> & MUe1 & WMe1 & MIe1 & FRSe1).
pose proof (agree_blocks_of_munch bsegs _ mcMS me1 LBL MUe1 WMe1
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)) as AGe1.
eapply decst_rep_agree in RL10; [| exact AGe1]. clear AGe1.
pose proof (zbufs_agree mcMS me1 _ ZCMS (agree_blocks_of_munch bsegs _ mcMS me1 _ MUe1 WMe1
ltac:(intros b x Hb Hx; pose proof (BOUTMS b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia))) as ZBe1.
clear HDF FB0 FRS3 ZCMS. unfold bF5 in FRSe1. cbn [map repeat] in FRSe1.
cps_seg_post.

lazymatch goal with A : X14x.ART RT ΣMS me1 |- _ => rename A into ARTe1 end.
cps_release_intro_sub ARTe1 FRTMS SUBLMS (fun E : rt_frames RT Σ = [] => eq_trans POTMS (PNIL E)) Σr fl.
assert (NFLB : forall L, blocks_in_live RT ΣMS L -> forall b x, In b L -> blk_addr b <= x < blk_addr b + blk_size b -> outside [(fl, fl + 1)] x).
{ intros L BL b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl. apply NAC. right; right; left. exists (blk_addr b), (blk_size b). split; [exact (BL b Hb)| clear - Hx Hfl; cbn [fst snd] in Hfl; lia]. }
assert (FLS : fl < S \/ S + 160 <= fl).
{ destruct (Z_lt_dec fl S) as [L|L]; [left; exact L|]. destruct (Z_le_dec (S + 160) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists S, 160. split; [exact INL| clear - L G; lia]. }
cps_hide.
cps_seg (sbinit_epi_b usp lo f fl S).
destruct POST as (me2 & -> & MUe2 & WMe2 & MIe2 & STe2 & FLGe2).
eapply decst_rep_agree in RL10; [| exact (agree_blocks_of_munch bsegs _ me1 me2 LBL MUe2 WMe2 (NFLB LBL LIVELMS))].
pose proof (zbufs_agree me1 me2 _ ZBe1 (agree_blocks_of_munch bsegs _ me1 me2 _ MUe2 WMe2 (NFLB _ LIVEBMS))) as ZBe2.
clear ZBe1 FRMS FRSe1.
cps_release_done REL MUe2 WMe2 FLGe2.

apply Hk. clear Hk.
set (a := SBA AL G0 G1 EX OQ IQ MS PG ER).
set (st := sb_init_state mo lr).
set (BUFL := blocks_live [(tt, MS, 64); (tt, ER, 16); (tt, PG, 16); (tt, IQ, 32); (tt, OQ, 32); (tt, EX, N72); (tt, G1, 256); (tt, G0, 256)]) in *.
exists Σr, S, (sb_blocks st S a ++ LBL), (BUFL ++ NEWL ++ [(S, 160)]).
assert (ELIVE : rt_live RT Σr = (BUFL ++ NEWL ++ [(S, 160)]) ++ rt_live RT Σ) by (rewrite EL, LVTMS, <- !app_assoc; reflexivity).
assert (PERM : Permutation (BUFL ++ NEWL ++ [(S, 160)]) (blocks_live (sb_blocks st S a ++ LBL))).
{ unfold blocks_live. rewrite map_app. cbn [sb_blocks map blk_addr blk_size fst snd st sb_init_state sbd_subframeSize].
unfold SBSTATE_SIZEOF. rewrite <- ESFS, <- N72E.
apply Permutation_trans with ((S, 160) :: BUFL ++ NEWL); [rewrite app_assoc; apply Permutation_sym, Permutation_cons_append|].
apply perm_skip.
apply (Permutation_app (l := BUFL) (m := NEWL) (l' := [(G0, 256); (G1, 256); (EX, N72); (OQ, 32); (IQ, 32); (PG, 16); (ER, 16); (MS, 64)])
(m' := map (fun b : block => (blk_addr b, blk_size b)) LBL)); [| exact PERM3].
subst BUFL. unfold blocks_live. cbn [map blk_addr blk_size fst snd].
change [(MS, 64); (ER, 16); (PG, 16); (IQ, 32); (OQ, 32); (EX, N72); (G1, 256); (G0, 256)] with (rev [(G0, 256); (G1, 256); (EX, N72); (OQ, 32); (IQ, 32); (PG, 16); (ER, 16); (MS, 64)]).
apply Permutation_sym, Permutation_rev. }
assert (NDUP : List.NoDup (map blk_id (sb_blocks st S a ++ LBL))).
{ assert (E : map blk_id (sb_blocks st S a ++ LBL) = map fst (blocks_live (sb_blocks st S a ++ LBL))) by (unfold blocks_live; rewrite map_map; reflexivity).
rewrite E. apply (Permutation_NoDup (Permutation_map fst PERM)).
apply (live_nodup RT AF Σr me2 _ [] (rt_live RT Σ) ART ELIVE).
intros e He. apply in_app_iff in He. destruct He as [He|He].
- subst BUFL. unfold blocks_live in He. cbn [map blk_addr blk_size fst snd In] in He.
repeat (destruct He as [<-|He]; [cbn [snd]; clear - N72R; lia|]). destruct He.
- apply in_app_iff in He. destruct He as [He|[<-|[]]]; [| cbn [snd]; lia].
apply (Permutation_in _ PERM3) in He. unfold blocks_live in He. apply in_map_iff in He. destruct He as (b & <- & Hb). cbn [snd].
exact (drep_sizes_pos _ _ _ _ _ _ RL10 b Hb). }
assert (LENN : Z.of_nat (length (BUFL ++ NEWL ++ [(S, 160)])) = init_nblocks mo).
{ rewrite NBL. fold LNBL. rewrite !length_app. subst BUFL. unfold blocks_live. cbn [map length]. fold LNBL in LENL. clear - LENL. lia. }
assert (AL8ALL : forall x, In x (sb_blocks st S a ++ LBL) -> blk_addr x mod 8 = 0).
{ intros x Hx. apply in_app_iff in Hx. destruct Hx as [Hx|Hx]; [| exact (AL8L x Hx)].
cbn [sb_blocks In] in Hx.
repeat (destruct Hx as [<-|Hx]; [unfold blk_addr, a; cbn [fst snd a_g0 a_g1 a_exc a_oq a_iq a_msp a_pg a_er]; assumption|]). destruct Hx. }
split; [| split; [exact ELIVE|]; split; [exact PERM|]; split; [exact NDUP|]; split; [exact LENN|]; split; [exact EF|];
split; [rewrite ES; exact SPTMS|]; split; [rewrite EC; exact CRTMS|]; split; [rewrite EP; exact POTMS| exact AL8ALL]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists me2.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM10]|].
split. { split; [assumption|]. split; [exact MIe2|]. split; [cps_wmono| exact STe2]. }
split; [exact PF|].

assert (MOC : mo = ModeWB \/ mo = ModeUWB) by (clear - NENB; destruct mo; [congruence| left; reflexivity| right; reflexivity]).
assert (Q4 : Z.quot fs sfs = 4) by (clear - GEO; unfold hid in GEO; destruct GEO as [[-> ->]|[-> ->]]; reflexivity).
assert (DSMR : 0 <= dsm <= 7) by (rewrite EDSM; clear; destruct mo; cbn; lia).
assert (SFSP : 0 < sfs) by (clear - GEO'; unfold hid in GEO'; lia).
rewrite EDEC. unfold sb_wrap. rewrite ctl_gsr_snd. fold lr. fold st.
cbn [decst_rep]. exists a, (SBJ w0 (Z_to_bv 64 1000) zb4 zb4 (zw 64) (zw 64) (zw (Z.to_nat sfs)) (zw 8) (zw 8) (zw 16) (zw 4) (zw 4)), LBL.
split; [reflexivity|]. split; [exact S8|]. split; [clear - SPOS; lia|].
split.
{ unfold sb_inv, st, sb_init_state.
cbn [sbd_mode sbd_frame_size sbd_full_frame_size sbd_subframeSize sbd_nbSubframes sbd_lpcSize sbd_first sbd_sampling_rate sbd_lpc_enh_enabled sbd_encode_submode sbd_submodeID sbd_innov_save].
rewrite <- EFS, <- ESFS, <- EDSM, Q4. change (sbm_lpcSize mo) with 8.
split; [exact MOC|]. repeat split; try reflexivity; try (clear - LRR DSMR; lia). }
split.
{ unfold sb_junk_ok, st, sb_init_state. cbn [sj_pad1 sj_pad2 sj_g0 sj_g1 sj_exc sj_oq sj_iq sj_msp sj_pg sj_er sbd_subframeSize].
repeat split; try reflexivity. unfold zw. rewrite repeat_length, Z2Nat.id by lia. exact ESFS. }
split.
{ unfold sb_cells, st, sb_init_state, a.
cbn [sbd_mode sbd_frame_size sbd_full_frame_size sbd_subframeSize sbd_nbSubframes sbd_lpcSize sbd_first sbd_sampling_rate sbd_lpc_enh_enabled sbd_encode_submode sbd_submodeID
sbd_innov_save sb_isave_ptr a_low a_g0 a_g1 a_exc a_oq a_iq a_msp a_pg a_er sj_last_ener sj_seed sj_pad1 sj_pad2].
rewrite <- EMP, <- EFS, <- ESFS, <- EDSM, <- ESUB, Q4, (Z.mul_comm lr 2). change (sbm_lpcSize mo) with 8. exact XMS. }
split.
{ unfold sb_bufs, a. cbn [a_g0 a_g1 a_exc a_oq a_iq a_msp a_pg a_er sj_g0 sj_g1 sj_exc sj_oq sj_iq sj_msp sj_pg sj_er].
split; [apply (zbuf_recast 64); [lia| exact (proj2 (ZBe2 (tt, G0, 256) ltac:(cbn [In]; tauto)))]|].
split; [apply (zbuf_recast 64); [lia| exact (proj2 (ZBe2 (tt, G1, 256) ltac:(cbn [In]; tauto)))]|].
split.
{ pose proof (proj2 (ZBe2 (tt, EX, N72) ltac:(cbn [In]; tauto))) as ZX. clear - ZX GEO'. unfold hid in GEO'. subst N72.
destruct GEO' as [->| ->]; [apply (zbuf_recast 40)| apply (zbuf_recast 80)]; first [lia | exact ZX]. }
split; [apply (zbuf_recast 8); [lia| exact (proj2 (ZBe2 (tt, OQ, 32) ltac:(cbn [In]; tauto)))]|].
split; [apply (zbuf_recast 8); [lia| exact (proj2 (ZBe2 (tt, IQ, 32) ltac:(cbn [In]; tauto)))]|].
split; [apply (zbuf_recast 16); [lia| exact (proj2 (ZBe2 (tt, MS, 64) ltac:(cbn [In]; tauto)))]|].
split; [apply (zbuf_recast 4); [lia| exact (proj2 (ZBe2 (tt, PG, 16) ltac:(cbn [In]; tauto)))]|].
apply (zbuf_recast 4); [lia| exact (proj2 (ZBe2 (tt, ER, 16) ltac:(cbn [In]; tauto)))]. }
exists 0. exact RL10.
Qed.

Theorem init_cps_all : forall mo, init_cps_at mo.
Proof using AF CAL MSET SM0 AF_LIB.
intros mo. destruct mo.
- exact init_cps_nb.
- exact (init_cps_sb ModeWB ltac:(discriminate) init_cps_nb).
- exact (init_cps_sb ModeUWB ltac:(discriminate) (init_cps_sb ModeWB ltac:(discriminate) init_cps_nb)).
Qed.
End InitCPS.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition sb_init_state (mo : spx_mode) (rate : Z) : sbd_state bptr :=
mkSBD tt mo (2 * sbm_frameSize mo) (sbm_frameSize mo) (sbm_subframeSize mo) (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo)) (sbm_lpcSize mo)
1 (rate * 2) 0 tt tt tt tt tt tt tt tt None 1 (sbm_defaultSubmode mo).
Definition sb_wrap (mo : spx_mode) (low : dec_state bptr) : dec_state bptr :=
DecSB (sb_init_state mo (fst (speex_decoder_ctl low CtlGetSamplingRate)))
(snd (speex_decoder_ctl (snd (speex_decoder_ctl low CtlGetSamplingRate)) (CtlSetWideband 1))).
Definition init_dec (mo : spx_mode) : dec_state bptr :=
match mo with
| ModeNB => DecNB (nb_init_state tt)
| ModeWB => sb_wrap ModeWB (DecNB (nb_init_state tt))
| ModeUWB => sb_wrap ModeUWB (sb_wrap ModeWB (DecNB (nb_init_state tt)))
end.

Definition low_mode (mo : spx_mode) : spx_mode := match mo with ModeUWB => ModeWB | _ => ModeNB end.

Lemma sb_init_prun : forall mo (low_init : X1qy.M pst (option (dec_state unit))) (low : dec_state unit) q r q',
(forall q0 r0 q0', prun low_init q0 = Some (r0, q0') -> r0 = Some low /\ q0' = q0) ->
prun (sb_decoder_init (St := pst) p_calloc p_free mo low_init) q = Some (r, q') -> r = Some (sb_wrap mo low) /\ q' = q.
Proof.
intros mo low_init low q r q' HL H. unfold sb_decoder_init in H.
rewrite prun_bind in H. rewrite (prun_calloc_ok SIZEOF_SBDECSTATE 1 q) in H by (unfold SIZEOF_SBDECSTATE; lia).
cbv beta iota in H. rewrite prun_bind in H.
destruct (prun low_init q) as [[r0 q0]|] eqn:EL in H; [| discriminate H]. cbv beta iota in H.
destruct (HL q r0 q0 EL) as [-> ->]. cbv beta iota in H.
destruct (speex_decoder_ctl low CtlGetSamplingRate) as [rate low1] eqn:E1.
destruct (speex_decoder_ctl low1 (CtlSetWideband 1)) as [v2 low2] eqn:E2.
assert (SZ : 0 <= sbm_subframeSize mo * 4 < 1000 /\ 0 <= sbm_lpcSize mo * 4 < 1000 /\ 0 <= Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4 < 1000
/\ 0 <= 2 * sbm_lpcSize mo * 4 < 1000) by (destruct mo; repeat split; vm_compute; first [reflexivity | (intro X; discriminate X)]).
destruct SZ as (Z1 & Z2 & Z3 & Z4).
rewrite prun_bind in H. rewrite (prun_calloc_ok (QMF_ORDER * 4) 1 q) in H by (unfold QMF_ORDER; lia). cbv beta iota in H.
rewrite prun_bind in H. rewrite (prun_calloc_ok (QMF_ORDER * 4) 1 q) in H by (unfold QMF_ORDER; lia). cbv beta iota in H.
rewrite prun_bind in H. rewrite (prun_calloc_ok (sbm_subframeSize mo * 4) 1 q) in H by lia. cbv beta iota in H.
rewrite prun_bind in H. rewrite (prun_calloc_ok (sbm_lpcSize mo * 4) 1 q) in H by lia. cbv beta iota in H.
rewrite prun_bind in H. rewrite (prun_calloc_ok (sbm_lpcSize mo * 4) 1 q) in H by lia. cbv beta iota in H.
rewrite prun_bind in H. rewrite (prun_calloc_ok (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4) 1 q) in H by lia. cbv beta iota in H.
rewrite prun_bind in H. rewrite (prun_calloc_ok (Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) * 4) 1 q) in H by lia. cbv beta iota in H.
rewrite prun_bind in H. rewrite (prun_calloc_ok (2 * sbm_lpcSize mo * 4) 1 q) in H by lia. cbv beta iota in H.
rewrite prun_ret in H. injection H as <- <-. split; [| reflexivity].
unfold sb_wrap, sb_init_state. unfold bptr. rewrite E1. cbn [fst snd]. rewrite E2. reflexivity.
Qed.

Lemma init_prun : forall mo q r q',
prun (speex_decoder_init (St := pst) p_calloc p_free mo) q = Some (r, q') -> r = Some (init_dec mo) /\ q' = q.
Proof.
intros mo q r q' H. destruct mo; cbn [speex_decoder_init init_dec] in *.
- exact (nb_init_prun q r q' H).
- exact (sb_init_prun ModeWB _ _ q r q' nb_init_prun H).
- refine (sb_init_prun ModeUWB _ _ q r q' _ H). intros q0 r0 q0'. exact (sb_init_prun ModeWB _ _ q0 r0 q0' nb_init_prun).
Qed.

Lemma init_dec_depth : forall mo, dec_depth (init_dec mo) = match mo with ModeNB => 1 | ModeWB => 2 | ModeUWB => 3 end%nat.
Proof. destruct mo; reflexivity. Qed.
Lemma ctl_gsr_snd : forall d : dec_state bptr, snd (speex_decoder_ctl d CtlGetSamplingRate) = d.
Proof. destruct d; reflexivity. Qed.
Lemma init_low_rate : forall mo, fst (speex_decoder_ctl (init_dec mo) CtlGetSamplingRate) = match mo with ModeNB => 8000 | ModeWB => 16000 | ModeUWB => 32000 end.
Proof. destruct mo; reflexivity. Qed.

Definition SBINIT_SITES : list Z := [0xb52a8; 0xb54dc; 0xb5500; 0xb5530; 0xb5564; 0xb5594; 0xb55c4; 0xb55f4; 0xb5624].
Definition sb_traces (rae : Z) (ras : list Z) : Prop := forall site, In site SBINIT_SITES -> In (site :: rae :: ras) SITE_TRACES.

Definition init_traces (mo : spx_mode) (rae : Z) (ras : list Z) : Prop :=
match mo with
| ModeNB => In (RA_nbinit_calloc :: ras) SITE_TRACES
| ModeWB => sb_traces rae ras /\ In (RA_nbinit_calloc :: rae :: ras) SITE_TRACES
| ModeUWB => sb_traces rae ras /\ sb_traces RA_sbinit_low (rae :: ras) /\ In (RA_nbinit_calloc :: RA_sbinit_low :: rae :: ras) SITE_TRACES
end.

Definition uw_entry (m : mem) (s0 : word) (usp lo : Z) (ras : list Z) : Prop :=
match ras with [] => not_frame lo (bv_unsigned s0) | _ :: _ => uw_chain USTACK_TOP m usp (bv_unsigned s0) ras end.

Lemma init_traces_harness : forall mo, init_traces mo 0x96f2c [0x96564].
Proof.
assert (D : forall l, (if in_dec (list_eq_dec Z.eq_dec) l SITE_TRACES then True else False) -> In l SITE_TRACES)
by (intros l H; destruct (in_dec (list_eq_dec Z.eq_dec) l SITE_TRACES) as [i|]; [exact i| destruct H]).
assert (SB1 : sb_traces 0x96f2c [0x96564]).
{ intros site Hs. cbn [SBINIT_SITES In] in Hs. repeat (destruct Hs as [<-|Hs]; [apply D; vm_compute; exact I|]). destruct Hs. }
assert (SB2 : sb_traces RA_sbinit_low [0x96f2c; 0x96564]).
{ intros site Hs. cbn [SBINIT_SITES In] in Hs. repeat (destruct Hs as [<-|Hs]; [apply D; vm_compute; exact I|]). destruct Hs. }
destruct mo; cbn [init_traces].
- apply D. vm_compute. exact I.
- split; [exact SB1| apply D; vm_compute; exact I].
- split; [exact SB1|]. split; [exact SB2| apply D; vm_compute; exact I].
Qed.

Lemma init_traces_low : forall mo rae ras, mo <> ModeNB -> init_traces mo rae ras -> sb_traces rae ras /\ init_traces (low_mode mo) RA_sbinit_low (rae :: ras).
Proof. intros mo rae ras NE H. destruct mo; [congruence| exact H| exact H]. Qed.

Lemma uw_entry_chain : forall live frames (m m' : mem) s0 usp lo ras f,
uw_entry m s0 usp lo ras -> rt_pres_fp live frames usp [] m m' -> lo <= f -> f <= usp ->
uw_chain USTACK_TOP m' f (bv_unsigned s0) ras.
Proof.
intros live frames m m' s0 usp lo ras f UE PF LF FU. destruct ras as [|r ras]; cbn [uw_entry] in UE.
- cbn [uw_chain]. exact (not_frame_stop lo _ f UE LF).
- apply (uw_chain_sp USTACK_TOP m' usp f _ r ras); [| exact FU].
apply (uw_chain_pres live frames usp m m' (r :: ras) usp _); [intros a Ha; exact (PF a Ha I)| lia| exact UE].
Qed.

Lemma sbinit_site_ch : forall live frames (m mk : mem) (s0 ra : word) usp lo ras site,
uw_entry m s0 usp lo ras -> rt_pres_fp live frames usp [] m mk ->
rw_cells asegs mk (usp + -16) [C8 s0; C8 ra] ->
In (site :: bv_unsigned ra :: ras) SITE_TRACES ->
lo <= usp -> usp mod 8 = 0 -> usp <= USTACK_TOP -> 192 <= usp -> 0 <= site < 2^64 ->
unwind_ch mk (Z_to_bv 64 site) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192)).
Proof.
intros live frames m mk s0 ra usp lo ras site UE PF REC TR LU U8 UT U192 SR.
exists (bv_unsigned ra :: ras). unfold USTACK_TOP in UT. rewrite !unsigned_lit by lia. split; [exact TR|].
apply (uw_chain_push USTACK_TOP mk (usp + -192) usp (bv_unsigned s0) (bv_unsigned ra) ras); [lia| exact U8| unfold USTACK_TOP; lia| apply bv_unsigned_in_range| |].
- rewrite !Z_to_bv_bv_unsigned. exact REC.
- exact (uw_entry_chain live frames m mk s0 usp lo ras usp UE PF LU ltac:(lia)).
Qed.

Lemma sbinit_low_entry : forall live frames (m mk : mem) (s0 ra : word) usp lo ras,
uw_entry m s0 usp lo ras -> rt_pres_fp live frames usp [] m mk ->
rw_cells asegs mk (usp + -16) [C8 s0; C8 ra] ->
lo <= usp -> usp mod 8 = 0 -> usp <= USTACK_TOP -> 192 <= usp ->
uw_entry mk (Z_to_bv 64 usp) (usp + -192) lo (bv_unsigned ra :: ras).
Proof.
intros live frames m mk s0 ra usp lo ras UE PF REC LU U8 UT U192. cbn [uw_entry]. unfold USTACK_TOP in UT. rewrite unsigned_lit by lia.
apply (uw_chain_push USTACK_TOP mk (usp + -192) usp (bv_unsigned s0) (bv_unsigned ra) ras); [lia| exact U8| unfold USTACK_TOP; lia| apply bv_unsigned_in_range| |].
- rewrite !Z_to_bv_bv_unsigned. exact REC.
- exact (uw_entry_chain live frames m mk s0 usp lo ras usp UE PF LU ltac:(lia)).
Qed.

Section KitX.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Lemma flag_not_client_sub : forall (Σ Σ1 : rts RT) f k usp fl a,
rt_frames RT Σ1 = (f, k) :: rt_frames RT Σ -> (forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ1)) ->
~ aclient (rt_live RT Σ1) (rt_frames RT Σ1) USTACK_TOP fl -> fl < usp ->
aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> a <> fl.
Proof.
intros Σ Σ1 f k usp fl a FRS LV NAC FLU Ha E. subst a. apply NAC. rewrite FRS.
destruct Ha as [H|[H|[H|[H|H]]]]; [lia| right; left; exact H|
right; right; left; destruct H as (p & n & Hin & Hp); exists p, n; split; [exact (LV _ Hin)| exact Hp]|
right; right; right; left; destruct H as (f' & k' & Hin & Hf); exists f', k'; split; [right; exact Hin| exact Hf]|
right; right; right; right; destruct H as (f' & k' & Hin & Hf); exists f', k'; split; [right; exact Hin| exact Hf]].
Qed.

Lemma live_nodup : forall (Σ : rts RT) (m : mem) L pre rest, ART RT Σ m -> rt_live RT Σ = pre ++ L ++ rest ->
(forall e, In e L -> 0 < snd e) -> List.NoDup (map fst L).
Proof using AF.
intros Σ m L. induction L as [|[p n] L IH]; intros pre rest ART0 E POS; [constructor|].
cbn [map fst]. constructor.
- intros Hin. apply in_map_iff in Hin. destruct Hin as ([p2 n2] & E2 & Hin). cbn [fst] in E2. subst p2.
pose proof (POS (p, n) ltac:(left; reflexivity)) as P1. pose proof (POS (p, n2) ltac:(right; exact Hin)) as P2. cbn [snd] in P1, P2.
destruct (af_live_disj RT AF Σ m p n p n2 pre (L ++ rest) ART0 E ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hin)); lia.
- apply (IH (pre ++ [(p, n)]) rest ART0); [rewrite <- app_assoc; exact E| intros e He; apply POS; right; exact He].
Qed.
End KitX.

Ltac cps_release_intro_sub ARTc EF SUBL PREL Σ2 fl :=
lazymatch type of EF with
| rt_frames ?RT ?Σ1 = (?f, ?k) :: ?fr =>
lazymatch type of ARTc with
| ART RT Σ1 ?m =>
let fszb := eval vm_compute in (fs_size k - 8) in
let FLC := fresh "FLC" in let NAC := fresh "NAC" in let FL0 := fresh "FL0" in let FLW := fresh "FLW" in let FW := fresh "FW" in
let REL := fresh "REL" in
destruct (af_frame_release RT ltac:(eassumption) Σ1 m f k fr ARTc EF PREL) as (Σ2 & fl & FLC & NAC & FL0 & FLW & FW & REL);
change (fs_size k - 8) with fszb in FW; replace (f + fs_size k - 8) with (f + fszb) in FW by (change (fs_size k) with (fszb + 8); lia);
match goal with LO : rt_sp0 RT Σ1 - _ <= ?lo |- _ => let B := fresh "BFL" in assert (B : fl + 1 <= lo) by ulc end;
cps_norm;
lazymatch goal with
| PF : rt_pres_fp (rt_live RT ?Σ) (rt_frames RT ?Σ) ?U0 _ _ _ |- _ =>
let NFL := fresh "NFL" in
pose proof (fun a (Ha : aclient (rt_live RT Σ) (rt_frames RT Σ) U0 a) =>
flag_not_client_sub RT Σ Σ1 f k U0 fl a EF SUBL NAC ltac:(ulc) Ha) as NFL
| _ => idtac
end
end
end.

Lemma zbuf_recast : forall n m A, (n <= 80)%nat -> rw_cells asegs m A [CB (4 * n) (zb (4 * n))] -> rw_cells asegs m A (f32 (zw n)).
Proof.
intros n m A Hn X. apply (rw_cells_recast asegs m A _ (f32 (zw n)) X); [apply cells_wf_f32|].
do 81 (destruct n as [|n]; [vm_compute; reflexivity|]). exfalso. lia.
Qed.

Lemma sbi_frame_rec : forall (m : mem) usp (c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 : cell) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word),
rw_cells asegs m (usp + -192) [c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
cells_size [c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80] = 88%nat ->
rw_cells asegs m (usp + -16) [C8 s0; C8 ra].
Proof.
intros m usp c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra X SZ.
change [c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
with (([c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80] ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1]) ++ [C8 s0; C8 ra]) in X.
apply (proj1 (rw_cells_app asegs m _ _ _)) in X. destruct X as [_ X].
rewrite cells_size_app, SZ in X. cbn [cells_size csize Nat.add] in X.
replace (usp + -16) with (usp + -192 + Z.of_nat (88 + 88)) by lia. exact X.
Qed.

Definition init_stack (mo : spx_mode) : Z := match mo with ModeNB => 64 | ModeWB => 288 | ModeUWB => 480 end.
Definition init_nblocks (mo : spx_mode) : Z := match mo with ModeNB => 1 | ModeWB => 10 | ModeUWB => 19 end.

Definition init_credit (mo : spx_mode) : Z := match mo with ModeNB => 0 | ModeWB => 1 | ModeUWB => 4 end.
Definition mode_depth (mo : spx_mode) : nat := match mo with ModeNB => 1 | ModeWB => 2 | ModeUWB => 3 end.

Section InitCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis CAL : calloc_contract RT.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.

Definition init_cps_at (mo : spx_mode) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (lo : Z) (ras : list Z) (OUT STEREO : Z),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 (sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode mo) -> tp = Z_to_bv 64 0x630458 ->
Z.of_nat (length (rt_live RT Σ)) + init_nblocks mo <= LIVE_MAX -> init_credit mo <= rt_credit RT Σ ->
(length (rt_frames RT Σ) + mode_depth mo <= FRAMES_MAX)%nat ->
init_traces mo (bv_unsigned ra) ras -> uw_entry m s0 (bv_unsigned sp) lo ras ->
ART RT Σ m -> mem_inv asegs m -> frm0 fc ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + init_stack mo <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_decoder_init m)))
(fun c => exists (Σ' : rts RT) (D : Z) (LBD : list block) (NEW : list (Z * Z)),
ASTA RT Σ' PMc (fun ms => exists m',
ret_stL (fun _ fc' => frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 D) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [] m m'
/\ DREP OUT STEREO m' D (init_dec mo) LBD) c
/\ rt_live RT Σ' = NEW ++ rt_live RT Σ /\ Permutation NEW (blocks_live LBD) /\ List.NoDup (map blk_id LBD) /\ Z.of_nat (length NEW) = init_nblocks mo
/\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ - init_credit mo <= rt_credit RT Σ' <= rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ
/\ (forall x, In x LBD -> blk_addr x mod 8 = 0)).

Theorem init_cps_nb : init_cps_at ModeNB.
Proof using AF CAL MSET AF_LIB.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ras OUT STEREO
FDO MST E0 ETP LVM CR0 FRM TR UE ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
cbn [init_traces init_nblocks init_credit init_stack sb_mode_ptr] in *.
intros T c Hc Hk.
refine (nb_decoder_init_ok RT AF CAL MSET AF_LIB Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
FDO MST E0 ETP ltac:(lia) ltac:(lia) _ ART0 MI0 ST0 LOW LOR SPT ltac:(clear - SPA; Z.div_mod_to_equations; lia) T c Hc _).
{ exists ras. split; [exact TR| exact UE]. }
intros c' (Σ' & D & Hc' & LV & FRS & SP0 & CR & PO). apply Hk.
assert (D8 : D mod 8 = 0).
{ destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms & (m' & _ & _ & _ & REP) & _). specialize (REP OUT STEREO). cbn [decst_rep] in REP. destruct REP as (_ & AL & _). exact AL. }
exists Σ', D, [(tt, D, NBSTATE_SIZEOF)], [(D, NBSTATE_SIZEOF)].
split; [| split; [exact LV|]; split; [apply Permutation_refl|]; split; [repeat constructor; intros []|]; split; [reflexivity|]; split; [exact FRS|]; split; [exact SP0|];
split; [lia| split; [exact PO| intros x [<-|[]]; exact D8]]].
eapply ASTA_conseq; [exact Hc'|]. intros ms (m' & RS & AFT & PF & REP). exists m'.
split; [| split; [exact AFT|]; split; [exact PF| exact (REP OUT STEREO)]].
unfold ret_stL in *. destruct RS as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & F' & fc' & E & -> & ->).
do 16 eexists. split; [exact E| exact FRM0].
Qed.

Definition sb_sm_ptr (mo : spx_mode) : Z := match mo with ModeUWB => A_sb_uwb_mode | _ => A_sb_wb_mode end.
Lemma sb_mode_facts : forall mo (m : mem), mo <> ModeNB -> lib_consts m ->
exists (c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12 g1 g2 lf fg sm0 sm1 sm2 sm3 sm4 sm5 sm6 sm7 : word) (pad : list byte),
ro_cells asegs m (sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode mo) (sbi_desc_cells (Z_to_bv 64 (sb_sm_ptr mo)) c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12)
/\ ro_cells asegs m (sb_sm_ptr mo) (sbmode_cells (sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (low_mode mo)) (sbm_frameSize mo) (sbm_subframeSize mo) 8
g1 g2 lf fg pad sm0 sm1 sm2 sm3 sm4 sm5 sm6 sm7 (sbm_defaultSubmode mo))
/\ length pad = 4%nat.
Proof.
intros mo m NE LC. destruct mo; [congruence| |].
- pose proof (lib_const m A_speex_wb_mode LC_speex_wb_mode LC ltac:(lc_in)) as D.
pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as B.
rewrite <- (firstn_skipn 18 LC_sb_wb_mode) in B. apply (proj1 (ro_cells_app asegs m _ _ _)) in B. destruct B as [B _].
unfold LC_sb_wb_mode in B. cbn [firstn] in B. unfold LC_speex_wb_mode in D.
do 24 eexists. cbn [sb_mode_ptr sb_sm_ptr low_mode sbm_frameSize sbm_subframeSize sbm_defaultSubmode].
split; [exact D|]. split; [exact B| reflexivity].
- pose proof (lib_const m A_speex_uwb_mode LC_speex_uwb_mode LC ltac:(lc_in)) as D.
pose proof (lib_const m A_sb_uwb_mode LC_sb_uwb_mode LC ltac:(lc_in)) as B.
rewrite <- (firstn_skipn 18 LC_sb_uwb_mode) in B. apply (proj1 (ro_cells_app asegs m _ _ _)) in B. destruct B as [B _].
unfold LC_sb_uwb_mode in B. cbn [firstn] in B. unfold LC_speex_uwb_mode in D.
do 24 eexists. cbn [sb_mode_ptr sb_sm_ptr low_mode sbm_frameSize sbm_subframeSize sbm_defaultSubmode].
split; [exact D|]. split; [exact B| reflexivity].
Qed.
Lemma sb_mode_arith : forall mo, mo <> ModeNB ->
let MP := sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode mo in let SM := sb_sm_ptr mo in
MP mod 8 = 0 /\ 0x10000 <= MP /\ MP + 104 <= 0x652000 /\ In (MP, 96) ACC_LITS
/\ SM mod 8 = 0 /\ 0x10000 <= SM /\ SM + 216 <= 0x652000 /\ In (SM, 216) ACC_LITS
/\ SM + 40 = sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR mo
/\ ((sbm_frameSize mo = 160 /\ sbm_subframeSize mo = 40) \/ (sbm_frameSize mo = 320 /\ sbm_subframeSize mo = 80))
/\ - 2^31 <= sbm_defaultSubmode mo < 2^31.
Proof.
intros mo NE. destruct mo; [congruence| |]; cbn [sb_mode_ptr sb_sm_ptr sb_submodes_ptr sbm_frameSize sbm_subframeSize sbm_defaultSubmode];
unfold A_speex_wb_mode, A_speex_uwb_mode, A_sb_wb_mode, A_sb_uwb_mode, WB_SUBMODES_PTR, UWB_SUBMODES_PTR, A_sb_wb_mode, A_sb_uwb_mode, ACC_LITS; cbn [In];
(split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [repeat (first [left; reflexivity | right])|];
split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [repeat (first [left; reflexivity | right])|]; split; [reflexivity|]; split; [| lia]).
- left. split; reflexivity.
- right. split; reflexivity.
Qed.

Lemma newchunks_apart : forall (Σ Σ1 : rts RT) (m1 : mem) NEW L usp a p n,
ART RT Σ1 m1 -> rt_live RT Σ1 = NEW ++ L -> (forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT Σ1)) -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
rt_sp0 RT Σ - STACK_WIN <= usp -> In (p, n) NEW -> aclient L (rt_frames RT Σ) usp a -> ~ (p <= a < p + n).
Proof using AF.
intros Σ Σ1 m1 NEW L usp a p n ART1 LV FRS SP0 LU INN Ha Hin.
assert (INL : In (p, n) (rt_live RT Σ1)) by (rewrite LV; apply in_app_iff; left; exact INN).
pose proof (af_live_range RT AF Σ1 m1 p n ART1 INL) as (L0 & L1 & L2). rewrite SP0 in L1.
destruct Ha as [H|[H|[H|[H|H]]]].
- lia.
- pose proof (client_static_range a H). unfold SEGTOP_A in *. lia.
- destruct H as (p' & n' & Hin' & Hp').
destruct (in_split _ _ INN) as (n1 & n2 & EN). rewrite EN, <- app_assoc in LV. cbn [app] in LV.
destruct (af_live_disj RT AF Σ1 m1 p n p' n' n1 (n2 ++ L) ART1 LV ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hin')); lia.
- destruct H as (f & k & Hinf & Hf). apply FRS in Hinf.
pose proof (af_frames_range RT AF Σ1 m1 f k ART1 Hinf) as (_ & _ & _ & R3). destruct (R3 p n INL); lia.
- destruct H as (f & k & Hinf & Hf). apply FRS in Hinf.
pose proof (af_fshadow_apart RT AF Σ1 m1 f k ART1 Hinf) as (SL & _). destruct (SL p n INL); lia.
Qed.

Ltac sigma_app EL EF ES :=
lazymatch type of ES with
| rt_sp0 ?RT ?Σ' = rt_sp0 ?RT ?Σ =>
repeat match goal with
| H : In ?e0 (rt_live RT Σ) |- _ =>
let H' := fresh H in assert (H' : In e0 (rt_live RT Σ')) by (rewrite EL; apply in_app_iff; right; exact H); clear H; rename H' into H
end;
repeat match goal with H : rt_sp0 RT Σ - _ <= _ |- _ => rewrite <- ES in H end;
repeat match goal with H : In ?e0 (rt_frames RT Σ) |- _ => rewrite <- EF in H end
end.

Lemma drep_head : forall OUT STEREO (m : mem) S (d : dec_state bptr) LBD, DREP OUT STEREO m S d LBD -> exists n, In (tt, S, n) LBD /\ 0 < n /\ S mod 8 = 0.
Proof.
intros OUT STEREO m S d LBD H. destruct d as [st|s low]; cbn [decst_rep] in H.
- destruct H as [-> NB]. exists NBSTATE_SIZEOF. destruct (nb_blk st). split; [left; reflexivity|]. split; [unfold NBSTATE_SIZEOF; lia| exact (proj1 NB)].
- destruct H as (a & j & LBL & -> & S8 & _). exists SBSTATE_SIZEOF. destruct (sbd_blk s) eqn:E. split; [left; cbn [sb_blocks]; rewrite E; reflexivity|].
split; [unfold SBSTATE_SIZEOF; lia| exact S8].
Qed.
Lemma drep_sizes_pos : forall (d : dec_state bptr) OUT STEREO (m : mem) S LBD, DREP OUT STEREO m S d LBD -> forall b, In b LBD -> 0 < blk_size b.
Proof.
induction d as [st|s low IHd]; intros OUT STEREO m S LBD H b Hb; cbn [decst_rep] in H.
- destruct H as [-> _]. destruct Hb as [<-|[]]. unfold blk_size, NBSTATE_SIZEOF. cbn. lia.
- destruct H as (a & j & LBL & -> & _ & _ & INV & _ & _ & _ & OUTL & RL). apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| exact (IHd _ _ _ _ _ RL b Hb)].
destruct INV as (IM & _ & _ & ISF & _). assert (0 < sbd_subframeSize s) by (rewrite ISF; destruct IM as [E|E]; rewrite E; cbn; lia).
cbn [sb_blocks In] in Hb. unfold SBSTATE_SIZEOF in Hb.
repeat (destruct Hb as [<-|Hb]; [unfold blk_size; cbn [snd]; lia|]). destruct Hb.
Qed.

Lemma new_old_apart : forall (Σ : rts RT) (m : mem) NEW L p1 n1 p2 n2, ART RT Σ m -> rt_live RT Σ = NEW ++ L -> In (p1, n1) NEW -> In (p2, n2) L ->
p1 + n1 <= p2 \/ p2 + n2 <= p1.
Proof using AF.
intros Σ m NEW L p1 n1 p2 n2 ART0 LV H1 H2. destruct (in_split _ _ H1) as (l1 & l2 & E). rewrite E, <- app_assoc in LV. cbn [app] in LV.
apply (af_live_disj RT AF Σ m p1 n1 p2 n2 l1 (l2 ++ L) ART0 LV). apply in_app_iff. right. apply in_app_iff. right. exact H2.
Qed.

Lemma zero_chunk : forall (m : mem) B n, 0 <= n -> wr_at asegs m B n -> bytes_at asegs m B (repeat (Z_to_bv 8 0) (Z.to_nat n)) ->
rw_cells asegs m B [CB (Z.to_nat n) (zb (Z.to_nat n))].
Proof.
intros m B n N0 WR BY. split; [split; [split; [unfold zb; apply repeat_length| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BY]|].
cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact WR.
Qed.
Definition zbufs (m : mem) (BL : list block) : Prop :=
forall b, In b BL -> 0 <= blk_size b /\ rw_cells asegs m (blk_addr b) [CB (Z.to_nat (blk_size b)) (zb (Z.to_nat (blk_size b)))].
Lemma zbufs_nil : forall m, zbufs m []. Proof. intros m b []. Qed.
Lemma zbufs_cons : forall (m : mem) B n BL, 0 <= n -> rw_cells asegs m B [CB (Z.to_nat n) (zb (Z.to_nat n))] -> zbufs m BL -> zbufs m ((tt, B, n) :: BL).
Proof. intros m B n BL N0 X Z b [<-|Hb]; [split; [exact N0| exact X]| exact (Z b Hb)]. Qed.
Lemma zbufs_agree : forall (m m' : mem) BL, zbufs m BL -> agree_blocks asegs m m' BL -> zbufs m' BL.
Proof.
intros m m' BL Z AG b Hb. destruct (Z b Hb) as [N0 X]. split; [exact N0|].
apply (rw_cells_agree_at asegs m m' _ _ X). apply (agree_blocks_at asegs m m' BL b _ _ AG Hb X); [lia|].
cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. lia.
Qed.

Lemma rw_cells_pres_cl : forall live frames sp (m m' : mem) A cs, rt_pres live frames sp m m' -> wmono asegs m m' -> rw_cells asegs m A cs ->
(forall x, A <= x < A + Z.of_nat (cells_size cs) -> aclient live frames sp x) -> rw_cells asegs m' A cs.
Proof. intros live frames sp m m' A cs PR WM X CL. apply (rw_cells_agree asegs m m' A cs X); [apply (agree_of_pres live frames sp m m' _ PR); exact CL| exact WM]. Qed.
Lemma rw_cells_pres_stack : forall live frames sp (m m' : mem) A cs n, rt_pres live frames sp m m' -> wmono asegs m m' -> rw_cells asegs m A cs ->
Z.of_nat (cells_size cs) = n -> sp <= A -> A + n <= USTACK_TOP -> rw_cells asegs m' A cs.
Proof. intros live frames sp m m' A cs n PR WM X E H1 H2. apply (rw_cells_pres_cl live frames sp m m' A cs PR WM X). intros x Hx. left. lia. Qed.
Lemma rw_cells_pres_live : forall live frames sp (m m' : mem) A cs n p k, rt_pres live frames sp m m' -> wmono asegs m m' -> rw_cells asegs m A cs ->
Z.of_nat (cells_size cs) = n -> In (p, k) live -> p <= A -> A + n <= p + k -> rw_cells asegs m' A cs.
Proof. intros live frames sp m m' A cs n p k PR WM X E IN H1 H2. apply (rw_cells_pres_cl live frames sp m m' A cs PR WM X). intros x Hx. right; right; left. exists p, k. split; [exact IN| lia]. Qed.
Lemma rw_cells_pres_frame : forall live frames sp (m m' : mem) A cs n f k, rt_pres live frames sp m m' -> wmono asegs m m' -> rw_cells asegs m A cs ->
Z.of_nat (cells_size cs) = n -> In (f, k) frames -> f <= A -> A + n <= f + fs_size k - 8 -> rw_cells asegs m' A cs.
Proof. intros live frames sp m m' A cs n f k PR WM X E IN H1 H2. apply (rw_cells_pres_cl live frames sp m m' A cs PR WM X). intros x Hx. right; right; right; left. exists f, k. split; [exact IN| lia]. Qed.
Lemma rw_cells_pres_fshadow : forall live frames sp (m m' : mem) A cs n f k, rt_pres live frames sp m m' -> wmono asegs m m' -> rw_cells asegs m A cs ->
Z.of_nat (cells_size cs) = n -> In (f, k) frames -> shad f <= A -> A + n <= shad (f + fs_size k) -> rw_cells asegs m' A cs.
Proof. intros live frames sp m m' A cs n f k PR WM X E IN H1 H2. apply (rw_cells_pres_cl live frames sp m m' A cs PR WM X). intros x Hx. right; right; right; right. exists f, k. split; [exact IN| lia]. Qed.

Theorem init_cps_sb : forall mo, mo <> ModeNB -> init_cps_at (low_mode mo) -> init_cps_at mo.
Proof using AF CAL SM0 AF_LIB.
intros mo NENB IH Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ras OUT STEREO
FDO MST -> -> LVM CR0 FRM TR UE ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
destruct (init_traces_low mo _ _ NENB TR) as (TRS & TRL). clear TR.
assert (EDEC : init_dec mo = sb_wrap mo (init_dec (low_mode mo))) by (destruct mo; [congruence| reflexivity| reflexivity]).
assert (STK : init_stack mo = 192 + Z.max (init_stack (low_mode mo)) (ctl_stack (init_dec (low_mode mo)))) by (destruct mo; [congruence| reflexivity| reflexivity]).
assert (NBL : init_nblocks mo = 9 + init_nblocks (low_mode mo)) by (destruct mo; [congruence| reflexivity| reflexivity]).
assert (CRL : init_credit mo = 1 + init_credit (low_mode mo) + 2 * (Z.of_nat (mode_depth (low_mode mo)) - 1)) by (destruct mo; [congruence| reflexivity| reflexivity]).
assert (DPL : mode_depth mo = S (mode_depth (low_mode mo))) by (destruct mo; [congruence| reflexivity| reflexivity]).
assert (DDL : dec_depth (init_dec (low_mode mo)) = mode_depth (low_mode mo)) by (destruct mo; reflexivity).
assert (LST : 0 <= init_stack (low_mode mo)) by (destruct mo; cbn; lia).
assert (LNB : 1 <= init_nblocks (low_mode mo)) by (destruct mo; cbn; lia).
assert (LCR : 0 <= init_credit (low_mode mo)) by (destruct mo; cbn; lia).
assert (LDP : (1 <= mode_depth (low_mode mo) <= 2)%nat) by (destruct mo; cbn; lia).
rewrite STK in LOR. rewrite NBL in LVM. rewrite CRL in CR0. rewrite DPL in FRM.
set (lowmo := low_mode mo) in *. set (LSTK := init_stack lowmo) in *. set (CSTK := ctl_stack (init_dec lowmo)) in *.
set (LNBL := init_nblocks lowmo) in *. set (LCRD := init_credit lowmo) in *. set (LDEP := mode_depth lowmo) in *.
assert (CST : 0 <= CSTK) by (subst CSTK; generalize (init_dec lowmo); intros d; induction d; cbn [ctl_stack]; unfold NBCTL_STACK; lia).

destruct (sb_mode_arith mo NENB) as (MP8 & MPLO & MPHI & MPLIT & SM8 & SMLO & SMHI & SMLIT & ESUB & GEO & DSR).
pose proof (fun m (LC : lib_consts m) => sb_mode_facts mo m NENB LC) as MODEK. fold lowmo in MODEK.
set (MP := sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode mo) in *.
set (NBM := sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode lowmo) in *.
set (SM := sb_sm_ptr mo) in *. set (fs := sbm_frameSize mo) in *. set (sfs := sbm_subframeSize mo) in *. set (dsm := sbm_defaultSubmode mo) in *.
pose proof (eq_refl : MP = sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode mo) as EMP. clearbody MP.
pose proof (eq_refl : NBM = sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode lowmo) as ENBM. clearbody NBM.
pose proof (eq_refl : SM = sb_sm_ptr mo) as ESM. clearbody SM.
pose proof (eq_refl : fs = sbm_frameSize mo) as EFS. clearbody fs. pose proof (eq_refl : sfs = sbm_subframeSize mo) as ESFS. clearbody sfs.
pose proof (eq_refl : dsm = sbm_defaultSubmode mo) as EDSM. clearbody dsm.
destruct (MODEK m (AF_LIB Σ m ART0)) as (c1 & c2 & c3 & c4 & c5 & c6 & c7 & c9 & c10 & c11 & c12 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND0 & _ & _).
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
assert (OBM : aobj asegs m MP 96) by (apply (aobj_lit RT AF Σ m MP 96 ART0 MPLIT); unfold APP_TOP; lia).
pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
assert (LOS : SH_HI <= lo) by (unfold SH_HI, STACK_WIN in *; lia).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [] m) as PF.
pose proof (fun E : rt_frames RT Σ = [] => af_pois_nil RT AF Σ m ART0 E) as PNIL.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
assert (LO192 : lo <= usp + -192) by (clear - LOR LST; unfold RT_STACK in LOR; lia).
cps_norm. cps_hide.

cps_seg (sbinit_w1 usp lo MP).
destruct POST as (m1 & j8 & j16 & j24 & j32 & j40 & j48 & j56 & j64 & j72 & j80 & xt1 & xa3 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
cps_seg_post.

cps_rt_sized SM0 0. { cbn; tauto. } { cps_callok. }
intros cc2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP & PO1).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS).
cps_new_frame ART2 FRS1 LV1 SP1 WRF WRS sf. cps_hide.

cps_seg (sbinit_w2 usp lo MP f sf).
destruct POST as (m3 & xa2 & xa3' & k24 & l32 & k36 & k40 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & FRB3 & FRS3).
clear FR1 FRB FRS.
cps_seg_post.
assert (SUBF1 : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT Σ1)) by (intros e He; rewrite FRS1; right; exact He).
assert (SUBL1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ1)) by (intros e He; rewrite LV1; exact He).

assert (UW3 : unwind_ch m3 (Z_to_bv 64 RA_sbinit_calloc0) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))).
{ apply (sbinit_site_ch (rt_live RT Σ) (rt_frames RT Σ) m m3 s0 ra usp lo ras RA_sbinit_calloc0 UE PF (sbi_frame_rec m3 usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR3 eq_refl));
[apply TRS; unfold SBINIT_SITES, RA_sbinit_calloc0; cbn [In]; tauto| ulc| clear - SPA; Z.div_mod_to_equations; lia| ulc| ulc| unfold RA_sbinit_calloc0; lia]. }
cps_rt CAL.
{ rewrite LV1. clear - LVM LNB. lia. } { change (mcost (160 * 1)) with 0. rewrite CR1. clear - CR0 LCR LDP. lia. } { cps_callok. }
intros cc4 (Σ2 & S & Hc4 & LV2 & FRS2 & SP2 & CR2 & SPOS & S16 & STOP & PO2).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
change (160 * 1) with 160 in *. change (mcost 160) with 0 in CR2. rewrite Z.sub_0_r in CR2. change (Z.to_nat 160) with 160%nat in *.
cps_unpack Hc4 as (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & WRS4 & ACS4 & BYS4).
assert (SUBF2 : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT Σ2)) by (intros e He; rewrite FRS2; exact (SUBF1 e He)).
assert (SUBL2 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ2)) by (intros e He; rewrite LV2; right; exact (SUBL1 e He)).
pose proof (fun a (Ha : aclient (rt_live RT Σ) (rt_frames RT Σ) usp a) =>
newchunks_apart Σ Σ2 m4 [(S, 160)] (rt_live RT Σ) usp a S 160 ART4 ltac:(rewrite LV2, LV1; reflexivity) SUBF2 ltac:(rewrite SP2; exact SP1)
ltac:(ulc) ltac:(left; reflexivity) Ha) as NAS.
cps_sigma LV2 FRS2 SP2.
destruct (live_below_lo RT AF Σ2 m4 S 160 lo ART4 INL LOW) as (_ & BS1 & _).
pose proof (live_facts RT AF Σ2 m4 S 160 ART4 INL) as (_ & _ & SIMG & SHI).
destruct (frame_live_apart RT AF Σ2 m4 f 0%nat S 160 ART4 INF INL) as (FLA1 & FLA2).
change (fs_size 0) with 64 in FLA1, FLA2. rewrite SHF0, <- SHF in FLA2.
assert (S8 : S mod 8 = 0) by (clear - S16; Z.div_mod_to_equations; lia).
assert (BLK : rw_cells asegs m4 S [CB 160 (repeat (Z_to_bv 8 0) 160)]).
{ split; [split; [split; [vm_compute; reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BYS4]| exact WRS4]. }
apply sbst_zero_recast in BLK. clear BYS4 WRS4.
assert (OBS4 : aobj asegs m4 S 160) by (split; [lia|]; split; [ulc| exact ACS4]).
assert (OBM4 : aobj asegs m4 MP 96) by (apply (aobj_lit RT AF Σ2 m4 MP 96 ART4 MPLIT); ulc).
assert (OBSM4 : aobj asegs m4 SM 216) by (apply (aobj_lit RT AF Σ2 m4 SM 216 ART4 SMLIT); ulc).
destruct (MODEK m4 (AF_LIB Σ2 m4 ART4)) as (d1 & d2 & d3 & d4 & d5 & d6 & d7 & d9 & d10 & d11 & d12 & g1 & g2 & lf & fg & sm0 & sm1 & sm2 & sm3 & sm4 & sm5 & sm6 & sm7 & pad & ND4 & NS4 & LPAD).
cps_hide.

cps_seg (sbinit_w3 usp S MP SM NBM f sf fs sfs 8 dsm).
destruct POST as (m5 & xa1 & -> & MU5 & WM5 & MI5 & X5).
clear BLK OBS4 OBM4 OBSM4 ND4 NS4.
cps_seg_post.

assert (UE5 : uw_entry m5 (Z_to_bv 64 usp) (usp + -192) lo (bv_unsigned ra :: ras)).
{ apply (sbinit_low_entry (rt_live RT Σ) (rt_frames RT Σ) m m5 s0 ra usp lo ras UE PF (sbi_frame_rec m5 usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR3 eq_refl));
[ulc| clear - SPA; Z.div_mod_to_equations; lia| ulc| ulc]. }
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end;
[ eapply (IH Σ2 PMc) with (lo := lo) (ras := bv_unsigned ra :: ras) (OUT := 0) (STEREO := STEREO); cps_auto | ].
{ rewrite ENBM. reflexivity. }
{ rewrite LV2, LV1. cbn [length]. fold LNBL. clear - LVM. lia. }
{ fold LCRD. rewrite CR2, CR1. clear - CR0 LDP. lia. }
{ rewrite FRS2, FRS1. cbn [length]. fold LDEP. clear - FRM. lia. }
{ rewrite unsigned_lit by ulc. exact UE5. }
{ rewrite unsigned_lit by ulc. eassumption. }
{ rewrite unsigned_lit by ulc. fold LSTK. pose proof (Z.le_max_l LSTK CSTK) as MX. unfold RT_STACK. clear - LOR MX. lia. }
{ rewrite unsigned_lit by ulc. ulc. }
{ rewrite unsigned_lit by ulc. clear - SPA. Z.div_mod_to_equations. lia. }
intros cc6 (Σ3 & AL & LBL & NEWL & Hc6 & LV3 & PERM3 & NDL & LENL & FRS3' & SP3 & CR3 & PO3 & AL8L).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
destruct (ASTA_unpack RT Σ3 PMc _ cc6 Hc6) as (ms6 & PO6 & Hc6'). clear Hc6. cbv beta in PO6.
destruct PO6 as (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & RL6).
destruct RS6 as (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & F6 & fc6 & -> & FRM6).
rewrite (unsigned_lit (usp + -192)) in * by ulc.
cps_unpack_tr PRES6 m5.
assert (SUBF3 : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT Σ3)) by (intros e He; rewrite FRS3'; exact (SUBF2 e He)).
assert (SUBL3 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ3)) by (intros e He; rewrite LV3; apply in_app_iff; right; exact (SUBL2 e He)).
assert (LIVEL : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT Σ3)).
{ intros b Hb. rewrite LV3. apply in_app_iff. left. apply (Permutation_in _ (Permutation_sym PERM3)). unfold blocks_live. apply (in_map (fun b => (blk_addr b, blk_size b))). exact Hb. }
assert (NAL : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> outside (blocks_ivs LBL) a).
{ intros a Ha. apply outside_blocks_ivs. intros b Hb.
apply (newchunks_apart Σ Σ3 m6 NEWL (rt_live RT Σ2) usp a (blk_addr b) (blk_size b) ART6 LV3 SUBF3 ltac:(rewrite SP3, SP2; exact SP1) ltac:(ulc)).
- apply (Permutation_in _ (Permutation_sym PERM3)). unfold blocks_live. apply (in_map (fun b => (blk_addr b, blk_size b))). exact Hb.
- apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) usp _ (rt_frames RT Σ) usp a Ha); [exact SUBL2| auto| lia]. }
sigma_app LV3 FRS3' SP3.
destruct (drep_head 0 STEREO m6 AL _ LBL RL6) as (nl & HAL & NLP & AL8).
pose proof (LIVEL _ HAL) as INAL. unfold blk_addr, blk_size in INAL. cbn [fst snd] in INAL.
destruct (live_below_lo RT AF Σ3 m6 AL nl lo ART6 INAL LOW) as (AL0 & AL1 & _).
destruct (af_acc_live RT AF Σ3 m6 S 160 ART6 INL) as (_ & ACS6).
assert (OBS6 : aobj asegs m6 S 160) by (split; [lia|]; split; [ulc| exact ACS6]).
assert (OBSM6 : aobj asegs m6 SM 216) by (apply (aobj_lit RT AF Σ3 m6 SM 216 ART6 SMLIT); ulc).
destruct (MODEK m6 (AF_LIB Σ3 m6 ART6)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & g1' & g2' & lf' & fg' & sm0' & sm1' & sm2' & sm3' & sm4' & sm5' & sm6' & sm7' & pad' & _ & NS6 & LPAD').
cps_hide.

cps_seg (sbinit_w4 usp lo S MP SM NBM AL f sf fs sfs dsm).
{ clear - AL0 AL1 NLP LO192 SPT. unfold USTACK_TOP in SPT. lia. }
destruct POST as (m7 & ya3 & ya4 & ya5 & ya6 & ya7 & -> & MU7 & WM7 & MI7 & ST7 & X7 & FR7).
assert (BOUTL : forall b x, In b LBL -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x Hb Hx. pose proof (LIVEL b Hb) as LB.
destruct (live_below_lo RT AF Σ3 m6 _ _ lo ART6 LB LOW) as (_ & B1 & _).
destruct (frame_live_apart RT AF Σ3 m6 f 0%nat _ _ ART6 INF LB) as (B2 & B3). change (fs_size 0) with 64 in B2, B3. rewrite SHF0, <- SHF in B3.
pose proof (new_old_apart Σ3 m6 NEWL (rt_live RT Σ2) _ _ S 160 ART6 LV3
ltac:(apply (Permutation_in _ (Permutation_sym PERM3)); unfold blocks_live; apply (in_map (fun b => (blk_addr b, blk_size b))); exact Hb)
ltac:(rewrite LV2; left; reflexivity)) as B4.
clear - B1 B2 B3 B4 Hx. lia. }
assert (SNL : ~ In S (map blk_id LBL)).
{ intros Hin. apply in_map_iff in Hin. destruct Hin as (b & Eb & Hb). unfold blk_id in Eb.
pose proof (drep_sizes_pos _ _ _ _ _ _ RL6 b Hb) as PB. destruct (BOUTL b (blk_addr b) Hb ltac:(lia)) as (_ & B & _). clear - B Eb. lia. }
pose proof (agree_blocks_of_munch asegs _ m6 m7 LBL MU7 WM7
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1 LO192; cbn [outside]; repeat split; lia)) as AG7.
eapply decst_rep_agree in RL6; [| exact AG7]. clear AG7.
clear X5 FR3 OBS6 OBSM6 NS6 ACS6.
cps_seg_post.

apply (proj1 (rw_cells_app asegs m7 S [_; _; _; _; _; _; _; _] (_ :: _))) in X7. destruct X7 as [XA X7].
change (Z.of_nat (cells_size _)) with 40 in X7. chunk_uncons X7 as XP. replace (S + 40 + 4) with (S + 44) in X7 by lia.
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end;
[ eapply (ctl_gsr_live_all RT AF SM0 AF_LIB (init_dec lowmo) Σ3 PMc) with (OUT := 0) (STEREO := STEREO) (LBD := LBL) (P := S + 40) (lo := lo) (pb := S) (nb := 160); cps_auto | ].
{ exists w0. exact XP. }
{ rewrite DDL, FRS3', FRS2, FRS1. cbn [length]. fold LDEP. clear - FRM. lia. }
{ rewrite DDL. fold LDEP. clear - CR3 CR2 CR1 CR0 LCR LDP. fold LCRD in CR3. lia. }
{ rewrite unsigned_lit by ulc. eassumption. }
{ rewrite unsigned_lit by ulc. fold CSTK. pose proof (Z.le_max_r LSTK CSTK) as MX. unfold RT_STACK. clear - LOR MX. lia. }
{ rewrite unsigned_lit by ulc. ulc. }
{ rewrite unsigned_lit by ulc. clear - SPA. Z.div_mod_to_equations. lia. }
intros cc8 (Σ4 & Hc8 & LV4 & FRS4 & SP4 & CR4 & PO4).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
destruct (ASTA_unpack RT Σ4 PMc _ cc8 Hc8) as (ms8 & PO8 & Hc8'). clear Hc8. cbv beta in PO8.
destruct PO8 as (m8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & RL8 & XP8 & RNG8).
destruct RS8 as (yt0 & yt1 & yt2 & yb1 & yb2 & yb3 & yb4 & yb5 & yb6 & yb7 & yt3 & yt4 & yt5 & yt6 & F8 & fc8 & -> & FRM8).
rewrite (unsigned_lit (usp + -192)) in * by ulc.
replace (S + 40 + 4) with (S + 44) in PRES8 by lia.
assert (OUTB : forall x, (lo <= x \/ (S <= x < S + 160) \/ (f <= x < f + 64) \/ (sf <= x < sf + 8)) -> outside (blocks_ivs LBL) x).
{ intros x Hx. apply outside_blocks_ivs. intros b Hb Hin. pose proof (BOUTL b x Hb Hin) as H1. clear - Hx H1. lia. }
xfp PRES8 WM8 OUTB XA. xfp PRES8 WM8 OUTB X7. xfp PRES8 WM8 OUTB FR7. xfp PRES8 WM8 OUTB FRB3. xfp PRES8 WM8 OUTB FRS3.
assert (PF8 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp [] m m8).
{ apply (pres_fp_trans _ _ _ _ m m7 m8 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ3) (rt_frames RT Σ3) (usp + -192) _ m7 m8 PRES8); [exact SUBL3| exact SUBF3| lia|].
intros x Hx _. cbn [outside]. split; [pose proof (NAS x Hx) as N; clear - N; cbn [fst snd]; lia| exact (NAL x Hx)]. }
clear PF PRES8 RL6 XP. rename PF8 into PF.
cps_sigma LV4 FRS4 SP4.
repeat match goal with A : X0ec.ART RT _ m7 |- _ => clear A | A : mem_inv asegs m7 |- _ => clear A | A : stk asegs m7 _ _ |- _ => clear A end.
set (lr := fst (speex_decoder_ctl (init_dec lowmo) CtlGetSamplingRate)) in *.
assert (LRV : lr = match lowmo with ModeNB => 8000 | ModeWB => 16000 | ModeUWB => 32000 end) by (subst lr; apply init_low_rate).
assert (LRR : - 2^30 <= lr < 2^30) by (rewrite LRV; generalize lowmo; intros [| |]; split; vm_compute; first [reflexivity | (intro X; discriminate X)]).
assert (ALR : 0 < AL < 2^63) by (clear - AL0 AL1 NLP LO192 SPT; unfold USTACK_TOP in SPT; lia).
pose proof (rw_cells_join _ _ _ _ _ XA (rw_cells_join _ _ _ _ _ XP8 X7 ltac:(cbn; lia)) ltac:(cbn; lia)) as X8. cbn [app] in X8. clear XA XP8 X7.
destruct (af_acc_live RT AF Σ4 m8 S 160 ART8 INL) as (_ & ACS8).
assert (OBS8 : aobj asegs m8 S 160) by (split; [lia|]; split; [ulc| exact ACS8]).
apply (proj1 (rw_cells_app asegs m8 f [_; _; _; _] (_ :: _))) in FRB3. destruct FRB3 as [FB0 FB1].
change (Z.of_nat (cells_size _)) with 32 in FB1. chunk_uncons FB1 as TMP. replace (f + 32 + 4) with (f + 36) in FB1 by lia.
clear LPAD LPAD'. cps_hide.

cps_seg (sbinit_w5 usp S SM AL f sf lr).
{ reflexivity. } { reflexivity. }
destruct POST as (m9 & -> & MU9 & WM9 & MI9 & X9 & TMP9).
pose proof (agree_blocks_of_munch asegs _ m8 m9 LBL MU9 WM9
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)) as AG9.
eapply decst_rep_agree in RL8; [| exact AG9]. clear AG9.
clear X8 TMP OBS8 ACS8.
cps_seg_post.

assert (F8' : f mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
assert (ACT : acc asegs m9 (f + 32) 4).
{ apply (acc_ushadow asegs m9 (f + 32) 4); [clear - F8'; Z.div_mod_to_equations; lia| lia| lia|].
replace (shad (f + 32)) with (sf + 4) by (rewrite SHF; unfold shad; clear - F8'; Z.div_mod_to_equations; lia).
destruct FRS3 as [[_ BY] _]. cbn [cells_bytes cbytes app] in BY.
change [Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 4; Z_to_bv 8 (-13); Z_to_bv 8 (-13); Z_to_bv 8 (-13)]
with ([Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-15); Z_to_bv 8 (-15)] ++ [Z_to_bv 8 4] ++ [Z_to_bv 8 (-13); Z_to_bv 8 (-13); Z_to_bv 8 (-13)]) in BY.
apply bytes_at_app in BY. destruct BY as [_ BY]. apply bytes_at_app in BY. destruct BY as [BY _]. exact BY. }
assert (PRE9 : creq_pre STEREO m9 AL (init_dec lowmo) (f + 32) (CtlSetWideband 1)).
{ cbn [creq_pre]. exists (Z_to_bv 64 1). split; [exact TMP9|]. split; [reflexivity| lia]. }
assert (M4f : (f + 32) mod 4 = 0) by (clear - F8'; Z.div_mod_to_equations; lia).
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end;
[ eapply (ctl_cps_all RT AF SM0 AF_LIB (init_dec lowmo) Σ4 PMc) with (OUT := 0) (STEREO := STEREO) (LBD := LBL) (r := CtlSetWideband 1) (P := f + 32) (lo := lo) (fp := f) (kp := 0%nat); cps_auto | ].
{ cbn [creq_ok]. right. reflexivity. }
{ intros b Hb. rewrite LV4. exact (LIVEL b Hb). }
{ cbn [creq_size]. change (fs_size 0) with 64. lia. }
{ rewrite DDL, FRS4, FRS3', FRS2, FRS1. cbn [length]. fold LDEP. clear - FRM. lia. }
{ rewrite DDL in CR4 |- *. fold LDEP in CR4 |- *. fold LCRD in CR3. clear - CR4 CR3 CR2 CR1 CR0 LCR LDP. lia. }
{ rewrite unsigned_lit by ulc. eassumption. }
{ rewrite unsigned_lit by ulc. fold CSTK. pose proof (Z.le_max_r LSTK CSTK) as MX. unfold RT_STACK. clear - LOR MX. lia. }
{ rewrite unsigned_lit by ulc. ulc. }
{ rewrite unsigned_lit by ulc. clear - SPA. Z.div_mod_to_equations. lia. }
intros cc10 (Σ5 & Hc10 & LV5 & FRS5 & SP5 & CR5 & PO5).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
destruct (ASTA_unpack RT Σ5 PMc _ cc10 Hc10) as (ms10 & PO10 & Hc10'). clear Hc10. cbv beta in PO10.
destruct PO10 as (m10 & RS10 & (ART10 & MI10 & WM10 & ST10) & PRES10 & RL10 & CP10 & ACP10).
destruct RS10 as (xt0 & xt1' & xt2 & xb1 & xb2 & xb3 & xb4 & xb5 & xb6 & xb7 & xt3 & xt4 & xt5 & xt6 & F10 & fc10 & -> & FRM10).
rewrite (unsigned_lit (usp + -192)) in * by ulc.
cbn [creq_ivs creq_size app] in PRES10. replace (f + 32 + 4) with (f + 36) in PRES10 by lia.
xfp PRES10 WM10 OUTB X9. xfp PRES10 WM10 OUTB FR7. xfp PRES10 WM10 OUTB FB0. xfp PRES10 WM10 OUTB FB1. xfp PRES10 WM10 OUTB FRS3.
assert (PF10 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp [] m m10).
{ apply (pres_fp_trans _ _ _ _ m m9 m10 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ4) (rt_frames RT Σ4) (usp + -192) _ m9 m10 PRES10);
[intros e He; rewrite LV4; exact (SUBL3 e He)| intros e He; rewrite FRS4; exact (SUBF3 e He)| lia|].
intros x Hx _. cbn [outside]. split; [pose proof (NAF x Hx) as (N & _); clear - N; cbn [fst snd]; lia| exact (NAL x Hx)]. }
clear PF PRES10 RL8 TMP9 PRE9. rename PF10 into PF.
cps_sigma LV5 FRS5 SP5.
repeat match goal with A : X0ec.ART RT _ m9 |- _ => clear A | A : mem_inv asegs m9 |- _ => clear A | A : stk asegs m9 _ _ |- _ => clear A end.

destruct (af_acc_live RT AF Σ5 m10 S 160 ART10 INL) as (_ & ACS10).
assert (OBS10 : aobj asegs m10 S 160) by (split; [lia|]; split; [ulc| exact ACS10]).
assert (OBSM10 : aobj asegs m10 SM 216) by (apply (aobj_lit RT AF Σ5 m10 SM 216 ART10 SMLIT); ulc).
destruct (MODEK m10 (AF_LIB Σ5 m10 ART10)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & h1 & h2 & hlf & hfg & hm0 & hm1 & hm2 & hm3 & hm4 & hm5 & hm6 & hm7 & hpad & _ & NS10 & LPAD10).
cps_hide.
cps_seg (sbinit_w6 usp S SM NBM f sf fs sfs dsm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ zb4 zb4).
destruct POST as (m11 & za2' & za3' & -> & MU11 & WM11 & MI11 & X11).
pose proof (agree_blocks_of_munch asegs _ m10 m11 LBL MU11 WM11
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)) as AG11.
eapply decst_rep_agree in RL10; [| exact AG11]. clear AG11.
clear X9 OBS10 OBSM10 NS10 ACS10 LPAD10.
cps_seg_post.
assert (LEN5 : Z.of_nat (length (rt_live RT Σ5)) = Z.of_nat (length (rt_live RT Σ)) + 1 + LNBL).
{ rewrite LV5, LV4, LV3, length_app, LV2, LV1. cbn [length]. fold LNBL in LENL. clear - LENL. lia. }
assert (GEO' : sfs = 40 \/ sfs = 80) by (clear - GEO; unfold hid in GEO; lia).
assert (SUBF5 : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT Σ5)) by (intros e He; rewrite FRS5, FRS4; exact (SUBF3 e He)).
assert (SUBL5 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ5)) by (intros e He; rewrite LV5, LV4; exact (SUBL3 e He)).
assert (LIVEL5 : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT Σ5)) by (intros b Hb; rewrite LV5, LV4; exact (LIVEL b Hb)).
assert (CRD5 : 0 <= rt_credit RT Σ5).
{ rewrite DDL in CR4, CR5. fold LDEP in CR4, CR5. fold LCRD in CR3. clear - CR5 CR4 CR3 CR2 CR1 CR0 LCR LDP. lia. }

set (N72 := if sfs =? 40 then 160 else 320) in *.
assert (N72R : 160 <= N72 <= 320) by (subst N72; destruct GEO' as [->| ->]; cbn; lia).
assert (N72E : N72 = 4 * sfs) by (subst N72; destruct GEO' as [->| ->]; reflexivity).
assert (MC256 : mcost 256 = 0) by reflexivity. assert (MC32 : mcost 32 = 0) by reflexivity. assert (MC16 : mcost 16 = 0) by reflexivity. assert (MC64 : mcost 64 = 0) by reflexivity.
assert (MC72 : mcost N72 = 0) by (unfold mcost; replace (N72 <=? 64512) with true by (symmetry; apply Z.leb_le; lia); reflexivity).
assert (WMT5 : wmono asegs m m11) by cps_wmono. clear WM1 WM2 WM3 WM4 WM5 WM6 WM7 WM8 WM9 WM10 WM11.
assert (LVT5 : rt_live RT Σ5 = NEWL ++ (S, 160) :: rt_live RT Σ) by (rewrite LV5, LV4, LV3, LV2, LV1; reflexivity).
assert (FRT5 : rt_frames RT Σ5 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRS5, FRS4, FRS3', FRS2; exact FRS1).
assert (SPT5 : rt_sp0 RT Σ5 = rt_sp0 RT Σ) by (rewrite SP5, SP4, SP3, SP2; exact SP1).
assert (POT5 : rt_pois RT Σ5 = rt_pois RT Σ) by (rewrite PO5, PO4, PO3, PO2; exact PO1).
assert (CRT5 : rt_credit RT Σ - init_credit mo <= rt_credit RT Σ5 <= rt_credit RT Σ).
{ rewrite CRL. fold LCRD LDEP. rewrite DDL in CR4, CR5. fold LDEP in CR4, CR5. fold LCRD in CR3. clear - CR5 CR4 CR3 CR2 CR1 LCR LDP. lia. }
clear LV5 LV4 LV3 LV2 LV1 FRS5 FRS4 FRS3' FRS2 FRS1 SP5 SP4 SP3 SP2 SP1 PO5 PO4 PO3 PO2 PO1 CR5 CR4 CR3 CR2 CR1.
pose proof (zbufs_nil m11) as ZB5.
assert (LIVEB5 : blocks_in_live RT Σ5 []) by (intros b []).
assert (BOUT5 : forall b x, In b (@nil block) -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)) by (intros b x []).
clear FB1 CP10 ACP10.

assert (UWG0 : unwind_ch m11 (Z_to_bv 64 742620) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))).
{ apply (sbinit_site_ch (rt_live RT Σ) (rt_frames RT Σ) m m11 s0 ra usp lo ras 742620 UE PF (sbi_frame_rec m11 usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR7 eq_refl));
[apply TRS; unfold SBINIT_SITES; cbn [In]; tauto| ulc| clear - SPA; Z.div_mod_to_equations; lia| ulc| ulc| lia]. }
cps_rt CAL.
all: try (lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- Z.of_nat (length _) < LIVE_MAX => rewrite LEN5; clear - LVM LNB; lia
| |- mcost _ <= _ => replace (256 * 1) with 256 by lia; rewrite MC256; exact CRD5
| |- _ <= _ < _ => clear - N72R; lia
| |- _ <= _ <= _ => clear - N72R; lia
end).
intros ccG0 (ΣG0 & G0 & HccG0 & LVG0 & FRSG0 & SPG0 & CRG0 & POSG0 & AL16G0 & TOPG0 & POG0).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
replace (256 * 1) with 256 in * by lia. rewrite MC256 in CRG0. rewrite Z.sub_0_r in CRG0.
revert X11 FR7 FB0 FRS3.
cps_unpack HccG0 as (mG0 & RSG0 & (ARTG0 & MIG0 & WMG0 & STG0) & PRESG0 & WRG0 & ACG0 & BYG0).
intros X11 FR7 FB0 FRS3.
apply (rw_cells_pres_live _ _ _ m11 mG0 _ _ 160 S 160 PRESG0 WMG0) in X11; [| reflexivity| exact INL| lia| lia].
apply (rw_cells_pres_stack _ _ _ m11 mG0 _ _ 192 PRESG0 WMG0) in FR7; [| reflexivity| lia| clear - SPT; unfold USTACK_TOP; lia].
apply (rw_cells_pres_frame _ _ _ m11 mG0 _ _ 32 f 0%nat PRESG0 WMG0) in FB0; [| reflexivity| exact INF| lia| change (fs_size 0) with 64; lia].
apply (rw_cells_pres_fshadow _ _ _ m11 mG0 _ _ 8 f 0%nat PRESG0 WMG0) in FRS3; [| reflexivity| exact INF| rewrite <- SHF; lia| change (fs_size 0) with 64; rewrite SHF0; lia].
pose proof (agree_blocks_of_pres RT Σ5 (rt_frames RT Σ5) (usp + -192) m11 mG0 LBL PRESG0 WMG0 LIVEL5) as AGG0.
eapply decst_rep_agree in RL10; [| exact AGG0]. clear AGG0.
pose proof (zbufs_agree m11 mG0 [] ZB5 (agree_blocks_of_pres RT Σ5 (rt_frames RT Σ5) (usp + -192) m11 mG0 [] PRESG0 WMG0 LIVEB5)) as ZB0G0.
clear PRESG0 ZB5.
assert (SUBFG0 : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT ΣG0)) by (intros e He; rewrite FRSG0; exact (SUBF5 e He)).
assert (SUBLG0 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT ΣG0)) by (intros e He; rewrite LVG0; right; exact (SUBL5 e He)).
assert (LIVELG0 : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT ΣG0)) by (intros b Hb; rewrite LVG0; right; exact (LIVEL5 b Hb)).
assert (LIVEBG0 : blocks_in_live RT ΣG0 ((tt, G0, 256) :: [])) by (intros b [<-|Hb]; rewrite LVG0; [left; reflexivity| right; exact (LIVEB5 b Hb)]).
assert (LENG0 : Z.of_nat (length (rt_live RT ΣG0)) = Z.of_nat (length (rt_live RT Σ)) + 1 + LNBL + 1) by (rewrite LVG0; cbn [length]; rewrite Nat2Z.inj_succ, LEN5; lia).
assert (CRDG0 : 0 <= rt_credit RT ΣG0) by (rewrite CRG0; exact CRD5).
assert (ING0 : In (G0, 256) (rt_live RT ΣG0)) by (rewrite LVG0; left; reflexivity).
pose proof (new_old_apart ΣG0 mG0 [(G0, 256)] (rt_live RT Σ5) G0 256 S 160 ARTG0 LVG0 ltac:(left; reflexivity) INL) as APG0.
cps_sigma LVG0 FRSG0 SPG0.
destruct (live_below_lo RT AF ΣG0 mG0 G0 256 lo ARTG0 ING0 LOW) as (_ & LOG0 & _).
destruct (frame_live_apart RT AF ΣG0 mG0 f 0%nat G0 256 ARTG0 INF ING0) as (FA1G0 & FA2G0). change (fs_size 0) with 64 in FA1G0, FA2G0. rewrite SHF0, <- SHF in FA2G0.
assert (BOUTG0 : forall b x, In b ((tt, G0, 256) :: []) -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x [<-|Hb] Hx; [unfold blk_addr, blk_size in Hx; cbn [fst snd] in Hx; clear - Hx LOG0 APG0 FA1G0 FA2G0; lia| exact (BOUT5 b x Hb Hx)]. }
assert (BRG0 : 0 < G0 < 2^63) by (clear - POSG0 TOPG0 N72R; unfold USTACK_TOP in TOPG0; lia).
assert (LVTG0 : rt_live RT ΣG0 = blocks_live ((tt, G0, 256) :: []) ++ NEWL ++ (S, 160) :: rt_live RT Σ) by (rewrite LVG0, LVT5; reflexivity).
assert (FRTG0 : rt_frames RT ΣG0 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRSG0; exact FRT5).
assert (SPTG0 : rt_sp0 RT ΣG0 = rt_sp0 RT Σ) by (rewrite SPG0; exact SPT5).
assert (POTG0 : rt_pois RT ΣG0 = rt_pois RT Σ) by (rewrite POG0; exact POT5).
assert (CRTG0 : rt_credit RT Σ - init_credit mo <= rt_credit RT ΣG0 <= rt_credit RT Σ) by (rewrite CRG0; exact CRT5).
assert (AL8G0 : G0 mod 8 = 0) by (clear - AL16G0; Z.div_mod_to_equations; lia).
clear LVG0 FRSG0 SPG0 POG0 CRG0 LVT5 FRT5 SPT5 POT5 CRT5 POSG0 AL16G0 TOPG0 SUBF5 SUBL5 LIVEL5 LIVEB5 LEN5 CRD5 BOUT5.
pose proof (zbufs_cons mG0 G0 256 [] ltac:(clear - N72R; lia) (zero_chunk mG0 G0 256 ltac:(clear - N72R; lia) WRG0 BYG0) ZB0G0) as ZBG0.
clear WRG0 BYG0 ZB0G0 ING0 APG0 LOG0 FA1G0 FA2G0 ACG0.
repeat match goal with H : In (G0, _) (rt_live RT _) |- _ => clear H end.
destruct (af_acc_live RT AF ΣG0 mG0 S 160 ARTG0 INL) as (_ & ACSG0).
assert (OBSG0 : aobj asegs mG0 S 160) by (split; [lia|]; split; [ulc| exact ACSG0]).
cps_hide.
cps_seg (sbinit_w7 usp lo S SM G0 f sf sfs). { reflexivity. } { reflexivity. }
destruct POST as (mcG0 & wa2G0 & wa3G0 & -> & MUG0 & WM'G0 & MI'G0 & XG0 & FRG0).
repeat match goal with H : context [if sfs =? 40 then ?a else ?a] |- _ => replace (if sfs =? 40 then a else a) with a in H by (destruct (sfs =? 40); reflexivity) end.
pose proof (agree_blocks_of_munch asegs _ mG0 mcG0 LBL MUG0 WM'G0
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)) as AG'G0.
eapply decst_rep_agree in RL10; [| exact AG'G0]. clear AG'G0.
pose proof (zbufs_agree mG0 mcG0 _ ZBG0 (agree_blocks_of_munch asegs _ mG0 mcG0 _ MUG0 WM'G0
ltac:(intros b x Hb Hx; pose proof (BOUTG0 b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia))) as ZCG0.
clear X11 FR7 OBSG0 ACSG0 UWG0 ZBG0 BRG0.
revert FB0 FRS3.
cps_seg_post.
intros FB0 FRS3.
eapply rw_cells_transport in FB0; [| exact MUG0| exact WM'G0| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 32; split; [clear - FLA1; unfold hid in FLA1; lia| exact I]].
eapply rw_cells_transport in FRS3; [| exact MUG0| exact WM'G0| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 8; split; [clear - FLA2; unfold hid in FLA2; lia| exact I]].
assert (WMTG0 : wmono asegs m mcG0) by cps_wmono. clear WMG0 WM'G0 WMT5 MUG0.

assert (UWG1 : unwind_ch mcG0 (Z_to_bv 64 742656) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))).
{ apply (sbinit_site_ch (rt_live RT Σ) (rt_frames RT Σ) m mcG0 s0 ra usp lo ras 742656 UE PF (sbi_frame_rec mcG0 usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRG0 eq_refl));
[apply TRS; unfold SBINIT_SITES; cbn [In]; tauto| ulc| clear - SPA; Z.div_mod_to_equations; lia| ulc| ulc| lia]. }
cps_rt CAL.
all: try (lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- Z.of_nat (length _) < LIVE_MAX => rewrite LENG0; clear - LVM LNB; lia
| |- mcost _ <= _ => replace (256 * 1) with 256 by lia; rewrite MC256; exact CRDG0
| |- _ <= _ < _ => clear - N72R; lia
| |- _ <= _ <= _ => clear - N72R; lia
end).
intros ccG1 (ΣG1 & G1 & HccG1 & LVG1 & FRSG1 & SPG1 & CRG1 & POSG1 & AL16G1 & TOPG1 & POG1).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
replace (256 * 1) with 256 in * by lia. rewrite MC256 in CRG1. rewrite Z.sub_0_r in CRG1.
revert XG0 FRG0 FB0 FRS3.
cps_unpack HccG1 as (mG1 & RSG1 & (ARTG1 & MIG1 & WMG1 & STG1) & PRESG1 & WRG1 & ACG1 & BYG1).
intros XG0 FRG0 FB0 FRS3.
apply (rw_cells_pres_live _ _ _ mcG0 mG1 _ _ 160 S 160 PRESG1 WMG1) in XG0; [| reflexivity| exact INL| lia| lia].
apply (rw_cells_pres_stack _ _ _ mcG0 mG1 _ _ 192 PRESG1 WMG1) in FRG0; [| reflexivity| lia| clear - SPT; unfold USTACK_TOP; lia].
apply (rw_cells_pres_frame _ _ _ mcG0 mG1 _ _ 32 f 0%nat PRESG1 WMG1) in FB0; [| reflexivity| exact INF| lia| change (fs_size 0) with 64; lia].
apply (rw_cells_pres_fshadow _ _ _ mcG0 mG1 _ _ 8 f 0%nat PRESG1 WMG1) in FRS3; [| reflexivity| exact INF| rewrite <- SHF; lia| change (fs_size 0) with 64; rewrite SHF0; lia].
pose proof (agree_blocks_of_pres RT ΣG0 (rt_frames RT ΣG0) (usp + -192) mcG0 mG1 LBL PRESG1 WMG1 LIVELG0) as AGG1.
eapply decst_rep_agree in RL10; [| exact AGG1]. clear AGG1.
pose proof (zbufs_agree mcG0 mG1 ((tt, G0, 256) :: []) ZCG0 (agree_blocks_of_pres RT ΣG0 (rt_frames RT ΣG0) (usp + -192) mcG0 mG1 ((tt, G0, 256) :: []) PRESG1 WMG1 LIVEBG0)) as ZB0G1.
clear PRESG1 ZCG0.
assert (SUBFG1 : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT ΣG1)) by (intros e He; rewrite FRSG1; exact (SUBFG0 e He)).
assert (SUBLG1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT ΣG1)) by (intros e He; rewrite LVG1; right; exact (SUBLG0 e He)).
assert (LIVELG1 : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT ΣG1)) by (intros b Hb; rewrite LVG1; right; exact (LIVELG0 b Hb)).
assert (LIVEBG1 : blocks_in_live RT ΣG1 ((tt, G1, 256) :: ((tt, G0, 256) :: []))) by (intros b [<-|Hb]; rewrite LVG1; [left; reflexivity| right; exact (LIVEBG0 b Hb)]).
assert (LENG1 : Z.of_nat (length (rt_live RT ΣG1)) = Z.of_nat (length (rt_live RT Σ)) + 1 + LNBL + 2) by (rewrite LVG1; cbn [length]; rewrite Nat2Z.inj_succ, LENG0; lia).
assert (CRDG1 : 0 <= rt_credit RT ΣG1) by (rewrite CRG1; exact CRDG0).
assert (ING1 : In (G1, 256) (rt_live RT ΣG1)) by (rewrite LVG1; left; reflexivity).
pose proof (new_old_apart ΣG1 mG1 [(G1, 256)] (rt_live RT ΣG0) G1 256 S 160 ARTG1 LVG1 ltac:(left; reflexivity) INL) as APG1.
cps_sigma LVG1 FRSG1 SPG1.
destruct (live_below_lo RT AF ΣG1 mG1 G1 256 lo ARTG1 ING1 LOW) as (_ & LOG1 & _).
destruct (frame_live_apart RT AF ΣG1 mG1 f 0%nat G1 256 ARTG1 INF ING1) as (FA1G1 & FA2G1). change (fs_size 0) with 64 in FA1G1, FA2G1. rewrite SHF0, <- SHF in FA2G1.
assert (BOUTG1 : forall b x, In b ((tt, G1, 256) :: ((tt, G0, 256) :: [])) -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x [<-|Hb] Hx; [unfold blk_addr, blk_size in Hx; cbn [fst snd] in Hx; clear - Hx LOG1 APG1 FA1G1 FA2G1; lia| exact (BOUTG0 b x Hb Hx)]. }
assert (BRG1 : 0 < G1 < 2^63) by (clear - POSG1 TOPG1 N72R; unfold USTACK_TOP in TOPG1; lia).
assert (LVTG1 : rt_live RT ΣG1 = blocks_live ((tt, G1, 256) :: ((tt, G0, 256) :: [])) ++ NEWL ++ (S, 160) :: rt_live RT Σ) by (rewrite LVG1, LVTG0; reflexivity).
assert (FRTG1 : rt_frames RT ΣG1 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRSG1; exact FRTG0).
assert (SPTG1 : rt_sp0 RT ΣG1 = rt_sp0 RT Σ) by (rewrite SPG1; exact SPTG0).
assert (POTG1 : rt_pois RT ΣG1 = rt_pois RT Σ) by (rewrite POG1; exact POTG0).
assert (CRTG1 : rt_credit RT Σ - init_credit mo <= rt_credit RT ΣG1 <= rt_credit RT Σ) by (rewrite CRG1; exact CRTG0).
assert (AL8G1 : G1 mod 8 = 0) by (clear - AL16G1; Z.div_mod_to_equations; lia).
clear LVG1 FRSG1 SPG1 POG1 CRG1 LVTG0 FRTG0 SPTG0 POTG0 CRTG0 POSG1 AL16G1 TOPG1 SUBFG0 SUBLG0 LIVELG0 LIVEBG0 LENG0 CRDG0 BOUTG0.
pose proof (zbufs_cons mG1 G1 256 ((tt, G0, 256) :: []) ltac:(clear - N72R; lia) (zero_chunk mG1 G1 256 ltac:(clear - N72R; lia) WRG1 BYG1) ZB0G1) as ZBG1.
clear WRG1 BYG1 ZB0G1 ING1 APG1 LOG1 FA1G1 FA2G1 ACG1.
repeat match goal with H : In (G1, _) (rt_live RT _) |- _ => clear H end.
destruct (af_acc_live RT AF ΣG1 mG1 S 160 ARTG1 INL) as (_ & ACSG1).
assert (OBSG1 : aobj asegs mG1 S 160) by (split; [lia|]; split; [ulc| exact ACSG1]).
cps_hide.
cps_seg (sbinit_w8 usp lo S SM G1 f sf sfs). { reflexivity. } { reflexivity. }
destruct POST as (mcG1 & wa2G1 & wa3G1 & -> & MUG1 & WM'G1 & MI'G1 & XG1 & FRG1).
repeat match goal with H : context [if sfs =? 40 then 160 else 320] |- _ => change (if sfs =? 40 then 160 else 320) with N72 in H end.
repeat match goal with H : context [if sfs =? 40 then ?a else ?a] |- _ => replace (if sfs =? 40 then a else a) with a in H by (destruct (sfs =? 40); reflexivity) end.
pose proof (agree_blocks_of_munch asegs _ mG1 mcG1 LBL MUG1 WM'G1
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)) as AG'G1.
eapply decst_rep_agree in RL10; [| exact AG'G1]. clear AG'G1.
pose proof (zbufs_agree mG1 mcG1 _ ZBG1 (agree_blocks_of_munch asegs _ mG1 mcG1 _ MUG1 WM'G1
ltac:(intros b x Hb Hx; pose proof (BOUTG1 b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia))) as ZCG1.
clear XG0 FRG0 OBSG1 ACSG1 UWG1 ZBG1 BRG1.
revert FB0 FRS3.
cps_seg_post.
intros FB0 FRS3.
eapply rw_cells_transport in FB0; [| exact MUG1| exact WM'G1| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 32; split; [clear - FLA1; unfold hid in FLA1; lia| exact I]].
eapply rw_cells_transport in FRS3; [| exact MUG1| exact WM'G1| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 8; split; [clear - FLA2; unfold hid in FLA2; lia| exact I]].
assert (WMTG1 : wmono asegs m mcG1) by cps_wmono. clear WMG1 WM'G1 WMTG0 MUG1.

assert (UWEX : unwind_ch mcG1 (Z_to_bv 64 742704) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))).
{ apply (sbinit_site_ch (rt_live RT Σ) (rt_frames RT Σ) m mcG1 s0 ra usp lo ras 742704 UE PF (sbi_frame_rec mcG1 usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRG1 eq_refl));
[apply TRS; unfold SBINIT_SITES; cbn [In]; tauto| ulc| clear - SPA; Z.div_mod_to_equations; lia| ulc| ulc| lia]. }
cps_rt CAL.
all: try (lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- Z.of_nat (length _) < LIVE_MAX => rewrite LENG1; clear - LVM LNB; lia
| |- mcost _ <= _ => replace (N72 * 1) with N72 by lia; rewrite MC72; exact CRDG1
| |- _ <= _ < _ => clear - N72R; lia
| |- _ <= _ <= _ => clear - N72R; lia
end).
intros ccEX (ΣEX & EX & HccEX & LVEX & FRSEX & SPEX & CREX & POSEX & AL16EX & TOPEX & POEX).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
replace (N72 * 1) with N72 in * by lia. rewrite MC72 in CREX. rewrite Z.sub_0_r in CREX.
revert XG1 FRG1 FB0 FRS3.
cps_unpack HccEX as (mEX & RSEX & (ARTEX & MIEX & WMEX & STEX) & PRESEX & WREX & ACEX & BYEX).
intros XG1 FRG1 FB0 FRS3.
apply (rw_cells_pres_live _ _ _ mcG1 mEX _ _ 160 S 160 PRESEX WMEX) in XG1; [| reflexivity| exact INL| lia| lia].
apply (rw_cells_pres_stack _ _ _ mcG1 mEX _ _ 192 PRESEX WMEX) in FRG1; [| reflexivity| lia| clear - SPT; unfold USTACK_TOP; lia].
apply (rw_cells_pres_frame _ _ _ mcG1 mEX _ _ 32 f 0%nat PRESEX WMEX) in FB0; [| reflexivity| exact INF| lia| change (fs_size 0) with 64; lia].
apply (rw_cells_pres_fshadow _ _ _ mcG1 mEX _ _ 8 f 0%nat PRESEX WMEX) in FRS3; [| reflexivity| exact INF| rewrite <- SHF; lia| change (fs_size 0) with 64; rewrite SHF0; lia].
pose proof (agree_blocks_of_pres RT ΣG1 (rt_frames RT ΣG1) (usp + -192) mcG1 mEX LBL PRESEX WMEX LIVELG1) as AGEX.
eapply decst_rep_agree in RL10; [| exact AGEX]. clear AGEX.
pose proof (zbufs_agree mcG1 mEX ((tt, G1, 256) :: ((tt, G0, 256) :: [])) ZCG1 (agree_blocks_of_pres RT ΣG1 (rt_frames RT ΣG1) (usp + -192) mcG1 mEX ((tt, G1, 256) :: ((tt, G0, 256) :: [])) PRESEX WMEX LIVEBG1)) as ZB0EX.
clear PRESEX ZCG1.
assert (SUBFEX : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT ΣEX)) by (intros e He; rewrite FRSEX; exact (SUBFG1 e He)).
assert (SUBLEX : forall e, In e (rt_live RT Σ) -> In e (rt_live RT ΣEX)) by (intros e He; rewrite LVEX; right; exact (SUBLG1 e He)).
assert (LIVELEX : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT ΣEX)) by (intros b Hb; rewrite LVEX; right; exact (LIVELG1 b Hb)).
assert (LIVEBEX : blocks_in_live RT ΣEX ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))) by (intros b [<-|Hb]; rewrite LVEX; [left; reflexivity| right; exact (LIVEBG1 b Hb)]).
assert (LENEX : Z.of_nat (length (rt_live RT ΣEX)) = Z.of_nat (length (rt_live RT Σ)) + 1 + LNBL + 3) by (rewrite LVEX; cbn [length]; rewrite Nat2Z.inj_succ, LENG1; lia).
assert (CRDEX : 0 <= rt_credit RT ΣEX) by (rewrite CREX; exact CRDG1).
assert (INEX : In (EX, N72) (rt_live RT ΣEX)) by (rewrite LVEX; left; reflexivity).
pose proof (new_old_apart ΣEX mEX [(EX, N72)] (rt_live RT ΣG1) EX N72 S 160 ARTEX LVEX ltac:(left; reflexivity) INL) as APEX.
cps_sigma LVEX FRSEX SPEX.
destruct (live_below_lo RT AF ΣEX mEX EX N72 lo ARTEX INEX LOW) as (_ & LOEX & _).
destruct (frame_live_apart RT AF ΣEX mEX f 0%nat EX N72 ARTEX INF INEX) as (FA1EX & FA2EX). change (fs_size 0) with 64 in FA1EX, FA2EX. rewrite SHF0, <- SHF in FA2EX.
assert (BOUTEX : forall b x, In b ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))) -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x [<-|Hb] Hx; [unfold blk_addr, blk_size in Hx; cbn [fst snd] in Hx; clear - Hx LOEX APEX FA1EX FA2EX; lia| exact (BOUTG1 b x Hb Hx)]. }
assert (BREX : 0 < EX < 2^63) by (clear - POSEX TOPEX N72R; unfold USTACK_TOP in TOPEX; lia).
assert (LVTEX : rt_live RT ΣEX = blocks_live ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))) ++ NEWL ++ (S, 160) :: rt_live RT Σ) by (rewrite LVEX, LVTG1; reflexivity).
assert (FRTEX : rt_frames RT ΣEX = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRSEX; exact FRTG1).
assert (SPTEX : rt_sp0 RT ΣEX = rt_sp0 RT Σ) by (rewrite SPEX; exact SPTG1).
assert (POTEX : rt_pois RT ΣEX = rt_pois RT Σ) by (rewrite POEX; exact POTG1).
assert (CRTEX : rt_credit RT Σ - init_credit mo <= rt_credit RT ΣEX <= rt_credit RT Σ) by (rewrite CREX; exact CRTG1).
assert (AL8EX : EX mod 8 = 0) by (clear - AL16EX; Z.div_mod_to_equations; lia).
clear LVEX FRSEX SPEX POEX CREX LVTG1 FRTG1 SPTG1 POTG1 CRTG1 POSEX AL16EX TOPEX SUBFG1 SUBLG1 LIVELG1 LIVEBG1 LENG1 CRDG1 BOUTG1.
pose proof (zbufs_cons mEX EX N72 ((tt, G1, 256) :: ((tt, G0, 256) :: [])) ltac:(clear - N72R; lia) (zero_chunk mEX EX N72 ltac:(clear - N72R; lia) WREX BYEX) ZB0EX) as ZBEX.
clear WREX BYEX ZB0EX INEX APEX LOEX FA1EX FA2EX ACEX.
repeat match goal with H : In (EX, _) (rt_live RT _) |- _ => clear H end.
destruct (af_acc_live RT AF ΣEX mEX S 160 ARTEX INL) as (_ & ACSEX).
assert (OBSEX : aobj asegs mEX S 160) by (split; [lia|]; split; [ulc| exact ACSEX]).
cps_hide.
cps_seg (sbinit_w9 usp lo S SM EX f sf sfs). { reflexivity. } { reflexivity. }
destruct POST as (mcEX & wa2EX & wa3EX & -> & MUEX & WM'EX & MI'EX & XEX & FREX).
repeat match goal with H : context [if sfs =? 40 then ?a else ?a] |- _ => replace (if sfs =? 40 then a else a) with a in H by (destruct (sfs =? 40); reflexivity) end.
pose proof (agree_blocks_of_munch asegs _ mEX mcEX LBL MUEX WM'EX
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)) as AG'EX.
eapply decst_rep_agree in RL10; [| exact AG'EX]. clear AG'EX.
pose proof (zbufs_agree mEX mcEX _ ZBEX (agree_blocks_of_munch asegs _ mEX mcEX _ MUEX WM'EX
ltac:(intros b x Hb Hx; pose proof (BOUTEX b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia))) as ZCEX.
clear XG1 FRG1 OBSEX ACSEX UWEX ZBEX BREX.
revert FB0 FRS3.
cps_seg_post.
intros FB0 FRS3.
eapply rw_cells_transport in FB0; [| exact MUEX| exact WM'EX| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 32; split; [clear - FLA1; unfold hid in FLA1; lia| exact I]].
eapply rw_cells_transport in FRS3; [| exact MUEX| exact WM'EX| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 8; split; [clear - FLA2; unfold hid in FLA2; lia| exact I]].
assert (WMTEX : wmono asegs m mcEX) by cps_wmono. clear WMEX WM'EX WMTG1 MUEX.

assert (UWOQ : unwind_ch mcEX (Z_to_bv 64 742756) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))).
{ apply (sbinit_site_ch (rt_live RT Σ) (rt_frames RT Σ) m mcEX s0 ra usp lo ras 742756 UE PF (sbi_frame_rec mcEX usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FREX eq_refl));
[apply TRS; unfold SBINIT_SITES; cbn [In]; tauto| ulc| clear - SPA; Z.div_mod_to_equations; lia| ulc| ulc| lia]. }
cps_rt CAL.
all: try (lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- Z.of_nat (length _) < LIVE_MAX => rewrite LENEX; clear - LVM LNB; lia
| |- mcost _ <= _ => replace (32 * 1) with 32 by lia; rewrite MC32; exact CRDEX
| |- _ <= _ < _ => clear - N72R; lia
| |- _ <= _ <= _ => clear - N72R; lia
end).
intros ccOQ (ΣOQ & OQ & HccOQ & LVOQ & FRSOQ & SPOQ & CROQ & POSOQ & AL16OQ & TOPOQ & POOQ).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
replace (32 * 1) with 32 in * by lia. rewrite MC32 in CROQ. rewrite Z.sub_0_r in CROQ.
revert XEX FREX FB0 FRS3.
cps_unpack HccOQ as (mOQ & RSOQ & (ARTOQ & MIOQ & WMOQ & STOQ) & PRESOQ & WROQ & ACOQ & BYOQ).
intros XEX FREX FB0 FRS3.
apply (rw_cells_pres_live _ _ _ mcEX mOQ _ _ 160 S 160 PRESOQ WMOQ) in XEX; [| reflexivity| exact INL| lia| lia].
apply (rw_cells_pres_stack _ _ _ mcEX mOQ _ _ 192 PRESOQ WMOQ) in FREX; [| reflexivity| lia| clear - SPT; unfold USTACK_TOP; lia].
apply (rw_cells_pres_frame _ _ _ mcEX mOQ _ _ 32 f 0%nat PRESOQ WMOQ) in FB0; [| reflexivity| exact INF| lia| change (fs_size 0) with 64; lia].
apply (rw_cells_pres_fshadow _ _ _ mcEX mOQ _ _ 8 f 0%nat PRESOQ WMOQ) in FRS3; [| reflexivity| exact INF| rewrite <- SHF; lia| change (fs_size 0) with 64; rewrite SHF0; lia].
pose proof (agree_blocks_of_pres RT ΣEX (rt_frames RT ΣEX) (usp + -192) mcEX mOQ LBL PRESOQ WMOQ LIVELEX) as AGOQ.
eapply decst_rep_agree in RL10; [| exact AGOQ]. clear AGOQ.
pose proof (zbufs_agree mcEX mOQ ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))) ZCEX (agree_blocks_of_pres RT ΣEX (rt_frames RT ΣEX) (usp + -192) mcEX mOQ ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))) PRESOQ WMOQ LIVEBEX)) as ZB0OQ.
clear PRESOQ ZCEX.
assert (SUBFOQ : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT ΣOQ)) by (intros e He; rewrite FRSOQ; exact (SUBFEX e He)).
assert (SUBLOQ : forall e, In e (rt_live RT Σ) -> In e (rt_live RT ΣOQ)) by (intros e He; rewrite LVOQ; right; exact (SUBLEX e He)).
assert (LIVELOQ : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT ΣOQ)) by (intros b Hb; rewrite LVOQ; right; exact (LIVELEX b Hb)).
assert (LIVEBOQ : blocks_in_live RT ΣOQ ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))) by (intros b [<-|Hb]; rewrite LVOQ; [left; reflexivity| right; exact (LIVEBEX b Hb)]).
assert (LENOQ : Z.of_nat (length (rt_live RT ΣOQ)) = Z.of_nat (length (rt_live RT Σ)) + 1 + LNBL + 4) by (rewrite LVOQ; cbn [length]; rewrite Nat2Z.inj_succ, LENEX; lia).
assert (CRDOQ : 0 <= rt_credit RT ΣOQ) by (rewrite CROQ; exact CRDEX).
assert (INOQ : In (OQ, 32) (rt_live RT ΣOQ)) by (rewrite LVOQ; left; reflexivity).
pose proof (new_old_apart ΣOQ mOQ [(OQ, 32)] (rt_live RT ΣEX) OQ 32 S 160 ARTOQ LVOQ ltac:(left; reflexivity) INL) as APOQ.
cps_sigma LVOQ FRSOQ SPOQ.
destruct (live_below_lo RT AF ΣOQ mOQ OQ 32 lo ARTOQ INOQ LOW) as (_ & LOOQ & _).
destruct (frame_live_apart RT AF ΣOQ mOQ f 0%nat OQ 32 ARTOQ INF INOQ) as (FA1OQ & FA2OQ). change (fs_size 0) with 64 in FA1OQ, FA2OQ. rewrite SHF0, <- SHF in FA2OQ.
assert (BOUTOQ : forall b x, In b ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))) -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x [<-|Hb] Hx; [unfold blk_addr, blk_size in Hx; cbn [fst snd] in Hx; clear - Hx LOOQ APOQ FA1OQ FA2OQ; lia| exact (BOUTEX b x Hb Hx)]. }
assert (BROQ : 0 < OQ < 2^63) by (clear - POSOQ TOPOQ N72R; unfold USTACK_TOP in TOPOQ; lia).
assert (LVTOQ : rt_live RT ΣOQ = blocks_live ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))) ++ NEWL ++ (S, 160) :: rt_live RT Σ) by (rewrite LVOQ, LVTEX; reflexivity).
assert (FRTOQ : rt_frames RT ΣOQ = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRSOQ; exact FRTEX).
assert (SPTOQ : rt_sp0 RT ΣOQ = rt_sp0 RT Σ) by (rewrite SPOQ; exact SPTEX).
assert (POTOQ : rt_pois RT ΣOQ = rt_pois RT Σ) by (rewrite POOQ; exact POTEX).
assert (CRTOQ : rt_credit RT Σ - init_credit mo <= rt_credit RT ΣOQ <= rt_credit RT Σ) by (rewrite CROQ; exact CRTEX).
assert (AL8OQ : OQ mod 8 = 0) by (clear - AL16OQ; Z.div_mod_to_equations; lia).
clear LVOQ FRSOQ SPOQ POOQ CROQ LVTEX FRTEX SPTEX POTEX CRTEX POSOQ AL16OQ TOPOQ SUBFEX SUBLEX LIVELEX LIVEBEX LENEX CRDEX BOUTEX.
pose proof (zbufs_cons mOQ OQ 32 ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))) ltac:(clear - N72R; lia) (zero_chunk mOQ OQ 32 ltac:(clear - N72R; lia) WROQ BYOQ) ZB0OQ) as ZBOQ.
clear WROQ BYOQ ZB0OQ INOQ APOQ LOOQ FA1OQ FA2OQ ACOQ.
repeat match goal with H : In (OQ, _) (rt_live RT _) |- _ => clear H end.
destruct (af_acc_live RT AF ΣOQ mOQ S 160 ARTOQ INL) as (_ & ACSOQ).
assert (OBSOQ : aobj asegs mOQ S 160) by (split; [lia|]; split; [ulc| exact ACSOQ]).
cps_hide.
cps_seg (sbinit_w10 usp lo S SM OQ f sf sfs). { reflexivity. } { reflexivity. }
destruct POST as (mcOQ & wa2OQ & wa3OQ & -> & MUOQ & WM'OQ & MI'OQ & XOQ & FROQ).
repeat match goal with H : context [if sfs =? 40 then ?a else ?a] |- _ => replace (if sfs =? 40 then a else a) with a in H by (destruct (sfs =? 40); reflexivity) end.
pose proof (agree_blocks_of_munch asegs _ mOQ mcOQ LBL MUOQ WM'OQ
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)) as AG'OQ.
eapply decst_rep_agree in RL10; [| exact AG'OQ]. clear AG'OQ.
pose proof (zbufs_agree mOQ mcOQ _ ZBOQ (agree_blocks_of_munch asegs _ mOQ mcOQ _ MUOQ WM'OQ
ltac:(intros b x Hb Hx; pose proof (BOUTOQ b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia))) as ZCOQ.
clear XEX FREX OBSOQ ACSOQ UWOQ ZBOQ BROQ.
revert FB0 FRS3.
cps_seg_post.
intros FB0 FRS3.
eapply rw_cells_transport in FB0; [| exact MUOQ| exact WM'OQ| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 32; split; [clear - FLA1; unfold hid in FLA1; lia| exact I]].
eapply rw_cells_transport in FRS3; [| exact MUOQ| exact WM'OQ| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 8; split; [clear - FLA2; unfold hid in FLA2; lia| exact I]].
assert (WMTOQ : wmono asegs m mcOQ) by cps_wmono. clear WMOQ WM'OQ WMTEX MUOQ.

assert (UWIQ : unwind_ch mcOQ (Z_to_bv 64 742804) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))).
{ apply (sbinit_site_ch (rt_live RT Σ) (rt_frames RT Σ) m mcOQ s0 ra usp lo ras 742804 UE PF (sbi_frame_rec mcOQ usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FROQ eq_refl));
[apply TRS; unfold SBINIT_SITES; cbn [In]; tauto| ulc| clear - SPA; Z.div_mod_to_equations; lia| ulc| ulc| lia]. }
cps_rt CAL.
all: try (lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- Z.of_nat (length _) < LIVE_MAX => rewrite LENOQ; clear - LVM LNB; lia
| |- mcost _ <= _ => replace (32 * 1) with 32 by lia; rewrite MC32; exact CRDOQ
| |- _ <= _ < _ => clear - N72R; lia
| |- _ <= _ <= _ => clear - N72R; lia
end).
intros ccIQ (ΣIQ & IQ & HccIQ & LVIQ & FRSIQ & SPIQ & CRIQ & POSIQ & AL16IQ & TOPIQ & POIQ).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
replace (32 * 1) with 32 in * by lia. rewrite MC32 in CRIQ. rewrite Z.sub_0_r in CRIQ.
revert XOQ FROQ FB0 FRS3.
cps_unpack HccIQ as (mIQ & RSIQ & (ARTIQ & MIIQ & WMIQ & STIQ) & PRESIQ & WRIQ & ACIQ & BYIQ).
intros XOQ FROQ FB0 FRS3.
apply (rw_cells_pres_live _ _ _ mcOQ mIQ _ _ 160 S 160 PRESIQ WMIQ) in XOQ; [| reflexivity| exact INL| lia| lia].
apply (rw_cells_pres_stack _ _ _ mcOQ mIQ _ _ 192 PRESIQ WMIQ) in FROQ; [| reflexivity| lia| clear - SPT; unfold USTACK_TOP; lia].
apply (rw_cells_pres_frame _ _ _ mcOQ mIQ _ _ 32 f 0%nat PRESIQ WMIQ) in FB0; [| reflexivity| exact INF| lia| change (fs_size 0) with 64; lia].
apply (rw_cells_pres_fshadow _ _ _ mcOQ mIQ _ _ 8 f 0%nat PRESIQ WMIQ) in FRS3; [| reflexivity| exact INF| rewrite <- SHF; lia| change (fs_size 0) with 64; rewrite SHF0; lia].
pose proof (agree_blocks_of_pres RT ΣOQ (rt_frames RT ΣOQ) (usp + -192) mcOQ mIQ LBL PRESIQ WMIQ LIVELOQ) as AGIQ.
eapply decst_rep_agree in RL10; [| exact AGIQ]. clear AGIQ.
pose proof (zbufs_agree mcOQ mIQ ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))) ZCOQ (agree_blocks_of_pres RT ΣOQ (rt_frames RT ΣOQ) (usp + -192) mcOQ mIQ ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))) PRESIQ WMIQ LIVEBOQ)) as ZB0IQ.
clear PRESIQ ZCOQ.
assert (SUBFIQ : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT ΣIQ)) by (intros e He; rewrite FRSIQ; exact (SUBFOQ e He)).
assert (SUBLIQ : forall e, In e (rt_live RT Σ) -> In e (rt_live RT ΣIQ)) by (intros e He; rewrite LVIQ; right; exact (SUBLOQ e He)).
assert (LIVELIQ : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT ΣIQ)) by (intros b Hb; rewrite LVIQ; right; exact (LIVELOQ b Hb)).
assert (LIVEBIQ : blocks_in_live RT ΣIQ ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))))) by (intros b [<-|Hb]; rewrite LVIQ; [left; reflexivity| right; exact (LIVEBOQ b Hb)]).
assert (LENIQ : Z.of_nat (length (rt_live RT ΣIQ)) = Z.of_nat (length (rt_live RT Σ)) + 1 + LNBL + 5) by (rewrite LVIQ; cbn [length]; rewrite Nat2Z.inj_succ, LENOQ; lia).
assert (CRDIQ : 0 <= rt_credit RT ΣIQ) by (rewrite CRIQ; exact CRDOQ).
assert (INIQ : In (IQ, 32) (rt_live RT ΣIQ)) by (rewrite LVIQ; left; reflexivity).
pose proof (new_old_apart ΣIQ mIQ [(IQ, 32)] (rt_live RT ΣOQ) IQ 32 S 160 ARTIQ LVIQ ltac:(left; reflexivity) INL) as APIQ.
cps_sigma LVIQ FRSIQ SPIQ.
destruct (live_below_lo RT AF ΣIQ mIQ IQ 32 lo ARTIQ INIQ LOW) as (_ & LOIQ & _).
destruct (frame_live_apart RT AF ΣIQ mIQ f 0%nat IQ 32 ARTIQ INF INIQ) as (FA1IQ & FA2IQ). change (fs_size 0) with 64 in FA1IQ, FA2IQ. rewrite SHF0, <- SHF in FA2IQ.
assert (BOUTIQ : forall b x, In b ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))) -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x [<-|Hb] Hx; [unfold blk_addr, blk_size in Hx; cbn [fst snd] in Hx; clear - Hx LOIQ APIQ FA1IQ FA2IQ; lia| exact (BOUTOQ b x Hb Hx)]. }
assert (BRIQ : 0 < IQ < 2^63) by (clear - POSIQ TOPIQ N72R; unfold USTACK_TOP in TOPIQ; lia).
assert (LVTIQ : rt_live RT ΣIQ = blocks_live ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))) ++ NEWL ++ (S, 160) :: rt_live RT Σ) by (rewrite LVIQ, LVTOQ; reflexivity).
assert (FRTIQ : rt_frames RT ΣIQ = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRSIQ; exact FRTOQ).
assert (SPTIQ : rt_sp0 RT ΣIQ = rt_sp0 RT Σ) by (rewrite SPIQ; exact SPTOQ).
assert (POTIQ : rt_pois RT ΣIQ = rt_pois RT Σ) by (rewrite POIQ; exact POTOQ).
assert (CRTIQ : rt_credit RT Σ - init_credit mo <= rt_credit RT ΣIQ <= rt_credit RT Σ) by (rewrite CRIQ; exact CRTOQ).
assert (AL8IQ : IQ mod 8 = 0) by (clear - AL16IQ; Z.div_mod_to_equations; lia).
clear LVIQ FRSIQ SPIQ POIQ CRIQ LVTOQ FRTOQ SPTOQ POTOQ CRTOQ POSIQ AL16IQ TOPIQ SUBFOQ SUBLOQ LIVELOQ LIVEBOQ LENOQ CRDOQ BOUTOQ.
pose proof (zbufs_cons mIQ IQ 32 ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))) ltac:(clear - N72R; lia) (zero_chunk mIQ IQ 32 ltac:(clear - N72R; lia) WRIQ BYIQ) ZB0IQ) as ZBIQ.
clear WRIQ BYIQ ZB0IQ INIQ APIQ LOIQ FA1IQ FA2IQ ACIQ.
repeat match goal with H : In (IQ, _) (rt_live RT _) |- _ => clear H end.
destruct (af_acc_live RT AF ΣIQ mIQ S 160 ARTIQ INL) as (_ & ACSIQ).
assert (OBSIQ : aobj asegs mIQ S 160) by (split; [lia|]; split; [ulc| exact ACSIQ]).
cps_hide.
cps_seg (sbinit_w11 usp lo S SM IQ f sf sfs). { reflexivity. } { reflexivity. }
destruct POST as (mcIQ & wa2IQ & wa3IQ & -> & MUIQ & WM'IQ & MI'IQ & XIQ & FRIQ).
repeat match goal with H : context [if sfs =? 40 then ?a else ?a] |- _ => replace (if sfs =? 40 then a else a) with a in H by (destruct (sfs =? 40); reflexivity) end.
pose proof (agree_blocks_of_munch asegs _ mIQ mcIQ LBL MUIQ WM'IQ
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)) as AG'IQ.
eapply decst_rep_agree in RL10; [| exact AG'IQ]. clear AG'IQ.
pose proof (zbufs_agree mIQ mcIQ _ ZBIQ (agree_blocks_of_munch asegs _ mIQ mcIQ _ MUIQ WM'IQ
ltac:(intros b x Hb Hx; pose proof (BOUTIQ b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia))) as ZCIQ.
clear XOQ FROQ OBSIQ ACSIQ UWIQ ZBIQ BRIQ.
revert FB0 FRS3.
cps_seg_post.
intros FB0 FRS3.
eapply rw_cells_transport in FB0; [| exact MUIQ| exact WM'IQ| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 32; split; [clear - FLA1; unfold hid in FLA1; lia| exact I]].
eapply rw_cells_transport in FRS3; [| exact MUIQ| exact WM'IQ| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 8; split; [clear - FLA2; unfold hid in FLA2; lia| exact I]].
assert (WMTIQ : wmono asegs m mcIQ) by cps_wmono. clear WMIQ WM'IQ WMTOQ MUIQ.

assert (UWPG : unwind_ch mcIQ (Z_to_bv 64 742852) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))).
{ apply (sbinit_site_ch (rt_live RT Σ) (rt_frames RT Σ) m mcIQ s0 ra usp lo ras 742852 UE PF (sbi_frame_rec mcIQ usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRIQ eq_refl));
[apply TRS; unfold SBINIT_SITES; cbn [In]; tauto| ulc| clear - SPA; Z.div_mod_to_equations; lia| ulc| ulc| lia]. }
cps_rt CAL.
all: try (lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- Z.of_nat (length _) < LIVE_MAX => rewrite LENIQ; clear - LVM LNB; lia
| |- mcost _ <= _ => replace (16 * 1) with 16 by lia; rewrite MC16; exact CRDIQ
| |- _ <= _ < _ => clear - N72R; lia
| |- _ <= _ <= _ => clear - N72R; lia
end).
intros ccPG (ΣPG & PG & HccPG & LVPG & FRSPG & SPPG & CRPG & POSPG & AL16PG & TOPPG & POPG).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
replace (16 * 1) with 16 in * by lia. rewrite MC16 in CRPG. rewrite Z.sub_0_r in CRPG.
revert XIQ FRIQ FB0 FRS3.
cps_unpack HccPG as (mPG & RSPG & (ARTPG & MIPG & WMPG & STPG) & PRESPG & WRPG & ACPG & BYPG).
intros XIQ FRIQ FB0 FRS3.
apply (rw_cells_pres_live _ _ _ mcIQ mPG _ _ 160 S 160 PRESPG WMPG) in XIQ; [| reflexivity| exact INL| lia| lia].
apply (rw_cells_pres_stack _ _ _ mcIQ mPG _ _ 192 PRESPG WMPG) in FRIQ; [| reflexivity| lia| clear - SPT; unfold USTACK_TOP; lia].
apply (rw_cells_pres_frame _ _ _ mcIQ mPG _ _ 32 f 0%nat PRESPG WMPG) in FB0; [| reflexivity| exact INF| lia| change (fs_size 0) with 64; lia].
apply (rw_cells_pres_fshadow _ _ _ mcIQ mPG _ _ 8 f 0%nat PRESPG WMPG) in FRS3; [| reflexivity| exact INF| rewrite <- SHF; lia| change (fs_size 0) with 64; rewrite SHF0; lia].
pose proof (agree_blocks_of_pres RT ΣIQ (rt_frames RT ΣIQ) (usp + -192) mcIQ mPG LBL PRESPG WMPG LIVELIQ) as AGPG.
eapply decst_rep_agree in RL10; [| exact AGPG]. clear AGPG.
pose proof (zbufs_agree mcIQ mPG ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))) ZCIQ (agree_blocks_of_pres RT ΣIQ (rt_frames RT ΣIQ) (usp + -192) mcIQ mPG ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))) PRESPG WMPG LIVEBIQ)) as ZB0PG.
clear PRESPG ZCIQ.
assert (SUBFPG : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT ΣPG)) by (intros e He; rewrite FRSPG; exact (SUBFIQ e He)).
assert (SUBLPG : forall e, In e (rt_live RT Σ) -> In e (rt_live RT ΣPG)) by (intros e He; rewrite LVPG; right; exact (SUBLIQ e He)).
assert (LIVELPG : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT ΣPG)) by (intros b Hb; rewrite LVPG; right; exact (LIVELIQ b Hb)).
assert (LIVEBPG : blocks_in_live RT ΣPG ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))))) by (intros b [<-|Hb]; rewrite LVPG; [left; reflexivity| right; exact (LIVEBIQ b Hb)]).
assert (LENPG : Z.of_nat (length (rt_live RT ΣPG)) = Z.of_nat (length (rt_live RT Σ)) + 1 + LNBL + 6) by (rewrite LVPG; cbn [length]; rewrite Nat2Z.inj_succ, LENIQ; lia).
assert (CRDPG : 0 <= rt_credit RT ΣPG) by (rewrite CRPG; exact CRDIQ).
assert (INPG : In (PG, 16) (rt_live RT ΣPG)) by (rewrite LVPG; left; reflexivity).
pose proof (new_old_apart ΣPG mPG [(PG, 16)] (rt_live RT ΣIQ) PG 16 S 160 ARTPG LVPG ltac:(left; reflexivity) INL) as APPG.
cps_sigma LVPG FRSPG SPPG.
destruct (live_below_lo RT AF ΣPG mPG PG 16 lo ARTPG INPG LOW) as (_ & LOPG & _).
destruct (frame_live_apart RT AF ΣPG mPG f 0%nat PG 16 ARTPG INF INPG) as (FA1PG & FA2PG). change (fs_size 0) with 64 in FA1PG, FA2PG. rewrite SHF0, <- SHF in FA2PG.
assert (BOUTPG : forall b x, In b ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))))) -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x [<-|Hb] Hx; [unfold blk_addr, blk_size in Hx; cbn [fst snd] in Hx; clear - Hx LOPG APPG FA1PG FA2PG; lia| exact (BOUTIQ b x Hb Hx)]. }
assert (BRPG : 0 < PG < 2^63) by (clear - POSPG TOPPG N72R; unfold USTACK_TOP in TOPPG; lia).
assert (LVTPG : rt_live RT ΣPG = blocks_live ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))))) ++ NEWL ++ (S, 160) :: rt_live RT Σ) by (rewrite LVPG, LVTIQ; reflexivity).
assert (FRTPG : rt_frames RT ΣPG = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRSPG; exact FRTIQ).
assert (SPTPG : rt_sp0 RT ΣPG = rt_sp0 RT Σ) by (rewrite SPPG; exact SPTIQ).
assert (POTPG : rt_pois RT ΣPG = rt_pois RT Σ) by (rewrite POPG; exact POTIQ).
assert (CRTPG : rt_credit RT Σ - init_credit mo <= rt_credit RT ΣPG <= rt_credit RT Σ) by (rewrite CRPG; exact CRTIQ).
assert (AL8PG : PG mod 8 = 0) by (clear - AL16PG; Z.div_mod_to_equations; lia).
clear LVPG FRSPG SPPG POPG CRPG LVTIQ FRTIQ SPTIQ POTIQ CRTIQ POSPG AL16PG TOPPG SUBFIQ SUBLIQ LIVELIQ LIVEBIQ LENIQ CRDIQ BOUTIQ.
pose proof (zbufs_cons mPG PG 16 ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))) ltac:(clear - N72R; lia) (zero_chunk mPG PG 16 ltac:(clear - N72R; lia) WRPG BYPG) ZB0PG) as ZBPG.
clear WRPG BYPG ZB0PG INPG APPG LOPG FA1PG FA2PG ACPG.
repeat match goal with H : In (PG, _) (rt_live RT _) |- _ => clear H end.
destruct (af_acc_live RT AF ΣPG mPG S 160 ARTPG INL) as (_ & ACSPG).
assert (OBSPG : aobj asegs mPG S 160) by (split; [lia|]; split; [ulc| exact ACSPG]).
cps_hide.
cps_seg (sbinit_w12 usp lo S SM PG f sf sfs). { reflexivity. } { reflexivity. }
destruct POST as (mcPG & wa2PG & wa3PG & -> & MUPG & WM'PG & MI'PG & XPG & FRPG).
repeat match goal with H : context [if sfs =? 40 then ?a else ?a] |- _ => replace (if sfs =? 40 then a else a) with a in H by (destruct (sfs =? 40); reflexivity) end.
pose proof (agree_blocks_of_munch asegs _ mPG mcPG LBL MUPG WM'PG
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)) as AG'PG.
eapply decst_rep_agree in RL10; [| exact AG'PG]. clear AG'PG.
pose proof (zbufs_agree mPG mcPG _ ZBPG (agree_blocks_of_munch asegs _ mPG mcPG _ MUPG WM'PG
ltac:(intros b x Hb Hx; pose proof (BOUTPG b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia))) as ZCPG.
clear XIQ FRIQ OBSPG ACSPG UWPG ZBPG BRPG.
revert FB0 FRS3.
cps_seg_post.
intros FB0 FRS3.
eapply rw_cells_transport in FB0; [| exact MUPG| exact WM'PG| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 32; split; [clear - FLA1; unfold hid in FLA1; lia| exact I]].
eapply rw_cells_transport in FRS3; [| exact MUPG| exact WM'PG| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 8; split; [clear - FLA2; unfold hid in FLA2; lia| exact I]].
assert (WMTPG : wmono asegs m mcPG) by cps_wmono. clear WMPG WM'PG WMTIQ MUPG.

assert (UWER : unwind_ch mcPG (Z_to_bv 64 742900) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))).
{ apply (sbinit_site_ch (rt_live RT Σ) (rt_frames RT Σ) m mcPG s0 ra usp lo ras 742900 UE PF (sbi_frame_rec mcPG usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRPG eq_refl));
[apply TRS; unfold SBINIT_SITES; cbn [In]; tauto| ulc| clear - SPA; Z.div_mod_to_equations; lia| ulc| ulc| lia]. }
cps_rt CAL.
all: try (lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- Z.of_nat (length _) < LIVE_MAX => rewrite LENPG; clear - LVM LNB; lia
| |- mcost _ <= _ => replace (16 * 1) with 16 by lia; rewrite MC16; exact CRDPG
| |- _ <= _ < _ => clear - N72R; lia
| |- _ <= _ <= _ => clear - N72R; lia
end).
intros ccER (ΣER & ER & HccER & LVER & FRSER & SPER & CRER & POSER & AL16ER & TOPER & POER).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
replace (16 * 1) with 16 in * by lia. rewrite MC16 in CRER. rewrite Z.sub_0_r in CRER.
revert XPG FRPG FB0 FRS3.
cps_unpack HccER as (mER & RSER & (ARTER & MIER & WMER & STER) & PRESER & WRER & ACER & BYER).
intros XPG FRPG FB0 FRS3.
apply (rw_cells_pres_live _ _ _ mcPG mER _ _ 160 S 160 PRESER WMER) in XPG; [| reflexivity| exact INL| lia| lia].
apply (rw_cells_pres_stack _ _ _ mcPG mER _ _ 192 PRESER WMER) in FRPG; [| reflexivity| lia| clear - SPT; unfold USTACK_TOP; lia].
apply (rw_cells_pres_frame _ _ _ mcPG mER _ _ 32 f 0%nat PRESER WMER) in FB0; [| reflexivity| exact INF| lia| change (fs_size 0) with 64; lia].
apply (rw_cells_pres_fshadow _ _ _ mcPG mER _ _ 8 f 0%nat PRESER WMER) in FRS3; [| reflexivity| exact INF| rewrite <- SHF; lia| change (fs_size 0) with 64; rewrite SHF0; lia].
pose proof (agree_blocks_of_pres RT ΣPG (rt_frames RT ΣPG) (usp + -192) mcPG mER LBL PRESER WMER LIVELPG) as AGER.
eapply decst_rep_agree in RL10; [| exact AGER]. clear AGER.
pose proof (zbufs_agree mcPG mER ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))))) ZCPG (agree_blocks_of_pres RT ΣPG (rt_frames RT ΣPG) (usp + -192) mcPG mER ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))))) PRESER WMER LIVEBPG)) as ZB0ER.
clear PRESER ZCPG.
assert (SUBFER : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT ΣER)) by (intros e He; rewrite FRSER; exact (SUBFPG e He)).
assert (SUBLER : forall e, In e (rt_live RT Σ) -> In e (rt_live RT ΣER)) by (intros e He; rewrite LVER; right; exact (SUBLPG e He)).
assert (LIVELER : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT ΣER)) by (intros b Hb; rewrite LVER; right; exact (LIVELPG b Hb)).
assert (LIVEBER : blocks_in_live RT ΣER ((tt, ER, 16) :: ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))))))) by (intros b [<-|Hb]; rewrite LVER; [left; reflexivity| right; exact (LIVEBPG b Hb)]).
assert (LENER : Z.of_nat (length (rt_live RT ΣER)) = Z.of_nat (length (rt_live RT Σ)) + 1 + LNBL + 7) by (rewrite LVER; cbn [length]; rewrite Nat2Z.inj_succ, LENPG; lia).
assert (CRDER : 0 <= rt_credit RT ΣER) by (rewrite CRER; exact CRDPG).
assert (INER : In (ER, 16) (rt_live RT ΣER)) by (rewrite LVER; left; reflexivity).
pose proof (new_old_apart ΣER mER [(ER, 16)] (rt_live RT ΣPG) ER 16 S 160 ARTER LVER ltac:(left; reflexivity) INL) as APER.
cps_sigma LVER FRSER SPER.
destruct (live_below_lo RT AF ΣER mER ER 16 lo ARTER INER LOW) as (_ & LOER & _).
destruct (frame_live_apart RT AF ΣER mER f 0%nat ER 16 ARTER INF INER) as (FA1ER & FA2ER). change (fs_size 0) with 64 in FA1ER, FA2ER. rewrite SHF0, <- SHF in FA2ER.
assert (BOUTER : forall b x, In b ((tt, ER, 16) :: ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))))) -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x [<-|Hb] Hx; [unfold blk_addr, blk_size in Hx; cbn [fst snd] in Hx; clear - Hx LOER APER FA1ER FA2ER; lia| exact (BOUTPG b x Hb Hx)]. }
assert (BRER : 0 < ER < 2^63) by (clear - POSER TOPER N72R; unfold USTACK_TOP in TOPER; lia).
assert (LVTER : rt_live RT ΣER = blocks_live ((tt, ER, 16) :: ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))))) ++ NEWL ++ (S, 160) :: rt_live RT Σ) by (rewrite LVER, LVTPG; reflexivity).
assert (FRTER : rt_frames RT ΣER = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRSER; exact FRTPG).
assert (SPTER : rt_sp0 RT ΣER = rt_sp0 RT Σ) by (rewrite SPER; exact SPTPG).
assert (POTER : rt_pois RT ΣER = rt_pois RT Σ) by (rewrite POER; exact POTPG).
assert (CRTER : rt_credit RT Σ - init_credit mo <= rt_credit RT ΣER <= rt_credit RT Σ) by (rewrite CRER; exact CRTPG).
assert (AL8ER : ER mod 8 = 0) by (clear - AL16ER; Z.div_mod_to_equations; lia).
clear LVER FRSER SPER POER CRER LVTPG FRTPG SPTPG POTPG CRTPG POSER AL16ER TOPER SUBFPG SUBLPG LIVELPG LIVEBPG LENPG CRDPG BOUTPG.
pose proof (zbufs_cons mER ER 16 ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))))) ltac:(clear - N72R; lia) (zero_chunk mER ER 16 ltac:(clear - N72R; lia) WRER BYER) ZB0ER) as ZBER.
clear WRER BYER ZB0ER INER APER LOER FA1ER FA2ER ACER.
repeat match goal with H : In (ER, _) (rt_live RT _) |- _ => clear H end.
destruct (af_acc_live RT AF ΣER mER S 160 ARTER INL) as (_ & ACSER).
assert (OBSER : aobj asegs mER S 160) by (split; [lia|]; split; [ulc| exact ACSER]).
cps_hide.
cps_seg (sbinit_w13 usp lo S SM ER f sf sfs). { reflexivity. } { reflexivity. }
destruct POST as (mcER & wa2ER & wa3ER & -> & MUER & WM'ER & MI'ER & XER & FRER).
repeat match goal with H : context [if sfs =? 40 then ?a else ?a] |- _ => replace (if sfs =? 40 then a else a) with a in H by (destruct (sfs =? 40); reflexivity) end.
pose proof (agree_blocks_of_munch asegs _ mER mcER LBL MUER WM'ER
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)) as AG'ER.
eapply decst_rep_agree in RL10; [| exact AG'ER]. clear AG'ER.
pose proof (zbufs_agree mER mcER _ ZBER (agree_blocks_of_munch asegs _ mER mcER _ MUER WM'ER
ltac:(intros b x Hb Hx; pose proof (BOUTER b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia))) as ZCER.
clear XPG FRPG OBSER ACSER UWER ZBER BRER.
revert FB0 FRS3.
cps_seg_post.
intros FB0 FRS3.
eapply rw_cells_transport in FB0; [| exact MUER| exact WM'ER| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 32; split; [clear - FLA1; unfold hid in FLA1; lia| exact I]].
eapply rw_cells_transport in FRS3; [| exact MUER| exact WM'ER| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 8; split; [clear - FLA2; unfold hid in FLA2; lia| exact I]].
assert (WMTER : wmono asegs m mcER) by cps_wmono. clear WMER WM'ER WMTPG MUER.

assert (UWMS : unwind_ch mcER (Z_to_bv 64 742948) (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -192))).
{ apply (sbinit_site_ch (rt_live RT Σ) (rt_frames RT Σ) m mcER s0 ra usp lo ras 742948 UE PF (sbi_frame_rec mcER usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRER eq_refl));
[apply TRS; unfold SBINIT_SITES; cbn [In]; tauto| ulc| clear - SPA; Z.div_mod_to_equations; lia| ulc| ulc| lia]. }
cps_rt CAL.
all: try (lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- Z.of_nat (length _) < LIVE_MAX => rewrite LENER; clear - LVM LNB; lia
| |- mcost _ <= _ => replace (64 * 1) with 64 by lia; rewrite MC64; exact CRDER
| |- _ <= _ < _ => clear - N72R; lia
| |- _ <= _ <= _ => clear - N72R; lia
end).
intros ccMS (ΣMS & MS & HccMS & LVMS & FRSMS & SPMS & CRMS & POSMS & AL16MS & TOPMS & POMS).
repeat match goal with H : ASTA RT _ PMc (eq _) _ |- _ => clear H end.
replace (64 * 1) with 64 in * by lia. rewrite MC64 in CRMS. rewrite Z.sub_0_r in CRMS.
revert XER FRER FB0 FRS3.
cps_unpack HccMS as (mMS & RSMS & (ARTMS & MIMS & WMMS & STMS) & PRESMS & WRMS & ACMS & BYMS).
intros XER FRER FB0 FRS3.
apply (rw_cells_pres_live _ _ _ mcER mMS _ _ 160 S 160 PRESMS WMMS) in XER; [| reflexivity| exact INL| lia| lia].
apply (rw_cells_pres_stack _ _ _ mcER mMS _ _ 192 PRESMS WMMS) in FRER; [| reflexivity| lia| clear - SPT; unfold USTACK_TOP; lia].
apply (rw_cells_pres_frame _ _ _ mcER mMS _ _ 32 f 0%nat PRESMS WMMS) in FB0; [| reflexivity| exact INF| lia| change (fs_size 0) with 64; lia].
apply (rw_cells_pres_fshadow _ _ _ mcER mMS _ _ 8 f 0%nat PRESMS WMMS) in FRS3; [| reflexivity| exact INF| rewrite <- SHF; lia| change (fs_size 0) with 64; rewrite SHF0; lia].
pose proof (agree_blocks_of_pres RT ΣER (rt_frames RT ΣER) (usp + -192) mcER mMS LBL PRESMS WMMS LIVELER) as AGMS.
eapply decst_rep_agree in RL10; [| exact AGMS]. clear AGMS.
pose proof (zbufs_agree mcER mMS ((tt, ER, 16) :: ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))))) ZCER (agree_blocks_of_pres RT ΣER (rt_frames RT ΣER) (usp + -192) mcER mMS ((tt, ER, 16) :: ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))))) PRESMS WMMS LIVEBER)) as ZB0MS.
clear PRESMS ZCER.
assert (SUBFMS : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT ΣMS)) by (intros e He; rewrite FRSMS; exact (SUBFER e He)).
assert (SUBLMS : forall e, In e (rt_live RT Σ) -> In e (rt_live RT ΣMS)) by (intros e He; rewrite LVMS; right; exact (SUBLER e He)).
assert (LIVELMS : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT ΣMS)) by (intros b Hb; rewrite LVMS; right; exact (LIVELER b Hb)).
assert (LIVEBMS : blocks_in_live RT ΣMS ((tt, MS, 64) :: ((tt, ER, 16) :: ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))))))) by (intros b [<-|Hb]; rewrite LVMS; [left; reflexivity| right; exact (LIVEBER b Hb)]).
assert (LENMS : Z.of_nat (length (rt_live RT ΣMS)) = Z.of_nat (length (rt_live RT Σ)) + 1 + LNBL + 8) by (rewrite LVMS; cbn [length]; rewrite Nat2Z.inj_succ, LENER; lia).
assert (CRDMS : 0 <= rt_credit RT ΣMS) by (rewrite CRMS; exact CRDER).
assert (INMS : In (MS, 64) (rt_live RT ΣMS)) by (rewrite LVMS; left; reflexivity).
pose proof (new_old_apart ΣMS mMS [(MS, 64)] (rt_live RT ΣER) MS 64 S 160 ARTMS LVMS ltac:(left; reflexivity) INL) as APMS.
cps_sigma LVMS FRSMS SPMS.
destruct (live_below_lo RT AF ΣMS mMS MS 64 lo ARTMS INMS LOW) as (_ & LOMS & _).
destruct (frame_live_apart RT AF ΣMS mMS f 0%nat MS 64 ARTMS INF INMS) as (FA1MS & FA2MS). change (fs_size 0) with 64 in FA1MS, FA2MS. rewrite SHF0, <- SHF in FA2MS.
assert (BOUTMS : forall b x, In b ((tt, MS, 64) :: ((tt, ER, 16) :: ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))))))) -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ (x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x [<-|Hb] Hx; [unfold blk_addr, blk_size in Hx; cbn [fst snd] in Hx; clear - Hx LOMS APMS FA1MS FA2MS; lia| exact (BOUTER b x Hb Hx)]. }
assert (BRMS : 0 < MS < 2^63) by (clear - POSMS TOPMS N72R; unfold USTACK_TOP in TOPMS; lia).
assert (LVTMS : rt_live RT ΣMS = blocks_live ((tt, MS, 64) :: ((tt, ER, 16) :: ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: [])))))))) ++ NEWL ++ (S, 160) :: rt_live RT Σ) by (rewrite LVMS, LVTER; reflexivity).
assert (FRTMS : rt_frames RT ΣMS = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRSMS; exact FRTER).
assert (SPTMS : rt_sp0 RT ΣMS = rt_sp0 RT Σ) by (rewrite SPMS; exact SPTER).
assert (POTMS : rt_pois RT ΣMS = rt_pois RT Σ) by (rewrite POMS; exact POTER).
assert (CRTMS : rt_credit RT Σ - init_credit mo <= rt_credit RT ΣMS <= rt_credit RT Σ) by (rewrite CRMS; exact CRTER).
assert (AL8MS : MS mod 8 = 0) by (clear - AL16MS; Z.div_mod_to_equations; lia).
clear LVMS FRSMS SPMS POMS CRMS LVTER FRTER SPTER POTER CRTER POSMS AL16MS TOPMS SUBFER SUBLER LIVELER LIVEBER LENER CRDER BOUTER.
pose proof (zbufs_cons mMS MS 64 ((tt, ER, 16) :: ((tt, PG, 16) :: ((tt, IQ, 32) :: ((tt, OQ, 32) :: ((tt, EX, N72) :: ((tt, G1, 256) :: ((tt, G0, 256) :: []))))))) ltac:(clear - N72R; lia) (zero_chunk mMS MS 64 ltac:(clear - N72R; lia) WRMS BYMS) ZB0MS) as ZBMS.
clear WRMS BYMS ZB0MS INMS APMS LOMS FA1MS FA2MS ACMS.
repeat match goal with H : In (MS, _) (rt_live RT _) |- _ => clear H end.
destruct (af_acc_live RT AF ΣMS mMS S 160 ARTMS INL) as (_ & ACSMS).
assert (OBSMS : aobj asegs mMS S 160) by (split; [lia|]; split; [ulc| exact ACSMS]).
cps_hide.
cps_seg (sbinit_w14 usp lo S SM MS f sf). { reflexivity. } { reflexivity. }
destruct POST as (mcMS & wa0MS & wa1MS & wa2MS & -> & MUMS & WM'MS & MI'MS & XMS & FRMS).
repeat match goal with H : context [if sfs =? 40 then ?a else ?a] |- _ => replace (if sfs =? 40 then a else a) with a in H by (destruct (sfs =? 40); reflexivity) end.
pose proof (agree_blocks_of_munch asegs _ mMS mcMS LBL MUMS WM'MS
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)) as AG'MS.
eapply decst_rep_agree in RL10; [| exact AG'MS]. clear AG'MS.
pose proof (zbufs_agree mMS mcMS _ ZBMS (agree_blocks_of_munch asegs _ mMS mcMS _ MUMS WM'MS
ltac:(intros b x Hb Hx; pose proof (BOUTMS b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia))) as ZCMS.
clear XER FRER OBSMS ACSMS UWMS ZBMS BRMS.
revert FB0 FRS3.
cps_seg_post.
intros FB0 FRS3.
eapply rw_cells_transport in FB0; [| exact MUMS| exact WM'MS| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 32; split; [clear - FLA1; unfold hid in FLA1; lia| exact I]].
eapply rw_cells_transport in FRS3; [| exact MUMS| exact WM'MS| cbn [disjoint_from]; change (Z.of_nat (cells_size _)) with 8; split; [clear - FLA2; unfold hid in FLA2; lia| exact I]].
assert (WMTMS : wmono asegs m mcMS) by cps_wmono. clear WMMS WM'MS WMTER MUMS.

assert (FTOP' : f + 64 <= APP_TOP) by (clear - FTOP; unfold APP_TOP, USTACK_TOP in *; change (fs_size 0) with 64 in FTOP; lia).
chunk_uncons FB0 as HDF.
cps_hide.
cps_seg (sbinit_epi_a usp f sf).
destruct POST as (me1 & -> & MUe1 & WMe1 & MIe1 & FRSe1).
pose proof (agree_blocks_of_munch asegs _ mcMS me1 LBL MUe1 WMe1
ltac:(intros b x Hb Hx; pose proof (BOUTL b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia)) as AGe1.
eapply decst_rep_agree in RL10; [| exact AGe1]. clear AGe1.
pose proof (zbufs_agree mcMS me1 _ ZCMS (agree_blocks_of_munch asegs _ mcMS me1 _ MUe1 WMe1
ltac:(intros b x Hb Hx; pose proof (BOUTMS b x Hb Hx) as H1; clear - H1; cbn [outside]; repeat split; lia))) as ZBe1.
clear HDF FB0 FRS3 ZCMS. unfold bF5 in FRSe1. cbn [map repeat] in FRSe1.
cps_seg_post.

lazymatch goal with A : X0ec.ART RT ΣMS me1 |- _ => rename A into ARTe1 end.
cps_release_intro_sub ARTe1 FRTMS SUBLMS (fun E : rt_frames RT Σ = [] => eq_trans POTMS (PNIL E)) Σr fl.
assert (NFLB : forall L, blocks_in_live RT ΣMS L -> forall b x, In b L -> blk_addr b <= x < blk_addr b + blk_size b -> outside [(fl, fl + 1)] x).
{ intros L BL b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl. apply NAC. right; right; left. exists (blk_addr b), (blk_size b). split; [exact (BL b Hb)| clear - Hx Hfl; cbn [fst snd] in Hfl; lia]. }
assert (FLS : fl < S \/ S + 160 <= fl).
{ destruct (Z_lt_dec fl S) as [L|L]; [left; exact L|]. destruct (Z_le_dec (S + 160) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists S, 160. split; [exact INL| clear - L G; lia]. }
cps_hide.
cps_seg (sbinit_epi_b usp lo f fl S).
destruct POST as (me2 & -> & MUe2 & WMe2 & MIe2 & STe2 & FLGe2).
eapply decst_rep_agree in RL10; [| exact (agree_blocks_of_munch asegs _ me1 me2 LBL MUe2 WMe2 (NFLB LBL LIVELMS))].
pose proof (zbufs_agree me1 me2 _ ZBe1 (agree_blocks_of_munch asegs _ me1 me2 _ MUe2 WMe2 (NFLB _ LIVEBMS))) as ZBe2.
clear ZBe1 FRMS FRSe1.
cps_release_done REL MUe2 WMe2 FLGe2.

apply Hk. clear Hk.
set (a := SBA AL G0 G1 EX OQ IQ MS PG ER).
set (st := sb_init_state mo lr).
set (BUFL := blocks_live [(tt, MS, 64); (tt, ER, 16); (tt, PG, 16); (tt, IQ, 32); (tt, OQ, 32); (tt, EX, N72); (tt, G1, 256); (tt, G0, 256)]) in *.
exists Σr, S, (sb_blocks st S a ++ LBL), (BUFL ++ NEWL ++ [(S, 160)]).
assert (ELIVE : rt_live RT Σr = (BUFL ++ NEWL ++ [(S, 160)]) ++ rt_live RT Σ) by (rewrite EL, LVTMS, <- !app_assoc; reflexivity).
assert (PERM : Permutation (BUFL ++ NEWL ++ [(S, 160)]) (blocks_live (sb_blocks st S a ++ LBL))).
{ unfold blocks_live. rewrite map_app. cbn [sb_blocks map blk_addr blk_size fst snd st sb_init_state sbd_subframeSize].
unfold SBSTATE_SIZEOF. rewrite <- ESFS, <- N72E.
apply Permutation_trans with ((S, 160) :: BUFL ++ NEWL); [rewrite app_assoc; apply Permutation_sym, Permutation_cons_append|].
apply perm_skip.
apply (Permutation_app (l := BUFL) (m := NEWL) (l' := [(G0, 256); (G1, 256); (EX, N72); (OQ, 32); (IQ, 32); (PG, 16); (ER, 16); (MS, 64)])
(m' := map (fun b : block => (blk_addr b, blk_size b)) LBL)); [| exact PERM3].
subst BUFL. unfold blocks_live. cbn [map blk_addr blk_size fst snd].
change [(MS, 64); (ER, 16); (PG, 16); (IQ, 32); (OQ, 32); (EX, N72); (G1, 256); (G0, 256)] with (rev [(G0, 256); (G1, 256); (EX, N72); (OQ, 32); (IQ, 32); (PG, 16); (ER, 16); (MS, 64)]).
apply Permutation_sym, Permutation_rev. }
assert (NDUP : List.NoDup (map blk_id (sb_blocks st S a ++ LBL))).
{ assert (E : map blk_id (sb_blocks st S a ++ LBL) = map fst (blocks_live (sb_blocks st S a ++ LBL))) by (unfold blocks_live; rewrite map_map; reflexivity).
rewrite E. apply (Permutation_NoDup (Permutation_map fst PERM)).
apply (live_nodup RT AF Σr me2 _ [] (rt_live RT Σ) ART ELIVE).
intros e He. apply in_app_iff in He. destruct He as [He|He].
- subst BUFL. unfold blocks_live in He. cbn [map blk_addr blk_size fst snd In] in He.
repeat (destruct He as [<-|He]; [cbn [snd]; clear - N72R; lia|]). destruct He.
- apply in_app_iff in He. destruct He as [He|[<-|[]]]; [| cbn [snd]; lia].
apply (Permutation_in _ PERM3) in He. unfold blocks_live in He. apply in_map_iff in He. destruct He as (b & <- & Hb). cbn [snd].
exact (drep_sizes_pos _ _ _ _ _ _ RL10 b Hb). }
assert (LENN : Z.of_nat (length (BUFL ++ NEWL ++ [(S, 160)])) = init_nblocks mo).
{ rewrite NBL. fold LNBL. rewrite !length_app. subst BUFL. unfold blocks_live. cbn [map length]. fold LNBL in LENL. clear - LENL. lia. }
assert (AL8ALL : forall x, In x (sb_blocks st S a ++ LBL) -> blk_addr x mod 8 = 0).
{ intros x Hx. apply in_app_iff in Hx. destruct Hx as [Hx|Hx]; [| exact (AL8L x Hx)].
cbn [sb_blocks In] in Hx.
repeat (destruct Hx as [<-|Hx]; [unfold blk_addr, a; cbn [fst snd a_g0 a_g1 a_exc a_oq a_iq a_msp a_pg a_er]; assumption|]). destruct Hx. }
split; [| split; [exact ELIVE|]; split; [exact PERM|]; split; [exact NDUP|]; split; [exact LENN|]; split; [exact EF|];
split; [rewrite ES; exact SPTMS|]; split; [rewrite EC; exact CRTMS|]; split; [rewrite EP; exact POTMS| exact AL8ALL]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists me2.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM10]|].
split. { split; [assumption|]. split; [exact MIe2|]. split; [cps_wmono| exact STe2]. }
split; [exact PF|].

assert (MOC : mo = ModeWB \/ mo = ModeUWB) by (clear - NENB; destruct mo; [congruence| left; reflexivity| right; reflexivity]).
assert (Q4 : Z.quot fs sfs = 4) by (clear - GEO; unfold hid in GEO; destruct GEO as [[-> ->]|[-> ->]]; reflexivity).
assert (DSMR : 0 <= dsm <= 7) by (rewrite EDSM; clear; destruct mo; cbn; lia).
assert (SFSP : 0 < sfs) by (clear - GEO'; unfold hid in GEO'; lia).
rewrite EDEC. unfold sb_wrap. rewrite ctl_gsr_snd. fold lr. fold st.
cbn [decst_rep]. exists a, (SBJ w0 (Z_to_bv 64 1000) zb4 zb4 (zw 64) (zw 64) (zw (Z.to_nat sfs)) (zw 8) (zw 8) (zw 16) (zw 4) (zw 4)), LBL.
split; [reflexivity|]. split; [exact S8|]. split; [clear - SPOS; lia|].
split.
{ unfold sb_inv, st, sb_init_state.
cbn [sbd_mode sbd_frame_size sbd_full_frame_size sbd_subframeSize sbd_nbSubframes sbd_lpcSize sbd_first sbd_sampling_rate sbd_lpc_enh_enabled sbd_encode_submode sbd_submodeID sbd_innov_save].
rewrite <- EFS, <- ESFS, <- EDSM, Q4. change (sbm_lpcSize mo) with 8.
split; [exact MOC|]. repeat split; try reflexivity; try (clear - LRR DSMR; lia). }
split.
{ unfold sb_junk_ok, st, sb_init_state. cbn [sj_pad1 sj_pad2 sj_g0 sj_g1 sj_exc sj_oq sj_iq sj_msp sj_pg sj_er sbd_subframeSize].
repeat split; try reflexivity. unfold zw. rewrite repeat_length, Z2Nat.id by lia. exact ESFS. }
split.
{ unfold sb_cells, st, sb_init_state, a.
cbn [sbd_mode sbd_frame_size sbd_full_frame_size sbd_subframeSize sbd_nbSubframes sbd_lpcSize sbd_first sbd_sampling_rate sbd_lpc_enh_enabled sbd_encode_submode sbd_submodeID
sbd_innov_save sb_isave_ptr a_low a_g0 a_g1 a_exc a_oq a_iq a_msp a_pg a_er sj_last_ener sj_seed sj_pad1 sj_pad2].
rewrite <- EMP, <- EFS, <- ESFS, <- EDSM, <- ESUB, Q4, (Z.mul_comm lr 2). change (sbm_lpcSize mo) with 8. exact XMS. }
split.
{ unfold sb_bufs, a. cbn [a_g0 a_g1 a_exc a_oq a_iq a_msp a_pg a_er sj_g0 sj_g1 sj_exc sj_oq sj_iq sj_msp sj_pg sj_er].
split; [apply (zbuf_recast 64); [lia| exact (proj2 (ZBe2 (tt, G0, 256) ltac:(cbn [In]; tauto)))]|].
split; [apply (zbuf_recast 64); [lia| exact (proj2 (ZBe2 (tt, G1, 256) ltac:(cbn [In]; tauto)))]|].
split.
{ pose proof (proj2 (ZBe2 (tt, EX, N72) ltac:(cbn [In]; tauto))) as ZX. clear - ZX GEO'. unfold hid in GEO'. subst N72.
destruct GEO' as [->| ->]; [apply (zbuf_recast 40)| apply (zbuf_recast 80)]; first [lia | exact ZX]. }
split; [apply (zbuf_recast 8); [lia| exact (proj2 (ZBe2 (tt, OQ, 32) ltac:(cbn [In]; tauto)))]|].
split; [apply (zbuf_recast 8); [lia| exact (proj2 (ZBe2 (tt, IQ, 32) ltac:(cbn [In]; tauto)))]|].
split; [apply (zbuf_recast 16); [lia| exact (proj2 (ZBe2 (tt, MS, 64) ltac:(cbn [In]; tauto)))]|].
split; [apply (zbuf_recast 4); [lia| exact (proj2 (ZBe2 (tt, PG, 16) ltac:(cbn [In]; tauto)))]|].
apply (zbuf_recast 4); [lia| exact (proj2 (ZBe2 (tt, ER, 16) ltac:(cbn [In]; tauto)))]. }
exists 0. exact RL10.
Qed.

Theorem init_cps_all : forall mo, init_cps_at mo.
Proof using AF CAL MSET SM0 AF_LIB.
intros mo. destruct mo.
- exact init_cps_nb.
- exact (init_cps_sb ModeWB ltac:(discriminate) init_cps_nb).
- exact (init_cps_sb ModeUWB ltac:(discriminate) (init_cps_sb ModeWB ltac:(discriminate) init_cps_nb)).
Qed.
End InitCPS.
