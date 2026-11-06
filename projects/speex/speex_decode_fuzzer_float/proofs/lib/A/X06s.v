(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1df X1ck X1cg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1nt X1rg X1rh X1re X1od X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X000 X04b X00c X07z X05o X05p X05s X05t
X0ae X09j X09u X0af X09p X09o X05l X05c X05m X09f X06d X069 X068 X06e
X071 X06v X06t X06u X073 X07j X072.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12c X14x X0r0 X0ra X0qz X0v9 X0rb X0wl X0wm X110 X106 X10c X10b X0w9 X0x2 X0x1 X0x6 X0xn X0xl X0xm X0xu X0ya X0xt.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X106 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x6 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xu OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ya OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xt.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Lemma live_remove_list_app : forall ps l1 l2, live_remove_list ps (l1 ++ l2) = live_remove_list ps l1 ++ live_remove_list ps l2.
Proof. induction ps as [|p ps IH]; intros l1 l2; [reflexivity|]. cbn [live_remove_list fold_right]. unfold live_remove_list in IH. rewrite IH. apply live_remove_app. Qed.
Lemma live_remove_list_all : forall ps l, (forall e, In e l -> In (fst e) ps) -> live_remove_list ps l = [].
Proof.
intros ps l H. destruct (live_remove_list ps l) as [|e l'] eqn:E; [reflexivity|]. exfalso.
assert (He : In e (live_remove_list ps l)) by (rewrite E; left; reflexivity).
pose proof (live_remove_list_sub _ _ _ He) as He1. pose proof (H e He1) as Hin.
clear E H He1. revert l He. induction ps as [|p ps IH]; intros l He; [destruct Hin|]. cbn [live_remove_list fold_right] in He.
apply live_remove_in in He as (He & NE). destruct Hin as [E|Hin]; [exact (NE (eq_sym E))| exact (IH Hin l He)].
Qed.
Lemma live_remove_list_none : forall ps l, (forall e, In e l -> ~ In (fst e) ps) -> live_remove_list ps l = l.
Proof.
induction ps as [|p ps IH]; intros l H; [reflexivity|]. cbn [live_remove_list fold_right]. unfold live_remove_list in IH.
rewrite IH by (intros e He Hin; apply (H e He); right; exact Hin). apply live_remove_none. intros e He E. apply (H e He). left. symmetry. exact E.
Qed.
Lemma live_remove_list_perm : forall ps l l', Permutation l l' -> Permutation (live_remove_list ps l) (live_remove_list ps l').
Proof. induction ps as [|p ps IH]; intros l l' P; [exact P|]. cbn [live_remove_list fold_right]. apply perm_live_remove. apply IH. exact P. Qed.

Lemma h_drep_head : forall OUT STEREO (m : mem) S (d : dec_state bptr) LBD, DREP OUT STEREO m S d LBD -> exists n, In (tt, S, n) LBD /\ 0 < n /\ S mod 8 = 0.
Proof.
intros OUT STEREO m S d LBD H. destruct d as [st|s low]; cbn [decst_rep] in H.
- destruct H as [-> NB]. exists NBSTATE_SIZEOF. destruct (nb_blk st). split; [left; reflexivity|]. split; [unfold NBSTATE_SIZEOF; lia| exact (proj1 NB)].
- destruct H as (a & j & LBL & -> & S8 & _). exists SBSTATE_SIZEOF. destruct (sbd_blk s) eqn:E. split; [left; cbn [sb_blocks]; rewrite E; reflexivity|].
split; [unfold SBSTATE_SIZEOF; lia| exact S8].
Qed.

Lemma in_ras_9736c : In 0x976d8 ALLOC_RAS.  Proof. unfold ALLOC_RAS. cbn [In]. tauto. Qed.
Lemma in_ras_97374 : In 0x976e0 ALLOC_RAS.  Proof. unfold ALLOC_RAS. cbn [In]. tauto. Qed.

Lemma destroy_stack_le : forall d, destroy_stack d <= 32 * Z.of_nat (dec_depth d) - 16.
Proof. induction d as [st|s low IH]; cbn [destroy_stack dec_depth]; [lia|]. rewrite Nat2Z.inj_succ. lia. Qed.

Section Clean.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis DESTROY : forall d, destroy_cps_at RT d.
Hypothesis BDES : speex_bits_destroy_cps RT.
Hypothesis SCLR : ogg_stream_clear_cps RT.
Hypothesis YCLR : ogg_sync_clear_cps RT.
Variable X : hinv.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.

Theorem h_clean_ok : h_clean_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Proof using AF ERR_loc OUT_loc IO_img AF_DRV DESTROY BDES SCLR YCLR.
intros HX h T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m & ra & t0 & t1 & t2 & a4 & a5 & a6 & a7 & r2 & r5 & r7 & r8 & r9 & r10 & t3 & t4 & t5 & t6 & v40 & v48 & v56 & v88 & j224 & j232 & v136
& ogc & opc & Hc & FRM & HS & HR & OGJ & OPJ).
pose proof (own_pos RT OUT_rep ERR_rep IO_FP X Σ1 m a h _ _ _ HR) as OPOS.
destruct HR as (ART1 & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & _ & _ & _ & BITS & SY & _ & _ & OSR & _ & _ & _ & DEC & HP).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART1 HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
unfold h_regs in Hc. unfold h_spill_cl in SP.

destruct (stk_carve bsegs m (x_lo X) (x_S1 X) 48 ST ltac:(lia)) as (STC & (jf & JF)).
replace (x_S1 X - Z.of_nat 48) with (x_S1 X + -48) in STC, JF by lia.
destruct (cl_frame_of_CB m (x_S1 X + -48) jf JF) as (c0 & c1 & c2 & c3 & c4 & c5 & FR). clear JF.
assert (SR0 : 0 <= a_S a < 2^63).
{ pose proof DEC as DEC0. unfold h_dec_rep in DEC0. destruct (h_st h) as [d|] eqn:EST; [| destruct DEC0 as (-> & _); lia].
destruct DEC0 as (R & _). destruct (h_drep_head _ _ _ _ _ _ R) as (n & INB & N0 & _).
assert (NS : h_st h <> None) by (rewrite EST; discriminate).
pose proof (own_in_blk a h NS _ INB) as INO. cbn [blk_addr blk_size] in INO.
destruct (proj1 HSP _ _ INO) as (P0 & PL & _). cbn [blk_addr blk_size fst snd] in P0, PL. unfold USTACK_TOP in *. lia. }

set (ADDR_OK := fun (ps : list Z) => (forall e, In e (h_own a h) -> fst e <> a_Dsy a \/ sy_data (h_oy h) = None -> In (fst e) ps)
/\ (forall e, In e (x_live X) -> ~ In (fst e) ps)
/\ (sy_data (h_oy h) <> None -> ~ In (a_Dsy a) ps)).
assert (K_ep : forall (Σ4 : rts RT) (m4 : mem) (cc4 : config) (ps : list Z)
(ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' : word) Fr' fc',
ASTA RT Σ4 (PMfd F0 fs0) (eq (MS (mkR ra' (Z64 (x_S1 X + -48)) (x_gp X) (Z64 6524056) t0' t1' t2' (Z64 (x_F X + 8480)) s1' a0' a1' a2' a3' a4' a5' a6' a7'
s2' s3' (Z64 (h_packet_count h)) r5 (Z64 (-8)) r7 r8 r9 r10 (Z64 (h_channels h)) t3' t4' t5' t6') Fr' (Z64 0x976ec) fc' None m4 (seg_rom bsegs))) cc4 ->
X1cn.frm0 fc' -> ADDR_OK ps ->
rt_live RT Σ4 = live_remove_list ps (rt_live RT Σ1) -> rt_frames RT Σ4 = rt_frames RT Σ1 -> rt_sp0 RT Σ4 = rt_sp0 RT Σ1 ->
rt_credit RT Σ4 = rt_credit RT Σ1 -> rt_pois RT Σ4 = rt_pois RT Σ1 ->
ART RT Σ4 m4 -> mem_inv bsegs m4 -> stk bsegs m4 (x_lo X) (x_S1 X + -48) ->
rw_cells bsegs m4 (x_S1 X + -48) (cl_frame c0 (Z64 (x_sf X)) r2 (Z64 (x_S1 X)) (Z64 (x_usp X)) (Z64 0x974b0)) ->
rt_pres_fp (x_live X) [(x_F X, 8%nat)] (x_S1 X) (h_WL IO_FP X) (x_mR X) m4 -> ERR_rep m4 -> (forall so, OUT_rep so (x_mR X) -> OUT_rep so m4) -> io_ssp m4 ->
rw_cells bsegs m4 (x_S1 X) (hsp (Z64 (x_sf X + 16)) (Z64 (x_F X)) (Z64 (x_F X)) (Z64 (x_d X)) (Z64 (x_F X + 64)) v40 v48 v56 (Z64 (x_F X + HO_RATE)) (Z64 (x_F X + HO_CBK))
(Z64 (h_granule_frame_size h)) v88 (Z64 (x_F X + HO_ENH)) (Z64 (h_extra_headers h)) (Z64 (x_F X + HO_OY)) (Z64 SHB)
(Z64 (x_F X + HO_STEREO)) v136 (Z64 (x_F X + HO_OG)) (Z64 (x_F X + HO_OS)) (Z64 (x_F X + HO_OP))
(Z64 (h_speex_serialno h)) (Z64 (x_F X + HO_LOOK)) (Z64 (x_F X + HO_FSZ)) (Z64 (x_F X + HO_BITS)) (Z64 (h_nframes h))
(Z64 (x_F X + HO_OUT)) (Z64 (a_S a)) j224 j232 (Z64 (x_F X))) ->
rw_cells bsegs m4 (x_sf X) [CB 16 HSH_P1] ->
sync_rep m4 (x_F X + 8480) (a_Dsy a) (h_oy h) (a_sybytes a) ->
realizes bsegs cc4 T).
{ intros Σ4 m4 cc4 ps ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' Fr' fc' Hc4 FRM4 (PS1 & PS2 & PS3) EL4 EF4 ES4 EC4 EP4
ART4 MI4 ST4 FR4 PF4 ERR4 OUTR4 SSP4 SP4 LSH4 SY4. clear Hc.
refine (rz_evt RT AF Σ4 (PMfd F0 fs0) _ _ T cc4 (PMfd_mat_stable F0 fs0) Hc4 _ _).
{ eapply cl_epi; [unfold USTACK_TOP in *; lia | exact FR4 | exact MI4]. }
intros ms5 cc5 -> Hc5. clear Hc4.
pose proof (stk_release bsegs m4 (x_lo X) (x_S1 X + -48) _ ST4 FR4 ltac:(lia)) as ST4'. cbn [cells_size cl_frame csize Nat.add] in ST4'.
replace (x_S1 X + -48 + Z.of_nat 48) with (x_S1 X) in ST4' by lia.
assert (INF4 : In (x_F X, 8%nat) (rt_frames RT Σ4)) by (rewrite EF4, EF; left; reflexivity).
assert (SYL4 : sy_data (h_oy h) <> None -> In (a_Dsy a, sy_storage (h_oy h)) (rt_live RT Σ4)).
{ intros NS. rewrite EL4. apply live_remove_list_keep; [| exact (PS3 NS)].
rewrite EL. apply in_or_app. left. exact (Permutation_in _ (Permutation_sym PERM) (own_in_Dsy a h NS)). }
unfold A_sync_clear_h in Hc5.
Time cps_rt (YCLR Σ4 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 (x_F X + 8480) (a_Dsy a) (x_F X) (x_lo X) 8%nat
(h_oy h) (a_sybytes a)).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ change (fs_size 8) with 16384. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). exact ST4'. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold RT_STACK. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). clear - S32. Z.div_mod_to_equations. lia. }
intros cc6 (Σ5 & Hc6 & EL5 & EF5 & ES5 & EC5 & EP5). clear Hc5.
Time cps_unpack_lib Hc6 as (m5 & RS & RA5 & PR5 & SY5).
destruct RS as (-> & ->).
destruct RA5 as (ART5 & MI5 & ST5).

refine (rz_evt RT AF Σ5 (PMfd F0 fs0) _ _ T cc6 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply cl_w5; [reflexivity | exact MI5]. }
intros ms7 cc7 -> Hc7. clear Hc.

assert (XD : sy_data (h_oy h) <> None -> forall e, In e (x_live X) -> fst e <> a_Dsy a).
{ intros NS [q k] Hq E. cbn [fst] in E. subst q.
assert (INS : In (a_Dsy a, sy_storage (h_oy h)) (h_own a h)) by (apply own_in_Dsy; exact NS).
destruct (proj1 HSP _ _ INS) as (_ & _ & _ & _ & _ & SEP). pose proof (OPOS _ _ INS) as P1.
pose proof (proj1 (hi_live _ _ _ HX) _ _ Hq) as P2. destruct (SEP _ _ Hq); lia. }
assert (XIN : forall e, In e (x_live X) -> In e (sync_clear_live (h_oy h) (a_Dsy a) (rt_live RT Σ4))).
{ intros e He. assert (He4 : In e (rt_live RT Σ4)).
{ rewrite EL4. apply live_remove_list_keep; [rewrite EL; apply in_or_app; right; exact He| exact (PS2 e He)]. }
unfold sync_clear_live, bptr. destruct (sy_data (h_oy h)) eqn:ED; [| exact He4].
apply live_remove_keep; [exact He4| apply XD; [discriminate| exact He]]. }
assert (ELX : rt_live RT Σ5 = x_live X).
{ rewrite EL5, EL4, EL. unfold sync_clear_live, bptr. destruct (sy_data (h_oy h)) eqn:ED.
- change (live_remove (a_Dsy a) (live_remove_list ps (a_P a ++ x_live X))) with (live_remove_list (a_Dsy a :: ps) (a_P a ++ x_live X)).
rewrite live_remove_list_app, live_remove_list_all, live_remove_list_none; [reflexivity| |].
+ intros e He [E|Hin]; [exact (XD ltac:(discriminate) e He (eq_sym E))| exact (PS2 e He Hin)].
+ intros e He. pose proof (Permutation_in _ PERM He) as Ho. destruct (Z.eq_dec (fst e) (a_Dsy a)) as [E|NE]; [left; symmetry; exact E|].
right. apply PS1; [exact Ho| left; exact NE].
- rewrite live_remove_list_app, live_remove_list_all, live_remove_list_none; [reflexivity| exact PS2 |].
intros e He. apply PS1; [exact (Permutation_in _ PERM He)| right; reflexivity]. }
rewrite EF4, EF in PR5.
assert (FPH : fp_h X a h [(x_F X + 8480, x_F X + 8480 + 32)]) by (apply fp_h_cons; [right; right; left; lia| apply fp_h_nil]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ4 m4 m5 a h _ _ HSP PR5 XIN FPH (AF_DRV _ _ ART5) PF4 ERR4 OUTR4 SSP4)
as (PF5 & ERR5 & OUTR5 & _).
assert (INF : In (x_F X, 8%nat) [(x_F X, 8%nat)]) by (left; reflexivity).
pose proof hsp_size as HSPS.
eapply (htr_rw _ _ _ _ m4 m5 PR5) in SP4; rewrite ?HSPS; [| apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_cons; [lia| apply rng_out_nil]].
eapply (htr_rw _ _ _ _ m4 m5 PR5) in LSH4; cbn [cells_size csize Nat.add];
[| apply (acl_fshadow _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; lia| apply rng_out_cons; [lia| apply rng_out_nil]].

assert (HCR : h_cost h <= FUZZ_COST - 1).
{ destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PC & _ & _ & _ & B & _ & P1 & P2 & _ & _ & _ & _ & P7 & _).
pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold h_cost, h_consumed, h_pend, H_HDR_CREDIT, H_DEC_CREDIT, FUZZ_COST, MAX_FUZZ_SIZE in *. lia. }
apply Hk. unfold at_XT.
do 4 eexists. do 24 eexists. do 27 eexists.
split; [exact Hc7|]. split; [exact FRM4|]. split; [exact ELX|]. split; [rewrite EF5, EF4; exact EF|]. split; [rewrite ES5, ES4; exact ESP|].
split; [rewrite EP5, EP4; exact EPO0|]. split; [rewrite EC5, EC4; lia|].
split; [exact ART5|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact PF5|]. split; [exact ERR5|]. split; [exact OUTR5|].
split; [exact SP4| exact LSH4]. }

assert (BSH_OF : forall m', rt_pres_fp (x_live X) [(x_F X, 8%nat)] (x_S1 X) (h_WL IO_FP X) (x_mR X) m' -> ro_cells bsegs m' (shad (x_F X + 8400)) bits_shadow).
{ intros m' PF'. pose proof (h_shr_at OUT_rep IO_FP IO_img X HX m' PF') as B. destruct B as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
pose proof (bytes_at_sub m' (x_sf X + 16) HSH_R 1034 6 B ltac:(vm_compute; lia)) as B6.
assert (E6 : firstn 6 (skipn 1034 HSH_R) = repeat (Z_to_bv 8 0) 6) by (vm_compute; reflexivity).
rewrite E6 in B6. replace (x_sf X + 16 + Z.of_nat 1034) with (x_sf X + 1050) in B6 by (change (Z.of_nat 1034) with 1034; lia).
assert (ESB : shad (x_F X + 8400) = x_sf X + 1050)
by (rewrite (shad_aligned_add (x_F X) 8400 ltac:(clear - F64; Z.div_mod_to_equations; lia) ltac:(lia)), <- ESF; change (8400 / 8) with 1050; reflexivity).
rewrite ESB. unfold bits_shadow. split; [cbn; tauto|]. cbn [cells_bytes cbytes map repeat app]. exact B6. }

assert (XNE : forall p q, In (p, q) (h_own a h) -> forall e, In e (x_live X) -> fst e <> p).
{ intros p q Hin [q' k] Hq E. cbn [fst] in E. subst q'.
destruct (proj1 HSP _ _ Hin) as (_ & _ & _ & _ & _ & SEP). pose proof (OPOS _ _ Hin) as P1.
pose proof (proj1 (hi_live _ _ _ HX) _ _ Hq) as P2. destruct (SEP _ _ Hq); lia. }
pose proof (proj2 (proj2 HSP)) as NDO.
assert (ADDR : forall ps, (forall p, In p ps -> exists q, In (p, q) (h_own a h) /\ (sy_data (h_oy h) <> None -> p <> a_Dsy a)) ->
In (a_Dc a) ps -> (h_st h <> None -> forall b, In b (a_LBD a) -> In (blk_addr b) ps) ->
(h_stream_init h <> 0 -> In (a_Bd a) ps /\ In (a_L a) ps /\ In (a_G a) ps) -> ADDR_OK ps).
{ intros ps PSO PDc PBL PST. split; [| split].
- intros [p q] Hin Hcase. cbn [fst] in Hcase |- *. unfold h_own in Hin. apply in_app_or in Hin as [Hin|Hin].
+ destruct (h_st h) as [d|] eqn:EST; [| destruct Hin]. unfold blocks_live in Hin. apply in_map_iff in Hin as (b & E & Hb). injection E as <- <-.
apply PBL; [first [discriminate | rewrite EST; discriminate]| exact Hb].
+ apply in_app_or in Hin as [[E|[]]|Hin]; [injection E as <- <-; exact PDc|].
apply in_app_or in Hin as [Hin|Hin].
* destruct (h_stream_init h =? 0) eqn:E0; [destruct Hin|]. apply Z.eqb_neq in E0.
destruct (PST E0) as (PB & PL & PG). destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; assumption.
* destruct (sy_data (h_oy h)) eqn:ED; [| destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
destruct Hcase as [NE|E]; [contradiction| discriminate].
- intros e He Hin. destruct (PSO _ Hin) as (q & Hq & _). exact (XNE _ _ Hq e He eq_refl).
- intros NS Hin. destruct (PSO _ Hin) as (q & Hq & NE). exact (NE NS eq_refl). }
assert (K_bd : forall (Σ2 : rts RT) (m2 : mem) (cc2 : config) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) Fr' fc',
ASTA RT Σ2 (PMfd F0 fs0) (eq (MS (mkR (Z64 0x976e0) (Z64 (x_S1 X + -48)) (x_gp X) (Z64 6524056) t0' t1' t2' (Z64 (x_F X + 8480)) (Z64 (x_F X + HO_OS))
(Z64 (x_F X + HO_BITS)) a1' a2' a3' a4' a5' a6' a7' (Z64 (h_stream_init h)) (Z64 (x_F X + HO_BITS))
(Z64 (h_packet_count h)) r5 (Z64 (-8)) r7 r8 r9 r10 (Z64 (h_channels h)) t3' t4' t5' t6') Fr' (Z64 A_bits_destroy_h) fc' None m2 (seg_rom bsegs))) cc2 ->
X1cn.frm0 fc' ->
rt_live RT Σ2 = live_remove_list (map blk_addr (a_LBD a)) (rt_live RT Σ1) -> rt_frames RT Σ2 = rt_frames RT Σ1 -> rt_sp0 RT Σ2 = rt_sp0 RT Σ1 ->
rt_credit RT Σ2 = rt_credit RT Σ1 -> rt_pois RT Σ2 = rt_pois RT Σ1 ->
ART RT Σ2 m2 -> mem_inv bsegs m2 -> stk bsegs m2 (x_lo X) (x_S1 X + -48) ->
rw_cells bsegs m2 (x_S1 X + -48) (cl_frame c0 (Z64 (x_sf X)) r2 (Z64 (x_S1 X)) (Z64 (x_usp X)) (Z64 0x974b0)) ->
rt_pres_fp (x_live X) [(x_F X, 8%nat)] (x_S1 X) (h_WL IO_FP X) (x_mR X) m2 -> ERR_rep m2 -> (forall so, OUT_rep so (x_mR X) -> OUT_rep so m2) -> io_ssp m2 ->
rw_cells bsegs m2 (x_S1 X) (hsp (Z64 (x_sf X + 16)) (Z64 (x_F X)) (Z64 (x_F X)) (Z64 (x_d X)) (Z64 (x_F X + 64)) v40 v48 v56 (Z64 (x_F X + HO_RATE)) (Z64 (x_F X + HO_CBK))
(Z64 (h_granule_frame_size h)) v88 (Z64 (x_F X + HO_ENH)) (Z64 (h_extra_headers h)) (Z64 (x_F X + HO_OY)) (Z64 SHB)
(Z64 (x_F X + HO_STEREO)) v136 (Z64 (x_F X + HO_OG)) (Z64 (x_F X + HO_OS)) (Z64 (x_F X + HO_OP))
(Z64 (h_speex_serialno h)) (Z64 (x_F X + HO_LOOK)) (Z64 (x_F X + HO_FSZ)) (Z64 (x_F X + HO_BITS)) (Z64 (h_nframes h))
(Z64 (x_F X + HO_OUT)) (Z64 (a_S a)) j224 j232 (Z64 (x_F X))) ->
rw_cells bsegs m2 (x_sf X) [CB 16 HSH_P1] ->
bits_rep bsegs m2 (x_F X + HO_BITS) (a_Dc a) (h_bits h) -> h_os_rep X m2 a h ->
sync_rep m2 (x_F X + 8480) (a_Dsy a) (h_oy h) (a_sybytes a) ->
realizes bsegs cc2 T).
{ intros Σ2 m2 cc2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Fr' fc' Hc2 FRM2 EL2 EF2 ES2 EC2 EP2 ART2 MI2 ST2 FR2 PF2 ERR2 OUTR2 SSP2 SP2 LSH2
BITS2 OSR2 SY2. clear Hc.
assert (INF2 : In (x_F X, 8%nat) (rt_frames RT Σ2)) by (rewrite EF2, EF; left; reflexivity).
assert (INDc : In (a_Dc a, sb_buf_size (h_bits h)) (rt_live RT Σ2)).
{ rewrite EL2. apply live_remove_list_keep; [rewrite EL; apply in_or_app; left; exact (Permutation_in _ (Permutation_sym PERM) (own_in_Dc a h))|].
cbn [fst]. intros Hin. apply in_map_iff in Hin as (b & E & Hb). unfold h_dec_rep in DEC. destruct (h_st h) as [d|]; [| destruct DEC as (_ & E0); rewrite E0 in Hb; destruct Hb].
destruct DEC as (_ & _ & _ & _ & _ & _ & _ & NDc & _). exact (NDc b Hb E). }
unfold HO_BITS in BITS2. unfold A_bits_destroy_h in Hc2.
Time cps_rt (BDES Σ2 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 (x_F X + 8400) (a_Dc a) (x_F X) (x_lo X) 8%nat (h_bits h)).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ destruct HP as (_ & _ & _ & _ & B & _). exact B. }
{ destruct HP as (_ & _ & _ & _ & _ & B & _). exact B. }
{ exact (BSH_OF m2 PF2). }
{ change (fs_size 8) with 16384. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). exact ST2. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold RT_STACK. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). clear - S32. Z.div_mod_to_equations. lia. }
{ apply unwind_ok_ch. split; [cbn; rewrite unsigned_lit by lia; exact in_ras_97374|].
left. rewrite !unsigned_lit by (unfold USTACK_TOP in *; lia). lia. }
intros cc3 (Σ3 & Hc3 & EL3 & EF3 & ES3 & EC3 & EP3). clear Hc2.
Time cps_unpack_lib Hc3 as (v3 & m3 & RS & RA3 & PR3).
destruct RS as (-> & ->).
destruct RA3 as (ART3 & MI3 & ST3).
rewrite EF2, EF in PR3.
assert (INL2 : forall p q, In (p, q) (h_own a h) -> ~ In p (map blk_addr (a_LBD a)) -> p <> a_Dc a -> In (p, q) (rt_live RT Σ3)).
{ intros p q Hin NB NE. rewrite EL3, EL2. apply live_remove_keep; [| exact NE]. apply live_remove_list_keep; [| exact NB].
rewrite EL. apply in_or_app. left. exact (Permutation_in _ (Permutation_sym PERM) Hin). }

assert (NOS : h_stream_init h <> 0 -> forall p, In p [a_Bd a; a_L a; a_G a] -> ~ In p (map blk_addr (a_LBD a)) /\ p <> a_Dc a).
{ intros NE p Hp. pose proof NDO as ND1. unfold h_own in ND1. replace (h_stream_init h =? 0) with false in ND1 by (symmetry; apply Z.eqb_neq; exact NE).
rewrite !map_app in ND1. cbn [map fst] in ND1.
split.
- intros Hb. unfold h_dec_rep in DEC. destruct (h_st h) as [d|] eqn:EST; [| destruct DEC as (_ & E0); rewrite E0 in Hb; destruct Hb].
apply (nodup_app_disj _ _ p ND1); [unfold blocks_live; rewrite map_map; exact Hb|].
destruct Hp as [<-|[<-|[<-|[]]]]; rewrite ?in_app_iff; cbn; tauto.
- intros E. subst p. apply NoDup_app_remove_l in ND1. apply NoDup_cons_iff in ND1 as (N1 & _). apply N1.
destruct Hp as [E|[E|[E|[]]]]; rewrite ?in_app_iff; cbn; rewrite <- E; tauto. }
pose proof (own_ne_Dsy a h NDO) as ONE.
assert (NDsy : sy_data (h_oy h) <> None -> ~ In (a_Dsy a) (map blk_addr (a_LBD a)) /\ a_Dsy a <> a_Dc a).
{ intros NS. destruct (ONE NS) as (N1 & _ & N3). split; [| congruence].
intros Hb. apply in_map_iff in Hb as (b & E & Hb).
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E0); rewrite E0 in Hb; destruct Hb]).
exact (N3 NS0 b Hb E). }
assert (XL3 : forall e, In e (x_live X) -> In e (rt_live RT Σ3)).
{ intros [p q] He. rewrite EL3, EL2. apply live_remove_keep; [apply live_remove_list_keep|].
- rewrite EL. apply in_or_app. right. exact He.
- cbn [fst]. intros Hb. apply in_map_iff in Hb as (b & E & Hb).
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E0); rewrite E0 in Hb; destruct Hb]).
exact (XNE _ _ (own_in_blk a h NS0 b Hb) (p, q) He (eq_sym E)).
- cbn [fst]. exact (XNE _ _ (own_in_Dc a h) (p, q) He). }
assert (PR3S : rt_pres_fp (rt_live RT Σ3) [(x_F X, 8%nat)] (x_S1 X) [] m2 m3).
{ apply (pres_fp_mono _ _ _ _ _ _ _ m2 m3 PR3); [intros e He; exact He| intros e He; exact He| lia]. }
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ3 m2 m3 a h _ _ HSP PR3S XL3 (fp_h_nil X a h) (AF_DRV _ _ ART3) PF2 ERR2 OUTR2 SSP2)
as (PF3 & ERR3 & OUTR3 & SSP3).
assert (INF : In (x_F X, 8%nat) [(x_F X, 8%nat)]) by (left; reflexivity).
pose proof hsp_size as HSPS.
eapply (htr_rw _ _ _ _ m2 m3 PR3) in FR2; [| cbn [cl_frame cells_size csize Nat.add]; apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_nil].
eapply (htr_rw _ _ _ _ m2 m3 PR3) in SP2; rewrite ?HSPS; [| apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_nil].
eapply (htr_rw _ _ _ _ m2 m3 PR3) in LSH2; cbn [cells_size csize Nat.add];
[| apply (acl_fshadow _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; lia| apply rng_out_nil].
assert (OSR3 : h_os_rep X m3 a h).
{ apply (h_os_rep_tr _ _ _ _ m2 m3 PR3 X a h OSR2).
- apply (acl_frame _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
destruct (NOS NE (a_Bd a) (or_introl eq_refl)) as (B1 & B2). destruct (NOS NE (a_L a) (or_intror (or_introl eq_refl))) as (L1 & L2).
destruct (NOS NE (a_G a) (or_intror (or_intror (or_introl eq_refl)))) as (G1 & G2).
split; [apply (acl_live _ _ _ _ _ _ _ (INL2 _ _ IB B1 B2)); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (INL2 _ _ IL L1 L2)); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (INL2 _ _ IG G1 G2)); lia| apply rng_out_nil]. }
assert (SY3 : sync_rep m3 (x_F X + 8480) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m2 m3 PR3 _ _ _ _ SY2).
- apply (acl_frame _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_nil.
- intros NS. destruct (NDsy NS) as (N1 & N2). split; [| apply rng_out_nil].
apply (acl_live _ _ _ _ _ _ _ (INL2 _ _ (own_in_Dsy a h NS) N1 N2)); unfold bptr in *; lia. }
clear OSR2 SY2 BITS2 PR3S.

assert (SIR : 0 <= h_stream_init h < 2^63) by (destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S & _); destruct S as [S|S]; rewrite S; lia).
refine (rz_evt RT AF Σ3 (PMfd F0 fs0) _ _ T cc3 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply cl_w3; [reflexivity | exact SIR | exact MI3]. }
intros ms4 cc4 POST4 Hc4. clear Hc. cbv beta in POST4.

assert (PSO_blk : forall p, In p (map blk_addr (a_LBD a)) -> exists q, In (p, q) (h_own a h) /\ (sy_data (h_oy h) <> None -> p <> a_Dsy a)).
{ intros p Hp. apply in_map_iff in Hp as (b & <- & Hb).
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E0); rewrite E0 in Hb; destruct Hb]).
exists (blk_size b). split; [exact (own_in_blk a h NS0 b Hb)|]. intros NS. exact (proj2 (proj2 (ONE NS)) NS0 b Hb). }
assert (PSO_Dc : exists q, In (a_Dc a, q) (h_own a h) /\ (sy_data (h_oy h) <> None -> a_Dc a <> a_Dsy a)).
{ exists (sb_buf_size (h_bits h)). split; [exact (own_in_Dc a h)| intros NS; exact (proj1 (ONE NS))]. }
destruct POST4 as [(NE4 & ->) | (E4 & ->)].
-
pose proof OSR3 as OSR3'. unfold h_os_rep in OSR3'. replace (h_stream_init h =? 0) with false in OSR3' by (symmetry; apply Z.eqb_neq; exact NE4).
destruct OSR3' as (OSC & LSH0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & LS0 & BS0 & BL & BG & LG & _).
destruct (own_in_os a h NE4) as (IB & IL & IG).
destruct (NOS NE4 (a_Bd a) (or_introl eq_refl)) as (B1 & B2). destruct (NOS NE4 (a_L a) (or_intror (or_introl eq_refl))) as (L1 & L2).
destruct (NOS NE4 (a_G a) (or_intror (or_intror (or_introl eq_refl)))) as (G1 & G2).
assert (SLV : stream_live RT Σ3 (h_os h) (a_Bd a) (a_L a) (a_G a)).
{ split; [exact (INL2 _ _ IB B1 B2)|]. split; [exact (INL2 _ _ IL L1 L2)|]. split; [exact (INL2 _ _ IG G1 G2)|]. split; [exact BL|]. split; [exact BG| exact LG]. }
pose proof (h_acc_at OUT_rep IO_FP IO_img X HX m3 PF3) as (_ & _ & _ & _ & _ & _ & ACOS & _).
assert (INF3 : In (x_F X, 8%nat) (rt_frames RT Σ3)) by (rewrite EF3, EF2, EF; left; reflexivity).
unfold HO_OS in OSC, ACOS. unfold A_stream_clear_h in Hc4.
Time cps_rt (SCLR Σ3 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 (x_F X + 8688) (a_Bd a) (a_L a) (a_G a) (x_F X) (x_lo X) 8%nat
(h_os h) (a_shdr a)).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ unfold bptr in *. lia. }
{ unfold bptr in *. lia. }
{ change (fs_size 8) with 16384. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). exact ST3. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold RT_STACK. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). clear - S32. Z.div_mod_to_equations. lia. }
intros cc5 (Σ4 & Hc5 & EL4 & EF4 & ES4 & EC4 & EP4). clear Hc4.
Time cps_unpack_lib Hc5 as (m4 & RS & RA4 & PR4 & OSC4).
destruct RS as (-> & ->).
destruct RA4 as (ART4 & MI4 & ST4).
rewrite EF3, EF2, EF in PR4.
assert (XL4 : forall e, In e (x_live X) -> In e (live_remove (a_G a) (live_remove (a_L a) (live_remove (a_Bd a) (rt_live RT Σ3))))).
{ intros e He. apply live_remove_keep; [apply live_remove_keep; [apply live_remove_keep; [exact (XL3 e He)|]|]|].
- exact (XNE _ _ IB e He). - exact (XNE _ _ IL e He). - exact (XNE _ _ IG e He). }
assert (PR4S : rt_pres_fp (live_remove (a_G a) (live_remove (a_L a) (live_remove (a_Bd a) (rt_live RT Σ3)))) [(x_F X, 8%nat)] (x_S1 X)
[(x_F X + 8688, x_F X + 8688 + 408)] m3 m4).
{ apply (pres_fp_mono _ _ _ _ _ _ _ m3 m4 PR4); [intros e He; exact He| intros e He; exact He| lia]. }
assert (FPH4 : fp_h X a h [(x_F X + 8688, x_F X + 8688 + 408)]) by (apply fp_h_cons; [right; right; left; lia| apply fp_h_nil]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ4 m3 m4 a h _ _ HSP PR4S XL4 FPH4 (AF_DRV _ _ ART4) PF3 ERR3 OUTR3 SSP3)
as (PF4 & ERR4 & OUTR4 & SSP4).
clear PR4S.
eapply (htr_rw _ _ _ _ m3 m4 PR4) in FR2; [| cbn [cl_frame cells_size csize Nat.add]; apply acl_stack; unfold USTACK_TOP in *; lia|
apply rng_out_cons; [cbn [cl_frame cells_size csize Nat.add]; lia| apply rng_out_nil]].
eapply (htr_rw _ _ _ _ m3 m4 PR4) in SP2; rewrite ?HSPS; [| apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_cons; [lia| apply rng_out_nil]].
eapply (htr_rw _ _ _ _ m3 m4 PR4) in LSH2; cbn [cells_size csize Nat.add];
[| apply (acl_fshadow _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; lia| apply rng_out_cons; [lia| apply rng_out_nil]].
assert (SY4 : sync_rep m4 (x_F X + 8480) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m3 m4 PR4 _ _ _ _ SY3).
- apply (acl_frame _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia| apply rng_out_nil].
- intros NS. destruct (NDsy NS) as (N1 & N2). destruct ((proj1 (proj2 (ONE NS))) NE4) as (NB & NL & NG).
pose proof (own_in_Dsy a h NS) as INS. unfold bptr in *. split.
+ apply (acl_live _ _ _ (a_Dsy a) (sy_storage (h_oy h))); [| lia| lia].
apply live_remove_keep; [apply live_remove_keep; [apply live_remove_keep; [exact (INL2 _ _ INS N1 N2)|]|]|]; cbn [fst]; congruence.
+ apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ INS); lia| apply rng_out_nil]. }
clear SY3 PR4.
replace (ret_pc (Z64 620268)) with (Z64 0x976ec) in Hc by (symmetry; apply ret_pc_even; [lia| reflexivity]).
apply (K_ep Σ4 m4 cc5 ([a_G a; a_L a; a_Bd a; a_Dc a] ++ map blk_addr (a_LBD a)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr' fc' Hc FRM2).
{ apply ADDR.
- intros p Hp. cbn [app In] in Hp. destruct Hp as [<-|[<-|[<-|[<-|Hp]]]].
+ exists (8 * os_lacing_storage (h_os h)). split; [exact IG| intros NS; exact (proj2 (proj2 ((proj1 (proj2 (ONE NS))) NE4)))].
+ exists (4 * os_lacing_storage (h_os h)). split; [exact IL| intros NS; exact (proj1 (proj2 ((proj1 (proj2 (ONE NS))) NE4)))].
+ exists (os_body_storage (h_os h)). split; [exact IB| intros NS; exact (proj1 ((proj1 (proj2 (ONE NS))) NE4))].
+ exact PSO_Dc.
+ exact (PSO_blk p Hp).
- right; right; right; left; reflexivity.
- intros _ b Hb. right; right; right; right. apply in_map. exact Hb.
- intros _. split; [right; right; left; reflexivity|]. split; [right; left; reflexivity| left; reflexivity]. }
{ rewrite EL4, EL3, EL2. reflexivity. }
{ rewrite EF4, EF3, EF2. reflexivity. }
{ rewrite ES4, ES3, ES2. reflexivity. }
{ rewrite EC4, EC3, EC2. reflexivity. }
{ rewrite EP4, EP3, EP2. reflexivity. }
{ exact ART4. }
{ exact MI4. }
{ exact ST4. }
{ exact FR2. }
{ exact PF4. }
{ exact ERR4. }
{ exact OUTR4. }
{ exact SSP4. }
{ exact SP2. }
{ exact LSH2. }
{ exact SY4. }
-
apply (K_ep Σ3 m3 cc4 (a_Dc a :: map blk_addr (a_LBD a)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr' fc' Hc4 FRM2).
{ apply ADDR.
- intros p Hp. destruct Hp as [<-|Hp]; [exact PSO_Dc| exact (PSO_blk p Hp)].
- left; reflexivity.
- intros _ b Hb. right. apply in_map. exact Hb.
- intros NE. exfalso. exact (NE E4). }
{ rewrite EL3, EL2. reflexivity. }
{ rewrite EF3, EF2. reflexivity. }
{ rewrite ES3, ES2. reflexivity. }
{ rewrite EC3, EC2. reflexivity. }
{ rewrite EP3, EP2. reflexivity. }
{ exact ART3. }
{ exact MI3. }
{ exact ST3. }
{ exact FR2. }
{ exact PF3. }
{ exact ERR3. }
{ exact OUTR3. }
{ exact SSP3. }
{ exact SP2. }
{ exact LSH2. }
{ exact SY3. } }

refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply cl_w1; [exact SR0 | unfold USTACK_TOP in *; lia | exact SP | exact FR | exact MI]. }
intros ms1 cc1 (m1 & POST1 & MU1 & WM1 & MI1 & FR1) Hc1. clear Hc FR.

assert (PR1 : rt_pres_fp (rt_live RT Σ1) [(x_F X, 8%nat)] (x_S1 X) [] m m1).
{ apply (pres_fp_of_munch _ _ _ _ _ m m1 MU1). intros x Hx _. cbn [outside]. split; [| exact I]. intros Hin.
destruct Hx as [H|[H|[H|[H|H]]]].
- lia.
- pose proof (client_static_range _ H). unfold SEGTOP_A, USTACK_TOP in *. lia.
- destruct H as (p & q & Hpq & Hx). rewrite EL in Hpq. apply in_app_or in Hpq as [Hpq|Hpq].
+ destruct (proj1 HSP _ _ (Permutation_in _ PERM Hpq)) as (_ & PL & _). lia.
+ destruct (hi_live_geo _ _ _ HX p q Hpq) as (PL & _). lia.
- destruct H as (f & k & [E|[]] & Hx). injection E as <- <-. change (fs_size 8) with 16384 in Hx. lia.
- destruct H as (f & k & [E|[]] & Hx). injection E as <- <-. change (fs_size 8) with 16384 in Hx. rewrite <- ESF, ESF2 in Hx. unfold SH_HI in *. lia. }
assert (ART1' : ART RT Σ1 m1).
{ apply (af_frame RT AF Σ1 m m1 (x_S1 X + -48) ART1); [rewrite ESP; pose proof (hi_lo _ _ _ HX) as (LW0 & _); unfold STACK_WIN in *; lia| | exact WM1].
intros b Hb. apply MU1. cbn [outside]. rewrite EF in Hb. split; [intros Hin; apply Hb; left; unfold USTACK_TOP in *; lia| exact I]. }
assert (STC1 : stk bsegs m1 (x_lo X) (x_S1 X + -48)).
{ apply (stk_agree bsegs m m1 _ _ STC); [| exact WM1]. apply (agree_of_munch _ m m1 _ MU1). intros x Hx. cbn [outside]. split; [lia| exact I]. }
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m m1 a h _ _ HSP PR1
ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) (fp_h_nil X a h) (AF_DRV _ _ ART1') PF ERR OUTR SSP) as (PF1 & ERR1 & OUTR1 & SSP1).
assert (INF : In (x_F X, 8%nat) [(x_F X, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
pose proof hsp_size as HSPS.
eapply (htr_rw _ _ _ _ m m1 PR1) in SP; rewrite ?HSPS; [| apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_nil].
eapply (htr_rw _ _ _ _ m m1 PR1) in LSH; cbn [cells_size csize Nat.add];
[| apply (acl_fshadow _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; lia| apply rng_out_nil].
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
assert (BITS1 : bits_rep bsegs m1 (x_F X + HO_BITS) (a_Dc a) (h_bits h)).
{ apply (bits_rep_tr _ _ _ _ m m1 PR1 _ _ _ BITS BOK); [| apply rng_out_nil| | apply rng_out_nil].
- apply (acl_frame _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_BITS; lia.
- apply (acl_live _ _ _ _ _ _ _ (INL _ (own_in_Dc a h))); lia. }
assert (OSR1 : h_os_rep X m1 a h).
{ apply (h_os_rep_tr _ _ _ _ m m1 PR1 X a h OSR).
- apply (acl_frame _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IB)); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IL)); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IG)); lia| apply rng_out_nil]. }
unfold HO_OY in SY.
assert (SY1 : sync_rep m1 (x_F X + 8480) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m m1 PR1 _ _ _ _ SY).
- apply (acl_frame _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_nil.
- intros NS. split; [| apply rng_out_nil]. pose proof (own_in_Dsy a h NS) as INS. unfold bptr in *.
apply (acl_live _ _ _ _ _ _ _ (INL _ INS)); lia. }
assert (DEC1 : h_dec_rep X m1 a h).
{ apply (h_dec_rep_tr _ _ _ _ m m1 PR1 X a h DEC). intros b Hb. split; [| apply rng_out_nil].
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E0); rewrite E0 in Hb; destruct Hb]).
apply (acl_live _ _ _ _ _ _ _ (INL _ (own_in_blk a h NS0 b Hb))); lia. }
clear BITS OSR SY DEC PR1 MU1 WM1.
pose proof (own_ne_Dsy a h NDO) as ONE.
destruct POST1 as [(NS0 & ->) | (ES0 & ->)].
-
pose proof DEC1 as DEC1'. unfold h_dec_rep in DEC1'. destruct (h_st h) as [d|] eqn:EST; [| destruct DEC1' as (ES & _); exfalso; exact (NS0 ES)].
destruct DEC1' as (R1 & SPOS & DEP & _ & _ & NDB & _ & NDc & LB19).
assert (NST : h_st h <> None) by (rewrite EST; discriminate).
assert (INB : forall b, In b (a_LBD a) -> In (blk_addr b, blk_size b) (rt_live RT Σ1)) by (intros b Hb; exact (INL _ (own_in_blk a h NST b Hb))).
pose proof (destroy_stack_le d) as DSL.
unfold A_destroy_h in Hc1.
Time cps_rt (DESTROY d Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (x_F X + HO_OUT) (x_F X + HO_STEREO) (a_S a) (x_lo X)
(a_LBD a)).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). exact STC1. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold RT_STACK, bptr in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). clear - S32. Z.div_mod_to_equations. lia. }
{ apply unwind_ok_ch. split; [cbn; rewrite unsigned_lit by lia; exact in_ras_9736c|].
left. rewrite !unsigned_lit by (unfold USTACK_TOP in *; lia). lia. }
intros cc2 (Σ2 & Hc2 & EL2 & EF2 & ES2 & EC2 & EP2). clear Hc1.
Time cps_unpack_lib Hc2 as (v2 & m2 & RS & RA2 & PR2).
destruct RS as (-> & ->).
destruct RA2 as (ART2 & MI2 & ST2).
rewrite EF in PR2.

assert (NBLK : forall p q, In (p, q) (h_own a h) -> (forall b, In b (a_LBD a) -> blk_addr b <> p) -> In (p, q) (rt_live RT Σ2)).
{ intros p q Hin NB. rewrite EL2. apply live_remove_list_keep; [exact (INL _ Hin)|]. cbn [fst]. intros Hb. apply in_map_iff in Hb as (b & E & Hb). exact (NB b Hb E). }
assert (NOSB : h_stream_init h <> 0 -> forall p, In p [a_Bd a; a_L a; a_G a] -> forall b, In b (a_LBD a) -> blk_addr b <> p).
{ intros NE p Hp b Hb E. pose proof NDO as ND1. unfold h_own in ND1. rewrite EST in ND1.
replace (h_stream_init h =? 0) with false in ND1 by (symmetry; apply Z.eqb_neq; exact NE).
rewrite !map_app in ND1. apply (nodup_app_disj _ _ p ND1); [unfold blocks_live; rewrite map_map, <- E; apply in_map; exact Hb|].
destruct Hp as [<-|[<-|[<-|[]]]]; cbn [map fst app]; [right; left| right; right; left| right; right; right; left]; reflexivity. }
assert (XL2 : forall e, In e (x_live X) -> In e (rt_live RT Σ2)).
{ intros [p q] He. rewrite EL2. apply live_remove_list_keep; [rewrite EL; apply in_or_app; right; exact He|].
cbn [fst]. intros Hb. apply in_map_iff in Hb as (b & E & Hb). exact (XNE _ _ (own_in_blk a h NST b Hb) (p, q) He (eq_sym E)). }
assert (PR2S : rt_pres_fp (rt_live RT Σ2) [(x_F X, 8%nat)] (x_S1 X) [] m1 m2).
{ apply (pres_fp_mono _ _ _ _ _ _ _ m1 m2 PR2); [intros e He; exact He| intros e He; exact He| lia]. }
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ2 m1 m2 a h _ _ HSP PR2S XL2 (fp_h_nil X a h) (AF_DRV _ _ ART2) PF1 ERR1 OUTR1 SSP1)
as (PF2 & ERR2 & OUTR2 & SSP2).
clear PR2S.
eapply (htr_rw _ _ _ _ m1 m2 PR2) in FR1; [| cbn [cl_frame cells_size csize Nat.add]; apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_nil].
eapply (htr_rw _ _ _ _ m1 m2 PR2) in SP; rewrite ?HSPS; [| apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_nil].
eapply (htr_rw _ _ _ _ m1 m2 PR2) in LSH; cbn [cells_size csize Nat.add];
[| apply (acl_fshadow _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; lia| apply rng_out_nil].
assert (BITS2 : bits_rep bsegs m2 (x_F X + HO_BITS) (a_Dc a) (h_bits h)).
{ apply (bits_rep_tr _ _ _ _ m1 m2 PR2 _ _ _ BITS1 BOK); [| apply rng_out_nil| | apply rng_out_nil].
- apply (acl_frame _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_BITS; lia.
- apply (acl_live _ _ _ _ _ _ _ (NBLK _ _ (own_in_Dc a h) NDc)); lia. }
assert (OSR2 : h_os_rep X m2 a h).
{ apply (h_os_rep_tr _ _ _ _ m1 m2 PR2 X a h OSR1).
- apply (acl_frame _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
split; [apply (acl_live _ _ _ _ _ _ _ (NBLK _ _ IB (NOSB NE _ (or_introl eq_refl)))); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (NBLK _ _ IL (NOSB NE _ (or_intror (or_introl eq_refl))))); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (NBLK _ _ IG (NOSB NE _ (or_intror (or_intror (or_introl eq_refl)))))); lia| apply rng_out_nil]. }
assert (SY2 : sync_rep m2 (x_F X + 8480) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m1 m2 PR2 _ _ _ _ SY1).
- apply (acl_frame _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_nil.
- intros NS. split; [| apply rng_out_nil]. pose proof (own_in_Dsy a h NS) as INS.
pose proof (proj2 (proj2 (ONE NS)) ltac:(discriminate)) as NBD. unfold bptr in *.
apply (acl_live _ _ _ _ _ _ _ (NBLK _ _ INS NBD)); lia. }
clear BITS1 OSR1 SY1 DEC1 PR2.

refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T cc2 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply cl_w2; [reflexivity | exact MI2]. }
intros ms3 cc3 -> Hc3. clear Hc.
apply (K_bd Σ2 m2 cc3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc3 FRM EL2); assumption.
-
assert (ELBD : a_LBD a = []).
{ unfold h_dec_rep in DEC1. destruct (h_st h) as [d|]; [destruct DEC1 as (_ & SPOS & _); lia| exact (proj2 DEC1)]. }
assert (EL1 : rt_live RT Σ1 = live_remove_list (map blk_addr (a_LBD a)) (rt_live RT Σ1)) by (rewrite ELBD; reflexivity).
apply (K_bd Σ1 m1 cc1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc1 FRM EL1); try reflexivity; assumption.
Qed.
End Clean.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Lemma live_remove_list_app : forall ps l1 l2, live_remove_list ps (l1 ++ l2) = live_remove_list ps l1 ++ live_remove_list ps l2.
Proof. induction ps as [|p ps IH]; intros l1 l2; [reflexivity|]. cbn [live_remove_list fold_right]. unfold live_remove_list in IH. rewrite IH. apply live_remove_app. Qed.
Lemma live_remove_list_all : forall ps l, (forall e, In e l -> In (fst e) ps) -> live_remove_list ps l = [].
Proof.
intros ps l H. destruct (live_remove_list ps l) as [|e l'] eqn:E; [reflexivity|]. exfalso.
assert (He : In e (live_remove_list ps l)) by (rewrite E; left; reflexivity).
pose proof (live_remove_list_sub _ _ _ He) as He1. pose proof (H e He1) as Hin.
clear E H He1. revert l He. induction ps as [|p ps IH]; intros l He; [destruct Hin|]. cbn [live_remove_list fold_right] in He.
apply live_remove_in in He as (He & NE). destruct Hin as [E|Hin]; [exact (NE (eq_sym E))| exact (IH Hin l He)].
Qed.
Lemma live_remove_list_none : forall ps l, (forall e, In e l -> ~ In (fst e) ps) -> live_remove_list ps l = l.
Proof.
induction ps as [|p ps IH]; intros l H; [reflexivity|]. cbn [live_remove_list fold_right]. unfold live_remove_list in IH.
rewrite IH by (intros e He Hin; apply (H e He); right; exact Hin). apply live_remove_none. intros e He E. apply (H e He). left. symmetry. exact E.
Qed.
Lemma live_remove_list_perm : forall ps l l', Permutation l l' -> Permutation (live_remove_list ps l) (live_remove_list ps l').
Proof. induction ps as [|p ps IH]; intros l l' P; [exact P|]. cbn [live_remove_list fold_right]. apply perm_live_remove. apply IH. exact P. Qed.

Lemma h_drep_head : forall OUT STEREO (m : mem) S (d : dec_state bptr) LBD, DREP OUT STEREO m S d LBD -> exists n, In (tt, S, n) LBD /\ 0 < n /\ S mod 8 = 0.
Proof.
intros OUT STEREO m S d LBD H. destruct d as [st|s low]; cbn [decst_rep] in H.
- destruct H as [-> NB]. exists NBSTATE_SIZEOF. destruct (nb_blk st). split; [left; reflexivity|]. split; [unfold NBSTATE_SIZEOF; lia| exact (proj1 NB)].
- destruct H as (a & j & LBL & -> & S8 & _). exists SBSTATE_SIZEOF. destruct (sbd_blk s) eqn:E. split; [left; cbn [sb_blocks]; rewrite E; reflexivity|].
split; [unfold SBSTATE_SIZEOF; lia| exact S8].
Qed.

Lemma in_ras_970b8 : In 0x97424 ALLOC_RAS.  Proof. unfold ALLOC_RAS. cbn [In]. tauto. Qed.
Lemma in_ras_970c0 : In 0x9742c ALLOC_RAS.  Proof. unfold ALLOC_RAS. cbn [In]. tauto. Qed.

Lemma destroy_stack_le : forall d, destroy_stack d <= 32 * Z.of_nat (dec_depth d) - 16.
Proof. induction d as [st|s low IH]; cbn [destroy_stack dec_depth]; [lia|]. rewrite Nat2Z.inj_succ. lia. Qed.

Section Clean.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis DESTROY : forall d, destroy_cps_at RT d.
Hypothesis BDES : speex_bits_destroy_cps RT.
Hypothesis SCLR : ogg_stream_clear_cps RT.
Hypothesis YCLR : ogg_sync_clear_cps RT.
Variable X : hinv.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.

Theorem h_clean_ok : h_clean_cps RT OUT_rep ERR_rep IO_FP X F0 fs0.
Proof using AF ERR_loc OUT_loc IO_img AF_DRV DESTROY BDES SCLR YCLR.
intros HX h T c Hc Hk.
destruct Hc as (Σ1 & a & Fx & fc & m & ra & t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & r5 & r8 & t3 & t4 & t5 & t6 & v80 & v88 & v144 & v176 & j0 & j192 & j200
& ogc & opc & Hc & FRM & HS & HR & OGJ & OPJ).
pose proof (own_pos RT OUT_rep ERR_rep IO_FP X Σ1 m a h _ _ _ HR) as OPOS.
destruct HR as (ART1 & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & _ & _ & _ & BITS & SY & _ & _ & OSR & _ & _ & _ & DEC & HP).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART1 HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
unfold h_regs in Hc. unfold h_spill in SP.

destruct (stk_carve asegs m (x_lo X) (x_S1 X) 48 ST ltac:(lia)) as (STC & (jf & JF)).
replace (x_S1 X - Z.of_nat 48) with (x_S1 X + -48) in STC, JF by lia.
destruct (cl_frame_of_CB m (x_S1 X + -48) jf JF) as (c0 & c1 & c2 & c3 & c4 & c5 & FR). clear JF.
assert (SR0 : 0 <= a_S a < 2^63).
{ pose proof DEC as DEC0. unfold h_dec_rep in DEC0. destruct (h_st h) as [d|] eqn:EST; [| destruct DEC0 as (-> & _); lia].
destruct DEC0 as (R & _). destruct (h_drep_head _ _ _ _ _ _ R) as (n & INB & N0 & _).
assert (NS : h_st h <> None) by (rewrite EST; discriminate).
pose proof (own_in_blk a h NS _ INB) as INO. cbn [blk_addr blk_size] in INO.
destruct (proj1 HSP _ _ INO) as (P0 & PL & _). cbn [blk_addr blk_size fst snd] in P0, PL. unfold USTACK_TOP in *. lia. }

set (ADDR_OK := fun (ps : list Z) => (forall e, In e (h_own a h) -> fst e <> a_Dsy a \/ sy_data (h_oy h) = None -> In (fst e) ps)
/\ (forall e, In e (x_live X) -> ~ In (fst e) ps)
/\ (sy_data (h_oy h) <> None -> ~ In (a_Dsy a) ps)).
assert (K_ep : forall (Σ4 : rts RT) (m4 : mem) (cc4 : config) (ps : list Z)
(ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' : word) Fr' fc',
ASTA RT Σ4 (PMfd F0 fs0) (eq (MS (mkR ra' (Z64 (x_S1 X + -48)) (x_gp X) (Z64 6489176) t0' t1' t2' (Z64 (x_F X + 8480)) s1' a0' a1' a2' a3' a4' a5' a6' a7'
s2' s3' (Z64 (x_F X + HO_OUT)) r5 (Z64 (h_packet_count h)) (Z64 (x_F X + HO_OS)) r8 (Z64 (a_S a))
(Z64 (x_F X + HO_OG)) (Z64 (x_F X + HO_BITS)) t3' t4' t5' t6') Fr' (Z64 0x97438) fc' None m4 (seg_rom asegs))) cc4 ->
X1cn.frm0 fc' -> ADDR_OK ps ->
rt_live RT Σ4 = live_remove_list ps (rt_live RT Σ1) -> rt_frames RT Σ4 = rt_frames RT Σ1 -> rt_sp0 RT Σ4 = rt_sp0 RT Σ1 ->
rt_credit RT Σ4 = rt_credit RT Σ1 -> rt_pois RT Σ4 = rt_pois RT Σ1 ->
ART RT Σ4 m4 -> mem_inv asegs m4 -> stk asegs m4 (x_lo X) (x_S1 X + -48) ->
rw_cells asegs m4 (x_S1 X + -48) (cl_frame c0 (Z64 (x_sf X)) (Z64 (x_F X + HO_OP)) (Z64 (x_S1 X)) (Z64 (x_usp X)) (Z64 0x971b0)) ->
rt_pres_fp (x_live X) [(x_F X, 8%nat)] (x_S1 X) (h_WL IO_FP X) (x_mR X) m4 -> ERR_rep m4 -> (forall so, OUT_rep so (x_mR X) -> OUT_rep so m4) -> io_ssp m4 ->
rw_cells asegs m4 (x_S1 X) (hsp j0 (Z64 (x_F X + 64)) (Z64 (x_F X + 48)) (Z64 (x_sf X + 16)) (Z64 (x_F X)) (Z64 (x_F X)) (Z64 (x_F X + HO_LOOK))
(Z64 (x_F X + HO_RATE)) (Z64 (x_F X + HO_ENH)) (Z64 (x_d X)) v80 v88 (Z64 SHB) (Z64 (h_granule_frame_size h))
(Z64 (h_extra_headers h)) (Z64 (x_F X + HO_OY)) (Z64 (h_eos h)) (Z64 (h_nframes h)) v144 (Z64 (x_F X + HO_OS))
(Z64 (x_F X + HO_STEREO)) (Z64 (x_F X + HO_FSZ)) v176 (Z64 (h_channels h)) j192 j200 (Z64 (x_F X))) ->
rw_cells asegs m4 (x_sf X) [CB 16 HSH_P1] ->
sync_rep m4 (x_F X + 8480) (a_Dsy a) (h_oy h) (a_sybytes a) ->
realizes asegs cc4 T).
{ intros Σ4 m4 cc4 ps ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' t3' t4' t5' t6' Fr' fc' Hc4 FRM4 (PS1 & PS2 & PS3) EL4 EF4 ES4 EC4 EP4
ART4 MI4 ST4 FR4 PF4 ERR4 OUTR4 SSP4 SP4 LSH4 SY4. clear Hc.
refine (rz_evt RT AF Σ4 (PMfd F0 fs0) _ _ T cc4 (PMfd_mat_stable F0 fs0) Hc4 _ _).
{ eapply cl_epi; [unfold USTACK_TOP in *; lia | exact FR4 | exact MI4]. }
intros ms5 cc5 -> Hc5. clear Hc4.
pose proof (stk_release asegs m4 (x_lo X) (x_S1 X + -48) _ ST4 FR4 ltac:(lia)) as ST4'. cbn [cells_size cl_frame csize Nat.add] in ST4'.
replace (x_S1 X + -48 + Z.of_nat 48) with (x_S1 X) in ST4' by lia.
assert (INF4 : In (x_F X, 8%nat) (rt_frames RT Σ4)) by (rewrite EF4, EF; left; reflexivity).
assert (SYL4 : sy_data (h_oy h) <> None -> In (a_Dsy a, sy_storage (h_oy h)) (rt_live RT Σ4)).
{ intros NS. rewrite EL4. apply live_remove_list_keep; [| exact (PS3 NS)].
rewrite EL. apply in_or_app. left. exact (Permutation_in _ (Permutation_sym PERM) (own_in_Dsy a h NS)). }
unfold A_sync_clear_h in Hc5.
Time cps_rt (YCLR Σ4 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 (x_F X + 8480) (a_Dsy a) (x_F X) (x_lo X) 8%nat
(h_oy h) (a_sybytes a)).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ change (fs_size 8) with 16384. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). exact ST4'. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold RT_STACK. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). clear - S32. Z.div_mod_to_equations. lia. }
intros cc6 (Σ5 & Hc6 & EL5 & EF5 & ES5 & EC5 & EP5). clear Hc5.
Time cps_unpack_lib Hc6 as (m5 & RS & RA5 & PR5 & SY5).
destruct RS as (-> & ->).
destruct RA5 as (ART5 & MI5 & ST5).

refine (rz_evt RT AF Σ5 (PMfd F0 fs0) _ _ T cc6 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply cl_w5; [reflexivity | exact MI5]. }
intros ms7 cc7 -> Hc7. clear Hc.

assert (XD : sy_data (h_oy h) <> None -> forall e, In e (x_live X) -> fst e <> a_Dsy a).
{ intros NS [q k] Hq E. cbn [fst] in E. subst q.
assert (INS : In (a_Dsy a, sy_storage (h_oy h)) (h_own a h)) by (apply own_in_Dsy; exact NS).
destruct (proj1 HSP _ _ INS) as (_ & _ & _ & _ & _ & SEP). pose proof (OPOS _ _ INS) as P1.
pose proof (proj1 (hi_live _ _ _ HX) _ _ Hq) as P2. destruct (SEP _ _ Hq); lia. }
assert (XIN : forall e, In e (x_live X) -> In e (sync_clear_live (h_oy h) (a_Dsy a) (rt_live RT Σ4))).
{ intros e He. assert (He4 : In e (rt_live RT Σ4)).
{ rewrite EL4. apply live_remove_list_keep; [rewrite EL; apply in_or_app; right; exact He| exact (PS2 e He)]. }
unfold sync_clear_live, bptr. destruct (sy_data (h_oy h)) eqn:ED; [| exact He4].
apply live_remove_keep; [exact He4| apply XD; [discriminate| exact He]]. }
assert (ELX : rt_live RT Σ5 = x_live X).
{ rewrite EL5, EL4, EL. unfold sync_clear_live, bptr. destruct (sy_data (h_oy h)) eqn:ED.
- change (live_remove (a_Dsy a) (live_remove_list ps (a_P a ++ x_live X))) with (live_remove_list (a_Dsy a :: ps) (a_P a ++ x_live X)).
rewrite live_remove_list_app, live_remove_list_all, live_remove_list_none; [reflexivity| |].
+ intros e He [E|Hin]; [exact (XD ltac:(discriminate) e He (eq_sym E))| exact (PS2 e He Hin)].
+ intros e He. pose proof (Permutation_in _ PERM He) as Ho. destruct (Z.eq_dec (fst e) (a_Dsy a)) as [E|NE]; [left; symmetry; exact E|].
right. apply PS1; [exact Ho| left; exact NE].
- rewrite live_remove_list_app, live_remove_list_all, live_remove_list_none; [reflexivity| exact PS2 |].
intros e He. apply PS1; [exact (Permutation_in _ PERM He)| right; reflexivity]. }
rewrite EF4, EF in PR5.
assert (FPH : fp_h X a h [(x_F X + 8480, x_F X + 8480 + 32)]) by (apply fp_h_cons; [right; right; left; lia| apply fp_h_nil]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ4 m4 m5 a h _ _ HSP PR5 XIN FPH (AF_DRV _ _ ART5) PF4 ERR4 OUTR4 SSP4)
as (PF5 & ERR5 & OUTR5 & _).
assert (INF : In (x_F X, 8%nat) [(x_F X, 8%nat)]) by (left; reflexivity).
assert (HSPS : forall w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208,
cells_size (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208) = 216%nat)
by reflexivity.
eapply (htr_rw _ _ _ _ m4 m5 PR5) in SP4; rewrite ?HSPS; [| apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_cons; [lia| apply rng_out_nil]].
eapply (htr_rw _ _ _ _ m4 m5 PR5) in LSH4; cbn [cells_size csize Nat.add];
[| apply (acl_fshadow _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; lia| apply rng_out_cons; [lia| apply rng_out_nil]].

assert (HCR : h_cost h <= FUZZ_COST - 1).
{ destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PC & _ & _ & _ & B & _ & P1 & P2 & _ & _ & _ & _ & P7 & _).
pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold h_cost, h_consumed, h_pend, H_HDR_CREDIT, H_DEC_CREDIT, FUZZ_COST, MAX_FUZZ_SIZE in *. lia. }
apply Hk. unfold at_XT.
exists Σ5, Fr', fc', m5, (Z64 618928), r, r0, r1, (Z64 0), r2, r3, r4, r6, r7, r9, r10, (Z64 (x_F X + HO_OP)), (Z64 (x_F X + HO_OUT)), r5, (Z64 (h_packet_count h)),
(Z64 (x_F X + HO_OS)), r8, (Z64 (a_S a)), (Z64 (x_F X + HO_OG)), (Z64 (x_F X + HO_BITS)), r11, r12, r13, r14.
exists j0, (Z64 (x_F X + 64)), (Z64 (x_F X + 48)), (Z64 (x_F X + HO_LOOK)), (Z64 (x_F X + HO_RATE)), (Z64 (x_F X + HO_ENH)), v80, v88,
(Z64 (h_granule_frame_size h)), (Z64 (h_extra_headers h)), (Z64 (x_F X + HO_OY)), (Z64 (h_eos h)), (Z64 (h_nframes h)), v144, (Z64 (x_F X + HO_OS)),
(Z64 (x_F X + HO_STEREO)), (Z64 (x_F X + HO_FSZ)), v176, (Z64 (h_channels h)), j192, j200.
split; [exact Hc7|]. split; [exact FRM4|]. split; [exact ELX|]. split; [rewrite EF5, EF4; exact EF|]. split; [rewrite ES5, ES4; exact ESP|].
split; [rewrite EP5, EP4; exact EPO0|]. split; [rewrite EC5, EC4; lia|].
split; [exact ART5|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact PF5|]. split; [exact ERR5|]. split; [exact OUTR5|].
split; [exact SP4| exact LSH4]. }

assert (BSH_OF : forall m', rt_pres_fp (x_live X) [(x_F X, 8%nat)] (x_S1 X) (h_WL IO_FP X) (x_mR X) m' -> ro_cells asegs m' (shad (x_F X + 8400)) bits_shadow).
{ intros m' PF'. pose proof (h_shr_at OUT_rep IO_FP IO_img X HX m' PF') as B. destruct B as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
pose proof (bytes_at_sub m' (x_sf X + 16) HSH_R 1034 6 B ltac:(vm_compute; lia)) as B6.
assert (E6 : firstn 6 (skipn 1034 HSH_R) = repeat (Z_to_bv 8 0) 6) by (vm_compute; reflexivity).
rewrite E6 in B6. replace (x_sf X + 16 + Z.of_nat 1034) with (x_sf X + 1050) in B6 by (change (Z.of_nat 1034) with 1034; lia).
assert (ESB : shad (x_F X + 8400) = x_sf X + 1050)
by (rewrite (shad_aligned_add (x_F X) 8400 ltac:(clear - F64; Z.div_mod_to_equations; lia) ltac:(lia)), <- ESF; change (8400 / 8) with 1050; reflexivity).
rewrite ESB. unfold bits_shadow. split; [cbn; tauto|]. cbn [cells_bytes cbytes map repeat app]. exact B6. }

assert (XNE : forall p q, In (p, q) (h_own a h) -> forall e, In e (x_live X) -> fst e <> p).
{ intros p q Hin [q' k] Hq E. cbn [fst] in E. subst q'.
destruct (proj1 HSP _ _ Hin) as (_ & _ & _ & _ & _ & SEP). pose proof (OPOS _ _ Hin) as P1.
pose proof (proj1 (hi_live _ _ _ HX) _ _ Hq) as P2. destruct (SEP _ _ Hq); lia. }
pose proof (proj2 (proj2 HSP)) as NDO.
assert (ADDR : forall ps, (forall p, In p ps -> exists q, In (p, q) (h_own a h) /\ (sy_data (h_oy h) <> None -> p <> a_Dsy a)) ->
In (a_Dc a) ps -> (h_st h <> None -> forall b, In b (a_LBD a) -> In (blk_addr b) ps) ->
(h_stream_init h <> 0 -> In (a_Bd a) ps /\ In (a_L a) ps /\ In (a_G a) ps) -> ADDR_OK ps).
{ intros ps PSO PDc PBL PST. split; [| split].
- intros [p q] Hin Hcase. cbn [fst] in Hcase |- *. unfold h_own in Hin. apply in_app_or in Hin as [Hin|Hin].
+ destruct (h_st h) as [d|] eqn:EST; [| destruct Hin]. unfold blocks_live in Hin. apply in_map_iff in Hin as (b & E & Hb). injection E as <- <-.
apply PBL; [first [discriminate | rewrite EST; discriminate]| exact Hb].
+ apply in_app_or in Hin as [[E|[]]|Hin]; [injection E as <- <-; exact PDc|].
apply in_app_or in Hin as [Hin|Hin].
* destruct (h_stream_init h =? 0) eqn:E0; [destruct Hin|]. apply Z.eqb_neq in E0.
destruct (PST E0) as (PB & PL & PG). destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; assumption.
* destruct (sy_data (h_oy h)) eqn:ED; [| destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
destruct Hcase as [NE|E]; [contradiction| discriminate].
- intros e He Hin. destruct (PSO _ Hin) as (q & Hq & _). exact (XNE _ _ Hq e He eq_refl).
- intros NS Hin. destruct (PSO _ Hin) as (q & Hq & NE). exact (NE NS eq_refl). }
assert (K_bd : forall (Σ2 : rts RT) (m2 : mem) (cc2 : config) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) Fr' fc',
ASTA RT Σ2 (PMfd F0 fs0) (eq (MS (mkR (Z64 0x9742c) (Z64 (x_S1 X + -48)) (x_gp X) (Z64 6489176) t0' t1' t2' (Z64 (x_F X + 8480)) (Z64 (x_F X + HO_OS))
(Z64 (x_F X + HO_BITS)) a1' a2' a3' a4' a5' a6' a7' (Z64 (h_stream_init h)) (Z64 (x_F X + HO_BITS))
(Z64 (x_F X + HO_OUT)) r5 (Z64 (h_packet_count h)) (Z64 (x_F X + HO_OS)) r8 (Z64 (a_S a))
(Z64 (x_F X + HO_OG)) (Z64 (x_F X + HO_BITS)) t3' t4' t5' t6') Fr' (Z64 A_bits_destroy_h) fc' None m2 (seg_rom asegs))) cc2 ->
X1cn.frm0 fc' ->
rt_live RT Σ2 = live_remove_list (map blk_addr (a_LBD a)) (rt_live RT Σ1) -> rt_frames RT Σ2 = rt_frames RT Σ1 -> rt_sp0 RT Σ2 = rt_sp0 RT Σ1 ->
rt_credit RT Σ2 = rt_credit RT Σ1 -> rt_pois RT Σ2 = rt_pois RT Σ1 ->
ART RT Σ2 m2 -> mem_inv asegs m2 -> stk asegs m2 (x_lo X) (x_S1 X + -48) ->
rw_cells asegs m2 (x_S1 X + -48) (cl_frame c0 (Z64 (x_sf X)) (Z64 (x_F X + HO_OP)) (Z64 (x_S1 X)) (Z64 (x_usp X)) (Z64 0x971b0)) ->
rt_pres_fp (x_live X) [(x_F X, 8%nat)] (x_S1 X) (h_WL IO_FP X) (x_mR X) m2 -> ERR_rep m2 -> (forall so, OUT_rep so (x_mR X) -> OUT_rep so m2) -> io_ssp m2 ->
rw_cells asegs m2 (x_S1 X) (hsp j0 (Z64 (x_F X + 64)) (Z64 (x_F X + 48)) (Z64 (x_sf X + 16)) (Z64 (x_F X)) (Z64 (x_F X)) (Z64 (x_F X + HO_LOOK))
(Z64 (x_F X + HO_RATE)) (Z64 (x_F X + HO_ENH)) (Z64 (x_d X)) v80 v88 (Z64 SHB) (Z64 (h_granule_frame_size h))
(Z64 (h_extra_headers h)) (Z64 (x_F X + HO_OY)) (Z64 (h_eos h)) (Z64 (h_nframes h)) v144 (Z64 (x_F X + HO_OS))
(Z64 (x_F X + HO_STEREO)) (Z64 (x_F X + HO_FSZ)) v176 (Z64 (h_channels h)) j192 j200 (Z64 (x_F X))) ->
rw_cells asegs m2 (x_sf X) [CB 16 HSH_P1] ->
bits_rep asegs m2 (x_F X + HO_BITS) (a_Dc a) (h_bits h) -> h_os_rep X m2 a h ->
sync_rep m2 (x_F X + 8480) (a_Dsy a) (h_oy h) (a_sybytes a) ->
realizes asegs cc2 T).
{ intros Σ2 m2 cc2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Fr' fc' Hc2 FRM2 EL2 EF2 ES2 EC2 EP2 ART2 MI2 ST2 FR2 PF2 ERR2 OUTR2 SSP2 SP2 LSH2
BITS2 OSR2 SY2. clear Hc.
assert (INF2 : In (x_F X, 8%nat) (rt_frames RT Σ2)) by (rewrite EF2, EF; left; reflexivity).
assert (INDc : In (a_Dc a, sb_buf_size (h_bits h)) (rt_live RT Σ2)).
{ rewrite EL2. apply live_remove_list_keep; [rewrite EL; apply in_or_app; left; exact (Permutation_in _ (Permutation_sym PERM) (own_in_Dc a h))|].
cbn [fst]. intros Hin. apply in_map_iff in Hin as (b & E & Hb). unfold h_dec_rep in DEC. destruct (h_st h) as [d|]; [| destruct DEC as (_ & E0); rewrite E0 in Hb; destruct Hb].
destruct DEC as (_ & _ & _ & _ & _ & _ & _ & NDc & _). exact (NDc b Hb E). }
unfold HO_BITS in BITS2. unfold A_bits_destroy_h in Hc2.
Time cps_rt (BDES Σ2 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 (x_F X + 8400) (a_Dc a) (x_F X) (x_lo X) 8%nat (h_bits h)).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ destruct HP as (_ & _ & _ & _ & B & _). exact B. }
{ destruct HP as (_ & _ & _ & _ & _ & B & _). exact B. }
{ exact (BSH_OF m2 PF2). }
{ change (fs_size 8) with 16384. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). exact ST2. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold RT_STACK. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). clear - S32. Z.div_mod_to_equations. lia. }
{ apply unwind_ok_ch. split; [cbn; rewrite unsigned_lit by lia; exact in_ras_970c0|].
left. rewrite !unsigned_lit by (unfold USTACK_TOP in *; lia). lia. }
intros cc3 (Σ3 & Hc3 & EL3 & EF3 & ES3 & EC3 & EP3). clear Hc2.
Time cps_unpack_lib Hc3 as (v3 & m3 & RS & RA3 & PR3).
destruct RS as (-> & ->).
destruct RA3 as (ART3 & MI3 & ST3).
rewrite EF2, EF in PR3.
assert (INL2 : forall p q, In (p, q) (h_own a h) -> ~ In p (map blk_addr (a_LBD a)) -> p <> a_Dc a -> In (p, q) (rt_live RT Σ3)).
{ intros p q Hin NB NE. rewrite EL3, EL2. apply live_remove_keep; [| exact NE]. apply live_remove_list_keep; [| exact NB].
rewrite EL. apply in_or_app. left. exact (Permutation_in _ (Permutation_sym PERM) Hin). }

assert (NOS : h_stream_init h <> 0 -> forall p, In p [a_Bd a; a_L a; a_G a] -> ~ In p (map blk_addr (a_LBD a)) /\ p <> a_Dc a).
{ intros NE p Hp. pose proof NDO as ND1. unfold h_own in ND1. replace (h_stream_init h =? 0) with false in ND1 by (symmetry; apply Z.eqb_neq; exact NE).
rewrite !map_app in ND1. cbn [map fst] in ND1.
split.
- intros Hb. unfold h_dec_rep in DEC. destruct (h_st h) as [d|] eqn:EST; [| destruct DEC as (_ & E0); rewrite E0 in Hb; destruct Hb].
apply (nodup_app_disj _ _ p ND1); [unfold blocks_live; rewrite map_map; exact Hb|].
destruct Hp as [<-|[<-|[<-|[]]]]; rewrite ?in_app_iff; cbn; tauto.
- intros E. subst p. apply NoDup_app_remove_l in ND1. apply NoDup_cons_iff in ND1 as (N1 & _). apply N1.
destruct Hp as [E|[E|[E|[]]]]; rewrite ?in_app_iff; cbn; rewrite <- E; tauto. }
pose proof (own_ne_Dsy a h NDO) as ONE.
assert (NDsy : sy_data (h_oy h) <> None -> ~ In (a_Dsy a) (map blk_addr (a_LBD a)) /\ a_Dsy a <> a_Dc a).
{ intros NS. destruct (ONE NS) as (N1 & _ & N3). split; [| congruence].
intros Hb. apply in_map_iff in Hb as (b & E & Hb).
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E0); rewrite E0 in Hb; destruct Hb]).
exact (N3 NS0 b Hb E). }
assert (XL3 : forall e, In e (x_live X) -> In e (rt_live RT Σ3)).
{ intros [p q] He. rewrite EL3, EL2. apply live_remove_keep; [apply live_remove_list_keep|].
- rewrite EL. apply in_or_app. right. exact He.
- cbn [fst]. intros Hb. apply in_map_iff in Hb as (b & E & Hb).
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E0); rewrite E0 in Hb; destruct Hb]).
exact (XNE _ _ (own_in_blk a h NS0 b Hb) (p, q) He (eq_sym E)).
- cbn [fst]. exact (XNE _ _ (own_in_Dc a h) (p, q) He). }
assert (PR3S : rt_pres_fp (rt_live RT Σ3) [(x_F X, 8%nat)] (x_S1 X) [] m2 m3).
{ apply (pres_fp_mono _ _ _ _ _ _ _ m2 m3 PR3); [intros e He; exact He| intros e He; exact He| lia]. }
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ3 m2 m3 a h _ _ HSP PR3S XL3 (fp_h_nil X a h) (AF_DRV _ _ ART3) PF2 ERR2 OUTR2 SSP2)
as (PF3 & ERR3 & OUTR3 & SSP3).
assert (INF : In (x_F X, 8%nat) [(x_F X, 8%nat)]) by (left; reflexivity).
assert (HSPS : forall w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208,
cells_size (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208) = 216%nat)
by reflexivity.
eapply (htr_rw _ _ _ _ m2 m3 PR3) in FR2; [| cbn [cl_frame cells_size csize Nat.add]; apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_nil].
eapply (htr_rw _ _ _ _ m2 m3 PR3) in SP2; rewrite ?HSPS; [| apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_nil].
eapply (htr_rw _ _ _ _ m2 m3 PR3) in LSH2; cbn [cells_size csize Nat.add];
[| apply (acl_fshadow _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; lia| apply rng_out_nil].
assert (OSR3 : h_os_rep X m3 a h).
{ apply (h_os_rep_tr _ _ _ _ m2 m3 PR3 X a h OSR2).
- apply (acl_frame _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
destruct (NOS NE (a_Bd a) (or_introl eq_refl)) as (B1 & B2). destruct (NOS NE (a_L a) (or_intror (or_introl eq_refl))) as (L1 & L2).
destruct (NOS NE (a_G a) (or_intror (or_intror (or_introl eq_refl)))) as (G1 & G2).
split; [apply (acl_live _ _ _ _ _ _ _ (INL2 _ _ IB B1 B2)); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (INL2 _ _ IL L1 L2)); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (INL2 _ _ IG G1 G2)); lia| apply rng_out_nil]. }
assert (SY3 : sync_rep m3 (x_F X + 8480) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m2 m3 PR3 _ _ _ _ SY2).
- apply (acl_frame _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_nil.
- intros NS. destruct (NDsy NS) as (N1 & N2). split; [| apply rng_out_nil].
apply (acl_live _ _ _ _ _ _ _ (INL2 _ _ (own_in_Dsy a h NS) N1 N2)); unfold bptr in *; lia. }
clear OSR2 SY2 BITS2 PR3S.

assert (SIR : 0 <= h_stream_init h < 2^63) by (destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S & _); destruct S as [S|S]; rewrite S; lia).
refine (rz_evt RT AF Σ3 (PMfd F0 fs0) _ _ T cc3 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply cl_w3; [reflexivity | exact SIR | exact MI3]. }
intros ms4 cc4 POST4 Hc4. clear Hc. cbv beta in POST4.

assert (PSO_blk : forall p, In p (map blk_addr (a_LBD a)) -> exists q, In (p, q) (h_own a h) /\ (sy_data (h_oy h) <> None -> p <> a_Dsy a)).
{ intros p Hp. apply in_map_iff in Hp as (b & <- & Hb).
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E0); rewrite E0 in Hb; destruct Hb]).
exists (blk_size b). split; [exact (own_in_blk a h NS0 b Hb)|]. intros NS. exact (proj2 (proj2 (ONE NS)) NS0 b Hb). }
assert (PSO_Dc : exists q, In (a_Dc a, q) (h_own a h) /\ (sy_data (h_oy h) <> None -> a_Dc a <> a_Dsy a)).
{ exists (sb_buf_size (h_bits h)). split; [exact (own_in_Dc a h)| intros NS; exact (proj1 (ONE NS))]. }
destruct POST4 as [(NE4 & ->) | (E4 & ->)].
-
pose proof OSR3 as OSR3'. unfold h_os_rep in OSR3'. replace (h_stream_init h =? 0) with false in OSR3' by (symmetry; apply Z.eqb_neq; exact NE4).
destruct OSR3' as (OSC & LSH0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & LS0 & BS0 & BL & BG & LG).
destruct (own_in_os a h NE4) as (IB & IL & IG).
destruct (NOS NE4 (a_Bd a) (or_introl eq_refl)) as (B1 & B2). destruct (NOS NE4 (a_L a) (or_intror (or_introl eq_refl))) as (L1 & L2).
destruct (NOS NE4 (a_G a) (or_intror (or_intror (or_introl eq_refl)))) as (G1 & G2).
assert (SLV : stream_live RT Σ3 (h_os h) (a_Bd a) (a_L a) (a_G a)).
{ split; [exact (INL2 _ _ IB B1 B2)|]. split; [exact (INL2 _ _ IL L1 L2)|]. split; [exact (INL2 _ _ IG G1 G2)|]. split; [exact BL|]. split; [exact BG| exact LG]. }
pose proof (h_acc_at OUT_rep IO_FP IO_img X HX m3 PF3) as (_ & _ & _ & _ & _ & _ & ACOS & _).
assert (INF3 : In (x_F X, 8%nat) (rt_frames RT Σ3)) by (rewrite EF3, EF2, EF; left; reflexivity).
unfold HO_OS in OSC, ACOS. unfold A_stream_clear_h in Hc4.
Time cps_rt (SCLR Σ3 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 (x_F X + 8688) (a_Bd a) (a_L a) (a_G a) (x_F X) (x_lo X) 8%nat
(h_os h) (a_shdr a)).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ unfold bptr in *. lia. }
{ unfold bptr in *. lia. }
{ change (fs_size 8) with 16384. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). exact ST3. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold RT_STACK. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). clear - S32. Z.div_mod_to_equations. lia. }
intros cc5 (Σ4 & Hc5 & EL4 & EF4 & ES4 & EC4 & EP4). clear Hc4.
Time cps_unpack_lib Hc5 as (m4 & RS & RA4 & PR4 & OSC4).
destruct RS as (-> & ->).
destruct RA4 as (ART4 & MI4 & ST4).
rewrite EF3, EF2, EF in PR4.
assert (XL4 : forall e, In e (x_live X) -> In e (live_remove (a_G a) (live_remove (a_L a) (live_remove (a_Bd a) (rt_live RT Σ3))))).
{ intros e He. apply live_remove_keep; [apply live_remove_keep; [apply live_remove_keep; [exact (XL3 e He)|]|]|].
- exact (XNE _ _ IB e He). - exact (XNE _ _ IL e He). - exact (XNE _ _ IG e He). }
assert (PR4S : rt_pres_fp (live_remove (a_G a) (live_remove (a_L a) (live_remove (a_Bd a) (rt_live RT Σ3)))) [(x_F X, 8%nat)] (x_S1 X)
[(x_F X + 8688, x_F X + 8688 + 408)] m3 m4).
{ apply (pres_fp_mono _ _ _ _ _ _ _ m3 m4 PR4); [intros e He; exact He| intros e He; exact He| lia]. }
assert (FPH4 : fp_h X a h [(x_F X + 8688, x_F X + 8688 + 408)]) by (apply fp_h_cons; [right; right; left; lia| apply fp_h_nil]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ4 m3 m4 a h _ _ HSP PR4S XL4 FPH4 (AF_DRV _ _ ART4) PF3 ERR3 OUTR3 SSP3)
as (PF4 & ERR4 & OUTR4 & SSP4).
clear PR4S.
eapply (htr_rw _ _ _ _ m3 m4 PR4) in FR2; [| cbn [cl_frame cells_size csize Nat.add]; apply acl_stack; unfold USTACK_TOP in *; lia|
apply rng_out_cons; [cbn [cl_frame cells_size csize Nat.add]; lia| apply rng_out_nil]].
eapply (htr_rw _ _ _ _ m3 m4 PR4) in SP2; rewrite ?HSPS; [| apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_cons; [lia| apply rng_out_nil]].
eapply (htr_rw _ _ _ _ m3 m4 PR4) in LSH2; cbn [cells_size csize Nat.add];
[| apply (acl_fshadow _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; lia| apply rng_out_cons; [lia| apply rng_out_nil]].
assert (SY4 : sync_rep m4 (x_F X + 8480) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m3 m4 PR4 _ _ _ _ SY3).
- apply (acl_frame _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia| apply rng_out_nil].
- intros NS. destruct (NDsy NS) as (N1 & N2). destruct ((proj1 (proj2 (ONE NS))) NE4) as (NB & NL & NG).
pose proof (own_in_Dsy a h NS) as INS. unfold bptr in *. split.
+ apply (acl_live _ _ _ (a_Dsy a) (sy_storage (h_oy h))); [| lia| lia].
apply live_remove_keep; [apply live_remove_keep; [apply live_remove_keep; [exact (INL2 _ _ INS N1 N2)|]|]|]; cbn [fst]; congruence.
+ apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ INS); lia| apply rng_out_nil]. }
clear SY3 PR4.
replace (ret_pc (Z64 619576)) with (Z64 0x97438) in Hc by (symmetry; apply ret_pc_even; [lia| reflexivity]).
apply (K_ep Σ4 m4 cc5 ([a_G a; a_L a; a_Bd a; a_Dc a] ++ map blk_addr (a_LBD a)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr' fc' Hc FRM2).
{ apply ADDR.
- intros p Hp. cbn [app In] in Hp. destruct Hp as [<-|[<-|[<-|[<-|Hp]]]].
+ exists (8 * os_lacing_storage (h_os h)). split; [exact IG| intros NS; exact (proj2 (proj2 ((proj1 (proj2 (ONE NS))) NE4)))].
+ exists (4 * os_lacing_storage (h_os h)). split; [exact IL| intros NS; exact (proj1 (proj2 ((proj1 (proj2 (ONE NS))) NE4)))].
+ exists (os_body_storage (h_os h)). split; [exact IB| intros NS; exact (proj1 ((proj1 (proj2 (ONE NS))) NE4))].
+ exact PSO_Dc.
+ exact (PSO_blk p Hp).
- right; right; right; left; reflexivity.
- intros _ b Hb. right; right; right; right. apply in_map. exact Hb.
- intros _. split; [right; right; left; reflexivity|]. split; [right; left; reflexivity| left; reflexivity]. }
{ rewrite EL4, EL3, EL2. reflexivity. }
{ rewrite EF4, EF3, EF2. reflexivity. }
{ rewrite ES4, ES3, ES2. reflexivity. }
{ rewrite EC4, EC3, EC2. reflexivity. }
{ rewrite EP4, EP3, EP2. reflexivity. }
{ exact ART4. }
{ exact MI4. }
{ exact ST4. }
{ exact FR2. }
{ exact PF4. }
{ exact ERR4. }
{ exact OUTR4. }
{ exact SSP4. }
{ exact SP2. }
{ exact LSH2. }
{ exact SY4. }
-
apply (K_ep Σ3 m3 cc4 (a_Dc a :: map blk_addr (a_LBD a)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr' fc' Hc4 FRM2).
{ apply ADDR.
- intros p Hp. destruct Hp as [<-|Hp]; [exact PSO_Dc| exact (PSO_blk p Hp)].
- left; reflexivity.
- intros _ b Hb. right. apply in_map. exact Hb.
- intros NE. exfalso. exact (NE E4). }
{ rewrite EL3, EL2. reflexivity. }
{ rewrite EF3, EF2. reflexivity. }
{ rewrite ES3, ES2. reflexivity. }
{ rewrite EC3, EC2. reflexivity. }
{ rewrite EP3, EP2. reflexivity. }
{ exact ART3. }
{ exact MI3. }
{ exact ST3. }
{ exact FR2. }
{ exact PF3. }
{ exact ERR3. }
{ exact OUTR3. }
{ exact SSP3. }
{ exact SP2. }
{ exact LSH2. }
{ exact SY3. } }

refine (rz_evt RT AF Σ1 (PMfd F0 fs0) _ _ T c (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply cl_w1; [exact SR0 | unfold USTACK_TOP in *; lia | exact SP | exact FR | exact MI]. }
intros ms1 cc1 (m1 & POST1 & MU1 & WM1 & MI1 & FR1) Hc1. clear Hc FR.

assert (PR1 : rt_pres_fp (rt_live RT Σ1) [(x_F X, 8%nat)] (x_S1 X) [] m m1).
{ apply (pres_fp_of_munch _ _ _ _ _ m m1 MU1). intros x Hx _. cbn [outside]. split; [| exact I]. intros Hin.
destruct Hx as [H|[H|[H|[H|H]]]].
- lia.
- pose proof (client_static_range _ H). unfold SEGTOP_A, USTACK_TOP in *. lia.
- destruct H as (p & q & Hpq & Hx). rewrite EL in Hpq. apply in_app_or in Hpq as [Hpq|Hpq].
+ destruct (proj1 HSP _ _ (Permutation_in _ PERM Hpq)) as (_ & PL & _). lia.
+ destruct (hi_live_geo _ _ _ HX p q Hpq) as (PL & _). lia.
- destruct H as (f & k & [E|[]] & Hx). injection E as <- <-. change (fs_size 8) with 16384 in Hx. lia.
- destruct H as (f & k & [E|[]] & Hx). injection E as <- <-. change (fs_size 8) with 16384 in Hx. rewrite <- ESF, ESF2 in Hx. unfold SH_HI in *. lia. }
assert (ART1' : ART RT Σ1 m1).
{ apply (af_frame RT AF Σ1 m m1 (x_S1 X + -48) ART1); [rewrite ESP; pose proof (hi_lo _ _ _ HX) as (LW0 & _); unfold STACK_WIN in *; lia| | exact WM1].
intros b Hb. apply MU1. cbn [outside]. rewrite EF in Hb. split; [intros Hin; apply Hb; left; unfold USTACK_TOP in *; lia| exact I]. }
assert (STC1 : stk asegs m1 (x_lo X) (x_S1 X + -48)).
{ apply (stk_agree asegs m m1 _ _ STC); [| exact WM1]. apply (agree_of_munch _ m m1 _ MU1). intros x Hx. cbn [outside]. split; [lia| exact I]. }
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m m1 a h _ _ HSP PR1
ltac:(intros e He; rewrite EL; apply in_or_app; right; exact He) (fp_h_nil X a h) (AF_DRV _ _ ART1') PF ERR OUTR SSP) as (PF1 & ERR1 & OUTR1 & SSP1).
assert (INF : In (x_F X, 8%nat) [(x_F X, 8%nat)]) by (left; reflexivity).
assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
assert (HSPS : forall w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208,
cells_size (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208) = 216%nat)
by reflexivity.
eapply (htr_rw _ _ _ _ m m1 PR1) in SP; rewrite ?HSPS; [| apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_nil].
eapply (htr_rw _ _ _ _ m m1 PR1) in LSH; cbn [cells_size csize Nat.add];
[| apply (acl_fshadow _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; lia| apply rng_out_nil].
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
assert (BITS1 : bits_rep asegs m1 (x_F X + HO_BITS) (a_Dc a) (h_bits h)).
{ apply (bits_rep_tr _ _ _ _ m m1 PR1 _ _ _ BITS BOK); [| apply rng_out_nil| | apply rng_out_nil].
- apply (acl_frame _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_BITS; lia.
- apply (acl_live _ _ _ _ _ _ _ (INL _ (own_in_Dc a h))); lia. }
assert (OSR1 : h_os_rep X m1 a h).
{ apply (h_os_rep_tr _ _ _ _ m m1 PR1 X a h OSR).
- apply (acl_frame _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IB)); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IL)); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (INL _ IG)); lia| apply rng_out_nil]. }
unfold HO_OY in SY.
assert (SY1 : sync_rep m1 (x_F X + 8480) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m m1 PR1 _ _ _ _ SY).
- apply (acl_frame _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_nil.
- intros NS. split; [| apply rng_out_nil]. pose proof (own_in_Dsy a h NS) as INS. unfold bptr in *.
apply (acl_live _ _ _ _ _ _ _ (INL _ INS)); lia. }
assert (DEC1 : h_dec_rep X m1 a h).
{ apply (h_dec_rep_tr _ _ _ _ m m1 PR1 X a h DEC). intros b Hb. split; [| apply rng_out_nil].
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E0); rewrite E0 in Hb; destruct Hb]).
apply (acl_live _ _ _ _ _ _ _ (INL _ (own_in_blk a h NS0 b Hb))); lia. }
clear BITS OSR SY DEC PR1 MU1 WM1.
pose proof (own_ne_Dsy a h NDO) as ONE.
destruct POST1 as [(NS0 & ->) | (ES0 & ->)].
-
pose proof DEC1 as DEC1'. unfold h_dec_rep in DEC1'. destruct (h_st h) as [d|] eqn:EST; [| destruct DEC1' as (ES & _); exfalso; exact (NS0 ES)].
destruct DEC1' as (R1 & SPOS & DEP & _ & _ & NDB & _ & NDc & LB19).
assert (NST : h_st h <> None) by (rewrite EST; discriminate).
assert (INB : forall b, In b (a_LBD a) -> In (blk_addr b, blk_size b) (rt_live RT Σ1)) by (intros b Hb; exact (INL _ (own_in_blk a h NST b Hb))).
pose proof (destroy_stack_le d) as DSL.
unfold A_destroy_h in Hc1.
Time cps_rt (DESTROY d Σ1 (PMfd F0 fs0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (x_F X + HO_OUT) (x_F X + HO_STEREO) (a_S a) (x_lo X)
(a_LBD a)).
{ apply PMfd_fdfs_only. }
{ apply PMfd_mat_stable. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). exact STC1. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold RT_STACK, bptr in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). unfold USTACK_TOP in *. lia. }
{ rewrite unsigned_lit by (unfold USTACK_TOP in *; lia). clear - S32. Z.div_mod_to_equations. lia. }
{ apply unwind_ok_ch. split; [cbn; rewrite unsigned_lit by lia; exact in_ras_970b8|].
left. rewrite !unsigned_lit by (unfold USTACK_TOP in *; lia). lia. }
intros cc2 (Σ2 & Hc2 & EL2 & EF2 & ES2 & EC2 & EP2). clear Hc1.
Time cps_unpack_lib Hc2 as (v2 & m2 & RS & RA2 & PR2).
destruct RS as (-> & ->).
destruct RA2 as (ART2 & MI2 & ST2).
rewrite EF in PR2.

assert (NBLK : forall p q, In (p, q) (h_own a h) -> (forall b, In b (a_LBD a) -> blk_addr b <> p) -> In (p, q) (rt_live RT Σ2)).
{ intros p q Hin NB. rewrite EL2. apply live_remove_list_keep; [exact (INL _ Hin)|]. cbn [fst]. intros Hb. apply in_map_iff in Hb as (b & E & Hb). exact (NB b Hb E). }
assert (NOSB : h_stream_init h <> 0 -> forall p, In p [a_Bd a; a_L a; a_G a] -> forall b, In b (a_LBD a) -> blk_addr b <> p).
{ intros NE p Hp b Hb E. pose proof NDO as ND1. unfold h_own in ND1. rewrite EST in ND1.
replace (h_stream_init h =? 0) with false in ND1 by (symmetry; apply Z.eqb_neq; exact NE).
rewrite !map_app in ND1. apply (nodup_app_disj _ _ p ND1); [unfold blocks_live; rewrite map_map, <- E; apply in_map; exact Hb|].
destruct Hp as [<-|[<-|[<-|[]]]]; cbn [map fst app]; [right; left| right; right; left| right; right; right; left]; reflexivity. }
assert (XL2 : forall e, In e (x_live X) -> In e (rt_live RT Σ2)).
{ intros [p q] He. rewrite EL2. apply live_remove_list_keep; [rewrite EL; apply in_or_app; right; exact He|].
cbn [fst]. intros Hb. apply in_map_iff in Hb as (b & E & Hb). exact (XNE _ _ (own_in_blk a h NST b Hb) (p, q) He (eq_sym E)). }
assert (PR2S : rt_pres_fp (rt_live RT Σ2) [(x_F X, 8%nat)] (x_S1 X) [] m1 m2).
{ apply (pres_fp_mono _ _ _ _ _ _ _ m1 m2 PR2); [intros e He; exact He| intros e He; exact He| lia]. }
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ2 m1 m2 a h _ _ HSP PR2S XL2 (fp_h_nil X a h) (AF_DRV _ _ ART2) PF1 ERR1 OUTR1 SSP1)
as (PF2 & ERR2 & OUTR2 & SSP2).
clear PR2S.
eapply (htr_rw _ _ _ _ m1 m2 PR2) in FR1; [| cbn [cl_frame cells_size csize Nat.add]; apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_nil].
eapply (htr_rw _ _ _ _ m1 m2 PR2) in SP; rewrite ?HSPS; [| apply acl_stack; unfold USTACK_TOP in *; lia| apply rng_out_nil].
eapply (htr_rw _ _ _ _ m1 m2 PR2) in LSH; cbn [cells_size csize Nat.add];
[| apply (acl_fshadow _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; lia| apply rng_out_nil].
assert (BITS2 : bits_rep asegs m2 (x_F X + HO_BITS) (a_Dc a) (h_bits h)).
{ apply (bits_rep_tr _ _ _ _ m1 m2 PR2 _ _ _ BITS1 BOK); [| apply rng_out_nil| | apply rng_out_nil].
- apply (acl_frame _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_BITS; lia.
- apply (acl_live _ _ _ _ _ _ _ (NBLK _ _ (own_in_Dc a h) NDc)); lia. }
assert (OSR2 : h_os_rep X m2 a h).
{ apply (h_os_rep_tr _ _ _ _ m1 m2 PR2 X a h OSR1).
- apply (acl_frame _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; unfold HO_OS; lia.
- apply rng_out_nil.
- intros NE. destruct (own_in_os a h NE) as (IB & IL & IG).
split; [apply (acl_live _ _ _ _ _ _ _ (NBLK _ _ IB (NOSB NE _ (or_introl eq_refl)))); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (NBLK _ _ IL (NOSB NE _ (or_intror (or_introl eq_refl))))); lia|]. split; [apply rng_out_nil|].
split; [apply (acl_live _ _ _ _ _ _ _ (NBLK _ _ IG (NOSB NE _ (or_intror (or_intror (or_introl eq_refl)))))); lia| apply rng_out_nil]. }
assert (SY2 : sync_rep m2 (x_F X + 8480) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m1 m2 PR2 _ _ _ _ SY1).
- apply (acl_frame _ _ _ (x_F X) 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_nil.
- intros NS. split; [| apply rng_out_nil]. pose proof (own_in_Dsy a h NS) as INS.
pose proof (proj2 (proj2 (ONE NS)) ltac:(discriminate)) as NBD. unfold bptr in *.
apply (acl_live _ _ _ _ _ _ _ (NBLK _ _ INS NBD)); lia. }
clear BITS1 OSR1 SY1 DEC1 PR2.

refine (rz_evt RT AF Σ2 (PMfd F0 fs0) _ _ T cc2 (PMfd_mat_stable F0 fs0) Hc _ _).
{ eapply cl_w2; [reflexivity | exact MI2]. }
intros ms3 cc3 -> Hc3. clear Hc.
apply (K_bd Σ2 m2 cc3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc3 FRM EL2); assumption.
-
assert (ELBD : a_LBD a = []).
{ unfold h_dec_rep in DEC1. destruct (h_st h) as [d|]; [destruct DEC1 as (_ & SPOS & _); lia| exact (proj2 DEC1)]. }
assert (EL1 : rt_live RT Σ1 = live_remove_list (map blk_addr (a_LBD a)) (rt_live RT Σ1)) by (rewrite ELBD; reflexivity).
apply (K_bd Σ1 m1 cc1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc1 FRM EL1); try reflexivity; assumption.
Qed.
End Clean.
