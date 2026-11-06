(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0h YG10 YG0u YG0d YG0y YG0w YG0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF0k YF6m YF0r YF0u YF1f YF6e YF6a.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF1d YF0q YF6n YF6c YF6j YF6l YF07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Set Printing Depth 100. Set Printing Width 200.
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Ltac cs_case HS HEn Htp kb :=
lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ => replace (Z_to_bv 5 k) with kb by (img_try (img_apply bv_eq; img_refl)) end;
let RR := fresh "RR" in rreg HS kb RR; rewrite RR;
first [ rewrite HEn by (img_try ((img_case; cbv); img_lia)); first [ refine (YF6n.Er _ _ _ _ _ _ _ _ _ _ _ _ _); img_refl | symmetry; refine (YF6n.Er _ _ _ _ _ _ _ _ _ _ _ _ _); img_refl ]
| rewrite Htp; img_refl | symmetry; rewrite Htp; img_refl ].
Ltac inlist := cbn [In]; repeat (first [ left; img_refl | right ]); fail.
Section h. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (S : astate) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (p : sptr) (n : Z) (ch : list (Z * Z * Z)).
Let tr : list Z := call_trace ly (0x53640 + D_2c4) regs ch.
Let sp0 : Z := bv_unsigned (getr regs 2).
Let pa : Z := sptr_addr B ly p.
Let nn : Z := req_size n.
Hypothesis PRE : acall_pre tfxsegs B ly S W regs mem md ch.
Hypothesis HBLK : In (p, n) (blocks S).
Hypothesis HA0 : getr regs 10 = w64 pa.
Hypothesis HU : In tr (as_universe B).
Hypothesis IA1 : tfx_ialloc_spec.
Hypothesis U1 : tfx_unwind_spec.
Hypothesis HTSD : ly_tsd ly = TFX_TSD.
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfxsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation q := (st_qthread S).
Lemma M : ARm B ly S rd0. Proof. img_exact (proj1 (proj1 PRE)). Qed.
Let WF : Wf (as_universe B) S := am_wf B ly S rd0 M.
Let LO : layout_ok ly := am_layout B ly S rd0 M.
Definition kk : chunk := match find_user (st_chunks S) p with Some k => k | None => mkChunk PNull 0 CAllocated end.
Lemma kk_facts : find_user (st_chunks S) p = Some kk /\ In kk (st_chunks S) /\ ck_state kk = CAllocated /\ ck_user kk = p /\ ck_req kk = n.
Proof.
pose proof (find_user_block _ 0 0 0 S p n WF HBLK) as (k & Hf & Hk & Hst & Hu & Hr). unfold kk. rewrite Hf. auto.
Qed.
Lemma KF : cfacts B ly S kk. Proof. img_exact (chunk_facts B ly S rd0 kk M (proj1 (proj2 kk_facts))). Qed.
Lemma Epa : pa = ck_base B ly kk + ck_rz kk.
Proof. pose proof KF as (_ & _ & _ & G4 & _). pose proof kk_facts as (_ & _ & _ & Hu & _). unfold pa. rewrite <- Hu. img_exact G4. Qed.
Lemma Enn : nn = ck_n kk.
Proof. pose proof kk_facts as (_ & _ & _ & _ & Hr). unfold nn, ck_n. rewrite Hr. img_refl. Qed.
Definition hb1 : Z := match rd0 (pa - 15) with Some b => b | None => 0 end.
Definition jw (a : Z) : Z := match rdword rd0 a with Some w => w | None => 0 end.
Definition j1 : Z := jw (T + t_stats + 24).
Definition j2 : Z := jw (T + t_stats + 32).
Definition j3 : Z := jw pa.
Local Notation E0 := (YF6n.E0 ly regs ch pa nn hb1 q j1 j2 j3).
Local Notation LENv := (YF6n.LENv ly regs ch).
Local Notation IMv := (YF6n.IMv pa).
Local Notation HWv := (YF6n.HWv hb1).
Local Notation SPv := (YF6n.SPv pa).
Local Notation N8v := (YF6n.N8v nn).
Local Notation CNT8v := (YF6n.CNT8v nn).
Local Notation QBFv := (YF6n.QBFv nn q).
Lemma cell_sym : forall e (w : nat) e', cell_lookup (Tfx_const ly) e = Some (ACell e w (AV e')) -> val_mem tfxsegs m0 (aeval B ly e) w (aeval B ly e').
Proof. intros e w e' E. img_exact (tfx_const_lookup_sym B TB ly S H0 mem e w e' M E). Qed.
Lemma cell_lit : forall a (w : nat) x, cell_lookup (Tfx_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) -> val_mem tfxsegs m0 a w x.
Proof. intros a w x E. img_exact (tfx_const_lookup B TB ly S H0 mem a w x M E). Qed.
Lemma cell_state : forall c e (w : nat) e', In c (acells B ly S) -> c = ACell e w (AV e') -> val_mem tfxsegs m0 (aeval B ly e) w (aeval B ly e').
Proof.
intros c e w e' Hin ->. img_apply (cell_holds_val_mem B ly H0 mem e w e'). img_exact (proj1 (Forall_forall _ _) (am_cells B ly S rd0 M) _ Hin).
Qed.
Lemma cell_stateZ : forall c e (w : nat) x, In c (acells B ly S) -> c = ACell e w (AV (ANum x)) -> val_mem tfxsegs m0 (aeval B ly e) w x.
Proof. intros c e w x Hin E. img_exact (cell_state c e w (ANum x) Hin E). Qed.
Lemma vis_range : forall e len i, In (e, len) (ajunk B ly S) \/ In (e, len) (aareas S) \/ In (e, len) (aclient S) ->
0 <= i < len -> rd0 (aeval B ly e + i) <> None.
Proof.
intros e len i Hin Hi. destruct Hin as [Hin|[Hin|Hin]].
- img_exact (proj1 (Forall_forall _ _) (am_junk B ly S rd0 M) _ Hin i Hi).
- img_exact (proj1 (Forall_forall _ _) (am_areas B ly S rd0 M) _ Hin i Hi).
- img_exact (proj1 (Forall_forall _ _) (am_client B ly S rd0 M) _ Hin i Hi).
Qed.
Lemma in_thread_junk : forall r, In r thread_junk -> In r (ajunk B ly S).
Proof. intros r Hr. unfold ajunk. right. right. do 5 (img_apply in_or_app; right). img_apply in_or_app. left. img_exact Hr. Qed.
Lemma junk_vals : val_mem tfxsegs m0 (T + t_stats + 24) 8 j1 /\ 0 <= j1 < 2 ^ 64 /\ val_mem tfxsegs m0 (T + t_stats + 32) 8 j2 /\ 0 <= j2 < 2 ^ 64.
Proof.
assert (V : forall a, T + t_stats <= a -> a + 8 <= T + t_unwinding -> val_mem tfxsegs m0 a 8 (jw a) /\ 0 <= jw a < 2 ^ 64).
{ intros a H1 H2. destruct (vis_word H0 mem a) as (w & Rw & Vw & Ew).
- intros i Hi. replace (a + i) with (aeval B ly (AT t_stats) + (a + i - (T + t_stats))) by (img_try (cbn; img_lia)).
img_apply (vis_range (AT t_stats) (t_unwinding - t_stats)); [img_try (left; img_apply in_thread_junk; unfold thread_junk; cbn; tauto) | img_lia].
- unfold jw. rewrite Ew. auto. }
unfold j1, j2. pose proof (V (T + t_stats + 24)) as [A1 A2]; [img_try (unfold t_stats, t_unwinding; img_lia) | img_try (unfold t_stats, t_unwinding; img_lia)|].
pose proof (V (T + t_stats + 32)) as [A3 A4]; [img_try (unfold t_stats, t_unwinding; img_lia) | img_try (unfold t_stats, t_unwinding; img_lia)|]. auto.
Qed.
Lemma hdr_In : forall c, In c (chunk_cells kk) -> In c (acells B ly S).
Proof. intros c Hc. unfold acells. rewrite !in_app_iff. do 2 right. left. img_apply in_flat_map. exists kk. split; [img_try (img_exact (proj1 (proj2 kk_facts))) | img_try (img_exact Hc)]. Qed.
Lemma hb1_facts : rd0 (pa - 15) = Some hb1 /\ 0 <= hb1 < 256 /\ Z.land hb1 127 = 17.
Proof.
pose proof kk_facts as (_ & Hk & Hst & _).
assert (C : cell_holds B ly rd0 (ACell (aoff (aoff (sptr_exp (ck_beg kk)) (ck_rz kk - kChunkHeaderSize)) 1) 1 (AVmask 127 17))).
{ img_apply (proj1 (Forall_forall _ _) (am_cells B ly S rd0 M)). img_apply hdr_In. unfold chunk_cells. img_apply in_app_iff. left. cbn. tauto. }
cbn [cell_holds c_at c_val c_w] in C. rewrite (YF0u.EA2 B ly S rd0 M kk _ _ Hk) in C. unfold kChunkHeaderSize in C.
replace (ck_base B ly kk + (ck_rz kk - 16) + 1) with (pa - 15) in C by (img_try (rewrite Epa; img_lia)).
destruct C as (b & Hb & Hm). unfold hb1. rewrite Hb. destruct (aview_vis_byte H0 mem (pa - 15) ltac:(img_try (rewrite Hb; discriminate))) as (b' & E' & R' & _).
rewrite Hb in E'. injection E' as <-. auto.
Qed.
Lemma hw_val : val_mem tfxsegs m0 (pa - 16) 4 HWv /\ val_mem tfxsegs m0 (pa - 12) 4 nn.
Proof.
pose proof kk_facts as (_ & Hk & Hst & _). pose proof hb1_facts as (HB & HR & _).
assert (EH : aeval B ly (aoff (sptr_exp (ck_beg kk)) (ck_rz kk - kChunkHeaderSize)) = pa - 16).
{ rewrite (YF0u.EA B ly S rd0 M kk _ Hk). rewrite Epa. unfold kChunkHeaderSize. img_lia. }
assert (EH2 : forall d, aeval B ly (aoff (aoff (sptr_exp (ck_beg kk)) (ck_rz kk - kChunkHeaderSize)) d) = pa - 16 + d).
{ intros d. rewrite (YF0u.EA2 B ly S rd0 M kk _ _ Hk). rewrite Epa. unfold kChunkHeaderSize. img_lia. }
assert (V0 : val_mem tfxsegs m0 (pa - 16) 1 2).
{ rewrite <- EH. eapply cell_stateZ; [img_try (img_apply hdr_In; unfold chunk_cells; img_apply in_app_iff; left; left; img_refl)|]. unfold z1, c1, hdr_state. rewrite Hst. img_refl. }
assert (V2 : val_mem tfxsegs m0 (pa - 14) 2 0).
{ replace (pa - 14) with (pa - 16 + 2) by img_lia. rewrite <- (EH2 2). eapply cell_stateZ; [img_try (img_apply hdr_In; unfold chunk_cells; img_apply in_app_iff; left; do 2 right; left; img_refl)|]. img_refl. }
assert (V4 : val_mem tfxsegs m0 (pa - 12) 4 (ck_n kk)).
{ replace (pa - 12) with (pa - 16 + 4) by img_lia. rewrite <- (EH2 4). eapply cell_stateZ; [img_try (img_apply hdr_In; unfold chunk_cells; img_apply in_app_iff; left; do 3 right; left; img_refl)|]. img_refl. }
split; [|img_try (rewrite Enn; img_exact V4)].
intros i Hi. unfold YF6n.HWv.
assert (LB : forall v (w j : nat), YP0g.le_byte v w j = (v mod 2 ^ (8 * Z.of_nat w)) / 2 ^ (8 * Z.of_nat j) mod 256).
{ intros v w j. unfold YP0g.le_byte. rewrite Z.shiftr_div_pow2 by img_lia. img_refl. }
destruct i as [|[|[|[|i]]]]; [| | | |img_lia].
- rewrite (V0 0%nat ltac:(img_lia)). do 2 f_equal. rewrite !LB. img_change (2 ^ (8 * Z.of_nat 1)) with 256. img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
img_change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite !Z.div_1_r. Z.div_mod_to_equations. nia.
- img_change (Z.of_nat 1) with 1. replace (pa - 16 + 1) with (pa - 15) by img_lia. rewrite (aview_byte _ _ _ _ HB). do 2 f_equal.
rewrite !LB. img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296. img_change (2 ^ (8 * Z.of_nat 1)) with 256. Z.div_mod_to_equations. nia.
- replace (pa - 16 + Z.of_nat 2) with (pa - 14 + Z.of_nat 0) by img_lia. rewrite (V2 0%nat ltac:(img_lia)). do 2 f_equal.
rewrite !LB. img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296. img_change (2 ^ (8 * Z.of_nat 2)) with 65536. img_change (2 ^ (8 * Z.of_nat 0)) with 1.
rewrite !Z.div_1_r. Z.div_mod_to_equations. nia.
- replace (pa - 16 + Z.of_nat 3) with (pa - 14 + Z.of_nat 1) by img_lia. rewrite (V2 1%nat ltac:(img_lia)). do 2 f_equal.
rewrite !LB. img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296. img_change (2 ^ (8 * Z.of_nat 2)) with 65536.
img_change (2 ^ (8 * Z.of_nat 1)) with 256. img_change (2 ^ (8 * Z.of_nat 3)) with 16777216. Z.div_mod_to_equations. nia.
Qed.
Lemma user_vis : forall a, pa <= a < pa + 8 -> rd0 a <> None.
Proof.
intros a Ha. pose proof kk_facts as (_ & Hk & Hst & Hu & _). pose proof (YF1f.ext_rounded B ly S rd0 M kk Hk) as (ER & NN1 & NN2 & NN3). rewrite <- Enn in *.
destruct (Z_lt_le_dec a (pa + nn)) as [L|L].
- replace a with (aeval B ly (sptr_exp (ck_user kk)) + (a - pa)) by (img_try (unfold pa; rewrite <- Hu; unfold sptr_addr; img_lia)).
img_apply (vis_range _ (ck_n kk)); [|img_try (rewrite <- Enn; img_lia)]. do 2 right. unfold aclient. img_apply in_app_iff. left. img_apply in_flat_map. exists kk. split; [img_try (img_exact Hk)|].
unfold chunk_user. rewrite Hst. left. img_refl.
- replace a with (aeval B ly (aoff (sptr_exp (ck_beg kk)) (ck_rz kk + ck_n kk)) + (a - pa - nn)) by (img_try (rewrite (YF0u.EA B ly S rd0 M kk _ Hk), Epa, Enn; img_lia)).
img_apply (vis_range _ (ck_extent kk - ck_rz kk - ck_n kk)); [|img_try (rewrite <- Enn; img_lia)].
left. unfold ajunk. right. right. rewrite !in_app_iff. do 2 right. left. img_apply in_flat_map. exists kk. split; [img_try (img_exact Hk)|].
unfold chunk_junk. rewrite !in_app_iff. do 3 right. left. img_refl.
Qed.
Lemma j3_val : val_mem tfxsegs m0 pa 8 j3 /\ 0 <= j3 < 2 ^ 64.
Proof.
destruct (vis_word H0 mem pa) as (w & Rw & Vw & Ew); [img_try (intros i Hi; img_apply user_vis; img_lia)|]. unfold j3, jw. rewrite Ew. auto.
Qed.
Lemma unwinding_val : val_mem tfxsegs m0 (T + t_unwinding) 1 0.
Proof.
replace (T + t_unwinding) with (aeval B ly (AT t_unwinding)) by img_refl.
eapply cell_stateZ; [|img_refl]. unfold acells. rewrite !in_app_iff. do 8 right. left. img_refl.
Qed.
Lemma meta_vis : forall a, pa - 16 <= a < pa -> rd0 a <> None.
Proof.
intros a Ha. pose proof kk_facts as (_ & Hk & _). pose proof hw_val as [V1 V2].
destruct (Z_lt_le_dec a (pa - 12)) as [L1|L1]. { replace a with (pa - 16 + (a - (pa - 16))) by img_lia. img_exact (val_mem_vis _ _ _ _ _ (a - (pa - 16)) V1 ltac:(img_lia)). }
destruct (Z_lt_le_dec a (pa - 8)) as [L2|L2]. { replace a with (pa - 12 + (a - (pa - 12))) by img_lia. img_exact (val_mem_vis _ _ _ _ _ (a - (pa - 12)) V2 ltac:(img_lia)). }
replace a with (aeval B ly (aoff (sptr_exp (ck_beg kk)) (ck_rz kk - 8)) + (a - (pa - 8))) by (img_try (rewrite (YF0u.EA B ly S rd0 M kk _ Hk), Epa; img_lia)).
img_apply (vis_range _ 8); [|img_lia]. left. unfold ajunk. right. right. rewrite !in_app_iff. do 2 right. left. img_apply in_flat_map. exists kk. split; [img_try (img_exact Hk)|].
unfold chunk_junk. rewrite !in_app_iff. right. left. left. img_refl.
Qed.
Lemma shadow_vis : forall i, 0 <= i < CNT8v -> exists v, rd0 (SPv + i) = Some v.
Proof.
intros i Hi. pose proof kk_facts as (_ & Hk & _). pose proof (YF1f.ext_rounded B ly S rd0 M kk Hk) as (ER & NN1 & NN2 & NN3).
pose proof (YF1f.u_al8 B ly S rd0 M kk Hk) as (U8 & B8 & R8). pose proof KF as (G1 & G2 & G3 & G4 & G5 & _).
unfold YF6n.CNT8v, YF6n.N8v in Hi. rewrite Z_div_mult in Hi by img_lia. rewrite <- Enn in *.
set (g := pa + 8 * i).
assert (FC : find_chunk_at B ly (st_chunks S) g = Some kk).
{ img_apply (find_chunk_at_hit B ly S rd0 (st_chunks S) kk g M ltac:(img_try (intros x Hx; img_exact Hx)) (wf_chunks_nodup _ _ _ _ _ WF) Hk). (subst g; cbv beta).
pose proof Epa as EP. clear - EP Hi ER NN2 G5. rewrite EP. img_lia. }
assert (SH : ashadow B ly S g = Some (chunk_granule kk ((g - ck_base B ly kk) / 8))) by (img_try (unfold ashadow; rewrite FC; img_refl)).
pose proof kk_facts as (_ & _ & _ & Hu & _).
assert (PC : exists c, pa = c * 8). { apply Z.mod_divide in U8 as [c Hc]; [|img_lia]. exists c. unfold pa. rewrite <- Hu. img_exact Hc. }
destruct PC as [c Hc].
pose proof (am_shadow B ly S rd0 M g _ ltac:(img_try ((subst g; cbv beta); rewrite Hc; replace (c * 8 + 8 * i) with ((c + i) * 8) by img_lia; img_apply Z_mod_mult)) SH) as R.
exists (chunk_granule kk ((g - ck_base B ly kk) / 8)). rewrite <- R. f_equal. unfold shadow_addr, YF6n.SPv. (subst g; cbv beta).
rewrite Hc. replace (c * 8 + 8 * i) with ((c + i) * 8) by img_lia. rewrite !Z_div_mult by img_lia. img_lia.
Qed.
Lemma ial_vals : val_mem tfxsegs m0 TFX_IAL_FLAG 1 (if st_internal_inited S then 1 else 0) /\ val_mem tfxsegs m0 (TFX_IAL_FLAG + 1) 1 0 /\
(if st_internal_inited S then val_mem tfxsegs m0 TFX_IAL_W 8 4096 /\ val_mem tfxsegs m0 (TFX_IAL_W + 8) 8 (TFX_IAL_W + 16)
else val_mem tfxsegs m0 TFX_IAL_W 8 0 /\ val_mem tfxsegs m0 (TFX_IAL_W + 8) 8 0) /\
(forall a, TFX_IAL_LO <= a < TFX_IAL_W \/ TFX_IAL_W + 16 <= a < TFX_IAL_HI -> mbyte tfxsegs m0 a = Some (Z_to_bv 8 0)).
Proof.
assert (IN : forall c, In c (ialloc_cells B S) -> In c (acells B ly S)) by (img_try (intros c Hc; unfold acells; rewrite !in_app_iff; do 7 right; left; img_exact Hc)).
unfold ialloc_cells in IN. rewrite (ts_ial_flag _ TB), (ts_ial_lo _ TB), (ts_ial_w _ TB) in IN.
splits.
- replace TFX_IAL_FLAG with (aeval B ly (ANum TFX_IAL_FLAG)) at 1 by img_refl. eapply cell_stateZ; [img_try (img_apply IN; left; img_refl) | img_try (destruct (st_internal_inited S); img_refl)].
- replace (TFX_IAL_FLAG + 1) with (aeval B ly (ANum (TFX_IAL_FLAG + 1))) by img_refl. eapply cell_stateZ; [img_try (img_apply IN; right; left; img_refl) | img_refl].
- assert (E1 : aeval B ly (AIal (TFX_IAL_W - TFX_IAL_LO)) = TFX_IAL_W) by (img_try (cbn; rewrite (ts_ial_lo _ TB); img_lia)).
assert (E2 : aeval B ly (AIal (TFX_IAL_W - TFX_IAL_LO + 8)) = TFX_IAL_W + 8) by (img_try (cbn; rewrite (ts_ial_lo _ TB); img_lia)).
assert (E3 : aeval B ly (AIal (TFX_IAL_W - TFX_IAL_LO + 16)) = TFX_IAL_W + 16) by (img_try (cbn; rewrite (ts_ial_lo _ TB); img_lia)).
destruct (st_internal_inited S); split.
+ rewrite <- E1. eapply cell_stateZ; [img_try (img_apply IN; do 2 right; left; img_refl) | img_refl].
+ rewrite <- E2, <- E3. eapply cell_state; [img_try (img_apply IN; do 3 right; left; img_refl) | img_refl].
+ rewrite <- E1. eapply cell_stateZ; [img_try (img_apply IN; do 2 right; left; img_refl) | img_refl].
+ rewrite <- E2. eapply (cell_state _ _ 8 (ANum 0)); [img_try (img_apply IN; do 3 right; left; img_refl) | img_refl].
- intros a Ha. pose proof (am_zero B ly S rd0 M) as ZR. unfold ialloc_zero in ZR. rewrite (ts_ial_lo _ TB), (ts_ial_w _ TB), (ts_ial_hi _ TB) in ZR.
apply Forall_cons_iff in ZR as [Z1 ZR]. apply Forall_cons_iff in ZR as [Z2 _].
assert (R : rd0 a = Some 0).
{ destruct Ha as [Ha|Ha].
- replace a with (aeval B ly (AIal 0) + (a - TFX_IAL_LO)) by (img_try (cbn; rewrite (ts_ial_lo _ TB); img_lia)). img_apply Z1. cbn [snd]. img_lia.
- replace a with (aeval B ly (AIal (TFX_IAL_W - TFX_IAL_LO + 16)) + (a - (TFX_IAL_W + 16))) by (img_try (cbn; rewrite (ts_ial_lo _ TB); img_lia)). img_apply Z2. cbn [snd]. img_lia. }
img_exact (aview_byte _ _ _ _ R).
Qed.
Lemma HB1 : 0 <= hb1 < 256 /\ Z.land hb1 127 = 17. Proof. pose proof hb1_facts; tauto. Qed.
Lemma HSP : ly_stk_lo ly + ASTACK <= sp0 <= ly_stk_hi ly.
Proof. destruct PRE as (_ & _ & _ & _ & Hlo & _ & Hhi & _). unfold spZ in *. unfold sp0. img_lia. Qed.
Lemma IMG : img_cover ly.
Proof. destruct PRE as ((_ & LED & _) & _). img_exact (img_cover_of_ledger ly S md LED). Qed.
Lemma HI : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 (ly_Q ly) kPtrArrayResv /\ ly_Q ly + kPtrArrayResv <= ASAN_CEIL /\
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ zone3 (ly_F ly) kFakeStackSize /\ ly_F ly + kFakeStackSize <= ASAN_CEIL /\
zone3 (ly_NB ly) kNodesBlockSize /\ ly_NB ly + kNodesBlockSize <= ASAN_CEIL /\ zone3 (ly_SB ly) kStoreBlockSize /\ ly_SB ly + kStoreBlockSize <= ASAN_CEIL /\
zone3 (ly_C ly) 256 /\ ly_C ly + 256 <= ASAN_CEIL /\ kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= ly_space ly /\ ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
zone3 (ck_base B ly kk) (ck_extent kk) /\ ck_base B ly kk + ck_extent kk <= ASAN_CEIL /\ 16 <= ck_rz kk /\ ly_stk_lo ly mod 4096 = 0.
Proof. img_exact (YF1f.HIGH B ly S rd0 M kk (proj1 (proj2 kk_facts)) IMG). Qed.
Lemma items_n_pos : forall b x, In b (all_batches S) -> In x (b_items b) -> 1 <= ck_n x.
Proof.
intros b x Hb Hx. pose proof (proj1 (Forall_forall _ _) (wq_items _ (wf_quarantine _ _ _ _ _ WF)) x ltac:(img_try (unfold q_items; img_apply in_flat_map; exists b; auto))) as [X1 _].
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) x X1) as [N _]. unfold ck_n. pose proof (req_size_bounds (ck_req x) ltac:(img_lia)). img_lia.
Qed.
Lemma b_bytes_ge : forall b, In b (all_batches S) -> kBatchBytes <= b_bytes b.
Proof.
intros b Hb. unfold b_bytes.
assert (G : forall l, incl l (b_items b) -> 0 <= fold_right (fun k acc => ck_n k + acc) 0 l).
{ induction l as [|x t IH]; intros Hl; cbn; [img_lia|]. pose proof (items_n_pos b x Hb (Hl x (or_introl eq_refl))). pose proof (IH ltac:(img_try (intros y Hy; img_apply Hl; right; img_exact Hy))). img_lia. }
pose proof (G (b_items b) ltac:(img_try (intros y Hy; img_exact Hy))). img_lia.
Qed.
Lemma sum_bytes_ge : forall l, incl l (all_batches S) -> 0 <= sum_bytes l.
Proof.
induction l as [|b t IH]; intros Hl; cbn; [img_try (unfold sum_bytes; cbn; img_lia)|]. unfold sum_bytes in *. cbn.
pose proof (b_bytes_ge b (Hl b (or_introl eq_refl))). pose proof (IH ltac:(img_try (intros y Hy; img_apply Hl; right; img_exact Hy))). unfold kBatchBytes in *. img_lia.
Qed.
Lemma QB_facts : 0 <= qc_bytes q /\ QBFv <= YF6n.QBMAX /\ 1 <= nn < 2 ^ 28.
Proof.
pose proof (wq_bytes_t _ (wf_quarantine _ _ _ _ _ WF)) as QE.
pose proof (sum_bytes_ge (qc_list q) ltac:(img_try (intros y Hy; unfold all_batches; img_apply in_app_iff; left; img_exact Hy))) as S1.
pose proof kk_facts as (_ & Hk & _ & _ & Hr). pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ WF) kk Hk) as [N _].
pose proof (req_size_bounds (ck_req kk) ltac:(img_lia)) as (Q1' & Q2 & Q3). rewrite Hr in Q1', Q2, Q3, N. unfold MALLOC_MAX in N.
assert (QT : qc_bytes q <= kQuarantineCacheMax) by (img_try (destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT); img_exact (proj1 HQT))).
unfold YF6n.QBFv, YF6n.QBMAX. unfold nn.
splits; [img_try (img_change (st_qthread S) with q in QE; img_lia) | img_try (destruct (need_new_batch q); unfold kBatchBytes; img_lia) | img_lia | img_lia].
Qed.
Lemma p_zone : zone3 (pa - 16) (N8v + 16).
Proof.
pose proof kk_facts as (_ & Hk & _). pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (YF1f.ext_rounded B ly S rd0 M kk Hk) as (ER & NN1 & NN2 & NN3). pose proof Epa as EP. rewrite <- Enn in *.
pose proof HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ZK & _). clear - G1 G4 G5 ER NN1 NN2 NN3 EP ZK.
unfold YF6n.N8v. rewrite EP. ceil. unfold zone3, zone3cases, in_app in *. img_lia.
Qed.
Lemma p_facts : 4096 + 16 <= pa /\ pa + N8v <= ASAN_CEIL /\ pa mod 16 = 0 /\ pa mod 8 = 0 /\ 8 <= N8v /\ nn <= N8v < nn + 8 /\ N8v mod 8 = 0 /\
1 <= LENv <= 30 /\ 0 <= IMv - (0xab3c0 + D_10c0) <= 8 * 0x7fff /\ IMv mod 8 = 0 /\ SHADOW_OFF + 514 <= SPv /\ SPv + CNT8v <= kHighMemBeg /\ SPv mod 2 = 0 /\
CNT8v = (nn + 7) / 8.
Proof.
pose proof kk_facts as (_ & Hk & _). pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (YF1f.ext_rounded B ly S rd0 M kk Hk) as (ER & NN1 & NN2 & NN3). pose proof (YF1f.u_al8 B ly S rd0 M kk Hk) as (U8 & B8 & R8).
pose proof Epa as EP. rewrite <- Enn in *.
assert (LO16 : 4096 <= ck_base B ly kk) by (img_try (clear - G1; unfold in_app in G1; img_lia)).
assert (P16 : pa mod 16 = 0).
{ rewrite EP. apply Z.mod_divide in G3 as [c Hc]; [|img_lia]. apply Z.mod_divide in G6 as [c' Hc']; [|img_lia]. rewrite Hc, Hc'. img_apply Z.mod_divide; [img_lia|]. exists (c + c'). img_lia. }
unfold YF6n.N8v, YF6n.LENv, YF6n.IMv, YF6n.SPv, YF6n.CNT8v, YF6n.N8v. rewrite !Z_div_mult by img_lia.
pose proof (unwind_of_chain_length (0x53640 + D_2c4) ((spZ regs, raZ regs, s0Z regs) :: ch)) as UL.
assert (LEN : (1 <= length (YF6n.tr ly regs ch) <= 30)%nat).
{ unfold YF6n.tr, call_trace. destruct (frame0_ok ly regs); [img_try (img_exact UL) | img_try (cbn; img_lia)]. }
apply Z.mod_divide in P16 as [c Hc]; [|img_lia].
pose proof (Z.div_le_mono 4112 pa 8 ltac:(img_lia) ltac:(img_lia)) as S1. img_change (4112 / 8) with 514 in S1.
pose proof (YF1f.hs_bounds (pa + (nn + 7) / 8 * 8 - 8) ltac:(img_lia) ltac:(img_try (ceil; unfold kHighMemEnd, ASAN_CEIL in *; img_lia))) as [_ S2].
unfold shadow_addr in S2. replace (pa + (nn + 7) / 8 * 8 - 8) with (pa + ((nn + 7) / 8 - 1) * 8) in S2 by img_lia. rewrite Z.div_add in S2 by img_lia.
assert (D32 : 0 <= pa / 2 ^ 32 <= 32767).
{ img_change (2 ^ 32) with 4294967296. split; [img_try (img_apply Z.div_pos; img_lia)|].
pose proof (Z.div_le_mono pa 140737479966720 4294967296 ltac:(img_lia) ltac:(img_try (ceil; unfold ASAN_CEIL in *; img_lia))) as X. img_change (140737479966720 / 4294967296) with 32767 in X. img_exact X. }
assert (IM8 : ((701376 + D_10c0) + 8 * (pa / 2 ^ 32)) mod 8 = 0). { img_apply Z.mod_divide; [img_lia|]. exists ((87672 + D_218) + pa / 2 ^ 32). img_lia. }
assert (SP2 : (SHADOW_OFF + pa / 8) mod 2 = 0).
{ rewrite Hc. replace (c * 16) with (c * 2 * 8) by img_lia. rewrite Z_div_mult by img_lia. unfold SHADOW_OFF. img_apply Z.mod_divide; [img_lia|]. exists (1073725440 + c). img_lia. }
assert (P8 : pa mod 8 = 0). { rewrite Hc. replace (c * 16) with (c * 2 * 8) by img_lia. img_apply Z_mod_mult. }
assert (P16' : pa mod 16 = 0). { rewrite Hc. img_apply Z_mod_mult. }
assert (N88 : (nn + 7) / 8 * 8 mod 8 = 0) by img_apply Z_mod_mult.
splits; first [assumption | img_lia].
Qed.
Lemma E2 : ew E0 2 = getr regs 2. Proof. img_exact (YF6n.E2 ly regs ch pa nn hb1 q j1 j2 j3). Qed.
Lemma E10 : ew E0 10 = w64 pa. Proof. rewrite (YF6n.E10 ly regs ch pa nn hb1 q j1 j2 j3). img_exact HA0. Qed.
Lemma EaT : ew E0 32 = w64 T. Proof. img_refl. Qed.
Lemma EaC : ew E0 33 = w64 (ly_C ly). Proof. img_refl. Qed.
Lemma EaSB : ew E0 34 = w64 SB. Proof. img_refl. Qed.
Lemma EaTOP : ew E0 35 = w64 (ly_top ly). Proof. img_refl. Qed.
Lemma EaLEN : ew E0 36 = w64 LENv. Proof. img_refl. Qed.
Lemma EaIM : ew E0 37 = w64 IMv. Proof. img_refl. Qed.
Lemma EaHW : ew E0 38 = w64 HWv. Proof. img_refl. Qed.
Lemma EaN : ew E0 39 = w64 nn. Proof. img_refl. Qed.
Lemma EaSHB : ew E0 40 = w64 SHADOW_OFF. Proof. img_refl. Qed.
Lemma EaSP : ew E0 41 = w64 SPv. Proof. img_refl. Qed.
Lemma EaN8 : ew E0 42 = w64 N8v. Proof. img_refl. Qed.
Lemma EaCNT8 : ew E0 43 = w64 CNT8v. Proof. img_refl. Qed.
Lemma EaQBF : ew E0 50 = w64 QBFv. Proof. img_refl. Qed.
Lemma EaJ1 : ew E0 51 = w64 j1. Proof. img_refl. Qed.
Lemma EaJ2 : ew E0 52 = w64 j2. Proof. img_refl. Qed.
Lemma EaJ3 : ew E0 53 = w64 j3. Proof. img_refl. Qed.
Lemma chunk_lit : forall a (w : BinNums.N) x, val_mem tfxsegs m0 a (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 0 (YQ0b.mkChunk a (CVal w (SLit x))).
Proof. intros a w x Hm Hx Hw. eapply chunk_ok_val; [img_refl | img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (rewrite Z.add_0_l; img_exact Hm)]. Qed.
Lemma chunk_lit_at : forall base a (w : BinNums.N) x, val_mem tfxsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 base (YQ0b.mkChunk a (CVal w (SLit x))).
Proof. intros base a w x Hm Hx Hw. eapply chunk_ok_val; [img_refl | img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (img_exact Hm)]. Qed.
Lemma chunk_atom : forall base a (w : BinNums.N) k d x, ew E0 k = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfxsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YQ0b.chunk_ok tfxsegs E0 m0 base (YQ0b.mkChunk a (CVal w (SOff k d))).
Proof.
intros base a w k d x Hk Hr Hm Hx Hw. eapply chunk_ok_val; [| img_try (img_exact Hx) | img_try (img_exact Hw) | img_try (img_exact Hm)].
cbn [sv_denot]. rewrite Hk. unfold w64. rewrite Zbv_add_unsigned. f_equal. img_lia.
Qed.
Lemma val_mem_writable : forall a (w : nat) v o, val_mem tfxsegs m0 a w v -> a <= o < a + Z.of_nat w -> off_img o -> writable_at tfxsegs m0 o.
Proof. intros a w v o Hv Ho Ha. img_apply vis_writable_off; [img_try (img_exact Ha)|]. replace o with (a + (o - a)) by img_lia. eapply val_mem_vis; [img_try (img_exact Hv) | img_lia]. Qed.
Ltac offw := first [ img_lia | img_apply off_img_high; unfold TFX_IMG_END, kHighMemBeg in *; ceil; unfold ASAN_CEIL in *; img_lia
| apply (zone3_off_img _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 HI)))))); unfold kThreadObjSize, t_qc, t_unwinding, t_stats, t_cache in *; img_lia
| img_apply (zone3_off_img _ _ _ p_zone); unfold YF6n.N8v in *; img_lia ].
Local Ltac reg_intro := unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
Local Ltac r8 := img_change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); img_lia.
Local Ltac r4 := img_change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); img_lia.
Local Ltac lit_region :=
reg_intro; split; [img_lia|]; split; [img_lia|]; split; [img_try (intros o Ho; img_lia)|];
repeat (img_apply Forall_cons; [img_try (img_apply chunk_lit; [img_apply cell_lit; (img_case; vm_compute); img_refl | cbn; img_lia | cbn; img_lia]) |]); img_apply Forall_nil.
Lemma REG0_ok : Forall (region_ok tfxsegs E0 m0) YF6n.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hF1 & hF2 & hNB1 & hNB2 & hSB1 & hSB2 & hC1 & hC2 & hS1 & hS2 & hSP1 & hSP2 & hK1 & hK2 & hK3 & _). unfold zone3 in hQ1, hT1, hF1, hNB1, hSB1, hC1, hK1.
pose proof HSP as [S1 S2]. pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof p_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14).
pose proof QB_facts as (Qa & Qb & Q8). pose proof HB1 as [HBR _].
pose proof junk_vals as (J1 & J1R & J2 & J2R). pose proof j3_val as [J3 J3R].
pose proof hw_val as [W1 W2].
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kHighShadowBeg, kQuarantineCacheMax, EV_MAX, kBatchSlots in
hP1, hP2, hQ1, hQ2, hT1, hT2, hF1, hF2, hNB1, hNB2, hSB1, hSB2, hC1, hC2, hS1, hS2, hSP1, hSP2, hK1, hK2, S1, S2, T2, T4, T7, P1, P2, P11, P12.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
destruct PRE as (_ & _ & _ & _ & _ & _ & _ & HPRES & _). unfold spZ in HPRES. fold sp0 in HPRES.
unfold YF6n.REG0, flit1, flit4, flit8, flits8, fatom8. cbn [map combine seq length Z.of_nat Pos.of_succ_nat Pos.succ fst snd Z.mul Z.add Pos.mul Pos.add].
unfold aSB, aSHB, aC, aT, aTOP, aJ1, aJ2, aJ3, aQS, aQF, aQB, aB, aBB, aBC, aSLOT, aHW, aN.
img_apply Forall_cons.
{   img_apply (region_ok_stack tfxsegs E0 m0 2 sp0 (- ASTACK)); [img_try (rewrite E2; img_refl) | img_try (unfold ASTACK in *; img_lia) | img_lia |].
intros a Ha. img_apply apresent_writable; [img_try (unfold TFX_IMG_END, ASTACK in *; img_lia) | img_try (img_apply HPRES; img_exact Ha)]. }
do 11 (img_apply Forall_cons; [img_try (lit_region)|]).
img_apply Forall_cons. {   reg_intro. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 40%nat 0 SHADOW_OFF); [img_refl | img_try (unfold SHADOW_OFF; img_lia) | | img_try (unfold SHADOW_OFF; cbn; img_lia) | img_try (cbn; img_lia)].
rewrite Z.add_0_l. img_apply cell_lit. img_case; vm_compute. all: img_refl. }
do 13 (img_apply Forall_cons; [img_try (lit_region)|]).
img_apply Forall_cons. {   reg_intro. unfold TFX_TP. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply chunk_lit; [| img_try (unfold TFX_TSD; cbn; img_lia) | img_try (cbn; img_lia)].
replace ((6148432 + D_10c0) - 88) with (aeval B ly (ATp (-88))) by (img_try (cbn; rewrite (ts_tp B TB); img_refl)).
replace TFX_TSD with (aeval B ly (ATsd 0)) by (img_try (cbn; rewrite HTSD; unfold TFX_TSD; img_lia)). img_apply cell_sym. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_intro. unfold TFX_TSD. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom 0 _ 8 33%nat 0 (ly_C ly)); [img_try (rewrite EaC; unfold w64; f_equal; img_lia) | img_lia | | img_try (cbn; img_lia) | img_try (cbn; img_lia)].
rewrite Z.add_0_l. replace (6284536 + D_10c0) with (aeval B ly (ATsd 0)) by (img_try (cbn; rewrite HTSD; img_refl)).
replace (ly_C ly) with (aeval B ly (AC 0)) by (img_try (cbn; img_lia)). img_apply cell_sym. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_intro. rewrite EaC. unfold w64. rewrite unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- img_apply chunk_lit_at; [| img_try (cbn; img_lia) | img_try (cbn; img_lia)]. replace (ly_C ly + 8) with (aeval B ly (AC 8)) by img_refl. img_apply (cell_sym (AC 8) 4 (ANum 0)). img_case; vm_compute. all: img_refl.
- img_apply (chunk_atom _ _ 8 32%nat 0 T); [img_try (rewrite EaT; unfold w64; f_equal; img_lia) | img_lia | | img_try (cbn; img_lia) | img_try (cbn; img_lia)].
replace (ly_C ly + 152) with (aeval B ly (AC 152)) by img_refl. replace T with (aeval B ly (AT 0)) by (img_try (cbn; img_lia)).
img_apply cell_sym. img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]]])].
- img_apply (chunk_atom _ _ 8 33%nat 0 (ly_C ly)); [img_try (rewrite EaC; unfold w64; f_equal; img_lia) | img_lia | | img_try (cbn; img_lia) | img_try (cbn; img_lia)].
replace (ly_T ly + 0) with (aeval B ly (AT 0)) by (img_try (cbn; img_lia)). replace (ly_C ly) with (aeval B ly (AC 0)) by (img_try (cbn; img_lia)). img_apply cell_sym. img_case; vm_compute. all: img_refl.
- img_apply (chunk_atom _ _ 8 35%nat 0 (ly_top ly)); [img_try (rewrite EaTOP; unfold w64; f_equal; img_lia) | img_lia | | img_try (cbn; img_lia) | img_try (cbn; img_lia)].
replace (ly_T ly + 8) with (aeval B ly (AT 8)) by (img_try (cbn; img_lia)). replace (ly_top ly) with (aeval B ly (ATop 0)) by (img_try (cbn; img_lia)). img_apply cell_sym. img_case; vm_compute. all: img_refl.
- img_apply (chunk_atom _ _ 8 35%nat (- kStackSpan) (ly_top ly - kStackSpan)); [img_try (rewrite EaTOP; unfold w64; f_equal; img_lia) | img_try (unfold kStackSpan; img_lia) | | img_try (unfold kStackSpan; cbn; img_lia) | img_try (cbn; img_lia)].
replace (ly_T ly + 16) with (aeval B ly (AT 16)) by (img_try (cbn; img_lia)). replace (ly_top ly - kStackSpan) with (aeval B ly (ATop (- kStackSpan))) by (img_try (cbn; img_lia)).
img_apply cell_sym. img_case; vm_compute. all: img_refl.
- img_apply chunk_lit_at; [| img_try (cbn; img_lia) | img_try (cbn; img_lia)]. replace (ly_T ly + 40) with (aeval B ly (AT 40)) by (img_try (cbn; img_lia)). img_apply (cell_sym (AT 40) 1 (ANum 0)). img_case; vm_compute. all: img_refl. }
img_apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by img_lia. unfold t_unwinding.
pose proof unwinding_val as U. unfold t_unwinding in U.
split; [img_lia|]. split; [img_lia|]. split.
{ intros o Ho. img_apply (val_mem_writable _ _ _ _ U); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFX_IMG_END; offw. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. img_apply chunk_lit_at; [img_try (img_exact U) | img_try (cbn; img_lia) | img_try (cbn; img_lia)]. }
img_apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by img_lia. unfold t_stats in *.
split; [img_lia|]. split; [img_lia|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o 2832); [img_try (img_apply (val_mem_writable _ _ _ _ J1)) | img_try (img_apply (val_mem_writable _ _ _ _ J2))]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFX_IMG_END; offw. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- img_apply (chunk_atom _ _ 8 51%nat 0 j1); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact J1 | img_lia]) | img_try (r8) | img_try (cbn; img_lia)].
- img_apply (chunk_atom _ _ 8 52%nat 0 j2); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (eapply val_mem_addr; [img_exact J2 | img_lia]) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_cons. {   reg_intro. rewrite E10. unfold w64. rewrite unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o (-12)); [img_try (img_apply (val_mem_writable _ _ _ _ W1)) | img_try (img_apply (val_mem_writable _ _ _ _ W2))]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFX_IMG_END; offw. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])].
- img_apply (chunk_atom _ _ 4 38%nat 0 HWv); [img_try (rewrite Z.sub_0_r; img_refl) | img_try (unfold YF6n.HWv; img_lia) | img_try (replace (pa + -16) with (pa - 16) by img_lia; img_exact W1) | img_try (unfold YF6n.HWv; r4) | img_try (cbn; img_lia)].
- img_apply (chunk_atom _ _ 4 39%nat 0 nn); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (replace (pa + -12) with (pa - 12) by img_lia; img_exact W2) | img_try (r4) | img_try (cbn; img_lia)]. }
img_apply Forall_cons. {   reg_intro. rewrite E10. unfold w64. rewrite unsigned_lit_small by img_lia.
split; [img_lia|]. split; [img_lia|]. split.
{ intros o Ho. img_apply (val_mem_writable _ _ _ _ J3); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFX_IMG_END; offw. }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_atom _ _ 8 53%nat 0 j3); [img_try (rewrite Z.sub_0_r; img_refl) | img_lia | img_try (rewrite Z.add_0_r; img_exact J3) | img_try (r8) | img_try (cbn; img_lia)]. }
img_apply Forall_nil.
Qed.
Lemma PAIRS_ok : pairwise_disjoint E0 YF6n.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hF1 & hF2 & hNB1 & hNB2 & hSB1 & hSB2 & hC1 & hC2 & hS1 & hS2 & hSP1 & hSP2 & hK1 & hK2 & hK3 & _). unfold zone3 in hQ1, hT1, hF1, hNB1, hSB1, hC1, hK1.
pose proof HSP as [S1 S2]. pose proof p_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & _). pose proof QB_facts as (_ & _ & Q8).
pose proof kk_facts as (_ & Hk & _). pose proof Epa as EP. pose proof (YF1f.ext_rounded B ly S rd0 M kk Hk) as (ER & NN1 & NN2 & NN3). rewrite <- Enn in ER, NN1, NN2, NN3.
pose proof (YF0u.SX B ly S rd0 M 2 6 _ _ eq_refl eq_refl ltac:(img_lia)) as DCT.
pose proof (YF0u.SX B ly S rd0 M 6 8 _ _ eq_refl eq_refl ltac:(img_lia)) as DCS.
pose proof (YF0u.SX B ly S rd0 M 2 8 _ _ eq_refl eq_refl ltac:(img_lia)) as DTS.
pose proof (YF0u.anyX B ly S rd0 M kk 6 _ Hk eq_refl ltac:(img_lia)) as DCP.
pose proof (YF0u.anyX B ly S rd0 M kk 2 _ Hk eq_refl ltac:(img_lia)) as DTP.
pose proof (YF0u.anyX B ly S rd0 M kk 8 _ Hk eq_refl ltac:(img_lia)) as DSP.
unfold zdisjoint in DCT, DCS, DTS, DCP, DTP, DSP. cbn [fst snd] in DCT, DCS, DTS, DCP, DTP, DSP.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
img_apply pairwise_disjoint_of_extents. unfold YF6n.REG0, flit1, flit4, flit8, flits8, fatom8, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add].
unfold aSB, aSHB, aC, aT, aTOP, aJ1, aJ2, aJ3, aHW, aN.
rewrite E2, E10, EaT, EaC. unfold w64.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, ASTACK in *.
fold sp0. rewrite !unsigned_lit_small by img_lia.
clear - S1 S2 hT1 hT2 hC1 hC2 hS1 hS2 hSP1 hSP2 hK1 hK2 hK3 hP1 hP2 hNB1 hSB1 P1 P2 P5 EP ER NN1 Usp DCT DCS DTS DCP DTP DSP CR CR0.
unfold TFX_TP, TFX_TSD, t_qc, t_unwinding, t_stats in *. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in hT1, hC1, hK1.
repeat split;
first [ clear DCT DCS DTS DCP DTP DSP hT1 hC1 hK1; img_lia
| clear - hT1 CR0; img_lia
| clear - hC1 CR0; img_lia
| clear - hK1 hK3 EP ER NN1 P5 CR0; img_lia
| clear - hC1 hC2 hT1 hT2 DCT; img_lia
| clear - hC1 hC2 S1 S2 hS1 hS2 Usp DCS; img_lia
| clear - hT1 hT2 S1 S2 hS1 hS2 Usp DTS; img_lia
| clear - hC1 hC2 hK1 hK2 hK3 EP ER NN1 P5 DCP; img_lia
| clear - hT1 hT2 hK1 hK2 hK3 EP ER NN1 P5 DTP; img_lia
| clear - S1 S2 hS1 hS2 Usp hK1 hK2 hK3 EP ER NN1 P5 DSP; img_lia ].
Qed.
Lemma FACTS_ok : atoms_ok E0 (f_atoms YF6n.FFM).
Proof.
pose proof HI as (hP1 & hP2 & hQ1 & hQ2 & hT1 & hT2 & hF1 & hF2 & hNB1 & hNB2 & hSB1 & hSB2 & hC1 & hC2 & hS1 & hS2 & hSP1 & hSP2 & hK1 & hK2 & hK3 & _). unfold zone3 in hQ1, hT1, hF1, hNB1, hSB1, hC1, hK1.
pose proof HSP as [S1 S2]. pose proof (lo_top ly LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct PRE as (_ & _ & _ & Hal & _). unfold spZ in Hal. fold sp0 in Hal.
pose proof p_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14).
pose proof QB_facts as (Qa & Qb & Q8). pose proof HB1 as [HBR _].
pose proof junk_vals as (_ & J1R & _ & J2R). pose proof j3_val as [_ J3R].
pose proof (lo_space_al ly LO) as SAL. pose proof (lo_T_al ly LO) as TAL. pose proof (lo_C_al ly LO) as CAL. unfold page_aligned in TAL, T3.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, kHighShadowBeg, kQuarantineCacheMax, EV_MAX, ASTACK in
hP1, hP2, hQ1, hQ2, hT1, hT2, hF1, hF2, hNB1, hNB2, hSB1, hSB2, hC1, hC2, hS1, hS2, hSP1, hSP2, hK1, hK2, S1, S2, T2, T4, T7, P1, P2, P11, P12.
assert (E2' : ew E0 2 = w64 sp0) by (img_try (rewrite E2; unfold sp0, w64; symmetry; img_apply Z_to_bv_bv_unsigned)).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
assert (AF : forall k X lo hi al, ew E0 k = w64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k (mkAF lo hi al)).
{ clear. intros k X lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by img_exact HX. repeat split; img_lia. }
cbn [YF6n.FFM f_atoms atoms_ok]. unfold aSB, aSHB, aC, aT, aTOP, aLEN, aIM, aHW, aN, aSP, aN8, aCNT8, aQB, aJ1, aJ2, aJ3.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, ASTACK.
split. { img_apply (AF 2%nat sp0); [img_try (img_exact E2')| | | |]. all: clear - CR0 Usp S1 S2 hS1 hS2 T4 Hal; first [img_lia | img_change (2 ^ 4) with 16; img_exact Hal]. }
split. { img_apply (AF 10%nat pa); [img_try (img_exact E10)| | | |].
all: clear - CR0 P1 P2 P3 P5; first [img_lia | img_change (2 ^ 4) with 16; img_exact P3 | apply Z.mod_divide in P3 as [c Hc]; [|img_lia]; img_lia]. }
split. { img_apply (AF 32%nat T); [img_try (img_exact EaT)| | | |]. all: clear - CR0 hT1 hT2 TAL; first [img_lia | img_exact TAL]. }
split. { img_apply (AF 33%nat (ly_C ly)); [img_try (img_exact EaC)| | | |]. all: clear - CR0 hC1 hC2 CAL; first [img_lia | img_exact CAL]. }
split. { img_apply (AF 34%nat SB); [img_try (img_exact EaSB)| | | |]. all: clear - CR0 hSP1 hSP2 hP1 hP2 SAL; first [img_lia | img_exact SAL]. }
split. { img_apply (AF 35%nat (ly_top ly)); [img_try (img_exact EaTOP)| | | |]. all: clear - CR0 T1 T2 T3 T4 T7 hS1; unfold ly_bot, kStackSpan in *; first [img_lia | img_exact T3]. }
split. { img_apply (AF 36%nat LENv); [img_try (img_exact EaLEN)| | | |]. all: clear - CR0 P8; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 37%nat IMv); [img_try (img_exact EaIM)| | | |]. all: clear - CR0 P9 P10; first [img_lia | img_change (2 ^ 3) with 8; img_exact P10]. }
split. { img_apply (AF 38%nat HWv); [img_try (img_exact EaHW)| | | |]. all: clear - CR0 HBR; unfold YF6n.HWv; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 39%nat nn); [img_try (img_exact EaN)| | | |]. all: clear - CR0 Q8; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 40%nat SHADOW_OFF); [img_try (img_exact EaSHB)| | | |]. all: clear; unfold SHADOW_OFF; first [img_lia | img_refl]. }
split. { img_apply (AF 41%nat SPv); [img_try (img_exact EaSP)| | | |]. all: unfold YF6n.SPv, SHADOW_OFF in *; clear - CR0 P1 P2 P5 P11 P12 P13 P14 Q8; first [img_lia | img_change (2 ^ 1) with 2; img_exact P13 | rewrite P14 in P12; pose proof (Z.div_pos (nn + 7) 8); nia]. }
split. { img_apply (AF 42%nat N8v); [img_try (img_exact EaN8)| | | |]. all: clear - CR0 P5 P6 P7 Q8; first [img_lia | img_change (2 ^ 3) with 8; img_exact P7 | apply Z.mod_divide in P7 as [c Hc]; [|img_lia]; img_lia]. }
split. { img_apply (AF 43%nat CNT8v); [img_try (img_exact EaCNT8)| | | |]. all: clear - CR0 P5 P6 P14 Q8; rewrite ?P14 in *; unfold YF6n.N8v in *; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r | nia]. }
split. { img_apply (AF 50%nat QBFv); [img_try (img_exact EaQBF)| | | |]. all: clear - CR0 Qa Qb Q8; unfold YF6n.QBFv, YF6n.QBMAX, kQuarantineCacheMax, kBatchBytes in *; first [destruct (need_new_batch q); img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 51%nat j1); [img_try (img_exact EaJ1)| | | |]. all: clear - CR0 J1R; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split. { img_apply (AF 52%nat j2); [img_try (img_exact EaJ2)| | | |]. all: clear - CR0 J2R; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
split; [|img_try (img_exact I)]. { img_apply (AF 53%nat j3); [img_try (img_exact EaJ3)| | | |]. all: clear - CR0 J3R; first [img_lia | img_change (2 ^ 0) with 1; img_apply Z.mod_1_r]. }
Qed.
Lemma SEED_ok : st_ok tfxsegs E0 YF6n.SS0 (restrict (w_H W) (mkst regs (w64 (0x53100 + D_2c4)) mem (seg_rom tfxsegs))).
Proof.
destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Htp & _). rewrite (ts_tp _ TB) in Htp.
rewrite restrict_mkst_fx. unfold YF6n.SS0, YF6n.E0, w64. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_pin; [img_try (img_apply regs_ok_Ereg) | img_try (intros X; discriminate) | img_try (cbn [sv_denot]; img_exact Htp)].
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem mkst]. img_exact REG0_ok.
- img_exact PAIRS_ok.
- split; [img_try (img_exact FACTS_ok) | img_try (split; img_exact I)].
Qed.
Theorem FH_ok : YF6n.free_hyps W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S).
Proof.
pose proof PRE as PRE'. destruct PRE' as ((MM & _ & _) & Hev & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQT). unfold spZ, raZ, s0Z in *. fold sp0 in Hal, Hlo, Hbot, Hhi, HPRES, Hch.
pose proof kk_facts as (_ & Hk & Hst & Hu & Hr). pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). pose proof Epa as EP.
pose proof (YF1f.ext_rounded B ly S rd0 M kk Hk) as (ER & NN1 & NN2 & NN3). rewrite <- Enn in ER, NN1, NN2, NN3.
pose proof p_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14).
pose proof QB_facts as (Qa & Qb & Q8). pose proof HB1 as [HBR HBM].
pose proof junk_vals as (_ & J1R & _ & J2R). pose proof j3_val as [_ J3R]. pose proof HI as HH.
constructor.
- img_exact LO.
- img_exact HA0.
- rewrite (ts_tp _ TB) in Htp. img_exact Htp.
- img_exact Hra.
- destruct Hch as [R4096 _]. img_exact R4096.
- splits; img_lia.
- img_exact Hal.
- destruct Hch as [_ CH]. unfold frame0_ok, spZ, s0Z in CH. fold sp0 in CH. img_exact CH.
- img_exact p_zone.
- img_exact IMG.
- img_exact P3.
- img_exact Q8.
- img_exact HBR.
- img_exact HBM.
-   intros a Ha.
pose proof (YF0u.anyX B ly S rd0 M kk 8 _ Hk eq_refl ltac:(img_lia)) as D7. pose proof (YF0u.anyX B ly S rd0 M kk 2 _ Hk eq_refl ltac:(img_lia)) as D2.
pose proof (YF0u.anyX B ly S rd0 M kk 6 _ Hk eq_refl ltac:(img_lia)) as D6. pose proof (YF0u.anyX B ly S rd0 M kk 4 _ Hk eq_refl ltac:(img_lia)) as D4.
pose proof (YF0u.anyX B ly S rd0 M kk 5 _ Hk eq_refl ltac:(img_lia)) as D5. pose proof (YF0u.anyX B ly S rd0 M kk 7 _ Hk eq_refl ltac:(img_lia)) as DD.
unfold zdisjoint in D7, D2, D6, D4, D5, DD. cbn [fst snd] in D7, D2, D6, D4, D5, DD. clear - Ha D7 D2 D6 D4 D5 DD EP ER G5 P5. unfold YF6n.N8v in *. splits; img_lia.
-   intros a Ha. img_apply vis_apresent_off; [img_try (img_exact (zone3_off_img _ _ a p_zone ltac:(clear - Ha P5 P6; img_lia)))|].
destruct (Z_lt_le_dec a pa); [img_try (img_apply meta_vis; img_lia) | img_try (img_apply user_vis; img_lia)].
-   intros a Ha. destruct (shadow_vis (a - SPv) ltac:(img_lia)) as [v Hv]. replace (SPv + (a - SPv)) with a in Hv by img_lia.
img_apply vis_apresent; [img_try (unfold SHADOW_OFF, kHighMemBeg, TFX_IMG_END in *; img_lia) | img_try (rewrite Hv; discriminate)].
- split; [img_try (img_exact Qa) | img_try (img_exact Qb)].
- splits; img_lia.
- pose proof ial_vals as IV. img_exact IV.
- img_exact IA1.
- img_exact U1.
- img_exact SEED_ok.
Qed.
Let s1 : astate := set_internal_inited true (set_nev (st_nev S + 1) S).
Let kk' : chunk := mkChunk (ck_beg kk) (ck_req kk) CQuarantined.
Lemma CONST_OUT : Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) ->
~ YF6n.WIN ly regs pa (aeval B ly (c_at c) + i) /\ ~ YF6n.IZONE (aeval B ly (c_at c) + i) /\
0 <= aeval B ly (c_at c) + i < 2 ^ 64) (as_const B ly).
Proof.
rewrite (ts_const _ TB). img_apply Forall_forall. intros c Hc i Hi. pose proof FH_ok as FH.
pose proof (proj1 (forallb_forall _ _) (YF6e.Tfx_const_loc ly) c Hc) as K. unfold YF6e.const_loc_ok in K.
assert (LOW : forall a, YF6e.low_ok a (Z.max 1 (Z.of_nat (c_w c))) = true -> ~ YF6n.WIN ly regs pa (a + i) /\ ~ YF6n.IZONE (a + i) /\ 0 <= a + i < 2 ^ 64).
{ intros a L. unfold YF6e.low_ok in L. set (w := Z.max 1 (Z.of_nat (c_w c))) in *.
assert (R : (TFX_IMG_LO <= a /\ a + w <= TFX_IAL_LO) \/ (TFX_IAL_HI <= a /\ a + w <= TFX_IAL_FLAG) \/ (TFX_IAL_FLAG + 4 <= a /\ a + w <= TFX_IMG_END) \/
(SHADOW_OFF + TFX_IMG_LO / 8 <= a /\ a + w <= SHADOW_OFF + TFX_IMG_END / 8)) by img_lia.
clear L. unfold YF6n.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG, TFX_IMG_LO, TFX_IMG_END, SHADOW_OFF in *.
img_change (65536 / 8) with 8192 in R. img_change ((6287360 + D_1000) / 8) with (785920 + D_200) in R.
split; [|img_lia]. destruct R as [R|[R|[R|R]]].
1-3: img_apply (YF6n.notWIN_img W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH); unfold TFX_IMG_LO, TFX_IMG_END; img_lia.
img_apply (YF6n.notWIN_shb W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH); unfold kLowShadowBeg, kHighMemBeg; img_lia. }
destruct (c_at c); try discriminate K; cbn [aeval].
- apply LOW, K.
- pose proof (YF6n.LYB W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH) as (LB & _). ceil; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in LB.
split; [img_try (img_apply (YF6n.notWIN_Thead W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH); img_lia)|].
unfold YF6n.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG. img_lia.
- pose proof (YF6n.LYB W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH) as (_ & _ & _ & _ & _ & _ & LB & _). ceil; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in LB.
split; [img_try (img_apply (YF6n.notWIN_C W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH); img_lia)|].
unfold YF6n.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG. img_lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- pose proof (YF6n.LYBD W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH) as (HD1 & HD2 & _). ceil; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HD1, HD2.
split; [img_try (img_apply (YF6n.notWIN_D W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH); img_lia)|].
unfold YF6n.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG. img_lia.
Qed.
Lemma DFP_RANGE : forall a, depot_footprint B ly a -> 0 <= a < 2 ^ 64.
Proof.
pose proof (YF6n.LYB W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH_ok) as LB.
intros a Ha. unfold depot_footprint in Ha. rewrite (ts_depot _ TB), (ts_store _ TB) in Ha.
ceil; unfold zone3, TFX_DEPOT, TFX_STORE, d_map1, kHighMemBeg, ASAN_CEIL, kNodesBlockSize, kStoreBlockSize in *. img_lia.
Qed.
Lemma DFP_OUT : forall a, depot_footprint B ly a -> ~ YF6n.WIN ly regs pa a /\ ~ YF6n.IZONE a /\ YF6n.DZONE ly a.
Proof.
pose proof FH_ok as FH. pose proof (YF6n.LYB W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH) as LB.
intros a Ha. unfold depot_footprint in Ha. rewrite (ts_depot _ TB), (ts_store _ TB) in Ha. unfold YF6n.IZONE, YF6n.DZONE.
pose proof LB as (_ & _ & _ & _ & _ & _ & _ & _ & ZNB & _ & ZSB & _). unfold zone3, zone3cases in ZNB, ZSB.
ceil; unfold zone3, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, TFX_DEPOT, TFX_STORE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG, d_map1, kHighMemBeg, ASAN_CEIL, kNodesBlockSize, kStoreBlockSize in *.
destruct Ha as [Ha|[Ha|[Ha|Ha]]].
- split; [img_try (img_apply (YF6n.notWIN_img W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH); unfold TFX_IMG_LO, TFX_IMG_END; img_lia) | img_lia].
- split; [img_try (img_apply (YF6n.notWIN_NB W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH); unfold kNodesBlockSize; img_lia) | img_lia].
- split; [img_try (img_apply (YF6n.notWIN_SB W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH); unfold kStoreBlockSize; img_lia) | img_lia].
- split; [img_try (img_apply (YF6n.notWIN_img W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH); unfold TFX_IMG_LO, TFX_IMG_END; img_lia) | img_lia].
Qed.
Lemma CONST_ZONE : Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) ->
~ (YF6n.SPv pa <= aeval B ly (c_at c) + i < YF6n.SPv pa + YF6n.CNT8v nn)) (as_const B ly).
Proof.
pose proof FH_ok as FH.
rewrite (ts_const _ TB). img_apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (forallb_forall _ _) (YF6e.Tfx_const_loc ly) c Hc) as K. unfold YF6e.const_loc_ok in K.
pose proof (YF6n.LYB W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH) as (ZT & _ & _ & _ & _ & _ & ZC & _).
pose proof (YF6n.LYBD W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH) as (ZD & _).
pose proof (YF6n.derived_ranges W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH) as (_ & _ & SH1 & SH2 & SH3 & P8 & N81 & N82 & N83 & _).
pose proof (YF6n.fh_Hp _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as (_ & _ & ZP).
unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize, YF6n.N8v in ZT, ZC, ZD, ZP.
unfold YF6n.CNT8v, YF6n.N8v in *. rewrite SH3 in *. ceil. unfold ASAN_CEIL, kHighMemBeg, SHADOW_OFF in *.
assert (LOW : forall a, YF6e.low_ok a (Z.max 1 (Z.of_nat (c_w c))) = true -> ~ (2147450880 + pa / 8 <= a + i < 2147450880 + pa / 8 + (nn + 7) / 8 * 8 / 8)).
{ intros a L. unfold YF6e.low_ok in L. set (w := Z.max 1 (Z.of_nat (c_w c))) in *.
assert (R : (TFX_IMG_LO <= a /\ a + w <= TFX_IAL_LO) \/ (TFX_IAL_HI <= a /\ a + w <= TFX_IAL_FLAG) \/ (TFX_IAL_FLAG + 4 <= a /\ a + w <= TFX_IMG_END) \/
(SHADOW_OFF + TFX_IMG_LO / 8 <= a /\ a + w <= SHADOW_OFF + TFX_IMG_END / 8)) by img_lia.
clear L K. unfold TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG, TFX_IMG_LO, TFX_IMG_END, SHADOW_OFF in R. img_change (65536 / 8) with 8192 in R. img_change ((6287360 + D_1000) / 8) with (785920 + D_200) in R.
assert (R' : (65536 <= a /\ a + w <= (6287360 + D_1000)) \/ (2147450880 + 8192 <= a /\ a + w <= 2147450880 + (785920 + D_200))) by (img_try (clear - R; img_lia)). clear R. rename R' into R.
rewrite Z_div_mult in * by img_lia. pose proof (Z.div_pos pa 8 ltac:(img_lia) ltac:(img_lia)).
destruct R as [R|R]; [img_lia|].
destruct ZP as [Z1|[Z2|Z3]].
- assert (Y : (pa + (nn + 7) / 8 * 8) / 8 <= 65536 / 8) by (img_try (img_apply Z.div_le_mono; img_lia)). rewrite Z.div_add in Y by img_lia. img_change (65536 / 8) with 8192 in Y. img_lia.
- assert (Y : (6287360 + D_1000) / 8 <= pa / 8) by (img_try (img_apply Z.div_le_mono; img_lia)). img_change ((6287360 + D_1000) / 8) with (785920 + D_200) in Y. img_lia.
- assert (Y : 17594333495296 / 8 <= pa / 8) by (img_try (img_apply Z.div_le_mono; img_lia)). img_change (17594333495296 / 8) with 2199291686912 in Y. img_lia. }
rewrite Z_div_mult in * by img_lia. pose proof (Z.div_pos pa 8 ltac:(img_lia) ltac:(img_lia)).
destruct (c_at c); try discriminate K; cbn [aeval]; try (apply LOW, K).
- clear LOW. assert (Y : (pa + (nn + 7) / 8 * 8) / 8 <= 140737479966720 / 8) by (img_try (img_apply Z.div_le_mono; img_lia)). rewrite Z.div_add in Y by img_lia. img_change (140737479966720 / 8) with 17592184995840 in Y. img_lia.
- clear LOW. assert (Y : (pa + (nn + 7) / 8 * 8) / 8 <= 140737479966720 / 8) by (img_try (img_apply Z.div_le_mono; img_lia)). rewrite Z.div_add in Y by img_lia. img_change (140737479966720 / 8) with 17592184995840 in Y. img_lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- clear LOW. assert (Y : (pa + (nn + 7) / 8 * 8) / 8 <= 140737479966720 / 8) by (img_try (img_apply Z.div_le_mono; img_lia)). rewrite Z.div_add in Y by img_lia. img_change (140737479966720 / 8) with 17592184995840 in Y. img_lia.
Qed.
Lemma val_mem_aview : forall H m a (w : nat) v k0, val_mem tfxsegs (mrestrict H m) a w v -> (k0 < w)%nat ->
aview tfxsegs H m (a + Z.of_nat k0) = Some (YG0h.le_byte v w k0).
Proof.
intros H m a w v k0 Hv Hk. unfold aview. rewrite (Hv k0 Hk). cbn [option_map]. img_change (YG0h.le_byte v w k0) with (YP0g.le_byte v w k0). f_equal. img_apply unsigned_lit_small8.
unfold YP0g.le_byte. img_apply Z.mod_pos_bound. img_lia.
Qed.
Lemma ENQ_PRE : forall z (msD : machine_state) mem4 msE matE E5,
aok s1 (KDepot tr) z ->
YF6n.MEQI W ly regs mem pa (ms_mem msD) ->
(forall x : word, ~ (sp0 - 2256 - DEP_STK <= bv_unsigned x < sp0 - 2256) -> ~ depot_footprint B ly (bv_unsigned x) -> mem4 x = ms_mem msD x) ->
depot_mem_ok B ly (depot_after z tr s1) (aview tfxsegs (w_H W) mem4) ->
Forall (cell_holds B ly (aview tfxsegs (w_H W) mem4)) (as_const B ly) ->
msE = mkst (ms_regs msE) (w64 (0x35dd8 + D_150)) (ms_mem msE) (seg_rom tfxsegs) ->
(forall k0, (k0 < aHAVf)%nat -> ew E5 k0 = ew E0 k0) ->
st_ok tfxsegs E5 SS_E (restrict (w_H W) msE) ->
YF6l.EQS ly regs pa nn mem4 (ms_mem msE) ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem msE) a) ->
enq_pre B ly (YF1f.S' S kk z tr) W (ms_regs msE) (ms_mem msE) (with_vm_backing (m_vm_lazy md) matE md) kk'.
Proof.
intros z msD mem4 msE matE E5 AOK MEQD Hfr4 DEPOK HC4 HshE HEn5 HS EQE PRESE.
destruct PRE as (HAR & Hev & Hra & Hal & Hlo & Hbot & Hhi & HPRES & Hgp & Htp & Hch & HQT). destruct HAR as (M' & LED & BUD & MW & HSH). clear M'.
pose proof kk_facts as (Hf & Hk & Hst & Hu & Hr). pose proof KF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). pose proof Epa as EP.
pose proof (YF1f.ext_rounded B ly S rd0 M kk Hk) as (ER & NN1 & NN2 & NN3). rewrite <- Enn in ER, NN1, NN2, NN3.
pose proof HB1 as [HBR HBM]. pose proof HSP as HSP'. pose proof p_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14).
pose proof QB_facts as (Qa & Qb & Q8).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
pose proof FH_ok as FH. pose proof (YF6n.LYB W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH) as LB.
set (rd := aview tfxsegs (w_H W) mem) in *. set (rd' := aview tfxsegs (w_H W) (ms_mem msE)).
assert (EM : forall lo hi a, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (img_try (intros; img_lia)).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ YF1f.D B ly kk sp0 a -> rd' a = rd a).
{ intros a Ha ND. (subst rd rd'; cbv beta). img_apply aview_same.
assert (Ux : bv_unsigned (Z_to_bv 64 a) = a) by (img_try (img_apply unsigned_lit_small; img_exact Ha)).
unfold YF1f.D, YF1f.DT, YF1f.DK, YF1f.DS, YF1f.DI, YF1f.DH in ND. rewrite Hu, <- Enn in ND. img_change (sptr_addr B ly p) with pa in ND.
assert (NW : ~ YF6n.WIN ly regs pa a).
{ intros X. img_apply ND. clear ND. unfold YF6n.WIN, YF6n.WINT, YF6n.WINB in X. fold sp0 in X.
destruct X as [X|[X|X]]; [img_try (do 2 right; left; img_exact X) | img_try (left; clear - X; img_lia) | img_try (right; left; img_exact X)]. }
rewrite (proj1 EQE (Z_to_bv 64 a)); rewrite ?Ux.
2:{ intros X. img_apply NW. img_exact (YF6n.WIN2_WIN ly regs pa a X). }
2:{ intros X. img_apply ND. do 5 right. clear - X NN2. unfold YF6n.SPv, YF6n.CNT8v, YF6n.N8v, shadow_addr in *. rewrite Z_div_mult in X by img_lia. img_lia. }
rewrite Hfr4; rewrite ?Ux.
2:{ intros X. img_apply ND. do 2 right; left. clear - X. unfold DEP_STK, ASTACK in *. img_lia. }
2:{ intros X. img_apply ND. do 4 right; left; img_exact X. }
img_apply (proj1 MEQD); rewrite ?Ux; [img_try (img_exact NW)|].
intros X. img_apply ND. do 3 right; left. unfold YF6n.IZONE in X. rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB). img_exact X. }
assert (VIS : forall a, rd a <> None -> rd' a <> None).
{ intros a Hv HN. (subst rd rd'; cbv beta). unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W x) eqn:Hx; [img_try (img_exact (Hv HN))|].
destruct (seg_rom tfxsegs x) eqn:ROM; [img_try (destruct (ms_mem msE x); discriminate)|].
destruct (ms_mem msE x) as [|] eqn:E'; [img_try (discriminate)|]. clear HN.
destruct (mem x) as [b0|] eqn:EE0; [img_try (clear Hv) | img_try (img_exact (Hv eq_refl))].
set (a' := bv_unsigned x). assert (Ha' : 0 <= a' < 2 ^ 64) by (img_try ((subst a'; cbv beta); img_apply u64_range)).
assert (Ex : Z_to_bv 64 a' = x) by (img_try ((subst a'; cbv beta); img_apply Z_to_bv_bv_unsigned)).
assert (NIMG : ~ (0x10000 <= a' < (0x5ff000 + D_1000))).
{ intros X. img_apply (tfx_rom_all a' X). rewrite Ex. img_exact ROM. }
assert (PRX : forall m, apresent (w_H W) m a' -> m x = None -> False).
{ intros m [_ [bb Hb]] Hm. rewrite Ex in Hb. congruence. }
destruct (EM (YF6n.SPv pa) (YF6n.SPv pa + YF6n.CNT8v nn) a') as [C1|C1].
{ rewrite (proj2 EQE x C1) in E'. discriminate. }
destruct (EM (sp0 - ASTACK) sp0 a') as [C0|C0]. { img_exact (PRX _ (PRESE a' C0) E'). }
assert (WPRES : forall i r, nth_error (ss_mem SS_E) i = Some r ->
base_val E5 (YQ0b.r_base r) + YQ0b.r_wlo r <= a' < base_val E5 (YQ0b.r_base r) + YQ0b.r_whi r -> off_img a' -> False).
{ intros i r Hi Hrr Hh. img_exact (PRX _ (st_ok_window_apresent_off (w_H W) E5 _ _ i r a' HS Hi Hrr Hh) E'). }
assert (BT : bv_unsigned (ew E5 32) = ly_T ly) by (img_try (rewrite (HEn5 32%nat ltac:((img_case; cbv); img_lia)), EaT; unfold w64; img_apply unsigned_lit_small; pose proof LB as (LB1 & _); clear - LB1; ceil; unfold zone3, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; img_lia)).
assert (B10 : bv_unsigned (ew E5 10) = pa) by (img_try (rewrite (HEn5 10%nat ltac:((img_case; cbv); img_lia)), E10; unfold w64; img_apply unsigned_lit_small; clear - P1 P2 P5; ceil; unfold kHighMemBeg, ASAN_CEIL in *; img_lia)).
destruct (EM (ly_T ly + t_unwinding) (ly_T ly + t_unwinding + 1) a') as [C2|C2].
{ eapply (WPRES 34%nat); [img_refl | img_try (cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite BT; clear - C2; unfold t_unwinding in *; img_lia) | img_try (pose proof LB as (ZT & _); img_apply (zone3_off_img _ _ a' ZT); clear - C2; unfold kThreadObjSize, t_unwinding in *; img_lia) ]. }
destruct (EM (ly_T ly + t_stats + 24) (ly_T ly + t_stats + 40) a') as [C3|C3].
{ eapply (WPRES 35%nat); [img_refl | img_try (cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite BT; clear - C3; unfold t_stats in *; img_lia) | img_try (pose proof LB as (ZT & _); img_apply (zone3_off_img _ _ a' ZT); clear - C3; unfold kThreadObjSize, t_stats in *; img_lia) ]. }
destruct (EM (pa - 16) (pa - 8) a') as [C4|C4].
{ eapply (WPRES 36%nat); [img_refl | img_try (cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite B10; clear - C4; img_lia) | img_try (img_apply (zone3_off_img _ _ a' p_zone); clear - C4 P5; unfold YF6n.N8v in *; img_lia) ]. }
destruct (EM pa (pa + 8) a') as [C5|C5].
{ eapply (WPRES 37%nat); [img_refl | img_try (cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite B10; clear - C5; img_lia) | img_try (img_apply (zone3_off_img _ _ a' p_zone); clear - C5 P5; unfold YF6n.N8v in *; img_lia) ]. }
assert (NW : ~ YF6n.WIN ly regs pa a').
{ unfold YF6n.WIN, YF6n.WINT, YF6n.WINB. fold sp0. clear - C0 C2 C3 C4 C5. intros [X|[[X|X]|[X|X]]]; eauto. }
assert (E4 : mem4 x = None).
{ rewrite <- E'. symmetry. img_apply (proj1 EQE x); [img_try (intros X; img_apply NW; img_exact (YF6n.WIN2_WIN ly regs pa a' X)) | img_try (img_exact C1)]. }
assert (EMD : depot_footprint B ly a' \/ ~ depot_footprint B ly a') by (img_try (unfold depot_footprint; clear - EM;
destruct (EM (as_depot B) (as_depot B + d_map1 + 8 * 32768) a'); [img_try (tauto)|]; destruct (EM (ly_NB ly) (ly_NB ly + kNodesBlockSize) a'); [img_try (tauto)|];
destruct (EM (ly_SB ly) (ly_SB ly + kStoreBlockSize) a'); [img_try (tauto)|]; destruct (EM (as_store B) (as_store B + 64) a'); tauto)).
destruct EMD as [C6|C6].
{ destruct DEPOK as (_ & _ & DV). rewrite Forall_forall in DV.
assert (BLK : forall e len, In (e, len) [(ADepot (d_nuniq + 4), 12); (AStore 8, 8); (AStore 24, 8); (ANB 0, kNodesBlockSize); (ASB 0, kStoreBlockSize)] ->
aeval B ly e <= a' < aeval B ly e + len -> False).
{ intros e len Hin Hrg. pose proof (DV _ Hin (a' - aeval B ly e) ltac:(img_try (cbn [fst snd]; img_lia))) as V. cbn [fst snd] in V.
replace (aeval B ly e + (a' - aeval B ly e)) with a' in V by img_lia. img_apply V. unfold aview, mbyte, mrestrict. rewrite Ex, Hx, E4, ROM. img_refl. }
unfold depot_footprint in C6. rewrite (ts_depot _ TB), (ts_store _ TB) in C6. unfold TFX_DEPOT, TFX_STORE, d_map1 in C6.
destruct C6 as [C6|[C6|[C6|C6]]].
- img_apply NIMG. img_lia.
- img_apply (BLK (ANB 0) kNodesBlockSize); [img_try (cbn; tauto) | img_try (cbn [aeval]; img_lia)].
- img_apply (BLK (ASB 0) kStoreBlockSize); [img_try (cbn; tauto) | img_try (cbn [aeval]; img_lia)].
- img_apply NIMG. img_lia. }
assert (ED : ms_mem msD x = None).
{ rewrite <- E4. symmetry. img_apply Hfr4; [|img_try (img_exact C6)]. intros X. img_apply C0. clear - X. unfold DEP_STK, ASTACK in *. (subst a'; cbv beta). fold sp0. img_lia. }
destruct (EM TFX_IAL_LO TFX_IAL_HI a') as [C7|C7]; [img_try (img_apply NIMG; unfold TFX_IAL_LO, TFX_IAL_HI in C7; img_lia)|].
destruct (EM TFX_IAL_FLAG (TFX_IAL_FLAG + 4) a') as [C8|C8]; [img_try (img_apply NIMG; unfold TFX_IAL_FLAG in C8; img_lia)|].
rewrite (proj1 MEQD x) in ED; [img_try (congruence) | img_try (img_exact NW) | img_try (unfold YF6n.IZONE; tauto)]. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> ms_mem msE (w64 a) = mem (w64 a)).
{ intros a0 Hb Hx0. assert (Ha0 : kLowShadowBeg <= a0 < kHighShadowEnd) by (img_try (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; img_lia)). clear Hb.
unfold w64 in *. set (x := Z_to_bv 64 a0) in *.
assert (Hx : w_H W x = true) by img_exact Hx0. clear Hx0.
assert (ROM : seg_rom tfxsegs x = None) by (img_try ((subst x; cbv beta); img_apply seg_rom_none_high; clear - Ha0; unfold TFX_IMG_END, kLowShadowBeg, kHighShadowEnd in *; img_lia)).
set (a' := bv_unsigned x). assert (Ha' : 0 <= a' < 2 ^ 64) by (img_try ((subst a'; cbv beta); img_apply u64_range)).
assert (Ex : Z_to_bv 64 a' = x) by (img_try ((subst a'; cbv beta); img_apply Z_to_bv_bv_unsigned)).
assert (NIMG : ~ (0x10000 <= a' < (0x5ff000 + D_1000))).
{ intros X. img_apply (tfx_rom_all a' X). rewrite Ex. img_exact ROM. }
assert (PRX : forall m, apresent (w_H W) m a' -> False).
{ intros m [Hh _]. rewrite Ex, Hx in Hh. discriminate. }
destruct (EM (YF6n.SPv pa) (YF6n.SPv pa + YF6n.CNT8v nn) a') as [C1|C1].
{ exfalso. img_exact (PRX mem (fh_Hsh_pres _ _ _ _ _ _ _ _ _ _ _ _ _ FH a' C1)). }
destruct (EM (sp0 - ASTACK) sp0 a') as [C0|C0]. { exfalso. img_exact (PRX _ (PRESE a' C0)). }
assert (WPRES : forall i r, nth_error (ss_mem SS_E) i = Some r ->
base_val E5 (YQ0b.r_base r) + YQ0b.r_wlo r <= a' < base_val E5 (YQ0b.r_base r) + YQ0b.r_whi r -> off_img a' -> False).
{ intros i r Hi Hrr Hh. img_exact (PRX _ (st_ok_window_apresent_off (w_H W) E5 _ _ i r a' HS Hi Hrr Hh)). }
assert (BT : bv_unsigned (ew E5 32) = ly_T ly) by (img_try (rewrite (HEn5 32%nat ltac:((img_case; cbv); img_lia)), EaT; unfold w64; img_apply unsigned_lit_small; pose proof LB as (LB1 & _); clear - LB1; ceil; unfold zone3, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; img_lia)).
assert (B10 : bv_unsigned (ew E5 10) = pa) by (img_try (rewrite (HEn5 10%nat ltac:((img_case; cbv); img_lia)), E10; unfold w64; img_apply unsigned_lit_small; clear - P1 P2 P5; ceil; unfold kHighMemBeg, ASAN_CEIL in *; img_lia)).
destruct (EM (ly_T ly + t_unwinding) (ly_T ly + t_unwinding + 1) a') as [C2|C2].
{ exfalso. eapply (WPRES 34%nat); [img_refl | img_try (cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite BT; clear - C2; unfold t_unwinding in *; img_lia) | img_try (pose proof LB as (ZT & _); img_apply (zone3_off_img _ _ a' ZT); clear - C2; unfold kThreadObjSize, t_unwinding in *; img_lia) ]. }
destruct (EM (ly_T ly + t_stats + 24) (ly_T ly + t_stats + 40) a') as [C3|C3].
{ exfalso. eapply (WPRES 35%nat); [img_refl | img_try (cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite BT; clear - C3; unfold t_stats in *; img_lia) | img_try (pose proof LB as (ZT & _); img_apply (zone3_off_img _ _ a' ZT); clear - C3; unfold kThreadObjSize, t_stats in *; img_lia) ]. }
destruct (EM (pa - 16) (pa - 8) a') as [C4|C4].
{ exfalso. eapply (WPRES 36%nat); [img_refl | img_try (cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite B10; clear - C4; img_lia) | img_try (img_apply (zone3_off_img _ _ a' p_zone); clear - C4 P5; unfold YF6n.N8v in *; img_lia) ]. }
destruct (EM pa (pa + 8) a') as [C5|C5].
{ exfalso. eapply (WPRES 37%nat); [img_refl | img_try (cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val]; rewrite B10; clear - C5; img_lia) | img_try (img_apply (zone3_off_img _ _ a' p_zone); clear - C5 P5; unfold YF6n.N8v in *; img_lia) ]. }
assert (NW : ~ YF6n.WIN ly regs pa a').
{ unfold YF6n.WIN, YF6n.WINT, YF6n.WINB. fold sp0. clear - C0 C2 C3 C4 C5. intros [X|[[X|X]|[X|X]]]; eauto. }
assert (EMD : depot_footprint B ly a' \/ ~ depot_footprint B ly a') by (img_try (unfold depot_footprint; clear - EM;
destruct (EM (as_depot B) (as_depot B + d_map1 + 8 * 32768) a'); [img_try (tauto)|]; destruct (EM (ly_NB ly) (ly_NB ly + kNodesBlockSize) a'); [img_try (tauto)|];
destruct (EM (ly_SB ly) (ly_SB ly + kStoreBlockSize) a'); [img_try (tauto)|]; destruct (EM (as_store B) (as_store B + 64) a'); tauto)).
destruct EMD as [C6|C6].
{ exfalso. destruct DEPOK as (_ & _ & DV). rewrite Forall_forall in DV.
assert (BLK : forall e len, In (e, len) [(ADepot (d_nuniq + 4), 12); (AStore 8, 8); (AStore 24, 8); (ANB 0, kNodesBlockSize); (ASB 0, kStoreBlockSize)] ->
aeval B ly e <= a' < aeval B ly e + len -> False).
{ intros e len Hin Hrg. pose proof (DV _ Hin (a' - aeval B ly e) ltac:(img_try (cbn [fst snd]; img_lia))) as V. cbn [fst snd] in V.
replace (aeval B ly e + (a' - aeval B ly e)) with a' in V by img_lia. img_apply V. unfold aview, mbyte, mrestrict. rewrite Ex, ROM, Hx. img_refl. }
unfold depot_footprint in C6. rewrite (ts_depot _ TB), (ts_store _ TB) in C6. unfold TFX_DEPOT, TFX_STORE, d_map1 in C6.
destruct C6 as [C6|[C6|[C6|C6]]].
- img_apply NIMG. img_lia.
- img_apply (BLK (ANB 0) kNodesBlockSize); [img_try (cbn; tauto) | img_try (cbn [aeval]; img_lia)].
- img_apply (BLK (ASB 0) kStoreBlockSize); [img_try (cbn; tauto) | img_try (cbn [aeval]; img_lia)].
- img_apply NIMG. img_lia. }
destruct (EM TFX_IAL_LO TFX_IAL_HI a') as [C7|C7]; [img_try (exfalso; img_apply NIMG; unfold TFX_IAL_LO, TFX_IAL_HI in C7; img_lia)|].
destruct (EM TFX_IAL_FLAG (TFX_IAL_FLAG + 4) a') as [C8|C8]; [img_try (exfalso; img_apply NIMG; unfold TFX_IAL_FLAG in C8; img_lia)|].
rewrite (proj1 EQE x); [| img_try (intros X; img_apply NW; img_exact (YF6n.WIN2_WIN ly regs pa a' X)) | img_try (img_exact C1)].
rewrite (Hfr4 x); [| img_try (intros X; img_apply C0; clear - X; unfold DEP_STK, ASTACK in *; (subst a'; cbv beta); fold sp0; img_lia) | img_try (img_exact C6)].
img_apply (proj1 MEQD x); [img_try (img_exact NW) | img_try (unfold YF6n.IZONE; tauto)]. }
assert (BT : bv_unsigned (ew E5 32) = ly_T ly) by (img_try (rewrite (HEn5 32%nat ltac:((img_case; cbv); img_lia)), EaT; unfold w64; img_apply unsigned_lit_small; pose proof LB as (LB1 & _); clear - LB1; ceil; unfold zone3, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; img_lia)).
assert (B10 : bv_unsigned (ew E5 10) = pa) by (img_try (rewrite (HEn5 10%nat ltac:((img_case; cbv); img_lia)), E10; unfold w64; img_apply unsigned_lit_small; clear - P1 P2 P5; ceil; unfold kHighMemBeg, ASAN_CEIL in *; img_lia)).
assert (R38 : rho_of E5 38%nat = HWv) by (img_try (unfold rho_of; rewrite (HEn5 38%nat ltac:((img_case; cbv); img_lia)), EaHW; unfold w64; img_apply unsigned_lit_small; unfold YF6n.HWv; clear - HBR; img_lia)).
assert (T1V : zev (rho_of E5) T1term = 3 + 256 * hb1) by (img_try (img_apply T1_val; [img_try (img_exact HBR) | img_try (rewrite R38; img_refl)])).
assert (V1 : val_mem tfxsegs (mrestrict (w_H W) (ms_mem msE)) (pa - 16) 4 (3 + 256 * hb1)).
{ memv HS 36%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite B10; img_lia) | img_try (img_apply YF6k.denot_by_zev; [img_refl | clear - HBR; img_lia | img_exact T1V]) | img_try (clear - HBR; img_lia)]. }
assert (V2 : val_mem tfxsegs (mrestrict (w_H W) (ms_mem msE)) (pa - 12) 4 nn).
{ memv HS 36%nat 1%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite B10; img_lia) | img_try (cbn [sv_denot]; rewrite (HEn5 39%nat ltac:((img_case; cbv); img_lia)), EaN; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia) | img_try (clear - Q8; img_lia)]. }
assert (V7 : val_mem tfxsegs (mrestrict (w_H W) (ms_mem msE)) (ly_T ly + t_unwinding) 1 0).
{ memv HS 34%nat 0%nat; [img_try (cbn [base_val YQ0b.r_base]; rewrite BT; unfold t_unwinding; img_lia) | img_refl | img_lia]. }
assert (NEW_hdr : forall i, (i < 4)%nat -> rd' (sptr_addr B ly (ck_user kk) - 16 + Z.of_nat i) = Some (YG0h.le_byte (3 + 256 * hb1) 4 i)).
{ intros i Hi. (subst rd'; cbv beta). rewrite Hu. img_change (sptr_addr B ly p) with pa. img_exact (val_mem_aview _ _ _ _ _ i V1 Hi). }
assert (NEW_n : forall i, (i < 4)%nat -> rd' (sptr_addr B ly (ck_user kk) - 12 + Z.of_nat i) = Some (YG0h.le_byte (ck_n kk) 4 i)).
{ intros i Hi. (subst rd'; cbv beta). rewrite Hu, <- Enn. img_change (sptr_addr B ly p) with pa. img_exact (val_mem_aview _ _ _ _ _ i V2 Hi). }
assert (NEW_unw : rd' (ly_T ly + t_unwinding) = Some 0).
{ (subst rd'; cbv beta). rewrite <- (Z.add_0_r (ly_T ly + t_unwinding)). img_exact (val_mem_aview _ _ _ _ _ 0 V7 ltac:(img_lia)). }
assert (NEW_sh : forall a, YF1f.DH B ly kk a -> rd a <> None -> rd' a = Some shHeapFreed).
{ intros a Hd Hv. (subst rd rd'; cbv beta). unfold YF1f.DH in Hd. rewrite Hu, <- Enn in Hd. img_change (sptr_addr B ly p) with pa in Hd.
assert (Ha : 0 <= a < 2 ^ 64).
{ clear - Hd P1 P2 NN2 NN3. ceil; unfold YF6n.N8v, shadow_addr, SHADOW_OFF, kHighMemBeg, ASAN_CEIL in *.
pose proof (Z.div_pos pa 8 ltac:(img_lia) ltac:(img_lia)). pose proof (Z.div_le_upper_bound pa 8 pa ltac:(img_lia) ltac:(img_lia)). img_lia. }
unfold aview, mbyte, mrestrict in Hv |- *.
assert (ROM : seg_rom tfxsegs (Z_to_bv 64 a) = None).
{ img_apply seg_rom_none_high. unfold TFX_IMG_END. unfold shadow_addr, SHADOW_OFF in Hd. pose proof (Z.div_pos pa 8 ltac:(img_try (clear - P1; img_lia)) ltac:(img_lia)). img_lia. }
destruct (w_H W (Z_to_bv 64 a)) eqn:Hx; [img_try (rewrite ROM in Hv; exfalso; img_exact (Hv eq_refl))|].
rewrite (proj2 EQE (Z_to_bv 64 a)); [img_refl|]. rewrite unsigned_lit_small by img_exact Ha.
unfold YF6n.SPv, YF6n.CNT8v, YF6n.N8v. unfold shadow_addr in Hd. rewrite Z_div_mult by img_lia. img_exact Hd. }
assert (AGI : forall a, YF6n.IZONE a -> ms_mem msE (Z_to_bv 64 a) = ms_mem msD (Z_to_bv 64 a)).
{ intros a Hz. assert (Ha : 0 <= a < 2 ^ 64) by (img_try (unfold YF6n.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG in Hz; img_lia)).
assert (NW : ~ YF6n.WIN ly regs pa a).
{ img_apply (YF6n.notWIN_img W ly regs mem ch pa nn hb1 q j1 j2 j3 (st_internal_inited S) FH). clear - Hz. unfold YF6n.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG, TFX_IMG_LO, TFX_IMG_END in *. img_lia. }
rewrite (proj1 EQE (Z_to_bv 64 a)); rewrite ?unsigned_lit_small by img_exact Ha.
2:{ intros X. img_apply NW. img_exact (YF6n.WIN2_WIN ly regs pa a X). }
2:{ clear - Hz P11. unfold YF6n.IZONE, YF6n.SPv, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG, SHADOW_OFF in *. img_lia. }
img_apply Hfr4; rewrite ?unsigned_lit_small by img_exact Ha.
- pose proof (lo_top ly LO) as (_ & _ & _ & _ & _ & _ & T7). clear - Hz HSP' T7.
unfold YF6n.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG, kHighMemBeg, ASTACK, DEP_STK in *. img_lia.
- intros X. destruct (DFP_OUT a X) as (_ & NI & _). img_exact (NI Hz). }
assert (IAL : Forall (cell_holds B ly rd') (ialloc_cells B (YF1f.S' S kk z tr)) /\ Forall (range_zero B ly rd') (ialloc_zero B)).
{ destruct MEQD as [_ IP]. unfold YF6n.IAL_POST in IP. cbv zeta in IP. destruct IP as (I1 & I2 & I3 & I4 & I5).
assert (XF : forall a0 (w : nat) v, YF6n.IZONE a0 -> (forall k0, (k0 < w)%nat -> YF6n.IZONE (a0 + Z.of_nat k0)) ->
val_mem tfxsegs (mrestrict (w_H W) (ms_mem msD)) a0 w v -> val_mem tfxsegs (mrestrict (w_H W) (ms_mem msE)) a0 w v).
{ intros a0 w v _ Hz Hv. eapply val_mem_frame; [|img_try (img_exact Hv)]. intros k0 Hk0. apply AGI, Hz, Hk0. }
unfold ialloc_cells, ialloc_zero. rewrite (YF1f.S'_inited S kk z tr), (ts_ial_flag _ TB), (ts_ial_lo _ TB), (ts_ial_w _ TB), (ts_ial_hi _ TB).
assert (ZF : YF6n.IZONE TFX_IAL_FLAG /\ YF6n.IZONE (TFX_IAL_FLAG + 1) /\ (forall k0, (k0 < 8)%nat -> YF6n.IZONE (TFX_IAL_W + Z.of_nat k0)) /\
(forall k0, (k0 < 8)%nat -> YF6n.IZONE (TFX_IAL_W + 8 + Z.of_nat k0))).
{ unfold YF6n.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG, TFX_IAL_W. splits; intros; img_lia. }
destruct ZF as (Z1 & Z2 & Z3 & Z4). (subst rd'; cbv beta). split.
- img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros k0 Hk0. destruct k0; [|img_lia].
assert (ZZ : forall k0 : nat, (k0 < 1)%nat -> YF6n.IZONE (TFX_IAL_FLAG + Z.of_nat k0)) by (img_try (intros [|] ?; [img_try (rewrite Z.add_0_r; img_exact Z1) | img_try (exfalso; img_lia)])).
img_apply (val_mem_aview _ _ _ _ _ 0 (XF _ _ _ Z1 ZZ I1)). img_lia. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z1 c1 aeval]. intros k0 Hk0. destruct k0; [|img_lia].
assert (ZZ : forall k0 : nat, (k0 < 1)%nat -> YF6n.IZONE (TFX_IAL_FLAG + 1 + Z.of_nat k0)) by (img_try (intros [|] ?; [img_try (rewrite Z.add_0_r; img_exact Z2) | img_try (exfalso; img_lia)])).
img_apply (val_mem_aview _ _ _ _ _ 0 (XF _ _ _ Z2 ZZ I2)). img_lia. }
img_apply Forall_cons. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. rewrite (ts_ial_lo _ TB). replace (TFX_IAL_LO + (TFX_IAL_W - TFX_IAL_LO)) with TFX_IAL_W by img_lia.
intros k0 Hk0. pose proof (Z3 0%nat ltac:(lia)) as Z3_0; change (Z.of_nat 0) with 0 in Z3_0; rewrite Z.add_0_r in Z3_0. img_exact (val_mem_aview _ _ _ _ _ k0 (XF _ _ _ Z3_0 Z3 I3) Hk0). }
img_apply Forall_cons; [|img_try (img_apply Forall_nil)]. { cbn [cell_holds c_at c_val c_w z8 c8 aeval]. rewrite (ts_ial_lo _ TB). replace (TFX_IAL_LO + (TFX_IAL_W - TFX_IAL_LO + 8)) with (TFX_IAL_W + 8) by img_lia.
replace (TFX_IAL_LO + (TFX_IAL_W - TFX_IAL_LO + 16)) with (TFX_IAL_W + 16) by img_lia.
intros k0 Hk0. pose proof (Z4 0%nat ltac:(lia)) as Z4_0; change (Z.of_nat 0) with 0 in Z4_0; rewrite Z.add_0_r in Z4_0. img_exact (val_mem_aview _ _ _ _ _ k0 (XF _ _ _ Z4_0 Z4 I4) Hk0). }
- assert (ZR : forall a0, TFX_IAL_LO <= a0 < TFX_IAL_W \/ TFX_IAL_W + 16 <= a0 < TFX_IAL_HI -> aview tfxsegs (w_H W) (ms_mem msE) a0 = Some 0).
{ intros a0 Ha0. unfold aview. rewrite (mbyte_mrestrict_same (w_H W) (ms_mem msD) (ms_mem msE) a0).
- rewrite (I5 a0 Ha0). img_refl.
- img_apply AGI. unfold YF6n.IZONE, TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_W in *. img_lia. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_nil])]; intros i Hi; cbn [fst snd aeval] in Hi |- *; rewrite (ts_ial_lo _ TB); img_apply ZR; unfold TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_W in *; img_lia. }
assert (SHB : kLowShadowBeg <= YF6n.SPv pa /\ YF6n.SPv pa + YF6n.CNT8v nn <= kHighMemBeg) by (img_try (clear - P11 P12; unfold kLowShadowBeg, SHADOW_OFF in *; img_lia)).
assert (AG4 : forall a, 0 <= a < 2 ^ 64 -> ~ YF6n.WIN ly regs pa a -> ~ (YF6n.SPv pa <= a < YF6n.SPv pa + YF6n.CNT8v nn) ->
aview tfxsegs (w_H W) (ms_mem msE) a = aview tfxsegs (w_H W) mem4 a).
{ intros a Ha NW HZ. img_apply aview_same. img_apply (proj1 EQE); rewrite unsigned_lit_small by img_exact Ha; [|img_try (img_exact HZ)].
intros X. img_apply NW. img_exact (YF6n.WIN2_WIN ly regs pa a X). }
assert (DEP : depot_mem_ok B ly (depot_after z tr s1) rd').
{ eapply (YF6e.depot_mem_ok_agree B ly (depot_after z tr s1) (depot_after z tr s1)); [| img_try (img_exact (am_universe B ly S _ M)) | img_refl | | img_try (img_exact DEPOK)].
- img_apply (WfP_weaken _ 1 1 1); try img_lia. img_exact (YF1f.sd_wf B ly S rd M z tr Hev AOK HU).
- intros a Ha. (subst rd'; cbv beta).
pose proof LB as (_ & _ & _ & _ & _ & _ & _ & _ & ZNB & _ & ZSB & _).
img_apply AG4; [img_try (img_exact (DFP_RANGE a Ha)) | img_try (img_exact (proj1 (DFP_OUT a Ha))) |].
unfold depot_footprint in Ha. rewrite (ts_depot _ TB), (ts_store _ TB) in Ha. clear - Ha ZNB ZSB SHB.
unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, TFX_DEPOT, TFX_STORE, d_map1, kLowShadowBeg, kHighMemBeg, kNodesBlockSize, kStoreBlockSize in *. img_lia. }
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ img_apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly (aview tfxsegs (w_H W) mem4)); [img_try (img_exact (proj1 (Forall_forall _ _) HC4 c Hc))|].
intros i Hi. (subst rd'; cbv beta). destruct (proj1 (Forall_forall _ _) CONST_OUT c Hc i Hi) as (X1 & X2 & X3). img_apply AG4; [img_try (img_exact X3) | img_try (img_exact X1) |].
img_exact (proj1 (Forall_forall _ _) CONST_ZONE c Hc i Hi). }
pose proof (YF1f.free_mid_ARm B TB ly S rd rd' M kk hb1 Hk Hst (conj HBR HBM) z tr Hev AOK HU sp0 HSP' IMG AG VIS NEW_hdr NEW_n NEW_unw NEW_sh IAL DEP CONST') as MM.
pose proof (YF1f.abudget_step B ly S rd M kk Hk z tr) as BS.
rreg HS (1%bv : bv 5) Q1'. rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4.
rreg HS (10%bv : bv 5) Q10. rreg HS (11%bv : bv 5) Q11. rreg HS (13%bv : bv 5) Q13. rreg HS (14%bv : bv 5) Q14.
rewrite (HEn5 2%nat ltac:(img_try ((img_case; cbv); img_lia))), E2 in Q2. rewrite (HEn5 3%nat ltac:(img_try ((img_case; cbv); img_lia))), (YF6n.Er ly regs ch pa nn hb1 q j1 j2 j3 3 3%bv eq_refl) in Q3.
rewrite (HEn5 32%nat ltac:(img_try ((img_case; cbv); img_lia))), EaT in Q10, Q11. rewrite (HEn5 10%nat ltac:(img_try ((img_case; cbv); img_lia))), E10 in Q13. rewrite (HEn5 39%nat ltac:(img_try ((img_case; cbv); img_lia))), EaN in Q14.
assert (SPE : spZ (ms_regs msE) = sp0 - 2288).
{ unfold spZ. rewrite Q2. unfold sp0, w64. rewrite unsigned_lit_small by (img_try (clear - Usp Hlo LB; unfold spZ, kHighMemBeg, ASTACK in *; unfold sp0 in *; img_lia)). img_refl. }
unfold enq_pre. rewrite !SPE. unfold raZ. rewrite Q1'. splits.
- split; [img_try (img_exact MM) | img_try (split; [|split; [|split]])].
+ eapply ALedger_same; [img_try (img_exact (YF1f.ALedger_S' B ly S rd M kk Hk z tr tfxsegs md LED)) | img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_apply eager_used_wvb)].
+ destruct BUD as [BUD PIN]. split; [| img_try (img_exact (YF1f.asecA_S' B ly S rd M kk Hk z tr _ PIN))]. rewrite BS. clear - BUD. unfold EV_A. img_lia.
+ eapply amwf_same; [img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_exact MW)].
+ eapply (ahs_transfer tfxsegs B ly S _ (w_H W) mem (ms_mem msE) (al_img_env tfxsegs ly S md (am_layout B ly S _ M) LED) M HSH VIS HSK).
* eapply (aclient_band_same_frames B ly S); [img_try (img_exact MM) | img_try (first [img_exact (YF1f.frames' S kk z tr) | img_exact (YF1f.frames' B ly S kk z tr) | img_exact (YF1f.frames' B ly S rd M kk Hk z tr)])].
*   first [img_exact (YF1f.sec_extents' B ly S rd M kk Hk z tr) | img_exact (YF1f.sec_extents' S kk z tr) | img_refl].
*
intros g Hg Hga HF _. pose proof (shadow_addr_band_rw g Hga) as SBg. img_apply AG; [img_try (clear - SBg; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; img_lia)|].
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg.
destruct LB as (LT1 & _ & LP1 & LP2 & _ & _ & _ & _ & LNB & _ & LSB & _ & _ & _ & _ & _ & LSK).
unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kThreadObjSize, kNodesBlockSize, kStoreBlockSize in LT1, LNB, LSB. unfold kHighMemBeg in LT1, LP1, LNB, LSB, LSK.
unfold YF1f.D, YF1f.DT, YF1f.DK, YF1f.DS, YF1f.DI, YF1f.DH. rewrite Hu, <- Enn. img_change (sptr_addr B ly p) with pa.
intros [X|[X|[X|[X|[X|X]]]]].
-- clear - X SBg LT1. unfold t_unwinding, t_stats in X. img_lia.
-- rewrite EP in X. clear - X SBg G1 G5 ER NN1 NN3. ceil. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G1. img_lia.
-- clear - X SBg LSK HSP'. unfold ASTACK in *. img_lia.
-- rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB) in X. clear - X SBg. unfold TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_FLAG in X. img_lia.
-- unfold depot_footprint in X. rewrite (ts_depot _ TB), (ts_store _ TB) in X. clear - X SBg LNB LSB. ceil. unfold TFX_DEPOT, TFX_STORE, d_map1, kNodesBlockSize, kStoreBlockSize, ASAN_CEIL in *. img_lia.
-- pose proof (YF1f.u_al8 B ly S rd M kk Hk) as (U8 & _). rewrite Hu in U8. img_change (sptr_addr B ly p) with pa in U8.
refine (hfree_shadow_off_range B ly S rd kk pa nn g M Hk _ _ U8 _ Hg HF X); rewrite ?EP; clear - G5 ER NN1 NN3; img_lia.
- rewrite BS. destruct BUD as [BUD _]. clear - BUD. img_lia.
- rewrite (YF1f.all_batches_S' S kk z tr), (YF1f.S'_nev S kk z tr). pose proof (wf_batches_ev _ _ _ _ _ WF). img_lia.
-   img_exact (YF1f.refill_reg_S' B ly S rd M kk Hk z tr Hev kBatchClass ltac:(img_try (unfold kBatchClass; img_lia))).
- img_exact (YF1f.k'_in B ly S rd M kk Hk z tr).
- img_refl.
- img_exact (YF1f.k'_fresh_items B ly S rd M kk Hk Hst z tr).
- img_apply YK0s.ret_ok_even. img_refl.
- rewrite unsigned_lit_small by img_lia. img_lia.
- unfold sp0. replace (bv_unsigned (getr regs 2) - 2288) with (bv_unsigned (getr regs 2) + (-143) * 16) by img_lia. rewrite Z_mod_plus_full. img_exact Hal.
- clear - Hlo. unfold spZ, QSTACK, ASTACK in *. unfold sp0. img_lia.
- clear - Hhi. unfold spZ in *. unfold sp0. img_lia.
- intros a Ha. img_apply PRESE. clear - Ha. unfold QSTACK, ASTACK in *. img_lia.
- rewrite Q3. img_exact Hgp.
- rewrite Q4. rewrite (ts_tp _ TB) in Htp |- *. img_refl.
- rewrite Q10. unfold w64. rewrite Zbv_add_unsigned. f_equal; unfold t_qc; img_lia.
- rewrite Q11. unfold w64. rewrite Zbv_add_unsigned. f_equal; unfold t_cache; img_lia.
- rewrite Q13. img_change (ck_user kk') with (ck_user kk). rewrite Hu. img_change (sptr_addr B ly p) with pa. unfold w64, kChunkHeaderSize. rewrite Zbv_add_unsigned. f_equal; img_lia.
- rewrite Q14. img_change (ck_n kk') with (ck_n kk). rewrite <- Enn. img_refl.
-
img_exact (YF1f.qloose_S' B ly S rd M kk Hk Hst z tr HQT).
Qed.
Lemma MID_AG : forall (msD : machine_state) mem4 (memE : word -> option byte),
YF6n.MEQI W ly regs mem pa (ms_mem msD) ->
(forall x : word, ~ (sp0 - 2256 - DEP_STK <= bv_unsigned x < sp0 - 2256) -> ~ depot_footprint B ly (bv_unsigned x) -> mem4 x = ms_mem msD x) ->
YF6l.EQS ly regs pa nn mem4 memE ->
forall a, 0 <= a < 2 ^ 64 -> ~ YF1f.D B ly kk sp0 a -> aview tfxsegs (w_H W) memE a = rd0 a.
Proof.
intros msD mem4 memE MEQD Hfr4 EQE a Ha ND.
pose proof kk_facts as (Hf & Hk & Hst & Hu & Hr).
pose proof (YF1f.ext_rounded B ly S rd0 M kk Hk) as (ER & NN1 & NN2 & NN3). rewrite <- Enn in ER, NN1, NN2, NN3.
img_apply aview_same.
assert (Ux : bv_unsigned (Z_to_bv 64 a) = a) by (img_try (img_apply unsigned_lit_small; img_exact Ha)).
unfold YF1f.D, YF1f.DT, YF1f.DK, YF1f.DS, YF1f.DI, YF1f.DH in ND. rewrite Hu, <- Enn in ND. img_change (sptr_addr B ly p) with pa in ND.
assert (NW : ~ YF6n.WIN ly regs pa a).
{ intros X. img_apply ND. clear ND. unfold YF6n.WIN, YF6n.WINT, YF6n.WINB in X. fold sp0 in X.
destruct X as [X|[X|X]]; [img_try (do 2 right; left; img_exact X) | img_try (left; clear - X; img_lia) | img_try (right; left; img_exact X)]. }
rewrite (proj1 EQE (Z_to_bv 64 a)); rewrite ?Ux.
2:{ intros X. img_apply NW. img_exact (YF6n.WIN2_WIN ly regs pa a X). }
2:{ intros X. img_apply ND. do 5 right. clear - X NN2. unfold YF6n.SPv, YF6n.CNT8v, YF6n.N8v, shadow_addr in *. rewrite Z_div_mult in X by img_lia. img_lia. }
rewrite Hfr4; rewrite ?Ux.
2:{ intros X. img_apply ND. do 2 right; left. clear - X. unfold DEP_STK, ASTACK in *. img_lia. }
2:{ intros X. img_apply ND. do 4 right; left; img_exact X. }
img_apply (proj1 MEQD); rewrite ?Ux; [img_try (img_exact NW)|].
intros X. img_apply ND. do 3 right; left. unfold YF6n.IZONE in X. rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB), (ts_ial_flag _ TB). img_exact X.
Qed.
Lemma s1_wf : Wf (as_universe B) s1.
Proof.
destruct PRE as ((MM & _ & _) & Hev & _).
img_apply (WfP_weaken _ 1 1 1); try img_lia. unfold s1. img_apply WfP_set_internal_inited. img_apply WfP_tick; [img_try (img_exact (am_wf B ly S _ MM)) | img_try (img_exact Hev)].
Qed.
Lemma aview_eq_mbyte : forall (H H' : word -> bool) (m m' : word -> option byte) a,
aview tfxsegs H' m' a = aview tfxsegs H m a -> mbyte tfxsegs (mrestrict H' m') a = mbyte tfxsegs (mrestrict H m) a.
Proof.
intros H H' m m' a E. unfold aview in E.
destruct (mbyte tfxsegs (mrestrict H' m') a) as [b'|], (mbyte tfxsegs (mrestrict H m) a) as [b|]; cbn in E; try discriminate; [|img_refl].
injection E as E. f_equal. img_apply bv_eq. img_exact E.
Qed.
Lemma kept_of_aview : forall (E : env) (W5 : world tfxsegs) (m m' : word -> option byte) r,
(forall a, base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r ->
aview tfxsegs (w_H W5) m' a = aview tfxsegs (w_H W) m a) ->
(forall a, base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r ->
aview tfxsegs (w_H W5) m' a = aview tfxsegs (w_H W) m a /\ TFX_IMG_END <= a < 2 ^ 64) ->
region_kept tfxsegs E (mrestrict (w_H W) m) (mrestrict (w_H W5) m') r.
Proof.
intros E W5 m m' r Hext Hwin. split.
- intros a Ha. img_apply aview_eq_mbyte. img_apply Hext. img_exact Ha.
- intros a Ha Hw. destruct (Hwin a Ha) as [EQ Hh]. img_apply apresent_writable; [img_try (img_exact Hh)|].
pose proof (writable_high_apresent (w_H W) m a Hh Hw) as P. apply apresent_mbyte in P as [b Hb].
assert (A : aview tfxsegs (w_H W) m a = Some (bv_unsigned b)) by (img_try (unfold aview; rewrite Hb; img_refl)).
rewrite <- EQ in A. apply aview_some in A as (b' & Hb' & _). img_exact (mbyte_high_apresent (w_H W5) m' a b' Hh Hb').
Qed.
End h.
End f.
