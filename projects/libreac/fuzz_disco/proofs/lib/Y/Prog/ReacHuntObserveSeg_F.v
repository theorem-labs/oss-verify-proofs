(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of ctrl_lay_block on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChz.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACb8.v. *)
(* Modified by Theorem Labs, 2026-10: the walk of ctrl_lay_block on image B (fuzz_grant.asan-ubsan), ported from
   image A's closed walk lib/A/Prog/CtrlLayBlock.v (a working branch 5aae1e8a0ce), itself written with proof steps adapted
   from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, AC8k.v, AChz.v, ACa2.v and ACb8.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/CtrlLayBlock.v, with its module paths, module names and numbers changed; 805 of its 880 lines of code are new or changed and 987 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/ReacHuntObserveSeg_A.v, with its numbers changed; 960 of its 1052 lines of code are new or changed and 788 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YA0q YCbm YK06 YI0m YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i YXcalls YCbj.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1g YC1h YC1i YC45 YC4b YC7k YC81 YC85 YC88 YCbw YCkd YCbf YCj1 YCja YCjr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ClassifyCore ReacDiscoClassifyOnSegment ReacDiscoTableObserve.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require ReacFrameCleanLen.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_classify_c disco_table_c hunt_c reac_disco_table_observe_c reac_frame_clean_len_c reac_hunt_observe_c
HuntObsFacts HuntObsLib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacHuntObserveCore.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
Context {PO : PAObjImg lib_both3_0_listing}.
Context {PW : PAWinImg lib_both3_0_listing}.
Context {PV : PAObjVal lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Hypothesis ASM1 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TCOS : treac_disco_classify_on_segment_spec B.
Hypothesis TOBS : treac_disco_table_observe_spec B.
Hypothesis HRO : YRo.tfib_ro_unowned B.
#[local] Notation ho_count := (@ReacHuntObserveCore.ho_count rc PI).
#[local] Notation hoC := (@ReacHuntObserveCore.hoC rc PI).
#[local] Notation ho_post := (@ReacHuntObserveCore.ho_post rc SK PI B).
#[local] Notation ho_fsh := (@ReacHuntObserveCore.ho_fsh rc PI).
#[local] Notation ho_regs_mid := (@ReacHuntObserveCore.ho_regs_mid rc PI B).
#[local] Notation ho_cfg := (@ReacHuntObserveCore.ho_cfg rc PI).
#[local] Notation ho_base := (@ReacHuntObserveCore.ho_base rc SK PI B).
#[local] Notation ho_L := (@ReacHuntObserveCore.ho_L rc PI).
#[local] Notation ho_U := (@ReacHuntObserveCore.ho_U rc PI).
#[local] Notation ho_Lk := (@ReacHuntObserveCore.ho_Lk rc PI).
#[local] Notation ho_Lk' := (@ReacHuntObserveCore.ho_Lk' rc PI).
#[local] Notation EHOm := (@ReacHuntObserveCore.EHOm rc PI B).
#[local] Notation ho_seg_F_stmt := (@ReacHuntObserveCore.ho_seg_F_stmt rc SK PI B).
#[local] Notation ho_seg_G_stmt := (@ReacHuntObserveCore.ho_seg_G_stmt rc SK PI B).
#[local] Notation ho_seg_T_stmt := (@ReacHuntObserveCore.ho_seg_T_stmt rc SK PI B).
#[local] Notation hoEF_region_win := (@ReacHuntObserveCore.hoEF_region_win rc PI).
#[local] Notation hoEF_region_wc := (@ReacHuntObserveCore.hoEF_region_wc rc PI).
#[local] Notation hoF_e32 := (@ReacHuntObserveCore.hoF_e32 rc PI B).
#[local] Notation hoF_val_mem_ext := (@ReacHuntObserveCore.hoF_val_mem_ext rc PI).
#[local] Notation hoF_garr_ext := (@ReacHuntObserveCore.hoF_garr_ext rc PI).
#[local] Notation hoF_aview_frame := (@ReacHuntObserveCore.hoF_aview_frame rc PI).
Hypothesis ho_mid_entry : forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F SH (wo : bool) af,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  ho_fsh W2 mem2 F SH -> length SH = 16%nat -> Forall (fun z : Z => 0 <= z < 256) SH ->
  (wo = true -> c_out c <> 0 /\ getr regs2 19 = w64 (c_out c)) ->
  st_ok_pi (fx := c_fq c) SEGS VAL (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) (ss_hoM SH wo af)
    (restrict (w_H W2) (mkst (fx := c_fq c) regs2 (Z_to_bv 64 (BASE + af)) mem2 (seg_rom SEGS)))
  /\ img_env VAL A_LIM (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)).
Hypothesis ho_shokM : forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F (wo : bool),
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  (wo = true -> c_out c <> 0 /\ getr regs2 19 = w64 (c_out c)) ->
  sh_ok SEGS HOBx (ho_SHM wo) (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) (mrestrict (w_H W2) mem2).
Hypothesis ho_segT : ho_seg_T_stmt.
Hypothesis ho_segG : ho_seg_G_stmt.

Lemma tho_facts_hold : forall (Hh FB T' A : list byte) (len now c : Z),
  length FB = 50%nat -> hunt_c.hunt_ok Hh ->
  disco_classify_c.cm_ret FB (reac_frame_clean_len_c.reac_frame_clean_len_model len)
    (disco_table_c.sub Hh 412 6) (Some (disco_table_c.sub Hh 400 12)) = 0 ->
  reac_disco_table_observe_c.observe_model (disco_table_c.sub Hh 0 400)
    (disco_classify_c.sight FB (reac_frame_clean_len_c.reac_frame_clean_len_model len)) 0 now T' c ->
  length T' = 400%nat ->
  reac_hunt_observe_c.ho_answer T'
    (disco_classify_c.sight FB (reac_frame_clean_len_c.reac_frame_clean_len_model len)) A ->
  reac_hunt_observe_c.ho_facts Hh FB (reac_frame_clean_len_c.reac_frame_clean_len_model len)
    (disco_table_c.sub Hh 0 400) A.
Proof.
  intros Hh FB T' A len now c LF HOK R0 OM LT' (r & FRr & EA). subst A.
  set (L := reac_frame_clean_len_c.reac_frame_clean_len_model len) in *.
  set (G := disco_classify_c.sight FB L) in *. set (T := disco_table_c.sub Hh 0 400) in *.
  pose proof (HuntObsLib.cm_ret0_len _ _ _ _ R0) as L50.
  destruct (HuntObsLib.cm_ret0_facts _ _ _ _ R0) as [NU DK].
  destruct (HuntObsFacts.sight_vals FB L LF) as (SM & SR & SC & SH & SD). fold G in SM, SR, SC, SH, SD.
  pose proof (HuntObsFacts.sight_len FB L LF) as LG. fold G in LG.
  destruct (HuntObsFacts.sight_ok FB L LF) as [S1 S2]. fold G in S1, S2.
  pose proof HOK as (LH & _).
  assert (TOK : disco_table_c.table_ok T) by (destruct HOK as (_ & X & _); exact X).
  destruct TOK as (TT1 & TT2 & TT3 & TT4).
  assert (LT : length T = 400%nat) by (unfold T; apply HuntObsLib.len_sub; lia).
  destruct (reac_disco_table_observe.observe_model_tbl T G 0 now T' c LT LG TT1 TT2 TT3 S1 S2 OM)
    as (T1' & T2' & _ & T4i).
  destruct (HuntObsFacts.obs_at T G 0 now T' c r LT LG TT1 TT3 S1 OM FRr) as [CH RL].
  assert (MG : disco_table_c.s_mac G = disco_table_c.sub FB 6 6).
  { rewrite SM. unfold disco_classify_c.src, CtrlParsed.fld, disco_table_c.sub. reflexivity. }
  assert (NE : disco_table_c.s_mac G <> disco_table_c.sub Hh 412 6).
  { rewrite SM. intros X. unfold CtrlParsed.bytes_eqb in NU. rewrite X in NU.
    match type of NU with context [list_eq_dec ?d ?a ?b] => destruct (list_eq_dec d a b) as [_|Y] end;
      [discriminate | apply Y; reflexivity]. }
  assert (DF : (CtrlParsed.fb FB 16 = 0 /\ CtrlParsed.fb FB 17 = 0) \/ disco_classify_c.fsum FB = 0).
  { destruct DK as [DK|DK]; [left; exact (HuntObsLib.dkind1 _ _ DK) | right; exact DK]. }
  unfold reac_hunt_observe_c.ho_facts. destruct (Z.ltb r 0) eqn:RL0; cbv beta iota.
  - apply Z.ltb_lt in RL0.
    split; [lia|]. split; [exact MG|]. split; [exact NE|]. split; [rewrite SC; lia|].
    split; [exact S1|]. split; [exact DF|]. split; [exact SH|].
    split; [intros X; apply SD; lia|].
    intros (j & Hj & Ej & Rj). destruct (RL j Hj Ej Rj) as [X _]. lia.
  - apply Z.ltb_ge in RL0. unfold disco_table_c.tbl_T1 in T1'.
    assert (Hrn : 0 <= r < disco_table_c.n_of T') by (destruct FRr as [(X & _) | (X & _)]; lia).
    destruct (HuntObsFacts.ho_entry_f T' G r LT' LG ltac:(lia)) as (EM & ER & EH & EI & EO & EC).
    destruct (T4i TT4 r Hrn) as (H01 & H40 & _).
    rewrite EM, ER, EH, EI, EO, EC.
    split; [lia|]. split; [exact MG|]. split; [exact NE|]. split; [rewrite <- SC; apply CH; lia|].
    split; [apply T2'; exact Hrn|]. split; [exact DF|]. split; [exact H01|].
    split; [intros X; apply H40; lia|].
    intros (j & Hj & Ej & Rj). destruct (RL j Hj Ej Rj) as [_ X]. exact X.
Qed.


Lemma hoEF_awr_own : forall STK sp0 FP bl0 blc ly own x a,
  awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc ly (x :: own) a.
Proof.
intros STK sp0 FP bl0 blc ly own x a [H | [H | [H | (cid & pos & Hin & Hr)]]];
[left; exact H | right; left; exact H | right; right; left; exact H |].
right; right; right. exists cid, pos. split; [right; exact Hin | exact Hr].
Qed.

Ltac hoEF_win HS i wlo whi :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let r := eval vm_compute in (nth i rs got_regionP) in
let r' := eval vm_compute in (set_window r wlo whi) in
lazymatch r with YP09.mkRegion (Some ?nn) ?lo ?hi ?wlo0 ?whi0 ?cs =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r r' HS
  ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (hoEF_region_win Ex (ms_mem msx) nn lo hi wlo0 whi0 cs wlo whi
     (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
     ltac:(first [left; lia | right; split; lia]))) as HS3;
clear HS; rename HS3 into HS end end; norm_ss HS.

Lemma hoEF_aview_frame : forall E rs (Hv : word -> bool) (m m' : word -> option byte) a,
  frame_of E rs (mrestrict Hv m) (mrestrict Hv m') -> 0 <= a < 2 ^ 64 ->
  ~ in_wrange E rs a -> aview SEGS Hv m' a = aview SEGS Hv m a.
Proof.
intros E rs Hv m m' a HFR Ha Hn. unfold aview, mbyte.
rewrite (HFR (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; exact Hn)). reflexivity.
Qed.

Lemma hoEF_hull_kept : forall (rd rd' : reader) a nn,
  (forall s, shadow_addr a / 8 * 8 <= s < shadow_addr (a + nn - 1) / 8 * 8 + 8 -> rd' s = rd s) ->
  shadow_hull_vis rd a nn -> shadow_hull_vis rd' a nn.
Proof. intros rd rd' a nn HK HV s Hs. rewrite (HK s Hs). exact (HV s Hs). Qed.

Ltac hoF_ro HS i :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS
  ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r 0 0
     (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
     ltac:(intros o Ho; exfalso; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.

Ltac hoF_awr0 :=
let a := fresh "a" in let Ha := fresh "Ha" in let rg := fresh "rg" in
let Hrg := fresh "Hrg" in let Hrng := fresh "Hrng" in
intros a Ha; destruct Ha as (rg & Hrg & Hrng);
cbn [ss_mem In] in Hrg;
repeat (destruct Hrg as [<- | Hrg];
  [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrng; exfalso; lia | ]);
destruct Hrg.

Lemma hoF_ereg : forall (c : hoC) (regs2 : bvmap 5 word) (FL : Z) (n : nat) (rr : bv 5),
  (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> ew (EHOm c regs2 FL) n = getr regs2 rr.
Proof.
intros c regs2 FL n rr Hn Hr. unfold EHOm. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_nat regs2 _ n rr Hr).
Qed.

Lemma hoF_shok_env : forall E E' m,
  ew E' 21 = ew E 21 -> ew E' 32 = ew E 32 ->
  sh_ok SEGS HOBx (ho_SHM false) E m -> sh_ok SEGS HOBx (ho_SHM false) E' m.
Proof.
intros E E' m E21 E32 H. unfold sh_ok, ho_SHM in *. cbn [app] in *.
pose proof (Forall_inv H) as Hx. apply Forall_cons; [|apply Forall_nil].
assert (U1 : U E' (SOff 21 0) = U E (SOff 21 0)) by (rewrite !U_SOff, E21; reflexivity).
assert (U2 : U E' HOBx = U E HOBx) by (unfold HOBx; rewrite !U_SOff, E32; reflexivity).
unfold shent_ok, app_apart in *. cbn [she_m she_lo she_hi] in *. rewrite U1, U2. exact Hx.
Qed.

Lemma hoF_ro_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
intros a [(s & Hs & _ & Hr) | Hrel]; [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hrel)].
Qed.

Lemma hoF_rdword_ext : forall (rd rd' : Z -> option Z) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as E0. rewrite Z.add_0_r in E0.
rewrite E0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Lemma hoF_out_safe : forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F -> c_out c <> 0 ->
  forall a, c_out c <= a < c_out c + 24 ->
    ~ in_img SEGS a /\ (a < F \/ F + 128 <= a) /\ 4096 <= a /\ a < YM05.alloc_ceiling.
Proof.
intros c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB Hout a Ha.
pose proof HB as (HPRE & HMID & _ & HFeq & _).
pose proof HMID as (HJ & Hfrs & Hfa & Hperm & _).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & POUTF & _).
destruct (POUTF Hout) as (HTO & _ & _).
destruct HTO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLOC).
pose proof (proj1 HJ) as HAR.
assert (HinF : In (1, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (HFA1 : frame_addr ly2 1 fpos = F) by (rewrite Hfa; symmetry; exact HFeq).
destruct HLOC as [(cid & pos & Hin & Hlo & Hhi) | (b & m & Hin & Hlo & Hhi)].
- assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; right; exact Hin).
  rewrite <- (Hfa cid pos) in Hlo, Hhi.
  destruct (in_split _ _ Hin) as (l2 & l3 & Esp).
  pose proof (sep_frames_pos _ _ LAWS ly2 S2 W2 mem2 md2 (1, fpos) (cid, pos) [] l2 l3 HAR
    ltac:(rewrite Hfrs, Esp; reflexivity)) as Hdj.
  unfold zdisjoint, frame_rng in Hdj. cbn [fst snd] in Hdj.
  rewrite HFA1 in Hdj. change (fs_frame_bytes 1) with 128 in Hdj.
  pose proof (frames_bounds _ _ LAWS ly2 S2 W2 mem2 md2 cid pos HAR Hin2) as (Hg1 & Hg2 & _).
  destruct (al_client_img _ _ LAWS ly2 S2 W2 mem2 md2 a HAR
    ltac:(right; left; exists cid, pos; split; [exact Hin2 | lia])) as [_ Hni].
  split; [exact Hni | lia].
- assert (Hin2 : In (b, m) (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin).
  pose proof (sep_block_frame _ _ LAWS ly2 S2 W2 mem2 md2 b m 1 fpos HAR Hin2 HinF) as Hdj.
  unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
  rewrite HFA1 in Hdj. change (fs_frame_bytes 1) with 128 in Hdj.
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR Hin2) as (_ & Hb1 & Hb2 & _).
  destruct (al_client_img _ _ LAWS ly2 S2 W2 mem2 md2 a HAR
    ltac:(left; exists b, m; split; [exact Hin2 | lia])) as [_ Hni].
  split; [exact Hni | lia].
Qed.

Lemma hoF_base_mem : forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F mem3 md3 regs3,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  ajournal SEGS B (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
    ((1, fpos) :: c_own c) ly2 S2 W2 mem3 md3 k2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_out c <> 0 /\ c_out c <= a < c_out c + 24) ->
     ~ (sp1 - 4096 <= a < sp1 + 56) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  ho_regs_mid c regs3 sp1 F -> ho_fsh W2 mem2 F ho_shC ->
  ho_base c fpos ly2 S2 W2 mem3 md3 k2 H2 regs3 sp1 F /\ ho_fsh W2 mem3 F ho_shC.
Proof.
intros c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F mem3 md3 regs3 HB HJ3 HUP HPR HRG3 HFSH.
pose proof (hoF_out_safe c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB) as HOS.
pose proof HB as (HPRE & HMID & HSP1 & HFeq & HRG & HSV).
pose proof HMID as (HJ & Hfrs & Hfa & Hperm & HKEPT & HROm & HGH & HLH & HFLAG & HKLE).
pose proof HPRE as (PJ & PRO & PRA & PRA4 & PGP & PTP & PAL & PWIN & PSP & PDEP & PLEN & PNOW &
  POUT & PH0 & PH8 & PIN & PHB & PHE & PHW & PHOK & PFBL & PHG & PF50 & POUTF & PKM & PKT).
pose proof HKEPT as (KP1 & KP2 & KP3 & KP4 & KP5 & KP6).
pose proof HSP1 as (HSP1a & HSP1b & HSP1c).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (HSTK : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
rewrite HSTK in PWIN.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & X0 & X1 & X2 & X3 & _) & _).
assert (Hsp1lo : YM05.alloc_ceiling + 8512 <= sp1) by lia.
assert (Hsp1hi : sp1 + 160 <= spZ (c_regs c)) by lia.
assert (Hsp47 : spZ (c_regs c) <= 2 ^ 47) by lia.
clear X0 X1 X2 X3.
assert (HinF : In (1, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (HFA1 : frame_addr ly2 1 fpos = F) by (rewrite Hfa; symmetry; exact HFeq).
pose proof (frames_bounds _ _ LAWS ly2 S2 W2 mem2 md2 1 fpos HAR HinF) as (HF1 & HF2 & _).
rewrite HFA1 in HF1, HF2. change (fs_frame_bytes 1) with 128 in HF2.
assert (HinH : In (c_hb c, c_hn c) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); exact PIN).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (c_hb c) (c_hn c) HAR HinH) as (_ & Hhb4 & Hbceil & _).
assert (HLOW : forall a, 0 <= a < YM05.alloc_ceiling -> ~ (c_out c <> 0 /\ c_out c <= a < c_out c + 24) ->
  aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a)
  by (intros a Ha Hno; apply HUP; [lia | exact Hno | lia]).
assert (HF8 : 8 * (F / 8) <= F) by (apply Z.mul_div_le; lia).
assert (HF8p : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (HFSH3 : ho_fsh W2 mem3 F ho_shC).
{ intros i Hi. rewrite (HLOW (SB + F / 8 + i)); [exact (HFSH i Hi) | unfold SB; lia | ].
  intros (Hout & Hlo & Hhi). destruct (POUTF Hout) as (HTO & _ & _).
  destruct HTO as (_ & _ & HAM & _). unfold amem_range in HAM. rewrite CC3, CC5 in HAM.
  unfold SB in *. lia. }
split; [|exact HFSH3].
split; [exact HPRE|].
split.
{ split; [exact HJ3|]. split; [exact Hfrs|]. split; [exact Hfa|]. split; [exact Hperm|].
  split.
  { split.
    { intros a Ha1 Ha2 Ha3. rewrite HSTK in Ha2.
      rewrite HUP; [exact (KP1 a Ha1 ltac:(rewrite HSTK; exact Ha2) Ha3) | lia
                    | intros X; apply Ha3; right; exact X | lia]. }
    split.
    { intros b m i Hin Hi Hw.
      assert (Hin2 : In (b, m) (ablocks B ly2 S2))
        by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin).
      destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR Hin2) as (_ & Hb1 & Hb2 & _).
      rewrite HLOW; [exact (KP2 b m i Hin Hi Hw) | lia | intros X; apply Hw; right; exact X]. }
    split.
    { intros a Hi Ho He. pose proof (pa_img_range a Hi) as Hir.
      unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hir.
      rewrite HLOW; [exact (KP3 a Hi Ho He) | lia | ].
      intros (Hout & Hlo & Hhi). exact (proj1 (HOS Hout a (conj Hlo Hhi)) Hi). }
    split.
    { intros cid pos a Hin Hz Hw.
      assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; right; exact Hin).
      pose proof (frames_bounds _ _ LAWS ly2 S2 W2 mem2 md2 cid pos HAR Hin2) as (Hg1 & Hg2 & _).
      rewrite (Hfa cid pos) in Hg1, Hg2.
      pose proof (fs_frame_bytes_nonneg cid) as Hgn.
      rewrite HLOW; [exact (KP4 cid pos a Hin Hz Hw) | | intros X; apply Hw; right; exact X].
      unfold in_zr, frame_rng, shadow_addr in Hz. cbn [fst snd] in Hz.
      rewrite <- SB_SHADOW_OFF in Hz. unfold SB in Hz.
      assert (8 * (frame_addr (c_lyc c) cid pos / 8) <= frame_addr (c_lyc c) cid pos)
        by (apply Z.mul_div_le; lia).
      assert (8 * (fs_frame_bytes cid / 8) <= fs_frame_bytes cid) by (apply Z.mul_div_le; lia).
      assert (0 <= frame_addr (c_lyc c) cid pos / 8) by (apply Z.div_pos; lia).
      lia. }
    split.
    { intros a Ha1 Ha2 Ha3. apply HPR. exact (KP5 a Ha1 Ha2 Ha3). }
    { intros a Ha. apply HPR. exact (KP6 a Ha). } }
  split.
  { intros a Hro Ho He. pose proof (hoF_ro_img a Hro) as Hi. pose proof (pa_img_range a Hi) as Hir.
    unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hir.
    rewrite HLOW; [exact (HROm a Hro Ho He) | lia | ].
    intros (Hout & Hlo & Hhi). exact (proj1 (HOS Hout a (conj Hlo Hhi)) Hi). }
  split.
  { apply (hoF_garr_ext W2 mem2 mem3); [|exact HGH].
    intros i Hi. rewrite length_map, HLH in Hi. change (Z.of_nat 480) with 480 in Hi.
    apply HLOW; [lia|]. intros (Hout & Hlo & Hhi). destruct (POUTF Hout) as (_ & Hsep & _). lia. }
  split; [exact HLH|].
  split; [|exact HKLE].
  rewrite (hoF_rdword_ext (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) mem3)); [exact HFLAG|].
  intros i Hi. rewrite HFA1. apply HLOW; [lia|].
  intros (Hout & Hlo & Hhi). destruct (HOS Hout (F + 120 + i) (conj Hlo Hhi)) as (_ & HX & _). lia. }
split; [exact HSP1|]. split; [exact HFeq|]. split; [exact HRG3|].
intros j Hj. apply (hoF_val_mem_ext W2 mem2 mem3); [|exact (HSV j Hj)].
intros k Hk. apply HUP; [lia | | lia].
intros (Hout & Hlo & Hhi). destruct (POUTF Hout) as (HTO & _).
destruct HTO as (_ & _ & _ & HSPS & _). rewrite HSTK in HSPS. lia.
Qed.

Lemma hoF_snez : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SLTU (SLit 0) (SOff n 0)) = Z_to_bv 64 (if v =? 0 then 0 else 1).
Proof.
intros E n v En Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, U_SLit, (U_atom E n v En Hv). cbn [zalu_raw]. change (zcanon 0) with 0.
destruct (Z.eqb_spec v 0) as [->|Hne]; [reflexivity|].
destruct (Z.ltb_spec 0 v); [reflexivity | lia].
Qed.

Lemma hoF_bge : forall E (k : nat) v, ew E k = Z_to_bv 64 v -> 0 <= v <= 8 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff k 0)) = (v <=? 0).
Proof.
intros E k v Ek Hv. rewrite hoF_off0, Ek. cbn [sv_denot branch_taken]. unfold bv_lts.
rewrite (YK11.bv_signed_small (Z_to_bv 64 0)) by (rewrite unsigned_lit_small; lia).
rewrite (YK11.bv_signed_small (Z_to_bv 64 v)) by (rewrite unsigned_lit_small; lia).
rewrite !unsigned_lit_small by lia.
destruct (Z.leb_spec v 0); destruct (Z.ltb_spec 0 v); try reflexivity; lia.
Qed.

Lemma hoF_mul48 : forall E (k : nat) v, ew E k = Z_to_bv 64 v -> 0 <= v <= 8 ->
  sv_denot E (SMd M_MUL (SOff k 0) (SLit 48)) = Z_to_bv 64 (48 * v).
Proof.
intros E k v Ek Hv. rewrite denot_lit_U. f_equal.
rewrite U_SMd, (U_atom E k v Ek) by lia. rewrite U_lit by lia. cbn [zmd_raw].
rewrite Z.mul_comm. apply zcanon_id. unfold M64. lia.
Qed.

Lemma hoF_not : forall E (k : nat) v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_XOR (SOff k 0) (SLit (-1))) = Z_to_bv 64 (2 ^ 64 - 1 - v).
Proof. intros E k v Ek Hv. rewrite denot_lit_U, (U_not E k v Ek Hv). reflexivity. Qed.

Lemma hoF_subT : forall (H2 T' : list byte), H2 = T' ++ skipn 400 H2 -> length T' = 400%nat ->
  disco_table_c.sub H2 0 400 = T'.
Proof.
intros H2 T' HH LT. unfold disco_table_c.sub. change (Z.to_nat 0) with 0%nat. change (skipn 0 H2) with H2.
rewrite HH. apply ho_firstn_exact. exact LT.
Qed.

Lemma hoF_mbyte2 : forall (H : word -> bool) (ma mb : word -> option byte) a b,
  aview SEGS H mb b = aview SEGS H ma a -> mbyte SEGS (mrestrict H mb) b = mbyte SEGS (mrestrict H ma) a.
Proof.
intros H ma mb a b E. unfold aview in E.
destruct (mbyte SEGS (mrestrict H mb) b) as [x|] eqn:Ex;
destruct (mbyte SEGS (mrestrict H ma) a) as [y|] eqn:Ey; cbn in E; try discriminate; [|reflexivity].
f_equal. injection E as E. apply bv_eq. exact E.
Qed.

Lemma hoF_garr_shift : forall (Wx : world SEGS) ma mb a b l,
  (forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS (w_H Wx) mb (b + i) = aview SEGS (w_H Wx) ma (a + i)) ->
  garr8 SEGS (mrestrict (w_H Wx) ma) a l -> garr8 SEGS (mrestrict (w_H Wx) mb) b l.
Proof.
intros Wx ma mb a b l HE HGa j Hj. destruct (HGa j Hj) as [Hv Hr]. split; [|exact Hr].
intros kk Hk. pose proof (Hv kk Hk) as H0.
replace (a + Z.of_nat j + Z.of_nat kk) with (a + Z.of_nat j) in H0 by lia.
replace (b + Z.of_nat j + Z.of_nat kk) with (b + Z.of_nat j) by lia.
rewrite (hoF_mbyte2 (w_H Wx) ma mb (a + Z.of_nat j) (b + Z.of_nat j) (HE (Z.of_nat j) ltac:(lia))).
exact H0.
Qed.

Lemma hoF_garr_some : forall (Wx : world SEGS) m a l i,
  garr8 SEGS (mrestrict (w_H Wx) m) a l -> a <= i < a + Z.of_nat (length l) ->
  aview SEGS (w_H Wx) m i <> None.
Proof.
intros Wx m a l i HGa Hi. destruct (HGa (Z.to_nat (i - a)) ltac:(lia)) as [Hv _].
pose proof (Hv 0%nat ltac:(lia)) as Hb.
replace (a + Z.of_nat (Z.to_nat (i - a)) + Z.of_nat 0) with i in Hb by lia.
unfold aview. rewrite Hb. discriminate.
Qed.

Lemma hoF_ans_empty : forall (T G : list byte), disco_table_c.n_of T = 0 -> reac_hunt_observe_c.ho_answer T G G.
Proof.
intros T G Hn. exists (-1). split; [left; split; [reflexivity | intros j Hj; lia] | reflexivity].
Qed.

Lemma hoF_model : forall (c : hoC) (T' H2 : list byte) ret (OUT : list byte -> Prop),
  reac_disco_table_observe_c.observe_model (disco_table_c.sub (c_H c) 0 400)
    (disco_classify_c.sight (c_FB c) (ho_L c)) 0 (c_now c) T' ret ->
  disco_classify_c.cm_ret (c_FB c) (ho_L c) (ho_U c) (ho_Lk c) = 0 ->
  H2 = T' ++ skipn 400 H2 ->
  skipn 400 H2 = ho_Lk' c ++ disco_table_c.sub (c_H c) 412 12 ++
    (if disco_table_c.n_of (disco_table_c.sub (c_H c) 0 400) =? 0
     then Mem.le8 (Z_to_bv 64 (c_now c)) else disco_table_c.sub (c_H c) 424 8) ++ skipn 432 (c_H c) ->
  (c_out c <> 0 -> exists A,
     reac_hunt_observe_c.ho_answer T' (disco_classify_c.sight (c_FB c) (ho_L c)) A /\ OUT A /\
     reac_hunt_observe_c.ho_facts (c_H c) (c_FB c) (ho_L c) (disco_table_c.sub (c_H c) 0 400) A) ->
  tho_model (c_H c) (c_FB c) (c_O c) (c_len c) (c_now c) (c_out c) (if ret =? 0 then 0 else 1) H2 OUT.
Proof.
intros c T' H2 ret OUT HOM HRET HH2 HSK ANS.
unfold tho_model. cbv zeta. split.
- intros X. exfalso. apply X. exact HRET.
- intros _. exists T', ret. split; [exact HOM|]. split; [reflexivity|]. split; [|exact ANS].
  transitivity (T' ++ skipn 400 H2); [exact HH2|]. rewrite HSK. reflexivity.
Qed.

Lemma hoF_shadow_in_frame : forall ly S (W : world SEGS) mem md cid pos p n x,
  AR SEGS B ly S W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= p -> p + n <= frame_addr ly cid pos + fs_frame_bytes cid -> p <= x < p + n ->
  in_zr (shadow_of_addr SHADOW_OFF x) (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8).
Proof.
intros ly S W mem md cid pos p n x HAR Hin Hfp Hpn Hx.
destruct (frame_al64 SEGS B ly S W mem md cid pos HAR Hin) as (Hal & Hbal & Hb64).
pose proof (Z.div_mod (frame_addr ly cid pos) 64 ltac:(lia)) as Df.
pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)) as Db.
rewrite Hal, Z.add_0_r in Df. rewrite Hbal, Z.add_0_r in Db.
assert (E8f : frame_addr ly cid pos / 8 = 8 * (frame_addr ly cid pos / 64))
  by (rewrite Df at 1; replace (64 * (frame_addr ly cid pos / 64)) with (8 * (frame_addr ly cid pos / 64) * 8) by lia;
      rewrite Z.div_mul by lia; reflexivity).
assert (E8b : fs_frame_bytes cid / 8 = 8 * (fs_frame_bytes cid / 64))
  by (rewrite Db at 1; replace (64 * (fs_frame_bytes cid / 64)) with (8 * (fs_frame_bytes cid / 64) * 8) by lia;
      rewrite Z.div_mul by lia; reflexivity).
assert (L1 : frame_addr ly cid pos / 8 <= x / 8) by (apply Z.div_le_mono; lia).
assert (L2 : x / 8 < frame_addr ly cid pos / 8 + fs_frame_bytes cid / 8)
  by (rewrite E8f, E8b; apply Z.div_lt_upper_bound; lia).
unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd]. lia.
Qed.

Lemma hoF_out_ra : forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F -> c_out c <> 0 ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (c_out c) 24 /\
  shadow_hull_vis (aview SEGS (w_H W2) mem2) (c_out c) 24.
Proof.
intros c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB Hout.
pose proof HB as (HPRE & HMID & _).
pose proof HMID as (HJ & Hfrs & Hfa & Hperm & HKEPT & _).
pose proof HPRE as ((mdc & PJ) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & POUT & PH0 & _ & PIN & PHB & PHE & _ & _
  & _ & _ & _ & POUTF & _).
destruct (POUTF Hout) as (HTO & HSEPH & _).
destruct HTO as (_ & H63 & HAM & _ & _ & HRA & _ & _ & _ & _ & HLOC).
pose proof (proj1 HJ) as HAR. pose proof (proj1 PJ) as HARc.
pose proof HKEPT as (_ & _ & _ & KP4 & _).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (c_hb c) (c_hn c) HARc PIN) as (_ & _ & _ & Hbapp & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
unfold amem_range in HAM. rewrite CC3, CC4, CC5 in HAM.
destruct HLOC as [(cid & pos & Hin & Hlo & Hhi) | (b & m & Hin & Hlo & Hhi)].
- assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; right; exact Hin).
  split.
  + intros x Hx. destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    rewrite <- Hs. apply (KP4 cid pos); [exact Hin | right |].
    * exact (hoF_shadow_in_frame (c_lyc c) (c_Sc c) (c_W c) (c_memc c) mdc cid pos (c_out c) 24 x HARc Hin Hlo Hhi Hx).
    * assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
      assert (0 <= x / 8) by (apply Z.div_pos; lia).
      unfold tho_wr, shadow_of_addr, SHADOW_OFF. lia.
  + apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 mem2 md2 cid pos (c_out c) 24 HAR Hin2);
      try rewrite (Hfa cid pos); lia.
- assert (Hin2 : In (b, m) (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin).
  split.
  + apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 b m (c_out c) 24 HAR Hin2); lia.
  + apply (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 b m (c_out c) 24 HAR Hin2); lia.
Qed.

Lemma hoF_regs_mid : forall (c : hoC) (regs2 regs3 : bvmap 5 word) sp1 F,
  ho_regs_mid c regs2 sp1 F ->
  getr regs3 2 = getr regs2 2 -> getr regs3 3 = getr regs2 3 -> getr regs3 4 = getr regs2 4 ->
  getr regs3 8 = getr regs2 8 -> getr regs3 9 = getr regs2 9 -> getr regs3 18 = getr regs2 18 ->
  getr regs3 21 = getr regs2 21 -> getr regs3 24 = getr regs2 24 -> getr regs3 25 = getr regs2 25 ->
  ho_regs_mid c regs3 sp1 F.
Proof.
intros c regs2 regs3 sp1 F HR Q2 Q3 Q4 Q8 Q9 Q18 Q21 Q24 Q25.
unfold ho_regs_mid in *. rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q21, Q24, Q25. exact HR.
Qed.

Lemma hoF_toT : forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F mem3 md3 regs3 r,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  ajournal SEGS B (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
    ((1, fpos) :: c_own c) ly2 S2 W2 mem3 md3 k2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 <= a < sp1 + 56) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  ho_regs_mid c regs3 sp1 F -> ho_fsh W2 mem2 F ho_shC ->
  getr regs3 20 = w64 r -> (r = -1 \/ r = 0 \/ r = 1) -> hunt_c.hunt_ok H2 ->
  tho_model (c_H c) (c_FB c) (c_O c) (c_len c) (c_now c) (c_out c) r H2
    (fun A => garr8 SEGS (mrestrict (w_H W2) mem3) (c_out c) (map (fun b : byte => bv_unsigned b) A)) ->
  SRr SEGS W2 (ho_cfg c regs3 mem3 md3 0x7344) (ho_post c).
Proof.
intros c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F mem3 md3 regs3 r HB HJ3 HW HPR HRG3 HFSH R20 Hr HOK HM.
destruct (hoF_base_mem c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F mem3 md3 regs3 HB HJ3
  ltac:(intros a Ha _ Hs; apply HW; [exact Ha | lia]) HPR HRG3 HFSH) as [HB3 HF3].
exact (ho_segT c fpos ly2 S2 W2 mem3 md3 k2 regs3 sp1 F H2 r HB3 R20 Hr HF3 HOK HM).
Qed.

Lemma hoF_toG : forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F mem3 md3 regs3 T' r,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  ajournal SEGS B (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
    ((1, fpos) :: c_own c) ly2 S2 W2 mem3 md3 k2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 <= a < sp1 + 56) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  ho_regs_mid c regs3 sp1 F -> ho_fsh W2 mem2 F ho_shC ->
  getr regs3 19 = w64 (48 * disco_table_c.n_of T') -> getr regs3 20 = w64 (2 ^ 64 - 1 - c_h c) ->
  getr regs3 23 = w64 (F + 32) -> getr regs3 26 = w64 432 -> getr regs3 27 = w64 (48 * 0) ->
  hunt_c.hunt_ok H2 -> H2 = T' ++ skipn 400 H2 -> length T' = 400%nat ->
  0 < disco_table_c.n_of T' <= 8 -> (r = 0 \/ r = 1) ->
  rdword (aview SEGS (w_H W2) mem3) (sp1 + 8) = Some SB ->
  rdword (aview SEGS (w_H W2) mem3) (sp1 + 16) = Some (c_out c) ->
  rdword (aview SEGS (w_H W2) mem3) (sp1 + 24) = Some r ->
  garr8 SEGS (mrestrict (w_H W2) mem3) (F + 32)
    (map (fun b : byte => bv_unsigned b) (disco_classify_c.sight (c_FB c) (ho_L c))) ->
  c_out c <> 0 ->
  garr8 SEGS (mrestrict (w_H W2) mem3) (c_out c)
    (map (fun b : byte => bv_unsigned b) (disco_classify_c.sight (c_FB c) (ho_L c))) ->
  (forall A, reac_hunt_observe_c.ho_answer T' (disco_classify_c.sight (c_FB c) (ho_L c)) A ->
     tho_model (c_H c) (c_FB c) (c_O c) (c_len c) (c_now c) (c_out c) r H2 (fun A' => A' = A)) ->
  SRr SEGS W2 (ho_cfg c regs3 mem3 md3 0x7448) (ho_post c).
Proof.
intros c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F mem3 md3 regs3 T' r HB HJ3 HW HPR HRG3 HFSH
  R19 R20 R23 R26 R27 HOK HH2 LT' Hn Hr Q8 Q16 Q24 HGS Hout HGO HANS.
destruct (hoF_base_mem c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F mem3 md3 regs3 HB HJ3
  ltac:(intros a Ha _ Hs; apply HW; [exact Ha | lia]) HPR HRG3 HFSH) as [HB3 HF3].
pose proof HB as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PFBL & _).
exact (ho_segG c fpos ly2 S2 W2 mem3 md3 k2 regs3 sp1 F H2 T' (disco_classify_c.sight (c_FB c) (ho_L c)) r
  (disco_table_c.n_of T') 0 HB3 R19 R20 R23 R26 R27 HF3 HOK HH2 LT' eq_refl ltac:(lia) Hn Hr Q8 Q16 Q24 HGS
  (HuntObsFacts.sight_len (c_FB c) (ho_L c) PFBL) eq_refl ltac:(intros j Hj; lia) Hout HGO HANS).
Qed.

Ltac hoF_awr1 U2 :=
let a := fresh "a" in let Ha := fresh "Ha" in let rg := fresh "rg" in
let Hrg := fresh "Hrg" in let Hrng := fresh "Hrng" in
intros a Ha; destruct Ha as (rg & Hrg & Hrng);
cbn [ss_mem In] in Hrg;
repeat (destruct Hrg as [<- | Hrg];
  [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrng; rewrite ?U2 in Hrng;
   first [exfalso; lia | left; lia] | ]);
destruct Hrg.

Ltac hoF_ms MSn :=
lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msk) |- _ => rename msk into MSn
| HSx : st_ok _ _ _ (restrict _ ?msk) |- _ => rename msk into MSn end.

Ltac hoF_hw m0 MS sp U2 HWn :=
lazymatch goal with HFx : frame_of _ _ (mrestrict (w_H ?Wx) m0) (mrestrict _ (ms_mem MS)) |- _ =>
assert (HWn : forall a, 0 <= a < 2 ^ 64 -> ~ (sp <= a < sp + 56) ->
   aview SEGS (w_H Wx) (ms_mem MS) a = aview SEGS (w_H Wx) m0 a);
[ let a := fresh "a" in let Ha := fresh "Ha" in let Hs := fresh "Hs" in
  let rg := fresh "rg" in let Hrg := fresh "Hrg" in let Hrng := fresh "Hrng" in
  intros a Ha Hs; apply (hoF_aview_frame _ _ Wx m0 (ms_mem MS) a HFx Ha);
  intros (rg & Hrg & Hrng); cbn [ss_mem In] in Hrg;
  repeat (destruct Hrg as [<- | Hrg];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrng; rewrite ?U2 in Hrng; lia | ]);
  destruct Hrg
| clear HFx ] end;
try (lazymatch goal with HFx : frame_of _ _ m0 (ms_mem MS) |- _ => clear HFx end).

Ltac hoF_hp m0 MS HPn :=
lazymatch goal with HGx : mem_grows (mrestrict (w_H ?Wx) m0) (mrestrict _ (ms_mem MS)) |- _ =>
assert (HPn : forall a, apresent (w_H Wx) m0 a -> apresent (w_H Wx) (ms_mem MS) a)
  by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; eapply apresent_grows; [exact HGx | exact Ha]);
clear HGx end.

Ltac hoF_rd HS r Hr :=
lazymatch type of HS with
| st_ok_pi _ _ ?Ev ?ssx (restrict ?Hv ?msx) =>
  pose proof (st_ok_pi_restrict_reg Hv Ev ssx msx r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
  change (sr_get (ss_regs ssx) r) with e in Hr
| st_ok ?sg ?Ev ?ssx (restrict ?Hv ?msx) =>
  pose proof (st_ok_restrict_reg sg Hv Ev ssx msx r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
  change (sr_get (ss_regs ssx) r) with e in Hr end.

Ltac hoF_same HS AG Ren r n :=
let Hr := fresh "Hr" in hoF_rd HS r Hr;
rewrite Hr, hoF_off0; try rewrite (AG n ltac:(lia)); apply Ren; [lia | reflexivity].

Lemma hoF_post : forall (c : hoC) fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 T' ret,
  ho_base c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ->
  0 <= ret < 2 ^ 64 ->
  getr regs2 19 = w64 (c_out c) -> getr regs2 20 = w64 (if ret =? 0 then 0 else 1) ->
  getr regs2 22 = w64 (c_h c + 384) -> getr regs2 23 = w64 (F + 32) ->
  getr regs2 27 = w64 (SB + (c_h c + 384) / 8) -> getr regs2 26 = w64 SB ->
  ho_fsh W2 mem2 F ho_shC -> hunt_c.hunt_ok H2 ->
  H2 = T' ++ skipn 400 H2 -> length T' = 400%nat ->
  garr8 SEGS (mrestrict (w_H W2) mem2) (F + 32)
    (map (fun b : byte => bv_unsigned b) (disco_classify_c.sight (c_FB c) (ho_L c))) ->
  reac_disco_table_observe_c.observe_model (disco_table_c.sub (c_H c) 0 400)
    (disco_classify_c.sight (c_FB c) (ho_L c)) 0 (c_now c) T' ret ->
  disco_classify_c.cm_ret (c_FB c) (ho_L c) (ho_U c) (ho_Lk c) = 0 ->
  skipn 400 H2 = ho_Lk' c ++ disco_table_c.sub (c_H c) 412 12 ++
    (if disco_table_c.n_of (disco_table_c.sub (c_H c) 0 400) =? 0
     then Mem.le8 (Z_to_bv 64 (c_now c)) else disco_table_c.sub (c_H c) 424 8) ++ skipn 432 (c_H c) ->
  c_out c <> 0 ->
  garr8 SEGS (mrestrict (w_H W2) mem2) (c_out c)
    (map (fun b : byte => bv_unsigned b) (disco_classify_c.sight (c_FB c) (ho_L c))) ->
  SRr SEGS W2 (ho_cfg c regs2 mem2 md2 0x7414) (ho_post c).
Proof.
intros c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 T' ret HB Hret R19 R20 R22 R23 R27 R26 HFSH HOK2 HH2 LT'
  HGS HOM HRET HSK Hout HGO.
pose proof HB as (HPRE & HMID & HSP1 & HFeq & HRG & HSV).
pose proof HMID as (HJ & Hfrs & Hfa & Hperm & HKEPT & HROm & HGH & HLH & HFLAG & HKLE).
pose proof HRG as (R2 & R3 & R4 & R8 & R9 & R18 & R21 & R24 & R25).
pose proof HPRE as (PJ & PRO & PRA & PRA4 & PGP & PTP & PAL & PWIN & PSP & PDEP & PLEN & PNOW &
  POUT & PH0 & PH8 & PIN & PHB & PHE & PHW & PHOK & PFBL & PHG & PF50 & POUTF & PKM & PKT).
pose proof HSP1 as (HSP1a & HSP1b & HSP1c).
assert (HSTK : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
rewrite HSTK in PWIN.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (Hsp47 : YM05.alloc_ceiling + 8512 <= sp1 /\ sp1 + 160 <= c_sp0 c /\ c_sp0 c <= 2 ^ 47).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & X0 & X1 & X2 & X3 & _) & _).
  lia. }
destruct Hsp47 as (Hsp1lo & Hsp1hi & Hsp47).
destruct (POUTF Hout) as (HTO & _ & _). destruct HTO as (_ & H63 & _ & HSPS & _). rewrite HSTK in HSPS.
assert (HinH : In (c_hb c, c_hn c) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); exact PIN).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (c_hb c) (c_hn c) (proj1 HJ) HinH)
  as (_ & _ & Hbceil & _ & _ & _ & _).
assert (HsubT : disco_table_c.sub H2 0 400 = T') by (apply hoF_subT; assumption).
assert (Hr01 : (if ret =? 0 then 0 else 1) = 0 \/ (if ret =? 0 then 0 else 1) = 1)
  by (destruct (ret =? 0); [left | right]; reflexivity).
destruct (ho_mid_entry c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ho_shC false 0x7414 HB HFSH
   eq_refl ltac:(unfold ho_shC; repeat (apply Forall_cons; [lia|]); apply Forall_nil)
   ltac:(discriminate)) as [HS HEI].
pose proof (ho_shokM c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F false HB ltac:(discriminate)) as SHOK.
pose (RUN := paj_run (fx := c_fq c) B LAWS).
pose (RUNTO := paj_run_to (fx := c_fq c) B LAWS).
pose (BR := paj_branch (fx := c_fq c) (PI := PI)).
assert (AG : forall m, (m < 33)%nat -> ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) m
                                     = ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) m) by reflexivity.
assert (E21x : ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) 21 = Z_to_bv 64 (c_h c))
  by (rewrite (hoF_ereg c regs2 _ 21 21%bv ltac:(lia) ltac:(reflexivity)); exact R21).
assert (E2x : ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) 2 = Z_to_bv 64 sp1)
  by (rewrite (hoF_ereg c regs2 _ 2 2%bv ltac:(lia) ltac:(reflexivity)); exact R2).
pose proof (hoF_e32 c regs2 (flag_addr (c_lyc c) 1 fpos)) as E32x.
assert (Hdv : (c_h c + 384) / 8 <= c_h c + 384) by (apply Z.div_le_upper_bound; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (22%bv : bv 5) (SOff 21 384) HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E21x, unsigned_lit_small by lia; rewrite R22; reflexivity)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (27%bv : bv 5)
  (SAlu ALU_ADD (SAlu ALU_SRL (SOff 21 384) (SLit 3)) (SOff 32 0)) HS ltac:(vm_compute; reflexivity)
  ltac:(rewrite (hoF_u_shadow Ev 21 32 (c_h c) 384 SB E21x E32x) by (unfold SB; lia);
        cbn [ms_regs restrict mkst]; rewrite R27; reflexivity)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (9%bv : bv 5) (SOff 2 0) HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E2x, unsigned_lit_small by lia; rewrite Z.add_0_r, R9; reflexivity)) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
destruct (ho_count _ (c_h c) H2 HOK2 HGH) as [Hn HV].
rewrite HsubT in Hn, HV.
add_atom HS 60%nat (Z_to_bv 64 (disco_table_c.n_of T')) E60.
rebaseE HS AG HEv. clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  pose proof (hoF_shok_env _ Ex _ (AG 21%nat ltac:(lia)) (AG 32%nat ltac:(lia)) SHOK) as SHOK2 end.
clear SHOK. rename SHOK2 into SHOK.
ra_join_fact HS 60%nat (mkAF 0 8 0) ltac:(rewrite E60, unsigned_lit_small by lia;
  change (2 ^ 0) with 1; rewrite Z.mod_1_r; split; [lia|]; split; [reflexivity | lia]).
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
pose proof (ast_ok_pi_set_region Ex ssx msx 8%nat (YP09.mkRegion (Some 21%nat) 0 480 0 480 [])
  (YP09.mkRegion (Some 21%nat) 0 480 0 480 [YP09.mkChunk 384 (CVal 4 (SOff 60 0))]) HS
  ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  ltac:(apply (hoEF_region_wc Ex (ms_mem msx) 21%nat 0 480 0 480 [] 0 480);
        [ exact (st_ok_pi_region_nth Ex ssx msx 8%nat (YP09.mkRegion (Some 21%nat) 0 480 0 480 []) HS
                   ltac:(vm_compute; reflexivity))
        | right; split; lia
        | cbn [base_val]; rewrite (AG 21%nat ltac:(lia)), E21x, unsigned_lit_small by lia;
          apply (chunk_ok_val SEGS Ex _ (c_h c) 384 4 (SOff 60 0) (disco_table_c.n_of T'));
          [ cbn [sv_denot]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | zside | zside | exact HV ] ])) as HS3;
clear HS; rename HS3 into HS end. norm_ss HS.
hoF_ro HS 1%nat. hoF_ro HS 6%nat. hoF_ro HS 7%nat. hoF_ro HS 8%nat.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
assert (U2 : bv_unsigned (ew Ex 2) = sp1) by (rewrite (AG 2%nat ltac:(lia)), E2x; apply unsigned_lit_small; lia) end.
assert (E21y := E21x). rewrite <- (AG 21%nat ltac:(lia)) in E21y.
unfold ho_cfg.
paj_run_tok RUN HS HJ SHOK HOspan.
{ hoF_awr1 U2. }
hoF_ms MS1. hoF_hw mem2 MS1 sp1 U2 HW1. hoF_hp mem2 MS1 HP1.
psrr_branch_tok RUN BR HS SHOK HOspan.
- norm_ss HS.
  lazymatch type of Hc with context [sv_denot ?Ex (SLit 0)] =>
    rewrite (hoF_bge Ex 60 (disco_table_c.n_of T') E60 Hn) in Hc end.
  apply Z.leb_le in Hc. assert (Hn0 : disco_table_c.n_of T' = 0) by lia.
  paj_run_to_tok RUNTO HS HJ SHOK HOspan 0x7344.
  { hoF_awr1 U2. }
  pmkst HS.
  hoF_ms MS2. hoF_hw (ms_mem MS1) MS2 sp1 U2 HW2. hoF_hp (ms_mem MS1) MS2 HP2.
  assert (HW : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 <= a < sp1 + 56) ->
    aview SEGS (w_H W2) (ms_mem MS2) a = aview SEGS (w_H W2) mem2 a)
    by (intros a Ha Hs; rewrite (HW2 a Ha Hs); exact (HW1 a Ha Hs)).
  assert (HP : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem MS2) a)
    by (intros a Ha; exact (HP2 a (HP1 a Ha))).
  assert (Q2 : getr (ms_regs MS2) 2 = getr regs2 2) by hoF_same HS AG hoF_ereg (2%bv : bv 5) 2%nat.
  assert (Q3 : getr (ms_regs MS2) 3 = getr regs2 3) by hoF_same HS AG hoF_ereg (3%bv : bv 5) 3%nat.
  assert (Q4 : getr (ms_regs MS2) 4 = getr regs2 4) by hoF_same HS AG hoF_ereg (4%bv : bv 5) 4%nat.
  assert (Q8 : getr (ms_regs MS2) 8 = getr regs2 8) by hoF_same HS AG hoF_ereg (8%bv : bv 5) 8%nat.
  assert (Q18 : getr (ms_regs MS2) 18 = getr regs2 18) by hoF_same HS AG hoF_ereg (18%bv : bv 5) 18%nat.
  assert (Q21 : getr (ms_regs MS2) 21 = getr regs2 21) by hoF_same HS AG hoF_ereg (21%bv : bv 5) 21%nat.
  assert (Q24 : getr (ms_regs MS2) 24 = getr regs2 24) by hoF_same HS AG hoF_ereg (24%bv : bv 5) 24%nat.
  assert (Q25 : getr (ms_regs MS2) 25 = getr regs2 25) by hoF_same HS AG hoF_ereg (25%bv : bv 5) 25%nat.
  assert (Q9 : getr (ms_regs MS2) 9 = getr regs2 9)
    by (let Hr := fresh "Hr" in hoF_rd HS (9%bv : bv 5) Hr;
        rewrite Hr, hoF_off0, (AG 2%nat ltac:(lia)), E2x, R9; reflexivity).
  assert (Q20 : getr (ms_regs MS2) 20 = w64 (if ret =? 0 then 0 else 1))
    by (let Hr := fresh "Hr" in hoF_rd HS (20%bv : bv 5) Hr;
        rewrite Hr, hoF_off0, (AG 20%nat ltac:(lia)), (hoF_ereg c regs2 _ 20 20%bv ltac:(lia) ltac:(reflexivity));
        exact R20).
  refine (hoF_toT c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F (ms_mem MS2) _ (ms_regs MS2)
    (if ret =? 0 then 0 else 1) HB HJ HW HP
    (hoF_regs_mid c regs2 (ms_regs MS2) sp1 F HRG Q2 Q3 Q4 Q8 Q9 Q18 Q21 Q24 Q25) HFSH Q20
    ltac:(destruct Hr01 as [X | X]; rewrite X; lia) HOK2 _).
  apply (hoF_model c T'); [exact HOM | exact HRET | exact HH2 | exact HSK |].
  intros _. exists (disco_classify_c.sight (c_FB c) (ho_L c)).
  assert (HA : reac_hunt_observe_c.ho_answer T' (disco_classify_c.sight (c_FB c) (ho_L c))
                 (disco_classify_c.sight (c_FB c) (ho_L c))) by (apply hoF_ans_empty; exact Hn0).
  split; [exact HA|]. split.
  + apply (hoF_garr_ext W2 mem2 (ms_mem MS2)); [|exact HGO].
    intros i Hi. rewrite length_map, (HuntObsFacts.sight_len (c_FB c) (ho_L c) PFBL) in Hi.
    change (Z.of_nat 24) with 24 in Hi. apply HW; lia.
  + exact (tho_facts_hold (c_H c) (c_FB c) T' _ (c_len c) (c_now c) ret PFBL PHOK HRET HOM LT' HA).
- norm_ss HS.
  lazymatch type of Hc with context [sv_denot ?Ex (SLit 0)] =>
    rewrite (hoF_bge Ex 60 (disco_table_c.n_of T') E60 Hn) in Hc end.
  apply Z.leb_gt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK HOspan 0x7448.
  { hoF_awr1 U2. }
  pmkst HS.
  hoF_ms MS2. hoF_hw (ms_mem MS1) MS2 sp1 U2 HW2. hoF_hp (ms_mem MS1) MS2 HP2.
  assert (HW : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 <= a < sp1 + 56) ->
    aview SEGS (w_H W2) (ms_mem MS2) a = aview SEGS (w_H W2) mem2 a)
    by (intros a Ha Hs; rewrite (HW2 a Ha Hs); exact (HW1 a Ha Hs)).
  assert (HP : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem MS2) a)
    by (intros a Ha; exact (HP2 a (HP1 a Ha))).
  assert (Q2 : getr (ms_regs MS2) 2 = getr regs2 2) by hoF_same HS AG hoF_ereg (2%bv : bv 5) 2%nat.
  assert (Q3 : getr (ms_regs MS2) 3 = getr regs2 3) by hoF_same HS AG hoF_ereg (3%bv : bv 5) 3%nat.
  assert (Q4 : getr (ms_regs MS2) 4 = getr regs2 4) by hoF_same HS AG hoF_ereg (4%bv : bv 5) 4%nat.
  assert (Q8 : getr (ms_regs MS2) 8 = getr regs2 8) by hoF_same HS AG hoF_ereg (8%bv : bv 5) 8%nat.
  assert (Q18 : getr (ms_regs MS2) 18 = getr regs2 18) by hoF_same HS AG hoF_ereg (18%bv : bv 5) 18%nat.
  assert (Q21 : getr (ms_regs MS2) 21 = getr regs2 21) by hoF_same HS AG hoF_ereg (21%bv : bv 5) 21%nat.
  assert (Q24 : getr (ms_regs MS2) 24 = getr regs2 24) by hoF_same HS AG hoF_ereg (24%bv : bv 5) 24%nat.
  assert (Q25 : getr (ms_regs MS2) 25 = getr regs2 25) by hoF_same HS AG hoF_ereg (25%bv : bv 5) 25%nat.
  assert (Q9 : getr (ms_regs MS2) 9 = getr regs2 9)
    by (let Hr := fresh "Hr" in hoF_rd HS (9%bv : bv 5) Hr;
        rewrite Hr, hoF_off0, (AG 2%nat ltac:(lia)), E2x, R9; reflexivity).
  assert (Q19 : getr (ms_regs MS2) 19 = w64 (48 * disco_table_c.n_of T'))
    by (let Hr := fresh "Hr" in hoF_rd HS (19%bv : bv 5) Hr;
        rewrite Hr; exact (hoF_mul48 _ 60 (disco_table_c.n_of T') E60 Hn)).
  assert (Q20 : getr (ms_regs MS2) 20 = w64 (2 ^ 64 - 1 - c_h c))
    by (let Hr := fresh "Hr" in hoF_rd HS (20%bv : bv 5) Hr;
        rewrite Hr; exact (hoF_not _ 21 (c_h c) E21y ltac:(lia))).
  assert (Q23 : getr (ms_regs MS2) 23 = w64 (F + 32))
    by (let Hr := fresh "Hr" in hoF_rd HS (23%bv : bv 5) Hr;
        rewrite Hr, hoF_off0, (AG 23%nat ltac:(lia)), (hoF_ereg c regs2 _ 23 23%bv ltac:(lia) ltac:(reflexivity));
        exact R23).
  assert (Q26 : getr (ms_regs MS2) 26 = w64 432)
    by (let Hr := fresh "Hr" in hoF_rd HS (26%bv : bv 5) Hr; rewrite Hr; reflexivity).
  assert (Q27 : getr (ms_regs MS2) 27 = w64 (48 * 0))
    by (let Hr := fresh "Hr" in hoF_rd HS (27%bv : bv 5) Hr; rewrite Hr; reflexivity).
  lazymatch type of HS with st_ok_pi _ _ ?Ek ?ssk (restrict ?Hk ?msk) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssk) got_regionP) in
    pose proof (st_ok_pi_region_nth Ek ssk (restrict Hk msk) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
  cbn [ms_mem restrict] in HR0.
  assert (RD8 : rdword (aview SEGS (w_H W2) (ms_mem MS2)) (sp1 + 8) = Some SB).
  { apply rdword_of_val_mem; [|unfold SB; lia].
    refine (field_of_region _ _ 2%nat sp1 _ 0 56 0 56 8 8%N (SOff 26 0) SB HR0 U2 _ _ _ _).
    - cbn [In]. repeat (first [left; reflexivity | right]).
    - rewrite hoF_off0, (AG 26%nat ltac:(lia)), (hoF_ereg c regs2 _ 26 26%bv ltac:(lia) ltac:(reflexivity)).
      exact R26.
    - unfold SB. cbn. lia.
    - cbn. lia. }
  assert (RD16 : rdword (aview SEGS (w_H W2) (ms_mem MS2)) (sp1 + 16) = Some (c_out c)).
  { apply rdword_of_val_mem; [|lia].
    refine (field_of_region _ _ 2%nat sp1 _ 0 56 0 56 16 8%N (SOff 19 0) (c_out c) HR0 U2 _ _ _ _).
    - cbn [In]. repeat (first [left; reflexivity | right]).
    - rewrite hoF_off0, (AG 19%nat ltac:(lia)), (hoF_ereg c regs2 _ 19 19%bv ltac:(lia) ltac:(reflexivity)).
      exact R19.
    - cbn. lia.
    - cbn. lia. }
  assert (RD24 : rdword (aview SEGS (w_H W2) (ms_mem MS2)) (sp1 + 24) = Some (if ret =? 0 then 0 else 1)).
  { apply rdword_of_val_mem; [|destruct Hr01 as [X | X]; rewrite X; lia].
    refine (field_of_region _ _ 2%nat sp1 _ 0 56 0 56 24 8%N (SOff 20 0) (if ret =? 0 then 0 else 1) HR0 U2 _ _ _ _).
    - cbn [In]. repeat (first [left; reflexivity | right]).
    - rewrite hoF_off0, (AG 20%nat ltac:(lia)), (hoF_ereg c regs2 _ 20 20%bv ltac:(lia) ltac:(reflexivity)).
      exact R20.
    - cbn. destruct Hr01 as [X | X]; rewrite X; lia.
    - cbn. lia. }
  assert (LG : length (disco_classify_c.sight (c_FB c) (ho_L c)) = 24%nat)
    by exact (HuntObsFacts.sight_len (c_FB c) (ho_L c) PFBL).
  refine (hoF_toG c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F (ms_mem MS2) _ (ms_regs MS2) T'
    (if ret =? 0 then 0 else 1) HB HJ HW HP
    (hoF_regs_mid c regs2 (ms_regs MS2) sp1 F HRG Q2 Q3 Q4 Q8 Q9 Q18 Q21 Q24 Q25) HFSH Q19 Q20 Q23 Q26 Q27
    HOK2 HH2 LT' ltac:(lia) Hr01 RD8 RD16 RD24 _ Hout _ _).
  + apply (hoF_garr_ext W2 mem2 (ms_mem MS2)); [|exact HGS].
    intros i Hi. rewrite length_map, LG in Hi. change (Z.of_nat 24) with 24 in Hi.
    pose proof (frames_bounds _ _ LAWS ly2 S2 W2 mem2 md2 1 fpos (proj1 (proj1 HMID))
      ltac:(rewrite Hfrs; left; reflexivity)) as (HF1 & HF2 & _).
    rewrite Hfa, <- HFeq in HF1, HF2. change (fs_frame_bytes 1) with 128 in HF2.
    apply HW; lia.
  + apply (hoF_garr_ext W2 mem2 (ms_mem MS2)); [|exact HGO].
    intros i Hi. rewrite length_map, LG in Hi. change (Z.of_nat 24) with 24 in Hi. apply HW; lia.
  + intros A HA. apply (hoF_model c T'); [exact HOM | exact HRET | exact HH2 | exact HSK |].
    intros _. exists A. split; [exact HA|]. split; [reflexivity|].
    exact (tho_facts_hold (c_H c) (c_FB c) T' A (c_len c) (c_now c) ret PFBL PHOK HRET HOM LT' HA).
Qed.

Lemma ho_segF : ho_seg_F_stmt.
Proof.
unfold ho_seg_F_stmt.
intros c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 T' ret HB R10 Hret R19 R20 R22 R23 R27 R26
  HFSH HOK2 HH2 LT' HGS HOM HRET HSK HGO.
pose proof HB as (HPRE & HMID & HSP1 & HFeq & HRG & HSV).
pose proof HMID as (HJ & Hfrs & Hfa & Hperm & HKEPT & HROm & HGH & HLH & HFLAG & HKLE).
pose proof HRG as (R2 & R3 & R4 & R8 & R9 & R18 & R21 & R24 & R25).
pose proof HPRE as (PJ & PRO & PRA & PRA4 & PGP & PTP & PAL & PWIN & PSP & PDEP & PLEN & PNOW &
  POUT & PH0 & PH8 & PIN & PHB & PHE & PHW & PHOK & PFBL & PHG & PF50 & POUTF & PKM & PKT).
pose proof HSP1 as (HSP1a & HSP1b & HSP1c).
assert (HSTK : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
rewrite HSTK in PWIN.
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (Hsp47 : YM05.alloc_ceiling + 8512 <= sp1 /\ sp1 + 160 <= c_sp0 c /\ c_sp0 c <= 2 ^ 47 /\
                c_sp0 c mod 16 = 0 /\ c_sp0 c - c_STK c <= sp1 - 8512).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (X5 & _ & X0 & X1 & X2 & X3 & _) & _).
  repeat split; lia. }
destruct Hsp47 as (Hsp1lo & Hsp1hi & Hsp47 & Hsp0al & Hsp1stk).
assert (HinF : In (1, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (HFA1 : frame_addr ly2 1 fpos = F) by (rewrite Hfa; symmetry; exact HFeq).
pose proof (frames_bounds _ _ LAWS ly2 S2 W2 mem2 md2 1 fpos (proj1 HJ) HinF) as (HF1 & HF2 & HFapp).
rewrite HFA1 in HF1, HF2, HFapp. change (fs_frame_bytes 1) with 128 in HF2, HFapp.
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 1 fpos (proj1 HJ) HinF) as (HF64 & _ & _).
rewrite HFA1 in HF64.
assert (HF8 : 8 * (F / 8) <= F) by (apply Z.mul_div_le; lia).
assert (HF8p : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (LG : length (disco_classify_c.sight (c_FB c) (ho_L c)) = 24%nat)
  by exact (HuntObsFacts.sight_len (c_FB c) (ho_L c) PFBL).
destruct (ho_mid_entry c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ho_shC false 0x73fc HB HFSH
   eq_refl ltac:(unfold ho_shC; repeat (apply Forall_cons; [lia|]); apply Forall_nil)
   ltac:(discriminate)) as [HS HEI].
pose proof (ho_shokM c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F false HB ltac:(discriminate)) as SHOK.
pose (RUN := paj_run (fx := c_fq c) B LAWS).
pose (RUNTO := paj_run_to (fx := c_fq c) B LAWS).
pose (BR := paj_branch (fx := c_fq c) (PI := PI)).
assert (AG : forall m, (m < 33)%nat -> ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) m
                                     = ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) m) by reflexivity.
assert (E2x : ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) 2 = Z_to_bv 64 sp1)
  by (rewrite (hoF_ereg c regs2 _ 2 2%bv ltac:(lia) ltac:(reflexivity)); exact R2).
assert (E19x : ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) 19 = Z_to_bv 64 (c_out c))
  by (rewrite (hoF_ereg c regs2 _ 19 19%bv ltac:(lia) ltac:(reflexivity)); exact R19).
assert (E10x : ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) 10 = Z_to_bv 64 ret)
  by (rewrite (hoF_ereg c regs2 _ 10 10%bv ltac:(lia) ltac:(reflexivity)); exact R10).
assert (U2 : bv_unsigned (ew (EHOm c regs2 (flag_addr (c_lyc c) 1 fpos)) 2) = sp1)
  by (rewrite E2x; apply unsigned_lit_small; lia).
hoF_ro HS 0%nat. hoF_ro HS 1%nat. hoF_ro HS 6%nat. hoF_ro HS 7%nat. hoF_ro HS 8%nat.
unfold ho_cfg.
paj_run_tok RUN HS HJ SHOK HOspan.
{ hoF_awr0. }
hoF_ms MS1. hoF_hw mem2 MS1 sp1 U2 HW1. hoF_hp mem2 MS1 HP1.
psrr_branch_tok RUN BR HS SHOK HOspan.
- norm_ss HS.
  rewrite branch_eq_U, (U_atom _ 19 (c_out c) E19x POUT), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK HOspan 0x7344.
  { hoF_awr0. }
  pmkst HS.
  hoF_ms MS2. hoF_hw (ms_mem MS1) MS2 sp1 U2 HW2. hoF_hp (ms_mem MS1) MS2 HP2.
  assert (HW : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 <= a < sp1 + 56) ->
    aview SEGS (w_H W2) (ms_mem MS2) a = aview SEGS (w_H W2) mem2 a)
    by (intros a Ha Hs; rewrite (HW2 a Ha Hs); exact (HW1 a Ha Hs)).
  assert (HP : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem MS2) a)
    by (intros a Ha; exact (HP2 a (HP1 a Ha))).
  assert (Q2 : getr (ms_regs MS2) 2 = getr regs2 2) by hoF_same HS AG hoF_ereg (2%bv : bv 5) 2%nat.
  assert (Q3 : getr (ms_regs MS2) 3 = getr regs2 3) by hoF_same HS AG hoF_ereg (3%bv : bv 5) 3%nat.
  assert (Q4 : getr (ms_regs MS2) 4 = getr regs2 4) by hoF_same HS AG hoF_ereg (4%bv : bv 5) 4%nat.
  assert (Q8 : getr (ms_regs MS2) 8 = getr regs2 8) by hoF_same HS AG hoF_ereg (8%bv : bv 5) 8%nat.
  assert (Q9 : getr (ms_regs MS2) 9 = getr regs2 9) by hoF_same HS AG hoF_ereg (9%bv : bv 5) 9%nat.
  assert (Q18 : getr (ms_regs MS2) 18 = getr regs2 18) by hoF_same HS AG hoF_ereg (18%bv : bv 5) 18%nat.
  assert (Q21 : getr (ms_regs MS2) 21 = getr regs2 21) by hoF_same HS AG hoF_ereg (21%bv : bv 5) 21%nat.
  assert (Q24 : getr (ms_regs MS2) 24 = getr regs2 24) by hoF_same HS AG hoF_ereg (24%bv : bv 5) 24%nat.
  assert (Q25 : getr (ms_regs MS2) 25 = getr regs2 25) by hoF_same HS AG hoF_ereg (25%bv : bv 5) 25%nat.
  assert (Q20 : getr (ms_regs MS2) 20 = w64 (if ret =? 0 then 0 else 1))
    by (let Hr := fresh "Hr" in hoF_rd HS (20%bv : bv 5) Hr; rewrite Hr; exact (hoF_snez _ 10 ret E10x Hret)).
  refine (hoF_toT c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F (ms_mem MS2) _ (ms_regs MS2)
    (if ret =? 0 then 0 else 1) HB HJ HW HP
    (hoF_regs_mid c regs2 (ms_regs MS2) sp1 F HRG Q2 Q3 Q4 Q8 Q9 Q18 Q21 Q24 Q25) HFSH Q20
    ltac:(destruct (ret =? 0); lia) HOK2 _).
  apply (hoF_model c T'); [exact HOM | exact HRET | exact HH2 | exact HSK |].
  intros X. exfalso. exact (X Hc).
- norm_ss HS.
  rewrite branch_eq_U, (U_atom _ 19 (c_out c) E19x POUT), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
  rename Hc into Hout.
  destruct (POUTF Hout) as (HTO & HSEPH & _).
  destruct HTO as (Hal8 & H63 & HAM & HSPS & _ & _ & _ & HAWR & _ & _ & _).
  rewrite HSTK in HSPS.
  pose proof (hoF_out_ra c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB Hout) as (HORA & HOHV).
  pose proof (hoF_out_safe c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB Hout) as HOS.
  paj_run_tok RUN HS HJ SHOK HOspan.
  { hoF_awr0. }
  hoF_ms MS2. hoF_hw (ms_mem MS1) MS2 sp1 U2 HW2. hoF_hp (ms_mem MS1) MS2 HP2.
  assert (HW : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 <= a < sp1 + 56) ->
    aview SEGS (w_H W2) (ms_mem MS2) a = aview SEGS (w_H W2) mem2 a)
    by (intros a Ha Hs; rewrite (HW2 a Ha Hs); exact (HW1 a Ha Hs)).
  assert (HP : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem MS2) a)
    by (intros a Ha; exact (HP2 a (HP1 a Ha))).
  assert (Q2 : getr (ms_regs MS2) 2 = getr regs2 2) by hoF_same HS AG hoF_ereg (2%bv : bv 5) 2%nat.
  assert (Q3 : getr (ms_regs MS2) 3 = getr regs2 3) by hoF_same HS AG hoF_ereg (3%bv : bv 5) 3%nat.
  assert (Q4 : getr (ms_regs MS2) 4 = getr regs2 4) by hoF_same HS AG hoF_ereg (4%bv : bv 5) 4%nat.
  assert (Q8 : getr (ms_regs MS2) 8 = getr regs2 8) by hoF_same HS AG hoF_ereg (8%bv : bv 5) 8%nat.
  assert (Q9 : getr (ms_regs MS2) 9 = getr regs2 9) by hoF_same HS AG hoF_ereg (9%bv : bv 5) 9%nat.
  assert (Q18 : getr (ms_regs MS2) 18 = getr regs2 18) by hoF_same HS AG hoF_ereg (18%bv : bv 5) 18%nat.
  assert (Q19 : getr (ms_regs MS2) 19 = getr regs2 19) by hoF_same HS AG hoF_ereg (19%bv : bv 5) 19%nat.
  assert (Q21 : getr (ms_regs MS2) 21 = getr regs2 21) by hoF_same HS AG hoF_ereg (21%bv : bv 5) 21%nat.
  assert (Q22 : getr (ms_regs MS2) 22 = getr regs2 22) by hoF_same HS AG hoF_ereg (22%bv : bv 5) 22%nat.
  assert (Q23 : getr (ms_regs MS2) 23 = getr regs2 23) by hoF_same HS AG hoF_ereg (23%bv : bv 5) 23%nat.
  assert (Q24 : getr (ms_regs MS2) 24 = getr regs2 24) by hoF_same HS AG hoF_ereg (24%bv : bv 5) 24%nat.
  assert (Q25 : getr (ms_regs MS2) 25 = getr regs2 25) by hoF_same HS AG hoF_ereg (25%bv : bv 5) 25%nat.
  assert (Q26 : getr (ms_regs MS2) 26 = getr regs2 26) by hoF_same HS AG hoF_ereg (26%bv : bv 5) 26%nat.
  assert (Q27 : getr (ms_regs MS2) 27 = getr regs2 27) by hoF_same HS AG hoF_ereg (27%bv : bv 5) 27%nat.
  assert (Q20 : getr (ms_regs MS2) 20 = w64 (if ret =? 0 then 0 else 1))
    by (let Hr := fresh "Hr" in hoF_rd HS (20%bv : bv 5) Hr; rewrite Hr; exact (hoF_snez _ 10 ret E10x Hret)).
  assert (Ra0 : getr (ms_regs MS2) 10 = w64 (c_out c))
    by (let Hr := fresh "Hr" in hoF_rd HS (10%bv : bv 5) Hr; rewrite Hr, hoF_off0; exact E19x).
  assert (Ra1 : getr (ms_regs MS2) 11 = w64 (F + 32))
    by (let Hr := fresh "Hr" in hoF_rd HS (11%bv : bv 5) Hr;
        rewrite Hr, hoF_off0, (hoF_ereg c regs2 _ 23 23%bv ltac:(lia) ltac:(reflexivity)); exact R23).
  assert (Ra2 : getr (ms_regs MS2) 12 = w64 24)
    by (let Hr := fresh "Hr" in hoF_rd HS (12%bv : bv 5) Hr; rewrite Hr; reflexivity).
  assert (Rra : getr (ms_regs MS2) 1 = Z_to_bv 64 (BASE + 29716))
    by (let Hr := fresh "Hr" in hoF_rd HS (1%bv : bv 5) Hr; rewrite Hr; exact (codeptr_val _ 29716 HEI)).
  assert (Hspz : spZ (ms_regs MS2) = sp1) by (unfold spZ; rewrite Q2, R2; apply unsigned_lit_small; lia).
  assert (HFSH2 : ho_fsh W2 (ms_mem MS2) F ho_shC).
  { intros i Hi. rewrite HW; [exact (HFSH i Hi) | unfold SB; lia | unfold SB; lia]. }
  assert (HGS2 : garr8 SEGS (mrestrict (w_H W2) (ms_mem MS2)) (F + 32)
    (map (fun b : byte => bv_unsigned b) (disco_classify_c.sight (c_FB c) (ho_L c)))).
  { apply (hoF_garr_ext W2 mem2 (ms_mem MS2)); [|exact HGS].
    intros i Hi. rewrite length_map, LG in Hi. change (Z.of_nat 24) with 24 in Hi. apply HW; lia. }
  pmkst HS.
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ _ _) ?mdX) _ =>
    eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIGMA AS___asan_memcpy) (AMEMCPY (c_fq c)) W2
      (ms_regs MS2) (ms_mem MS2) (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
      ((1, fpos) :: c_own c) ly2 S2 mdX k2 (c_out c) (F + 32) 24 (sp1 - c_sp0 c) _ HJ) end.
    - exact Ra0.
    - exact Ra1.
    - exact Ra2.
    - lia.
    - lia.
    - lia.
    - rewrite Hspz. lia.
    - assert (Hs16 : sp1 mod 16 = 0).
      { pose proof (Z_div_mod_eq_full sp1 32) as D.
        replace sp1 with ((sp1 / 32 * 2) * 16) by lia. apply Z.mod_mul. lia. }
      rewrite Zminus_mod, Hs16, Hsp0al. reflexivity.
    - lia.
    - unfold ESTACK. lia.
    - rewrite Q3. exact R3.
    - rewrite Q4. exact R4.
    - exact Rra.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. split.
      + apply (hoEF_awr_mid (c_STK c) (c_sp0 c) (c_FP c) (ablocks B (c_ly c) (c_S c))
          (ablocks B (c_lyc c) (c_Sc c)) (ablocks B ly2 S2) (c_lyc c) ly2 (c_own c) (1, fpos) a).
        * intros p Hp. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hp.
        * exact Hfa.
        * exact (proj1 (HAWR a Ha)).
      + unfold ESTACK. lia.
    - exact HAM.
    - unfold amem_range in HAM. rewrite CC3, CC4, CC5 in HAM.
      apply (range_addressable_kept_win (aview SEGS (w_H W2) mem2) _ sp1 (sp1 + 56)); [exact HW | lia | lia | lia | exact HORA].
    - intros _. unfold amem_range in HAM. rewrite CC3, CC4, CC5 in HAM.
      apply (shadow_hull_vis_kept_win (aview SEGS (w_H W2) mem2) _ sp1 (sp1 + 56)); [exact HW | lia | lia | lia | lia | exact HOHV].
    - split; [lia|]. split; [lia|]. split.
      { intros a Ha. split.
        - apply (hoF_garr_some W2 (ms_mem MS2) (F + 32) _ a HGS2). rewrite length_map, LG. change (Z.of_nat 24) with 24. lia.
        - rewrite Hspz. unfold ESTACK. lia. }
      split.
      { destruct (HOS (c_out c) ltac:(lia)) as (_ & X1 & _). destruct (HOS (c_out c + 23) ltac:(lia)) as (_ & X2 & _). lia. }
      split; [apply (amem_range_sub_app F 128); [exact HFapp | lia | lia | lia | lia]|].
      split.
      { assert (DF : (F + 32) / 8 = F / 8 + 4) by (replace (F + 32) with (F + 4 * 8) by lia; apply Z.div_add; lia).
        apply zero_shadow_range.
        - pose proof (Z_div_mod_eq_full F 64) as D. replace (F + 32) with ((F / 64 * 8 + 4) * 8) by lia.
          apply Z.mod_mul. lia.
        - reflexivity.
        - intros i Hi. change (24 / 8) with 3 in Hi. unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF, DF.
          replace (SB + (F / 8 + 4) + i) with (SB + F / 8 + (4 + i)) by lia.
          rewrite (HFSH2 (4 + i) ltac:(lia)).
          assert (Hi3 : i = 0 \/ i = 1 \/ i = 2) by lia.
          destruct Hi3 as [-> | [-> | ->]]; reflexivity. }
      intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 (ms_mem MS2) _ 1 fpos (F + 32) 24 (proj1 HJ) HinF);
        rewrite ?HFA1; try change (fs_frame_bytes 1) with 128; lia. }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff & Hfr & Hpres3 & Hsame).
  assert (P2 : getr regs3 2 = getr regs2 2) by (rewrite <- Q2; exact (HP3 2 ltac:(unfold acallee_saved; lia))).
  assert (P3 : getr regs3 3 = getr regs2 3) by (rewrite <- Q3; exact (HP3 3 ltac:(unfold acallee_saved; lia))).
  assert (P4 : getr regs3 4 = getr regs2 4) by (rewrite <- Q4; exact (HP3 4 ltac:(unfold acallee_saved; lia))).
  assert (P8 : getr regs3 8 = getr regs2 8) by (rewrite <- Q8; exact (HP3 8 ltac:(unfold acallee_saved; lia))).
  assert (P9 : getr regs3 9 = getr regs2 9) by (rewrite <- Q9; exact (HP3 9 ltac:(unfold acallee_saved; lia))).
  assert (P18 : getr regs3 18 = getr regs2 18) by (rewrite <- Q18; exact (HP3 18 ltac:(unfold acallee_saved; lia))).
  assert (P19 : getr regs3 19 = getr regs2 19) by (rewrite <- Q19; exact (HP3 19 ltac:(unfold acallee_saved; lia))).
  assert (P21 : getr regs3 21 = getr regs2 21) by (rewrite <- Q21; exact (HP3 21 ltac:(unfold acallee_saved; lia))).
  assert (P22 : getr regs3 22 = getr regs2 22) by (rewrite <- Q22; exact (HP3 22 ltac:(unfold acallee_saved; lia))).
  assert (P23 : getr regs3 23 = getr regs2 23) by (rewrite <- Q23; exact (HP3 23 ltac:(unfold acallee_saved; lia))).
  assert (P24 : getr regs3 24 = getr regs2 24) by (rewrite <- Q24; exact (HP3 24 ltac:(unfold acallee_saved; lia))).
  assert (P25 : getr regs3 25 = getr regs2 25) by (rewrite <- Q25; exact (HP3 25 ltac:(unfold acallee_saved; lia))).
  assert (P26 : getr regs3 26 = getr regs2 26) by (rewrite <- Q26; exact (HP3 26 ltac:(unfold acallee_saved; lia))).
  assert (P27 : getr regs3 27 = getr regs2 27) by (rewrite <- Q27; exact (HP3 27 ltac:(unfold acallee_saved; lia))).
  assert (P20 : getr regs3 20 = w64 (if ret =? 0 then 0 else 1))
    by (rewrite <- Q20; exact (HP3 20 ltac:(unfold acallee_saved; lia))).
  assert (HUP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_out c <> 0 /\ c_out c <= a < c_out c + 24) ->
    ~ (sp1 - 4096 <= a < sp1 + 56) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha Ho Hs.
    rewrite (Hfr a Ha ltac:(intros X; apply Ho; split; [exact Hout | exact X]) ltac:(unfold ESTACK; lia)).
    apply HW; [exact Ha | lia]. }
  destruct (hoF_base_mem c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F mem3 md3 regs3 HB HJ3 HUP3
    ltac:(intros a Ha; exact (Hpres3 a (HP a Ha)))
    (hoF_regs_mid c regs2 regs3 sp1 F HRG P2 P3 P4 P8 P9 P18 P21 P24 P25) HFSH) as [HB3 HFSH3].
  refine (hoF_post c fpos ly2 S2 W2 mem3 md3 k2 regs3 sp1 F H2 T' ret HB3 Hret
    ltac:(rewrite P19; exact R19) P20 ltac:(rewrite P22; exact R22) ltac:(rewrite P23; exact R23)
    ltac:(rewrite P27; exact R27) ltac:(rewrite P26; exact R26) HFSH3 HOK2 HH2 LT' _ HOM HRET HSK Hout _).
  + apply (hoF_garr_ext W2 mem2 mem3); [|exact HGS].
    intros i Hi. rewrite length_map, LG in Hi. change (Z.of_nat 24) with 24 in Hi.
    destruct (HOS (c_out c) ltac:(lia)) as (_ & X1 & _). destruct (HOS (c_out c + 23) ltac:(lia)) as (_ & X2 & _).
    apply HUP3; lia.
  + apply (hoF_garr_shift W2 mem2 mem3 (F + 32) (c_out c)); [|exact HGS].
    intros i Hi. rewrite length_map, LG in Hi. change (Z.of_nat 24) with 24 in Hi.
    rewrite (Heff i ltac:(lia)). apply HW; lia.
Qed.

End h.
End f.
End d.
