(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 577 of its 632 lines of code are new or changed and 1223 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC45 YC85 YC88 YCkd YC1g YC1h YC81 YC4b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel reac_master_only_cadence_ns_c reac_rate_snap_c
reac_frame_clean_len_c slot_inv slot_frame reac_hunt_verdict_name_c disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require CtrlParsed reac_disco_table_init_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntSeat DiscoYEntProCuts DiscoYEntProSeat DiscoYEntProDCuts DiscoYEntProDLib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require ReacDiscoTableInit ReacDiscoGateInit ReacDiscoPeerLockInit.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma pd_chk : forall lo hi cs,
  forallb (fun c => (lo <=? YP09.c_off c) && (YP09.c_off c + YP09.c_len c <=? hi)) cs = true ->
  forall c, In c cs -> forall i, 0 <= i < YP09.c_len c -> lo <= YP09.c_off c + i < hi.
Proof.
intros lo hi cs H c Hc i Hi. pose proof (proj1 (forallb_forall _ _) H c Hc) as Hx. cbn beta in Hx.
apply andb_prop in Hx as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma pd_awr_ro : forall E rs STK sp0 FP bl0 blc ly own,
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
intros E rs STK sp0 FP bl0 blc ly own Hc a (r & Hin & Ha).
pose proof (proj1 (forallb_forall _ _) Hc r Hin) as Hx. apply Z.leb_le in Hx. lia.
Qed.

Lemma pd_saddr_T : forall q, 0 <= q < 400 -> saddr_ok (2160 + q) (dsh_loop ((2160 + q) / 8)).
Proof. intros q Hq. rewrite pd_sh_T by lia. left. reflexivity. Qed.

Lemma pd_saddr_G : forall q, 0 <= q < 264 -> saddr_ok (2624 + q) (dsh_loop ((2624 + q) / 8)).
Proof. intros q Hq. rewrite pd_sh_G by lia. left. reflexivity. Qed.

Lemma pd_saddr_L : forall q, 0 <= q < 12 -> saddr_ok (2960 + q) (dsh_loop ((2960 + q) / 8)).
Proof.
intros q Hq. destruct (Z_lt_le_dec q 8) as [Hq8 | Hq8].
- replace ((2960 + q) / 8) with 370 by lia. rewrite pd_sh_L0. left. reflexivity.
- replace ((2960 + q) / 8) with 371 by lia. rewrite pd_sh_L1. right. split; lia.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma pd_frame_all : forall E rs (H : word -> bool) (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hc a. apply aview_eq_of. apply HF. intros (r & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hc r Hin) as Hx. apply Z.leb_le in Hx. lia.
Qed.

Lemma pd_frame_tr : forall (cx : dcx) (W : world SEGS) m (W2 : world SEGS) m2,
  p_frame cx dsh_loop ps_C3 W m ->
  0 <= d_A cx < 2 ^ 64 -> 0 <= d_FB cx < 2 ^ 64 -> 0 <= shadow_addr (d_FB cx) < 2 ^ 64 ->
  (forall a, (d_S cx - 104 <= a < d_S cx \/ d_A cx <= a < d_A cx + 472 \/ d_FB cx <= a < d_FB cx + 24 \/
              d_FB cx + 4088 <= a < d_FB cx + 4096 \/ shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384) ->
     aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) m a) ->
  (forall a, d_FB cx <= a < d_FB cx + 4096 -> apresent (w_H W2) m2 a) ->
  (forall i, 0 <= i < 512 -> apresent (w_H W2) m2 (shadow_addr (d_FB cx) + i)) ->
  (forall a, d_A cx <= a < d_A cx + 472 -> apresent (w_H W2) m2 a) ->
  p_frame cx dsh_loop ps_C3 W2 m2.
Proof.
intros cx W m W2 m2 (E & HE & HRG & HFL) HAr HFr HSr HK HPF HPS HPA.
pose proof HE as (EE & _ & _ & E60 & EF & ESH).
assert (U2 : base_val E (Some AT_STK) = d_S cx).
{ cbn [base_val]. unfold AT_STK. rewrite (EE 2%nat 2%bv eq_refl). reflexivity. }
assert (U60 : base_val E (Some AT_A) = d_A cx).
{ cbn [base_val]. rewrite E60. apply unsigned_lit_small. exact HAr. }
assert (U516 : base_val E (Some AT_F) = d_FB cx).
{ cbn [base_val]. rewrite EF. apply unsigned_lit_small. exact HFr. }
assert (U529 : base_val E (Some AT_SH) = shadow_addr (d_FB cx)).
{ cbn [base_val]. rewrite ESH. apply unsigned_lit_small. exact HSr. }
exists E. split; [exact HE|]. split.
- unfold p_regions in HRG |- *.
  pose proof (Forall_inv HRG) as R1. apply Forall_inv_tail in HRG.
  pose proof (Forall_inv HRG) as R2. apply Forall_inv_tail in HRG.
  pose proof (Forall_inv HRG) as R3. apply Forall_inv_tail in HRG.
  pose proof (Forall_inv HRG) as R4. clear HRG.
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (pd_rok_move E _ _ _ R1).
    * cbn [YP09.r_wlo YP09.r_whi]. intros o Ho. lia.
    * cbn [YP09.r_base YP09.r_chunks]. rewrite U2. intros c Hc i Hi.
      pose proof (pd_chk (-104) 0 dsave_chunks ltac:(vm_compute; reflexivity) c Hc i Hi) as Hci.
      apply (mbyte_of_aview SEGS). apply HK. left. lia.
  + apply (pd_rok_move E _ _ _ R2).
    * cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. rewrite U60. intros o Ho.
      apply (apresent_writable SEGS). apply HPA. lia.
    * cbn [YP09.r_base YP09.r_chunks]. rewrite U60. intros c Hc i Hi.
      pose proof (pd_chk 0 472 ps_C3 ltac:(vm_compute; reflexivity) c Hc i Hi) as Hci.
      apply (mbyte_of_aview SEGS). apply HK. right. left. lia.
  + apply (pd_rok_move E _ _ _ R3).
    * cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. rewrite U516. intros o Ho.
      apply (apresent_writable SEGS). apply HPF. unfold DFRAME_SIZE in Ho. lia.
    * cbn [YP09.r_base YP09.r_chunks]. rewrite U516. intros c Hc i Hi.
      pose proof (pd_chk 0 24 dfhdr3 ltac:(vm_compute; reflexivity) c Hc i Hi) as Hci.
      apply (mbyte_of_aview SEGS). apply HK. right. right. left. lia.
  + apply (pd_rok_move E _ _ _ R4).
    * unfold fshadow_region. cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. rewrite U529. intros o Ho.
      apply (apresent_writable SEGS). apply HPS. unfold DFRAME_SH in Ho. lia.
    * unfold fshadow_region. cbn [YP09.r_base YP09.r_chunks]. rewrite U529. intros c Hc i Hi.
      pose proof (pd_chk 0 384 (dsh_chunks dsh_loop) ltac:(vm_compute; reflexivity) c Hc i Hi) as Hci.
      apply (mbyte_of_aview SEGS). apply HK. right. right. right. right. lia.
- rewrite <- HFL. apply rdword_ext. intros kk Hkk. apply HK. right. right. right. left.
  change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
Qed.

Definition pd_zone (cx : dcx) (a : Z) : Prop :=
  d_S cx - 104 <= a < d_S cx \/ d_A cx <= a < d_A cx + 472 \/ d_FB cx <= a < d_FB cx + 4096 \/
  shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512.

Definition pd_kept (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
  (W2 : world SEGS) (mem2 : word -> option byte) (sp t n : Z) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - (16 + ESTACK) <= a < sp) -> ~ (t <= a < t + n) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ (t <= a < t + n) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a).

Lemma pd_keep_all : forall (cx : dcx) lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 t n,
  pd_kept lyc Sc W memc W2 mem2 (d_A cx) t n ->
  In (DFRAME_CLASS, c_fpos cx) (frames Sc) -> frame_addr lyc DFRAME_CLASS (c_fpos cx) = d_FB cx ->
  alloc_ceiling + LLVMF_STK <= d_S cx -> d_S cx <= 2 ^ 47 -> d_S cx - 607 <= d_A cx <= d_S cx - 576 ->
  forall a, pd_zone cx a -> ~ (t <= a < t + n) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros cx lyc Sc W memc W2 mem2 t n (K1 & K4) Hin Efa Hs1 Hs2 HA a Hz Hn.
pose proof asan_consts as (Hac & _). unfold LLVMF_STK, ESTACK in *.
destruct Hz as [Hz | [Hz | [Hz | Hz]]].
- apply K1; [lia | lia | exact Hn].
- apply K1; [lia | lia | exact Hn].
- apply (K4 DFRAME_CLASS (c_fpos cx) a Hin); [|exact Hn]. left.
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
- apply (K4 DFRAME_CLASS (c_fpos cx) a Hin); [|exact Hn]. right.
  unfold in_zr. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia.
Qed.

Lemma pd_blocks_perm : forall (B : asyms) cx h ly S ly2 S2,
  d_blocks B cx h [] ly S -> Permutation (ablocks B ly2 S2) (ablocks B ly S) -> d_blocks B cx h [] ly2 S2.
Proof.
intros B cx h ly S ly2 S2 (P1 & P2 & P3 & P4) HP.
split; [exact (perm_trans HP P1)|]. split; [exact P2|]. split; [|exact P4].
rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HP), <- (blocks_bytes_bsum B ly S). exact P3.
Qed.

Lemma pd_rC3_call : forall cx (B : asyms) (regs regsc regs2 : bvmap 5 word),
  p_rC3 cx B regs ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 23; 24; 27]%bv -> getr regsc r = getr regs r) ->
  aregs_preserved regsc regs2 -> p_rC3 cx B regs2.
Proof.
intros cx B regs regsc regs2 HR HG HP.
assert (K : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 23; 24; 27]%bv -> getr regs2 r = getr regs r).
{ intros r Hr. rewrite <- (HG r Hr). cbv [In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [match goal with |- getr _ ?rr = _ =>
    let z := eval vm_compute in (bv_unsigned rr) in exact (HP z ltac:(unfold acallee_saved; lia)) end|]).
  destruct Hr. }
destruct HR as ((Hsp & Hgp & Htp & H8 & H9 & H19 & H27) & H18 & H24 & H23).
unfold p_rC3, p_rbase, spZ in *.
rewrite !K by (cbv; tauto).
repeat split; assumption.
Qed.

Lemma pd_ra4096 : forall k, 0 <= k < 2 ^ 40 -> 4096 <= bv_unsigned (Z_to_bv 64 (BASE + k)).
Proof.
intros k Hk. pose proof (@pa_B_ok _ lib_both3_0_listing PI) as HB. pose proof (pa_base_lo (L := lib_both3_0_listing) (PI := PI)) as HL. unfold YImgTop.IMG_LO in HL.
rewrite unsigned_lit_small by lia. lia.
Qed.

Lemma pd_kept_T : forall (B : asyms) lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 sp t,
  ReacDiscoTableInit.treac_disco_table_init_kept B lyc Sc W memc W2 mem2 sp t -> pd_kept lyc Sc W memc W2 mem2 sp t 400.
Proof. intros B lyc Sc W memc W2 mem2 sp t (K1 & _ & _ & K4 & _). split; [exact K1 | exact K4]. Qed.

Lemma pd_kept_G : forall (B : asyms) lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 sp t,
  ReacDiscoGateInit.treac_disco_gate_init_kept B lyc Sc W memc W2 mem2 sp t -> pd_kept lyc Sc W memc W2 mem2 sp t 264.
Proof. intros B lyc Sc W memc W2 mem2 sp t (K1 & _ & _ & K4 & _). split; [exact K1 | exact K4]. Qed.

Lemma pd_kept_L : forall (B : asyms) lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 sp t,
  ReacDiscoPeerLockInit.treac_disco_peer_lock_init_kept B lyc Sc W memc W2 mem2 sp t -> pd_kept lyc Sc W memc W2 mem2 sp t 12.
Proof. intros B lyc Sc W memc W2 mem2 sp t (K1 & _ & _ & K4 & _). split; [exact K1 | exact K4]. Qed.

Lemma pd_shm : forall (cx : dcx) (W : world SEGS) m m',
  p_frame cx dsh_loop ps_C3 W m -> 0 <= shadow_addr (d_FB cx) < 2 ^ 64 ->
  (forall a, aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  forall k, 0 <= k < DFRAME_SH -> aview SEGS (w_H W) m' (shadow_addr (d_FB cx) + k) = Some (dsh_loop k).
Proof.
intros cx W m m' Hfr Hsh Heq k Hk. rewrite Heq.
exact (pd_sh_val cx dsh_loop ps_C3 W m ltac:(vm_compute; reflexivity) Hsh Hfr k Hk).
Qed.

Lemma pd_arith_zone : forall dS dA FB sh a off n,
  4096 <= FB -> FB + 4096 <= dS - 32768 -> dS - 607 <= dA <= dS - 576 ->
  (sh + 512 <= FB \/ FB + 4096 <= sh) -> 2160 <= off -> off + n <= 3072 ->
  (dS - 104 <= a < dS \/ dA <= a < dA + 472 \/ FB <= a < FB + 24 \/ FB + 4088 <= a < FB + 4096 \/ sh <= a < sh + 384) ->
  (dS - 104 <= a < dS \/ dA <= a < dA + 472 \/ FB <= a < FB + 4096 \/ sh <= a < sh + 512) /\
  ~ (FB + off <= a < FB + off + n).
Proof. intros dS dA FB sh a off n H1 H2 H3 H4 H5 H6 H7. lia. Qed.

Lemma pd_sh_disj : forall FB, in_app FB 4096 -> shadow_addr FB + 512 <= FB \/ FB + 4096 <= shadow_addr FB.
Proof.
intros FB H. pose proof ASAN_CEIL_range as (HC & _).
unfold in_app, shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

Ltac pd_ro HS n :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis TTINIT : ReacDiscoTableInit.treac_disco_table_init_spec B.
Hypothesis TGINIT : ReacDiscoGateInit.treac_disco_gate_init_spec B.
Hypothesis TLINIT : ReacDiscoPeerLockInit.treac_disco_peer_lock_init_spec B.

Definition pd_I (cx : dcx) (h : Z) (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word)
  (m : word -> option byte) (md : Model) (k : Z) : Prop :=
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly S W m md k /\ 0 <= k <= EV_PRO /\
  p_rC3 cx B regs /\ p_frame cx dsh_loop ps_C3 W m /\ d_blocks B cx h [] ly S /\
  val_mem SEGS (rd W m) (d_A cx + 184) 8 h /\ pd_our cx W m.

Lemma pd_post : forall cx h ly S (W : world SEGS) regs m md k (msr : bvmap 5 word) msm ly2 S2 (W2 : world SEGS) regs2 mem2 md2 off n,
  pd_I cx h ly S W regs m md k ->
  (forall a, aview SEGS (w_H W) msm a = aview SEGS (w_H W) m a) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 23; 24; 27]%bv -> getr msr r = getr regs r) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly2 S2 W2 mem2 md2 k ->
  aregs_preserved msr regs2 -> frames S2 = frames S -> Permutation (ablocks B ly2 S2) (ablocks B ly S) ->
  pd_kept ly S W msm W2 mem2 (d_A cx) (d_FB cx + off) n ->
  2160 <= off -> off + n <= 3072 ->
  pd_I cx h ly2 S2 W2 regs2 mem2 md2 k /\
  (forall a, d_FB cx <= a < d_FB cx + 4096 -> ~ (d_FB cx + off <= a < d_FB cx + off + n) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) m a).
Proof.
intros cx h ly S W regs m md k msr msm ly2 S2 W2 regs2 mem2 md2 off n (HC & Hk & HrC3 & Hfr & Hbl & H184 & Hour)
  Hmeq RG HJ2 HP2 Hfrs2 Hperm2 HK Hoff Hn.
pose proof HC as (Hbase & HJ & Hfrs).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC) as (HSmod & HSlo & HShi & HFB1 & HFB2 & HFBapp & HFBimg & HFBmod & _ & _ & _ & _ & Hin3 & EFB3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HAmod).
assert (HAr2 : d_S cx - 607 <= d_A cx <= d_S cx - 576) by (unfold MFRAME in HAr; lia).
assert (HArange : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in *; lia).
assert (HFBrange : 0 <= d_FB cx < 2 ^ 64) by lia.
pose proof (shadow_addr_bounds (d_FB cx) ltac:(unfold kHighMemEnd in *; lia)) as HSHb.
assert (HSHrange : 0 <= shadow_addr (d_FB cx) < 2 ^ 64) by (unfold kLowMemEnd, kHighShadowEnd in *; lia).
pose proof (pd_sh_disj (d_FB cx) HFBapp) as Hsd.
assert (HC2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 mem2 md2 k)
  by (split; [exact Hbase | split; [exact HJ2 | rewrite Hfrs2; exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC2) as (_ & _ & _ & _ & _ & _ & _ & _ & HFpres2 & HSHpres2 & HWpres2 & _ & _ & _ & _).
pose proof (pd_keep_all cx ly S W msm W2 mem2 (d_FB cx + off) n HK Hin3 EFB3 HSlo HShi HAr2) as Kz0.
assert (Kz : forall a, pd_zone cx a -> ~ (d_FB cx + off <= a < d_FB cx + off + n) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) m a).
{ intros a Hz Hnz. rewrite (Kz0 a Hz Hnz). apply Hmeq. }
clear Kz0.
assert (HFS : d_FB cx + 4096 <= d_S cx - 32768) by (unfold LLVMF_STK in *; lia).
split.
- split; [exact HC2|]. split; [exact Hk|]. split; [exact (pd_rC3_call cx B regs msr regs2 HrC3 RG HP2)|].
  split; [|split; [exact (pd_blocks_perm B cx h ly S ly2 S2 Hbl Hperm2)|split]].
  + apply (pd_frame_tr cx W m W2 mem2 Hfr HArange HFBrange HSHrange).
    * intros a Ha.
      destruct (pd_arith_zone (d_S cx) (d_A cx) (d_FB cx) (shadow_addr (d_FB cx)) a off n HFB1 HFS HAr2 Hsd Hoff Hn Ha)
        as (Hz & Hnz).
      exact (Kz a Hz Hnz).
    * exact HFpres2.
    * exact HSHpres2.
    * intros a Ha. apply HWpres2. unfold LLVMF_STK. lia.
  + apply (pd_val_kept W m W2 mem2 (d_A cx + 184) 8 h); [|exact H184].
    intros x Hx. apply Kz; [unfold pd_zone; lia | lia].
  + unfold pd_our in *. apply (garr8_aview_kept SEGS (w_H W) (w_H W2) m mem2); [|exact Hour].
    change (length (map (fun b : byte => bv_unsigned b) (our_of (c_pl cx)))) with 6%nat.
    intros a Ha. unfold d_obj, dobj_off in Ha.
    apply Kz; [unfold pd_zone; lia | lia].
- intros a Ha Hnz. apply Kz; [unfold pd_zone; lia | exact Hnz].
Qed.

Lemma pd_stepT : forall (fq : YK11.FPState) cx h ly S (W : world SEGS) regs m md k,
  pd_I cx h ly S W regs m md k ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + POFF_C4) regs m md)
    (fun W' c' => exists ly' S' regs' m' md',
       c' = cfg_at (fx := fq) SEGS (BASE + 0x710) regs' m' md' /\
       pd_I cx h ly' S' W' regs' m' md' k /\
       (forall a, d_FB cx <= a < d_FB cx + 4096 -> ~ (d_obj cx OT <= a < d_obj cx OT + 400) ->
          aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) /\
       pd_objT cx W' m').
Proof.
intros fq cx h ly S W regs m md k (HC & Hk & HrC3 & Hfr & Hbl & H184 & Hour).
pose proof HC as (Hbase & HJ & Hfrs).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC) as (HSmod & HSlo & HShi & HFB1 & HFB2 & HFBapp & HFBimg & HFBmod & HFpres & HSHpres & HWpres & HAR3 & Hin3 & EFB3 & EFL3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HAmod).
pose proof HrC3 as (HrB & H18 & H24 & H23).
assert (HAr2 : d_S cx - 607 <= d_A cx <= d_S cx - 576) by (unfold MFRAME in HAr; lia).
assert (HArange : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in *; lia).
assert (HFBrange : 0 <= d_FB cx < 2 ^ 64) by lia.
pose proof (shadow_addr_bounds (d_FB cx) ltac:(unfold kHighMemEnd in *; lia)) as HSHb.
assert (HSHrange : 0 <= shadow_addr (d_FB cx) < 2 ^ 64) by (unfold kLowMemEnd, kHighShadowEnd in *; lia).
pose proof Hfr as (E & HdE & HRG & HFL).
pose proof (pd_regs_ok cx E regs h B HdE HrB HArange HSHrange) as HROK.
pose proof (p_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_loop ps_C3 ly S W regs m md k E POFF_C4 pd_sr (pd_vals regs h) [] [] [] (d_facts [] []) HC HdE HRG HFL HROK
  (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly S W m md k E (pd_vals regs h) [] [] HC HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_p in HS.
pd_ro HS 60%nat. pd_ro HS 516%nat. pd_ro HS 529%nat.
assert (HEI : img_env VAL A_LIM (d_env cx E (pd_vals regs h))).
{ pose proof HdE as (_ & _ & HEI0 & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HEI0 a Ha). }
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS). pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + POFF_C4)) with (Z_to_bv 64 (BASE + POFF_C4)).
paj_run_shc RUNP RUNC HS HJ.
{ apply pd_awr_ro. vm_compute. reflexivity. }
set (Ed := d_env cx E (pd_vals regs h)) in *.
assert (Hmeq : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) m a).
{ lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    exact (pd_frame_all Ex rs (w_H W) m (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) end. }
clear HF HFr HG.
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 23; 24; 27]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r HS). rewrite (HROK r).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
assert (R1 : getr (ms_regs ms) 1%bv = Z_to_bv 64 (BASE + 1808)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  exact (codeptr_val _ 1808 HEI). }
assert (Ed516 : ew Ed 516 = Z_to_bv 64 (d_FB cx)).
{ subst Ed. unfold d_env. rewrite ew_havoc_old by (cbv; lia). pose proof HdE as (_ & _ & _ & _ & E516 & _). exact E516. }
assert (R10 : getr (ms_regs ms) 10%bv = w64 (d_obj cx OT)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  cbn [sv_denot]. rewrite Ed516. unfold w64, d_obj, dobj_off. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Hsp : spZ (ms_regs ms) = d_A cx).
{ unfold spZ. rewrite (RG 2%bv ltac:(cbv; tauto)). exact (proj1 HrB). }
assert (HCm : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly S W (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HCm) as (_ & _ & _ & _ & _ & _ & _ & _ & HFpresm & _ & _ & HARm & _ & _ & _).
pose proof (pd_shm cx W m (ms_mem ms) Hfr HSHrange Hmeq) as Hshm.
pmkst HS. rewrite pa_sigma_reac_disco_table_init.
eapply SRr_bind.
{ eapply (TTINIT fq LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly S W (ms_mem ms) _ k (ms_regs ms) (d_obj cx OT) HJ).
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite R1. apply pd_ra4096. lia.
  - rewrite (RG 3%bv ltac:(cbv; tauto)). exact (proj1 (proj2 HrB)).
  - rewrite (RG 4%bv ltac:(cbv; tauto)). exact (proj1 (proj2 (proj2 HrB))).
  - exact R10.
  - rewrite Hsp. lia.
  - rewrite Hsp. unfold LLVMF_STK, ReacDiscoTableInit.REAC_DISCO_TABLE_INIT_STK, ESTACK. lia.
  - rewrite Hsp. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - right. rewrite Hsp. unfold d_obj, dobj_off, ReacDiscoTableInit.REAC_DISCO_TABLE_INIT_STK, ESTACK, LLVMF_STK in *. lia.
  - intros a Ha. unfold d_obj, dobj_off in Ha. split.
    + right. right. right. exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite EFB3. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
    + apply HFpresm. lia.
  - unfold d_obj, dobj_off. apply (amem_range_sub_app (d_FB cx) 4096); [exact HFBapp | lia | lia | lia | lia].
  - unfold d_obj. cbn [dobj_off].
    apply (pd_ra_range cx dsh_loop W (ms_mem ms) 2160 400 Hshm); [lia | lia | lia | unfold DFRAME_SH; lia | exact pd_saddr_T].
  - apply (shadow_hull_vis_of_frame SEGS B LAWS ly S W (ms_mem ms) _ DFRAME_CLASS (c_fpos cx) _ 400 HARm Hin3);
      rewrite ?EFB3; unfold d_obj, dobj_off; change (fs_frame_bytes DFRAME_CLASS) with 4096; lia. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJ2 & HP2 & Hra2 & Hfrs2 & Hperm2 & HK & HGT & HTok).
apply SRr_ret.
rewrite Hsp in HK.
destruct (pd_post cx h ly S W regs m md k (ms_regs ms) (ms_mem ms) ly2 S2 W2 regs2 mem2 md2 2160 400
  (conj HC (conj Hk (conj HrC3 (conj Hfr (conj Hbl (conj H184 Hour)))))) Hmeq RG HJ2 HP2 Hfrs2 Hperm2
  (pd_kept_T B ly S W (ms_mem ms) W2 mem2 (d_A cx) (d_obj cx OT) HK) ltac:(lia) ltac:(lia)) as (HI2 & Kf).
exists ly2, S2, regs2, mem2, md2.
split; [rewrite Hc2, R1; reflexivity|].
split; [exact HI2|]. split.
- intros a Ha Hn. exact (Kf a Ha Hn).
- exists reac_disco_table_init_c.zero_table. split; [vm_compute; reflexivity|]. split; [exact HGT | exact HTok].
Qed.
Lemma pd_stepG : forall (fq : YK11.FPState) cx h ly S (W : world SEGS) regs m md k,
  pd_I cx h ly S W regs m md k ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + 0x710) regs m md)
    (fun W' c' => exists ly' S' regs' m' md',
       c' = cfg_at (fx := fq) SEGS (BASE + 0x718) regs' m' md' /\
       pd_I cx h ly' S' W' regs' m' md' k /\
       (forall a, d_FB cx <= a < d_FB cx + 4096 -> ~ (d_obj cx OG <= a < d_obj cx OG + 264) ->
          aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) /\
       pd_objG cx W' m').
Proof.
intros fq cx h ly S W regs m md k (HC & Hk & HrC3 & Hfr & Hbl & H184 & Hour).
pose proof HC as (Hbase & HJ & Hfrs).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC) as (HSmod & HSlo & HShi & HFB1 & HFB2 & HFBapp & HFBimg & HFBmod & HFpres & HSHpres & HWpres & HAR3 & Hin3 & EFB3 & EFL3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HAmod).
pose proof HrC3 as (HrB & H18 & H24 & H23).
assert (HAr2 : d_S cx - 607 <= d_A cx <= d_S cx - 576) by (unfold MFRAME in HAr; lia).
assert (HArange : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in *; lia).
assert (HFBrange : 0 <= d_FB cx < 2 ^ 64) by lia.
pose proof (shadow_addr_bounds (d_FB cx) ltac:(unfold kHighMemEnd in *; lia)) as HSHb.
assert (HSHrange : 0 <= shadow_addr (d_FB cx) < 2 ^ 64) by (unfold kLowMemEnd, kHighShadowEnd in *; lia).
pose proof Hfr as (E & HdE & HRG & HFL).
pose proof (pd_regs_ok cx E regs h B HdE HrB HArange HSHrange) as HROK.
pose proof (p_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_loop ps_C3 ly S W regs m md k E 0x710 pd_sr (pd_vals regs h) [] [] [] (d_facts [] []) HC HdE HRG HFL HROK
  (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly S W m md k E (pd_vals regs h) [] [] HC HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_p in HS.
pd_ro HS 60%nat. pd_ro HS 516%nat. pd_ro HS 529%nat.
assert (HEI : img_env VAL A_LIM (d_env cx E (pd_vals regs h))).
{ pose proof HdE as (_ & _ & HEI0 & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HEI0 a Ha). }
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS). pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + 0x710)) with (Z_to_bv 64 (BASE + 0x710)).
paj_run_shc RUNP RUNC HS HJ.
{ apply pd_awr_ro. vm_compute. reflexivity. }
set (Ed := d_env cx E (pd_vals regs h)) in *.
assert (Hmeq : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) m a).
{ lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    exact (pd_frame_all Ex rs (w_H W) m (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) end. }
clear HF HFr HG.
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 23; 24; 27]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r HS). rewrite (HROK r).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
assert (R1 : getr (ms_regs ms) 1%bv = Z_to_bv 64 (BASE + 1816)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  exact (codeptr_val _ 1816 HEI). }
assert (Ed516 : ew Ed 516 = Z_to_bv 64 (d_FB cx)).
{ subst Ed. unfold d_env. rewrite ew_havoc_old by (cbv; lia). pose proof HdE as (_ & _ & _ & _ & E516 & _). exact E516. }
assert (R10 : getr (ms_regs ms) 10%bv = w64 (d_obj cx OG)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  cbn [sv_denot]. rewrite Ed516. unfold w64, d_obj, dobj_off. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Hsp : spZ (ms_regs ms) = d_A cx).
{ unfold spZ. rewrite (RG 2%bv ltac:(cbv; tauto)). exact (proj1 HrB). }
assert (HCm : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly S W (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HCm) as (_ & _ & _ & _ & _ & _ & _ & _ & HFpresm & _ & _ & HARm & _ & _ & _).
pose proof (pd_shm cx W m (ms_mem ms) Hfr HSHrange Hmeq) as Hshm.
pmkst HS. rewrite pa_sigma_reac_disco_gate_init.
eapply SRr_bind.
{ eapply (TGINIT fq LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly S W (ms_mem ms) _ k (ms_regs ms) (d_obj cx OG) HJ).
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite R1. apply pd_ra4096. lia.
  - rewrite (RG 3%bv ltac:(cbv; tauto)). exact (proj1 (proj2 HrB)).
  - rewrite (RG 4%bv ltac:(cbv; tauto)). exact (proj1 (proj2 (proj2 HrB))).
  - exact R10.
  - rewrite Hsp. lia.
  - rewrite Hsp. unfold LLVMF_STK, ReacDiscoGateInit.REAC_DISCO_GATE_INIT_STK, ESTACK. lia.
  - rewrite Hsp. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - right. rewrite Hsp. unfold d_obj, dobj_off, ReacDiscoGateInit.REAC_DISCO_GATE_INIT_STK, ESTACK, LLVMF_STK in *. lia.
  - intros a Ha. unfold d_obj, dobj_off in Ha. split.
    + right. right. right. exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite EFB3. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
    + apply HFpresm. lia.
  - unfold d_obj, dobj_off. apply (amem_range_sub_app (d_FB cx) 4096); [exact HFBapp | lia | lia | lia | lia].
  - unfold d_obj. cbn [dobj_off].
    apply (pd_ra_range cx dsh_loop W (ms_mem ms) 2624 264 Hshm); [lia | lia | lia | unfold DFRAME_SH; lia | exact pd_saddr_G].
  - apply (shadow_hull_vis_of_frame SEGS B LAWS ly S W (ms_mem ms) _ DFRAME_CLASS (c_fpos cx) _ 264 HARm Hin3);
      rewrite ?EFB3; unfold d_obj, dobj_off; change (fs_frame_bytes DFRAME_CLASS) with 4096; lia. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJ2 & HP2 & Hra2 & Hr10x & Hfrs2 & Hperm2 & HK & HGT & HTok).
apply SRr_ret.
rewrite Hsp in HK.
destruct (pd_post cx h ly S W regs m md k (ms_regs ms) (ms_mem ms) ly2 S2 W2 regs2 mem2 md2 2624 264
  (conj HC (conj Hk (conj HrC3 (conj Hfr (conj Hbl (conj H184 Hour)))))) Hmeq RG HJ2 HP2 Hfrs2 Hperm2
  (pd_kept_G B ly S W (ms_mem ms) W2 mem2 (d_A cx) (d_obj cx OG) HK) ltac:(lia) ltac:(lia)) as (HI2 & Kf).
exists ly2, S2, regs2, mem2, md2.
split; [rewrite Hc2, R1; reflexivity|].
split; [exact HI2|]. split.
- intros a Ha Hn. exact (Kf a Ha Hn).
- exists (repeat (CtrlParsed.zb 0) 264). split; [apply repeat_length|]. split; [exact HGT | exact HTok].
Qed.
Lemma pd_stepL : forall (fq : YK11.FPState) cx h ly S (W : world SEGS) regs m md k,
  pd_I cx h ly S W regs m md k ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + 0x718) regs m md)
    (fun W' c' => exists ly' S' regs' m' md',
       c' = cfg_at (fx := fq) SEGS (BASE + 0x720) regs' m' md' /\
       pd_I cx h ly' S' W' regs' m' md' k /\
       (forall a, d_FB cx <= a < d_FB cx + 4096 -> ~ (d_obj cx OLOCK <= a < d_obj cx OLOCK + 12) ->
          aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) /\
       pd_objL cx W' m').
Proof.
intros fq cx h ly S W regs m md k (HC & Hk & HrC3 & Hfr & Hbl & H184 & Hour).
pose proof HC as (Hbase & HJ & Hfrs).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC) as (HSmod & HSlo & HShi & HFB1 & HFB2 & HFBapp & HFBimg & HFBmod & HFpres & HSHpres & HWpres & HAR3 & Hin3 & EFB3 & EFL3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HAmod).
pose proof HrC3 as (HrB & H18 & H24 & H23).
assert (HAr2 : d_S cx - 607 <= d_A cx <= d_S cx - 576) by (unfold MFRAME in HAr; lia).
assert (HArange : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in *; lia).
assert (HFBrange : 0 <= d_FB cx < 2 ^ 64) by lia.
pose proof (shadow_addr_bounds (d_FB cx) ltac:(unfold kHighMemEnd in *; lia)) as HSHb.
assert (HSHrange : 0 <= shadow_addr (d_FB cx) < 2 ^ 64) by (unfold kLowMemEnd, kHighShadowEnd in *; lia).
pose proof Hfr as (E & HdE & HRG & HFL).
pose proof (pd_regs_ok cx E regs h B HdE HrB HArange HSHrange) as HROK.
pose proof (p_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_loop ps_C3 ly S W regs m md k E 0x718 pd_sr (pd_vals regs h) [] [] [] (d_facts [] []) HC HdE HRG HFL HROK
  (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly S W m md k E (pd_vals regs h) [] [] HC HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_p in HS.
pd_ro HS 60%nat. pd_ro HS 516%nat. pd_ro HS 529%nat.
assert (HEI : img_env VAL A_LIM (d_env cx E (pd_vals regs h))).
{ pose proof HdE as (_ & _ & HEI0 & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HEI0 a Ha). }
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS). pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + 0x718)) with (Z_to_bv 64 (BASE + 0x718)).
paj_run_shc RUNP RUNC HS HJ.
{ apply pd_awr_ro. vm_compute. reflexivity. }
set (Ed := d_env cx E (pd_vals regs h)) in *.
assert (Hmeq : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) m a).
{ lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    exact (pd_frame_all Ex rs (w_H W) m (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) end. }
clear HF HFr HG.
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 23; 24; 27]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r HS). rewrite (HROK r).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
assert (R1 : getr (ms_regs ms) 1%bv = Z_to_bv 64 (BASE + 1824)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  exact (codeptr_val _ 1824 HEI). }
assert (Ed516 : ew Ed 516 = Z_to_bv 64 (d_FB cx)).
{ subst Ed. unfold d_env. rewrite ew_havoc_old by (cbv; lia). pose proof HdE as (_ & _ & _ & _ & E516 & _). exact E516. }
assert (R10 : getr (ms_regs ms) 10%bv = w64 (d_obj cx OLOCK)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  cbn [sv_denot]. rewrite Ed516. unfold w64, d_obj, dobj_off. rewrite unsigned_lit_small by lia. reflexivity. }
assert (Hsp : spZ (ms_regs ms) = d_A cx).
{ unfold spZ. rewrite (RG 2%bv ltac:(cbv; tauto)). exact (proj1 HrB). }
assert (HCm : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly S W (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HCm) as (_ & _ & _ & _ & _ & _ & _ & _ & HFpresm & _ & _ & HARm & _ & _ & _).
pose proof (pd_shm cx W m (ms_mem ms) Hfr HSHrange Hmeq) as Hshm.
pmkst HS. rewrite pa_sigma_reac_disco_peer_lock_init.
eapply SRr_bind.
{ eapply (TLINIT fq LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly S W (ms_mem ms) _ k (ms_regs ms) (d_obj cx OLOCK) HJ).
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite R1. apply pd_ra4096. lia.
  - rewrite (RG 3%bv ltac:(cbv; tauto)). exact (proj1 (proj2 HrB)).
  - rewrite (RG 4%bv ltac:(cbv; tauto)). exact (proj1 (proj2 (proj2 HrB))).
  - exact R10.
  - rewrite Hsp. lia.
  - rewrite Hsp. unfold LLVMF_STK, ReacDiscoPeerLockInit.REAC_DISCO_PEER_LOCK_INIT_STK, ESTACK. lia.
  - rewrite Hsp. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - unfold d_obj, dobj_off. lia.
  - right. rewrite Hsp. unfold d_obj, dobj_off, ReacDiscoPeerLockInit.REAC_DISCO_PEER_LOCK_INIT_STK, ESTACK, LLVMF_STK in *. lia.
  - intros a Ha. unfold d_obj, dobj_off in Ha. split.
    + right. right. right. exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite EFB3. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
    + apply HFpresm. lia.
  - unfold d_obj, dobj_off. apply (amem_range_sub_app (d_FB cx) 4096); [exact HFBapp | lia | lia | lia | lia].
  - unfold d_obj. cbn [dobj_off].
    apply (pd_ra_range cx dsh_loop W (ms_mem ms) 2960 12 Hshm); [lia | lia | lia | unfold DFRAME_SH; lia | exact pd_saddr_L].
  - apply (shadow_hull_vis_of_frame SEGS B LAWS ly S W (ms_mem ms) _ DFRAME_CLASS (c_fpos cx) _ 12 HARm Hin3);
      rewrite ?EFB3; unfold d_obj, dobj_off; change (fs_frame_bytes DFRAME_CLASS) with 4096; lia. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJ2 & HP2 & Hra2 & Hr10x & Hfrs2 & Hperm2 & HK & HGT & HTok).
apply SRr_ret.
rewrite Hsp in HK.
destruct (pd_post cx h ly S W regs m md k (ms_regs ms) (ms_mem ms) ly2 S2 W2 regs2 mem2 md2 2960 12
  (conj HC (conj Hk (conj HrC3 (conj Hfr (conj Hbl (conj H184 Hour)))))) Hmeq RG HJ2 HP2 Hfrs2 Hperm2
  (pd_kept_L B ly S W (ms_mem ms) W2 mem2 (d_A cx) (d_obj cx OLOCK) HK) ltac:(lia) ltac:(lia)) as (HI2 & Kf).
exists ly2, S2, regs2, mem2, md2.
split; [rewrite Hc2, R1; reflexivity|].
split; [exact HI2|]. split.
- intros a Ha Hn. exact (Kf a Ha Hn).
- exists (repeat (CtrlParsed.zb 0) 12). split; [apply repeat_length|]. split; [exact HGT | exact HTok].
Qed.
Lemma pd_objT_tr : forall (cx : dcx) (W : world SEGS) m (W2 : world SEGS) m2,
  pd_objT cx W m ->
  (forall a, d_FB cx <= a < d_FB cx + 4096 -> ~ (d_obj cx OG <= a < d_obj cx OG + 264) ->
     aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) m a) -> pd_objT cx W2 m2.
Proof.
intros cx W m W2 m2 (X & HX & HG & HOK) HK. exists X. split; [exact HX|]. split; [|exact HOK].
apply (garr8_aview_kept SEGS (w_H W) (w_H W2) m m2); [|exact HG].
rewrite length_map. intros a Ha. rewrite HX in Ha. cbn [Z.of_nat] in Ha. unfold d_obj, dobj_off in *. apply HK; lia.
Qed.

Lemma pd_objT_trL : forall (cx : dcx) (W : world SEGS) m (W2 : world SEGS) m2,
  pd_objT cx W m ->
  (forall a, d_FB cx <= a < d_FB cx + 4096 -> ~ (d_obj cx OLOCK <= a < d_obj cx OLOCK + 12) ->
     aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) m a) -> pd_objT cx W2 m2.
Proof.
intros cx W m W2 m2 (X & HX & HG & HOK) HK. exists X. split; [exact HX|]. split; [|exact HOK].
apply (garr8_aview_kept SEGS (w_H W) (w_H W2) m m2); [|exact HG].
rewrite length_map. intros a Ha. rewrite HX in Ha. cbn [Z.of_nat] in Ha. unfold d_obj, dobj_off in *. apply HK; lia.
Qed.

Lemma pd_objG_trL : forall (cx : dcx) (W : world SEGS) m (W2 : world SEGS) m2,
  pd_objG cx W m ->
  (forall a, d_FB cx <= a < d_FB cx + 4096 -> ~ (d_obj cx OLOCK <= a < d_obj cx OLOCK + 12) ->
     aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) m a) -> pd_objG cx W2 m2.
Proof.
intros cx W m W2 m2 (X & HX & HG & HOK) HK. exists X. split; [exact HX|]. split; [|exact HOK].
apply (garr8_aview_kept SEGS (w_H W) (w_H W2) m m2); [|exact HG].
rewrite length_map. intros a Ha. rewrite HX in Ha. cbn [Z.of_nat] in Ha. unfold d_obj, dobj_off in *. apply HK; lia.
Qed.

Theorem pb_proD1 : pd_seg1 B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold pd_seg1. intros cx h W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HF0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hcan & HrC4 & Hfr & Hbl & H184 & Hour).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
assert (HI : pd_I cx h ly3 S3 W regs mem3 md3 k)
  by (split; [exact HC | split; [unfold EV_PRO in *; lia | split; [exact (proj1 HrC4) |
      split; [exact Hfr | split; [exact Hbl | split; [exact H184 | exact Hour]]]]]]).
eapply SRr_bind; [exact (pd_stepT fq cx h ly3 S3 W regs mem3 md3 k HI)|].
cbv beta. intros W1 c1 _ (ly1 & S1 & regs1 & mem1 & md1 & -> & HI1 & K1 & HT1).
eapply SRr_bind; [exact (pd_stepG fq cx h ly1 S1 W1 regs1 mem1 md1 k HI1)|].
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HI2 & K2 & HG2).
eapply SRr_bind; [exact (pd_stepL fq cx h ly2 S2 W2 regs2 mem2 md2 k HI2)|].
cbv beta. intros W3 c3 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HI3 & K3 & HL3).
apply SRr_ret.
destruct HI3 as (HC3 & Hk3 & HrC3' & Hfr3 & Hbl3 & H184' & Hour3).
destruct HC3 as (Hbase3 & HJ3 & Hfrs3).
unfold pd_K1, pd_at, d_at.
exists fq, ly4, S4, regs4, mem4, md4, k, acc.
split; [reflexivity|]. split; [exact HF0|].
split; [exact Hbase3|]. split; [exact HJ3|]. split; [exact Hfrs3|].
split; [exact Hk3|].
split; [pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _); unfold EV_PRO in *; lia|].
split; [rewrite MT_TRIV; exact I|].
split; [exact Hacc|].
split; [exact Hcan|]. split; [exact HrC3'|]. split; [exact I|]. split; [exact Hfr3|]. split; [exact Hbl3|]. split; [exact H184'|].
split; [exact Hour3|].
split; [exact (pd_objT_trL cx W2 mem2 W3 mem4 (pd_objT_tr cx W1 mem1 W2 mem2 HT1 K2) K3)|].
split; [exact (pd_objG_trL cx W2 mem2 W3 mem4 HG2 K3)|].
exact HL3.
Qed.
End h.
End f.
End d.
