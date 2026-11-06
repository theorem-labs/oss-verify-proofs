(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 358 of its 394 lines of code are new or changed and 1242 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame YC81.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC4b YC45 YC1i DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_hunt_observe.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntRecLib DiscoEntRecCut DiscoEntRec2Kit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma e3_want : forall R, 0 <= rec_want R < 65536.
Proof.
intros R. unfold rec_want, rdb.
pose proof (u8_range (nth 0%nat R (Z_to_bv 8 0))). pose proof (u8_range (nth 1%nat R (Z_to_bv 8 0))). lia.
Qed.

Ltac e3_ro HS n :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.

Ltac e3_win USH :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros b wlo whi a Hin Ha; vm_compute in Hin;
  change (fs_frame_bytes DFRAME_CLASS / 8) with 512;
  repeat (destruct Hin as [Hin|Hin];
    [ injection Hin; intros; subst; cbn [base_val] in Ha; first [ lia | rewrite USH in Ha; lia ] | ]);
  destruct Hin.

Ltac e3_awr cx USH EFB3 :=
  cbn [ss_mem];
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat (shadow_addr (d_FB cx)));
      [ reflexivity | exact USH
      | let a := fresh "a" in let Ha := fresh "Ha" in
        intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right;
        exists DFRAME_CLASS, (c_fpos cx); split; [left; reflexivity|]; right;
        unfold in_zr; cbn [fst snd]; rewrite EFB3; change (fs_frame_bytes DFRAME_CLASS / 8) with 512; lia
      | ] ].

Ltac e3_upd USH :=
  lazymatch goal with
  | HFr : frame_of ?Eo ?rs (mrestrict ?Hh ?m1) (mrestrict _ ?m2),
    MEQ : forall a, _ -> ~ (?lo <= a < ?hi) -> aview _ _ ?m1 a = aview _ _ ?m0 a |- _ =>
    let MEQ2 := fresh "MEQ" in
    pose proof (rl_meq_frame Eo rs Hh m0 m1 m2 lo hi HFr ltac:(e3_win USH) MEQ) as MEQ2; clear MEQ; rename MEQ2 into MEQ
  end;
  lazymatch goal with
  | HG : mem_grows (mrestrict ?Hh ?m1) (mrestrict _ ?m2), MPR : forall a, apresent _ ?m0 a -> apresent _ ?m1 a |- _ =>
    let MPR2 := fresh "MPR" in pose proof (rl_pres_grow Hh m0 m1 m2 HG MPR) as MPR2; clear MPR; rename MPR2 into MPR
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Ltac e3_run RUNTOP stop cx USH EFB3 :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict (w_H _) _), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    paj_run_to_shc RUNTOP HS HJ stop; [ e3_awr cx USH EFB3 | e3_upd USH ] end.

Ltac e3_br RUNP BR := lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ => psrr_branch_pi RUNP BR HS end.

Ltac e3_rg HRO regs :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ss (restrict (w_H ?W) ?ms) |- _ =>
    assert (RG : forall r r0 : bv 5, sr_get (ss_regs ss) r = sr_get r2_sr r0 -> getr (ms_regs ms) r = getr regs r0)
      by (let r := fresh "r" in let r0 := fresh "r0" in let Heq := fresh "Heq" in
          intros r r0 Heq; rewrite (st_ok_pi_restrict_reg (w_H W) Ec ss ms r HS), Heq; symmetry; exact (HRO r0))
  end.

Ltac e3_cv E550 E555 Hn :=
  lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ =>
    rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U in Hc;
    rewrite ?(U_atom _ 550 _ E550), ?(U_atom _ 555 _ E555), ?U_lit in Hc by lia;
    repeat match type of Hc with
      | negb _ = true => apply negb_true_iff in Hc
      | negb _ = false => apply negb_false_iff in Hc
      end;
    first [ apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc | apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc ];
    rename Hc into Hn
  end.

Ltac e3_same := lazymatch goal with RG : forall r r0 : bv 5, _ -> _ |- getr _ ?r = _ =>
  rewrite (RG r r ltac:(vm_compute; reflexivity)); assumption end.

Ltac e3_reg r :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ss (restrict (w_H ?W) ?ms) |- getr (ms_regs ?ms) r = _ =>
    rewrite (st_ok_pi_restrict_reg (w_H W) Ec ss ms r HS);
    let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
  end.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBRT : d_body_rt_stmt B.

Lemma e3_Aout : forall cx ly3 S3 W mem md k a,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem md k -> d_A cx <= a < d_A cx + 472 ->
  ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + fs_frame_bytes DFRAME_CLASS / 8).
Proof.
intros cx ly3 S3 W mem md k a HC Ha Hs.
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem md k HC) as (_ & HSlo & HShi & HFB0 & HFB1 & _).
pose proof alloc_ceiling_val as Hac. unfold LLVMF_STK in HSlo.
assert (HSr : 0 <= d_S cx - MFRAME) by (unfold MFRAME; lia).
destruct (d_A_range cx HSr) as (HAr & _). unfold MFRAME in HAr.
unfold shadow_addr, SHADOW_OFF in Hs. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Hs. lia.
Qed.

Lemma e3_vmA : forall cx ly3 S3 W mem md k m m' off v,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem md k -> 0 <= off -> off + 8 <= 472 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + fs_frame_bytes DFRAME_CLASS / 8) ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  val_mem SEGS (rd W m) (d_A cx + off) 8 v -> val_mem SEGS (rd W m') (d_A cx + off) 8 v.
Proof.
intros cx ly3 S3 W mem md k m m' off v HC Ho1 Ho2 HK HV.
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem md k HC) as (_ & HSlo & HShi & _).
pose proof alloc_ceiling_val as Hac. unfold LLVMF_STK in HSlo.
assert (HSr : 0 <= d_S cx - MFRAME) by (unfold MFRAME; lia).
destruct (d_A_range cx HSr) as (HAr & _). unfold MFRAME in HAr.
apply (r2_val_mem_keep W m m' _ _ (d_A cx + off) 8 v HK); [lia | change (Z.of_nat 8) with 8; lia | | exact HV].
intros x Hx. apply (e3_Aout cx ly3 S3 W mem md k x HC). change (Z.of_nat 8) with 8 in Hx. lia.
Qed.

Lemma e3_garr8 : forall cx ly3 S3 W mem md k m m' p q l,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem md k ->
  in_app p q -> Z.of_nat (length l) <= q ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + fs_frame_bytes DFRAME_CLASS / 8) ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  garr8 SEGS (rd W m) p l -> garr8 SEGS (rd W m') p l.
Proof.
intros cx ly3 S3 W mem md k m m' p q l HC Hpq Hl HK HG.
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem md k HC) as (_ & _ & _ & HFB0 & HFB1 & _).
pose proof alloc_ceiling_val as Hac.
pose proof Hpq as Hpq'. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpq'.
apply (r2_garr8_keep W m m' _ _ p l HK); [lia | lia | | exact HG].
intros x Hx Hs. apply (fshadow_not_app (d_FB cx) 512 p q x); [lia | lia | exact Hpq | | lia].
unfold shadow_addr, SHADOW_OFF in Hs. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Hs. lia.
Qed.

Lemma e3_rd : forall cx h n xb shf ly3 S3 W m1 m2 md k a,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W m1 md k ->
  d_body B cx h n xb shf ly3 S3 W m2 ->
  shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + fs_frame_bytes DFRAME_CLASS / 8 ->
  ~ d_rdset B cx h a.
Proof.
intros cx h n xb shf ly3 S3 W m1 m2 md k a HC Hb Ha Hrd.
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m1 md k HC)
  as (_ & _ & _ & HFB0 & HFB1 & HFBapp & _ & _ & _ & _ & _ & HAR3 & _).
pose proof alloc_ceiling_val as Hac.
pose proof Hb as (T & G & Lk & H & _ & _ & _ & (Hperm & _) & _ & _ & _ & _ & (_ & _ & Hcimg) & _).
pose proof HC as (((_ & _ & _ & _ & Hpn & _) & _) & _).
unfold shadow_addr, SHADOW_OFF in Ha. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha.
assert (Hno : forall p q, in_app p q -> p <= a < p + q -> False).
{ intros p q Hpq Hpa. apply (fshadow_not_app (d_FB cx) 512 p q a); [lia | lia | exact Hpq | lia | exact Hpa]. }
assert (Himg : ~ in_img SEGS a).
{ intros Hi. pose proof (pa_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. lia. }
assert (Hblk : forall p q, In (p, q) (ablocks B ly3 S3) -> p <= a < p + req_size q -> False).
{ intros p q Hin Hpa. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin) as (_ & _ & _ & Hpapp & _).
  exact (Hno p _ Hpapp Hpa). }
unfold d_rdset in Hrd.
destruct Hrd as [Ho | [Ho | [Ho | [Ho | [Hh | [(Hn0 & Hp) | [(Hro & _ & _) | Hcan]]]]]]].
1-4: unfold d_objr, d_obj in Ho; cbn [dobj_off dobj_size] in Ho; apply (Hno (d_FB cx) 4096 HFBapp); lia.
- apply (Hblk h HUNT_SIZE).
  + apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity.
  + change (req_size HUNT_SIZE) with HUNT_SIZE. exact Hh.
- destruct Hpn as [(Hn' & _) | (_ & Hin0)]; [lia|].
  apply (Hblk (c_p cx) (c_n cx)).
  + apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. right. exact Hin0.
  + unfold req_size. destruct (Z.eqb_spec (c_n cx) 0); lia.
- apply Himg. destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; assumption | exact (pa_relro_img a Hr)].
- exact (Himg (Hcimg a Hcan)).
Qed.

Lemma e3_rL : forall cx (regs regs' : bvmap 5 word), d_rL B cx regs ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 -> getr regs' 8 = getr regs 8 ->
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 20 = getr regs 20 ->
  getr regs' 25 = getr regs 25 -> d_rL B cx regs'.
Proof.
intros cx regs regs' (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25) E2 E3 E4 E8 E9 E18 E20 E25.
unfold d_rL. rewrite E3, E4, E8, E9, E18, E20, E25.
split; [unfold spZ; rewrite E2; exact Hsp|]. repeat split; assumption.
Qed.

Lemma e3_land : forall (fq : YK11.FPState) cx pc h i n now fr R X W ly3 S3 mem3 md k acc E ss ms,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD i + 1 -> st_nev S3 <= st_nev (c_S cx) + (EV_HEAD i + 1) ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i + mo_malloc MT REC_MAX ->
  0 <= i < MAX_OPS -> 0 <= n -> 0 <= now < 2 ^ 64 -> 4096 <= fr ->
  d_body B cx h n [(fr, r2_len cx n)] dsh_loop ly3 S3 W mem3 ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
  d_E cx E -> ew E AT_FL = r2_flag cx -> d_land_chk dsh_rec (ss_mem ss) = true ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + fs_frame_bytes DFRAME_CLASS / 8) ->
     aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a) ->
  (forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms) a) ->
  d_rL B cx (ms_regs ms) -> R (ms_regs ms) -> X W (ms_mem ms) -> d_sp0 cx i now W (ms_mem ms) ->
  d_arm_at_pf B MT XM_LIB RLO RHI tfib_K cx pc h i n now (dxb fr (r2_len cx n)) dsh_rec R X W (mkCfg ms md).
Proof.
intros fq cx pc h i n now fr R X W ly3 S3 mem3 md k acc E ss ms
  HFRM0 Hbase HJ Hfrs Hk Hnev Hmo Hacc Hi Hn Hnow Hfr Hb HS Hrv Hpc HE HFL Hchk HK HP HL HR HX Hsp0.
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md k) by exact (conj Hbase (conj HJ Hfrs)).
pose proof Hb as (T & G & Lk & H & (E0 & _ & _ & _ & H216 & H152) & _).
destruct (r2_land_win B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md k mem3 _ _ h HC HK
  (fun a Ha => e3_Aout cx ly3 S3 W (ms_mem ms) md k a HC ltac:(lia)) H216 H152) as (H216' & H152').
destruct (DLAND LAWS FFL fq cx h dsh_rec ly3 S3 W md k E ss ms HC HE HFL HS Hchk H216' H152') as (Hfr' & Hsh').
unfold d_arm_at_pf, d_at.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md, k, acc.
split.
{ unfold cfg_at. pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv) as Hms.
  rewrite Hpc in Hms. rewrite Hms at 1. reflexivity. }
refine (conj HFRM0 (conj Hbase (conj HJ (conj Hfrs (conj Hk (conj Hnev (conj Hmo (conj Hacc _)))))))).
refine (conj Hi (conj Hn (conj Hnow (conj HL (conj HR (conj HX (conj Hsp0 _))))))).
unfold dxb. rewrite (proj2 (Z.eqb_neq fr 0) ltac:(lia)).
exact (DBRT cx h n n [(fr, r2_len cx n)] dsh_loop dsh_rec ly3 S3 W mem3 (ms_mem ms) (d_S cx) (d_S cx)
  (fun a => shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + fs_frame_bytes DFRAME_CLASS / 8) Hb
  ltac:(unfold LLVMF_STK; lia) ltac:(lia)
  (fun a Ha => or_intror (e3_rd cx h n _ dsh_loop ly3 S3 W (ms_mem ms) mem3 md k a HC Hb Ha))
  HK (fun a _ Ha => HP a Ha) Hfr' Hsh' ltac:(lia)).
Qed.

Theorem r2_e3 : r2_e3_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op fr W c Hq.
destruct Hq as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hi & Hn & Hnow & HrL & (H27 & H24 & H23 & H19 & H22 & H26) & (Hfr4 & (Hop & Hop3) & (M408 & M248 & M392) & HFR) &
  Hsp0 & Hbody).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj Hbase (conj HJ Hfrs)).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC)
  as (HSmod & HSlo & HShi & HFB0 & HFB1 & HFBapp & HFBimg & HFBmod & HFpres & HSHpres & HWpres & HAR3 & Hin3 & EFB3 & EFL3).
pose proof alloc_ceiling_val as Hac.
pose proof Hbody as (T & G & Lk & H & Hfrm & Hsh & Hobj & Hbl & Hinp & Himg & Hoff & Hgeo & Hcan & Hstk & Hwr).
pose proof Hfrm as (E0 & HE0 & HR0 & HF0 & H216 & H152).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). unfold HUNT_SIZE in G4.
pose proof Hinp as (Hnr & HGinp & HOIp).
pose proof Hbl as (Hperm & _ & _ & _).
assert (HinF : In (fr, r2_len cx n) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 HinF) as (Hf16 & Hf4k & Hfc & Hfapp & _).
pose proof (e3_want (rest_of (c_pl cx) n)) as Hwant.
assert (Hlen : 0 <= r2_len cx n <= REC_MAX /\ r2_len cx n <= rec_rem n /\ 0 <= rec_rem n <= n).
{ unfold r2_len, rec_len, rec_rem, rec_take, REC_MAX. lia. }
assert (Hreq : r2_len cx n <= req_size (r2_len cx n)) by (unfold req_size; destruct (Z.eqb_spec (r2_len cx n) 0); lia).
assert (KX : forall m', (forall a, 0 <= a < 2 ^ 64 ->
    ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + fs_frame_bytes DFRAME_CLASS / 8) ->
    aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem3 a) ->
  val_mem SEGS (rd W m') (d_A cx + 408) 8 op /\ val_mem SEGS (rd W m') (d_A cx + 248) 8 (d_cur cx (rec_rem n)) /\
  val_mem SEGS (rd W m') (d_A cx + 392) 8 (r2_sx op) /\ d_sp0 cx i now W m' /\
  garr8 SEGS (rd W m') fr
    (map (fun b : byte => bv_unsigned b) (firstn (Z.to_nat (r2_len cx n)) (rest_of (c_pl cx) (rec_rem n))))).
{ intros m' HK. destruct Hsp0 as (S232 & S344).
  split; [exact (e3_vmA cx ly3 S3 W mem3 md3 k mem3 m' 408 op HC ltac:(lia) ltac:(lia) HK M408)|].
  split; [exact (e3_vmA cx ly3 S3 W mem3 md3 k mem3 m' 248 _ HC ltac:(lia) ltac:(lia) HK M248)|].
  split; [exact (e3_vmA cx ly3 S3 W mem3 md3 k mem3 m' 392 _ HC ltac:(lia) ltac:(lia) HK M392)|].
  split; [split; [exact (e3_vmA cx ly3 S3 W mem3 md3 k mem3 m' 232 _ HC ltac:(lia) ltac:(lia) HK S232)
                 | exact (e3_vmA cx ly3 S3 W mem3 md3 k mem3 m' 344 _ HC ltac:(lia) ltac:(lia) HK S344)]|].
  apply (e3_garr8 cx ly3 S3 W mem3 md3 k mem3 m' fr (req_size (r2_len cx n)) _ HC Hfapp); [|exact HK | exact HFR].
  rewrite length_map, length_firstn. lia. }
assert (CH : forall E, d_E cx E -> YP09.chunk_ok SEGS (d_env cx E (r2_vals regs [w64 h])) (rd W mem3) (d_A cx)
  (YP09.mkChunk 216 (CVal 8 (SOff (AT_X + 32) 0)))).
{ intros E1 _. apply (chunk_ok_val SEGS _ _ (d_A cx) 216 8 _ h); [| lia | lia | exact H216].
  rewrite sv_denot_SOff0, (r2_env_ex cx E1 regs [w64 h] 0 (AT_X + 32) eq_refl ltac:(cbn; lia)). reflexivity. }
destruct (r2_seat B MT XM_LIB RLO RHI tfib_K LAWS TL DSEAT DFACTS fq cx RA_CPY h n [(fr, r2_len cx n)] dsh_loop
  ly3 S3 W regs mem3 md3 k [w64 h] [YP09.mkChunk 216 (CVal 8 (SOff (AT_X + 32) 0))] [] [] [] [] HC HrL Hbody
  (fun E HE => conj I (conj I (conj (Forall_cons _ _ _ (CH E HE) (Forall_nil _))
    (conj (Forall_nil _) (conj (Forall_nil _) (conj I (Forall_nil _)))))))
  ltac:(vm_compute; reflexivity)) as (E & HdE & HS).
pose proof (r2_regs_ok B cx E regs [w64 h] HdE HrL) as HRO.
pose proof (r2_env_img cx E (r2_vals regs [w64 h]) HdE) as HEI.
pose proof (d_E_env cx E (r2_vals regs [w64 h]) HdE) as HdE'.
pose proof HdE as (_ & _ & _ & _ & _ & ESH).
assert (USH : bv_unsigned (ew (d_env cx E (r2_vals regs [w64 h])) 529) = shadow_addr (d_FB cx)).
{ rewrite d_env_old by (unfold AT_FL; lia). change 529%nat with AT_SH. rewrite ESH. unfold w64.
  apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia. }
assert (E550 : ew (d_env cx E (r2_vals regs [w64 h])) 550 = Z_to_bv 64 (op mod 4))
  by (rewrite (r2_env_reg cx E regs [w64 h] 19%bv 550 eq_refl); exact H19).
assert (E555 : ew (d_env cx E (r2_vals regs [w64 h])) 555 = Z_to_bv 64 (r2_len cx n))
  by (rewrite (r2_env_reg cx E regs [w64 h] 24%bv 555 eq_refl); exact H24).
assert (E557 : ew (d_env cx E (r2_vals regs [w64 h])) 557 = w64 (d_obj cx OOUR))
  by (rewrite (r2_env_reg cx E regs [w64 h] 26%bv 557 eq_refl); exact H26).
assert (E558 : ew (d_env cx E (r2_vals regs [w64 h])) 558 = w64 fr)
  by (rewrite (r2_env_reg cx E regs [w64 h] 27%bv 558 eq_refl); exact H27).
assert (E563 : ew (d_env cx E (r2_vals regs [w64 h])) 563 = w64 h)
  by exact (r2_env_ex cx E regs [w64 h] 0 563 eq_refl ltac:(cbn; lia)).
assert (HlenB : 0 <= r2_len cx n < 65536) by (unfold REC_MAX in Hlen; lia).
unfold ss_d in HS.
e3_ro HS 516%nat. e3_ro HS 60%nat.
pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
assert (MEQ : forall a, 0 <= a < 2 ^ 64 ->
  ~ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + fs_frame_bytes DFRAME_CLASS / 8) ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem3 a) by (intros; reflexivity).
assert (MPR : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) mem3 a) by (intros a0 Ha0; exact Ha0).
unfold cfg_at. change (w64 (BASE + RA_CPY)) with (Z_to_bv 64 (BASE + RA_CPY)).
e3_run RUNTOP 3280 cx USH EFB3.
e3_br RUNP BR.
- e3_cv E550 E555 Hb0.
  e3_run RUNTOP 3280 cx USH EFB3.
  e3_rg HRO regs.
  destruct (KX _ MEQ) as (K408 & K248 & K392 & Ksp0 & Kfr).
  apply SRr_ret. exists (rec_rem n), fr, (r2_len cx n). split; [reflexivity|]. split; [reflexivity|].
  left. split; [lia|]. unfold cls_in. rewrite (proj2 (Z.eqb_eq (op mod 4) 0) Hb0).
  eapply (e3_land fq cx _ h i n now fr _ _ W ly3 S3 mem3 _ k acc _ _ _ HFRM0 Hbase HJ Hfrs Hk Hnev Hmo Hacc Hi Hn Hnow
    Hfr4 Hbody HS eq_refl eq_refl HdE' (d_env_fl cx E _) ltac:(vm_compute; reflexivity) MEQ MPR).
  + apply (e3_rL cx regs _ HrL); apply RG; vm_compute; reflexivity.
  + unfold dR_cls. repeat match goal with |- _ /\ _ => split end; e3_same.
  + cbv beta. split; [lia|]. split; [exact Hop|]. split.
    { unfold d_frm. split; [lia|]. split; [lia|]. split; [lia | exact Kfr]. }
    split; [exact K248|]. split; [exact K408|]. split; [exact K392|]. split; lia.
  + exact Ksp0.
- e3_cv E550 E555 Hb0.
  e3_run RUNTOP 3304 cx USH EFB3.
  e3_br RUNP BR.
  + e3_cv E550 E555 Hb1.
    e3_run RUNTOP 3304 cx USH EFB3.
    e3_rg HRO regs.
    destruct (KX _ MEQ) as (K408 & K248 & K392 & Ksp0 & Kfr).
    apply SRr_ret. exists (rec_rem n), fr, (r2_len cx n). split; [reflexivity|]. split; [reflexivity|].
    left. split; [lia|]. unfold cls_in. rewrite (proj2 (Z.eqb_neq (op mod 4) 0) Hb0).
    eapply (e3_land fq cx _ h i n now fr _ _ W ly3 S3 mem3 _ k acc _ _ _ HFRM0 Hbase HJ Hfrs Hk Hnev Hmo Hacc Hi Hn Hnow
      Hfr4 Hbody HS eq_refl eq_refl HdE' (d_env_fl cx E _) ltac:(vm_compute; reflexivity) MEQ MPR).
    * apply (e3_rL cx regs _ HrL); apply RG; vm_compute; reflexivity.
    * unfold dR_cls. repeat match goal with |- _ /\ _ => split end; e3_same.
    * cbv beta. split; [lia|]. split; [exact Hop|]. split.
      { unfold d_frm. split; [lia|]. split; [lia|]. split; [lia | exact Kfr]. }
      split; [exact K248|]. split; [exact K408|]. split; [exact K392|]. split; lia.
    * exact Ksp0.
  + e3_cv E550 E555 Hb1.
    e3_run RUNTOP 5812 cx USH EFB3.
    e3_br RUNP BR.
    * e3_cv E550 E555 Hb2.
      e3_run RUNTOP 5812 cx USH EFB3.
      e3_rg HRO regs.
      destruct (KX _ MEQ) as (K408 & K248 & K392 & Ksp0 & Kfr).
      apply SRr_ret. exists (rec_rem n), fr, (r2_len cx n). split; [reflexivity|]. split; [reflexivity|].
      right. split; [exact Hb1|]. unfold hobs_in.
      eapply (e3_land fq cx _ h i n now fr _ _ W ly3 S3 mem3 _ k acc _ _ _ HFRM0 Hbase HJ Hfrs Hk Hnev Hmo Hacc Hi Hn Hnow
        Hfr4 Hbody HS eq_refl eq_refl HdE' (d_env_fl cx E _) ltac:(vm_compute; reflexivity) MEQ MPR).
      -- apply (e3_rL cx regs _ HrL); apply RG; vm_compute; reflexivity.
      -- unfold dR_hobs. refine (conj _ (conj _ _)).
         ++ e3_reg (19%bv : bv 5). rewrite sv_denot_SOff0. exact E563.
         ++ rewrite (proj2 (Z.ltb_lt 11 (r2_len cx n)) Hb2). e3_reg (11%bv : bv 5). cbn [sv_denot]. rewrite E558.
            unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
         ++ repeat match goal with |- _ /\ _ => split end; e3_same.
      -- cbv beta. split; [exact Hb1|]. split; [exact Hop|]. split.
         { unfold d_frm. split; [lia|]. split; [lia|]. split; [lia | exact Kfr]. }
         split; [apply reac_hunt_observe.clean_le; lia|]. split; [exact K248|]. split; lia.
      -- exact Ksp0.
    * e3_cv E550 E555 Hb2.
      e3_run RUNTOP 5812 cx USH EFB3.
      e3_rg HRO regs.
      destruct (KX _ MEQ) as (K408 & K248 & K392 & Ksp0 & Kfr).
      apply SRr_ret. exists (rec_rem n), fr, (r2_len cx n). split; [reflexivity|]. split; [reflexivity|].
      right. split; [exact Hb1|]. unfold hobs_in.
      eapply (e3_land fq cx _ h i n now fr _ _ W ly3 S3 mem3 _ k acc _ _ _ HFRM0 Hbase HJ Hfrs Hk Hnev Hmo Hacc Hi Hn Hnow
        Hfr4 Hbody HS eq_refl eq_refl HdE' (d_env_fl cx E _) ltac:(vm_compute; reflexivity) MEQ MPR).
      -- apply (e3_rL cx regs _ HrL); apply RG; vm_compute; reflexivity.
      -- unfold dR_hobs. refine (conj _ (conj _ _)).
         ++ e3_reg (19%bv : bv 5). rewrite sv_denot_SOff0. exact E563.
         ++ rewrite (proj2 (Z.ltb_ge 11 (r2_len cx n)) Hb2). e3_reg (11%bv : bv 5). rewrite sv_denot_SOff0. exact E557.
         ++ repeat match goal with |- _ /\ _ => split end; e3_same.
      -- cbv beta. split; [exact Hb1|]. split; [exact Hop|]. split.
         { unfold d_frm. split; [lia|]. split; [lia|]. split; [lia | exact Kfr]. }
         split; [apply reac_hunt_observe.clean_le; lia|]. split; [exact K248|]. split; lia.
      -- exact Ksp0.
Qed.

End h.
End f.
End d.
