(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC94.v, with its module paths and module names changed; 201 of its 223 lines of code are new or changed and 227 lines of the source are left out. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgEncC CPgMainC CodecRo CodecGlobs CPgWalk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgWalkKept CPgWalkCall CPgWalkRo CPgWalkImg CPgSat.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st codec_amain_lem codec_amain_encl codec_amain_rd13l codec_amain_rd13t.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_text.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.


Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis IV : img_shadow_vis tfibsegs B.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Hypothesis RF : cpw_rows_free B CA_ROSTRS.
Hypothesis CTA : cdc_text_arg_specX tfibsegs B MT AM_text_arg.
Hypothesis CS7 : cdc_check_seg7_specX tfibsegs B MT CA_RLO CA_RHI CA_SEG7 CA_GLYPH CA_ROSTRS AM_check_seg7.
Hypothesis CTC : cdc_check_text_counter_specX tfibsegs B MT CA_RLO CA_RHI CA_SEG7 CA_GLYPH CA_ROSTRS AM_check_text_counter.
Hypothesis COC : cdc_owed_counter_text_specX tfibsegs B MT CA_RLO CA_RHI CA_GLYPH CA_ROSTRS AM_owed_counter_text.

(* the bytes of the zones the walk leaves alone: off the write windows of both runs *)
Ltac r13_zk HFr0 HFr1 B2 BF BS Fd :=
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha;
  lazymatch type of HFr1 with frame_of _ _ (mrestrict ?Hh ?m1) (mrestrict _ ?m2) =>
  lazymatch type of HFr0 with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ m1) =>
    transitivity (aview tfibsegs Hh m1 a);
    [ revert a Ha; eapply (r13_run_kept _ _ _ _ _ _ HFr1)
    | revert a Ha; eapply (r13_run_kept _ _ _ _ _ _ HFr0) ];
    let x := fresh "x" in let Hx := fresh "Hx" in
    intros x Hx; unfold r13_zone, am_keepzone in Hx; fold Fd in Hx; split; [lia|]; r13_nwr B2 BF BS end end.
(* k.p / k.desk at 0x8105c, out of the record's p / desk region (index 7 of the state) *)
Ltac r13_pd HS Fv off e v HRv Hout :=
  lazymatch type of HS with YP0l.st_ok _ ?Ev ?ssx (restrict ?Hh ?msx) =>
    let r := eval vm_compute in (nth 7 (ss_mem ssx) got_region) in
    let HR := fresh "HR" in
    pose proof (st_ok_region_nth Ev ssx (restrict Hh msx) 7 r HS ltac:(vm_compute; reflexivity)) as HR;
    pose proof (field_of_region _ _ 33 Fv _ _ _ _ _ off 8 e v HR ltac:(assumption)
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) HRv ltac:(cbn; lia) ltac:(cbn; lia)) as Hout end.

Theorem seg_rd13_holds : seg_rd13 B MT K XM_LIB.
Proof.
intros g pos sp1 ops W2 c2 H.
destruct H as (ly2 & S2 & regs2 & mem2 & md2 & kj & -> & HJ & Hfr & Hkj & HMO & HC & HP).
destruct HP as ((Hops & R26) & Hkind & c & pv & dv & od & Hcur & Hc1 & Hpd & R23 & Hkat).
replace (rd_pc 13) with 0x81038 by (vm_compute; reflexivity).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
pose proof Hkat as (KA & Kwf).
pose proof KA as (Vkind & Vp & Vdesk & Va & Vb & Vc & Vdelta & Gbytes & Vn & Vrc & Gbef & Gout & Vwrc & Gwant & Vwl & Vwk & Vwd).
cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out kz_want_rc kz_want kz_want_len
  kz_want_key kz_want_display k_rdZ] in Vkind, Vp, Vdesk, Va, Vb, Vc, Vdelta, Gbytes, Vn, Vrc, Gbef, Gout, Vwrc, Gwant, Vwl, Vwk, Vwd.
set (F := FA g pos) in *.
replace (F + 176 + 8) with (F + 184) in Vp by lia. replace (F + 176 + 16) with (F + 192) in Vdesk by lia.
replace (F + 176 + 24) with (F + 200) in Va by lia. replace (F + 176 + 28) with (F + 204) in Vb by lia.
set (ys := [dv]).
set (E := am_env g pos c regs2 ys).
assert (Hpdr : 0 <= pv < 2 ^ 64 /\ 0 <= dv < 2 ^ 64)
  by (destruct Hpd as [(-> & -> & _) | [(-> & -> & _) | (-> & -> & _)]]; unfold CA_PERS, CM_SPEC_C24, CM_SPEC_PC; lia).
assert (EF : ew E 33 = Z_to_bv 64 F) by exact (am_ew_F g pos c regs2 ys).
assert (E37 : ew E 37 = Z_to_bv 64 dv) by exact (am_ew_y g pos c regs2 ys 0).
assert (E23 : ew E 23 = Z_to_bv 64 pv) by exact (eq_trans (am_ew_reg g pos c regs2 ys 23 23%bv eq_refl) R23).
assert (HFB : base_val E (Some 33%nat) = F) by (cbn [base_val]; rewrite EF; apply unsigned_lit_small; unfold AM_HI in *; lia).
assert (Hrs : Forall (region_ok tfibsegs E (mrestrict (w_H W2) mem2)) r13_rs).
{ unfold r13_rs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
  - rewrite am_shm0_eq. exact (am_shadow_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys 54 55
      HJ Hfr HC ltac:(lia) ltac:(lia)).
  - apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys); try exact HJ; try exact Hfr;
      try exact HC; try lia.
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val tfibsegs E _ F 176 4 (SLit 13) 13); [reflexivity | zside | zside | exact Vkind].
  - apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys); try exact HJ; try exact Hfr;
      try exact HC; try lia.
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val tfibsegs E _ F 184 8 (SOff 23 0) pv);
        [cbn [sv_denot]; rewrite E23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | zside | exact Vp].
    + apply (chunk_ok_val tfibsegs E _ F 192 8 (SOff 37 0) dv);
        [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | zside | exact Vdesk].
  - apply (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ys); try exact HJ; try exact Hfr;
      try exact HC; try lia.
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val tfibsegs E _ F 204 4 (SLit 0) 0); [reflexivity | zside | zside | exact Vb]. }
assert (Hin3 : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
pose proof HJ as (HAR & _).
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 3 pos HAR Hin3) as (_ & _ & Happ).
assert (E512 : fs_frame_bytes 3 = 512) by reflexivity.
rewrite EFA, E512 in Happ. rewrite E512 in Hfceil.
assert (ESH : ew E 34 = Z_to_bv 64 (shadow_addr F)) by exact (am_ew_SH g pos c regs2 ys).
pose proof (Z.div_mod F 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8.
assert (Hfsh : F + 512 <= shadow_addr F \/ shadow_addr F + 64 <= F).
{ unfold in_app in Happ. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
  destruct Happ as (_ & [Hlow | (Hh1 & Hh2)]); [left; lia|].
  right. assert (D4 : 2199291686912 <= F / 8) by (apply Z.div_le_lower_bound; lia). lia. }
assert (Hshb : 2147450880 + 512 <= shadow_addr F <= 2147450880 + 2 ^ 44)
  by (unfold shadow_addr, SHADOW_OFF, AM_HI in *; split; [assert (512 <= F / 8) by (apply Z.div_le_lower_bound; lia); lia
      | assert (F / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia); lia]).
assert (HSB : base_val E (Some 34%nat) = shadow_addr F)
  by (cbn [base_val]; rewrite ESH; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF, AM_HI in *; lia).
assert (B2 : bv_unsigned (ew E 2) = sp1).
{ pose proof HC as (_ & _ & R2 & _). unfold E. rewrite (am_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2.
  unfold w64. apply unsigned_lit_small. unfold AM_HI in *. lia. }
assert (HB2 : base_val E (Some 2%nat) = sp1) by (cbn [base_val]; exact B2).
assert (Hpdj : pairwise_disjoint E r13_rs).
{ apply pairwise_disjoint_of_extents. unfold r13_rs, am_shadow_region, r13_kk, r13_kpd, r13_kb, am_frame_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite HFB, HSB.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold shadow_addr, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd in *. repeat split; lia. }
(* a frame byte is not a byte of the image (AR_client_img_law), so a range of the frame lies off an image range *)
assert (FAPART : forall q n lo hi, 0 < n -> (forall a, q <= a < q + n -> in_img tfibsegs a) ->
  0 <= lo -> lo < hi -> hi <= 512 -> F + hi <= q \/ q + n <= F + lo).
{ intros q n lo hi Hn0 Himg Hlo Hlh Hhi.
  destruct (Z_le_gt_dec (F + hi) q) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (q + n) (F + lo)) as [H2|H2]; [right; exact H2|].
  exfalso. set (a := Z.max q (F + lo)).
  pose proof (al_client_img _ _ LAWS ly2 S2 W2 mem2 md2 a HAR) as Hc. apply Hc; [|apply Himg; unfold a; lia].
  right. left. exists 3, pos. split; [exact Hin3|]. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA, E512.
  unfold a. lia. }
assert (IG : forall a, A_GOT_shadow <= a < A_GOT_shadow + 8 -> in_img tfibsegs a)
  by (intros a Ha; unfold A_GOT_shadow in Ha; r13_img_seg).
assert (IC : forall a, A_shadow_glob <= a < A_shadow_glob + 8 -> in_img tfibsegs a)
  by (intros a Ha; unfold A_shadow_glob in Ha; r13_img_seg).
pose proof (FAPART A_GOT_shadow 8 176 208 ltac:(lia) IG ltac:(lia) ltac:(lia) ltac:(lia)) as AG1.
pose proof (FAPART A_shadow_glob 8 176 208 ltac:(lia) IC ltac:(lia) ltac:(lia) ltac:(lia)) as AG2.
unfold A_GOT_shadow, A_shadow_glob in AG1, AG2.
assert (Hap : Forall (fun r => all_disjoint E r am_regs) r13_rs).
{ unfold r13_rs. repeat apply Forall_cons; try apply Forall_nil; apply all_disjoint_of_extents;
  unfold am_regs, am_regs0, cw_regs, am_spill_region, am_cur_region, stack_region, got_region, bcell_region,
    am_shadow_region, r13_kk, r13_kpd, r13_kb, am_frame_region, extent_of_region;
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi]; rewrite ?HFB, ?HSB, ?HB2; cbn [base_val];
  unfold A_GOT_shadow, A_shadow_glob;
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
  unfold shadow_addr, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, AM_HI in *; repeat split; lia. }
pose proof (am_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c 0x81038 ys r13_rs []
  HJ Hfr HC Hcur eq_refl Hrs Hpdj Hap I) as HS.
fold E in HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
unfold cfg_at. change (w64 0x81038) with (Z_to_bv 64 0x81038).
assert (BF : bv_unsigned (ew E 33) = F) by (cbn [base_val] in HFB; exact HFB).
assert (BS : bv_unsigned (ew E 34) = shadow_addr F) by (cbn [base_val] in HSB; exact HSB).
pose proof EFA as EFL.
set (Q := fun W3 c3 => inv_enc B MT K XM_LIB g pos sp1 ops 10 W3 c3 \/ inv_latch B MT K XM_LIB g pos sp1 ops W3 c3).
assert (CONT : forall (y1 y10 y11 y12 pv' dv' : Z) (d' : desk) ms md,
  YP0l.st_ok tfibsegs (am_env g pos c regs2 [dv; y1; y10; y11; y12]) r13_ss_mid (restrict (w_H W2) ms) ->
  ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 (ms_mem ms) md kj ->
  pd_okA pv' dv' (Some d') ->
  val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (F + 184) 8 pv' ->
  val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (F + 192) 8 dv' ->
  (forall a, r13_zone g pos sp1 a -> aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a) ->
  SRr tfibsegs W2 (mkCfg ms md) Q).
{ intros y1 y10 y11 y12 pv' dv' d' ms md H1 H2 H3 H4 H5 H6.
  eapply (r13_tail B MT K XM_LIB) with (g := g) (pos := pos) (sp1 := sp1) (ops := ops) (ly2 := ly2) (S2 := S2)
    (W2 := W2) (regs2 := regs2) (mem2 := mem2) (md2 := md2) (kj := kj) (c := c) (pv := pv) (dv := dv) (od := od)
    (y1 := y1) (y10 := y10) (y11 := y11) (y12 := y12) (pv' := pv') (dv' := dv') (d' := d') (ms := ms) (md := md);
  eassumption. }
aj_run tfibtbl_lib_ok HS HJ.
{ r13_awr. }
rename HFr into HFr0. clear HF HG.
srr_branch_sh tfibtbl_lib_ok HS.
all: lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hcond end.
all: rewrite branch_ne_U, U_lit in Hcond by lia; unfold U in Hcond;
  rewrite (am_den_off E 23%nat pv 0 E23 ltac:(lia) ltac:(lia)), Z.add_0_r, unsigned_lit_small in Hcond by lia.
- (* s7 <> 0: k.p and k.desk as they were *)
  apply negb_true_iff, Z.eqb_neq in Hcond.
  aj_run_to tfibtbl_lib_ok HS HJ 0x8105c.
  { r13_awr. }
  rename HFr into HFr1. clear HF HG.
  assert (DP : sv_denot E (SOff 23 0) = Z_to_bv 64 pv)
    by (cbn [sv_denot]; rewrite E23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  assert (DD : sv_denot E (SOff 37 0) = Z_to_bv 64 dv)
    by (cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  r13_pd HS F 184 (SOff 23 0) pv DP VP1.
  r13_pd HS F 192 (SOff 37 0) dv DD VD1.
  lazymatch type of HS with YP0l.st_ok _ _ _ (restrict _ ?msx) =>
    assert (KZ : forall a, r13_zone g pos sp1 a -> aview tfibsegs (w_H W2) (ms_mem msx) a = aview tfibsegs (w_H W2) mem2 a)
    by r13_zk HFr0 HFr1 B2 BF BS F end.
  assert (Hod : exists d', pd_okA pv dv (Some d')).
  { destruct Hpd as [(Hp0 & _ & _) | [(-> & -> & _) | (-> & -> & _)]]; [lia | exists c24 | exists pc]; unfold pd_okA; tauto. }
  destruct Hod as (d' & Hpd').
  unfold E, ys in HS. r13_join g pos c regs2 dv.
  eapply (CONT _ _ _ _ pv dv d'); [exact HS | exact HJ | exact Hpd' | exact VP1 | exact VD1 | exact KZ].
- (* s7 = 0: diginet_personality_of(1) through the library table, the two stores *)
  apply negb_false_iff, Z.eqb_eq in Hcond.
  aj_run_to tfibtbl_lib_ok HS HJ 0x8105c.
  { r13_awr. }
  rename HFr into HFr1. clear HF HG.
  assert (DP : sv_denot E (SLit 645408) = Z_to_bv 64 645408) by reflexivity.
  assert (DD : sv_denot E (SLit 644768) = Z_to_bv 64 644768) by reflexivity.
  r13_pd HS F 184 (SLit 645408) 645408 DP VP1.
  r13_pd HS F 192 (SLit 644768) 644768 DD VD1.
  lazymatch type of HS with YP0l.st_ok _ _ _ (restrict _ ?msx) =>
    assert (KZ : forall a, r13_zone g pos sp1 a -> aview tfibsegs (w_H W2) (ms_mem msx) a = aview tfibsegs (w_H W2) mem2 a)
    by r13_zk HFr0 HFr1 B2 BF BS F end.
  assert (Hpd' : pd_okA 645408 644768 (Some c24))
    by (unfold pd_okA, CA_PERS, CM_SPEC_C24; right; left; repeat split; reflexivity).
  unfold E, ys in HS. r13_join g pos c regs2 dv.
  eapply (CONT _ _ _ _ 645408 644768 c24); [exact HS | exact HJ | exact Hpd' | exact VP1 | exact VD1 | exact KZ].
Qed.
End b.
End a.
