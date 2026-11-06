(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 338 of its 373 lines of code are new or changed and 1243 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntProC.v, with its module names changed; 445 of its 504 lines of code are new or changed and 314 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop YCbp.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1i YC1g YC1h YC81 YC4b DiscoACjr ACj1 DiscoACja YC85.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import StackFreeDef StackFreeJournal.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoSites DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntRec DiscoEntExitPostPf.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition ex_vals (regs : bvmap 5 word) (h : Z) : list word :=
  [Z_to_bv 64 h; getr regs 1; getr regs 5; getr regs 6; getr regs 7;
   getr regs 10; getr regs 11; getr regs 12; getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17;
   getr regs 20; getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26; getr regs 27;
   getr regs 28; getr regs 29; getr regs 30; getr regs 31].
Definition ex_sr : list sv :=
  [SLit 0; SOff 532 0; SOff AT_A 0; SOff 3 0; SOff 4 0; SOff 533 0; SOff 534 0; SOff 535 0;
   SOff AT_STK 0; SOff AT_A 0; SOff 536 0; SOff 537 0; SOff 538 0; SOff 539 0; SOff 540 0; SOff 541 0;
   SOff 542 0; SOff 543 0; SOff 32 0; SOff 531 0; SOff 544 0; SOff 545 0; SOff 546 0; SOff 547 0;
   SOff 548 0; SOff 549 0; SOff 550 0; SOff 551 0; SOff 552 0; SOff 553 0; SOff 554 0; SOff 555 0].
Definition ex_span : Z * Z := (0, 0).

Section w. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head} {LS : lib_shape}.
Section wf.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section wh.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MT_TRIV : MT = ameter_triv.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis AFREE : forall fq : YK11.FPState, afree_realizes (fx := fq) SEGS B.
Variable SF6_ENTRY : Z.
Hypothesis de_sf6 : SIGMA DS___asan_stack_free_6 = SF6_ENTRY.
Hypothesis ASF6 : forall fq : YK11.FPState, astack_free_realizes (fx := fq) SEGS B SF6_ENTRY 6.
Hypothesis DUNIV : duniv_ok B.
Hypothesis de_ail : asink_img_laws SEGS B tfib_K.

Lemma ex_regs_ok : forall (cx : dcx) (h : Z) (regs : bvmap 5 word) (E : env),
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  d_E cx E -> d_rX B cx h regs ->
  regs_ok (d_env cx E (ex_vals regs h)) ex_sr regs.
Proof.
intros cx h regs E Hbase HdE HrX.
destruct Hbase as ((HPRE & _) & _).
destruct HPRE as (HAR & Hra & Hra4 & Hgp0 & Htp0 & Hstk & Hpres & Hch & HQT).
destruct HdE as (EE & E32 & HEI & E60 & E516 & E529).
unfold AT_A, AT_F, AT_SH in E60, E516, E529.
destruct HrX as (Hsp & Hgp & Htp & Hs0 & Hs1 & Hs2 & H19).
regs_ok_cases.
- rewrite E60. unfold spZ in Hsp. unfold w64. rewrite <- Hsp. symmetry. apply Z_to_bv_bv_unsigned.
- rewrite (EE 3%nat 3%bv eq_refl), Hgp, Hgp0. reflexivity.
- rewrite (EE 4%nat 4%bv eq_refl), Htp, Htp0. reflexivity.
- rewrite (EE 2%nat 2%bv eq_refl), Hs0. unfold w64, d_S, spZ. apply Z_to_bv_bv_unsigned.
- rewrite E60, Hs1. reflexivity.
- rewrite E32, Hs2. reflexivity.
- exact H19.
Qed.

Lemma ex_chain_alt : forall (cx : dcx) ly3 S3 (W3 : world SEGS) mem3 md3 k,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  bad_next (d_S cx) (ly_top ly3) (s0Z (c_regs cx)) = true \/
  fpchain (rdword (aview SEGS (w_H W3) mem3)) (s0Z (c_regs cx)) (ly_top ly3) [].
Proof.
intros cx ly3 S3 W3 mem3 md3 k HC.
pose proof HC as (Hbase & HJ & Hfrs).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W3 mem3 md3 k HC) as
  (HSmod & HSlo & HShi & _).
pose proof (proj1 (proj1 Hbase)) as HPRE.
destruct HPRE as (HAR & Hra & Hra4 & Hgp0 & Htp0 & Hstk & Hpres & Hch & HQT).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _).
unfold d_S in *.
destruct Hch as [[Hbad _] | (Hlo & Hhi & Hal & Hfp & _)].
- left. unfold bad_next. rewrite Etop.
  destruct Hbad as [Hb|[Hb|Hb]].
  + apply Bool.orb_true_iff. left. apply Bool.orb_true_iff. left. apply Z.leb_le. unfold LLVMF_STK in *. lia.
  + apply Bool.orb_true_iff. left. apply Bool.orb_true_iff. right. apply Z.leb_le. lia.
  + apply Bool.orb_true_iff. right. apply Bool.negb_true_iff. apply Z.eqb_neq. exact Hb.
- right. destruct Hfp as (r & Hr & Hrr). exists r. split; [|exact Hrr].
  rewrite <- Hr. unfold rdword.
  assert (K : forall i, 0 <= i < 8 ->
    aview SEGS (w_H W3) mem3 (s0Z (c_regs cx) - 8 + i) = aview SEGS (w_H (c_W cx)) (c_mem cx) (s0Z (c_regs cx) - 8 + i)).
  { intros i Hi. apply F1; unfold LLVMF_STK in *; lia. }
  assert (K0 : aview SEGS (w_H W3) mem3 (s0Z (c_regs cx) - 8) = aview SEGS (w_H (c_W cx)) (c_mem cx) (s0Z (c_regs cx) - 8))
    by (apply F1; unfold LLVMF_STK in *; lia).
  rewrite K0, (K 1), (K 2), (K 3), (K 4), (K 5), (K 6), (K 7) by lia. reflexivity.
Qed.

Theorem pb_exit : exit_spec B MT XM_LIB XN_LIB RLO RHI tfib_K.
Proof.
unfold exit_spec.
intros cx h W c Hpre.
destruct Hpre as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & Hfrm0 & Hbase & HJ3 & Hfrs3 & Hkb & Hnevb & Hmle & Haccb
 & HrX & Hbody).
pose proof HrX as (Hsp0 & Hgp0 & Htp0 & Hs00 & Hs10 & Hs20 & H19).
destruct Hbody as (Hframe & Hblocks & Himg).
destruct Hframe as (E & HdE & Hregs & Hflagw).
subst c.
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ3 | exact Hfrs3]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC) as
  (HSmod & HSlo & HShi & HFB1 & HFB2 & HFBapp & HFBimg & HFBmod & HFpres & HSHpres & HWpres & HAR3 & Hin3 & EFB3 & EFL3).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HAmod).
pose proof (ex_regs_ok cx h regs E Hbase HdE HrX) as HROK.
pose proof (d_seat_x B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx ly3 S3 W regs mem3 md3 k E EXIT_OFF ex_sr
  (ex_vals regs h) [] [] [] [] (d_facts [] []) HC HdE Hregs Hflagw HROK
  (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E (ex_vals regs h) [] [] HC HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
pose proof (paj_ret_at (fx := fq) (PL := PL_disco) (PI := PI)) as RET.
pose proof (proj1 (proj1 Hbase)) as HPRE.
pose proof HPRE as (HAR & Hra1 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HdE as (EE & E32 & HEI & E60 & E516 & E529).
unfold AT_A, AT_F, AT_SH in E60, E516, E529.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (ex_vals regs h)) (mrestrict (w_H W) mem3))
  by (apply Forall_nil).
assert (AGd : forall n0, (n0 < AT_FL)%nat -> ew (d_env cx E (ex_vals regs h)) n0 = ew E n0)
  by (intros n0 Hn0; apply d_env_old; exact Hn0).
pose proof (d_E_env cx E (ex_vals regs h) HdE) as HdEd.
pose proof (proj1 (proj2 (proj2 HdEd))) as HEId.
assert (HArange : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
assert (HFBrange : 0 <= d_FB cx < 2 ^ 64) by lia.
pose proof (shadow_addr_bounds (d_FB cx) ltac:(unfold kHighMemEnd in *; lia)) as HSHb.
assert (HSHrange : 0 <= shadow_addr (d_FB cx) < 2 ^ 64)
  by (unfold kLowMemEnd, kHighShadowEnd in *; lia).
unfold cfg_at. change (w64 (BASE + EXIT_OFF)) with (Z_to_bv 64 (BASE + EXIT_OFF)).
unfold ss_x in HS.
paj_run_tok RUN HS HJ3 SHOK ex_span;
[ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc lyx own) end;
  apply awr_ok_cons_ro; [clear; cbn; lia|];
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (d_A cx - d_S cx));
  [ reflexivity
  | rewrite (AGd 60%nat ltac:(unfold AT_FL; lia)), E60; unfold w64;
    rewrite unsigned_lit_small by exact HArange; lia
  | cbn [YP09.r_wlo]; unfold LLVMF_STK, MFRAME in *; lia
  | cbn [YP09.r_whi]; unfold MFRAME in *; lia
  | ];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat (d_FB cx));
  [ reflexivity
  | rewrite (AGd 516%nat ltac:(unfold AT_FL; lia)), E516; unfold w64;
    apply unsigned_lit_small; exact HFBrange
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right;
    exists DFRAME_CLASS, (c_fpos cx); split; [left; reflexivity|]; left;
    unfold in_zr; cbn [fst snd]; rewrite EFB3; change (fs_frame_bytes DFRAME_CLASS) with 4096;
    unfold DFRAME_SIZE in *; lia
  | ];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat (shadow_addr (d_FB cx)));
  [ reflexivity
  | rewrite (AGd 529%nat ltac:(unfold AT_FL; lia)), E529; unfold w64;
    apply unsigned_lit_small; exact HSHrange
  | unfold fshadow_region; cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right;
    exists DFRAME_CLASS, (c_fpos cx); split; [left; reflexivity|]; right;
    unfold in_zr; cbn [fst snd]; rewrite EFB3; change (fs_frame_bytes DFRAME_CLASS / 8) with 512;
    unfold DFRAME_SH in *; lia
  | ];
  apply awr_ok_cons_ro; [clear; cbn; lia|];
  apply awr_ok_cons_ro; [clear; cbn; lia|];
  apply awr_ok_nil | ].
assert (E531 : ew (d_env cx E (ex_vals regs h)) 531%nat = Z_to_bv 64 h)
  by (change 531%nat with (AT_X + 0)%nat; rewrite (d_env_x cx E (ex_vals regs h) 0%nat ltac:(cbn; lia)); reflexivity).
match goal with HS2 : st_ok _ _ _ (restrict (w_H W) _) |- _ => rename HS2 into HSC end.
prreg HSC (10%bv : bv 5) Ra0.
prreg HSC (1%bv : bv 5) Rra.
prreg HSC (2%bv : bv 5) Qsp.
prreg HSC (3%bv : bv 5) Qgp.
prreg HSC (4%bv : bv 5) Qtp.
prreg HSC (8%bv : bv 5) Qs0.
pose proof (proj1 (proj2 (proj1 Hbase))) as HraE.
assert (E1v : ew E 1 = Z_to_bv 64 RA_LLVMF)
  by (rewrite (EE 1%nat 1%bv eq_refl), <- HraE; unfold raZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (E2v : ew E 2 = Z_to_bv 64 (d_S cx))
  by (rewrite (EE 2%nat 2%bv eq_refl); unfold d_S, spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (E8v : ew E 8 = Z_to_bv 64 (s0Z (c_regs cx)))
  by (rewrite (EE 8%nat 8%bv eq_refl); unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned).
assert (E3v : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (E4v : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
rewrite (AGd 2%nat ltac:(unfold AT_FL; lia)), E2v in Qs0.
rewrite (AGd 60%nat ltac:(unfold AT_FL; lia)), E60 in Qsp.
rewrite (AGd 3%nat ltac:(unfold AT_FL; lia)), E3v in Qgp.
rewrite (AGd 4%nat ltac:(unfold AT_FL; lia)), E4v in Qtp.
rewrite E531 in Ra0.
assert (USPd : bv_unsigned (ew (d_env cx E (ex_vals regs h)) AT_STK) = d_S cx)
  by (unfold AT_STK; rewrite (AGd 2%nat ltac:(unfold AT_FL; lia)), E2v; apply unsigned_lit_small;
      unfold LLVMF_STK in *; lia).
lazymatch type of HSC with st_ok _ ?Ec ?ssc ?msx =>
  assert (HR0 : region_ok SEGS Ec (ms_mem msx) (YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks))
  by (apply (st_ok_region_nth Ec ssc msx 0%nat _ HSC); vm_compute; reflexivity) end.
cbn [ms_mem restrict] in HR0.
match goal with HR0 : region_ok _ _ (mrestrict (w_H W) ?mc) _ |- _ => set (memc := mc) in * end.
assert (HRD8 : rdword (aview SEGS (w_H W) memc) (d_S cx - 8) = Some RA_LLVMF).
{ apply rdword_of_val_mem; [| unfold RA_LLVMF; lia].
  replace (d_S cx - 8) with (d_S cx + (-8)) by lia.
  apply (field_of_region _ _ AT_STK (d_S cx) dsave_chunks (-104) 0 0 0 (-8) 8%N (SOff 1 0) RA_LLVMF HR0
    USPd ltac:(vm_compute; tauto)
    ltac:(cbn [sv_denot]; rewrite (AGd 1%nat ltac:(unfold AT_FL; lia)), E1v, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(cbn; unfold RA_LLVMF; lia) ltac:(cbn; lia)). }
assert (HRD16 : rdword (aview SEGS (w_H W) memc) (d_S cx - 16) = Some (s0Z (c_regs cx))).
{ apply rdword_of_val_mem; [| unfold s0Z; apply bv_unsigned_in_range].
  replace (d_S cx - 16) with (d_S cx + (-16)) by lia.
  apply (field_of_region _ _ AT_STK (d_S cx) dsave_chunks (-104) 0 0 0 (-16) 8%N (SOff 8 0)
    (s0Z (c_regs cx)) HR0 USPd ltac:(vm_compute; tauto)
    ltac:(cbn [sv_denot]; rewrite (AGd 8%nat ltac:(unfold AT_FL; lia)), E8v, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr64;
          unfold bv_modulus in Hr64; cbn [Z.of_N] in Hr64 |- *; lia)
    ltac:(cbn; lia)). }
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyX ?SX ?WX ?mX ?mdX ?kX =>
  assert (HCc : d_ctx B MT XM_LIB RLO RHI tfib_K cx lyX SX WX mX mdX kX)
  by (split; [exact Hbase | split; [exact HJ3 | exact Hfrs3]]) end.
pose proof (ex_chain_alt _ _ _ _ _ _ _ HCc) as HALT.
pose proof pa_B_ok as HBok. pose proof pa_base_lo as HBlo.
assert (Hpc0 : pc_free_ra0 (as_code B) < BASE) by exact (proj1 (pal_rt_below B TL)).
assert (HU3 : In [pc_free_ra0 (as_code B); BASE + 9556; RA_LLVMF] (as_universe B))
  by (apply DUNIV; unfold d_sites; cbn [In]; repeat (first [left; reflexivity | right])).
assert (HU2 : In [pc_free_ra0 (as_code B); BASE + 9556] (as_universe B))
  by (apply DUNIV; unfold d_sites; cbn [In]; repeat (first [left; reflexivity | right])).
lazymatch type of HSC with st_ok _ _ _ (restrict _ ?msX) =>
  assert (HspX : spZ (ms_regs msX) = d_A cx)
    by (unfold spZ; rewrite Qsp; unfold w64; apply unsigned_lit_small; exact HArange);
  assert (Hs0X : s0Z (ms_regs msX) = d_S cx)
    by (unfold s0Z; rewrite Qs0; apply unsigned_lit_small; unfold LLVMF_STK in *; lia);
  assert (HraX : raZ (ms_regs msX) = BASE + 9556)
    by (unfold raZ; rewrite Rra; apply unsigned_lit_small; unfold IMG_LO in *; lia);
  destruct (d_call_chain B MT XM_LIB RLO RHI tfib_K (pc_free_ra0 (as_code B)) 9556 cx _ _ _ _ _ _ (ms_regs msX)
    (s0Z (c_regs cx)) HCc Hpc0 ltac:(lia) ltac:(unfold IMG_LO in *; lia) HU2 HU3 HspX Hs0X
    ltac:(unfold MFRAME, LLVMF_STK in *; lia) HraX HRD8 HRD16 HALT) as (ch & Hchain & Huniv)
end.
pose proof (proj1 Hbase) as HPX.
destruct HPX as (_ & _ & _ & _ & _ & _ & _ & _ & HevE & _).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & HnevJ & _).
pmkst HSC.
rewrite (pal_free B TL).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?rT _ ?mT _) ?dT) _ =>
    eapply (aj_free_at (fx := fq) SEGS B LAWS pa_segs_low (pal_env B TL) ML (AFREE fq) W rT mT LLVMF_STK (d_S cx) []
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 dT k h HUNT_SIZE
      (d_A cx - d_S cx) (Z_to_bv 64 (BASE + 9556)) ch HJ3) end.
  - apply (Permutation_in _ (Permutation_sym (proj1 Hblocks))). cbn [app In]. left. reflexivity.
  - exact Ra0.
  - rewrite HspX. lia.
  - lia.
  - unfold MFRAME, LLVMF_STK in *. lia.
  - unfold ASTACK, MFRAME, LLVMF_STK in *. lia.
  - exact Qgp.
  - exact Qtp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold EV_HEAD, EV_PRO, EV_ITER, EV_LIB, MAX_OPS in *. lia.
  - exact Hchain.
  - exact Huniv.
  - intros Hin. exfalso. exact (Forall_inv (proj1 (proj2 Hblocks)) Hin). }
cbv beta. intros W2 c2 Hwle2 (ly4 & S4 & regs4 & mem4 & md4 & Hc2 & HJ4 & HP4 & Hbl4 & Hfr4 & HK4).
subst c2.
assert (Hinh : In (h, HUNT_SIZE) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym (proj1 Hblocks))); cbn [app In]; left; reflexivity).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W memc _ h HUNT_SIZE DFRAME_CLASS (c_fpos cx) (proj1 HJ3) Hinh Hin3)
  as HdHF.
unfold zdisjoint in HdHF. cbn [fst snd] in HdHF. rewrite EFB3 in HdHF. change (req_size HUNT_SIZE) with 480 in HdHF. change (fs_frame_bytes DFRAME_CLASS) with 4096 in HdHF.
destruct (al_blocks _ _ LAWS ly3 S3 W memc _ h HUNT_SIZE (proj1 HJ3) Hinh) as (_ & Hh4096 & Hhceil & Hhapp & _).
change (req_size HUNT_SIZE) with 480 in Hh4096, Hhceil, Hhapp.
assert (Hfrs4 : frames S4 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite Hfr4; exact Hfrs3).
assert (HC4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W2 mem4 md4 (k + 1))
  by (split; [exact Hbase | split; [exact HJ4 | exact Hfrs4]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly4 S4 W2 mem4 md4 (k + 1) HC4) as
  (_ & _ & _ & _ & _ & _ & _ & _ & HFpres4 & HSHpres4 & HWpres4 & HAR4 & Hin4 & EFB4 & EFL4).
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ3)) as (Kc3 & _ & Kg3 & _).
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ4)) as (Kc4 & _ & Kg4 & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kg3, Kg4. rewrite (pal_cell B TL) in Kc3, Kc4.
assert (AG33 : forall n0, (n0 < 33)%nat -> ew (d_env cx E (ex_vals regs h)) n0 = ew E n0)
  by (intros n0 Hn0; apply d_env_old; unfold AT_FL; lia).
unfold w64 in E60, E516, E529, E32.
assert (E530 : ew (d_env cx E (ex_vals regs h)) 530%nat
  = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)))
  by (change 530%nat with AT_FL; exact (d_env_fl cx E (ex_vals regs h))).
reseat HSC HJ4 HP4 [0; 1; 2; 3; 4; 5]%nat AG33 ltac:(idtac;
  first
  [ eapply (region_kept_stack_aj SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (d_S cx) (d_S cx));
    [ exact HK4 | exact HJ4
    | rewrite (AGd 2%nat ltac:(unfold AT_FL; lia)), E2v; apply unsigned_lit_small; unfold LLVMF_STK in *; lia
    | unfold ASTACK, MFRAME, LLVMF_STK in *; lia | unfold LLVMF_STK in *; lia | lia | lia | lia ]
  | eapply (region_kept_stack_aj SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (d_S cx) (d_A cx));
    [ exact HK4 | exact HJ4
    | rewrite (AGd 60%nat ltac:(unfold AT_FL; lia)), E60; apply unsigned_lit_small; exact HArange
    | unfold ASTACK, MFRAME, LLVMF_STK in *; lia | unfold MFRAME, LLVMF_STK in *; lia
    | unfold MFRAME, LLVMF_STK in *; lia | lia | lia ]
  | eapply (region_kept_ownframe_aj SEGS B _ _ _ _ _ _ _ _ _ (fun a => h <= a < h + req_size HUNT_SIZE)
      _ _ _ _ _ _ (d_FB cx) DFRAME_CLASS (c_fpos cx));
    [ exact HK4
    | rewrite (AGd 516%nat ltac:(unfold AT_FL; lia)), E516; apply unsigned_lit_small; exact HFBrange
    | exact Hin3
    | left; rewrite EFB3; change (fs_frame_bytes DFRAME_CLASS) with 4096; lia
    | intros a Ha; unfold not; cbv beta; change (req_size HUNT_SIZE) with 480; lia
    | intros a Ha; apply HFpres4; unfold DFRAME_SIZE in *; lia ]
  | eapply (region_kept_ownframe_aj SEGS B _ _ _ _ _ _ _ _ _ (fun a => h <= a < h + req_size HUNT_SIZE)
      _ _ _ _ _ _ (shadow_addr (d_FB cx)) DFRAME_CLASS (c_fpos cx));
    [ exact HK4
    | rewrite (AGd 529%nat ltac:(unfold AT_FL; lia)), E529; apply unsigned_lit_small; exact HSHrange
    | exact Hin3
    | right; rewrite EFB3; change (fs_frame_bytes DFRAME_CLASS / 8) with 512; lia
    | intros a Ha Hx; cbv beta in Hx;
      refine (fshadow_not_app (d_FB cx) 512 h (req_size HUNT_SIZE) a ltac:(lia) ltac:(lia) Hhapp _ Hx);
      revert Ha; unfold shadow_addr, SHADOW_OFF; lia
    | intros a Ha; replace a with (shadow_addr (d_FB cx) + (a - shadow_addr (d_FB cx))) by lia;
      apply HSHpres4; unfold DFRAME_SH in *; lia ]
  | apply (region_kept_val_at _ _ _ (A_OBJ 1) (pa_val (A_OBJ 1)) 8 (pa_val (A_OBJ 66)));
    [ rewrite (AGd (A_OBJ 1) ltac:(unfold A_OBJ, AT_FL; lia));
      rewrite (img_env_atomP E (A_OBJ 1) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia));
      apply unsigned_lit_small; apply pa_val_range
    | exact (val_mem_of_rdword SEGS _ _ _ _ Kg3) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg4) | lia ]
  | apply (region_kept_val_at _ _ _ (A_OBJ 66) (pa_val (A_OBJ 66)) 8 SHADOW_OFF);
    [ rewrite (AGd (A_OBJ 66) ltac:(unfold A_OBJ, AT_FL; lia));
      rewrite (img_env_atomP E (A_OBJ 66) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia));
      apply unsigned_lit_small; apply pa_val_range
    | exact (val_mem_of_rdword SEGS _ _ _ _ Kc3) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc4) | lia ] ]).
lazymatch type of HSC with st_ok_pi _ _ ?Ev _ (restrict _ ?msv) =>
  assert (SHOK2 : sh_ok SEGS (SOff 32 0) [] Ev (mrestrict (w_H W2) (ms_mem msv))) by apply Forall_nil end.
paj_run_tok RUN HSC HJ4 SHOK2 ex_span;
[ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc lyx own) end;
  apply awr_ok_cons_ro; [clear; cbn; lia|];
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (d_A cx - d_S cx));
  [ reflexivity
  | rewrite E60; rewrite unsigned_lit_small by exact HArange; lia
  | cbn [YP09.r_wlo]; unfold LLVMF_STK, MFRAME in *; lia
  | cbn [YP09.r_whi]; unfold MFRAME in *; lia
  | ];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat (d_FB cx));
  [ reflexivity
  | rewrite E516; apply unsigned_lit_small; exact HFBrange
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right;
    exists DFRAME_CLASS, (c_fpos cx); split; [left; reflexivity|]; left;
    unfold in_zr; cbn [fst snd]; rewrite EFB4; change (fs_frame_bytes DFRAME_CLASS) with 4096;
    unfold DFRAME_SIZE in *; lia
  | ];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat (shadow_addr (d_FB cx)));
  [ reflexivity
  | rewrite E529; apply unsigned_lit_small; exact HSHrange
  | unfold fshadow_region; cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right;
    exists DFRAME_CLASS, (c_fpos cx); split; [left; reflexivity|]; right;
    unfold in_zr; cbn [fst snd]; rewrite EFB4; change (fs_frame_bytes DFRAME_CLASS / 8) with 512;
    unfold DFRAME_SH in *; lia
  | ];
  apply awr_ok_cons_ro; [clear; cbn; lia|];
  apply awr_ok_cons_ro; [clear; cbn; lia|];
  apply awr_ok_nil | ].
match goal with HS2 : st_ok _ _ _ (restrict (w_H W2) _) |- _ => rename HS2 into HSF end.
prreg HSF (10%bv : bv 5) Fa0.
prreg HSF (11%bv : bv 5) Fa1.
prreg HSF (1%bv : bv 5) Fra.
prreg HSF (2%bv : bv 5) Fsp.
prreg HSF (3%bv : bv 5) Fgp.
prreg HSF (4%bv : bv 5) Ftp.
pose proof (FFL ly4 S4 W2 mem4 md4 DFRAME_CLASS (c_fpos cx) HAR4 Hin4) as (_ & _ & _ & HFLb).
rewrite EFL4 in HFLb.
lazymatch type of HSF with st_ok _ ?Ex ?ssx ?msr =>
  pose proof (st_ok_region_nth Ex ssx msr 2%nat _ HSF eq_refl) as HRF end.
lazymatch type of HRF with region_ok _ ?Ex ?mm (YP09.mkRegion (Some ?nn) ?lo ?hi ?wlo ?whi ?cs) =>
  pose proof (field_of_region Ex mm nn (d_FB cx) cs lo hi wlo whi 4088 8%N (SOff 530 0)
    (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) HRF
    ltac:(rewrite E516; apply unsigned_lit_small; exact HFBrange)
    ltac:(vm_compute; tauto)
    ltac:(cbn [sv_denot]; rewrite E530, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(cbn; lia)
    ltac:(cbn; lia)) as HFLAGV end.
rewrite Z.add_comm in HFLAGV.
pose proof (rdword_of_val_mem _ _ _ _ _ HFLAGV ltac:(lia)) as HFLAG.
pmkst HSF.
rewrite de_sf6.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?rT _ ?mT _) ?dT) _ =>
    eapply (aj_stack_free_at (fx := fq) SEGS B LAWS pa_segs_low ML SF6_ENTRY DFRAME_CLASS
      (ASF6 fq) ltac:(unfold DFRAME_CLASS; lia) W2 rT mT LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [] ly4 S4 dT (k + 1) (c_fpos cx) 3072 (d_A cx - d_S cx) (Z_to_bv 64 (BASE + 9948)) HJ4) end.
  - rewrite Fa0, E516, EFB4. reflexivity.
  - rewrite Fa1. reflexivity.
  - change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
  - reflexivity.
  - rewrite EFB4, EFL4. change (fs_frame_bytes DFRAME_CLASS) with 4096.
    replace (d_FB cx + 4096 - 8) with (4088 + d_FB cx) by lia. exact HFLAG.
  - unfold spZ. rewrite Fsp, E60. rewrite unsigned_lit_small by exact HArange. lia.
  - lia.
  - unfold MFRAME, LLVMF_STK in *. lia.
  - unfold ESTACK, LLVMF_STK, MFRAME in *. lia.
  - rewrite Fgp, (AG33 3%nat ltac:(lia)), E3v. reflexivity.
  - rewrite Ftp, (AG33 4%nat ltac:(lia)), E4v. reflexivity.
  - exact Fra.
  - apply ret_ok_codeptr_v; [lia | reflexivity]. }
cbv beta. intros W5 c5 Hwle5 (Hw5 & regs5 & mem5 & md5 & Hc5 & HJ5 & HP5 & Hf5v & Hkeep5 & Hpres5).
subst W5 c5.
reseat HSF HJ5 HP5 [0]%nat AG33 ltac:(idtac;
  apply (region_kept_pointwise SEGS _ _ _ 2%nat (-104)%Z 0%Z 0%Z 0%Z _ (d_S cx));
  [ rewrite (AG33 2%nat ltac:(lia)), E2v; apply unsigned_lit_small; unfold LLVMF_STK in *; lia
  | intros a Ha; apply (mbyte_of_aview SEGS); apply Hkeep5;
    [ unfold LLVMF_STK in *; lia
    | unfold not; cbv beta; rewrite EFB4; change (sf_span DFRAME_CLASS 3072) with 512;
      unfold shadow_addr, SHADOW_OFF; unfold LLVMF_STK in *; lia
    | rewrite EFL4; unfold LLVMF_STK in *; lia
    | unfold not; cbv beta; unfold ESTACK, MFRAME, LLVMF_STK in *; lia ]
  | lia ]).
match goal with HS2 : st_ok_pi _ _ _ _ (restrict (w_H W2) _) |- _ => rename HS2 into HSG end.
lazymatch type of HSG with st_ok_pi _ _ ?Ev _ (restrict _ ?msv) =>
  assert (SHOK3 : sh_ok SEGS (SOff 32 0) [] Ev (mrestrict (w_H W2) (ms_mem msv))) by apply Forall_nil end.
paj_run_tok RUN HSG HJ5 SHOK3 ex_span;
[ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc lyx own) end;
  repeat (apply awr_ok_cons_ro; [clear; cbn; lia|]); apply awr_ok_nil | ].
match goal with HS2 : st_ok_pi _ _ _ _ (restrict (w_H W2) _) |- _ => rename HS2 into HSR end.
prreg HSR (1%bv : bv 5) Gr1.
prreg HSR (2%bv : bv 5) Gr2.
prreg HSR (3%bv : bv 5) Gr3.
prreg HSR (4%bv : bv 5) Gr4.
prreg HSR (8%bv : bv 5) Gr8.
prreg HSR (9%bv : bv 5) Gr9.
prreg HSR (10%bv : bv 5) Gr10.
prreg HSR (18%bv : bv 5) Gr18.
prreg HSR (19%bv : bv 5) Gr19.
prreg HSR (20%bv : bv 5) Gr20.
prreg HSR (21%bv : bv 5) Gr21.
prreg HSR (22%bv : bv 5) Gr22.
prreg HSR (23%bv : bv 5) Gr23.
prreg HSR (24%bv : bv 5) Gr24.
prreg HSR (25%bv : bv 5) Gr25.
prreg HSR (26%bv : bv 5) Gr26.
prreg HSR (27%bv : bv 5) Gr27.
assert (Hab : forall c p S0, ablocks B ly4 (stack_free_state c p S0) = ablocks B ly4 S0)
  by (intros c p S0; unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
destruct Hbl4 as (l1 & l2 & El3 & El4).
assert (HPERM : Permutation (ablocks B ly4 (stack_free_state DFRAME_CLASS (c_fpos cx) S4))
  (ablocks B (c_ly cx) (c_S cx))).
{ rewrite Hab, El4. apply (Permutation_cons_inv (a := (h, HUNT_SIZE))).
  eapply perm_trans; [apply Permutation_middle|]. rewrite <- El3. exact (proj1 Hblocks). }
eapply (RET W2 _ _ _ _ _ HSR eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
lazymatch goal with |- context [v_jalr (getr (ms_regs ?msX) 1) 0] =>
  assert (Hpc : v_jalr (getr (ms_regs msX) 1) 0 = getr (c_regs cx) 1)
  by (rewrite Gr1, (AG33 1%nat ltac:(lia)), E1v;
      rewrite v_jalr_lit_even by (unfold RA_LLVMF; first [lia | reflexivity]);
      rewrite <- E1v; exact (EE 1%nat 1%bv eq_refl));
  rewrite Hpc;
  assert (HPR : aregs_preserved (c_regs cx) (ms_regs msX))
end.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
    r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite Gr2, (AG33 2%nat ltac:(lia)). exact (EE 2%nat 2%bv eq_refl).
  - replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite Gr3, (AG33 3%nat ltac:(lia)). exact (EE 3%nat 3%bv eq_refl).
  - replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite Gr4, (AG33 4%nat ltac:(lia)). exact (EE 4%nat 4%bv eq_refl).
  - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite Gr8, (AG33 8%nat ltac:(lia)). exact (EE 8%nat 8%bv eq_refl).
  - replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite Gr9, (AG33 9%nat ltac:(lia)). exact (EE 9%nat 9%bv eq_refl).
  - replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite Gr18, (AG33 18%nat ltac:(lia)). exact (EE 18%nat 18%bv eq_refl).
  - replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite Gr19, (AG33 19%nat ltac:(lia)). exact (EE 19%nat 19%bv eq_refl).
  - replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite Gr20, (AG33 20%nat ltac:(lia)). exact (EE 20%nat 20%bv eq_refl).
  - replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite Gr21, (AG33 21%nat ltac:(lia)). exact (EE 21%nat 21%bv eq_refl).
  - replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite Gr22, (AG33 22%nat ltac:(lia)). exact (EE 22%nat 22%bv eq_refl).
  - replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite Gr23, (AG33 23%nat ltac:(lia)). exact (EE 23%nat 23%bv eq_refl).
  - replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite Gr24, (AG33 24%nat ltac:(lia)). exact (EE 24%nat 24%bv eq_refl).
  - replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite Gr25, (AG33 25%nat ltac:(lia)). exact (EE 25%nat 25%bv eq_refl).
  - replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite Gr26, (AG33 26%nat ltac:(lia)). exact (EE 26%nat 26%bv eq_refl).
  - replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). rewrite Gr27, (AG33 27%nat ltac:(lia)). exact (EE 27%nat 27%bv eq_refl). }
eapply exit_post_nil.
all: first
  [ exact MT_TRIV
  | exact de_ail
  | exact Hfrm0
  | exact Hbase
  | (apply (ajournal_materialize SEGS B LAWS pa_segs_low); eassumption)
  | (unfold EV_LIB; unfold EV_HEAD, EV_PRO, EV_ITER, MAX_OPS in Hkb; lia)
  | exact HPERM
  | exact HPR
  | exact Gr10 ].
Qed.
End wh.
End wf.
End w.
