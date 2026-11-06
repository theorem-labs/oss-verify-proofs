(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC94.v, with its module paths and module names changed; 470 of its 496 lines of code are new or changed and 223 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/codec_bmain_head_mid.v, with its module names changed; 120 of its 180 lines of code are new or changed and 436 lines of the source are left out. *)
(* RUN 0x826f4-0x82718 of the image-B walk of LLVMFuzzerTestOneInput (lib/AU/Prog/codec_bmain_inv.v seg_run):
   run()'s switch on the kind.
     0x826f4 lw a0,0(s7)             a0 = k.kind (s7 = k = F + 192)
     0x826f8 li a1,10; 0x826fc bltu a1,a0,0x8281c   10 < kind: ENC11 (SYSEX)
     0x82700 .. 0x82718              a0 = kind * 4 + 0x20f3c, lw a0,0(a0), a0 += 0x20f3c, jr a0: run()'s table, ENCk
   No store, no instrumented check and no UBSan trap edge (codec_bmain_inv.v's lists have no pc in
   0x826f4-0x82718): the walk reads k.kind and one word of the image's table at 0x20f3c.
   It is the image-A RUN (lib/A/Prog/codec_amain_run.v) at image B, in the form of the image-B HEAD tail
   (lib/AU/Prog/codec_bmain_head_tail.v, whose record region ht_rk and run tactics it uses): the walk is split on
   the kind (0 .. 11, enc_okZ) first, so the record's kind is a literal of the state's region at F + 192 and every
   address of the run is a literal. For kinds 0 .. 10 the run stops before the table load (0x82710), the record's
   region is replaced by the table's (11 words of the read-only image), and a second run reaches enc_pc kind, so
   each table entry is checked against the ENC root of codec_bmain_inv.v; kind 11 takes the branch to 0x8281c.
   The end cut is the exit bridge's (codec_bmain_st.bm_exit, bm_mcut); the record's bytes, the cursor and the 60
   shadow bytes are kept (the only write window of the state is the cursor's, which the runs do not use). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CodecRo CodecGlobs CPgWalkU CPgWalkImgU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_st codec_bmain_lem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_headl codec_bmain_head_tail.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* run()'s table: 11 words of the read-only image; the pc of its load *)
Definition RN_TBL : Z := 0x20f3c.
Definition rn_rt : YP09.region := cpg_img_region RN_TBL 44.
Definition RN_LD : Z := 0x82710.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.

Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).

(* the base regions but the .got slot and the cell, then the record's kind n (a literal when it runs) *)
Ltac rn_go n :=
  lazymatch goal with
  | HS0 : st_ok _ _ _ _, HRk : region_ok _ _ _ (ht_rk _),
    U2 : bv_unsigned (ew _ 2) = ?sp1, U33 : bv_unsigned (ew _ 33) = _ |- _ =>
  ht_keep HS0 [0; 3; 4]%nat;
  lazymatch goal with HSx : st_ok _ ?Ev _ _ |- _ =>
    pose proof (ast_ok_add_region tfibsegs Ev _ _ (ht_rk n) HSx eq_refl HRk
      ltac:(cbn [ss_mem]; unfold ht_rk, bm_frame_region, stack_region, bm_spill_region, bm_cur_region;
            cbn [all_disjoint]; unfold extent_disjoint;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U33, U2;
            repeat split; lia)) as HS2;
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2; clear HSx; rename HS2 into HS end
  end.

Lemma run_n : forall n g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kev c k od,
0 <= n <= 11 -> kz_kind k = n ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kev ->
frames S2 = [(3, pos)] -> 0 <= kev <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ops_at ops regs2 -> cur_at g sp1 c W2 mem2 -> k_at g pos k W2 mem2 -> enc_okZ k od ->
SRr tfibsegs W2 (cfg_at tfibsegs PC_RUN regs2 mem2 md2)
  (fun W3 c3 => exists kind, inv_enc B MT K XM_LIB g pos sp1 ops kind W3 c3).
Proof using TL LAWS ML ROB.
intros n g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kev c k od Hn Ek HJ Hfr Hk Hmo HC Hops Hcur Hkat Henc.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hng & Hpg & Hpng & Hblk).
unfold BM_HI in Hchi.
pose proof HC as (Hpre & _ & R2 & _).
pose proof HC as HSH. do 47 (destruct HSH as (_ & HSH)). destruct HSH as (HSH & _).
pose proof HC as HPerm0. do 49 (destruct HPerm0 as (_ & HPerm0)).
destruct Hops as (Hops1 & Hops2).
pose proof Hcur as (Hc & C184 & C192).
destruct Hkat as (Hkat & Hkwf).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (Hsh : SB + 512 <= shadow_addr (FA g pos) <= SB + 2 ^ 44).
{ unfold shadow_addr. rewrite <- SB_SHADOW_OFF. split; [apply Z.add_le_mono_l; apply Z.div_le_lower_bound; lia|].
  apply Z.add_le_mono_l. apply Z.div_le_upper_bound; lia. }
unfold SB in Hsh.
pose proof (bm_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev c PC_RUN [] [] []
  HJ Hfr HC Hcur eq_refl (Forall_nil _) I (Forall_nil _) I) as HS0.
assert (HRk : region_ok tfibsegs (bm_env g pos c regs2 []) (mrestrict (w_H W2) mem2) (ht_rk n)).
{ apply (bm_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kev c [] 192 196 192 192 _
    HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val tfibsegs _ _ (FA g pos) 192 4 (SLit n) n); [reflexivity | cbn; lia | cbn; lia |].
  rewrite <- Ek. exact (proj1 Hkat). }
assert (HE2 : ew (bm_env g pos c regs2 []) 2 = getr regs2 2) by exact (bm_ew_reg g pos c regs2 [] 2 2%bv eq_refl).
assert (U2 : bv_unsigned (ew (bm_env g pos c regs2 []) 2) = sp1)
  by (rewrite HE2, R2; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew (bm_env g pos c regs2 []) 33) = FA g pos)
  by (rewrite (bm_ew_F g pos c regs2 []); apply unsigned_lit_small; lia).
assert (HE20 : ew (bm_env g pos c regs2 []) 20 = getr regs2 20) by exact (bm_ew_reg g pos c regs2 [] 20 20%bv eq_refl).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 184 <= a < sp1 + 200) ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity).
unfold cfg_at. change (w64 PC_RUN) with (Z_to_bv 64 PC_RUN).
rn_go n.
(* the end of the run at enc_pc n: the cut *)
assert (Hend : forall W3 regs3 mem3 md3 ly3 S3 k3 ss3 pc3,
  ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly3 S3 W3 mem3 md3 k3 ->
  ly3 = ly2 -> S3 = S2 -> k3 = kev -> W3 = W2 ->
  st_ok tfibsegs (bm_env g pos c regs2 []) ss3 (restrict (w_H W3) (mkst regs3 pc3 mem3 (seg_rom tfibsegs))) ->
  bm_keep_ok (ss_regs ss3) = true ->
  sr_get (ss_regs ss3) (20%bv : bv 5) = SOff 20 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 184 <= a < sp1 + 200) ->
     aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
  val_mem tfibsegs (mrestrict (w_H W3) mem3) (sp1 + 184) 8 (e_p g + c) ->
  val_mem tfibsegs (mrestrict (w_H W3) mem3) (sp1 + 192) 8 (e_n g - c) ->
  pc3 = Z_to_bv 64 (enc_pc n) ->
  inv_enc B MT K XM_LIB g pos sp1 ops n W3 (mkCfg (mkst regs3 pc3 mem3 (seg_rom tfibsegs)) md3)).
{ intros W3 regs3 mem3 md3 ly3 S3 k3 ss3 pc3 HJ3 -> -> -> -> HS3 Hkeep R20 KE3 V184 V192 ->.
  assert (HC3 : mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs3 mem3 md3).
  { eapply (bm_exit B MT K XM_LIB LAWS); [exact HC | exact HJ3 | apply env_agree_refl | exact HS3 | exact Hkeep
    | | | exact HPerm0].
    - intros a Ha. unfold bm_keepzone in Ha. apply KE3; [lia|]. lia.
    - intros i Hi. rewrite KE3 by lia. exact (HSH i Hi). }
  unfold inv_enc. eapply bm_mcut; [exact HJ3 | exact Hfr | lia | exact Hmo | exact HC3 |].
  assert (G20 : getr regs3 20 = getr regs2 20).
  { rewrite (st_ok_restrict_reg tfibsegs (w_H W2) _ ss3 _ (20%bv : bv 5) HS3). cbn [ms_regs mkst restrict].
    rewrite R20. cbn [sv_denot]. rewrite HE20, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  split; [split; [exact Hops1 | rewrite G20; exact Hops2]|].
  split; [lia|].
  exists c, k, od.
  split; [split; [exact Hc | split; [exact V184 | exact V192]]|].
  split; [|split; [exact Henc | exact Ek]].
  split; [|exact Hkwf].
  apply (hd_kcall_kept W2 W2 mem2 mem3 (FA g pos + 192) k Hkat Hkwf).
  intros x Hx. apply KE3; lia. }
(* the read-only image at any state of the journal, for the table's region *)
assert (HRO : forall ly3 S3 W3 mem3 md3 k3,
  ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly3 S3 W3 mem3 md3 k3 ->
  arodata_okP tfibsegs CB_RLO CB_RHI B (aview tfibsegs (w_H W3) mem3))
  by (intros ly3 S3 W3 mem3 md3 k3 HJ3; exact (arodata_ok_at B MT K XM_LIB g [(3, pos)] ly3 S3 W3 mem3 md3 k3 Hpre HJ3)).
assert (HT0 : forall a, RN_TBL <= a < RN_TBL + 44 ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
  by (intros a Ha; apply (tl_lib_consts B TL); unfold lib_const_addr; unfold RN_TBL in Ha; lia).
assert (Hn' : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/
  n = 10 \/ n = 11) by lia.
(* without kz_kind k = n in the context, the last case's subst makes n the literal 11, not kz_kind k *)
clear Hn Ek.
repeat (destruct Hn' as [-> | Hn']); [ .. | subst n].
(* kind 0 .. 10: the kind run to the table load, the table's region in place of the record's, the run to ENCk *)
1-11: ht_run sp1 U2 RN_LD; ht_keep HS [1; 2; 3]%nat;
  lazymatch goal with HS : st_ok _ ?Ev _ (restrict _ ?msx), HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof (ast_ok_add_region tfibsegs Ev _ _ rn_rt HS eq_refl
      (cpg_img_region_ok B CB_RLO CB_RHI Ev W2 (ms_mem msx) RN_TBL 44 (HRO _ _ _ _ _ _ HJx) (bm_in_ro RN_TBL 44 eq_refl)
         (fun a Ha => proj1 (HT0 a Ha)) (fun a Ha => proj2 (HT0 a Ha)) eq_refl
         ltac:(unfold RN_TBL; lia) ltac:(lia) ltac:(unfold RN_TBL; lia))
      ltac:(cbn [ss_mem]; unfold rn_rt, cpg_img_region, RN_TBL; cbn [all_disjoint]; unfold extent_disjoint;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U2; repeat split; lia)) as HS2;
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2; clear HS; rename HS2 into HS end.
1-11: lazymatch goal with HRk : region_ok _ _ _ (ht_rk ?n) |- _ =>
  let pc := eval vm_compute in (enc_pc n) in ht_run sp1 U2 pc end.
(* kind 11: bltu taken, one run to SYSEX *)
12: ht_run sp1 U2 0x8281c.
(* the end cut, for every kind *)
all: lazymatch goal with HS : st_ok _ ?Ev ?ssx (restrict _ ?msx), HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  let Hshape := fresh "Hshape" in
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) Ev ssx msx HS eq_refl) as Hshape;
  rewrite Hshape in HS |- *; clear Hshape;
  apply SRr_ret;
  let r3 := eval vm_compute in (nth 3 (ss_mem ssx) got_region) in
  let HR := fresh "HR" in
  pose proof (st_ok_region_nth Ev ssx _ 3 r3 HS ltac:(vm_compute; reflexivity)) as HR;
  cbn [ms_mem mkst restrict] in HR;
  eexists; eapply Hend;
  [ exact HJx | reflexivity | reflexivity | reflexivity | reflexivity | exact HS
  | vm_compute; reflexivity | vm_compute; reflexivity | exact KE
  | apply (field_of_region Ev _ 2 sp1 _ _ _ _ _ 184 8 (SOff 35 0) (e_p g + c) HR U2);
    [ cbn [In]; left; reflexivity
    | cbn [sv_denot]; rewrite (bm_ew_CP g pos c regs2 []), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold BM_HI in *; cbn; lia | cbn; lia ]
  | apply (field_of_region Ev _ 2 sp1 _ _ _ _ _ 192 8 (SOff 36 0) (e_n g - c) HR U2);
    [ cbn [In]; right; left; reflexivity
    | cbn [sv_denot]; rewrite (bm_ew_CN g pos c regs2 []), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold BM_HI in *; cbn; lia | cbn; lia ]
  | vm_compute; reflexivity ] end.
Qed.

Theorem seg_run_holds : seg_run B MT K XM_LIB.
Proof using TL LAWS ML ROB.
intros g pos sp1 ops W2 c2
  (ly2 & S2 & regs2 & mem2 & md2 & kev & -> & HJ & Hfr & Hk & Hmo & HC & Hops & (c & k & od & Hcur & Hkat & Henc)).
pose proof Henc as (Hkind & _).
exact (run_n (kz_kind k) g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kev c k od Hkind eq_refl HJ Hfr Hk Hmo HC Hops
  Hcur Hkat Henc).
Qed.
End b.
End a.
