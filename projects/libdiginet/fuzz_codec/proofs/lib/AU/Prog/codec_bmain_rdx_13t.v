(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AC94.v, with its module paths and module names changed; 691 of its 712 lines of code are new or changed and 228 lines of the source are left out. *)
(* Segment RD13 (COUNTER_TEXT) of the image-B walk of LLVMFuzzerTestOneInput, from the join at 0x8130c
   (lib/AU/Prog/codec_bmain_rdx_13.v): text_arg, check_text_seg7, check_text_counter and owed_counter_text, each
   through its image-B contract (lib/AU/Prog/CPgChkU.v), then owed_counter_text's refusal to LATCH (the dots byte's
   shadow back to f8) or kind 10 and k.b = dots to ENC10.
     0x8130c  addi a0,s1,184; ld s6,104(s1) (text = F + 80); mv a1,s6; jal text_arg (ra = 0x8131c);
     0x8131c  jal check_text_seg7 (ra = 0x81320);
     0x81320  mv a0,s6; ld s8,120(s1) (k.bytes = F + 232); mv a1,s8; mv a2,s9 (the dots byte F + 448);
              jal check_text_counter (ra = 0x81334);
     0x81334  mv a0,s6; mv a1,s8; mv a2,s9; jal owed_counter_text (ra = 0x81344);
     0x81344  beqz a0,0x81664; 0x81348 sb s11,56(s2); j 0x82df4 (LATCH);
     0x81664  lbu a0,0(s9); li a1,10; sw a1,0(s7); sw a0,28(s7); sb s11,56(s2); j 0x8274c (ENC10).
   Each call state is re-seated after the return by the callee post's tcj_kept (jafter_call_keep), the cut's
   bytes carried by lib/AU/Prog/codec_bmain_rdx_l13.v's r13_run_kept / r13_call_kept.
   It is the image-A part lib/A/Prog/codec_amain_rd13t.v at image B. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require YD1y.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CPgSat.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CodecRo CodecGlobs CPgWalkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkKeptU CPgWalkCallU CPgWalkRoU CPgWalkImgU CPgSatU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_inv codec_bmain_st codec_bmain_lem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import codec_bmain_headl codec_bmain_encl codec_bmain_rdx_l13.
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
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis IV : img_shadow_vis tfibsegs B.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Hypothesis RF : cpw_rows_free B CB_ROSTRS.
Hypothesis CTA : cdcU_text_arg_specX tfibsegs B MT BM_text_arg.
Hypothesis CS7 : cdcU_check_seg7_specX tfibsegs B MT CB_RLO CB_RHI CB_SEG7 CB_GLYPH CB_ROSTRS BM_check_seg7.
Hypothesis CTC : cdcU_check_text_counter_specX tfibsegs B MT CB_RLO CB_RHI CB_SEG7 CB_GLYPH CB_ROSTRS BM_check_text_counter.
Hypothesis COC : cdcU_owed_counter_text_specX tfibsegs B MT CB_RLO CB_RHI CB_GLYPH CB_ROSTRS BM_owed_counter_text.

(* the stopped state as a configuration of the cut *)
Ltac r13_shape W2 HS pc :=
  lazymatch type of HS with YP0l.st_ok _ _ ?ssx (restrict _ ?msx) =>
    let Hpc := fresh "Hpc" in let Hshape := fresh "Hshape" in
    assert (Hpc : ss_pc ssx = pc) by (vm_compute; reflexivity);
    pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) _ ssx msx HS eq_refl) as Hshape;
    rewrite Hpc in Hshape; rewrite Hshape in HS |- *; clear Hpc Hshape end.
(* the frame's 60 shadow bytes at an end cut, out of the shadow region (index i) of the state *)
Ltac r13_shadow W2 HS idx BS :=
  let i := fresh "i" in let Hi := fresh "Hi" in
  intros i Hi; rewrite <- bm_shm0_eq;
  lazymatch type of HS with YP0l.st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
    let r := eval vm_compute in (nth idx (ss_mem ssx) got_region) in
    apply (bm_sh_read_all Ev W2 (ms_mem msx) r _ bm_shm0);
    [ exact (st_ok_region_nth Ev ssx (restrict (w_H W2) msx) idx r HS ltac:(vm_compute; reflexivity))
    | cbn [YP09.r_base base_val]; exact BS
    | vm_compute; reflexivity
    | vm_compute (Z.of_nat (length bm_shm0)); lia ] end.
(* register 20 (s4, the loop counter) at an end cut *)
Ltac r13_ops HS E20 R20 :=
  lazymatch type of HS with YP0l.st_ok _ ?Ev ?ssx (restrict ?Hh ?msx) =>
    rewrite (st_ok_restrict_reg tfibsegs Hh Ev ssx msx (20%bv : bv 5) HS);
    let e := eval vm_compute in (sr_get (ss_regs ssx) (20%bv : bv 5)) in
    change (sr_get (ss_regs ssx) (20%bv : bv 5)) with e;
    rewrite (bm_den_off Ev 20%nat _ 0 (eq_trans E20 R20) ltac:(lia) ltac:(lia)), Z.add_0_r; reflexivity end.

(* RD13 from the join at 0x8130c (lib/AU/Prog/codec_bmain_rdx_13.v): text_arg, check_text_seg7, check_text_counter and
   owed_counter_text, the refusal to LATCH or kind 10 and k.b = dots to ENC10 *)
Lemma r13_tail : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c pv dv od (y1 y10 y11 y12 pv' dv' : Z) (d' : desk) ms md,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kj ->
frames S2 = [(3, pos)] -> 0 <= kj <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
0 <= ops <= 255 -> getr regs2 20 = w64 ops -> cur_at g sp1 c W2 mem2 -> 1 <= c ->
pd_okB pv dv od -> getr regs2 22 = w64 pv -> k_at g pos (k_rdZ 13 pv dv) W2 mem2 ->
YP0l.st_ok tfibsegs (bm_env g pos c regs2 [dv; y1; y10; y11; y12]) r13_ss_mid (restrict (w_H W2) ms) ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 (ms_mem ms) md kj ->
pd_okB pv' dv' (Some d') ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (FA g pos + 200) 8 pv' ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (FA g pos + 208) 8 dv' ->
(forall a, r13_zone g pos sp1 a -> aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a) ->
SRr tfibsegs W2 (mkCfg ms md)
  (fun W3 c3 => inv_enc B MT K XM_LIB g pos sp1 ops 10 W3 c3 \/ inv_latch B MT K XM_LIB g pos sp1 ops W3 c3).
Proof.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 kj c pv dv od y1 y10 y11 y12 pv' dv' d' ms md
  HJ Hfr Hkj HMO HC Hops R20 Hcur Hc1 Hpd R22 Hkat HS HJ1 Hpd' Vp' Vd' KZ.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
destruct (bm_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
set (F := FA g pos) in *.
assert (Hin3 : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
pose proof HJ as (HAR & _).
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 3 pos HAR Hin3) as (_ & _ & Happ).
assert (E512 : fs_frame_bytes 3 = 512) by reflexivity.
rewrite EFA, E512 in Happ. rewrite E512 in Hfceil.
pose proof (Z.div_mod F 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8.
  set (E1 := bm_env g pos c regs2 [dv; y1; y10; y11; y12]) in HS.
  pose proof HC as (_ & _ & R2 & R9 & R8 & R3 & R4 & _).
  assert (B21 : bv_unsigned (ew E1 2) = sp1).
  { unfold E1. rewrite (bm_ew_reg g pos c regs2 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small.
    unfold BM_HI in *. lia. }
  assert (BF1 : bv_unsigned (ew E1 33) = F) by (unfold E1; rewrite bm_ew_F; apply unsigned_lit_small; unfold BM_HI in *; lia).
  assert (BS1 : bv_unsigned (ew E1 34) = shadow_addr F).
  { unfold E1. rewrite bm_ew_SH. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF, BM_HI in *. lia. }
  (* 0x8130c addi a0,s1,184; ld s6,104(s1); mv a1,s6; jal text_arg *)
  aj_run_to tfibtbl_lib_ok HS HJ1 0x83ba0.
  { r13_awr. }
  r13_reg HS (1%bv : bv 5) Rra. r13_reg HS (2%bv : bv 5) Rsp. r13_reg HS (3%bv : bv 5) Rgp. r13_reg HS (4%bv : bv 5) Rtp.
  r13_reg HS (10%bv : bv 5) Ra0. r13_reg HS (11%bv : bv 5) Ra1.
  pose proof HC as HPerm0. do 49 (destruct HPerm0 as (_ & HPerm0)).
  pose proof Hcur as (Hc0 & _ & _).
  assert (Usp : spZ (ms_regs ms0) = sp1)
    by (unfold spZ; rewrite Rsp, B21, Z.add_0_r; apply unsigned_lit_small; unfold BM_HI in *; lia).
  assert (Hes : ESTACK = 4096) by reflexivity.

  pose proof HC as (Hpre0 & _).
  pose proof Hpre0 as Hpre1. unfold e_pre, codec_lib_pre_x in Hpre1.
  destruct Hpre1 as (_ & _ & _ & _ & _ & _ & _ & _ & Hev0 & Hlive0 & _).
  (* the frame's shadow bytes at the call, from the shadow region *)
  lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssx (restrict _ ?msx) |- _ =>
    let r := eval vm_compute in (nth 5 (ss_mem ssx) got_region) in
    assert (SH1 : forall i, 0 <= i < 60 ->
      aview tfibsegs (w_H W2) (ms_mem msx) (shadow_addr F + i) = Some (nth (Z.to_nat i) r13_shm1 0))
    by (intros i Hi; apply (bm_sh_read_all Ev W2 (ms_mem msx) r (shadow_addr F) r13_shm1);
        [ exact (st_ok_region_nth Ev ssx (restrict (w_H W2) msx) 5 r HS ltac:(vm_compute; reflexivity))
        | cbn [YP09.r_base base_val]; exact BS1
        | vm_compute; reflexivity
        | vm_compute (Z.of_nat (length r13_shm1)); lia ]);
    (* the cursor's two words, from the cursor region *)
    let rc := eval vm_compute in (nth 4 (ss_mem ssx) got_region) in
    let HR := fresh "HR" in
    pose proof (st_ok_region_nth Ev ssx (restrict (w_H W2) msx) 4 rc HS ltac:(vm_compute; reflexivity)) as HR;
    assert (VC184 : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msx)) (sp1 + 184) 8 (e_p g + c))
    by (apply (field_of_region Ev _ 2 sp1 _ 184 200 184 200 184 8 (SOff 35 0) (e_p g + c) HR);
        [ exact B21 | cbn [In]; left; reflexivity
        | cbn [sv_denot]; unfold E1; rewrite bm_ew_CP, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | unfold BM_HI in *; cbn; lia | cbn; lia ]);
    assert (VC192 : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msx)) (sp1 + 192) 8 (e_n g - c))
    by (apply (field_of_region Ev _ 2 sp1 _ 184 200 184 200 192 8 (SOff 36 0) (e_n g - c) HR);
        [ exact B21 | cbn [In]; right; left; reflexivity
        | cbn [sv_denot]; unfold E1; rewrite bm_ew_CN, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | cbn; lia | cbn; lia ]);
    clear HR end.
  pose proof (r13_bs_all W2 _ F Hf64 SH1) as (BST & BSB & BSD).
  lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssx (restrict _ ?msx) |- _ =>
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
    destruct (r13_ta_pre B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 kj c ly2 S2 W2 (ms_mem msx) _ kj HC HJ Hfr HJ1 Hfr HPerm0
      ltac:(lia) BST) as (TA1 & TA2 & TA3 & TA4 & TA5 & TA6 & TA7 & TA8 & TA9 & TA10 & TA11 & TA12 & TA13);
    eapply SRr_bind;
    [ eapply (CTA LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 (ms_mem msx)
        _ kj (ms_regs msx) (sp1 + 184) (F + 80) (e_p g + c)
        (skipn (Z.to_nat c) (map (fun b : byte => bv_unsigned b) (e_pl g))) (r13_cur W2 (ms_mem msx) (F + 80) 65))
    | ] end.
  - apply (cpw_entry B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 ly2 S2 W2
      (ms_mem ms0) _ kj (ms_regs ms0) TB_text_arg).
    + exact HJ1.
    + rewrite Rra. apply ret_ok_even. vm_compute. reflexivity.
    + unfold raZ. rewrite Rra, unsigned_lit_small by lia. lia.
    + rewrite Rgp, Z.add_0_r, Z_to_bv_bv_unsigned. unfold E1. rewrite (bm_ew_reg g pos c regs2 _ 3 3%bv eq_refl). exact R3.
    + rewrite Rtp, Z.add_0_r, Z_to_bv_bv_unsigned. unfold E1. rewrite (bm_ew_reg g pos c regs2 _ 4 4%bv eq_refl). exact R4.
    + rewrite Usp. pose proof (Z.div_mod sp1 32 ltac:(lia)) as D32. rewrite Hsp32, Z.add_0_r in D32.
      rewrite D32. replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by lia. apply Z_mod_mult.
    + rewrite Usp. unfold TB_text_arg. lia.
    + rewrite Usp. lia.
    + unfold EV_CDC. lia.
    + apply Permutation_refl.
    + rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HPerm0), <- (blocks_bytes_bsum B (e_ly g) (e_S g)).
      unfold LIVE_CDC, LIVE_LIB in *. lia.
  - rewrite Ra0, B21. reflexivity.
  - exact TA13.
  - rewrite Usp. exact TA1.
  - exact VC184.
  - rewrite TA2. replace (sp1 + 184 + 8) with (sp1 + 192) by lia. exact VC192.
  - exact TA3.
  - exact TA4.
  - exact TA5.
  - rewrite Usp. exact TA6.
  - rewrite Ra1, BF1. reflexivity.
  - rewrite Usp. exact TA7.
  - exact TA8.
  - exact TA9.
  - exact TA10.
  - exact TA11.
  - exact TA12.
  - (* the post of text_arg *)
    intros W4 c4 Hwle4 HP4.
    destruct HP4 as (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HPR4 & Hfr4 & HPerm4 & HIO4 & HMO4 & KT4 & Vip4 & Vin4 & Gtx4).
    rewrite Usp in KT4.
    unfold EV_CDC in HJ4. rewrite Z.add_0_r in HJ4.
    pose proof HJ4 as (HAR4 & _).
    assert (Hin4 : In (3, pos) (frames S4)) by (rewrite Hfr4, Hfr; left; reflexivity).
    assert (EFL4 : frame_addr ly4 3 pos = F) by exact (r13_efa B g pos ly4 S4 W4 mem4 md4 kj HJ4).
    destruct (al_frames _ _ LAWS ly4 S4 W4 mem4 md4 3 pos HAR4 Hin4) as (_ & _ & PF4 & PS4).
    rewrite EFL4 in PF4, PS4. change (fs_frame_bytes 3) with 512 in PF4. change (fs_frame_bytes 3 / 8) with 64 in PS4.
    assert (Hin2 : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
    assert (Hfsh : F + 512 <= shadow_addr F \/ shadow_addr F + 64 <= F).
    { unfold in_app in Happ. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
      destruct Happ as (_ & [Hlow | (Hh1 & Hh2)]); [left; lia|].
      right. assert (D4 : 2199291686912 <= F / 8) by (apply Z.div_le_lower_bound; lia). lia. }
    assert (Hshb : 2147450880 + 512 <= shadow_addr F <= 2147450880 + 2 ^ 44)
      by (unfold shadow_addr, SHADOW_OFF, SB, BM_HI in *; split; [assert (512 <= F / 8) by (apply Z.div_le_lower_bound; lia); lia
          | assert (F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia); lia]).
    lazymatch type of HS with YP0l.st_ok _ _ ?ssv _ =>
      let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ssv) in
      jafter_call_keep HS K regs4 (mrestrict (w_H W4) mem4) HPR4 [0; 1; 2; 3; 5; 6; 7]%nat HS2 end.
    match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
    { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
      all: r13_keep KT4 EFA Hin2 ltac:(let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_wlo YP09.r_whi] in Ha;
          first [ apply PF4; lia | replace a with (shadow_addr F + (a - shadow_addr F)) by lia; apply PS4; lia ])
        HJ1 HJ4.
    }
    specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
    rewrite Rra.
    (* the kept chain: Zj, from the join's memory *)
    set (Zj := fun a => r13_zone g pos sp1 a \/ (F + 200 <= a < F + 216)).
    assert (ZJF : forall a, Zj a -> (sp1 + 16 <= a < sp1 + 160) \/ (e_sp0 g - 104 <= a < e_sp0 g) \/ (F + 200 <= a < F + 220) \/
      (F + 224 <= a < F + 376) \/ (F + 504 <= a < F + 512)).
    { intros a Ha. unfold Zj, r13_zone, bm_keepzone in Ha. fold F in Ha. lia. }
    assert (KJ1 : forall a, Zj a -> aview tfibsegs (w_H W2) (ms_mem ms0) a = aview tfibsegs (w_H W2) (ms_mem ms) a).
    { eapply (r13_run_kept _ _ _ _ _ Zj HFr). intros a Ha. pose proof (ZJF a Ha) as Ha'.
      split; [lia|]. r13_nwr B21 BF1 BS1. }
    assert (KJ2 : forall a, Zj a -> aview tfibsegs (w_H W4) mem4 a = aview tfibsegs (w_H W2) (ms_mem ms) a).
    { intros a Ha. rewrite <- (KJ1 a Ha).
      apply (r13_call_kept B TB_text_arg ly2 S2 W2 (ms_mem ms0) W4 mem4 sp1 _ g pos Zj KT4 Hin2 EFA); [|exact Ha].
      intros x Hx. pose proof (ZJF x Hx) as Hx'. fold F.
      split; [|let HE := fresh "HE" in intros HE; cbv beta in HE; lia].
      destruct Hx' as [Hx' | [Hx' | Hx']]; [left; split; lia | left; split; lia | right; left; lia]. }
    clear HF HFr HG KJ1.
    (* 0x8131c jal check_text_seg7 *)
    lazymatch type of HS with YP0l.st_ok _ ?En _ _ => remember En as E2 eqn:HE2 in HS end.
    assert (B22 : bv_unsigned (ew E2 2) = sp1) by (rewrite HE2, ew_havoc_old by lia; exact B21).
    assert (BF2 : bv_unsigned (ew E2 33) = F) by (rewrite HE2, ew_havoc_old by lia; exact BF1).
    assert (BS2 : bv_unsigned (ew E2 34) = shadow_addr F) by (rewrite HE2, ew_havoc_old by lia; exact BS1).
    assert (G32 : ew E2 3 = getr regs2 3)
      by (rewrite HE2, ew_havoc_old by lia; unfold E1; exact (bm_ew_reg g pos c regs2 _ 3 3%bv eq_refl)).
    assert (G42 : ew E2 4 = getr regs2 4)
      by (rewrite HE2, ew_havoc_old by lia; unfold E1; exact (bm_ew_reg g pos c regs2 _ 4 4%bv eq_refl)).
    assert (HPermC4 : Permutation (ablocks B ly4 S4) (ablocks B (e_ly g) (e_S g))) by exact (Permutation_trans HPerm4 HPerm0).
    aj_run_to tfibtbl_lib_ok HS HJ4 0x84148.
    { r13_awr. }
    r13_reg HS (1%bv : bv 5) Rra2. r13_reg HS (2%bv : bv 5) Rsp2. r13_reg HS (3%bv : bv 5) Rgp2. r13_reg HS (4%bv : bv 5) Rtp2.
    lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssx (restrict _ ?msx) |- _ =>
      assert (Usp2 : spZ (ms_regs msx) = sp1)
        by (unfold spZ; rewrite Rsp2, B22, Z.add_0_r; apply unsigned_lit_small; unfold BM_HI in *; lia);
      rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
      eapply SRr_bind;
      [ eapply (CS7 LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly4 S4 W4 (ms_mem msx)
          _ kj (ms_regs msx))
      | ] end.
    + r13_entry B HJ4 Rra2 Rgp2 Rtp2 G32 G42 R3 R4 Usp2 Hsp32 TB_check_seg7 HPermC4.
    + rewrite Usp2. apply (r13_cimg_rd B); [exact TL | exact GM | exact IV | exact RF | |
        unfold TB_check_seg7, TB_owed_seg7, CB_RHI; lia].
      exact (arodata_ok_at B MT K XM_LIB g [(3, pos)] _ _ _ _ _ _ (proj1 HC) HJ4).
    + exact seg7_agree.
    + (* the post of check_text_seg7 *)
      intros W5 c5 Hwle5 HP5.
      destruct HP5 as (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HPR5 & Hfr5 & HPerm5 & HIO5 & HMO5 & KT5 & _).
      rewrite Usp2 in KT5. unfold EV_CDC in HJ5. rewrite Z.add_0_r in HJ5.
      pose proof HJ5 as (HAR5 & _).
      assert (Hin5 : In (3, pos) (frames S5)) by (rewrite Hfr5, Hfr4, Hfr; left; reflexivity).
      assert (EFL5 : frame_addr ly5 3 pos = F) by exact (r13_efa B g pos ly5 S5 W5 mem5 md5 kj HJ5).
      destruct (al_frames _ _ LAWS ly5 S5 W5 mem5 md5 3 pos HAR5 Hin5) as (_ & _ & PF5 & PS5).
      rewrite EFL5 in PF5, PS5. change (fs_frame_bytes 3) with 512 in PF5. change (fs_frame_bytes 3 / 8) with 64 in PS5.
      (* the run to the call kept every byte of the zones (no write window but the shadow byte 56 and k's two fields) *)
      lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem4) (mrestrict _ ?mB) |- _ =>
        assert (KJ3 : forall a, Zj a -> aview tfibsegs (w_H W4) mB a = aview tfibsegs (w_H W2) (ms_mem ms) a)
        by (intros a Ha; rewrite <- (KJ2 a Ha); revert a Ha; eapply (r13_run_kept _ _ _ _ _ Zj HFr);
            intros a Ha; pose proof (ZJF a Ha) as Ha'; split; [lia|]; r13_nwr B22 BF2 BS2);
        assert (KT3 : forall a, (F + 80 <= a < F + 145) \/ (sp1 + 184 <= a < sp1 + 200) ->
          aview tfibsegs (w_H W4) mB a = aview tfibsegs (w_H W4) mem4 a)
        by (eapply (r13_run_kept _ _ _ _ _ _ HFr); intros a Ha; split; [lia|]; r13_nwr B22 BF2 BS2) end.
      lazymatch type of HS with YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) =>
        let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ssv) in
        jafter_call_keep HS K regs5 (mrestrict (w_H W5) mem5) HPR5 [0; 1; 2; 3; 4; 5; 6]%nat HS2 end.
      match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
      { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
        all: r13_keep KT5 EFL4 Hin4 ltac:(let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
            cbn [YP09.r_wlo YP09.r_whi] in Ha;
            first [ apply PF5; lia | replace a with (shadow_addr F + (a - shadow_addr F)) by lia; apply PS5; lia ])
          HJ4 HJ5. }
      specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
      rewrite Rra2.
      (* the call kept the zones (it writes nothing outside its own window) *)
      lazymatch type of KT5 with tcj_kept _ _ _ _ _ _ ?mB _ _ _ _ =>
        assert (KJ4 : forall a, Zj a -> aview tfibsegs (w_H W5) mem5 a = aview tfibsegs (w_H W2) (ms_mem ms) a)
        by (intros a Ha; rewrite <- (KJ3 a Ha);
            apply (r13_call_kept B TB_check_seg7 ly4 S4 W4 mB W5 mem5 sp1 _ g pos Zj KT5 Hin4 EFL4); [|exact Ha];
            intros x Hx; pose proof (ZJF x Hx) as Hx'; fold F;
            split; [|let HE := fresh "HE" in intros HE; exact HE];
            destruct Hx' as [Hx' | [Hx' | Hx']]; [left; split; lia | left; split; lia | right; left; lia]);
        assert (KT4' : forall a, (F + 80 <= a < F + 145) \/ (sp1 + 184 <= a < sp1 + 200) ->
          aview tfibsegs (w_H W5) mem5 a = aview tfibsegs (w_H W4) mem4 a)
        by (intros a Ha; rewrite <- (KT3 a Ha);
            apply (r13_call_kept B TB_check_seg7 ly4 S4 W4 mB W5 mem5 sp1 _ g pos
              (fun x => (F + 80 <= x < F + 145) \/ (sp1 + 184 <= x < sp1 + 200)) KT5 Hin4 EFL4); [|exact Ha];
            intros x Hx; split; [|let HE := fresh "HE" in intros HE; exact HE];
            destruct Hx as [Hx | Hx]; [right; left; lia | left; split; lia]) end.
      clear KJ2 KJ3 KT3.
      (* 0x81320 mv a0,s6; ld s8,120(s1); mv a1,s8; mv a2,s9; jal check_text_counter *)
      lazymatch type of HS with YP0l.st_ok _ ?En _ _ => remember En as E3 eqn:HE3 in HS end.
      assert (B23 : bv_unsigned (ew E3 2) = sp1) by (rewrite HE3, ew_havoc_old by lia; exact B22).
      assert (BF3 : bv_unsigned (ew E3 33) = F) by (rewrite HE3, ew_havoc_old by lia; exact BF2).
      assert (BS3 : bv_unsigned (ew E3 34) = shadow_addr F) by (rewrite HE3, ew_havoc_old by lia; exact BS2).
      assert (G33 : ew E3 3 = getr regs2 3) by (rewrite HE3, ew_havoc_old by lia; exact G32).
      assert (G43 : ew E3 4 = getr regs2 4) by (rewrite HE3, ew_havoc_old by lia; exact G42).
      assert (HPermC5 : Permutation (ablocks B ly5 S5) (ablocks B (e_ly g) (e_S g))) by exact (Permutation_trans HPerm5 HPermC4).
      aj_run_to tfibtbl_lib_ok HS HJ5 0x841c4.
      { r13_awr. }
      lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem5) (mrestrict _ ?mB) |- _ =>
        assert (KJ5 : forall a, Zj a -> aview tfibsegs (w_H W5) mB a = aview tfibsegs (w_H W2) (ms_mem ms) a)
        by (intros a Ha; rewrite <- (KJ4 a Ha); revert a Ha; eapply (r13_run_kept _ _ _ _ _ Zj HFr);
            intros a Ha; pose proof (ZJF a Ha) as Ha'; split; [lia|]; r13_nwr B23 BF3 BS3);
        assert (KT5' : forall a, (F + 80 <= a < F + 145) \/ (sp1 + 184 <= a < sp1 + 200) ->
          aview tfibsegs (w_H W5) mB a = aview tfibsegs (w_H W4) mem4 a)
        by (intros a Ha; rewrite <- (KT4' a Ha); revert a Ha;
            eapply (r13_run_kept _ _ _ _ _ (fun x => (F + 80 <= x < F + 145) \/ (sp1 + 184 <= x < sp1 + 200)) HFr);
            intros a Ha; split; [lia|]; r13_nwr B23 BF3 BS3);
        clear HFr end.
      clear KJ4 KT4'.
      r13_reg HS (1%bv : bv 5) Rra3. r13_reg HS (2%bv : bv 5) Rsp3. r13_reg HS (3%bv : bv 5) Rgp3. r13_reg HS (4%bv : bv 5) Rtp3.
      r13_reg HS (10%bv : bv 5) Ra03. r13_reg HS (11%bv : bv 5) Ra13. r13_reg HS (12%bv : bv 5) Ra23.
      set (dat := skipn (Z.to_nat c) (map (fun b : byte => bv_unsigned b) (e_pl g))) in *.
      set (tb := text_takenZ dat ++ [0] ++ skipn (1 + text_lenZ dat) (r13_cur W2 (ms_mem ms0) (F + 80) 65)) in *.
      assert (Ltb : length tb = 65%nat) by (apply r13_tb_len; apply r13_cur_len; lia).
      pose proof Hkat as (KA & Kwf).
      pose proof KA as (_ & _ & _ & _ & _ & _ & _ & Gbytes & _).
      cbn [kz_bytes k_rdZ] in Gbytes. change (FA g pos) with F in Gbytes. replace (F + 192 + 40) with (F + 232) in Gbytes by lia.
      lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssx (restrict _ ?msx) |- _ =>
        assert (Usp3 : spZ (ms_regs msx) = sp1)
          by (unfold spZ; rewrite Rsp3, B23, Z.add_0_r; apply unsigned_lit_small; unfold BM_HI in *; lia);
        let r := eval vm_compute in (nth 4 (ss_mem ssx) got_region) in
        assert (SH3 : forall i, 0 <= i < 60 ->
          aview tfibsegs (w_H W5) (ms_mem msx) (shadow_addr F + i) = Some (nth (Z.to_nat i) r13_shm1 0))
        by (intros i Hi; apply (bm_sh_read_all Ev W5 (ms_mem msx) r (shadow_addr F) r13_shm1);
            [ exact (st_ok_region_nth Ev ssx (restrict (w_H W5) msx) 4 r HS ltac:(vm_compute; reflexivity))
            | cbn [YP09.r_base base_val]; exact BS3
            | vm_compute; reflexivity
            | vm_compute (Z.of_nat (length r13_shm1)); lia ]);
        assert (Gtb : garr8 tfibsegs (mrestrict (w_H W5) (ms_mem msx)) (F + 80) tb)
          by (apply (bm_garr8_kept_x (w_H W4) (w_H W5) mem4 (ms_mem msx)); [|exact Gtx4];
              intros x Hx; rewrite Ltb in Hx; apply KT5'; left; cbn in Hx; lia);
        assert (Gsj : garr8 tfibsegs (mrestrict (w_H W5) (ms_mem msx)) (F + 232) (repeat 0 24))
          by (apply (bm_garr8_kept_x (w_H W2) (w_H W5) mem2 (ms_mem msx)); [|exact Gbytes];
              intros x Hx; rewrite repeat_length in Hx;
              assert (Zx : r13_zone g pos sp1 x) by (right; right; fold F; cbn in Hx; lia);
              rewrite (KJ5 x (or_introl Zx)); exact (KZ x Zx));
        pose proof HJ5 as (HAR5c & _);
        destruct (al_frames _ _ LAWS ly5 S5 W5 (ms_mem msx) _ 3 pos HAR5c Hin5) as (_ & _ & PF5c & _);
        rewrite EFL5 in PF5c; change (fs_frame_bytes 3) with 512 in PF5c;
        destruct (aview tfibsegs (w_H W5) (ms_mem msx) (F + 448)) as [dj|] eqn:Edj;
          [| exfalso; exact (aview_some_of_apresent tfibsegs _ _ _ (proj1 (PF5c (F + 448) ltac:(lia))) Edj)];
        pose proof (r13_bs_all W5 _ F Hf64 SH3) as (BST3 & BSB3 & BSD3);
        rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
        eapply SRr_bind;
        [ eapply (CTC LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly5 S5 W5 (ms_mem msx)
            _ kj (ms_regs msx) (F + 80) (F + 232) (F + 448) tb (repeat 0 24) dj)
        | ] end.
      * r13_entry B HJ5 Rra3 Rgp3 Rtp3 G33 G43 R3 R4 Usp3 Hsp32 TB_check_text_counter HPermC5.
      * rewrite Ra03, BF3. reflexivity.
      * rewrite Usp3. split; [lia|]. split; [exact Gtb|]. split; [unfold tb; apply in_or_app; right; left; reflexivity|].
        rewrite Ltb. change (Z.of_nat 65) with 65.
        apply (satU_main_text_rd tfibsegs B LAWS ly5 S5 W5 _ _ sp1 TB_check_text_counter pos F LLVMF_STK (e_sp0 g)
          HAR5c Hin5 EFL5 Hf64 BST3); unfold TB_check_text_counter; change ESTACK with 4096; lia.
      * rewrite Ltb. eapply sat_main_cobj; [exact Hin5 | exact EFL5 | lia | lia].
      * eapply sat_main_cobj; [exact Hin5 | exact EFL5 | lia | lia].
      * eapply sat_main_cobj; [exact Hin5 | exact EFL5 | lia | lia].
      * rewrite Ra13, BF3. reflexivity.
      * rewrite Usp3. eapply (sat_frame_dst tfibsegs B LAWS); [exact HJ5 | left; reflexivity | exact Hin5 | exact EFL5 | exact Hf64
          | vm_compute; reflexivity | lia | lia | change (fs_frame_bytes 3) with 512; lia | exact BSB3
          | unfold TB_check_text_counter; change ESTACK with 4096; lia
          | unfold TB_check_text_counter; change ESTACK with 4096; lia | change ESTACK with 4096; lia ].
      * exact Gsj.
      * reflexivity.
      * rewrite Ra23, BF3. reflexivity.
      * rewrite Usp3. eapply (satU_main_dots_dst tfibsegs B LAWS); [exact HJ5 | left; reflexivity | exact Hin5 | exact EFL5 | exact Hf64 | exact BSD3
          | unfold TB_check_text_counter; change ESTACK with 4096; lia
          | unfold TB_check_text_counter; change ESTACK with 4096; lia | change ESTACK with 4096; lia ].
      * apply val_mem1_of_aviewA. exact Edj.
      * lia.
      * rewrite Ltb. change (Z.of_nat 65) with 65. lia.
      * rewrite Ltb. change (Z.of_nat 65) with 65. lia.
      * rewrite Usp3. apply (r13_cimg_rd B); [exact TL | exact GM | exact IV | exact RF | |
          unfold TB_check_text_counter, CB_RHI; change ESTACK with 4096; lia].
        exact (arodata_ok_at B MT K XM_LIB g [(3, pos)] _ _ _ _ _ _ (proj1 HC) HJ5).
      * rewrite (counter_text_agree tb (garr8_bytes_ok tfibsegs _ _ _ Gtb)).
        destruct (owed_counter_text_spec tb) as [[r1 s1] d1]. split; [reflexivity | intros _; split; reflexivity].
      * rewrite Hfr5, Hfr4, Hfr. cbn. lia.
      * (* the post of check_text_counter *)
        intros W6 c6 Hwle6 HP6.
        destruct HP6 as (ly6 & S6 & regs6 & mem6 & md6 & -> & HJ6 & HPR6 & Hfr6 & HPerm6 & HIO6 & HMO6 & KT6 & (s1 & d1 & Gsg6 & Ls1 & Vdt6)).
        lazymatch type of KT6 with tcj_kept _ _ _ _ _ _ ?mB _ _ _ _ => set (mC := mB) in * end.
        rewrite Usp3 in KT6. unfold EV_CDC in HJ6. rewrite Z.add_0_r in HJ6.
        pose proof HJ6 as (HAR6 & _).
        assert (Hin6 : In (3, pos) (frames S6)) by (rewrite Hfr6, Hfr5, Hfr4, Hfr; left; reflexivity).
        assert (EFL6 : frame_addr ly6 3 pos = F) by exact (r13_efa B g pos ly6 S6 W6 mem6 md6 kj HJ6).
        destruct (al_frames _ _ LAWS ly6 S6 W6 mem6 md6 3 pos HAR6 Hin6) as (_ & _ & PF6 & PS6).
        rewrite EFL6 in PF6, PS6. change (fs_frame_bytes 3) with 512 in PF6. change (fs_frame_bytes 3 / 8) with 64 in PS6.
        lazymatch type of HS with YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) =>
          let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ssv) in
          jafter_call_keep HS K regs6 (mrestrict (w_H W6) mem6) HPR6 [0; 1; 2; 3; 4; 5; 6]%nat HS2 end.
        match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
        { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
          all: r13_keep KT6 EFL5 Hin5 ltac:(let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
              cbn [YP09.r_wlo YP09.r_whi] in Ha;
              first [ apply PF6; lia | replace a with (shadow_addr F + (a - shadow_addr F)) by lia; apply PS6; lia ])
            HJ5 HJ6. }
        specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
        rewrite Rra3.
        (* the call kept the zones off k.bytes and the dots byte *)
        set (Zj2 := fun a => Zj a /\ ~ (F + 232 <= a < F + 256)).
        assert (KJ6 : forall a, Zj2 a -> aview tfibsegs (w_H W6) mem6 a = aview tfibsegs (w_H W2) (ms_mem ms) a).
        { intros a Ha. rewrite <- (KJ5 a (proj1 Ha)).
          apply (r13_call_kept B TB_check_text_counter ly5 S5 W5 mC W6 mem6 sp1 _ g pos Zj2 KT6 Hin5 EFL5); [|exact Ha].
          intros x (Hx & Hnb). pose proof (ZJF x Hx) as Hx'. fold F.
          split; [|let HE := fresh "HE" in intros HE; cbv beta in HE; lia].
          destruct Hx' as [Hx' | [Hx' | Hx']]; [left; split; lia | left; split; lia | right; left; lia]. }
        assert (KT6' : forall a, (F + 80 <= a < F + 145) \/ (sp1 + 184 <= a < sp1 + 200) ->
          aview tfibsegs (w_H W6) mem6 a = aview tfibsegs (w_H W4) mem4 a).
        { intros a Ha. rewrite <- (KT5' a Ha).
          apply (r13_call_kept B TB_check_text_counter ly5 S5 W5 mC W6 mem6 sp1 _ g pos
            (fun x => (F + 80 <= x < F + 145) \/ (sp1 + 184 <= x < sp1 + 200)) KT6 Hin5 EFL5); [|exact Ha].
          intros x Hx. split; [|let HE := fresh "HE" in intros HE; cbv beta in HE; lia].
          destruct Hx as [Hx | Hx]; [right; left; lia | left; split; lia]. }
        clear KJ5 KT5'.
        (* 0x81334 mv a0,s6; mv a1,s8; mv a2,s9; jal owed_counter_text *)
        lazymatch type of HS with YP0l.st_ok _ ?En _ _ => remember En as E4 eqn:HE4 in HS end.
        assert (B24 : bv_unsigned (ew E4 2) = sp1) by (rewrite HE4, ew_havoc_old by lia; exact B23).
        assert (BF4 : bv_unsigned (ew E4 33) = F) by (rewrite HE4, ew_havoc_old by lia; exact BF3).
        assert (BS4 : bv_unsigned (ew E4 34) = shadow_addr F) by (rewrite HE4, ew_havoc_old by lia; exact BS3).
        assert (G34 : ew E4 3 = getr regs2 3) by (rewrite HE4, ew_havoc_old by lia; exact G33).
        assert (G44 : ew E4 4 = getr regs2 4) by (rewrite HE4, ew_havoc_old by lia; exact G43).
        assert (HPermC6 : Permutation (ablocks B ly6 S6) (ablocks B (e_ly g) (e_S g))) by exact (Permutation_trans HPerm6 HPermC5).
        aj_run_to tfibtbl_lib_ok HS HJ6 0x84474.
        { r13_awr. }
        lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem6) (mrestrict _ ?mB) |- _ =>
          assert (KJ7 : forall a, Zj2 a -> aview tfibsegs (w_H W6) mB a = aview tfibsegs (w_H W2) (ms_mem ms) a)
          by (intros a Ha; rewrite <- (KJ6 a Ha); revert a Ha; eapply (r13_run_kept _ _ _ _ _ Zj2 HFr);
              intros a Ha; pose proof (ZJF a (proj1 Ha)) as Ha'; split; [lia|]; r13_nwr B24 BF4 BS4);
          assert (KT7 : forall a, (F + 80 <= a < F + 145) \/ (sp1 + 184 <= a < sp1 + 200) \/ (F + 232 <= a < F + 256) \/
            (F + 448 <= a < F + 449) -> aview tfibsegs (w_H W6) mB a = aview tfibsegs (w_H W6) mem6 a)
          by (eapply (r13_run_kept _ _ _ _ _ _ HFr); intros a Ha; split; [lia|]; r13_nwr B24 BF4 BS4);
          clear HFr end.
        clear KJ6.
        r13_reg HS (1%bv : bv 5) Rra4. r13_reg HS (2%bv : bv 5) Rsp4. r13_reg HS (3%bv : bv 5) Rgp4. r13_reg HS (4%bv : bv 5) Rtp4.
        r13_reg HS (10%bv : bv 5) Ra04. r13_reg HS (11%bv : bv 5) Ra14. r13_reg HS (12%bv : bv 5) Ra24.
        apply garr8_app in Gsg6 as (Gs1 & G16). rewrite Ls1 in G16.
        lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssx (restrict _ ?msx) |- _ =>
          assert (Usp4 : spZ (ms_regs msx) = sp1)
            by (unfold spZ; rewrite Rsp4, B24, Z.add_0_r; apply unsigned_lit_small; unfold BM_HI in *; lia);
          let r := eval vm_compute in (nth 4 (ss_mem ssx) got_region) in
          assert (SH4 : forall i, 0 <= i < 60 ->
            aview tfibsegs (w_H W6) (ms_mem msx) (shadow_addr F + i) = Some (nth (Z.to_nat i) r13_shm1 0))
          by (intros i Hi; apply (bm_sh_read_all Ev W6 (ms_mem msx) r (shadow_addr F) r13_shm1);
              [ exact (st_ok_region_nth Ev ssx (restrict (w_H W6) msx) 4 r HS ltac:(vm_compute; reflexivity))
              | cbn [YP09.r_base base_val]; exact BS4
              | vm_compute; reflexivity
              | vm_compute (Z.of_nat (length r13_shm1)); lia ]);
          assert (Gtb7 : garr8 tfibsegs (mrestrict (w_H W6) (ms_mem msx)) (F + 80) tb)
            by (apply (bm_garr8_kept_x (w_H W4) (w_H W6) mem4 (ms_mem msx)); [|exact Gtx4];
                intros x Hx; rewrite Ltb in Hx; rewrite (KT7 x ltac:(left; cbn in Hx; lia)); apply KT6'; left; cbn in Hx; lia);
          assert (Gs17 : garr8 tfibsegs (mrestrict (w_H W6) (ms_mem msx)) (F + 232) s1)
            by (apply (bm_garr8_kept_x (w_H W6) (w_H W6) mem6 (ms_mem msx)); [|exact Gs1];
                intros x Hx; rewrite Ls1 in Hx; apply KT7; right; right; left; cbn in Hx; lia);
          assert (Vdt7 : val_mem tfibsegs (mrestrict (w_H W6) (ms_mem msx)) (F + 448) 1 d1)
            by (apply (cw_val_mem_kept (w_H W6) (w_H W6) mem6 (ms_mem msx)); [|exact Vdt6];
                intros x Hx; apply KT7; right; right; right; cbn in Hx; lia);
          pose proof HJ6 as (HAR6c & _);
          pose proof (r13_bs_all W6 _ F Hf64 SH4) as (BST4 & BSB4 & BSD4);
          rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
          eapply SRr_bind;
          [ eapply (COC LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly6 S6 W6 (ms_mem msx)
              _ kj (ms_regs msx) (F + 80) (F + 232) (F + 448) tb s1 d1)
          | ] end.
        -- r13_entry B HJ6 Rra4 Rgp4 Rtp4 G34 G44 R3 R4 Usp4 Hsp32 TB_owed_counter_text HPermC6.
        -- rewrite Ra04, BF4. reflexivity.
        -- rewrite Usp4. split; [lia|]. split; [exact Gtb7|]. split; [unfold tb; apply in_or_app; right; left; reflexivity|].
           rewrite Ltb. change (Z.of_nat 65) with 65.
           apply (satU_main_text_rd tfibsegs B LAWS ly6 S6 W6 _ _ sp1 TB_owed_counter_text pos F LLVMF_STK (e_sp0 g)
             HAR6c Hin6 EFL6 Hf64 BST4); unfold TB_owed_counter_text; change ESTACK with 4096; lia.
        -- rewrite Ltb. eapply sat_main_cobj; [exact Hin6 | exact EFL6 | lia | lia].
        -- eapply sat_main_cobj; [exact Hin6 | exact EFL6 | lia | lia].
        -- rewrite Ra14, BF4. reflexivity.
        -- rewrite Usp4. eapply (sat_frame_dst_in tfibsegs B LAWS) with (boff := 232) (bn := 24);
             [exact HJ6 | left; reflexivity | exact Hin6 | exact EFL6 | exact Hf64 | vm_compute; reflexivity | lia | lia | lia | lia
             | change (fs_frame_bytes 3) with 512; lia | exact BSB4
             | unfold TB_owed_counter_text; change ESTACK with 4096; lia
             | unfold TB_owed_counter_text; change ESTACK with 4096; lia | change ESTACK with 4096; lia ].
        -- exact Gs17.
        -- exact Ls1.
        -- rewrite Ra24, BF4. reflexivity.
        -- left. split.
           ++ rewrite Usp4. eapply (satU_main_dots_dst tfibsegs B LAWS); [exact HJ6 | left; reflexivity | exact Hin6 | exact EFL6 | exact Hf64
                | exact BSD4 | unfold TB_owed_counter_text; change ESTACK with 4096; lia
                | unfold TB_owed_counter_text; change ESTACK with 4096; lia | change ESTACK with 4096; lia ].
           ++ eapply sat_main_cobj; [exact Hin6 | exact EFL6 | lia | lia].
        -- exact Vdt7.
        -- lia.
        -- rewrite Ltb. change (Z.of_nat 65) with 65. lia.
        -- rewrite Ltb. change (Z.of_nat 65) with 65. lia.
        -- rewrite Usp4. apply (r13_cimg_rd2 B); [exact TL | exact GM | exact IV | exact RF | |
             unfold TB_owed_counter_text, CB_RHI; change ESTACK with 4096; lia].
           exact (arodata_ok_at B MT K XM_LIB g [(3, pos)] _ _ _ _ _ _ (proj1 HC) HJ6).
        -- rewrite Hfr6, Hfr5, Hfr4, Hfr. cbn. lia.
        -- (* the post of owed_counter_text *)
           intros W7 c7 Hwle7 HP7.
           destruct HP7 as (ly7 & S7 & regs7 & mem7 & md7 & -> & HJ7 & HPR7 & Hfr7 & HPerm7 & HIO7 & HMO7 & KT7o & HR7).
           lazymatch type of KT7o with tcj_kept _ _ _ _ _ _ ?mB _ _ _ _ => set (mD := mB) in * end.
           rewrite Usp4 in KT7o. unfold EV_CDC in HJ7. rewrite Z.add_0_r in HJ7.
           pose proof HJ7 as (HAR7 & _).
           assert (Hin7 : In (3, pos) (frames S7)) by (rewrite Hfr7, Hfr6, Hfr5, Hfr4, Hfr; left; reflexivity).
           assert (Hfr7' : frames S7 = [(3, pos)]) by (rewrite Hfr7, Hfr6, Hfr5, Hfr4, Hfr; reflexivity).
           assert (EFL7 : frame_addr ly7 3 pos = F) by exact (r13_efa B g pos ly7 S7 W7 mem7 md7 kj HJ7).
           destruct (al_frames _ _ LAWS ly7 S7 W7 mem7 md7 3 pos HAR7 Hin7) as (_ & _ & PF7 & PS7).
           rewrite EFL7 in PF7, PS7. change (fs_frame_bytes 3) with 512 in PF7. change (fs_frame_bytes 3 / 8) with 64 in PS7.
           lazymatch type of HS with YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) =>
             let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ssv) in
             jafter_call_keep HS K regs7 (mrestrict (w_H W7) mem7) HPR7 [0; 1; 2; 3; 4; 5; 6]%nat HS2 end.
           match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
           { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
             all: r13_keep KT7o EFL6 Hin6 ltac:(let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
                 cbn [YP09.r_wlo YP09.r_whi] in Ha;
                 first [ apply PF7; lia | replace a with (shadow_addr F + (a - shadow_addr F)) by lia; apply PS7; lia ])
               HJ6 HJ7. }
           specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
           rewrite Rra4.
           (* what the call kept: the zones, the cursor, the 16 bytes after the digits *)
           assert (KJ8 : forall a, Zj2 a -> aview tfibsegs (w_H W7) mem7 a = aview tfibsegs (w_H W2) (ms_mem ms) a).
           { intros a Ha. rewrite <- (KJ7 a Ha).
             apply (r13_call_kept B TB_owed_counter_text ly6 S6 W6 mD W7 mem7 sp1 _ g pos Zj2 KT7o Hin6 EFL6); [|exact Ha].
             intros x (Hx & Hnb). pose proof (ZJF x Hx) as Hx'. fold F.
             split; [|let HE := fresh "HE" in intros HE; cbv beta in HE; lia].
             destruct Hx' as [Hx' | [Hx' | Hx']]; [left; split; lia | left; split; lia | right; left; lia]. }
           assert (KT8 : forall a, (sp1 + 184 <= a < sp1 + 200) \/ (F + 240 <= a < F + 256) ->
             aview tfibsegs (w_H W7) mem7 a = aview tfibsegs (w_H W6) mem6 a).
           { intros a Ha. rewrite <- (KT7 a ltac:(destruct Ha; [right; left | right; right; left]; lia)).
             apply (r13_call_kept B TB_owed_counter_text ly6 S6 W6 mD W7 mem7 sp1 _ g pos
               (fun x => (sp1 + 184 <= x < sp1 + 200) \/ (F + 240 <= x < F + 256)) KT7o Hin6 EFL6); [|exact Ha].
             intros x Hx. split; [|let HE := fresh "HE" in intros HE; cbv beta in HE; lia].
             destruct Hx as [Hx | Hx]; [left; split; lia | right; left; lia]. }
           assert (Vip8 : val_mem tfibsegs (mrestrict (w_H W7) mem7) (sp1 + 184) 8 (e_p g + c + Z.of_nat (text_usedZ dat))).
           { apply (cw_val_mem_kept (w_H W4) (w_H W7) mem4 mem7); [|exact Vip4]. intros x Hx. cbn in Hx.
             rewrite (KT8 x ltac:(left; lia)). apply KT6'. right. lia. }
           assert (Vin8 : val_mem tfibsegs (mrestrict (w_H W7) mem7) (sp1 + 192) 8 (Z.of_nat (length dat - text_usedZ dat))).
           { replace (sp1 + 192) with (sp1 + 184 + 8) by lia.
             apply (cw_val_mem_kept (w_H W4) (w_H W7) mem4 mem7); [|exact Vin4]. intros x Hx. cbn in Hx.
             rewrite (KT8 x ltac:(left; lia)). apply KT6'. right. lia. }
           assert (G168 : garr8 tfibsegs (mrestrict (w_H W7) mem7) (F + 232 + 8) (repeat 0xa5 16)).
           { apply (bm_garr8_kept_x (w_H W6) (w_H W7) mem6 mem7); [|exact G16].
             intros x Hx. rewrite repeat_length in Hx. cbn in Hx. apply KT8. right. lia. }
           clear KJ7 KT7 KT6'.
           assert (HPermC7 : Permutation (ablocks B ly7 S7) (ablocks B (e_ly g) (e_S g))) by exact (Permutation_trans HPerm7 HPermC6).
           assert (HMO7' : mo_le MT (e_S g) S7 0).
           { pose proof (mle_station MT _ _ _ 0 0 MTL HMO HMO4) as M4.
             pose proof (mle_station MT _ _ _ _ 0 MTL M4 HMO5) as M5.
             pose proof (mle_station MT _ _ _ _ 0 MTL M5 HMO6) as M6.
             pose proof (mle_station MT _ _ _ _ 0 MTL M6 HMO7) as M7. exact M7. }
           (* owed_counter_text's answer *)
           revert HR7. destruct (owed_counter_text_spec tb) as [[ro so] dd] eqn:EOC. intros (HA0 & HOK & HNO).
           lazymatch type of HS with YP0l.st_ok _ ?En _ _ => remember En as E5 eqn:HE5 in HS end.
           assert (B25 : bv_unsigned (ew E5 2) = sp1) by (rewrite HE5, ew_havoc_old by lia; exact B24).
           assert (BF5 : bv_unsigned (ew E5 33) = F) by (rewrite HE5, ew_havoc_old by lia; exact BF4).
           assert (BS5 : bv_unsigned (ew E5 34) = shadow_addr F) by (rewrite HE5, ew_havoc_old by lia; exact BS4).
           assert (HAE5 : env_agree 35 (bm_env g pos c regs2 [dv; y1; y10; y11; y12]) E5).
           { rewrite HE5, HE4, HE3, HE2. repeat (apply env_agree_havoc_ge; [lia|]). apply env_agree_refl. }
           assert (E20 : ew E5 20 = getr regs2 20).
           { rewrite HE5, HE4, HE3, HE2, !ew_havoc_old by lia. unfold E1. exact (bm_ew_reg g pos c regs2 _ 20 20%bv eq_refl). }
           lazymatch type of HS with YP0l.st_ok _ ?Ev ?ssx (restrict ?Hh ?msx) =>
             let e := eval vm_compute in (sr_get (ss_regs ssx) (10%bv : bv 5)) in
             pose proof (st_ok_restrict_reg tfibsegs Hh Ev ssx msx (10%bv : bv 5) HS) as RA0;
             change (sr_get (ss_regs ssx) (10%bv : bv 5)) with e in RA0 end.
           lazymatch type of RA0 with _ = ?rhs =>
             let RA1 := fresh "RA1" in assert (RA1 : w64 ro = rhs) by (rewrite <- HA0; exact RA0); clear RA0; rename RA1 into RA0 end.
           pose proof (r13_owed_rc tb ro so dd EOC) as Hro.
           assert (Hused : (text_usedZ dat <= length dat)%nat) by (unfold text_usedZ, text_lenZ, text_hdrZ; lia).
           (* 0x81344 beqz a0,0x81664 *)
           srr_branch_sh tfibtbl_lib_ok HS.
           all: lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hcond end.
           all: rewrite branch_eq_U in Hcond; unfold U in Hcond; rewrite <- RA0 in Hcond.
           all: destruct Hro as [Hro | Hro]; rewrite Hro in Hcond; try (vm_compute in Hcond; discriminate Hcond).
           2: { (* a0 = E_RANGE: 0x81348 the dots byte's shadow back to f8, to LATCH *)
             aj_run_to tfibtbl_lib_ok HS HJ7 0x82df4.
             { r13_awr. }
             lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem7) (mrestrict _ ?mB) |- _ =>
               assert (KF : forall a, Zj2 a \/ (sp1 + 184 <= a < sp1 + 200) ->
                 aview tfibsegs (w_H W7) mB a = aview tfibsegs (w_H W7) mem7 a)
               by (eapply (r13_run_kept _ _ _ _ _ _ HFr); intros a Ha;
                   destruct Ha as [Ha | Ha];
                   [ pose proof (ZJF a (proj1 Ha)) as Ha'; destruct Ha as (_ & Hnb) | ];
                   split; try lia; r13_nwr B25 BF5 BS5);
               clear HFr end.
             r13_shape W7 HS PC_LATCH.
             apply SRr_ret. right. unfold inv_latch.
             eapply bm_mcut; [exact HJ7 | exact Hfr7' | lia | exact HMO7' | | ].
             - eapply (bm_exit B MT K XM_LIB LAWS); [exact HC | exact HJ7 | exact HAE5 | exact HS | vm_compute; reflexivity | | | exact HPermC7].
               + intros a Ha.
                 assert (Hz : Zj2 a) by (split; [left; left; exact Ha | unfold bm_keepzone in Ha; fold F in Ha; lia]).
                 rewrite (KF a (or_introl Hz)), (KJ8 a Hz). exact (KZ a (or_introl Ha)).
               + r13_shadow W7 HS 4%nat BS5.
             - split; [split; [exact Hops | r13_ops HS E20 R20] |].
               exists (c + Z.of_nat (text_usedZ dat)). unfold cur_at. split; [lia|]. split.
               + apply (cw_val_mem_kept (w_H W7) (w_H W7) mem7 _); [intros x Hx; apply KF; right; cbn in Hx; lia|].
                 replace (e_p g + (c + Z.of_nat (text_usedZ dat))) with (e_p g + c + Z.of_nat (text_usedZ dat)) by lia.
                 exact Vip8.
               + apply (cw_val_mem_kept (w_H W7) (w_H W7) mem7 _); [intros x Hx; apply KF; right; cbn in Hx; lia|].
                 replace (e_n g - (c + Z.of_nat (text_usedZ dat))) with (Z.of_nat (length dat - text_usedZ dat)) by lia.
                 exact Vin8. }
           { (* a0 = 0: 0x81664 lbu a0,0(s9) the dots byte, k.kind = 10, k.b = dots, its shadow back to f8, to ENC10 *)
           destruct (HOK Hro) as (Gso & Vdd).
           rewrite Hro in EOC.
           pose proof (reader_ok_13 tb so dd EOC) as RO13.
           pose proof RO13 as (_ & Hdd32 & _ & _ & Lcb & _ & _ & _ & Hdd8 & _).
           specialize (Hdd8 eq_refl). unfold counter_bytes in Lcb. rewrite length_app, repeat_length in Lcb.
           assert (Lso : length so = 8%nat) by lia.
           (* the dots byte as a new atom N of the environment, read through a region of the frame *)
           lazymatch type of HS with YP0l.st_ok _ ?Ev ?ssx (restrict ?Hh ?msx) =>
             let N := eval vm_compute in (run_K 0 (SOff 32 0) [] ssx) in
             pose proof (st_ok_agree tfibsegs N Ev (havoc Ev N [Z_to_bv 64 dd]) ssx _ HS
               (env_agree_havoc_ge N N Ev Ev [Z_to_bv 64 dd] (le_n N) (env_agree_refl N Ev))
               ltac:(vm_compute; reflexivity)) as HS1;
             pose proof (env_agree_havoc_ge 35 N _ Ev [Z_to_bv 64 dd] ltac:(lia) HAE5) as HAE6;
             pose proof (ew_havoc_new Ev N [Z_to_bv 64 dd] 0 (Z_to_bv 64 0) ltac:(cbn; lia)) as EN;
             rewrite Nat.add_0_r in EN; cbn [nth] in EN;
             clear HS; rename HS1 into HS;
             remember (havoc Ev N [Z_to_bv 64 dd]) as E6 eqn:HE6;
             assert (B26 : bv_unsigned (ew E6 2) = sp1) by (rewrite HE6, ew_havoc_old by lia; exact B25);
             assert (BF6 : bv_unsigned (ew E6 33) = F) by (rewrite HE6, ew_havoc_old by lia; exact BF5);
             assert (BS6 : bv_unsigned (ew E6 34) = shadow_addr F) by (rewrite HE6, ew_havoc_old by lia; exact BS5);
             assert (E206 : ew E6 20 = getr regs2 20) by (rewrite HE6, ew_havoc_old by lia; exact E20);
             assert (DN : sv_denot E6 (SOff N 0) = Z_to_bv 64 dd)
               by (rewrite (bm_den_off E6 N dd 0 EN ltac:(lia) ltac:(lia)), Z.add_0_r; reflexivity);
             let HS2 := fresh "HS2" in
             pose proof (YP03.st_ok_add_fact tfibsegs E6 ssx (restrict Hh msx) N (mkAF 0 255 0) HS
               ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EN, unsigned_lit_small by lia;
                     rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia)) as HS2;
             clear HS; rename HS2 into HS;
             set (r_dots := YP09.mkRegion (Some 33%nat) 448 449 0 0 [YP09.mkChunk 448 (CVal 1 (SOff N 0))]) end.
           assert (IG : forall a, A_GOT_shadow <= a < A_GOT_shadow + 8 -> in_img tfibsegs a)
             by (intros a Ha; unfold A_GOT_shadow in Ha; apply YD1y.in_img_hull; lia).
           assert (IC : forall a, A_shadow_glob <= a < A_shadow_glob + 8 -> in_img tfibsegs a)
             by (intros a Ha; unfold A_shadow_glob in Ha; apply YD1y.in_img_hull; lia).
           pose proof (r13_frame_apart B LAWS _ _ _ _ _ pos F A_GOT_shadow 8 448 449 HAR7 Hin7 EFL7 ltac:(lia) IG
             ltac:(lia) ltac:(lia) ltac:(lia)) as AG1.
           pose proof (r13_frame_apart B LAWS _ _ _ _ _ pos F A_shadow_glob 8 448 449 HAR7 Hin7 EFL7 ltac:(lia) IC
             ltac:(lia) ltac:(lia) ltac:(lia)) as AG2.
           unfold A_GOT_shadow, A_shadow_glob in AG1, AG2.
           lazymatch type of HS with YP0l.st_ok _ ?Ev ?ssx (restrict ?Hh ?msx) =>
             let HS2 := fresh "HS2" in
             pose proof (ast_ok_add_region tfibsegs Ev ssx (restrict Hh msx) r_dots HS eq_refl
               ltac:(unfold region_ok, r_dots; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
                     rewrite BF6; split; [lia|]; split; [unfold BM_HI in *; lia|]; split; [intros o Ho; lia|];
                     apply Forall_cons; [|apply Forall_nil];
                     apply (chunk_ok_val tfibsegs Ev _ F 448 1 (SOff _ 0) dd DN ltac:(cbn; lia) ltac:(lia));
                     cbn [ms_mem restrict]; exact Vdd)
               ltac:(unfold r_dots;
                     let rs := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with rs;
                     cbn [all_disjoint]; unfold extent_disjoint;
                     cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?B26, ?BF6, ?BS6;
                     unfold shadow_addr, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, BM_HI in *;
                     repeat split; lia)) as HS2;
             clear HS; rename HS2 into HS end.
           aj_run_to tfibtbl_lib_ok HS HJ7 0x8274c.
           { r13_awr. }
           lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem7) (mrestrict _ ?mB) |- _ =>
             assert (KF : forall a, Zj2 a \/ (sp1 + 184 <= a < sp1 + 200) \/ (F + 232 <= a < F + 256) ->
               aview tfibsegs (w_H W7) mB a = aview tfibsegs (w_H W7) mem7 a)
             by (eapply (r13_run_kept _ _ _ _ _ _ HFr); intros a Ha;
                 destruct Ha as [Ha | Ha];
                 [ pose proof (ZJF a (proj1 Ha)) as Ha'; destruct Ha as (_ & Hnb) | ];
                 split; try lia; r13_nwr B26 BF6 BS6);
             clear HFr end.
           r13_shape W7 HS (enc_pc 10).
           apply SRr_ret. left. unfold inv_enc.
           eapply bm_mcut; [exact HJ7 | exact Hfr7' | lia | exact HMO7' | | ].
           - eapply (bm_exit B MT K XM_LIB LAWS); [exact HC | exact HJ7 | exact HAE6 | exact HS | vm_compute; reflexivity | | | exact HPermC7].
             + intros a Ha.
               assert (Hz : Zj2 a) by (split; [left; left; exact Ha | unfold bm_keepzone in Ha; fold F in Ha; lia]).
               rewrite (KF a (or_introl Hz)), (KJ8 a Hz). exact (KZ a (or_introl Ha)).
             + r13_shadow W7 HS 5%nat BS6.
           - split; [split; [exact Hops | r13_ops HS E206 R20] |]. split; [lia|].
             exists (c + Z.of_nat (text_usedZ dat)),
               (mkKcallZ 10 pv' dv' 0 dd 0 0 (so ++ repeat 0xa5 16) 0 0 fa5 fa5 0 (repeat 0 24) 0 0 0), (Some d').
             assert (Hpd'r : 0 <= pv' < 2 ^ 64 /\ 0 <= dv' < 2 ^ 64)
               by (destruct Hpd' as [(-> & -> & _) | [(-> & -> & _) | (-> & -> & _)]]; unfold CB_PERS, CM_SPEC_C24, CM_SPEC_PC; lia).
             split; [|split; [|split]].
             + unfold cur_at. split; [lia|]. split.
               * apply (cw_val_mem_kept (w_H W7) (w_H W7) mem7 _); [intros x Hx; apply KF; right; left; cbn in Hx; lia|].
                 replace (e_p g + (c + Z.of_nat (text_usedZ dat))) with (e_p g + c + Z.of_nat (text_usedZ dat)) by lia.
                 exact Vip8.
               * apply (cw_val_mem_kept (w_H W7) (w_H W7) mem7 _); [intros x Hx; apply KF; right; left; cbn in Hx; lia|].
                 replace (e_n g - (c + Z.of_nat (text_usedZ dat))) with (Z.of_nat (length dat - text_usedZ dat)) by lia.
                 exact Vin8.
             + split.
               * fold F. pose proof Hkat as (KA0 & _). fold F in KA0.
                 lazymatch type of HS with YP0l.st_ok _ ?Ev ?ssx (restrict _ ?msx) =>
                   let rk := eval vm_compute in (nth 6 (ss_mem ssx) got_region) in
                   let rb := eval vm_compute in (nth 7 (ss_mem ssx) got_region) in
                   pose proof (st_ok_region_nth Ev ssx (restrict (w_H W7) msx) 6 rk HS ltac:(vm_compute; reflexivity)) as HRk;
                   pose proof (st_ok_region_nth Ev ssx (restrict (w_H W7) msx) 7 rb HS ltac:(vm_compute; reflexivity)) as HRb end.
                 apply (r13_k_kept W2 W7 mem2 _ F pv dv 10 pv' dv' dd (so ++ repeat 0xa5 16) KA0).
                 -- intros x Hx. assert (Hz : Zj2 x).
                    { split; [|lia]. left. right. fold F. destruct Hx as [Hx | [Hx | Hx]]; [left | right | right]; lia. }
                    rewrite (KF x (or_introl Hz)), (KJ8 x Hz). apply KZ. right. fold F.
                    destruct Hx as [Hx | [Hx | Hx]]; [left | right | right]; lia.
                 -- apply (field_of_region _ _ 33 F _ _ _ _ _ 192 4 (SLit 10) 10 HRk BF6);
                      [cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | cbn; lia | cbn; lia].
                 -- apply (cw_val_mem_kept (w_H W2) (w_H W7) (ms_mem ms) _); [|exact Vp'].
                    intros x Hx. cbn in Hx. assert (Hz : Zj2 x) by (split; [right; lia | lia]).
                    rewrite (KF x (or_introl Hz)). exact (KJ8 x Hz).
                 -- apply (cw_val_mem_kept (w_H W2) (w_H W7) (ms_mem ms) _); [|exact Vd'].
                    intros x Hx. cbn in Hx. assert (Hz : Zj2 x) by (split; [right; lia | lia]).
                    rewrite (KF x (or_introl Hz)). exact (KJ8 x Hz).
                 -- eapply (field_of_region _ _ 33 F _ _ _ _ _ 220 4 _ dd HRb BF6);
                      [cbn [In]; repeat (first [left; reflexivity | right]) | exact DN | cbn; lia | cbn; lia].
                 -- apply (bm_garr8_kept_x (w_H W7) (w_H W7) mem7 _).
                    { intros x Hx. rewrite length_app, repeat_length, Lso in Hx. apply KF. right. right. cbn in Hx. lia. }
                    apply garr8_app. split; [exact Gso|]. rewrite Lso. exact G168.
               * unfold kcall_wfZ. cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out
                   kz_want_rc kz_want kz_want_len kz_want_key kz_want_display].
                 rewrite length_app, repeat_length, Lso, fa5_len, repeat_length. repeat split; lia.
             + unfold enc_okZ. cbn [kz_kind kz_p kz_desk kz_before kz_out]. split; [lia|]. split; [exact Hpd'|].
               split; [|split; reflexivity]. unfold rdr_kZ. cbn [kz_kind kz_a kz_b kz_c kz_delta kz_bytes kz_n]. exact RO13.
             + reflexivity. }
Qed.
End b.
End a.
