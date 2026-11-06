(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img's image range set to libreac/fuzz_boxreg's own (Reusable/YImgTop.v IMG_LO, IMG_TOP). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YCbq.v, with its module paths and module names changed; 447 of its 579 lines of code are new or changed and 2830 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxExit.v, with its module paths and module names changed; 316 of its 405 lines of code are new or changed and 490 lines of the source are left out. *)
(* Case op & 3 = 0 of the B walk of LLVMFuzzerTestOneInput, piece F -> FR: from the cut C0_F (0x808f0), where
   every check of the turn is passed, the name is loaded from the slot 0x60 and free (name) is called at 0x808f4
   (YC85.v afree04_sub over the lx_hyps field lh_free, the trace site 0x94c of LX_FSITES), to the cut C0_FR
   (0x808f8).  The call takes the name block away, so the turn's events and spending are those LI_K asks for; the
   rest of the cut (the slots of the turn, the saved words, the frame and its shadow) is read back from the
   symbolic state the call leaves (YC1h.v jafter_call_keep_hi), and the registry's bytes, prev and the caller's
   input from the call's acall_kept. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h YC85 BoxBCJ.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxCase0Defs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd reac_boxreg_declare_c
  reac_boxreg_declare_inv LLVMFuzzerTestOneInput_case0 LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_rn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxCase0Chk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HY : lx_hyps B MT.

Theorem c0_f : forall POST (i : nat), lx_from B MT POST (C0_FR B MT i) -> lx_from B MT POST (C0_F B MT i).
Proof.
  intros POST i HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR MLE
    (pos & r & fab & op & nm & bs & bs2 & HCOM & HNM & H60 & HRG & HINV2 & HFAB2 & HKEPT).
  pose proof (lh_laws _ _ HY) as LAWS0. pose (RUN0 := paj_run B LAWS0).
  pose proof (lh_tl _ _ HY) as TL.
  pose proof (lh_mtl _ _ HY) as MTL. pose proof (lh_mtfl _ _ HY) as MTFL.
  pose proof (lh_free _ _ HY) as AFREE.
  destruct HCOM as (HBD & Hi64 & HPREV & HINV & HFAB & Hposlt & Hop & Hop3 & HSLL & H58 & H48 & H20 & H21 & H27).
  destruct HNM as (Hk & Hacc & HAB & HFTOK & Hnm4096 & HNB & HCUR).
  pose proof HINV as ((HL & HB1 & _) & _).
  unfold Boxreg.boxreg_B1 in HB1.
  assert (Hmono : forall p n, In (p, n) (ablocks B (lc_ly cx) (lc_S cx)) -> In (p, n) (ablocks B ly3 S3))
    by (intros p n Hp; rewrite HAB; apply in_or_app; left; exact Hp).
  assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3))
    by (rewrite HAB; apply in_or_app; right; left; reflexivity).
  assert (Hnmin : In (nm, c0_nk (lc_pl cx) pos + 1) (ablocks B ly3 S3))
    by (rewrite HAB; apply in_or_app; right; right; left; reflexivity).
  destruct (c0c_seat B MT HY cx fp k ly3 S3 W3 ms3 md3 i (c0_pos2 (lc_pl cx) pos) C0P_F r fab nm 0 0 r
              (Boxreg.bx_n bs) 0 0 [] [] HB HJ HFR HBD HSLL H58 H48 H60 HCUR ltac:(lia)
              H20 H21 H27 Hmono Hrin ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(apply Forall_nil) ltac:(vm_compute; reflexivity) ltac:(apply Forall_nil)
              ltac:(reflexivity)) as (HS & SHOK).
  set (E := lx_env cx fp (ms_regs ms3) (c0c_ex cx fp i (c0_pos2 (lc_pl cx) pos) r nm 0 0 r (Boxreg.bx_n bs) 0 0))
    in HS, SHOK.
  assert (HEI : img_env VAL A_LIM E) by (unfold E; apply lx_env_img).
  pose proof HBD as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSHAD & HFLAG
    & HS10 & HS18 & HS80 & HINP).
  assert (HE : lx_E cx fp E) by (unfold E; apply (lx_env_E cx fp ms3 _); exact HREGS).
  pose proof HE as (E2 & E8 & E3 & E4 & E22 & E32 & ESAV & E46 & E47).
  pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
  pose proof (lx_F_facts B MT LAWS0 cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & HFimg & HFal & HSHeq).
  pose proof (lx_frame_addr_eq B MT LAWS0 cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EFA3.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (E2' : ew E 2 = w64 (lsp1 cx)) by exact E2.
  assert (E8' : ew E 8 = w64 (lsp0 cx)) by exact E8.
  assert (E22' : ew E 22 = w64 (lSH cx fp)) by exact E22.
  assert (E32' : ew E 32 = w64 SHADOW_OFF) by exact E32.
  assert (E46' : ew E 46 = w64 (lF cx fp)) by exact E46.
  assert (WS : LX_STK = 32768) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
  assert (Hes : ESTACK = 4096) by reflexivity.
  assert (UB2 : bv_unsigned (ew E 2) = lsp0 cx + (lsp1 cx - lsp0 cx))
    by (rewrite E2'; unfold w64; rewrite unsigned_lit_small by lia; lia).
  assert (UB46 : bv_unsigned (ew E 46) = lF cx fp)
    by (rewrite E46'; unfold w64; rewrite unsigned_lit_small by lia; lia).
  assert (UB8 : bv_unsigned (ew E 8) = lsp0 cx)
    by (rewrite E8'; unfold w64; rewrite unsigned_lit_small by lia; lia).
  paj_run_tok RUN0 HS HJ SHOK C0C_Bspan; [ c0c_awr cx fp EFA3 UB2 UB46 | ].

  pose proof HB as (HPRE & _ & _ & Hpn & _ & Hfr0 & Hev & Hlive & Hrod & MOK & HNEEDB & HTR).
  pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT0).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47' & Hbot & Htop & Htop2).
  pose proof HJ as (HAR3 & Hly3 & _).
  assert (E48 : ew E 48 = w64 nm) by exact (lx_env_ex cx fp (ms_regs ms3) _ 0%nat ltac:(lia)).
  pose proof (pa_B_ok (L := boxb_listing)) as (HBo0 & HBo1 & HBo4).
  pose proof (pa_base_lo (L := boxb_listing)) as HBlo.
  assert (ESP0 : lsp0 cx = spZ (lc_regs cx)) by reflexivity.
  pmkst HS. rewrite (pal_free B TL).
  prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
  prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
  assert (Qsp : spZ (ms_regs ms) = lsp1 cx)
    by (unfold spZ; rewrite Rsp, E2'; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).

  pose proof (c0c_layout_addrs _ _ _ LX_CID fp Hly3) as (EFA3' & EFL3 & ETOP3).
  assert (E33 : ew E 33 = getr (lc_regs cx) 1) by exact (ESAV 0%nat ltac:(lia)).
  assert (E34 : ew E 34 = getr (lc_regs cx) 8) by exact (ESAV 1%nat ltac:(lia)).
  assert (QRA8 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (lsp0 cx - 8) = Some (raZ (lc_regs cx))).
  { replace (lsp0 cx - 8) with (lsp0 cx + -8) by lia.
    eapply (c0c_word E _ (w_H W3) ms 0 8%nat); [exact HS | reflexivity | exact UB8 | cbn; tauto | | apply u64_range].
    rewrite lx_sv_SOff0, E33. unfold raZ. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (QS016 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (lsp0 cx - 16) = Some (s0Z (lc_regs cx))).
  { replace (lsp0 cx - 16) with (lsp0 cx + -16) by lia.
    eapply (c0c_word E _ (w_H W3) ms 0 8%nat); [exact HS | reflexivity | exact UB8 | cbn; tauto | | apply u64_range].
    rewrite lx_sv_SOff0, E34. unfold s0Z. symmetry. apply Z_to_bv_bv_unsigned. }

  eapply SRr_bind.
  { eapply (afree04_sub SEGS B LAWS0 pa_segs_low MT AFREE W3 (ms_regs ms) (ms_mem ms) LX_STK (lsp0 cx) []
      (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)] ly3 S3 _ k nm
      (c0_nk (lc_pl cx) pos + 1) (lsp1 cx - lsp0 cx) (Z_to_bv 64 (BASE + 2380)) (lch cx) HJ).
    - exact Hnmin.
    - rewrite Ra0. exact E48.
    - rewrite Qsp. lia.
    - exact (c0c_mod16 _ _ Hsp1al Hsp0al).
    - lia.
    - rewrite Has, WS. lia.
    - rewrite Rgp, E3. exact Hgp.
    - rewrite Rtp, E4. exact Htp.
    - exact Rra.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev3 & _). unfold LX_EV in Hev. lia.
    - apply (achain_chain_pre ly3 _ (lsp1 cx) (lsp0 cx)).
      + apply (c0c_achain_ly (lc_ly cx)); [exact ETOP3|].
        apply (lx_achain cx _ (lsp1 cx)); [exact Hch | lia | lia | rewrite ESP0; exact (c0c_mod8 _ Hal16) | exact Hra4
          | intros a Ha; eapply aview_above_of_journal; [exact HJ | exact Ha] | exact QRA8 | exact QS016 | lia].
      + rewrite Qsp. lia.
      + unfold s0Z. rewrite Rs0, E8'. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
      + unfold raZ. rewrite Rra, unsigned_lit_small by lia. lia.
    - apply HTR. right. split; [reflexivity|]. unfold raZ. rewrite Rra, unsigned_lit_small by lia.
      replace (BASE + 2380 - BASE) with 2380 by lia. unfold LX_FSITES. right; left; reflexivity.
    - exact HFTOK.
    - apply (mok_station MT (lc_S cx) S3 (lc_T cx) acc (mo_free MT) MTL MOK MLE (mo_free_nonneg MT MTL)).
      pose proof (mo_malloc_mono MT MTL (c0_nk (lc_pl cx) pos + 1) 48
        ltac:(pose proof (LLVMFuzzerTestOneInput_rn.rn_k_range (c0_pl2 (lc_pl cx) pos)); unfold c0_nk; lia)) as Hmm.
      pose proof (mo_free_nonneg MT MTL) as Hfr. pose proof (mo_malloc_nonneg MT MTL 48 ltac:(lia)) as Hm48.
      assert (HAI : 0 <= LX_AI MT) by (unfold LX_AI; lia).
      assert (Hprod : Z.of_nat i * LX_AI MT <= 63 * LX_AI MT)
        by (apply Z.mul_le_mono_nonneg_r; [exact HAI | lia]).
      unfold LX_NEED, LX_AI, LX_A1 in *. lia. }

  cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Ebl1 & Ebl2) & Hfrs2 & HK2 & MLE2 & HJsub).

  pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & _ & Hnev2 & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  pose proof HJ as (HARc & _).
  rewrite HFR in Hfrs2.
  assert (Hfin2 : In (LX_CID, fp) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  assert (Hfin3 : In (LX_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (al_blocks _ _ LAWS0 _ _ _ _ _ r LX_REG HARc Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
  change (req_size LX_REG) with 288 in Hrceil, Hria.
  destruct (al_blocks _ _ LAWS0 _ _ _ _ _ nm (c0_nk (lc_pl cx) pos + 1) HARc Hnmin)
    as (Hnm16 & Hnm4 & Hnmceil & Hnmia & _).
  pose proof (sep_block_frame SEGS B LAWS0 ly3 S3 W3 (ms_mem ms) _ nm (c0_nk (lc_pl cx) pos + 1)
                LX_CID fp HARc Hnmin Hfin3) as HdNF.
  unfold zdisjoint in HdNF. cbn [fst snd] in HdNF.
  rewrite (lx_frame_addr_eq B MT LAWS0 cx fp W3 ms ly3 S3 _ k HB HJ) in HdNF.
  change (fs_frame_bytes LX_CID) with 512 in HdNF.

  assert (Hnk : 0 <= c0_nk (lc_pl cx) pos <= 47)
    by (pose proof (LLVMFuzzerTestOneInput_rn.rn_k_range (c0_pl2 (lc_pl cx) pos)) as Hrk; unfold c0_nk; lia).
  assert (Hne0 : (c0_nk (lc_pl cx) pos + 1 =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (Hreqnm : req_size (c0_nk (lc_pl cx) pos + 1) = c0_nk (lc_pl cx) pos + 1)
    by (unfold req_size; rewrite Hne0; reflexivity).
  rewrite Hreqnm in HdNF, Hnmceil, Hnmia.
  


  assert (UB22 : bv_unsigned (ew E 22) = lSH cx fp).
  { rewrite E22'. unfold w64. rewrite unsigned_lit_small; [reflexivity|].
    rewrite HSHeq. unfold SHADOW_OFF.
    pose proof (Z.div_pos (lF cx fp) 8 ltac:(lia) ltac:(lia)) as Hd0.
    pose proof (Z.div_le_upper_bound (lF cx fp) 8 (2 ^ 61) ltac:(lia) ltac:(lia)) as Hd1. lia. }
  jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0;1;2;3]%nat HS2.

  match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
  { cbn [ms_mem restrict].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]];
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.base_val]; intros a Ha.
    - rewrite UB8 in Ha. apply (mbyte_of_aview SEGS). apply (proj1 HK2); lia.
    - rewrite UB8 in Ha. exfalso. lia.
    - rewrite UB2 in Ha. apply (mbyte_of_aview SEGS). apply (proj1 HK2); lia.
    - intros _. rewrite UB2 in Ha. apply (apresent_writable SEGS). apply Hpres2. lia.
    - rewrite UB46 in Ha. apply (mbyte_of_aview SEGS).
      apply (proj1 (proj2 (proj2 (proj2 HK2))) LX_CID fp a Hfin3).
      + left. unfold in_zr, frame_rng. cbn [fst snd].
        rewrite (lx_frame_addr_eq B MT LAWS0 cx fp W3 ms ly3 S3 _ k HB HJ).
        change (fs_frame_bytes LX_CID) with 512. lia.
      + rewrite Hreqnm. lia.
    - rewrite UB46 in Ha. exfalso. lia.
    - rewrite UB22 in Ha. apply (mbyte_of_aview SEGS).
      apply (proj1 (proj2 (proj2 (proj2 HK2))) LX_CID fp a Hfin3).
      + right. unfold in_zr. cbn [fst snd].
        rewrite (lx_frame_addr_eq B MT LAWS0 cx fp W3 ms ly3 S3 _ k HB HJ).
        change (fs_frame_bytes LX_CID / 8) with 64. unfold lSH in Ha. lia.
      + rewrite Hreqnm. rewrite HSHeq in Ha.
        intros HEa. exact (fshadow_not_app (lF cx fp) 64 nm (c0_nk (lc_pl cx) pos + 1) a HF0 ltac:(lia)
          Hnmia ltac:(unfold SHADOW_OFF in Ha; lia) ltac:(lia)).
    - rewrite UB22 in Ha. exfalso. lia. }
  specialize (HS2 HRK). clear HRK.
  rewrite <- restrict_mkst_fx in HS2.

  assert (EX : forall j, (j < 12)%nat ->
    ew E (LA_EX + j) = nth j (c0c_ex cx fp i (c0_pos2 (lc_pl cx) pos) r nm 0 0 r (Boxreg.bx_n bs) 0 0) (w64 0))
    by (intros j Hj; apply lx_env_ex; lia).
  assert (E49 : ew E 49 = w64 (2 ^ 64 - 1 - r)) by exact (EX 1%nat ltac:(lia)).
  assert (E50 : ew E 50 = w64 (2 ^ 64 - 1 - (lF cx fp + 64))) by exact (EX 2%nat ltac:(lia)).
  assert (E52 : ew E 52 = w64 (lc_p cx + Z.of_nat (c0_pos2 (lc_pl cx) pos))) by exact (EX 4%nat ltac:(lia)).
  assert (E53 : ew E 53 = w64 (lc_n cx - Z.of_nat (c0_pos2 (lc_pl cx) pos))) by exact (EX 5%nat ltac:(lia)).
  assert (E56 : ew E 56 = w64 (Boxreg.bx_n bs)) by exact (EX 8%nat ltac:(lia)).
  assert (E59 : ew E 59 = w64 (Z.of_nat i)) by exact (EX 11%nat ltac:(lia)).
  assert (E20 : ew E 20 = w64 r)
    by (unfold E; rewrite (lx_env_reg cx fp _ _ 20 (20%bv : bv 5)) by reflexivity; exact H20).
  assert (E27 : ew E 27 = w64 fab)
    by (unfold E; rewrite (lx_env_reg cx fp _ _ 27 (27%bv : bv 5)) by reflexivity; exact H27).
  set (E' := havoc E 512 (map (getr regs2) CLOB)) in HS2.
  set (ms2 := mkst regs2 (Z_to_bv 64 (BASE + 2380)) mem2 (seg_rom SEGS)) in HS2.
  assert (HEI2 : img_env VAL A_LIM E')
    by (unfold E'; apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]).
  assert (HE2 : lx_E cx fp E').
  { apply (lx_E_agree cx fp E); [exact HE|]. intros n Hn. unfold E'. apply ew_havoc_old. unfold LA_EX in Hn. lia. }

  pose proof (lx_slot_of_ss B MT cx fp W2 ms2 HB) as SLOT.
  assert (RNG2 : forall off v, lslot cx W3 ms3 off v -> 0 <= v < 2 ^ 64)
    by (intros off v Hv; exact (c0_rdword_range _ _ _ _ Hv)).
  pose proof HSLL as (S08 & S28 & S30 & S38 & S40 & S68 & S70 & S78).
  pose proof (RNG2 _ _ S30) as Hfab64. pose proof (RNG2 _ _ H48) as Hnn64.
  pose proof (RNG2 _ _ H60) as Hnm64. pose proof (RNG2 _ _ H58) as Hi64b. pose proof (RNG2 _ _ S40) as Hsh64.
  assert (N08 : lslot cx W2 ms2 0x08 3).
  { eapply (SLOT E' _ _ _ _ _ _ 0x08 (SLit 3)); [exact HE2 | exact HS2 | reflexivity | cbn [In]; tauto
      | reflexivity | lia]. }
  assert (N10 : lslot cx W2 ms2 0x10 (lF cx fp)).
  { eapply (SLOT E' _ _ _ _ _ _ 0x10 (SOff 46 0)); [exact HE2 | exact HS2 | reflexivity | cbn [In]; tauto
      | rewrite lx_sv_SOff0; c0c_ew; exact E46' | lia]. }
  assert (N18 : lslot cx W2 ms2 0x18 (lF cx fp)).
  { eapply (SLOT E' _ _ _ _ _ _ 0x18 (SOff 46 0)); [exact HE2 | exact HS2 | reflexivity | cbn [In]; tauto
      | rewrite lx_sv_SOff0; c0c_ew; exact E46' | lia]. }
  assert (N80 : lslot cx W2 ms2 0x80 (lF cx fp)).
  { eapply (SLOT E' _ _ _ _ _ _ 0x80 (SOff 46 0)); [exact HE2 | exact HS2 | reflexivity | cbn [In]; tauto
      | rewrite lx_sv_SOff0; c0c_ew; exact E46' | lia]. }
  assert (N28 : lslot cx W2 ms2 0x28 (r + 280)).
  { eapply (SLOT E' _ _ _ _ _ _ 0x28 (SOff 20 280)); [exact HE2 | exact HS2 | reflexivity | cbn [In]; tauto
      | apply (c0c_den_off E' 20 280 r); [exact E20 | lia | lia] | lia]. }
  assert (N30 : lslot cx W2 ms2 0x30 fab).
  { eapply (SLOT E' _ _ _ _ _ _ 0x30 (SOff 27 0)); [exact HE2 | exact HS2 | reflexivity | cbn [In]; tauto
      | rewrite lx_sv_SOff0; c0c_ew; exact E27 | lia]. }
  assert (N38 : lslot cx W2 ms2 0x38 0).
  { eapply (SLOT E' _ _ _ _ _ _ 0x38 (SLit 0)); [exact HE2 | exact HS2 | reflexivity | cbn [In]; tauto
      | reflexivity | lia]. }
  assert (N40 : lslot cx W2 ms2 0x40 (shadow_addr (r + 280))).
  { eapply (SLOT E' _ _ _ _ _ _ 0x40 c0c_shx); [exact HE2 | exact HS2 | reflexivity | cbn [In]; tauto
      | unfold c0c_shx; rewrite (denot_shx E' 20%nat LA_SB 280 r SHADOW_OFF E20 E32');
        [reflexivity | lia | lia | lia | unfold SHADOW_OFF; lia]
      | lia]. }
  assert (N48b : lslot cx W2 ms2 0x48 (Boxreg.bx_n bs)).
  { eapply (SLOT E' _ _ _ _ _ _ 0x48 (SOff 56 0)); [exact HE2 | exact HS2 | reflexivity | cbn [In]; tauto
      | rewrite lx_sv_SOff0; c0c_ew; exact E56 | lia]. }
  assert (N58 : lslot cx W2 ms2 0x58 (Z.of_nat i)).
  { eapply (SLOT E' _ _ _ _ _ _ 0x58 (SOff 59 0)); [exact HE2 | exact HS2 | reflexivity | cbn [In]; tauto
      | rewrite lx_sv_SOff0; c0c_ew; exact E59 | lia]. }
  assert (N60 : lslot cx W2 ms2 0x60 nm).
  { eapply (SLOT E' _ _ _ _ _ _ 0x60 (SOff 48 0)); [exact HE2 | exact HS2 | reflexivity | cbn [In]; tauto
      | rewrite lx_sv_SOff0; c0c_ew; exact E48 | lia]. }
  assert (N68 : lslot cx W2 ms2 0x68 (lF cx fp + 32)).
  { eapply (SLOT E' _ _ _ _ _ _ 0x68 (SOff 46 32)); [exact HE2 | exact HS2 | reflexivity | cbn [In]; tauto
      | apply (c0c_den_off E' 46 32 (lF cx fp)); [exact E46' | lia | lia] | lia]. }
  assert (N70 : lslot cx W2 ms2 0x70 (2 ^ 64 - 1 - r)).
  { eapply (SLOT E' _ _ _ _ _ _ 0x70 (SOff 49 0)); [exact HE2 | exact HS2 | reflexivity | cbn [In]; tauto
      | rewrite lx_sv_SOff0; c0c_ew; exact E49 | lia]. }
  assert (N78 : lslot cx W2 ms2 0x78 (2 ^ 64 - 1 - (lF cx fp + 64))).
  { eapply (SLOT E' _ _ _ _ _ _ 0x78 (SOff 50 0)); [exact HE2 | exact HS2 | reflexivity | cbn [In]; tauto
      | rewrite lx_sv_SOff0; c0c_ew; exact E50 | lia]. }
  pose proof HCUR as (HcurL & Hcur88 & Hcur90).
  pose proof (RNG2 _ _ Hcur88) as Hcur88r. pose proof (RNG2 _ _ Hcur90) as Hcur90r.
  assert (N88 : lslot cx W2 ms2 0x88 (lc_p cx + Z.of_nat (c0_pos2 (lc_pl cx) pos))).
  { eapply (SLOT E' _ _ _ _ _ _ 0x88 (SOff 52 0)); [exact HE2 | exact HS2 | reflexivity | cbn [In]; tauto
      | rewrite lx_sv_SOff0; c0c_ew; exact E52 | lia]. }
  assert (N90 : lslot cx W2 ms2 0x90 (lc_n cx - Z.of_nat (c0_pos2 (lc_pl cx) pos))).
  { eapply (SLOT E' _ _ _ _ _ _ 0x90 (SOff 53 0)); [exact HE2 | exact HS2 | reflexivity | cbn [In]; tauto
      | rewrite lx_sv_SOff0; c0c_ew; exact E53 | lia]. }

  assert (KRUN : forall a, 0 <= a < 2 ^ 64 -> ~ (lsp1 cx <= a < lsp1 cx + 152) ->
     aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha Hout. unfold aview. f_equal.
    apply (c0c_mbyte_frame E _ _ _ a HFr Ha).
    intros (rg & Hin & Hr).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hr;
        first [ rewrite UB2 in Hr; lia | lia ] | ]).
    destruct Hin. }

  assert (Hceil1 : alloc_ceiling <= lsp1 cx) by lia.
  assert (KEEPB : forall b m j, In (b, m) (ablocks B ly3 S3) -> 0 <= j < req_size m ->
      ~ (nm <= b + j < nm + (c0_nk (lc_pl cx) pos + 1)) ->
      aview SEGS (w_H W2) mem2 (b + j) = aview SEGS (w_H W3) (ms_mem ms3) (b + j)).
  { intros b m j Hin Hj Hne.
    destruct (al_blocks _ _ LAWS0 _ _ _ _ _ b m HARc Hin) as (_ & Hb4096 & Hbceil & _).
    rewrite <- (KRUN (b + j) ltac:(lia) ltac:(lia)).
    apply (proj1 (proj2 HK2) b m j Hin Hj). rewrite Hreqnm. exact Hne. }
  assert (KEEPF : forall a, lF cx fp <= a < lF cx fp + 512 ->
      aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. rewrite <- (KRUN a ltac:(lia) ltac:(lia)).
    apply (proj1 (proj2 (proj2 (proj2 HK2))) LX_CID fp a Hfin3).
    - left. unfold in_zr, frame_rng. cbn [fst snd].
      rewrite (lx_frame_addr_eq B MT LAWS0 cx fp W3 ms ly3 S3 _ k HB HJ).
      change (fs_frame_bytes LX_CID) with 512. lia.
    - rewrite Hreqnm. lia. }
  pose proof (sep_blocks_pos SEGS B LAWS0 ly3 S3 W3 (ms_mem ms) _ (r, LX_REG) (nm, c0_nk (lc_pl cx) pos + 1)
                (ablocks B (lc_ly cx) (lc_S cx)) [] [] HARc ltac:(rewrite HAB; reflexivity)) as HdRN.
  unfold zdisjoint, block_rng in HdRN. cbn [fst snd] in HdRN.
  change (req_size LX_REG) with 288 in HdRN. rewrite Hreqnm in HdRN.
  assert (Hpin3 : In (lc_p cx, lc_n cx) (ablocks B ly3 S3)).
  { apply Hmono. pose proof HB as (_ & _ & _ & Hpn0 & _).
    destruct Hpn0 as [Hn0 | (_ & Hin0)]; [exfalso; unfold lc_n in Hn0; lia | exact Hin0]. }
  assert (Hnp : 0 < lc_n cx).
  { pose proof HB as (_ & _ & _ & Hpn0 & _). destruct Hpn0 as [Hn0 | (Hn0 & _)]; [unfold lc_n in Hn0; lia | lia]. }
  assert (Hreqp : req_size (lc_n cx) = lc_n cx)
    by (unfold req_size; rewrite (proj2 (Z.eqb_neq (lc_n cx) 0) ltac:(lia)); reflexivity).
  assert (Hne2 : (lc_p cx, lc_n cx) <> (nm, c0_nk (lc_pl cx) pos + 1)).
  { intros Hq. injection Hq as Hq1 Hq2.
    pose proof HB as (_ & _ & _ & Hpn1 & _).
    assert (Hin0 : In (lc_p cx, lc_n cx) (ablocks B (lc_ly cx) (lc_S cx)))
      by (destruct Hpn1 as [Hz | (_ & Hi0)]; [exfalso; unfold lc_n in Hz; lia | exact Hi0]).
    rewrite Hq1, Hq2 in Hin0.
    assert (Hge : 0 <= 0 < req_size (snd (nm, c0_nk (lc_pl cx) pos + 1)))
      by (cbn [snd]; rewrite Hreqnm; lia).
    exact (lx_inFP_nil _ (HFTOK Hin0 0 Hge)). }
  pose proof (sep_blocks SEGS B LAWS0 ly3 S3 W3 (ms_mem ms) _ (lc_p cx) (lc_n cx) nm
                (c0_nk (lc_pl cx) pos + 1) HARc Hpin3 Hnmin Hne2) as HdPN.
  unfold zdisjoint, block_rng in HdPN. cbn [fst snd] in HdPN.
  rewrite Hreqp, Hreqnm in HdPN.
  assert (Hmem2 : ms_mem ms2 = mem2) by reflexivity.
  assert (NPREV : lprev cx fp W2 ms2 bs).
  { intros j Hj. unfold lview. rewrite Hmem2. rewrite (KEEPF (lF cx fp + 64 + j) ltac:(unfold LX_REG in Hj; lia)).
    exact (HPREV j Hj). }
  assert (NREG : lreg W2 ms2 r bs2).
  { intros j Hj. unfold lview. rewrite Hmem2.
    rewrite (KEEPB r LX_REG j Hrin ltac:(change (req_size LX_REG) with 288; exact Hj) ltac:(unfold LX_REG in Hj; lia)).
    exact (HRG j Hj). }
  assert (NGARR : garr8 SEGS (mrestrict (w_H W2) (ms_mem ms2)) (lc_p cx)
                    (map (fun b0 : byte => bv_unsigned b0) (lc_pl cx))).
  { intros j Hj. destruct (HINP j Hj) as (Hv & Hr0). split; [|exact Hr0].
    intros kk Hkk. assert (Hk0 : kk = 0%nat) by lia. subst kk. cbn [Z.of_nat].
    rewrite !Z.add_0_r. rewrite Hmem2.
    pose proof (Hv 0%nat ltac:(lia)) as Hv0. change (Z.of_nat 0) with 0 in Hv0. rewrite Z.add_0_r in Hv0.
    rewrite (mbyte_of_aview SEGS (w_H W3) (w_H W2) (ms_mem ms3) mem2 (lc_p cx + Z.of_nat j)).
    - exact Hv0.
    - assert (Hj0 : (0 <= Z.of_nat j)%Z) by apply Nat2Z.is_nonneg.
      assert (HjZ : (Z.of_nat j < lc_n cx)%Z)
        by (unfold lc_n; apply Nat2Z.inj_lt; rewrite length_map in Hj; exact Hj).
      apply (KEEPB (lc_p cx) (lc_n cx) (Z.of_nat j) Hpin3).
      + rewrite Hreqp. split; [exact Hj0 | exact HjZ].
      + destruct HdPN as [Hd1 | Hd1]; lia. }

  prreg HS2 (20%bv : bv 5) R20. prreg HS2 (21%bv : bv 5) R21. prreg HS2 (27%bv : bv 5) R27.
  assert (NSAV : lsaved cx W2 ms2) by exact (lx_saved_of_ss B MT cx fp W2 ms2 HB E' _ HE2 HS2 eq_refl).
  assert (NSH : lshadow cx fp W2 ms2 LSH_iter).
  { eapply (lx_shadow_of_ss B MT LAWS0 cx fp W2 ms2 ly2 S2 md2 (k + 1) HB HJ2 Hfrs2 E');
      [exact HE2 | exact HS2 | reflexivity | vm_compute; reflexivity]. }
  assert (NFL : rdword (lview W2 ms2) (lF cx fp + fs_frame_bytes LX_CID - 8) = Some (lFL cx fp)).
  { eapply (lx_flag_of_ss B MT LAWS0 cx fp W2 ms2 ly2 S2 md2 (k + 1) HB HJ2 Hfrs2 E');
      [exact HE2 | exact HS2 | reflexivity | cbn [In]; tauto]. }
  assert (NBODY : lx_body cx fp C0P_FR W2 ms2 LSH_iter).
  { eapply (lx_land cx fp W2 ms2 E' C0P_FR _ LSH_iter);
      [ exact HE2 | exact HS2 | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity
      | exact NSAV | exact NSH | exact NFL | exact N10 | exact N18 | exact N80 | exact NGARR]. }

  assert (DROP : forall (L : list (Z * Z)) x y m1 m2, ~ In x L -> x <> y ->
            m1 ++ x :: m2 = L ++ [y; x] -> m1 ++ m2 = L ++ [y]).
  { induction L as [|c L IH]; intros x y n1 n2 Hni Hxy Heq.
    - destruct n1 as [|a [|b n1']]; cbn [app] in Heq.
      + injection Heq as Ea _. exfalso. apply Hxy. exact Ea.
      + injection Heq as Ea Heq. subst a. subst n2. reflexivity.
      + injection Heq as Ea Eb Heq2. subst a. subst b.
        exfalso. destruct n1'; cbn [app] in Heq2; discriminate.
    - destruct n1 as [|a n1]; cbn [app] in Heq.
      + injection Heq as Ea _. exfalso. apply Hni. left. symmetry. exact Ea.
      + injection Heq as Ea Heq. subst a. cbn [app]. f_equal.
        apply (IH x y n1 n2); [intros Hin; apply Hni; right; exact Hin | exact Hxy | exact Heq]. }
  assert (HnotC : ~ In (nm, c0_nk (lc_pl cx) pos + 1) (ablocks B (lc_ly cx) (lc_S cx))).
  { intros Hin0. assert (Hge : 0 <= 0 < req_size (snd (nm, c0_nk (lc_pl cx) pos + 1)))
      by (cbn [snd]; rewrite Hreqnm; lia).
    exact (lx_inFP_nil _ (HFTOK Hin0 0 Hge)). }
  assert (HNEQ : (nm, c0_nk (lc_pl cx) pos + 1) <> (r, LX_REG)).
  { intros Hq. injection Hq as Hq1 Hq2. change (req_size LX_REG) with 288 in HdRN. lia. }
  assert (NBLK : lblk B cx ly2 S2 r).
  { unfold lblk. rewrite Ebl2.
    apply (DROP (ablocks B (lc_ly cx) (lc_S cx)) (nm, c0_nk (lc_pl cx) pos + 1) (r, LX_REG) l1 l2
             HnotC HNEQ). rewrite <- Ebl1. rewrite HAB. reflexivity. }

  apply (HNEXT cx fp (k + 1) (acc + mo_free MT) ly2 S2 W2 ms2 md2 HB HJ2 Hfrs2
           (mle_station MT (lc_S cx) S3 S2 acc (mo_free MT) MTL MLE MLE2)).
  exists pos, r, fab, op, bs, bs2.
  split.
  { split; [exact NBODY|]. split; [exact Hi64|]. split; [exact NPREV|]. split; [exact HINV|].
    split; [exact HFAB|]. split; [exact Hposlt|]. split; [exact Hop|]. split; [exact Hop3|].
    split.
    { split; [exact N08|]. split; [exact N28|]. split; [exact N30|]. split; [exact N38|].
      split; [exact N40|]. split; [exact N68|]. split; [exact N70 | exact N78]. }
    split; [exact N58|]. split; [exact N48b|].
    split; [rewrite R20; exact E20|].
    split; [rewrite R21; apply (c0c_den_off E' 46 64 (lF cx fp)); [exact E46' | lia | lia]
           | rewrite R27; exact E27]. }
  split; [lia|].
  split.
  { pose proof (mo_malloc_mono MT MTL (c0_nk (lc_pl cx) pos + 1) 48 ltac:(lia)) as Hmm2.
    replace ((Z.of_nat i + 1) * LX_AI MT) with (Z.of_nat i * LX_AI MT + LX_AI MT) by ring.
    assert (HAIe : LX_AI MT = mo_malloc MT 48 + mo_free MT) by reflexivity. lia. }
  split; [exact NBLK|].
  split; [split; [exact HcurL | split; [exact N88 | exact N90]]|].
  split; [exact NREG|]. split; [exact HINV2|]. split; [exact HFAB2 | exact HKEPT].
Qed.


End a.
