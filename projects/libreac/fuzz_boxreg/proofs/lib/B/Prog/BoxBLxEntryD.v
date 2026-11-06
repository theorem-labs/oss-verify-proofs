(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 909 of its 980 lines of code are new or changed and 860 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase0TN.v, with its module names changed; 125 of its 166 lines of code are new or changed and 939 lines of the source are left out. *)
(* Lane D of the entry phase of the B walk of fuzz_boxreg's LLVMFuzzerTestOneInput (fuzz_boxreg.asan-ubsan 0x7ffac):
   the call of check (r, fabric) at 0x80210 and its return to ss_K (0x80214).
   le_D : le_K_stmt B MT -> le_D_stmt B MT (BoxBLxEntryDefs.v).

   The walk (the model is BoxBLxEntry.v le_from_C, the reac_boxreg_init call):
   - the call: cl_callS with check's stack CHECK_STKB and no footprint, from sp1 = sp0 + (sp1 - sp0); the chain
     from le_saved_at / le_chain, gp / tp from lx_E, ra = BASE + 616;
   - the callee: lh_check (BoxBCheck.v tbcheck_spec) with
       afn_pre from cl_callS;
       arodata_okP: lx_arodata_kept (BoxBLxDefs.v) on le_cut's journal and lx_base's arodata fact;
       a0 = r (register 10 = atom 84), a1 = fab (register 11 = atom 99);
       In (r, REG_SIZEB) (ablocks ..) from le_cut's ablocks equation (REG_SIZEB = LX_REG = 288);
       the bytes: lreg (init_bytes fab) of le_cut;
       boxreg_B16 / bx_fabric: le_check_model (Pau's BoxregInit.init_bytes_inv);
       img_shadow_vis, ZERO's bytes and margins, memchr's constants: le_check_img (BoxBLxDefs.v BLxLib);
       globs_marked [(ZERO, 6)]: le_globs_marked_d (the start-up registration's cells);
   - after the call: tbcheck_post gives ly' = ly, S' = S, W' = W; lx_keep_call_fp (no footprint) and le_kept4 keep
     the four regions; the registers check may clobber are the fresh atoms 128 .. (havoc E 128, lx_E_agree,
     img_env_havoc), and the state is ss_K;
   - the le_K_stmt argument with le_cut at the new state: journal k = 1 + 0, frames / mo_le / ablocks unchanged,
     lreg from check's post, atoms 84 / 96 / 97 / 98 / 99 kept (< 128). *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase YC4b BoxRo PaStep.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit BoxBCheck.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import SnprintfDefB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxEntryDefs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregInit reac_boxreg_init_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* Pau's model: the registry reac_boxreg_init leaves passes check's facts for its fabric. *)
Lemma le_check_model : forall x,
  Boxreg.boxreg_B16 (reac_boxreg_init_c.init_bytes (reac_boxreg_init_c.clamp40 x)) /\
  Boxreg.bx_fabric (reac_boxreg_init_c.init_bytes (reac_boxreg_init_c.clamp40 x)) = reac_boxreg_init_c.clamp40 x.
Proof.
  intros x. destruct (BoxregInit.init_bytes_inv x) as ((I1 & _) & _ & I3). split; [exact I1 | exact I3].
Qed.

(* A symbolic state after a call, computed (BoxBLxEntry.v le_norm). *)
Ltac led_norm HS :=
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.

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

(* ZERO's shadow (the start-up registration's cells, BoxBLxDefs.v BLxLib) in every AR state (a Theorem Labs lane's draft in
   BoxBLxEntry.v). *)
Lemma le_globs_marked_d : globs_marked SEGS B [(VAL (A_OBJ 4), 6)].
Proof.
  intros ly S W mem md q sz Hin HAR. destruct Hin as [Heq | []]. injection Heq as <- <-.
  pose proof (lh_glob B MT HY) as HG.
  pose proof (blx_cells B HG ly (z1 (ANum (shadow_addr (VAL (A_OBJ 4)))) 6)
    ltac:(unfold lx_glob_cells, LX_GLOBS; cbn [flat_map app fst snd]; left; reflexivity)) as Hc.
  pose proof (am_const _ _ _ _ (proj1 HAR)) as HC. rewrite Forall_forall in HC. specialize (HC _ Hc).
  unfold cell_holds in HC. cbn [z1 c1 c_at c_w c_val aeval] in HC.
  pose proof (blx_al B HG (4%nat, 6) ltac:(unfold LX_GLOBS; left; reflexivity)) as Hal. cbn [fst] in Hal.
  split.
  - pose proof (Z.div_mod (VAL (A_OBJ 4)) 32 ltac:(lia)) as D. rewrite Hal, Z.add_0_r in D. rewrite D.
    replace (32 * (VAL (A_OBJ 4) / 32)) with ((4 * (VAL (A_OBJ 4) / 32)) * 8) by lia. apply Z_mod_mult.
  - split; [lia|]. intros i Hi. change ((6 + 7) / 8) with 1 in Hi. assert (Hi0 : i = 0) by lia. subst i.
    specialize (HC 0%nat ltac:(lia)). cbn [Z.of_nat] in HC. rewrite Z.add_0_r in HC.
    unfold shadow_of_addr. rewrite Z.add_0_r. unfold shadow_addr in HC. rewrite HC. reflexivity.
Qed.

(* The image facts check takes, state-free (BoxBLxDefs.v BLxLib). *)
Lemma le_check_img :
  img_shadow_vis SEGS B /\
  absn_rom_bytes SEGS B (VAL (A_OBJ 4)) (map (fun b : byte => bv_unsigned b) Boxreg.zero6) /\
  IMG_LO + 64 <= VAL (A_OBJ 4) /\ VAL (A_OBJ 4) + 6 + 64 <= IMG_HI /\
  absn_rom_bytes SEGS B MCH_LOB MCH_CONSTSB.
Proof.
  pose proof (lh_glob B MT HY) as HG.
  pose proof (blx_marg B HG (4%nat, 6) ltac:(unfold LX_GLOBS; left; reflexivity)) as (M1 & M2). cbn [fst snd] in M1, M2.
  pose proof (blx_rom_bytes B HG (4%nat, [0; 0; 0; 0; 0; 0]) ltac:(unfold LX_GLOB_BYTES; left; reflexivity)) as Hz.
  cbn [fst snd] in Hz.
  assert (Ez : map (fun b : byte => bv_unsigned b) Boxreg.zero6 = [0; 0; 0; 0; 0; 0]) by (vm_compute; reflexivity).
  split; [exact (blx_isv B HG)|]. split; [rewrite Ez; exact Hz|].
  split; [exact M1|]. split; [exact M2 | exact (blx_mch B HG)].
Qed.

(* D: the call of check (r, fabric) (0x80210) and its return to ss_K (0x80214). *)
Theorem le_D : le_K_stmt B MT -> le_D_stmt B MT.
Proof.
  intros HK POST cx fp E W ms md ly S r b fab pos HC HS.
  pose proof HC as (HFROM & HB & HEI & HE & E84 & E96 & Hb & E99 & Hfab & E97 & E98 & Hpos & HJ & HFR & Hmle & Hbl & Hreg).
  pose proof (le_sp_facts B MT cx HB) as (Hal16 & Hsp0lo & Hsp0hi & Hsp1 & Hal32).
  pose proof HB as (HPRE & H10 & H11 & Hn & Hgarr & Hfr0 & Hnev & Hlive & Hro & Hmok & Hneed & Htr).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  pose proof (lh_laws B MT HY) as LAWS. pose proof (lh_tl B MT HY) as TL.
  pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
  pose proof (lx_F_facts B MT LAWS cx fp W ms ly S md 1 HB HJ HFR) as (HF0 & HFc & HFia & HFo & HF64 & HSHeq).
  pose proof (lx_frame_addr_eq B MT LAWS cx fp W ms ly S md 1 HB HJ) as Hfa. change LX_CID with 3 in Hfa.
  pose proof HJ as (HAR1 & _ & _ & _ & _ & _ & _ & _ & HJF1 & _ & _ & _ & _ & HJpres & _).
  assert (Hrin : In (r, LX_REG) (ablocks B ly S)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
  pose proof (lx_extents B MT LAWS cx fp W ms ly S md 1 HB HJ HFR E HE) as (U8 & U2 & U46 & U22).
  (* check's premises that do not depend on the call *)
  pose proof (le_check_img) as (Hisv & Hzero & Hzlo & Hzhi & Hmch).
  pose proof (le_check_model (le_sx b)) as (HB16 & Hbxf). rewrite <- Hfab in HB16, Hbxf.
  pose proof (lx_arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hro) as HroD.
  (* check (r, fabric) (0x80210) *)
  pose proof (le_saved_at B MT cx fp E _ _ W ms HB HE HS eq_refl) as HSV.
  pose proof (le_chain B MT cx fp ly S W ms md 1 HB HJ HSV) as Hach.
  pmkst HS.
  prreg HS (10%bv : bv 5) Ia0. prreg HS (11%bv : bv 5) Ia1. prreg HS (2%bv : bv 5) I2.
  prreg HS (3%bv : bv 5) I3. prreg HS (4%bv : bv 5) I4. prreg HS (1%bv : bv 5) I1. prreg HS (8%bv : bv 5) I8.
  rewrite pa_sigma_check.
  pose proof HE as (EW2 & EW8 & EW3 & EW4 & EW22 & EW32 & EWSV & EW46 & EW47).
  unfold LA_SP, LA_SP0, LA_FSH, LA_SB, LA_F, LA_FL in EW2, EW8, EW22, EW32, EW46, EW47.
  assert (HspI : spZ (ms_regs ms) = lsp1 cx).
  { unfold spZ. rewrite I2, EW2. unfold w64. apply unsigned_lit_small. lia. }
  assert (H16 : (lsp1 cx - lsp0 cx) mod 16 = 0).
  { assert (H16' : lsp1 cx mod 16 = 0)
      by (unfold lsp1; replace (32 * ((lsp0 cx - 256) / 32)) with ((2 * ((lsp0 cx - 256) / 32)) * 16) by lia;
          apply Z_mod_mult).
    rewrite Zminus_mod, H16', Hal16. reflexivity. }
  assert (Ha0D : getr (ms_regs ms) 10 = w64 r) by (rewrite Ia0; exact E84).
  assert (Ha1D : getr (ms_regs ms) 11 = w64 fab) by (rewrite Ia1; exact E99).
  eapply SRr_bind.
  { eapply (cl_callS B LAWS W (ms_regs ms) (ms_mem ms) _ LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx)
      (lc_md cx) [(3, fp)] ly S md 1 CHECK_STKB [] 0 (lsp1 cx - lsp0 cx) (getr (ms_regs ms) 1) (lch cx) _ HJ).
    - rewrite HspI. lia.
    - exact H16.
    - lia.
    - unfold CHECK_STKB. change ESTACK with 4096. lia.
    - unfold CHECK_STKB, LX_STK. change ESTACK with 4096. lia.
    - rewrite I3, EW3. exact Hgp.
    - rewrite I4, EW4. exact Htp.
    - reflexivity.
    - rewrite I1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite I1, unsigned_lit_small by (pose proof pa_B_ok; lia). pose proof pa_base_lo. lia.
    - replace (lsp0 cx + (lsp1 cx - lsp0 cx)) with (lsp1 cx) by lia.
      unfold s0Z. rewrite I8, EW8. unfold w64. rewrite unsigned_lit_small by lia. exact Hach.
    - intros HPREc.
      exact (lh_check B MT HY ly S W (ms_regs ms) (ms_mem ms) md (lch cx) r fab (reac_boxreg_init_c.init_bytes fab)
        [(VAL (A_OBJ 4), 6)] HPREc HroD Ha0D Ha1D Hrin Hreg HB16 Hbxf Hisv le_globs_marked_d Hzero
        (or_introl eq_refl) Hzlo Hzhi Hmch).
    - intros a Ha. exfalso. exact (lx_inFP_nil a Ha). }
  cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HJc & HP5 & (-> & -> & -> & Hperm5 & Hchk)).

  rewrite I1.
  replace (lsp0 cx + (lsp1 cx - lsp0 cx)) with (lsp1 cx) in HJc by lia.
  change (1 + 0) with 1 in HJ5.
  assert (Hkeep5 : lx_keep cx fp W [] (ms_mem ms) mem5).
  { eapply (lx_keep_call_fp B MT LAWS cx fp W ms ly S md 1 HB HJ HFR [] [] CHECK_STKB
      _ _ mem5 md5 0); [lia | | apply Forall_nil | | exact HJc].
    - intros q m Hq. rewrite Hbl. apply in_or_app. left. exact Hq.
    - intros a _ Ha. exact (lx_inFP_nil a Ha). }
  pose proof HJ5 as (HAR5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ5pres & _).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 3 fp HAR5 ltac:(rewrite HFR; left; reflexivity)) as (_ & _ & HF5pres & _).
  rewrite Hfa in HF5pres. change (fs_frame_bytes 3) with 512 in HF5pres.
  jafter_call_keep_pi HS 128%nat regs5 (mrestrict (w_H W) mem5) HP5 [0; 1; 2; 3]%nat HS2.

  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    apply (le_kept4 cx fp E); [exact U8 | exact U2 | exact U46 | exact U22 | lia | lia | |].
    - intros a Ha. apply Hkeep5. unfold lx_keep_at. change (fs_frame_bytes LX_CID) with 512.
      destruct Ha as [Ha|[Ha|Ha]]; [left; lia | right; right; left; lia | right; right; right; left; change (512 / 8) with 64; lia].
    - intros a [Ha | [Ha | Ha]]; [apply HJ5pres; unfold LX_STK, LX_SPILL in *; lia | apply HF5pres; lia | lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  set (ms5 := mkst regs5 (Z_to_bv 64 (BASE + 616)) mem5 (seg_rom SEGS)) in *.
  remember (havoc E 128 (map (getr regs5) CLOB)) as E6 eqn:HEq6.
  assert (EA6 : forall n, (n < 128)%nat -> ew E6 n = ew E n) by (intros n Hnn; rewrite HEq6; apply ew_havoc_old; exact Hnn).
  assert (HE6 : lx_E cx fp E6) by (apply (lx_E_agree cx fp E E6 HE); intros n Hnn; apply EA6; unfold LA_EX in Hnn; lia).
  assert (HEI6 : img_env VAL A_LIM E6)
    by (rewrite HEq6; apply img_env_havoc; [exact HEI | unfold A_TEXT; rewrite length_map; cbn [length CLOB]; lia]).
  led_norm HS.
  (* check's return (0x80214): the cut K *)
  apply (HK POST cx fp E6 W ms5 md5 ly S r b fab pos); [|exact HS].
  split; [exact HFROM|]. split; [exact HB|]. split; [exact HEI6|]. split; [exact HE6|].
  split; [rewrite EA6 by lia; exact E84|]. split; [rewrite EA6 by lia; exact E96|]. split; [exact Hb|].
  split; [rewrite EA6 by lia; exact E99|]. split; [exact Hfab|].
  split; [rewrite EA6 by lia; exact E97|]. split; [rewrite EA6 by lia; exact E98|]. split; [exact Hpos|].
  split; [exact HJ5|]. split; [exact HFR|]. split; [exact Hmle|]. split; [exact Hbl|].
  exact Hchk.
Qed.
End a.
