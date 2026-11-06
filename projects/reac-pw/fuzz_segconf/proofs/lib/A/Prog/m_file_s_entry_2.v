(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first segment of check_reply's walk (fuzz_command.asan, 0x86d78), from the
   entry to the memchr call 0x86ef8 (cr_s1 : CR_MC_stmt -> CR_ENTRY_stmt, lib/A/Prog/check_reply_m.v), ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close) at
   c8557374ad2e, with the class-1 side-stack frame steps of A/ACa2.v (cgif_raw_addframe) and A/AChf.v (flushFrame):
   the entry seed cr_entry (check_reply_k.v); a token run over the prologue to the call of __asan_stack_malloc_1; the
   call through aj_stack_malloc_atS; the state after it (the kept stack and GOT regions, the frame F as a0's atom 46,
   fresh atoms 58 = F's flag cell and 59 = F's shadow, the frame's header, tail and shadow, g_rec's GOT word and
   fields, the reply's NUL byte); a plain run over the frame set-up; the frame's shadow made read-only and a token run
   over the inline checks #1..#4 to 0x86ef8; there the registers and the regions' fields give cr_mid and cr_regs_at. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s1.v, with its module paths, module names and numbers changed; 375 of its 436 lines of code are new or changed and 466 lines of the source are left out. *)
(* S_MF_ENTRY, part 2: m_file's walk on fuzz_segconf.asan (image A, m_file at 0x85ebc) from the entry to the inner
   cut ENT_LBL at the label test 0x85ff4 (m_file_s_entry_c.v), lemma mf_entry_walk. From the entry seed
   (m_file_s_entry_1.v, mf_entry_seed): the prologue run 0x85ebc-0x85f2c, whose `beqz` on the use-after-return
   option cell the executor decides from AR's constant 1 (the real-stack fallback 0x85f4c-0x85f64 is dead and is not
   walked); the class-1 side-stack frame request at 0x85f30 (aj_stack_malloc_atS; every entry region kept across
   it); the frame's atoms, facts and regions; the run 0x85f34-0x85ff0 that writes the frame header and its 16
   shadow bytes; and the facts ENT_LBL asks, read back from the symbolic state (registers, low.i's shadow, the
   saved registers, the flag pointer, the mconf block's bytes).
   A lane of the G2 walk owner. Closed against G2 FINAL (the image-A owner's contracts 6f783602b5e3). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt PaArtOwn PaNoChain PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtPFShared RtPFCmd RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_entry_m m_file_s_entry_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_entry_1 m_file_s_entry_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require m_file_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.




(* a saved register below sp0, from the prologue's region (Some 2, -104 .. 0) of the symbolic state *)
Ltac mfsv Ev RG V ER :=
  lazymatch goal with
  |- val_mem _ _ (mv_sp ?v - 8 - 8 * Z.of_nat ?jj) 8 (bv_unsigned (getr ?regs (Z_to_bv 5 ?rz))) =>
    let off := eval vm_compute in (-8 - 8 * Z.of_nat jj) in
    let rn := eval vm_compute in (Z.to_nat rz) in
    let HV := fresh "HV" in
    pose proof (field_of_region_any Ev _ 2%nat _ _ _ _ _ _ off 8 (SOff rn 0) RG V
                  ltac:(cbn; tauto) ltac:(cbn; lia)) as HV;
    cbn [sv_denot N.to_nat Pos.to_nat Z.of_N] in HV;
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned in HV;
    rewrite (ER rn (Z_to_bv 5 rz) ltac:(lia) ltac:(vm_compute; reflexivity)) in HV;
    rewrite Z.mod_small in HV by (pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 rz))); cbn in *; lia);
    unfold mv_sp; replace (spZ (mv_regs v) - 8 - 8 * Z.of_nat jj) with (spZ (mv_regs v) + off) by (cbn; lia);
    exact HV
  end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SSP : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) SegInstA.gotwA SegInstA.guardA.
Hypothesis ASM : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
@RtFormat.asnprintf_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_snprintf)
  SegInstA.gotwA SegInstA.guardA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let errno_low := pal_env B TL.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

(* ===================================== the walk ===================================== *)
(* 0x85ebc .. 0x85f30: the prologue's stores, the realignment, the two GOT loads and the option cell's `beqz`
   (the cell is AR's constant 1, so the executor drops the real-stack fallback), to the frame request. *)
Lemma mf_entry_walk : forall (fx0 : YK11.FPState), ENT_LBL_F B -> MF_ENTRY_stmt (fx := fx0) B.
Proof.
intros fx0 LBL v CX HFRM.
pose proof CX as CX0. unfold mf_cx in CX.
destruct CX as (HPRE & HROOM & HROD & HLIT & HWD & HRL & HCAT & HSSPv & H10 & Hc64 & H11 & Ht64 & H12 & Hlp64
  & HMP & HEV).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HMP as (Hc0 & Hc16 & HMC & HCH & HCA & HCT & Hgenb & Hrefb & Hovfb & Ht0 & HTS & Hslen & HTH & HTA
  & HTM & HTD & HOS & HLAB).
pose proof (mf_mconf_gen _ _ _ HMC) as [HGEN HGENR].
destruct (al_const _ _ LAWS (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) HAR) as (Kcell & Kuar & Kgot & Kgu).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite (palf_got_uar B TLF) in Kgu.
destruct HCH as (bc & mcn & Hbcin & Hbclo & Hbchi).
destruct (al_blocks _ _ LAWS (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) bc mcn HAR Hbcin)
  as (Hbc16 & Hbc4096 & Hbcceil & Hbcapp & Hbcpres & _ & Hbcn).
pose proof (req_size_pos mcn ltac:(lia)) as [Hrq1 Hrq2].
destruct HTH as (bt & mtn & Hbtin & Hbtlo & Hbthi).
destruct (al_blocks _ _ LAWS (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) bt mtn HAR Hbtin)
  as (Hbt16 & Hbt4096 & Hbtceil & Hbtapp & Hbtpres & _ & Hbtn).
pose proof (req_size_pos mtn ltac:(lia)) as [Hrt1 Hrt2].
assert (HLP : 0 <= mf_lptr (mv_lp v) (mv_lab v) < 2 ^ 64).
{ unfold mf_lptr. destruct (mv_lab v); [lia | vm_compute; split; [discriminate | reflexivity]]. }
destruct (mf_entry_seed B TL TLF v CX0 HGEN ltac:(lia) HLP) as (HS & SHOK & UU).
cbn zeta in UU. destruct UU as (U2 & U33 & U10 & U11 & U34 & U35 & U36 & U37 & UBx & E32e).
set (E := MfE (mv_regs v) (as_uar_cell B) (mc_gen (mv_mc v)) (mf_b0 (mv_s v)) (mf_lptr (mv_lp v) (mv_lab v)))
  in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold MfE; apply Eimg_env).
(* the seed is at this file's ambient FP state; the statement is at fx0 (PaFx.v:74) *)
pose proof (st_ok_pi_restrict_xfx _ fx0 _ _ _ _ _ _ _ _ _ HS) as HS0. clear HS. rename HS0 into HS.
(* the run lemmas at fx0, the FP state of the statement *)
pose (RUN0 := paj_run (fx := fx0) B LAWS).
pose (RUNTO0 := paj_run_to (fx := fx0) B LAWS).
pose (BR0 := paj_branch (fx := fx0) (PI := PI)).
pose (RUNP0 := SRr_run_pi_AJ (fx := fx0) B LAWS).
pose (RUNTOP0 := SRr_run_to_pi_AJ (fx := fx0) B LAWS).
pose proof (ajournal_init SEGS B SegInstA.STK_m_file (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v))
  (mv_ly v) (mv_S v) (mv_W v) (mv_regs v) (mv_mem v) (mv_md v) (mv_ch v) HPRE) as HJ.
unfold MF_POST, cfg_at.
change (w64 (BASE + AF_m_file)) with (Z_to_bv 64 (BASE + AF_m_file)).
pose proof pa_segs_low as Hsegs.
pose proof YM05.alloc_ceiling_val as HAC.
destruct (mf_s1_bounds (spZ (mv_regs v)) Hal16) as (Hs1e & Hs1m & Hs1a & Hs1b).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
assert (Ho16 : (mf_s1 (spZ (mv_regs v)) - spZ (mv_regs v)) mod 16 = 0).
{ replace (mf_s1 (spZ (mv_regs v)) - spZ (mv_regs v)) with (- 288 - (spZ (mv_regs v) - 288) mod 32)
    by (unfold mf_s1; lia).
  destruct Hs1m as [Hm | Hm]; rewrite Hm; reflexivity. }
(* the prologue's stores, to the frame request 0x85f30 *)
paj_run_tok RUN0 HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn; rewrite HSTK; lia | cbn; lia |].
  eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn; rewrite HSTK; lia | cbn; lia |].
  eapply awr_ok_cons_stack_off with (n := 33%nat) (d := mf_s1 (spZ (mv_regs v)) - spZ (mv_regs v));
    [reflexivity | rewrite U33; lia | cbn; rewrite HSTK; unfold mf_s1 in *; lia
    | cbn; unfold mf_s1 in *; lia |].
  do 6 (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
rename HFr into HFr1. clear HF HG.
(* the constant cells at the state the prologue's run reached *)
pose proof (proj1 HJ) as HAR1.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR1) as (Kcell1 & Kuar1 & Kgot1 & Kgu1).
rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1. rewrite (palf_got_uar B TLF) in Kgu1.
(* 0x85f30: the class-1 side-stack frame request *)
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
pose proof (palf_sm B TLF 1 ltac:(right; left; reflexivity)) as SM1e.
change (cs_stack_malloc 1) with SS___asan_stack_malloc_1 in SM1e. rewrite SM1e.
pose proof (count_cid_le_length 1 (frames (mv_S v))) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 1 (ASM fx0) ltac:(lia)
    (mv_W v) (ms_regs msX) (ms_mem msX) SegInstA.STK_m_file (spZ (mv_regs v))
    (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) []
    (mv_ly v) (mv_S v) _ 0 (mf_s1 (spZ (mv_regs v)) - spZ (mv_regs v)) _ HJ) end.
  - unfold spZ at 1. rewrite R2, U33. lia.
  - exact Ho16.
  - lia.
  - rewrite HSTK; unfold ESTACK; lia.
  - first [rewrite R3; exact Hgp].
  - first [rewrite R4; exact Htp].
  - exact R1.
  - first [apply ret_ok_codeptr_v; [lia | reflexivity]].
  - first [change (fs_frames 1) with 8192; unfold sa_room in HROOM; lia]. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2
  & Hz & Hflag & HK & HJc & (fS2 & ES2)).
(* the frame F = frame_addr ly 1 fpos, its flag cell and its shadow *)
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS (mv_ly v) S2 (mv_W v) mem2 md2 1 fpos HAR2 Hfin2) as (HFal & HFapp & HFpres & HFSpres).
destruct (al_flag _ _ LAWS (mv_ly v) S2 (mv_W v) mem2 md2 1 fpos HAR2 Hfin2) as (_ & _ & HFLapp & HFLce).
destruct (frames_bounds SEGS B LAWS (mv_ly v) S2 (mv_W v) mem2 md2 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & _).
pose proof (frm_off_imgP B (mv_ly v) S2 (mv_W v) mem2 md2 1 fpos HAR2 Hfin2) as HFoff.
destruct (al_const _ _ LAWS (mv_ly v) S2 (mv_W v) mem2 md2 HAR2) as (Kcell2 & Kuar2 & Kgot2 & Kgu2).
rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2. rewrite (palf_got_uar B TLF) in Kgu2.
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
(* the state after the call: every region of the entry is kept *)
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H (mv_W v)) mem2) HP2 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict].
  destruct (al_blocks _ _ LAWS (mv_ly v) S2 (mv_W v) mem2 md2 bc mcn HAR2 ltac:(rewrite Eab; exact Hbcin))
    as (_ & _ & _ & _ & Hbcpres2 & _ & _).
  pose proof HK as (HK1 & HKb & HK3 & HK4 & HK5 & HK6).
  repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_stack_aj SEGS B);
      [exact HK | exact HJ2 | exact U2 | lia | rewrite HSTK; unfold mf_s1 in *; lia | lia | lia | lia].
  - eapply (region_kept_stack_aj SEGS B);
      [exact HK | exact HJ2 | exact U2 | lia | rewrite HSTK; unfold mf_s1 in *; lia | lia | lia | lia].
  - eapply (region_kept_stack_aj SEGS B);
      [exact HK | exact HJ2 | exact U33 | lia | rewrite HSTK; unfold mf_s1 in *; lia | lia | lia | lia].
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U10; intros a Ha.
    + apply (mbyte_of_aview SEGS). replace a with (bc + (a - bc)) by lia.
      apply (HKb bc mcn (a - bc));
        [exact Hbcin | unfold seg_spec.MC_GEN, seg_spec.SEG_M_SIZE in *; lia | intros []].
    + intros _. apply (apresent_writable SEGS).
      apply (proj1 (Hbcpres2 a ltac:(unfold seg_spec.MC_GEN, seg_spec.SEG_M_SIZE in *; lia))).
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U11; intros a Ha.
    + apply (mbyte_of_aview SEGS). replace a with (bt + (a - bt)) by lia.
      apply (HKb bt mtn (a - bt)); [exact Hbtin | lia | intros []].
    + intros _. exfalso. lia.
  - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
      [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
      | exact (val_mem_of_rdword SEGS (w_H (mv_W v)) (ms_mem ms) _ _ Kgot1)
      | exact (val_mem_of_rdword SEGS (w_H (mv_W v)) mem2 _ _ Kgot2) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
      [exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
      | exact (val_mem_of_rdword SEGS (w_H (mv_W v)) (ms_mem ms) _ _ Kcell1)
      | exact (val_mem_of_rdword SEGS (w_H (mv_W v)) mem2 _ _ Kcell2) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (as_uar_cell B));
      [exact (HEI (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
      | exact (val_mem_of_rdword SEGS (w_H (mv_W v)) (ms_mem ms) _ _ Kgu1)
      | exact (val_mem_of_rdword SEGS (w_H (mv_W v)) mem2 _ _ Kgu2) | lia].
  - apply (region_kept_val_at E _ _ 34%nat (as_uar_cell B) 4 1);
      [exact U34 | exact (val_mem_of_rd32 SEGS (w_H (mv_W v)) (ms_mem ms) _ _ Kuar1)
      | exact (val_mem_of_rd32 SEGS (w_H (mv_W v)) mem2 _ _ Kuar2) | lia]. }
specialize (HS2 HQ). clear HQ HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (Ev1 := havoc E 40 (map (getr regs2) CLOB)) in HS.
assert (HEI1 : img_env VAL A_LIM Ev1)
  by (subst Ev1; apply img_env_havoc; [exact HEI | rewrite length_map; unfold A_TEXT; cbn; lia]).
set (F := frame_addr (mv_ly v) 1 fpos) in *. set (FL := flag_addr (mv_ly v) 1 fpos) in *.
assert (E44a : ew Ev1 44 = Z_to_bv 64 F)
  by (subst Ev1; unfold havoc, CLOB; cbn [ew map nth Nat.ltb Nat.leb Nat.sub]; exact Ha0).
unfold in_app in HFapp, HFLapp. red in HFoff.
assert (HFb : 4096 <= F /\ F + 128 <= alloc_ceiling) by lia.
assert (HFLb : 4096 <= FL < alloc_ceiling) by lia.
assert (HF8 : 512 <= F / 8 < 2 ^ 44)
  by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
lazymatch type of HS with st_ok_pi _ _ _ ?ssv ?msv =>
  pose proof (st_ok_pi_havoc_hi 56 Ev1 ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS
    ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
remember (havoc Ev1 56 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) as Ev2 eqn:HEv2 in HS.
assert (HEI2 : img_env VAL A_LIM Ev2)
  by (rewrite HEv2; apply img_env_havoc; [exact HEI1 | unfold A_TEXT; cbn; lia]).
assert (AG : forall k, (k < 40)%nat -> ew Ev2 k = ew E k)
  by (intros k Hk; rewrite HEv2, ew_havoc_old by lia; subst Ev1; apply ew_havoc_old; lia).
assert (E44 : ew Ev2 44 = Z_to_bv 64 F) by (rewrite HEv2, ew_havoc_old by lia; exact E44a).
assert (E56 : ew Ev2 56 = Z_to_bv 64 FL)
  by (rewrite HEv2; exact (ew_havoc_new Ev1 56 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0)
        ltac:(cbn; lia))).
assert (E57 : ew Ev2 57 = Z_to_bv 64 (SB + F / 8))
  by (rewrite HEv2; exact (ew_havoc_new Ev1 56 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0)
        ltac:(cbn; lia))).
assert (E32' : ew Ev2 32 = Z_to_bv 64 SB) by (rewrite AG by lia; exact E32e).
assert (U44 : bv_unsigned (ew Ev2 44) = F) by (rewrite E44; apply unsigned_lit_small; lia).
assert (U56 : bv_unsigned (ew Ev2 56) = FL) by (rewrite E56; apply unsigned_lit_small; lia).
assert (U57 : bv_unsigned (ew Ev2 57) = SB + F / 8)
  by (rewrite E57; apply unsigned_lit_small; unfold SB; lia).
assert (RF : 0 <= F < 2 ^ 64) by lia.
(* the frame's alignment and its shadow's, and the alias of (F >> 3) + SB *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_fact Ev _ _ 44 (PTR 5) HS
    ltac:(unfold afact_ok, PTR; cbn [af_lo af_hi af_al2]; rewrite U44; change (2 ^ 5) with 32; lia)) as HS3 end.
clear HS. rename HS3 into HS.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HFd8 : F / 8 = 4 * (F / 32))
  by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia;
      reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_fact Ev _ _ 57 (mkAF (SB + 512) (SB + 2 ^ 44) 2) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U57; change (2 ^ 2) with 4; unfold SB;
          split; [lia|]; split;
          [rewrite HFd8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia;
           apply Z_mod_mult | lia])) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 44 32 57 F SB E44 RF E32' E57)) as HS3 end.
clear HS. rename HS3 into HS. mfnorm HS.
(* the frame and its shadow are apart from the two blocks, the stack and the image cells *)
pose proof (sep_block_frame SEGS B LAWS (mv_ly v) S2 (mv_W v) mem2 md2 bc mcn 1 fpos HAR2
  ltac:(rewrite Eab; exact Hbcin) Hfin2) as HdCF.
pose proof (sep_block_frame SEGS B LAWS (mv_ly v) S2 (mv_W v) mem2 md2 bt mtn 1 fpos HAR2
  ltac:(rewrite Eab; exact Hbtin) Hfin2) as HdTF.
unfold zdisjoint, frame_rng in HdCF, HdTF. cbn [fst snd] in HdCF, HdTF.
assert (ZF : mf_nam ((bc + req_size mcn <= F \/ F + 128 <= bc) /\ (bt + req_size mtn <= F \/ F + 128 <= bt)))
  by (unfold mf_nam; change (fs_frame_bytes 1) with 128 in *; lia).
unfold shadow_addr in HFSpres.
(* the numbers the region disjointness needs, with every disjunction boxed *)
pose proof YM05.alloc_ceiling_val as HACw.
assert (ZSw : alloc_ceiling + 8560 <= spZ (mv_regs v) /\ spZ (mv_regs v) <= 2 ^ 47 /\
              spZ (mv_regs v) - 304 <= mf_s1 (spZ (mv_regs v)) <= spZ (mv_regs v) - 288)
  by (rewrite HSTK in *; lia).
assert (ZBw : 4096 <= bc /\ bc + req_size mcn <= alloc_ceiling /\ bc <= mv_c v /\
              mv_c v + 9236 <= bc + mcn /\ mcn <= req_size mcn /\
              4096 <= bt /\ bt + req_size mtn <= alloc_ceiling /\ bt <= mv_t v /\
              mv_t v + Z.of_nat (length (mv_s v)) + 1 <= bt + mtn /\ mtn <= req_size mtn /\
              mf_nam (bc + req_size mcn <= 2147446784 \/ 17594333495296 <= bc) /\
              mf_nam (bt + req_size mtn <= 2147446784 \/ 17594333495296 <= bt))
  by (clear - Hbcapp Hbtapp Hbc4096 Hbcceil Hbclo Hbchi Hrq2 Hbt4096 Hbtceil Hbtlo Hbthi Hrt2;
      unfold mf_nam, in_app, kLowShadowBeg, kHighMemBeg, seg_spec.SEG_M_SIZE in *; lia).
assert (ZOw : 65536 <= VAL (A_OBJ 0) /\ VAL (A_OBJ 0) + 8 <= 6295552 /\
              65536 <= VAL (A_OBJ 1) /\ VAL (A_OBJ 1) + 8 <= 6295552 /\
              65536 <= VAL (A_OBJ 12) /\ VAL (A_OBJ 12) + 8 <= 6295552 /\
              65536 <= as_uar_cell B /\ as_uar_cell B + 8 <= 6295552)
  by (pose proof (pa_obj_img 0 ltac:(lia)); pose proof (pa_obj_img 1 ltac:(lia));
      pose proof (pa_obj_img 12 ltac:(lia)); pose proof (palf_uar_img B TLF);
      unfold kImgEnd in *; lia).
assert (ZFw : 4096 <= F /\ F + 128 <= alloc_ceiling /\ F mod 32 = 0 /\
              F = 32 * (F / 32) /\ F / 8 = 4 * (F / 32) /\
              mf_nam (F + 128 <= 2147446784 \/ 17594333495296 <= F))
  by (unfold mf_nam, kLowShadowBeg, kHighMemBeg in *; lia).
pose proof (palf_sep B TLF) as Hsepw. cbn [zseps zseps_from fst snd] in Hsepw.
lazymatch type of Hsepw with ?T => change (mf_nam T) in Hsepw end.
assert (ZFi : mf_nam (F + 128 <= 65536 \/ 6295552 <= F)) by (unfold mf_nam, off_img, kImgEnd in *; lia).
assert (ZCi2 : mf_nam (bc + req_size mcn <= 65536 \/ 6295552 <= bc))
  by (unfold mf_nam; pose proof (blk_off_imgP B (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) bc mcn HAR Hbcin)
        as Hq; unfold off_img, kImgEnd in *; lia).
assert (ZTi2 : mf_nam (bt + req_size mtn <= 65536 \/ 6295552 <= bt))
  by (unfold mf_nam; pose proof (blk_off_imgP B (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) bt mtn HAR Hbtin)
        as Hq; unfold off_img, kImgEnd in *; lia).
assert (V2 : bv_unsigned (ew Ev2 2) = spZ (mv_regs v)) by (rewrite AG by lia; exact U2).
assert (V33 : bv_unsigned (ew Ev2 33) = mf_s1 (spZ (mv_regs v))) by (rewrite AG by lia; exact U33).
assert (V10 : bv_unsigned (ew Ev2 10) = mv_c v) by (rewrite AG by lia; exact U10).
assert (V11 : bv_unsigned (ew Ev2 11) = mv_t v) by (rewrite AG by lia; exact U11).
assert (V34 : bv_unsigned (ew Ev2 34) = as_uar_cell B) by (rewrite AG by lia; exact U34).
assert (V0o : bv_unsigned (ew Ev2 (A_OBJ 0)) = VAL (A_OBJ 0))
  by exact (HEI2 (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (V1o : bv_unsigned (ew Ev2 (A_OBJ 1)) = VAL (A_OBJ 1))
  by exact (HEI2 (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (V12o : bv_unsigned (ew Ev2 (A_OBJ 12)) = VAL (A_OBJ 12))
  by exact (HEI2 (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
unfold A_OBJ in V0o, V1o, V12o, ZOw. cbn [Nat.add] in V0o, V1o, V12o, ZOw.
(* the frame's header words (FB + 0 .. FB + 23) and the sixteen shadow bytes are the run's write windows *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_add_region Ev ssv msv (YP09.mkRegion (Some 44%nat) 0 32 0 32 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
          rewrite U44; split; [lia|]; split; [lia|]; split; [|constructor];
          intros o Ho; apply (apresent_writable SEGS); exact (proj1 (HFpres (F + o) ltac:(lia))))
    ltac:(mfdj HACw ZSw ZBw ZOw ZFw ZFi ZCi2 ZTi2 ZF Hsepw)) as HS3 end.
clear HS. rename HS3 into HS. mfnorm HS.
(* the frame's sixteen shadow bytes *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_add_region Ev ssv msv (YP09.mkRegion (Some 57%nat) 0 16 0 16 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
          rewrite U57; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [|constructor];
          intros o Ho; apply (apresent_writable SEGS); rewrite SB_SHADOW_OFF;
          exact (proj1 (HFSpres o ltac:(lia))))
    ltac:(mfdj HACw ZSw ZBw ZOw ZFw ZFi ZCi2 ZTi2 ZF Hsepw)) as HS3 end.
clear HS. rename HS3 into HS. mfnorm HS.
(* 0x85f34-0x85ff0: the frame header and the sixteen shadow bytes, to the label test 0x85ff4 *)
paj_run_to_sh RUNTOP0 HS HJ2 (AF_m_file + 0x138).
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc0 ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc0 fr lyx own) end.
  eapply YCbq.awr_ok_cons_gen with (k := 57%nat) (b := SB + F / 8);
    [reflexivity | exact U57 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha;
     right; right; right; left; exists 1, fpos; split; [left; reflexivity|]; right;
     unfold in_zr, shadow_addr; cbn [fst snd]; change (fs_frame_bytes 1 / 8) with 16;
     fold F; unfold SB, SHADOW_OFF in *; lia |].
  eapply YCbq.awr_ok_cons_gen with (k := 44%nat) (b := F);
    [reflexivity | exact U44 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha;
     right; right; right; left; exists 1, fpos; split; [left; reflexivity|]; left;
     unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; fold F; lia |].
  eapply awr_ok_cons_stack; [reflexivity | exact V2 | cbn; rewrite HSTK; lia | cbn; lia |].
  eapply awr_ok_cons_stack; [reflexivity | exact V2 | cbn; rewrite HSTK; lia | cbn; lia |].
  eapply awr_ok_cons_stack_off with (n := 33%nat) (d := mf_s1 (spZ (mv_regs v)) - spZ (mv_regs v));
    [reflexivity | rewrite V33; lia | cbn; rewrite HSTK; unfold mf_s1 in *; lia
    | cbn; unfold mf_s1 in *; lia |].
  do 6 (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
(* ===== 0x85ff4: the cut ENT_LBL, read back from the symbolic state ===== *)
rename HFr into HFr2. clear HF HG.
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (26%bv : bv 5) P26.
prreg HS (27%bv : bv 5) P27.
(* the env's low atoms are the entry's registers *)
assert (ER : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew Ev2 n = getr (mv_regs v) r).
{ intros n r Hn Hr. rewrite AG by lia. unfold E, MfE. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat _ _ n r Hr). }
assert (W64 : forall (x : bv 64) z, bv_unsigned x = z -> 0 <= z < 2 ^ 64 -> x = w64 z)
  by (intros x0 z0 Hx0 Hz0; apply bv_eq; rewrite m_file_k.mf_w64_u by lia; exact Hx0).
pose proof (ER 12%nat (12%bv : bv 5) ltac:(lia) eq_refl) as ER12.
pose proof (ER 2%nat (2%bv : bv 5) ltac:(lia) eq_refl) as ER2.
assert (Hlp : getr (mv_regs v) 12 = w64 (mv_lp v)) by (rewrite H12; reflexivity).
assert (REGS : ent_lbl_regs B v fpos (ms_regs ms0)).
{ unfold ent_lbl_regs, mv_sp. fold F.
  split; [first [rewrite P2; apply W64; [exact V33 | unfold mf_s1 in *; lia]]|].
  split; [first [rewrite P3, (ER 3%nat (3%bv : bv 5) ltac:(lia) eq_refl); exact Hgp]|].
  split; [first [rewrite P4, (ER 4%nat (4%bv : bv 5) ltac:(lia) eq_refl); exact Htp]|].
  split; [first [rewrite P8, ER2; apply W64; [reflexivity | lia]]|].
  split; [first [rewrite P9; apply W64; [exact V33 | unfold mf_s1 in *; lia]]|].
  split; [rewrite P18; apply bv_eq; rewrite m_file_k.mf_w64_u by (unfold SHADOW_OFF; lia);
           rewrite E32', unsigned_lit_small by (unfold SB; lia); apply SB_SHADOW_OFF|].
  split; [first [rewrite P19; apply W64; [exact U44 | lia]]|].
  split; [first [rewrite P20, ER12; exact Hlp]|].
  split; [first [rewrite P21; apply W64; [exact V10 | lia]]|].
  split; [first [rewrite P22; apply W64; [rewrite V10; apply unsigned_lit_small; unfold seg_spec.MC_N; lia
                                         | unfold seg_spec.MC_N; lia]]|].
  split; [first [rewrite P23; apply W64; [rewrite V10; apply unsigned_lit_small; unfold seg_spec.MC_READING; lia
                                         | unfold seg_spec.MC_READING; lia]]|].
  split; [first [rewrite P24; apply W64; [exact U44 | lia]]|].
  split; [rewrite P26; apply bv_eq;
           rewrite m_file_k.mf_w64_u by (rewrite <- SB_SHADOW_OFF; unfold SB; lia);
           rewrite U57; rewrite SB_SHADOW_OFF; reflexivity|].
  rewrite P27; apply W64; [exact V11 | lia]. }
(* the bytes no run or call wrote: c's block and the flag word FB + 120 *)
set (KZ := fun a => ~ ((bc <= a < bc + req_size mcn) \/ (F + 120 <= a < F + 128))).
assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ KZ a ->
          rdW (mv_W v) (ms_mem ms0) a = rdW (mv_W v) mem2 a).
{ first [apply (kept_of_frame Ev2 _ (w_H (mv_W v)) mem2 (ms_mem ms0) KZ HFr2)].
  intros b wlo whi a Hin Ha. subst KZ. cbn beta. intros Hc.
  lazymatch type of Hin with In _ (windows ?rs) =>
    let w := eval vm_compute in (windows rs) in change (In (b, wlo, whi) w) in Hin end.
  revert Hc Ha. repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val];
    rewrite ?V2, ?V33, ?U44, ?U57; intros Hc Ha;
    revert HACw ZSw ZBw ZFw ZF Hc Ha; clear; unfold mf_nam, SB, mf_s1; intros; first [lia]|]).
  first [destruct Hin]. }
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a) ->
          rdW (mv_W v) (ms_mem ms) a = rdW (mv_W v) (mv_mem v) a).
{ first [apply (kept_of_frame E _ (w_H (mv_W v)) (mv_mem v) (ms_mem ms) (fun a => alloc_ceiling <= a) HFr1)].
  intros b wlo whi a Hin Ha.
  lazymatch type of Hin with In _ (windows ?rs) =>
    let w := eval vm_compute in (windows rs) in change (In (b, wlo, whi) w) in Hin end.
  revert Ha. repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val];
    rewrite ?U2, ?U33; intros Ha; revert HACw ZSw Ha; clear; unfold mf_s1; intros; first [lia]|]).
  first [destruct Hin]. }
assert (KC : forall a, bc <= a < bc + req_size mcn -> rdW (mv_W v) (ms_mem ms0) a = rdW (mv_W v) (mv_mem v) a).
{ intros a Ha. first [
  rewrite KR2 by (try lia; subst KZ; cbn beta; tauto);
  pose proof HK as (_ & HKb & _);
  replace a with (bc + (a - bc)) by lia; rewrite (HKb bc mcn (a - bc)) by (first [exact Hbcin | lia | intros []]);
  replace (bc + (a - bc)) with a by lia; apply KR1; lia]. }
assert (MCONF : sa_mconf (rdW (mv_W v) (ms_mem ms0)) (mv_c v) (mv_mc v)).
{ apply (m_file_k.mf_mconf_keep (mv_W v) (mv_W v) (mv_mem v) (ms_mem ms0)
           (fun a => ~ (bc <= a < bc + req_size mcn))); [| first [lia]
           | first [unfold seg_spec.SEG_M_SIZE; lia] | | exact HMC].
  - intros a Ha Hn. first [apply KC; lia].
  - intros a Ha Hn. first [apply Hn; unfold seg_spec.SEG_M_SIZE in *; lia]. }
(* the memory facts: the flag word (kept since the frame request), low.i's shadow bytes and the saved registers
   (the symbolic state's regions) *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  let r0 := eval vm_compute in (nth_error (ss_mem ssv) 0) in
  lazymatch r0 with Some ?rr =>
    pose proof (st_ok_pi_region_nth Ev ssv msv 0%nat rr HS ltac:(vm_compute; reflexivity)) as RG0 end;
  let r3 := eval vm_compute in (nth_error (ss_mem ssv) 3) in
  lazymatch r3 with Some ?rr =>
    pose proof (st_ok_pi_region_nth Ev ssv msv 3%nat rr HS ltac:(vm_compute; reflexivity)) as RG3 end end.
cbn [ms_mem restrict] in RG0, RG3.
assert (MEM : ent_lbl_mem v (mv_W v) (ms_mem ms0) fpos).
{ unfold ent_lbl_mem. fold F FL. split; [|split].
  - exact (mf_flag_keep (mv_W v) mem2 (ms_mem ms0) F FL
             (fun a Ha Hin => KR2 a Ha (fun H => H (or_intror Hin))) ltac:(lia) ltac:(lia) Hflag).
  - intros i Hi. unfold MF_LOW_OFF.
    rewrite <- SB_SHADOW_OFF. rewrite <- U57.
    exact (mf_low_bytes Ev2 _ _ RG0 eq_refl i Hi).
  - exact (mf_saved_bytes Ev2 _ _ (mv_regs v) RG3 V2 ER). }
(* the cut *)
pmkst HS.
change (AF_m_file + 0x138) with MF_LBL.
first [
  exact (LBL fx0 v (mv_ly v) S2 (mv_W v) (ms_regs ms0) (ms_mem ms0) _ fpos CX0 HFRM eq_refl
    (ex_intro _ fS2 ES2) Hfin2 ltac:(rewrite Eab; apply Permutation_refl) HJ2 REGS MEM MCONF
    (fun a Ha => KC a ltac:(unfold seg_spec.SEG_M_SIZE in *; lia)))].
Qed.
End e.
End f.
End d.
