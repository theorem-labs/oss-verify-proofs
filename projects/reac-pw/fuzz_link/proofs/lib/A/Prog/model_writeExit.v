(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 419 of its 453 lines of code are new or changed and 1890 lines of the source are left out. *)
(* model_write (fuzz_link.asan 0x88100) on image A: the EXIT segment of its walk, from the EXIT cut (+0x210) to the
   return (cut interface lib/A/Prog/model_writeDefs.v; listing
   (internal path) (internal record, sha256 2152d78b142c)):
     +0x210..+0x218  sd 0x45e0360e, 0(s11): the frame's magic retired
     +0x21c          beqz s2 (not taken: s2 = F >= 4096; the real-stack arm +0x238 is never reached)
     +0x220..+0x228  meta_fill_f5(s5, 0x80): the 128 shadow bytes of the 1024-byte class-4 frame
                     (LinkWalkSide.v aj_gx_set_shadow_at)
     +0x22c, +0x230  ld a0, 0x3f8(s2); sb zero, 0(a0): the inline release of the frame's flag byte
                     (LinkWalkSide.v paj_flag_to_plain_x: the journal loses the frame)
     +0x244..+0x280  a0 := s8; sp := s0 - 0x80; the twelve restores; sp += 0x80
     +0x284          ret
   The two runs are the plain engine's (no instrumented check in the segment). The first runs at the cut's
   registers with one region, F's first word; the second runs at meta_fill_f5's return registers with three: the
   prologue's saves [sp0 - 104, sp0) as the cut's base gives them, F's flag-address word and the flag byte. The Post
   is LinkWalkSide.v apost_side_gen: the cut's kept clause and the three runs' (each writes only the side frame the
   call took, its shadow and its flag byte), and the cut's result clause `mw_pf`, whose model block no step of the
   segment touches.

   Section hypotheses: LAWS (AR_laws), LV (LinkVals), TB (PcapSyms B), HSEGS (pa_segs = tfibsegs), MFF5
   (meta_fill_f5's contract, lib/A/Rt/SetShadow.v link_set_shadow_f5).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b YC88.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
index_of_c talk_c model_write_c model_writeDefs model_writeKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Definition MW_RET : Z := AF_model_write + 0x284.   (* `ret` *)

(* the words the second run's stack region holds: ra and s0, s1, s2 .. s11 at the entry, then the flag address *)
Definition mw_xs (regs : bvmap 5 word) (fl : Z) : list word :=
  [Z_to_bv 64 (raZ regs); getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21;
   getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26; getr regs 27; Z_to_bv 64 fl].

(* the saves, at the entry sp (atom 8 = s0): ra at -8 (atom 32), s0 at -16 (atom 33), s1 at -24, s2 .. s11 at
   -32 .. -104 (atoms 35 .. 44) *)
Definition mw_stk_region : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-104) 0 0 0
    [YP09.mkChunk (-8) (CVal 8 (SOff 32 0)); YP09.mkChunk (-16) (CVal 8 (SOff 33 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 34 0)); YP09.mkChunk (-32) (CVal 8 (SOff 35 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 36 0)); YP09.mkChunk (-48) (CVal 8 (SOff 37 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 38 0)); YP09.mkChunk (-64) (CVal 8 (SOff 39 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 40 0)); YP09.mkChunk (-80) (CVal 8 (SOff 41 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 42 0)); YP09.mkChunk (-96) (CVal 8 (SOff 43 0));
     YP09.mkChunk (-104) (CVal 8 (SOff 44 0))].
(* F's flag-address word (atom 18 = s2 = F) and the flag byte (atom 45) *)
Definition mw_flw_region : YP09.region :=
  YP09.mkRegion (Some 18%nat) 1016 1024 0 0 [YP09.mkChunk 1016 (CVal 8 (SOff 45 0))].
Definition mw_flag_region : YP09.region := YP09.mkRegion (Some 45%nat) 0 1 0 1 [].

Lemma mw_sbm_fds' : forall md md', same_but_materialized md md' -> m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof. intros md md' H. unfold same_but_materialized in H. rewrite H. apply wvb_fds_fs. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
(* meta_fill_f5 (0x55f7c): lib/A/Rt/SetShadow.v link_set_shadow_f5 *)
Hypothesis MFF5 : aset_shadow_realizes pa_segs B (pa_sigma LS___asan_set_shadow_f5) 0xf5.

Lemma mw_ms_eta : forall ms : machine_state,
  ms_fregs ms = fp_regs -> ms_svc_pending ms = None -> ms_resv ms = None -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H1 H2 H3 H4; cbn in *; subst; reflexivity. Qed.

Theorem mw_exit : mw_exit_obl SK B.
Proof.
intros cx fpos ly3 S3 W3 ms3 md3 HPX (Hpc & HB & HPF).
pose proof HPX as (HPRE & HRD & HP).
pose proof HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hro).
pose proof HB as HB0.
unfold mw_base in HB. cbv zeta in HB.
destruct HB as (Hrv & Hsv & Hrom & Hfrg & Hfcs & HJ3 & Hfrs3 & Hnin & Hfpos & HfS & Hperm & Hwit & Hfa &
  R2 & R9 & R8 & R18 & R27 & R21 & R23 & R19 & R20 & R3 & R4 & Hsra & Hsav & Hflw & HK & Hfds & Hfs).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0' & HB1' & HB2').
assert (HKv : MODEL_WRITE_AK = 8416) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
set (regs := mw_regs cx) in *.
set (lyc := mw_lyc cx) in *. set (Sc := mw_Sc cx) in *.
set (F := mw_F cx fpos) in *. set (FL := mw_FL cx fpos) in *. set (SH := mw_SH cx fpos) in *.
set (sp1 := mw_sp1 cx) in *.
assert (EF : F = frame_addr lyc 4 fpos) by reflexivity.
assert (EFL : FL = flag_addr lyc 4 fpos) by reflexivity.
assert (ESH : SH = SHADOW_OFF + F / 8) by reflexivity.
(* the frame, its flag and its shadow at the cut *)
pose proof (ajournal_gx_AR pa_segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
pose proof (ajournal_gx_AR pa_segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
assert (Hfin3 : In (4, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
destruct (aj_gx_frame_addr SK pa_segs B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 4 fpos HJ3) as (EF3 & EFL3).
destruct (aj_gx_frame_addr SK pa_segs B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 4 fpos HJ) as (EFc & EFLc).
assert (Fa3 : frame_addr ly3 4 fpos = F) by (rewrite EF3, EF, EFc; reflexivity).
assert (FLa3 : flag_addr ly3 4 fpos = FL) by (rewrite EFL3, EFL, EFLc; reflexivity).
destruct (frames_bounds pa_segs B LAWS ly3 S3 W3 (ms_mem ms3) md3 4 fpos HAR3 Hfin3) as (HF4096 & HFceil & HFapp).
rewrite Fa3 in HF4096, HFceil, HFapp. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
change (fs_frame_bytes 4) with 1024 in HFceil, HFapp.
pose proof (frame_al64 pa_segs B ly3 S3 W3 (ms_mem ms3) md3 4 fpos HAR3 Hfin3) as (HFa64 & _ & _). rewrite Fa3 in HFa64.
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 fpos HAR3 Hfin3) as (_ & _ & HFpres & HFSpres).
rewrite Fa3 in HFpres, HFSpres. change (fs_frame_bytes 4) with 1024 in HFpres, HFSpres.
change (1024 / 8) with 128 in HFSpres.
destruct (al_flag _ _ LAWS _ _ _ _ _ 4 fpos HAR3 Hfin3) as (HFLpres & HFLown & HFLapp & HFLceil).
rewrite FLa3 in HFLpres, HFLown, HFLapp, HFLceil. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLapp.
assert (HF8b : 0 <= F / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
(* the flag byte is not a byte of the frame *)
assert (HFLnF : ~ (F <= FL < F + 1024)) by (intros HH; exact (proj2 (HFpres FL HH) HFLown)).
(* the stack pointers *)
assert (Hspw : 0 <= mw_sp cx < 2 ^ 64) by (unfold mw_sp, spZ; apply getr_rng).
rewrite HKv in Hwlo.
assert (Esp : mw_sp cx = spZ regs) by reflexivity.
destruct (aj_gx_unpack SK pa_segs B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs 0 HJ ltac:(lia) Hal16
  ltac:(lia) Hwhi) as (_ & _ & _ & _ & HSTK & HXO & _ & _ & _ & _ & Hceil & H47).
destruct (sp1_facts (mw_sp cx - 128) ltac:(lia)
  ltac:(rewrite Esp; rewrite Zminus_mod, Hal16; reflexivity)) as (Hsp1r & Hsp1al32 & Hsp1al16).
change (32 * ((mw_sp cx - 128) / 32)) with sp1 in Hsp1r, Hsp1al32, Hsp1al16.
assert (Hsp1w : 0 <= sp1 < 2 ^ 64) by lia.
(* ---- the first run: +0x210 .. the call of meta_fill_f5 ---- *)
assert (Hms3 : restrict (w_H W3) ms3 =
   mkst (ms_regs ms3) (Z_to_bv 64 (BASE + MW_CUT_EXIT)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom pa_segs)).
{ rewrite (mw_ms_eta ms3 Hfrg Hsv Hrv Hfcs) at 1. rewrite Hpc, Hrom. rewrite restrict_mkst_fx. reflexivity. }
remember (Eimg (Ereg (ms_regs ms3) [])) as E1 eqn:HE1.
assert (HEI1 : img_env pa_val A_LIM E1) by (subst E1; apply Eimg_env).
assert (ER1 : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < A_TEXT)%nat ->
          ew E1 n = getr (ms_regs ms3) r)
  by (intros n r Hr Hn; subst E1; rewrite Eimg_low by exact Hn; exact (ew_Ereg_nat _ _ n r Hr)).
assert (HRO1 : regs_ok E1 sr_atoms (ms_regs ms3)) by (subst E1; apply regs_ok_Eimg_Ereg).
clear HE1.
assert (U18 : bv_unsigned (ew E1 18) = F)
  by (rewrite (ER1 18%nat 18%bv eq_refl ltac:(unfold A_TEXT; lia)), R18; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E1 27) = F)
  by (rewrite (ER1 27%nat 27%bv eq_refl ltac:(unfold A_TEXT; lia)), R27; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi pa_segs pa_val E1
    (mkSS MW_CUT_EXIT sr_atoms [YP09.mkRegion (Some 27%nat) 0 8 0 8 []] None
       (mkFacts [(18%nat, mkAF 4096 (2 ^ 47) 6); (27%nat, mkAF 4096 (2 ^ 47) 6)] [] []))
    (restrict (w_H W3) ms3)).
{ rewrite Hms3. apply pa_entry_st_ok_full.
  - exact HRO1.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U27.
    split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable pa_segs). apply (proj1 (HFpres (F + o) ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U18, U27. change (2 ^ 6) with 64. repeat split; first [exact HFa64 | lia]. }
assert (SHOK : sh_ok pa_segs (SLit SHADOW_OFF) (@nil shent) E1 (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
pose (RUNC := paj_run_call_plain_x SK B LAWS (mw_G cx) HGok (mw_XO cx) (mw_OUT cx)).
pose (RUNF := paj_flag_to_plain_x SK B LAWS (mw_G cx) HGok (mw_XO cx) (mw_OUT cx)).
lazymatch type of HS with
| st_ok_pi _ _ ?Ev ?ssx (restrict (w_H ?Wx) ?msx) =>
  lazymatch type of RUNC with context [sym_runN_pi ?tpi _ _] =>
    let r := eval vm_compute in (sym_runN_pi tpi FUEL ssx) in
    lazymatch r with (?ssf, PRS_call ?sf) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_runN_pi tpi FUEL ssx = (ssf, PRS_call sf)) by (vm_compute; reflexivity);
      eapply (RUNC Wx FUEL Ev ssx ssf sf msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI1 HS Hrun HJ3);
      clear Hrun
    end
  end
end.
{ cbn [ss_mem].
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U27 in Ha.
    left. apply (aj_gx_awr_frame SK pa_segs B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 4 fpos a HJ3
      (or_introl eq_refl)).
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Fa3. change (fs_frame_bytes 4) with 1024. lia. }
  apply awr_ok_x_nil. }
cbv beta. intros ms4 mat4 HS4 HJ4 HF4 HFr4 HG4.
cbn [ms_mem mkst] in HF4, HFr4, HG4.
pmkst HS4.
prreg HS4 (1%bv : bv 5) Q1. prreg HS4 (2%bv : bv 5) Q2. prreg HS4 (3%bv : bv 5) Q3. prreg HS4 (4%bv : bv 5) Q4.
prreg HS4 (10%bv : bv 5) Q10. prreg HS4 (11%bv : bv 5) Q11. prreg HS4 (8%bv : bv 5) Q8.
prreg HS4 (24%bv : bv 5) Q24. prreg HS4 (18%bv : bv 5) Q18.
rewrite (ER1 2%nat 2%bv eq_refl ltac:(unfold A_TEXT; lia)) in Q2.
rewrite (ER1 3%nat 3%bv eq_refl ltac:(unfold A_TEXT; lia)) in Q3.
rewrite (ER1 4%nat 4%bv eq_refl ltac:(unfold A_TEXT; lia)) in Q4.
rewrite (ER1 21%nat 21%bv eq_refl ltac:(unfold A_TEXT; lia)) in Q10.
rewrite (ER1 8%nat 8%bv eq_refl ltac:(unfold A_TEXT; lia)) in Q8.
rewrite (ER1 24%nat 24%bv eq_refl ltac:(unfold A_TEXT; lia)) in Q24.
rewrite (ER1 18%nat 18%bv eq_refl ltac:(unfold A_TEXT; lia)) in Q18.
assert (Usp4 : spZ (ms_regs ms4) = sp1) by (unfold spZ; rewrite Q2, R2; apply unsigned_lit_small; exact Hsp1w).
(* ---- +0x228: meta_fill_f5(SH, 128) ---- *)
eapply SRr_bind.
{ eapply (aj_gx_set_shadow_at SK pa_segs B LAWS pa_segs_low (pa_sigma LS___asan_set_shadow_f5) 0xf5 MFF5
    (mw_G cx) (mw_XO cx) (mw_OUT cx) W3 (ms_regs ms4) (ms_mem ms4) (mw_STK cx) (mw_sp0 cx) (mw_FP cx)
    (mw_ly cx) (mw_S cx) (mw_W0 cx) (mw_mem0 cx) (mw_md0 cx) ((4, fpos) :: mw_own cx) ly3 S3 _ (mw_k cx) 4 fpos
    SH 128 (getr (ms_regs ms4) 1) HGok HJ4 (or_introl eq_refl)).
  - rewrite Q10, R21. reflexivity.
  - rewrite Q11. reflexivity.
  - lia.
  - unfold shadow_addr. rewrite Fa3, ESH. unfold SHADOW_OFF. lia.
  - unfold shadow_addr. rewrite Fa3, ESH. change (fs_frame_bytes 4 / 8) with 128. unfold SHADOW_OFF. lia.
  - rewrite Usp4. exact Hsp1al16.
  - rewrite Usp4, Hes. lia.
  - rewrite Usp4. lia.
  - rewrite Q3, R3. exact Hgp.
  - rewrite Q4, R4. exact Htp.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Hset5 & Hun5 & Hpres5 & Hsm5).
pose proof (ajournal_gx_AR pa_segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5) as HAR5.
destruct (al_flag _ _ LAWS _ _ _ _ _ 4 fpos HAR5 Hfin3) as (HFLpres5 & _ & _ & _). rewrite FLa3 in HFLpres5.
(* what the first run and meta_fill_f5 kept: everything but F's first word and F's shadow *)
pose proof (kept_of_frame (segs := pa_segs) E1 _ (w_H W3) (ms_mem ms3) (ms_mem ms4) (fun a => F <= a < F + 8) HFr4
  ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
        repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
                rewrite ?U27 in HrrW; cbv beta; lia|]); destruct HinW)) as UN4.
assert (UN45 : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 8) -> ~ (SH <= a < SH + 128) ->
          aview pa_segs (w_H W3) mem5 a = aview pa_segs (w_H W3) (ms_mem ms3) a).
{ intros a Ha H1 H2. rewrite (Hun5 a Ha H2). exact (UN4 a Ha H1). }
(* ---- the second run: +0x22c .. +0x284, the release of the flag byte and the restores ---- *)
set (xs := mw_xs regs FL).
remember (Eimg (Ereg regs5 xs)) as E2 eqn:HE2.
assert (HEI2 : img_env pa_val A_LIM E2) by (subst E2; apply Eimg_env).
assert (ER2 : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < A_TEXT)%nat ->
          ew E2 n = getr regs5 r)
  by (intros n r Hr Hn; subst E2; rewrite Eimg_low by exact Hn; exact (ew_Ereg_nat _ _ n r Hr)).
assert (EX2 : forall j, (j < 14)%nat -> ew E2 (32 + j) = nth j xs (Z_to_bv 64 0))
  by (intros j Hj; subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs5 xs j)).
assert (HRO2 : regs_ok E2 sr_atoms regs5) by (subst E2; apply regs_ok_Eimg_Ereg).
clear HE2.
assert (G8 : getr regs5 8 = w64 (mw_sp cx))
  by exact (eq_trans (HP5 8 ltac:(unfold acallee_saved; lia)) (eq_trans Q8 R8)).
assert (G18 : getr regs5 18 = w64 F)
  by exact (eq_trans (HP5 18 ltac:(unfold acallee_saved; lia)) (eq_trans Q18 R18)).
assert (G24 : getr regs5 24 = getr (ms_regs ms3) 24)
  by exact (eq_trans (HP5 24 ltac:(unfold acallee_saved; lia)) Q24).
assert (G3 : getr regs5 3 = getr regs 3)
  by exact (eq_trans (HP5 3 ltac:(unfold acallee_saved; lia)) (eq_trans Q3 R3)).
assert (G4 : getr regs5 4 = getr regs 4)
  by exact (eq_trans (HP5 4 ltac:(unfold acallee_saved; lia)) (eq_trans Q4 R4)).
assert (U2_8 : bv_unsigned (ew E2 8) = mw_sp cx)
  by (rewrite (ER2 8%nat 8%bv eq_refl ltac:(unfold A_TEXT; lia)), G8; apply unsigned_lit_small; exact Hspw).
assert (U2_18 : bv_unsigned (ew E2 18) = F)
  by (rewrite (ER2 18%nat 18%bv eq_refl ltac:(unfold A_TEXT; lia)), G18; apply unsigned_lit_small; lia).
assert (E2_45 : ew E2 45 = Z_to_bv 64 FL) by exact (EX2 13%nat ltac:(lia)).
assert (U2_45 : bv_unsigned (ew E2 45) = FL) by (rewrite E2_45; apply unsigned_lit_small; lia).
(* the saves and the flag-address word at mem5 *)
assert (RW5 : forall a, mw_sp cx - 104 <= a < mw_sp cx - 7 \/ a = F + 1016 ->
          rdword (aview pa_segs (w_H W3) mem5) a = rdword (aview pa_segs (w_H W3) (ms_mem ms3)) a).
{ intros a Ha. apply mw_rdword_ext. intros i Hi. apply UN45; unfold SHADOW_OFF in *; lia. }
assert (CH : forall (j : nat) off (r : Z), (j < 13)%nat ->
          rdword (aview pa_segs (w_H W3) (ms_mem ms3)) (mw_sp cx + off) = Some (bv_unsigned (nth j xs (Z_to_bv 64 0))) ->
          mw_sp cx - 104 <= mw_sp cx + off < mw_sp cx - 7 ->
          YP09.chunk_ok pa_segs E2 (mrestrict (w_H W3) mem5) (mw_sp cx) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j off r Hj Hrd Hoff.
  apply (chunk_ok_val pa_segs E2 _ (mw_sp cx) off 8 (SOff (32 + j) 0) (bv_unsigned (nth j xs (Z_to_bv 64 0)))).
  - cbn [sv_denot]. rewrite (EX2 j ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (bv_unsigned_in_range 64 (nth j xs (Z_to_bv 64 0))) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    change (8 * Z.of_N 8) with 64. exact Hr.
  - cbn. lia.
  - apply (val_mem_of_rdword pa_segs). rewrite RW5 by lia. exact Hrd. }
assert (HS5 : st_ok_pi pa_segs pa_val E2
    (mkSS (AF_model_write + 0x22c) sr_atoms [mw_stk_region; mw_flw_region; mw_flag_region] None
       (mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (18%nat, mkAF 4096 (2 ^ 47) 6); (45%nat, mkAF 4096 (2 ^ 47) 0)]
          [] []))
    (restrict (w_H W3) (mkst regs5 (Z_to_bv 64 (BASE + (AF_model_write + 0x22c))) mem5 (seg_rom pa_segs)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact HRO2.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, mw_stk_region, mw_flw_region, mw_flag_region;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U2_8, ?U2_18, ?U2_45.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      pose proof (Hsav 0 ltac:(lia)) as V0. pose proof (Hsav 1 ltac:(lia)) as V1. pose proof (Hsav 2 ltac:(lia)) as V2.
      pose proof (Hsav 3 ltac:(lia)) as V3. pose proof (Hsav 4 ltac:(lia)) as V4. pose proof (Hsav 5 ltac:(lia)) as V5.
      pose proof (Hsav 6 ltac:(lia)) as V6. pose proof (Hsav 7 ltac:(lia)) as V7. pose proof (Hsav 8 ltac:(lia)) as V8.
      pose proof (Hsav 9 ltac:(lia)) as V9. pose proof (Hsav 10 ltac:(lia)) as V10. pose proof (Hsav 11 ltac:(lia)) as V11.
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (CH 0%nat (-8) 0 ltac:(lia)); [|lia].
        replace (mw_sp cx + -8) with (mw_sp cx - 8) by lia. rewrite Hsra. unfold xs, mw_xs. cbn [nth].
        unfold raZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
      * apply (CH 1%nat (-16) 0 ltac:(lia)); [replace (mw_sp cx + -16) with (mw_sp cx - 16 - 8 * 0) by lia;
          rewrite V0; reflexivity | lia].
      * apply (CH 2%nat (-24) 0 ltac:(lia)); [replace (mw_sp cx + -24) with (mw_sp cx - 16 - 8 * 1) by lia;
          rewrite V1; reflexivity | lia].
      * apply (CH 3%nat (-32) 0 ltac:(lia)); [replace (mw_sp cx + -32) with (mw_sp cx - 16 - 8 * 2) by lia;
          rewrite V2; reflexivity | lia].
      * apply (CH 4%nat (-40) 0 ltac:(lia)); [replace (mw_sp cx + -40) with (mw_sp cx - 16 - 8 * 3) by lia;
          rewrite V3; reflexivity | lia].
      * apply (CH 5%nat (-48) 0 ltac:(lia)); [replace (mw_sp cx + -48) with (mw_sp cx - 16 - 8 * 4) by lia;
          rewrite V4; reflexivity | lia].
      * apply (CH 6%nat (-56) 0 ltac:(lia)); [replace (mw_sp cx + -56) with (mw_sp cx - 16 - 8 * 5) by lia;
          rewrite V5; reflexivity | lia].
      * apply (CH 7%nat (-64) 0 ltac:(lia)); [replace (mw_sp cx + -64) with (mw_sp cx - 16 - 8 * 6) by lia;
          rewrite V6; reflexivity | lia].
      * apply (CH 8%nat (-72) 0 ltac:(lia)); [replace (mw_sp cx + -72) with (mw_sp cx - 16 - 8 * 7) by lia;
          rewrite V7; reflexivity | lia].
      * apply (CH 9%nat (-80) 0 ltac:(lia)); [replace (mw_sp cx + -80) with (mw_sp cx - 16 - 8 * 8) by lia;
          rewrite V8; reflexivity | lia].
      * apply (CH 10%nat (-88) 0 ltac:(lia)); [replace (mw_sp cx + -88) with (mw_sp cx - 16 - 8 * 9) by lia;
          rewrite V9; reflexivity | lia].
      * apply (CH 11%nat (-96) 0 ltac:(lia)); [replace (mw_sp cx + -96) with (mw_sp cx - 16 - 8 * 10) by lia;
          rewrite V10; reflexivity | lia].
      * apply (CH 12%nat (-104) 0 ltac:(lia)); [replace (mw_sp cx + -104) with (mw_sp cx - 16 - 8 * 11) by lia;
          rewrite V11; reflexivity | lia].
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val pa_segs E2 _ F 1016 8 (SOff 45 0) FL).
      * cbn [sv_denot]. rewrite E2_45, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      * cbn. lia.
      * cbn. lia.
      * apply (val_mem_of_rdword pa_segs). rewrite RW5 by lia. exact Hflw.
    + split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable pa_segs). replace (FL + o) with FL by lia. exact HFLpres5.
  - apply pairwise_disjoint_of_extents. unfold mw_stk_region, mw_flw_region, mw_flag_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2_8, U2_18, U2_45.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2_8, U2_18, U2_45. change (2 ^ 4) with 16. change (2 ^ 6) with 64. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat split; first [exact HFa64 | lia | unfold mw_sp; exact Hal16]. }
rewrite Q1.
lazymatch type of HS5 with
| st_ok_pi _ _ ?Ev ?ssx (restrict (w_H ?Wx) ?msx) =>
  lazymatch type of RUNF with context [sym_run_toN_pi ?tpi _ _ _] =>
    let r := eval vm_compute in (sym_run_toN_pi tpi FUEL MW_RET ssx) in
    lazymatch r with (?ssf, ?stf) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_run_toN_pi tpi FUEL MW_RET ssx = (ssf, stf)) by (vm_compute; reflexivity);
      eapply (RUNF Wx FUEL MW_RET Ev ssx ssf stf msx _ _ _ _ _ _ _ _ _ _ _ _ _ 4 fpos _ HEI2 HS5 Hrun I HJ5
        ltac:(lia));
      clear Hrun
    end
  end
end.
{ (* the run writes the flag byte only *)
  intros a Ha. cbn [ss_mem in_wrange] in Ha. destruct Ha as (r0 & Hin & Hr0). vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [subst r0; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr0;
          rewrite ?U2_8, ?U2_18, ?U2_45 in Hr0; first [lia | right; right; right; rewrite FLa3; lia] |]).
  destruct Hin. }
{ (* the flag byte holds 0 at the end of the run *)
  intros msr HSr.
  lazymatch type of HSr with st_ok_pi _ _ _ ?ssx _ =>
    let o := eval vm_compute in (nth_error (ss_mem ssx) 2) in
    lazymatch o with Some ?rr =>
      pose proof (st_ok_pi_region_nth _ _ _ 2 rr HSr ltac:(vm_compute; reflexivity)) as HRf
    end
  end.
  pose proof (field_of_region (segs := pa_segs) E2 (ms_mem msr) 45 FL _ _ _ _ _ 0 1%N (SLit 0) 0 HRf U2_45
    ltac:(cbn; repeat (first [left; reflexivity | right]))
    ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
  rewrite FLa3. specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite !Z.add_0_r in Hv. exact Hv. }
cbv beta. intros ms6 mat6 HS6 HJ6 HF6 HFr6 HG6.
cbn [ms_mem mkst] in HF6, HFr6, HG6.
(* ---- the return ---- *)
prreg HS6 (1%bv : bv 5) T1. prreg HS6 (10%bv : bv 5) T10.
assert (T1' : getr (ms_regs ms6) 1 = Z_to_bv 64 (raZ regs)) by (rewrite T1; exact (EX2 0%nat ltac:(lia))).
clear T1. rename T1' into T1.
rewrite (ER2 24%nat 24%bv eq_refl ltac:(unfold A_TEXT; lia)), G24 in T10.
assert (KEEP : aregs_preserved regs (ms_regs ms6)).
{ intros rr Hr. unfold acallee_saved in Hr.
  assert (Hc : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/
               rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
  clear Hr.
  repeat (destruct Hc as [Hc | Hc]; [subst rr;
    lazymatch goal with |- getr _ (Z_to_bv 5 ?c) = _ =>
      let Q := fresh "Q" in prreg HS6 (Z_to_bv 5 c) Q; rewrite Q;
      first [ exact (EX2 1%nat ltac:(lia)) | exact (EX2 2%nat ltac:(lia)) | exact (EX2 3%nat ltac:(lia))
            | exact (EX2 4%nat ltac:(lia)) | exact (EX2 5%nat ltac:(lia)) | exact (EX2 6%nat ltac:(lia))
            | exact (EX2 7%nat ltac:(lia)) | exact (EX2 8%nat ltac:(lia)) | exact (EX2 9%nat ltac:(lia))
            | exact (EX2 10%nat ltac:(lia)) | exact (EX2 11%nat ltac:(lia)) | exact (EX2 12%nat ltac:(lia))
            | refine (eq_trans (ER2 8%nat 8%bv eq_refl ltac:(unfold A_TEXT; lia)) (eq_trans G8 _));
              unfold w64, mw_sp, spZ; apply Z_to_bv_bv_unsigned
            | exact (eq_trans (ER2 3%nat 3%bv eq_refl ltac:(unfold A_TEXT; lia)) G3)
            | exact (eq_trans (ER2 4%nat 4%bv eq_refl ltac:(unfold A_TEXT; lia)) G4) ]
    end |]).
  subst rr. prreg HS6 (Z_to_bv 5 27) Q. rewrite Q. exact (EX2 12%nat ltac:(lia)). }
eapply (paj_ret_at (PL := PL_link) (PI := PI) W3 _ _ _ _ _ HS6 eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
rewrite T1. unfold raZ. rewrite Z_to_bv_bv_unsigned. unfold YK0s.ret_ok in Hraw. rewrite Hraw.
(* the kept clause, from the cut's *)
assert (Hslo_c : alloc_ceiling <= mw_sp cx - MODEL_WRITE_AK) by (rewrite HKv; lia).
set (Ea := fun a => mw_E cx a \/ aside_rng lyc 4 fpos a).
assert (HinF : forall a, F <= a < F + 1024 -> Ea a).
{ intros a Ha. right. left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes 4) with 1024.
  lia. }
assert (HinSH : forall a, SH <= a < SH + 128 -> Ea a).
{ intros a Ha. right. right. left. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite <- EF.
  change (fs_frame_bytes 4 / 8) with 128. rewrite ESH in Ha. lia. }
pose proof (kept_of_frame (segs := pa_segs) E2 _ (w_H W3) mem5 (ms_mem ms6) (fun a => a = FL) HFr6
  ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
        repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
                rewrite ?U2_8, ?U2_18, ?U2_45 in HrrW; cbv beta; lia|]); destruct HinW)) as UN6.
assert (K4 : akept pa_segs B lyc Sc (mw_W cx) (mw_memc cx) W3 (ms_mem ms4) (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) Ea).
{ eapply (akept_step SK pa_segs B LAWS pa_segs_low lyc Sc (mw_W cx) (mw_memc cx) (mw_mdc cx) W3 (ms_mem ms3) W3
    (ms_mem ms4) (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) Ea Ea (fun a => F <= a < F + 8) HARc Hslo_c ltac:(lia) HK).
  - intros a Ha Hn. exact (UN4 a Ha Hn).
  - intros a _ Hp. eapply apresent_grows; [exact HG4 | exact Hp].
  - intros a H; exact H.
  - intros a Ha. left. apply HinF. lia. }
assert (K5 : akept pa_segs B lyc Sc (mw_W cx) (mw_memc cx) W3 mem5 (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) Ea).
{ eapply (akept_step SK pa_segs B LAWS pa_segs_low lyc Sc (mw_W cx) (mw_memc cx) (mw_mdc cx) W3 (ms_mem ms4) W3
    mem5 (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) Ea Ea (fun a => SH <= a < SH + 128) HARc Hslo_c ltac:(lia) K4).
  - intros a Ha Hn. exact (Hun5 a Ha Hn).
  - intros a _ Hp. exact (Hpres5 a Hp).
  - intros a H; exact H.
  - intros a Ha. left. apply HinSH. exact Ha. }
assert (K6 : akept pa_segs B lyc Sc (mw_W cx) (mw_memc cx) W3 (ms_mem ms6) (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) Ea).
{ eapply (akept_step SK pa_segs B LAWS pa_segs_low lyc Sc (mw_W cx) (mw_memc cx) (mw_mdc cx) W3 mem5 W3
    (ms_mem ms6) (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) Ea Ea (fun a => a = FL) HARc Hslo_c ltac:(lia) K5).
  - intros a Ha Hn. exact (UN6 a Ha Hn).
  - intros a _ Hp. eapply apresent_grows; [exact HG6 | exact Hp].
  - intros a H; exact H.
  - intros a Ha. left. right. right. right. rewrite <- EFL. exact Ha. }
(* the model block at the end is the cut's *)
assert (MB : forall a, mw_E cx a -> aview pa_segs (w_H W3) (ms_mem ms6) a = aview pa_segs (w_H W3) (ms_mem ms3) a).
{ intros a HE. assert (Hns : ~ aside_rng lyc 4 fpos a) by (eapply mw_blk_not_side; eassumption).
  assert (HBF : mw_m cx <= a < mw_m cx + MD_SIZE /\ 0 <= a < 2 ^ 47)
    by (pose proof (mw_blk_facts SK B cx a HPX HE) as (_ & _ & H1 & _ & H3); split; assumption).
  destruct HBF as (Ha & Ha47).
  assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
  rewrite (UN6 a Ha64 ltac:(intros HH; apply Hns; right; right; rewrite <- EFL; exact HH)).
  apply UN45; [exact Ha64 | |].
  - intros HH. apply Hns. left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- EF.
    change (fs_frame_bytes 4) with 1024. lia.
  - intros HH. apply Hns. right. left. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite <- EF.
    change (fs_frame_bytes 4 / 8) with 128. rewrite ESH in HH. lia. }
destruct (mw_sbm_fds' _ _ Hsm5) as (Sf1 & Sf2).
destruct (wvb_fds_fs (m_vm_lazy md3) mat4 md3) as (Wf1 & Wf2).
destruct (wvb_fds_fs (m_vm_lazy md5) mat6 md5) as (Vf1 & Vf2).
destruct (wvb_fds_fs (m_vm_lazy (with_vm_backing (m_vm_lazy md5) mat6 md5)) mat'
  (with_vm_backing (m_vm_lazy md5) mat6 md5)) as (Uf1 & Uf2).
destruct Hwit as (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Eab1).
apply (apost_side_gen SK pa_segs B LAWS pa_segs_low MODEL_WRITE_AK 0 (mw_E cx)
  (mw_G cx) (mw_XO cx) (mw_OUT cx) (mw_STK cx) (mw_sp0 cx) (mw_FP cx) (mw_ly cx) (mw_S cx) (mw_W0 cx) (mw_mem0 cx)
  (mw_md0 cx) (mw_own cx) lyc Sc (mw_W cx) (mw_memc cx) (mw_mdc cx) (mw_k cx) regs (ms_regs ms6)
  ly3 (stack_free_state 4 fpos S3) W3 (ms_mem ms6) _ (mw_k cx) 4 fpos S1 W1 mem1 md1).
- exact HJ.
- apply (ajournal_gx_materialize pa_segs B LAWS pa_segs_low). exact HJ6.
- lia.
- rewrite Uf1, Vf1, Sf1, Wf1. exact Hfds.
- rewrite Uf2, Vf2, Sf2, Wf2. exact Hfs.
- exact KEEP.
- exact HAR1.
- exact Hfrs1.
- exact Eab1.
- exact K6.
- split.
  { apply (set_fs_trans S3 (stack_free_state 4 fpos S3) Sc); [exact (set_fs_of_exists S3 Sc HfS) |].
    apply stack_free_state_set_fs. }
  split.
  { rewrite stack_free_state_set_fs, ablocks_set_fs. exact Hperm. }
  (* the post's result *)
  intros mbs kbs tab nm al H1 H2 H3 H4 H5. cbv zeta.
  destruct (HPF mbs kbs tab nm al H1 H2 H3 H4 H5) as (Hrc & mbs' & Hm' & Hrest).
  split; [rewrite T10; exact Hrc|].
  exists mbs'. split; [|exact Hrest].
  apply (mw_amodel_move pa_segs (rdW W3 (ms_mem ms3))).
  + exact Hm'.
  + intros x Hx. apply (mbyte_of_aview_eq pa_segs). apply MB.
    unfold mw_E, mw_wr, model_write_awr. exists (mw_m cx, mw_m cx + MD_SIZE). split; [left; reflexivity|].
    cbn [fst snd]. exact Hx.
  + intros x Hx. eapply mw_blk_writable with (cx := cx) (own' := mw_own cx) (ly' := ly3)
      (S' := stack_free_state 4 fpos S3) (W' := W3) (m' := ms_mem ms6) (k' := mw_k cx).
    all: first
      [ exact LAWS | exact HSEGS | exact HPX | exact HJ6 | exact Hfa
      | intros y Hy; exact Hy
      | intros bb mm Hb; rewrite stack_free_state_set_fs, ablocks_set_fs;
        apply (Permutation_in (l := ablocks B lyc Sc)); [apply Permutation_sym; exact Hperm | exact Hb]
      | unfold mw_E, mw_wr, model_write_awr; exists (mw_m cx, mw_m cx + MD_SIZE); split; [left; reflexivity|];
        cbn [fst snd]; exact Hx ].
Qed.

About mw_exit.
Print Assumptions mw_exit.

End b.
End a.
