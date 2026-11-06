(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its numbers changed; 399 of its 453 lines of code are new or changed and 3047 lines of the source are left out. *)
(* Stretch S7 of the footprint (_F) re-run of reac_box_catalogue_match.v (source commit d69f7c708f6, proved on
   FACTS ed6b6b7b0ab) by the same script over lib/Lib/StepF; image fuzz_ctrl v1.9.0 asan, ELF fuzz_ctrl.debug
   sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd; route (a) of 22:20Z; for the cgif-form
   walk C_reac_box_catalogue_match.v only.

   S7 = the silent stretch after the inline frame release (pc 0x847c0, the `j 0x84824` that follows the
   `sb zero,0(a0)` at 0x847bc) to the `ret` at 0x84860: `j`, `mv a0,s3`, `addi sp,s0,-128`, the twelve `ld` of the
   callee-saved registers from [S - 96, S), `addi sp,sp,128`, `ret` (the source's `do 17 step`), then the post.

   Source lemma: cm_exit (reac_box_catalogue_match.v:2899), which runs 0x84724 -> `ret` through the release. The
   source script runs THROUGH the release (the 1-byte store of 0 at the class-2 in-use flag byte), which the
   cgif-form walk performs itself (astack_free_law / frame_flag_lawP), so the script is split there. This file
   holds everything of cm_exit's side-stack arm from 0x847c0 on, verbatim: the rw_cells transport of the twelve
   saves, the 17 steps, and the whole post block (the munch / wmono join, fl_asan_cells, the addressable window,
   the fp block with cm_cls_keep1 / cm_cls_rel and the tls block with fl_tls_same). The only facts taken as
   premises are the ones the release event itself produces at the post-store memory M - the six write transports
   of cm_exit (wmono_write, cm_shadow_rw_write, mem_inv_store, stk_write x2, munch_write) and the released flag
   byte - and cm_exit_rel_after_store_F below derives exactly those from the pre-store memory, so nothing of
   cm_exit's text is left to no one.

   Arm: the walk takes only the side-stack arm (nn = 1), and 0x847c0 is reached only by that arm (the
   machine-stack arm branches at 0x84730 to 0x847c4 and joins at 0x84824), so this stretch is the fake-arm part by
   construction; no real-stack text is re-run here.

   Footprint: one rng premise, ExecF.rng RNG (S - 96) 96 - the only region the run reads or writes is the saves
   window [S - 96, S) its own rw_cells premise names (instruction fetch is not an access). StepF reported nothing
   further uncovered.

   cm_exit_rel_of_F re-derives the old lib.Lib Exec.evt form of this stretch with ExecF.rng_all.
   reac_box_catalogue_match.v is unchanged apart from comment text; no helper of it is re-proved (they are used as they stand, with the
   section arguments the source's Section Match discharge gives them).

   Route (C) `_on` forms (F-on-spec.md (a working note, not in this delivery), a Theorem Labs lane 2026-10-29; rule 24: no function proved: the premise of the
   already-proved stretch is narrowed, no new function): Section MatchF7On, placed before Section MatchF7, is
   Section MatchF7 with `SR : shadow_rw m` narrowed to
   `SR_on : shadow_rw_on (reac_box_catalogue_match_shadow_R f len S FS) m`. It re-proves cm_exit_rel_F,
   cm_exit_rel_after_store_F, cm_exit_rel_of_F and cm_release_store_F as `<name>_on` over
   reac_box_catalogue_match_on.v (cmInv_on, fk_facts_on, cm_stk_win_on, cm_stk_fr_on, cmPost_on): the premise
   `shadow_rw M` / `shadow_rw mcur` becomes the post form `forall P, shadow_rw_on P m -> shadow_rw_on P M` (that
   file's srw_post, carried across the release store by cm_post_srw_write), and the final post is cmPost_on, whose
   shadow conjunct is the same post form. cm_release_store_F does not depend on SR; its twin has its statement.
   Section MatchF7 keeps every statement byte-identical: cm_exit_rel_F and cm_exit_rel_after_store_F are now
   corollaries of their `_on` twins; cm_exit_rel_of_F (the check of cm_exit_rel_F at ExecF.RNG_all) and
   cm_release_store_F keep their proofs. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcBox RcBoxLib RcSynth RcParse
  RcMatch RcMatchLib RcAsan RcAsanLib RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib
  memcmp_c bcmp_wrap_c reac_ctrl_parse_c reac_box_model_block_c reac_box_model_block
  reac_box_catalogue_match_c reac_box_catalogue_match_lib reac_box_catalogue_match.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_catalogue_match_on.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* ==== Route (C): the `_on` forms (Section MatchF7's variables and hypotheses, SR narrowed to SR_on) ==== *)
Section MatchF7On.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (f len S FS : Z) (fb : list byte).
Hypothesis Rf : 0 <= f < 2^64.
Hypothesis Rlen : 0 <= len < 2^64.
Hypothesis RS : S < 2^64.
Hypothesis S16 : S mod 16 = 0.
Hypothesis HK : 9136 <= S.
Hypothesis ST : stk rsegs m (S - 9136) S.
Hypothesis Hfb : length fb = 50%nat.
Hypothesis SR_on : shadow_rw_on (reac_box_catalogue_match_shadow_R f len S FS) m.
Hypothesis HHM : HIGHMEM_BEG <= S - 9136.
Hypothesis HAE : S <= APPMEM_END.
Hypothesis AW : addressable m (S - 9136) 9136.
Hypothesis FP0 : fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - 9136) S
  (reac_box_catalogue_match_W S) (reac_box_catalogue_match_D f len).

(* The source's Section Match names at this section's variables (unchanged), and the re-proved names of
   reac_box_catalogue_match_on.v (on-api.md's argument prefixes, SR_on in the place of SR). *)
Local Abbreviation cmPost7_on :=
  (reac_box_catalogue_match_on.cmPost_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb).
Local Abbreviation cmInv7_on :=
  (reac_box_catalogue_match_on.cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS).
Local Abbreviation fk_facts7_on :=
  (reac_box_catalogue_match_on.fk_facts_on tp m f len S FS fb Rf Rlen S16 HK ST Hfb SR_on AW FP0).
Local Abbreviation cm_stk_win7_on :=
  (reac_box_catalogue_match_on.cm_stk_win_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS ST).
Local Abbreviation cm_stk_fr7_on :=
  (reac_box_catalogue_match_on.cm_stk_fr_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fb Rf Rlen S16 HK
     ST Hfb).
Local Abbreviation cmSAVES7 := (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10).
Local Abbreviation acl_fs7 := (acl_fs tp m f len S FS FP0).
Local Abbreviation CA_facts7 := (CA_facts f len S fb Rf Rlen S16 Hfb).
Local Abbreviation cm_CA_lo7 := (cm_CA_lo f len S fb Rf Rlen S16 Hfb).
Local Abbreviation cm_sh_add87 := (cm_sh_add8 f len S fb Rf Rlen Hfb).
Local Abbreviation sh_out_app7 := (sh_out_app f len S fb Rf Rlen Hfb).
Local Abbreviation cm_cls_keep17 := (cm_cls_keep1 f len S FS fb Rf Rlen HK Hfb).
Local Abbreviation cm_cls_rel7 := (cm_cls_rel f len S FS fb Rf Rlen HK Hfb).
Local Abbreviation cm_tls_cells7 := (cm_tls_cells f len S fb Rf Rlen Hfb).
Local Abbreviation cm_dj_in7 := (cm_dj_in f len S fb Rf Rlen HK Hfb).

(* cm_exit_rel_F over cmInv_on: M's shadow premise is the post form (every region shadow_rw_on P m stays so in M)
   and the post is cmPost_on, whose shadow conjunct is that same form. Section MatchF7's script, with fk_facts_on,
   cm_stk_win_on, cm_stk_fr_on for the old names. *)
Lemma cm_exit_rel_F_on : forall (RNG : footprint) (fr sp2 jj r : Z) (mc M : word -> option byte)
    (x1 y0 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
  r = want CM_T len fb ->
  cmInv7_on fr sp2 jj 1 mc ->
  munch [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
         (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] mc M ->
  wmono rsegs mc M -> mem_inv rsegs M -> (forall P, shadow_rw_on P m -> shadow_rw_on P M) ->
  stk rsegs M (S - 9136) S -> stk rsegs M FS (FS + FS_SIZE) ->
  mrd rsegs M (wa (fs_flag FS 2 jj)) = Some (Z_to_bv 8 0) ->
  rng RNG (S - 96) 96 ->
  evtF rsegs RNG cmPost7_on
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 (CA S)) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 fr) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x847c0) fc None M (seg_rom rsegs)).
Proof.
  intros RNG fr sp2 jj r mc M x1 y0 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6
    Er INVk MUc WMc Jmicur SRcur STwcur STfs1 RDfl RSAV.
  (* cm_exit's preamble, at nn = 1. *)
  pose proof (cm_stk_win7_on fr sp2 jj 1 mc INVk) as STw.
  pose proof (cm_stk_fr7_on fr sp2 jj 1 mc INVk) as STf.
  pose proof INVk as INV.
  destruct INV as (HFK & Jmu & Jwm & Jrm & Jmi & JAC & JSR & JFP & JTL & JAD & JAWX & SAV & FLG).
  pose proof HFK as HFKc.
  pose proof (fk_facts7_on fr sp2 jj 1 HFK) as (Fm8 & Fpos & Fhi & Fwv & Fap & Fsh & Fsp2).
  pose proof CA_facts7 as (CA32 & CAlo & CAhi). pose proof cm_CA_lo7 as (CAlo2 & CAhi2).
  pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'. pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
  destruct acl_fs7 as (FSpos & FSmod & FSgt & FShi & FSapp & _). unfold FS_SIZE in FShi.
  pose proof RS as RSb.
  destruct HFK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)]; [clear -En; lia|].
  assert (FRlo : FS + 36864 <= fr).
  { rewrite Ef. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
    change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. lia. }
  assert (FRhi2 : fr + 256 <= FS + 11571200).
  { rewrite Ef. unfold fs_frame, fs_B, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
    change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. change (2 ^ (14 - 2)) with 4096 in Hj. lia. }
  assert (SHIN : forall k, 0 <= k < 32 -> in_shadow (shadow_addr fr + k)).
  { intros k Hk. rewrite <- (cm_sh_add87 fr k Fm8). apply rt_app_shadow. apply FSapp.
    unfold FS_SIZE. lia. }
  assert (SBlo : 0 <= shadow_addr fr) by
    (pose proof (rt_shadow_bound (shadow_addr fr + 0) (SHIN 0 ltac:(lia))); lia).
  assert (SBhi : shadow_addr fr + 40 <= 2 ^ 64) by
    (pose proof (rt_shadow_bound (shadow_addr fr + 31) (SHIN 31 ltac:(lia))); lia).
  assert (FLo : FS <= fs_flag FS 2 jj /\ fs_flag FS 2 jj + 1 <= FS + 36864).
  { unfold fs_flag, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
    change (2 ^ 15) with 32768. change (2 ^ 13) with 8192. change (2 ^ 12) with 4096 in Hj. lia. }
  assert (OUTW : forall y, S - 9136 <= y < S ->
            outside [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
                     (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] (shadow_addr y)).
  { intros y Hy.
    assert (Hap : app_mem y) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; right; lia).
    pose proof (rt_app_shadow y Hap) as Hsh.
    cbn [outside]. split; [| split; [| split; [| exact I]]].
    - apply (sh_out_app7 (shadow_addr y) fr (fr + 8) Hsh).
      intros z Hz. apply FSapp. unfold FS_SIZE. lia.
    - pose proof (acl_sh_ge y (fr + 8 * 32) ltac:(lia)) as G.
      rewrite (cm_sh_add87 fr 32 Fm8) in G. lia.
    - apply (sh_out_app7 (shadow_addr y) (fs_flag FS 2 jj) (fs_flag FS 2 jj + 1) Hsh).
      intros z Hz. apply FSapp. unfold FS_SIZE. lia. }
  (* the twelve saves, transported to the memory the release left *)
  assert (SAFup : shadow_addr fr + 40 <= S - 96)
    by (unfold shadow_addr, ASAN_K in *; Z.div_mod_to_equations; lia).
  assert (SAVf : rw_cells rsegs M (S - 96) cmSAVES7)
    by (apply (rw_cells_transport rsegs _ mc M (S - 96) cmSAVES7 SAV MUc WMc);
        cbn [disjoint_from cells_size csize];
        split; [right; lia | split; [right; lia | split; [right; lia | exact I]]]).
  clear SAV. unfold cmSAVES in SAVf. replace (S - 96) with (S + -96) in SAVf by lia.
  (* 0x847c0 j 0x84824 ; mv a0,s3 ; addi sp,s0,-128 ; 12 x ld ; addi sp,sp,128 ; ret *)
  do 17 step.
  apply evtF_done. unfold reac_box_catalogue_match_on.cmPost_on. subst r.
  unfold aWc, aXs in Jmu.
  assert (FRin : fs_frame FS 2 0 <= fr /\ fr + 256 <= fs_frame FS 2 (fs_M 2)).
  { rewrite Ef. unfold fs_frame, fs_B, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
    change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. change (2 ^ 12) with 4096 in Hj. lia. }
  assert (FLin : fs_flag FS 2 0 <= fs_flag FS 2 jj /\ fs_flag FS 2 jj + 1 <= fs_flag FS 2 0 + fs_M 2).
  { unfold fs_flag, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
    change (2 ^ 12) with 4096 in Hj. lia. }
  assert (INframe : In (fs_frame FS 2 0, fs_frame FS 2 (fs_M 2)) (fp_w [0%nat;1%nat;2%nat] FS))
    by (apply in_flat_map; exists 2%nat; split; [cbn [In]; tauto | cbn [fp_w1 In]; tauto]).
  assert (INflag : In (fs_flag FS 2 0, fs_flag FS 2 0 + fs_M 2) (fp_w [0%nat;1%nat;2%nat] FS))
    by (apply in_flat_map; exists 2%nat; split; [cbn [In]; tauto | cbn [fp_w1 In]; tauto]).
  assert (INsh : In (shadow_addr (fs_frame FS 2 0), shadow_addr (fs_frame FS 2 (fs_M 2)))
                    (fp_w [0%nat;1%nat;2%nat] FS))
    by (apply in_flat_map; exists 2%nat; split; [cbn [In]; tauto | cbn [fp_w1 In]; tauto]).
  assert (SG1f : shadow_addr (fs_frame FS 2 0) <= shadow_addr fr) by (apply acl_sh_ge; destruct FRin; lia).
  assert (SG2f : shadow_addr fr + 32 <= shadow_addr (fs_frame FS 2 (fs_M 2))).
  { pose proof (cm_sh_add87 fr 32 Fm8) as E. replace (fr + 8 * 32) with (fr + 256) in E by lia. rewrite <- E.
    apply acl_sh_ge. destruct FRin; lia. }
  assert (SUB : sub_fp [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
                        (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)]
                  ([(S - 9136, S)] ++ fp_w [0%nat;1%nat;2%nat] FS
                     ++ [(shadow_addr (S - 9136), shadow_addr S)])).
  { intros x Hx. cbn [app outside] in Hx. destruct Hx as (_ & Hx2).
    apply cm_out_app in Hx2. destruct Hx2 as (Hxfp & _). cbn [outside].
    split; [| split; [| split; [| exact I]]].
    - intros Hcc. apply (out_in _ _ _ x Hxfp INframe). destruct FRin as (A1 & A2). lia.
    - intros Hcc. apply (out_in _ _ _ x Hxfp INsh). lia.
    - intros Hcc. apply (out_in _ _ _ x Hxfp INflag). destruct FLin as (B1 & B2). lia. }
  exists u0, u1, u2, y1, y2, y3, y4, y5, y6, y7, u3, u4, u5, u6, M.
  split; [reflexivity|].
  split; [eapply (munch_trans _ m mc); [exact Jmu | eapply munch_weaken; [exact SUB | exact MUc]] |].
  split; [eapply (wmono_trans rsegs m mc); [exact Jwm | exact WMc] |].
  split; [exact Jmicur |].
  split; [exact STwcur |].
  split; [ eapply fl_asan_cells; [exact JAC | exact MUc |];
           intros x Hx; unfold RT_LO, RT_HI, ASAN_GT in *; cbn [outside];
           split; [ clear -Hx FSgt FRlo; unfold ASAN_GT in *; lia
                  | split; [ clear -Hx SBlo Fpos; unfold shadow_addr, ASAN_K in *;
                             Z.div_mod_to_equations; lia
                           | split; [ clear -Hx FSgt FLo; unfold ASAN_GT in *; lia | exact I ] ] ] |].
  split; [exact SRcur |].
  assert (M2 : fs_M 2 = 4096) by reflexivity.
  assert (FLv : fs_flag FS 2 jj = FS + 28672 + jj)
    by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; change (2 ^ 15) with 32768;
        change (2 ^ 13) with 8192; lia).
  pose proof FRin as (FRa & FRb). pose proof FLin as (FLa & FLb).
  assert (BELh : forall x, FS <= x < FS + 36864 -> x <> fs_flag FS 2 jj ->
            outside [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
                     (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] x).
  { intros x Hx Hne. cbn [outside]. split; [lia | split; [| split; [lia | exact I]]].
    intros [A B]. apply (acl_app_not_shadow x); [apply FSapp; unfold FS_SIZE; lia |].
    pose proof (SHIN (x - shadow_addr fr) ltac:(lia)) as HS.
    replace (shadow_addr fr + (x - shadow_addr fr)) with x in HS by lia. exact HS. }
  assert (DJall : forall DT TS C T DB kk, asan_tls_cells mc (bv_unsigned tp) DT TS C T DB kk ->
            fp_dj [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
                   (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)]
                  (fp_tls (bv_unsigned tp) DT TS C T DB kk)).
  { intros DT TS C T DB kk HTx. pose proof (JTL DT TS C T DB kk HTx) as JTLi. unfold aXs in JTLi.
    constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd].
    - apply (cm_dj_in7 _ _ (fs_frame FS 2 0) (fs_frame FS 2 (fs_M 2)) fr (fr + 8) JTLi);
        [apply in_or_app; left; exact INframe | destruct FRin; lia | destruct FRin; lia].
    - apply (cm_dj_in7 _ _ (shadow_addr (fs_frame FS 2 0)) (shadow_addr (fs_frame FS 2 (fs_M 2)))
               (shadow_addr fr) (shadow_addr fr + 32) JTLi); [apply in_or_app; left; exact INsh | lia | lia].
    - apply (cm_dj_in7 _ _ (fs_flag FS 2 0) (fs_flag FS 2 0 + fs_M 2) (fs_flag FS 2 jj) (fs_flag FS 2 jj + 1)
               JTLi); [apply in_or_app; left; exact INflag | destruct FLin; lia | destruct FLin; lia]. }
  split.
  { split; [lia | split; [lia | split; [unfold APPMEM_END; lia |]]].
    intros i Hi.
    exact (cm_ab_keep _ mc M _ (JAWX (S - 9136 + i) ltac:(lia) ltac:(lia)) MUc
             (OUTW (S - 9136 + i) ltac:(lia))). }
  split.
  { destruct JFP as (DT & TS & C & T & DB & kk & HTx & HTP & HP & H88 & H96 & HCL & HFSb & HAb & HWd & HDd).
    pose proof (DJall DT TS C T DB kk HTx) as DJ.
    exists DT, TS, C, T, DB, kk.
    split; [eapply cm_tls_cells7; [exact HTx | exact MUc | exact DJ]|].
    split; [eapply fl_bytes; [exact HTP | exact MUc | intros x Hx; rewrite length_le8 in Hx;
             eapply fl_dj_out; [exact DJ | cbn [fp_tls In]; do 2 right; left; reflexivity | lia]]|].
    split; [unfold fs_place in *; destruct HP as (P1 & P2 & P3 & P4 & P5);
             split; [exact P1|]; split; [exact P2|]; split; [exact P3|]; split; [exact P4 | exact STfs1]|].
    split; [eapply fl_bytes; [exact H88 | exact MUc | intros x Hx; rewrite length_le8 in Hx; apply BELh; lia]|].
    split; [eapply fl_bytes; [exact H96 | exact MUc | intros x Hx; cbn [length] in Hx; apply BELh; lia]|].
    split.
    { apply Forall_cons_iff in HCL as [HC0 HCL]. apply Forall_cons_iff in HCL as [HC1 HCL].
      apply Forall_cons_iff in HCL as [HC2 _].
      constructor; [exact (cm_cls_keep17 _ mc M 0%nat (fs_flag FS 2 jj) ltac:(lia) ltac:(lia) BELh MUc HC0)|].
      constructor; [exact (cm_cls_keep17 _ mc M 1%nat (fs_flag FS 2 jj) ltac:(lia) ltac:(lia) BELh MUc HC1)|].
      constructor; [exact (cm_cls_rel7 _ mc M jj Hj BELh MUc RDfl HC2) | constructor]. }
    split; [exact HFSb|]. split; [exact HAb|]. split; [exact HWd | exact HDd]. }
  intros DT TS C T DB k HTM.
  destruct JFP as (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _).
  pose proof (JTL DT0 TS0 C0 T0 DB0 k0 HT0) as JTLi0.
  pose proof (DJall DT0 TS0 C0 T0 DB0 k0 HT0) as DJ0.
  assert (Hc : Forall (fun d => forall x, fst d <= x < snd d ->
                 outside [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
                          (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] x)
               (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0)).
  { apply Forall_forall. intros [a b] Hin x Hx. eapply fl_dj_out; [exact DJ0 | exact Hin | cbn [fst snd] in Hx; lia]. }
  destruct (fl_tls_same mc M _ (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HTM MUc Hc)
    as (E1 & E2 & E3 & E4 & E5 & E6).
  subst DT0 TS0 C0 T0 DB0 k0. exact JTLi0.
Qed.

(* cm_exit_rel_after_store_F over cmInv_on: mcur's shadow premise is the post form, carried across the release
   store by cm_post_srw_write (in the place of cm_shadow_rw_write); the other five transports and the released
   byte's value are the old script's. *)
Lemma cm_exit_rel_after_store_F_on : forall (RNG : footprint) (fr sp2 jj r : Z) (mc mcur : word -> option byte)
    (x1 y0 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
  r = want CM_T len fb ->
  cmInv7_on fr sp2 jj 1 mc ->
  munch [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
         (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] mc mcur ->
  wmono rsegs mc mcur -> mem_inv rsegs mcur -> (forall P, shadow_rw_on P m -> shadow_rw_on P mcur) ->
  stk rsegs mcur (S - 9136) S -> stk rsegs mcur FS (FS + FS_SIZE) ->
  store_ok rsegs mcur (wa (fs_flag FS 2 jj)) 1 = true ->
  rng RNG (S - 96) 96 ->
  evtF rsegs RNG cmPost7_on
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 (CA S)) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 fr) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x847c0) fc None
        (write_to_mem mcur (wa (fs_flag FS 2 jj)) (le1 (Z_to_bv 64 0))) (seg_rom rsegs)).
Proof.
  intros RNG fr sp2 jj r mc mcur x1 y0 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6
    Er INVk MUc WMc Jmicur SRcur STwcur STfs1 SOKfl RSAV.
  pose proof INVk as INV.
  destruct INV as (HFK & _ & _ & _ & _ & _ & _ & JFP & _).
  pose proof (fk_facts7_on fr sp2 jj 1 HFK) as (Fm8 & Fpos & Fhi & Fwv & Fap & Fsh & Fsp2).
  pose proof CA_facts7 as (CA32 & CAlo & CAhi). pose proof cm_CA_lo7 as (CAlo2 & CAhi2).
  pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'. pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
  destruct acl_fs7 as (FSpos & FSmod & FSgt & FShi & FSapp & _). unfold FS_SIZE in FShi.
  destruct HFK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)]; [clear -En; lia|].
  assert (FLo : FS <= fs_flag FS 2 jj /\ fs_flag FS 2 jj + 1 <= FS + 36864).
  { unfold fs_flag, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
    change (2 ^ 15) with 32768. change (2 ^ 13) with 8192. change (2 ^ 12) with 4096 in Hj. lia. }
  (* cm_exit's transports of the release store, the shadow one in the post form *)
  apply (wmono_write rsegs mc mcur (wa (fs_flag FS 2 jj)) (le1 (Z_to_bv 64 0))) in WMc.
  apply (reac_box_catalogue_match_on.cm_post_srw_write m mcur (wa (fs_flag FS 2 jj)) (le1 (Z_to_bv 64 0)))
    in SRcur.
  apply (mem_inv_store rsegs mcur (wa (fs_flag FS 2 jj)) (le1 (Z_to_bv 64 0))) in Jmicur;
    [| rewrite length_le1; exact SOKfl].
  apply (stk_write rsegs mcur (S - 9136) S (fs_flag FS 2 jj) (le1 (Z_to_bv 64 0))) in STwcur;
    [| unfold FS_SIZE in *; lia | rewrite length_le1; lia].
  apply (munch_write _ mc mcur (fs_flag FS 2 jj) (le1 (Z_to_bv 64 0))) in MUc;
    [| unfold FS_SIZE in *; lia | rewrite length_le1; lia
     | rewrite length_le1; cbn [inside]; right; right; left; split; lia].
  apply (stk_write rsegs mcur FS (FS + FS_SIZE) (fs_flag FS 2 jj) (le1 (Z_to_bv 64 0))) in STfs1;
    [| unfold FS_SIZE in *; lia | rewrite length_le1; lia].
  assert (RDfl : mrd rsegs (write_to_mem mcur (wa (fs_flag FS 2 jj)) (le1 (Z_to_bv 64 0)))
                   (wa (fs_flag FS 2 jj)) = Some (Z_to_bv 8 0)).
  { pose proof (bytes_at_write_same rsegs mcur (fs_flag FS 2 jj) (le1 (Z_to_bv 64 0)) ltac:(lia)
                  ltac:(rewrite length_le1; unfold FS_SIZE in *; lia)) as BW.
    destruct BW as (_ & _ & BW). specialize (BW 0%nat ltac:(rewrite length_le1; lia)).
    replace (fs_flag FS 2 jj + Z.of_nat 0) with (fs_flag FS 2 jj) in BW by lia.
    rewrite BW. reflexivity. }
  exact (cm_exit_rel_F_on RNG fr sp2 jj r mc _ x1 y0 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6
           Er INVk MUc WMc Jmicur SRcur STwcur STfs1 RDfl RSAV).
Qed.

(* cm_exit_rel_of_F over cmInv_on: the old evt form of cm_exit_rel_F_on, with ExecF.rng_all. *)
Lemma cm_exit_rel_of_F_on : forall (fr sp2 jj r : Z) (mc M : word -> option byte)
    (x1 y0 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
  r = want CM_T len fb ->
  cmInv7_on fr sp2 jj 1 mc ->
  munch [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
         (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] mc M ->
  wmono rsegs mc M -> mem_inv rsegs M -> (forall P, shadow_rw_on P m -> shadow_rw_on P M) ->
  stk rsegs M (S - 9136) S -> stk rsegs M FS (FS + FS_SIZE) ->
  mrd rsegs M (wa (fs_flag FS 2 jj)) = Some (Z_to_bv 8 0) ->
  evt rsegs cmPost7_on
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 (CA S)) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 fr) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x847c0) fc None M (seg_rom rsegs)).
Proof.
  intros fr sp2 jj r mc M x1 y0 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6
    Er INVk MUc WMc Jmicur SRcur STwcur STfs1 RDfl.
  pose proof STwcur as (Slo & Shi & _).
  eapply evtF_evt, (cm_exit_rel_F_on RNG_all); try eassumption.
  apply rng_all; lia.
Qed.

(* cm_release_store_F's twin: the release store takes no shadow premise, so the statement and the script are
   Section MatchF7's (the glue's `_on` walk cites this name). *)
Lemma cm_release_store_F_on : forall (RNG : footprint) (fr sp2 jj r : Z) (mc mcur : word -> option byte)
    (x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word) (Q : machine_state -> Prop),
  rng RNG (fs_flag FS 2 jj) 1 ->
  store_ok rsegs mcur (wa (fs_flag FS 2 jj)) 1 = true ->
  evtF rsegs RNG Q
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 (CA S)) (wa (fs_flag FS 2 jj))
             y1 y2 y3 y4 y5 y6 y7 (Z_to_bv 64 fr) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x847c0) fc None (write_to_mem mcur (wa (fs_flag FS 2 jj)) (le1 (Z_to_bv 64 0)))
        (seg_rom rsegs)) ->
  evtF rsegs RNG Q
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 (CA S)) (wa (fs_flag FS 2 jj))
             y1 y2 y3 y4 y5 y6 y7 (Z_to_bv 64 fr) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x847bc) fc None mcur (seg_rom rsegs)).
Proof.
  intros RNG fr sp2 jj r mc mcur x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 Q RFL SOK K.
  rewrite (le1_lit_byte 0) in K.
  step.
  exact K.
Qed.

End MatchF7On.

(* reac_box_catalogue_match.v's Section Match variables, and the hypotheses cm_exit itself takes (its four callee
   contracts, and the premises only the earlier stretches use, are not needed here). *)
Section MatchF7.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (f len S FS : Z) (fb : list byte).
Hypothesis Rf : 0 <= f < 2^64.
Hypothesis Rlen : 0 <= len < 2^64.
Hypothesis RS : S < 2^64.
Hypothesis S16 : S mod 16 = 0.
Hypothesis HK : 9136 <= S.
Hypothesis ST : stk rsegs m (S - 9136) S.
Hypothesis Hfb : length fb = 50%nat.
Hypothesis SR : shadow_rw m.
Hypothesis HHM : HIGHMEM_BEG <= S - 9136.
Hypothesis HAE : S <= APPMEM_END.
Hypothesis AW : addressable m (S - 9136) 9136.
Hypothesis FP0 : fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - 9136) S
  (reac_box_catalogue_match_W S) (reac_box_catalogue_match_D f len).

(* The source's Section Match names at this section's variables (the discharge order is the source's), and the
   `_on` forms the corollaries cite (SR_on7: SR's restriction to R). *)
Notation cmPost7 := (cmPost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb).
Notation cmInv7 := (cmInv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS).
Local Abbreviation cmPost7_on :=
  (reac_box_catalogue_match_on.cmPost_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb).
Local Abbreviation cmInv7_on :=
  (reac_box_catalogue_match_on.cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS).
Local Abbreviation SR_on7 := (shadow_rw_on_of_shadow_rw (reac_box_catalogue_match_shadow_R f len S FS) m SR).

(* The corollaries' conversions (F-on-spec.md, "Corollaries"): the old invariant gives cmInv_on (its shadow conjunct
   restricted to R), and cmPost_on gives cmPost (shadow_rw m' from the post form at the whole shadow, SR). *)
Lemma cm_inv_to_on : forall fr sp2 jj nn mc, cmInv7 fr sp2 jj nn mc -> cmInv7_on fr sp2 jj nn mc.
Proof.
  intros fr sp2 jj nn mc (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6
           (conj (shadow_rw_on_of_shadow_rw (reac_box_catalogue_match_shadow_R f len S FS) mc A7) A8))))))).
Qed.

Lemma cmPost_of_on : forall ms, cmPost7_on ms -> cmPost7 ms.
Proof.
  intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    E & MU & WM & MI' & STw & AC' & SRp & REST).
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  exact (conj E (conj MU (conj WM (conj MI' (conj STw (conj AC'
           (conj (shadow_rw_of_on_all m' (SRp (fun _ => True) (shadow_rw_on_of_shadow_rw (fun _ => True) m SR)))
              REST))))))).
Qed.

(* S7: 0x847c0 -> the `ret` at 0x84860, side-stack arm. The state is cm_exit's state at 0x84724 with nn = 1
   (s2 = fr, s3 = r, s6 = shadow_addr fr, s7 = fr, sp = sp2, s0 = S, s1 = CA), a0 free (it holds the flag pointer
   the `ld a0,248(s2)` at 0x847b8 read; the `mv a0,s3` at 0x84824 discards it) and the memory M the release left.
   M's premises are cm_exit's own six write transports at the flag byte plus the released byte's value. The script
   runs in cm_exit_rel_F_on; this is its corollary (cmInv to cmInv_on, shadow_rw M to the post form, cmPost_on to
   cmPost). *)
Lemma cm_exit_rel_F : forall (RNG : footprint) (fr sp2 jj r : Z) (mc M : word -> option byte)
    (x1 y0 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
  r = want CM_T len fb ->
  cmInv7 fr sp2 jj 1 mc ->
  munch [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
         (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] mc M ->
  wmono rsegs mc M -> mem_inv rsegs M -> shadow_rw M ->
  stk rsegs M (S - 9136) S -> stk rsegs M FS (FS + FS_SIZE) ->
  mrd rsegs M (wa (fs_flag FS 2 jj)) = Some (Z_to_bv 8 0) ->
  rng RNG (S - 96) 96 ->
  evtF rsegs RNG cmPost7
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 (CA S)) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 fr) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x847c0) fc None M (seg_rom rsegs)).
Proof.
  intros RNG fr sp2 jj r mc M x1 y0 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6
    Er INVk MUc WMc Jmicur SRcur STwcur STfs1 RDfl RSAV.
  eapply evtF_mono;
    [ exact (cm_exit_rel_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb Rf Rlen RS S16 HK
               ST Hfb SR_on7 HHM HAE AW FP0 RNG fr sp2 jj r mc M x1 y0 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9
               z10 u3 u4 u5 u6 Er (cm_inv_to_on fr sp2 jj 1 mc INVk) MUc WMc Jmicur
               (fun P _ => shadow_rw_on_of_shadow_rw P M SRcur) STwcur STfs1 RDfl RSAV)
    | exact cmPost_of_on ].
Qed.

(* The same run from the state BEFORE the release store (the end of stretch S6, pc 0x847bc, memory mcur): the six
   write transports of cm_exit at the class-2 in-use flag byte, verbatim, and the released byte's value. The walk
   may use this form when its release law hands it the written memory, and cm_exit_rel_F when it hands the facts.
   The script runs in cm_exit_rel_after_store_F_on; this is its corollary. *)
Lemma cm_exit_rel_after_store_F : forall (RNG : footprint) (fr sp2 jj r : Z) (mc mcur : word -> option byte)
    (x1 y0 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
  r = want CM_T len fb ->
  cmInv7 fr sp2 jj 1 mc ->
  munch [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
         (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] mc mcur ->
  wmono rsegs mc mcur -> mem_inv rsegs mcur -> shadow_rw mcur ->
  stk rsegs mcur (S - 9136) S -> stk rsegs mcur FS (FS + FS_SIZE) ->
  store_ok rsegs mcur (wa (fs_flag FS 2 jj)) 1 = true ->
  rng RNG (S - 96) 96 ->
  evtF rsegs RNG cmPost7
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 (CA S)) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 fr) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x847c0) fc None
        (write_to_mem mcur (wa (fs_flag FS 2 jj)) (le1 (Z_to_bv 64 0))) (seg_rom rsegs)).
Proof.
  intros RNG fr sp2 jj r mc mcur x1 y0 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6
    Er INVk MUc WMc Jmicur SRcur STwcur STfs1 SOKfl RSAV.
  eapply evtF_mono;
    [ exact (cm_exit_rel_after_store_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb Rf
               Rlen RS S16 HK ST Hfb SR_on7 HHM HAE AW FP0 RNG fr sp2 jj r mc mcur x1 y0 u0 u1 u2 y1 y2 y3 y4 y5
               y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 Er (cm_inv_to_on fr sp2 jj 1 mc INVk) MUc WMc Jmicur
               (fun P _ => shadow_rw_on_of_shadow_rw P mcur SRcur) STwcur STfs1 SOKfl RSAV)
    | exact cmPost_of_on ].
Qed.

(* The old evt form of this stretch from the footprint form, with ExecF.rng_all: the check that the _F statement is
   the old one plus the footprint premise, nothing weaker. *)
Lemma cm_exit_rel_of_F : forall (fr sp2 jj r : Z) (mc M : word -> option byte)
    (x1 y0 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
  r = want CM_T len fb ->
  cmInv7 fr sp2 jj 1 mc ->
  munch [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
         (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] mc M ->
  wmono rsegs mc M -> mem_inv rsegs M -> shadow_rw M ->
  stk rsegs M (S - 9136) S -> stk rsegs M FS (FS + FS_SIZE) ->
  mrd rsegs M (wa (fs_flag FS 2 jj)) = Some (Z_to_bv 8 0) ->
  evt rsegs cmPost7
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 (CA S)) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 fr) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x847c0) fc None M (seg_rom rsegs)).
Proof.
  intros fr sp2 jj r mc M x1 y0 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6
    Er INVk MUc WMc Jmicur SRcur STwcur STfs1 RDfl.
  pose proof STwcur as (Slo & Shi & _).
  eapply evtF_evt, (cm_exit_rel_F RNG_all); try eassumption.
  apply rng_all; lia.
Qed.

(* The release store itself (0x847bc `sb zero,0(a0)`, one step), so that S6 + the store + S7 is ONE footprint run
   for ProgWorld.ctl_release_of_free_law_stmt: a Theorem Labs lane's rebase-interfaces.md section 2.4 (a working note, not in this delivery), exact statement text.
   Proof: StepF's step, then the premise; StepF leaves the stored byte as [Z_to_bv 8 0], which le1_lit_byte turns
   into le1 (Z_to_bv 64 0) (a Theorem Labs lane's note). *)
Lemma cm_release_store_F : forall (RNG : footprint) (fr sp2 jj r : Z) (mc mcur : word -> option byte)
    (x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word) (Q : machine_state -> Prop),
  rng RNG (fs_flag FS 2 jj) 1 ->
  store_ok rsegs mcur (wa (fs_flag FS 2 jj)) 1 = true ->
  evtF rsegs RNG Q
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 (CA S)) (wa (fs_flag FS 2 jj))
             y1 y2 y3 y4 y5 y6 y7 (Z_to_bv 64 fr) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x847c0) fc None (write_to_mem mcur (wa (fs_flag FS 2 jj)) (le1 (Z_to_bv 64 0)))
        (seg_rom rsegs)) ->
  evtF rsegs RNG Q
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 (CA S)) (wa (fs_flag FS 2 jj))
             y1 y2 y3 y4 y5 y6 y7 (Z_to_bv 64 fr) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x847bc) fc None mcur (seg_rom rsegs)).
Proof.
  intros RNG fr sp2 jj r mc mcur x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 Q RFL SOK K.
  rewrite (le1_lit_byte 0) in K.
  step.
  exact K.
Qed.

End MatchF7.

Check cm_exit_rel_F_on.
Print Assumptions cm_exit_rel_F_on.
Check cm_exit_rel_after_store_F_on.
Print Assumptions cm_exit_rel_after_store_F_on.
Check cm_release_store_F_on.
Print Assumptions cm_release_store_F_on.
