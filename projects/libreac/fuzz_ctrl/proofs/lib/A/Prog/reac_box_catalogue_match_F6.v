(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its addresses changed; 279 of its 357 lines of code are new or changed and 3023 lines of the source are left out. *)
(* Footprint (_F) re-run of stretch S6 of reac_box_catalogue_match.v (image A, asan): the exit cut 0x84724 to the
   inline frame-release store `sb zero,0(a0)` at 0x847bc, the state at the store before it executes. Only the
   side-stack arm (nn = 1, s2 = fr = fs_frame FS 2 jj) is lifted: the cgif-form walk takes that arm, and the
   release itself is cgif's event (astack_free_law), not a step of this run.

   Provenance: footprint re-run of reac_box_catalogue_match.v (source commit d69f7c708f6, proved on FACTS
   ed6b6b7b0ab) by the same script over lib/Lib/StepF; image fuzz_ctrl v1.9.0 asan, ELF fuzz_ctrl.debug sha256
   78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd; route (a) of 22:20Z; for the cgif-form walk
   C_reac_box_catalogue_match.v only.

   Method (recipe segF-rerun-recipe.md steps 2-4 (a working note, not in this delivery)): the script of
   reac_box_catalogue_match.v's cm_exit (lines 2899-3302, its second bullet = the side-stack arm) over StepF's
   step, cut at the release store; cm_exit runs THROUGH 0x847bc to the `ret`, so its script is split there, and
   the state facts the script has at the store are the post predicate cmRelPost. Three rng premises close every
   access of the run: the 8-byte frame-magic store at [fr, fr + 8) (sd a0,0(s7) at 0x8472c), the 32 shadow-byte
   stores at [shadow_addr fr, shadow_addr fr + 32) (sb a0,k(s6), 0x84738..0x847b4) and the 8-byte read of the
   flag pointer at [fr + 248, fr + 256) (ld a0,248(s2) at 0x847b8). The window [S - 9136, S) is not touched
   before the store, so it takes no rng premise.
   cm_exit_rel_of_F re-derives the old Exec.evt form of the same stretch with ExecF.rng_all.
   The section variables and hypotheses are those of reac_box_catalogue_match.v's Section Match, minus the four
   callee contracts (this stretch calls no callee). reac_box_catalogue_match.v itself is unchanged apart from comment text.

   Route (C) `_on` forms (F-on-spec.md (a working note, not in this delivery), a Theorem Labs lane 2026-10-29; rule 24: no function proved: the premise of the
   already-proved stretch is narrowed, no new function): Section MatchF6On, placed before Section MatchF6, is
   Section MatchF6 with `SR : shadow_rw m` narrowed to
   `SR_on : shadow_rw_on (reac_box_catalogue_match_shadow_R f len S FS) m`. It defines cmRelPost_on and re-proves
   cm_rel_bounds, cm_exit_rel_F and cm_exit_rel_of_F as `<name>_on` over reac_box_catalogue_match_on.v (cmInv_on,
   fk_facts_on, cm_stk_win_on, cm_stk_fr_on); cmRelPost_on is cmRelPost with its shadow conjunct the post form
   `forall P, shadow_rw_on P m -> shadow_rw_on P mcur` (that file's srw_post). Section MatchF6 keeps every
   statement byte-identical: cm_rel_bounds and cm_exit_rel_F are now corollaries of their `_on` twins, and
   cm_exit_rel_of_F keeps its proof (the check of cm_exit_rel_F at ExecF.RNG_all). *)
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

(* ==== Route (C): the `_on` forms (Section MatchF6's variables and hypotheses, SR narrowed to SR_on) ==== *)
Section MatchF6On.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (f len S FS : Z) (fb : list byte).
Hypothesis Rf : 0 <= f < 2^64.
Hypothesis Rlen : 0 <= len < 2^64.
Hypothesis RS : S < 2^64.
Hypothesis S16 : S mod 16 = 0.
Hypothesis HK : 9136 <= S.
Hypothesis ST : stk rsegs m (S - 9136) S.
Hypothesis Hwin : forall a, S - 9136 <= a < S -> seg_rom rsegs (wa a) = None.
Hypothesis Hfb : length fb = 50%nat.
Hypothesis HF : 50 <= len -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fb /\ (f + 50 <= S - 9136 \/ S <= f).
Hypothesis HT : forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a).
Hypothesis MI : mem_inv rsegs m.
Hypothesis AC : asan_cells m.
Hypothesis SR_on : shadow_rw_on (reac_box_catalogue_match_shadow_R f len S FS) m.
Hypothesis HHM : HIGHMEM_BEG <= S - 9136.
Hypothesis HAE : S <= APPMEM_END.
Hypothesis AW : addressable m (S - 9136) 9136.
Hypothesis AFU : 50 <= len -> addressable m f 50 /\ app_mem (f + 50).
Hypothesis AT : addressable m CM_T 3256.
Hypothesis ABC : addressable m REAC_CTRL_PARSE_BC 6.
Hypothesis HBCMP : bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)).
Hypothesis HMEMCMP : bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)).
Hypothesis HGOT : bytes_at rsegs m GOT_CF (le8 (wa CF)).
Hypothesis HCF254 : bytes_at rsegs m (CF + 254) [Z_to_bv 8 1].
Hypothesis HCF255 : bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].
Hypothesis FP0 : fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - 9136) S
  (reac_box_catalogue_match_W S) (reac_box_catalogue_match_D f len).
Hypothesis TLS0 : reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - 9136) S.

(* The names of reac_box_catalogue_match.v at this section's variables (unchanged), and the re-proved names of
   reac_box_catalogue_match_on.v (on-api.md's argument prefixes, SR_on in the place of SR). *)
Local Abbreviation cmCA := (CA S).
Local Abbreviation cmR := (reac_box_catalogue_match_shadow_R f len S FS).
Local Abbreviation cmINV_on :=
  (reac_box_catalogue_match_on.cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS).
Local Abbreviation fk_facts_on6 :=
  (reac_box_catalogue_match_on.fk_facts_on tp m f len S FS fb Rf Rlen S16 HK ST Hfb SR_on AW FP0).
Local Abbreviation cm_fr_sh_R6 :=
  (reac_box_catalogue_match_on.cm_fr_sh_R tp m f len S FS fb Rf Rlen S16 HK Hfb FP0).
Local Abbreviation cm_stk_win_on6 :=
  (reac_box_catalogue_match_on.cm_stk_win_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS ST).
Local Abbreviation cm_stk_fr_on6 :=
  (reac_box_catalogue_match_on.cm_stk_fr_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fb Rf Rlen S16 HK
     ST Hfb).

(* One store of the shadow byte k of the released side-stack frame (0xf5), on evtF goals: the text of Section
   MatchF6's shstfF (StepF's stored byte [Z_to_bv 8 245]) with the `_on` file's shstf steps: the memory tracker is
   the post form srw_post (every region shadow_rw_on P m stays shadow_rw_on P mcur), the store's store_ok comes
   from cm_sh_sok_on at R (the frame's shadow byte k is in R: cm_fr_sh_R), and cm_post_srw_write carries srw_post
   across the write. *)
Local Ltac shstfF_on fr0 mc0 k :=
  lazymatch goal with
  | [ SHIN : forall kk, _ -> in_shadow (shadow_addr fr0 + kk),
      WMc : wmono rsegs mc0 ?mcur,
      SRcur : reac_box_catalogue_match_on.srw_post m ?mcur,
      FKc : cmFK S FS fr0 _ _ _,
      Jmicur : mem_inv rsegs ?mcur,
      MUc : munch ?W mc0 ?mcur,
      STwcur : stk rsegs ?mcur (S - 9136) S
      |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) ] =>
    let SOK := fresh "SOK" in
    assert (SOK : store_ok rsegs mcur (wa (shadow_addr fr0 + k)) 1 = true)
      by (apply (reac_box_catalogue_match_on.cm_sh_sok_on cmR mcur); [exact (SRcur cmR SR_on) |
          apply (cm_fr_sh_R6 fr0 _ _ _ k FKc); intros; lia | apply SHIN; lia]);
    step;
    apply (wmono_write rsegs mc0 mcur (wa (shadow_addr fr0 + k)) [Z_to_bv 8 245]) in WMc;
    apply (reac_box_catalogue_match_on.cm_post_srw_write m mcur (wa (shadow_addr fr0 + k)) [Z_to_bv 8 245])
      in SRcur;
    apply (mem_inv_store rsegs mcur (wa (shadow_addr fr0 + k)) [Z_to_bv 8 245]) in Jmicur;
      [| cbn [length]; exact SOK];
    apply (stk_write rsegs mcur (S - 9136) S (shadow_addr fr0 + k) [Z_to_bv 8 245]) in STwcur;
      [| lia | cbn [length]; lia];
    apply (munch_write W mc0 mcur (shadow_addr fr0 + k) [Z_to_bv 8 245]) in MUc;
      [| lia | cbn [length]; lia | cbn [length]; cbn [inside]; right; left; split; lia];
    clear SOK
  end.

(* cmRelPost with its `shadow_rw mcur` conjunct replaced by the post form: every region whose shadow bytes are
   writable and readable in m stays so in mcur. *)
Definition cmRelPost_on (fr sp2 jj r : Z) (mc : word -> option byte)
    (x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word) : machine_state -> Prop :=
  fun ms' => exists mcur : word -> option byte,
    ms' = MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 cmCA)
                  (wa (fs_flag FS 2 jj)) y1 y2 y3 y4 y5 y6 y7
                  (Z_to_bv 64 fr) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
                  (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
             F (Z_to_bv 64 0x847bc) fc None mcur (seg_rom rsegs) /\
    munch [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
           (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] mc mcur /\
    wmono rsegs mc mcur /\ mem_inv rsegs mcur /\ (forall P, shadow_rw_on P m -> shadow_rw_on P mcur) /\
    stk rsegs mcur (S - 9136) S /\ stk rsegs mcur FS (FS + FS_SIZE) /\
    store_ok rsegs mcur (wa (fs_flag FS 2 jj)) 1 = true.

(* cm_rel_bounds over cmInv_on: the script's own FRlo / FRhi2 / SHIN / SBlo / SBhi, fk_facts_on for fk_facts. *)
Lemma cm_rel_bounds_on : forall fr sp2 jj mc, cmINV_on fr sp2 jj 1 mc ->
  0 <= fr /\ fr + 256 <= 2^64 /\ 0 <= shadow_addr fr /\ shadow_addr fr + 32 <= 2^64.
Proof.
  intros fr sp2 jj mc INVk.
  pose proof INVk as INV. destruct INV as (HFK & _).
  pose proof (fk_facts_on6 fr sp2 jj 1 HFK) as (Fm8 & Fpos & Fhi & _ & _ & _ & _).
  pose proof (acl_fs tp m f len S FS FP0) as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  unfold FS_SIZE in FShi.
  pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
  destruct HFK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)]; [exfalso; clear -En; lia|].
  assert (FRlo : FS + 36864 <= fr).
  { rewrite Ef. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
    change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. lia. }
  assert (FRhi2 : fr + 256 <= FS + 11571200).
  { rewrite Ef. unfold fs_frame, fs_B, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
    change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. change (2 ^ (14 - 2)) with 4096 in Hj. lia. }
  assert (SHIN : forall k, 0 <= k < 32 -> in_shadow (shadow_addr fr + k)).
  { intros k Hk. rewrite <- (cm_sh_add8 f len S fb Rf Rlen Hfb fr k Fm8). apply rt_app_shadow. apply FSapp.
    unfold FS_SIZE. lia. }
  pose proof (rt_shadow_bound (shadow_addr fr + 0) (SHIN 0 ltac:(lia))) as B0.
  pose proof (rt_shadow_bound (shadow_addr fr + 31) (SHIN 31 ltac:(lia))) as B1.
  split; [lia|]. split; [lia|]. split; lia.
Qed.

(* cm_exit_rel_F over cmInv_on, with cmRelPost_on as its post: Section MatchF6's script with the `_on` file's exit
   steps (srw_post from the invariant's wmono / rd_mono by cm_post_srw_inv, carried across the frame-magic store
   and the 32 shadow stores by cm_post_srw_write; the shadow stores by shstfF_on). *)
Lemma cm_exit_rel_F_on : forall (RNG : footprint) (fr sp2 jj nn : Z) (mc : word -> option byte) (r : Z)
    (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
  rng RNG fr 8 -> rng RNG (fr + 248) 8 -> rng RNG (shadow_addr fr) 32 ->
  nn = 1 -> r = want CM_T len fb -> cmINV_on fr sp2 jj nn mc ->
  evtF rsegs RNG (cmRelPost_on fr sp2 jj r mc x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6)
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 cmCA) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x84724) fc None mc (seg_rom rsegs)).
Proof.
  intros RNG fr sp2 jj nn mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6
    RFW RFL RSHD Enn Er INVk.
  subst nn.
  pose proof (cm_stk_win_on6 fr sp2 jj 1 mc INVk) as STw.
  pose proof (cm_stk_fr_on6 fr sp2 jj 1 mc INVk) as STf.
  pose proof INVk as INV.
  destruct INV as (HFK & Jmu & Jwm & Jrm & Jmi & JAC & JSR & JFP & JTL & JAD & JAWX & SAV & FLG).
  pose proof HFK as HFKc.
  pose proof (fk_facts_on6 fr sp2 jj 1 HFK) as (Fm8 & Fpos & Fhi & Fwv & Fap & Fsh & Fsp2).
  pose proof (CA_facts f len S fb Rf Rlen S16 Hfb) as (CA32 & CAlo & CAhi).
  pose proof (cm_CA_lo f len S fb Rf Rlen S16 Hfb) as (CAlo2 & CAhi2).
  pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'. pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
  pose proof (acl_fs tp m f len S FS FP0) as (FSpos & FSmod & FSgt & FShi & FSapp & _). unfold FS_SIZE in FShi.
  pose proof RS as RSb.
  destruct HFK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)]; [exfalso; clear -En; lia|].
  assert (FRlo : FS + 36864 <= fr).
  { rewrite Ef. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
    change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. lia. }
  assert (FRhi2 : fr + 256 <= FS + 11571200).
  { rewrite Ef. unfold fs_frame, fs_B, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
    change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. change (2 ^ (14 - 2)) with 4096 in Hj. lia. }
  assert (SOKfr : store_ok rsegs mc (wa fr) 8 = true) by
    (apply (wv_store_ok mc mc fr 8);
      [ intros i Hi; exact (stk_wv mc fr (fr + 192) (fr + i) STf ltac:(lia))
      | apply wmono_refl | lia | lia ]).
  assert (SHIN : forall k, 0 <= k < 32 -> in_shadow (shadow_addr fr + k)).
  { intros k Hk. rewrite <- (cm_sh_add8 f len S fb Rf Rlen Hfb fr k Fm8). apply rt_app_shadow. apply FSapp.
    unfold FS_SIZE. lia. }
  assert (SBlo : 0 <= shadow_addr fr) by
    (pose proof (rt_shadow_bound (shadow_addr fr + 0) (SHIN 0 ltac:(lia))); lia).
  assert (SBhi : shadow_addr fr + 40 <= 2 ^ 64) by
    (pose proof (rt_shadow_bound (shadow_addr fr + 31) (SHIN 31 ltac:(lia))); lia).
  assert (FLo : FS <= fs_flag FS 2 jj /\ fs_flag FS 2 jj + 1 <= FS + 36864).
  { unfold fs_flag, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
    change (2 ^ 15) with 32768. change (2 ^ 13) with 8192. change (2 ^ 12) with 4096 in Hj. lia. }
  pose proof (wmono_refl rsegs mc) as WMc.
  pose proof (reac_box_catalogue_match_on.cm_post_srw_inv m mc Jwm Jrm) as SRcur.
  pose proof Jmi as Jmicur.
  pose proof (munch_refl [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
                          (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] mc) as MUc.
  pose proof STw as STwcur.
  step. step. step.
  change (Z_to_bv 64 fr) with (wa fr).
  apply (wmono_write rsegs mc mc (wa fr) (le8 (Z_to_bv 64 1172321806))) in WMc.
  apply (reac_box_catalogue_match_on.cm_post_srw_write m mc (wa fr) (le8 (Z_to_bv 64 1172321806))) in SRcur.
  apply (mem_inv_store rsegs mc (wa fr) (le8 (Z_to_bv 64 1172321806))) in Jmicur;
    [| rewrite length_le8; exact SOKfr].
  apply (munch_write _ mc mc fr (le8 (Z_to_bv 64 1172321806))) in MUc;
    [| lia | rewrite length_le8; lia | cbn [inside]; left; split; [lia | rewrite length_le8; lia]].
  apply (stk_write rsegs mc (S - 9136) S fr (le8 (Z_to_bv 64 1172321806))) in STwcur;
    [| lia | rewrite length_le8; lia].
  replace (if (1 =? 0)%Z then 0 else fr) with fr by reflexivity.
  step. rewrite (cm_eqb0 fr) by lia.
  replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  step.
  shstfF_on fr mc 4. shstfF_on fr mc 5. shstfF_on fr mc 6. shstfF_on fr mc 7.
  shstfF_on fr mc 0. shstfF_on fr mc 1. shstfF_on fr mc 2. shstfF_on fr mc 3.
  shstfF_on fr mc 12. shstfF_on fr mc 13. shstfF_on fr mc 14. shstfF_on fr mc 15.
  shstfF_on fr mc 8. shstfF_on fr mc 9. shstfF_on fr mc 10. shstfF_on fr mc 11.
  shstfF_on fr mc 20. shstfF_on fr mc 21. shstfF_on fr mc 22. shstfF_on fr mc 23.
  shstfF_on fr mc 16. shstfF_on fr mc 17. shstfF_on fr mc 18. shstfF_on fr mc 19.
  shstfF_on fr mc 28. shstfF_on fr mc 29. shstfF_on fr mc 30. shstfF_on fr mc 31.
  shstfF_on fr mc 24. shstfF_on fr mc 25. shstfF_on fr mc 26. shstfF_on fr mc 27.
  specialize (FLG eq_refl).
  pose proof JFP as JFPc.
  destruct JFPc as (DTx & TSx & Cx & Tx & DBx & kkx & _ & _ & HPfs & _ & _ & _ & _ & _ & _ & _).
  destruct HPfs as (FSP1 & FSP2 & FSP3 & FSP4 & FSPstk).
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (FLGm : bytes_at rsegs m1 (fr + 248) (le8 (Z_to_bv 64 (fs_flag FS 2 jj))))
      by (eapply fl_bytes; [exact FLG | exact MUc |
           intros x Hx; rewrite length_le8 in Hx; cbn [outside];
           split; [lia | split; [ intros [A B];
             apply (acl_app_not_shadow x);
             [ apply FSapp; unfold FS_SIZE; lia
             | pose proof (SHIN (x - shadow_addr fr) ltac:(lia)) as HS;
               replace (shadow_addr fr + (x - shadow_addr fr)) with x in HS by lia; exact HS ]
             | split; [ lia | exact I ]]]]);
    assert (RD : ov_read_bytes rsegs m1 (wa (fr + 248)) 8 = Some (le8 (Z_to_bv 64 (fs_flag FS 2 jj))))
      by (replace (fr + 248) with (fr + 248 + 0) by lia;
          rewrite (bytes_at_read rsegs m1 _ (le8 (Z_to_bv 64 (fs_flag FS 2 jj))) 0 8 FLGm)
            by (try rewrite length_le8; lia); reflexivity);
    assert (SOKfl : store_ok rsegs m1 (wa (fs_flag FS 2 jj)) 1 = true)
      by (apply (wv_store_ok mc m1 (fs_flag FS 2 jj) 1);
          [ intros i Hi; replace (fs_flag FS 2 jj + i) with (fs_flag FS 2 jj) by lia;
            exact (stk_wv mc FS (FS + FS_SIZE) (fs_flag FS 2 jj) FSPstk ltac:(unfold FS_SIZE; lia))
          | exact WMc | lia | unfold FS_SIZE in *; lia ]);
    assert (STfs1 : stk rsegs m1 FS (FS + FS_SIZE))
      by (repeat (apply stk_write; [| lia | rewrite ?length_le1, ?length_le8; cbn [length]; lia]); exact FSPstk) end.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => set (m1 := mm) in * end.
  step.
  change (Z_to_bv 64 (fs_flag FS 2 jj)) with (wa (fs_flag FS 2 jj)).
  clearbody m1.
  (* The cut: the release store 0x847bc is the walk's event, not a step of this run. *)
  apply evtF_done. unfold cmRelPost_on. exists m1.
  split; [reflexivity|]. split; [exact MUc|]. split; [exact WMc|]. split; [exact Jmicur|].
  split; [exact SRcur|]. split; [exact STwcur|]. split; [exact STfs1 | exact SOKfl].
Qed.

(* cm_exit_rel_of_F over cmInv_on: the old Exec.evt form of cm_exit_rel_F_on with ExecF.rng_all. *)
Corollary cm_exit_rel_of_F_on : forall (fr sp2 jj nn : Z) (mc : word -> option byte) (r : Z)
    (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
  nn = 1 -> r = want CM_T len fb -> cmINV_on fr sp2 jj nn mc ->
  evt rsegs (cmRelPost_on fr sp2 jj r mc x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6)
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 cmCA) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x84724) fc None mc (seg_rom rsegs)).
Proof.
  intros fr sp2 jj nn mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 Enn Er INVk.
  subst nn.
  pose proof (cm_rel_bounds_on fr sp2 jj mc INVk) as (B1 & B2 & B3 & B4).
  apply (evtF_evt rsegs RNG_all).
  apply (cm_exit_rel_F_on RNG_all fr sp2 jj 1 mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10
           u3 u4 u5 u6);
    [ apply rng_all; lia | apply rng_all; lia | apply rng_all; lia | reflexivity | exact Er | exact INVk ].
Qed.

End MatchF6On.

Section MatchF6.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (f len S FS : Z) (fb : list byte).
Hypothesis Rf : 0 <= f < 2^64.
Hypothesis Rlen : 0 <= len < 2^64.
Hypothesis RS : S < 2^64.
Hypothesis S16 : S mod 16 = 0.
Hypothesis HK : 9136 <= S.
Hypothesis ST : stk rsegs m (S - 9136) S.
Hypothesis Hwin : forall a, S - 9136 <= a < S -> seg_rom rsegs (wa a) = None.
Hypothesis Hfb : length fb = 50%nat.
Hypothesis HF : 50 <= len -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fb /\ (f + 50 <= S - 9136 \/ S <= f).
Hypothesis HT : forall a, CM_T <= a < CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a).
Hypothesis MI : mem_inv rsegs m.
Hypothesis AC : asan_cells m.
Hypothesis SR : shadow_rw m.
Hypothesis HHM : HIGHMEM_BEG <= S - 9136.
Hypothesis HAE : S <= APPMEM_END.
Hypothesis AW : addressable m (S - 9136) 9136.
Hypothesis AFU : 50 <= len -> addressable m f 50 /\ app_mem (f + 50).
Hypothesis AT : addressable m CM_T 3256.
Hypothesis ABC : addressable m REAC_CTRL_PARSE_BC 6.
Hypothesis HBCMP : bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)).
Hypothesis HMEMCMP : bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)).
Hypothesis HGOT : bytes_at rsegs m GOT_CF (le8 (wa CF)).
Hypothesis HCF254 : bytes_at rsegs m (CF + 254) [Z_to_bv 8 1].
Hypothesis HCF255 : bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].
Hypothesis FP0 : fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (S - 9136) S
  (reac_box_catalogue_match_W S) (reac_box_catalogue_match_D f len).
Hypothesis TLS0 : reac_box_catalogue_match_tls m (bv_unsigned tp) FS (S - 9136) S.

(* The section-discharged names of reac_box_catalogue_match.v, at this section's variables, and the `_on` forms the
   corollaries cite (SR_on6: SR's restriction to R). *)
Local Notation cmCA := (CA S).
Local Notation cmINV := (cmInv ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS).
Local Abbreviation cmINV_on :=
  (reac_box_catalogue_match_on.cmInv_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS).
Local Abbreviation SR_on6 := (shadow_rw_on_of_shadow_rw (reac_box_catalogue_match_shadow_R f len S FS) m SR).

(* The state at the release store 0x847bc, before it executes: a0 is the flag byte's address (the word the
   epilogue read from fr + 248), s2 = s7 = fr, s6 = shadow_addr fr, s3 = r; the memory mcur is mc with the frame
   magic word and the frame's 32 released shadow bytes written, so it is a munch of mc inside the frame word, the
   frame's shadow bytes and the class-2 flag byte of the frame (the byte the store writes), it keeps the runtime
   relations (wmono, mem_inv, shadow_rw), the window and the side stack read back (stk), and the store itself is
   allowed (store_ok at the flag byte). *)
Definition cmRelPost (fr sp2 jj r : Z) (mc : word -> option byte)
    (x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word) : machine_state -> Prop :=
  fun ms' => exists mcur : word -> option byte,
    ms' = MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 cmCA)
                  (wa (fs_flag FS 2 jj)) y1 y2 y3 y4 y5 y6 y7
                  (Z_to_bv 64 fr) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
                  (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
             F (Z_to_bv 64 0x847bc) fc None mcur (seg_rom rsegs) /\
    munch [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
           (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] mc mcur /\
    wmono rsegs mc mcur /\ mem_inv rsegs mcur /\ shadow_rw mcur /\
    stk rsegs mcur (S - 9136) S /\ stk rsegs mcur FS (FS + FS_SIZE) /\
    store_ok rsegs mcur (wa (fs_flag FS 2 jj)) 1 = true.

(* The corollaries' conversions (F-on-spec.md, "Corollaries"): the old invariant gives cmInv_on (its shadow conjunct
   restricted to R), and cmRelPost_on gives cmRelPost (shadow_rw mcur from the post form at the whole shadow, SR). *)
Lemma cm_inv_to_on : forall fr sp2 jj nn mc, cmINV fr sp2 jj nn mc -> cmINV_on fr sp2 jj nn mc.
Proof.
  intros fr sp2 jj nn mc (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6
           (conj (shadow_rw_on_of_shadow_rw (reac_box_catalogue_match_shadow_R f len S FS) mc A7) A8))))))).
Qed.

Lemma cmRelPost_of_on : forall (fr sp2 jj r : Z) (mc : word -> option byte)
    (x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word) ms,
  cmRelPost_on gp tp s11 F fc m S FS fr sp2 jj r mc x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6
    ms ->
  cmRelPost fr sp2 jj r mc x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 ms.
Proof.
  intros fr sp2 jj r mc x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 ms
    (mcur & E & MU & WM & MI' & SRp & ST1 & ST2 & SOK).
  exists mcur.
  exact (conj E (conj MU (conj WM (conj MI'
           (conj (shadow_rw_of_on_all mcur (SRp (fun _ => True) (shadow_rw_on_of_shadow_rw (fun _ => True) m SR)))
              (conj ST1 (conj ST2 SOK))))))).
Qed.

(* The two ranges the run touches lie in [0, 2^64): the frame slot (fs_B 2 = 256 bytes) of the side stack and its
   32 shadow bytes. The corollary needs this to instantiate RNG with RNG_all; the proof is cm_rel_bounds_on's
   (the script's own FRlo / FRhi2 / SHIN / SBlo / SBhi). *)
Lemma cm_rel_bounds : forall fr sp2 jj mc, cmINV fr sp2 jj 1 mc ->
  0 <= fr /\ fr + 256 <= 2^64 /\ 0 <= shadow_addr fr /\ shadow_addr fr + 32 <= 2^64.
Proof.
  intros fr sp2 jj mc INVk.
  exact (cm_rel_bounds_on ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m f len S FS fb Rf Rlen S16 HK ST Hfb SR_on6
           HAE AW FP0 fr sp2 jj mc (cm_inv_to_on fr sp2 jj 1 mc INVk)).
Qed.

(* S6: the exit cut 0x84724 to the release store 0x847bc on the side-stack arm. The script is that of
   reac_box_catalogue_match.v's cm_exit, second bullet (the arm nn = 1), cut after the `ld a0,248(s2)` of
   0x847b8: the frame magic word, the not-taken `beqz s2`, the 32 released shadow bytes and the flag-pointer
   load, with the memory facts the script carries at that point handed over as cmRelPost. The script runs in
   cm_exit_rel_F_on; this is its corollary (cmInv to cmInv_on, cmRelPost_on to cmRelPost). *)
Lemma cm_exit_rel_F : forall (RNG : footprint) (fr sp2 jj nn : Z) (mc : word -> option byte) (r : Z)
    (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
  rng RNG fr 8 -> rng RNG (fr + 248) 8 -> rng RNG (shadow_addr fr) 32 ->
  nn = 1 -> r = want CM_T len fb -> cmINV fr sp2 jj nn mc ->
  evtF rsegs RNG (cmRelPost fr sp2 jj r mc x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6)
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 cmCA) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x84724) fc None mc (seg_rom rsegs)).
Proof.
  intros RNG fr sp2 jj nn mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6
    RFW RFL RSHD Enn Er INVk.
  eapply evtF_mono;
    [ exact (cm_exit_rel_F_on ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len S FS fb Rf Rlen RS S16 HK
               ST Hfb SR_on6 HHM HAE AW FP0 RNG fr sp2 jj nn mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9
               z10 u3 u4 u5 u6 RFW RFL RSHD Enn Er (cm_inv_to_on fr sp2 jj nn mc INVk))
    | exact (cmRelPost_of_on fr sp2 jj r mc x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6) ].
Qed.

(* The old Exec.evt form of the same stretch, from the footprint form with ExecF.rng_all: the check that
   cm_exit_rel_F is the old statement plus the three footprint premises, nothing weaker. *)
Corollary cm_exit_rel_of_F : forall (fr sp2 jj nn : Z) (mc : word -> option byte) (r : Z)
    (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
  nn = 1 -> r = want CM_T len fb -> cmINV fr sp2 jj nn mc ->
  evt rsegs (cmRelPost fr sp2 jj r mc x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6)
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 cmCA) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x84724) fc None mc (seg_rom rsegs)).
Proof.
  intros fr sp2 jj nn mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 Enn Er INVk.
  subst nn.
  pose proof (cm_rel_bounds fr sp2 jj mc INVk) as (B1 & B2 & B3 & B4).
  apply (evtF_evt rsegs RNG_all).
  apply (cm_exit_rel_F RNG_all fr sp2 jj 1 mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10
           u3 u4 u5 u6);
    [ apply rng_all; lia | apply rng_all; lia | apply rng_all; lia | reflexivity | exact Er | exact INVk ].
Qed.

End MatchF6.

Check cm_exit_rel_F_on.
Print Assumptions cm_exit_rel_F_on.
