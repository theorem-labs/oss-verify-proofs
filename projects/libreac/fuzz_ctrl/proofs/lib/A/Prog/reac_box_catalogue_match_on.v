(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/C_reac_ctrl_classify_box_frameLib.v, with its module paths and module names changed; 2442 of its 2524 lines of code are new or changed and 907 lines of the source are left out. *)
(* lib/A/Prog/reac_box_catalogue_match_on.v -- route (C) (a Theorem Labs lane 09:20Z; frozen form, a Theorem Labs lane 09:38Z; 09:58Z ruling;
   layout approved by a Theorem Labs lane 10:49Z): reac_box_catalogue_match's run, image A, with the four callee contracts in
   their `_on` form and the universal `shadow_rw m` premise narrowed to
   `shadow_rw_on (reac_box_catalogue_match_shadow_R f len S FS) m` (a Theorem Labs lane's R and contract_on,
   reac_box_catalogue_match_c.v 578488127b5). rule 24: no function proved here that is not
   already proved: this is reac_box_catalogue_match.v's run (blob 6770846641b), same scripts.

   reac_box_catalogue_match.v's code is unchanged since release c5e779efe8c (comments edited); it keeps every code line of the source blob above and adds 11. Its Section Match takes the old callee contracts, and
   `<callee>_contract -> <callee>_contract_on` does not hold, so no old statement follows from this file.

   Layout: the 83 Section Match declarations whose generalized form has neither SR nor a callee contract nor the old
   invariant in its statement are re-used at this Section's variables (the Local Abbreviation block; each passes the
   section variables and hypotheses that declaration was generalized over). The rest is re-proved here as `<name>_on`
   with the old script; the changed steps are:
   - fk_facts_on: the frame's shadow bytes are writable from SR_on (cm_fr_sh_R);
   - the shadow conjunct of cmInv_on (shadow_rw_on cmR mc) across a run: ShadowRwOnT.shadow_rw_on_mem_mono;
   - each callee call: its `_on` premise from the invariant's shadow_rw_on cmR by shadow_rw_on_mono and the R
     inclusion at that call (cm_R_sm2, cm_R_parse, cm_R_mb, cm_R_bcmp); the callee's post form
     `forall P, shadow_rw_on P m -> shadow_rw_on P m'` applied to cmR for cm_Wc_rd_on;
   - the exit: the post form srw_post (`forall P, shadow_rw_on P m -> shadow_rw_on P mc`) is carried across every
     store (cm_post_srw_write) and gives cmPost_on; each shadow store's store_ok comes from cm_sh_sok_on at cmR.
   asan_stack_malloc_shadow_R is unfolded in ONE place only (cm_sm_R_frames / cm_sm_R_words), so a change of that leaf
   reaches this file there (a Theorem Labs lane 10:5xZ). *)
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
  reac_box_catalogue_match_c reac_box_catalogue_match_lib.
(* The narrowed premise, the callees' `_on` Definition leaves, and the source run (Required, not Imported: its
   Section names are re-used below at this file's Section variables). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require rng_asan sh_word_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c_on bcmp_wrap_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_catalogue_match.
Import ListNotations.
Open Scope Z_scope.

(* MemMono.v's store-footprint hook, Local here (a Theorem Labs lane made MemMono's `::=` Local at 8bac67328ab; a Theorem Labs lane
   sanctioned this copy of MemMono.v:207-217's body): the store_done steps of the re-proved scripts carry munch /
   wmono / rd_mono / stk across each store by it, as reac_box_catalogue_match.v's scripts do. *)
Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | RMo : rd_mono ?mq m |- _ => apply (rd_mono_write mq m (wa a) bs) in RMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* ---- leaf lemmas with no run binder ---- *)

(* A shadow byte of the region is writable, so a 1-byte store at it is allowed. *)
Lemma cm_sh_sok_on : forall (P : Z -> Prop) mc a, shadow_rw_on P mc -> P a -> in_shadow a ->
  store_ok rsegs mc (wa a) 1 = true.
Proof.
  intros P mc a HS HP Ha. pose proof (rt_shadow_bound a Ha) as R.
  apply (wv_store_ok mc mc a 1);
    [ intros i Hi; replace (a + i) with a by lia; exact (proj1 (HS a HP Ha)) | apply wmono_refl | lia | lia ].
Qed.

(* Post form: a write keeps every region's bytes writable and readable. *)
Lemma cm_shadow_rw_write_on : forall mc a bs,
  forall P, shadow_rw_on P mc -> shadow_rw_on P (write_to_mem mc a bs).
Proof.
  intros mc a bs P H x HP Hx. destruct (H x HP Hx) as [Hw (b & Hb)]. split; [apply wview_write_mono, Hw|].
  unfold mrd in *. destruct (reac_box_catalogue_match.cm_wtm_cases bs mc a (wa x)) as [E|[v E]]; rewrite E;
    [exists b; exact Hb | exists v; reflexivity].
Qed.

Section MatchOn.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (f len S FS : Z) (fb : list byte).
(* Section Match's premises in its order: the four callee contracts in their `_on` form, SR narrowed to SR_on. *)
Hypothesis HPC_on : reac_ctrl_parse_contract_on.
Hypothesis HMB_on : reac_box_model_block_contract_on.
Hypothesis HBC_on : bcmp_wrap_contract_on.
Hypothesis HSM_on : asan_stack_malloc_2_contract_on.
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

(* ---- Section Match's declarations re-used at this Section's variables (each with the section variables and
   hypotheses its generalized form takes; reac_box_catalogue_match.v's About output) ---- *)
Local Abbreviation fpw3_out_hi := reac_box_catalogue_match.fpw3_out_hi.
Local Abbreviation out_in := reac_box_catalogue_match.out_in.
Local Abbreviation fpw3_in_frame := reac_box_catalogue_match.fpw3_in_frame.
Local Abbreviation fpw3_out_sh := reac_box_catalogue_match.fpw3_out_sh.
Local Abbreviation fp_w_incl := reac_box_catalogue_match.fp_w_incl.
Local Abbreviation fp_dj_incl := reac_box_catalogue_match.fp_dj_incl.
Local Abbreviation fp_single := reac_box_catalogue_match.fp_single.
Local Abbreviation aWf := (@reac_box_catalogue_match.aWf S).
Local Abbreviation aDf := (@reac_box_catalogue_match.aDf f len).
Local Abbreviation aXs := (@reac_box_catalogue_match.aXs S FS).
Local Abbreviation aWc := (@reac_box_catalogue_match.aWc S FS).
Local Abbreviation aTL := (@reac_box_catalogue_match.aTL tp S FS).
Local Abbreviation acl_fs := (@reac_box_catalogue_match.acl_fs tp m f len S FS FP0).
Local Abbreviation acl_out_fpw_d := (@reac_box_catalogue_match.acl_out_fpw_d tp m f len S FS FP0).
Local Abbreviation acl_out_fpw_hi := (@reac_box_catalogue_match.acl_out_fpw_hi tp m f len S FS HAE FP0).
Local Abbreviation acl_out_fpw_sh := (@reac_box_catalogue_match.acl_out_fpw_sh tp m f len S FS HAE FP0).
Local Abbreviation acl_out_Xs_sh := (@reac_box_catalogue_match.acl_out_Xs_sh tp m f len S FS S16 HAE FP0).
Local Abbreviation acl_out_Wc_sh := (@reac_box_catalogue_match.acl_out_Wc_sh tp m f len S FS S16 HHM HAE FP0).
Local Abbreviation acl_out_Wc := (@reac_box_catalogue_match.acl_out_Wc S FS HK HAE).
Local Abbreviation cm_sh_add8 := (@reac_box_catalogue_match.cm_sh_add8 f len S fb Rf Rlen Hfb).
Local Abbreviation CA := (@reac_box_catalogue_match.CA S).
Local Abbreviation CA_facts := (@reac_box_catalogue_match.CA_facts f len S fb Rf Rlen S16 Hfb).
Local Abbreviation cmFK := (@reac_box_catalogue_match.cmFK S FS).
Local Abbreviation cmSAVES := (@reac_box_catalogue_match.cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10).
Local Abbreviation cm_ab_keep := reac_box_catalogue_match.cm_ab_keep.
Local Abbreviation cmAWX := (@reac_box_catalogue_match.cmAWX S).
Local Abbreviation cm_CA_lo := (@reac_box_catalogue_match.cm_CA_lo f len S fb Rf Rlen S16 Hfb).
Local Abbreviation cmHF := (@reac_box_catalogue_match.cmHF S).
Local Abbreviation cm_out_app := reac_box_catalogue_match.cm_out_app.
Local Abbreviation fpw3_in_shadow := reac_box_catalogue_match.fpw3_in_shadow.
Local Abbreviation cm_fr_bounds := (@reac_box_catalogue_match.cm_fr_bounds tp m f len S FS fb Rf Rlen S16 HK Hfb HHM FP0).
Local Abbreviation cm_sub := (@reac_box_catalogue_match.cm_sub f len S FS fb Rf Rlen S16 HK Hfb).
Local Abbreviation sh_out_app := (@reac_box_catalogue_match.sh_out_app f len S fb Rf Rlen Hfb).
Local Abbreviation cm_forall_firstn := reac_box_catalogue_match.cm_forall_firstn.
Local Abbreviation cm_forall_skipn := reac_box_catalogue_match.cm_forall_skipn.
Local Abbreviation fpw3_in_hint := reac_box_catalogue_match.fpw3_in_hint.
Local Abbreviation fpw3_in_flag := reac_box_catalogue_match.fpw3_in_flag.
Local Abbreviation acl_rt_out_Wc := (@reac_box_catalogue_match.acl_rt_out_Wc tp m f len S FS fb Rf Rlen HK Hfb HAE FP0).
Local Abbreviation acl_hdr_out_Wc := (@reac_box_catalogue_match.acl_hdr_out_Wc tp m f len S FS fb Rf Rlen HK Hfb HAE FP0).
Local Abbreviation cm_flag_upd := (@reac_box_catalogue_match.cm_flag_upd f len S FS fb Rf Rlen HK Hfb).
Local Abbreviation cm_f_out := (@reac_box_catalogue_match.cm_f_out tp m f len S FS fb Rf Rlen HK Hfb HF HAE AFU FP0).
Local Abbreviation cm_f_sh_out := (@reac_box_catalogue_match.cm_f_sh_out tp m f len S FS fb Rf Rlen S16 HK Hfb HF HHM HAE AFU FP0).
Local Abbreviation cm_AF := (@reac_box_catalogue_match.cm_AF tp m f len S FS fb Rf Rlen S16 HK Hfb HF HHM HAE AFU FP0).
Local Abbreviation cm_FB := (@reac_box_catalogue_match.cm_FB tp m f len S FS fb Rf Rlen HK Hfb HF HAE AFU FP0).
Local Abbreviation cm_parse_addr := (@reac_box_catalogue_match.cm_parse_addr f len S fb Rf Rlen Hfb).
Local Abbreviation cm_miss_short := (@reac_box_catalogue_match.cm_miss_short len fb).
Local Abbreviation cm_miss_hdr := (@reac_box_catalogue_match.cm_miss_hdr len fb).
Local Abbreviation out_incl := reac_box_catalogue_match.out_incl.
Local Abbreviation cm_out_fpw_c := (@reac_box_catalogue_match.cm_out_fpw_c FS).
Local Abbreviation cm_fpw1_out := (@reac_box_catalogue_match.cm_fpw1_out tp m f len S FS fb Rf Rlen HK Hfb HAE FP0).
Local Abbreviation cm_fpw3_out := (@reac_box_catalogue_match.cm_fpw3_out FS).
Local Abbreviation acl_out_fpw_lo := (@reac_box_catalogue_match.acl_out_fpw_lo tp m f len S FS fb Rf Rlen HK Hfb HAE FP0).
Local Abbreviation cm_lo_out := (@reac_box_catalogue_match.cm_lo_out tp m f len S FS fb Rf Rlen HK Hfb HHM HAE FP0).
Local Abbreviation cm_lo_sh_out := (@reac_box_catalogue_match.cm_lo_sh_out tp m f len S FS fb Rf Rlen S16 HK Hfb HHM HAE FP0).
Local Abbreviation cm_lo_bytes := (@reac_box_catalogue_match.cm_lo_bytes tp m f len S FS fb Rf Rlen HK Hfb HHM HAE FP0).
Local Abbreviation cm_lo_addr := (@reac_box_catalogue_match.cm_lo_addr tp m f len S FS fb Rf Rlen S16 HK Hfb HHM HAE FP0).
Local Abbreviation cm_tbl := (@reac_box_catalogue_match.cm_tbl tp m f len S FS fb Rf Rlen HK Hfb HT HHM HAE FP0).
Local Abbreviation cm_geo := (@reac_box_catalogue_match.cm_geo tp m f len S FS fb Rf Rlen S16 HK Hfb FP0).
Local Abbreviation cm_fr2 := (@reac_box_catalogue_match.cm_fr2 f len S FS fb Rf Rlen Hfb).
Local Abbreviation cm_tls_call := (@reac_box_catalogue_match.cm_tls_call tp S FS).
Local Abbreviation cmWc := (@reac_box_catalogue_match.cmWc FS).
Local Abbreviation cm_Wc_sub := (@reac_box_catalogue_match.cm_Wc_sub tp m f len S FS fb Rf Rlen S16 HK Hfb FP0).
Local Abbreviation cm_Wc_out := (@reac_box_catalogue_match.cm_Wc_out f len S FS fb Rf Rlen Hfb).
Local Abbreviation cm_sh_in := (@reac_box_catalogue_match.cm_sh_in f len S fb Rf Rlen Hfb).
Local Abbreviation cm_Wc_rd := (@reac_box_catalogue_match.cm_Wc_rd tp m f len S FS fb Rf Rlen HK Hfb FP0).
Local Abbreviation cm_cls_keep := (@reac_box_catalogue_match.cm_cls_keep f len S FS fb Rf Rlen HK Hfb).
Local Abbreviation cm_cls_fp := (@reac_box_catalogue_match.cm_cls_fp FS).
Local Abbreviation cm_cls_out_Wc := (@reac_box_catalogue_match.cm_cls_out_Wc tp m f len S FS fb Rf Rlen S16 HK Hfb HHM HAE FP0).
Local Abbreviation cm_Wc_saves := (@reac_box_catalogue_match.cm_Wc_saves tp m f len S FS fb Rf Rlen S16 HK Hfb HHM HAE FP0).
Local Abbreviation cm_Wc_flag := (@reac_box_catalogue_match.cm_Wc_flag tp m f len S FS fb Rf Rlen S16 HK Hfb HHM HAE FP0).
Local Abbreviation cm_dj_sh := (@reac_box_catalogue_match.cm_dj_sh f len S fb Rf Rlen HK Hfb HHM).
Local Abbreviation cm_dj_lo := (@reac_box_catalogue_match.cm_dj_lo tp m f len S FS FP0).
Local Abbreviation cm_f_apart := (@reac_box_catalogue_match.cm_f_apart tp m f len S FS fb Rf Rlen S16 HK Hfb HF FP0).
Local Abbreviation cm_model_addr := (@reac_box_catalogue_match.cm_model_addr f len S fb Rf Rlen Hfb).
Local Abbreviation cm_Wc_swap := (@reac_box_catalogue_match.cm_Wc_swap f len FS Rf Rlen).
Local Abbreviation cm_sh_sok := (@reac_box_catalogue_match.cm_sh_sok f len S fb Rf Rlen Hfb).
Local Abbreviation cm_sh_div := (@reac_box_catalogue_match.cm_sh_div f len S fb Rf Rlen Hfb).
Local Abbreviation cm_wtm_cases := reac_box_catalogue_match.cm_wtm_cases.
Local Abbreviation cm_shadow_rw_write := reac_box_catalogue_match.cm_shadow_rw_write.
Local Abbreviation cm_rd_list := (@reac_box_catalogue_match.cm_rd_list f len S fb Rf Rlen HK Hfb).
Local Abbreviation cm_nth_fold1 := (@reac_box_catalogue_match.cm_nth_fold1 f len S fb Rf Rlen HK Hfb).
Local Abbreviation cm_ks := reac_box_catalogue_match.cm_ks.
Local Abbreviation cm_ks_bound := (@reac_box_catalogue_match.cm_ks_bound f len S fb Rf Rlen Hfb).
Local Abbreviation cm_ks_cover := (@reac_box_catalogue_match.cm_ks_cover f len S fb Rf Rlen Hfb).
Local Abbreviation cm_dj_in := (@reac_box_catalogue_match.cm_dj_in f len S fb Rf Rlen HK Hfb).
Local Abbreviation cm_bytes_upd1 := (@reac_box_catalogue_match.cm_bytes_upd1 f len S fb Rf Rlen HK Hfb).
Local Abbreviation cm_forall_upd := reac_box_catalogue_match.cm_forall_upd.
Local Abbreviation cm_cls_keep1 := (@reac_box_catalogue_match.cm_cls_keep1 f len S FS fb Rf Rlen HK Hfb).
Local Abbreviation cm_cls_rel := (@reac_box_catalogue_match.cm_cls_rel f len S FS fb Rf Rlen HK Hfb).
Local Abbreviation cm_tls_cells := (@reac_box_catalogue_match.cm_tls_cells f len S fb Rf Rlen Hfb).

(* ---- R and its pieces at this Section's binders ---- *)
Local Abbreviation cmR := (reac_box_catalogue_match_shadow_R f len S FS).

(* The ONE place this file unfolds the side-stack class predicate (a Theorem Labs lane 10:5xZ: a change of that leaf reaches
   this file here only): the class-c frames' shadow, c <= 2, is the class-c block. *)
Lemma cm_sm_R_frames : forall c a, (c <= 2)%nat ->
  shadow_addr (fs_frame FS c 0) <= a < shadow_addr (fs_frame FS c (fs_M c)) ->
  asan_stack_malloc_shadow_R FS c a.
Proof.
  intros c a Hc Ha. unfold asan_stack_malloc_shadow_R. cbv beta.
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  unfold shadow_addr, fs_frame, fs_B, fs_M in *.
  destruct c as [|[|[|c]]]; cbn [Z.of_nat Pos.of_succ_nat] in *; try lia; Z.div_mod_to_equations; lia.
Qed.

(* A byte of the class-c frames' shadow, c <= 2, is in R ((FS)). *)
Lemma cm_R_class : forall c a, (c <= 2)%nat ->
  shadow_addr (fs_frame FS c 0) <= a < shadow_addr (fs_frame FS c (fs_M c)) -> cmR a.
Proof.
  intros c a Hc Ha. unfold reac_box_catalogue_match_shadow_R. right; left.
  exists c. split; [exact Hc | exact (cm_sm_R_frames c a Hc Ha)].
Qed.

(* -- cm_Wc_rd: the shadow it re-reads after a class-c callee at sp2 with window K -- *)
Definition cm_Wc_rd_shadow_R (sp2 K : Z) (c : nat) (a : Z) : Prop :=
  shadow_addr (fs_frame FS c 0) <= a < shadow_addr (fs_frame FS c (fs_M c)) \/
  shadow_addr (sp2 - K) <= a < shadow_addr sp2.

(* cm_Wc_rd (reac_box_catalogue_match.v:1711) with its shadow premise narrowed to the two regions it reads. *)
Lemma cm_Wc_rd_on : forall fr sp2 K d n c mc mc', (c <= 2)%nat -> munch (cmWc fr sp2 K d n c) mc mc' ->
  (forall y, fr + d <= y < fr + d + n -> exists b, mrd rsegs mc' (wa y) = Some b) ->
  stk rsegs mc' (sp2 - K) sp2 -> stk rsegs mc' FS (FS + FS_SIZE) ->
  shadow_rw_on (cm_Wc_rd_shadow_R sp2 K c) mc' ->
  (forall a, sp2 - K <= a < sp2 -> app_mem a) -> (sp2 - K) mod 8 = 0 -> rd_mono mc mc'.
Proof.
  intros fr sp2 K d n c mc mc' Hc MU HB STw STf SR' Happ Hm8.
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  pose proof (rd_of_stk mc' _ _ STf) as RF.
  apply (rd_mono_list _ mc mc' MU).
  unfold reac_box_catalogue_match.cmWc. constructor; [exact HB|].
  constructor; [intros y Hy; exact (rd_of_stk mc' _ _ STw y Hy)|].
  apply Forall_app. split.
  - assert (F8 : fs_frame FS c 0 mod 8 = 0).
    { unfold fs_frame, fs_B. destruct c as [|[|[|c]]]; cbn [Z.of_nat Pos.of_succ_nat]; try lia; Z.div_mod_to_equations; lia. }
    assert (FA : forall a, fs_frame FS c 0 <= a < fs_frame FS c (fs_M c) -> app_mem a).
    { intros a Ha. apply FSapp. unfold fs_frame, fs_B, fs_M, FS_SIZE in *.
      destruct c as [|[|[|c]]]; cbn [Z.of_nat Pos.of_succ_nat] in *; try lia. }
    cbn [fp_w flat_map fp_w1 app]. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]];
      cbn [fst snd]; intros y Hy.
    + apply RF. unfold fs_hint, FS_SIZE in *. destruct c as [|[|[|c]]]; cbn [Z.of_nat Pos.of_succ_nat] in *; lia.
    + apply RF. unfold fs_flag, fs_M, FS_SIZE in *. destruct c as [|[|[|c]]]; cbn [Z.of_nat Pos.of_succ_nat] in *; lia.
    + apply RF. unfold fs_frame, fs_B, fs_M, FS_SIZE in *. destruct c as [|[|[|c]]]; cbn [Z.of_nat Pos.of_succ_nat] in *; lia.
    + exact (proj2 (SR' y (or_introl Hy) (cm_sh_in _ _ y F8 FA Hy))).
  - constructor; [|constructor]. cbn [fst snd]. intros y Hy.
    exact (proj2 (SR' y (or_intror Hy) (cm_sh_in _ _ y Hm8 Happ Hy))).
Qed.

(* R covers cm_Wc_rd's region for every callee window inside the run's window. *)
Lemma cm_Wc_rd_R : forall sp2 K c, (c <= 2)%nat -> S - 9136 <= sp2 - K -> sp2 <= S ->
  forall a, cm_Wc_rd_shadow_R sp2 K c a -> cmR a.
Proof.
  intros sp2 K c Hc H1 H2 a [Ha|Ha].
  - exact (cm_R_class c a Hc Ha).
  - unfold reac_box_catalogue_match_shadow_R, CM_K. left. unfold shadow_addr in *. Z.div_mod_to_equations. lia.
Qed.

(* The frame's shadow bytes are in R: (W) for the machine-stack frame CA - 192 (k < 24), the class-2 block for a
   side-stack frame (k < 32). *)
Lemma cm_fr_sh_R : forall fr sp2 jj nn k, cmFK fr sp2 jj nn -> 0 <= k -> (nn = 0 -> k < 24) -> (nn = 1 -> k < 32) ->
  cmR (shadow_addr fr + k).
Proof.
  intros fr sp2 jj nn k FK Hk0 H0 H1.
  pose proof CA_facts as (CAm & CAlo & CAhi).
  destruct FK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)]; subst fr nn.
  - specialize (H0 eq_refl). unfold reac_box_catalogue_match_shadow_R, CM_K. left.
    unfold shadow_addr in *. Z.div_mod_to_equations. lia.
  - specialize (H1 eq_refl). apply (cm_R_class 2); [lia|].
    unfold shadow_addr, fs_frame, fs_B, fs_M in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
    change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in *.
    Z.div_mod_to_equations. lia.
Qed.

(* A buffer [fr + d, fr + d + n) of the frame: its aligned shadow words are in (W) or in the class-2 block. *)
Lemma cm_buf_sh_R : forall fr sp2 jj nn d n, cmFK fr sp2 jj nn -> 0 <= d -> 0 < n -> d + n <= 192 ->
  forall a, sh_word_on.sh_word_on (fr + d) n a -> cmR a.
Proof.
  intros fr sp2 jj nn d n FK Hd Hn Hdn a (_ & Ha).
  pose proof CA_facts as (CAm & CAlo & CAhi).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  unfold rng_asan.sh_al8_lo, rng_asan.sh_al8_hi in Ha.
  destruct FK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)]; subst fr.
  - unfold reac_box_catalogue_match_shadow_R, CM_K. left. unfold shadow_addr in *. Z.div_mod_to_equations. lia.
  - apply (cm_R_class 2); [lia|].
    unfold shadow_addr, fs_frame, fs_B, fs_M, ASAN_K in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
    change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in *.
    Z.div_mod_to_equations. lia.
Qed.

(* The bcmp wrapper at 0x846dc (reac_box_catalogue_match.v:2520: L = f + 18, R = fr + 112, N = 32): its R is in R. *)
Lemma cm_R_bcmp : forall fr sp2 jj nn, cmFK fr sp2 jj nn -> 50 <= len ->
  forall a, bcmp_wrap_shadow_R (f + 18) (fr + 112) 32 a -> cmR a.
Proof.
  intros fr sp2 jj nn FK L a [(_ & Ha)|Ha].
  - unfold reac_box_catalogue_match_shadow_R. right; right. split; [exact L|]. left. split; [lia|].
    unfold rng_asan.sh_al8_lo, rng_asan.sh_al8_hi, shadow_addr in *. Z.div_mod_to_equations. lia.
  - exact (cm_buf_sh_R fr sp2 jj nn 112 32 FK ltac:(lia) ltac:(lia) ltac:(lia) a Ha).
Qed.

(* __asan_stack_malloc_2 at 0x84504 (reac_box_catalogue_match.v:972): its R (class 2) is in R. *)
Lemma cm_R_sm2 : forall a, asan_stack_malloc_shadow_R FS 2 a -> cmR a.
Proof. intros a Ha. unfold reac_box_catalogue_match_shadow_R. right; left. exists 2%nat. split; [lia | exact Ha]. Qed.

(* reac_ctrl_parse at 0x84684 (reac_box_catalogue_match.v:2017: f, n = len, o = fr + 32, S = sp2, FS): its R
   (a Theorem Labs lane's, class 1) is in R. *)
Lemma cm_R_parse : forall fr sp2 jj nn, cmFK fr sp2 jj nn -> 50 <= len ->
  forall a, reac_ctrl_parse_shadow_R f len (fr + 32) sp2 FS a -> cmR a.
Proof.
  intros fr sp2 jj nn FK L a [Ha|[Ha|[(_ & Ha)|[(_ & Ha)|(_ & Ha)]]]].
  - pose proof CA_facts as (CAm & CAlo & CAhi).
    unfold reac_box_catalogue_match_shadow_R, CM_K. left.
    destruct FK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)]; subst sp2;
      unfold shadow_addr in *; Z.div_mod_to_equations; lia.
  - unfold reac_box_catalogue_match_shadow_R. right; left. exists 1%nat. split; [lia | exact Ha].
  - exact (cm_buf_sh_R fr sp2 jj nn 32 36 FK ltac:(lia) ltac:(lia) ltac:(lia) a Ha).
  - unfold reac_box_catalogue_match_shadow_R. right; right. split; [exact L | left; exact Ha].
  - unfold reac_box_catalogue_match_shadow_R. right; right. split; [exact L | right; right; exact Ha].
Qed.

(* reac_box_model_block at 0x846c8 (reac_box_catalogue_match.v:2344: p = CM_T + 296 i, b = 0, o = fr + 112, S = sp2,
   FS): at b = 0 the name / JOIN disjuncts are false; its window words, its class-0 block, the row's words and the
   buffer's words are in R. *)
Lemma cm_R_mb : forall fr sp2 jj nn (i : nat) row nb, cmFK fr sp2 jj nn -> 50 <= len -> (i < 11)%nat ->
  forall a, reac_box_model_block_shadow_R sp2 FS (CM_T + 296 * Z.of_nat i) 0 (fr + 112) row nb a -> cmR a.
Proof.
  intros fr sp2 jj nn i row nb FK L Hi a [Ha|[Ha|[(_ & _ & Ha)|[(_ & Hb & _)|[(_ & Ha)|[(Hb & _)|(Hb & _)]]]]]].
  - pose proof CA_facts as (CAm & CAlo & CAhi).
    destruct Ha as (_ & Ha). unfold reac_box_catalogue_match_shadow_R, CM_K. left.
    unfold rng_asan.sh_al8_lo, rng_asan.sh_al8_hi, REAC_BOX_MODEL_BLOCK_K in Ha.
    destruct FK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)]; subst sp2;
      unfold shadow_addr in *; Z.div_mod_to_equations; lia.
  - unfold reac_box_catalogue_match_shadow_R. right; left. exists 0%nat. split; [lia | exact Ha].
  - unfold reac_box_catalogue_match_shadow_R. right; right. split; [exact L|]. right; left.
    split; [lia|]. unfold rng_asan.sh_al8_lo, rng_asan.sh_al8_hi, shadow_addr in *. Z.div_mod_to_equations. lia.
  - destruct Hb; lia.
  - exact (cm_buf_sh_R fr sp2 jj nn 112 32 FK ltac:(lia) ltac:(lia) ltac:(lia) a Ha).
  - lia.
  - lia.
Qed.

(* -- the post form along a run: every region of m stays present (the exit carries it across each store) -- *)
Definition srw_post (mc : word -> option byte) : Prop := forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P mc.

Lemma cm_post_srw_inv : forall mc, wmono rsegs m mc -> rd_mono m mc -> srw_post mc.
Proof. intros mc WM RM P H. exact (A.ShadowRwOnT.shadow_rw_on_mem_mono P m mc H WM RM). Qed.

Lemma cm_post_srw_write : forall mc a bs, srw_post mc -> srw_post (write_to_mem mc a bs).
Proof. intros mc a bs H P HP. exact (cm_shadow_rw_write_on mc a bs P (H P HP)). Qed.

(* ---- re-proved: the old scripts, renamed `<name>_on`; changed steps listed in the header ---- *)

(* Each frame is 8-aligned, below the window top, writable and application memory, with writable shadow bytes. *)
Lemma fk_facts_on : forall fr sp2 jj nn, cmFK fr sp2 jj nn ->
  fr mod 8 = 0 /\ 0 < fr /\ fr + 192 <= CA /\
  (forall i, 0 <= i < 192 -> wview rsegs m (wa (fr + i)) <> None) /\
  (forall i, 0 <= i < 192 -> app_mem (fr + i)) /\
  (forall i, 0 <= i < 24 -> wview rsegs m (wa (fr / 8 + ASAN_K + i)) <> None) /\
  (sp2 = CA \/ sp2 = CA - 192).
Proof.
  intros fr sp2 jj nn HFK.
  pose proof CA_facts as (CAm & CAlo & CAhi).
  destruct FP0 as (DT & TS & C & T & DB & kk & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & _ & HFS & _).
  unfold FS_SIZE in HFS, P4. pose proof P5 as (_ & _ & P5h). unfold FS_SIZE in P5h.
  pose proof ST as (_ & _ & STh). destruct AW as (_ & _ & _ & AWh).
  assert (BASE : fr mod 8 = 0 /\ 0 < fr /\ fr + 192 <= CA /\
    (forall i, 0 <= i < 192 -> wview rsegs m (wa (fr + i)) <> None) /\
    (forall i, 0 <= i < 192 -> app_mem (fr + i)) /\ (sp2 = CA \/ sp2 = CA - 192)).
  { destruct HFK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)]; subst fr sp2.
    - split; [unfold reac_box_catalogue_match.CA; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
      split; [intros i Hi; apply (proj1 (STh (CA - 192 + i) ltac:(lia)))|].
      split; [|right; reflexivity].
      intros i Hi. replace (CA - 192 + i) with (S - 9136 + (CA - 192 + i - (S - 9136))) by lia.
      exact (proj1 (AWh (CA - 192 + i - (S - 9136)) ltac:(lia))).
    - assert (M8 : fs_frame FS 2 jj mod 8 = 0).
      { unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
        change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. Z.div_mod_to_equations; lia. }
      assert (LO : FS + 36864 <= fs_frame FS 2 jj).
      { unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
        change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. lia. }
      assert (HI : fs_frame FS 2 jj + 256 <= FS + FS_SIZE).
      { unfold fs_frame, fs_B, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
        change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. change (2 ^ 12) with 4096 in Hj.
        unfold FS_SIZE. lia. }
      unfold FS_SIZE in HI.
      split; [exact M8|]. split; [lia|]. split; [lia|].
      split; [intros i Hi; exact (proj1 (P5h (fs_frame FS 2 jj + i) ltac:(lia)))|].
      split; [|left; reflexivity].
      intros i Hi. apply P4. lia. }
  destruct BASE as (B1 & B2 & B3 & B4 & B5 & B6).
  split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|].
  split; [|exact B6].
  intros i Hi. pose proof (B5 (8 * i) ltac:(lia)) as Ap.
  pose proof (rt_app_shadow (fr + 8 * i) Ap) as Sh.
  replace (fr / 8 + ASAN_K + i) with (shadow_addr (fr + 8 * i))
    by (rewrite (cm_sh_add8 fr i B1); unfold shadow_addr; lia).
  assert (HR : cmR (shadow_addr (fr + 8 * i))).
  { rewrite (cm_sh_add8 fr i B1).
    apply (cm_fr_sh_R fr sp2 jj nn i HFK ltac:(lia) ltac:(intros; lia) ltac:(intros; lia)). }
  exact (proj1 (SR_on _ HR Sh)).
Qed.


(* The state carried from the entry to the gate (pc 0x845dc): the geometry, the write relation, the runtime cells,
   the whole side-stack state (fp [0;1;2]), the callee window addressable, the saves, and (side path) the flag
   pointer word the epilogue reads. *)
Definition cmInv_on (fr sp2 jj nn : Z) (mc : word -> option byte) : Prop :=
  cmFK fr sp2 jj nn /\
  munch aWc m mc /\ wmono rsegs m mc /\ rd_mono m mc /\ mem_inv rsegs mc /\
  asan_cells mc /\ shadow_rw_on cmR mc /\
  fp [0%nat; 1%nat; 2%nat] mc (bv_unsigned tp) FS (S - 9136) S aWf aDf /\ aTL mc /\
  addressable mc (sp2 - 8800) 8800 /\ cmAWX fr mc /\
  rw_cells rsegs mc (S - 96) cmSAVES /\
  (nn = 1 -> bytes_at rsegs mc (fr + 248) (le8 (Z_to_bv 64 (fs_flag FS 2 jj)))).


(* The register state at the gate (0x845dc): s0 = S, s1 = CA, s2 = frame (0 real / fr side), s3 = f, s4 = len,
   s5 = ASAN_K, s6 = shadow_addr fr, s7 = fr, a2 = 50. *)
Definition cmKB_on (Q : machine_state -> Prop) : Prop :=
  forall (fr sp2 jj nn : Z) (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    cmInv_on fr sp2 jj nn mc ->
    evt rsegs Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               ra0 ra1 (Z_to_bv 64 50) ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
               (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x845dc) fc None mc (seg_rom rsegs)).

(* An application byte apart from the header's two application ranges (the sd s7 slot at CA+24 and the three header
   words at fr) is apart from the whole header footprint cmHF (its shadow range is in shadow memory). *)
Lemma cmHF_out_pt_on : forall fr sp2 jj nn x, cmFK fr sp2 jj nn -> app_mem x ->
  ~ (CA + 24 <= x < CA + 32) -> ~ (fr <= x < fr + 24) -> outside (cmHF fr) x.
Proof.
  intros fr sp2 jj nn x FK Hap H1 H2.
  pose proof (fk_facts_on fr sp2 jj nn FK) as (FR8 & FRpos & _ & _ & _ & _ & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (_ & FRhi).
  pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
  unfold reac_box_catalogue_match.cmHF. cbn [outside]. split; [exact H1|]. split; [exact H2|]. split; [|exact I].
  pose proof (acl_sh_out x fr (fr + 8 * 24) Hap ltac:(lia) ltac:(lia)) as Ho.
  rewrite (cm_sh_add8 fr 24 FR8) in Ho. exact Ho.
Qed.


(* A byte of the side stack's header [FS, FS + 36864) is apart from the header footprint cmHF. *)
Lemma cmHF_out_side_on : forall fr sp2 jj nn x, cmFK fr sp2 jj nn -> FS <= x < FS + 36864 -> outside (cmHF fr) x.
Proof.
  intros fr sp2 jj nn x FK Hx.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). unfold FS_SIZE in FShi.
  assert (Hap : app_mem x) by (apply FSapp; unfold FS_SIZE; lia).
  apply (cmHF_out_pt_on fr sp2 jj nn x FK Hap).
  - lia.
  - destruct FK as [(Ef & _ & _ & _) | (Hj & Ef & _ & _)]; subst fr.
    + lia.
    + unfold fs_frame, fs_B. cbn [Z.of_nat]. change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. lia.
Qed.


(* A byte of the runtime's cells [RT_LO, RT_HI) is apart from the header footprint cmHF. *)
Lemma cmHF_out_rt_on : forall fr sp2 jj nn x, cmFK fr sp2 jj nn -> RT_LO <= x < RT_HI -> outside (cmHF fr) x.
Proof.
  intros fr sp2 jj nn x FK Hx.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & _).
  pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'.
  unfold RT_LO, RT_HI in Hx.
  assert (Hap : app_mem x) by (unfold app_mem, LOWMEM_END; left; lia).
  apply (cmHF_out_pt_on fr sp2 jj nn x FK Hap).
  - lia.
  - unfold ASAN_GT in FRgt. lia.
Qed.


(* The 12 saved registers [S - 96, S) are apart from the header footprint cmHF. *)
Lemma cmHF_out_saves_on : forall fr sp2 jj nn x, cmFK fr sp2 jj nn -> S - 96 <= x < S -> outside (cmHF fr) x.
Proof.
  intros fr sp2 jj nn x FK Hx.
  pose proof CA_facts as (CA32 & CAlo & CAhi). pose proof cm_CA_lo as (CAlo2 & CAhi2).
  pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'.
  pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). unfold FS_SIZE in FShi.
  assert (Hap : app_mem x) by (right; unfold HIGHMEM_BEG, APPMEM_END; lia).
  apply (cmHF_out_pt_on fr sp2 jj nn x FK Hap).
  - lia.
  - destruct FK as [(Ef & _ & _ & _) | (Hj & Ef & _ & _)]; subst fr.
    + lia.
    + unfold fs_frame, fs_B, fs_M in Hj |- *. cbn [Z.of_nat] in Hj |- *.
      change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in Hj. lia.
Qed.


(* The epilogue's flag-pointer word [fr + 248, fr + 256) (side path) is apart from the header footprint cmHF. *)
Lemma cmHF_out_flag_on : forall fr sp2 jj nn x, cmFK fr sp2 jj nn -> nn = 1 -> fr + 248 <= x < fr + 256 ->
  outside (cmHF fr) x.
Proof.
  intros fr sp2 jj nn x FK Enn Hx.
  pose proof CA_facts as (CA32 & CAlo & CAhi). pose proof cm_CA_lo as (CAlo2 & CAhi2).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). unfold FS_SIZE in FShi.
  pose proof FK as FKc.
  destruct FK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)].
  - subst nn. discriminate Enn.
  - assert (FRlo : FS + 36864 <= fr).
    { rewrite Ef. unfold fs_frame, fs_B. cbn [Z.of_nat]. change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. lia. }
    assert (FRhi2 : fr + 256 <= FS + 11571200).
    { rewrite Ef. unfold fs_frame, fs_B, fs_M in Hj |- *. cbn [Z.of_nat] in Hj |- *.
      change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. change (2 ^ (14 - 2)) with 4096 in Hj. lia. }
    assert (Hap : app_mem x) by (apply FSapp; unfold FS_SIZE; lia).
    apply (cmHF_out_pt_on fr sp2 jj nn x FKc Hap).
    + lia.
    + lia.
Qed.


(* The shadow byte of a byte of the callee window [sp2 - 8800, sp2) is apart from the header footprint cmHF. *)
Lemma cmHF_sh_body_on : forall fr sp2 jj nn y, cmFK fr sp2 jj nn -> app_mem y -> sp2 - 8800 <= y < sp2 ->
  outside (cmHF fr) (shadow_addr y).
Proof.
  intros fr sp2 jj nn y FK Hap Hy.
  pose proof CA_facts as (CA32 & CAlo & CAhi). pose proof cm_CA_lo as (CAlo2 & CAhi2).
  pose proof (fk_facts_on fr sp2 jj nn FK) as (FR8 & FRpos & _ & _ & FAPP & _ & _).
  pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'. pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). unfold FS_SIZE in FShi.
  pose proof (rt_app_shadow y Hap) as Hsh.
  unfold reac_box_catalogue_match.cmHF. cbn [outside]. split; [|split; [|split; [|exact I]]].
  - apply (sh_out_app (shadow_addr y) (CA + 24) (CA + 32) Hsh).
    intros z Hz. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. right. lia.
  - apply (sh_out_app (shadow_addr y) fr (fr + 24) Hsh).
    intros z Hz. replace z with (fr + (z - fr)) by lia. apply FAPP. lia.
  - destruct FK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)]; subst fr sp2.
    + pose proof (acl_win_sh y (CA - 192) (CA - 192 + 8 * 24) FR8 ltac:(lia)) as Ho.
      rewrite (cm_sh_add8 (CA - 192) 24 FR8) in Ho. exact Ho.
    + assert (LEf : fs_frame FS 2 jj + 8 * 24 <= y).
      { unfold fs_frame, fs_B, fs_M in Hj |- *. cbn [Z.of_nat] in Hj |- *.
        change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in Hj. lia. }
      pose proof (acl_win_sh y (fs_frame FS 2 jj) (fs_frame FS 2 jj + 8 * 24) FR8 ltac:(lia)) as Ho.
      rewrite (cm_sh_add8 (fs_frame FS 2 jj) 24 FR8) in Ho. exact Ho.
Qed.


(* The shadow byte of a window byte outside the frame is apart from the header footprint cmHF. *)
Lemma cmHF_sh_win_on : forall fr sp2 jj nn y, cmFK fr sp2 jj nn -> S - 9136 <= y < S -> ~ (fr <= y < fr + 192) ->
  outside (cmHF fr) (shadow_addr y).
Proof.
  intros fr sp2 jj nn y FK Hy Hyf.
  pose proof CA_facts as (CA32 & CAlo & CAhi). pose proof cm_CA_lo as (CAlo2 & CAhi2).
  pose proof (fk_facts_on fr sp2 jj nn FK) as (FR8 & FRpos & _ & _ & FAPP & _ & _).
  pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'. pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
  assert (Hap : app_mem y) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; right; lia).
  pose proof (rt_app_shadow y Hap) as Hsh.
  unfold reac_box_catalogue_match.cmHF. cbn [outside]. split; [|split; [|split; [|exact I]]].
  - apply (sh_out_app (shadow_addr y) (CA + 24) (CA + 32) Hsh).
    intros z Hz. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. right. lia.
  - apply (sh_out_app (shadow_addr y) fr (fr + 24) Hsh).
    intros z Hz. replace z with (fr + (z - fr)) by lia. apply FAPP. lia.
  - pose proof (acl_win_sh y fr (fr + 8 * 24) FR8 ltac:(lia)) as Ho.
    rewrite (cm_sh_add8 fr 24 FR8) in Ho. exact Ho.
Qed.


(* The invariant survives the header run: writes land only in cmHF, which is inside the caller footprint aWc
   (cm_sub), and the side stack's class bytes fp_w [0;1;2] and the window shadow (fl_fp_free). *)
Lemma cm_inv_step_on : forall fr sp2 jj nn mc mc',
  cmInv_on fr sp2 jj nn mc ->
  munch (cmHF fr) mc mc' -> wmono rsegs mc mc' -> rd_mono mc mc' -> mem_inv rsegs mc' ->
  cmInv_on fr sp2 jj nn mc'.
Proof.
  intros fr sp2 jj nn mc mc' INV MU WM RM MI'.
  destruct INV as (FK & MUmc & WMmc & RMmc & MImc & ACmc & SRmc & FPg & TLg & ADg & AWXg & SVg & FLg).
  pose proof (cm_sub fr sp2 jj nn FK) as SUB.
  pose proof FPg as FPpack.
  destruct FPg as (DT0 & TS0 & C0 & T0 & DB0 & kk0 & HT0 & HTPle & HPl & H88 & H96 & HCL & HFSlo & HApphi & HWd & HDd).
  destruct HPl as (HP1 & HP2 & HP3 & HP4 & HPstk).
  split; [exact FK|].
  split; [exact (munch_trans aWc m mc mc' MUmc (munch_weaken (cmHF fr) aWc mc mc' SUB MU))|].
  split; [exact (wmono_trans rsegs m mc mc' WMmc WM)|].
  split; [exact (rd_mono_trans m mc mc' RMmc RM)|].
  split; [exact MI'|].
  split; [exact (fl_asan_cells (cmHF fr) mc mc' ACmc MU (fun x Hx => cmHF_out_rt_on fr sp2 jj nn x FK Hx))|].
  split; [exact (A.ShadowRwOnT.shadow_rw_on_mem_mono _ mc mc' SRmc WM RM)|].
  split.
  { apply (fl_fp_free [0%nat; 1%nat; 2%nat] mc mc' (bv_unsigned tp) FS (S - 9136) S aWf aDf (cmHF fr) FPpack TLg MU WM).
    - unfold reac_box_catalogue_match.aWf, reac_box_catalogue_match.aWc, reac_box_catalogue_match.aXs. cbn [app]. exact SUB.
    - intros x Hx. apply (cmHF_out_side_on fr sp2 jj nn x FK). lia.
    - intros x Hx. right. apply RM. exact (rd_of_stk mc FS (FS + FS_SIZE) HPstk x Hx).
    - intros c Hc.
      pose proof (proj1 (Forall_forall _ _) HCL c Hc) as (Hc6 & h & flags & HH & HFf & HLn & HF01).
      split.
      + exists h. apply (fl_bytes (cmHF fr) mc mc' (fs_hint FS c) (le8 h) HH MU).
        intros x Hx. rewrite length_le8 in Hx. apply (cmHF_out_side_on fr sp2 jj nn x FK).
        unfold fs_hint in Hx. lia.
      + exists flags. split; [|split; [exact HLn | exact HF01]].
        apply (fl_bytes (cmHF fr) mc mc' (fs_flag FS c 0) flags HFf MU).
        intros x Hx. rewrite HLn in Hx. apply (cmHF_out_side_on fr sp2 jj nn x FK).
        unfold fs_flag, fs_M in Hx. destruct Hc as [E | [E | [E | []]]]; subst c; cbn [Z.of_nat] in Hx.
        * change (2 ^ 15) with 32768 in Hx. change (2 ^ (15 - 0)) with 32768 in Hx.
          change (2 ^ (14 - 0)) with 16384 in Hx. lia.
        * change (2 ^ 15) with 32768 in Hx. change (2 ^ (15 - 1)) with 16384 in Hx.
          change (2 ^ (14 - 1)) with 8192 in Hx. lia.
        * change (2 ^ 15) with 32768 in Hx. change (2 ^ (15 - 2)) with 8192 in Hx.
          change (2 ^ (14 - 2)) with 4096 in Hx. lia. }
  split.
  { intros DT TS C T DB kk HTcells'.
    assert (Hc : Forall (fun d => forall x, fst d <= x < snd d -> outside (cmHF fr) x)
                   (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0)).
    { apply Forall_forall. intros [a b] Hin x Hx. apply SUB. unfold reac_box_catalogue_match.aWc. cbn [outside]. split.
      - pose proof (fl_dj_out aWf (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0 ++ [(FS, fs_frame FS 0 0)]) a b x
                      HWd (in_or_app _ _ _ (or_introl Hin)) Hx) as Ho.
        unfold reac_box_catalogue_match.aWf in Ho. cbn [outside] in Ho. exact (proj1 Ho).
      - exact (fl_dj_out_r (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0) aXs a b x
                 (TLg DT0 TS0 C0 T0 DB0 kk0 HT0) Hin Hx). }
    destruct (fl_tls_same mc mc' (cmHF fr) (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0 DT TS C T DB kk HT0 HTcells' MU Hc)
      as (E1 & E2 & E3 & E4 & E5 & E6). subst DT0 TS0 C0 T0 DB0 kk0.
    exact (TLg DT TS C T DB kk HT0). }
  split.
  { apply (addr_munch (cmHF fr) mc mc' (sp2 - 8800) 8800 ADg MU).
    intros i Hi. apply (cmHF_sh_body_on fr sp2 jj nn (sp2 - 8800 + i) FK).
    - destruct ADg as (_ & _ & _ & ADbytes). exact (proj1 (ADbytes i Hi)).
    - lia. }
  split.
  { intros x Hx Hxf.
    exact (cm_ab_keep (cmHF fr) mc mc' x (AWXg x Hx Hxf) MU (cmHF_sh_win_on fr sp2 jj nn x FK Hx Hxf)). }
  split.
  { apply (acl_rw (cmHF fr) mc mc' (S - 96) cmSAVES SVg MU WM).
    intros x Hx. apply (cmHF_out_saves_on fr sp2 jj nn x FK).
    unfold reac_box_catalogue_match.cmSAVES in Hx. cbn [cells_size csize] in Hx. lia. }
  intros Enn.
  apply (fl_bytes (cmHF fr) mc mc' (fr + 248) (le8 (Z_to_bv 64 (fs_flag FS 2 jj))) (FLg Enn) MU).
  intros x Hx. rewrite length_le8 in Hx. apply (cmHF_out_flag_on fr sp2 jj nn x FK Enn). lia.
Qed.


(* The ASan shadow-check tactics this proof uses (chk_core with pre_sr / no_extra), file-local. The text is that of the
   longer image-A reac_box_model_block.v (blob 0dcbcb8154d, lines 313-351), which this proof was written against; the
   reac_box_model_block.v of this tree (after the MemMono split) does not define them. *)
Ltac steps_until_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; steps_until_if
  | _ => idtac
  end.


Ltac bjoin G r := lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.


Ltac chk_core X RX r SH pre extra :=
  let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
  destruct SH as (k & RK & OK & KR);
  pre X RX; steps_until_if; clear RK;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by (clear -KR; lia);
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evt segs Q (MS (bvmap_set r rr R) F B fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ bjoin G r
        | step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_land7; extra X;
          step;
          let MB := fresh "MB" in pose proof (Z.mod_pos_bound X 8 eq_refl) as MB;
          first [ rewrite (rc_lts_signed (X mod 8) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia])
                | rewrite (rc_lts_signed (X mod 8 + 1) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 + 1 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia])
                | rewrite (rc_lts_signed (X mod 8 + 3) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 + 3 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia]) ];
          clear MB; bjoin G r ]
      | intros ?; simp_regs; clear OK KR ]
  end.


Ltac pre_sr X RX := step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_shr3.

Ltac no_extra X := idtac.


Ltac cm_wv :=
  let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
  match goal with
  | |- wview _ _ (wa ?x) <> None =>
    first
      [ match goal with H : forall a, _ -> wview rsegs m (wa a) <> None |- _ => apply H; lia end
      | match goal with H : forall k, 0 <= k < 192 -> wview rsegs m (wa (?fr + k)) <> None |- _ =>
          replace x with (fr + (x - fr)) by lia; apply H; lia end
      | match goal with H : forall k, 0 <= k < 24 -> wview rsegs m (wa (?s + k)) <> None |- _ =>
          replace x with (s + (x - s)) by lia; apply H; lia end ]
  end.


Ltac cm_wst a n :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs mm (wa a) n = true)
        by (eapply wv_store_ok;
            [ cm_wv | eassumption
            | try unfold ASAN_K; Z.div_mod_to_equations; lia
            | try unfold ASAN_K; Z.div_mod_to_equations; lia ])
  end.


(* The header run from 0x84538 to the gate at 0x845dc: the sd s7 at CA+24, the three header words at fr, fr+8, fr+16,
   and the 24 shadow bytes at shadow_addr fr + 0..23; it reaches the gate in the cmKB_on register state and rebuilds the
   invariant at the written memory (cm_inv_step_on), then hands control to the gate (eapply K). *)
Lemma cm_header_on : forall (Q : machine_state -> Prop) (fr sp2 jj nn : Z) (mc : word -> option byte)
    (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs6 rt3 rt4 rt5 rt6 : word),
  cmKB_on Q -> cmInv_on fr sp2 jj nn mc ->
  evt rsegs Q
    (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
             ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             rs6 (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
         F (Z_to_bv 64 0x84538) fc None mc (seg_rom rsegs)).
Proof.
  intros Q fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs6 rt3 rt4 rt5 rt6 K INV.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof cm_CA_lo as (CAlo2 & CAhi2).
  pose proof INV as INVk.
  destruct INV as (FK & MUg & WMg & RMg & MIg & ACg & SRg & FPg & TLg & ADg & AWXg & SVg & FLg).
  clear MUg.
  pose proof (fk_facts_on fr sp2 jj nn FK) as (FR8 & FRpos & FR192 & FW & FAP & FSW & FSPc).
  assert (cmSTW : forall a, S - 9136 <= a < S -> wview rsegs m (wa a) <> None)
    by (intros a Ha; exact (stk_wv m _ _ _ ST Ha)).
  assert (MUh : munch (cmHF fr) mc mc) by apply munch_refl.
  assert (WMh : wmono rsegs mc mc) by apply wmono_refl.
  assert (RMh : rd_mono mc mc) by apply rd_mono_refl.
  unfold reac_box_catalogue_match.cmHF, shadow_addr in MUh.
  cm_wst (CA + 24) 8%nat. step. store_done.
  do 3 step.
  step. rewrite (unsigned_lit fr) by lia. rewrite rc_shr3.
  do 6 step.
  cm_wst fr 8%nat. step. store_done.
  cm_wst (fr + 8) 8%nat. step. store_done.
  cm_wst (fr + 16) 8%nat. step. store_done.
  step. step.
  assert (SHlo : 0 <= fr / 8 + ASAN_K).
  { assert (0 <= fr / 8) by (apply Z.div_pos; lia). unfold ASAN_K; lia. }
  assert (SHhi : fr / 8 + ASAN_K + 24 <= 2 ^ 64).
  { unfold ASAN_K. Z.div_mod_to_equations. lia. }
  cm_wst (fr / 8 + ASAN_K) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 1) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 2) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 3) 1%nat. step. store_done.
  step.
  cm_wst (fr / 8 + ASAN_K + 4) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 5) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 6) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 7) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 8) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 9) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 10) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 11) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 12) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 13) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 14) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 15) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 20) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 21) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 22) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 23) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 16) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 17) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 18) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 19) 1%nat. step. store_done.
  eapply K.
  eapply cm_inv_step_on; [exact INVk | exact MUh | exact WMh | exact RMh | exact MIg].
Qed.


(* Build cmInv_on at the join from: the frame facts, the run's footprint Wm (inside aWc), the class hint/flag readback,
   the saves and (side path) the flag word. The asan state is rebuilt by fl_fp_free / fl_tls_same / addr_munch. *)
Lemma cm_mk_inv_on : forall (fr sp2 jj nn : Z) (mc : word -> option byte) (Wm : list ivl),
  cmFK fr sp2 jj nn ->
  munch Wm m mc -> wmono rsegs m mc -> rd_mono m mc -> mem_inv rsegs mc ->
  sub_fp Wm aWc ->
  (forall y, S - 9136 <= y < S -> app_mem y -> outside Wm (shadow_addr y)) ->
  (forall c, In c [0%nat; 1%nat; 2%nat] ->
     (exists h', bytes_at rsegs mc (fs_hint FS c) (le8 h')) /\
     (exists flags', bytes_at rsegs mc (fs_flag FS c 0) flags' /\ Z.of_nat (length flags') = fs_M c /\
        Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags')) ->
  rw_cells rsegs mc (S - 96) cmSAVES ->
  (nn = 1 -> bytes_at rsegs mc (fr + 248) (le8 (Z_to_bv 64 (fs_flag FS 2 jj)))) ->
  cmInv_on fr sp2 jj nn mc.
Proof.
  intros fr sp2 jj nn mc Wm FK MUw WMw RMw MIw SUBw SHW Hcls SAVESmc FLAGmc.
  pose proof (fk_facts_on fr sp2 jj nn FK) as (FR8 & FRpos & FR192 & FW & FAP & FSW & FSPc).
  pose proof CA_facts as (CA32 & CAlo & CAhi). pose proof cm_CA_lo as (CAlo2 & CAhi2).
  pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
  pose proof FP0 as FPpack0.
  pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & kk0 & HT0 & HTP0 & HPl0 & H880 & H960 & HCL0 & HFS0 & HApp0 & HWd0 & HDd0).
  pose proof HPl0 as (P1 & P2 & P3 & P4 & P5).
  split; [exact FK|].
  split; [exact (munch_weaken Wm aWc m mc SUBw MUw)|].
  split; [exact WMw|].
  split; [exact RMw|].
  split; [exact MIw|].
  split; [exact (fl_asan_cells Wm m mc AC MUw (fun x Hx => SUBw x (acl_rt_out_Wc x Hx)))|].
  split; [exact (A.ShadowRwOnT.shadow_rw_on_mem_mono _ m mc SR_on WMw RMw)|].
  split.
  { apply (fl_fp_free [0%nat; 1%nat; 2%nat] m mc (bv_unsigned tp) FS (S - 9136) S aWf aDf Wm FPpack0 TLS0 MUw WMw).
    - exact SUBw.
    - intros x Hx. apply SUBw. exact (acl_hdr_out_Wc x Hx).
    - intros x Hx. right. apply RMw. exact (rd_of_stk m FS (FS + FS_SIZE) P5 x Hx).
    - exact Hcls. }
  split.
  { intros DT TS C T DB kk HTcells.
    assert (apart : Forall (fun d => forall x, fst d <= x < snd d -> outside Wm x)
                      (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0)).
    { apply Forall_forall. intros [a b] Hin x Hx. apply SUBw. unfold reac_box_catalogue_match.aWc. cbn [outside]. split.
      - pose proof (fl_dj_out aWf (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0 ++ [(FS, fs_frame FS 0 0)]) a b x
                      HWd0 (in_or_app _ _ _ (or_introl Hin)) Hx) as Ho.
        unfold reac_box_catalogue_match.aWf in Ho. cbn [outside] in Ho. exact (proj1 Ho).
      - exact (fl_dj_out_r (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0) aXs a b x
                 (TLS0 DT0 TS0 C0 T0 DB0 kk0 HT0) Hin Hx). }
    destruct (fl_tls_same m mc Wm (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0 DT TS C T DB kk HT0 HTcells MUw apart)
      as (E1 & E2 & E3 & E4 & E5 & E6). subst DT0 TS0 C0 T0 DB0 kk0.
    exact (TLS0 DT TS C T DB kk HT0). }
  split.
  { assert (ADm : addressable m (sp2 - 8800) 8800).
    { apply (acl_addr_sub m (S - 9136) 9136 (sp2 - 8800) 8800 AW);
        destruct FSPc as [Esp|Esp]; try rewrite Esp; lia. }
    apply (addr_munch Wm m mc (sp2 - 8800) 8800 ADm MUw).
    intros i Hi. apply SHW.
    - destruct FSPc as [Esp|Esp]; rewrite Esp; lia.
    - right. unfold HIGHMEM_BEG, APPMEM_END. destruct FSPc as [Esp|Esp]; rewrite Esp; lia. }
  split.
  { intros x Hx _.
    pose proof AW as AWc. destruct AWc as (_ & _ & _ & AWb).
    pose proof (AWb (x - (S - 9136)) ltac:(clear -Hx; lia)) as ABx.
    replace (S - 9136 + (x - (S - 9136))) with x in ABx by (clear; lia).
    exact (cm_ab_keep Wm m mc x ABx MUw (SHW x Hx (proj1 ABx))). }
  split; [exact SAVESmc|].
  exact FLAGmc.
Qed.


(* A side-stack header byte (a hint or flag of class 0/1/2) is apart from the side-arm footprint: the data ranges by
   lia (with FShi, Hfrlo, the jj bound), the frame's shadow range by acl_sh_out (app vs shadow). *)
Ltac cm_hdr_out HFSapp HHm8 :=
  cbn [outside]; unfold fs_hint, fs_flag, fs_M in *; cbn [Z.of_nat] in *;
  repeat first [ change (2 ^ 15) with 32768 in *
               | change (2 ^ (15 - 0)) with 32768 in *
               | change (2 ^ (14 - 0)) with 16384 in *
               | change (2 ^ (15 - 1)) with 16384 in *
               | change (2 ^ (14 - 1)) with 8192 in *
               | change (2 ^ (15 - 2)) with 8192 in * ];
  repeat split; try exact I;
  first
    [ lia
    | match goal with
      | |- ~ (shadow_addr ?frr <= ?xx < _) =>
          let A := fresh "A" in let B := fresh "B" in intros [A B];
          pose proof (acl_sh_out xx frr (frr + 8 * 32) ltac:(apply HFSapp; unfold FS_SIZE; lia)
                        ltac:(lia) ltac:(unfold APPMEM_END; lia)) as Hso;
          rewrite (cm_sh_add8 frr 32 HHm8) in Hso; apply Hso; split; [exact A | exact B]
      end ].


Lemma cm_entry_on : forall (Q : machine_state -> Prop) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  cmKB_on Q ->
  evt rsegs Q
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 REAC_BOX_CATALOGUE_MATCH) fc None m (seg_rom rsegs)).
Proof.
  intros Q t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 K.
  unfold REAC_BOX_CATALOGUE_MATCH.
  assert (STbox : stk rsegs m (S - 9136) S /\ True) by (split; [exact ST | exact I]).
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof cm_CA_lo as (CAlo2 & CAhi2).
  pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
  pose proof AC as (CK & GCK & _ & _ & _ & UA & GUA & _).
  unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR in CK, GCK, UA, GUA.
  apply bytes_ro8 in CK. apply bytes_ro8 in GCK. apply bytes_ro4 in UA. apply bytes_ro8 in GUA.
  unfold REAL_BCMP, REAL_MEMCMP, GOT_CF, CF in HBCMP, HMEMCMP, HGOT, HCF254, HCF255.
  assert (MU : munch [(S - 9136, S)] m m) by apply munch_refl.
  assert (WM : wmono rsegs m m) by apply wmono_refl.
  assert (RM : rd_mono m m) by apply rd_mono_refl.
  pose proof ST as ST0.
  carve_frame 96%nat ST0.
  step.
  assert (HSz : store_ok rsegs m (wa (S - 128)) 8 = true)
    by (eapply wv_store_ok; [intros i Hi; apply (stk_wv m (S - 9136) (S - 96)); [exact ST0 | lia] |
        apply wmono_refl | lia | lia]).
  step. store_done.
  do 12 step.
  step. step.
  assert (EA : Z.land (bv_unsigned (Z_to_bv 64 (S + -128))) 18446744073709551584 = CA).
  { rewrite unsigned_lit by lia. rewrite land_align32 by lia. unfold reac_box_catalogue_match.CA.
    replace (S + -128) with (S - 128) by lia. reflexivity. }
  rewrite EA.
  do 8 step.
  step. step.
  replace (bv_eqb (sx32 (wa 1)) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity). cbv iota.
  step. step.
  (* transport fp to the pre-malloc memory m0 *)
  pose proof (fl_fp [0%nat;1%nat;2%nat] m m0 (bv_unsigned tp) FS (S - 9136) S [] aDf
                [(S - 9136, S)] FP0 MU WM ltac:(intros x Hx; exact Hx)) as FP1.
  destruct FP1 as (DT & TS & C & T & DB & kk & HT1 & HTP1 & HPl1 & H881 & H961 & HCL1 & HFS1 & HAPP1 & HWd1 & HDd1).
  pose proof HCL1 as HCL1'. do 2 apply Forall_cons_iff in HCL1' as [_ HCL1']. apply Forall_cons_iff in HCL1' as [HC2 _].
  destruct HC2 as (_ & h & flags & HH2 & HF2 & HFl2 & HFb2).
  pose proof HWd1 as Hw0. unfold fp_dj in Hw0. apply Forall_cons_iff in Hw0. destruct Hw0 as [Hw0 _].
  cbn [fp_tls app] in Hw0.
  repeat (let Hd := fresh "Hd" in apply Forall_cons_iff in Hw0; destruct Hw0 as [Hd Hw0]; cbn [fst snd] in Hd).
  (* asan state at m0 *)
  assert (AC0 : asan_cells m0).
  { apply (fl_asan_cells [(S - 9136, S)] m m0 AC MU). intros x Hx. unfold RT_LO, RT_HI in Hx.
    cbn [outside]. split; [clear -Hx HHM'; lia | exact I]. }
  pose proof (A.ShadowRwOnT.shadow_rw_on_mem_mono _ m m0 SR_on WM RM) as SR0.
  pose proof (stk_split rsegs m0 (S - 9136) CA (S - 96) ST0 ltac:(lia)) as [STA _].
  pose proof HSM_on as HM. unfold asan_stack_malloc_2_contract_on, asan_stack_malloc_contract_on in HM. cbv zeta in HM.
  eapply evt_cut.
  { eapply HM with (lo := S - 9136) (FS := FS) (h := h) (DT := DT) (TS := TS) (C := C) (T := T)
      (DB := DB) (k := kk) (flags := flags).
    all: rewrite ?(unsigned_lit CA), ?(unsigned_lit 192) by lia.
    - unfold fs_B; cbn; lia.
    - reflexivity.
    - exact AC0.
    - exact (shadow_rw_on_mono _ _ m0 cm_R_sm2 SR0).
    - exact MI.
    - exact HT1.
    - intros Hc; lia.
    - exact HTP1.
    - exact HPl1.
    - exact H881.
    - exact H961.
    - exact HH2.
    - exact HF2.
    - exact HFl2.
    - exact HFb2.
    - exact STA.
    - unfold ASAN_STACK_MALLOC_K; lia.
    - unfold ASAN_STACK_MALLOC_K; clear -HFS1 CAlo2 CAhi2; lia.
    - intros a Ha; apply HAPP1; unfold ASAN_STACK_MALLOC_K in Ha; clear -Ha CAlo2 CAhi2; lia.
    - cbn [disjoint_from]; unfold ASAN_STACK_MALLOC_K; repeat split; try exact I;
        match goal with |- _ + _ <= ?lo \/ ?hi <= _ =>
          match goal with Hd : ly_dj _ _ lo hi |- _ => unfold ly_dj in Hd; lia end end. }
  intros ms' PO.
  destruct PO as (u0 & u1 & u2 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & u3 & u4 & u5 & u6 & m2 & E &
                  WM2 & MI2 & ST2 & FSP2 & (h2 & HH2') & ALT).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 541960)) with (Z_to_bv 64 541960)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  step. step. step. step.
  pose proof acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj).
  unfold ASAN_GT in FSgt. unfold FS_SIZE in FShi.
  rewrite (unsigned_lit CA) in ST2 by lia.
  pose proof FP0 as (DTx & TSx & Cx & Tx & DBx & kkx & _ & _ & _ & _ & _ & HCLx & _).
  pose proof HCLx as HCLy.
  apply Forall_cons_iff in HCLy as [(_ & h0 & flags0 & HH0 & HF0 & HFl0 & HFb0) HCLy1].
  apply Forall_cons_iff in HCLy1 as [(_ & h1 & flags1 & HH1 & HF1 & HFl1 & HFb1) HCLy2].
  apply Forall_cons_iff in HCLy2 as [(_ & h2m & flags2m & HH2m & HF2m & HFl2m & HFb2m) _].
  destruct ALT as [(Hall & Ex0 & MUf) | (ii & Hii0 & Hiipre & Hiinth & FRM)].
  - (* ================= real-stack arm (fr = CA - 192) ================= *)
    subst x0.
    replace (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false by reflexivity. cbv iota.
    rewrite (unsigned_lit CA) in MUf by lia. unfold ASAN_STACK_MALLOC_K in MUf.
    assert (RM2r : rd_mono m0 m2).
    { apply (rd_mono_list _ _ _ MUf). repeat constructor; cbn [fst snd]; intros y Hy.
      - apply (rd_of_bytes _ _ _ HH2'). rewrite length_le8. cbn [Z.of_nat]. unfold fs_hint in *. lia.
      - apply (rd_of_stk _ _ _ ST2). lia. }
    assert (RMr : rd_mono m m2) by (apply (rd_mono_trans _ _ _ RM RM2r)).
    assert (WMr : wmono rsegs m m2) by (apply (wmono_trans _ _ _ _ WM WM2)).
    assert (FR2 : rw_cells rsegs m2 (S - 96) cmSAVES).
    { apply (rw_cells_transport rsegs _ m0 m2 _ _ FR MUf WM2).
      cbn [disjoint_from cells_size csize Nat.add cmSAVES]. unfold fs_hint. repeat split; lia. }
    assert (MUr : munch [(S - 9136, S); (fs_hint FS 2, fs_hint FS 2 + 8)] m m2).
    { apply (munch_trans _ m m0 m2).
      - eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *.
        destruct Hx as (Hw & _). split; [exact Hw | exact I].
      - eapply munch_weaken; [|exact MUf]. intros x Hx. cbn [outside] in *.
        destruct Hx as (Hw & Hh & _). split; [exact Hh | split; [clear -Hw CAlo2 CAhi2; lia | exact I]]. }
    clear MUf.
    step. step.
    match goal with |- context [Z.land ?x 18446744073709551584] =>
      replace (Z.land x 18446744073709551584) with (CA - 192)
        by (rewrite ?(unsigned_lit CA), ?unsigned_lit by lia; rewrite land_align32 by lia;
            Z.div_mod_to_equations; lia) end.
    step. step.
    rewrite (unsigned_lit CA) by lia.
    assert (HSz2 : store_ok rsegs m2 (wa (CA - 4096)) 8 = true)
      by (eapply wv_store_ok;
          [intros i Hi; apply (stk_wv m2 (S - 9136) CA); [exact ST2 | lia] | apply wmono_refl | lia | lia]).
    step. store_done.
    step.
    rewrite (rc_lts_signed (CA - 192) (CA - 4096)) by lia.
    replace (CA - 192 <? CA - 4096) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    step.
    clear ST; destruct STbox as [ST _].
    eapply (cm_header_on Q (CA - 192) (CA - 192) 0 0 _); [exact K|].
    apply (cm_mk_inv_on (CA - 192) (CA - 192) 0 0 _ [(S - 9136, S); (fs_hint FS 2, fs_hint FS 2 + 8)]).
    + left. split; [reflexivity | split; [reflexivity | split; reflexivity]].
    + exact MUr.
    + exact WMr.
    + exact RMr.
    + exact MI2.
    + intros x Hx. unfold reac_box_catalogue_match.aWc in Hx. cbn [outside] in Hx. destruct Hx as (Hw & Hxs).
      unfold reac_box_catalogue_match.aXs in Hxs. apply cm_out_app in Hxs. destruct Hxs as (Hfpw & _).
      cbn [outside]. split; [exact Hw | split; [|exact I]].
      exact (out_in _ _ _ _ Hfpw (fpw3_in_hint FS 2 ltac:(cbn; tauto))).
    + intros y Hy Hap. pose proof (rt_app_shadow y Hap) as Hsh.
      cbn [outside]. split; [|split; [|exact I]].
      * unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh.
        clear -Hsh Hy HHM'. lia.
      * apply (sh_out_app (shadow_addr y) (fs_hint FS 2) (fs_hint FS 2 + 8) Hsh).
        intros z Hz. apply FSapp. unfold fs_hint in *. unfold FS_SIZE. lia.
    + intros c Hc. cbn in Hc. destruct Hc as [Hc|[Hc|[Hc|[]]]]; subst c.
      * split.
        -- exists h0. apply (fl_bytes _ m _ (fs_hint FS 0) (le8 h0) HH0 MUr).
           intros x Hx. rewrite length_le8 in Hx. cbn [Z.of_nat] in Hx.
           cbn [outside]. unfold fs_hint in *. split; [lia | split; [lia | exact I]].
        -- exists flags0. split; [|split; [exact HFl0 | exact HFb0]].
           apply (fl_bytes _ m _ (fs_flag FS 0 0) flags0 HF0 MUr).
           intros x Hx. rewrite HFl0 in Hx. cbn [outside].
           unfold fs_flag, fs_M in *; cbn [Z.of_nat] in *;
             change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 0)) with 32768 in *;
             change (2 ^ (14 - 0)) with 16384 in *; unfold fs_hint in *.
           split; [lia | split; [lia | exact I]].
      * split.
        -- exists h1. apply (fl_bytes _ m _ (fs_hint FS 1) (le8 h1) HH1 MUr).
           intros x Hx. rewrite length_le8 in Hx. cbn [Z.of_nat] in Hx.
           cbn [outside]. unfold fs_hint in *. split; [lia | split; [lia | exact I]].
        -- exists flags1. split; [|split; [exact HFl1 | exact HFb1]].
           apply (fl_bytes _ m _ (fs_flag FS 1 0) flags1 HF1 MUr).
           intros x Hx. rewrite HFl1 in Hx. cbn [outside].
           unfold fs_flag, fs_M in *; cbn [Z.of_nat] in *;
             change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 1)) with 16384 in *;
             change (2 ^ (14 - 1)) with 8192 in *; unfold fs_hint in *.
           split; [lia | split; [lia | exact I]].
      * split.
        -- destruct (rd8_le8 _ (fs_hint FS 2)
             ltac:(unfold fs_hint; lia) ltac:(unfold fs_hint; lia)
             ltac:(intros i Hi; apply RMr; apply (rd_of_bytes _ _ _ HH2m);
                   rewrite length_le8; cbn [Z.of_nat]; unfold fs_hint; lia)) as (hw & Hhw).
           exists hw. exact Hhw.
        -- exists flags2m. split; [|split; [exact HFl2m | exact HFb2m]].
           apply (fl_bytes _ m _ (fs_flag FS 2 0) flags2m HF2m MUr).
           intros x Hx. rewrite HFl2m in Hx. cbn [outside].
           unfold fs_flag, fs_M in *; cbn [Z.of_nat] in *;
             change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 2)) with 8192 in *;
             change (2 ^ (14 - 2)) with 4096 in *; unfold fs_hint in *.
           split; [lia | split; [lia | exact I]].
    + exact FR2.
    + intros Hcontra; discriminate Hcontra.
  - (* ================= side-stack arm (fr = fs_frame FS 2 jj) ================= *)
    unfold asan_stack_malloc_frame in FRM. cbv zeta in FRM.
    rewrite (unsigned_lit CA) in FRM by lia.
    rewrite (unsigned_lit 192) in FRM by lia.
    replace (fs_B 2) with 256 in FRM by reflexivity.
    replace (fs_shadow_n 2 192) with 32 in FRM by reflexivity.
    destruct FRM as (Ex0 & Hm64 & _ & HFL & H24 & Hflagword & HSH & HADD & STF & APF & FSlo & FShi' & GT & FRA' & DIS & MU2).
    remember ((bv_unsigned h + ii) mod fs_M 2) as jj eqn:Ejj.
    assert (Hjj : 0 <= jj < fs_M 2) by (subst jj; apply Z.mod_pos_bound; reflexivity).
    remember (fs_frame FS 2 jj) as fr eqn:Efr.
    subst x0.
    unfold FS_SIZE in FShi'. change (fs_M 2) with 4096 in Hjj.
    unfold ASAN_STACK_MALLOC_K in MU2.
    replace (fr + 256 - 8) with (fr + 248) in * by lia.
    assert (Hm8 : fr mod 8 = 0) by (clear -Hm64; Z.div_mod_to_equations; lia).
    unfold ASAN_GT in GT.
    assert (Hfrlo : FS + 36864 <= fr) by
      (rewrite Efr; unfold fs_frame, fs_B; cbn [Z.of_nat]; change (2 ^ 20) with 1048576; change (2 ^ 2) with 4; lia).
    rewrite (rc_neq0_64 fr) by lia. cbn [negb]. cbv iota.
    assert (RM2r : rd_mono m0 m2).
    { apply (rd_mono_list _ _ _ MU2). repeat constructor; cbn [fst snd]; intros y Hy.
      - apply (rd_of_bytes _ _ _ HH2'). rewrite length_le8. cbn [Z.of_nat]. unfold fs_hint in *. lia.
      - apply (rd_of_bytes _ _ _ HFL). cbn [length]. lia.
      - apply (rd_of_bytes _ _ _ H24). rewrite length_le8. cbn [Z.of_nat]. lia.
      - apply (rd_of_bytes _ _ _ Hflagword). rewrite length_le8. cbn [Z.of_nat]. lia.
      - apply (rd_of_bytes _ _ _ HSH). rewrite repeat_length, Z2Nat.id by lia. lia.
      - apply (rd_of_stk _ _ _ ST2). lia. }
    assert (RMw : rd_mono m m2) by (apply (rd_mono_trans _ _ _ RM RM2r)).
    assert (WMw : wmono rsegs m m2) by (apply (wmono_trans _ _ _ _ WM WM2)).
    assert (FR2 : rw_cells rsegs m2 (S - 96) cmSAVES).
    { apply (rw_cells_transport rsegs _ m0 m2 _ _ FR MU2 WM2).
      cbn [disjoint_from cells_size csize Nat.add cmSAVES].
      unfold fs_hint, fs_flag, fs_M. cbn [Z.of_nat]. change (2 ^ 15) with 32768. change (2 ^ (15 - 2)) with 8192.
      repeat split; right; first [ lia | (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia) ]. }
    assert (MUw : munch [(S - 9136, S); (fs_hint FS 2, fs_hint FS 2 + 8); (fs_flag FS 2 jj, fs_flag FS 2 jj + 1);
                         (fr + 24, fr + 32); (fr + 248, fr + 256); (shadow_addr fr, shadow_addr fr + 32); (CA - 208, CA)] m m2).
    { apply (munch_trans _ m m0 m2).
      - eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *.
        split; [exact (proj1 Hx) | exact I].
      - eapply munch_weaken; [|exact MU2]. intros x Hx. cbn [outside] in Hx. exact (proj2 Hx). }
    clear ST; destruct STbox as [ST _].
    eapply (cm_header_on Q fr CA jj 1 m2); [exact K|].
    apply (cm_mk_inv_on fr CA jj 1 m2 [(S - 9136, S); (fs_hint FS 2, fs_hint FS 2 + 8); (fs_flag FS 2 jj, fs_flag FS 2 jj + 1);
                     (fr + 24, fr + 32); (fr + 248, fr + 256); (shadow_addr fr, shadow_addr fr + 32); (CA - 208, CA)]).
    + right. split; [exact Hjj | split; [exact Efr | split; reflexivity]].
    + exact MUw.
    + exact WMw.
    + exact RMw.
    + exact MI2.
    + intros x Hx. unfold reac_box_catalogue_match.aWc in Hx. cbn [outside] in Hx. destruct Hx as (Hwn & Hxs).
      unfold reac_box_catalogue_match.aXs in Hxs. apply cm_out_app in Hxs. destruct Hxs as (Hfpw & Hws).
      cbn [outside] in Hws. destruct Hws as (Hws & _).
      cbn [outside]. split; [exact Hwn|]. split.
      { exact (out_in _ _ _ _ Hfpw (fpw3_in_hint FS 2 ltac:(cbn; tauto))). }
      split.
      { intros Hc. apply (out_in _ _ _ _ Hfpw (fpw3_in_flag FS 2 ltac:(cbn; tauto))).
        unfold fs_flag, fs_M in *. destruct Hc. split; lia. }
      split.
      { intros Hc. apply (out_in _ _ _ _ Hfpw (fpw3_in_frame FS 2 ltac:(cbn; tauto))).
        rewrite Efr in *. unfold fs_frame, fs_B, fs_M in *. cbn [Z.of_nat] in *.
        change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in Hjj.
        destruct Hc. split; lia. }
      split.
      { intros Hc. apply (out_in _ _ _ _ Hfpw (fpw3_in_frame FS 2 ltac:(cbn; tauto))).
        rewrite Efr in *. unfold fs_frame, fs_B, fs_M in *. cbn [Z.of_nat] in *.
        change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in Hjj.
        destruct Hc. split; lia. }
      split.
      { pose proof (out_in _ _ _ _ Hfpw (fpw3_in_shadow FS 2 ltac:(cbn; tauto))) as HFin.
        assert (GE : shadow_addr (fs_frame FS 2 0) <= shadow_addr fr).
        { apply acl_sh_ge. rewrite Efr. unfold fs_frame, fs_B. cbn [Z.of_nat]. change (2 ^ 20) with 1048576. lia. }
        assert (LE : shadow_addr fr + 32 <= shadow_addr (fs_frame FS 2 (fs_M 2))).
        { rewrite Efr. unfold shadow_addr, fs_frame, fs_B, fs_M in *. cbn [Z.of_nat] in *.
          change (2 ^ 20) with 1048576 in *. change (2 ^ (14 - 2)) with 4096 in Hjj.
          Z.div_mod_to_equations; lia. }
        intros [A B]. clear -HFin GE LE A B. lia. }
      split; [|exact I].
      intros Hc. apply Hwn. clear -Hc CAlo2 CAhi2. lia.
    + intros y Hy Hap. pose proof (rt_app_shadow y Hap) as Hsh.
      cbn [outside]. split.
      { unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh.
        clear -Hsh Hy HHM'. lia. }
      split.
      { apply (sh_out_app (shadow_addr y) (fs_hint FS 2) (fs_hint FS 2 + 8) Hsh).
        intros z Hz. apply FSapp. unfold fs_hint in *. unfold FS_SIZE. lia. }
      split.
      { apply (sh_out_app (shadow_addr y) (fs_flag FS 2 jj) (fs_flag FS 2 jj + 1) Hsh).
        intros z Hz. apply FSapp. unfold fs_flag, fs_M in *. cbn [Z.of_nat] in *.
        change (2 ^ 15) with 32768 in *. change (2 ^ (15 - 2)) with 8192 in *. unfold FS_SIZE. lia. }
      split.
      { apply (sh_out_app (shadow_addr y) (fr + 24) (fr + 32) Hsh).
        intros z Hz. apply APF. lia. }
      split.
      { apply (sh_out_app (shadow_addr y) (fr + 248) (fr + 256) Hsh).
        intros z Hz. apply APF. lia. }
      split; [|split; [|exact I]].
      { intros [A B]. pose proof (acl_sh_ge y (fr + 8 * 32) ltac:(lia)) as G.
        rewrite (cm_sh_add8 fr 32 Hm8) in G. lia. }
      { apply (sh_out_app (shadow_addr y) (CA - 208) CA Hsh).
        intros z Hz. right. unfold HIGHMEM_BEG, APPMEM_END. clear -Hz Hy HHM' HAE' CAlo2 CAhi2. lia. }
    + intros c Hc. cbn in Hc. destruct Hc as [Hc|[Hc|[Hc|[]]]]; subst c.
      * split.
        -- exists h0. apply (fl_bytes _ m _ (fs_hint FS 0) (le8 h0) HH0 MUw).
           intros x Hx. rewrite length_le8 in Hx. cbn [Z.of_nat] in Hx.
           cm_hdr_out FSapp Hm8.
        -- exists flags0. split; [|split; [exact HFl0 | exact HFb0]].
           apply (fl_bytes _ m _ (fs_flag FS 0 0) flags0 HF0 MUw).
           intros x Hx. rewrite HFl0 in Hx.
           cm_hdr_out FSapp Hm8.
      * split.
        -- exists h1. apply (fl_bytes _ m _ (fs_hint FS 1) (le8 h1) HH1 MUw).
           intros x Hx. rewrite length_le8 in Hx. cbn [Z.of_nat] in Hx.
           cm_hdr_out FSapp Hm8.
        -- exists flags1. split; [|split; [exact HFl1 | exact HFb1]].
           apply (fl_bytes _ m _ (fs_flag FS 1 0) flags1 HF1 MUw).
           intros x Hx. rewrite HFl1 in Hx.
           cm_hdr_out FSapp Hm8.
      * split.
        -- exists h2. exact HH2'.
        -- apply (cm_flag_upd m0 m2
             [(fs_hint FS 2, fs_hint FS 2 + 8); (fs_flag FS 2 jj, fs_flag FS 2 jj + 1);
              (fr + 24, fr + 32); (fr + 248, fr + 256); (shadow_addr fr, shadow_addr fr + 32); (CA - 208, CA)]
             flags jj Hjj HFl2 HFb2 HF2 MU2); [| exact HFL].
           intros x Hx Hxne.
           assert (Hxap : app_mem x) by (apply FSapp; unfold fs_flag, fs_M in *; cbn [Z.of_nat] in *;
             change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 2)) with 8192 in *; unfold FS_SIZE; lia).
           cbn [outside]. split.
           { unfold fs_hint, fs_flag, fs_M in *; cbn [Z.of_nat] in *;
               change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 2)) with 8192 in *; lia. }
           split.
           { intros [A B]. apply Hxne. unfold fs_flag in *. lia. }
           split.
           { unfold fs_flag, fs_M in *; cbn [Z.of_nat] in *;
               change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 2)) with 8192 in *; lia. }
           split.
           { unfold fs_flag, fs_M in *; cbn [Z.of_nat] in *;
               change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 2)) with 8192 in *; lia. }
           split; [|split; [|exact I]].
           { intros [A B]. pose proof (acl_sh_out x fr (fr + 8 * 32) Hxap ltac:(lia) ltac:(unfold APPMEM_END; lia)) as Hso.
             rewrite (cm_sh_add8 fr 32 Hm8) in Hso. apply Hso. split; [exact A | exact B]. }
           { unfold fs_flag, fs_M in *; cbn [Z.of_nat] in *;
               change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 2)) with 8192 in *; lia. }
    + exact FR2.
    + intros _. exact Hflagword.
Qed.


(* The register state at the reac_ctrl_parse call (pc 0x84684): a0 = f, a1 = len, a2 = fr + 32 (the parse buffer),
   s0 = S, s1 = CA, s2 = frame, s3 = f, s4 = len, s5 = ASAN_K, s6 = shadow_addr fr, s7 = fr; the input is at least
   50 bytes and its four header bytes 12, 13, 16, 17 are 0x88 0x19 0xcd 0xea (the first five tests of RcMatch's
   cm_gate_on passed), the invariant holds at mc and the parse buffer is addressable. *)
Definition cmPB_on (Q : machine_state -> Prop) : Prop :=
  forall (fr sp2 jj nn : Z) (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    50 <= len -> cp_v fb 12 = 0x88 -> cp_v fb 13 = 0x19 -> cp_v fb 16 = 0xcd -> cp_v fb 17 = 0xea ->
    cmInv_on fr sp2 jj nn mc -> addressable mc (fr + 32) 36 ->
    evt rsegs Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               (Z_to_bv 64 f) (Z_to_bv 64 len) (Z_to_bv 64 (fr + 32)) ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
               (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x84684) fc None mc (seg_rom rsegs)).


(* The register state at the catalogue-miss tail (pc 0x84720): the short-input branch of `bltu len,50` and the four
   header-byte mismatch branches all reach it with the invariant unchanged at mc, and there the result the contract
   names is 0 (want CM_T len fb = 0). *)
Definition cmMiss_on (Q : machine_state -> Prop) : Prop :=
  forall (fr sp2 jj nn : Z) (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    want CM_T len fb = 0 -> cmInv_on fr sp2 jj nn mc ->
    evt rsegs Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
               (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x84720) fc None mc (seg_rom rsegs)).


(* After a 1-byte store at E (pc already past it): keep the stored bytes as a bytes_at fact HB on the written memory
   (store_done's remember renames that memory in HB too), then store_done. *)
Ltac cm_keep HB :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?mm ?a ?bs) ?ro) =>
      let E := addr_expr a in
      change (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs);
      assert (HB : bytes_at segs (write_to_mem mm (wa E) bs) E bs)
        by (apply bytes_at_write_same; simpl_sizes; lia);
      store_done
  end.


(* The run from the gate at 0x845dc to the reac_ctrl_parse call: `bltu len,50` (short input -> the miss tail), then
   the four shadow-checked loads of f+12, f+13, f+16, f+17 (each instrumented check passes from `addressable mc f 50`,
   so the call of __asan_report_* is not reached; each header byte is compared: a mismatch -> the miss tail), then
   the un-poisoning of the parse buffer's shadow (bytes 4..8 -> 0,0,0,0,4), ending at the call entry with
   `addressable (fr + 32) 36` (cmPB_on). *)
Lemma cm_gate_on : forall (Q : machine_state -> Prop) (fr sp2 jj nn : Z) (mc : word -> option byte)
    (rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
  cmPB_on Q -> cmMiss_on Q -> cmInv_on fr sp2 jj nn mc ->
  evt rsegs Q
    (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
             ra0 ra1 (Z_to_bv 64 50) ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) s8 s9 s10 s11 rt3 rt4 rt5 rt6)
         F (Z_to_bv 64 0x845dc) fc None mc (seg_rom rsegs)).
Proof.
  intros Q fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 KP KM INV.
  pose proof INV as INVk.
  destruct INV as (FK & MUg & WMg & RMg & MIg & _).
  step.
  rewrite cm_ltu_lit by (clear -Rlen; lia).
  destruct (Z.ltb_spec len 50) as [L|L]; cbv iota.
  { eapply KM; [exact (cm_miss_short L) | exact INVk]. }
  destruct (HF L) as (Hf0 & Hf50 & _ & _).
  pose proof (cm_FB mc L MUg) as BF.
  pose proof (cm_AF mc L MUg) as AF.
  clear MUg.
  pose proof (rd_byte rsegs mc f fb 12 BF ltac:(rewrite Hfb; clear; lia)) as R12.
  pose proof (rd_byte rsegs mc f fb 13 BF ltac:(rewrite Hfb; clear; lia)) as R13.
  pose proof (rd_byte rsegs mc f fb 16 BF ltac:(rewrite Hfb; clear; lia)) as R16.
  pose proof (rd_byte rsegs mc f fb 17 BF ltac:(rewrite Hfb; clear; lia)) as R17.
  change (Z.of_nat 12) with 12 in R12. change (Z.of_nat 13) with 13 in R13.
  change (Z.of_nat 16) with 16 in R16. change (Z.of_nat 17) with 17 in R17.
  clear BF.
  pose proof (byte_range (nth 12 fb (Z_to_bv 8 0))) as BR12. pose proof (byte_range (nth 13 fb (Z_to_bv 8 0))) as BR13.
  pose proof (byte_range (nth 16 fb (Z_to_bv 8 0))) as BR16. pose proof (byte_range (nth 17 fb (Z_to_bv 8 0))) as BR17.
  assert (RX12 : 0 <= f + 12 < 2^64) by (clear -Hf0 Hf50; lia).
  assert (RX13 : 0 <= f + 13 < 2^64) by (clear -Hf0 Hf50; lia).
  assert (RX16 : 0 <= f + 16 < 2^64) by (clear -Hf0 Hf50; lia).
  assert (RX17 : 0 <= f + 17 < 2^64) by (clear -Hf0 Hf50; lia).
  pose proof (acl_shadow mc f 50 12 1 (f + 12) AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
    ltac:(pose proof (Z.mod_pos_bound (f + 12) 8 eq_refl); clear -H; lia) eq_refl) as SH12.
  pose proof (acl_shadow mc f 50 13 1 (f + 13) AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
    ltac:(pose proof (Z.mod_pos_bound (f + 13) 8 eq_refl); clear -H; lia) eq_refl) as SH13.
  pose proof (acl_shadow mc f 50 16 1 (f + 16) AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
    ltac:(pose proof (Z.mod_pos_bound (f + 16) 8 eq_refl); clear -H; lia) eq_refl) as SH16.
  pose proof (acl_shadow mc f 50 17 1 (f + 17) AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
    ltac:(pose proof (Z.mod_pos_bound (f + 17) 8 eq_refl); clear -H; lia) eq_refl) as SH17.
  clear AF.
  (* byte 12: 0x88 *)
  step.
  chk_core (f + 12) RX12 (Z_to_bv 5 12) SH12 pre_sr no_extra.
  step. step. step.
  rewrite cm_eqb_zxb by (clear; lia).
  destruct (Z.eqb_spec (bv_unsigned (nth 12 fb (Z_to_bv 8 0))) 136) as [E12|E12]; cbn [negb]; cbv iota.
  2: { eapply KM; [exact (cm_miss_hdr 12%nat 136 L ltac:(clear; lia) E12) | exact INVk]. }
  (* byte 13: 0x19 *)
  step.
  chk_core (f + 13) RX13 (Z_to_bv 5 12) SH13 pre_sr no_extra.
  step. step. step.
  rewrite cm_eqb_zxb by (clear; lia).
  destruct (Z.eqb_spec (bv_unsigned (nth 13 fb (Z_to_bv 8 0))) 25) as [E13|E13]; cbn [negb]; cbv iota.
  2: { eapply KM; [exact (cm_miss_hdr 13%nat 25 L ltac:(clear; lia) E13) | exact INVk]. }
  (* byte 16: 0xcd *)
  step.
  chk_core (f + 16) RX16 (Z_to_bv 5 12) SH16 pre_sr no_extra.
  step. step. step.
  rewrite cm_eqb_zxb by (clear; lia).
  destruct (Z.eqb_spec (bv_unsigned (nth 16 fb (Z_to_bv 8 0))) 205) as [E16|E16]; cbn [negb]; cbv iota.
  2: { eapply KM; [exact (cm_miss_hdr 16%nat 205 L ltac:(clear; lia) E16) | exact INVk]. }
  (* byte 17: 0xea *)
  step.
  chk_core (f + 17) RX17 (Z_to_bv 5 12) SH17 pre_sr no_extra.
  step. step. step.
  rewrite cm_eqb_zxb by (clear; lia).
  destruct (Z.eqb_spec (bv_unsigned (nth 17 fb (Z_to_bv 8 0))) 234) as [E17|E17]; cbn [negb]; cbv iota.
  2: { eapply KM; [exact (cm_miss_hdr 17%nat 234 L ltac:(clear; lia) E17) | exact INVk]. }
  clear R12 R13 R16 R17 BR12 BR13 BR16 BR17 RX12 RX13 RX16 RX17.
  (* the un-poisoning of the parse buffer's shadow bytes 4..8 (all inside cmHF fr) *)
  step.
  pose proof (fk_facts_on fr sp2 jj nn FK) as (FR8 & FRpos & FR192 & _ & FAP & FSW & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (_ & FRhi).
  assert (SHlo : 0 <= shadow_addr fr).
  { unfold shadow_addr. assert (D : 0 <= fr / 8) by (apply Z.div_pos; clear -FRpos; lia). unfold ASAN_K. clear -D. lia. }
  assert (SHhi : shadow_addr fr + 24 <= 2 ^ 64).
  { unfold shadow_addr, ASAN_K. clear -FRpos FRhi RS. Z.div_mod_to_equations. lia. }
  assert (FSW' : forall i, 0 <= i < 24 -> wview rsegs m (wa (shadow_addr fr + i)) <> None) by exact FSW.
  clear FSW.
  assert (MUh : munch (cmHF fr) mc mc) by apply munch_refl.
  assert (WMh : wmono rsegs mc mc) by apply wmono_refl.
  assert (RMh : rd_mono mc mc) by apply rd_mono_refl.
  unfold reac_box_catalogue_match.cmHF in MUh.
  cm_wst (shadow_addr fr + 4) 1%nat. step. cm_keep B4.
  cm_wst (shadow_addr fr + 5) 1%nat. step. cm_keep B5.
  cm_wst (shadow_addr fr + 6) 1%nat. step. cm_keep B6.
  cm_wst (shadow_addr fr + 7) 1%nat. step. cm_keep B7.
  step.
  cm_wst (shadow_addr fr + 8) 1%nat. step. cm_keep B8.
  step. step.
  eapply KP; [exact L | exact E12 | exact E13 | exact E16 | exact E17 | |].
  - eapply cm_inv_step_on; [exact INVk | exact MUh | exact WMh | exact RMh | exact MIg].
  - eapply cm_parse_addr; [exact FR8 | clear -FRpos; lia | clear -FRhi HAE; lia | | exact B4 | exact B5 | exact B6
                          | exact B7 | exact B8].
    intros i Hi. replace (fr + 32 + i) with (fr + (32 + i)) by (clear; lia). apply FAP. clear -Hi; lia.
Qed.


(* ============================ (c) the calls ============================ *)

(* The window and the frame read back in any memory the run reached (wmono, rd_mono from m; the side stack's stk). *)
Lemma cm_stk_win_on : forall fr sp2 jj nn mc, cmInv_on fr sp2 jj nn mc -> stk rsegs mc (S - 9136) S.
Proof.
  intros fr sp2 jj nn mc (_ & _ & WM & RM & _).
  destruct ST as (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (H a Ha) as (Hv & Hb). split; [apply WM, Hv | apply RM, Hb].
Qed.


Lemma cm_stk_fr_on : forall fr sp2 jj nn mc, cmInv_on fr sp2 jj nn mc -> stk rsegs mc fr (fr + 192).
Proof.
  intros fr sp2 jj nn mc INV. pose proof (cm_stk_win_on fr sp2 jj nn mc INV) as SW.
  destruct INV as (FK & _ & _ & _ & _ & _ & _ & FP & _).
  pose proof CA_facts as (CA32 & CAlo & CAhi). pose proof cm_CA_lo as (CAlo2 & CAhi2).
  destruct FK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)].
  - subst fr. destruct (stk_split rsegs mc (S - 9136) (CA - 192) S SW ltac:(lia)) as (_ & SW2).
    destruct (stk_split rsegs mc (CA - 192) (CA - 192 + 192) S SW2 ltac:(lia)) as (SW3 & _). exact SW3.
  - destruct FP as (DT & TS & C & T & DB & k & _ & _ & (_ & _ & _ & _ & P5) & _).
    assert (LO : FS <= fr) by (rewrite Ef; unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (HI : fr + 192 <= FS + FS_SIZE).
    { rewrite Ef. unfold fs_frame, fs_B, fs_M, FS_SIZE in *. cbn [Z.of_nat] in *.
      change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. change (2 ^ (14 - 2)) with 4096 in Hj. lia. }
    destruct (stk_split rsegs mc FS fr (FS + FS_SIZE) P5 ltac:(lia)) as (_ & P6).
    destruct (stk_split rsegs mc fr (fr + 192) (FS + FS_SIZE) P6 ltac:(lia)) as (P7 & _). exact P7.
Qed.


(* A callee of class c at sp2 with window [sp2 - K, sp2) and a buffer [fr + d, fr + d + n) of the frame: its fp from
   the invariant's fp (fp_single); the buffer of a side-stack frame is apart from the thread cells by aTL. *)
Lemma cm_fp_call_on : forall c fr sp2 jj nn mc K d n D',
  cmInv_on fr sp2 jj nn mc -> In c [0%nat; 1%nat; 2%nat] -> 0 <= K <= 8800 -> 0 <= d -> 0 <= n -> d + n <= 192 ->
  fp_dj D' (fp_w [c] FS) ->
  fp [c] mc (bv_unsigned tp) FS (sp2 - K) sp2 ((sp2 - K, sp2) :: [(fr + d, fr + d + n)]) D'.
Proof.
  intros c fr sp2 jj nn mc K d n D' INV Hc HKr Hd Hn Hdn HD.
  destruct INV as (FK & _ & _ & _ & _ & _ & _ & FP & TL & _).
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc). pose proof cm_fr2 as (F20 & F2M).
  pose proof (fp_single c _ mc (bv_unsigned tp) FS (S - 9136) S aWf aDf Hc FP) as FPc.
  destruct FPc as (DT & TS & C & T & DB & k & HTc & HTP & HP & H88 & H96 & HCL & HFS & HA & HWd & HDd).
  exists DT, TS, C, T, DB, k.
  split; [exact HTc|]. split; [exact HTP|]. split; [exact HP|]. split; [exact H88|]. split; [exact H96|].
  split; [exact HCL|]. split; [lia|]. split; [intros a Ha; apply HA; lia|].
  split; [|exact HD].
  unfold reac_box_catalogue_match.aWf in HWd. apply fl_dj_cons in HWd as [HW1 _].
  apply fl_dj_cons. split; [apply (fl_dj_sub _ _ _ _ _ HW1); lia|].
  apply fl_dj_cons. split; [|unfold fp_dj; constructor].
  destruct Gc as [(En & Ef & Fhi) | (En & Ef & Hj & Fhi & Fhi2)].
  - apply (fl_dj_sub _ _ _ _ _ HW1); lia.
  - pose proof (TL DT TS C T DB k HTc) as TLd. unfold reac_box_catalogue_match.aXs in TLd.
    assert (INf : In (fs_frame FS 2 0, fs_frame FS 2 (fs_M 2))
                     (fp_w [0%nat; 1%nat; 2%nat] FS ++ [(shadow_addr (S - 9136), shadow_addr S)]))
      by (apply in_or_app; left; apply fpw3_in_frame; cbn; tauto).
    unfold fp_dj in TLd |- *. constructor; [|constructor]. apply Forall_app. split.
    + apply Forall_forall. intros [a b] Hin. cbn [fst snd].
      rewrite Forall_forall in TLd. pose proof (TLd (a, b) Hin) as Hab. rewrite Forall_forall in Hab.
      pose proof (Hab _ INf) as Hly. cbn [fst snd] in Hly. rewrite F20, F2M in Hly. unfold ly_dj in *. lia.
    + constructor; [|constructor]. cbn [fst snd]. unfold ly_dj, fs_frame. cbn [Z.of_nat]. lia.
Qed.


(* A buffer of the frame is apart from the class-0 and class-1 side-stack bytes. *)
Lemma cm_dj_buf_on : forall fr sp2 jj nn d n c, cmFK fr sp2 jj nn -> (c <= 1)%nat -> 0 <= d -> 0 < n -> d + n <= 192 ->
  fp_dj [(fr + d, fr + d + n)] (fp_w [c] FS).
Proof.
  intros fr sp2 jj nn d n c FK Hc Hd Hn Hdn.
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc).
  pose proof (fk_facts_on fr sp2 jj nn FK) as (_ & _ & _ & _ & FAP & _ & _).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). pose proof HAE as HAE'. unfold FS_SIZE in FShi.
  assert (Hfr : fs_frame FS c (fs_M c) <= fr).
  { clear -Gc Hc FShi Gsp. unfold fs_frame, fs_B, fs_M.
    destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat]; destruct Gc as [(_ & E & _)|(_ & E & Hj & _)]; lia. }
  unfold fp_dj. constructor; [|constructor]. cbn [fp_w flat_map fp_w1 app].
  constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; cbn [fst snd]; unfold ly_dj.
  - right. clear -Gfs Hd Hc. unfold fs_hint. destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat]; lia.
  - right. clear -Gfs Hd Hc. unfold fs_flag, fs_M. destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat]; lia.
  - right. clear -Hfr Hd. lia.
  - apply cm_dj_sh.
    + intros z Hz. replace z with (fr + (z - fr)) by (clear; lia). apply FAP. clear -Hz Hd Hdn. lia.
    + clear -Hn. lia.
    + clear -FSpos Hc. unfold fs_frame, fs_B. destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat]; lia.
    + clear -Hc. unfold fs_frame, fs_B, fs_M. destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat]; lia.
    + clear -Hc FShi HAE'. unfold fs_frame, fs_B, fs_M, APPMEM_END in *.
      destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat]; lia.
Qed.


(* The shadow byte of a window byte outside the callee window [sp2 - 8800, sp2) is apart from the callee writes. *)
Lemma cm_Wc_sh_out_on : forall fr sp2 jj nn K d n c x, cmFK fr sp2 jj nn -> In c [0%nat; 1%nat; 2%nat] ->
  0 <= K <= 8800 -> K mod 8 = 0 -> 0 <= d -> d + n <= 192 -> S - 9136 <= x < S ->
  ~ (sp2 - 8800 <= x < sp2) -> outside (cmWc fr sp2 K d n c) (shadow_addr x).
Proof.
  intros fr sp2 jj nn K d n c x FK Hc HKr HK8 Hd Hdn Hx Hx2.
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc).
  pose proof (fk_facts_on fr sp2 jj nn FK) as (_ & FRpos & _ & _ & FAP & _ & _).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). pose proof HHM as HHM'. pose proof HAE as HAE'.
  unfold FS_SIZE in FShi. unfold HIGHMEM_BEG in HHM'. unfold APPMEM_END in HAE'.
  assert (Hap : app_mem x) by (clear -Hx HHM' HAE'; unfold app_mem, HIGHMEM_BEG, APPMEM_END; right; lia).
  pose proof (rt_app_shadow x Hap) as Hsh.
  assert (Ho3 : outside (fp_w [0%nat; 1%nat; 2%nat] FS) x)
    by (apply acl_out_fpw_hi; [clear -Hx FShi; unfold FS_SIZE; lia | exact Hap]).
  unfold reac_box_catalogue_match.cmWc. cbn [outside]. split; [|split].
  - apply (sh_out_app _ (fr + d) (fr + d + n) Hsh).
    intros z Hz. replace z with (fr + (z - fr)) by (clear -Hz; lia). apply FAP. clear -Hz Hd Hdn. lia.
  - apply (sh_out_app _ (sp2 - K) sp2 Hsh).
    intros z Hz. clear -Hz Gsp HKr HHM' HAE'. unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia.
  - apply fl_out_app; [exact (cm_out_fpw_c c (shadow_addr x) Hc (acl_out_fpw_sh x Hap Ho3))|].
    cbn [outside]. split; [|exact I].
    apply acl_win_sh; [clear -G16 HK8; Z.div_mod_to_equations; lia | clear -Hx2 HKr; lia].
Qed.


(* The invariant survives a call whose writes Wm are inside aWc and apart from the saves and the flag word, given the
   class hint/flag readback, the callee window addressable and every readable byte still readable. *)
Lemma cm_inv_mu_on : forall fr sp2 jj nn mc mc' Wm,
  cmInv_on fr sp2 jj nn mc ->
  munch Wm mc mc' -> wmono rsegs mc mc' -> rd_mono mc mc' -> mem_inv rsegs mc' ->
  sub_fp Wm aWc ->
  (forall c, In c [0%nat; 1%nat; 2%nat] ->
     (exists h', bytes_at rsegs mc' (fs_hint FS c) (le8 h')) /\
     (exists flags', bytes_at rsegs mc' (fs_flag FS c 0) flags' /\ Z.of_nat (length flags') = fs_M c /\
        Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags')) ->
  addressable mc' (sp2 - 8800) 8800 ->
  (forall x, S - 9136 <= x < S -> ~ (fr <= x < fr + 192) -> ~ (sp2 - 8800 <= x < sp2) ->
     outside Wm (shadow_addr x)) ->
  (forall x, S - 96 <= x < S -> outside Wm x) ->
  (nn = 1 -> forall x, fr + 248 <= x < fr + 256 -> outside Wm x) ->
  cmInv_on fr sp2 jj nn mc'.
Proof.
  intros fr sp2 jj nn mc mc' Wm INV MU WM RM MI' SUB Hcls AD' OAW OSV OFL.
  destruct INV as (FK & MUmc & WMmc & RMmc & MImc & ACmc & SRmc & FPg & TLg & ADg & AWXg & SVg & FLg).
  pose proof FPg as FPpack.
  destruct FPg as (DT0 & TS0 & C0 & T0 & DB0 & kk0 & HT0 & HTPle & HPl & H88 & H96 & HCL & HFSlo & HApphi & HWd & HDd).
  destruct HPl as (HP1 & HP2 & HP3 & HP4 & HPstk).
  split; [exact FK|].
  split; [exact (munch_trans aWc m mc mc' MUmc (munch_weaken Wm aWc mc mc' SUB MU))|].
  split; [exact (wmono_trans rsegs m mc mc' WMmc WM)|].
  split; [exact (rd_mono_trans m mc mc' RMmc RM)|].
  split; [exact MI'|].
  split; [exact (fl_asan_cells Wm mc mc' ACmc MU (fun x Hx => SUB x (acl_rt_out_Wc x Hx)))|].
  split; [exact (A.ShadowRwOnT.shadow_rw_on_mem_mono _ mc mc' SRmc WM RM)|].
  split.
  { apply (fl_fp_free [0%nat; 1%nat; 2%nat] mc mc' (bv_unsigned tp) FS (S - 9136) S aWf aDf Wm FPpack TLg MU WM).
    - unfold reac_box_catalogue_match.aWf, reac_box_catalogue_match.aWc, reac_box_catalogue_match.aXs in *. cbn [app]. exact SUB.
    - intros x Hx. apply SUB. exact (acl_hdr_out_Wc x Hx).
    - intros x Hx. right. apply RM. exact (rd_of_stk mc FS (FS + FS_SIZE) HPstk x Hx).
    - exact Hcls. }
  split.
  { intros DT TS C T DB kk HTcells'.
    assert (Hc : Forall (fun d => forall x, fst d <= x < snd d -> outside Wm x)
                   (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0)).
    { apply Forall_forall. intros [a b] Hin x Hx. apply SUB. unfold reac_box_catalogue_match.aWc. cbn [outside]. split.
      - pose proof (fl_dj_out aWf (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0 ++ [(FS, fs_frame FS 0 0)]) a b x
                      HWd (in_or_app _ _ _ (or_introl Hin)) Hx) as Ho.
        unfold reac_box_catalogue_match.aWf in Ho. cbn [outside] in Ho. exact (proj1 Ho).
      - exact (fl_dj_out_r (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0) aXs a b x
                 (TLg DT0 TS0 C0 T0 DB0 kk0 HT0) Hin Hx). }
    destruct (fl_tls_same mc mc' Wm (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0 DT TS C T DB kk HT0 HTcells' MU Hc)
      as (E1 & E2 & E3 & E4 & E5 & E6). subst DT0 TS0 C0 T0 DB0 kk0.
    exact (TLg DT TS C T DB kk HT0). }
  split; [exact AD'|].
  split.
  { intros x Hx Hxf.
    destruct (Z_lt_le_dec x (sp2 - 8800)) as [Lo|Lo].
    - exact (cm_ab_keep Wm mc mc' x (AWXg x Hx Hxf) MU (OAW x Hx Hxf ltac:(clear -Lo; lia))).
    - destruct (Z_lt_le_dec x sp2) as [In2|Hi2].
      + pose proof AD' as AD'c. destruct AD'c as (_ & _ & _ & ADb).
        pose proof (ADb (x - (sp2 - 8800)) ltac:(clear -Lo In2; lia)) as ABx.
        replace (sp2 - 8800 + (x - (sp2 - 8800))) with x in ABx by (clear; lia). exact ABx.
      + exact (cm_ab_keep Wm mc mc' x (AWXg x Hx Hxf) MU (OAW x Hx Hxf ltac:(clear -Hi2; lia))). }
  split.
  { apply (acl_rw Wm mc mc' (S - 96) cmSAVES SVg MU WM).
    intros x Hx. apply OSV. unfold reac_box_catalogue_match.cmSAVES in Hx. cbn [cells_size csize] in Hx. clear -Hx. lia. }
  intros Enn.
  apply (fl_bytes Wm mc mc' (fr + 248) (le8 (Z_to_bv 64 (fs_flag FS 2 jj))) (FLg Enn) MU).
  intros x Hx. rewrite length_le8 in Hx. apply (OFL Enn). clear -Hx. lia.
Qed.


(* The register state at the 11-row loop head (pc 0x846ac), row i: s0 = S, s1 = CA, s2 = frame, s3 = the row
   address T + 296 i, s4 = fr + 112 (the model buffer), s5 = f + 18 (the input's 32 bytes), s6 = shadow_addr fr,
   s7 = fr, s8 = 11 - i (the rows left), s9 = 1, s10 = -8; the gate passed and no earlier row matches. *)
Definition cmLH_on (i : nat) (Q : machine_state -> Prop) : Prop :=
  forall (fr sp2 jj nn : Z) (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    RcMatch.cm_gate len fb = true -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
    cmInv_on fr sp2 jj nn mc ->
    evt rsegs Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 (CM_T + 296 * Z.of_nat i))
               (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               (Z_to_bv 64 (11 - Z.of_nat i)) (Z_to_bv 64 1) (Z_to_bv 64 (-8)) s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x846ac) fc None mc (seg_rom rsegs)).


(* The register state at the no-row tail (pc 0x84700): the parse result other than 9 and the exhausted loop reach it
   with the invariant at mc, and there the result the contract names is 0 (want CM_T len fb = 0). *)
Definition cmNone_on (Q : machine_state -> Prop) : Prop :=
  forall (fr sp2 jj nn : Z) (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs3 rs4 rs5 rs8 rs9 rs10 rt3 rt4 rt5 rt6 : word),
    want CM_T len fb = 0 -> cmInv_on fr sp2 jj nn mc ->
    evt rsegs Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) rs3 rs4 rs5 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               rs8 rs9 rs10 s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x84700) fc None mc (seg_rom rsegs)).


(* The run from the reac_ctrl_parse call at 0x84684 to the loop head: the call runs by its asan contract at the frame
   buffer [fr + 32, fr + 68) with the side-stack footprint fp [1] (fp_single of the invariant's fp [0;1;2]); at its
   return the invariant is rebuilt at the written memory (cm_inv_mu_on), `bne a0,9` sends a result other than 9 to the
   no-row tail (cmNone_on), and the equal branch sets up the loop registers and reaches the loop head of row 0. *)
Lemma cm_parse_on : forall Q, cmLH_on 0 Q -> cmNone_on Q -> cmPB_on Q.
Proof.
  intros Q KL KN fr sp2 jj nn mc rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 L E12 E13 E16 E17 INV APB.
  pose proof INV as INVk.
  destruct INV as (FK & MUg & WMg & RMg & MIg & ACg & SRg & FPg & TLg & ADg & AWXg & SVg & FLg).
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc).
  pose proof (fk_facts_on fr sp2 jj nn FK) as (_ & FRpos & _ & _ & FAP & _ & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRhi).
  destruct (HF L) as (Hf0 & Hf50 & _ & Hfd).
  pose proof (cm_FB mc L MUg) as BF. pose proof (cm_AF mc L MUg) as AF.
  pose proof (cm_stk_win_on fr sp2 jj nn mc INVk) as STW.
  destruct (stk_split rsegs mc (S - 9136) (sp2 - 8800) S STW ltac:(clear -Gsp; lia)) as (_ & STW2).
  destruct (stk_split rsegs mc (sp2 - 8800) sp2 S STW2 ltac:(clear -Gsp; lia)) as (STc & _).
  pose proof (cm_stk_fr_on fr sp2 jj nn mc INVk) as STF.
  destruct (stk_split rsegs mc fr (fr + 68) (fr + 192) STF ltac:(clear -FRpos; lia)) as (STF2 & _).
  destruct (stk_carve rsegs mc fr (fr + 68) 36 STF2 ltac:(clear -FRpos; lia)) as (_ & (junk & RWo)).
  replace (fr + 68 - Z.of_nat 36) with (fr + 32) in RWo by (clear -FRpos; lia).
  pose proof (cm_f_apart L fr sp2 jj nn FK) as Hfo.
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj).
  clear STW STW2 STF STF2.
  step.
  eapply evt_cut.
  { eapply HPC_on with (f := f) (n := len) (o := fr + 32) (S := sp2) (FS := FS) (fr := fb) (junk := junk);
      unfold REAC_CTRL_PARSE_K.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact Rf.
    - exact Rlen.
    - clear -FRpos FRhi RS. lia.
    - clear -Gsp RS. lia.
    - exact G16.
    - clear -Gsp HK. lia.
    - exact STc.
    - exact MIg.
    - exact Hfb.
    - intros _. split; [exact Hf0|]. split; [exact Hf50|]. clear -Hfd Gsp. lia.
    - intros i Hi. apply (proj2 (proj2 BF)). rewrite Hfb. pose proof (cp_rd_lt39 len fb i Hi). clear -H. lia.
    - intros _. split; [clear -G8; Z.div_mod_to_equations; lia|]. split; [clear -FRhi RS; lia|].
      split; [exact RWo|]. split; [clear -Gc Gsp; destruct Gc as [(_ & E & _)|(_ & _ & _ & _ & E)]; lia|].
      intros _. clear -Hfo. lia.
    - exact ACg.
    - exact (shadow_rw_on_mono _ _ mc (cm_R_parse fr sp2 jj nn FK L) SRg).
    - clear -Gsp HHM. lia.
    - clear -Gsp HAE. lia.
    - exact ADg.
    - intros _. exact AF.
    - intros _. split; [exact APB|].
      split; [replace (fr + 32 + 36) with (fr + 68) by (clear -FRpos; lia); apply FAP; clear; lia|].
      right. clear -FRgt. unfold asan_stack_malloc_c.CF, ASAN_GT in *. lia.
    - apply (cm_lo_addr mc _ _ MUg ABC). unfold REAC_CTRL_PARSE_BC, ASAN_GT. lia.
    - apply (cm_lo_bytes mc _ _ MUg HBCMP); unfold REAL_BCMP, ASAN_GT; [lia | rewrite length_le8; lia].
    - apply (cm_lo_bytes mc _ _ MUg HMEMCMP); unfold REAL_MEMCMP, ASAN_GT; [lia | rewrite length_le8; lia].
    - apply (cm_lo_bytes mc _ _ MUg HGOT); unfold GOT_CF, ASAN_GT; [lia | rewrite length_le8; lia].
    - apply (cm_lo_bytes mc _ _ MUg HCF254); unfold CF, ASAN_GT; cbn [length Z.of_nat Pos.of_succ_nat]; lia.
    - apply (cm_lo_bytes mc _ _ MUg HCF255); unfold CF, ASAN_GT; cbn [length Z.of_nat Pos.of_succ_nat]; lia.
    - unfold reac_ctrl_parse_W, reac_ctrl_parse_D, REAC_CTRL_PARSE_K.
      replace (fr + 32 =? 0) with false by (symmetry; apply Z.eqb_neq; clear -FRpos; lia).
      replace (len <? 50) with false by (symmetry; apply Z.ltb_ge; exact L).
      cbn [app].
      apply (cm_fp_call_on 1%nat fr sp2 jj nn mc 8800 32 36); try (clear; lia).
      + exact INVk.
      + cbn. tauto.
      + apply (fl_dj_cons (f, f + 50) [(fr + 32, fr + 32 + 36)] (fp_w [1%nat] FS)). split.
        * unfold reac_box_catalogue_match.aDf in FSdj. replace (len <? 50) with false in FSdj by (symmetry; apply Z.ltb_ge; exact L).
          exact (fp_dj_incl _ _ _ (fp_w_incl 1%nat [0%nat; 1%nat; 2%nat] FS ltac:(cbn; tauto)) FSdj).
        * exact (cm_dj_buf_on fr sp2 jj nn 32 36 1%nat FK ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                   ltac:(clear; lia)).
    - unfold reac_ctrl_parse_tls, REAC_CTRL_PARSE_K.
      exact (cm_tls_call mc 1%nat 8800 sp2 TLg ltac:(cbn; tauto) ltac:(clear -Gsp; lia) ltac:(clear -Gsp; lia)). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & E2 & MU2 & WM2
              & MI2 & ST2 & RO2 & AC2 & SW2 & AW2 & FP2 & TL2).
  subst ms'.
  specialize (RO2 ltac:(clear -FRpos; lia)).
  unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in MU2, ST2, AW2.
  replace (fr + 32 =? 0) with false in MU2 by (symmetry; apply Z.eqb_neq; clear -FRpos; lia).
  cbn [app] in MU2.
  assert (MUc : munch (cmWc fr sp2 8800 32 36 1%nat) mc m2) by exact MU2. clear MU2.
  destruct (cm_bytes_of_rw rsegs m2 (fr + 32) 36 _ RO2) as (BO2 & LO2).
  assert (RDB : forall y, fr + 32 <= y < fr + 32 + 36 -> exists b, mrd rsegs m2 (wa y) = Some b).
  { intros y Hy. apply (acl_bytes_rd m2 (fr + 32) _ y BO2). rewrite LO2.
    change (Z.of_nat 36) with 36. clear -Hy. lia. }
  pose proof FP2 as (DTx & TSx & Cx & Tx & DBx & kx & _ & _ & (_ & _ & _ & _ & STFS2) & _).
  assert (APPw : forall a, sp2 - 8800 <= a < sp2 -> app_mem a).
  { intros a Ha. replace a with (sp2 - 8800 + (a - (sp2 - 8800))) by (clear -Ha; lia).
    apply (acl_app_in mc (sp2 - 8800) 8800); [exact ADg | clear -Ha; lia]. }
  assert (RM2 : rd_mono mc m2).
  { apply (cm_Wc_rd_on fr sp2 8800 32 36 1%nat mc m2 ltac:(clear; lia) MUc RDB ST2 STFS2
             (shadow_rw_on_mono _ _ m2 (cm_Wc_rd_R sp2 8800 1%nat ltac:(clear; lia) ltac:(clear -Gsp; lia)
                ltac:(clear -Gsp; lia)) (SW2 _ SRg)) APPw
             ltac:(clear -G16; Z.div_mod_to_equations; lia)). }
  pose proof FPg as FPc.
  destruct FPc as (DT0 & TS0 & C0 & T0 & DB0 & kk0 & HT0 & HTP0 & HPl0 & H880 & H960 & HCL0 & HFS0 & HApp0 & HWd0
                   & HDd0).
  rewrite Forall_forall in HCL0.
  assert (INV2 : cmInv_on fr sp2 jj nn m2).
  { apply (cm_inv_mu_on fr sp2 jj nn mc m2 (cmWc fr sp2 8800 32 36 1%nat) INVk MUc WM2 RM2 MI2).
    - exact (cm_Wc_sub fr sp2 jj nn 8800 32 36 1%nat FK ltac:(cbn; tauto) ltac:(clear; lia) ltac:(clear; lia)
               ltac:(clear; lia) ltac:(clear; lia)).
    - intros c Hc. destruct Hc as [<-|[<-|[<-|[]]]].
      + apply (cm_cls_keep 0%nat mc m2 (cmWc fr sp2 8800 32 36 1%nat) (HCL0 0%nat ltac:(cbn; tauto)) MUc).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 8800 32 36 1%nat 0%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_introl Hx)).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 8800 32 36 1%nat 0%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_intror Hx)).
      + exact (cm_cls_fp 1%nat m2 (bv_unsigned tp) (sp2 - 8800) sp2 _ _ FP2).
      + apply (cm_cls_keep 2%nat mc m2 (cmWc fr sp2 8800 32 36 1%nat) (HCL0 2%nat ltac:(cbn; tauto)) MUc).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 8800 32 36 1%nat 2%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_introl Hx)).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 8800 32 36 1%nat 2%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_intror Hx)).
    - exact AW2.
    - intros x Hx _ Hx2.
      exact (cm_Wc_sh_out_on fr sp2 jj nn 8800 32 36 1%nat x FK ltac:(cbn; tauto) ltac:(clear; lia)
               ltac:(clear; reflexivity) ltac:(clear; lia) ltac:(clear; lia) Hx Hx2).
    - intros x Hx. exact (cm_Wc_saves fr sp2 jj nn 8800 32 36 1%nat x FK ltac:(cbn; tauto) ltac:(clear; lia)
                            ltac:(clear; lia) ltac:(clear; lia) Hx).
    - intros Enn x Hx. exact (cm_Wc_flag fr sp2 jj nn 8800 32 36 1%nat x FK Enn ltac:(clear; lia)
                                ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) Hx). }
  replace (ret_pc (Z_to_bv 64 0x84688)) with (Z_to_bv 64 0x84688)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  step. step.
  pose proof (ctrlparse_kind_range len fb) as KR.
  rewrite cm_eqb_lit by (clear -KR; lia).
  destruct (Z.eqb_spec (fst (ctrlparse len fb)) 9) as [K9|K9]; cbn [negb]; cbv iota.
  - assert (G : RcMatch.cm_gate len fb = true).
    { unfold RcMatch.cm_gate. rewrite (proj2 (Z.leb_le 50 len) L), E12, E13, E16, E17, K9. reflexivity. }
    do 7 step.
    eapply KL; [exact G | intros j Hj; clear -Hj; lia | exact INV2].
  - eapply KN; [| exact INV2].
    apply cm_gate_false. unfold RcMatch.cm_gate. rewrite (proj2 (Z.eqb_neq _ _) K9).
    rewrite !andb_false_r. reflexivity.
Qed.


(* The shadow byte of a window byte below the callee window [sp2 - K, sp2) is apart from the callee writes. *)
Lemma cm_Wc_sh_lo_on : forall fr sp2 jj nn K d n c x, cmFK fr sp2 jj nn -> In c [0%nat; 1%nat; 2%nat] ->
  0 <= K <= 8800 -> K mod 8 = 0 -> 0 <= d -> d + n <= 192 -> S - 9136 <= x < sp2 - K ->
  outside (cmWc fr sp2 K d n c) (shadow_addr x).
Proof.
  intros fr sp2 jj nn K d n c x FK Hc HKr HK8 Hd Hdn Hx.
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc).
  pose proof (fk_facts_on fr sp2 jj nn FK) as (_ & FRpos & _ & _ & FAP & _ & _).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). pose proof HHM as HHM'. pose proof HAE as HAE'.
  unfold FS_SIZE in FShi. unfold HIGHMEM_BEG in HHM'. unfold APPMEM_END in HAE'.
  assert (Hap : app_mem x) by (clear -Hx Gsp HKr HHM' HAE'; unfold app_mem, HIGHMEM_BEG, APPMEM_END; right; lia).
  pose proof (rt_app_shadow x Hap) as Hsh.
  assert (Ho3 : outside (fp_w [0%nat; 1%nat; 2%nat] FS) x)
    by (apply acl_out_fpw_hi; [clear -Hx FShi; unfold FS_SIZE; lia | exact Hap]).
  unfold reac_box_catalogue_match.cmWc. cbn [outside]. split; [|split].
  - apply (sh_out_app _ (fr + d) (fr + d + n) Hsh).
    intros z Hz. replace z with (fr + (z - fr)) by (clear -Hz; lia). apply FAP. clear -Hz Hd Hdn. lia.
  - apply (sh_out_app _ (sp2 - K) sp2 Hsh).
    intros z Hz. clear -Hz Gsp HKr HHM' HAE'. unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia.
  - apply fl_out_app; [exact (cm_out_fpw_c c (shadow_addr x) Hc (acl_out_fpw_sh x Hap Ho3))|].
    cbn [outside]. split; [|exact I].
    apply acl_win_sh; [clear -G16 HK8; Z.div_mod_to_equations; lia | clear -Hx; lia].
Qed.


(* The callee window [sp2 - 8800, sp2) stays addressable: the part below the callee's window by its shadow apart from
   the callee writes, the callee's window by the callee's post. *)
Lemma cm_ad_join_on : forall fr sp2 jj nn K d n c ma mb, cmFK fr sp2 jj nn -> In c [0%nat; 1%nat; 2%nat] ->
  0 <= K <= 8800 -> K mod 8 = 0 -> 0 <= d -> d + n <= 192 ->
  addressable ma (sp2 - 8800) 8800 -> munch (cmWc fr sp2 K d n c) ma mb -> addressable mb (sp2 - K) K ->
  addressable mb (sp2 - 8800) 8800.
Proof.
  intros fr0 sp0 jj0 nn0 K d n c ma mb FK Hc HKr HK8 Hd Hdn ADa MU ADb.
  pose proof (cm_geo fr0 sp0 jj0 nn0 FK) as (_ & _ & G16' & Gsp' & _).
  assert (ADlo : addressable mb (sp0 - 8800) (8800 - K)).
  { apply (acl_addr_munch (cmWc fr0 sp0 K d n c) ma mb (sp0 - 8800) (8800 - K)
             (acl_addr_sub ma (sp0 - 8800) 8800 (sp0 - 8800) (8800 - K) ADa ltac:(clear; lia)
                ltac:(clear -HKr; lia) ltac:(clear -HKr; lia)) MU).
    intros k Hk. apply (cm_Wc_sh_lo_on fr0 sp0 jj0 nn0 K d n c _ FK Hc HKr HK8 Hd Hdn). clear -Hk Gsp' HKr. lia. }
  assert (AJ : addressable mb (sp0 - 8800) ((8800 - K) + K)).
  { apply (acl_addr_join mb (sp0 - 8800) (8800 - K) K ADlo); [| clear -HKr; lia].
    replace (sp0 - 8800 + (8800 - K)) with (sp0 - K) by (clear; lia). exact ADb. }
  replace (8800 - K + K) with 8800 in AJ by (clear; lia). exact AJ.
Qed.


(* The shadow byte of a byte of a frame buffer is apart from the writes of a class-0 or class-1 callee. *)
Lemma cm_Wc_sh_buf_on : forall fr sp2 jj nn K d n c k, cmFK fr sp2 jj nn -> (c <= 1)%nat -> 0 <= K <= 8800 ->
  K mod 8 = 0 -> 0 <= d -> d + n <= 192 -> 0 <= k < n ->
  outside (cmWc fr sp2 K d n c) (shadow_addr (fr + d + k)).
Proof.
  intros fr sp2 jj nn K d n c k FK Hc HKr HK8 Hd Hdn Hk.
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc).
  pose proof (fk_facts_on fr sp2 jj nn FK) as (_ & FRpos & _ & _ & FAP & _ & _).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). pose proof HHM as HHM'. pose proof HAE as HAE'.
  unfold FS_SIZE in FShi. unfold HIGHMEM_BEG in HHM'. unfold APPMEM_END in HAE'.
  assert (Hap : app_mem (fr + d + k)).
  { replace (fr + d + k) with (fr + (d + k)) by (clear; lia). apply FAP. clear -Hd Hdn Hk. lia. }
  pose proof (rt_app_shadow _ Hap) as Hsh.
  assert (Hfr0 : fs_frame FS c (fs_M c) <= fr).
  { clear -Gc Hc FShi Gsp. unfold fs_frame, fs_B, fs_M.
    destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat]; destruct Gc as [(_ & E & _)|(_ & E & Hj & _)]; lia. }
  unfold reac_box_catalogue_match.cmWc. cbn [outside]. split; [|split].
  - apply (sh_out_app _ (fr + d) (fr + d + n) Hsh).
    intros z Hz. replace z with (fr + (z - fr)) by (clear -Hz; lia). apply FAP. clear -Hz Hd Hdn. lia.
  - apply (sh_out_app _ (sp2 - K) sp2 Hsh).
    intros z Hz. clear -Hz Gsp HKr HHM' HAE'. unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia.
  - apply fl_out_app.
    + cbn [fp_w flat_map fp_w1 app outside]. split; [|split; [|split; [|split; [|exact I]]]].
      * apply (sh_out_app _ (fs_hint FS c) (fs_hint FS c + 8) Hsh). intros z Hz. apply FSapp.
        clear -Hz Hc FSpos. unfold fs_hint, FS_SIZE in *. destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat] in *; lia.
      * apply (sh_out_app _ (fs_flag FS c 0) (fs_flag FS c 0 + fs_M c) Hsh). intros z Hz. apply FSapp.
        clear -Hz Hc FSpos. unfold fs_flag, fs_M, FS_SIZE in *.
        destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat] in *; lia.
      * apply (sh_out_app _ (fs_frame FS c 0) (fs_frame FS c (fs_M c)) Hsh). intros z Hz. apply FSapp.
        clear -Hz Hc FSpos. unfold fs_frame, fs_B, fs_M, FS_SIZE in *.
        destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat] in *; lia.
      * apply acl_win_sh;
          [ clear -Hc FSmod; unfold fs_frame, fs_B; destruct c as [|[|c]]; cbn [Z.of_nat Pos.of_succ_nat];
            Z.div_mod_to_equations; lia
          | clear -Hfr0 Hd Hk; lia ].
    + cbn [outside]. split; [|exact I].
      apply acl_win_sh; [clear -G16 HK8; Z.div_mod_to_equations; lia |].
      clear -Gc Gsp HKr Hd Hdn Hk FShi.
      destruct Gc as [(_ & E & _)|(_ & _ & _ & _ & E)]; lia.
Qed.


(* The register state at the row-match tail (pc 0x84864): the bcmp wrapper returned 0, s3 is the matching row's
   address r, and there the result the contract names is r (want CM_T len fb = r). *)
Definition cmHit_on (Q : machine_state -> Prop) : Prop :=
  forall (fr sp2 jj nn r : Z) (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs4 rs5 rs8 rs9 rs10 rt3 rt4 rt5 rt6 : word),
    want CM_T len fb = r -> cmInv_on fr sp2 jj nn mc ->
    evt rsegs Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 r) rs4 rs5
               (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) rs8 rs9 rs10 s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x84864) fc None mc (seg_rom rsegs)).


(* The register state at the bcmp wrapper call (pc 0x846dc), row i: a0 = f + 18, a1 = fr + 112, a2 = 32, the loop
   registers as at the loop head; the model buffer is addressable and holds row i's 32-byte declaration. *)
Definition cmBC_on (i : nat) (Q : machine_state -> Prop) : Prop :=
  forall (fr sp2 jj nn : Z) (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
    RcMatch.cm_gate len fb = true -> (i < 11)%nat -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
    cmInv_on fr sp2 jj nn mc -> addressable mc (fr + 112) 32 ->
    bytes_at rsegs mc (fr + 112) (nth i DECLS []) ->
    evt rsegs Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 32) ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 (CM_T + 296 * Z.of_nat i))
               (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               (Z_to_bv 64 (11 - Z.of_nat i)) (Z_to_bv 64 1) (Z_to_bv 64 (-8)) s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x846dc) fc None mc (seg_rom rsegs)).


(* The run from the loop head at 0x846ac (row i) to the bcmp wrapper call: the un-poisoning of the model buffer's
   shadow (bytes 14..17 -> 0, inside cmHF fr, cm_inv_step_on), the reac_box_model_block call (row T + 296 i, b = 0,
   o = fr + 112) by its asan contract with the side-stack footprint fp [0] (fp_single); the row is a catalogue row, so
   the result is 1 and the buffer holds row i's declaration (cm_rc); at the return the invariant is rebuilt
   (cm_inv_mu_on), `bne a0,s9` (s9 = 1) falls through, and a0/a1/a2 are set for the bcmp wrapper (cmBC_on). *)
Lemma cm_model_on : forall i Q, (i < 11)%nat -> cmBC_on i Q -> cmLH_on i Q.
Proof.
  intros i Q Hi KB fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 G Hnd INV.
  pose proof INV as INVk.
  assert (L50 : 50 <= len).
  { destruct (Z.leb_spec 50 len) as [L|L]; [exact L|]. exfalso. unfold RcMatch.cm_gate in G.
    rewrite (proj2 (Z.leb_gt 50 len) L) in G. cbn [andb] in G. discriminate G. }
  destruct INV as (FK & MUg & WMg & RMg & MIg & ACg & SRg & FPg & TLg & ADg & AWXg & SVg & FLg).
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc).
  pose proof (fk_facts_on fr sp2 jj nn FK) as (FR8 & FRpos & FR192 & FW & FAP & FSW & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRhi).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj).
  clear MUg.
  assert (SHlo : 0 <= shadow_addr fr).
  { unfold shadow_addr. assert (D : 0 <= fr / 8) by (apply Z.div_pos; clear -FRpos; lia).
    unfold ASAN_K. clear -D. lia. }
  assert (SHhi : shadow_addr fr + 24 <= 2 ^ 64).
  { unfold shadow_addr, ASAN_K. clear -FRpos FRhi RS. Z.div_mod_to_equations. lia. }
  assert (FSW' : forall k, 0 <= k < 24 -> wview rsegs m (wa (shadow_addr fr + k)) <> None) by exact FSW.
  clear FSW.
  assert (MUh : munch (cmHF fr) mc mc) by apply munch_refl.
  assert (WMh : wmono rsegs mc mc) by apply wmono_refl.
  assert (RMh : rd_mono mc mc) by apply rd_mono_refl.
  unfold reac_box_catalogue_match.cmHF in MUh.
  cm_wst (shadow_addr fr + 14) 1%nat. step. cm_keep B14.
  cm_wst (shadow_addr fr + 15) 1%nat. step. cm_keep B15.
  cm_wst (shadow_addr fr + 16) 1%nat. step. cm_keep B16.
  cm_wst (shadow_addr fr + 17) 1%nat. step. cm_keep B17.
  pose proof (cm_inv_step_on fr sp2 jj nn mc _ INVk MUh WMh RMh MIg) as INV1.
  pose proof INV1 as INV1k.
  destruct INV1 as (_ & MU1 & WM1 & RM1 & MI1 & AC1 & SR1 & FP1 & TL1 & AD1 & AWX1 & SV1 & FL1).
  assert (ADm : addressable m1 (fr + 112) 32).
  { apply (cm_model_addr m1 fr FR8 ltac:(clear -FRpos; lia)
             ltac:(clear -FRhi HAE; unfold APPMEM_END in *; lia));
      [ intros k Hk; replace (fr + 112 + k) with (fr + (112 + k)) by (clear -Hk; lia); apply FAP; clear -Hk; lia
      | exact B14 | exact B15 | exact B16 | exact B17 ]. }
  pose proof (cm_stk_fr_on fr sp2 jj nn m1 INV1k) as STF1.
  destruct (stk_split rsegs m1 fr (fr + 144) (fr + 192) STF1 ltac:(clear -FRpos; lia)) as (STF1a & _).
  destruct (stk_carve rsegs m1 fr (fr + 144) 32 STF1a ltac:(clear -FRpos; lia)) as (_ & (ob & RWm)).
  replace (fr + 144 - Z.of_nat 32) with (fr + 112) in RWm by (clear -FRpos; lia).
  pose proof (cm_stk_win_on fr sp2 jj nn m1 INV1k) as STW1.
  destruct (stk_split rsegs m1 (S - 9136) (sp2 - 4272) S STW1 ltac:(clear -Gsp; lia)) as (_ & STW1b).
  destruct (stk_split rsegs m1 (sp2 - 4272) sp2 S STW1b ltac:(clear -Gsp; lia)) as (STc1 & _).
  pose proof (cm_tbl m1 MU1) as BT.
  pose proof (bytes_at_sub rsegs m1 CM_T CM_TBL (296 * i) 296 BT ltac:(rewrite CM_TBL_len; clear -Hi; lia)) as BR.
  apply (bytes_at_addr rsegs m1 _ (CM_T + 296 * Z.of_nat i)) in BR; [|clear; lia].
  fold (cm_row i) in BR.
  pose proof (cm_lo_addr m1 CM_T 3256 MU1 AT ltac:(unfold CM_T, ASAN_GT; clear; lia)) as ATm.
  do 4 step.
  eapply evt_cut.
  { eapply HMB_on with (p := CM_T + 296 * Z.of_nat i) (b := 0) (o := fr + 112) (FS := FS)
                    (row := cm_row i) (nb := @nil byte) (ob := ob);
      rewrite ?unsigned_lit by (clear -Gsp RS HK; lia); unfold REAC_BOX_MODEL_BLOCK_K.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold CM_T. clear -Hi. lia.
    - clear. lia.
    - clear -FRpos FRhi RS. lia.
    - exact G16.
    - exact STc1.
    - intros _. split; [unfold CM_T; clear -Hi; Z.div_mod_to_equations; lia|].
      split; [exact (cm_row_len i Hi)|]. split; [exact BR|].
      split; [right; unfold CM_T in *; clear -Hi Gsp HHM; unfold HIGHMEM_BEG in *; lia|].
      right; right; clear -Hi FRgt; unfold CM_T, ASAN_GT in *; lia.
    - intros _ [E|E]; discriminate E.
    - intros _. split; [exact RWm|].
      split; [clear -Gc Gsp FShi; destruct Gc as [(_ & E & _)|(_ & _ & _ & _ & E)]; lia|].
      right. clear -FRgt. unfold JOIN_0014, ASAN_GT in *. lia.
    - exact MI1.
    - exact AC1.
    - exact (shadow_rw_on_mono _ _ m1 (cm_R_mb fr sp2 jj nn i _ _ FK L50 Hi) SR1).
    - clear -Gsp HHM. unfold HIGHMEM_BEG in *. lia.
    - clear -Gsp HAE. lia.
    - exact (acl_addr_sub m1 (sp2 - 8800) 8800 (sp2 - 4272) 4272 AD1 ltac:(clear; lia) ltac:(clear; lia)
               ltac:(clear; lia)).
    - intros _. exact (acl_addr_sub m1 CM_T 3256 (CM_T + 296 * Z.of_nat i) 296 ATm ltac:(clear -Hi; lia)
                         ltac:(clear; lia) ltac:(clear -Hi; lia)).
    - intros _ [E|E]; discriminate E.
    - intros _. split; [exact ADm|].
      split; [replace (fr + 112 + 32) with (fr + 144) by (clear; lia); apply FAP; clear; lia|].
      right. clear -FRgt. unfold RT_HI, ASAN_GT in *. lia.
    - intros E; discriminate E.
    - intros E; discriminate E.
    - unfold reac_box_model_block_W, reac_box_model_block_D.
      replace (fr + 112 =? 0) with false by (symmetry; apply Z.eqb_neq; clear -FRpos; lia).
      replace (CM_T + 296 * Z.of_nat i =? 0) with false
        by (symmetry; apply Z.eqb_neq; unfold CM_T; clear -Hi; lia).
      cbn [app].
      apply (cm_fp_call_on 0%nat fr sp2 jj nn m1 4272 112 32); try (clear; lia).
      + exact INV1k.
      + cbn. tauto.
      + apply (fl_dj_cons (CM_T + 296 * Z.of_nat i, CM_T + 296 * Z.of_nat i + 296)
                 [(fr + 112, fr + 112 + 32)] (fp_w [0%nat] FS)). split.
        * apply cm_dj_lo; [unfold CM_T; clear -Hi; lia | unfold CM_T, ASAN_GT; clear -Hi; lia | clear; lia].
        * exact (cm_dj_buf_on fr sp2 jj nn 112 32 0%nat FK ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
                   ltac:(clear; lia)).
    - intros _ [E|E]; discriminate E.
    - unfold reac_box_model_block_tls.
      exact (cm_tls_call m1 0%nat 4272 sp2 TL1 ltac:(cbn; tauto) ltac:(clear -Gsp; lia) ltac:(clear -Gsp; lia)). }
  intros ms' Hpost. unfold reac_box_model_block_post_on in Hpost.
  rewrite (unsigned_lit sp2) in Hpost by (clear -Gsp RS HK; lia).
  destruct Hpost as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6''
                     & m2 & E2 & PB & WM2 & MI2 & ST2 & AC2 & SW2 & AW2 & FP2 & TL2).
  subst ms'.
  assert (Z0 : (CM_T + 296 * Z.of_nat i =? 0) || (fr + 112 =? 0) = false)
    by (apply orb_false_iff; split; apply Z.eqb_neq; [unfold CM_T; clear -Hi; lia | clear -FRpos; lia]).
  rewrite Z0 in PB |- *. destruct PB as (BB & MU2).
  destruct (cm_rc i (@nil byte) Hi) as (RC & SY). rewrite RC. rewrite SY in BB.
  unfold reac_box_model_block_X, REAC_BOX_MODEL_BLOCK_K in MU2, ST2, AW2. cbn [app] in MU2.
  assert (MUc : munch (cmWc fr sp2 4272 112 32 0%nat) m1 m2)
    by exact (munch_weaken _ _ m1 m2 (cm_Wc_swap fr sp2 4272 112 32 0%nat) MU2).
  clear MU2.
  pose proof (cm_decl_len i Hi) as LD.
  assert (RDB : forall y, fr + 112 <= y < fr + 112 + 32 -> exists b, mrd rsegs m2 (wa y) = Some b).
  { intros y Hy. apply (acl_bytes_rd m2 (fr + 112) _ y BB). rewrite LD.
    change (Z.of_nat 32) with 32. clear -Hy. lia. }
  pose proof FP2 as (DTx & TSx & Cx & Tx & DBx & kx & _ & _ & (_ & _ & _ & _ & STFS2) & _).
  assert (APPw : forall a, sp2 - 4272 <= a < sp2 -> app_mem a).
  { intros a Ha. replace a with (sp2 - 8800 + (a - (sp2 - 8800))) by (clear -Ha; lia).
    apply (acl_app_in m1 (sp2 - 8800) 8800); [exact AD1 | clear -Ha; lia]. }
  assert (RM2 : rd_mono m1 m2).
  { apply (cm_Wc_rd_on fr sp2 4272 112 32 0%nat m1 m2 ltac:(clear; lia) MUc RDB ST2 STFS2
             (shadow_rw_on_mono _ _ m2 (cm_Wc_rd_R sp2 4272 0%nat ltac:(clear; lia) ltac:(clear -Gsp; lia)
                ltac:(clear -Gsp; lia)) (SW2 _ SR1)) APPw
             ltac:(clear -G16; Z.div_mod_to_equations; lia)). }
  pose proof FP1 as FPc.
  destruct FPc as (DT0 & TS0 & C0 & T0 & DB0 & kk0 & HT0 & HTP0 & HPl0 & H880 & H960 & HCL0 & HFS0 & HApp0 & HWd0
                   & HDd0).
  rewrite Forall_forall in HCL0.
  assert (AD2 : addressable m2 (sp2 - 8800) 8800)
    by exact (cm_ad_join_on fr sp2 jj nn 4272 112 32 0%nat m1 m2 FK ltac:(cbn; tauto) ltac:(clear; lia)
                ltac:(clear; reflexivity) ltac:(clear; lia) ltac:(clear; lia) AD1 MUc AW2).
  assert (INV2 : cmInv_on fr sp2 jj nn m2).
  { apply (cm_inv_mu_on fr sp2 jj nn m1 m2 (cmWc fr sp2 4272 112 32 0%nat) INV1k MUc WM2 RM2 MI2).
    - exact (cm_Wc_sub fr sp2 jj nn 4272 112 32 0%nat FK ltac:(cbn; tauto) ltac:(clear; lia) ltac:(clear; lia)
               ltac:(clear; lia) ltac:(clear; lia)).
    - intros c Hc. destruct Hc as [<-|[<-|[<-|[]]]].
      + exact (cm_cls_fp 0%nat m2 (bv_unsigned tp) (sp2 - 4272) sp2 _ _ FP2).
      + apply (cm_cls_keep 1%nat m1 m2 (cmWc fr sp2 4272 112 32 0%nat) (HCL0 1%nat ltac:(cbn; tauto)) MUc).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 4272 112 32 0%nat 1%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_introl Hx)).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 4272 112 32 0%nat 1%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_intror Hx)).
      + apply (cm_cls_keep 2%nat m1 m2 (cmWc fr sp2 4272 112 32 0%nat) (HCL0 2%nat ltac:(cbn; tauto)) MUc).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 4272 112 32 0%nat 2%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_introl Hx)).
        * intros x Hx. exact (cm_cls_out_Wc fr sp2 jj nn 4272 112 32 0%nat 2%nat x FK ltac:(clear; lia)
            ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
            (or_intror Hx)).
    - exact AD2.
    - intros x Hx _ Hx2.
      exact (cm_Wc_sh_out_on fr sp2 jj nn 4272 112 32 0%nat x FK ltac:(cbn; tauto) ltac:(clear; lia)
               ltac:(clear; reflexivity) ltac:(clear; lia) ltac:(clear; lia) Hx Hx2).
    - intros x Hx. exact (cm_Wc_saves fr sp2 jj nn 4272 112 32 0%nat x FK ltac:(cbn; tauto) ltac:(clear; lia)
                            ltac:(clear; lia) ltac:(clear; lia) Hx).
    - intros Enn x Hx. exact (cm_Wc_flag fr sp2 jj nn 4272 112 32 0%nat x FK Enn ltac:(clear; lia)
                                ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) Hx). }
  assert (ADm2 : addressable m2 (fr + 112) 32).
  { apply (acl_addr_munch (cmWc fr sp2 4272 112 32 0%nat) m1 m2 (fr + 112) 32 ADm MUc).
    intros k Hk. exact (cm_Wc_sh_buf_on fr sp2 jj nn 4272 112 32 0%nat k FK ltac:(clear; lia) ltac:(clear; lia)
                          ltac:(clear; reflexivity) ltac:(clear; lia) ltac:(clear; lia) Hk). }
  replace (ret_pc (Z_to_bv 64 0x846cc)) with (Z_to_bv 64 0x846cc)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  step.
  rewrite cm_eqb_lit by (clear; lia).
  replace (1 =? 1) with true by reflexivity. cbn [negb]. cbv iota.
  do 3 step.
  eapply KB; [exact G | exact Hi | exact Hnd | exact INV2 | exact ADm2 | exact BB].
Qed.


(* cmLH_on with the row-address and rows-left registers given by equations (for the loop's back edge). *)
Lemma cm_lh_eq_on : forall i Q, cmLH_on i Q ->
  forall (fr sp2 jj nn : Z) (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 w3 w8 : word),
    w3 = Z_to_bv 64 (CM_T + 296 * Z.of_nat i) -> w8 = Z_to_bv 64 (11 - Z.of_nat i) ->
    RcMatch.cm_gate len fb = true -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
    cmInv_on fr sp2 jj nn mc ->
    evt rsegs Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 S) (Z_to_bv 64 CA)
               ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) w3
               (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               w8 (Z_to_bv 64 1) (Z_to_bv 64 (-8)) s11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x846ac) fc None mc (seg_rom rsegs)).
Proof.
  intros i Q K fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 w3 w8 -> ->.
  apply K.
Qed.


(* The run from the bcmp wrapper call at 0x846dc (row i) to the next loop head: the wrapper compares the input's 32
   bytes at f + 18 with the model buffer by its contract (both ranges addressable, the window [sp2 - 4560, sp2) below
   the frame); at its return the invariant is rebuilt (cm_inv_mu_on, the wrapper writes only its window); `beqz a0` sends
   a match to the row-match tail (cmHit_on, want = T + 296 i); otherwise the model buffer's shadow is marked unusable
   again (bytes 14..17 -> 0xf8, inside cmHF fr), s8 counts down, s3 moves to the next row, and `bnez s8` reaches the
   loop head of row i + 1 (cmLH_on) or, after the last row, the no-row tail (cmNone_on, want = 0). *)
Lemma cm_bcmp_on : forall i Q, (i < 11)%nat -> ((i + 1 < 11)%nat -> cmLH_on (i + 1)%nat Q) -> cmNone_on Q -> cmHit_on Q ->
  cmBC_on i Q.
Proof.
  intros i Q Hi KL KN KH fr sp2 jj nn mc rra rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 G _ Hnd INV ADb BB.
  pose proof INV as INVk.
  destruct INV as (FK & MUg & WMg & RMg & MIg & ACg & SRg & FPg & TLg & ADg & AWXg & SVg & FLg).
  pose proof (cm_geo fr sp2 jj nn FK) as (G8 & Gfs & G16 & Gsp & Gc).
  pose proof (fk_facts_on fr sp2 jj nn FK) as (FR8 & FRpos & FR192 & FW & FAP & FSW & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRhi).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj). unfold FS_SIZE in FShi.
  assert (L : 50 <= len).
  { destruct (Z.leb_spec 50 len) as [L|L]; [exact L|]. exfalso. unfold RcMatch.cm_gate in G.
    rewrite (proj2 (Z.leb_gt 50 len) L) in G. cbn [andb] in G. discriminate G. }
  destruct (HF L) as (Hf0 & Hf50 & _ & Hfd). destruct (AFU L) as (_ & Af50).
  pose proof (cm_FB mc L MUg) as BF. pose proof (cm_AF mc L MUg) as AF.
  pose proof (bytes_at_sub rsegs mc f fb 18 32 BF ltac:(rewrite Hfb; clear; lia)) as BK.
  apply (bytes_at_addr rsegs mc _ (f + 18)) in BK; [|clear; lia].
  fold (cm_blk fb) in BK.
  assert (LK : length (cm_blk fb) = 32%nat)
    by (unfold cm_blk; rewrite length_firstn, length_skipn, Hfb; clear; lia).
  destruct (memcmp_model_total (cm_blk fb) (nth i DECLS []) 32 ltac:(rewrite LK; clear; lia)
              ltac:(rewrite (cm_decl_len i Hi); clear; lia)) as [v Hv].
  pose proof (mm_spec 32 (cm_blk fb) (nth i DECLS []) v LK (cm_decl_len i Hi) Hv) as [MM VR].
  pose proof (cm_stk_win_on fr sp2 jj nn mc INVk) as STW.
  destruct (stk_split rsegs mc (S - 9136) (sp2 - 4560) S STW ltac:(clear -Gsp; lia)) as (_ & STW2).
  destruct (stk_split rsegs mc (sp2 - 4560) sp2 S STW2 ltac:(clear -Gsp; lia)) as (STc & _).
  clear STW STW2.
  step.
  eapply evt_cut.
  { eapply HBC_on with (ls := cm_blk fb) (rs := nth i DECLS []) (v := v) (lo := sp2 - 4560);
      cbv zeta; rewrite ?unsigned_lit by (clear -Hf0 Hf50 FRpos FRhi RS Gsp HK; lia); unfold BCMP_WRAP_K.
    - exact BK.
    - exact BB.
    - exact Hv.
    - exact MIg.
    - clear. lia.
    - exact (acl_addr_sub mc f 50 (f + 18) 32 AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
    - exact ADb.
    - unfold end_in_app. right. replace (f + 18 + 32) with (f + 50) by (clear; lia). exact Af50.
    - unfold end_in_app. right. replace (fr + 112 + 32) with (fr + 144) by (clear; lia). apply FAP. clear; lia.
    - right. replace (f + 18 + 7) with (f + 25) by (clear; lia). exact (acl_app_in mc f 50 25 AF ltac:(clear; lia)).
    - right. replace (fr + 112 + 7) with (fr + 119) by (clear; lia). apply FAP. clear; lia.
    - clear -Hfd Gsp. lia.
    - clear -Gc Gsp. destruct Gc as [(_ & E & _)|(_ & _ & _ & _ & E)]; lia.
    - exact STc.
    - clear. lia.
    - clear -Gsp HHM. unfold HIGHMEM_BEG in *. lia.
    - clear -Gsp HAE. lia.
    - exact ACg.
    - exact (shadow_rw_on_mono _ _ mc (cm_R_bcmp fr sp2 jj nn FK L) SRg).
    - apply (cm_lo_bytes mc _ _ MUg HBCMP); unfold REAL_BCMP, ASAN_GT; [lia | rewrite length_le8; lia].
    - apply (cm_lo_bytes mc _ _ MUg HMEMCMP); unfold REAL_MEMCMP, ASAN_GT; [lia | rewrite length_le8; lia].
    - apply (cm_lo_bytes mc _ _ MUg HGOT); unfold GOT_CF, ASAN_GT; [lia | rewrite length_le8; lia].
    - apply (cm_lo_bytes mc _ _ MUg HCF254); unfold CF, ASAN_GT; cbn [length Z.of_nat Pos.of_succ_nat]; lia.
    - apply (cm_lo_bytes mc _ _ MUg HCF255); unfold CF, ASAN_GT; cbn [length Z.of_nat Pos.of_succ_nat]; lia. }
  intros ms' Hpost. unfold bcmp_wrap_post_on in Hpost.
  rewrite (unsigned_lit sp2) in Hpost by (clear -Gsp RS HK; lia).
  destruct Hpost as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6''
                     & m2 & E2 & MU2 & WM2 & MI2 & ST2 & AC2 & SW2 & _ & _).
  subst ms'. unfold BCMP_WRAP_K in MU2.
  assert (SUBb : sub_fp [(sp2 - 4560, sp2)] aWc).
  { intros x Hx. unfold reac_box_catalogue_match.aWc in Hx. cbn [outside] in Hx |- *. destruct Hx as (Hw & _).
    split; [clear -Hw Gsp; lia | exact I]. }
  assert (RM2 : rd_mono mc m2).
  { apply (rd_mono_list _ mc m2 MU2). constructor; [|constructor]. cbn [fst snd].
    intros y Hy. exact (rd_of_stk m2 _ _ ST2 y Hy). }
  pose proof FPg as FPc.
  destruct FPc as (DT0 & TS0 & C0 & T0 & DB0 & kk0 & HT0 & HTP0 & HPl0 & H880 & H960 & HCL0 & HFS0 & HApp0 & HWd0
                   & HDd0).
  rewrite Forall_forall in HCL0.
  assert (OB : forall x, x < S - 9136 \/ S - 96 <= x -> outside [(sp2 - 4560, sp2)] x).
  { intros x Hx. cbn [outside]. split; [clear -Hx Gsp; lia | exact I]. }
  assert (INV2 : cmInv_on fr sp2 jj nn m2).
  { apply (cm_inv_mu_on fr sp2 jj nn mc m2 [(sp2 - 4560, sp2)] INVk MU2 WM2 RM2 MI2 SUBb).
    - intros c Hc. apply (cm_cls_keep c mc m2 _ (HCL0 c Hc) MU2).
      + intros x Hx. apply OB. left. clear -Hx Hc FShi FSpos. unfold fs_hint in Hx.
        destruct Hc as [<-|[<-|[<-|[]]]]; cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia.
      + intros x Hx. apply OB. left. clear -Hx Hc FShi FSpos. unfold fs_flag, fs_M in Hx.
        destruct Hc as [<-|[<-|[<-|[]]]]; cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia.
    - apply (addr_munch _ mc m2 (sp2 - 8800) 8800 ADg MU2). intros k Hk.
      apply (fl_shadow_out [(sp2 - 4560, sp2)] (sp2 - 4560) sp2);
        [intros x Hx; exact Hx | clear -Gsp HHM; unfold HIGHMEM_BEG in *; lia |].
      apply rt_app_shadow. exact (acl_app_in mc (sp2 - 8800) 8800 k ADg Hk).
    - intros x Hx _ _. apply (fl_shadow_out [(sp2 - 4560, sp2)] (sp2 - 4560) sp2);
        [intros y Hy; exact Hy | clear -Gsp HHM; unfold HIGHMEM_BEG in *; lia |].
      apply rt_app_shadow. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END.
      right. pose proof HHM as HHMb. pose proof HAE as HAEb.
      unfold HIGHMEM_BEG, APPMEM_END in HHMb, HAEb. clear -Hx HHMb HAEb. lia.
    - intros x Hx. apply OB. right. clear -Hx. lia.
    - intros Enn x Hx. apply OB. left. clear -Hx Gc Enn. destruct Gc as [(E & _)|(_ & _ & _ & _ & E)]; lia. }
  replace (ret_pc (Z_to_bv 64 0x846e0)) with (Z_to_bv 64 0x846e0)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  step.
  rewrite cm_eqb0 by (clear -VR; lia).
  destruct (Z.eqb_spec v 0) as [V0|V0]; cbv iota.
  - eapply KH; [| exact INV2].
    apply cm_want_hit; [exact G | exact Hi | symmetry; apply MM; exact V0 | exact Hnd].
  - assert (Hne : nth i DECLS [] <> cm_blk fb) by (intros Hq; apply V0; apply MM; symmetry; exact Hq).
    assert (SHlo : 0 <= shadow_addr fr).
    { unfold shadow_addr. assert (D : 0 <= fr / 8) by (apply Z.div_pos; clear -FRpos; lia).
      unfold ASAN_K. clear -D. lia. }
    assert (SHhi : shadow_addr fr + 24 <= 2 ^ 64).
    { unfold shadow_addr, ASAN_K. clear -FRpos FRhi RS. Z.div_mod_to_equations. lia. }
    assert (FSW' : forall k, 0 <= k < 24 -> wview rsegs m (wa (shadow_addr fr + k)) <> None) by exact FSW.
    clear FSW.
    pose proof INV2 as INV2k.
    destruct INV2 as (_ & MUa & WMa & _).
    clear MUa MUg MU2.
    assert (MUh : munch (cmHF fr) m2 m2) by apply munch_refl.
    assert (WMh : wmono rsegs m2 m2) by apply wmono_refl.
    assert (RMh : rd_mono m2 m2) by apply rd_mono_refl.
    unfold reac_box_catalogue_match.cmHF in MUh.
    cm_wst (shadow_addr fr + 14) 1%nat. step. store_done.
    cm_wst (shadow_addr fr + 15) 1%nat. step. store_done.
    cm_wst (shadow_addr fr + 16) 1%nat. step. store_done.
    cm_wst (shadow_addr fr + 17) 1%nat. step. store_done.
    pose proof (cm_inv_step_on fr sp2 jj nn m2 _ INV2k MUh WMh RMh MI2) as INV3.
    step. step. step.
    rewrite cm_eqb_lit by (clear -Hi; lia).
    destruct (Z.eqb_spec (11 - Z.of_nat i + -1) 0) as [K0|K0]; cbn [negb]; cbv iota.
    + eapply KN; [| exact INV3].
      apply cm_want_none. intros j Hj.
      destruct (Nat.eq_dec j i) as [->|Hji]; [exact Hne | apply Hnd; clear -K0 Hj Hji; lia].
    + assert (HS11 : (i + 1 < 11)%nat).
      { destruct (Nat.ltb_spec i 10) as [Hlt|Hge]; [clear -Hlt; lia|].
        exfalso. apply K0. replace i with 10%nat by (clear -Hge Hi; lia). vm_compute. reflexivity. }
      eapply (cm_lh_eq_on (i + 1)%nat Q (KL HS11));
        [ f_equal; clear; lia | f_equal; clear; lia | exact G | | exact INV3 ].
      intros j Hj. destruct (Nat.eq_dec j i) as [->|Hji]; [exact Hne | apply Hnd; clear -Hj Hji; lia].
Qed.


(* The whole run after the gate: by downward induction on the rows left, every loop head of a row i < 11 reaches Q
   (cm_model_on, then cm_bcmp_on, then the next row), so the reac_ctrl_parse call reaches Q (cm_parse_on). *)
Lemma cm_loop_on : forall Q, cmNone_on Q -> cmHit_on Q -> forall k i, (i + k = 11)%nat -> (i < 11)%nat -> cmLH_on i Q.
Proof.
  intros Q KN KH k. induction k as [|k IH]; intros i Hik Hi; [clear -Hik Hi; lia|].
  apply (cm_model_on i Q Hi). apply (cm_bcmp_on i Q Hi); [| exact KN | exact KH].
  intros Hs. apply (IH (i + 1)%nat); clear -Hik Hs; lia.
Qed.


Lemma cm_calls_on : forall Q, cmNone_on Q -> cmHit_on Q -> cmPB_on Q.
Proof. intros Q KN KH. apply cm_parse_on; [apply (cm_loop_on Q KN KH 11 0); clear; lia | exact KN]. Qed.



(* ============================ (e) the no-match join, the row-match tail and the exit ============================ *)

(* The contract's post: the result in a0, sp and the callee-saved registers restored, and the memory facts the
   caller is given (the writes inside the window, the class-0/1/2 side-stack bytes and the window's shadow). *)
Definition cmPost_on : machine_state -> Prop := fun ms' =>
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch ([(S - 9136, S)] ++ fp_w [0%nat; 1%nat; 2%nat] FS ++ [(shadow_addr (S - 9136), shadow_addr S)]) m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (S - 9136) S /\
    asan_cells m' /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m') /\ addressable m' (S - 9136) 9136 /\
    fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (S - 9136) S (reac_box_catalogue_match_W S)
      (reac_box_catalogue_match_D f len) /\
    reac_box_catalogue_match_tls m' (bv_unsigned tp) FS (S - 9136) S.


Ltac tcell DJ sel :=
  eapply fl_bytes; [eassumption | eassumption |
    let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
    rewrite ?length_app, ?length_le8, ?length_le4, ?length_le1 in Hx; cbn [length] in Hx;
    eapply fl_dj_out; [exact DJ | cbn [fp_tls In]; sel; reflexivity | lia] ].


(* One store of the shadow byte k of the frame: the memory facts the exit carries are moved across it and the
   24-byte shadow list keeps its value with that byte set to 0 (0xf5 for shstf, a released side-stack frame). *)
Ltac shst fr0 mc0 k :=
  lazymatch goal with
  | [ SHIN : forall kk, _ -> in_shadow (shadow_addr fr0 + kk),
      WMc : wmono rsegs mc0 ?mcur,
      SRcur : srw_post ?mcur,
      FKc : cmFK fr0 _ _ _,
      Jmicur : mem_inv rsegs ?mcur,
      MUc : munch ?W mc0 ?mcur,
      BSH : bytes_at rsegs ?mcur (shadow_addr fr0) ?cs,
      STwcur : stk rsegs ?mcur (S - 9136) S,
      Lcs : length ?cs = 24%nat
      |- evt _ _ (MS _ _ _ _ _ ?mcur _) ] =>
    let SOK := fresh "SOK" in
    assert (SOK : store_ok rsegs mcur (wa (shadow_addr fr0 + k)) 1 = true)
      by (apply (cm_sh_sok_on cmR mcur); [exact (SRcur cmR SR_on) |
          apply (cm_fr_sh_R fr0 _ _ _ k FKc); intros; lia | apply SHIN; lia]);
    step;
    apply (wmono_write rsegs mc0 mcur (wa (shadow_addr fr0 + k)) (le1 (Z_to_bv 64 0))) in WMc;
    apply (cm_post_srw_write mcur (wa (shadow_addr fr0 + k)) (le1 (Z_to_bv 64 0))) in SRcur;
    apply (mem_inv_store rsegs mcur (wa (shadow_addr fr0 + k)) (le1 (Z_to_bv 64 0))) in Jmicur;
      [| rewrite length_le1; exact SOK];
    apply (stk_write rsegs mcur (S - 9136) S (shadow_addr fr0 + k) (le1 (Z_to_bv 64 0))) in STwcur;
      [| lia | rewrite length_le1; lia];
    apply (munch_write W mc0 mcur (shadow_addr fr0 + k) (le1 (Z_to_bv 64 0))) in MUc;
      [| lia | rewrite length_le1; lia | rewrite length_le1; cbn [inside]; right; left; split; lia];
    let B2 := fresh "BSHn" in
    pose proof (bytes_at_write_inside rsegs mcur (shadow_addr fr0) cs k (le1 (Z_to_bv 64 0)) BSH ltac:(lia)
                 ltac:(rewrite length_le1, Lcs; lia)) as B2;
    let L2 := fresh "Lcsn" in
    assert (L2 : length (upd_bytes cs (Z.to_nat k) (le1 (Z_to_bv 64 0))) = 24%nat)
      by (rewrite upd_bytes_length; [exact Lcs | rewrite length_le1, Lcs; lia]);
    clear BSH Lcs SOK; rename B2 into BSH; rename L2 into Lcs
  end.


Ltac shstf fr0 mc0 k :=
  lazymatch goal with
  | [ SHIN : forall kk, _ -> in_shadow (shadow_addr fr0 + kk),
      WMc : wmono rsegs mc0 ?mcur,
      SRcur : srw_post ?mcur,
      FKc : cmFK fr0 _ _ _,
      Jmicur : mem_inv rsegs ?mcur,
      MUc : munch ?W mc0 ?mcur,
      STwcur : stk rsegs ?mcur (S - 9136) S
      |- evt _ _ (MS _ _ _ _ _ ?mcur _) ] =>
    let SOK := fresh "SOK" in
    assert (SOK : store_ok rsegs mcur (wa (shadow_addr fr0 + k)) 1 = true)
      by (apply (cm_sh_sok_on cmR mcur); [exact (SRcur cmR SR_on) |
          apply (cm_fr_sh_R fr0 _ _ _ k FKc); intros; lia | apply SHIN; lia]);
    step;
    apply (wmono_write rsegs mc0 mcur (wa (shadow_addr fr0 + k)) (le1 (Z_to_bv 64 (-11)))) in WMc;
    apply (cm_post_srw_write mcur (wa (shadow_addr fr0 + k)) (le1 (Z_to_bv 64 (-11)))) in SRcur;
    apply (mem_inv_store rsegs mcur (wa (shadow_addr fr0 + k)) (le1 (Z_to_bv 64 (-11)))) in Jmicur;
      [| rewrite length_le1; exact SOK];
    apply (stk_write rsegs mcur (S - 9136) S (shadow_addr fr0 + k) (le1 (Z_to_bv 64 (-11)))) in STwcur;
      [| lia | rewrite length_le1; lia];
    apply (munch_write W mc0 mcur (shadow_addr fr0 + k) (le1 (Z_to_bv 64 (-11)))) in MUc;
      [| lia | rewrite length_le1; lia | rewrite length_le1; cbn [inside]; right; left; split; lia];
    clear SOK
  end.


(* The exit 0x84724: the frame's first word is set to the frame magic, then on the machine-stack arm the frame's 24
   shadow bytes are set to 0 (the frame is usable again) and on the side-stack arm its 32 shadow bytes to 0xf5
   (released) and the frame's in-use flag byte to 0; a0 = s3 = r, sp and the 12 saved registers are restored from
   [S - 96, S) and the function returns. *)
Lemma cm_exit_on : forall fr sp2 jj nn mc r
    (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
  r = want CM_T len fb -> cmInv_on fr sp2 jj nn mc ->
  evt rsegs cmPost_on
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 CA) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x84724) fc None mc (seg_rom rsegs)).
Proof.
  intros fr sp2 jj nn mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 Er INVk.
  pose proof (cm_stk_win_on fr sp2 jj nn mc INVk) as STw.
  pose proof (cm_stk_fr_on fr sp2 jj nn mc INVk) as STf.
  pose proof INVk as INV.
  destruct INV as (HFK & Jmu & Jwm & Jrm & Jmi & JAC & JSR & JFP & JTL & JAD & JAWX & SAV & FLG).
  pose proof HFK as HFKc.
  pose proof (fk_facts_on fr sp2 jj nn HFK) as (Fm8 & Fpos & Fhi & Fwv & Fap & Fsh & Fsp2).
  pose proof CA_facts as (CA32 & CAlo & CAhi). pose proof cm_CA_lo as (CAlo2 & CAhi2).
  pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'. pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). unfold FS_SIZE in FShi.
  pose proof RS as RSb.
  destruct HFK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)].
  - subst nn.
    assert (SOKfr : store_ok rsegs mc (wa fr) 8 = true) by
      (apply (wv_store_ok mc mc fr 8);
        [ intros i Hi; exact (stk_wv mc fr (fr + 192) (fr + i) STf ltac:(lia))
        | apply wmono_refl | lia | lia ]).
    assert (SHIN : forall k, 0 <= k < 24 -> in_shadow (shadow_addr fr + k)).
    { intros k Hk. rewrite <- (cm_sh_add8 fr k Fm8). apply rt_app_shadow. apply Fap. lia. }
    assert (SBlo : 0 <= shadow_addr fr) by
      (pose proof (rt_shadow_bound (shadow_addr fr + 0) (SHIN 0 ltac:(lia))); lia).
    assert (SBhi : shadow_addr fr + 32 <= 2 ^ 64) by
      (pose proof (rt_shadow_bound (shadow_addr fr + 23) (SHIN 23 ltac:(lia))); lia).
    assert (OUTW : forall y, S - 9136 <= y < S -> ~ (fr <= y < fr + 192) ->
              outside [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 24)] (shadow_addr y)).
    { intros y Hy Hyf. pose proof (cmHF_sh_win_on fr sp2 jj 0 y HFKc Hy Hyf) as Ho.
      unfold reac_box_catalogue_match.cmHF in Ho. cbn [outside] in Ho |- *. destruct Ho as (_ & H2 & H3 & _).
      split; [clear -H2; lia | split; [exact H3 | exact I]]. }
    pose proof (wmono_refl rsegs mc) as WMc.
    pose proof (cm_post_srw_inv mc Jwm Jrm) as SRcur.
    pose proof Jmi as Jmicur.
    pose proof (munch_refl [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 24)] mc) as MUc.
    pose proof STw as STwcur.
    step. step. step.
    change (Z_to_bv 64 fr) with (wa fr).
    apply (wmono_write rsegs mc mc (wa fr) (le8 (Z_to_bv 64 1172321806))) in WMc.
    apply (cm_post_srw_write mc (wa fr) (le8 (Z_to_bv 64 1172321806))) in SRcur.
    apply (mem_inv_store rsegs mc (wa fr) (le8 (Z_to_bv 64 1172321806))) in Jmicur;
      [| rewrite length_le8; exact SOKfr].
    apply (munch_write _ mc mc fr (le8 (Z_to_bv 64 1172321806))) in MUc;
      [| lia | rewrite length_le8; lia | cbn [inside]; left; split; [lia | rewrite length_le8; lia]].
    apply (stk_write rsegs mc (S - 9136) S fr (le8 (Z_to_bv 64 1172321806))) in STwcur;
      [| lia | rewrite length_le8; lia].
    replace (if (0 =? 0)%Z then 0 else fr) with 0 by reflexivity.
    step. rewrite bv_eqb_refl. cbv iota.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      destruct (cm_rd_list m1 24 (shadow_addr fr) SBlo ltac:(lia)
        (fun i Hi => proj2 (SRcur cmR SR_on (shadow_addr fr + i)
          (cm_fr_sh_R fr sp2 jj 0 i HFKc ltac:(lia) ltac:(intros; lia) ltac:(intros; lia)) (SHIN i ltac:(lia))))) as (cs0 & Lcs & BSH) end.
    assert (LcsO : (24 = length cs0)%nat) by (symmetry; exact Lcs).
    shst fr mc 4. shst fr mc 5. shst fr mc 6. shst fr mc 7. shst fr mc 0. shst fr mc 1. shst fr mc 2. shst fr mc 3.
    shst fr mc 12. shst fr mc 13. shst fr mc 14. shst fr mc 15. shst fr mc 8. shst fr mc 9. shst fr mc 10. shst fr mc 11.
    shst fr mc 20. shst fr mc 21. shst fr mc 22. shst fr mc 23. shst fr mc 16. shst fr mc 17. shst fr mc 18. shst fr mc 19.
    assert (FRup : fr + 320 <= S) by lia.
    assert (SAFup : shadow_addr fr + 24 <= S - 96)
      by (unfold shadow_addr, ASAN_K in *; Z.div_mod_to_equations; lia).
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (SAVf : rw_cells rsegs mf (S - 96) cmSAVES)
        by (apply (rw_cells_transport rsegs _ mc mf (S - 96) cmSAVES SAV MUc WMc);
            cbn [disjoint_from cells_size csize]; split; [right; lia | split; [right; lia | exact I]]) end.
    clear SAV. unfold reac_box_catalogue_match.cmSAVES in SAVf. replace (S - 96) with (S + -96) in SAVf by lia.
    do 16 step.
    apply evt_done. unfold cmPost_on. subst r.
    unfold reac_box_catalogue_match.aWc, reac_box_catalogue_match.aXs in Jmu.
    exists u0, u1, u2, y1, y2, y3, y4, y5, y6, y7, u3, u4, u5, u6. eexists.
    assert (SUB : sub_fp [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 24)]
                    ([(S - 9136, S)] ++ fp_w [0%nat; 1%nat; 2%nat] FS
                       ++ [(shadow_addr (S - 9136), shadow_addr S)])).
    { intros x Hx. cbn [app outside] in Hx. destruct Hx as (Hx1 & Hx2).
      apply cm_out_app in Hx2. destruct Hx2 as (Hxfp & Hxsh).
      cbn [outside] in Hxsh. destruct Hxsh as (Hxsh & _).
      pose proof (acl_sh_ge fr (S - 9136) ltac:(lia)) as G1.
      pose proof (acl_sh_ge S (fr + 192) ltac:(lia)) as G2.
      replace (fr + 192) with (fr + 8 * 24) in G2 by lia.
      rewrite (cm_sh_add8 fr 24 Fm8) in G2.
      cbn [outside]. split; [| split; [| exact I]].
      - clear -Hx1 Fhi Fpos CAlo CAhi Ef. lia.
      - clear -Hxsh G1 G2. lia. }
    split; [reflexivity|].
    match goal with |- munch _ _ ?Mm /\ _ => set (M := Mm) in * end.
    split; [eapply (munch_trans _ m mc); [exact Jmu | eapply munch_weaken; [exact SUB | exact MUc]] |].
    split; [eapply (wmono_trans rsegs m mc); [exact Jwm | exact WMc] |].
    split; [exact Jmicur |].
    split; [exact STwcur |].
    split; [ eapply fl_asan_cells; [exact JAC | exact MUc |];
             intros x Hx; unfold RT_LO, RT_HI in Hx; cbn [outside];
             split; [ clear -Hx HHM' CAlo CAhi Ef Fhi; lia
                    | split; [ clear -Hx SBlo Fpos; unfold shadow_addr, ASAN_K in *;
                               Z.div_mod_to_equations; lia
                             | exact I ] ] |].
    split; [exact SRcur |].
    split.
    { symmetry in LcsO.
      assert (BSHf : bytes_at rsegs M (shadow_addr fr)
        (fold_left (fun l k => upd_bytes l k (le1 (Z_to_bv 64 0))) cm_ks cs0)) by exact BSH.
      assert (LF : length (fold_left (fun l k => upd_bytes l k (le1 (Z_to_bv 64 0))) cm_ks cs0) = 24%nat)
        by exact Lcs.
      assert (COV : forall q, 0 <= q < 24 -> mrd rsegs M (wa (shadow_addr fr + q)) = Some (Z_to_bv 8 0)).
      { intros q Hq. destruct BSHf as (_ & _ & HBf).
        specialize (HBf (Z.to_nat q) ltac:(rewrite LF; lia)).
        rewrite Z2Nat.id in HBf by lia. rewrite HBf.
        rewrite (cm_nth_fold1 (le1 (Z_to_bv 64 0)) cm_ks (Z.to_nat q) cs0 eq_refl
                   ltac:(rewrite LcsO; lia) ltac:(intros kk Hkk; rewrite LcsO; apply cm_ks_bound; exact Hkk)).
        destruct (in_dec Nat.eq_dec (Z.to_nat q) cm_ks) as [_|Hn]; [reflexivity|].
        exfalso; apply Hn; apply cm_ks_cover; lia. }
      split; [lia | split; [lia | split; [unfold APPMEM_END; lia |]]].
      intros i Hi.
      destruct (Z_lt_le_dec (S - 9136 + i) fr) as [Lo|Lo];
        [| destruct (Z_lt_le_dec (S - 9136 + i) (fr + 192)) as [Inr|Hi2]].
      - exact (cm_ab_keep _ mc M _ (JAWX (S - 9136 + i) ltac:(lia) ltac:(lia)) MUc
                 (OUTW (S - 9136 + i) ltac:(lia) ltac:(lia))).
      - split; [replace (S - 9136 + i) with (fr + (S - 9136 + i - fr)) by lia; apply Fap; lia |].
        exists (Z_to_bv 8 0). split.
        + replace (shadow_addr (S - 9136 + i)) with (shadow_addr fr + (S - 9136 + i - fr) / 8).
          2:{ rewrite <- (cm_sh_div fr (S - 9136 + i - fr) Fm8). f_equal. lia. }
          apply COV. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
        + unfold shadow_ok. left. vm_compute. reflexivity.
      - exact (cm_ab_keep _ mc M _ (JAWX (S - 9136 + i) ltac:(lia) ltac:(lia)) MUc
                 (OUTW (S - 9136 + i) ltac:(lia) ltac:(lia))). }
    assert (SG1 : shadow_addr (S - 9136) <= shadow_addr fr) by (apply acl_sh_ge; lia).
    assert (SG2 : shadow_addr fr + 24 <= shadow_addr S).
    { pose proof (acl_sh_ge S (fr + 192) ltac:(lia)) as G.
      replace (fr + 192) with (fr + 8 * 24) in G by lia. rewrite (cm_sh_add8 fr 24 Fm8) in G. exact G. }
    assert (BEL : forall x, FS <= x < FS + FS_SIZE ->
               outside [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 24)] x).
    { intros x Hx. unfold FS_SIZE in Hx. cbn [outside]. split; [| split; [| exact I]].
      - clear -Hx FShi Fpos Fhi CAlo CAhi Ef. lia.
      - intros [A B]. pose proof (SHIN (x - shadow_addr fr) ltac:(lia)) as HSx.
        replace (shadow_addr fr + (x - shadow_addr fr)) with x in HSx by lia.
        apply (acl_app_not_shadow x); [apply FSapp; unfold FS_SIZE; lia | exact HSx]. }
    split.
    { destruct JFP as (DT & TS & C & T & DB & kk & HTx & HTP & HP & H88 & H96 & HCL & HFSb & HAb & HWd & HDd).
      pose proof (JTL DT TS C T DB kk HTx) as JTLi.
      assert (DJ : fp_dj [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 24)]
                     (fp_tls (bv_unsigned tp) DT TS C T DB kk)).
      { pose proof HWd as HW'. unfold fp_dj in HW'. apply Forall_inv in HW'.
        apply Forall_app in HW' as [HWtls _].
        constructor; [| constructor; [| constructor]].
        - eapply Forall_impl; [| exact HWtls]. intros [a b] Hd. unfold ly_dj in *; cbn [fst snd] in *.
          clear -Hd Fhi Fpos CAlo CAhi Ef. lia.
        - unfold fp_dj in JTLi. eapply Forall_impl; [| exact JTLi]. intros [a b] Hd.
          unfold reac_box_catalogue_match.aXs in Hd. apply Forall_app in Hd as [_ Hd]. apply Forall_inv in Hd.
          unfold ly_dj in *; cbn [fst snd] in *. clear -Hd SG1 SG2. lia. }
      exists DT, TS, C, T, DB, kk.
      split; [eapply cm_tls_cells; [exact HTx | exact MUc | exact DJ]|].
      split; [eapply fl_bytes; [exact HTP | exact MUc | intros x Hx; rewrite length_le8 in Hx;
               eapply fl_dj_out; [exact DJ | cbn [fp_tls In]; do 2 right; left; reflexivity | lia]]|].
      split; [unfold fs_place in *; destruct HP as (P1 & P2 & P3 & P4 & P5);
               split; [exact P1|]; split; [exact P2|]; split; [exact P3|]; split; [exact P4|];
               eapply (stk_transport rsegs _ mc M FS (FS + FS_SIZE));
                 [exact P5 | exact MUc | exact WMc | intros x Hx; left; apply BEL; exact Hx]|].
      split; [eapply fl_bytes; [exact H88 | exact MUc | intros x Hx; rewrite length_le8 in Hx; apply BEL;
               unfold FS_SIZE; lia]|].
      split; [eapply fl_bytes; [exact H96 | exact MUc | intros x Hx; cbn [length] in Hx; apply BEL;
               unfold FS_SIZE; lia]|].
      split; [exact (Forall_impl _ (fun c Hc => fl_cls _ mc M FS c BEL MUc Hc) HCL)|].
      split; [exact HFSb|]. split; [exact HAb|]. split; [exact HWd | exact HDd]. }
    intros DT TS C T DB k HTM.
    destruct JFP as (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd & _).
    pose proof (JTL DT0 TS0 C0 T0 DB0 k0 HT0) as JTLi0.
    assert (DJ0 : fp_dj [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 24)]
                   (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0)).
    { pose proof HWd as HW'. unfold fp_dj in HW'. apply Forall_inv in HW'.
      apply Forall_app in HW' as [HWtls _].
      constructor; [| constructor; [| constructor]].
      - eapply Forall_impl; [| exact HWtls]. intros [a b] Hd. unfold ly_dj in *; cbn [fst snd] in *.
        clear -Hd Fhi Fpos CAlo CAhi Ef. lia.
      - unfold fp_dj in JTLi0. eapply Forall_impl; [| exact JTLi0]. intros [a b] Hd.
        unfold reac_box_catalogue_match.aXs in Hd. apply Forall_app in Hd as [_ Hd]. apply Forall_inv in Hd.
        unfold ly_dj in *; cbn [fst snd] in *. clear -Hd SG1 SG2. lia. }
    assert (Hc : Forall (fun d => forall x, fst d <= x < snd d ->
                   outside [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 24)] x)
                 (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0)).
    { apply Forall_forall. intros [a b] Hin x Hx. eapply fl_dj_out; [exact DJ0 | exact Hin | cbn [fst snd] in Hx; lia]. }
    destruct (fl_tls_same mc M _ (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HTM MUc Hc)
      as (E1 & E2 & E3 & E4 & E5 & E6).
    subst DT0 TS0 C0 T0 DB0 k0. exact JTLi0.
  - subst nn.
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
    { intros k Hk. rewrite <- (cm_sh_add8 fr k Fm8). apply rt_app_shadow. apply FSapp.
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
      - apply (sh_out_app (shadow_addr y) fr (fr + 8) Hsh).
        intros z Hz. apply FSapp. unfold FS_SIZE. lia.
      - pose proof (acl_sh_ge y (fr + 8 * 32) ltac:(lia)) as G.
        rewrite (cm_sh_add8 fr 32 Fm8) in G. lia.
      - apply (sh_out_app (shadow_addr y) (fs_flag FS 2 jj) (fs_flag FS 2 jj + 1) Hsh).
        intros z Hz. apply FSapp. unfold FS_SIZE. lia. }
    pose proof (wmono_refl rsegs mc) as WMc.
    pose proof (cm_post_srw_inv mc Jwm Jrm) as SRcur.
    pose proof Jmi as Jmicur.
    pose proof (munch_refl [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
                            (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] mc) as MUc.
    pose proof STw as STwcur.
    step. step. step.
    change (Z_to_bv 64 fr) with (wa fr).
    apply (wmono_write rsegs mc mc (wa fr) (le8 (Z_to_bv 64 1172321806))) in WMc.
    apply (cm_post_srw_write mc (wa fr) (le8 (Z_to_bv 64 1172321806))) in SRcur.
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
    shstf fr mc 4. shstf fr mc 5. shstf fr mc 6. shstf fr mc 7. shstf fr mc 0. shstf fr mc 1. shstf fr mc 2. shstf fr mc 3.
    shstf fr mc 12. shstf fr mc 13. shstf fr mc 14. shstf fr mc 15. shstf fr mc 8. shstf fr mc 9. shstf fr mc 10. shstf fr mc 11.
    shstf fr mc 20. shstf fr mc 21. shstf fr mc 22. shstf fr mc 23. shstf fr mc 16. shstf fr mc 17. shstf fr mc 18. shstf fr mc 19.
    shstf fr mc 28. shstf fr mc 29. shstf fr mc 30. shstf fr mc 31. shstf fr mc 24. shstf fr mc 25. shstf fr mc 26. shstf fr mc 27.
    specialize (FLG eq_refl).
    pose proof JFP as JFPc.
    destruct JFPc as (DTx & TSx & Cx & Tx & DBx & kkx & _ & _ & HPfs & _ & _ & _ & _ & _ & _ & _).
    destruct HPfs as (FSP1 & FSP2 & FSP3 & FSP4 & FSPstk).
    match goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
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
        by (repeat (apply stk_write; [| lia | rewrite ?length_le1, ?length_le8; lia]); exact FSPstk) end.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m1 := mm) in * end.
    step.
    change (Z_to_bv 64 (fs_flag FS 2 jj)) with (wa (fs_flag FS 2 jj)).
    apply (wmono_write rsegs mc m1 (wa (fs_flag FS 2 jj)) (le1 (Z_to_bv 64 0))) in WMc.
    apply (cm_post_srw_write m1 (wa (fs_flag FS 2 jj)) (le1 (Z_to_bv 64 0))) in SRcur.
    apply (mem_inv_store rsegs m1 (wa (fs_flag FS 2 jj)) (le1 (Z_to_bv 64 0))) in Jmicur;
      [| rewrite length_le1; exact SOKfl].
    apply (stk_write rsegs m1 (S - 9136) S (fs_flag FS 2 jj) (le1 (Z_to_bv 64 0))) in STwcur;
      [| unfold FS_SIZE in *; lia | rewrite length_le1; lia].
    apply (munch_write _ mc m1 (fs_flag FS 2 jj) (le1 (Z_to_bv 64 0))) in MUc;
      [| unfold FS_SIZE in *; lia | rewrite length_le1; lia
       | rewrite length_le1; cbn [inside]; right; right; left; split; lia].
    apply (stk_write rsegs m1 FS (FS + FS_SIZE) (fs_flag FS 2 jj) (le1 (Z_to_bv 64 0))) in STfs1;
      [| unfold FS_SIZE in *; lia | rewrite length_le1; lia].
    clearbody m1.
    step.
    assert (SAFup : shadow_addr fr + 40 <= S - 96)
      by (unfold shadow_addr, ASAN_K in *; Z.div_mod_to_equations; lia).
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (SAVf : rw_cells rsegs mf (S - 96) cmSAVES)
        by (apply (rw_cells_transport rsegs _ mc mf (S - 96) cmSAVES SAV MUc WMc);
            cbn [disjoint_from cells_size csize];
            split; [right; lia | split; [right; lia | split; [right; lia | exact I]]]) end.
    clear SAV. unfold reac_box_catalogue_match.cmSAVES in SAVf. replace (S - 96) with (S + -96) in SAVf by lia.
    do 17 step.
    apply evt_done. unfold cmPost_on. subst r.
    unfold reac_box_catalogue_match.aWc, reac_box_catalogue_match.aXs in Jmu.
    exists u0, u1, u2, y1, y2, y3, y4, y5, y6, y7, u3, u4, u5, u6. eexists.
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
    { pose proof (cm_sh_add8 fr 32 Fm8) as E. replace (fr + 8 * 32) with (fr + 256) in E by lia. rewrite <- E.
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
    split; [reflexivity|].
    match goal with |- munch _ _ ?Mm /\ _ => set (M := Mm) in * end.
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
    assert (RDfl : mrd rsegs M (wa (fs_flag FS 2 jj)) = Some (Z_to_bv 8 0)).
    { change (mrd rsegs (write_to_mem m1 (wa (fs_flag FS 2 jj)) (le1 (Z_to_bv 64 0))) (wa (fs_flag FS 2 jj))
              = Some (Z_to_bv 8 0)).
      pose proof (bytes_at_write_same rsegs m1 (fs_flag FS 2 jj) (le1 (Z_to_bv 64 0)) ltac:(lia)
                    ltac:(rewrite length_le1; unfold FS_SIZE in *; lia)) as BW.
      destruct BW as (_ & _ & BW). specialize (BW 0%nat ltac:(rewrite length_le1; lia)).
      replace (fs_flag FS 2 jj + Z.of_nat 0) with (fs_flag FS 2 jj) in BW by lia.
      rewrite BW. reflexivity. }
    assert (DJall : forall DT TS C T DB kk, asan_tls_cells mc (bv_unsigned tp) DT TS C T DB kk ->
              fp_dj [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
                     (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)]
                    (fp_tls (bv_unsigned tp) DT TS C T DB kk)).
    { intros DT TS C T DB kk HTx. pose proof (JTL DT TS C T DB kk HTx) as JTLi. unfold reac_box_catalogue_match.aXs in JTLi.
      constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd].
      - apply (cm_dj_in _ _ (fs_frame FS 2 0) (fs_frame FS 2 (fs_M 2)) fr (fr + 8) JTLi);
          [apply in_or_app; left; exact INframe | destruct FRin; lia | destruct FRin; lia].
      - apply (cm_dj_in _ _ (shadow_addr (fs_frame FS 2 0)) (shadow_addr (fs_frame FS 2 (fs_M 2)))
                 (shadow_addr fr) (shadow_addr fr + 32) JTLi); [apply in_or_app; left; exact INsh | lia | lia].
      - apply (cm_dj_in _ _ (fs_flag FS 2 0) (fs_flag FS 2 0 + fs_M 2) (fs_flag FS 2 jj) (fs_flag FS 2 jj + 1)
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
      split; [eapply cm_tls_cells; [exact HTx | exact MUc | exact DJ]|].
      split; [eapply fl_bytes; [exact HTP | exact MUc | intros x Hx; rewrite length_le8 in Hx;
               eapply fl_dj_out; [exact DJ | cbn [fp_tls In]; do 2 right; left; reflexivity | lia]]|].
      split; [unfold fs_place in *; destruct HP as (P1 & P2 & P3 & P4 & P5);
               split; [exact P1|]; split; [exact P2|]; split; [exact P3|]; split; [exact P4 | exact STfs1]|].
      split; [eapply fl_bytes; [exact H88 | exact MUc | intros x Hx; rewrite length_le8 in Hx; apply BELh; lia]|].
      split; [eapply fl_bytes; [exact H96 | exact MUc | intros x Hx; cbn [length] in Hx; apply BELh; lia]|].
      split.
      { apply Forall_cons_iff in HCL as [HC0 HCL]. apply Forall_cons_iff in HCL as [HC1 HCL].
        apply Forall_cons_iff in HCL as [HC2 _].
        constructor; [exact (cm_cls_keep1 _ mc M 0%nat (fs_flag FS 2 jj) ltac:(lia) ltac:(lia) BELh MUc HC0)|].
        constructor; [exact (cm_cls_keep1 _ mc M 1%nat (fs_flag FS 2 jj) ltac:(lia) ltac:(lia) BELh MUc HC1)|].
        constructor; [exact (cm_cls_rel _ mc M jj Hj BELh MUc RDfl HC2) | constructor]. }
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


(* The no-match join 0x84704: the five shadow bytes 4 .. 8 of the frame (the parse buffer) are set to 0xf8 (the
   variable is out of scope), then the exit at 0x84724 with s3 = r = want CM_T len fb. *)
Lemma cm_tail_on : forall fr sp2 jj nn mc r
    (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 : word),
  r = want CM_T len fb -> cmInv_on fr sp2 jj nn mc ->
  evt rsegs cmPost_on
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 CA) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 r) z4 z5 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z8 z9 z10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x84704) fc None mc (seg_rom rsegs)).
Proof.
  intros fr sp2 jj nn mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z4 z5 z8 z9 z10 u3 u4 u5 u6 Er INVk.
  pose proof INVk as INV.
  destruct INV as (FK & MUg & WMg & RMg & MIg & ACg & SRg & FPg & TLg & ADg & AWXg & SVg & FLg).
  clear MUg.
  pose proof (fk_facts_on fr sp2 jj nn FK) as (FR8 & FRpos & FR192 & FW & FAP & FSW & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRhi).
  assert (SHlo : 0 <= shadow_addr fr).
  { unfold shadow_addr. assert (D : 0 <= fr / 8) by (apply Z.div_pos; clear -FRpos; lia).
    unfold ASAN_K. clear -D. lia. }
  assert (SHhi : shadow_addr fr + 24 <= 2 ^ 64).
  { unfold shadow_addr, ASAN_K. clear -FRpos FRhi RS. Z.div_mod_to_equations. lia. }
  assert (FSW' : forall k, 0 <= k < 24 -> wview rsegs m (wa (shadow_addr fr + k)) <> None) by exact FSW.
  clear FSW.
  assert (MUh : munch (cmHF fr) mc mc) by apply munch_refl.
  assert (WMh : wmono rsegs mc mc) by apply wmono_refl.
  assert (RMh : rd_mono mc mc) by apply rd_mono_refl.
  unfold reac_box_catalogue_match.cmHF in MUh.
  step.
  cm_wst (shadow_addr fr + 4) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 5) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 6) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 7) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 8) 1%nat. step. store_done.
  step.
  eapply (cm_exit_on fr sp2 jj nn _ r); [exact Er|].
  eapply cm_inv_step_on; [exact INVk | exact MUh | exact WMh | exact RMh | exact MIg].
Qed.


(* The no-row tail 0x84700: the result register s3 is set to 0 and the run joins the tail (cm_tail_on) with
   r = 0 = want CM_T len fb. *)
Lemma cm_none_holds_on : cmNone_on cmPost_on.
Proof.
  intros fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs3 rs4 rs5 rs8 rs9 rs10 rt3 rt4 rt5 rt6
    Hw INVk.
  step.
  exact (cm_tail_on fr sp2 jj nn mc 0 rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs4 rs5 rs8 rs9 rs10
           rt3 rt4 rt5 rt6 ltac:(symmetry; exact Hw) INVk).
Qed.


(* The row-match tail 0x84864: the model buffer's four shadow bytes 14 .. 17 are set to 0xf8 again and the run
   joins the tail (cm_tail_on) with r = the matching row's address. *)
Lemma cm_hit_holds_on : cmHit_on cmPost_on.
Proof.
  intros fr sp2 jj nn r mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs4 rs5 rs8 rs9 rs10 rt3 rt4 rt5 rt6
    Hw INVk.
  pose proof INVk as INV.
  destruct INV as (FK & MUg & WMg & RMg & MIg & ACg & SRg & FPg & TLg & ADg & AWXg & SVg & FLg).
  clear MUg.
  pose proof (fk_facts_on fr sp2 jj nn FK) as (FR8 & FRpos & FR192 & FW & FAP & FSW & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRhi).
  assert (SHlo : 0 <= shadow_addr fr).
  { unfold shadow_addr. assert (D : 0 <= fr / 8) by (apply Z.div_pos; clear -FRpos; lia).
    unfold ASAN_K. clear -D. lia. }
  assert (SHhi : shadow_addr fr + 24 <= 2 ^ 64).
  { unfold shadow_addr, ASAN_K. clear -FRpos FRhi RS. Z.div_mod_to_equations. lia. }
  assert (FSW' : forall k, 0 <= k < 24 -> wview rsegs m (wa (shadow_addr fr + k)) <> None) by exact FSW.
  clear FSW.
  assert (MUh : munch (cmHF fr) mc mc) by apply munch_refl.
  assert (WMh : wmono rsegs mc mc) by apply wmono_refl.
  assert (RMh : rd_mono mc mc) by apply rd_mono_refl.
  unfold reac_box_catalogue_match.cmHF in MUh.
  step.
  cm_wst (shadow_addr fr + 14) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 15) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 16) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 17) 1%nat. step. store_done.
  step.
  eapply (cm_tail_on fr sp2 jj nn _ r); [symmetry; exact Hw|].
  eapply cm_inv_step_on; [exact INVk | exact MUh | exact WMh | exact RMh | exact MIg].
Qed.


(* The catalogue-miss tail 0x84720: the result register s3 is set to 0 and the run reaches the exit (cm_exit_on). *)
Lemma cm_miss_holds_on : cmMiss_on cmPost_on.
Proof.
  intros fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 Hw INVk.
  step.
  exact (cm_exit_on fr sp2 jj nn mc 0 rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 (Z_to_bv 64 len) (wa ASAN_K)
           s8 s9 s10 rt3 rt4 rt5 rt6 ltac:(symmetry; exact Hw) INVk).
Qed.


(* The gate and everything after it: the gate's tests reach the parse call (cm_gate_on) or the miss tail
   (cm_miss_holds_on); the call and the row loop (cm_calls_on) end in the no-row tail (cm_none_holds_on) or the row-match
   tail (cm_hit_holds_on). *)
Lemma cm_body_on : cmKB_on cmPost_on.
Proof.
  intros fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 INVk.
  apply (cm_gate_on cmPost_on fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6);
    [ apply cm_calls_on; [exact cm_none_holds_on | exact cm_hit_holds_on]
    | exact cm_miss_holds_on
    | exact INVk ].
Qed.


End MatchOn.

(* reac_box_catalogue_match_c.v's reac_box_catalogue_match_contract_on (a Theorem Labs lane) from the `_on` contracts of the
   four callees: the entry run (cm_entry_on) reaches the gate in the state cmKB_on names; from there the gate, the
   reac_ctrl_parse call, the 11-row loop with the reac_box_model_block call and the bcmp wrapper, and the tails and
   the exit (cm_body_on) reach cmPost_on, the contract's post. *)
Theorem reac_box_catalogue_match_holds_on :
  reac_ctrl_parse_contract_on -> reac_box_model_block_contract_on -> bcmp_wrap_contract_on ->
  asan_stack_malloc_2_contract_on -> reac_box_catalogue_match_contract_on.
Proof.
  intros HPC HMB HBC HSM.
  unfold reac_box_catalogue_match_contract_on, REAC_BOX_CATALOGUE_MATCH, CM_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f len S FS fb Ea0 Ea1 Esp Rf Rlen RS S16 HK ST Hwin Hfb HF HT MI AC SR HHM HAE AW AFU AT ABC
    HBCMP HMEMCMP HGOT HCF254 HCF255 FP0 TLS0.
  subst a0 a1 sp.
  eapply cm_entry_on; try eassumption.
  apply cm_body_on; assumption.
Qed.

Print Assumptions reac_box_catalogue_match_holds_on.
Print Assumptions cm_entry_on.
Print Assumptions cm_parse_on.
Print Assumptions cm_model_on.
Print Assumptions cm_bcmp_on.
Print Assumptions cm_exit_on.
Print Assumptions cm_body_on.
