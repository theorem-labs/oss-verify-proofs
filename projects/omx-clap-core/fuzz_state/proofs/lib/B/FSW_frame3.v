(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFl3.v:106-108
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:383-389, 448-454, 493-498, 501-509 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:625-631 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:208-214, 227-233 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg10.v, with its module paths and module names changed; 2634 of its 2686 lines of code are new or changed and 608 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_parse_value.v; 152 of its 219 lines of code are new or changed and 2619 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_frame3.v from a working branch
   2767db174a0, same lemma names; imports point at lib/B's image files (YB1v, YB1w, YF0x, FSH_Base, FSH_Rt, FSPstat,
   FSH_Fn_reader and the other lib/B FSW files); the image-agnostic FSupoison, FSupoisonU, FSH_YC20, FSH_Gen stay lib/A's.
   rule 24: proves no function (kind: segment lemma). *)
(* The fake-frame kit steps of fs's ASan walks that need RELOC's FP-keyed core (the twin of FSW_frame.v, as FSW_K3.v is
   of FSW_K.v; when S0 merges RELOC each pair folds into one file). Owner: lane CRT (a Theorem Labs lane), per the walk-kit layout
   (a Theorem Labs lane 22:01Z, the FSW_frame / FSW_frame3 split agreed 23:27Z). A kit: no function's contract is proved here
   (rule 24).
   - fsw_after_callU_s0_own: the after-call state of a caller that still holds its fake frame (own = [(cid, pos)] from
     the grant to the epilogue flag store) and runs at a non-empty FP (fs's callers sit at FS_PSTAT_FP). Composed by
     FSW_K3's fsw_ajournal_sub4, whose FP relation has four arms: the callee's FP bytes are FP bytes in a live block,
     a temporary block, FP bytes of the image (the statics), or bytes of the caller's OWN frames (decode_spec_ff's lenp
     inside the caller's frame). The caller journal has its own start world W0 (from the second callee on,
     the journal starts at the entry world, not at the call world).
   - fsw_resume_after_stack_mallocU: the symbolic state at the return of __asan_stack_malloc_<cid>, the corollary of
     FSW_rres's fsw_resume_after_rtU_s0 with two extra regions (one stack slot, the granted frame with its flag word)
     and the frame's alignment fact.
   Port-from:
   - fsw_after_callU_s0_own: FSW_K.v fsw_after_callU_s0 (a working branch 770a908106b), the same proof with
     FSW_K3's fsw_ajournal_sub4 in place of ajournal_sub; it replaces the two-arm version removed from FSW_frame.v at
     a working branch fd08073092b. Shape asked by a Theorem Labs lane (starved) for all six fake-frame walks.
   - fsw_resume_after_stack_mallocU: a Theorem Labs lane's crcs_resume_sm (a working branch c4bfd3bc057,
     lib/A/FSH_check_reject_clean_starved.v:201-289), statement unchanged but for the crcs_ -> fsw_ names; the proof is
     now an instance of a Theorem Labs lane's fsw_resume_after_rtU_s0 (a working branch cd423a71760), keeping
     a Theorem Labs lane's region, disjointness and fact arguments for the slot and the frame.
   Rule 24 lookup outputs (index v5 built 2026-10-28T21:58:24Z, status read from a file, not through a pipe):
   `proof-index __asan_stack_malloc_3` exits 0 with 0 file(s) named for it and 382 by address, and lists
   omx-clap-core/fuzz_state as not address-searched; `git grep` over origin/main, origin/ossv/recipes, origin/ossv/candidates
   and origin/release/pau-projects-recipes (2026-10-28 ~22:10Z) returns no line for either lemma name. Donors are named
   above per lemma (FSW_K.v fsw_after_callU_s0; a Theorem Labs lane's crcs_resume_sm); the released plain / UBSan fuzz_state trees
   on ossv/recipes are the structural template. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v FSH_Base FSH_Rt FSW_K FSW_K3 FSW_rres FSW_frame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* the resume state after the grant: the s0 window (atom 8, chunks cs), one stack slot at atom nsl, and the granted frame
   at atom nF with its flag word (eflag) in the last 8 bytes *)
Definition fsw_resume_regions (lo hi : Z) (cs : list YP09.chunk) (nsl : nat) (slo shi : Z) (nF : nat) (eflag : sv)
  (cid : Z) : list YP09.region :=
  [YP09.mkRegion (Some 8%nat) lo hi lo hi cs;
   YP09.mkRegion (Some nsl) slo shi slo shi [];
   YP09.mkRegion (Some nF) 0 (fs_frame_bytes cid) 0 (fs_frame_bytes cid) [YP09.mkChunk (fs_frame_bytes cid - 8) (CVal 8 eflag)]].
Definition fsw_resume_ss (r lo hi : Z) (cs : list YP09.chunk) (nsl : nat) (slo shi : Z) (nF : nat) (eflag : sv)
  (cid : Z) : sstate :=
  mkSS r sr_atoms (fsw_resume_regions lo hi cs nsl slo shi nF eflag cid) None
    (mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (nF, mkAF 4096 (2 ^ 47) 5)] [] []).

Section f3. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

Lemma fsw_after_callU_s0_own : forall STK sp0 FP ly S U W0 mem md own lyc Sc Uc W memC mdC k STKc FPc sp1 regsC
  ly' S' U' W' regs' mem' md' kc extra cs r lo hi,
  ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison Uc memC) mdC k ->
  ARU tfibsegs B lyc Sc Uc W memC mdC ->
  ajournal tfibsegs B STKc sp1 FPc lyc Sc W (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem') md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (forall a, inFP FPc a ->
     (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
     in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
     (inFP FP a /\ in_img tfibsegs a) \/
     in_frames lyc own a) ->
  aregs_preserved regsC regs' -> spZ regsC = sp1 ->
  YK11.getr regs' 8%bv = Z_to_bv 64 sp0 ->
  sp0 - STK <= sp1 - STKc -> sp1 <= sp0 -> sp0 - STK <= sp0 + lo -> sp1 <= sp0 + lo -> lo <= hi -> hi <= 0 ->
  regions_wf [fs_ret_s0_region lo hi cs] = true ->
  Forall (fun c => lo <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= hi) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' extra) (mrestrict (w_H W) memC) sp0) cs ->
  ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' (k + kc) /\
  st_ok tfibsegs (Ereg regs' extra) (fss_ret_s0 r lo hi cs)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros STK sp0 FP ly S U W0 mem md own lyc Sc Uc W memC mdC k STKc FPc sp1 regsC ly' S' U' W' regs' mem' md' kc
  extra cs r lo hi HJ HARUc HJc OK' PO' HFP HP Hsp Hs0 Hlo1 Hhi1 Hwin Habove Hlohi Hhi0 Hwf Hin Hcs.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HJ2 : ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' (k + kc)).
{ exact (fsw_ajournal_sub4 B STK sp0 FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison Uc memC) mdC k STKc sp1
    FPc [] ly' S' W' (unpoison U' mem') md' kc HJ HJc ltac:(lia) ltac:(lia) HFP). }
split; [exact HJ2|].
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact HAR2 | split; [exact OK' | exact PO']]).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
assert (E8 : bv_unsigned (ew (Ereg regs' extra) 8) = sp0)
  by (rewrite (ew_Ereg_nat regs' extra 8 8%bv eq_refl), Hs0; apply wz; lia).
rewrite restrict_mkst_fx. unfold fss_ret_s0. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor]. unfold region_ok, fs_ret_s0_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E8. split; [lia|]. split; [lia|]. split.
  + intros o Ho. apply (apresent_writable tfibsegs).
    apply (fsw_apresent_unpoison B ly' S' U' W' mem' md' _ HARU'); [lia|]. apply Hpres2. lia.
  + apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hin c Hc) as Hci.
    pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
    apply (chunk_ok_mbyte _ (mrestrict (w_H W) memC)); [|exact Hck].
    destruct Hci as [Hc0 Hc1]. intros i Hi. apply (mbyte_of_aview tfibsegs).
    rewrite <- (fsw_aview_unpoison_high B ly' S' U' W' mem' md' _ HARU') by lia.
    rewrite <- (fsw_aview_unpoison_high B lyc Sc Uc W memC mdC _ HARUc) by lia.
    apply F1; [lia | intros Hx; lia].
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E8.
  change (2 ^ 4) with 16. split; [|exact I]. split; [lia | split; [exact Hal16 | lia]].
Qed.

Lemma fsw_resume_after_stack_mallocU : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc S2 U (W : world tfibsegs) memT mdc
  mem2 md2 k cid pos sp1 regs2 extra r lo hi cs nsl slo shi nF eflag,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 ((cid, pos) :: own) lyc S2 W (unpoison U mem2) md2 k ->
  ARU tfibsegs B lyc S2 U W mem2 md2 -> ARU tfibsegs B lyc Sc U W memT mdc ->
  acall_kept tfibsegs B lyc Sc W (unpoison U memT) W (unpoison U mem2) (sp1 - ESTACK) sp1 (fun _ => False) ->
  In (cid, pos) (frames S2) -> 0 <= cid ->
  bv_unsigned (ew (Ereg regs2 extra) 8) = sp0 -> bv_unsigned (ew (Ereg regs2 extra) nsl) = sp1 ->
  bv_unsigned (ew (Ereg regs2 extra) nF) = frame_addr lyc cid pos ->
  sv_denot (Ereg regs2 extra) eflag = Z_to_bv 64 (flag_addr lyc cid pos) ->
  rdword (aview tfibsegs (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) = Some (flag_addr lyc cid pos) ->
  lo <= hi <= 0 -> sp1 <= sp0 + lo -> slo <= shi -> sp1 + shi <= sp0 + lo -> sp0 - STK <= sp1 + slo ->
  regions_wf (fsw_resume_regions lo hi cs nsl slo shi nF eflag cid) = true ->
  Forall (fun c => lo <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= hi) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 extra) (mrestrict (w_H W) memT) sp0) cs ->
  st_ok tfibsegs (Ereg regs2 extra) (fsw_resume_ss r lo hi cs nsl slo shi nF eflag cid)
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc S2 U W memT mdc mem2 md2 k cid pos sp1 regs2 extra r lo hi cs nsl slo
  shi nF eflag HJ HARU2 HARUc Hkept Hin Hc0 E8 Esl EF Eflag Hflag Hlohi Hlo Hsl Hsh Hsw Hwf Hcin Hcs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (ARU_AR tfibsegs B lyc S2 U W mem2 md2 HARU2) as HAR2.
destruct (al_frames _ _ LAWS lyc S2 W (unpoison U mem2) md2 cid pos HAR2 Hin) as (Hal32 & _ & Hfp & _).
destruct (frames_bounds tfibsegs B LAWS lyc S2 W (unpoison U mem2) md2 cid pos HAR2 Hin) as (H4096 & Hfc & _).
destruct (al_flag _ _ LAWS lyc S2 W (unpoison U mem2) md2 cid pos HAR2 Hin) as (_ & _ & Hflapp & Hflc).
pose proof (fs_frame_bytes_pos cid Hc0) as Hfb.
destruct Hkept as (K1 & _).
(* s0 = sp0 as a register value, the form FSW_rres takes *)
assert (Es0 : YK11.getr regs2 8%bv = Z_to_bv 64 sp0).
{ pose proof E8 as E8'. rewrite (ew_Ereg_nat regs2 extra 8 8%bv eq_refl) in E8'. rewrite <- E8', Z_to_bv_bv_unsigned.
  reflexivity. }
set (F := frame_addr lyc cid pos) in *. set (FL := flag_addr lyc cid pos) in *.
assert (FL4096 : 4096 <= FL) by (unfold in_app in Hflapp; lia).
set (rslot := YP09.mkRegion (Some nsl) slo shi slo shi []).
set (rframe := YP09.mkRegion (Some nF) 0 (fs_frame_bytes cid) 0 (fs_frame_bytes cid)
  [YP09.mkChunk (fs_frame_bytes cid - 8) (CVal 8 eflag)]).
change (fsw_resume_ss r lo hi cs nsl slo shi nF eflag cid)
  with (fss_ret_s0_args r lo hi cs [rslot; rframe] [(nF, mkAF 4096 (2 ^ 47) 5)]).
apply (fsw_resume_after_rtU_s0 B STK sp0 FP ly S W0 mem0 md0 ((cid, pos) :: own) lyc S2 U W mem2 md2 k regs2 memT extra
  cs [rslot; rframe] [(nF, mkAF 4096 (2 ^ 47) 5)] r lo hi HJ HARU2 Es0).
- lia.
- lia.
- lia.
- exact Hwf.
- exact Hcin.
- exact Hcs.
- (* the s0 window's bytes are the same after the call: above the callee's ESTACK window, so acall_kept keeps them *)
  intros a Ha. apply (mbyte_of_aview tfibsegs).
  rewrite <- (fsw_aview_unpoison_high B lyc S2 U W mem2 md2 _ HARU2) by lia.
  rewrite <- (fsw_aview_unpoison_high B lyc Sc U W memT mdc _ HARUc) by lia.
  apply K1; lia.
- constructor; [|constructor; [|constructor]].
  + (* the stack slot: present after the call, inside the journal's window *)
    unfold region_ok, rslot. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Esl. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable tfibsegs).
    apply (fsw_apresent_unpoison B lyc S2 U W mem2 md2 _ HARU2); [lia|]. apply Hpres. lia.
  + (* the frame: present and not owned (AR_frames_law), its flag word the callee's rdword *)
    unfold region_ok, rframe. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite EF. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable tfibsegs).
      destruct (Hfp (F + o) ltac:(lia)) as (Hp & Hno).
      exact (fsw_apresent_notowned B lyc S2 U W mem2 md2 (F + o) HARU2 ltac:(lia) Hno Hp).
    * constructor; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs _ _ F (fs_frame_bytes cid - 8) 8 eflag FL Eflag); [cbn; lia | cbn; lia|].
      replace (F + (fs_frame_bytes cid - 8)) with (F + fs_frame_bytes cid - 8) by lia.
      exact (val_mem_of_rdword tfibsegs (w_H W) mem2 _ _ Hflag).
- apply pairwise_disjoint_of_extents. unfold fss_ret_s0_regs, fs_ret_s0_region, rslot, rframe, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E8, Esl, EF.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
- cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite EF. change (2 ^ 5) with 32.
  split; [lia | split; [exact Hal32 | lia]].
Qed.

(* ---- the after-call state of a fake-frame caller whose callee has a RAISED window top ----
   Every WRITER callee (put, indent, put_string, write_value, pj_write) states its post at a window top ot above the
   call sp (FSH_Fn_FORM 3a): the callee journal runs from sp1 with spZ regsC <= sp1 <= sp0, and the caller's s0 (its
   own entry sp, s0v) can lie INSIDE the callee's window. So the saved words at [s0v + lo, s0v + hi) are not kept by
   the callee journal's outside-window clause; only the callee post's `wkeep` keeps them, on the raw memory. The keep
   is therefore a premise, stated over mbyte of the raw memory so that wkeep discharges it with no unpoison bridge
   (WRITER, a Theorem Labs lane 22:46Z / 22:47Z). Otherwise as fsw_after_callU_s0_own. *)
Lemma fsw_after_callU_s0_ot : forall STK sp0 FP ly S U W0 mem md own lyc Sc Uc W memC mdC k STKc FPc sp1 regsC
  ly' S' U' W' regs' mem' md' kc extra cs r lo hi s0v,
  ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison Uc memC) mdC k ->
  ajournal tfibsegs B STKc sp1 FPc lyc Sc W (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem') md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (forall a, inFP FPc a ->
     (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
     in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/
     (inFP FP a /\ in_img tfibsegs a) \/
     in_frames lyc own a) ->
  aregs_preserved regsC regs' -> spZ regsC <= sp1 ->
  YK11.getr regs' 8%bv = Z_to_bv 64 s0v -> s0v mod 16 = 0 ->
  sp0 - STK <= sp1 - STKc -> sp1 <= sp0 ->
  sp0 - STK <= s0v + lo -> lo <= hi -> hi <= 0 -> s0v <= sp0 ->
  regions_wf [fs_ret_s0_region lo hi cs] = true ->
  Forall (fun c => lo <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= hi) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' extra) (mrestrict (w_H W) memC) s0v) cs ->
  (forall a, s0v + lo <= a < s0v + hi ->
     mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) memC) a) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' (k + kc) /\
  st_ok tfibsegs (Ereg regs' extra) (fss_ret_s0 r lo hi cs)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros STK sp0 FP ly S U W0 mem md own lyc Sc Uc W memC mdC k STKc FPc sp1 regsC ly' S' U' W' regs' mem' md' kc
  extra cs r lo hi s0v HJ HJc OK' PO' HFP HP Hsp Hs0 Hs0al Hlo1 Hhi1 Hwin Hlohi Hhi0 Hs0top Hwf Hin Hcs Hkeep.
pose proof asan_consts as (C1 & _ & C3 & _). pose proof ASAN_CEIL_range as (Hc1 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HJ2 : ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' (k + kc)).
{ exact (fsw_ajournal_sub4 B STK sp0 FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison Uc memC) mdC k STKc sp1
    FPc [] ly' S' W' (unpoison U' mem') md' kc HJ HJc ltac:(lia) ltac:(lia) HFP). }
split; [exact HJ2|].
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact HAR2 | split; [exact OK' | exact PO']]).
assert (E8 : bv_unsigned (ew (Ereg regs' extra) 8) = s0v)
  by (rewrite (ew_Ereg_nat regs' extra 8 8%bv eq_refl), Hs0; apply wz; unfold ASAN_CEIL in *; lia).
rewrite restrict_mkst_fx. unfold fss_ret_s0. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor]. unfold region_ok, fs_ret_s0_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E8. split; [unfold ASAN_CEIL in *; lia|]. split; [unfold ASAN_CEIL in *; lia|]. split.
  + intros o Ho. apply (apresent_writable tfibsegs).
    apply (fsw_apresent_unpoison B ly' S' U' W' mem' md' _ HARU'); [unfold ASAN_CEIL in *; lia|].
    apply Hpres2. lia.
  + apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hin c Hc) as Hci.
    pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
    apply (chunk_ok_mbyte _ (mrestrict (w_H W) memC)); [|exact Hck].
    destruct Hci as [Hcb0 Hcb1]. intros i Hi. apply Hkeep. lia.
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E8.
  change (2 ^ 4) with 16. split; [|exact I]. unfold ASAN_CEIL in *. split; [lia | split; [exact Hs0al | lia]].
Qed.

End f3.
