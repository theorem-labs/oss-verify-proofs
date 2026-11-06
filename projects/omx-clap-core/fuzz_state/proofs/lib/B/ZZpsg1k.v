(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: IMAGE B (fs.asan-ubsan) walk of parse_value 0x82fcc, stage lemmas. HEADER: see
   FSW_parse_value_holds.v (the composition into parse_value_spec k, the rule-24 line, the reuse search, the port
   sources, every pc walked and every report site). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/Prog/FSW_parse_value.v, with its module names and numbers changed; 1163 of its 1272 lines of code are new or changed and 1247 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan, image B) twin of lib/A/FSW_put_string.v at
   a working branch ca67007c8c2 (a Theorem Labs lane), and another Theorem Labs lane: same lemma names and statement shapes;
   imports point at lib/B's image files and walk kit (YB1v, YB1w, FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer,
   FSW_K, FSW_K3, FSW_ret, FSW_frame, FSW_frame3, FSW_rd, FSW_strkit and lib/B's put_string files); the
   image-agnostic FSupoison, FSupoisonU, FSupoisonStack, FSH_YC20, FSH_Gen and FSW_writer_model stay lib/A's.
   Every address, cut, branch, offset and register of put_string's own code is RE-MEASURED on image B
   (A_put_string 0x85fc8, 928 bytes; the neutral excerpt put_string.fuzz_state.asan-ubsan.s), never copied.
   rule 24: proves no function (kind: segment lemma). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_put_string.v; 99 of its 134 lines of code are new or changed and 1237 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan, image B) twin of lib/A/ZZpsg1k.v at
   a working branch ca67007c8c2 (a Theorem Labs lane), and another Theorem Labs lane: same lemma names and statement shapes;
   imports point at lib/B's image files and walk kit (YB1v, YB1w, FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer,
   FSW_K, FSW_K3, FSW_ret, FSW_frame, FSW_frame3, FSW_rd, FSW_strkit and lib/B's put_string files); the
   image-agnostic FSupoison, FSupoisonU, FSupoisonStack, FSH_YC20, FSH_Gen and FSW_writer_model stay lib/A's.
   Every address, cut, branch, offset and register of put_string's own code is RE-MEASURED on image B
   (A_put_string 0x85fc8, 928 bytes; the neutral excerpt put_string.fuzz_state.asan-ubsan.s), never copied.
   rule 24: proves no function (kind: segment lemma). *)
(* SCRATCH (a Theorem Labs lane): GENERIC helpers of put_string's put calls, image B (fs.asan-ubsan), split out of ZZpsg1.v so
   that the other segment parts can import them without SEG1's walk. Folded into FSW_put_string.v by a Theorem Labs lane.
   - ps_quote_src: the quote string PS_Q1 = 0x21240 ([34], FS_RO_STRS's 23rd entry) as put's source at any ARU state
     with the read-only view: the bytes (FSW_strkit.cstr_ok_kept_tbl, which needs fs_img_facts) and the table home.
     The same statement as a Theorem Labs lane's ps_quote_src (agreed 2026-10-29); this is the copy a Theorem Labs lane folds.
   - ps_heads_put: fs_heads and put's buffer-head premise at a put's RETURN, from the call's heads, put's uswap /
     bswap and put's wout_ok at the return. Neither relation alone gives them (a head of U at the old buffer's start
     survives uswap's first arm while bswap's third arm removes its block); the case analysis uses AR's block bounds
     (every block at 4096 or above), upoison_ok's heads inside blocks and U's pairwise disjointness
     (ZZpsmodel.psm_pw_once), and ZZpssep.pss_bswap_keep for the blocks that are not the buffer's. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v FSH_Base FSH_Rt FSPstat FSW_strkit FSW_put_string ZZpsmodel ZZpssep.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require
FSH_Fn_writer.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the quote string is FS_RO_STRS's 23rd entry *)
Lemma ps_q1_tbl : In (PS_Q1, [34]) FS_RO_STRS.
Proof. unfold FS_RO_STRS, PS_Q1. do 22 right. left. reflexivity. Qed.

Section K. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HIMG : fs_img_facts tfibsegs B.

(* ================= the quote string as put's source ================= *)
Lemma ps_quote_src : forall ly S U (W : world tfibsegs) mem md buf,
  ARU tfibsegs B ly S U W mem md -> arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  zbytes_at tfibsegs W mem PS_Q1 [34] /\ FSH_Fn_writer.wsrc_kept B tfibsegs ly S U W mem buf PS_Q1 [34] /\
  0 <= PS_Q1 /\ PS_Q1 + 1 <= alloc_ceiling.
Proof.
intros ly S U W mem md buf HARU HRO.
pose proof (cstr_ok_kept_tbl B ly S U W mem md PS_Q1 [34] HIMG HARU HRO (or_introl ps_q1_tbl))
  as ((Hg & _) & H4096 & Hceil & _).
split; [|split; [|split]].
- unfold zbytes_at. intros j Hj. cbn [length] in Hj.
  assert (j = 0%nat) as -> by lia. exact (Hg 0%nat ltac:(cbn; lia)).
- right; right; right. exists [34]. split; [exact ps_q1_tbl | exact (Nat.le_succ_diag_r _)].
- unfold PS_Q1. lia.
- cbn [length] in Hceil. lia.
Qed.

(* ================= fs_heads and the buffer head at a put's return ================= *)
Lemma ps_heads_put : forall lyc Sc U (W : world tfibsegs) memc mdc ly' S' U' (W' : world tfibsegs) mem' md'
    o buf buf' cap cap' failed' (text' : list Z),
  ARU tfibsegs B lyc Sc U W memc mdc -> fs_heads B lyc Sc U ->
  (cap = 0 -> buf = 0) -> (cap <> 0 -> In (buf - HEAD, HEAD) U) ->
  ARU tfibsegs B ly' S' U' W' mem' md' ->
  FSH_Fn_writer.wout_ok B tfibsegs ly' S' W' mem' o buf' cap' failed' text' ->
  FSH_Fn_writer.bswap (ablocks B lyc Sc) (ablocks B ly' S') buf buf' cap cap' ->
  FSH_Fn_writer.uswap U U' buf buf' cap ->
  fs_heads B ly' S' U' /\ (cap' <> 0 -> In (buf' - HEAD, HEAD) U').
Proof.
intros lyc Sc U W memc mdc ly' S' U' W' mem' md' o buf buf' cap cap' failed' text'
  HARU Hh Hc0 HHD HARU' HOUT' Hbs Hus.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B lyc Sc U W memc mdc HARU) as HAR.
pose proof (ARU_AR tfibsegs B ly' S' U' W' mem' md' HARU') as HAR'.
destruct HARU as (_ & (HUok & HUpw) & _).
destruct HARU' as (_ & (HUok' & _) & _).
assert (B4' : forall p n, In (p, n) (ablocks B ly' S') -> 4096 <= p)
  by (intros p n Hp; exact (proj1 (proj2 (al_blocks _ _ LAWS ly' S' W' (unpoison U' mem') md' p n HAR' Hp)))).
(* every head lies at 4096 or above: upoison_ok puts it inside a block *)
assert (U4 : forall r, In r U -> 4096 <= fst r).
{ intros r Hr. rewrite Forall_forall in HUok. destruct (HUok r Hr) as (_ & _ & _ & p & n & Hp & Hpr & _).
  pose proof (proj1 (proj2 (al_blocks _ _ LAWS lyc Sc W (unpoison U memc) mdc p n HAR Hp))). lia. }
assert (U4' : forall r, In r U' -> 4096 <= fst r).
{ intros r Hr. rewrite Forall_forall in HUok'. destruct (HUok' r Hr) as (_ & _ & _ & p & n & Hp & Hpr & _).
  pose proof (B4' p n Hp). lia. }
(* put's wout_ok at the return: the new buffer's block, and cap' = 0 -> buf' = 0 *)
assert (NB : cap' <> 0 -> In (buf' - HEAD, cap' + HEAD) (ablocks B ly' S')).
{ intros Hc. unfold FSH_Fn_writer.wout_ok in HOUT'.
  destruct HOUT' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [(E0 & _) | (_ & HRB & _)]);
    [exfalso; exact (Hc E0) | exact (proj1 HRB)]. }
assert (Z0' : buf' <> 0 -> cap' <> 0).
{ intros Hb Hc. unfold FSH_Fn_writer.wout_ok in HOUT'.
  destruct HOUT' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [(_ & E1 & _) | (_ & HRB & _)]);
    [exact (Hb E1) | destruct HRB as (_ & _ & Hn & _); lia]. }
assert (Hcap0' : 0 <= cap').
{ unfold FSH_Fn_writer.wout_ok in HOUT'. destruct HOUT' as (_ & _ & _ & _ & _ & (Hc & _) & _). exact Hc. }
assert (RQ : 16 <= req_size (cap' + HEAD)) by (pose proof (pss_req_ge (cap' + HEAD)); unfold HEAD in *; lia).
(* the new head, wherever uswap puts it *)
assert (NEW : 4096 <= buf' - HEAD ->
  exists m, In (buf' - HEAD, m) (ablocks B ly' S') /\ 16 <= req_size m).
{ intros H4. exists (cap' + HEAD). split; [|exact RQ].
  apply NB. apply Z0'. unfold HEAD in *. lia. }
(* an old head off the buffer's start keeps its block *)
assert (OLD : forall r, In r U -> fst r <> buf - HEAD ->
  snd r = 16 /\ exists m, In (fst r, m) (ablocks B ly' S') /\ 16 <= req_size m).
{ intros r Hr Hne. destruct (Hh r Hr) as (H16 & m & Hm & Hrm). split; [exact H16|].
  exists m. split; [exact (pss_bswap_keep _ _ buf buf' cap cap' _ _ Hbs Hm Hne) | exact Hrm]. }
destruct Hus as [(-> & ->) | [(U1 & U2 & EU & EU') | (Ec & EU')]].
- (* the heads stay, the buffer stays *)
  split.
  + intros r Hr. destruct (Z.eq_dec (fst r) (buf - HEAD)) as [E | E]; [|exact (OLD r Hr E)].
    destruct (Hh r Hr) as (H16 & _). split; [exact H16|].
    rewrite E. apply NEW. rewrite <- E. exact (U4 r Hr).
  + intros Hc. destruct (Z.eq_dec cap 0) as [Ec | Ec]; [|exact (HHD Ec)].
    exfalso. pose proof (B4' _ _ (NB Hc)) as Hb. rewrite (Hc0 Ec) in Hb. unfold HEAD in Hb. lia.
- (* the old head leaves, the new one joins at the end *)
  assert (NO : ~ In (buf - HEAD, HEAD) (U1 ++ U2)).
  { rewrite EU in HUpw. exact (psm_pw_once (buf - HEAD, HEAD) U1 U2 HUpw ltac:(cbn; unfold HEAD; lia)). }
  assert (IU : forall r, In r (U1 ++ U2) -> In r U).
  { intros r Hr. rewrite EU. apply in_app_or in Hr as [Hr | Hr]; apply in_or_app; [left | right; right]; exact Hr. }
  split.
  + intros r Hr. rewrite EU' in Hr. apply in_app_or in Hr as [Hr | Hr];
      [| apply in_app_or in Hr as [Hr | [Er | []]]].
    * destruct (Z.eq_dec (fst r) (buf - HEAD)) as [E | E];
        [|exact (OLD r (IU r (in_or_app _ _ _ (or_introl Hr))) E)].
      exfalso. destruct (Hh r (IU r (in_or_app _ _ _ (or_introl Hr)))) as (H16 & _).
      apply NO. destruct r as [r1 r2]. cbn [fst snd] in E, H16. subst r1 r2. unfold HEAD.
      apply in_or_app. left. exact Hr.
    * destruct (Z.eq_dec (fst r) (buf - HEAD)) as [E | E];
        [|exact (OLD r (IU r (in_or_app _ _ _ (or_intror Hr))) E)].
      exfalso. destruct (Hh r (IU r (in_or_app _ _ _ (or_intror Hr)))) as (H16 & _).
      apply NO. destruct r as [r1 r2]. cbn [fst snd] in E, H16. subst r1 r2. unfold HEAD.
      apply in_or_app. right. exact Hr.
    * subst r. cbn [fst snd]. split; [unfold HEAD; reflexivity|]. apply NEW.
      apply (U4' (buf' - HEAD, HEAD)). rewrite EU'. apply in_or_app. right. apply in_or_app. right. left. reflexivity.
  + intros _. rewrite EU'. apply in_or_app. right. apply in_or_app. right. left. reflexivity.
- (* cap = 0: the new head only joins *)
  split.
  + intros r Hr. rewrite EU' in Hr. apply in_app_or in Hr as [Hr | [Er | []]].
    * destruct (Z.eq_dec (fst r) (buf - HEAD)) as [E | E]; [|exact (OLD r Hr E)].
      exfalso. pose proof (U4 r Hr) as H4. rewrite E, (Hc0 Ec) in H4. unfold HEAD in H4. lia.
    * subst r. cbn [fst snd]. split; [unfold HEAD; reflexivity|]. apply NEW.
      apply (U4' (buf' - HEAD, HEAD)). rewrite EU'. apply in_or_app. right. left. reflexivity.
  + intros _. rewrite EU'. apply in_or_app. right. left. reflexivity.
Qed.

End K.
