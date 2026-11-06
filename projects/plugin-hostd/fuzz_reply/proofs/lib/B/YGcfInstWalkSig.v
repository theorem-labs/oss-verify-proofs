(* CARRIED from commit 9e2e0be6e3e5010921fb7ec0e30341da3a6c3da2,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfInstWalkSig.v, sha256 63bb82b7d82aa9da22858b83004947fc29ee6e7f70cd2b8c583b90ea2bd4d3c2 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the
   module paths only: OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib M -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable M, except lib.B (the asan-ubsan image twin of lib/A/YGcfInstWalkSig.v)
   for: YGcfRmodel MemnormT AllocG. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* DRAFT (lane M, a working branch): the SEAM between a unit's relocated walk and the generic cf instance layer.

   The layer is generic over CfParams / CfImg and the opaque allocator relation ARX; a unit's walk is NOT, because
   every arm is a machine run that decodes that unit's own bytes out of [segs].  So each unit supplies its walk's
   tops, and this record is exactly what the layer consumes.  The field texts are a Theorem Labs lane's walk tops
   (a Theorem Labs lane's walk-tops list for a working branch; the lines are cited below), with
   [tfibsegs] replaced by the section's [segs] and the A' numeral 0x32524 by CfImg's [cf_pc_allocate]:
   - wsa_hit    A/MemnormHitG.v:188   ARM_HITG_em
   - wsa_hitk   A/MemnormHitK.v:143   ARM_HITK_em
   - wsa_missg  A/MemnormMissG0.v:307 alloc_missg_cf_em (inner A/MemnormMissG.v:559)
   - wsa_missk  A/MemnormMissK0.v:305 alloc_missk_cf_em (inner A/MemnormMissK.v:364)
   - wsa_sec    A/AGioM.v:76          alloc_sec_w_em    (arms A/AGk0M.v:275 / :531 / :584)
   The refill is NOT a field: A11's miss arms carry it as their own Section hypothesis (RFm), discharged on the
   unit's side when it instantiates them, and the wrapper-segment entry facts are the unit's rows A1 / A2.
   The Deallocate half (A/MemnormDnull.v:198, A/MemnormDcommon.v:120, A/MemnormDmid.v:154 / :210, A/DGg1.v:571)
   is lane F2's record, in its own file: its common and null arms end in MemnormDleaf.dealloc_leaf_raw_eem, which
   is not in this branch's base yet, and one writer owns one file.

   FROZEN only after a Theorem Labs lane confirms the field list against preset's lines and lane W's reply relocation, and
   after the two satisfiability witnesses (preset at ameter_cf; reply at init_state, A/AD26.v:215).
   FIELD ROUND 3 PART 3b (a Theorem Labs lane ruling 2026-10-30 18:50Z): the two miss fields take the call state's
   `YAkMemnorm.memnorm segs mem -> arodata_ok_cf segs B mem ->` right after the pre (the Allocate contract's MP at the
   cf instance, YGcfMallocComposeE), as the round-3 miss arms (MemnormMissG0W / K0W) need them.  The hit fields and
   the secondary field do not read them and stay as they were (so AllocGtopM's secondary contract keeps no MP). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK0j YK15 YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfRmodel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import MemnormT AllocG.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section b.
Variable segs : list Segment.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
(* the walk's opaque relation at one ghost set: [ARX_cf Hp] of YGcfInstBase has this type *)
Variable ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable nmax : Z.
Variable lmax : Z.
Variable lpost : astate -> Prop.
Variable cf : Z.

(* a Theorem Labs lane's check against preset (A11 a working branch 89ce03e835, 2026-10-29 23:49Z): the call-site
   arguments are alignment 8 and alloc_type 1 only (YGcfInstBase.al_cf / atp_cf), the entry is CfImg's
   cf_pc_allocate and the out-of-memory byte is as_oom_byte B; every arm takes `cf = 0 \/ cf = 1` (one generic
   instance for both can_fill values).  The uninited-cache refutation (MemnormAtop's UNINIT) is the interface's
   if_uninit, discharged by the instance, not a walk field. *)
Local Abbreviation PRE := (AllocG.alloc_pre segs B U ARX rpre nmax lmax 8 1 cf).
Local Abbreviation LEAF := (MemnormT.alloc_leaf_em segs B mt ARX AOX lpost (as_oom_byte B)).
(* the call state's memory facts (field round 3 part 3b): MemnormT's MP at the cf instance *)
Local Abbreviation MPA := (fun m => arodata_ok_cf segs B m).

(* The unit's Allocate walk, at this instance's parameters.  Every field is the unit's own theorem; nothing here
   is proved, and nothing here mentions a numeral. *)
Record WalkSigA : Prop := {
  (* the hit arm, 49 <= n <= 64512 with a cached chunk *)
  wsa_hit : forall inst so bp ly S W regs mem md n tr l off,
    cf = 0 \/ cf = 1 ->
    PRE inst so bp ly S W regs mem md n tr ->
    49 <= n <= 64512 -> st_cache_inited S = true ->
    pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
    amreal segs (mt n tr S) W (cfg_at segs cf_pc_allocate regs mem md)
      (LEAF inst ly S W regs mem md n tr);
  (* the small-class (K) hit arm, 0 <= n <= 48 *)
  wsa_hitk : forall inst so bp ly S W regs mem md n tr l off,
    cf = 0 \/ cf = 1 ->
    PRE inst so bp ly S W regs mem md n tr ->
    0 <= n <= 48 -> st_cache_inited S = true ->
    pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
    amreal segs (mt n tr S) W (cfg_at segs cf_pc_allocate regs mem md)
      (LEAF inst ly S W regs mem md n tr);
  (* the miss arm (the cache is empty), 49 <= n <= 64512, at either can_fill *)
  wsa_missg : forall inst so bp ly S W regs mem md n tr,
    cf = 0 \/ cf = 1 ->
    PRE inst so bp ly S W regs mem md n tr -> arodata_ok_cf segs B mem ->
    49 <= n <= 64512 ->
    pc_chunks (cache S (chunk_class n)) = [] ->
    amreal segs (mt n tr S) W (cfg_at segs cf_pc_allocate regs mem md)
      (LEAF inst ly S W regs mem md n tr);
  (* the small-class miss arm *)
  wsa_missk : forall inst so bp ly S W regs mem md n tr,
    cf = 0 \/ cf = 1 ->
    PRE inst so bp ly S W regs mem md n tr -> arodata_ok_cf segs B mem ->
    0 <= n <= 48 ->
    pc_chunks (cache S (chunk_class n)) = [] ->
    amreal segs (mt n tr S) W (cfg_at segs cf_pc_allocate regs mem md)
      (LEAF inst ly S W regs mem md n tr);
  (* the secondary arm, at the widened bound the unit's CfParams fixes *)
  wsa_sec : forall inst so bp ly S W regs mem md n tr,
    cf = 0 \/ cf = 1 ->
    PRE inst so bp ly S W regs mem md n tr ->
    64513 <= n ->
    amreal segs (mt n tr S) W (cfg_at segs cf_pc_allocate regs mem md)
      (LEAF inst ly S W regs mem md n tr)
}.

(* The four arms are MemnormAtop's hypotheses (A/MemnormAtop.v:66-81) at MP := MPA (the hit arms ignore it), so a unit
   that has WalkSigA has MemnormT.aalloc_prim_realizes_em's inputs; the secondary field is AllocGtopM's. *)
Lemma wsa_prim_arms : WalkSigA ->
  (forall inst so bp ly S W regs mem md n tr l off, cf = 0 \/ cf = 1 ->
     PRE inst so bp ly S W regs mem md n tr -> MPA mem -> 49 <= n <= 64512 -> st_cache_inited S = true ->
     pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
     amreal segs (mt n tr S) W (cfg_at segs cf_pc_allocate regs mem md) (LEAF inst ly S W regs mem md n tr)) /\
  (forall inst so bp ly S W regs mem md n tr l off, cf = 0 \/ cf = 1 ->
     PRE inst so bp ly S W regs mem md n tr -> MPA mem -> 0 <= n <= 48 -> st_cache_inited S = true ->
     pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
     amreal segs (mt n tr S) W (cfg_at segs cf_pc_allocate regs mem md) (LEAF inst ly S W regs mem md n tr)).
Proof.
intros [H1 H2 _ _ _]. split.
- intros inst so bp ly S W regs mem md n tr l off HC P _. exact (H1 inst so bp ly S W regs mem md n tr l off HC P).
- intros inst so bp ly S W regs mem md n tr l off HC P _. exact (H2 inst so bp ly S W regs mem md n tr l off HC P).
Qed.

End b.
End a.
