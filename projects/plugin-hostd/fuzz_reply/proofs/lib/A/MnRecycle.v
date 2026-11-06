(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MnRecycle.v (a working branch 30a1993588f, c5 + memnorm; file sha256 c5ed09f39019) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 2 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-29 (a Theorem Labs lane, p102 row N9-MNARM; task MEMNORM, a Theorem Labs lane; split a Theorem Labs lane): DRAFT, statements.
   rule 24: no function proved (kind: statement drafts - the memnorm-keeping twins of QuarantineCallback::Recycle
   (0x33e30) and SizeClassAllocator64LocalCache::Deallocate (0x34234) inside the drain's DoRecycle; cgif proofs
   DGif1dr.dgif1_rchunk_cgif (YFfs / YFg7 primary arm, YFg9 / YFg8 secondary arm) and dgif1_cdealloc_cgif (YFg0),
   through DGif1dI).
   WHY INSIDE THE WALK.  At cgif the owned set [aowned] meets the read-only segment [0x10000, 0x30000) (YF0m.v:279-286
   Tfib_owned_static: (0x102e8, 8) .. (0x20e62, 0x1e), (0x1cccb, 21) .. (0x21588, 2)), so the callee post's raw frame
   DIfaceR.acall_raw_x (outside the owned sets, the scratch and E: mem' = mem) admits a ROM byte copied into the overlay
   at an owned address and does not give the keep.  The keep is proved inside the callee walk, per runner phase, from
   the phase's own write window (proof route, a Theorem Labs lane 16:30Z: st_ok + frame_of as preset's YGcallMxmn.v:677
   memnorm_frame_of; the mmap / munmap nodes by MemnormGk.klaw_commit3 / klaw_munmap and MemnormG.amreal_m_node).
   STATEMENT SHAPE (a Theorem Labs lane): ErrnoG's raw add-on with `MemnormT.memnorm_keep im_segs mem mem'` next to
   `errno_kept B mem mem'` in the SAME post (amreal has no rule that joins two contracts). Additive: ErrnoG, DIfaceR and
   every existing statement are unchanged.
   - [de_rchunk_m_t] / [de_cdealloc_m_t]: ErrnoG.de_rchunk_t / de_cdealloc_t (ErrnoG.v:274-286 / :298-309) with the
     keep right after errno_kept;
   - [de_rchunk_em_e] / [de_cdealloc_em_e]: they give the ErrnoG forms (drop the keep; Qed);
   - [DIfaceREm]: ErrnoG.DIfaceRE's four fields at the keep forms, and [DIfaceREm_RE] (Qed). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DeallocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG DGif0 DIfaceR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ErrnoG MemnormT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import MnEnq MnDrain.
Import ListNotations.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.
Section rc.
Variable B : asyms.
Variable ARXr : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Definition de_rchunk_m_t : Prop :=
forall inst ly X k ks zs cbp W regs mem md,
rcc_pre_x B ARXr inst ly X k cbp W regs mem md -> DRq X (k :: ks) zs ->
amreal im_segs (recycle_chunk k X) W (cfg_at im_segs dg_rchunk regs mem md)
(fun r W' c' => exists regs' mem' md',
  c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
  acall_post_x B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  acall_raw_x B AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  ErrnoG.errno_kept B mem mem' /\
  MemnormT.memnorm_keep im_segs mem mem' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
   aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a) /\
  DRq (snd r) ks zs /\ st_cache_inited (snd r) = true /\ (forall a, AOX ly (snd r) a -> AOX ly X a)).
Definition de_cdealloc_m_t : Prop :=
forall inst ly X its z zs W regs mem md,
cd_pre_x B ARXr inst ly X z W regs mem md -> DRq X its (z :: zs) ->
amreal im_segs (cache_dealloc kBatchClass z X) W (cfg_at im_segs dg_cdealloc regs mem md)
(fun r W' c' => exists regs' mem' md',
  c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
  acall_post_x B ARXr AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  acall_raw_x B AOX inst KSTACK_CF ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
  ErrnoG.errno_kept B mem mem' /\
  MemnormT.memnorm_keep im_segs mem mem' /\
  (forall a, 0 <= a < 2 ^ 64 -> YFeuC.puser ly X a -> aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
  (forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a) /\
  DRq (snd r) its zs /\ st_cache_inited (snd r) = true /\ (forall a, AOX ly (snd r) a -> AOX ly X a)).

Lemma de_rchunk_em_e : de_rchunk_m_t -> ErrnoG.de_rchunk_t B ARXr AOX DRq.
Proof.
intros H inst ly X k ks zs cbp W regs mem md P D.
eapply amreal_mono; [| exact (H inst ly X k ks zs cbp W regs mem md P D)].
intros r W' c' (regs' & mem' & md' & Hc & HP & HR & HE & _ & HT).
exists regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HR|]. split; [exact HE | exact HT].
Qed.
Lemma de_cdealloc_em_e : de_cdealloc_m_t -> ErrnoG.de_cdealloc_t B ARXr AOX DRq.
Proof.
intros H inst ly X its z zs W regs mem md P D.
eapply amreal_mono; [| exact (H inst ly X its z zs W regs mem md P D)].
intros r W' c' (regs' & mem' & md' & Hc & HP & HR & HE & _ & HT).
exists regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HR|]. split; [exact HE | exact HT].
Qed.
End rc.

(* ErrnoG.DIfaceRE at the keep forms *)
Section b.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable ARXr : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world im_segs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop.
Variable dbody : astate -> M unit.
Variable L24 : Z.
Variable QB : astate -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
(* DGif0.DIface's memory predicate at Put's call of Enqueue (DIfaceR.enq_spec_g's premise). *)
Variable MP : (word -> option byte) -> Prop.
Record DIfaceREm : Prop := {
  dem_enqueue : de_enqueue_m_t B U ARX AOX rpre lpost fpre dpost L24 QB MP;
  dem_drain : de_drain_m_t B ARX AOX dbody L24 QB;
  dem_rchunk : de_rchunk_m_t B ARXr AOX DRq;
  dem_cdealloc : de_cdealloc_m_t B ARXr AOX DRq
}.
Lemma DIfaceREm_RE : DIfaceREm -> ErrnoG.DIfaceRE B U ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP.
Proof.
intros [HE HD HR HC]. constructor.
- exact (de_enqueue_em_e B U ARX AOX rpre lpost fpre dpost L24 QB MP HE).
- exact (de_drain_em_e B ARX AOX dbody L24 QB HD).
- exact (de_rchunk_em_e B ARXr AOX DRq HR).
- exact (de_cdealloc_em_e B ARXr AOX DRq HC).
Qed.
End b.
End d.
