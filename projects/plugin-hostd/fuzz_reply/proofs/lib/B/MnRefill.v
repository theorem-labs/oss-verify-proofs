(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MnRefill.v (commit 30a1993588f, c5 + memnorm; file sha256 30e2d494441d) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/MnRefill.v at commit 789778cb16f, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10-29 (a Theorem Labs lane, p102 row N9-MNARM; task MEMNORM, a Theorem Labs lane): DRAFT, statements only.
   rule 24: no function proved (kind: statement drafts - the memnorm-keeping twin of the Allocate miss arms' REFILL
   callee, SizeClassAllocator64LocalCache::Refill at ag_refill).

   WHY.  The miss arms (AGim / AGin, their seeds AGiw / AGja) call the refill through AIfaceM.if_refill
   (AGif0n.v:283-298).  Its post [rleaf] (AGif0n.v:253-268) frames the raw memory outside the owned sets at S0 and at
   the result and the refill's stack window [spZ regs - RSTACK, spZ regs).  At cgif [aowned] meets the read-only
   segment [0x10000, 0x30000) (YF0m.v:279-286), so rleaf's raw frame does not give the keep; the refill walk's own
   windows do (CLrefillR's three routes: the uninit step YFkv / YFhn.refill_leaf_init, the inited B2 leaves YFkt /
   YFkz over YFko.WINR, the B3 leaves CLrefillB3.LEAF_std over YFkn's MEQ and YFkm.XC_owned).

   WHAT, as ErrnoG.v:396-495 states the errno add-on of the same field (and in its order):
   - [rleaf_em]: ErrnoG.rleaf_e with `memnorm mem -> memnorm mem'` right after errno, inside the same existential;
   - [amm_refill_t]: AIfaceM.if_refill over rleaf_em (ErrnoG.ame_refill_t's premises, byte for byte);
   - [amm_refill_e]: amm_refill_t gives ErrnoG.ame_refill_t (drop the keep; Qed);
   - [refill_cgif_m_stmt]: the cgif statement the proof owes, at AGif1m.refill_cgif's instantiation (ARX_cgif,
     aowned, rpre_cgif, qtight, refill_tree; AImg_cgif / AGImg_cgif).
   ErrnoG, AGif0n, AGif1m and every existing statement are unchanged. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AllocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseAG AGif0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ErrnoG MemnormT.
Import ListNotations.
Open Scope Z_scope.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {AG : AGImg}.
Local Open Scope am_scope.

(* ErrnoG.rleaf_e with the keep (right after errno_kept, inside the same existential) *)
Definition rleaf_em (B : asyms) (ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (lpost : astate -> Prop)
(inst : Z) (ly : alayout) (S0 : astate) (n cl : Z) (W : world im_segs) (regs : bvmap 5 word) (mem : word -> option byte)
(md : Model) (r : unit * astate) (W' : world im_segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
ARX inst ly' (snd r) W' mem' md' /\ lpost (snd r) /\ st_cache_inited (snd r) = true /\
blocks_bytes (snd r) = blocks_bytes S0 /\ layout_le (length (st_secs S0)) ly ly' /\
wle W W' /\ aregs_preserved regs regs' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S0 a -> ~ AOX ly' (snd r) a -> ~ (spZ regs - ImgBaseAG.RSTACK <= a < spZ regs) ->
   aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
(forall x : word, ~ AOX ly S0 (bv_unsigned x) -> ~ AOX ly' (snd r) (bv_unsigned x) ->
   ~ (spZ regs - ImgBaseAG.RSTACK <= bv_unsigned x < spZ regs) -> mem' x = mem x) /\
ErrnoG.errno_kept B mem mem' /\
MemnormT.memnorm_keep im_segs mem mem' /\
(forall a, spZ regs - ImgBaseAG.RSTACK <= a < spZ regs -> apresent (w_H W') mem' a) /\
getr regs' 10 = w64 (match pc_chunks (cache (snd r) cl) with [] => 0 | _ => 1 end).

Lemma rleaf_em_e : forall B ARX AOX lpost inst ly S0 n cl W regs mem md r W' c',
  rleaf_em B ARX AOX lpost inst ly S0 n cl W regs mem md r W' c' ->
  ErrnoG.rleaf_e B ARX AOX lpost inst ly S0 n cl W regs mem md r W' c'.
Proof.
intros B ARX AOX lpost inst ly S0 n cl W regs mem md r W' c'
  (ly' & regs' & mem' & md' & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & _ & H13 & H14).
exists ly', regs', mem', md'. tauto.
Qed.

Section v.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable rtree : Z -> M unit.

(* AIfaceM.if_refill over rleaf_em (ErrnoG.ame_refill_t's premises unchanged) *)
Definition amm_refill_t : Prop :=
forall inst ly S0 W mem0 md0 n (sp0 : Z) (regs : bvmap 5 word) (mem : word -> option byte) (mat : list word),
ARX inst ly S0 W mem0 md0 -> rpre S0 n -> 0 <= n -> from_primary n = true ->
pc_chunks (cache S0 (chunk_class n)) = [] ->
ly_stk_lo ly + ImgBaseAG.AFSTACK <= sp0 -> ly_bot ly < sp0 -> sp0 <= ly_stk_hi ly -> sp0 mod 16 = 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - ImgBaseAG.AFSTACK <= a < sp0) -> aview im_segs (w_H W) mem a = aview im_segs (w_H W) mem0 a) ->
(forall x : word, ~ (sp0 - ImgBaseAG.AFSTACK <= bv_unsigned x < sp0) -> ~ (ly_T ly + t_unwinding <= bv_unsigned x < ly_T ly + t_unwinding + 1) ->
   mem x = mem0 x) ->
(forall a, sp0 - ImgBaseAG.AFSTACK <= a < sp0 -> apresent (w_H W) mem a) ->
spZ regs = sp0 - 176 -> getr regs 1 = w64 ag_refill_ret -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 im_tp ->
getr regs 10 = w64 (ly_T ly + t_cache) -> getr regs 11 = w64 (ly_T ly + t_cache + 80 * chunk_class n) ->
getr regs 12 = w64 inst -> getr regs 13 = w64 (chunk_class n) ->
amreal im_segs (rtree (chunk_class n) (set_nev (st_nev S0 + 1) S0)) W
  (cfg_at im_segs ag_refill regs mem (with_vm_backing (m_vm_lazy md0) mat md0))
  (rleaf_em B ARX AOX lpost inst ly S0 n (chunk_class n) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0)).

Lemma amm_refill_e : amm_refill_t -> ErrnoG.ame_refill_t B ARX AOX rpre lpost rtree.
Proof.
intros H inst ly S0 W mem0 md0 n sp0 regs mem mat H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19
  H20.
eapply amreal_mono; [| exact (H inst ly S0 W mem0 md0 n sp0 regs mem mat H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13
  H14 H15 H16 H17 H18 H19 H20)].
intros r W' c' HL. exact (rleaf_em_e B ARX AOX lpost inst ly S0 n (chunk_class n) W regs mem _ r W' c' HL).
Qed.
End v.
End g.
