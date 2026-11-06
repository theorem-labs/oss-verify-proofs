(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MnEnq.v (commit 30a1993588f, c5 + memnorm; file sha256 1235d7cc4fb2) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/MnEnq.v (commit d2dafa219c1, file sha256 be3db38f6717) onto plugin-hostd/fuzz_reply's asan-ubsan image (unstripped fuzz_reply.asan-ubsan, sha256 3389287e1d61; pin 10ffb5f9202a) by alreloc ced0368250cb6538 (A -> B, direct map 541d2a13b9d2): 0 numerals moved; module paths lib.A -> lib.B and the image twins A<r> -> Y<r>. *)
(* Theorem Labs, 2026-10-29 (a Theorem Labs lane, p102 row N9-MNARM; task MEMNORM, a Theorem Labs lane; split a Theorem Labs lane): DRAFT, statements.
   rule 24: no function proved (kind: statement drafts - the memnorm-keeping twin of the QuarantineCache::Enqueue callee
   contract at Put's call, used by the Deallocate mid arm (DGg2) and drain arm (DGfz); cgif proof CLenqcgif's arms
   enq_room_xs / enq_hit_xs / enq_miss_xs, raw frames YFgp.MEQ and twins).
   WHY INSIDE THE WALK.  At cgif the owned set [aowned] meets the read-only segment [0x10000, 0x30000) (YF0m.v:279-286
   Tfib_owned_static: (0x102e8, 8) .. (0x20e62, 0x1e), (0x1cccb, 21) .. (0x2146c, 2)), so the callee post's raw frame
   DIfaceR.acall_raw_x (outside the owned sets, the scratch and E: mem' = mem) admits a ROM byte copied into the overlay
   at an owned address and does not give the keep.  The keep is proved inside the callee walk, per runner phase, from
   the phase's own write window (proof route, a Theorem Labs lane 16:30Z: st_ok + frame_of as preset's YGcallMxmn.v:677
   memnorm_frame_of; the mmap / munmap nodes by MemnormGk.klaw_commit3 / klaw_munmap and MemnormG.amreal_m_node).
   STATEMENT SHAPE (a Theorem Labs lane): ErrnoG's raw add-on with `MemnormT.memnorm_keep im_segs mem mem'` next to
   `errno_kept B mem mem'` in the SAME post (amreal has no rule that joins two contracts). Additive: ErrnoG, DIfaceR and
   every existing statement are unchanged.
   - [acall_raw_em_x]: ErrnoG.acall_raw_e_x (ErrnoG.v:254-256) plus the keep; also the Drain add-on's (MnDrain.v);
   - [de_enqueue_m_t]: ErrnoG.de_enqueue_t (ErrnoG.v:356) at acall_raw_em_x;
   - [de_enqueue_em_e]: it gives ErrnoG.de_enqueue_t (drop the keep; Qed). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DeallocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG DGif0 DIfaceR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ErrnoG MemnormT.
Import ListNotations.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.

(* ErrnoG.acall_raw_e_x with the keep *)
Definition acall_raw_em_x (B : asyms) (AOX : alayout -> astate -> Z -> Prop) : fxrel :=
fun inst stk ly S W regs mem md E ly' S' W' regs' mem' md' =>
acall_raw_x B AOX inst stk ly S W regs mem md E ly' S' W' regs' mem' md' /\ ErrnoG.errno_kept B mem mem' /\
MemnormT.memnorm_keep im_segs mem mem'.

Section b.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world im_segs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop.
Variable L24 : Z.
Variable QB : astate -> Prop.
(* DGif0.DIface's memory predicate at Put's call of Enqueue (DIfaceR.enq_spec_g's premise). *)
Variable MP : (word -> option byte) -> Prop.

(* QuarantineCache::Enqueue at Put's call: ErrnoG.de_enqueue_t with the keep *)
Definition de_enqueue_m_t : Prop := enq_spec_g B U ARX AOX rpre lpost fpre dpost L24 QB MP (acall_raw_em_x B AOX).

Lemma de_enqueue_em_e : de_enqueue_m_t -> ErrnoG.de_enqueue_t B U ARX AOX rpre lpost fpre dpost L24 QB MP.
Proof.
intros H inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17
  H18 H19 H20 H21 H22 H23 H24.
eapply amreal_mono; [| exact (H inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat H1 H2 H3 H4 H5 H6 H7 H8 H9 H10
  H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24)].
intros r W' c' (regs' & mem' & md' & nb & Hc & HP & (HR & HE & _) & HT).
exists regs', mem', md', nb. split; [exact Hc|]. split; [exact HP|]. split; [split; [exact HR | exact HE] | exact HT].
Qed.
End b.
End d.
