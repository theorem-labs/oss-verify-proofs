(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MnDrain.v (a working branch 30a1993588f, c5 + memnorm; file sha256 408efca2b80a) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10-29 (a Theorem Labs lane, p102 row N9-MNARM; task MEMNORM, a Theorem Labs lane; split a Theorem Labs lane): DRAFT, statements.
   rule 24: no function proved (kind: statement drafts - the memnorm-keeping twin of the Quarantine::Drain callee
   contract at Put's call, used by the Deallocate drain arm (DGfz); cgif proof DGif1d.dr_drain_cgif =
   DGif1df.tfib_drain_ok_cf with DGif1dr's recycle fields, cut memory DMiface.dmem_q over dwin_q).
   WHY INSIDE THE WALK.  At cgif the owned set [aowned] meets the read-only segment [0x10000, 0x30000) (YF0m.v:279-286
   Tfib_owned_static: (0x102e8, 8) .. (0x20e62, 0x1e), (0x1cccb, 21) .. (0x21588, 2)), so the callee post's raw frame
   DIfaceR.acall_raw_x (outside the owned sets, the scratch and E: mem' = mem) admits a ROM byte copied into the overlay
   at an owned address and does not give the keep.  The keep is proved inside the callee walk, per runner phase, from
   the phase's own write window (proof route, a Theorem Labs lane 16:30Z: st_ok + frame_of as preset's YGcallMxmn.v:677
   memnorm_frame_of; the mmap / munmap nodes by MemnormGk.klaw_commit3 / klaw_munmap and MemnormG.amreal_m_node).
   STATEMENT SHAPE (a Theorem Labs lane): ErrnoG's raw add-on with `MemnormT.memnorm_keep im_segs mem mem'` next to
   `errno_kept B mem mem'` in the SAME post (amreal has no rule that joins two contracts). Additive: ErrnoG, DIfaceR and
   every existing statement are unchanged.
   - [de_drain_m_t]: ErrnoG.de_drain_t (ErrnoG.v:360) at MnEnq.acall_raw_em_x;
   - [de_drain_em_e]: it gives ErrnoG.de_drain_t (drop the keep; Qed). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import MnEnq.
Import ListNotations.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.
Section b.
Variable B : asyms.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable dbody : astate -> M unit.
Variable L24 : Z.
Variable QB : astate -> Prop.

(* Quarantine::Drain at Put's call: ErrnoG.de_drain_t with the keep *)
Definition de_drain_m_t : Prop := drain_spec_g B ARX AOX dbody L24 QB (acall_raw_em_x B AOX).

Lemma de_drain_em_e : de_drain_m_t -> ErrnoG.de_drain_t B ARX AOX dbody L24 QB.
Proof.
intros H inst ly X W regs mem md PRE.
eapply amreal_mono; [| exact (H inst ly X W regs mem md PRE)].
intros r W' c' (regs' & mem' & md' & Hc & HP & (HR & HE & _)).
exists regs', mem', md'. split; [exact Hc|]. split; [exact HP | split; [exact HR | exact HE]].
Qed.
End b.
End d.
