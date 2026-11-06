(* sup_resp's walk on the ASan build of plugin-hostd/fuzz_command, part 0: the snprintf text of "resp %d", a constant
   cell found by computation, and the read-only bytes kept across a step with an empty footprint.

   The step through the snprintf wrapper, which writes sup_resp's own side-stack frame, is the kit's aj_art_own_at
   (lib/A/Prog/PaArtOwn.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaArt CmdBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecAns.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module RA := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.RecAns.

(* a one-byte constant cell of the allocator record, found in a cell list by computation *)
Definition z1_in (a v : Z) (l : list acell) : bool :=
existsb (fun c => match c with ACell (ANum a') 1 (AV (ANum v')) => (a' =? a) && (v' =? v) | _ => false end) l.
Lemma z1_in_sound : forall a v l, z1_in a v l = true -> In (z1 (ANum a) v) l.
Proof.
intros a v l. induction l as [|c l IH]; cbn [z1_in existsb]; [discriminate|].
intros H. apply orb_true_iff in H as [H | H]; [left | right; exact (IH H)].
destruct c as [ca cw cv]. destruct ca; try discriminate. destruct cw as [|[|cw]]; try discriminate.
destruct cv as [e|mk zk]; try discriminate. destruct e; try discriminate.
apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

(* the format "resp %d" (the pinned image's literal at 0x21d00, CmdRo.v RO_lit_21d00) and the text it makes of an
   int: fuzz_command's plain proof, lib/Prog/RecAns.v:25-57 *)
Lemma sr_fmt_parse : PF.pf_parse RA.RESP_FMT = Some RA.RESP_PS.
Proof. exact RA.resp_parse. Qed.
Lemma sr_fmt_text : forall c, PF.pf_text RA.RESP_PS [PF.AInt c] = Some (RA.RESP_HEAD ++ PF.pf_dec c).
Proof. exact RA.resp_text. Qed.
Lemma sr_fmt_bytes : forall c, -2^31 <= c < 2^31 -> PF.pf_bytes (RA.RESP_HEAD ++ PF.pf_dec c) = resp c.
Proof. exact RA.pf_resp. Qed.
Lemma sr_fmt_len : forall c, -2^31 <= c < 2^31 -> (6 <= length (RA.RESP_HEAD ++ PF.pf_dec c) <= 16)%nat.
Proof. exact RA.resp_len. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section j.
Variable segs : list Segment.
Variable B : asyms.
(* the read-only bytes of the image stay the image's across a step of the walk whose footprint is empty: the
   journal's image clause, with the RELRO range inside the image (cmd_ro_ok's words; CmdBase.v's arodata_ok_journalP
   for an empty footprint, where fp_spares needs no ro_below_ofl) *)
Lemma aro_journal0 : forall rlo rhi STK sp0 ly S W0 mem md own lyc Sc W memc mdc k,
(forall a, rlo <= a < rhi -> in_img segs a) ->
ajournal segs B STK sp0 [] ly S W0 mem md own lyc Sc W memc mdc k ->
arodata_okP segs rlo rhi B (aview segs (w_H W0) mem) -> arodata_okP segs rlo rhi B (aview segs (w_H W) memc).
Proof.
intros rlo rhi STK sp0 ly S W0 mem md own lyc Sc W memc mdc k Himg HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He | ].
- destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr] | exact (Himg a Hgot)].
- split; [intros (r & Hr & _); destruct Hr | intros (r & Hr & _); destruct Hr].
Qed.
End j.
End d.
