(* Group LAW-meter of A top_x's hypotheses (TOPX-OWNERS.md (sha256 bb821fae800d; internal record)): W_LLVMFuzzerTestOneInput_top_x.v's MLAW and
   MO_FR, each stated exactly as top_x states it (MO_FR at :247 since W8's F3 merge b85bd3e626e: KF-COUNT #4's set_fs
   form), at the instance's meter MT := ameter_triv (Reusable/YCbp.v: mo_ok / mo_le are True), the meter
   ReplyATopX.v and ReplyDriverCf.v use.  Neither lemma has a premise that could be false: MLAW is closed, MO_FR's
   conclusion is True at this meter.  At MT := MT_sec, MO_FR needs that meter's own law (KF-COUNT's), not this lemma.
   proves no function (kind: model and invariant lemmas). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YG00 YG0d YC5d YCbp YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l.
Open Scope Z_scope.

Section m.
Context {rc : YM05.RunCeil}.

(* lib/A/W_LLVMFuzzerTestOneInput_top_x.v MLAW at MT := ameter_triv *)
Lemma topx_MLAW : ameter_laws ameter_triv.
Proof. exact ameter_triv_laws. Qed.

(* top_x.v:247 MO_FR at MT := ameter_triv *)
Lemma topx_MO_FR : forall s f, mo_le ameter_triv s (set_fs f s) 0.
Proof. intros s f. exact I. Qed.
End m.
