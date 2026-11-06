(* proves no function (rule 24; kind: segment lemma): k3's statements of image B's GN_RI_step_x / GN_RI_end_x
   (W_LLVMFuzzerTestOneInput_top_x.v :904-905 at MT := ameter_triv, RINV := ReplyRINVB.fr_RINV, MMAX := fr_MMAX) from
   the LS halves k3's lib/B/ReplyBTop.v states as its Section hypotheses GN_RI_step_room_x / GN_RI_end_ls_x (:119-120).
   - GN_RI_step_ri_x / GN_RI_end_ri_x: the RINV halves (PROVED, lib/B/ReplyRINVB_gone.v's RG.GN_RI_step_ri_holds /
     RG.GN_RI_end_ri_holds).
   - GN_RI_step_x_of_room / GN_RI_end_x_of_ls: k3's two rows from their LS halves, for ReplyBTop.v :497-498, which call
     them as `ReplyRINVB_gone_k3.GN_RI_step_x_of_room GN_RI_step_room_x rc fx` and
     `ReplyRINVB_gone_k3.GN_RI_end_x_of_ls GN_RI_end_ls_x rc fx`.
   - Section k3_scratch: k3's two Context lines, and the four gone rows closed by exact from them.
  LS IS GENERIC: lib/B/ReplyBTopLifts.v (LSxBO) cannot load on the window yet (its :51 Requires ReplyLSBRrPre, which
  the window leaves out on purpose), so this file does not Require it.  Each statement is k3's text with (@LS rc) for
  (@LSxBO rc), over an implicit LS : forall rc, lfcx -> Z -> lmod -> alayout -> astate -> Prop; at k3's call LS is
  inferred as LSxBO from k3's hypothesis.  k3's other two gone rows, GN_RI_pairs_x and GN_RI_read_x, are PROVED in
  lib/B/ReplyRINVB_gone.v.
  NOT HERE: the two rows at B's v3 LS instance, in lib/B/ReplyRINVB_gone_ls.v: at the counting meter MT_sec (the
  instance with its count clause fr_SEC) GN_RI_step_x_sec / GN_RI_end_x_sec, the forms k3 plugs; at ameter_triv
  GN_RI_step_lsi_triv / GN_RI_end_lsi_cap. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YK11 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0f YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
  ReplyRINVB W_LLVMFuzzerTestOneInput_gone_base ReplyRINVB_gone.
Open Scope Z_scope.

(* ================================================================== k3's GN_RI_step_x / GN_RI_end_x, at every LS *)
Definition GN_RI_step_x_T (LS : forall (rc : YM05.RunCeil), @lfcx rc -> Z -> lmod -> alayout -> astate -> Prop) : Prop :=
  forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_LLVMFuzzerTestOneInput_gone_base.GN_RI_step rc TfibB ameter_triv (@LS rc) (@ReplyRINVB.fr_RINV rc) fr_MMAX.
Definition GN_RI_end_x_T (LS : forall (rc : YM05.RunCeil), @lfcx rc -> Z -> lmod -> alayout -> astate -> Prop) : Prop :=
  forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_LLVMFuzzerTestOneInput_gone_base.GN_RI_end rc TfibB ameter_triv (@LS rc) (@ReplyRINVB.fr_RINV rc).

(* ---- PROVED: the RINV halves, at k3's parameters and every LS *)
Lemma GN_RI_step_ri_x {LS : forall (rc : YM05.RunCeil), @lfcx rc -> Z -> lmod -> alayout -> astate -> Prop} :
  forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @ReplyRINVB_gone.RG.GN_RI_step_ri rc TfibB ameter_triv (@LS rc) (@ReplyRINVB.fr_RINV rc).
Proof. intros rc fx. apply ReplyRINVB_gone.RG.GN_RI_step_ri_holds. Qed.
Lemma GN_RI_end_ri_x {LS : forall (rc : YM05.RunCeil), @lfcx rc -> Z -> lmod -> alayout -> astate -> Prop} :
  forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @ReplyRINVB_gone.RG.GN_RI_end_ri rc TfibB ameter_triv (@LS rc) (@ReplyRINVB.fr_RINV rc).
Proof. intros rc fx. apply ReplyRINVB_gone.RG.GN_RI_end_ri_holds. Qed.

(* ---- k3's GN_RI_step_x / GN_RI_end_x from their LS halves; each premise is k3's Context line (ReplyBTop.v :119 /
   :120) with (@LS rc) for (@LSxBO rc) *)
Lemma GN_RI_step_x_of_room {LS : forall (rc : YM05.RunCeil), @lfcx rc -> Z -> lmod -> alayout -> astate -> Prop} :
  (forall (rc : YM05.RunCeil) (fx : YK11.FPState), @ReplyRINVB_gone.RG.GN_RI_step_room rc TfibB ameter_triv (@LS rc) (@ReplyRINVB.fr_RINV rc) fr_MMAX) ->
  forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_LLVMFuzzerTestOneInput_gone_base.GN_RI_step rc TfibB ameter_triv (@LS rc) (@ReplyRINVB.fr_RINV rc) fr_MMAX.
Proof.
  intros HR rc fx. apply ReplyRINVB_gone.RG.GN_RI_step_of_parts.
  - apply ReplyRINVB_gone.RG.GN_RI_step_ri_holds.
  - apply ReplyRINVB_gone.RG.GN_RI_step_ls_of_room. exact (HR rc fx).
Qed.
Lemma GN_RI_end_x_of_ls {LS : forall (rc : YM05.RunCeil), @lfcx rc -> Z -> lmod -> alayout -> astate -> Prop} :
  (forall (rc : YM05.RunCeil) (fx : YK11.FPState), @ReplyRINVB_gone.RG.GN_RI_end_ls rc TfibB ameter_triv (@LS rc) (@ReplyRINVB.fr_RINV rc)) ->
  forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_LLVMFuzzerTestOneInput_gone_base.GN_RI_end rc TfibB ameter_triv (@LS rc) (@ReplyRINVB.fr_RINV rc).
Proof.
  intros HL rc fx. apply ReplyRINVB_gone.RG.GN_RI_end_of_parts.
  - apply ReplyRINVB_gone.RG.GN_RI_end_ri_holds.
  - exact (HL rc fx).
Qed.

(* ================================================================== one Check per obligation *)
Check (fun LS => @GN_RI_step_x_of_room LS : _ -> GN_RI_step_x_T LS).
Check (fun LS => @GN_RI_end_x_of_ls LS : _ -> GN_RI_end_x_T LS).

(* ================================================================== scratch: k3's Context lines (ReplyBTop.v :119-120,
   verbatim but for (@LS rc)), and the four gone rows closed by exact, the last two as ReplyBTop.v :497-498 call them *)
Section k3_scratch.
Context (LS : forall (rc : YM05.RunCeil), @lfcx rc -> Z -> lmod -> alayout -> astate -> Prop).
Context (GN_RI_step_room_x : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @ReplyRINVB_gone.RG.GN_RI_step_room rc TfibB ameter_triv (@LS rc) (@ReplyRINVB.fr_RINV rc) fr_MMAX).
Context (GN_RI_end_ls_x : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @ReplyRINVB_gone.RG.GN_RI_end_ls rc TfibB ameter_triv (@LS rc) (@ReplyRINVB.fr_RINV rc)).
Goal forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_LLVMFuzzerTestOneInput_gone_base.GN_RI_pairs rc (@ReplyRINVB.fr_RINV rc).
Proof. intros rc fx. exact (ReplyRINVB_gone.GN_RI_pairs_x rc fx). Qed.
Goal forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_LLVMFuzzerTestOneInput_gone_base.GN_RI_read rc (@ReplyRINVB.fr_RINV rc).
Proof. intros rc fx. exact (ReplyRINVB_gone.GN_RI_read_x rc fx). Qed.
Goal forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_LLVMFuzzerTestOneInput_gone_base.GN_RI_step rc TfibB ameter_triv (@LS rc) (@ReplyRINVB.fr_RINV rc) fr_MMAX.
Proof. intros rc fx. exact (GN_RI_step_x_of_room GN_RI_step_room_x rc fx). Qed.
Goal forall (rc : YM05.RunCeil) (fx : YK11.FPState), @W_LLVMFuzzerTestOneInput_gone_base.GN_RI_end rc TfibB ameter_triv (@LS rc) (@ReplyRINVB.fr_RINV rc).
Proof. intros rc fx. exact (GN_RI_end_x_of_ls GN_RI_end_ls_x rc fx). Qed.
End k3_scratch.

(* ================================================================== the axiom audit (toolchain/allowed-axioms.txt) *)
Print Assumptions GN_RI_step_ri_x.
Print Assumptions GN_RI_end_ri_x.
Print Assumptions GN_RI_step_x_of_room.
Print Assumptions GN_RI_end_x_of_ls.
