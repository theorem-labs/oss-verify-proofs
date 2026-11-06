(* The forms of lib/A/Prog/HarnessPropsA.v at the ASan image's values are the ASan statements' own forms:
   answer_ok_mA (lib/A/Prog/check_reply_answer_c.v:43-47), reply_okA (lib/A/Prog/check_reply_c.v:53-60, which names
   the shape by its bytes where the plain reply_ok reads it from the image) and rt_okA
   (lib/A/Prog/check_round_trip_c.v:61-66). With harness_props_holds_a (lib/A/Prog/HarnessPropsAProof.v) they
   discharge the abort edges of check_reply_answer, check_reply and check_round_trip. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel check_reply_c
  HarnessPropsProof.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import HarnessPropsA.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require sup_reply_code_c check_reply_answer_c
  check_reply_c check_round_trip_c.
Import ListNotations.
Open Scope Z_scope.

Local Notation atoi_a := A.Prog.sup_reply_code_c.atoi_a.
Local Notation reply_code_a := A.Prog.sup_reply_code_c.reply_code_a.

Lemma answer_ok_a_bridge : forall ans xr n w0,
  answer_ok_at reply_code_a ans xr n w0 <-> A.Prog.check_reply_answer_c.answer_ok_mA ans xr n w0.
Proof. reflexivity. Qed.

Lemma shape_addr_strA : forall n w0, img_str (shape_addr n w0) = A.Prog.check_reply_c.shape_strA n w0.
Proof.
  intros n w0. unfold shape_addr, A.Prog.check_reply_c.shape_strA.
  destruct (n =? 0); [exact img_lit | apply img_shape].
Qed.

Lemma reply_ok_a_bridge : forall n w0 xr,
  reply_ok_at reply_code_a n w0 xr <-> A.Prog.check_reply_c.reply_okA n w0 xr.
Proof.
  intros n w0 xr. unfold reply_ok_at, A.Prog.check_reply_c.reply_okA. rewrite shape_addr_strA, img_lit. reflexivity.
Qed.

Lemma rt_ok_a_bridge : forall R q sb hb ws,
  rt_ok_at atoi_a reply_code_a R q sb hb ws <-> A.Prog.check_round_trip_c.rt_okA R q sb hb ws.
Proof. reflexivity. Qed.
