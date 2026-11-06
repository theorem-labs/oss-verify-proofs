(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 1536 of its 1692 lines of code are new or changed and 1217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_write_value.v, with its module paths and module names changed; 32 of its 88 lines of code are new or changed and 1636 lines of the source are left out. *)
(* write_value (fs.asan-ubsan 0x84010, preset_file.c:525-575): the CLOSING theorem of the image-B ASan walk of fs's recursive
   value writer, against lib/B/FSH_Fn_writer.v's write_value_spec_at (statement set a working branch
   50968be8342: no CTX binder and no `In (raZ regs :: spine ch) CTX` premise; the buffer-head-in-U premise).
   The image-B twin of image A's closing section (a Theorem Labs lane's lib/A/FSW_write_value.v, wv_spec_or / wv_level /
   write_value_holds; CTX-dropped text a working branch 1a5dc5b2e7c:1812-1863, CTX text
   a working branch e64687560bd:1768-1817). The arm form (wv_chain_o, wv_post, wv_spec_on, wv_spec_of_arms) and
   the leaf arms wv_null / wv_false / wv_true / wv_str are lib/B/FSW_write_value_entry.v's (a Theorem Labs lane); wv_num is
   lib/B/FSW_write_value_num.v's (a Theorem Labs lane); wv_arr / wv_obj are lib/B/ZZwvB_cont.v's (a Theorem Labs lane). The callees are
   Section hypotheses (put_spec, put_string_spec, indent_spec at image B, and the strlen interceptor's
   astrlen_realizesU at B's PC_strlen 0x426c4), with the image facts IMG and the shadow-base cells HSS, as in image A's
   theorem.
   Rule 24: proves function write_value (image B, fuzz_state.asan-ubsan 0x84010). Reuse search (a Theorem Labs lane 04:2xZ, re-run
   by a Theorem Labs lane 06:22Z, proof-index unpiped): write_value: 14 named, 15 by address, 4 related, 8 lemma(s), all
   fuzz_state / fuzz_preset PLAIN and UBSAN proofs (lib/Prog, lib/U/Prog) or other projects' write_value; 0x84010: 0 hits
   (exit 1). 579 named cold heads searched: none proves write_value_spec_at for image B. The bespoke image-B proofs
   (a working branch) are templates only; no bridge (a Theorem Labs lane 04:50Z). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI04 YI16 YK06 YO09 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v FSH_Base FSH_Rt FSPstat FSH_Fn_writer.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSW_write_value_entry FSW_write_value_num ZZwvB_cont.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the shadow-base cells (FSH_Base.FsShadowSyms) and the image facts (FSH_Rt.fs_img_facts), as in image A's theorem *)
Hypothesis HSS : FsShadowSyms B.
Hypothesis IMG : fs_img_facts tfibsegs B.

(* ================= the callees, as Section hypotheses (image A's theorem takes the same four) ================= *)
Hypothesis HPUT : put_spec B tfibsegs.
Hypothesis HPS : put_string_spec B tfibsegs.
Hypothesis HIND : indent_spec B tfibsegs.
(* the strlen interceptor's contract (FSH_Gen.astrlen_realizesU at image B's PC_strlen 0x426c4; FSH_Rt.FsRt.fr_strlen) *)
Hypothesis HSLEN : astrlen_realizesU tfibsegs B PC_strlen.

(* ================= the closing theorem: all seven arms, every level ================= *)
Lemma wv_spec_or : forall (P1 P2 : PjTree.jv -> Prop) k,
  wv_spec_on B P1 k -> wv_spec_on B P2 k -> wv_spec_on B (fun t => P1 t \/ P2 t) k.
Proof.
intros P1 P2 k H1 H2 ly S U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail [Ht|Ht];
  [exact (H1 ly S U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail Ht)
  |exact (H2 ly S U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail Ht)].
Qed.
(* one level: the leaf arms, and the container arms over the next level. Each arm is applied with its callee contracts
   and image facts taken from this Section's hypotheses (an imported arm is quantified over the ones it uses). The
   container arms' recursive call is write_value at level S k; at k = 2 they are vacuous (depth (JArr _) >= 1), and the
   guard k < 2 keeps level 2 from asking for itself (2 - 3 = 2 - 2 in nat). *)
Lemma wv_level : forall k, ((k < 2)%nat -> write_value_spec_at B tfibsegs (S k)) ->
  write_value_spec_at B tfibsegs k.
Proof.
intros k IH.
apply (wv_spec_of_arms B
  (fun t => t = PjTree.JNull \/ t = PjTree.JFalse \/ t = PjTree.JTrue \/ (exists txt bits, t = PjTree.JNum txt bits))
  (fun t => (exists s, t = PjTree.JStr s) \/ (exists items, t = PjTree.JArr items) \/
            (exists members, t = PjTree.JObj members))
  k).
- intros t. destruct t as [| | |txt bits|s|items|members].
  + left. left. reflexivity.
  + left. right. left. reflexivity.
  + left. right. right. left. reflexivity.
  + left. right. right. right. exists txt, bits. reflexivity.
  + right. left. exists s. reflexivity.
  + right. right. left. exists items. reflexivity.
  + right. right. right. exists members. reflexivity.
- refine (wv_spec_or (fun t => t = PjTree.JNull)
    (fun t => t = PjTree.JFalse \/ t = PjTree.JTrue \/ (exists txt bits, t = PjTree.JNum txt bits)) k _ _);
    [solve [eapply wv_null; eassumption]|].
  refine (wv_spec_or (fun t => t = PjTree.JFalse)
    (fun t => t = PjTree.JTrue \/ (exists txt bits, t = PjTree.JNum txt bits)) k _ _);
    [solve [eapply wv_false; eassumption]|].
  refine (wv_spec_or (fun t => t = PjTree.JTrue) (fun t => exists txt bits, t = PjTree.JNum txt bits) k _ _).
  + solve [eapply wv_true; eassumption].
  + solve [eapply wv_num; eassumption].
- refine (wv_spec_or (fun t => exists s, t = PjTree.JStr s)
    (fun t => (exists items, t = PjTree.JArr items) \/ (exists members, t = PjTree.JObj members)) k _ _);
    [solve [eapply wv_str; eassumption]|].
  refine (wv_spec_or (fun t => exists items, t = PjTree.JArr items) (fun t => exists members, t = PjTree.JObj members)
    k _ _).
  + solve [eapply wv_arr; eassumption].
  + solve [eapply wv_obj; eassumption].
Qed.
(* write_value_spec_at at every level: level 2 (leaves only), then 1, then 0 *)
Theorem write_value_holds : forall k, write_value_spec_at B tfibsegs k.
Proof.
assert (H2 : forall k, (2 <= k)%nat -> write_value_spec_at B tfibsegs k).
{ intros k Hk. apply wv_level. intros Hlt. exfalso. lia. }
assert (H1 : write_value_spec_at B tfibsegs 1).
{ apply wv_level. intros _. apply H2. lia. }
intros k. destruct k as [|[|k]].
- apply wv_level. intros _. exact H1.
- exact H1.
- apply H2. lia.
Qed.
End W.

(* ================= write_value, every level: image A's top theorem, form and name ================= *)
(* image A's lib/A/ZZwv_arm.v:194 write_value_spec_holds (S0 2b91e53c5db), binder list and premises word for word, over
   image B's modules, so that ENTRY composes both images the same way. Image B's write_value_holds already has the
   container arms discharged (ZZwvB_cont.wv_arr / wv_obj); what remains are the callees' specs and the image / runtime
   facts, each owned elsewhere. *)
Theorem write_value_spec_holds {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} (B : asyms) :
  FsShadowSyms B -> fs_img_facts tfibsegs B ->
  put_spec B tfibsegs -> indent_spec B tfibsegs -> put_string_spec B tfibsegs ->
  astrlen_realizesU tfibsegs B PC_strlen ->
  forall k, write_value_spec_at B tfibsegs k.
Proof.
intros HSS HIMG HPUT HIND HPS HSLEN.
exact (write_value_holds B HSS HIMG HPUT HPS HIND HSLEN).
Qed.

About write_value_holds.
Print Assumptions write_value_holds.
Print Assumptions write_value_spec_holds.
