(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require ShapeAlg SpinAlg Spec SpecNoKill AsanInit.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import ImgParams MainDefs MainTree MainAsm Img_src13 Main_src13.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import TopLevelGen.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Plain Require Import PImg.
Import ListNotations.
Open Scope Z_scope.

Definition SPEC : list (list byte) -> Fs.Fs -> list event -> Prop := Common.Spec.spec.
Definition TSU : tfam := fun inp _ => SPEC (in_argv inp) (in_fs inp).

Lemma SPEC_nil : forall argv fs, SPEC argv fs [].
Proof.
  intros argv fs. unfold SPEC, Common.Spec.spec.
  assert (D : forall msg f, Common.Spec.t_die msg f []) by (intros; apply Common.ShapeAlg.t_emit_has_nil).
  assert (A2 : forall (A B : Common.ShapeAlg.TSet), A [] -> Common.ShapeAlg.t_alt2 A B []).
  { intros A B HA. left. exact HA. }
  destruct argv as [|a0 [|path [|x l]]]; try apply D.
  destruct (4096 <=? length path)%nat; [apply D|].
  destruct (Common.Spec.list_byte_eqb path []); [apply D|].
  destruct (Common.Spec.list_byte_eqb path Common.Spec.dot_path); [apply A2, D|].
  destruct (fs_lookup fs path); [apply A2, D | apply D].
Qed.

Lemma NOKILL : tfam_no_kill TSU.
Proof.
  intros inp en tr H sig fs Hin.
  pose proof (Common.SpecNoKill.spec_nokill (in_argv inp) (in_fs inp) tr H) as HF.
  rewrite Forall_forall in HF. exact (HF _ Hin).
Qed.

Section Plain.
  Variable CS : certs IP_src13.

  Lemma PLAIN : side_ok psegs p_init_pc p_phdrs source_alloc_limit TSU.
  Proof.
    intros [rsp rbrk rmb rdr] inp Hen Hv.
    assert (Hsv48 : in_va_size inp = Sv48) by (destruct Hv as (_ & _ & _ & _ & _ & _ & _ & _ & H & _); exact H).
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
    destruct Hen as [Hrsp [Hrbrk [Hrmb Hrfit]]].
    destruct Hv as [Hargv [Henvp [Hfs [_ [[Huid Hgid] [Hnof [Hsig [Hhw _]]]]]]]].
    destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw abt va urnd tmp].
    cbn [in_va_size in_argv in_envp in_fs in_uid in_gid in_nofile in_hwcap] in *. subst va.
    pose proof (realizes_spec_src13 rsp rdr rbrk rmb argv envp (fs_seed_tmp fs tmp) stdin uid gid hw groups net nofile sigmask abt urnd
                  Hrsp Hrbrk Hargv Henvp Hrfit Huid Hhw CS) as HR.
    split.
    - intros tr. exact (Common.SpinAlg.srealizes_obs_iff _ _ _ HR tr).
    - exact (Common.SpinAlg.srealizes_no_error _ _ _ HR).
  Qed.
End Plain.
