(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import ShapeAlg SpinAlg CfgStep RegEqv AsanInit.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv NodesCfg NodesCfgA ITreeCfg Ceiling.
From OSSVerify.Proofs.openssl.punycode.lib.A Require SrzEqv.
From OSSVerify.Proofs.openssl.punycode.lib Require Import TopLevel Obligations.
From OSSVerify.Proofs.openssl.punycode.lib Require Spec.
From OSSVerify.Proofs.openssl.punycode.lib.Top Require Import TopBridge.
From OSSVerify.Proofs.openssl.punycode.lib.Spec Require Import Prog Canon CanonSpec ModelInv UnforcedK LB_Main ProgDetIface ProgDet ProgNoEnomem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

(* [comment removed for export] *)
Lemma init_cfg_eqv : forall segs pc ph en inp mo,
  RegEqv.cfg_eqv (mkCfg (ms0 segs pc ph en inp) mo)
                 (mkCfg (init_machine_state segs pc ph (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) mo).
Proof.
  intros segs pc ph en inp mo. split; [| reflexivity]. cbn [cfg_ms]. unfold ms0, init_ms. rewrite init_mkst. unfold mkst, MS, regupd.
  split; [intros r _; symmetry; apply init_regs_mkR|]. repeat split; reflexivity.
Qed.

Section Lane.
Variable segs : list Segment.
Variable rstage : Z.
Variable pc : N.
Variable ph : PhdrInfo.
Variable lim : Z.
Hypothesis Hlow : segs_low segs.
Hypothesis Hlim : (KLIM + SMALLREQ <= lim)%Z.
Hypothesis Himpl : forall (en : ExecEntry) (inp : ProcInput),
  valid_entry (mkImage segs pc ph) en inp -> valid_input_w inp ->
  impl segs (at_node segs) (the_prog segs rstage inp en) (epost the_post) (ms0 segs pc ph en inp).

Theorem plain_lane_realizes : image_realizes segs pc ph lim Spec.spec.
Proof.
  intros sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask urnd Hsp Hbrk Hmb Hargv Henvp Hfit Huid Hfs Hhw.
  set (inp := AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd).   (* [comment removed for export] *)
  set (en := mkEntry sp brk0 mbase rdraw).
  assert (Hvi : valid_input_w inp) by (split; [exact Hargv| split; [exact Henvp| reflexivity]]).
  assert (Hve : valid_entry (mkImage segs pc ph) en inp).
  { rewrite (valid_entry_sv48 _ _ _ (eq_refl : in_va_size inp = Sv48)). cbn. exact (conj Hsp (conj Hbrk (conj Hmb Hfit))). }
  pose proof (run_ceiling_eq segs pc ph en inp eq_refl Hve) as Hceil.
  pose proof (prog_model_ok (CE__ := run_ceiling en) segs rstage pc ph lim en inp Hlow Hve Hvi Hceil) as [Hl_a Hs_a].
  pose proof (prog_no_enomem_any segs rstage pc ph lim Hlow Hlim) as HNE.
  pose proof (HNE en inp Hve Hvi) as Hne.
  pose proof (prog_det_gen segs rstage pc ph lim Hlow HNE en inp Hve Hvi) as Hdet.
  pose proof (Himpl en inp Hve Hvi) as Hi.
  unfold the_prog in *.
  set (t := @prog (run_ceiling en) segs rstage (in_argv inp)) in *.
  set (mo := mo0 segs lim en inp) in *.
  pose proof (leaves_unreachable_a_c t mo Hne Hl_a) as Hl.
  pose proof (tsafe_nsafe_c t mo Hne (tsafe_a_c nsafe t mo Hne Hs_a)) as Hs.
  assert (HT : tree_at node segs (at_node segs) nstep_c minv nsafe_c t (epost the_post) (ms0 segs pc ph en inp) mo).
  { split; [exact Hi|]. split; [exact Hl|]. split; [apply mo0_not_halted|]. split; [apply mo0_minv| exact Hs]. }
  pose proof (impl_realizes node segs (at_node segs) nstep_c nexit minv nsafe_c (nodes_sound_cfg segs) t _ _ _ HT) as HR.
  assert (Heq : t_eq (tree_shape node nstep_c nexit t mo) (Spec.spec argv fs)).
  { eapply t_eq_trans; [| apply canon_spec_eq]. intros tr. exact (Hdet tr). }
  change (init_config segs pc ph sp brk0 mbase rdraw lim inp)
    with (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp).
  rewrite init_config_eq.
  apply (SrzEqv.srealizes_of_realizes_eqv segs (mkCfg (ms0 segs pc ph en inp) mo) _ (Spec.spec argv fs)).
  - exact (rz_conseq segs _ _ _ HR Heq).
  - apply init_cfg_eqv.
Qed.

End Lane.
