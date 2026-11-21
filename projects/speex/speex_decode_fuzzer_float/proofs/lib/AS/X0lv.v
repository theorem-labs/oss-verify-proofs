(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (asan_node_x_sound_all and the start-up certificate over the launch's ProcInput with the launch premises and the run's CONFIG_RSEQ flag in place of argv/envp/uid/hw and entry_stack_fits; asan_startup removed). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Asan.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0ms.
Local Instance asanreflect_fx : X0ms.FPState := X0ms.fx0.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import
X0mx X0n0 X0jx X0k2 X0k3 X0m4 X0m6 X0m7
X0li X0lh X0ll X0lm X0lj X0kj X0ly
X0l7 X0l9 X0la X0nf X0lc X0ld X0ls X0k8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs := None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

Lemma XN0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, ext_stmt SEGS A nx0 LIMIT XN0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs cs' E R FULL model T _ _ H. discriminate H. Qed.
Lemma XE0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, emit_stmt SEGS A nx0 LIMIT XE0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, ext2_stmt SEGS A nx0 LIMIT XB0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

Section XAll.
  Variable apc : N.
Variable sp : word.
Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable inp : ProcInput.
Variable FS0 : Fs.Fs.
Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hapc : Z.of_N apc = a_entry ASAN_A.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH apc sp rdraw brk0 mbase inp E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw inp E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  (** #108: the plan's CONFIG_RSEQ flag is the run's own, [rseq_z (kb_rseq (in_kernel inp))] *)
  Let RZ := rseq_z (kb_rseq (in_kernel inp)).

  Theorem asan_node_x_sound_all : forall x,
    x_stmt ASEGS ASAN_A NX0 X0kj.LIMIT RZ SINV (argH0 sp rdraw inp) FS0 x.
Proof.
    assert (AH : forall E a, argH0 sp rdraw inp E a = true -> CEIL <= bv_unsigned a)
      by (intros E a H; eapply argH0_high; first [eassumption | exact asan_img_facts]).
    pose proof (argH0_agree sp rdraw inp) as AA.
intros [ | | | | | | | | | | | ].
    - exact (asan_node_x_sound_XIMemset NX0 X0kj.LIMIT RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - exact (asan_node_x_sound_XIMemcpy NX0 X0kj.LIMIT RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - exact (asan_node_x_sound_XMemset NX0 X0kj.LIMIT RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - exact (asan_node_x_sound_XMemcpy NX0 X0kj.LIMIT RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - exact (asan_node_x_sound_XMemIsZero NX0 X0kj.LIMIT RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - eapply node_x_sound_XEnvScan_asan_gen; eassumption.
    - eapply node_x_sound_XPnScan_asan_gen; eassumption.
- apply x_sound_layout.
    - exact (asan_node_x_sound_XIStrncpy NX0 X0kj.LIMIT RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - exact (asan_node_x_sound_XPopFree NX0 X0kj.LIMIT RZ SINV _ AH AA SINV_frame SINV_agree FS0).
    - exact (asan_node_x_sound_XSniff NX0 X0kj.LIMIT RZ SINV _ FS0 asan_wx asan_in_hull asan_hull_ok AH SINV_frame).
- eapply asan_node_x_sound_XHeapSort; eassumption.
Qed.
End XAll.

Section Startup.
  Variable apc : N.

Variable sp : word.
Variable rdraw : EntryDraw.
Variables brk0 mbase : word.
  Variable inp : ProcInput.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk ASEGS brk0.
Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Huid : valid_id (in_uid inp).

  #[local] Notation SINV := (SINV0 APH apc sp rdraw brk0 mbase inp).
  #[local] Notation argH := (argH0 sp rdraw inp).
  #[local] Notation E0a := (E0 sp rdraw brk0 inp).
#[local] Notation LIM := X0kj.LIMIT.
  #[local] Notation RZ := (rseq_z (kb_rseq (in_kernel inp))).
  #[local] Notation fs := (in_fs inp).

Variable IT0 : itab.
Hypothesis IT0_ok : itab_sound ASEGS IT0.

Variable HS_asan : nat -> option acs.
Variable startup_plan : plan.
Variable startup_shape : shape.
Variables KC0 BFUEL FUEL : nat.
Hypothesis startup_cert :
    check ASEGS IT0 ASAN_A NX0 LIM RZ XN0 XE0 XB0 HS_asan KC0 BFUEL FUEL None (asan_a_init RZ) startup_plan = COk startup_shape.

Variable HOLES : nat -> env -> Fs.Fs -> TSet.
Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
Hypothesis HOLES_sound : holes_stmt ASEGS ASAN_A NX0 LIM HS_asan SINV argH HOLES fs.

  Let AA := argH0_agree sp rdraw inp.
  Let SF := SINV0_frame APH apc sp rdraw brk0 mbase inp.
  Let SA := SINV0_agree APH apc sp rdraw brk0 mbase inp.
End Startup.
