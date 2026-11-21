(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch stated over the run's whole input; the start-up per CONFIG_RSEQ value and the new auxv layout). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.simdjson.fuzz_atpointer.images Require Import Asan.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import
  Zg2 Z7g CatSim Zp6 Z10r Zp7 Z10a Z14
  Z1b Z1e Z1c.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zg2.
Local Instance asanreflect_fx : Zg2.FPState := Zg2.fx0.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Z78 Z7a Z7b Z2z Z2y Z33 Z1s Z30.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Z3g.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Z2n Z3c Z2t Z2w Z3m.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Z1f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section AsanInstance.
  (* LPS 727298f3: the run, as AS/Z2w.v's Section GenericInit (and AS/Z1s.v's
     Section Init) names it: the run's whole launch input [inp], and every
     launch hypothesis those sections read.  [eassumption] places each where
     the instances need it. *)
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable FS0 : Fs.Fs.
  Variable inp : ProcInput.
  #[local] Notation INP := inp.
  #[local] Notation argv := (in_argv inp).
  #[local] Notation envp := (in_envp inp).
  #[local] Notation uid := (in_uid inp).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hzr : Z1f.zero_random_draw (ed_random rdraw).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  (* the launch's CONFIG_RSEQ flag, read off the kernel build: never pinned *)
  #[local] Notation RZ := (rseq_z (kb_rseq (in_kernel INP))).
  #[local] Notation SINV0a := (SINV0 ASAN_A APH sp rdraw brk0 mbase inp).
  #[local] Notation argH0a := (argH0 sp rdraw inp).

  Section AnySINV.

    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0a E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0a E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen : x_stmt ASEGS ASAN_A NX0 LIMIT RZ SINV argH0a FS0 XEnvScan.
    Proof.
      pose proof asan_img_facts as IMG.
      eapply (init_x_sound_envscan ASEGS ASAN_A APH asan_wx asan_in_hull asan_hull_ok
                W_88b50 W_88b54 W_88b58
                ltac:(cbn [x_envscan x_envscan_k ASAN_A]; lia)
                (fetch_lit _ _ _ _ eq_refl F_88b50) (fetch_lit _ _ _ _ eq_refl F_88b54) (fetch_lit _ _ _ _ eq_refl F_88b58)
                ltac:(repeat split; reflexivity)
                D_88b50 D_88b54 D_88b58); eassumption.
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen : x_stmt ASEGS ASAN_A NX0 LIMIT RZ SINV argH0a FS0 XPnScan.
    Proof.
      pose proof asan_img_facts as IMG.
      eapply (init_x_sound_pnscan ASEGS ASAN_A APH asan_wx asan_in_hull asan_hull_ok
                W_88c0c W_88c10 W_88c14 W_88c18 W_88c1c
                ltac:(cbn [x_pnscan x_pnscan_k ASAN_A]; lia)
                (fetch_lit _ _ _ _ eq_refl F_88c0c) (fetch_lit _ _ _ _ eq_refl F_88c10) (fetch_lit _ _ _ _ eq_refl F_88c14)
                (fetch_lit _ _ _ _ eq_refl F_88c18) (fetch_lit _ _ _ _ eq_refl F_88c1c)
                ltac:(repeat split; reflexivity)
                D_88c0c D_88c10 D_88c14 D_88c18 D_88c1c); eassumption.
    Qed.

    Theorem node_x_sound_XLayout_asan_gen : x_stmt ASEGS ASAN_A NX0 LIMIT RZ SINV argH0a FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.

  Theorem node_x_sound_XEnvScan_asan :
    x_stmt ASEGS ASAN_A NX0 LIMIT RZ SINV0a argH0a FS0 XEnvScan.
  Proof. apply node_x_sound_XEnvScan_asan_gen; first [exact (fun E M H => H) | apply SINV0_frame | apply SINV0_agree]. Qed.

  Theorem node_x_sound_XPnScan_asan :
    x_stmt ASEGS ASAN_A NX0 LIMIT RZ SINV0a argH0a FS0 XPnScan.
  Proof. apply node_x_sound_XPnScan_asan_gen; first [exact (fun E M H => H) | apply SINV0_frame | apply SINV0_agree]. Qed.

  Theorem node_x_sound_XLayout_asan :
    x_stmt ASEGS ASAN_A NX0 LIMIT RZ SINV0a argH0a FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End AsanInstance.
