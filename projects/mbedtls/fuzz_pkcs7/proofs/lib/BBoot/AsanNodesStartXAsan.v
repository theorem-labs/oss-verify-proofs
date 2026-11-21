(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 after the bzip2 compress target's version (the section takes the run's whole ProcInput, entry point, launch and channel-reader premises; x_stmt takes the CONFIG_RSEQ flag; SINV_frame written out in plain text and the encoded (CDefT) name table removed; the soundness proofs apply the init lemmas by binder name). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape AsanAcctImages.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanPlanImages.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import Asan_code_startx.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section AsanInstance.
  (** #108: the run is AsanInit's whole input (donor: the bzip2/bzip2_compress_target unit's
      K/AS/AsanNodesStartXAsan.v,
      statement and proof shape).  mbedtls' own: the ceiling [bv_unsigned sp] in every [x_stmt]
      (this port's ruling: the fork's usp ceiling), mbedtls' three-clause [SINV_frame], [HULL_cov],
      and the instantiation by binder name.  UNIT: [RZ] is the CONFIG_RSEQ flag as 0/1. *)
  Variable apc : N.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* the entry draw [Run.en_draw] *)
  Variable brk0 mbase : word.
  Variable inp : ProcInput.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hapc : Z.of_N apc = a_entry BOTH.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Huid : valid_id (in_uid inp).
  Hypothesis Hzr : AsanCeil.zero_random_draw (ed_random rdraw).
  Hypothesis Hlaunch : valid_launch inp.
  Hypothesis Hrdr : in_channel_reader inp = true.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.

  Let RZ := rseq_z (kb_rseq (in_kernel inp)).

  Section AnySINV.
    (** any invariant implying SINV0 and stable like it *)
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH apc sp rdraw brk0 mbase inp E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0 sp rdraw inp E a = true -> M' a = M a) ->
      (forall a : word, bv_unsigned sp <= bv_unsigned a -> M a <> None -> M' a <> None) -> SINV E M -> SINV E M'.
    Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen :
      x_stmt ASEGS BOTH NX0 LIMIT RZ (bv_unsigned sp) SINV (argH0 sp rdraw inp) FS0 XEnvScan.
    Proof.
      eapply init_x_sound_envscan with (segs := ASEGS) (A := BOTH) (ph := APH)
        (we1 := W_dd408) (we2 := W_dd40c) (we3 := W_dd410)
        (Fe1 := fetch_lit _ _ _ _ eq_refl F_dd408) (Fe2 := fetch_lit _ _ _ _ eq_refl F_dd40c)
        (Fe3 := fetch_lit _ _ _ _ eq_refl F_dd410)
        (De1 := D_dd408) (De2 := D_dd40c) (De3 := D_dd410)
        (apc := apc) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (mbase := mbase) (inp := inp) (FS0 := FS0)
        (SINV := SINV);
        first [ eassumption | exact asan_wx | exact asan_in_hull | exact asan_hull_ok | exact asan_hull_cov
              | exact asan_img_facts
              | (cbn [x_envscan x_envscan_k BOTH]; lia) | (repeat split; reflexivity) ].
    Qed.

    Theorem node_x_sound_XPnScan_asan_gen :
      x_stmt ASEGS BOTH NX0 LIMIT RZ (bv_unsigned sp) SINV (argH0 sp rdraw inp) FS0 XPnScan.
    Proof.
      eapply init_x_sound_pnscan with (segs := ASEGS) (A := BOTH) (ph := APH)
        (wp0 := W_dd4c4) (wp1 := W_dd4c8) (wp2 := W_dd4cc) (wp3 := W_dd4d0) (wp4 := W_dd4d4)
        (Fp0 := fetch_lit _ _ _ _ eq_refl F_dd4c4) (Fp1 := fetch_lit _ _ _ _ eq_refl F_dd4c8)
        (Fp2 := fetch_lit _ _ _ _ eq_refl F_dd4cc) (Fp3 := fetch_lit _ _ _ _ eq_refl F_dd4d0)
        (Fp4 := fetch_lit _ _ _ _ eq_refl F_dd4d4)
        (Dp0 := D_dd4c4) (Dp1 := D_dd4c8) (Dp2 := D_dd4cc) (Dp3 := D_dd4d0) (Dp4 := D_dd4d4)
        (apc := apc) (sp := sp) (rdraw := rdraw) (brk0 := brk0) (mbase := mbase) (inp := inp) (FS0 := FS0)
        (SINV := SINV);
        first [ eassumption | exact asan_wx | exact asan_in_hull | exact asan_hull_ok | exact asan_hull_cov
              | exact asan_img_facts
              | (cbn [x_pnscan x_pnscan_k BOTH]; lia) | (repeat split; reflexivity) ].
    Qed.

    Theorem node_x_sound_XLayout_asan_gen :
      x_stmt ASEGS BOTH NX0 LIMIT RZ (bv_unsigned sp) SINV (argH0 sp rdraw inp) FS0 XLayout.
    Proof. apply x_sound_layout. Qed.
  End AnySINV.

  (** at SINV0 itself (its frame, agreement and implication are AsanInit's) *)
  Theorem node_x_sound_XEnvScan_asan :
    x_stmt ASEGS BOTH NX0 LIMIT RZ (bv_unsigned sp) (SINV0 APH apc sp rdraw brk0 mbase inp) (argH0 sp rdraw inp) FS0 XEnvScan.
  Proof.
    apply node_x_sound_XEnvScan_asan_gen; first [ eassumption | exact (fun _ _ H => H) | (intros E M M' H1 H2; eapply SINV0_frame; eassumption) | apply SINV0_agree ].
  Qed.

  Theorem node_x_sound_XPnScan_asan :
    x_stmt ASEGS BOTH NX0 LIMIT RZ (bv_unsigned sp) (SINV0 APH apc sp rdraw brk0 mbase inp) (argH0 sp rdraw inp) FS0 XPnScan.
  Proof.
    apply node_x_sound_XPnScan_asan_gen; first [ eassumption | exact (fun _ _ H => H) | (intros E M M' H1 H2; eapply SINV0_frame; eassumption) | apply SINV0_agree ].
  Qed.

  Theorem node_x_sound_XLayout_asan :
    x_stmt ASEGS BOTH NX0 LIMIT RZ (bv_unsigned sp) (SINV0 APH apc sp rdraw brk0 mbase inp) (argH0 sp rdraw inp) FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End AsanInstance.
