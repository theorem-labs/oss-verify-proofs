(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_knock from proofs/cgif/cgif_file_fuzzer/lib/A/AD2o.v and AD2p.v at
   c8557374ad2e. This file is knock's closing assembly of lib/A/KnockClose.v's parts (rule 24: no function proved; kind:
   assembly): it instantiates KnockClose's asan Section at closed parts, so fuzz_knock's two ASan statements rest on no
   Section hypothesis. cgif's AD2o keeps three program-walk hypotheses that its AD2p discharges; knock's program contract
   (lib/A/APgLib.v knock_lib_x_all) takes none, so the closing is one file and there is no AD2p. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/AD2o.v at origin/ossv/recipes 6ebe35ba632; taken for
   reac-pw/fuzz_pin image A: it instantiates lib/A/PinClose.v's asan Section (its 13 arguments, the trace tables of
   lib/A/ACej.v / ACejTfib.v in places 8-12); the program contract is lib/A/PPgLib.v's (pin_lib_contract_x_all_tfib over
   pin_lib_x_all, in the roles of APgLib's knock_ names), and its proof pin_lib_x is stated here, from the program walks'
   top lemmas with their wrapper, allocator and image hypotheses bound at pin's B (lib/A/PinWrapBinders.v), in the place
   knock's APgLib.v:305-312 proves knock_lib_x_all; the allocator parts are lib/A/PinAllocClose.v's; the shape equation
   pin_ag_sil_shape_eq is stated for image B; names knock_* -> pin_*, module paths changed. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_pin Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YG00 YG01 YG0f YG0d YC5d YCbp YM05.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YG0q YO09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require AWalkFw0 AB01 AB12 AB1n ACej ACejTfib AD2l AD2m AD1k AD1o AD1l AD1j AD1q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require AD1u ACeh AE2k.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require PPgLib PPgMain PPgParse PPgCat PPgRow PPgLeaf.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require PinAllocClose PinWrapBinders PinAsanTop PinClose.
Local Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.
#[local] Existing Instance AD1q.pin_ag_sil_shape.
(* the read-only window below the sink head, the class the program walks take as a Context *)
#[local] Existing Instance PinWrapBinders.pin_ROB.

(* The shape the core's driver (lib/A/AD1q.v) states is the shape ASAN_T states (lib/A/PinAsanTop.v pin_shape, the
   agreement shape of lib/AgreePin.v). *)
Lemma pin_ag_sil_shape_eq : AD1q.pin_ag_sil_shape = PinAsanTop.pin_shape.
Proof. reflexivity. Qed.

(* ============================== the program contract's closed form ==============================
   lib/A/PPgLib.v's pin_lib_x_all, in the place fuzz_knock's lib/A/APgLib.v:280-312 proves knock_lib_x_all: the harness
   walk (lib/A/PPgMain.v pin_lib_x_A) at B := AD2l.TfibB, with its Section hypotheses bound at TfibB: the core's laws,
   the side stack for frames, the wrappers and the read-only objects' fact pin_ro_law (lib/A/PinWrapBinders.v), the
   sink's image laws (lib/A/AD1u.v tfib_AIL), the callees at their contracts (lib/A/PPgRow.v, PPgParse.v with
   PPgCat.v's reac_box_catalogue, PPgLeaf.v), the meter's laws (ameter_triv, lib/Reusable/YCbp.v) and XL0_HXL. The
   allocator's malloc and free facts are premises here (fuzz_ctrl's form, origin/ossv/recipes 7097a4593001
   proofs/libreac/fuzz_ctrl/lib/A/ACtl.v:1184-1185): pin_driver_TfibB passes the ones PinClose's H_DRIVER receives,
   and pin_lib_x passes lib/A/PinAllocClose.v's. *)
Ltac pin_bind AM AF LEAF :=
  first [ exact PinWrapBinders.pin_tfib_lib | exact PinWrapBinders.pin_LAWS | exact PinWrapBinders.pin_ML
        | exact PinWrapBinders.pin_ASM0 | exact PinWrapBinders.pin_ASM1 | exact PinWrapBinders.pin_SMP
        | exact PinWrapBinders.pin_ASF | exact PinWrapBinders.pin_FFL
        | exact (AD1u.tfib_AIL AD2l.TfibB AD2l.TfibB_syms)
        | exact AM | exact AF
        | exact PinWrapBinders.pin_AMEMCPY | exact PinWrapBinders.pin_AMEMCHR | exact PinWrapBinders.pin_ASTRLEN
        | exact PinWrapBinders.pin_ABCMP | exact PinWrapBinders.pin_ASTRCSPN | exact PinWrapBinders.pin_ASTRNCMP
        | exact PinWrapBinders.pin_ro_law_TfibB
        | exact ameter_triv_laws | exact ameter_triv_fs_laws | exact PPgLib.XL0_HXL | exact LEAF ].
Section f. Context {rc : YM05.RunCeil} {LS : YO09.lib_shape}.
Lemma pin_lib_x_of :
  (forall fx : YK11.FPState, @amalloc_realizes fx rc AWalkFw0.tfibsegs AD2l.TfibB) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc AWalkFw0.tfibsegs AD2l.TfibB) ->
  @PPgLib.pin_lib_x_all rc LS.
Proof.
intros AM AF LEAF fx.
specialize (AM fx). specialize (AF fx).
eapply PPgMain.pin_lib_x_A;
  first [ pin_bind AM AF LEAF
        | (eapply PPgRow.pin_pb_rowX; pin_bind AM AF LEAF)
        | (eapply PPgParse.pin_pb_parseX_A;
             first [ pin_bind AM AF LEAF | (eapply PPgCat.pin_pb_catalogueX; pin_bind AM AF LEAF) ])
        | (eapply PPgLeaf.pin_pb_check_knownX; pin_bind AM AF LEAF)
        | (eapply PPgLeaf.pin_pb_check_rowX; pin_bind AM AF LEAF)
        | (eapply PPgLeaf.pin_pb_check_labelX; pin_bind AM AF LEAF) ].
Qed.
Theorem pin_lib_x : @PPgLib.pin_lib_x_all rc LS.
Proof. exact (pin_lib_x_of (PinAllocClose.pin_amalloc_closed rc) (PinAllocClose.pin_afree_closed rc)). Qed.
End f.

(* PinClose's H_DRIVER at B := AD2l.TfibB, from lib/A/AD1q.v DRV_MAINX (the core's driver walk). The adapter bridges two
   differences. (1) H_DRIVER hands over the three allocator parts for every FPState; DRV_MAINX takes them at YK11.fx0,
   and the program contract takes the free and malloc parts at every FPState (fuzz_ctrl's form). (2) DRV_MAINX takes the
   driver's other parts, which H_DRIVER leaves inside itself; they are supplied here: TfibSyms (AD2l.TfibB_syms), the read
   check (AD2m.tfib_ARDCHK), the program contract LIBX (pin_lib_x at ameter_triv / XL0 / RO_LO..RO_HI, through
   PPgLib.pin_lib_contract_x_all_tfib; its LEAF holds by eq_refl at AD1q.pin_ag_sil_shape), MT_FREE (ameter_triv's mo_ok
   is True), RO_IN (RO_LO..RO_HI is in_ro_tfa's second disjunct) and the stdio sites (AD1k, AD1o, AD1l, AD1j). H_DRIVER's
   two trace premises are not used: AD2l.TfibB_syms carries them. *)
Lemma pin_driver_TfibB : forall rc : YM05.RunCeil,
  (forall fx : YK11.FPState, @amalloc_realizes fx rc AWalkFw0.tfibsegs AD2l.TfibB) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc AWalkFw0.tfibsegs AD2l.TfibB) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc AWalkFw0.tfibsegs AD2l.TfibB OCpy (pc_wrap_memcpy (as_code AD2l.TfibB))) ->
  universe_ok (as_universe AD2l.TfibB) ->
  (forall t, In t ACejTfib.Tfib_drv_traces -> In t (as_universe AD2l.TfibB)) ->
  PinClose.drv_mainA AB01.HS_tfib AB12.TFIB rc.
Proof.
  intros rc AM AF AI _ _.
  exact (@AD1q.DRV_MAINX rc AD2l.TfibB AD2l.TfibB_syms (AM YK11.fx0) (AF YK11.fx0) (AI YK11.fx0)
    (AD2m.tfib_ARDCHK AD2l.TfibB AD2l.TfibB_syms)
    ameter_triv PPgLib.XL0 PPgLib.XL0 PPgLib.RO_LO PPgLib.RO_HI (fun _ _ => I) (fun a H => or_intror H)
    (PPgLib.pin_lib_contract_x_all_tfib AD2l.TfibB ameter_triv PPgLib.XL0 PPgLib.XL0 PPgLib.RO_LO PPgLib.RO_HI
      (@pin_lib_x_of rc AD1q.pin_ag_sil_shape AM AF (fun _ _ _ => eq_refl)))
    AD1k.xst AD1k.tfib_xst_frame
    (AD1o.tfib_printf_first AD2l.TfibB AD2l.TfibB_syms (YG0q.AR_laws_ok AWalkFw0.tfibsegs AD2l.TfibB) AD2l.TfibB_syms)
    (AD1o.tfib_printf_next AD2l.TfibB AD2l.TfibB_syms (YG0q.AR_laws_ok AWalkFw0.tfibsegs AD2l.TfibB) AD2l.TfibB_syms)
    AD1k.est AD1k.tfib_est_img AD1k.tfib_est_frame
    (AD1k.tfib_fwrite_site AD2l.TfibB AD2l.TfibB_syms (YG0q.AR_laws_ok AWalkFw0.tfibsegs AD2l.TfibB))
    (AD1k.tfib_refused_site AD2l.TfibB AD2l.TfibB_syms (YG0q.AR_laws_ok AWalkFw0.tfibsegs AD2l.TfibB) AD2l.TfibB_syms)
    (AD1l.tfib_fprintf_open_site AD2l.TfibB AD2l.TfibB_syms (YG0q.AR_laws_ok AWalkFw0.tfibsegs AD2l.TfibB) AD2l.TfibB_syms)
    (AD1l.tfib_fprintf_rderr_site AD2l.TfibB AD2l.TfibB_syms (YG0q.AR_laws_ok AWalkFw0.tfibsegs AD2l.TfibB) AD2l.TfibB_syms)
    (AD1l.tfib_fprintf_usage_site AD2l.TfibB AD2l.TfibB_syms (YG0q.AR_laws_ok AWalkFw0.tfibsegs AD2l.TfibB) AD2l.TfibB_syms)
    (AD1j.tfib_exit_site AD2l.TfibB AD2l.TfibB_syms (YG0q.AR_laws_ok AWalkFw0.tfibsegs AD2l.TfibB))).
Qed.

(* PinClose's asan Section at its parts, in its order: HS_TBL / TFIB_TBL / H_STARTUP from the start-up certificate
   (AB01.HS_tfib, AB12.TFIB, AB1n.tfib_startup_T1), B := AD2l.TfibB, the allocator parts from lib/A/PinAllocClose.v, the
   trace tables of lib/A/ACej.v / ACejTfib.v with H_TRACES_B by reflexivity, and H_DRIVER from pin_driver_TfibB. *)
Theorem ASAN_T_closed : PinAsanTop.ASAN_T.
Proof.
  exact (PinClose.ASAN_T_of_parts AB01.HS_tfib AB12.TFIB AB1n.tfib_startup_T1 AD2l.TfibB
    PinAllocClose.pin_amalloc_closed PinAllocClose.pin_afree_closed PinAllocClose.pin_aicpy_closed
    ACej.Tfib_universe ACej.Tfib_universe_ok eq_refl ACejTfib.Tfib_drv_traces ACejTfib.Tfib_universe_drv
    pin_driver_TfibB).
Qed.
Theorem pin_asan_agrees_closed : Statements.asan_agrees.
Proof. exact (PinAsanTop.asan_agrees_of_asan_side ASAN_T_closed). Qed.
Theorem pin_asan_halts_closed : Statements.asan_halts.
Proof. exact (PinAsanTop.asan_halts_of_asan_side ASAN_T_closed). Qed.
