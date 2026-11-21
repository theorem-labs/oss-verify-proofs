(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Lib Require Import PropExec MState Mem Cells Exec ITree Nodes Decode RegsEquiv Image CTree.
Require OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import ExFlushIface FL4Inst FlLibStmt FlLibIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Plain Require Import PImg RMalloc_iface RF_malloc_spec RF_free_spec F_calloc
  F_printf_iface Stdio_iface F_fprintf_fl F_fwritex_stderr F_stdio_flush F_fwrite F_vfprintf Harness_iface FlLinks FlLinksM FlSafeM Fuzz_bridge_fl PlainMain_asm.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Spec Require Import PState Monad Stdio Driver Prog ProgC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import TopLevel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require TFlDfl TFlDI.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require FlLibIfaceII FlLibIfaceInf FlLibIfaceIsy.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require ICall6 Sync6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Plain Require Import RunDraw.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState InflateState HarnessSmallFacts Prog.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec Require Import FlushStages.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CLOSE.
  Definition FL_TW : bvmap 5 word -> bvmap 5 word -> iptrs -> Z -> Z -> inflate_state -> ZCall -> Z -> (word -> option byte) -> Prop := ICall6.TWF.
  Definition FL_SSAFE : inflate_state -> ZCall -> Prop := Sync6.SSAFE6.
  Definition TW_LOCAL6_T (fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState) : Prop :=
    ltac:(match type of (@fl_lib_ok fx FL_TW FL_SSAFE) with ?A -> _ => exact A end).
  Definition L_DI6_T (fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState) : Prop :=
    ltac:(match type of (@fl_lib_ok fx FL_TW FL_SSAFE) with _ -> ?A -> _ => exact A end).
  Definition L_DFL6_T (fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState) : Prop :=
    ltac:(match type of (@fl_lib_ok fx FL_TW FL_SSAFE) with _ -> _ -> ?A -> _ => exact A end).
  Definition L_II6_T (fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState) : Prop :=
    ltac:(match type of (@fl_lib_ok fx FL_TW FL_SSAFE) with _ -> _ -> _ -> ?A -> _ => exact A end).
  Definition L_INF6_T (fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState) : Prop :=
    ltac:(match type of (@fl_lib_ok fx FL_TW FL_SSAFE) with _ -> _ -> _ -> _ -> ?A -> _ => exact A end).
  Definition L_INB6_T (fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState) : Prop :=
    ltac:(match type of (@fl_lib_ok fx FL_TW FL_SSAFE) with _ -> _ -> _ -> _ -> _ -> ?A -> _ => exact A end).
  Definition L_ISY6_T (fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState) : Prop :=
    ltac:(match type of (@fl_lib_ok fx FL_TW FL_SSAFE) with _ -> _ -> _ -> _ -> _ -> _ -> ?A -> _ => exact A end).
  Let TW_LOCAL6 : forall fx, TW_LOCAL6_T fx := fun _ => @FlLibIfaceInf.TW_LOCAL6_ok.
  Let L_DI6 : forall fx, L_DI6_T fx := fun fx => @TFlDI.L_DI6_ok fx.
  Let L_DFL6 : forall fx, L_DFL6_T fx := fun fx => @TFlDfl.L_DFL6_ok fx.
  Let L_II6 : forall fx, L_II6_T fx := fun fx => @FlLibIfaceII.L_II6_ok fx.
  Let L_INF6 : forall fx, L_INF6_T fx := fun fx => @FlLibIfaceInf.L_INF6_ok fx.
  Let L_INB6 : forall fx, L_INB6_T fx := fun fx => @FlLibIfaceInf.L_INB6_ok fx.
  Let L_ISY6 : forall fx, L_ISY6_T fx := fun fx => @FlLibIfaceIsy.L_ISY6_ok fx.

  Definition FLIB (fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState) : @fl_lib fx :=
    @fl_lib_ok fx FL_TW FL_SSAFE (TW_LOCAL6 fx) (L_DI6 fx) (L_DFL6 fx) (L_II6 fx) (L_INF6 fx) (L_INB6 fx) (L_ISY6 fx).

  Let SSAFE_IN : forall (s : inflate_state) (zc : ZI.ZCall),
    0 <= is_bits s < 40 /\ 0 <= is_hold s < 2 ^ 64 /\ 0 <= is_have s < 2 ^ 31 /\
    - 2 ^ 31 <= is_flags s < 2 ^ 31 /\ 0 <= is_wrap s < 2 ^ 31 /\ 0 <= is_mode s < 2 ^ 31 /\
    Forall (fun b => 0 <= b < 256) (ZI.zc_input zc) /\ zlength (ZI.zc_input zc) < 2 ^ 31 ->
    Sync6.SYNC14 s -> FL_SSAFE s zc := fun _ _ H H' => conj H H'.   (* 1.4: SSAFE6 = the bounds + SYNC14 *)

  Lemma fl_links_closed : forall fx d, 4 <= zlength d <= 2 ^ 20 -> Forall (fun c => 0 <= c < 256) d -> fl_links (FLIB fx) FL4 8%N d.
  Proof.
    intros fx d Hn Hb.
    pose proof (@fl_ds0_eq fx FL_TW FL_SSAFE (TW_LOCAL6 fx) (L_DI6 fx) (L_DFL6 fx) (L_II6 fx) (L_INF6 fx) (L_INB6 fx) (L_ISY6 fx)) as E1.
    pose proof (@fl_is0_eq fx FL_TW FL_SSAFE (TW_LOCAL6 fx) (L_DI6 fx) (L_DFL6 fx) (L_II6 fx) (L_INF6 fx) (L_INB6 fx) (L_ISY6 fx)) as E2.
    pose proof (@fl_dsafe_eq fx FL_TW FL_SSAFE (TW_LOCAL6 fx) (L_DI6 fx) (L_DFL6 fx) (L_II6 fx) (L_INF6 fx) (L_INB6 fx) (L_ISY6 fx)) as E3.
    pose proof (@fl_isafe_eq fx FL_TW FL_SSAFE (TW_LOCAL6 fx) (L_DI6 fx) (L_DFL6 fx) (L_II6 fx) (L_INF6 fx) (L_INB6 fx) (L_ISY6 fx)) as E4.
    change (is0 7) with (is0 FlushStages.KI) in E2.
    pose proof (@fl_ssafe_eq fx FL_TW FL_SSAFE (TW_LOCAL6 fx) (L_DI6 fx) (L_DFL6 fx) (L_II6 fx) (L_INF6 fx) (L_INB6 fx) (L_ISY6 fx)) as E5.
    assert (SSF : ZI.zr_rc (IR1 (FLIB fx) FL4 8%N d) = Z_OK -> fl_ssafe (FLIB fx) (IS1 (FLIB fx) FL4 8%N d) (IZC2 (FLIB fx) FL4 8%N d)).
    { intros R1. replace (fl_ssafe (FLIB fx)) with FL_SSAFE by (symmetry; exact E5).
      apply SSAFE_IN; [exact (safe_ssf (FLIB fx) d Hn Hb E1 E2) | exact (safe_sy14 (FLIB fx) d Hn Hb E1 E2 R1)]. }
    exact (fl_links_of (FLIB fx) d Hn Hb E1 E2
             (safe_d1 (FLIB fx) d Hn Hb E1 E2 E3) (safe_d2 (FLIB fx) d Hn Hb E1 E2 E3) (safe_isf1 (FLIB fx) d Hn Hb E1 E2 E4)
             SSF (safe_isf3 (FLIB fx) d Hn Hb E1 E2 E4)).
  Qed.

  Lemma fprintf_zerr_bridge : forall amsg msg, In (amsg, msg) Fuzz_bridge_fl.ZERR_MSGS -> @Fuzz_bridge_fl.fprintf_zerr_stmt_fl PState amsg msg.
  Proof. intros amsg msg H. exact (F_fprintf_fl.fprintf_zerr_fl amsg msg H). Qed.

  Theorem fuzz_one_closed : forall rc : runConstT, @fuzz_one_stmt rc FL4.
  Proof.
    intros rc.
    exact (@fuzz_one_bridge rc FL4 FLIB 8%N fl_links_closed
             rmalloc_spec_z (rcalloc_spec_proof rmalloc_spec_zz) rfree_spec_proof
             fprintf_zerr_bridge fwritex_stderr_proof stdio_write_flush_proof fwrite_diag_proof towrite_proof).
  Qed.

  Theorem plain_implC_closed : forall (en : ExecEntry) (inp : ProcInput),
      valid_entry (mkImage psegs p_init_pc p_phdrs) en inp ->
      valid_input_either inp ->
      implC psegs (at_node psegs) (progC_tree FL4 psegs PREAD_STAGE inp en) (epost (fun (_ : unit) (_ : machine_state) => True))
            (ms0 psegs p_init_pc p_phdrs en inp).
  Proof. exact (plain_impl FL4 fuzz_one_closed). Qed.
End CLOSE.
