(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import SimInv ExitSim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX Hoare BBFrame SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame ShapeLaws LibTail.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes LibWritev.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_stdio_call U_exit_base U_stdio_defs U_exit U_main_entry U_read_base U_world U_stdio_readerr_defs U_stdio_readerr_tail U_stdio_readerr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_stdio_oomltac.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_stdio_oomtail () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.U.U_stdio_call.SCR_"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.expr"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.kentry"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KWord"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KAlign"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KRange"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KWr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KImg"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BB.SymRun.vals_ev"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.regs_ok"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_readerr_tail.ENV"; "srOOM0"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.know_ok"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_readerr_defs.knRE0"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.realizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.t_die"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.msg_oom"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition KEPT_OOM : list nat := [2; 3; 4]%nat.
Definition srOOM0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_OOM 6.

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x1d4b4 srOOM0 [] knRE0 39.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA knRE0.
Definition ssA0' : sym_state := SS 0x1d4f4 srOOM0 [] knRE0 39.
Definition rA' := Eval vm_compute in run scr0 ssA0'.
(* [comment removed for export] *)
Definition resB : stdio_res := ltac2:(CDefT.buildp (gd_tbl_P_stdio_oomtail ()) "(0.+4<=30.+2.+41>20.(1.+7=790.)(1.+7=790.)(1.+7=790.)(1.=)(1.+1040<.)(1.+13.)(2.$3.(4.#0.)(1.-<0.))(5.$6.(4.#27.)(5.$6.(1.+41>20.)(5.$6.(2.$3.(4.#0.)(1.-<0.))(5.$6.(1.+10800.)(5.$6.(1.+5=0<8.)(5.$6.(4.#2<.)(5.$6.(4.#2=.)(5.$6.(4.#2>.)(5.$6.(1.+1.)(5.$6.(1.+13.)(5.$6.(1.+13.)(5.$6.(4.#32.)(5.$6.(4.#33.)(5.$6.(4.#34.)(5.$6.(4.#35.)(5.$6.(4.#36.)(5.$6.(4.#37.)(5.$6.(4.#38.)(5.$6.(1.+13.)(5.$6.(1.+4<=30.)(5.$6.(4.#1:.)(5.$6.(4.#1;.)(5.$6.(4.#1<.)(5.$6.(4.#1=.)(5.$6.(4.#1>.)(5.$6.(4.#1?.)(5.$6.(4.#20.)(5.$6.(4.#21.)(5.$6.(4.#43.)(5.$6.(4.#44.)(5.$6.(4.#45.)(5.$6.(4.#46.)(7.$6.)))))))))))))))))))))))))))))))))(5.$8.(9.(:.(1.=)+4<=50.)#8.(1.+7=790.))(5.$8.(9.(:.(1.=)+4<=58.)#8.(1.+7=790.))(5.$8.(9.(:.(1.=)+4<=68.)#8.(1.+7=790.))(5.$8.(9.(:.(1.=)+4<=40.)#8.(1.=))(5.$8.(9.(:.(1.=)+4<=38.)#8.(1.=))(5.$8.(9.(:.(1.=)+4<=;8.)#4.(1.+????????????????.))(5.$8.(9.(:.(4.#0.)-;8.)#8.(4.#1;.))(5.$8.(9.(:.(4.#0.)-;0.)#8.(4.#1:.))(5.$8.(9.(:.(4.#0.)-:8.)#8.(4.#19.))(5.$8.(9.(:.(4.#0.)-:0.)#8.(4.#18.))(5.$8.(9.(:.(4.#0.)-98.)#8.(4.#?.))(5.$8.(9.(:.(4.#0.)-90.)#8.(4.#>.))(5.$8.(9.(:.(4.#0.)-88.)#8.(1.+1=4=4.))(5.$8.(;.(4.#0.)+10.)(5.$8.(<.(4.#0.)+7???80000000.+800000000000.)(5.$8.(=.(:.(4.#0.)-800000.)+800000.)(5.$8.(<.(4.#2.)+7???80000000.+800000400000.)(5.$8.(=.(:.(1.=)+4<000.)+32000.)(5.$8.(>.+10000.+4;<=8.)(5.$8.(9.(:.(1.=)+4;<=8.)#8.(1.+7=330.))(5.$8.(>.+4;<>0.+4<=38.)(5.$8.(>.+4<=48.+4<=50.)(5.$8.(>.+4<=60.+4<=68.)(5.$8.(>.+4<=70.+4<=;8.)(5.$8.(>.+4<=;<.+4<?20.)(5.$8.(9.(:.(1.=)+4<?68.)#1.(1.=))(5.$8.(9.(:.(1.=)+5=020.)#4.(4.#5.))(5.$8.(9.(:.(1.=)+7=328.)#4.(1.=))(5.$8.(9.(:.(1.=)+7=330.)#8.(4.#3.))(5.$8.(9.(:.(1.=)+7=353.)#1.(1.=))(5.$8.(9.(:.(1.=)+7=770.)#8.(1.=))(5.$8.(9.(:.(1.=)+7=780.)#8.(1.=))(5.$8.(<.(4.#5.)+1.+3?????.)(5.$8.(>.+7=108.+7=120.)(7.$8.))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
Lemma resB_eq : stdio_call 39 srA knA = Some resB.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition srB0 : list expr := Eval vm_compute in sc_sr resB.
Definition knB0 : list kentry := Eval vm_compute in sc_kn resB.
Definition ssB0 : sym_state := SS 0x41e20 srB0 [] knB0 71.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knB0.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section OomTail.
  Variable sp0 : word.
  Variable BL : list (list byte).
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  (* [comment removed for export] *)
  #[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma oom_sym : ltac2:(CDefT.buildp (gd_tbl_P_stdio_oomtail ()) "Ppc,$?.Pvals,(10.(11.&40.))PR,(12.&5.(11.&40.))PM,P,(11.&40.)(13.(11.&8.))P,(14.(15.$?.R4.+1=4;4.)(15.$?.R4.+1=4?4.))P,(15.$16.(17.(11.&40.)R4.)#27.)P,(15.(11.&40.)(18.R5.#0.)Vsp0,)P,(19.(1:.VBL,R6.)$1;.R5.)P,(1<.$1=.(1:.VBL,R7.)R5.$1>.)(1?.$1=.(20.(21.$22.R7.(23.&40.R9.)R6.(24.$1=.))Vmodel,)(25.$26.(27.Vmodel,)))")
(* [comment removed for export] *).
  Proof.
    intros pc vals R M Hpc HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    assert (STEP : forall T,
      (forall R' M', regs_ok (ENV BL vals) srA R' -> know_ok RSEGS (ENV BL vals) M' knA ->
         realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x41a34) M' (seg_rom RSEGS)) model) T) ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model) T).
    { intros T HT. destruct Hpc as [-> | ->].
      - run_blk scr0 39%nat. apply HT; assumption.
      - run_blk scr0 39%nat. apply HT; assumption. }
    apply STEP. clear STEP HR HK R M. intros R M HR HK.
    (* [comment removed for export] *)
    oom_stdio_exit HL P0 resB_eq Hfd2 (@eq_refl _ (m_fs model)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variables (tid : Z) (R : bvmap 5 word) (M : word -> option byte) (canw : word).   (* [comment removed for export] *)
  Hypothesis Rsp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).
  Hypothesis Rgp : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis Rtp : getr R 4 = Z_to_bv 64 0x5d0c8.
  Hypothesis Mstack : stack_writable M sp0.
  Hypothesis Mimg : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.
  Hypothesis Mgot : cell M 0x4bcd8 8 0x7d330.
  Hypothesis Mcomp : rdn RSEGS M (Z_to_bv 64 0x4cf68) 1 = Some [Z_to_bv 8 0].
  Hypothesis Mtid : cell M 0x5d020 4 tid.
  Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
  Hypothesis Mlock : cell M 0x7d328 4 0.
  Hypothesis Mcanary : rdn RSEGS M (Z_to_bv 64 0x7d330) 8 = Some (word_to_le_bytes 8 canw).
  Hypothesis Mneedlocks : rdn RSEGS M (Z_to_bv 64 0x7d353) 1 = Some [Z_to_bv 8 0].
  Hypothesis Mstdin : cell M 0x7d770 8 0.
  Hypothesis Mofl : cell M 0x7d780 8 0.

  Definition valsOOM : list word := valsRE sp0 sp0 tid R canw.
  Let E : env := ENV BL valsOOM.

  #[using="Type"] Lemma valsOOM_len : length valsOOM = 39%nat.
  Proof. apply valsRE_len. Qed.

  #[using="Type"] Lemma evOOM_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof. intros i Hi. apply (evRE_junk sp0 BL sp0 tid R canw i Hi). Qed.

  Ltac reg_caseOOM :=
    cbn [nth srOOM0 all_regs];
    first [ lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot E (EVar n)) with (ev E n);
              first [ rewrite (evOOM_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact Rgp | exact Rtp
          | rewrite Rsp, alu_add; change (ev E 0) with sp0; unfold v_add; apply bv_eq;
            rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Zplus_mod_idemp_r; f_equal; lia
          | idtac ].

  #[using="Hvsp SPlo SPhi Rsp Rgp Rtp"] Lemma regs_okOOM : regs_ok E srOOM0 R.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseOOM.
  Qed.

  #[using="Hvsp SPlo SPhi Mstack Mimg Mgot Mcomp Mtid Htid Mlock Mcanary Mneedlocks Mstdin Mofl"] Lemma know_okOOM : know_ok RSEGS E M knRE0.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply (know_okRE sp0 BL Hvsp sp0 tid R M canw Mstack Mimg Mgot Mcomp Mtid Htid Mlock Mcanary Mneedlocks Mstdin Mofl); lia.
  Qed.

  #[using="sp0 BL Hvsp Hh Hlazy Hfd2 SPlo SPhi tid canw Rsp Rgp Rtp Mstack Mimg Mgot Mcomp Mtid Htid Mlock Mcanary Mneedlocks Mstdin Mofl E"] Theorem ref_oom_tail : ltac2:(CDefT.buildp (gd_tbl_P_stdio_oomtail ()) "Ppc,$?.P,(14.(15.$?.R1.+1=4;4.)(15.$?.R1.+1=4?4.))(1?.$1=.(20.(21.$22.VR,(23.&40.R2.)VM,(24.$1=.))Vmodel,)(25.$26.(27.Vmodel,)))")
(* [comment removed for export] *).
  Proof.
    intros pc Hpc.
    eapply (oom_sym pc valsOOM R M Hpc valsOOM_len eq_refl regs_okOOM know_okOOM).
  Qed.
End OomTail.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
