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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX Hoare BBFrame SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibTail.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_exit_base U_main_entry U_read_base U_world.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_stdio_readerr_defs U_stdio_readerr_tail.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_stdio_readerr () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.not"; "Stdlib.Lists.List.In"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.BB.SymRun.vals_ev"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.regs_ok"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_readerr_tail.ENV"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_readerr_defs.srRE0"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.know_ok"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_readerr_defs.knRE0"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "Corelib.Init.Nat.add"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.realizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.t_die"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.msg_read_error"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.dot_path"].


(* [comment removed for export] *)
Definition re_ivs : list (Z * Z) :=
  [(0x10000,0x4bcd8); (0x4bce0,0x4cf20); (0x7d108,0x7d120)]%Z.   (* [comment removed for export] *)

Section ReadErr.
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
  #[using="Hvsp Hh Hlazy Hfd2"] Theorem re_tail : ltac2:(CDefT.buildp (gd_tbl_P_stdio_readerr ()) "Ppath,(0.(1.&8.))Ppp,(1.&40.)Pt8,(0.(1.&8.))Pvals,(0.(1.&40.))PR,(2.&5.(1.&40.))PM,P,(1.&40.)(3.(1.&8.))P,(4.(5.(1.&8.)(6.&8.=)R6.))P,(7.(8.(9.(1.&8.)R7.))+3<.)P,(:.$;.(9.(1.&40.)R5.)#27.)P,(:.(1.&40.)(<.R6.#0.)Vsp0,)P,(:.(1.&40.)(<.R7.#2.)R9.)P,(7.(=.&40.Vsp0,)(=.&40.R:.))P,(7.(>.(>.(=.&40.R;.)(8.(9.(1.&8.)R<.)))+8.)(>.(=.&40.Vsp0,)+400000.))P,(?.(10.VBL,R:.)$11.R9.)P,(12.$13.(10.VBL,R;.)R9.$14.)P,(:.(3.(0.(1.&8.)))(15.$13.R:.R>.(16.(9.(1.&8.)R?.)#1.))(17.(0.(1.&8.))(18.(1.&8.)R?.(19.(1.&8.)(6.&8.=)(1:.(1.&8.))))))P,(:.(3.(0.(1.&8.)))(15.$13.R;.(6.&40.(>.(=.&40.R?.)(8.(9.(1.&8.)R10.))))#8.)(17.(0.(1.&8.))R>.))(1;.$13.(1<.(1=.$1>.R=.(6.&40.+1=478.)R<.(1?.$13.))Vmodel,)(20.(21.R11.)(22.Vmodel,)))")
(* [comment removed for export] *).
  Proof.
    intros path pp t8 vals R M Hnonul HPl HL P0 P2 Hpp1 Hpp2 HR HK Hstr Ht8.
    unfold t_die.
    eapply (re_segBC sp0 BL model Hvsp Hh Hlazy path pp (Z.of_nat (length path)) _ t8 vals);
      try eassumption; try lia.
    intros vals' R' M' HL' Q0 Q2 Q113 HR' HK' Hstr'.
    eapply (re_segF sp0 BL model Hvsp Hh Hlazy Hfd2 path pp _ vals'); try eassumption; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variables (pp : word) (tid : Z) (R : bvmap 5 word) (M : word -> option byte) (canw : word).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis Rsp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).
  Hypothesis Rgp : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis Rtp : getr R 4 = Z_to_bv 64 0x5d0c8.
  Hypothesis Rs2 : getr R 18 = pp.
  (* [comment removed for export] *)
  Hypothesis Mstack : stack_writable M sp0.
  Hypothesis Mimg : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.   (* [comment removed for export] *)
  Hypothesis Mgot : cell M 0x4bcd8 8 0x7d330.                      (* [comment removed for export] *)
  Hypothesis Mcomp : rdn RSEGS M (Z_to_bv 64 0x4cf68) 1 = Some [Z_to_bv 8 0].   (* [comment removed for export] *)
  Hypothesis Mtid : cell M 0x5d020 4 tid.
  Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
  Hypothesis Mlock : cell M 0x7d328 4 0.                           (* [comment removed for export] *)
  Hypothesis Mcanary : rdn RSEGS M (Z_to_bv 64 0x7d330) 8 = Some (word_to_le_bytes 8 canw).   (* [comment removed for export] *)
  Hypothesis Mneedlocks : rdn RSEGS M (Z_to_bv 64 0x7d353) 1 = Some [Z_to_bv 8 0].   (* [comment removed for export] *)
  Hypothesis Mstdin : cell M 0x7d770 8 0.                          (* [comment removed for export] *)
  Hypothesis Mofl : cell M 0x7d780 8 0.                            (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis Hpp1 : (bv_unsigned sp0 <= bv_unsigned pp)%Z.

  Definition valsRE : list word :=
    [sp0; pp; pp; canw; pp; Z_to_bv 64 tid] ++ junk_vals R ++ [Z_to_bv 64 0].   (* [comment removed for export] *)
  Let E : env := ENV BL valsRE.

  #[using="Type"] Lemma valsRE_len : length valsRE = 39%nat.
  Proof. unfold valsRE. rewrite !length_app, junk_vals_length. reflexivity. Qed.

  #[using="Type"] Lemma evRE_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold E, ENV. cbn [ev]. unfold valsRE.
    change (6 + i)%nat with (length [sp0; pp; pp; canw; pp; Z_to_bv 64 tid] + i)%nat.
    unfold vals_ev. rewrite app_nth2_plus, app_nth1 by (rewrite junk_vals_length; exact Hi).
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  #[using="Type"] Lemma spxRE_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

  Ltac reg_caseRE :=
    cbn [nth srRE0 all_regs];
    first [ rewrite spxRE_val
          | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot E (EVar n)) with (ev E n);
              first [ rewrite (evRE_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact Rgp | exact Rtp | exact Rs2
          | rewrite Rsp, alu_add; change (ev E 0) with sp0; unfold v_add; apply bv_eq;
            rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Zplus_mod_idemp_r; f_equal; lia
          | idtac ].

  #[using="Hvsp SPlo SPhi Rsp Rgp Rtp Rs2"] Lemma regs_okRE : regs_ok E srRE0 R.
  Proof.
    pose proof SPlo. pose proof SPhi.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseRE.
  Qed.

  #[using="Mimg"] Lemma img_clear_of : forall lo hi, In (lo, hi) re_ivs -> img_clear M lo hi.
  Proof. intros lo hi Hin. exact (proj1 (Forall_forall _ _) Mimg (lo, hi) Hin). Qed.

  Ltac kimg := split; [lia|]; split; [lia|]; apply img_clear_of; cbn; tauto.
  Ltac kcell H := split; [lia|]; split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|];
                 rewrite adenot_lit0; cbn [edenot];
                 first [exact H | rewrite H; reflexivity | idtac].

  #[using="Hvsp SPlo SPhi SPal Mstack Mimg Mgot Mcomp Mtid Htid Mlock Mcanary Mneedlocks Mstdin Mofl Hpp1"] Lemma know_okRE : (bv_unsigned pp + 8 <= bv_unsigned sp0 + 4194304)%Z -> know_ok RSEGS E M knRE0.
  Proof.
    intros Hpp2. pose proof SPlo. pose proof SPhi. pose proof SPal.
    unfold know_ok, knRE0.
    repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [kentry_ok].
    - (* [comment removed for export] *) split; [lia|]. change (edenot E (EVar 0)) with sp0. exact SPal.
    - change (edenot E (EVar 0)) with sp0. lia.
    - (* [comment removed for export] *) split; [apply flat_intro; cbn; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off]. change (edenot E (EVar 0)) with sp0.
      replace (bv_unsigned sp0 + -8388608 + d)%Z with (bv_unsigned sp0 - 8388608 + d)%Z by lia.
      apply Mstack; lia.
    - change (edenot E (EVar 2)) with pp. lia.
    - (* [comment removed for export] *) split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|].
      intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia.
      apply store_ok_data; rewrite u_small by lia; lia.
    - kimg.
    - kcell Mgot.
    - kimg.
    - kcell Mcomp.
    - kcell Mtid.
    - kcell Mlock.
    - kcell Mcanary.
    - kcell Mneedlocks.
    - kcell Mstdin.
    - kcell Mofl.
    - change (edenot E (EVar 5)) with (Z_to_bv 64 tid : word). rewrite u_small by lia. lia.
    - kimg.
  Qed.

  (* [comment removed for export] *)
  #[using="BL Hvsp Hh Hlazy Hfd2 SPlo SPhi SPal tid canw Rsp Rgp Rtp Rs2 Mstack Mimg Mgot Mcomp Mtid Htid Mlock Mcanary Mneedlocks Mstdin Mofl Hpp1 E"] Theorem ref_read_error : ltac2:(CDefT.buildp (gd_tbl_P_stdio_readerr ()) "Ppath,(0.(1.&8.))Pt8,(0.(1.&8.))P,(4.(5.(1.&8.)(6.&8.=)R2.))P,(7.(8.(9.(1.&8.)R3.))+3<.)P,(7.(>.(>.(=.&40.Vpp,)(8.(9.(1.&8.)R4.)))+8.)(>.(=.&40.Vsp0,)+400000.))P,(:.(3.(0.(1.&8.)))(15.$13.VM,Vpp,(16.(9.(1.&8.)R5.)#1.))(17.(0.(1.&8.))(18.(1.&8.)R5.(19.(1.&8.)(6.&8.=)(1:.(1.&8.))))))P,(:.(3.(0.(1.&8.)))(15.$13.VM,(6.&40.(>.(=.&40.Vpp,)(8.(9.(1.&8.)R6.))))#8.)(17.(0.(1.&8.))R5.))(1;.$13.(1<.(1=.$1>.VR,(6.&40.+1=478.)VM,(1?.$13.))Vmodel,)(20.(21.R7.)(22.Vmodel,)))")
(* [comment removed for export] *).
  Proof.
    intros path t8 Hnonul HPl Hpp2 Hstr Ht8.
    eapply (re_tail path pp t8 valsRE R M); try eassumption.
    - apply valsRE_len.
    - reflexivity.
    - reflexivity.
    - apply regs_okRE.
    - apply know_okRE. lia.
  Qed.

  #[using="BL Hvsp Hh Hlazy Hfd2 SPlo SPhi SPal tid canw Rsp Rgp Rtp Rs2 Mstack Mimg Mgot Mcomp Mtid Htid Mlock Mcanary Mneedlocks Mstdin Mofl Hpp1 E"] Corollary ref_read_error_dot : ltac2:(CDefT.buildp (gd_tbl_P_stdio_readerr ()) "Pt8,(0.(1.&8.))P,(7.(>.(=.&40.Vpp,)+9.)(>.(=.&40.Vsp0,)+400000.))P,(:.(3.(0.(1.&8.)))(15.$13.VM,Vpp,#2.)(17.(0.(1.&8.))(19.(1.&8.)(6.&8.+2>.)(19.(1.&8.)(6.&8.=)(1:.(1.&8.))))))P,(:.(3.(0.(1.&8.)))(15.$13.VM,(6.&40.(>.(=.&40.Vpp,)+1.))#8.)(17.(0.(1.&8.))R3.))(1;.$13.(1<.(1=.$1>.VR,(6.&40.+1=478.)VM,(1?.$13.))Vmodel,)(20.(21.$23.)(22.Vmodel,)))")
(* [comment removed for export] *).
  Proof.
    intros t8 Hpp2 Hstr Ht8.
    apply (ref_read_error dot_path t8).
    - cbn. intros [E0|[]]. apply (f_equal bv_unsigned) in E0. vm_compute in E0. lia.
    - cbn. lia.
    - cbn [length dot_path Z.of_nat Pos.of_succ_nat]. lia.
    - exact Hstr.
    - exact Ht8.
  Qed.
End ReadErr.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
