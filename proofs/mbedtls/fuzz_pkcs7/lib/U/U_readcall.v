(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells Step Frame RegsExt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX StepTac MemSplit SpecConsts AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX BBFrame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes SysNodes NodesDir.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_exit_base U_main_entry U_fwrite_err U_readcall_defs.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
Ltac mkR_getr_cases HR solve_known :=
  intros r; pose proof (ridx_range r) as Hi;
  rewrite <- (ridx_roundtrip r); set (i := ridx r) in *; clearbody i;
  destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    [ .. | lia];
    lazymatch goal with |- _ = getr ?RB (Z_to_bv 5 (Z.of_nat ?k)) =>
      first
        [ (transitivity (getr RB (Z_to_bv 5 (Z.of_nat k))); [reflexivity|reflexivity])
        | rewrite (HR (Z_to_bv 5 (Z.of_nat k)));
          lazymatch goal with |- _ = edenot _ (sr_get ?L ?rr) =>
            let e := eval vm_compute in (sr_get L rr) in change (sr_get L rr) with e end;
          cbn [edenot]; solve_known ]
    end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_readcall () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "Corelib.Init.Datatypes.None"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.State.FdFile"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.Fs.fs_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.realizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.len_word"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_empty"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "LinuxProcessSemantics.LinuxProcessSem.State.with_fds"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_insert"; "stdpp.bitvector.definitions.bv_add"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "LinuxProcessSemantics.LinuxProcessSem.State.FdDir"; "RocqVerifyHarness.AgentSubmission.BB.StoreOk.mem_grows"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_remove"].


Section RC.
  Variable sp0 : word.
  Variable model : Model.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Variables (R : bvmap 5 word) (M : word -> option byte).
  (* [comment removed for export] *)
  Hypothesis WIN : ltac2:(CDefT.buildp (gd_tbl_P_readcall ()) "Pa,(0.&40.)P,(1.(2.(3.(4.&40.Vsp0,)+800000.)(4.&40.R1.))(5.(4.&40.R1.)(4.&40.Vsp0,)))(6.(7.(8.(0.&8.))(9.$:.VM,R2.)(;.(0.&8.))))")
(* [comment removed for export] *).
  Hypothesis G2 : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).
  Hypothesis G3 : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis G4 : getr R 4 = Z_to_bv 64 0x5d0c8.
  Hypothesis G10 : getr R 10 = Z_to_bv 64 3.

  #[using="Hvsp SPlo SPhi WIN"] Lemma win_store_ok : ltac2:(CDefT.buildp (gd_tbl_P_readcall ()) "Pd,$<.Pm,$=.P,(2.=R2.)P,(2.(>.R3.(?.R2.))+800000.)(7.$10.(11.$:.VM,(12.&40.(>.(3.(4.&40.Vsp0,)+800000.)R4.))R3.)$13.)")
(* [comment removed for export] *).
  Proof.
    intros d m Hd Hm. pose proof SPlo. pose proof SPhi.
    apply store_ok_of_all; rewrite u_small by lia; [lia|]. intros x Hx. apply WIN. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Read.
    Variables (buf n : Z) (p : list byte) (off : word) (data : list byte).
    Hypothesis G1 : getr R 1 = Z_to_bv 64 0x1d334.
    Hypothesis G11 : getr R 11 = Z_to_bv 64 buf.
    Hypothesis G12 : getr R 12 = Z_to_bv 64 n.
    Hypothesis Hn : (1 <= n <= 65536)%Z.
    Hypothesis Hbuf : (0 <= buf)%Z.
    Hypothesis Hbufhi : (buf + n <= bv_unsigned sp0 - 8388608)%Z.   (* [comment removed for export] *)
    Hypothesis BOK : store_ok RSEGS M (Z_to_bv 64 buf) (Z.to_nat n) = true.

    Definition valsRD : list word := [sp0; Z_to_bv 64 buf; Z_to_bv 64 n] ++ junk_vals R.
    Let E : env := Env (vals_ev valsRD) (blobs_ev []).
    #[using="Type"] Lemma valsRD_len : length valsRD = 35%nat.
    Proof. unfold valsRD. rewrite length_app, junk_vals_length. reflexivity. Qed.
    #[using="Type"] Lemma vR0 : vals_ev valsRD 0 = sp0. Proof. reflexivity. Qed.
    #[using="Type"] Lemma vR1 : vals_ev valsRD 1 = Z_to_bv 64 buf. Proof. reflexivity. Qed.
    #[using="Type"] Lemma vR2 : vals_ev valsRD 2 = Z_to_bv 64 n. Proof. reflexivity. Qed.
    Ltac evs := unfold E; cbn [ev eb]; rewrite ?vR0, ?vR1, ?vR2.

    #[using="Type"] Lemma evRD_junk : forall i, (i < 32)%nat -> ev E (3 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
    Proof.
      intros i Hi. unfold E. cbn [ev]. unfold valsRD.
      change (3 + i)%nat with (length [sp0; Z_to_bv 64 buf; Z_to_bv 64 n] + i)%nat.
      unfold vals_ev. rewrite app_nth2_plus.
      unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
    Qed.

    #[using="Hvsp SPlo SPhi G2 G3 G4 G10 G1 G11 G12"] Lemma regs_okRD : regs_ok E sr_RD R.
    Proof.
      pose proof SPlo. pose proof SPhi.
      apply regs_ok_by_index. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
        cbn [nth sr_RD all_regs];
        first [ (cbn [edenot]; first [ reflexivity | exact G1 | exact G3 | exact G4 | exact G10
                                      | (evs; first [exact G11 | exact G12])
                                      | (rewrite G2, alu_add; evs; unfold v_add; apply bv_eq;
                                         rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Zplus_mod_idemp_r; f_equal; lia) ])
              | (lazymatch goal with |- _ = edenot _ (EVar ?k) =>
                   change (edenot E (EVar k)) with (ev E k); rewrite (evRD_junk (k - 3)) by lia; reflexivity end) ].
    Qed.

    #[using="Hvsp SPlo SPhi SPal WIN"] Lemma know_okRD : know_ok RSEGS E M kn_RD.
    Proof.
      pose proof SPlo. pose proof SPhi. pose proof SPal.
      unfold know_ok, kn_RD.
      repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [kentry_ok].
      - split; [lia|]. cbn [edenot]; evs. assumption.
      - cbn [edenot]; evs. lia.
      - split; [apply flat_intro; cbn; lia|].
        intros d m Hd Hm. unfold estart. cbn [a_base a_off]. cbn [edenot]; evs. apply win_store_ok; lia.
    Qed.

    Let bs : list byte := file_read data off (Z_to_bv 64 n).

    #[using="sp0 Hvsp SPlo Hn"] Lemma bs_len : (Z.of_nat (length bs) <= n)%Z.
    Proof.
      pose proof (proj1 (file_read_length_le data off (Z_to_bv 64 n))) as L.
      unfold word_to_nat in L. rewrite u_small in L by lia. subst bs. lia.
    Qed.

    (* [comment removed for export] *)
    #[using="Hvsp Hh Hlazy SPlo SPhi SPal WIN G2 G3 G4 G10 G1 G11 G12 Hn Hbuf Hbufhi BOK E"] Theorem read_file_call : ltac2:(CDefT.buildp (gd_tbl_P_readcall ()) "PK,$14.P,(7.(8.$15.)(16.(17.Vmodel,)(12.&40.+3.))(18.$15.(19.Vp,Voff,)))P,(7.(8.(1:.(0.&8.)))(1;.(1<.Vmodel,)Vp,)(18.(1:.(0.&8.))Vdata,))P,Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)(1=.$:.(1>.(1?.(20.(12.&40.+1=334.)(12.&40.(3.(4.&40.Vsp0,)+80.))(12.&40.+10800.)(12.&40.+5=0<8.)(21.VR,(22.&5.+5.$23.))(21.VR,(22.&5.+6.$23.))(21.VR,(22.&5.+7.$23.))(21.VR,(22.&5.+8.$23.))(21.VR,(22.&5.+9.$23.))(24.(0.&8.)Vbs,)R7.R6.R5.R4.R3.R2.R1.(21.VR,(22.&5.+12.$23.))(21.VR,(22.&5.+13.$23.))(21.VR,(22.&5.+14.$23.))(21.VR,(22.&5.+15.$23.))(21.VR,(22.&5.+16.$23.))(21.VR,(22.&5.+17.$23.))(21.VR,(22.&5.+18.$23.))(21.VR,(22.&5.+19.$23.))(21.VR,(22.&5.+1:.$23.))(21.VR,(22.&5.+1;.$23.))(21.VR,(22.&5.+1<.$23.))(21.VR,(22.&5.+1=.$23.))(21.VR,(22.&5.+1>.$23.))(21.VR,(22.&5.+1?.$23.)))(25.&5.(0.&40.))(12.&40.+1=334.)(12.&20.=)(;.(0.&40.))(26.(26.VM,(27.(3.(4.&40.Vsp0,)+88.))(28.(12.&40.+1=334.)))(27.Vbuf,)Vbs,)(29.$:.))(2:.(2;.(17.Vmodel,)(12.&40.+3.)(19.Vp,(2<.&40.Voff,(24.(0.&8.)Vbs,))))Vmodel,))R:.)(1=.$:.(1>.(2=.$2>.VR,(12.&40.+4731<.)VM,(29.$:.))Vmodel,)R4.)")
(* [comment removed for export] *).
    Proof.
      intros K Hfd Hfs HC.
      pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof bs_len as BL.
      pose proof regs_okRD as HR. pose proof know_okRD as HK.
      (* [comment removed for export] *)
      run_block_gen FUEL_RC STOPS_RC scr0 35%nat true.
      rename EQM into EQMA. rename R0 into RA. rename M0 into MA.
      (* [comment removed for export] *)
      eapply (rz_read_file RSEGS RA _ MA model ECALLW (Z_to_bv 64 3) p off data n); try apply is_ecall_ECALLW.
      - vm_compute. reflexivity.
      - exact Hh.
      - exact Hlazy.
      - regv HR (17 : reg). reflexivity.
      - regv HR (10 : reg). reflexivity.
      - rewrite u_small by lia. lia.
      - exact Hfd.
      - exact Hfs.
      - regv HR (12 : reg). cbn [edenot]. evs. reflexivity.
      - lia.
      - unfold MAX_RW_COUNT. lia.
      - lia.
      - regv HR (11 : reg). cbn [edenot]. evs. rewrite u_small by lia. unfold TASK_SIZE. lia.
      - regv HR (11 : reg). cbn [edenot]. evs. rewrite EQMA.
        eapply store_ok_mono; [apply mem_denot_grows | exact BOK].
      - rewrite v_addi_pc4 by lia.
        (* [comment removed for export] *)
        regv HR (11 : reg). cbn [edenot]. regv HR (12 : reg). cbn [edenot]. evs. fold bs.
        lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mx _) _) _ => set (M2 := Mx) end.
        assert (EQ2 : M2 = write_to_mem (write_to_mem M (wa (bv_unsigned sp0 - 136)) (le8 (Z_to_bv 64 0x1d334))) (wa buf) bs).
        { subst M2. rewrite EQMA. cbn [mem_denot logRDA]. unfold adenot, v_addi, wa, le8. cbn [a_base a_off edenot ev]. evs.
          (* [comment removed for export] *)
          reflexivity. }
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr _ =>
          pose proof (env_app_regs valsRD [len_word bs] (blobs_ev []) sr RA ltac:(rewrite valsRD_len; vm_compute; reflexivity) HR) as HR1 end.
        pose proof (regs_set_a0 _ _ _ (len_word bs) (EVar 35) HR1
                      ltac:(cbn [edenot ev]; rewrite <- valsRD_len, <- (Nat.add_0_r (length valsRD)); rewrite vals_ev_app_r; reflexivity)) as HR2.
        assert (HK2 : know_ok RSEGS (Env (vals_ev (valsRD ++ [len_word bs])) (blobs_ev [])) M2 kn_RDB).
        { unfold know_ok, kn_RDB. pose proof SPal.
          assert (V0 : vals_ev (valsRD ++ [len_word bs]) 0 = sp0) by reflexivity.
          assert (V35 : vals_ev (valsRD ++ [len_word bs]) 35 = len_word bs).
          { rewrite <- valsRD_len, <- (Nat.add_0_r (length valsRD)). rewrite vals_ev_app_r. reflexivity. }
          krdv HK 0%nat (-136)%Z 8%nat W0; [unfold flat, estart; cbn [a_base a_off edenot ev]; evs; lia|].
          unfold adenot, v_addi in W0. cbn [a_base a_off edenot ev] in W0. unfold E in W0. cbn [ev] in W0. rewrite vR0 in W0.
          repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [kentry_ok edenot ev]; rewrite ?V0, ?V35.
          - split; [lia|]. assumption.
          - lia.
          - split; [lia|]. split; [apply flat_intro; cbn [edenot ev]; rewrite ?V0; lia|].
            unfold adenot, v_addi. cbn [a_base a_off edenot ev]. rewrite V0.
            rewrite EQ2. change (write_to_mem ?m0 ?a0 ?b0) with (wbytes m0 a0 b0).
            lazymatch goal with |- context [wbytes (write_to_mem ?m1 ?a1 ?b1) _ _] => change (write_to_mem m1 a1 b1) with (wbytes m1 a1 b1) end.
            unfold wa.
            rewrite rdn_wbytes_out_Z by (split; [lia|]; split; [lia|]; split; [lia|]; split; lia).
            rewrite rdn_wbytes_hit8 by (zsimp; lia). unfold le8. reflexivity.
          - unfold len_word. rewrite u_small by lia. lia. }
        clear HR HR1 HK. rename HR2 into HR. rename HK2 into HK. clearbody M2.
        (* [comment removed for export] *)
        run_block_gen FUEL_RC STOPS_RC scr0 36%nat true.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rn _ ?Mn _) _) _ => rename Rn into RB; rename Mn into MB end.
        cbn [mem_denot] in EQM. subst MB.
        apply (realizes_getr_ext RSEGS
                 (mkR (Z_to_bv 64 0x1d334) (Z_to_bv 64 (bv_unsigned sp0 - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x5d0c8)
                      (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9)
                      (len_word bs) (getr RB (Z_to_bv 5 11)) (getr RB (Z_to_bv 5 12)) (getr RB (Z_to_bv 5 13))
                      (getr RB (Z_to_bv 5 14)) (getr RB (Z_to_bv 5 15)) (getr RB (Z_to_bv 5 16)) (getr RB (Z_to_bv 5 17))
                      (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                      (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)) RB).
        { mkR_getr_cases HR
            ltac:(first [ reflexivity
                        | (rewrite alu_add; change (ev _ 0) with (vals_ev (valsRD ++ [len_word bs]) 0);
                           rewrite vals_ev_app_l by (rewrite valsRD_len; lia); rewrite vR0;
                           unfold v_add; etransitivity; [reflexivity|];
                           apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; try rewrite Zplus_mod_idemp_r; f_equal; lia)
                        | (lazymatch goal with |- _ = ev _ ?k =>
                             change (ev _ k) with (vals_ev (valsRD ++ [len_word bs]) k);
                             first [ (rewrite <- valsRD_len, <- (Nat.add_0_r (length valsRD)) at 1 || idtac); fail
                                   | (rewrite vals_ev_app_l by (rewrite valsRD_len; lia);
                                      change (vals_ev valsRD k) with (ev E k); rewrite (evRD_junk (k - 3)) by lia;
                                      etransitivity; [reflexivity|]; reflexivity)
                                   | (replace k with (length valsRD + 0)%nat by (rewrite valsRD_len; reflexivity);
                                      rewrite vals_ev_app_r; reflexivity) ] end) ]). }
        change (mkst ?Rx ?pc ?Mx ?rom) with (MS Rx bvmap_empty pc (Z_to_bv 32 0) None Mx rom).
        rewrite EQ2. apply HC.
    Qed.

    (* [comment removed for export] *)
    #[using="Hvsp Hh Hlazy SPlo SPhi SPal WIN G2 G3 G4 G10 buf n G1 G11 G12 Hn Hbuf Hbufhi BOK E"] Theorem read_dir_call : ltac2:(CDefT.buildp (gd_tbl_P_readcall ()) "PK,$14.P,(7.(8.$15.)(16.(17.Vmodel,)(12.&40.+3.))(18.$15.$2?.))P,Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)PM',P,(0.&40.)(8.(0.&8.))P,Px,(0.&40.)P,(6.(1.(2.(3.(4.&40.Vsp0,)+90.)(4.&40.R1.))(5.(4.&40.R1.)(3.(4.&40.Vsp0,)+80.))))P,(6.(1.(2.+5=024.(4.&40.R2.))(5.(4.&40.R2.)+5=028.)))(7.(8.(0.&8.))A1.R4.R3.A1.VM,R3.)P,(30.VM,R2.)(1=.$:.(1>.(1?.(20.(12.&40.+1=334.)(12.&40.(3.(4.&40.Vsp0,)+80.))(12.&40.+10800.)(12.&40.+5=0<8.)(21.VR,(22.&5.+5.$23.))(21.VR,(22.&5.+6.$23.))(21.VR,(22.&5.+7.$23.))(21.VR,(22.&5.+8.$23.))(21.VR,(22.&5.+9.$23.))(12.&40.(3.(31.+2.+40.)+1.))R:.R9.R8.R7.R6.R5.R4.(21.VR,(22.&5.+12.$23.))(21.VR,(22.&5.+13.$23.))(21.VR,(22.&5.+14.$23.))(21.VR,(22.&5.+15.$23.))(21.VR,(22.&5.+16.$23.))(21.VR,(22.&5.+17.$23.))(21.VR,(22.&5.+18.$23.))(21.VR,(22.&5.+19.$23.))(21.VR,(22.&5.+1:.$23.))(21.VR,(22.&5.+1;.$23.))(21.VR,(22.&5.+1<.$23.))(21.VR,(22.&5.+1=.$23.))(21.VR,(22.&5.+1>.$23.))(21.VR,(22.&5.+1?.$23.)))(25.&5.(0.&40.))(12.&40.+1=334.)(12.&20.=)(;.(0.&40.))R3.(29.$:.))Vmodel,)R<.)(1=.$:.(1>.(2=.$2>.VR,(12.&40.+4731<.)VM,(29.$:.))Vmodel,)R3.)")
(* [comment removed for export] *).
    Proof.
      intros K Hfd HC.
      pose proof SPlo as Hlo. pose proof SPhi as Hhi.
      pose proof regs_okRD as HR. pose proof know_okRD as HK.
      run_block_gen FUEL_RC STOPS_RC scr0 35%nat true.
      rename EQM into EQMA. rename R0 into RA. rename M0 into MA.
      eapply (rz_read_dir_mapped RSEGS RA _ MA model ECALLW (Z_to_bv 64 3) n); try apply is_ecall_ECALLW.
      - vm_compute. reflexivity.
      - exact Hh.
      - exact Hlazy.
      - regv HR (17 : reg). reflexivity.
      - regv HR (10 : reg). reflexivity.
      - rewrite u_small by lia. lia.
      - exact Hfd.
      - regv HR (12 : reg). cbn [edenot]. evs. reflexivity.
      - lia.
      - lia.
      - regv HR (11 : reg). cbn [edenot]. evs. rewrite u_small by lia. unfold TASK_SIZE. lia.
      - regv HR (11 : reg). cbn [edenot]. evs. rewrite EQMA.
        eapply store_ok_mono; [apply mem_denot_grows | exact BOK].
      - rewrite v_addi_pc4 by lia.
        pose proof (regs_set_a0 _ _ _ (errno_ret EISDIR) (ELit (2 ^ 64 - 21)) HR
                      ltac:(cbn [edenot]; rewrite errno_ret_lit; apply bv_eq; reflexivity)) as HR2.
        clear HR. rename HR2 into HR.
        assert (HK2 : know_ok RSEGS E MA kn_RDD).
        { unfold know_ok, kn_RDD. pose proof SPal.
          krdv HK 0%nat (-136)%Z 8%nat W0; [unfold flat, estart; cbn [a_base a_off edenot ev]; evs; lia|].
          repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [kentry_ok edenot]; evs.
          - split; [lia|]. assumption.
          - lia.
          - split; [apply flat_intro; cbn [edenot ev]; evs; lia|].
            intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. evs. rewrite EQMA.
            eapply store_ok_mono; [apply mem_denot_grows | apply win_store_ok; lia].
          - split; [lia|]. split; [apply flat_intro; cbn [edenot ev]; evs; lia|]. exact W0.
          - split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?(u_small 0) by lia; lia|].
            intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia.
            apply store_ok_data; rewrite u_small by lia; lia. }
        clear HK. rename HK2 into HK.
        run_block_gen FUEL_RC STOPS_RC scr0 35%nat true.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rn _ ?Mn _) _) _ => rename Rn into RB; rename Mn into MB end.
        rename EQM into EQMB.
        apply (realizes_getr_ext RSEGS
                 (mkR (Z_to_bv 64 0x1d334) (Z_to_bv 64 (bv_unsigned sp0 - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x5d0c8)
                      (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9)
                      (Z_to_bv 64 (2 ^ 64 - 1)) (getr RB (Z_to_bv 5 11)) (getr RB (Z_to_bv 5 12)) (getr RB (Z_to_bv 5 13))
                      (getr RB (Z_to_bv 5 14)) (getr RB (Z_to_bv 5 15)) (getr RB (Z_to_bv 5 16)) (getr RB (Z_to_bv 5 17))
                      (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                      (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)) RB).
        { mkR_getr_cases HR
            ltac:(first [ reflexivity
                        | (rewrite alu_add; evs; unfold v_add; etransitivity; [reflexivity|];
                           apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; try rewrite Zplus_mod_idemp_r; f_equal; lia)
                        | (lazymatch goal with |- _ = ev _ ?k =>
                             change (ev _ k) with (ev E k); rewrite (evRD_junk (k - 3)) by lia;
                             etransitivity; [reflexivity|]; reflexivity end) ]). }
        change (mkst ?Rx ?pc ?Mx ?rom) with (MS Rx bvmap_empty pc (Z_to_bv 32 0) None Mx rom).
        apply HC.
        + intros x N1 N2. pose proof (u64_range x). rewrite EQMB. rewrite mem_denot_out.
          2:{ cbn [log_out logRDD]. unfold adenot, v_addi. cbn [a_base a_off edenot]. evs.
              rewrite ?(u_small 0) by lia. repeat split; rewrite ?u_small by lia; lia. }
          rewrite EQMA. apply mem_denot_out.
          cbn [log_out logRDA]. unfold adenot, v_addi. cbn [a_base a_off edenot]. evs.
          rewrite ?(u_small 0) by lia. repeat split; rewrite ?u_small by lia; lia.
        + rewrite EQMB. eapply mem_grows_trans; [|apply mem_denot_grows]. rewrite EQMA. apply mem_denot_grows.
    Qed.
  End Read.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Close.
    Hypothesis G1 : getr R 1 = Z_to_bv 64 0x1d348.

    Definition valsCL : list word := [sp0] ++ junk_vals R.
    Let E : env := Env (vals_ev valsCL) (blobs_ev []).
        #[using="Type"] Lemma vC0 : vals_ev valsCL 0 = sp0. Proof. reflexivity. Qed.
    Ltac evc := unfold E; cbn [ev eb]; rewrite ?vC0.

    #[using="Type"] Lemma evCL_junk : forall i, (i < 32)%nat -> ev E (1 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
    Proof.
      intros i Hi. unfold E. cbn [ev]. unfold valsCL.
      change (1 + i)%nat with (length [sp0] + i)%nat.
      unfold vals_ev. rewrite app_nth2_plus.
      unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
    Qed.

    #[using="Hvsp SPlo SPhi G2 G3 G4 G10 G1"] Lemma regs_okCL : regs_ok E sr_CL R.
    Proof.
      pose proof SPlo. pose proof SPhi.
      apply regs_ok_by_index. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
        cbn [nth sr_CL all_regs];
        first [ (cbn [edenot]; first [ reflexivity | exact G1 | exact G3 | exact G4 | exact G10
                                      | (rewrite G2, alu_add; evc; unfold v_add; apply bv_eq;
                                         rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Zplus_mod_idemp_r; f_equal; lia) ])
              | (lazymatch goal with |- _ = edenot _ (EVar ?k) =>
                   change (edenot E (EVar k)) with (ev E k); rewrite (evCL_junk (k - 1)) by lia; reflexivity end) ].
    Qed.

    #[using="Hvsp SPlo SPhi SPal WIN"] Lemma know_okCL : know_ok RSEGS E M kn_RD.
    Proof.
      pose proof SPlo. pose proof SPhi. pose proof SPal.
      unfold know_ok, kn_RD.
      repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [kentry_ok].
      - split; [lia|]. cbn [edenot]; evc. assumption.
      - cbn [edenot]; evc. lia.
      - split; [apply flat_intro; cbn; lia|].
        intros d m Hd Hm. unfold estart. cbn [a_base a_off]. cbn [edenot]; evc. apply win_store_ok; lia.
    Qed.

    #[using="Hvsp Hh Hlazy SPlo SPhi SPal WIN G2 G3 G4 G10 G1 E"] Theorem close_call : ltac2:(CDefT.buildp (gd_tbl_P_readcall ()) "Pe,$15.PK,$14.P,(7.(8.$15.)(16.(17.Vmodel,)(12.&40.+3.))(18.$15.R2.))P,Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)PM',P,(0.&40.)(8.(0.&8.))P,Px,(0.&40.)P,(6.(1.(2.(3.(4.&40.Vsp0,)+90.)(4.&40.R1.))(5.(4.&40.R1.)(3.(4.&40.Vsp0,)+80.))))(7.(8.(0.&8.))A1.R3.R2.A1.VM,R2.)P,(30.VM,R2.)(1=.$:.(1>.(1?.(20.(12.&40.+1=348.)(12.&40.(3.(4.&40.Vsp0,)+80.))(12.&40.+10800.)(12.&40.+5=0<8.)(21.VR,(22.&5.+5.$23.))(21.VR,(22.&5.+6.$23.))(21.VR,(22.&5.+7.$23.))(21.VR,(22.&5.+8.$23.))(21.VR,(22.&5.+9.$23.))(12.&40.=)R:.R9.R8.R7.R6.R5.R4.(21.VR,(22.&5.+12.$23.))(21.VR,(22.&5.+13.$23.))(21.VR,(22.&5.+14.$23.))(21.VR,(22.&5.+15.$23.))(21.VR,(22.&5.+16.$23.))(21.VR,(22.&5.+17.$23.))(21.VR,(22.&5.+18.$23.))(21.VR,(22.&5.+19.$23.))(21.VR,(22.&5.+1:.$23.))(21.VR,(22.&5.+1;.$23.))(21.VR,(22.&5.+1<.$23.))(21.VR,(22.&5.+1=.$23.))(21.VR,(22.&5.+1>.$23.))(21.VR,(22.&5.+1?.$23.)))(25.&5.(0.&40.))(12.&40.+1=348.)(12.&20.=)(;.(0.&40.))R3.(29.$:.))(2:.(32.(17.Vmodel,)(12.&40.+3.))Vmodel,))R<.)(1=.$:.(1>.(2=.$2>.VR,(12.&40.+472;<.)VM,(29.$:.))Vmodel,)R3.)")
(* [comment removed for export] *).
    Proof.
      intros e K Hfd HC.
      pose proof SPlo as Hlo. pose proof SPhi as Hhi.
      pose proof regs_okCL as HR. pose proof know_okCL as HK.
      run_block_gen FUEL_RC STOPS_RC scr0 33%nat true.
      rename EQM into EQMA. rename R0 into RA. rename M0 into MA.
      eapply (rz_close RSEGS RA _ MA model ECALLW (Z_to_bv 64 3) e); try apply is_ecall_ECALLW.
      - vm_compute. reflexivity.
      - exact Hh.
      - exact Hlazy.
      - regv HR (17 : reg). reflexivity.
      - regv HR (10 : reg). reflexivity.
      - rewrite u_small by lia. lia.
      - exact Hfd.
      - rewrite v_addi_pc4 by lia.
        pose proof (regs_set_a0 _ _ _ (Z_to_bv 64 0) (ELit 0) HR ltac:(reflexivity)) as HR2.
        clear HR. rename HR2 into HR.
        run_block_gen FUEL_RC STOPS_RC scr0 33%nat true.
        lazymatch goal with |- realizes _ (mkCfg (mkst ?Rn _ ?Mn _) _) _ => rename Rn into RB; rename Mn into MB end.
        cbn [mem_denot] in EQM. subst MB.
        apply (realizes_getr_ext RSEGS
                 (mkR (Z_to_bv 64 0x1d348) (Z_to_bv 64 (bv_unsigned sp0 - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x5d0c8)
                      (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9)
                      (Z_to_bv 64 0) (getr RB (Z_to_bv 5 11)) (getr RB (Z_to_bv 5 12)) (getr RB (Z_to_bv 5 13))
                      (getr RB (Z_to_bv 5 14)) (getr RB (Z_to_bv 5 15)) (getr RB (Z_to_bv 5 16)) (getr RB (Z_to_bv 5 17))
                      (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
                      (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31)) RB).
        { mkR_getr_cases HR
            ltac:(first [ reflexivity
                        | (rewrite alu_add; evc; unfold v_add; etransitivity; [reflexivity|];
                           apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; try rewrite Zplus_mod_idemp_r; f_equal; lia)
                        | (lazymatch goal with |- _ = ev _ ?k =>
                             change (ev _ k) with (ev E k); rewrite (evCL_junk (k - 1)) by lia;
                             etransitivity; [reflexivity|]; reflexivity end) ]). }
        change (mkst ?Rx ?pc ?Mx ?rom) with (MS Rx bvmap_empty pc (Z_to_bv 32 0) None Mx rom).
        apply HC.
        + intros x N1. pose proof (u64_range x). rewrite EQMA. apply mem_denot_out.
          cbn [log_out logCLA]. unfold adenot, v_addi. cbn [a_base a_off edenot]. evc.
          rewrite ?(u_small 0) by lia. repeat split; rewrite ?u_small by lia; lia.
        + rewrite EQMA. apply mem_denot_grows.
    Qed.
  End Close.
End RC.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
