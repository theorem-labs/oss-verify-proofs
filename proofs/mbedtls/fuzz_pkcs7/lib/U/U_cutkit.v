(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells Step Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX StepTac MemSplit StartupAux ArgvEnv Layout
  SymExec SymExec2 SymExec2Sound SymDriveX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_img U_startup_defs U_startup U_startup_facts U_main_entry U_exit_base U_main_open U_main_cut U_tailkit.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_cutkit () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_at_of_rdn : ltac2:(CDefT.buildp (gd_tbl_P_cutkit ()) "Pm,P,(0.&40.)(1.(0.&8.))Pbs,(2.(0.&8.))Pa,$3.P,(4.(1.(2.(0.&8.)))(5.$6.R3.(7.&40.R1.)(8.(0.&8.)R2.))(9.(2.(0.&8.))R2.))P,(:.=R2.)P,(:.(;.R3.(<.(8.(0.&8.)R4.)))(=.+2.+40.))(>.$6.R6.R4.R5.)")
(* [comment removed for export] *).
Proof.
  intros m bs. induction bs as [|b bs IH]; intros a H Ha Hl.
  - apply bytes_at_nil. cbn in Hl. lia.
  - cbn [length] in H, Hl. rewrite rdn_unfold in H.
    destruct (mrd RSEGS m (Z_to_bv 64 a)) as [b'|] eqn:E; [|discriminate].
    destruct (rdn RSEGS m (Z_to_bv 64 a + 1) (length bs)) as [r|] eqn:E2; [|discriminate].
    injection H as Hb Hr. subst b' r.
    change (b :: bs) with ([b] ++ bs). apply (proj2 (bytes_at_app RSEGS m a [b] bs)). split.
    + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. destruct i; [|lia].
      cbn. rewrite Z.add_0_r. unfold wa. exact E.
    + change (Z.of_nat (length [b])) with 1%Z. apply IH; try lia.
      replace (Z_to_bv 64 (a + 1)) with (Z_to_bv 64 a + 1 : word); [exact E2|].
      apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_unsigned (1 : word)) with 1%Z.
      rewrite !bv_wrap64_mod. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma bytes_at_cons8 : ltac2:(CDefT.buildp (gd_tbl_P_cutkit ()) "Pm,P,(0.&40.)(1.(0.&8.))Pa,$3.Pv,(0.&40.)Pbs,(2.(0.&8.))P,(4.(1.(2.(0.&8.)))(5.$6.R4.(7.&40.R3.)#8.)(9.(2.(0.&8.))(?.#8.R2.)))P,(>.$6.R5.(;.R4.+8.)R2.)P,(:.=R5.)(>.$6.R7.R6.(10.(0.&8.)(11.R5.)R4.))")
(* [comment removed for export] *).
Proof.
  intros m a v bs H HB Ha. pose proof (bytes_at_bound _ _ _ _ HB).
  apply (proj2 (bytes_at_app RSEGS m a (le8 v) bs)). rewrite length_le8. split; [|exact HB].
  apply bytes_at_of_rdn; rewrite ?length_le8; [exact H | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma ro_addr_data : forall a : Z, (0x4c000 <= a < 0x7e000)%Z -> ro_addr RSEGS (wa a) = false.
Proof.
  intros a Ha.
  apply (wview_not_ro RSEGS (fun _ => None) (wa a)); [|reflexivity].
  pose proof (store_ok_data (fun _ => None) (wa a) 1 ltac:(unfold wa; rewrite u_small by lia; lia)
                ltac:(unfold wa; rewrite u_small by lia; cbn; lia)) as S.
  pose proof (store_ok_wview RSEGS (fun _ => None) (wa a) 1 0 S ltac:(lia)) as W.
  unfold wa in W |- *. rewrite u_small in W by lia. rewrite Z.add_0_r in W. exact W.
Qed.

Lemma ro_addr_high : forall a : Z, (0x7e000 <= a < 2 ^ 64)%Z -> ro_addr RSEGS (wa a) = false.
Proof.
  intros a Ha. unfold ro_addr, wa. rewrite u_small by lia. rewrite find_segment_high by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AtCut.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rd : EntryDraw.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid rd regs0 mem0.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  (* [comment removed for export] *)
  #[using="AMB a0s path envv tid rd regs0 Hvsp ME SPlo SPhi"] Lemma mem0_none : ltac2:(CDefT.buildp (gd_tbl_P_cutkit ()) "Pa,$3.P,(12.(:.=R1.)(13.R1.(14.(15.&40.Vsp0,)+800000.)))P,(16.(13.R2.+4<?20.)(16.(12.(:.+4<?21.R2.)(13.R2.+5<??8.))(16.(16.(12.(:.+5=0>0.R2.)(13.R2.+5=150.))(12.(:.+7=108.R2.)(13.R2.+7=330.)))(:.+7=3<0.R2.))))(4.(1.(0.&8.))A1.Vmem0,(7.&40.R3.)(17.(0.&8.)))")
(* [comment removed for export] *).
  Proof.
    intros a Ha Hn. pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    rewrite (main_entry_mem_data sp0 [a0s; path] envv tid rd regs0 mem0 ME)
      by (rewrite stack_max_size_val, u_small by lia; lia).
    pose proof (u64_range tid).
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    repeat (rewrite MemSplit.wbytes_outside by
      (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite !u_small by lia; lia)).
    reflexivity.
  Qed.

  Variable M : word -> option byte.
  Hypothesis CM : cut_mem sp0 a0s path envv mem0 M.

  #[using="AMB a0s path envv tid rd regs0 mem0 Hvsp ME SPlo SPhi CM"] Lemma cut_clear : ltac2:(CDefT.buildp (gd_tbl_P_cutkit ()) "Pa,$3.P,(12.(:.=R1.)(13.R1.(14.(15.&40.Vsp0,)+800000.)))P,(16.(13.R2.+4<?20.)(16.(12.(:.+4<?21.R2.)(13.R2.+5<??8.))(16.(16.(12.(:.+5=0>0.R2.)(13.R2.+5=150.))(12.(:.+7=108.R2.)(13.R2.+7=330.)))(:.+7=3<0.R2.))))(4.(1.(0.&8.))A1.VM,(18.R3.)(17.(0.&8.)))")
(* [comment removed for export] *).
  Proof.
    intros a Ha Hn. pose proof SPlo. unfold wa. rewrite (cm_below _ _ _ _ _ _ CM) by (rewrite u_small by lia; lia).
    apply mem0_none; assumption.
  Qed.

  #[using="AMB sp0 a0s path envv tid rd regs0 mem0 Hvsp ME SPlo SPhi CM"] Theorem cut_mem_inv : mem_inv RSEGS M.
  Proof.
    intros x b Hx. pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range x) as Hxr.
    rewrite <- (Z_to_bv_bv_unsigned x) in Hx |- *. change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)) in Hx |- *.
    destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned sp0 - 8388608)) as [Hlow|Hhigh].
    - destruct (Z.lt_ge_cases (bv_unsigned x) 0x4cf20) as [A|A].
      { rewrite cut_clear in Hx by lia. discriminate. }
      destruct (Z.lt_ge_cases (bv_unsigned x) 0x7d3c0) as [B|B].
      { apply ro_addr_data. lia. }
      rewrite cut_clear in Hx by lia. discriminate.
    - apply ro_addr_high. lia.
  Qed.

  
  #[using="a0s path envv tid mem0 Hvsp Htid SPlo SPhi CM"] Theorem cut_frame : ltac2:(CDefT.buildp (gd_tbl_P_cutkit ()) "(19.$6.VM,(14.(15.&40.Vsp0,)+78.)(1:.$1;.(1<.(7.&40.=))(1:.$1;.(1<.(7.&40.=))(1:.$1;.(1<.(7.&40.=))(1:.$1;.(1<.(7.&40.=))(1:.$1;.(1<.(7.&40.(;.(15.&40.Vsp0,)+20.)))(1:.$1;.(1<.(7.&40.+1=24<.))(1:.$1;.(1<.(7.&40.+2.))(1:.$1;.(1<.(7.&40.(;.(15.&40.Vsp0,)+8.)))(1:.$1;.(1<.(7.&40.+3?2:8.))(1=.$1;.)))))))))))")
(* [comment removed for export] *).
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. destruct CM as [AB BE WO WI RA S0 S1 S2 S3 S4 S5 S6 S7 PA PL PH].
    unfold cell8 in *.
    split.
    - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply (bytes_at_cons8 M _ _ _ S7); [|lia]. replace (bv_unsigned sp0 - 120 + 8)%Z with (bv_unsigned sp0 - 112)%Z by lia.
      apply (bytes_at_cons8 M _ _ _ S6); [|lia]. replace (bv_unsigned sp0 - 112 + 8)%Z with (bv_unsigned sp0 - 104)%Z by lia.
      apply (bytes_at_cons8 M _ _ _ S5); [|lia]. replace (bv_unsigned sp0 - 104 + 8)%Z with (bv_unsigned sp0 - 96)%Z by lia.
      apply (bytes_at_cons8 M _ _ _ S4); [|lia]. replace (bv_unsigned sp0 - 96 + 8)%Z with (bv_unsigned sp0 - 88)%Z by lia.
      apply (bytes_at_cons8 M _ _ _ S3); [|lia]. replace (bv_unsigned sp0 - 88 + 8)%Z with (bv_unsigned sp0 - 80)%Z by lia.
      apply (bytes_at_cons8 M _ _ _ S2); [|lia]. replace (bv_unsigned sp0 - 80 + 8)%Z with (bv_unsigned sp0 - 72)%Z by lia.
      apply (bytes_at_cons8 M _ _ _ S1); [|lia]. replace (bv_unsigned sp0 - 72 + 8)%Z with (bv_unsigned sp0 - 64)%Z by lia.
      apply (bytes_at_cons8 M _ _ _ S0); [|lia]. replace (bv_unsigned sp0 - 64 + 8)%Z with (bv_unsigned sp0 - 56)%Z by lia.
      rewrite <- (app_nil_r (le8 (Z_to_bv 64 0x3f2a8))).
      apply (bytes_at_cons8 M _ _ _ RA); [|lia]. apply bytes_at_nil. lia.
    - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. apply WI. unfold wa. rewrite u_small by lia. lia.
  Qed.

  #[using="AMB sp0 a0s path envv rd regs0 mem0 Hvsp Htid ME SPlo SPhi CM"] Theorem cut_tid_cell : rw_cells RSEGS M 0x5d020 [C4 tid].
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (@cut_tail_mem AMB sp0 a0s path envv tid rd regs0 mem0) as TM.
    repeat (specialize (TM ltac:(assumption))).
    pose proof (tm_tid _ _ _ TM) as T. rewrite Z_to_bv_bv_unsigned in T.
    split.
    - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply bytes_at_of_rdn; rewrite ?length_le4; [|lia|lia]. exact T.
    - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
      pose proof (store_ok_wview RSEGS M (wa 0x5d020) 4 (Z.to_nat i)
                    (store_ok_data M (wa 0x5d020) 4 ltac:(unfold wa; rewrite u_small by lia; lia) ltac:(unfold wa; rewrite u_small by lia; cbn; lia))
                    ltac:(lia)) as W.
      unfold wa in W |- *. rewrite u_small in W by lia. rewrite Z2Nat.id in W by lia. exact W.
  Qed.
End AtCut.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
