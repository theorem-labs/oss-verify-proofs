(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import StartupTac ArgvEnv Layout.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_img U_startup_defs U_code_3b000_3c000.
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_startup2 () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.list"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.stack_to_mem"; "LinuxProcessSemantics.LinuxProcessSem.Run.entry_stack_image"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.phdrs"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.BB.MemSplit.cmem"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.wrap_mem"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.mul"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "RocqVerifyHarness.AgentSubmission.BB.Layout.cat_envp_ptr"; "Corelib.Lists.ListDef.nth"; "RocqVerifyHarness.AgentSubmission.BB.Layout.auxv_words"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.at_random_ptr"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.BB.StartupTac.bwd"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Nat.add"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.BB.Hoare.regs_agree"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.BB.CatExec.cat_argv_ptr"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.app"; "Corelib.Lists.ListDef.skipn"; "RocqVerifyHarness.AgentSubmission.BB.CatExec.wbytes"; "RocqVerifyHarness.AgentSubmission.U.U_startup_defs.after_last_slash"; "RocqVerifyHarness.AgentSubmission.BB.MemSplit.wfJ"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.U.U_startup_defs.envp_w"; "RocqVerifyHarness.AgentSubmission.U.U_startup_defs.J_aux"; "RocqVerifyHarness.AgentSubmission.U.U_startup_defs.D_libc"; "RocqVerifyHarness.AgentSubmission.BB.ZStores.zeros"; "Corelib.Init.Datatypes.None"].

Abbreviation RPH := Ubsan.M.phdrs.

Section P3.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.          (* [comment removed for export] *)
  Variable rdraw : EntryDraw.  (* [comment removed for export] *)
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation mem0 := (wrap_mem RPH sp0 av ev uid hw rdraw) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).
  Local Notation stk := (stack_to_mem sp0 (entry_stack_image RPH sp0 av ev uid hw rdraw)) (only parsing).
  (* [comment removed for export] *)
  Local Notation E := (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))%Z (only parsing).
  Local Notation A := (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))%Z (only parsing).

  Local Notation pn := (cat_argv_ptr sp0 av ev 0) (only parsing).
  Local Notation rnd := (at_random_ptr sp0 av ev) (only parsing).
  Local Notation s := (nth 0 av []) (only parsing).
  Local Notation A8 := (Z_to_bv 64 0x7d340) (only parsing).

  #[using="sp0 Hva"] Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.
  #[using="sp0 Hve"] Lemma len_ev : (Z.of_nat (length ev) <= 256)%Z.
  Proof. destruct Hve as [H1 _]. lia. Qed.

  #[using="Hlo"] Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  #[using="Hhi"] Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.

  
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Hlo"] Lemma rd_above : ltac2:(CDefT.buildp (gd_tbl_P_startup2 ()) "PJ,P,(0.&40.)(1.(0.&8.))PD,P,(0.&40.)(1.(0.&8.))Pa,$2.Pn,$3.Pbs,(4.(0.&8.))P,(5.(6.&40.Vsp0,)R3.)P,(7.(8.R4.(9.R3.))(:.+2.+40.))P,(;.(1.(4.(0.&8.)))(<.(=.$>.)(?.Vsp0,(10.$11.Vsp0,Vav,Vev,Vuid,Vhw,Vrdraw,))(12.&40.R5.)R4.)(13.(4.(0.&8.))R3.))(;.(1.(4.(0.&8.)))(<.$14.(15.Vsp0,(16.$11.Vsp0,Vav,Vev,Vuid,Vhw,Vrdraw,)R8.R7.)(12.&40.R6.)R5.)(13.(4.(0.&8.))R4.))")
(* [comment removed for export] *).
  Proof.
    intros J D a n bs Ha Hn H. pose proof (u64_range (Z_to_bv 64 a)).
    rewrite rdn_cmem_above by (unorm; lia).
    apply rdn_wrap_stack_above. exact H.
  Qed.

  #[using="Hva Hve Hlo Hhi"] Lemma rd_envp : ltac2:(CDefT.buildp (gd_tbl_P_startup2 ()) "PJ,P,(0.&40.)(1.(0.&8.))PD,P,(0.&40.)(1.(0.&8.))Pk,$3.P,(17.R1.(18.(4.(0.&8.))Vev,))(;.(1.(4.(0.&8.)))(<.$14.(15.Vsp0,(16.$11.Vsp0,Vav,Vev,Vuid,Vhw,Vrdraw,)R4.R3.)(12.&40.(8.(8.(8.(6.&40.Vsp0,)+10.)(19.+8.(9.(18.(4.(0.&8.))Vav,))))(19.+8.(9.R2.))))#8.)(13.(4.(0.&8.))(1:.#8.(1;.Vsp0,Vav,Vev,R2.))))")
(* [comment removed for export] *).
  Proof.
    intros J D k Hk. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (E + 8 * Z.of_nat k)) with (sp0 + nat_to_word (envp_off av + 8 * k))
      by (rewrite word_add_nat; f_equal; unfold envp_off; lia).
    exact (read_envp_ptr_k [] RPH sp0 rdraw av ev uid hw Hva Hve Hsp_hi' k Hk).
  Qed.

  #[using="Hva Hve Hlo Hhi"] Lemma rd_envp_null : ltac2:(CDefT.buildp (gd_tbl_P_startup2 ()) "PJ,P,(0.&40.)(1.(0.&8.))PD,P,(0.&40.)(1.(0.&8.))(;.(1.(4.(0.&8.)))(<.$14.(15.Vsp0,(16.$11.Vsp0,Vav,Vev,Vuid,Vhw,Vrdraw,)R2.R1.)(12.&40.(8.(8.(8.(6.&40.Vsp0,)+10.)(19.+8.(9.(18.(4.(0.&8.))Vav,))))(19.+8.(9.(18.(4.(0.&8.))Vev,)))))#8.)(13.(4.(0.&8.))(1:.#8.(12.&40.=))))")
(* [comment removed for export] *).
  Proof.
    intros J D. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (E + 8 * Z.of_nat (length ev)))
      with (sp0 + nat_to_word (envp_off av + 8 * length ev))
      by (rewrite word_add_nat; f_equal; unfold envp_off; lia).
    exact (read_envp_null [] RPH sp0 rdraw av ev uid hw Hva Hve Hsp_hi').
  Qed.

  #[using="Hva Hve Hlo Hhi"] Lemma rd_auxv : ltac2:(CDefT.buildp (gd_tbl_P_startup2 ()) "PJ,P,(0.&40.)(1.(0.&8.))PD,P,(0.&40.)(1.(0.&8.))Pj,$3.Pw,(0.&40.)P,(17.R2.#14.)P,(;.(0.&40.)(1<.(0.&40.)R3.(1=.$11.(1>.Vsp0,Vav,Vev,)Vuid,Vhw,)(12.&40.=))R2.)(;.(1.(4.(0.&8.)))(<.$14.(15.Vsp0,(16.$11.Vsp0,Vav,Vev,Vuid,Vhw,Vrdraw,)R6.R5.)(12.&40.(8.(8.(8.(8.(6.&40.Vsp0,)+18.)(19.+8.(9.(18.(4.(0.&8.))Vav,))))(19.+8.(9.(18.(4.(0.&8.))Vev,))))(19.+8.(9.R4.))))#8.)(13.(4.(0.&8.))(1:.#8.R3.)))")
(* [comment removed for export] *).
  Proof.
    intros J D j w Hj Hw. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (A + 8 * Z.of_nat j)) with (sp0 + nat_to_word (auxv_off av ev + 8 * j))
      by (rewrite word_add_nat; f_equal; unfold auxv_off; lia).
    rewrite <- Hw. exact (read_auxv_word [] RPH sp0 rdraw av ev uid hw Hva Hve Hsp_hi' j Hj).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Hva Hve Hlo Hhi"] Lemma envp_loop : ltac2:(CDefT.buildp (gd_tbl_P_startup2 ()) "PG,P,$1?.SpP,(20.$14.R1.)Pn,$3.Pk,$3.Pregs,(21.&5.(0.&40.))PJ,P,(0.&40.)(1.(0.&8.))PD,P,(0.&40.)(1.(0.&8.))Prom,P,(0.&40.)(1.(0.&8.))P,(;.$3.(22.R5.R6.)(18.(4.(0.&8.))Vev,))P,(;.(0.&40.)(23.R5.(24.&5.+9.$25.))(12.&40.(8.(8.(8.(6.&40.Vsp0,)+10.)(19.+8.(9.(18.(4.(0.&8.))Vav,))))(19.+8.(9.R6.)))))P,Pregs',(21.&5.(0.&40.))P,(;.(0.&40.)(23.R1.(24.&5.+9.$25.))(12.&40.(8.(8.(8.(8.(6.&40.Vsp0,)+10.)(19.+8.(9.(18.(4.(0.&8.))Vav,))))(19.+8.(9.(18.(4.(0.&8.))Vev,))))+8.)))P,(;.(0.&40.)(23.R2.(24.&5.+:.$25.))(12.&40.=))P,(26.Lr,(0.&5.)(27.(0.&5.)R1.(28.(0.&5.)(24.&5.+9.$25.)(28.(0.&5.)(24.&5.+:.$25.)(=.(0.&5.)))))R9.R3.)A1.R>.(29.$2:.R4.(24.&40.+3>?=0.$25.)(15.Vsp0,(16.$11.Vsp0,Vav,Vev,Vuid,Vhw,Vrdraw,)R9.R8.)R7.)A1.R;.(29.$2:.R7.(24.&40.+3>?<4.$25.)(15.Vsp0,(16.$11.Vsp0,Vav,Vev,Vuid,Vhw,Vrdraw,)R6.R5.)R4.)")
(* [comment removed for export] *).
  Proof.
    intros G HG.
    pose proof len_av as Hlen. pose proof len_ev as Hlev.
    induction n as [|n IH]; intros k regs J D rom Hkn H9 Hk0.
    - (* [comment removed for export] *)
      assert (k = length ev) by lia. subst k.
      eapply HG.
      { ld_step F_3b86c D_3b86c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
          ltac:(apply rd_envp_null) ltac:(apply bytes_le_to_Z_8).
        sv F_3b870 D_3b870 (Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8)).
        stepb_ft F_3b874 D_3b874 ltac:(pin; cond_compute).
        apply mst_refl. }
      apply Hk0; [gres; reflexivity | gres; reflexivity | solve_regs_agree].
    - assert (Hk : (k < length ev)%nat) by lia.
      pose proof (cat_envp_ptr_nz sp0 av ev Hva Hve Hsp_lo' Hsp_hi' k Hk) as Hnz.
      eapply HG.
      { ld_step F_3b86c D_3b86c (word_to_le_bytes 8 (cat_envp_ptr sp0 av ev k)) (cat_envp_ptr sp0 av ev k)
          ltac:(apply rd_envp; exact Hk) ltac:(apply bytes_le_to_Z_8).
        sv F_3b870 D_3b870 (Z_to_bv 64 (E + 8 * Z.of_nat (S k))).
        stepb_tk F_3b874 D_3b874 ltac:(pin; apply c_eq_0_false; exact Hnz).
        apply mst_refl. }
      eapply (IH (S k)); [lia | gres; reflexivity |].
      intros regs' H9' H10' Hag. apply Hk0; [exact H9' | exact H10' |].
      eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Hva Hve Hhi"] Lemma pn_bounds : ltac2:(CDefT.buildp (gd_tbl_P_startup2 ()) "(2;.(5.(6.&40.Vsp0,)(6.&40.(2<.Vsp0,Vav,Vev,#0.)))(7.(8.(8.(6.&40.(2<.Vsp0,Vav,Vev,#0.))(9.(18.(0.&8.)(1<.(4.(0.&8.))#0.Vav,(=.(0.&8.))))))+1.)(:.+2.+40.)))")
(* [comment removed for export] *).
  Proof.
    pose proof len_av.
    exact (argv_ptr_bounds_at sp0 av ev Hva Hve Hsp_hi' 0 ltac:(lia)).
  Qed.

  #[using="Hva Hve Hlo Hhi"] Lemma rd_argv0_byte : ltac2:(CDefT.buildp (gd_tbl_P_startup2 ()) "PJ,P,(0.&40.)(1.(0.&8.))PD,P,(0.&40.)(1.(0.&8.))Pj,$3.Pb,(0.&8.)P,(2=.R2.(18.(0.&8.)(1<.(4.(0.&8.))#0.Vav,(=.(0.&8.)))))P,(;.(0.&8.)(1<.(0.&8.)R3.(2>.(0.&8.)(1<.(4.(0.&8.))#0.Vav,(=.(0.&8.)))(28.(0.&8.)(12.&8.=)(=.(0.&8.))))(12.&8.=))R2.)(;.(1.(4.(0.&8.)))(<.$14.(15.Vsp0,(16.$11.Vsp0,Vav,Vev,Vuid,Vhw,Vrdraw,)R6.R5.)(12.&40.(8.(6.&40.(2<.Vsp0,Vav,Vev,#0.))(9.R4.)))#1.)(13.(4.(0.&8.))(28.(0.&8.)R3.(=.(0.&8.)))))")
(* [comment removed for export] *).
  Proof.
    intros J D j b Hj Hb. pose proof len_av. pose proof pn_bounds as [Hp1 Hp2].
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j)) with (pn + nat_to_word j)
      by (rewrite word_add_nat; reflexivity).
    rewrite <- Hb.
    exact (read_argv_byte_k RPH [] sp0 av ev 0 j uid hw rdraw ltac:(lia) Hj
             (bsb_nw RPH sp0 av ev uid hw rdraw Hva Hve Hsp_hi')).
  Qed.

  #[using="Type"] Lemma rdn_addr : ltac2:(CDefT.buildp (gd_tbl_P_startup2 ()) "Psegs,(4.$>.)Pm,P,(0.&40.)(1.(0.&8.))Pa,(0.&40.)Pa',(0.&40.)Pn,$3.Pr,(1.(4.(0.&8.)))P,(;.(1.(4.(0.&8.)))(<.R6.R5.R3.R2.)R1.)P,(;.(0.&40.)R5.R4.)(;.(1.(4.(0.&8.)))(<.R8.R7.R6.R4.)R3.)")
(* [comment removed for export] *).
  Proof. intros; subst; reflexivity. Qed.

  #[using="sp0"] Lemma c_eq_byte47 : forall b : byte,
    c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 47) = bv_eqb b (Z_to_bv 8 47).
  Proof.
    intros b. pose proof (u8_range b). unfold c_eq, bv_eqb.
    rewrite !u_Z2bv by lia. reflexivity.
  Qed.

  #[using="sp0"] Lemma c_eq_byte0 : forall b : byte, b <> Z_to_bv 8 0 ->
    c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 0) = false.
  Proof.
    intros b Hb. pose proof (u8_range b). apply c_eq_0_false. rewrite u_Z2bv by lia.
    intro Hz. apply Hb. apply bv_eq. rewrite Hz. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Hva Hve Hlo Hhi"] Lemma prog_loop : ltac2:(CDefT.buildp (gd_tbl_P_startup2 ()) "PG,P,$1?.SpP,(20.$14.R1.)Pl2,(4.(0.&8.))Pj,$3.Pacc,$3.Pregs,(21.&5.(0.&40.))PJ,P,(0.&40.)(1.(0.&8.))PD,P,(0.&40.)(1.(0.&8.))Prom,P,(0.&40.)(1.(0.&8.))P,(;.(4.(0.&8.))(2?.(0.&8.)R6.(1<.(4.(0.&8.))#0.Vav,(=.(0.&8.))))R7.)P,(2=.R7.(18.(0.&8.)(1<.(4.(0.&8.))#0.Vav,(=.(0.&8.)))))P,(2=.R7.R8.)P,(;.(0.&40.)(23.R7.(24.&5.+:.$25.))(12.&40.+7=340.))P,(;.(0.&40.)(23.R8.(24.&5.+;.$25.))(12.&40.(8.(8.(6.&40.(2<.Vsp0,Vav,Vev,#0.))(9.R:.))+1.)))P,(;.(0.&40.)(23.R9.(24.&5.+<.$25.))(12.&40.+2?.))P,Pregs',(21.&5.(0.&40.))P,(;.(0.&40.)(23.R1.(24.&5.+;.$25.))(12.&40.(8.(8.(6.&40.(2<.Vsp0,Vav,Vev,#0.))(9.(18.(0.&8.)(1<.(4.(0.&8.))#0.Vav,(=.(0.&8.))))))+1.)))P,(26.Lr,(0.&5.)(27.(0.&5.)R1.(28.(0.&5.)(24.&5.+;.$25.)(28.(0.&5.)(24.&5.+=.$25.)(=.(0.&5.)))))R<.R2.)A1.R12.(29.$2:.R3.(24.&40.+3?094.$25.)(15.Vsp0,(16.$11.Vsp0,Vav,Vev,Vuid,Vhw,Vrdraw,)R<.(30.R;.(12.&40.+7=340.)(1:.#8.(12.&40.(8.(6.&40.(2<.Vsp0,Vav,Vev,#0.))(9.(31.R10.R?.R>.)))))))R:.)A1.R10.(29.$2:.R;.(24.&40.+3?088.$25.)(15.Vsp0,(16.$11.Vsp0,Vav,Vev,Vuid,Vhw,Vrdraw,)R:.(30.R9.(12.&40.+7=340.)(1:.#8.(12.&40.(8.(6.&40.(2<.Vsp0,Vav,Vev,#0.))(9.R<.))))))R8.)")
(* [comment removed for export] *).
  Proof.
    intros G HG.
    pose proof len_av as Hlen. pose proof pn_bounds as [Hp1 Hp2].
    pose proof (valid_argv_str_nz av 0 Hva ltac:(lia)) as Hnz.
    induction l2 as [|b l2 IH]; intros j acc regs J D rom Hskip Hj Hacc H10 H11 H12 Hk0.
    - (* [comment removed for export] *)
      assert (Hjl : j = length s).
      { pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
      eapply HG.
      { lb_step F_3b930 D_3b930 (Z_to_bv 8 0)
          ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | subst j; rewrite app_nth2 by lia; rewrite Nat.sub_diag; reflexivity] | f_equal; lia]).
        stepb_ft F_3b934 D_3b934 ltac:(pin; cond_compute).
        stepb_ft F_3b938 D_3b938 ltac:(pin; cond_compute).
        apply mst_refl. }
      apply Hk0; [gres; pin; f_equal; lia | solve_regs_agree].
    - assert (Hjlt : (j < length s)%nat).
      { pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
      assert (Hb : nth j (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = b).
      { rewrite app_nth1 by lia. rewrite <- (Nat.add_0_r j), <- nth_skipn, Hskip. reflexivity. }
      assert (Hbnz : b <> Z_to_bv 8 0).
      { intros Hb0. apply Hnz. rewrite <- Hb0, <- Hb, app_nth1 by lia. apply nth_In. lia. }
      assert (Hskip' : skipn (S j) s = l2).
      { replace (S j) with (1 + j)%nat by lia. rewrite <- skipn_skipn, Hskip. reflexivity. }
      cbn [after_last_slash] in Hk0.
      destruct (bv_eqb b (Z_to_bv 8 47)) eqn:Eb.
      + (* [comment removed for export] *)
        eapply HG.
        { lb_step F_3b930 D_3b930 b
            ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
          stepb_tk F_3b934 D_3b934 ltac:(pin; rewrite c_eq_byte47; exact Eb).
          stw F_3b928 D_3b928 (Z_to_bv 64 0x7d340) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1)) ltac:(ok_data).
          rewrite wbytes_shadow by (rewrite ?length_N_to_le_bytes; rewrite ?length_N_to_le_bytes; first [reflexivity | region_side]).
          sv F_3b92c D_3b92c (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)).
          apply mst_refl. }
        replace (bv_unsigned pn + Z.of_nat j + 1)%Z with (bv_unsigned pn + Z.of_nat (S j))%Z by lia.
        eapply (IH (S j) (S j)); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
        intros regs' H11' Hag. apply Hk0; [exact H11'|].
        eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
      + eapply HG.
        { lb_step F_3b930 D_3b930 b
            ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
          stepb_ft F_3b934 D_3b934 ltac:(pin; rewrite c_eq_byte47; exact Eb).
          stepb_tk F_3b938 D_3b938 ltac:(pin; apply c_eq_byte0; exact Hbnz).
          sv F_3b92c D_3b92c (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)).
          apply mst_refl. }
        eapply (IH (S j) acc); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
        intros regs' H11' Hag. apply Hk0; [exact H11'|].
        eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Ltac rdA j w := eapply rdn_addr; [apply (rd_auxv _ _ j w); [lia | reflexivity] | f_equal; lia].

  #[using="Hva Hve Hlo Hhi"] Lemma p3_run : ltac2:(CDefT.buildp (gd_tbl_P_startup2 ()) "PG,P,$1?.SpP,(20.$14.R1.)Pregs,(21.&5.(0.&40.))PJf,P,(0.&40.)(1.(0.&8.))Prom,P,(0.&40.)(1.(0.&8.))P,(32.Vsp0,R2.)P,(;.(0.&40.)(23.R4.(24.&5.+2.$25.))(12.&40.(33.(6.&40.Vsp0,)+1:0.)))P,(;.(0.&40.)(23.R5.(24.&5.+8.$25.))(2<.Vsp0,Vav,Vev,#0.))P,(;.(0.&40.)(23.R6.(24.&5.+9.$25.))(34.Vsp0,Vav,))P,(;.(0.&40.)(23.R7.(24.&5.+:.$25.))(12.&40.(33.(6.&40.Vsp0,)+170.)))P,Pregs',(21.&5.(0.&40.))P,(;.(0.&40.)(23.R1.(24.&5.+1.$25.))(12.&40.+3?09<.))P,(;.(0.&40.)(23.R2.(24.&5.+2.$25.))(12.&40.(33.(6.&40.Vsp0,)+1:0.)))P,(;.(0.&40.)(23.R3.(24.&5.+:.$25.))(12.&40.(33.(6.&40.Vsp0,)+170.)))P,(;.(0.&40.)(23.R4.(24.&5.+12.$25.))(12.&40.+7=350.))P,(26.Lr,(0.&5.)(27.(0.&5.)R1.(28.(0.&5.)(24.&5.+1.$25.)(28.(0.&5.)(24.&5.+9.$25.)(28.(0.&5.)(24.&5.+:.$25.)(28.(0.&5.)(24.&5.+;.$25.)(28.(0.&5.)(24.&5.+<.$25.)(28.(0.&5.)(24.&5.+=.$25.)(28.(0.&5.)(24.&5.+12.$25.)(=.(0.&5.))))))))))R=.R5.)A1.R10.(29.$2:.R6.(24.&40.+3?2:<.$25.)(15.Vsp0,(16.$11.Vsp0,Vav,Vev,Vuid,Vhw,Vrdraw,)(35.Vsp0,Vav,Vev,Vuid,Vhw,R=.)(36.Vsp0,Vav,Vev,Vhw,))R<.)A1.R;.(29.$2:.R9.(24.&40.+3>?;8.$25.)(15.Vsp0,(16.$11.Vsp0,Vav,Vev,Vuid,Vhw,Vrdraw,)(30.R8.(12.&40.(33.(6.&40.Vsp0,)+170.))(37.#130.))L,(0.&40.)(38.(0.&8.)))R7.)")
(* [comment removed for export] *).
  Proof.
    intros G HG regs Jf rom HJ H2 H8 H9 H10 Hk.
    pose proof len_av as Hlen. pose proof len_ev as Hlev. pose proof pn_bounds as [Hp1 Hp2].
    unfold envp_w in H9.
    eapply HG.
    { sn F_3b860 D_3b860.   (* [comment removed for export] *)
    ld_step F_3b864 D_3b864 (word_to_le_bytes 8 (Z_to_bv 64 0x5cff8)) (Z_to_bv 64 0x5cff8)
      ltac:(rd_img img_48568_8) ltac:(apply bytes_le_to_Z_8).
    stw F_3b868 D_3b868 (Z_to_bv 64 0x5cff8) (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ltac:(ok_data).
      apply mst_refl. }
    (* [comment removed for export] *)
    eapply (envp_loop G HG (length ev) 0); [lia | gres; pin; f_equal; lia |].
    intros regs1 H9a H10a Hag1.
    carry Hag1 H2 (2 : reg) H2a. carry Hag1 H8 (8 : reg) H8a.
    clear H9 H10 H8 H2.
    eapply HG.
    { sn F_3b878 D_3b878.   (* [comment removed for export] *)
    sn F_3b87c D_3b87c.   (* [comment removed for export] *)
    stw F_3b880 D_3b880 (Z_to_bv 64 0x7d358)
      (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))) ltac:(ok_data).
    (* [comment removed for export] *)
    ld_step F_3b884 D_3b884 (word_to_le_bytes 8 (Z_to_bv 64 3)) (Z_to_bv 64 3) ltac:(rdA 0%nat (Z_to_bv 64 3)) ltac:(apply bytes_le_to_Z_8).
    stepb_ft F_3b888 D_3b888 ltac:(pin; cond_compute).
    sv F_3b88c D_3b88c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 16)).
    sn F_3b890 D_3b890.   (* [comment removed for export] *)
    sv F_3b894 D_3b894 (Z_to_bv 64 (bv_unsigned sp0 - 368)).  (* [comment removed for export] *)
    sn F_3b898 D_3b898.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_3b8a8 D_3b8a8 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_3b8ac D_3b8ac (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 0x10040) ltac:(rdA 1%nat (Z_to_bv 64 0x10040)) ltac:(apply bytes_le_to_Z_8).
    sn F_3b8b0 D_3b8b0.   (* [comment removed for export] *)
    sv F_3b8b4 D_3b8b4 (Z_to_bv 64 (bv_unsigned sp0 - 344)).   (* [comment removed for export] *)
    stw F_3b8b8 D_3b8b8 (Z_to_bv 64 (bv_unsigned sp0 - 344)) (Z_to_bv 64 0x10040) ltac:(ok_win HJ).
    sn F_3b8bc D_3b8bc.   (* [comment removed for export] *)
    ld_step F_3b89c D_3b89c (word_to_le_bytes 8 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rdA 2%nat (Z_to_bv 64 4)) ltac:(apply bytes_le_to_Z_8).
    sv F_3b8a0 D_3b8a0 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 32)).
    stepb_ft F_3b8a4 D_3b8a4 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_3b8a8 D_3b8a8 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_3b8ac D_3b8ac (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rdA 3%nat (Z_to_bv 64 56)) ltac:(apply bytes_le_to_Z_8).
    sn F_3b8b0 D_3b8b0.   (* [comment removed for export] *)
    sv F_3b8b4 D_3b8b4 (Z_to_bv 64 (bv_unsigned sp0 - 336)).   (* [comment removed for export] *)
    stw F_3b8b8 D_3b8b8 (Z_to_bv 64 (bv_unsigned sp0 - 336)) (Z_to_bv 64 56) ltac:(ok_win HJ).
    sn F_3b8bc D_3b8bc.   (* [comment removed for export] *)
    ld_step F_3b89c D_3b89c (word_to_le_bytes 8 (Z_to_bv 64 5)) (Z_to_bv 64 5) ltac:(rdA 4%nat (Z_to_bv 64 5)) ltac:(apply bytes_le_to_Z_8).
    sv F_3b8a0 D_3b8a0 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 48)).
    stepb_ft F_3b8a4 D_3b8a4 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_3b8a8 D_3b8a8 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_3b8ac D_3b8ac (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rdA 5%nat (Z_to_bv 64 10)) ltac:(apply bytes_le_to_Z_8).
    sn F_3b8b0 D_3b8b0.   (* [comment removed for export] *)
    sv F_3b8b4 D_3b8b4 (Z_to_bv 64 (bv_unsigned sp0 - 328)).   (* [comment removed for export] *)
    stw F_3b8b8 D_3b8b8 (Z_to_bv 64 (bv_unsigned sp0 - 328)) (Z_to_bv 64 10) ltac:(ok_win HJ).
    sn F_3b8bc D_3b8bc.   (* [comment removed for export] *)
    ld_step F_3b89c D_3b89c (word_to_le_bytes 8 (Z_to_bv 64 16)) (Z_to_bv 64 16) ltac:(rdA 6%nat (Z_to_bv 64 16)) ltac:(apply bytes_le_to_Z_8).
    sv F_3b8a0 D_3b8a0 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 64)).
    stepb_ft F_3b8a4 D_3b8a4 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_3b8a8 D_3b8a8 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_3b8ac D_3b8ac (word_to_le_bytes 8 hw) hw ltac:(rdA 7%nat hw) ltac:(apply bytes_le_to_Z_8).
    sn F_3b8b0 D_3b8b0.   (* [comment removed for export] *)
    sv F_3b8b4 D_3b8b4 (Z_to_bv 64 (bv_unsigned sp0 - 240)).   (* [comment removed for export] *)
    stw F_3b8b8 D_3b8b8 (Z_to_bv 64 (bv_unsigned sp0 - 240)) hw ltac:(ok_win HJ).
    sn F_3b8bc D_3b8bc.   (* [comment removed for export] *)
    ld_step F_3b89c D_3b89c (word_to_le_bytes 8 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rdA 8%nat (Z_to_bv 64 6)) ltac:(apply bytes_le_to_Z_8).
    sv F_3b8a0 D_3b8a0 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 80)).
    stepb_ft F_3b8a4 D_3b8a4 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_3b8a8 D_3b8a8 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_3b8ac D_3b8ac (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096) ltac:(rdA 9%nat (Z_to_bv 64 4096)) ltac:(apply bytes_le_to_Z_8).
    sn F_3b8b0 D_3b8b0.   (* [comment removed for export] *)
    sv F_3b8b4 D_3b8b4 (Z_to_bv 64 (bv_unsigned sp0 - 320)).   (* [comment removed for export] *)
    stw F_3b8b8 D_3b8b8 (Z_to_bv 64 (bv_unsigned sp0 - 320)) (Z_to_bv 64 4096) ltac:(ok_win HJ).
    sn F_3b8bc D_3b8bc.   (* [comment removed for export] *)
    ld_step F_3b89c D_3b89c (word_to_le_bytes 8 (Z_to_bv 64 11)) (Z_to_bv 64 11) ltac:(rdA 10%nat (Z_to_bv 64 11)) ltac:(apply bytes_le_to_Z_8).
    sv F_3b8a0 D_3b8a0 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 96)).
    stepb_ft F_3b8a4 D_3b8a4 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_3b8a8 D_3b8a8 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_3b8ac D_3b8ac (word_to_le_bytes 8 uid) uid ltac:(rdA 11%nat uid) ltac:(apply bytes_le_to_Z_8).
    sn F_3b8b0 D_3b8b0.   (* [comment removed for export] *)
    sv F_3b8b4 D_3b8b4 (Z_to_bv 64 (bv_unsigned sp0 - 280)).   (* [comment removed for export] *)
    stw F_3b8b8 D_3b8b8 (Z_to_bv 64 (bv_unsigned sp0 - 280)) uid ltac:(ok_win HJ).
    sn F_3b8bc D_3b8bc.   (* [comment removed for export] *)
    ld_step F_3b89c D_3b89c (word_to_le_bytes 8 (Z_to_bv 64 12)) (Z_to_bv 64 12) ltac:(rdA 12%nat (Z_to_bv 64 12)) ltac:(apply bytes_le_to_Z_8).
    sv F_3b8a0 D_3b8a0 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 112)).
    stepb_ft F_3b8a4 D_3b8a4 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_3b8a8 D_3b8a8 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_3b8ac D_3b8ac (word_to_le_bytes 8 uid) uid ltac:(rdA 13%nat uid) ltac:(apply bytes_le_to_Z_8).
    sn F_3b8b0 D_3b8b0.   (* [comment removed for export] *)
    sv F_3b8b4 D_3b8b4 (Z_to_bv 64 (bv_unsigned sp0 - 272)).   (* [comment removed for export] *)
    stw F_3b8b8 D_3b8b8 (Z_to_bv 64 (bv_unsigned sp0 - 272)) uid ltac:(ok_win HJ).
    sn F_3b8bc D_3b8bc.   (* [comment removed for export] *)
    ld_step F_3b89c D_3b89c (word_to_le_bytes 8 (Z_to_bv 64 23)) (Z_to_bv 64 23) ltac:(rdA 14%nat (Z_to_bv 64 23)) ltac:(apply bytes_le_to_Z_8).
    sv F_3b8a0 D_3b8a0 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 128)).
    stepb_ft F_3b8a4 D_3b8a4 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_3b8a8 D_3b8a8 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_3b8ac D_3b8ac (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 15%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sn F_3b8b0 D_3b8b0.   (* [comment removed for export] *)
    sv F_3b8b4 D_3b8b4 (Z_to_bv 64 (bv_unsigned sp0 - 184)).   (* [comment removed for export] *)
    stw F_3b8b8 D_3b8b8 (Z_to_bv 64 (bv_unsigned sp0 - 184)) (Z_to_bv 64 0) ltac:(ok_win HJ).
    sn F_3b8bc D_3b8bc.   (* [comment removed for export] *)
    ld_step F_3b89c D_3b89c (word_to_le_bytes 8 (Z_to_bv 64 25)) (Z_to_bv 64 25) ltac:(rdA 16%nat (Z_to_bv 64 25)) ltac:(apply bytes_le_to_Z_8).
    sv F_3b8a0 D_3b8a0 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 144)).
    stepb_ft F_3b8a4 D_3b8a4 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepb_ft F_3b8a8 D_3b8a8 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    ld_step F_3b8ac D_3b8ac (word_to_le_bytes 8 (at_random_ptr sp0 av ev)) (at_random_ptr sp0 av ev) ltac:(rdA 17%nat (at_random_ptr sp0 av ev)) ltac:(apply bytes_le_to_Z_8).
    sn F_3b8b0 D_3b8b0.   (* [comment removed for export] *)
    sv F_3b8b4 D_3b8b4 (Z_to_bv 64 (bv_unsigned sp0 - 168)).   (* [comment removed for export] *)
    stw F_3b8b8 D_3b8b8 (Z_to_bv 64 (bv_unsigned sp0 - 168)) (at_random_ptr sp0 av ev) ltac:(ok_win HJ).
    sn F_3b8bc D_3b8bc.   (* [comment removed for export] *)
    ld_step F_3b89c D_3b89c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 18%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sv F_3b8a0 D_3b8a0 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 160)).
    stepb_tk F_3b8a4 D_3b8a4 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    ld_step F_3b8c0 D_3b8c0 (word_to_le_bytes 8 hw) hw
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)
    ld_step F_3b8c4 D_3b8c4 (zeros 8) (Z_to_bv 64 0)
      ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)
      ltac:(reflexivity).
    sn F_3b8c8 D_3b8c8.   (* [comment removed for export] *)
    stw F_3b8cc D_3b8cc (Z_to_bv 64 0x7d3b8) hw ltac:(ok_data).   (* [comment removed for export] *)
    stepb_tk F_3b8d0 D_3b8d0 ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    ld_step F_3b8e8 D_3b8e8 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    stw F_3b8ec D_3b8ec (Z_to_bv 64 0x7d380) (Z_to_bv 64 4096) ltac:(ok_data).
    stepb_tk F_3b8f0 D_3b8f0 ltac:(pin; apply c_eq_0_false; lia).   (* [comment removed for export] *)
    stepb_tk F_3b8f8 D_3b8f8 ltac:(pin; apply c_eq_0_false; lia).
    (* [comment removed for export] *)
    sn F_3b904 D_3b904.
    ld_step F_3b908 D_3b908 (word_to_le_bytes 8 (Z_to_bv 64 0x7d348)) (Z_to_bv 64 0x7d348)
      ltac:(rd_img img_48570_8) ltac:(apply bytes_le_to_Z_8).
    sn F_3b90c D_3b90c.
    ld_step F_3b910 D_3b910 (word_to_le_bytes 8 (Z_to_bv 64 0x7d340)) (Z_to_bv 64 0x7d340)
      ltac:(rd_img img_48578_8) ltac:(apply bytes_le_to_Z_8).
    stw F_3b914 D_3b914 (Z_to_bv 64 0x7d348) (cat_argv_ptr sp0 av ev 0) ltac:(ok_data).
    sv F_3b918 D_3b918 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0 + 1)).   (* [comment removed for export] *)
    stw F_3b91c D_3b91c (Z_to_bv 64 0x7d340) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0)) ltac:(ok_data).
    sn F_3b920 D_3b920.   (* [comment removed for export] *)
    sn F_3b924 D_3b924.   (* [comment removed for export] *)
      apply mst_refl. }
    (* [comment removed for export] *)
    eapply (prog_loop G HG s 0 0); [reflexivity | lia | lia | gres; reflexivity | gres; reflexivity | gres; reflexivity |].
    intros regs2 H11b Hag2.
    carry Hag2 H2a (2 : reg) H2b.
    eapply HG.
    { sv F_3b93c D_3b93c (Z_to_bv 64 (bv_unsigned sp0 - 368)).   (* [comment removed for export] *)
      sn F_3b940 D_3b940.   (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk.
    - gres; bveq.
    - gres; exact H2b.
    - gres; reflexivity.
    - gres. pose proof (Hag2 (18:reg) ltac:(notin_list)) as T; rewrite T; gres; reflexivity.
    - ra_chain.
  Qed.

End P3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
