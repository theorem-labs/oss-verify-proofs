(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk StepTac. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanStartLoops AllocSim MmapSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanStartLoops OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlan AxSymExec3F. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3F.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import EntryKn StdioSymDrive.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import EntryGlue.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import AsanBootKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootImg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require BootKn1__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Boot1 Boot2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boot3_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables argv envp : list (list byte).
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.

  (* [comment removed for export] *)
  Let E7 : env := E7 sp rdraw argv envp uid hw.
  Let MEM0 : word -> option byte := MEM0 sp rdraw argv envp uid hw.
  Let above_ok := above_ok sp rdraw argv envp uid hw.
  Let E8 := E8 sp rdraw argv envp uid hw.
  Let tls_ok := tls_ok sp.
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).

  #[using="Hsp"] Lemma SL : 0x7fff80000000 <= usp. Proof. destruct Hsp as (H & _ & _). unfold sp_window_lo in H. exact H. Qed.
  #[using="Hsp"] Lemma SH : usp <= 0x800000000000. Proof. destruct Hsp as (_ & H & _). unfold sp_window_hi in H. exact H. Qed.
  #[using="sp envp Hva usp envc"] Lemma LA : 1 <= argc <= 1024. Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  #[using="sp argv Hve usp argc"] Lemma LE : 0 <= envc <= 256. Proof. unfold envc. destruct Hve as [H _]. lia. Qed.



  (* [comment removed for export] *)
  Definition E9 (a t : word) : env := Env (vals_ev (vals0 PH sp rdraw argv envp uid hw ++ [a; t])) (blobs0 rdraw argv).
  Definition E10 (a t c : word) : env := Env (vals_ev (vals0 PH sp rdraw argv envp uid hw ++ [a; t; c])) (blobs0 rdraw argv).

  #[using="Type"] Lemma E9_agree : forall a t, env_agree 8 (E8 a) (E9 a t).
  Proof.
    intros a t. unfold E8, Boot2.E8, E9.
    change (vals0 PH sp rdraw argv envp uid hw ++ [a; t]) with (vals0 PH sp rdraw argv envp uid hw ++ ([a] ++ [t])).
    rewrite (app_assoc _ [a] [t]).
    apply (vals_app_agree (vals0 PH sp rdraw argv envp uid hw ++ [a]) [t]).
  Qed.
  #[using="Type"] Lemma E10_agree : forall a t c, env_agree 9 (E9 a t) (E10 a t c).
  Proof.
    intros a t c. unfold E9, E10.
    change (vals0 PH sp rdraw argv envp uid hw ++ [a; t; c]) with (vals0 PH sp rdraw argv envp uid hw ++ ([a; t] ++ [c])).
    rewrite (app_assoc _ [a; t] [c]).
    apply (vals_app_agree (vals0 PH sp rdraw argv envp uid hw ++ [a; t]) [c]).
  Qed.
  #[using="Type"] Lemma ev_E9_tls : forall a t, ev (E9 a t) V_TLS = a. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ev_E9_tid : forall a t, ev (E9 a t) V_TID = t. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ev_E10_tls : forall a t c, ev (E10 a t c) V_TLS = a. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ev_E10_can : forall a t c, ev (E10 a t c) V_CANARY = c. Proof. reflexivity. Qed.

  #[using="Hsp"] Lemma above_ok_blockE : forall E lows M log,
    ev E 0%nat = sp -> lows_ok E usp lows ->
    above_ok M -> log_below_b 0%nat lows log = true -> above_ok (mem_denot E M log).
  Proof. intros. eapply (Boot2.above_ok_blockE sp rdraw argv envp uid hw Hsp); eassumption. Qed.

  Ltac vmc := lazymatch goal with |- log_below_b _ _ _ = true => vmeq_refl
                               | |- sr_vars_lt _ _ = true => vmeq_refl
                               | |- kn_vars_lt _ _ = true => vmeq_refl end.
  Ltac regne := intros HH; apply (f_equal bv_unsigned) in HH; discriminate HH.

  Definition tid_ok (t : word) : Prop := 0 < bv_unsigned t < 4194304.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="usp argc envc"] Lemma glue_settid : forall a t R M,
    tid_ok t -> regs_ok (E8 a) SR4e R -> know_ok SEGS (E8 a) M KN4e ->
    regs_ok (E9 a t) SR5 (regupd R 10%bv t) /\ know_ok SEGS (E9 a t) M KN5.
  Proof.
    intros a t R M Ht HR HK.
    assert (HR9 : regs_ok (E9 a t) SR4e R) by (eapply regs_ok_agree; [apply E9_agree | vmc | exact HR]).
    assert (HK9 : know_ok SEGS (E9 a t) M KN4e) by (eapply know_ok_agree; [apply E9_agree | vmc | exact HK]).
    split.
    - unfold SR5. apply regs_ok_set; [exact HR9 | regne | apply ev_E9_tid].
    - unfold KN5. apply know_ok_app_intro; [exact HK9|]. constructor; [|constructor].
      cbn [kentry_ok edenot]. rewrite ev_E9_tid. unfold tid_ok in Ht. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition is_kword_at (k : Z) (w : nat) (K : kentry) : bool :=
    match K with KWord (SA (ELit 0) k') w' _ => Z.eqb k k' && Nat.eqb w w' | _ => false end.

  #[using="Hsp usp argc envc"] Lemma phase5 : forall a t R M,
    tls_ok a -> tid_ok t ->
    regs_ok (E9 a t) SR5 R -> know_ok SEGS (E9 a t) M KN5 -> above_ok M -> mem_grows MEM0 M ->
    exists c R' M', msteps SEGS (mkst R (Z_to_bv 64 A_set_tid_ret) M ROM) (mkst R' (Z_to_bv 64 A_maxva_smeared) M' ROM)
      /\ regs_ok (E10 a t c) SR6e R' /\ know_ok SEGS (E10 a t c) M' KN6e /\ above_ok M' /\ mem_grows MEM0 M'.
  Proof.
    intros a t R M HT Ht HR HK HA HG. pose proof HT as (T1 & T2 & T3 & T4). pose proof SL. pose proof SH.
    (* [comment removed for export] *)
    ms_block_with HR HK FUEL [A_ssp_sb] noscr 9%nat R5 HR5 HK5 MS5.
    lazymatch type of HK5 with know_ok _ _ ?m _ => set (M5 := m) in * end.
    assert (A5 : above_ok M5).
    { unfold M5. apply (above_ok_blockE (E9 a t) [(EVar V_TLS, 4096)]); [reflexivity | | exact HA | vmc].
      constructor; [|constructor]. cbn [fst snd edenot]. rewrite ev_E9_tls. lia. }
    assert (G5 : mem_grows MEM0 M5) by (unfold M5; eapply mem_grows_trans; [exact HG | apply mem_denot_grows]).
    clearbody M5. clear HR HK HA HG.
    (* [comment removed for export] *)
    destruct (fetchd_some _ _ ssp_sb_code) as (wb & Fb & NEb & Db).
    destruct (fetchd_some _ _ ssp_ld_code) as (wl & Fl & NEl & Dl).
    assert (G10 : getr R5 10%bv = Z_to_bv 64 A_stack_chk_guard) by (rewrite (HR5 10%bv); reflexivity).
    assert (Hst1 : store_ok SEGS M5 (v_addi (getr R5 10%bv) (bv_signed (1%bv : bv 12))) 1 = true).
    { rewrite G10. unfold v_addi. rewrite u_small by (unfold A_stack_chk_guard; lia). change (bv_signed _) with 1.
      let i := kidx KN5e (is_kwr_cov (ELit 0) A_stack_chk_guard 8) in
      eapply (kwr_store_ok_lit SEGS (E9 a t) M5 KN5e i); [exact HK5 | reflexivity | ..]; unfold A_stack_chk_guard; lia. }
    pose proof (step_sb SEGS R5 (Z_to_bv 64 A_ssp_sb) M5 ROM wb 10%bv 0%bv 1%bv Fb NEb Db Hst1) as STb.
    rewrite G10 in STb. unfold v_addi in STb. rewrite !u_small in STb by (unfold A_stack_chk_guard, A_ssp_sb; lia).
    change (bv_signed (1%bv : bv 12)) with 1 in STb. rewrite <- ssp_sb_next in STb.
    set (M5' := wbytes M5 (Z_to_bv 64 (A_stack_chk_guard + 1)) (word_to_le_bytes 1 (getr R5 0%bv))) in STb.
    (* [comment removed for export] *)
    assert (RD8 : exists bs, rdn SEGS M5' (Z_to_bv 64 A_stack_chk_guard) 8 = Some bs /\ length bs = 8%nat).
    { apply rdn_readable; [rewrite u_small; unfold A_stack_chk_guard; lia|].
      intros j Hj. rewrite u_small by (unfold A_stack_chk_guard; lia).
      apply (readable_grows SEGS M5); [unfold M5'; apply wbytes_grows|].
      (* [comment removed for export] *)
      Ltac rb1 HK5 M5 a t k :=
        let i := kidx KN5e (is_kword_at (A_stack_chk_guard + k) 1) in
        pose proof (know_nth SEGS (E9 a t) M5 KN5e i _ HK5 eq_refl) as (_ & _ & RDk);
        rewrite adenot_lit0 in RDk;
        pose proof (readable_of_rdn SEGS M5 1 _ _ RDk ltac:(rewrite u_small; unfold A_stack_chk_guard; lia) 0%nat ltac:(lia)) as RR;
        rewrite u_small in RR by (unfold A_stack_chk_guard; lia);
        replace (Z_to_bv 64 (A_stack_chk_guard + Z.of_nat _)) with (Z_to_bv 64 (A_stack_chk_guard + k + Z.of_nat 0)) by (f_equal; lia);
        exact RR.
      destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; [rb1 HK5 M5 a t 0 | rb1 HK5 M5 a t 1 | rb1 HK5 M5 a t 2 | rb1 HK5 M5 a t 3
                                             | rb1 HK5 M5 a t 4 | rb1 HK5 M5 a t 5 | rb1 HK5 M5 a t 6 | rb1 HK5 M5 a t 7 | lia]. }
    destruct RD8 as (bs & RD8 & LEN8).
    set (c := Z_to_bv 64 (bytes_le_to_Z bs)).
    assert (Hc : word_to_le_bytes 8 c = bs) by (unfold c; apply word_to_le_bytes_of_lez; [exact LEN8 | lia]).
    (* [comment removed for export] *)
    pose proof (step_ld SEGS R5 (Z_to_bv 64 A_ssp_ld) M5' ROM wl 10%bv 10%bv 0%bv bs c Fl NEl Dl) as STl.
    rewrite G10 in STl. unfold v_addi in STl. rewrite !u_small in STl by (unfold A_stack_chk_guard, A_ssp_ld; lia).
    change (bv_signed (0%bv : bv 12)) with 0 in STl. rewrite Z.add_0_r, <- ssp_ld_next in STl.
    specialize (STl RD8).
    replace (bv_eqb (10%bv : reg) (0%bv : reg)) with false in STl by reflexivity.  (* [comment removed for export] *)
    assert (Hcu : bytes_le_to_Z bs = bv_unsigned c).
    { unfold c. rewrite u_small; [reflexivity|]. pose proof (AX2S.bytes_le_to_Z_bound bs) as B. rewrite LEN8 in B. cbn in B. lia. }
    specialize (STl Hcu).
    (* [comment removed for export] *)
    assert (HR6 : regs_ok (E10 a t c) SR6 (regupd R5 10%bv c)).
    { unfold SR6. apply regs_ok_set; [| regne | apply ev_E10_can].
      eapply regs_ok_agree; [apply E10_agree | vmc | exact HR5]. }
    assert (HK6 : know_ok SEGS (E10 a t c) M5' KN6).
    { unfold KN6. constructor.
      - cbn [kentry_ok]. split; [lia|]. split.
        + unfold flat, estart. cbn [a_base a_off edenot]. rewrite u_small by lia. unfold A_stack_chk_guard. lia.
        + rewrite adenot_lit0. cbn [edenot]. rewrite ev_E10_can, Hc. exact RD8.
      - apply (know_change_keep SEGS (E10 a t c) M5 M5').
        + eapply know_ok_agree; [apply E10_agree | vmc | exact HK5].
        + intros x Hx. unfold M5'. apply wbytes_outside; rewrite ?length_N_to_le_bytes; rewrite u_small by (unfold A_stack_chk_guard; lia).
          * unfold A_stack_chk_guard. cbn. lia.
          * unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx. rewrite !u_small in Hx by (unfold A_stack_chk_guard; lia).
            cbn [length word_to_le_bytes Z_to_le_bytes Z.of_nat]. lia.
        + unfold M5'. apply wbytes_grows. }
    assert (A5' : above_ok M5').
    { intros x Hx. unfold M5'. rewrite wbytes_outside; rewrite ?length_N_to_le_bytes; try (rewrite u_small by (unfold A_stack_chk_guard; lia)).
      - apply A5. exact Hx.
      - unfold A_stack_chk_guard. cbn. lia.
      - right. cbn [length word_to_le_bytes Z_to_le_bytes]. unfold A_stack_chk_guard. unfold usp in *. lia. }
    assert (G5' : mem_grows MEM0 M5') by (eapply mem_grows_trans; [exact G5 | unfold M5'; apply wbytes_grows]).
    clearbody M5'.
    (* [comment removed for export] *)
    assert (B6 : exists R7 M7, msteps SEGS (mkst (regupd R5 10%bv c) (Z_to_bv 64 A_ssp_after_ld) M5' ROM) (mkst R7 (Z_to_bv 64 A_maxva_smeared) M7 ROM)
                 /\ regs_ok (E10 a t c) SR6e R7 /\ know_ok SEGS (E10 a t c) M7 KN6e /\ above_ok M7 /\ mem_grows MEM0 M7).
    { ms_block_with HR6 HK6 FUEL [A_maxva_smeared] noscr 10%nat R7 HR7 HK7 MS7.
      lazymatch type of HK7 with know_ok _ _ ?m _ => set (M7 := m) in * end.
      assert (A7 : above_ok M7).
      { unfold M7. apply (above_ok_blockE (E10 a t c) [(EVar V_TLS, 4096)]); [reflexivity | | exact A5' | vmc].
        constructor; [|constructor]. cbn [fst snd edenot]. rewrite ev_E10_tls. lia. }
      assert (G7 : mem_grows MEM0 M7) by (unfold M7; eapply mem_grows_trans; [exact G5' | apply mem_denot_grows]).
      clearbody M7. exists R7, M7. repeat split; assumption. }
    destruct B6 as (R7 & M7 & MS7 & HR7 & HK7 & A7 & G7).
    exists c, R7, M7. split; [|split; [exact HR7 | split; [exact HK7 | split; [exact A7 | exact G7]]]].
    eapply msteps_trans; [exact MS5|].
    eapply mst_step; [reflexivity | exact STb |].
    eapply mst_step; [reflexivity | exact STl |].
    exact MS7.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Type"] Lemma sr6e_a0 : sr_get SR6e 10%bv = smear_reg (EAlu ALU_ADD (EVar V_SP) (ELit (-160))).
  Proof. vmeq_refl. Qed.

  #[using="Type"] Lemma ev_E10_sp : forall a t c, ev (E10 a t c) V_SP = sp. Proof. reflexivity. Qed.

  #[using="Hsp usp argc envc"] Lemma frame_range : forall a t c,
    2 ^ 46 <= bv_unsigned (edenot (E10 a t c) (EAlu ALU_ADD (EVar V_SP) (ELit (-160)))) < 2 ^ 47.
  Proof.
    intros a t c. pose proof SL. pose proof SH. cbn [edenot]. rewrite ev_E10_sp, u_add64.
    change (bv_unsigned (Z_to_bv 64 (-160))) with (2 ^ 64 - 160).
    replace (bv_unsigned sp + (2 ^ 64 - 160)) with ((bv_unsigned sp - 160) + 1 * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full, Z.mod_small by (unfold usp in *; lia). unfold usp in *. lia.
  Qed.

  #[using="Hsp usp argc envc"] Lemma phase6 : forall a t c R M,
    tls_ok a ->
    regs_ok (E10 a t c) SR6e R -> know_ok SEGS (E10 a t c) M KN6e -> above_ok M -> mem_grows MEM0 M ->
    exists R' M', msteps SEGS (mkst R (Z_to_bv 64 A_maxva_smeared) M ROM) (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM)
      /\ regs_ok (E10 a t c) SR_E3 R' /\ know_ok SEGS (E10 a t c) M' KN_E3 /\ above_ok M' /\ mem_grows MEM0 M'.
  Proof.
    intros a t c R M HT HR HK HA HG. pose proof SL. pose proof SH.
    (* [comment removed for export] *)
    assert (HR7 : regs_ok (E10 a t c) SR7 R).
    { unfold SR7. apply (regs_ok_upd1 (E10 a t c) SR6e R R 10%bv); [exact HR | regne | | intros; reflexivity].
      rewrite (HR 10%bv), sr6e_a0. change (edenot (E10 a t c) (ELit MAXVA)) with (Z_to_bv 64 MAXVA). unfold MAXVA.
      apply smear_reg_val. apply frame_range. }
    clear HR.
    ms_block_with HR7 HK FUEL [A_internal_mmap_ecall] noscr 10%nat R8 HR8 HK8 MS8.
    lazymatch type of HK8 with know_ok _ _ ?m _ => set (M8 := m) in * end.
    assert (A8 : above_ok M8).
    { unfold M8. apply (above_ok_blockE (E10 a t c) [(EVar V_TLS, 4096)]); [reflexivity | | exact HA | vmc].
      constructor; [|constructor]. cbn [fst snd edenot]. rewrite ev_E10_tls. pose proof HT as (T1 & T2 & T3 & T4). lia. }
    assert (G8 : mem_grows MEM0 M8) by (unfold M8; eapply mem_grows_trans; [exact HG | apply mem_denot_grows]).
    clearbody M8. exists R8, M8. repeat split; assumption.
  Qed.
End Walk.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.StartupAux OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefLayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.ArgvEnv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.Hoare OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanStartLoops OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.ExitSim.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryKn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.EntryGlue.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.BootKn1__A3.BootKn1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.Boot2.TwB.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance boot3_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables argv envp : list (list byte).
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.

  (* [comment removed for export] *)
  Let E7 : env := E7 sp rdraw argv envp uid hw.
  Let MEM0 : word -> option byte := MEM0 sp rdraw argv envp uid hw.
  Let above_ok := above_ok sp rdraw argv envp uid hw.
  Let E8 := E8 sp rdraw argv envp uid hw.
  Let tls_ok := tls_ok sp.
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).

  #[using="Hsp"] Lemma SL : 0x7fff80000000 <= usp. Proof. destruct Hsp as (H & _ & _). unfold sp_window_lo in H. exact H. Qed.
  #[using="Hsp"] Lemma SH : usp <= 0x800000000000. Proof. destruct Hsp as (_ & H & _). unfold sp_window_hi in H. exact H. Qed.
  #[using="sp envp Hva usp envc"] Lemma LA : 1 <= argc <= 1024. Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  #[using="sp argv Hve usp argc"] Lemma LE : 0 <= envc <= 256. Proof. unfold envc. destruct Hve as [H _]. lia. Qed.



  (* [comment removed for export] *)
  Definition E9 (a t : word) : env := Env (vals_ev (vals0 PH sp rdraw argv envp uid hw ++ [a; t])) (blobs0 rdraw argv).
  Definition E10 (a t c : word) : env := Env (vals_ev (vals0 PH sp rdraw argv envp uid hw ++ [a; t; c])) (blobs0 rdraw argv).

  #[using="Type"] Lemma E9_agree : forall a t, env_agree 8 (E8 a) (E9 a t).
  Proof.
    intros a t. unfold E8, A3.Boot2.TwB.E8, E9.
    change (vals0 PH sp rdraw argv envp uid hw ++ [a; t]) with (vals0 PH sp rdraw argv envp uid hw ++ ([a] ++ [t])).
    rewrite (app_assoc _ [a] [t]).
    apply (vals_app_agree (vals0 PH sp rdraw argv envp uid hw ++ [a]) [t]).
  Qed.
  #[using="Type"] Lemma E10_agree : forall a t c, env_agree 9 (E9 a t) (E10 a t c).
  Proof.
    intros a t c. unfold E9, E10.
    change (vals0 PH sp rdraw argv envp uid hw ++ [a; t; c]) with (vals0 PH sp rdraw argv envp uid hw ++ ([a; t] ++ [c])).
    rewrite (app_assoc _ [a; t] [c]).
    apply (vals_app_agree (vals0 PH sp rdraw argv envp uid hw ++ [a; t]) [c]).
  Qed.
  #[using="Type"] Lemma ev_E9_tls : forall a t, ev (E9 a t) V_TLS = a. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ev_E9_tid : forall a t, ev (E9 a t) V_TID = t. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ev_E10_tls : forall a t c, ev (E10 a t c) V_TLS = a. Proof. reflexivity. Qed.
  #[using="Type"] Lemma ev_E10_can : forall a t c, ev (E10 a t c) V_CANARY = c. Proof. reflexivity. Qed.

  #[using="Hsp"] Lemma above_ok_blockE : forall E lows M log,
    ev E 0%nat = sp -> lows_ok E usp lows ->
    above_ok M -> log_below_b 0%nat lows log = true -> above_ok (mem_denot E M log).
  Proof. intros. eapply (A3.Boot2.TwB.above_ok_blockE sp rdraw argv envp uid hw Hsp); eassumption. Qed.

  Ltac vmc := lazymatch goal with |- log_below_b _ _ _ = true => vmeq_refl
                               | |- sr_vars_lt _ _ = true => vmeq_refl
                               | |- kn_vars_lt _ _ = true => vmeq_refl end.
  Ltac regne := intros HH; apply (f_equal bv_unsigned) in HH; discriminate HH.

  Definition tid_ok (t : word) : Prop := 0 < bv_unsigned t < 4194304.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="usp argc envc"] Lemma glue_settid : forall a t R M,
    tid_ok t -> regs_ok (E8 a) SR4e R -> know_ok SEGS (E8 a) M KN4e ->
    regs_ok (E9 a t) SR5 (regupd R 10%bv t) /\ know_ok SEGS (E9 a t) M KN5.
  Proof.
    intros a t R M Ht HR HK.
    assert (HR9 : regs_ok (E9 a t) SR4e R) by (eapply regs_ok_agree; [apply E9_agree | vmc | exact HR]).
    assert (HK9 : know_ok SEGS (E9 a t) M KN4e) by (eapply know_ok_agree; [apply E9_agree | vmc | exact HK]).
    split.
    - unfold SR5. apply regs_ok_set; [exact HR9 | regne | apply ev_E9_tid].
    - unfold KN5. apply know_ok_app_intro; [exact HK9|]. constructor; [|constructor].
      cbn [kentry_ok edenot]. rewrite ev_E9_tid. unfold tid_ok in Ht. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition is_kword_at (k : Z) (w : nat) (K : kentry) : bool :=
    match K with KWord (SA (ELit 0) k') w' _ => Z.eqb k k' && Nat.eqb w w' | _ => false end.

  #[using="Hsp usp argc envc"] Lemma phase5 : forall a t R M,
    tls_ok a -> tid_ok t ->
    regs_ok (E9 a t) SR5 R -> know_ok SEGS (E9 a t) M KN5 -> above_ok M -> mem_grows MEM0 M ->
    exists c R' M', msteps SEGS (mkst R (Z_to_bv 64 A_set_tid_ret) M ROM) (mkst R' (Z_to_bv 64 A_maxva_smeared) M' ROM)
      /\ regs_ok (E10 a t c) SR6e R' /\ know_ok SEGS (E10 a t c) M' KN6e /\ above_ok M' /\ mem_grows MEM0 M'.
  Proof.
    intros a t R M HT Ht HR HK HA HG. pose proof HT as (T1 & T2 & T3 & T4). pose proof SL. pose proof SH.
    (* [comment removed for export] *)
    ms_block_with HR HK FUEL [A_ssp_sb] noscr 9%nat R5 HR5 HK5 MS5.
    lazymatch type of HK5 with know_ok _ _ ?m _ => set (M5 := m) in * end.
    assert (A5 : above_ok M5).
    { unfold M5. apply (above_ok_blockE (E9 a t) [(EVar V_TLS, 4096)]); [reflexivity | | exact HA | vmc].
      constructor; [|constructor]. cbn [fst snd edenot]. rewrite ev_E9_tls. lia. }
    assert (G5 : mem_grows MEM0 M5) by (unfold M5; eapply mem_grows_trans; [exact HG | apply mem_denot_grows]).
    clearbody M5. clear HR HK HA HG.
    (* [comment removed for export] *)
    destruct (fetchd_some _ _ ssp_sb_code) as (wb & Fb & NEb & Db).
    destruct (fetchd_some _ _ ssp_ld_code) as (wl & Fl & NEl & Dl).
    assert (G10 : getr R5 10%bv = Z_to_bv 64 A_stack_chk_guard) by (rewrite (HR5 10%bv); reflexivity).
    assert (Hst1 : store_ok SEGS M5 (v_addi (getr R5 10%bv) (bv_signed (1%bv : bv 12))) 1 = true).
    { rewrite G10. unfold v_addi. rewrite u_small by (unfold A_stack_chk_guard; lia). change (bv_signed _) with 1.
      let i := kidx KN5e (is_kwr_cov (ELit 0) A_stack_chk_guard 8) in
      eapply (kwr_store_ok_lit SEGS (E9 a t) M5 KN5e i); [exact HK5 | reflexivity | ..]; unfold A_stack_chk_guard; lia. }
    pose proof (step_sb SEGS R5 (Z_to_bv 64 A_ssp_sb) M5 ROM wb 10%bv 0%bv 1%bv Fb NEb Db Hst1) as STb.
    rewrite G10 in STb. unfold v_addi in STb. rewrite !u_small in STb by (unfold A_stack_chk_guard, A_ssp_sb; lia).
    change (bv_signed (1%bv : bv 12)) with 1 in STb. rewrite <- ssp_sb_next in STb.
    set (M5' := wbytes M5 (Z_to_bv 64 (A_stack_chk_guard + 1)) (word_to_le_bytes 1 (getr R5 0%bv))) in STb.
    (* [comment removed for export] *)
    assert (RD8 : exists bs, rdn SEGS M5' (Z_to_bv 64 A_stack_chk_guard) 8 = Some bs /\ length bs = 8%nat).
    { apply rdn_readable; [rewrite u_small; unfold A_stack_chk_guard; lia|].
      intros j Hj. rewrite u_small by (unfold A_stack_chk_guard; lia).
      apply (readable_grows SEGS M5); [unfold M5'; apply wbytes_grows|].
      (* [comment removed for export] *)
      Ltac rb1 HK5 M5 a t k :=
        let i := kidx KN5e (is_kword_at (A_stack_chk_guard + k) 1) in
        pose proof (know_nth SEGS (E9 a t) M5 KN5e i _ HK5 eq_refl) as (_ & _ & RDk);
        rewrite adenot_lit0 in RDk;
        pose proof (readable_of_rdn SEGS M5 1 _ _ RDk ltac:(rewrite u_small; unfold A_stack_chk_guard; lia) 0%nat ltac:(lia)) as RR;
        rewrite u_small in RR by (unfold A_stack_chk_guard; lia);
        replace (Z_to_bv 64 (A_stack_chk_guard + Z.of_nat _)) with (Z_to_bv 64 (A_stack_chk_guard + k + Z.of_nat 0)) by (f_equal; lia);
        exact RR.
      destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; [rb1 HK5 M5 a t 0 | rb1 HK5 M5 a t 1 | rb1 HK5 M5 a t 2 | rb1 HK5 M5 a t 3
                                             | rb1 HK5 M5 a t 4 | rb1 HK5 M5 a t 5 | rb1 HK5 M5 a t 6 | rb1 HK5 M5 a t 7 | lia]. }
    destruct RD8 as (bs & RD8 & LEN8).
    set (c := Z_to_bv 64 (bytes_le_to_Z bs)).
    assert (Hc : word_to_le_bytes 8 c = bs) by (unfold c; apply word_to_le_bytes_of_lez; [exact LEN8 | lia]).
    (* [comment removed for export] *)
    pose proof (step_ld SEGS R5 (Z_to_bv 64 A_ssp_ld) M5' ROM wl 10%bv 10%bv 0%bv bs c Fl NEl Dl) as STl.
    rewrite G10 in STl. unfold v_addi in STl. rewrite !u_small in STl by (unfold A_stack_chk_guard, A_ssp_ld; lia).
    change (bv_signed (0%bv : bv 12)) with 0 in STl. rewrite Z.add_0_r, <- ssp_ld_next in STl.
    specialize (STl RD8).
    replace (bv_eqb (10%bv : reg) (0%bv : reg)) with false in STl by reflexivity.  (* [comment removed for export] *)
    assert (Hcu : bytes_le_to_Z bs = bv_unsigned c).
    { unfold c. rewrite u_small; [reflexivity|]. pose proof (AX2S.bytes_le_to_Z_bound bs) as B. rewrite LEN8 in B. cbn in B. lia. }
    specialize (STl Hcu).
    (* [comment removed for export] *)
    assert (HR6 : regs_ok (E10 a t c) SR6 (regupd R5 10%bv c)).
    { unfold SR6. apply regs_ok_set; [| regne | apply ev_E10_can].
      eapply regs_ok_agree; [apply E10_agree | vmc | exact HR5]. }
    assert (HK6 : know_ok SEGS (E10 a t c) M5' KN6).
    { unfold KN6. constructor.
      - cbn [kentry_ok]. split; [lia|]. split.
        + unfold flat, estart. cbn [a_base a_off edenot]. rewrite u_small by lia. unfold A_stack_chk_guard. lia.
        + rewrite adenot_lit0. cbn [edenot]. rewrite ev_E10_can, Hc. exact RD8.
      - apply (know_change_keep SEGS (E10 a t c) M5 M5').
        + eapply know_ok_agree; [apply E10_agree | vmc | exact HK5].
        + intros x Hx. unfold M5'. apply wbytes_outside; rewrite ?length_N_to_le_bytes; rewrite u_small by (unfold A_stack_chk_guard; lia).
          * unfold A_stack_chk_guard. cbn. lia.
          * unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx. rewrite !u_small in Hx by (unfold A_stack_chk_guard; lia).
            cbn [length word_to_le_bytes Z_to_le_bytes Z.of_nat]. lia.
        + unfold M5'. apply wbytes_grows. }
    assert (A5' : above_ok M5').
    { intros x Hx. unfold M5'. rewrite wbytes_outside; rewrite ?length_N_to_le_bytes; try (rewrite u_small by (unfold A_stack_chk_guard; lia)).
      - apply A5. exact Hx.
      - unfold A_stack_chk_guard. cbn. lia.
      - right. cbn [length word_to_le_bytes Z_to_le_bytes]. unfold A_stack_chk_guard. unfold usp in *. lia. }
    assert (G5' : mem_grows MEM0 M5') by (eapply mem_grows_trans; [exact G5 | unfold M5'; apply wbytes_grows]).
    clearbody M5'.
    (* [comment removed for export] *)
    assert (B6 : exists R7 M7, msteps SEGS (mkst (regupd R5 10%bv c) (Z_to_bv 64 A_ssp_after_ld) M5' ROM) (mkst R7 (Z_to_bv 64 A_maxva_smeared) M7 ROM)
                 /\ regs_ok (E10 a t c) SR6e R7 /\ know_ok SEGS (E10 a t c) M7 KN6e /\ above_ok M7 /\ mem_grows MEM0 M7).
    { ms_block_with HR6 HK6 FUEL [A_maxva_smeared] noscr 10%nat R7 HR7 HK7 MS7.
      lazymatch type of HK7 with know_ok _ _ ?m _ => set (M7 := m) in * end.
      assert (A7 : above_ok M7).
      { unfold M7. apply (above_ok_blockE (E10 a t c) [(EVar V_TLS, 4096)]); [reflexivity | | exact A5' | vmc].
        constructor; [|constructor]. cbn [fst snd edenot]. rewrite ev_E10_tls. lia. }
      assert (G7 : mem_grows MEM0 M7) by (unfold M7; eapply mem_grows_trans; [exact G5' | apply mem_denot_grows]).
      clearbody M7. exists R7, M7. repeat split; assumption. }
    destruct B6 as (R7 & M7 & MS7 & HR7 & HK7 & A7 & G7).
    exists c, R7, M7. split; [|split; [exact HR7 | split; [exact HK7 | split; [exact A7 | exact G7]]]].
    eapply msteps_trans; [exact MS5|].
    eapply mst_step; [reflexivity | exact STb |].
    eapply mst_step; [reflexivity | exact STl |].
    exact MS7.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Type"] Lemma sr6e_a0 : sr_get SR6e 10%bv = smear_reg (EAlu ALU_ADD (EVar V_SP) (ELit (-160))).
  Proof. vmeq_refl. Qed.

  #[using="Type"] Lemma ev_E10_sp : forall a t c, ev (E10 a t c) V_SP = sp. Proof. reflexivity. Qed.

  #[using="Hsp usp argc envc"] Lemma frame_range : forall a t c,
    2 ^ 46 <= bv_unsigned (edenot (E10 a t c) (EAlu ALU_ADD (EVar V_SP) (ELit (-160)))) < 2 ^ 47.
  Proof.
    intros a t c. pose proof SL. pose proof SH. cbn [edenot]. rewrite ev_E10_sp, u_add64.
    change (bv_unsigned (Z_to_bv 64 (-160))) with (2 ^ 64 - 160).
    replace (bv_unsigned sp + (2 ^ 64 - 160)) with ((bv_unsigned sp - 160) + 1 * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full, Z.mod_small by (unfold usp in *; lia). unfold usp in *. lia.
  Qed.

  #[using="Hsp usp argc envc"] Lemma phase6 : forall a t c R M,
    tls_ok a ->
    regs_ok (E10 a t c) SR6e R -> know_ok SEGS (E10 a t c) M KN6e -> above_ok M -> mem_grows MEM0 M ->
    exists R' M', msteps SEGS (mkst R (Z_to_bv 64 A_maxva_smeared) M ROM) (mkst R' (Z_to_bv 64 A_internal_mmap_ecall) M' ROM)
      /\ regs_ok (E10 a t c) SR_E3 R' /\ know_ok SEGS (E10 a t c) M' KN_E3 /\ above_ok M' /\ mem_grows MEM0 M'.
  Proof.
    intros a t c R M HT HR HK HA HG. pose proof SL. pose proof SH.
    (* [comment removed for export] *)
    assert (HR7 : regs_ok (E10 a t c) SR7 R).
    { unfold SR7. apply (regs_ok_upd1 (E10 a t c) SR6e R R 10%bv); [exact HR | regne | | intros; reflexivity].
      rewrite (HR 10%bv), sr6e_a0. change (edenot (E10 a t c) (ELit MAXVA)) with (Z_to_bv 64 MAXVA). unfold MAXVA.
      apply smear_reg_val. apply frame_range. }
    clear HR.
    ms_block_with HR7 HK FUEL [A_internal_mmap_ecall] noscr 10%nat R8 HR8 HK8 MS8.
    lazymatch type of HK8 with know_ok _ _ ?m _ => set (M8 := m) in * end.
    assert (A8 : above_ok M8).
    { unfold M8. apply (above_ok_blockE (E10 a t c) [(EVar V_TLS, 4096)]); [reflexivity | | exact HA | vmc].
      constructor; [|constructor]. cbn [fst snd edenot]. rewrite ev_E10_tls. pose proof HT as (T1 & T2 & T3 & T4). lia. }
    assert (G8 : mem_grows MEM0 M8) by (unfold M8; eapply mem_grows_trans; [exact HG | apply mem_denot_grows]).
    clearbody M8. exists R8, M8. repeat split; assumption.
  Qed.
End Walk.
End TwB.
(* [comment removed for export] *) Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
