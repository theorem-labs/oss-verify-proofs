(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)

From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import RunCtx.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.World Require Import Tgt_checksum_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import
  StartupTac ArgvEnv RefLayout U0Img U0StartupDefs U0_code_15000_16000  .
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require L10Walk.
Ltac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.StepTac.chain_step ::= OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_chain_step.

Abbreviation SEGS := Tgt_checksum_fuzzer_ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Tgt_checksum_fuzzer_ubsan.M.phdrs.

Section P3.
  (* port727 (): the launch as Common/ArgvEnv's Scaffold has it. *)
  Variable sp0 : word.
  Variable inp : ProcInput.
  Variables mbase brk : word.
#[local] Instance RC_a1_1 : RunCtx := mkRunCtx inp sp0 mbase.
  Variable rdraw : EntryDraw.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Local Notation gid := (in_gid inp) (only parsing).
  Local Notation rseq := (kb_rseq (in_kernel inp)) (only parsing).
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation ENT := (Z_to_bv 64 (Z.of_N Tgt_checksum_fuzzer_ubsan.M.init_pc)) (only parsing).
  Local Notation mem0 := (wrap_mem inp mbase RPH ENT sp0 rdraw) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH ENT sp0 rdraw)) (only parsing).
  Local Notation stk := (stack_to_mem sp0 (entry_stack_image inp mbase RPH ENT sp0 rdraw)) (only parsing).
  Local Notation E := (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))%Z (only parsing).
  Local Notation A := (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))%Z (only parsing).

  Local Notation pn := (cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 0) (only parsing).
  Local Notation rnd := (at_random_ptr sp0 rseq av ev) (only parsing).
  Local Notation xfn := (at_execfn_ptr (ed_top rdraw) (in_execfn inp)) (only parsing).
  Local Notation s := (nth 0 av []) (only parsing).
  Local Notation A8 := (Z_to_bv 64 0x50000) (only parsing).

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.
  Lemma len_ev : (Z.of_nat (length ev) <= 256)%Z.
  Proof. destruct Hve as [H1 _]. lia. Qed.

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.


  Lemma rd_above : forall J D (a : Z) n bs,
    (bv_unsigned sp0 <= a)%Z -> (a + Z.of_nat n < 2^64)%Z ->
    rdn (run_segments SEGS rc_inp rc_sp rc_mb) stk (Z_to_bv 64 a) n = Some bs ->
    rdn (run_segments SEGS rc_inp rc_sp rc_mb) (CM J D) (Z_to_bv 64 a) n = Some bs.
  Proof.
    intros J D a n bs Ha Hn H. pose proof (u64_range (Z_to_bv 64 a)).
    rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). exact H.
  Qed.

  Lemma rd_envp : forall J D k, (k < length ev)%nat ->
    rdn (run_segments SEGS rc_inp rc_sp rc_mb) (CM J D) (Z_to_bv 64 (E + 8 * Z.of_nat k)) 8
    = Some (word_to_le_bytes 8 (cat_envp_ptr (ed_top rdraw) av ev (in_execfn inp) k)).
  Proof.
    intros J D k Hk. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (E + 8 * Z.of_nat k)) with (sp0 + nat_to_word (envp_off av + 8 * k))
      by (rewrite word_add_nat; f_equal; unfold envp_off; lia).
    eapply read_envp_ptr_k; first [eassumption | exact Hsp_hi' | exact Hk].
  Qed.

  Lemma rd_envp_null : forall J D,
    rdn (run_segments SEGS rc_inp rc_sp rc_mb) (CM J D) (Z_to_bv 64 (E + 8 * Z.of_nat (length ev))) 8
    = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Proof.
    intros J D. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (E + 8 * Z.of_nat (length ev)))
      with (sp0 + nat_to_word (envp_off av + 8 * length ev))
      by (rewrite word_add_nat; f_equal; unfold envp_off; lia).
    eapply read_envp_null; first [eassumption | exact Hsp_hi'].
  Qed.

  (* port727: 's vector, 2 * auxv_count rseq words (Common/RefLayout.read_auxv_word). *)
  Lemma rd_auxv : forall J D j w, (j < 2 * auxv_count rseq)%nat ->
    nth j (auxv_words (launch_auxv inp sp0 mbase) RPH ENT uid gid hw rnd xfn) (Z_to_bv 64 0) = w ->
    rdn (run_segments SEGS rc_inp rc_sp rc_mb) (CM J D) (Z_to_bv 64 (A + 8 * Z.of_nat j)) 8 = Some (word_to_le_bytes 8 w).
  Proof.
    intros J D j w Hj Hw. pose proof len_av. pose proof len_ev.
    assert (Hj' : (j < 58)%nat) by (destruct (kb_rseq (in_kernel inp)); cbn [auxv_count] in Hj; lia).
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (A + 8 * Z.of_nat j)) with (sp0 + nat_to_word (auxv_off av ev + 8 * j))
      by (rewrite word_add_nat; f_equal; unfold auxv_off; lia).
    rewrite <- Hw. eapply read_auxv_word; first [eassumption | exact Hsp_hi'].
  Qed.

  Lemma envp_loop : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall n k regs J D rom,
    (k + n = length ev)%nat ->
    getr regs 9 = Z_to_bv 64 (E + 8 * Z.of_nat k) ->
    (forall regs',
        getr regs' 9 = Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8) ->
        getr regs' 10 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [9; 10]%list) regs regs' ->
        G (mkst regs' (0x155b8 : word) (CM J D) rom)) ->
    G (mkst regs (0x155ac : word) (CM J D) rom).
  Proof.
    intros G HG.
    pose proof len_av as Hlen. pose proof len_ev as Hlev.
    induction n as [|n IH]; intros k regs J D rom Hkn H9 Hk0.
    -
      assert (k = length ev) by lia. subst k.
      eapply HG.
      { ld_step F_15500 D_15500 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
          ltac:(apply rd_envp_null) ltac:(apply bytes_le_to_Z_8).
        sv F_15504 D_15504 (Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8)).
        stepb_ft F_15508 D_15508 ltac:(pin; cond_compute).
        OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
      apply Hk0; [gres; reflexivity | gres; reflexivity | solve_regs_agree].
    - assert (Hk : (k < length ev)%nat) by lia.
      pose proof (cat_envp_ptr_nz Sv48 inp mbase RPH ENT sp0 brk rdraw Hvl Hlau Hsp_lo' Hsp_hi' k Hk) as Hnz.
      eapply HG.
      { ld_step F_15500 D_15500 (word_to_le_bytes 8 (cat_envp_ptr (ed_top rdraw) av ev (in_execfn inp) k)) (cat_envp_ptr (ed_top rdraw) av ev (in_execfn inp) k)
          ltac:(apply rd_envp; exact Hk) ltac:(apply bytes_le_to_Z_8).
        sv F_15504 D_15504 (Z_to_bv 64 (E + 8 * Z.of_nat (S k))).
        stepb_tk F_15508 D_15508 ltac:(pin; apply c_eq_0_false; exact Hnz).
        OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
      eapply (IH (S k)); [lia | gres; reflexivity |].
      intros regs' H9' H10' Hag. apply Hk0; [exact H9' | exact H10' |].
      eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
  Qed.


  Lemma pn_bounds :
    (bv_unsigned sp0 <= bv_unsigned pn)%Z
    /\ (bv_unsigned pn + Z.of_nat (length s) + 1 < 2^64)%Z.
  Proof.
    pose proof len_av.
    exact (argv_ptr_bounds_at Sv48 inp mbase sp0 brk rdraw Hlau 0 ltac:(lia)).
  Qed.

  Lemma rd_argv0_byte : forall J D j b, (j <= length s)%nat ->
    nth j (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = b ->
    rdn (run_segments SEGS rc_inp rc_sp rc_mb) (CM J D) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j)) 1 = Some [b].
  Proof.
    intros J D j b Hj Hb. pose proof len_av. pose proof pn_bounds as [Hp1 Hp2].
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j)) with (pn + nat_to_word j)
      by (rewrite word_add_nat; reflexivity).
    rewrite <- Hb.
    exact (read_argv_byte_k Sv48 (run_segments SEGS rc_inp rc_sp rc_mb) inp mbase RPH ENT sp0 brk rdraw 0 j Hlau ltac:(lia) Hj).
  Qed.

  Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
  Proof. intros; subst; reflexivity. Qed.

  Lemma c_eq_byte47 : forall b : byte,
    c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 47) = bv_eqb b (Z_to_bv 8 47).
  Proof.
    intros b. pose proof (u8_range b). unfold c_eq, bv_eqb.
    rewrite !u_Z2bv by lia. reflexivity.
  Qed.

  Lemma c_eq_byte0 : forall b : byte, b <> Z_to_bv 8 0 ->
    c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 0) = false.
  Proof.
    intros b Hb. pose proof (u8_range b). apply c_eq_0_false. rewrite u_Z2bv by lia.
    intro Hz. apply Hb. apply bv_eq. rewrite Hz. reflexivity.
  Qed.

  Lemma prog_loop : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall l2 j acc regs J D rom,
    skipn j s = l2 -> (j <= length s)%nat -> (acc <= j)%nat ->
    getr regs 10 = Z_to_bv 64 0x50000 ->
    getr regs 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1) ->
    getr regs 12 = Z_to_bv 64 47 ->
    (forall regs',
        getr regs' 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat (length s) + 1) ->
        regs_agree (fun r => In r [11; 13]%list) regs regs' ->
        G (mkst regs' (0x1567c : word)
                       (CM J (wbytes D A8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn
                                 + Z.of_nat (after_last_slash l2 j acc)))))) rom)) ->
    G (mkst regs (0x15670 : word)
                   (CM J (wbytes D A8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat acc))))) rom).
  Proof.
    intros G HG.
    pose proof len_av as Hlen. pose proof pn_bounds as [Hp1 Hp2].
    pose proof (valid_argv_str_nz av 0 Hva ltac:(lia)) as Hnz.
    induction l2 as [|b l2 IH]; intros j acc regs J D rom Hskip Hj Hacc H10 H11 H12 Hk0.
    -
      assert (Hjl : j = length s).
      { pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
      eapply HG.
      { lb_step F_155c4 D_155c4 (Z_to_bv 8 0)
          ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | subst j; rewrite app_nth2 by lia; rewrite Nat.sub_diag; reflexivity] | f_equal; lia]).
        stepb_ft F_155c8 D_155c8 ltac:(pin; cond_compute).
        stepb_ft F_155cc D_155cc ltac:(pin; cond_compute).
        OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
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
      +
        eapply HG.
        { lb_step F_155c4 D_155c4 b
            ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
          stepb_tk F_155c8 D_155c8 ltac:(pin; rewrite c_eq_byte47; exact Eb).
          stw F_155bc D_155bc (Z_to_bv 64 0x50000) (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) + Z.of_nat j + 1)) ltac:(ok_data).
          rewrite wbytes_shadow by (rewrite ?length_N_to_le_bytes; rewrite ?length_N_to_le_bytes; first [reflexivity | region_side]).
          sv F_155c0 D_155c0 (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) + Z.of_nat (S j) + 1)).
          OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
        replace (bv_unsigned pn + Z.of_nat j + 1)%Z with (bv_unsigned pn + Z.of_nat (S j))%Z by lia.
        eapply (IH (S j) (S j)); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
        intros regs' H11' Hag. apply Hk0; [exact H11'|].
        eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
      + eapply HG.
        { lb_step F_155c4 D_155c4 b
            ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
          stepb_ft F_155c8 D_155c8 ltac:(pin; rewrite c_eq_byte47; exact Eb).
          stepb_tk F_155cc D_155cc ltac:(pin; apply c_eq_byte0; exact Hbnz).
          sv F_155c0 D_155c0 (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) + Z.of_nat (S j) + 1)).
          OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
        eapply (IH (S j) acc); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
        intros regs' H11' Hag. apply Hk0; [exact H11'|].
        eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
  Qed.



  (* port727: the bound and the word, once the kernel's CONFIG_RSEQ is fixed (the destruct's
     equation, found by its type). *)
  Ltac rsq := match goal with H : kb_rseq (in_kernel _) = _ |- _ => rewrite H end.
  Ltac rdA j w := eapply rdn_addr; [apply (rd_auxv _ _ j w);
      [ rsq; cbn [auxv_count]; lia
      | unfold auxv_words, auxv_entries, launch_auxv; cbn [la_rseq la_sysinfo_ehdr la_cache la_minsigstksz];
        try rsq; reflexivity ] | f_equal; lia].

  Lemma p3_run : forall G, bwd (run_segments SEGS rc_inp rc_sp rc_mb) G -> forall regs Jf rom,
    wfJ sp0 Jf ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 8 = pn ->
    getr regs 9 = envp_w sp0 inp ->
    getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
    (forall regs',
        getr regs' 1 = Z_to_bv 64 0x15684 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
        getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
        getr regs' 18 = Z_to_bv 64 0x50010 ->
        regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 18]%list) regs regs' ->
        G (mkst regs' (0x15894 : word) (CM (J_aux sp0 inp mbase rdraw Jf) (D_libc sp0 inp rdraw)) rom)) ->
    G (mkst regs (0x155a0 : word)
         (CM (wbytes Jf (Z_to_bv 64 (bv_unsigned sp0 - 368)) (zeros 304)) (fun _ => None)) rom).
  Proof.
    intros G HG regs Jf rom HJ H2 H8 H9 H10 Hk.
    (* port727: the vector's length depends on the kernel's CONFIG_RSEQ. *)
    destruct (kb_rseq (in_kernel inp)) eqn:RS.
    { unfold J_aux in Hk; rewrite RS in Hk; cbn iota in Hk.
    pose proof len_av as Hlen. pose proof len_ev as Hlev. pose proof pn_bounds as [Hp1 Hp2].
    unfold envp_w in H9.
    eapply HG.
    { sn F_154f4 D_154f4.
    ld_step F_154f8 D_154f8 (word_to_le_bytes 8 (Z_to_bv 64 0x2fcb0)) (Z_to_bv 64 0x2fcb0)
      ltac:(rd_img img_1e940_8) ltac:(apply bytes_le_to_Z_8).
    stw F_154fc D_154fc (Z_to_bv 64 0x2fcb0) (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ltac:(ok_data).
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    eapply (envp_loop G HG (length ev) 0); [lia | gres; pin; f_equal; lia |].
    intros regs1 H9a H10a Hag1.
    carry Hag1 H2 (2 : reg) H2a. carry Hag1 H8 (8 : reg) H8a.
    clear H9 H10 H8 H2.
    eapply HG.
    { sn F_1550c D_1550c.
    sn F_15510 D_15510.
    stw F_15514 D_15514 (Z_to_bv 64 0x50018)
      (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))) ltac:(ok_data).
    (* port727: 's auxv, CONFIG_RSEQ (29 pairs with AT_NULL); generated by gen_s0startup2_a2.py *)
    ld_step F_15518 D_15518 (word_to_le_bytes 8 (Z_to_bv 64 33)) (Z_to_bv 64 33) ltac:(rdA 0%nat (Z_to_bv 64 33)) ltac:(apply bytes_le_to_Z_8).
    stepb_ft F_1551c D_1551c ltac:(pin; cond_compute).
    sv F_15520 D_15520 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 16)).
    sn F_15524 D_15524.
    sv F_15528 D_15528 (Z_to_bv 64 (bv_unsigned sp0 - 368)).
    sn F_1552c D_1552c.
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 33 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (la_sysinfo_ehdr (launch_auxv inp sp0 mbase))) (la_sysinfo_ehdr (launch_auxv inp sp0 mbase)) ltac:(rdA 1%nat (la_sysinfo_ehdr (launch_auxv inp sp0 mbase))) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 104)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 104)) (la_sysinfo_ehdr (launch_auxv inp sp0 mbase)) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 40)) (Z_to_bv 64 40) ltac:(rdA 2%nat (Z_to_bv 64 40)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 32)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_tk F_1553c D_1553c ltac:(pin; cond_compute).   (* key 40 >= AUX_CNT: skipped *)
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 41)) (Z_to_bv 64 41) ltac:(rdA 4%nat (Z_to_bv 64 41)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 48)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_tk F_1553c D_1553c ltac:(pin; cond_compute).   (* key 41 >= AUX_CNT: skipped *)
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 42)) (Z_to_bv 64 42) ltac:(rdA 6%nat (Z_to_bv 64 42)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 64)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_tk F_1553c D_1553c ltac:(pin; cond_compute).   (* key 42 >= AUX_CNT: skipped *)
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 43)) (Z_to_bv 64 43) ltac:(rdA 8%nat (Z_to_bv 64 43)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 80)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_tk F_1553c D_1553c ltac:(pin; cond_compute).   (* key 43 >= AUX_CNT: skipped *)
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 44)) (Z_to_bv 64 44) ltac:(rdA 10%nat (Z_to_bv 64 44)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 96)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_tk F_1553c D_1553c ltac:(pin; cond_compute).   (* key 44 >= AUX_CNT: skipped *)
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 45)) (Z_to_bv 64 45) ltac:(rdA 12%nat (Z_to_bv 64 45)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 112)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_tk F_1553c D_1553c ltac:(pin; cond_compute).   (* key 45 >= AUX_CNT: skipped *)
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 46)) (Z_to_bv 64 46) ltac:(rdA 14%nat (Z_to_bv 64 46)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 128)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_tk F_1553c D_1553c ltac:(pin; cond_compute).   (* key 46 >= AUX_CNT: skipped *)
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 47)) (Z_to_bv 64 47) ltac:(rdA 16%nat (Z_to_bv 64 47)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 144)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_tk F_1553c D_1553c ltac:(pin; cond_compute).   (* key 47 >= AUX_CNT: skipped *)
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 51)) (Z_to_bv 64 51) ltac:(rdA 18%nat (Z_to_bv 64 51)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 160)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_tk F_1553c D_1553c ltac:(pin; cond_compute).   (* key 51 >= AUX_CNT: skipped *)
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 16)) (Z_to_bv 64 16) ltac:(rdA 20%nat (Z_to_bv 64 16)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 176)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 16 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (in_hwcap inp)) (in_hwcap inp) ltac:(rdA 21%nat (in_hwcap inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 240)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 240)) (in_hwcap inp) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rdA 22%nat (Z_to_bv 64 6)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 192)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 6 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096) ltac:(rdA 23%nat (Z_to_bv 64 4096)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 320)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 320)) (Z_to_bv 64 4096) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 17)) (Z_to_bv 64 17) ltac:(rdA 24%nat (Z_to_bv 64 17)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 208)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 17 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (Z_to_bv 64 100)) (Z_to_bv 64 100) ltac:(rdA 25%nat (Z_to_bv 64 100)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 232)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 232)) (Z_to_bv 64 100) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 3)) (Z_to_bv 64 3) ltac:(rdA 26%nat (Z_to_bv 64 3)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 224)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 3 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 0x10040) ltac:(rdA 27%nat (Z_to_bv 64 0x10040)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 344)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 344)) (Z_to_bv 64 0x10040) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rdA 28%nat (Z_to_bv 64 4)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 240)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 4 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rdA 29%nat (Z_to_bv 64 56)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 336)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 336)) (Z_to_bv 64 56) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 5)) (Z_to_bv 64 5) ltac:(rdA 30%nat (Z_to_bv 64 5)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 256)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 5 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rdA 31%nat (Z_to_bv 64 10)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 328)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 328)) (Z_to_bv 64 10) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 7)) (Z_to_bv 64 7) ltac:(rdA 32%nat (Z_to_bv 64 7)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 272)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 7 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 33%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 312)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 312)) (Z_to_bv 64 0) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 8)) (Z_to_bv 64 8) ltac:(rdA 34%nat (Z_to_bv 64 8)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 288)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 8 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 35%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 304)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 304)) (Z_to_bv 64 0) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 9)) (Z_to_bv 64 9) ltac:(rdA 36%nat (Z_to_bv 64 9)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 304)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 9 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_N Tgt_checksum_fuzzer_ubsan.M.init_pc))) (Z_to_bv 64 (Z.of_N Tgt_checksum_fuzzer_ubsan.M.init_pc)) ltac:(rdA 37%nat (Z_to_bv 64 (Z.of_N Tgt_checksum_fuzzer_ubsan.M.init_pc))) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 296)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 296)) (Z_to_bv 64 (Z.of_N Tgt_checksum_fuzzer_ubsan.M.init_pc)) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 11)) (Z_to_bv 64 11) ltac:(rdA 38%nat (Z_to_bv 64 11)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 320)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 11 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rdA 39%nat (in_uid inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 280)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 280)) (in_uid inp) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 12)) (Z_to_bv 64 12) ltac:(rdA 40%nat (Z_to_bv 64 12)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 336)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 12 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rdA 41%nat (in_uid inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 272)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 272)) (in_uid inp) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 13)) (Z_to_bv 64 13) ltac:(rdA 42%nat (Z_to_bv 64 13)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 352)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 13 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rdA 43%nat (in_gid inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 264)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 264)) (in_gid inp) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 14)) (Z_to_bv 64 14) ltac:(rdA 44%nat (Z_to_bv 64 14)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 368)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 14 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rdA 45%nat (in_gid inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 256)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 256)) (in_gid inp) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 23)) (Z_to_bv 64 23) ltac:(rdA 46%nat (Z_to_bv 64 23)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 384)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 23 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 47%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 184)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 184)) (Z_to_bv 64 0) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 25)) (Z_to_bv 64 25) ltac:(rdA 48%nat (Z_to_bv 64 25)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 400)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 25 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))) (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)) ltac:(rdA 49%nat (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 168)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 168)) (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 31)) (Z_to_bv 64 31) ltac:(rdA 50%nat (Z_to_bv 64 31)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 416)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 31 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (at_execfn_ptr (ed_top rdraw) (in_execfn inp))) (at_execfn_ptr (ed_top rdraw) (in_execfn inp)) ltac:(rdA 51%nat (at_execfn_ptr (ed_top rdraw) (in_execfn inp))) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 120)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 120)) (at_execfn_ptr (ed_top rdraw) (in_execfn inp)) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 27)) (Z_to_bv 64 27) ltac:(rdA 52%nat (Z_to_bv 64 27)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 432)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 27 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (Z_to_bv 64 28)) (Z_to_bv 64 28) ltac:(rdA 53%nat (Z_to_bv 64 28)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 152)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 152)) (Z_to_bv 64 28) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 28)) (Z_to_bv 64 28) ltac:(rdA 54%nat (Z_to_bv 64 28)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 448)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 28 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (Z_to_bv 64 32)) (Z_to_bv 64 32) ltac:(rdA 55%nat (Z_to_bv 64 32)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 144)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 144)) (Z_to_bv 64 32) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 56%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 464)).
    stepb_tk F_15538 D_15538 ltac:(pin; cond_compute).
    ld_step F_15554 D_15554 (word_to_le_bytes 8 (in_hwcap inp)) (in_hwcap inp)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    ld_step F_15558 D_15558 (zeros 8) (Z_to_bv 64 0)
      ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)
      ltac:(reflexivity).
    sn F_1555c D_1555c.
    stw F_15560 D_15560 (Z_to_bv 64 0x50078) (in_hwcap inp) ltac:(ok_data).
    stepb_tk F_15564 D_15564 ltac:(pin; cond_compute).
    ld_step F_1557c D_1557c (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    stw F_15580 D_15580 (Z_to_bv 64 0x50040) (Z_to_bv 64 4096) ltac:(ok_data).
    stepb_tk F_15584 D_15584 ltac:(pin; apply c_eq_0_false; lia).
    stepb_tk F_1558c D_1558c ltac:(pin; apply c_eq_0_false; lia).
    sn F_15598 D_15598.
    ld_step F_1559c D_1559c (word_to_le_bytes 8 (Z_to_bv 64 0x50008)) (Z_to_bv 64 0x50008)
      ltac:(rd_img img_1e948_8) ltac:(apply bytes_le_to_Z_8).
    sn F_155a0 D_155a0.
    ld_step F_155a4 D_155a4 (word_to_le_bytes 8 (Z_to_bv 64 0x50000)) (Z_to_bv 64 0x50000)
      ltac:(rd_img img_1e950_8) ltac:(apply bytes_le_to_Z_8).
    stw F_155a8 D_155a8 (Z_to_bv 64 0x50008) (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) ltac:(ok_data).
    sv F_155ac D_155ac (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) + Z.of_nat 0 + 1)).
    stw F_155b0 D_155b0 (Z_to_bv 64 0x50000) (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) + Z.of_nat 0)) ltac:(ok_data).
    sn F_155b4 D_155b4.
    sn F_155b8 D_155b8.
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    eapply (prog_loop G HG s 0 0); [reflexivity | lia | lia | gres; reflexivity | gres; reflexivity | gres; reflexivity |].
    intros regs2 H11b Hag2.
    carry Hag2 H2a (2 : reg) H2b.
    eapply HG.
    { sv F_155d0 D_155d0 (Z_to_bv 64 (bv_unsigned sp0 - 368)).
      sn F_155d4 D_155d4.
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk.
    - gres; bveq.
    - gres; exact H2b.
    - gres; reflexivity.
    - gres. pose proof (Hag2 (18:reg) ltac:(notin_list)) as T; rewrite T; gres; reflexivity.
    - ra_chain.
    }
    { unfold J_aux in Hk; rewrite RS in Hk; cbn iota in Hk.
    pose proof len_av as Hlen. pose proof len_ev as Hlev. pose proof pn_bounds as [Hp1 Hp2].
    unfold envp_w in H9.
    eapply HG.
    { sn F_154f4 D_154f4.
    ld_step F_154f8 D_154f8 (word_to_le_bytes 8 (Z_to_bv 64 0x2fcb0)) (Z_to_bv 64 0x2fcb0)
      ltac:(rd_img img_1e940_8) ltac:(apply bytes_le_to_Z_8).
    stw F_154fc D_154fc (Z_to_bv 64 0x2fcb0) (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ltac:(ok_data).
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    eapply (envp_loop G HG (length ev) 0); [lia | gres; pin; f_equal; lia |].
    intros regs1 H9a H10a Hag1.
    carry Hag1 H2 (2 : reg) H2a. carry Hag1 H8 (8 : reg) H8a.
    clear H9 H10 H8 H2.
    eapply HG.
    { sn F_1550c D_1550c.
    sn F_15510 D_15510.
    stw F_15514 D_15514 (Z_to_bv 64 0x50018)
      (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))) ltac:(ok_data).
    (* port727: 's auxv, no CONFIG_RSEQ (27 pairs with AT_NULL); generated by gen_s0startup2_a2.py *)
    ld_step F_15518 D_15518 (word_to_le_bytes 8 (Z_to_bv 64 33)) (Z_to_bv 64 33) ltac:(rdA 0%nat (Z_to_bv 64 33)) ltac:(apply bytes_le_to_Z_8).
    stepb_ft F_1551c D_1551c ltac:(pin; cond_compute).
    sv F_15520 D_15520 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 16)).
    sn F_15524 D_15524.
    sv F_15528 D_15528 (Z_to_bv 64 (bv_unsigned sp0 - 368)).
    sn F_1552c D_1552c.
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 33 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (la_sysinfo_ehdr (launch_auxv inp sp0 mbase))) (la_sysinfo_ehdr (launch_auxv inp sp0 mbase)) ltac:(rdA 1%nat (la_sysinfo_ehdr (launch_auxv inp sp0 mbase))) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 104)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 104)) (la_sysinfo_ehdr (launch_auxv inp sp0 mbase)) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 40)) (Z_to_bv 64 40) ltac:(rdA 2%nat (Z_to_bv 64 40)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 32)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_tk F_1553c D_1553c ltac:(pin; cond_compute).   (* key 40 >= AUX_CNT: skipped *)
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 41)) (Z_to_bv 64 41) ltac:(rdA 4%nat (Z_to_bv 64 41)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 48)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_tk F_1553c D_1553c ltac:(pin; cond_compute).   (* key 41 >= AUX_CNT: skipped *)
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 42)) (Z_to_bv 64 42) ltac:(rdA 6%nat (Z_to_bv 64 42)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 64)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_tk F_1553c D_1553c ltac:(pin; cond_compute).   (* key 42 >= AUX_CNT: skipped *)
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 43)) (Z_to_bv 64 43) ltac:(rdA 8%nat (Z_to_bv 64 43)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 80)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_tk F_1553c D_1553c ltac:(pin; cond_compute).   (* key 43 >= AUX_CNT: skipped *)
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 44)) (Z_to_bv 64 44) ltac:(rdA 10%nat (Z_to_bv 64 44)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 96)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_tk F_1553c D_1553c ltac:(pin; cond_compute).   (* key 44 >= AUX_CNT: skipped *)
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 45)) (Z_to_bv 64 45) ltac:(rdA 12%nat (Z_to_bv 64 45)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 112)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_tk F_1553c D_1553c ltac:(pin; cond_compute).   (* key 45 >= AUX_CNT: skipped *)
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 46)) (Z_to_bv 64 46) ltac:(rdA 14%nat (Z_to_bv 64 46)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 128)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_tk F_1553c D_1553c ltac:(pin; cond_compute).   (* key 46 >= AUX_CNT: skipped *)
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 47)) (Z_to_bv 64 47) ltac:(rdA 16%nat (Z_to_bv 64 47)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 144)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_tk F_1553c D_1553c ltac:(pin; cond_compute).   (* key 47 >= AUX_CNT: skipped *)
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 51)) (Z_to_bv 64 51) ltac:(rdA 18%nat (Z_to_bv 64 51)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 160)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_tk F_1553c D_1553c ltac:(pin; cond_compute).   (* key 51 >= AUX_CNT: skipped *)
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 16)) (Z_to_bv 64 16) ltac:(rdA 20%nat (Z_to_bv 64 16)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 176)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 16 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (in_hwcap inp)) (in_hwcap inp) ltac:(rdA 21%nat (in_hwcap inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 240)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 240)) (in_hwcap inp) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rdA 22%nat (Z_to_bv 64 6)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 192)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 6 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096) ltac:(rdA 23%nat (Z_to_bv 64 4096)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 320)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 320)) (Z_to_bv 64 4096) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 17)) (Z_to_bv 64 17) ltac:(rdA 24%nat (Z_to_bv 64 17)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 208)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 17 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (Z_to_bv 64 100)) (Z_to_bv 64 100) ltac:(rdA 25%nat (Z_to_bv 64 100)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 232)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 232)) (Z_to_bv 64 100) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 3)) (Z_to_bv 64 3) ltac:(rdA 26%nat (Z_to_bv 64 3)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 224)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 3 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 0x10040) ltac:(rdA 27%nat (Z_to_bv 64 0x10040)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 344)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 344)) (Z_to_bv 64 0x10040) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rdA 28%nat (Z_to_bv 64 4)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 240)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 4 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rdA 29%nat (Z_to_bv 64 56)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 336)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 336)) (Z_to_bv 64 56) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 5)) (Z_to_bv 64 5) ltac:(rdA 30%nat (Z_to_bv 64 5)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 256)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 5 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rdA 31%nat (Z_to_bv 64 10)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 328)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 328)) (Z_to_bv 64 10) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 7)) (Z_to_bv 64 7) ltac:(rdA 32%nat (Z_to_bv 64 7)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 272)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 7 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 33%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 312)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 312)) (Z_to_bv 64 0) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 8)) (Z_to_bv 64 8) ltac:(rdA 34%nat (Z_to_bv 64 8)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 288)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 8 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 35%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 304)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 304)) (Z_to_bv 64 0) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 9)) (Z_to_bv 64 9) ltac:(rdA 36%nat (Z_to_bv 64 9)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 304)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 9 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_N Tgt_checksum_fuzzer_ubsan.M.init_pc))) (Z_to_bv 64 (Z.of_N Tgt_checksum_fuzzer_ubsan.M.init_pc)) ltac:(rdA 37%nat (Z_to_bv 64 (Z.of_N Tgt_checksum_fuzzer_ubsan.M.init_pc))) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 296)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 296)) (Z_to_bv 64 (Z.of_N Tgt_checksum_fuzzer_ubsan.M.init_pc)) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 11)) (Z_to_bv 64 11) ltac:(rdA 38%nat (Z_to_bv 64 11)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 320)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 11 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rdA 39%nat (in_uid inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 280)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 280)) (in_uid inp) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 12)) (Z_to_bv 64 12) ltac:(rdA 40%nat (Z_to_bv 64 12)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 336)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 12 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rdA 41%nat (in_uid inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 272)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 272)) (in_uid inp) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 13)) (Z_to_bv 64 13) ltac:(rdA 42%nat (Z_to_bv 64 13)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 352)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 13 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rdA 43%nat (in_gid inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 264)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 264)) (in_gid inp) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 14)) (Z_to_bv 64 14) ltac:(rdA 44%nat (Z_to_bv 64 14)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 368)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 14 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rdA 45%nat (in_gid inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 256)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 256)) (in_gid inp) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 23)) (Z_to_bv 64 23) ltac:(rdA 46%nat (Z_to_bv 64 23)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 384)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 23 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 47%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 184)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 184)) (Z_to_bv 64 0) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 25)) (Z_to_bv 64 25) ltac:(rdA 48%nat (Z_to_bv 64 25)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 400)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 25 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))) (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)) ltac:(rdA 49%nat (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 168)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 168)) (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 31)) (Z_to_bv 64 31) ltac:(rdA 50%nat (Z_to_bv 64 31)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 416)).
    stepb_ft F_15538 D_15538 ltac:(pin; cond_compute).
    stepb_ft F_1553c D_1553c ltac:(pin; cond_compute).   (* key 31 < AUX_CNT *)
    ld_step F_15540 D_15540 (word_to_le_bytes 8 (at_execfn_ptr (ed_top rdraw) (in_execfn inp))) (at_execfn_ptr (ed_top rdraw) (in_execfn inp)) ltac:(rdA 51%nat (at_execfn_ptr (ed_top rdraw) (in_execfn inp))) ltac:(apply bytes_le_to_Z_8).
    sn F_15544 D_15544.
    sv F_15548 D_15548 (Z_to_bv 64 (bv_unsigned sp0 - 120)).
    stw F_1554c D_1554c (Z_to_bv 64 (bv_unsigned sp0 - 120)) (at_execfn_ptr (ed_top rdraw) (in_execfn inp)) ltac:(ok_win HJ).
    sn F_15550 D_15550.
    ld_step F_15530 D_15530 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 52%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sv F_15534 D_15534 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 432)).
    stepb_tk F_15538 D_15538 ltac:(pin; cond_compute).
    ld_step F_15554 D_15554 (word_to_le_bytes 8 (in_hwcap inp)) (in_hwcap inp)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    ld_step F_15558 D_15558 (zeros 8) (Z_to_bv 64 0)
      ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)
      ltac:(reflexivity).
    sn F_1555c D_1555c.
    stw F_15560 D_15560 (Z_to_bv 64 0x50078) (in_hwcap inp) ltac:(ok_data).
    stepb_tk F_15564 D_15564 ltac:(pin; cond_compute).
    ld_step F_1557c D_1557c (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    stw F_15580 D_15580 (Z_to_bv 64 0x50040) (Z_to_bv 64 4096) ltac:(ok_data).
    stepb_tk F_15584 D_15584 ltac:(pin; apply c_eq_0_false; lia).
    stepb_tk F_1558c D_1558c ltac:(pin; apply c_eq_0_false; lia).
    sn F_15598 D_15598.
    ld_step F_1559c D_1559c (word_to_le_bytes 8 (Z_to_bv 64 0x50008)) (Z_to_bv 64 0x50008)
      ltac:(rd_img img_1e948_8) ltac:(apply bytes_le_to_Z_8).
    sn F_155a0 D_155a0.
    ld_step F_155a4 D_155a4 (word_to_le_bytes 8 (Z_to_bv 64 0x50000)) (Z_to_bv 64 0x50000)
      ltac:(rd_img img_1e950_8) ltac:(apply bytes_le_to_Z_8).
    stw F_155a8 D_155a8 (Z_to_bv 64 0x50008) (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) ltac:(ok_data).
    sv F_155ac D_155ac (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) + Z.of_nat 0 + 1)).
    stw F_155b0 D_155b0 (Z_to_bv 64 0x50000) (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) + Z.of_nat 0)) ltac:(ok_data).
    sn F_155b4 D_155b4.
    sn F_155b8 D_155b8.
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    eapply (prog_loop G HG s 0 0); [reflexivity | lia | lia | gres; reflexivity | gres; reflexivity | gres; reflexivity |].
    intros regs2 H11b Hag2.
    carry Hag2 H2a (2 : reg) H2b.
    eapply HG.
    { sv F_155d0 D_155d0 (Z_to_bv 64 (bv_unsigned sp0 - 368)).
      sn F_155d4 D_155d4.
      OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_mst_refl. }
    apply Hk.
    - gres; bveq.
    - gres; exact H2b.
    - gres; reflexivity.
    - gres. pose proof (Hag2 (18:reg) ltac:(notin_list)) as T; rewrite T; gres; reflexivity.
    - ra_chain.
    }
  Qed.

End P3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.StepTac.chain_step ::= OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.L10Walk.l10_chain_step_kit.
