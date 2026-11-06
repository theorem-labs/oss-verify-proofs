(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ArgvEnv RefLayout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Cls Require Import ClsTac.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1BootCode S1BootDefs.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section Img.
  Variable SEGS : list Segment.
  Hypothesis HX : s1b_ok SEGS = true.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section P3.
  Variable sp0 : word.
  Variable rdraw : EntryDraw.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation mem0 := (wrap_mem RPH sp0 av ev uid hw rdraw) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).
  Local Notation stk := (stack_to_mem sp0 (entry_stack_image RPH sp0 av ev uid hw rdraw)) (only parsing).

  Local Notation E := (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))%Z (only parsing).
  Local Notation A := (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))%Z (only parsing).

  Local Notation pn := (cat_argv_ptr sp0 av ev 0) (only parsing).
  Local Notation rnd := (at_random_ptr sp0 av ev) (only parsing).
  Local Notation s := (nth 0 av []) (only parsing).
  Local Notation A8 := (Z_to_bv 64 0x120938) (only parsing).

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.
  Lemma len_ev : (Z.of_nat (length ev) <= 256)%Z.
  Proof. destruct Hve as [H1 _]. lia. Qed.

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.

  Lemma rd_above : forall J D (a : Z) n bs,
    (bv_unsigned sp0 <= a)%Z -> (a + Z.of_nat n < 2^64)%Z ->
    rdn SEGS stk (Z_to_bv 64 a) n = Some bs ->
    rdn SEGS (CM J D) (Z_to_bv 64 a) n = Some bs.
  Proof.
    intros J D a n bs Ha Hn H. pose proof (u64_range (Z_to_bv 64 a)).
    rewrite rdn_cmem_above by (unorm; lia).
    rewrite rdn_wrap_stack_above by (unorm; lia). exact H.
  Qed.

  Lemma rd_envp : forall J D k, (k < length ev)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (E + 8 * Z.of_nat k)) 8
    = Some (word_to_le_bytes 8 (cat_envp_ptr sp0 av ev k)).
  Proof.
    intros J D k Hk. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (E + 8 * Z.of_nat k)) with (sp0 + nat_to_word (envp_off av + 8 * k))
      by (rewrite word_add_nat; f_equal; unfold envp_off; lia).
    exact (read_envp_ptr_k SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_hi' k Hk).
  Qed.

  Lemma rd_envp_null : forall J D,
    rdn SEGS (CM J D) (Z_to_bv 64 (E + 8 * Z.of_nat (length ev))) 8
    = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Proof.
    intros J D. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (E + 8 * Z.of_nat (length ev)))
      with (sp0 + nat_to_word (envp_off av + 8 * length ev))
      by (rewrite word_add_nat; f_equal; unfold envp_off; lia).
    exact (read_envp_null SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_hi').
  Qed.

  Lemma rd_auxv : forall J D j w, (j < 20)%nat ->
    nth j (auxv_words RPH rnd uid hw) (Z_to_bv 64 0) = w ->
    rdn SEGS (CM J D) (Z_to_bv 64 (A + 8 * Z.of_nat j)) 8 = Some (word_to_le_bytes 8 w).
  Proof.
    intros J D j w Hj Hw. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (A + 8 * Z.of_nat j)) with (sp0 + nat_to_word (auxv_off av ev + 8 * j))
      by (rewrite word_add_nat; f_equal; unfold auxv_off; lia).
    rewrite <- Hw. exact (read_auxv_word SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_hi' j Hj).
  Qed.

  Lemma envp_loop : forall G, bwd SEGS G -> forall n k regs J D rom,
    (k + n = length ev)%nat ->
    getr regs 9 = Z_to_bv 64 (E + 8 * Z.of_nat k) ->
    (forall regs',
        getr regs' 9 = Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8) ->
        getr regs' 10 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [9; 10]%list) regs regs' ->
        G (mkst regs' (0xcf7d8 : word) (CM J D) rom)) ->
    G (mkst regs (0xcf7cc : word) (CM J D) rom).
  Proof.
    intros G HG.
    pose proof len_av as Hlen. pose proof len_ev as Hlev.
    induction n as [|n IH]; intros k regs J D rom Hkn H9 Hk0.
    -
      assert (k = length ev) by lia. subst k.
      eapply HG.
      { ld_step (F_cf78c _ HX) D_cf78c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
          ltac:(apply rd_envp_null) ltac:(apply bytes_le_to_Z_8).
        sv (F_cf790 _ HX) D_cf790 (Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8)).
        stepb_ft (F_cf794 _ HX) D_cf794 ltac:(pin; cond_compute).
        apply mst_refl. }
      apply Hk0; [gres; reflexivity | gres; reflexivity | solve_regs_agree].
    - assert (Hk : (k < length ev)%nat) by lia.
      pose proof (cat_envp_ptr_nz RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' k Hk) as Hnz.
      eapply HG.
      { ld_step (F_cf78c _ HX) D_cf78c (word_to_le_bytes 8 (cat_envp_ptr sp0 av ev k)) (cat_envp_ptr sp0 av ev k)
          ltac:(apply rd_envp; exact Hk) ltac:(apply bytes_le_to_Z_8).
        sv (F_cf790 _ HX) D_cf790 (Z_to_bv 64 (E + 8 * Z.of_nat (S k))).
        stepb_tk (F_cf794 _ HX) D_cf794 ltac:(pin; apply c_eq_0_false; exact Hnz).
        apply mst_refl. }
      eapply (IH (S k)); [lia | gres; reflexivity |].
      intros regs' H9' H10' Hag. apply Hk0; [exact H9' | exact H10' |].
      eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
  Qed.

  Lemma pn_bounds :
    (bv_unsigned sp0 <= bv_unsigned pn)%Z
    /\ (bv_unsigned pn + Z.of_nat (length s) + 1 < 2^64)%Z.
  Proof.
    pose proof len_av.
    exact (argv_ptr_bounds_at sp0 av ev Hva Hve Hsp_hi' 0 ltac:(lia)).
  Qed.

  Lemma rd_argv0_byte : forall J D j b, (j <= length s)%nat ->
    nth j (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = b ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j)) 1 = Some [b].
  Proof.
    intros J D j b Hj Hb. pose proof len_av. pose proof pn_bounds as [Hp1 Hp2].
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j)) with (pn + nat_to_word j)
      by (rewrite word_add_nat; reflexivity).
    rewrite <- Hb.
    exact (read_argv_byte_k RPH SEGS sp0 av ev 0 j uid hw rdraw ltac:(lia) Hj
             (bsb_nw RPH sp0 av ev uid hw rdraw Hva Hve Hsp_hi')).
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

  Lemma prog_loop : forall G, bwd SEGS G -> forall l2 j acc regs J D rom,
    skipn j s = l2 -> (j <= length s)%nat -> (acc <= j)%nat ->
    getr regs 10 = Z_to_bv 64 0x120938 ->
    getr regs 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1) ->
    getr regs 12 = Z_to_bv 64 47 ->
    (forall regs',
        getr regs' 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat (length s) + 1) ->
        regs_agree (fun r => In r [11; 13]%list) regs regs' ->
        G (mkst regs' (0xcf89c : word)
                       (CM J (wbytes D A8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn
                                 + Z.of_nat (after_last_slash l2 j acc)))))) rom)) ->
    G (mkst regs (0xcf890 : word)
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
      { lb_step (F_cf850 _ HX) D_cf850 (Z_to_bv 8 0)
          ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | subst j; rewrite app_nth2 by lia; rewrite Nat.sub_diag; reflexivity] | f_equal; lia]).
        stepb_ft (F_cf854 _ HX) D_cf854 ltac:(pin; cond_compute).
        stepb_ft (F_cf858 _ HX) D_cf858 ltac:(pin; cond_compute).
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
      +
        eapply HG.
        { lb_step (F_cf850 _ HX) D_cf850 b
            ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
          stepb_tk (F_cf854 _ HX) D_cf854 ltac:(pin; rewrite c_eq_byte47; exact Eb).
          stw (F_cf848 _ HX) D_cf848 (Z_to_bv 64 0x120938) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1)) ltac:(ok_dat HX).
          rewrite wbytes_shadow by (rewrite ?length_N_to_le_bytes; rewrite ?length_N_to_le_bytes; first [reflexivity | region_side]).
          sv (F_cf84c _ HX) D_cf84c (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)).
          apply mst_refl. }
        replace (bv_unsigned pn + Z.of_nat j + 1)%Z with (bv_unsigned pn + Z.of_nat (S j))%Z by lia.
        eapply (IH (S j) (S j)); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
        intros regs' H11' Hag. apply Hk0; [exact H11'|].
        eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
      + eapply HG.
        { lb_step (F_cf850 _ HX) D_cf850 b
            ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
          stepb_ft (F_cf854 _ HX) D_cf854 ltac:(pin; rewrite c_eq_byte47; exact Eb).
          stepb_tk (F_cf858 _ HX) D_cf858 ltac:(pin; apply c_eq_byte0; exact Hbnz).
          sv (F_cf84c _ HX) D_cf84c (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)).
          apply mst_refl. }
        eapply (IH (S j) acc); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
        intros regs' H11' Hag. apply Hk0; [exact H11'|].
        eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
  Qed.

  Ltac rdA j w := eapply rdn_addr; [apply (rd_auxv _ _ j w); [lia | reflexivity] | f_equal; lia].

  Lemma p3_run : forall G, bwd SEGS G -> forall regs Jf rom,
    wfJ sp0 Jf ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 8 = pn ->
    getr regs 9 = envp_w sp0 av ->
    getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
    (forall regs',
        getr regs' 1 = Z_to_bv 64 0xcf8a4 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
        getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
        getr regs' 18 = Z_to_bv 64 0x120948 ->
        regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 18]%list) regs regs' ->
        G (mkst regs' (0xcfab4 : word) (CM (J_aux sp0 av ev uid hw Jf) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0xcf7c0 : word)
         (CM (wbytes Jf (Z_to_bv 64 (bv_unsigned sp0 - 368)) (zeros 304)) (fun _ => None)) rom).
  Proof.
    intros G HG regs Jf rom HJ H2 H8 H9 H10 Hk.
    pose proof len_av as Hlen. pose proof len_ev as Hlev. pose proof pn_bounds as [Hp1 Hp2].
    unfold envp_w in H9.
    eapply HG.
    { sn (F_cf780 _ HX) D_cf780.
    ld_step (F_cf784 _ HX) D_cf784 (word_to_le_bytes 8 (Z_to_bv 64 0x1005e8)) (Z_to_bv 64 0x1005e8)
      ltac:(rd_img (img_ed060_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
    stw (F_cf788 _ HX) D_cf788 (Z_to_bv 64 0x1005e8) (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ltac:(ok_dat HX).
      apply mst_refl. }

    eapply (envp_loop G HG (length ev) 0); [lia | gres; pin; f_equal; lia |].
    intros regs1 H9a H10a Hag1.
    carry Hag1 H2 (2 : reg) H2a. carry Hag1 H8 (8 : reg) H8a.
    clear H9 H10 H8 H2.
    eapply HG.
    { sn (F_cf798 _ HX) D_cf798.
    sn (F_cf79c _ HX) D_cf79c.
    stw (F_cf7a0 _ HX) D_cf7a0 (Z_to_bv 64 0x120950)
      (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))) ltac:(ok_dat HX).

    ld_step (F_cf7a4 _ HX) D_cf7a4 (word_to_le_bytes 8 (Z_to_bv 64 3)) (Z_to_bv 64 3) ltac:(rdA 0%nat (Z_to_bv 64 3)) ltac:(apply bytes_le_to_Z_8).
    stepb_ft (F_cf7a8 _ HX) D_cf7a8 ltac:(pin; cond_compute).
    sv (F_cf7ac _ HX) D_cf7ac (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 16)).
    sn (F_cf7b0 _ HX) D_cf7b0.
    sv (F_cf7b4 _ HX) D_cf7b4 (Z_to_bv 64 (bv_unsigned sp0 - 368)).
    sn (F_cf7b8 _ HX) D_cf7b8.

    stepb_ft (F_cf7c8 _ HX) D_cf7c8 ltac:(pin; cond_compute).
    ld_step (F_cf7cc _ HX) D_cf7cc (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 0x10040) ltac:(rdA 1%nat (Z_to_bv 64 0x10040)) ltac:(apply bytes_le_to_Z_8).
    sn (F_cf7d0 _ HX) D_cf7d0.
    sv (F_cf7d4 _ HX) D_cf7d4 (Z_to_bv 64 (bv_unsigned sp0 - 344)).
    stw (F_cf7d8 _ HX) D_cf7d8 (Z_to_bv 64 (bv_unsigned sp0 - 344)) (Z_to_bv 64 0x10040) ltac:(ok_win HJ).
    sn (F_cf7dc _ HX) D_cf7dc.
    ld_step (F_cf7bc _ HX) D_cf7bc (word_to_le_bytes 8 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rdA 2%nat (Z_to_bv 64 4)) ltac:(apply bytes_le_to_Z_8).
    sv (F_cf7c0 _ HX) D_cf7c0 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 32)).
    stepb_ft (F_cf7c4 _ HX) D_cf7c4 ltac:(pin; cond_compute).

    stepb_ft (F_cf7c8 _ HX) D_cf7c8 ltac:(pin; cond_compute).
    ld_step (F_cf7cc _ HX) D_cf7cc (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rdA 3%nat (Z_to_bv 64 56)) ltac:(apply bytes_le_to_Z_8).
    sn (F_cf7d0 _ HX) D_cf7d0.
    sv (F_cf7d4 _ HX) D_cf7d4 (Z_to_bv 64 (bv_unsigned sp0 - 336)).
    stw (F_cf7d8 _ HX) D_cf7d8 (Z_to_bv 64 (bv_unsigned sp0 - 336)) (Z_to_bv 64 56) ltac:(ok_win HJ).
    sn (F_cf7dc _ HX) D_cf7dc.
    ld_step (F_cf7bc _ HX) D_cf7bc (word_to_le_bytes 8 (Z_to_bv 64 5)) (Z_to_bv 64 5) ltac:(rdA 4%nat (Z_to_bv 64 5)) ltac:(apply bytes_le_to_Z_8).
    sv (F_cf7c0 _ HX) D_cf7c0 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 48)).
    stepb_ft (F_cf7c4 _ HX) D_cf7c4 ltac:(pin; cond_compute).

    stepb_ft (F_cf7c8 _ HX) D_cf7c8 ltac:(pin; cond_compute).
    ld_step (F_cf7cc _ HX) D_cf7cc (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rdA 5%nat (Z_to_bv 64 10)) ltac:(apply bytes_le_to_Z_8).
    sn (F_cf7d0 _ HX) D_cf7d0.
    sv (F_cf7d4 _ HX) D_cf7d4 (Z_to_bv 64 (bv_unsigned sp0 - 328)).
    stw (F_cf7d8 _ HX) D_cf7d8 (Z_to_bv 64 (bv_unsigned sp0 - 328)) (Z_to_bv 64 10) ltac:(ok_win HJ).
    sn (F_cf7dc _ HX) D_cf7dc.
    ld_step (F_cf7bc _ HX) D_cf7bc (word_to_le_bytes 8 (Z_to_bv 64 16)) (Z_to_bv 64 16) ltac:(rdA 6%nat (Z_to_bv 64 16)) ltac:(apply bytes_le_to_Z_8).
    sv (F_cf7c0 _ HX) D_cf7c0 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 64)).
    stepb_ft (F_cf7c4 _ HX) D_cf7c4 ltac:(pin; cond_compute).

    stepb_ft (F_cf7c8 _ HX) D_cf7c8 ltac:(pin; cond_compute).
    ld_step (F_cf7cc _ HX) D_cf7cc (word_to_le_bytes 8 hw) hw ltac:(rdA 7%nat hw) ltac:(apply bytes_le_to_Z_8).
    sn (F_cf7d0 _ HX) D_cf7d0.
    sv (F_cf7d4 _ HX) D_cf7d4 (Z_to_bv 64 (bv_unsigned sp0 - 240)).
    stw (F_cf7d8 _ HX) D_cf7d8 (Z_to_bv 64 (bv_unsigned sp0 - 240)) hw ltac:(ok_win HJ).
    sn (F_cf7dc _ HX) D_cf7dc.
    ld_step (F_cf7bc _ HX) D_cf7bc (word_to_le_bytes 8 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rdA 8%nat (Z_to_bv 64 6)) ltac:(apply bytes_le_to_Z_8).
    sv (F_cf7c0 _ HX) D_cf7c0 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 80)).
    stepb_ft (F_cf7c4 _ HX) D_cf7c4 ltac:(pin; cond_compute).

    stepb_ft (F_cf7c8 _ HX) D_cf7c8 ltac:(pin; cond_compute).
    ld_step (F_cf7cc _ HX) D_cf7cc (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096) ltac:(rdA 9%nat (Z_to_bv 64 4096)) ltac:(apply bytes_le_to_Z_8).
    sn (F_cf7d0 _ HX) D_cf7d0.
    sv (F_cf7d4 _ HX) D_cf7d4 (Z_to_bv 64 (bv_unsigned sp0 - 320)).
    stw (F_cf7d8 _ HX) D_cf7d8 (Z_to_bv 64 (bv_unsigned sp0 - 320)) (Z_to_bv 64 4096) ltac:(ok_win HJ).
    sn (F_cf7dc _ HX) D_cf7dc.
    ld_step (F_cf7bc _ HX) D_cf7bc (word_to_le_bytes 8 (Z_to_bv 64 11)) (Z_to_bv 64 11) ltac:(rdA 10%nat (Z_to_bv 64 11)) ltac:(apply bytes_le_to_Z_8).
    sv (F_cf7c0 _ HX) D_cf7c0 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 96)).
    stepb_ft (F_cf7c4 _ HX) D_cf7c4 ltac:(pin; cond_compute).

    stepb_ft (F_cf7c8 _ HX) D_cf7c8 ltac:(pin; cond_compute).
    ld_step (F_cf7cc _ HX) D_cf7cc (word_to_le_bytes 8 uid) uid ltac:(rdA 11%nat uid) ltac:(apply bytes_le_to_Z_8).
    sn (F_cf7d0 _ HX) D_cf7d0.
    sv (F_cf7d4 _ HX) D_cf7d4 (Z_to_bv 64 (bv_unsigned sp0 - 280)).
    stw (F_cf7d8 _ HX) D_cf7d8 (Z_to_bv 64 (bv_unsigned sp0 - 280)) uid ltac:(ok_win HJ).
    sn (F_cf7dc _ HX) D_cf7dc.
    ld_step (F_cf7bc _ HX) D_cf7bc (word_to_le_bytes 8 (Z_to_bv 64 12)) (Z_to_bv 64 12) ltac:(rdA 12%nat (Z_to_bv 64 12)) ltac:(apply bytes_le_to_Z_8).
    sv (F_cf7c0 _ HX) D_cf7c0 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 112)).
    stepb_ft (F_cf7c4 _ HX) D_cf7c4 ltac:(pin; cond_compute).

    stepb_ft (F_cf7c8 _ HX) D_cf7c8 ltac:(pin; cond_compute).
    ld_step (F_cf7cc _ HX) D_cf7cc (word_to_le_bytes 8 uid) uid ltac:(rdA 13%nat uid) ltac:(apply bytes_le_to_Z_8).
    sn (F_cf7d0 _ HX) D_cf7d0.
    sv (F_cf7d4 _ HX) D_cf7d4 (Z_to_bv 64 (bv_unsigned sp0 - 272)).
    stw (F_cf7d8 _ HX) D_cf7d8 (Z_to_bv 64 (bv_unsigned sp0 - 272)) uid ltac:(ok_win HJ).
    sn (F_cf7dc _ HX) D_cf7dc.
    ld_step (F_cf7bc _ HX) D_cf7bc (word_to_le_bytes 8 (Z_to_bv 64 23)) (Z_to_bv 64 23) ltac:(rdA 14%nat (Z_to_bv 64 23)) ltac:(apply bytes_le_to_Z_8).
    sv (F_cf7c0 _ HX) D_cf7c0 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 128)).
    stepb_ft (F_cf7c4 _ HX) D_cf7c4 ltac:(pin; cond_compute).

    stepb_ft (F_cf7c8 _ HX) D_cf7c8 ltac:(pin; cond_compute).
    ld_step (F_cf7cc _ HX) D_cf7cc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 15%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sn (F_cf7d0 _ HX) D_cf7d0.
    sv (F_cf7d4 _ HX) D_cf7d4 (Z_to_bv 64 (bv_unsigned sp0 - 184)).
    stw (F_cf7d8 _ HX) D_cf7d8 (Z_to_bv 64 (bv_unsigned sp0 - 184)) (Z_to_bv 64 0) ltac:(ok_win HJ).
    sn (F_cf7dc _ HX) D_cf7dc.
    ld_step (F_cf7bc _ HX) D_cf7bc (word_to_le_bytes 8 (Z_to_bv 64 25)) (Z_to_bv 64 25) ltac:(rdA 16%nat (Z_to_bv 64 25)) ltac:(apply bytes_le_to_Z_8).
    sv (F_cf7c0 _ HX) D_cf7c0 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 144)).
    stepb_ft (F_cf7c4 _ HX) D_cf7c4 ltac:(pin; cond_compute).

    stepb_ft (F_cf7c8 _ HX) D_cf7c8 ltac:(pin; cond_compute).
    ld_step (F_cf7cc _ HX) D_cf7cc (word_to_le_bytes 8 (at_random_ptr sp0 av ev)) (at_random_ptr sp0 av ev) ltac:(rdA 17%nat (at_random_ptr sp0 av ev)) ltac:(apply bytes_le_to_Z_8).
    sn (F_cf7d0 _ HX) D_cf7d0.
    sv (F_cf7d4 _ HX) D_cf7d4 (Z_to_bv 64 (bv_unsigned sp0 - 168)).
    stw (F_cf7d8 _ HX) D_cf7d8 (Z_to_bv 64 (bv_unsigned sp0 - 168)) (at_random_ptr sp0 av ev) ltac:(ok_win HJ).
    sn (F_cf7dc _ HX) D_cf7dc.
    ld_step (F_cf7bc _ HX) D_cf7bc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 18%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sv (F_cf7c0 _ HX) D_cf7c0 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 160)).
    stepb_tk (F_cf7c4 _ HX) D_cf7c4 ltac:(pin; cond_compute).

    ld_step (F_cf7e0 _ HX) D_cf7e0 (word_to_le_bytes 8 hw) hw
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    ld_step (F_cf7e4 _ HX) D_cf7e4 (zeros 8) (Z_to_bv 64 0)
      ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)
      ltac:(reflexivity).
    sn (F_cf7e8 _ HX) D_cf7e8.
    stw (F_cf7ec _ HX) D_cf7ec (Z_to_bv 64 0x1209b0) hw ltac:(ok_dat HX).
    stepb_tk (F_cf7f0 _ HX) D_cf7f0 ltac:(pin; cond_compute).

    ld_step (F_cf808 _ HX) D_cf808 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    stw (F_cf80c _ HX) D_cf80c (Z_to_bv 64 0x120978) (Z_to_bv 64 4096) ltac:(ok_dat HX).
    stepb_tk (F_cf810 _ HX) D_cf810 ltac:(pin; apply c_eq_0_false; lia).
    stepb_tk (F_cf818 _ HX) D_cf818 ltac:(pin; apply c_eq_0_false; lia).

    sn (F_cf824 _ HX) D_cf824.
    ld_step (F_cf828 _ HX) D_cf828 (word_to_le_bytes 8 (Z_to_bv 64 0x120940)) (Z_to_bv 64 0x120940)
      ltac:(rd_img (img_ed068_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
    sn (F_cf82c _ HX) D_cf82c.
    ld_step (F_cf830 _ HX) D_cf830 (word_to_le_bytes 8 (Z_to_bv 64 0x120938)) (Z_to_bv 64 0x120938)
      ltac:(rd_img (img_ed070_8 _ HX)) ltac:(apply bytes_le_to_Z_8).
    stw (F_cf834 _ HX) D_cf834 (Z_to_bv 64 0x120940) (cat_argv_ptr sp0 av ev 0) ltac:(ok_dat HX).
    sv (F_cf838 _ HX) D_cf838 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0 + 1)).
    stw (F_cf83c _ HX) D_cf83c (Z_to_bv 64 0x120938) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0)) ltac:(ok_dat HX).
    sn (F_cf840 _ HX) D_cf840.
    sn (F_cf844 _ HX) D_cf844.
      apply mst_refl. }

    eapply (prog_loop G HG s 0 0); [reflexivity | lia | lia | gres; reflexivity | gres; reflexivity | gres; reflexivity |].
    intros regs2 H11b Hag2.
    carry Hag2 H2a (2 : reg) H2b.
    eapply HG.
    { sv (F_cf85c _ HX) D_cf85c (Z_to_bv 64 (bv_unsigned sp0 - 368)).
      sn (F_cf860 _ HX) D_cf860.
      apply mst_refl. }
    apply Hk.
    - gres; bveq.
    - gres; exact H2b.
    - gres; reflexivity.
    - gres. pose proof (Hag2 (18:reg) ltac:(notin_list)) as T; rewrite T; gres; reflexivity.
    - ra_chain.
  Qed.

End P3.

End Img.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
