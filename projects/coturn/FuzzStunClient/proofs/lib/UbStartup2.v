(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import StartupTac ArgvEnv RefLayout CatExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbImg UbStartupDefs Ub_code_1b104_1c2fc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.peel ::= peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma rdn_addr : forall (segs : list Segment) m (a a' : word) n (r : option (list byte)),
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

Section P3.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variables uid hw : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Abbreviation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).
  Local Abbreviation stk := (stack_to_mem sp0 (entry_stack_image RPH sp0 av ev uid hw rdraw)) (only parsing).
  (* [comment removed for export] *)
  Local Abbreviation E := (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))%Z (only parsing).
  Local Abbreviation A := (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))%Z (only parsing).
  Local Abbreviation pn := (cat_argv_ptr sp0 av ev 0) (only parsing).
  Local Abbreviation rnd := (at_random_ptr sp0 av ev) (only parsing).
  Local Abbreviation s := (nth 0 av []) (only parsing).
  Local Abbreviation A8 := (Z_to_bv 64 0x56ed8) (only parsing).

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.
  Lemma len_ev : (Z.of_nat (length ev) <= 256)%Z.
  Proof. destruct Hve as [H1 _]. lia. Qed.

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (sp_window_hi >= bv_unsigned sp0)%Z. Proof. unfold sp_window_hi. lia. Qed.
  Lemma Hsp_hi'' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.

  Lemma bsb_len : (Z.of_nat (length (build_stack_bytes RPH sp0 av ev uid hw rdraw)) <= 2240000)%Z.
  Proof. exact (bsb_bound RPH sp0 av ev uid hw rdraw Hva Hve). Qed.

  (* [comment removed for export] *)
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
    exact (read_envp_ptr_k SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hhi k Hk).
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
    exact (read_envp_null SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hhi).
  Qed.

  Lemma rd_auxv : forall J D j w, (j < 20)%nat ->
    nth j (auxv_words RPH rnd uid hw) (Z_to_bv 64 0) = w ->
    rdn SEGS (CM J D) (Z_to_bv 64 (A + 8 * Z.of_nat j)) 8 = Some (word_to_le_bytes 8 w).
  Proof.
    intros J D j w Hj Hw. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (A + 8 * Z.of_nat j)) with (sp0 + nat_to_word (auxv_off av ev + 8 * j))
      by (rewrite word_add_nat; f_equal; unfold auxv_off; lia).
    rewrite <- Hw. exact (read_auxv_word SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hhi j Hj).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma envp_loop : forall G, bwd SEGS G -> forall n k regs J D rom,
    (k + n = length ev)%nat ->
    getr regs 9 = Z_to_bv 64 (E + 8 * Z.of_nat k) ->
    (forall regs',
        getr regs' 9 = Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8) ->
        getr regs' 10 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [9; 10]%list) regs regs' ->
        G (mkst regs' (0x1b764 : word) (CM J D) rom)) ->
    G (mkst regs (0x1b758 : word) (CM J D) rom).
  Proof.
    intros G HG.
    pose proof len_av as Hlen. pose proof len_ev as Hlev.
    induction n as [|n IH]; intros k regs J D rom Hkn H9 Hk0.
    - (* [comment removed for export] *)
      assert (k = length ev) by lia. subst k.
      eapply HG.
      { ld_step F_1b758 D_1b758 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
          ltac:(apply rd_envp_null) ltac:(apply bytes_le_to_Z_8).
        sv F_1b75c D_1b75c (Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8)).
        stepb_ft F_1b760 D_1b760 ltac:(pin; cond_compute).
        apply mst_refl. }
      apply Hk0; [gres; reflexivity | gres; reflexivity | solve_regs_agree].
    - assert (Hk : (k < length ev)%nat) by lia.
      pose proof (cat_envp_ptr_nz RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi'' k Hk) as Hnz.
      eapply HG.
      { ld_step F_1b758 D_1b758 (word_to_le_bytes 8 (cat_envp_ptr sp0 av ev k)) (cat_envp_ptr sp0 av ev k)
          ltac:(apply rd_envp; exact Hk) ltac:(apply bytes_le_to_Z_8).
        sv F_1b75c D_1b75c (Z_to_bv 64 (E + 8 * Z.of_nat (S k))).
        stepb_tk F_1b760 D_1b760 ltac:(pin; apply c_eq_0_false; exact Hnz).
        apply mst_refl. }
      eapply (IH (S k)); [lia | gres; reflexivity |].
      intros regs' H9' H10' Hag. apply Hk0; [exact H9' | exact H10' |].
      eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pn_bounds :
    (bv_unsigned sp0 <= bv_unsigned pn)%Z
    /\ (bv_unsigned pn + Z.of_nat (length s) + 1 < 2^64)%Z.
  Proof.
    pose proof len_av.
    exact (argv_ptr_bounds_at sp0 av ev Hva Hve Hhi 0 ltac:(lia)).
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
             (bsb_nw RPH sp0 av ev uid hw rdraw Hva Hve Hhi)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma prog_loop : forall G, bwd SEGS G -> forall l2 j acc regs J D rom,
    skipn j s = l2 -> (j <= length s)%nat -> (acc <= j)%nat ->
    getr regs 10 = A8 ->
    getr regs 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1) ->
    getr regs 12 = Z_to_bv 64 47 ->
    (forall regs',
        getr regs' 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat (length s) + 1) ->
        regs_agree (fun r => In r [11; 13]%list) regs regs' ->
        G (mkst regs' (0x1b828 : word)
                       (CM J (wbytes D A8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn
                                 + Z.of_nat (after_last_slash l2 j acc)))))) rom)) ->
    G (mkst regs (0x1b81c : word)
                   (CM J (wbytes D A8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat acc))))) rom).
  Proof.
    intros G HG.
    pose proof len_av as Hlen. pose proof pn_bounds as [Hp1 Hp2].
    pose proof (valid_argv_str_nz av 0 Hva ltac:(lia)) as Hnz.
    induction l2 as [|b l2 IH]; intros j acc regs J D rom Hskip Hj Hacc H10 H11 H12 Hk0.
    - (* [comment removed for export] *)
      assert (Hjl : j = length s).
      { pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
      eapply HG.
      { lb_step F_1b81c D_1b81c (Z_to_bv 8 0)
          ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | subst j; rewrite app_nth2 by lia; rewrite Nat.sub_diag; reflexivity] | f_equal; lia]).
        stepb_ft F_1b820 D_1b820 ltac:(pin; cond_compute).
        stepb_ft F_1b824 D_1b824 ltac:(pin; cond_compute).
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
        { lb_step F_1b81c D_1b81c b
            ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
          stepb_tk F_1b820 D_1b820 ltac:(pin; rewrite c_eq_byte47; exact Eb).
          stw F_1b814 D_1b814 (Z_to_bv 64 0x56ed8) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1))
            ltac:(ok_data).
          rewrite wbytes_shadow by (rewrite ?length_N_to_le_bytes; rewrite ?length_N_to_le_bytes; first [reflexivity | region_side]).
          sv F_1b818 D_1b818 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)).
          apply mst_refl. }
        replace (bv_unsigned pn + Z.of_nat j + 1)%Z with (bv_unsigned pn + Z.of_nat (S j))%Z by lia.
        eapply (IH (S j) (S j)); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
        intros regs' H11' Hag. apply Hk0; [exact H11'|].
        eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
      + eapply HG.
        { lb_step F_1b81c D_1b81c b
            ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
          stepb_ft F_1b820 D_1b820 ltac:(pin; rewrite c_eq_byte47; exact Eb).
          stepb_tk F_1b824 D_1b824 ltac:(pin; apply c_eq_byte0; exact Hbnz).
          sv F_1b818 D_1b818 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)).
          apply mst_refl. }
        eapply (IH (S j) acc); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
        intros regs' H11' Hag. apply Hk0; [exact H11'|].
        eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
  Qed.

  Ltac rdA j w := eapply rdn_addr; [apply (rd_auxv _ _ j w); [lia | reflexivity] | f_equal; lia].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma p3_run : forall G, bwd SEGS G -> forall regs Jf rom,
    wfJ sp0 Jf ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 8 = pn ->
    getr regs 9 = envp_w sp0 av ->
    (forall regs',
        getr regs' 1 = Z_to_bv 64 0x1b830 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
        getr regs' 8 = pn ->
        getr regs' 9 = Z_to_bv 64 (A + 160) ->
        getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
        getr regs' 18 = Z_to_bv 64 0x56ee8 ->
        regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 18]%list) regs regs' ->
        G (mkst regs' (0x1ba40 : word) (CM (J_aux sp0 av ev uid hw Jf) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0x1b74c : word)
         (CM (wbytes Jf (Z_to_bv 64 (bv_unsigned sp0 - 368)) (zeros 304)) (fun _ => None)) rom).
  Proof.
    intros G HG regs Jf rom HJ0 H2 H8 H9 Hk.
    pose proof len_av as Hlen. pose proof len_ev as Hlev. pose proof pn_bounds as [Hp1 Hp2].
    assert (HJ : wfJ sp0 (wbytes Jf (Z_to_bv 64 (bv_unsigned sp0 - 368)) (zeros 304))) by (apply wfJ_wbytes; exact HJ0).
    unfold envp_w in H9.
    eapply HG.
    { sn F_1b74c D_1b74c.   (* [comment removed for export] *)
      ld_step F_1b750 D_1b750 (word_to_le_bytes 8 (Z_to_bv 64 0x36b90)) (Z_to_bv 64 0x36b90)
        ltac:(rd_img img_25198_8) ltac:(apply bytes_le_to_Z_8).
                                   (* [comment removed for export] *)
      stw F_1b754 D_1b754 (Z_to_bv 64 0x36b90) (Z_to_bv 64 E) ltac:(ok_data).   (* [comment removed for export] *)
      apply mst_refl. }
    (* [comment removed for export] *)
    eapply (envp_loop G HG (length ev) 0); [lia | gres; pin; f_equal; lia |].
    intros regs1 H9a H10a Hag1.
    carry Hag1 H2 (2 : reg) H2a. carry Hag1 H8 (8 : reg) H8a.
    clear H9 H8 H2.
    eapply HG.
    { sn F_1b764 D_1b764.   (* [comment removed for export] *)
      sn F_1b768 D_1b768.   (* [comment removed for export] *)
      stw F_1b76c D_1b76c (Z_to_bv 64 0x56ef0) (Z_to_bv 64 A) ltac:(ok_data).   (* [comment removed for export] *)
      (* [comment removed for export] *)
      ld_step F_1b770 D_1b770 (word_to_le_bytes 8 (Z_to_bv 64 3)) (Z_to_bv 64 3) ltac:(rdA 0%nat (Z_to_bv 64 3)) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_1b774 D_1b774 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      sv F_1b778 D_1b778 (Z_to_bv 64 (A + 16)).   (* [comment removed for export] *)
      sn F_1b77c D_1b77c.   (* [comment removed for export] *)
      sv F_1b780 D_1b780 (Z_to_bv 64 (bv_unsigned sp0 - 368)).   (* [comment removed for export] *)
      sn F_1b784 D_1b784.   (* [comment removed for export] *)
      (* [comment removed for export] *)
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 0x10040) ltac:(rdA 1%nat (Z_to_bv 64 0x10040)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.   (* [comment removed for export] *)
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 344)).   (* [comment removed for export] *)
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 344)) (Z_to_bv 64 0x10040) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.   (* [comment removed for export] *)
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rdA 2%nat (Z_to_bv 64 4)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 32)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      (* [comment removed for export] *)
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rdA 3%nat (Z_to_bv 64 56)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 336)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 336)) (Z_to_bv 64 56) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 5)) (Z_to_bv 64 5) ltac:(rdA 4%nat (Z_to_bv 64 5)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 48)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      (* [comment removed for export] *)
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rdA 5%nat (Z_to_bv 64 10)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 328)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 328)) (Z_to_bv 64 10) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 16)) (Z_to_bv 64 16) ltac:(rdA 6%nat (Z_to_bv 64 16)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 64)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      (* [comment removed for export] *)
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 hw) hw ltac:(rdA 7%nat hw) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 240)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 240)) hw ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rdA 8%nat (Z_to_bv 64 6)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 80)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      (* [comment removed for export] *)
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096) ltac:(rdA 9%nat (Z_to_bv 64 4096)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 320)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 320)) (Z_to_bv 64 4096) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 11)) (Z_to_bv 64 11) ltac:(rdA 10%nat (Z_to_bv 64 11)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 96)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      (* [comment removed for export] *)
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 uid) uid ltac:(rdA 11%nat uid) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 280)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 280)) uid ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 12)) (Z_to_bv 64 12) ltac:(rdA 12%nat (Z_to_bv 64 12)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 112)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      (* [comment removed for export] *)
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 uid) uid ltac:(rdA 13%nat uid) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 272)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 272)) uid ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 23)) (Z_to_bv 64 23) ltac:(rdA 14%nat (Z_to_bv 64 23)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 128)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      (* [comment removed for export] *)
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 15%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 184)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 184)) (Z_to_bv 64 0) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 25)) (Z_to_bv 64 25) ltac:(rdA 16%nat (Z_to_bv 64 25)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 144)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      (* [comment removed for export] *)
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (at_random_ptr sp0 av ev)) (at_random_ptr sp0 av ev) ltac:(rdA 17%nat (at_random_ptr sp0 av ev)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 168)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 168)) (at_random_ptr sp0 av ev) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 18%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 160)).
      stepb_tk F_1b790 D_1b790 ltac:(pin; cond_compute).   (* [comment removed for export] *)
      (* [comment removed for export] *)
      ld_step F_1b7ac D_1b7ac (word_to_le_bytes 8 hw) hw
        ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)
      ld_step F_1b7b0 D_1b7b0 (zeros 8) (Z_to_bv 64 0)
        ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)
        ltac:(reflexivity).   (* [comment removed for export] *)
      sn F_1b7b4 D_1b7b4.   (* [comment removed for export] *)
      stw F_1b7b8 D_1b7b8 (Z_to_bv 64 0x56f50) hw ltac:(ok_data).   (* [comment removed for export] *)
      stepb_tk F_1b7bc D_1b7bc ltac:(pin; cond_compute).   (* [comment removed for export] *)
      (* [comment removed for export] *)
      ld_step F_1b7d4 D_1b7d4 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096)
        ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)
      stw F_1b7d8 D_1b7d8 (Z_to_bv 64 0x56f18) (Z_to_bv 64 4096) ltac:(ok_data).   (* [comment removed for export] *)
      stepb_tk F_1b7dc D_1b7dc ltac:(pin; apply c_eq_0_false; lia).   (* [comment removed for export] *)
      stepb_tk F_1b7e4 D_1b7e4 ltac:(pin; apply c_eq_0_false; lia).
      (* [comment removed for export] *)
      sn F_1b7f0 D_1b7f0.   (* [comment removed for export] *)
      ld_step F_1b7f4 D_1b7f4 (word_to_le_bytes 8 (Z_to_bv 64 0x56ee0)) (Z_to_bv 64 0x56ee0)
        ltac:(rd_img img_251a0_8) ltac:(apply bytes_le_to_Z_8).
      sn F_1b7f8 D_1b7f8.   (* [comment removed for export] *)
      ld_step F_1b7fc D_1b7fc (word_to_le_bytes 8 (Z_to_bv 64 0x56ed8)) (Z_to_bv 64 0x56ed8)
        ltac:(rd_img img_251a8_8) ltac:(apply bytes_le_to_Z_8).
      stw F_1b800 D_1b800 (Z_to_bv 64 0x56ee0) (cat_argv_ptr sp0 av ev 0) ltac:(ok_data).   (* [comment removed for export] *)
      sv F_1b804 D_1b804 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0 + 1)).   (* [comment removed for export] *)
      stw F_1b808 D_1b808 (Z_to_bv 64 0x56ed8) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0)) ltac:(ok_data).   (* [comment removed for export] *)
      sn F_1b80c D_1b80c.   (* [comment removed for export] *)
      sn F_1b810 D_1b810.   (* [comment removed for export] *)
      apply mst_refl. }
    (* [comment removed for export] *)
    eapply (prog_loop G HG s 0 0); [reflexivity | lia | lia | gres; reflexivity | gres; reflexivity | gres; reflexivity |].
    intros regs2 H11b Hag2.
    carry Hag2 H2a (2 : reg) H2b.
    eapply HG.
    { sv F_1b828 D_1b828 (Z_to_bv 64 (bv_unsigned sp0 - 368)).   (* [comment removed for export] *)
      sn F_1b82c D_1b82c.   (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk.
    - gres; reflexivity.
    - gres. exact H2b.
    - gres. pose proof (Hag2 (8:reg) ltac:(notin_list)) as T; rewrite T; gres; exact H8a.
    - gres. pose proof (Hag2 (9:reg) ltac:(notin_list)) as T; rewrite T; gres; reflexivity.
    - gres; reflexivity.
    - gres. pose proof (Hag2 (18:reg) ltac:(notin_list)) as T; rewrite T; gres; reflexivity.
    - ra_chain.
  Qed.

End P3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
