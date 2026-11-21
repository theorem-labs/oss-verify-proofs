(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the start-up section reads the launch input, mmap base and entry point, the argv and envp pointers follow the launch's string layout, and the auxv walk covers 27 pairs, or 29 under CONFIG_RSEQ; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
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
Local Set Default Proof Using "All".

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
  Variable v : VaSize.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 brk : word.
  Variable rdraw : EntryDraw.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va v (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH entry sp0 rdraw)) (only parsing).
  Local Notation stk := (stack_to_mem sp0 (entry_stack_image inp mbase RPH entry sp0 rdraw)) (only parsing).
  (* [comment removed for export] *)
  Local Notation E := (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))%Z (only parsing).
  Local Notation A := (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))%Z (only parsing).
  Local Notation pn := (cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 0) (only parsing).
  Local Notation rndp := (at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev) (only parsing).
  Local Notation s := (nth 0 av []) (only parsing).
  Local Notation A8 := (Z_to_bv 64 0x56ed8) (only parsing).

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.
  Lemma len_ev : (Z.of_nat (length ev) <= 256)%Z.
  Proof. destruct Hve as [H1 _]. lia. Qed.

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.

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
    = Some (word_to_le_bytes 8 (cat_envp_ptr (ed_top rdraw) av ev (in_execfn inp) k)).
  Proof.
    intros J D k Hk. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (E + 8 * Z.of_nat k)) with (sp0 + nat_to_word (envp_off av + 8 * k))
      by (rewrite word_add_nat; f_equal; unfold envp_off; lia).
    eapply read_envp_ptr_k; first [exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hsp_lo' | exact Hsp_hi' | exact Hk].
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
    eapply read_envp_null; first [exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hsp_lo' | exact Hsp_hi'].
  Qed.

  (* LPS 08b1429: the auxv is [StackLayout.auxv_entries], 27 pairs, or 29 under CONFIG_RSEQ. *)
  Lemma rd_auxv : forall J D j w,
    (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat ->
    nth j (auxv_words (launch_auxv inp sp0 mbase) RPH entry (in_uid inp) (in_gid inp) (in_hwcap inp) rndp
             (at_execfn_ptr (ed_top rdraw) (in_execfn inp))) (Z_to_bv 64 0) = w ->
    rdn SEGS (CM J D) (Z_to_bv 64 (A + 8 * Z.of_nat j)) 8 = Some (word_to_le_bytes 8 w).
  Proof.
    intros J D j w Hj Hw. pose proof len_av. pose proof len_ev.
    assert (Hac : (auxv_count (kb_rseq (in_kernel inp)) <= 29)%nat)
      by (unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia).
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (A + 8 * Z.of_nat j)) with (sp0 + nat_to_word (auxv_off av ev + 8 * j))
      by (rewrite word_add_nat; f_equal; unfold auxv_off; lia).
    rewrite <- Hw. eapply read_auxv_word; first [exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hsp_lo' | exact Hsp_hi' | exact Hj].
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
      assert (Hnz : bv_unsigned (cat_envp_ptr (ed_top rdraw) av ev (in_execfn inp) k) <> 0%Z)
        by (eapply cat_envp_ptr_nz; first [exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hsp_lo' | exact Hsp_hi' | exact Hk | exact RPH | exact entry | exact SEGS]).
      eapply HG.
      { ld_step F_1b758 D_1b758 (word_to_le_bytes 8 (cat_envp_ptr (ed_top rdraw) av ev (in_execfn inp) k)) (cat_envp_ptr (ed_top rdraw) av ev (in_execfn inp) k)
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
    eapply argv_ptr_bounds_at; first [exact Hvl | exact Hlau | exact Hsp_hi' | lia].
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
    eapply read_argv_byte_k; first [exact Hlau | lia | exact Hj].
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

  Ltac rewrite_ers := match goal with Hrs : kb_rseq (in_kernel inp) = _ |- _ => rewrite Hrs end.
  Ltac rdA j w := eapply rdn_addr;
    [ apply (rd_auxv _ _ j w);
      [ unfold auxv_count; rewrite_ers; simpl; lia
      | cbv beta delta [auxv_words auxv_entries];
        change (la_rseq (launch_auxv inp sp0 mbase)) with (kb_rseq (in_kernel inp));
        rewrite_ers; reflexivity ]
    | f_equal; lia ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma p3_run : forall G, bwd SEGS G -> forall regs Jf rom,
    wfJ sp0 Jf ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 8 = pn ->
    getr regs 9 = envp_w inp sp0 ->
    (forall regs',
        getr regs' 1 = Z_to_bv 64 0x1b830 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
        getr regs' 8 = pn ->
        getr regs' 9 = Z_to_bv 64 (A + 16 * Z.of_nat (auxv_count (kb_rseq (in_kernel inp)))) ->
        getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
        getr regs' 18 = Z_to_bv 64 0x56ee8 ->
        regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 18]%list) regs regs' ->
        G (mkst regs' (0x1ba40 : word) (CM (J_aux inp mbase entry sp0 rdraw Jf) (D_libc inp sp0 rdraw)) rom)) ->
    G (mkst regs (0x1b74c : word)
         (CM (wbytes Jf (Z_to_bv 64 (bv_unsigned sp0 - 368)) (zeros 304)) (fun _ => None)) rom).
  Proof.
    intros G HG regs Jf rom HJ0 H2 H8 H9 Hk.
    pose proof len_av as Hlen. pose proof len_ev as Hlev. pose proof pn_bounds as [Hp1 Hp2].
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
    (* The auxv walk runs 29 pairs with CONFIG_RSEQ and 27 without; both are walked. *)
    assert (Hr : kb_rseq (in_kernel inp) = true \/ kb_rseq (in_kernel inp) = false)
      by (destruct (kb_rseq (in_kernel inp)); auto).
    destruct Hr as [Ers | Ers];
      unfold J_aux, J_rseq in Hk; rewrite Ers in Hk; cbv iota in Hk.
    - eapply HG.
    { sn F_1b764 D_1b764.   (* [comment removed for export] *)
      sn F_1b768 D_1b768.   (* [comment removed for export] *)
      stw F_1b76c D_1b76c (Z_to_bv 64 0x56ef0) (Z_to_bv 64 A) ltac:(ok_data).   (* [comment removed for export] *)
      ld_step F_1b770 D_1b770 (word_to_le_bytes 8 (Z_to_bv 64 33)) (Z_to_bv 64 33) ltac:(rdA 0%nat (Z_to_bv 64 33)) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_1b774 D_1b774 ltac:(pin; cond_compute).
      sv F_1b778 D_1b778 (Z_to_bv 64 (A + 16)).
      sn F_1b77c D_1b77c.
      sv F_1b780 D_1b780 (Z_to_bv 64 (bv_unsigned sp0 - 368)).
      sn F_1b784 D_1b784.
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (la_sysinfo_ehdr (launch_auxv inp sp0 mbase))) (la_sysinfo_ehdr (launch_auxv inp sp0 mbase)) ltac:(rdA 1%nat (la_sysinfo_ehdr (launch_auxv inp sp0 mbase))) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 104)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 104)) (la_sysinfo_ehdr (launch_auxv inp sp0 mbase)) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 40)) (Z_to_bv 64 40) ltac:(rdA 2%nat (Z_to_bv 64 40)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 32)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_tk F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 41)) (Z_to_bv 64 41) ltac:(rdA 4%nat (Z_to_bv 64 41)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 48)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_tk F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 42)) (Z_to_bv 64 42) ltac:(rdA 6%nat (Z_to_bv 64 42)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 64)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_tk F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 43)) (Z_to_bv 64 43) ltac:(rdA 8%nat (Z_to_bv 64 43)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 80)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_tk F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 44)) (Z_to_bv 64 44) ltac:(rdA 10%nat (Z_to_bv 64 44)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 96)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_tk F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 45)) (Z_to_bv 64 45) ltac:(rdA 12%nat (Z_to_bv 64 45)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 112)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_tk F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 46)) (Z_to_bv 64 46) ltac:(rdA 14%nat (Z_to_bv 64 46)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 128)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_tk F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 47)) (Z_to_bv 64 47) ltac:(rdA 16%nat (Z_to_bv 64 47)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 144)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_tk F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 51)) (Z_to_bv 64 51) ltac:(rdA 18%nat (Z_to_bv 64 51)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 160)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_tk F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 16)) (Z_to_bv 64 16) ltac:(rdA 20%nat (Z_to_bv 64 16)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 176)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (in_hwcap inp)) (in_hwcap inp) ltac:(rdA 21%nat (in_hwcap inp)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 240)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 240)) (in_hwcap inp) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rdA 22%nat (Z_to_bv 64 6)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 192)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096) ltac:(rdA 23%nat (Z_to_bv 64 4096)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 320)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 320)) (Z_to_bv 64 4096) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 17)) (Z_to_bv 64 17) ltac:(rdA 24%nat (Z_to_bv 64 17)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 208)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 100)) (Z_to_bv 64 100) ltac:(rdA 25%nat (Z_to_bv 64 100)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 232)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 232)) (Z_to_bv 64 100) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 3)) (Z_to_bv 64 3) ltac:(rdA 26%nat (Z_to_bv 64 3)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 224)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 0x10040) ltac:(rdA 27%nat (Z_to_bv 64 0x10040)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 344)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 344)) (Z_to_bv 64 0x10040) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rdA 28%nat (Z_to_bv 64 4)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 240)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rdA 29%nat (Z_to_bv 64 56)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 336)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 336)) (Z_to_bv 64 56) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 5)) (Z_to_bv 64 5) ltac:(rdA 30%nat (Z_to_bv 64 5)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 256)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rdA 31%nat (Z_to_bv 64 10)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 328)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 328)) (Z_to_bv 64 10) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 7)) (Z_to_bv 64 7) ltac:(rdA 32%nat (Z_to_bv 64 7)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 272)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 33%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 312)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 312)) (Z_to_bv 64 0) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 8)) (Z_to_bv 64 8) ltac:(rdA 34%nat (Z_to_bv 64 8)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 288)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 35%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 304)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 304)) (Z_to_bv 64 0) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 9)) (Z_to_bv 64 9) ltac:(rdA 36%nat (Z_to_bv 64 9)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 304)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (entry)) (entry) ltac:(rdA 37%nat (entry)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 296)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 296)) (entry) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 11)) (Z_to_bv 64 11) ltac:(rdA 38%nat (Z_to_bv 64 11)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 320)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rdA 39%nat (in_uid inp)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 280)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 280)) (in_uid inp) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 12)) (Z_to_bv 64 12) ltac:(rdA 40%nat (Z_to_bv 64 12)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 336)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rdA 41%nat (in_uid inp)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 272)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 272)) (in_uid inp) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 13)) (Z_to_bv 64 13) ltac:(rdA 42%nat (Z_to_bv 64 13)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 352)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rdA 43%nat (in_gid inp)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 264)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 264)) (in_gid inp) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 14)) (Z_to_bv 64 14) ltac:(rdA 44%nat (Z_to_bv 64 14)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 368)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rdA 45%nat (in_gid inp)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 256)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 256)) (in_gid inp) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 23)) (Z_to_bv 64 23) ltac:(rdA 46%nat (Z_to_bv 64 23)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 384)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 47%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 184)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 184)) (Z_to_bv 64 0) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 25)) (Z_to_bv 64 25) ltac:(rdA 48%nat (Z_to_bv 64 25)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 400)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))) (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)) ltac:(rdA 49%nat (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 168)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 168)) (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 31)) (Z_to_bv 64 31) ltac:(rdA 50%nat (Z_to_bv 64 31)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 416)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (at_execfn_ptr (ed_top rdraw) (in_execfn inp))) (at_execfn_ptr (ed_top rdraw) (in_execfn inp)) ltac:(rdA 51%nat (at_execfn_ptr (ed_top rdraw) (in_execfn inp))) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 120)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 120)) (at_execfn_ptr (ed_top rdraw) (in_execfn inp)) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 27)) (Z_to_bv 64 27) ltac:(rdA 52%nat (Z_to_bv 64 27)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 432)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 28)) (Z_to_bv 64 28) ltac:(rdA 53%nat (Z_to_bv 64 28)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 152)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 152)) (Z_to_bv 64 28) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 28)) (Z_to_bv 64 28) ltac:(rdA 54%nat (Z_to_bv 64 28)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 448)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 32)) (Z_to_bv 64 32) ltac:(rdA 55%nat (Z_to_bv 64 32)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 144)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 144)) (Z_to_bv 64 32) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 56%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 464)).
      stepb_tk F_1b790 D_1b790 ltac:(pin; cond_compute).
      (* [comment removed for export] *)
      ld_step F_1b7ac D_1b7ac (word_to_le_bytes 8 (in_hwcap inp)) (in_hwcap inp)
        ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)
      ld_step F_1b7b0 D_1b7b0 (zeros 8) (Z_to_bv 64 0)
        ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)
        ltac:(reflexivity).   (* [comment removed for export] *)
      sn F_1b7b4 D_1b7b4.   (* [comment removed for export] *)
      stw F_1b7b8 D_1b7b8 (Z_to_bv 64 0x56f50) (in_hwcap inp) ltac:(ok_data).   (* [comment removed for export] *)
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
      stw F_1b800 D_1b800 (Z_to_bv 64 0x56ee0) (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) ltac:(ok_data).   (* [comment removed for export] *)
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
    + gres; reflexivity.
    + gres. exact H2b.
    + gres. pose proof (Hag2 (8:reg) ltac:(notin_list)) as T; rewrite T; gres; exact H8a.
    + gres. pose proof (Hag2 (9:reg) ltac:(notin_list)) as T; rewrite T; gres; reflexivity.
    + gres; reflexivity.
    + gres. pose proof (Hag2 (18:reg) ltac:(notin_list)) as T; rewrite T; gres; reflexivity.
    + ra_chain.
    - eapply HG.
    { sn F_1b764 D_1b764.   (* [comment removed for export] *)
      sn F_1b768 D_1b768.   (* [comment removed for export] *)
      stw F_1b76c D_1b76c (Z_to_bv 64 0x56ef0) (Z_to_bv 64 A) ltac:(ok_data).   (* [comment removed for export] *)
      ld_step F_1b770 D_1b770 (word_to_le_bytes 8 (Z_to_bv 64 33)) (Z_to_bv 64 33) ltac:(rdA 0%nat (Z_to_bv 64 33)) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_1b774 D_1b774 ltac:(pin; cond_compute).
      sv F_1b778 D_1b778 (Z_to_bv 64 (A + 16)).
      sn F_1b77c D_1b77c.
      sv F_1b780 D_1b780 (Z_to_bv 64 (bv_unsigned sp0 - 368)).
      sn F_1b784 D_1b784.
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (la_sysinfo_ehdr (launch_auxv inp sp0 mbase))) (la_sysinfo_ehdr (launch_auxv inp sp0 mbase)) ltac:(rdA 1%nat (la_sysinfo_ehdr (launch_auxv inp sp0 mbase))) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 104)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 104)) (la_sysinfo_ehdr (launch_auxv inp sp0 mbase)) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 40)) (Z_to_bv 64 40) ltac:(rdA 2%nat (Z_to_bv 64 40)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 32)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_tk F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 41)) (Z_to_bv 64 41) ltac:(rdA 4%nat (Z_to_bv 64 41)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 48)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_tk F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 42)) (Z_to_bv 64 42) ltac:(rdA 6%nat (Z_to_bv 64 42)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 64)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_tk F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 43)) (Z_to_bv 64 43) ltac:(rdA 8%nat (Z_to_bv 64 43)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 80)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_tk F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 44)) (Z_to_bv 64 44) ltac:(rdA 10%nat (Z_to_bv 64 44)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 96)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_tk F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 45)) (Z_to_bv 64 45) ltac:(rdA 12%nat (Z_to_bv 64 45)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 112)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_tk F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 46)) (Z_to_bv 64 46) ltac:(rdA 14%nat (Z_to_bv 64 46)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 128)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_tk F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 47)) (Z_to_bv 64 47) ltac:(rdA 16%nat (Z_to_bv 64 47)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 144)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_tk F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 51)) (Z_to_bv 64 51) ltac:(rdA 18%nat (Z_to_bv 64 51)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 160)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_tk F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 16)) (Z_to_bv 64 16) ltac:(rdA 20%nat (Z_to_bv 64 16)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 176)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (in_hwcap inp)) (in_hwcap inp) ltac:(rdA 21%nat (in_hwcap inp)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 240)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 240)) (in_hwcap inp) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rdA 22%nat (Z_to_bv 64 6)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 192)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096) ltac:(rdA 23%nat (Z_to_bv 64 4096)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 320)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 320)) (Z_to_bv 64 4096) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 17)) (Z_to_bv 64 17) ltac:(rdA 24%nat (Z_to_bv 64 17)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 208)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 100)) (Z_to_bv 64 100) ltac:(rdA 25%nat (Z_to_bv 64 100)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 232)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 232)) (Z_to_bv 64 100) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 3)) (Z_to_bv 64 3) ltac:(rdA 26%nat (Z_to_bv 64 3)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 224)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 0x10040) ltac:(rdA 27%nat (Z_to_bv 64 0x10040)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 344)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 344)) (Z_to_bv 64 0x10040) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rdA 28%nat (Z_to_bv 64 4)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 240)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rdA 29%nat (Z_to_bv 64 56)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 336)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 336)) (Z_to_bv 64 56) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 5)) (Z_to_bv 64 5) ltac:(rdA 30%nat (Z_to_bv 64 5)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 256)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rdA 31%nat (Z_to_bv 64 10)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 328)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 328)) (Z_to_bv 64 10) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 7)) (Z_to_bv 64 7) ltac:(rdA 32%nat (Z_to_bv 64 7)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 272)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 33%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 312)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 312)) (Z_to_bv 64 0) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 8)) (Z_to_bv 64 8) ltac:(rdA 34%nat (Z_to_bv 64 8)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 288)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 35%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 304)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 304)) (Z_to_bv 64 0) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 9)) (Z_to_bv 64 9) ltac:(rdA 36%nat (Z_to_bv 64 9)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 304)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (entry)) (entry) ltac:(rdA 37%nat (entry)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 296)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 296)) (entry) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 11)) (Z_to_bv 64 11) ltac:(rdA 38%nat (Z_to_bv 64 11)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 320)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rdA 39%nat (in_uid inp)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 280)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 280)) (in_uid inp) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 12)) (Z_to_bv 64 12) ltac:(rdA 40%nat (Z_to_bv 64 12)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 336)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rdA 41%nat (in_uid inp)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 272)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 272)) (in_uid inp) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 13)) (Z_to_bv 64 13) ltac:(rdA 42%nat (Z_to_bv 64 13)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 352)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rdA 43%nat (in_gid inp)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 264)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 264)) (in_gid inp) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 14)) (Z_to_bv 64 14) ltac:(rdA 44%nat (Z_to_bv 64 14)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 368)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rdA 45%nat (in_gid inp)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 256)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 256)) (in_gid inp) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 23)) (Z_to_bv 64 23) ltac:(rdA 46%nat (Z_to_bv 64 23)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 384)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 47%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 184)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 184)) (Z_to_bv 64 0) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 25)) (Z_to_bv 64 25) ltac:(rdA 48%nat (Z_to_bv 64 25)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 400)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))) (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)) ltac:(rdA 49%nat (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 168)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 168)) (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 31)) (Z_to_bv 64 31) ltac:(rdA 50%nat (Z_to_bv 64 31)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 416)).
      stepb_ft F_1b790 D_1b790 ltac:(pin; cond_compute).
      stepb_ft F_1b794 D_1b794 ltac:(pin; cond_compute).
      ld_step F_1b798 D_1b798 (word_to_le_bytes 8 (at_execfn_ptr (ed_top rdraw) (in_execfn inp))) (at_execfn_ptr (ed_top rdraw) (in_execfn inp)) ltac:(rdA 51%nat (at_execfn_ptr (ed_top rdraw) (in_execfn inp))) ltac:(apply bytes_le_to_Z_8).
      sn F_1b79c D_1b79c.
      sv F_1b7a0 D_1b7a0 (Z_to_bv 64 (bv_unsigned sp0 - 120)).
      stw F_1b7a4 D_1b7a4 (Z_to_bv 64 (bv_unsigned sp0 - 120)) (at_execfn_ptr (ed_top rdraw) (in_execfn inp)) ltac:(ok_win HJ0).
      sn F_1b7a8 D_1b7a8.
      ld_step F_1b788 D_1b788 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 52%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
      sv F_1b78c D_1b78c (Z_to_bv 64 (A + 432)).
      stepb_tk F_1b790 D_1b790 ltac:(pin; cond_compute).
      (* [comment removed for export] *)
      ld_step F_1b7ac D_1b7ac (word_to_le_bytes 8 (in_hwcap inp)) (in_hwcap inp)
        ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)
      ld_step F_1b7b0 D_1b7b0 (zeros 8) (Z_to_bv 64 0)
        ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)
        ltac:(reflexivity).   (* [comment removed for export] *)
      sn F_1b7b4 D_1b7b4.   (* [comment removed for export] *)
      stw F_1b7b8 D_1b7b8 (Z_to_bv 64 0x56f50) (in_hwcap inp) ltac:(ok_data).   (* [comment removed for export] *)
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
      stw F_1b800 D_1b800 (Z_to_bv 64 0x56ee0) (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) ltac:(ok_data).   (* [comment removed for export] *)
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
    + gres; reflexivity.
    + gres. exact H2b.
    + gres. pose proof (Hag2 (8:reg) ltac:(notin_list)) as T; rewrite T; gres; exact H8a.
    + gres. pose proof (Hag2 (9:reg) ltac:(notin_list)) as T; rewrite T; gres; reflexivity.
    + gres; reflexivity.
    + gres. pose proof (Hag2 (18:reg) ltac:(notin_list)) as T; rewrite T; gres; reflexivity.
    + ra_chain.
  Qed.

End P3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
