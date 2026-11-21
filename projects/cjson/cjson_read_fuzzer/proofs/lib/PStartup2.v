(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the section takes the whole ProcInput, the mmap base, brk and the launch hypotheses; envp/argv pointers from the stack top and exec filename; the auxv walk follows the new auxv layout in both CONFIG_RSEQ cases; bsb_len dropped, Proof using added, some comments removed. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.StartupTac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.ArgvEnv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.RefLayout.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import PStartupImg PStartupDefs PStartupCode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
#[local] Existing Instance fx0.
Unset Lia Cache.

Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Plain.M.phdrs.
Abbreviation RENT := (Z_to_bv 64 (Z.of_N Plain.M.init_pc)).

Section P3.
  Variable sp0 : word.
  Variable inp : ProcInput.
  Variables mbase brk : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).
  Local Notation rseq := (kb_rseq (in_kernel inp)) (only parsing).

  Local Notation mem0 := (wrap_mem inp mbase RPH RENT sp0 rdraw) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH RENT sp0 rdraw)) (only parsing).
  Local Notation stk := (stack_to_mem sp0 (entry_stack_image inp mbase RPH RENT sp0 rdraw)) (only parsing).
  (* [comment removed for export] *)
  Local Notation E := (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))%Z (only parsing).
  Local Notation A := (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))%Z (only parsing).

  Local Notation pn := (cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 0) (only parsing).
  Local Notation rnd := (at_random_ptr sp0 rseq av ev) (only parsing).
  Local Notation s := (nth 0 av []) (only parsing).
  Local Notation A8 := (Z_to_bv 64 0x53b08) (only parsing).

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.
  Lemma len_ev : (Z.of_nat (length ev) <= 256)%Z.
  Proof. destruct Hve as [H1 _]. lia. Qed.

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof using Hlo. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof using Hhi. exact Hhi. Qed.
  Ltac lctx := first [ exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hsp_lo' | exact Hsp_hi' | exact Hal ].

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
  Proof using Hhi Hlo Hve Hva Hvl Hlau.
    intros J D k Hk. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (E + 8 * Z.of_nat k)) with (sp0 + nat_to_word (envp_off av + 8 * k))
      by (rewrite word_add_nat; f_equal; unfold envp_off; lia).
    eapply read_envp_ptr_k; first [lctx | exact Hk].
  Qed.

  Lemma rd_envp_null : forall J D,
    rdn SEGS (CM J D) (Z_to_bv 64 (E + 8 * Z.of_nat (length ev))) 8
    = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Proof using Hhi Hlo Hve Hva Hvl Hlau.
    intros J D. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (E + 8 * Z.of_nat (length ev)))
      with (sp0 + nat_to_word (envp_off av + 8 * length ev))
      by (rewrite word_add_nat; f_equal; unfold envp_off; lia).
    eapply read_envp_null; lctx.
  Qed.

  Local Notation AUXW := (auxv_words (launch_auxv inp sp0 mbase) RPH RENT (in_uid inp) (in_gid inp) hw rnd
                            (at_execfn_ptr (ed_top rdraw) (in_execfn inp))) (only parsing).

  Lemma rd_auxv : forall J D j w, (j < 2 * auxv_count rseq)%nat ->
    nth j AUXW (Z_to_bv 64 0) = w ->
    rdn SEGS (CM J D) (Z_to_bv 64 (A + 8 * Z.of_nat j)) 8 = Some (word_to_le_bytes 8 w).
  Proof using Hhi Hlo Hve Hva Hvl Hlau.
    intros J D j w Hj Hw. pose proof len_av. pose proof len_ev.
    assert (Hj58 : (j < 58)%nat) by (unfold auxv_count in Hj; destruct (kb_rseq (in_kernel inp)); lia).
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (A + 8 * Z.of_nat j)) with (sp0 + nat_to_word (auxv_off av ev + 8 * j))
      by (rewrite word_add_nat; f_equal; unfold auxv_off; lia).
    rewrite <- Hw. eapply read_auxv_word; first [lctx | exact Hj].
  Qed.

  (** The auxv's tail: under CONFIG_RSEQ two more pairs, AT_RSEQ_FEATURE_SIZE
      (27, 28) and AT_RSEQ_ALIGN (28, 32), then AT_NULL; without it AT_NULL
      follows AT_EXECFN directly ([StackLayout.auxv_entries]). *)
  Lemma auxw_tail_rseq : rseq = true ->
    nth 52 AUXW (Z_to_bv 64 0) = Z_to_bv 64 27 /\ nth 53 AUXW (Z_to_bv 64 0) = Z_to_bv 64 28
    /\ nth 54 AUXW (Z_to_bv 64 0) = Z_to_bv 64 28 /\ nth 55 AUXW (Z_to_bv 64 0) = Z_to_bv 64 32
    /\ nth 56 AUXW (Z_to_bv 64 0) = Z_to_bv 64 0.
  Proof using.
    intros Hrs. unfold auxv_words, auxv_entries.
    change (la_rseq (launch_auxv inp sp0 mbase)) with (kb_rseq (in_kernel inp)). rewrite Hrs.
    repeat split; reflexivity.
  Qed.

  Lemma auxw_tail_norseq : rseq = false -> nth 52 AUXW (Z_to_bv 64 0) = Z_to_bv 64 0.
  Proof using.
    intros Hrs. unfold auxv_words, auxv_entries.
    change (la_rseq (launch_auxv inp sp0 mbase)) with (kb_rseq (in_kernel inp)). rewrite Hrs.
    reflexivity.
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
        G (mkst regs' (0x14844 : word) (CM J D) rom)) ->
    G (mkst regs (0x14838 : word) (CM J D) rom).
  Proof using Hhi Hlo Hve Hva Hvl Hlau.
    intros G HG.
    pose proof len_av as Hlen. pose proof len_ev as Hlev.
    induction n as [|n IH]; intros k regs J D rom Hkn H9 Hk0.
    - (* [comment removed for export] *)
      assert (k = length ev) by lia. subst k.
      eapply HG.
      { ld_step F_14838 D_14838 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
          ltac:(apply rd_envp_null) ltac:(apply bytes_le_to_Z_8).
        sv F_1483c D_1483c (Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8)).
        stepb_ft F_14840 D_14840 ltac:(pin; cond_compute).
        apply mst_refl. }
      apply Hk0; [gres; reflexivity | gres; reflexivity | solve_regs_agree].
    - assert (Hk : (k < length ev)%nat) by lia.
      assert (Hnz : bv_unsigned (cat_envp_ptr (ed_top rdraw) av ev (in_execfn inp) k) <> 0%Z)
        by (eapply cat_envp_ptr_nz with (ph := RPH) (entry := RENT); first [lctx | exact Hk]).
      eapply HG.
      { ld_step F_14838 D_14838 (word_to_le_bytes 8 (cat_envp_ptr (ed_top rdraw) av ev (in_execfn inp) k)) (cat_envp_ptr (ed_top rdraw) av ev (in_execfn inp) k)
          ltac:(apply rd_envp; exact Hk) ltac:(apply bytes_le_to_Z_8).
        sv F_1483c D_1483c (Z_to_bv 64 (E + 8 * Z.of_nat (S k))).
        stepb_tk F_14840 D_14840 ltac:(pin; apply c_eq_0_false; exact Hnz).
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
  Proof using Hhi Hve Hva Hvl Hlau.
    pose proof len_av.
    eapply argv_ptr_bounds_at; first [lctx | lia].
  Qed.

  Lemma rd_argv0_byte : forall J D j b, (j <= length s)%nat ->
    nth j (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = b ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j)) 1 = Some [b].
  Proof using Hhi Hlo Hve Hva Hvl Hlau.
    intros J D j b Hj Hb. pose proof len_av. pose proof pn_bounds as [Hp1 Hp2].
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j)) with (pn + nat_to_word j)
      by (rewrite word_add_nat; reflexivity).
    rewrite <- Hb.
    exact (read_argv_byte_k Sv48 SEGS inp mbase RPH RENT sp0 brk rdraw 0 j Hlau ltac:(lia) Hj).
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma prog_loop : forall G, bwd SEGS G -> forall l2 j acc regs J D rom,
    skipn j s = l2 -> (j <= length s)%nat -> (acc <= j)%nat ->
    getr regs 10 = Z_to_bv 64 0x53b08 ->
    getr regs 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1) ->
    getr regs 12 = Z_to_bv 64 47 ->
    (forall regs',
        getr regs' 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat (length s) + 1) ->
        regs_agree (fun r => In r [11; 13]%list) regs regs' ->
        G (mkst regs' (0x14908 : word)
                       (CM J (wbytes D A8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn
                                 + Z.of_nat (after_last_slash l2 j acc)))))) rom)) ->
    G (mkst regs (0x148fc : word)
                   (CM J (wbytes D A8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat acc))))) rom).
  Proof using Hhi Hlo Hve Hva Hvl Hlau.
    intros G HG.
    pose proof len_av as Hlen. pose proof pn_bounds as [Hp1 Hp2].
    pose proof (valid_argv_str_nz av 0 Hva ltac:(lia)) as Hnz.
    induction l2 as [|b l2 IH]; intros j acc regs J D rom Hskip Hj Hacc H10 H11 H12 Hk0.
    - (* [comment removed for export] *)
      assert (Hjl : j = length s).
      { pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
      eapply HG.
      { lb_step F_148fc D_148fc (Z_to_bv 8 0)
          ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | subst j; rewrite app_nth2 by lia; rewrite Nat.sub_diag; reflexivity] | f_equal; lia]).
        stepb_ft F_14900 D_14900 ltac:(pin; cond_compute).
        stepb_ft F_14904 D_14904 ltac:(pin; cond_compute).
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
        { lb_step F_148fc D_148fc b
            ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
          stepb_tk F_14900 D_14900 ltac:(pin; rewrite c_eq_byte47; exact Eb).
          stw F_148f4 D_148f4 (Z_to_bv 64 0x53b08) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1)) ltac:(ok_data).
          rewrite wbytes_shadow by (rewrite ?length_N_to_le_bytes; rewrite ?length_N_to_le_bytes; first [reflexivity | region_side]).
          sv F_148f8 D_148f8 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)).
          apply mst_refl. }
        replace (bv_unsigned pn + Z.of_nat j + 1)%Z with (bv_unsigned pn + Z.of_nat (S j))%Z by lia.
        eapply (IH (S j) (S j)); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
        intros regs' H11' Hag. apply Hk0; [exact H11'|].
        eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
      + eapply HG.
        { lb_step F_148fc D_148fc b
            ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
          stepb_ft F_14900 D_14900 ltac:(pin; rewrite c_eq_byte47; exact Eb).
          stepb_tk F_14904 D_14904 ltac:(pin; apply c_eq_byte0; exact Hbnz).
          sv F_148f8 D_148f8 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)).
          apply mst_refl. }
        eapply (IH (S j) acc); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
        intros regs' H11' Hag. apply Hk0; [exact H11'|].
        eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Ltac rdA j w := eapply rdn_addr;
    [apply (rd_auxv _ _ j w); [unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia | reflexivity] | f_equal; lia].
  (* a read in the auxv's tail, whose words depend on CONFIG_RSEQ; the case hypothesis is the
     one [p3_run]'s split put in context (a tactic body cannot name it before it exists) *)
  (* idtac first: an Ltac whose head is a match runs when passed as a tactic argument *)
  Ltac rdT j w :=
    idtac; lazymatch goal with
    | Hrs : kb_rseq (in_kernel _) = _ |- _ =>
      eapply rdn_addr;
      [apply (rd_auxv _ _ j w);
         [unfold auxv_count; rewrite Hrs; lia
         | first [ apply (auxw_tail_norseq Hrs)
                 | destruct (auxw_tail_rseq Hrs) as (T52 & T53 & T54 & T55 & T56);
                   first [exact T52 | exact T53 | exact T54 | exact T55 | exact T56] ] ]
      | f_equal; lia]
    end.

  Lemma p3_run : forall G, bwd SEGS G -> forall regs Jf rom,
    wfJ sp0 Jf ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 8 = pn ->
    getr regs 9 = envp_w sp0 inp ->
    getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
    (forall regs',
        getr regs' 1 = Z_to_bv 64 0x14910 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
        getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
        getr regs' 18 = Z_to_bv 64 0x53b18 ->
        regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 18]%list) regs regs' ->
        G (mkst regs' (0x14b20 : word) (CM (J_aux sp0 inp mbase rdraw Jf) (D_libc sp0 inp rdraw)) rom)) ->
    G (mkst regs (0x1482c : word)
         (CM (wbytes Jf (Z_to_bv 64 (bv_unsigned sp0 - 368)) (zeros 304)) (fun _ => None)) rom).
  Proof using Hva Hve Hvl Hlau Hlo Hhi Hal.
    intros G HG regs Jf rom HJ H2 H8 H9 H10 Hk.
    pose proof len_av as Hlen. pose proof len_ev as Hlev. pose proof pn_bounds as [Hp1 Hp2].
    unfold envp_w in H9.
    eapply HG.
    { sn F_1482c D_1482c.   (* [comment removed for export] *)
    ld_step F_14830 D_14830 (word_to_le_bytes 8 (Z_to_bv 64 0x337c0)) (Z_to_bv 64 0x337c0)
      ltac:(rd_img img_224c0_8) ltac:(apply bytes_le_to_Z_8).
    stw F_14834 D_14834 (Z_to_bv 64 0x337c0) (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ltac:(ok_data).
      apply mst_refl. }
    (* [comment removed for export] *)
    eapply (envp_loop G HG (length ev) 0); [lia | gres; pin; f_equal; lia |].
    intros regs1 H9a H10a Hag1.
    carry Hag1 H2 (2 : reg) H2a. carry Hag1 H8 (8 : reg) H8a.
    clear H9 H10 H8 H2.
    eapply HG.
    { sn F_14844 D_14844.   (* [comment removed for export] *)
    sn F_14848 D_14848.   (* [comment removed for export] *)
    stw F_1484c D_1484c (Z_to_bv 64 0x53b20)
      (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))) ltac:(ok_data).
    (* [comment removed for export] *)
    (* the auxv loop: [aux[t] = v] for each pair with t < 38, 26 common pairs *)
    ld_step F_14850 D_14850 (word_to_le_bytes 8 (Z_to_bv 64 33)) (Z_to_bv 64 33) ltac:(rdA 0%nat (Z_to_bv 64 33)) ltac:(apply bytes_le_to_Z_8).
    stepb_ft F_14854 D_14854 ltac:(pin; cond_compute).
    sv F_14858 D_14858 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 16)).
    sn F_1485c D_1485c.
    sv F_14860 D_14860 (Z_to_bv 64 (bv_unsigned sp0 - 368)).
    sn F_14864 D_14864.
    stepb_ft F_14874 D_14874 ltac:(pin; cond_compute).
    ld_step F_14878 D_14878 (word_to_le_bytes 8 (ehdr_w sp0 inp mbase)) (ehdr_w sp0 inp mbase) ltac:(rdA 1%nat (ehdr_w sp0 inp mbase)) ltac:(apply bytes_le_to_Z_8).
    sn F_1487c D_1487c.
    sv F_14880 D_14880 (Z_to_bv 64 (bv_unsigned sp0 - 104)).
    stw F_14884 D_14884 (Z_to_bv 64 (bv_unsigned sp0 - 104)) (ehdr_w sp0 inp mbase) ltac:(ok_win HJ).
    sn F_14888 D_14888.
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 40)) (Z_to_bv 64 40) ltac:(rdA 2%nat (Z_to_bv 64 40)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 32)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_tk F_14874 D_14874 ltac:(pin; cond_compute).   (* t >= 38: skipped *)
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 41)) (Z_to_bv 64 41) ltac:(rdA 4%nat (Z_to_bv 64 41)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 48)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_tk F_14874 D_14874 ltac:(pin; cond_compute).   (* t >= 38: skipped *)
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 42)) (Z_to_bv 64 42) ltac:(rdA 6%nat (Z_to_bv 64 42)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 64)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_tk F_14874 D_14874 ltac:(pin; cond_compute).   (* t >= 38: skipped *)
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 43)) (Z_to_bv 64 43) ltac:(rdA 8%nat (Z_to_bv 64 43)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 80)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_tk F_14874 D_14874 ltac:(pin; cond_compute).   (* t >= 38: skipped *)
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 44)) (Z_to_bv 64 44) ltac:(rdA 10%nat (Z_to_bv 64 44)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 96)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_tk F_14874 D_14874 ltac:(pin; cond_compute).   (* t >= 38: skipped *)
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 45)) (Z_to_bv 64 45) ltac:(rdA 12%nat (Z_to_bv 64 45)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 112)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_tk F_14874 D_14874 ltac:(pin; cond_compute).   (* t >= 38: skipped *)
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 46)) (Z_to_bv 64 46) ltac:(rdA 14%nat (Z_to_bv 64 46)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 128)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_tk F_14874 D_14874 ltac:(pin; cond_compute).   (* t >= 38: skipped *)
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 47)) (Z_to_bv 64 47) ltac:(rdA 16%nat (Z_to_bv 64 47)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 144)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_tk F_14874 D_14874 ltac:(pin; cond_compute).   (* t >= 38: skipped *)
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 51)) (Z_to_bv 64 51) ltac:(rdA 18%nat (Z_to_bv 64 51)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 160)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_tk F_14874 D_14874 ltac:(pin; cond_compute).   (* t >= 38: skipped *)
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 16)) (Z_to_bv 64 16) ltac:(rdA 20%nat (Z_to_bv 64 16)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 176)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_ft F_14874 D_14874 ltac:(pin; cond_compute).
    ld_step F_14878 D_14878 (word_to_le_bytes 8 hw) constr:(hw) ltac:(rdA 21%nat constr:(hw)) ltac:(apply bytes_le_to_Z_8).
    sn F_1487c D_1487c.
    sv F_14880 D_14880 (Z_to_bv 64 (bv_unsigned sp0 - 240)).
    stw F_14884 D_14884 (Z_to_bv 64 (bv_unsigned sp0 - 240)) constr:(hw) ltac:(ok_win HJ).
    sn F_14888 D_14888.
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rdA 22%nat (Z_to_bv 64 6)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 192)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_ft F_14874 D_14874 ltac:(pin; cond_compute).
    ld_step F_14878 D_14878 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096) ltac:(rdA 23%nat (Z_to_bv 64 4096)) ltac:(apply bytes_le_to_Z_8).
    sn F_1487c D_1487c.
    sv F_14880 D_14880 (Z_to_bv 64 (bv_unsigned sp0 - 320)).
    stw F_14884 D_14884 (Z_to_bv 64 (bv_unsigned sp0 - 320)) (Z_to_bv 64 4096) ltac:(ok_win HJ).
    sn F_14888 D_14888.
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 17)) (Z_to_bv 64 17) ltac:(rdA 24%nat (Z_to_bv 64 17)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 208)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_ft F_14874 D_14874 ltac:(pin; cond_compute).
    ld_step F_14878 D_14878 (word_to_le_bytes 8 (Z_to_bv 64 100)) (Z_to_bv 64 100) ltac:(rdA 25%nat (Z_to_bv 64 100)) ltac:(apply bytes_le_to_Z_8).
    sn F_1487c D_1487c.
    sv F_14880 D_14880 (Z_to_bv 64 (bv_unsigned sp0 - 232)).
    stw F_14884 D_14884 (Z_to_bv 64 (bv_unsigned sp0 - 232)) (Z_to_bv 64 100) ltac:(ok_win HJ).
    sn F_14888 D_14888.
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 3)) (Z_to_bv 64 3) ltac:(rdA 26%nat (Z_to_bv 64 3)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 224)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_ft F_14874 D_14874 ltac:(pin; cond_compute).
    ld_step F_14878 D_14878 (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 0x10040) ltac:(rdA 27%nat (Z_to_bv 64 0x10040)) ltac:(apply bytes_le_to_Z_8).
    sn F_1487c D_1487c.
    sv F_14880 D_14880 (Z_to_bv 64 (bv_unsigned sp0 - 344)).
    stw F_14884 D_14884 (Z_to_bv 64 (bv_unsigned sp0 - 344)) (Z_to_bv 64 0x10040) ltac:(ok_win HJ).
    sn F_14888 D_14888.
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rdA 28%nat (Z_to_bv 64 4)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 240)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_ft F_14874 D_14874 ltac:(pin; cond_compute).
    ld_step F_14878 D_14878 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rdA 29%nat (Z_to_bv 64 56)) ltac:(apply bytes_le_to_Z_8).
    sn F_1487c D_1487c.
    sv F_14880 D_14880 (Z_to_bv 64 (bv_unsigned sp0 - 336)).
    stw F_14884 D_14884 (Z_to_bv 64 (bv_unsigned sp0 - 336)) (Z_to_bv 64 56) ltac:(ok_win HJ).
    sn F_14888 D_14888.
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 5)) (Z_to_bv 64 5) ltac:(rdA 30%nat (Z_to_bv 64 5)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 256)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_ft F_14874 D_14874 ltac:(pin; cond_compute).
    ld_step F_14878 D_14878 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rdA 31%nat (Z_to_bv 64 10)) ltac:(apply bytes_le_to_Z_8).
    sn F_1487c D_1487c.
    sv F_14880 D_14880 (Z_to_bv 64 (bv_unsigned sp0 - 328)).
    stw F_14884 D_14884 (Z_to_bv 64 (bv_unsigned sp0 - 328)) (Z_to_bv 64 10) ltac:(ok_win HJ).
    sn F_14888 D_14888.
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 7)) (Z_to_bv 64 7) ltac:(rdA 32%nat (Z_to_bv 64 7)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 272)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_ft F_14874 D_14874 ltac:(pin; cond_compute).
    ld_step F_14878 D_14878 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 33%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sn F_1487c D_1487c.
    sv F_14880 D_14880 (Z_to_bv 64 (bv_unsigned sp0 - 312)).
    stw F_14884 D_14884 (Z_to_bv 64 (bv_unsigned sp0 - 312)) (Z_to_bv 64 0) ltac:(ok_win HJ).
    sn F_14888 D_14888.
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 8)) (Z_to_bv 64 8) ltac:(rdA 34%nat (Z_to_bv 64 8)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 288)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_ft F_14874 D_14874 ltac:(pin; cond_compute).
    ld_step F_14878 D_14878 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 35%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sn F_1487c D_1487c.
    sv F_14880 D_14880 (Z_to_bv 64 (bv_unsigned sp0 - 304)).
    stw F_14884 D_14884 (Z_to_bv 64 (bv_unsigned sp0 - 304)) (Z_to_bv 64 0) ltac:(ok_win HJ).
    sn F_14888 D_14888.
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 9)) (Z_to_bv 64 9) ltac:(rdA 36%nat (Z_to_bv 64 9)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 304)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_ft F_14874 D_14874 ltac:(pin; cond_compute).
    ld_step F_14878 D_14878 (word_to_le_bytes 8 (Z_to_bv 64 0x12000)) (Z_to_bv 64 0x12000) ltac:(rdA 37%nat (Z_to_bv 64 0x12000)) ltac:(apply bytes_le_to_Z_8).
    sn F_1487c D_1487c.
    sv F_14880 D_14880 (Z_to_bv 64 (bv_unsigned sp0 - 296)).
    stw F_14884 D_14884 (Z_to_bv 64 (bv_unsigned sp0 - 296)) (Z_to_bv 64 0x12000) ltac:(ok_win HJ).
    sn F_14888 D_14888.
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 11)) (Z_to_bv 64 11) ltac:(rdA 38%nat (Z_to_bv 64 11)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 320)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_ft F_14874 D_14874 ltac:(pin; cond_compute).
    ld_step F_14878 D_14878 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rdA 39%nat (in_uid inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_1487c D_1487c.
    sv F_14880 D_14880 (Z_to_bv 64 (bv_unsigned sp0 - 280)).
    stw F_14884 D_14884 (Z_to_bv 64 (bv_unsigned sp0 - 280)) (in_uid inp) ltac:(ok_win HJ).
    sn F_14888 D_14888.
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 12)) (Z_to_bv 64 12) ltac:(rdA 40%nat (Z_to_bv 64 12)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 336)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_ft F_14874 D_14874 ltac:(pin; cond_compute).
    ld_step F_14878 D_14878 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rdA 41%nat (in_uid inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_1487c D_1487c.
    sv F_14880 D_14880 (Z_to_bv 64 (bv_unsigned sp0 - 272)).
    stw F_14884 D_14884 (Z_to_bv 64 (bv_unsigned sp0 - 272)) (in_uid inp) ltac:(ok_win HJ).
    sn F_14888 D_14888.
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 13)) (Z_to_bv 64 13) ltac:(rdA 42%nat (Z_to_bv 64 13)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 352)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_ft F_14874 D_14874 ltac:(pin; cond_compute).
    ld_step F_14878 D_14878 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rdA 43%nat (in_gid inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_1487c D_1487c.
    sv F_14880 D_14880 (Z_to_bv 64 (bv_unsigned sp0 - 264)).
    stw F_14884 D_14884 (Z_to_bv 64 (bv_unsigned sp0 - 264)) (in_gid inp) ltac:(ok_win HJ).
    sn F_14888 D_14888.
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 14)) (Z_to_bv 64 14) ltac:(rdA 44%nat (Z_to_bv 64 14)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 368)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_ft F_14874 D_14874 ltac:(pin; cond_compute).
    ld_step F_14878 D_14878 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rdA 45%nat (in_gid inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_1487c D_1487c.
    sv F_14880 D_14880 (Z_to_bv 64 (bv_unsigned sp0 - 256)).
    stw F_14884 D_14884 (Z_to_bv 64 (bv_unsigned sp0 - 256)) (in_gid inp) ltac:(ok_win HJ).
    sn F_14888 D_14888.
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 23)) (Z_to_bv 64 23) ltac:(rdA 46%nat (Z_to_bv 64 23)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 384)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_ft F_14874 D_14874 ltac:(pin; cond_compute).
    ld_step F_14878 D_14878 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 47%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sn F_1487c D_1487c.
    sv F_14880 D_14880 (Z_to_bv 64 (bv_unsigned sp0 - 184)).
    stw F_14884 D_14884 (Z_to_bv 64 (bv_unsigned sp0 - 184)) (Z_to_bv 64 0) ltac:(ok_win HJ).
    sn F_14888 D_14888.
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 25)) (Z_to_bv 64 25) ltac:(rdA 48%nat (Z_to_bv 64 25)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 400)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_ft F_14874 D_14874 ltac:(pin; cond_compute).
    ld_step F_14878 D_14878 (word_to_le_bytes 8 rnd) constr:(rnd) ltac:(rdA 49%nat constr:(rnd)) ltac:(apply bytes_le_to_Z_8).
    sn F_1487c D_1487c.
    sv F_14880 D_14880 (Z_to_bv 64 (bv_unsigned sp0 - 168)).
    stw F_14884 D_14884 (Z_to_bv 64 (bv_unsigned sp0 - 168)) constr:(rnd) ltac:(ok_win HJ).
    sn F_14888 D_14888.
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 31)) (Z_to_bv 64 31) ltac:(rdA 50%nat (Z_to_bv 64 31)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 416)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_ft F_14874 D_14874 ltac:(pin; cond_compute).
    ld_step F_14878 D_14878 (word_to_le_bytes 8 (execfn_w inp rdraw)) (execfn_w inp rdraw) ltac:(rdA 51%nat (execfn_w inp rdraw)) ltac:(apply bytes_le_to_Z_8).
    sn F_1487c D_1487c.
    sv F_14880 D_14880 (Z_to_bv 64 (bv_unsigned sp0 - 120)).
    stw F_14884 D_14884 (Z_to_bv 64 (bv_unsigned sp0 - 120)) (execfn_w inp rdraw) ltac:(ok_win HJ).
    sn F_14888 D_14888.
      apply mst_refl. }
    (* CONFIG_RSEQ (kb_rseq (in_kernel inp), free under valid_input) adds two
       pairs before AT_NULL: both cases are walked. *)
    destruct (Sumbool.sumbool_of_bool (kb_rseq (in_kernel inp))) as [Hrs | Hrs];
      [ unfold J_aux in Hk; rewrite Hrs in Hk
      | rewrite (J_aux_norseq sp0 inp mbase rdraw Jf Hlo Hhi Hrs) in Hk ].
  { eapply HG.
    { ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 27)) (Z_to_bv 64 27) ltac:(rdT 52%nat (Z_to_bv 64 27)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 432)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_ft F_14874 D_14874 ltac:(pin; cond_compute).
    ld_step F_14878 D_14878 (word_to_le_bytes 8 (Z_to_bv 64 28)) (Z_to_bv 64 28) ltac:(rdT 53%nat (Z_to_bv 64 28)) ltac:(apply bytes_le_to_Z_8).
    sn F_1487c D_1487c.
    sv F_14880 D_14880 (Z_to_bv 64 (bv_unsigned sp0 - 152)).
    stw F_14884 D_14884 (Z_to_bv 64 (bv_unsigned sp0 - 152)) (Z_to_bv 64 28) ltac:(ok_win HJ).
    sn F_14888 D_14888.
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 28)) (Z_to_bv 64 28) ltac:(rdT 54%nat (Z_to_bv 64 28)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 448)).
    stepb_ft F_14870 D_14870 ltac:(pin; cond_compute).
    stepb_ft F_14874 D_14874 ltac:(pin; cond_compute).
    ld_step F_14878 D_14878 (word_to_le_bytes 8 (Z_to_bv 64 32)) (Z_to_bv 64 32) ltac:(rdT 55%nat (Z_to_bv 64 32)) ltac:(apply bytes_le_to_Z_8).
    sn F_1487c D_1487c.
    sv F_14880 D_14880 (Z_to_bv 64 (bv_unsigned sp0 - 144)).
    stw F_14884 D_14884 (Z_to_bv 64 (bv_unsigned sp0 - 144)) (Z_to_bv 64 32) ltac:(ok_win HJ).
    sn F_14888 D_14888.
    ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdT 56%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 464)).
    stepb_tk F_14870 D_14870 ltac:(pin; cond_compute).   (* AT_NULL: the loop ends *)
    ld_step F_1488c D_1488c (word_to_le_bytes 8 hw) constr:(hw)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)
    ld_step F_14890 D_14890 (zeros 8) (Z_to_bv 64 0)
      ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)
      ltac:(reflexivity).
    sn F_14894 D_14894.   (* [comment removed for export] *)
    stw F_14898 D_14898 (Z_to_bv 64 0x53b80) constr:(hw) ltac:(ok_data).   (* [comment removed for export] *)
    stepb_tk F_1489c D_1489c ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    ld_step F_148b4 D_148b4 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    stw F_148b8 D_148b8 (Z_to_bv 64 0x53b48) (Z_to_bv 64 4096) ltac:(ok_data).
    stepb_tk F_148bc D_148bc ltac:(pin; apply c_eq_0_false; lia).   (* [comment removed for export] *)
    stepb_tk F_148c4 D_148c4 ltac:(pin; apply c_eq_0_false; lia).
    (* [comment removed for export] *)
    sn F_148d0 D_148d0.
    ld_step F_148d4 D_148d4 (word_to_le_bytes 8 (Z_to_bv 64 0x53b10)) (Z_to_bv 64 0x53b10)
      ltac:(rd_img img_224c8_8) ltac:(apply bytes_le_to_Z_8).
    sn F_148d8 D_148d8.
    ld_step F_148dc D_148dc (word_to_le_bytes 8 (Z_to_bv 64 0x53b08)) (Z_to_bv 64 0x53b08)
      ltac:(rd_img img_224d0_8) ltac:(apply bytes_le_to_Z_8).
    stw F_148e0 D_148e0 (Z_to_bv 64 0x53b10) constr:(pn) ltac:(ok_data).
    sv F_148e4 D_148e4 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0 + 1)).   (* [comment removed for export] *)
    stw F_148e8 D_148e8 (Z_to_bv 64 0x53b08) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0)) ltac:(ok_data).
    sn F_148ec D_148ec.   (* [comment removed for export] *)
    sn F_148f0 D_148f0.   (* [comment removed for export] *)
      apply mst_refl. }
    (* [comment removed for export] *)
    eapply (prog_loop G HG s 0 0); [reflexivity | lia | lia | gres; reflexivity | gres; reflexivity | gres; reflexivity |].
    intros regs2 H11b Hag2.
    carry Hag2 H2a (2 : reg) H2b.
    eapply HG.
    { sv F_14908 D_14908 (Z_to_bv 64 (bv_unsigned sp0 - 368)).   (* [comment removed for export] *)
      sn F_1490c D_1490c.   (* [comment removed for export] *)
      apply mst_refl. }
    apply Hk.
    - gres; bveq.
    - gres; exact H2b.
    - gres; reflexivity.
    - gres. pose proof (Hag2 (18:reg) ltac:(notin_list)) as T; rewrite T; gres; reflexivity.
    - ra_chain.
  }
  { eapply HG.
    { ld_step F_14868 D_14868 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdT 52%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sv F_1486c D_1486c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 432)).
    stepb_tk F_14870 D_14870 ltac:(pin; cond_compute).   (* AT_NULL: the loop ends *)
    ld_step F_1488c D_1488c (word_to_le_bytes 8 hw) constr:(hw)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).   (* [comment removed for export] *)
    ld_step F_14890 D_14890 (zeros 8) (Z_to_bv 64 0)
      ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)
      ltac:(reflexivity).
    sn F_14894 D_14894.   (* [comment removed for export] *)
    stw F_14898 D_14898 (Z_to_bv 64 0x53b80) constr:(hw) ltac:(ok_data).   (* [comment removed for export] *)
    stepb_tk F_1489c D_1489c ltac:(pin; cond_compute).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    ld_step F_148b4 D_148b4 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    stw F_148b8 D_148b8 (Z_to_bv 64 0x53b48) (Z_to_bv 64 4096) ltac:(ok_data).
    stepb_tk F_148bc D_148bc ltac:(pin; apply c_eq_0_false; lia).   (* [comment removed for export] *)
    stepb_tk F_148c4 D_148c4 ltac:(pin; apply c_eq_0_false; lia).
    (* [comment removed for export] *)
    sn F_148d0 D_148d0.
    ld_step F_148d4 D_148d4 (word_to_le_bytes 8 (Z_to_bv 64 0x53b10)) (Z_to_bv 64 0x53b10)
      ltac:(rd_img img_224c8_8) ltac:(apply bytes_le_to_Z_8).
    sn F_148d8 D_148d8.
    ld_step F_148dc D_148dc (word_to_le_bytes 8 (Z_to_bv 64 0x53b08)) (Z_to_bv 64 0x53b08)
      ltac:(rd_img img_224d0_8) ltac:(apply bytes_le_to_Z_8).
    stw F_148e0 D_148e0 (Z_to_bv 64 0x53b10) constr:(pn) ltac:(ok_data).
    sv F_148e4 D_148e4 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0 + 1)).   (* [comment removed for export] *)
    stw F_148e8 D_148e8 (Z_to_bv 64 0x53b08) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0)) ltac:(ok_data).
    sn F_148ec D_148ec.   (* [comment removed for export] *)
    sn F_148f0 D_148f0.   (* [comment removed for export] *)
      apply mst_refl. }
    (* [comment removed for export] *)
    eapply (prog_loop G HG s 0 0); [reflexivity | lia | lia | gres; reflexivity | gres; reflexivity | gres; reflexivity |].
    intros regs2 H11b Hag2.
    carry Hag2 H2a (2 : reg) H2b.
    eapply HG.
    { sv F_14908 D_14908 (Z_to_bv 64 (bv_unsigned sp0 - 368)).   (* [comment removed for export] *)
      sn F_1490c D_1490c.   (* [comment removed for export] *)
      apply mst_refl. }
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
