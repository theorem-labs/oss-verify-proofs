(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.cjson.cjson_read_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.StartupTac.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.ArgvEnv.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib Require PStartupDefs.
Import OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib.PStartupDefs.RefLayout.
From OssFuzzTheorems.Proofs.cjson.cjson_read_fuzzer.lib Require Import UStartupImg UStartupDefs UStartupCode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
#[local] Existing Instance fx0.
Unset Lia Cache.

Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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
  Local Notation stk := (stack_to_mem sp0 (entry_stack_image RPH sp0 av ev uid hw rdraw)) (only parsing).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Notation E := (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))%Z (only parsing).
  Local Notation A := (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))%Z (only parsing).

  Local Notation pn := (cat_argv_ptr sp0 av ev 0) (only parsing).
  Local Notation rnd := (at_random_ptr sp0 av ev) (only parsing).
  Local Notation s := (nth 0 av []) (only parsing).
  Local Notation A8 := (Z_to_bv 64 0x54c48) (only parsing).

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.
  Lemma len_ev : (Z.of_nat (length ev) <= 256)%Z.
  Proof. destruct Hve as [H1 _]. lia. Qed.

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof. exact Hhi. Qed.

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
        G (mkst regs' (0x15988 : word) (CM J D) rom)) ->
    G (mkst regs (0x1597c : word) (CM J D) rom).
  Proof using Hva Hve Hlo Hhi.
    intros G backG n.
    pose proof len_av as avCount. pose proof len_ev as evCount.
    induction n as [|n deeper]; intros k regs J D rom slotsLeft cursorAt onExit.
    - assert (k = length ev) as atNull by lia. subst k.
      gsteps backG.
      + ld_step F_1597c D_1597c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
          ltac:(apply rd_envp_null) ltac:(apply bytes_le_to_Z_8).
        sv F_15980 D_15980 (Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8)).
        stepb F_15984 D_15984.
        apply mst_refl.
      + refine (onExit _ _ _ _); [gres; reflexivity | gres; reflexivity | solve_regs_agree].
    - gsteps backG.
      + ld_step F_1597c D_1597c (word_to_le_bytes 8 (cat_envp_ptr sp0 av ev k))
          (cat_envp_ptr sp0 av ev k) ltac:(apply rd_envp; lia) ltac:(apply bytes_le_to_Z_8).
        sv F_15980 D_15980 (Z_to_bv 64 (E + 8 * Z.of_nat (S k))).
        stepb_tk F_15984 D_15984 ltac:(apply c_eq_0_false;
          apply (cat_envp_ptr_nz RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi'); lia).
        apply mst_refl.
      + eapply (deeper (S k)); [lia | gres; reflexivity |].
        intros regs' cursorEnd a0Null keptOut.
        apply onExit; [exact cursorEnd | exact a0Null |].
        eapply regs_agree_trans; [| exact keptOut]. solve_regs_agree.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma prog_loop : forall G, bwd SEGS G -> forall l2 j acc regs J D rom,
    skipn j s = l2 -> (j <= length s)%nat -> (acc <= j)%nat ->
    getr regs 10 = Z_to_bv 64 0x54c48 ->
    getr regs 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1) ->
    getr regs 12 = Z_to_bv 64 47 ->
    (forall regs',
        getr regs' 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat (length s) + 1) ->
        regs_agree (fun r => In r [11; 13]%list) regs regs' ->
        G (mkst regs' (0x15a4c : word)
                       (CM J (wbytes D A8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn
                                 + Z.of_nat (after_last_slash l2 j acc)))))) rom)) ->
    G (mkst regs (0x15a40 : word)
                   (CM J (wbytes D A8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat acc))))) rom).
  Proof using Hva Hve Hlo Hhi.
    intros G backG l2.
    pose proof len_av as avCount. pose proof pn_bounds as [pnFloor pnRoof].
    assert (noNul : ~ In (Z_to_bv 8 0) s).
    { destruct Hva as (_ & _ & _ & cleanStrs & _).
      exact (proj1 (Forall_nth _ _) cleanStrs 0%nat [] ltac:(lia)). }
    induction l2 as [|c tail more];
      intros j acc regs J D rom suffix jFits accBehind a0At a1At a2At onExit.
    - assert (j = length s) as jEnd by (apply skipn_all_iff in suffix; lia).
      assert (nulByte : nth j (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = Z_to_bv 8 0)
        by (rewrite jEnd; apply nth_middle).
      gsteps backG.
      + lb_step F_15a40 D_15a40 (Z_to_bv 8 0)
          ltac:(apply (rdn_addr _ _ _ _ _ _ (rd_argv0_byte J _ j _ jFits nulByte)); f_equal; lia).
        stepb_ft F_15a44 D_15a44 ltac:(pin; cond_compute).
        stepb F_15a48 D_15a48.
        apply mst_refl.
      + apply onExit; [gres; pin; f_equal; lia | solve_regs_agree].
    - assert (jInside : (j < length s)%nat).
      { pose proof (f_equal (@length byte) suffix) as lens.
        rewrite length_skipn in lens. cbn [length] in lens. lia. }
      rewrite (skipn_nth s j (Z_to_bv 8 0) jInside) in suffix.
      injection suffix as cAt tailAt.
      assert (cNonNul : c <> Z_to_bv 8 0).
      { intro cZero. apply noNul. rewrite <- cZero, <- cAt. apply nth_In. exact jInside. }
      assert (cByte : nth j (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = c)
        by (rewrite app_nth1 by exact jInside; exact cAt).
      cbn [after_last_slash] in onExit.
      destruct (bv_eqb c (Z_to_bv 8 47)) eqn:slashTest.
      + gsteps backG.
        * lb_step F_15a40 D_15a40 c
            ltac:(apply (rdn_addr _ _ _ _ _ _ (rd_argv0_byte J _ j _ jFits cByte)); f_equal; lia).
          stepb_tk F_15a44 D_15a44 ltac:(pin; rewrite c_eq_byte47; exact slashTest).
          stw F_15a38 D_15a38 (Z_to_bv 64 347208)
            (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j))) ok_data.
          rewrite wbytes_shadow by (len_rw; unorm; lia).
          sv F_15a3c D_15a3c (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)).
          apply mst_refl.
        * eapply (more (S j) (S j));
            [exact tailAt | lia | lia | gres; exact a0At | gres; reflexivity | gres; exact a2At |].
          intros regs' a1Done keptOut.
          apply onExit; [exact a1Done |].
          eapply regs_agree_trans; [| exact keptOut]. solve_regs_agree.
      + gsteps backG.
        * lb_step F_15a40 D_15a40 c
            ltac:(apply (rdn_addr _ _ _ _ _ _ (rd_argv0_byte J _ j _ jFits cByte)); f_equal; lia).
          stepb_ft F_15a44 D_15a44 ltac:(pin; rewrite c_eq_byte47; exact slashTest).
          stepb_tk F_15a48 D_15a48 ltac:(apply c_eq_byte0; exact cNonNul).
          sv F_15a3c D_15a3c (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)).
          apply mst_refl.
        * eapply (more (S j) acc);
            [exact tailAt | lia | lia | gres; exact a0At | gres; reflexivity | gres; exact a2At |].
          intros regs' a1Done keptOut.
          apply onExit; [exact a1Done |].
          eapply regs_agree_trans; [| exact keptOut]. solve_regs_agree.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Ltac rdA j w := eapply rdn_addr; [apply (rd_auxv _ _ j w); [lia | reflexivity] | f_equal; lia].

  Lemma p3_run : forall G, bwd SEGS G -> forall regs Jf rom,
    wfJ sp0 Jf ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 8 = pn ->
    getr regs 9 = envp_w sp0 av ->
    getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
    (forall regs',
        getr regs' 1 = Z_to_bv 64 0x15a54 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
        getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
        getr regs' 18 = Z_to_bv 64 0x54c58 ->
        regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 18]%list) regs regs' ->
        G (mkst regs' (0x15c64 : word) (CM (J_aux sp0 av ev uid hw Jf) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0x15970 : word)
         (CM (wbytes Jf (Z_to_bv 64 (bv_unsigned sp0 - 368)) (zeros 304)) (fun _ => None)) rom).
  Proof using Hva Hve Hlo Hhi.
    intros G backG regs Jf rom jfFull spAt s0At s1At a0At onExit.
    pose proof len_av as avCount. pose proof len_ev as evCount.
    pose proof pn_bounds as [pnFloor pnRoof].
    gsteps backG.
    - sn F_15970 D_15970.
      ld_step F_15974 D_15974 (word_to_le_bytes 8 (Z_to_bv 64 215296)) (Z_to_bv 64 215296)
        ltac:(rd_img img_23608_8) ltac:(apply bytes_le_to_Z_8).
      stw F_15978 D_15978 (Z_to_bv 64 215296) (envp_w sp0 av) ok_data.
      apply mst_refl.
    - eapply (envp_loop G backG (length ev) 0%nat); [lia | gres; pin; unfold envp_w; f_equal; lia |].
      intros envRegs cursorPast nullSeen keptEnv.
      carry keptEnv spAt (2 : reg) spEnv. carry keptEnv s0At (8 : reg) s0Env.
      gsteps backG.
      + sn F_15988 D_15988. sn F_1598c D_1598c.
        stw F_15990 D_15990 (Z_to_bv 64 347232)
          (Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8)) ok_data.
        ld_step F_15994 D_15994 (word_to_le_bytes 8 (Z_to_bv 64 3)) (Z_to_bv 64 3)
          ltac:(rdA 0%nat (Z_to_bv 64 3)) ltac:(apply bytes_le_to_Z_8).
        stepb F_15998 D_15998.
        sv F_1599c D_1599c (Z_to_bv 64 (A + 8 * Z.of_nat 2)).
        sn F_159a0 D_159a0.
        sv F_159a4 D_159a4 (Z_to_bv 64 (bv_unsigned sp0 - 368)).
        sn F_159a8 D_159a8.
        stepb F_159b8 D_159b8.
        ld_step F_159bc D_159bc (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600)
          ltac:(rdA 1%nat (Z_to_bv 64 65600)) ltac:(apply bytes_le_to_Z_8).
        sn F_159c0 D_159c0.
        sv F_159c4 D_159c4 (Z_to_bv 64 (bv_unsigned sp0 - 344)).
        stw F_159c8 D_159c8 (Z_to_bv 64 (bv_unsigned sp0 - 344)) (Z_to_bv 64 65600) ltac:(ok_win jfFull).
        sn F_159cc D_159cc.
        ld_step F_159ac D_159ac (word_to_le_bytes 8 (Z_to_bv 64 4)) (Z_to_bv 64 4)
          ltac:(rdA 2%nat (Z_to_bv 64 4)) ltac:(apply bytes_le_to_Z_8).
        sv F_159b0 D_159b0 (Z_to_bv 64 (A + 8 * Z.of_nat 4)).
        stepb F_159b4 D_159b4. stepb F_159b8 D_159b8.
        ld_step F_159bc D_159bc (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56)
          ltac:(rdA 3%nat (Z_to_bv 64 56)) ltac:(apply bytes_le_to_Z_8).
        sn F_159c0 D_159c0. sv F_159c4 D_159c4 (Z_to_bv 64 (bv_unsigned sp0 - 336)).
        stw F_159c8 D_159c8 (Z_to_bv 64 (bv_unsigned sp0 - 336)) (Z_to_bv 64 56) ltac:(ok_win jfFull).
        sn F_159cc D_159cc.
        ld_step F_159ac D_159ac (word_to_le_bytes 8 (Z_to_bv 64 5)) (Z_to_bv 64 5)
          ltac:(rdA 4%nat (Z_to_bv 64 5)) ltac:(apply bytes_le_to_Z_8).
        sv F_159b0 D_159b0 (Z_to_bv 64 (A + 8 * Z.of_nat 6)).
        stepb F_159b4 D_159b4. stepb F_159b8 D_159b8.
        ld_step F_159bc D_159bc (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10)
          ltac:(rdA 5%nat (Z_to_bv 64 10)) ltac:(apply bytes_le_to_Z_8).
        sn F_159c0 D_159c0. sv F_159c4 D_159c4 (Z_to_bv 64 (bv_unsigned sp0 - 328)).
        stw F_159c8 D_159c8 (Z_to_bv 64 (bv_unsigned sp0 - 328)) (Z_to_bv 64 10) ltac:(ok_win jfFull).
        sn F_159cc D_159cc.
        ld_step F_159ac D_159ac (word_to_le_bytes 8 (Z_to_bv 64 16)) (Z_to_bv 64 16)
          ltac:(rdA 6%nat (Z_to_bv 64 16)) ltac:(apply bytes_le_to_Z_8).
        sv F_159b0 D_159b0 (Z_to_bv 64 (A + 8 * Z.of_nat 8)).
        stepb F_159b4 D_159b4. stepb F_159b8 D_159b8.
        ld_step F_159bc D_159bc (word_to_le_bytes 8 hw) hw
          ltac:(rdA 7%nat hw) ltac:(apply bytes_le_to_Z_8).
        sn F_159c0 D_159c0. sv F_159c4 D_159c4 (Z_to_bv 64 (bv_unsigned sp0 - 240)).
        stw F_159c8 D_159c8 (Z_to_bv 64 (bv_unsigned sp0 - 240)) hw ltac:(ok_win jfFull).
        sn F_159cc D_159cc.
        ld_step F_159ac D_159ac (word_to_le_bytes 8 (Z_to_bv 64 6)) (Z_to_bv 64 6)
          ltac:(rdA 8%nat (Z_to_bv 64 6)) ltac:(apply bytes_le_to_Z_8).
        sv F_159b0 D_159b0 (Z_to_bv 64 (A + 8 * Z.of_nat 10)).
        stepb F_159b4 D_159b4. stepb F_159b8 D_159b8.
        ld_step F_159bc D_159bc (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096)
          ltac:(rdA 9%nat (Z_to_bv 64 4096)) ltac:(apply bytes_le_to_Z_8).
        sn F_159c0 D_159c0. sv F_159c4 D_159c4 (Z_to_bv 64 (bv_unsigned sp0 - 320)).
        stw F_159c8 D_159c8 (Z_to_bv 64 (bv_unsigned sp0 - 320)) (Z_to_bv 64 4096) ltac:(ok_win jfFull).
        sn F_159cc D_159cc.
        ld_step F_159ac D_159ac (word_to_le_bytes 8 (Z_to_bv 64 11)) (Z_to_bv 64 11)
          ltac:(rdA 10%nat (Z_to_bv 64 11)) ltac:(apply bytes_le_to_Z_8).
        sv F_159b0 D_159b0 (Z_to_bv 64 (A + 8 * Z.of_nat 12)).
        stepb F_159b4 D_159b4. stepb F_159b8 D_159b8.
        ld_step F_159bc D_159bc (word_to_le_bytes 8 uid) uid
          ltac:(rdA 11%nat uid) ltac:(apply bytes_le_to_Z_8).
        sn F_159c0 D_159c0. sv F_159c4 D_159c4 (Z_to_bv 64 (bv_unsigned sp0 - 280)).
        stw F_159c8 D_159c8 (Z_to_bv 64 (bv_unsigned sp0 - 280)) uid ltac:(ok_win jfFull).
        sn F_159cc D_159cc.
        ld_step F_159ac D_159ac (word_to_le_bytes 8 (Z_to_bv 64 12)) (Z_to_bv 64 12)
          ltac:(rdA 12%nat (Z_to_bv 64 12)) ltac:(apply bytes_le_to_Z_8).
        sv F_159b0 D_159b0 (Z_to_bv 64 (A + 8 * Z.of_nat 14)).
        stepb F_159b4 D_159b4. stepb F_159b8 D_159b8.
        ld_step F_159bc D_159bc (word_to_le_bytes 8 uid) uid
          ltac:(rdA 13%nat uid) ltac:(apply bytes_le_to_Z_8).
        sn F_159c0 D_159c0. sv F_159c4 D_159c4 (Z_to_bv 64 (bv_unsigned sp0 - 272)).
        stw F_159c8 D_159c8 (Z_to_bv 64 (bv_unsigned sp0 - 272)) uid ltac:(ok_win jfFull).
        sn F_159cc D_159cc.
        ld_step F_159ac D_159ac (word_to_le_bytes 8 (Z_to_bv 64 23)) (Z_to_bv 64 23)
          ltac:(rdA 14%nat (Z_to_bv 64 23)) ltac:(apply bytes_le_to_Z_8).
        sv F_159b0 D_159b0 (Z_to_bv 64 (A + 8 * Z.of_nat 16)).
        stepb F_159b4 D_159b4. stepb F_159b8 D_159b8.
        ld_step F_159bc D_159bc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
          ltac:(rdA 15%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
        sn F_159c0 D_159c0. sv F_159c4 D_159c4 (Z_to_bv 64 (bv_unsigned sp0 - 184)).
        stw F_159c8 D_159c8 (Z_to_bv 64 (bv_unsigned sp0 - 184)) (Z_to_bv 64 0) ltac:(ok_win jfFull).
        sn F_159cc D_159cc.
        ld_step F_159ac D_159ac (word_to_le_bytes 8 (Z_to_bv 64 25)) (Z_to_bv 64 25)
          ltac:(rdA 16%nat (Z_to_bv 64 25)) ltac:(apply bytes_le_to_Z_8).
        sv F_159b0 D_159b0 (Z_to_bv 64 (A + 8 * Z.of_nat 18)).
        stepb F_159b4 D_159b4. stepb F_159b8 D_159b8.
        ld_step F_159bc D_159bc (word_to_le_bytes 8 (at_random_ptr sp0 av ev)) (at_random_ptr sp0 av ev)
          ltac:(rdA 17%nat (at_random_ptr sp0 av ev)) ltac:(apply bytes_le_to_Z_8).
        sn F_159c0 D_159c0. sv F_159c4 D_159c4 (Z_to_bv 64 (bv_unsigned sp0 - 168)).
        stw F_159c8 D_159c8 (Z_to_bv 64 (bv_unsigned sp0 - 168)) (at_random_ptr sp0 av ev) ltac:(ok_win jfFull).
        sn F_159cc D_159cc.
        ld_step F_159ac D_159ac (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
          ltac:(rdA 18%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
        sv F_159b0 D_159b0 (Z_to_bv 64 (A + 8 * Z.of_nat 20)).
        stepb F_159b4 D_159b4.
        ld_step F_159d0 D_159d0 (word_to_le_bytes 8 hw) hw
          ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
        ld_step F_159d4 D_159d4 (zeros 8) (Z_to_bv 64 0)
          ltac:(rewrite rdn_cmem_win by region_side; peel;
                apply rdn_wbytes_zeros_in; unorm; lia) ltac:(reflexivity).
        sn F_159d8 D_159d8.
        stw F_159dc D_159dc (Z_to_bv 64 347328) hw ok_data.
        stepb F_159e0 D_159e0.
        ld_step F_159f8 D_159f8 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096)
          ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
        stw F_159fc D_159fc (Z_to_bv 64 347272) (Z_to_bv 64 4096) ok_data.
        stepb_tk F_15a00 D_15a00 ltac:(pin; apply c_eq_0_false; lia).
        stepb_tk F_15a08 D_15a08 ltac:(pin; apply c_eq_0_false; lia).
        sn F_15a14 D_15a14.
        ld_step F_15a18 D_15a18 (word_to_le_bytes 8 (Z_to_bv 64 347216)) (Z_to_bv 64 347216)
          ltac:(rd_img img_23610_8) ltac:(apply bytes_le_to_Z_8).
        sn F_15a1c D_15a1c.
        ld_step F_15a20 D_15a20 (word_to_le_bytes 8 (Z_to_bv 64 347208)) (Z_to_bv 64 347208)
          ltac:(rd_img img_23618_8) ltac:(apply bytes_le_to_Z_8).
        stw F_15a24 D_15a24 (Z_to_bv 64 347216) (cat_argv_ptr sp0 av ev 0) ok_data.
        sv F_15a28 D_15a28 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0 + 1)).
        stw F_15a2c D_15a2c (Z_to_bv 64 347208) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0)) ok_data.
        sn F_15a30 D_15a30. sn F_15a34 D_15a34.
        apply mst_refl.
      + eapply (prog_loop G backG s 0%nat 0%nat);
          [reflexivity | lia | lia | gres; reflexivity | gres; reflexivity | gres; reflexivity |].
        intros progRegs a1Last keptProg.
        carry keptProg spEnv (2 : reg) spProg. carry keptProg spEnv (18 : reg) s2Prog.
        gsteps backG.
        * sv F_15a4c D_15a4c (Z_to_bv 64 (bv_unsigned sp0 - 368)).
          sn F_15a50 D_15a50.
          apply mst_refl.
        * replace (Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8)) with (auxv_w sp0 av ev)
            by (unfold auxv_w; f_equal; lia).
          apply onExit;
            [gres; reflexivity | gres; exact spProg | gres; reflexivity
            | gres; rewrite s2Prog; reflexivity | ra_chain].
  Qed.

End P3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
