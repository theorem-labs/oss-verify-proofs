(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (section P3 over the launch's ProcInput and its launch facts; musl's auxv walk over the new auxv, 27 pairs or 29 under CONFIG_RSEQ with AT_SYSINFO_EHDR and AT_EXECFN, so the start-up symbolic in CONFIG_RSEQ; bsb_len's bound 2101782; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import StartupTac ArgvEnv RefLayout.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_15000_16000.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Musl Require Import StartupBase StartupDefs.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := rl_segs.

(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := RPH0.

Section P3.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLI : RelocImg RL} {RLD : RelocData RL} {RLW : RelocRW RL RLD} {RST : RelocStart RL RLD}.
  Variable sp0 : word.
  Variable inp : ProcInput.
  Variables mbase brk : word.
  Variable ent : word.   (* the image's entry, as [Run.init_machine_state] hands it to the auxv *)
  Variable drw : EntryDraw.   (* [comment removed for export] *)
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase drw) inp.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.
  Local Notation av := (in_argv inp) (only parsing).
  Local Notation ev := (in_envp inp) (only parsing).
  Local Notation uid := (in_uid inp) (only parsing).
  Local Notation gid := (in_gid inp) (only parsing).
  Local Notation hw := (in_hwcap inp) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z. Proof using Hlo. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z. Proof using Hhi. exact Hhi. Qed.
  (* the launch facts a layout lemma of ArgvEnv/RefLayout asks for *)
  Ltac lctx := first [ exact Hva | exact Hve | exact Hvl | exact Hlau | exact Hsp_lo' | exact Hsp_hi' | exact Hal ].

  Local Notation mem0 := (wrap_mem inp mbase RPH ent sp0 drw) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem inp mbase RPH ent sp0 drw)) (only parsing).
  Local Notation stk := (stack_to_mem sp0 (entry_stack_image inp mbase RPH ent sp0 drw)) (only parsing).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Notation E := (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))%Z (only parsing).
  Local Notation A := (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))%Z (only parsing).

  Local Notation pn := (cat_argv_ptr (ed_top drw) av ev (in_execfn inp) 0) (only parsing).
  Local Notation rnd := (at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev) (only parsing).
  Local Notation xfn := (at_execfn_ptr (ed_top drw) (in_execfn inp)) (only parsing).
  Local Notation s := (nth 0 av []) (only parsing).
  Local Notation A8 := (rl dA_2f848 0x2f858) (only parsing).

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.
  Lemma len_ev : (Z.of_nat (length ev) <= 256)%Z.
  Proof. destruct Hve as [H1 _]. lia. Qed.

  Lemma bsb_len : (Z.of_nat (length (entry_stack_image inp mbase RPH ent sp0 drw)) <= 2101782)%Z.
  Proof using Hvl Hlau. exact (bsb_bound Sv48 inp mbase RPH ent sp0 brk drw Hvl Hlau). Qed.

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
    = Some (word_to_le_bytes 8 (cat_envp_ptr (ed_top drw) av ev (in_execfn inp) k)).
  Proof.
    intros J D k Hk. pose proof len_av. pose proof len_ev.
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (E + 8 * Z.of_nat k)) with (sp0 + nat_to_word (envp_off av + 8 * k))
      by (rewrite word_add_nat; f_equal; unfold envp_off; lia).
    eapply read_envp_ptr_k; first [lctx | exact Hk].
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
    eapply read_envp_null; lctx.
  Qed.

  (* the auxv is [auxv_count (kb_rseq (in_kernel inp))] pairs: 27, or 29 under CONFIG_RSEQ *)
  Lemma rd_auxv : forall J D j w, (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat ->
    nth j (auxv_words (launch_auxv inp sp0 mbase) RPH ent (in_uid inp) (in_gid inp) (in_hwcap inp) rnd xfn)
        (Z_to_bv 64 0) = w ->
    rdn SEGS (CM J D) (Z_to_bv 64 (A + 8 * Z.of_nat j)) 8 = Some (word_to_le_bytes 8 w).
  Proof.
    intros J D j w Hj Hw. pose proof len_av. pose proof len_ev.
    assert (Hc : (auxv_count (kb_rseq (in_kernel inp)) <= 29)%nat)
      by (unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia).
    apply rd_above; [lia | lia |].
    replace (Z_to_bv 64 (A + 8 * Z.of_nat j)) with (sp0 + nat_to_word (auxv_off av ev + 8 * j))
      by (rewrite word_add_nat; f_equal; unfold auxv_off; lia).
    rewrite <- Hw. eapply read_auxv_word; first [lctx | exact Hj].
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
        G (mkst regs' (rl dF_15170 0x151b4) (CM J D) rom)) ->
    G (mkst regs (rl dF_15170 0x151a8) (CM J D) rom).
  Proof.
    intros G HG.
    pose proof len_av as Hlen. pose proof len_ev as Hlev.
    induction n as [|n IH]; intros k regs J D rom Hkn H9 Hk0.
    - (* [comment removed for export] *)
      assert (k = length ev) by lia. subst k.
      eapply HG.
      { ld_step F_151a8 D_151a8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
          ltac:(apply rd_envp_null) ltac:(apply bytes_le_to_Z_8).
        sv F_151ac D_151ac (Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8)).
        stepb_ft F_151b0 D_151b0 ltac:(pin; rl_cond).
        apply mst_refl. }
      apply Hk0; [gres; reflexivity | gres; reflexivity | solve_regs_agree].
    - assert (Hk : (k < length ev)%nat) by lia.
      assert (Hnz : bv_unsigned (cat_envp_ptr (ed_top drw) av ev (in_execfn inp) k) <> 0%Z)
        by (eapply cat_envp_ptr_nz; try (first [lctx | exact Hk]); first [exact RPH | exact ent | exact SEGS]).
      eapply HG.
      { ld_step F_151a8 D_151a8 (word_to_le_bytes 8 (cat_envp_ptr (ed_top drw) av ev (in_execfn inp) k)) (cat_envp_ptr (ed_top drw) av ev (in_execfn inp) k)
          ltac:(apply rd_envp; exact Hk) ltac:(apply bytes_le_to_Z_8).
        sv F_151ac D_151ac (Z_to_bv 64 (E + 8 * Z.of_nat (S k))).
        stepb_tk F_151b0 D_151b0 ltac:(pin; apply c_eq_0_false; exact Hnz).
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
    eapply argv_ptr_bounds_at; try (first [lctx | lia]); first [exact RPH | exact ent | exact SEGS].
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
    exact (read_argv_byte_k Sv48 SEGS inp mbase RPH ent sp0 brk drw 0 j Hlau ltac:(lia) Hj).
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
    getr regs 10 = rl dA_2f848 0x2f858 ->
    getr regs 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1) ->
    getr regs 12 = Z_to_bv 64 47 ->
    (forall regs',
        getr regs' 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat (length s) + 1) ->
        regs_agree (fun r => In r [11; 13]%list) regs regs' ->
        G (mkst regs' (rl dF_15170 0x15278)
                       (CM J (wbytes D A8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn
                                 + Z.of_nat (after_last_slash l2 j acc)))))) rom)) ->
    G (mkst regs (rl dF_15170 0x1526c)
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
      { lb_step F_1526c D_1526c (Z_to_bv 8 0)
          ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | subst j; rewrite app_nth2 by lia; rewrite Nat.sub_diag; reflexivity] | f_equal; lia]).
        stepb_ft F_15270 D_15270 ltac:(pin; rl_cond).
        stepb_ft F_15274 D_15274 ltac:(pin; rl_cond).
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
        { lb_step F_1526c D_1526c b
            ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
          stepb_tk F_15270 D_15270 ltac:(pin; rewrite c_eq_byte47; exact Eb).
          stw F_15264 D_15264 (rl dA_2f848 0x2f858) (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top drw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) + Z.of_nat j + 1)) ltac:(ok_data).
          rewrite wbytes_shadow by (rewrite ?length_N_to_le_bytes; rewrite ?length_N_to_le_bytes; first [reflexivity | region_side]).
          sv F_15268 D_15268 (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top drw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) + Z.of_nat (S j) + 1)).
          apply mst_refl. }
        replace (bv_unsigned pn + Z.of_nat j + 1)%Z with (bv_unsigned pn + Z.of_nat (S j))%Z by lia.
        eapply (IH (S j) (S j)); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
        intros regs' H11' Hag. apply Hk0; [exact H11'|].
        eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
      + eapply HG.
        { lb_step F_1526c D_1526c b
            ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
          stepb_ft F_15270 D_15270 ltac:(pin; rewrite c_eq_byte47; exact Eb).
          stepb_tk F_15274 D_15274 ltac:(pin; apply c_eq_byte0; exact Hbnz).
          sv F_15268 D_15268 (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top drw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) + Z.of_nat (S j) + 1)).
          apply mst_refl. }
        eapply (IH (S j) acc); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
        intros regs' H11' Hag. apply Hk0; [exact H11'|].
        eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Ltac rdA j w := eapply rdn_addr;
    [ apply (rd_auxv _ _ j w);
      [ first [ lia
              | unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia
              | unfold auxv_count; match goal with H : kb_rseq (in_kernel inp) = _ |- _ => rewrite H end; lia ]
      | first [ reflexivity
              | unfold auxv_words, auxv_entries;
                change (la_rseq (launch_auxv inp sp0 mbase)) with (kb_rseq (in_kernel inp));
                match goal with H : kb_rseq (in_kernel inp) = _ |- _ => rewrite H end; reflexivity ] ]
    | f_equal; lia ].

  Lemma p3_run : forall G, bwd SEGS G -> forall regs Jf rom,
    wfJ sp0 Jf ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 8 = pn ->
    getr regs 9 = envp_w sp0 inp ->
    getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
    (forall regs',
        getr regs' 1 = rl dF_15170 0x15280 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
        getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
        getr regs' 18 = rl dA_2f848 0x2f868 ->
        regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 18]%list) regs regs' ->
        G (mkst regs' (rl dF_15490 0x15490) (CM (J_aux sp0 inp mbase ent drw Jf) (D_libc sp0 inp drw)) rom)) ->
    G (mkst regs (rl dF_15170 0x1519c)
         (CM (wbytes Jf (Z_to_bv 64 (bv_unsigned sp0 - 368)) (zeros 304)) (fun _ => None)) rom).
  Proof using fx RL RLC RLS RLI RLD RLW RST Hva Hve Hvl Hlau Hlo Hhi Hal.
    intros G HG regs Jf rom HJ H2 H8 H9 H10 Hk.
    pose proof len_av as Hlen. pose proof len_ev as Hlev. pose proof pn_bounds as [Hp1 Hp2].
    unfold envp_w in H9.
    eapply HG.
    { sn F_1519c D_1519c.   (* [comment removed for export] *)
    ld_step F_151a0 D_151a0 (word_to_le_bytes 8 (rl dA_2f6b0s 0x2f6b0)) (rl dA_2f6b0s 0x2f6b0)
      ltac:(rd_img img_1e3b8_8) ltac:(apply bytes_le_to_Z_8).
    stw F_151a4 D_151a4 (rl dA_2f6b0s 0x2f6b0) (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ltac:(ok_data).
      apply mst_refl. }
    (* [comment removed for export] *)
    eapply (envp_loop G HG (length ev) 0); [lia | gres; pin; f_equal; lia |].
    intros regs1 H9a H10a Hag1.
    carry Hag1 H2 (2 : reg) H2a. carry Hag1 H8 (8 : reg) H8a.
    clear H9 H10 H8 H2.
    (* the 26 pairs every launch carries ([StackLayout.auxv_entries]); musl stores aux[t] for t < 38 *)
    eapply HG.
    { sn F_151b4 D_151b4.   (* [comment removed for export] *)
    sn F_151b8 D_151b8.   (* [comment removed for export] *)
    stw F_151bc D_151bc (rl dA_2f848 0x2f870)
      (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))) ltac:(ok_data).
    ld_step F_151c0 D_151c0 (word_to_le_bytes 8 (Z_to_bv 64 33)) (Z_to_bv 64 33) ltac:(rdA 0%nat (Z_to_bv 64 33)) ltac:(apply bytes_le_to_Z_8).
    stepb_ft F_151c4 D_151c4 ltac:(pin; rl_cond).
    sv F_151c8 D_151c8 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 16)).
    sn F_151cc D_151cc.
    sv F_151d0 D_151d0 (Z_to_bv 64 (bv_unsigned sp0 - 368)).
    sn F_151d4 D_151d4.
    stepb_ft F_151e4 D_151e4 ltac:(pin; rl_cond).
    ld_step F_151e8 D_151e8 (word_to_le_bytes 8 (la_sysinfo_ehdr (launch_auxv inp sp0 mbase))) (la_sysinfo_ehdr (launch_auxv inp sp0 mbase)) ltac:(rdA 1%nat (la_sysinfo_ehdr (launch_auxv inp sp0 mbase))) ltac:(apply bytes_le_to_Z_8).
    sn F_151ec D_151ec.
    sv F_151f0 D_151f0 (Z_to_bv 64 (bv_unsigned sp0 - 104)).
    stw F_151f4 D_151f4 (Z_to_bv 64 (bv_unsigned sp0 - 104)) (la_sysinfo_ehdr (launch_auxv inp sp0 mbase)) ltac:(ok_win HJ).
    sn F_151f8 D_151f8.
    (* auxv entry 1: type 40 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 40)) (Z_to_bv 64 40) ltac:(rdA 2%nat (Z_to_bv 64 40)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 32)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_tk F_151e4 D_151e4 ltac:(pin; rl_cond).   (* t >= 38: back to the loop head *)
    (* auxv entry 2: type 41 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 41)) (Z_to_bv 64 41) ltac:(rdA 4%nat (Z_to_bv 64 41)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 48)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_tk F_151e4 D_151e4 ltac:(pin; rl_cond).   (* t >= 38: back to the loop head *)
    (* auxv entry 3: type 42 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 42)) (Z_to_bv 64 42) ltac:(rdA 6%nat (Z_to_bv 64 42)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 64)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_tk F_151e4 D_151e4 ltac:(pin; rl_cond).   (* t >= 38: back to the loop head *)
    (* auxv entry 4: type 43 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 43)) (Z_to_bv 64 43) ltac:(rdA 8%nat (Z_to_bv 64 43)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 80)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_tk F_151e4 D_151e4 ltac:(pin; rl_cond).   (* t >= 38: back to the loop head *)
    (* auxv entry 5: type 44 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 44)) (Z_to_bv 64 44) ltac:(rdA 10%nat (Z_to_bv 64 44)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 96)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_tk F_151e4 D_151e4 ltac:(pin; rl_cond).   (* t >= 38: back to the loop head *)
    (* auxv entry 6: type 45 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 45)) (Z_to_bv 64 45) ltac:(rdA 12%nat (Z_to_bv 64 45)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 112)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_tk F_151e4 D_151e4 ltac:(pin; rl_cond).   (* t >= 38: back to the loop head *)
    (* auxv entry 7: type 46 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 46)) (Z_to_bv 64 46) ltac:(rdA 14%nat (Z_to_bv 64 46)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 128)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_tk F_151e4 D_151e4 ltac:(pin; rl_cond).   (* t >= 38: back to the loop head *)
    (* auxv entry 8: type 47 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 47)) (Z_to_bv 64 47) ltac:(rdA 16%nat (Z_to_bv 64 47)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 144)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_tk F_151e4 D_151e4 ltac:(pin; rl_cond).   (* t >= 38: back to the loop head *)
    (* auxv entry 9: type 51 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 51)) (Z_to_bv 64 51) ltac:(rdA 18%nat (Z_to_bv 64 51)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 160)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_tk F_151e4 D_151e4 ltac:(pin; rl_cond).   (* t >= 38: back to the loop head *)
    (* auxv entry 10: type 16 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 16)) (Z_to_bv 64 16) ltac:(rdA 20%nat (Z_to_bv 64 16)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 176)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_ft F_151e4 D_151e4 ltac:(pin; rl_cond).
    ld_step F_151e8 D_151e8 (word_to_le_bytes 8 (in_hwcap inp)) (in_hwcap inp) ltac:(rdA 21%nat (in_hwcap inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_151ec D_151ec.
    sv F_151f0 D_151f0 (Z_to_bv 64 (bv_unsigned sp0 - 240)).
    stw F_151f4 D_151f4 (Z_to_bv 64 (bv_unsigned sp0 - 240)) (in_hwcap inp) ltac:(ok_win HJ).
    sn F_151f8 D_151f8.
    (* auxv entry 11: type 6 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rdA 22%nat (Z_to_bv 64 6)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 192)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_ft F_151e4 D_151e4 ltac:(pin; rl_cond).
    ld_step F_151e8 D_151e8 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096) ltac:(rdA 23%nat (Z_to_bv 64 4096)) ltac:(apply bytes_le_to_Z_8).
    sn F_151ec D_151ec.
    sv F_151f0 D_151f0 (Z_to_bv 64 (bv_unsigned sp0 - 320)).
    stw F_151f4 D_151f4 (Z_to_bv 64 (bv_unsigned sp0 - 320)) (Z_to_bv 64 4096) ltac:(ok_win HJ).
    sn F_151f8 D_151f8.
    (* auxv entry 12: type 17 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 17)) (Z_to_bv 64 17) ltac:(rdA 24%nat (Z_to_bv 64 17)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 208)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_ft F_151e4 D_151e4 ltac:(pin; rl_cond).
    ld_step F_151e8 D_151e8 (word_to_le_bytes 8 (Z_to_bv 64 100)) (Z_to_bv 64 100) ltac:(rdA 25%nat (Z_to_bv 64 100)) ltac:(apply bytes_le_to_Z_8).
    sn F_151ec D_151ec.
    sv F_151f0 D_151f0 (Z_to_bv 64 (bv_unsigned sp0 - 232)).
    stw F_151f4 D_151f4 (Z_to_bv 64 (bv_unsigned sp0 - 232)) (Z_to_bv 64 100) ltac:(ok_win HJ).
    sn F_151f8 D_151f8.
    (* auxv entry 13: type 3 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 3)) (Z_to_bv 64 3) ltac:(rdA 26%nat (Z_to_bv 64 3)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 224)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_ft F_151e4 D_151e4 ltac:(pin; rl_cond).
    ld_step F_151e8 D_151e8 (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 0x10040) ltac:(rdA 27%nat (Z_to_bv 64 0x10040)) ltac:(apply bytes_le_to_Z_8).
    sn F_151ec D_151ec.
    sv F_151f0 D_151f0 (Z_to_bv 64 (bv_unsigned sp0 - 344)).
    stw F_151f4 D_151f4 (Z_to_bv 64 (bv_unsigned sp0 - 344)) (Z_to_bv 64 0x10040) ltac:(ok_win HJ).
    sn F_151f8 D_151f8.
    (* auxv entry 14: type 4 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rdA 28%nat (Z_to_bv 64 4)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 240)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_ft F_151e4 D_151e4 ltac:(pin; rl_cond).
    ld_step F_151e8 D_151e8 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rdA 29%nat (Z_to_bv 64 56)) ltac:(apply bytes_le_to_Z_8).
    sn F_151ec D_151ec.
    sv F_151f0 D_151f0 (Z_to_bv 64 (bv_unsigned sp0 - 336)).
    stw F_151f4 D_151f4 (Z_to_bv 64 (bv_unsigned sp0 - 336)) (Z_to_bv 64 56) ltac:(ok_win HJ).
    sn F_151f8 D_151f8.
    (* auxv entry 15: type 5 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 5)) (Z_to_bv 64 5) ltac:(rdA 30%nat (Z_to_bv 64 5)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 256)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_ft F_151e4 D_151e4 ltac:(pin; rl_cond).
    ld_step F_151e8 D_151e8 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rdA 31%nat (Z_to_bv 64 10)) ltac:(apply bytes_le_to_Z_8).
    sn F_151ec D_151ec.
    sv F_151f0 D_151f0 (Z_to_bv 64 (bv_unsigned sp0 - 328)).
    stw F_151f4 D_151f4 (Z_to_bv 64 (bv_unsigned sp0 - 328)) (Z_to_bv 64 10) ltac:(ok_win HJ).
    sn F_151f8 D_151f8.
    (* auxv entry 16: type 7 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 7)) (Z_to_bv 64 7) ltac:(rdA 32%nat (Z_to_bv 64 7)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 272)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_ft F_151e4 D_151e4 ltac:(pin; rl_cond).
    ld_step F_151e8 D_151e8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 33%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sn F_151ec D_151ec.
    sv F_151f0 D_151f0 (Z_to_bv 64 (bv_unsigned sp0 - 312)).
    stw F_151f4 D_151f4 (Z_to_bv 64 (bv_unsigned sp0 - 312)) (Z_to_bv 64 0) ltac:(ok_win HJ).
    sn F_151f8 D_151f8.
    (* auxv entry 17: type 8 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 8)) (Z_to_bv 64 8) ltac:(rdA 34%nat (Z_to_bv 64 8)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 288)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_ft F_151e4 D_151e4 ltac:(pin; rl_cond).
    ld_step F_151e8 D_151e8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 35%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sn F_151ec D_151ec.
    sv F_151f0 D_151f0 (Z_to_bv 64 (bv_unsigned sp0 - 304)).
    stw F_151f4 D_151f4 (Z_to_bv 64 (bv_unsigned sp0 - 304)) (Z_to_bv 64 0) ltac:(ok_win HJ).
    sn F_151f8 D_151f8.
    (* auxv entry 18: type 9 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 9)) (Z_to_bv 64 9) ltac:(rdA 36%nat (Z_to_bv 64 9)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 304)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_ft F_151e4 D_151e4 ltac:(pin; rl_cond).
    ld_step F_151e8 D_151e8 (word_to_le_bytes 8 ent) ent ltac:(rdA 37%nat ent) ltac:(apply bytes_le_to_Z_8).
    sn F_151ec D_151ec.
    sv F_151f0 D_151f0 (Z_to_bv 64 (bv_unsigned sp0 - 296)).
    stw F_151f4 D_151f4 (Z_to_bv 64 (bv_unsigned sp0 - 296)) ent ltac:(ok_win HJ).
    sn F_151f8 D_151f8.
    (* auxv entry 19: type 11 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 11)) (Z_to_bv 64 11) ltac:(rdA 38%nat (Z_to_bv 64 11)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 320)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_ft F_151e4 D_151e4 ltac:(pin; rl_cond).
    ld_step F_151e8 D_151e8 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rdA 39%nat (in_uid inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_151ec D_151ec.
    sv F_151f0 D_151f0 (Z_to_bv 64 (bv_unsigned sp0 - 280)).
    stw F_151f4 D_151f4 (Z_to_bv 64 (bv_unsigned sp0 - 280)) (in_uid inp) ltac:(ok_win HJ).
    sn F_151f8 D_151f8.
    (* auxv entry 20: type 12 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 12)) (Z_to_bv 64 12) ltac:(rdA 40%nat (Z_to_bv 64 12)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 336)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_ft F_151e4 D_151e4 ltac:(pin; rl_cond).
    ld_step F_151e8 D_151e8 (word_to_le_bytes 8 (in_uid inp)) (in_uid inp) ltac:(rdA 41%nat (in_uid inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_151ec D_151ec.
    sv F_151f0 D_151f0 (Z_to_bv 64 (bv_unsigned sp0 - 272)).
    stw F_151f4 D_151f4 (Z_to_bv 64 (bv_unsigned sp0 - 272)) (in_uid inp) ltac:(ok_win HJ).
    sn F_151f8 D_151f8.
    (* auxv entry 21: type 13 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 13)) (Z_to_bv 64 13) ltac:(rdA 42%nat (Z_to_bv 64 13)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 352)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_ft F_151e4 D_151e4 ltac:(pin; rl_cond).
    ld_step F_151e8 D_151e8 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rdA 43%nat (in_gid inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_151ec D_151ec.
    sv F_151f0 D_151f0 (Z_to_bv 64 (bv_unsigned sp0 - 264)).
    stw F_151f4 D_151f4 (Z_to_bv 64 (bv_unsigned sp0 - 264)) (in_gid inp) ltac:(ok_win HJ).
    sn F_151f8 D_151f8.
    (* auxv entry 22: type 14 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 14)) (Z_to_bv 64 14) ltac:(rdA 44%nat (Z_to_bv 64 14)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 368)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_ft F_151e4 D_151e4 ltac:(pin; rl_cond).
    ld_step F_151e8 D_151e8 (word_to_le_bytes 8 (in_gid inp)) (in_gid inp) ltac:(rdA 45%nat (in_gid inp)) ltac:(apply bytes_le_to_Z_8).
    sn F_151ec D_151ec.
    sv F_151f0 D_151f0 (Z_to_bv 64 (bv_unsigned sp0 - 256)).
    stw F_151f4 D_151f4 (Z_to_bv 64 (bv_unsigned sp0 - 256)) (in_gid inp) ltac:(ok_win HJ).
    sn F_151f8 D_151f8.
    (* auxv entry 23: type 23 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 23)) (Z_to_bv 64 23) ltac:(rdA 46%nat (Z_to_bv 64 23)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 384)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_ft F_151e4 D_151e4 ltac:(pin; rl_cond).
    ld_step F_151e8 D_151e8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 47%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sn F_151ec D_151ec.
    sv F_151f0 D_151f0 (Z_to_bv 64 (bv_unsigned sp0 - 184)).
    stw F_151f4 D_151f4 (Z_to_bv 64 (bv_unsigned sp0 - 184)) (Z_to_bv 64 0) ltac:(ok_win HJ).
    sn F_151f8 D_151f8.
    (* auxv entry 24: type 25 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 25)) (Z_to_bv 64 25) ltac:(rdA 48%nat (Z_to_bv 64 25)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 400)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_ft F_151e4 D_151e4 ltac:(pin; rl_cond).
    ld_step F_151e8 D_151e8 (word_to_le_bytes 8 (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))) (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)) ltac:(rdA 49%nat (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))) ltac:(apply bytes_le_to_Z_8).
    sn F_151ec D_151ec.
    sv F_151f0 D_151f0 (Z_to_bv 64 (bv_unsigned sp0 - 168)).
    stw F_151f4 D_151f4 (Z_to_bv 64 (bv_unsigned sp0 - 168)) (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)) ltac:(ok_win HJ).
    sn F_151f8 D_151f8.
    (* auxv entry 25: type 31 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 31)) (Z_to_bv 64 31) ltac:(rdA 50%nat (Z_to_bv 64 31)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 416)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_ft F_151e4 D_151e4 ltac:(pin; rl_cond).
    ld_step F_151e8 D_151e8 (word_to_le_bytes 8 (at_execfn_ptr (ed_top drw) (in_execfn inp))) (at_execfn_ptr (ed_top drw) (in_execfn inp)) ltac:(rdA 51%nat (at_execfn_ptr (ed_top drw) (in_execfn inp))) ltac:(apply bytes_le_to_Z_8).
    sn F_151ec D_151ec.
    sv F_151f0 D_151f0 (Z_to_bv 64 (bv_unsigned sp0 - 120)).
    stw F_151f4 D_151f4 (Z_to_bv 64 (bv_unsigned sp0 - 120)) (at_execfn_ptr (ed_top drw) (in_execfn inp)) ltac:(ok_win HJ).
    sn F_151f8 D_151f8.
      apply mst_refl. }
    (* CONFIG_RSEQ: two more pairs, then AT_NULL; otherwise AT_NULL at once.  Both cases. *)
    destruct (Sumbool.sumbool_of_bool (kb_rseq (in_kernel inp))) as [Hrs|Hrs];
      [ unfold J_aux in Hk; rewrite Hrs in Hk; cbv iota in Hk
      | rewrite (J_aux_norseq sp0 inp mbase ent drw Jf Hlo Hhi Hrs) in Hk ].
    - eapply HG.
      {
    (* auxv entry 26: type 27 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 27)) (Z_to_bv 64 27) ltac:(rdA 52%nat (Z_to_bv 64 27)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 432)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_ft F_151e4 D_151e4 ltac:(pin; rl_cond).
    ld_step F_151e8 D_151e8 (word_to_le_bytes 8 (Z_to_bv 64 28)) (Z_to_bv 64 28) ltac:(rdA 53%nat (Z_to_bv 64 28)) ltac:(apply bytes_le_to_Z_8).
    sn F_151ec D_151ec.
    sv F_151f0 D_151f0 (Z_to_bv 64 (bv_unsigned sp0 - 152)).
    stw F_151f4 D_151f4 (Z_to_bv 64 (bv_unsigned sp0 - 152)) (Z_to_bv 64 28) ltac:(ok_win HJ).
    sn F_151f8 D_151f8.
    (* auxv entry 27: type 28 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 28)) (Z_to_bv 64 28) ltac:(rdA 54%nat (Z_to_bv 64 28)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 448)).
    stepb_ft F_151e0 D_151e0 ltac:(pin; rl_cond).
    stepb_ft F_151e4 D_151e4 ltac:(pin; rl_cond).
    ld_step F_151e8 D_151e8 (word_to_le_bytes 8 (Z_to_bv 64 32)) (Z_to_bv 64 32) ltac:(rdA 55%nat (Z_to_bv 64 32)) ltac:(apply bytes_le_to_Z_8).
    sn F_151ec D_151ec.
    sv F_151f0 D_151f0 (Z_to_bv 64 (bv_unsigned sp0 - 144)).
    stw F_151f4 D_151f4 (Z_to_bv 64 (bv_unsigned sp0 - 144)) (Z_to_bv 64 32) ltac:(ok_win HJ).
    sn F_151f8 D_151f8.
    (* AT_NULL at entry 28 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 56%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 464)).
    stepb_tk F_151e0 D_151e0 ltac:(pin; rl_cond).
    ld_step F_151fc D_151fc (word_to_le_bytes 8 (in_hwcap inp)) (in_hwcap inp)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    ld_step F_15200 D_15200 (zeros 8) (Z_to_bv 64 0)
      ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)
      ltac:(reflexivity).
    sn F_15204 D_15204.
    stw F_15208 D_15208 (rl dA_2f848 0x2f8d0) (in_hwcap inp) ltac:(ok_data).
    stepb_tk F_1520c D_1520c ltac:(pin; rl_cond).
    ld_step F_15224 D_15224 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    stw F_15228 D_15228 (rl dA_2f848 0x2f898) (Z_to_bv 64 4096) ltac:(ok_data).
    stepb_tk F_1522c D_1522c ltac:(pin; apply c_eq_0_false; lia).
    stepb_tk F_15234 D_15234 ltac:(pin; apply c_eq_0_false; lia).
    sn F_15240 D_15240.
    ld_step F_15244 D_15244 (word_to_le_bytes 8 (rl dA_2f848 0x2f860)) (rl dA_2f848 0x2f860)
      ltac:(rd_img img_1e3c0_8) ltac:(apply bytes_le_to_Z_8).
    sn F_15248 D_15248.
    ld_step F_1524c D_1524c (word_to_le_bytes 8 (rl dA_2f848 0x2f858)) (rl dA_2f848 0x2f858)
      ltac:(rd_img img_1e3c8_8) ltac:(apply bytes_le_to_Z_8).
    stw F_15250 D_15250 (rl dA_2f848 0x2f860) (cat_argv_ptr (ed_top drw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) ltac:(ok_data).
    sv F_15254 D_15254 (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top drw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) + Z.of_nat 0 + 1)).
    stw F_15258 D_15258 (rl dA_2f848 0x2f858) (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top drw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) + Z.of_nat 0)) ltac:(ok_data).
    sn F_1525c D_1525c.
    sn F_15260 D_15260.
      apply mst_refl. }
    eapply (prog_loop G HG s 0 0); [reflexivity | lia | lia | gres; reflexivity | gres; reflexivity | gres; reflexivity |];
    intros regs2 H11b Hag2;
    carry Hag2 H2a (2 : reg) H2b;
    (eapply HG; [ sv F_15278 D_15278 (Z_to_bv 64 (bv_unsigned sp0 - 368)); sn F_1527c D_1527c; apply mst_refl | ]);
    (apply Hk;
     [ gres; bveq
     | gres; exact H2b
     | gres; reflexivity
     | gres; pose proof (Hag2 (18:reg) ltac:(notin_list)) as T; rewrite T; gres; reflexivity
     | ra_chain ]).
    - eapply HG.
      {
    (* AT_NULL at entry 26 *)
    ld_step F_151d8 D_151d8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 52%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
    sv F_151dc D_151dc (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 432)).
    stepb_tk F_151e0 D_151e0 ltac:(pin; rl_cond).
    ld_step F_151fc D_151fc (word_to_le_bytes 8 (in_hwcap inp)) (in_hwcap inp)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    ld_step F_15200 D_15200 (zeros 8) (Z_to_bv 64 0)
      ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)
      ltac:(reflexivity).
    sn F_15204 D_15204.
    stw F_15208 D_15208 (rl dA_2f848 0x2f8d0) (in_hwcap inp) ltac:(ok_data).
    stepb_tk F_1520c D_1520c ltac:(pin; rl_cond).
    ld_step F_15224 D_15224 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096)
      ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
    stw F_15228 D_15228 (rl dA_2f848 0x2f898) (Z_to_bv 64 4096) ltac:(ok_data).
    stepb_tk F_1522c D_1522c ltac:(pin; apply c_eq_0_false; lia).
    stepb_tk F_15234 D_15234 ltac:(pin; apply c_eq_0_false; lia).
    sn F_15240 D_15240.
    ld_step F_15244 D_15244 (word_to_le_bytes 8 (rl dA_2f848 0x2f860)) (rl dA_2f848 0x2f860)
      ltac:(rd_img img_1e3c0_8) ltac:(apply bytes_le_to_Z_8).
    sn F_15248 D_15248.
    ld_step F_1524c D_1524c (word_to_le_bytes 8 (rl dA_2f848 0x2f858)) (rl dA_2f848 0x2f858)
      ltac:(rd_img img_1e3c8_8) ltac:(apply bytes_le_to_Z_8).
    stw F_15250 D_15250 (rl dA_2f848 0x2f860) (cat_argv_ptr (ed_top drw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) ltac:(ok_data).
    sv F_15254 D_15254 (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top drw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) + Z.of_nat 0 + 1)).
    stw F_15258 D_15258 (rl dA_2f848 0x2f858) (Z_to_bv 64 (bv_unsigned (cat_argv_ptr (ed_top drw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) + Z.of_nat 0)) ltac:(ok_data).
    sn F_1525c D_1525c.
    sn F_15260 D_15260.
      apply mst_refl. }
    eapply (prog_loop G HG s 0 0); [reflexivity | lia | lia | gres; reflexivity | gres; reflexivity | gres; reflexivity |];
    intros regs2 H11b Hag2;
    carry Hag2 H2a (2 : reg) H2b;
    (eapply HG; [ sv F_15278 D_15278 (Z_to_bv 64 (bv_unsigned sp0 - 368)); sn F_1527c D_1527c; apply mst_refl | ]);
    (apply Hk;
     [ gres; bveq
     | gres; exact H2b
     | gres; reflexivity
     | gres; pose proof (Hag2 (18:reg) ltac:(notin_list)) as T; rewrite T; gres; reflexivity
     | ra_chain ]).
  Qed.

End P3.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
