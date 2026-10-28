(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AgentLib BackingAlgebra AsanPlacement AsanCeil AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DefsK_b Ba0PlanImagesK_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HandoffBridgeK HandoffLedgerK HandoffBInvK HandoffCellsK HandoffRolesK.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0HandoffK_b Ba0ArtCellsK_b Ba0DrvEntryK_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIface HeapIfaceA HeapIfaceABx ArtBridge CatExec ArgvEnv FileSim MemSplit RefLayout MuslStrlen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition tid_chk (cs : acs) : bool :=
  match kfind_word (kn cs) (ELit 0) 0x673c58 4 with Some v => existsb (kentry_eqb (KRange v 1 4194303)) (kn cs) | None => false end.

Section EntryG.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  #[local] Abbreviation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Abbreviation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Abbreviation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  Let AH := argH0_high APH0 sp rdraw argv envp uid hw Hsp Hva.

  Variables BUDGET LENMAX KMAX : Z.
  Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
  Variable EXTRA : list (Z * Z).
  Hypothesis EXTRA_wf : A_wf EXTRA.

  Variable cs : acs.
  Hypothesis CHK0 : as0_chk cs = true.
  Hypothesis CHKD : drv_chk cs = true.
  Hypothesis BUD_le : a_eager cs + a_abytes cs + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
  Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (a_totsz cs + BUDGET)
                   + (Z.of_nat (length (segments_reserved ASEGS0) + length (a_maps cs)) + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.

  Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis HC : CSOK E cs R FULL model.

  #[local] Abbreviation A0 := (as0_A0 EXTRA cs E).
  #[local] Abbreviation Hx := (ahid A0 model).
  #[local] Abbreviation MV := (mrestrict Hx FULL).
  #[local] Abbreviation usp := (bv_unsigned sp).
  #[local] Abbreviation argc := (Z.of_nat (length argv)).
  #[local] Abbreviation envc := (Z.of_nat (length envp)).
  #[local] Abbreviation L0 := (Z.of_nat (length (nth 0 argv []))).

  Ltac LINEQ e Hn H :=
    pose proof (hb_lin ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model e HC Hn) as H;
    unfold LZ in H;
    match type of H with context [lin_of ?x] => let l := eval vm_compute in (lin_of x) in change (lin_of x) with l in H end;
    cbv [AX2SK.lden AX2SK.tden fst snd AX2SK.uE] in H; cbn [edenot] in H;
    repeat match type of H with context [bv_unsigned (ev E ?n)] => change (bv_unsigned (ev E n)) with (VZ E n) in H end;
    rewrite ?Z.add_0_r in H.

  (* [comment removed for export] *)
  Lemma g_vals : VZ E 1 = argc /\ VZ E 2 = envc /\ VZ E 3 = L0 /\ 32768 * VZ E 0 + 16 * VZ E 6 + 4096 * VZ E 10 = usp.
  Proof. eapply (ent_vals sp brk0 rdraw argv envp uid hw fs); eassumption. Qed.
  Lemma g_sp0 : uE E e_sp0 = usp.
  Proof. eapply (sp0_val sp brk0 rdraw argv envp uid hw fs); eassumption. Qed.
  Lemma g_rng : 0x7fff80000000 <= usp <= 2 ^ 47 /\ usp mod 16 = 0.
  Proof. destruct Hsp as (H1 & H2 & H3). unfold sp_window_lo, sp_window_hi in *. lia. Qed.
  Lemma g_bounds : 1 <= argc <= 1024 /\ 0 <= envc <= 256 /\ 0 <= L0 <= 131071.
  Proof.
    pose proof Hve as [Hle _]. pose proof Hva as (Hac & _ & Hfa & _).
    split; [exact Hac|]. split; [lia|]. split; [lia|].
    destruct argv as [|a l]; [cbn in Hac; lia|]. inversion Hfa as [|x l' Hx _]; subst. cbn [nth]. exact Hx.
  Qed.
  Lemma g_vis_high : forall x : word, usp - 8388608 <= bv_unsigned x -> Hx x = false.
  Proof. eapply (vis_high sp brk0 rdraw argv envp uid hw fs); eassumption. Qed.
  Lemma g_simg_top : usp + Z.of_nat (length (entry_stack_image APH0 sp argv envp uid hw rdraw)) <= 2 ^ 47
                     /\ Z.of_nat (length (build_stack_bytes APH0 sp argv envp uid hw rdraw)) <= Z.of_nat (length (entry_stack_image APH0 sp argv envp uid hw rdraw))
                     /\ (usp + Z.of_nat (length (entry_stack_image APH0 sp argv envp uid hw rdraw))) mod 4096 = 0.
  Proof. eapply (simg_top sp rdraw argv envp uid hw); eassumption. Qed.

  (* [comment removed for export] *)
  Lemma gval_spk48 : edenot E (KE_SPK (-48)) = Z_to_bv 64 (usp - 48).
  Proof.
    destruct (drv_chk_parts cs CHKD) as (_ & _ & _ & L2 & _). destruct g_vals as (_ & _ & _ & U0). pose proof g_rng.
    apply word_of_u. remember (bv_unsigned (edenot E (KE_SPK (-48)))) as x eqn:Ex. LINEQ (KE_SPK (-48)) L2 H0. rewrite <- Ex in H0. lia.
  Qed.
  Lemma gval_spk8 : edenot E (KE_SPK 8) = Z_to_bv 64 (usp + 8).
  Proof.
    destruct (drv_chk_parts cs CHKD) as (_ & _ & _ & _ & L3 & _). destruct g_vals as (_ & _ & _ & U0).
    apply word_of_u. remember (bv_unsigned (edenot E (KE_SPK 8))) as x eqn:Ex. LINEQ (KE_SPK 8) L3 H0. rewrite <- Ex in H0. lia.
  Qed.
  Lemma gval_envp : edenot E KE_ENVP = Z_to_bv 64 (usp + 16 + 8 * argc).
  Proof.
    destruct (drv_chk_parts cs CHKD) as (_ & _ & _ & _ & _ & L4 & _). destruct g_vals as (U1 & _ & _ & U0).
    apply word_of_u. remember (bv_unsigned (edenot E KE_ENVP)) as x eqn:Ex. LINEQ KE_ENVP L4 H0. rewrite <- Ex in H0. lia.
  Qed.
  Lemma gval_p0 : edenot E KE_P0 = Z_to_bv 64 (usp + 8 * argc + 8 * envc + 184).
  Proof.
    destruct (drv_chk_parts cs CHKD) as (_ & _ & _ & _ & _ & _ & L5 & _). destruct g_vals as (U1 & U2 & _ & U0).
    apply word_of_u. remember (bv_unsigned (edenot E KE_P0)) as x eqn:Ex. LINEQ KE_P0 L5 H0. rewrite <- Ex in H0. lia.
  Qed.
  Lemma gval_argc : edenot E (EVar 1) = Z_to_bv 64 argc.
  Proof. destruct g_vals as (U1 & _). apply word_of_u. exact U1. Qed.

  (* [comment removed for export] *)
  Definition DRV_REGVG : list (Z * Z) :=
    [(1, 0x1180b0); (2, usp - 48); (3, 0x10800); (4, 0x673d00); (8, usp + 8); (9, argc); (10, argc); (11, usp + 8);
     (12, usp + 16 + 8 * argc); (18, 0xa7b04); (19, usp + 16 + 8 * argc); (20, 0); (21, 0); (22, 0); (23, 0); (24, 0); (25, 0); (26, 0); (27, 0)].

  Lemma g_reg : forall r e, In (r, e) DRV_REGS -> getr R (Z_to_bv 5 r) = edenot E e.
  Proof. eapply (ent_reg sp brk0 rdraw argv envp uid hw fs); eassumption. Qed.

  Theorem entg_regs : forall r v, In (r, v) DRV_REGVG -> getr R (Z_to_bv 5 r) = Z_to_bv 64 v.
  Proof.
    intros r v Hin. unfold DRV_REGVG in Hin.
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 1 (ELit 0x1180b0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 2 (KE_SPK (-48))) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_spk48|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 3 (ELit 0x10800)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 4 (ELit 0x673d00)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 8 (KE_SPK 8)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_spk8|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 9 (EVar 1)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_argc|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 10 (EVar 1)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_argc|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 11 (KE_SPK 8)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_spk8|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 12 (KE_ENVP)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_envp|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 18 (ELit 0xa7b04)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 19 (KE_ENVP)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); exact gval_envp|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 20 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 21 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 22 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 23 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 24 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 25 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 26 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin as [Hin|Hin]; [injection Hin as <- <-; rewrite (g_reg 27 (ELit 0)) by (unfold DRV_REGS; cbn [In]; repeat (first [left; reflexivity | right])); reflexivity|].
    destruct Hin.
  Qed.

  (* [comment removed for export] *)
  Lemma g_stkword : forall off v, kfind_word (kn cs) e_sp0 off 8 = Some v ->
    rdn ASEGS0 MV (Z_to_bv 64 (usp + off)) 8 = Some (word_to_le_bytes 8 (edenot E v)).
  Proof. eapply (ent_stkword sp brk0 rdraw argv envp uid hw fs); eassumption. Qed.

  (* [comment removed for export] *)
  Theorem entg_stack_words :
    rdn ASEGS0 MV (Z_to_bv 64 usp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 argc))
    /\ rdn ASEGS0 MV (Z_to_bv 64 (usp + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp + 8 * argc + 8 * envc + 184))).
  Proof.
    destruct (drv_chk_parts cs CHKD) as (_ & _ & _ & _ & _ & _ & _ & _ & K0 & K8 & _).
    pose proof (g_stkword 0 _ K0) as H0. pose proof (g_stkword 8 _ K8) as H8.
    rewrite Z.add_0_r, gval_argc in H0. rewrite gval_p0 in H8. auto.
  Qed.

  Lemma wsb_eqG : 8 * Wsb APH0 sp rdraw argv envp uid hw
                  = Z.of_nat (length (build_stack_bytes APH0 sp argv envp uid hw rdraw)) - 16 - (8 * argc + 8 * envc + 184).
  Proof.
    destruct (bsb_ge APH0 sp rdraw argv envp uid hw) as [_ Hm]. unfold Wsb.
    set (n := Z.of_nat (length (build_stack_bytes APH0 sp argv envp uid hw rdraw)) - 16 - (8 * argc + 8 * envc + 184)) in *.
    pose proof (Z.div_mod n 8 ltac:(lia)) as D. rewrite Hm in D. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem entg_strblock : forall x : word,
    usp + 8 * argc + 8 * envc + 184 <= bv_unsigned x < usp + Z.of_nat (length (build_stack_bytes APH0 sp argv envp uid hw rdraw)) - 16 ->
    MV x = wrap_mem APH0 sp argv envp uid hw rdraw x.
  Proof.
    intros x Hxr. pose proof g_rng as SR. pose proof g_bounds as GB. unfold mrestrict. rewrite (g_vis_high x ltac:(lia)).
    apply (hbi_argblock ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs E cs R FULL model HC).
    rewrite hbi_argH. rewrite g_sp0. pose proof wsb_eqG as W.
    apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. left. apply orb_true_iff. right.
    apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
  Qed.

  (* [comment removed for export] *)
  Theorem entg_str0 :
    rdn ASEGS0 MV (cat_argv_ptr sp argv envp 0) (length (nth 0 argv []) + 1) = Some (nth 0 argv [] ++ [Z_to_bv 8 0])
    /\ bv_unsigned (cat_argv_ptr sp argv envp 0) = usp + 8 * argc + 8 * envc + 184.
  Proof.
    pose proof g_rng as SR. pose proof g_bounds as GB.
    assert (Hk' : (0 < length argv)%nat) by lia.
    pose proof (u_cat_argv_ptr APH0 sp rdraw argv envp uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat Hk') as Hu.
    assert (CS : Z.of_nat (cat_struct_size argv envp) = 8 * argc + 8 * envc + 184).
    { unfold cat_struct_size, auxv_size. lia. }
    pose proof (bsb_len_lower APH0 sp argv envp uid hw rdraw) as Hlow.
    pose proof (total_arg_bytes_firstn_le 1%nat argv) as Hmono.
    pose proof (total_arg_bytes_firstn_S argv 0%nat Hk') as Hstep.
    pose proof (bsb_nw APH0 sp argv envp uid hw rdraw Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
    assert (T0 : total_arg_bytes_nat (firstn 0 argv) = 0%nat) by reflexivity. rewrite T0 in Hu, Hstep.
    split; [|rewrite Hu; lia].
    rewrite <- (read_argv_cstr_k APH0 ASEGS0 sp argv envp 0%nat uid hw rdraw Hk' Hnw).
    rewrite <- (rdn_wmem_stack ASEGS0 APH0 sp argv envp uid hw rdraw) by lia.
    apply rdn_ext; [lia|]. intros x Hxr. unfold wmem. apply entg_strblock. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem entg_str0_hi : bv_unsigned (cat_argv_ptr sp argv envp 0) + L0 + 1 + 16 <= 2 ^ 47.
  Proof.
    pose proof g_rng as SR. pose proof g_bounds as GB.
    assert (Hk' : (0 < length argv)%nat) by lia.
    pose proof (u_cat_argv_ptr APH0 sp rdraw argv envp uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat Hk') as Hu.
    pose proof (bsb_len_lower APH0 sp argv envp uid hw rdraw) as Hlow.
    pose proof (total_arg_bytes_firstn_le 1%nat argv) as Hmono.
    pose proof (total_arg_bytes_firstn_S argv 0%nat Hk') as Hstep.
    assert (T0 : total_arg_bytes_nat (firstn 0 argv) = 0%nat) by reflexivity. rewrite T0 in Hu, Hstep.
    destruct g_simg_top as (T1 & T2 & _). rewrite Hu. lia.
  Qed.

  (* [comment removed for export] *)
  Hypothesis CHKS : stk_chk cs = true.
  #[local] Abbreviation SIMGx := (entry_stack_image APH0 sp argv envp uid hw rdraw).
  #[local] Abbreviation LBx := (Z.of_nat (length (build_stack_bytes APH0 sp argv envp uid hw rdraw))).

  Lemma g_argH_defined : forall x : word, usp <= bv_unsigned x < usp + Z.of_nat (length SIMGx) -> argH E x = true -> FULL x <> None.
  Proof. eapply (argH_defined sp brk0 rdraw argv envp uid hw fs); eassumption. Qed.

  Theorem entg_stack_defined : forall i, 0 <= i < Z.of_nat (length SIMGx) -> FULL (Z_to_bv 64 (usp + i)) <> None.
  Proof.
    intros i Hi. pose proof g_rng as SR. pose proof g_bounds as GB. destruct g_simg_top as (T1 & T2 & _).
    destruct (stk_chk_parts cs CHKS) as (CA & LA & LR & (bi & CB)).
    destruct (drv_chk_parts cs CHKD) as (_ & _ & L1 & _ & _ & _ & _ & _ & K0 & K8 & K16 & _).
    destruct (hbi_vals ASEGS0 ASAN0 APH0 sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit E cs R FULL model HC)
      as (_ & _ & _ & _ & _ & _ & U4 & _).
    destruct g_vals as (V1 & V2 & _ & V0).
    pose proof wsb_eqG as WE.
    destruct (bsb_ge APH0 sp rdraw argv envp uid hw) as [BG _].
    assert (UX : bv_unsigned (Z_to_bv 64 (usp + i)) = usp + i) by (apply u_small; lia).
    (* [comment removed for export] *)
    assert (KW : forall b off v d, kfind_word (kn cs) b off 8 = Some v -> lin_nowrapR (kn cs) b = true ->
                 (flat E (SA b off) 8 -> estart E (SA b off) = usp + d) -> d <= i < d + 8 -> FULL (Z_to_bv 64 (usp + i)) <> None).
    { intros b off v d Hk Hl Hst Hd.
      destruct (hb_word_at ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model b off 8 v HC Hk)
        as (_ & Hf & Hr & _).
      rewrite (hb_adenot E _ _ Hf), (Hst Hf) in Hr.
      apply (rdn_bytes_some ASEGS0 ASAN0 asan0_in_hull FULL _ 8 _ Hr).
      - rewrite UX, u_small by lia. change (Z.of_nat 8) with 8. lia.
      - rewrite UX. unfold in_hull. cbn [img_lo img_hi ASAN0]. apply andb_false_iff. right. apply Z.ltb_ge. lia. }
    destruct (Z_lt_le_dec i 24) as [C1|C1].
    { (* [comment removed for export] *)
      assert (ST : forall off, flat E (SA e_sp0 off) 8 -> estart E (SA e_sp0 off) = usp + off)
        by (intros off _; rewrite hb_estart; fold (uE E e_sp0); rewrite g_sp0; reflexivity).
      destruct (Z_lt_le_dec i 8); [apply (KW e_sp0 0 _ 0 K0 L1 (ST 0)); lia|].
      destruct (Z_lt_le_dec i 16); [apply (KW e_sp0 8 _ 8 K8 L1 (ST 8)); lia | apply (KW e_sp0 16 _ 16 K16 L1 (ST 16)); lia]. }
    destruct (Z_lt_le_dec i (8 * argc + 8 * envc + 24)) as [C2|C2].
    { apply g_argH_defined; [rewrite UX; lia|]. rewrite hbi_argH, g_sp0, UX.
      apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. left. apply orb_true_iff. left.
      apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
    destruct (Z_lt_le_dec i (8 * argc + 8 * envc + 184)) as [C3|C3].
    { (* [comment removed for export] *)
      assert (UA : uE E KE_AUX = usp + 8 * argc + 8 * envc).
      { unfold uE. remember (bv_unsigned (edenot E KE_AUX)) as s0 eqn:Es. LINEQ KE_AUX LA H. rewrite <- Es in H. lia. }
      assert (ST : forall off, flat E (SA KE_AUX off) 8 -> estart E (SA KE_AUX off) = usp + (8 * argc + 8 * envc + off))
        by (intros off _; rewrite hb_estart; fold (uE E KE_AUX); rewrite UA; ring).
      set (k := (i - (8 * argc + 8 * envc)) / 8).
      assert (Hk : i - (8 * argc + 8 * envc) = 8 * k + (i - (8 * argc + 8 * envc)) mod 8) by (apply Z.div_mod; lia).
      pose proof (Z.mod_pos_bound (i - (8 * argc + 8 * envc)) 8 ltac:(lia)) as Hm.
      assert (Hin : In (8 * k) AUX_OFFS).
      { assert (Hk3 : 3 <= k < 23) by lia. unfold AUX_OFFS.
        assert (Hc : k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15
                     \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22) by lia.
        repeat (destruct Hc as [->|Hc]; [cbn [In]; tauto|]). subst k. rewrite Hc. cbn [In]. tauto. }
      destruct (CA _ Hin) as (v & Hv).
      apply (KW KE_AUX (8 * k) v (8 * argc + 8 * envc + 8 * k) Hv LA (ST (8 * k))). lia. }
    destruct (Z_lt_le_dec i (LBx - 16)) as [C4|C4].
    { apply g_argH_defined; [rewrite UX; lia|]. rewrite hbi_argH, g_sp0, UX.
      apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. left. apply orb_true_iff. right.
      apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
    destruct (Z_lt_le_dec i LBx) as [C5|C5].
    { (* [comment removed for export] *)
      assert (UR : uE E KE_RND = usp + 8 * argc + 8 * envc + 8 * Wsb APH0 sp rdraw argv envp uid hw).
      { unfold uE. remember (bv_unsigned (edenot E KE_RND)) as s0 eqn:Es. LINEQ KE_RND LR H. rewrite <- Es in H. rewrite U4 in H. lia. }
      pose proof (hb_kn ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC (kfind_blob16_In _ _ _ _ CB)) as (Hf & _ & Hb).
      assert (EL : elenZ E (ELit 16) = 16) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
      rewrite EL in Hb. rewrite hb_estart in Hb. fold (uE E KE_RND) in Hb. rewrite UR in Hb.
      specialize (Hb (i - (LBx - 16)) ltac:(lia)).
      replace (usp + 8 * argc + 8 * envc + 8 * Wsb APH0 sp rdraw argv envp uid hw + 184 + (i - (LBx - 16))) with (usp + i) in Hb by lia.
      exact (mr_defined sp rdraw argv envp uid hw cs E FULL model _ _ Hb). }
    apply g_argH_defined; [rewrite UX; lia|]. rewrite hbi_argH, g_sp0, UX.
    apply andb_true_intro. split; [apply Z.leb_le; lia|]. apply orb_true_iff. right.
    apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
  Qed.

  (* [comment removed for export] *)
  Corollary entg_stack_defined_top : forall top, top mod 4096 = 0 -> top <= usp + 4096 ->
    forall i, 0 <= i < top - usp -> FULL (Z_to_bv 64 (usp + i)) <> None.
  Proof.
    intros top Hm Hle i Hi. apply entg_stack_defined. destruct g_simg_top as (T1 & T2 & T3).
    pose proof (bsb_ge APH0 sp rdraw argv envp uid hw) as [G _]. pose proof g_bounds as GB.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  (* [comment removed for export] *)
  Theorem entg_str0_defined :
    forall i, 0 <= i < L0 + 1 + 16 -> FULL (Z_to_bv 64 (bv_unsigned (cat_argv_ptr sp argv envp 0) + i)) <> None.
  Proof.
    intros i Hi. pose proof g_rng as SR. pose proof g_bounds as GB.
    assert (Hk' : (0 < length argv)%nat) by lia.
    pose proof (u_cat_argv_ptr APH0 sp rdraw argv envp uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat Hk') as Hu.
    pose proof (bsb_len_lower APH0 sp argv envp uid hw rdraw) as Hlow.
    pose proof (total_arg_bytes_firstn_le 1%nat argv) as Hmono.
    pose proof (total_arg_bytes_firstn_S argv 0%nat Hk') as Hstep.
    assert (T0 : total_arg_bytes_nat (firstn 0 argv) = 0%nat) by reflexivity. rewrite T0 in Hu, Hstep.
    destruct g_simg_top as (_ & T2 & _).
    set (q := bv_unsigned (cat_argv_ptr sp argv envp 0)) in *.
    replace (q + i) with (usp + (q - usp + i)) by ring.
    apply entg_stack_defined. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem entg_tid : tid_chk cs = true -> exists tid : word,
    1 <= bv_unsigned tid <= 4194303 /\ rdn ASEGS0 MV (Z_to_bv 64 0x673c58) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros CT. unfold tid_chk in CT.
    destruct (kfind_word (kn cs) (ELit 0) 0x673c58 4) as [v|] eqn:K2; [|discriminate].
    exists (edenot E v).
    pose proof (hb_knb ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC CT) as RG. cbn [kentry_ok] in RG.
    split; [exact RG|].
    eapply (ent_litcell sp brk0 rdraw argv envp uid hw fs); try eassumption. lia.
  Qed.
End EntryG.
