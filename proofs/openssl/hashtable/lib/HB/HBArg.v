(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk StepTac ShapeAlg SpinAlg AgentLib Hoare RefMemcpyLib RefLayout ArgvEnv StartupAux FileSim
  AsanAcct AsanAcctShape HBMemcpyBase HBMemcpy HBMemchr SumsLib RtStrlen HBStrlen.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore CxPlan CxPlanSound HBPlanImage HBAtable AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxAcctNoLazy HBStdioDefs HBStdioWriteR.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ArgLoops AsanNodesArg CxNodesArgSound CxNodesEmitSound CxNodesFactSound.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import DietTac.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS. Import AN.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Fixpoint noblob (e : expr) : bool :=
  match e with
  | EBlob _ _ _ _ => false
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => noblob a && noblob b
  | EExt _ _ _ a => noblob a
  | _ => true
  end.

Lemma edenot_ev_only : forall E E' b e,
  expr_vars_lt b e = true -> noblob e = true -> (forall n, (n < b)%nat -> ev E n = ev E' n) -> edenot E e = edenot E' e.
Proof.
  intros E E' b e. induction e; intros Hv Hb Hag; cbn [edenot]; cbn [expr_vars_lt noblob] in Hv, Hb; try reflexivity.
  - apply Hag. apply Nat.ltb_lt. exact Hv.
  - apply andb_prop in Hv as [H1 H2]. apply andb_prop in Hb as [B1 B2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_prop in Hv as [H1 H2]. apply andb_prop in Hb as [B1 B2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_prop in Hv as [H1 H2]. apply andb_prop in Hb as [B1 B2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_prop in Hv as [H1 H2]. apply andb_prop in Hb as [B1 B2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - rewrite IHe by assumption. reflexivity.
  - discriminate.
Qed.

Lemma total_firstn1 : forall (l : list (list byte)), (0 < length l)%nat ->
  total_arg_bytes_nat (firstn 1 l) = (length (nth 0 l []) + 1)%nat.
Proof. intros [|a r] H; [cbn in H; lia|]. cbn [firstn nth]. rewrite total_arg_bytes_cons. change (total_arg_bytes_nat (firstn 0 r)) with 0%nat. lia. Qed.

Definition idx1 (i : nat) : nat := match i with O => 0%nat | _ => 1%nat end.

#[local] Ltac in_list := cbn [In]; repeat (first [left; (reflexivity || (apply bv_eq; reflexivity)) | right]).
(* [comment removed for export] *)
#[local] Ltac kept_in_list Hin :=
  cbn [In] in Hin;
  repeat (destruct Hin as [<-|Hin]; [in_list|]); destruct Hin.

Section AsanInst.
  Variables (sp brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InStreams).
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable hw : word.           (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk HASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Hypothesis Hfit : entry_stack_fits sp argv envp.   (* [comment removed for export] *)
  Variable FS0 : Fs.Fs.

  Let bsb := build_stack_bytes HAPH sp argv envp uid hw rdraw.
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let argv0 := nth 0 argv [].
  Let argv1 := nth 1 argv [].
  Let L0 := Z.of_nat (length argv0).
  Let L1 := Z.of_nat (length argv1).
  Let W := (Z.of_nat (length bsb) - 16 - (8 * argc + 8 * envc + 184)) / 8.
  Let STR0 := usp + 8 * argc + 8 * envc + 184.
  Let TOP := STR0 + 8 * W.

  (* [comment removed for export] *)
  Definition SINV1 (E : env) (M : word -> option byte) : Prop :=
    SINV0 HAPH sp rdraw brk0 argv envp uid hw E M /\ eb E 1%nat = argv0 /\ eb E 2%nat = argv1.

  Lemma SINV1_frame : forall E M M', (forall a, argH0 HAPH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV1 E M -> SINV1 E M'.
  Proof. intros E M M' Hf (H0 & H1 & H2). split; [|auto]. eapply SINV0_frame; diet_eassumption. Qed.

  Lemma SINV1_agree : forall E E' M, env_agree NX0 E E' -> SINV1 E M -> SINV1 E' M.
  Proof.
    intros E E' M Hag (H0 & H1 & H2). pose proof Hag as [_ Heb]. split; [|rewrite <- Heb; auto].
    eapply SINV0_agree; diet_eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma len_av : 1 <= argc <= 1024. Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  Lemma len_ev : 0 <= envc <= 256. Proof. unfold envc. destruct Hve as [H _]. lia. Qed.
  Lemma usp_lo : 0x7fff80000000 <= usp. Proof. unfold usp. destruct Hsp as [H _]. exact H. Qed.
  Lemma usp_al : usp mod 16 = 0. Proof. unfold usp. destruct Hsp as (_ & _ & H). exact H. Qed.
  Lemma L0_le : L0 <= 131071.
  Proof. unfold L0, argv0. apply (valid_argv_str_len argv 0 Hva). destruct Hva as [H _]. lia. Qed.
  Lemma L1_le : L1 <= 131071.
  Proof.
    unfold L1, argv1. destruct (Nat.lt_ge_cases 1 (length argv)) as [Hl|Hl].
    - apply (valid_argv_str_len argv 1 Hva Hl).
    - rewrite nth_overflow by lia. cbn. lia.
  Qed.

  Lemma W_facts : 0 <= W /\ 8 * W = Z.of_nat (length bsb) - 16 - (8 * argc + 8 * envc + 184).
  Proof. pose proof (W_range HAPH sp rdraw argv envp uid hw Hva Hve) as (W1 & W2 & W3). unfold W, bsb, argc, envc. split; [exact W1 | exact W2]. Qed.

  Lemma TOP_eq : TOP = usp + Z.of_nat (length bsb) - 16.
  Proof. pose proof W_facts as [W1 W2]. unfold TOP, STR0. lia. Qed.

  (* [comment removed for export] *)
  Lemma strings_fit : Z.of_nat (total_arg_bytes_nat argv) <= 8 * W.
  Proof.
    pose proof W_facts as [W1 W2]. rewrite W2.
    pose proof (length_bsb_eq HAPH sp rdraw argv envp uid hw) as LB. fold bsb in LB. rewrite LB.
    unfold stack_image_size, argc, envc. cbv zeta. rewrite !total_arg_bytes_Z.
    pose proof (Z.mod_pos_bound (8 + (Z.of_nat (length argv) + 1) * 8 + (Z.of_nat (length envp) + 1) * 8 + 160
                                  + Z.of_nat (total_arg_bytes_nat argv) + Z.of_nat (total_arg_bytes_nat envp)) 8 ltac:(lia)).
    match goal with |- _ <= ?x => match x with context [((8 - ?l mod 8) mod 8)%Z] =>
      pose proof (Z.mod_pos_bound (8 - l mod 8) 8 ltac:(lia)) end end.
    lia.
  Qed.

  Lemma argv0_fit : L0 + 1 <= Z.of_nat (total_arg_bytes_nat argv).
  Proof.
    unfold L0, argv0. destruct argv as [|a0 rest]; [destruct Hva as [H _]; cbn in H; lia|].
    cbn [nth]. rewrite total_arg_bytes_cons. lia.
  Qed.

  Lemma argv01_fit : 2 <= argc -> L0 + 1 + L1 + 1 <= Z.of_nat (total_arg_bytes_nat argv).
  Proof.
    unfold L0, L1, argv0, argv1, argc. destruct argv as [|a0 [|a1 rest]]; cbn [length nth]; try lia.
    rewrite !total_arg_bytes_cons. lia.
  Qed.

  Lemma Lay_ha : 0x7fff80000000 <= usp /\ usp + 192 <= STR0 /\ STR0 + L0 + 1 <= TOP
                   /\ (2 <= argc -> STR0 + L0 + 1 + L1 + 1 <= TOP)
                   /\ TOP mod 8 = 0 /\ TOP + 16 <= 2 ^ 47 /\ L0 <= 131071 /\ L1 <= 131071 /\ 1 <= argc <= 1024.
  Proof.
    pose proof len_av. pose proof len_ev. pose proof usp_lo. pose proof usp_al. pose proof L0_le. pose proof L1_le.
    pose proof W_facts as [W1 W2]. pose proof strings_fit. pose proof argv0_fit. pose proof TOP_eq.
    pose proof (usp_fit HAPH sp rdraw argv envp uid hw Hfit) as UF. fold bsb in UF. fold usp in UF.
    unfold TOP, STR0 in *.
    repeat split; try lia.
    intros Hargc2. pose proof (argv01_fit Hargc2). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma Hnz_ha : forall i j, (j < length (ARG argv0 argv1 i))%nat -> bv_unsigned (byte_at (ARG argv0 argv1 i) j) <> 0.
  Proof.
    intros i j Hj Hz.
    assert (GEN : forall k, (k < length argv)%nat -> (j < length (nth k argv []))%nat -> bv_unsigned (byte_at (nth k argv []) j) = 0 -> False).
    { intros k Hk Hjk Hz'. apply (byte_at_nz (nth k argv []) j (valid_argv_str_nz argv k Hva Hk) Hjk).
      apply bv_eq. rewrite Hz'. reflexivity. }
    destruct i as [|i]; cbn [ARG] in Hj, Hz.
    - apply (GEN 0%nat); [destruct Hva as [H _]; lia | exact Hj | exact Hz].
    - destruct (Nat.lt_ge_cases 1 (length argv)) as [Hl|Hl].
      + apply (GEN 1%nat Hl Hj Hz).
      + unfold argv1 in Hj. rewrite nth_overflow in Hj by lia. cbn in Hj. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma argH0_high_ha : forall E (a : word), argH0 HAPH sp rdraw argv envp uid hw E a = true -> CEIL <= bv_unsigned a /\ usp <= bv_unsigned a.
  Proof. intros E a H. exact (argH0_high HAPH sp rdraw argv envp uid hw Hsp Hva E a H). Qed.

  Lemma vals_of_SINV1 : forall E M, SINV1 E M ->
    uE E e_sp0 = usp /\ uE E e_str0 = STR0 /\ edenot E (EVar V_L0) = Z_to_bv 64 L0
    /\ edenot E (EVar V_ARGC) = Z_to_bv 64 argc /\ edenot E (EVar V_L1) = Z_to_bv 64 L1
    /\ eb E 1%nat = argv0 /\ eb E 2%nat = argv1.
  Proof.
    intros E M ((Hev & Hmem) & B1 & B2).
    assert (AG : forall e, expr_vars_lt NX0 e = true -> noblob e = true -> edenot E e = edenot (E0 HAPH sp rdraw brk0 argv envp uid hw) e).
    { intros e He Hb. apply (edenot_ev_only E _ NX0 e He Hb). exact Hev. }
    pose proof (u_e_sp0 HAPH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U0.
    pose proof (u_e_str0 HAPH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U1.
    unfold uE in *. rewrite (AG e_sp0) by reflexivity. rewrite (AG e_str0) by reflexivity.
    change (edenot E (EVar V_L0)) with (ev E 3%nat). change (edenot E (EVar V_ARGC)) with (ev E 1%nat).
    change (edenot E (EVar V_L1)) with (ev E 7%nat).
    rewrite (Hev 3%nat), (Hev 1%nat), (Hev 7%nat) by (unfold NX0; lia).
    repeat split; try assumption; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_of_SINV1 : forall E M (a : word), SINV1 E M -> STR0 <= bv_unsigned a < TOP -> exists b, M a = Some b.
  Proof.
    intros E M a ((Hev & Hmem) & _ & _) Ha. pose proof W_facts as [W1 W2]. pose proof TOP_eq as TE. pose proof len_av. pose proof len_ev.
    rewrite Hmem.
    2:{ unfold argH0. apply orb_true_intro. right. apply andb_true_intro. fold usp argc envc bsb. fold W.
        split; [apply Z.leb_le | apply Z.ltb_lt]; unfold STR0, TOP in Ha; lia. }
    rewrite wrap_above_sp by (unfold usp, STR0 in *; lia). unfold stack_to_mem. fold usp.
    (* [comment removed for export] *)
    unfold entry_stack_image. fold bsb. rewrite length_app, Nat2Z.inj_add.
    replace (usp <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; unfold STR0 in Ha; lia).
    replace (bv_unsigned a - usp <? Z.of_nat (length bsb) + Z.of_nat (length (entry_slack sp bsb (ed_slack rdraw)))) with true
      by (symmetry; apply Z.ltb_lt; unfold STR0 in Ha; lia).
    rewrite nth_error_app1 by (unfold STR0 in Ha; lia).
    destruct (nth_error bsb (Z.to_nat (bv_unsigned a - usp))) as [b|] eqn:Hn; [exists b; reflexivity|].
    apply nth_error_None in Hn. unfold STR0 in Ha. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cat_argv_ptr_STR : forall i, arg_ok argc i ->
    cat_argv_ptr sp argv envp (idx1 i) = Z_to_bv 64 (STR STR0 argv0 i).
  Proof.
    intros i Hi. pose proof len_av as LA. pose proof len_ev as LE.
    pose proof (usp_fit HAPH sp rdraw argv envp uid hw Hfit) as UF. fold bsb usp in UF.
    assert (Hk : (idx1 i < length argv)%nat) by (destruct i; cbn [idx1 arg_ok] in *; unfold argc in *; lia).
    rewrite (cat_argv_ptr_offset sp argv envp (idx1 i) Hk).
    unfold cat_string_base. rewrite nat_to_word_add_merge, word_add_nat. fold usp. apply f_equal.
    unfold cat_struct_size, auxv_size.
    destruct i as [|i]; cbn [idx1 STR].
    - change (total_arg_bytes_nat (firstn 0 argv)) with 0%nat. unfold STR0, argc, envc. lia.
    - rewrite total_firstn1 by lia. unfold STR0, argc, envc, argv0. lia.
  Qed.

  Lemma str_of_SINV1 : forall E M i j, SINV1 E M -> arg_ok argc i -> (j <= length (ARG argv0 argv1 i))%nat ->
    M (Z_to_bv 64 (STR STR0 argv0 i + Z.of_nat j)) = Some (byte_at (ARG argv0 argv1 i) j).
  Proof.
    intros E M i j HS Hi Hj.
    pose proof Lay_ha as LAY. pose proof (STR_range usp STR0 TOP argc argv0 argv1 LAY i Hi) as [R1 R2].
    pose proof (STR_bounds usp STR0 TOP argc argv0 argv1 LAY i) as SB.
    pose proof (STR0_le STR0 TOP argv0 argv1 i) as S0.
    unfold LEN in R2.
    destruct (rd_of_SINV1 E M (Z_to_bv 64 (STR STR0 argv0 i + Z.of_nat j)) HS) as [b Hb].
    { rewrite u64_lit; lia. }
    rewrite Hb. f_equal.
    (* [comment removed for export] *)
    destruct HS as ((Hev & Hmem) & _ & _).
    assert (Hk : (idx1 i < length argv)%nat) by (pose proof len_av; destruct i; cbn [idx1 arg_ok] in *; unfold argc in *; lia).
    assert (Harg : nth (idx1 i) argv [] = ARG argv0 argv1 i) by (destruct i; reflexivity).
    pose proof (read_argv_byte_k HAPH HASEGS sp argv envp (idx1 i) j uid hw rdraw Hk ltac:(rewrite Harg; exact Hj)
                  (lay_bsb_nw HAPH sp rdraw argv envp uid hw Hva Hve ltac:(destruct Hsp as (_ & H & _); exact H))) as RD.
    rewrite (cat_argv_ptr_STR i Hi), word_add_nat, u64_lit in RD by lia. rewrite Harg in RD. fold bsb in RD.
    rewrite <- wrap_above_sp in RD |- * || idtac.
    assert (Hm : M (Z_to_bv 64 (STR STR0 argv0 i + Z.of_nat j))
                 = stack_to_mem sp (entry_stack_image HAPH sp argv envp uid hw rdraw) (Z_to_bv 64 (STR STR0 argv0 i + Z.of_nat j))).
    { rewrite Hmem.
      2:{ pose proof W_facts as [W1 W2]. pose proof len_av. pose proof len_ev.
          unfold argH0. apply orb_true_intro. right. apply andb_true_intro. fold usp argc envc bsb. fold W.
          rewrite u64_lit by lia. split; [apply Z.leb_le | apply Z.ltb_lt]; unfold STR0, TOP in *; lia. }
      apply wrap_above_sp. rewrite u64_lit by lia. fold usp. lia. }
    rewrite Hm in Hb. cbn [rdn] in RD. rewrite Hb in RD. injection RD as RD'. unfold byte_at. exact RD'.
  Qed.

  (* [comment removed for export] *)
  Lemma Fi_all :
    fetch_word HASEGS (Z_to_bv 64 (0x1d05c4 + 0)) = Some W_istrlen_0 /\ fetch_word HASEGS (Z_to_bv 64 (0x1d05c4 + 4)) = Some W_istrlen_4 /\
    fetch_word HASEGS (Z_to_bv 64 (0x1d05c4 + 8)) = Some W_istrlen_8 /\ fetch_word HASEGS (Z_to_bv 64 (0x1d05c4 + 12)) = Some W_istrlen_12 /\
    fetch_word HASEGS (Z_to_bv 64 (0x1d05c4 + 16)) = Some W_istrlen_16 /\ fetch_word HASEGS (Z_to_bv 64 (0x1d05c4 + 20)) = Some W_istrlen_20 /\
    fetch_word HASEGS (Z_to_bv 64 (0x1d05c4 + 24)) = Some W_istrlen_24.
  Proof. exact (istrlen_code_of_code_at HASEGS ha_istrlen_entry ha_istrlen_code). Qed.
  Lemma Fi0 : fetch_word HASEGS (Z_to_bv 64 0x1d05c4) = Some W_istrlen_0. Proof. exact (proj1 Fi_all). Qed.
  Lemma Fi1 : fetch_word HASEGS (Z_to_bv 64 (0x1d05c4 + 4)) = Some W_istrlen_4. Proof. exact (proj1 (proj2 Fi_all)). Qed.
  Lemma Fi2 : fetch_word HASEGS (Z_to_bv 64 (0x1d05c4 + 8)) = Some W_istrlen_8. Proof. exact (proj1 (proj2 (proj2 Fi_all))). Qed.
  Lemma Fi3 : fetch_word HASEGS (Z_to_bv 64 (0x1d05c4 + 12)) = Some W_istrlen_12. Proof. exact (proj1 (proj2 (proj2 (proj2 Fi_all)))). Qed.
  Lemma Fi4 : fetch_word HASEGS (Z_to_bv 64 (0x1d05c4 + 16)) = Some W_istrlen_16. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 Fi_all))))). Qed.
  Lemma Fi5 : fetch_word HASEGS (Z_to_bv 64 (0x1d05c4 + 20)) = Some W_istrlen_20. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Fi_all)))))). Qed.
  Lemma Fi6 : fetch_word HASEGS (Z_to_bv 64 (0x1d05c4 + 24)) = Some W_istrlen_24. Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Fi_all)))))). Qed.

  Lemma istrlen_ecalls : is_ecall W_istrlen_0 = false /\ is_ecall W_istrlen_4 = false /\ is_ecall W_istrlen_8 = false /\ is_ecall W_istrlen_12 = false
                         /\ is_ecall W_istrlen_16 = false /\ is_ecall W_istrlen_20 = false /\ is_ecall W_istrlen_24 = false.
  Proof. repeat split; reflexivity. Qed.

  Lemma Gro_ha : img_lo HAT <= g_ro_lo (argtab_of HAT) /\ g_ro_hi (argtab_of HAT) <= img_hi HAT.
  Proof. cbn. lia. Qed.

  Lemma Gfile_ha : img_lo HAT <= g_file_lo (argtab_of HAT) /\ g_file_hi (argtab_of HAT) <= img_hi HAT
                     /\ img_lo HAT <= g_canary_got (argtab_of HAT) /\ g_canary_got (argtab_of HAT) + 8 <= img_hi HAT
                     /\ img_lo HAT <= g_canary (argtab_of HAT) /\ g_canary (argtab_of HAT) + 8 <= img_hi HAT.
  Proof. cbn. lia. Qed.

  (* [comment removed for export] *)
  Lemma memchr_ha : forall mem (s : word) (buf : list byte) (K n : Z) rom regs (ret : word),
    rdn HASEGS mem s (length buf) = Some buf ->
    (bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + Z.of_nat (length buf) ->
    bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64 ->
    0 <= K -> bv_unsigned (nth (Z.to_nat K) buf (Z_to_bv 8 0)) = 0 ->
    (forall j, (j < Z.to_nat K)%nat -> bv_unsigned (nth j buf (Z_to_bv 8 0)) <> 0) ->
    K + 8 <= n -> n < 2 ^ 64 ->
    (forall i, g_ro_lo (argtab_of HAT) <= i < g_ro_hi (argtab_of HAT) -> mem (Z_to_bv 64 i) = None) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 10%bv = s -> getr regs 11%bv = Z_to_bv 64 0 -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps HASEGS (mkst regs (Z_to_bv 64 (g_memchr (argtab_of HAT))) mem rom) (mkst regs' ret mem rom)
      /\ kept_ok regs regs' /\ getr regs' 10%bv = Z_to_bv 64 (bv_unsigned s + K).
  Proof.
    intros mem s buf K n rom regs ret Hbuf Hwin Hnw HK0 Hz Hnzj HKn Hn64 Hro Hret H1 H10 H11 H12.
    assert (HOK : mchrH mem s buf K n) by (constructor; try assumption; exact Hro).
    destruct (ref_memchr0 mem s buf K n rom regs ret HOK Hret H1 H10 H11 H12) as (regs' & Hms & Hkc & Ha0).
    exists regs'. split; [replace (Z_to_bv 64 (g_memchr (argtab_of HAT))) with (0x560d0c%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
    split; [|exact Ha0]. apply kept_regs. intros k Hin. apply Hkc. unfold callee_saved. kept_in_list Hin.
  Qed.

  (* [comment removed for export] *)
  Lemma memcpy_ha : forall mem0 (dst src : word) (n : Z) (bs : list byte) (regs : bvmap 5 word) (ret : word),
    0 <= n -> length bs = Z.to_nat n ->
    rdn HASEGS mem0 src (length bs) = Some bs ->
    store_ok HASEGS mem0 dst (length bs) = true ->
    (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst) ->
    bv_unsigned src + n < 2 ^ 64 -> bv_unsigned dst + n < 2 ^ 64 ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = dst -> getr regs 11%bv = src -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps HASEGS (mkst regs (Z_to_bv 64 (x_memcpy HAT)) mem0 (seg_rom HASEGS))
                  (mkst regs' ret (wbytes mem0 dst bs) (seg_rom HASEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = dst.
  Proof.
    intros mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
    pose proof (u64_range dst) as Hdr.
    assert (HOK : mcH mem0 dst src n bs) by (constructor; try assumption; lia).
    destruct (HBMemcpy.ref_memcpy mem0 dst src n bs (seg_rom HASEGS) HOK regs ret Hret R1 R10 R11 R12) as (regs' & Hms & Hk).
    exists regs'. split; [replace (Z_to_bv 64 (x_memcpy HAT)) with (0x560e08%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
    split; [|rewrite <- R10; apply Hk; unfold callee_kept; in_list].
    apply kept_regs. intros k Hin. apply Hk. unfold callee_kept. kept_in_list Hin.
  Qed.

  (* [comment removed for export] *)
  Lemma stdio_ha : forall (H : word -> bool) regs mem model (su f wb wp fd : Z) (s l bufp bufsz can ret : word)
         (pending extra : list byte) (K : TSet),
    H_off_segments HASEGS H -> lazy_all_hidden H model ->
    range_avoids H (Z_to_bv 64 (su - 112)) 112 -> range_avoids H (Z_to_bv 64 wb) (length pending) -> range_avoids H s (length extra) ->
    getr regs 2%bv = Z_to_bv 64 su -> getr regs 10%bv = Z_to_bv 64 f -> getr regs 11%bv = s -> getr regs 12%bv = l -> getr regs 1%bv = ret ->
    4294967296 + 112 <= su -> su <= 0x800000000000 ->
    store_ok HASEGS mem (Z_to_bv 64 (su - 112)) 112 = true ->
    g_file_lo (argtab_of HAT) <= f -> f + 232 <= g_file_hi (argtab_of HAT) ->
    rdn HASEGS mem (Z_to_bv 64 (f + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wp)) ->
    rdn HASEGS mem (Z_to_bv 64 (f + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wb)) ->
    rdn HASEGS mem (Z_to_bv 64 (f + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
    rdn HASEGS mem (Z_to_bv 64 (f + 88)) 8 = Some (word_to_le_bytes 8 bufp) ->
    rdn HASEGS mem (Z_to_bv 64 (f + 96)) 8 = Some (word_to_le_bytes 8 bufsz) ->
    rdn HASEGS mem (Z_to_bv 64 (g_canary_got (argtab_of HAT))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (g_canary (argtab_of HAT)))) ->
    rdn HASEGS mem (Z_to_bv 64 (g_canary (argtab_of HAT))) 8 = Some (word_to_le_bytes 8 can) ->
    0 < fd < 2147483648 ->
    fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
    m_halted model = None ->
    0 <= wb <= wp -> wp <= 2 ^ 47 -> wp - wb = Z.of_nat (length pending) -> bv_unsigned l = Z.of_nat (length extra) ->
    Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30 ->
    (wp <= su - 112 \/ su <= wb) -> (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s) ->
    bv_unsigned s + bv_unsigned l <= 2 ^ 47 ->
    rdn HASEGS mem (Z_to_bv 64 wb) (length pending) = Some pending -> rdn HASEGS mem s (length extra) = Some extra ->
    ret_ok ret -> K [] ->
    (forall regs' mem',
       getr regs' 10%bv = l -> getr regs' 2%bv = Z_to_bv 64 su -> getr regs' 1%bv = ret ->
       getr regs' 8%bv = getr regs 8%bv -> getr regs' 9%bv = getr regs 9%bv ->
       getr regs' 18%bv = getr regs 18%bv -> getr regs' 19%bv = getr regs 19%bv -> getr regs' 20%bv = getr regs 20%bv ->
       getr regs' 21%bv = getr regs 21%bv -> getr regs' 22%bv = getr regs 22%bv -> getr regs' 23%bv = getr regs 23%bv ->
       getr regs' 24%bv = getr regs 24%bv -> getr regs' 25%bv = getr regs 25%bv -> getr regs' 26%bv = getr regs 26%bv ->
       getr regs' 27%bv = getr regs 27%bv -> getr regs' 3%bv = getr regs 3%bv -> getr regs' 4%bv = getr regs 4%bv ->
       (forall x : word, ~ (su - 112 <= bv_unsigned x < su) -> ~ (f + 32 <= bv_unsigned x < f + 48) ->
                          ~ (f + 56 <= bv_unsigned x < f + 64) -> mem' x = mem x) ->
       mem_grows mem mem' ->
       rdn HASEGS mem' (Z_to_bv 64 (f + 32)) 8 = Some (word_to_le_bytes 8 (v_add bufp bufsz)) ->
       rdn HASEGS mem' (Z_to_bv 64 (f + 40)) 8 = Some (word_to_le_bytes 8 bufp) ->
       rdn HASEGS mem' (Z_to_bv 64 (f + 56)) 8 = Some (word_to_le_bytes 8 bufp) ->
       crz HASEGS (mkCfg (mkst regs' ret mem' (seg_rom HASEGS)) model) K) ->
    crz HASEGS (mkCfg (mkst regs (Z_to_bv 64 (g_stdio_write (argtab_of HAT))) mem (seg_rom HASEGS)) model)
             (t_emit (map (WriteEv (Z_to_bv 64 fd)) (pending ++ extra)) K).
  Proof.
    intros H regs mem model su f wb wp fd s l bufp bufsz can ret pending extra K
           HH HL AVF AVP AVE Hsp' Ha0 Ha1 Ha2 Hra SUlo SUhi SOK0 Flo Fhi Fwp Fwb Ffd Fbuf Fbsz C1 C2 FD Hfd Hh WBP WPhi
           LENP LENE M30 DISJP DISJE SNW RDP RDE Hret HKnil HK.
    replace (Z_to_bv 64 (g_stdio_write (argtab_of HAT))) with (0x55b4a8%bv : word) by (apply bv_eq; reflexivity).
    apply (ha_stdio_write_s H regs mem model su f wb wp fd s l bufp bufsz can ret pending extra K); try assumption; try (cbn in *; lia).
    - constructor; assumption.
    - split; [exact C1 | exact C2].
    - intros regs' mem' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST.
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      apply (HK regs' mem'); assumption.
  Qed.

  (* [comment removed for export] *)
  Variable SV : env -> (word -> option byte) -> Prop.
  Hypothesis SV_to1 : forall E M, SV E M -> SINV1 E M.
  Hypothesis SV_frame : forall E M M', (forall a, argH0 HAPH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SV E M -> SV E M'.
  Hypothesis SV_agree : forall E E' M, env_agree NX0 E E' -> SV E M -> SV E' M.
  #[local] Notation AH := (argH0 HAPH sp rdraw argv envp uid hw).

  Lemma vals_of_SV : forall E M, SV E M ->
    uE E e_sp0 = usp /\ uE E e_str0 = STR0 /\ edenot E (EVar V_L0) = Z_to_bv 64 L0
    /\ edenot E (EVar V_ARGC) = Z_to_bv 64 argc /\ edenot E (EVar V_L1) = Z_to_bv 64 L1
    /\ eb E 1%nat = argv0 /\ eb E 2%nat = argv1.
  Proof. intros E M H. exact (vals_of_SINV1 E M (SV_to1 E M H)). Qed.
  Lemma rd_of_SV : forall E M (a : word), SV E M -> STR0 <= bv_unsigned a < TOP -> exists b, M a = Some b.
  Proof. intros E M a H. exact (rd_of_SINV1 E M a (SV_to1 E M H)). Qed.
  Lemma str_of_SV : forall E M i j, SV E M -> arg_ok argc i -> (j <= length (ARG argv0 argv1 i))%nat ->
    M (Z_to_bv 64 (STR STR0 argv0 i + Z.of_nat j)) = Some (byte_at (ARG argv0 argv1 i) j).
  Proof. intros E M i j H. exact (str_of_SINV1 E M i j (SV_to1 E M H)). Qed.

  (* [comment removed for export] *)
  #[local] Notation NXS := (NX0_spw).

  Theorem ha_ext_sound : ext_stmt HASEGS HAT NX0 LIMIT (xn HASEGS HAT NX0) SV AH usp FS0.
  Proof.
    intros id args.
    pose proof Lay_ha as LAY. pose proof istrlen_ecalls as EC.
    destruct id as [|[|[|[|[|[|[|[|id]]]]]]]]; cbn [xn].
    - eapply (xn_sound_argstrlen HASEGS HAT NX0 LIMIT SV AH FS0 hat_segs_wx hat_in_hull hat_hull_ok usp SV_frame
               W_istrlen_0 W_istrlen_4 W_istrlen_8 W_istrlen_12 W_istrlen_16 W_istrlen_20 W_istrlen_24);
        [cbn; lia | exact Fi0 | exact Fi1 | exact Fi2 | exact Fi3 | exact Fi4 | exact Fi5 | exact Fi6
        | exact EC | exact D_istrlen_0 | exact D_istrlen_4 | exact D_istrlen_8 | exact D_istrlen_12 | exact D_istrlen_16 | exact D_istrlen_20 | exact D_istrlen_24
        | exact LAY | exact Hnz_ha | exact vals_of_SV | exact str_of_SV | reflexivity ].
    - eapply (xn_sound_argmemchr HASEGS HAT NX0 LIMIT SV AH FS0 hat_segs_wx hat_in_hull hat_hull_ok usp argH0_high_ha NXS
               (argH0_agree HAPH sp rdraw argv envp uid hw) SV_frame SV_agree);
        [exact LAY | exact Hnz_ha | exact vals_of_SV | exact rd_of_SV | exact str_of_SV | reflexivity | exact Gro_ha | exact memchr_ha].
    - eapply (xn_sound_argnul HASEGS HAT NX0 LIMIT SV AH FS0 hat_segs_wx hat_in_hull hat_hull_ok usp SV_frame);
        [exact LAY | exact vals_of_SV | exact str_of_SV | reflexivity].
    - eapply (xn_sound_memcpyarg HASEGS HAT NX0 LIMIT SV AH FS0 hat_segs_wx hat_in_hull hat_hull_ok usp argH0_high_ha NXS
               (argH0_agree HAPH sp rdraw argv envp uid hw) SV_frame SV_agree);
        [exact LAY | exact vals_of_SV | exact str_of_SV | reflexivity | exact memcpy_ha].
    - intros cs cs' E R FULL model T _ _ Hn _. discriminate Hn.
    - apply xn_sound_reldiff.
    - apply xn_sound_zerocover.
    - apply xn_sound_srlbound.
    - intros cs cs' E R FULL model T _ _ Hn _. discriminate Hn.
  Qed.

  Theorem ha_emit_sound : emit_stmt' HASEGS HAT NX0 LIMIT SV AH FS0 usp.
  Proof.
    pose proof Lay_ha as LAY. pose proof istrlen_ecalls as EC.
    eapply (xe_sound HASEGS HAT NX0 LIMIT SV AH FS0 hat_in_hull hat_hull_ok usp argH0_high_ha NXS
             (argH0_agree HAPH sp rdraw argv envp uid hw) SV_frame SV_agree
             W_istrlen_0 W_istrlen_4 W_istrlen_8 W_istrlen_12 W_istrlen_16 W_istrlen_20 W_istrlen_24);
      [cbn; lia | exact EC | exact LAY | exact vals_of_SV | exact str_of_SV | reflexivity | exact Gro_ha | exact stdio_ha | exact Gfile_ha].
  Qed.

End AsanInst.

(* [comment removed for export] *)
Corollary ha_ext_sound1 : forall sp brk0 argv envp rdraw hw uid,
  valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  forall FS0, ext_stmt HASEGS HAT NX0 LIMIT (xn HASEGS HAT NX0) (SINV1 sp brk0 argv envp rdraw hw uid) (argH0 HAPH sp rdraw argv envp uid hw) (bv_unsigned sp) FS0.
Proof.
  intros sp brk0 argv envp rdraw hw uid Hsp Hva Hve Hfit FS0.
  apply (ha_ext_sound sp brk0 argv envp rdraw hw Hsp Hva Hve uid Hfit FS0 (SINV1 sp brk0 argv envp rdraw hw uid));
    [exact (fun E M H => H) | apply SINV1_frame | apply SINV1_agree].
Qed.
Corollary ha_emit_sound1 : forall sp brk0 argv envp rdraw hw uid,
  valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  forall FS0, emit_stmt HASEGS HAT NX0 LIMIT (xe HASEGS HAT NX0) (SINV1 sp brk0 argv envp rdraw hw uid) (argH0 HAPH sp rdraw argv envp uid hw) (bv_unsigned sp) FS0.
Proof.
  intros sp brk0 argv envp rdraw hw uid Hsp Hva Hve Hfit FS0.
  apply (ha_emit_sound sp brk0 argv envp rdraw hw Hsp Hva Hve uid Hfit FS0 (SINV1 sp brk0 argv envp rdraw hw uid));
    [exact (fun E M H => H) | apply SINV1_frame | apply SINV1_agree].
Qed.
