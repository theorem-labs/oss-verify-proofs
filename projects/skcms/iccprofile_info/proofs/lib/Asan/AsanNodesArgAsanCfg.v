(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec CatExec CatSim SeqExec StoreOk StepTac ShapeAlg SpinAlg AgentLib Hoare RefMemcpyLib RefLayout ArgvEnv StartupAux
  AsanAcct AsanAcctShape AsanAcctImages AsanMemcpyBase AsanMemcpy AsanMemchr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanAcctNoLazy.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import ArgLoops AsanNodesArg AsanNodesArgSoundCfg AsanNodesFactSoundCfg Arg_code_istrlen_asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import SpinAlgCfg AsanPlanSoundCfg.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import AN.
Unset Lia Cache.
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_lia_core := first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                                | Zify.zify; xlia zchecker ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
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
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variables (argv envp : list (list byte)).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variables uid hw : word.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Variable FS0 : Fs.Fs.

  Let bsb := build_stack_bytes APH sp argv envp uid hw rdraw.
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
    SINV0 APH sp rdraw brk0 argv envp uid hw E M /\ eb E 1%nat = argv0 /\ eb E 2%nat = argv1.

  Lemma SINV1_frame : forall E M M', (forall a, argH0 APH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV1 E M -> SINV1 E M'.
  Proof. intros E M M' Hf (H0 & H1 & H2). split; [|auto]. eapply SINV0_frame; eassumption. Qed.

  Lemma SINV1_agree : forall E E' M, env_agree NX0 E E' -> SINV1 E M -> SINV1 E' M.
  Proof.
    intros E E' M Hag (H0 & H1 & H2). pose proof Hag as [_ Heb]. split; [|rewrite <- Heb; auto].
    eapply SINV0_agree; eassumption.
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
  Proof. pose proof (W_range APH sp rdraw argv envp uid hw Hva Hve) as (W1 & W2 & W3). unfold W, bsb, argc, envc. split; [exact W1 | exact W2]. Qed.

  Lemma TOP_eq : TOP = usp + Z.of_nat (length bsb) - 16.
  Proof. pose proof W_facts as [W1 W2]. unfold TOP, STR0. lia. Qed.

  (* [comment removed for export] *)
  Lemma strings_fit : Z.of_nat (total_arg_bytes_nat argv) <= 8 * W.
  Proof.
    pose proof W_facts as [W1 W2]. rewrite W2.
    pose proof (length_bsb_eq APH sp rdraw argv envp uid hw) as LB. fold bsb in LB. rewrite LB.
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

  Lemma Lay_asan : 0x7fff80000000 <= usp /\ usp + 192 <= STR0 /\ STR0 + L0 + 1 <= TOP
                   /\ (2 <= argc -> STR0 + L0 + 1 + L1 + 1 <= TOP)
                   /\ TOP mod 8 = 0 /\ TOP + 16 <= 2 ^ 47 /\ L0 <= 131071 /\ L1 <= 131071 /\ 1 <= argc <= 1024.
  Proof.
    pose proof len_av. pose proof len_ev. pose proof usp_lo. pose proof usp_al. pose proof L0_le. pose proof L1_le.
    pose proof W_facts as [W1 W2]. pose proof strings_fit. pose proof argv0_fit. pose proof TOP_eq.
    pose proof (usp_fit APH sp rdraw argv envp uid hw Hfit) as UF. fold bsb in UF. fold usp in UF.
    unfold TOP, STR0 in *.
    repeat split; try lia.
    intros Hargc2. pose proof (argv01_fit Hargc2). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma Hnz_asan : forall i j, (j < length (ARG argv0 argv1 i))%nat -> bv_unsigned (byte_at (ARG argv0 argv1 i) j) <> 0.
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
  Lemma argH0_high_asan : forall E (a : word), argH0 APH sp rdraw argv envp uid hw E a = true -> CEIL <= bv_unsigned a.
  Proof. intros E a H. exact (argH0_high APH sp rdraw argv envp uid hw Hsp Hva E a H). Qed.

  Lemma vals_of_SINV1 : forall E M, SINV1 E M ->
    uE E e_sp0 = usp /\ uE E e_str0 = STR0 /\ edenot E (EVar V_L0) = Z_to_bv 64 L0
    /\ edenot E (EVar V_ARGC) = Z_to_bv 64 argc /\ edenot E (EVar V_L1) = Z_to_bv 64 L1
    /\ eb E 1%nat = argv0 /\ eb E 2%nat = argv1.
  Proof.
    intros E M ((Hev & Hmem) & B1 & B2).
    assert (AG : forall e, expr_vars_lt NX0 e = true -> noblob e = true -> edenot E e = edenot (E0 APH sp rdraw brk0 argv envp uid hw) e).
    { intros e He Hb. apply (edenot_ev_only E _ NX0 e He Hb). exact Hev. }
    pose proof (u_e_sp0 APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U0.
    pose proof (u_e_str0 APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U1.
    unfold uE in *. rewrite (AG e_sp0) by reflexivity. rewrite (AG e_str0) by reflexivity.
    change (edenot E (EVar V_L0)) with (ev E 3%nat). change (edenot E (EVar V_ARGC)) with (ev E 1%nat).
    change (edenot E (EVar V_L1)) with (ev E 7%nat).
    rewrite (Hev 3%nat), (Hev 1%nat), (Hev 7%nat) by (unfold NX0; lia).
    repeat split; try assumption; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma mem_str_block : forall E M (a : word), SINV1 E M -> STR0 <= bv_unsigned a < TOP ->
    M a = stack_to_mem sp (entry_stack_image APH sp argv envp uid hw rdraw) a.
  Proof.
    intros E M a ((Hev & Hmem) & _ & _) Ha. pose proof W_facts as [W1 W2]. pose proof len_av. pose proof len_ev.
    rewrite Hmem.
    2:{ unfold argH0. apply orb_true_intro. right. apply andb_true_intro. fold usp argc envc bsb. fold W.
        split; [apply Z.leb_le | apply Z.ltb_lt]; unfold STR0, TOP in Ha; lia. }
    apply wrap_above_sp. fold usp. unfold STR0 in Ha. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_of_SINV1 : forall E M (a : word), SINV1 E M -> STR0 <= bv_unsigned a < TOP -> exists b, M a = Some b.
  Proof.
    intros E M a HS Ha. pose proof W_facts as [W1 W2]. pose proof TOP_eq as TE. pose proof len_av. pose proof len_ev.
    rewrite (mem_str_block E M a HS Ha). unfold stack_to_mem, entry_stack_image. fold bsb. fold usp.
    replace (usp <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; unfold STR0 in Ha; lia).
    rewrite length_app.
    replace (bv_unsigned a - usp <? Z.of_nat (length bsb + length (entry_slack sp bsb (ed_slack rdraw))))
      with true by (symmetry; apply Z.ltb_lt; unfold STR0 in Ha; lia).
    rewrite nth_error_app1 by (unfold STR0 in Ha; lia).
    destruct (nth_error bsb (Z.to_nat (bv_unsigned a - usp))) as [b|] eqn:Hn; [exists b; reflexivity|].
    apply nth_error_None in Hn. unfold STR0 in Ha. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cat_argv_ptr_STR : forall i, arg_ok argc i ->
    cat_argv_ptr sp argv envp (idx1 i) = Z_to_bv 64 (STR STR0 argv0 i).
  Proof.
    intros i Hi. pose proof len_av as LA. pose proof len_ev as LE.
    pose proof (usp_fit APH sp rdraw argv envp uid hw Hfit) as UF. fold bsb usp in UF.
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
    pose proof Lay_asan as LAY. pose proof (STR_range usp STR0 TOP argc argv0 argv1 LAY i Hi) as [R1 R2].
    pose proof (STR_bounds usp STR0 TOP argc argv0 argv1 LAY i) as SB.
    pose proof (STR0_le STR0 TOP argv0 argv1 i) as S0.
    unfold LEN in R2.
    assert (Hk : (idx1 i < length argv)%nat) by (pose proof len_av; destruct i; cbn [idx1 arg_ok] in *; unfold argc in *; lia).
    assert (Harg : nth (idx1 i) argv [] = ARG argv0 argv1 i) by (destruct i; reflexivity).
    pose proof (read_argv_byte_k APH ASEGS sp argv envp (idx1 i) j uid hw rdraw Hk ltac:(rewrite Harg; exact Hj)
                  (lay_bsb_nw APH sp rdraw argv envp uid hw Hva Hve ltac:(destruct Hsp as (_ & H & _); exact H))) as RD.
    rewrite (cat_argv_ptr_STR i Hi), word_add_nat, u64_lit in RD by lia. rewrite Harg in RD. fold bsb in RD.
    destruct (rd_of_SINV1 E M (Z_to_bv 64 (STR STR0 argv0 i + Z.of_nat j)) HS) as [b Hb]; [rewrite u64_lit; lia|].
    rewrite Hb. f_equal.
    rewrite (mem_str_block E M _ HS) in Hb by (rewrite u64_lit; lia).
    cbn [rdn] in RD. rewrite Hb in RD. injection RD as RD'. unfold byte_at. exact RD'.
  Qed.

  (* [comment removed for export] *)
  Lemma istrlen_ecalls : is_ecall W_63514 = false /\ is_ecall W_63518 = false /\ is_ecall W_6351c = false /\ is_ecall W_63520 = false
                         /\ is_ecall W_63524 = false /\ is_ecall W_63528 = false /\ is_ecall W_6352c = false.
  Proof. repeat split; reflexivity. Qed.

  Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.   (* [comment removed for export] *)
  Lemma Gro_asan : img_lo INFO_ASAN <= g_ro_lo (argtab_of INFO_ASAN) /\ g_ro_hi (argtab_of INFO_ASAN) <= img_hi INFO_ASAN.
  Proof. cbn. lia. Qed.
  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

  Section AnyFP.
  Context {FP : PropExec.FPState}.

  (* [comment removed for export] *)
  Lemma memchr_asan : forall mem (s : word) (buf : list byte) (K n : Z) rom regs (ret : word),
    rdn ASEGS mem s (length buf) = Some buf ->
    (bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + Z.of_nat (length buf) ->
    bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64 ->
    0 <= K -> bv_unsigned (nth (Z.to_nat K) buf (Z_to_bv 8 0)) = 0 ->
    (forall j, (j < Z.to_nat K)%nat -> bv_unsigned (nth j buf (Z_to_bv 8 0)) <> 0) ->
    K + 8 <= n -> n < 2 ^ 64 ->
    (forall i, g_ro_lo (argtab_of INFO_ASAN) <= i < g_ro_hi (argtab_of INFO_ASAN) -> mem (Z_to_bv 64 i) = None) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 10%bv = s -> getr regs 11%bv = Z_to_bv 64 0 -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps ASEGS (mkst regs (Z_to_bv 64 (g_memchr (argtab_of INFO_ASAN))) mem rom) (mkst regs' ret mem rom)
      /\ kept_ok regs regs' /\ getr regs' 10%bv = Z_to_bv 64 (bv_unsigned s + K).
  Proof.
    intros mem s buf K n rom regs ret Hbuf Hwin Hnw HK0 Hz Hnzj HKn Hn64 Hro Hret H1 H10 H11 H12.
    assert (HOK : mchrH mem s buf K n) by (constructor; try assumption; exact Hro).
    destruct (ref_memchr0 mem s buf K n rom regs ret HOK Hret H1 H10 H11 H12) as (regs' & Hms & Hkc & Ha0).
    exists regs'. split; [replace (Z_to_bv 64 (g_memchr (argtab_of INFO_ASAN))) with (0x97d20%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
    split; [|exact Ha0]. apply kept_regs. intros k Hin. apply Hkc. unfold callee_saved. kept_in_list Hin.
  Qed.

  (* [comment removed for export] *)
  Lemma memcpy_asan : forall mem0 (dst src : word) (n : Z) (bs : list byte) (regs : bvmap 5 word) (ret : word),
    0 <= n -> length bs = Z.to_nat n ->
    rdn ASEGS mem0 src (length bs) = Some bs ->
    store_ok ASEGS mem0 dst (length bs) = true ->
    (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst) ->
    bv_unsigned src + n < 2 ^ 64 -> bv_unsigned dst + n < 2 ^ 64 ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = dst -> getr regs 11%bv = src -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps ASEGS (mkst regs (Z_to_bv 64 (x_memcpy INFO_ASAN)) mem0 (seg_rom ASEGS))
                  (mkst regs' ret (wbytes mem0 dst bs) (seg_rom ASEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = dst.
  Proof.
    intros mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
    pose proof (u64_range dst) as Hdr.
    assert (HOK : mcH mem0 dst src n bs) by (constructor; try assumption; lia).
    destruct (AsanMemcpy.ref_memcpy mem0 dst src n bs (seg_rom ASEGS) HOK regs ret Hret R1 R10 R11 R12) as (regs' & Hms & Hk).
    exists regs'. split; [replace (Z_to_bv 64 (x_memcpy INFO_ASAN)) with (0x97e1c%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
    split; [|rewrite <- R10; apply Hk; unfold callee_kept; in_list].
    apply kept_regs. intros k Hin. apply Hk. unfold callee_kept. kept_in_list Hin.
  Qed.

  (* [comment removed for export] *)
  Variable SV : env -> (word -> option byte) -> Prop.
  Hypothesis SV_to1 : forall E M, SV E M -> SINV1 E M.
  Hypothesis SV_frame : forall E M M', (forall a, argH0 APH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SV E M -> SV E M'.
  Hypothesis SV_agree : forall E E' M, env_agree NX0 E E' -> SV E M -> SV E' M.
  #[local] Notation AH := (argH0 APH sp rdraw argv envp uid hw).

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

  Theorem asan_ext_sound_fp : forall id args,
    APSC.node1_stmt_fp ASEGS INFO_ASAN NX0 LIMIT SV AH FS0 FP always (xn ASEGS INFO_ASAN NX0 id args).
  Proof.
    intros id args.
    pose proof Lay_asan as LAY. pose proof istrlen_ecalls as EC.
    destruct id as [|[|[|[|[|[|[|[|[|[|id]]]]]]]]]]; cbn [xn].
    - eapply (xn_sound_argstrlen ASEGS INFO_ASAN NX0 LIMIT SV AH FS0 asan_wx asan_in_hull SV_frame
               W_63514 W_63518 W_6351c W_63520 W_63524 W_63528 W_6352c);
        [cbn; lia | exact F_63514 | exact F_63518 | exact F_6351c | exact F_63520 | exact F_63524 | exact F_63528 | exact F_6352c
        | exact EC | exact D_63514 | exact D_63518 | exact D_6351c | exact D_63520 | exact D_63524 | exact D_63528 | exact D_6352c
        | exact LAY | exact Hnz_asan | exact vals_of_SV | exact str_of_SV ].
    - eapply (xn_sound_argmemchr ASEGS INFO_ASAN NX0 LIMIT SV AH FS0 asan_wx asan_in_hull asan_hull_ok argH0_high_asan
               (argH0_agree APH sp rdraw argv envp uid hw) SV_frame SV_agree NX0_sp0);
        [exact LAY | exact Hnz_asan | exact vals_of_SV | exact rd_of_SV | exact str_of_SV | exact Gro_asan | exact memchr_asan].
    - eapply (xn_sound_argnul ASEGS INFO_ASAN NX0 LIMIT SV AH FS0 asan_wx asan_in_hull SV_frame);
        [exact LAY | exact vals_of_SV | exact str_of_SV].
    - eapply (xn_sound_memcpyarg ASEGS INFO_ASAN NX0 LIMIT SV AH FS0 asan_wx asan_in_hull asan_hull_ok argH0_high_asan
               (argH0_agree APH sp rdraw argv envp uid hw) SV_frame SV_agree NX0_sp0);
        [exact LAY | exact vals_of_SV | exact str_of_SV | exact memcpy_asan].
    - intros cs cs' E R FULL model T _ _ Hn _. discriminate Hn.
    - apply xn_sound_reldiff.
    - apply xn_sound_zerocover.
    - apply xn_sound_srlbound.
    - apply xn_sound_argregion.   (* [comment removed for export] *)
    - apply xn_sound_argregion_b. (* [comment removed for export] *)
    - intros cs cs' E R FULL model T _ _ Hn _. discriminate Hn.
  Qed.
  End AnyFP.

  (* [comment removed for export] *)
  Theorem asan_ext_sound_cfg : forall (SV : env -> (word -> option byte) -> Prop) (FPS : PropExec.FPState -> Prop),
    (forall E M, SV E M -> SINV1 E M) ->
    (forall E M M', (forall a, argH0 APH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SV E M -> SV E M') ->
    (forall E E' M, env_agree NX0 E E' -> SV E M -> SV E' M) ->
    forall id args, APSC.node1_stmt_cfg ASEGS INFO_ASAN NX0 LIMIT SV (argH0 APH sp rdraw argv envp uid hw) FS0 FPS always
                                       (xn ASEGS INFO_ASAN NX0 id args).
  Proof.
    intros SV FPS H1 H2 H3 id args. apply APSC.node1_of_fp. intros FP _.
    exact (@asan_ext_sound_fp FP SV H1 H2 H3 id args).
  Qed.
End AsanInst.
