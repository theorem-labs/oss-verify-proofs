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
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk StepTac ShapeAlg SpinAlg AgentLib Hoare RefMemcpyLib RefLayout ArgvEnv StartupAux AsanAcct AsanAcctShape.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanAcctNoLazy ArgLoops AsanNodesArg AsanNodesArgSound AsanNodesEmitSound AsanNodesFactSound
  AsanMainLib ImgParams MainDefs MainAsm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import AN.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Section Specs.
  Context {fx : FPState}.
  Variable ip : imgparams.
  Definition MEMCHR_STMT : Prop := forall mem (s : word) (buf : list byte) (K n : Z) rom regs (ret : word),
    rdn (ip_segs ip) mem s (length buf) = Some buf ->
    (bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + Z.of_nat (length buf) ->
    bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64 ->
    0 <= K -> bv_unsigned (nth (Z.to_nat K) buf (Z_to_bv 8 0)) = 0 ->
    (forall j, (j < Z.to_nat K)%nat -> bv_unsigned (nth j buf (Z_to_bv 8 0)) <> 0) ->
    K + 8 <= n -> n < 2 ^ 64 ->
    (forall i, g_ro_lo (ip_G ip) <= i < g_ro_hi (ip_G ip) -> mem (Z_to_bv 64 i) = None) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 10%bv = s -> getr regs 11%bv = Z_to_bv 64 0 -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps (ip_segs ip) (mkst regs (Z_to_bv 64 (g_memchr (ip_G ip))) mem rom) (mkst regs' ret mem rom)
      /\ kept_ok regs regs' /\ getr regs' 10%bv = Z_to_bv 64 (bv_unsigned s + K).
  Definition MEMCPY_STMT : Prop := forall mem0 (dst src : word) (n : Z) (bs : list byte) (regs : bvmap 5 word) (ret : word),
    0 <= n -> length bs = Z.to_nat n ->
    rdn (ip_segs ip) mem0 src (length bs) = Some bs ->
    store_ok (ip_segs ip) mem0 dst (length bs) = true ->
    (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst) ->
    bv_unsigned src + n < 2 ^ 64 -> bv_unsigned dst + n < 2 ^ 64 ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = dst -> getr regs 11%bv = src -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps (ip_segs ip) (mkst regs (Z_to_bv 64 (x_memcpy (ip_A ip))) mem0 (seg_rom (ip_segs ip)))
                  (mkst regs' ret (wbytes mem0 dst bs) (seg_rom (ip_segs ip)))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = dst.
  Definition STDIO_STMT : Prop := forall (H : word -> bool) regs mem model (su f wb wp fd : Z) (s l bufp bufsz can ret : word)
         (pending extra : list byte) (K : TSet),
    H_off_segments (ip_segs ip) H -> lazy_all_hidden H model ->
    range_avoids H (Z_to_bv 64 (su - 112)) 112 -> range_avoids H (Z_to_bv 64 wb) (length pending) -> range_avoids H s (length extra) ->
    getr regs 2%bv = Z_to_bv 64 su -> getr regs 10%bv = Z_to_bv 64 f -> getr regs 11%bv = s -> getr regs 12%bv = l -> getr regs 1%bv = ret ->
    4294967296 + 112 <= su -> su <= 0x800000000000 ->
    store_ok (ip_segs ip) mem (Z_to_bv 64 (su - 112)) 112 = true ->
    g_file_lo (ip_G ip) <= f -> f + 232 <= g_file_hi (ip_G ip) ->
    rdn (ip_segs ip) mem (Z_to_bv 64 (f + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wp)) ->
    rdn (ip_segs ip) mem (Z_to_bv 64 (f + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wb)) ->
    rdn (ip_segs ip) mem (Z_to_bv 64 (f + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
    rdn (ip_segs ip) mem (Z_to_bv 64 (f + 88)) 8 = Some (word_to_le_bytes 8 bufp) ->
    rdn (ip_segs ip) mem (Z_to_bv 64 (f + 96)) 8 = Some (word_to_le_bytes 8 bufsz) ->
    rdn (ip_segs ip) mem (Z_to_bv 64 (g_canary_got (ip_G ip))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (g_canary (ip_G ip)))) ->
    rdn (ip_segs ip) mem (Z_to_bv 64 (g_canary (ip_G ip))) 8 = Some (word_to_le_bytes 8 can) ->
    0 < fd < 2147483648 ->
    fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
    m_halted model = None ->
    0 <= wb <= wp -> wp <= 0x800000000000 (* [comment removed for export] *) -> wp - wb = Z.of_nat (length pending) -> bv_unsigned l = Z.of_nat (length extra) ->
    Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30 ->   (* [comment removed for export] *)
    Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30 ->
    (wp <= su - 112 \/ su <= wb) -> (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s) ->
    bv_unsigned s + bv_unsigned l <= 0x800000000000 (* [comment removed for export] *) ->
    rdn (ip_segs ip) mem (Z_to_bv 64 wb) (length pending) = Some pending -> rdn (ip_segs ip) mem s (length extra) = Some extra ->
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
       rdn (ip_segs ip) mem' (Z_to_bv 64 (f + 32)) 8 = Some (word_to_le_bytes 8 (v_add bufp bufsz)) ->
       rdn (ip_segs ip) mem' (Z_to_bv 64 (f + 40)) 8 = Some (word_to_le_bytes 8 bufp) ->
       rdn (ip_segs ip) mem' (Z_to_bv 64 (f + 56)) 8 = Some (word_to_le_bytes 8 bufp) ->
       srealizes (ip_segs ip) (mkCfg (mkst regs' ret mem' (seg_rom (ip_segs ip))) model) K) ->
    srealizes (ip_segs ip) (mkCfg (mkst regs (Z_to_bv 64 (g_stdio_write (ip_G ip))) mem (seg_rom (ip_segs ip))) model)
             (t_emit (map (WriteEv (Z_to_bv 64 fd)) (pending ++ extra)) K).
End Specs.

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

Section ArgInst.
  Context {fx : FPState}.
  (* [comment removed for export] *)
  Variable ip : imgparams.
  Variable ph : PhdrInfo.
  #[local] Notation SEGS := (ip_segs ip).
  #[local] Notation A := (ip_A ip).
  #[local] Notation G := (ip_G ip).
  #[local] Notation LIM := (ip_limit ip).
  #[local] Notation APH := ph.
  #[local] Notation ASEGS := (ip_segs ip).
  Hypothesis WX : wx_segs_nowrap SEGS.
  Hypothesis IN_HULL : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_OK : hull_ok A.
  (* [comment removed for export] *)
  Hypothesis Gro : img_lo A <= g_ro_lo G /\ g_ro_hi G <= img_hi A.
  Hypothesis Gfile : img_lo A <= g_file_lo G /\ g_file_hi G <= img_hi A /\ img_lo A <= g_canary_got G /\ g_canary_got G + 8 <= img_hi A
                     /\ img_lo A <= g_canary G /\ g_canary G + 8 <= img_hi A.
  (* [comment removed for export] *)
  Variables wi0 wi1 wi2 wi3 wi4 wi5 wi6 : bv 32.
  Hypothesis Xis : 0 <= g_istrlen G /\ g_istrlen G + 28 < 2 ^ 64.
  Hypothesis Ei : is_ecall wi0 = false /\ is_ecall wi1 = false /\ is_ecall wi2 = false /\ is_ecall wi3 = false
                  /\ is_ecall wi4 = false /\ is_ecall wi5 = false /\ is_ecall wi6 = false.
  Definition istrlen_code : Prop :=
    fetch_word SEGS (Z_to_bv 64 (g_istrlen G)) = Some wi0 /\ fetch_word SEGS (Z_to_bv 64 (g_istrlen G + 4)) = Some wi1
    /\ fetch_word SEGS (Z_to_bv 64 (g_istrlen G + 8)) = Some wi2 /\ fetch_word SEGS (Z_to_bv 64 (g_istrlen G + 12)) = Some wi3
    /\ fetch_word SEGS (Z_to_bv 64 (g_istrlen G + 16)) = Some wi4 /\ fetch_word SEGS (Z_to_bv 64 (g_istrlen G + 20)) = Some wi5
    /\ fetch_word SEGS (Z_to_bv 64 (g_istrlen G + 24)) = Some wi6
    /\ decode_any wi0 = Some (OpImm ALU_ADD 11 0 0, 4%Z) /\ decode_any wi1 = Some (Op ALU_ADD 12 10 11, 4%Z)
    /\ decode_any wi2 = Some (Load SZ1 false 12 12 0, 4%Z) /\ decode_any wi3 = Some (OpImm ALU_ADD 11 11 1, 4%Z)
    /\ decode_any wi4 = Some (Branch BC_NE 12 0 8180, 4%Z) /\ decode_any wi5 = Some (OpImm ALU_ADD 10 11 4095, 4%Z)
    /\ decode_any wi6 = Some (Jalr 0 1 0, 4%Z).
  Hypothesis ISTR : g_istrlen G = 0 \/ istrlen_code.
  (* [comment removed for export] *)
  Hypothesis MEMCHR : MEMCHR_STMT ip.
  Hypothesis MEMCPY : MEMCPY_STMT ip.
  Hypothesis STDIO : STDIO_STMT ip.
  (* [comment removed for export] *)
  Variables (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)).   (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Variable hw : word.   (* [comment removed for export] *)
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
  Let STR0 := usp + 8 * argc + 8 * envc + 184.   (* [comment removed for export] *)
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

  Lemma Lay_i : 0x7fff80000000 <= usp /\ usp + 176 <= STR0 /\ STR0 + L0 + 1 <= TOP
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
  Lemma Hnz_i : forall i j, (j < length (ARG argv0 argv1 i))%nat -> bv_unsigned (byte_at (ARG argv0 argv1 i) j) <> 0.
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
  Lemma argH0_high_i : forall E (a : word), argH0 APH sp rdraw argv envp uid hw E a = true -> CEIL <= bv_unsigned a.
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
  Lemma rd_of_SINV1 : forall E M (a : word), SINV1 E M -> STR0 <= bv_unsigned a < TOP -> exists b, M a = Some b.
  Proof.
    intros E M a ((Hev & Hmem) & _ & _) Ha. pose proof W_facts as [W1 W2]. pose proof TOP_eq as TE. pose proof len_av. pose proof len_ev.
    rewrite Hmem.
    2:{ unfold argH0. apply orb_true_intro. right. apply andb_true_intro. fold usp argc envc bsb. fold W.
        split; [apply Z.leb_le | apply Z.ltb_lt]; unfold STR0, TOP in Ha; lia. }
    rewrite wrap_above_sp by (unfold usp, STR0 in *; lia). fold bsb. unfold stack_to_mem. fold usp.
    replace (usp <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; unfold STR0 in Ha; lia).
    (* [comment removed for export] *)
    assert (HL : (length bsb <= length (entry_stack_image APH sp argv envp uid hw rdraw))%nat)
      by (unfold entry_stack_image; cbv zeta; rewrite length_app; fold bsb; lia).
    replace (bv_unsigned a - usp <? Z.of_nat (length (entry_stack_image APH sp argv envp uid hw rdraw))) with true
      by (symmetry; apply Z.ltb_lt; unfold STR0 in Ha; lia).
    unfold entry_stack_image. cbv zeta. fold bsb. rewrite nth_error_app1 by (unfold STR0 in Ha; lia).
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
    pose proof Lay_i as LAY. pose proof (STR_range usp STR0 TOP argc argv0 argv1 LAY i Hi) as [R1 R2].
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
    pose proof (read_argv_byte_k APH ASEGS sp argv envp (idx1 i) j uid hw rdraw Hk ltac:(rewrite Harg; exact Hj)
                  (lay_bsb_nw APH sp rdraw argv envp uid hw Hva Hve ltac:(destruct Hsp as (_ & H & _); exact H))) as RD.
    rewrite (cat_argv_ptr_STR i Hi), word_add_nat, u64_lit in RD by lia. rewrite Harg in RD. fold bsb in RD.
    assert (Hm : M (Z_to_bv 64 (STR STR0 argv0 i + Z.of_nat j))
                 = stack_to_mem sp (entry_stack_image APH sp argv envp uid hw rdraw) (Z_to_bv 64 (STR STR0 argv0 i + Z.of_nat j))).
    { rewrite Hmem.
      2:{ pose proof W_facts as [W1 W2]. pose proof len_av. pose proof len_ev.
          unfold argH0. apply orb_true_intro. right. apply andb_true_intro. fold usp argc envc bsb. fold W.
          rewrite u64_lit by lia. split; [apply Z.leb_le | apply Z.ltb_lt]; unfold STR0, TOP in *; lia. }
      apply wrap_above_sp. rewrite u64_lit by lia. fold usp. lia. }
    rewrite Hm in Hb. cbn [rdn] in RD. rewrite Hb in RD. injection RD as RD'. unfold byte_at. exact RD'.
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

  (* [comment removed for export] *)

  Theorem arg_ext_sound : forall id args, (id < 10)%nat ->
    node1_stmt SEGS A NX0 LIM SV AH FS0 always
      (fun cs => if ((id =? 0)%nat && (g_istrlen G =? 0))%bool then None else xn SEGS A NX0 G id args cs).
  Proof.
    intros id args Hid.
    pose proof Lay_i as LAY. pose proof Ei as EC. pose proof argH0_high_i as AHh. pose proof (argH0_agree APH sp rdraw argv envp uid hw) as AAg.
    destruct id as [|[|[|[|[|[|[|[|[|[|id]]]]]]]]]]; [| | | | | | | | | |lia]; cbn [Nat.eqb andb xn].
    - destruct (Z.eqb_spec (g_istrlen G) 0) as [Hz|Hz]; [intros cs cs' E R FULL model T _ _ Hn _; discriminate Hn|].
      destruct ISTR as [G0|(Fi0 & Fi1 & Fi2 & Fi3 & Fi4 & Fi5 & Fi6 & Di0 & Di1 & Di2 & Di3 & Di4 & Di5 & Di6)]; [lia|].
      eapply (xn_sound_argstrlen SEGS A NX0 LIM SV AH FS0 WX IN_HULL HULL_OK SV_frame G wi0 wi1 wi2 wi3 wi4 wi5 wi6);
        first [exact Xis | exact Fi0 | exact Fi1 | exact Fi2 | exact Fi3 | exact Fi4 | exact Fi5 | exact Fi6 | exact EC
              | exact Di0 | exact Di1 | exact Di2 | exact Di3 | exact Di4 | exact Di5 | exact Di6
              | exact LAY | exact Hnz_i | exact vals_of_SV | exact rd_of_SV | exact str_of_SV | exact Gro ].
    - eapply (xn_sound_argmemchr SEGS A NX0 NX0_min_ok_NX0 LIM SV AH FS0 WX IN_HULL HULL_OK AHh AAg SV_frame SV_agree G);
        first [exact LAY | exact Hnz_i | exact vals_of_SV | exact rd_of_SV | exact str_of_SV | exact Gro | exact MEMCHR].
    - eapply (xn_sound_argnul SEGS A NX0 LIM SV AH FS0 WX IN_HULL HULL_OK SV_frame);
        first [exact LAY | exact vals_of_SV | exact str_of_SV].
    - eapply (xn_sound_memcpyarg SEGS A NX0 NX0_min_ok_NX0 LIM SV AH FS0 WX IN_HULL HULL_OK AHh AAg SV_frame SV_agree);
        first [exact LAY | exact vals_of_SV | exact str_of_SV | exact MEMCPY].
    - intros cs cs' E R FULL model T _ _ Hn _. discriminate Hn.
    - apply xn_sound_reldiff.
    - apply xn_sound_zerocover.
    - apply xn_sound_srlbound.
    - intros cs cs' E R FULL model T _ _ Hn _. discriminate Hn.
    - intros cs cs' E R FULL model T _ _ Hn _. discriminate Hn.
  Qed.

  Theorem arg_emit_sound : emit_stmt SEGS A NX0 LIM (xe SEGS A NX0 G) SV AH FS0.
  Proof.
    pose proof Lay_i as LAY. pose proof Ei as EC. pose proof argH0_high_i as AHh. pose proof (argH0_agree APH sp rdraw argv envp uid hw) as AAg.
    eapply (xe_sound SEGS A NX0 NX0_min_ok_NX0 LIM SV AH FS0 IN_HULL HULL_OK AHh AAg SV_frame SV_agree G wi0 wi1 wi2 wi3 wi4 wi5 wi6);
      first [exact Xis | exact EC | exact LAY | exact vals_of_SV | exact str_of_SV | exact Gro | exact STDIO | exact Gfile].
  Qed.
  (* [comment removed for export] *)
  Theorem arg_emit_soundW : forall id args cs ws, xe_ws id args cs = Some ws ->
    emit_stmtW_at SEGS A NX0 LIM (xe SEGS A NX0 G) SV AH FS0 id args cs ws.
  Proof.
    pose proof Lay_i as LAY. pose proof Ei as EC. pose proof argH0_high_i as AHh. pose proof (argH0_agree APH sp rdraw argv envp uid hw) as AAg.
    eapply (xe_soundW SEGS A NX0 NX0_min_ok_NX0 LIM SV AH FS0 IN_HULL HULL_OK AHh AAg SV_frame SV_agree G wi0 wi1 wi2 wi3 wi4 wi5 wi6);
      first [exact Xis | exact EC | exact LAY | exact vals_of_SV | exact str_of_SV | exact Gro | exact STDIO | exact Gfile].
  Qed.
End ArgInst.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem arg_hooks_of_specs : forall (ip : imgparams) (ph : PhdrInfo),
  wx_segs_nowrap (ip_segs ip) ->
  (forall a : word, in_hull (ip_A ip) (bv_unsigned a) = false -> find_segment (ip_segs ip) (bv_unsigned a) 1 = None) ->
  hull_ok (ip_A ip) ->
  img_lo (ip_A ip) <= g_ro_lo (ip_G ip) /\ g_ro_hi (ip_G ip) <= img_hi (ip_A ip) ->
  (img_lo (ip_A ip) <= g_file_lo (ip_G ip) /\ g_file_hi (ip_G ip) <= img_hi (ip_A ip) /\ img_lo (ip_A ip) <= g_canary_got (ip_G ip)
   /\ g_canary_got (ip_G ip) + 8 <= img_hi (ip_A ip) /\ img_lo (ip_A ip) <= g_canary (ip_G ip) /\ g_canary (ip_G ip) + 8 <= img_hi (ip_A ip)) ->
  g_istrlen (ip_G ip) = 0 ->
  (forall (fy : FPState), MEMCHR_STMT (fx:=fy) ip) -> (forall (fy : FPState), MEMCPY_STMT (fx:=fy) ip) ->
  (forall (fy : FPState), STDIO_STMT (fx:=fy) ip) ->
  arg_hooks_ok ip ph.
Proof.
  intros ip ph WX IH HOK Gro Gfile G0 MC MP SW sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit.
  assert (S1 : forall E M, SINVm ph sp rdraw brk0 argv envp uid hw (content_of argv fs) E M -> SINV1 ph sp rdraw brk0 argv envp uid hw E M).
  { intros E M (H0 & H1 & H2 & _). exact (conj H0 (conj H1 H2)). }
  pose proof (SINVm_frame ph sp rdraw brk0 argv envp uid hw (content_of argv fs)) as SF.
  pose proof (SINVm_agree ph sp rdraw brk0 argv envp uid hw (content_of argv fs)) as SA.
  set (w0 := Z_to_bv 32 0x13).   (* [comment removed for export] *)
  assert (Xis : 0 <= g_istrlen (ip_G ip) /\ g_istrlen (ip_G ip) + 28 < 2 ^ 64) by (rewrite G0; lia).
  assert (Ei : is_ecall w0 = false /\ is_ecall w0 = false /\ is_ecall w0 = false /\ is_ecall w0 = false
               /\ is_ecall w0 = false /\ is_ecall w0 = false /\ is_ecall w0 = false) by (repeat split; reflexivity).
  split.
  - intros fy id args Hid.
    exact (arg_ext_sound (fx:=fy) ip ph WX IH HOK Gro w0 w0 w0 w0 w0 w0 w0 Xis Ei (or_introl G0) (MC fy) (MP fy) sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit fs _ S1 SF SA id args Hid).
  - intros fy. exact (arg_emit_soundW (fx:=fy) ip ph IH HOK Gro Gfile w0 w0 w0 w0 w0 w0 w0 Xis Ei (SW fy) sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit fs _ S1 SF SA).
Qed.

(* [comment removed for export] *)
Theorem arg_hooks_of_specs_istrlen : forall (ip : imgparams) (ph : PhdrInfo) (wi0 wi1 wi2 wi3 wi4 wi5 wi6 : bv 32),
  wx_segs_nowrap (ip_segs ip) ->
  (forall a : word, in_hull (ip_A ip) (bv_unsigned a) = false -> find_segment (ip_segs ip) (bv_unsigned a) 1 = None) ->
  hull_ok (ip_A ip) ->
  img_lo (ip_A ip) <= g_ro_lo (ip_G ip) /\ g_ro_hi (ip_G ip) <= img_hi (ip_A ip) ->
  (img_lo (ip_A ip) <= g_file_lo (ip_G ip) /\ g_file_hi (ip_G ip) <= img_hi (ip_A ip) /\ img_lo (ip_A ip) <= g_canary_got (ip_G ip)
   /\ g_canary_got (ip_G ip) + 8 <= img_hi (ip_A ip) /\ img_lo (ip_A ip) <= g_canary (ip_G ip) /\ g_canary (ip_G ip) + 8 <= img_hi (ip_A ip)) ->
  0 <= g_istrlen (ip_G ip) /\ g_istrlen (ip_G ip) + 28 < 2 ^ 64 ->
  (is_ecall wi0 = false /\ is_ecall wi1 = false /\ is_ecall wi2 = false /\ is_ecall wi3 = false
   /\ is_ecall wi4 = false /\ is_ecall wi5 = false /\ is_ecall wi6 = false) ->
  istrlen_code ip wi0 wi1 wi2 wi3 wi4 wi5 wi6 ->
  (forall (fy : FPState), MEMCHR_STMT (fx:=fy) ip) -> (forall (fy : FPState), MEMCPY_STMT (fx:=fy) ip) ->
  (forall (fy : FPState), STDIO_STMT (fx:=fy) ip) ->
  arg_hooks_ok ip ph.
Proof.
  intros ip ph wi0 wi1 wi2 wi3 wi4 wi5 wi6 WX IH HOK Gro Gfile Xis Ei IC MC MP SW sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit.
  assert (S1 : forall E M, SINVm ph sp rdraw brk0 argv envp uid hw (content_of argv fs) E M -> SINV1 ph sp rdraw brk0 argv envp uid hw E M).
  { intros E M (H0 & H1 & H2 & _). exact (conj H0 (conj H1 H2)). }
  pose proof (SINVm_frame ph sp rdraw brk0 argv envp uid hw (content_of argv fs)) as SF.
  pose proof (SINVm_agree ph sp rdraw brk0 argv envp uid hw (content_of argv fs)) as SA.
  split.
  - intros fy id args Hid.
    exact (arg_ext_sound (fx:=fy) ip ph WX IH HOK Gro wi0 wi1 wi2 wi3 wi4 wi5 wi6 Xis Ei (or_intror IC) (MC fy) (MP fy) sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit fs _ S1 SF SA id args Hid).
  - intros fy. exact (arg_emit_soundW (fx:=fy) ip ph IH HOK Gro Gfile wi0 wi1 wi2 wi3 wi4 wi5 wi6 Xis Ei (SW fy) sp rdraw brk0 argv envp Hsp Hva Hve uid hw Hfit fs _ S1 SF SA).
Qed.
