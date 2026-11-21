(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revised entry stack block, with the strings at its top, and the launch facts; the run's mmap base; path_at's bound below TASK_SIZE). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BRelSpec BSimInv BExitSim BPropExec BCatSim BCatExec BErrEscape BSeqExec BStreamExec BStreamSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.

Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma with_fds_fs : forall f m, m_fs (with_fds f m) = m_fs m.
Proof. reflexivity. Qed.

Lemma with_fds_fds : forall f m, m_fds (with_fds f m) = f.
Proof. reflexivity. Qed.

Section FX1. Context {fx : DFP}.
Lemma adv_eff_ret : forall regs pc x8 mem rom r,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := dfp_regs; ms_pc_val := pc; ms_svc_pending := Some x8;
       ms_resv := None; ms_fcsr := dfp_csr; ms_mem := mem; ms_rom := rom |} (mkEffect r [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof.
  intros regs pc x8 mem rom r.
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros apply_writes apply_zeros].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

End FX1.

Lemma in_sysno_si : forall segs ms x8, in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.
Lemma in_arg0_si : forall segs ms x8, in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.
Lemma in_arg1_si : forall segs ms x8, in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1.
Proof. reflexivity. Qed.
Lemma in_arg2_si : forall segs ms x8, in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2.
Proof. reflexivity. Qed.
Lemma in_mem_si : forall segs ms x8, in_mem (sys_input segs ms x8) = ms_read_byte ms.
Proof. reflexivity. Qed.
Lemma in_wmem_si : forall segs ms x8,
  in_wmem (sys_input segs ms x8) = ms_writable_byte segs ms.
Proof. reflexivity. Qed.

Lemma fd_lookup_cons_eq : forall fds fd e, fd_lookup ((fd, e) :: fds) fd = Some e.
Proof. intros. cbn. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma fd_lookup_cons_neq : forall fds k e fd, k <> fd ->
  fd_lookup ((k, e) :: fds) fd = fd_lookup fds fd.
Proof.
  intros fds k e fd Hne. cbn.
  rewrite (bv_eqb_neq k fd Hne). reflexivity.
Qed.

Lemma fd_lookup_filter_neq : forall fds fd fd', fd' <> fd ->
  fd_lookup (List.filter (fun p => negb (bv_eqb (fst p) fd)) fds) fd' = fd_lookup fds fd'.
Proof.
  induction fds as [|[k e] fds IH]; intros fd fd' Hne; [reflexivity|].
  cbn [List.filter fst].
  destruct (bv_eqb k fd) eqn:Hk.
  - apply bv_eqb_eq in Hk. subst k.
    cbn [negb]. rewrite IH by exact Hne. cbn [fd_lookup].
    rewrite bv_eqb_neq by congruence. reflexivity.
  - cbn [negb fd_lookup]. destruct (bv_eqb k fd'); [reflexivity | apply IH; exact Hne].
Qed.

Lemma fd_lookup_insert_eq : forall fds fd e, fd_lookup (fd_insert fds fd e) fd = Some e.
Proof. intros. unfold fd_insert. apply fd_lookup_cons_eq. Qed.

Lemma fd_lookup_insert_neq : forall fds fd e fd', fd' <> fd ->
  fd_lookup (fd_insert fds fd e) fd' = fd_lookup fds fd'.
Proof.
  intros fds fd e fd' Hne. unfold fd_insert.
  rewrite fd_lookup_cons_neq by congruence.
  apply fd_lookup_filter_neq. exact Hne.
Qed.

Lemma fd_lookup_remove_neq : forall fds fd fd', fd' <> fd ->
  fd_lookup (fd_remove fds fd) fd' = fd_lookup fds fd'.
Proof. intros. unfold fd_remove. apply fd_lookup_filter_neq. assumption. Qed.

Lemma length_file_read : forall data off count,
  length (file_read data off count)
  = Nat.min (word_to_nat count) (length data - word_to_nat off)%nat.
Proof.
  intros data off count. rewrite file_read_unguarded.
  rewrite length_firstn, length_skipn. reflexivity.
Qed.

Lemma firstn_add {A} : forall (l : list A) n m,
  firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof.
  induction l as [|x l IH]; intros n m.
  - rewrite !firstn_nil, skipn_nil, firstn_nil. reflexivity.
  - destruct n as [|n]; [reflexivity|].
    cbn [firstn skipn Nat.add app]. rewrite IH. reflexivity.
Qed.

Definition mrb (segs : list Segment) (mem : word -> option byte)
    : word -> option byte :=
  fun a => match mem a with Some b => Some b | None => seg_rom segs a end.

Section FX2. Context {fx : DFP}.

End FX2.

Lemma mrb_first : forall segs mem a n b rest,
  rdn segs mem a (S n) = Some (b :: rest) -> mrb segs mem a = Some b.
Proof.
  intros segs mem a n b rest H. unfold mrb. cbn [rdn] in H.
  destruct (match mem a with Some b0 => Some b0 | None => seg_rom segs a end)
    as [b1|]; [|discriminate].
  destruct (rdn segs mem (a + 1) n) as [rest1|]; [|discriminate].
  injection H; intros; subst; congruence.
Qed.

Lemma rdn_tail : forall segs mem a n b rest,
  rdn segs mem a (S n) = Some (b :: rest) -> rdn segs mem (a + 1) n = Some rest.
Proof.
  intros segs mem a n b rest H. cbn [rdn] in H.
  destruct (match mem a with Some b0 => Some b0 | None => seg_rom segs a end)
    as [b1|]; [|discriminate].
  destruct (rdn segs mem (a + 1) n) as [rest1|]; [|discriminate].
  injection H; intros; subst; reflexivity.
Qed.

Lemma read_cstr_aux_of_rdn : forall segs str fuel mem a,
  (length str < fuel)%nat -> ~ In (Z_to_bv 8 0) str ->
  (bv_unsigned a + Z.of_nat (length str) < TASK_SIZE)%Z ->
  rdn segs mem a (length str + 1) = Some (str ++ [Z_to_bv 8 0]) ->
  read_cstr_aux (mrb segs mem) a fuel = CstrOk str.
Proof.
  intros segs str; induction str as [|b str IH]; intros fuel mem a Hf Hnz Hlo Hr.
  - cbn [length] in *. destruct fuel as [|fuel]; [lia|].
    assert (Hb0 : mrb segs mem a = Some (Z_to_bv 8 0))
      by (apply (mrb_first segs mem a 0 (Z_to_bv 8 0) []); exact Hr).
    rewrite read_cstr_aux_accepted
      by (rewrite access_okb_one; apply Z.ltb_lt; lia).
    rewrite Hb0. reflexivity.
  - cbn [length] in *. destruct fuel as [|fuel]; [lia|].
    rewrite read_cstr_aux_accepted
      by (rewrite access_okb_one; apply Z.ltb_lt; lia).
    cbn [app] in Hr.
    assert (Hb : b <> Z_to_bv 8 0) by (intro; apply Hnz; left; auto).
    assert (Hfirst : mrb segs mem a = Some b)
      by (apply (mrb_first segs mem a (length str + 1) b (str ++ [Z_to_bv 8 0]));
          exact Hr).
    assert (Htail : rdn segs mem (a + 1) (length str + 1)
                    = Some (str ++ [Z_to_bv 8 0]))
      by (apply (rdn_tail segs mem a (length str + 1) b (str ++ [Z_to_bv 8 0]));
          exact Hr).
    assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z)
      by (apply bv_unsigned_succ_below_task_size; lia).
    rewrite Hfirst. rewrite (bv_eqb_neq b (Z_to_bv 8 0) Hb).
    rewrite (IH fuel mem (a + 1) ltac:(lia)
               ltac:(intro; apply Hnz; right; assumption) ltac:(lia) Htail).
    reflexivity.
Qed.

Lemma read_cstr_of_rdn : forall segs mem a str,
  (length str <= 4095)%nat -> ~ In (Z_to_bv 8 0) str ->
  (bv_unsigned a + Z.of_nat (length str) < TASK_SIZE)%Z ->
  rdn segs mem a (length str + 1) = Some (str ++ [Z_to_bv 8 0]) ->
  read_cstr (mrb segs mem) a = CstrOk str.
Proof.
  intros segs mem a str Hlen Hnz Hlo Hr.
  unfold read_cstr. apply read_cstr_aux_of_rdn; [|exact Hnz|exact Hlo|exact Hr].
  change path_max with 4096%nat. lia.
Qed.

Lemma read_cstr_aux_toolong_of_rdn : forall segs fuel bs mem a,
  length bs = fuel -> ~ In (Z_to_bv 8 0) bs ->
  (fuel <> 0%nat -> (bv_unsigned a + Z.of_nat fuel <= TASK_SIZE)%Z) ->
  rdn segs mem a fuel = Some bs ->
  read_cstr_aux (mrb segs mem) a fuel = CstrTooLong.
Proof.
  intros segs fuel; induction fuel as [|fuel IH]; intros bs mem a Hlen Hnz Hlo Hr;
    [reflexivity|].
  specialize (Hlo ltac:(lia)).
  destruct bs as [|b bs]; [cbn in Hlen; lia|].
  rewrite read_cstr_aux_accepted
    by (rewrite access_okb_one; apply Z.ltb_lt; lia).
  assert (Hb : b <> Z_to_bv 8 0) by (intro; apply Hnz; left; auto).
  assert (Hfirst : mrb segs mem a = Some b)
    by (apply (mrb_first segs mem a fuel b bs); exact Hr).
  assert (Htail : rdn segs mem (a + 1) fuel = Some bs)
    by (apply (rdn_tail segs mem a fuel b bs); exact Hr).
  assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z)
    by (apply bv_unsigned_succ_below_task_size; lia).
  rewrite Hfirst. rewrite (bv_eqb_neq b (Z_to_bv 8 0) Hb).
  rewrite (IH bs mem (a + 1) ltac:(cbn in Hlen; lia)
             ltac:(intro; apply Hnz; right; assumption)
             ltac:(intro; lia) Htail).
  reflexivity.
Qed.

Lemma read_cstr_toolong_of_rdn : forall segs mem a bs,
  length bs = 4096%nat -> ~ In (Z_to_bv 8 0) bs ->
  (bv_unsigned a + 4096 <= TASK_SIZE)%Z ->
  rdn segs mem a 4096%nat = Some bs ->
  read_cstr (mrb segs mem) a = CstrTooLong.
Proof.
  intros segs mem a bs Hlen Hnz Hlo Hr.
  unfold read_cstr. change path_max with 4096%nat.
  eapply read_cstr_aux_toolong_of_rdn; [exact Hlen|exact Hnz| |exact Hr].
  intros _. change (Z.of_nat 4096) with 4096%Z. lia.
Qed.

Lemma read_argv_cstr_k :
  forall v segs inp mbase ph entry (sp brk : word) draw k,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (k < length (in_argv inp))%nat ->
  rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw))
      (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
      (length (nth k (in_argv inp) []) + 1)
  = Some (nth k (in_argv inp) [] ++ [Z_to_bv 8 0]).
Proof.
  intros v segs inp mbase ph entry sp brk draw k Hlaunch Hk.
  pose proof (entry_stack_image_no_wrap v inp mbase ph entry sp brk draw Hlaunch)
    as Hnw.
  destruct (bsb_byte_k inp mbase ph entry sp draw k Hk) as [pre [post [E Hlen]]].
  pose proof (read_at_offset_image segs inp mbase ph entry sp draw
    pre (nth k (in_argv inp) [] ++ [Z_to_bv 8 0]) post
    (length (nth k (in_argv inp) []) + 1)) as H.
  rewrite Hlen in H.
  replace (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
             (in_execfn inp) k)
    with (sp + nat_to_word
                 (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
                    (in_argv inp) (in_envp inp) (in_execfn inp)
                  + total_arg_bytes_nat (firstn k (in_argv inp)))).
  2:{ rewrite (cat_argv_ptr_offset _ _ _ _ k Hk),
        (cat_string_base_offset v inp mbase sp brk draw Hlaunch).
      rewrite nat_to_word_add_merge. reflexivity. }
  apply H; [exact E | | exact Hnw].
  rewrite length_app. cbn [length]. lia.
Qed.

Lemma ENOMEM_in_openat_errnos : In ENOMEM openat_errnos.
Proof. left. reflexivity. Qed.

Definition open_copyins (ms : machine_state) : list (word * nat) :=
  [(ms_gpr ms 1,
    cstr_access_len_aux (ms_read_byte ms) (ms_gpr ms 1) path_max)].

