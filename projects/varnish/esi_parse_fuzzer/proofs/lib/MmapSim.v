(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the anonymous grant at Linux's own placement from the hint (Placement.linux_place_is) with the place_declined_b premise, munmap over mmap_fixed_destroyed_next as an injected allocation call with its ENOMEM refusal, the per-byte access_ok of path strings below TASK_SIZE and the access_ok range of each write, and argv read from the launch input ProcInput). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec SimInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Stre9ts AllocSim.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Stre9ts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Acfg.

Module ErrEddx.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec CatSim.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section OmniWithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

End OmniWithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AllErrorWithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End AllErrorWithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Section NoUnmodeledWithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End NoUnmodeledWithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End ErrEddx.

Module FileSim.
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Placement.  (* 08b1429: LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_is, read qualified *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec SimInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Stre9ts.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.ErrEddx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.Stredvh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Stre9ts.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_fds_fs : forall f m, m_fs (with_fds f m) = m_fs m.
Proof. reflexivity. Qed.
Lemma with_fds_halted : forall f m, m_halted (with_fds f m) = m_halted m.
Proof. reflexivity. Qed.
Lemma with_fds_fds : forall f m, m_fds (with_fds f m) = f.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma adv_eff_ret : forall regs pc x8 mem rom r,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc; ms_svc_pending := Some x8;
       ms_resv := None; ms_fcsr := Z_to_bv 32 0; ms_mem := mem; ms_rom := rom |} (mkEffect r [] []))
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

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fd_lookup_cons_eq : forall fds fd e, fd_lookup ((fd, e) :: fds) fd = Some e.
Proof. intros. cbn. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma fd_lookup_cons_neq : forall fds k e fd, k <> fd ->
  fd_lookup ((k, e) :: fds) fd = fd_lookup fds fd.
Proof.
  intros fds k e fd Hne. cbn.
  rewrite (bv_eqb_neq k fd Hne). reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

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

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma length_file_read : forall data off count,
  length (file_read data off count)
  = Nat.min (word_to_nat count) (length data - word_to_nat off)%nat.
Proof.
  intros data off count. rewrite file_read_unguarded.
  rewrite length_firstn, length_skipn. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mrb (segs : list Segment) (mem : word -> option byte)
    : word -> option byte :=
  fun a => match mem a with Some b => Some b | None => seg_rom segs a end.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mrb_first : forall segs mem a n b rest,
  rdn segs mem a (S n) = Some (b :: rest) -> mrb segs mem a = Some b.
Proof.
  intros segs mem a n b rest H. unfold mrb. cbn [rdn] in H.
  destruct (match mem a with Some b0 => Some b0 | None => seg_rom segs a end)
    as [b1|]; [|discriminate].
  destruct (rdn segs mem (a + 1) n) as [rest1|]; [|discriminate].
  injection H; intros; subst; congruence.
Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ENOMEM_in_openat_errnos : In ENOMEM openat_errnos.
Proof. left. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition open_copyins (ms : machine_state) : list (word * nat) :=
  [(ms_gpr ms 1,
    cstr_access_len_aux (ms_read_byte ms) (ms_gpr ms 1) path_max)].

(* [comment removed for export] *)
End FileSim.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_sb_any : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 1%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            [Z_to_bv 8 (bv_unsigned (getr regs rs2))]) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  rewrite <- N_to_le_bytes_1_small.
  apply (step_sb segs regs pc mem rom w rs1 rs2 imm); assumption.
Qed.

(* [comment removed for export] *)
Lemma step_sb_at : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12)
                          (a v : word) (b : byte),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  Z_to_bv 8 (bv_unsigned v) = b ->
  RiscvSemantics.store_ok segs mem a 1%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a [b]) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm a v b Hf He Hd Ha Hv Hb Hok.
  rewrite (step_sb_any segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
  - rewrite Ha, Hv, Hb. reflexivity.
  - rewrite Ha. exact Hok.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zfill (a n : word) (m : word -> option byte) : word -> option byte :=
  zmem m a n.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition munmap_model (addr n : word) (m : Model) : Model :=
  with_mmap_destroyed addr n (mmap_fixed_destroyed_next (m_vmmaps m) addr n) m.

Lemma iv_subtract_outside : forall (b s : word) lo hi,
  (0 < bv_unsigned s)%Z -> (lo < hi)%Z ->
  (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b)%Z ->
  iv_subtract b s lo hi = [(b, s)].
Proof.
  intros b s lo hi Hs Hlh Hd. unfold iv_subtract. cbv zeta.
  destruct Hd as [Hd|Hd].
  - rewrite (proj2 (Z.ltb_lt (bv_unsigned b) lo)) by lia.
    rewrite (proj2 (Z.ltb_ge hi (bv_unsigned b + bv_unsigned s))) by lia.
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned b) lo)) by lia.
    rewrite (proj2 (Z.ltb_lt hi (bv_unsigned b + bv_unsigned s))) by lia.
    rewrite Z.max_l by lia.
    replace (bv_unsigned b + bv_unsigned s - bv_unsigned b)%Z
      with (bv_unsigned s) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma maps_subtract_exact : forall l (a n : word),
  (0 < bv_unsigned n)%Z ->
  (forall b s, In (b, s) l -> (0 < bv_unsigned s)%Z) ->
  (forall b s, In (b, s) l -> b = a -> s = n) ->
  (forall b s, In (b, s) l -> b <> a ->
     (bv_unsigned b + bv_unsigned s <= bv_unsigned a
      \/ bv_unsigned a + bv_unsigned n <= bv_unsigned b)%Z) ->
  maps_subtract l (bv_unsigned a) (bv_unsigned a + bv_unsigned n)
  = map_remove l a.
Proof.
  induction l as [|[b s] r IH]; intros a n Hn Hpos Hu Hd; [reflexivity|].
  assert (IHr : maps_subtract r (bv_unsigned a) (bv_unsigned a + bv_unsigned n)
                = map_remove r a).
  { apply IH; [exact Hn
              | intros b' s' H; apply (Hpos b' s'); right; exact H
              | intros b' s' H; apply (Hu b' s'); right; exact H
              | intros b' s' H; apply (Hd b' s'); right; exact H]. }
  cbn [maps_subtract]. rewrite IHr.
  unfold map_remove. cbn [List.filter fst]. fold (map_remove r a).
  destruct (bv_eqb b a) eqn:E; cbn [negb].
  - apply bv_eqb_eq in E. subst b.
    rewrite (Hu a s (or_introl eq_refl) eq_refl).
    unfold iv_subtract. cbv zeta.
    rewrite (proj2 (Z.ltb_ge _ _) (Z.le_refl (bv_unsigned a))).
    rewrite (proj2 (Z.ltb_ge _ _) (Z.le_refl (bv_unsigned a + bv_unsigned n))).
    reflexivity.
  - assert (Hne : b <> a) by (intros ->; rewrite bv_eqb_refl in E; discriminate).
    rewrite (iv_subtract_outside b s); [reflexivity | | lia |].
    + exact (Hpos b s (or_introl eq_refl)).
    + exact (Hd b s (or_introl eq_refl) Hne).
Qed.
Definition mmap_model (a n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
               ((a, n) :: vm_maps (m_vmmaps m))
               (vm_noaccess (m_vmmaps m))
               (vm_start_brk (m_vmmaps m))
               (vm_brk (m_vmmaps m))
               (vm_limit (m_vmmaps m))
               (vm_mmap_base (m_vmmaps m))
               (vm_init_sp (m_vmmaps m))) m.

(* [comment removed for export] *)
Definition page_round_up (len : word) : word :=
  Z_to_bv 64 (page_round_up_Z (bv_unsigned len)).

(* [comment removed for export] *)
Definition grant_ok (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a
  && (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n)
  && (vm_backing_used m + n <=? vm_limit (m_vmmaps m))%Z.

Lemma grant_ok_intro : forall hint m a n,
  (0 < n)%Z -> (n mod page_size = 0)%Z ->
  LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true ->
  (vm_backing_used m + n <= vm_limit (m_vmmaps m))%Z ->
  grant_ok hint m a n = true.
Proof.
  intros hint m a n Hn Hnal Hpl Hbud.
  destruct (LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_is_admissible _ _ _ _ _ Hn Hnal Hpl)
    as (Hal & Hpos & Htop & Hfree).
  unfold grant_ok. rewrite Hpl, Hfree.
  rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos),
    (proj2 (Z.leb_le _ _) Htop), (proj2 (Z.leb_le _ _) Hbud).
  reflexivity.
Qed.
Lemma munmap_model_halted : forall addr n m, m_halted (munmap_model addr n m) = m_halted m.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma munmap_model_no_lazy : forall addr n m,
  m_vm_lazy m = [] -> m_vm_lazy (munmap_model addr n m) = [].
Proof.
  intros addr n m Hlazy. unfold munmap_model, with_mmap_destroyed,
    vm_forget_range, with_vm_backing, with_vmmaps.
  cbn [m_vm_lazy]. rewrite Hlazy. reflexivity.
Qed.
Lemma grant_ok_place : forall hint m a n,
  grant_ok hint m a n = true ->
  LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_is (m_vmmaps m) (kb_thp (m_kernel m)) hint n a = true.
Proof.
  intros hint m a n H. unfold grant_ok in H.
  rewrite !andb_true_iff in H. tauto.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_free_cons : forall (b s : word) r (lo n : word),
  region_free ((b, s) :: r) lo n = true ->
  (bv_unsigned lo + bv_unsigned n <= bv_unsigned b
   \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo)%Z
  /\ region_free r lo n = true.
Proof.
  intros b s r lo n H. cbn [region_free] in H.
  apply andb_true_iff in H. destruct H as [H1 H2].
  split; [|exact H2].
  apply negb_true_iff in H1. unfold iv_overlap in H1.
  apply andb_false_iff in H1.
  destruct H1 as [H1 | H1]; [right | left]; apply Z.ltb_ge in H1; lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma in_arg3_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 3 = ms_gpr ms 3.
Proof. reflexivity. Qed.

Lemma in_arg4_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 4 = ms_gpr ms 4.
Proof. reflexivity. Qed.

Lemma in_arg5_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 5 = ms_gpr ms 5.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition mmap_args_ok (ms : machine_state) : Prop :=
  ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 3
  /\ ms_gpr ms 3 = Z_to_bv 64 34 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
  /\ ms_gpr ms 5 = Z_to_bv 64 0.

(* [comment removed for export] *)
Lemma mmap_args_ok_gates : forall ms,
  mmap_args_ok ms ->
  w_is0 (ms_gpr ms 1) = false /\
  mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)
  = true.
Proof.
  (intros ms; (first [ intro dR_7; dand5 dR_7 as H1 H2 H3 H4 H5 | intros (H1 & H2 & H3 & H4 & H5) ])).
  split; [unfold w_is0; apply bv_eqb_neq; exact H1|].
  unfold mmap_modeled_b. rewrite H2, H3, H5. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition munmap_args_ok (ms : machine_state) (model : Model) : Prop :=
  (bv_unsigned (ms_gpr ms 0) mod page_size = 0)%Z /\
  ms_gpr ms 1 <> Z_to_bv 64 0 /\
  (bv_unsigned (ms_gpr ms 0) + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) <= TASK_SIZE)%Z /\
  map_has (vm_maps (m_vmmaps model)) (ms_gpr ms 0)
    (page_round_up (ms_gpr ms 1)) = true.

(* [comment removed for export] *)
Definition munmap_eff (ms : machine_state) : SyscallEffect :=
  mkEffectU (Z_to_bv 64 0) [] [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))] [] [].

Lemma syscall_spec_munmap : forall segs ms x8 model o,
  bv_unsigned x8 = 215%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> munmap_spec (ms_gpr ms 0) (ms_gpr ms 1) (sys_input segs ms x8) model o).
Proof.
  intros segs ms x8 model o Hno.
  unfold syscall_spec, dispatch.
  rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.

From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.  (* 08b1429: check_munmap and its proofs, as the model's MmapSim imports them *)
Lemma munmap_check_modeled : forall ms model eff,
  munmap_args_ok ms model ->
  check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in munmap_errnos r
        then match us with
             | [] => CheckOk model []
             | _ => CheckReject
             end
        else if w_is0 r
                && listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]
        then CheckOk (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []
        else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms model eff (Hal & Hlen & Hnw & Hhas).
  unfold check_munmap.
  rewrite (proj2 (Z.eqb_eq _ _) Hal).
  unfold w_is0 at 1. rewrite (bv_eqb_neq _ _ Hlen).
  cbn [negb orb]. cbv zeta.
  rewrite (proj2 (Z.ltb_ge _ _) Hnw). cbv beta iota.
  unfold page_round_up in Hhas. rewrite Hhas. reflexivity.
Qed.

Lemma munmap_fail_ok : forall segs ms x8 model e,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  In e munmap_errnos ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (errno_ret e) [] []) model []).
Proof.
  intros segs ms x8 model e Hno Ha HIn.
  apply (proj2 (syscall_spec_munmap _ _ _ _ _ Hno)). apply check_munmap_sound_ok.
  rewrite (munmap_check_modeled ms model _ Ha).
  rewrite errno_ret_in_intro by assumption. reflexivity.
Qed.
Lemma ENOMEM_in_munmap_errnos : In ENOMEM munmap_errnos.
Proof. left. reflexivity. Qed.
(* [comment removed for export] *)
Lemma munmap_outcome_si : forall segs ms x8 model o,
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  syscall_spec (sys_input segs ms x8) model o <->
  (exists e, In e munmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) model [])
  \/ o = Ok (munmap_eff ms)
         (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) [].
Proof.
  (intros segs ms x8 model o Hno; (first [ intro dR_8; dand4 dR_8 as Hal Hlen Hnw Hhas | intros (Hal & Hlen & Hnw & Hhas) ])).
  rewrite (syscall_spec_215 _ model o) by (rewrite in_sysno_sys_input; exact Hno).
  rewrite in_arg0_sys_input, in_arg1_sys_input.
  unfold munmap_eff, munmap_model, page_round_up.
  apply munmap_exact_outcome; [exact Hal | unfold w_is0; apply bv_eqb_neq; exact Hlen | exact Hnw |].
  unfold page_round_up in Hhas. exact Hhas.
Qed.

(* 08b1429: munmap (215) is an injected alloc-family call. With the exact mapping present its ENOMEM
   refusal is spurious, so under the alloc-only config the unmap is its one outcome (ruling (a)). *)
Lemma munmap_outcome_acfg : forall segs ms x8 model o,
  bv_unsigned x8 = 215%Z -> m_halted model = None ->
  munmap_args_ok ms model ->
  syscall_spec_acfg (sys_input segs ms x8) model o <->
  o = Ok (munmap_eff ms) (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) [].
Proof.
  intros segs ms x8 model o Hno Hh Hargs.
  apply (acfg_lift_munmap (sys_input segs ms x8) model
           (fun o' => o' = Ok (munmap_eff ms)
                             (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) [])).
  - first [rewrite in_sysno_sys_input; exact Hno | rewrite in_sysno_si; exact Hno].
  - exact Hh.
  - intros o'. exact (munmap_outcome_si segs ms x8 model o' Hno Hargs).
  - intros o' ->. do 3 eexists. split; [reflexivity|].
    split; [vm_compute; reflexivity | rewrite munmap_model_halted; exact Hh].
  - eexists. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ENOMEM_in_mmap_errnos : In ENOMEM mmap_errnos.
Proof. left. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition grant_refusable (hint : word) (m : Model) (n : Z) : bool :=
  mmap_grant_refusable hint (Z_to_bv 64 34) m n.

Lemma w_is0_false_ne : forall x : word, x <> Z_to_bv 64 0 -> w_is0 x = false.
Proof.
  intros x H. unfold w_is0. destruct (bv_eqb x (Z_to_bv 64 0)) eqn:E; [|reflexivity].
  exfalso. apply H. apply bv_eq. unfold bv_eqb in E. apply Z.eqb_eq in E. exact E.
Qed.

(* The two side conditions of [Placement.linux_place_is_iff], from the nonzero length. *)
Lemma mmap_len_place_ok : forall len,
  w_is0 len = false ->
  (0 < page_round_up_Z (bv_unsigned len))%Z /\ (page_round_up_Z (bv_unsigned len) mod page_size = 0)%Z.
Proof.
  intros len H. apply w_is0_false_pos in H. split.
  - pose proof (page_round_up_Z_pos _ H). unfold page_size in *. lia.
  - apply LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.page_round_up_Z_aligned.
Qed.

Lemma grant_ok_not_refusable : forall hint m a n,
  grant_ok hint m a n = true -> grant_refusable hint m n = false.
Proof.
  intros hint m a n H. unfold grant_ok in H. rewrite !andb_true_iff in H.
  destruct H as [[[[[H0 _] _] _] _] H5].
  unfold grant_refusable.
  apply (mmap_grant_not_refusable hint (Z_to_bv 64 34) m n a H0).
  unfold mmap_noreserve_backed_ok.
  replace (mmap_noreserve_b (Z_to_bv 64 34)) with false by (vm_compute; reflexivity).
  exact H5.
Qed.

Lemma grant_refusable_false_iff : forall hint m n,
  (0 < n)%Z -> (n mod page_size = 0)%Z ->
  grant_refusable hint m n = false <-> exists a, grant_ok hint m a n = true.
Proof.
  intros hint m n Hn Hnal. split.
  - intros H. unfold grant_refusable in H.
    destruct (mmap_grant_refusable_false _ _ _ _ Hn Hnal H) as (Hb & a & Hp).
    unfold mmap_noreserve_backed_ok in Hb.
    replace (mmap_noreserve_b (Z_to_bv 64 34)) with false in Hb by (vm_compute; reflexivity).
    exists a. apply grant_ok_intro; [exact Hn | exact Hnal | exact Hp | apply Z.leb_le; exact Hb].
  - intros (a & Ha). exact (grant_ok_not_refusable hint m a n Ha).
Qed.

Lemma mmap_outcome_si : forall segs ms x8 model o,
  bv_unsigned x8 = 222%Z ->
  m_halted model = None ->
  mmap_args_ok ms ->
  (* LPS 727298f3: off the [place_declined_b] decline, as [mmap_rw_outcome] needs. *)
  place_declined_b (m_kernel model) (m_vmmaps model) (ms_gpr ms 0)
    (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = false ->
  syscall_spec_acfg (sys_input segs ms x8) model o <->
  (exists e, In e (mmap_errnos_when (grant_refusable (ms_gpr ms 0) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))))
             /\ o = Ok (mkEffect (errno_ret e) [] []) model [])
  \/ (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true
       /\ o = Ok (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
                 (mmap_model a (page_round_up (ms_gpr ms 1)) model) []).
Proof.
  intros segs ms x8 model o Hno Hh Ha Hdecl. revert o.
  destruct (mmap_len_place_ok (ms_gpr ms 1) (proj1 (mmap_args_ok_gates ms Ha))) as [Hn0 Hnal].
  refine (acfg_lift_mmap_when (sys_input segs ms x8) model
            (fun o => exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true
               /\ o = Ok (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
                         (mmap_model a (page_round_up (ms_gpr ms 1)) model) [])
            (grant_refusable (ms_gpr ms 0) model (page_round_up_Z (bv_unsigned (ms_gpr ms 1)))) _ Hh _ _ _ _).
  - rewrite in_sysno_sys_input. exact Hno.
  - intros o. cbv beta.
    destruct (mmap_args_ok_gates ms Ha) as [Hl Hmb].
    (first [ dand5 Ha as _ _ Hflags _ _ | destruct Ha as (_ & _ & Hflags & _ & _) ]).
    rewrite (syscall_spec_222 _ model o) by (rewrite in_sysno_sys_input; exact Hno).
    rewrite in_arg0_sys_input, in_arg1_sys_input, in_arg2_sys_input,
            in_arg3_sys_input, in_arg4_sys_input, in_arg5_sys_input.
    rewrite (mmap_rw_outcome _ _ _ _ _ _ _ model o Hl Hmb Hdecl). unfold mmap_err_out.
    rewrite Hflags.
    assert (Hnr : mmap_noreserve_b (Z_to_bv 64 34) = false) by (vm_compute; reflexivity).
    unfold mmap_noreserve_backed_ok, with_mmap_backing. rewrite Hnr.
    unfold mmap_model, page_round_up.
    split; (intros [H | (a & Hg & ->)]; [left; exact H | right; exists a; split; [|reflexivity]]).
    + destruct Hg as [Hpl Hb].
      apply (proj2 (LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_is_iff _ _ _ _ _ Hn0 Hnal)) in Hpl.
      apply grant_ok_intro; [exact Hn0 | exact Hnal | exact Hpl | apply Z.leb_le; exact Hb].
    + unfold grant_ok in Hg. rewrite !andb_true_iff in Hg. destruct Hg as [[[[[H0 _] _] _] _] H5].
      split; [exact (proj1 (LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_is_iff _ _ _ _ _ Hn0 Hnal) H0)
             | exact H5].
  - intros o (a & Hg & ->).
    exists (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))]),
      (mmap_model a (page_round_up (ms_gpr ms 1)) model), [].
    split; [reflexivity|]. split; [|exact Hh].
    unfold grant_ok in Hg. rewrite !andb_true_iff in Hg. destruct Hg as [[[[[_ H1] _] _] _] _].
    apply Z.eqb_eq in H1. exact H1.
  - intros o (a & Hg & _). exact (grant_ok_not_refusable _ _ _ _ Hg).
  - intros Hf. destruct (proj1 (grant_refusable_false_iff (ms_gpr ms 0) model _ Hn0 Hnal) Hf) as [a Ha'].
    eexists. exists a. split; [exact Ha' | reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition unfill (a n : word) (m : word -> option byte) : word -> option byte :=
  fun x => if Z.leb (bv_unsigned a) (bv_unsigned x)
              && Z.ltb (bv_unsigned x) (bv_unsigned a + bv_unsigned n)
           then None else m x.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

Inductive twm : machine_state -> Model -> list (list byte) -> word -> Prop :=
| twm_exit : forall ms model x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    twm ms model [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| twm_write : forall ms model buf bufs code,
    (1 <= length buf)%nat ->
    twm_pend ms model buf bufs code ->
    twm ms model (buf :: bufs) code
| twm_munmap : forall ms model x8 bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 215%Z ->
    munmap_args_ok ms model ->
    (forall e, In e munmap_errnos ->
       twm (advance_past_svc (set_gpr0 ms (errno_ret e))) model bufs code) ->
    twm (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code ->
    twm ms model bufs code
| twm_step : forall ms ms' model bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    twm ms' model bufs code ->
    twm ms model bufs code
(** The put-style retry loop realizing one buffer: a write-pending state
    offering the remainder [rest]; the environment delivers any nonempty
    prefix, the loop reissues on the rest.  The trace contribution of the
    whole node is exactly the FULL buffer (WallSim's [to_wall] shape,
    inlined here because the continuation is the mutual [twm]). *)
with twm_pend : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmp_write : forall ms model x8 rest bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = Z_to_bv 64 1 ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
    (* the range [vfs_write]'s [access_ok] accepts; see [CatSim.write1_check_n] *)
    access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
    (1 <= length rest)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
       twm_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest)))) model
         (skipn n rest) bufs code) ->
    twm_pend ms model rest bufs code
with twm_tail : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmt_done : forall ms model bufs code,
    twm ms model bufs code ->
    twm_tail ms model [] bufs code
| twmt_more : forall ms model rest bufs code,
    (1 <= length rest)%nat ->
    twm_pend ms model rest bufs code ->
    twm_tail ms model rest bufs code
| twmt_step : forall ms ms' model rest bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    twm_tail ms' model rest bufs code ->
    twm_tail ms model rest bufs code.

Scheme twm_min := Minimality for twm Sort Prop
  with twm_pend_min := Minimality for twm_pend Sort Prop
  with twm_tail_min := Minimality for twm_tail Sort Prop.
Combined Scheme twm_mutind from twm_min, twm_pend_min, twm_tail_min.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive tmw : machine_state -> Model -> list (list byte) -> word
                -> list (list byte) -> word -> Prop :=
| tmw_mmap : forall ms model x8 bf cf bs cs,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 222%Z ->
    mmap_args_ok ms ->
    (forall e, In e mmap_errnos ->
       twm (advance_past_svc (set_gpr0 ms (errno_ret e))) model bf cf) ->
    (forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
       twm (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
           (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs) ->
    (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
    tmw ms model bf cf bs cs
| tmw_step : forall ms ms' model bf cf bs cs,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    tmw ms' model bf cf bs cs ->
    tmw ms model bf cf bs cs.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition two_traces (bf : list (list byte)) (cf : word)
    (bs : list (list byte)) (cs : word)
    (fs : Fs.Fs) (tr : list event) : Prop :=
  is_prefix tr (wevents bf ++ [ExitEv cf fs]) \/
  is_prefix tr (wevents bs ++ [ExitEv cs fs]).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


Definition mm_path (c : config) : Prop :=
  (m_halted (cfg_model c) = None /\ m_vm_lazy (cfg_model c) = [] /\
   fd1chan (cfg_model c) /\
   ((exists bf cf bs cs, tmw (cfg_ms c) (cfg_model c) bf cf bs cs
                         /\ bufs_modeled bf /\ bufs_modeled bs)
    \/ (exists rest bufs code,
          twm_tail (cfg_ms c) (cfg_model c) rest bufs code
          /\ buf_modeled rest /\ bufs_modeled bufs)))
  \/ m_halted (cfg_model c) <> None.


End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

