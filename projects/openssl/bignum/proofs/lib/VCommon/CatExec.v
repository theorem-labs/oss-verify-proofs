(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch input ProcInput, the CONFIG_RSEQ flag and the init stack window). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import ExitSim PropExec CatSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithFP.
Context {fx : FPState}.

Lemma ms_read_bytes_aux_rdn : forall segs ms n addr,
  ms_rom ms = seg_rom segs ->
  ms_read_bytes_aux ms addr n = rdn segs (ms_mem ms) addr n.
Proof.
  intros segs ms n. induction n as [|n IH]; intros addr Hrom; [reflexivity|].
  cbn [ms_read_bytes_aux rdn]. unfold ms_read_byte. rewrite Hrom.
  destruct (ms_mem ms addr) as [b|].
  - rewrite IH by exact Hrom. reflexivity.
  - unfold seg_rom. destruct (memory_read segs addr 1) as [[|b r]|];
      try reflexivity; rewrite IH by exact Hrom; reflexivity.
Qed.

Lemma ms_read_bytes_rdn : forall segs ms addr len,
  ms_rom ms = seg_rom segs ->
  ms_read_bytes ms addr len = rdn segs (ms_mem ms) addr (word_to_nat len).
Proof. intros. unfold ms_read_bytes. apply ms_read_bytes_aux_rdn; assumption. Qed.

Fixpoint wbytes (m : word -> option byte) (addr : word) (bs : list byte)
    : word -> option byte :=
  match bs with
  | [] => m
  | b :: rest => wbytes (fun a => if bv_eqb a addr then Some b else m a) (addr+1) rest
  end.

Lemma wbytes_below : forall bs m (addr x : word),
  (bv_unsigned addr + Z.of_nat (length bs) <= 2^64)%Z ->
  (bv_unsigned x < bv_unsigned addr)%Z ->
  wbytes m addr bs x = m x.
Proof.
  induction bs as [|b rest IH]; intros m addr x Hnw Hlt; [reflexivity|].
  cbn [wbytes length] in *.
  assert (Hne : bv_eqb x addr = false)
    by (unfold bv_eqb; apply Z.eqb_neq; lia).
  destruct rest as [|b' rest'].
  - cbn [wbytes]. rewrite Hne. reflexivity.
  - assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z)
      by (apply u_add1; cbn [length] in Hnw; lia).
    rewrite IH by lia.
    cbv beta. rewrite Hne. reflexivity.
Qed.

Lemma length_Z_to_le_bytes : forall n z, length (Z_to_le_bytes n z) = n.
Proof.
  induction n as [|n IH]; intro z; [reflexivity|].
  cbn [Z_to_le_bytes length]. rewrite IH. reflexivity.
Qed.

Lemma length_N_to_le_bytes : forall n (v : word), length (word_to_le_bytes n v) = n.
Proof. intros. unfold word_to_le_bytes. apply length_Z_to_le_bytes. Qed.

Lemma write_to_mem_wbytes : forall bs (m : word -> option byte) (addr : word),
  write_to_mem m addr bs = wbytes m addr bs.
Proof.
  induction bs as [|b rest IH]; intros m addr; [reflexivity|].
  cbn [write_to_mem wbytes]. apply IH.
Qed.

(* [comment removed for export] *)
Lemma step_sd : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 8%nat = true ->
  exists bs, length bs = 8%nat /\
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm)) bs) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  exists (word_to_le_bytes 8 (getr regs rs2)). split; [reflexivity|].
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma launch_string_base_arith : forall v inp mbase (sp brk : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (bv_unsigned sp
   + Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp)
                 (in_envp inp))
   + Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                 (in_execfn inp))
   + 8 <= bv_unsigned (ed_top draw))%Z.
Proof.
  intros v inp mbase sp brk draw Hlaunch.
  cbn [entry_launch_ok_va] in Hlaunch.
  destruct Hlaunch as (_ & (_ & _ & Hhi) & _).
  unfold launch_sp_hi, align_down16 in Hhi.
  pose proof (Z.mod_pos_bound
    (bv_unsigned (ed_top draw) - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                   (in_execfn inp))) 16 ltac:(lia)).
  lia.
Qed.

Lemma launch_sp_le_ed_top : forall v inp mbase (sp brk : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (bv_unsigned sp <= bv_unsigned (ed_top draw))%Z.
Proof.
  intros v inp mbase sp brk draw Hlaunch.
  pose proof (launch_string_base_arith v inp mbase sp brk draw Hlaunch).
  pose proof (Nat2Z.is_nonneg
    (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
  pose proof (Nat2Z.is_nonneg
    (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).
  lia.
Qed.

Lemma stack_max_size_val : stack_max_size = 8388608%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma wrap_mem_below :
  forall v inp mbase ph entry (sp brk : word) draw (addr : word),
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (bv_unsigned addr < bv_unsigned sp - stack_max_size)%Z ->
  wrap_mem inp mbase ph entry sp draw addr = None.
Proof.
  intros v inp mbase ph entry sp brk draw addr Hlau Hlt.
  pose proof stack_max_size_val as Hsms.
  pose proof (launch_sp_le_ed_top v inp mbase sp brk draw Hlau) as Htop.
  pose proof (Z.le_max_l (bv_unsigned (ed_top draw) - stack_max_size)
                (bv_unsigned mbase + stack_guard_gap_bytes (in_kernel inp))) as Hmax.
  unfold wrap_mem, stack_to_mem.
  assert (Hsp : Z.leb (bv_unsigned sp) (bv_unsigned addr) = false)
    by (apply Z.leb_gt; lia).
  rewrite Hsp.
  assert (Hgate : Z.leb (stack_window_lo (in_kernel inp) mbase draw)
                        (bv_unsigned addr) = false)
    by (apply Z.leb_gt; unfold stack_window_lo in *; lia).
  rewrite Hgate. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma flat_map_app' : forall {A B : Type} (f : A -> list B) l1 l2,
  flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof.
  intros A B f l1 l2. induction l1 as [|x xs IH]; cbn; [reflexivity|].
  rewrite IH, app_assoc. reflexivity.
Qed.

Lemma skipn_nth : forall {A : Type} (l : list A) k d, (k < length l)%nat ->
  skipn k l = nth k l d :: skipn (S k) l.
Proof.
  induction l as [|x xs IH]; intros k d Hk; [cbn in Hk; lia|].
  destruct k as [|k']; [reflexivity|].
  cbn [skipn nth]. apply IH. cbn in Hk; lia.
Qed.

Lemma flat_map_split : forall {A B : Type} (f : A -> list B) l k d, (k < length l)%nat ->
  flat_map f l = flat_map f (firstn k l) ++ f (nth k l d) ++ flat_map f (skipn (S k) l).
Proof.
  intros A B f l k d Hk.
  rewrite <- (firstn_skipn k l) at 1.
  rewrite flat_map_app'.
  rewrite (skipn_nth l k d Hk). reflexivity.
Qed.

Lemma flat_map_le8_decomp : forall (l : list word) k, (k < length l)%nat ->
  flat_map word_le8 l =
  flat_map word_le8 (firstn k l) ++ word_le8 (nth k l (Z_to_bv 64 0))
    ++ flat_map word_le8 (skipn (S k) l).
Proof. intros l k Hk. apply (flat_map_split word_le8 l k (Z_to_bv 64 0) Hk). Qed.

Lemma flatten_strings_decomp : forall strs k, (k < length strs)%nat ->
  flatten_strings strs =
  flatten_strings (firstn k strs) ++ (nth k strs [] ++ [Z_to_bv 8 0])
    ++ flatten_strings (skipn (S k) strs).
Proof.
  intros strs k Hk.
  apply (flat_map_split (fun s => s ++ [Z_to_bv 8 0]) strs k [] Hk).
Qed.

Lemma total_arg_bytes_cons : forall s l,
  total_arg_bytes_nat (s :: l) = (length s + 1 + total_arg_bytes_nat l)%nat.
Proof. reflexivity. Qed.

Lemma total_arg_bytes_firstn_le : forall k l,
  (total_arg_bytes_nat (firstn k l) <= total_arg_bytes_nat l)%nat.
Proof.
  induction k as [|k IH]; intros l.
  - change (total_arg_bytes_nat (firstn 0 l)) with 0%nat. lia.
  - destruct l as [|s rest]; [cbn; lia|].
    cbn [firstn]. rewrite !total_arg_bytes_cons. specialize (IH rest). lia.
Qed.

Lemma total_arg_bytes_firstn_within : forall (l : list (list byte)) k,
  (k < length l)%nat ->
  (total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1
   <= total_arg_bytes_nat l)%nat.
Proof.
  intros l. induction l as [|s rest IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k'].
  - cbn [firstn nth]. change (total_arg_bytes_nat []) with 0%nat.
    rewrite total_arg_bytes_cons. lia.
  - cbn [firstn nth]. rewrite !total_arg_bytes_cons.
    specialize (IH k' ltac:(cbn in Hk; lia)). lia.
Qed.

Lemma natN_le : forall n m, (n <= m)%nat -> (N.of_nat n <= N.of_nat m)%N.
Proof. intros n m H. lia. Qed.

(* [comment removed for export] *)
Lemma of_nat_131071 : Z.of_nat 131071 = 131071%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma of_nat_2097152 : Z.of_nat 2097152 = 2097152%Z.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_Z2bv_lt : forall z, (0 <= z)%Z -> (z < 2 ^ 64)%Z ->
  bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z H0 H1. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  apply Z.mod_small. lia.
Qed.

Lemma word_add_nat_Z2bv : forall (a : word) (n : nat),
  a + nat_to_word n = Z_to_bv 64 (bv_unsigned a + Z.of_nat n).
Proof.
  intros a n. apply bv_eq. unfold nat_to_word.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  apply Zplus_mod_idemp_r.
Qed.

Lemma word_sub_nat : forall (a : word) (n : nat),
  a - nat_to_word n = Z_to_bv 64 (bv_unsigned a - Z.of_nat n).
Proof.
  intros a n. apply bv_eq. unfold nat_to_word.
  rewrite bv_sub_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  apply Zminus_mod_idemp_r.
Qed.

Definition cat_struct_size (av ev : list (list byte)) : nat :=
  (8 * block_items av ev)%nat.

Definition cat_string_base (top : word) (av ev : list (list byte))
    (execfn : list byte) : word :=
  string_base_addr top av ev execfn.

Definition cat_env_base (top : word) (av ev : list (list byte))
    (execfn : list byte) : word :=
  cat_string_base top av ev execfn + nat_to_word (total_arg_bytes_nat av).

Definition cat_argv_ptr (top : word) (av ev : list (list byte))
    (execfn : list byte) (k : nat) : word :=
  nth k (fst (string_addrs (cat_string_base top av ev execfn) av)) (Z_to_bv 64 0).

Definition cat_struct_prefix (top : word) (av ev : list (list byte))
    (execfn : list byte) : list byte :=
  word_le8 (len_word av)
  ++ flat_map word_le8 (fst (string_addrs (cat_string_base top av ev execfn) av))
  ++ word_le8 (Z_to_bv 64 0)
  ++ flat_map word_le8 (fst (string_addrs (cat_env_base top av ev execfn) ev))
  ++ word_le8 (Z_to_bv 64 0).

Definition byte_at (s : list byte) (k : nat) : byte :=
  nth k (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0).

Definition pend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
    : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := Some (Z_to_bv 64 64);
     ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}.

End WithFP.
