(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef); ported to LPS 727298f3: statements written out as text, lemmas added for the revision, the launch input as a ProcInput. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import ExitSim PropExec CatSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14listk16option37Corelib4Init5Logicm92eqk13nat3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeo87Segment3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticss7dmachine_states76ms_mems7h1ms_read_bytes_auxs76ms_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hj53rdnhj57seg_rom3h5LinuxProcessSemanticsfLinuxProcessSem6BvBaseho2bword_to_nats7dms_read_byteshfbbv_unsignedk16length79OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec4FPX1~~~~~~hu76wbytes46Stdlib6ZArith6BinInt1Zij03addij02leij06of_natij03powij02ltm92or01Zho2dZ_to_le_bytess7h0word_to_le_bytess7cwrite_to_mem3h5LinuxProcessSemanticsfLinuxProcessSem5Stateiq8estack_max_sizeho28word_le836Stdlib5Lists4Listiv48flat_mapk13appk11S37Corelib4Init5Peanojhd2lt37Corelib5Lists7ListDefjj76firstnjj73nthjj75skipnhf7Z_to_bv3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutjn2fflatten_stringsk13nilk14cons37Corelib4Init3Natjs63addhj5h3total_arg_bytes_natjhd2lejs63muljn29auxv_sizeho2bnat_to_wordhu7fcat_struct_sizehf6bv_addhu7fcat_string_basek13fstjn2cstring_addrshu7ccat_argv_ptro88PhdrInfoho28len_wordjn2dat_random_ptrjn2aauxv_byteshu7ccat_env_basehu7h1cat_struct_prefixm92exjn29EntryDrawjn2h1build_stack_bytesk14Some3h5LinuxProcessSemanticsfLinuxProcessSem3Runlg0h1entry_stack_imagejn2cstack_to_memm93andhu77byte_atlg0avalid_argvm93notiv42Ink14Nonem91Is7h3Build_machine_states78set_gpr0lg0h0advance_past_svc3h5LinuxProcessSemantics5Riscv7Preludelrf5bvmaphj56fp_csrhj57fp_regshj54mksthj56regupdhj56v_addihf2BVhf4BvWf" s.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma ms_read_bytes_aux_rdn : ltac2:(zQ "d0!h9!jc!l9!m0!nd!o2!rd!ve!hge!hh7!hic!hn0!hn7>4segs@1$2$6>2ms$7>1n$5>4addr@1$1@1$0#k0>0@3$4>0@1$1@1$0#k0@1$3@1$1@1$0#8@1$a^3@1$c^4@3$4@1$3@1$2@1$1@1$0#8@3$9^4^2^3@4$b^5@1$8^4^2^3").
Proof.
  intros segs ms n. induction n as [|n IH]; intros addr Hrom; [reflexivity|].
  cbn [ms_read_bytes_aux rdn]. unfold ms_read_byte. rewrite Hrom.
  destruct (ms_mem ms addr) as [b|].
  - rewrite IH by exact Hrom. reflexivity.
  - unfold seg_rom. destruct (memory_read segs addr 1) as [[|b r]|];
      try reflexivity; rewrite IH by exact Hrom; reflexivity.
Qed.

Lemma ms_read_bytes_rdn : ltac2:(zQ "d0!h9!jc!l9!m0!nd!hr1!rd!ve!hge!hs0!hic!hn0!hn7>4segs@1$2$6>2ms$7>4addr@1$1@1$0#k0>3len@1$1@1$0#k0>0@3$4>0@1$1@1$0#k0@1$3@1$1@1$0#8@1$a^3@1$c^4@3$4@1$3@1$2@1$1@1$0#8@3$9^4^3^2@4$b^5@1$8^4^3@1$5^2").
Proof. intros. unfold ms_read_bytes. apply ms_read_bytes_aux_rdn; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint wbytes (m : word -> option byte) (addr : word) (bs : list byte)
    : word -> option byte :=
  match bs with
  | [] => m
  | b :: rest => wbytes (fun a => if bv_eqb a addr then Some b else m a) (addr+1) rest
  end.

(* [comment removed for export] *)
Lemma wbytes_above : ltac2:(zQ "b0!h9!jc!m0!ht0!hte!l9!nd!ii6!ik8!ikf!il5>2bs@1$5@1$1@1$0#8>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>4addr@1$1@1$0#k0>1x@1$1@1$0#k0>0@2$9@2$8@2$3@1$0#k0^2@1$a@2$4@1$1@1$0#8^4@2$3@1$0#k0^1@3$6@1$2@1$1@1$0#8@4$7^4^3^5^2@1^4^2").
Proof.
  induction bs as [|b rest IH]; intros m addr x Hle; [reflexivity|].
  cbn [wbytes length] in *.
  pose proof (u64_range x) as Hx.
  assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z)
    by (apply u_add1; lia).
  rewrite IH by lia.
  cbv beta.
  assert (Hne : bv_eqb x addr = false)
    by (unfold bv_eqb; apply Z.eqb_neq; lia).
  rewrite Hne. reflexivity.
Qed.

Lemma rdn_wbytes_disjoint : ltac2:(zQ "f0!h9!jc!l9!ht0!m0!hn0!ik8!ikf!il5!hte!o2!nd!rd!ii6!ilf>4segs@1$2$c>2bs@1$2@1$1@1$0#8>1m>0@1$1@1$0#k0@1$4@1$1@1$0#8>4addr@1$1@1$0#k0>1a@1$1@1$0#k0>1n$a>0@2$7@2$6@2$3@1$0#k0^3@1$8@2$9@1$1@1$0#8^5@2$3@1$0#k0^2>0@2$7@2$6@2$3@1$0#k0^3@1$8^2@2$e+2+k0@3$b@1$4@1$2@1$1@1$0#8@4$5^8@3$d^6^5^7^4^3@4$5^8^6^4^3").
Proof.
  intros segs bs m addr a n Hle Hnw. apply rdn_ext; [exact Hnw|].
  intros x Hx. apply wbytes_above. lia.
Qed.

(* [comment removed for export] *)
Lemma wbytes_below : ltac2:(zQ "d0!h9!jc!ht0!m0!hte!l9!nd!ii6!ik8!ikf!im6!il5!ilf>2bs@1$5@1$1@1$0#8>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>4addr@1$1@1$0#k0>1x@1$1@1$0#k0>0@2$9@2$8@2$2@1$0#k0^2@1$b@2$4@1$1@1$0#8^4@2$c+2+k0>0@2$a@2$2@1$0#k0^2@2$2@1$0#k0^3@3$6@1$3@1$1@1$0#8@4$7^5^4^6^3@1^5^3").
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

Lemma rdn_wbytes_below : ltac2:(zQ "f0!h9!jc!l9!ht0!m0!hn0!ik8!ikf!il5!hte!o2!nd!rd!ii6!ilf>4segs@1$2$c>2bs@1$2@1$1@1$0#8>1m>0@1$1@1$0#k0@1$4@1$1@1$0#8>4addr@1$1@1$0#k0>1a@1$1@1$0#k0>1n$a>0@2$7@2$6@2$3@1$0#k0^2@1$8^1@2$3@1$0#k0^3>0@2$7@2$6@2$3@1$0#k0^4@1$8@2$9@1$1@1$0#8^6@2$e+2+k0@3$b@1$4@1$2@1$1@1$0#8@4$5^8@3$d^6^5^7^4^3@4$5^8^6^4^3").
Proof.
  intros segs bs m addr a n Hle Hnw.
  pose proof (u64_range addr) as Ha.
  apply rdn_ext; [lia|].
  intros x Hx. apply wbytes_below; [exact Hnw|lia].
Qed.

(* [comment removed for export] *)
Lemma rdn_wbytes_out : ltac2:(zQ "h00!h9!jc!ht0!ik8!ikf!il5!l9!hte!m0!hn0!ilf!o2!nd!imc!rd!ii6>4segs@1$6$e>2bs@1$6@1$1@1$0#8>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>4addr@1$1@1$0#k0>1a@1$1@1$0#k0>1n$b>0@2$d@2$4@2$3@2$2@1$0#k0^2@1$5^1@2$2@1$0#k0^3@2$4@2$3@2$2@1$0#k0^3@1$5@2$7@1$1@1$0#8^5@2$2@1$0#k0^2>0@2$4@2$3@2$2@1$0#k0^3@1$5^2@2$a+2+k0>0@2$4@2$3@2$2@1$0#k0^5@1$5@2$7@1$1@1$0#8^7@2$a+2+k0@3$c@1$8@1$6@1$1@1$0#8@4$9^9@3$f^7^6^8^5^4@4$9^9^7^5^4").
Proof.
  intros segs bs m addr a n [Hb|Hd] Hnw Hnw'.
  - apply rdn_wbytes_below; [exact Hb | exact Hnw'].
  - apply rdn_wbytes_disjoint; [exact Hd | exact Hnw].
Qed.

Lemma length_Z_to_le_bytes : ltac2:(zQ "70!o2!hte!nd!h9!in1!in4!jc>1n$0>1z$4@3$2$0@2$1@1$6@1$3#8@2$5^2^1^2").
Proof.
  induction n as [|n IH]; intro z; [reflexivity|].
  cbn [Z_to_le_bytes length]. rewrite IH. reflexivity.
Qed.

Lemma length_N_to_le_bytes : ltac2:(zQ "60!o2!h9!jc!hte!nd!io5>1n$0>1v@1$2@1$1#k0@3$4$0@2$3@1$2@1$1#8@2$5^2^1^2").
Proof. intros. unfold word_to_le_bytes. apply length_Z_to_le_bytes. Qed.

(* [comment removed for export] *)
Lemma write_to_mem_wbytes : ltac2:(zQ "71!h9!jc!m0!l9!nd!ip9!ii6&>0@1$1@1$0#k0@1$2@1$1@1$0#8>2bs@1$3@1$1@1$0#8>1m~0>4addr@1$1@1$0#k0@3$4~0@3$5^2^1^3@3$6^2^1^3").
Proof.
  induction bs as [|b rest IH]; intros m addr; [reflexivity|].
  cbn [write_to_mem wbytes]. apply IH.
Qed.

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

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stack_max_size_val : ltac2:(zQ "30!nd!in1!it6@3$0$1$2+ogggg0").
Proof. vm_compute. reflexivity. Qed.

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

Lemma flat_map_le8_decomp : ltac2:(zQ "f0!h9!jc!iu8!jg7!jh3!l9!jh9!hte!o2!nd!jj1!jke!jl8!jlf!jm8>1l@1$5@1$1@1$0#k0>1k$8>0@2$a^1@2$7@1$1@1$0#k0^2@3$9@1$5@1$1@1$0#8@4$3@1$1@1$0#k0@1$1@1$0#8$2^3@3$4@1$1@1$0#8@4$3@1$1@1$0#k0@1$1@1$0#8$2@3$b@1$1@1$0#k0^2^3@3$4@1$1@1$0#8@1$2@4$c@1$1@1$0#k0^2^3@2$e@1$0#k0Z@4$3@1$1@1$0#k0@1$1@1$0#8$2@3$d@1$1@1$0#k0@1$6^2^3").
Proof. intros l k Hk. apply (flat_map_split word_le8 l k (Z_to_bv 64 0) Hk). Qed.

Lemma flatten_strings_decomp : ltac2:(zQ "h00!h9!jc!l9!jh3!jq6!jr9!jh9!jrf!hte!o2!nd!jj1!jke!jl8!jlf!jm8>4strs@1$2@1$2@1$1@1$0#8>1k$9>0@2$b^1@2$8@1$2@1$1@1$0#8^2@3$a@1$2@1$1@1$0#8@1$4^3@3$3@1$1@1$0#8@1$4@3$c@1$2@1$1@1$0#8^2^3@3$3@1$1@1$0#8@3$3@1$1@1$0#8@4$d@1$2@1$1@1$0#8^2^3@1$5@1$1@1$0#8@3$7@1$1@1$0#8@2$f@1$0#8Z@1$5@1$1@1$0#8@1$4@3$e@1$2@1$1@1$0#8@1$6^2^3").
Proof.
  intros strs k Hk.
  apply (flat_map_split (fun s => s ++ [Z_to_bv 8 0]) strs k [] Hk).
Qed.

Lemma total_arg_bytes_cons : ltac2:(zQ "90!l9!h9!jc!jt8!jtf!jrf!hte!o2!nd>1s@1$0@1$2@1$1#8>1l@1$0@1$0@1$2@1$1#8@3$8$7@1$4@3$5@1$0@1$2@1$1#8^2^1@2$3@2$3@2$6@1$2@1$1#8^2N1@1$4^1").
Proof. reflexivity. Qed.

Lemma total_arg_bytes_firstn_le : ltac2:(zQ "70!l9!h9!jtf!jc!o2!jv7!jke>1k$4>1l@1$0@1$0@1$3@1$1#8@2$5@1$2@3$6@1$0@1$3@1$1#8^2^1@1$2^1").
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

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cat_struct_size (av ev : list (list byte)) : nat :=
  (8 * block_items av ev)%nat.

Definition cat_string_base (top : word) (av ev : list (list byte))
    (execfn : list byte) : word :=
  string_base_addr top av ev execfn.

Definition cat_env_base (top : word) (av ev : list (list byte))
    (execfn : list byte) : word :=
  cat_string_base top av ev execfn + nat_to_word (total_arg_bytes_nat av).

(* [comment removed for export] *)
Definition cat_argv_ptr (top : word) (av ev : list (list byte))
    (execfn : list byte) (k : nat) : word :=
  nth k (fst (string_addrs (cat_string_base top av ev execfn) av)) (Z_to_bv 64 0).

Definition cat_string_off (rseq : bool) (sp top : word)
    (av ev : list (list byte)) (execfn : list byte) : nat :=
  (block_head_size rseq av ev + block_pad_len rseq sp top av ev execfn)%nat.

Lemma nth_string_addrs : ltac2:(zQ "f0!h9!jc!l9!kkf!hte!o2!nd!jj1!jke!jl8!kh1!kl5!jtf!jm8!kj3>4strs@1$2@1$2@1$1@1$0#8>4base@1$1@1$0#k0>1k$5>0@2$7^1@2$4@1$2@1$1@1$0#8^3@3$6@1$1@1$0#k0@4$9@1$1@1$0#k0^2@3$3@1$2@1$1@1$0#k0@1$1@1$0#k0@2$b^3^4@2$d@1$0#k0Z@3$e@1$0#k0^3@1$a@1$c@3$8@1$2@1$1@1$0#8^2^4").
Proof.
  induction strs as [|s rest IH]; intros base k Hk; [cbn in Hk; lia|].
  rewrite string_addrs_fst_structure.
  destruct k as [|k'].
  - cbn [nth firstn]. change (total_arg_bytes_nat []) with 0%nat.
    rewrite word_add_0. reflexivity.
  - cbn [nth]. rewrite (IH (base + len_word s + 1) k' ltac:(cbn in Hk; lia)).
    cbn [firstn]. rewrite total_arg_bytes_cons.
    rewrite len_word_nat, word1_nat, !nat_to_word_add_merge.
    f_equal. f_equal. lia.
Qed.

Lemma cat_argv_ptr_offset : forall top av ev execfn k, (k < length av)%nat ->
  cat_argv_ptr top av ev execfn k
  = cat_string_base top av ev execfn
    + nat_to_word (total_arg_bytes_nat (firstn k av)).
Proof. intros. unfold cat_argv_ptr. apply nth_string_addrs. assumption. Qed.

Lemma u_cat_string_base : forall v inp mbase (sp brk : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  bv_unsigned (cat_string_base (ed_top draw) (in_argv inp) (in_envp inp)
                 (in_execfn inp))
  = (bv_unsigned (ed_top draw) - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                   (in_execfn inp)))%Z.
Proof.
  intros v inp mbase sp brk draw Hlaunch.
  pose proof (launch_string_base_arith v inp mbase sp brk draw Hlaunch) as HA.
  pose proof (u64_range sp). pose proof (u64_range (ed_top draw)).
  pose proof (Nat2Z.is_nonneg
    (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
  unfold cat_string_base, string_base_addr. rewrite word_sub_nat.
  assert (Hz : (0 <= bv_unsigned (ed_top draw)
                     - Z.of_nat (8 + launch_string_bytes (in_argv inp)
                                       (in_envp inp) (in_execfn inp))
                < 2 ^ 64)%Z).
  { rewrite Nat2Z.inj_add. change (Z.of_nat 8) with 8%Z. lia. }
  rewrite (u_Z2bv_lt _ (proj1 Hz) (proj2 Hz)).
  rewrite Nat2Z.inj_add. change (Z.of_nat 8) with 8%Z. lia.
Qed.

Lemma cat_string_base_offset : forall v inp mbase (sp brk : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  cat_string_base (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp)
  = sp + nat_to_word (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
                        (in_argv inp) (in_envp inp) (in_execfn inp)).
Proof.
  intros v inp mbase sp brk draw Hlaunch.
  pose proof (launch_string_base_arith v inp mbase sp brk draw Hlaunch) as HA.
  pose proof (u_cat_string_base v inp mbase sp brk draw Hlaunch) as Hu.
  pose proof (u64_range sp). pose proof (u64_range (ed_top draw)).
  apply bv_eq. rewrite Hu, word_add_nat_Z2bv.
  unfold cat_string_off, block_pad_len.
  rewrite u_Z2bv_lt
    by (rewrite Nat2Z.inj_add; rewrite Z2Nat.id by lia; lia).
  rewrite Nat2Z.inj_add. rewrite Z2Nat.id by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cat_struct_prefix (top : word) (av ev : list (list byte))
    (execfn : list byte) : list byte :=
  word_le8 (len_word av)
  ++ flat_map word_le8 (fst (string_addrs (cat_string_base top av ev execfn) av))
  ++ word_le8 (Z_to_bv 64 0)
  ++ flat_map word_le8 (fst (string_addrs (cat_env_base top av ev execfn) ev))
  ++ word_le8 (Z_to_bv 64 0).

Lemma length_cat_struct_prefix : forall top av ev execfn,
  length (cat_struct_prefix top av ev execfn) = cat_struct_size av ev.
Proof.
  intros top av ev execfn.
  unfold cat_struct_prefix, cat_struct_size, block_items.
  rewrite !length_app, !length_flat_map_le8, !length_string_addrs_fst,
    !length_n_to_le_8.
  lia.
Qed.

Definition cat_block_head (la : LaunchAuxv) (ph : PhdrInfo)
    (entry sp top : word) (av ev : list (list byte)) (execfn : list byte)
    (uid gid hw : word) (draw : EntryDraw) : list byte :=
  block_below_random la ph entry sp top av ev execfn uid gid hw
  ++ at_random_bytes (ed_random draw)
  ++ repeat (Z_to_bv 8 0) (block_pad_len (la_rseq la) sp top av ev execfn).

Lemma length_cat_block_head :
  forall la ph entry sp top av ev execfn uid gid hw draw,
  length (cat_block_head la ph entry sp top av ev execfn uid gid hw draw)
  = cat_string_off (la_rseq la) sp top av ev execfn.
Proof.
  intros la ph entry sp top av ev execfn uid gid hw draw.
  unfold cat_block_head, block_below_random, cat_string_off. cbv zeta.
  rewrite (string_addrs_pair av). cbv beta iota.
  rewrite (string_addrs_pair ev). cbv beta iota.
  rewrite !length_app, !repeat_length, !length_flat_map_le8,
    !length_string_addrs_fst, length_auxv_bytes, length_at_random_bytes,
    !length_n_to_le_8.
  unfold block_head_size, block_items. lia.
Qed.

(* [comment removed for export] *)
Lemma bsb_argv_prefix : forall inp mbase ph entry (sp : word) draw, exists tail,
  entry_stack_image inp mbase ph entry sp draw =
    word_le8 (len_word (in_argv inp))
    ++ flat_map word_le8
         (fst (string_addrs
                 (cat_string_base (ed_top draw) (in_argv inp) (in_envp inp)
                    (in_execfn inp))
                 (in_argv inp)))
    ++ tail.
Proof.
  intros inp mbase ph entry sp draw.
  rewrite entry_stack_image_block.
  unfold build_stack_bytes, cat_string_base. cbv zeta.
  rewrite (string_addrs_pair (in_argv inp)). cbv beta iota.
  rewrite (string_addrs_pair (in_envp inp)). cbv beta iota.
  eexists. rewrite <- !app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bsb_ptr_k : forall inp mbase ph entry (sp : word) draw k,
  (k < length (in_argv inp))%nat -> exists post,
  entry_stack_image inp mbase ph entry sp draw =
    (word_le8 (len_word (in_argv inp))
      ++ flat_map word_le8
           (firstn k (fst (string_addrs
                             (cat_string_base (ed_top draw) (in_argv inp)
                                (in_envp inp) (in_execfn inp))
                             (in_argv inp)))))
    ++ word_le8 (nth k (fst (string_addrs
                               (cat_string_base (ed_top draw) (in_argv inp)
                                  (in_envp inp) (in_execfn inp))
                               (in_argv inp))) (Z_to_bv 64 0))
    ++ post.
Proof.
  intros inp mbase ph entry sp draw k Hk.
  destruct (bsb_argv_prefix inp mbase ph entry sp draw) as [tail E].
  assert (Hk' : (k < length (fst (string_addrs
                   (cat_string_base (ed_top draw) (in_argv inp) (in_envp inp)
                      (in_execfn inp)) (in_argv inp))))%nat)
    by (rewrite length_string_addrs_fst; exact Hk).
  rewrite (flat_map_le8_decomp _ k Hk') in E.
  eexists. rewrite E. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma read_argv_ptr_k : forall segs inp mbase ph entry (sp : word) draw k,
  (k < length (in_argv inp))%nat ->
  (bv_unsigned sp
   + Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw))
     < 2 ^ 64)%Z ->
  rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw))
      (sp + nat_to_word (8 + 8 * k)) 8%nat
  = Some (word_le8 (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
                      (in_execfn inp) k)).
Proof.
  intros segs inp mbase ph entry sp draw k Hk Hnw.
  destruct (bsb_ptr_k inp mbase ph entry sp draw k Hk) as [post E].
  pose proof (read_at_offset_image segs inp mbase ph entry sp draw
    (word_le8 (len_word (in_argv inp))
      ++ flat_map word_le8
           (firstn k (fst (string_addrs
                             (cat_string_base (ed_top draw) (in_argv inp)
                                (in_envp inp) (in_execfn inp))
                             (in_argv inp)))))
    (word_le8 (nth k (fst (string_addrs
                             (cat_string_base (ed_top draw) (in_argv inp)
                                (in_envp inp) (in_execfn inp))
                             (in_argv inp))) (Z_to_bv 64 0)))
    post 8%nat E (length_n_to_le_8 _) Hnw) as H'.
  assert (Hlen : length (word_le8 (len_word (in_argv inp))
      ++ flat_map word_le8
           (firstn k (fst (string_addrs
                             (cat_string_base (ed_top draw) (in_argv inp)
                                (in_envp inp) (in_execfn inp))
                             (in_argv inp)))))
    = (8 + 8 * k)%nat).
  { rewrite length_app, length_n_to_le_8, length_flat_map_le8, firstn_length_le;
      [reflexivity | rewrite length_string_addrs_fst; lia]. }
  rewrite Hlen in H'.
  rewrite H'. unfold cat_argv_ptr. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bsb_strings_split : forall inp mbase ph entry (sp : word) draw, exists tail,
  entry_stack_image inp mbase ph entry sp draw
  = cat_block_head (launch_auxv inp sp mbase) ph entry sp (ed_top draw)
      (in_argv inp) (in_envp inp) (in_execfn inp)
      (in_uid inp) (in_gid inp) (in_hwcap inp) draw
    ++ flatten_strings (in_argv inp) ++ tail.
Proof.
  intros inp mbase ph entry sp draw.
  rewrite entry_stack_image_block, build_stack_bytes_split_random.
  unfold cat_block_head, block_above_random.
  eexists. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma bsb_byte_k : forall inp mbase ph entry (sp : word) draw k,
  (k < length (in_argv inp))%nat -> exists pre post,
  entry_stack_image inp mbase ph entry sp draw
  = pre ++ (nth k (in_argv inp) [] ++ [Z_to_bv 8 0]) ++ post
  /\ length pre
     = (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
          (in_argv inp) (in_envp inp) (in_execfn inp)
        + total_arg_bytes_nat (firstn k (in_argv inp)))%nat.
Proof.
  intros inp mbase ph entry sp draw k Hk.
  destruct (bsb_strings_split inp mbase ph entry sp draw) as [tail E].
  rewrite (flatten_strings_decomp (in_argv inp) k Hk) in E.
  exists (cat_block_head (launch_auxv inp sp mbase) ph entry sp (ed_top draw)
            (in_argv inp) (in_envp inp) (in_execfn inp)
            (in_uid inp) (in_gid inp) (in_hwcap inp) draw
          ++ flatten_strings (firstn k (in_argv inp))).
  eexists.
  split.
  - rewrite E. rewrite <- !app_assoc. reflexivity.
  - rewrite length_app, length_cat_block_head, length_flatten_strings.
    reflexivity.
Qed.

Lemma read_argv_byte_k :
  forall v segs inp mbase ph entry (sp brk : word) draw k j,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (k < length (in_argv inp))%nat ->
  (j <= length (nth k (in_argv inp) []))%nat ->
  rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw))
      (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k
       + nat_to_word j) 1%nat
  = Some [nth j (nth k (in_argv inp) [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)].
Proof.
  intros v segs inp mbase ph entry sp brk draw k j Hlaunch Hk Hj.
  pose proof (entry_stack_image_no_wrap v inp mbase ph entry sp brk draw Hlaunch)
    as Hnw.
  destruct (bsb_byte_k inp mbase ph entry sp draw k Hk) as [pre [post [E Hlen]]].
  pose proof (read_byte_at_image segs inp mbase ph entry sp draw
    pre (nth k (in_argv inp) [] ++ [Z_to_bv 8 0]) post j E) as H'.
  rewrite Hlen in H'.
  replace (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
             (in_execfn inp) k + nat_to_word j)
    with (sp + nat_to_word
                 (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
                    (in_argv inp) (in_envp inp) (in_execfn inp)
                  + total_arg_bytes_nat (firstn k (in_argv inp)) + j)).
  2:{ rewrite (cat_argv_ptr_offset _ _ _ _ k Hk),
        (cat_string_base_offset v inp mbase sp brk draw Hlaunch).
      rewrite !nat_to_word_add_merge. f_equal. f_equal. lia. }
  apply H'; [rewrite length_app; cbn [length]; lia | exact Hnw].
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

Definition byte_at : ltac2:(zQ "40!h9!jc!l9!o2>1s@1$2@1$1@1$0#8>1k$3@1$1@1$0#8") := ltac2:(zQ "90!h9!jc!jm8!jh3!jrf!l9!o2!jr9!jl8\1s@1$5@1$1@1$0#8\1k$6@4$8@1$1@1$0#8^1@3$3@1$1@1$0#8^2@3$4@1$1@1$0#8@2$2@1$0#8Z@1$7@1$1@1$0#8@2$2@1$0#8Z").

Lemma nth_lt_byte_at : ltac2:(zQ "a0!h9!jc!hte!l9!o2!nd!jj1!jl8!ll8!jm8>1s@1$3@1$1@1$0#8>1j$4>0@2$6^1@2$2@1$1@1$0#8^2@3$5@1$1@1$0#8@2$8^3^2@4$7@1$1@1$0#8^2^3@2$9@1$0#8Z").
Proof. intros s j Hj. unfold byte_at. apply app_nth1. exact Hj. Qed.

Lemma byte_at_len : ltac2:(zQ "70!h9!jc!hte!l9!nd!ll8!jm8>1s@1$3@1$1@1$0#8@3$4@1$1@1$0#8@2$5^1@2$2@1$1@1$0#8^1@2$6@1$0#8Z").
Proof.
  intros s. unfold byte_at. rewrite app_nth2 by lia.
  rewrite Nat.sub_diag. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma valid_argv_len : ltac2:(zQ "70!l9!h9!jc!hte!lm3!ikf!il5>2av@1$0@1$0@1$2@1$1#8>0@1$4^1@2$5@1$6@2$3@1$0@1$2@1$1#8^2+kg0").
Proof. intros av [Hlen _]. lia. Qed.

Lemma valid_argv_str_len : ltac2:(zQ "b0!h9!jc!l9!hte!o2!jr9!jj1!jl8!lm3!ikf!il5>2av@1$2@1$2@1$1@1$0#8>1k$4>0@1$8^2>0@2$6^2@2$3@1$2@1$1@1$0#8^3@2$9@1$a@2$3@1$1@1$0#8@4$7@1$2@1$1@1$0#8^3^4@1$5@1$1@1$0#8+hvvvf").
Proof.
  intros av k [_ [_ [Hstr _]]] Hk.
  rewrite Forall_forall in Hstr.
  specialize (Hstr _ (nth_In av [] Hk)). exact Hstr.
Qed.

Lemma valid_argv_str_nz : ltac2:(zQ "c0!h9!jc!l9!hte!o2!jr9!ln1!jj1!jl8!lm3!ln7!jm8>2av@1$2@1$2@1$1@1$0#8>1k$4>0@1$9^2>0@2$7^2@2$3@1$2@1$1@1$0#8^3@1$6@3$a@1$1@1$0#8@2$b@1$0#8Z@4$8@1$2@1$1@1$0#8^3^4@1$5@1$1@1$0#8").
Proof.
  intros av k [_ [_ [_ [Hnz _]]]] Hk.
  rewrite Forall_forall in Hnz. apply Hnz. apply nth_In. exact Hk.
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

(* [comment removed for export] *)
Lemma adv_set : ltac2:(zQ "h21!h9!jc!m0!lnd!lo4!nd!lo8!ve!lpf!lqa!lu5!lue!lv8!mg3!mgb!mh5!mhf!mi4&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4regs@2$a@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>2sv@1$2@1$1@1$0#k0>3mem~0>3rom~0>1v@1$1@1$0#k0@3$5$7@1$9@2$8@8$6^6@1$c?2fx^5^4@1$3@1$1@1$0#k0@1$b?2fx^3^2^1@5$d?2fx@3$e^6@3$h0@1$0#5+aKv$4@2$h1@1$0#5+a^1@2$f^5+4^3^2").
Proof.
  intros regs pc sv mem rom v.
  unfold advance_past_svc, set_gpr0, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
End FPX1.
(* [comment removed for export] *)
