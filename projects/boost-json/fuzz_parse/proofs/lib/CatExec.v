(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cat_struct_size : ltac2:(zQ "40!l9!h9!jc!o2>2av@1$0@1$0@1$2@1$1#8>2ev@1$0@1$0@1$2@1$1#8$3") := ltac2:(zQ "70!l9!jt8!h9!jc!hte!jvd!kg4\2av@1$0@1$0@1$3@1$2#8\2ev@1$0@1$0@1$3@1$2#8@2$1@2$1@2$1N8@2$5@2$1@2$4@1$0@1$3@1$2#8^2N1N8@2$5@2$1@2$4@1$0@1$3@1$2#8^1N1N8$6").  (* [comment removed for export] *)

Definition cat_string_base : ltac2:(zQ "30!l9!h9!jc>2sp@1$2@1$1#k0>2av@1$0@1$0@1$2@1$1#8>2ev@1$0@1$0@1$2@1$1#8@1$2@1$1#k0") := ltac2:(zQ "60!l9!h9!jc!kh1!ki0!kj3\2sp@1$2@1$1#k0\2av@1$0@1$0@1$2@1$1#8\2ev@1$0@1$0@1$2@1$1#8@3$5@1$1#k0^3@1$3@2$4^2^1").

Definition cat_env_base : ltac2:(zQ "30!l9!h9!jc>2sp@1$2@1$1#k0>2av@1$0@1$0@1$2@1$1#8>2ev@1$0@1$0@1$2@1$1#8@1$2@1$1#k0") := ltac2:(zQ "70!l9!h9!jc!kh1!kjc!jtf!kj3\2sp@1$2@1$1#k0\2av@1$0@1$0@1$2@1$1#8\2ev@1$0@1$0@1$2@1$1#8@3$6@1$1#k0@3$4^3^2^1@1$3@1$5^2").

(* [comment removed for export] *)
Definition cat_argv_ptr : ltac2:(zQ "40!l9!h9!jc!o2>2sp@1$2@1$1#k0>2av@1$0@1$0@1$2@1$1#8>2ev@1$0@1$0@1$2@1$1#8>1k$3@1$2@1$1#k0") := ltac2:(zQ "90!h9!jc!l9!kkf!o2!jl8!kl5!kjc!jm8\2sp@1$1@1$0#k0\2av@1$2@1$2@1$1@1$0#8\2ev@1$2@1$2@1$1@1$0#8\1k$4@4$5@1$1@1$0#k0^1@3$3@1$2@1$1@1$0#k0@1$1@1$0#k0@2$6@3$7^4^3^2^3@2$8@1$0#k0Z").

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

Lemma cat_argv_ptr_offset : ltac2:(zQ "d0!h9!l9!jc!hte!o2!nd!jj1!jke!kh1!km5!kjc!jtf!kj3>2sp@1$2@1$0#k0>2av@1$1@1$1@1$2@1$0#8>2ev@1$1@1$1@1$2@1$0#8>1k$4>0@2$6^1@2$3@1$1@1$2@1$0#8^3@3$5@1$2@1$0#k0@4$9^5^4^3^2@3$c@1$0#k0@3$a^5^4^3@1$8@1$b@3$7@1$1@1$2@1$0#8^2^4").
Proof. intros. unfold cat_argv_ptr. apply nth_string_addrs. assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cat_struct_prefix : ltac2:(zQ "40!h9!jc!l9!kn5>2ph$3>2sp@1$1@1$0#k0>2av@1$2@1$2@1$1@1$0#8>2ev@1$2@1$2@1$1@1$0#8>3uid@1$1@1$0#k0>2hw@1$1@1$0#k0@1$2@1$1@1$0#8") := ltac2:(zQ "f0!h9!jc!l9!jh3!iu8!kkf!kl5!jg7!jm8!ko0!kn5!koc!kpd!kqb!kjc\2ph$a\2sp@1$1@1$0#k0\2av@1$2@1$2@1$1@1$0#8\2ev@1$2@1$2@1$1@1$0#8\3uid@1$1@1$0#k0\2hw@1$1@1$0#k0@3$3@1$1@1$0#8@1$4@2$9@1$2@1$1@1$0#8^4@3$3@1$1@1$0#8@4$7@1$1@1$0#k0@1$1@1$0#8$4@3$5@1$2@1$1@1$0#k0@1$1@1$0#k0@2$6@3$e^5^4^3^4@3$3@1$1@1$0#8@1$4@2$8@1$0#k0Z@3$3@1$1@1$0#8@4$7@1$1@1$0#k0@1$1@1$0#8$4@3$5@1$2@1$1@1$0#k0@1$1@1$0#k0@2$6@3$d^5^4^3^3@3$3@1$1@1$0#8@1$4@2$8@1$0#k0Z@4$c^6@3$b^5^4^3^2^1").

Lemma length_cat_struct_prefix : ltac2:(zQ "90!h9!jc!l9!hte!o2!nd!kn5!krb!ki0>2ph$6>2sp@1$1@1$0#k0>2av@1$2@1$2@1$1@1$0#8>2ev@1$2@1$2@1$1@1$0#8>3uid@1$1@1$0#k0>2hw@1$1@1$0#k0@3$5$4@2$3@1$1@1$0#8@6$7^6^5^4^3^2^1@2$8^4^3").
Proof.
  intros ph sp av ev uid hw. unfold cat_struct_prefix, cat_struct_size.
  rewrite !length_app, !length_flat_map_le8, !length_string_addrs_fst,
    !length_n_to_le_8, length_auxv_bytes.
  lia.
Qed.

(* [comment removed for export] *)
Lemma bsb_argv_prefix : ltac2:(zQ "f0!h9!jc!l9!jh3!iu8!kkf!nd!kt1!ko0!kn5!kt6!ku3!kl5!kjc!jg7>2ph$9>2sp@1$1@1$0#k0>2av@1$2@1$2@1$1@1$0#8>2ev@1$2@1$2@1$1@1$0#8>3uid@1$1@1$0#k0>2hw@1$1@1$0#k0>3rnd$a@2$7@1$2@1$1@1$0#8\4tail@1$2@1$1@1$0#8@3$6@1$2@1$1@1$0#8@7$b^8^7^6^5^4^3^2@3$3@1$1@1$0#8@1$4@2$8@1$2@1$1@1$0#8^6@3$3@1$1@1$0#8@4$e@1$1@1$0#k0@1$1@1$0#8$4@3$5@1$2@1$1@1$0#k0@1$1@1$0#k0@2$c@3$d^7^6^5^6^1").
Proof.
  intros ph sp av ev uid hw rnd. unfold build_stack_bytes.
  rewrite (string_addrs_pair av). cbv beta iota.
  rewrite (string_addrs_pair ev). cbv beta iota.
  eexists. rewrite <- !app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bsb_ptr_k : ltac2:(zQ "h51!h9!jc!l9!jh3!iu8!kkf!kl5!kjc!hte!o2!nd!kt1!jj1!jke!jl8!ko0!kn5!kt6!ku3!jg7!jm8&@3$5@1$2@1$1@1$0#k0@1$1@1$0#k0@2$6@3$7^9^8^7^8>2ph$h0>2sp@1$1@1$0#k0>2av@1$2@1$2@1$1@1$0#8>2ev@1$2@1$2@1$1@1$0#8>1k$9>3uid@1$1@1$0#k0>2hw@1$1@1$0#k0>3rnd$h1>0@2$c^4@2$8@1$2@1$1@1$0#8^6@2$b@1$2@1$1@1$0#8\4post@1$2@1$1@1$0#8@3$a@1$2@1$1@1$0#8@7$h2^a^9^8^7^5^4^3@3$3@1$1@1$0#8@3$3@1$1@1$0#8@1$4@2$f@1$2@1$1@1$0#8^8@4$h3@1$1@1$0#k0@1$1@1$0#8$4@3$d@1$1@1$0#k0^6~0@3$3@1$1@1$0#8@1$4@4$e@1$1@1$0#k0^6~0@2$h4@1$0#k0Z^1").
Proof.
  intros ph sp av ev k uid hw rnd Hk.
  destruct (bsb_argv_prefix ph sp av ev uid hw rnd) as [tail E].
  assert (Hk' : (k < length (fst (string_addrs (cat_string_base sp av ev) av)))%nat)
    by (rewrite length_string_addrs_fst; exact Hk).
  rewrite (flat_map_le8_decomp _ k Hk') in E.
  eexists. rewrite E. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma read_argv_ptr_k : ltac2:(zQ "hb0!h9!jc!l9!hte!kv9!o2!m0!nd!jt8!jvd!jj1!kh1!iu8!kn5!rd!lic!kt6!ku3!lk2!km5!hn0!ik8!im6!il5!ilf!kj3!ht0>2ph$d>4segs@1$2$e>2sp@1$1@1$0#k0>2av@1$2@1$2@1$1@1$0#8>2ev@1$2@1$2@1$1@1$0#8>1k$5>3uid@1$1@1$0#k0>2hw@1$1@1$0#k0>3rnd$h0>0@2$a^4@2$3@1$2@1$1@1$0#8^6>0@2$h6@2$h5@2$ha@1$0#k0^8@1$h7@2$3@1$1@1$0#8@7$h1^a^8^7^6^4^3^2@2$h8+2+k0@3$7@1$6@1$2@1$1@1$0#8@4$h4^a@2$h2^9@7$f^b^9^8^7^5^4^3@3$h9@1$0#k0^9@1$b@2$8N8@2$9N8^6N8@2$4@1$2@1$1@1$0#8@1$c@4$h3^9^8^7^6").
Proof.
  intros ph segs sp av ev k uid hw rnd Hk Hnw.
  destruct (bsb_ptr_k ph sp av ev k uid hw rnd Hk) as [post E].
  pose proof (read_at_offset_image segs ph sp av ev uid hw rnd
    (word_le8 (len_word av)
      ++ flat_map word_le8 (firstn k (fst (string_addrs (cat_string_base sp av ev) av))))
    (word_le8 (nth k (fst (string_addrs (cat_string_base sp av ev) av)) (Z_to_bv 64 0)))
    post 8%nat E (length_n_to_le_8 _) Hnw) as H'.
  assert (Hlen : length (word_le8 (len_word av)
      ++ flat_map word_le8 (firstn k (fst (string_addrs (cat_string_base sp av ev) av))))
    = (8 + 8 * k)%nat).
  { rewrite length_app, length_n_to_le_8, length_flat_map_le8, firstn_length_le;
      [reflexivity | rewrite length_string_addrs_fst; lia]. }
  rewrite Hlen in H'.
  rewrite H'. unfold cat_argv_ptr. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bsb_strings_split : ltac2:(zQ "b0!h9!jc!l9!jh3!nd!kt1!kn5!kt6!ku3!jq6!krb>2ph$6>2sp@1$1@1$0#k0>2av@1$2@1$2@1$1@1$0#8>2ev@1$2@1$2@1$1@1$0#8>3uid@1$1@1$0#k0>2hw@1$1@1$0#k0>3rnd$7@2$5@1$2@1$1@1$0#8\4tail@1$2@1$1@1$0#8@3$4@1$2@1$1@1$0#8@7$8^8^7^6^5^4^3^2@3$3@1$1@1$0#8@6$a^8^7^6^5^4^3@3$3@1$1@1$0#8@1$9^6^1").
Proof.
  intros ph sp av ev uid hw rnd. unfold build_stack_bytes, cat_struct_prefix, cat_env_base, cat_string_base.
  rewrite (string_addrs_pair av). cbv beta iota.
  rewrite (string_addrs_pair ev). cbv beta iota.
  eexists. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma bsb_byte_k : ltac2:(zQ "h50!h9!jc!l9!jh3!hte!o2!jr9!nd!kt1!jrf!ll2!jt8!jj1!jke!jl8!kn5!kt6!ku3!ki0!jtf!jm8>2ph$f>2sp@1$1@1$0#k0>2av@1$2@1$2@1$1@1$0#8>2ev@1$2@1$2@1$1@1$0#8>1k$5>3uid@1$1@1$0#k0>2hw@1$1@1$0#k0>3rnd$h0>0@2$c^4@2$4@1$2@1$1@1$0#8^6@2$8@1$2@1$1@1$0#8\3pre@1$2@1$1@1$0#8@2$8@1$2@1$1@1$0#8\4post@1$2@1$1@1$0#8@2$a@3$7@1$2@1$1@1$0#8@7$h1^b^a^9^8^6^5^4@3$3@1$1@1$0#8^2@3$3@1$1@1$0#8@3$3@1$1@1$0#8@4$e@1$2@1$1@1$0#8^7^9@1$6@1$1@1$0#8@3$9@1$1@1$0#8@2$h4@1$0#8Z@1$6@1$1@1$0#8^1@3$7$5@2$4@1$1@1$0#8^2@2$b@2$h2^9^8@1$h3@3$d@1$2@1$1@1$0#8^7^9").
Proof.
  intros ph sp av ev k uid hw rnd Hk.
  destruct (bsb_strings_split ph sp av ev uid hw rnd) as [tail E].
  rewrite (flatten_strings_decomp av k Hk) in E.
  exists (cat_struct_prefix ph sp av ev uid hw ++ flatten_strings (firstn k av)).
  eexists.
  split.
  - rewrite E. rewrite <- !app_assoc. reflexivity.
  - rewrite length_app, length_cat_struct_prefix, length_flatten_strings. reflexivity.
Qed.

Lemma read_argv_byte_k : ltac2:(zQ "he0!h9!jc!l9!jr9!hte!jl8!jrf!o2!jm8!kv9!jh3!m0!nd!jv7!jj1!kh1!kn5!rd!lic!kt6!ku3!lk2!km5!hn0!ik8!im6!il5!ilf!kj3!ht0>2ph$h0>4segs@1$2$h1>2sp@1$1@1$0#k0>2av@1$2@1$2@1$1@1$0#8>2ev@1$2@1$2@1$1@1$0#8>1k$7>1j$7>3uid@1$1@1$0#k0>2hw@1$1@1$0#k0>3rnd$h3>0@2$e^5@2$4@1$2@1$1@1$0#8^7>0@2$d^5@2$4@1$1@1$0#8@4$5@1$2@1$1@1$0#8^6^8@1$3@1$1@1$0#8>0@2$h9@2$h8@2$hd@1$0#k0^a@1$ha@2$4@1$1@1$0#8@7$h4^c^a^9^8^5^4^3@2$hb+2+k0@3$c@1$b@1$2@1$1@1$0#8@4$h7^c@2$h5^b@7$h2^d^b^a^9^6^5^4@3$hc@1$0#k0@4$h6^b^a^9^8@1$f^7N1@2$9@1$2@1$1@1$0#8@3$6@1$1@1$0#8@4$5@1$1@1$0#8^7@3$a@1$1@1$0#8@4$5@1$2@1$1@1$0#8^8^a@1$3@1$1@1$0#8@3$6@1$1@1$0#8@2$8@1$0#8Z@1$3@1$1@1$0#8@2$8@1$0#8Z@1$3@1$1@1$0#8").
Proof.
  intros ph segs sp av ev k j uid hw rnd Hk Hj Hnw.
  destruct (bsb_byte_k ph sp av ev k uid hw rnd Hk) as [pre [post [E Hlen]]].
  pose proof (read_byte_at_image segs ph sp av ev uid hw rnd
    pre (nth k av [] ++ [Z_to_bv 8 0]) post j E) as H'.
  rewrite Hlen in H'.
  replace (cat_argv_ptr sp av ev k + nat_to_word j)
    with (sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av) + j)).
  2:{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
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
