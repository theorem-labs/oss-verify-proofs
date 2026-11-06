(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshfbbv_unsigned37Corelib4Init5Logicka3and3h5LinuxProcessSemanticsfLinuxProcessSem5Statem4atwo_pow_6446Stdlib6ZArith6BinInt1Zpf2lepf2lthf2bv01Zka2eqm49errno_retpf3sub37Corelib4Init9Datatypesu04listu06optionu04Someu03natm4eread_bytes_aux37Corelib4Init5Peanohi62le37Corelib5Lists7ListDefhk06firstnm4eread_bytes_map3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasehn2bword_to_natu06lengthpf6of_natm4h2readable_bytes_auxm4ereadable_bytesu04prodm4dgather_iovecsm4dgather_prefixm4aiovs_totalm4fpage_round_up_Zm46in_argka3iff3h5LinuxProcessSemanticsfLinuxProcessSem5Monadije7outcome3h5LinuxProcessSemanticsfLinuxProcessSem5Specsin7csyscall_specm45Modelm4dSyscallEffectm4cSyscallInputm48in_sysno5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Fs5Ioctliu7aioctl_spec4h5LinuxProcessSemanticsfLinuxProcessSem3Sys7Syscalljia5cmd32jia4fd325h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Fs4Openjmfbopenat_specjmfaclose_spec5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Fs9ReadWritejs09read_specjs0bwritev_spec5h5LinuxProcessSemanticsfLinuxProcessSem3Sys6Kernel4Forkkh5h4set_tid_address_spec5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Mm4Mmapkm68brk_speckm6bmunmap_speckm69mmap_spec5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Mm8Mprotectks2dmprotect_specu03nilm47FdEntrym45m_fdsije2Okm47MemCopym45eventm49fd_lookupm49fd_removem49mkEffectUm48with_fdshf7Z_to_bv3h5LinuxProcessSemanticsfLinuxProcessSem2Fsln44pathu04boolm45FdDirm49SockStateu04truem46ENOTTYiu7h0tty_only_request69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7RelSpec~~~~~~lu79nodevnullu04Noneka2exm45m_tidm48with_tidkh5h0PID_MAX_ENVELOPEm48m_vmmapsm46vm_brkkm68brk_r_okkm6abrk_unmapskm69brk_zeroskm6dwith_brk_nextm47vm_mapspf3addu04consu05falseu04pairm49TASK_SIZEm47map_hasm4amap_removem4dmaps_subtractm4cmkVmMapsFullm49page_sizem4avm_init_spm48vm_limitm4cvm_mmap_basem4bvm_noaccessm4bvm_reservedm4cvm_start_brkkm6h3with_mmap_destroyedjia5w_is0pf6modulokm6bmmap_errnos36Stdlib5Lists4Listnqd2Inm46ENOMEMlu7cmmap_err_outu03appka2orm46VmMapsm49alloc_topm4bregion_freem4bwith_vmmapskm6bmmap_anon_bkm6emmap_modeled_bkm6h8mmap_noreserve_backed_okkm6h2mmap_off_aligned_bkm6h1with_mmap_backingkm6fmmap_noaccess_bm4cmap_containskm6h9mmap_fixed_destroyed_nextkm6h5mmap_fixed_noaccess_bkm6h5with_mmap_replacementks2fmprotect_errnoslu7h0mprotect_err_outks2h2mprotect_budget_okks2h9mprotect_grows_conflict_bks2h3mprotect_model_nextks2h2mprotect_modeled_bm46EISDIRm4aaccess_okbhn28len_wordm46FdFileln49file_readln49fs_lookupm49fd_insertm47in_wmemm44m_fsm4erw_count_clamp4h5LinuxProcessSemanticsfLinuxProcessSem3Sys7Uaccesspv9h0delivered_writeshf6bv_addm4h3cstr_access_len_auxm46in_memm48path_maxije9Unmodeledm4beff_copyinsm4cwith_copyinsije3Sysjiaerecord_copyinslu7dafter_copyinsm48alloc_fdjmfdopenat_errnosjmfh0open_result_speclu78open_reslu78open_outjmfh2modeled_open_flagsjmfh0openat_body_speclu7aopen_readsjia7err_retm4bCstrTooLongm4cENAMETOOLONGm4bcstr_resultm49read_cstrm46CstrOkm46ENOENTka3not5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Fs5Nameirq7epath_has_slashjmfh0openat_read_specjmfepath_is_dirrefm4ecap_iovecs_auxm4acap_iovecspv9crw_bytes_maxije4bindije9get_modelije5inputjs08iovcnt32m49FdChannelm45ImpOkm4dimport_iovecsm4h6import_iovecs_accessesm4aiov_import4h5LinuxProcessSemanticsfLinuxProcessSem3Sys4Uapisr8aAT_FDCWD32jmfh2open_ignored_flagspf5ldiff" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_eqb_refl : forall {n : N} (a : bv n), bv_eqb a a = true.
Proof. intros n a. apply bv_eqb_eq. reflexivity. Qed.

Lemma word_unsigned_range : ltac2:(zQ "70!h9!jc!le!p2!r7!rc!s1>1w@1$6@1$0#k0@2$2@2$4Z@2$1@1$0#k0^1@2$5@2$1@1$0#k0^1$3").
Proof.
  intros w. pose proof (bv_unsigned_in_range _ w) as H.
  unfold two_pow_64. unfold bv_modulus in H.
  change (Z.of_N 64) with 64%Z in H. exact H.
Qed.

Lemma errno_ret_unsigned : ltac2:(zQ "80!s6!r7!s9!h9!se!p2!ta!jc>1e$0>0@2$1+1^1>0@2$1^2+vvf@3$2$0@2$7@1$3#k0@1$4^3@2$6$5^3").
Proof.
  intros e H1 H2. unfold errno_ret, two_pow_64.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (Z.of_N 64) with 64%Z.
  replace (- e)%Z with (2 ^ 64 - e + (-1) * 2 ^ 64)%Z by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma read_bytes_aux_prefix : ltac2:(zQ "a0!h9!s1!v8!vf!hg8!hgf!s9!hh5!hja!hl7>1k$5>1n$5>2mp>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a@1$1@1$0#k0>1w@1$2@1$1@1$0#8>0@2$8^5^4>0@3$6@1$3@1$2@1$1@1$0#8@3$7^4^3^5@2$4@1$2@1$1@1$0#8^2@3$6@1$3@1$2@1$1@1$0#8@3$7^5^4^7@2$4@1$2@1$1@1$0#8@3$9@1$1@1$0#8^7^3").
Proof.
  induction k as [|k IH]; intros n mp a w Hk Hw; [reflexivity|].
  destruct n as [|n]; [lia|].
  cbn in Hw. destruct (mp a) as [b|] eqn:Hb; [|discriminate].
  destruct (read_bytes_aux mp (a + 1) n) as [r|] eqn:Hr; [|discriminate].
  inversion Hw; subst w.
  cbn. rewrite Hb. rewrite (IH n mp (a + 1) r ltac:(lia) Hr). reflexivity.
Qed.

Lemma read_bytes_map_prefix : ltac2:(zQ "b0!h9!s1!v8!vf!hg8!s9!hm1!jc!hl7!hq1!r7>2mp>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a@1$1@1$0#k0>3len@1$1@1$0#k0>1k@1$1@1$0#k0>1w@1$2@1$1@1$0#8>0@2$a@2$7@1$0#k0^2@2$7@1$0#k0^3>0@3$5@1$3@1$2@1$1@1$0#8@3$6^6^5^4@2$4@1$2@1$1@1$0#8^2@3$5@1$3@1$2@1$1@1$0#8@3$6^7^6^4@2$4@1$2@1$1@1$0#8@3$8@1$1@1$0#8@1$9^4^3").
Proof.
  intros mp a len k w Hk Hw. rewrite read_bytes_map_eq in *.
  unfold word_to_nat in *.
  apply read_bytes_aux_prefix with (n := Z.to_nat (bv_unsigned len));
    [lia | assumption].
Qed.

Lemma read_bytes_aux_length : ltac2:(zQ "90!h9!s1!v8!hgf!vf!s9!hg8!hr0!hh5>2mp>0@1$1@1$0#k0@1$4@1$1@1$0#8>1k$3>1a@1$1@1$0#k0>1w@1$2@1$1@1$0#8>0@3$5@1$4@1$2@1$1@1$0#8@3$8^4^2^3@2$6@1$2@1$1@1$0#8^1@3$5$3@2$7@1$1@1$0#8^2^4").
Proof.
  intros mp k; induction k as [|k IH]; intros a w Hw; cbn in Hw.
  - inversion Hw. reflexivity.
  - destruct (mp a); [|discriminate].
    destruct (read_bytes_aux mp (a + 1) k) eqn:Hr; [|discriminate].
    inversion Hw; subst. cbn. now rewrite (IH _ _ Hr).
Qed.

Lemma read_bytes_map_length : ltac2:(zQ "b0!h9!s1!v8!vf!s9!hg8!hr0!s6!hm1!hr9!jc>2mp>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a@1$1@1$0#k0>3len@1$1@1$0#k0>1w@1$2@1$1@1$0#8>0@3$4@1$3@1$2@1$1@1$0#8@3$8^4^3^2@2$5@1$2@1$1@1$0#8^1@3$4$7@1$9@2$6@1$1@1$0#8^2@2$a@1$0#k0^3").
Proof.
  intros mp a len w Hw. rewrite read_bytes_map_eq in Hw.
  unfold word_to_nat in Hw.
  rewrite (read_bytes_aux_length _ _ _ _ Hw).
  pose proof (word_unsigned_range len). lia.
Qed.

Lemma readable_bytes_aux_full : ltac2:(zQ "90!h9!s1!v8!vf!s9!hg8!hgf!hh5!hs2>2mp>0@1$1@1$0#k0@1$3@1$1@1$0#8>1k$6>1a@1$1@1$0#k0>1w@1$2@1$1@1$0#8>0@3$4@1$3@1$2@1$1@1$0#8@3$7^4^2^3@2$5@1$2@1$1@1$0#8^1@3$4@1$2@1$1@1$0#8@3$8^5^3^4^2").
Proof.
  intros mp k; induction k as [|k IH]; intros a w Hw; cbn in *.
  - now inversion Hw.
  - destruct (mp a); [|discriminate].
    destruct (read_bytes_aux mp (a + 1) k) eqn:Hr; [|discriminate].
    inversion Hw; subst. now rewrite (IH _ _ Hr).
Qed.

Lemma readable_bytes_full : ltac2:(zQ "80!h9!s1!v8!vf!s9!hg8!hm1!ht8>2mp>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a@1$1@1$0#k0>3len@1$1@1$0#k0>1w@1$2@1$1@1$0#8>0@3$4@1$3@1$2@1$1@1$0#8@3$6^4^3^2@2$5@1$2@1$1@1$0#8^1@3$4@1$2@1$1@1$0#8@3$7^5^4^3^2").
Proof.
  intros. rewrite read_bytes_map_eq in *. rewrite readable_bytes_eq.
  now apply readable_bytes_aux_full.
Qed.

Lemma len_word_unsigned : forall {A} (l : list A),
  (Z.of_nat (length l) < two_pow_64)%Z ->
  bv_unsigned (len_word l) = Z.of_nat (length l).
Proof.
  intros A l Hl. unfold len_word.
  rewrite Z_to_bv_small; [reflexivity|].
  unfold bv_modulus. change (Z.of_N 64) with 64%Z.
  unfold two_pow_64 in Hl. lia.
Qed.

(* [comment removed for export] *)
Lemma gather_prefix_full : ltac2:(zQ "90!h9!s1!v8!vf!s9!hg8!hu9!hv0!ig0>2mp>0@1$1@1$0#k0@1$3@1$1@1$0#8>4iovs@1$2@2$6@1$1@1$0#k0@1$1@1$0#k0>2bs@1$2@1$1@1$0#8>0@3$4@1$3@1$2@1$1@1$0#8@2$7^3^2@2$5@1$2@1$1@1$0#8^1@3$4@1$2@1$1@1$0#8@2$8^4^3^2").
Proof.
  induction iovs as [|[base len] r IH]; intros bs Hg; cbn in *.
  - now inversion Hg.
  - destruct (read_bytes_map mp base len) as [w|] eqn:Hw; [|discriminate].
    destruct (gather_iovecs mp r) as [rest|] eqn:Hr; [|discriminate].
    inversion Hg; subst.
    rewrite (readable_bytes_full _ _ _ _ Hw).
    rewrite (read_bytes_map_length _ _ _ _ Hw), Z.eqb_refl.
    now rewrite (IH _ eq_refl).
Qed.

Lemma gather_iovecs_length : ltac2:(zQ "c0!h9!s1!v8!vf!s9!hg8!hr0!hu9!s6!hv0!ih0!hr9>2mp>0@1$1@1$0#k0@1$3@1$1@1$0#8>4iovs@1$2@2$7@1$1@1$0#k0@1$1@1$0#k0>2bs@1$2@1$1@1$0#8>0@3$4@1$3@1$2@1$1@1$0#8@2$9^3^2@2$5@1$2@1$1@1$0#8^1@3$4$8@1$b@2$6@1$1@1$0#8^2@1$a^3").
Proof.
  induction iovs as [|[base len] r IH]; intros bs Hg; cbn in *.
  - now inversion Hg.
  - destruct (read_bytes_map mp base len) as [w|] eqn:Hw; [|discriminate].
    destruct (gather_iovecs mp r) as [rest|] eqn:Hr; [|discriminate].
    inversion Hg; subst.
    rewrite length_app, Nat2Z.inj_add.
    rewrite (read_bytes_map_length _ _ _ _ Hw), (IH _ eq_refl). reflexivity.
Qed.

Lemma page_round_up_Z_nonneg : ltac2:(zQ "30!r7!s6!ihd>1z$1>0@2$0Z^1@2$0Z@1$2^2").
Proof.
  intros z Hz. unfold page_round_up_Z, page_size.
  apply Z.mul_nonneg_nonneg; [|lia].
  apply Z.div_pos; lia.
Qed.

Lemma page_round_up_Z_mono : ltac2:(zQ "30!s6!ihd!r7>1a$0>1b$0>0@2$2^2^1@2$2@1$1^3@1$1^2").
Proof.
  intros a b H. unfold page_round_up_Z, page_size.
  apply Z.mul_le_mono_nonneg_r; [lia|].
  apply Z.div_le_mono; lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac sys_unfold :=
  unfold record_copyins, with_copyins,
    err_ret, ret_only, errno_from, lowest_fd,
    set_fds, set_vmmaps, forget_vm_range,
    set_stdin, set_fs, set_halted, set_tid,
    get_model, get_fds, get_vmmaps, modify, input, sysno, arg,
    bind, pure, choose, alt, unmodeled, emit in *.

(* [comment removed for export] *)
Lemma Ok_inj {A} : forall (x x' : A) m m' e e',
  Ok x m e = Ok x' m' e' -> x = x' /\ m = m' /\ e = e'.
Proof. intros x x' m m' e e' H. injection H. auto. Qed.

Lemma Ok_Unmodeled {A} : forall (x : A) m e, Ok x m e = Unmodeled -> False.
Proof. intros x m e H. discriminate H. Qed.

Lemma Unmodeled_Ok {A} : forall (x : A) m e, Unmodeled = Ok x m e -> False.
Proof. intros x m e H. discriminate H. Qed.

Lemma Some_inj' {A} : forall (x y : A), Some x = Some y -> x = y.
Proof. intros x y H. injection H. auto. Qed.

Lemma Some_None {A} : forall (x : A), Some x = None -> False.
Proof. intros x H. discriminate H. Qed.

Lemma None_Some {A} : forall (x : A), None = Some x -> False.
Proof. intros x H. discriminate H. Qed.

(* [comment removed for export] *)
Ltac inv_sys :=
  repeat first
  [ progress subst
  | match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    | H : Ok _ _ _ = Ok _ _ _ |- _ => apply Ok_inj in H; destruct H as (? & ? & ?); subst
    | H : Ok _ _ _ = Unmodeled |- _ => exfalso; exact (Ok_Unmodeled _ _ _ H)
    | H : Unmodeled = Ok _ _ _ |- _ => exfalso; exact (Unmodeled_Ok _ _ _ H)
    | H : Some _ = Some _ |- _ => apply Some_inj' in H; subst
    | H : Some _ = None |- _ => exfalso; exact (Some_None _ H)
    | H : None = Some _ |- _ => exfalso; exact (None_Some _ H)
    | H : False |- _ => contradiction
    | H : true = false |- _ => exfalso; exact (Bool.diff_true_false H)
    | H : false = true |- _ => exfalso; exact (Bool.diff_false_true H)
    | H : _ \/ _ |- _ => destruct H
    end
  | progress cbv beta zeta in * ].

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma syscall_spec_29 : ltac2:(zQ "f0!iif!s9!ij8!h9!s6!imc!iq5!ir5!ird!isd!itc!jhc!jle!jm7!jc>1i$9>1m$7>1o@1$5$8>0@3$1$4@2$e@1$3#k0@1$a^3+hd@2$2@3$6^4^3^2@5$b@1$d@2$0^4N0@1$c@2$0^4N1^4^3^2").
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_56 : ltac2:(zQ "e0!iif!s9!ij8!h9!s6!imc!iq5!ir5!ird!isd!itc!jq3!jm7!jc>1i$9>1m$7>1o@1$5$8>0@3$1$4@2$d@1$3#k0@1$a^3+j8@2$2@3$6^4^3^2@6$b@1$c@2$0^4N0@2$0^4N1@2$0^4N2^4^3^2").
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_57 : ltac2:(zQ "e0!s9!ij8!h9!s6!imc!iq5!ir5!ird!isd!iif!itc!jr2!jm7!jc>1i$8>1m$6>1o@1$4$7>0@3$0$3@2$d@1$2#k0@1$a^3+j9@2$1@3$5^4^3^2@4$b@1$c@2$9^4N0^4^3^2").
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_63 : ltac2:(zQ "e0!iif!s9!ij8!h9!s6!imc!iq5!ir5!ird!isd!itc!jv9!jm7!jc>1i$9>1m$7>1o@1$5$8>0@3$1$4@2$d@1$3#k0@1$a^3+jf@2$2@3$6^4^3^2@6$b@1$c@2$0^4N0@2$0^4N1@2$0^4N2^4^3^2").
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_66 : ltac2:(zQ "e0!iif!s9!ij8!h9!s6!imc!iq5!ir5!ird!isd!itc!kg6!jm7!jc>1i$9>1m$7>1o@1$5$8>0@3$1$4@2$d@1$3#k0@1$a^3+k2@2$2@3$6^4^3^2@6$b@1$c@2$0^4N0@2$0^4N1@2$0^4N2^4^3^2").
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_96 : ltac2:(zQ "c0!s9!ij8!h9!s6!imc!iq5!ir5!ird!isd!itc!kkd!jc>1i$8>1m$6>1o@1$4$7>0@3$0$3@2$b@1$2#k0@1$9^3+m0@2$1@3$5^4^3^2@3$a^4^3^2").
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_214 : ltac2:(zQ "d0!s9!ij8!h9!s6!imc!iq5!ir5!ird!isd!iif!itc!kpa!jc>1i$8>1m$6>1o@1$4$7>0@3$0$3@2$c@1$2#k0@1$a^3+t6@2$1@3$5^4^3^2@4$b@2$9^4N0^4^3^2").
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_215 : ltac2:(zQ "d0!iif!s9!ij8!h9!s6!imc!iq5!ir5!ird!isd!itc!kq6!jc>1i$9>1m$7>1o@1$5$8>0@3$1$4@2$c@1$3#k0@1$a^3+t7@2$2@3$6^4^3^2@5$b@2$0^4N0@2$0^4N1^4^3^2").
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_222 : ltac2:(zQ "d0!iif!s9!ij8!h9!s6!imc!iq5!ir5!ird!isd!itc!kr5!jc>1i$9>1m$7>1o@1$5$8>0@3$1$4@2$c@1$3#k0@1$a^3+te@2$2@3$6^4^3^2@9$b@2$0^4N0@2$0^4N1@2$0^4N2@2$0^4N3@2$0^4N4@2$0^4N5^4^3^2").
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_226 : ltac2:(zQ "d0!iif!s9!ij8!h9!s6!imc!iq5!ir5!ird!isd!itc!kva!jc>1i$9>1m$7>1o@1$5$8>0@3$1$4@2$c@1$3#k0@1$a^3+u2@2$2@3$6^4^3^2@6$b@2$0^4N0@2$0^4N1@2$0^4N2^4^3^2").
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma close_outcome : ltac2:(zQ "h92!h9!s1!lgb!hu9!lh1!ird!s9!imc!lhb!hg8!v8!hgf!vf!ij8!li3!li9!ir5!isd!lj3!ljb!lk7!ll3!llf!jr2!lma&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>2fd@1$1@1$0#k0>1i$h1>1m$h0>1e$4>1o@1$7$5>0@3$6@1$c$4@2$h3@1$8^3^5@2$9$4^2@2$d@4$h7^6^5^4^2@3$6@1$7$5^2@4$e$5@6$h5@2$h8@1$0#k0Z@1$2@2$3@1$1@1$0#k0@1$a@1$1@1$0#8~1~1@1$2$f@1$2@2$3@1$1@1$0#k0$b@2$h6@2$h4@1$8^4^6^4@1$2$h2").
Proof.
  intros fd i m e o Hlk. unfold close_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk in *; inv_sys. reflexivity.
  - intros ->. neexists 4. split; [reflexivity|]. rewrite Hlk.
    split; [|reflexivity]. neexists 4. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nodevnull : ltac2:(zQ "10!lh1>1e$0$0") := ltac2:(zQ "71!h9!s1!lpf!lh1!lq7!lqe!lr6&\1p$2\6offset@1$1@1$0#k0^3\1e$3M3\1e$3$3^1\4chan@1$1@1$0#k0^2~0~0~0~0^1\2sk$6^2\2id@1$1@1$0#k0\6writer$4^3\2rd$4\2wr$4^3$5").

Lemma ioctl_tty_outcome : ltac2:(zQ "hc2!h9!s1!lgb!hu9!s9!lh1!ird!imc!hg8!lq7!v8!hgf!vf!ls2!ij8!li3!ls9!li9!ir5!isd!se!lj3!ljb!lhb!ll3!jhc!lt2!mi1&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>2fd@1$1@1$0#k0>3req@1$1@1$0#k0>1i$h3>1m$h2>1e$5>1o@1$7$6>0@3$4@1$c$5@2$h6@1$h7^3^6@2$8$5@1$hb^2>0@3$4$9@1$ha^6$d@2$e@5$h9^8^7^6^5^3@3$4@1$7$6^3@4$f$6@6$h8@1$h4$h0@1$2@2$3@1$1@1$0#k0@1$a@1$1@1$0#8~1~1@1$2$h1@1$2@2$3@1$1@1$0#k0$b^5@1$2$h5").
Proof.
  intros fd req i m e0 o Hlk Hreq. set (e := nodevnull e0) in *.
  assert (ND : e <> FdUrandom) by (subst e; destruct e0; cbn; congruence).
  clearbody e. clear e0.
  unfold ioctl_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk in *;
      destruct e; try (exfalso; eapply ND; reflexivity); rewrite ?Hreq in *; inv_sys; reflexivity.
  - intros ->. neexists 4. split; [reflexivity|]. rewrite Hlk.
    split; [|reflexivity]. destruct e; try (exfalso; eapply ND; reflexivity); rewrite ?Hreq; reflexivity.
Qed.

(* [comment removed for export] *)

Lemma set_tid_fresh_outcome : ltac2:(zQ "ha2!h9!s1!lgb!hu9!ird!le!s9!imc!rc!jc!mie!v8!hgf!vf!mj5!ij8!li3!li9!ir5!isd!lj3!mja!ll3!mk2!mkd!kkd&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1i$h3>1m$h2>1o@1$7$4>0@3$6@1$d@1$1@1$0#k0@1$h5^2@1$a@1$1@1$0#k0@2$f@3$h9^4^3^2@2$e@1$1@1$0#k0\1t@1$1@1$0#k0@2$5@2$5@2$8Z@2$9@1$0#k0^1@2$8@2$9@1$0#k0^1$h8@3$6@1$7$4^3@4$h0$4@6$h6^1@1$2@2$3@1$1@1$0#k0@1$b@1$1@1$0#8~1~1@1$2$h1@1$2@2$3@1$1@1$0#k0$c@2$h7^1^4@1$2$h4").
Proof.
  intros i m o Htid. unfold set_tid_address_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Htid in *; inv_sys.
    eexists; split; [split; eassumption|reflexivity].
  - (intros nd_i1; ndestruct nd_i1 as (t & Ht & ->)). neexists 4. split; [reflexivity|]. rewrite Htid.
    split; [|reflexivity]. neexists 4. split; [exists t; split; [exact Ht|reflexivity]|].
    split; [|reflexivity]. neexists 4. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)

Lemma brk_outcome : ltac2:(zQ "hb0!h9!s1!lgb!ird!hu9!s9!imc!mm2!mmd!lq7!v8!hgf!ls2!le!mj5!ij8!li3!li9!ir5!isd!lj3!ll3!mn6!kpa!mo2!mp0!mpd>3req@1$1@1$0#k0>1i$h3>1m$h2>1o@1$6$3@2$f@4$h7^4^3^2^1@2$e@1$1@1$0#k0\1r@1$1@1$0#k0@2$d@3$5$9@3$h6^3^5^1$c@3$5@1$6$3^2@4$h0$3@6$h5^1@1$2@2$4@1$1@1$0#k0@1$a@1$1@1$0#8@3$h9^5^1@1$8@1$7^3@2$h8^1@1$8@1$7^3@1$2$h1@1$2@2$4@1$1@1$0#k0$b@3$ha^3^5^1@1$2$h4").
Proof.
  intros req i m o. unfold brk_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    eexists; split; [eassumption|reflexivity].
  - (intros nd_i2; ndestruct nd_i2 as (r & Hr & ->)). neexists 4. split; [reflexivity|].
    split; [|reflexivity]. neexists 4. split; [exists r; split; [exact Hr|reflexivity]|].
    split; [|reflexivity]. neexists 4. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma munmap_exact_outcome : ltac2:(zQ "ie2!h9!s1!mm2!jc!lgb!hu9!s9!ird!lq7!imc!ihd!mqe!mr8!lma!mre!ms5!v8!hgf!msd!ls2!ij8!s6!li3!li9!ir5!isd!mt4!lj3!mu0!mua!mv7!ll3!ng7!nh6!mmd!ni2!nif!nja!nk9!nl7!nm5!kq6!nn4!noc!r7!np5&@2$5@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>4addr@1$1@1$0#k0>3len@1$1@1$0#k0>1i$h9>1m$h8>1o@1$9$7>0@3$6$h5@2$id@2$3@1$0#k0^5$i1Z>0@3$6$8@1$ib^5$f>0@2$ic@2$c@2$3@1$0#k0^7@1$a@2$3@1$0#k0^6$ha=1n@1$1@1$0#k0@2$d@1$0#k0@1$a@2$3@1$0#k0^7>0@3$6$8@3$hc@1$b@1$2^6^9^1$h3@2$h4@5$i9^a^9^8^7^6@3$6@1$9$7^6@4$h6$7@6$hf@2$d@1$0#k0Z@1$4@2$5@1$1@1$0#k0@1$h0@1$1@1$0#8~1@3$e~0@4$h2@1$1@1$0#k0@1$1@1$0#k0^a^2~1@1$4$h7@1$4@2$5@1$1@1$0#k0$h1@4$ia^a^2@8$i0@1$i7@1$2^7@2$hd@1$b@1$2^7^a@3$he@1$i6@1$2^7@2$3@1$0#k0^a@2$c@2$3@1$0#k0^a@2$3@1$0#k0^2@1$i8@1$2^7@1$i2@1$2^7@1$i4@1$2^7@1$i5@1$2^7@1$i3@1$2^7^7@1$4$hb").
Proof.
  intros addr len i m o Hal Hlen Hnw. cbv zeta. intros Hhas. unfold munmap_spec.
  rewrite (proj2 (Z.eqb_eq _ _) Hal), Hlen. cbn [negb orb].
  rewrite (proj2 (Z.ltb_ge _ _) Hnw). sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hhas in *; inv_sys. reflexivity.
  - intros ->. neexists 4. split; [reflexivity|]. rewrite Hhas.
    split; [|reflexivity]. neexists 4. split; [reflexivity|].
    split; [|reflexivity]. neexists 4. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_err_out : ltac2:(zQ "30!imc!ir5!ird>1m$1>1o@1$0$2P") := ltac2:(zQ "h42!h9!s1!lgb!hu9!s6!ird!imc!v8!hgf!le!s9!mj5!li3!li9!ir5!se!lj3!ll3!npe!ns0&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0\1m$e\1o@1$6$5@2$b$4\1e$4@2$9@3$h3$4^1$h2@3$a@1$6$5^2@4$c$5@6$h1@1$f^1@1$2@2$3@1$1@1$0#k0@1$7@1$1@1$0#8~1~1@1$2$d@1$2@2$3@1$1@1$0#k0$8^3@1$2$h0").

Lemma mmap_err_out_enomem : ltac2:(zQ "h22!h9!s1!lgb!hu9!ird!imc!v8!hgf!s9!ij8!li3!ns6!li9!ir5!se!lj3!ll3!nsf&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1m$d>1o@1$5$4@2$9@2$h1^2^1@3$8@1$5$4^1@4$a$4@6$h0@1$e$b@1$2@2$3@1$1@1$0#k0@1$6@1$1@1$0#8~1~1@1$2$c@1$2@2$3@1$1@1$0#k0$7^2@1$2$f").
Proof.
  intros m o. unfold mmap_err_out, mmap_errnos. split.
  - (intros nd_i3; ndestruct nd_i3 as (e & [<- | []] & ->)). reflexivity.
  - intros ->. exists ENOMEM. split; [left; reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma mmap_rw_outcome : ltac2:(zQ "j83!h9!s1!s9!hu9!lq7!lgb!ls2!le!jc!ird!mre!msd!s6!imc!mqe!nl7!ntf!ms5!v8!hgf!mj5!ij8!nu5!li3!li9!ir5!isd!nua!nv3!lj3!mm2!ll3!ng7!ihd!nh6!nvf!mmd!ni2!nif!nja!nk9!nm5!ogd!ohb!oia!ojc!ol9!kr5!on0!noc!nsf!mr8!r7!rc!np5!lma&@2$3@1$1@1$0#k0@1$1@1$0#k0&@4$b@1$1@1$0#k0@1$1@1$0#k0^1^2&@1$5~0>4addr@1$1@1$0#k0>3len@1$1@1$0#k0>4prot@1$1@1$0#k0>5flags@1$1@1$0#k0>2fd@1$1@1$0#k0>3off@1$1@1$0#k0>1i$ha>1m$h9>1o@1$d$9>0@3$2$4@1$ie^4$6>0@3$2$4@1$ib^7$6>0@3$2$4@1$j1^a$h1>0@3$2$4@3$ic^a^9^7$6=1h$hb@1$he^6=2nZ$c@1$i1@2$8@1$0#k0^d=1n@1$1@1$0#k0@2$j7@1$0#k0^1@2$h5@9$if^h0^f^e^d^c^b^a^9^8@2$h6@2$j2^9^8@2$h4@1$1@1$0#k0\1a@1$1@1$0#k0@2$7@2$7@3$2$c@2$j6@2$8@1$0#k0^1$i2Z@2$7@2$j5Z@2$8@1$0#k0^1@2$7@2$j4@2$j3@2$8@1$0#k0^1^3@1$hc^4@2$7@3$2$4@3$i3@3$h0~0@1$f^4@1$e^4^1^2$6@3$2$4@3$id^e^a^3$6@3$2@1$d$9^9@4$h7$9@6$hf^1@1$5@2$3@1$1@1$0#k0@1$h2@1$1@1$0#8@3$a~0~1~2~2@1$5$h8@1$5@2$3@1$1@1$0#k0$h3@4$j0^e^1^2@2$ia@8$i0@1$f^4@3$a~0~1@1$e^4@1$i8^4@1$i9^4@1$i4^4@1$i6^4@1$i7^4@1$i5^4^a@1$5$hd").
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod. cbv zeta. unfold mmap_spec.
  rewrite Hoff, Hanon, Hlen, Hmod. cbn [negb]. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. eexists; split; [|reflexivity]. repeat split; assumption.
  - intros [(e & He & ->) | (a & Ha & ->)].
    + left. neexists 4. split; [exists e; split; [exact He|reflexivity]|].
      split; reflexivity.
    + right. neexists 4; (split; [reflexivity|]); (split; [|reflexivity]).
      neexists 4. split; [exists a; split; [exact Ha|reflexivity]|].
      split; [|reflexivity]. neexists 4. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_noaccess_outcome : ltac2:(zQ "j83!h9!s1!hu9!s9!lq7!lgb!ls2!le!jc!mre!msd!ird!ms5!s6!imc!mqe!nl7!ntf!v8!hgf!mj5!ij8!nu5!li3!li9!ir5!isd!nua!nv3!lj3!mm2!ll3!ng7!ihd!nh6!nvf!mmd!ni2!nif!nja!nk9!nm5!ogd!ohb!oia!oo6!ol9!kr5!on0!noc!nsf!mr8!r7!rc!np5!lma&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$5~0&@4$a@1$1@1$0#k0@1$1@1$0#k0^1^2>4addr@1$1@1$0#k0>3len@1$1@1$0#k0>4prot@1$1@1$0#k0>5flags@1$1@1$0#k0>2fd@1$1@1$0#k0>3off@1$1@1$0#k0>1i$ha>1m$h9>1o@1$e$b>0@3$3$4@1$ie^4$6>0@3$3$4@1$ib^7$6>0@3$3$4@1$j1^a$c>0@3$3$4@3$ic^a^9^7$c>0@3$3$4@3$id^b^a^8$6=1h$hb@1$he^7=2nZ$d@1$i1@2$8@1$0#k0^e=1n@1$1@1$0#k0@2$j7@1$0#k0^1@2$h5@9$if^h1^h0^f^e^d^c^b^a^9@2$h6@2$j2^a^9@2$h4@1$1@1$0#k0\1a@1$1@1$0#k0@2$7@2$7@3$3$d@2$j6@2$8@1$0#k0^1$i2Z@2$7@2$j5Z@2$8@1$0#k0^1@2$7@2$j4@2$j3@2$8@1$0#k0^1^3@1$hc^4@3$3$4@3$i3@3$h1~0@1$h0^4@1$f^4^1^2$6@3$3@1$e$b^a@4$h7$b@6$hf^1@1$5@2$2@1$1@1$0#k0@1$h2@1$1@1$0#8~1@3$9~0~2~1@1$5$h8@1$5@2$2@1$1@1$0#k0$h3@4$j0^f^1^2@2$ia@8$i0@1$h0^4@3$9~0~2@1$f^4@3$9~0~2@1$i8^4@1$i9^4@1$i4^4@1$i6^4@1$i7^4@1$i5^4^b@1$5$hd").
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna. cbv zeta. unfold mmap_spec.
  rewrite Hoff, Hanon, Hlen, Hmod, Hna. cbn [negb]. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. eexists; split; [|reflexivity]. repeat split; assumption.
  - intros [(e & He & ->) | (a & Ha & ->)].
    + left. neexists 4. split; [exists e; split; [exact He|reflexivity]|].
      split; reflexivity.
    + right. neexists 4; (split; [reflexivity|]); (split; [|reflexivity]).
      neexists 4. split; [exists a; split; [exact Ha|reflexivity]|].
      split; [|reflexivity]. neexists 4. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_noaccess_outcome : ltac2:(zQ "jf5!h9!s1!lgb!hu9!s9!lq7!jc!ls2!s6!ird!mre!ms5!msd!imc!v8!hgf!nu5!li3!li9!lj3!ll3!mqe!nl7!mr8!le!mj5!ij8!ir5!isd!nua!nv3!se!mm2!op9!mv7!ng7!ihd!nh6!nvf!mmd!ni2!nif!nja!nk9!nm5!ogd!ohb!npe!oq8!os6!oia!oo6!ol9!kr5!nn4!ou0!noc!nsf!ns0!r7!rc!np5!lma&@2$3@1$1@1$0#k0@1$e@1$1@1$0#8&@1$2~0&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~2&@4$c@1$1@1$0#k0@1$1@1$0#k0^h7^6>4addr@1$1@1$0#k0>3len@1$1@1$0#k0>4prot@1$1@1$0#k0>5flags@1$1@1$0#k0>2fd@1$1@1$0#k0>3off@1$1@1$0#k0>1i$hc>1m$hb>1o@1$d$9>0@3$4$5@1$j4^4$7>0@3$4$5@1$ie^7$7>0@3$4$5@1$j8^a$b>0@3$4$5@3$j2^a^9^7$b>0@3$4$5@3$j3^b^a^8$b>0@3$4$5@3$j1^c^b^9$7=1h$hd@1$i0^8=2nZ$8@1$i4@2$6@1$0#k0^f=1n@1$1@1$0#k0@2$je@1$0#k0^1>0@2$jb@2$h7@2$6@1$0#k0^h2^2@1$he^3>0@3$4$8@2$jd@2$6@1$0#k0^h3$i5Z>0@2$jcZ@2$6@1$0#k0^h4>0@3$4$5@3$i6@1$h6^6^h5^4$7>0@3$4$5@3$i1@1$h5^7^h6^5$7@2$ha@9$j5^h7^h6^h5^h4^h3^h2^h1^h0^f@2$h0@2$j9^h0^f@2$h0@3$4@1$d$9^f@4$h1$9@6$h4^h7~1~3@3$a~2~4~3@1$2$h2@1$2@2$3@1$1@1$0#k0$f@4$j7^h4^h7^6@2$id@8$i3@1$h6^8@1$h5^8@3$a~2~4@3$i2@1$ib^8@2$6@1$0#k0^h7@2$h7@2$6@1$0#k0^h7@2$6@1$0#k0^6@1$ic^8@1$i7^8@1$i9^8@1$ia^8@1$i8^8^h0@1$2$h3@2$h9$8\1e$8@2$h8@3$ja$8^1$if@3$4@1$d$9^h0@4$h1$9@6$h4@1$hf^1~1~3@3$a~2@4$c@1$1@1$0#k0@1$1@1$0#k0^h8^7~3@1$2$h2@1$2@2$3@1$1@1$0#k0$f@4$j6^h8^7@3$j0^9^h8^7^h1@1$2$h3").
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfx. cbv zeta.
  intros Hce Hal Hpos Hrf Hmc.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfx. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrf, Hmc. cbn [andb]. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right; left. reflexivity.
    + right; right. eexists; split; [eassumption|reflexivity].
  - intros [(e & He & ->) | [-> | (e & He & ->)]].
    + left. neexists 4. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right; left. neexists 4. repeat split; reflexivity.
    + right; right. neexists 4. split; [exists e; split; [exact He|reflexivity]|].
      split; [|reflexivity]. neexists 4. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mprotect_err_out : ltac2:(zQ "30!imc!ir5!ird>1m$1>1o@1$0$2P") := ltac2:(zQ "h42!h9!s1!lgb!hu9!s6!ird!imc!v8!hgf!le!s9!mj5!li3!li9!ir5!se!lj3!ll3!ova!ns0&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0\1m$e\1o@1$6$5@2$b$4\1e$4@2$9@3$h3$4^1$h2@3$a@1$6$5^2@4$c$5@6$h1@1$f^1@1$2@2$3@1$1@1$0#k0@1$7@1$1@1$0#8~1~1@1$2$d@1$2@2$3@1$1@1$0#k0$8^3@1$2$h0").

Lemma mprotect_err_out_enomem : ltac2:(zQ "h22!h9!s1!lgb!hu9!ird!imc!v8!hgf!s9!ij8!li3!ns6!li9!ir5!se!lj3!ll3!pgd&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1m$d>1o@1$5$4@2$9@2$h1^2^1@3$8@1$5$4^1@4$a$4@6$h0@1$e$b@1$2@2$3@1$1@1$0#k0@1$6@1$1@1$0#8~1~1@1$2$c@1$2@2$3@1$1@1$0#k0$7^2@1$2$f").
Proof.
  intros m o. unfold mprotect_err_out, mprotect_errnos. split.
  - (intros nd_i4; ndestruct nd_i4 as (e & [<- | []] & ->)). reflexivity.
  - intros ->. exists ENOMEM. split; [left; reflexivity | reflexivity].
Qed.

Lemma mprotect_expose_outcome : ltac2:(zQ "ic2!h9!s1!s9!lq7!lgb!hu9!ls2!jc!ird!ms5!imc!op9!ihd!lma!mre!v8!hgf!msd!le!ij8!nu5!s6!li3!li9!ir5!isd!nua!lj3!mm2!ll3!nh6!p2!mqe!nk9!pi2!pj9!pl7!pmf!kva!noc!pgd!mr8!rc!np5&@2$5@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>4addr@1$1@1$0#k0>3len@1$1@1$0#k0>4prot@1$1@1$0#k0>1i$h9>1m$h8>1o@1$a$8>0@3$2$3@1$i3^4$9>0@3$2$h5@2$ib@2$7@1$0#k0^7$heZ>0@3$2$3@1$i7^7$9>0@2$ia@2$i9@2$7@1$0#k0^9@1$c@2$7@1$0#k0^8$hf>0@3$2$3@1$i5^8$6=1h$ha@1$hc^7=1n@1$1@1$0#k0@2$d@1$0#k0@1$c@2$7@1$0#k0^b>0@3$2$3@3$b@1$i1^2^d^1$6>0@3$2$3@3$b@1$i0^3^e^2$6@2$h3@6$i6^f^e^d^c^b^a@2$h4@2$i8^b^a@2$h2@3$2$3@3$i2^b^f^3$6@3$2@1$a$8^a@4$h6$8@6$hd@2$d@1$0#k0Z@1$4@2$5@1$1@1$0#k0@1$f@1$1@1$0#8@3$e~0@4$h1@1$1@1$0#k0@1$1@1$0#k0^f^3~1~1@1$4$h7@1$4@2$5@1$1@1$0#k0$h0@3$i4^b^f^3@1$4$hb").
Proof.
  intros addr len prot i m o Hgc Hal Hlen Hnw Hmod. cbv zeta. intros Hna Hma.
  unfold mprotect_spec.
  rewrite Hgc, (proj2 (Z.eqb_eq _ _) Hal), Hlen, (proj2 (Z.leb_gt _ _) Hnw), Hmod. cbn [negb].
  unfold mprotect_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hna, Hma in *; cbn [andb] in *; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. split; [assumption|reflexivity].
  - intros [(e & He & ->) | (Hb & ->)]; neexists 4; (split; [reflexivity|]);
      rewrite Hna, Hma; cbn [andb]; (split; [|reflexivity]).
    + left. neexists 4. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. neexists 4. split; [exists tt; split; [exact Hb|reflexivity]|].
      split; [|reflexivity]. neexists 4. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma read_dir_outcome : ltac2:(zQ "hd2!h9!s1!lgb!hu9!s9!ird!imc!lh1!hg8!lq7!v8!hgf!vf!ls2!ij8!li3!po6!lqe!li9!ir5!isd!pof!se!lj3!ljb!lhb!ll3!jv9!jc&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>2fd@1$1@1$0#k0>3buf@1$1@1$0#k0>5count@1$1@1$0#k0>1i$h4>1m$h3>1o@1$6$5>0@3$4@1$c$7@2$h8@1$h9^2^6@2$8$7$h1>0@3$4$9@2$h5^6@2$hc@1$0#k0^5$d@2$e@6$hb^8^7^6^5^4^3@3$4@1$6$5^3@4$f$5@6$ha@1$h6$h0@1$2@2$3@1$1@1$0#k0@1$a@1$1@1$0#8~1~1@1$2$h2@1$2@2$3@1$1@1$0#k0$b^4@1$2$h7").
Proof.
  intros fd buf count i m o Hlk Hacc. unfold read_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk, ?Hacc in *; cbn [negb] in *; inv_sys.
    reflexivity.
  - intros ->. neexists 4. split; [reflexivity|]. split; [|reflexivity].
    neexists 4. split; [reflexivity|]. rewrite Hlk, Hacc. cbn [negb]. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma read_file_outcome : ltac2:(zQ "i82!h9!s1!v8!lgb!s9!hg8!vf!hu9!ppc!ird!imc!lh1!pq8!lhb!lq7!hgf!ls2!ij8!pr1!pre!lpf!li3!li9!ir5!isd!pof!lj3!psb!ljb!pt7!pu1!ll3!hm1!pu8!llf!jv9!qid!lma!qk2!jc&@2$7@1$1@1$0#k0@1$1@1$0#k0&@1$3~0>2fd@1$1@1$0#k0>3buf@1$1@1$0#k0>5count@1$1@1$0#k0>1i$h8>1m$h7>1o@1$a$9>1p$h4>3off@1$1@1$0#k0>4data@1$2@1$1@1$0#8>1w@1$2@1$1@1$0#8>0@3$4@1$6$b@2$hc@1$d^6^a@2$5$b@2$c^4^3>0@3$4$e@2$h9^a@2$i7@1$0#k0^9$h0>0@3$4@1$6@1$2@1$1@1$0#8@2$h3@1$he^8^6@2$5@1$2@1$1@1$0#8^4=2bs@1$2@1$1@1$0#8@3$h2^5^6@2$i5@1$0#k0@1$i1^b>0@3$4@1$6@1$2@1$1@1$0#8@3$i0@1$hd^b^d@2$8@1$1@1$0#8^1@2$5@1$2@1$1@1$0#8^5@2$h1@6$i3^f^e^d^c^b^a@3$4@1$a$9^a@4$h5$9@6$hf@2$8@1$1@1$0#8^2@2$i4^e^2~1~1@1$3$h6@1$3@2$7@1$1@1$0#k0$f@2$i2@3$hb@1$d^b^f@2$c^9@3$i6@1$0#k0^8@2$8@1$1@1$0#8^2^b@1$3$ha").
Proof.
  intros fd buf count i m o p off data w Hlk Hacc Hfs. cbv zeta. intros Hw.
  unfold read_spec. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hlk, Hacc in *; cbn [negb] in *;
      rewrite Hfs in *; cbv zeta in *; rewrite Hw in *; inv_sys; reflexivity.
  - intros ->. neexists 4. split; [reflexivity|]. split; [|reflexivity].
    neexists 4. split; [reflexivity|]. rewrite Hlk, Hacc. cbn [negb].
    rewrite Hfs. cbv zeta. rewrite Hw.
    split; [|reflexivity]. neexists 4. repeat split; reflexivity.
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition open_reads : ltac2:(zQ "60!h9!s1!v8!hgf!hu9!isd>1i$5>5pathp@1$1@1$0#k0@1$2@2$4@1$1@1$0#k0$3") := ltac2:(zQ "b0!h9!s1!hgf!hu9!mre!lgb!msd!isd!qkb!qm2!qmb\1i$7\5pathp@1$1@1$0#k0@3$4@2$3@1$1@1$0#k0$2@4$6@1$1@1$0#k0$2^1@3$8@1$9^2^1$a@1$5@2$3@1$1@1$0#k0$2").

(* [comment removed for export] *)
Definition after_copyins : ltac2:(zQ "70!imc!ird!v8!hgf!hu9!h9!s1>1R@1$2@2$4@1$6@1$5#k0$3>4body>0@1$0$1P>1o@1$0$1P") := ltac2:(zQ "h10!ird!imc!v8!hgf!hu9!h9!s1!ntf!le!s9!mj5!li3!qn6!ir5!qo3!lj3!qp1\1R@1$2@2$4@1$6@1$5#k0$3\4body>0@1$1$0P\1o@1$1$0M1\1o@1$1$0P^1\3eff$0\2m'$d\3evs@1$2$f@2$a$0\4core$0@2$8@1^6@4$b$0^1^3^2@3$9$0^4@2$h0@3$7@2$4@1$6@1$5#k0$3^7@1$e^1^1@1^2@1$c$0").

Lemma record_copyins_iff : ltac2:(zQ "d0!ird!v8!hgf!hu9!ij8!h9!qq0!imc!ir5!isd!qq7!qr9!s1>1R@1$1@2$3@1$c@1$5#k0$2>4spec@1$6$0>1i$9>1m$8>1o@1$7$0@2$4@5$a^5^4^3^2^1@3$b^5@2^4^3^2^1").
Proof.
  intros R spec i m o. unfold record_copyins, after_copyins, bind, pure.
  destruct o as [eff m' evs|]; split.
  - (intros nd_i5; ndestruct nd_i5 as (core & m1 & evs1 & evs2 & Hc & Hp & ->)). apply Ok_inj in Hp as (-> & -> & ->).
    exists core. rewrite app_nil_r. auto.
  - (intros nd_i6; ndestruct nd_i6 as (core & Hc & ->)). nexists core, m', evs, []. rewrite app_nil_r. auto.
  - intros [H | (core & m1 & evs1 & _ & Hp)]; [exact H|]. exfalso. exact (Unmodeled_Ok _ _ _ Hp).
  - intros H. left. exact H.
Qed.

(* [comment removed for export] *)
Lemma after_copyins_det : ltac2:(zQ "h14!h9!s1!lgb!hu9!ird!imc!v8!hgf!s9!ij8!li3!li9!ll3!ir5!lj3!qp1!qr9&@2$3@1$1@1$0#k0@1$6@1$1@1$0#8&@1$2~0&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~2>1R@1$6@2$3@1$1@1$0#k0$7>4body>1x@1$5$4P>1r@1$1@1$0#k0>2m0$d>4evs0@1$6$e>0>1o@1$5$4@2$9@1^5^1@3$8@1$5$4^1@4$a$4@6$c^4~1~3~3@1$2$b@1$2@2$3@1$1@1$0#k0$7^3^2>1o@1$5$4@2$9@3$h0^7^6^1@3$8@1$5$4^1@4$a$4@2$f^7@6$c^5~1~3~3@1$2$b@1$2@2$3@1$1@1$0#k0$7^4^3").
Proof.
  intros R body r m0 evs0 Hb o. unfold after_copyins. destruct o as [eff m' evs|]; split.
  - (intros nd_i7; ndestruct nd_i7 as (core & Hc & ->)). apply Hb in Hc. apply Ok_inj in Hc as (-> & -> & ->).
    cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
  - intros H. apply Ok_inj in H as (-> & -> & ->). exists (mkEffect r [] []).
    split; [apply Hb; reflexivity|]. cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
  - intros H. apply Hb in H. exfalso. exact (Unmodeled_Ok _ _ _ H).
  - intros H. exfalso. exact (Unmodeled_Ok _ _ _ H).
Qed.

(* [comment removed for export] *)
Definition open_res : ltac2:(zQ "50!ir5!h9!imc!ird!s1>1m$0>2mk>0@1$4@1$1#k0$0>1o@1$2$3P") := ltac2:(zQ "hb4!h9!s1!lgb!hu9!ird!lhb!s9!s6!imc!qsa!v8!hgf!le!li3!lh1!li9!ir5!lj3!ll3!mie!vf!mj5!nu5!se!ljb!qt5!ns0&@2$3@1$1@1$0#k0@1$a@1$1@1$0#8&@1$2~0&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~2\1m$h0\2mk>0@1$1@1$0#k0$h0\1o@1$8$4@2$h6@2$h5$7\1e$7@2$c@3$ha$7^1$h9@3$6@1$8$4^2@4$d$4@6$h2@1$h7^1~1~3~3@1$2$f@1$2@2$3@1$1@1$0#k0$b^4@1$2$h1@2$c@3$6@1$h4$e@2$h8@1$5^3@1$9@1$5^3@1$h3$e@3$6@1$8$4^1@4$d$4@6$h2@1$9@1$5^3~1~3~3@1$2$f@1$2@2$3@1$1@1$0#k0$b@1^2@1$9@1$5^3@1$2$h1").

(* [comment removed for export] *)
Definition open_out : ltac2:(zQ "80!h9!ir5!s1!v8!hgf!hu9!imc!ird>1R@1$3@2$5@1$2@1$0#k0$4>1m$1>2mk>0@1$2@1$0#k0$1>1o@1$6$7P") := ltac2:(zQ "hc4!h9!s1!lgb!hu9!ird!lhb!v8!hgf!s9!s6!imc!qsa!le!li3!lh1!li9!ir5!lj3!ll3!qp1!mie!vf!mj5!nu5!se!ljb!qt5!ns0&@2$3@1$1@1$0#k0@1$6@1$1@1$0#8&@1$2~0&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~2\1R@1$6@2$3@1$1@1$0#k0$7\1m$h0\2mk>0@1$1@1$0#k0$h0\1o@1$a$4@2$h7@2$h6$9\1e$9@2$c@3$hb$9^1$ha@3$8@1$a$4^2@4$d$4@2$h3^5@6$h2@1$h8^1~1~3~3@1$2$f@1$2@2$3@1$1@1$0#k0$7^4@1$2$h1@2$c@3$8@1$h5$e@2$h9@1$5^3@1$b@1$5^3@1$h4$e@3$8@1$a$4^1@4$d$4@2$h3^4@6$h2@1$b@1$5^3~1~3~3@1$2$f@1$2@2$3@1$1@1$0#k0$7@1^2@1$b@1$5^3@1$2$h1").

Lemma open_result_outcome : ltac2:(zQ "90!ir5!h9!s1!ij8!imc!ird!isd!qu6!qvb>1m$0>2mk>0@1$2@1$1#k0>0$0$0>1i$6>1o@1$4$5@2$3@5$7^4^3^2^4^1@3$8^4\2fd@1$2@1$1#k0@2^4^1^5^1").
Proof.
  intros m mk i o. unfold open_result_spec, open_res. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. split; [assumption|reflexivity].
  - intros [(e & He & ->) | (Hfree & ->)].
    + left. neexists 4. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. neexists 4. split; [eexists; split; [split; [exact Hfree|reflexivity]|reflexivity]|].
      split; [|reflexivity]. neexists 4. repeat split; reflexivity.
Qed.

Lemma after_copyins_open : ltac2:(zQ "c0!imc!ird!ij8!h9!ir5!s1!v8!hgf!hu9!qr9!rg7!qvb>1R@1$6@2$8@1$5@1$3#k0$7>4body>1x@1$0$1P>1m$4>2mk>0@1$5@1$3#k0$4>0>1o@1$0$1@2$2@1^4^1@3$b^3^2^1>1o@1$0$1@2$2@3$9^6^5^1@4$a^6^4^3^1").
Proof.
  intros R body m mk Hb o. unfold after_copyins, open_out. destruct o as [eff m' evs|]; split.
  - (intros nd_i8; ndestruct nd_i8 as (core & Hc & ->)). apply Hb in Hc.
    destruct Hc as [(e & He & Hc) | (Hfree & Hc)]; apply Ok_inj in Hc as (-> & -> & ->);
      cbn [eff_copyins]; rewrite app_nil_r.
    + left. exists e. auto.
    + right. auto.
  - intros [(e & He & H) | (Hfree & H)]; apply Ok_inj in H as (-> & -> & ->).
    + exists (mkEffect (errno_ret e) [] []). split; [apply Hb; left; exists e; auto|].
      cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
    + exists (mkEffect (alloc_fd (m_fds m)) [] []). split; [apply Hb; right; auto|].
      cbn [eff_copyins]. rewrite app_nil_r. reflexivity.
  - intros H. apply Hb in H. destruct H as [(e & _ & H) | (_ & H)]; exfalso; exact (Unmodeled_Ok _ _ _ H).
  - intros [(e & _ & H) | (_ & H)]; exfalso; exact (Unmodeled_Ok _ _ _ H).
Qed.

(* [comment removed for export] *)
Lemma openat_spec_body : ltac2:(zQ "f0!h9!s1!lq7!ls2!s9!ij8!imc!ir5!ird!isd!rh3!ria!jq3!qr9!rjf>5dirfd@1$1@1$0#k0>5pathp@1$1@1$0#k0>5flags@1$1@1$0#k0>1i$9>1m$7>1o@1$6$8>0@3$4$2@1$a^4$3@2$5@6$c^7^6^5^4^3^2@3$d@2$e^4^6@7$b^4^3^7^6^5^4^3^2").
Proof.
  intros dirfd pathp flags i m o Hfl. unfold openat_spec.
  transitivity (record_copyins (open_reads i pathp) (openat_core_spec dirfd pathp flags) i m o).
  { unfold bind, input, open_reads. destruct o as [eff m' evs|]; split.
    - (intros nd_i9; ndestruct nd_i9 as (i0 & m1 & evs1 & evs2 & Hi & Hk & ->)). apply Ok_inj in Hi as (-> & -> & ->). exact Hk.
    - intros Hk. nexists i, m, [], evs. split; [reflexivity|]. split; [exact Hk|reflexivity].
    - intros [H | (i0 & m1 & evs1 & Hi & Hk)]; [exfalso; exact (Unmodeled_Ok _ _ _ H)|].
      apply Ok_inj in Hi as (-> & -> & ->). exact Hk.
    - intros Hk. right. nexists i, m, []. split; [reflexivity|exact Hk]. }
  rewrite record_copyins_iff.
  assert (Hcore : forall o', openat_core_spec dirfd pathp flags i m o' <->
                            openat_body_spec i m dirfd pathp flags i m o').
  { intros o'. unfold openat_core_spec. rewrite Hfl. cbn [negb].
    unfold bind, input, get_model. destruct o' as [eff m' evs|]; split.
    - (intros nd_i10; ndestruct nd_i10 as (i0 & m1 & evs1 & evs2 & Hi & (m0 & m2 & evs3 & evs4 & Hm & Hb & ->) & ->)).
      apply Ok_inj in Hi as (-> & -> & ->). apply Ok_inj in Hm as (-> & -> & ->). exact Hb.
    - intros Hb. nexists i, m, [], evs. split; [reflexivity|]. split; [|reflexivity].
      nexists m, m, [], evs. split; [reflexivity|]. split; [exact Hb|reflexivity].
    - intros [H | (i0 & m1 & evs1 & Hi & [H | (m0 & m2 & evs2 & Hm & Hb)])];
        [exfalso; exact (Unmodeled_Ok _ _ _ H)| exfalso; exact (Unmodeled_Ok _ _ _ H)|].
      apply Ok_inj in Hi as (-> & -> & ->). apply Ok_inj in Hm as (-> & -> & ->). exact Hb.
    - intros Hb. right. nexists i, m, []. split; [reflexivity|]. right.
      nexists m, m, []. split; [reflexivity|exact Hb]. }
  unfold after_copyins. destruct o as [eff m' evs|]; [|apply Hcore].
  split; (intros nd_i11; ndestruct nd_i11 as (core & Hc & ->)); exists core; (split; [apply Hcore; exact Hc|reflexivity]).
Qed.

(* [comment removed for export] *)
Lemma err_ret_outcome : ltac2:(zQ "h32!h9!s1!lgb!hu9!ird!imc!v8!hgf!s9!ij8!s6!li3!li9!ir5!isd!se!lj3!ll3!rkd&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1e$a>1i$e>1m$d>1o@1$5$4@2$9@4$h2^4^3^2^1@3$8@1$5$4^1@4$b$4@6$h1@1$f^4@1$2@2$3@1$1@1$0#k0@1$6@1$1@1$0#8~1~1@1$2$c@1$2@2$3@1$1@1$0#k0$7^2@1$2$h0").
Proof. intros. unfold err_ret, ret_only, pure. reflexivity. Qed.

Section Openat.
  Variables (dirfd pathp flags : word) (i : SyscallInput) (m : Model).
  Hypothesis Hfl : ltac2:(zQ "40!lq7!ls2!s9!rh3@3$2$0@1$3?5flags$1").

  (* [comment removed for export] *)
  Lemma openat_toolong_outcome : ltac2:(zQ "h72!h9!s1!lgb!hu9!ird!s9!imc!v8!hgf!ij8!li3!rl8!rm6!li9!rn5!se!lj3!qm2!ll3!ro3!qp1!jq3!rjf&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1o@1$6$4>0@3$5$e@2$h3@1$h1?1i?5pathp$b@2$9@6$h5?5dirfd?5pathp?5flags?1i?1m^2@3$5@1$6$4^2@4$a$4@2$h4@2$h6?1i?5pathp@6$h2@1$f$c@1$2@2$3@1$1@1$0#k0@1$7@1$1@1$0#8~1~1@1$2$d@1$2@2$3@1$1@1$0#k0$8?1m@1$2$h0").
  Proof.
    intros o Hp. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_det.
    intros o'. unfold openat_body_spec. rewrite Hp. apply err_ret_outcome.
  Qed.

  (* [comment removed for export] *)
  Lemma openat_empty_outcome : ltac2:(zQ "h72!h9!s1!lgb!hu9!ird!s9!imc!v8!hgf!ij8!li3!rof!rp8!li9!rn5!se!lj3!qm2!ll3!ro3!qp1!jq3!rjf&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1o@1$6$4>0@3$5$e@2$h3@1$h1?1i?5pathp@1$b@1$2@1$1@1$0#8@2$9@6$h5?5dirfd?5pathp?5flags?1i?1m^2@3$5@1$6$4^2@4$a$4@2$h4@2$h6?1i?5pathp@6$h2@1$f$c@1$2@2$3@1$1@1$0#k0@1$7@1$1@1$0#8~1~1@1$2$d@1$2@2$3@1$1@1$0#k0$8?1m@1$2$h0").
  Proof.
    intros o Hp. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_det.
    intros o'. unfold openat_body_spec. rewrite Hp. cbn [path_eqb]. apply err_ret_outcome.
  Qed.

  Hypothesis Hdir : ltac2:(zQ "40!s9!h9!su9!s1@3$0@1$3@1$1#k0?5dirfd$2").
  Hypothesis Hrd : ltac2:(zQ "60!s9!h9!s6!sv7!tge!jc@3$0$2@2$4@2$5@1$1#k0?5flags$3Z").

  Lemma openat_body_resolved : ltac2:(zQ "h20!s9!h9!s1!v8!lq7!ms5!lgb!ij8!rq1!imc!rof!ird!rn5!qm2!ro3!rtc!ria!rue>1p@1$3@1$2@1$1#8>1o@1$9$b>0@3$0$c@2$e@1$d?1i?5pathp@1$a^2>0@1$8@3$0@1$3@1$2@1$1#8^3@1$6@1$2@1$1#8>0@3$0$4@1$f^4$5@2$7@8$h0?1i?1m?5dirfd?5pathp?5flags?1i?1m^4@5$h1^5?1m?1i?1m^4").
  Proof.
    intros p o Hp Hne Hsl. unfold openat_body_spec. rewrite Hp.
    replace (path_eqb p []) with false by (destruct p; [congruence|reflexivity]).
    rewrite Hdir, bv_eqb_refl. cbn [negb]. unfold openat_resolved_spec. rewrite Hsl, Hrd.
    reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma openat_absent_outcome : ltac2:(zQ "i02!h9!s1!lgb!s9!v8!hu9!ird!lq7!ms5!imc!mie!hgf!vf!ij8!rq1!pre!li3!rof!rp8!li9!rn5!se!lj3!qm2!pu1!ll3!ro3!qp1!rtc!jq3!sg3!rjf&@2$5@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1p@1$4@1$1@1$0#8>1o@1$9$6>0@3$3$h4@2$ha@1$h7?1i?5pathp@1$h1^2>0@1$e@3$3@1$4@1$1@1$0#8^3@1$2@1$1@1$0#8>0@3$3$7@1$hc^4$8>0@3$3$7@1$he^5$8>0@3$3@1$c@1$4@1$1@1$0#8@2$f@1$h8?1m^6@1$a@1$4@1$1@1$0#8@2$d@6$hd?5dirfd?5pathp?5flags?1i?1m^6@3$3@1$9$6^6@4$h0$6@2$hb@2$hf?1i?5pathp@6$h9@1$h5$h2@1$2@2$5@1$1@1$0#k0@1$4@1$1@1$0#8~1~1@1$2$h3@1$2@2$5@1$1@1$0#k0$b?1m@1$2$h6").
  Proof.
    intros p o Hp Hne Hsl Hnd Hfs. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_det.
    intros o'. rewrite (openat_body_resolved p o' Hp Hne Hsl). unfold openat_read_spec.
    rewrite Hnd, Hfs. apply err_ret_outcome.
  Qed.

  (* [comment removed for export] *)
  Lemma openat_dot_outcome : ltac2:(zQ "h50!s9!h9!s1!lq7!v8!ls2!ij8!imc!rof!lqe!ird!rn5!psb!qm2!lhb!ro3!llf!jq3!sg3!rg7!rjf>1p@1$4@1$2@1$1#8>1o@1$7$a>0@3$0$b@2$f@1$d?1i?5pathp@1$8^2>0@3$0$3@1$h2^3$5@2$6@6$h1?5dirfd?5pathp?5flags?1i?1m^3@4$h3@2$h4?1i?5pathp?1m\2fd@1$2@1$1#k0@2$h0@3$c@1$e?1m^1$9?1m^3").
  Proof.
    intros p o Hp Hdr. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_open.
    assert (Hne : p <> []).
    { intros ->. discriminate Hdr. }
    intros o'. rewrite (openat_body_resolved p o' Hp Hne (path_is_dirref_no_slash p Hdr)).
    unfold openat_read_spec. rewrite Hdr. apply open_result_outcome.
  Qed.

  (* [comment removed for export] *)
  Lemma openat_file_outcome : ltac2:(zQ "hd0!h9!s1!v8!s9!lq7!ms5!hg8!lgb!vf!ij8!rq1!pre!imc!rof!pq8!ird!rn5!psb!qm2!lhb!pu1!ro3!llf!rtc!jq3!sg3!rg7!rjf!lma>1p@1$2@1$1@1$0#8>1d@1$2@1$1@1$0#8>1o@1$c$f>0@3$3$h0@2$h5@1$h2?1i?5pathp@1$d^3>0@1$a@3$3@1$2@1$1@1$0#8^4@1$7@1$1@1$0#8>0@3$3$4@1$h7^5$5>0@3$3$4@1$h9^6$5>0@3$3@1$8@1$2@1$1@1$0#8@2$b@1$h4?1m^7@2$6@1$2@1$1@1$0#8^6@2$9@6$h8?5dirfd?5pathp?5flags?1i?1m^6@4$ha@2$hb?1i?5pathp?1m\2fd@1$1@1$0#k0@2$h6@3$h1@1$h3?1m^1@2$e^9@2$hc@1$0#k0Z?1m^6").
  Proof.
    intros p d o Hp Hne Hsl Hnd Hfs. rewrite (openat_spec_body _ _ _ _ _ _ Hfl). apply after_copyins_open.
    intros o'. rewrite (openat_body_resolved p o' Hp Hne Hsl). unfold openat_read_spec.
    rewrite Hnd, Hfs. apply open_result_outcome.
  Qed.
End Openat.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma cap_iovecs_aux_id : ltac2:(zQ "92!h9!s1!v8!hu9!s9!s6!sh5!ih0!r7&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>4iovs~1>4left$5>0@2$8@1$7^2^1@3$4~1@2$6^3^2^3").
Proof.
  induction iovs as [|[b n] r IH]; intros left H; [reflexivity|].
  cbn [cap_iovecs_aux]. cbn [iovs_total] in H. pose proof (iovs_total_nonneg r).
  rewrite Z.min_r by lia. rewrite Z_to_bv_bv_unsigned, IH by lia. reflexivity.
Qed.

Lemma cap_iovecs_id_rw : ltac2:(zQ "92!h9!s1!v8!hu9!s9!si6!ih0!sj3!r7&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>4iovs~1>0@2$8@1$6^1$7@3$4~1@1$5^2^2").
Proof.
  intros iovs H. unfold cap_iovecs. apply cap_iovecs_aux_id.
  unfold MAX_RW_COUNT. unfold rw_bytes_max in H. lia.
Qed.

(* [comment removed for export] *)
Lemma bind_input_get_model : ltac2:(zQ "90!ir5!ird!isd!sk3!ij8!qq0!skb!sl8!imc>1k>0$2>0$0@1$5$1>1i$2>1m$0>1o@1$8$1@2$4@7$3$2$1$7\2i0$2@4$3$0$1$6\2m0$0@2^6^2^1^3^2^1@5^4^3^2^3^2^1").
Proof.
  intros k i m o. unfold bind, input, get_model. destruct o as [eff m' evs|]; split.
  - (intros nd_i12; ndestruct nd_i12 as (i0 & m1 & e1 & e2 & Hi & (m0 & m2 & e3 & e4 & Hm & Hk & ->) & ->)).
    apply Ok_inj in Hi as (-> & -> & ->). apply Ok_inj in Hm as (-> & -> & ->). exact Hk.
  - intros Hk. nexists i, m, [], evs. split; [reflexivity|]. split; [|reflexivity].
    nexists m, m, [], evs. split; [reflexivity|]. split; [exact Hk|reflexivity].
  - intros [H | (i0 & m1 & e1 & Hi & [H | (m0 & m2 & e2 & Hm & Hk)])];
      [exfalso; exact (Unmodeled_Ok _ _ _ H) | exfalso; exact (Unmodeled_Ok _ _ _ H) |].
    apply Ok_inj in Hi as (-> & -> & ->). apply Ok_inj in Hm as (-> & -> & ->). exact Hk.
  - intros Hk. right. nexists i, m, []. split; [reflexivity|]. right.
    nexists m, m, []. split; [reflexivity| exact Hk].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma writev_chan_zero_outcome : ltac2:(zQ "i42!h9!s1!lgb!hu9!s9!ird!v8!imc!lh1!qm2!sm1!hg8!lq7!ms5!hgf!vf!ij8!s6!li3!smd!sn9!li9!ir5!isd!lj3!ljb!so1!sp1!sqb!ih0!lhb!ll3!qp1!kg6!noc!lma&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>2fd@1$1@1$0#k0>3iov@1$1@1$0#k0>6iovcnt@1$1@1$0#k0>1i$h7>1m$h6>1o@1$7$5>2ch@1$1@1$0#k0>4iovs@1$6~0>0@3$4@1$f$8@2$h9@1$he^4^8@2$b$8@1$h3^2>0@3$4$c@1$i2^3$d>0@3$4$hc@3$ha@1$9^7^9@1$a^8@1$h4^3>0@3$4$h1@1$hd^4Z@2$h0@6$i1^c^b^a^9^8^7@3$4@1$7$5^7@4$h2$5@2$i0@3$hb@1$9^9^b@1$a^a@6$hf@2$i3@1$0#k0Z@1$2@2$3@1$1@1$0#k0@1$6@1$1@1$0#8~1~1@1$2$h5@1$2@2$3@1$1@1$0#k0$e^8@1$2$h8").
Proof.
  intros fd iov iovcnt i m o ch iovs Hfd Hch Himp Htot.
  assert (Hcap : cap_iovecs iovs = iovs) by (apply cap_iovecs_id_rw; unfold rw_bytes_max; lia).
  unfold writev_spec. rewrite bind_input_get_model. rewrite Hfd, Hch. cbv iota.
  transitivity
    (record_copyins (import_iovecs_accesses (in_mem i) iov (iovcnt32 iovcnt))
       (ret_only (Z_to_bv 64 0)) i m o).
  { rewrite Himp. cbv zeta. rewrite Hcap, Htot. cbn [Z.eqb]. reflexivity. }
  rewrite record_copyins_iff. apply after_copyins_det. intros o'. unfold ret_only, pure. reflexivity.
Qed.
(* [comment removed for export] *)
