(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec CatExec SeqExec StepTac ArgvEnv.

Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_RefLayout () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.ABoot.PropExec.rdn"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Peano.le"; "Corelib.Init.Nat.add"; "stdpp.bitvector.definitions.bv_add"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.nat_to_word"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.skipn"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.build_auxv"; "Stdlib.Lists.List.flat_map"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.word_le8"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.app"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.len_word"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.string_addrs"; "OSSVerify.KrLib.ABoot.CatExec.cat_string_base"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.ABoot.CatExec.cat_env_base"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.auxv_bytes"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.at_random_ptr"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Nat.mul"; "Corelib.Init.Peano.lt"; "envp_off"; "cat_envp_ptr"; "auxv_off"; "Corelib.Lists.ListDef.nth"; "auxv_words"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.at_random_bytes"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.ed_random"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.of_nat"; "OSSVerify.KrLib.ABoot.CatExec.cat_struct_size"; "OSSVerify.KrLib.ABoot.PropExec.total_arg_bytes_nat"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.ABoot.CatExec.cat_argv_ptr"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.AT_PHDR"; "Stdlib.ZArith.BinInt.Z.of_N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.ph_addr"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.AT_PHENT"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.ph_ent"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.AT_PHNUM"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.ph_num"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.AT_HWCAP"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.AT_PAGESZ"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.AT_UID"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.AT_EUID"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.AT_SECURE"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.AT_RANDOM"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.AT_NULL"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_skipn : ltac2:(CDefT.buildp (gd_tbl_RefLayout ()) "Psegs,(0.$1.)Pmem,P,(2.&40.)(3.(2.&8.))Pn,$4.Pa,(2.&40.)Pbs,(0.(2.&8.))Poff,$4.Pk,$4.P,(5.(3.(0.(2.&8.)))(6.R7.R6.R4.R5.)(7.(0.(2.&8.))R3.))P,(8.(9.R3.R2.)R6.)(5.(3.(0.(2.&8.)))(6.R9.R8.(:.&40.R6.(;.R4.))R3.)(7.(0.(2.&8.))(<.(2.&8.)R3.(=.(2.&8.)R4.R5.))))")
(* [comment removed for export] *).
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs off k H Hk.
  - assert (off = 0%nat) by lia. assert (k = 0%nat) by lia. subst.
    rewrite word_add_0. cbn in H |- *. injection H as <-. reflexivity.
  - cbn [rdn] in H.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
      as [b|] eqn:Eb; [|discriminate].
    destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
    injection H as <-.
    destruct off as [|off].
    + rewrite word_add_0. cbn [skipn].
      eapply rdn_firstn; [|exact Hk].
      cbn [rdn]. rewrite Eb, Er. reflexivity.
    + cbn [skipn].
      replace (a + nat_to_word (S off)) with (a + 1 + nat_to_word off)
        by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
      apply (IH (a+1) rest off k Er). lia.
Qed.

Lemma firstn_app_exact : forall {A} (l1 l2 : list A) n,
  length l1 = n -> firstn n (l1 ++ l2) = l1.
Proof.
  intros A l1 l2 n H. subst n. rewrite firstn_app, firstn_all, Nat.sub_diag.
  cbn. apply app_nil_r.
Qed.

Lemma skipn_app_exact : forall {A} (l1 l2 : list A) n,
  length l1 = n -> skipn n (l1 ++ l2) = l2.
Proof.
  intros A l1 l2 n H. subst n. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma skipn_repeat' : forall {A} (x : A) off n,
  skipn off (repeat x n) = repeat x (n - off).
Proof.
  intros A x off. induction off as [|off IH]; intros n.
  - cbn. rewrite Nat.sub_0_r. reflexivity.
  - destruct n as [|n]; [reflexivity|]. cbn [repeat skipn]. rewrite IH. f_equal.
Qed.

Lemma firstn_repeat' : forall {A} (x : A) k n, (k <= n)%nat ->
  firstn k (repeat x n) = repeat x k.
Proof.
  intros A x k. induction k as [|k IH]; intros n H; [reflexivity|].
  destruct n as [|n]; [lia|]. cbn [repeat firstn]. rewrite IH by lia. reflexivity.
Qed.

Lemma repeat_firstn_skipn : forall {A} (x : A) n off k,
  (off + k <= n)%nat -> firstn k (skipn off (repeat x n)) = repeat x k.
Proof.
  intros A x n off k H.
  rewrite skipn_repeat', firstn_repeat' by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cat_envp_ptr (sp : word) (av ev : list (list byte)) (k : nat) : word :=
  nth k (fst (string_addrs (cat_env_base sp av ev) ev)) (Z_to_bv 64 0).

(* [comment removed for export] *)
Definition envp_off (av : list (list byte)) : nat := (8 + 8 * (length av + 1))%nat.
Definition auxv_off (av ev : list (list byte)) : nat :=
  (8 + 8 * (length av + 1) + 8 * (length ev + 1))%nat.

(* [comment removed for export] *)
Definition auxv_words (ph : PhdrInfo) (rnd uid hw : word) : list word :=
  flat_map (fun e => [fst e; snd e]) (auxv_entries ph rnd uid hw).

Lemma build_auxv_words : ltac2:(CDefT.buildp (gd_tbl_RefLayout ()) "Pentries,(0.(>.(2.&40.)(2.&40.)))(5.(0.(2.&8.))(?.R1.)(10.(2.&40.)(2.&8.)$11.(10.(>.(2.&40.)(2.&40.))(2.&40.)Le,(>.(2.&40.)(2.&40.))(12.(2.&40.)(13.(2.&40.)(2.&40.)R1.)(12.(2.&40.)(14.(2.&40.)(2.&40.)R1.)(15.(2.&40.))))R1.)))")
(* [comment removed for export] *).
Proof.
  induction entries as [|[t v] es IH]; [reflexivity|].
  cbn [build_auxv flat_map fst snd app].
  change (build_auxv es) with
    (flat_map (fun e : bv 64 * bv 64 => word_le8 (fst e) ++ word_le8 (snd e)) es) in IH.
  rewrite IH, <- app_assoc. reflexivity.
Qed.

Lemma auxv_bytes_words : forall ph rnd uid hw,
  auxv_bytes ph rnd uid hw = flat_map word_le8 (auxv_words ph rnd uid hw).
Proof. intros. unfold auxv_bytes, auxv_words. apply build_auxv_words. Qed.

Lemma length_auxv_words : forall ph rnd uid hw, length (auxv_words ph rnd uid hw) = 20%nat.
Proof. reflexivity. Qed.

Section Layout.

  Variable segs : list Segment.
  Variable ph : PhdrInfo.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.       (* [comment removed for export] *)

  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
  Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.

  Let bsb := build_stack_bytes ph sp av ev uid hw rdraw.
  (* [comment removed for export] *)
  Let stk := stack_to_mem sp (entry_stack_image ph sp av ev uid hw rdraw).

  #[using="Hva Hve Hsp_hi"] Lemma lay_bsb_nw : (bv_unsigned sp + Z.of_nat (length bsb) < 2^64)%Z.
  Proof. exact (bsb_nw ph sp av ev uid hw rdraw Hva Hve Hsp_hi). Qed.

  #[using="ph sp rdraw ev uid hw Hva stk"] Lemma lay_len_av : (1 <= length av <= 1024)%nat.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  #[using="ph sp rdraw av uid hw Hve stk"] Lemma lay_len_ev : (length ev <= 256)%nat.
  Proof. destruct Hve as [H1 _]. lia. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma bsb_decomp : ltac2:(CDefT.buildp (gd_tbl_RefLayout ()) "(16.(0.(2.&8.))Lstrs_tail,(0.(2.&8.))(5.(0.(2.&8.))Vbsb,(17.(2.&8.)(17.(2.&8.)(11.(18.(0.(2.&8.))Vav,))(10.(2.&40.)(2.&8.)$11.(13.(0.(2.&40.))(2.&40.)(19.(1:.Vsp,Vav,Vev,)Vav,))))(17.(2.&8.)(11.(1;.&40.=))(17.(2.&8.)(10.(2.&40.)(2.&8.)$11.(13.(0.(2.&40.))(2.&40.)(19.(1<.Vsp,Vav,Vev,)Vev,)))(17.(2.&8.)(11.(1;.&40.=))(17.(2.&8.)(1=.Vph,(1>.Vsp,Vav,Vev,)Vuid,Vhw,)R1.)))))))")
(* [comment removed for export] *).
  Proof.
    unfold bsb, build_stack_bytes, cat_env_base, cat_string_base, cat_struct_size.
    rewrite (string_addrs_pair av). cbv beta iota.
    rewrite (string_addrs_pair ev). cbv beta iota.
    eexists. rewrite <- !app_assoc. reflexivity.
  Qed.

  #[using="ph rdraw uid hw stk"] Lemma len_argc_argv : ltac2:(CDefT.buildp (gd_tbl_RefLayout ()) "(5.$4.(1?.(2.&8.)(17.(2.&8.)(11.(18.(0.(2.&8.))Vav,))(10.(2.&40.)(2.&8.)$11.(13.(0.(2.&40.))(2.&40.)(19.(1:.Vsp,Vav,Vev,)Vav,)))))(9.#8.(20.#8.(1?.(0.(2.&8.))Vav,))))")
(* [comment removed for export] *).
  Proof.
    rewrite length_app, length_n_to_le_8, length_flat_map_le8, length_string_addrs_fst. lia.
  Qed.

  #[using="ph rdraw uid hw stk"] Lemma len_envp_ptrs : ltac2:(CDefT.buildp (gd_tbl_RefLayout ()) "(5.$4.(1?.(2.&8.)(10.(2.&40.)(2.&8.)$11.(13.(0.(2.&40.))(2.&40.)(19.(1<.Vsp,Vav,Vev,)Vev,))))(20.#8.(1?.(0.(2.&8.))Vev,)))")
(* [comment removed for export] *).
  Proof. rewrite length_flat_map_le8, length_string_addrs_fst. lia. Qed.

  (* [comment removed for export] *)
  #[using="Hva Hve Hsp_hi bsb"] Lemma read_argv_null :
    rdn segs stk (sp + nat_to_word (8 + 8 * length av)) 8%nat = Some (word_le8 (Z_to_bv 64 0)).
  Proof.
    destruct bsb_decomp as [tl E].
    pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw _ (word_le8 (Z_to_bv 64 0)) _ 8%nat E
                  (length_n_to_le_8 _) lay_bsb_nw) as H.
    rewrite len_argc_argv in H. exact H.
  Qed.

  (* [comment removed for export] *)
  #[using="Hva Hve Hsp_hi bsb"] Lemma read_envp_ptr_k : ltac2:(CDefT.buildp (gd_tbl_RefLayout ()) "Pk,$4.P,(21.R1.(1?.(0.(2.&8.))Vev,))(5.(3.(0.(2.&8.)))(6.Vsegs,Vstk,(:.&40.Vsp,(;.(9.(22.Vav,)(20.#8.R2.))))#8.)(7.(0.(2.&8.))(11.(23.Vsp,Vav,Vev,R2.))))")
(* [comment removed for export] *).
  Proof.
    intros k Hk.
    destruct bsb_decomp as [tl E].
    assert (Hk' : (k < length (fst (string_addrs (cat_env_base sp av ev) ev)))%nat)
      by (rewrite length_string_addrs_fst; exact Hk).
    rewrite (flat_map_le8_decomp _ k Hk') in E.
    rewrite <- !app_assoc in E.
    match type of E with
    | bsb = ?p1 ++ ?p2 ++ ?p3 ++ ?p4 ++ ?mid ++ ?rest =>
        pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw (p1 ++ p2 ++ p3 ++ p4) mid rest 8%nat) as H
    end.
    rewrite <- !app_assoc in H.
    specialize (H E (length_n_to_le_8 _) lay_bsb_nw).
    rewrite !length_app in H.
    rewrite !length_flat_map_le8 in H.
    rewrite length_string_addrs_fst in H.
    rewrite firstn_length_le in H by (rewrite length_string_addrs_fst; lia).
    rewrite !length_n_to_le_8 in H.
    unfold envp_off, cat_envp_ptr.
    replace (8 + 8 * (length av + 1) + 8 * k)%nat with (8 + (8 * length av + (8 + 8 * k)))%nat by lia.
    exact H.
  Qed.

  (* [comment removed for export] *)
  #[using="Hva Hve Hsp_hi bsb"] Lemma read_envp_null : ltac2:(CDefT.buildp (gd_tbl_RefLayout ()) "(5.(3.(0.(2.&8.)))(6.Vsegs,Vstk,(:.&40.Vsp,(;.(9.(22.Vav,)(20.#8.(1?.(0.(2.&8.))Vev,)))))#8.)(7.(0.(2.&8.))(11.(1;.&40.=))))")
(* [comment removed for export] *).
  Proof.
    destruct bsb_decomp as [tl E].
    match type of E with
    | bsb = ?p1 ++ ?p2 ++ ?p3 ++ ?mid ++ ?rest =>
        pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw (p1 ++ p2 ++ p3) mid rest 8%nat) as H
    end.
    rewrite <- !app_assoc in H.
    specialize (H E (length_n_to_le_8 _) lay_bsb_nw).
    rewrite !length_app in H. rewrite len_envp_ptrs in H.
    rewrite !length_n_to_le_8 in H.
    rewrite length_flat_map_le8, length_string_addrs_fst in H.
    unfold envp_off.
    match type of H with
    | rdn _ _ (sp + nat_to_word ?n) 8 = _ =>
        replace (8 + 8 * (length av + 1) + 8 * length ev)%nat with n by lia
    end.
    exact H.
  Qed.

  (* [comment removed for export] *)
  #[using="Hva Hve Hsp_hi bsb"] Lemma read_auxv_all : ltac2:(CDefT.buildp (gd_tbl_RefLayout ()) "(5.(3.(0.(2.&8.)))(6.Vsegs,Vstk,(:.&40.Vsp,(;.(24.Vav,Vev,)))#:0.)(7.(0.(2.&8.))(1=.Vph,(1>.Vsp,Vav,Vev,)Vuid,Vhw,)))")
(* [comment removed for export] *).
  Proof.
    destruct bsb_decomp as [tl E].
    match type of E with
    | bsb = ?p1 ++ ?p2 ++ ?p3 ++ ?p4 ++ ?mid ++ ?rest =>
        pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw (p1 ++ p2 ++ p3 ++ p4) mid rest 160%nat) as H
    end.
    rewrite <- !app_assoc in H.
    specialize (H E (length_auxv_bytes _ _ _ _) lay_bsb_nw).
    rewrite !length_app in H. rewrite len_envp_ptrs in H.
    rewrite !length_n_to_le_8 in H.
    rewrite length_flat_map_le8, length_string_addrs_fst in H.
    unfold auxv_off.
    match type of H with
    | rdn _ _ (sp + nat_to_word ?n) _ = _ =>
        replace (8 + 8 * (length av + 1) + 8 * (length ev + 1))%nat with n by lia
    end.
    exact H.
  Qed.

  (* [comment removed for export] *)
  #[using="Hva Hve Hsp_hi bsb"] Lemma read_auxv_word : ltac2:(CDefT.buildp (gd_tbl_RefLayout ()) "Pj,$4.P,(21.R1.#14.)(5.(3.(0.(2.&8.)))(6.Vsegs,Vstk,(:.&40.Vsp,(;.(9.(24.Vav,Vev,)(20.#8.R2.))))#8.)(7.(0.(2.&8.))(11.(25.(2.&40.)R2.(26.Vph,(1>.Vsp,Vav,Vev,)Vuid,Vhw,)(1;.&40.=)))))")
(* [comment removed for export] *).
  Proof.
    intros j Hj.
    rewrite <- nat_to_word_add_merge.
    rewrite (rdn_skipn segs stk 160 _ _ (8 * j) 8 read_auxv_all) by lia.
    f_equal. rewrite auxv_bytes_words.
    rewrite (flat_map_le8_decomp _ j) by (rewrite length_auxv_words; exact Hj).
    rewrite skipn_app_exact
      by (rewrite length_flat_map_le8, firstn_length_le by (rewrite length_auxv_words; lia); lia).
    apply firstn_app_exact. apply length_n_to_le_8.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="stk"] Lemma bsb_random_split : ltac2:(CDefT.buildp (gd_tbl_RefLayout ()) "(16.(0.(2.&8.))Lpre,(0.(2.&8.))(27.(5.(0.(2.&8.))Vbsb,(17.(2.&8.)R1.(28.(29.Vrdraw,))))(27.(5.(2.&40.)(1>.Vsp,Vav,Vev,)(:.&40.Vsp,(;.(1?.(2.&8.)R1.))))(5.$2:.(2;.(2<.(1?.(2.&8.)R1.))+8.)=))))")
(* [comment removed for export] *).
  Proof.
    unfold bsb, build_stack_bytes, at_random_ptr.
    rewrite (string_addrs_pair av). cbv beta iota.
    rewrite (string_addrs_pair ev). cbv beta iota zeta.
    match goal with
    | |- exists pre, ?raw ++ repeat ?z ?pd ++ at_random_bytes (ed_random rdraw) = _ /\ _ /\ _ =>
        exists (raw ++ repeat z pd)
    end.
    split; [rewrite <- !app_assoc; reflexivity|].
    rewrite !length_app, !repeat_length, !length_flat_map_le8, !length_string_addrs_fst,
      !length_n_to_le_8, length_auxv_bytes, !length_flatten_strings.
    unfold auxv_size.
    match goal with
    | |- _ /\ (Z.of_nat (?L' + _) mod 8 = 0)%Z => set (L := L')
    end.
    replace (8 + (length av + 1) * 8 + (length ev + 1) * 8 + 160
             + total_arg_bytes_nat av + total_arg_bytes_nat ev)%nat with L by lia.
    assert (Hpd : (0 <= (8 - Z.of_nat L mod 8) mod 8 < 8)%Z) by (apply Z.mod_pos_bound; lia).
    split; [reflexivity|].
    rewrite Nat2Z.inj_add, Z2Nat.id by lia.
    rewrite <- Zplus_mod_idemp_l. rewrite Zplus_mod_idemp_r.
    replace (Z.of_nat L mod 8 + (8 - Z.of_nat L mod 8))%Z with 8%Z by lia.
    reflexivity.
  Qed.

  #[using="Hva Hve Hsp_hi"] Lemma at_random_off : ltac2:(CDefT.buildp (gd_tbl_RefLayout ()) "(16.$4.Loff,$4.(27.(5.(2.&40.)(1>.Vsp,Vav,Vev,)(:.&40.Vsp,(;.R1.)))(27.(5.$4.(9.R1.#10.)(1?.(2.&8.)Vbsb,))(27.(5.$2:.(2;.(2<.R1.)+8.)=)Pj,$4.Pn,$4.P,(8.(9.R2.R1.)#10.)(5.(3.(0.(2.&8.)))(6.Vsegs,Vstk,(:.&40.(1>.Vsp,Vav,Vev,)(;.R3.))R2.)(7.(0.(2.&8.))(<.(2.&8.)R2.(=.(2.&8.)R3.(28.(29.Vrdraw,))))))))))")
(* [comment removed for export] *).
  Proof.
    destruct bsb_random_split as [pre [E [Hp Hmod]]].
    pose proof (length_at_random_bytes (ed_random rdraw)) as HL.
    exists (length pre). split; [exact Hp|]. split.
    { unfold bsb in E |- *. rewrite E, length_app, HL. reflexivity. }
    split; [exact Hmod|].
    intros j n Hjn. rewrite Hp, nat_to_word_add_merge.
    rewrite <- (firstn_skipn j (at_random_bytes (ed_random rdraw))) in E.
    rewrite app_assoc in E.
    rewrite <- (firstn_skipn n (skipn j (at_random_bytes (ed_random rdraw)))) in E.
    pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw (pre ++ firstn j (at_random_bytes (ed_random rdraw)))
                  (firstn n (skipn j (at_random_bytes (ed_random rdraw))))
                  (skipn n (skipn j (at_random_bytes (ed_random rdraw)))) n E) as H.
    assert (Hlen : length (pre ++ firstn j (at_random_bytes (ed_random rdraw))) = (length pre + j)%nat).
    { rewrite length_app, firstn_length_le by lia. reflexivity. }
    rewrite Hlen in H.
    apply H; [rewrite firstn_length_le; [reflexivity | rewrite length_skipn; lia] | exact lay_bsb_nw].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Hva Hve"] Lemma lay_bsb_len : (Z.of_nat (length bsb) <= 2240000)%Z.
  Proof. exact (bsb_bound ph sp av ev uid hw rdraw Hva Hve). Qed.

  #[using="stk"] Lemma auxv_off_bound : (auxv_off av ev + 160 + 16 <= length bsb)%nat.
  Proof.
    unfold bsb, build_stack_bytes. cbv zeta.
    rewrite (string_addrs_pair av). cbv beta iota.
    rewrite (string_addrs_pair ev). cbv beta iota.
    rewrite !length_app, length_at_random_bytes, !repeat_length, !length_flat_map_le8,
      !length_string_addrs_fst, !length_n_to_le_8, length_auxv_bytes,
      !length_flatten_strings.
    unfold auxv_size, auxv_off. lia.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Type"] Lemma cat_envp_ptr_eq : ltac2:(CDefT.buildp (gd_tbl_RefLayout ()) "Pk,$4.P,(21.R1.(1?.(0.(2.&8.))Vev,))(5.(2.&40.)(23.Vsp,Vav,Vev,R2.)(:.&40.Vsp,(;.(9.(9.(2=.Vav,Vev,)(2>.Vav,))(2>.(<.(0.(2.&8.))R2.Vev,))))))")
(* [comment removed for export] *).
  Proof.
    intros k Hk. unfold cat_envp_ptr. rewrite nth_string_addrs by exact Hk.
    unfold cat_env_base, cat_string_base. rewrite !nat_to_word_add_merge.
    rewrite Nat.add_assoc. reflexivity.
  Qed.

  #[using="ph sp rdraw av uid hw Hve stk"] Lemma total_firstn_ev_bound : forall k,
    (Z.of_nat (total_arg_bytes_nat (firstn k ev)) <= 131072)%Z.
  Proof.
    intros k. destruct Hve as [_ [Htot _]]. rewrite total_arg_bytes_Z in Htot.
    pose proof (total_arg_bytes_firstn_le k ev). lia.
  Qed.

  #[using="ph sp rdraw uid hw Hva Hve stk"] Lemma struct_av_bound :
    (Z.of_nat (cat_struct_size av ev + total_arg_bytes_nat av) <= 2107576)%Z.
  Proof.
    destruct Hva as [[Hl0 Hl] [Hta _]]. destruct Hve as [Hle _].
    rewrite total_arg_bytes_Z in Hta. unfold cat_struct_size, auxv_size. lia.
  Qed.

  #[using="ph rdraw uid hw Hva Hve Hsp_lo Hsp_hi stk"] Lemma u_cat_envp_ptr : ltac2:(CDefT.buildp (gd_tbl_RefLayout ()) "Pk,$4.P,(21.R1.(1?.(0.(2.&8.))Vev,))(5.$2:.(2?.&40.(23.Vsp,Vav,Vev,R2.))(30.(2?.&40.Vsp,)(2<.(9.(9.(2=.Vav,Vev,)(2>.Vav,))(2>.(<.(0.(2.&8.))R2.Vev,))))))")
(* [comment removed for export] *).
  Proof.
    intros k Hk. rewrite cat_envp_ptr_eq by exact Hk. rewrite word_add_nat.
    pose proof struct_av_bound. pose proof (total_firstn_ev_bound k).
    unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
    apply u_Z2bv; lia.
  Qed.

  #[using="ph rdraw uid hw Hva Hve Hsp_lo Hsp_hi stk"] Lemma cat_envp_ptr_nz : forall k, (k < length ev)%nat ->
    bv_unsigned (cat_envp_ptr sp av ev k) <> 0%Z.
  Proof.
    intros k Hk. rewrite u_cat_envp_ptr by exact Hk. unfold sp_window_lo in Hsp_lo. lia.
  Qed.

  #[using="ph rdraw uid hw Hva Hve Hsp_lo Hsp_hi stk"] Lemma u_cat_argv_ptr : ltac2:(CDefT.buildp (gd_tbl_RefLayout ()) "Pk,$4.P,(21.R1.(1?.(0.(2.&8.))Vav,))(5.$2:.(2?.&40.(31.Vsp,Vav,Vev,R2.))(30.(2?.&40.Vsp,)(2<.(9.(2=.Vav,Vev,)(2>.(<.(0.(2.&8.))R2.Vav,))))))")
(* [comment removed for export] *).
  Proof.
    intros k Hk. rewrite cat_argv_ptr_offset by exact Hk. unfold cat_string_base.
    rewrite nat_to_word_add_merge, word_add_nat.
    pose proof struct_av_bound. pose proof (total_arg_bytes_firstn_le k av).
    unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
    apply u_Z2bv; lia.
  Qed.

  #[using="Hva"] Lemma argv_str_len : forall k, (k < length av)%nat ->
    (Z.of_nat (length (nth k av [])) <= 131071)%Z.
  Proof. intros k Hk. exact (valid_argv_str_len av k Hva Hk). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma auxv_words_eq : ltac2:(CDefT.buildp (gd_tbl_RefLayout ()) "Prnd,(2.&40.)(5.(0.(2.&40.))(26.Vph,R1.Vuid,Vhw,)(12.(2.&40.)$32.(12.(2.&40.)(1;.&40.(33.(34.Vph,)))(12.(2.&40.)$35.(12.(2.&40.)(1;.&40.(33.(36.Vph,)))(12.(2.&40.)$37.(12.(2.&40.)(1;.&40.(33.(38.Vph,)))(12.(2.&40.)$39.(12.(2.&40.)Vhw,(12.(2.&40.)$3:.(12.(2.&40.)(1;.&40.+1000.)(12.(2.&40.)$3;.(12.(2.&40.)Vuid,(12.(2.&40.)$3<.(12.(2.&40.)Vuid,(12.(2.&40.)$3=.(12.(2.&40.)(1;.&40.=)(12.(2.&40.)$3>.(12.(2.&40.)R1.(12.(2.&40.)$3?.(12.(2.&40.)(1;.&40.=)(15.(2.&40.)))))))))))))))))))))))")
(* [comment removed for export] *).
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Hva Hve Hsp_lo Hsp_hi"] Lemma rnd_facts : ltac2:(CDefT.buildp (gd_tbl_RefLayout ()) "PHal,(5.$2:.(2;.(2?.&40.Vsp,)+10.)=)(27.(40.(2?.&40.Vsp,)(2?.&40.(1>.Vsp,Vav,Vev,)))(27.(40.(30.(2?.&40.(1>.Vsp,Vav,Vev,))+10.)(30.(2?.&40.Vsp,)(2<.(1?.(2.&8.)Vbsb,))))(27.(41.(30.(2?.&40.Vsp,)(2<.(1?.(2.&8.)Vbsb,)))(42.+2.+40.))(27.(5.$2:.(2;.(2?.&40.(1>.Vsp,Vav,Vev,))+8.)=)Pj,$4.Pn,$4.P,(8.(9.R2.R1.)#10.)(5.(3.(0.(2.&8.)))(6.Vsegs,Vstk,(1;.&40.(30.(2?.&40.(1>.Vsp,Vav,Vev,))(2<.R3.)))R2.)(7.(0.(2.&8.))(<.(2.&8.)R2.(=.(2.&8.)R3.(28.(29.Vrdraw,))))))))))")
(* [comment removed for export] *).
  Proof.
    intros Hal.
    destruct at_random_off as [off [Hp [Hlen [Hmod Hrd]]]].
    pose proof lay_bsb_nw as Hnw. pose proof lay_bsb_len as Hbl.
    unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
    assert (Hu : bv_unsigned (at_random_ptr sp av ev) = (bv_unsigned sp + Z.of_nat off)%Z).
    { rewrite Hp, word_add_nat. apply u_Z2bv; lia. }
    rewrite Hu. split; [lia|]. split; [lia|]. split; [lia|]. split.
    - rewrite Z.add_mod by lia.
      replace (bv_unsigned sp mod 8)%Z with 0%Z.
      2:{ symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
      rewrite Hmod. reflexivity.
    - intros j n Hjn. rewrite <- Hu. rewrite <- word_add_nat. apply Hrd. exact Hjn.
  Qed.

End Layout.
