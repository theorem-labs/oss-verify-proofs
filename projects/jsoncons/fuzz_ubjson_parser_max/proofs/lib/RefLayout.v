(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec SeqExec StepTac ArgvEnv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__RefLayout () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefLayout."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1app"; "1cons"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1snd"; "2and"; "2eq"; "2ex"; "2not"; "3add"]; ["3mul"; "4le"; "4lt"; "5firstn"; "5nth"; "5skipn"; "6Z"; "0Hal"; "7len_word"; "7nat_to_word"; "7word_le8"; "8PhdrInfo"; "8Segment"; "8ph_addr"; "8ph_ent"; "8ph_num"]; ["9AT_EUID"; "9AT_HWCAP"; "9AT_NULL"; "9AT_PAGESZ"; "9AT_PHDR"; "9AT_PHENT"; "9AT_PHNUM"; "9AT_RANDOM"; "9AT_SECURE"; "9AT_UID"; "9at_random_bytes"; "9at_random_ptr"; "9auxv_bytes"; "9build_auxv"; "9ed_random"; "9string_addrs"]; [":cat_argv_ptr"; ":cat_env_base"; ":cat_string_base"; ":cat_struct_size"; ";rdn"; ";total_arg_bytes_nat"; "<auxv_off"; "<auxv_words"; "<cat_envp_ptr"; "<envp_off"; "=flat_map"; ">add"; ">le"; ">lt"; ">modulo"; ">of_N"]; [">of_nat"; ">pow"; "0a"; "0av"; "0bs"; "0bsb"; "0e"; "0entries"; "0ev"; "0hw"; "0j"; "0k"; "0mem"; "0n"; "0off"; "0ph"]; ["0pre"; "0rdraw"; "0rnd"; "0segs"; "0sp"; "?Z_to_bv"; "?bv"; "?bv_add"; "?bv_unsigned"; "0stk"; "0strs_tail"; "0uid"]]).
Lemma rdn_skipn : ltac2:(TCodec.tc2 tcn__RefLayout "QD'5'L%211'RFyR0%211'8y8%511%311p051'6%<14'<%812&QDr7r6r4r5%544321(0r3%22;1%;3:41'A&?r2%2261%421<r9r8&RG&I%11@%33OB1%E4651>&C&E%13OED%33Q0B1%D2M1%M3L61p0>1p0D1pTHQ21pTNQ31pT:Q31pT6Q;1pTLQ61pTJQ81pU8QA1").
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
Definition cat_envp_ptr (sp : word) (av ev : list (list byte)) (k : nat) : word :=
nth k (fst (string_addrs (cat_env_base sp av ev) ev)) (Z_to_bv 64 0).
Definition envp_off (av : list (list byte)) : nat := (8 + 8 * (length av + 1))%nat.
Definition auxv_off (av ev : list (list byte)) : nat :=
(8 + 8 * (length av + 1) + 8 * (length ev + 1))%nat.
Definition auxv_words (ph : PhdrInfo) (rnd uid hw : word) : list word :=
flat_map (fun e => [fst e; snd e]) (auxv_entries ph rnd uid hw).
Lemma build_auxv_words : ltac2:(TCodec.tc2 tcn__RefLayout "N'5'9'RFyR0%211%4211%611'<y8%711%:11&Q=r1%211&QJ&J(2&3%13>>6&:%13@@8(7%11B%73C31%83D61qT>D1%<4EF1>%=4GB<1%E3B?1pT@G1").
Proof.
induction entries as [|[t v] es IH]; [reflexivity|].
cbn [build_auxv flat_map fst snd app].
change (build_auxv es) with
(flat_map (fun e : bv 64 * bv 64 => word_le8 (fst e) ++ word_le8 (snd e)) es) in IH.
rewrite IH, <- app_assoc. reflexivity.
Qed.
Lemma auxv_bytes_words : ltac2:(TCodec.tc2 tcn__RefLayout "I'K'RFyR0%211'<'5y8%611%311&Q<r4r3r2r1%544321&QJ&J&QG%148765%44@<31%@3<61pTDB1pUHC1pU6D1pU0H1").
Proof. intros. unfold auxv_bytes, auxv_words. apply build_auxv_words. Qed.
Lemma length_auxv_words : ltac2:(TCodec.tc2 tcn__RefLayout "D'K'RFyR0%211'<'6&4&QGr4r3r2r1%544321%72:1uD%;3:21pTD=1pUH>1pU6?1pU0C1").
Proof. reflexivity. Qed.
Section Layout.
Variable segs : list Segment.
Variable ph : PhdrInfo.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable av ev : list (list byte).
Variable uid : word.
Variable hw : word.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.
Let bsb := build_stack_bytes ph sp av ev uid hw rdraw.
Let stk := stack_to_mem sp (entry_stack_image ph sp av ev uid hw rdraw).
Lemma lay_bsb_nw : ltac2:(TCodec.tc2 tcn__RefLayout "D&QM&QK&RHyR0vRD%3221&R0&4'RFy8%211vR5%5221%711%=291&R1+2+R0%3221%C251").
Proof. exact (bsb_nw ph sp av ev uid hw rdraw Hva Hve Hsp_hi). Qed.
Lemma lay_len_av : ltac2:(TCodec.tc2 tcn__RefLayout "?';'Au1&4'5'RFy8%211%411vR3%7221%:291uQP0%<231%>231").
Proof. destruct Hva as [[H1 H2] _]. lia. Qed.
Lemma lay_len_ev : ltac2:(TCodec.tc2 tcn__RefLayout ";'A&4'5'RFy8%211%411vR8%7221uX0%:221").
Proof. destruct Hve as [H1 _]. lia. Qed.
Lemma bsb_decomp : ltac2:(TCodec.tc2 tcn__RefLayout "QE'='5'RFy8%211%411'<vR5&1&J&HvR3%2271%411&QJyR0%>11&3%A12&Q?&QBvRDvR8%332<1%521=%83791%<4:FA1%C3G>1&REz%22?1%F11&QA%13<F;%?21<%B3AC1%F4DQ0K1&Q<vR?&Q;%13CMBvRKvR9%645321r1%Q53Q921%Q63Q:?1%Q73Q;;1%Q83Q<A1%Q93Q=F1%Q<3Q=Q;1qUFQ>1%QD2Q?1").
Proof.
unfold bsb, build_stack_bytes, cat_env_base, cat_string_base, cat_struct_size.
rewrite (string_addrs_pair av). cbv beta iota.
rewrite (string_addrs_pair ev). cbv beta iota.
eexists. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma len_argc_argv : ltac2:(TCodec.tc2 tcn__RefLayout "Q4'<'6&4'RFy8%211&1&J&H'5%115vR3%4221%611&QJyR0%=11&3%912&Q?&QBvRDvR8%332<1%521=%83791%<4:EC1%E3F>1%J2G1&?u8&@%N2FE%2231%5241%Q33Q271").
Proof.
rewrite length_app, length_n_to_le_8, length_flat_map_le8, length_string_addrs_fst. lia.
Qed.
Lemma len_envp_ptrs : ltac2:(TCodec.tc2 tcn__RefLayout "M'<'6&4'RFy8%211&QJyR0%511&J&3'5%114&Q?&QAvRDvR3vR8%43321%6212%:38<1%?4=@<1%D2A1&@u8%>1D%H219%4231%L3K61").
Proof. rewrite length_flat_map_le8, length_string_addrs_fst. lia. Qed.
Lemma read_argv_null : ltac2:(TCodec.tc2 tcn__RefLayout "Q2'<'8'5'RFy8%211%411%611&QDvRCvRI&RGyR0vRD&I&?u8&@&4vR3%22>1%4251%7261%911%=3<;1%A4@?19(0&J&REz%22B1%411%62J1%Q13J81").
Proof.
destruct bsb_decomp as [tl E].
pose proof (read_at_offset_image segs ph sp av ev uid hw rdraw _ (word_le8 (Z_to_bv 64 0)) _ 8%nat E
(length_n_to_le_8 _) lay_bsb_nw) as H.
rewrite len_argc_argv in H. exact H.
Qed.
Lemma read_envp_ptr_k : ltac2:(TCodec.tc2 tcn__RefLayout "Q;'6&Br1&4'5'RFy8%211%411vR8%7221%:291'<'8%116&QDvRCvRI&RGyR0vRD&I&?&QIvR3%211&@u8r2%3221%8251%:11%>3=<1%B4A@16(0&J&QH%14A=L9%311%52O1%L3J71p0N1pTHQ:1").
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
Lemma read_envp_null : ltac2:(TCodec.tc2 tcn__RefLayout "Q5'<'8'5'RFy8%211%411%611&QDvRCvRI&RGyR0vRD&I&?&QIvR3%211&@u8&4vR8%22A1%5241%:271%<11%@3?>1%D4CB18(0&J&REz%22E1%411%62M1%Q43M81").
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
Lemma read_auxv_all : ltac2:(TCodec.tc2 tcn__RefLayout "Q1'<'8'5'RFy8%211%411%611&QDvRCvRI&RGyR0vRD&I&QFvR3vR8%3221%511%93871uU0%>4=<21(0&Q<vR?&Q;%13>;:vRKvR9%645321%82I1%Q03I:1").
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
Lemma read_auxv_word : ltac2:(TCodec.tc2 tcn__RefLayout "QE'6&Br1uD%3221'<'8'5'RFy8%211%411%611&QDvRCvRI&RGyR0vRD&I&?&QFvR3vR8%3221&@u8r2%3221%9251%;11%?3>=1%C4BA16(0&J&D%L1C&QGvR?&Q;%13FBAvRKvR9%645321&REz%22M1%<4;D41%>11%@2Q61%Q=3Q6B1p0Q?1pTFQD1").
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
Lemma bsb_random_split : ltac2:(TCodec.tc2 tcn__RefLayout "Q<'='5'RFy8%211%411';'<vR5&1r1&Q:&Q>vRA%211%411%73<61%:3<91yR0%A11&Q;vRDvR3vR8%43321&RG&I&4%12HB%311%53<91%H3<71'F&QN&R0%117+8%4221z%Q03721%Q2291%Q32H1qU2Q51%Q;2Q61").
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
Lemma at_random_off : ltac2:(TCodec.tc2 tcn__RefLayout "R6'='6';'<'RFyR0%211&Q;vRDvR3vR8%43321&RG&Ir1%211%43;81%>3;61&?u@%2261&4y8%C11vR5%4221%G3I61'F&QN&R0%11@+8%4221z%O3721'Ar2%C21G%321C'8'5%11B%311&QDvRCvRIr3%Q211%Q43Q;Q51%64541=(0&C&E&Q:&Q>vRA%211%411%63Q3<1%83Q4G1%:2C1%QJ3C<1p0H1pTLQN1pTFQO1%QO2O1%R02Q81%R12QB1qTNR31%R52R41").
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
Lemma lay_bsb_len : ltac2:(TCodec.tc2 tcn__RefLayout ";&QL&R0&4'RFy8%211vR5%5221%711+RT[`0%:221").
Proof. exact (bsb_bound ph sp av ev uid hw rdraw Hva Hve). Qed.
Lemma auxv_off_bound : ltac2:(TCodec.tc2 tcn__RefLayout "A'A&?&QFvR3vR8%3221uU0%6221u@%8221&4'RFy8%211vR5%5221%@271").
Proof.
unfold bsb, build_stack_bytes. cbv zeta.
rewrite (string_addrs_pair av). cbv beta iota.
rewrite (string_addrs_pair ev). cbv beta iota.
rewrite !length_app, length_at_random_bytes, !repeat_length, !length_flat_map_le8,
!length_string_addrs_fst, !length_n_to_le_8, length_auxv_bytes,
!length_flatten_strings.
unfold auxv_size, auxv_off. lia.
Qed.
Lemma cat_envp_ptr_eq : ltac2:(TCodec.tc2 tcn__RefLayout "Q5'6&Br1&4'5'RFy8%211%411vR8%7221%:291'<yR0%911&QHvRDvR3r2%4432:1&RG&I&?&QC%127?&QE%119%5231&C%13E;D%511%9241%;11%=3DA1%F3D?1p0H1pTHQ41").
Proof.
intros k Hk. unfold cat_envp_ptr. rewrite nth_string_addrs by exact Hk.
unfold cat_env_base, cat_string_base. rewrite !nat_to_word_add_merge.
rewrite Nat.add_assoc. reflexivity.
Qed.
Lemma total_firstn_ev_bound : ltac2:(TCodec.tc2 tcn__RefLayout "B'6&QL&R0&QE&C'5'RFy8%211%411r1vR8%83321%:11%<11+TPP0%?221pTHA1").
Proof.
intros k. destruct Hve as [_ [Htot _]]. rewrite total_arg_bytes_Z in Htot.
pose proof (total_arg_bytes_firstn_le k ev). lia.
Qed.
Lemma struct_av_bound : ltac2:(TCodec.tc2 tcn__RefLayout "=&QL&R0&?&QCvR3vR8%3221&QE%114%7231%911+RPZUH%<221").
Proof.
destruct Hva as [[Hl0 Hl] [Hta _]]. destruct Hve as [Hle _].
rewrite total_arg_bytes_Z in Hta. unfold cat_struct_size, auxv_size. lia.
Qed.
Lemma u_cat_envp_ptr : ltac2:(TCodec.tc2 tcn__RefLayout "Q8'6&Br1&4'5'RFy8%211%411vR8%7221%:291'<'F&RHyR0&QHvRDvR3r2%4432;1%7261&QK%9286&R0&?&QC%129B&QE%11;%5231&C%13H=G%511%9241%;11%>2=1%I3H@1p0K1pTHQ71").
Proof.
intros k Hk. rewrite cat_envp_ptr_eq by exact Hk. rewrite word_add_nat.
pose proof struct_av_bound. pose proof (total_firstn_ev_bound k).
unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
apply u_Z2bv; lia.
Qed.
Lemma cat_envp_ptr_nz : ltac2:(TCodec.tc2 tcn__RefLayout "L'6&Br1&4'5'RFy8%211%411vR8%7221%:291&>'<'F&RHyR0&QHvRDvR3r2%4432<1%7261z%;3:21%=11p0?1pTHK1").
Proof.
intros k Hk. rewrite u_cat_envp_ptr by exact Hk. unfold sp_window_lo in Hsp_lo. lia.
Qed.
Lemma u_cat_argv_ptr : ltac2:(TCodec.tc2 tcn__RefLayout "Q6'6&Br1&4'5'RFy8%211%411vR3%7221%:291'<'F&RHyR0&Q@vRDvR8r2%443;21%7261&QK%9286&R0&?&QC%12B9&QE&C%13F;E%311%7251%911%<2;1%G3F>1p0I1pTHQ51").
Proof.
intros k Hk. rewrite cat_argv_ptr_offset by exact Hk. unfold cat_string_base.
rewrite nat_to_word_add_merge, word_add_nat.
pose proof struct_av_bound. pose proof (total_arg_bytes_firstn_le k av).
unfold sp_window_hi in Hsp_hi. unfold sp_window_lo in Hsp_lo.
apply u_Z2bv; lia.
Qed.
Lemma argv_str_len : ltac2:(TCodec.tc2 tcn__RefLayout "I'6&Br1&4'5'RFy8%211%411vR3%7221%:291&QL&R0&Dr2(7%11:%44:391%@2<1%711+SooO%:221p0<1pTHH1").
Proof. intros k Hk. exact (valid_argv_str_len av k Hva Hk). Qed.
Lemma auxv_words_eq : ltac2:(TCodec.tc2 tcn__RefLayout "R1'RFyR0%211'<'5%113&QGvR?r1vRKvR9%544321(2&Q4&RE&QO&M%11:%311%52B1&Q5&N%11?%811%:2G1&Q6&O%11D%=11%?2L1&Q1&Q3+TP0%C2Q01&Q9&Q0&Q8z%H2Q51&Q7&Q2(7%11Q8%O3Q951%Q03Q:41%Q13Q;Q51%Q23Q<71%Q33Q=91%Q43Q><1%Q53Q?Q81%Q63Q@?1%Q73QAQ:1%Q83QBB1%Q93QCD1%Q:3QDG1%Q;3QEQ=1%Q<3QFJ1%Q=3QGL1%Q>3QHQ11%Q?3QIQ31%Q@3QJQ81%QA3QKQ:1%QB3QLQA1%QL3QJQD1pU6QN1").
Proof. reflexivity. Qed.
Lemma rnd_facts : ltac2:(TCodec.tc2 tcn__RefLayout "RA'<'F&QN&RHyR0vRD%3221+@%6221z%:3921';&QL&Q;vR3vR8%33;21%>2=1%62<1&QK%123=&R0&4'RFy8%211vR5%5221%711%:2G1%B2:1&QM&R1+2+R0%3221%5271+8%Q42E1%Q73Q61N'6'A&?r2r1%3221u@%6221'8'5%11I%311&QDvRCvRI&REr3%Q411%Q72Q91%42QG1%84761A(0&C&E&Q:&Q>vRA%211%411%63Q<=1%83Q=K1%:2E1%R83E<1p0J1pTLQ21pTFQ31%R12Q51%R22Q91%R32Q@1%R42QM1pQ@R61").
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
