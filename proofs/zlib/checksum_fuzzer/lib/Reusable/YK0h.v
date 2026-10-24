(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n YK11 YK0i.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Section c.
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
Lemma wbytes_above : forall bs m (addr x : word),
(bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
wbytes m addr bs x = m x.
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
Lemma rdn_wbytes_disjoint : forall segs bs m (addr a : word) n,
(bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned a)%Z ->
(bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
rdn segs (wbytes m addr bs) a n = rdn segs m a n.
Proof.
intros segs bs m addr a n Hle Hnw. apply rdn_ext; [exact Hnw|].
intros x Hx. apply wbytes_above. lia.
Qed.
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
Lemma rdn_wbytes_below : forall segs bs m (addr a : word) n,
(bv_unsigned a + Z.of_nat n <= bv_unsigned addr)%Z ->
(bv_unsigned addr + Z.of_nat (length bs) <= 2^64)%Z ->
rdn segs (wbytes m addr bs) a n = rdn segs m a n.
Proof.
intros segs bs m addr a n Hle Hnw.
pose proof (u64_range addr) as Ha.
apply rdn_ext; [lia|].
intros x Hx. apply wbytes_below; [exact Hnw|lia].
Qed.
Lemma rdn_wbytes_out : forall segs bs m (addr a : word) n,
(bv_unsigned a + Z.of_nat n <= bv_unsigned addr
\/ bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned a)%Z ->
(bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
(bv_unsigned addr + Z.of_nat (length bs) <= 2^64)%Z ->
rdn segs (wbytes m addr bs) a n = rdn segs m a n.
Proof.
intros segs bs m addr a n [Hb|Hd] Hnw Hnw'.
- apply rdn_wbytes_below; [exact Hb | exact Hnw'].
- apply rdn_wbytes_disjoint; [exact Hd | exact Hnw].
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
Lemma stack_max_size_val : stack_max_size = 8388608%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma wrap_mem_below : forall ph (sp : word) argv envp (addr : word) uid hw rnd,
(bv_unsigned addr < bv_unsigned sp - stack_max_size)%Z ->
wrap_mem ph sp argv envp uid hw rnd addr = None.
Proof.
intros ph sp argv envp addr uid hw rnd Hlt.
pose proof stack_max_size_val as Hsms.
unfold wrap_mem, stack_to_mem.
assert (Hsp : Z.leb (bv_unsigned sp) (bv_unsigned addr) = false)
by (apply Z.leb_gt; lia).
rewrite Hsp.
assert (Hgate : Z.leb (bv_unsigned sp - stack_max_size) (bv_unsigned addr) = false)
by (apply Z.leb_gt; lia).
rewrite Hgate. reflexivity.
Qed.
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
Lemma natN_le : forall n m, (n <= m)%nat -> (N.of_nat n <= N.of_nat m)%N.
Proof. intros n m H. lia. Qed.
Lemma of_nat_131071 : Z.of_nat 131071 = 131071%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma of_nat_2097152 : Z.of_nat 2097152 = 2097152%Z.
Proof. vm_compute. reflexivity. Qed.
Definition cat_struct_size (av ev : list (list byte)) : nat :=
(8 + (length av + 1) * 8 + (length ev + 1) * 8 + auxv_size)%nat.
Definition cat_string_base (sp : word) (av ev : list (list byte)) : word :=
sp + nat_to_word (cat_struct_size av ev).
Definition cat_env_base (sp : word) (av ev : list (list byte)) : word :=
cat_string_base sp av ev + nat_to_word (total_arg_bytes_nat av).
Definition cat_argv_ptr (sp : word) (av ev : list (list byte)) (k : nat) : word :=
nth k (fst (string_addrs (cat_string_base sp av ev) av)) (Z_to_bv 64 0).
Lemma nth_string_addrs : forall strs (base : word) k, (k < length strs)%nat ->
nth k (fst (string_addrs base strs)) (Z_to_bv 64 0)
= base + nat_to_word (total_arg_bytes_nat (firstn k strs)).
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
Lemma cat_argv_ptr_offset : forall sp av ev k, (k < length av)%nat ->
cat_argv_ptr sp av ev k
= cat_string_base sp av ev + nat_to_word (total_arg_bytes_nat (firstn k av)).
Proof. intros. unfold cat_argv_ptr. apply nth_string_addrs. assumption. Qed.
Definition cat_struct_prefix (ph : PhdrInfo) (sp : word) (av ev : list (list byte))
(uid : word) (hw : word) : list byte :=
word_le8 (len_word av)
++ flat_map word_le8 (fst (string_addrs (cat_string_base sp av ev) av))
++ word_le8 (Z_to_bv 64 0)
++ flat_map word_le8 (fst (string_addrs (cat_env_base sp av ev) ev))
++ word_le8 (Z_to_bv 64 0) ++ auxv_bytes ph (at_random_ptr sp av ev) uid hw.
Lemma length_cat_struct_prefix : forall ph sp av ev uid hw,
length (cat_struct_prefix ph sp av ev uid hw) = cat_struct_size av ev.
Proof.
intros ph sp av ev uid hw. unfold cat_struct_prefix, cat_struct_size.
rewrite !length_app, !length_flat_map_le8, !length_string_addrs_fst,
!length_n_to_le_8, length_auxv_bytes.
lia.
Qed.
Lemma bsb_argv_prefix : forall ph (sp : word) av ev uid hw rnd, exists tail,
build_stack_bytes ph sp av ev uid hw rnd =
word_le8 (len_word av)
++ flat_map word_le8 (fst (string_addrs (cat_string_base sp av ev) av))
++ tail.
Proof.
intros ph sp av ev uid hw rnd. unfold build_stack_bytes.
rewrite (string_addrs_pair av). cbv beta iota.
rewrite (string_addrs_pair ev). cbv beta iota.
eexists. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma bsb_ptr_k : forall ph (sp : word) av ev k uid hw rnd, (k < length av)%nat -> exists post,
build_stack_bytes ph sp av ev uid hw rnd =
(word_le8 (len_word av)
++ flat_map word_le8 (firstn k (fst (string_addrs (cat_string_base sp av ev) av))))
++ word_le8 (nth k (fst (string_addrs (cat_string_base sp av ev) av)) (Z_to_bv 64 0))
++ post.
Proof.
intros ph sp av ev k uid hw rnd Hk.
destruct (bsb_argv_prefix ph sp av ev uid hw rnd) as [tail E].
assert (Hk' : (k < length (fst (string_addrs (cat_string_base sp av ev) av)))%nat)
by (rewrite length_string_addrs_fst; exact Hk).
rewrite (flat_map_le8_decomp _ k Hk') in E.
eexists. rewrite E. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma read_argv_ptr_k : forall ph segs (sp : word) av ev k uid hw rnd, (k < length av)%nat ->
(bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)) < 2^64)%Z ->
rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
(sp + nat_to_word (8 + 8 * k)) 8%nat
= Some (word_le8 (cat_argv_ptr sp av ev k)).
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
Lemma bsb_strings_split : forall ph (sp : word) av ev uid hw rnd, exists tail,
build_stack_bytes ph sp av ev uid hw rnd = cat_struct_prefix ph sp av ev uid hw ++ flatten_strings av ++ tail.
Proof.
intros ph sp av ev uid hw rnd. unfold build_stack_bytes, cat_struct_prefix, cat_env_base, cat_string_base.
rewrite (string_addrs_pair av). cbv beta iota.
rewrite (string_addrs_pair ev). cbv beta iota.
eexists. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma bsb_byte_k : forall ph (sp : word) av ev k uid hw rnd, (k < length av)%nat -> exists pre post,
build_stack_bytes ph sp av ev uid hw rnd = pre ++ (nth k av [] ++ [Z_to_bv 8 0]) ++ post
/\ length pre = (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))%nat.
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
Lemma read_argv_byte_k : forall ph segs (sp : word) av ev k j uid hw rnd,
(k < length av)%nat -> (j <= length (nth k av []))%nat ->
(bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)) < 2^64)%Z ->
rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
(cat_argv_ptr sp av ev k + nat_to_word j) 1%nat
= Some [nth j (nth k av [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)].
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
Lemma read_argv_str_k : forall ph segs (sp : word) av ev k uid hw rnd, (k < length av)%nat ->
(bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)) < 2^64)%Z ->
rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd)) (cat_argv_ptr sp av ev k)
(length (nth k av []))
= Some (nth k av []).
Proof.
intros ph segs sp av ev k uid hw rnd Hk Hnw.
destruct (bsb_byte_k ph sp av ev k uid hw rnd Hk) as [pre [post [E Hlen]]].
pose proof (read_at_offset_image segs ph sp av ev uid hw rnd
pre (nth k av []) ([Z_to_bv 8 0] ++ post) (length (nth k av []))) as H.
rewrite Hlen in H.
replace (cat_argv_ptr sp av ev k)
with (sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))).
2:{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
rewrite nat_to_word_add_merge. reflexivity. }
apply H; [ | reflexivity | exact Hnw].
rewrite E. rewrite <- !app_assoc. reflexivity.
Qed.
Definition byte_at (s : list byte) (k : nat) : byte :=
nth k (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0).
Lemma nth_lt_byte_at : forall s j, (j < length s)%nat ->
byte_at s j = nth j s (Z_to_bv 8 0).
Proof. intros s j Hj. unfold byte_at. apply app_nth1. exact Hj. Qed.
Lemma byte_at_len : forall s, byte_at s (length s) = Z_to_bv 8 0.
Proof.
intros s. unfold byte_at. rewrite app_nth2 by lia.
rewrite Nat.sub_diag. reflexivity.
Qed.
Lemma byte_at_nz : forall s j, ~ In (Z_to_bv 8 0) s -> (j < length s)%nat ->
byte_at s j <> Z_to_bv 8 0.
Proof.
intros s j Hnz Hj Hc.
apply Hnz. rewrite <- Hc. rewrite nth_lt_byte_at by exact Hj.
apply nth_In. exact Hj.
Qed.
Lemma byte_at_bound : forall s j, (bv_unsigned (byte_at s j) < 256)%Z.
Proof. intros s j. unfold byte_at. apply nth_app0_bound. Qed.
Lemma valid_argv_len : forall av, valid_argv av ->
(Z.of_nat (length av) <= 1024)%Z.
Proof. intros av [Hlen _]. lia. Qed.
Lemma valid_argv_nonempty : forall av, valid_argv av -> (1 <= length av)%nat.
Proof. intros av [Hlen _]. lia. Qed.
Lemma valid_argv_str_len : forall av k, valid_argv av -> (k < length av)%nat ->
(Z.of_nat (length (nth k av [])) <= 131071)%Z.
Proof.
intros av k [_ [_ [Hstr _]]] Hk.
rewrite Forall_forall in Hstr.
specialize (Hstr _ (nth_In av [] Hk)). exact Hstr.
Qed.
Lemma valid_argv_str_nz : forall av k, valid_argv av -> (k < length av)%nat ->
~ In (Z_to_bv 8 0) (nth k av []).
Proof.
intros av k [_ [_ [_ [Hnz _]]]] Hk.
rewrite Forall_forall in Hnz. apply Hnz. apply nth_In. exact Hk.
Qed.
Lemma valid_argv_str_plain : forall av k, valid_argv av ->
(S k < length av)%nat ->
path_eqb (nth (S k) av []) dot_path = false ->
openat_plain_name (nth (S k) av []) = true.
Proof.
intros av k [_ [_ [_ [_ Hpl]]]] Hk Hdot.
assert (Hnth : nth (S k) av [] = nth k (tl av) []).
{ destruct av as [|a av']; [cbn in Hk; lia | reflexivity]. }
assert (Hk' : (k < length (tl av))%nat).
{ destruct av as [|a av']; cbn in *; lia. }
rewrite Forall_forall in Hpl.
destruct (Hpl _ (nth_In (tl av) [] Hk')) as [Hsl Hdd].
rewrite Hnth in Hdot |- *.
unfold openat_plain_name, path_is_dirref.
rewrite Hdot, Hsl, Hdd. reflexivity.
Qed.
Lemma valid_argv_str_bytes : forall av k, valid_argv av -> (k < length av)%nat ->
Forall (fun b : byte => (bv_unsigned b < 256)%Z) (nth k av []).
Proof.
intros av k _ _. apply Forall_forall. intros b _. apply u8_range.
Qed.
Lemma v_addi_pred : forall x : word, v_addi (x + 1) (-1) = x.
Proof.
intro x. apply bv_eq. unfold v_addi.
rewrite Z_to_bv_unsigned, bv_add_unsigned.
change (bv_unsigned (1 : word)) with 1%Z.
rewrite bv_wrap_add_idemp_l.
replace (bv_unsigned x + 1 + -1)%Z with (bv_unsigned x) by lia.
apply bv_wrap_bv_unsigned.
Qed.
Definition pend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
: machine_state :=
{| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := Some (Z_to_bv 64 64);
ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}.
Lemma adv_set : forall regs pc sv mem rom v,
advance_past_svc (set_gpr0
{| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |} v)
= mkst (regupd regs 10 v) (v_addi pc 4) mem rom.
Proof.
intros regs pc sv mem rom v.
unfold advance_past_svc, set_gpr0, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom].
unfold mkst, regupd.
rewrite b_npc4. reflexivity.
Qed.
Lemma tw_write_gen : forall segs regs pc mem rom buf bufs code,
ms_gpr (pend regs pc mem rom) 0 = Z_to_bv 64 1 ->
ms_read_bytes (pend regs pc mem rom)
(ms_gpr (pend regs pc mem rom) 1) (ms_gpr (pend regs pc mem rom) 2) = Some buf ->
(1 <= length buf)%nat ->
(forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
to_wexit segs (mkst (regupd regs 10 (len_word (firstn n buf)))
(v_addi pc 4) mem rom) bufs code) ->
to_wexit segs (pend regs pc mem rom) (buf :: bufs) code.
Proof.
intros segs regs pc mem rom buf bufs code Hg0 Hr Hnb Hcont.
eapply tw_write;
[reflexivity | reflexivity | exact Hg0 | exact Hr | exact Hnb | ].
intros n Hn1 Hn2. unfold pend. rewrite adv_set. apply Hcont; assumption.
Qed.
Lemma tw_exit0 : forall segs ms x8,
ms_svc_pending ms = Some x8 -> is_exit_no x8 ->
ms_gpr ms 0 = Z_to_bv 64 0 ->
to_wexit segs ms [] (Z_to_bv 64 0).
Proof.
intros segs ms x8 Hsvc Hex Hg0.
assert (Hc : bv_and (ms_gpr ms 0) (Z_to_bv 64 255) = Z_to_bv 64 0).
{ rewrite Hg0. apply bv_eq.
rewrite bv_and_unsigned, !Z_to_bv_unsigned. reflexivity. }
rewrite <- Hc. eapply tw_exit; eassumption.
Qed.
Lemma tw_write_rec : forall segs regs pc mem rom buf bufs code,
bv_unsigned (getr regs 17) = 64%Z ->
reg_get regs 10 = Z_to_bv 64 1 ->
ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |}
(reg_get regs 11) (reg_get regs 12) = Some buf ->
(1 <= length buf)%nat ->
(forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
to_wexit segs (mkst (regupd regs 10 (len_word (firstn n buf)))
(v_addi pc 4) mem rom) bufs code) ->
to_wexit segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |}
(buf :: bufs) code.
Proof.
intros segs regs pc mem rom buf bufs code H17 H10 Hr Hnb Hcont.
eapply tw_write.
- cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_0. exact H10.
- unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_1, arg_reg_2. exact Hr.
- exact Hnb.
- intros n Hn1 Hn2. rewrite adv_set. apply Hcont; assumption.
Qed.
Lemma tw_exit_rec : forall segs regs pc mem rom,
bv_unsigned (getr regs 17) = 93%Z ->
reg_get regs 10 = Z_to_bv 64 0 ->
to_wexit segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |} [] (Z_to_bv 64 0).
Proof.
intros segs regs pc mem rom H17 H10.
eapply tw_exit0.
- cbn [ms_svc_pending]. reflexivity.
- left. exact H17.
- unfold ms_gpr. cbn [ms_regs].
rewrite arg_reg_0. exact H10.
Qed.
End c.
