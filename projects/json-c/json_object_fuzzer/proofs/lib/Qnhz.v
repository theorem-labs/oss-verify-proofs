(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsV0 QsRG.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import QsV0 QsRG.Mq0 QsRG.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import ListNotations.
Open Scope bv_scope.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma ms_read_bytes_aux_rdn : forall segs ms n addr,
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

#[using="Type"] Lemma ms_read_bytes_rdn : forall segs ms addr len,
ms_rom ms = seg_rom segs ->
ms_read_bytes ms addr len = rdn segs (ms_mem ms) addr (word_to_nat len).
Proof. intros. unfold ms_read_bytes. apply ms_read_bytes_aux_rdn; assumption. Qed.

Fixpoint wbytes (m : word -> option byte) (addr : word) (bs : list byte)
: word -> option byte :=
match bs with
| [] => m
| b :: rest => wbytes (fun a => if bv_eqb a addr then Some b else m a) (addr+1) rest
end.

#[using="Type"] Lemma wbytes_above : forall bs m (addr x : word),
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

#[using="Type"] Lemma rdn_wbytes_disjoint : forall segs bs m (addr a : word) n,
(bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned a)%Z ->
(bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
rdn segs (wbytes m addr bs) a n = rdn segs m a n.
Proof.
intros segs bs m addr a n Hle Hnw. apply rdn_ext; [exact Hnw|].
intros x Hx. apply wbytes_above. lia.
Qed.

#[using="Type"] Lemma wbytes_below : forall bs m (addr x : word),
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

#[using="Type"] Lemma rdn_wbytes_below : forall segs bs m (addr a : word) n,
(bv_unsigned a + Z.of_nat n <= bv_unsigned addr)%Z ->
(bv_unsigned addr + Z.of_nat (length bs) <= 2^64)%Z ->
rdn segs (wbytes m addr bs) a n = rdn segs m a n.
Proof.
intros segs bs m addr a n Hle Hnw.
pose proof (u64_range addr) as Ha.
apply rdn_ext; [lia|].
intros x Hx. apply wbytes_below; [exact Hnw|lia].
Qed.

#[using="Type"] Lemma rdn_wbytes_out : forall segs bs m (addr a : word) n,
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

#[using="Type"] Lemma length_Z_to_le_bytes : forall n z, length (Z_to_le_bytes n z) = n.
Proof.
induction n as [|n IH]; intro z; [reflexivity|].
cbn [Z_to_le_bytes length]. rewrite IH. reflexivity.
Qed.

#[using="Type"] Lemma length_N_to_le_bytes : forall n (v : word), length (word_to_le_bytes n v) = n.
Proof. intros. unfold word_to_le_bytes. apply length_Z_to_le_bytes. Qed.

#[using="Type"] Lemma write_to_mem_wbytes : forall bs (m : word -> option byte) (addr : word),
write_to_mem m addr bs = wbytes m addr bs.
Proof.
induction bs as [|b rest IH]; intros m addr; [reflexivity|].
cbn [write_to_mem wbytes]. apply IH.
Qed.

#[using="Type"] Lemma step_sd : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
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

#[using="Type"] Lemma stack_max_size_val : stack_max_size = 8388608%Z.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma wrap_mem_below : forall ph (sp : word) argv envp (addr : word) uid hw rnd,
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

#[using="Type"] Lemma flat_map_app' : forall {A B : Type} (f : A -> list B) l1 l2,
flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof.
intros A B f l1 l2. induction l1 as [|x xs IH]; cbn; [reflexivity|].
rewrite IH, app_assoc. reflexivity.
Qed.

#[using="Type"] Lemma skipn_nth : forall {A : Type} (l : list A) k d, (k < length l)%nat ->
skipn k l = nth k l d :: skipn (S k) l.
Proof.
induction l as [|x xs IH]; intros k d Hk; [cbn in Hk; lia|].
destruct k as [|k']; [reflexivity|].
cbn [skipn nth]. apply IH. cbn in Hk; lia.
Qed.

#[using="Type"] Lemma flat_map_split : forall {A B : Type} (f : A -> list B) l k d, (k < length l)%nat ->
flat_map f l = flat_map f (firstn k l) ++ f (nth k l d) ++ flat_map f (skipn (S k) l).
Proof.
intros A B f l k d Hk.
rewrite <- (firstn_skipn k l) at 1.
rewrite flat_map_app'.
rewrite (skipn_nth l k d Hk). reflexivity.
Qed.

#[using="Type"] Lemma flat_map_le8_decomp : forall (l : list word) k, (k < length l)%nat ->
flat_map word_le8 l =
flat_map word_le8 (firstn k l) ++ word_le8 (nth k l (Z_to_bv 64 0))
++ flat_map word_le8 (skipn (S k) l).
Proof. intros l k Hk. apply (flat_map_split word_le8 l k (Z_to_bv 64 0) Hk). Qed.

#[using="Type"] Lemma flatten_strings_decomp : forall strs k, (k < length strs)%nat ->
flatten_strings strs =
flatten_strings (firstn k strs) ++ (nth k strs [] ++ [Z_to_bv 8 0])
++ flatten_strings (skipn (S k) strs).
Proof.
intros strs k Hk.
apply (flat_map_split (fun s => s ++ [Z_to_bv 8 0]) strs k [] Hk).
Qed.

#[using="Type"] Lemma total_arg_bytes_cons : forall s l,
total_arg_bytes_nat (s :: l) = (length s + 1 + total_arg_bytes_nat l)%nat.
Proof. reflexivity. Qed.

#[using="Type"] Lemma total_arg_bytes_firstn_le : forall k l,
(total_arg_bytes_nat (firstn k l) <= total_arg_bytes_nat l)%nat.
Proof.
induction k as [|k IH]; intros l.
- change (total_arg_bytes_nat (firstn 0 l)) with 0%nat. lia.
- destruct l as [|s rest]; [cbn; lia|].
cbn [firstn]. rewrite !total_arg_bytes_cons. specialize (IH rest). lia.
Qed.

#[using="Type"] Lemma natN_le : forall n m, (n <= m)%nat -> (N.of_nat n <= N.of_nat m)%N.
Proof. intros n m H. lia. Qed.

#[using="Type"] Lemma of_nat_131071 : Z.of_nat 131071 = 131071%Z.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma of_nat_2097152 : Z.of_nat 2097152 = 2097152%Z.
Proof. vm_compute. reflexivity. Qed.

Definition cat_struct_size (av ev : list (list byte)) : nat :=
(8 + (length av + 1) * 8 + (length ev + 1) * 8 + auxv_size)%nat.

Definition cat_string_base (sp : word) (av ev : list (list byte)) : word :=
sp + nat_to_word (cat_struct_size av ev).

Definition cat_env_base (sp : word) (av ev : list (list byte)) : word :=
cat_string_base sp av ev + nat_to_word (total_arg_bytes_nat av).

Definition cat_argv_ptr (sp : word) (av ev : list (list byte)) (k : nat) : word :=
nth k (fst (string_addrs (cat_string_base sp av ev) av)) (Z_to_bv 64 0).

#[using="Type"] Lemma nth_string_addrs : forall strs (base : word) k, (k < length strs)%nat ->
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

#[using="Type"] Lemma cat_argv_ptr_offset : forall sp av ev k, (k < length av)%nat ->
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

#[using="Type"] Lemma length_cat_struct_prefix : forall ph sp av ev uid hw,
length (cat_struct_prefix ph sp av ev uid hw) = cat_struct_size av ev.
Proof.
intros ph sp av ev uid hw. unfold cat_struct_prefix, cat_struct_size.
rewrite !length_app, !length_flat_map_le8, !length_string_addrs_fst,
!length_n_to_le_8, length_auxv_bytes.
lia.
Qed.

#[using="Type"] Lemma bsb_argv_prefix : forall ph (sp : word) av ev uid hw rnd, exists tail,
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

#[using="Type"] Lemma bsb_ptr_k : forall ph (sp : word) av ev k uid hw rnd, (k < length av)%nat -> exists post,
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

#[using="Type"] Lemma read_argv_ptr_k : forall ph segs (sp : word) av ev k uid hw rnd, (k < length av)%nat ->
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

#[using="Type"] Lemma bsb_strings_split : forall ph (sp : word) av ev uid hw rnd, exists tail,
build_stack_bytes ph sp av ev uid hw rnd = cat_struct_prefix ph sp av ev uid hw ++ flatten_strings av ++ tail.
Proof.
intros ph sp av ev uid hw rnd. unfold build_stack_bytes, cat_struct_prefix, cat_env_base, cat_string_base.
rewrite (string_addrs_pair av). cbv beta iota.
rewrite (string_addrs_pair ev). cbv beta iota.
eexists. rewrite <- !app_assoc. reflexivity.
Qed.

#[using="Type"] Lemma bsb_byte_k : forall ph (sp : word) av ev k uid hw rnd, (k < length av)%nat -> exists pre post,
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

#[using="Type"] Lemma read_argv_byte_k : forall ph segs (sp : word) av ev k j uid hw rnd,
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

#[using="Type"] Lemma read_argv_str_k : forall ph segs (sp : word) av ev k uid hw rnd, (k < length av)%nat ->
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

#[using="Type"] Lemma nth_lt_byte_at : forall s j, (j < length s)%nat ->
byte_at s j = nth j s (Z_to_bv 8 0).
Proof. intros s j Hj. unfold byte_at. apply app_nth1. exact Hj. Qed.

#[using="Type"] Lemma byte_at_len : forall s, byte_at s (length s) = Z_to_bv 8 0.
Proof.
intros s. unfold byte_at. rewrite app_nth2 by lia.
rewrite Nat.sub_diag. reflexivity.
Qed.

#[using="Type"] Lemma byte_at_nz : forall s j, ~ In (Z_to_bv 8 0) s -> (j < length s)%nat ->
byte_at s j <> Z_to_bv 8 0.
Proof.
intros s j Hnz Hj Hc.
apply Hnz. rewrite <- Hc. rewrite nth_lt_byte_at by exact Hj.
apply nth_In. exact Hj.
Qed.

#[using="Type"] Lemma byte_at_bound : forall s j, (bv_unsigned (byte_at s j) < 256)%Z.
Proof. intros s j. unfold byte_at. apply nth_app0_bound. Qed.

#[using="Type"] Lemma valid_argv_len : forall av, valid_argv av ->
(Z.of_nat (length av) <= 1024)%Z.
Proof. intros av [Hlen _]. lia. Qed.

#[using="Type"] Lemma valid_argv_nonempty : forall av, valid_argv av -> (1 <= length av)%nat.
Proof. intros av [Hlen _]. lia. Qed.

#[using="Type"] Lemma valid_argv_str_len : forall av k, valid_argv av -> (k < length av)%nat ->
(Z.of_nat (length (nth k av [])) <= 131071)%Z.
Proof.
intros av k [_ [_ [Hstr _]]] Hk.
rewrite Forall_forall in Hstr.
specialize (Hstr _ (nth_In av [] Hk)). exact Hstr.
Qed.

#[using="Type"] Lemma valid_argv_str_nz : forall av k, valid_argv av -> (k < length av)%nat ->
~ In (Z_to_bv 8 0) (nth k av []).
Proof.
intros av k [_ [_ [_ [Hnz _]]]] Hk.
rewrite Forall_forall in Hnz. apply Hnz. apply nth_In. exact Hk.
Qed.

#[using="Type"] Lemma valid_argv_str_plain : forall av k, valid_argv av ->
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

#[using="Type"] Lemma valid_argv_str_bytes : forall av k, valid_argv av -> (k < length av)%nat ->
Forall (fun b : byte => (bv_unsigned b < 256)%Z) (nth k av []).
Proof.
intros av k _ _. apply Forall_forall. intros b _. apply u8_range.
Qed.

#[using="Type"] Lemma v_addi_pred : forall x : word, v_addi (x + 1) (-1) = x.
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
{| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc; ms_svc_pending := Some (Z_to_bv 64 64);
ms_resv := None; ms_fcsr := fC; ms_mem := mem; ms_rom := rom |}.

#[using="Type"] Lemma adv_set : forall regs pc sv mem rom v,
advance_past_svc (set_gpr0
{| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fC;
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

#[using="Type"] Lemma tw_write_gen : forall segs regs pc mem rom buf bufs code,
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

#[using="Type"] Lemma tw_exit0 : forall segs ms x8,
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

#[using="Type"] Lemma tw_write_rec : forall segs regs pc mem rom buf bufs code,
bv_unsigned (getr regs 17) = 64%Z ->
reg_get regs 10 = Z_to_bv 64 1 ->
ms_read_bytes {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fC;
ms_mem := mem; ms_rom := rom |}
(reg_get regs 11) (reg_get regs 12) = Some buf ->
(1 <= length buf)%nat ->
(forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
to_wexit segs (mkst (regupd regs 10 (len_word (firstn n buf)))
(v_addi pc 4) mem rom) bufs code) ->
to_wexit segs {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fC;
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

#[using="Type"] Lemma tw_exit_rec : forall segs regs pc mem rom,
bv_unsigned (getr regs 17) = 93%Z ->
reg_get regs 10 = Z_to_bv 64 0 ->
to_wexit segs {| ms_regs := regs; ms_fregs := fF; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fC;
ms_mem := mem; ms_rom := rom |} [] (Z_to_bv 64 0).
Proof.
intros segs regs pc mem rom H17 H10.
eapply tw_exit0.
- cbn [ms_svc_pending]. reflexivity.
- left. exact H17.
- unfold ms_gpr. cbn [ms_regs].
rewrite arg_reg_0. exact H10.
Qed.
End FPGEN1.

End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwNp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs.
Import QwNp.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= Q6q3.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= Q6q3.mkr__nia_1.
Open Scope bv_scope.

Lemma syscall_spec_79 : forall i m o,
bv_unsigned (in_sysno i) = 79%Z ->
syscall_spec i m o <->
newfstatat_spec (fd32 (in_arg i 0)) (in_arg i 1) (flag32 (in_arg i 3)) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_113 : forall i m o,
bv_unsigned (in_sysno i) = 113%Z ->
syscall_spec i m o <-> clock_gettime_spec (clockid32 (in_arg i 0)) (in_arg i 1) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_216 : forall i m o,
bv_unsigned (in_sysno i) = 216%Z ->
syscall_spec i m o <-> mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma syscall_spec_278 : forall i m o,
bv_unsigned (in_sysno i) = 278%Z ->
syscall_spec i m o <-> getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma bind_input_model : forall (k : SyscallInput -> Model -> Sys SyscallEffect) i m o,
(bind input (fun i0 => bind get_model (fun m0 => k i0 m0))) i m o <-> k i m i m o.
Proof.
intros k i m o. unfold bind, input, get_model. destruct o as [eff m' evs|]; split.
- intros (i0 & m1 & e1 & e2 & Hi & (m0 & m2 & e3 & e4 & Hm & Hk & ->) & ->).
apply Ok_inj in Hi as (-> & -> & ->). apply Ok_inj in Hm as (-> & -> & ->). exact Hk.
- intros Hk. exists i, m, [], evs. split; [reflexivity|]. split; [|reflexivity].
exists m, m, [], evs. split; [reflexivity|]. split; [exact Hk|reflexivity].
- intros [H | (i0 & m1 & e1 & Hi & [H | (m0 & m2 & e2 & Hm & Hk)])];
[exfalso; exact (Unmodeled_Ok _ _ _ H) | exfalso; exact (Unmodeled_Ok _ _ _ H) |].
apply Ok_inj in Hi as (-> & -> & ->). apply Ok_inj in Hm as (-> & -> & ->). exact Hk.
- intros Hk. right. exists i, m, []. split; [reflexivity|]. right.
exists m, m, []. split; [reflexivity| exact Hk].
Qed.

Lemma bind_input : forall (k : SyscallInput -> Sys SyscallEffect) i m o,
(bind input (fun i0 => k i0)) i m o <-> k i i m o.
Proof.
intros k i m o. unfold bind, input. destruct o as [eff m' evs|]; split.
- intros (i0 & m1 & e1 & e2 & Hi & Hk & ->). apply Ok_inj in Hi as (-> & -> & ->). exact Hk.
- intros Hk. exists i, m, [], evs. split; [reflexivity|]. split; [exact Hk|reflexivity].
- intros [H | (i0 & m1 & e1 & Hi & Hk)]; [exfalso; exact (Unmodeled_Ok _ _ _ H)|].
apply Ok_inj in Hi as (-> & -> & ->). exact Hk.
- intros Hk. right. exists i, m, []. split; [reflexivity|exact Hk].
Qed.

Lemma bind_model : forall (k : Model -> Sys SyscallEffect) i m o,
(bind get_model (fun m0 => k m0)) i m o <-> k m i m o.
Proof.
intros k i m o. unfold bind, get_model. destruct o as [eff m' evs|]; split.
- intros (i0 & m1 & e1 & e2 & Hi & Hk & ->). apply Ok_inj in Hi as (-> & -> & ->). exact Hk.
- intros Hk. exists m, m, [], evs. split; [reflexivity|]. split; [exact Hk|reflexivity].
- intros [H | (i0 & m1 & e1 & Hi & Hk)]; [exfalso; exact (Unmodeled_Ok _ _ _ H)|].
apply Ok_inj in Hi as (-> & -> & ->). exact Hk.
- intros Hk. right. exists m, m, []. split; [reflexivity|exact Hk].
Qed.

Definition getrandom_out (buf buflen : word) (m : Model) (o : outcome SyscallEffect) : Prop :=
exists bs, Z.of_nat (length bs) = bv_unsigned buflen
/\ o = Ok (mkEffect (len_word bs) [(buf, bs)] []) m [].

Lemma getrandom_outcome : forall buf buflen flags i m o w,
(bv_unsigned flags = 0%Z \/ bv_unsigned flags = GRND_NONBLOCK) ->
modeled_rw_count buflen = true ->
w_is0 buflen = false ->
(bv_unsigned buflen <= getrandom_small_max)%Z ->
read_bytes_map (in_wmem i) buf buflen = Some w ->
getrandom_spec buf buflen flags i m o <-> getrandom_out buf buflen m o.
Proof.
intros buf buflen flags i m o w Hfl Hcnt Hnz Hsm Hw. unfold getrandom_spec.
replace (Z.eqb (bv_unsigned flags) 0 || Z.eqb (bv_unsigned flags) GRND_NONBLOCK) with true
by (symmetry; destruct Hfl as [-> | ->]; reflexivity).
clear Hfl. rewrite Hcnt. cbn [negb]. rewrite bind_input, Hw, Hnz. cbn [negb].
replace (bv_unsigned buflen <=? getrandom_small_max)%Z with true by (symmetry; apply Z.leb_le; exact Hsm).
unfold getrandom_out. sys_unfold.
split.
- destruct o as [x m' evs|]; intros H; inv_sys.
eexists; split; [eassumption|reflexivity].
- intros (bs & H1 & ->).
eexists _, _, _, _. split; [exists bs; split; [exact H1|reflexivity]|].
split; reflexivity.
Qed.

Lemma EINTR_in_getrandom_errnos : In EINTR getrandom_errnos.
Proof. left. reflexivity. Qed.

Definition stat_reads (i : SyscallInput) (pathp : word) : list (word * nat) :=
[(pathp, cstr_access_len_aux (in_mem i) pathp path_max)].

Lemma newfstatat_spec_body : forall dirfd pathp flags i m o,
newfstatat_spec dirfd pathp flags i m o <->
after_copyins (stat_reads i pathp) (newfstatat_core_spec dirfd pathp flags i m) o.
Proof.
intros dirfd pathp flags i m o. unfold newfstatat_spec.
rewrite (bind_input (fun i0 => _)). cbv beta. apply record_copyins_iff.
Qed.

Section Newfstatat.
Variables (dirfd pathp flags : word) (i : SyscallInput) (m : Model).
Hypothesis Hfl : bv_unsigned flags = 0%Z.

#[using="Hfl"] Lemma statat_flags0_modeled : modeled_statat_flags flags = true.
Proof. unfold modeled_statat_flags. rewrite Hfl. reflexivity. Qed.

#[using="Hfl"] Lemma newfstatat_core : forall o,
newfstatat_core_spec dirfd pathp flags i m o <->
match read_cstr (in_mem i) pathp with
| CstrTooLong => err_ret ENAMETOOLONG
| CstrFault => err_ret EFAULT
| CstrOk p =>
if path_eqb p [] then err_ret ENOENT
else if negb (bv_eqb dirfd AT_FDCWD32) then unmodeled
else if path_eqb p dot_path then unmodeled
else match fs_lookup (m_fs m) p with
| None => err_ret ENOENT
| Some _ => unmodeled
end
end i m o.
Proof.
intros o. unfold newfstatat_core_spec. rewrite (bind_input_model (fun i0 m0 => _)). cbv beta.
rewrite statat_flags0_modeled. cbn [negb]. reflexivity.
Qed.

#[using="Hfl"] Lemma newfstatat_toolong_outcome : forall o,
read_cstr (in_mem i) pathp = CstrTooLong ->
newfstatat_spec dirfd pathp flags i m o <->
o = Ok (with_copyins (stat_reads i pathp) (mkEffect (errno_ret ENAMETOOLONG) [] [])) m [].
Proof.
intros o Hp. rewrite newfstatat_spec_body. apply after_copyins_det.
intros o'. rewrite newfstatat_core, Hp. apply err_ret_outcome.
Qed.

#[using="Hfl"] Lemma newfstatat_empty_outcome : forall o,
read_cstr (in_mem i) pathp = CstrOk [] ->
newfstatat_spec dirfd pathp flags i m o <->
o = Ok (with_copyins (stat_reads i pathp) (mkEffect (errno_ret ENOENT) [] [])) m [].
Proof.
intros o Hp. rewrite newfstatat_spec_body. apply after_copyins_det.
intros o'. rewrite newfstatat_core, Hp. cbn [path_eqb]. apply err_ret_outcome.
Qed.

Hypothesis Hdir : dirfd = AT_FDCWD32.

#[using="Hfl Hdir"] Lemma newfstatat_absent_outcome : forall p o,
read_cstr (in_mem i) pathp = CstrOk p -> p <> [] -> p <> dot_path ->
fs_lookup (m_fs m) p = None ->
newfstatat_spec dirfd pathp flags i m o <->
o = Ok (with_copyins (stat_reads i pathp) (mkEffect (errno_ret ENOENT) [] [])) m [].
Proof.
intros p o Hp Hne Hnd Hfs. rewrite newfstatat_spec_body. apply after_copyins_det.
intros o'. rewrite newfstatat_core, Hp.
replace (path_eqb p []) with false by (destruct p; [congruence|reflexivity]).
rewrite Hdir, bv_eqb_refl. cbn [negb].
replace (path_eqb p dot_path) with false
by (destruct (path_eqb p dot_path) eqn:E; [apply path_eqb_eq in E; congruence|reflexivity]).
rewrite Hfs. apply err_ret_outcome.
Qed.

#[using="Hfl Hdir"] Lemma newfstatat_present_unmodeled : forall p d o,
read_cstr (in_mem i) pathp = CstrOk p -> p <> [] -> p <> dot_path ->
fs_lookup (m_fs m) p = Some d ->
newfstatat_spec dirfd pathp flags i m o <-> o = Unmodeled.
Proof.
intros p d o Hp Hne Hnd Hfs. rewrite newfstatat_spec_body.
assert (Hb : forall o', newfstatat_core_spec dirfd pathp flags i m o' <-> o' = Unmodeled).
{ intros o'. rewrite newfstatat_core, Hp.
replace (path_eqb p []) with false by (destruct p; [congruence|reflexivity]).
rewrite Hdir, bv_eqb_refl. cbn [negb].
replace (path_eqb p dot_path) with false
by (destruct (path_eqb p dot_path) eqn:E; [apply path_eqb_eq in E; congruence|reflexivity]).
rewrite Hfs. unfold unmodeled. reflexivity. }
unfold after_copyins. destruct o as [eff m' evs|].
- split; [intros (core & Hc & _); apply Hb in Hc; discriminate Hc | intros H; discriminate H].
- split; [reflexivity | intros _; apply Hb; reflexivity].
Qed.
End Newfstatat.

Definition clock_rt_out (tp : word) (m : Model) (o : outcome SyscallEffect) : Prop :=
exists bs, realtime_ok_b bs = true /\ o = Ok (mkEffect (Z_to_bv 64 0) [(tp, bs)] []) m [].

Lemma clock_gettime_realtime_outcome : forall clkid tp i m o w,
clockid_percall_b clkid = true ->
read_bytes_map (in_wmem i) tp (Z_to_bv 64 16) = Some w ->
clock_gettime_spec clkid tp i m o <-> clock_rt_out tp m o.
Proof.
intros clkid tp i m o w Hid Hw. unfold clock_gettime_spec. rewrite Hid.
rewrite bind_input, Hw. unfold clock_rt_out. sys_unfold.
split.
- destruct o as [x m' evs|]; intros H; inv_sys. eexists; split; [eassumption|reflexivity].
- intros (bs & Hbs & ->). eexists _, _, _, _. split; [exists bs; split; [exact Hbs|reflexivity]|].
split; reflexivity.
Qed.

Lemma realtime_ok_zeros : realtime_ok_b (repeat (Z_to_bv 8 0) 16) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma clockid32_realtime : forall w : word,
bv_unsigned w = 0%Z -> clockid_percall_b (clockid32 w) = true.
Proof.
intros w Hw. unfold clockid_percall_b, clockid32, abi_low32. rewrite Hw.
cbn. reflexivity.
Qed.

Section Mremap.
Variables (old old_size new_size flags : word) (i : SyscallInput) (m : Model).
Hypothesis Hflags : bv_unsigned flags = MREMAP_MAYMOVE.
Hypothesis Hal : (bv_unsigned old mod page_size = 0)%Z.
Hypothesis Hnew : page_align_is0_b new_size = false.
Hypothesis Hold : page_align_is0_b old_size = false.

Let h := m_vmmaps m.
Let old_nZ := page_round_up_Z (bv_unsigned old_size).
Let new_nZ := page_round_up_Z (bv_unsigned new_size).
Let old_n : word := Z_to_bv 64 old_nZ.
Let new_n : word := Z_to_bv 64 new_nZ.

Hypothesis Hsrc : mremap_source_b h old old_n old_nZ = true.
Hypothesis Hunif : mremap_backing_uniform_b m old old_n = true.

#[using="Hflags Hal Hnew Hold h Hsrc Hunif"] Lemma mremap_spec_head : forall o,
mremap_spec old old_size new_size flags i m o <->
(if Z.eqb old_nZ new_nZ then ret_only old
else
alt
(e <- errno_from mremap_errnos ;; err_ret e)
(if (new_nZ <? old_nZ)%Z then
modify (fun _ => mremap_model_next m old old_n old new_n) ;;
pure (mremap_inplace_effect old old_n new_n old_nZ new_nZ)
else
let move :=
dst <- choose (fun dst =>
mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true) ;;
modify (fun _ => mremap_model_next m old old_n dst new_n) ;;
pure (mremap_move_effect old old_n dst old_nZ new_nZ) in
if mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ
then alt
(modify (fun _ => mremap_model_next m old old_n old new_n) ;;
pure (mremap_inplace_effect old old_n new_n old_nZ new_nZ))
move
else move))%sys i m o.
Proof.
intros o. unfold mremap_spec. rewrite Hflags, (proj2 (Z.eqb_eq _ _) Hal), Hnew, Hold, Z.eqb_refl.
cbn [negb Z.eqb].
rewrite (bind_model (fun m0 => _)). cbv beta zeta. fold old_nZ new_nZ. fold old_n new_n. fold h.
rewrite Hsrc, Hunif. cbn [andb negb]. reflexivity.
Qed.

#[using="Hflags Hal Hnew Hold h old_n new_n Hsrc Hunif"] Lemma mremap_same_outcome : forall o,
old_nZ = new_nZ ->
mremap_spec old old_size new_size flags i m o <-> o = Ok (mkEffect old [] []) m [].
Proof.
intros o Heq. rewrite mremap_spec_head. rewrite (proj2 (Z.eqb_eq _ _) Heq).
unfold ret_only, pure. reflexivity.
Qed.

Definition mremap_err_out (o : outcome SyscallEffect) : Prop :=
exists e, In e mremap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) m [].

#[using="Hflags Hal Hnew Hold h Hsrc Hunif"] Lemma mremap_shrink_outcome : forall o,
(new_nZ < old_nZ)%Z ->
mremap_spec old old_size new_size flags i m o <->
mremap_err_out o
\/ o = Ok (mkEffectU old [] [] [(old + new_n, Z_to_bv 64 (old_nZ - new_nZ))] [] [])
(mremap_model_next m old old_n old new_n) [].
Proof.
intros o Hlt. rewrite mremap_spec_head.
replace (Z.eqb old_nZ new_nZ) with false by (symmetry; apply Z.eqb_neq; lia).
rewrite (proj2 (Z.ltb_lt _ _) Hlt). unfold mremap_err_out, mremap_inplace_effect.
rewrite (proj2 (Z.ltb_lt _ _) Hlt). sys_unfold.
split.
- destruct o as [x m' evs|]; intros H; inv_sys.
+ left. eexists; split; [eassumption|reflexivity].
+ right. reflexivity.
- intros [(e & He & ->) | ->].
+ left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
+ right. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
Qed.

Definition mremap_grow_out (o : outcome SyscallEffect) : Prop :=
mremap_err_out o
\/ (mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ = true
/\ o = Ok (mkEffect old [] [(old + old_n, Z_to_bv 64 (new_nZ - old_nZ))])
(mremap_model_next m old old_n old new_n) [])
\/ (exists dst, mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true
/\ o = Ok (mkEffectU dst [] [(dst + old_n, Z_to_bv 64 (new_nZ - old_nZ))] [(old, old_n)]
[mkCopy old dst old_n] [])
(mremap_model_next m old old_n dst new_n) []).

#[using="Hflags Hal Hnew Hold h Hsrc Hunif"] Lemma mremap_grow_outcome : forall o,
(old_nZ < new_nZ)%Z ->
mremap_spec old old_size new_size flags i m o <-> mremap_grow_out o.
Proof.
intros o Hlt. rewrite mremap_spec_head.
replace (Z.eqb old_nZ new_nZ) with false by (symmetry; apply Z.eqb_neq; lia).
replace (new_nZ <? old_nZ)%Z with false by (symmetry; apply Z.ltb_ge; lia).
unfold mremap_grow_out, mremap_err_out, mremap_inplace_effect, mremap_move_effect, mremap_tail.
replace (new_nZ <? old_nZ)%Z with false by (symmetry; apply Z.ltb_ge; lia).
rewrite (proj2 (Z.ltb_lt _ _) Hlt).
destruct (mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ) eqn:Hip; sys_unfold.
- split.
+ destruct o as [x m' evs|]; intros H; inv_sys.
* left. eexists; split; [eassumption|reflexivity].
* right; left. split; reflexivity.
* right; right. eexists; split; [eassumption|reflexivity].
+ intros [(e & He & ->) | [(_ & ->) | (dst & Hd & ->)]].
* left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
* right; left. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
* right; right. eexists _, _, _, _. split; [exists dst; split; [exact Hd|reflexivity]|].
split; [|reflexivity]. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
- split.
+ destruct o as [x m' evs|]; intros H; inv_sys.
* left. eexists; split; [eassumption|reflexivity].
* right; right. eexists; split; [eassumption|reflexivity].
+ intros [(e & He & ->) | [(Hc & _) | (dst & Hd & ->)]]; [| discriminate Hc |].
* left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
* right. eexists _, _, _, _. split; [exists dst; split; [exact Hd|reflexivity]|].
split; [|reflexivity]. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
Qed.
End Mremap.

Lemma ENOMEM_in_mremap_errnos : In ENOMEM mremap_errnos.
Proof. left. reflexivity. Qed.
End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsV0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsV0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Lemma step_lbu_fault : forall segs regs pc mem rom w rd rs (imm : bv 12) (isz : Z),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ1 false rd rs imm, isz) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = None ->
RiscvSemantics.step segs (mkst regs pc mem rom) = MachineFault.
Proof.
intros segs regs pc mem rom w rd rs imm isz Hfetch Hecall Hdecode Hread.
step_pipeline Hfetch Hecall Hdecode.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread.
reflexivity.
Qed.

#[using="Type"] Lemma step_ld_fault : forall segs regs pc mem rom w rd rs (imm : bv 12) (isz : Z),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ8 true rd rs imm, isz) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 8%nat = None ->
RiscvSemantics.step segs (mkst regs pc mem rom) = MachineFault.
Proof.
intros segs regs pc mem rom w rd rs imm isz Hfetch Hecall Hdecode Hread.
step_pipeline Hfetch Hecall Hdecode.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread.
reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma msteps_star_nil : forall ms ms' model,
m_halted model = None ->
m_vm_lazy model = [] ->
msteps segs ms ms' ->
star segs (mkCfg ms model) [] (mkCfg ms' model).
Proof.
intros ms ms' model Hh Hlazy H.
induction H as [ms | ms ms1 ms2 Hsvc Hstep H IH].
- apply star_refl.
- change ([] : list event) with (([] : list event) ++ []).
eapply star_step; [| exact IH].
apply (sstep_instr segs ms model ms1 model); [assumption | assumption |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

#[using="Type"] Lemma msteps_illegal_error : forall ms ms' model,
m_halted model = None ->
m_vm_lazy model = [] ->
msteps segs ms ms' ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
reaches_error segs (mkCfg ms model).
Proof.
intros ms ms' model Hh Hlazy Hm Hsvc Hill.
exists [], (mkCfg ms' model), [].
split; [apply msteps_star_nil; assumption |].
apply sstep_instr_fault; [assumption | assumption |].
rewrite (mi_account_step_no_lazy segs ms' model Hlazy), Hill. reflexivity.
Qed.

End WithSegs.

Section OmniWithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma illegal_exec : forall ms model,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineFault ->
OmniRun.exec segs (mkCfg ms model) (fun tr o => tr = [] /\ o = OError (mkCfg ms model)).
Proof.
intros ms model Hh Hlazy Hsvc Hill.
apply exec_step; [exact Hh | | |].
- exists [], SError. apply sstep_instr_fault; [assumption | assumption |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hill. reflexivity.
- intros evs Hss. inversion Hss; subst; split; reflexivity.
- intros evs c' Hnext. exfalso. inversion Hnext; subst; try congruence.
match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hill in H;
discriminate
end.
Qed.

#[using="Type"] Lemma instr_exec : forall ms ms' model (Q : post),
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
OmniRun.exec segs (mkCfg ms' model) Q ->
OmniRun.exec segs (mkCfg ms model) Q.
Proof.
intros ms ms' model Q Hh Hlazy Hsvc Hstep Hex.
apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
- apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
- intros evs st Hss.
exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
- eapply exec_conseq; [exact Hex |]. intros tr o H. cbn [app]. exact H.
Qed.

#[using="Type"] Lemma msteps_exec : forall ms ms' model (Q : post),
m_halted model = None ->
m_vm_lazy model = [] ->
msteps segs ms ms' ->
OmniRun.exec segs (mkCfg ms' model) Q ->
OmniRun.exec segs (mkCfg ms model) Q.
Proof.
intros ms ms' model Q Hh Hlazy Hm Hex.
induction Hm as [ms0 | ms0 ms1 ms2 Hsvc Hstep Htail IH]; [exact Hex |].
eapply instr_exec; eauto.
Qed.

#[using="Type"] Lemma msteps_illegal_exec : forall ms ms' model,
m_halted model = None ->
m_vm_lazy model = [] ->
msteps segs ms ms' ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
OmniRun.exec segs (mkCfg ms model) (fun tr o => tr = [] /\ o = OError (mkCfg ms' model)).
Proof.
intros ms ms' model Hh Hlazy Hm Hsvc Hill.
eapply msteps_exec; [exact Hh | exact Hlazy | exact Hm |].
apply illegal_exec; assumption.
Qed.

#[using="Type"] Lemma fault_covered_at : forall ms model,
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineFault ->
~ unmodeled_at segs (mkCfg ms model).
Proof.
intros ms model Hlazy Hsvc Hfault (_ & [(_ & Hum) | (x8 & Hsvc' & _)]); cbn in *.
- rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hfault in Hum.
discriminate.
- congruence.
Qed.

#[using="Type"] Lemma msteps_illegal_errors : forall ms ms' model,
m_halted model = None ->
m_vm_lazy model = [] ->
msteps segs ms ms' ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
OmniRun.exec segs (mkCfg ms model) errors.
Proof.
intros ms ms' model Hh Hlazy Hm Hsvc Hill.
eapply exec_conseq; [eapply msteps_illegal_exec; eassumption |].
intros tr o (_ & ->). exact I.
Qed.

#[using="Type"] Lemma msteps_illegal_covered : forall ms ms' model,
m_halted model = None ->
m_vm_lazy model = [] ->
msteps segs ms ms' ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
OmniRun.coexec segs (mkCfg ms model) (covered segs).
Proof.
intros ms ms' model Hh Hlazy Hm Hsvc Hill.
apply exec_coexec.
eapply exec_conseq; [eapply msteps_illegal_exec; eassumption |].
intros tr o (_ & ->). unfold covered. apply fault_covered_at; assumption.
Qed.

#[using="Type"] Lemma msteps_illegal_no_exit : forall ms ms' model,
m_halted model = None ->
m_vm_lazy model = [] ->
msteps segs ms ms' ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
forall code, ~ OmniRun.exec segs (mkCfg ms model) (exits_with code).
Proof.
intros ms ms' model Hh Hlazy Hm Hsvc Hill code Hex.
destruct (exec_realizes _ _ _ (msteps_illegal_exec _ _ _ Hh Hlazy Hm Hsvc Hill))
as (tr & o & Hm' & _ & ->).
exact (exec_sound _ _ _ Hex _ _ Hm').
Qed.

#[using="Type"] Lemma msteps_illegal_not_never_errors : forall ms ms' model,
m_halted model = None ->
m_vm_lazy model = [] ->
msteps segs ms ms' ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
~ OmniRun.coexec segs (mkCfg ms model) never_errors.
Proof.
intros ms ms' model Hh Hlazy Hm Hsvc Hill Hco.
destruct (exec_realizes _ _ _ (msteps_illegal_exec _ _ _ Hh Hlazy Hm Hsvc Hill))
as (tr & o & Hm' & _ & ->).
exact (coexec_sound _ _ _ _ Hm' _ Hco I).
Qed.

End OmniWithSegs.

Section AllErrorWithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma illegal_all_traces_error : forall ms model,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineFault ->
all_traces_error segs (mkCfg ms model).
Proof.
intros ms model Hh Hlazy Hsvc Hill.
constructor.
- exists [], SError. apply sstep_instr_fault; [assumption | assumption |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hill. reflexivity.
- intros evs c' Hnext. inversion Hnext; subst; try congruence.
match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hill in H;
discriminate
end.
Qed.

#[using="Type"] Lemma instr_all_traces_error : forall ms ms' model,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
all_traces_error segs (mkCfg ms' model) ->
all_traces_error segs (mkCfg ms model).
Proof.
intros ms ms' model Hh Hlazy Hsvc Hstep Hall.
constructor.
- exists [], (SNext (mkCfg ms' model)).
apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
- intros evs c' Hnext.
destruct (sstep_instr_inv segs ms model ms' evs (SNext c')
Hlazy Hsvc Hstep Hnext) as [_ Hto].
inversion Hto; subst. exact Hall.
Qed.

#[using="Type"] Lemma msteps_all_traces_error : forall ms ms' model,
m_halted model = None ->
m_vm_lazy model = [] ->
msteps segs ms ms' ->
all_traces_error segs (mkCfg ms' model) ->
all_traces_error segs (mkCfg ms model).
Proof.
intros ms ms' model Hh Hlazy Hm Hall.
induction Hm as [ms0 | ms0 ms1 ms2 Hsvc Hstep Htail IH].
- exact Hall.
- eapply instr_all_traces_error; eauto.
Qed.

#[using="Type"] Lemma msteps_illegal_all_traces_error : forall ms ms' model,
m_halted model = None ->
m_vm_lazy model = [] ->
msteps segs ms ms' ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
all_traces_error segs (mkCfg ms model).
Proof.
intros ms ms' model Hh Hlazy Hm Hfinal_svc Hillegal.
apply all_traces_error_iff. eapply msteps_illegal_errors; eassumption.
Qed.

End AllErrorWithSegs.

Section NoUnmodeledWithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma star_stuck_refl : forall c tr c',
(forall evs c2, ~ sstep segs c evs (SNext c2)) ->
star segs c tr c' -> c' = c.
Proof.
intros c tr c' Hno Hstar. inversion Hstar; subst; [reflexivity|].
exfalso. eapply Hno; eassumption.
Qed.

#[using="Type"] Lemma fault_no_unmodeled : forall ms model,
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineFault ->
~ reaches_unmodeled segs (mkCfg ms model).
Proof.
intros ms model Hlazy Hsvc Hfault (tr & c & Hstar & Hun).
assert (Hno : forall evs c2, ~ sstep segs (mkCfg ms model) evs (SNext c2)).
{ intros evs c2 Hss. inversion Hss; subst; try congruence.
match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hfault in H;
discriminate
end. }
rewrite (star_stuck_refl _ tr c Hno Hstar) in Hun.
destruct Hun as (_ & [(_ & Hum) | (x8 & Hsvc' & _)]); cbn in *.
- rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hfault in Hum.
discriminate.
- congruence.
Qed.

#[using="Type"] Lemma instr_no_unmodeled : forall ms ms' model,
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
~ reaches_unmodeled segs (mkCfg ms' model) ->
~ reaches_unmodeled segs (mkCfg ms model).
Proof.
intros ms ms' model Hlazy Hsvc Hstep Hnext (tr & c & Hstar & Hun).
inversion Hstar as [| c1 evs c2 tr2 c3 Hss Hrest]; subst.
- destruct Hun as (_ & [(_ & Hum) | (x8 & Hsvc' & _)]); cbn in *.
+ rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep in Hum.
discriminate.
+ congruence.
- destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
Hlazy Hsvc Hstep Hss)
as [_ Hc2].
inversion Hc2; subst. apply Hnext. exists tr2, c. split; assumption.
Qed.

#[using="Type"] Lemma msteps_fault_no_unmodeled : forall ms ms' model,
msteps segs ms ms' ->
m_vm_lazy model = [] ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
~ reaches_unmodeled segs (mkCfg ms model).
Proof.
intros ms ms' model Hm Hlazy Hsvc Hfault.
destruct (m_halted model) as [code |] eqn:Hh.
-
intros (tr & c & Hstar & Hun).
inversion Hstar as [| c1 evs c2 tr2 c3 Hss]; subst.
+ destruct Hun as (Hun & _). cbn in Hun. congruence.
+ pose proof (sstep_from_running segs _ _ _ Hss) as Hrun. cbn in Hrun. congruence.
- apply coexec_covered. eapply msteps_illegal_covered; eassumption.
Qed.

End NoUnmodeledWithSegs.

#[using="Type"] Lemma err_escape_omni_run :
forall segs pc ph sp brk0 mb rnd lim inp ms',
msteps segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ms' ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp errors.
Proof.
intros segs pc ph sp brk0 mb rnd lim inp ms' Hm Hsvc Hill.
cbn [omni_run]. unfold init_config.
eapply msteps_illegal_errors; [reflexivity | reflexivity | exact Hm | exact Hsvc | exact Hill].
Qed.

#[using="Type"] Lemma err_escape_omni_covered :
forall segs pc ph sp brk0 mb rnd lim inp ms',
msteps segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ms' ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
omni_corun (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (covered segs).
Proof.
intros segs pc ph sp brk0 mb rnd lim inp ms' Hm Hsvc Hill.
cbn [omni_corun]. unfold init_config.
eapply msteps_illegal_covered; [reflexivity | reflexivity | exact Hm | exact Hsvc | exact Hill].
Qed.

#[using="Type"] Lemma err_escape_omni_equiv :
forall segs pc ph sp brk0 mb rnd lim inp T limT et ms',
msteps segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ms' ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
omni_equiv (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) T limT et inp.
Proof.
intros segs pc ph sp brk0 mb rnd lim inp T limT et ms' Hm Hsvc Hill.
left. eapply err_escape_omni_run; eassumption.
Qed.

#[using="Type"] Lemma err_escape_omni_strong_equiv :
forall segs pc ph sp brk0 mb rnd inp T et ms',
msteps segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ms' ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
omni_strong_equiv (mkImage segs pc ph) T (mkEntry sp brk0 mb rnd) et inp.
Proof.
intros segs pc ph sp brk0 mb rnd inp T et ms' Hm Hsvc Hill.
split.
- cbn [img_segments]. eapply err_escape_omni_covered; eassumption.
- eapply err_escape_omni_equiv; eassumption.
Qed.

#[using="Type"] Lemma err_escape_equiv :
forall segs pc ph sp brk0 mb rnd lim inp (target : behavior) ms',
msteps segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ms' ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
Equivalence.equiv (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) target.
Proof.
intros segs pc ph sp brk0 mb rnd lim inp target ms' Hm Hsvc Hill.
left. apply bh_all_errors_iff. eapply err_escape_omni_run; eassumption.
Qed.

#[using="Type"] Lemma err_escape_modeled :
forall segs pc ph sp brk0 mb rnd lim inp ms',
msteps segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ms' ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
Equivalence.modeled (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
intros segs pc ph sp brk0 mb rnd lim inp ms' Hm Hsvc Hill.
apply modeled_iff. cbn [img_segments]. eapply err_escape_omni_covered; eassumption.
Qed.

#[using="Type"] Lemma err_escape_strong_equiv :
forall segs pc ph sp brk0 mb rnd lim inp (target : behavior) ms',
msteps segs (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ms' ->
ms_svc_pending ms' = None ->
RiscvSemantics.step segs ms' = MachineFault ->
Equivalence.modeled (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp)
/\ Equivalence.equiv (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp)
target.
Proof.
intros segs pc ph sp brk0 mb rnd lim inp target ms' Hm Hsvc Hill.
split; [eapply err_escape_modeled | eapply err_escape_equiv]; eassumption.
Qed.
End FPGEN1.
