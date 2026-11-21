(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up stack layout is restated for the revision's entry block, over the run's ProcInput with valid_launch and entry_launch_ok_va: strings anchored at the entry draw's top with the execfn string, the AT_RANDOM bytes below them, 27 or 29 auxv pairs by the CONFIG_RSEQ flag, datoms for GID, AT_SYSINFO_EHDR, AT_EXECFN, AT_MINSIGSTKSZ and the eight cache words, and the zero window down to stack_window_depth; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK14 YK1a YK1b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0b YQ0i.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Lemma nth_error_app_off : forall {A} (l1 l2 : list A) j,
nth_error (l1 ++ l2) (length l1 + j) = nth_error l2 j.
Proof. intros A l1 l2 j. rewrite nth_error_app2 by lia. f_equal. lia. Qed.
Lemma nth_error_flat_map_le8 : forall (l : list word) k i,
(k < length l)%nat -> (i < 8)%nat ->
nth_error (flat_map word_le8 l) (8 * k + i) = nth_error (word_le8 (nth k l (Z_to_bv 64 0))) i.
Proof.
induction l as [|w l IH]; intros k i Hk Hi; [cbn in Hk; lia|].
cbn [flat_map nth]. destruct k as [|k].
- rewrite nth_error_app1 by (rewrite length_n_to_le_8; lia). f_equal; lia.
- replace (8 * S k + i)%nat with (length (word_le8 w) + (8 * k + i))%nat
by (rewrite length_n_to_le_8; lia).
rewrite nth_error_app_off. apply IH; [cbn in Hk; lia| exact Hi].
Qed.
Lemma nth_error_flatten_strings : forall (l : list (list byte)) k j,
(k < length l)%nat -> (j <= length (nth k l []))%nat ->
nth_error (flatten_strings l) (total_arg_bytes_nat (firstn k l) + j)
= nth_error (nth k l [] ++ [Z_to_bv 8 0]) j.
Proof.
induction l as [|s l IH]; intros k j Hk Hj; [cbn in Hk; lia|].
cbn [flatten_strings flat_map nth firstn] in *. fold (flatten_strings l).
destruct k as [|k].
- change (total_arg_bytes_nat []) with 0%nat. rewrite Nat.add_0_l.
cbn [nth] in Hj. apply nth_error_app1. rewrite length_app. cbn [length]. lia.
- cbn [firstn]. rewrite total_arg_bytes_cons.
replace (length s + 1 + total_arg_bytes_nat (firstn k l) + j)%nat
with (length (s ++ [Z_to_bv 8 0]) + (total_arg_bytes_nat (firstn k l) + j))%nat
by (rewrite length_app; cbn [length]; lia).
rewrite nth_error_app_off. apply IH; [cbn in Hk; lia| exact Hj].
Qed.
Lemma word_le8_nth : forall (w : word) i, (i < 8)%nat ->
nth_error (word_le8 w) i = Some (byte_of_word w (Z.of_nat i)).
Proof.
intros w i Hi.
destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try reflexivity. lia.
Qed.
Lemma word_le8_st_bytes : forall w : word, word_le8 w = st_bytes 8 w.
Proof. intros w. reflexivity. Qed.
Fixpoint auxv_words (l : list (word * word)) : list word :=
match l with [] => [] | (k, v) :: r => k :: v :: auxv_words r end.
Lemma build_auxv_words : forall l, build_auxv l = flat_map word_le8 (auxv_words l).
Proof.
induction l as [|[k v] l IH]; [reflexivity|].
cbn [build_auxv auxv_words flat_map fst snd]. fold (build_auxv l). rewrite IH, app_assoc. reflexivity.
Qed.
Lemma length_auxv_words : forall l, length (auxv_words l) = (2 * length l)%nat.
Proof. induction l as [|[k v] l IH]; [reflexivity|]. cbn [auxv_words length]. rewrite IH. lia. Qed.
(* 08b1429: the entry block runs from sp to ed_top (StackLayout.build_stack_bytes): argc, argv[], envp[], the auxv
   (27 pairs, or 29 under CONFIG_RSEQ), a 0/8-byte gap, the 16 AT_RANDOM bytes, the arch_align_stack pad, then the
   argv/envp strings, the exec file name and the 8-byte slot below ed_top. The old raw_len/pad_len/rand_off layout is gone. *)
Lemma pad_aligns : forall n : Z, 0 <= n -> (n + (8 - n mod 8) mod 8) mod 8 = 0.
Proof.
intros n Hn.
pose proof (Z.div_mod n 8 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Hr.
set (r := n mod 8) in *. set (q := n / 8) in *.
destruct (Z.eq_dec r 0) as [Hr0|Hr0].
- rewrite Hr0. change ((8 - 0) mod 8) with 0. rewrite Z.add_0_r. subst r. exact Hr0.
- rewrite (Z.mod_small (8 - r) 8) by lia.
replace (n + (8 - r)) with ((q + 1) * 8) by lia. apply Z_mod_mult.
Qed.
Section g.
Variables (la : LaunchAuxv) (ph : PhdrInfo) (entry sp top : word).
Variables (av ev : list (list byte)) (xf : list byte) (uid gid hw : word) (rnd : EntryDraw).
Lemma bsb_decomp :
build_stack_bytes la ph entry sp top av ev xf uid gid hw rnd =
word_le8 (len_word av)
++ flat_map word_le8 (fst (string_addrs (string_base_addr top av ev xf) av))
++ word_le8 (Z_to_bv 64 0)
++ flat_map word_le8 (fst (string_addrs (string_base_addr top av ev xf + nat_to_word (total_arg_bytes_nat av)) ev))
++ word_le8 (Z_to_bv 64 0)
++ auxv_bytes la ph entry uid gid hw (at_random_ptr sp (la_rseq la) av ev) (at_execfn_ptr top xf)
++ repeat (Z_to_bv 8 0) (8 * (block_items av ev mod 2))
++ at_random_bytes (ed_random rnd)
++ repeat (Z_to_bv 8 0) (block_pad_len (la_rseq la) sp top av ev xf)
++ flatten_strings av ++ flatten_strings ev ++ xf ++ [Z_to_bv 8 0] ++ repeat (Z_to_bv 8 0) 8.
Proof.
unfold build_stack_bytes. cbv zeta.
rewrite (string_addrs_pair av). cbv beta iota.
rewrite (string_addrs_pair ev). cbv beta iota.
rewrite <- !app_assoc. reflexivity.
Qed.
End g.
Definition bytes_at (m : word -> option byte) (a : Z) (bs : list byte) : Prop :=
forall j, (j < length bs)%nat -> m (Z_to_bv 64 (a + Z.of_nat j)) = nth_error bs j.
Lemma bytes_at_app_inv : forall m a l1 l2,
bytes_at m a (l1 ++ l2) -> bytes_at m a l1 /\ bytes_at m (a + Z.of_nat (length l1)) l2.
Proof.
intros m a l1 l2 H. split; intros j Hj.
- rewrite <- (nth_error_app1 l1 l2 Hj). apply H. rewrite length_app. lia.
- rewrite <- (nth_error_app_off l1 l2 j).
replace (a + Z.of_nat (length l1) + Z.of_nat j) with (a + Z.of_nat (length l1 + j)) by lia.
apply H. rewrite length_app. lia.
Qed.
Lemma bytes_at_app_l : forall m a l1 l2, bytes_at m a (l1 ++ l2) -> bytes_at m a l1.
Proof. intros m a l1 l2 H. apply (bytes_at_app_inv m a l1 l2 H). Qed.
Lemma bytes_at_app_r : forall m a l1 l2,
bytes_at m a (l1 ++ l2) -> bytes_at m (a + Z.of_nat (length l1)) l2.
Proof. intros m a l1 l2 H. apply (bytes_at_app_inv m a l1 l2 H). Qed.
Lemma bytes_at_le8_nth : forall m a (l : list word) k,
bytes_at m a (flat_map word_le8 l) -> (k < length l)%nat ->
bytes_at m (a + 8 * Z.of_nat k) (word_le8 (nth k l (Z_to_bv 64 0))).
Proof.
intros m a l k H Hk j Hj. rewrite length_n_to_le_8 in Hj.
rewrite <- (nth_error_flat_map_le8 l k j Hk Hj).
replace (a + 8 * Z.of_nat k + Z.of_nat j) with (a + Z.of_nat (8 * k + j)) by lia.
apply H. rewrite length_flat_map_le8. lia.
Qed.
Lemma tab_firstn_S : forall (l : list (list byte)) k, (k < length l)%nat ->
(total_arg_bytes_nat (firstn (S k) l) = total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1)%nat.
Proof.
induction l as [|s l IH]; intros k Hk; [cbn in Hk; lia|].
destruct k as [|k].
- cbn [firstn nth]. rewrite total_arg_bytes_cons, firstn_O. change (total_arg_bytes_nat []) with 0%nat. lia.
- cbn [firstn nth]. rewrite !total_arg_bytes_cons. rewrite IH by (cbn in Hk; lia). lia.
Qed.
Lemma tab_firstn_nth_le : forall (l : list (list byte)) k, (k < length l)%nat ->
(total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1 <= total_arg_bytes_nat l)%nat.
Proof.
intros l k Hk. rewrite <- tab_firstn_S by exact Hk. apply total_arg_bytes_firstn_le.
Qed.
Lemma bytes_at_strings_nth : forall m a (l : list (list byte)) k,
bytes_at m a (flatten_strings l) -> (k < length l)%nat ->
bytes_at m (a + Z.of_nat (total_arg_bytes_nat (firstn k l))) (nth k l [] ++ [Z_to_bv 8 0]).
Proof.
intros m a l k H Hk j Hj. rewrite length_app in Hj. cbn [length] in Hj.
rewrite <- (nth_error_flatten_strings l k j Hk ltac:(lia)).
replace (a + Z.of_nat (total_arg_bytes_nat (firstn k l)) + Z.of_nat j)
with (a + Z.of_nat (total_arg_bytes_nat (firstn k l) + j)) by lia.
apply H. rewrite length_flatten_strings. pose proof (tab_firstn_nth_le l k Hk). lia.
Qed.
Lemma bytes_at_frame : forall m m' a bs,
(forall x : word, a <= bv_unsigned x < a + Z.of_nat (length bs) -> m' x = m x) ->
0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
bytes_at m a bs -> bytes_at m' a bs.
Proof.
intros m m' a bs Hfr Ha Hnw H j Hj. rewrite Hfr; [apply H; exact Hj|].
rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?x) with (x mod 2^64). rewrite Z.mod_small by lia. lia.
Qed.
Lemma bytes_at_rdn : forall segs m a bs,
bytes_at m a bs -> rdn segs m (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
intros segs m a bs H. apply (proj2 (rdn_mbytes segs m (length bs) a bs)).
split; [reflexivity|]. intros i Hi. unfold mbyte. rewrite (H i Hi).
destruct (nth_error bs i) eqn:Hn; [reflexivity|].
exfalso. apply nth_error_None in Hn. lia.
Qed.
Lemma bytes_at_mbyte : forall segs m a bs j,
bytes_at m a bs -> (j < length bs)%nat ->
mbyte segs m (a + Z.of_nat j) = nth_error bs j.
Proof.
intros segs m a bs j H Hj. unfold mbyte. rewrite (H j Hj).
destruct (nth_error bs j) eqn:Hn; [reflexivity|].
exfalso. apply nth_error_None in Hn. lia.
Qed.
Lemma regions_wf_app : forall l1 l2, regions_wf (l1 ++ l2) = regions_wf l1 && regions_wf l2.
Proof. induction l1 as [|r l1 IH]; intros l2; cbn; [reflexivity|]. rewrite IH, andb_assoc. reflexivity. Qed.
Lemma pairwise_disjoint_app : forall (En : env) l1 l2,
pairwise_disjoint En l1 -> pairwise_disjoint En l2 ->
(forall r1 r2, In r1 l1 -> In r2 l2 -> extent_disjoint En r1 r2) ->
pairwise_disjoint En (l1 ++ l2).
Proof.
intros En l1; induction l1 as [|r l1 IH]; intros l2 H1 H2 H12; cbn; [exact H2|].
destruct H1 as [Ha H1]. split.
- clear IH H1. induction l1 as [|r' l1 IH']; cbn in *.
+ clear Ha. induction l2 as [|r2 l2 IH2]; cbn; [exact I|]. split.
* apply H12; [left; reflexivity| left; reflexivity].
* apply IH2; [destruct H2; assumption|]. intros r1 r0 Hr1 Hr0. apply H12; [exact Hr1| right; exact Hr0].
+ destruct Ha as [Hrr' Ha]. split; [exact Hrr'|]. apply IH'; [exact Ha|].
intros r1 r2 Hr1 Hr2. apply H12; [destruct Hr1; [left|right;right]; assumption| exact Hr2].
- apply IH; [exact H1| exact H2|]. intros r1 r2 Hr1 Hr2. apply H12; [right; exact Hr1| exact Hr2].
Qed.
Lemma tget_empty : forall (A : Type) (p : positive), tget p (@TEmpty A) = None.
Proof. intros A p. destruct p; reflexivity. Qed.
Lemma mod8_of_mod16 : forall z k, z mod 16 = 0 -> (z + 8 * k) mod 8 = 0.
Proof.
intros z k Hz.
pose proof (Z.div_mod z 16 ltac:(lia)) as Hdm. rewrite Hz, Z.add_0_r in Hdm.
rewrite Hdm. replace (16 * (z / 16) + 8 * k) with ((2 * (z / 16) + k) * 8) by lia. apply Z_mod_mult.
Qed.
Definition z_envp (zsp : Z) (av : list (list byte)) : Z := zsp + 16 + 8 * Z.of_nat (length av).
Definition z_auxv (zsp : Z) (av ev : list (list byte)) : Z :=
z_envp zsp av + 8 * Z.of_nat (length ev) + 8.
(* 08b1429: the strings sit at the TOP of the block, below the 8-byte slot under ed_top (StackLayout.string_base_addr) *)
Definition z_strs (ztop : Z) (av ev : list (list byte)) (xf : list byte) : Z :=
ztop - 8 - Z.of_nat (launch_string_bytes av ev xf).
Definition z_argv (ztop : Z) (av ev : list (list byte)) (xf : list byte) (k : nat) : Z :=
z_strs ztop av ev xf + Z.of_nat (total_arg_bytes_nat (firstn k av)).
Definition z_envs (ztop : Z) (av ev : list (list byte)) (xf : list byte) (k : nat) : Z :=
z_strs ztop av ev xf + Z.of_nat (total_arg_bytes_nat av) + Z.of_nat (total_arg_bytes_nat (firstn k ev)).
Definition z_xfn (ztop : Z) (av ev : list (list byte)) (xf : list byte) : Z :=
z_strs ztop av ev xf + Z.of_nat (total_arg_bytes_nat av) + Z.of_nat (total_arg_bytes_nat ev).
(* the AT_RANDOM bytes: C - 16 above sp (StackLayout.at_random_ptr) *)
Definition z_rand (zsp : Z) (rs : bool) (av ev : list (list byte)) : Z :=
zsp + Z.of_nat (block_head_size rs av ev) - 16.
Definition NUL : byte := Z_to_bv 8 0.
Definition E0 (sp top : word) (rs : bool) (av ev : list (list byte)) (xf : list byte)
(xw : nat -> word) (xd : nat -> list byte) : env :=
let zsp := bv_unsigned sp in
let zt := bv_unsigned top in
mkEnv (fun n => match n with
| 0 => sp
| 1 => Z_to_bv 64 (z_argv zt av ev xf 0)
| 2 => Z_to_bv 64 (z_argv zt av ev xf 1)
| 3 => Z_to_bv 64 (Z.of_nat (length av))
| 4 => Z_to_bv 64 (z_envp zsp av)
| 5 => Z_to_bv 64 (z_auxv zsp av ev)
| 6 => Z_to_bv 64 (z_rand zsp rs av ev)
| _ => xw n
end)%nat
(fun d => match d with
| 0 => nth 0 av [] ++ [NUL]
| 1 => nth 1 av [] ++ [NUL]
| _ => xd d
end)%nat.
Definition UID_DATOM : nat := 4%nat.
Definition uid_bytes (uid : word) : list byte := word_le8 uid.
Definition HWCAP_DATOM : nat := 6%nat.
Definition hwcap_bytes (hw : word) : list byte := word_le8 hw.
Definition RAND_DATOM : nat := 7%nat.
Definition rand_bytes (rnd : EntryDraw) : list byte := at_random_bytes (ed_random rnd).
Lemma length_rand_bytes : forall rnd, length (rand_bytes rnd) = 16%nat.
Proof. intros rnd. reflexivity. Qed.
Lemma length_hwcap_bytes : forall hw, length (hwcap_bytes hw) = 8%nat.
Proof. intros hw. reflexivity. Qed.
Lemma length_uid_bytes : forall uid, length (uid_bytes uid) = 8%nat.
Proof. intros uid. reflexivity. Qed.
(* 08b1429: the auxv values the start-up copies into aux[] that are not literals of the image *)
Definition GID_DATOM : nat := 8%nat.
Definition SYSI_DATOM : nat := 9%nat.
Definition XFN_DATOM : nat := 10%nat.
Definition CW_DATOM (i : nat) : nat := (11 + i)%nat.
Definition MSS_DATOM : nat := 19%nat.
Definition cache_list (c : CacheWords) : list word :=
[cw_l1i_size c; cw_l1i_geom c; cw_l1d_size c; cw_l1d_geom c; cw_l2_size c; cw_l2_geom c; cw_l3_size c; cw_l3_geom c].
(* StackLayout.auxv_entries, pair by pair; the CONFIG_RSEQ pair only when rs (27 or 29 pairs, auxv_size rs bytes) *)
Definition auxv_chunks (ph : PhdrInfo) (ent : Z) (rs : bool) : list chunk :=
[ mkChunk 0 (CVal 8 (SLit 33));   mkChunk 8 (CData SYSI_DATOM 0 8);
mkChunk 16 (CVal 8 (SLit 40));  mkChunk 24 (CData 11 0 8);
mkChunk 32 (CVal 8 (SLit 41));  mkChunk 40 (CData 12 0 8);
mkChunk 48 (CVal 8 (SLit 42));  mkChunk 56 (CData 13 0 8);
mkChunk 64 (CVal 8 (SLit 43));  mkChunk 72 (CData 14 0 8);
mkChunk 80 (CVal 8 (SLit 44));  mkChunk 88 (CData 15 0 8);
mkChunk 96 (CVal 8 (SLit 45));  mkChunk 104 (CData 16 0 8);
mkChunk 112 (CVal 8 (SLit 46)); mkChunk 120 (CData 17 0 8);
mkChunk 128 (CVal 8 (SLit 47)); mkChunk 136 (CData 18 0 8);
mkChunk 144 (CVal 8 (SLit 51)); mkChunk 152 (CData MSS_DATOM 0 8);
mkChunk 160 (CVal 8 (SLit 16)); mkChunk 168 (CData HWCAP_DATOM 0 8);
mkChunk 176 (CVal 8 (SLit 6));  mkChunk 184 (CVal 8 (SLit 4096));
mkChunk 192 (CVal 8 (SLit 17)); mkChunk 200 (CVal 8 (SLit 100));
mkChunk 208 (CVal 8 (SLit 3));  mkChunk 216 (CVal 8 (SLit (Z.of_N (ph_addr ph))));
mkChunk 224 (CVal 8 (SLit 4));  mkChunk 232 (CVal 8 (SLit (Z.of_N (ph_ent ph))));
mkChunk 240 (CVal 8 (SLit 5));  mkChunk 248 (CVal 8 (SLit (Z.of_N (ph_num ph))));
mkChunk 256 (CVal 8 (SLit 7));  mkChunk 264 (CVal 8 (SLit 0));
mkChunk 272 (CVal 8 (SLit 8));  mkChunk 280 (CVal 8 (SLit 0));
mkChunk 288 (CVal 8 (SLit 9));  mkChunk 296 (CVal 8 (SLit ent));
mkChunk 304 (CVal 8 (SLit 11)); mkChunk 312 (CData UID_DATOM 0 8);
mkChunk 320 (CVal 8 (SLit 12)); mkChunk 328 (CData UID_DATOM 0 8);
mkChunk 336 (CVal 8 (SLit 13)); mkChunk 344 (CData GID_DATOM 0 8);
mkChunk 352 (CVal 8 (SLit 14)); mkChunk 360 (CData GID_DATOM 0 8);
mkChunk 368 (CVal 8 (SLit 23)); mkChunk 376 (CVal 8 (SLit 0));
mkChunk 384 (CVal 8 (SLit 25)); mkChunk 392 (CVal 8 (SOff 6 0));
mkChunk 400 (CVal 8 (SLit 31)); mkChunk 408 (CData XFN_DATOM 0 8) ]
++ (if rs then [ mkChunk 416 (CVal 8 (SLit 27)); mkChunk 424 (CVal 8 (SLit 28));
mkChunk 432 (CVal 8 (SLit 28)); mkChunk 440 (CVal 8 (SLit 32)) ] else [])
++ [ mkChunk (if rs then 448 else 416) (CVal 8 (SLit 0)); mkChunk (if rs then 456 else 424) (CVal 8 (SLit 0)) ].
Definition R_free (W : Z) : region :=
mkRegion (Some 0%nat) (-W) 0 (-W) 0 [mkChunk (-W) (CZero W)].
Definition R_hdr (two : bool) : region :=
mkRegion (Some 0%nat) 0 (if two then 24 else 16) 0 0
(mkChunk 0 (CVal 8 (SOff 3 0)) :: mkChunk 8 (CVal 8 (SOff 1 0))
:: if two then [mkChunk 16 (CVal 8 (SOff 2 0))] else []).
Definition R_argvnull : region := mkRegion (Some 4%nat) (-8) 0 0 0 [mkChunk (-8) (CVal 8 (SLit 0))].
Definition R_envnull : region := mkRegion (Some 5%nat) (-8) 0 0 0 [mkChunk (-8) (CVal 8 (SLit 0))].
Definition R_auxv (ph : PhdrInfo) (ent : Z) (rs : bool) : region :=
mkRegion (Some 5%nat) 0 (Z.of_nat (auxv_size rs)) 0 0 (auxv_chunks ph ent rs).
Definition R_rand : region := mkRegion (Some 6%nat) 0 16 0 0 [mkChunk 0 (CData RAND_DATOM 0 16)].
Definition R_argv0 : region := mkRegion (Some 1%nat) 0 1 0 0 [mkChunk 0 (CData 0 0 1)].
Definition R_argv1 : region := mkRegion (Some 2%nat) 0 1 0 0 [mkChunk 0 (CData 1 0 1)].
Definition stack_regions (ph : PhdrInfo) (ent W : Z) (two rs : bool) : smem :=
R_free W :: R_hdr two :: R_argvnull :: R_envnull :: R_auxv ph ent rs :: R_rand :: R_argv0
:: (if two then [R_argv1] else []).
Definition K_stack : Z := 4194304.
Definition SP_LO : Z := 0x7fff80000000.
Definition SP_HI : Z := 0x800000000000.
Definition ptr_fact (al : Z) : afact := mkAF SP_LO (SP_HI - 16) al.
(* 08b1429: argv[0] now sits at ed_top - 8 - L, which is not 8-aligned *)
Definition G0 (two : bool) : facts :=
mkFacts [ (0%nat, mkAF SP_LO SP_HI 4);
(1%nat, mkAF SP_LO SP_HI 0);
(2%nat, mkAF SP_LO SP_HI 0);
(3%nat, mkAF (if two then 2 else 1) 1024 0);
(4%nat, ptr_fact 3);
(5%nat, ptr_fact 3);
(6%nat, ptr_fact 3) ] [] [].
Definition regs0 : list sv := [SLit 0; SLit 0; SOff 0 0].
Definition ss0 (pc : Z) (ph : PhdrInfo) (W : Z) (two rs : bool) (img : smem) : sstate :=
mkSS pc regs0 (stack_regions ph pc W two rs ++ img) None (G0 two).
Fixpoint zallb (f : Z -> bool) (a : Z) (n : nat) : bool :=
match n with O => true | S n' => f a && zallb f (a + 1) n' end.
Lemma zallb_sound : forall f n a x, zallb f a n = true -> a <= x < a + Z.of_nat n -> f x = true.
Proof.
induction n as [|n IH]; intros a x H Hx; [lia|].
cbn [zallb] in H. apply andb_prop in H as [H1 H2].
destruct (Z.eq_dec x a) as [->|Hne]; [exact H1|].
apply (IH (a + 1)); [exact H2| lia].
Qed.
Definition img_limit : Z := SP_LO - 8388608.
Definition img_byte_ok (segs : list Segment) (a : Z) : bool :=
match img_byte segs a with Some _ => true | None => false end.
Definition img_zero_ok (segs : list Segment) (a : Z) : bool :=
match img_byte segs a with Some b => bv_eqb b (Z_to_bv 8 0) | None => false end.
Definition img_writable_ok (segs : list Segment) (a : Z) : bool :=
match wview segs (fun _ => None) (Z_to_bv 64 a) with Some _ => true | None => false end.
Definition img_chunk_ok (segs : list Segment) (c : chunk) : bool :=
match c_val c with
| CImg len => zallb (img_byte_ok segs) (c_off c) (Z.to_nat len)
| CZero len => zallb (img_zero_ok segs) (c_off c) (Z.to_nat len)
| _ => false
end.
Definition img_region_ok (segs : list Segment) (r : region) : bool :=
match r_base r with
| Some _ => false
| None => (0 <=? r_lo r) && (r_hi r <=? img_limit) && region_wf r
&& zallb (img_writable_ok segs) (r_wlo r) (Z.to_nat (r_whi r - r_wlo r))
&& forallb (img_chunk_ok segs) (r_chunks r)
end.
Definition img_disjoint (r r' : region) : bool := (r_hi r <=? r_lo r') || (r_hi r' <=? r_lo r).
Fixpoint img_pairwise (rs : smem) : bool :=
match rs with [] => true | r :: rs' => forallb (img_disjoint r) rs' && img_pairwise rs' end.
Definition img_check (segs : list Segment) (img : smem) : bool :=
forallb (img_region_ok segs) img && img_pairwise img.
Section h.
Variable segs : list Segment.
Lemma img_regions_base : forall img r,
forallb (img_region_ok segs) img = true -> In r img -> r_base r = None.
Proof.
intros img r H Hin. pose proof (proj1 (forallb_forall _ _) H r Hin) as Hr.
unfold img_region_ok in Hr. destruct (r_base r); [discriminate| reflexivity].
Qed.
Lemma img_regions_hi : forall img r,
forallb (img_region_ok segs) img = true -> In r img -> 0 <= r_lo r /\ r_hi r <= img_limit.
Proof.
intros img r H Hin. pose proof (proj1 (forallb_forall _ _) H r Hin) as Hr.
unfold img_region_ok in Hr. destruct (r_base r); [discriminate|].
rewrite !andb_true_iff in Hr. destruct Hr as [[[[H1 H2] _] _] _].
apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma img_regions_wf : forall img, forallb (img_region_ok segs) img = true -> regions_wf img = true.
Proof.
induction img as [|r img IH]; cbn; intros H; [reflexivity|].
apply andb_prop in H as [Hr H]. rewrite IH, andb_true_r by exact H.
unfold img_region_ok in Hr. destruct (r_base r); [discriminate|].
rewrite !andb_true_iff in Hr. tauto.
Qed.
Lemma img_pairwise_sound : forall (E : env) img,
forallb (img_region_ok segs) img = true -> img_pairwise img = true -> pairwise_disjoint E img.
Proof.
intros E. induction img as [|r img IH]; cbn; intros Hok H; [exact I|].
apply andb_prop in Hok as [Hr Hok]. apply andb_prop in H as [Hd H].
split; [|apply IH; assumption].
assert (Hb : r_base r = None) by (unfold img_region_ok in Hr; destruct (r_base r); [discriminate|reflexivity]).
clear IH H Hr. induction img as [|r' img IH']; cbn; [exact I|].
cbn in Hd. apply andb_prop in Hd as [Hrr' Hd]. cbn in Hok. apply andb_prop in Hok as [Hr' Hok].
split; [|apply IH'; assumption].
assert (Hb' : r_base r' = None) by (unfold img_region_ok in Hr'; destruct (r_base r'); [discriminate|reflexivity]).
unfold extent_disjoint. rewrite Hb, Hb'. cbn [base_val].
unfold img_disjoint in Hrr'. apply orb_prop in Hrr' as [Hx|Hx]; apply Z.leb_le in Hx; lia.
Qed.
End h.
(* 08b1429: what lies at z_strs, up to ed_top *)
Definition stack_tail (av ev : list (list byte)) (xf : list byte) : list byte :=
flatten_strings av ++ flatten_strings ev ++ xf ++ [NUL] ++ repeat (Z_to_bv 8 0) 8.
Lemma bytes_at_addr : forall m a a' bs, a = a' -> bytes_at m a bs -> bytes_at m a' bs.
Proof. intros m a a' bs -> H. exact H. Qed.
Section t.
Variable segs : list Segment.
Variable ph : PhdrInfo.
Variable inp : ProcInput.
Variable pc : N.
Variables mbase sp brk : word.
Variable rnd : EntryDraw.
Local Notation av := (in_argv inp) (only parsing).
Local Notation ev := (in_envp inp) (only parsing).
Local Notation xf := (in_execfn inp) (only parsing).
Local Notation rs := (kb_rseq (in_kernel inp)) (only parsing).
Local Notation zsp := (bv_unsigned sp) (only parsing).
Local Notation zt := (bv_unsigned (ed_top rnd)) (only parsing).
Local Notation LS := (Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))) (only parsing).
Local Notation HS := (Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))) (only parsing).
Local Notation esi := (entry_stack_image inp mbase ph (Z_to_bv 64 (Z.of_N pc)) sp rnd) (only parsing).
Local Notation m0 := (wrap_mem inp mbase ph (Z_to_bv 64 (Z.of_N pc)) sp rnd) (only parsing).
Local Notation SB := (string_base_addr (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp)) (only parsing).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
Lemma zsp_lo : SP_LO <= zsp. Proof. exact (proj1 Hsp). Qed.
Lemma zsp_hi : zsp <= SP_HI. Proof. exact (proj1 (proj2 Hsp)). Qed.
Lemma zsp_al : zsp mod 16 = 0. Proof. exact (proj2 (proj2 Hsp)). Qed.
Lemma argc_bounds : 1 <= Z.of_nat (length av) <= 1024. Proof. exact (proj1 Hva). Qed.
Lemma envc_bound : Z.of_nat (length ev) <= 256. Proof. exact (proj1 Hve). Qed.
Lemma tab_av_bound : Z.of_nat (total_arg_bytes_nat av) <= 2097152.
Proof. rewrite <- total_arg_bytes_Z. exact (proj1 (proj2 Hva)). Qed.
Lemma tab_ev_bound : Z.of_nat (total_arg_bytes_nat ev) <= 131072.
Proof. rewrite <- total_arg_bytes_Z. exact (proj1 (proj2 Hve)). Qed.
Lemma top_hi : zt <= SP_HI.
Proof. destruct Hlau as ((_ & H & _) & _ & _). exact H. Qed.
Lemma top_lo : SP_HI - 1073741824 <= zt.
Proof.
destruct Hlau as ((_ & _ & H) & _ & _). change (va_stack_top Sv48) with SP_HI in H.
unfold stack_rnd_max, page_size, SP_HI in *. revert H. destruct (kb_aslr (in_kernel inp)); intros H; lia.
Qed.
Lemma ls_eq : LS = Z.of_nat (total_arg_bytes_nat av) + Z.of_nat (total_arg_bytes_nat ev) + Z.of_nat (length xf) + 1.
Proof. unfold launch_string_bytes. rewrite !length_flatten_strings. lia. Qed.
Lemma ls_bound : LS + 8 * (Z.of_nat (length av) + Z.of_nat (length ev)) <= 2097152.
Proof. destruct Hvl as [_ Hb]. unfold launch_bytes, e2big_limit in Hb. lia. Qed.
Lemma aux_size : Z.of_nat (auxv_size rs) = 432 \/ Z.of_nat (auxv_size rs) = 464.
Proof. destruct (kb_rseq (in_kernel inp)); [right|left]; reflexivity. Qed.
Lemma hs_eq : HS = 8 * (Z.of_nat (length av) + Z.of_nat (length ev) + 3) + Z.of_nat (auxv_size rs)
+ 8 * Z.of_nat ((length av + length ev + 3) mod 2) + 16.
Proof. unfold block_head_size, block_items. cbv zeta. lia. Qed.
Lemma hs_mod16 : HS mod 16 = 0.
Proof.
rewrite hs_eq.
pose proof (Nat.div_mod (length av + length ev + 3) 2 ltac:(lia)) as Dm.
assert (E : 8 * (Z.of_nat (length av) + Z.of_nat (length ev) + 3) + Z.of_nat (auxv_size rs)
+ 8 * Z.of_nat ((length av + length ev + 3) mod 2) + 16
= (Z.of_nat ((length av + length ev + 3) / 2) + Z.of_nat ((length av + length ev + 3) mod 2) + 1) * 16
+ Z.of_nat (auxv_size rs)) by lia.
rewrite E, Z.add_mod, Z_mod_mult, Z.add_0_l, Z.mod_mod by lia.
destruct aux_size as [A|A]; rewrite A; reflexivity.
Qed.
(* Run.entry_launch_ok_va: sp = align_down16(top - 8 - L - r) - C with r in [0, 4095] *)
Lemma launch_sp : zsp + HS <= zt - 8 - LS /\ zt - 8 - LS - (zsp + HS) <= 4110.
Proof.
destruct Hlau as (_ & (_ & Hlo & Hhi) & _).
unfold launch_sp_lo, launch_sp_hi, align_down16 in Hlo, Hhi.
pose proof (Z.mod_pos_bound (zt - 8 - LS) 16 ltac:(lia)).
pose proof (Z.mod_pos_bound (zt - 8 - LS - 4095) 16 ltac:(lia)).
split; lia.
Qed.
Lemma pad_eq : Z.of_nat (block_pad_len rs sp (ed_top rnd) av ev xf) = zt - 8 - LS - zsp - HS.
Proof. pose proof launch_sp as [H1 _]. unfold block_pad_len. rewrite Z2Nat.id by lia. reflexivity. Qed.
Lemma length_esi : Z.of_nat (length esi) = zt - zsp.
Proof. exact (length_entry_stack_image_launch Sv48 inp mbase ph (Z_to_bv 64 (Z.of_N pc)) sp brk rnd Hlau). Qed.
Lemma lay_strs : z_rand zsp rs av ev + 16 <= z_strs zt av ev xf /\ z_strs zt av ev xf + LS + 8 = zt.
Proof. pose proof launch_sp as [H1 _]. unfold z_rand, z_strs. lia. Qed.
Lemma m0_image : bytes_at m0 zsp esi.
Proof.
intros j Hj. pose proof length_esi as HB. pose proof top_hi as HT. pose proof zsp_lo as HL. pose proof (u64_range sp).
unfold SP_HI, SP_LO in *.
unfold wrap_mem, stack_to_mem. cbv zeta.
rewrite u_Z2bv by lia.
replace (bv_unsigned sp <=? bv_unsigned sp + Z.of_nat j) with true by (symmetry; apply Z.leb_le; lia).
replace (bv_unsigned sp + Z.of_nat j - bv_unsigned sp) with (Z.of_nat j) by lia.
replace (Z.of_nat j <? Z.of_nat (length esi)) with true by (symmetry; apply Z.ltb_lt; lia).
rewrite Nat2Z.id.
destruct (nth_error esi j) eqn:Hn; [reflexivity|].
exfalso. apply nth_error_None in Hn. lia.
Qed.
(* the zero window below sp is [stack_window_lo, sp) (Run.init_machine_state), at least 6144513 bytes *)
Lemma m0_zero : forall x, zsp - stack_window_depth <= x < zsp -> m0 (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
Proof.
intros x Hx. pose proof zsp_lo as HL. unfold SP_LO in HL.
pose proof (stack_window_lo_valid inp sp brk mbase rnd Hvl Hlau) as HW.
unfold stack_window_depth, stack_window_reach, stack_max_size in *.
pose proof (u64_range sp).
unfold wrap_mem, stack_to_mem. cbv zeta. rewrite u_Z2bv by lia.
replace (bv_unsigned sp <=? x) with false by (symmetry; apply Z.leb_gt; lia).
replace (stack_window_lo (in_kernel inp) mbase rnd <=? x) with true by (symmetry; apply Z.leb_le; lia).
replace (x <? bv_unsigned sp) with true by (symmetry; apply Z.ltb_lt; lia).
reflexivity.
Qed.
Lemma m0_below : forall x, 0 <= x < img_limit -> m0 (Z_to_bv 64 x) = None.
Proof.
intros x Hx. pose proof zsp_lo as HL. pose proof top_lo as HT. pose proof (u64_range sp).
assert (HW : bv_unsigned (ed_top rnd) - stack_max_size <= stack_window_lo (in_kernel inp) mbase rnd)
by (unfold stack_window_lo; apply Z.le_max_l).
unfold img_limit, SP_LO, SP_HI, stack_max_size in *.
unfold wrap_mem, stack_to_mem. cbv zeta. rewrite u_Z2bv by lia.
replace (bv_unsigned sp <=? x) with false by (symmetry; apply Z.leb_gt; lia).
replace (stack_window_lo (in_kernel inp) mbase rnd <=? x) with false by (symmetry; apply Z.leb_gt; lia).
reflexivity.
Qed.
Lemma m0_above : forall x, zt <= x < 2 ^ 64 -> m0 (Z_to_bv 64 x) = None.
Proof.
intros x Hx. pose proof length_esi as HB. pose proof zsp_lo. pose proof top_hi. pose proof (u64_range sp).
unfold SP_LO, SP_HI in *.
unfold wrap_mem, stack_to_mem. cbv zeta. rewrite u_Z2bv by lia.
replace (bv_unsigned sp <=? x) with true by (symmetry; apply Z.leb_le; lia).
replace (x - bv_unsigned sp <? Z.of_nat (length esi)) with false by (symmetry; apply Z.ltb_ge; lia).
replace (x <? bv_unsigned sp) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite andb_false_r. reflexivity.
Qed.
Lemma m0_dec : bytes_at m0 zsp
(word_le8 (len_word av)
++ flat_map word_le8 (fst (string_addrs SB av))
++ word_le8 (Z_to_bv 64 0)
++ flat_map word_le8 (fst (string_addrs (SB + nat_to_word (total_arg_bytes_nat av)) ev))
++ word_le8 (Z_to_bv 64 0)
++ auxv_bytes (launch_auxv inp sp mbase) ph (Z_to_bv 64 (Z.of_N pc)) (in_uid inp) (in_gid inp) (in_hwcap inp)
(at_random_ptr sp rs av ev) (at_execfn_ptr (ed_top rnd) xf)
++ repeat (Z_to_bv 8 0) (8 * (block_items av ev mod 2))
++ at_random_bytes (ed_random rnd)
++ repeat (Z_to_bv 8 0) (block_pad_len rs sp (ed_top rnd) av ev xf)
++ flatten_strings av ++ flatten_strings ev ++ xf ++ [Z_to_bv 8 0] ++ repeat (Z_to_bv 8 0) 8).
Proof. pose proof m0_image as H. unfold entry_stack_image in H. rewrite bsb_decomp in H. exact H. Qed.
Local Ltac lens H :=
rewrite ?length_app, ?length_n_to_le_8, ?length_flat_map_le8, ?length_string_addrs_fst, ?repeat_length,
?length_at_random_bytes, ?length_flatten_strings, ?length_auxv_bytes in H;
try change (la_rseq (launch_auxv inp sp mbase)) with (kb_rseq (in_kernel inp)) in H.
Lemma m0_argc : bytes_at m0 zsp (word_le8 (len_word av)).
Proof. pose proof m0_dec as H. exact (bytes_at_app_l _ _ _ _ H). Qed.
Lemma m0_argv_ptrs : bytes_at m0 (zsp + 8) (flat_map word_le8 (fst (string_addrs SB av))).
Proof.
pose proof m0_dec as H. apply bytes_at_app_r in H. apply bytes_at_app_l in H. lens H.
eapply bytes_at_addr; [|exact H]. lia.
Qed.
Lemma m0_argv_null : bytes_at m0 (z_envp zsp av - 8) (word_le8 (Z_to_bv 64 0)).
Proof.
pose proof m0_dec as H. do 2 (apply bytes_at_app_r in H). apply bytes_at_app_l in H. lens H.
eapply bytes_at_addr; [|exact H]. unfold z_envp. lia.
Qed.
Lemma m0_envp_ptrs : bytes_at m0 (z_envp zsp av) (flat_map word_le8 (fst (string_addrs (SB + nat_to_word (total_arg_bytes_nat av)) ev))).
Proof.
pose proof m0_dec as H. do 3 (apply bytes_at_app_r in H). apply bytes_at_app_l in H. lens H.
eapply bytes_at_addr; [|exact H]. unfold z_envp. lia.
Qed.
Lemma m0_envp_null : bytes_at m0 (z_auxv zsp av ev - 8) (word_le8 (Z_to_bv 64 0)).
Proof.
pose proof m0_dec as H. do 4 (apply bytes_at_app_r in H). apply bytes_at_app_l in H. lens H.
eapply bytes_at_addr; [|exact H]. unfold z_auxv, z_envp. lia.
Qed.
Lemma m0_auxv : bytes_at m0 (z_auxv zsp av ev)
(auxv_bytes (launch_auxv inp sp mbase) ph (Z_to_bv 64 (Z.of_N pc)) (in_uid inp) (in_gid inp) (in_hwcap inp)
(at_random_ptr sp rs av ev) (at_execfn_ptr (ed_top rnd) xf)).
Proof.
pose proof m0_dec as H. do 5 (apply bytes_at_app_r in H). apply bytes_at_app_l in H. lens H.
eapply bytes_at_addr; [|exact H]. unfold z_auxv, z_envp. lia.
Qed.
Lemma m0_rand : bytes_at m0 (z_rand zsp rs av ev) (rand_bytes rnd).
Proof.
pose proof m0_dec as H. do 7 (apply bytes_at_app_r in H). apply bytes_at_app_l in H. lens H.
eapply bytes_at_addr; [|exact H]. unfold z_rand. rewrite hs_eq. unfold block_items. lia.
Qed.
Lemma m0_tail : bytes_at m0 (z_strs zt av ev xf) (stack_tail av ev xf).
Proof.
pose proof m0_dec as H. do 9 (apply bytes_at_app_r in H). lens H.
eapply bytes_at_addr; [|exact H]. rewrite pad_eq. unfold z_strs. rewrite hs_eq. unfold block_items. lia.
Qed.
Lemma stack_tail_end : z_strs zt av ev xf + Z.of_nat (length (stack_tail av ev xf)) = zt.
Proof.
unfold stack_tail, z_strs. rewrite !length_app, !length_flatten_strings, repeat_length. cbn [length].
rewrite ls_eq. lia.
Qed.
Lemma m0_argv_strs : bytes_at m0 (z_strs zt av ev xf) (flatten_strings av).
Proof. pose proof m0_tail as H. unfold stack_tail in H. exact (bytes_at_app_l _ _ _ _ H). Qed.
Lemma m0_envp_strs : bytes_at m0 (z_strs zt av ev xf + Z.of_nat (total_arg_bytes_nat av)) (flatten_strings ev).
Proof.
pose proof m0_tail as H. unfold stack_tail in H. apply bytes_at_app_r in H. apply bytes_at_app_l in H.
rewrite length_flatten_strings in H. exact H.
Qed.
Lemma u_sb : bv_unsigned SB = z_strs zt av ev xf.
Proof. exact (u_cat_string_base Sv48 inp mbase sp brk rnd Hlau). Qed.
Lemma layout_facts :
z_envp zsp av = zsp + 16 + 8 * Z.of_nat (length av)
/\ z_auxv zsp av ev = z_envp zsp av + 8 * Z.of_nat (length ev) + 8
/\ z_rand zsp rs av ev = z_auxv zsp av ev + Z.of_nat (auxv_size rs) + 8 * Z.of_nat ((length av + length ev + 3) mod 2)
/\ z_rand zsp rs av ev + 16 <= z_strs zt av ev xf
/\ z_argv zt av ev xf 0 = z_strs zt av ev xf
/\ z_xfn zt av ev xf + Z.of_nat (length xf) + 1 + 8 = zt
/\ zt <= SP_HI
/\ SP_LO <= zsp <= SP_HI.
Proof.
pose proof hs_eq as HE. pose proof lay_strs as [L1 L2]. pose proof ls_eq as LE. pose proof top_hi. pose proof zsp_lo. pose proof zsp_hi.
unfold z_argv. rewrite firstn_O. change (total_arg_bytes_nat []) with 0%nat.
unfold z_xfn, z_rand, z_auxv, z_envp in *. repeat split; lia.
Qed.
Lemma argv_no_nul : forall k, (k < length av)%nat -> ~ In NUL (nth k av []).
Proof. intros k Hk. apply valid_argv_str_nz; [exact Hva| exact Hk]. Qed.
Lemma envp_no_nul : forall k, (k < length ev)%nat -> ~ In NUL (nth k ev []).
Proof.
intros k Hk. destruct Hve as (_ & _ & _ & Hnz). rewrite Forall_forall in Hnz.
apply Hnz. apply nth_In. exact Hk.
Qed.
Lemma argv_str_len : forall k, (k < length av)%nat -> Z.of_nat (length (nth k av [])) <= 131071.
Proof. intros k Hk. apply valid_argv_str_len; [exact Hva| exact Hk]. Qed.
Lemma z_argv_end : forall k, (k < length av)%nat ->
z_argv zt av ev xf k + Z.of_nat (length (nth k av [])) + 1
<= z_strs zt av ev xf + Z.of_nat (total_arg_bytes_nat av).
Proof. intros k Hk. unfold z_argv. pose proof (tab_firstn_nth_le av k Hk). lia. Qed.
Lemma z_envs_end : forall k, (k < length ev)%nat ->
z_envs zt av ev xf k + Z.of_nat (length (nth k ev [])) + 1 <= z_xfn zt av ev xf.
Proof. intros k Hk. unfold z_envs, z_xfn. pose proof (tab_firstn_nth_le ev k Hk). lia. Qed.
Lemma z_argv_bounds : forall k, (k < length av)%nat ->
z_strs zt av ev xf <= z_argv zt av ev xf k
/\ z_argv zt av ev xf k + Z.of_nat (length (nth k av [])) + 1
<= z_strs zt av ev xf + Z.of_nat (total_arg_bytes_nat av).
Proof. intros k Hk. split; [unfold z_argv; lia| apply z_argv_end; exact Hk]. Qed.
Lemma z_envs_bounds : forall k, (k < length ev)%nat ->
z_strs zt av ev xf + Z.of_nat (total_arg_bytes_nat av) <= z_envs zt av ev xf k
/\ z_envs zt av ev xf k + Z.of_nat (length (nth k ev [])) + 1 <= z_xfn zt av ev xf.
Proof. intros k Hk. split; [unfold z_envs; lia| apply z_envs_end; exact Hk]. Qed.
Lemma z_rand_end : z_rand zsp rs av ev + 16 < 2 ^ 63.
Proof. pose proof layout_facts as (_ & _ & _ & F4 & _ & F6 & F7 & _). pose proof lay_strs as [_ L2]. unfold SP_HI in *. lia. Qed.
Lemma block_fits : z_rand zsp rs av ev + 16 <= SP_HI.
Proof. pose proof layout_facts as (_ & _ & _ & F4 & _ & _ & F7 & _). pose proof lay_strs as [_ L2]. lia. Qed.
Lemma strs_fit : z_xfn zt av ev xf + Z.of_nat (length xf) + 1 <= SP_HI - 8.
Proof. pose proof layout_facts as (_ & _ & _ & _ & _ & F6 & F7 & _). lia. Qed.
Lemma z_argv_fits : forall k, (k < length av)%nat ->
z_argv zt av ev xf k + Z.of_nat (length (nth k av [])) + 1 <= SP_HI - 8.
Proof. intros k Hk. pose proof (z_argv_end k Hk). pose proof strs_fit. unfold z_xfn in *. lia. Qed.
Lemma z_envs_fits : forall k, (k < length ev)%nat ->
z_envs zt av ev xf k + Z.of_nat (length (nth k ev [])) + 1 <= SP_HI - 8.
Proof. intros k Hk. pose proof (z_envs_end k Hk). pose proof strs_fit. lia. Qed.
Lemma strs_lo : SP_LO <= z_strs zt av ev xf.
Proof. pose proof layout_facts as (_ & _ & F3 & F4 & _ & _ & _ & F8). pose proof aux_size. unfold z_auxv, z_envp in *. lia. Qed.
Lemma u_argv_ptr : forall k, (k < length av)%nat ->
nth k (fst (string_addrs SB av)) (Z_to_bv 64 0) = Z_to_bv 64 (z_argv zt av ev xf k).
Proof. intros k Hk. rewrite nth_string_addrs by exact Hk. rewrite word_add_nat, u_sb. reflexivity. Qed.
Lemma u_envp_ptr : forall k, (k < length ev)%nat ->
nth k (fst (string_addrs (SB + nat_to_word (total_arg_bytes_nat av)) ev)) (Z_to_bv 64 0) = Z_to_bv 64 (z_envs zt av ev xf k).
Proof.
intros k Hk. rewrite nth_string_addrs by exact Hk. rewrite !word_add_nat, u_sb.
pose proof strs_lo. pose proof strs_fit. unfold z_xfn, SP_LO, SP_HI in *.
rewrite u_Z2bv by lia. reflexivity.
Qed.
Lemma m0_argv_ptr : forall k, (k < length av)%nat ->
bytes_at m0 (zsp + 8 + 8 * Z.of_nat k) (word_le8 (Z_to_bv 64 (z_argv zt av ev xf k))).
Proof.
intros k Hk. rewrite <- u_argv_ptr by exact Hk. apply bytes_at_le8_nth; [exact m0_argv_ptrs|].
rewrite length_string_addrs_fst. exact Hk.
Qed.
Lemma m0_envp_ptr : forall k, (k < length ev)%nat ->
bytes_at m0 (z_envp zsp av + 8 * Z.of_nat k) (word_le8 (Z_to_bv 64 (z_envs zt av ev xf k))).
Proof.
intros k Hk. rewrite <- u_envp_ptr by exact Hk. apply bytes_at_le8_nth; [exact m0_envp_ptrs|].
rewrite length_string_addrs_fst. exact Hk.
Qed.
Lemma m0_argv_str : forall k, (k < length av)%nat ->
bytes_at m0 (z_argv zt av ev xf k) (nth k av [] ++ [NUL]).
Proof. intros k Hk. unfold z_argv. apply bytes_at_strings_nth; [exact m0_argv_strs| exact Hk]. Qed.
Lemma m0_envp_str : forall k, (k < length ev)%nat ->
bytes_at m0 (z_envs zt av ev xf k) (nth k ev [] ++ [NUL]).
Proof. intros k Hk. unfold z_envs. apply bytes_at_strings_nth; [exact m0_envp_strs| exact Hk]. Qed.
Lemma at_random_ptr_val : at_random_ptr sp rs av ev = Z_to_bv 64 (z_rand zsp rs av ev).
Proof. unfold at_random_ptr, z_rand. rewrite word_add_nat. f_equal. pose proof hs_eq. pose proof aux_size. lia. Qed.
Lemma zsp_pos : 0 <= zsp. Proof. pose proof zsp_lo. unfold SP_LO in *. lia. Qed.
Lemma envp_ptr_nonzero : forall k, (k < length ev)%nat ->
Z_to_bv 64 (z_envs zt av ev xf k) <> Z_to_bv 64 0.
Proof.
intros k Hk Heq. apply (f_equal bv_unsigned) in Heq.
pose proof (z_envs_bounds k Hk). pose proof strs_lo. pose proof strs_fit. unfold z_xfn, SP_LO, SP_HI in *.
rewrite u_Z2bv in Heq by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0 in Heq. lia.
Qed.
Lemma init_argv_ptr_rdn : forall k, (k < length av)%nat ->
rdn segs m0 (Z_to_bv 64 (zsp + 8 + 8 * Z.of_nat k)) 8 = Some (word_le8 (Z_to_bv 64 (z_argv zt av ev xf k))).
Proof. intros k Hk. apply (bytes_at_rdn segs m0 _ (word_le8 _)). apply m0_argv_ptr. exact Hk. Qed.
Lemma init_argv_cstr_rdn : forall k, (k < length av)%nat ->
rdn segs m0 (Z_to_bv 64 (z_argv zt av ev xf k)) (length (nth k av []) + 1) = Some (nth k av [] ++ [NUL]).
Proof.
intros k Hk. replace (length (nth k av []) + 1)%nat with (length (nth k av [] ++ [NUL]))
by (rewrite length_app; reflexivity).
apply bytes_at_rdn. apply m0_argv_str. exact Hk.
Qed.
Lemma init_envp_ptr_rdn : forall k, (k < length ev)%nat ->
rdn segs m0 (Z_to_bv 64 (z_envp zsp av + 8 * Z.of_nat k)) 8
= Some (word_le8 (Z_to_bv 64 (z_envs zt av ev xf k))).
Proof. intros k Hk. apply (bytes_at_rdn segs m0 _ (word_le8 _)). apply m0_envp_ptr. exact Hk. Qed.
Lemma init_envp_null_rdn :
rdn segs m0 (Z_to_bv 64 (z_envp zsp av + 8 * Z.of_nat (length ev))) 8 = Some (word_le8 (Z_to_bv 64 0)).
Proof.
replace (z_envp zsp av + 8 * Z.of_nat (length ev)) with (z_auxv zsp av ev - 8) by (unfold z_auxv; lia).
apply (bytes_at_rdn segs m0 _ (word_le8 _)). apply m0_envp_null.
Qed.
Lemma init_envp_cstr_rdn : forall k, (k < length ev)%nat ->
rdn segs m0 (Z_to_bv 64 (z_envs zt av ev xf k)) (length (nth k ev []) + 1) = Some (nth k ev [] ++ [NUL]).
Proof.
intros k Hk. replace (length (nth k ev []) + 1)%nat with (length (nth k ev [] ++ [NUL]))
by (rewrite length_app; reflexivity).
apply bytes_at_rdn. apply m0_envp_str. exact Hk.
Qed.
Variable W : Z.
Hypothesis HW : 0 < W <= stack_window_depth.
Lemma regions_wf_stack : forall two, regions_wf (stack_regions ph (Z.of_N pc) W two rs) = true.
Proof.
intros two. unfold stack_regions. cbn [regions_wf].
replace (region_wf (R_free W)) with true.
2:{ symmetry. unfold region_wf, R_free, chunk_inside, c_len, cv_len;
cbn [r_lo r_hi r_wlo r_whi r_chunks forallb c_off c_val].
rewrite !andb_true_iff, !orb_true_iff, !Z.leb_le. lia. }
destruct two; destruct (kb_rseq (in_kernel inp)); reflexivity.
Qed.
Variable xw : nat -> word.
Variable xd : nat -> list byte.
Hypothesis Hxd : xd UID_DATOM = uid_bytes (in_uid inp).
Hypothesis Hxh : xd HWCAP_DATOM = hwcap_bytes (in_hwcap inp).
Hypothesis Hxr : xd RAND_DATOM = rand_bytes rnd.
Hypothesis Hxg : xd GID_DATOM = word_le8 (in_gid inp).
Hypothesis Hxs : xd SYSI_DATOM = word_le8 (la_sysinfo_ehdr (launch_auxv inp sp mbase)).
Hypothesis Hxx : xd XFN_DATOM = word_le8 (at_execfn_ptr (ed_top rnd) (in_execfn inp)).
Hypothesis Hxm : xd MSS_DATOM = word_le8 (la_minsigstksz (launch_auxv inp sp mbase)).
Hypothesis Hxc : forall i, (i < 8)%nat ->
xd (CW_DATOM i) = word_le8 (nth i (cache_list (la_cache (launch_auxv inp sp mbase))) (Z_to_bv 64 0)).
Local Notation E := (E0 sp (ed_top rnd) (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp) (in_execfn inp) xw xd) (only parsing).
Lemma ed_uid : ed E UID_DATOM = word_le8 (in_uid inp). Proof. exact Hxd. Qed.
Lemma ed_hwcap : ed E HWCAP_DATOM = word_le8 (in_hwcap inp). Proof. exact Hxh. Qed.
Lemma ed_rand : ed E RAND_DATOM = rand_bytes rnd. Proof. exact Hxr. Qed.
Lemma ed_gid : ed E GID_DATOM = word_le8 (in_gid inp). Proof. exact Hxg. Qed.
Lemma ew0 : bv_unsigned (ew E 0) = zsp. Proof. reflexivity. Qed.
Lemma ew1 : bv_unsigned (ew E 1) = z_strs zt av ev xf.
Proof.
cbn [ew E0]. unfold z_argv. rewrite firstn_O. change (total_arg_bytes_nat []) with 0%nat.
pose proof strs_lo. pose proof strs_fit. unfold z_xfn, SP_LO, SP_HI in *.
rewrite u_Z2bv by lia. lia.
Qed.
Lemma ew2 : bv_unsigned (ew E 2) = z_strs zt av ev xf + Z.of_nat (length (nth 0 av [])) + 1.
Proof.
cbn [ew E0]. pose proof argc_bounds.
pose proof (z_argv_end 0 ltac:(lia)). pose proof strs_lo. pose proof strs_fit.
replace (z_argv (bv_unsigned (ed_top rnd)) (in_argv inp) (in_envp inp) (in_execfn inp) 1)
with (z_argv (bv_unsigned (ed_top rnd)) (in_argv inp) (in_envp inp) (in_execfn inp) 0 + Z.of_nat (length (nth 0 (in_argv inp) [])) + 1)
by (unfold z_argv; rewrite (tab_firstn_S (in_argv inp) 0) by lia; lia).
unfold z_argv, z_xfn, SP_LO, SP_HI in *. rewrite firstn_O in *. change (total_arg_bytes_nat []) with 0%nat in *.
rewrite u_Z2bv by lia. lia.
Qed.
Lemma ew2' : (2 <= length av)%nat -> bv_unsigned (ew E 2) = z_argv zt av ev xf 1.
Proof.
intros H2. rewrite ew2. unfold z_argv. rewrite (tab_firstn_S (in_argv inp) 0) by lia.
rewrite firstn_O. change (total_arg_bytes_nat []) with 0%nat. lia.
Qed.
Lemma ew3 : bv_unsigned (ew E 3) = Z.of_nat (length av).
Proof. cbn [ew E0]. pose proof argc_bounds. apply u_Z2bv; lia. Qed.
Lemma ew4 : bv_unsigned (ew E 4) = z_envp zsp av.
Proof.
cbn [ew E0]. pose proof layout_facts as (F1 & F2 & F3 & F4 & _ & _ & F7 & F8). pose proof aux_size. pose proof strs_fit.
unfold z_xfn, SP_LO, SP_HI in *. apply u_Z2bv; lia.
Qed.
Lemma ew5 : bv_unsigned (ew E 5) = z_auxv zsp av ev.
Proof.
cbn [ew E0]. pose proof layout_facts as (F1 & F2 & F3 & F4 & _ & _ & F7 & F8). pose proof aux_size. pose proof strs_fit.
unfold z_xfn, SP_LO, SP_HI in *. apply u_Z2bv; lia.
Qed.
Lemma ew6 : bv_unsigned (ew E 6) = z_rand zsp rs av ev.
Proof.
cbn [ew E0]. pose proof layout_facts as (F1 & F2 & F3 & F4 & _ & _ & F7 & F8). pose proof aux_size. pose proof strs_fit.
unfold z_xfn, SP_LO, SP_HI in *. apply u_Z2bv; lia.
Qed.
Lemma ew6_word : ew E 6 = at_random_ptr sp rs av ev.
Proof. rewrite at_random_ptr_val. reflexivity. Qed.
Lemma ed0 : ed E 0 = nth 0 av [] ++ [NUL]. Proof. reflexivity. Qed.
Lemma ed1 : ed E 1 = nth 1 av [] ++ [NUL]. Proof. reflexivity. Qed.
(* chunk lemmas over any environment: the auxv region is checked under each rseq case *)
Lemma chunk_ok_word : forall (En : env) m base off v (w : word),
sv_denot En v = w -> bytes_at m (base + off) (word_le8 w) ->
chunk_ok segs En m base (mkChunk off (CVal 8 v)).
Proof.
intros En m base off v w Hv Hb i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *.
exists (byte_of_word w i). split; [rewrite Hv; reflexivity|].
replace i with (Z.of_nat (Z.to_nat i)) by lia.
rewrite (bytes_at_mbyte segs m (base + off) (word_le8 w) (Z.to_nat i) Hb)
by (rewrite length_n_to_le_8; lia).
apply word_le8_nth. lia.
Qed.
Lemma chunk_ok_zero : forall (En : env) m base off len,
(forall i, 0 <= i < len -> m (Z_to_bv 64 (base + off + i)) = Some (Z_to_bv 8 0)) ->
chunk_ok segs En m base (mkChunk off (CZero len)).
Proof.
intros En m base off len H i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *.
exists (Z_to_bv 8 0). split; [reflexivity|]. unfold mbyte. rewrite H by exact Hi. reflexivity.
Qed.
Lemma chunk_ok_data1 : forall (En : env) m base off d s,
bytes_at m (base + off) [nth s (ed En d) NUL] -> (s < length (ed En d))%nat ->
chunk_ok segs En m base (mkChunk off (CData d (Z.of_nat s) 1)).
Proof.
intros En m base off d s Hb Hs i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *.
exists (nth s (ed En d) NUL). split.
- replace (Z.to_nat (Z.of_nat s + i)) with s by lia. apply nth_error_nth'. exact Hs.
- replace i with (Z.of_nat 0) by lia. apply (bytes_at_mbyte segs m (base + off) [nth s (ed En d) NUL] 0 Hb).
cbn. lia.
Qed.
Lemma chunk_ok_data8 : forall (En : env) m base off d (w : word),
ed En d = word_le8 w -> bytes_at m (base + off) (word_le8 w) ->
chunk_ok segs En m base (mkChunk off (CData d 0 8)).
Proof.
intros En m base off d w Hd Hb i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *.
rewrite Hd. exists (byte_of_word w i). split.
- rewrite Z.add_0_l. replace (Z.to_nat i) with (Z.to_nat i) by reflexivity.
rewrite word_le8_nth by lia. f_equal. f_equal. lia.
- replace i with (Z.of_nat (Z.to_nat i)) by lia.
rewrite (bytes_at_mbyte segs m (base + off) (word_le8 w) (Z.to_nat i) Hb)
by (rewrite length_n_to_le_8; lia).
apply word_le8_nth. lia.
Qed.
Lemma chunk_ok_data : forall (En : env) m base off d bs,
ed En d = bs -> bytes_at m (base + off) bs ->
chunk_ok segs En m base (mkChunk off (CData d 0 (Z.of_nat (length bs)))).
Proof.
intros En m base off d bs Hd Hb i Hi. cbn [c_off c_val c_len cv_len cbyte] in Hi |- *.
rewrite Hd, Z.add_0_l.
destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hn;
[| exfalso; apply nth_error_None in Hn; lia].
exists b. split; [reflexivity|].
replace i with (Z.of_nat (Z.to_nat i)) by lia.
rewrite (bytes_at_mbyte segs m (base + off) bs (Z.to_nat i) Hb) by lia. exact Hn.
Qed.
Lemma region_ok_free : region_ok segs E m0 (R_free W).
Proof.
unfold region_ok, R_free; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite ew0.
pose proof zsp_lo. pose proof zsp_hi. pose proof stack_window_depth_val. unfold SP_LO, SP_HI in *.
split; [lia|]. split; [lia|]. split.
- intros o Ho. unfold writable_at, wview. rewrite m0_zero by lia. discriminate.
- constructor; [|constructor]. apply chunk_ok_zero. intros i Hi. apply m0_zero. lia.
Qed.
Lemma sv_denot_SOff0 : forall n, sv_denot E (SOff n 0) = ew E n.
Proof. intros n. cbn. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma region_ok_hdr : forall two : bool,
(if two then 2 <= length av else True)%nat -> region_ok segs E m0 (R_hdr two).
Proof.
intros two Htwo.
unfold region_ok, R_hdr; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite ew0.
pose proof zsp_lo. pose proof zsp_hi. unfold SP_LO, SP_HI in *. pose proof argc_bounds.
split; [lia|]. split; [destruct two; lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
- apply (chunk_ok_word _ _ _ _ _ (len_word av)).
+ rewrite sv_denot_SOff0. apply bv_eq. rewrite ew3. unfold len_word. symmetry. apply u_Z2bv; lia.
+ rewrite Z.add_0_r. exact m0_argc.
- apply (chunk_ok_word _ _ _ _ _ (Z_to_bv 64 (z_argv zt av ev xf 0))).
+ rewrite sv_denot_SOff0. reflexivity.
+ replace (zsp + 8) with (zsp + 8 + 8 * Z.of_nat 0) by lia. apply m0_argv_ptr. lia.
- destruct two; [|constructor]. constructor; [|constructor].
apply (chunk_ok_word _ _ _ _ _ (Z_to_bv 64 (z_argv zt av ev xf 1))).
+ rewrite sv_denot_SOff0. reflexivity.
+ replace (zsp + 16) with (zsp + 8 + 8 * Z.of_nat 1) by lia. apply m0_argv_ptr. lia.
Qed.
Lemma region_ok_argvnull : region_ok segs E m0 R_argvnull.
Proof.
unfold region_ok, R_argvnull; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite ew4.
pose proof layout_facts as (F1 & F2 & F3 & F4 & _ & _ & F7 & F8). pose proof argc_bounds. pose proof aux_size. pose proof strs_fit.
unfold z_xfn, SP_LO, SP_HI in *.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_word _ _ _ _ _ (Z_to_bv 64 0)); [reflexivity|].
replace (z_envp zsp av + -8) with (z_envp zsp av - 8) by lia. exact m0_argv_null.
Qed.
Lemma region_ok_envnull : region_ok segs E m0 R_envnull.
Proof.
unfold region_ok, R_envnull; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite ew5.
pose proof layout_facts as (F1 & F2 & F3 & F4 & _ & _ & F7 & F8). pose proof argc_bounds. pose proof envc_bound. pose proof aux_size. pose proof strs_fit.
unfold z_xfn, SP_LO, SP_HI in *.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_word _ _ _ _ _ (Z_to_bv 64 0)); [reflexivity|].
replace (z_auxv zsp av ev + -8) with (z_auxv zsp av ev - 8) by lia. exact m0_envp_null.
Qed.
(* both auxv layouts (27 pairs, or 29 under CONFIG_RSEQ): a case split on kb_rseq, no kernel pin *)
Lemma region_ok_auxv : region_ok segs E m0 (R_auxv ph (Z.of_N pc) rs).
Proof.
pose proof m0_auxv as H. unfold auxv_bytes in H. rewrite build_auxv_words in H.
pose proof (sv_denot_SOff0 6) as HR6. rewrite ew6_word in HR6.
unfold region_ok, R_auxv; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite ew5.
pose proof layout_facts as (F1 & F2 & F3 & F4 & _ & _ & F7 & F8). pose proof aux_size as AS. pose proof strs_fit.
unfold z_xfn, SP_LO, SP_HI in *.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
clear F1 F2 F3 F4 F7 F8 AS.
unfold auxv_entries in H. cbn [la_rseq launch_auxv la_cache la_sysinfo_ehdr la_minsigstksz] in H.
unfold auxv_chunks. revert H HR6.
destruct (kb_rseq (in_kernel inp)); intros H HR6; cbn [app] in H |- *;
set (WL := auxv_words _) in H;
(repeat match goal with
| |- Forall _ [] => constructor
| |- Forall _ (mkChunk ?off (CData _ _ _) :: _) =>
constructor;
[ apply (chunk_ok_data8 _ _ _ _ _ (nth (Z.to_nat (off / 8)) WL (Z_to_bv 64 0)));
[ first [ exact Hxd | exact Hxh | exact Hxg | exact Hxs | exact Hxx | exact Hxm
| exact (Hxc 0 ltac:(lia)) | exact (Hxc 1 ltac:(lia)) | exact (Hxc 2 ltac:(lia)) | exact (Hxc 3 ltac:(lia))
| exact (Hxc 4 ltac:(lia)) | exact (Hxc 5 ltac:(lia)) | exact (Hxc 6 ltac:(lia)) | exact (Hxc 7 ltac:(lia)) ]
| replace (z_auxv (bv_unsigned sp) (in_argv inp) (in_envp inp) + off)
with (z_auxv (bv_unsigned sp) (in_argv inp) (in_envp inp) + 8 * Z.of_nat (Z.to_nat (off / 8))) by (clear; cbn; lia);
apply bytes_at_le8_nth; [exact H | unfold WL; rewrite length_auxv_words; cbn [length]; clear; cbn; lia] ]
| ]
| |- Forall _ (mkChunk ?off _ :: _) =>
constructor;
[ apply (chunk_ok_word _ _ _ _ _ (nth (Z.to_nat (off / 8)) WL (Z_to_bv 64 0)));
[ | replace (z_auxv (bv_unsigned sp) (in_argv inp) (in_envp inp) + off)
with (z_auxv (bv_unsigned sp) (in_argv inp) (in_envp inp) + 8 * Z.of_nat (Z.to_nat (off / 8))) by (clear; cbn; lia);
apply bytes_at_le8_nth; [exact H | unfold WL; rewrite length_auxv_words; cbn [length]; clear; cbn; lia] ]
| ]
end);
first [exact HR6 | reflexivity].
Qed.
Lemma region_ok_rand : region_ok segs E m0 R_rand.
Proof.
unfold region_ok, R_rand; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite ew6.
pose proof layout_facts as (F1 & F2 & F3 & F4 & _ & _ & F7 & F8). pose proof aux_size. pose proof strs_fit.
unfold z_xfn, SP_LO, SP_HI in *.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
change 16 with (Z.of_nat (length (rand_bytes rnd))). apply chunk_ok_data; [exact ed_rand|].
rewrite Z.add_0_r. exact m0_rand.
Qed.
Lemma region_ok_argv0 : region_ok segs E m0 R_argv0.
Proof.
unfold region_ok, R_argv0; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite ew1.
pose proof strs_lo. pose proof strs_fit. pose proof argc_bounds. unfold z_xfn, SP_LO, SP_HI in *.
pose proof (z_argv_end 0 ltac:(lia)).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
change (CData 0 0 1) with (CData 0 (Z.of_nat 0) 1). apply chunk_ok_data1.
- rewrite ed0, Z.add_0_r. intros j Hj. cbn in Hj.
pose proof (m0_argv_str 0 ltac:(lia)) as Hs. unfold z_argv in Hs. rewrite firstn_O in Hs.
change (total_arg_bytes_nat []) with 0%nat in Hs. rewrite Z.add_0_r in Hs.
rewrite (Hs j) by (rewrite length_app; cbn; lia).
destruct j; [|lia]. destruct (nth 0 (in_argv inp) [] ++ [NUL]) eqn:Hn; [|reflexivity].
exfalso. destruct (nth 0 (in_argv inp) []); discriminate.
- rewrite ed0, length_app. cbn. lia.
Qed.
Lemma region_ok_argv1 : (2 <= length av)%nat -> region_ok segs E m0 R_argv1.
Proof.
intros H2.
unfold region_ok, R_argv1; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite (ew2' H2).
pose proof strs_lo. pose proof strs_fit. unfold z_xfn, SP_LO, SP_HI in *.
pose proof (z_argv_end 1 ltac:(lia)).
assert (Hz0 : z_strs zt av ev xf <= z_argv zt av ev xf 1) by (unfold z_argv; lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
change (CData 1 0 1) with (CData 1 (Z.of_nat 0) 1). apply chunk_ok_data1.
- rewrite ed1, Z.add_0_r. intros j Hj. cbn in Hj.
pose proof (m0_argv_str 1 ltac:(lia)) as Hs.
rewrite (Hs j) by (rewrite length_app; cbn; lia).
destruct j; [|lia]. destruct (nth 1 (in_argv inp) [] ++ [NUL]) eqn:Hn; [|reflexivity].
exfalso. destruct (nth 1 (in_argv inp) []); discriminate.
- rewrite ed1, length_app. cbn. lia.
Qed.
Lemma pairwise_disjoint_stack : forall two : bool,
(if two then 2 <= length av else True)%nat ->
pairwise_disjoint E (stack_regions ph (Z.of_N pc) W two rs).
Proof.
intros two Htwo.
pose proof layout_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
pose proof argc_bounds as HA. pose proof envc_bound as HE. pose proof aux_size as AS. pose proof strs_fit.
pose proof (z_argv_end 0 ltac:(lia)) as HZ0. pose proof ew2 as E2.
unfold z_xfn in *.
unfold stack_regions. destruct two; cbn [pairwise_disjoint all_disjoint app]; unfold extent_disjoint;
cbn [r_base r_lo r_hi R_free R_hdr R_argvnull R_envnull R_auxv R_rand R_argv0 R_argv1 base_val];
rewrite ?ew0, ?ew1, ?ew3, ?ew4, ?ew5, ?ew6 in *.
- repeat split; lia.
- repeat split; lia.
Qed.
Lemma stack_regions_lo : forall two r, In r (stack_regions ph (Z.of_N pc) W two rs) ->
img_limit <= base_val E (r_base r) + r_lo r.
Proof.
intros two r Hin.
pose proof layout_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8). pose proof argc_bounds as HA. pose proof ew2 as E2.
pose proof stack_window_depth_val. pose proof aux_size. pose proof strs_lo.
unfold img_limit, SP_LO, SP_HI in *.
unfold stack_regions in Hin. cbn [In app] in Hin.
repeat match type of Hin with
| _ \/ _ => destruct Hin as [<-|Hin]
| In _ (if ?b then _ else _) => destruct b; cbn [In] in Hin
| False => destruct Hin
end;
cbn [r_base r_lo R_free R_hdr R_argvnull R_envnull R_auxv R_rand R_argv0 R_argv1 base_val];
rewrite ?ew0, ?ew1, ?ew3, ?ew4, ?ew5, ?ew6; lia.
Qed.

Lemma region_ok_img : forall r, img_region_ok segs r = true -> region_ok segs E m0 r.
Proof.
intros r H. unfold img_region_ok in H.
destruct (r_base r) as [n|] eqn:Hb; [discriminate|].
apply andb_prop in H as [H Hc]. apply andb_prop in H as [H Hw]. apply andb_prop in H as [H Hwf].
apply andb_prop in H as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
apply region_wf_facts in Hwf as (Hlohi & Hwr & Hci).
pose proof zsp_lo as HL. unfold img_limit, SP_LO in *. pose proof stack_max_size_val as HSZ.
unfold region_ok. rewrite Hb. cbn [base_val]. rewrite !Z.add_0_l.
split; [lia|]. split; [lia|]. split.
- intros o Ho. pose proof (zallb_sound _ _ _ o Hw ltac:(lia)) as Ho'. unfold img_writable_ok in Ho'.
unfold writable_at. rewrite Z.add_0_l.
apply (wview_grows segs (fun _ => None)); [intros x Hx; exfalso; apply Hx; reflexivity|].
destruct (wview segs (fun _ => None) (Z_to_bv 64 o)); [discriminate| discriminate Ho'].
- apply Forall_forall. intros c Hin.
pose proof (proj1 (forallb_forall _ _) Hc c Hin) as Hck.
pose proof (chunk_inside_facts r c (proj1 (forallb_forall _ _) Hci c Hin)) as (C1 & C2 & C3).
intros i Hi. unfold img_chunk_ok in Hck.
assert (Hm : m0 (Z_to_bv 64 (0 + c_off c + i)) = None).
{ apply m0_below. cbn [c_off c_len] in Hi. unfold img_limit, SP_LO. lia. }
unfold mbyte. rewrite Hm. rewrite Z.add_0_l in *.
unfold c_len in Hi.
destruct (c_val c) as [w v|len|len|d s len] eqn:Hcv; try discriminate Hck; cbn [cbyte cv_len] in Hi |- *.
+ pose proof (zallb_sound _ _ _ (c_off c + i) Hck ltac:(lia)) as Hz. unfold img_zero_ok, img_byte in Hz.
destruct (seg_rom segs (Z_to_bv 64 (c_off c + i))) as [b|]; [|discriminate].
exists (Z_to_bv 8 0). split; [reflexivity|]. f_equal.
unfold bv_eqb in Hz. apply Z.eqb_eq in Hz. apply bv_eq. exact Hz.
+ pose proof (zallb_sound _ _ _ (c_off c + i) Hck ltac:(lia)) as Hz. unfold img_byte_ok, img_byte in Hz.
unfold img_byte.
destruct (seg_rom segs (Z_to_bv 64 (c_off c + i))) as [b|]; [|discriminate].
exists b. split; reflexivity.
Qed.
Lemma regs_ok_init : regs_ok E regs0 (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp).
Proof.
intros r. unfold sr_get, regs0.
assert (Hsr : forall r' : reg, bv_unsigned r' <> 2 ->
sv_denot E (if bv_eqb r' 0 then SLit 0 else nth (ridx r') [SLit 0; SLit 0; SOff 0 0] (SLit 0))
= Z_to_bv 64 0).
{ intros r' Hr'. destruct (bv_eqb r' 0); [reflexivity|]. unfold ridx.
destruct (Z.to_nat (bv_unsigned r')) as [|[|[|k]]] eqn:Hk; try reflexivity; [exfalso; lia|].
destruct k; reflexivity. }
destruct (Z.eq_dec (bv_unsigned r) 2) as [Hr2|Hr2].
- assert (r = 2%bv) as -> by (apply bv_eq; exact Hr2).
rewrite getr_same by reg_neq_tac.
match goal with |- _ = sv_denot E ?v => replace v with (SOff 0 0) by reflexivity end.
symmetry. apply sv_denot_SOff0.
- rewrite Hsr by exact Hr2.
rewrite getr_other by (intros H; apply Hr2; rewrite H; reflexivity).
destruct (Z.eq_dec (bv_unsigned r) 10) as [Hr10|Hr10].
+ assert (r = 10%bv) as -> by (apply bv_eq; exact Hr10). rewrite getr_same by reg_neq_tac. reflexivity.
+ rewrite getr_other by (intros H; apply Hr10; rewrite H; reflexivity).
unfold getr. destruct (bv_eqb r 0); [reflexivity|].
unfold reg_get, bvmap_get, bvmap_empty. rewrite tget_empty. reflexivity.
Qed.
Lemma facts_ok_init : forall two : bool,
(if two then 2 <= length av else True)%nat -> facts_ok E (G0 two).
Proof.
intros two Htwo. unfold facts_ok, G0; cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
split; [|split; exact I].
pose proof layout_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
pose proof argc_bounds as HA. pose proof envc_bound as HE. pose proof zsp_al as HAL.
pose proof hs_mod16 as H16. pose proof aux_size as AS. pose proof strs_lo as SL. pose proof strs_fit as SF.
pose proof (z_argv_end 0 ltac:(lia)) as HZ0. pose proof ew2 as E2.
unfold afact_ok, ptr_fact; cbn [af_lo af_hi af_al2].
rewrite ew0, ew1, ew3, ew4, ew5, ew6.
change (2^4) with 16. change (2^3) with 8. change (2^0) with 1. rewrite !Z.mod_1_r.
assert (H8b : (bv_unsigned sp + 16 + 8 * Z.of_nat (length av)) mod 8 = 0).
{ replace (bv_unsigned sp + 16 + 8 * Z.of_nat (length av)) with (bv_unsigned sp + 8 * (2 + Z.of_nat (length av))) by lia.
apply mod8_of_mod16. exact HAL. }
assert (H8c : (bv_unsigned sp + 16 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 8) mod 8 = 0).
{ replace (bv_unsigned sp + 16 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 8)
with (bv_unsigned sp + 8 * (3 + Z.of_nat (length av) + Z.of_nat (length ev))) by lia.
apply mod8_of_mod16. exact HAL. }
assert (H8d : (bv_unsigned sp + HS - 16) mod 8 = 0).
{ pose proof (Z.div_mod HS 16 ltac:(lia)) as Dm. rewrite H16, Z.add_0_r in Dm.
replace (bv_unsigned sp + HS - 16) with (bv_unsigned sp + 8 * (2 * (HS / 16) - 2)) by lia.
apply mod8_of_mod16. exact HAL. }
unfold z_argv in HZ0. rewrite firstn_O in HZ0. change (total_arg_bytes_nat []) with 0%nat in HZ0.
unfold z_xfn, z_rand, z_auxv, z_envp, SP_LO, SP_HI in *.
destruct two; repeat split; try lia.
Qed.
Theorem init_st_ok : forall (two : bool) (img : smem),
(if two then 2 <= length av else True)%nat ->
img_check segs img = true ->
@st_ok segs fx0 E (ss0 (Z.of_N pc) ph W two rs img) (init_machine_state segs pc ph sp mbase rnd inp).
Proof.
intros two img Htwo Himg. unfold img_check in Himg. apply andb_prop in Himg as [Hiok Hipw].
rewrite init_mkst. unfold st_ok, ss0, mkst;
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem
ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [apply regs_ok_init|].
split; [|apply facts_ok_init; exact Htwo].
split; [|split].
- rewrite regions_wf_app, regions_wf_stack, (img_regions_wf segs) by exact Hiok. reflexivity.
- apply Forall_app. split.
+ unfold stack_regions.
constructor; [apply region_ok_free|].
constructor; [apply region_ok_hdr; exact Htwo|].
constructor; [apply region_ok_argvnull|].
constructor; [apply region_ok_envnull|].
constructor; [apply region_ok_auxv|].
constructor; [apply region_ok_rand|].
constructor; [apply region_ok_argv0|].
destruct two; [|constructor]. constructor; [apply region_ok_argv1; exact Htwo| constructor].
+ apply Forall_forall. intros r Hin. apply region_ok_img.
exact (proj1 (forallb_forall _ _) Hiok r Hin).
- apply pairwise_disjoint_app.
+ apply pairwise_disjoint_stack. exact Htwo.
+ apply (img_pairwise_sound segs); assumption.
+ intros r1 r2 H1 H2. unfold extent_disjoint. right.
pose proof (stack_regions_lo two r1 H1).
pose proof (img_regions_hi segs img r2 Hiok H2) as [Hlo2 Hhi2].
rewrite (img_regions_base segs img r2 Hiok H2). cbn [base_val]. lia.
Qed.
Lemma afact_ok_argc : forall lo hi : Z,
lo <= Z.of_nat (length av) <= hi -> afact_ok E 3 (mkAF lo hi 0).
Proof.
intros lo hi H. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite ew3.
change (2^0) with 1. rewrite Z.mod_1_r. lia.
Qed.
Lemma sext32_argc : sv_denot E (SExt true 32 (SOff 3 0)) = sv_denot E (SOff 3 0).
Proof.
pose proof ew3 as H3. pose proof argc_bounds.
cbn [sv_denot]. rewrite Z.add_0_r, H3.
apply bv_eq. unfold sext. rewrite bv_sign_extend_unsigned.
unfold bv_signed. rewrite bv_extract_unsigned, Z.shiftr_0_r, !Z_to_bv_unsigned.
unfold bv_swrap, bv_wrap.
change (bv_modulus 64) with (2^64). change (bv_modulus 32) with (2^32).
change (bv_half_modulus 32) with (2^31).
rewrite (Z.mod_small (Z.of_nat (length av)) (2^64)) by lia.
rewrite (Z.mod_small (Z.of_nat (length av)) (2^32)) by lia.
rewrite (Z.mod_small (_ + 2^31) (2^32)) by lia.
rewrite ?Z.mod_small by lia. lia.
Qed.
End t.
Fixpoint cond_caps_whi (l : list acond) (n : nat) (whi lo hi : Z) : bool :=
match l with
| [] => false
| c :: l' =>
(match ac_c c, ac_a c, ac_b c with
| BC_GEU, SOff O 0, SOff m K =>
Nat.eqb m n && (whi <=? K) && (0 <=? lo + K) && (hi + K <? 2 ^ 64)
| _, _, _ => false
end) || cond_caps_whi l' n whi lo hi
end.
Definition wr_below_sp (G : facts) (rs : smem) : bool :=
match atom_lookup (f_atoms G) 0 with
| None => false
| Some f0 =>
forallb (fun r =>
(r_whi r <=? r_wlo r) ||
match r_base r with
| None => r_whi r <=? af_lo f0
| Some O => r_whi r <=? 0
| Some n => match atom_lookup (f_atoms G) n with
| Some f => (af_hi f + r_whi r <=? af_lo f0)
|| cond_caps_whi (f_conds G) n (r_whi r) (af_lo f) (af_hi f)
| None => false
end
end) rs
end.
Lemma acond_geu_sp_intro : forall E n K,
0 <= bv_unsigned (ew E n) + K <= bv_unsigned (ew E 0) ->
branch_taken BC_GEU (sv_denot E (SOff 0 0)) (sv_denot E (SOff n K)) = true.
Proof.
intros E n K HK. pose proof (u64_range (ew E 0)) as H0.
cbn [branch_taken sv_denot]. unfold bv_ltu. rewrite Z.add_0_r, !Z_to_bv_unsigned.
change (bv_wrap 64 ?x) with (x mod 2^64). rewrite !Z.mod_small by lia.
apply negb_true_iff. apply Z.ltb_ge. lia.
Qed.
Lemma cond_caps_whi_sound : forall E l n whi lo hi,
conds_ok E l -> cond_caps_whi l n whi lo hi = true ->
lo <= bv_unsigned (ew E n) <= hi ->
bv_unsigned (ew E n) + whi <= bv_unsigned (ew E 0).
Proof.
intros E l n whi lo hi. induction l as [|c l IH]; cbn [cond_caps_whi conds_ok]; intros Hok H Hn;
[discriminate|].
destruct Hok as [Hc Hl]. apply orb_prop in H as [H|H]; [|exact (IH Hl H Hn)]. clear IH Hl.
destruct c as [cc ca cb]; cbn [ac_c ac_a ac_b] in H. unfold acond_ok in Hc; cbn [ac_c ac_a ac_b] in Hc.
destruct cc; try discriminate H.
destruct ca as [|n0 z0| | | | | | | | |]; try discriminate H.
destruct n0; [|discriminate H]. destruct z0; try discriminate H.
destruct cb as [|m K| | | | | | | | |]; try discriminate H.
rewrite !andb_true_iff in H. destruct H as [[[Hm Hw] Hlo] Hhi].
apply Nat.eqb_eq in Hm. subst m. apply Z.leb_le in Hw. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
pose proof (u64_range (ew E 0)) as H0.
cbn [branch_taken sv_denot] in Hc. unfold bv_ltu in Hc. rewrite Z.add_0_r, !Z_to_bv_unsigned in Hc.
change (bv_wrap 64 ?x) with (x mod 2^64) in Hc. rewrite !Z.mod_small in Hc by lia.
apply negb_true_iff in Hc. apply Z.ltb_ge in Hc. lia.
Qed.
Lemma wr_below_sp_sound : forall E G rs x,
facts_ok E G -> wr_below_sp G rs = true -> in_wrange E rs x -> x < bv_unsigned (ew E 0).
Proof.
intros E G rs x HG H (r & Hin & Hx). unfold wr_below_sp in H.
destruct (atom_lookup (f_atoms G) 0) as [f0|] eqn:H0; [|discriminate].
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) H0) as (Hf0 & _).
pose proof (proj1 (forallb_forall _ _) H r Hin) as Hr. cbn beta in Hr.
apply orb_prop in Hr as [Hr|Hr]; [apply Z.leb_le in Hr; lia|].
destruct (r_base r) as [[|n]|] eqn:Hb; cbn [base_val] in Hx.
- apply Z.leb_le in Hr. lia.
- destruct (atom_lookup (f_atoms G) (S n)) as [f|] eqn:Hn; [|discriminate].
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hn) as (Hf & _).
apply orb_prop in Hr as [Hr|Hr]; [apply Z.leb_le in Hr; lia|].
pose proof (cond_caps_whi_sound E (f_conds G) (S n) (r_whi r) (af_lo f) (af_hi f)
(proj1 (proj2 HG)) Hr Hf). lia.
- apply Z.leb_le in Hr. lia.
Qed.
Lemma bytes_at_frame_sp : forall E G rs m m' a bs,
facts_ok E G -> wr_below_sp G rs = true -> frame_of E rs m m' ->
bv_unsigned (ew E 0) <= a -> a + Z.of_nat (length bs) <= 2^64 ->
bytes_at m a bs -> bytes_at m' a bs.
Proof.
intros E G rs m m' a bs HG Hw Hfr Ha Hnw H.
pose proof (u64_range (ew E 0)).
apply (bytes_at_frame m m' a bs); [|lia|exact Hnw|exact H].
intros x Hx. apply Hfr. intros Hin. pose proof (wr_below_sp_sound E G rs _ HG Hw Hin). lia.
Qed.
