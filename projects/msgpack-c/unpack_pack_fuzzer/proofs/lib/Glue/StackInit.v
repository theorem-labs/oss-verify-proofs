(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the entry block read off by offset over the launch's whole ProcInput and mmap base: Linux's layout with the 27- or 29-pair auxv by la_rseq (LA, auxws, AUXV, length_AUXV, length_auxws), the odd-item gap, AT_RANDOM, the arch_align_stack pad, the strings with the exec name and the eight-byte slot under the stack VMA's end (strarea, length_strarea); the window below sp from stack_window_lo (WLO); flat_pairs added; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)). *)
From Stdlib Require Import ZArith NArith Bool List Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Z_to_bv : simpl never.

Module SI.

Fixpoint total_nat (args : list (list byte)) : nat :=
  match args with [] => 0%nat | a :: args' => (length a + 1 + total_nat args')%nat end.

Lemma total_arg_bytes_nat : forall l, total_arg_bytes l = Z.of_nat (total_nat l).
Proof.
  induction l as [|x l IH]; [reflexivity|].
  cbv [total_arg_bytes] in *. cbn [fold_right total_nat]. rewrite IH. lia.
Qed.

Lemma length_flatten_strings : forall l, length (flatten_strings l) = total_nat l.
Proof.
  induction l as [|x l IH]; [reflexivity|].
  unfold flatten_strings in *. cbn [flat_map total_nat]. rewrite !length_app, IH. cbn [length]. lia.
Qed.

Lemma length_word_le8 : forall w, length (word_le8 w) = 8%nat.
Proof. reflexivity. Qed.

Lemma length_flat_map_le8 : forall l, length (flat_map word_le8 l) = (8 * length l)%nat.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [flat_map]. rewrite length_app, IH, length_word_le8. cbn [length]. lia. Qed.

Lemma u64_range : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range _ w). unfold bv_modulus in H. exact H. Qed.

Lemma Z_to_bv64_unsigned : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hz. Qed.

Lemma nat_to_word_add : forall (a : word) (n : nat),
  bv_unsigned a + Z.of_nat n < 2 ^ 64 -> bv_unsigned (a + nat_to_word n)%bv = bv_unsigned a + Z.of_nat n.
Proof.
  intros a n H. unfold nat_to_word. rewrite bv_add_unsigned, Z_to_bv_unsigned.
  pose proof (u64_range a).
  rewrite (bv_wrap_small 64 (Z.of_nat n)) by (unfold bv_modulus; lia).
  apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

Lemma word_add_0 : forall a : word, (a + nat_to_word 0)%bv = a.
Proof. intros a. apply bv_add_0_r. reflexivity. Qed.

Lemma nat_to_word_merge : forall m k : nat, (nat_to_word m + nat_to_word k)%bv = nat_to_word (m + k).
Proof.
  intros m k. apply bv_eq. unfold nat_to_word.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned, bv_wrap_add_idemp. f_equal. lia.
Qed.

Lemma nat_to_word_add_merge : forall (a : word) (m k : nat),
  (a + nat_to_word m + nat_to_word k)%bv = (a + nat_to_word (m + k))%bv.
Proof.
  intros a m k. rewrite <- nat_to_word_merge. apply bv_eq.
  rewrite !bv_add_unsigned. rewrite bv_wrap_add_idemp_l, bv_wrap_add_idemp_r. f_equal. lia.
Qed.

Lemma len_word_nat : forall (s : list byte), len_word s = nat_to_word (length s).
Proof. reflexivity. Qed.
Lemma word1_nat : (1%bv : word) = nat_to_word 1.
Proof. apply bv_eq. reflexivity. Qed.

Lemma string_addrs_pair : forall strs (base : word),
  string_addrs base strs = (fst (string_addrs base strs), (base + nat_to_word (total_nat strs))%bv).
Proof.
  induction strs as [|s rest IH]; intro base.
  - cbn. rewrite word_add_0. reflexivity.
  - cbn [string_addrs]. rewrite (IH (base + len_word s + 1)%bv). cbn [fst]. f_equal.
    rewrite len_word_nat, word1_nat, !nat_to_word_add_merge. cbn [total_nat]. f_equal. f_equal. lia.
Qed.

Lemma string_addrs_fst : forall strs (base : word),
  fst (string_addrs base strs) =
  match strs with [] => [] | s :: rest => base :: fst (string_addrs (base + len_word s + 1)%bv rest) end.
Proof.
  intros strs base. destruct strs as [|s rest]; [reflexivity|]. cbn [string_addrs].
  destruct (string_addrs (base + len_word s + 1)%bv rest); reflexivity.
Qed.

Lemma length_string_addrs_fst : forall strs (base : word), length (fst (string_addrs base strs)) = length strs.
Proof.
  induction strs as [|s rest IH]; intro base; [reflexivity|].
  rewrite string_addrs_fst. cbn [length]. rewrite IH. reflexivity.
Qed.

Lemma word_le8_nth : forall (w : word) (i : nat) d, (i < 8)%nat ->
  nth i (word_le8 w) d = Z_to_bv 8 (Z.shiftr (bv_unsigned w) (8 * Z.of_nat i)).
Proof.
  intros w i d Hi.
  do 8 (destruct i as [|i]; [reflexivity|]). lia.
Qed.

Lemma flat_map_le8_nth : forall (l : list word) k i d dw, (k < length l)%nat -> (i < 8)%nat ->
  nth (8 * k + i) (flat_map word_le8 l) d = nth i (word_le8 (nth k l dw)) d.
Proof.
  induction l as [|w l IH]; intros k i d dw Hk Hi; cbn [length] in Hk; [lia|].
  cbn [flat_map]. destruct k as [|k].
  - cbn [nth Nat.mul Nat.add]. rewrite app_nth1 by (rewrite length_word_le8; lia). reflexivity.
  - rewrite app_nth2 by (rewrite length_word_le8; lia). rewrite length_word_le8.
    replace (8 * S k + i - 8)%nat with (8 * k + i)%nat by lia. cbn [nth]. apply IH; lia.
Qed.

(* The launch's entry block ([Run.entry_stack_image]) read off by offset.
   Linux's layout at LPS 08b1429: argc, the argv pointers, NULL, the envp
   pointers, NULL, the auxv (27 or 29 pairs, by [la_rseq]), the odd-item gap,
   the sixteen AT_RANDOM bytes, the [arch_align_stack] pad, the strings and
   the exec name, and the eight-byte slot under the stack VMA's end. *)
Lemma flat_pairs : forall es : list (word * word),
  flat_map (fun e : word * word => word_le8 (fst e) ++ word_le8 (snd e)) es
  = flat_map word_le8 (flat_map (fun e : word * word => [fst e; snd e]) es).
Proof.
  (* [word_le8] did NOT change at the revision (75d69e00
     theories/LinuxProcessSem/BvBase.v:66; [git diff f1006fe8 75d69e00 --
     theories/LinuxProcessSem/BvBase.v] is empty), so this is not a model
     repair: the old script's [app_assoc] had nothing left to match once
     [app_nil_r] had flattened the only right-nested append.  This is the
     model's own proof of the same equation,
     [Common.RefLayout.build_auxv_words] (75d69e00
     theories/Common/RefLayout.v:105-113), with the normalisation steps made
     optional so it holds whichever shape [cbn] leaves. *)
  induction es as [|[t v] es IH]; [reflexivity|].
  cbn [flat_map fst snd app]. rewrite IH, ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Section Entry.
Variables (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp brk0 mbase : word) (inp : ProcInput) (draw : EntryDraw).
Notation argv := (in_argv inp).
Notation envp := (in_envp inp).
Notation execfn := (in_execfn inp).
Notation uid := (in_uid inp).
Notation gid := (in_gid inp).
Notation hwcap := (in_hwcap inp).

Definition LA : LaunchAuxv := launch_auxv inp sp mbase.
Definition ENTRY : word := Z_to_bv 64 (Z.of_N pc).
Definition TOP : word := ed_top draw.
Definition nargc : nat := length argv.
Definition nenvc : nat := length envp.
Definition HEAD : nat := block_head_size (la_rseq LA) argv envp.
Definition LSB : nat := launch_string_bytes argv envp execfn.
Definition str_base : word := string_base_addr TOP argv envp execfn.
Definition argv_ptrs : list word := fst (string_addrs str_base argv).
Definition env_str_base : word := (str_base + nat_to_word (total_nat argv))%bv.
Definition envp_ptrs : list word := fst (string_addrs env_str_base envp).
Definition ARND : word := at_random_ptr sp (la_rseq LA) argv envp.
Definition AEXECFN : word := at_execfn_ptr TOP execfn.
Definition auxws : list word :=
  flat_map (fun e : word * word => [fst e; snd e]) (auxv_entries LA ph ENTRY uid gid hwcap ARND AEXECFN).
Definition AUXV : list byte := auxv_bytes LA ph ENTRY uid gid hwcap ARND AEXECFN.
Definition gap : nat := (8 * (block_items argv envp mod 2))%nat.
Definition pad : nat := block_pad_len (la_rseq LA) sp TOP argv envp execfn.
Definition BSB : list byte := build_stack_bytes LA ph ENTRY sp TOP argv envp execfn uid gid hwcap draw.
Definition IMG : list byte := entry_stack_image inp mbase ph ENTRY sp draw.
Definition mem0 : word -> option byte := ms_mem (init_machine_state segs pc ph sp mbase draw inp).
Definition SP : Z := bv_unsigned sp.
Definition WLO : Z := stack_window_lo (in_kernel inp) mbase draw.

Lemma LA_rseq : la_rseq LA = kb_rseq (in_kernel inp).
Proof. reflexivity. Qed.

Lemma AUXV_eq : AUXV = flat_map word_le8 auxws.
Proof. unfold AUXV, auxv_bytes, build_auxv, auxws. apply flat_pairs. Qed.

Lemma length_AUXV : length AUXV = auxv_size (la_rseq LA).
Proof. unfold AUXV. apply length_auxv_bytes. Qed.

Lemma length_auxws : length auxws = (2 * auxv_count (la_rseq LA))%nat.
Proof. unfold auxws, auxv_entries. destruct (la_rseq LA); reflexivity. Qed.

Theorem BSB_eq : BSB = word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0)
   ++ flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0) ++ AUXV ++ repeat (Z_to_bv 8 0) gap
   ++ at_random_bytes (ed_random draw) ++ repeat (Z_to_bv 8 0) pad
   ++ flatten_strings argv ++ flatten_strings envp ++ execfn ++ [Z_to_bv 8 0] ++ repeat (Z_to_bv 8 0) 8.
Proof.
  unfold BSB, build_stack_bytes. cbv zeta.
  rewrite (string_addrs_pair argv). cbv beta iota. rewrite (string_addrs_pair envp). cbv beta iota.
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma IMG_eq : IMG = BSB.
Proof. reflexivity. Qed.

Lemma length_argv_ptrs : length argv_ptrs = nargc.
Proof. unfold argv_ptrs. apply length_string_addrs_fst. Qed.
Lemma length_envp_ptrs : length envp_ptrs = nenvc.
Proof. unfold envp_ptrs. apply length_string_addrs_fst. Qed.

Lemma length_BSB : length BSB = (HEAD + pad + LSB + 8)%nat.
Proof. unfold BSB. rewrite length_build_stack_bytes. reflexivity. Qed.

Lemma HEAD_eq : Z.of_nat HEAD = 8 * Z.of_nat nargc + 8 * Z.of_nat nenvc + 24 + Z.of_nat (auxv_size (la_rseq LA)) + Z.of_nat gap + 16.
Proof. unfold HEAD, block_head_size, gap, block_items, nargc, nenvc. cbv zeta. lia. Qed.

Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hlaunch : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase draw) inp.

Lemma SP_lo : 0x7fff80000000 <= SP.
Proof. unfold SP. destruct Hsp as [H _]. unfold sp_window_lo in H. exact H. Qed.

Lemma geom : SP + Z.of_nat HEAD + Z.of_nat LSB + 8 <= bv_unsigned TOP.
Proof.
  pose proof Hlaunch as Hok. cbn [entry_launch_ok_va] in Hok. destruct Hok as (_ & (_ & _ & Hhi) & _).
  unfold launch_sp_hi, align_down16 in Hhi. unfold HEAD, LSB, SP, TOP. rewrite LA_rseq.
  pose proof (Z.mod_pos_bound
    (bv_unsigned (ed_top draw) - 8 - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp)))
    16 ltac:(lia)) as Hm.
  lia.
Qed.

Lemma top_hi : bv_unsigned TOP <= 0x800000000000.
Proof.
  pose proof Hlaunch as Hok. cbn [entry_launch_ok_va] in Hok. destruct Hok as ((_ & Ht & _) & _ & _).
  (* [valid_stack_top_va]'s bound is [va_stack_top Sv48] (75d69e00
     theories/LinuxProcessSem/Run.v:3612), and [va_stack_top] only REDUCES to
     [sp_window_hi] (75d69e00 theories/LinuxProcessSem/State.v:494-499), so the
     constant [sp_window_hi] does not occur in [Ht] and [unfold ... in Ht]
     had nothing to unfold.  Conversion settles it. *)
  unfold TOP. exact Ht.
Qed.

Lemma pad_eq : Z.of_nat pad = bv_unsigned TOP - 8 - Z.of_nat LSB - SP - Z.of_nat HEAD.
Proof. pose proof geom. unfold pad, block_pad_len. unfold HEAD, LSB, SP in *. rewrite Z2Nat.id by lia. lia. Qed.

Lemma BSB_end : SP + Z.of_nat (length BSB) = bv_unsigned TOP.
Proof. rewrite length_BSB. pose proof pad_eq. lia. Qed.

Lemma BSB_top : SP + Z.of_nat (length BSB) <= 0x800000000000.
Proof. rewrite BSB_end. exact top_hi. Qed.

Lemma mem0_unfold : forall addr, mem0 addr =
  match stack_to_mem sp IMG addr with
  | Some b => Some b
  | None => if (Z.leb WLO (bv_unsigned addr) && Z.ltb (bv_unsigned addr) SP)%bool then Some (Z_to_bv 8 0) else None
  end.
Proof. reflexivity. Qed.

Lemma mem0_block : forall (k : nat) b, nth_error BSB k = Some b -> mem0 (Z_to_bv 64 (SP + Z.of_nat k)) = Some b.
Proof.
  intros k b Hk.
  assert (Hlt : (k < length BSB)%nat) by (apply nth_error_Some; congruence).
  pose proof BSB_top as Htop. pose proof SP_lo as Hlo.
  rewrite mem0_unfold. unfold stack_to_mem. rewrite Z_to_bv64_unsigned by lia. fold SP.
  replace (SP <=? SP + Z.of_nat k) with true by (symmetry; apply Z.leb_le; lia).
  replace (SP + Z.of_nat k - SP) with (Z.of_nat k) by lia.
  rewrite IMG_eq.
  replace (Z.of_nat k <? Z.of_nat (length BSB)) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite Nat2Z.id, Hk. reflexivity.
Qed.

Lemma mem0_below : forall a, WLO <= a < SP -> mem0 (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Proof.
  intros a Ha. pose proof SP_lo as Hlo. pose proof (u64_range sp) as Hu. pose proof (u64_range mbase) as Hmb.
  pose proof (stack_guard_gap_bytes_bounds (in_kernel inp)) as [Hg0 Hg1].
  pose proof (Z.le_max_l (bv_unsigned (ed_top draw) - stack_max_size) (bv_unsigned mbase + stack_guard_gap_bytes (in_kernel inp))) as Hw.
  (* #38 widened [stack_window_lo] to the MAXIMUM of the 8 MiB window and the
     mmap base plus the guard gap; only the right arm bounds the window below
     by a nonnegative address, so [Z.le_max_r] is what gives [0 <= a]. *)
  pose proof (Z.le_max_r (bv_unsigned (ed_top draw) - stack_max_size) (bv_unsigned mbase + stack_guard_gap_bytes (in_kernel inp))) as Hwr.
  rewrite mem0_unfold. unfold SP, WLO, stack_window_lo, stack_max_size, stack_to_mem in *.
  rewrite Z_to_bv64_unsigned by lia.
  replace (bv_unsigned sp <=? a) with false by (symmetry; apply Z.leb_gt; lia).
  replace (Z.max (bv_unsigned (ed_top draw) - 8 * 1024 * 1024) (bv_unsigned mbase + stack_guard_gap_bytes (in_kernel inp)) <=? a) with true by (symmetry; apply Z.leb_le; lia).
  replace (a <? bv_unsigned sp) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma mem0_none_low : forall a, 0 <= a < WLO -> a < SP -> mem0 (Z_to_bv 64 a) = None.
Proof.
  intros a Ha Hs. pose proof (u64_range sp) as Hu. rewrite mem0_unfold. unfold SP, WLO, stack_to_mem in *.
  rewrite Z_to_bv64_unsigned by lia.
  replace (bv_unsigned sp <=? a) with false by (symmetry; apply Z.leb_gt; lia).
  replace (stack_window_lo (in_kernel inp) mbase draw <=? a) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.

Lemma mem0_piece : forall pre mid post (i : nat),
  BSB = pre ++ mid ++ post -> (i < length mid)%nat ->
  mem0 (Z_to_bv 64 (SP + Z.of_nat (length pre) + Z.of_nat i)) = Some (nth i mid (Z_to_bv 8 0)).
Proof.
  intros pre mid post i HB Hi.
  replace (SP + Z.of_nat (length pre) + Z.of_nat i) with (SP + Z.of_nat (length pre + i)) by lia.
  apply mem0_block. rewrite HB. rewrite nth_error_app2 by lia.
  replace (length pre + i - length pre)%nat with i by lia.
  rewrite nth_error_app1 by exact Hi. apply nth_error_nth'. exact Hi.
Qed.

Definition argcZ : Z := Z.of_nat nargc.
Definition envcZ : Z := Z.of_nat nenvc.

Lemma argc_range : 1 <= argcZ <= 1024.
Proof. unfold argcZ, nargc. destruct Hva as [H _]. exact H. Qed.
Lemma envc_range : 0 <= envcZ <= 256.
Proof. unfold envcZ, nenvc. destruct Hve as [H _]. lia. Qed.

Definition word_at (A : Z) (w : word) : Prop :=
  forall i : nat, (i < 8)%nat -> mem0 (Z_to_bv 64 (A + Z.of_nat i)) = Some (nth i (word_le8 w) (Z_to_bv 8 0)).

Lemma word_at_piece : forall pre w post,
  BSB = pre ++ word_le8 w ++ post -> word_at (SP + Z.of_nat (length pre)) w.
Proof. intros pre w post HB i Hi. apply (mem0_piece pre (word_le8 w) post i HB). rewrite length_word_le8. exact Hi. Qed.

Lemma words_at_piece : forall pre (l : list word) post k d,
  BSB = pre ++ flat_map word_le8 l ++ post -> (k < length l)%nat ->
  word_at (SP + Z.of_nat (length pre) + 8 * Z.of_nat k) (nth k l d).
Proof.
  intros pre l post k d HB Hk i Hi.
  replace (SP + Z.of_nat (length pre) + 8 * Z.of_nat k + Z.of_nat i) with (SP + Z.of_nat (length pre) + Z.of_nat (8 * k + i)) by lia.
  rewrite (mem0_piece pre (flat_map word_le8 l) post (8 * k + i) HB) by (rewrite length_flat_map_le8; lia).
  f_equal. apply flat_map_le8_nth; assumption.
Qed.

Lemma argc_word : word_at SP (len_word argv).
Proof.
  replace SP with (SP + Z.of_nat (@length byte [])) by (cbn; lia).
  eapply (word_at_piece []). rewrite BSB_eq. reflexivity.
Qed.

Lemma len_word_argv : bv_unsigned (len_word argv) = argcZ.
Proof. unfold len_word, argcZ, nargc. apply Z_to_bv64_unsigned. pose proof argc_range. unfold argcZ, nargc in *. lia. Qed.

Lemma argv_ptr_word : forall k, (k < nargc)%nat -> word_at (SP + 8 + 8 * Z.of_nat k) (nth k argv_ptrs (Z_to_bv 64 0)).
Proof.
  intros k Hk.
  replace (SP + 8) with (SP + Z.of_nat (length (word_le8 (len_word argv)))) by (rewrite length_word_le8; lia).
  eapply words_at_piece; [|rewrite length_argv_ptrs; exact Hk].
  rewrite BSB_eq. reflexivity.
Qed.

Lemma argv_cons : exists a0 rest, argv = a0 :: rest.
Proof.
  pose proof argc_range as H. unfold argcZ, nargc in H. clear -H.
  destruct (in_argv inp) as [|a0 rest]; [cbn in H; lia | exists a0, rest; reflexivity].
Qed.

Lemma argv_ptr0 : forall a0 rest, argv = a0 :: rest -> nth 0 argv_ptrs (Z_to_bv 64 0) = str_base.
Proof.
  intros a0 rest Ha. unfold argv_ptrs. rewrite string_addrs_fst. rewrite Ha. reflexivity.
Qed.

Lemma LSB_eq : Z.of_nat LSB = Z.of_nat (total_nat argv) + Z.of_nat (total_nat envp) + Z.of_nat (length execfn) + 1.
Proof. unfold LSB, launch_string_bytes. rewrite !length_flatten_strings. lia. Qed.

Lemma str_base_val : bv_unsigned str_base = SP + Z.of_nat (HEAD + pad).
Proof.
  pose proof geom as G. pose proof pad_eq as P. pose proof (u64_range (ed_top draw)) as UT. pose proof SP_lo.
  unfold str_base, string_base_addr, nat_to_word, TOP in *.
  rewrite bv_sub_unsigned, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  rewrite (Z.mod_small (Z.of_nat (8 + LSB))) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Definition envp_off : Z := 16 + 8 * argcZ.

Lemma envp_block : BSB = (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0))
                         ++ (flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0))
                         ++ (AUXV ++ repeat (Z_to_bv 8 0) gap ++ at_random_bytes (ed_random draw) ++ repeat (Z_to_bv 8 0) pad
                             ++ flatten_strings argv ++ flatten_strings envp ++ execfn ++ [Z_to_bv 8 0] ++ repeat (Z_to_bv 8 0) 8).
Proof. rewrite BSB_eq. repeat rewrite app_assoc. reflexivity. Qed.

Lemma envp_off_eq : Z.of_nat (length (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0))) = envp_off.
Proof. rewrite !length_app, !length_word_le8, length_flat_map_le8, length_argv_ptrs. unfold envp_off, argcZ. lia. Qed.

Definition envp_img : list byte := flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0).

Lemma length_envp_img : length envp_img = Z.to_nat (8 * envcZ + 8).
Proof. unfold envp_img. rewrite length_app, length_flat_map_le8, length_word_le8, length_envp_ptrs. unfold envcZ. lia. Qed.

Lemma envp_img_byte : forall i : nat, (i < length envp_img)%nat ->
  mem0 (Z_to_bv 64 (SP + envp_off + Z.of_nat i)) = Some (nth i envp_img (Z_to_bv 8 0)).
Proof.
  intros i Hi. rewrite <- envp_off_eq. apply (mem0_piece _ envp_img _ i envp_block Hi).
Qed.

Lemma env_str_base_val : bv_unsigned env_str_base = bv_unsigned str_base + Z.of_nat (total_nat argv).
Proof.
  pose proof geom as G. pose proof pad_eq as P. pose proof LSB_eq as L. pose proof str_base_val as S. pose proof (u64_range (ed_top draw)).
  unfold env_str_base. apply nat_to_word_add. unfold TOP in *. lia.
Qed.

Lemma envp_ptr_val : forall k, (k < nenvc)%nat ->
  SP < bv_unsigned (nth k envp_ptrs (Z_to_bv 64 0)) < 2 ^ 64.
Proof.
  assert (G : forall strs (base : word) k, (k < length strs)%nat ->
            bv_unsigned base + Z.of_nat (total_nat strs) < 2 ^ 64 ->
            bv_unsigned base <= bv_unsigned (nth k (fst (string_addrs base strs)) (Z_to_bv 64 0)) < 2 ^ 64).
  { induction strs as [|s rest IH]; intros base k Hk Hnw; cbn [length] in Hk; [lia|].
    rewrite string_addrs_fst. destruct k as [|k].
    - cbn [nth]. pose proof (u64_range base). lia.
    - cbn [nth]. cbn [total_nat] in Hnw.
      assert (Hb : bv_unsigned (base + len_word s + 1)%bv = bv_unsigned base + Z.of_nat (length s) + 1).
      { rewrite len_word_nat, word1_nat, nat_to_word_add_merge. rewrite nat_to_word_add; [lia|]. lia. }
      specialize (IH (base + len_word s + 1)%bv k ltac:(lia)). rewrite Hb in IH. lia. }
  intros k Hk. unfold envp_ptrs.
  pose proof geom as Gm. pose proof pad_eq as P. pose proof LSB_eq as L. pose proof str_base_val as S.
  pose proof env_str_base_val as Hev. pose proof HEAD_eq as HE. pose proof (u64_range (ed_top draw)).
  specialize (G envp env_str_base k Hk ltac:(rewrite Hev; unfold TOP in *; lia)). rewrite Hev in G.
  unfold TOP in *. lia.
Qed.

Definition auxv_off : Z := 24 + 8 * argcZ + 8 * envcZ.

Lemma auxv_block : BSB = (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0)
                          ++ flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0))
                         ++ flat_map word_le8 auxws
                         ++ (repeat (Z_to_bv 8 0) gap ++ at_random_bytes (ed_random draw) ++ repeat (Z_to_bv 8 0) pad
                             ++ flatten_strings argv ++ flatten_strings envp ++ execfn ++ [Z_to_bv 8 0] ++ repeat (Z_to_bv 8 0) 8).
Proof. rewrite BSB_eq, AUXV_eq. repeat rewrite app_assoc. reflexivity. Qed.

Lemma auxv_word : forall j, (j < length auxws)%nat -> word_at (SP + auxv_off + 8 * Z.of_nat j) (nth j auxws (Z_to_bv 64 0)).
Proof.
  intros j Hj.
  replace (SP + auxv_off) with (SP + Z.of_nat (length (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0)
                          ++ flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0)))).
  2:{ rewrite !length_app, !length_word_le8, !length_flat_map_le8, length_argv_ptrs, length_envp_ptrs. unfold auxv_off, argcZ, envcZ. lia. }
  eapply words_at_piece; [exact auxv_block| exact Hj].
Qed.

Lemma ARND_val : bv_unsigned ARND = SP + Z.of_nat HEAD - 16.
Proof.
  pose proof geom as G. pose proof HEAD_eq as HE. pose proof (u64_range (ed_top draw)).
  (* [SP] is [bv_unsigned sp] by definition, but [lia] is syntactic on atoms:
     [geom] speaks of [SP] and the side condition of [bv_unsigned sp], so the
     two have to be spelled the same before [lia] sees them. *)
  unfold ARND, at_random_ptr. fold HEAD.
  rewrite nat_to_word_add by (unfold TOP, SP in *; lia). fold SP. lia.
Qed.

Lemma random_block :
  BSB = (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0)
         ++ flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0) ++ AUXV ++ repeat (Z_to_bv 8 0) gap)
        ++ at_random_bytes (ed_random draw)
        ++ (repeat (Z_to_bv 8 0) pad ++ flatten_strings argv ++ flatten_strings envp ++ execfn ++ [Z_to_bv 8 0] ++ repeat (Z_to_bv 8 0) 8).
Proof. rewrite BSB_eq. repeat rewrite app_assoc. reflexivity. Qed.

Lemma random_byte : forall i : nat, (i < 16)%nat ->
  mem0 (Z_to_bv 64 (SP + (Z.of_nat HEAD - 16) + Z.of_nat i)) = Some (nth i (at_random_bytes (ed_random draw)) (Z_to_bv 8 0)).
Proof.
  intros i Hi.
  replace (SP + (Z.of_nat HEAD - 16)) with (SP + Z.of_nat (length (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0)
         ++ flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0) ++ AUXV ++ repeat (Z_to_bv 8 0) gap))).
  2:{ rewrite !length_app, !length_word_le8, !length_flat_map_le8, length_argv_ptrs, length_envp_ptrs, length_AUXV, repeat_length.
      pose proof HEAD_eq. lia. }
  apply (mem0_piece _ (at_random_bytes (ed_random draw)) _ i random_block). rewrite length_at_random_bytes. exact Hi.
Qed.

Lemma argv_null_block : BSB = (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs) ++ word_le8 (Z_to_bv 64 0)
        ++ (flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0) ++ AUXV ++ repeat (Z_to_bv 8 0) gap
            ++ at_random_bytes (ed_random draw) ++ repeat (Z_to_bv 8 0) pad
            ++ flatten_strings argv ++ flatten_strings envp ++ execfn ++ [Z_to_bv 8 0] ++ repeat (Z_to_bv 8 0) 8).
Proof. rewrite BSB_eq. repeat rewrite app_assoc. reflexivity. Qed.

Lemma argv_null_word : word_at (SP + 8 + 8 * argcZ) (Z_to_bv 64 0).
Proof.
  replace (SP + 8 + 8 * argcZ) with (SP + Z.of_nat (length (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs))).
  2:{ rewrite length_app, length_word_le8, length_flat_map_le8, length_argv_ptrs. unfold argcZ. lia. }
  exact (word_at_piece _ _ _ argv_null_block).
Qed.

(* The strings, the exec name, its NUL and the eight-byte slot: [str_base] up to the stack VMA's end. *)
Definition strarea : list byte := flatten_strings argv ++ flatten_strings envp ++ execfn ++ [Z_to_bv 8 0] ++ repeat (Z_to_bv 8 0) 8.
Lemma length_strarea : length strarea = (LSB + 8)%nat.
Proof. unfold strarea, LSB, launch_string_bytes. rewrite !length_app, repeat_length. cbn [length]. lia. Qed.

Lemma strarea_block :
  BSB = (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0)
         ++ flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0) ++ AUXV ++ repeat (Z_to_bv 8 0) gap
         ++ at_random_bytes (ed_random draw) ++ repeat (Z_to_bv 8 0) pad)
        ++ strarea ++ [].
Proof. rewrite BSB_eq. unfold strarea. rewrite app_nil_r. repeat rewrite app_assoc. reflexivity. Qed.

Lemma strarea_byte : forall i : nat, (i < length strarea)%nat ->
  mem0 (Z_to_bv 64 (bv_unsigned str_base + Z.of_nat i)) = Some (nth i strarea (Z_to_bv 8 0)).
Proof.
  intros i Hi. rewrite str_base_val.
  replace (SP + Z.of_nat (HEAD + pad)) with (SP + Z.of_nat (length (word_le8 (len_word argv) ++ flat_map word_le8 argv_ptrs ++ word_le8 (Z_to_bv 64 0)
         ++ flat_map word_le8 envp_ptrs ++ word_le8 (Z_to_bv 64 0) ++ AUXV ++ repeat (Z_to_bv 8 0) gap
         ++ at_random_bytes (ed_random draw) ++ repeat (Z_to_bv 8 0) pad))).
  2:{ rewrite !length_app, !length_word_le8, !length_flat_map_le8, length_argv_ptrs, length_envp_ptrs, length_AUXV,
        !repeat_length, length_at_random_bytes. pose proof HEAD_eq. lia. }
  apply (mem0_piece _ strarea _ i strarea_block). exact Hi.
Qed.

Lemma argv0_byte : forall a0 rest (i : nat), argv = a0 :: rest -> (i <= length a0)%nat ->
  mem0 (Z_to_bv 64 (bv_unsigned str_base + Z.of_nat i)) = Some (nth i (a0 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)).
Proof.
  intros a0 rest i Ha Hi.
  assert (E : strarea = (a0 ++ [Z_to_bv 8 0]) ++ (flatten_strings rest ++ flatten_strings envp ++ execfn ++ [Z_to_bv 8 0] ++ repeat (Z_to_bv 8 0) 8)).
  { unfold strarea. rewrite Ha. unfold flatten_strings at 1. cbn [flat_map]. rewrite <- app_assoc. reflexivity. }
  rewrite strarea_byte by (rewrite E, length_app, length_app; cbn [length]; lia).
  rewrite E. rewrite app_nth1 by (rewrite length_app; cbn [length]; lia). reflexivity.
Qed.

Lemma argv_ptr1 : forall a0 a1 rest, argv = a0 :: a1 :: rest ->
  nth 1 argv_ptrs (Z_to_bv 64 0) = (str_base + len_word a0 + 1)%bv.
Proof.
  intros a0 a1 rest Ha. unfold argv_ptrs. rewrite Ha. cbn [string_addrs].
  destruct (string_addrs (str_base + len_word a0 + 1 + len_word a1 + 1)%bv rest). reflexivity.
Qed.

Lemma argv_ptr1_val : forall a0 a1 rest, argv = a0 :: a1 :: rest ->
  bv_unsigned (nth 1 argv_ptrs (Z_to_bv 64 0)) = bv_unsigned str_base + Z.of_nat (length a0) + 1.
Proof.
  intros a0 a1 rest Ha. rewrite (argv_ptr1 a0 a1 rest Ha). rewrite len_word_nat, word1_nat, nat_to_word_add_merge.
  pose proof geom as G. pose proof pad_eq as P. pose proof LSB_eq as L. pose proof str_base_val as S. pose proof (u64_range (ed_top draw)).
  assert (HA : (length a0 + 1 <= total_nat argv)%nat) by (rewrite Ha; cbn [total_nat]; lia).
  rewrite nat_to_word_add; [lia|]. unfold TOP in *. lia.
Qed.

End Entry.

End SI.
