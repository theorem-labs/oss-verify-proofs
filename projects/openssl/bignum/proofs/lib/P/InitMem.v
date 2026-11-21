(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch input ProcInput, the CONFIG_RSEQ flag, the new auxv layout, the init stack window and head_size_ge stated outside the section so that it takes the launch input only); and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec Tac Arr Bytes.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma extract_byte_eq : forall (v : word) (k : N),
  bv_extract k 8 v = Z_to_bv 8 (Z.shiftr (bv_unsigned v) (Z.of_N k)).
Proof. intros v k. apply bv_eq. rewrite bv_extract_unsigned, Z_to_bv_unsigned. reflexivity. Qed.

Lemma word_le8_le8 : forall v : word, word_le8 v = le8 v.
Proof.
  intros v. unfold word_le8, le8, word_to_le_bytes. cbn [Z_to_le_bytes].
  rewrite !extract_byte_eq. rewrite !Z.shiftr_shiftr by lia. cbn [Z.of_N Z.add].
  rewrite Z.shiftr_0_r. reflexivity.
Qed.

Lemma flat_map_word_le8 : forall ws, flat_map word_le8 ws = u64s ws.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [flat_map u64s]. rewrite word_le8_le8, IH. reflexivity. Qed.

Lemma bv_extract_extract : forall n (v : bv n) (s1 l1 s2 l2 : N), (s1 + l1 <= l2)%N ->
  bv_extract s1 l1 (bv_extract s2 l2 v) = bv_extract (s1 + s2) l1 v.
Proof.
  intros n v s1 l1 s2 l2 H. apply bv_eq. rewrite !bv_extract_unsigned. unfold bv_wrap, bv_modulus.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i (Z.of_N l1)).
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
    rewrite Z.mod_pow2_bits_low by lia. rewrite Z.shiftr_spec by lia. f_equal. lia.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma at_random_bytes_split : forall r : bv 128,
  at_random_bytes r = le8 (bv_extract 0 64 r) ++ le8 (bv_extract 64 64 r).
Proof.
  intros r. rewrite <- (word_le8_le8 (bv_extract 0 64 r)), <- (word_le8_le8 (bv_extract 64 64 r)).
  unfold at_random_bytes, word_le8. cbn [app].
  rewrite !bv_extract_extract by lia. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

Fixpoint rw_bytes_b (A : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' =>
      match seg_rom segs (wa A), wview segs (fun _ => None) (wa A) with
      | Some b', Some _ => bv_eqb b b' && rw_bytes_b (A + 1) bs'
      | _, _ => false
      end
  end.

Lemma rw_bytes_b_sound : forall bs A (m : word -> option byte),
  rw_bytes_b A bs = true ->
  (forall a : word, (A <= bv_unsigned a < A + Z.of_nat (length bs))%Z -> m a = None) ->
  (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z ->
  forall i b, nth_error bs i = Some b ->
    mrd segs m (wa (A + Z.of_nat i)) = Some b /\ wview segs m (wa (A + Z.of_nat i)) <> None.
Proof.
  induction bs as [|b0 bs IH]; intros A m Hb Hm HA Hl i b Hn; [destruct i; discriminate|].
  cbn [rw_bytes_b] in Hb.
  destruct (seg_rom segs (wa A)) as [b'|] eqn:Er; [|discriminate].
  destruct (wview segs (fun _ => None) (wa A)) as [bw|] eqn:Ew; [|discriminate].
  apply andb_prop in Hb. destruct Hb as [Hbe Hb]. unfold bv_eqb in Hbe. apply Z.eqb_eq in Hbe. apply bv_eq in Hbe. subst b'.
  cbn [length] in Hl, Hm.
  destruct i as [|i].
  - cbn in Hn. injection Hn as ->. rewrite Z.add_0_r.
    assert (Hnone : m (wa A) = None). { apply Hm. rewrite wa_unsigned by lia. lia. }
    split. { unfold mrd. rewrite Hnone. exact Er. }
    unfold wview in *. rewrite Hnone. intros C. rewrite C in Ew. discriminate.
  - cbn in Hn. replace (A + Z.of_nat (S i))%Z with ((A + 1) + Z.of_nat i)%Z by lia.
    apply (IH (A + 1)%Z m Hb); try lia; [|exact Hn]. intros a Ha. apply Hm. lia.
Qed.

Lemma rw_cells_image0 : forall (m : word -> option byte) A bs,
  (forall a : word, (A <= bv_unsigned a < A + Z.of_nat (length bs))%Z -> m a = None) ->
  rw_bytes_b A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z ->
  rw_cells segs m A [CB (length bs) bs].
Proof.
  intros m A bs Hm Hb HA Hl. pose proof (rw_bytes_b_sound bs A m Hb Hm HA Hl) as G.
  split; [split|].
  - cbn. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [lia|].
    intros i Hi. destruct (nth_error bs i) as [b|] eqn:E. { apply (proj1 (G i b E)). } apply nth_error_None in E. lia.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E. { apply (proj2 (G _ b E)). } apply nth_error_None in E. lia.
Qed.

Lemma rw_cells_recast : forall m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells segs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* The entry stack at LPS 08b1429: the image IS Linux's block, from sp up to
   the stack VMA's end [ed_top]; below sp the window [Run.stack_window_lo, sp)
   reads zero. *)
Section Init.
  Variables (inp : ProcInput) (mbase : word) (ph : PhdrInfo) (entry sp : word) (draw : EntryDraw).
  Local Notation m0 := (wrap_mem inp mbase ph entry sp draw).
  Local Notation img := (entry_stack_image inp mbase ph entry sp draw).
  Local Notation WLO := (stack_window_lo (in_kernel inp) mbase draw).

  Lemma init_at : forall a : word,
    m0 a = if (Z.leb (bv_unsigned sp) (bv_unsigned a)) then
             (if Z.ltb (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length img))
              then nth_error img (Z.to_nat (bv_unsigned a - bv_unsigned sp)) else None)
           else if Z.leb WLO (bv_unsigned a) then Some (Z_to_bv 8 0) else None.
  Proof using inp mbase ph entry sp draw.
    intros a. unfold wrap_mem, stack_to_mem.
    destruct (Z.leb_spec0 (bv_unsigned sp) (bv_unsigned a)).
    - destruct (Z.ltb_spec0 (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length img))).
      + destruct (nth_error img (Z.to_nat (bv_unsigned a - bv_unsigned sp))) eqn:E; [reflexivity|].
        apply nth_error_None in E. lia.
      + replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with false by (symmetry; apply Z.ltb_ge; lia).
        rewrite andb_false_r. reflexivity.
    - replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite andb_true_r. reflexivity.
  Qed.

  Lemma init_at_block : forall a : word,
    (bv_unsigned sp <= bv_unsigned a < bv_unsigned sp + Z.of_nat (length img))%Z ->
    m0 a = nth_error img (Z.to_nat (bv_unsigned a - bv_unsigned sp)).
  Proof using inp mbase ph entry sp draw.
    intros a Ha. rewrite init_at.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length img))) with true by (symmetry; apply Z.ltb_lt; lia).
    reflexivity.
  Qed.

  Lemma init_none_above : forall a : word, (bv_unsigned sp + Z.of_nat (length img) <= bv_unsigned a)%Z -> m0 a = None.
  Proof using inp mbase ph entry sp draw.
    intros a Ha. rewrite init_at.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length img))) with false by (symmetry; apply Z.ltb_ge; lia).
    reflexivity.
  Qed.

  (* [comment removed for export] *)
  Hypothesis WLE : (WLO <= bv_unsigned sp)%Z.

  Lemma init_none : forall a : word, (bv_unsigned a < WLO)%Z -> m0 a = None.
  Proof using inp mbase ph entry sp draw WLE.
    intros a Ha. rewrite init_at.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia).
    replace (Z.leb WLO (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia).
    reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma init_stk : forall lo, (0 <= lo)%Z -> (WLO <= lo)%Z -> stk segs m0 lo (bv_unsigned sp).
  Proof using inp mbase ph entry sp draw.
    intros lo Hlo0 Hlo.
    pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
    split; [lia|]. split; [lia|]. intros a Ha.
    assert (E : m0 (wa a) = Some (Z_to_bv 8 0)).
    { rewrite init_at, wa_unsigned by lia.
      replace (Z.leb (bv_unsigned sp) a) with false by (symmetry; apply Z.leb_gt; lia).
      replace (Z.leb WLO a) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
    split. { unfold wview. rewrite E. discriminate. } exists (Z_to_bv 8 0). unfold mrd. rewrite E. reflexivity.
  Qed.

  Hypothesis IMGHI : (bv_unsigned sp + Z.of_nat (length img) <= 2^64)%Z.

  (* [comment removed for export] *)
  Lemma init_stack_bytes : bytes_at segs m0 (bv_unsigned sp) img.
  Proof using inp mbase ph entry sp draw IMGHI.
    pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
    split; [lia|]. split; [lia|]. intros i Hi. unfold mrd.
    assert (EA : bv_unsigned (wa (bv_unsigned sp + Z.of_nat i)) = (bv_unsigned sp + Z.of_nat i)%Z) by (apply wa_unsigned; lia).
    rewrite init_at_block by (rewrite EA; lia). rewrite EA.
    replace (Z.to_nat (bv_unsigned sp + Z.of_nat i - bv_unsigned sp)) with i by lia.
    destruct (nth_error img i) eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
  Qed.

  Lemma init_stack_wr : wr_at segs m0 (bv_unsigned sp) (Z.of_nat (length img)).
  Proof using inp mbase ph entry sp draw IMGHI.
    pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
    split; [lia|]. split; [lia|]. intros i Hi. unfold wview.
    assert (EA : bv_unsigned (wa (bv_unsigned sp + i)) = (bv_unsigned sp + i)%Z) by (apply wa_unsigned; lia).
    rewrite init_at_block by (rewrite EA; lia). rewrite EA.
    destruct (nth_error img (Z.to_nat (bv_unsigned sp + i - bv_unsigned sp))) eqn:E; [discriminate|].
    apply nth_error_None in E. lia.
  Qed.

  Lemma init_stack_u8arr : u8arr segs m0 (bv_unsigned sp) img.
  Proof using inp mbase ph entry sp draw IMGHI. split; [apply init_stack_bytes | apply init_stack_wr]. Qed.

  (* [comment removed for export] *)
  Hypothesis SEGS_LOW : forall a : word, (WLO <= bv_unsigned a)%Z -> find_segment segs (bv_unsigned a) 1 = None.
  Hypothesis IMGTOP : (bv_unsigned sp + Z.of_nat (length img) <= UTOP)%Z.
  Lemma init_mem_inv : mem_inv segs m0.
  Proof using inp mbase ph entry sp draw WLE SEGS_LOW IMGTOP.
    apply mem_inv_intro.
    - intros a Hs. unfold seg_addr in Hs.
      destruct (Z.lt_ge_cases (bv_unsigned a) WLO) as [Hl|Hh].
      + pose proof (Nat2Z.is_nonneg (length img)). lia.
      + rewrite SEGS_LOW in Hs by lia. discriminate.
    - intros a b H. unfold ro_addr.
      destruct (Z.lt_ge_cases (bv_unsigned a) WLO) as [Hl|Hh].
      + rewrite init_none in H by lia. discriminate.
      + rewrite SEGS_LOW by lia. split; [reflexivity|].
        destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned sp + Z.of_nat (length img))) as [Hl'|Hh']; [lia|].
        rewrite init_none_above in H by lia. discriminate.
  Qed.
End Init.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint str_ptrs (base : Z) (strs : list (list byte)) : list Z :=
  match strs with
  | [] => []
  | s :: rest => base :: str_ptrs (base + Z.of_nat (length s) + 1)%Z rest
  end.

Lemma str_ptrs_length : forall strs base, length (str_ptrs base strs) = length strs.
Proof. induction strs; intros; cbn; [reflexivity|]. now rewrite IHstrs. Qed.

Lemma total_arg_bytes_cons : forall s0 strs, total_arg_bytes (s0 :: strs) = (Z.of_nat (length s0) + 1 + total_arg_bytes strs)%Z.
Proof. reflexivity. Qed.
Lemma total_arg_bytes_nil : total_arg_bytes [] = 0%Z.
Proof. reflexivity. Qed.

Lemma total_arg_bytes_nonneg : forall strs, (0 <= total_arg_bytes strs)%Z.
Proof. induction strs; [rewrite total_arg_bytes_nil | rewrite total_arg_bytes_cons]; lia. Qed.

Lemma flatten_strings_length : forall strs, Z.of_nat (length (flatten_strings strs)) = total_arg_bytes strs.
Proof.
  induction strs as [|s0 strs IH]; [reflexivity|]. rewrite total_arg_bytes_cons. unfold flatten_strings in *. cbn [flat_map].
  rewrite app_length, app_length. cbn [length]. lia.
Qed.

Lemma string_addrs_eq : forall strs base,
  string_addrs (Z_to_bv 64 base) strs = (map (Z_to_bv 64) (str_ptrs base strs), Z_to_bv 64 (base + total_arg_bytes strs)%Z).
Proof.
  induction strs as [|s0 strs IH]; intros base; cbn [string_addrs str_ptrs map].
  - rewrite total_arg_bytes_nil, Z.add_0_r. reflexivity.
  - unfold len_word. rewrite !lit_add_lit.
    change (Z_to_bv 64 (base + Z.of_nat (length s0))) with (wa (base + Z.of_nat (length s0))). rewrite wa_succ. unfold wa.
    rewrite IH. cbn [fst snd]. f_equal. f_equal. rewrite total_arg_bytes_cons. lia.
Qed.

Lemma str_ptrs_nth : forall strs base i s, nth_error strs i = Some s ->
  exists off, nth_error (str_ptrs base strs) i = Some (base + off)%Z /\
    (0 <= off)%Z /\ (off + Z.of_nat (length s) + 1 <= total_arg_bytes strs)%Z /\
    firstn (length s + 1) (skipn (Z.to_nat off) (flatten_strings strs)) = s ++ [Z_to_bv 8 0].
Proof.
  induction strs as [|s0 strs IH]; intros base [|i] s Hn; cbn in Hn; try discriminate.
  - injection Hn as ->. exists 0%Z. cbn [str_ptrs nth_error]. rewrite Z.add_0_r. split; [reflexivity|].
    split; [lia|]. split. { rewrite total_arg_bytes_cons. pose proof (total_arg_bytes_nonneg strs). lia. }
    unfold flatten_strings. change (Z.to_nat 0) with 0%nat. rewrite skipn_O. cbn [flat_map].
    rewrite firstn_app. rewrite (@firstn_all2 _ (length s + 1) (s ++ [Z_to_bv 8 0])) by (rewrite app_length; cbn; lia).
    rewrite app_length. cbn [length]. replace (length s + 1 - (length s + 1))%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
  - destruct (IH (base + Z.of_nat (length s0) + 1)%Z i s Hn) as (off & Hp & Ho & Ht & Hf).
    exists (Z.of_nat (length s0) + 1 + off)%Z. cbn [str_ptrs nth_error].
    split. { rewrite Hp. f_equal. lia. } split; [lia|]. split. { rewrite total_arg_bytes_cons. lia. }
    unfold flatten_strings. cbn [flat_map]. rewrite skipn_app, app_length. cbn [length].
    replace (Z.to_nat (Z.of_nat (length s0) + 1 + off) - (length s0 + 1))%nat with (Z.to_nat off) by lia.
    rewrite skipn_all2 by (rewrite app_length; cbn; lia). cbn [app]. exact Hf.
Qed.


Lemma wr_at_sub : forall m a n a' n', wr_at segs m a n -> (a <= a')%Z -> (a' + n' <= a + n)%Z -> wr_at segs m a' n'.
Proof.
  intros m a n a' n' (Ha & Hn & H) H1 H2. split; [lia|]. split; [lia|].
  intros i Hi. replace (a' + i)%Z with (a + (a' - a + i))%Z by lia. apply H. lia.
Qed.

Lemma rw_cells_of_parts : forall m A cs,
  cells_wf cs -> bytes_at segs m A (cells_bytes cs) -> wr_at segs m A (Z.of_nat (cells_size cs)) -> rw_cells segs m A cs.
Proof. intros m A cs Hwf Hb Hw. split; [split; assumption| exact Hw]. Qed.

Lemma bytes_at_slice : forall m a bs off k,
  bytes_at segs m a bs -> (off + k <= length bs)%nat ->
  bytes_at segs m (a + Z.of_nat off) (firstn k (skipn off bs)).
Proof.
  intros m a bs off k H Hk.
  rewrite <- (firstn_skipn off bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length in H. replace (Nat.min off (length bs)) with off in H by lia.
  rewrite <- (firstn_skipn k (skipn off bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma str_ptrs_bounds : forall strs base i p, nth_error (str_ptrs base strs) i = Some p ->
  (base <= p /\ p < base + total_arg_bytes strs)%Z.
Proof.
  induction strs as [|s0 strs IH]; intros base [|i] p Hn; cbn in Hn; try discriminate.
  - injection Hn as <-. rewrite total_arg_bytes_cons. pose proof (total_arg_bytes_nonneg strs). lia.
  - apply IH in Hn. rewrite total_arg_bytes_cons. lia.
Qed.

(* [comment removed for export] *)
Lemma auxv_bytes_words : forall la ph entry uid gid hw ar ae,
  auxv_bytes la ph entry uid gid hw ar ae
  = u64s (flat_map (fun e => [fst e; snd e]) (auxv_entries la ph entry uid gid hw ar ae)).
Proof.
  intros. unfold auxv_bytes, build_auxv.
  generalize (auxv_entries la ph entry uid gid hw ar ae) as es.
  induction es as [|[t v] es IH]; [reflexivity|].
  cbn [flat_map fst snd app u64s]. rewrite IH, !word_le8_le8, <- app_assoc. reflexivity.
Qed.

Section Layout.
  (* [comment removed for export] *)
  Variables (inp : ProcInput) (mbase : word) (ph : PhdrInfo) (entry sp : word) (draw : EntryDraw).
  Local Notation usp := (bv_unsigned sp).
  Local Notation argv := (in_argv inp).
  Local Notation envp := (in_envp inp).
  Local Notation execfn := (in_execfn inp).
  Local Notation top := (ed_top draw).
  Local Notation m0 := (wrap_mem inp mbase ph entry sp draw).
  Local Notation img := (entry_stack_image inp mbase ph entry sp draw).

  Definition argc : Z := Z.of_nat (length (in_argv inp)).
  Definition envc : Z := Z.of_nat (length (in_envp inp)).
  (* Size of the block's head: argc, the two pointer arrays, the auxv, the alignment gap, AT_RANDOM. *)
  Definition head_size : Z := Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)).
  (* The strings at the block's top: argv, envp, the exec file name and its NUL. *)
  Definition str_len : Z := Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp)).
  Definition str_base : Z := (bv_unsigned (ed_top draw) - 8 - str_len)%Z.
  Definition argv_ptrs : list word := map (Z_to_bv 64) (str_ptrs str_base (in_argv inp)).
  Definition env_base : Z := (str_base + total_arg_bytes (in_argv inp))%Z.
  Definition envp_ptrs : list word := map (Z_to_bv 64) (str_ptrs env_base (in_envp inp)).
  Definition execfn_addr : Z := (env_base + total_arg_bytes (in_envp inp))%Z.
  Definition rnd_addr : Z := (bv_unsigned sp + head_size - 16)%Z.
  Definition gap_len : nat := (8 * (block_items (in_argv inp) (in_envp inp) mod 2))%nat.
  Definition pad_len : nat :=
    block_pad_len (kb_rseq (in_kernel inp)) sp (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp).
  Definition auxv_words : list word :=
    flat_map (fun e => [fst e; snd e])
      (auxv_entries (launch_auxv inp sp mbase) ph entry (in_uid inp) (in_gid inp) (in_hwcap inp)
         (Z_to_bv 64 rnd_addr) (Z_to_bv 64 execfn_addr)).
  Definition envp_addr : Z := (bv_unsigned sp + 8 * (argc + 2))%Z.
  Definition auxv_addr : Z := (bv_unsigned sp + 8 * (argc + envc + 3))%Z.

  Lemma string_base_eq : string_base_addr top argv envp execfn = Z_to_bv 64 str_base.
  Proof.
    unfold string_base_addr, str_base, str_len, nat_to_word. apply bv_eq.
    rewrite bv_sub_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
    rewrite Zminus_mod_idemp_r. f_equal. lia.
  Qed.

  Lemma at_random_ptr_eq : at_random_ptr sp (kb_rseq (in_kernel inp)) argv envp = Z_to_bv 64 rnd_addr.
  Proof.
    unfold at_random_ptr, rnd_addr, head_size, nat_to_word.
    rewrite <- (Z_to_bv_bv_unsigned sp) at 1. rewrite lit_add_lit. f_equal.
    set (B := block_head_size _ _ _).
    assert (HB : (16 <= B)%nat) by (unfold B, block_head_size; cbv zeta; lia).
    rewrite Nat2Z.inj_sub by lia. lia.
  Qed.

  Lemma at_execfn_ptr_eq : at_execfn_ptr top execfn = Z_to_bv 64 execfn_addr.
  Proof.
    unfold at_execfn_ptr, execfn_addr, env_base, str_base, str_len, launch_string_bytes, nat_to_word.
    pose proof (flatten_strings_length argv). pose proof (flatten_strings_length envp).
    apply bv_eq. rewrite bv_sub_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
    rewrite Zminus_mod_idemp_r. f_equal. lia.
  Qed.

  Lemma length_auxv_words : length auxv_words = (2 * auxv_count (kb_rseq (in_kernel inp)))%nat.
  Proof using inp mbase ph entry sp draw.
    pose proof (length_auxv_bytes (launch_auxv inp sp mbase) ph entry (in_uid inp) (in_gid inp) (in_hwcap inp)
                  (Z_to_bv 64 rnd_addr) (Z_to_bv 64 execfn_addr)) as H.
    rewrite auxv_bytes_words, u64s_length in H. unfold auxv_size in H.
    change (la_rseq (launch_auxv inp sp mbase)) with (kb_rseq (in_kernel inp)) in H.
    unfold auxv_words. lia.
  Qed.

  Lemma argv_ptrs_length : length argv_ptrs = length argv.
  Proof. unfold argv_ptrs. rewrite map_length. apply str_ptrs_length. Qed.
  Lemma envp_ptrs_length : length envp_ptrs = length envp.
  Proof. unfold envp_ptrs. rewrite map_length. apply str_ptrs_length. Qed.

  Lemma head_size_eq :
    head_size = (8 * (argc + envc + 3) + Z.of_nat (8 * length auxv_words) + Z.of_nat gap_len + 16)%Z.
  Proof using inp mbase ph entry sp draw.
    rewrite length_auxv_words. unfold head_size, block_head_size, gap_len, argc, envc, auxv_size.
    cbv zeta. unfold block_items. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma image_eq :
    img = le8 (Z_to_bv 64 argc) ++ u64s argv_ptrs ++ le8 (Z_to_bv 64 0) ++ u64s envp_ptrs ++ le8 (Z_to_bv 64 0)
          ++ u64s auxv_words ++ repeat (Z_to_bv 8 0) gap_len ++ at_random_bytes (ed_random draw)
          ++ repeat (Z_to_bv 8 0) pad_len
          ++ flatten_strings argv ++ flatten_strings envp ++ execfn ++ [Z_to_bv 8 0]
          ++ repeat (Z_to_bv 8 0) 8.
  Proof using inp mbase ph entry sp draw.
    unfold entry_stack_image, build_stack_bytes. cbv zeta.
    rewrite string_base_eq, string_addrs_eq. cbv beta iota.
    try change (str_base + total_arg_bytes argv)%Z with env_base.
    rewrite string_addrs_eq. cbv beta iota.
    change (la_rseq (launch_auxv inp sp mbase)) with (kb_rseq (in_kernel inp)).
    rewrite at_random_ptr_eq, at_execfn_ptr_eq, auxv_bytes_words.
    unfold argv_ptrs, envp_ptrs, auxv_words, gap_len, pad_len, argc, len_word.
    rewrite !flat_map_word_le8, !word_le8_le8, <- !app_assoc. reflexivity.
  Qed.

  Section Launch.
  (* [comment removed for export] *)
  Hypothesis HSP : (bv_unsigned sp + head_size <= bv_unsigned (ed_top draw) - 8 - str_len)%Z.

  Lemma pad_len_eq : Z.of_nat pad_len = (bv_unsigned (ed_top draw) - 8 - str_len - bv_unsigned sp - head_size)%Z.
  Proof using inp mbase ph entry sp draw HSP. unfold pad_len, block_pad_len. unfold head_size, str_len in *. rewrite Z2Nat.id by lia. reflexivity. Qed.

  Lemma image_length : Z.of_nat (length img) = (bv_unsigned (ed_top draw) - bv_unsigned sp)%Z.
  Proof using inp mbase ph entry sp draw HSP.
    pose proof pad_len_eq as P. unfold entry_stack_image. rewrite length_build_stack_bytes.
    change (la_rseq (launch_auxv inp sp mbase)) with (kb_rseq (in_kernel inp)).
    unfold pad_len, head_size, str_len in *. lia.
  Qed.

  Lemma image_hi : (bv_unsigned sp + Z.of_nat (length img) <= 2^64)%Z.
  Proof using inp mbase ph entry sp draw HSP. rewrite image_length. pose proof (u64_range (ed_top draw)). lia. Qed.

  Lemma str_base_eq : str_base = (bv_unsigned sp + head_size + Z.of_nat pad_len)%Z.
  Proof using inp mbase ph entry sp draw HSP. rewrite pad_len_eq. unfold str_base. lia. Qed.

  Lemma str_top : (env_base + total_arg_bytes envp <= bv_unsigned (ed_top draw) - 9)%Z.
  Proof using inp mbase ph entry sp draw HSP.
    unfold env_base, str_base, str_len, launch_string_bytes.
    pose proof (flatten_strings_length argv). pose proof (flatten_strings_length envp). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma init_pieces :
    bytes_at segs m0 usp (le8 (Z_to_bv 64 argc)) /\
    bytes_at segs m0 (usp + 8) (u64s (argv_ptrs ++ [Z_to_bv 64 0])) /\
    bytes_at segs m0 (usp + 8 * (argc + 2)) (u64s (envp_ptrs ++ [Z_to_bv 64 0])) /\
    bytes_at segs m0 (usp + 8 * (argc + envc + 3)) (u64s auxv_words) /\
    bytes_at segs m0 str_base (flatten_strings argv) /\
    bytes_at segs m0 env_base (flatten_strings envp) /\
    bytes_at segs m0 rnd_addr (at_random_bytes (ed_random draw)).
  Proof using inp mbase ph entry sp draw HSP.
    pose proof (init_stack_bytes inp mbase ph entry sp draw image_hi) as B. rewrite image_eq in B.
    pose proof head_size_eq as HH. pose proof str_base_eq as HS.
    pose proof argv_ptrs_length as LA. pose proof envp_ptrs_length as LE.
    pose proof (flatten_strings_length argv) as L1.
    apply bytes_at_app in B. destruct B as [B0 B].
    apply bytes_at_app in B. destruct B as [B1 B].
    apply bytes_at_app in B. destruct B as [B2 B].
    apply bytes_at_app in B. destruct B as [B3 B].
    apply bytes_at_app in B. destruct B as [B4 B].
    apply bytes_at_app in B. destruct B as [B5 B].
    apply bytes_at_app in B. destruct B as [B6 B].
    apply bytes_at_app in B. destruct B as [B7 B].
    apply bytes_at_app in B. destruct B as [B8 B].
    apply bytes_at_app in B. destruct B as [B9 B].
    apply bytes_at_app in B. destruct B as [B10 _].
    rewrite ?length_le8, ?u64s_length, ?repeat_length, ?length_at_random_bytes in *.
    unfold argc, envc in *.
    repeat match goal with |- _ /\ _ => split end.
    - exact B0.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app segs m0 _ _ _)). split.
      + replace (usp + 8)%Z with (usp + Z.of_nat 8)%Z by lia. exact B1.
      + rewrite u64s_length. replace (usp + 8 + Z.of_nat (8 * length argv_ptrs))%Z
          with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv_ptrs))%Z by lia. exact B2.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app segs m0 _ _ _)). split.
      + replace (usp + 8 * (Z.of_nat (length argv) + 2))%Z
          with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv_ptrs) + Z.of_nat 8)%Z by lia. exact B3.
      + rewrite u64s_length.
        replace (usp + 8 * (Z.of_nat (length argv) + 2) + Z.of_nat (8 * length envp_ptrs))%Z
          with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv_ptrs) + Z.of_nat 8 + Z.of_nat (8 * length envp_ptrs))%Z by lia.
        exact B4.
    - match type of B5 with bytes_at _ _ ?A _ => replace (usp + 8 * (Z.of_nat (length argv) + Z.of_nat (length envp) + 3))%Z with A by lia end.
      exact B5.
    - match type of B9 with bytes_at _ _ ?A _ => replace str_base with A by lia end. exact B9.
    - match type of B10 with bytes_at _ _ ?A _ => replace env_base with A by (unfold env_base; lia) end. exact B10.
    - match type of B7 with bytes_at _ _ ?A _ => replace rnd_addr with A by (unfold rnd_addr; lia) end. exact B7.
  Qed.

  (* the same pieces in any memory that holds the image (the stack at main) *)
  Lemma image_pieces : forall m, bytes_at segs m usp img ->
    bytes_at segs m usp (le8 (Z_to_bv 64 argc)) /\
    bytes_at segs m (usp + 8) (u64s (argv_ptrs ++ [Z_to_bv 64 0])) /\
    bytes_at segs m (usp + 8 * (argc + 2)) (u64s (envp_ptrs ++ [Z_to_bv 64 0])) /\
    bytes_at segs m (usp + 8 * (argc + envc + 3)) (u64s auxv_words) /\
    bytes_at segs m str_base (flatten_strings argv) /\
    bytes_at segs m env_base (flatten_strings envp) /\
    bytes_at segs m rnd_addr (at_random_bytes (ed_random draw)).
  Proof using inp mbase ph entry sp draw HSP.
    intros m B. rewrite image_eq in B.
    pose proof head_size_eq as HH. pose proof str_base_eq as HS.
    pose proof argv_ptrs_length as LA. pose proof envp_ptrs_length as LE.
    pose proof (flatten_strings_length argv) as L1.
    apply bytes_at_app in B. destruct B as [B0 B].
    apply bytes_at_app in B. destruct B as [B1 B].
    apply bytes_at_app in B. destruct B as [B2 B].
    apply bytes_at_app in B. destruct B as [B3 B].
    apply bytes_at_app in B. destruct B as [B4 B].
    apply bytes_at_app in B. destruct B as [B5 B].
    apply bytes_at_app in B. destruct B as [B6 B].
    apply bytes_at_app in B. destruct B as [B7 B].
    apply bytes_at_app in B. destruct B as [B8 B].
    apply bytes_at_app in B. destruct B as [B9 B].
    apply bytes_at_app in B. destruct B as [B10 _].
    rewrite ?length_le8, ?u64s_length, ?repeat_length, ?length_at_random_bytes in *.
    unfold argc, envc in *.
    repeat match goal with |- _ /\ _ => split end.
    - exact B0.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app segs m _ _ _)). split.
      + replace (usp + 8)%Z with (usp + Z.of_nat 8)%Z by lia. exact B1.
      + rewrite u64s_length. replace (usp + 8 + Z.of_nat (8 * length argv_ptrs))%Z
          with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv_ptrs))%Z by lia. exact B2.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app segs m _ _ _)). split.
      + replace (usp + 8 * (Z.of_nat (length argv) + 2))%Z
          with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv_ptrs) + Z.of_nat 8)%Z by lia. exact B3.
      + rewrite u64s_length.
        replace (usp + 8 * (Z.of_nat (length argv) + 2) + Z.of_nat (8 * length envp_ptrs))%Z
          with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv_ptrs) + Z.of_nat 8 + Z.of_nat (8 * length envp_ptrs))%Z by lia.
        exact B4.
    - match type of B5 with bytes_at _ _ ?A _ => replace (usp + 8 * (Z.of_nat (length argv) + Z.of_nat (length envp) + 3))%Z with A by lia end.
      exact B5.
    - match type of B9 with bytes_at _ _ ?A _ => replace str_base with A by lia end. exact B9.
    - match type of B10 with bytes_at _ _ ?A _ => replace env_base with A by (unfold env_base; lia) end. exact B10.
    - match type of B7 with bytes_at _ _ ?A _ => replace rnd_addr with A by (unfold rnd_addr; lia) end. exact B7.
  Qed.

  (* argv[i]'s string and the up-to-7 bytes after its NUL, in a memory that holds the image *)
  Lemma image_argv_string : forall m, bytes_at segs m usp img ->
    forall i s, nth_error argv i = Some s ->
    exists p slack, nth_error argv_ptrs i = Some (Z_to_bv 64 p) /\ (str_base <= p)%Z /\
      (p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= usp + Z.of_nat (length img))%Z /\
      bytes_at segs m p (s ++ Z_to_bv 8 0 :: slack) /\
      ((- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Proof using inp mbase ph entry sp draw HSP.
    intros m IMG i s Hn. destruct (str_ptrs_nth argv str_base i s Hn) as (off & Hp & Ho & Ht & Hf).
    pose proof image_length as IL. pose proof str_top as ST. pose proof str_base_eq as SB.
    pose proof (total_arg_bytes_nonneg envp) as TE. pose proof (flatten_strings_length argv) as L1.
    assert (HH0 : (0 <= head_size)%Z) by (unfold head_size; lia).
    set (p := (str_base + off)%Z). set (e := (p + Z.of_nat (length s) + 1)%Z). set (k := ((- e) mod 8)%Z).
    assert (HK : (0 <= k < 8)%Z) by (subst k; apply Z.mod_pos_bound; lia).
    assert (OFF : (usp <= p)%Z /\ (e + k <= usp + Z.of_nat (length img))%Z).
    { subst p e. unfold env_base in ST. split; lia. }
    exists p, (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) img)).
    split; [unfold argv_ptrs; rewrite nth_error_map, Hp; reflexivity|]. split; [subst p; lia|].
    assert (LS : length (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) img)) = Z.to_nat k)
      by (rewrite length_firstn, length_skipn; lia).
    rewrite LS. split; [lia|]. split; [| lia].
    destruct (image_pieces m IMG) as (_ & _ & _ & _ & B6 & _).
    pose proof (bytes_at_slice m str_base (flatten_strings argv) (Z.to_nat off) (length s + 1) B6 ltac:(lia)) as BS.
    rewrite Hf in BS. replace (str_base + Z.of_nat (Z.to_nat off))%Z with p in BS by (subst p; lia).
    pose proof (bytes_at_slice m usp img (Z.to_nat (e - usp)) (Z.to_nat k) IMG ltac:(lia)) as BK.
    replace (usp + Z.of_nat (Z.to_nat (e - usp)))%Z with (p + Z.of_nat (length (s ++ [Z_to_bv 8 0])))%Z in BK
      by (rewrite length_app; cbn [length]; subst e; lia).
    pose proof (proj2 (bytes_at_app segs m p _ _) (conj BS BK)) as BB. rewrite <- app_assoc in BB. cbn [app] in BB. exact BB.
  Qed.

  Lemma init_argv_string : forall i s, nth_error argv i = Some s ->
    exists p, nth_error argv_ptrs i = Some (Z_to_bv 64 p) /\ (str_base <= p)%Z /\
      (p + Z.of_nat (length s) + 1 <= env_base)%Z /\ bytes_at segs m0 p (s ++ [Z_to_bv 8 0]).
  Proof using inp mbase ph entry sp draw HSP.
    intros i s Hn. destruct (str_ptrs_nth argv str_base i s Hn) as (off & Hp & Ho & Ht & Hf).
    exists (str_base + off)%Z. split. { unfold argv_ptrs. rewrite nth_error_map, Hp. reflexivity. }
    split; [lia|]. split. { unfold env_base. lia. }
    destruct init_pieces as (_ & _ & _ & _ & B6 & _).
    pose proof (flatten_strings_length argv).
    pose proof (bytes_at_slice m0 str_base (flatten_strings argv) (Z.to_nat off) (length s + 1) B6 ltac:(lia)) as B.
    rewrite Hf in B. replace (str_base + Z.of_nat (Z.to_nat off))%Z with (str_base + off)%Z in B by lia. exact B.
  Qed.

  Lemma argv_ptr_bounds : forall i p, nth_error argv_ptrs i = Some p ->
    (str_base <= bv_unsigned p < env_base)%Z.
  Proof using inp mbase ph entry sp draw HSP.
    intros i p Hn. unfold argv_ptrs in Hn. rewrite nth_error_map in Hn.
    destruct (nth_error (str_ptrs str_base argv) i) as [q|] eqn:E; [|discriminate]. injection Hn as <-.
    apply str_ptrs_bounds in E. pose proof str_top. pose proof str_base_eq.
    pose proof (u64_range sp). pose proof (u64_range (ed_top draw)).
    pose proof (total_arg_bytes_nonneg envp).
    unfold head_size in *. unfold env_base in *. rewrite unsigned_lit; lia.
  Qed.

  Lemma envp_ptr_bounds : forall i p, nth_error envp_ptrs i = Some p ->
    (env_base <= bv_unsigned p < env_base + total_arg_bytes envp)%Z.
  Proof using inp mbase ph entry sp draw HSP.
    intros i p Hn. unfold envp_ptrs in Hn. rewrite nth_error_map in Hn.
    destruct (nth_error (str_ptrs env_base envp) i) as [q|] eqn:E; [|discriminate]. injection Hn as <-.
    apply str_ptrs_bounds in E. pose proof str_top. pose proof str_base_eq.
    pose proof (u64_range sp). pose proof (u64_range (ed_top draw)).
    pose proof (total_arg_bytes_nonneg argv).
    unfold head_size in *. unfold env_base in *. rewrite unsigned_lit; lia.
  Qed.

  End Launch.
End Layout.

(* [comment removed for export] *)
(* Stated outside [Section Layout], as openssl/bndiv's P/InitMem.v states it: inside the
   section its proof went through [head_size_eq], so discharge gave it all six section
   variables, and [head_size_ge inp] at the call sites was a universally quantified fact
   that lia cannot use. *)
Lemma head_size_ge : forall inp, (8 * (argc inp + envc inp + 3) + 16 <= head_size inp)%Z.
Proof. intros inp. unfold head_size, block_head_size, argc, envc. cbv zeta. unfold block_items. lia. Qed.

(* The launch conjunct of [Run.valid_entry_va] gives the [HSP] premise above. *)
Lemma launch_hsp : forall v inp mbase (sp brk : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (bv_unsigned sp + head_size inp <= bv_unsigned (ed_top draw) - 8 - str_len inp)%Z.
Proof.
  intros v inp mbase sp brk draw Hok. cbn [entry_launch_ok_va] in Hok.
  destruct Hok as (_ & (_ & _ & Hhi) & _).
  unfold launch_sp_hi, align_down16 in Hhi. unfold head_size, str_len.
  pose proof (Z.mod_pos_bound
    (bv_unsigned (ed_top draw) - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))) 16 ltac:(lia)).
  lia.
Qed.

(* VENDORED from the sibling openssl/bndiv P/InitMem.v:642-782, verbatim, seven lemmas.
   WHY: BgP/Impl.v:47 and BgU/Impl.v:46 both call [stack_window_lo_valid] and this unit
   defines it NOWHERE -- the two comments beside those calls point at the model's
   Common/StoreOk.v, which this tree's dune cannot reach (VCommon/Ax/AxEntryS.v:448 says
   so in as many words, and :265 records that the lemma 'is NOT carried' because it needs
   [launch_top_minus_sp] from Common/StepTac.v, equally unrequirable).  AxEntryS worked
   round that by proving its own [zero_window] for the facts IT needed; BgP/Impl needs the
   lemma itself, over [entry_launch_ok_va] rather than over AxEntryS's section hypotheses.
   THE DONOR IS SELF-CONSISTENT: bndiv's P/Impl.v:51 and U/Impl.v:53 call it in exactly the
   position bignum's BgP/Impl.v:47 does, with the same argument list
   [inp sp0 brk mbase draw VLN LAU], and bndiv's P/InitMem.v is what supplies it there.
   bndiv solved the unrequirable-dependency problem the same way: it vendors
   [launch_top_minus_sp] (its Common/StepTac copy is at VCommon/StepTac.v:860) and
   [launch_base_gap_le] (its AxEntryS copy is at VCommon/Ax/AxEntryS.v:324) locally, so a
   second copy of those two names in one unit is the donor's own settled arrangement and
   not a new homonym risk -- neither file is Required by the other in either unit.
   The two files' Require blocks are identical modulo the unit segment (Stdlib ZArith
   NArith List Lia Bool; LPS BvBase RiscvSemantics MemImageType StackLayout State Run;
   Riscv Prelude Instr Decode DecodeC Sem Fpu; lib.Lib PropExec Tac Arr Bytes; lib.Spec
   StrFun), so the donor's vocabulary transfers with its reasoning.  Placed inside
   [Section WithSegs] exactly as in the donor; none of the seven mentions [segs], so
   discharge gives them no extra argument. *)
Lemma block_head_size_le : forall rseq argv envp,
  (Z.of_nat (block_head_size rseq argv envp)
   <= 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 512)%Z.
Proof.
  intros rseq argv envp.
  unfold block_head_size, block_items, auxv_size, auxv_count.
  pose proof (Nat.mod_upper_bound
                (length argv + length envp + 3) 2 ltac:(lia)).
  destruct rseq; lia.
Qed.

Lemma launch_top_minus_sp : forall inp (top sp : word),
  valid_launch inp ->
  valid_launch_sp top inp sp ->
  (bv_unsigned top - bv_unsigned sp <= 2101782)%Z.
Proof.
  intros inp top sp [_ Hb] [_ [Hlo _]].
  unfold launch_bytes, e2big_limit in Hb.
  unfold launch_sp_lo, align_down16 in Hlo.
  pose proof (block_head_size_le (kb_rseq (in_kernel inp))
                (in_argv inp) (in_envp inp)).
  pose proof (Z.mod_pos_bound
    (bv_unsigned top - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                     (in_execfn inp))
     - 4095) 16 ltac:(lia)).
  lia.
Qed.

Lemma page_round_up_Z_fixed : forall n,
  (n mod page_size = 0)%Z -> page_round_up_Z n = n.
Proof.
  intros n Hn. unfold page_round_up_Z, page_size in *.
  apply Z.mod_divide in Hn; [|lia]. destruct Hn as [k Hk]. subst n.
  replace (k * 4096 + 4096 - 1)%Z with (k * 4096 + 4095)%Z by lia.
  rewrite Z.div_add_l by lia.
  replace (4095 / 4096)%Z with 0%Z by reflexivity. lia.
Qed.

Lemma mmap_gap_sv48 : forall kb,
  mmap_gap Sv48 kb
  = (let g := (stack_max_size + (stack_guard_gap_bytes kb
                 + if kb_aslr kb then stack_rnd_max else 0))%Z in
     if (g <? mmap_min_gap)%Z then mmap_min_gap else g).
Proof.
  intros kb. pose proof (stack_guard_gap_bytes_bounds kb) as Hgg.
  unfold mmap_gap. cbv zeta.
  rewrite Z.mod_small
    by (unfold two_pow_64, stack_max_size, stack_rnd_max;
        destruct (kb_aslr kb); lia).
  assert (Hmax : mmap_max_gap Sv48 = 117281240296105%Z)
    by (vm_compute; reflexivity).
  rewrite !Hmax.
  unfold mmap_min_gap in *. rewrite !Z.gtb_ltb.
  destruct (kb_aslr kb); cbv beta iota delta [andb];
  [ destruct (stack_max_size
              <? stack_max_size + (stack_guard_gap_bytes kb + stack_rnd_max))%Z
      eqn:Ein
  | destruct (stack_max_size
              <? stack_max_size + (stack_guard_gap_bytes kb + 0))%Z
      eqn:Ein ];
  try apply Z.ltb_lt in Ein; try apply Z.ltb_ge in Ein;
  cbv beta iota delta [andb];
  repeat (match goal with
          | |- context [(?x <? ?y)%Z] =>
              let E := fresh "E" in destruct (x <? y)%Z eqn:E;
              [ apply Z.ltb_lt in E | apply Z.ltb_ge in E ]
          end;
          cbv beta iota delta [andb]);
  unfold stack_max_size, stack_rnd_max in *; lia.
Qed.

Lemma mmap_gap_sv48_mod : forall kb,
  (mmap_gap Sv48 kb mod page_size = 0)%Z.
Proof.
  intros kb.
  assert (H4096 : forall x : Z, ((4096 * x) mod 4096 = 0)%Z)
    by (intro x; rewrite Z.mul_comm; apply Z_mod_mult).
  rewrite mmap_gap_sv48. cbv zeta.
  unfold stack_guard_gap_bytes, mmap_min_gap, stack_max_size,
    stack_rnd_max, page_size.
  destruct (_ <? _)%Z;
    [ replace (128 * 1024 * 1024)%Z with (4096 * 32768)%Z by reflexivity;
      apply H4096 |].
  destruct (kb_aslr kb);
    [ replace (8 * 1024 * 1024
               + (4096 * stack_guard_gap_pages kb + 1073737728))%Z
        with (4096 * (264191 + stack_guard_gap_pages kb))%Z by lia
    | replace (8 * 1024 * 1024 + (4096 * stack_guard_gap_pages kb + 0))%Z
        with (4096 * (2048 + stack_guard_gap_pages kb))%Z by lia ];
    apply H4096.
Qed.

Lemma launch_base_gap_le : forall kb mbase,
  valid_launch_base Sv48 kb mbase ->
  (bv_unsigned mbase + stack_guard_gap_bytes kb
   <= va_stack_top Sv48
      - (if kb_aslr kb then 0x407ff000 else 8 * 1024 * 1024))%Z.
Proof.
  intros kb mbase (r & Hr & _ & _ & Heq).
  pose proof (stack_guard_gap_bytes_bounds kb) as Hgg.
  rewrite Heq. unfold mmap_base_of.
  assert (Hdiv : (page_size
                  | va_stack_top Sv48 - mmap_gap Sv48 kb - page_size * r)%Z).
  { apply Z.divide_sub_r; [apply Z.divide_sub_r|].
    - exists 34359738368%Z. vm_compute. reflexivity.
    - apply Z.mod_divide; [unfold page_size; lia|]. apply mmap_gap_sv48_mod.
    - exists r. unfold page_size. lia. }
  rewrite page_round_up_Z_fixed
    by (apply Z.mod_divide; [unfold page_size; lia | exact Hdiv]).
  rewrite mmap_gap_sv48. cbv zeta.
  unfold mmap_min_gap, va_stack_top, sp_window_hi, stack_max_size,
    stack_rnd_max, page_size in *.
  destruct (kb_aslr kb); cbv beta iota;
  repeat (match goal with
          | |- context [(?x <? ?y)%Z] =>
              let E := fresh "E" in destruct (x <? y)%Z eqn:E;
              [ apply Z.ltb_lt in E | apply Z.ltb_ge in E ]
          end;
          cbv beta iota);
  lia.
Qed.

(* Both floors of the zero window are at least 6144513 bytes below [sp]
   ([Startup.STK_DEPTH] = stack_max_size - 2244095) for every launch the
   fifth conjunct of [Run.valid_entry_va] admits. *)
Lemma stack_window_lo_valid : forall inp (sp brk0 mbase : word) draw,
  valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase draw) inp ->
  (stack_window_lo (in_kernel inp) mbase draw
   <= bv_unsigned sp + 2244095 - stack_max_size)%Z.
Proof.
  intros inp sp brk0 mbase draw Hlaunch (Htop & Hsp & Hbase).
  pose proof (launch_top_minus_sp inp (ed_top draw) sp Hlaunch Hsp) as Hd.
  pose proof (launch_base_gap_le (in_kernel inp) mbase Hbase) as Hg.
  destruct Htop as (_ & Hhi & Hlo).
  unfold stack_window_lo, stack_max_size,
    va_stack_top, sp_window_hi, stack_rnd_max, page_size in *.
  destruct (kb_aslr (in_kernel inp)); cbv beta iota in Hg, Hlo;
    apply Z.max_lub; lia.
Qed.

(* [comment removed for export] *)
Fixpoint segs_top (sg : list Segment) : Z :=
  match sg with
  | [] => 0
  | s0 :: rest => Z.max (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) (segs_top rest)
  end.

Lemma find_segment_high : forall sg a n, (1 <= n)%Z -> (segs_top sg <= a)%Z -> find_segment sg a n = None.
Proof.
  induction sg as [|s0 sg IH]; intros a n Hn Ha; [reflexivity|]. cbn [find_segment segs_top] in *.
  replace (Z.leb (a + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite andb_false_r. apply IH; lia.
Qed.

(* [comment removed for export] *)
Lemma init_mem_inv' : forall inp mbase ph entry sp draw,
  (stack_window_lo (in_kernel inp) mbase draw <= bv_unsigned sp)%Z ->
  (bv_unsigned sp + Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw)) <= UTOP)%Z ->
  (segs_top segs <= stack_window_lo (in_kernel inp) mbase draw)%Z ->
  mem_inv segs (wrap_mem inp mbase ph entry sp draw).
Proof.
  intros inp mbase ph entry sp draw H1 H2 H3. apply init_mem_inv; try assumption.
  intros a Ha. apply find_segment_high; lia.
Qed.
End WithSegs.
