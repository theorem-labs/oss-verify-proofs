(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import PropExec Tac Arr Bytes.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import StrFun.
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

Section Init.

  Variables (ph : PhdrInfo) (sp : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw).
  Notation m0 := (wrap_mem ph sp argv envp uid hw draw).
  Notation img := (build_stack_bytes ph sp argv envp uid hw draw).
  Notation ent := (entry_stack_image ph sp argv envp uid hw draw).
  Hypothesis SPLO : (stack_max_size <= bv_unsigned sp)%Z.
  Hypothesis IMGHI : (bv_unsigned sp + Z.of_nat (length img) <= 2^64)%Z.
  Let SMS : stack_max_size = 8388608%Z := eq_refl.

  Lemma init_at : forall a : word,
    m0 a = if (Z.leb (bv_unsigned sp) (bv_unsigned a)) then
             (if Z.ltb (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length ent))
              then nth_error ent (Z.to_nat (bv_unsigned a - bv_unsigned sp)) else None)
           else if Z.leb (bv_unsigned sp - stack_max_size) (bv_unsigned a) then Some (Z_to_bv 8 0) else None.
  Proof.
    intros a. unfold wrap_mem, stack_to_mem.
    destruct (Z.leb_spec0 (bv_unsigned sp) (bv_unsigned a)).
    - destruct (Z.ltb_spec0 (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length ent))).
      + destruct (nth_error ent (Z.to_nat (bv_unsigned a - bv_unsigned sp))) eqn:E; [reflexivity|].
        apply nth_error_None in E. lia.
      + replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with false by (symmetry; apply Z.ltb_ge; lia).
        rewrite andb_false_r. reflexivity.
    - replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite andb_true_r. reflexivity.
  Qed.

  Lemma ent_len_ge : (Z.of_nat (length img) <= Z.of_nat (length ent))%Z.
  Proof. unfold entry_stack_image. cbv zeta. rewrite app_length. lia. Qed.

  Lemma init_at_block : forall a : word,
    (bv_unsigned sp <= bv_unsigned a < bv_unsigned sp + Z.of_nat (length img))%Z ->
    m0 a = nth_error img (Z.to_nat (bv_unsigned a - bv_unsigned sp)).
  Proof.
    intros a Ha. pose proof ent_len_ge as EL. rewrite init_at.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length ent))) with true by (symmetry; apply Z.ltb_lt; lia).
    apply entry_stack_image_block_prefix. lia.
  Qed.

  Lemma init_none : forall a : word, (bv_unsigned a < bv_unsigned sp - stack_max_size)%Z -> m0 a = None.
  Proof.
    intros a Ha. rewrite init_at.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia).
    replace (Z.leb (bv_unsigned sp - stack_max_size) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia).
    reflexivity.
  Qed.

  Lemma init_none_above : forall a : word, (bv_unsigned sp + Z.of_nat (length ent) <= bv_unsigned a)%Z -> m0 a = None.
  Proof.
    intros a Ha. rewrite init_at.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length ent))) with false by (symmetry; apply Z.ltb_ge; lia).
    reflexivity.
  Qed.

  Lemma init_stack_bytes : bytes_at segs m0 (bv_unsigned sp) img.
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
    split; [lia|]. split; [lia|]. intros i Hi. unfold mrd.
    assert (EA : bv_unsigned (wa (bv_unsigned sp + Z.of_nat i)) = (bv_unsigned sp + Z.of_nat i)%Z) by (apply wa_unsigned; lia).
    rewrite init_at_block by (rewrite EA; lia). rewrite EA.
    replace (Z.to_nat (bv_unsigned sp + Z.of_nat i - bv_unsigned sp)) with i by lia.
    destruct (nth_error img i) eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
  Qed.

  Lemma init_stack_wr : wr_at segs m0 (bv_unsigned sp) (Z.of_nat (length img)).
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
    split; [lia|]. split; [lia|]. intros i Hi. unfold wview.
    assert (EA : bv_unsigned (wa (bv_unsigned sp + i)) = (bv_unsigned sp + i)%Z) by (apply wa_unsigned; lia).
    rewrite init_at_block by (rewrite EA; lia). rewrite EA.
    destruct (nth_error img (Z.to_nat (bv_unsigned sp + i - bv_unsigned sp))) eqn:E; [discriminate|].
    apply nth_error_None in E. lia.
  Qed.

  Lemma init_stack_u8arr : u8arr segs m0 (bv_unsigned sp) img.
  Proof. split; [apply init_stack_bytes | apply init_stack_wr]. Qed.

  Lemma init_stk : stk segs m0 (bv_unsigned sp - stack_max_size) (bv_unsigned sp).
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
    split; [lia|]. split; [lia|]. intros a Ha.
    assert (E : m0 (wa a) = Some (Z_to_bv 8 0)).
    { rewrite init_at, wa_unsigned by lia.
      replace (Z.leb (bv_unsigned sp) a) with false by (symmetry; apply Z.leb_gt; lia).
      replace (Z.leb (bv_unsigned sp - stack_max_size) a) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
    split. { unfold wview. rewrite E. discriminate. } exists (Z_to_bv 8 0). unfold mrd. rewrite E. reflexivity.
  Qed.

  Hypothesis SEGS_LOW : forall a : word, (bv_unsigned sp - stack_max_size <= bv_unsigned a)%Z -> find_segment segs (bv_unsigned a) 1 = None.
  Hypothesis IMGTOP : (bv_unsigned sp + Z.of_nat (length ent) <= UTOP)%Z.
  Lemma init_mem_inv : mem_inv segs m0.
  Proof.
    apply mem_inv_intro.
    - intros a Hs. unfold seg_addr in Hs.
      destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned sp - stack_max_size)) as [Hl|Hh].
      + pose proof (Nat2Z.is_nonneg (length ent)). lia.
      + rewrite SEGS_LOW in Hs by lia. discriminate.
    - intros a b H. unfold ro_addr.
      destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned sp - stack_max_size)) as [Hl|Hh].
      + rewrite init_none in H by lia. discriminate.
      + rewrite SEGS_LOW by lia. split; [reflexivity|].
        destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned sp + Z.of_nat (length ent))) as [Hl'|Hh']; [lia|].
        rewrite init_none_above in H by lia. discriminate.
  Qed.
End Init.

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

Section Layout.

  Variables (ph : PhdrInfo) (sp : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw).
  Notation usp := (bv_unsigned sp).
  Definition argc : Z := Z.of_nat (length argv).
  Definition envc : Z := Z.of_nat (length envp).

  Definition struct_size : Z := (8 * (argc + envc) + 184)%Z.
  Definition str_base : Z := (usp + struct_size)%Z.
  Definition argv_ptrs : list word := map (Z_to_bv 64) (str_ptrs str_base argv).
  Definition env_base : Z := (str_base + total_arg_bytes argv)%Z.
  Definition envp_ptrs : list word := map (Z_to_bv 64) (str_ptrs env_base envp).

  Definition raw_len : Z := (struct_size + total_arg_bytes argv + total_arg_bytes envp)%Z.
  Definition pad_len : Z := ((8 - raw_len mod 8) mod 8)%Z.
  Definition rnd_addr : Z := (usp + raw_len + pad_len)%Z.
  Definition auxv_words : list word :=
    [Z_to_bv 64 3; Z_to_bv 64 (Z.of_N (ph_addr ph)); Z_to_bv 64 4; Z_to_bv 64 (Z.of_N (ph_ent ph));
     Z_to_bv 64 5; Z_to_bv 64 (Z.of_N (ph_num ph)); Z_to_bv 64 16; hw; Z_to_bv 64 6; Z_to_bv 64 4096;
     Z_to_bv 64 11; uid; Z_to_bv 64 12; uid; Z_to_bv 64 23; Z_to_bv 64 0;
     Z_to_bv 64 25; Z_to_bv 64 rnd_addr; Z_to_bv 64 0; Z_to_bv 64 0].

  Lemma at_random_ptr_eq : at_random_ptr sp argv envp = Z_to_bv 64 rnd_addr.
  Proof.
    unfold at_random_ptr, rnd_addr, pad_len, raw_len, struct_size, argc, envc, auxv_size, nat_to_word.
    rewrite <- (Z_to_bv_bv_unsigned sp) at 1. rewrite lit_add_lit. f_equal.
    pose proof (flatten_strings_length argv). pose proof (flatten_strings_length envp).
    pose proof (total_arg_bytes_nonneg argv). pose proof (total_arg_bytes_nonneg envp).
    set (L := (8 + (length argv + 1) * 8 + (length envp + 1) * 8 + 160 + length (flatten_strings argv) + length (flatten_strings envp))%nat).
    replace (Z.of_nat L) with (8 * (Z.of_nat (length argv) + Z.of_nat (length envp)) + 184 + total_arg_bytes argv + total_arg_bytes envp)%Z by lia.
    Z.div_mod_to_equations. lia.
  Qed.

  Definition raw_bytes : list byte :=
    u64s (Z_to_bv 64 argc :: argv_ptrs ++ [Z_to_bv 64 0] ++ envp_ptrs ++ [Z_to_bv 64 0] ++ auxv_words)
    ++ flatten_strings argv ++ flatten_strings envp.

  Lemma raw_bytes_length : Z.of_nat (length raw_bytes) = raw_len.
  Proof.
    unfold raw_bytes, raw_len. rewrite !app_length, u64s_length. cbn [length]. repeat rewrite app_length. cbn [length].
    repeat rewrite app_length. cbn [length]. unfold argv_ptrs, envp_ptrs. rewrite !map_length, !str_ptrs_length.
    pose proof (flatten_strings_length argv). pose proof (flatten_strings_length envp). unfold struct_size, argc, envc.
    change (length auxv_words) with 20%nat. lia.
  Qed.

  Lemma build_stack_bytes_eq :
    build_stack_bytes ph sp argv envp uid hw draw = raw_bytes ++ repeat (Z_to_bv 8 0) (Z.to_nat pad_len) ++ at_random_bytes (ed_random draw).
  Proof.
    unfold build_stack_bytes. rewrite length_auxv_bytes.
    unfold nat_to_word. rewrite <- (Z_to_bv_bv_unsigned sp) at 1. rewrite lit_add_lit.
    replace (usp + Z.of_nat (8 + (length argv + 1) * 8 + (length envp + 1) * 8 + auxv_size))%Z with str_base.
    2:{ unfold str_base, struct_size, argc, envc, auxv_size. lia. }
    rewrite string_addrs_eq. cbn [fst snd]. fold env_base. rewrite string_addrs_eq. cbn [fst snd].
    unfold auxv_bytes, build_auxv, auxv_entries. rewrite at_random_ptr_eq.
    cbn [flat_map fst snd]. unfold AT_PHDR, AT_PHENT, AT_PHNUM, AT_HWCAP, AT_PAGESZ, AT_UID, AT_EUID, AT_SECURE, AT_RANDOM, AT_NULL.
    lazymatch goal with |- (?r ++ repeat _ _ ++ at_random_bytes _) = _ => set (RAW := r) end.
    assert (ER : RAW = raw_bytes).
    { subst RAW. unfold raw_bytes, argv_ptrs, envp_ptrs, auxv_words, len_word. fold argc.
      cbn [u64s]. rewrite !u64s_app. cbn [u64s]. rewrite <- !app_assoc. cbn [app].
      repeat (apply f_equal2; [ first [ reflexivity | symmetry; apply flat_map_word_le8 | apply flat_map_word_le8 ] | ]).
      reflexivity. }
    rewrite ER. f_equal. f_equal. f_equal. unfold pad_len. rewrite raw_bytes_length. reflexivity.
  Qed.

  Lemma build_stack_bytes_length :
    Z.of_nat (length (build_stack_bytes ph sp argv envp uid hw draw)) = (raw_len + pad_len + 16)%Z.
  Proof.
    rewrite build_stack_bytes_eq, !app_length, repeat_length. rewrite length_at_random_bytes.
    pose proof raw_bytes_length. unfold pad_len. Z.div_mod_to_equations. lia.
  Qed.

  Notation m0 := (wrap_mem ph sp argv envp uid hw draw).
  Hypothesis SPLO : (stack_max_size <= bv_unsigned sp)%Z.
  Hypothesis IMGHI : (bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp argv envp uid hw draw)) <= 2^64)%Z.

  Lemma wr_at_sub : forall m a n a' n', wr_at segs m a n -> (a <= a')%Z -> (a' + n' <= a + n)%Z -> wr_at segs m a' n'.
  Proof.
    intros m a n a' n' (Ha & Hn & H) H1 H2. split; [lia|]. split; [lia|].
    intros i Hi. replace (a' + i)%Z with (a + (a' - a + i))%Z by lia. apply H. lia.
  Qed.

  Lemma rw_cells_of_parts : forall m A cs,
    cells_wf cs -> bytes_at segs m A (cells_bytes cs) -> wr_at segs m A (Z.of_nat (cells_size cs)) -> rw_cells segs m A cs.
  Proof. intros m A cs Hwf Hb Hw. split; [split; assumption| exact Hw]. Qed.

  Lemma raw_len_nonneg : (0 <= struct_size /\ 0 <= total_arg_bytes argv /\ 0 <= total_arg_bytes envp /\ 0 <= pad_len < 8)%Z.
  Proof.
    pose proof (total_arg_bytes_nonneg argv). pose proof (total_arg_bytes_nonneg envp).
    unfold struct_size, argc, envc, pad_len. Z.div_mod_to_equations. lia.
  Qed.

  Lemma init_wr : wr_at segs m0 usp (raw_len + pad_len + 16).
  Proof. rewrite <- build_stack_bytes_length. apply (init_stack_wr ph sp argv envp uid hw draw SPLO IMGHI). Qed.

  Lemma init_pieces :
    bytes_at segs m0 usp (le8 (Z_to_bv 64 argc)) /\
    bytes_at segs m0 (usp + 8) (u64s (argv_ptrs ++ [Z_to_bv 64 0])) /\
    bytes_at segs m0 (usp + 8 * (argc + 2)) (u64s (envp_ptrs ++ [Z_to_bv 64 0])) /\
    bytes_at segs m0 (usp + 8 * (argc + envc + 3)) (u64s auxv_words) /\
    bytes_at segs m0 str_base (flatten_strings argv) /\
    bytes_at segs m0 env_base (flatten_strings envp) /\
    bytes_at segs m0 rnd_addr (at_random_bytes (ed_random draw)).
  Proof.
    pose proof (init_stack_bytes ph sp argv envp uid hw draw SPLO IMGHI) as B. rewrite build_stack_bytes_eq in B.
    unfold raw_bytes in B. cbn [u64s app] in B.
    rewrite u64s_app in B. cbn [u64s app] in B. rewrite u64s_app in B. cbn [u64s app] in B.
    repeat rewrite <- app_assoc in B. cbn [app] in B.
    pose proof raw_len_nonneg as RN.
    pose proof (flatten_strings_length argv) as L1. pose proof (flatten_strings_length envp) as L2.
    apply bytes_at_app in B. destruct B as [B0 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B1 B]. rewrite u64s_length in B. unfold argv_ptrs in B. rewrite map_length, str_ptrs_length in B.
    apply bytes_at_app in B. destruct B as [B2 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B3 B]. rewrite u64s_length in B. unfold envp_ptrs in B. rewrite map_length, str_ptrs_length in B.
    apply bytes_at_app in B. destruct B as [B4 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B5 B]. rewrite u64s_length in B. change (length auxv_words) with 20%nat in B.
    apply bytes_at_app in B. destruct B as [B6 B].
    apply bytes_at_app in B. destruct B as [B7 B].
    apply bytes_at_app in B. destruct B as [B8 B]. rewrite repeat_length in B.
    repeat match goal with |- _ /\ _ => split end.
    - exact B0.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app segs m0 _ _ _)). split; [exact B1|].
      rewrite u64s_length. unfold argv_ptrs at 1. rewrite map_length, str_ptrs_length.
      replace (usp + 8 + Z.of_nat (8 * length argv))%Z with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv))%Z by lia. exact B2.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app segs m0 _ _ _)). split.
      + replace (usp + 8 * (argc + 2))%Z with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8)%Z by (unfold argc; lia). exact B3.
      + rewrite u64s_length. unfold envp_ptrs at 1. rewrite map_length, str_ptrs_length.
        replace (usp + 8 * (argc + 2) + Z.of_nat (8 * length envp))%Z
          with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp))%Z by (unfold argc; lia). exact B4.
    - replace (usp + 8 * (argc + envc + 3))%Z
        with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8)%Z by (unfold argc, envc; lia). exact B5.
    - replace str_base with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8 + Z.of_nat (8 * 20))%Z
        by (unfold str_base, struct_size, argc, envc; lia). exact B6.
    - replace env_base with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8 + Z.of_nat (8 * 20) + Z.of_nat (length (flatten_strings argv)))%Z
        by (unfold env_base, str_base, struct_size, argc, envc; lia). exact B7.
    - replace rnd_addr with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8 + Z.of_nat (8 * 20)
                             + Z.of_nat (length (flatten_strings argv)) + Z.of_nat (length (flatten_strings envp)) + Z.of_nat (Z.to_nat pad_len))%Z
        by (unfold rnd_addr, raw_len, struct_size, argc, envc; lia). exact B.
  Qed.

  Lemma bytes_at_slice : forall m a bs off k,
    bytes_at segs m a bs -> (off + k <= length bs)%nat ->
    bytes_at segs m (a + Z.of_nat off) (firstn k (skipn off bs)).
  Proof.
    intros m a bs off k H Hk.
    rewrite <- (firstn_skipn off bs) in H. apply bytes_at_app in H. destruct H as [_ H].
    rewrite firstn_length in H. replace (Nat.min off (length bs)) with off in H by lia.
    rewrite <- (firstn_skipn k (skipn off bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
  Qed.

  Lemma init_argv_string : forall i s, nth_error argv i = Some s ->
    exists p, nth_error argv_ptrs i = Some (Z_to_bv 64 p) /\ (str_base <= p)%Z /\
      (p + Z.of_nat (length s) + 1 <= env_base)%Z /\ bytes_at segs m0 p (s ++ [Z_to_bv 8 0]).
  Proof.
    intros i s Hn. destruct (str_ptrs_nth argv str_base i s Hn) as (off & Hp & Ho & Ht & Hf).
    exists (str_base + off)%Z. split. { unfold argv_ptrs. rewrite nth_error_map, Hp. reflexivity. }
    split; [lia|]. split. { unfold env_base. lia. }
    destruct init_pieces as (_ & _ & _ & _ & B6 & _).
    pose proof (flatten_strings_length argv).
    pose proof (bytes_at_slice m0 str_base (flatten_strings argv) (Z.to_nat off) (length s + 1) B6 ltac:(lia)) as B.
    rewrite Hf in B. replace (str_base + Z.of_nat (Z.to_nat off))%Z with (str_base + off)%Z in B by lia. exact B.
  Qed.

  Definition envp_addr : Z := (usp + 8 * (argc + 2))%Z.
  Definition auxv_addr : Z := (usp + 8 * (argc + envc + 3))%Z.

  Lemma argv_ptrs_length : length argv_ptrs = length argv.
  Proof. unfold argv_ptrs. rewrite map_length. apply str_ptrs_length. Qed.
  Lemma envp_ptrs_length : length envp_ptrs = length envp.
  Proof. unfold envp_ptrs. rewrite map_length. apply str_ptrs_length. Qed.

  Lemma str_ptrs_bounds : forall strs base i p, nth_error (str_ptrs base strs) i = Some p ->
    (base <= p /\ p < base + total_arg_bytes strs)%Z.
  Proof.
    induction strs as [|s0 strs IH]; intros base [|i] p Hn; cbn in Hn; try discriminate.
    - injection Hn as <-. rewrite total_arg_bytes_cons. pose proof (total_arg_bytes_nonneg strs). lia.
    - apply IH in Hn. rewrite total_arg_bytes_cons. lia.
  Qed.

  Lemma argv_ptr_bounds : forall i p, nth_error argv_ptrs i = Some p ->
    (str_base <= bv_unsigned p < env_base)%Z.
  Proof.
    intros i p Hn. unfold argv_ptrs in Hn. rewrite nth_error_map in Hn.
    destruct (nth_error (str_ptrs str_base argv) i) as [q|] eqn:E; [|discriminate]. injection Hn as <-.
    apply str_ptrs_bounds in E. pose proof raw_len_nonneg. pose proof build_stack_bytes_length.
    pose proof (bv_unsigned_in_range 64 sp).
    unfold env_base. rewrite unsigned_lit; [lia|]. unfold str_base, raw_len in *. lia.
  Qed.

  Lemma envp_ptr_bounds : forall i p, nth_error envp_ptrs i = Some p ->
    (env_base <= bv_unsigned p < env_base + total_arg_bytes envp)%Z.
  Proof.
    intros i p Hn. unfold envp_ptrs in Hn. rewrite nth_error_map in Hn.
    destruct (nth_error (str_ptrs env_base envp) i) as [q|] eqn:E; [|discriminate]. injection Hn as <-.
    apply str_ptrs_bounds in E. pose proof raw_len_nonneg. pose proof build_stack_bytes_length.
    pose proof (bv_unsigned_in_range 64 sp).
    rewrite unsigned_lit; [lia|]. unfold env_base, str_base, raw_len in *. lia.
  Qed.
End Layout.

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

Lemma init_mem_inv' : forall ph sp argv envp uid hw draw,
  (stack_max_size <= bv_unsigned sp)%Z ->
  (bv_unsigned sp + Z.of_nat (length (entry_stack_image ph sp argv envp uid hw draw)) <= UTOP)%Z ->
  (segs_top segs <= bv_unsigned sp - stack_max_size)%Z ->
  mem_inv segs (wrap_mem ph sp argv envp uid hw draw).
Proof.
  intros ph sp argv envp uid hw draw H1 H2 H3. apply init_mem_inv; try assumption.
  intros a Ha. apply find_segment_high; lia.
Qed.
End WithSegs.
