(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes.
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

Lemma bytes_le_to_Z_nonneg : forall bs : list byte, (0 <= bytes_le_to_Z bs)%Z.
Proof. intros bs. rewrite bytes_le_to_Z_le_val. apply (proj1 (le_val_range _ (bytes_ok_map bs))). Qed.

Lemma Z_to_le_bytes_to_Z : forall (bs : list byte), Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. cbn in Hb.
  pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256%Z.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs)%Z with (bv_unsigned b + bytes_le_to_Z bs * 256)%Z by lia.
    rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8)%Z with 256%Z.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs)%Z with (bytes_le_to_Z bs * 256 + bv_unsigned b)%Z by lia.
    rewrite Z.div_add_l, Z.div_small by lia. rewrite Z.add_0_r. exact IH.
Qed.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (le_val_range _ (bytes_ok_map bs)) as R. rewrite map_length, Hl in R. rewrite <- bytes_le_to_Z_le_val in R.
  unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z. rewrite Z.mod_small by (cbn in R; lia).
  rewrite <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Definition guard_bytes (rb : list byte) : list byte := firstn 1 rb ++ [Z_to_bv 8 0] ++ firstn 6 (skipn 2 rb).
Definition entry_guard (rnd : EntryDraw) : word := le_bytes_to_word (guard_bytes (at_random_bytes (ed_random rnd))).

Lemma guard_bytes_length : forall rb, (8 <= length rb)%nat -> length (guard_bytes rb) = 8%nat.
Proof. intros rb H. unfold guard_bytes. rewrite !app_length, !firstn_length, skipn_length. cbn [length]. lia. Qed.

Lemma guard_bytes_firstn8 : forall rb, guard_bytes (firstn 8 rb) = guard_bytes rb.
Proof.
  intros rb. unfold guard_bytes. rewrite firstn_firstn by lia. f_equal. f_equal.
  rewrite skipn_firstn_comm. cbn [Nat.sub]. rewrite firstn_firstn by lia. reflexivity.
Qed.

Lemma le8_entry_guard : forall rnd, le8 (entry_guard rnd) = guard_bytes (at_random_bytes (ed_random rnd)).
Proof. intros rnd. apply le8_of_bytes. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.

Section Init.
  Variables (ph : PhdrInfo) (sp : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Notation m0 := (wrap_mem ph sp argv envp uid hw rnd).
  Notation img := (build_stack_bytes ph sp argv envp uid hw rnd).
  Notation simg := (entry_stack_image ph sp argv envp uid hw rnd).
  Hypothesis SPLO : (stack_max_size <= bv_unsigned sp)%Z.
  Hypothesis IMGHI : (bv_unsigned sp + Z.of_nat (length img) <= 2^64)%Z.
  Let SMS : stack_max_size = 8388608%Z := eq_refl.

  #[using="Type"] Lemma simg_eq : simg = img ++ entry_slack sp img (ed_slack rnd).
  Proof. reflexivity. Qed.

  #[using="Type"] Lemma simg_length_ge : (length img <= length simg)%nat.
  Proof. rewrite simg_eq, app_length. lia. Qed.

  #[using="Type"] Lemma simg_top : (bv_unsigned sp + Z.of_nat (length simg) = entry_page_top sp img)%Z.
  Proof. apply entry_stack_image_top. Qed.

  #[using="Type"] Lemma simg_length_le : (Z.of_nat (length simg) <= Z.of_nat (length img) + 4095)%Z.
  Proof.
    pose proof simg_top as T. unfold entry_page_top, entry_block_top, page_round_up_Z, page_size in T.
    Z.div_mod_to_equations. lia.
  Qed.

  #[using="Type"] Lemma simg_nth_block : forall i, (i < length img)%nat -> nth_error simg i = nth_error img i.
  Proof. intros i Hi. apply entry_stack_image_block_prefix. exact Hi. Qed.

  #[using="Type"] Lemma init_at : forall a : word,
    m0 a = if (Z.leb (bv_unsigned sp) (bv_unsigned a)) then
             (if Z.ltb (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length simg))
              then nth_error simg (Z.to_nat (bv_unsigned a - bv_unsigned sp)) else None)
           else if Z.leb (bv_unsigned sp - stack_max_size) (bv_unsigned a) then Some (Z_to_bv 8 0) else None.
  Proof.
    intros a. unfold wrap_mem, stack_to_mem.
    destruct (Z.leb_spec0 (bv_unsigned sp) (bv_unsigned a)).
    - destruct (Z.ltb_spec0 (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length simg))).
      + destruct (nth_error simg (Z.to_nat (bv_unsigned a - bv_unsigned sp))) eqn:E; [reflexivity|].
        apply nth_error_None in E. lia.
      + replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with false by (symmetry; apply Z.ltb_ge; lia).
        rewrite andb_false_r. reflexivity.
    - replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite andb_true_r. reflexivity.
  Qed.

  #[using="Type"] Lemma init_at_block : forall a : word,
    (bv_unsigned sp <= bv_unsigned a)%Z -> (bv_unsigned a - bv_unsigned sp < Z.of_nat (length img))%Z ->
    m0 a = nth_error img (Z.to_nat (bv_unsigned a - bv_unsigned sp)).
  Proof.
    intros a H1 H2. rewrite init_at. pose proof simg_length_ge.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length simg))) with true by (symmetry; apply Z.ltb_lt; lia).
    apply simg_nth_block. lia.
  Qed.

  #[using="SMS"] Lemma init_none : forall a : word, (bv_unsigned a < bv_unsigned sp - stack_max_size)%Z -> m0 a = None.
  Proof.
    intros a Ha. rewrite init_at.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia).
    replace (Z.leb (bv_unsigned sp - stack_max_size) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia).
    reflexivity.
  Qed.

  #[using="Type"] Lemma init_none_above : forall a : word, (entry_page_top sp img <= bv_unsigned a)%Z -> m0 a = None.
  Proof.
    intros a Ha. rewrite init_at. pose proof simg_top.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length simg))) with false by (symmetry; apply Z.ltb_ge; lia).
    reflexivity.
  Qed.

  #[using="Type"] Lemma entry_page_top_le : (entry_page_top sp img <= bv_unsigned sp + Z.of_nat (length img) + 4095)%Z.
  Proof. pose proof simg_top. pose proof simg_length_le. lia. Qed.

  #[using="SPLO IMGHI SMS"] Lemma init_stack_bytes : bytes_at segs m0 (bv_unsigned sp) img.
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
    split; [lia|]. split; [lia|]. intros i Hi. unfold mrd.
    rewrite init_at_block by (rewrite wa_unsigned by lia; lia).
    rewrite wa_unsigned by lia.
    replace (Z.to_nat (bv_unsigned sp + Z.of_nat i - bv_unsigned sp)) with i by lia.
    destruct (nth_error img i) eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
  Qed.

  #[using="SPLO IMGHI SMS"] Lemma init_stack_wr : wr_at segs m0 (bv_unsigned sp) (Z.of_nat (length img)).
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
    split; [lia|]. split; [lia|]. intros i Hi. unfold wview.
    rewrite init_at_block by (rewrite wa_unsigned by lia; lia). rewrite wa_unsigned by lia.
    destruct (nth_error img (Z.to_nat (bv_unsigned sp + i - bv_unsigned sp))) eqn:E; [discriminate|].
    apply nth_error_None in E. lia.
  Qed.

  #[using="SPLO IMGHI SMS"] Lemma init_stack_u8arr : u8arr segs m0 (bv_unsigned sp) img.
  Proof. split; [apply init_stack_bytes | apply init_stack_wr]. Qed.

  #[using="SPLO"] Lemma init_stk : stk segs m0 (bv_unsigned sp - stack_max_size) (bv_unsigned sp).
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
  #[using="SMS SEGS_LOW"] Lemma init_mem_inv : mem_inv segs m0.
  Proof.
    intros a b H. unfold ro_addr.
    destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned sp - stack_max_size)) as [Hl|Hh].
    - rewrite init_none in H by lia. discriminate.
    - rewrite SEGS_LOW by lia. reflexivity.
  Qed.
End Init.

Fixpoint str_ptrs (base : Z) (strs : list (list byte)) : list Z :=
  match strs with
  | [] => []
  | s :: rest => base :: str_ptrs (base + Z.of_nat (length s) + 1)%Z rest
  end.

#[using="Type"] Lemma str_ptrs_length : forall strs base, length (str_ptrs base strs) = length strs.
Proof. induction strs; intros; cbn; [reflexivity|]. now rewrite IHstrs. Qed.

#[using="Type"] Lemma total_arg_bytes_cons : forall s0 strs, total_arg_bytes (s0 :: strs) = (Z.of_nat (length s0) + 1 + total_arg_bytes strs)%Z.
Proof. reflexivity. Qed.
#[using="Type"] Lemma total_arg_bytes_nil : total_arg_bytes [] = 0%Z.
Proof. reflexivity. Qed.

#[using="Type"] Lemma total_arg_bytes_nonneg : forall strs, (0 <= total_arg_bytes strs)%Z.
Proof. induction strs; [rewrite total_arg_bytes_nil | rewrite total_arg_bytes_cons]; lia. Qed.

#[using="Type"] Lemma flatten_strings_length : forall strs, Z.of_nat (length (flatten_strings strs)) = total_arg_bytes strs.
Proof.
  induction strs as [|s0 strs IH]; [reflexivity|]. rewrite total_arg_bytes_cons. unfold flatten_strings in *. cbn [flat_map].
  rewrite app_length, app_length. cbn [length]. lia.
Qed.

#[using="Type"] Lemma string_addrs_eq : forall strs base,
  string_addrs (Z_to_bv 64 base) strs = (map (Z_to_bv 64) (str_ptrs base strs), Z_to_bv 64 (base + total_arg_bytes strs)%Z).
Proof.
  induction strs as [|s0 strs IH]; intros base; cbn [string_addrs str_ptrs map].
  - rewrite total_arg_bytes_nil, Z.add_0_r. reflexivity.
  - unfold len_word. rewrite !lit_add_lit.
    change (Z_to_bv 64 (base + Z.of_nat (length s0))) with (wa (base + Z.of_nat (length s0))). rewrite wa_succ. unfold wa.
    rewrite IH. cbn [fst snd]. f_equal. f_equal. rewrite total_arg_bytes_cons. lia.
Qed.

#[using="Type"] Lemma str_ptrs_nth : forall strs base i s, nth_error strs i = Some s ->
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
  Variables (ph : PhdrInfo) (sp : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
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

  #[using="Type"] Lemma at_random_ptr_eq : at_random_ptr sp argv envp = Z_to_bv 64 rnd_addr.
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

  #[using="Type"] Lemma raw_bytes_length : Z.of_nat (length raw_bytes) = raw_len.
  Proof.
    unfold raw_bytes, raw_len. rewrite !app_length, u64s_length. cbn [length]. repeat rewrite app_length. cbn [length].
    repeat rewrite app_length. cbn [length]. unfold argv_ptrs, envp_ptrs. rewrite !map_length, !str_ptrs_length.
    pose proof (flatten_strings_length argv). pose proof (flatten_strings_length envp). unfold struct_size, argc, envc.
    change (length auxv_words) with 20%nat. lia.
  Qed.

  #[using="Type"] Lemma build_stack_bytes_eq :
    build_stack_bytes ph sp argv envp uid hw rnd = raw_bytes ++ repeat (Z_to_bv 8 0) (Z.to_nat pad_len) ++ at_random_bytes (ed_random rnd).
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

  #[using="Type"] Lemma build_stack_bytes_length :
    Z.of_nat (length (build_stack_bytes ph sp argv envp uid hw rnd)) = (raw_len + pad_len + 16)%Z.
  Proof.
    rewrite build_stack_bytes_eq, !app_length, repeat_length, length_at_random_bytes.
    pose proof raw_bytes_length. unfold pad_len. Z.div_mod_to_equations. lia.
  Qed.

  Notation m0 := (wrap_mem ph sp argv envp uid hw rnd).
  Hypothesis SPLO : (stack_max_size <= bv_unsigned sp)%Z.
  Hypothesis IMGHI : (bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp argv envp uid hw rnd)) <= 2^64)%Z.

  #[using="ph sp argv envp uid hw rnd"] Lemma wr_at_sub : forall m a n a' n', wr_at segs m a n -> (a <= a')%Z -> (a' + n' <= a + n)%Z -> wr_at segs m a' n'.
  Proof.
    intros m a n a' n' (Ha & Hn & H) H1 H2. split; [lia|]. split; [lia|].
    intros i Hi. replace (a' + i)%Z with (a + (a' - a + i))%Z by lia. apply H. lia.
  Qed.

  #[using="Type"] Lemma rw_cells_of_parts : forall m A cs,
    cells_wf cs -> bytes_at segs m A (cells_bytes cs) -> wr_at segs m A (Z.of_nat (cells_size cs)) -> rw_cells segs m A cs.
  Proof. intros m A cs Hwf Hb Hw. split; [split; assumption| exact Hw]. Qed.

  #[using="ph sp uid hw rnd"] Lemma raw_len_nonneg : (0 <= struct_size /\ 0 <= total_arg_bytes argv /\ 0 <= total_arg_bytes envp /\ 0 <= pad_len < 8)%Z.
  Proof.
    pose proof (total_arg_bytes_nonneg argv). pose proof (total_arg_bytes_nonneg envp).
    unfold struct_size, argc, envc, pad_len. Z.div_mod_to_equations. lia.
  Qed.

  #[using="SPLO IMGHI"] Lemma init_wr : wr_at segs m0 usp (raw_len + pad_len + 16).
  Proof. rewrite <- build_stack_bytes_length. apply (init_stack_wr ph sp argv envp uid hw rnd SPLO IMGHI). Qed.

  #[using="SPLO IMGHI"] Lemma init_pieces :
    bytes_at segs m0 usp (le8 (Z_to_bv 64 argc)) /\
    bytes_at segs m0 (usp + 8) (u64s (argv_ptrs ++ [Z_to_bv 64 0])) /\
    bytes_at segs m0 (usp + 8 * (argc + 2)) (u64s (envp_ptrs ++ [Z_to_bv 64 0])) /\
    bytes_at segs m0 (usp + 8 * (argc + envc + 3)) (u64s auxv_words) /\
    bytes_at segs m0 str_base (flatten_strings argv) /\
    bytes_at segs m0 env_base (flatten_strings envp) /\
    bytes_at segs m0 rnd_addr (at_random_bytes (ed_random rnd)).
  Proof.
    pose proof (init_stack_bytes ph sp argv envp uid hw rnd SPLO IMGHI) as B. rewrite build_stack_bytes_eq in B.
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

  #[using="ph sp argv envp uid hw rnd"] Lemma bytes_at_slice : forall m a bs off k,
    bytes_at segs m a bs -> (off + k <= length bs)%nat ->
    bytes_at segs m (a + Z.of_nat off) (firstn k (skipn off bs)).
  Proof.
    intros m a bs off k H Hk.
    rewrite <- (firstn_skipn off bs) in H. apply bytes_at_app in H. destruct H as [_ H].
    rewrite firstn_length in H. replace (Nat.min off (length bs)) with off in H by lia.
    rewrite <- (firstn_skipn k (skipn off bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
  Qed.

  #[using="SPLO IMGHI"] Lemma init_argv_string : forall i s, nth_error argv i = Some s ->
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

  #[using="Type"] Lemma argv_ptrs_length : length argv_ptrs = length argv.
  Proof. unfold argv_ptrs. rewrite map_length. apply str_ptrs_length. Qed.
  #[using="Type"] Lemma envp_ptrs_length : length envp_ptrs = length envp.
  Proof. unfold envp_ptrs. rewrite map_length. apply str_ptrs_length. Qed.

  #[using="ph sp argv envp uid hw rnd"] Lemma str_ptrs_bounds : forall strs base i p, nth_error (str_ptrs base strs) i = Some p ->
    (base <= p /\ p < base + total_arg_bytes strs)%Z.
  Proof.
    induction strs as [|s0 strs IH]; intros base [|i] p Hn; cbn in Hn; try discriminate.
    - injection Hn as <-. rewrite total_arg_bytes_cons. pose proof (total_arg_bytes_nonneg strs). lia.
    - apply IH in Hn. rewrite total_arg_bytes_cons. lia.
  Qed.

  #[using="ph uid hw rnd IMGHI"] Lemma argv_ptr_bounds : forall i p, nth_error argv_ptrs i = Some p ->
    (str_base <= bv_unsigned p < env_base)%Z.
  Proof.
    intros i p Hn. unfold argv_ptrs in Hn. rewrite nth_error_map in Hn.
    destruct (nth_error (str_ptrs str_base argv) i) as [q|] eqn:E; [|discriminate]. injection Hn as <-.
    apply str_ptrs_bounds in E. pose proof raw_len_nonneg. pose proof build_stack_bytes_length.
    pose proof (bv_unsigned_in_range 64 sp).
    unfold env_base. rewrite unsigned_lit; [lia|]. unfold str_base, raw_len in *. lia.
  Qed.

  #[using="ph uid hw rnd IMGHI"] Lemma envp_ptr_bounds : forall i p, nth_error envp_ptrs i = Some p ->
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

#[using="Type"] Lemma find_segment_high : forall sg a n, (1 <= n)%Z -> (segs_top sg <= a)%Z -> find_segment sg a n = None.
Proof.
  induction sg as [|s0 sg IH]; intros a n Hn Ha; [reflexivity|]. cbn [find_segment segs_top] in *.
  replace (Z.leb (a + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite andb_false_r. apply IH; lia.
Qed.

#[using="Type"] Lemma init_mem_inv' : forall ph sp argv envp uid hw rnd,
  (stack_max_size <= bv_unsigned sp)%Z ->
  (bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp argv envp uid hw rnd)) <= 2^64)%Z ->
  (segs_top segs <= bv_unsigned sp - stack_max_size)%Z ->
  mem_inv segs (wrap_mem ph sp argv envp uid hw rnd).
Proof.
  intros ph sp argv envp uid hw rnd H1 H2 H3. apply init_mem_inv; try assumption.
  intros a Ha. apply find_segment_high; lia.
Qed.
End WithSegs.
