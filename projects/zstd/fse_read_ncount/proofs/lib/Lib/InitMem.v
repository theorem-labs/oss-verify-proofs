(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 08b1429 (the entry stack block runs from sp to ed_top: head, random bytes, pad, strings, exec name, 8-byte slot; the zero window starts at stack_window_lo; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes PropExec.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma extract_byte_eq : forall (v : word) (k : N),
  bv_extract k 8 v = Z_to_bv 8 (Z.shiftr (bv_unsigned v) (Z.of_N k)).
Proof. intros v k. apply bv_eq. rewrite bv_extract_unsigned, Z_to_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
Lemma word_le8_le8 : forall v : word, word_le8 v = le8 v.
Proof.
  intros v. unfold word_le8, le8, word_to_le_bytes. cbn [Z_to_le_bytes].
  rewrite !extract_byte_eq. rewrite !Z.shiftr_shiftr by lia. cbn [Z.of_N Z.add].
  rewrite Z.shiftr_0_r. reflexivity.
Qed.

Lemma flat_map_word_le8 : forall ws, flat_map word_le8 ws = u64s ws.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [flat_map u64s]. rewrite word_le8_le8, IH. reflexivity. Qed.

(* The auxv is serialized pairwise; as a word list it is the flattened pairs. *)
Lemma build_auxv_u64s : forall es : list (word * word),
  build_auxv es = u64s (flat_map (fun e => [fst e; snd e]) es).
Proof.
  induction es as [|[k v] es IH]; [reflexivity|].
  unfold build_auxv in *. cbn [flat_map fst snd app u64s].
  rewrite IH, !word_le8_le8, <- app_assoc. reflexivity.
Qed.

Lemma lit_sub_nat : forall (t : word) (n : nat), t - nat_to_word n = Z_to_bv 64 (bv_unsigned t - Z.of_nat n).
Proof.
  intros t n. apply bv_eq. rewrite bv_sub_unsigned, !Z_to_bv_unsigned. unfold nat_to_word.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Zminus_mod_idemp_r. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma rw_cells_recast : forall m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells segs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* The initial memory at 08b1429: the block from sp to ed_top, zeros on
   [stack_window_lo, sp), nothing elsewhere. *)
Section Init.
  Variables (inp : ProcInput) (mbase : word) (ph : PhdrInfo) (entry sp : word) (draw : EntryDraw).
  Notation m0 := (wrap_mem inp mbase ph entry sp draw).
  Notation img := (entry_stack_image inp mbase ph entry sp draw).
  Notation LOW := (stack_window_lo (in_kernel inp) mbase draw).
  Hypothesis IMGHI : (bv_unsigned sp + Z.of_nat (length img) <= 2^64)%Z.
  Hypothesis LOWSP : (LOW <= bv_unsigned sp)%Z.
  Hypothesis LOW0 : (0 <= LOW)%Z.

  Lemma init_at : forall a : word,
    m0 a = if (Z.leb (bv_unsigned sp) (bv_unsigned a)) then
             (if Z.ltb (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length img))
              then nth_error img (Z.to_nat (bv_unsigned a - bv_unsigned sp)) else None)
           else if Z.leb LOW (bv_unsigned a) then Some (Z_to_bv 8 0) else None.
  Proof.
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

  Lemma init_none : forall a : word, (bv_unsigned a < LOW)%Z -> m0 a = None.
  Proof.
    intros a Ha. rewrite init_at.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia).
    replace (Z.leb LOW (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia).
    reflexivity.
  Qed.

  Lemma init_none_above : forall a : word, (bv_unsigned sp + Z.of_nat (length img) <= bv_unsigned a)%Z -> m0 a = None.
  Proof.
    intros a Ha. rewrite init_at.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length img))) with false by (symmetry; apply Z.ltb_ge; lia).
    reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma init_stack_bytes : bytes_at segs m0 (bv_unsigned sp) img.
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
    split; [lia|]. split; [lia|]. intros i Hi. unfold mrd. rewrite init_at.
    rewrite wa_unsigned by lia.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned sp + Z.of_nat i)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned sp + Z.of_nat i - bv_unsigned sp) (Z.of_nat (length img))) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (Z.to_nat (bv_unsigned sp + Z.of_nat i - bv_unsigned sp)) with i by lia.
    destruct (nth_error img i) eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
  Qed.

  Lemma init_stack_wr : wr_at segs m0 (bv_unsigned sp) (Z.of_nat (length img)).
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
    split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite init_at, wa_unsigned by lia.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned sp + i)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned sp + i - bv_unsigned sp) (Z.of_nat (length img))) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (nth_error img (Z.to_nat (bv_unsigned sp + i - bv_unsigned sp))) eqn:E; [discriminate|].
    apply nth_error_None in E. lia.
  Qed.

  Lemma init_stack_u8arr : u8arr segs m0 (bv_unsigned sp) img.
  Proof. split; [apply init_stack_bytes | apply init_stack_wr]. Qed.

  (* [comment removed for export] *)
  Lemma init_stk : stk segs m0 LOW (bv_unsigned sp).
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
    split; [lia|]. split; [lia|]. intros a Ha.
    assert (E : m0 (wa a) = Some (Z_to_bv 8 0)).
    { rewrite init_at, wa_unsigned by lia.
      replace (Z.leb (bv_unsigned sp) a) with false by (symmetry; apply Z.leb_gt; lia).
      replace (Z.leb LOW a) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
    split. { unfold wview. rewrite E. discriminate. } exists (Z_to_bv 8 0). unfold mrd. rewrite E. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Hypothesis SEGS_LOW : forall a : word, (LOW <= bv_unsigned a)%Z -> find_segment segs (bv_unsigned a) 1 = None.
  Lemma init_mem_inv : mem_inv segs m0.
  Proof.
    intros a b H. unfold ro_addr.
    destruct (Z.lt_ge_cases (bv_unsigned a) LOW) as [Hl|Hh].
    - rewrite init_none in H by lia. discriminate.
    - rewrite SEGS_LOW by lia. reflexivity.
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma str_ptrs_bounds : forall strs base i p, nth_error (str_ptrs base strs) i = Some p ->
  (base <= p /\ p < base + total_arg_bytes strs)%Z.
Proof.
  induction strs as [|s0 strs IH]; intros base [|i] p Hn; cbn in Hn; try discriminate.
  - injection Hn as <-. rewrite total_arg_bytes_cons. pose proof (total_arg_bytes_nonneg strs). lia.
  - apply IH in Hn. rewrite total_arg_bytes_cons. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* The block's layout at 08b1429, as offsets from sp and from top.           *)
(* ------------------------------------------------------------------------- *)

Definition argc (argv : list (list byte)) : Z := Z.of_nat (length argv).
Definition envc (envp : list (list byte)) : Z := Z.of_nat (length envp).
(* The string area: argv strings, envp strings, the exec name, each NUL-terminated. *)
Definition lstr (argv envp : list (list byte)) (execfn : list byte) : Z :=
  Z.of_nat (launch_string_bytes argv envp execfn).
(* The head C: argc, the pointer arrays, the auxv, the gap and the random bytes. *)
Definition hsz (rseq : bool) (argv envp : list (list byte)) : Z :=
  Z.of_nat (block_head_size rseq argv envp).
Definition str_base (top : word) (argv envp : list (list byte)) (execfn : list byte) : Z :=
  (bv_unsigned top - 8 - lstr argv envp execfn)%Z.
Definition argv_ptrs (top : word) (argv envp : list (list byte)) (execfn : list byte) : list word :=
  map (Z_to_bv 64) (str_ptrs (str_base top argv envp execfn) argv).
Definition env_base (top : word) (argv envp : list (list byte)) (execfn : list byte) : Z :=
  (str_base top argv envp execfn + total_arg_bytes argv)%Z.
Definition envp_ptrs (top : word) (argv envp : list (list byte)) (execfn : list byte) : list word :=
  map (Z_to_bv 64) (str_ptrs (env_base top argv envp execfn) envp).
Definition execfn_base (top : word) (argv envp : list (list byte)) (execfn : list byte) : Z :=
  (env_base top argv envp execfn + total_arg_bytes envp)%Z.
Definition rnd_addr (sp : word) (rseq : bool) (argv envp : list (list byte)) : Z :=
  (bv_unsigned sp + hsz rseq argv envp - 16)%Z.
Definition execfn_ptr (top : word) (execfn : list byte) : Z :=
  (bv_unsigned top - (8 + Z.of_nat (length execfn) + 1))%Z.
Definition auxv_words (la : LaunchAuxv) (ph : PhdrInfo) (entry uid gid hw : word) (sp top : word)
    (argv envp : list (list byte)) (execfn : list byte) : list word :=
  flat_map (fun e => [fst e; snd e])
    (auxv_entries la ph entry uid gid hw (Z_to_bv 64 (rnd_addr sp (la_rseq la) argv envp))
       (Z_to_bv 64 (execfn_ptr top execfn))).
Definition rnd_bytes (draw : EntryDraw) : list byte := at_random_bytes (ed_random draw).
Definition gap_len (argv envp : list (list byte)) : nat := (8 * (block_items argv envp mod 2))%nat.
Definition head_words (la : LaunchAuxv) (ph : PhdrInfo) (entry uid gid hw : word) (sp top : word)
    (argv envp : list (list byte)) (execfn : list byte) : list word :=
  Z_to_bv 64 (argc argv) :: argv_ptrs top argv envp execfn ++ [Z_to_bv 64 0]
    ++ envp_ptrs top argv envp execfn ++ [Z_to_bv 64 0] ++ auxv_words la ph entry uid gid hw sp top argv envp execfn.

Lemma rnd_bytes_length : forall draw, length (rnd_bytes draw) = 16%nat.
Proof. reflexivity. Qed.

Lemma length_auxv_words : forall la ph entry uid gid hw sp top argv envp execfn,
  length (auxv_words la ph entry uid gid hw sp top argv envp execfn) = (2 * auxv_count (la_rseq la))%nat.
Proof. intros [ehdr c msz [|]] ph entry uid gid hw sp top argv envp execfn; reflexivity. Qed.

Lemma lstr_eq : forall argv envp execfn,
  lstr argv envp execfn = (total_arg_bytes argv + total_arg_bytes envp + Z.of_nat (length execfn) + 1)%Z.
Proof.
  intros. unfold lstr, launch_string_bytes.
  pose proof (flatten_strings_length argv). pose proof (flatten_strings_length envp). lia.
Qed.

Lemma hsz_eq : forall rseq argv envp,
  hsz rseq argv envp
  = (8 * (argc argv + envc envp + 3) + 16 * Z.of_nat (auxv_count rseq) + Z.of_nat (gap_len argv envp) + 16)%Z.
Proof.
  intros. unfold hsz, block_head_size, gap_len, auxv_size, argc, envc. cbv zeta.
  set (G := (block_items argv envp mod 2)%nat). unfold block_items. lia.
Qed.

Lemma gap_len_bound : forall argv envp, (Z.of_nat (gap_len argv envp) <= 8)%Z.
Proof.
  intros. unfold gap_len. pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)). lia.
Qed.

Lemma string_base_addr_eq : forall top argv envp execfn,
  string_base_addr top argv envp execfn = Z_to_bv 64 (str_base top argv envp execfn).
Proof.
  intros. unfold string_base_addr, str_base, lstr. rewrite lit_sub_nat. f_equal. lia.
Qed.

Lemma at_random_ptr_eq : forall sp rseq argv envp,
  at_random_ptr sp rseq argv envp = Z_to_bv 64 (rnd_addr sp rseq argv envp).
Proof.
  intros. unfold at_random_ptr, rnd_addr, hsz, nat_to_word.
  rewrite <- (Z_to_bv_bv_unsigned sp) at 1. rewrite lit_add_lit. f_equal.
  unfold block_head_size. cbv zeta. set (G := (block_items argv envp mod 2)%nat). lia.
Qed.

Lemma at_execfn_ptr_eq : forall top execfn,
  at_execfn_ptr top execfn = Z_to_bv 64 (execfn_ptr top execfn).
Proof. intros. unfold at_execfn_ptr, execfn_ptr. rewrite lit_sub_nat. f_equal. lia. Qed.

Lemma build_stack_bytes_eq : forall la ph entry sp top argv envp execfn uid gid hw draw,
  build_stack_bytes la ph entry sp top argv envp execfn uid gid hw draw
  = u64s (head_words la ph entry uid gid hw sp top argv envp execfn)
    ++ repeat (Z_to_bv 8 0) (gap_len argv envp)
    ++ rnd_bytes draw
    ++ repeat (Z_to_bv 8 0) (block_pad_len (la_rseq la) sp top argv envp execfn)
    ++ flatten_strings argv ++ flatten_strings envp ++ execfn ++ [Z_to_bv 8 0]
    ++ repeat (Z_to_bv 8 0) 8.
Proof.
  intros. unfold build_stack_bytes. cbv zeta.
  rewrite string_base_addr_eq, string_addrs_eq. cbv beta iota.
  rewrite string_addrs_eq. cbv beta iota.
  rewrite at_random_ptr_eq, at_execfn_ptr_eq. unfold auxv_bytes. rewrite build_auxv_u64s.
  rewrite !flat_map_word_le8, !word_le8_le8.
  unfold head_words, auxv_words, argv_ptrs, envp_ptrs, env_base, rnd_bytes, gap_len.
  cbn [u64s]. rewrite !u64s_app. cbn [u64s]. rewrite !app_nil_r, <- !app_assoc.
  reflexivity.
Qed.

Lemma length_u64s_head : forall la ph entry uid gid hw sp top argv envp execfn,
  Z.of_nat (length (u64s (head_words la ph entry uid gid hw sp top argv envp execfn)))
  = (8 * (argc argv + envc envp + 3) + 16 * Z.of_nat (auxv_count (la_rseq la)))%Z.
Proof.
  intros. rewrite u64s_length. unfold head_words. cbn [length]. rewrite !app_length. cbn [length].
  rewrite length_auxv_words. unfold argv_ptrs, envp_ptrs. rewrite !map_length, !str_ptrs_length.
  unfold argc, envc. lia.
Qed.

(* The block runs from sp to top when the pad is not clamped. *)
Lemma build_stack_bytes_length_top : forall la ph entry sp top argv envp execfn uid gid hw draw,
  (bv_unsigned sp + hsz (la_rseq la) argv envp + lstr argv envp execfn + 8 <= bv_unsigned top)%Z ->
  Z.of_nat (length (build_stack_bytes la ph entry sp top argv envp execfn uid gid hw draw))
  = (bv_unsigned top - bv_unsigned sp)%Z.
Proof.
  intros la ph entry sp top argv envp execfn uid gid hw draw H.
  rewrite length_build_stack_bytes. unfold block_pad_len. unfold hsz, lstr in H.
  rewrite !Nat2Z.inj_add. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma bytes_at_slice : forall segs m a bs off k,
  bytes_at segs m a bs -> (off + k <= length bs)%nat ->
  bytes_at segs m (a + Z.of_nat off) (firstn k (skipn off bs)).
Proof.
  intros segs0 m a bs off k H Hk.
  rewrite <- (firstn_skipn off bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length in H. replace (Nat.min off (length bs)) with off in H by lia.
  rewrite <- (firstn_skipn k (skipn off bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma wr_at_sub : forall segs m a n a' n', wr_at segs m a n -> (a <= a')%Z -> (a' + n' <= a + n)%Z -> wr_at segs m a' n'.
Proof.
  intros segs0 m a n a' n' (Ha & Hn & H) H1 H2. split; [lia|]. split; [lia|].
  intros i Hi. replace (a' + i)%Z with (a + (a' - a + i))%Z by lia. apply H. lia.
Qed.

Lemma rw_cells_of_parts : forall segs m A cs,
  cells_wf cs -> bytes_at segs m A (cells_bytes cs) -> wr_at segs m A (Z.of_nat (cells_size cs)) -> rw_cells segs m A cs.
Proof. intros segs0 m A cs Hwf Hb Hw. split; [split; assumption| exact Hw]. Qed.

(* The block's pieces, read off any memory that holds the block at sp. *)
Section Pieces.
  Variables (m : word -> option byte) (la : LaunchAuxv) (ph : PhdrInfo) (entry sp top : word)
            (argv envp : list (list byte)) (execfn : list byte) (uid gid hw : word) (draw : EntryDraw).
  Notation usp := (bv_unsigned sp).
  Notation img := (build_stack_bytes la ph entry sp top argv envp execfn uid gid hw draw).
  Hypothesis IMG : bytes_at segs m usp img.
  Hypothesis PADOK : (usp + hsz (la_rseq la) argv envp + lstr argv envp execfn + 8 <= bv_unsigned top)%Z.

  Lemma stack_pieces :
    bytes_at segs m usp (le8 (Z_to_bv 64 (argc argv))) /\
    bytes_at segs m (usp + 8) (u64s (argv_ptrs top argv envp execfn ++ [Z_to_bv 64 0])) /\
    bytes_at segs m (usp + 8 * (argc argv + 2)) (u64s (envp_ptrs top argv envp execfn ++ [Z_to_bv 64 0])) /\
    bytes_at segs m (usp + 8 * (argc argv + envc envp + 3)) (u64s (auxv_words la ph entry uid gid hw sp top argv envp execfn)) /\
    bytes_at segs m (rnd_addr sp (la_rseq la) argv envp) (rnd_bytes draw) /\
    bytes_at segs m (str_base top argv envp execfn) (flatten_strings argv) /\
    bytes_at segs m (env_base top argv envp execfn) (flatten_strings envp).
  Proof.
    pose proof IMG as B. rewrite build_stack_bytes_eq in B.
    unfold head_words in B. cbn [u64s] in B. rewrite !u64s_app in B. cbn [u64s] in B. rewrite !app_nil_r in B.
    repeat rewrite <- app_assoc in B.
    pose proof (hsz_eq (la_rseq la) argv envp) as HS. pose proof (lstr_eq argv envp execfn) as HL.
    pose proof (total_arg_bytes_nonneg argv). pose proof (total_arg_bytes_nonneg envp).
    pose proof (flatten_strings_length argv) as L1. pose proof (flatten_strings_length envp) as L2.
    assert (PAD : Z.of_nat (block_pad_len (la_rseq la) sp top argv envp execfn)
                  = (bv_unsigned top - 8 - lstr argv envp execfn - usp - hsz (la_rseq la) argv envp)%Z).
    { unfold block_pad_len. unfold hsz, lstr in *. rewrite Z2Nat.id by lia. reflexivity. }
    apply bytes_at_app in B. destruct B as [B0 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B1 B]. rewrite u64s_length in B. unfold argv_ptrs in B. rewrite map_length, str_ptrs_length in B.
    apply bytes_at_app in B. destruct B as [B2 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B3 B]. rewrite u64s_length in B. unfold envp_ptrs in B. rewrite map_length, str_ptrs_length in B.
    apply bytes_at_app in B. destruct B as [B4 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B5 B]. rewrite u64s_length, length_auxv_words in B.
    apply bytes_at_app in B. destruct B as [B6 B]. rewrite repeat_length in B.
    apply bytes_at_app in B. destruct B as [B7 B]. rewrite rnd_bytes_length in B.
    apply bytes_at_app in B. destruct B as [B8 B]. rewrite repeat_length in B.
    apply bytes_at_app in B. destruct B as [B9 B].
    apply bytes_at_app in B. destruct B as [B10 _].
    unfold argc, envc in *.
    repeat match goal with |- _ /\ _ => split end.
    - exact B0.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app segs m _ _ _)). split.
      + replace (usp + 8)%Z with (usp + Z.of_nat 8)%Z by lia. exact B1.
      + rewrite u64s_length. unfold argv_ptrs at 1. rewrite map_length, str_ptrs_length.
        replace (usp + 8 + Z.of_nat (8 * length argv))%Z with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv))%Z by lia. exact B2.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app segs m _ _ _)). split.
      + replace (usp + 8 * (Z.of_nat (length argv) + 2))%Z with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8)%Z by lia. exact B3.
      + rewrite u64s_length. unfold envp_ptrs at 1. rewrite map_length, str_ptrs_length.
        replace (usp + 8 * (Z.of_nat (length argv) + 2) + Z.of_nat (8 * length envp))%Z
          with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp))%Z by lia. exact B4.
    - replace (usp + 8 * (Z.of_nat (length argv) + Z.of_nat (length envp) + 3))%Z
        with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8)%Z by lia. exact B5.
    - match type of B7 with bytes_at _ _ ?A _ => replace (rnd_addr sp (la_rseq la) argv envp) with A; [exact B7|] end.
      unfold rnd_addr. rewrite HS. lia.
    - match type of B9 with bytes_at _ _ ?A _ => replace (str_base top argv envp execfn) with A; [exact B9|] end.
      unfold str_base. rewrite PAD, HS. lia.
    - match type of B10 with bytes_at _ _ ?A _ => replace (env_base top argv envp execfn) with A; [exact B10|] end.
      unfold env_base, str_base. rewrite PAD, HS, L1. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma init_argv_string : forall i s, nth_error argv i = Some s ->
    exists p, nth_error (argv_ptrs top argv envp execfn) i = Some (Z_to_bv 64 p)
      /\ (str_base top argv envp execfn <= p)%Z
      /\ (p + Z.of_nat (length s) + 1 <= env_base top argv envp execfn)%Z
      /\ bytes_at segs m p (s ++ [Z_to_bv 8 0]).
  Proof.
    intros i s Hn. destruct (str_ptrs_nth argv (str_base top argv envp execfn) i s Hn) as (off & Hp & Ho & Ht & Hf).
    exists (str_base top argv envp execfn + off)%Z. split. { unfold argv_ptrs. rewrite nth_error_map, Hp. reflexivity. }
    split; [lia|]. split. { unfold env_base. lia. }
    destruct stack_pieces as (_ & _ & _ & _ & _ & B6 & _).
    pose proof (flatten_strings_length argv).
    pose proof (bytes_at_slice segs m (str_base top argv envp execfn) (flatten_strings argv) (Z.to_nat off) (length s + 1) B6 ltac:(lia)) as B.
    rewrite Hf in B. replace (str_base top argv envp execfn + Z.of_nat (Z.to_nat off))%Z with (str_base top argv envp execfn + off)%Z in B by lia.
    exact B.
  Qed.

  Lemma argv_ptrs_length : length (argv_ptrs top argv envp execfn) = length argv.
  Proof. unfold argv_ptrs. rewrite map_length. apply str_ptrs_length. Qed.
  Lemma envp_ptrs_length : length (envp_ptrs top argv envp execfn) = length envp.
  Proof. unfold envp_ptrs. rewrite map_length. apply str_ptrs_length. Qed.

  Lemma layout_bounds :
    (usp + hsz (la_rseq la) argv envp <= str_base top argv envp execfn)%Z /\
    (str_base top argv envp execfn <= env_base top argv envp execfn)%Z /\
    (env_base top argv envp execfn <= execfn_base top argv envp execfn)%Z /\
    (execfn_base top argv envp execfn + Z.of_nat (length execfn) + 1 + 8 = bv_unsigned top)%Z.
  Proof.
    pose proof (lstr_eq argv envp execfn). pose proof (total_arg_bytes_nonneg argv). pose proof (total_arg_bytes_nonneg envp).
    unfold execfn_base, env_base, str_base. lia.
  Qed.

  Lemma argv_ptr_bounds : forall i p, nth_error (argv_ptrs top argv envp execfn) i = Some p ->
    (str_base top argv envp execfn <= bv_unsigned p < env_base top argv envp execfn)%Z.
  Proof.
    intros i p Hn. unfold argv_ptrs in Hn. rewrite nth_error_map in Hn.
    destruct (nth_error (str_ptrs (str_base top argv envp execfn) argv) i) as [q|] eqn:E; [|discriminate]. injection Hn as <-.
    apply str_ptrs_bounds in E. pose proof layout_bounds as (LB1 & LB2 & LB3 & LB4).
    pose proof (bv_unsigned_in_range 64 sp) as [R1 _].
    assert (R2 : (bv_unsigned top < 2^64)%Z) by (pose proof (bv_unsigned_in_range 64 top) as [_ R]; unfold bv_modulus in R; cbn in R; lia).
    pose proof (Nat2Z.is_nonneg (block_head_size (la_rseq la) argv envp)). unfold hsz in LB1.
    unfold env_base in *. rewrite unsigned_lit by lia. lia.
  Qed.

  Lemma envp_ptr_bounds : forall i p, nth_error (envp_ptrs top argv envp execfn) i = Some p ->
    (env_base top argv envp execfn <= bv_unsigned p < execfn_base top argv envp execfn)%Z.
  Proof.
    intros i p Hn. unfold envp_ptrs in Hn. rewrite nth_error_map in Hn.
    destruct (nth_error (str_ptrs (env_base top argv envp execfn) envp) i) as [q|] eqn:E; [|discriminate]. injection Hn as <-.
    apply str_ptrs_bounds in E. pose proof layout_bounds as (LB1 & LB2 & LB3 & LB4).
    pose proof (bv_unsigned_in_range 64 sp) as [R1 _].
    assert (R2 : (bv_unsigned top < 2^64)%Z) by (pose proof (bv_unsigned_in_range 64 top) as [_ R]; unfold bv_modulus in R; cbn in R; lia).
    pose proof (Nat2Z.is_nonneg (block_head_size (la_rseq la) argv envp)). unfold hsz in LB1.
    unfold execfn_base in *. rewrite unsigned_lit by lia. lia.
  Qed.
End Pieces.

(* ------------------------------------------------------------------------- *)
(* Launch facts: what valid_launch and entry_launch_ok_va give the block.    *)
(* Copies of the model's StepTac/StoreOk lemmas (AS/StepTac.v, AS/StoreOk.v). *)
(* ------------------------------------------------------------------------- *)

Lemma im_block_head_size_le : forall rseq argv envp,
  (Z.of_nat (block_head_size rseq argv envp)
   <= 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 512)%Z.
Proof.
  intros rseq argv envp.
  unfold block_head_size, block_items, auxv_size, auxv_count.
  pose proof (Nat.mod_upper_bound (length argv + length envp + 3) 2 ltac:(lia)).
  destruct rseq; lia.
Qed.

Lemma im_launch_top_minus_sp : forall inp (top sp : word),
  valid_launch inp -> valid_launch_sp top inp sp ->
  (bv_unsigned top - bv_unsigned sp <= 2101782)%Z.
Proof.
  intros inp top sp [_ Hb] [_ [Hlo _]].
  unfold launch_bytes, e2big_limit in Hb.
  unfold launch_sp_lo, align_down16 in Hlo.
  pose proof (im_block_head_size_le (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)).
  pose proof (Z.mod_pos_bound
    (bv_unsigned top - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))
     - 4095) 16 ltac:(lia)).
  lia.
Qed.

Lemma im_launch_padok : forall inp (top sp : word),
  valid_launch_sp top inp sp ->
  (bv_unsigned sp + hsz (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)
   + lstr (in_argv inp) (in_envp inp) (in_execfn inp) + 8 <= bv_unsigned top)%Z.
Proof.
  intros inp top sp [_ [_ Hhi]].
  unfold launch_sp_hi, align_down16 in Hhi. unfold hsz, lstr.
  pose proof (Z.mod_pos_bound
    (bv_unsigned top - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))) 16 ltac:(lia)).
  lia.
Qed.

Lemma im_page_round_up_Z_aligned : forall n,
  (n mod page_size = 0)%Z -> page_round_up_Z n = n.
Proof.
  intros n Hn. unfold page_round_up_Z, page_size in *.
  apply Z.mod_divide in Hn; [|lia]. destruct Hn as [k Hk]. subst n.
  replace (k * 4096 + 4096 - 1)%Z with (k * 4096 + 4095)%Z by lia.
  rewrite Z.div_add_l by lia.
  replace (4095 / 4096)%Z with 0%Z by reflexivity. lia.
Qed.

Lemma im_mmap_gap_sv48 : forall kb,
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

Lemma im_mmap_gap_sv48_mod : forall kb,
  (mmap_gap Sv48 kb mod page_size = 0)%Z.
Proof.
  intros kb.
  assert (H4096 : forall x : Z, ((4096 * x) mod 4096 = 0)%Z)
    by (intro x; rewrite Z.mul_comm; apply Z_mod_mult).
  rewrite im_mmap_gap_sv48. cbv zeta.
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

Lemma im_launch_base_gap_le : forall kb mbase,
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
    - apply Z.mod_divide; [unfold page_size; lia|]. apply im_mmap_gap_sv48_mod.
    - exists r. unfold page_size. lia. }
  rewrite im_page_round_up_Z_aligned
    by (apply Z.mod_divide; [unfold page_size; lia | exact Hdiv]).
  rewrite im_mmap_gap_sv48. cbv zeta.
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

(* The usable stack below sp: at least 6144513 bytes (the model's
   [stack_window_depth]); 8 MiB counted from ed_top less the block. *)
Definition im_stack_depth : Z := 6144513.

Lemma launch_facts : forall inp (sp brk mbase : word) draw,
  valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp ->
  (bv_unsigned sp mod 16 = 0)%Z /\
  (bv_unsigned sp + hsz (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)
   + lstr (in_argv inp) (in_envp inp) (in_execfn inp) + 8 <= bv_unsigned (ed_top draw))%Z /\
  (bv_unsigned (ed_top draw) - bv_unsigned sp <= 2101782)%Z /\
  (bv_unsigned (ed_top draw) <= 0x800000000000)%Z /\
  (stack_window_lo (in_kernel inp) mbase draw <= bv_unsigned sp - im_stack_depth)%Z /\
  (bv_unsigned sp - stack_max_size <= stack_window_lo (in_kernel inp) mbase draw)%Z.
Proof.
  intros inp sp brk mbase draw Hvl (Htop & Hsp & Hbase).
  pose proof (im_launch_top_minus_sp inp (ed_top draw) sp Hvl Hsp) as Hd.
  pose proof (im_launch_padok inp (ed_top draw) sp Hsp) as Hp.
  pose proof (im_launch_base_gap_le (in_kernel inp) mbase Hbase) as Hg.
  pose proof (Nat2Z.is_nonneg (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
  pose proof (Nat2Z.is_nonneg (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).
  unfold hsz, lstr in Hp.
  pose proof Hsp as (H16 & _).
  destruct Htop as (_ & Hhi & Hlo).
  split; [exact H16|]. split; [unfold hsz, lstr; lia|]. split; [exact Hd|].
  split. { unfold va_stack_top, sp_window_hi in Hhi. exact Hhi. }
  split.
  - unfold stack_window_lo, im_stack_depth, stack_max_size,
      va_stack_top, sp_window_hi, stack_rnd_max, page_size in *.
    destruct (kb_aslr (in_kernel inp)); cbv beta iota in Hg, Hlo; apply Z.max_lub; lia.
  - unfold stack_window_lo. apply Z.le_trans with (bv_unsigned (ed_top draw) - stack_max_size)%Z; [lia | apply Z.le_max_l].
Qed.

Lemma launch_image_length : forall inp (sp brk mbase : word) ph entry draw,
  valid_launch inp ->
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp ->
  Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw)) = (bv_unsigned (ed_top draw) - bv_unsigned sp)%Z.
Proof.
  intros inp sp brk mbase ph entry draw Hvl Hok.
  pose proof (launch_facts inp sp brk mbase draw Hvl Hok) as (_ & Hp & _).
  unfold entry_stack_image. apply build_stack_bytes_length_top. exact Hp.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma testbit_bv_wrap : forall n z i, (0 <= i)%Z ->
  Z.testbit (bv_wrap n z) i = if (i <? Z.of_N n)%Z then Z.testbit z i else false.
Proof.
  intros n z i Hi. unfold bv_wrap, bv_modulus.
  destruct (Z.ltb_spec i (Z.of_N n)).
  - apply Z.mod_pow2_bits_low. lia.
  - apply Z.mod_pow2_bits_high. lia.
Qed.

(* [comment removed for export] *)
Lemma extract8_via64 : forall (r : bv 128) (h k : N), (k + 8 <= 64)%N ->
  bv_extract (h + k) 8 r = Z_to_bv 8 (Z.shiftr (bv_unsigned (Z_to_bv 64 (bv_unsigned (bv_extract h 64 r)))) (Z.of_N k)).
Proof.
  intros r h k Hk. apply bv_eq. rewrite Z_to_bv_bv_unsigned. rewrite !bv_extract_unsigned, Z_to_bv_unsigned.
  apply Z.bits_inj'. intros i Hi.
  rewrite !testbit_bv_wrap, !Z.shiftr_spec, testbit_bv_wrap, Z.shiftr_spec by lia.
  change (Z.of_N 8) with 8%Z. destruct (Z.ltb_spec i 8); [|reflexivity].
  replace (i + Z.of_N k <? Z.of_N 64)%Z with true by (symmetry; apply Z.ltb_lt; lia). f_equal. lia.
Qed.

Definition draw_canary (d : EntryDraw) : Z := bv_unsigned (bv_extract 0 64 (ed_random d)).
Definition draw_secret (d : EntryDraw) : Z := bv_unsigned (bv_extract 64 64 (ed_random d)).

Lemma draw_canary_range : forall d, (0 <= draw_canary d < 2^64)%Z.
Proof. intros d. unfold draw_canary. pose proof (bv_unsigned_in_range 64 (bv_extract 0 64 (ed_random d))) as H. unfold bv_modulus in H. cbn in H. lia. Qed.
Lemma draw_secret_range : forall d, (0 <= draw_secret d < 2^64)%Z.
Proof. intros d. unfold draw_secret. pose proof (bv_unsigned_in_range 64 (bv_extract 64 64 (ed_random d))) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

Lemma at_random_bytes_split : forall r : bv 128,
  at_random_bytes r = le8 (Z_to_bv 64 (bv_unsigned (bv_extract 0 64 r))) ++ le8 (Z_to_bv 64 (bv_unsigned (bv_extract 64 64 r))).
Proof.
  intros r. unfold at_random_bytes, le8, word_to_le_bytes. cbn [Z_to_le_bytes app].
  rewrite !Z.shiftr_shiftr by lia. cbn [Z.add].
  rewrite (extract8_via64 _ 0 0), (extract8_via64 _ 0 8), (extract8_via64 _ 0 16), (extract8_via64 _ 0 24),
          (extract8_via64 _ 0 32), (extract8_via64 _ 0 40), (extract8_via64 _ 0 48), (extract8_via64 _ 0 56),
          (extract8_via64 _ 64 0), (extract8_via64 _ 64 8), (extract8_via64 _ 64 16), (extract8_via64 _ 64 24),
          (extract8_via64 _ 64 32), (extract8_via64 _ 64 40), (extract8_via64 _ 64 48), (extract8_via64 _ 64 56) by lia.
  cbn [Z.of_N N.add Pos.add]. rewrite !Z.shiftr_0_r. reflexivity.
Qed.

Lemma rnd_bytes_split : forall d,
  rnd_bytes d = le8 (Z_to_bv 64 (draw_canary d)) ++ le8 (Z_to_bv 64 (draw_secret d)).
Proof. intros d. apply at_random_bytes_split. Qed.

(* [comment removed for export] *)
Definition entry_atop (en : ExecEntry) : Z := (bv_unsigned (en_sp en) - stack_max_size)%Z.
Definition entry_secret (en : ExecEntry) : Z := draw_secret (en_draw en).
Definition entry_canary (en : ExecEntry) : Z := draw_canary (en_draw en).

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

Lemma init_mem_inv' : forall inp mbase ph entry sp draw,
  (0 <= stack_window_lo (in_kernel inp) mbase draw)%Z ->
  (stack_window_lo (in_kernel inp) mbase draw <= bv_unsigned sp)%Z ->
  (segs_top segs <= stack_window_lo (in_kernel inp) mbase draw)%Z ->
  mem_inv segs (wrap_mem inp mbase ph entry sp draw).
Proof.
  intros inp mbase ph entry sp draw H0 H1 H2. apply init_mem_inv; try assumption.
  intros a Ha. apply find_segment_high; lia.
Qed.
End WithSegs.

(* The launch values the old entry image did not carry (08b1429): the
   auxv's launch record, the exec name, the gid and the stack VMA's end.
   Library sections that reason about the entry block take them as one
   implicit instance; the top level builds it from the input and entry. *)
Class launchT : Type := LaunchT {
  L_LA : LaunchAuxv;
  L_EXECFN : list byte;
  L_GID : word;
  L_TOP : word
}.

Definition launch_of (inp : ProcInput) (sp : word) (mbase : word) (draw : EntryDraw) : launchT :=
  {| L_LA := launch_auxv inp sp mbase; L_EXECFN := in_execfn inp; L_GID := in_gid inp; L_TOP := ed_top draw |}.

Lemma entry_stack_image_launch_of : forall inp mbase ph entry sp draw,
  entry_stack_image inp mbase ph entry sp draw
  = @build_stack_bytes (@L_LA (launch_of inp sp mbase draw)) ph entry sp (@L_TOP (launch_of inp sp mbase draw))
      (in_argv inp) (in_envp inp) (@L_EXECFN (launch_of inp sp mbase draw))
      (in_uid inp) (@L_GID (launch_of inp sp mbase draw)) (in_hwcap inp) draw.
Proof. reflexivity. Qed.
