(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS ; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11. *)
(* Lib/InitMem at rocq-LPS = the simdjson donor's ported
   Lib/InitMem.v (the proof repository ) word for word but its one import line (our Lib/Tac Requires the
   per-binary Lib/Image). This package's r30q2 Lib/InitMem had the donor's PRE-port statements, all of them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Bytes.
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

Lemma wr_at_sub : forall m a n a' n', wr_at segs m a n -> (a <= a')%Z -> (a' + n' <= a + n)%Z -> wr_at segs m a' n'.
Proof.
  intros m a n a' n' (Ha & Hn & H) H1 H2. split; [lia|]. split; [lia|].
  intros i Hi. replace (a' + i)%Z with (a + (a' - a + i))%Z by lia. apply H. lia.
Qed.

Lemma rw_cells_of_parts : forall m A cs,
  cells_wf cs -> bytes_at segs m A (cells_bytes cs) -> wr_at segs m A (Z.of_nat (cells_size cs)) -> rw_cells segs m A cs.
Proof. intros m A cs Hwf Hb Hw. split; [split; assumption| exact Hw]. Qed.

Lemma bytes_at_eqa : forall m a b bs, bytes_at segs m a bs -> a = b -> bytes_at segs m b bs.
Proof. intros m a b bs H E. subst b. exact H. Qed.

Lemma bytes_at_slice : forall m a bs off k,
  bytes_at segs m a bs -> (off + k <= length bs)%nat ->
  bytes_at segs m (a + Z.of_nat off) (firstn k (skipn off bs)).
Proof.
  intros m a bs off k H Hk.
  rewrite <- (firstn_skipn off bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length in H. replace (Nat.min off (length bs)) with off in H by lia.
  rewrite <- (firstn_skipn k (skipn off bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

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

(* The initial memory of a launch: Linux's block from [sp] up to the stack
   VMA's end, zero bytes in [[stack_window_lo, sp)], nothing elsewhere. *)
Section Init.

  Variables (inp : ProcInput) (mbase : word) (ph : PhdrInfo) (entry sp : word) (draw : EntryDraw).
  Notation m0 := (wrap_mem inp mbase ph entry sp draw).
  Notation ent := (entry_stack_image inp mbase ph entry sp draw).
  Notation wlo := (stack_window_lo (in_kernel inp) mbase draw).

  Lemma init_at : forall a : word,
    m0 a = if (Z.leb (bv_unsigned sp) (bv_unsigned a)) then
             (if Z.ltb (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length ent))
              then nth_error ent (Z.to_nat (bv_unsigned a - bv_unsigned sp)) else None)
           else if Z.leb wlo (bv_unsigned a) then Some (Z_to_bv 8 0) else None.
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

  Lemma init_at_block : forall a : word,
    (bv_unsigned sp <= bv_unsigned a < bv_unsigned sp + Z.of_nat (length ent))%Z ->
    m0 a = nth_error ent (Z.to_nat (bv_unsigned a - bv_unsigned sp)).
  Proof.
    intros a Ha. rewrite init_at.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length ent))) with true by (symmetry; apply Z.ltb_lt; lia).
    reflexivity.
  Qed.

  Lemma init_none : forall a : word,
    (bv_unsigned a < bv_unsigned sp)%Z -> (bv_unsigned a < wlo)%Z -> m0 a = None.
  Proof.
    intros a H1 H2. rewrite init_at.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia).
    replace (Z.leb wlo (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia).
    reflexivity.
  Qed.

  Lemma init_none_above : forall a : word, (bv_unsigned sp + Z.of_nat (length ent) <= bv_unsigned a)%Z -> m0 a = None.
  Proof.
    intros a Ha. rewrite init_at.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length ent))) with false by (symmetry; apply Z.ltb_ge; lia).
    reflexivity.
  Qed.

  Lemma init_stk : forall lo, (wlo <= lo)%Z -> (0 <= lo)%Z -> stk segs m0 lo (bv_unsigned sp).
  Proof.
    intros lo Hlo H0. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
    split; [lia|]. split; [lia|]. intros a Ha.
    assert (E : m0 (wa a) = Some (Z_to_bv 8 0)).
    { rewrite init_at, wa_unsigned by lia.
      replace (Z.leb (bv_unsigned sp) a) with false by (symmetry; apply Z.leb_gt; lia).
      replace (Z.leb wlo a) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
    split. { unfold wview. rewrite E. discriminate. } exists (Z_to_bv 8 0). unfold mrd. rewrite E. reflexivity.
  Qed.

  Section Inv.
    Variable L : Z.
    Hypothesis SEGS_LOW : forall a : word, (L <= bv_unsigned a)%Z -> find_segment segs (bv_unsigned a) 1 = None.
    Hypothesis LSP : (L <= bv_unsigned sp)%Z.
    Hypothesis LWLO : (L <= wlo)%Z.

    Lemma init_mem_inv : mem_inv segs m0.
    Proof.
      intros a b H. unfold ro_addr.
      destruct (Z.lt_ge_cases (bv_unsigned a) L) as [Hl|Hh].
      - rewrite init_none in H by lia. discriminate.
      - rewrite SEGS_LOW by lia. reflexivity.
    Qed.
  End Inv.

  Hypothesis IMGHI : (bv_unsigned sp + Z.of_nat (length ent) <= 2^64)%Z.

  Lemma init_stack_bytes : bytes_at segs m0 (bv_unsigned sp) ent.
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
    split; [lia|]. split; [lia|]. intros i Hi. unfold mrd.
    assert (EA : bv_unsigned (wa (bv_unsigned sp + Z.of_nat i)) = (bv_unsigned sp + Z.of_nat i)%Z) by (apply wa_unsigned; lia).
    rewrite init_at_block by (rewrite EA; lia). rewrite EA.
    replace (Z.to_nat (bv_unsigned sp + Z.of_nat i - bv_unsigned sp)) with i by lia.
    destruct (nth_error ent i) eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
  Qed.

  Lemma init_stack_wr : wr_at segs m0 (bv_unsigned sp) (Z.of_nat (length ent)).
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
    split; [lia|]. split; [lia|]. intros i Hi. unfold wview.
    assert (EA : bv_unsigned (wa (bv_unsigned sp + i)) = (bv_unsigned sp + i)%Z) by (apply wa_unsigned; lia).
    rewrite init_at_block by (rewrite EA; lia). rewrite EA.
    destruct (nth_error ent (Z.to_nat (bv_unsigned sp + i - bv_unsigned sp))) eqn:E; [discriminate|].
    apply nth_error_None in E. lia.
  Qed.
End Init.

Lemma init_mem_inv' : forall inp mbase ph entry sp draw L,
  (L <= bv_unsigned sp)%Z -> (L <= stack_window_lo (in_kernel inp) mbase draw)%Z ->
  (segs_top segs <= L)%Z ->
  mem_inv segs (wrap_mem inp mbase ph entry sp draw).
Proof.
  intros inp mbase ph entry sp draw L H1 H2 H4. apply (init_mem_inv inp mbase ph entry sp draw L); try assumption.
  intros a Ha. apply find_segment_high; lia.
Qed.

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

Lemma str_ptrs_bounds : forall strs base i p, nth_error (str_ptrs base strs) i = Some p ->
  (base <= p /\ p < base + total_arg_bytes strs)%Z.
Proof.
  induction strs as [|s0 strs IH]; intros base [|i] p Hn; cbn in Hn; try discriminate.
  - injection Hn as <-. rewrite total_arg_bytes_cons. pose proof (total_arg_bytes_nonneg strs). lia.
  - apply IH in Hn. rewrite total_arg_bytes_cons. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* The layout of [StackLayout.build_stack_bytes], as offsets from [sp] and     *)
(* from the stack VMA's end [top]: argc, the argv pointers, NULL, the envp     *)
(* pointers, NULL, the auxv, the odd-item gap, the sixteen AT_RANDOM bytes,     *)
(* the [arch_align_stack] pad, the argv/envp strings, the exec name and its    *)
(* NUL, and the eight-byte slot under [top].                                   *)
(* ------------------------------------------------------------------------- *)

Definition argc (argv : list (list byte)) : Z := Z.of_nat (length argv).
Definition envc (envp : list (list byte)) : Z := Z.of_nat (length envp).

Definition lsb (argv envp : list (list byte)) (execfn : list byte) : Z :=
  Z.of_nat (launch_string_bytes argv envp execfn).

Definition str_base (top : word) (argv envp : list (list byte)) (execfn : list byte) : Z :=
  (bv_unsigned top - 8 - lsb argv envp execfn)%Z.
Definition env_base (top : word) (argv envp : list (list byte)) (execfn : list byte) : Z :=
  (str_base top argv envp execfn + total_arg_bytes argv)%Z.
Definition xfn_base (top : word) (argv envp : list (list byte)) (execfn : list byte) : Z :=
  (env_base top argv envp execfn + total_arg_bytes envp)%Z.

Definition argv_ptrs (top : word) (argv envp : list (list byte)) (execfn : list byte) : list word :=
  map (Z_to_bv 64) (str_ptrs (str_base top argv envp execfn) argv).
Definition envp_ptrs (top : word) (argv envp : list (list byte)) (execfn : list byte) : list word :=
  map (Z_to_bv 64) (str_ptrs (env_base top argv envp execfn) envp).

Definition head_len (rseq : bool) (argv envp : list (list byte)) : Z :=
  Z.of_nat (block_head_size rseq argv envp).
Definition rnd_addr (rseq : bool) (sp : word) (argv envp : list (list byte)) : Z :=
  (bv_unsigned sp + head_len rseq argv envp - 16)%Z.
Definition envp_addr (sp : word) (argv : list (list byte)) : Z := (bv_unsigned sp + 8 * (argc argv + 2))%Z.
Definition auxv_addr (sp : word) (argv envp : list (list byte)) : Z := (bv_unsigned sp + 8 * (argc argv + envc envp + 3))%Z.
Definition gap_len (argv envp : list (list byte)) : nat := (8 * (block_items argv envp mod 2))%nat.

Definition auxv_words (la : LaunchAuxv) (ph : PhdrInfo) (entry sp top : word) (argv envp : list (list byte))
    (execfn : list byte) (uid gid hw : word) : list word :=
  flat_map (fun e : word * word => [fst e; snd e])
    (auxv_entries la ph entry uid gid hw (Z_to_bv 64 (rnd_addr (la_rseq la) sp argv envp))
                  (Z_to_bv 64 (xfn_base top argv envp execfn))).

(* What the launch conjunct of [Run.valid_entry_va] guarantees about the
   block: the pad [arch_align_stack] left is not clamped, so the block runs
   exactly from [sp] to [top]. *)
Definition geom_ok (rseq : bool) (sp top : word) (argv envp : list (list byte)) (execfn : list byte) : Prop :=
  (bv_unsigned sp + head_len rseq argv envp + lsb argv envp execfn + 8 <= bv_unsigned top)%Z.

(* The facts about a launch the start-up and [main] read off the block: the
   block's geometry and the stack VMA's end inside the Sv48 window.  The
   auxv's length stays symbolic in [la_rseq la]: no kernel build is pinned. *)
Definition launch_ok (la : LaunchAuxv) (sp top : word) (argv envp : list (list byte)) (execfn : list byte) : Prop :=
  geom_ok (la_rseq la) sp top argv envp execfn /\ (bv_unsigned top <= sp_window_hi)%Z.

Lemma lsb_eq : forall argv envp execfn,
  lsb argv envp execfn = (total_arg_bytes argv + total_arg_bytes envp + Z.of_nat (length execfn) + 1)%Z.
Proof.
  intros argv envp execfn. pose proof (flatten_strings_length argv). pose proof (flatten_strings_length envp).
  unfold lsb, launch_string_bytes. lia.
Qed.

Lemma xfn_base_eq : forall top argv envp execfn,
  xfn_base top argv envp execfn = (bv_unsigned top - 9 - Z.of_nat (length execfn))%Z.
Proof. intros. unfold xfn_base, env_base, str_base. rewrite lsb_eq. lia. Qed.

Lemma lit_sub_wrap : forall (a : word) (k : Z), a - Z_to_bv 64 k = Z_to_bv 64 (bv_unsigned a - k).
Proof.
  intros a k. apply bv_eq. rewrite bv_sub_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  apply Zminus_mod_idemp_r.
Qed.

Lemma string_base_addr_eq : forall top argv envp execfn,
  string_base_addr top argv envp execfn = Z_to_bv 64 (str_base top argv envp execfn).
Proof.
  intros. unfold string_base_addr, nat_to_word. rewrite lit_sub_wrap. f_equal. unfold str_base, lsb. lia.
Qed.

Lemma at_execfn_ptr_eq : forall top argv envp execfn,
  at_execfn_ptr top execfn = Z_to_bv 64 (xfn_base top argv envp execfn).
Proof.
  intros. unfold at_execfn_ptr, nat_to_word. rewrite lit_sub_wrap, xfn_base_eq. f_equal. lia.
Qed.

Lemma at_random_ptr_eq : forall (sp : word) rseq argv envp,
  at_random_ptr sp rseq argv envp = Z_to_bv 64 (rnd_addr rseq sp argv envp).
Proof.
  intros. unfold at_random_ptr, rnd_addr, head_len, nat_to_word.
  assert (H16 : (16 <= block_head_size rseq argv envp)%nat) by (unfold block_head_size; cbv zeta; lia).
  rewrite <- (Z_to_bv_bv_unsigned sp) at 1. rewrite lit_add_lit. f_equal. lia.
Qed.

Lemma u64s_flat_pairs : forall es : list (word * word),
  u64s (flat_map (fun e : word * word => [fst e; snd e]) es)
  = flat_map (fun e : word * word => word_le8 (fst e) ++ word_le8 (snd e)) es.
Proof.
  induction es as [|e es IH]; [reflexivity|]. cbn [flat_map].
  rewrite u64s_app, IH. cbn [u64s]. rewrite ?app_nil_r.
  rewrite ?(word_le8_le8 (fst e)), ?(word_le8_le8 (snd e)).
  rewrite <- ?app_assoc. reflexivity.
Qed.

Lemma build_stack_bytes_eq : forall la ph entry (sp top : word) argv envp execfn (uid gid hw : word) draw,
  build_stack_bytes la ph entry sp top argv envp execfn uid gid hw draw =
  le8 (Z_to_bv 64 (argc argv)) ++ u64s (argv_ptrs top argv envp execfn) ++ le8 (Z_to_bv 64 0)
  ++ u64s (envp_ptrs top argv envp execfn) ++ le8 (Z_to_bv 64 0)
  ++ u64s (auxv_words la ph entry sp top argv envp execfn uid gid hw)
  ++ repeat (Z_to_bv 8 0) (gap_len argv envp) ++ at_random_bytes (ed_random draw)
  ++ repeat (Z_to_bv 8 0) (block_pad_len (la_rseq la) sp top argv envp execfn)
  ++ flatten_strings argv ++ flatten_strings envp ++ execfn ++ [Z_to_bv 8 0] ++ repeat (Z_to_bv 8 0) 8.
Proof.
  intros. unfold build_stack_bytes. cbv zeta.
  rewrite string_base_addr_eq, string_addrs_eq. cbv beta iota.
  rewrite string_addrs_eq. cbv beta iota.
  rewrite (at_random_ptr_eq sp (la_rseq la) argv envp), (at_execfn_ptr_eq top argv envp execfn).
  unfold auxv_bytes, build_auxv, auxv_words. rewrite <- u64s_flat_pairs.
  rewrite !word_le8_le8, !flat_map_word_le8.
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma length_bsb : forall la ph entry (sp top : word) argv envp execfn (uid gid hw : word) draw,
  Z.of_nat (length (build_stack_bytes la ph entry sp top argv envp execfn uid gid hw draw))
  = (head_len (la_rseq la) argv envp + Z.of_nat (block_pad_len (la_rseq la) sp top argv envp execfn)
     + lsb argv envp execfn + 8)%Z.
Proof. intros. rewrite length_build_stack_bytes. unfold head_len, lsb. lia. Qed.

Lemma pad_len_eq : forall rseq (sp top : word) argv envp execfn,
  geom_ok rseq sp top argv envp execfn ->
  Z.of_nat (block_pad_len rseq sp top argv envp execfn)
  = (bv_unsigned top - 8 - lsb argv envp execfn - bv_unsigned sp - head_len rseq argv envp)%Z.
Proof.
  intros rseq sp top argv envp execfn G. unfold geom_ok in G. unfold block_pad_len. unfold lsb, head_len in *.
  rewrite Z2Nat.id by lia. lia.
Qed.

Lemma head_len_eq : forall rseq argv envp,
  head_len rseq argv envp
  = (8 * (argc argv + envc envp + 3) + 16 * Z.of_nat (auxv_count rseq) + Z.of_nat (gap_len argv envp) + 16)%Z.
Proof.
  intros. unfold head_len, block_head_size, gap_len, block_items, auxv_size, argc, envc. cbv zeta.
  remember ((length argv + length envp + 3) mod 2)%nat as q. lia.
Qed.

Lemma head_len_ge : forall rseq argv envp,
  (8 * (argc argv + envc envp + 3) + Z.of_nat (auxv_size rseq) + 16 <= head_len rseq argv envp)%Z.
Proof.
  intros. rewrite head_len_eq. unfold gap_len, auxv_size.
  pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)). lia.
Qed.

Lemma auxv_words_length : forall la ph entry sp top argv envp execfn uid gid hw,
  length (auxv_words la ph entry sp top argv envp execfn uid gid hw) = (2 * auxv_count (la_rseq la))%nat.
Proof. intros. unfold auxv_words, auxv_entries. destruct (la_rseq la); reflexivity. Qed.

Lemma argv_ptrs_length : forall top argv envp execfn, length (argv_ptrs top argv envp execfn) = length argv.
Proof. intros. unfold argv_ptrs. rewrite map_length. apply str_ptrs_length. Qed.
Lemma envp_ptrs_length : forall top argv envp execfn, length (envp_ptrs top argv envp execfn) = length envp.
Proof. intros. unfold envp_ptrs. rewrite map_length. apply str_ptrs_length. Qed.

Lemma img_length : forall la ph entry (sp top : word) argv envp execfn (uid gid hw : word) draw,
  geom_ok (la_rseq la) sp top argv envp execfn ->
  Z.of_nat (length (build_stack_bytes la ph entry sp top argv envp execfn uid gid hw draw))
  = (bv_unsigned top - bv_unsigned sp)%Z.
Proof. intros la ph entry sp top argv envp execfn uid gid hw draw G. rewrite length_bsb, (pad_len_eq _ _ _ _ _ _ G). lia. Qed.

Lemma str_base_ge : forall rseq (sp top : word) argv envp execfn,
  geom_ok rseq sp top argv envp execfn ->
  (bv_unsigned sp + head_len rseq argv envp <= str_base top argv envp execfn)%Z.
Proof. intros rseq sp top argv envp execfn G. unfold geom_ok in G. unfold str_base. lia. Qed.

Lemma envp_ptrs_nz : forall rseq (sp top : word) argv envp execfn,
  geom_ok rseq sp top argv envp execfn ->
  Forall (fun w : word => bv_unsigned w <> 0%Z) (envp_ptrs top argv envp execfn).
Proof.
  intros rseq sp top argv envp execfn G.
  apply Forall_forall. intros w Hw. apply In_nth_error in Hw. destruct Hw as [i Hi].
  unfold envp_ptrs in Hi. rewrite nth_error_map in Hi.
  destruct (nth_error (str_ptrs (env_base top argv envp execfn) envp) i) as [q|] eqn:E; [|discriminate].
  cbn in Hi. injection Hi as <-.
  apply str_ptrs_bounds in E.
  pose proof (str_base_ge _ _ _ _ _ _ G) as SB. pose proof (head_len_ge rseq argv envp) as HG.
  pose proof (lsb_eq argv envp execfn) as LE. pose proof (total_arg_bytes_nonneg argv) as TA.
  pose proof (bv_unsigned_in_range 64 top) as RT. unfold bv_modulus in RT. cbn in RT.
  pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS. cbn in RS.
  unfold env_base, str_base, argc, envc in *.
  rewrite unsigned_lit by lia. lia.
Qed.

(* Reading the block back out of a memory that holds it at [sp]. *)
Section Pieces.
  Variables (la : LaunchAuxv) (ph : PhdrInfo) (entry sp top : word) (argv envp : list (list byte))
            (execfn : list byte) (uid gid hw : word) (draw : EntryDraw) (m : word -> option byte).
  Notation img := (build_stack_bytes la ph entry sp top argv envp execfn uid gid hw draw).
  Notation usp := (bv_unsigned sp).
  Notation AP := (argv_ptrs top argv envp execfn).
  Notation EP := (envp_ptrs top argv envp execfn).
  Notation AW := (auxv_words la ph entry sp top argv envp execfn uid gid hw).
  Hypothesis IMG : bytes_at segs m usp img.
  Hypothesis GEOM : geom_ok (la_rseq la) sp top argv envp execfn.

  Lemma img_pieces :
    bytes_at segs m usp (le8 (Z_to_bv 64 (argc argv))) /\
    bytes_at segs m (usp + 8) (u64s (AP ++ [Z_to_bv 64 0])) /\
    bytes_at segs m (envp_addr sp argv) (u64s EP ++ le8 (Z_to_bv 64 0) ++ u64s AW) /\
    bytes_at segs m (auxv_addr sp argv envp) (u64s AW) /\
    bytes_at segs m (rnd_addr (la_rseq la) sp argv envp) (at_random_bytes (ed_random draw)) /\
    bytes_at segs m (str_base top argv envp execfn) (flatten_strings argv) /\
    bytes_at segs m (env_base top argv envp execfn) (flatten_strings envp) /\
    bytes_at segs m (xfn_base top argv envp execfn) (execfn ++ [Z_to_bv 8 0] ++ repeat (Z_to_bv 8 0) 8).
  Proof.
    pose proof IMG as B. rewrite build_stack_bytes_eq in B.
    pose proof (flatten_strings_length argv) as L1. pose proof (flatten_strings_length envp) as L2.
    pose proof (pad_len_eq _ _ _ _ _ _ GEOM) as PL.
    pose proof (head_len_eq (la_rseq la) argv envp) as HL.
    pose proof (auxv_words_length la ph entry sp top argv envp execfn uid gid hw) as AL.
    apply bytes_at_app in B. destruct B as [B0 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B1 B]. rewrite u64s_length, argv_ptrs_length in B.
    apply bytes_at_app in B. destruct B as [B2 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B3 B]. rewrite u64s_length, envp_ptrs_length in B.
    apply bytes_at_app in B. destruct B as [B4 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B5 B]. rewrite u64s_length, AL in B.
    apply bytes_at_app in B. destruct B as [B6 B]. rewrite repeat_length in B.
    apply bytes_at_app in B. destruct B as [B7 B]. rewrite length_at_random_bytes in B.
    apply bytes_at_app in B. destruct B as [B8 B]. rewrite repeat_length in B.
    apply bytes_at_app in B. destruct B as [B9 B].
    apply bytes_at_app in B. destruct B as [B10 B].
    unfold envp_addr, auxv_addr, rnd_addr, xfn_base, env_base, str_base, argc, envc in *.
    repeat match goal with |- _ /\ _ => split end.
    - exact B0.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app segs m _ _ _)). split; [exact B1|].
      rewrite u64s_length, argv_ptrs_length. apply (bytes_at_eqa _ _ _ _ B2). lia.
    - apply (proj2 (bytes_at_app segs m _ _ _)). split; [apply (bytes_at_eqa _ _ _ _ B3); lia|].
      rewrite u64s_length, envp_ptrs_length. apply (proj2 (bytes_at_app segs m _ _ _)).
      split; [apply (bytes_at_eqa _ _ _ _ B4); lia|].
      rewrite length_le8. apply (bytes_at_eqa _ _ _ _ B5). lia.
    - apply (bytes_at_eqa _ _ _ _ B5). lia.
    - apply (bytes_at_eqa _ _ _ _ B7). lia.
    - apply (bytes_at_eqa _ _ _ _ B9). lia.
    - apply (bytes_at_eqa _ _ _ _ B10). lia.
    - apply (bytes_at_eqa _ _ _ _ B). lia.
  Qed.

  Lemma img_argv_string : forall i s, nth_error argv i = Some s ->
    exists p, nth_error AP i = Some (Z_to_bv 64 p) /\ (str_base top argv envp execfn <= p)%Z /\
      (p + Z.of_nat (length s) + 1 <= env_base top argv envp execfn)%Z /\ bytes_at segs m p (s ++ [Z_to_bv 8 0]).
  Proof.
    intros i s Hn. destruct (str_ptrs_nth argv (str_base top argv envp execfn) i s Hn) as (off & Hp & Ho & Ht & Hf).
    exists (str_base top argv envp execfn + off)%Z. split. { unfold argv_ptrs. rewrite nth_error_map, Hp. reflexivity. }
    split; [lia|]. split. { unfold env_base. lia. }
    destruct img_pieces as (_ & _ & _ & _ & _ & B6 & _).
    pose proof (flatten_strings_length argv).
    pose proof (bytes_at_slice m (str_base top argv envp execfn) (flatten_strings argv) (Z.to_nat off) (length s + 1) B6 ltac:(lia)) as B.
    rewrite Hf in B. replace (str_base top argv envp execfn + Z.of_nat (Z.to_nat off))%Z with (str_base top argv envp execfn + off)%Z in B by lia.
    exact B.
  Qed.

  (* An argv string with the bytes after its NUL up to the next 8-byte
     boundary: the strings sit under the eight-byte slot below [top], so
     those bytes are always inside the block. *)
  Lemma img_argv_cstring : forall i s, nth_error argv i = Some s ->
    exists p slack, nth_error AP i = Some (Z_to_bv 64 p) /\ (str_base top argv envp execfn <= p)%Z /\
      (p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= usp + Z.of_nat (length img))%Z /\
      bytes_at segs m p (s ++ Z_to_bv 8 0 :: slack) /\
      ((- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Proof.
    intros i s Hn. destruct (str_ptrs_nth argv (str_base top argv envp execfn) i s Hn) as (off & Hp & Ho & Ht & Hf).
    pose proof (img_length la ph entry sp top argv envp execfn uid gid hw draw GEOM) as BL. pose proof (flatten_strings_length argv) as L1.
    pose proof (lsb_eq argv envp execfn) as LE.
    pose proof (str_base_ge _ _ _ _ _ _ GEOM) as SB. pose proof (head_len_ge (la_rseq la) argv envp) as HG.
    pose proof (total_arg_bytes_nonneg envp) as TE.
    unfold argc, envc in HG.
    set (p := (str_base top argv envp execfn + off)%Z).
    set (e := (p + Z.of_nat (length s) + 1)%Z).
    set (k := ((- e) mod 8)%Z).
    assert (HK : (0 <= k < 8)%Z) by (subst k; apply Z.mod_pos_bound; lia).
    assert (OFF : (usp <= p /\ e + k <= usp + Z.of_nat (length img))%Z).
    { subst p e k. unfold str_base in *. split; lia. }
    exists p, (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) img)).
    split; [unfold argv_ptrs; rewrite nth_error_map, Hp; reflexivity|]. split; [subst p; lia|].
    assert (LS : length (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) img)) = Z.to_nat k).
    { rewrite length_firstn, length_skipn. lia. }
    rewrite LS. split; [lia|]. split; [| lia].
    destruct img_pieces as (_ & _ & _ & _ & _ & B6 & _).
    pose proof (bytes_at_slice m (str_base top argv envp execfn) (flatten_strings argv) (Z.to_nat off) (length s + 1) B6 ltac:(lia)) as BS.
    rewrite Hf in BS. replace (str_base top argv envp execfn + Z.of_nat (Z.to_nat off))%Z with p in BS by (subst p; lia).
    pose proof (bytes_at_slice m usp img (Z.to_nat (e - usp)) (Z.to_nat k) IMG ltac:(lia)) as BK.
    replace (usp + Z.of_nat (Z.to_nat (e - usp)))%Z with (p + Z.of_nat (length (s ++ [Z_to_bv 8 0])))%Z in BK
      by (rewrite length_app; cbn [length]; subst e; lia).
    pose proof (proj2 (bytes_at_app segs m p _ _) (conj BS BK)) as BB. rewrite <- app_assoc in BB. cbn [app] in BB. exact BB.
  Qed.

End Pieces.
End WithSegs.

(* The sixteen AT_RANDOM bytes as the canary word and the secret word. *)
Lemma testbit_bv_wrap : forall n z i, (0 <= i)%Z ->
  Z.testbit (bv_wrap n z) i = if (i <? Z.of_N n)%Z then Z.testbit z i else false.
Proof.
  intros n z i Hi. unfold bv_wrap, bv_modulus.
  destruct (Z.ltb_spec i (Z.of_N n)).
  - apply Z.mod_pow2_bits_low. lia.
  - apply Z.mod_pow2_bits_high. lia.
Qed.

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

Definition rnd_bytes (d : EntryDraw) : list byte := at_random_bytes (ed_random d).
Lemma rnd_bytes_length : forall d, length (rnd_bytes d) = 16%nat.
Proof. reflexivity. Qed.

Lemma rnd_bytes_split : forall d,
  rnd_bytes d = le8 (Z_to_bv 64 (draw_canary d)) ++ le8 (Z_to_bv 64 (draw_secret d)).
Proof. intros d. apply at_random_bytes_split. Qed.

Definition entry_atop (en : ExecEntry) : Z := (bv_unsigned (en_sp en) - stack_max_size)%Z.
Definition entry_secret (en : ExecEntry) : Z := draw_secret (en_draw en).
Definition entry_canary (en : ExecEntry) : Z := draw_canary (en_draw en).



(* ------------------------------------------------------------------------- *)
(* The launch conjunct, read as arithmetic.  [launch_sp_le_top] ...          *)
(* [stack_window_lo_valid] are the model's own lemmas (Common/StepTac.v and   *)
(* Common/StoreOk.v at ), copied here because this library does not   *)
(* vendor those two files.                                                   *)
(* ------------------------------------------------------------------------- *)

Lemma geom_of_launch : forall v inp (sp brk mbase : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  geom_ok (kb_rseq (in_kernel inp)) sp (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp).
Proof.
  intros v inp sp brk mbase draw Hok.
  cbn [entry_launch_ok_va] in Hok.
  destruct Hok as (_ & (_ & _ & Hhi) & _).
  unfold launch_sp_hi, align_down16 in Hhi. unfold geom_ok, head_len, lsb.
  pose proof (Z.mod_pos_bound
    (bv_unsigned (ed_top draw) - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp)))
    16 ltac:(lia)) as Hm.
  lia.
Qed.

Lemma top_of_launch : forall inp (sp brk mbase : word) draw,
  entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp ->
  (bv_unsigned (ed_top draw) <= sp_window_hi)%Z.
Proof.
  intros inp sp brk mbase draw Hok.
  cbn [entry_launch_ok_va] in Hok.
  destruct Hok as ((_ & Htop & _) & _ & _). exact Htop.
Qed.

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

Lemma launch_sp_le_top : forall inp (top sp : word),
  valid_launch_sp top inp sp ->
  (bv_unsigned sp <= bv_unsigned top)%Z.
Proof.
  intros inp top sp [_ [_ Hhi]].
  unfold launch_sp_hi, align_down16 in Hhi.
  pose proof (Nat2Z.is_nonneg
    (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).
  pose proof (Nat2Z.is_nonneg
    (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
  pose proof (Z.mod_pos_bound
    (bv_unsigned top - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                     (in_execfn inp))) 16 ltac:(lia)).
  lia.
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

Lemma stack_window_lo_ge_sp : forall inp (sp brk0 mbase : word) draw,
  entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase draw) inp ->
  (bv_unsigned sp - stack_max_size
   <= stack_window_lo (in_kernel inp) mbase draw)%Z.
Proof.
  intros inp sp brk0 mbase draw (_ & Hsp & _).
  pose proof (launch_sp_le_top inp (ed_top draw) sp Hsp).
  unfold stack_window_lo.
  apply Z.le_trans with (bv_unsigned (ed_top draw) - stack_max_size)%Z;
    [lia | apply Z.le_max_l].
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
   for every launch the fifth conjunct of [Run.valid_entry_va] admits. *)
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
