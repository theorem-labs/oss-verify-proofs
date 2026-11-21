(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the init and Layout sections read the ProcInput, mmap base, entry and draw, floor the window at stack_window_lo, and restate the revision's stack block (AT_RANDOM below the strings, auxv_bytes vector, exec file name, pad) through head_bytes and tail_bytes; and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef); internal commit ids in comments replaced by public commits or removed. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

#[using="Type"] Lemma rw_bytes_b_sound : forall bs A (m : word -> option byte),
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

#[using="Type"] Lemma rw_cells_image0 : forall (m : word -> option byte) A bs,
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
#[using="Type"] Lemma rw_cells_recast : forall m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells segs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
    destruct WR as (HA & HN & HW).
    split; [split; [split; assumption|] | split; [split; assumption|]].
    + split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
  - intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
    pose proof (cells_bytes_length cs1 W1) as L1.
    split; [split; [split; assumption|] |].
    + split; [exact B1|]. rewrite L1. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
      * apply HW1. lia.
      * replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rd_u64 : forall m A (w : word) rest a,
  bytes_at segs m A (le8 w ++ rest) -> a = wa A -> ov_read_bytes segs m a 8 = Some (le8 w).
Proof.
  intros m A w rest a B ->.
  assert (L : (0 + 8 <= length (le8 w ++ rest))%nat) by (rewrite app_length, length_le8; lia).
  pose proof (bytes_at_ov_read segs m A (le8 w ++ rest) 0 8 B L) as R.
  rewrite Z.add_0_r in R. rewrite R. f_equal; reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Init.
  (* [comment removed for export] *)
  Variables (inp : ProcInput) (mb : word) (ph : PhdrInfo) (entry : word)
            (sp : word) (draw : EntryDraw).
  Notation m0 := (wrap_mem inp mb ph entry sp draw).
  Notation img := (entry_stack_image inp mb ph entry sp draw).
  (* the zero-filled window's floor, exactly [wrap_mem]'s own guard *)
  Notation wlo := (stack_window_lo (in_kernel inp) mb draw).
  Hypothesis SPLO : (wlo <= bv_unsigned sp)%Z.
  Hypothesis IMGHI : (bv_unsigned sp + Z.of_nat (length img) <= 2^64)%Z.
  Let SMS : stack_max_size = 8388608%Z := eq_refl.

  #[using="Type"] Lemma init_at : forall a : word,
    m0 a = if (Z.leb (bv_unsigned sp) (bv_unsigned a)) then
             (if Z.ltb (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length img))
              then nth_error img (Z.to_nat (bv_unsigned a - bv_unsigned sp)) else None)
           else if Z.leb wlo (bv_unsigned a) then Some (Z_to_bv 8 0) else None.
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

  (* SPLO added 2026-11-06: init_at's window is now stack_window_lo (in_kernel inp) mb draw
     rather than the constant bv_unsigned sp - stack_max_size, and the two `Z.leb … = false`
     steps below discharge through SPLO's wlo <= bv_unsigned sp. The compiler named this
     exactly -- "section variable used but not declared: SPLO" at the Qed -- which is
     `Proof using` doing its job: the annotation had to catch up with the proof. *)
  #[using="SMS SPLO"] Lemma init_none : forall a : word, (bv_unsigned a < wlo)%Z -> m0 a = None.
  Proof.
    intros a Ha. rewrite init_at.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia).
    replace (Z.leb wlo (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia).
    reflexivity.
  Qed.

  #[using="Type"] Lemma init_none_above : forall a : word, (bv_unsigned sp + Z.of_nat (length img) <= bv_unsigned a)%Z -> m0 a = None.
  Proof.
    intros a Ha. rewrite init_at.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a - bv_unsigned sp) (Z.of_nat (length img))) with false by (symmetry; apply Z.ltb_ge; lia).
    reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="SPLO IMGHI SMS"] Lemma init_stack_bytes : bytes_at segs m0 (bv_unsigned sp) img.
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
    split; [lia|]. split; [lia|]. intros i Hi. unfold mrd. rewrite init_at.
    rewrite wa_unsigned by lia.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned sp + Z.of_nat i)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned sp + Z.of_nat i - bv_unsigned sp) (Z.of_nat (length img))) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (Z.to_nat (bv_unsigned sp + Z.of_nat i - bv_unsigned sp)) with i by lia.
    destruct (nth_error img i) eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
  Qed.

  #[using="SPLO IMGHI SMS"] Lemma init_stack_wr : wr_at segs m0 (bv_unsigned sp) (Z.of_nat (length img)).
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
    split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite init_at, wa_unsigned by lia.
    replace (Z.leb (bv_unsigned sp) (bv_unsigned sp + i)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned sp + i - bv_unsigned sp) (Z.of_nat (length img))) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (nth_error img (Z.to_nat (bv_unsigned sp + i - bv_unsigned sp))) eqn:E; [discriminate|].
    apply nth_error_None in E. lia.
  Qed.

  #[using="SPLO IMGHI SMS"] Lemma init_stack_u8arr : u8arr segs m0 (bv_unsigned sp) img.
  Proof. split; [apply init_stack_bytes | apply init_stack_wr]. Qed.

  (* The window floor is non-negative, with NO launch premise.  [Run.stack_window_lo]
     is [Z.max (ed_top - stack_max_size) (mbase + stack_guard_gap_bytes kb)], so its
     right branch alone bounds it below: [bv_unsigned mb] is non-negative and so is the
     guard gap ([State.stack_guard_gap_bytes_bounds]).  The model's two sharper bounds,
     [StoreOk.stack_window_lo_ge_sp] and [StoreOk.stack_window_lo_valid], both need
     [entry_launch_ok_va], which this section does not carry -- and neither is vendored
     here.  Before the floor was the literal [bv_unsigned sp - 8 MiB] and
     [lia] read [0 <= floor] off [R]; now the floor is an opaque application and the
     bound has to be supplied. *)
  #[using="Type"] Lemma init_wlo_nonneg : (0 <= wlo)%Z.
  Proof.
    pose proof (bv_unsigned_in_range 64 mb) as RMB. unfold bv_modulus in RMB. cbn in RMB.
    pose proof (stack_guard_gap_bytes_bounds (in_kernel inp)) as GG.
    pose proof (Z.le_max_r (bv_unsigned (ed_top draw) - stack_max_size)
                           (bv_unsigned mb + stack_guard_gap_bytes (in_kernel inp))) as HM.
    unfold stack_window_lo. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="SPLO"] Lemma init_stk : stk segs m0 wlo (bv_unsigned sp).
  Proof.
    pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
    pose proof init_wlo_nonneg as W0.
    split; [lia|]. split; [lia|]. intros a Ha.
    assert (E : m0 (wa a) = Some (Z_to_bv 8 0)).
    { rewrite init_at, wa_unsigned by lia.
      replace (Z.leb (bv_unsigned sp) a) with false by (symmetry; apply Z.leb_gt; lia).
      replace (Z.leb wlo a) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
    split. { unfold wview. rewrite E. discriminate. } exists (Z_to_bv 8 0). unfold mrd. rewrite E. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Hypothesis SEGS_LOW : forall a : word, (wlo <= bv_unsigned a)%Z -> find_segment segs (bv_unsigned a) 1 = None.
  (* SPLO added 2026-11-06: this proof rewrites with `init_none`, which now
     depends on SPLO because init_at's window became stack_window_lo.  The
     compiler named the exact replacement list; this is `Proof using` doing
     its job, the annotation catching up with a dependency the body gained. *)
  #[using="SMS SEGS_LOW SPLO"] Lemma init_mem_inv : mem_inv segs m0.
  Proof.
    intros a b H. unfold ro_addr.
    destruct (Z.lt_ge_cases (bv_unsigned a) wlo) as [Hl|Hh].
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

(* [comment removed for export] *)
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

(* Z-literal subtraction, the mirror of [lit_add_lit]; needed because
   [StackLayout.string_base_addr] places the string area by subtracting from
   [ed_top] rather than by adding to [sp]. *)
Lemma lit_sub_lit : forall a b, (Z_to_bv 64 a - Z_to_bv 64 b : word) = Z_to_bv 64 (a - b).
Proof.
  intros a b. apply bv_eq. rewrite bv_sub_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. reflexivity.
Qed.

(* PROVENANCE (rule 23c).  [Section Layout] below is a restatement of this
   file's pre-revision stack arithmetic against LPS 75d69e00, ported from
   75d69e00:theories/Common/AsanInit.v:
     :214   [Let CHEAD := Z.of_nat (block_head_size rseq argv envp)]  -> [struct_size]
     :218   [Let W := Z.of_nat (block_pad_len rseq sp top argv envp execfn)] -> [pad_len]
     :220   [Let STR0 := usp + CHEAD + W]                             -> [str_base]
     :913, :950  [Hu : bv_unsigned (at_random_ptr sp rseq argv envp) = usp + CHEAD - 16]
                                                                      -> [u_at_random_ptr]
     :917, :955  [Ha : (at_random_ptr sp rseq argv envp + nat_to_word (Z.to_nat i))%bv
                        = Z_to_bv 64 (usp + CHEAD - 16 + i)]          -> [at_random_ptr_off]
     :989   [atr_ptr_eq : at_random_ptr sp rseq argv envp = edenot E0 (e_atrandom RZ)]
                                                                      -> [at_random_ptr_eq]
   The checker image excludes the model's theories/Common, so the text is
   carried here rather than Required.
   DIFFERENCES FROM THE DONOR, complete list:
     1. the donor's section abbreviations are re-bound to this file's own
        section variables; [CHEAD] keeps the donor's definition verbatim,
        [Z.of_nat (block_head_size rseq argv envp)].
     2. the donor states [Hu] and [Ha] inside two [kentry_ok] proofs about a
        symbolic machine; here they are standalone lemmas, and the donor's
        [rewrite Hp, word_add_nat, u64_lit] step is the same step through this
        tree's [lit_add_lit] / [unsigned_lit], because this tree carries no
        [word_add_nat].
     3. the donor's [atr_ptr_eq] lands in [edenot E0 (e_atrandom RZ)]; there is
        no expression language here, so [at_random_ptr_eq] lands in
        [Z_to_bv 64 rnd_addr] -- the same address spelled as a literal, which
        is also the shape the OLD [at_random_ptr_eq] in this file had.
     4. no premise added to a published statement and no statement weakened:
        every declaration below is tree-local, under proofs/lib/.
   [StackLayout.block_head_size], [Run.block_head_size_bounds] (Run.v:3889) and
   [Run.block_head_size_mod16] (Run.v:3904) are USED, not restated: both files
   are in the image, and the head size is not this tree's to rebuild.

   WHAT MOVED, and why no arity fix would have caught it.  Before the revision
   the sixteen AT_RANDOM bytes sat ABOVE the strings, at [usp + raw_len +
   pad_len], and [struct_size] was the literal [8*(argc+envc) + 184] -- the 184
   baking in an [auxv_size] of 160, ten auxv pairs.  At 75d69e00 they sit
   BELOW the strings, at [usp + C - 16], the vector is 27 pairs (29 under
   CONFIG_RSEQ) in [create_elf_tables]' own order, the exec file name is
   published, and the strings run from [usp + C + W] up to [ed_top].  So
     C = block_head_size rseq argv envp = 8*argc + 8*envc + 472 + 32*rseq + 8*G,
     G = (argc + envc + 3) mod 2,
   which is NOT the old [struct_size] plus a constant: it gains a parity term
   and an rseq term, and it now includes the sixteen bytes itself.
   [ed_slack] and [entry_slack] are DELETED at the revision (Run.v:1332), so
   the image is the block and nothing above it. *)
Section Layout.
  Variables (inp : ProcInput) (mb : word) (ph : PhdrInfo) (entry : word)
            (sp : word) (rnd : EntryDraw).
  Notation usp := (bv_unsigned sp).
  Notation argv := (in_argv inp).
  Notation envp := (in_envp inp).
  Notation execfn := (in_execfn inp).
  Notation top := (ed_top rnd).
  (* CONFIG_RSEQ is FREE.  [valid_input]'s conjunct 17 at 75d69e00 gives
     [in_kernel inp = recorded_kernel (in_kernel inp)], which fixes kb_vdso,
     kb_vlenb, kb_cache, kb_skb_head and the four socket-memory fields and
     leaves kb_thp, kb_aslr, kb_guard, kb_rnd_bits and kb_rseq alone.  The flag
     is therefore carried symbolically -- exactly as AsanInit.v:158 carries it
     with [Let rseq := kb_rseq kb] -- and nothing below pins the kernel record. *)
  Notation rseq := (kb_rseq (in_kernel inp)).
  Notation la := (launch_auxv inp sp mb).

  Definition argc : Z := Z.of_nat (length argv).
  Definition envc : Z := Z.of_nat (length envp).
  (* the zero gap [STACK_ROUND]'s mask leaves between the vector and the
     sixteen random bytes: [8 * (items mod 2)] *)
  Definition gap_len : nat := (8 * (block_items argv envp mod 2))%nat.
  (* C: sp to the TOP of the sixteen AT_RANDOM bytes *)
  Definition struct_size : Z := Z.of_nat (block_head_size rseq argv envp).
  (* L: the string bytes with their NULs, the exec file name included *)
  Definition str_len : Z := Z.of_nat (launch_string_bytes argv envp execfn).
  (* W: the [arch_align_stack] pad between the random bytes and argv[0] *)
  Definition pad_nat : nat := block_pad_len rseq sp top argv envp execfn.
  Definition pad_len : Z := Z.of_nat pad_nat.
  Definition rnd_addr : Z := (usp + struct_size - 16)%Z.
  Definition str_base : Z := (usp + struct_size + pad_len)%Z.
  Definition env_base : Z := (str_base + total_arg_bytes argv)%Z.
  Definition raw_len : Z := (struct_size + pad_len + str_len + 8)%Z.
  Definition argv_ptrs : list word := map (Z_to_bv 64) (str_ptrs str_base argv).
  Definition envp_ptrs : list word := map (Z_to_bv 64) (str_ptrs env_base envp).

  Lemma lay_rseq : la_rseq la = rseq.
  Proof. reflexivity. Qed.

  (* Run.v:3889 and Run.v:3904, used rather than re-derived. *)
  Lemma struct_size_bounds :
    (8 * (argc + envc) + 472 <= struct_size <= 8 * (argc + envc) + 512)%Z.
  Proof. unfold struct_size, argc, envc. apply block_head_size_bounds. Qed.

  Lemma struct_size_mod16 : (struct_size mod 16 = 0)%Z.
  Proof. unfold struct_size. apply block_head_size_mod16. Qed.

  Lemma struct_size_parts :
    struct_size = (8 * Z.of_nat (block_items argv envp) + Z.of_nat (auxv_size rseq)
                   + Z.of_nat gap_len + 16)%Z.
  Proof. unfold struct_size, gap_len, block_head_size. cbv zeta. lia. Qed.

  Lemma argc_envc_nonneg : (0 <= argc /\ 0 <= envc)%Z.
  Proof. unfold argc, envc. lia. Qed.

  Lemma pad_len_nonneg : (0 <= pad_len)%Z.
  Proof. unfold pad_len. lia. Qed.

  Lemma str_len_lo : (1 <= str_len)%Z.
  Proof. unfold str_len, launch_string_bytes. lia. Qed.

  (* The old [raw_len_nonneg] gave [0 <= pad_len < 8] because the pre-revision
     pad was [(8 - len mod 8) mod 8].  The revision's pad is whatever
     [arch_align_stack] left, clamped at 0, so only the lower bound survives
     without a launch premise; the head's bound is the donor's, not a literal. *)
  Lemma raw_len_nonneg :
    (472 <= struct_size /\ 0 <= total_arg_bytes argv /\ 0 <= total_arg_bytes envp
     /\ 0 <= pad_len /\ 1 <= str_len)%Z.
  Proof.
    pose proof (total_arg_bytes_nonneg argv). pose proof (total_arg_bytes_nonneg envp).
    pose proof struct_size_bounds. pose proof argc_envc_nonneg.
    pose proof pad_len_nonneg. pose proof str_len_lo. lia.
  Qed.

  (* AsanInit.v:989 -- the lemma this whole section was blocked on. *)
  Lemma at_random_ptr_eq :
    at_random_ptr sp rseq argv envp = Z_to_bv 64 rnd_addr.
  Proof.
    pose proof (block_head_size_bounds rseq argv envp) as HC.
    pose proof (Nat2Z.is_nonneg (length argv)).
    pose proof (Nat2Z.is_nonneg (length envp)).
    unfold at_random_ptr, rnd_addr, struct_size, nat_to_word.
    rewrite <- (Z_to_bv_bv_unsigned sp) at 1. rewrite lit_add_lit. f_equal. lia.
  Qed.

  Lemma entry_image_length_raw :
    (Z.of_nat (length (entry_stack_image inp mb ph entry sp rnd)) = raw_len)%Z.
  Proof.
    unfold entry_stack_image. rewrite length_build_stack_bytes, lay_rseq.
    unfold raw_len, struct_size, pad_len, pad_nat, str_len. lia.
  Qed.

  (* ---------------------------------------------------------------------- *)
  (* The block spans sp..ed_top.  This is [Run.valid_launch_sp]'s content and
     the reason [block_pad_len]'s [Z.to_nat] clamp never bites; it is a premise
     on a tree-local lemma, not on a published statement. *)
  Hypothesis SPAN : (usp + struct_size + str_len + 8 <= bv_unsigned top)%Z.

  Lemma span_pad :
    pad_len = (bv_unsigned top - 8 - str_len - usp - struct_size)%Z.
  Proof.
    unfold pad_len, pad_nat, block_pad_len, str_len, struct_size in *. lia.
  Qed.

  Lemma str_base_top :
    str_base = (bv_unsigned top - 8 - str_len)%Z.
  Proof. unfold str_base. pose proof span_pad. lia. Qed.

  Lemma string_base_eq :
    string_base_addr top argv envp execfn = Z_to_bv 64 str_base.
  Proof.
    pose proof str_base_top. unfold str_len in *.
    unfold string_base_addr, nat_to_word.
    rewrite <- (Z_to_bv_bv_unsigned top) at 1. rewrite lit_sub_lit. f_equal. lia.
  Qed.

  (* ---------------------------------------------------------------------- *)
  Definition head_bytes : list byte :=
    le8 (Z_to_bv 64 argc)
    ++ u64s argv_ptrs ++ le8 (Z_to_bv 64 0)
    ++ u64s envp_ptrs ++ le8 (Z_to_bv 64 0)
    ++ auxv_bytes la ph entry (in_uid inp) (in_gid inp) (in_hwcap inp)
         (Z_to_bv 64 rnd_addr) (at_execfn_ptr top execfn)
    ++ repeat (Z_to_bv 8 0) gap_len.

  Definition tail_bytes : list byte :=
    repeat (Z_to_bv 8 0) pad_nat
    ++ flatten_strings argv ++ flatten_strings envp ++ execfn ++ [Z_to_bv 8 0]
    ++ repeat (Z_to_bv 8 0) 8.

  Lemma build_stack_bytes_eq :
    entry_stack_image inp mb ph entry sp rnd
    = head_bytes ++ at_random_bytes (ed_random rnd) ++ tail_bytes.
  Proof.
    unfold entry_stack_image. rewrite build_stack_bytes_split_random.
    unfold block_below_random, block_above_random, head_bytes, tail_bytes.
    cbv zeta. rewrite !lay_rseq, string_base_eq, at_random_ptr_eq.
    rewrite string_addrs_eq. cbv beta iota. cbn [fst snd].
    change (Z_to_bv 64 (str_base + total_arg_bytes argv)) with (Z_to_bv 64 env_base).
    rewrite string_addrs_eq. cbv beta iota. cbn [fst snd].
    rewrite !flat_map_word_le8, !word_le8_le8.
    unfold argv_ptrs, envp_ptrs, len_word, argc, gap_len, pad_nat.
    rewrite <- !app_assoc. reflexivity.
  Qed.

  Lemma length_head_bytes :
    Z.of_nat (length head_bytes) = (struct_size - 16)%Z.
  Proof.
    unfold head_bytes. rewrite !app_length, !length_le8, !u64s_length, repeat_length.
    rewrite length_auxv_bytes, lay_rseq.
    unfold argv_ptrs, envp_ptrs. rewrite !map_length, !str_ptrs_length.
    pose proof struct_size_parts. unfold block_items, gap_len in *. lia.
  Qed.

  (* the pad, the strings and the eight-byte slot [create_init_stack_vma]
     skipped -- [tail_bytes] carries that slot, so the +8 is part of it *)
  Lemma length_tail_bytes :
    Z.of_nat (length tail_bytes) = (pad_len + str_len + 8)%Z.
  Proof.
    unfold tail_bytes. rewrite !app_length, !repeat_length. cbn [length].
    pose proof (flatten_strings_length argv). pose proof (flatten_strings_length envp).
    unfold pad_len, str_len, launch_string_bytes. lia.
  Qed.

  Lemma build_stack_bytes_length :
    (Z.of_nat (length (entry_stack_image inp mb ph entry sp rnd))
     = struct_size + pad_len + str_len + 8)%Z.
  Proof. pose proof entry_image_length_raw. unfold raw_len in *. lia. Qed.

  (* ---------------------------------------------------------------------- *)
  Notation m0 := (wrap_mem inp mb ph entry sp rnd).
  Notation eimg := (entry_stack_image inp mb ph entry sp rnd).
  Notation wlo := (stack_window_lo (in_kernel inp) mb rnd).
  Hypothesis SPLO : (wlo <= usp)%Z.
  Hypothesis IMGHI : (usp + Z.of_nat (length eimg) <= 2^64)%Z.

  Lemma usp_fit : (usp + raw_len <= 2 ^ 64)%Z.
  Proof. pose proof IMGHI. rewrite entry_image_length_raw in *. lia. Qed.

  Lemma entry_image_eq :
    eimg = head_bytes ++ at_random_bytes (ed_random rnd) ++ tail_bytes.
  Proof. exact build_stack_bytes_eq. Qed.

  Lemma entry_image_length : (Z.of_nat (length eimg) = raw_len)%Z.
  Proof. exact entry_image_length_raw. Qed.

  (* AsanInit.v:913 / :950 -- [Hu]. *)
  Lemma u_at_random_ptr :
    bv_unsigned (at_random_ptr sp rseq argv envp) = (usp + struct_size - 16)%Z.
  Proof.
    pose proof usp_fit. pose proof raw_len_nonneg. pose proof (bv_unsigned_in_range 64 sp) as R.
    unfold bv_modulus in R. cbn in R.
    rewrite at_random_ptr_eq. unfold rnd_addr. apply unsigned_lit.
    unfold raw_len in *. lia.
  Qed.

  (* AsanInit.v:917 / :955 -- [Ha]. *)
  Lemma at_random_ptr_off : forall i : Z,
    (at_random_ptr sp rseq argv envp + nat_to_word (Z.to_nat i))%bv
    = Z_to_bv 64 (usp + struct_size - 16 + i) \/ (i < 0)%Z.
  Proof.
    intros i. destruct (Z_lt_dec i 0) as [Hi|Hi]; [right; exact Hi|left].
    rewrite at_random_ptr_eq. unfold nat_to_word, rnd_addr.
    rewrite lit_add_lit. f_equal. lia.
  Qed.

  Lemma wr_at_sub : forall m a n a' n', wr_at segs m a n -> (a <= a')%Z -> (a' + n' <= a + n)%Z -> wr_at segs m a' n'.
  Proof.
    intros m a n a' n' (Ha & Hn & H) H1 H2. split; [lia|]. split; [lia|].
    intros i Hi. replace (a' + i)%Z with (a + (a' - a + i))%Z by lia. apply H. lia.
  Qed.

  Lemma rw_cells_of_parts : forall m A cs,
    cells_wf cs -> bytes_at segs m A (cells_bytes cs) -> wr_at segs m A (Z.of_nat (cells_size cs)) -> rw_cells segs m A cs.
  Proof. intros m A cs Hwf Hb Hw. split; [split; assumption| exact Hw]. Qed.

  Lemma init_wr : wr_at segs m0 usp raw_len.
  Proof.
    apply (wr_at_sub _ _ _ _ _ (init_stack_wr inp mb ph entry sp rnd SPLO IMGHI)); [lia|].
    rewrite entry_image_length. lia.
  Qed.

  Lemma init_pieces :
    bytes_at segs m0 usp (le8 (Z_to_bv 64 argc)) /\
    bytes_at segs m0 (usp + 8) (u64s (argv_ptrs ++ [Z_to_bv 64 0])) /\
    bytes_at segs m0 (usp + 8 * (argc + 2)) (u64s (envp_ptrs ++ [Z_to_bv 64 0])) /\
    bytes_at segs m0 (usp + 8 * (argc + envc + 3))
      (auxv_bytes la ph entry (in_uid inp) (in_gid inp) (in_hwcap inp)
         (Z_to_bv 64 rnd_addr) (at_execfn_ptr top execfn)) /\
    bytes_at segs m0 rnd_addr (at_random_bytes (ed_random rnd)) /\
    bytes_at segs m0 str_base (flatten_strings argv) /\
    bytes_at segs m0 env_base (flatten_strings envp).
  Proof.
    pose proof (init_stack_bytes inp mb ph entry sp rnd SPLO IMGHI) as B.
    rewrite entry_image_eq in B. unfold head_bytes, tail_bytes in B.
    repeat rewrite <- app_assoc in B.
    pose proof raw_len_nonneg as RN. pose proof struct_size_parts as SP.
    pose proof (flatten_strings_length argv) as L1.
    pose proof (flatten_strings_length envp) as L2.
    apply bytes_at_app in B. destruct B as [B0 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B1 B].
      rewrite u64s_length in B. unfold argv_ptrs at 1 in B. rewrite map_length, str_ptrs_length in B.
    apply bytes_at_app in B. destruct B as [B2 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B3 B].
      rewrite u64s_length in B. unfold envp_ptrs at 1 in B. rewrite map_length, str_ptrs_length in B.
    apply bytes_at_app in B. destruct B as [B4 B]. rewrite length_le8 in B.
    apply bytes_at_app in B. destruct B as [B5 B].
      rewrite length_auxv_bytes, lay_rseq in B.
    apply bytes_at_app in B. destruct B as [B6 B]. rewrite repeat_length in B.
    apply bytes_at_app in B. destruct B as [B7 B]. rewrite length_at_random_bytes in B.
    apply bytes_at_app in B. destruct B as [B8 B]. rewrite repeat_length in B.
    apply bytes_at_app in B. destruct B as [B9 B]. rewrite L1 in B.
    apply bytes_at_app in B. destruct B as [B10 B].
    repeat match goal with |- _ /\ _ => split end.
    - exact B0.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r.
      apply (proj2 (bytes_at_app segs m0 _ _ _)). split; [exact B1|].
      rewrite u64s_length. unfold argv_ptrs at 1. rewrite map_length, str_ptrs_length.
      replace (usp + 8 + Z.of_nat (8 * length argv))%Z
        with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv))%Z by lia. exact B2.
    - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r.
      apply (proj2 (bytes_at_app segs m0 _ _ _)). split.
      + replace (usp + 8 * (argc + 2))%Z
          with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8)%Z
          by (unfold argc; lia). exact B3.
      + rewrite u64s_length. unfold envp_ptrs at 1. rewrite map_length, str_ptrs_length.
        replace (usp + 8 * (argc + 2) + Z.of_nat (8 * length envp))%Z
          with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8
                + Z.of_nat (8 * length envp))%Z by (unfold argc; lia). exact B4.
    - replace (usp + 8 * (argc + envc + 3))%Z
        with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8
              + Z.of_nat (8 * length envp) + Z.of_nat 8)%Z by (unfold argc, envc; lia).
      exact B5.
    - replace rnd_addr
        with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8
              + Z.of_nat (8 * length envp) + Z.of_nat 8
              + Z.of_nat (auxv_size rseq) + Z.of_nat gap_len)%Z
        by (unfold rnd_addr, block_items in *; lia).
      exact B7.
    - replace str_base
        with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8
              + Z.of_nat (8 * length envp) + Z.of_nat 8
              + Z.of_nat (auxv_size rseq) + Z.of_nat gap_len + 16
              + Z.of_nat pad_nat)%Z
        by (unfold str_base, pad_len, block_items in *; lia).
      exact B9.
    - replace env_base
        with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8
              + Z.of_nat (8 * length envp) + Z.of_nat 8
              + Z.of_nat (auxv_size rseq) + Z.of_nat gap_len + 16
              + Z.of_nat pad_nat + total_arg_bytes argv)%Z
        by (unfold env_base, str_base, pad_len, block_items in *; lia).
      exact B10.
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
    destruct init_pieces as (_ & _ & _ & _ & _ & B6 & _).
    pose proof (flatten_strings_length argv).
    pose proof (bytes_at_slice m0 str_base (flatten_strings argv) (Z.to_nat off) (length s + 1) B6 ltac:(lia)) as B.
    rewrite Hf in B. replace (str_base + Z.of_nat (Z.to_nat off))%Z with (str_base + off)%Z in B by lia. exact B.
  Qed.

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
    apply str_ptrs_bounds in E. pose proof raw_len_nonneg. pose proof usp_fit.
    pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
    pose proof (flatten_strings_length argv). pose proof (flatten_strings_length envp).
    pose proof (total_arg_bytes_nonneg envp).
    unfold env_base. rewrite unsigned_lit; [lia|].
    unfold str_base, raw_len, str_len, launch_string_bytes in *. lia.
  Qed.

  Lemma envp_ptr_bounds : forall i p, nth_error envp_ptrs i = Some p ->
    (env_base <= bv_unsigned p < env_base + total_arg_bytes envp)%Z.
  Proof.
    intros i p Hn. unfold envp_ptrs in Hn. rewrite nth_error_map in Hn.
    destruct (nth_error (str_ptrs env_base envp) i) as [q|] eqn:E; [|discriminate]. injection Hn as <-.
    apply str_ptrs_bounds in E. pose proof raw_len_nonneg. pose proof usp_fit.
    pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R.
    pose proof (flatten_strings_length argv). pose proof (flatten_strings_length envp).
    pose proof (total_arg_bytes_nonneg argv).
    rewrite unsigned_lit; [lia|].
    unfold env_base, str_base, raw_len, str_len, launch_string_bytes in *. lia.
  Qed.
End Layout.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Fixpoint segs_bot (sg : list Segment) : Z :=
  match sg with
  | [] => 2^64
  | s0 :: rest => Z.min (Z.of_N (seg_base s0)) (segs_bot rest)
  end.

#[using="Type"] Lemma find_segment_low : forall sg a n, (a < segs_bot sg)%Z -> find_segment sg a n = None.
Proof.
  induction sg as [|s0 sg IH]; intros a n Ha; [reflexivity|]. cbn [find_segment segs_bot] in *.
  replace (Z.leb (Z.of_N (seg_base s0)) a) with false by (symmetry; apply Z.leb_gt; lia).
  cbn [andb]. apply IH; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ro_addr_off_image : forall x : word,
  (bv_unsigned x < segs_bot segs \/ segs_top segs <= bv_unsigned x)%Z -> ro_addr segs x = false.
Proof.
  intros x [Hx|Hx]; unfold ro_addr.
  - rewrite find_segment_low by lia. reflexivity.
  - rewrite find_segment_high by lia. reflexivity.
Qed.

#[using="Type"] Lemma init_mem_inv' : forall inp mb ph entry sp draw,
  (stack_window_lo (in_kernel inp) mb draw <= bv_unsigned sp)%Z ->
  (bv_unsigned sp
   + Z.of_nat (length (entry_stack_image inp mb ph entry sp draw)) <= 2^64)%Z ->
  (segs_top segs <= stack_window_lo (in_kernel inp) mb draw)%Z ->
  mem_inv segs (wrap_mem inp mb ph entry sp draw).
Proof.
  intros inp mb ph entry sp draw H1 H2 H3. apply init_mem_inv; try assumption.
  intros a Ha. apply find_segment_high; lia.
Qed.
End WithSegs.

(* [comment removed for export] *)
Ltac exact_evt H :=
  lazymatch type of H with evt _ _ ?s1 =>
    lazymatch goal with |- evt _ _ ?s2 =>
      replace s2 with s1; [exact H|];
      cbv delta [mkR]; repeat first [reflexivity | lia | progress f_equal]
    end
  end.

