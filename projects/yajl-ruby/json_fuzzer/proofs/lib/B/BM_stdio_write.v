(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac ITree Nodes Decode SysStep MonadX SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages ITreeA NodesA SysStepA MonadA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit BM_monadx BM_syscalls BM_stdio_lib BX_file.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition STDIO_WRITE : Z := 0x980b4.
Definition STDIO_WRITE_DEPTH : Z := 112.
Definition SITE_A : Z := 0x9813c.
Definition SITE_B : Z := 0x981c4.

(* [comment removed for export] *)
Definition boxed (P : Prop) : Prop := P.

(* [comment removed for export] *)
Definition iovs_of (buf s : list Z) : list (list byte) :=
  match buf with [] => [to_bytes s] | _ => [to_bytes buf; to_bytes s] end.

(* [comment removed for export] *)
End RC__1.
Ltac src_now SRC SEPS MU LSB :=
  unfold boxed in SRC;
  lazymatch goal with
  | |- bytes_at _ ?m' ?S (to_bytes ?s) =>
      destruct SEPS as [-> | [SEP1 SEP2]];
      [ apply bytes_at_nil; lia
      | apply (bytes_at_transport _ _ _ m' _ _ SRC MU); cbn [disjoint_from]; rewrite LSB; unfold zlength in SEP1, SEP2; lia ]
  end.

(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma writev_loop_unfold {St} : forall fuel fd iovs,
  @writev_loop St fuel fd iovs =
  (k <- msys (NWritev fd (map to_bytes iovs)) (dec_writev (zlength (zconcat iovs))) ;;
   if k =? zlength (zconcat iovs) then mret tt
   else match fuel with O => munr | S fuel' => writev_loop fuel' fd (advance_iovs iovs k) end).
Proof. intros [|fuel] fd iovs; reflexivity. Qed.

(* [comment removed for export] *)
Definition loop_iovs (buf s : list Z) (two : bool) (i : nat) : list (list Z) :=
  if two then [skipn i buf; s] else [skipn i s].
Definition loop_rem (buf s : list Z) (two : bool) (i : nat) : Z :=
  if two then zlength buf - Z.of_nat i + zlength s else zlength s - Z.of_nat i.
Definition loop_cnt (two : bool) : Z := if two then 2 else 1.

Lemma to_bytes_skipn : forall i l, to_bytes (skipn i l) = skipn i (to_bytes l).
Proof. intros. unfold to_bytes. rewrite skipn_map. reflexivity. Qed.
Lemma length_to_bytes : forall l, length (to_bytes l) = length l.
Proof. intros. unfold to_bytes. apply length_map. Qed.

Lemma bytes_at_skip : forall m A bs i, bytes_at bsegs m A bs -> (i <= length bs)%nat ->
  bytes_at bsegs m (A + Z.of_nat i) (skipn i bs).
Proof.
  intros m A bs i H Hi. rewrite <- (firstn_skipn i bs) in H. apply bytes_at_app in H as [_ H].
  rewrite firstn_length_le in H by lia. exact H.
Qed.

Lemma zconcat_loop_iovs : forall (buf s : list Z) (two : bool) (i : nat),
  (i <= (if two then length buf else length s))%nat ->
  zlength (zconcat (loop_iovs buf s two i)) = loop_rem buf s two i.
Proof.
  intros buf s two i Hi. unfold loop_iovs, loop_rem, zlength. destruct two; cbn [zconcat];
  rewrite ?length_app, ?length_skipn; cbn [length]; lia.
Qed.

Lemma length_concat_map_to_bytes : forall l, length (concat (map to_bytes l)) = length (zconcat l).
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [map concat zconcat]. rewrite !length_app, length_to_bytes, IH. reflexivity. Qed.

(* [comment removed for export] *)
End RC__2.
Ltac exact_at H :=
  lazymatch goal with |- bytes_at _ _ ?g _ =>
    lazymatch type of H with bytes_at _ _ ?a _ => replace g with a by lia; exact H end end.

Section RC__3.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma frame_iov_bytes2 : forall m q j0 w8 w16 w24 w32 rest,
  rw_cells bsegs m q (CB 8 j0 :: C8 w8 :: C8 w16 :: C8 w24 :: C8 w32 :: rest) ->
  bytes_at bsegs m (q + 8) (iovec_bytes [(w8, w16); (w24, w32)]).
Proof.
  intros m q j0 w8 w16 w24 w32 rest [[WF FB] _].
  cbn [cells_wf cell_wf] in WF. destruct WF as [L8 _].
  cbn [cells_bytes cbytes] in FB.
  apply bytes_at_app in FB as [_ FB]. rewrite L8 in FB.
  cbn [iovec_bytes flat_map fst snd]. rewrite app_nil_r.
  apply bytes_at_app in FB as [F1 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [F2 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [F3 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [F4 _].
  apply bytes_at_app. rewrite length_app, !length_le8. split.
  - apply bytes_at_app. rewrite length_le8. split; [exact_at F1| exact_at F2].
  - apply bytes_at_app. rewrite length_le8. split; [exact_at F3| exact_at F4].
Qed.

Lemma frame_iov_bytes1 : forall m q j0 w8 w16 w24 w32 rest,
  rw_cells bsegs m q (CB 8 j0 :: C8 w8 :: C8 w16 :: C8 w24 :: C8 w32 :: rest) ->
  bytes_at bsegs m (q + 24) (iovec_bytes [(w24, w32)]).
Proof.
  intros m q j0 w8 w16 w24 w32 rest [[WF FB] _].
  cbn [cells_wf cell_wf] in WF. destruct WF as [L8 _].
  cbn [cells_bytes cbytes] in FB.
  apply bytes_at_app in FB as [_ FB]. rewrite L8 in FB.
  cbn [iovec_bytes flat_map fst snd]. rewrite app_nil_r.
  apply bytes_at_app in FB as [F1 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [F2 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [F3 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [F4 _].
  apply bytes_at_app. rewrite length_le8. split; [exact_at F3| exact_at F4].
Qed.

(* [comment removed for export] *)
Lemma at_node_writev_loop : forall ms (fd : Z) (buf s : list Z) (two : bool) (i : nat) (B S q iov : Z)
    (w8 w16 w24 w32 : word) (j0 : list byte) (rest : list cell),
  ms_svc_pending ms = Some (Z_to_bv 64 66) -> ms_rom ms = seg_rom bsegs ->
  (fd = 1 \/ fd = 2) -> areg ms 10 = Z_to_bv 64 fd -> areg ms 12 = Z_to_bv 64 (loop_cnt two) ->
  areg ms 11 = Z_to_bv 64 iov -> iov = (if two then q + 8 else q + 24) ->
  rw_cells bsegs (ms_mem ms) q (CB 8 j0 :: C8 w8 :: C8 w16 :: C8 w24 :: C8 w32 :: rest) ->
  (if two then w8 = Z_to_bv 64 (B + Z.of_nat i) /\ w16 = Z_to_bv 64 (zlength buf - Z.of_nat i)
               /\ w24 = Z_to_bv 64 S /\ w32 = Z_to_bv 64 (zlength s) /\ (i <= length buf)%nat
   else w24 = Z_to_bv 64 (S + Z.of_nat i) /\ w32 = Z_to_bv 64 (zlength s - Z.of_nat i) /\ (i <= length s)%nat /\ S + Z.of_nat i < 2^64) ->
  bytes_at bsegs (ms_mem ms) B (to_bytes buf) -> bytes_at bsegs (ms_mem ms) S (to_bytes s) ->
  zlength buf + zlength s <= WRITEV_MAX -> 0 <= q -> q + 40 <= 0x800000000000 -> B + zlength buf <= 0x800000000000 -> S + zlength s <= 0x800000000000 ->
  at_node bsegs (NWritev fd (map to_bytes (loop_iovs buf s two i))) ms.
Proof.
  intros ms fd buf s two i B S q iov w8 w16 w24 w32 j0 rest SVC ROM FD A10 A12 A11 -> FR FOK BUFB SRC LENS Q0 Qhi BBhi SShi.
  pose proof (bytes_at_bound _ _ _ _ BUFB) as BB. rewrite length_to_bytes in BB.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite length_to_bytes in BS.
  unfold zlength, WRITEV_MAX in *.
  cbn [at_node]. rewrite SVC, ROM, A10, A11, A12. split_spine; try reflexivity; try exact FD.
  - destruct two; reflexivity.
  - destruct two; cbn; lia.
  - rewrite length_concat_map_to_bytes.
    pose proof (zconcat_loop_iovs buf s two i) as E. unfold zlength in E. rewrite E.
    2:{ destruct two; [destruct FOK as (_&_&_&_&H)|destruct FOK as (_&_&H&_)]; exact H. }
    unfold writev_node_max, loop_rem, zlength. destruct two; lia.
  - (* [comment removed for export] *)
    rewrite unsigned_lit by (destruct two; lia). unfold TASK_SIZE. destruct two; cbn [loop_iovs map length Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
  - destruct two.
    + destruct FOK as (-> & -> & -> & -> & ILE).
      exists [(Z_to_bv 64 (B + Z.of_nat i), Z_to_bv 64 (Z.of_nat (length buf) - Z.of_nat i)); (Z_to_bv 64 S, Z_to_bv 64 (Z.of_nat (length s)))].
      rewrite unsigned_lit by lia. split; [apply (frame_iov_bytes2 _ _ _ _ _ _ _ _ FR)|].
      constructor; [|constructor; [|constructor]]; cbn [fst snd].
      * rewrite length_to_bytes, length_skipn, unsigned_lit by lia. split; [f_equal; lia|].
        split; [| unfold TASK_SIZE; lia].
        rewrite to_bytes_skipn. apply bytes_at_skip; [exact BUFB| rewrite length_to_bytes; exact ILE].
      * rewrite length_to_bytes, unsigned_lit by lia. split; [reflexivity| split; [exact SRC| unfold TASK_SIZE; lia]].
    + destruct FOK as (-> & -> & ILE & SIhi).
      exists [(Z_to_bv 64 (S + Z.of_nat i), Z_to_bv 64 (Z.of_nat (length s) - Z.of_nat i))].
      rewrite unsigned_lit by lia. split; [apply (frame_iov_bytes1 _ _ _ _ _ _ _ _ FR)|].
      constructor; [|constructor]; cbn [fst snd].
      rewrite length_to_bytes, length_skipn, unsigned_lit by lia. split; [f_equal; lia|].
      split; [| unfold TASK_SIZE; lia].
      rewrite to_bytes_skipn. apply bytes_at_skip; [exact SRC| rewrite length_to_bytes; exact ILE].
Qed.

(* [comment removed for export] *)
Lemma list_eq_nth_error : forall {X} (xs ys : list X),
  length xs = length ys -> (forall i, (i < length xs)%nat -> nth_error xs i = nth_error ys i) -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] L H; cbn in L; try discriminate; [reflexivity|].
  pose proof (H 0%nat ltac:(cbn; lia)) as H0. cbn in H0. injection H0 as ->. f_equal.
  apply IH; [lia|]. intros i Hi. exact (H (S i) ltac:(cbn; lia)).
Qed.

Lemma bytes_at_det : forall m a xs ys,
  bytes_at bsegs m a xs -> bytes_at bsegs m a ys -> length xs = length ys -> xs = ys.
Proof.
  intros m a xs ys (_ & _ & Hx) (_ & _ & Hy) L. apply list_eq_nth_error; [exact L|].
  intros i Hi. rewrite <- Hx by exact Hi. rewrite <- Hy by lia. reflexivity.
Qed.

Lemma iovec_bytes_inj : forall i1 i2, length i1 = length i2 -> iovec_bytes i1 = iovec_bytes i2 -> i1 = i2.
Proof.
  induction i1 as [|[b l] i1 IH]; intros [|[b' l'] i2] L E; cbn in L; try discriminate; [reflexivity|].
  cbn [iovec_bytes flat_map fst snd] in E. rewrite <- !app_assoc in E.
  assert (E1 : le8 b = le8 b').
  { apply (f_equal (firstn 8)) in E. rewrite !firstn_app, !length_le8, !Nat.sub_diag, !firstn_O, !app_nil_r in E.
    rewrite !firstn_all2 in E by (rewrite length_le8; lia). exact E. }
  apply (f_equal (skipn 8)) in E. rewrite !skipn_app, !length_le8, !Nat.sub_diag, !skipn_O in E.
  rewrite !skipn_all2 in E by (rewrite length_le8; lia). cbn [app] in E.
  assert (E2 : le8 l = le8 l').
  { apply (f_equal (firstn 8)) in E. rewrite !firstn_app, !length_le8, !Nat.sub_diag, !firstn_O, !app_nil_r in E.
    rewrite !firstn_all2 in E by (rewrite length_le8; lia). exact E. }
  apply (f_equal (skipn 8)) in E. rewrite !skipn_app, !length_le8, !Nat.sub_diag, !skipn_O in E.
  rewrite !skipn_all2 in E by (rewrite length_le8; lia).
  apply (f_equal le_bytes_to_word) in E1. apply (f_equal le_bytes_to_word) in E2. rewrite !le_bytes_to_word_le8 in E1, E2.
  subst b' l'. f_equal. apply IH; [lia|]. exact E.
Qed.

(* [comment removed for export] *)
Lemma node_policy_writev_loop : forall ms (fd : Z) (buf s : list Z) (two : bool) (i : nat) (B S q iov : Z)
    (w8 w16 w24 w32 : word) (j0 : list byte) (rest : list cell) (P : acc -> Prop),
  (forall a k, q <= a -> a + Z.of_nat k <= q + 112 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, B <= a -> a + Z.of_nat k <= B + zlength buf -> P (Z_to_bv 64 a, k)) ->
  (forall a k, S <= a -> a + Z.of_nat k <= S + zlength s -> P (Z_to_bv 64 a, k)) ->
  areg ms 11 = Z_to_bv 64 iov -> iov = (if two then q + 8 else q + 24) ->
  rw_cells bsegs (ms_mem ms) q (CB 8 j0 :: C8 w8 :: C8 w16 :: C8 w24 :: C8 w32 :: rest) ->
  (if two then w8 = Z_to_bv 64 (B + Z.of_nat i) /\ w16 = Z_to_bv 64 (zlength buf - Z.of_nat i)
               /\ w24 = Z_to_bv 64 S /\ w32 = Z_to_bv 64 (zlength s) /\ (i <= length buf)%nat
   else w24 = Z_to_bv 64 (S + Z.of_nat i) /\ w32 = Z_to_bv 64 (zlength s - Z.of_nat i) /\ (i <= length s)%nat /\ S + Z.of_nat i < 2^64) ->
  0 <= q -> q + 40 <= 2^64 -> 0 <= B -> B + zlength buf < 2^64 -> 0 <= S < 2^64 -> S + zlength s <= 2^64 ->
  zlength buf + zlength s <= WRITEV_MAX ->
  node_policy bsegs P (NWritev fd (map to_bytes (loop_iovs buf s two i))) ms.
Proof.
  intros ms fd buf s two i B S q iov w8 w16 w24 w32 j0 rest P PFR PBUF PSRC A11 -> FR FOK Q0 Qhi B0 Bhi S0 Shi LENS.
  unfold WRITEV_MAX in LENS. unfold node_policy. cbn [node_ranges]. rewrite A11.
  assert (LEN : length (map to_bytes (loop_iovs buf s two i)) = (if two then 2 else 1)%nat)
    by (unfold loop_iovs; destruct two; reflexivity).
  rewrite LEN. unfold zlength in *.
  assert (UI : bv_unsigned (Z_to_bv 64 (if two then q + 8 else q + 24)) = (if two then q + 8 else q + 24))
    by (destruct two; apply unsigned_lit; lia).
  rewrite UI. split.
  - intros lo hi a k Hin Hlo Hhi Ha. destruct Hin as [Hin|[]]. injection Hin as <- <-.
    apply PFR; destruct two; cbn in Hhi; lia.
  - intros iovs Hb HF lo hi a k Hin Hlo Hhi Ha.
    pose proof (Forall2_length HF) as LI. rewrite LEN in LI.
    destruct two.
    + destruct FOK as (-> & -> & -> & -> & ILE).
      pose proof (frame_iov_bytes2 _ _ _ _ _ _ _ _ FR) as OURS.
      assert (iovs = [(Z_to_bv 64 (B + Z.of_nat i), Z_to_bv 64 (Z.of_nat (length buf) - Z.of_nat i)); (Z_to_bv 64 S, Z_to_bv 64 (Z.of_nat (length s)))]) as ->.
      { apply iovec_bytes_inj; [cbn; lia|]. eapply bytes_at_det; [exact Hb | exact OURS | rewrite !length_iovec_bytes; cbn; lia]. }
      cbn [iov_ranges map fst snd In] in Hin.
      destruct Hin as [Hin|[Hin|[]]]; injection Hin as <- <-.
      * rewrite (unsigned_lit (B + Z.of_nat i)) in Hlo, Hhi by lia. rewrite (unsigned_lit (Z.of_nat (length buf) - Z.of_nat i)) in Hhi by lia. apply PBUF; lia.
      * rewrite (unsigned_lit S) in Hlo, Hhi by lia. rewrite (unsigned_lit (Z.of_nat (length s))) in Hhi by lia. apply PSRC; lia.
    + destruct FOK as (-> & -> & ILE & SIhi).
      pose proof (frame_iov_bytes1 _ _ _ _ _ _ _ _ FR) as OURS.
      assert (iovs = [(Z_to_bv 64 (S + Z.of_nat i), Z_to_bv 64 (Z.of_nat (length s) - Z.of_nat i))]) as ->.
      { apply iovec_bytes_inj; [cbn; lia|]. eapply bytes_at_det; [exact Hb | exact OURS | rewrite !length_iovec_bytes; cbn; lia]. }
      cbn [iov_ranges map fst snd In] in Hin.
      destruct Hin as [Hin|[]]; injection Hin as <- <-. rewrite (unsigned_lit (S + Z.of_nat i)) in Hlo, Hhi by lia. rewrite (unsigned_lit (Z.of_nat (length s) - Z.of_nat i)) in Hhi by lia. apply PSRC; lia.
Qed.

Section StdioWrite.
  (* [comment removed for export] *)
  Context {St : Type}.


  Definition stdio_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (Fp : Z) (flags : word) (B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
      (l : Z) (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - STDIO_WRITE_DEPTH, bv_unsigned sp); (Fp + 32, Fp + 64)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' Fp (file_cells flags (B + bufsize) B B wfn B bufsize fd mode lbf tail)
      /\ ssp_cells m' canary
      /\ st' = st.

  (* [comment removed for export] *)
  Lemma stdio_write_exit :
    forall (ra' gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x6 t3 t4 t5 t6 : word)
           (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (m0 m : mem) (st : St)
           (Fp : Z) (flags : word) (wend wpos wbase B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
           (lens lo : Z) (canary : word) (j0 : list byte) (w8 w16 w24 w32 : word) (P : acc -> Prop),
      (forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
      (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
      (forall a k, Fp <= a -> a + Z.of_nat k <= Fp + 232 -> P (Z_to_bv 64 a, k)) ->
      rw_cells bsegs m Fp (file_cells flags wend wpos wbase wfn B bufsize fd mode lbf tail) ->
      rw_cells bsegs m (bv_unsigned sp + -112)
        [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 canary; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      munch [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
      stk bsegs m lo (bv_unsigned sp + -112) -> (lo <= bv_unsigned sp + -112) -> (0x603000 <= lo) -> (bv_unsigned sp < 2^64) ->
      rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells bsegs m ssp_guard [C8 canary] ->
      (0 <= Fp) -> (Fp + 232 <= lo) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (0 <= B) -> (0 <= bufsize) -> (B + bufsize < 2^64) -> (0 <= lens < 2^64) ->
      evtA bsegs P (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
                   lens lo canary m0 st tt st)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 lens) (Z_to_bv 64 Fp) a0 a1 a2 a3 a4 a5 a6 a7
                 x2 x3 x4 (Z_to_bv 64 ssp_guard) x6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x98148) fc None m (seg_rom bsegs)).
  Proof.
    intros until P. intros PSTK PIMG PFILE FC FR MU WM MI ST LO GLO SPHI GOT GUARD Fp0 FPLO FSEP1 FSEP2 B0 BS0 BShi LENS.
    unfold got_ssp, ssp_guard in *. unfold file_cells in FC.
    do 6 step. step. step. step. step. if_false.
    do 10 step.
    release_frame FR ST (bv_unsigned sp).
    unfold stdio_write_post, file_cells, STDIO_WRITE_DEPTH. sys_finish.
    + split; [exact GOT| exact GUARD].
    + reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition adv_post (two : bool) (i : nat) (k : Z) (ra' gp tp t0 t1 t2 a6 t3 t4 t5 t6 : word)
      (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem)
      (Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
      (buf s : list Z) (S lo : Z) (canary : word) (j0 : list byte) : machine_state -> Prop :=
    fun ms' => exists (two' : bool) (i' : nat) (a3' a4' a5' w8' w16' w24' w32' : word) (m' : mem),
      advance_iovs (loop_iovs buf s two i) k = loop_iovs buf s two' i'
      /\ ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
                   (Z_to_bv 64 fd) (Z_to_bv 64 (bv_unsigned sp + (if two' then -104 else -88))) (Z_to_bv 64 (loop_cnt two'))
                   a3' a4' a5' a6 (Z_to_bv 64 66) (Z_to_bv 64 (loop_cnt two'))
                   (Z_to_bv 64 (bv_unsigned sp + (if two then -104 else -88)))
                   (Z_to_bv 64 (bv_unsigned sp + (if two' then -104 else -88)))
                   (Z_to_bv 64 ssp_guard) (Z_to_bv 64 (loop_rem buf s two' i')) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 SITE_B) fc None m' (seg_rom bsegs)
      /\ rw_cells bsegs m' Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail)
      /\ rw_cells bsegs m' (bv_unsigned sp + -112)
           [CB 8 j0; C8 w8'; C8 w16'; C8 w24'; C8 w32'; C8 canary; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ (if two' then w8' = Z_to_bv 64 (B + Z.of_nat i') /\ w16' = Z_to_bv 64 (zlength buf - Z.of_nat i')
                     /\ w24' = Z_to_bv 64 S /\ w32' = Z_to_bv 64 (zlength s) /\ (i' <= length buf)%nat
          else w24' = Z_to_bv 64 (S + Z.of_nat i') /\ w32' = Z_to_bv 64 (zlength s - Z.of_nat i') /\ (i' <= length s)%nat /\ S + Z.of_nat i' < 2^64)
      /\ bytes_at bsegs m' B (to_bytes buf)
      /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] m0 m' /\ wmono bsegs m0 m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp + -112)
      /\ rw_cells bsegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells bsegs m' ssp_guard [C8 canary].

  Lemma stdio_write_advance :
    forall (two : bool) (i : nat) (k : Z)
           (ra' gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 t3 t4 t5 t6 : word)
           (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (m0 m : mem)
           (Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
           (buf s : list Z) (S lo : Z) (canary : word) (j0 : list byte) (w8 w16 w24 w32 : word) (P : acc -> Prop),
      (forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
      (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
      (forall a k, Fp <= a -> a + Z.of_nat k <= Fp + 232 -> P (Z_to_bv 64 a, k)) ->
      (forall a k, B <= a -> a + Z.of_nat k <= B + bufsize -> P (Z_to_bv 64 a, k)) ->
      (forall a k, S <= a -> a + Z.of_nat k <= S + zlength s -> P (Z_to_bv 64 a, k)) ->
      rw_cells bsegs m Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
      rw_cells bsegs m (bv_unsigned sp + -112)
        [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 canary; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      (if two then w8 = Z_to_bv 64 (B + Z.of_nat i) /\ w16 = Z_to_bv 64 (zlength buf - Z.of_nat i)
                   /\ w24 = Z_to_bv 64 S /\ w32 = Z_to_bv 64 (zlength s) /\ (i <= length buf)%nat
       else w24 = Z_to_bv 64 (S + Z.of_nat i) /\ w32 = Z_to_bv 64 (zlength s - Z.of_nat i) /\ (i <= length s)%nat /\ S + Z.of_nat i < 2^64) ->
      (1 <= k < loop_rem buf s two i) -> (zlength buf + zlength s <= WRITEV_MAX) ->
      bytes_at bsegs m B (to_bytes buf) ->
      munch [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
      stk bsegs m lo (bv_unsigned sp + -112) -> (lo <= bv_unsigned sp + -112) -> (0x603000 <= lo) -> (bv_unsigned sp < 2^64) ->
      rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells bsegs m ssp_guard [C8 canary] ->
      (fd = 1 \/ fd = 2) -> (0 <= Fp) -> (Fp + 232 <= lo) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (0 <= B) -> (B + zlength buf < 2^64) -> (0 <= S) -> (S + zlength s <= 2^64) ->
      (B + zlength buf <= lo \/ bv_unsigned sp <= B) ->
      evtA bsegs P (adv_post two i k ra' gp tp t0 t1 t2 a6 t3 t4 t5 t6 ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0
                   Fp flags wend B bufsize wfn fd mode lbf tail buf s S lo canary j0)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
                 (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (loop_cnt two)) (Z_to_bv 64 (bv_unsigned sp + (if two then -104 else -88))) x4 (Z_to_bv 64 ssp_guard)
                 (Z_to_bv 64 (loop_rem buf s two i)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x981d4) fc None m (seg_rom bsegs)).
  Proof.
    intros until P. intros PSTK PIMG PFILE PBUF PSRC FC FR FOK K LENS BUFB MU WM MI ST LO GLO SPHI GOT GUARD FD Fp0 FPLO FSEP1 FSEP2 B0 BBhi S0 Shi SEPB.
    unfold got_ssp, ssp_guard, loop_rem, WRITEV_MAX in *. unfold zlength in *. unfold file_cells in FC.
    pose proof (bytes_at_bound _ _ _ _ BUFB) as BB. rewrite length_to_bytes in BB.
    pose proof (length_to_bytes buf) as LBB.
    destruct two.
    - destruct FOK as (-> & -> & -> & -> & ILE). unfold loop_cnt.
      step. if_cases Hneg; zify_cond Hneg. 1:{ exfalso. rewrite ?land_W64_small in Hneg by lia. lia. }
      step. step.
      remember (Z.of_nat (length buf) - Z.of_nat i) as la eqn:Ela.
      destruct (Z.ltb_spec la k) as [ADV|STAY].
      + (* [comment removed for export] *)
        replace (v_sltu (Z_to_bv 64 la) (Z_to_bv 64 k)) with (Z_to_bv 64 1 : word).
        2:{ unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia. destruct (Z.ltb_spec0 la k); [reflexivity| exfalso; lia]. }
        step. step. step. step. step. step.
        rewrite (unsigned_lit la) by lia.
        replace (Z.land 18446744073709551615 la) with la by (rewrite Z.land_comm, land_W64_small by lia; reflexivity).
        rewrite (unsigned_lit la), (unsigned_lit k) by lia.
        step. step. step. if_cases Hb; zify_cond Hb. 1:{ exfalso. lia. }
        step. step.
        do 10 step.
        rewrite ?(unsigned_lit k), ?(unsigned_lit (Z.of_nat (length s))) by lia.
        rewrite ?(unsigned_lit (k - la)), ?(unsigned_lit (la + Z.of_nat (length s))) by lia.
        rewrite ?(unsigned_lit (Z.of_nat (length s))), ?(unsigned_lit (k - la)) in FR by lia.
        replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd : word) by (symmetry; apply sx32_small; lia).
        replace (Z_to_bv 64 (bv_swrap 32 (2 - 1)) : word) with (Z_to_bv 64 1 : word) by reflexivity.
        replace (Z_to_bv 64 (la + Z.of_nat (length s) - k) : word) with (Z_to_bv 64 (Z.of_nat (length s) - Z.of_nat (Z.to_nat (k - la))) : word) by (f_equal; lia).
        apply evtA_done. unfold adv_post, loop_rem, loop_cnt, zlength. exists false, (Z.to_nat (k - la)). do 8 eexists.
        split. { unfold advance_iovs, loop_iovs, zlength. rewrite length_skipn.
                 replace (Z.of_nat (length buf - i)) with la by lia.
                 destruct (Z.ltb_spec la k); [| exfalso; lia]. repeat f_equal; try lia. }
        split. { unfold SITE_B. cbv delta [mkR]. reflexivity. }
        split. { exact FC. }
        split. { exact FR. }
        split. { repeat split; try (f_equal; lia); lia. }
        exact (conj BUFB (conj MU (conj WM (conj MI (conj ST (conj GOT GUARD)))))).
      + replace (v_sltu (Z_to_bv 64 la) (Z_to_bv 64 k)) with (Z_to_bv 64 0 : word).
        2:{ unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia. destruct (Z.ltb_spec0 la k); [exfalso; lia| reflexivity]. }
        step. step. step. step. step. step.
        rewrite Z.land_0_l. rewrite (unsigned_lit 0) by lia. rewrite Z.sub_0_r. rewrite (unsigned_lit k) by lia.
        step. step. step. if_cases Hb; zify_cond Hb. 2:{ exfalso. lia. }
        step.
        do 10 step.
        rewrite ?(unsigned_lit k), ?(unsigned_lit la), ?(unsigned_lit (la + Z.of_nat (length s))) by lia.
        rewrite ?(unsigned_lit k), ?(unsigned_lit la) in FR by lia.
        replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd : word) by (symmetry; apply sx32_small; lia).
        replace (Z_to_bv 64 (bv_swrap 32 (2 - 0)) : word) with (Z_to_bv 64 2 : word) by reflexivity.
        replace (Z_to_bv 64 (la + Z.of_nat (length s) - k) : word)
           with (Z_to_bv 64 (Z.of_nat (length buf) - Z.of_nat (Z.to_nat k + i)%nat + Z.of_nat (length s)) : word) by (f_equal; lia).
        apply evtA_done. unfold adv_post, loop_rem, loop_cnt, zlength. exists true, (Z.to_nat k + i)%nat. do 8 eexists.
        split. { unfold advance_iovs, loop_iovs, zlength. rewrite length_skipn.
                 replace (Z.of_nat (length buf - i)) with la by lia.
                 destruct (Z.ltb_spec la k); [exfalso; lia|]. rewrite skipn_skipn. repeat f_equal; try lia. }
        split. { unfold SITE_B. cbv delta [mkR]. reflexivity. }
        split. { exact FC. }
        split. { exact FR. }
        split. { repeat split; try (f_equal; lia); lia. }
        exact (conj BUFB (conj MU (conj WM (conj MI (conj ST (conj GOT GUARD)))))).
    - destruct FOK as (-> & -> & ILE & SIhi). unfold loop_cnt.
      step. if_cases Hneg; zify_cond Hneg. 1:{ exfalso. rewrite ?land_W64_small in Hneg by lia. lia. }
      step. step.
      remember (Z.of_nat (length s) - Z.of_nat i) as ls eqn:Els.
      replace (v_sltu (Z_to_bv 64 ls) (Z_to_bv 64 k)) with (Z_to_bv 64 0 : word).
      2:{ unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia. destruct (Z.ltb_spec0 ls k); [exfalso; lia| reflexivity]. }
      step. step. step. step. step. step.
      rewrite Z.land_0_l. rewrite (unsigned_lit 0) by lia. rewrite Z.sub_0_r. rewrite (unsigned_lit k) by lia.
      step. step. step. if_cases Hb; zify_cond Hb. 2:{ exfalso. lia. }
      step.
      do 10 step.
      rewrite ?(unsigned_lit k), ?(unsigned_lit ls) by lia.
      rewrite ?(unsigned_lit k), ?(unsigned_lit ls), ?(unsigned_lit (S + Z.of_nat i)) in FR by lia.
      replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd : word) by (symmetry; apply sx32_small; lia).
      replace (Z_to_bv 64 (bv_swrap 32 (1 - 0)) : word) with (Z_to_bv 64 1 : word) by reflexivity.
      replace (Z_to_bv 64 (ls - k) : word) with (Z_to_bv 64 (Z.of_nat (length s) - Z.of_nat (Z.to_nat k + i)%nat) : word) by (f_equal; lia).
      apply evtA_done. unfold adv_post, loop_rem, loop_cnt, zlength. exists false, (Z.to_nat k + i)%nat. do 8 eexists.
      split. { unfold advance_iovs, loop_iovs. rewrite skipn_skipn. reflexivity. }
      split. { unfold SITE_B. cbv delta [mkR]. reflexivity. }
      split. { exact FC. }
      split. { exact FR. }
      split. { repeat split; try (f_equal; lia); lia. }
      exact (conj BUFB (conj MU (conj WM (conj MI (conj ST (conj GOT GUARD)))))).
  Qed.

  (* [comment removed for export] *)
  Lemma stdio_write_round :
    forall (KONT : Z -> @M St unit) (two siteA : bool) (i : nat)
           (ra' gp tp t0 t1 t2 a3 a4 a5 a6 x3 x4 t3 t4 t5 t6 : word)
           (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (m0 m : mem) (st : St)
           (Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
           (buf s : list Z) (S lo : Z) (canary : word) (j0 : list byte) (w8 w16 w24 w32 : word) (P : acc -> Prop),
      (forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
      (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
      (forall a k, Fp <= a -> a + Z.of_nat k <= Fp + 232 -> P (Z_to_bv 64 a, k)) ->
      (forall a k, B <= a -> a + Z.of_nat k <= B + bufsize -> P (Z_to_bv 64 a, k)) ->
      (forall a k, S <= a -> a + Z.of_nat k <= S + zlength s -> P (Z_to_bv 64 a, k)) ->
      rw_cells bsegs m Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
      rw_cells bsegs m (bv_unsigned sp + -112)
        [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 canary; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      (if two then w8 = Z_to_bv 64 (B + Z.of_nat i) /\ w16 = Z_to_bv 64 (zlength buf - Z.of_nat i)
                   /\ w24 = Z_to_bv 64 S /\ w32 = Z_to_bv 64 (zlength s) /\ (i <= length buf)%nat
       else w24 = Z_to_bv 64 (S + Z.of_nat i) /\ w32 = Z_to_bv 64 (zlength s - Z.of_nat i) /\ (i <= length s)%nat /\ S + Z.of_nat i < 2^64) ->
      (if siteA then x3 = Z_to_bv 64 (bv_unsigned sp + (if two then -104 else -88))
       else x4 = Z_to_bv 64 (bv_unsigned sp + (if two then -104 else -88))) ->
      bytes_at bsegs m B (to_bytes buf) ->
      boxed (bytes_at bsegs m0 S (to_bytes s)) ->
      munch [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
      stk bsegs m lo (bv_unsigned sp + -112) -> (lo <= bv_unsigned sp + -112) -> (0x603000 <= lo) -> (bv_unsigned sp <= 0x800000000000) ->
      rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells bsegs m ssp_guard [C8 canary] ->
      (fd = 1 \/ fd = 2) ->
      (0 <= Fp) -> (Fp + 232 <= lo) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (0 <= B) -> (0 <= bufsize) -> (zlength buf <= bufsize) -> (B + bufsize <= 0x800000000000) ->
      (zlength buf + zlength s <= WRITEV_MAX) -> (0 <= S < 2^64) -> (S + zlength s <= 0x800000000000) ->
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S))) ->
      (B + zlength buf <= lo \/ bv_unsigned sp <= B) ->
      (forall (k : Z) (ra2 : word) (ms' : machine_state),
          adv_post two i k ra2 gp tp t0 t1 t2 a6 t3 t4 t5 t6 ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0
                   Fp flags wend B bufsize wfn fd mode lbf tail buf s S lo canary j0 ms' ->
          implMA bsegs P (KONT k) st
            (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
                              (zlength s) lo canary m0 st) ms') ->
      implMA bsegs P
        (k <- msys (NWritev fd (map to_bytes (loop_iovs buf s two i))) (dec_writev (zlength (zconcat (loop_iovs buf s two i)))) ;;
         if k =? zlength (zconcat (loop_iovs buf s two i)) then mret tt else KONT k) st
        (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
                          (zlength s) lo canary m0 st)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
                 (Z_to_bv 64 fd) (Z_to_bv 64 (bv_unsigned sp + (if two then -104 else -88))) (Z_to_bv 64 (loop_cnt two))
                 a3 a4 a5 a6 (Z_to_bv 64 66) (Z_to_bv 64 (loop_cnt two)) x3 x4
                 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 (loop_rem buf s two i)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (if siteA then SITE_A else SITE_B)) fc None m (seg_rom bsegs)).
  Proof.
    intros until P. intros PSTK PIMG PFILE PBUF PSRC FC FR FOK SITE BUFB SRC MU WM MI ST LO GLO SPHI GOT GUARD FD Fp0 FPLO FSEP1 FSEP2 B0 BS0 BUFLE BShi
           LENS S0 Shi SEPS SEPB HK.
    assert (ILE : (i <= (if two then length buf else length s))%nat)
      by (destruct two; [destruct FOK as (_&_&_&_&H)|destruct FOK as (_&_&H&_)]; exact H).
    rewrite !zconcat_loop_iovs by exact ILE.
    pose proof (bytes_at_bound _ _ _ _ BUFB) as BB. rewrite length_to_bytes in BB.
    assert (BSRC : 0 <= S /\ S + Z.of_nat (length s) <= 2^64)
      by (pose proof (bytes_at_bound _ _ _ _ SRC) as X; rewrite length_to_bytes in X; exact X).
    (* [comment removed for export] *)
    assert (SRCm : bytes_at bsegs m S (to_bytes s)).
    { unfold boxed in SRC. destruct SEPS as [-> | [SEP1 SEP2]].
      - apply bytes_at_nil. lia.
      - apply (bytes_at_transport _ _ _ m _ _ SRC MU). cbn [disjoint_from]. rewrite length_to_bytes. unfold zlength in *. lia. }
    assert (REM0 : 0 <= loop_rem buf s two i) by (unfold loop_rem, zlength; destruct two; cbn in ILE; lia).
    assert (REMhi : loop_rem buf s two i < 2^32) by (unfold loop_rem, WRITEV_MAX, zlength in *; destruct two; cbn in ILE; lia).
    apply implMA_sysk.
    unfold SITE_A, SITE_B. unfold file_cells in FC.
    (* [comment removed for export] *)
    destruct siteA; [subst x3| subst x4]; step_ecallA; split.
    1,3: split; [ eapply (at_node_writev_loop _ fd buf s two i B S (bv_unsigned sp + -112)); try reflexivity; try eassumption;
                  first [unfold zlength in *; lia | destruct two; cbn -[Z.add]; lia]
                | eapply (node_policy_writev_loop _ fd buf s two i B S (bv_unsigned sp + -112)); try reflexivity; try eassumption;
                  first [intros; apply PSTK; lia | intros; apply PBUF; unfold zlength in *; lia | unfold zlength, WRITEV_MAX in *; lia | destruct two; cbn -[Z.add]; lia] ].
    all: intros rsp k Hdec; unfold dec_writev in Hdec; apply dec_count_Some in Hdec as (-> & Hk0 & Hk1 & Hk64).
    all: rewrite Z.max_l in Hk0 by exact REM0.
    1: destruct (Z.eqb_spec k (loop_rem buf s two i)) as [EQ|NE];
         [apply implMA_ret | eapply implMA_evtA; [| intros ms' Hadv; exact (HK k (Z_to_bv 64 0x98144) ms' Hadv)]].
    3: destruct (Z.eqb_spec k (loop_rem buf s two i)) as [EQ|NE];
         [apply implMA_ret | eapply implMA_evtA; [| intros ms' Hadv; exact (HK k (Z_to_bv 64 0x981cc) ms' Hadv)]].
    (* [comment removed for export] *)
    all: unfold eff0; sys_nret.
    all: do 4 step.
    all: if_cases Hc; zify_cond Hc; [| exfalso; rewrite ?land_W64_small in Hc by lia; lia].
    all: step.
    1,2: replace (ret_pc (Z_to_bv 64 0x98144)) with (Z_to_bv 64 0x98144 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    3,4: replace (ret_pc (Z_to_bv 64 0x981cc)) with (Z_to_bv 64 0x981cc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    3,4: step.
    all: step; if_cases Hx; zify_cond Hx; rewrite ?land_W64_small in Hx by lia; try (exfalso; lia).
    all: lazymatch goal with
         | |- evtA _ _ _ (MS _ _ (Z_to_bv 64 0x981d4) _ _ _ _) =>
             eapply stdio_write_advance; try eassumption; unfold zlength in *; try lia
         | |- _ => eapply stdio_write_exit; try eassumption; unfold zlength in *; try lia
         end.
    all: unfold WRITEV_MAX in LENS; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma stdio_write_loop :
    forall (fuel : nat) (two siteA : bool) (i : nat)
           (ra' gp tp t0 t1 t2 a3 a4 a5 a6 x3 x4 t3 t4 t5 t6 : word)
           (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (m0 m : mem) (st : St)
           (Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
           (buf s : list Z) (S lo : Z) (canary : word) (j0 : list byte) (w8 w16 w24 w32 : word) (P : acc -> Prop),
      (forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
      (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
      (forall a k, Fp <= a -> a + Z.of_nat k <= Fp + 232 -> P (Z_to_bv 64 a, k)) ->
      (forall a k, B <= a -> a + Z.of_nat k <= B + bufsize -> P (Z_to_bv 64 a, k)) ->
      (forall a k, S <= a -> a + Z.of_nat k <= S + zlength s -> P (Z_to_bv 64 a, k)) ->
      rw_cells bsegs m Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
      rw_cells bsegs m (bv_unsigned sp + -112)
        [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 canary; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      (if two then w8 = Z_to_bv 64 (B + Z.of_nat i) /\ w16 = Z_to_bv 64 (zlength buf - Z.of_nat i)
                   /\ w24 = Z_to_bv 64 S /\ w32 = Z_to_bv 64 (zlength s) /\ (i <= length buf)%nat
       else w24 = Z_to_bv 64 (S + Z.of_nat i) /\ w32 = Z_to_bv 64 (zlength s - Z.of_nat i) /\ (i <= length s)%nat /\ S + Z.of_nat i < 2^64) ->
      (if siteA then x3 = Z_to_bv 64 (bv_unsigned sp + (if two then -104 else -88))
       else x4 = Z_to_bv 64 (bv_unsigned sp + (if two then -104 else -88))) ->
      bytes_at bsegs m B (to_bytes buf) ->
      boxed (bytes_at bsegs m0 S (to_bytes s)) ->
      munch [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
      stk bsegs m lo (bv_unsigned sp + -112) -> (lo <= bv_unsigned sp + -112) -> (0x603000 <= lo) -> (bv_unsigned sp <= 0x800000000000) ->
      rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells bsegs m ssp_guard [C8 canary] ->
      (fd = 1 \/ fd = 2) ->
      (0 <= Fp) -> (Fp + 232 <= lo) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (0 <= B) -> (0 <= bufsize) -> (zlength buf <= bufsize) -> (B + bufsize <= 0x800000000000) ->
      (zlength buf + zlength s <= WRITEV_MAX) -> (0 <= S < 2^64) -> (S + zlength s <= 0x800000000000) ->
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S))) ->
      (B + zlength buf <= lo \/ bv_unsigned sp <= B) ->
      implMA bsegs P (writev_loop fuel fd (loop_iovs buf s two i)) st
        (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
                          (zlength s) lo canary m0 st)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
                 (Z_to_bv 64 fd) (Z_to_bv 64 (bv_unsigned sp + (if two then -104 else -88))) (Z_to_bv 64 (loop_cnt two))
                 a3 a4 a5 a6 (Z_to_bv 64 66) (Z_to_bv 64 (loop_cnt two)) x3 x4
                 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 (loop_rem buf s two i)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (if siteA then SITE_A else SITE_B)) fc None m (seg_rom bsegs)).
  Proof.
    induction fuel as [|fuel IH]; intros; rewrite writev_loop_unfold;
      (eapply stdio_write_round; [eassumption .. | ]);
      intros k ra2 ms' (two' & i' & a3' & a4' & a5' & w8' & w16' & w24' & w32' & m' & E & -> & FC' & FR' & FOK' & BUFB' & MU' & WM' & MI' & ST' & GOT' & GUARD').
    - apply implMA_unr.
    - rewrite E. eapply (IH two' false i'); try eassumption; try reflexivity; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma stdio_write_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
           (buf s : list Z) (S lo : Z) (canary : word) (P : acc -> Prop),
      (forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
      (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
      (forall a k, Fp <= a -> a + Z.of_nat k <= Fp + 232 -> P (Z_to_bv 64 a, k)) ->
      (forall a k, B <= a -> a + Z.of_nat k <= B + bufsize -> P (Z_to_bv 64 a, k)) ->
      (forall a k, S <= a -> a + Z.of_nat k <= S + zlength s -> P (Z_to_bv 64 a, k)) ->
      rw_cells bsegs m Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
      bytes_at bsegs m B (to_bytes buf) ->
      bytes_at bsegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      (fd = 1 \/ fd = 2) ->
      stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - STDIO_WRITE_DEPTH) -> (0x603000 <= lo) ->
      (bv_unsigned sp < 0x800000000000) (* [comment removed for export] *) ->
      ssp_cells m canary -> mem_inv bsegs m ->
      (0 <= Fp) -> (Fp + 232 <= lo) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (0 <= B) -> (0 <= bufsize) -> (zlength buf <= bufsize) -> (B + bufsize <= 0x800000000000) ->
      (zlength buf + zlength s < 2^62) (* [comment removed for export] *) ->
      (0 <= S < 2^64) -> (S + zlength s <= 0x800000000000) ->
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S))) ->
      (B + zlength buf <= lo \/ bv_unsigned sp <= B) ->
      implMA bsegs P (stdio_writev (St:=St) fd buf s) st
            (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
                              (zlength s) lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x980b4) fc None m (seg_rom bsegs)).
  Proof.
    intros until P. intros PSTK PIMG PFILE PBUF PSRC FC BUFB SRC -> -> -> FD ST LO GLO SPTS SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BS0 BUFLE BShi LENS0 S0 Shi SEPS SEPB.
    unfold stdio_writev. destruct (Z.ltb_spec WRITEV_MAX (zlength buf + zlength s)) as [|LENS]; [apply implMA_unr|].
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, STDIO_WRITE_DEPTH, WRITEV_MAX in *.
    unfold zlength in *.
    assert (LSB : length (to_bytes s) = length s) by apply length_to_bytes.
    change (bytes_at bsegs m S (to_bytes s)) with (boxed (bytes_at bsegs m S (to_bytes s))) in SRC.
    assert (LBB : length (to_bytes buf) = length buf) by apply length_to_bytes.
    pose proof (bytes_at_bound _ _ _ _ BUFB) as BB. rewrite LBB in BB.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    (* [comment removed for export] *)
    apply implMA_from_evtA.
    unfold file_cells in FC.
    carve_frame 112%nat ST.
    do 12 step. do 13 step.
    rewrite !unsigned_lit by lia.
    destruct buf as [|b0 buf'].
    - (* [comment removed for export] *)
      change (Z.of_nat (@length Z [])) with 0 in *. rewrite !Z.add_0_r in *. rewrite Z.lxor_nilpotent.
      change (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word).
      step. if_true. do 6 step.
      replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd : word) by (symmetry; apply sx32_small; lia).
      replace (Z_to_bv 64 (B - B + Z.of_nat (length s)) : word) with (Z_to_bv 64 (loop_rem [] s false 0) : word)
        by (unfold loop_rem, zlength; cbn [length Z.of_nat]; f_equal; lia).
      apply evtA_done. change (iovs_init [] s) with (loop_iovs [] s false 0).
      eapply (stdio_write_loop (length (@nil Z) + length s) false true 0); try eassumption; try reflexivity;
        try (cbn [length Z.of_nat]; unfold zlength; lia).
      { change (B + zlength (@nil Z)) with (B + 0). rewrite Z.add_0_r. exact FC. }
      { unfold zlength. repeat split; try (f_equal; lia); lia. }
      { unfold zlength. cbn [length Z.of_nat]. lia. }
    - (* [comment removed for export] *)
      set (nb := Z.of_nat (length (b0 :: buf'))) in *.
      assert (NB1 : 1 <= nb) by (subst nb; cbn [length]; lia).
      replace (Z.lxor (B + nb) B) with (Z.lxor (B + nb) (B + 0)) by (rewrite Z.add_0_r; reflexivity).
      assert (XNZ : Z.lxor (B + nb) (B + 0) <> 0) by (intros E; apply Z.lxor_eq in E; lia).
      replace (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.lxor (B + nb) (B + 0)))) with (Z_to_bv 64 1 : word).
      2:{ pose proof (Z_lxor_range (B + nb) (B + 0) ltac:(lia) ltac:(lia)) as XR.
          unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
          destruct (Z.ltb_spec0 0 (Z.lxor (B + nb) (B + 0))); [reflexivity| exfalso; lia]. }
      step. if_cases Hb; zify_cond Hb. 1:{ exfalso. lia. } do 7 step.
      replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd : word) by (symmetry; apply sx32_small; lia).
      replace (Z_to_bv 64 (B + nb - B + Z.of_nat (length s)) : word) with (Z_to_bv 64 (loop_rem (b0 :: buf') s true 0) : word)
        by (unfold loop_rem, zlength; subst nb; f_equal; lia).
      apply evtA_done. change (iovs_init (b0 :: buf') s) with (loop_iovs (b0 :: buf') s true 0).
      eapply (stdio_write_loop (length (b0 :: buf') + length s) true true 0); try eassumption; try reflexivity;
        try (subst nb; unfold zlength; lia).
      { subst nb. unfold zlength. repeat split; try lia; f_equal; rewrite ?unsigned_lit by lia; lia. }
  Qed.
End StdioWrite.
End RC__3.
