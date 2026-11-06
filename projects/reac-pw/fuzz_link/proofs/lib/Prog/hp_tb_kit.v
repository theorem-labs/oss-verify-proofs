(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/check_no_overread.v, with its module paths, module names, addresses and numbers changed; 599 of its 725 lines of code are new or changed and 726 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_egress/lib/Prog/check_restamp.v; 174 of its 229 lines of code are new or changed and 670 lines of the source are left out. *)
(* reac-pw/fuzz_link, PLAIN build: kit lemmas of the text_buf walk (lane hp, clone a Theorem Labs lane).
   Adapted from libreac/fuzz_pcap lib/Prog/KindB.v (origin/ossv/recipes 4b6f0df50aa): the generic
   memory, register and allocator-law facts the released SR walks use. Names carry the prefix `tb_`.
   The image bounds tb_rsegs_top / tb_rsegs_res_top are checked by computation on link's plain
   image (Img0.rsegs; its last LOAD segment ends at 0x960e0). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0 MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YK14 YP09 YO0i YO0f YO0d YM05.
Import ListNotations.
Local Open Scope Z_scope.

Lemma tb_bytes_at_transfer : forall segs m m' a bs, bytes_at segs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs m' (a + i) = mbyte segs m (a + i)) ->
  bytes_at segs m' a bs.
Proof.
  intros segs m m' a bs (H1 & H2 & H) E. split; [exact H1|]. split; [exact H2|].
  intros i Hi. change (mbyte segs m' (a + Z.of_nat i) = nth_error bs i).
  rewrite E by lia. exact (H i Hi).
Qed.

Lemma tb_rw_cells_transfer : forall segs m m' a cs, rw_cells segs m a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> mbyte segs m' (a + i) = mbyte segs m (a + i) /\
     (writable_at segs m (a + i) -> writable_at segs m' (a + i))) ->
  rw_cells segs m' a cs.
Proof.
  intros segs m m' a cs [[Hwf Hb] (Ha & Hn & Hw)] E.
  pose proof (cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hwf|]|].
  - apply (tb_bytes_at_transfer segs m); [exact Hb|]. intros i Hi. apply E. rewrite <- L. exact Hi.
  - split; [exact Ha|]. split; [exact Hn|]. intros i Hi. apply (proj2 (E i Hi)). exact (Hw i Hi).
Qed.

(* the same bytes, cut into other cells *)
Lemma tb_rw_cells_recell : forall segs m a cs cs', rw_cells segs m a cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> rw_cells segs m a cs'.
Proof.
  intros segs m a cs cs' [[Hwf Hb] Hw] Hwf' E.
  split; [split; [exact Hwf' | rewrite E; exact Hb]|].
  rewrite <- (cells_bytes_length cs' Hwf'), E, (cells_bytes_length cs Hwf). exact Hw.
Qed.

(* cap+1 bytes of one value are cap bytes of it and one more *)
Lemma tb_tbuf_split : forall segs m h cap (x : byte), 0 <= cap ->
  rw_cells segs m h [CB (Z.to_nat (cap + 1)) (repeat x (Z.to_nat (cap + 1)))] ->
  rw_cells segs m h [CB (Z.to_nat cap) (repeat x (Z.to_nat cap)); C1 x].
Proof.
  intros segs m h cap x Hc H. apply (tb_rw_cells_recell segs m h _ _ H).
  - cbn [cells_wf cell_wf]. split; [apply repeat_length | tauto].
  - cbn [cells_bytes cbytes]. rewrite !app_nil_r.
    replace (Z.to_nat (cap + 1)) with (Z.to_nat cap + 1)%nat by lia.
    rewrite repeat_app. reflexivity.
Qed.

Lemma tb_nth_error_seq_lt : forall s k i, (i < k)%nat -> nth_error (seq s k) i = Some (s + i)%nat.
Proof.
  intros s k. revert s. induction k as [|k IH]; intros s i Hi; [lia|].
  destruct i as [|i]; cbn; [f_equal; lia|]. rewrite IH by lia. f_equal. lia.
Qed.

Lemma tb_present_rw_cells : forall segs m a (k : nat), 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> present m (a + i)) ->
  exists junk, rw_cells segs m a [CB k junk].
Proof.
  intros segs m a k Ha Hk H.
  exists (map (fun i => match m (wa (a + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 k)).
  assert (L : length (map (fun i => match m (wa (a + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end)
                         (seq 0 k)) = k) by (rewrite length_map, length_seq; reflexivity).
  split; [split|].
  - cbn. split; [exact L | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [exact Ha|]. split; [rewrite L; exact Hk|].
    intros i Hi. rewrite L in Hi.
    destruct (H (Z.of_nat i) ltac:(lia)) as [b E].
    rewrite (map_nth_error _ _ _ (tb_nth_error_seq_lt 0 k i Hi)). cbn [Nat.add].
    unfold mrd. unfold wa. rewrite E. reflexivity.
  - split; [exact Ha|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    destruct (H i ltac:(lia)) as [b E]. unfold wview, wa. rewrite E. discriminate.
Qed.

Lemma tb_ms_rel_MS : forall segs s R F pc fc rv m0 ro, ms_rel segs s (MS R F pc fc rv m0 ro) ->
  s = MS R F pc fc rv (ms_mem s) ro /\ mem_rel segs (ms_mem s) m0.
Proof.
  intros segs [r f p sv rv' c mm o] R F pc fc rv m0 ro (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  cbn in *. subst. split; [reflexivity | exact H8].
Qed.

Lemma tb_rw_cells_of_rel : forall segs m m0 A cs, mem_rel segs m m0 -> rw_cells segs m0 A cs -> rw_cells segs m A cs.
Proof.
  intros segs m m0 A cs HR [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - exact (proj2 (bytes_at_rel segs m m0 A _ HR) Hb).
  - exact (wr_at_rel segs m m0 A _ HR Hw).
Qed.

Lemma tb_rw_cells_normalize : forall segs m A cs, ro_agree segs m -> rw_cells segs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ro_addr segs (Z_to_bv 64 (A + i)) = false) ->
  rw_cells segs (normalize segs m) A cs.
Proof.
  intros segs m A cs RO [[Hwf Hb] Hw] Hro. split; [split; [exact Hwf|]|].
  - exact (bytes_at_normalize segs m A _ RO Hb).
  - exact (wr_at_norm segs m (normalize segs m) A _ (mem_rel_normalize segs m RO) Hw Hro).
Qed.

Lemma tb_find_segment_none_above : forall segs top a n,
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs = true -> top <= a -> 0 < n ->
  find_segment segs a n = None.
Proof.
  induction segs as [|s segs IH]; intros top a n H Ha Hn; cbn [find_segment]; [reflexivity|].
  cbn [forallb] in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
  match goal with |- context [if ?c then _ else _] => destruct c eqn:E end.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - apply IH with top; assumption.
Qed.

Lemma tb_find_segment_in : forall segs a n seg, find_segment segs a n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|s segs IH]; intros a n seg H; cbn [find_segment] in H; [discriminate|].
  match type of H with context [if ?c then _ else _] => destruct c eqn:E end.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity|]. lia.
  - destruct (IH a n seg H) as (Hi & H1 & H2). split; [right; exact Hi|]. lia.
Qed.

Lemma tb_rsegs_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 2 ^ 20) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tb_rsegs_res_top :
  forallb (fun s => bv_unsigned (fst s) + bv_unsigned (snd s) <=? 2 ^ 21) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tb_writable_hi_present : forall m a, 2 ^ 20 <= a < 2 ^ 64 -> writable_at rsegs m a -> present m a.
Proof.
  intros m a Ha. unfold writable_at, wview, present.
  destruct (m (Z_to_bv 64 a)) as [b|]; [intros _; exists b; reflexivity|].
  rewrite unsigned_lit by lia.
  rewrite (tb_find_segment_none_above rsegs (2 ^ 20) a 1 tb_rsegs_top) by lia.
  intros W. exfalso. apply W. reflexivity.
Qed.

Lemma tb_ro_addr_hi : forall a, 2 ^ 20 <= a < 2 ^ 64 -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. unfold ro_addr. rewrite unsigned_lit by lia.
  rewrite (tb_find_segment_none_above rsegs (2 ^ 20) a 1 tb_rsegs_top) by lia. reflexivity.
Qed.

Lemma tb_stk_normalize : forall m lo hi, stk rsegs m lo hi -> 2 ^ 20 <= lo -> stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi (H1 & H2 & H) Hlo. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  assert (N : normalize rsegs m (wa a) = m (wa a)) by (unfold normalize, wa; rewrite tb_ro_addr_hi by lia; reflexivity).
  destruct (H a Ha) as [W [b E]]. split.
  - unfold wview in *. rewrite N. exact W.
  - exists b. unfold mrd in *. rewrite N. exact E.
Qed.

Section Img.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Hypothesis SEGS : ms_segs B = rsegs.

Lemma tb_in_img_of_seg : forall a seg, 0 <= a -> find_segment rsegs a 1 = Some seg -> in_img B a.
Proof using SEGS.
  intros a seg Ha F. destruct (tb_find_segment_in _ _ _ _ F) as (Hin & H1 & H2).
  pose proof (proj1 (forallb_forall _ rsegs) tb_rsegs_top seg Hin) as T. apply Z.leb_le in T.
  unfold in_img. rewrite SEGS. split; [intro E; rewrite E in Hin; destruct Hin|].
  exists (segment_reservation seg). split; [apply in_map; exact Hin|].
  unfold segment_reservation, page_round_down_Z, page_round_up_Z. cbn [fst snd].
  change page_size with 4096.
  pose proof (N2Z.is_nonneg (seg_base seg)) as P1. pose proof (N2Z.is_nonneg (seg_size seg)) as P2.
  set (bs := Z.of_N (seg_base seg)) in *. set (sz := Z.of_N (seg_size seg)) in *.
  pose proof (Z.mul_div_le bs 4096 ltac:(lia)) as D1.
  pose proof (Z.div_pos bs 4096 ltac:(lia) ltac:(lia)) as D2.
  pose proof (Z.mul_div_le (bs + sz + 4096 - 1) 4096 ltac:(lia)) as D3.
  pose proof (Z.mul_succ_div_gt (bs + sz + 4096 - 1) 4096 ltac:(lia)) as D4.
  rewrite !unsigned_lit by lia. lia.
Qed.

Lemma tb_present_of_writable_out : forall m a, 0 <= a < 2 ^ 64 -> ~ in_img B a -> writable_at rsegs m a ->
  present m a.
Proof using SEGS.
  intros m a Ha NI. unfold writable_at, wview, present.
  destruct (m (Z_to_bv 64 a)) as [b|]; [intros _; exists b; reflexivity|].
  rewrite unsigned_lit by lia.
  destruct (find_segment rsegs a 1) as [seg|] eqn:F.
  - exfalso. apply NI. eapply tb_in_img_of_seg; [lia | exact F].
  - intros W. exfalso. apply W. reflexivity.
Qed.

Lemma tb_ro_addr_out : forall a, 0 <= a < 2 ^ 64 -> ~ in_img B a -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof using SEGS.
  intros a Ha NI. unfold ro_addr. rewrite unsigned_lit by lia.
  destruct (find_segment rsegs a 1) as [seg|] eqn:F; [|reflexivity].
  exfalso. apply NI. eapply tb_in_img_of_seg; [lia | exact F].
Qed.

End Img.

Lemma tb_pairwise_app_mid : forall {X} (R : X -> X -> Prop) b1 x b2 y,
  pairwise R (b1 ++ x :: b2) -> In y (b1 ++ b2) -> R x y \/ R y x.
Proof.
  intros X R b1. induction b1 as [|z b1 IH]; intros x b2 y HP Hin; cbn in *.
  - left. apply (proj1 HP). exact Hin.
  - destruct HP as [H1 H2]. destruct Hin as [<-|Hin].
    + right. apply H1. apply in_or_app. right. left. reflexivity.
    + exact (IH x b2 y H2 Hin).
Qed.

Section Laws.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.

Lemma tb_block_facts : forall L A mem md q k i, MR L A mem md -> In (q, k) (blocks L A) -> 0 <= i < k ->
  present mem (q + i) /\ 4096 <= q /\ q + k <= alloc_ceiling /\ ~ owned B L A (q + i).
Proof using LAWS.
  intros L A mem md q k i HM Hin Hi. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp).
  cbn in E. injection E as <- <-. exact (mr_blocks B MR LAWS L A mem md p k' i HM Hp Hi).
Qed.

Lemma tb_blocks_mid_disjoint : forall L A mem md b1 b2 d n q k, MR L A mem md ->
  blocks L A = b1 ++ (d, n) :: b2 -> In (q, k) (b1 ++ b2) -> q + k <= d \/ d + n <= q.
Proof using LAWS.
  intros L A mem md b1 b2 d n q k HM E Hin.
  pose proof (mr_blocks_disjoint B MR LAWS L A mem md HM) as P. rewrite E in P.
  destruct (tb_pairwise_app_mid _ _ _ _ _ P Hin) as [D|D]; unfold ranges_disjoint in D; cbn in D; lia.
Qed.

End Laws.

Section Regs.
Context {fx : YK11.FPState}.

Lemma tb_canon_mkst : forall regs pc mem rom,
  RegisterBridge.canonical_register_state (mkst regs pc mem rom) = MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem rom.
Proof. reflexivity. Qed.

Lemma tb_eqv_mkst : forall R F pc fc m ro ms, Regs6ss.ms_eqv (MS R F pc fc None m ro) ms -> F = fp_regs -> fc = fp_csr ->
  exists R', ms = mkst R' pc m ro /\ Regs6ss.xregs_eqv R R'.
Proof.
  intros R F pc fc m ro [r f p sv rv c mm o] (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) -> ->.
  cbn in *. subst. exists r. split; [reflexivity | exact H1].
Qed.

Lemma tb_getr_of_eqv : forall M R (r : bv 5), Regs6ss.xregs_eqv M R -> bv_eqb r 0 = false -> getr R r = reg_get M r.
Proof. intros M R r H NZ. unfold getr. rewrite NZ. symmetry. apply H. exact NZ. Qed.

Lemma tb_preserved_chain : forall (own : Z -> bool) regs R1 R2 R3 M1 M3,
  Regs6ss.xregs_eqv M1 R1 -> regs_preserved R1 R2 -> Regs6ss.xregs_eqv M3 R3 ->
  (forall r, callee_saved r -> own r = false ->
     reg_get M3 (Z_to_bv 5 r) = reg_get R2 (Z_to_bv 5 r) /\ reg_get M1 (Z_to_bv 5 r) = reg_get regs (Z_to_bv 5 r)) ->
  (forall r, callee_saved r -> own r = true -> reg_get M3 (Z_to_bv 5 r) = reg_get regs (Z_to_bv 5 r)) ->
  regs_preserved regs R3.
Proof.
  intros own regs R1 R2 R3 M1 M3 X1 P X3 K1 K2 r Hr.
  assert (Hk : 0 < r < 32) by (unfold callee_saved in Hr; lia).
  assert (NZ : bv_eqb (Z_to_bv 5 r) 0 = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. change (bv_unsigned 0) with 0. lia. }
  rewrite (tb_getr_of_eqv _ _ _ X3 NZ). unfold getr. rewrite NZ.
  destruct (own r) eqn:O; [exact (K2 r Hr O)|].
  destruct (K1 r Hr O) as [E1 E2]. rewrite E1, <- E2.
  pose proof (P r Hr) as E3. unfold getr in E3. rewrite NZ in E3. rewrite E3. symmetry. apply X1. exact NZ.
Qed.

End Regs.
