From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct PjSame memcpy_c memset_c same_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import LedgerCells fuzz_alloc_ran_out_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* The straight-line runs of check_no_overread in the plain build of #102 (symbol check_no_overread FUNC LOCAL 0x13778
   size 652 in pau-preset-102/omx-clap-core/unstripped/fuzz_preset/fuzz_preset.plain, sha256 c8f4d6b8e567b0b1, the
   unstripped twin of the pinned 805604bb).  Every pc, stack offset and callee entry below is read from that listing:
     default_malloc 0x178d8, memcpy 0x21a68, memset 0x21e6c, fuzz_alloc_ran_out 0x158cc, parse_noting 0x13a04,
     same 0x1428c, pj_free 0x15c08, free 0x17798; frame 0xf0 = 240, saved s7..s0, ra at sp + 0xa8 .. sp + 0xe8;
     trees at sp + 0x70, sp + 0x38, sp; s7 = 0x347b8 after the auipc at 0x137b8, so s7 - 0x18 = GL_OWN_RAN_OUT
     (g_own_ran_out, one byte).
   The three copies are fuzz_preset.c's padded (#102 lines 509-521) inlined: malloc (n + 16), and when the block is
   not NULL a memcpy (when n <> 0) and a 16-byte memset of the fill.  malloc's contract gives a non-NULL block, so
   every `beqz a0` to the NULL arm (which stores 1 into g_own_ran_out) is not taken. *)

Ltac br_lits := unfold_cond; rewrite ?unsigned_lit by lia.

Ltac fin_post :=
  lazymatch goal with |- ?P ?ms => try unfold P end;
  hnf;
  hot_eexists_all;
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ reflexivity | ]
  | |- _ = _ => reflexivity
  end;
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.AndN.and_splits;
  try assumption.

Lemma cno_rw_cut : forall m A (n k : Z) junk, 0 <= n -> 0 <= k ->
  rw_cells rsegs m A [CB (Z.to_nat (n + k)) junk] ->
  rw_cells rsegs m A [CB (Z.to_nat n) (firstn (Z.to_nat n) junk)] /\
  rw_cells rsegs m (A + n) [CB (Z.to_nat k) (skipn (Z.to_nat n) junk)].
Proof.
  intros m A n k junk Hn Hk [[Hwf Hb] Hw].
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  destruct Hw as (W1 & W2 & W). cbn [cells_size csize] in W1, W2, W.
  rewrite <- (firstn_skipn (Z.to_nat n) junk) in Hb.
  apply (proj1 (bytes_at_app rsegs _ _ _ _)) in Hb. destruct Hb as [B1 B2].
  rewrite length_firstn in B2. replace (Nat.min (Z.to_nat n) (length junk)) with (Z.to_nat n) in B2 by lia.
  rewrite Z2Nat.id in B2 by lia.
  split; split; [split| |split|].
  - cbn [cells_wf cell_wf]. split; [rewrite length_firstn; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B1.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. apply W. lia.
  - cbn [cells_wf cell_wf]. split; [rewrite length_skipn; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B2.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + n + i) with (A + (n + i)) by lia. apply W. lia.
Qed.

Lemma cno_rw_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

Lemma cno_join : forall m q n x fill, length x = Z.to_nat n -> 0 <= n -> 0 <= fill < 256 ->
  bytes_at rsegs m q x ->
  rw_cells rsegs m (q + n) [CB (Z.to_nat 16) (repeat (Z_to_bv 8 (fill mod 256)) (Z.to_nat 16))] ->
  bytes_at rsegs m q (x ++ repeat (Z_to_bv 8 fill) 16).
Proof.
  intros m q n x fill SL Hn Hf B R. apply (proj2 (bytes_at_app rsegs _ _ _ _)). split; [exact B|].
  rewrite SL, Z2Nat.id by lia. rewrite Z.mod_small in R by lia. exact (cno_rw_bytes _ _ _ _ R).
Qed.

(* One byte cell of value 0 is the le1 of the word 0 (the form of fuzz_alloc_ran_out_contract). *)
Lemma cno_le1_0 : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. unfold le1. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma cno_ro1_bytes : forall m A, ro_cells rsegs m A [C1 (Z_to_bv 8 0)] -> bytes_at rsegs m A (le1 (Z_to_bv 64 0)).
Proof. intros m A [_ H]. cbn [cells_bytes cbytes app] in H. rewrite cno_le1_0. exact H. Qed.

Lemma cno_bytes_ro1 : forall m A, bytes_at rsegs m A (le1 (Z_to_bv 64 0)) -> ro_cells rsegs m A [C1 (Z_to_bv 8 0)].
Proof.
  intros m A H. rewrite cno_le1_0 in H. split; [cbn [cells_wf cell_wf]; tauto|].
  cbn [cells_bytes cbytes app]. exact H.
Qed.

Ltac cno_call_memcpy MC x j :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply MC with (src := x) (junk := j); rewrite ?unsigned_lit by lia; first [eassumption | lia]
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold memcpy_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO;
      post_call rsegs mm ]
  end.

Ltac cno_call_memset MS0 j :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply MS0 with (junk := j); rewrite ?unsigned_lit by lia; eassumption
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold memset_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO;
      post_call rsegs mm ]
  end.

(* The same, with the junk of the target cell found by unification. *)
Ltac cno_call_memset_e MS0 :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply MS0; rewrite ?unsigned_lit by lia; eassumption
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold memset_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO;
      post_call rsegs mm ]
  end.

(* fuzz_alloc_ran_out (0x158cc) through its contract, when g_ran_out (one byte) is 0: a0 = 0, every other register
   and memory kept, back at ra. *)
Ltac cno_call_ranout FAR :=
  eapply evt_cut;
  [ eapply FAR with (ran_out := Z_to_bv 64 0);
    [ rewrite unsigned_lit by lia; lia | apply cno_ro1_bytes; eassumption ]
  | let ms' := fresh "ms'" in let E := fresh "E" in
    intros ms' E; cbv beta in E; subst ms';
    lazymatch goal with
    | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
    end ].

(* 0x13778 .. 0x137b0: addi sp, sp, -0xf0; sd ra, s0..s7 at 0xe8 .. 0xa8; s3 = n, s4 = data, s2 = n + 16;
   a0 = s2; jal default_malloc (0x178d8), ra 0x137b4. *)
Definition seg0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (d n : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x137b4) (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (n + 16))
                  a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (n + 16)) (Z_to_bv 64 n) (Z_to_bv 64 d) s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x178d8) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp + -72, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
    rw_cells rsegs m' (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma cno_seg0 : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (d n : Z) (j : list byte),
  0 <= d < 2 ^ 64 -> 0 <= n <= 2 ^ 28 -> 240 <= bv_unsigned sp ->
  rw_cells rsegs m (bv_unsigned sp + -72) [CB 72 j] ->
  evt rsegs (seg0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m d n)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13778) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d n j
    Hd Hn Hsp FR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp + -72, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  apply (rw_cells_split_CB rsegs _ _ [] 72%nat j [] [8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 15 step.
  finish.
Qed.

Definition copy_post (ra' sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 : word) (pc' : Z)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q d n : Z) (x : list byte) (fill : Z)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 pc') fc None m' (seg_rom rsegs) /\
    munch [(q, q + n + 16)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    bytes_at rsegs m' q (x ++ repeat (Z_to_bv 8 fill) 16) /\ bytes_at rsegs m' d x.

Section Copy.
Hypothesis MC : memcpy_contract.
Hypothesis MS0 : memset_contract.

(* 0x137b4 .. 0x137f4: s0 = a0; auipc s7 (s7 = 0x347b8); beqz a0 (the NULL arm, not taken); memcpy(s0, s4, s3) when
   s3 <> 0; memset(s0 + s3, 0x31, 16); j 0x137f0; a0 = s2; jal default_malloc, ra 0x137f8. *)
Lemma cno_copy1 : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q d n : Z) (x junk : list byte),
  0 < q -> q + n + 16 <= 2 ^ 64 -> 0 <= n -> 0 <= d -> d + n <= 2 ^ 64 ->
  length x = Z.to_nat n -> bytes_at rsegs m d x ->
  rw_cells rsegs m q [CB (Z.to_nat (n + 16)) junk] ->
  (n = 0 \/ d + n <= q \/ q + n + 16 <= d) -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists a1' a2',
               copy_post (Z_to_bv 64 0x137f8) sp gp tp (Z_to_bv 64 q) s1 (Z_to_bv 64 (n + 16)) (Z_to_bv 64 n)
                 (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0x347b8) s8 s9 s10 s11 (Z_to_bv 64 (n + 16)) a1' a2'
                 0x178d8 F fc m q d n x 49 ms')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (n + 16)) (Z_to_bv 64 n) (Z_to_bv 64 d) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x137b4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q d n x junk
    Hq Hqn Hn Hd Hdn SL SRC DST DS MI.
  pose proof (munch_refl [(q, q + n + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (cno_rw_cut m q n 16 junk Hn ltac:(lia) DST) as [D1 D2]. clear DST.
  step. step.
  step. br_lits. if_false.
  step.
  destruct (Z.eq_dec n 0) as [N0|N0].
  - destruct x as [|b x]; [|cbn [length] in SL; lia].
    br_lits. if_true.
    do 4 step.
    cno_call_memset MS0 (skipn (Z.to_nat n) junk).
    do 3 step.
    apply evt_done. hnf. do 2 eexists. fin_post.
    all: first [ apply bytes_at_nil; lia
               | apply (cno_join _ q n); [cbn [length]; lia | lia | lia | apply bytes_at_nil; lia | eassumption] ].
  - br_lits. if_false.
    do 4 step.
    cno_call_memcpy MC x (firstn (Z.to_nat n) junk).
    do 4 step.
    cno_call_memset MS0 (skipn (Z.to_nat n) junk).
    do 3 step.
    apply evt_done. hnf. do 2 eexists. fin_post.
    all: apply (cno_join _ q n); [exact SL | lia | lia | eapply cno_rw_bytes; eassumption | eassumption].
Qed.

(* 0x137f8 .. 0x13834: s1 = a0; beqz a0 (not taken); memcpy(s1, s4, s3) when s3 <> 0; memset(s1 + s3, 0x32, 16);
   j 0x13830; a0 = s2; jal default_malloc, ra 0x13838. *)
Lemma cno_copy2 : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q d n : Z) (x junk : list byte),
  0 < q -> q + n + 16 <= 2 ^ 64 -> 0 <= n -> 0 <= d -> d + n <= 2 ^ 64 ->
  length x = Z.to_nat n -> bytes_at rsegs m d x ->
  rw_cells rsegs m q [CB (Z.to_nat (n + 16)) junk] ->
  (n = 0 \/ d + n <= q \/ q + n + 16 <= d) -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists a1' a2',
               copy_post (Z_to_bv 64 0x13838) sp gp tp s0 (Z_to_bv 64 q) (Z_to_bv 64 (n + 16)) (Z_to_bv 64 n)
                 (Z_to_bv 64 d) s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (n + 16)) a1' a2'
                 0x178d8 F fc m q d n x 50 ms')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (n + 16)) (Z_to_bv 64 n) (Z_to_bv 64 d) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x137f8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q d n x junk
    Hq Hqn Hn Hd Hdn SL SRC DST DS MI.
  pose proof (munch_refl [(q, q + n + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (cno_rw_cut m q n 16 junk Hn ltac:(lia) DST) as [D1 D2]. clear DST.
  step.
  step. br_lits. if_false.
  step.
  destruct (Z.eq_dec n 0) as [N0|N0].
  - destruct x as [|b x]; [|cbn [length] in SL; lia].
    br_lits. if_true.
    do 4 step.
    cno_call_memset MS0 (skipn (Z.to_nat n) junk).
    do 3 step.
    apply evt_done. hnf. do 2 eexists. fin_post.
    all: first [ apply bytes_at_nil; lia
               | apply (cno_join _ q n); [cbn [length]; lia | lia | lia | apply bytes_at_nil; lia | eassumption] ].
  - br_lits. if_false.
    do 4 step.
    cno_call_memcpy MC x (firstn (Z.to_nat n) junk).
    do 4 step.
    cno_call_memset MS0 (skipn (Z.to_nat n) junk).
    do 3 step.
    apply evt_done. hnf. do 2 eexists. fin_post.
    all: apply (cno_join _ q n); [exact SL | lia | lia | eapply cno_rw_bytes; eassumption | eassumption].
Qed.

(* 0x13838 .. 0x13860: s2 = a0; beqz a0 (not taken); memcpy(s2, s4, s3) when s3 <> 0; memset(s2 + s3, 0, 16),
   back at 0x13864. *)
Lemma cno_copy3 : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q d n : Z) (x junk : list byte),
  0 < q -> q + n + 16 <= 2 ^ 64 -> 0 <= n -> 0 <= d -> d + n <= 2 ^ 64 ->
  length x = Z.to_nat n -> bytes_at rsegs m d x ->
  rw_cells rsegs m q [CB (Z.to_nat (n + 16)) junk] ->
  (n = 0 \/ d + n <= q \/ q + n + 16 <= d) -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists a0' a1' a2',
               copy_post (Z_to_bv 64 0x13864) sp gp tp s0 s1 (Z_to_bv 64 q) (Z_to_bv 64 n)
                 (Z_to_bv 64 d) s5 s6 s7 s8 s9 s10 s11 a0' a1' a2' 0x13864 F fc m q d n x 0 ms')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 n) (Z_to_bv 64 d) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13838) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q d n x junk
    Hq Hqn Hn Hd Hdn SL SRC DST DS MI.
  pose proof (munch_refl [(q, q + n + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (cno_rw_cut m q n 16 junk Hn ltac:(lia) DST) as [D1 D2]. clear DST.
  step.
  step. br_lits. if_false.
  step.
  destruct (Z.eq_dec n 0) as [N0|N0].
  - destruct x as [|b x]; [|cbn [length] in SL; lia].
    br_lits. if_true.
    do 4 step.
    cno_call_memset MS0 (skipn (Z.to_nat n) junk).
    apply evt_done. hnf. do 3 eexists. fin_post.
    all: first [ apply bytes_at_nil; lia
               | apply (cno_join _ q n); [cbn [length]; lia | lia | lia | apply bytes_at_nil; lia | eassumption] ].
  - br_lits. if_false.
    do 4 step.
    cno_call_memcpy MC x (firstn (Z.to_nat n) junk).
    do 4 step.
    cno_call_memset MS0 (skipn (Z.to_nat n) junk).
    apply evt_done. hnf. do 3 eexists. fin_post.
    all: apply (cno_join _ q n); [exact SL | lia | lia | eapply cno_rw_bytes; eassumption | eassumption].
Qed.

End Copy.

Definition jump_post (R : bvmap 5 word) (F : bvmap 5 word) (pc' : word) (fc : bv 32) (m : word -> option byte)
    : machine_state -> Prop :=
  fun ms' => ms' = MS R F pc' fc None m (seg_rom rsegs).

(* The run 0x13864 .. 0x138b4 (out_of_memory() before the first reading): s5 = g_own_ran_out (0); the three trees at
   sp + 0x70, sp + 0x38, sp zeroed by memset (struct pj a = empty); s4 = -1 (r1's initial value); bnez s5 and
   bnez fuzz_alloc_ran_out() not taken (both 0); a2 = sp + 0x70, a0 = s0, a1 = s3; jal parse_noting (0x13a04),
   ra 0x138b8. *)
Definition zero_post (sp gp tp s0 s1 s2 s3 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x138b8) sp gp tp t0 t1 t2 s0 s1 s0 s3 (Z_to_bv 64 (bv_unsigned sp + 112)) a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x13a04) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp, bv_unsigned sp + 168)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Section Zero.
Hypothesis MS0 : memset_contract.
Hypothesis FAR : fuzz_alloc_ran_out_contract.

Lemma cno_zero : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (j : list byte),
  bv_unsigned sp + 168 <= 2 ^ 64 -> GL_OWN_RAN_OUT + 1 <= bv_unsigned sp -> G_RAN_OUT + 1 <= bv_unsigned sp ->
  rw_cells rsegs m (bv_unsigned sp) [CB 168 j] -> mem_inv rsegs m ->
  ro_cells rsegs m GL_OWN_RAN_OUT [C1 (Z_to_bv 8 0)] ->
  ro_cells rsegs m G_RAN_OUT [C1 (Z_to_bv 8 0)] ->
  evt rsegs (zero_post sp gp tp s0 s1 s2 s3 s6 (Z_to_bv 64 0x347b8) s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 0x347b8) s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x13864) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m j
    Hsp HOW HGR RW MI OWN GRO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp, bv_unsigned sp + 168)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  change 168%nat with (Z.to_nat (56 + 112)) in RW.
  destruct (cno_rw_cut m (bv_unsigned sp) 56 112 j ltac:(lia) ltac:(lia) RW) as [R1 R23]. clear RW.
  change (Z.to_nat 112) with (Z.to_nat (56 + 56)) in R23.
  destruct (cno_rw_cut m (bv_unsigned sp + 56) 56 56 _ ltac:(lia) ltac:(lia) R23) as [R2 R3]. clear R23.
  replace (bv_unsigned sp + 56 + 56) with (bv_unsigned sp + 112) in R3 by lia.
  unfold GL_OWN_RAN_OUT in OWN, HOW. unfold G_RAN_OUT in GRO, HGR.
  step.
  do 4 step.
  cno_call_memset_e MS0.
  do 4 step.
  cno_call_memset_e MS0.
  do 4 step.
  cno_call_memset_e MS0.
  step.
  step. br_lits. if_false.
  step.
  cno_call_ranout FAR.
  step. br_lits. if_false.
  do 4 step.
  finish.
Qed.

End Zero.

Section Guards.
Hypothesis FAR : fuzz_alloc_ran_out_contract.

(* 0x138b8 .. 0x13924, after the first reading: s4 = a0 (r1); j 0x138fc; a0 = g_own_ran_out (0); s5 = 1; bnez a0 not
   taken; fuzz_alloc_ran_out (0x158cc) returns 0, beqz a0 taken to 0x13918; a2 = sp + 0x38, a0 = s1, a1 = s3;
   jal parse_noting, ra 0x13928. *)
Lemma cno_guard1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  bv_unsigned sp + 56 < 2 ^ 64 ->
  ro_cells rsegs m GL_OWN_RAN_OUT [C1 (Z_to_bv 8 0)] -> ro_cells rsegs m G_RAN_OUT [C1 (Z_to_bv 8 0)] ->
  evt rsegs (jump_post (mkR (Z_to_bv 64 0x13928) sp gp tp t0 t1 t2 s0 s1 s1 s3 (Z_to_bv 64 (bv_unsigned sp + 56))
                           a3 a4 a5 a6 a7 s2 s3 a0 (Z_to_bv 64 1) s6 (Z_to_bv 64 0x347b8) s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x13a04) fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 0x347b8) s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x138b8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hsp OWN GRO.
  unfold GL_OWN_RAN_OUT in OWN. unfold G_RAN_OUT in GRO.
  do 4 step.
  step. br_lits. if_false.
  step.
  cno_call_ranout FAR.
  step. br_lits. if_true.
  do 4 step.
  apply evt_done. unfold jump_post. reflexivity.
Qed.

(* 0x13928 .. 0x13950, after the second reading: s6 = a0 (r2); a0 = g_own_ran_out (0); bnez a0 not taken;
   fuzz_alloc_ran_out returns 0, beqz a0 taken to 0x13944; a2 = sp, a0 = s2, a1 = s3; jal parse_noting, ra 0x13954. *)
Lemma cno_guard2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  ro_cells rsegs m GL_OWN_RAN_OUT [C1 (Z_to_bv 8 0)] -> ro_cells rsegs m G_RAN_OUT [C1 (Z_to_bv 8 0)] ->
  evt rsegs (jump_post (mkR (Z_to_bv 64 0x13954) sp gp tp t0 t1 t2 s0 s1 s2 s3 sp
                           a3 a4 a5 a6 a7 s2 s3 s4 s5 a0 (Z_to_bv 64 0x347b8) s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x13a04) fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 0x347b8) s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x13928) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m OWN GRO.
  unfold GL_OWN_RAN_OUT in OWN. unfold G_RAN_OUT in GRO.
  do 2 step.
  step. br_lits. if_false.
  step.
  cno_call_ranout FAR.
  step. br_lits. if_true.
  do 4 step.
  apply evt_done. unfold jump_post. reflexivity.
Qed.

(* 0x13954 .. 0x13964, after the third reading: s3 = a0 (r0); a0 = g_own_ran_out (0); bnez a0 not taken;
   fuzz_alloc_ran_out returns 0 (ran_out = out_of_memory() = 0), bnez a0 not taken: on to the compares at 0x13968. *)
Lemma cno_guard3 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  ro_cells rsegs m GL_OWN_RAN_OUT [C1 (Z_to_bv 8 0)] -> ro_cells rsegs m G_RAN_OUT [C1 (Z_to_bv 8 0)] ->
  evt rsegs (jump_post (mkR (Z_to_bv 64 0x13964) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2
                           a3 a4 a5 a6 a7 s2 a0 s4 s5 s6 (Z_to_bv 64 0x347b8) s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x13968) fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 0x347b8) s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x13954) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m OWN GRO.
  unfold GL_OWN_RAN_OUT in OWN. unfold G_RAN_OUT in GRO.
  do 2 step.
  step. br_lits. if_false.
  step.
  cno_call_ranout FAR.
  step. br_lits. if_false.
  apply evt_done. unfold jump_post. reflexivity.
Qed.

End Guards.

(* 0x13968 when the three readings failed (s3 = s4 = s6 <> 0): bnez s4 to 0x13994; bne s4, s3 and bne s6, s3 not
   taken; s5 = 0 (ran_out); a0 = sp + 0x70; jal pj_free (0x15c08), ra 0x139a8. *)
Lemma cno_cmp_none : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  s4 = s3 -> s6 = s3 -> bv_unsigned s3 <> 0 -> bv_unsigned sp + 112 < 2 ^ 64 ->
  evt rsegs (jump_post (mkR (Z_to_bv 64 0x139a8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 112)) a1 a2
                           a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 0) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x15c08) fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13968) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    E4 E6 HA Hsp.
  subst s4 s6.
  step. if_true.
  step. if_false.
  step. if_false.
  do 3 step.
  apply evt_done. unfold jump_post. reflexivity.
Qed.

Definition cmp_some_post (sp gp tp s0 s1 s2 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (L : Z -> Z -> Prop) (lo : Z) (t : jv) (D1 D2 D0 : list (Z * Z)) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x139a8) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 112)) a1 a2 a3 a4 a5 a6 a7
                  s2 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x15c08) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - same_k t, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\
    pj_node rsegs m' L (bv_unsigned sp + 112) t D1 /\ pj_node rsegs m' L (bv_unsigned sp + 56) t D2 /\
    pj_node rsegs m' L (bv_unsigned sp) t D0.

Section Same.
Hypothesis SAME : same_contract.

(* 0x13968 when the three readings succeeded (s3 = s4 = s6 = 0): same(sp + 0x70, sp + 0x38) at 0x13978 (ra 0x1397c),
   same(sp + 0x70, sp) at 0x1398c (ra 0x13990), both 1 on equal trees; then the two bne not taken; s5 = 0;
   a0 = sp + 0x70; jal pj_free, ra 0x139a8. *)
Lemma cno_cmp_some : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (L : Z -> Z -> Prop) (lo : Z) (t : jv)
    (D1 D2 D0 : list (Z * Z)),
  bv_unsigned sp + 168 <= 2 ^ 64 ->
  pj_node rsegs m L (bv_unsigned sp + 112) t D1 -> pj_node rsegs m L (bv_unsigned sp + 56) t D2 ->
  pj_node rsegs m L (bv_unsigned sp) t D0 ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + same_k t <= bv_unsigned sp ->
  (forall z, pj_foot (bv_unsigned sp + 112) D1 z -> outside [(bv_unsigned sp - same_k t, bv_unsigned sp)] z) ->
  (forall z, pj_foot (bv_unsigned sp + 56) D2 z -> outside [(bv_unsigned sp - same_k t, bv_unsigned sp)] z) ->
  (forall z, pj_foot (bv_unsigned sp) D0 z -> outside [(bv_unsigned sp - same_k t, bv_unsigned sp)] z) ->
  evt rsegs (cmp_some_post sp gp tp s0 s1 s2 s7 s8 s9 s10 s11 F fc m L lo t D1 D2 D0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 0) (Z_to_bv 64 0) s5 (Z_to_bv 64 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13968) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L lo t D1 D2 D0
    Hsp P1 P2 P0 MI ST LO O1 O2 O0.
  step. if_false.
  step. if_false.
  step. step. step.
  eapply evt_cut.
  { eapply SAME with (pa := bv_unsigned sp + 112) (pb := bv_unsigned sp + 56) (ta := t) (tb := t)
      (Da := D1) (Db := D2) (L := L) (lo := lo); first [reflexivity | eassumption]. }
  intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
              E & MU2 & WM2 & MI2 & ST2 & RES & Q1 & Q2).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x1397c)) with (Z_to_bv 64 0x1397c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct RES as [(_ & Er)|(NE & _)]; [subst r | congruence].
  pose proof (pj_node_munch rsegs _ m L m2 L _ t D0 P0 (pj_node_blocks rsegs t m L _ D0 P0) MU2 O0) as Q0.
  clear P1 P2 P0 MI ST.
  step. if_false.
  step. if_false.
  step. step. step.
  eapply evt_cut.
  { eapply SAME with (pa := bv_unsigned sp + 112) (pb := bv_unsigned sp) (ta := t) (tb := t)
      (Da := D1) (Db := D0) (L := L) (lo := lo);
      first [reflexivity | eassumption | symmetry; apply Z_to_bv_bv_unsigned]. }
  intros ms' (t0'' & t1'' & t2'' & r & b1 & b2 & b3 & b4 & b5 & b6 & b7 & t3'' & t4'' & t5'' & t6'' & m3 &
              E & MU3 & WM3 & MI3 & ST3 & RES & R1 & R0).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x13990)) with (Z_to_bv 64 0x13990) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct RES as [(_ & Er)|(NE & _)]; [subst r | congruence].
  pose proof (pj_node_munch rsegs _ m2 L m3 L _ t D2 Q2 (pj_node_blocks rsegs t m2 L _ D2 Q2) MU3 O2) as R2.
  pose proof (munch_trans _ _ _ _ MU2 MU3) as MU.
  pose proof (wmono_trans rsegs _ _ _ WM2 WM3) as WM.
  clear Q1 Q2 Q0 MI2 ST2 MU2 MU3 WM2 WM3.
  step. if_false.
  step. if_false.
  step. if_false.
  do 3 step.
  finish.
Qed.

End Same.

(* 0x139a8: a0 = sp + 0x38; jal pj_free, ra 0x139b0. *)
Lemma cno_mv_free2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  bv_unsigned sp + 56 < 2 ^ 64 ->
  evt rsegs (jump_post (mkR (Z_to_bv 64 0x139b0) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 56)) a1 a2
                           a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15c08) fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x139a8) fc None m (seg_rom rsegs)).
Proof.
  intros. do 2 step. apply evt_done. unfold jump_post. reflexivity.
Qed.

(* 0x139b0: a0 = sp; jal pj_free, ra 0x139b8. *)
Lemma cno_mv_free3 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (jump_post (mkR (Z_to_bv 64 0x139b8) sp gp tp t0 t1 t2 s0 s1 sp a1 a2
                           a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15c08) fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x139b0) fc None m (seg_rom rsegs)).
Proof.
  intros. do 2 step. apply evt_done. unfold jump_post. reflexivity.
Qed.

(* 0x139b8: a0 = s0; jal free (0x17798), ra 0x139c0. *)
Lemma cno_mv_rel1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (jump_post (mkR (Z_to_bv 64 0x139c0) sp gp tp t0 t1 t2 s0 s1 s0 a1 a2
                           a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x17798) fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x139b8) fc None m (seg_rom rsegs)).
Proof.
  intros. do 2 step. apply evt_done. unfold jump_post. reflexivity.
Qed.

(* 0x139c0: a0 = s1; jal free, ra 0x139c8. *)
Lemma cno_mv_rel2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (jump_post (mkR (Z_to_bv 64 0x139c8) sp gp tp t0 t1 t2 s0 s1 s1 a1 a2
                           a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x17798) fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x139c0) fc None m (seg_rom rsegs)).
Proof.
  intros. do 2 step. apply evt_done. unfold jump_post. reflexivity.
Qed.

(* 0x139c8: a0 = s2; jal free, ra 0x139d0. *)
Lemma cno_mv_rel3 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (jump_post (mkR (Z_to_bv 64 0x139d0) sp gp tp t0 t1 t2 s0 s1 s2 a1 a2
                           a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x17798) fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x139c8) fc None m (seg_rom rsegs)).
Proof.
  intros. do 2 step. apply evt_done. unfold jump_post. reflexivity.
Qed.

(* 0x139d0 .. 0x139fc: a0 = s5 (ran_out); ld ra, s0..s7 from sp + 0xe8 .. sp + 0xa8; addi sp, sp, 0xf0; ret. *)
Lemma cno_epilogue : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v s6v s7v : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  bv_unsigned sp + 240 < 2 ^ 64 ->
  bytes_at rsegs m (bv_unsigned sp + 168)
    (le8 s7v ++ le8 s6v ++ le8 s5v ++ le8 s4v ++ le8 s3v ++ le8 s2v ++ le8 s1v ++ le8 s0v ++ le8 rav) ->
  evt rsegs (jump_post (mkR rav (Z_to_bv 64 (bv_unsigned sp + 240)) gp tp t0 t1 t2 s0v s1v s5 a1 a2
                           a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc rav) fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x139d0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    rav s0v s1v s2v s3v s4v s5v s6v s7v F fc m Hsp BY.
  assert (RO : ro_cells rsegs m (bv_unsigned sp + 168)
                 [C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]).
  { split; [cbn [cells_wf cell_wf]; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BY. }
  clear BY.
  do 12 step. apply evt_done. unfold jump_post. reflexivity.
Qed.
