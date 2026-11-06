(* Shared helpers for the evt segments of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain):
   the move of a segment's evt body onto the CJ-normalized memory, where MemNorm.task_mem holds, which every callee
   that prints needs (printf_env) and which FR does not give for the slot's [normalize rsegs mem].
   - M1 mem := normalize_cj (normalize mem): no read-only byte, no byte above TASK_SIZE outside the image;
   - m1_mem_inv, m1_task_mem: the machine facts of M1;
   - bytes_m1, wr_m1, stk_m1, rw_cells_m1: facts of mem (or of normalize mem) below TASK_SIZE hold of M1;
   - bytes_back: a fact of the inner run's end memory holds of every memory the slot relates to the outer end;
   - apart_noimg: a block with no byte in the image's reserved pages lies apart from a range inside one page set;
   - seg_lift_cj: an evt from M1 to a post with munch / wmono / sp, gp, tp / Pin gives seg_evt's post from
     normalize mem (MemNorm.evt_normalize_cj, FrameAPI.wx_apart_rsegs).
   Segment lemma: the memory lift the evt segments share. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0o YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require RoAdapt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec.
Import ListNotations.
Open Scope Z_scope.

Definition M1 (mem : word -> option byte) : word -> option byte := normalize_cj rsegs (normalize rsegs mem).

Lemma ro_agree_norm : forall mem, ro_agree rsegs (normalize rsegs mem).
Proof.
  intros mem a Hro. unfold mrd, normalize. rewrite Hro. reflexivity.
Qed.

Lemma m1_rel : forall mem, mem_rel_cj rsegs (normalize rsegs mem) (M1 mem).
Proof. intros mem. apply mem_rel_cj_normalize. apply ro_agree_norm. Qed.

Lemma m1_mem_inv : forall mem, Mem.mem_inv rsegs (M1 mem).
Proof.
  intros mem a b E. unfold M1, normalize_cj in E. destruct (cj_drop rsegs a) eqn:D; [discriminate E|].
  exact (proj1 (cj_drop_false rsegs a D)).
Qed.

Lemma m1_task_mem : forall mem, MemNorm.task_mem rsegs (M1 mem).
Proof.
  intros mem a b E. unfold M1, normalize_cj in E. destruct (cj_drop rsegs a) eqn:D; [discriminate E|].
  exact (proj2 (cj_drop_false rsegs a D)).
Qed.

(* A fact of mem below TASK_SIZE holds of M1 mem. *)
Lemma bytes_m1 : forall mem a bs, ro_agree rsegs mem -> a + Z.of_nat (length bs) <= TASK_SIZE ->
  bytes_at rsegs mem a bs -> bytes_at rsegs (M1 mem) a bs.
Proof.
  intros mem a bs Hro Hlt H. unfold M1. apply bytes_at_normalize_cj_low; [apply ro_agree_norm | exact Hlt |].
  exact (bytes_at_normalize rsegs mem a bs Hro H).
Qed.

Lemma bytes_m1_n : forall mem a bs, a + Z.of_nat (length bs) <= TASK_SIZE ->
  bytes_at rsegs (normalize rsegs mem) a bs -> bytes_at rsegs (M1 mem) a bs.
Proof.
  intros mem a bs Hlt H. unfold M1. apply bytes_at_normalize_cj_low; [apply ro_agree_norm | exact Hlt | exact H].
Qed.

Lemma rel_norm_self : forall mem, mem_rel rsegs (normalize rsegs mem) (normalize rsegs mem).
Proof.
  intros mem. split.
  - intros a. unfold normalize. destruct (ro_addr rsegs a); reflexivity.
  - intros a b Hro E. unfold normalize in E. rewrite Hro in E. discriminate E.
Qed.

Lemma keep_low : forall mem x, wview rsegs (normalize rsegs mem) x <> None -> bv_unsigned x < TASK_SIZE ->
  cj_drop rsegs x = false.
Proof.
  intros mem x Hw Hlt. apply cj_drop_false_intro.
  - exact (ro_false_of_wview rsegs (normalize rsegs mem) (normalize rsegs mem) x (rel_norm_self mem) Hw).
  - right. exact Hlt.
Qed.

Lemma wa_low : forall a, 0 <= a < TASK_SIZE -> bv_unsigned (wa a) < TASK_SIZE.
Proof.
  intros a Ha. unfold wa. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  replace (bv_modulus 64) with (2 ^ 64) by reflexivity. unfold TASK_SIZE in *. rewrite Z.mod_small; lia.
Qed.

Lemma wr_m1 : forall mem a n, wr_at rsegs (normalize rsegs mem) a n -> a + n <= TASK_SIZE ->
  wr_at rsegs (M1 mem) a n.
Proof.
  intros mem a n H Hlt. pose proof H as (H0 & H1 & H2).
  apply (wr_at_norm_cj rsegs (normalize rsegs mem) (M1 mem) a n (m1_rel mem) H).
  intros i Hi. apply (keep_low mem); [exact (H2 i Hi)|]. apply wa_low. lia.
Qed.

Lemma stk_m1 : forall mem lo hi, stk rsegs (normalize rsegs mem) lo hi -> hi <= TASK_SIZE ->
  stk rsegs (M1 mem) lo hi.
Proof.
  intros mem lo hi (H0 & H1 & H) Hlt. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb).
  assert (Hk : cj_drop rsegs (wa a) = false) by (apply (keep_low mem); [exact Hw | apply wa_low; lia]).
  split.
  - rewrite (wview_rel_cj rsegs (normalize rsegs mem) (M1 mem) (wa a) (m1_rel mem) Hk). exact Hw.
  - exists b. unfold mrd in *. rewrite (mem_rel_cj_keep rsegs _ _ _ (m1_rel mem) Hk). exact Hb.
Qed.

(* Back from the inner run's end memory m1' to a memory m the slot relates (mem_rel) to the outer end m'. *)
Lemma bytes_back : forall m m' m1' a bs, mem_rel_cj rsegs m' m1' -> mem_rel rsegs m m' ->
  bytes_at rsegs m1' a bs -> bytes_at rsegs m a bs.
Proof.
  intros m m' m1' a bs H1 H2 H.
  pose proof (bytes_at_rel_cj rsegs m' m1' a bs H1 H) as H'.
  destruct H' as (Ha & Hb & Hc). split; [exact Ha|]. split; [exact Hb|]. intros i Hi.
  rewrite <- (Hc i Hi). apply (mrd_rel rsegs m m'). exact H2.
Qed.

(* A block with no byte in the reserved pages lies apart from a range whose every byte is in a reserved page. *)
Lemma apart_noimg : forall x n lo hi, blk_noimg rsegs x n -> 0 < n -> lo < hi ->
  (forall a, lo <= a < hi -> exists s, In s (segments_reserved rsegs) /\
     bv_unsigned (fst s) <= a < bv_unsigned (fst s) + bv_unsigned (snd s)) ->
  apart x n lo hi.
Proof.
  intros x n lo hi H Hn Hlh Hall. unfold apart.
  destruct (Z_le_gt_dec (x + n) lo) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec hi x) as [R|R]; [right; exact R|].
  exfalso. assert (Hi : 0 <= Z.max lo x - x < n) by lia.
  destruct (Hall (Z.max lo x) ltac:(lia)) as (s & Hin & Hs).
  apply (H (Z.max lo x - x) Hi s Hin). replace (x + (Z.max lo x - x)) with (Z.max lo x) by lia. exact Hs.
Qed.

Lemma mrd_m1 : forall mem x, ro_agree rsegs mem -> bv_unsigned x < TASK_SIZE -> mrd rsegs (M1 mem) x = mrd rsegs mem x.
Proof.
  intros mem x Hro Hx. unfold M1.
  rewrite (mrd_normalize_cj rsegs (normalize rsegs mem) x (ro_agree_norm mem) (or_intror (or_intror Hx))).
  symmetry. exact (mrd_rel rsegs mem (normalize rsegs mem) x (mem_rel_normalize rsegs mem Hro)).
Qed.

Lemma mrd_m1_n : forall mem x, bv_unsigned x < TASK_SIZE ->
  mrd rsegs (M1 mem) x = mrd rsegs (normalize rsegs mem) x.
Proof.
  intros mem x Hx. unfold M1.
  exact (mrd_normalize_cj rsegs (normalize rsegs mem) x (ro_agree_norm mem) (or_intror (or_intror Hx))).
Qed.

(* n bytes are there when every one of them reads. *)
Lemma bytes_exist : forall m a n, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall k, (k < n)%nat -> exists b, mrd rsegs m (wa (a + Z.of_nat k)) = Some b) ->
  exists bs, length bs = n /\ bytes_at rsegs m a bs.
Proof.
  intros m a n H0 H1 H.
  exists (map (fun k => match mrd rsegs m (wa (a + Z.of_nat k)) with Some b => b | None => Z_to_bv 8 0 end)
            (seq 0 n)).
  split; [rewrite length_map, length_seq; reflexivity|].
  split; [exact H0|]. rewrite length_map, length_seq. split; [exact H1|].
  intros i Hi. assert (Hn : nth_error (seq 0 n) i = Some i).
  { rewrite nth_error_seq. replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi). reflexivity. }
  rewrite nth_error_map, Hn. unfold option_map. cbv beta iota.
  destruct (H i Hi) as (b & Hb). rewrite Hb. reflexivity.
Qed.

Lemma wr_of_stk : forall m lo hi, stk rsegs m lo hi -> wr_at rsegs m lo (hi - lo).
Proof.
  intros m lo hi (H0 & H1 & H). split; [exact H0|]. split; [lia|]. intros i Hi. apply (H (lo + i)). lia.
Qed.

Lemma rw_cells_m1 : forall mem a cs, ro_agree rsegs mem -> a + Z.of_nat (cells_size cs) <= TASK_SIZE ->
  RoAdapt.not_ro rsegs a (Z.of_nat (cells_size cs)) ->
  rw_cells rsegs mem a cs -> rw_cells rsegs (M1 mem) a cs.
Proof.
  intros mem a cs Hro Hlt Hnr H.
  pose proof (RoAdapt.rw_cells_norm rsegs mem a cs Hro H Hnr) as Hn.
  destruct Hn as ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
  - apply bytes_m1_n; [|exact Hb]. rewrite cells_bytes_length by exact Hwf. exact Hlt.
  - apply wr_m1; [exact Hw | exact Hlt].
Qed.

Lemma ms_rel_cj_MS : forall s R F pc fc rv m0 ro, ms_rel_cj rsegs s (MS R F pc fc rv m0 ro) ->
  s = MS R F pc fc rv (ms_mem s) ro /\ mem_rel_cj rsegs (ms_mem s) m0.
Proof.
  intros s R F pc fc rv m0 ro (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8). split; [|exact E8].
  destruct s. cbn in *. subst. reflexivity.
Qed.

(* The lift: an evt body run on M1 mem gives seg_evt's post from normalize mem (Prog/Seg/Tac_seg.v). *)
Lemma seg_lift_cj : forall (mem : word -> option byte) (R F : bvmap 5 word) (pc : word) (fc : bv 32) (pc' : Z)
    (W Win : list ivl) (sp gp tp : word) (Pin Pst : bvmap 5 word -> (word -> option byte) -> Prop),
  sub_fp Win W ->
  (forall R' m1' m' m regs', Pin R' m1' -> mem_rel_cj rsegs m' m1' -> mem_rel rsegs m m' ->
     Regs6ss.xregs_eqv R' regs' -> Pst regs' m) ->
  Exec.evt rsegs (fun s0 => exists R' F' fc' m1', s0 = MS R' F' (Z_to_bv 64 pc') fc' None m1' (seg_rom rsegs) /\
       frm_zero fc' /\ munch Win (M1 mem) m1' /\ wmono rsegs (M1 mem) m1' /\
       YK11.getr R' 2 = sp /\ YK11.getr R' 3 = gp /\ YK11.getr R' 4 = tp /\ Pin R' m1')
    (MS R F pc fc None (M1 mem) (seg_rom rsegs)) ->
  Exec.evt rsegs (fun ms => exists R' F' fc' m', ms = MS R' F' (Z_to_bv 64 pc') fc' None m' (seg_rom rsegs) /\
       frm_zero fc' /\ munch W (normalize rsegs mem) m' /\ wmono rsegs (normalize rsegs mem) m' /\
       YK11.getr R' 2 = sp /\ YK11.getr R' 3 = gp /\ YK11.getr R' 4 = tp /\
       (forall regs' m, Regs6ss.xregs_eqv R' regs' -> mem_rel rsegs m m' -> Pst regs' m))
    (MS R F pc fc None (normalize rsegs mem) (seg_rom rsegs)).
Proof.
  intros mem R F pc fc pc' W Win sp gp tp Pin Pst HW HP HE.
  eapply evt_mono.
  - exact (evt_normalize_cj rsegs _ R F pc fc None (normalize rsegs mem) (seg_rom rsegs) wx_apart_rsegs
             (ro_agree_norm mem) HE).
  - intros s (s0 & (R' & F' & fc' & m1' & -> & Hz & MU & WM & E2 & E3 & E4 & HPin) & Hrel & Hsame).
    destruct (ms_rel_cj_MS s _ _ _ _ _ _ _ Hrel) as (Es & Hm).
    exists R', F', fc', (ms_mem s). split; [exact Es|]. split; [exact Hz|].
    split; [exact (munch_weaken Win W _ _ HW (munch_rel_cj rsegs Win _ _ _ _ (m1_rel mem) Hm Hsame MU))|].
    split; [exact (wmono_rel_cj rsegs _ _ _ _ (m1_rel mem) Hm Hsame WM)|].
    split; [exact E2|]. split; [exact E3|]. split; [exact E4|].
    intros regs' m Hx Hr. exact (HP R' m1' (ms_mem s) m regs' HPin Hm Hr Hx).
Qed.
