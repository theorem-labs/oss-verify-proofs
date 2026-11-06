From Stdlib Require Import String ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Cells Step Frame Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts printf_facts_c RecKindB.
Import ListNotations.
Open Scope Z_scope.

Lemma pf_digits_digits : forall k f n acc, 0 <= n < 10 ^ Z.of_nat (S k) -> (k < f)%nat ->
  pf_bytes (pf_digits f n acc) = digits (S k) n (pf_bytes acc).
Proof.
  induction k as [|k IH]; intros f n acc Hn Hf; destruct f as [|f]; try lia.
  - cbn [pf_digits digits]. change (10 ^ Z.of_nat 1) with 10 in Hn.
    destruct (Z.ltb_spec n 10); [reflexivity | lia].
  - rewrite digits_S. cbn [pf_digits]. destruct (Z.ltb_spec n 10) as [H|H]; [reflexivity|].
    rewrite IH; [reflexivity | | lia].
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
    replace (10 * 10 ^ Z.of_nat (S k)) with (10 ^ Z.of_nat (S (S k)))
      by (rewrite (Nat2Z.inj_succ (S k)), Z.pow_succ_r by lia; ring). lia.
Qed.

Definition RESP_HEAD : list Z := [114; 101; 115; 112; 32].

Lemma pf_resp : forall c, -2^31 <= c < 2^31 -> pf_bytes (RESP_HEAD ++ pf_dec c) = resp c.
Proof.
  intros c Hc. unfold resp, pf_dec, dec, RESP_HEAD. unfold pf_bytes at 1. rewrite map_app. f_equal.
  assert (P : 10 ^ Z.of_nat (S 9) = 10000000000) by reflexivity.
  destruct (Z.ltb_spec c 0) as [N|N].
  - cbn [map app]. f_equal. replace (Z.abs c) with (- c) by lia.
    exact (pf_digits_digits 9 11 (- c) [] ltac:(rewrite P; lia) ltac:(lia)).
  - cbn [app]. replace (Z.abs c) with c by lia.
    exact (pf_digits_digits 9 11 c [] ltac:(rewrite P; lia) ltac:(lia)).
Qed.

Definition RESP_FMT : list Z := [114; 101; 115; 112; 32; 37; 100].
Definition RESP_PS : list pf_piece := [PLit 114; PLit 101; PLit 115; PLit 112; PLit 32; Pd].

Lemma resp_parse : pf_parse RESP_FMT = Some RESP_PS.
Proof. reflexivity. Qed.

Lemma resp_text : forall c, pf_text RESP_PS [AInt c] = Some (RESP_HEAD ++ pf_dec c).
Proof. intros c. cbn. rewrite app_nil_r. reflexivity. Qed.

Lemma resp_fmt_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10982 (pf_bytes (RESP_FMT ++ [0])).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma resp_len : forall c, -2^31 <= c < 2^31 ->
  (6 <= length (RESP_HEAD ++ pf_dec c) <= 16)%nat.
Proof.
  intros c Hc. rewrite <- (length_map (Z_to_bv 8)). change (map (Z_to_bv 8) ?l) with (pf_bytes l).
  rewrite pf_resp by exact Hc. apply resp_length. exact Hc.
Qed.

Lemma stk_normalize : forall mem lo hi, 2 ^ 20 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> YP09.writable_at rsegs mem a) -> stk rsegs (MemNorm.normalize rsegs mem) lo hi.
Proof.
  intros mem lo hi Hlo Hhi HW. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (writable_hi_present mem a ltac:(lia) (HW a Ha)) as [bb E].
  assert (NE : MemNorm.normalize rsegs mem (wa a) = mem (wa a)) by (apply normalize_rw; unfold wa; apply ro_addr_hi; lia).
  unfold wview, mrd. rewrite NE. unfold wa. rewrite E. split; [discriminate | exists bb; reflexivity].
Qed.

Lemma rw_cells_app_split : forall segs m A cs1 cs2, rw_cells segs m A (cs1 ++ cs2) ->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2 [[Hwf Hb] (W1 & W2 & W3)].
  apply cells_wf_app in Hwf as [Hw1 Hw2]. rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [Hb1 Hb2].
  rewrite cells_size_app in W2, W3. rewrite (cells_bytes_length cs1 Hw1) in Hb2.
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply W3. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by ring.
    apply W3. lia.
Qed.

Lemma lit_mod32 : forall z, bv_unsigned (Z_to_bv 64 z) mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
  intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  Z.div_mod_to_equations. lia.
Qed.

Lemma bytes_at_firstn_skipn : forall segs m a bs k, bytes_at segs m a bs ->
  bytes_at segs m a (firstn k bs) /\ bytes_at segs m (a + Z.of_nat (length (firstn k bs))) (skipn k bs).
Proof. intros segs m a bs k H. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. exact H. Qed.

Lemma pf_img_free_hi : forall D n, 2 ^ 21 <= D -> pf_img_free D n.
Proof.
  intros D n HD i Hi s Hs. pose proof (proj1 (forallb_forall _ _) rsegs_res_top s Hs) as T. apply Z.leb_le in T.
  pose proof (bv_unsigned_in_range 64 (fst s)). lia.
Qed.

Lemma stk_normalize_cj : forall mem lo hi, 2 ^ 20 <= lo -> hi <= TASK_SIZE ->
  (forall a, lo <= a < hi -> YP09.writable_at rsegs mem a) -> stk rsegs (MemNorm.normalize_cj rsegs mem) lo hi.
Proof.
  intros mem lo hi Hlo Hhi HW. unfold TASK_SIZE in Hhi. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (writable_hi_present mem a ltac:(lia) (HW a Ha)) as [bb E].
  assert (NE : MemNorm.normalize_cj rsegs mem (wa a) = mem (wa a)).
  { unfold MemNorm.normalize_cj. rewrite (MemNorm.cj_drop_false_intro rsegs (wa a)); [reflexivity | |].
    - unfold wa. apply ro_addr_hi. lia.
    - right. unfold wa. rewrite unsigned_lit by lia. unfold TASK_SIZE. lia. }
  unfold wview, mrd. rewrite NE. unfold wa. rewrite E. split; [discriminate | exists bb; reflexivity].
Qed.

Lemma task_mem_munch1 : forall m m' lo hi, MemNorm.task_mem rsegs m -> munch [(lo, hi)] m m' -> hi <= TASK_SIZE ->
  MemNorm.task_mem rsegs m'.
Proof.
  intros m m' lo hi HT HM Hhi a b E.
  destruct (Z_lt_ge_dec (bv_unsigned a) TASK_SIZE) as [D|D]; [right; exact D|].
  assert (O : outside [(lo, hi)] (bv_unsigned a)) by (cbn; split; [lia | exact I]).
  rewrite (HM a O) in E. exact (HT a b E).
Qed.

Lemma ms_rel_cj_MS : forall s R F pc fc rv m0 ro, MemNorm.ms_rel_cj rsegs s (MS R F pc fc rv m0 ro) ->
  s = MS R F pc fc rv (ms_mem s) ro /\ MemNorm.mem_rel_cj rsegs (ms_mem s) m0.
Proof.
  intros [r f p sv rv' c mm o] R F pc fc rv m0 ro (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  cbn in *. subst. split; [reflexivity | exact H8].
Qed.

Lemma rw_cells_rel_cj : forall segs m m0 a cs, MemNorm.mem_rel_cj segs m m0 -> rw_cells segs m0 a cs -> rw_cells segs m a cs.
Proof.
  intros segs m m0 a cs HR [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - exact (MemNorm.bytes_at_rel_cj segs m m0 a _ HR Hb).
  - exact (MemNorm.wr_at_rel_cj segs m m0 a _ HR Hw).
Qed.
