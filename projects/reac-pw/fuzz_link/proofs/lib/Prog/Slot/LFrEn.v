(* The slot LLVMFuzzerTestOneInput (fuzz_link.c:764-790), plain image: the entry of its SR frame (S-FR item
   8). From the entry's premises LGV (lib_contract_x_T's, lib/Prog/Slot/LFr.v) this file gives
   - lfr_init: the first frame relation, LFR g [] T0 L0 A0 mem0 md0 (boxreg LLVMFuzzerTestOneInput_fr.v
     lf_fr_init); the one fact LGV does not hold, ro_agree of mem0, comes from lib_pre's rodata_ok and the
     allocator's tables (MemNorm.ro_agree_of_rodata_ok; its second premise, the static_owned read-only
     bytes, is len_tbl below: the debruijn / size-class tables are AllocExtra.ax_tables, every other
     static_owned byte of this image lies in a writable segment);
   - lentry_ms: the evt-level state at ENTRY = 0x1384c that the entry worker (a Theorem Labs lane, LEDefs.v
     le_entry_mem) walks from, stated with the LDefs / link_mem predicates;
   - cut_entry: the config at ENTRY is a CUT with lentry_ms, hb = [] and T = T0.
   The memory facts are of the evt view normalize_cj rsegs mem0 (LFr.v lcanon). The image facts are
   closed vm checks over the plain image's segments (seg0 0x10000 r--, seg1 0x12000 r-x, seg2 0x20000 rw-,
   seg3 0x21000 rw-, up to 0x97000): .rodata bytes are read-only (the view reads the image), .data.rel.ro
   bytes are frame_RELRO (G_img gives mem0 = image), and the .bss bytes g_nl, g_names, long_alias and errno
   are writable and readable in EVERY memory (their segment is "rw-" and carries their bytes). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Closed checks over the image, and what they give in any memory
   ========================================================================== *)

(* f holds on [lo, lo + k): a check over a range, linear in k (Z counter, unary length) *)
Fixpoint zall (f : Z -> bool) (lo : Z) (k : nat) : bool :=
  match k with O => true | S k' => f lo && zall f (Z.succ lo) k' end.

Lemma zall_ok : forall f k lo, zall f lo k = true -> forall a, lo <= a < lo + Z.of_nat k -> f a = true.
Proof.
  intros f k. induction k as [|k IH]; intros lo H a Ha; [lia|].
  cbn [zall] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec a lo) as [->|Hne]; [exact H1|].
  apply (IH (Z.succ lo) H2). lia.
Qed.

(* an image byte in a readable and writable segment that carries it: every memory reads and may write it *)
Definition en_chk (a : Z) : bool :=
  match find_segment rsegs a 1 with
  | Some seg => seg_writable seg && seg_readable seg &&
      match segment_byte_at (seg_bytes seg) (Z.to_N (a - Z.of_N (seg_base seg))) with
      | Some _ => true
      | None => false
      end
  | None => false
  end.

Lemma en_chk_ok : forall m a, 0 <= a < 2 ^ 64 -> en_chk a = true ->
  wview rsegs m (wa a) <> None /\ (exists b, Mem.mrd rsegs m (wa a) = Some b) /\
  Mem.ro_addr rsegs (wa a) = false.
Proof.
  intros m a Ha H. unfold en_chk in H.
  assert (Eu : bv_unsigned (wa a) = a) by (apply Mem.wa_unsigned; exact Ha).
  destruct (find_segment rsegs a 1) as [seg|] eqn:Ef; [|discriminate H].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (a - Z.of_N (seg_base seg)))) as [b|] eqn:Eb;
    [|discriminate H3].
  split; [|split].
  - unfold wview. destruct (m (wa a)); [discriminate|]. rewrite Eu, Ef, H1, Eb. discriminate.
  - unfold Mem.mrd. destruct (m (wa a)) as [b'|]; [exists b'; reflexivity|].
    exists b. unfold seg_rom, memory_read. rewrite Eu. change (Z.of_N 1) with 1. rewrite Ef, H2.
    cbv zeta. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite Eb. reflexivity.
  - unfold Mem.ro_addr. rewrite Eu, Ef, H1. reflexivity.
Qed.

(* the bytes a memory reads at [A, A + n) *)
Fixpoint rd_list (m : word -> option byte) (A : Z) (n : nat) : list byte :=
  match n with
  | O => []
  | S n' => match Mem.mrd rsegs m (wa A) with Some b => b | None => zb 0 end :: rd_list m (A + 1) n'
  end.

Lemma rd_list_length : forall m n A, length (rd_list m A n) = n.
Proof. intros m n. induction n as [|n IH]; intros A; cbn [rd_list length]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma rd_list_nth : forall m n A i, (i < n)%nat ->
  (exists b, Mem.mrd rsegs m (wa (A + Z.of_nat i)) = Some b) ->
  Mem.mrd rsegs m (wa (A + Z.of_nat i)) = nth_error (rd_list m A n) i.
Proof.
  intros m n. induction n as [|n IH]; intros A i Hi Hb; [lia|].
  destruct i as [|i]; cbn [rd_list nth_error].
  - replace (A + Z.of_nat 0) with A in * by lia. destruct Hb as [b Hb]. rewrite Hb. reflexivity.
  - replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) in * by lia. apply IH; [lia | exact Hb].
Qed.

Lemma rd_list_at : forall m A n, 0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> exists b, Mem.mrd rsegs m (wa (A + Z.of_nat i)) = Some b) ->
  Mem.bytes_at rsegs m A (rd_list m A n).
Proof.
  intros m A n HA Hn H. split; [exact HA|]. rewrite rd_list_length. split; [exact Hn|].
  intros i Hi. apply rd_list_nth; [exact Hi | exact (H i Hi)].
Qed.

Lemma en_rd : forall m A n, 0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  (forall a, A <= a < A + Z.of_nat n -> en_chk a = true) -> Mem.bytes_at rsegs m A (rd_list m A n).
Proof.
  intros m A n HA Hn H. apply rd_list_at; [exact HA | exact Hn|].
  intros i Hi. exact (proj1 (proj2 (en_chk_ok m (A + Z.of_nat i) ltac:(lia) (H (A + Z.of_nat i) ltac:(lia))))).
Qed.

Lemma en_wr : forall m A n, 0 <= A -> A + n <= 2 ^ 64 ->
  (forall a, A <= a < A + n -> en_chk a = true) -> Mem.wr_at rsegs m A n.
Proof.
  intros m A n HA Hn H. split; [exact HA|]. split; [exact Hn|].
  intros i Hi. exact (proj1 (en_chk_ok m (A + i) ltac:(lia) (H (A + i) ltac:(lia)))).
Qed.

Lemma en_rw_cb : forall m A n, 0 <= A -> 0 <= n -> A + n <= 2 ^ 64 ->
  (forall a, A <= a < A + n -> en_chk a = true) -> exists bs, Step.rw_cells rsegs m A [CB (Z.to_nat n) bs].
Proof.
  intros m A n HA Hn HAn H. exists (rd_list m A (Z.to_nat n)).
  split; [split|].
  - cbn [Cells.cells_wf Cells.cell_wf]. split; [apply rd_list_length | exact I].
  - cbn [Cells.cells_bytes Cells.cbytes]. rewrite app_nil_r.
    apply en_rd; [exact HA | rewrite Z2Nat.id by lia; exact HAn | rewrite Z2Nat.id by lia; exact H].
  - cbn [Cells.cells_size Cells.csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact (en_wr m A n HA HAn H).
Qed.

(* g_nl, g_names and long_alias with its 3 slack bytes: one run of .bss, [0x31b80, 0x74528) *)
Definition EN_BSS_LEN : Z := NK_SIZE + G_NAMES_SIZE + LONG_ALIAS_SIZE + 3.

Lemma en_bss_chk : zall en_chk A_G_NL (Z.to_nat 272808) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma en_bss : forall a, A_G_NL <= a < A_G_NL + EN_BSS_LEN -> en_chk a = true.
Proof.
  intros a Ha. apply (zall_ok en_chk (Z.to_nat 272808) A_G_NL en_bss_chk).
  unfold EN_BSS_LEN, NK_SIZE, G_NAMES_SIZE, LONG_ALIAS_SIZE in Ha. rewrite Z2Nat.id by lia. exact Ha.
Qed.

Lemma en_errno_chk : zall en_chk A_ERRNO 4 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma en_errno : forall a, A_ERRNO <= a < A_ERRNO + 4 -> en_chk a = true.
Proof. intros a Ha. exact (zall_ok en_chk 4 A_ERRNO en_errno_chk a Ha). Qed.

(* the static_owned bytes of this image that are not the allocator's tables lie in writable segments:
   [0x95878, 0x95910) (guard, libc + 3 / + 8 / + 48, lock) and the GOT guard [0x208d8, 0x208e0) *)
Definition en_rw_b (a : Z) : bool := negb (Mem.ro_addr rsegs (Z_to_bv 64 a)).

Lemma en_so_chk : zall en_rw_b 0x95878 (Z.to_nat 0x98) && zall en_rw_b 0x208d8 8 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma en_so_rw : forall a, (0x95878 <= a < 0x95910 \/ 0x208d8 <= a < 0x208e0) ->
  Mem.ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. pose proof en_so_chk as Hc. apply andb_prop in Hc as [H1 H2].
  assert (E : en_rw_b a = true).
  { destruct Ha as [Ha|Ha].
    - apply (zall_ok en_rw_b (Z.to_nat 0x98) 0x95878 H1). rewrite Z2Nat.id by lia. lia.
    - apply (zall_ok en_rw_b 8 0x208d8 H2). cbn [Z.of_nat Pos.of_succ_nat]. lia. }
  unfold en_rw_b in E. apply negb_true_iff in E. exact E.
Qed.

(* the image bytes at [a, a + |bs|): read-only (the view reads the image) or .data.rel.ro (frame_RELRO,
   where G_img gives the image's bytes), and equal to bs *)
Definition relro_b (x : Z) : bool :=
  existsb (fun r => (fst r <=? x) && (x <? fst r + snd r)) frame_RELRO.

Lemma relro_b_ok : forall x, relro_b x = true -> in_globals frame_RELRO x.
Proof.
  intros x H. unfold relro_b in H. apply existsb_exists in H as ([lo len] & Hin & Hc).
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists lo, len. split; [exact Hin | cbn [fst snd] in *; lia].
Qed.

Definition img_byte_ok (x : Z) (b : byte) : bool :=
  (Mem.ro_addr rsegs (Z_to_bv 64 x) || relro_b x) &&
  match seg_rom rsegs (Z_to_bv 64 x) with Some b' => Z.eqb (bv_unsigned b') (bv_unsigned b) | None => false end.

Fixpoint img_bytes_b (a : Z) (bs : list byte) : bool :=
  match bs with [] => true | b :: bs' => img_byte_ok a b && img_bytes_b (a + 1) bs' end.

Definition img_chk (a : Z) (bs : list byte) : bool :=
  (0 <=? a) && (a + Z.of_nat (length bs) <=? TASK_SIZE) && img_bytes_b a bs.

Definition nz_b (s : list byte) : bool := forallb (fun b => negb (Z.eqb (bv_unsigned b) 0)) s.

Definition cstr_chk (a : Z) (s : list byte) : bool := img_chk a (s ++ [zb 0]) && nz_b s.

Lemma img_byte_sound : forall m x b, MemNorm.ro_agree rsegs m -> G_img rsegs frame_RELRO m ->
  img_byte_ok x b = true -> Mem.mrd rsegs m (Z_to_bv 64 x) = Some b.
Proof.
  intros m x b Hro HG H. unfold img_byte_ok in H. apply andb_prop in H as [Hk Hs].
  destruct (seg_rom rsegs (Z_to_bv 64 x)) as [b'|] eqn:Es; [|discriminate Hs].
  apply Z.eqb_eq in Hs. assert (Eb : b' = b) by (apply bv_eq; exact Hs). subst b'.
  apply orb_prop in Hk as [Hk|Hk].
  - rewrite (Hro _ Hk). exact Es.
  - pose proof (HG x (relro_b_ok x Hk)) as E. change (mbyte rsegs m x = Some b). rewrite E. exact Es.
Qed.

Lemma img_bytes_b_ok : forall m bs a, MemNorm.ro_agree rsegs m -> G_img rsegs frame_RELRO m ->
  img_bytes_b a bs = true -> forall i, (i < length bs)%nat -> Mem.mrd rsegs m (wa (a + Z.of_nat i)) = nth_error bs i.
Proof.
  intros m bs. induction bs as [|b bs IH]; intros a Hro HG H i Hi; cbn [length] in Hi; [lia|].
  cbn [img_bytes_b] in H. apply andb_prop in H as [Hb H].
  destruct i as [|i]; cbn [nth_error].
  - replace (a + Z.of_nat 0) with a by lia. exact (img_byte_sound m a b Hro HG Hb).
  - replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply (IH (a + 1) Hro HG H). lia.
Qed.

Lemma img_chk_ok : forall m a bs, MemNorm.ro_agree rsegs m -> G_img rsegs frame_RELRO m ->
  img_chk a bs = true -> Mem.bytes_at rsegs (normalize_cj rsegs m) a bs.
Proof.
  intros m a bs Hro HG H. unfold img_chk in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply (bytes_at_normalize_cj_low rsegs m a bs Hro H2).
  split; [exact H1|]. split; [unfold TASK_SIZE in H2; lia|].
  exact (img_bytes_b_ok m bs a Hro HG H3).
Qed.

Lemma nz_b_ok : forall s, nz_b s = true -> ~ In (zb 0) s.
Proof.
  intros s H Hin. unfold nz_b in H. rewrite forallb_forall in H. specialize (H _ Hin).
  vm_compute in H. discriminate H.
Qed.

Lemma cstr_chk_ok : forall m a s, MemNorm.ro_agree rsegs m -> G_img rsegs frame_RELRO m ->
  cstr_chk a s = true -> cstr_at (normalize_cj rsegs m) a s.
Proof.
  intros m a s Hro HG H. unfold cstr_chk in H. apply andb_prop in H as [H1 H2].
  split; [exact (img_chk_ok m a _ Hro HG H1) | exact (nz_b_ok s H2)].
Qed.

Lemma en_texts_chk :
  forallb (fun i => img_chk (A_TEXTS + 8 * Z.of_nat i) (le8 (wz (nth i texts_ptrs 0)))) (seq 0 11) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma en_odd_chk :
  forallb (fun i => img_chk (A_ODD + 8 * Z.of_nat i) (le8 (wz (nth i odd_ptrs 0))) &&
                    cstr_chk (nth i odd_ptrs 0) (nth i odd_strs [])) (seq 0 6) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma en_policy_chk :
  cstr_chk A_PREFIX S_PREFIX && cstr_chk A_SERVED S_SERVED && cstr_chk A_VLAN S_VLAN && cstr_chk A_EMPTY [] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma en_img : forall m, MemNorm.ro_agree rsegs m -> G_img rsegs frame_RELRO m ->
  odd_at (normalize_cj rsegs m) /\ texts_at (normalize_cj rsegs m) /\ policy_ro (normalize_cj rsegs m).
Proof.
  intros m Hro HG. split; [|split].
  - intros i Hi. pose proof (proj1 (forallb_forall _ _) en_odd_chk i (proj2 (in_seq 6 0 i) ltac:(lia))) as H.
    apply andb_prop in H as [H1 H2].
    split; [exact (img_chk_ok m _ _ Hro HG H1) | exact (cstr_chk_ok m _ _ Hro HG H2)].
  - intros i Hi. pose proof (proj1 (forallb_forall _ _) en_texts_chk i (proj2 (in_seq 11 0 i) ltac:(lia))) as H.
    exact (img_chk_ok m _ _ Hro HG H).
  - pose proof en_policy_chk as H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
    apply andb_prop in H as [H1 H2].
    split; [exact (cstr_chk_ok m _ _ Hro HG H1)|]. split; [exact (cstr_chk_ok m _ _ Hro HG H2)|].
    split; [exact (cstr_chk_ok m _ _ Hro HG H3) | exact (cstr_chk_ok m _ _ Hro HG H4)].
Qed.

(* a word the allocator's laws give byte by byte (YO0d word_mem), as the 8 bytes le8 (KindBGlue.v
   word_mem_le8, restated here to keep this file's imports small) *)
Lemma en_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. f_equal. lia.
Qed.

Lemma en_le_byte_bv : forall v k, 0 <= v < 2 ^ 64 ->
  Z_to_bv 8 (le_byte v 8 k) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)).
Proof.
  intros v k Hv. unfold le_byte. change (8 * Z.of_nat 8) with 64.
  rewrite (Z.mod_small v (2 ^ 64)) by lia.
  apply Mem.Z_to_bv8_mod. change 256 with (2 ^ 8). apply Z.mod_mod. lia.
Qed.

Lemma en_word_mem_le8 : forall m a v, word_mem rsegs m a v -> 0 <= v < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  Mem.bytes_at rsegs m a (Mem.le8 (Z_to_bv 64 v)).
Proof.
  intros m a v Hw Hv Ha Hb. split; [exact Ha|]. rewrite Mem.length_le8. split; [lia|].
  intros i Hi. unfold Mem.le8, word_to_le_bytes. rewrite en_nth_le_bytes by exact Hi.
  rewrite MState.unsigned_lit by lia. rewrite <- en_le_byte_bv by exact Hv. exact (Hw i Hi).
Qed.

(* the view keeps a byte's writability where it keeps the byte: below TASK_SIZE and not read-only *)
Lemma en_wv : forall m x, 0 <= x < TASK_SIZE -> Mem.ro_addr rsegs (wa x) = false ->
  wview rsegs (normalize_cj rsegs m) (wa x) = wview rsegs m (wa x).
Proof.
  intros m x Hx Hro. unfold wview, normalize_cj.
  assert (Eu : bv_unsigned (wa x) = x) by (apply Mem.wa_unsigned; unfold TASK_SIZE in Hx; lia).
  assert (Ec : cj_drop rsegs (wa x) = false).
  { apply (cj_drop_false_intro rsegs (wa x) Hro). right. rewrite Eu. lia. }
  rewrite Ec. reflexivity.
Qed.

Lemma en_hi_ro : forall a, LF_TOP <= a < 2 ^ 64 -> Mem.ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold Mem.ro_addr. rewrite Mem.wa_unsigned by (unfold LF_TOP in Ha; lia).
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. pose proof (lfr_find_top a 1 seg E). unfold LF_TOP in *. lia.
Qed.

(* ==========================================================================
   2. The evt-level state at ENTRY (a Theorem Labs lane's le_entry_mem, in LDefs / link_mem terms)
   ========================================================================== *)

(* the payload pointer as the entry stores it: p itself (0 <= p < 2^64 when n > 0, len_ghost); when n = 0
   lib_pre gives only p = empty, an arbitrary Z, so the 64-bit value of a0 is used *)
Definition len_p0 (g : lghost) : Z := bv_unsigned (wz (lg_p g)).

(* the ghost facts the entry needs. a Theorem Labs lane's le_place asks A_IMG_TOP <= p0 at every n: that is false at
   n = 0 (p0 is the contract's `empty`, 0x31b60 under the frame) and not given at n > 0 (the allocator's
   laws place a block at 4096 <= p, below its ceiling and outside the image, nothing more); what holds at
   n > 0 is LDefs blk_out S p n *)
Definition len_ghost (g : lghost) : Prop :=
  lg_S g mod 16 = 0 /\ 0x960e0 + SLOT_STACK_Z <= lg_S g /\ lg_S g <= 2 ^ 47 /\
  lg_n g = Z.of_nat (length (lg_pl g)) /\ lg_n g <= 2 ^ 28 + 2 ^ 11 /\
  (0 < lg_n g -> len_p0 g = lg_p g /\ blk_out (lg_S g) (lg_p g) (lg_n g)).

(* the memory at ENTRY: exactly the conjuncts of a Theorem Labs lane's le_entry_mem (LEDefs.v) for
   G = LEnt (lg_S g) (len_p0 g) (lg_pl g) gp R, in the same nesting (le_base (le_img ..) ..) *)
Definition len_mem (g : lghost) (m : word -> option byte) : Prop :=
  ((odd_at m /\ texts_at m /\ policy_ro m /\ guard_m m) /\
   la_ok m /\ bytes_at rsegs m (len_p0 g) (lg_pl g) /\ wr_at rsegs m A_ERRNO 4 /\
   mem_inv rsegs m /\ MemNorm.task_mem rsegs m) /\
  (exists jk, rw_cells rsegs m A_G_NL [CB (Z.to_nat NK_SIZE) jk]) /\
  (exists jg, rw_cells rsegs m A_G_NAMES [CB (Z.to_nat G_NAMES_SIZE) jg]) /\
  stk rsegs m (lg_S g - SLOT_STACK_Z) (lg_S g).

(* the machine state at ENTRY: every register is regs0's (ra, sp, tp, a0, a1 as lib_pre fixes them), the
   FP file free with rounding mode 0, the view m with len_mem *)
Definition lentry_ms (g : lghost) (ms : machine_state) : Prop :=
  exists (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ms = MS (mkR (wz (lg_ra g)) (wz (lg_S g)) (getr (lg_regs g) 3) (wz A_TP)
                 (getr (lg_regs g) 5) (getr (lg_regs g) 6) (getr (lg_regs g) 7)
                 (getr (lg_regs g) 8) (getr (lg_regs g) 9) (wz (len_p0 g)) (wz (lg_n g))
                 (getr (lg_regs g) 12) (getr (lg_regs g) 13) (getr (lg_regs g) 14) (getr (lg_regs g) 15)
                 (getr (lg_regs g) 16) (getr (lg_regs g) 17) (getr (lg_regs g) 18) (getr (lg_regs g) 19)
                 (getr (lg_regs g) 20) (getr (lg_regs g) 21) (getr (lg_regs g) 22) (getr (lg_regs g) 23)
                 (getr (lg_regs g) 24) (getr (lg_regs g) 25) (getr (lg_regs g) 26) (getr (lg_regs g) 27)
                 (getr (lg_regs g) 28) (getr (lg_regs g) 29) (getr (lg_regs g) 30) (getr (lg_regs g) 31))
            F (wz L_ENTRY) fc None m (seg_rom rsegs) /\
    frm0 fc /\ len_ghost g /\ len_mem g m.

Lemma len_p0_eq : forall g, 0 <= lg_p g < 2 ^ 64 -> len_p0 g = lg_p g.
Proof. intros g H. unfold len_p0, wz. apply MState.unsigned_lit. exact H. Qed.

(* ==========================================================================
   3. lfr_init and cut_entry
   ========================================================================== *)

Section EN.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.

(* lff_ax holds at every FP state (LFF's frame_allocator is stated for each); fx0 keeps the lemmas below free
   of an FP-state argument they do not use *)
Let AX : AllocExtra B (aa_MR API) := @lff_ax YK11.fx0 rc B API SH SK FF.

(* MemNorm.ro_agree_of_rodata_ok's second premise (FrameSlotG.v's TBL) for this image *)
Lemma len_tbl : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned B a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true -> mbyte (ms_segs B) mem a = seg_rom (ms_segs B) (Z_to_bv 64 a).
Proof.
  intros L A mem md HM a Hso Ha Hro.
  pose proof FF as (HS & _ & _ & _ & _ & _ & HGUA & HGOT & _ & HLCK & HLIBC & HSCL & HSMC & HMDC & HDBR & _ & _ & _
    & HVML & HDBL & _).
  assert (Hrw : forall x, (0x95878 <= x < 0x95910 \/ 0x208d8 <= x < 0x208e0) ->
    Mem.ro_addr (ms_segs B) (Z_to_bv 64 x) = false).
  { intros x Hx. rewrite HS. exact (en_so_rw x Hx). }
  unfold static_owned in Hso.
  destruct Hso as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]];
    [ | | | | | | apply (ax_tables AX L A mem md a HM); tauto
    | apply (ax_tables AX L A mem md a HM); tauto
    | apply (ax_tables AX L A mem md a HM); tauto
    | apply (ax_tables AX L A mem md a HM); tauto | ];
    first [ unfold vml_lo, vml_len in H; rewrite HVML in H; lia
          | exfalso; rewrite (Hrw a) in Hro; [discriminate Hro|];
            rewrite ?HLCK, ?HLIBC, ?HGOT, ?HGUA in H; lia ].
Qed.

Lemma len_ro_agree : forall g, LGV B API g -> MemNorm.ro_agree rsegs (lg_mem g).
Proof.
  intros g ((Hpre & _) & _). pose proof Hpre as (HM & _).
  rewrite <- (lff_segs B API FF).
  apply (ro_agree_of_rodata_ok B (lg_mem g)); [| exact (len_tbl _ _ _ _ HM)].
  unfold lib_pre in Hpre.
  repeat match type of Hpre with _ /\ ?R => destruct Hpre as [_ Hpre] end. exact Hpre.
Qed.

(* S-FR item 2 at ENTRY (boxreg lf_fr_init) *)
Lemma lfr_init : forall g, LGV B API g -> LFR B API g [] (lg_T g) (lg_L g) (lg_A g) (lg_mem g) (lg_md g).
Proof.
  intros g HV. pose proof (len_ro_agree g HV) as Hro.
  pose proof HV as ((Hpre & _ & _ & Hres & _) & (Hmf & _) & _).
  destruct Hpre as (HM & HW & HB & HID & _ & _ & _ & _ & Hstw & _ & Herr & _).
  split; [exact HV|]. split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact HID|].
  split; [exists (m_vmmaps (lg_md g)); apply with_vmmaps_self|].
  split; [intros a _ _; split; [reflexivity | tauto]|].
  split; [intros a _ _; split; [reflexivity | tauto]|].
  split; [intros a k i _ _ _; reflexivity|].
  split; [exact Hstw|]. split; [exact Herr|]. split; [intros i _; reflexivity|].
  split; [rewrite (lff_segs B API FF); exact Hro|].
  split; [rewrite sb_hb_nil; exact Hres|].
  split; [apply Permutation_refl|].
  split; [|exact Hmf].
  unfold lkept. destruct (lg_T g) as [|t T'];
    [right; split; [reflexivity | left; reflexivity] | left; split; [discriminate | reflexivity]].
Qed.

Lemma len_ghost_ok : forall g, LGV B API g -> len_ghost g.
Proof.
  intros g ((Hpre & Hn & _ & Hres & Hroom & _ & _ & _ & _ & Hsp47) & _).
  destruct Hpre as (HM & HW & _ & _ & _ & Hal & Hceil & _ & _ & _ & _ & _ & _ & Hcase & _).
  pose proof (@alloc_ceiling_value rc) as [[AC _] _].
  pose proof (@alloc_ceiling_lt rc) as ACL.
  cbn [lib_room mf_shape] in Hroom. destruct Hroom as (_ & HBy & _).
  unfold len_ghost, lg_S. unfold SLOT_STACK in Hceil.
  split; [exact Hal|]. split; [unfold SLOT_STACK_Z; lia|]. split; [exact Hsp47|]. split; [exact Hn|].
  destruct Hcase as [(Hn0 & _) | (Hn0 & q & Hq & Hp)]; [split; [lia | intros H; lia]|].
  destruct Hres as (_ & _ & _ & _ & _ & _ & _ & Hub & _).
  pose proof (ub_le_ubytes (lg_A g) q (lg_n g) HW Hq) as Hle.
  destruct (mr_blocks_range B (aa_MR API) (aa_laws API) (lg_L g) (lg_A g) (lg_mem g) (lg_md g) q (lg_n g) HM Hq)
    as [HR1 HR2].
  rewrite Hp in HR1, HR2.
  split; [lia|]. intros _. split; [apply len_p0_eq; lia|].
  split; [exact HR1|]. split; [unfold SLOT_STACK_Z; lia|].
  intros i Hi s Hs Hr. apply (ax_blocks_img AX (lg_L g) (lg_A g) (lg_mem g) (lg_md g) q (lg_n g) i HM Hq Hi).
  rewrite Hp. split; [rewrite (lff_segs B API FF); exact lfr_rsegs_nonnil|].
  exists s. split; [rewrite (lff_segs B API FF); exact Hs | exact Hr].
Qed.

Lemma len_guard : forall L A m md, aa_MR API L A m md -> MemNorm.ro_agree rsegs m -> guard_m (normalize_cj rsegs m).
Proof.
  intros L A m md HM Hro.
  destruct (ax_statics AX L A m md HM) as (Hgot & (gv & Hgv & Hgd) & _).
  rewrite (lff_segs B API FF), (lff_got B API FF), (lff_guard B API FF) in *.
  split.
  - apply (bytes_at_normalize_cj_low rsegs m _ _ Hro);
      [rewrite Mem.length_le8; unfold A_GOT_GUARD_S, TASK_SIZE; lia|].
    apply (en_word_mem_le8 m A_GOT_GUARD_S A_GUARD_S Hgot);
      unfold A_GUARD_S, A_GOT_GUARD_S; lia.
  - exists (wz gv). apply (bytes_at_normalize_cj_low rsegs m _ _ Hro);
      [rewrite Mem.length_le8; unfold A_GUARD_S, TASK_SIZE; lia|].
    apply (en_word_mem_le8 m A_GUARD_S gv Hgd); unfold A_GUARD_S; lia.
Qed.

Lemma len_mem_ok : forall g, LGV B API g -> len_mem g (normalize_cj rsegs (lg_mem g)).
Proof.
  intros g HV. pose proof (len_ro_agree g HV) as Hro. pose proof (len_ghost_ok g HV) as HGh.
  pose proof HV as ((Hpre & Hn & Hblk & _) & (_ & Hnul) & _ & _ & HGimg & _).
  destruct Hpre as (HM & _ & _ & _ & _ & _ & Hceil & _ & Hstw & _ & _ & _ & _ & Hcase & _).
  rewrite (lff_segs B API FF) in HGimg, Hstw.
  pose proof (@alloc_ceiling_value rc) as [[AC _] _]. pose proof (@alloc_ceiling_lt rc) as ACL.
  destruct HGh as (_ & HS1 & HS2 & _ & _ & Hplace).
  set (m := normalize_cj rsegs (lg_mem g)).
  destruct (en_img (lg_mem g) Hro HGimg) as (Hodd & Htexts & Hpol).
  split; [split; [split; [exact Hodd|]; split; [exact Htexts|]; split; [exact Hpol|];
                  exact (len_guard _ _ _ _ HM Hro)|]|].
  - split.
    { (* la_ok *)
      exists (rd_list m A_LONG_ALIAS 300), (rd_list m (A_LONG_ALIAS + LONG_ALIAS_SIZE) 3).
      assert (HB : forall a, A_LONG_ALIAS <= a < A_LONG_ALIAS + LONG_ALIAS_SIZE + 3 -> en_chk a = true).
      { intros a Ha. apply en_bss. unfold EN_BSS_LEN, A_LONG_ALIAS, A_G_NL, LONG_ALIAS_SIZE, NK_SIZE, G_NAMES_SIZE in *. lia. }
      assert (Z300 : Z.of_nat 300 = 300) by reflexivity. assert (Z3 : Z.of_nat 3 = 3) by reflexivity.
      unfold A_LONG_ALIAS, LONG_ALIAS_SIZE in *.
      split; [split; [split|]|].
      - cbn [Cells.cells_wf Cells.cell_wf]. split; [apply rd_list_length | split; exact I].
      - cbn [Cells.cells_bytes Cells.cbytes]. rewrite app_nil_r. apply Mem.bytes_at_app. split.
        + apply en_rd; [lia | rewrite Z300; lia |].
          intros a Ha. apply HB. rewrite Z300 in Ha. lia.
        + rewrite rd_list_length, Z300.
          apply (bytes_at_normalize_cj_low rsegs (lg_mem g) _ _ Hro); [cbn [length Z.of_nat]; unfold TASK_SIZE; lia|].
          exact Hnul.
      - cbn [Cells.cells_size Cells.csize]. apply en_wr; [lia | lia |].
        intros a Ha. apply HB. lia.
      - split; [|apply rd_list_length]. apply en_rd; [lia | rewrite Z3; lia |].
        intros a Ha. apply HB. rewrite Z3 in Ha. lia. }
    split.
    { (* the payload *)
      destruct Hcase as [(Hn0 & _) | (Hn0 & q & Hq & Hp)].
      - assert (Epl : lg_pl g = []) by (destruct (lg_pl g); [reflexivity | cbn in Hn; lia]).
        rewrite Epl. apply Mem.bytes_at_nil. pose proof (bv_unsigned_in_range 64 (wz (lg_p g))) as R.
        unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R. unfold len_p0. lia.
      - destruct (Hplace Hn0) as (Ep & HB1 & HB2 & _). rewrite Ep.
        apply (bytes_at_normalize_cj_low rsegs (lg_mem g) _ _ Hro);
          [unfold SLOT_STACK_Z, TASK_SIZE in *; lia|].
        split; [lia|]. split; [unfold SLOT_STACK_Z in *; lia|].
        intros i Hi. pose proof (Hblk (Z.of_nat i) ltac:(lia)) as E. cbv zeta in E.
        rewrite (lff_segs B API FF), Nat2Z.id in E. exact E. }
    split; [apply en_wr; [unfold A_ERRNO, A_TP, ERRNO_TP_OFF; lia | unfold A_ERRNO, A_TP, ERRNO_TP_OFF; lia
           | exact en_errno]|].
    split; [exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs (lg_mem g)))|].
    exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs (lg_mem g))).
  - split; [apply en_rw_cb; [unfold A_G_NL; lia | unfold NK_SIZE; lia | unfold A_G_NL, NK_SIZE; lia |];
            intros a Ha; apply en_bss; unfold EN_BSS_LEN, NK_SIZE, G_NAMES_SIZE, LONG_ALIAS_SIZE in *; lia|].
    split; [apply en_rw_cb; [unfold A_G_NAMES; lia | unfold G_NAMES_SIZE; lia | unfold A_G_NAMES, G_NAMES_SIZE; lia |];
            intros a Ha; apply en_bss;
            unfold EN_BSS_LEN, A_G_NL, A_G_NAMES, NK_SIZE, G_NAMES_SIZE, LONG_ALIAS_SIZE in *; lia|].
    unfold SLOT_STACK in Hceil. unfold SLOT_STACK_Z in *. change (spZ (lg_regs g)) with (lg_S g) in Hceil.
    apply lfr_stk; [unfold LF_TOP; lia | lia |].
    intros a Ha. unfold writable_at, m. change (Z_to_bv 64 a) with (wa a).
    rewrite (en_wv (lg_mem g) a ltac:(unfold TASK_SIZE; lia) (en_hi_ro a ltac:(unfold LF_TOP; lia))).
    exact (Hstw a Ha).
Qed.

(* S-FR item 8: the config at ENTRY is the entry cut *)
Lemma cut_entry : forall g (fx' : YK11.FPState),
  LGV B API g -> frm_zero (@fp_csr fx') ->
  CUT B API g L_ENTRY [] (lg_T g) (lentry_ms g)
    (mkCfg (@YK11.mkst fx' (lg_regs g) (Z_to_bv 64 L_ENTRY) (lg_mem g) (seg_rom (ms_segs B))) (lg_md g)).
Proof.
  intros g fx' HV Hf.
  apply (cut_close B API fx' g L_ENTRY [] (lg_T g) (lentry_ms g) (lg_L g) (lg_A g) (lg_regs g) (lg_mem g)
           (lg_md g) Hf (lfr_init g HV)).
  pose proof HV as ((Hpre & _) & _).
  destruct Hpre as (_ & _ & _ & _ & Hra & _ & _ & _ & _ & Htp & _ & Hp & Hn & _).
  rewrite (lff_tp B API FF) in Htp.
  set (R0 := lg_regs g).
  assert (XE : Regs6ss.xregs_eqv R0
    (mkR (wz (lg_ra g)) (wz (lg_S g)) (getr R0 3) (wz A_TP) (getr R0 5) (getr R0 6) (getr R0 7)
         (getr R0 8) (getr R0 9) (wz (len_p0 g)) (wz (lg_n g))
         (getr R0 12) (getr R0 13) (getr R0 14) (getr R0 15) (getr R0 16) (getr R0 17) (getr R0 18)
         (getr R0 19) (getr R0 20) (getr R0 21) (getr R0 22) (getr R0 23) (getr R0 24) (getr R0 25)
         (getr R0 26) (getr R0 27) (getr R0 28) (getr R0 29) (getr R0 30) (getr R0 31))).
  { apply Regs6ss.mkR_eqv_of;
      first [ exact Hra | exact Htp | exact Hn
            | unfold wz, len_p0; rewrite Z_to_bv_bv_unsigned; exact Hp
            | unfold wz, lg_S, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
            | reflexivity ]. }
  exists (MS (mkR (wz (lg_ra g)) (wz (lg_S g)) (getr R0 3) (wz A_TP) (getr R0 5) (getr R0 6) (getr R0 7)
         (getr R0 8) (getr R0 9) (wz (len_p0 g)) (wz (lg_n g))
         (getr R0 12) (getr R0 13) (getr R0 14) (getr R0 15) (getr R0 16) (getr R0 17) (getr R0 18)
         (getr R0 19) (getr R0 20) (getr R0 21) (getr R0 22) (getr R0 23) (getr R0 24) (getr R0 25)
         (getr R0 26) (getr R0 27) (getr R0 28) (getr R0 29) (getr R0 30) (getr R0 31))
             (@fp_regs fx') (wz L_ENTRY) (@fp_csr fx') None (normalize_cj rsegs (lg_mem g)) (seg_rom rsegs)).
  split.
  - exists (@fp_regs fx'), (@fp_csr fx'), (normalize_cj rsegs (lg_mem g)).
    split; [reflexivity|]. split; [exact Hf|]. split; [exact (len_ghost_ok g HV) | exact (len_mem_ok g HV)].
  - unfold Regs6ss.ms_eqv, lcanon. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS].
    split; [exact (Regs6ss.xregs_eqv_sym _ _ XE)|]. repeat split.
Qed.

End EN.
