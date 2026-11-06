From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK14 YP09 YO0i YO0f YO0d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import AllocSI AllocGS.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecInv RecInvP snprintf_c.
Import ListNotations.
Local Open Scope Z_scope.

Section Home.
Variable B : malloc_syms.

Definition str_home (L : layout) (A : astate) (sp s n : Z) : Prop :=
  (sp <= s /\ s + n <= 2 ^ 64) \/
  (exists q k, In (q, k) (blocks L A) /\ q <= s /\ s + n <= q + k) \/
  (0 <= s /\ s + n <= 2 ^ 64 /\ forall i, 0 <= i < n -> ro_addr (ms_segs B) (Z_to_bv 64 (s + i)) = true).

Definition buf_home (L : layout) (A : astate) (O : list (Z * Z)) (sp s n : Z) : Prop :=
  (sp <= s /\ s + n <= 2 ^ 64) \/
  (exists q k, In (q, k) (blocks L A) /\ ~ In q (map fst O) /\ q <= s /\ s + n <= q + k) \/
  (0 <= s /\ s + n <= 2 ^ 64 /\ forall i, 0 <= i < n -> ro_addr (ms_segs B) (Z_to_bv 64 (s + i)) = true).

End Home.

Definition rec_area (a : Z) : Prop := REC_SC <= a < REC_SC + SC_SIZE \/ G_REC <= a < G_REC + REC_SIZE.

Definition f18_words (segs : list Segment) (mem : word -> option byte) : Prop :=
  rw_cells segs mem GOT_GUARD [C8 (Z_to_bv 64 GUARD)] /\ exists canary, rw_cells segs mem GUARD [C8 canary].

Definition fs_saved (r : Z) : Prop := r = 8 \/ r = 9 \/ (18 <= r <= 27).

Definition fp_kept (fx fx' : FPState) : Prop :=
  frm_zero (@fp_csr fx') /\
  forall r, fs_saved r -> reg_get (@fp_regs fx') (Z_to_bv 5 r) = reg_get (@fp_regs fx) (Z_to_bv 5 r).

Definition others_kept (segs : list Segment) (L : layout) (A : astate) (mem : word -> option byte)
    (L' : layout) (A' : astate) (mem' : word -> option byte) (O : list (Z * Z)) : Prop :=
  forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
    In (p, k) (user_blocks A') /\ ptr_addr L' p = ptr_addr L p /\
    forall i, 0 <= i < k -> mbyte segs mem' (ptr_addr L p + i) = mbyte segs mem (ptr_addr L p + i).

Definition owns_new (L : layout) (A : astate) (O O' : list (Z * Z)) : Prop :=
  forall pn, In pn O' -> In pn O \/ ~ In pn (blocks L A).

Section PostRec.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable MR : MR_t.

Definition call_post_rec (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (E excl : Z -> Prop)
    (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\ layout_le A L L' /\
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> ptr_addr L' p = ptr_addr L p) /\
  regs_preserved regs regs' /\
  (exists vm', md' = with_vmmaps vm' md) /\
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) ->
     ~ owned B L A a -> ~ owned B L' A' a -> ~ scratch_k B stk regs a -> ~ E a ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
     (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) /\
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> ~ excl (ptr_addr L p) -> 0 <= i < n ->
     mbyte (ms_segs B) mem' (ptr_addr L p + i) = mbyte (ms_segs B) mem (ptr_addr L p + i)) /\
  (forall a, scratch_k B stk regs a -> writable_at (ms_segs B) mem' a).

End PostRec.

Definition sb_le (b b' : sbound) : Prop :=
  sb_live b <= sb_live b' /\ sb_bytes b <= sb_bytes b' /\ sb_cap b = sb_cap b'.

Lemma sb_le_refl b : sb_le b b.
Proof. unfold sb_le. lia. Qed.

Lemma sb_le_trans b1 b2 b3 : sb_le b1 b2 -> sb_le b2 b3 -> sb_le b1 b3.
Proof. unfold sb_le. lia. Qed.

Lemma sb_le_malloc b n : 0 <= n -> sb_le b (sb_malloc b n).
Proof. unfold sb_le, sb_malloc. cbn. lia. Qed.

Lemma sb_free_le b n : 0 <= n -> sb_le (sb_free b n) b.
Proof. unfold sb_le, sb_free. cbn. lia. Qed.

Lemma sb_malloc_mono b b' n : sb_le b b' -> sb_le (sb_malloc b n) (sb_malloc b' n).
Proof. unfold sb_le, sb_malloc. cbn. lia. Qed.

Lemma sb_free_mono b b' n : sb_le b b' -> sb_le (sb_free b n) (sb_free b' n).
Proof. unfold sb_le, sb_free. cbn. lia. Qed.

Lemma res_ok_slots_le : forall A b b', sb_le b b' -> sb_live b' <= sb_cap b' -> res_ok_slots A b -> res_ok_slots A b'.
Proof.
  unfold sb_le, res_ok_slots. intros A b b' (L1 & L2 & L3) HC
    (R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & (R8 & R9) & R10 & R11).
  rewrite <- L3. repeat (split; [assumption|]). repeat split; lia.
Qed.

Definition sb_shift (b : sbound) (A A' : astate) : sbound :=
  SB (sb_live b + (nblocks A' - nblocks A)) (sb_bytes b + (ubytes A' - ubytes A)) (sb_cap b).

Lemma sb_shift_refl b A : sb_shift b A A = b.
Proof. destruct b as [l y c]. unfold sb_shift. cbn. f_equal; lia. Qed.

Lemma sb_shift_trans b A A1 A2 : sb_shift (sb_shift b A A1) A1 A2 = sb_shift b A A2.
Proof. destruct b as [l y c]. unfold sb_shift. cbn. f_equal; lia. Qed.

Lemma bsum_app : forall (l1 l2 : list (Z * Z)),
  fold_right (fun b acc => snd b + acc) 0 (l1 ++ l2) =
  fold_right (fun b acc => snd b + acc) 0 l1 + fold_right (fun b acc => snd b + acc) 0 l2.
Proof. induction l1 as [|x l1 IH]; intros l2; cbn; [lia|]. rewrite IH. lia. Qed.

Lemma blocks_counts : forall L A, nblocks A = Z.of_nat (length (blocks L A)) /\
  ubytes A = fold_right (fun b acc => snd b + acc) 0 (blocks L A).
Proof.
  intros L A. unfold nblocks, ubytes, blocks. rewrite length_map. split; [reflexivity|].
  induction (user_blocks A) as [|x l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma sb_shift_add : forall b L A L' A' l1 l2 p n,
  blocks L' A' = l1 ++ (p, n) :: l2 -> blocks L A = l1 ++ l2 -> sb_malloc b n = sb_shift b A A'.
Proof.
  intros b L A L' A' l1 l2 p n E1 E2.
  destruct (blocks_counts L A) as (N0 & U0). destruct (blocks_counts L' A') as (N1 & U1).
  rewrite E2 in N0, U0. rewrite E1 in N1, U1. rewrite bsum_app in U0, U1. cbn in U1.
  rewrite length_app in N0, N1. cbn [length] in N1.
  destruct b as [l y c]. unfold sb_shift, sb_malloc. cbn. f_equal; lia.
Qed.

Lemma sb_shift_del : forall b L A L' A' l1 l2 p n,
  blocks L A = l1 ++ (p, n) :: l2 -> blocks L' A' = l1 ++ l2 -> sb_free b n = sb_shift b A A'.
Proof.
  intros b L A L' A' l1 l2 p n E1 E2.
  destruct (blocks_counts L A) as (N0 & U0). destruct (blocks_counts L' A') as (N1 & U1).
  rewrite E1 in N0, U0. rewrite E2 in N1, U1. rewrite bsum_app in U0, U1. cbn in U0.
  rewrite length_app in N0, N1. cbn [length] in N0.
  destruct b as [l y c]. unfold sb_shift, sb_free. cbn. f_equal; lia.
Qed.

Lemma sb_shift_same : forall b L A L' A', blocks L' A' = blocks L A -> sb_shift b A A' = b.
Proof.
  intros b L A L' A' E.
  destruct (blocks_counts L A) as (N0 & U0). destruct (blocks_counts L' A') as (N1 & U1).
  rewrite E in N1, U1. destruct b as [l y c]. unfold sb_shift. cbn. f_equal; lia.
Qed.

Lemma sb_shift_perm : forall b L A L' A', Permutation (blocks L' A') (blocks L A) -> sb_shift b A A' = b.
Proof.
  intros b L A L' A' P.
  destruct (blocks_counts L A) as (N0 & U0). destruct (blocks_counts L' A') as (N1 & U1).
  rewrite (Permutation_length P) in N1.
  assert (S : forall l l' : list (Z * Z), Permutation l l' ->
    fold_right (fun b acc => snd b + acc) 0 l = fold_right (fun b acc => snd b + acc) 0 l').
  { intros l l' Q. induction Q; cbn; lia. }
  rewrite (S _ _ P) in U1. destruct b as [l y c]. unfold sb_shift. cbn. f_equal; lia.
Qed.

Definition sb_mallocs (b : sbound) (ns : list Z) : sbound := fold_left sb_malloc ns b.

Section Args.
Variable B : malloc_syms.

Definition str_arg (L : layout) (A : astate) (O : list (Z * Z)) (sp K : Z) (mem : word -> option byte)
    (p : Z) (v : option (list byte)) : Prop :=
  match v with
  | None => p = 0
  | Some x =>
      p <> 0 /\ no0 x /\ Z.of_nat (length x) <= LMAX /\
      exists slack, bytes_at (ms_segs B) mem p (x ++ Z_to_bv 8 0 :: slack) /\
        (- (p + Z.of_nat (length x) + 1)) mod 8 <= Z.of_nat (length slack) /\
        (p + Z.of_nat (length (x ++ Z_to_bv 8 0 :: slack)) <= sp - K \/ sp <= p) /\
        buf_home B L A O sp p (Z.of_nat (length x) + 1) /\
        (forall a, p <= a < p + Z.of_nat (length (x ++ Z_to_bv 8 0 :: slack)) -> ~ rec_area a)
  end.

End Args.

Lemma room_slots_mono : forall b b' n n', sb_le b b' -> 0 <= n <= n' -> room_slots b' n' -> room_slots b n.
Proof.
  unfold sb_le, room_slots. intros b b' n n' (L1 & L2 & L3) Hn (R0 & R1 & R2).
  split; [lia|]. split; [lia|]. rewrite L3.
  eapply CAPOK_mono; [| | | exact R2]; lia.
Qed.

Lemma room_slots_malloc : forall b n, 0 <= n -> room_slots (sb_malloc b n) n -> room_slots b n.
Proof. intros b n Hn H. exact (room_slots_mono b (sb_malloc b n) n n (sb_le_malloc b n Hn) ltac:(lia) H). Qed.

Lemma mbyte_of_bytes_at : forall segs m a bs i, bytes_at segs m a bs -> (i < length bs)%nat ->
  mbyte segs m (a + Z.of_nat i) = nth_error bs i.
Proof. intros segs m a bs i (_ & _ & H) Hi. exact (H i Hi). Qed.

Lemma bytes_at_transfer : forall segs m m' a bs, bytes_at segs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs m' (a + i) = mbyte segs m (a + i)) ->
  bytes_at segs m' a bs.
Proof.
  intros segs m m' a bs (H1 & H2 & H) E. split; [exact H1|]. split; [exact H2|].
  intros i Hi. change (mbyte segs m' (a + Z.of_nat i) = nth_error bs i).
  rewrite E by lia. exact (H i Hi).
Qed.

Lemma rw_cells_transfer : forall segs m m' a cs, rw_cells segs m a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> mbyte segs m' (a + i) = mbyte segs m (a + i) /\
     (writable_at segs m (a + i) -> writable_at segs m' (a + i))) ->
  rw_cells segs m' a cs.
Proof.
  intros segs m m' a cs [[Hwf Hb] (Ha & Hn & Hw)] E.
  pose proof (cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hwf|]|].
  - apply (bytes_at_transfer segs m); [exact Hb|]. intros i Hi. apply E. rewrite <- L. exact Hi.
  - split; [exact Ha|]. split; [exact Hn|]. intros i Hi. apply (proj2 (E i Hi)). exact (Hw i Hi).
Qed.

Lemma nth_error_seq_lt : forall s k i, (i < k)%nat -> nth_error (seq s k) i = Some (s + i)%nat.
Proof.
  intros s k. revert s. induction k as [|k IH]; intros s i Hi; [lia|].
  destruct i as [|i]; cbn; [f_equal; lia|]. rewrite IH by lia. f_equal. lia.
Qed.

Lemma present_rw_cells : forall segs m a (k : nat), 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
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
    rewrite (map_nth_error _ _ _ (nth_error_seq_lt 0 k i Hi)). cbn [Nat.add].
    unfold mrd. unfold wa. rewrite E. reflexivity.
  - split; [exact Ha|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    destruct (H i ltac:(lia)) as [b E]. unfold wview, wa. rewrite E. discriminate.
Qed.

Lemma present_writable : forall segs m a, present m a -> writable_at segs m a.
Proof. intros segs m a [b E]. unfold writable_at, wview. rewrite E. discriminate. Qed.

Lemma word_mem_munch : forall segs W m m' a v, munch W m m' ->
  (forall k, (k < 8)%nat -> 0 <= a + Z.of_nat k < 2 ^ 64 /\ outside W (a + Z.of_nat k)) ->
  word_mem segs m a v -> word_mem segs m' a v.
Proof.
  intros segs W m m' a v H R Wm k Hk. destruct (R k Hk) as [R1 R2]. unfold mbyte.
  rewrite (H (Z_to_bv 64 (a + Z.of_nat k))); [exact (Wm k Hk)|]. rewrite unsigned_lit by exact R1. exact R2.
Qed.

Lemma munch_mbyte : forall segs W m m' a, munch W m m' -> 0 <= a < 2 ^ 64 -> outside W a ->
  mbyte segs m' a = mbyte segs m a.
Proof.
  intros segs W m m' a H R O. unfold mbyte. rewrite (H (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit by exact R. exact O.
Qed.

Lemma munch_writable : forall segs W m m' a, munch W m m' -> 0 <= a < 2 ^ 64 -> outside W a ->
  (writable_at segs m a <-> writable_at segs m' a).
Proof.
  intros segs W m m' a H R O. unfold writable_at, wview. rewrite (H (Z_to_bv 64 a)); [tauto|].
  rewrite unsigned_lit by exact R. exact O.
Qed.

Lemma munch_present : forall W m m' a, munch W m m' -> 0 <= a < 2 ^ 64 -> outside W a ->
  present m a -> present m' a.
Proof.
  intros W m m' a H R O [b E]. exists b. rewrite (H (Z_to_bv 64 a)); [exact E|].
  rewrite unsigned_lit by exact R. exact O.
Qed.

Lemma outside_one : forall lo hi a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> outside [(lo, hi)] a.
Proof. intros lo hi a R H. cbn. split; [exact H | exact I]. Qed.

Lemma mbyte_ro : forall segs m a, mem_inv segs m -> ro_addr segs (Z_to_bv 64 a) = true ->
  mbyte segs m a = seg_rom segs (Z_to_bv 64 a).
Proof.
  intros segs m a MI RO. unfold mbyte. destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [|reflexivity].
  exfalso. rewrite (MI _ _ E) in RO. discriminate.
Qed.

Lemma ro_not_writable : forall segs m a, mem_inv segs m -> ro_addr segs (Z_to_bv 64 a) = true ->
  ~ writable_at segs m a.
Proof.
  intros segs m a MI RO. unfold writable_at, wview.
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:E.
  - rewrite (MI _ _ E) in RO. discriminate.
  - revert RO. unfold ro_addr.
    destruct (find_segment segs (bv_unsigned (Z_to_bv 64 a)) 1) as [seg|]; [|discriminate].
    destruct (seg_writable seg); [discriminate|]. intros _ W. apply W. reflexivity.
Qed.

Lemma find_segment_none_above : forall segs top a n,
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs = true -> top <= a -> 0 < n ->
  find_segment segs a n = None.
Proof.
  induction segs as [|s segs IH]; intros top a n H Ha Hn; cbn [find_segment]; [reflexivity|].
  cbn [forallb] in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
  match goal with |- context [if ?c then _ else _] => destruct c eqn:E end.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - apply IH with top; assumption.
Qed.

Lemma find_segment_in : forall segs a n seg, find_segment segs a n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|s segs IH]; intros a n seg H; cbn [find_segment] in H; [discriminate|].
  match type of H with context [if ?c then _ else _] => destruct c eqn:E end.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity|]. lia.
  - destruct (IH a n seg H) as (Hi & H1 & H2). split; [right; exact Hi|]. lia.
Qed.

Lemma rsegs_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 2 ^ 20) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rsegs_res_top :
  forallb (fun s => bv_unsigned (fst s) + bv_unsigned (snd s) <=? 2 ^ 21) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma writable_hi_present : forall m a, 2 ^ 20 <= a < 2 ^ 64 -> writable_at rsegs m a -> present m a.
Proof.
  intros m a Ha. unfold writable_at, wview, present.
  destruct (m (Z_to_bv 64 a)) as [b|]; [intros _; exists b; reflexivity|].
  rewrite unsigned_lit by lia.
  rewrite (find_segment_none_above rsegs (2 ^ 20) a 1 rsegs_top) by lia.
  intros W. exfalso. apply W. reflexivity.
Qed.

Lemma ret_pc_of_ok : forall k, YK0s.ret_ok k -> ret_pc k = k.
Proof.
  intros k H. unfold YK0s.ret_ok, v_jalr, jalr_tgtZ in H. rewrite Z.add_0_r in H.
  pose proof (bv_unsigned_in_range 64 k) as R. unfold bv_modulus in R.
  assert (T : Z.testbit (bv_unsigned k) 0 = false).
  { rewrite <- H at 1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Z.mod_pow2_bits_low by lia. rewrite Z.land_spec. apply Bool.andb_false_r. }
  assert (E : bv_unsigned k mod 2 = 0) by (rewrite Zmod_odd, <- Z.bit0_odd, T; reflexivity).
  rewrite <- (Z_to_bv_bv_unsigned k). apply ret_pc_even; [exact R | exact E].
Qed.

Section Img.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Hypothesis SEGS : ms_segs B = rsegs.

Lemma in_img_of_seg : forall a seg, 0 <= a -> find_segment rsegs a 1 = Some seg -> in_img B a.
Proof using SEGS.
  intros a seg Ha F. destruct (find_segment_in _ _ _ _ F) as (Hin & H1 & H2).
  pose proof (proj1 (forallb_forall _ rsegs) rsegs_top seg Hin) as T. apply Z.leb_le in T.
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

Lemma in_img_low : forall a, in_img B a -> 0 <= a < 2 ^ 21.
Proof using SEGS.
  intros a (_ & s & Hin & H1 & H2). rewrite SEGS in Hin.
  pose proof (proj1 (forallb_forall _ _) rsegs_res_top s Hin) as T. apply Z.leb_le in T.
  pose proof (bv_unsigned_in_range 64 (fst s)). lia.
Qed.

Lemma present_of_writable_out : forall m a, 0 <= a < 2 ^ 64 -> ~ in_img B a -> writable_at rsegs m a -> present m a.
Proof using SEGS.
  intros m a Ha NI. unfold writable_at, wview, present.
  destruct (m (Z_to_bv 64 a)) as [b|]; [intros _; exists b; reflexivity|].
  rewrite unsigned_lit by lia.
  destruct (find_segment rsegs a 1) as [seg|] eqn:F.
  - exfalso. apply NI. eapply in_img_of_seg; [lia | exact F].
  - intros W. exfalso. apply W. reflexivity.
Qed.

Lemma ro_in_img : forall a, 0 <= a < 2 ^ 64 -> ro_addr rsegs (Z_to_bv 64 a) = true -> in_img B a.
Proof using SEGS.
  intros a Ha H. unfold ro_addr in H. rewrite unsigned_lit in H by lia.
  destruct (find_segment rsegs a 1) as [seg|] eqn:F; [|discriminate].
  eapply in_img_of_seg; [lia | exact F].
Qed.

Lemma ro_addr_out : forall a, 0 <= a < 2 ^ 64 -> ~ in_img B a -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof using SEGS.
  intros a Ha NI. destruct (ro_addr rsegs (Z_to_bv 64 a)) eqn:E; [|reflexivity].
  exfalso. exact (NI (ro_in_img a Ha E)).
Qed.

Lemma in_img_found : forall a, 0 <= a -> find_segment rsegs a 1 <> None -> in_img B a.
Proof using SEGS.
  intros a Ha F. destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|contradiction].
  exact (in_img_of_seg a seg Ha E).
Qed.

End Img.

Lemma ro_addr_hi : forall a, 2 ^ 20 <= a < 2 ^ 64 -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. unfold ro_addr. rewrite unsigned_lit by lia.
  rewrite (find_segment_none_above rsegs (2 ^ 20) a 1 rsegs_top) by lia. reflexivity.
Qed.

Lemma normalize_rw : forall segs m x, ro_addr segs x = false -> normalize segs m x = m x.
Proof. intros segs m x H. unfold normalize. rewrite H. reflexivity. Qed.

Lemma mbyte_ro_agree : forall segs m a, ro_agree segs m -> ro_addr segs (Z_to_bv 64 a) = true ->
  mbyte segs m a = seg_rom segs (Z_to_bv 64 a).
Proof. intros segs m a H E. exact (H _ E). Qed.

Lemma rw_cells_rel : forall segs m m0 a cs, mem_rel segs m m0 -> rw_cells segs m0 a cs -> rw_cells segs m a cs.
Proof.
  intros segs m m0 a cs HR [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - exact (proj2 (bytes_at_rel segs m m0 a _ HR) Hb).
  - exact (wr_at_rel segs m m0 a _ HR Hw).
Qed.

Lemma rw_cells_normalize : forall segs m a cs, ro_agree segs m -> rw_cells segs m a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ro_addr segs (wa (a + i)) = false) ->
  rw_cells segs (normalize segs m) a cs.
Proof.
  intros segs m a cs Hro [[Hwf Hb] Hw] Hra. split; [split; [exact Hwf|]|].
  - exact (bytes_at_normalize segs m a _ Hro Hb).
  - exact (wr_at_norm segs m (normalize segs m) a _ (mem_rel_normalize segs m Hro) Hw Hra).
Qed.

Lemma ms_rel_MS : forall segs s R F pc fc rv m0 ro, ms_rel segs s (MS R F pc fc rv m0 ro) ->
  s = MS R F pc fc rv (ms_mem s) ro /\ mem_rel segs (ms_mem s) m0.
Proof.
  intros segs [r f p sv rv' c mm o] R F pc fc rv m0 ro (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  cbn in *. subst. split; [reflexivity | exact H8].
Qed.

Lemma pairwise_app_mid' : forall {X} (R : X -> X -> Prop) b1 x b2 y,
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

Lemma block_facts : forall L A mem md q k i, MR L A mem md -> In (q, k) (blocks L A) -> 0 <= i < k ->
  present mem (q + i) /\ 4096 <= q /\ q + k <= alloc_ceiling /\ ~ owned B L A (q + i).
Proof using LAWS.
  intros L A mem md q k i HM Hin Hi. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp).
  cbn in E. injection E as <- <-. exact (mr_blocks B MR LAWS L A mem md p k' i HM Hp Hi).
Qed.

Lemma owned_low : forall L A mem md a, MR L A mem md -> owned B L A a -> 0 <= a < alloc_ceiling.
Proof using LAWS. intros L A mem md a HM Ho. exact (mr_owned_low B MR LAWS L A mem md a HM Ho). Qed.

Lemma blocks_mid_disjoint : forall L A mem md b1 b2 d n q k, MR L A mem md ->
  blocks L A = b1 ++ (d, n) :: b2 -> In (q, k) (b1 ++ b2) -> q + k <= d \/ d + n <= q.
Proof using LAWS.
  intros L A mem md b1 b2 d n q k HM E Hin.
  pose proof (mr_blocks_disjoint B MR LAWS L A mem md HM) as P. rewrite E in P.
  destruct (pairwise_app_mid' _ _ _ _ _ P Hin) as [D|D]; unfold ranges_disjoint in D; cbn in D; lia.
Qed.

End Laws.

Section Regs.
Context {fx : YK11.FPState}.

Lemma canon_mkst : forall regs pc mem rom,
  RegisterBridge.canonical_register_state (mkst regs pc mem rom) = MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem rom.
Proof. reflexivity. Qed.

Lemma eqv_mkst : forall R F pc fc m ro ms, Regs6ss.ms_eqv (MS R F pc fc None m ro) ms -> F = fp_regs -> fc = fp_csr ->
  exists R', ms = mkst R' pc m ro /\ Regs6ss.xregs_eqv R R'.
Proof.
  intros R F pc fc m ro [r f p sv rv c mm o] (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) -> ->.
  cbn in *. subst. exists r. split; [reflexivity | exact H1].
Qed.

Lemma getr_of_eqv : forall M R (r : bv 5), Regs6ss.xregs_eqv M R -> bv_eqb r 0 = false -> getr R r = reg_get M r.
Proof. intros M R r H NZ. unfold getr. rewrite NZ. symmetry. apply H. exact NZ. Qed.

Lemma preserved_chain : forall (own : Z -> bool) regs R1 R2 R3 M1 M3,
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
  rewrite (getr_of_eqv _ _ _ X3 NZ). unfold getr. rewrite NZ.
  destruct (own r) eqn:O; [exact (K2 r Hr O)|].
  destruct (K1 r Hr O) as [E1 E2]. rewrite E1, <- E2.
  pose proof (P r Hr) as E3. unfold getr in E3. rewrite NZ in E3. rewrite E3. symmetry. apply X1. exact NZ.
Qed.

End Regs.
