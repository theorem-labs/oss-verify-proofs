From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct PjIn ReaderRes PvDefs memcpy_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require MemNorm FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require SoftFloat FloatScan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require FmtFp_facts3.
Import ListNotations.
Open Scope Z_scope.

Lemma pvn_find_ro : forall (segs : list Segment) lo hi a,
  forallb (fun s => seg_writable s || ((lo <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? hi)))
    segs = true ->
  a < lo \/ hi <= a ->
  match find_segment segs a 1 with Some sg => negb (seg_writable sg) | None => false end = false.
Proof.
  induction segs as [|s segs IH]; intros lo hi a H Ha; cbn [find_segment]; [reflexivity|].
  cbn [forallb] in H. apply andb_prop in H as [H1 H2].
  destruct ((Z.of_N (seg_base s) <=? a) && (a + 1 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    destruct (seg_writable s) eqn:W; [reflexivity|]. cbn in H1.
    apply andb_prop in H1 as [H3 H4]. apply Z.leb_le in H3. apply Z.leb_le in H4. lia.
  - exact (IH lo hi a H2 Ha).
Qed.

Lemma pvn_rsegs_ro :
  forallb (fun s => seg_writable s || ((0x10000 <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x23000)))
    rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pvn_ro_out : forall a, 0 <= a < 2 ^ 64 -> a < 0x10000 \/ 0x23000 <= a -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha Hout. unfold ro_addr. rewrite unsigned_lit by lia.
  exact (pvn_find_ro rsegs 0x10000 0x23000 a pvn_rsegs_ro Hout).
Qed.

Lemma pvn_keep : forall a, 0 <= a < 2 ^ 47 -> a < 0x10000 \/ 0x23000 <= a -> MemNorm.cj_drop rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha Hout. apply MemNorm.cj_drop_false_intro; [apply pvn_ro_out; lia|].
  right. rewrite unsigned_lit by lia. unfold TASK_SIZE. lia.
Qed.

Lemma pvn_ro_agree_write : forall m a bs, MemNorm.ro_agree rsegs m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> ro_addr rsegs (Z_to_bv 64 (a + i)) = false) ->
  MemNorm.ro_agree rsegs (write_to_mem m (wa a) bs).
Proof.
  intros m a bs RO H0 H1 HR x Hx. specialize (RO x Hx). unfold mrd in *.
  rewrite (write_to_mem_spec bs m a x H0 H1).
  destruct (Z.leb a (bv_unsigned x) && Z.ltb (bv_unsigned x) (a + Z.of_nat (length bs)))%bool eqn:E; [|exact RO].
  exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  specialize (HR (bv_unsigned x - a) ltac:(lia)). replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in HR by lia.
  rewrite Z_to_bv_bv_unsigned in HR. congruence.
Qed.

Lemma pvn_ms_rel : forall s R F pc fc rv m0 ro, MemNorm.ms_rel rsegs s (MS R F pc fc rv m0 ro) ->
  exists m', s = MS R F pc fc rv m' ro /\ MemNorm.mem_rel rsegs m' m0.
Proof.
  intros [r f p sv rv' c mm o] R F pc fc rv m0 ro H. unfold MemNorm.ms_rel, MS in H. cbn in H.
  destruct H as (-> & -> & -> & -> & -> & -> & -> & H). exists mm. split; [reflexivity | exact H].
Qed.

Lemma pvn_ms_rel_cj : forall s R F pc fc rv m0 ro, MemNorm.ms_rel_cj rsegs s (MS R F pc fc rv m0 ro) ->
  exists m', s = MS R F pc fc rv m' ro /\ MemNorm.mem_rel_cj rsegs m' m0.
Proof.
  intros [r f p sv rv' c mm o] R F pc fc rv m0 ro H. unfold MemNorm.ms_rel_cj, MS in H. cbn in H.
  destruct H as (-> & -> & -> & -> & -> & -> & -> & H). exists mm. split; [reflexivity | exact H].
Qed.

Lemma pvn_rw_rel : forall m m0 A cs, MemNorm.mem_rel rsegs m m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
  - exact (proj2 (MemNorm.bytes_at_rel rsegs m m0 A _ HR) Hb).
  - exact (MemNorm.wr_at_rel rsegs m m0 A _ HR Hw).
Qed.

Lemma pvn_rw_rel_cj : forall m m0 A cs, MemNorm.mem_rel_cj rsegs m m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
  - exact (MemNorm.bytes_at_rel_cj rsegs m m0 A _ HR Hb).
  - exact (MemNorm.wr_at_rel_cj rsegs m m0 A _ HR Hw).
Qed.

Lemma pvn_rw_norm : forall m A cs, MemNorm.ro_agree rsegs m -> rw_cells rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ro_addr rsegs (Z_to_bv 64 (A + i)) = false) ->
  rw_cells rsegs (MemNorm.normalize rsegs m) A cs.
Proof.
  intros m A cs RO ((Hwf & Hb) & Hw) Hro. split; [split; [exact Hwf|]|].
  - exact (MemNorm.bytes_at_normalize rsegs m A _ RO Hb).
  - exact (MemNorm.wr_at_norm rsegs m (MemNorm.normalize rsegs m) A _ (MemNorm.mem_rel_normalize rsegs m RO) Hw Hro).
Qed.

Lemma pvn_rw_norm_cj : forall m A cs, MemNorm.ro_agree rsegs m -> rw_cells rsegs m A cs ->
  A + Z.of_nat (cells_size cs) <= TASK_SIZE ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> MemNorm.cj_drop rsegs (Z_to_bv 64 (A + i)) = false) ->
  rw_cells rsegs (MemNorm.normalize_cj rsegs m) A cs.
Proof.
  intros m A cs RO ((Hwf & Hb) & Hw) Ht Hk. split; [split; [exact Hwf|]|].
  - apply MemNorm.bytes_at_normalize_cj_low; [exact RO | | exact Hb].
    rewrite cells_bytes_length by exact Hwf. exact Ht.
  - exact (MemNorm.wr_at_norm_cj rsegs m (MemNorm.normalize_cj rsegs m) A _
             (MemNorm.mem_rel_cj_normalize rsegs m RO) Hw Hk).
Qed.

Lemma pvn_stk_norm_cj : forall m lo hi, stk rsegs m lo hi ->
  (forall a, lo <= a < hi -> MemNorm.cj_drop rsegs (Z_to_bv 64 a) = false) ->
  stk rsegs (MemNorm.normalize_cj rsegs m) lo hi.
Proof.
  intros m lo hi (H1 & H2 & H) Hk. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  assert (N : MemNorm.normalize_cj rsegs m (wa a) = m (wa a))
    by (unfold MemNorm.normalize_cj, wa; rewrite Hk by exact Ha; reflexivity).
  destruct (H a Ha) as [W [b E]]. split.
  - unfold wview in *. rewrite N. exact W.
  - exists b. unfold mrd in *. rewrite N. exact E.
Qed.

Lemma pvn_le_back : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  assert (Hn : 0 <= bytes_le_to_Z bs).
  { clear IH. induction bs as [|b' bs' IH']; cbn [bytes_le_to_Z]; [lia|].
    apply Z.lor_nonneg. split; [apply bv_unsigned_in_range | apply Z.shiftl_nonneg; exact IH']. }
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  rewrite (lor_shiftl8_add (bv_unsigned b) (bytes_le_to_Z bs)) by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by ring.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by ring.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. exact IH.
Qed.

Lemma pvn_le8_back : forall bs, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. rewrite <- store_bytes_8'. unfold le_bytes_to_word. rewrite unsigned_lit_wrap.
  rewrite (Z_to_le_bytes_mod 8 (bytes_le_to_Z bs) 64) by lia.
  rewrite <- L. apply pvn_le_back.
Qed.

Lemma pvn_stk_C8 : forall m a, stk rsegs m a (a + 8) -> exists w, rw_cells rsegs m a [C8 w].
Proof.
  intros m a ST. destruct (stk_bytes rsegs m a (a + 8) ST ltac:(lia)) as (bs & L & B).
  replace (Z.to_nat (a + 8 - a)) with 8%nat in L by lia.
  exists (le_bytes_to_word bs). split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r, pvn_le8_back by exact L. exact B.
  - cbn [cells_size csize]. destruct ST as (S1 & S2 & S3). split; [lia|]. split; [lia|].
    intros i Hi. apply (S3 (a + i)). lia.
Qed.

Lemma pvn_stk_wr : forall m lo hi, stk rsegs m lo hi -> lo <= hi -> wr_at rsegs m lo (hi - lo).
Proof. intros m lo hi (H1 & H2 & H) Hle. split; [lia|]. split; [lia|]. intros i Hi. apply (H (lo + i)). lia. Qed.

Lemma pvn_byte_rt : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma pvn_map_rt : forall bs : list byte, map (Z_to_bv 8) (map (fun b : byte => bv_unsigned b) bs) = bs.
Proof. induction bs as [|b bs IH]; cbn; [reflexivity|]. rewrite pvn_byte_rt, IH. reflexivity. Qed.

Lemma pvn_src : forall m (tb : list byte) text P txt r,
  bytes_at rsegs m text tb -> text <= P <= text + Z.of_nat (length tb) -> rest_at tb text P = txt ++ r ->
  bytes_at rsegs m P (map (Z_to_bv 8) txt).
Proof.
  intros m tb text P txt r B HP RA. unfold rest_at, zb in RA.
  set (k := Z.to_nat (P - text)) in *.
  rewrite <- (firstn_skipn k tb) in B. apply bytes_at_app in B as [_ B].
  rewrite length_firstn, Nat.min_l in B by lia. replace (text + Z.of_nat k) with P in B by lia.
  assert (S : skipn k tb = map (Z_to_bv 8) txt ++ map (Z_to_bv 8) r).
  { rewrite <- map_app, <- RA. symmetry. apply pvn_map_rt. }
  rewrite S in B. apply bytes_at_app in B as [B _]. exact B.
Qed.

Lemma pvn_numch_range : forall c, numch c = true -> 43 <= c <= 101.
Proof.
  intros c H. unfold numch, digit in H.
  destruct (Z.leb_spec 48 c), (Z.leb_spec c 57), (Z.eqb_spec c 46), (Z.eqb_spec c 101), (Z.eqb_spec c 69),
    (Z.eqb_spec c 43), (Z.eqb_spec c 45); cbn in H; try discriminate; lia.
Qed.

Lemma pvn_numch_is : forall c, numch c = true -> FmtFp_facts3.is_numch c = true.
Proof.
  intros c H. unfold numch, digit in H. unfold FmtFp_facts3.is_numch.
  destruct (48 <=? c), (c <=? 57), (c =? 46), (c =? 101), (c =? 69), (c =? 43), (c =? 45); cbn in *; congruence.
Qed.

Lemma pvn_fclass : forall x, (Z.land (fp_class fmt_double x) 897 =? 0) = finite x.
Proof.
  intros x. unfold fp_class, finite. cbv zeta.
  change (fp_exp_field fmt_double x) with (Z.land (Z.shiftr x 52) 2047).
  change (Z.ones (fp_ew fmt_double)) with 2047.
  destruct (Z.land (Z.shiftr x 52) 2047 =? 2047).
  - destruct (fp_man_field fmt_double x =? 0), (fp_sign_bit fmt_double x), (fp_is_snan fmt_double x); reflexivity.
  - destruct (Z.land (Z.shiftr x 52) 2047 =? 0), (fp_man_field fmt_double x =? 0), (fp_sign_bit fmt_double x);
      reflexivity.
Qed.

Ltac pvn_r64 :=
  lazymatch goal with
  | |- 0 <= Z.lor _ _ < 2 ^ 64 => apply Z_lor_range; pvn_r64
  | |- 0 <= Z.lxor _ _ < 2 ^ 64 => apply Z_lxor_range; pvn_r64
  | |- 0 <= Z.shiftr _ _ < 2 ^ 64 => apply Z_shiftr_range; [pvn_r64 | first [lia | apply Z.land_nonneg; right; lia]]
  | |- 0 <= Z.land _ _ < 2 ^ 64 =>
      apply land_lt_pow2; [pvn_r64 | let H := fresh in
        lazymatch goal with |- 0 <= ?y => assert (H : 0 <= y < 2 ^ 64) by pvn_r64; lia end]
  | |- 0 <= SoftFloat.wrap64 _ < 2 ^ 64 => apply SoftFloat.wrap64_range
  | |- 0 <= (if ?c then _ else _) < 2 ^ 64 => destruct c; pvn_r64
  | |- _ => lia
  end.

Lemma pvn_to_d_range : forall a, 0 <= SoftFloat.f128_to_d a < 2 ^ 64.
Proof.
  intros a. unfold SoftFloat.f128_to_d. cbv zeta.
  repeat match goal with |- context [if ?c then pair _ _ else _] => destruct c end;
  cbv iota beta;
  cbv beta delta [SoftFloat.shl64 SoftFloat.add64 SoftFloat.sub64 SoftFloat.lo64 SoftFloat.hi64 SoftFloat.trunc_round
    SoftFloat.nez64 SoftFloat.eqz64 SoftFloat.b2z SoftFloat.sra63 SoftFloat.zext32 SoftFloat.sext32 SoftFloat.DQUIET].
  all: pvn_r64.
Qed.

Lemma pvn_bits_range : forall txt bits c, strtod_c.strtod_model txt = Some (bits, c) -> 0 <= bits < 2 ^ 64.
Proof.
  intros txt bits c H. unfold strtod_c.strtod_model, FloatScan.scan_strtod in H.
  destruct (FloatScan.floatscan _ _ _ _) as [[f y]|]; [|discriminate].
  injection H as <- _. apply pvn_to_d_range.
Qed.

Lemma pvn_eqb0 : forall z, 0 <= z < 2 ^ 64 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = (z =? 0).
Proof. intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma pvn_split_CB : forall m A k bs, rw_cells rsegs m A [CB (S k) bs] ->
  rw_cells rsegs m A [CB k (firstn k bs)] /\ rw_cells rsegs m (A + Z.of_nat k) [CB 1 (skipn k bs)].
Proof.
  intros m A k bs ((Hwf & Hb) & (W1 & W2 & W3)). cbn in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes cells_size csize] in Hb, W2, W3. rewrite app_nil_r in Hb.
  rewrite <- (firstn_skipn k bs) in Hb. apply bytes_at_app in Hb as [Hb1 Hb2].
  rewrite length_firstn, Nat.min_l in Hb2 by lia.
  split.
  - split; [split|].
    + cbn. split; [rewrite length_firstn; lia | exact I].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb1.
    + cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. apply W3. lia.
  - split; [split|].
    + cbn. split; [rewrite length_skipn; lia | exact I].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb2.
    + cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat k + i) with (A + (Z.of_nat k + i)) by lia. apply W3. lia.
Qed.

Lemma pvn_gotg : forall m v, v mod 8 = 0 -> bytes_at rsegs m (v + 16) (le8 (Z_to_bv 64 0)) ->
  rw_cells rsegs m 144608 [C8 (Z_to_bv 64 346888)] -> v + 24 <= 144608 \/ 144608 + 8 <= v + 16.
Proof.
  intros m v Hv (_ & _ & B1) ((_ & (_ & _ & B2)) & _).
  destruct (Z.eq_dec (v + 16) 144608) as [E|E]; [|lia].
  exfalso. specialize (B1 0%nat ltac:(rewrite length_le8; lia)).
  specialize (B2 0%nat ltac:(cbn [cells_bytes cbytes]; rewrite length_app, length_le8; cbn; lia)).
  rewrite E in B1. rewrite B1 in B2. vm_compute in B2. discriminate.
Qed.

Lemma pvn_first1 : forall (l : list Z) k, (k < length l)%nat ->
  firstn 1 (skipn k (map (Z_to_bv 8) l)) = [Z_to_bv 8 (nth k l 0)].
Proof. induction l as [|x l IH]; intros [|k] Hk; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.

Lemma pvn_rd_byte : forall m a l c, bytes_at rsegs m a (map (Z_to_bv 8) l) -> 0 <= c < Z.of_nat (length l) ->
  ov_read_bytes rsegs m (wa (a + c)) 1 = Some [Z_to_bv 8 (nth (Z.to_nat c) l 0)].
Proof.
  intros m a l c B Hc. rewrite (bytes_at_read rsegs m a _ c 1 B) by (try rewrite length_map; lia).
  rewrite pvn_first1 by lia. reflexivity.
Qed.

Lemma pvn_hdr : forall m v ty bits res, v mod 8 = 0 -> stk rsegs m v (v + 56) -> 0 <= ty < 2 ^ 32 ->
  0 <= bits < 2 ^ 64 -> 0 <= res < 2 ^ 64 ->
  bytes_at rsegs m v (le4 (Z_to_bv 64 ty)) -> bytes_at rsegs m (v + 8) (le8 (Z_to_bv 64 bits)) ->
  bytes_at rsegs m (v + 16) (le8 (Z_to_bv 64 res)) -> bytes_at rsegs m (v + 24) (le8 (Z_to_bv 64 0)) ->
  bytes_at rsegs m (v + 32) (le8 (Z_to_bv 64 0)) -> bytes_at rsegs m (v + 40) (le8 (Z_to_bv 64 0)) ->
  bytes_at rsegs m (v + 48) (le8 (Z_to_bv 64 0)) -> pj_hdr rsegs m v ty bits res 0 0 0 0.
Proof.
  intros. unfold pj_hdr, pj_rw, pj_u32, pj_u64.
  refine (conj (conj _ _) (conj (conj _ _) (conj (conj _ _) (conj (conj _ _) (conj (conj _ _)
    (conj (conj _ _) (conj (conj _ _) (conj _ _)))))))); first [assumption | lia].
Qed.

Lemma pvn_zchunk : forall m v off, bytes_at rsegs m v (repeat (Z_to_bv 8 0) 56) -> 0 <= off -> off + 8 <= 56 ->
  bytes_at rsegs m (v + off) (le8 (Z_to_bv 64 0)).
Proof. intros m v off H H1 H2. rewrite pj_le8_0. apply pj_zero_sub; [exact H | lia | cbn; lia]. Qed.

Lemma pvn_zchunk4 : forall m v, bytes_at rsegs m v (repeat (Z_to_bv 8 0) 56) -> bytes_at rsegs m v (le4 (Z_to_bv 64 0)).
Proof.
  intros m v H. rewrite pj_le4_0. replace v with (v + 0) by lia. apply pj_zero_sub; [exact H | lia | cbn; lia].
Qed.

Lemma pvn_rd : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs B. rewrite <- (Z.add_0_r a) at 1. rewrite (bytes_at_read rsegs m a bs 0 (length bs) B) by lia.
  cbn [Z.to_nat skipn]. rewrite firstn_all. reflexivity.
Qed.

Lemma pvn_nth_end : forall (l : list Z), nth (length l) (l ++ [0]) 0 = 0.
Proof. intros l. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma pvn_nth_in : forall (l : list Z) k, (k < length l)%nat -> nth k (l ++ [0]) 0 = nth k l 0.
Proof. intros l k Hk. apply app_nth1. exact Hk. Qed.

Lemma pvn_nth_numch : forall l k, Forall (fun c => numch c = true) l -> (k < length l)%nat -> 43 <= nth k l 0 <= 101.
Proof. intros l k H Hk. apply pvn_numch_range. rewrite Forall_forall in H. apply H. apply nth_In. exact Hk. Qed.

Lemma pvn_fclass_range : forall x, 0 <= fp_class fmt_double x < 1024.
Proof.
  intros x. unfold fp_class. cbv zeta.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; rewrite ?Z.shiftl_1_l; lia.
Qed.

Lemma pvn_zxb_nz : forall t, 1 <= t < 256 -> bv_eqb (zxb (Z_to_bv 8 t)) (Z_to_bv 64 0) = false.
Proof.
  intros t Ht. unfold bv_eqb, zxb.
  assert (E : bv_unsigned (Z_to_bv 8 t) = t) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; cbn; lia).
  rewrite E, !unsigned_lit by lia. apply Z.eqb_neq. lia.
Qed.

Definition pvn_hide (P : Prop) : Prop := P.

Ltac pvn_hide_all := repeat match goal with H : ?A \/ ?B |- _ => change (pvn_hide (A \/ B)) in H end.

Ltac dlia :=
  first [ lia
        | match goal with H : pvn_hide _ |- _ => let H' := fresh in pose proof H as H'; unfold pvn_hide in H'; lia end ].

Ltac dsplit := cbn [disjoint_from outside inside]; simpl_sizes; repeat split; dlia.

Ltac pvn_tw m E bs :=
  repeat match goal with
  | H : bytes_at rsegs m ?A ?cs |- _ =>
      first [ apply (bytes_at_write_other rsegs m E bs A cs) in H; [ | dlia | simpl_sizes; dlia | simpl_sizes; dlia ]
            | clear H ]
  | H : wr_at rsegs m ?A ?k |- _ => apply (wr_at_write rsegs m A k (wa E) bs) in H
  | H : rw_cells rsegs m ?A ?cs |- _ =>
      first [ apply (rw_cells_frame rsegs m A cs E bs) in H; [ | dlia | simpl_sizes; dlia | simpl_sizes; dlia ]
            | clear H ]
  | H : stk rsegs m ?lo ?hi |- _ => apply (stk_write rsegs m lo hi E bs) in H; [ | dlia | simpl_sizes; dlia ]
  | H : munch ?W ?m0 m |- _ =>
      apply (munch_write W m0 m E bs) in H; [ | dlia | simpl_sizes; dlia | cbn [inside]; simpl_sizes; dlia ]
  | H : wmono rsegs ?m0 m |- _ => apply (wmono_write rsegs m0 m (wa E) bs) in H
  end.

Ltac pvn_store m' NEW :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m (Z_to_bv 64 ?E) ?bs) _) =>
      change (write_to_mem m (Z_to_bv 64 E) bs) with (write_to_mem m (wa E) bs);
      pose proof (bytes_at_write_same segs m E bs ltac:(dlia) ltac:(simpl_sizes; dlia)) as NEW;
      pvn_tw m E bs;
      set (m' := write_to_mem m (wa E) bs) in *; clearbody m'
  end.

Ltac pvn_tc m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at rsegs m ?A ?cs |- _ =>
      first [ apply (bytes_at_transport rsegs W m m' A cs) in H; [ | exact MU | dsplit ]
            | clear H ]
  | H : wr_at rsegs m ?A ?k |- _ => apply (wr_at_transport rsegs m m' A k) in H; [ | exact WM ]
  | H : rw_cells rsegs m ?A ?cs |- _ =>
      first [ apply (rw_cells_transport rsegs W m m' A cs) in H; [ | exact MU | exact WM | dsplit ]
            | clear H ]
  | H : stk rsegs m ?lo ?hi |- _ =>
      first [ apply (stk_transport_disjoint rsegs W m m' lo hi) in H; [ | exact MU | exact WM | dsplit ]
            | clear H ]
  | H : munch ?Wq ?m0 m |- _ =>
      apply (munch_trans Wq m0 m m') in H;
      [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; intros ?x ?Hx; cbn [outside] in Hx |- *; repeat split; dlia | exact MU ] ]
  | H : wmono rsegs ?m0 m |- _ => apply (wmono_trans rsegs m0 m m') in H; [ | exact WM ]
  end.

Theorem pv_num_tail : memcpy_contract -> strtod_c.strtod_contract ->
  forall (x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (rao s0o s1o s2o s3o s4o : word) (q text len P d : Z) (tb : list byte) (v res : Z) (txt r : list Z) (lo : Z)
    (canary ev : word),
  s0 = Z_to_bv 64 v -> s1 = Z_to_bv 64 q -> a0 = Z_to_bv 64 res ->
  s2 = Z_to_bv 64 (-1) -> s3 = Z_to_bv 64 (Z.of_nat (length txt)) -> s4 = Z_to_bv 64 (P + Z.of_nat (length txt)) ->
  tp = Z_to_bv 64 strtod_c.STRTOD_TP ->
  pj_in_ok rsegs m q text len P d tb ->
  rest_at tb text P = txt ++ r -> Forall (fun c => numch c = true) txt -> (1 <= length txt)%nat ->
  Z.of_nat (length txt) < 2 ^ 30 ->
  pj_zero rsegs m v ->
  disjoint_from [(text, text + len); (q, q + 24)] v 56 ->
  (forall i, 0 <= i < 56 -> Mem.ro_addr rsegs (Z_to_bv 64 (v + i)) = false) ->
  0 <= res < 2 ^ 64 ->
  (res <> 0 -> exists junk, rw_cells rsegs m res [CB (S (length txt)) junk]) ->
  (res <> 0 -> 4096 <= res /\ (res + Z.of_nat (length txt) + 1 <= strtod_c.STRTOD_IMG_LO \/ strtod_c.STRTOD_GLOBALS_TOP <= res) /\
     res + Z.of_nat (length txt) + 1 <= bv_unsigned sp - strtod_c.STRTOD_K) ->
  (res <> 0 -> disjoint_from [(text, text + len); (q, q + 24); (v, v + 56); (strtod_c.STRTOD_ERRNO, strtod_c.STRTOD_ERRNO + 4);
     (strtod_c.STRTOD_GOT_GUARD, strtod_c.STRTOD_GOT_GUARD + 8); (strtod_c.STRTOD_GUARD, strtod_c.STRTOD_GUARD + 8)]
     res (Z.of_nat (length txt) + 1)) ->
  stk rsegs m lo (bv_unsigned sp + 16) -> lo <= bv_unsigned sp - strtod_c.STRTOD_K ->
  strtod_c.STRTOD_GLOBALS_TOP <= bv_unsigned sp - strtod_c.STRTOD_K -> bv_unsigned sp + 64 <= q -> bv_unsigned sp + 64 <= 2 ^ 47 ->
  rw_cells rsegs m (bv_unsigned sp + 16) [C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  disjoint_from [(q, q + 24); (text, text + len); (v, v + 56)] (bv_unsigned sp - strtod_c.STRTOD_K) (strtod_c.STRTOD_K + 64) ->
  disjoint_from [(q, q + 24); (text, text + len); (v, v + 56)] strtod_c.STRTOD_ERRNO 4 ->
  rw_cells rsegs m strtod_c.STRTOD_GOT_GUARD [C8 (Z_to_bv 64 strtod_c.STRTOD_GUARD)] ->
  rw_cells rsegs m strtod_c.STRTOD_GUARD [C8 canary] ->
  rw_cells rsegs m strtod_c.STRTOD_ERRNO [C4 ev] ->
  MemNorm.ro_agree rsegs m -> frm0 fc ->
  evt rsegs (pv_num_post rao (Z_to_bv 64 (bv_unsigned sp + 64)) gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc m
               q text len P d tb v res txt lo)
    (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15b48) fc None m (seg_rom rsegs)).
Proof.
  intros HMC HST x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m rao s0o s1o s2o s3o s4o q text len P d tb v res txt r lo canary ev
    E0 E1 E2 E3 E4 E5 E6 PJ RA NC L1 L30 PZ VD VRO RR RJ RB RD ST LO GT SQ SPB FR SK SE GG GD ER RO FRM.
  subst s0 s1 a0 s2 s3 s4 tp.
  unfold strtod_c.STRTOD_K, strtod_c.STRTOD_GLOBALS_TOP, strtod_c.STRTOD_IMG_LO, strtod_c.STRTOD_ERRNO,
    strtod_c.STRTOD_GOT_GUARD, strtod_c.STRTOD_GUARD, strtod_c.STRTOD_TP in *.
  pose proof (pj_in_ok_bounds rsegs m q text len P d tb PJ) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2 ^ 64) in SPR.
  cbn [disjoint_from] in VD, SK, SE.
  destruct VD as (VD1 & VD2 & _). destruct SK as (SK1 & SK2 & SK3 & _). destruct SE as (SE1 & SE2 & SE3 & _).
  assert (PL : P + Z.of_nat (length txt) <= text + len).
  { pose proof (f_equal (@length Z) RA) as Hl. unfold rest_at, zb in Hl.
    rewrite length_map, length_skipn, length_app in Hl. lia. }
  assert (LM : Z.of_nat (length (map (Z_to_bv 8) txt)) = Z.of_nat (length txt)) by (rewrite length_map; reflexivity).
  assert (SRC : bytes_at rsegs m P (map (Z_to_bv 8) txt)).
  { pose proof PJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TB & _). apply (pvn_src m tb text P txt r TB); [lia | exact RA]. }
  destruct PJ as (Q0 & Q8 & Q16 & QW & _ & _ & _ & _ & _ & TB & _ & _).
  pose proof PZ as ((VA & VS) & VZ). pose proof VS as (VB1 & VB2 & _).
  pose proof (pvn_zchunk4 m v VZ) as VT.
  pose proof (pvn_zchunk m v 8 VZ ltac:(lia) ltac:(lia)) as VN.
  pose proof (pvn_zchunk m v 16 VZ ltac:(lia) ltac:(lia)) as VR.
  pose proof (pvn_zchunk m v 24 VZ ltac:(lia) ltac:(lia)) as VK.
  pose proof (pvn_zchunk m v 32 VZ ltac:(lia) ltac:(lia)) as VY.
  pose proof (pvn_zchunk m v 40 VZ ltac:(lia) ltac:(lia)) as VC.
  pose proof (pvn_zchunk m v 48 VZ ltac:(lia) ltac:(lia)) as VE.
  pose proof (pvn_gotg m v VA VR GG) as GGD.
  pose proof (stk_of_rw_cells rsegs m 346888 [C8 canary] GD) as GDS.
  change (Z.of_nat (cells_size [C8 canary])) with 8 in GDS.
  destruct (stk_split rsegs m lo (bv_unsigned sp - 8928) (bv_unsigned sp + 16) ST ltac:(lia)) as [_ STK].
  pose proof (wmono_refl rsegs m) as WM.
  assert (HS0 : store_ok rsegs m (wa (v + 16)) 8 = true)
    by (apply (wr_at_store_ok rsegs m v 56 16 8);
        [replace 56 with (v + 56 - v) by lia; apply pvn_stk_wr; [exact VS | lia] | lia | lia]).
  assert (RO2 : MemNorm.ro_agree rsegs (write_to_mem m (wa (v + 16)) (le8 (Z_to_bv 64 res)))).
  { apply pvn_ro_agree_write; [exact RO | lia | rewrite length_le8; lia |].
    intros i Hi. rewrite length_le8 in Hi. replace (v + 16 + i) with (v + (16 + i)) by lia. apply VRO. lia. }
  clear ST PZ GD.
  pvn_hide_all.
  destruct (Z.eq_dec res 0) as [R0|R0].
  - subst res.
    assert (PZ2 : bytes_at rsegs (write_to_mem m (wa (v + 16)) (le8 (Z_to_bv 64 0))) v (repeat (Z_to_bv 8 0) 56)).
    { pose proof (bytes_at_write_inside rsegs m v (repeat (Z_to_bv 8 0) 56) 16 (le8 (Z_to_bv 64 0)) VZ
        ltac:(lia) ltac:(rewrite length_le8, repeat_length; lia)) as H.
      rewrite pj_le8_0 in H |- *. exact H. }
    pose proof (munch_refl [(v + 16, v + 24)] m) as MU0.
    clear VZ RJ RB RD.
    step.
    pvn_store m2 NEW.
    step. if_true.
    do 9 step.
    apply evt_done. unfold pv_num_post. do 18 eexists. split; [reflexivity|].
    split; [exact WM|]. split; [exact RO2|].
    left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact MU0|]. split; [split; [split; [exact VA | exact VS] | exact PZ2]|].
    unfold pj_in_ok.
    refine (conj Q0 (conj Q8 (conj Q16 (conj QW (conj B8 (conj B3 (conj B5 (conj B4 (conj B7 (conj TB (conj _ B9))))))))))).
    cbn [disjoint_from]. split; [dlia | exact I].
  - destruct (RJ R0) as [junk JK]. destruct (RB R0) as (RB1 & RB2 & RB3). specialize (RD R0).
    cbn [disjoint_from] in RD. destruct RD as (RD1 & RD2 & RD3 & RD4 & RD5 & RD6 & _).
    clear RJ RB. pvn_hide_all.
    apply pvn_split_CB in JK as [JA JB].
    pose proof (munch_refl [(bv_unsigned sp - 8928, bv_unsigned sp + 64); (res, res + Z.of_nat (length txt) + 1);
      (v, v + 24); (q, q + 8); (215028, 215028 + 4)] m) as MU.
    clear VZ.
    step.
    pvn_store m2 NEW.
    clear HS0 RO.
    step.
    assert (HZ : bv_eqb (Z_to_bv 64 res) (Z_to_bv 64 0) = false) by (rewrite pvn_eqb0 by lia; apply Z.eqb_neq; exact R0).
    if_cases HZ'; [rewrite HZ in HZ'; discriminate|]. clear HZ HZ'.
    pose proof (pvn_rd _ _ _ Q0) as RQ. rewrite length_le8 in RQ.
    do 3 step.
    clear RQ.
    eapply evt_cut.
    { apply (MemNorm.evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RO2 |].
      eapply (HMC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                (map (Z_to_bv 8) txt) (firstn (length txt) junk)).
      - rewrite unsigned_lit by lia. apply MemNorm.bytes_at_normalize; [exact RO2 | exact SRC].
      - rewrite length_map, unsigned_lit, Nat2Z.id by lia. reflexivity.
      - rewrite !unsigned_lit, Nat2Z.id by lia. apply pvn_rw_norm; [exact RO2 | exact JA |].
        intros i Hi. cbn [cells_size csize] in Hi. apply pvn_ro_out; dlia.
      - rewrite !unsigned_lit by lia. dlia.
      - apply MemNorm.mem_inv_normalize. }
    intros ms3 (s3m & Q3 & REL3 & ROS3).
    destruct Q3 as (k0 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & k8 & k9 & k10 & k11 & k12 & k13 & m3n
      & E3 & MU3 & WM3 & MI3 & DST3 & SRC3).
    subst s3m.
    destruct (pvn_ms_rel _ _ _ _ _ _ _ _ REL3) as (m3 & -> & HR3).
    cbn [ms_mem MS] in ROS3.
    rewrite !unsigned_lit in MU3 by lia. rewrite !unsigned_lit, Nat2Z.id in DST3 by lia.
    pose proof (MemNorm.mem_rel_normalize rsegs _ RO2) as RN2.
    pose proof (MemNorm.munch_rel rsegs _ _ _ _ _ RN2 HR3 ROS3 MU3) as MU3'.
    pose proof (MemNorm.wmono_rel rsegs _ _ _ _ RN2 HR3 ROS3 WM3) as WM3'.
    pose proof (MemNorm.ro_agree_same rsegs _ _ RO2 ROS3) as RO3.
    pose proof (pvn_rw_rel _ _ _ _ HR3 DST3) as DST.
    clear REL3 MU3 WM3 MI3 DST3 SRC3 HR3 RN2 ROS3 RO2 JA.
    pvn_tc m2 m3 MU3' WM3'.
    clear MU3' WM3'.
    replace (ret_pc (Z_to_bv 64 88924)) with (Z_to_bv 64 88924) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    pose proof DST as ((_ & DSTB) & _). cbn [cells_bytes cbytes] in DSTB. rewrite app_nil_r in DSTB.
    pose proof JB as (_ & JW). cbn [cells_size csize] in JW.
    assert (HS1 : store_ok rsegs m3 (wa (res + Z.of_nat (length txt))) 1 = true).
    { rewrite <- (Z.add_0_r (res + Z.of_nat (length txt))) at 1. apply (wr_at_store_ok rsegs m3 _ _ 0 1 JW); lia. }
    clear DST JB JW.
    pose proof (pvn_rd _ _ _ NEW) as RV. rewrite length_le8 in RV.
    step. step. step.
    assert (RO4 : MemNorm.ro_agree rsegs (write_to_mem m3 (wa (res + Z.of_nat (length txt))) (le1 (Z_to_bv 64 0)))).
    { apply pvn_ro_agree_write; [exact RO3 | lia | rewrite length_le1; lia |].
      intros i Hi. rewrite length_le1 in Hi. apply pvn_ro_out; dlia. }
    clear RV.
    pvn_store m4 NEW1.
    clear RO3 HS1 m2.
    assert (RES : bytes_at rsegs m4 res (map (Z_to_bv 8) (txt ++ [0]))).
    { rewrite map_app. apply bytes_at_app. split; [exact DSTB|]. rewrite length_map. exact NEW1. }
    clear DSTB NEW1.
    assert (LM2 : Z.of_nat (length (map (Z_to_bv 8) (txt ++ [0]))) = Z.of_nat (length txt) + 1)
      by (rewrite length_map, length_app; cbn [length]; lia).
    pose proof (pvn_rd _ _ _ NEW) as RV. rewrite length_le8 in RV.
    step. step. step.
    clear RV.
    destruct (stk_split rsegs m4 (bv_unsigned sp - 8928) (bv_unsigned sp) (bv_unsigned sp + 16) STK ltac:(lia)) as [STL STH].
    destruct (stk_split rsegs m4 (bv_unsigned sp) (bv_unsigned sp + 8) (bv_unsigned sp + 16) STH ltac:(lia)) as [_ STE].
    replace (bv_unsigned sp + 16) with (bv_unsigned sp + 8 + 8) in STE by lia.
    destruct (pvn_stk_C8 m4 (bv_unsigned sp + 8) STE) as [ej EJ].
    destruct (pvn_stk_C8 m4 346888 GDS) as [cn CN].
    clear STK STH STE GDS.
    eapply evt_cut.
    { apply (MemNorm.evt_normalize_cj rsegs); [exact FrameAPI.wx_apart_rsegs | exact RO4 |].
      eapply (HST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (bv_unsigned sp + 8) txt ej cn ev).
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - apply MemNorm.bytes_at_normalize_cj_low; [exact RO4 | | exact RES].
        rewrite length_map, length_app. cbn [length]. unfold TASK_SIZE. lia.
      - eapply Forall_impl; [|exact NC]. intros c Hc. apply pvn_numch_is. exact Hc.
      - exact L30.
      - apply pvn_rw_norm_cj; [exact RO4 | exact EJ | cbn [cells_size csize]; unfold TASK_SIZE; lia |].
        intros i Hi. cbn [cells_size csize] in Hi. apply pvn_keep; lia.
      - unfold strtod_c.STRTOD_K. apply pvn_stk_norm_cj; [exact STL|]. intros a Ha. apply pvn_keep; lia.
      - unfold strtod_c.STRTOD_GLOBALS_TOP, strtod_c.STRTOD_K. lia.
      - lia.
      - lia.
      - lia.
      - left. split; [exact RB2 | unfold strtod_c.STRTOD_K; lia].
      - right. lia.
      - lia.
      - lia.
      - unfold strtod_c.STRTOD_GOT_GUARD, strtod_c.STRTOD_GUARD.
        apply pvn_rw_norm_cj; [exact RO4 | exact GG | cbn [cells_size csize]; unfold TASK_SIZE; lia |].
        intros i Hi. cbn [cells_size csize] in Hi. apply pvn_keep; lia.
      - unfold strtod_c.STRTOD_GUARD.
        apply pvn_rw_norm_cj; [exact RO4 | exact CN | cbn [cells_size csize]; unfold TASK_SIZE; lia |].
        intros i Hi. cbn [cells_size csize] in Hi. apply pvn_keep; lia.
      - unfold strtod_c.STRTOD_ERRNO.
        apply pvn_rw_norm_cj; [exact RO4 | exact ER | cbn [cells_size csize]; unfold TASK_SIZE; lia |].
        intros i Hi. cbn [cells_size csize] in Hi. apply pvn_keep; lia.
      - exact (MemNorm.mem_inv_cj_inv _ _ (MemNorm.mem_inv_cj_normalize _ _)).
      - exact (MemNorm.mem_inv_cj_task _ _ (MemNorm.mem_inv_cj_normalize _ _)).
      - exact FRM. }
    intros ms5 (s5m & Q5 & REL5 & CJS5).
    destruct Q5 as (k14 & k15 & k16 & k17 & k18 & k19 & k20 & k21 & k22 & k23 & k24 & k25 & k26 & k27 & k28
      & F' & fc' & m5n & ev' & c & bits & E5 & SM & CR & EC & F10 & FO & FRM' & ER5 & MU5 & WM5 & MI5 & TM5 & ST5).
    subst s5m.
    destruct (pvn_ms_rel_cj _ _ _ _ _ _ _ _ REL5) as (m5 & -> & HR5).
    cbn [ms_mem MS] in CJS5.
    unfold strtod_c.STRTOD_K, strtod_c.STRTOD_ERRNO in MU5, ER5.
    pose proof (MemNorm.mem_rel_cj_normalize rsegs _ RO4) as RN4.
    pose proof (MemNorm.munch_rel_cj rsegs _ _ _ _ _ RN4 HR5 CJS5 MU5) as MU5'.
    pose proof (MemNorm.wmono_rel_cj rsegs _ _ _ _ RN4 HR5 CJS5 WM5) as WM5'.
    pose proof (MemNorm.ro_agree_same_cj rsegs _ _ RO4 CJS5) as RO5.
    pose proof (pvn_rw_rel_cj _ _ _ _ HR5 EC) as EC5.
    pose proof (pvn_rw_rel_cj _ _ _ _ HR5 ER5) as ER6.
    clear REL5 MU5 WM5 MI5 TM5 ST5 EC ER5 HR5 RN4 CJS5 RO4 EJ ER CN STL.
    pvn_tc m4 m5 MU5' WM5'.
    clear MU5' WM5'.
    replace (ret_pc (Z_to_bv 64 88948)) with (Z_to_bv 64 88948) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    pose proof (pvn_bits_range _ _ _ SM) as BR.
    step.
    assert (HS2 : store_ok rsegs m5 (wa (v + 8)) 8 = true)
      by (apply (wr_at_store_ok rsegs m5 v 56 8 8);
          [replace 56 with (v + 56 - v) by lia; apply pvn_stk_wr; [exact VS | lia] | lia | lia]).
    step.
    lazymatch goal with |- context [le8 (reg_get F' ?r)] =>
      replace (reg_get F' r) with (Z_to_bv 64 bits) by (rewrite <- F10; reflexivity) end.
    assert (RO6 : MemNorm.ro_agree rsegs (write_to_mem m5 (wa (v + 8)) (le8 (Z_to_bv 64 bits)))).
    { apply pvn_ro_agree_write; [exact RO5 | lia | rewrite length_le8; lia |].
      intros i Hi. rewrite length_le8 in Hi. replace (v + 8 + i) with (v + (8 + i)) by lia. apply VRO. lia. }
    clear EC5 HS2 GG.
    pvn_store m6 NEW2.
    clear RO5.
    pose proof (pvn_rd_byte m6 res (txt ++ [0]) c RES ltac:(rewrite length_app; cbn [length]; lia)) as RBY.
    destruct (Z.eq_dec c (Z.of_nat (length txt))) as [CE|CE].
    + replace (nth (Z.to_nat c) (txt ++ [0]) 0) with 0 in RBY by (rewrite CE, Nat2Z.id; symmetry; apply pvn_nth_end).
      step. clear RBY.
      step. if_cases HB; [vm_compute in HB; discriminate HB |]. clear HB.
      step. step. step.
      lazymatch goal with |- context [fread ?cc FMT_D ?rr] =>
        replace (fread cc FMT_D rr) with bits by (rewrite <- (unsigned_lit bits) by lia; rewrite <- F10; reflexivity) end.
      pose proof (pvn_fclass_range bits) as CLR.
      assert (EQX : bv_unsigned (Z_to_bv 64 (fp_class (fp_format FMT_D) bits)) = fp_class fmt_double bits)
        by (apply unsigned_lit; cbn [fp_format]; lia).
      rewrite EQX. clear EQX.
      assert (XR : 0 <= Z.land (fp_class fmt_double bits) 897 < 2 ^ 64) by (apply land_lt_pow2; lia).
      pose proof (pvn_fclass bits) as FC.
      destruct (finite bits) eqn:FIN.
      * apply Z.eqb_eq in FC. rewrite FC.
        step. if_cases HB; [vm_compute in HB; discriminate HB |]. clear HB.
        step. step.
        assert (HS3 : store_ok rsegs m6 (wa v) 4 = true)
          by (rewrite <- (Z.add_0_r v) at 1; apply (wr_at_store_ok rsegs m6 v 56 0 4);
              [replace 56 with (v + 56 - v) by lia; apply pvn_stk_wr; [exact VS | lia] | lia | lia]).
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m6 (Z_to_bv 64 v) ?bs) _) =>
          assert (RO7 : MemNorm.ro_agree rsegs (write_to_mem m6 (wa v) bs));
          [ apply pvn_ro_agree_write; [exact RO6 | lia | simpl_sizes; lia |];
            intros i Hi; rewrite ?length_le4, ?length_Z_to_le_bytes in Hi; apply VRO; lia | ] end.
        clear HS3.
        pvn_store m7 NEW3.
        clear RO6.
        assert (HS4 : store_ok rsegs m7 (wa q) 8 = true)
          by (rewrite <- (Z.add_0_r q) at 1; apply (wr_at_store_ok rsegs m7 q 24 0 8 QW); lia).
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m7 (Z_to_bv 64 q) ?bs) _) =>
          assert (RO8 : MemNorm.ro_agree rsegs (write_to_mem m7 (wa q) bs));
          [ apply pvn_ro_agree_write; [exact RO7 | lia | simpl_sizes; lia |];
            intros i Hi; rewrite ?length_le8, ?length_Z_to_le_bytes in Hi; apply pvn_ro_out; lia | ] end.
        clear HS4.
        pvn_store m8 NEW4.
        clear RO7.
        do 10 step.
        apply evt_done. unfold pv_num_post. do 18 eexists. split; [reflexivity|].
        split; [exact WM|]. split; [exact RO8|].
        right. split; [exact R0|]. exists c, bits.
        split; [exact SM|]. split; [lia|]. split; [exact FO|]. split; [exact FRM'|].
        split; [rewrite unsigned_lit by lia; unfold strtod_c.STRTOD_K, strtod_c.STRTOD_ERRNO;
                replace (bv_unsigned sp + 64 - 64 - 8928) with (bv_unsigned sp - 8928) by lia; exact MU|].
        split; [exists ev'; exact ER6|].
        split; [split; [eapply Forall_impl; [|exact NC]; intros x Hx; pose proof (pvn_numch_range x Hx); lia | exact RES]|].
        left. split; [exact CE|]. split; [exact FIN|]. split; [reflexivity|]. split.
        -- apply pvn_hdr; first [assumption | lia].
        -- unfold pj_in_ok.
           refine (conj NEW4 (conj Q8 (conj Q16 (conj QW (conj B8 (conj B3 (conj B5 (conj _ (conj B7 (conj TB (conj _ B9)))))))))));
             [lia | cbn [disjoint_from]; split; [dlia | exact I]].
      * apply Z.eqb_neq in FC.
        assert (HV : v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.land (fp_class fmt_double bits) 897)) = Z_to_bv 64 1).
        { rewrite v_sltu_b2z, !unsigned_lit by lia.
          replace (0 <? Z.land (fp_class fmt_double bits) 897) with true by (symmetry; apply Z.ltb_lt; lia).
          reflexivity. }
        rewrite HV. clear HV.
        step. if_cases HB; [| vm_compute in HB; discriminate HB]. clear HB.
        do 9 step.
        apply evt_done. unfold pv_num_post. do 18 eexists. split; [reflexivity|].
        split; [exact WM|]. split; [exact RO6|].
        right. split; [exact R0|]. exists c, bits.
        split; [exact SM|]. split; [lia|]. split; [exact FO|]. split; [exact FRM'|].
        split; [rewrite unsigned_lit by lia; unfold strtod_c.STRTOD_K, strtod_c.STRTOD_ERRNO;
                replace (bv_unsigned sp + 64 - 64 - 8928) with (bv_unsigned sp - 8928) by lia; exact MU|].
        split; [exists ev'; exact ER6|].
        split; [split; [eapply Forall_impl; [|exact NC]; intros x Hx; pose proof (pvn_numch_range x Hx); lia | exact RES]|].
        right. split; [right; exact FIN|]. split; [reflexivity|]. split.
        -- apply pvn_hdr; first [assumption | lia].
        -- unfold pj_in_ok.
           refine (conj Q0 (conj Q8 (conj Q16 (conj QW (conj B8 (conj B3 (conj B5 (conj B4 (conj B7 (conj TB (conj _ B9))))))))))).
           cbn [disjoint_from]. split; [dlia | exact I].
    + rewrite pvn_nth_in in RBY by lia.
      pose proof (pvn_nth_numch txt (Z.to_nat c) NC ltac:(lia)) as TV.
      step. clear RBY.
      step. if_cases HB; [| exfalso; rewrite pvn_zxb_nz in HB by lia; discriminate HB]. clear HB.
      do 9 step.
      apply evt_done. unfold pv_num_post. do 18 eexists. split; [reflexivity|].
      split; [exact WM|]. split; [exact RO6|].
      right. split; [exact R0|]. exists c, bits.
      split; [exact SM|]. split; [lia|]. split; [exact FO|]. split; [exact FRM'|].
      split; [rewrite unsigned_lit by lia; unfold strtod_c.STRTOD_K, strtod_c.STRTOD_ERRNO;
              replace (bv_unsigned sp + 64 - 64 - 8928) with (bv_unsigned sp - 8928) by lia; exact MU|].
      split; [exists ev'; exact ER6|].
      split; [split; [eapply Forall_impl; [|exact NC]; intros x Hx; pose proof (pvn_numch_range x Hx); lia | exact RES]|].
      right. split; [left; exact CE|]. split; [reflexivity|]. split.
      * apply pvn_hdr; first [assumption | lia].
      * unfold pj_in_ok.
        refine (conj Q0 (conj Q8 (conj Q16 (conj QW (conj B8 (conj B3 (conj B5 (conj B4 (conj B7 (conj TB (conj _ B9))))))))))).
        cbn [disjoint_from]. split; [dlia | exact I].
Qed.
