(** m_file (UBSan build, image 1696d6c34ffd, 0x14268): the sub-piece S_MFU_FRONT of S_MF_LINE
    (U/Prog/mfu_cuts.v).

    The head 0x14348 to the cuts LONG 0x143a4, HDR 0x14434, KEY 0x14528, or the tail 0x146b4 through 0x14688
    (an empty stripped line). Code:
      0x14348 s5 = p; s1 = line; strchr(p, '\n') 0x14358; 0x1435c [sp+0x40] = p;
      found: [sp+0x38] = nl, the -1 trap 0x1436c, s2 = nl + 1;
      not found: strlen(p) 0x1437c, the wrap trap 0x14384, e = p + len, [sp+0x38] = e, s2 = e;
      0x14394 line++ (`addiw`, the signed trap 0x14398); 0x1439c a1 = e - p; 0x143a0 `bge s6, a1`:
        |l| >= 512 goes to LONG 0x143a4 (s4 = 1, s6 = 511, s5 = p, a0 = e);
      0x143c8-0x14404 the comment scan over [p, e) (a1 = 0 at the first byte, -1, -2, ... after; the q = 1 trap
        0x143e0 is dead since q > p >= 1), storing the cut point p + q to [sp+0x38];
      0x14410 strip(&s, &e) on the cells 0x40 / 0x38; 0x14414 s5 = s, 0x14418 s4 = e;
      0x1441c s = e goes to 0x14688 (s4 = 1, `j` the tail); the NULL trap 0x14420 is dead (s >= p >= 1);
      0x14424 `lbu`, 0x14428 a2 = e - s, 0x14430 `bne a0, '['`: KEY 0x14528, else HDR 0x14434.

    Model: mf_line / mf_next / mf_rest of Prog/mfu_facts.v (break_nl_spec, mf_line_rest), SegModel.memchr for
    strchr's answer, mfp_facts' h_cut_idx for the scan, strip_c's strip_mid / strip_le and mfp_facts' slice
    lemmas for the stripped range, and m_line_empty / m_line_hdr / m_line_key for the three model cases.

    Every cut's premises are stated at the cut's memory, which differs from the head's only inside [lo, sp)
    (the callees' frames) and the two scratch cells [sp + 0x38, sp + 0x48): [frt_loop] carries m_file_loop
    across that, [frt_back] carries a cut's post back to the head's memory. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_tok_bridge mfu_facts mfp_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env m_file_c mfu_cuts mfu_kit.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import strchr_c strlen_c strip_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Spec Require Import StrFun StrFun2.
Import ListNotations.
Open Scope Z_scope.

(** ** Pure list facts *)

Lemma frt_memchr_prefix : forall (L R : list Z) ch, ~ In ch L -> memchr (L ++ ch :: R) ch = Some (length L).
Proof.
  induction L as [|b L IH]; intros R ch H; cbn [app memchr length].
  - rewrite Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec b ch) as [->|NE]; [exfalso; apply H; left; reflexivity|].
    rewrite IH by (intros X; apply H; right; exact X). reflexivity.
Qed.

Lemma frt_memchr_none : forall (L : list Z) ch, ~ In ch L -> memchr L ch = None.
Proof.
  induction L as [|b L IH]; intros ch H; cbn [memchr]; [reflexivity|].
  destruct (Z.eqb_spec b ch) as [->|NE]; [exfalso; apply H; left; reflexivity|].
  rewrite IH by (intros X; apply H; right; exact X). reflexivity.
Qed.

Lemma frt_memchr_split : forall (s L R : list Z) ch, s = L ++ ch :: R -> ~ In ch L -> memchr s ch = Some (length L).
Proof. intros s L R ch -> H. apply frt_memchr_prefix. exact H. Qed.

Lemma frt_memchr_none_eq : forall (s L : list Z) ch, s = L -> ~ In ch L -> memchr s ch = None.
Proof. intros s L ch -> H. apply frt_memchr_none. exact H. Qed.

Lemma frt_find_memchr : forall ch (l : list byte), find_byte ch l = memchr (zs l) ch.
Proof.
  intros ch l. unfold zs. induction l as [|b l IH]; cbn [map find_byte memchr]; [reflexivity|].
  rewrite <- IH. destruct (bv_unsigned b =? ch); [reflexivity|]. destruct (find_byte ch l); reflexivity.
Qed.

Lemma frt_strchr_val : forall (a q : Z) (bs : list byte), q = 10 ->
  strchr_val a q bs = match memchr (zs bs) 10 with Some i => a + Z.of_nat i | None => 0 end.
Proof.
  intros a q bs ->. unfold strchr_val, strchr_res. cbn [Z.eqb]. rewrite frt_find_memchr.
  destruct (memchr (zs bs) 10); reflexivity.
Qed.

Lemma frt_firstn_app : forall (s L R : list Z) q, s = L ++ R -> (q <= length L)%nat -> firstn q s = firstn q L.
Proof.
  intros s L R q -> H. rewrite firstn_app. replace (q - length L)%nat with 0%nat by lia.
  cbn [firstn]. apply app_nil_r.
Qed.

(** The stripped bytes of a prefix of l, as a slice of l. *)
Lemma frt_strip_slice : forall (l : list Z) (q : nat), (q <= length l)%nat ->
  slice (strip_lead (firstn q l)) (q - strip_trail (firstn q l)) l = h_strip (firstn q l).
Proof.
  intros l q Hq.
  assert (Lu : length (firstn q l) = q) by (rewrite length_firstn; lia).
  pose proof (strip_le (firstn q l)) as HLE. rewrite Lu in HLE.
  rewrite <- strip_mid. rewrite Lu. unfold slice.
  rewrite skipn_firstn_comm, firstn_firstn.
  replace (Nat.min (q - strip_lead (firstn q l) - strip_trail (firstn q l))
                   (q - strip_lead (firstn q l)))
    with (q - strip_lead (firstn q l) - strip_trail (firstn q l))%nat by lia.
  f_equal. lia.
Qed.

Lemma frt_slice_firstn : forall (l : list Z) q i j, (j <= q)%nat -> slice i j (firstn q l) = slice i j l.
Proof.
  intros l q i j H. unfold slice. rewrite skipn_firstn_comm, firstn_firstn.
  replace (Nat.min (j - i) (q - i)) with (j - i)%nat by lia. reflexivity.
Qed.

Lemma frt_hd0_nth : forall (l : list Z), hd0 l = nth 0 l 0.
Proof. intros [|x l]; reflexivity. Qed.

Lemma frt_firstn1_skipn : forall {A} (l : list A) (d : A) k,
  (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof.
  intros A l d. induction l as [|x l IH]; intros [|k] H; cbn [length skipn firstn nth] in *;
    first [ lia | reflexivity | apply IH; lia ].
Qed.

Lemma frt_nth_zs : forall (bs : list byte) k, nth k (zs bs) 0 = bv_unsigned (nth k bs (Z_to_bv 8 0)).
Proof.
  unfold zs. induction bs as [|b bs IH]; intros [|k]; cbn [map nth];
    first [ reflexivity | vm_compute; reflexivity | apply IH ].
Qed.

Lemma frt_bv8_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma frt_ub : forall b : byte, bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof. intros b. pose proof (frt_bv8_range b). apply unsigned_lit. lia. Qed.

Lemma frt_swrap32 : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia. Qed.

Lemma frt_signed_lit : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit by lia.
  destruct (Z.ltb_spec z (2 ^ 63)); [reflexivity | lia].
Qed.

Lemma frt_bytes_firstn : forall segs m a (bs : list byte) k,
  bytes_at segs m a bs -> bytes_at segs m a (firstn k bs).
Proof.
  intros segs m a bs k H. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma frt_zs_firstn : forall (bs : list byte) q, zs (firstn q bs) = firstn q (zs bs).
Proof. intros bs q. unfold zs. symmetry. apply firstn_map. Qed.

(** A byte of a C string (index [length s] is its NUL). *)
Lemma frt_rd : forall m a (s : list Z) k, cstr_at rsegs m a s -> (k <= length s)%nat ->
  exists b : byte, ov_read_bytes rsegs m (wa (a + Z.of_nat k)) 1 = Some [b] /\ bv_unsigned b = nth k s 0.
Proof.
  intros m a s k HC Hk. destruct (cstr_cut rsegs m a s HC) as (bs & sl & HB & Hz & Hn & Hnb & Hl & _ & _).
  assert (Hlen : length (bs ++ Z_to_bv 8 0 :: sl) = (length bs + S (length sl))%nat)
    by (rewrite length_app; cbn [length]; lia).
  exists (nth k (bs ++ Z_to_bv 8 0 :: sl) (Z_to_bv 8 0)).
  split.
  - rewrite (bytes_at_ov_read rsegs m a _ k 1 HB) by lia.
    rewrite (frt_firstn1_skipn _ (Z_to_bv 8 0) k) by lia. reflexivity.
  - destruct (Nat.lt_ge_cases k (length s)) as [Hlt|Hge].
    + rewrite app_nth1 by lia. rewrite <- Hz, frt_nth_zs. reflexivity.
    + assert (Ek : k = length bs) by lia. subst k.
      rewrite nth_middle, nth_overflow by lia. vm_compute. reflexivity.
Qed.

Lemma frt_firstn8_le8 : forall v : word, firstn 8 (skipn 0 (le8 v)) = le8 v.
Proof.
  intros v. change (skipn 0 (le8 v)) with (le8 v).
  replace 8%nat with (length (le8 v)) by apply length_le8. apply firstn_all.
Qed.

Lemma frt_read8 : forall m a v, cell8 m a v -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros m a v H. unfold cell8 in H. pose proof (length_le8 (Z_to_bv 64 v)) as L8.
  pose proof (bytes_at_ov_read rsegs m a (le8 (Z_to_bv 64 v)) 0 8 H ltac:(lia)) as R.
  change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r in R.
  rewrite frt_firstn8_le8 in R. exact R.
Qed.

Lemma frt_cell8_head : forall m A u cs, rw_cells rsegs m A (C8 u :: cs) -> bytes_at rsegs m A (le8 u).
Proof.
  intros m A u cs [[_ B] _]. cbn [cells_bytes cbytes] in B. apply bytes_at_app in B. exact (proj1 B).
Qed.

Lemma frt_cell8_snd : forall m A w u, rw_cells rsegs m A [CB 8 w; C8 u] -> bytes_at rsegs m (A + 8) (le8 u).
Proof.
  intros m A w u [[WF B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  apply bytes_at_app in B as [_ B2]. cbn [cells_wf cell_wf] in WF. destruct WF as [W1 _].
  rewrite W1 in B2. change (Z.of_nat 8) with 8 in B2. exact B2.
Qed.

Lemma frt_cell8_pair : forall m A u v, rw_cells rsegs m A [C8 u; C8 v] ->
  bytes_at rsegs m A (le8 u) /\ bytes_at rsegs m (A + 8) (le8 v).
Proof.
  intros m A u v H. split; [eapply frt_cell8_head; exact H|].
  destruct H as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  apply bytes_at_app in B as [_ B2]. rewrite length_le8 in B2. change (Z.of_nat 8) with 8 in B2. exact B2.
Qed.

Lemma frt_cell8_pair_at : forall m A B u v, rw_cells rsegs m A [C8 u; C8 v] -> B = A + 8 ->
  bytes_at rsegs m B (le8 v).
Proof. intros m A B u v H ->. exact (proj2 (frt_cell8_pair m A u v H)). Qed.

(** ** The walk *)
Section Front.
Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (lo : Z).
Variables (ra0 sp0 sp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word).
Variables (c p line : Z) (mc : mconf) (cur : option nat) (k0 : nat) (rest : list Z) (n : nat).
Hypothesis HCHR : strchr_contract.
Hypothesis HSLEN : strlen_contract.
Hypothesis HSTR : strip_contract.
Hypothesis HT : H_MF_TAIL n.
Hypothesis HLG : H_MFU_LONG n.
Hypothesis HHD : H_MFU_HDR n.
Hypothesis HKY : H_MFU_KEY n.
Hypothesis Hn : (length rest < S n)%nat.
Hypothesis Hrest : rest <> [].
Hypothesis HLOOP : m_file_loop m0 fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
                     ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.

Local Notation Sp := (bv_unsigned sp).
Local Notation Sp0 := (bv_unsigned sp0).
Local Notation LL := (mf_line rest).
Local Notation WF := [(bv_unsigned sp - 5952, bv_unsigned sp);
                      (bv_unsigned sp + 0x38, bv_unsigned sp + 0x48)].
Local Notation POST :=
  (mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m0 lo c k0
     (mf_fin (m_line (mc, cur) (line + 1) (mf_line rest)) line rest)).

Ltac fweq := rewrite ?unsigned_lit by lia;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia ].

(** The arithmetic the loop facts give. *)
Lemma frt_facts :
  Sp + 272 = Sp0 /\ lo + 6224 <= Sp0 /\ 0 <= lo /\ Sp0 < 2 ^ 63 /\
  0 < p /\ p + Z.of_nat (length rest) + 1 <= 2 ^ 64 /\
  (p + Z.of_nat (length rest) + 8 <= lo \/ Sp0 <= p) /\
  (c + SEG_M_SIZE + 4 <= lo \/ Sp0 <= c) /\ 0 < c /\ c mod 16 = 0 /\
  0 <= line /\ line + Z.of_nat (length rest) <= 65535 /\
  (length LL <= length rest)%nat /\ frm0 fc /\ 0x54088 <= lo /\ Sp0 mod 16 = 0.
Proof.
  pose proof HLOOP as HL.
  destruct HL as (Q1 & _ & _ & _ & _ & _ & _ & _ & Q9 & Q10 & _ & Q12 & _ & _ & Q15 & _ & _ &
                  Q18 & Q19 & _ & _ & Q22 & _ & Q24 & Q25 & _ & Q27 & _ & _ & Q30 & _).
  destruct Q27 as (HFRM & _ & _ & HIMG & HS63).
  destruct Q30 as (HSTK & HDEP & HM16 & _).
  destruct HSTK as (HLO0 & _ & _).
  destruct Q12 as (bsc & HBc & _). pose proof (bytes_at_bound rsegs m0 c _ HBc) as HCB.
  destruct (cstr_cut rsegs m0 p rest Q24) as (bs & sl & HB & Hz & _ & _ & Hl & _ & Hsl).
  pose proof (bytes_at_bound rsegs m0 p _ HB) as HBB.
  rewrite length_app in HBB. cbn [length] in HBB.
  assert (HLL : (length LL <= length rest)%nat).
  { destruct (mf_line_rest rest) as [[E _]|[E _]];
      [rewrite E at 2; rewrite length_app; cbn [length]; lia | rewrite E at 2; lia]. }
  unfold M_FILE_FRAME in Q1. unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in HDEP.
  unfold apart in Q15, Q25. unfold sa_img_end, SA, SEG_UBSAN in HIMG. cbn in HIMG.
  repeat split; try lia; try assumption.
Qed.

(** The memory of the walk: only the callees' frames below sp and the two scratch cells changed. *)
Definition frt_ok (m : word -> option byte) : Prop :=
  munch WF m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\ stk rsegs m lo Sp0.

Lemma frt_out_lo : forall x, 0 <= x < lo -> outside WF x.
Proof.
  intros x Hx. pose proof frt_facts as (HSP & HLO & _). cbn [outside].
  split; [lia | split; [lia | exact I]].
Qed.

Lemma frt_task : forall m, munch WF m0 m -> MemNorm.task_mem rsegs m.
Proof.
  intros m MU. pose proof frt_facts as (HSP & HLO & HLO0 & _).
  pose proof HLOOP as HL.
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                  _ & _ & _ & _ & _ & _ & _ & _ & _ & HPE & _ & _ & HSO & _).
  destruct HPE as (_ & TM & _ & _ & _). destruct HSO as (ST0 & _ & _ & HRO).
  intros a b E.
  destruct (Z_le_gt_dec lo (bv_unsigned a)) as [D1|D1].
  - destruct (Z_lt_ge_dec (bv_unsigned a) Sp0) as [D2|D2].
    + destruct ST0 as (_ & _ & HS). destruct (HS (bv_unsigned a) ltac:(lia)) as [_ (b' & Hb')].
      unfold mrd in Hb'. rewrite (HRO (bv_unsigned a) ltac:(lia)) in Hb'.
      destruct (m0 (wa (bv_unsigned a))) as [b0|] eqn:Em0; [|discriminate Hb'].
      unfold wa in Em0. rewrite Z_to_bv_bv_unsigned in Em0. exact (TM a b0 Em0).
    + assert (HO : outside WF (bv_unsigned a))
        by (cbn [outside]; split; [lia | split; [lia | exact I]]).
      rewrite (MU a HO) in E. exact (TM a b E).
  - assert (HO : outside WF (bv_unsigned a))
      by (cbn [outside]; split; [lia | split; [lia | exact I]]).
    rewrite (MU a HO) in E. exact (TM a b E).
Qed.

Lemma frt_loop : forall m, frt_ok m ->
  m_file_loop m fc Sp0 Sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Proof.
  intros m (MU & WM & MI & ST).
  pose proof frt_facts as (HSP & HLO & HLO0 & HS63 & HP0 & HPB & HAP & HAC & HC0 & HC16 & HLN0 & HLN & HLL &
                           HFRM & HIMG & HM16).
  pose proof HLOOP as HL.
  destruct HL as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 &
                  Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27 & Q28 & Q29 & Q30 & Q31).
  assert (TBlo : forall a v, cell8 m0 a v -> Sp <= a -> a + 8 <= Sp + 0x38 -> cell8 m a v).
  { intros a v HB D1 D2. unfold cell8 in *. eapply bytes_at_transport; [exact HB | exact MU |].
    rewrite length_le8. cbn [disjoint_from]. split; [right; lia | split; [left; lia | exact I]]. }
  assert (TBhi : forall a (bq : list byte), bytes_at rsegs m0 a bq -> Sp + 0x48 <= a -> bytes_at rsegs m a bq).
  { intros a bq HB D. eapply bytes_at_transport; [exact HB | exact MU |].
    cbn [disjoint_from]. split; [right; lia | split; [right; lia | exact I]]. }
  assert (TBimg : forall a (bq : list byte) (k : nat), bytes_at rsegs m0 a bq -> length bq = k ->
                    0 <= a -> a + Z.of_nat k <= lo -> bytes_at rsegs m a bq).
  { intros a bq k HB Hk D1 D2. subst k. eapply bytes_at_transport; [exact HB | exact MU |].
    cbn [disjoint_from]. split; [left; lia | split; [left; lia | exact I]]. }
  unfold m_file_loop.
  split; [exact Q1|].
  split; [unfold saved_at in *; apply TBhi; [exact Q2 | unfold M_FILE_SAVE; lia]|].
  split; [apply TBlo; [exact Q3 | lia | lia]|].
  split; [apply TBlo; [exact Q4 | lia | lia]|].
  split; [apply TBlo; [exact Q5 | lia | lia]|].
  split; [apply TBlo; [exact Q6 | lia | lia]|].
  split; [apply TBlo; [exact Q7 | lia | lia]|].
  split; [apply TBlo; [exact Q8 | lia | lia]|].
  split; [exact Q9|]. split; [exact Q10|]. split; [exact Q11|].
  split.
  { destruct Q12 as (bsc & HBc & ENc).
    assert (Lc : Z.of_nat (length bsc) = SEG_M_SIZE) by (destruct ENc as (L & _); exact L).
    exists bsc. split; [|exact ENc]. eapply bytes_at_transport; [exact HBc | exact MU |].
    cbn [disjoint_from]. unfold SEG_M_SIZE in *.
    split; [lia | split; [lia | exact I]]. }
  split; [eapply wr_at_transport; [exact Q13 | exact WM]|].
  split.
  { destruct Q14 as (slc & HBs & Hle).
    assert (Hc8 : c mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (Hk4 : (- (c + SEG_M_SIZE)) mod 8 = 4).
    { unfold SEG_M_SIZE.
      assert (E : - (c + 9236) = 4 + (- (c / 8) - 1155) * 8)
        by (pose proof (Z.div_mod c 8 ltac:(lia)) as D; lia).
      rewrite E, Z.mod_add by lia. reflexivity. }
    rewrite Hk4 in Hle.
    exists (firstn 4 slc). split.
    - eapply bytes_at_transport; [apply frt_bytes_firstn; exact HBs | exact MU |].
      rewrite length_firstn. cbn [disjoint_from]. unfold SEG_M_SIZE in *.
      split; [lia | split; [lia | exact I]].
    - rewrite Hk4, length_firstn. lia. }
  split; [exact Q15|]. split; [exact Q16|]. split; [exact Q17|].
  split; [exact Q18|]. split; [exact Q19|]. split; [exact Q20|]. split; [exact Q21|].
  split; [exact Q22|]. split; [exact Q23|].
  split.
  { destruct (cstr_cut rsegs m0 p rest Q24) as (bsp & slp & HBp & Hzp & Hnp & Hnbp & Hlp & Hmp & Hsp8).
    exists bsp, slp. split; [|split; [exact Hzp | split; [exact Hnp|]]].
    - eapply bytes_at_transport; [exact HBp | exact MU |].
      rewrite length_app. cbn [length]. cbn [disjoint_from]. unfold apart in Q25.
      split; [lia | split; [lia | exact I]].
    - rewrite Hlp in Hmp. exact Hmp. }
  split; [exact Q25|]. split; [exact Q26|].
  split.
  { destruct Q27 as (F1 & _ & SSP & F4 & F5).
    split; [exact F1|]. split; [apply frt_task; exact MU|].
    split; [|split; [exact F4 | exact F5]].
    destruct SSP as (G1 & (g & G2)). split.
    - eapply TBimg; [exact G1 | apply length_le8 | unfold sa_got_guard, SA, SEG_UBSAN; cbn; lia
                    | unfold sa_got_guard, SA, SEG_UBSAN; cbn; lia].
    - exists g. eapply TBimg; [exact G2 | apply length_le8 | unfold sa_guard, SA, SEG_UBSAN; cbn; lia
                    | unfold sa_guard, SA, SEG_UBSAN; cbn; lia]. }
  split.
  { intros a Ha. rewrite <- (Q28 a Ha). unfold mrd.
    unfold sa_catalogue, SA, SEG_UBSAN, CAT_BYTES in Ha. cbn in Ha.
    rewrite (MU (wa a) (frt_out_lo (bv_unsigned (wa a)) ltac:(rewrite wa_unsigned by lia; lia))).
    reflexivity. }
  split.
  { intros a Ha. rewrite <- (Q29 a Ha). unfold mrd. unfold M_KEY_WORDS in Ha.
    rewrite (MU (wa a) (frt_out_lo (bv_unsigned (wa a)) ltac:(rewrite wa_unsigned by lia; lia))).
    reflexivity. }
  split.
  { destruct Q30 as (_ & D1 & D2 & D3). split; [exact ST | split; [exact D1 | split; [exact D2 | exact D3]]]. }
  exact MI.
Qed.

Lemma frt_mid_ok : forall m, frt_ok m -> mfu_mid m0 m Sp0 lo c k0 mc false.
Proof.
  intros m FO. pose proof FO as (MU & WM & MI & ST).
  pose proof frt_facts as (HSP & HLO & _).
  pose proof (frt_loop m FO) as LP.
  destruct LP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  split; [|split; [exact WM | split; [exact MI | split; [exact ST | exact HM]]]].
  eapply munch_weaken; [|exact MU]. unfold sub_fp, mfu_W, M_FILE_W.
  intros x H. cbn [app outside] in H. cbn [outside].
  unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in H.
  destruct H as (H1 & _). split; [lia | split; [lia | exact I]].
Qed.

Lemma frt_back : forall m ms mf, frt_ok m ->
  evt rsegs (mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0 mf) ms ->
  evt rsegs (mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m0 lo c k0 mf) ms.
Proof.
  intros m ms mf (MU & WM & MI & ST) EV.
  pose proof frt_facts as (HSP & HLO & _).
  assert (SUB : sub_fp WF (M_FILE_W Sp0 c k0 mf)).
  { unfold sub_fp, M_FILE_W. intros x H. cbn [outside] in H. cbn [outside].
    unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in H.
    destruct H as (H1 & _). split; [lia | split; [lia | exact I]]. }
  eapply evt_mono; [exact EV|]. clear EV.
  unfold mfu_post, ret_void_fp.
  intros ms' (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & F' & fc' & m' &
              Hms & HF & HFk & MU' & WM' & MI' & TM' & ST' & QQ).
  exists y5, y6, y7, y10, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, F', fc', m'.
  split; [exact Hms|]. split; [exact HF|]. split; [exact HFk|].
  split; [eapply munch_trans; [eapply munch_weaken; [exact SUB | exact MU] | exact MU']|].
  split; [eapply wmono_trans; [exact WM | exact WM']|].
  split; [exact MI'|]. split; [exact TM'|]. split; [exact ST' | exact QQ].
Qed.

(** Scratch cells for the stores: 16 writable bytes at sp + 0x38. *)
Lemma frt_cells : forall m, stk rsegs m lo Sp0 -> exists junk, rw_cells rsegs m (Sp + 0x38) [CB 16 junk].
Proof.
  intros m ST. pose proof frt_facts as (HSP & HLO & HLO0 & _).
  destruct (stk_split rsegs m lo (Sp + 0x38) Sp0 ST ltac:(lia)) as [_ S1].
  destruct (stk_split rsegs m (Sp + 0x38) (Sp + 0x48) Sp0 S1 ltac:(lia)) as [S2 _].
  destruct (stk_carve rsegs m (Sp + 0x38) (Sp + 0x48) 16 S2 ltac:(cbn; lia)) as [_ [junk FR]].
  exists junk. replace (Sp + 0x48 - Z.of_nat 16) with (Sp + 0x38) in FR by (cbn; lia). exact FR.
Qed.

(** ** 0x14688: the empty stripped line joins the tail *)
Lemma frt_tail_empty : forall m (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y28 y29 y30 y31 : word),
  frt_ok m -> (length LL < 512)%nat -> h_strip (h_cut_comment LL) = [] ->
  evt rsegs POST
    (MS (mkR y1 sp gp tp y5 y6 y7 (Z_to_bv 64 c) y9 y10 y11 y12 y13 y14 y15 y16 y17
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) y20 y21 (Z_to_bv 64 0x1ff)
             (Z_to_bv 64 0x23) (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20)
             (Z_to_bv 64 0x3b) y28 y29 y30 y31)
        F (Z_to_bv 64 0x14688) fc None m (seg_rom rsegs)).
Proof.
  intros m y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y28 y29 y30 y31 FO H512 HE.
  pose proof frt_facts as (HSP & HLO & HLO0 & HS63 & HP0 & HPB & HAP & HAC & HC0 & HC16 & HLN0 & HLN & HLL &
                           HFRM & HIMG & HM16).
  pose proof (frt_loop m FO) as LP.
  pose proof LP as LP'.
  destruct LP' as (_ & R2 & R3 & R4 & R5 & R6 & R7 & R8 & _).
  pose proof HLOOP as HL0.
  destruct HL0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QC & _).
  step. step.
  rewrite (m_line_empty mc cur (line + 1) LL H512 HE).
  eapply (mfu_tail n y1 sp gp tp y5 y6 y7 (Z_to_bv 64 c) y9 y10 y11 y12 y13 y14 y15 y16 y17
            (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) (Z_to_bv 64 1) y21 (Z_to_bv 64 0x1ff)
            (Z_to_bv 64 0x23) (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20)
            (Z_to_bv 64 0x3b) y28 y29 y30 y31 F F fc fc m0 m lo
            ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc cur k0 rest mc cur).
  - exact HT.
  - lia.
  - exact Hrest.
  - exact HLOOP.
  - apply frt_mid_ok. exact FO.
  - exact R2.
  - exact R3.
  - exact R4.
  - exact R5.
  - exact R6.
  - exact R7.
  - exact R8.
  - apply mf_grows_refl.
  - exact QC.
  - lia.
  - lia.
  - exact HFRM.
  - intros k _. reflexivity.
  - unfold m_file_regs. repeat split; reflexivity.
Qed.

(** ** 0x14414: strip has returned; the tail, HDR or KEY *)
Lemma frt_after_strip : forall m (q : nat)
    (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y28 y29 y30 y31 : word),
  frt_ok m -> (length LL < 512)%nat -> (q <= length LL)%nat ->
  h_cut_comment LL = firstn q LL ->
  cell8 m (Sp + 0x40) (p + Z.of_nat (strip_lead (h_cut_comment LL))) ->
  cell8 m (Sp + 0x38) (p + Z.of_nat q - Z.of_nat (strip_trail (h_cut_comment LL))) ->
  evt rsegs POST
    (MS (mkR y1 sp gp tp y5 y6 y7 (Z_to_bv 64 c) (Z_to_bv 64 line) y10 y11 y12 y13 y14 y15 y16 y17
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) y20 y21 (Z_to_bv 64 0x1ff)
             (Z_to_bv 64 0x23) (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20)
             (Z_to_bv 64 0x3b) y28 y29 y30 y31)
        F (Z_to_bv 64 0x14414) fc None m (seg_rom rsegs)).
Proof.
  intros m q y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y28 y29 y30 y31 FO H512 Hq Hu C40 C38.
  pose proof frt_facts as (HSP & HLO & HLO0 & HS63 & HP0 & HPB & HAP & HAC & HC0 & HC16 & HLN0 & HLN & HLL &
                           HFRM & HIMG & HM16).
  pose proof (frt_loop m FO) as LP.
  pose proof LP as LP2.
  destruct LP2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                   _ & _ & _ & _ & _ & _ & HC & _).
  pose proof (strip_le (h_cut_comment LL)) as HLE.
  assert (Lu : length (h_cut_comment LL) = q) by (rewrite Hu, length_firstn; lia).
  rewrite Lu in HLE.
  pose proof (frt_read8 m (Sp + 0x40) _ C40) as RD40.
  pose proof (frt_read8 m (Sp + 0x38) _ C38) as RD38.
  step. step.
  step. if_cases K; cbv iota.
  - (* s5 = s4: the stripped line is empty *)
    zify_cond K. rewrite ?unsigned_lit in K by lia.
    apply (frt_tail_empty m y1 y5 y6 y7 (Z_to_bv 64 line) y10 y11 y12 y13 y14 y15 y16 y17
             (Z_to_bv 64 (p + Z.of_nat q - Z.of_nat (strip_trail (h_cut_comment LL))))
             (Z_to_bv 64 (p + Z.of_nat (strip_lead (h_cut_comment LL)))) y28 y29 y30 y31 FO H512).
    rewrite <- (strip_mid (h_cut_comment LL)). rewrite Lu.
    replace (q - strip_lead (h_cut_comment LL) - strip_trail (h_cut_comment LL))%nat with 0%nat by lia.
    reflexivity.
  - (* s5 <> s4 *)
    zify_cond K. rewrite ?unsigned_lit in K by lia.
    assert (Hij : (strip_lead (h_cut_comment LL) < q - strip_trail (h_cut_comment LL))%nat) by lia.
    assert (Hsl : slice (strip_lead (h_cut_comment LL)) (q - strip_trail (h_cut_comment LL)) LL
                  = h_strip (h_cut_comment LL)).
    { rewrite Hu. apply frt_strip_slice. lia. }
    assert (Hlen : length (h_strip (h_cut_comment LL))
                   = (q - strip_trail (h_cut_comment LL) - strip_lead (h_cut_comment LL))%nat)
      by (rewrite <- Hsl; rewrite slice_length by lia; reflexivity).
    destruct (frt_rd m p rest (strip_lead (h_cut_comment LL)) HC ltac:(lia)) as (b & RDb & Eb).
    pose proof (frt_bv8_range b) as Rb.
    assert (Enth : nth (strip_lead (h_cut_comment LL)) LL 0 = nth 0 (h_strip (h_cut_comment LL)) 0).
    { rewrite <- Hsl. rewrite slice_nth by lia. rewrite Nat.add_0_r. reflexivity. }
    assert (Ebl : bv_unsigned b = nth 0 (h_strip (h_cut_comment LL)) 0)
      by (rewrite Eb, <- Enth; apply mf_line_nth; lia).
    step. if_cases K2; cbv iota; [exfalso; zify_cond K2; rewrite ?unsigned_lit in K2 by lia; lia|].
    step. step. step.
    step. if_cases K3; cbv iota.
    + (* not '[': KEY *)
      zify_cond K3. rewrite ?frt_ub, ?unsigned_lit in K3 by lia.
      rewrite (m_line_key mc cur (line + 1) LL H512
                 ltac:(intros HX; rewrite HX in Hlen; cbn [length] in Hlen; lia)
                 ltac:(rewrite frt_hd0_nth, <- Ebl; lia)).
      eapply frt_back; [exact FO|].
      eapply (HKY y1 sp gp tp y5 y6 y7 (Z_to_bv 64 c) (Z_to_bv 64 line) _ _ _ y13 y14 y15 y16 y17
                (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) _ _ (Z_to_bv 64 0x1ff)
                (Z_to_bv 64 0x23) (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20)
                (Z_to_bv 64 0x3b) y28 y29 y30 y31 F fc m lo
                ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc cur k0 rest
                (strip_lead (h_cut_comment LL)) ((q - strip_trail (h_cut_comment LL))%nat)).
      * lia.
      * exact Hrest.
      * exact LP.
      * unfold mfu_lregs. repeat split; reflexivity.
      * reflexivity.
      * exact H512.
      * exact Hij.
      * lia.
      * exact Hsl.
      * rewrite <- Enth in Ebl. rewrite <- Ebl. lia.
      * fweq.
      * fweq.
      * fweq.
    + (* '[': HDR *)
      zify_cond K3. rewrite ?frt_ub, ?unsigned_lit in K3 by lia.
      rewrite (m_line_hdr mc cur (line + 1) LL H512
                 ltac:(rewrite frt_hd0_nth, <- Ebl; lia)).
      eapply frt_back; [exact FO|].
      eapply (HHD y1 sp gp tp y5 y6 y7 (Z_to_bv 64 c) (Z_to_bv 64 line) _ _ _ y13 y14 y15 y16 y17
                (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) _ _ (Z_to_bv 64 0x1ff)
                (Z_to_bv 64 0x23) (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20)
                (Z_to_bv 64 0x3b) y28 y29 y30 y31 F fc m lo
                ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc cur k0 rest
                (strip_lead (h_cut_comment LL)) ((q - strip_trail (h_cut_comment LL))%nat)).
      * lia.
      * exact Hrest.
      * exact LP.
      * unfold mfu_lregs. repeat split; reflexivity.
      * reflexivity.
      * exact H512.
      * exact Hij.
      * lia.
      * exact Hsl.
      * rewrite <- Enth in Ebl. rewrite <- Ebl. lia.
      * fweq.
      * fweq.
      * fweq.
Qed.

(** ** 0x14408: the strip call *)
Lemma frt_strip_call : forall m (q : nat)
    (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y28 y29 y30 y31 : word),
  frt_ok m -> (length LL < 512)%nat -> (q <= length LL)%nat ->
  h_cut_comment LL = firstn q LL ->
  cell8 m (Sp + 0x40) p -> cell8 m (Sp + 0x38) (p + Z.of_nat q) ->
  evt rsegs POST
    (MS (mkR y1 sp gp tp y5 y6 y7 (Z_to_bv 64 c) (Z_to_bv 64 line) y10 y11 y12 y13 y14 y15 y16 y17
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) y20 y21 (Z_to_bv 64 0x1ff)
             (Z_to_bv 64 0x23) (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20)
             (Z_to_bv 64 0x3b) y28 y29 y30 y31)
        F (Z_to_bv 64 0x14408) fc None m (seg_rom rsegs)).
Proof.
  intros m q y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y28 y29 y30 y31 FO H512 Hq Hu C40 C38.
  pose proof frt_facts as (HSP & HLO & HLO0 & HS63 & HP0 & HPB & HAP & HAC & HC0 & HC16 & HLN0 & HLN & HLL &
                           HFRM & HIMG & HM16).
  pose proof (frt_loop m FO) as LP.
  pose proof LP as LP2.
  destruct LP2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                   _ & _ & _ & _ & _ & _ & HC & _).
  destruct (cstr_cut rsegs m p rest HC) as (bsp & slp & HBp & Hzp & Hnp & Hnbp & Hlp & _ & _).
  assert (HBq : bytes_at rsegs m p (firstn q bsp)).
  { pose proof (frt_bytes_firstn rsegs m p (bsp ++ Z_to_bv 8 0 :: slp) q HBp) as HX.
    rewrite firstn_app in HX.
    replace (q - length bsp)%nat with 0%nat in HX by lia. cbn [firstn] in HX.
    rewrite app_nil_r in HX. exact HX. }
  step. step. step.
  eapply (mfu_strip HSTR POST (Z_to_bv 64 0x14414) sp gp tp y5 y6 y7 (Z_to_bv 64 c) (Z_to_bv 64 line)
            (Z_to_bv 64 (Sp + 0x40)) (Z_to_bv 64 (Sp + 0x38)) y12 y13 y14 y15 y16 y17
            (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) y20 y21 (Z_to_bv 64 0x1ff)
            (Z_to_bv 64 0x23) (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20)
            (Z_to_bv 64 0x3b) y28 y29 y30 y31 F fc fc m0 m lo
            ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc cur k0 rest mc false
            0x40 0x38 p (p + Z.of_nat q) (firstn q bsp)).
  - exact HLOOP.
  - apply frt_mid_ok. exact FO.
  - lia.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact C40.
  - exact C38.
  - rewrite unsigned_lit by lia. reflexivity.
  - rewrite unsigned_lit by lia. reflexivity.
  - exact HBq.
  - rewrite length_firstn. lia.
  - lia.
  - lia.
  - unfold apart. lia.
  - intros m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' MID MU' WM' C40' C38'.
    assert (Ez : zs (firstn q bsp) = h_cut_comment LL).
    { rewrite frt_zs_firstn, Hzp, Hu.
      destruct (mf_line_rest rest) as [[E _]|[E _]];
        [apply (frt_firstn_app rest LL (NL :: mf_rest rest) q E ltac:(lia))
        |apply (frt_firstn_app rest LL [] q ltac:(rewrite app_nil_r; exact E) ltac:(lia))]. }
    rewrite Ez in C40', C38'.
    pose proof FO as (MU & WM & MI & ST). pose proof MID as (_ & WM2 & MI2 & ST2 & _).
    replace (ret_pc (Z_to_bv 64 0x14414)) with (Z_to_bv 64 0x14414)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    eapply (frt_after_strip m' q (Z_to_bv 64 0x14414) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7'
              y20 y21 t3' t4' t5' t6').
    + split; [|split; [|split; [exact MI2 | exact ST2]]].
      * eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU'].
        unfold sub_fp. intros x HX. cbn [outside] in *.
        split; [lia | split; [lia | exact I]].
      * exact WM2.
    + exact H512.
    + exact Hq.
    + exact Hu.
    + exact C40'.
    + exact C38'.
Qed.

(** ** 0x143d0: the comment scan, k bytes done, j = |l| - k left *)
Lemma frt_scan : forall (j k : nat) m
    (y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (w10 w11 w21 : word),
  frt_ok m -> (length LL < 512)%nat ->
  (j + k = length LL)%nat -> (0 < j)%nat ->
  (forall i, (i < k)%nat -> cut_at LL i = false) ->
  cell8 m (Sp + 0x40) p -> cell8 m (Sp + 0x38) (p + Z.of_nat (length LL)) ->
  w10 = Z_to_bv 64 (p + Z.of_nat (length LL)) -> w11 = Z_to_bv 64 (0 - Z.of_nat k) ->
  w21 = Z_to_bv 64 (p + Z.of_nat k) ->
  evt rsegs POST
    (MS (mkR y1 sp gp tp y5 y6 y7 (Z_to_bv 64 c) (Z_to_bv 64 line) w10 w11 y12 y13 y14 y15 y16 y17
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) (Z_to_bv 64 1) w21 (Z_to_bv 64 0x1ff)
             (Z_to_bv 64 0x23) (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20)
             (Z_to_bv 64 0x3b) y28 y29 y30 y31)
        F (Z_to_bv 64 0x143d0) fc None m (seg_rom rsegs)).
Proof.
  induction j as [|j IH]; intros k m y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 w10 w11 w21
    FO H512 Hjk Hj HNC C40 C38 E10 E11 E21; [lia|]. subst w10 w11 w21.
  pose proof frt_facts as (HSP & HLO & HLO0 & HS63 & HP0 & HPB & HAP & HAC & HC0 & HC16 & HLN0 & HLN & HLL &
                           HFRM & HIMG & HM16).
  pose proof (frt_loop m FO) as LP.
  pose proof LP as LP2.
  destruct LP2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                   _ & _ & _ & _ & _ & _ & HC & _).
  assert (Hk : (k < length LL)%nat) by lia.
  destruct (frt_rd m p rest k HC ltac:(lia)) as (b & RDb & Eb).
  pose proof (frt_bv8_range b) as Rb.
  assert (Ebl : bv_unsigned b = nth k LL 0) by (rewrite Eb; apply mf_line_nth; lia).
  (* 0x14404: the cut point p + k is stored, then the strip call *)
  assert (CUT : forall (z12 z13 : word), cut_at LL k = true ->
    evt rsegs POST
      (MS (mkR y1 sp gp tp y5 y6 y7 (Z_to_bv 64 c) (Z_to_bv 64 line)
               (Z_to_bv 64 (p + Z.of_nat (length LL))) (Z_to_bv 64 (0 - Z.of_nat k)) z12 z13 y14 y15 y16 y17
               (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) (Z_to_bv 64 1)
               (Z_to_bv 64 (p + Z.of_nat k)) (Z_to_bv 64 0x1ff)
               (Z_to_bv 64 0x23) (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20)
               (Z_to_bv 64 0x3b) y28 y29 y30 y31)
          F (Z_to_bv 64 0x14404) fc None m (seg_rom rsegs))).
  { intros z12 z13 HCUT.
    pose proof FO as (MU & WM & MI & ST).
    destruct (frt_cells m ST) as (junk & FR).
    unfold cell8 in C40, C38.
    step.
    eapply (frt_strip_call _ k y1 y5 y6 y7 _ _ z12 z13 y14 y15 y16 y17 (Z_to_bv 64 1)
              (Z_to_bv 64 (p + Z.of_nat k)) y28 y29 y30 y31).
    - split; [exact MU | split; [exact WM | split; [exact MI | exact ST]]].
    - exact H512.
    - lia.
    - apply h_cut_idx; [lia | exact HNC | right; exact HCUT].
    - unfold cell8. exact C40.
    - unfold cell8. eapply frt_cell8_head. exact FR. }
  (* 0x143f4: no cut at k, go on *)
  assert (NEXT : forall (z12 z13 : word), cut_at LL k = false ->
    evt rsegs POST
      (MS (mkR y1 sp gp tp y5 y6 y7 (Z_to_bv 64 c) (Z_to_bv 64 line)
               (Z_to_bv 64 (p + Z.of_nat (length LL))) (Z_to_bv 64 (0 - Z.of_nat k)) z12 z13 y14 y15 y16 y17
               (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) (Z_to_bv 64 1)
               (Z_to_bv 64 (p + Z.of_nat k)) (Z_to_bv 64 0x1ff)
               (Z_to_bv 64 0x23) (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20)
               (Z_to_bv 64 0x3b) y28 y29 y30 y31)
          F (Z_to_bv 64 0x143f4) fc None m (seg_rom rsegs))).
  { intros z12 z13 HCF.
    step. step.
    step. if_cases Kb; cbv iota.
    - (* s5 + 1 <> a0: another byte *)
      zify_cond Kb. rewrite ?unsigned_lit in Kb by lia.
      eapply (IH (S k) m y1 y5 y6 y7 z12 z13 y14 y15 y16 y17 y28 y29 y30 y31);
        [ exact FO | exact H512 | lia | lia | | exact C40 | exact C38 | reflexivity | fweq | fweq ].
      intros i Hi. destruct (Nat.eq_dec i k) as [->|NE]; [exact HCF | apply HNC; lia].
    - (* s5 + 1 = a0: the line ends with no cut *)
      zify_cond Kb. rewrite ?unsigned_lit in Kb by lia.
      step.
      eapply (frt_strip_call m (length LL) y1 y5 y6 y7 _ _ z12 z13 y14 y15 y16 y17 (Z_to_bv 64 1)
                (Z_to_bv 64 (p + Z.of_nat k + 1)) y28 y29 y30 y31 FO H512 ltac:(lia)).
      + apply h_cut_idx; [lia | | left; reflexivity].
        intros i Hi. destruct (Nat.eq_dec i k) as [->|NE]; [exact HCF | apply HNC; lia].
      + exact C40.
      + exact C38. }
  (* 0x143dc: the byte is a mark *)
  assert (MARK : forall (z12 : word), is_mark (nth k LL 0) = true ->
    evt rsegs POST
      (MS (mkR y1 sp gp tp y5 y6 y7 (Z_to_bv 64 c) (Z_to_bv 64 line)
               (Z_to_bv 64 (p + Z.of_nat (length LL))) (Z_to_bv 64 (0 - Z.of_nat k)) z12 y13 y14 y15 y16 y17
               (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) (Z_to_bv 64 1)
               (Z_to_bv 64 (p + Z.of_nat k)) (Z_to_bv 64 0x1ff)
               (Z_to_bv 64 0x23) (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20)
               (Z_to_bv 64 0x3b) y28 y29 y30 y31)
          F (Z_to_bv 64 0x143dc) fc None m (seg_rom rsegs))).
  { intros z12 HM.
    step. if_cases Kz; cbv iota.
    - (* a1 = 0: k = 0, the mark starts the line *)
      assert (Hk0 : (k = 0)%nat)
        by (zify_cond Kz; rewrite ?unsigned_lit_wrap in Kz; Z.div_mod_to_equations; lia).
      apply CUT. unfold cut_at. rewrite HM. cbn [andb]. rewrite Hk0. reflexivity.
    - assert (Hk1 : (1 <= k)%nat)
        by (zify_cond Kz; rewrite ?unsigned_lit_wrap in Kz; Z.div_mod_to_equations; lia).
      step. if_cases Kt; cbv iota; [exfalso; zify_cond Kt; rewrite ?unsigned_lit in Kt by lia; lia|].
      destruct (frt_rd m p rest (k - 1) HC ltac:(lia)) as (b2 & RDb2 & Eb2).
      pose proof (frt_bv8_range b2) as Rb2.
      assert (Eb2l : bv_unsigned b2 = nth (k - 1) LL 0)
        by (rewrite Eb2; apply mf_line_nth; lia).
      step.
      step. if_cases Ks; cbv iota.
      + (* previous byte is ' ' *)
        apply CUT. unfold cut_at. rewrite HM. cbn [andb].
        apply orb_true_intro. right. unfold sp_tab. apply orb_true_intro. left.
        zify_cond Ks. rewrite ?frt_ub, ?unsigned_lit in Ks by lia.
        apply Z.eqb_eq. rewrite <- Eb2l. lia.
      + step.
        step. if_cases Kt2; cbv iota.
        * (* previous byte is '\t' *)
          apply CUT. unfold cut_at. rewrite HM. cbn [andb].
          apply orb_true_intro. right. unfold sp_tab. apply orb_true_intro. right.
          zify_cond Kt2. rewrite ?frt_ub, ?unsigned_lit in Kt2 by lia.
          apply Z.eqb_eq. rewrite <- Eb2l. lia.
        * (* neither: no cut here *)
          apply NEXT. unfold cut_at.
          apply andb_false_intro2. apply orb_false_intro; [apply Nat.eqb_neq; lia|].
          unfold sp_tab. apply orb_false_intro.
          -- zify_cond Ks. rewrite ?frt_ub, ?unsigned_lit in Ks by lia.
             apply Z.eqb_neq. rewrite <- Eb2l. lia.
          -- zify_cond Kt2. rewrite ?frt_ub, ?unsigned_lit in Kt2 by lia.
             apply Z.eqb_neq. rewrite <- Eb2l. lia. }
  (* 0x143d0 itself *)
  step.
  step. if_cases K1; cbv iota.
  - apply MARK.
    zify_cond K1. rewrite ?frt_ub, ?unsigned_lit in K1 by lia.
    unfold is_mark. apply orb_true_intro. right. apply Z.eqb_eq. rewrite <- Ebl. lia.
  - step. if_cases K2; cbv iota.
    + apply NEXT. unfold cut_at. apply andb_false_intro1.
      unfold is_mark. apply orb_false_intro.
      * zify_cond K2. rewrite ?frt_ub, ?unsigned_lit in K2 by lia.
        apply Z.eqb_neq. rewrite <- Ebl. lia.
      * zify_cond K1. rewrite ?frt_ub, ?unsigned_lit in K1 by lia.
        apply Z.eqb_neq. rewrite <- Ebl. lia.
    + apply MARK.
      zify_cond K2. rewrite ?frt_ub, ?unsigned_lit in K2 by lia.
      unfold is_mark. apply orb_true_intro. left. apply Z.eqb_eq. rewrite <- Ebl. lia.
Qed.

(** ** 0x143c8: the short line *)
Lemma frt_short : forall m (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (w10 w21 : word),
  frt_ok m -> (length LL < 512)%nat ->
  cell8 m (Sp + 0x40) p -> cell8 m (Sp + 0x38) (p + Z.of_nat (length LL)) ->
  w10 = Z_to_bv 64 (p + Z.of_nat (length LL)) -> w21 = Z_to_bv 64 p ->
  evt rsegs POST
    (MS (mkR y1 sp gp tp y5 y6 y7 (Z_to_bv 64 c) (Z_to_bv 64 line) w10 y11 y12 y13 y14 y15 y16 y17
             (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) (Z_to_bv 64 1) w21 (Z_to_bv 64 0x1ff)
             (Z_to_bv 64 0x23) (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20)
             (Z_to_bv 64 0x3b) y28 y29 y30 y31)
        F (Z_to_bv 64 0x143c8) fc None m (seg_rom rsegs)).
Proof.
  intros m y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 w10 w21 FO H512 C40 C38 E10 E21.
  subst w10 w21.
  pose proof frt_facts as (HSP & HLO & HLO0 & HS63 & HP0 & HPB & HAP & HAC & HC0 & HC16 & HLN0 & HLN & HLL &
                           HFRM & HIMG & HM16).
  step. if_cases K; cbv iota.
  - (* p >= p + |l| : the line is empty *)
    zify_cond K. rewrite ?unsigned_lit in K by lia.
    assert (EL : LL = []) by (apply length_zero_iff_nil; lia).
    eapply (frt_strip_call m (length LL) y1 y5 y6 y7 _ y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 1)
              (Z_to_bv 64 p) y28 y29 y30 y31 FO H512 ltac:(lia)).
    + rewrite EL. reflexivity.
    + exact C40.
    + exact C38.
  - zify_cond K. rewrite ?unsigned_lit in K by lia.
    step.
    eapply (frt_scan (length LL) 0%nat m y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31);
      [ exact FO | exact H512 | lia | lia | intros i Hi; lia | exact C40 | exact C38 | reflexivity
      | fweq | fweq ].
Qed.

(** ** 0x14394: line++ and the long-line test *)
Lemma frt_midl : forall m (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31 : word)
    (w10 w18 w21 : word),
  frt_ok m ->
  cell8 m (Sp + 0x40) p -> cell8 m (Sp + 0x38) (p + Z.of_nat (length LL)) ->
  w10 = Z_to_bv 64 (p + Z.of_nat (length LL)) -> w18 = Z_to_bv 64 (mf_next p rest) ->
  w21 = Z_to_bv 64 p ->
  evt rsegs POST
    (MS (mkR y1 sp gp tp y5 y6 y7 (Z_to_bv 64 c) (Z_to_bv 64 line) w10 y11 y12 y13 y14 y15 y16 y17
             w18 y19 (Z_to_bv 64 1) w21 (Z_to_bv 64 0x1ff)
             (Z_to_bv 64 0x23) (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20)
             (Z_to_bv 64 0x3b) y28 y29 y30 y31)
        F (Z_to_bv 64 0x14394) fc None m (seg_rom rsegs)).
Proof.
  intros m y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31 w10 w18 w21 FO C40 C38 E10 E18 E21.
  subst w10 w18 w21.
  pose proof frt_facts as (HSP & HLO & HLO0 & HS63 & HP0 & HPB & HAP & HAC & HC0 & HC16 & HLN0 & HLN & HLL &
                           HFRM & HIMG & HM16).
  step.
  rewrite (unsigned_lit line) by lia. rewrite (frt_swrap32 (line + 1)) by lia.
  step. if_cases K; cbv iota; [exfalso; zify_cond K; rewrite ?frt_signed_lit in K by lia; lia|].
  step. rewrite ?unsigned_lit by lia.
  step. if_cases K2; cbv iota.
  - (* 511 >= |l| : the short line *)
    eapply (frt_short m y1 y5 y6 y7 _ y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 _ _ FO);
      [ | exact C40 | exact C38 | reflexivity | reflexivity ].
    zify_cond K2. rewrite ?frt_signed_lit in K2 by lia. lia.
  - (* |l| >= 512 : LONG *)
    eapply frt_back; [exact FO|].
    eapply (HLG y1 sp gp tp y5 y6 y7 (Z_to_bv 64 c) (Z_to_bv 64 line)
              (Z_to_bv 64 (p + Z.of_nat (length LL))) _ y12 y13 y14 y15 y16 y17
              (Z_to_bv 64 (mf_next p rest)) (Z_to_bv 64 (line + 1)) (Z_to_bv 64 1) (Z_to_bv 64 p)
              (Z_to_bv 64 0x1ff) (Z_to_bv 64 0x23) (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK)
              (Z_to_bv 64 0x20) (Z_to_bv 64 0x3b) y28 y29 y30 y31 F fc m lo
              ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc cur k0 rest).
    + lia.
    + exact Hrest.
    + apply frt_loop. exact FO.
    + unfold mfu_lregs. repeat split; reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + zify_cond K2. rewrite ?frt_signed_lit in K2 by lia. lia.
Qed.

(** strchr's answer on the text left: the line's end, or none. *)
Lemma frt_break_cases :
  (memchr rest NL = Some (length LL) /\
   (length rest - length (mf_rest rest))%nat = S (length LL) /\ (length LL < length rest)%nat)
  \/ (memchr rest NL = None /\ LL = rest /\ (length rest - length (mf_rest rest))%nat = length LL).
Proof.
  assert (NI : ~ In NL LL).
  { unfold mf_line. destruct (break_nl rest) as [l q] eqn:Eb. cbn [fst].
    destruct (break_nl_spec rest l q Eb) as [N _]. exact N. }
  destruct (mf_line_rest rest) as [[E1 E2]|[E1 [E2 E3]]].
  - left. split; [apply (frt_memchr_split rest LL (mf_rest rest) NL E1 NI)|].
    split; [exact E2 | lia].
  - right. split; [apply (frt_memchr_none_eq rest LL NL E1 NI)|].
    split; [symmetry; exact E1 | exact E3].
Qed.

(** ** 0x14348: the head *)
Lemma frt_head : forall (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y21 y28 y29 y30 y31 : word),
  evt rsegs POST
    (MS (mkR y1 sp gp tp y5 y6 y7 (Z_to_bv 64 c) y9 y10 y11 y12 y13 y14 y15 y16 y17
             (Z_to_bv 64 p) (Z_to_bv 64 line) (Z_to_bv 64 1) y21 (Z_to_bv 64 0x1ff)
             (Z_to_bv 64 0x23) (Z_to_bv 64 (c + MC_N)) (Z_to_bv 64 BLANK_MASK) (Z_to_bv 64 0x20)
             (Z_to_bv 64 0x3b) y28 y29 y30 y31)
        F (Z_to_bv 64 M_FILE_HEAD) fc None m0 (seg_rom rsegs)).
Proof.
  intros y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y21 y28 y29 y30 y31.
  pose proof frt_facts as (HSP & HLO & HLO0 & HS63 & HP0 & HPB & HAP & HAC & HC0 & HC16 & HLN0 & HLN & HLL &
                           HFRM & HIMG & HM16).
  pose proof HLOOP as HL.
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                  _ & _ & _ & _ & _ & _ & QC & QA & _ & _ & _ & _ & QS & QMI).
  destruct QS as (ST0 & _ & _ & _).
  destruct (cstr_cut rsegs m0 p rest QC) as (bs & sl & HB & Hz & Hnn & Hnb & Hlb & Hmod & Hsl8).
  pose proof (bytes_at_bound rsegs m0 p _ HB) as HBB.
  rewrite length_app in HBB. cbn [length] in HBB.
  unfold apart in QA.
  assert (STlo : stk rsegs m0 lo Sp) by (destruct (stk_split rsegs m0 lo Sp Sp0 ST0 ltac:(lia)); assumption).
  assert (SThi : stk rsegs m0 Sp Sp0) by (destruct (stk_split rsegs m0 lo Sp Sp0 ST0 ltac:(lia)); assumption).
  unfold M_FILE_HEAD.
  step. step. step. step. step.
  eapply evt_cut.
  { eapply (HCHR) with (str := bs) (slack := sl) (lo := lo).
    - exact STlo.
    - rewrite unsigned_lit by lia. exact HB.
    - exact Hnb.
    - rewrite unsigned_lit by lia. exact Hmod.
    - exact QMI.
    - lia.
    - rewrite unsigned_lit by lia. lia. }
  intros ms' (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m1 & -> &
              MU1 & WM1 & MI1 & ST1 & BA1).
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite (unsigned_lit p) by lia.
  erewrite frt_strchr_val by (rewrite unsigned_lit by lia; reflexivity).
  rewrite Hz.
  assert (STa : stk rsegs m1 lo Sp0).
  { eapply stk_merge; [exact ST1 | | lia].
    eapply stk_transport_disjoint; [exact SThi | exact MU1 | exact WM1 |].
    cbn [disjoint_from]. split; [lia | exact I]. }
  assert (MUa : munch WF m0 m1).
  { eapply munch_weaken; [|exact MU1]. unfold sub_fp. intros x HX. cbn [outside] in *.
    split; [lia | exact I]. }
  assert (FO1 : frt_ok m1) by (split; [exact MUa | split; [exact WM1 | split; [exact MI1 | exact STa]]]).
  assert (HB1 : bytes_at rsegs m1 p (bs ++ Z_to_bv 8 0 :: sl)).
  { eapply bytes_at_transport; [exact HB | exact MU1 |].
    rewrite length_app. cbn [length]. cbn [disjoint_from]. split; [lia | exact I]. }
  clear MU1 BA1 ST1.
  destruct (frt_cells m1 STa) as (junk & FR).
  destruct (frt_break_cases) as [(EM & EN & _)|(EM & EL & ER)].
  - (* a newline: a0 = p + |l| *)
    rewrite EM.
    step.
    step. if_cases K0; cbv iota; [exfalso; zify_cond K0; rewrite ?unsigned_lit in K0 by lia; lia|].
    step. step.
    step. if_cases K1; cbv iota; [exfalso; zify_cond K1; rewrite ?unsigned_lit in K1 by lia; lia|].
    step. step.
    eapply frt_midl;
      [ | | | fweq | unfold mf_next; rewrite EN; fweq | fweq ].
    + split; [assumption | split; [assumption | split; [assumption | assumption]]].
    + unfold cell8. eapply frt_cell8_pair_at; [exact FR | lia].
    + unfold cell8. exact (proj1 (frt_cell8_pair _ _ _ _ FR)).
  - (* no newline: strlen *)
    rewrite EM.
    step.
    step. if_cases K0; cbv iota; [|exfalso; zify_cond K0; rewrite ?unsigned_lit in K0 by lia; lia].
    step. step.
    eapply evt_cut.
    { eapply (HSLEN) with (str := bs) (slack := sl).
      - rewrite unsigned_lit by lia. exact HB1.
      - exact Hnb.
      - rewrite unsigned_lit by lia. exact Hmod.
      - assumption. }
    intros ms' (v5 & v6 & v7 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m2 & -> &
                MU2 & WM2 & MI2 & BA2).
    rewrite ret_pc_even by (try lia; reflexivity).
    assert (ELn : length bs = length LL) by (rewrite Hlb, EL; reflexivity).
    rewrite ELn.
    assert (FR2 : rw_cells rsegs m2 (Sp + 0x38) _)
      by (eapply rw_cells_transport; [exact FR | exact MU2 | exact WM2 | cbn [disjoint_from]; exact I]).
    assert (STb : stk rsegs m2 lo Sp0)
      by (eapply stk_transport_disjoint; [exact STa | exact MU2 | exact WM2 | cbn [disjoint_from]; exact I]).
    assert (MUb : munch WF m0 m2).
    { eapply munch_trans; [exact MUa|].
      eapply (munch_weaken [] WF); [intros x HX; exact I | exact MU2]. }
    assert (WMb : wmono rsegs m0 m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
    clear FR MU2 WM2 MUa STa WM1.
    step.
    step. if_cases K2; cbv iota; [exfalso; zify_cond K2; rewrite ?zb_lxor_ones in K2 by lia;
                                  rewrite ?unsigned_lit in K2 by lia; lia|].
    step. step. step.
    eapply frt_midl;
      [ | | | fweq | unfold mf_next; rewrite ER; fweq | fweq ].
    + split; [exact MUb | split; [exact WMb | split; [exact MI2 | exact STb]]].
    + unfold cell8. eapply frt_cell8_pair_at; [exact FR2 | lia].
    + unfold cell8. exact (proj1 (frt_cell8_pair _ _ _ _ FR2)).
Qed.

End Front.

Theorem mfu_front_holds : strchr_contract -> strlen_contract -> strip_contract -> S_MFU_FRONT.
Proof.
  intros HC HL HS n HTT HLGG HHDD HKYY.
  unfold H_MF_HEAD.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc cur k0 rest Hnn Hrr HLL HRR.
  destruct HRR as (R0 & R2 & R3 & R4 & R6 & R7 & R8 & R9 & R10 & R11).
  subst s0 s2 s3 s4 s6 s7 s8 s9 s10 s11.
  rewrite (mf_fin_head (mc, cur) line rest Hrr).
  eapply frt_head; eassumption.
Qed.
