From Stdlib Require Import ZArith NArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import StrStr StrFun StrFun2 StrBytes StrWin.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import strchr_c strchr fourbyte_strstr_c twoway_strstr_c strstr_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require fourbyte_strstr twoway_strstr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_word_eq_tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require StepFast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.zstep ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.StepFast.sf_zstep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.TacDiet2.diet_word_eq_tac ].
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Stor0fe.sb_mem_after_store.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require AndN.
Import ListNotations.
Open Scope Z_scope.

Lemma ss_tobv_mod : forall e, Z_to_bv 64 (e mod 18446744073709551616) = Z_to_bv 64 e.
Proof.
  intros e. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
  apply Z.mod_mod. lia.
Qed.

Lemma ss_bytes_skip : forall segs m A (bs : list byte) k, bytes_at segs m A bs -> (k <= length bs)%nat ->
  bytes_at segs m (A + Z.of_nat k) (skipn k bs).
Proof.
  intros segs m A bs k (Ha & Hl & H) Hk. split; [lia|]. rewrite length_skipn. split; [lia|].
  intros j Hj. rewrite nth_error_skipn, <- H by lia.
  replace (A + Z.of_nat k + Z.of_nat j) with (A + Z.of_nat (k + j)) by lia. reflexivity.
Qed.

Lemma ss_bytes_prefix : forall segs m A (l1 l2 : list byte), bytes_at segs m A (l1 ++ l2) -> bytes_at segs m A l1.
Proof.
  intros segs m A l1 l2 (Ha & Hl & H). rewrite length_app in Hl. split; [lia|]. split; [lia|].
  intros i Hi. rewrite H by (rewrite length_app; lia). apply nth_error_app1. exact Hi.
Qed.

Lemma ss_bytes_str : forall segs m A (t hs : list byte), bytes_at segs m A (t ++ Z_to_bv 8 0 :: hs) ->
  bytes_at segs m A (t ++ [Z_to_bv 8 0]).
Proof.
  intros segs m A t hs H. replace (t ++ Z_to_bv 8 0 :: hs) with ((t ++ [Z_to_bv 8 0]) ++ hs) in H
    by (rewrite <- app_assoc; reflexivity).
  exact (ss_bytes_prefix _ _ _ _ _ H).
Qed.

Lemma ss_val_nil : forall A (hb : list byte), strstr_val A hb [] = A.
Proof. intros A hb. unfold strstr_val. cbn [map]. rewrite sw_ff_head by reflexivity. lia. Qed.

Ltac rd0 M HB A i addr :=
  let z := fresh "z" in let RD := fresh "RD" in let Hz := fresh "Hz" in
  assert (RD : ov_read_bytes rsegs M addr 1 = Some [Z_to_bv 8 0])
    by (apply (sb_rd1 rsegs M A _ i _ addr HB); [reflexivity | rewrite ?unsigned_lit by lia; lia]);
  set (z := Z_to_bv 8 0) in RD;
  assert (Hz : bv_unsigned z = 0) by reflexivity;
  clearbody z.

Ltac rdb M HB A i addr b :=
  let RD := fresh "RD" in
  assert (RD : ov_read_bytes rsegs M addr 1 = Some [b])
    by (apply (sb_rd1 rsegs M A _ i _ addr HB); [reflexivity | rewrite ?unsigned_lit by lia; lia]).

Section Tail.
Variables (FB : fourbyte_strstr_contract) (TW : twoway_strstr_contract).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 : word) (F : bvmap 5 word) (fc : bv 32)
          (m m2 : word -> option byte) (hb hs nb : list byte) (lo : Z) (g : word).
Hypothesis LO : lo <= bv_unsigned sp - 2256.
Hypothesis NN : ~ In (Z_to_bv 8 0) nb.
Hypothesis SN : bv_unsigned a1 + Z.of_nat (length nb) + 1 <= bv_unsigned sp - 2256 \/ bv_unsigned sp <= bv_unsigned a1.
Hypothesis SH : bv_unsigned a0 + Z.of_nat (length hb) + 1 + Z.of_nat (length hs) <= bv_unsigned sp - 2256
                \/ bv_unsigned sp <= bv_unsigned a0.
Hypothesis GL : GUARD + 8 <= bv_unsigned sp - 2256.
Hypothesis GGL : GOT_GUARD + 8 <= bv_unsigned sp - 2256.
Hypothesis MU2 : munch [(bv_unsigned sp - 2256, bv_unsigned sp)] m m2.
Hypothesis WM2 : wmono rsegs m m2.
Hypothesis MI2 : mem_inv rsegs m2.
Hypothesis ST2 : stk rsegs m2 lo (bv_unsigned sp + -16).
Hypothesis FR2 : rw_cells rsegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra].
Hypothesis HH2 : bytes_at rsegs m2 (bv_unsigned a0) (hb ++ Z_to_bv 8 0 :: hs).
Hypothesis HN2 : bytes_at rsegs m2 (bv_unsigned a1) (nb ++ [Z_to_bv 8 0]).
Hypothesis GG2 : bytes_at rsegs m2 GOT_GUARD (le8 (Z_to_bv 64 GUARD)).
Hypothesis GD2 : bytes_at rsegs m2 GUARD (le8 g).

Notation POSTQ := (strstr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 hb hs nb lo m).
Notation XS pc x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
  (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 x8 s1 x10 x11 x12 x13 x14 x15 x16 x17
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 pc) fc None m2 (seg_rom rsegs)).

Lemma ex_ret : forall pc x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  (pc = 0x1f1cc \/ pc = 0x1f188 \/ pc = 0x1f134 \/ pc = 0x1f204) ->
  x10 = Z_to_bv 64 (strstr_val (bv_unsigned a0) hb nb) ->
  evt rsegs POSTQ (XS pc x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
Proof.
  intros pc x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hpc ->.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ST2 as ST. pose proof FR2 as FR. pose proof ST2 as [LO0 _].
  destruct Hpc as [Hp|[Hp|[Hp|Hp]]]; subst pc.
  all: zstep; zstep; zstep; zstep; release_frame FR ST (bv_unsigned sp).
  all: apply evt_done; unfold strstr_post; repeat (lazymatch goal with |- ex _ => eexists end).
  all: (split; [reflexivity|]); OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.AndN.and_splits; assumption.
Qed.

Lemma f77c : forall x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  (bv_unsigned x13 = 0 -> strstr_val (bv_unsigned a0) hb nb = 0) ->
  (bv_unsigned x13 <> 0 -> Z_to_bv 64 (strstr_val (bv_unsigned a0) hb nb) = x10) ->
  evt rsegs POSTQ (XS 0x1f1f8 x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
Proof.
  intros x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 H0 H1.
  pose proof (bv_unsigned_in_range 64 x13) as R13. unfold bv_modulus in R13. cbn in R13.
  pose proof (bv_unsigned_in_range 64 x10) as R10. unfold bv_modulus in R10. cbn in R10.
  zstep. zstep. zstep.
  rewrite sw_mask77 by lia.
  destruct (Z.eqb_spec (bv_unsigned x13) 0) as [E|E]; cbv iota.
  - apply ex_ret; [lia|]. rewrite (H0 E). reflexivity.
  - rewrite Z_to_bv_bv_unsigned. apply ex_ret; [lia|]. symmetry. exact (H1 E).
Qed.

Lemma two_loop : forall (k p : nat) (A' : Z) (t : list byte) (b0 b1 cp cp1 : byte)
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  nb = [b0; b1] -> (length t - p = k)%nat ->
  bytes_at rsegs m2 A' (t ++ Z_to_bv 8 0 :: hs) -> ~ In (Z_to_bv 8 0) t ->
  nth_error t p = Some cp -> nth_error t (S p) = Some cp1 ->
  bv_unsigned x10 = A' + Z.of_nat p ->
  bv_unsigned x11 = bv_unsigned cp * 256 + bv_unsigned cp1 ->
  bv_unsigned x12 = bv_unsigned b0 * 256 + bv_unsigned b1 ->
  (forall j, (j <= p)%nat -> prefix_eqb (map bv_unsigned nb) (skipn j (map bv_unsigned t)) = false) ->
  strstr_val (bv_unsigned a0) hb nb = strstr_val A' t nb ->
  evt rsegs POSTQ (XS 0x1f160 x1 x5 x6 x7 a1 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
Proof.
  induction k as [k IH] using lt_wf_ind.
  intros p A' t b0 b1 cp cp1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
         ENB Hk HT NT Ep Ep1 H10 H11 H12 NOM VAL.
  pose proof (bytes_at_bound _ _ _ _ HT) as BT. rewrite length_app in BT. cbn [length] in BT.
  pose proof (nth_error_lt _ _ _ Ep1) as Lp1.
  destruct (sw_nth_full t hs (S (S p)) ltac:(lia)) as (b & Eb & Ebl & Ebe).
  pose proof (sw_byte_range b) as Rb. pose proof (sw_byte_range cp1) as R1. pose proof (sw_byte_range cp) as R0.
  pose proof (sw_byte_range b0) as Rn0. pose proof (sw_byte_range b1) as Rn1.
  assert (RD : ov_read_bytes rsegs m2 (Z_to_bv 64 (bv_unsigned x10 + 2)) 1 = Some [b]).
  { apply (sb_rd1 rsegs m2 A' _ (S (S p)) b _ HT Eb). rewrite unsigned_lit by lia. lia. }
  zstep. zstep. zstep. zstep. rewrite ?sw_land255. if_cases K; zify_cond K; rewrite ?sw_land255 in K.
  - assert (Hend : S (S p) = length t).
    { destruct (Nat.eq_dec (S (S p)) (length t)) as [E|NE]; [exact E|]. exfalso.
      exact (sw_nz t _ b NT (Ebl ltac:(lia)) K). }
    apply f77c.
    + intros _. rewrite VAL. apply sw_val_none_all. intros j Hj.
      destruct (Nat.le_gt_cases j p) as [Hjp|Hjp]; [exact (NOM j Hjp)|].
      apply sw_short_at; rewrite ENB; cbn [length]; lia.
    + intros Hb. exfalso. rewrite unsigned_lit in Hb by lia. exact (Hb K).
  - assert (Hlt : (S (S p) < length t)%nat).
    { destruct (Nat.eq_dec (S (S p)) (length t)) as [E|NE]; [|lia]. exfalso. apply K. rewrite (Ebe E). reflexivity. }
    pose proof (Ebl Hlt) as Ep2.
    zstep. zstep. zstep. zstep.
    rewrite (sw_w2_loop (bv_unsigned x11) (bv_unsigned b)) by lia.
    rewrite H11, sw_mod256 by lia.
    if_cases K2; zify_cond K2; rewrite H12 in K2.
    + eapply (IH (length t - S p)%nat ltac:(lia) (S p) A' t b0 b1 cp1 b);
        [exact ENB | lia | exact HT | exact NT | exact Ep1 | exact Ep2
        | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; reflexivity | exact H12 | | exact VAL].
      intros j Hj. destruct (Nat.eq_dec j (S p)) as [Ej|NE]; [|apply NOM; lia]. subst j.
      destruct (prefix_eqb _ _) eqn:E; [|reflexivity]. exfalso. rewrite ENB in E.
      apply (sw_win2 b0 b1 cp1 b t (S p) Ep1 Ep2) in E. lia.
    + zstep. apply f77c.
      * intros Hb. exfalso. rewrite unsigned_lit in Hb by lia. exact (K Hb).
      * intros _. rewrite VAL, (sw_val_found A' t nb (S p)).
        -- f_equal. lia.
        -- intros j Hj. apply NOM. lia.
        -- rewrite ENB. apply (sw_win2 b0 b1 cp1 b t (S p) Ep1 Ep2). lia.
Qed.

Lemma two_entry : forall (A' : Z) (t t' : list byte) (b0 b1 c0 c1 : byte)
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  nb = [b0; b1] -> t = c0 :: c1 :: t' -> bv_unsigned c0 = bv_unsigned b0 ->
  bytes_at rsegs m2 A' (t ++ Z_to_bv 8 0 :: hs) -> ~ In (Z_to_bv 8 0) t ->
  bv_unsigned x10 = A' -> bv_unsigned x11 = bv_unsigned c1 -> bv_unsigned x12 = bv_unsigned b1 ->
  strstr_val (bv_unsigned a0) hb nb = strstr_val A' t nb ->
  evt rsegs POSTQ (XS 0x1f144 x1 x5 x6 x7 a1 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
Proof.
  intros A' t t' b0 b1 c0 c1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
         ENB ET E0 HT NT H10 H11 H12 VAL.
  pose proof (bytes_at_bound _ _ _ _ HT) as BT. rewrite length_app in BT. cbn [length] in BT.
  pose proof HN2 as HN. rewrite ENB in HN.
  pose proof (bytes_at_bound _ _ _ _ HN) as BN. rewrite length_app in BN. cbn [length] in BN.
  pose proof (sw_byte_range c0) as Rc0. pose proof (sw_byte_range c1) as Rc1.
  pose proof (sw_byte_range b0) as Rb0. pose proof (sw_byte_range b1) as Rb1.
  assert (E0t : nth_error t 0 = Some c0) by (rewrite ET; reflexivity).
  assert (E1t : nth_error t 1 = Some c1) by (rewrite ET; reflexivity).
  rdb m2 HN (bv_unsigned a1) 0%nat a1 b0.
  subst t. rdb m2 HT A' 0%nat x10 c0.
  do 7 zstep.
  rewrite H11, H12, !sw_w2_entry by lia.
  if_cases K; zify_cond K.
  - apply ex_ret; [lia|]. rewrite VAL, (sw_val_found A' _ nb 0).
    + replace (A' + Z.of_nat 0) with (bv_unsigned x10) by lia. symmetry. apply Z_to_bv_bv_unsigned.
    + intros j Hj. lia.
    + rewrite ENB. apply (sw_win2 b0 b1 c0 c1 _ 0 E0t E1t). lia.
  - eapply (two_loop (length (c0 :: c1 :: t') - 0)%nat 0%nat A' (c0 :: c1 :: t') b0 b1 c0 c1);
      [exact ENB | lia | exact HT | exact NT | exact E0t | exact E1t
      | lia | rewrite unsigned_lit by lia; reflexivity | rewrite unsigned_lit by lia; reflexivity | | exact VAL].
    intros j Hj. replace j with 0%nat by lia.
    destruct (prefix_eqb _ _) eqn:E; [|reflexivity]. exfalso. rewrite ENB in E.
    apply (sw_win2 b0 b1 c0 c1 _ 0 E0t E1t) in E. lia.
Qed.

Lemma three_loop : forall (k p : nat) (A' : Z) (t : list byte) (b0 b1 b2 cp cp1 cp2 : byte)
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  nb = [b0; b1; b2] -> (length t - p = k)%nat ->
  bytes_at rsegs m2 A' (t ++ Z_to_bv 8 0 :: hs) -> ~ In (Z_to_bv 8 0) t ->
  nth_error t p = Some cp -> nth_error t (S p) = Some cp1 -> nth_error t (S (S p)) = Some cp2 ->
  bv_unsigned x10 = A' + Z.of_nat p ->
  bv_unsigned x11 = w3 (bv_unsigned b0) (bv_unsigned b1) (bv_unsigned b2) ->
  bv_unsigned x12 = w3 (bv_unsigned cp) (bv_unsigned cp1) (bv_unsigned cp2) ->
  (forall j, (j <= p)%nat -> prefix_eqb (map bv_unsigned nb) (skipn j (map bv_unsigned t)) = false) ->
  strstr_val (bv_unsigned a0) hb nb = strstr_val A' t nb ->
  evt rsegs POSTQ (XS 0x1f1dc x1 x5 x6 x7 a1 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
Proof.
  induction k as [k IH] using lt_wf_ind.
  intros p A' t b0 b1 b2 cp cp1 cp2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
         ENB Hk HT NT Ep Ep1 Ep2 H10 H11 H12 NOM VAL.
  pose proof (bytes_at_bound _ _ _ _ HT) as BT. rewrite length_app in BT. cbn [length] in BT.
  pose proof (nth_error_lt _ _ _ Ep2) as Lp2.
  destruct (sw_nth_full t hs (S (S (S p))) ltac:(lia)) as (b & Eb & Ebl & Ebe).
  pose proof (sw_byte_range b) as Rb. pose proof (sw_byte_range cp) as R0.
  pose proof (sw_byte_range cp1) as R1. pose proof (sw_byte_range cp2) as R2.
  pose proof (sw_byte_range b0) as Rn0. pose proof (sw_byte_range b1) as Rn1. pose proof (sw_byte_range b2) as Rn2.
  assert (RD : ov_read_bytes rsegs m2 (Z_to_bv 64 (bv_unsigned x10 + 3)) 1 = Some [b]).
  { apply (sb_rd1 rsegs m2 A' _ (S (S (S p))) b _ HT Eb). rewrite unsigned_lit by lia. lia. }
  zstep. zstep. zstep. zstep. rewrite ?sw_land255. if_cases K; zify_cond K; rewrite ?sw_land255 in K.
  - assert (Hend : S (S (S p)) = length t).
    { destruct (Nat.eq_dec (S (S (S p))) (length t)) as [E|NE]; [exact E|]. exfalso.
      exact (sw_nz t _ b NT (Ebl ltac:(lia)) K). }
    apply f77c.
    + intros _. rewrite VAL. apply sw_val_none_all. intros j Hj.
      destruct (Nat.le_gt_cases j p) as [Hjp|Hjp]; [exact (NOM j Hjp)|].
      apply sw_short_at; rewrite ENB; cbn [length]; lia.
    + intros Hb. exfalso. rewrite unsigned_lit in Hb by lia. exact (Hb K).
  - assert (Hlt : (S (S (S p)) < length t)%nat).
    { destruct (Nat.eq_dec (S (S (S p))) (length t)) as [E|NE]; [|lia]. exfalso. apply K. rewrite (Ebe E). reflexivity. }
    pose proof (Ebl Hlt) as Ep3.
    zstep. zstep. zstep.
    if_cases K2; zify_cond K2; rewrite H12, sw_w3_loop, H11 in K2 by lia.
    + eapply (IH (length t - S p)%nat ltac:(lia) (S p) A' t b0 b1 b2 cp1 cp2 b);
        [exact ENB | lia | exact HT | exact NT | exact Ep1 | exact Ep2 | exact Ep3
        | rewrite unsigned_lit by lia; lia | exact H11 | | | exact VAL].
      * rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
        rewrite H12. apply sw_w3_loop; lia.
      * intros j Hj. destruct (Nat.eq_dec j (S p)) as [Ej|NE]; [|apply NOM; lia]. subst j.
        destruct (prefix_eqb _ _) eqn:E; [|reflexivity]. exfalso. rewrite ENB in E.
        apply (sw_win3 b0 b1 b2 cp1 cp2 b t (S p) Ep1 Ep2 Ep3) in E. destruct E as (E1 & E2 & E3).
        apply K2. rewrite E1, E2, E3. reflexivity.
    + apply f77c.
      * intros Hb. exfalso. rewrite unsigned_lit in Hb by lia. exact (K Hb).
      * intros _. rewrite VAL, (sw_val_found A' t nb (S p)).
        -- f_equal. lia.
        -- intros j Hj. apply NOM. lia.
        -- rewrite ENB. apply (sw_win3 b0 b1 b2 cp1 cp2 b t (S p) Ep1 Ep2 Ep3).
           apply (sw_w3_inj _ _ _ _ _ _ R1 R2 Rb Rn0 Rn1 Rn2). exact K2.
Qed.

Lemma three_entry : forall (A' : Z) (t t' : list byte) (b0 b1 b2 c0 c1 c2 : byte)
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  nb = [b0; b1; b2] -> t = c0 :: c1 :: c2 :: t' -> bv_unsigned c0 = bv_unsigned b0 ->
  bytes_at rsegs m2 A' (t ++ Z_to_bv 8 0 :: hs) -> ~ In (Z_to_bv 8 0) t ->
  bv_unsigned x10 = A' -> bv_unsigned x11 = bv_unsigned c1 -> bv_unsigned x12 = bv_unsigned b1 ->
  bv_unsigned x13 = bv_unsigned c2 -> bv_unsigned x14 = bv_unsigned b2 ->
  strstr_val (bv_unsigned a0) hb nb = strstr_val A' t nb ->
  evt rsegs POSTQ (XS 0x1f198 x1 x5 x6 x7 a1 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
Proof.
  intros A' t t' b0 b1 b2 c0 c1 c2 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
         ENB ET E0 HT NT H10 H11 H12 H13 H14 VAL.
  pose proof (bytes_at_bound _ _ _ _ HT) as BT. rewrite length_app in BT. cbn [length] in BT.
  pose proof HN2 as HN. rewrite ENB in HN.
  pose proof (bytes_at_bound _ _ _ _ HN) as BN. rewrite length_app in BN. cbn [length] in BN.
  pose proof (sw_byte_range c0) as Rc0. pose proof (sw_byte_range c1) as Rc1. pose proof (sw_byte_range c2) as Rc2.
  pose proof (sw_byte_range b0) as Rb0. pose proof (sw_byte_range b1) as Rb1. pose proof (sw_byte_range b2) as Rb2.
  assert (E0t : nth_error t 0 = Some c0) by (rewrite ET; reflexivity).
  assert (E1t : nth_error t 1 = Some c1) by (rewrite ET; reflexivity).
  assert (E2t : nth_error t 2 = Some c2) by (rewrite ET; reflexivity).
  rdb m2 HN (bv_unsigned a1) 0%nat a1 b0.
  subst t. rdb m2 HT A' 0%nat x10 c0.
  do 13 zstep.
  if_cases K; zify_cond K; rewrite H11, H12, H13, H14, !sw_w3_entry in K by lia.
  - eapply (three_loop (length (c0 :: c1 :: c2 :: t') - 0)%nat 0%nat A' (c0 :: c1 :: c2 :: t') b0 b1 b2 c0 c1 c2);
      [exact ENB | lia | exact HT | exact NT | exact E0t | exact E1t | exact E2t | lia | | | | exact VAL].
    + rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
      rewrite H14, H12, sw_w3_entry by lia. apply Z.mod_small. apply sw_w3_range; lia.
    + rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
      rewrite H13, H11, sw_w3_entry by lia. apply Z.mod_small. apply sw_w3_range; lia.
    + intros j Hj. replace j with 0%nat by lia.
      destruct (prefix_eqb _ _) eqn:E; [|reflexivity]. exfalso. rewrite ENB in E.
      apply (sw_win3 b0 b1 b2 c0 c1 c2 _ 0 E0t E1t E2t) in E. destruct E as (E1 & E2 & E3).
      apply K. rewrite E1, E2, E3. reflexivity.
  - apply ex_ret; [lia|]. rewrite VAL, (sw_val_found A' _ nb 0).
    + replace (A' + Z.of_nat 0) with (bv_unsigned x10) by lia. symmetry. apply Z_to_bv_bv_unsigned.
    + intros j Hj. lia.
    + rewrite ENB. apply (sw_win3 b0 b1 b2 c0 c1 c2 _ 0 E0t E1t E2t).
      apply (sw_w3_inj _ _ _ _ _ _ Rc0 Rc1 Rc2 Rb0 Rb1 Rb2). exact K.
Qed.

Lemma four_tail : forall (A' : Z) (t : list byte) (b0 b1 b2 b3 : byte)
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  nb = [b0; b1; b2; b3] -> (4 <= length t)%nat ->
  bytes_at rsegs m2 A' (t ++ Z_to_bv 8 0 :: hs) -> ~ In (Z_to_bv 8 0) t -> bv_unsigned x10 = A' ->
  strstr_val (bv_unsigned a0) hb nb = strstr_val A' t nb ->
  evt rsegs POSTQ (XS 0x1f214 x1 x5 x6 x7 a1 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
Proof.
  intros A' t b0 b1 b2 b3 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 ENB Lt HT NT H10 VAL.
  pose proof FB as FB'. unfold fourbyte_strstr_contract, FOURBYTE_STRSTR in FB'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ST2 as ST. pose proof FR2 as FR. pose proof ST2 as [LO0 _].
  zstep. zstep. zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  eapply evt_cut.
  { eapply FB' with (hb := t) (n4 := nb).
    - rewrite H10. exact (ss_bytes_str _ _ _ _ _ HT).
    - exact NT.
    - lia.
    - exact (ss_bytes_prefix _ _ _ _ _ HN2).
    - rewrite ENB. reflexivity.
    - exact NN. }
  intros ms' (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & ->).
  apply evt_done. unfold strstr_post.
  exists y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m2.
  split. { rewrite H10, <- VAL. reflexivity. }
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.AndN.and_splits; assumption.
Qed.

Lemma tw_tail : forall (A' : Z) (t : list byte) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  nb <> [] -> bytes_at rsegs m2 A' (t ++ Z_to_bv 8 0 :: hs) -> ~ In (Z_to_bv 8 0) t -> bv_unsigned x10 = A' ->
  (- (A' + Z.of_nat (length t) + 1)) mod 8 <= Z.of_nat (length hs) ->
  (A' + Z.of_nat (length t) + 1 + Z.of_nat (length hs) <= bv_unsigned sp - 2256 \/ bv_unsigned sp <= A') ->
  strstr_val (bv_unsigned a0) hb nb = strstr_val A' t nb ->
  evt rsegs POSTQ (XS 0x1f11c x1 x5 x6 x7 a1 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
Proof.
  intros A' t x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 NE HT NT H10 PADt SHt VAL.
  pose proof TW as TW'. unfold twoway_strstr_contract, TWOWAY_STRSTR in TW'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ST2 as ST. pose proof FR2 as FR. pose proof ST2 as [LO0 _].
  pose proof (bytes_at_bound _ _ _ _ HH2) as BH. rewrite length_app in BH. cbn [length] in BH.
  zstep. zstep. zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  eapply evt_cut.
  { eapply TW' with (hb := t) (hs := hs) (nb := nb) (lo := lo) (g := g).
    - exact ST.
    - lia.
    - rewrite H10. exact HT.
    - exact NT.
    - rewrite H10. exact PADt.
    - exact HN2.
    - exact NN.
    - exact NE.
    - exact MI2.
    - rewrite H10. lia.
    - lia.
    - exact GG2.
    - exact GD2.
    - lia.
    - lia. }
  intros ms' (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & -> & MU' & WM' & MI' & ST' & HT' & HN').
  apply evt_done. unfold strstr_post.
  exists y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m'.
  split. { rewrite H10, <- VAL. reflexivity. }
  split. { eapply munch_trans; [exact MU2|]. eapply munch_weaken; [|exact MU'].
           unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | exact I]. }
  split. { eapply wmono_trans; eassumption. }
  split. { exact MI'. }
  split. { exact ST'. }
  split. { eapply bytes_at_transport; [exact HH2 | exact MU' |]. cbn [disjoint_from].
           rewrite length_app. cbn [length]. split; [lia | exact I]. }
  exact HN'.
Qed.

Lemma tail : forall (A' : Z) (t t' nb' : list byte) (c0 b0 : byte)
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  t = c0 :: t' -> nb = b0 :: nb' -> bv_unsigned c0 = bv_unsigned b0 -> bv_unsigned x10 = A' ->
  bytes_at rsegs m2 A' (t ++ Z_to_bv 8 0 :: hs) -> ~ In (Z_to_bv 8 0) t ->
  (- (A' + Z.of_nat (length t) + 1)) mod 8 <= Z.of_nat (length hs) ->
  (A' + Z.of_nat (length t) + 1 + Z.of_nat (length hs) <= bv_unsigned sp - 2256 \/ bv_unsigned sp <= A') ->
  strstr_val (bv_unsigned a0) hb nb = strstr_val A' t nb ->
  evt rsegs POSTQ (XS 0x1f0e4 x1 x5 x6 x7 a1 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
Proof.
  intros A' t t' nb' c0 b0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
         ET ENB E0 H10 HT NT PADt SHt VAL.
  pose proof HN2 as HN. rewrite ENB in HN.
  pose proof (bytes_at_bound _ _ _ _ HN) as BN. rewrite length_app in BN. cbn [length] in BN.
  pose proof (bytes_at_bound _ _ _ _ HT) as BT. rewrite length_app in BT.
  subst t. cbn [length] in BT.
  pose proof (sw_byte_range c0) as Rc0. pose proof (sw_byte_range b0) as Rb0.
  destruct nb' as [|b1 nb2].
  { rd0 m2 HN (bv_unsigned a1) 1%nat (Z_to_bv 64 (bv_unsigned a1 + 1)).
    zstep. zstep. if_cases K; zify_cond K; [|exfalso; lia].
    apply ex_ret; [lia|]. rewrite VAL, ENB, (sw_val_one A' (c0 :: t') c0 t' b0 eq_refl E0).
    rewrite <- H10. symmetry. apply Z_to_bv_bv_unsigned. }
  cbn [length] in BN. pose proof (sw_byte_range b1) as Rb1.
  assert (Nb1 : bv_unsigned b1 <> 0) by (apply (sw_nz nb 1 b1 NN); rewrite ENB; reflexivity).
  rdb m2 HN (bv_unsigned a1) 1%nat (Z_to_bv 64 (bv_unsigned a1 + 1)) b1.
  zstep. zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
  destruct t' as [|c1 t2].
  { rd0 m2 HT A' 1%nat (Z_to_bv 64 (bv_unsigned x10 + 1)).
    zstep. zstep. if_cases K; zify_cond K; [|exfalso; lia].
    zstep. apply ex_ret; [lia|]. rewrite VAL, (sw_val_short A' [c0] nb) by (rewrite ENB; cbn [length]; lia).
    reflexivity. }
  cbn [length] in BT. pose proof (sw_byte_range c1) as Rc1.
  assert (Nc1 : bv_unsigned c1 <> 0) by (apply (sw_nz _ 1 c1 NT); reflexivity).
  rdb m2 HT A' 1%nat (Z_to_bv 64 (bv_unsigned x10 + 1)) c1.
  zstep. zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
  destruct nb2 as [|b2 nb3].
  { rd0 m2 HN (bv_unsigned a1) 2%nat (Z_to_bv 64 (bv_unsigned a1 + 2)).
    zstep. zstep. if_cases K; zify_cond K; [|exfalso; lia].
    eapply (two_entry A' (c0 :: c1 :: t2) t2 b0 b1 c0 c1);
      [exact ENB | reflexivity | exact E0 | exact HT | exact NT | exact H10 | apply sb_u_byte | apply sb_u_byte | exact VAL]. }
  cbn [length] in BN. pose proof (sw_byte_range b2) as Rb2.
  assert (Nb2 : bv_unsigned b2 <> 0) by (apply (sw_nz nb 2 b2 NN); rewrite ENB; reflexivity).
  rdb m2 HN (bv_unsigned a1) 2%nat (Z_to_bv 64 (bv_unsigned a1 + 2)) b2.
  zstep. zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
  destruct t2 as [|c2 t3].
  { rd0 m2 HT A' 2%nat (Z_to_bv 64 (bv_unsigned x10 + 2)).
    zstep. zstep. if_cases K; zify_cond K; [|exfalso; lia].
    zstep. apply ex_ret; [lia|]. rewrite VAL, (sw_val_short A' [c0; c1] nb) by (rewrite ENB; cbn [length]; lia).
    reflexivity. }
  cbn [length] in BT. pose proof (sw_byte_range c2) as Rc2.
  assert (Nc2 : bv_unsigned c2 <> 0) by (apply (sw_nz _ 2 c2 NT); reflexivity).
  rdb m2 HT A' 2%nat (Z_to_bv 64 (bv_unsigned x10 + 2)) c2.
  zstep. zstep. if_cases K4; zify_cond K4; [exfalso; lia|].
  destruct nb3 as [|b3 nb4].
  { rd0 m2 HN (bv_unsigned a1) 3%nat (Z_to_bv 64 (bv_unsigned a1 + 3)).
    zstep. zstep. if_cases K; zify_cond K; [|exfalso; lia].
    eapply (three_entry A' (c0 :: c1 :: c2 :: t3) t3 b0 b1 b2 c0 c1 c2);
      [exact ENB | reflexivity | exact E0 | exact HT | exact NT | exact H10
      | apply sb_u_byte | apply sb_u_byte | apply sb_u_byte | apply sb_u_byte | exact VAL]. }
  cbn [length] in BN. pose proof (sw_byte_range b3) as Rb3.
  assert (Nb3 : bv_unsigned b3 <> 0) by (apply (sw_nz nb 3 b3 NN); rewrite ENB; reflexivity).
  rdb m2 HN (bv_unsigned a1) 3%nat (Z_to_bv 64 (bv_unsigned a1 + 3)) b3.
  zstep. zstep. if_cases K5; zify_cond K5; [exfalso; lia|].
  destruct t3 as [|c3 t4].
  { rd0 m2 HT A' 3%nat (Z_to_bv 64 (bv_unsigned x10 + 3)).
    zstep. zstep. if_cases K; zify_cond K; [|exfalso; lia].
    zstep. apply ex_ret; [lia|]. rewrite VAL, (sw_val_short A' [c0; c1; c2] nb) by (rewrite ENB; cbn [length]; lia).
    reflexivity. }
  cbn [length] in BT. pose proof (sw_byte_range c3) as Rc3.
  assert (Nc3 : bv_unsigned c3 <> 0) by (apply (sw_nz _ 3 c3 NT); reflexivity).
  rdb m2 HT A' 3%nat (Z_to_bv 64 (bv_unsigned x10 + 3)) c3.
  zstep. zstep. if_cases K6; zify_cond K6; [exfalso; lia|].
  destruct nb4 as [|b4 nb5].
  { rd0 m2 HN (bv_unsigned a1) 4%nat (Z_to_bv 64 (bv_unsigned a1 + 4)).
    zstep. zstep. if_cases K; zify_cond K; [|exfalso; lia].
    eapply (four_tail A' (c0 :: c1 :: c2 :: c3 :: t4) b0 b1 b2 b3);
      [exact ENB | cbn [length]; lia | exact HT | exact NT | exact H10 | exact VAL]. }
  cbn [length] in BN. pose proof (sw_byte_range b4) as Rb4.
  assert (Nb4 : bv_unsigned b4 <> 0) by (apply (sw_nz nb 4 b4 NN); rewrite ENB; reflexivity).
  rdb m2 HN (bv_unsigned a1) 4%nat (Z_to_bv 64 (bv_unsigned a1 + 4)) b4.
  zstep. zstep. if_cases K7; zify_cond K7; [exfalso; lia|].
  eapply (tw_tail A' (c0 :: c1 :: c2 :: c3 :: t4));
    [rewrite ENB; discriminate | exact HT | exact NT | exact H10 | exact PADt | exact SHt | exact VAL].
Qed.

End Tail.

Theorem strstr_holds_of : fourbyte_strstr_contract -> twoway_strstr_contract -> strstr_contract.
Proof.
  intros FB TW. unfold strstr_contract, STRSTR.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m hb hs nb lo g
         ST LO HH NH PAD A0 HN NN MI SH SN GG GD GL GGL.
  pose proof (munch_refl [(bv_unsigned sp - 2256, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ HH) as BH. pose proof (bytes_at_bound _ _ _ _ HN) as BN.
  rewrite length_app in BH, BN. cbn [length] in BH, BN.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  carve_frame 16%nat ST.
  zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into M1 end.
  destruct nb as [|b0 nb'].
  - rd0 M1 HN (bv_unsigned a1) 0%nat a1.
    zstep. zstep. if_cases K; zify_cond K; [|exfalso; lia].
    eapply ex_ret; try eassumption.
    + lia.
    + rewrite ss_val_nil. symmetry. apply Z_to_bv_bv_unsigned.
  - cbn [length] in SN, BN.
    assert (Nb0 : bv_unsigned b0 <> 0) by (apply (sw_nz (b0 :: nb') 0 b0 NN); reflexivity).
    pose proof (sw_byte_range b0) as Rb0.
    rdb M1 HN (bv_unsigned a1) 0%nat a1 b0.
    zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
    zstep.
    pose proof strchr_holds as SC. unfold strchr_contract, STRCHR in SC.
    call_lit SC by (rewrite ?unsigned_lit by lia; first [exact ST | exact HH | exact NH | exact PAD | assumption | lia]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into M2 end.
    assert (HHm : bytes_at rsegs M2 (bv_unsigned a0) (hb ++ Z_to_bv 8 0 :: hs)) by assumption.
    rewrite (Z.mod_small (bv_unsigned b0) 256) by lia.
    unfold strchr_val. rewrite (proj2 (Z.eqb_neq _ _) Nb0). cbv iota.
    unfold strchr_res. destruct (find_byte (bv_unsigned b0) hb) as [i|] eqn:FBY.
    + destruct (find_byte_Some _ _ _ FBY) as (Hi & (c & Ec & Hc) & Hbef).
      zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
      assert (ET : skipn i hb = c :: skipn (S i) hb) by (apply sw_skipn_nth; exact Ec).
      assert (H10 : bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat i)) = bv_unsigned a0 + Z.of_nat i)
        by (apply unsigned_lit; lia).
      assert (HT : bytes_at rsegs M2 (bv_unsigned a0 + Z.of_nat i) (skipn i hb ++ Z_to_bv 8 0 :: hs)).
      { pose proof (ss_bytes_skip _ _ _ _ i HHm ltac:(rewrite length_app; lia)) as X.
        rewrite skipn_app in X. replace (i - length hb)%nat with 0%nat in X by lia. exact X. }
      assert (NT : ~ In (Z_to_bv 8 0) (skipn i hb)).
      { intros Hin. apply NH. rewrite <- (firstn_skipn i hb). apply in_or_app. right. exact Hin. }
      assert (PADt : (- (bv_unsigned a0 + Z.of_nat i + Z.of_nat (length (skipn i hb)) + 1)) mod 8 <= Z.of_nat (length hs)).
      { rewrite length_skipn.
        replace (bv_unsigned a0 + Z.of_nat i + Z.of_nat (length hb - i)) with (bv_unsigned a0 + Z.of_nat (length hb)) by lia.
        exact PAD. }
      assert (SHt : bv_unsigned a0 + Z.of_nat i + Z.of_nat (length (skipn i hb)) + 1 + Z.of_nat (length hs)
                      <= bv_unsigned sp - 2256 \/ bv_unsigned sp <= bv_unsigned a0 + Z.of_nat i).
      { rewrite length_skipn. lia. }
      pose proof (sw_val_shift (bv_unsigned a0) hb (b0 :: nb') b0 nb' i eq_refl FBY) as VAL.
      eapply tail with (A' := bv_unsigned a0 + Z.of_nat i) (t := skipn i hb) (t' := skipn (S i) hb)
                       (nb' := nb') (c0 := c) (b0 := b0).
      all: first [eassumption | reflexivity].
    + zstep.
      lazymatch goal with
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_cases K2; zify_cond K2; [|exfalso; lia]
      | _ => idtac
      end.
      eapply ex_ret; try eassumption.
      * lia.
      * rewrite (sw_val_none _ hb (b0 :: nb') b0 nb' eq_refl FBY). reflexivity.
Qed.

Theorem strstr_holds : strstr_contract.
Proof. exact (strstr_holds_of fourbyte_strstr.fourbyte_strstr_holds twoway_strstr.twoway_strstr_holds). Qed.
