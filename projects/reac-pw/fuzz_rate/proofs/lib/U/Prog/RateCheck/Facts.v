(** Facts for the checking segment of reac-pw/fuzz_rate's LLVMFuzzerTestOneInput (UBSan) beyond the shared ones of
    Prog/RateCheck/Facts.v: MemNorm.task_mem of the UBSan library across a callee and a store, the key test
    `snez; addi -1; and` of the compiled pod_string, reac_rate_refuse_code's codes[] table in .data.rel.ro (its 40 bytes
    at 0x1edc0 are image bytes, so the stack and the pod block are apart from it), and the word facts of the loads and
    of the decide loop. The form is reac-pw/fuzz_role's U/Prog/RoleCheck/Facts.v. No function of a binary is proved here. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import reac_rate_refuse_code_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.RateCheck Require Import Facts.
Import ListNotations.
Open Scope Z_scope.

(** ** MemNorm.task_mem (UBSan library) *)
Lemma wview_task_u : forall m x, MemNorm.task_mem rsegs m -> wview rsegs m x <> None ->
  find_segment rsegs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE.
Proof.
  intros m x T W. destruct (m x) as [b|] eqn:E.
  - exact (T x b E).
  - left. unfold wview in W. rewrite E in W.
    destruct (find_segment rsegs (bv_unsigned x) 1); [discriminate | exfalso; apply W; reflexivity].
Qed.

Lemma task_mem_munch_u : forall W m m', MemNorm.task_mem rsegs m -> munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> wview rsegs m x <> None) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' T MU H x b E. destruct (outside_dec W (bv_unsigned x)) as [O|O].
  - rewrite (MU x O) in E. exact (T x b E).
  - exact (wview_task_u m x T (H x O)).
Qed.

Lemma task_mem_write_u : forall m a bs, MemNorm.task_mem rsegs m -> store_ok rsegs m a (length bs) = true ->
  MemNorm.task_mem rsegs (write_to_mem m a bs).
Proof.
  intros m a bs T S x b E. destruct (write_to_mem_some _ _ _ _ _ E) as [E' | (i & Hi & ->)].
  - exact (T x b E').
  - exact (wview_task_u m _ T (store_ok_wview rsegs m a (length bs) i S Hi)).
Qed.

(** ** pod_string's last-byte test: `lbu; snez; addi -1; and` with the body address *)
Lemma snez_mask : forall (b : byte) A, 0 <= A < 2^64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 0) (zxb b)) + -1)))
                     (bv_unsigned (Z_to_bv 64 A)))
  = Z_to_bv 64 (if bv_unsigned b =? 0 then A else 0).
Proof.
  intros b A HA. rewrite v_sltu_b2z. unfold zxb. pose proof (byte_range b) as Hb.
  rewrite (unsigned_lit (bv_unsigned b)) by lia. rewrite (unsigned_lit A) by lia.
  change (bv_unsigned (Z_to_bv 64 0)) with 0.
  destruct (Z.ltb_spec 0 (bv_unsigned b)) as [H|H].
  - replace (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.b2z true)) + -1))) with 0 by reflexivity.
    rewrite Z.land_0_l. rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
  - replace (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.b2z false)) + -1))) with (Z.ones 64) by reflexivity.
    rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia.
    reflexivity.
Qed.

(** ** reac_rate_refuse_code's codes[] table (40 bytes at 0x1edc0, .data.rel.ro): rate_check_contract's
    [CODES_TBL, CODES_TBL_END) (U/Prog/LLVMFuzzerTestOneInput_c.v) and the refuse_code contract's
    [REFUSE_TBL, REFUSE_TBL + REFUSE_TBL_SIZE) (U/Prog/reac_rate_refuse_code_c.v) *)
Definition CODES_LO : Z := 0x1edc0.
Definition CODES_HI : Z := 0x1ede8.

Definition ctbl (m : word -> option byte) : Prop :=
  forall a, CODES_LO <= a < CODES_HI -> mrd rsegs m (wa a) = seg_rom rsegs (wa a).

Lemma ctbl_refuse : forall m, ctbl m ->
  forall a, REFUSE_TBL <= a < REFUSE_TBL + REFUSE_TBL_SIZE -> mrd rsegs m (wa a) = seg_rom rsegs (wa a).
Proof. intros m T a Ha. apply T. unfold REFUSE_TBL, REFUSE_TBL_SIZE, CODES_LO, CODES_HI in *. lia. Qed.

Definition codes_rom_some (a : Z) : bool := match seg_rom rsegs (wa a) with Some _ => true | None => false end.

Lemma codes_rom : forall a, CODES_LO <= a < CODES_HI -> seg_rom rsegs (wa a) <> None.
Proof.
  intros a Ha. assert (H : forallb (fun j => codes_rom_some (CODES_LO + Z.of_nat j)) (seq 0 40) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  specialize (H (Z.to_nat (a - CODES_LO)) ltac:(apply in_seq; unfold CODES_LO, CODES_HI in *; lia)).
  unfold codes_rom_some in H. replace (CODES_LO + Z.of_nat (Z.to_nat (a - CODES_LO))) with a in H by lia.
  destruct (seg_rom rsegs (wa a)); [discriminate | discriminate H].
Qed.

Lemma ctbl_munch : forall W m1 m2, ctbl m1 -> munch W m1 m2 ->
  (forall a, CODES_LO <= a < CODES_HI -> outside W a) -> ctbl m2.
Proof.
  intros W m1 m2 T MU H a Ha. unfold mrd. rewrite (MU (wa a)).
  - exact (T a Ha).
  - rewrite wa_unsigned by (unfold CODES_LO, CODES_HI in *; lia). apply H. exact Ha.
Qed.

(** An interval where the image has no byte misses the table. *)
Lemma codes_apart : forall X Y, (forall a, X <= a < Y -> seg_rom rsegs (wa a) = None) ->
  forall a, CODES_LO <= a < CODES_HI -> ~ (X <= a < Y).
Proof. intros X Y H a Ha Hx. exact (codes_rom a Ha (H a Hx)). Qed.

(** ** Word facts of the walk *)
(** The pointer-overflow bound `a3 = ~(body)` of the key test at entry at: s10 - 104 at. *)
Lemma unsigned_sub_bound : forall (x : word) d k, bv_unsigned x = 2^64 - d -> 0 <= k -> 0 < d -> d + k < 2^64 ->
  bv_unsigned (Z_to_bv 64 (bv_unsigned x - k)) = 2^64 - (d + k).
Proof. intros x d k H H1 H2 H3. rewrite H. rewrite unsigned_lit by lia. lia. Qed.

(** `srli _,_,63` of any word: its top bit, 0 or 1 (the role the decide loop passes, 0x144fc `srli s4,a1,0x3f`). *)
Lemma srl63_range : forall y : word, 0 <= Z.shiftr (bv_unsigned y) 63 <= 1.
Proof.
  intros y. pose proof (bv_unsigned_in_range _ y) as Hy. unfold bv_modulus in Hy. change (2 ^ Z.of_N 64) with (2^64) in Hy.
  rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
  apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia.
Qed.

(** `and` of a 64-bit value with a nonnegative one stays below 2^64 (seqz_slli's premise at 0x145a0). *)
Lemma land_lt64 : forall a b, 0 <= a < 2^64 -> 0 <= b -> 0 <= Z.land a b < 2^64.
Proof.
  intros a b Ha Hb. split; [apply Z.land_nonneg; left; lia|].
  assert (E : Z.land a (Z.ones 64) = a) by (rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  rewrite <- E, <- Z.land_assoc, (Z.land_comm (Z.ones 64) b), Z.land_assoc, Z.land_ones by lia.
  pose proof (Z.mod_pos_bound (Z.land a b) (2^64) ltac:(lia)). lia.
Qed.

(** `beq`/`bne` of a word with a literal. *)
Lemma bv_eqb_lit : forall (x : word) c, 0 <= c < 2^64 -> bv_eqb x (Z_to_bv 64 c) = (bv_unsigned x =? c).
Proof. intros x c Hc. unfold bv_eqb. rewrite (unsigned_lit c) by lia. reflexivity. Qed.

Section Gen.
Variable segs : list Segment.

(** A run of bytes outside a callee's footprint (the contract review's bytes_at_munch_out): unlike
    bytes_at_transport, it needs only that each byte lies outside the footprint. *)
Lemma bytes_at_munch_out : forall W m m' a bs,
  munch W m m' -> (forall i, (i < length bs)%nat -> outside W (a + Z.of_nat i)) ->
  bytes_at segs m a bs -> bytes_at segs m' a bs.
Proof.
  intros W m m' a bs HM HO (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H2 i Hi). unfold mrd. rewrite (HM (wa (a + Z.of_nat i))); [reflexivity|].
  rewrite wa_unsigned by lia. apply HO, Hi.
Qed.

End Gen.
