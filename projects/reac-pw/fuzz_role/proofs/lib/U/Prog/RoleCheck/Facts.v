(** Facts for the checking segment of reac-pw/fuzz_role's LLVMFuzzerTestOneInput (UBSan) beyond the shared ones of
    Prog/RoleCheck/Facts.v: MemNorm.task_mem of the UBSan library across a callee and a store, the key test
    `snez; addi -1; and` of the compiled pod_string, and refuse_code's codes[] table in .data.rel.ro (its 16 bytes
    are image bytes, so the stack and the pod block are apart from it). No function of a binary is proved here. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog.RoleCheck Require Import Facts.
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

(** ** refuse_code's codes[] table (16 bytes at 0x1e1f8, .data.rel.ro) *)
Definition CODES_LO : Z := 0x1e1f8.
Definition CODES_HI : Z := 0x1e208.

Definition ctbl (m : word -> option byte) : Prop :=
  forall a, CODES_LO <= a < CODES_HI -> mrd rsegs m (wa a) = seg_rom rsegs (wa a).

Definition codes_rom_some (a : Z) : bool := match seg_rom rsegs (wa a) with Some _ => true | None => false end.

Lemma codes_rom : forall a, CODES_LO <= a < CODES_HI -> seg_rom rsegs (wa a) <> None.
Proof.
  intros a Ha. assert (H : forallb (fun j => codes_rom_some (CODES_LO + Z.of_nat j)) (seq 0 16) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (Z.to_nat (a - CODES_LO)) ltac:(apply in_seq; unfold CODES_LO, CODES_HI in *; lia)).
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

(** The pointer-overflow bound `a3 = ~(body)` of the key test at entry at: s10 - 104 at. *)
Lemma unsigned_sub_bound : forall (x : word) d k, bv_unsigned x = 2^64 - d -> 0 <= k -> 0 < d -> d + k < 2^64 ->
  bv_unsigned (Z_to_bv 64 (bv_unsigned x - k)) = 2^64 - (d + k).
Proof. intros x d k H H1 H2 H3. rewrite H. rewrite unsigned_lit by lia. lia. Qed.
