(** fuzz_rate's library answers: what reac_rate_bit, reac_rate_is_closed, reac_rate_best_drivable,
    reac_rate_cfg_decide and reac_rate_refuse_code return (src/reac_rate_cfg.c:16-90), as Gallina over the integer
    value of the 64-bit argument register, plus the harness's own copies of the same rules (fuzz_rate.c:41-61,
    89-98, 212-213). Shared by the plain and the UBSan contracts: it names no image address. Statement text; no
    function of a binary is proved here.

    Width. Each function compares the WHOLE 64-bit register: reac_rate_bit, reac_rate_is_closed and
    reac_rate_cfg_decide compare a0 / a1 with `beq` / `bne` / `xor` against 44100, 48000 and 96000 built by
    `lui; addiw` (plain 0x149f4-0x14a14, 0x149c0-0x149e4, 0x14c14-0x14c34; UBSan the same code at 0x14d48, 0x14d14,
    0x14f94), and reac_rate_cfg_decide compares the role a0 with 1 (`bne a0,a3` 0x14c08) and masks with a 64-bit
    `and` (0x14c44). reac_rate_best_drivable tests bits 2, 1 and 0 of a0 (`andi a1,a0,4`, `andi a1,a0,2`,
    `slli a0,a0,63; srai a0,a0,63`, 0x14a38-0x14a58). reac_rate_refuse_code takes the table path when a0 <= 4 as an
    unsigned 64-bit word (`bgeu a1,a0` with a1 = 4, plain 0x14994, UBSan 0x14cdc), else codes[0]. So each answer
    below is a function of the argument's integer value v = bv_unsigned of the register (0 <= v < 2^64); a caller
    that holds a C int passes its sign extension, so a negative int is a v >= 2^63 and is no closed rate.

    The enum values (libreac reac_cfg.h, the REAC_RATE_REFUSE_ names): NONE 0, NOT_CLOSED 1, NOT_DRIVABLE 2,
    ROLE_SLAVE 3, MALFORMED 4; REAC_RATE_REFUSE_CODES_INIT = "none", "not_closed", "not_drivable", "role_slave",
    "malformed" in that order (both images: the five strings at 0x103e1, 0x102d1, 0x10375, 0x10400, 0x103d7, read by
    Prog/reac_rate_refuse_code_c.v's [refuse_code_addr_img]). REAC_ROLE_SLAVE is 1, REAC_ROLE_MASTER 0 (the
    harness passes flags bit 1, fuzz_rate.c:246, main's `srli s4,a1,0x3f` plain 0x14404).

    Computation check against the compiled functions (2026-10-30, both images, unstripped twins sha256 4ecf851e...,
    593a406e...): an emulator run (unicorn 2.1.0 in docker rl3-check:1,
    every callee compiled, abort and every unimp hooked; rate_lib_check.py sha256 da5a2038b58f, a line-by-line Python
    copy of these definitions). All PASS in its plain result (sha256 e6135ed10fb9) and its UBSan result
    (e77cfeea3d55): reac_rate_bit and reac_rate_is_closed on 2521 values (the closed rates, their neighbours, sign-
    extended negatives, 2^32 + rate, 2^63 + rate, 2000 random sign-extended u32, 500 random u64), best_drivable on
    masks 0..255 and 500 random u64, cfg_decide on 284160 (role, hz, mask) triples (role in 0, 1, 2, 2^32 + 1,
    2^64 - 1; masks 0..255), refuse_code's pointer and string for r in 0..12, 2^32, 2^32 + 1, 2^63, 2^64 - 1;
    check_list and check_code return on these answers and abort on a perturbed one. *)
From Stdlib Require Import String ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor.
Import ListNotations.
Open Scope Z_scope.

(** The closed list (facts REAC_SAMPLE_RATE_44K1, _48K, _96K; fuzz_rate.c:41 closed_list, reac_rate_cfg.c:51-52
    ordered): the same three values in the same order. *)
Definition RATE_44K1 : Z := 44100.
Definition RATE_48K : Z := 48000.
Definition RATE_96K : Z := 96000.
Definition closed_list : list Z := [RATE_44K1; RATE_48K; RATE_96K].

(** reac_rate_bit(hz) (reac_rate_cfg.c:30-38): REAC_RATE_BIT_44100 = 1, _48000 = 2, _96000 = 4, else 0. *)
Definition rate_bit (hz : Z) : Z :=
  if hz =? RATE_44K1 then 1 else if hz =? RATE_48K then 2 else if hz =? RATE_96K then 4 else 0.

(** reac_rate_is_closed(hz) (reac_rate_cfg.c:24-28): 1 on a closed rate, else 0. *)
Definition rate_closed (hz : Z) : Z := if rate_bit hz =? 0 then 0 else 1.

(** reac_rate_best_drivable(mask) (reac_rate_cfg.c:40-47): the highest closed rate whose bit the mask sets. *)
Definition rate_best (mask : Z) : Z :=
  if Z.testbit mask 2 then RATE_96K
  else if Z.testbit mask 1 then RATE_48K
  else if Z.testbit mask 0 then RATE_44K1
  else 0.

Definition REFUSE_NONE : Z := 0.
Definition REFUSE_NOT_CLOSED : Z := 1.
Definition REFUSE_NOT_DRIVABLE : Z := 2.
Definition REFUSE_ROLE_SLAVE : Z := 3.
Definition REFUSE_MALFORMED : Z := 4.

(** reac_rate_cfg_decide(role, hz, mask) (reac_rate_cfg.c:77-90): a slave first, then a rate off the closed list,
    then a rate outside the mask; else accepted. *)
Definition decide_res (role hz mask : Z) : Z :=
  if role =? 1 then REFUSE_ROLE_SLAVE
  else if rate_bit hz =? 0 then REFUSE_NOT_CLOSED
  else if Z.land (rate_bit hz) mask =? 0 then REFUSE_NOT_DRIVABLE
  else REFUSE_NONE.

(** reac_rate_refuse_code(r) (reac_rate_cfg.c:16-22): codes[r] for r <= 4 (unsigned), else codes[NONE]; the
    answer as the string's bytes, without its NUL. *)
Definition REFUSE_STRS : list string := ["none"; "not_closed"; "not_drivable"; "role_slave"; "malformed"]%string.
Definition refuse_idx (r : Z) : nat := if r <=? 4 then Z.to_nat r else O.
Definition refuse_code_res (r : Z) : list byte := sbytes (nth (refuse_idx r) REFUSE_STRS "none"%string).

(** The harness's code_of(r) (fuzz_rate.c:52-61) on the enum value r. *)
Definition code_of_res (r : Z) : list byte :=
  sbytes (if r =? 1 then "not_closed"%string else if r =? 2 then "not_drivable"%string
          else if r =? 3 then "role_slave"%string else if r =? 4 then "malformed"%string else "none"%string).

(** The harness's bit_of(hz) (fuzz_rate.c:43-49): the first index of hz in closed_list, as a bit. *)
Fixpoint bit_of_go (hz : Z) (l : list Z) (i : Z) : Z :=
  match l with
  | [] => 0
  | c :: l' => if hz =? c then Z.shiftl 1 i else bit_of_go hz l' (i + 1)
  end.
Definition bit_of (hz : Z) : Z := bit_of_go hz closed_list 0.

(** The harness's expect_decide(role, hz, mask) (fuzz_rate.c:89-98). *)
Definition expect_decide (role hz mask : Z) : Z :=
  if role =? 1 then REFUSE_ROLE_SLAVE
  else if bit_of hz =? 0 then REFUSE_NOT_CLOSED
  else if Z.land mask (bit_of hz) =? 0 then REFUSE_NOT_DRIVABLE
  else REFUSE_NONE.

(** The best rate check_list expects (fuzz_rate.c:213). *)
Definition best_of (mask : Z) : Z :=
  if negb (Z.land mask 4 =? 0) then 96000
  else if negb (Z.land mask 2 =? 0) then 48000
  else if negb (Z.land mask 1 =? 0) then 44100
  else 0.

(** ** Facts the callers use *)
Lemma rate_bit_cases : forall hz,
  (hz = RATE_44K1 /\ rate_bit hz = 1) \/ (hz = RATE_48K /\ rate_bit hz = 2) \/
  (hz = RATE_96K /\ rate_bit hz = 4) \/
  (hz <> RATE_44K1 /\ hz <> RATE_48K /\ hz <> RATE_96K /\ rate_bit hz = 0).
Proof.
  intros hz. unfold rate_bit.
  destruct (Z.eqb_spec hz RATE_44K1); [left; auto|].
  destruct (Z.eqb_spec hz RATE_48K); [right; left; auto|].
  destruct (Z.eqb_spec hz RATE_96K); [right; right; left; auto|].
  right; right; right; auto.
Qed.

Lemma rate_bit_range : forall hz, 0 <= rate_bit hz <= 4.
Proof. intros hz. destruct (rate_bit_cases hz) as [[_ ->]|[[_ ->]|[[_ ->]|(_&_&_&->)]]]; lia. Qed.

Lemma rate_closed_range : forall hz, rate_closed hz = 0 \/ rate_closed hz = 1.
Proof. intros hz. unfold rate_closed. destruct (rate_bit hz =? 0); auto. Qed.

Lemma decide_res_range : forall role hz mask, 0 <= decide_res role hz mask <= 3.
Proof.
  intros role hz mask. unfold decide_res, REFUSE_ROLE_SLAVE, REFUSE_NOT_CLOSED, REFUSE_NOT_DRIVABLE, REFUSE_NONE.
  destruct (role =? 1); [lia|]. destruct (rate_bit hz =? 0); [lia|].
  destruct (Z.land (rate_bit hz) mask =? 0); lia.
Qed.

Lemma rate_best_range : forall mask,
  rate_best mask = 0 \/ rate_best mask = RATE_44K1 \/ rate_best mask = RATE_48K \/ rate_best mask = RATE_96K.
Proof.
  intros mask. unfold rate_best.
  destruct (Z.testbit mask 2); [auto|]. destruct (Z.testbit mask 1); [auto|].
  destruct (Z.testbit mask 0); auto.
Qed.

Lemma bit_of_rate_bit : forall hz, bit_of hz = rate_bit hz.
Proof.
  intros hz. unfold bit_of, rate_bit, closed_list. cbn [bit_of_go].
  destruct (hz =? RATE_44K1); [reflexivity|]. destruct (hz =? RATE_48K); [reflexivity|].
  destruct (hz =? RATE_96K); reflexivity.
Qed.

Lemma expect_decide_res : forall role hz mask, expect_decide role hz mask = decide_res role hz mask.
Proof.
  intros role hz mask. unfold expect_decide, decide_res. rewrite bit_of_rate_bit, Z.land_comm. reflexivity.
Qed.

Lemma testbit_land_pow : forall mask k, 0 <= k -> (Z.land mask (2 ^ k) =? 0) = negb (Z.testbit mask k).
Proof.
  intros mask k Hk. destruct (Z.testbit mask k) eqn:E; cbn [negb].
  - apply Z.eqb_neq. intros H. assert (Z.testbit (Z.land mask (2 ^ k)) k = true) as T.
    { rewrite Z.land_spec, E, Z.pow2_bits_true by lia. reflexivity. }
    rewrite H, Z.bits_0 in T. discriminate.
  - apply Z.eqb_eq. apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec j k) as [->|Hne]; [rewrite E; reflexivity|].
    rewrite Z.pow2_bits_false by lia. apply andb_false_r.
Qed.

Lemma best_of_rate_best : forall mask, best_of mask = rate_best mask.
Proof.
  intros mask. unfold best_of, rate_best.
  change (Z.land mask 4) with (Z.land mask (2 ^ 2)). change (Z.land mask 2) with (Z.land mask (2 ^ 1)).
  change (Z.land mask 1) with (Z.land mask (2 ^ 0)).
  rewrite (testbit_land_pow mask 2), (testbit_land_pow mask 1), (testbit_land_pow mask 0) by lia.
  rewrite !negb_involutive. reflexivity.
Qed.

Lemma code_of_refuse : forall r, 0 <= r <= 4 -> code_of_res r = refuse_code_res r.
Proof.
  intros r Hr. assert (r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4) as H by lia.
  destruct H as [->|[->|[->|[->| ->]]]]; reflexivity.
Qed.

Lemma refuse_idx_lt : forall r, (refuse_idx r < 5)%nat.
Proof. intros r. unfold refuse_idx. destruct (Z.leb_spec r 4); lia. Qed.

(** Each answer is one of the five strings. *)
Lemma refuse_code_res_cases : forall r,
  refuse_code_res r = sbytes "none" \/ refuse_code_res r = sbytes "not_closed" \/
  refuse_code_res r = sbytes "not_drivable" \/ refuse_code_res r = sbytes "role_slave" \/
  refuse_code_res r = sbytes "malformed".
Proof.
  intros r. unfold refuse_code_res. pose proof (refuse_idx_lt r) as H.
  destruct (refuse_idx r) as [|[|[|[|[|k]]]]]; [auto 6 | auto 6 | auto 6 | auto 6 | auto 6 | lia].
Qed.

(** No string holds a NUL byte: each is the C string's bytes before its terminator. *)
Lemma refuse_code_res_nonul : forall r, ~ In (Z_to_bv 8 0) (refuse_code_res r).
Proof.
  intros r. destruct (refuse_code_res_cases r) as [E|[E|[E|[E|E]]]]; rewrite E;
    vm_compute; intros H; repeat destruct H as [H|H]; try discriminate; exact H.
Qed.
