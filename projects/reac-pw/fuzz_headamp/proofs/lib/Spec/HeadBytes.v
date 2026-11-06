(** The byte layouts that fuzz_headamp's harness (fuzz_headamp.c) and reac_headamp_prop_parse_result
    (reac-pw f86a30a3 src/reac_headamp_prop.c) share in memory, as the contracts of Prog/ and U/Prog/ state them,
    and the names of the five parts of an answer of Pod/Headamp.v ([parse_props], [expect_model]). Both builds use
    this one file: no address of an image is in it. Statement text and length lemmas only; no function of a binary
    is proved here.
    - struct reac_headamp_setting (libreac include/reac/reac_headamp_tx.h:92-96): ch at +0, param at +1, value at
      +2, one uint8_t each, sizeof 3 (DWARF; the parse's `sb` at out + 3n + {0, 1, 2}, plain 0x14bac-0x14bb4, U
      0x15030-0x15038; check_cells_valid's `lbu` at +0/+1/+2, plain 0x146f8-0x14718).
    - struct reac_headamp_prop_result (reac_headamp_prop.h): int n at +0, int keys at +4, enum refusal at +8, 12 bytes
      (the parse's `sw` at 0x149a4-0x149ac; check_count's `lw` at +0 and +4, plain 0x146c0 / 0x146c8;
      check_keys `lw 4`, check_refusal `lw 8`).
    - struct expect (fuzz_headamp.c:56-62): int rc at +0, struct cell { int ch, param, value } cell[10] at +4 (12
      bytes each), int n at +0x7c, int keys at +0x80, enum refusal at +0x84, 136 bytes (expect_of's memset of 0x88
      bytes, plain 0x140fc; check_object `lw 0`, check_cells `lw 4 + 12i / 8 + 12i / 12 + 12i`, check_keys
      `lw 0x80`, check_refusal `lw 0x84`). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Mem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
Import ListNotations.
Open Scope Z_scope.

(** ** An answer (rc, cells, (n, keys, refusal)) of [parse_props] / [expect_model], by part *)
Definition answer := (Z * list cell * (Z * Z * Z))%type.
Definition ans_rc (o : answer) : Z := fst (fst o).
Definition ans_cells (o : answer) : list cell := snd (fst o).
Definition ans_n (o : answer) : Z := fst (fst (snd o)).
Definition ans_keys (o : answer) : Z := snd (fst (snd o)).
Definition ans_rf (o : answer) : Z := snd (snd o).

(** ** out: the cells as bytes *)
Definition ha_cell_bytes (c : cell) : list byte :=
  let '(ch, p, v) := c in [Z_to_bv 8 ch; Z_to_bv 8 p; Z_to_bv 8 v].
Definition ha_cells_bytes (cs : list cell) : list byte := flat_map ha_cell_bytes cs.

(** The byte the harness fills out with before each parse (memset(out, 0xa5, ..), fuzz_headamp.c:330, :351) and
    that check_no_overrun expects in the guard cell out[cap] (fuzz_headamp.c:190). *)
Definition GUARD_BYTE : byte := Z_to_bv 8 0xa5.

(** A cell whose three fields each fit a uint8_t: then the int fields of struct expect equal the bytes of out
    exactly when the cells are equal (check_cells compares `lw` with `lbu`). *)
Definition cell_bytes_ok (c : cell) : Prop :=
  let '(ch, p, v) := c in 0 <= ch < 256 /\ 0 <= p < 256 /\ 0 <= v < 256.

(** ** res: struct reac_headamp_prop_result *)
Definition ha_res_bytes (n keys rf : Z) : list byte :=
  le4 (Z_to_bv 64 n) ++ le4 (Z_to_bv 64 keys) ++ le4 (Z_to_bv 64 rf).
Definition ans_res_bytes (o : answer) : list byte := ha_res_bytes (ans_n o) (ans_keys o) (ans_rf o).

(** ** x: struct expect; the cells past n are 0 (expect_of's memset, fuzz_headamp.c:111). *)
Definition X_CELLS : nat := 10.
Definition x_cell_bytes (c : cell) : list byte :=
  let '(ch, p, v) := c in le4 (Z_to_bv 64 ch) ++ le4 (Z_to_bv 64 p) ++ le4 (Z_to_bv 64 v).
Definition x_cells_bytes (cs : list cell) : list byte := flat_map x_cell_bytes cs.
Definition x_bytes (o : answer) : list byte :=
  le4 (Z_to_bv 64 (ans_rc o)) ++ x_cells_bytes (ans_cells o) ++
  repeat (Z_to_bv 8 0) (12 * (X_CELLS - length (ans_cells o)))%nat ++ ans_res_bytes o.
(** Offsets of the fields check_keys / check_refusal read: 0x80 and 0x84. *)
Definition X_KEYS_OFF : Z := 128.
Definition X_RF_OFF : Z := 132.

(** ** Lengths *)
Lemma length_ha_cells_bytes : forall cs, length (ha_cells_bytes cs) = (3 * length cs)%nat.
Proof.
  induction cs as [|[[ch p] v] cs IH]; [reflexivity|].
  unfold ha_cells_bytes in *. cbn [flat_map ha_cell_bytes app length]. rewrite IH. lia.
Qed.

Lemma length_x_cells_bytes : forall cs, length (x_cells_bytes cs) = (12 * length cs)%nat.
Proof.
  induction cs as [|[[ch p] v] cs IH]; [reflexivity|].
  unfold x_cells_bytes in *. cbn [flat_map x_cell_bytes length]. rewrite !length_app, !length_le4.
  rewrite IH. lia.
Qed.

Lemma length_ha_res_bytes : forall n keys rf, length (ha_res_bytes n keys rf) = 12%nat.
Proof. intros. unfold ha_res_bytes. rewrite !length_app, !length_le4. reflexivity. Qed.

Lemma length_x_bytes : forall o, (length (ans_cells o) <= X_CELLS)%nat -> length (x_bytes o) = 136%nat.
Proof.
  intros o H. unfold x_bytes, ans_res_bytes. unfold X_CELLS in *.
  rewrite !length_app, length_le4, length_x_cells_bytes, repeat_length, length_ha_res_bytes. lia.
Qed.

(** The answer of [parse_props] / [expect_model] under [answer_ok], by part. *)
Lemma answer_ok_parts : forall cap o, answer_ok cap o ->
  ((ans_rc o = -1 /\ ans_cells o = [] /\ ans_n o = 0 /\ ans_keys o = 0 /\ ans_rf o = REFUSE_NONE) \/
   (0 <= ans_rc o <= cap /\ ans_rc o = Z.of_nat (length (ans_cells o)) /\ ans_n o = ans_rc o /\
    ans_rc o <= ans_keys o)) /\
  Forall cell_valid (ans_cells o).
Proof. intros cap [[rc cells] [[n keys] rf]] H. exact H. Qed.

Lemma cell_valid_bytes_ok : forall c, cell_valid c -> cell_bytes_ok c.
Proof.
  intros [[ch p] v] (H1 & H2 & H3). unfold HA_CHANNELS, HA_SENS, HA_SENS_MAX in *.
  cbn. destruct (p =? 2); lia.
Qed.
