(** * OSSVerify.Core.Driver: the input file every build reads

    Every binary in this collection is run as [<file> FILE].  A small driver
    linked into every build reads FILE whole and splits it as

      [u16 config word][config bytes][u32 allocation mask][payload]

    with both integers little-endian.  The low 15 bits of the config word are
    the config length; bit 15 asks for COUNTING MODE, in which the exit
    status is the number of allocations the library attempted instead of the
    harness's result (for an OSS-Fuzz harness binary that number is always 0).
    The allocation mask is read and ignored by the OSS-Fuzz harness binaries;
    the API drivers use it to refuse chosen allocations.  The driver then
    calls LLVMFuzzerTestOneInput on the payload [(config[0] & 3) + 1] times
    (once when there is no config) and prints each return value.

    It exits with status 2 without calling the harness when argv does not
    have exactly two strings, when FILE cannot be opened or read, when FILE
    has [max_input_bytes] bytes or more, or when FILE is shorter than its
    header.  docs/running.md has the details.

    This file writes that format down as Rocq data, so that statements and
    corollaries can name inputs ("the file [testcase_file p]") rather than
    byte lists.  It is a description of the driver's C source, which is in
    the src/ folder of the recipe archive a release attaches (a port-built
    project's driver is in its port archive; docs/reproducing.md says
    where); no statement depends on it, and nothing here is a claim about
    the binaries. *)

From Stdlib Require Import ZArith List Lia.
From stdpp.bitvector Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Core Require Import Shapes.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Constants *)

(** Inputs of this many bytes (64 MiB) or more are refused, with status 2. *)
Definition max_input_bytes : Z := 67108864.
(** The config length is 15 bits. *)
Definition max_config_bytes : Z := 32767.
(** Bit 15 of the config word. *)
Definition counting_bit : Z := 32768.
(** The header is at least the config word and the allocation mask. *)
Definition header_min_bytes : nat := 6.

(** ** Exit statuses the driver itself chooses *)
Module Status.
  (** Every harness call returned 0 or -1. *)
  Definition ok : word := Z_to_bv 64 0.
  (** The driver refused the input, or ran out of memory before or instead
      of calling the harness. *)
  Definition refused : word := Z_to_bv 64 2.
  (** The harness called exit() (libFuzzer's status for that case). *)
  Definition harness_exited : word := Z_to_bv 64 77.
  (** A harness call returned a value other than 0 or -1. *)
  Definition harness_bad_return : word := Z_to_bv 64 78.
  (** In counting mode, counts of 251 or more are reported as 251. *)
  Definition count_ceiling : Z := 251.
End Status.

Lemma ok_or_refused_is_driver_statuses :
  Exits.ok_or_refused = [Status.ok; Status.refused].
Proof. reflexivity. Qed.

(** ** Encoding *)

Definition byte_of (z : Z) : byte := Z_to_bv 8 z.

(** Little-endian encodings of a 16-bit and a 32-bit value. *)
Definition le16 (z : Z) : list byte := [byte_of z; byte_of (Z.shiftr z 8)].
Definition le32 (z : Z) : list byte :=
  [byte_of z; byte_of (Z.shiftr z 8); byte_of (Z.shiftr z 16); byte_of (Z.shiftr z 24)].

(** The input file for a config, an allocation mask and a payload. *)
Definition frame (counting : bool) (config : list byte) (mask : Z) (payload : list byte)
    : list byte :=
  le16 (Z.of_nat (length config) + (if counting then counting_bit else 0))
  ++ config ++ le32 mask ++ payload.

(** The file an OSS-Fuzz testcase [payload] becomes: six zero bytes (no
    config, so one harness call; no allocation mask), then the payload
    unchanged.  [oft run] and [oft reproduce] write exactly this. *)
Definition testcase_file (payload : list byte) : list byte := frame false [] 0 payload.

Lemma testcase_file_bytes : forall payload,
  testcase_file payload = repeat (byte_of 0) 6 ++ payload.
Proof. reflexivity. Qed.

(** How many times the harness is called for a config. *)
Definition calls (config : list byte) : nat :=
  match config with
  | [] => 1
  | c :: _ => S (Z.to_nat (Z.land (bv_unsigned c) 3))
  end.

Lemma calls_between : forall config, (1 <= calls config <= 4)%nat.
Proof.
  intros [| c config]; cbn [calls]; [lia |].
  change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound (bv_unsigned c) (2 ^ 2) ltac:(lia)). lia.
Qed.

(** ** Decoding *)

(** What the driver reads a file as, when it calls the harness at all. *)
Record Parsed := mkParsed {
  parsed_counting : bool;
  parsed_config : list byte;
  parsed_mask : Z;
  parsed_payload : list byte
}.

Definition u16_of (b0 b1 : byte) : Z := bv_unsigned b0 + 256 * bv_unsigned b1.
Definition u32_of (b0 b1 b2 b3 : byte) : Z :=
  bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2
  + 16777216 * bv_unsigned b3.

(** [None] exactly where the driver exits with status 2 on the file's
    contents (size, or a header the file is too short for). *)
Definition parse (file : list byte) : option Parsed :=
  if Z.of_nat (length file) <? max_input_bytes then
    match file with
    | b0 :: b1 :: rest =>
        let w := u16_of b0 b1 in
        let n := Z.to_nat (Z.land w max_config_bytes) in
        match skipn n rest with
        | m0 :: m1 :: m2 :: m3 :: payload =>
            Some (mkParsed (Z.testbit w 15) (firstn n rest) (u32_of m0 m1 m2 m3) payload)
        | _ => None
        end
    | _ => None
    end
  else None.

Lemma byte_of_unsigned : forall z, bv_unsigned (byte_of z) = z mod 256.
Proof. intros z. unfold byte_of. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma u16_of_le16 : forall z, 0 <= z < 65536 ->
  u16_of (byte_of z) (byte_of (Z.shiftr z 8)) = z.
Proof.
  intros z Hz. unfold u16_of. rewrite !byte_of_unsigned, Z.shiftr_div_pow2 by lia.
  change (2 ^ 8) with 256.
  rewrite (Z.mod_small (z / 256)) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  pose proof (Z.div_mod z 256 ltac:(lia)). lia.
Qed.

Lemma u32_of_le32 : forall z, 0 <= z < 4294967296 ->
  u32_of (byte_of z) (byte_of (Z.shiftr z 8)) (byte_of (Z.shiftr z 16))
         (byte_of (Z.shiftr z 24)) = z.
Proof.
  intros z Hz. unfold u32_of. rewrite !byte_of_unsigned, !Z.shiftr_div_pow2 by lia.
  change (2 ^ 8) with 256. change (2 ^ 16) with 65536. change (2 ^ 24) with 16777216.
  lia.
Qed.

(** [parse] undoes [frame]: the driver reads back exactly the config, mask
    and payload the file was built from. *)
Theorem parse_frame : forall counting config mask payload,
  (Z.of_nat (length config) <= max_config_bytes) ->
  0 <= mask < 4294967296 ->
  Z.of_nat (length (frame counting config mask payload)) < max_input_bytes ->
  parse (frame counting config mask payload)
  = Some (mkParsed counting config mask payload).
Proof.
  intros counting config mask payload Hc Hm Hlen.
  unfold parse. apply Z.ltb_lt in Hlen. rewrite Hlen.
  unfold frame, le16. cbn [app].
  set (n := Z.of_nat (length config)).
  set (w := n + (if counting then counting_bit else 0)).
  assert (Hw : 0 <= w < 65536)
    by (subst w; unfold max_config_bytes, counting_bit in *; destruct counting; lia).
  rewrite (u16_of_le16 w Hw).
  assert (Hland : Z.land w max_config_bytes = n).
  { subst w. unfold max_config_bytes, counting_bit in *.
    destruct counting.
    - change 32767 with (Z.ones 15). rewrite Z.land_ones by lia.
      rewrite Z.add_mod by lia. change (32768 mod 2 ^ 15) with 0.
      rewrite Z.add_0_r, Z.mod_mod by lia. apply Z.mod_small. lia.
    - rewrite Z.add_0_r. change 32767 with (Z.ones 15). rewrite Z.land_ones by lia.
      apply Z.mod_small. lia. }
  rewrite Hland. subst n. rewrite Nat2Z.id.
  rewrite skipn_app, Nat.sub_diag, skipn_all. cbn [app skipn le32].
  rewrite (u32_of_le32 mask Hm).
  rewrite firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. rewrite app_nil_r.
  f_equal. f_equal. subst w.
  destruct counting; unfold counting_bit, max_config_bytes in *.
  - apply Z.testbit_true; [lia |]. change (2 ^ 15) with 32768. lia.
  - apply Z.testbit_false; [lia |]. change (2 ^ 15) with 32768. lia.
Qed.

(** An OSS-Fuzz testcase is read back as itself, with no config and no
    allocation mask. *)
Corollary parse_testcase_file : forall payload,
  Z.of_nat (length payload) + 6 < max_input_bytes ->
  parse (testcase_file payload) = Some (mkParsed false [] 0 payload).
Proof.
  intros payload H. apply parse_frame.
  - cbn. unfold max_config_bytes. lia.
  - lia.
  - unfold frame. rewrite !length_app. cbn [length le16 le32]. lia.
Qed.
