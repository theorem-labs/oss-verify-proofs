(** fuzz_rate's two images hold pod.h's tables where [rate_plain_addrs] and [rate_ubsan_addrs] (defined here; the
    record type is Pod/Tables.v's pod_addrs) say:
    every table pointer, every string it points to (with its NUL), the ints, the float bit patterns, case 6's and
    case 8's type tables, kind 9's String and the separator texts, read from the images' loaded segments by
    computation. (ent_build's jump table entries are code offsets, checked by the walk that takes the jump.) The
    per-target part of the tables check; fuzz_role and fuzz_headamp have their own. The record values were read from
    fuzz_rate's ELF files.

    And the key: the text "reac.cfg.rate" and its NUL at 0x1045e in both images, the address both strcmp calls of
    each image pass as the key (plain: expect_rate inlined in LLVMFuzzerTestOneInput, auipc 0x14280 / addi s5 0x142a0,
    strcmp at 0x14308; reac_rate_prop_parse, auipc 0x14d68 / addi s1 0x14d6c, strcmp at 0x14dc4. UBSan: auipc 0x14284
    / addi a1 0x142b0, strcmp at 0x14360; auipc 0x150f0 / addi s1 0x150f4, strcmp at 0x1516c). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Tables Rate.
Require OSSVerify.reac_pw.fuzz_rate.images.Plain OSSVerify.reac_pw.fuzz_rate.images.Ubsan.
Import ListNotations.
Open Scope Z_scope.

Definition rate_plain_addrs : pod_addrs := {|
  pa_jt := 0x10548; pa_vocab := 0x1e8e0; pa_vocab_s := [0x1045e; 0x10320; 0x102bd; 0x10444; 0x10386; 0x10298; 0x1040b; 0x1049c; 0x103e6];
  pa_ints := 0x1056c; pa_floats := 0x105a4;
  pa_odd := 0x1e928; pa_odd_s := [0x102cb; 0x103d4; 0x103f3; 0x102ce; 0x102dc; 0x1032e; 0x10394; 0x102ab; 0x10457; 0x103d1; 0x10495; 0x1032f; 0x1046c; 0x103bb];
  pa_param := 0x10628; pa_param_rel := true; pa_param_s := [0x1033a; 0x10498; 0x102b8; 0x102f1; 0x104ac; 0x1032e; 0x103f6; 0x10332];
  pa_t6 := 0x10618; pa_t8 := 0x10608; pa_s9 := 0x1045e; pa_dot := 0x10338; pa_empty := 0x1032e; pa_hpfx := 0x102bd |}.
Definition rate_ubsan_addrs : pod_addrs := {|
  pa_jt := 0x10558; pa_vocab := 0x1ecc8; pa_vocab_s := [0x1045e; 0x10320; 0x102bd; 0x10444; 0x10386; 0x10298; 0x1040b; 0x1049c; 0x103e6];
  pa_ints := 0x1057c; pa_floats := 0x105b4;
  pa_odd := 0x1ed10; pa_odd_s := [0x102cb; 0x103d4; 0x103f3; 0x102ce; 0x102dc; 0x1032e; 0x10394; 0x102ab; 0x10457; 0x103d1; 0x10495; 0x1032f; 0x1046c; 0x103bb];
  pa_param := 0x1ed80; pa_param_rel := false; pa_param_s := [0x1033a; 0x10498; 0x102b8; 0x102f1; 0x104ac; 0x1032e; 0x103f6; 0x10332];
  pa_t6 := 0x10608; pa_t8 := 0x10618; pa_s9 := 0x1045e; pa_dot := 0x10338; pa_empty := 0x1032e; pa_hpfx := 0x102bd |}.

(** The n bytes of the image at a, as values. *)
Definition img_rd (segs : list Segment) (a : Z) (n : nat) : option (list Z) :=
  option_map (map bv_unsigned) (memory_read segs (Z_to_bv 64 a) (N.of_nat n)).

Definition zl (l : list byte) : list Z := map bv_unsigned l.
Definition le_z (n : nat) (v : Z) : list Z := zl (Z_to_le_bytes n v).

Fixpoint zl_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && zl_eqb a' b'
  | _, _ => false
  end.

Definition rd_is (segs : list Segment) (a : Z) (l : list Z) : bool :=
  match img_rd segs a (length l) with Some l' => zl_eqb l' l | None => false end.

(** The C string s (and its NUL) at a. *)
Definition cstr_at (segs : list Segment) (a : Z) (s : list byte) : bool := rd_is segs a (zl s ++ [0]).

(** A table of 8-byte pointers at t to the strings ss, the pointers being ps. *)
Fixpoint ptr_table (segs : list Segment) (t : Z) (ps : list Z) (ss : list (list byte)) : bool :=
  match ps, ss with
  | [], [] => true
  | p :: ps', s :: ss' => rd_is segs t (le_z 8 p) && cstr_at segs p s && ptr_table segs (t + 8) ps' ss'
  | _, _ => false
  end.

(** param[] as 4-byte offsets from the table (plain) at t + 4 i. *)
Fixpoint rel_table (segs : list Segment) (base t : Z) (ps : list Z) (ss : list (list byte)) : bool :=
  match ps, ss with
  | [], [] => true
  | p :: ps', s :: ss' => rd_is segs t (le_z 4 (p - base)) && cstr_at segs p s && rel_table segs base (t + 4) ps' ss'
  | _, _ => false
  end.

Definition addrs_ok (segs : list Segment) (pa : pod_addrs) : bool :=
  ptr_table segs (pa_vocab pa) (pa_vocab_s pa) vocab &&
  ptr_table segs (pa_odd pa) (pa_odd_s pa) odd_ch &&
  (if pa_param_rel pa then rel_table segs (pa_param pa) (pa_param pa) (pa_param_s pa) param
   else ptr_table segs (pa_param pa) (pa_param_s pa) param) &&
  rd_is segs (pa_ints pa) (flat_map (le_z 4) ints) &&
  rd_is segs (pa_floats pa) (flat_map (le_z 4) float_bits) &&
  rd_is segs (pa_t6 pa) (flat_map (le_z 4) t6) &&
  rd_is segs (pa_t8 pa) (flat_map (le_z 4) t8) &&
  cstr_at segs (pa_s9 pa) S9 && cstr_at segs (pa_dot pa) DOT && cstr_at segs (pa_empty pa) [] &&
  cstr_at segs (pa_hpfx pa) HPFX.

Lemma rate_plain_tables : addrs_ok OSSVerify.reac_pw.fuzz_rate.images.Plain.M.loaded_segments rate_plain_addrs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rate_ubsan_tables : addrs_ok OSSVerify.reac_pw.fuzz_rate.images.Ubsan.M.loaded_segments rate_ubsan_addrs = true.
Proof. vm_compute. reflexivity. Qed.

(** A control: the other build's addresses do not pass on this image. *)
Lemma rate_tables_control :
  addrs_ok OSSVerify.reac_pw.fuzz_rate.images.Plain.M.loaded_segments rate_ubsan_addrs = false /\
  addrs_ok OSSVerify.reac_pw.fuzz_rate.images.Ubsan.M.loaded_segments rate_plain_addrs = false.
Proof. vm_compute. split; reflexivity. Qed.

(** The key both parsers compare with (Pod/Rate.v's [RATE_KEY]), NUL-terminated at 0x1045e. *)
Definition RATE_KEY_ADDR : Z := 0x1045e.
Lemma rate_key_plain : cstr_at OSSVerify.reac_pw.fuzz_rate.images.Plain.M.loaded_segments RATE_KEY_ADDR RATE_KEY = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rate_key_ubsan : cstr_at OSSVerify.reac_pw.fuzz_rate.images.Ubsan.M.loaded_segments RATE_KEY_ADDR RATE_KEY = true.
Proof. vm_compute. reflexivity. Qed.
