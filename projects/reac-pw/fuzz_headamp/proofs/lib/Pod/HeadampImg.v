(** fuzz_headamp's two images hold pod.h's tables where [headamp_plain_addrs] and [headamp_ubsan_addrs] (defined
    here; the record type is Pod/Tables.v's pod_addrs) say: every table pointer, every string it points to (with its
    NUL), the ints, the float bit patterns, case 6's and case 8's type tables, kind 9's String and the separator
    texts, read from the images' loaded segments by computation. (ent_build's jump table entries are code offsets,
    checked by the walk that takes the jump.) The headamp twin of fuzz_role's Pod/RoleImg.v, with the same check
    functions.

    Where each address comes from (unstripped twins of the pinned images: fuzz_headamp.plain sha256
    fe40c856bfc73f2b..., fuzz_headamp.ubsan sha256 1d123858383d3510...; the pinned images the lemmas read are
    61497eebc35c52a0... and 0516fd55d25d0dc2..., harness.yaml). ELF .symtab (LOCAL OBJECT), plain / UBSan:
    ent_build.vocab 0x1ed60 / 0x1f260 (72 B, .data.rel.ro); ent_headamp_key.odd_ch 0x1eda8 / 0x1f2a8 (112 B,
    .data.rel.ro); ent_headamp_key.param.rel 0x105f0 (32 B, rel32) / ent_headamp_key.param 0x1f318 (64 B, pointers);
    ent_build.ints 0x10534 / 0x10544 (56 B); ent_build.floats 0x1056c / 0x1057c (84 B); ent_build.s 0x1042a / 0x1042a
    (14 B, kind 9's "reac.cfg.rate"); case 6's t[] (pod.h:342) = ent_build.t 0x105e0 / 0x105d0; case 8's t[]
    (pod.h:361) = ent_build.t.9 0x105d0 (plain) / ent_build.t.11 0x105e0 (UBSan). With no symbol of their own (the
    merged string literals and the switch table), from the auipc/addi pairs of LLVMFuzzerTestOneInput: the jump
    table (pod.h:281) 0x10510 / 0x10520 (also a `$d` mapping symbol), "." (pod.h:251) 0x1032d, "" (pod.h:0, the
    empty separator) 0x10323, "reac.headamp." (pod.h:253) 0x102bd, in both builds. The strings the pointer tables
    hold were read at the pointers. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Tables.
Require OSSVerify.reac_pw.fuzz_headamp.images.Plain OSSVerify.reac_pw.fuzz_headamp.images.Ubsan.
Import ListNotations.
Open Scope Z_scope.

Definition headamp_plain_addrs : pod_addrs := {|
  pa_jt := 0x10510; pa_vocab := 0x1ed60; pa_vocab_s := [0x1042a; 0x10315; 0x102bd; 0x10410; 0x1036c; 0x10298; 0x103d7; 0x10463; 0x103bd];
  pa_ints := 0x10534; pa_floats := 0x1056c;
  pa_odd := 0x1eda8; pa_odd_s := [0x102cb; 0x103ba; 0x103ca; 0x102ce; 0x102d1; 0x10323; 0x1037a; 0x102ab; 0x10423; 0x103b7; 0x1045c; 0x10324; 0x10438; 0x103a1];
  pa_param := 0x105f0; pa_param_rel := true; pa_param_s := [0x1032f; 0x1045f; 0x102b8; 0x102e6; 0x10473; 0x10323; 0x103cd; 0x10327];
  pa_t6 := 0x105e0; pa_t8 := 0x105d0; pa_s9 := 0x1042a; pa_dot := 0x1032d; pa_empty := 0x10323; pa_hpfx := 0x102bd |}.
Definition headamp_ubsan_addrs : pod_addrs := {|
  pa_jt := 0x10520; pa_vocab := 0x1f260; pa_vocab_s := [0x1042a; 0x10315; 0x102bd; 0x10410; 0x1036c; 0x10298; 0x103d7; 0x10463; 0x103bd];
  pa_ints := 0x10544; pa_floats := 0x1057c;
  pa_odd := 0x1f2a8; pa_odd_s := [0x102cb; 0x103ba; 0x103ca; 0x102ce; 0x102d1; 0x10323; 0x1037a; 0x102ab; 0x10423; 0x103b7; 0x1045c; 0x10324; 0x10438; 0x103a1];
  pa_param := 0x1f318; pa_param_rel := false; pa_param_s := [0x1032f; 0x1045f; 0x102b8; 0x102e6; 0x10473; 0x10323; 0x103cd; 0x10327];
  pa_t6 := 0x105d0; pa_t8 := 0x105e0; pa_s9 := 0x1042a; pa_dot := 0x1032d; pa_empty := 0x10323; pa_hpfx := 0x102bd |}.

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

Lemma headamp_plain_tables : addrs_ok OSSVerify.reac_pw.fuzz_headamp.images.Plain.M.loaded_segments headamp_plain_addrs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma headamp_ubsan_tables : addrs_ok OSSVerify.reac_pw.fuzz_headamp.images.Ubsan.M.loaded_segments headamp_ubsan_addrs = true.
Proof. vm_compute. reflexivity. Qed.

(** A control: the other build's addresses do not pass on this image. *)
Lemma headamp_tables_control :
  addrs_ok OSSVerify.reac_pw.fuzz_headamp.images.Plain.M.loaded_segments headamp_ubsan_addrs = false /\
  addrs_ok OSSVerify.reac_pw.fuzz_headamp.images.Ubsan.M.loaded_segments headamp_plain_addrs = false.
Proof. vm_compute. split; reflexivity. Qed.
