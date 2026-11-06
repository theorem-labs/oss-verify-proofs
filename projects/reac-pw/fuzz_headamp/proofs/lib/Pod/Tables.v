(** The tables of fuzz/pod.h (pod.h:226-232, :267-278, :342, :361, :369), as the model reads them, and where each
    binary holds them. The contents are the same in the six images of fuzz_role, fuzz_rate and fuzz_headamp (plain and
    UBSan); the addresses differ, so they are a per-image record [pod_addrs]. The values below were read from the six
    ELF files (the unstripped twins of the pinned images): the table pointers, the strings they point to, the ints and
    the float bit patterns. A per-image check against the image bytes is a computation over that image's segments.

    floats[] is kept as the bit patterns of the floats (what memcpy puts in the body). *)
From Stdlib Require Import String Ascii ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor.
Import ListNotations.
Open Scope Z_scope.

Local Open Scope string_scope.
(** ent_build's vocab[] (pod.h:267-270): keys of kind 1. *)
Definition vocab_s : list string :=
  ["reac.cfg.rate"; "reac.cfg.role"; "reac.headamp."; "reac.cfg.rate "; "REAC.cfg.rate";
   "some.other.control"; "reac.headamp"; "reac.cfg.role.x"; "reac.cfg.rat"].
(** ent_headamp_key's odd_ch[] (pod.h:226-229) and param[] (pod.h:230-232). *)
Definition odd_ch_s : list string :=
  ["-1"; "+3"; " 7"; "07"; "99999999999999999999"; ""; "x"; "3a"; "-0"; String (ascii_of_nat 9) "5";
   "48"; "47"; "0x1"; "-99999999999999999999"].
Definition param_s : list string := ["phantom"; "pad"; "sens"; "PAD"; "sensx"; ""; "phantom.x"; "sens "].
(** The separators and the fixed text of a head-amp key (pod.h:251, :253) and kind 9's String (pod.h:369). *)
Definition HPFX : list byte := sbytes "reac.headamp.".
Definition DOT : list byte := sbytes ".".
Definition S9 : list byte := sbytes "reac.cfg.rate".
Local Close Scope string_scope.

Definition vocab : list (list byte) := map sbytes vocab_s.
Definition odd_ch : list (list byte) := map sbytes odd_ch_s.
Definition param : list (list byte) := map sbytes param_s.
(** ints[] (pod.h:271-273), as int32 values. *)
Definition ints : list Z :=
  [0; 1; 2; -1; 44100; 48000; 96000; 55; 56; 255; 256; 47999; -2147483648; 2147483647].
(** floats[] (pod.h:274-278), as binary32 bit patterns. *)
Definition float_bits : list Z :=
  [0x00000000; 0x3effffff; 0x3f000000; 0x3f800000; 0xbf333333; 0xbf000000; 0xbeffffff; 0x472c4466; 0x473b7f80;
   0x47bb8000; 0x501502f9; 0xd01502f9; 0x437f6666; 0x437f8000; 0x425a6666; 0x4effffff; 0x4f000000; 0xcf000000;
   0xcf000001; 0x3f000002; 0x3fbfffff].
(** case 6's t[] (pod.h:342: LONG DOUBLE ID NONE) and case 8's t[] (pod.h:361: INT FLOAT BOOL STRING). *)
Definition t6 : list Z := [5; 7; 3; 1].
Definition t8 : list Z := [4; 6; 2; 8].

(** ** Where an image holds them *)
(** pa_jt: ent_build's switch table (9 rel32 entries; case 9 is taken by a branch). pa_vocab / pa_odd: arrays of
    8-byte pointers to the strings pa_vocab_s / pa_odd_s. pa_param: 8 rel32 offsets from the table to the strings
    when pa_param_rel, else 8-byte pointers. pa_t6 / pa_t8: 4 u32 each. pa_s9, pa_dot, pa_empty, pa_hpfx: the
    NUL-terminated texts S9, ".", "" and HPFX. *)
Record pod_addrs := {
  pa_jt : Z; pa_vocab : Z; pa_vocab_s : list Z; pa_ints : Z; pa_floats : Z;
  pa_odd : Z; pa_odd_s : list Z; pa_param : Z; pa_param_rel : bool; pa_param_s : list Z;
  pa_t6 : Z; pa_t8 : Z; pa_s9 : Z; pa_dot : Z; pa_empty : Z; pa_hpfx : Z }.


(** ** Facts by computation *)
Lemma vocab_length : length vocab = 9%nat. Proof. reflexivity. Qed.
Lemma odd_ch_length : length odd_ch = 14%nat. Proof. reflexivity. Qed.
Lemma param_length : length param = 8%nat. Proof. reflexivity. Qed.
Lemma ints_length : length ints = 14%nat. Proof. reflexivity. Qed.
Lemma float_bits_length : length float_bits = 21%nat. Proof. reflexivity. Qed.

(** strlen of each string (the measured values). *)
Lemma vocab_strlen : map (@length byte) vocab = [13; 13; 13; 14; 13; 18; 12; 15; 12]%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma odd_ch_strlen : map (@length byte) odd_ch = [2; 2; 2; 2; 20; 0; 1; 2; 2; 2; 2; 2; 3; 21]%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma param_strlen : map (@length byte) param = [7; 3; 4; 3; 5; 0; 9; 5]%nat.
Proof. vm_compute. reflexivity. Qed.

Definition no_nul (l : list byte) : bool := forallb (fun b => negb (bv_unsigned b =? 0)) l.
Lemma tables_no_nul :
  forallb no_nul vocab && forallb no_nul odd_ch && forallb no_nul param && no_nul HPFX && no_nul DOT
  && no_nul S9 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ints_range : forallb (fun v => (-2^31 <=? v) && (v <? 2^31)) ints = true.
Proof. vm_compute. reflexivity. Qed.
Lemma float_bits_range : forallb (fun v => (0 <=? v) && (v <? 2^32)) float_bits = true.
Proof. vm_compute. reflexivity. Qed.
