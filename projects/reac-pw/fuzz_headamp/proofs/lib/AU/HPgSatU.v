(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgSat.v at dd9ff534326, the image-B twin
   (fuzz_headamp.asan-ubsan): image B's segments read from lib/AU/Img0U.v (Img0U.rsegs, no local copy); the
   boolean checkers and their soundness lemmas are HPgSat.v's, used by name (no second copy); the descriptor
   check is restated over the table's two ends (HPgSat.global_chk names image A's); every measured fact is image
   B's (ten callee entries, the 43 descriptors of asan_globals and the call that registers them, the 36 strings,
   the 38 cells and the parse's four doubles, the stack-guard cells), and so are the shadow spans and the guard's
   address in the witness memory. *)
(* Image B's witnesses for the memory premises of reac-pw/fuzz_headamp's callee contracts (lib/A/HPgCSpec.v). At the
   pinned image, one concrete pair (H_w, mem_wB) satisfies every string premise (HPgBase.hd_cstr), the read-only
   cell premise (HPgBase.hd_ro_cells) and the stack-guard premise (HPgCSpec.hd_guard_ok) at the image's measured
   addresses (lib/AU/HPgImgB.v), and each callee entry holds its measured first instruction, so those contracts are
   not vacuous on image B. Every address, byte and descriptor field below is checked against the image's loaded
   segments by computation.
   Pinned image: fuzz_headamp.asan-ubsan, sha256 53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94
   (symbol names from its unstripped twin, sha256 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff,
   whose loaded sections are byte-equal to the pin's except .note.gnu.build-id).
   proves no function (kind: statement text) *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YP09 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgImgA HPgSat.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgImgB Img0U.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ======================================== the measured image facts ======================================== *)
(* 1. Callee entries (address, first instruction word, little-endian 4 bytes), in this order: check_no_overrun,
   check_count, check_cells_valid, check_object, check_cells, check_keys, check_refusal, check_plain (each
   `addi sp,sp,-0x10` but check_cells, `addi sp,sp,-0x20`), reac_headamp_prop_parse (`mv a3,zero`),
   reac_headamp_prop_parse_result (`addi sp,sp,-0x100`). Pinned image sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94. *)
Definition headamp_B_entries : list (Z * Z) :=
  [(0x83e7c, 0xff010113); (0x83f2c, 0xff010113); (0x83fcc, 0xff010113); (0x840c0, 0xff010113);
   (0x841c0, 0xfe010113); (0x843a4, 0xff010113); (0x84438, 0xff010113); (0x844cc, 0xff010113);
   (0x849a4, 0x00000693); (0x849ac, 0xf0010113)].
Lemma headamp_B_entries_chk : HPgSat.entries_chk Img0U.rsegs headamp_B_entries = true.
Proof. vm_compute. reflexivity. Qed.

(* 2. The registered globals: (descriptor address, (beg, size, size_with_redzone)). The descriptor table
   asan_globals is [AG_START_B, AG_STOP_B) (its own section, 0xac0 bytes), 43 descriptors of 64 bytes (beg, size,
   size_with_redzone, name, module, has_dynamic_init, location, odr_indicator, each 8 bytes LE; no descriptor has an
   ODR indicator: each odr_indicator word is all ones), in table order: the 40 of .rodata, then ent_build.vocab,
   ent_headamp_key.odd_ch and ent_headamp_key.param of .data.rel.ro. Pinned image sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94. *)
Definition AG_START_B : Z := 0xa10a0.
Definition AG_STOP_B : Z := 0xa1b60.
Definition headamp_B_globals : list (Z * (Z * Z * Z)) :=
  [(0xa10a0, (0x20f00, 14, 32)); (0xa10e0, (0x20f20, 14, 32)); (0xa1120, (0x20f40, 14, 32));
   (0xa1160, (0x20f60, 15, 32)); (0xa11a0, (0x20f80, 14, 32)); (0xa11e0, (0x20fa0, 19, 64));
   (0xa1220, (0x20fe0, 13, 32)); (0xa1260, (0x21000, 16, 32)); (0xa12a0, (0x21020, 13, 32));
   (0xa12e0, (0x21040, 56, 96)); (0xa1320, (0x210a0, 84, 128)); (0xa1360, (0x21120, 16, 32));
   (0xa13a0, (0x21140, 16, 32)); (0xa13e0, (0x21160, 14, 32)); (0xa1420, (0x21180, 3, 32));
   (0xa1460, (0x211a0, 3, 32)); (0xa14a0, (0x211c0, 3, 32)); (0xa14e0, (0x211e0, 3, 32));
   (0xa1520, (0x21200, 21, 64)); (0xa1560, (0x21240, 1, 32)); (0xa15a0, (0x21260, 2, 32));
   (0xa15e0, (0x21280, 3, 32)); (0xa1620, (0x212a0, 3, 32)); (0xa1660, (0x212c0, 3, 32));
   (0xa16a0, (0x212e0, 3, 32)); (0xa16e0, (0x21300, 3, 32)); (0xa1720, (0x21320, 4, 32));
   (0xa1760, (0x21340, 22, 64)); (0xa17a0, (0x21380, 8, 32)); (0xa17e0, (0x213a0, 4, 32));
   (0xa1820, (0x213c0, 5, 32)); (0xa1860, (0x213e0, 4, 32)); (0xa18a0, (0x21400, 6, 32));
   (0xa18e0, (0x21420, 10, 32)); (0xa1920, (0x21440, 6, 32)); (0xa1960, (0x21460, 2, 32));
   (0xa19a0, (0x214a0, 14, 32)); (0xa19e0, (0x214c0, 8, 32)); (0xa1a20, (0x214e0, 4, 32));
   (0xa1a60, (0x21500, 5, 32)); (0xa1aa0, (0x9c4e0, 72, 128)); (0xa1ae0, (0x9c560, 112, 160));
   (0xa1b20, (0x9c600, 64, 96))].
(* HPgSat.global_chk over a table [lo, hi): the row lies in the table at a multiple of 64 from lo, and its beg,
   size and size_with_redzone are the image's, beg 8-aligned and 0 < size <= size_with_redzone. *)
Definition global_chk_in (lo hi : Z) (segs : list Segment) (e : Z * (Z * Z * Z)) : bool :=
  let '(d, (beg, n, r)) := e in
  (lo <=? d) && (d + 64 <=? hi) && ((d - lo) mod 64 =? 0) &&
  HPgSat.img_val_chk segs d 8 beg && HPgSat.img_val_chk segs (d + 8) 8 n && HPgSat.img_val_chk segs (d + 16) 8 r &&
  (beg mod 8 =? 0) && (0 <? n) && (n <=? r).
(* Each row's beg, size and size_with_redzone are the image's; the k-th row is the descriptor at AG_START_B + 64 k;
   the table holds 43. *)
Lemma headamp_B_globals_chk :
  forallb (global_chk_in AG_START_B AG_STOP_B Img0U.rsegs) headamp_B_globals &&
  forallb (fun k => fst (nth k headamp_B_globals HPgSat.gdummy) =? AG_START_B + 64 * Z.of_nat k) (seq 0 43) &&
  (Z.of_nat (length headamp_B_globals) =? (AG_STOP_B - AG_START_B) / 64) = true.
Proof. vm_compute. reflexivity. Qed.
(* They are the rows of HPgImgB.headamp_B_globs (address, size), the record's hi_globs. *)
Lemma headamp_B_globals_globs :
  map (fun g => let '(_, (b, n, _)) := g in (b, n)) headamp_B_globals = headamp_B_globs /\
  hi_globs headamp_himg_B = headamp_B_globs.
Proof. split; reflexivity. Qed.
(* The table is the one the runtime registers: asan.module_ctor (0x8493c) loads a1 and a2 from the cells 0x9d468
   and 0x9d470 (auipc a0, 0x19 at 0x8494c; auipc a2, 0x19 at 0x84950; ld a1, -0x4e4(a0); ld a2, -0x4e0(a2)) and
   calls __asan_register_elf_globals at 0x3fb54 (jal at 0x84964); the two cells hold AG_START_B and AG_STOP_B.
   Pinned image sha256 53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94. *)
Definition headamp_B_reg_words : list (Z * Z) :=
  [(0x8494c, 0x00019517); (0x84950, 0x00019617); (0x84954, 0xb1c53583); (0x84958, 0xb2063603); (0x84964, 0x9f0bb0ef)].
Definition headamp_B_reg_cells : list (Z * Z) := [(0x9d468, AG_START_B); (0x9d470, AG_STOP_B)].
Lemma headamp_B_reg_chk :
  HPgSat.entries_chk Img0U.rsegs headamp_B_reg_words && HPgSat.img_cells_chk Img0U.rsegs headamp_B_reg_cells &&
  (AG_STOP_B - AG_START_B =? 43 * 64) = true.
Proof. vm_compute. reflexivity. Qed.

(* 3. The strings (HPgImgB.headamp_B_strs, address and text): each is followed by a NUL in the image and is the
   registered global of headamp_B_globals with beg = the address and size = length + 1. Pinned image sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94. *)
Lemma headamp_B_strs_chk : HPgSat.cstrs_img_chk Img0U.rsegs headamp_B_globals headamp_B_strs = true.
Proof. vm_compute. reflexivity. Qed.

(* 4. The read-only cells (HPgImgB.headamp_B_cells: the parse's four doubles, the harness's three division
   constants, the 31 pointer cells of .data.rel.ro) and the parse's four doubles (HPgImgB.headamp_B_dcs: 0.5 at
   0x10380, 256.0 at 0x10340, 0xc3e0000000000001 at 0x103f0, 2^63 at 0x10358): (cell, 8-byte value). Pinned image
   sha256 53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94. *)
Lemma headamp_B_cells_chk :
  HPgSat.img_cells_chk Img0U.rsegs headamp_B_cells && HPgSat.img_cells_chk Img0U.rsegs headamp_B_dcs = true.
Proof. vm_compute. reflexivity. Qed.

(* 5. The stack-guard cells: musl's __strtol_internal (0x95770) loads the GOT word 0x9d478 (auipc a0, 8 at 0x95798;
   ld s3, -0x320(a0) at 0x9579c) and reads the guard through it (ld a0, 0(s3) at 0x957a0); the GOT word holds
   0x5f8210, the address of __stack_chk_guard, which lies in .bss [0xa1b80, 0x5f9ab0). Pinned image sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94. *)
Definition GUARD_B : Z := 0x5f8210.
Definition headamp_B_guard_words : list (Z * Z) := [(0x95798, 0x00008517); (0x9579c, 0xce053983); (0x957a0, 0x0009b503)].
Lemma headamp_B_guard_chk :
  HPgSat.entries_chk Img0U.rsegs headamp_B_guard_words && HPgSat.img_cells_chk Img0U.rsegs [(0x9d478, GUARD_B)] &&
  (hi_gotw headamp_himg_B =? 0x9d478) && (hi_guard headamp_himg_B =? GUARD_B) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================ the witness ================================================ *)
(* No byte hidden (HPgSat.H_w). The shadow byte of a granule of a global is HPgSat.granule_shadow over image B's
   descriptors (0 for a full granule, size mod 8 for the last partial one, 0xf9 for a guard one). *)
(* The application spans whose shadow bytes the witness memory holds: the .rodata span of the 40 .rodata globals,
   64-byte aligned at both ends (it holds every string's shadow hull, which hd_cstr's shadow_hull_vis reads), and the
   span of the three .data.rel.ro globals. Every descriptor's [beg, beg + size_with_redzone) lies in one of them
   (lib/AU/HPgSatSegU.v headamp_B_globals_apart_chk). Pinned image sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94. *)
Definition shadow_spans_B : list (Z * Z) := [(0x20f00, 0x21540); (0x9c4e0, 0x9c660)].
(* The shadow byte at u >= SHADOW_OFF for an application address in a span: the byte granule_shadow gives for its
   granule, which is what the runtime writes when it registers the 43 globals. The two parts of the first span that
   no descriptor covers, [0x21480, 0x214a0) (after .str.33's guard bytes) and [0x21520, 0x21540) (after the last
   string's), the runtime never writes: their shadow bytes keep the 0 of the freshly mapped shadow (the hulls of
   the strings at 0x214a0 and 0x21500 read them). Pinned image sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94. *)
Definition span_shadow_B (u : Z) : option byte :=
  if existsb (fun r => (SHADOW_OFF + fst r / 8 <=? u) && (u <? SHADOW_OFF + snd r / 8)) shadow_spans_B
  then Some (Z_to_bv 8 (HPgSat.granule_shadow headamp_B_globals ((u - SHADOW_OFF) * 8)))
  else None.
(* The guard word __stack_chk_guard [GUARD_B, GUARD_B + 8) holds the canary the C library's start-up writes there
   (musl's __init_ssp); HPgSat.GUARD_CAN is one such value. The guard lies in .bss [0xa1b80, 0x5f9ab0) (pinned
   image sha256 53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94), so it is runtime data, not a
   program byte: the witness memory holds its eight bytes. *)
Definition guard_mem_B (u : Z) : option byte :=
  if (GUARD_B <=? u) && (u <? GUARD_B + 8) then Some (Z_to_bv 8 (YO0f.le_byte HPgSat.GUARD_CAN 8 (Z.to_nat (u - GUARD_B))))
  else None.
(* mem_wB holds the shadow bytes of the spans and the guard's eight bytes; every other address reads None, so each
   program byte (string, constant, pointer cell, GOT word) comes from the image through mbyte's fall-back to
   seg_rom. *)
Definition mem_wB : word -> option byte := fun w =>
  if bv_unsigned w <? SHADOW_OFF then guard_mem_B (bv_unsigned w) else span_shadow_B (bv_unsigned w).

(* W1. Every string of headamp_B_strs satisfies hd_cstr at (H_w, mem_wB). *)
Definition cstrs_wit_chk_B (l : list (Z * list Z)) : bool :=
  forallb (fun c => HPgSat.cstr_chk Img0U.rsegs HPgSat.H_w mem_wB (fst c) (snd c)) l.
Lemma hd_cstr_B_chk : cstrs_wit_chk_B headamp_B_strs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hd_cstr_B : forall a s, In (a, s) headamp_B_strs -> hd_cstr Img0U.rsegs HPgSat.H_w mem_wB a s.
Proof.
intros a s Hin. apply HPgSat.cstr_chk_ok.
pose proof hd_cstr_B_chk as E. unfold cstrs_wit_chk_B in E. rewrite forallb_forall in E.
exact (E (a, s) Hin).
Qed.
Print Assumptions hd_cstr_B.
(* A control: without the shadow bytes the checker refuses the first string (its shadow reads None). *)
Lemma hd_cstr_B_control :
  HPgSat.cstr_chk Img0U.rsegs HPgSat.H_w (fun _ => None)
    (fst (nth 0 headamp_B_strs (0, []))) (snd (nth 0 headamp_B_strs (0, []))) = false.
Proof. vm_compute. reflexivity. Qed.

(* W2. The read-only cells and the parse's four doubles. *)
Lemma hd_ro_cells_B_chk :
  HPgSat.cells_chk Img0U.rsegs (mrestrict HPgSat.H_w mem_wB) headamp_B_cells &&
  HPgSat.cells_chk Img0U.rsegs (mrestrict HPgSat.H_w mem_wB) headamp_B_dcs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hd_ro_cells_B :
  hd_ro_cells Img0U.rsegs HPgSat.H_w mem_wB headamp_B_cells /\ hd_ro_cells Img0U.rsegs HPgSat.H_w mem_wB headamp_B_dcs.
Proof.
pose proof hd_ro_cells_B_chk as E. apply andb_prop in E. destruct E as [E1 E2].
split; unfold hd_ro_cells; apply HPgSat.cells_chk_ok; assumption.
Qed.
Print Assumptions hd_ro_cells_B.

(* W3. The stack-guard premise at (hi_gotw, hi_guard) = (0x9d478, 0x5f8210): the GOT word (read from the image)
   holds the guard's address, and the guard's word (the witness memory's eight bytes) is readable. *)
Lemma hd_guard_B_chk :
  HPgSat.guard_chk (aview Img0U.rsegs HPgSat.H_w mem_wB) (hi_gotw headamp_himg_B) (hi_guard headamp_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hd_guard_B : hd_guard_ok (aview Img0U.rsegs HPgSat.H_w mem_wB) (hi_gotw headamp_himg_B) (hi_guard headamp_himg_B).
Proof. exact (HPgSat.guard_chk_ok _ _ _ hd_guard_B_chk). Qed.
Print Assumptions hd_guard_B.
(* A measured fact beside W3: the snapshot's fourth loaded segment spans .bss too (its bytes there are 0), so the
   guard's word is readable from the image alone; the premise holds with no memory byte. *)
Lemma hd_guard_B_img_chk :
  HPgSat.guard_chk (aview Img0U.rsegs HPgSat.H_w (fun _ => None)) (hi_gotw headamp_himg_B) (hi_guard headamp_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.

(* W4. Each callee entry holds its measured first instruction word in the image. *)
Lemma hd_entries_B : forall a w, In (a, w) headamp_B_entries ->
  forall k, (k < 4)%nat -> seg_rom Img0U.rsegs (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (YO0f.le_byte w 4 k)).
Proof.
intros a w Hin k Hk. refine (HPgSat.img_val_chk_ok Img0U.rsegs a 4 w _ k Hk).
pose proof headamp_B_entries_chk as E. unfold HPgSat.entries_chk in E. rewrite forallb_forall in E.
exact (E (a, w) Hin).
Qed.
Print Assumptions hd_entries_B.

(* W5. The string premises of hd_parse_result_specX (and hd_parse_specX) at (akey, aph, apad, asens) =
   (0x214a0, 0x214c0, 0x214e0, 0x21500) with the shared model's texts (Pod/Headamp.v HA_PREFIX, NAME_PHANTOM,
   NAME_PAD, NAME_SENS), in the order hd_parse_args states them; then the harness's own four literals at
   (hkey, hph, hpad, hsens) = (0x20f40, 0x21380, 0x213a0, 0x213c0) with the same texts (expect_of compares the
   pod's names with them: strncmp 0x83288, strcmp 0x83410, 0x83424, 0x83438). The texts are
   HPgImgB.headamp_B_strs' entries 32 .. 35 and 2, 24, 25, 26; the model texts are image-independent
   (HPgImgA.headamp_A_key_text, headamp_A_param_texts compute them). *)
Lemma hd_cstr_B_at : forall n a s, nth_error headamp_B_strs n = Some (a, s) -> hd_cstr Img0U.rsegs HPgSat.H_w mem_wB a s.
Proof. intros n a s E. apply hd_cstr_B. eapply nth_error_In. exact E. Qed.
Lemma hd_sat_parse_strs_B :
  (hd_cstr Img0U.rsegs HPgSat.H_w mem_wB (hi_akey headamp_himg_B) (hd_zbytes Headamp.HA_PREFIX) /\
   hd_cstr Img0U.rsegs HPgSat.H_w mem_wB (hi_aph headamp_himg_B) (hd_zbytes Headamp.NAME_PHANTOM) /\
   hd_cstr Img0U.rsegs HPgSat.H_w mem_wB (hi_apad headamp_himg_B) (hd_zbytes Headamp.NAME_PAD) /\
   hd_cstr Img0U.rsegs HPgSat.H_w mem_wB (hi_asens headamp_himg_B) (hd_zbytes Headamp.NAME_SENS)) /\
  (hd_cstr Img0U.rsegs HPgSat.H_w mem_wB (hi_hkey headamp_himg_B) (hd_zbytes Headamp.HA_PREFIX) /\
   hd_cstr Img0U.rsegs HPgSat.H_w mem_wB (hi_hph headamp_himg_B) (hd_zbytes Headamp.NAME_PHANTOM) /\
   hd_cstr Img0U.rsegs HPgSat.H_w mem_wB (hi_hpad headamp_himg_B) (hd_zbytes Headamp.NAME_PAD) /\
   hd_cstr Img0U.rsegs HPgSat.H_w mem_wB (hi_hsens headamp_himg_B) (hd_zbytes Headamp.NAME_SENS)).
Proof.
destruct HPgImgA.headamp_A_param_texts as (Ep & Ea & Es).
rewrite HPgImgA.headamp_A_key_text, Ep, Ea, Es.
split; (split; [|split; [|split]]).
- apply (hd_cstr_B_at 32); reflexivity.
- apply (hd_cstr_B_at 33); reflexivity.
- apply (hd_cstr_B_at 34); reflexivity.
- apply (hd_cstr_B_at 35); reflexivity.
- apply (hd_cstr_B_at 2); reflexivity.
- apply (hd_cstr_B_at 24); reflexivity.
- apply (hd_cstr_B_at 25); reflexivity.
- apply (hd_cstr_B_at 26); reflexivity.
Qed.
Print Assumptions hd_sat_parse_strs_B.
