(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Pod/RoleImgA.v at 7d5486c1b1d; fuzz_rate's image A: its addresses, the key of both strcmp calls, the % 24 multiplier, closed_list and ordered; the record check is Pod/RateImg.v's. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/Pod/RateImgA.v at 178e33ba81ec; the same facts for image B (fuzz_rate.asan-ubsan): its three .data.rel.ro table addresses, its jump-table targets, its % 33 constant cell, its pcs, its read-only range, the image module AsanUbsan, and a control against the plain and the UBSan image. *)
(** fuzz_rate's image B (fuzz_rate.asan-ubsan, pinned sha256
    c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14)
    holds pod.h's tables where [rate_asanubsan_addrs] says (the record type is Pod/Tables.v's pod_addrs and the check
    is Pod/RateImg.v's addrs_ok, as for the plain and the UBSan image), the key both strcmp calls pass where
    [RATE_ASANUBSAN_KEY_MAIN] and [RATE_ASANUBSAN_KEY_PARSE] say, ent_build's jump table where
    [rate_asanubsan_jt_tgts] says, the four multipliers that LLVMFuzzerTestOneInput loads from the constant pool
    where [rate_asanubsan_kcells] says, and the two tables of the three closed rates, fuzz_rate.c's closed_list and
    reac_rate_drivable_csv's ordered, where [RATE_ASANUBSAN_CLOSED] and [RATE_ASANUBSAN_ORDERED] say. Each address
    was measured on the unstripped twin of the pinned image (sha256
    a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1; its loaded bytes are the pinned image's except
    the ELF header's section-table fields 0x10028 .. 0x1003e and the build-id note 0x102b8 .. 0x102cb) and each byte
    is checked below against the pinned image's loaded segments by computation. Statement data and computation
    only: proves no function.

    Image B keeps each table and each string as a registered global of its own, so no string shares bytes with
    another (the plain image keeps the key and kind 9's String in vocab[0]'s bytes, 0x1045e): vocab, odd_ch and param
    are arrays of 8-byte pointers in .data.rel.ro (0x9bdc0, 0x9be40, 0x9bee0; param is an array of pointers here, not
    of offsets); ints, floats, case 6's t (ent_build.t), case 8's t (ent_build.t.11) and kind 9's s are in .rodata;
    ent_headamp_key's texts "reac.headamp.", "." and "" are .str.4 0x20fe0 (also vocab[2]), .str.33 0x21500 and
    .str.17 0x212e0 (also odd_ch[5] and param[5]). Every string address and every string's bytes are image A's; the
    three pointer tables are image A's at +0x300.

    The key "reac.cfg.rate" (Pod/Rate.v's RATE_KEY) is two globals, one per translation unit: fuzz_rate.c's .str
    0x20fa0 (also vocab[0]), which expect_rate inlined in LLVMFuzzerTestOneInput passes to the strcmp wrapper (auipc
    0x82c4c / addi a1 0x82c50, call 0x82c64), and reac_rate_cfg.c's .str.8 0x21720, which reac_rate_prop_parse passes
    (auipc 0x84904 / addi s2 0x84914, mv a1,s2 0x849d0, call 0x849d4). Kind 9's s 0x21200 holds the same text.

    The jump table: `jr a1` 0x8145c takes kinds 0 .. 8 (kind 9 leaves by `bltu a2,a1` 0x81438 to 0x81a94) to 0x20f6c
    plus the sign-extended 4-byte entry of the kind in the table at .rodata 0x20f6c (`auipc` / `addi` 0x81440 ..
    0x81444, `lw` 0x8144c). The constant pool: `ld` 0x80a94 reads 0x10330 for buflen = fuzz_u8 % 24
    (fuzz_rate.c:238); `ld` 0x81374 reads 0x10418 for count = fuzz_u8 % 33 (pod.h:424); `ld` 0x817fc and `ld` 0x81de4
    read 0x10318 for ints[(m >> 1) % 14] (pod.h:300) and odd_ch[c % 14] (pod.h:247); `ld` 0x81f6c reads 0x10310 for
    floats[(m >> 1) % 21] (pod.h:319). Each value is ceil(2^64 / d), so the high word of its product with x is x / d;
    the lemmas at the end give the quotient and the remainder each instruction sequence computes. closed_list 0x21520
    is read by LLVMFuzzerTestOneInput (`addi s2` 0x82e3c), check_list (0x836a0, 0x83708) and check_csv (0x838fc);
    ordered 0x216a0 by reac_rate_drivable_csv (`addi s7` 0x84424). Both hold Pod/RateCfg.v's closed_list.

    The facts come in two forms: Pod/RateImg.v's (memory_read of a whole run: addrs_ok, jt_ok, rd_is, cstr_at) and
    byte by byte through YK11.seg_rom (img_z, rom_is), the form in which rom_view (Reusable/YG0d.v) gives a reader's
    byte of read-only data. Every address of .rodata here lies in image B's read-only PT_LOAD [0x10000, 0x2fa0c)
    ([rate_asanubsan_ro], the form of YG0d.in_rom); the three pointer tables lie in .data.rel.ro, in the writable
    PT_LOAD that starts at 0x9b998. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK11.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Tables Rate RateImg RateCfg.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan OSSVerify.reac_pw.fuzz_rate.images.Plain
  OSSVerify.reac_pw.fuzz_rate.images.Ubsan.
Import ListNotations.
Open Scope Z_scope.

Local Abbreviation segsB := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments (only parsing).

(** ** The tables (Pod/Tables.v's record) *)
Definition rate_asanubsan_addrs : pod_addrs := {|
  pa_jt := 0x20f6c; pa_vocab := 0x9bdc0;
  pa_vocab_s := [0x20fa0; 0x20fc0; 0x20fe0; 0x21000; 0x21020; 0x21040; 0x21080; 0x210a0; 0x210c0];
  pa_ints := 0x210e0; pa_floats := 0x21140;
  pa_odd := 0x9be40;
  pa_odd_s := [0x21220; 0x21240; 0x21260; 0x21280; 0x212a0; 0x212e0; 0x21300; 0x21320; 0x21340; 0x21360; 0x21380;
               0x213a0; 0x213c0; 0x213e0];
  pa_param := 0x9bee0; pa_param_rel := false;
  pa_param_s := [0x21420; 0x21440; 0x21460; 0x21480; 0x214a0; 0x212e0; 0x214c0; 0x214e0];
  pa_t6 := 0x211c0; pa_t8 := 0x211e0; pa_s9 := 0x21200; pa_dot := 0x21500; pa_empty := 0x212e0; pa_hpfx := 0x20fe0 |}.

Lemma rate_asanubsan_tables : addrs_ok segsB rate_asanubsan_addrs = true.
Proof. vm_compute. reflexivity. Qed.

(** A control: the other builds' addresses do not pass on image B, nor image B's on the other builds. *)
Lemma rate_asanubsan_tables_control :
  addrs_ok segsB rate_plain_addrs = false /\ addrs_ok segsB rate_ubsan_addrs = false /\
  addrs_ok OSSVerify.reac_pw.fuzz_rate.images.Plain.M.loaded_segments rate_asanubsan_addrs = false /\
  addrs_ok OSSVerify.reac_pw.fuzz_rate.images.Ubsan.M.loaded_segments rate_asanubsan_addrs = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ** The key of both strcmp calls (Pod/Rate.v's [RATE_KEY]), each NUL-terminated *)
Definition RATE_ASANUBSAN_KEY_MAIN : Z := 0x20fa0.
Definition RATE_ASANUBSAN_KEY_PARSE : Z := 0x21720.

Lemma rate_asanubsan_key :
  cstr_at segsB RATE_ASANUBSAN_KEY_MAIN RATE_KEY = true /\
  cstr_at segsB RATE_ASANUBSAN_KEY_PARSE RATE_KEY = true.
Proof. vm_compute. split; reflexivity. Qed.

(** ** ent_build's jump table *)
(** The targets of kinds 0 .. 8. *)
Definition rate_asanubsan_jt_tgts : list Z :=
  [0x81460; 0x81900; 0x817c4; 0x81838; 0x81774; 0x81968; 0x819a0; 0x81888; 0x819f0].

(** At t + 4 k the table at jt holds the offset of target k from jt, as 4 little-endian bytes; each offset is in
    [0, 2^31), so the sign extension of `lw` keeps it. *)
Fixpoint jt_ok (segs : list Segment) (jt t : Z) (tgts : list Z) : bool :=
  match tgts with
  | [] => true
  | g :: gs => (0 <=? g - jt) && (g - jt <? 2^31) && rd_is segs t (le_z 4 (g - jt)) && jt_ok segs jt (t + 4) gs
  end.

Lemma rate_asanubsan_jt :
  jt_ok segsB (pa_jt rate_asanubsan_addrs) (pa_jt rate_asanubsan_addrs) rate_asanubsan_jt_tgts = true.
Proof. vm_compute. reflexivity. Qed.

(** Each target is an instruction of LLVMFuzzerTestOneInput [0x8076c, 0x83558), at an offset in [0, 2^31). *)
Lemma rate_asanubsan_jt_tgts_range : forall k, (k < 9)%nat ->
  0 <= nth k rate_asanubsan_jt_tgts 0 - 0x20f6c < 2^31 /\ 0x8076c <= nth k rate_asanubsan_jt_tgts 0 < 0x83558.
Proof.
  intros k Hk. do 9 (destruct k as [|k]; [cbn; lia|]). lia.
Qed.

(** ** The constant pool *)
Definition rate_asanubsan_k33 : Z := 0x07c1f07c1f07c1f1.
Definition rate_asanubsan_k24 : Z := 0x0aaaaaaaaaaaaaab.
Definition rate_asanubsan_k14 : Z := 0x124924924924924a.
Definition rate_asanubsan_k21 : Z := 0x0c30c30c30c30c31.
(** (address, 8-byte value). *)
Definition rate_asanubsan_kcells : list (Z * Z) :=
  [(0x10418, rate_asanubsan_k33); (0x10330, rate_asanubsan_k24); (0x10318, rate_asanubsan_k14);
   (0x10310, rate_asanubsan_k21)].

Lemma rate_asanubsan_kcells_rd :
  forallb (fun c => rd_is segsB (fst c) (le_z 8 (snd c))) rate_asanubsan_kcells = true.
Proof. vm_compute. reflexivity. Qed.

(** ** closed_list and ordered *)
Definition RATE_ASANUBSAN_CLOSED : Z := 0x21520.
Definition RATE_ASANUBSAN_ORDERED : Z := 0x216a0.

Lemma rate_asanubsan_rates_rd :
  rd_is segsB RATE_ASANUBSAN_CLOSED (flat_map (le_z 4) closed_list) = true /\
  rd_is segsB RATE_ASANUBSAN_ORDERED (flat_map (le_z 4) closed_list) = true.
Proof. vm_compute. split; reflexivity. Qed.

(** ** Byte by byte through seg_rom *)
(** The image's byte at a, as a value. *)
Definition img_z (segs : list Segment) (a : Z) : option Z :=
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 a)).

(** The values l at a, one byte each. *)
Definition rom_is (segs : list Segment) (a : Z) (l : list Z) : bool :=
  forallb (fun k => match img_z segs (a + Z.of_nat k) with Some v => v =? nth k l 0 | None => false end)
    (seq 0 (length l)).

Lemma rom_is_ok : forall segs a l, rom_is segs a l = true ->
  forall k, (k < length l)%nat -> img_z segs (a + Z.of_nat k) = Some (nth k l 0).
Proof.
  intros segs a l H k Hk. unfold rom_is in H. rewrite forallb_forall in H.
  specialize (H k ltac:(apply in_seq; lia)). cbv beta in H. revert H.
  destruct (img_z segs (a + Z.of_nat k)) as [v|]; intros H;
    [apply Z.eqb_eq in H; subst v; reflexivity | discriminate H].
Qed.

Local Lemma seq_ok : forall (f : nat -> bool) (n : nat), forallb f (seq 0 n) = true ->
  forall k, (k < n)%nat -> f k = true.
Proof. intros f n H k Hk. rewrite forallb_forall in H. apply H. apply in_seq. lia. Qed.

(** The pointer tables: entry k (8 bytes) and the C string it points to (its bytes and its NUL). *)
Lemma rate_asanubsan_vocab_chk : forallb (fun k =>
  rom_is segsB (0x9bdc0 + 8 * Z.of_nat k) (le_z 8 (nth k (pa_vocab_s rate_asanubsan_addrs) 0)) &&
  rom_is segsB (nth k (pa_vocab_s rate_asanubsan_addrs) 0) (zl (nth k vocab []) ++ [0])) (seq 0 9) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rate_asanubsan_odd_chk : forallb (fun k =>
  rom_is segsB (0x9be40 + 8 * Z.of_nat k) (le_z 8 (nth k (pa_odd_s rate_asanubsan_addrs) 0)) &&
  rom_is segsB (nth k (pa_odd_s rate_asanubsan_addrs) 0) (zl (nth k odd_ch []) ++ [0])) (seq 0 14) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rate_asanubsan_param_chk : forallb (fun k =>
  rom_is segsB (0x9bee0 + 8 * Z.of_nat k) (le_z 8 (nth k (pa_param_s rate_asanubsan_addrs) 0)) &&
  rom_is segsB (nth k (pa_param_s rate_asanubsan_addrs) 0) (zl (nth k param []) ++ [0])) (seq 0 8) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rate_asanubsan_vocab_rom : forall k, (k < 9)%nat ->
  rom_is segsB (0x9bdc0 + 8 * Z.of_nat k) (le_z 8 (nth k (pa_vocab_s rate_asanubsan_addrs) 0)) = true /\
  rom_is segsB (nth k (pa_vocab_s rate_asanubsan_addrs) 0) (zl (nth k vocab []) ++ [0]) = true.
Proof. intros k Hk. apply andb_prop. exact (seq_ok _ 9 rate_asanubsan_vocab_chk k Hk). Qed.

Lemma rate_asanubsan_odd_rom : forall k, (k < 14)%nat ->
  rom_is segsB (0x9be40 + 8 * Z.of_nat k) (le_z 8 (nth k (pa_odd_s rate_asanubsan_addrs) 0)) = true /\
  rom_is segsB (nth k (pa_odd_s rate_asanubsan_addrs) 0) (zl (nth k odd_ch []) ++ [0]) = true.
Proof. intros k Hk. apply andb_prop. exact (seq_ok _ 14 rate_asanubsan_odd_chk k Hk). Qed.

Lemma rate_asanubsan_param_rom : forall k, (k < 8)%nat ->
  rom_is segsB (0x9bee0 + 8 * Z.of_nat k) (le_z 8 (nth k (pa_param_s rate_asanubsan_addrs) 0)) = true /\
  rom_is segsB (nth k (pa_param_s rate_asanubsan_addrs) 0) (zl (nth k param []) ++ [0]) = true.
Proof. intros k Hk. apply andb_prop. exact (seq_ok _ 8 rate_asanubsan_param_chk k Hk). Qed.

(** The arrays of 4-byte values: element i at the table + 4 i. *)
Lemma rate_asanubsan_arrays_chk :
  forallb (fun i => rom_is segsB (0x210e0 + 4 * Z.of_nat i) (le_z 4 (nth i ints 0))) (seq 0 14) &&
  forallb (fun i => rom_is segsB (0x21140 + 4 * Z.of_nat i) (le_z 4 (nth i float_bits 0))) (seq 0 21) &&
  forallb (fun i => rom_is segsB (0x211c0 + 4 * Z.of_nat i) (le_z 4 (nth i t6 0))) (seq 0 4) &&
  forallb (fun i => rom_is segsB (0x211e0 + 4 * Z.of_nat i) (le_z 4 (nth i t8 0))) (seq 0 4) &&
  forallb (fun k => rom_is segsB (0x20f6c + 4 * Z.of_nat k) (le_z 4 (nth k rate_asanubsan_jt_tgts 0 - 0x20f6c)))
    (seq 0 9) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rate_asanubsan_ints_rom : forall i, (i < 14)%nat ->
  rom_is segsB (0x210e0 + 4 * Z.of_nat i) (le_z 4 (nth i ints 0)) = true.
Proof.
  intros i Hi. pose proof rate_asanubsan_arrays_chk as H. repeat rewrite andb_true_iff in H.
  destruct H as ((((H & _) & _) & _) & _). exact (seq_ok _ 14 H i Hi).
Qed.

Lemma rate_asanubsan_floats_rom : forall i, (i < 21)%nat ->
  rom_is segsB (0x21140 + 4 * Z.of_nat i) (le_z 4 (nth i float_bits 0)) = true.
Proof.
  intros i Hi. pose proof rate_asanubsan_arrays_chk as H. repeat rewrite andb_true_iff in H.
  destruct H as ((((_ & H) & _) & _) & _). exact (seq_ok _ 21 H i Hi).
Qed.

Lemma rate_asanubsan_t6_rom : forall i, (i < 4)%nat ->
  rom_is segsB (0x211c0 + 4 * Z.of_nat i) (le_z 4 (nth i t6 0)) = true.
Proof.
  intros i Hi. pose proof rate_asanubsan_arrays_chk as H. repeat rewrite andb_true_iff in H.
  destruct H as ((((_ & _) & H) & _) & _). exact (seq_ok _ 4 H i Hi).
Qed.

Lemma rate_asanubsan_t8_rom : forall i, (i < 4)%nat ->
  rom_is segsB (0x211e0 + 4 * Z.of_nat i) (le_z 4 (nth i t8 0)) = true.
Proof.
  intros i Hi. pose proof rate_asanubsan_arrays_chk as H. repeat rewrite andb_true_iff in H.
  destruct H as ((((_ & _) & _) & H) & _). exact (seq_ok _ 4 H i Hi).
Qed.

Lemma rate_asanubsan_jt_rom : forall k, (k < 9)%nat ->
  rom_is segsB (0x20f6c + 4 * Z.of_nat k) (le_z 4 (nth k rate_asanubsan_jt_tgts 0 - 0x20f6c)) = true.
Proof.
  intros k Hk. pose proof rate_asanubsan_arrays_chk as H. repeat rewrite andb_true_iff in H.
  destruct H as ((((_ & _) & _) & _) & H). exact (seq_ok _ 9 H k Hk).
Qed.

(** closed_list and ordered: rate i at the table + 4 i. *)
Lemma rate_asanubsan_rates_chk :
  forallb (fun i => rom_is segsB (RATE_ASANUBSAN_CLOSED + 4 * Z.of_nat i) (le_z 4 (nth i closed_list 0))) (seq 0 3) &&
  forallb (fun i => rom_is segsB (RATE_ASANUBSAN_ORDERED + 4 * Z.of_nat i) (le_z 4 (nth i closed_list 0))) (seq 0 3)
  = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rate_asanubsan_closed_rom : forall i, (i < 3)%nat ->
  rom_is segsB (RATE_ASANUBSAN_CLOSED + 4 * Z.of_nat i) (le_z 4 (nth i closed_list 0)) = true.
Proof.
  intros i Hi. pose proof rate_asanubsan_rates_chk as H. apply andb_prop in H as [H _]. exact (seq_ok _ 3 H i Hi).
Qed.

Lemma rate_asanubsan_ordered_rom : forall i, (i < 3)%nat ->
  rom_is segsB (RATE_ASANUBSAN_ORDERED + 4 * Z.of_nat i) (le_z 4 (nth i closed_list 0)) = true.
Proof.
  intros i Hi. pose proof rate_asanubsan_rates_chk as H. apply andb_prop in H as [_ H]. exact (seq_ok _ 3 H i Hi).
Qed.

(** Kind 9's s, ".", "" and "reac.headamp.", each with its NUL. *)
Lemma rate_asanubsan_texts_rom :
  rom_is segsB 0x21200 (zl S9 ++ [0]) = true /\ rom_is segsB 0x21500 (zl DOT ++ [0]) = true /\
  rom_is segsB 0x212e0 [0] = true /\ rom_is segsB 0x20fe0 (zl HPFX ++ [0]) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** The key at both addresses, with its NUL. *)
Lemma rate_asanubsan_key_rom :
  rom_is segsB RATE_ASANUBSAN_KEY_MAIN (zl RATE_KEY ++ [0]) = true /\
  rom_is segsB RATE_ASANUBSAN_KEY_PARSE (zl RATE_KEY ++ [0]) = true.
Proof. vm_compute. split; reflexivity. Qed.

(** The four multipliers, 8 bytes each. *)
Lemma rate_asanubsan_k33_rom : rom_is segsB 0x10418 (le_z 8 rate_asanubsan_k33) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rate_asanubsan_k24_rom : rom_is segsB 0x10330 (le_z 8 rate_asanubsan_k24) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rate_asanubsan_k14_rom : rom_is segsB 0x10318 (le_z 8 rate_asanubsan_k14) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rate_asanubsan_k21_rom : rom_is segsB 0x10310 (le_z 8 rate_asanubsan_k21) = true.
Proof. vm_compute. reflexivity. Qed.

(** [0x10000, 0x2fa0c) lies in a loaded segment of image B that is not writable (YG0d.in_rom's form): the ELF
    header, .rodata (the jump table, the constant pool, ints, floats, both t, s, closed_list, ordered and every string
    above) and the rest of the read-only PT_LOAD. *)
Lemma rate_asanubsan_ro_chk :
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? 0x10000) &&
                    (0x2fa0c <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segsB = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rate_asanubsan_ro : forall a, 0x10000 <= a < 0x2fa0c ->
  exists s, In s segsB /\ seg_writable s = false /\
            Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  intros a Ha. pose proof rate_asanubsan_ro_chk as H. apply existsb_exists in H as (s & Hs & E).
  repeat rewrite andb_true_iff in E. destruct E as ((E1 & E2) & E3).
  apply negb_true_iff in E1. apply Z.leb_le in E2. apply Z.leb_le in E3.
  exists s. split; [exact Hs|]. split; [exact E1|]. lia.
Qed.

(** ** The divisions by constants *)
(** The high word of x times M is x / d when M d - 2^64 is in [0, 2^64 / x). *)
Lemma rate_magic_div : forall d M x, 0 < d -> 0 <= x -> 2^64 <= M * d -> x * (M * d - 2^64) < 2^64 ->
  Z.shiftr (x * M) 64 = x / d.
Proof.
  intros d M x Hd Hx HM He. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod x d ltac:(lia)) as Hq. pose proof (Z.mod_pos_bound x d Hd) as Hr.
  set (q := x / d) in *. set (r0 := x mod d) in *. clearbody q r0.
  set (B := 2^64) in *. assert (HB : 0 < B) by (unfold B; lia). clearbody B.
  assert (E : (x * M - B * q) * d = x * (M * d - B) + B * r0).
  { transitivity (x * (M * d) - B * (d * q)); [ring|]. replace (d * q) with (x - r0) by lia. ring. }
  assert (L0 : 0 <= x * (M * d - B)) by (apply Z.mul_nonneg_nonneg; lia).
  assert (L1 : 0 <= B * r0) by (apply Z.mul_nonneg_nonneg; lia).
  assert (L2 : B * r0 <= B * (d - 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (Lo' : 0 <= (x * M - B * q) * d) by lia.
  assert (Hi' : (x * M - B * q) * d < B * d) by lia.
  set (r := x * M - B * q) in *.
  assert (Lo : 0 <= r).
  { destruct (Z.lt_ge_cases r 0) as [Hn|Hn]; [|lia].
    assert (r * d < 0) by (apply Z.mul_neg_pos; lia). lia. }
  assert (Hi : r < B).
  { destruct (Z.lt_ge_cases r B) as [Hn|Hn]; [lia|].
    assert (B * d <= r * d) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
  symmetry. apply (Z.div_unique (x * M) B q r); [left; lia | unfold r; ring].
Qed.

Local Lemma ulit : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact H. Qed.

Lemma rate_asanubsan_k33_mulhu : forall x, 0 <= x < 2^32 ->
  YK11.v_mulhu (Z_to_bv 64 x) (Z_to_bv 64 rate_asanubsan_k33) = Z_to_bv 64 (x / 33).
Proof.
  intros x Hx. unfold YK11.v_mulhu. rewrite (ulit x) by lia.
  rewrite (ulit rate_asanubsan_k33) by (unfold rate_asanubsan_k33; lia).
  rewrite (rate_magic_div 33 rate_asanubsan_k33 x); [reflexivity | lia | lia | unfold rate_asanubsan_k33; lia |].
  replace (rate_asanubsan_k33 * 33 - 2^64) with 17 by (unfold rate_asanubsan_k33; reflexivity). lia.
Qed.

Lemma rate_asanubsan_k24_mulhu : forall x, 0 <= x < 2^32 ->
  YK11.v_mulhu (Z_to_bv 64 x) (Z_to_bv 64 rate_asanubsan_k24) = Z_to_bv 64 (x / 24).
Proof.
  intros x Hx. unfold YK11.v_mulhu. rewrite (ulit x) by lia.
  rewrite (ulit rate_asanubsan_k24) by (unfold rate_asanubsan_k24; lia).
  rewrite (rate_magic_div 24 rate_asanubsan_k24 x); [reflexivity | lia | lia | unfold rate_asanubsan_k24; lia |].
  replace (rate_asanubsan_k24 * 24 - 2^64) with 8 by (unfold rate_asanubsan_k24; reflexivity). lia.
Qed.

Lemma rate_asanubsan_k14_mulhu : forall x, 0 <= x < 2^32 ->
  YK11.v_mulhu (Z_to_bv 64 x) (Z_to_bv 64 rate_asanubsan_k14) = Z_to_bv 64 (x / 14).
Proof.
  intros x Hx. unfold YK11.v_mulhu. rewrite (ulit x) by lia.
  rewrite (ulit rate_asanubsan_k14) by (unfold rate_asanubsan_k14; lia).
  rewrite (rate_magic_div 14 rate_asanubsan_k14 x); [reflexivity | lia | lia | unfold rate_asanubsan_k14; lia |].
  replace (rate_asanubsan_k14 * 14 - 2^64) with 12 by (unfold rate_asanubsan_k14; reflexivity). lia.
Qed.

Lemma rate_asanubsan_k21_mulhu : forall x, 0 <= x < 2^32 ->
  YK11.v_mulhu (Z_to_bv 64 x) (Z_to_bv 64 rate_asanubsan_k21) = Z_to_bv 64 (x / 21).
Proof.
  intros x Hx. unfold YK11.v_mulhu. rewrite (ulit x) by lia.
  rewrite (ulit rate_asanubsan_k21) by (unfold rate_asanubsan_k21; lia).
  rewrite (rate_magic_div 21 rate_asanubsan_k21 x); [reflexivity | lia | lia | unfold rate_asanubsan_k21; lia |].
  replace (rate_asanubsan_k21 * 21 - 2^64) with 5 by (unfold rate_asanubsan_k21; reflexivity). lia.
Qed.

Local Lemma all256 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall c, 0 <= c < 256 -> P c = true.
Proof.
  intros P H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat c).
  split; [lia | apply in_seq; lia].
Qed.

(** buflen = c % 24 (0x80a9c .. 0x80ab0): q = mulhu(c, K24); c + ((q << 3) - (q << 5)). *)
Lemma rate_asanubsan_k24_mod : forall c, 0 <= c < 256 ->
  YK11.v_add (Z_to_bv 64 c)
    (YK11.v_sub (YK11.v_slli (YK11.v_mulhu (Z_to_bv 64 c) (Z_to_bv 64 rate_asanubsan_k24)) 3)
                (YK11.v_slli (YK11.v_mulhu (Z_to_bv 64 c) (Z_to_bv 64 rate_asanubsan_k24)) 5)) =
  Z_to_bv 64 (c mod 24).
Proof.
  intros c Hc. apply bv_eq. apply Z.eqb_eq.
  exact (all256 (fun c => bv_unsigned (YK11.v_add (Z_to_bv 64 c)
    (YK11.v_sub (YK11.v_slli (YK11.v_mulhu (Z_to_bv 64 c) (Z_to_bv 64 rate_asanubsan_k24)) 3)
                (YK11.v_slli (YK11.v_mulhu (Z_to_bv 64 c) (Z_to_bv 64 rate_asanubsan_k24)) 5))) =?
                         bv_unsigned (Z_to_bv 64 (c mod 24)))
    ltac:(vm_compute; reflexivity) c Hc).
Qed.

(** count = c % 33 (0x81378 .. 0x81384): q = mulhu(c, K33); c - ((q << 5) | q). *)
Lemma rate_asanubsan_k33_mod : forall c, 0 <= c < 256 ->
  YK11.v_sub (Z_to_bv 64 c)
    (YK11.v_or (YK11.v_slli (YK11.v_mulhu (Z_to_bv 64 c) (Z_to_bv 64 rate_asanubsan_k33)) 5)
               (YK11.v_mulhu (Z_to_bv 64 c) (Z_to_bv 64 rate_asanubsan_k33))) = Z_to_bv 64 (c mod 33).
Proof.
  intros c Hc. apply bv_eq. apply Z.eqb_eq.
  exact (all256 (fun c => bv_unsigned (YK11.v_sub (Z_to_bv 64 c)
    (YK11.v_or (YK11.v_slli (YK11.v_mulhu (Z_to_bv 64 c) (Z_to_bv 64 rate_asanubsan_k33)) 5)
               (YK11.v_mulhu (Z_to_bv 64 c) (Z_to_bv 64 rate_asanubsan_k33)))) =?
                         bv_unsigned (Z_to_bv 64 (c mod 33)))
    ltac:(vm_compute; reflexivity) c Hc).
Qed.

(** x % 14 (0x81804 .. 0x8181c and 0x81de8 .. 0x81e00): q = mulhu(x, K14); x + ((q << 1) - (q << 4)). *)
Lemma rate_asanubsan_k14_mod : forall x, 0 <= x < 256 ->
  YK11.v_add (Z_to_bv 64 x)
    (YK11.v_sub (YK11.v_slli (YK11.v_mulhu (Z_to_bv 64 x) (Z_to_bv 64 rate_asanubsan_k14)) 1)
                (YK11.v_slli (YK11.v_mulhu (Z_to_bv 64 x) (Z_to_bv 64 rate_asanubsan_k14)) 4)) =
  Z_to_bv 64 (x mod 14).
Proof.
  intros x Hx. apply bv_eq. apply Z.eqb_eq.
  exact (all256 (fun x => bv_unsigned (YK11.v_add (Z_to_bv 64 x)
    (YK11.v_sub (YK11.v_slli (YK11.v_mulhu (Z_to_bv 64 x) (Z_to_bv 64 rate_asanubsan_k14)) 1)
                (YK11.v_slli (YK11.v_mulhu (Z_to_bv 64 x) (Z_to_bv 64 rate_asanubsan_k14)) 4))) =?
                         bv_unsigned (Z_to_bv 64 (x mod 14)))
    ltac:(vm_compute; reflexivity) x Hx).
Qed.

(** x % 21 (0x81f7c .. 0x81f88): x - mulhu(x, K21) * 21. *)
Lemma rate_asanubsan_k21_mod : forall x, 0 <= x < 256 ->
  YK11.v_sub (Z_to_bv 64 x) (YK11.v_mul (YK11.v_mulhu (Z_to_bv 64 x) (Z_to_bv 64 rate_asanubsan_k21))
    (Z_to_bv 64 21)) = Z_to_bv 64 (x mod 21).
Proof.
  intros x Hx. apply bv_eq. apply Z.eqb_eq.
  exact (all256 (fun x => bv_unsigned (YK11.v_sub (Z_to_bv 64 x)
    (YK11.v_mul (YK11.v_mulhu (Z_to_bv 64 x) (Z_to_bv 64 rate_asanubsan_k21)) (Z_to_bv 64 21))) =?
                         bv_unsigned (Z_to_bv 64 (x mod 21)))
    ltac:(vm_compute; reflexivity) x Hx).
Qed.
