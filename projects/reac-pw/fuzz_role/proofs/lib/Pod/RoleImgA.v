(** fuzz_role's image A (fuzz_role.asan, pinned sha256 614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb)
    holds pod.h's tables where [role_asan_addrs] says (the record type is Pod/Tables.v's pod_addrs and the check is
    Pod/RoleImg.v's addrs_ok, as for the plain and the UBSan image), ent_build's jump table where [role_asan_jt_tgts]
    says, and the three multipliers that LLVMFuzzerTestOneInput loads from the constant pool where [role_asan_kcells]
    says. Each address was measured on the unstripped twin of the pinned image (sha256
    6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6; its loaded bytes are the pinned image's except the
    ELF header's section-table fields and the build-id note) and each byte is checked below against the pinned image's
    loaded segments by computation. Statement data and computation only: proves no function.

    Image A keeps each table and each string as a registered global of its own, so no string shares bytes with
    another (the plain image keeps kind 9's String in vocab[0]'s bytes): vocab, odd_ch and param are arrays of 8-byte
    pointers in .data.rel.ro (0x9a500, 0x9a580, 0x9a620; param is an array of pointers here, not of offsets); ints,
    floats, case 6's t (ent_build.t), case 8's t (ent_build.t.9) and kind 9's s are in .rodata; ent_headamp_key's
    texts "reac.headamp.", "." and "" are .str.2 0x20f00 (also vocab[2]), .str.31 0x21420 and .str.15 0x21200 (also
    odd_ch[5] and param[5]).

    The jump table: `jr a1` 0x80b3c takes kinds 0 .. 8 (kind 9 leaves by `bltu` 0x80b18) to 0x20e94 plus the
    sign-extended 4-byte entry of the kind in the table at .rodata 0x20e94 (`auipc` / `addi` 0x80b20 .. 0x80b24, `lw`
    0x80b2c). The constant pool: `ld` 0x80a4c reads 0x10400 for count = fuzz_u8 % 33 (pod.h:424); `ld` 0x81200 and
    `ld` 0x813ac read 0x10318 for ints[(m >> 1) % 14] (pod.h:300) and odd_ch[c % 14] (pod.h:247); `ld` 0x81568 reads
    0x10310 for floats[(m >> 1) % 21] (pod.h:319). Each value is ceil(2^64 / d), so the high word of its product with
    x is x / d; the lemmas at the end give the quotient and the remainder each instruction sequence computes.

    The facts come in two forms: Pod/RoleImg.v's (memory_read of a whole run: addrs_ok, jt_ok, rd_is) and byte by
    byte through YK11.seg_rom (img_z, rom_is), the form in which rom_view (Reusable/YG0d.v) and arodata_okP
    (A/RPgBase.v) give a reader's byte of read-only data. Every address of .rodata here lies in image A's read-only
    PT_LOAD [0x10000, 0x2f634) ([role_asan_ro]); the three pointer tables lie in .data.rel.ro, in the writable PT_LOAD
    that starts at 0x9a0e8. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK11.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Tables RoleImg.
Require OSSVerify.reac_pw.fuzz_role.images.Asan OSSVerify.reac_pw.fuzz_role.images.Plain
  OSSVerify.reac_pw.fuzz_role.images.Ubsan.
Import ListNotations.
Open Scope Z_scope.

Local Abbreviation segsA := OSSVerify.reac_pw.fuzz_role.images.Asan.M.loaded_segments (only parsing).

(** ** The tables (Pod/Tables.v's record) *)
Definition role_asan_addrs : pod_addrs := {|
  pa_jt := 0x20e94; pa_vocab := 0x9a500;
  pa_vocab_s := [0x20ec0; 0x20ee0; 0x20f00; 0x20f20; 0x20f40; 0x20f60; 0x20fa0; 0x20fc0; 0x20fe0];
  pa_ints := 0x21000; pa_floats := 0x21060;
  pa_odd := 0x9a580;
  pa_odd_s := [0x21140; 0x21160; 0x21180; 0x211a0; 0x211c0; 0x21200; 0x21220; 0x21240; 0x21260; 0x21280; 0x212a0;
               0x212c0; 0x212e0; 0x21300];
  pa_param := 0x9a620; pa_param_rel := false;
  pa_param_s := [0x21340; 0x21360; 0x21380; 0x213a0; 0x213c0; 0x21200; 0x213e0; 0x21400];
  pa_t6 := 0x210e0; pa_t8 := 0x21100; pa_s9 := 0x21120; pa_dot := 0x21420; pa_empty := 0x21200; pa_hpfx := 0x20f00 |}.

Lemma role_asan_tables : addrs_ok segsA role_asan_addrs = true.
Proof. vm_compute. reflexivity. Qed.

(** A control: the other builds' addresses do not pass on image A, nor image A's on the other builds. *)
Lemma role_asan_tables_control :
  addrs_ok segsA role_plain_addrs = false /\ addrs_ok segsA role_ubsan_addrs = false /\
  addrs_ok OSSVerify.reac_pw.fuzz_role.images.Plain.M.loaded_segments role_asan_addrs = false /\
  addrs_ok OSSVerify.reac_pw.fuzz_role.images.Ubsan.M.loaded_segments role_asan_addrs = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ** ent_build's jump table *)
(** The targets of kinds 0 .. 8. *)
Definition role_asan_jt_tgts : list Z :=
  [0x80b40; 0x80fd8; 0x80eb4; 0x80f1c; 0x80e68; 0x81020; 0x810a8; 0x80f64; 0x810f8].

(** At t + 4 k the table at jt holds the offset of target k from jt, as 4 little-endian bytes; each offset is in
    [0, 2^31), so the sign extension of `lw` keeps it. *)
Fixpoint jt_ok (segs : list Segment) (jt t : Z) (tgts : list Z) : bool :=
  match tgts with
  | [] => true
  | g :: gs => (0 <=? g - jt) && (g - jt <? 2^31) && rd_is segs t (le_z 4 (g - jt)) && jt_ok segs jt (t + 4) gs
  end.

Lemma role_asan_jt : jt_ok segsA (pa_jt role_asan_addrs) (pa_jt role_asan_addrs) role_asan_jt_tgts = true.
Proof. vm_compute. reflexivity. Qed.

(** Each target is an instruction of LLVMFuzzerTestOneInput [0x7ff88, 0x82ab4), at an offset in [0, 2^31). *)
Lemma role_asan_jt_tgts_range : forall k, (k < 9)%nat ->
  0 <= nth k role_asan_jt_tgts 0 - 0x20e94 < 2^31 /\ 0x7ff88 <= nth k role_asan_jt_tgts 0 < 0x82ab4.
Proof.
  intros k Hk. do 9 (destruct k as [|k]; [cbn; lia|]). lia.
Qed.

(** ** The constant pool *)
Definition role_k33 : Z := 0x07c1f07c1f07c1f1.
Definition role_k14 : Z := 0x124924924924924a.
Definition role_k21 : Z := 0x0c30c30c30c30c31.
(** (address, 8-byte value). *)
Definition role_asan_kcells : list (Z * Z) := [(0x10400, role_k33); (0x10318, role_k14); (0x10310, role_k21)].

Lemma role_asan_kcells_rd : forallb (fun c => rd_is segsA (fst c) (le_z 8 (snd c))) role_asan_kcells = true.
Proof. vm_compute. reflexivity. Qed.

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
Lemma role_asan_vocab_chk : forallb (fun k =>
  rom_is segsA (0x9a500 + 8 * Z.of_nat k) (le_z 8 (nth k (pa_vocab_s role_asan_addrs) 0)) &&
  rom_is segsA (nth k (pa_vocab_s role_asan_addrs) 0) (zl (nth k vocab []) ++ [0])) (seq 0 9) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma role_asan_odd_chk : forallb (fun k =>
  rom_is segsA (0x9a580 + 8 * Z.of_nat k) (le_z 8 (nth k (pa_odd_s role_asan_addrs) 0)) &&
  rom_is segsA (nth k (pa_odd_s role_asan_addrs) 0) (zl (nth k odd_ch []) ++ [0])) (seq 0 14) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma role_asan_param_chk : forallb (fun k =>
  rom_is segsA (0x9a620 + 8 * Z.of_nat k) (le_z 8 (nth k (pa_param_s role_asan_addrs) 0)) &&
  rom_is segsA (nth k (pa_param_s role_asan_addrs) 0) (zl (nth k param []) ++ [0])) (seq 0 8) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma role_asan_vocab_rom : forall k, (k < 9)%nat ->
  rom_is segsA (0x9a500 + 8 * Z.of_nat k) (le_z 8 (nth k (pa_vocab_s role_asan_addrs) 0)) = true /\
  rom_is segsA (nth k (pa_vocab_s role_asan_addrs) 0) (zl (nth k vocab []) ++ [0]) = true.
Proof. intros k Hk. apply andb_prop. exact (seq_ok _ 9 role_asan_vocab_chk k Hk). Qed.

Lemma role_asan_odd_rom : forall k, (k < 14)%nat ->
  rom_is segsA (0x9a580 + 8 * Z.of_nat k) (le_z 8 (nth k (pa_odd_s role_asan_addrs) 0)) = true /\
  rom_is segsA (nth k (pa_odd_s role_asan_addrs) 0) (zl (nth k odd_ch []) ++ [0]) = true.
Proof. intros k Hk. apply andb_prop. exact (seq_ok _ 14 role_asan_odd_chk k Hk). Qed.

Lemma role_asan_param_rom : forall k, (k < 8)%nat ->
  rom_is segsA (0x9a620 + 8 * Z.of_nat k) (le_z 8 (nth k (pa_param_s role_asan_addrs) 0)) = true /\
  rom_is segsA (nth k (pa_param_s role_asan_addrs) 0) (zl (nth k param []) ++ [0]) = true.
Proof. intros k Hk. apply andb_prop. exact (seq_ok _ 8 role_asan_param_chk k Hk). Qed.

(** The arrays of 4-byte values: element i at the table + 4 i. *)
Lemma role_asan_arrays_chk :
  forallb (fun i => rom_is segsA (0x21000 + 4 * Z.of_nat i) (le_z 4 (nth i ints 0))) (seq 0 14) &&
  forallb (fun i => rom_is segsA (0x21060 + 4 * Z.of_nat i) (le_z 4 (nth i float_bits 0))) (seq 0 21) &&
  forallb (fun i => rom_is segsA (0x210e0 + 4 * Z.of_nat i) (le_z 4 (nth i t6 0))) (seq 0 4) &&
  forallb (fun i => rom_is segsA (0x21100 + 4 * Z.of_nat i) (le_z 4 (nth i t8 0))) (seq 0 4) &&
  forallb (fun k => rom_is segsA (0x20e94 + 4 * Z.of_nat k) (le_z 4 (nth k role_asan_jt_tgts 0 - 0x20e94)))
    (seq 0 9) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma role_asan_ints_rom : forall i, (i < 14)%nat ->
  rom_is segsA (0x21000 + 4 * Z.of_nat i) (le_z 4 (nth i ints 0)) = true.
Proof.
  intros i Hi. pose proof role_asan_arrays_chk as H. repeat rewrite andb_true_iff in H.
  destruct H as ((((H & _) & _) & _) & _). exact (seq_ok _ 14 H i Hi).
Qed.

Lemma role_asan_floats_rom : forall i, (i < 21)%nat ->
  rom_is segsA (0x21060 + 4 * Z.of_nat i) (le_z 4 (nth i float_bits 0)) = true.
Proof.
  intros i Hi. pose proof role_asan_arrays_chk as H. repeat rewrite andb_true_iff in H.
  destruct H as ((((_ & H) & _) & _) & _). exact (seq_ok _ 21 H i Hi).
Qed.

Lemma role_asan_t6_rom : forall i, (i < 4)%nat ->
  rom_is segsA (0x210e0 + 4 * Z.of_nat i) (le_z 4 (nth i t6 0)) = true.
Proof.
  intros i Hi. pose proof role_asan_arrays_chk as H. repeat rewrite andb_true_iff in H.
  destruct H as ((((_ & _) & H) & _) & _). exact (seq_ok _ 4 H i Hi).
Qed.

Lemma role_asan_t8_rom : forall i, (i < 4)%nat ->
  rom_is segsA (0x21100 + 4 * Z.of_nat i) (le_z 4 (nth i t8 0)) = true.
Proof.
  intros i Hi. pose proof role_asan_arrays_chk as H. repeat rewrite andb_true_iff in H.
  destruct H as ((((_ & _) & _) & H) & _). exact (seq_ok _ 4 H i Hi).
Qed.

Lemma role_asan_jt_rom : forall k, (k < 9)%nat ->
  rom_is segsA (0x20e94 + 4 * Z.of_nat k) (le_z 4 (nth k role_asan_jt_tgts 0 - 0x20e94)) = true.
Proof.
  intros k Hk. pose proof role_asan_arrays_chk as H. repeat rewrite andb_true_iff in H.
  destruct H as ((((_ & _) & _) & _) & H). exact (seq_ok _ 9 H k Hk).
Qed.

(** Kind 9's s, ".", "" and "reac.headamp.", each with its NUL. *)
Lemma role_asan_texts_rom :
  rom_is segsA 0x21120 (zl S9 ++ [0]) = true /\ rom_is segsA 0x21420 (zl DOT ++ [0]) = true /\
  rom_is segsA 0x21200 [0] = true /\ rom_is segsA 0x20f00 (zl HPFX ++ [0]) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** The three multipliers, 8 bytes each. *)
Lemma role_asan_k33_rom : rom_is segsA 0x10400 (le_z 8 role_k33) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma role_asan_k14_rom : rom_is segsA 0x10318 (le_z 8 role_k14) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma role_asan_k21_rom : rom_is segsA 0x10310 (le_z 8 role_k21) = true.
Proof. vm_compute. reflexivity. Qed.

(** [0x10000, 0x2f634) lies in a loaded segment of image A that is not writable (the first case of YG0d.in_rom and
    of RPgBase.in_roP): the ELF header, .rodata (the jump table, the constant pool, ints, floats, both t, s and every
    string above) and the rest of the read-only PT_LOAD. *)
Lemma role_asan_ro_chk :
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? 0x10000) &&
                    (0x2f634 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segsA = true.
Proof. vm_compute. reflexivity. Qed.

Lemma role_asan_ro : forall a, 0x10000 <= a < 0x2f634 ->
  exists s, In s segsA /\ seg_writable s = false /\
            Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  intros a Ha. pose proof role_asan_ro_chk as H. apply existsb_exists in H as (s & Hs & E).
  repeat rewrite andb_true_iff in E. destruct E as ((E1 & E2) & E3).
  apply negb_true_iff in E1. apply Z.leb_le in E2. apply Z.leb_le in E3.
  exists s. split; [exact Hs|]. split; [exact E1|]. lia.
Qed.

(** ** The divisions by constants *)
(** The high word of x times M is x / d when M d - 2^64 is in [0, 2^64 / x). *)
Lemma role_magic_div : forall d M x, 0 < d -> 0 <= x -> 2^64 <= M * d -> x * (M * d - 2^64) < 2^64 ->
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

Lemma role_k33_mulhu : forall x, 0 <= x < 2^32 ->
  YK11.v_mulhu (Z_to_bv 64 x) (Z_to_bv 64 role_k33) = Z_to_bv 64 (x / 33).
Proof.
  intros x Hx. unfold YK11.v_mulhu. rewrite (ulit x) by lia. rewrite (ulit role_k33) by (unfold role_k33; lia).
  rewrite (role_magic_div 33 role_k33 x); [reflexivity | lia | lia | unfold role_k33; lia |].
  replace (role_k33 * 33 - 2^64) with 17 by (unfold role_k33; reflexivity). lia.
Qed.

Lemma role_k14_mulhu : forall x, 0 <= x < 2^32 ->
  YK11.v_mulhu (Z_to_bv 64 x) (Z_to_bv 64 role_k14) = Z_to_bv 64 (x / 14).
Proof.
  intros x Hx. unfold YK11.v_mulhu. rewrite (ulit x) by lia. rewrite (ulit role_k14) by (unfold role_k14; lia).
  rewrite (role_magic_div 14 role_k14 x); [reflexivity | lia | lia | unfold role_k14; lia |].
  replace (role_k14 * 14 - 2^64) with 12 by (unfold role_k14; reflexivity). lia.
Qed.

Lemma role_k21_mulhu : forall x, 0 <= x < 2^32 ->
  YK11.v_mulhu (Z_to_bv 64 x) (Z_to_bv 64 role_k21) = Z_to_bv 64 (x / 21).
Proof.
  intros x Hx. unfold YK11.v_mulhu. rewrite (ulit x) by lia. rewrite (ulit role_k21) by (unfold role_k21; lia).
  rewrite (role_magic_div 21 role_k21 x); [reflexivity | lia | lia | unfold role_k21; lia |].
  replace (role_k21 * 21 - 2^64) with 5 by (unfold role_k21; reflexivity). lia.
Qed.

Local Lemma all256 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall c, 0 <= c < 256 -> P c = true.
Proof.
  intros P H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat c).
  split; [lia | apply in_seq; lia].
Qed.

(** count = c % 33 (0x80a5c .. 0x80a68): q = mulhu(c, K33); c - ((q << 5) | q). *)
Lemma role_k33_mod : forall c, 0 <= c < 256 ->
  YK11.v_sub (Z_to_bv 64 c)
    (YK11.v_or (YK11.v_slli (YK11.v_mulhu (Z_to_bv 64 c) (Z_to_bv 64 role_k33)) 5)
               (YK11.v_mulhu (Z_to_bv 64 c) (Z_to_bv 64 role_k33))) = Z_to_bv 64 (c mod 33).
Proof.
  intros c Hc. apply bv_eq. apply Z.eqb_eq.
  exact (all256 (fun c => bv_unsigned (YK11.v_sub (Z_to_bv 64 c)
    (YK11.v_or (YK11.v_slli (YK11.v_mulhu (Z_to_bv 64 c) (Z_to_bv 64 role_k33)) 5)
               (YK11.v_mulhu (Z_to_bv 64 c) (Z_to_bv 64 role_k33)))) =? bv_unsigned (Z_to_bv 64 (c mod 33)))
    ltac:(vm_compute; reflexivity) c Hc).
Qed.

(** x % 14 (0x81208 .. 0x8121c and 0x813b0 .. 0x813c4): q = mulhu(x, K14); x + ((q << 1) - (q << 4)). *)
Lemma role_k14_mod : forall x, 0 <= x < 256 ->
  YK11.v_add (Z_to_bv 64 x)
    (YK11.v_sub (YK11.v_slli (YK11.v_mulhu (Z_to_bv 64 x) (Z_to_bv 64 role_k14)) 1)
                (YK11.v_slli (YK11.v_mulhu (Z_to_bv 64 x) (Z_to_bv 64 role_k14)) 4)) = Z_to_bv 64 (x mod 14).
Proof.
  intros x Hx. apply bv_eq. apply Z.eqb_eq.
  exact (all256 (fun x => bv_unsigned (YK11.v_add (Z_to_bv 64 x)
    (YK11.v_sub (YK11.v_slli (YK11.v_mulhu (Z_to_bv 64 x) (Z_to_bv 64 role_k14)) 1)
                (YK11.v_slli (YK11.v_mulhu (Z_to_bv 64 x) (Z_to_bv 64 role_k14)) 4))) =?
                         bv_unsigned (Z_to_bv 64 (x mod 14)))
    ltac:(vm_compute; reflexivity) x Hx).
Qed.

(** x % 21 (0x8156c .. 0x81578): x - mulhu(x, K21) * 21. *)
Lemma role_k21_mod : forall x, 0 <= x < 256 ->
  YK11.v_sub (Z_to_bv 64 x) (YK11.v_mul (YK11.v_mulhu (Z_to_bv 64 x) (Z_to_bv 64 role_k21)) (Z_to_bv 64 21)) =
  Z_to_bv 64 (x mod 21).
Proof.
  intros x Hx. apply bv_eq. apply Z.eqb_eq.
  exact (all256 (fun x => bv_unsigned (YK11.v_sub (Z_to_bv 64 x)
    (YK11.v_mul (YK11.v_mulhu (Z_to_bv 64 x) (Z_to_bv 64 role_k21)) (Z_to_bv 64 21))) =?
                         bv_unsigned (Z_to_bv 64 (x mod 21)))
    ltac:(vm_compute; reflexivity) x Hx).
Qed.
