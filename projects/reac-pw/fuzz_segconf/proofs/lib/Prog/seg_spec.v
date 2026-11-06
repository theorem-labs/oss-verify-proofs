(** reac-pw/fuzz_segconf: the memory encodings of the spine's states (Spec/SegModel.v, theorem segconf_agrees) that
    the contracts of segconf's own functions read and write, plain (lib/Prog/*_c.v) and UBSan (lib/U/Prog/*_c.v).
    One file for both builds, as pin_spec.v is for reac-pw/fuzz_pin: the encodings are pure predicates over byte
    lists (the layouts are the same in both builds: the two images' DWARF layouts are
    identical), the [_at] forms take the build's segment list, and the addresses that differ between the builds are
    the per-build record [seg_addrs]. Statement text only: no function of the binary is proved here.

    Sources:
    - struct reac_segconf (reac_segconf.h:121-144), 16616 bytes, 8-aligned: seg[32] of 356 bytes at 0, n 0x2c80,
      present 0x2c84, path[512] 0x2c88, refusal[8][200] 0x2e88, n_refusals 0x34c8, refused 0x34cc, overflow 0x34d0,
      file[17][96] 0x34d4, n_files 0x3b34, files_overflow 0x3b38, stamp[17] 0x3b40, stamp_dir 0x3d60, home[256]
      0x3d80, base[512] 0x3e80, reading[96] 0x4080, gen 0x40e0.
    - struct reac_segconf_seg (reac_segconf.h:85-109), 356 bytes, 4-aligned: name[16] 0, role 0x10, role_set 0x14,
      ignore 0x18, ignore_set 0x1c, said_ignored 0x20, model[24] 0x24, model_set 0x3c, model_file[96] 0x40,
      role_file[96] 0xa0, ignore_file[96] 0x100, seen_gen 0x160.
    - struct mconf (fuzz_segconf.c:90-99), 9236 bytes: seg[32] of 256 bytes at 0, n 0x2000, overflow 0x2004, refused
      0x2008, kept[8][112] 0x200c, kept_knock[8] 0x238c, n_kept 0x23ac, gen 0x23b0, reading[96] 0x23b4.
    - struct mseg (fuzz_segconf.c:81-88), 256 bytes: name[16] 0, role 0x10, role_set 0x14, ignore 0x18, ignore_set
      0x1c, model_set 0x20, model[24] 0x24, role_file[96] 0x3c, ignore_file[96] 0x9c, gen 0xfc.
    - struct reac_declared_vlan (reac_declared_vlan.h), 18 bytes: parent[16] 0, uint16_t vid 0x10; struct mvlan
      (fuzz_segconf.c:314-317), 20 bytes: parent[16] 0, unsigned vid 0x10.

    What an encoding fixes. A char[cap] field holds its C string, the NUL, then bytes NOT fixed: they are what an
    earlier write left (cross_check's `model[0] = 0` keeps the old model bytes after the NUL; snprintf and memcpy
    write only the string and its NUL). An int field is its 4 little-endian bytes. Fields no function in scope
    writes are not fixed and are PRESERVED: each contract's munch lists exactly the byte ranges its function may
    write, so every other byte is unchanged (reac_segconf: said_ignored, present, path, file, n_files,
    files_overflow, stamp, stamp_dir, home, base; the entries seg[i] for i >= n and refusal[i] for i >= n_refusals,
    which no function reads before it writes them). One field is fixed beyond the model's list: kept_knock[i] = 0 for
    n_kept <= i < 8, because m_refuse appends (address, false) without writing kept_knock[n_kept] (fuzz_segconf.c:
    101-111 relies on calloc's zeros, and only the knock branch of m_key writes it, at n_kept, just before the
    m_refuse that keeps it).

    Bytes are the spine's [Z] values through [zs] (bv_unsigned). The box-model table is pin_spec's: fuzz_catalogue
    at sa_catalogue (plain 0x20ad0, UBSan 0x21468; .data.rel.ro, inside FrameAPI.frame_RELRO), 11 rows of 0x128
    bytes, the token pointers and display pointers of pin_spec.rows, the same in both images (read from the pinned
    ELFs 3776ca44d75c / 1696d6c34ffd); the image facts
    (row i's token pointer word, token i's bytes and NUL in .rodata) are Prog/fuzz_catalogue_row.v's row_img and
    tok_at (U: U/Prog/fuzz_catalogue_row.v), proved by vm_compute on each image; [cat_toks_bytes] below ties the
    token bytes to SegModel.cat_toks. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec.
Import ListNotations.
Open Scope Z_scope.

(** ** Per-build addresses *)
Record seg_addrs := SegAddrs {
  sa_catalogue : Z;   (* fuzz_catalogue (catalogue.c:12-23), 11 rows of 0x128 bytes *)
  sa_longl : Z;       (* LLVMFuzzerTestOneInput's static char longl[121] (.bss; FrameAPI.frame_G) *)
  sa_got_guard : Z;   (* the GOT cell that holds &__stack_chk_guard *)
  sa_guard : Z;       (* __stack_chk_guard *)
  sa_ro_end : Z;      (* the end of the read-only first PT_LOAD [0x10000, sa_ro_end): .rodata *)
  sa_img_end : Z;     (* the byte end of the last PT_LOAD (.bss) *)
  sa_img_top : Z      (* that end rounded up to a page: the first address no reserved segment covers. For the
                         record only: a block premise is stated as [blk_noimg] (no byte in a reserved segment),
                         which the slot can prove, never as an address bound against this field. *)
}.
(** Read from the pinned ELFs' program headers (plain 3776ca44d75c, UBSan 1696d6c34ffd) and symbol tables. *)
Definition SEG_PLAIN : seg_addrs := SegAddrs 0x20ad0 0x32ac0 0x21818 0x52e80 0x121d8 0x536e8 0x54000.
Definition SEG_UBSAN : seg_addrs := SegAddrs 0x21468 0x33460 0x221b0 0x53820 0x1229c 0x54088 0x55000.
Definition RO_LO : Z := 0x10000.

(** .rodata strings the contracts name, at the same address in both images. *)
Definition STR_BASE : Z := 0x10463.      (* "reac-pw.conf" (REAC_SEGCONF_FILE, BASE_FILE) *)
Definition STR_TNP : Z := 0x10433.       (* "takes no plan" *)
Definition STR_NOSUCH : Z := 0x10540.    (* "nosuch0" *)

(** ** Sizes and offsets *)
Definition SEG_C_SIZE : Z := 16616.
Definition SEG_M_SIZE : Z := 9236.
Definition RSEG_SIZE : Z := 356.
Definition MSEG_SIZE : Z := 256.
Definition RC_N : Z := 0x2c80.
Definition RC_REFUSAL : Z := 0x2e88.
Definition RC_REFUSAL_LEN : Z := 200.
Definition RC_NREF : Z := 0x34c8.
Definition RC_REFUSED : Z := 0x34cc.
Definition RC_OVERFLOW : Z := 0x34d0.
Definition RC_READING : Z := 0x4080.
Definition RC_GEN : Z := 0x40e0.
Definition RS_ROLE : Z := 0x10.
Definition RS_ROLE_SET : Z := 0x14.
Definition RS_IGNORE : Z := 0x18.
Definition RS_IGNORE_SET : Z := 0x1c.
Definition RS_MODEL : Z := 0x24.
Definition RS_MODEL_SET : Z := 0x3c.
Definition RS_MODEL_FILE : Z := 0x40.
Definition RS_ROLE_FILE : Z := 0xa0.
Definition RS_IGNORE_FILE : Z := 0x100.
Definition RS_SEEN_GEN : Z := 0x160.
Definition MC_N : Z := 0x2000.
Definition MC_OVERFLOW : Z := 0x2004.
Definition MC_REFUSED : Z := 0x2008.
Definition MC_KEPT : Z := 0x200c.
Definition MC_KEPT_LEN : Z := 112.
Definition MC_KNOCK : Z := 0x238c.
Definition MC_NKEPT : Z := 0x23ac.
Definition MC_GEN : Z := 0x23b0.
Definition MC_READING : Z := 0x23b4.
Definition MS_ROLE : Z := 0x10.
Definition MS_ROLE_SET : Z := 0x14.
Definition MS_IGNORE : Z := 0x18.
Definition MS_IGNORE_SET : Z := 0x1c.
Definition MS_MODEL_SET : Z := 0x20.
Definition MS_MODEL : Z := 0x24.
Definition MS_ROLE_FILE : Z := 0x3c.
Definition MS_IGNORE_FILE : Z := 0x9c.
Definition MS_GEN : Z := 0xfc.
Definition RVLAN_SIZE : Z := 18.
Definition MVLAN_SIZE : Z := 20.

(** The address of c->seg[i] and of m->seg[i]. *)
Definition rseg_addr (c : Z) (i : nat) : Z := c + RSEG_SIZE * Z.of_nat i.
Definition mseg_addr (m : Z) (i : nat) : Z := m + MSEG_SIZE * Z.of_nat i.
(** The address of c->refusal[i] and of m->kept[i]. *)
Definition refusal_addr (c : Z) (i : nat) : Z := c + RC_REFUSAL + RC_REFUSAL_LEN * Z.of_nat i.
Definition kept_addr (m : Z) (i : nat) : Z := m + MC_KEPT + MC_KEPT_LEN * Z.of_nat i.

(** ** Byte-list views *)
Definition zs (bs : list byte) : list Z := map bv_unsigned bs.
Definition zb (l : list Z) : list byte := map (Z_to_bv 8) l.
Definition ZERO : byte := Z_to_bv 8 0.
(** The bytes [off, off + n) of bs. *)
Definition fld (off n : nat) (bs : list byte) : list byte := firstn n (skipn off bs).
Definition fldz (off n : Z) (bs : list byte) : list byte := fld (Z.to_nat off) (Z.to_nat n) bs.

(** A char[cap] field holding the C string s: s, its NUL, then bytes not fixed. *)
Definition cstr_enc (cap : nat) (s : list Z) (f : list byte) : Prop :=
  length f = cap /\ (length s < cap)%nat /\ ~ In 0 s /\ firstn (S (length s)) (zs f) = s ++ [0].
(** An int, unsigned or enum field: the 4 little-endian bytes of v, 0 <= v < 2^32 (every value the model stores
    here is non-negative; signed fields hold values below 2^31). *)
Definition u32_enc (v : Z) (f : list byte) : Prop := 0 <= v < 2 ^ 32 /\ f = le4 (Z_to_bv 64 v).
(** An int field holding a C truth value the code stores as 1 or 0. *)
Definition flag_enc (b : bool) (f : list byte) : Prop := f = le4 (Z_to_bv 64 (if b then 1 else 0)).
(** The role field: an `enum reac_role_intent` that the harness reads back with `lw`, which sign-extends. The
    encoding therefore bounds it below 2^31, which is where check_role's premise on the role comes from: a caller
    cannot prove it otherwise. The model's roles are 0..4 (SegModel's
    role_intent_parse and the words table of m_key), so the bound costs nothing. One conjunct, as u32_enc was, so
    a walk that destructures an encoding positionally is unchanged. *)
Definition role_enc (v : Z) (f : list byte) : Prop := u32_enc v f /\ v < 2 ^ 31.

(** ** The reader's state, struct reac_segconf *)
(** The role field is an `enum reac_role_intent` the harness reads with `lw` (sign-extending), so the encoding
    bounds it below 2^31: the model's roles are 0..4 (SegModel's role_intent_parse and the words table). This is
    where check_role's premise on the role comes from (a caller cannot prove it otherwise). *)
Definition rseg_enc (s : rseg) (f : list byte) : Prop :=
  length f = 356%nat /\
  cstr_enc 16 (rs_name s) (fld 0 16 f) /\
  role_enc (rs_role s) (fldz RS_ROLE 4 f) /\
  flag_enc (rs_role_set s) (fldz RS_ROLE_SET 4 f) /\
  flag_enc (rs_ignore s) (fldz RS_IGNORE 4 f) /\
  flag_enc (rs_ignore_set s) (fldz RS_IGNORE_SET 4 f) /\
  cstr_enc 24 (rs_model s) (fldz RS_MODEL 24 f) /\
  flag_enc (rs_model_set s) (fldz RS_MODEL_SET 4 f) /\
  cstr_enc 96 (rs_model_file s) (fldz RS_MODEL_FILE 96 f) /\
  cstr_enc 96 (rs_role_file s) (fldz RS_ROLE_FILE 96 f) /\
  cstr_enc 96 (rs_ignore_file s) (fldz RS_IGNORE_FILE 96 f) /\
  u32_enc (rs_seen_gen s) (fldz RS_SEEN_GEN 4 f).

(** The 16616 bytes of a struct reac_segconf holding rc: seg[0 .. n) = rc_seg, n, refusal[0 .. n_refusals) =
    rc_refusal, n_refusals, refused, overflow, reading, gen. *)
Definition rconf_enc (rc : rconf) (bs : list byte) : Prop :=
  Z.of_nat (length bs) = SEG_C_SIZE /\
  (length (rc_seg rc) <= 32)%nat /\
  (forall i, (i < length (rc_seg rc))%nat ->
     rseg_enc (nth i (rc_seg rc) rseg_d) (fld (356 * i) 356 bs)) /\
  u32_enc (Z.of_nat (length (rc_seg rc))) (fldz RC_N 4 bs) /\
  (length (rc_refusal rc) <= 8)%nat /\
  (forall i, (i < length (rc_refusal rc))%nat ->
     cstr_enc 200 (nth i (rc_refusal rc) []) (fld (Z.to_nat RC_REFUSAL + 200 * i) 200 bs)) /\
  u32_enc (Z.of_nat (length (rc_refusal rc))) (fldz RC_NREF 4 bs) /\
  u32_enc (rc_refused rc) (fldz RC_REFUSED 4 bs) /\
  u32_enc (rc_overflow rc) (fldz RC_OVERFLOW 4 bs) /\
  cstr_enc 96 (rc_reading rc) (fldz RC_READING 96 bs) /\
  u32_enc (rc_gen rc) (fldz RC_GEN 4 bs).

(** ** The harness's model, struct mconf *)
Definition mseg_enc (g : mseg) (f : list byte) : Prop :=
  length f = 256%nat /\
  cstr_enc 16 (ms_name g) (fld 0 16 f) /\
  role_enc (ms_role g) (fldz MS_ROLE 4 f) /\
  flag_enc (ms_role_set g) (fldz MS_ROLE_SET 4 f) /\
  flag_enc (ms_ignore g) (fldz MS_IGNORE 4 f) /\
  flag_enc (ms_ignore_set g) (fldz MS_IGNORE_SET 4 f) /\
  flag_enc (ms_model_set g) (fldz MS_MODEL_SET 4 f) /\
  cstr_enc 24 (ms_model g) (fldz MS_MODEL 24 f) /\
  cstr_enc 96 (ms_role_file g) (fldz MS_ROLE_FILE 96 f) /\
  cstr_enc 96 (ms_ignore_file g) (fldz MS_IGNORE_FILE 96 f) /\
  u32_enc (ms_gen g) (fldz MS_GEN 4 f).

(** The 9236 bytes of a struct mconf holding mc: seg[0 .. n) = mc_seg, n, overflow, refused, kept[0 .. n_kept) and
    kept_knock[0 .. n_kept) = mc_kept, kept_knock[n_kept] = pend (when n_kept < 8), kept_knock[n_kept + 1 .. 8) = 0,
    n_kept, gen, reading. pend is true only between m_key's `kept_knock[n_kept] = 1` (fuzz_segconf.c:251-252) and
    the m_refuse that keeps it; everywhere else it is false ([mconf_enc]). *)
Definition mconf_encp (pend : bool) (mc : mconf) (bs : list byte) : Prop :=
  Z.of_nat (length bs) = SEG_M_SIZE /\
  (length (mc_seg mc) <= 32)%nat /\
  (forall i, (i < length (mc_seg mc))%nat ->
     mseg_enc (nth i (mc_seg mc) mseg_d) (fld (256 * i) 256 bs)) /\
  u32_enc (Z.of_nat (length (mc_seg mc))) (fldz MC_N 4 bs) /\
  u32_enc (mc_overflow mc) (fldz MC_OVERFLOW 4 bs) /\
  u32_enc (mc_refused mc) (fldz MC_REFUSED 4 bs) /\
  (length (mc_kept mc) <= 8)%nat /\
  (forall i, (i < length (mc_kept mc))%nat ->
     cstr_enc 112 (fst (nth i (mc_kept mc) ([], false))) (fld (Z.to_nat MC_KEPT + 112 * i) 112 bs) /\
     flag_enc (snd (nth i (mc_kept mc) ([], false))) (fld (Z.to_nat MC_KNOCK + 4 * i) 4 bs)) /\
  (forall i, (length (mc_kept mc) <= i < 8)%nat ->
     flag_enc (pend && (i =? length (mc_kept mc))%nat) (fld (Z.to_nat MC_KNOCK + 4 * i) 4 bs)) /\
  u32_enc (Z.of_nat (length (mc_kept mc))) (fldz MC_NKEPT 4 bs) /\
  u32_enc (mc_gen mc) (fldz MC_GEN 4 bs) /\
  cstr_enc 96 (mc_reading mc) (fldz MC_READING 96 bs).
Definition mconf_enc (mc : mconf) (bs : list byte) : Prop := mconf_encp false mc bs.

(** ** The VLAN tables *)
(** One struct reac_declared_vlan holding (parent, vid): memset + strncpy(parent, 15) leave the parent and zeros. *)
Definition rvlan_enc (e : list Z * Z) (f : list byte) : Prop :=
  length f = 18%nat /\ cstr_enc 16 (fst e) (fld 0 16 f) /\ 0 <= snd e < 65536 /\
  fld 16 2 f = le2 (Z_to_bv 64 (snd e)).
(** One struct mvlan holding (parent, vid) (a struct copy of m_split's stack mvlan: the bytes after the NUL are
    not fixed). *)
Definition mvlan_enc (e : list Z * Z) (f : list byte) : Prop :=
  length f = 20%nat /\ cstr_enc 16 (fst e) (fld 0 16 f) /\ u32_enc (snd e) (fld 16 4 f).
Definition rtab_enc (t : list (list Z * Z)) (bs : list byte) : Prop :=
  length bs = (18 * length t)%nat /\
  forall i, (i < length t)%nat -> rvlan_enc (nth i t ([], 0)) (fld (18 * i) 18 bs).
Definition mtab_enc (t : list (list Z * Z)) (bs : list byte) : Prop :=
  length bs = (20 * length t)%nat /\
  forall i, (i < length t)%nat -> mvlan_enc (nth i t ([], 0)) (fld (20 * i) 20 bs).
(** The guard entry tab[cap] the harness fills with 0x5a (fuzz_segconf.c:654). *)
Definition GUARD_BYTES : list byte := repeat (Z_to_bv 8 0x5a) 18.

(** The n bytes at a lie wholly below lo or at or above hi (an object apart from the stack region [lo, hi), or from
    a block). *)
Definition apart (a n lo hi : Z) : Prop := a + n <= lo \/ hi <= a.
(** The bytes a word-at-a-time reader takes of the C string s at a: s, its NUL and the slack up to the next 8-byte
    boundary (cstr_at's slack). A text block and the next heap block may be adjacent (16-aligned blocks, no slack
    after a block whose end is 8-aligned), so a premise that keeps a string apart from a BLOCK uses this span, not
    length s + 8 (unprovable when t = malloc(16) and m = t + 16). *)
Definition cstr_span (a : Z) (s : list Z) : Z := Z.of_nat (length s) + 1 + (- (a + Z.of_nat (length s) + 1)) mod 8.

(** ** In memory (the build's segment list [segs]) *)
Section At.
Variable segs : list Segment.

Definition rconf_at (m : word -> option byte) (c : Z) (rc : rconf) : Prop :=
  exists bs, bytes_at segs m c bs /\ rconf_enc rc bs.
Definition mconf_at (m : word -> option byte) (a : Z) (mc : mconf) : Prop :=
  exists bs, bytes_at segs m a bs /\ mconf_enc mc bs.
Definition mconf_atp (pend : bool) (m : word -> option byte) (a : Z) (mc : mconf) : Prop :=
  exists bs, bytes_at segs m a bs /\ mconf_encp pend mc bs.
Definition mseg_at (m : word -> option byte) (a : Z) (g : mseg) : Prop :=
  exists bs, bytes_at segs m a bs /\ mseg_enc g bs.
Definition rtab_at (m : word -> option byte) (a : Z) (t : list (list Z * Z)) : Prop :=
  exists bs, bytes_at segs m a bs /\ rtab_enc t bs.
Definition mtab_at (m : word -> option byte) (a : Z) (t : list (list Z * Z)) : Prop :=
  exists bs, bytes_at segs m a bs /\ mtab_enc t bs.
Definition guard_at (m : word -> option byte) (tab cap : Z) : Prop :=
  bytes_at segs m (tab + RVLAN_SIZE * cap) GUARD_BYTES.

(** The C string s at a: s, its NUL, and the bytes after it up to the next 8-byte boundary present (the slack the
    word-at-a-time readers need: strlen, strchr, memchr, strnlen in printf's %s, strstr; pin's strlen_c.v:23). *)
Definition cstr_at (m : word -> option byte) (a : Z) (s : list Z) : Prop :=
  exists bs slack, bytes_at segs m a (bs ++ ZERO :: slack) /\ zs bs = s /\ ~ In 0 s /\
    (- (a + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack).
(** A C string argument that may be NULL: None is the pointer 0. *)
Definition ocstr_at (m : word -> option byte) (a : Z) (o : option (list Z)) : Prop :=
  match o with None => a = 0 | Some s => a <> 0 /\ cstr_at m a s end.
(** The C string s at a with its NUL, no slack: what strcmp reads (CMD's strcmp_c.v: sx ++ [0]). *)
Definition cstrz_at (m : word -> option byte) (a : Z) (s : list Z) : Prop :=
  exists bs, bytes_at segs m a (bs ++ [ZERO]) /\ zs bs = s /\ ~ In 0 s.
Definition ocstrz_at (m : word -> option byte) (a : Z) (o : option (list Z)) : Prop :=
  match o with None => a = 0 | Some s => a <> 0 /\ cstrz_at m a s end.
(** The bytes after a block of n bytes at a, up to the next 8-byte boundary, present (the frame's
    block_slack_present gives them for every malloc block; struct mconf is 9236 bytes, so a C string at the end of
    m->reading reads up to 4 bytes past the block). *)
Definition blk_slack (m : word -> option byte) (a n : Z) : Prop :=
  exists sl, bytes_at segs m (a + n) sl /\ (- (a + n)) mod 8 <= Z.of_nat (length sl).
(** The saved registers of a frame: the words ws at consecutive 8-byte slots from a upward (a prologue's
    `sd` list, read by its epilogue). *)
Definition saved_at (m : word -> option byte) (a : Z) (ws : list word) : Prop :=
  bytes_at segs m a (concat (map le8 ws)).

(** No byte of the n bytes at a lies in a reserved segment of the image. This is what a printf destination needs
    (printf_facts_c.pf_img_free is this Prop with segs := rsegs), and it is what the slot can give: a frame's
    allocator laws say no byte of a live block is in_img B, and in_img is the PAGE-ROUNDED reservation of each
    segment (LPS Run.v segment_reservation). An address comparison against the image's end cannot be proved there,
    so every block premise here is stated in this form. *)
Definition blk_noimg (a n : Z) : Prop :=
  forall i, 0 <= i < n -> forall s, In s (segments_reserved segs) ->
    ~ (bv_unsigned (fst s) <= a + i < bv_unsigned (fst s) + bv_unsigned (snd s)).

(** The box-model table reads as in the image (it lies in .data.rel.ro, which mem_inv does not fix; FR's relro). *)
Definition cat_img (m : word -> option byte) (cat : Z) : Prop :=
  forall a, cat <= a < cat + CAT_BYTES -> mrd segs m (wa a) = seg_rom segs (wa a).

(** The stack region [lo, sp) a function and its callees use: present and writable (stk), deep enough, outside the
    image, sp 16-aligned (the frame's stack region [S - 65536, S) gives all four at every call site). *)
Definition stack_ok (m : word -> option byte) (lo sp depth : Z) : Prop :=
  stk segs m lo sp /\ lo + depth <= sp /\ sp mod 16 = 0 /\ (forall a, lo <= a < sp -> seg_rom segs (wa a) = None).

(** What every contract of a returning function promises: it comes back to ra with a0 = r, ra, sp, gp, tp, s0-s11,
    the FP registers and fcsr as they were (t0-t6 and a1-a7 not fixed), no byte changed outside W, the writable
    view kept, mem_inv, the stack region still present, and Q of the new memory. *)
Definition ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (m : word -> option byte) (W : list ivl) (lo : Z) (Q : (word -> option byte) -> Prop)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom segs) /\
    munch W m m' /\ wmono segs m m' /\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp) /\ Q m'.
(** The same for a void function: a0 not fixed either. *)
Definition ret_void (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (W : list ivl) (lo : Z) (Q : (word -> option byte) -> Prop)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom segs) /\
    munch W m m' /\ wmono segs m m' /\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp) /\ Q m'.
(** The n bytes at a are apart from every range of W. *)
Definition apart_all (a n : Z) (W : list ivl) : Prop := Forall (fun iv => apart a n (fst iv) (snd iv)) W.

(** One variadic argument of a refusal (refuse's a3 .. a7, read through its va_list by vsnprintf), for the
    spine's [arg].
    A STRING argument is a pointer to its C string (slack included, so printf's strnlen and memchr can read it),
    of at most 65535 bytes, apart from every range of W. W holds the stack region [lo, sp), the refusal slot
    [D, D + 200) that the prefix snprintf and vsnprintf write, and the 4 bytes of c->refused, which `c->refused++`
    (R:32) writes BEFORE either call reads an argument. The walk of refuse needs both the length bound and the
    refused range: without the bound, musl's printf_core reads
    strnlen(a, INT_MAX), returns -1 and prints nothing where the spine prints the text; without the refused range,
    an argument may be the refused cell itself, and the binary then prints its new bytes while the spine prints the
    old ones.
    An INTEGER argument is NON-NEGATIVE and below 2^31 in its register. The sign matters: F_long's conversion is
    `%zu`, which musl prints as a size_t while SegModel.fmt prints `dec` of the argument.
    Every call site meets all three: the strings are the line buffer (< 512), cur_name (< 16), known (77),
    c->reading (< 96), a segment name (< 16) or a model (< 24), all in parse_file's frame or in the c block below
    0x2c80; the integers are 511, 15 and 32. *)
Definition va_arg_ok (m : word -> option byte) (W : list ivl) (r : word) (a : arg) : Prop :=
  match a with
  | AS s => bv_unsigned r <> 0 /\ cstr_at m (bv_unsigned r) s /\ (length s <= 65535)%nat /\
            apart_all (bv_unsigned r) (Z.of_nat (length s) + 8) W
  | AI z => 0 <= z < 2 ^ 31 /\ bv_unsigned r = z
  end.
Fixpoint va_args_ok (m : word -> option byte) (W : list ivl) (rs : list word) (args : list arg) : Prop :=
  match args, rs with
  | [], _ => True
  | a :: args', r :: rs' => va_arg_ok m W r a /\ va_args_ok m W rs' args'
  | _ :: _, [] => False
  end.
End At.

(** ** The refusal formats *)
(** The 17 formats of reac_segconf.c's refusals (R:147 .. R:319), SegModel's names. *)
Definition REFUSE_FORMATS : list (list Z) :=
  [F_long; F_notclosed; F_after; F_unknown; F_noname; F_toolong; F_bound; F_twice; F_neither; F_outside;
   F_badrole; F_badignore; F_knock; F_badmodel; F_nokey; F_xmodel; F_xbox].
(** The kinds of a format's conversions in order, as SegModel.fmt reads them: true for %s and %.NNs (a pointer),
    false for %d, %u and %zu (an integer). *)
Fixpoint conv_kinds (f : list Z) : list bool :=
  match f with
  | [] => []
  | c :: f1 =>
      if negb (c =? 37) then conv_kinds f1 else
      match f1 with
      | [] => []
      | c1 :: f2 =>
          if c1 =? 115 then true :: conv_kinds f2
          else if (c1 =? 100) || (c1 =? 117) then false :: conv_kinds f2
          else if c1 =? 122 then match f2 with _ :: f3 => false :: conv_kinds f3 | [] => [] end
          else if c1 =? 46 then match f2 with _ :: _ :: _ :: f4 => true :: conv_kinds f4 | _ => [] end
          else []
      end
  end.
Definition arg_is_s (a : arg) : bool := match a with AS _ => true | AI _ => false end.
(** The bytes of struct reac_segconf that reac_segconf_parse_file may write: seg[32] and n, refusal[8], n_refusals,
    refused, overflow, reading and gen. *)
Definition RC_PARSE_W (c : Z) : list ivl :=
  [(c, c + RC_N + 4); (c + RC_REFUSAL, c + RC_OVERFLOW + 4); (c + RC_READING, c + RC_GEN + 4)].

(** ** Pointer answers of the reader's queries, in the spine's terms *)
(** reac_segconf_find: &c->seg[i] for the spine's r_find, else NULL. *)
Definition find_ptr (c : Z) (rc : rconf) (name : list Z) : Z :=
  match r_find rc name with Some i => rseg_addr c i | None => 0 end.
(** reac_segconf_role_file / ignore_file / model: the field of the found entry when the spine's accessor answers
    Some, else NULL. *)
Definition role_file_ptr (c : Z) (rc : rconf) (name : list Z) : Z :=
  match r_find rc name, r_role_file rc name with Some i, Some _ => rseg_addr c i + RS_ROLE_FILE | _, _ => 0 end.
Definition ignore_file_ptr (c : Z) (rc : rconf) (name : list Z) : Z :=
  match r_find rc name, r_ignore_file rc name with Some i, Some _ => rseg_addr c i + RS_IGNORE_FILE | _, _ => 0 end.
Definition model_ptr (c : Z) (rc : rconf) (name : list Z) : Z :=
  match r_find rc name, r_model rc name with Some i, Some _ => rseg_addr c i + RS_MODEL | _, _ => 0 end.
(** fuzz_catalogue_row / reac_box_catalogue_by_token: &fuzz_catalogue[i] for the spine's row, else NULL. *)
Definition cat_ptr (cat : Z) (o : option nat) : Z :=
  match o with Some i => cat + CAT_ROW * Z.of_nat i | None => 0 end.
Definition b2z (b : bool) : Z := if b then 1 else 0.
(** trim's leading blanks: the offset of the pointer trim returns (R:52-53). The NUL it stores is at
    trim_lead s + length (r_trim s) (R:54-58). *)
Definition trim_lead (s : list Z) : nat := length (takewhile blank (cut_nul s)).


(** ** The payload of one call of LLVMFuzzerTestOneInput (H:579-620), from the input bytes
    The slot's cut predicates (Prog/seg_cuts.v and lib/U/Prog/seg_cuts.v) and the walks of main name the input's
    quantities through these: the decoded payload, the cursor after k file records, and each turn's values. *)
Definition seg_in (inp : list byte) : list Z := zs inp.
Definition seg_pay (inp : list byte) : payload := decode (seg_in inp).
Definition seg_cap (inp : list byte) : Z := p_cap (seg_pay inp).
Definition seg_flags (inp : list byte) : Z := p_flags (seg_pay inp).
Definition seg_files (inp : list byte) : list file := p_files (seg_pay inp).
Definition seg_nfiles (inp : list byte) : Z := Z.of_nat (length (seg_files inp)).
Definition seg_file (inp : list byte) (f : nat) : file := nth f (seg_files inp) (File 0 []).
Definition seg_txt (inp : list byte) (f : nat) : list Z := f_text (seg_file inp f).
Definition seg_txt_n (inp : list byte) (f : nat) : Z := Z.of_nat (length (seg_txt inp f)).
Definition seg_lb (inp : list byte) (f : nat) : Z := f_lb (seg_file inp f).
Definition seg_label (inp : list byte) (f : nat) : option (list Z) := label_of (seg_lb inp f).

(** The cursor: the bytes left after the three header u8 (cap, flags, nfiles), then after k file records. *)
Definition seg_hdr (inp : list byte) : list Z :=
  snd (fuzz_u8 (snd (fuzz_u8 (snd (fuzz_u8 (seg_in inp)))))).
Fixpoint seg_skip (k : nat) (l : list Z) : list Z :=
  match k with
  | O => l
  | S k' =>
      let (_, i1) := fuzz_u8 l in
      let (len, i2) := fuzz_u16 i1 in
      let (_, i3) := fuzz_take i2 len in
      seg_skip k' i3
  end.
Definition seg_cur (inp : list byte) (k : nat) : list Z := seg_skip k (seg_hdr inp).
(** The address of the cursor after k records, for an input block at p, and the count left. *)
Definition seg_cur_at (inp : list byte) (p : Z) (k : nat) : Z :=
  p + Z.of_nat (length inp) - Z.of_nat (length (seg_cur inp k)).
Definition seg_cur_n (inp : list byte) (k : nat) : Z := Z.of_nat (length (seg_cur inp k)).

(** Turn k's reads: lb, the u16 length, the bytes fuzz_take takes (their address is the cursor after lb and the
    u16, and their count n' = min(len, left)), and the text = those bytes cut at their first NUL. *)
Definition seg_turn_tail (inp : list byte) (k : nat) : list Z :=
  snd (fuzz_u16 (snd (fuzz_u8 (seg_cur inp k)))).
Definition seg_turn_len (inp : list byte) (k : nat) : Z := fst (fuzz_u16 (snd (fuzz_u8 (seg_cur inp k)))).
Definition seg_turn_np (inp : list byte) (k : nat) : Z :=
  Z.of_nat (length (fst (fuzz_take (seg_turn_tail inp k) (seg_turn_len inp k)))).
Definition seg_turn_at (inp : list byte) (p : Z) (k : nat) : Z :=
  p + Z.of_nat (length inp) - Z.of_nat (length (seg_turn_tail inp k)).

(** The states after k turns, every one of them a drop-in (H:612-613): the last turn (H:615-617, m_cross and
    reac_segconf_parse) is [seg_turn] with [last] true. The whole run is SegModel.run. *)
Definition seg_turn_step (inp : list byte) (k : nat) (last : bool) (st : rconf * mconf * bool)
    : rconf * mconf * bool :=
  let '(c, mc, ret) := st in
  let t := seg_txt inp k in
  if last then
    let m1 := m_cross (m_file mc t None) in
    let (c1, n) := r_parse c t in
    (c1, m1, ret && (n =? Z.of_nat (length (mc_seg m1))))
  else
    let l := seg_label inp k in
    let m1 := m_file mc t l in
    let (c1, n) := r_parse_file c t l in
    (c1, m1, ret && (n =? Z.of_nat (length (mc_seg m1)))).
Fixpoint seg_run (inp : list byte) (k : nat) : rconf * mconf * bool :=
  match k with
  | O => (rconf0, mconf0, true)
  | S k' => seg_turn_step inp k' false (seg_run inp k')
  end.
Definition seg_rc (st : rconf * mconf * bool) : rconf := fst (fst st).
Definition seg_mc (st : rconf * mconf * bool) : mconf := snd (fst st).
Definition seg_ret (st : rconf * mconf * bool) : bool := snd st.
(** The state after turn k, whichever kind it was. *)
Definition seg_after (inp : list byte) (k : nat) : rconf * mconf * bool :=
  seg_turn_step inp k (Z.of_nat (S k) =? seg_nfiles inp) (seg_run inp k).

(** The VLAN tables the harness starts from (H:657-660) and the two answers (H:664-665). *)
Definition seg_tab0 (inp : list byte) : list (list Z * Z) := vlan_init (seg_pay inp).

(** ** Facts *)
Lemma skipn_repeat_gen : forall {A} (x : A) off len, skipn off (repeat x len) = repeat x (len - off).
Proof.
  intros A x off. induction off as [|off IH]; intros len; [rewrite Nat.sub_0_r; reflexivity|].
  destruct len as [|len]; [reflexivity|]. cbn [repeat skipn]. rewrite IH. reflexivity.
Qed.

Lemma firstn_repeat_gen : forall {A} (x : A) n len, firstn n (repeat x len) = repeat x (Nat.min n len).
Proof.
  intros A x n. induction n as [|n IH]; intros len; [reflexivity|].
  destruct len as [|len]; [reflexivity|]. cbn [repeat firstn Nat.min]. rewrite IH. reflexivity.
Qed.

Lemma fld_repeat : forall (x : byte) off n len, (off + n <= len)%nat -> fld off n (repeat x len) = repeat x n.
Proof.
  intros x off n len H. unfold fld. rewrite skipn_repeat_gen, firstn_repeat_gen. f_equal. lia.
Qed.

Lemma cstr_enc_nil_zero : forall cap, (0 < cap)%nat -> cstr_enc cap [] (repeat ZERO cap).
Proof.
  intros cap H. split; [apply repeat_length|]. split; [cbn; lia|]. split; [intros []|].
  destruct cap as [|cap]; [lia|]. reflexivity.
Qed.

Lemma u32_enc_zero : u32_enc 0 (repeat ZERO 4).
Proof. split; [lia | reflexivity]. Qed.

Lemma flag_enc_false_zero : flag_enc false (repeat ZERO 4).
Proof. reflexivity. Qed.

Ltac fz := unfold RC_N, RC_NREF, RC_REFUSED, RC_OVERFLOW, RC_READING, RC_GEN, MC_N, MC_OVERFLOW, MC_REFUSED,
  MC_KNOCK, MC_NKEPT, MC_GEN, MC_READING, SEG_C_SIZE, SEG_M_SIZE; lia.

(** reac_segconf_init's zeros encode rconf0, calloc's zeros encode mconf0. *)
Lemma rconf_enc_zero : rconf_enc rconf0 (repeat ZERO (Z.to_nat SEG_C_SIZE)).
Proof.
  unfold rconf_enc, fldz; cbn [rconf0 rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen length Z.of_nat].
  split; [rewrite repeat_length; fz|]. split; [lia|]. split; [intros i Hi; lia|].
  split; [rewrite fld_repeat by fz; exact u32_enc_zero|]. split; [lia|]. split; [intros i Hi; lia|].
  split; [rewrite fld_repeat by fz; exact u32_enc_zero|].
  split; [rewrite fld_repeat by fz; exact u32_enc_zero|].
  split; [rewrite fld_repeat by fz; exact u32_enc_zero|].
  split; [rewrite fld_repeat by fz; apply cstr_enc_nil_zero; lia|].
  rewrite fld_repeat by fz. exact u32_enc_zero.
Qed.

Lemma mconf_enc_zero : mconf_enc mconf0 (repeat ZERO (Z.to_nat SEG_M_SIZE)).
Proof.
  unfold mconf_enc, mconf_encp, fldz; cbn [mconf0 mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading length Z.of_nat].
  split; [rewrite repeat_length; fz|]. split; [lia|]. split; [intros i Hi; lia|].
  split; [rewrite fld_repeat by fz; exact u32_enc_zero|].
  split; [rewrite fld_repeat by fz; exact u32_enc_zero|].
  split; [rewrite fld_repeat by fz; exact u32_enc_zero|].
  split; [lia|]. split; [intros i Hi; lia|].
  split; [intros i Hi; rewrite fld_repeat by fz; exact flag_enc_false_zero|].
  split; [rewrite fld_repeat by fz; exact u32_enc_zero|].
  split; [rewrite fld_repeat by fz; exact u32_enc_zero|].
  rewrite fld_repeat by fz. apply cstr_enc_nil_zero. lia.
Qed.

(** The table's tokens are SegModel's [cat_toks], byte for byte. *)
Lemma cat_toks_bytes : map (fun i => zs (tok_bytes i)) (seq 0 CAT_N) = cat_toks.
Proof. vm_compute. reflexivity. Qed.

Lemma cat_tok_nth : forall i, (i < CAT_N)%nat -> zs (tok_bytes i) = nth i cat_toks [].
Proof.
  intros i Hi. unfold CAT_N in Hi.
  do 11 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
Qed.

(** R:258-263's join of the 11 tokens: 77 bytes, so `kn + 2 < 240` holds on every pass. *)
Lemma known_length : length known = 77%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma known_nulfree : ~ In 0 known.
Proof. intros H. vm_compute in H. repeat (destruct H as [H|H]; [discriminate H|]). exact H. Qed.
