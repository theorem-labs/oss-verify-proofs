(* reac-pw/fuzz_link, PLAIN build: the addresses of link's own globals, the views the contracts of
   its own functions take over them, and the two shapes those contracts have.

   Every address below was read from the image the proofs load (the unstripped twin of the pin
   ebe34b259b9f): link/donors/globals.tsv for the objects, link/donors/premises-plain.txt for the
   .rodata each own function forms. The byte OFFSETS inside the structures, and every pure
   function, are in lib/Prog/link_spec.v and are shared with the UBSan build.

   The two shapes:
   - `leaf`: a call that reaches no allocator and makes no system call. It keeps the callee-saved
     registers and the floating-point file, writes only its own frame and the addresses `Wr`
     names, and leaves `Post`. Almost every own function of link has this shape.
   - `leaf_fp`: the same, for the four that reach the printf layer (snprintf, fprintf, vfprintf).
     printf_core leaves fa0 free and only promises that the rounding mode is still 0, so those
     contracts give the same freedom (the form of the released snprintf contract,
     libreac/fuzz_boxreg lib/Prog/printf_facts_c.v:118-135). *)
From Stdlib Require Export ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Export
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Export Prelude Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Export YK0s YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Export
  PropExec MState Mem Cells Exec Step Frame FP Arr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Export Img0 MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Export link_spec.
Export ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Addresses in the plain image
   ========================================================================== *)

(* .bss *)
Definition A_G_NL : Z := 0x31b80.          (* struct nl_kernel g_nl, 271992 bytes *)
Definition A_G_NAMES : Z := 0x741f8.       (* char g_names[64][8] *)
Definition A_LONG_ALIAS : Z := 0x743f8.    (* msg_build.long_alias, char[301] *)
Definition A_G_SINK : Z := 0x74528.        (* FILE *g_sink *)
Definition A_G_SAID : Z := 0x74530.        (* char g_said[4096] *)
Definition A_G_SAY : Z := 0x75530.         (* FILE *g_say, in reac_served_mark.c *)

(* .data.rel.ro: the two pointer tables *)
Definition A_ODD : Z := 0x207c0.           (* const char *odd[6] *)
Definition A_TEXTS : Z := 0x207f0.         (* const char *texts[11] *)

(* .got: the slot reac_served_mark loads for `stderr` *)
Definition A_GOT_STDERR : Z := 0x20898.
Definition A_STDERR_VAR : Z := 0x20848.

(* .rodata *)
Definition A_NL_ERRNO_E : Z := 0x106e4.    (* nl_errno.e, 6 x int32 *)
Definition A_PREFIX : Z := 0x10517.        (* "reac-pw:" *)
Definition A_SERVED : Z := 0x10341.        (* "reac-pw:served" *)
Definition A_VLAN : Z := 0x1056f.          (* "vlan" *)
Definition A_EMPTY : Z := 0x10368.         (* "" *)
Definition A_FMT_S : Z := 0x103b9.         (* "%s" *)

(* The stack floor every printf path needs, and the stack protector's two words (gap 5 of
   link/ct/AMEND-mark.md). printf_core runs through the main CJ instance, where the CJ statements
   take `GLOBALS_TOP <= lo` and GLOBALS_TOP = sym 0x35000 = 0x97000 (lib/CJ/RL/I/IImgP.v:18);
   the plain image ends at 0x960e0, below it, so 0x97000 also covers the snprintf instance's
   IMG_END. A_GOT_GUARD is the .got slot holding &__stack_chk_guard, A_GUARD that word; both as the
   plain snprintf_c.v states them. *)
Definition A_IMG_TOP : Z := 0x97000.
Definition A_GOT_GUARD : Z := 0x208d8.
Definition A_GUARD : Z := 0x95878.

(* the entry of every own function of the plain image (link/functions.tsv) *)
Definition P_fuzz_socket : Z := 0x134a0.
Definition P_fuzz_send : Z := 0x13528.
Definition P_fuzz_recv : Z := 0x13610.
Definition P_fuzz_close : Z := 0x13778.
Definition P_fuzz_if_nametoindex : Z := 0x137c0.
Definition P_LLVMFuzzerTestOneInput : Z := 0x1384c.
Definition P_kernel : Z := 0x14190.
Definition P_text_buf : Z := 0x14fb0.
Definition P_model_read : Z := 0x14ffc.
Definition P_check_socket : Z := 0x150e4.
Definition P_index_of : Z := 0x15120.
Definition P_check_refused : Z := 0x151ac.
Definition P_check_bounds : Z := 0x151c0.
Definition P_check_read : Z := 0x15210.
Definition P_check_requests : Z := 0x15284.
Definition P_attr_text : Z := 0x1534c.
Definition P_nl_error : Z := 0x154b4.
Definition P_talk : Z := 0x156e4.
Definition P_text_of : Z := 0x15aa8.
Definition P_model_write : Z := 0x15c50.
Definition P_check_write : Z := 0x15d58.
Definition P_mark_quietly : Z := 0x15d88.
Definition P_check_mark : Z := 0x15e04.
Definition P_check_marks : Z := 0x15e34.
Definition P_model_decide : Z := 0x15eac.
Definition P_check_verdict : Z := 0x15f18.
Definition P_reac_link_alias_read : Z := 0x15f2c.
Definition P_nl_talk : Z := 0x16008.
Definition P_reac_link_alias_write : Z := 0x16290.
Definition P_copy_attr : Z := 0x1637c.
Definition P_reac_served_say_to : Z := 0x163f8.
Definition P_reac_served_decide : Z := 0x16404.
Definition P_reac_served_mark : Z := 0x16470.
Definition P_reac_code_emit : Z := 0x16640.
Definition P_remember : Z := 0x166b4.
Definition P_reac_served_unmark_all : Z := 0x16770.

(* ==========================================================================
   2. Views over memory
   ========================================================================== *)

Definition wz (a : Z) : word := Z_to_bv 64 a.

Definition u32_at (m : word -> option byte) (a v : Z) : Prop := bytes_at rsegs m a (le4 (wz v)).
Definition u64_at (m : word -> option byte) (a v : Z) : Prop := bytes_at rsegs m a (le8 (wz v)).

(* a C string at `a`: its bytes, then a NUL, and no NUL inside *)
Definition cstr_at (m : word -> option byte) (a : Z) (s : list byte) : Prop :=
  bytes_at rsegs m a (s ++ [zb 0]) /\ ~ In (zb 0) s.

(* a buffer text_buf(cap) made: cap bytes the reader may write and the guard byte after them
   (fuzz_link.c:656-666) *)
Definition tbuf_at (m : word -> option byte) (a cap : Z) (bs : list byte) : Prop :=
  rw_cells rsegs m a [CB (Z.to_nat cap) bs; C1 (zb GUARD_BYTE)].

(* the whole fake kernel as one byte list *)
Definition nlk_at (m : word -> option byte) (bs : list byte) : Prop :=
  u8arr rsegs m A_G_NL bs /\ Z.of_nat (length bs) = NK_SIZE.

(* the struct model block calloc handed out, at `p` *)
Definition model_at (m : word -> option byte) (p : Z) (bs : list byte) : Prop :=
  u8arr rsegs m p bs /\ Z.of_nat (length bs) = MD_SIZE.

(* the struct reac_served_marks block, at `p` *)
Definition marks_at (m : word -> option byte) (p : Z) (bs : list byte) : Prop :=
  u8arr rsegs m p bs /\ Z.of_nat (length bs) = MK_SIZE.

(* The interface table index_of and fuzz_if_nametoindex walk. The index is bounded
   (LinkHelpers, 2026-10-30): `u32_at` fixes only its low 32 bits, so without
   `0 <= ix < 2 ^ 31` the same memory satisfies iftab_at for ix and for ix + 2^32, and
   index_of's Post, which answers the sign-extended `lw`, would be false. The real indices
   are 2..65 and 101..104 (fuzz_link.c:94, :98). g_nl.if_name[i] points at a C
   string and g_nl.if_index[i] is its index (fuzz_link.c:84-98 fills it; 64 entries after
   interfaces()). The names live in g_names and in the `odd` table, both outside g_nl. *)
Definition iftab_at (m : word -> option byte) (bs : list byte) (tab : list (list byte * Z)) : Prop :=
  nk_n_if bs = Z.of_nat (length tab) /\ (Z.of_nat (length tab) <= 80)%Z /\
  forall i nm ix, nth_error tab i = Some (nm, ix) ->
    0 <= ix < 2 ^ 31 /\
    exists p, u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p /\ p <> 0 /\
              cstr_at m p nm /\
              u32_at m (A_G_NL + NK_IF_INDEX + 4 * Z.of_nat i) ix.

(* the four policy strings the two deciders and the marker form *)
Definition policy_ro (m : word -> option byte) : Prop :=
  cstr_at m A_PREFIX S_PREFIX /\ cstr_at m A_SERVED S_SERVED /\
  cstr_at m A_VLAN S_VLAN /\ cstr_at m A_EMPTY [].

(* ==========================================================================
   3. The two contract shapes
   ========================================================================== *)

Definition leaf (pc K : Z)
    (Pre : bvmap 5 word -> (word -> option byte) -> Prop)
    (Wr : bvmap 5 word -> (word -> option byte) -> list ivl)
    (Post : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Prop)
  : Prop :=
  forall (regs F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    Pre regs m ->
    mem_inv rsegs m -> stk rsegs m lo (spZ regs) -> lo + K <= spZ regs -> spZ regs < 2 ^ 63 ->
    evt rsegs
      (fun ms' => exists (regs' : bvmap 5 word) (m' : word -> option byte),
         ms' = MS regs' F (ret_pc (getr regs 1)) fc None m' (seg_rom rsegs) /\
         regs_preserved regs regs' /\
         munch ((spZ regs - K, spZ regs) :: Wr regs m) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (spZ regs) /\
         Post regs m regs' m')
      (MS regs F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Definition leaf_fp (pc K : Z)
    (Pre : bvmap 5 word -> (word -> option byte) -> Prop)
    (Wr : bvmap 5 word -> (word -> option byte) -> list ivl)
    (Post : bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Prop)
  : Prop :=
  forall (regs F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    Pre regs m ->
    mem_inv rsegs m -> task_mem rsegs m ->
    stk rsegs m lo (spZ regs) -> lo + K <= spZ regs -> spZ regs < 2 ^ 63 -> frm0 fc ->
    A_IMG_TOP <= lo ->
    bytes_at rsegs m A_GOT_GUARD (le8 (wz A_GUARD)) -> (exists c, bytes_at rsegs m A_GUARD (le8 c)) ->
    evt rsegs
      (fun ms' => exists (regs' Ft : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
         ms' = MS regs' Ft (ret_pc (getr regs 1)) fc' None m' (seg_rom rsegs) /\
         frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k) /\
         regs_preserved regs regs' /\
         munch ((spZ regs - K, spZ regs) :: Wr regs m) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ task_mem rsegs m' /\
         stk rsegs m' lo (spZ regs) /\
         Post regs m regs' m')
      (MS regs F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* the usual shorthands a contract needs *)
Definition arg (regs : bvmap 5 word) (i : Z) : Z := bv_unsigned (getr regs (Z_to_bv 5 (10 + i))).
Definition res (regs : bvmap 5 word) : Z := bv_unsigned (getr regs 10).
(* a result the C side reads as a signed int *)
Definition res_i32 (regs : bvmap 5 word) : Z :=
  let v := res regs mod 2 ^ 32 in if v <? 2 ^ 31 then v else v - 2 ^ 32.
Definition writes_nothing (regs : bvmap 5 word) (m : word -> option byte) : list ivl := [].
Definition unchanged (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop := m' = m.

(* errno: ___errno_location is `mv a0, tp; addi a0, a0, -0xa4` in both images *)
Definition ERRNO_TP_OFF : Z := -164.
Definition errno_at (regs : bvmap 5 word) : Z := bv_unsigned (getr regs 4) + ERRNO_TP_OFF.

Definition u16_at (m : word -> option byte) (a v : Z) : Prop := bytes_at rsegs m a (le2 (wz v)).

(* a struct nl_w the harness builds a reply in *)
Definition nlw_at (m : word -> option byte) (p : Z) (bs : list byte) : Prop :=
  u8arr rsegs m p bs /\ Z.of_nat (length bs) = NW_SIZE.

(* an argument the C side reads as `const char *`: NULL, or the C string at that address *)
Definition str_arg (m : word -> option byte) (a : Z) (o : option (list byte)) : Prop :=
  match o with None => a = 0 | Some s => a <> 0 /\ cstr_at m a s end.

(* a buffer argument a reader may fill: NULL or a zero cap is "no buffer" *)
Definition buf_arg (m : word -> option byte) (a cap : Z) : Prop :=
  a <> 0 -> 1 <= cap -> exists junk, rw_cells rsegs m a [CB (Z.to_nat cap) junk].

(* A pointer argument must not be inside the callee's own frame: the prologue would change
   what it points at, and a write through it would change the saved registers. Every contract
   that reads or writes through a pointer argument takes this. *)
Definition apart_frame (regs : bvmap 5 word) (K a n : Z) : Prop :=
  a + n <= spZ regs - K \/ spZ regs <= a.

(* ... and must not overlap the fake kernel, whose bytes the same function reads or writes. *)
Definition apart_gnl (a n : Z) : Prop :=
  a + n <= A_G_NL \/ A_G_NL + NK_SIZE <= a.

(* ... and the callee's own frame must not land in the fake kernel either: `stk` says only
   that [lo, sp) is writable, and .bss is writable too. Every function that reads or writes
   g_nl and pushes a frame takes this. *)
Definition frame_apart_gnl (regs : bvmap 5 word) (K : Z) : Prop :=
  apart_gnl (spZ regs - K) K.

(* A function whose returning path pushes a frame does NOT leave memory as it found it: the
   prologue stores ra and the callee-saved registers into [sp-K, sp) and nothing restores those
   bytes. `leaf` already says that only that window and `Wr` changed, so a contract that adds
   nothing of its own uses this and not `unchanged`. `unchanged` stays for the K = 0 functions,
   whose returning path touches no stack at all. *)
Definition only_frame (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop := True.

(* the heap block fmemopen hands out for one FILE and its cookie *)
Definition FILE_BLOCK : Z := 1304.

(* two byte ranges [a, a+n) and [b, b+k) are disjoint *)
Definition apart (a n b k : Z) : Prop := a + n <= b \/ b + k <= a.

(* the read-only image: the first PT_LOAD of the plain build, which is where the eleven
   `texts` strings live. The same two numbers plain snprintf_c.v holds as RO_LO and RO_END. *)
Definition A_RO_LO : Z := 0x10000.
Definition A_RO_END : Z := 0x11eb4.

(* A string no call of this unit can move: it is inside g_names, which only interfaces() writes
   (fuzz_link.c:83-109), or it is read-only image. Every interface name and every `odd` entry
   is one or the other, and a caller that reads a name AFTER a callee wrote g_said, errno,
   g_sink or g_say needs that (a Theorem Labs lane gap 17). *)
Definition kept_str (a n : Z) : Prop :=
  (A_G_NAMES <= a /\ a + n <= A_G_NAMES + G_NAMES_SIZE)
  \/ (forall i, 0 <= i < n -> ro_addr rsegs (wa (a + i)) = true).

(* The bytes a word-at-a-time strlen reads of the C string s at a: the string, its NUL, and the
   slack up to the next multiple of 8. This is the exact span, and it ends inside g_names for
   every slot of it, where a flat `length s + 8` does not: g_names[63] is at 0x743f0, so "nl63"
   plus 8 ends at 0x743fc, past g_names' end at 0x743f8 (a Theorem Labs lane, AMEND-slot item 10). *)
Definition name_span (a : Z) (s : list byte) : Z :=
  Z.of_nat (length s) + 1 + (- (a + Z.of_nat (length s) + 1)) mod 8.
