(* remember (reac_served_mark.c:38-47) on image A (fuzz_link.asan 0x89db4, 288 bytes; listing
   (internal path) (internal record, sha256 e02062b286f1)): keep the name of an interface this
   run marked, once, at most 32 of them. a0 = m (the struct reac_served_marks block), a1 = ifname. The plain contract
   is lib/Prog/remember_c.v; this file states the SAME link_spec result (`remember`) in link_amem.v's `aleaf_fx`
   form (the read-set shape for a function that reaches the printf family: rounding mode 0 at entry, a Post at
   SOME fx' related to the entry's by BoxBase.v `fxr`, and a Pre that also sees the call's block list).

   The image-A code, in order:
     +0x00..+0x20  push a 64-byte frame; save ra, s0..s6         (before any test)
     +0x24..+0x38  s5 := the shadow byte address of a0: the shadow base through the .got cell 0xa19d0
                   (LA_GOT_SHADOW -> LA_SHADOW_CELL 0xaa438 -> the base), plus a0 >> 3; s0 := a0, s1 := a1
     +0x3c..+0x44, +0xf8..+0x104  the instrumented check of the 4-byte load of m->n: shadow byte s of a0;
                   s = 0 passes; else (a0 & 7) + 3 < s passes; else errpath_load4 (0x5a45c)
     +0x48  lw s4, 0(s0) = m->n (MK_N = 0);  +0x4c s3 := s0 + 4 (MK_NAME)
     +0x50  blez s4 -> +0xa8                                     (no name kept yet: go to the append)
     +0x5c..+0x74  the loop over the kept names: wrapper_strcmp(m->name[i], ifname) (0x4304c); a hit (+0x68
                   beqz a0) leaves at once through the epilogue; else i := i + 1, the slot pointer += 16
     +0x78..+0x7c  addi a0, zero, 0x1f; bge a0, s4 -> +0xa8      (n <= 31: append; n = 32: return unchanged)
     +0x80..+0xa4  restore, pop, ret
     +0xa8..+0xac, +0x10c..+0x118  the instrumented check of the 4-byte store of m->n (the same shadow byte s5):
                   s = 0 passes; else (a0 & 7) + 3 < s passes; else errpath_store4 (0x5a77c)
     +0xb0..+0xc4  a3 := n + 1; a0 := m + 4 + 16 * n (the next slot); a2 := 0x21680 (".str.37" = "%s");
                   a1 := 16
     +0xc8  sw a3, 0(s0)                                         (m->n := n + 1, BEFORE the slot is written)
     +0xcc  a3 := ifname;  +0xd0..+0xf0 restore, pop (sp back to the entry sp)
     +0xf4  j wrapper_snprintf (0x43088)                         (TAIL call: snprintf(slot, 16, "%s", ifname))
   That is link_spec's `remember` (link_spec.v:411-413): a hit leaves the list alone; a miss with fewer than
   MARKS_MAX = 32 names appends `firstn 15 nm` (snprintf stores 15 bytes and a NUL into the 16-byte slot).

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame stores +0x04..+0x20 (inside [sp - K, sp)); each wrapper call
     takes ecall_pre-style premises that the walk derives from the journal (no journal lift of the strcmp or
     snprintf wrappers exists yet; pcap's aj_strcmp_at, A/Prog/PcapFuzzFopen.v:109-125, is the model); +0xa4 ret,
     and the tail jump at +0xf4, which returns to this function's own ra.
   - K = 64 + 2 * ESTACK = 8256: the 64-byte frame (no realignment: there is no `andi sp, sp, -0x20`), then the deepest
     callee window on the covered path. wrapper_strcmp is called at sp - 64 and states a 2 * ESTACK window (pcap
     Reusable/AStrcmpDef.v `astrcmp_realizes`; the ESTACK form of A/Rt/StrcmpDef.v is pcap's own literal instance
     only), so 64 + 8192. The snprintf tail jump happens with sp back at the entry sp (+0xf0 `addi sp, sp, 0x40`),
     and its window is 2 * ESTACK = 8192 below THAT sp (boxreg A/Rt/SnprintfDef.v `asnprintf_realizes`),
     which is inside [sp - 8256, sp). So K = 8256, an upper bound for the tail call as link-a/form/FORM.md
     (internal record, sha256 13aeff774164) section 5 says. The plain K (6400) does not carry over.
   - `0 < aarg regs 0`, `amarks_at m (aarg regs 0) gbs`, `marks_wf gbs`: +0x48 reads m->n; the loop reads the
     slots; `marks_wf` bounds n by MARKS_MAX and makes every slot a C string inside its 16 bytes, which is what
     lets `mk_names` read it and what makes each wrapper_strcmp stop inside the block.
   - the block's shadow and place (`range_addressable`, `shadow_hull_vis` over [a0, a0 + MK_SIZE),
     `amem_range (a0) (MK_SIZE + 8)`, `apart_frame regs K a0 MK_SIZE`, and the 8 bytes after the block visible):
     the two instrumented checks at +0x3c and +0xa8 (the 4 bytes at a0), every wrapper_strcmp's check of its
     first string, and snprintf's check of its 16-byte destination. The 8 visible bytes after MK_SIZE are the
     block's chunk tail (AR keeps it visible, boxreg SnprintfDef.v `asn_blk_tail_vis`): the last slot's NUL at
     a0 + 515 has its 8-byte word ending at a0 + 519.
   - THE DESTINATION OF snprintf. The contract at the wrapper (lib/A/Rt/LinkSnpDef.v
     `asnprintf_link_realizes`) asks of d = a0 + 4 + 16 n and w <= 16: the
     bytes writable and outside the window (the write set's `ajw`, `amarks_at`'s writability and
     `apart_frame`), in memory, addressable with the hull visible (`amarks_blk_ok`), not the runtime's
     (`~ aowned`), placed by `link_snp_place d w` (LinkSnpDef.v:179-180:
     above the image, the span between the stack-guard .got word and the guard, or the low arm
     `d + w <= IMG_LO`) and apart from the runtime cells `link_snp_rt_cells` (all inside the image [0x10000,
     0x654000); `link_snp_rt_cells_of_off`, LinkSnpDef.v:283).
     `amarks_ledger bl a0` gives the last three: `In (a0, MK_SIZE) bl` over the block list `aleaf_fx` hands the
     Pre (AR's block law then gives `~ aowned`), and `YCbq.off_img a0 MK_SIZE` (the block below the image's
     first page or above its top). The second is stated because no other premise places the block, and it is
     what the allocator gives: AR's block law (YG0d.v:430-436) puts every ledger block off the image, as
     LinkPaLib.v `blk_off_imgP` states it (`off_img p (req_size n)`, which implies the MK_SIZE form). An
     earlier text asked `IMG_TOP <= a0` alone, which AR does not give, so it could not be met at mark_quietly's
     sites 0x831f8 / 0x8347c (slot open item W7(b)).
   - the name: `aarg regs 1 <> 0`, `acstr_at m (aarg regs 1) nm`, `astr_rt_ok` at this K (wrapper_strcmp's second
     string and snprintf's `%s` argument: the span addressable, the shadow hull visible, the 8-byte band in
     memory, the rest of the NUL's word visible, the string outside the callee windows), and
     `apart (aarg regs 1) (|nm| + 8) (aarg regs 0) MK_SIZE` (snprintf asks its argument and its destination
     apart, boxreg SnprintfDef.v; the name is read after the slot is written).
   - `(length nm <= 15)%nat`: carried from the plain contract. Every call site passes a name of at most 15 bytes
     (reac_served_mark 0x89b1c and 0x89b70 pass their own a1, which the slot's callers take from name_of: a
     g_names entry, at most "nl63", or an `odd` entry, at most 11 bytes). It is what makes the Post's
     `remember` list hold the name itself and not a cut of it.
   - the format "%s": `acstr_at m LA_FMT_S S_FMT_S` and `astr_rt_ok` for it (+0xc0 forms 0x21680; the printf
     layer reads the format bytes and their shadow). Its two address bounds (0x10000 <= f and f + 3 below the
     .got cell of the stack guard 0xa2658) are closed facts of the constant and need no premise.
   - the write set [a0, a0 + MK_SIZE) and apre's `ajw` on it: the store +0xc8 (m->n) and snprintf's 16 bytes.
     The plain write set is the same block. The clause of `ajw` that grants it is `in_tmp_block`: the marks
     block is the calloc(1, 516) of LLVMFuzzerTestOneInput 0x82c84, a block allocated since the caller's
     journal began. `aivl` guards the NULL case (the plain L7 rule), although the Pre already gives 0 < a0.
   - the read set Rd (`aleaf_rd`): the name and its NUL. Every other byte this function reads is either in its
     write set (the block) or an image byte (the format), which `akb` keeps. The rest of the NUL's 8-byte word,
     which musl's word loop under strnlen reads, is covered by the Pre's visibility conjunct; it is not in Rd
     because this function reaches no allocator, so nothing can hand those bytes out during the call.
   EV = 0 (no allocator event: the printf layer below snprintf makes none), SIDE = [] (no frame_alloc).

   What does NOT carry over from the plain text:
   - the plain `leaf_fp` shape, with the printf floor `A_IMG_TOP <= lo` and the stack-protector words
     (A_GOT_GUARD, A_GUARD): on image A the floating-point freedom and the guard words belong to the wrapper's
     own contract, and the journal gives the stack.
   - `pf_img_free (arg regs 0) MK_SIZE` (the destination outside the image's reserved segments): its image-A
     form is `amarks_ledger` (above), which puts the block off the image.
   - the plain `apart_frame regs 6400 ...`: the window is now [sp - 8256, sp).
   Nothing of the plain Post is false of image A.
   Released proofs (rule 24): none of remember (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038)).
   THE FLOATING-POINT STATE is `aleaf_fx`'s. Entry: the shape takes `YK0o.frm_zero (fp_csr fx)`, which the
   released snprintf contract asks (boxreg A/Rt/SnprintfDef.v, its last premise) and the plain mark_quietly
   states (lib/Prog/mark_quietly_c.v:151); it holds at every call site, because the start-up fcsr is 0
   (`fp_frm_zero_fx0`, Reusable/YK0o.v:15) and none of the 36 listings of link's own functions holds an f* or
   csr* instruction (checked over link-a/listings/*.fuzz_link.asan.s (36 internal records, the sha256 of each in the
   records MANIFEST)). Exit: `apostF` returns at some fx' with `BoxBase.fxr fx fx'` (every f register but f10 kept, the
   fcsr kept or its rounding mode 0), which is what the snprintf tail call leaves (the printf family's shared post).
   THE BLOCK LIST the shape hands the Pre carries the marks block's ledger fact (`amarks_ledger`, above).
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem model_decide_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition REMEMBER_A : Z := 0x89db4.
(* the marks block is a block of the allocator's ledger (bl is the call's `ablocks B lyc Sc`, which `aleaf_fx`
   hands the Pre) and lies off the image (YCbq.v `off_img`: below the image's first page or above its top), as
   AR's block law places every ledger block: snprintf's destination placement and its separation from the
   runtime cells. Shared with reac_served_mark_c.v and mark_quietly_c.v. *)
Definition amarks_ledger (bl : list (Z * Z)) (p : Z) : Prop :=
  In (p, MK_SIZE) bl /\ YCbq.off_img p MK_SIZE.

Lemma REMEMBER_A_is_entry : REMEMBER_A = LA_remember. Proof. reflexivity. Qed.

(* the format literal of the slot write (listing +0xc0; .str.37, a registered 32-byte global) and its bytes *)
Definition LA_FMT_S : Z := 0x21680.
Definition S_FMT_S : list byte := map (Z_to_bv 8) [37; 115].

(* the runtime entries this function calls (listing +0x64, +0xf4) *)
Definition LA_wrapper_snprintf : Z := 0x43088.

(* the stack bound on image A: the 64-byte frame and the strcmp wrapper's 2 * ESTACK window *)
Definition REMEMBER_AFRAME : Z := 64.
Definition REMEMBER_AK : Z := REMEMBER_AFRAME + 2 * ESTACK.
Lemma REMEMBER_AK_val : REMEMBER_AK = 8256. Proof. reflexivity. Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

(* What the marks block at p must satisfy for the loop's wrapper_strcmp calls, for the two instrumented checks of
   m->n and for snprintf's destination, inside a function whose stack bound is K. Shared with
   reac_served_mark_c.v and mark_quietly_c.v, which pass the same block on to this function. *)
Definition amarks_blk_ok (regs : bvmap 5 word) (K : Z) (m : word -> option byte) (p : Z) : Prop :=
  0 < p /\ amem_range p (MK_SIZE + 8)
  /\ range_addressable (ard segs m) SHADOW_OFF p MK_SIZE
  /\ shadow_hull_vis (ard segs m) p MK_SIZE
  /\ (forall b, p + MK_SIZE <= b < p + MK_SIZE + 8 -> ard segs m b <> None)
  /\ apart_frame regs K p MK_SIZE.

Definition remember_apre (bl : list (Z * Z)) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists gbs nm,
    amarks_at segs m (aarg regs 0) gbs /\ marks_wf gbs
    /\ amarks_ledger bl (aarg regs 0)
    /\ amarks_blk_ok regs REMEMBER_AK m (aarg regs 0)
    /\ aarg regs 1 <> 0 /\ acstr_at segs m (aarg regs 1) nm /\ (length nm <= 15)%nat
    /\ astr_rt_ok segs regs REMEMBER_AK m (aarg regs 1) nm
    /\ apart (aarg regs 1) (Z.of_nat (length nm) + 8) (aarg regs 0) MK_SIZE
    /\ acstr_at segs m LA_FMT_S S_FMT_S
    /\ astr_rt_ok segs regs REMEMBER_AK m LA_FMT_S S_FMT_S.

(* the read set: the name and its NUL *)
Definition remember_ard (regs : bvmap 5 word) (m : word -> option byte) (a : Z) : Prop :=
  astr_rd segs m (aarg regs 1) a.

(* the write set: the marks block (the count word and the one slot snprintf fills) *)
Definition remember_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [aivl (aarg regs 0) MK_SIZE].

Definition remember_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  forall gbs nm, amarks_at segs m (aarg regs 0) gbs -> acstr_at segs m (aarg regs 1) nm ->
    exists gbs', amarks_at segs m' (aarg regs 0) gbs' /\ marks_wf gbs'
      /\ mk_names gbs' = remember (mk_names gbs) nm
      /\ mk_n gbs' = Z.of_nat (length (remember (mk_names gbs) nm)).

Definition remember_acontract : Prop :=
  aleaf_fx SK segs rlo rhi B REMEMBER_A REMEMBER_AK 0 []
    remember_apre remember_ard remember_awr remember_apost.

End c.
