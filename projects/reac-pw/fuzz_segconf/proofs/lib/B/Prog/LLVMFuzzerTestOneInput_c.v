(* reac-pw/fuzz_segconf, ASan builds: the contract of the test harness's entry function LLVMFuzzerTestOneInput
   (fuzz_segconf.c:579-673, with fuzz.h inlined). Statement text only: no function of the binary is proved here.

   DRAFT v0 by the harness walk owner (G1) for the image-A owner (the owner of segconf image A's contracts), who
   reviews it and commits it into its contracts branch; from then on it is the image-A owner's text.

   THE FORM. plugin-hostd/fuzz_command's lib/A/Prog/LLVMFuzzerTestOneInput_c.v:84-239 at origin/ossv/recipes
   501c0d516c69 (tLLVMFuzzerTestOneInput_spec): afn_pre at the entry, SRr of apost_baseF at the return. The pre is
   tfib_lib_pre_x's (fuzz_command lib/A/ACfn.v:41-63) conjunct for conjunct, and the post gives what
   tfib_lib_post_x (ACfn.v:64-78) asks of the function, in the same words, so the close's bridge is fuzz_command's
   lib/A/Prog/CmdLibX.v cmd_lib_x with segconf's names (a lemma, no rewrite). The only premises beyond
   tfib_lib_pre_x are image facts (the read-only constants and literals the function and its callees read, the
   box-model table, longl, the stack-protector cells) and the meter / event / live bounds, as in fuzz_command's
   text, which its close discharges from the image (CmdLibX.v:101-127).

   IMAGE-INDEPENDENT: no image module is Required. Every image number is a parameter (A_LLVMF, STK, EMPTY, RLO,
   RHI, LONGL, MOD40, CAT, WORDS, ROLES, GOTW, GUARD, and lit_fz / lit_rc : list Z -> Z from a literal's text to its
   address in
   fuzz_segconf.c's and in reac_segconf.c's module, as SegABase.sa_lit asks), instantiated by each image's walk
   and close. Image A's values, measured on the pin
   fuzz_segconf.asan 48c5355bdacb (twin 4362701197e4): A_LLVMF 0x84d34; LONGL 0x5de680 (the 121-byte .bss object
   `LLVMFuzzerTestOneInput.longl`, 160 bytes with its guard bytes); MOD40 0x103c8 (the 8-byte multiplier
   0x0666666666666667 that cap = u8 % 40 loads at 0x84ed4 / 0x84ed8 with no instrumented check); the literals
   lit_fz (sb "reac-pw.conf.d/%u-x.conf") = 0x20fe0, lit_fz (sb "%sx") = 0x21020, lit_fz (sb "nosuch0") = 0x21040,
   lit_fz (sb "enp1s0") = 0x21060 (registered globals of fuzz_segconf.c, PREMISES-A section 1.4); CAT 0xa18e0
   (fuzz_catalogue, RELRO); RLO / RHI = .data.rel.ro start 0xa14a0 / .got end 0xa3748 (PREMISES-A section 1.3).

   WHAT THE FUNCTION DOES (fuzz_segconf.c:579-673; image A 0x84d34, 1,122 instructions, frame 320 bytes realigned
   to 32, 36 instrumented checks, 11 abort sites of which 1 is its own). It takes a side-stack frame of class 3
   (288 bytes: v at 32, label[40] at 96, r at 176, probe[18] at 192, n at 256; the frame description at image A
   0x1ba5a) when the flag cell is non-zero, else the same 288 bytes on the real stack. It reads cap, flags and
   nfiles from the payload, allocates c = malloc(16616) and m = calloc(1, 9236), runs nfiles <= 4 file turns (each
   allocates text = malloc(n + 1), n <= 65535, and frees it), calls the reader and the model and the ten checks,
   allocates tab = calloc(cap + 1, 18) and mt = calloc(cap + 1, 20) (cap <= 39), runs the declared-VLAN part, and
   frees mt, tab, m, c. Allocator events: 2 + 2 * nfiles + 2 + 4 = 8 + 2 * nfiles (each calloc one event, as the
   calloc rule charges one malloc; to be confirmed against YGCalloc.acalloc_realizes_cgif by the walk). Live bytes
   above the entry's blocks: at most 16616 + 9236 + 65536 = 91,388 (in the file loop). It writes no image byte but
   longl[0 .. 120) (memset(longl, 'L', 120) when the label byte has bit 7), and never longl[120], which every
   reader of the label needs as its NUL: hence the global invariant ltoi_GI, as the plain / UBSan owner's GI_SLOT
   (lib/Prog/SlotFR.v:38-43). ltoi_PG and ltoi_GI are convertible to the listing's image-A SegGlob.seg_PG and
   SegGlob.GI_segA (commit 53e3728a30bd) at LONGL := SegGlob.A_LONGL, so the close needs no
   lemma for them; the names differ so that a walk can import both files.

   WHAT IT PROMISES. From afn_pre at A_LLVMF with the payload in a live block (or the empty object), it returns to
   ra with a0 = 0, every callee-saved register as at the entry, the live blocks those of the entry, the payload's
   bytes unchanged, longl[120] still 0, the meter and live bytes bounded, at an FP state whose fcsr has rounding
   mode 0 or is the entry's (apost_baseF). On the way none of the 11 abort sites is reached and no instrumented
   check reaches its error path; that is the content of the walk (the callees' posts and SegModel's
   harness_ok), not a premise.

   PENDING in this draft (named so nobody reads it as done):
   - LTOI_FZ_LITS / LTOI_RC_LITS hold the harness's own literals and every callee's <F>_LITS by module (the
     image-A owner's G5 check_knock_refused, G2 m_refuse, m_file - the G2 walk lane's text of record, taken in
     at intake -, G3 reac_segconf_parse_file and cross_check, whose list holds refuse's).
   - The callees' image premises beyond literals are in seg_himg: the box-model table (sa_cat), m_key.words and
     m_key.role (WORDS, ROLES; m_file_c.mf_words / mf_roles, added with m_file's intake), and the stack-protector
     cells. A later callee premise of that kind is appended here.
   - The T0.6 witness (this pre satisfiable at segconf's own entry state) waits on the start-up state
     (the image-A owner's start-up lane). *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Prog/LLVMFuzzerTestOneInput_c.v, derived mechanically (bkit derive_b.py): its Require lines name the lib/B copies; nothing else differs. The comments are the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require check_knock_refused_c m_refuse_c m_file_c
reac_segconf_parse_file_c cross_check_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ===================================== image-independent constants ===================================== *)
(* the multiplier cap = u8 % 40 loads: ceil(2 ^ 64 / 40), so mulhu(u8, M) * 40 is the multiple of 40 below u8 *)
Definition LTOI_MOD40 : Z := 0x0666666666666667.
(* the bytes of longl the function may write ([LONGL, LONGL + 120)) and the byte it keeps as the NUL *)
Definition LONGL_W : Z := 120.
Definition LONGL_N : Z := 121.
(* the literals the function itself passes to a callee or an interceptor: the label format (snprintf, c:608), the
   probe format (snprintf, c:640), the name no section opens (m_find and check_absent, c:645-646), the VLAN seed
   (memcpy, c:657 / c:659, snprintf folded to a 7-byte copy) *)
Definition LIT_LABEL : list Z := SegModel.sb "reac-pw.conf.d/%u-x.conf"%string.
Definition LIT_PROBE : list Z := SegModel.sb "%sx"%string.
Definition LIT_NOSUCH : list Z := SegModel.sb "nosuch0"%string.
Definition LIT_ENP : list Z := SegModel.sb "enp1s0"%string.
Definition LTOI_LITS : list (list Z) := [LIT_LABEL; LIT_PROBE; LIT_NOSUCH; LIT_ENP].

(* the program's writable statics: longl only (the plain / UBSan owner's frame_G, lib/FrameAPI.v:14) *)
Definition ltoi_PG (LONGL : Z) : list (Z * Z) := [(LONGL, LONGL + LONGL_N)].
(* the global invariant at call j: longl[120] is 0 (plain GI_SLOT, lib/Prog/SlotFR.v:41-43, over the reader); the
   body is SegGlob.zero_atA's at (LONGL + 120, 1) *)
Definition ltoi_GI (LONGL : Z) (j : nat) (rd : reader) : Prop :=
forall i, 0 <= i < 1 -> rd (LONGL + LONGL_W + i) = Some 0.

(* the allocator events of one call: malloc(c), calloc(m), malloc(text) and free(text) per file turn, calloc(tab),
   calloc(mt), free(mt), free(tab), free(m), free(c); the 33 callees spend none (the image-A contracts, EV_<F> = 0) *)
Definition EV_LTOI (pl : list byte) : Z := 8 + 2 * seg_spec.seg_nfiles pl.
(* the bytes live at once above the entry's blocks: c, m and the largest text block (n + 1 <= 65536) *)
Definition LIVE_LTOI : Z := 16616 + 9236 + 65536.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation rdW W mem := (aview segs (w_H W) mem).

(* the meter: every allocator event charged the cost of the largest allocation (a text block of 65,536 bytes;
   c is 16,616, m 9,236, tab and mt at most 800) and of a free, as fuzz_command's XM_LTOI *)
Definition XM_LTOI (pl : list byte) : Z := EV_LTOI pl * (mo_malloc MT 65536 + mo_free MT).

(* The literals the function and its callees read, split by translation unit. 18 texts exist TWICE in the image,
   one global per module (measured by the close lane in the pin 48c5355bdacb: "%s:%d: " at 0x210c0 in fuzz_segconf.c
   and 0x21aa0 in reac_segconf.c, "%s" 0x21080 / 0x21340, "reac-pw.conf" 0x210a0 / 0x21360, "%s: " 0x210e0 /
   0x21ac0, and the words segment, role, auto, master, slave, tap, box, model, ignore, yes, true, no, false, knock
   at 0x21100..0x212e0 against 0x214a0..0x21be0), so one map from a text to its address cannot serve both
   m_refuse (fuzz_segconf.c's copy) and refuse (reac_segconf.c's). The harness therefore takes two maps, lit_fz
   and lit_rc (each image's instance gives its own, SegInstA's seg_litA_fz / seg_litA_rc for image A), and every
   callee keeps its own single `lit` parameter, which the harness's walk instantiates with the map of that
   callee's module (the image-A owner's decision, 2026-10-30).
   fuzz_segconf.c, over lit_fz: the harness's own LTOI_LITS, check_knock_refused's, m_refuse's (m_file's are
   appended when the G2 walk lane's m_file_c.v lands).
   reac_segconf.c, over lit_rc: reac_segconf_parse_file's and cross_check's (cross_check's list contains
   refuse's; reac_segconf_parse takes cross_check's and parse_file's). *)
Definition LTOI_FZ_LITS : list (list Z) :=
LTOI_LITS ++ check_knock_refused_c.check_knock_refused_LITS ++ m_refuse_c.M_REFUSE_LITS ++ m_file_c.M_FILE_LITS.
Definition LTOI_RC_LITS : list (list Z) :=
reac_segconf_parse_file_c.PARSE_FILE_LITS ++ cross_check_c.CROSS_CHECK_LITS.
(* the image facts the function and its callees read *)
Definition seg_himg (LONGL MOD40 CAT WORDS ROLES GOTW GUARD : Z) (lit_fz lit_rc : list Z -> Z) (rd : reader)
: Prop :=
(* the multiplier of cap % 40 *)
sa_val rd MOD40 8 LTOI_MOD40 /\ sa_img segs B MOD40 8 /\
(* each literal: its bytes, NUL and slack, addressable, an image object, apart from longl; by module *)
(forall s, In s LTOI_FZ_LITS -> sa_lit segs B rd (lit_fz s) s /\
   sa_apart_all (lit_fz s) (Z.of_nat (length s) + 1) (ltoi_PG LONGL)) /\
(forall s, In s LTOI_RC_LITS -> sa_lit segs B rd (lit_rc s) s /\
   sa_apart_all (lit_rc s) (Z.of_nat (length s) + 1) (ltoi_PG LONGL)) /\
(* the box-model table m_file and reac_segconf_parse_file read, apart from longl *)
sa_cat segs B rd CAT /\ sa_apart_all CAT pin_spec.CAT_BYTES (ltoi_PG LONGL) /\
(* m_key.words and m_key.role, which m_file reads (both its calls, 0x851ac and 0x85204, pass them through its
   contract's WORDS / ROLES), each pinned at every allocator state (m_file_c.mf_words / mf_roles) *)
m_file_c.mf_words segs B rd WORDS /\ m_file_c.mf_roles segs B rd ROLES /\
(* the stack-protector cells musl's printf_core / strstr / strspn / strtol read in the callees *)
sa_ssp rd GOTW GUARD /\
(* longl: addressable at EVERY allocator state (its 121 bytes; the 39 guard bytes after it are not), its slack
   after the NUL at LONGL + LONGL_W mapped as an image byte, an image byte the runtime does not own, and not the
   stack-protector cells. PINNED, not an entry-state sa_addr (found by the plain / UBSan owner's review, 2026-10-30):
   longl is the label reac_segconf_parse_file reads, and side-stack frames are taken before it is read (this function's
   own class-3 frame, m_file's class 1, parse_file's class 5), across which the kit keeps no image shadow
   (SegABase.v, the comment on sa_pinned). Its tail is stated as sa_romtail, the form that is easier to
   discharge: a computation over segs alone (the rw .bss segment is in segs, and seg_rom reads it: LPS
   RiscvSemantics.v:397-405), with no AR argument, whereas sa_pinned_tail would need AR to keep an owned .bss byte
   mapped at every state. parse_file's and m_file's label premise asks sa_pinned_tail; the walk gives it from
   this conjunct by SegABase.sa_pinned_tail_of_romtail. *)
sa_pinned segs B LONGL LONGL_N /\ sa_romtail segs (LONGL + LONGL_W) /\ sa_img segs B LONGL LONGL_N /\
sa_disj GOTW 8 LONGL LONGL_N /\ sa_disj GUARD 8 LONGL LONGL_N /\ sa_disj MOD40 8 LONGL LONGL_N.

Definition LLVMFuzzerTestOneInput_contract (A_LLVMF STK EMPTY RLO RHI LONGL MOD40 CAT WORDS ROLES GOTW GUARD : Z)
(lit_fz lit_rc : list Z -> Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (p n : Z) (pl : list byte) (j : nat),
afn_pre segs B STK ly S W regs mem md ch ->
(* the machine stack from the entry sp to its top is present (tfib_lib_pre_x's astack_pres) *)
astack_pres ly (w_H W) mem (spZ regs) ->
(* rounding mode 0, which the printf wrappers the callees reach need (tfib_lib_pre_x's frm clause) *)
sa_frm0 ->
arodata_okP segs RLO RHI B (rdW W mem) ->
seg_himg LONGL MOD40 CAT WORDS ROLES GOTW GUARD lit_fz lit_rc (rdW W mem) ->
(* the driver's arguments (tfib_lib_pre_x): the payload in a live block, or the empty object when it has no
   byte, and its bytes *)
getr regs 10 = w64 p -> getr regs 11 = w64 n ->
((n = 0 /\ p = EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) ->
n = Z.of_nat (length pl) ->
garr8 segs (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) pl) ->
frames S = [] ->
ltoi_GI LONGL j (rdW W mem) ->
st_nev S + EV_LTOI pl <= EV_MAX -> blocks_bytes S + LIVE_LTOI <= LIVE_MAX ->
mo_ok MT S (XM_LTOI pl) ->
SRr segs W (cfg_at segs A_LLVMF regs mem md)
(apost_baseF segs B STK (ltoi_PG LONGL) regs ly S W mem md (EV_LTOI pl)
(fun ly' S' W' regs' mem' md' =>
 (* it returns 0 *)
 getr regs' 10 = w64 0 /\
 (* every block it allocated is freed: the live blocks are the entry's *)
 Permutation (ablocks B ly' S') (ablocks B ly S) /\
 (* the payload's bytes are unchanged *)
 (forall i, 0 <= i < n -> rdW W' mem' (p + i) = rdW W mem (p + i)) /\
 (* the global invariant for the next call *)
 ltoi_GI LONGL (Datatypes.S j) (rdW W' mem') /\
 (* the meter and the live bytes, chained by a caller *)
 mo_le MT S S' (XM_LTOI pl) /\ blocks_bytes S' <= blocks_bytes S + LIVE_LTOI)).
End d.
End c.
End b.
