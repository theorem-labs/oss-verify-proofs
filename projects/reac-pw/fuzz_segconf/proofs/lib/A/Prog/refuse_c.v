(* refuse (reac_segconf.c:30-48, static, variadic; fuzz_segconf.asan 0x88da4, 772 bytes, 193 instructions; frame
   160 bytes, side-stack frame class 0): the contract of the ASan build's code, in plugin-hostd/fuzz_command's
   lib/A/Prog form (afn_pre at the entry, SRr of apost_baseF at the return: it reaches the printf wrappers).
   Functional content: the plain contract lib/Prog/refuse_c.v:12-69 (refuse_pre :38-48, refuse_W :50-56,
   the contract :58-69), restated over the ASan reader.
   What the code does (objdump of fuzz_segconf.asan, 0x88da4-0x890a4): the variadic a3 .. a7 spilled to the real
   stack (0x88e04-0x88e1c, above s0 = entry sp - 48); the class-0 side-stack frame (`__asan_stack_malloc_0` at
   0x88e30, a0 = 0x40; object description `1 32 8 5 ap:43` at .rodata 0x1b009: the va_list ap at frame offset 32);
   c->refused++ (lw / sw of c + 0x34cc, 0x88ed8 / 0x88ee4); n_refusals >= 8 (`blt 7, n`, 0x88efc) returns; else
   dst = c + 0x2e88 + 200 n, where = c->reading[0] ? c->reading : "reac-pw.conf" (lbu of c + 0x4080 at 0x88f20),
   k = snprintf(dst, 200, "%s:%d: ", where, line) for line > 0 (0x88f5c), else snprintf(dst, 200, "%s: ", where)
   (0x88f74); k > 199 as unsigned returns; else vsnprintf(dst + k, 200 - k, fmt, ap) (0x88fa4, the caller's
   va_list over the spilled registers) and n_refusals++ (0x88fb0 / 0x88fb8). The frame is released inline
   (0x88fc4-0x89000: the magic 0x45e0360e into frame[0], shadow f5, the flag byte through frame[56]); no
   __asan_stack_free call. The post is the plain one: c holds SegModel.refuse rcs ln f args.
   What it reads: the shadow base and the use-after-return flag through the GOT words as_got_shadow B (image A
   0xa2a50) and as_got_uar B (0xa2aa8), both AR constants (lib/Reusable/YG0d.v AR_const_law), so the contract names
   neither; the c block; the format fmt; the variadic arguments; three literals (REFUSE_LITS); the
   stack-protector cells musl's printf_core reads. What it writes: its frames, refused, and when n_refusals < 8 the
   slot refusal[n] and n_refusals (refuse_W, the plain write list without its stack range). No abort site
   (provenance/evidence/image-tables/program.asan.tsv line 20).
   ASAN FACTS ADDED over the plain contract:
   - inline check 1, load4 of c->refused at c + 0x34cc (0x88ec4-0x89068, error arm __asan_report_load4 at
     0x8906c; the sw of the increment shares it), check 2, load4 of c->n_refusals at c + 0x34c8 (0x88edc-0x89078,
     error arm 0x89080), check 3, load1 of c->reading[0] at c + 0x4080 (0x88f0c-0x89088, error arm
     __asan_report_load1 at 0x89090), check 4, load4 of c->n_refusals before the increment (0x88fa8-0x8909c, error
     arm 0x890a4): all inside the block, killed by refuse_pre's sa_addr rd c SEG_C_SIZE.
   - the interceptors' ranges: snprintf's and vsnprintf's destination [dst, dst + 200) in the block (the same
     sa_addr); the formats "%s:%d: " / "%s: " and the default "reac-pw.conf" by sa_lit (REFUSE_LITS); fmt by
     `fp = lit f /\ sa_lit segs B rd fp f`: the format IS one of the module's literals, at the address the literal
     map gives it. sa_lit alone does NOT carry the plain .rodata bounds (sa_img also holds above the GOT word),
     and the released vsnprintf family needs the format below the GOT word (fuzz_command lib/A/Rt/RtPFCmd.v:94-95
     FR_cmd `CMD_IMG_LO <= f /\ f + len + 1 <= CMD_GOTW`, checked by computation in its fr_lit_ok :98-100); with
     fp = lit f the walk gets a concrete address for each of the 17 formats, all below the GOT word 0xa36d8 in
     image A, and every caller passes a literal address (reac_segconf_parse_file's 11 sites, cross_check's 2).
     Found by the G3 walk lane's contract review (D1) at 9b7c1301069e; the earlier wording of this line claimed sa_lit
     carried the bounds, which was false. (ASan's printf_common reads the format: INFERENCE from
     sanitizer_common_interceptors_format.inc, not read here.) Each %s argument by sa_va_args, whose forbidden
     ranges are the plain ones: the stack below the entry sp [ly_stk_lo ly, sp) (the plain [lo, sp)), the slot
     refusal[n] and the 4 bytes of c->refused.
   - where each object lies: the block by sa_heap (malloc(0x40e8) at LLVMFuzzerTestOneInput 0x84f80); each %s
     argument by refuse_va_locs: a live heap block or a live side-stack frame. This is NEW over the plain
     contract and a choice of this lane: sa_addr alone does not keep an argument out of the side-stack frame
     refuse takes (a never-used fake-stack slot may have a zero shadow), so the walk needs the argument in a live
     object to keep its bytes across the frame's writes. The image is NOT allowed: refuse calls
     `__asan_stack_malloc_0` before printf reads an argument, and the kit's astack_malloc_realizes
     (lib/Reusable/YG0d.v:293-308) keeps only bytes outside aowned B ly S and aowned B ly S', which include the
     shadow of every image byte (aowned's lm_zone shadow, YG0n.v:236-242), so an image argument's sa_addr would
     not survive to the printf call; a live frame's bytes and shadow are client bytes (aclient_byte) and are
     kept, a live block's shadow is AR's shadow_ok at every state. Every call site meets it: parse_file passes
     buf, cur_name and known (its class-5 frame), cross_check passes s->name and s->model (the block).
   - the class-0 side-stack frame: sa_room S.
   - NO keep clause (sa_kept) in the post: the class-0 frame, its shadow and its flag byte lie outside the stack
     window and the footprint, and astack_malloc_realizes keeps nothing of aowned B ly S (every image byte's
     shadow among it), so a keep clause over image shadow is not provable; a caller re-derives it from the exit
     state's AR through the record's pinned bytes.
   - it reaches snprintf and vsnprintf: apost_baseF, sa_frm0, sa_ssp rd gotw guard.
   - arodata_okP over the window RLO .. RHI: rows 4 and 5 ask rt_rom_view (fuzz_command lib/A/Rt/RtDefs.v:145 at
     origin/ossv/recipes 501c0d516c69), which AR does not give.
   - EV_refuse = 0, post tail sa_noalloc.
   Call sites (provenance/evidence/image-tables/callsites.asan.tsv lines 236, 244, 248, 255, 260, 266, 267, 273, 274, 276, 280, 339,
   340): reac_segconf_parse_file 0x87e74, 0x88060, 0x880f8, 0x8835c, 0x8842c, 0x884e8, 0x88510, 0x886e8, 0x88794,
   0x88834, 0x889ac (c, lineno >= 1, one of the 17 formats); cross_check 0x89350 and 0x8939c (c, a1 = 0, F_xmodel
   with s->name and s->model, F_xbox with s->name).
   image A: A_refuse = 0x88da4; STK_refuse = 160 + 16 + 3 * ESTACK (INFERENCE: the frame, the `andi sp,sp,-32`
   realignment at 0x88de0, and the printf wrappers' window as fuzz_command's answer_c.v takes it); RLO = 0xa14a0,
   RHI = 0xa3748 (readelf, fuzz_command's CmdGlob.v convention); gotw = 0xa36d8 (the GOT word musl's printf_core
   loads at 0x96e44; it holds 0x5ff078, read from the pin), guard = __stack_chk_guard 0x5ff078 (nm);
   lit S_base = 0x21360 (.str.1), lit F_addr_line = 0x21aa0
   (.str.31), lit F_addr = 0x21ac0 (.str.32) (objdump 0x88f3c, 0x88f4c, 0x88f68; bytes read from the pin).
   IMAGE-INDEPENDENT: no image module is Required; A_refuse, STK_refuse, RLO, RHI, lit, gotw and guard are
   parameters.
   The WALK takes these runtime entries as Section hypotheses (the interceptor lane's interface
   provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626)):
     RtPFSeg.seg_asnprintf_realizes (row 4, over the extended piece grammar: %zu, %u, %.24s beside %s %d;
     commit 755e9278f8ff, RtPFSeg.v:228), at the snprintf trampoline (image A 0x43a64);
     RtPFSeg.seg_avsnprintf_realizes (row 5, the caller's va_list; RtPFSeg.v:232, the released route's Ua form at
     U = [], not RtPFShared.v:226's text, which no released proof provides), at the vsnprintf trampoline
     (0x43a5c); and, from the image-A owner's frame (the interface's "Not in this layer: classes 0 / 1 / 3, the
     kit laws"): astack_malloc_realizes 0 (kit YG0d.v:293; `__asan_stack_malloc_0` 0x3e57c),
     stack_malloc_progressP, astack_free_law, frame_flag_lawP.
   They are NOT premises of this contract: the statement does not mention them. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* The literals refuse itself passes (reac_segconf.c's module): the two address formats and the default where. *)
Definition REFUSE_LITS : list (list Z) := [S_base; F_addr_line; F_addr].
(* Where each %s argument lies: P q n for the bytes and the NUL of every string argument, in the order the
   format reads them (the integer arguments take a register and no place). *)
Fixpoint refuse_va_locs (P : Z -> Z -> Prop) (rs : list word) (xs : list SegModel.arg) : Prop :=
match xs, rs with
| [], _ => True
| SegModel.AS s :: xs', r :: rs' => P (bv_unsigned r) (Z.of_nat (length s) + 1) /\ refuse_va_locs P rs' xs'
| SegModel.AI _ :: xs', _ :: rs' => refuse_va_locs P rs' xs'
| _ :: _, [] => False
end.
(* The bytes outside its stack window refuse writes (the plain refuse_W, lib/Prog/refuse_c.v:51-56, without its
   first range, which is the call's own stack window here). *)
Definition refuse_W (c : Z) (rcs : rconf) : list (Z * Z) :=
[(c + seg_spec.RC_REFUSED, c + seg_spec.RC_REFUSED + 4)] ++
(if (length (rc_refusal rcs) <? 8)%nat
 then [(seg_spec.refusal_addr c (length (rc_refusal rcs)),
        seg_spec.refusal_addr c (length (rc_refusal rcs)) + seg_spec.RC_REFUSAL_LEN);
       (c + seg_spec.RC_NREF, c + seg_spec.RC_NREF + 4)]
 else []).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
(* What refuse asks of its caller (the plain refuse_pre, lib/Prog/refuse_c.v:38-48, over the reader rd =
   aview segs (w_H W) mem): c is the reader's block, a live heap block of 16616 bytes holding rcs, addressable,
   with room in the u32 c->refused; line is ln, non-negative and below 2 ^ 31; f is one of the 17 formats and the
   arguments have its kinds; fp is f as a literal of the image; the variadic registers va hold the arguments
   (sa_va_args, apart from the stack below sp, the slot and c->refused) and each string lies in a live heap block
   or a live side-stack frame;
   printf's machine (the rounding mode and the stack-protector cells); refuse's own literals. The plain
   stack_ok / apart / blk_noimg / mem_inv conjuncts are afn_pre's, sa_heap's and sa_lit's here.
   Outside the sections: refuse_pre segs B lit gotw guard ly S regs rd c line fp va rcs ln f args. *)
Definition refuse_pre (lit : list Z -> Z) (gotw guard : Z) (ly : alayout) (S : astate) (regs : bvmap 5 word)
(rd : reader) (c line fp : Z) (va : list word) (rcs : rconf) (ln : Z) (f : list Z) (args : list SegModel.arg)
: Prop :=
c <> 0 /\ c mod 16 = 0 /\ sa_rconf rd c rcs /\ sa_heap B ly S c seg_spec.SEG_C_SIZE /\
sa_addr rd c seg_spec.SEG_C_SIZE /\
rc_refused rcs + 1 < 2 ^ 32 /\
0 <= ln < 2 ^ 31 /\ line = ln /\
In f seg_spec.REFUSE_FORMATS /\ seg_spec.conv_kinds f = map seg_spec.arg_is_s args /\
fp <> 0 /\ fp = lit f /\ sa_lit segs B rd fp f /\
sa_va_args rd
  [(ly_stk_lo ly, spZ regs);
   (seg_spec.refusal_addr c (length (rc_refusal rcs)),
    seg_spec.refusal_addr c (length (rc_refusal rcs)) + seg_spec.RC_REFUSAL_LEN);
   (c + seg_spec.RC_REFUSED, c + seg_spec.RC_REFUSED + 4)] va args /\
refuse_va_locs (fun q n => sa_heap B ly S q n \/ sa_fframe ly S q n) va args /\
sa_frm0 /\ sa_ssp rd gotw guard /\
(forall x, In x REFUSE_LITS -> sa_lit segs B rd (lit x) x).
(* the events this call spends: 0, it reaches no allocator entry *)
Definition EV_refuse : Z := 0.
Definition refuse_contract (A_refuse STK_refuse RLO RHI : Z) (lit : list Z -> Z) (gotw guard : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c line fp ln : Z) (rcs : rconf) (f : list Z)
  (args : list SegModel.arg),
afn_pre segs B STK_refuse ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 c -> 0 <= c < 2 ^ 64 -> getr regs 11 = w64 line -> 0 <= line < 2 ^ 64 ->
getr regs 12 = w64 fp -> 0 <= fp < 2 ^ 64 ->
refuse_pre lit gotw guard ly S regs (aview segs (w_H W) mem) c line fp
  [getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17] rcs ln f args ->
(* room for refuse's class-0 side-stack frame *)
sa_room S ->
st_nev S + EV_refuse <= EV_MAX ->
SRr segs W (cfg_at segs A_refuse regs mem md)
(apost_baseF segs B STK_refuse (refuse_W c rcs) regs ly S W mem md EV_refuse
(fun ly' S' W' regs' mem' md' =>
 sa_rconf (aview segs (w_H W') mem') c (SegModel.refuse rcs ln f args) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
