(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from projects/libreac/fuzz_grant/proofs/lib/A/Prog/CtrlParseCut.v. *)
(* reac_ctrl_parse (fuzz_scene.asan-ubsan 0x84028, 673 instructions): the contract of the ASan+UBSan build's code,
   in the caller-journal form (it writes the caller's 36-byte `struct reac_ctrl_parsed`). The return code and the
   36 bytes it writes are Pau's model `ctrlparse` (lib/Prog/RcParse.v:45). Statement only; the walk is ported later.
   The asan-ubsan twin of lib/A/Prog/P_reac_ctrl_parse.v. Ported from a Theorem Labs lane's
   proofs/libreac/fuzz_grant/lib/A/Prog/CtrlParseCut.v (at 9fb598002a1, lines 283-317): the listing
   modules are lib.AU.Prog's and their names changed; the core modules are lib.Reusable's except the image-specific
   YCbq, which is lib.AU's (MERGE-GATES.md 6o); the text of A_ctrl_parseP, TPARSE_STK, tctrl_parse_post and
   tctrl_parse_spec is the donor's. The UBSan checks need no premise the donor's statement does not have (below).
   Numbers: fuzz_scene.asan-ubsan, sha256 e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f
   (projects/libreac/fuzz_scene/harness.yaml at c8557374ad2e); symbols and DWARF lines from
   unstripped/fuzz_scene/fuzz_scene.asan-ubsan, whose bytes at 0x84028..0x84aac equal the pinned image's.
   - reac_ctrl_parse = 0x84028, st_size 2692 = 673 instructions (no compressed instruction).
   - LLVMFuzzerTestOneInput = 0x828a4 = the listing's base (SceneAddr.v:16 scene_text), so
     AF_reac_ctrl_parse = 0x84028 - 0x828a4 = 0x1784 (SceneList.v:22; slots SceneList.v:1531-2203).
   - the arguments: a0 = f (mv s5,a0 @0x8408c), a1 = n (mv s6,a1 @0x84070), a2 = o (mv s4,a2 @0x8406c).
   - f, 50 bytes: li a0,50 @0x84168; bltu s6,a0 @0x8416c rejects n < 50; it reads f[0..23) and f[32..39) (the two
     memcpys f[0..12), the bcmp f[0..6), checked byte loads f[12..23) and f[32..39), 0x84190..0x847b4).
   - o, 36 bytes: li a2,36 @0x84158; jal __asan_memset (0x53e8c) @0x84164 clears o[0..36) (o, or the local scratch
     when o = 0: beqz s4 @0x84150); __asan_memcpy (0x539f0) o+10 <- f[0..6) @0x841e4, o+4 <- f[6..12) @0x84208;
     the field stores, each after its shadow check, end at o+33 (sw o+0, sw o+16, sh o+20, sb o+22, sb o+23,
     sh o+24, sb o+26, sh o+28, sb o+30, sb o+31, sb o+32; 0x8423c..0x847bc).
   - TPARSE_STK: addi sp,sp,-128 @0x84028 and andi sp,sp,-32 @0x84064 give sp1 = 32 * ((sp - 128) / 32) >= sp - 144
     (sp mod 16 = 0). The fake frame is class 1 (li a0,128 @0x84094; jal __asan_stack_malloc_1 (0x3f10c) @0x84098);
     on that path every call runs at sp1. (The real-stack fallback 0x840b0..0x840c8, taken when the flag read at
     0x84084 is 0 or the call returns 0, does not happen in the model: the flag cell holds 1 and
     stack_malloc_progressP gives a class-1 frame under `length (frames Sc) <= 8`.) The deepest callee window is
     the bcmp wrapper's 2 * ESTACK (abcmp_realizes): jal __interceptor_trampoline_bcmp (0x44338) @0x84220;
     __asan_memset, __asan_memcpy and __asan_stack_malloc_1 take ESTACK, kind_of_link1 (0x84aac, jal @0x845b8)
     takes KIND_OF_LINK1_STK = ESTACK (P_kind_of_link1.v:126). So the call needs 144 + 2 * ESTACK = 8336 bytes;
     160 + 2 * ESTACK = 8352 covers it. The 41 words 0x84028..0x840cc equal the donor function's first 41 words
     except the five pc-relative ones (auipc @0x84074, @0x84078; ld @0x8407c, @0x84080; jal @0x84098).
   - the cells: auipc a1 @0x84074 (hi 22), ld a1 @0x84080 reads the GOT word 0x9ba40 (object 1), which holds
     0xa3af8 = __asan_shadow_memory_dynamic_address (object 16), ld s9 @0x84088 reads it; auipc a2 @0x84078 (hi 23),
     ld a2 @0x8407c reads the GOT word 0x9ba98 (object 0), which holds 0xa3b00 =
     __asan_option_detect_stack_use_after_return (object 17), lw a2 @0x84084 reads it.
   - The one caller: check_step (0x83294), jal @0x8369c, return site 0x836a0, with a0 = F + 32 (mv a0,s6 @0x83694;
     addi s6,s10,32 @0x83488), a1 = 50 (li a1,50 @0x83690), a2 = F + 128 (mv a2,s7 @0x83698; addi s7,s10,128
     @0x8348c), F = check_step's class-2 fake frame (li a0,224 @0x83304; jal __asan_stack_malloc_2 @0x8330c); its
     frame description "2 32 50 9 frame:140 128 36 5 p:143" (.rodata 0x14ef7): f = frame, o = p, f + 50 <= o.
   - the UBSan checks (trap mode: each branches to the function's one unimp 0xc0001073 @0x84824; .symtab has no
     __ubsan_handle_* symbol). Below, f and o are a0 and a2 at entry, s3 = o (mv s3,s4 @0x84154) since o <> 0,
     values are unsigned 64-bit and the source lines are reac_ctrlblk.c:
     G01 beqz s5 @0x84170 (262:25), f = 0.           G02 bgeu s5,a0 @0x84178 (262:25, a0 = -12), f >= 2^64 - 12.
     G03 bltu a0,s5 @0x841a0 (262:46, a0 = -14), f > 2^64 - 14.
     G04 bnez a0 @0x841c8 (266:14, andi a0,s3,3 @0x841c4), o mod 4 <> 0.
     G05 bltu a1,a0 @0x841f0 (267:25, a1 = f + 6, a0 = 7), f = 0 or f >= 2^64 - 6.
     G06 bltu a1,s5 @0x84240 (269:28, a1 = -15), f > 2^64 - 15. G07 bltu a0,s5 @0x84248 (269:28, a0 = -16), f > 2^64 - 16.
     G08 bltu a2,s5 @0x842ac (271:31, a2 = -19), f > 2^64 - 19.
     G09 beq a0,a2 @0x842f0 (273:17, a2 = -1, addi a0,s5,18 @0x842b0), f + 18 = 2^64 - 1 mod 2^64.
     G10 bltu a1,a5 @0x84338 (274:29, a1 = f + 21, a5 = 2), (f + 21) mod 2^64 < 2.
     G11 bltu a5,a0 @0x8439c (275:17, a5 = -5, a0 = f + 18), (f + 18) mod 2^64 > 2^64 - 5.
     G12 bltu a5,s5 @0x843e0 (277:21, a5 = -17), f > 2^64 - 17. G13 bltu a2,s5 @0x843fc (277:43, a2 = -18), f > 2^64 - 18.
     G14 bnez a0 @0x84444 (263:8, andi a0,s3,3 @0x84440), o mod 4 <> 0.
     G15..G21 test a0 = f + 18 (addi a0,s5,18 @0x842b0, not written again before 0x84788): (f + 18) mod 2^64 > 2^64 - k,
     G15 bltu a1,a0 @0x84620 (323:30) k = 17, G16 bltu a1,a0 @0x84628 (323:30) k = 18,
     G17 bltu a1,a0 @0x8468c (324:7) k = 15, G18 bltu a1,a0 @0x846b4 (324:41) k = 16,
     G19 bltu a2,a0 @0x846fc (327:17) k = 19, G20 bltu a3,a0 @0x84740 (328:17) k = 20,
     G21 bltu a3,a0 @0x84784 (329:17) k = 21.
     Every guard is false under the premises: `afobj ... f 50` puts [f, f + 50) in a frame of Sc, and the core's
     frames_bounds (under the AR of the ajournal premise and the walk's AR_laws hypothesis) gives 4096 <= frame_addr
     and frame_addr + fs_frame_bytes <= alloc ceiling <= 0x7fffff800000 (asan_consts), so 4096 <= f and
     f + 50 < 2^47: G01-G03, G05-G13 and G15-G21 never hold (the largest offset tested is f + 38). `afobj ... o 36`
     gives o mod 8 = 0 (SceneBase.v:54) and, the same way, 4096 <= o, so s3 = o and G04, G14 never hold. No premise
     is added. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaRun PaShadow PaJournal SceneSyms SceneList ScenePa ScenePaLib.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import SceneBase YC81 YC4b YC1g YC1h YC45 YC85 SceneFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import P_kind_of_link1 SceneRo ACj1 SceneACja.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg scene_listing}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).
(* The image address of the function. *)
Definition A_ctrl_parseP : Z := BASE + AF_reac_ctrl_parse.
(* The machine stack the call needs: its own 128-byte frame, realigned down to 32 bytes (at most 16 more),
   and below that 2 * ESTACK, which the bcmp wrapper's contract (abcmp_realizes) asks for; the other runtime
   entries and kind_of_link1 (KIND_OF_LINK1_STK = ESTACK) need less. *)
Definition TPARSE_STK : Z := 160 + 2 * ESTACK.
Section e.
Variable B : asyms.
Definition tctrl_parse_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (n o : Z) (fr : list byte) : world SEGS -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\ (exists ff, S2 = set_fs ff Sc) /\
getr regs2 10 = w64 (fst (ctrlparse n fr)) /\
(forall i, (i < 36)%nat -> aview SEGS (w_H W2) mem2 (o + Z.of_nat i) = Some (bv_unsigned (nth i (snd (ctrlparse n fr)) cp_z))) /\
acall_kept SEGS B lyc Sc W memc W2 mem2 (spZ regs - TPARSE_STK) (spZ regs) (fun a => o <= a < o + 36).
Definition tctrl_parse_spec : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch (f n o : Z) (fr : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 f -> getr regs 11 = w64 n -> getr regs 12 = w64 o -> 0 <= n < 2 ^ 64 ->
achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TPARSE_STK -> spZ regs <= sp0 ->
Z.of_nat (length (frames Sc)) <= 8 ->
afobj SEGS B lyc Sc W memc f 50 -> afobj SEGS B lyc Sc W memc o 36 -> f + 50 <= o \/ o + 36 <= f ->
(forall a, o <= a < o + 36 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
length fr = 50%nat ->
(forall i, (i < 50)%nat -> aview SEGS (w_H W) memc (f + Z.of_nat i) = Some (cp_v fr i)) ->
SRr SEGS W (cfg_at SEGS A_ctrl_parseP regs memc mdc)
(tctrl_parse_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs n o fr).
(* pb_ctrl_parse: proved in lib/AU/Prog/CtrlParse.v:88 (Qed), which lib/AU/G_Close.v applies. *)
(* The port plan, as written before the port (this file proves nothing): pb_ctrl_parse, of type tctrl_parse_spec, is a port of
   a Theorem Labs lane's walk of the same source (that walk is closed nowhere; see the last three items)
   (CtrlParse.v, CtrlParseMid.v, CtrlParseTail.v, CtrlParseEpi.v, with CtrlParseLib.v
   and the rest of CtrlParseCut.v: ss_cutA, pz_win_tac, pz_rebase, pz_bases, pz_awr_hd, pz_norm, pz_ctx, pz_rt, pz_ok,
   pz_E0, pz_cur, pz_post, the three cut specs, pz_open*, pz_std) over this listing, with these changes, each
   measured in fuzz_scene.asan-ubsan:
   - the listing modules are lib.AU.Prog's (the core modules as in the Require lines above); RET takes PL_scene
     (lib/AU/Prog/ScenePa.v:36); the listing is
     scene_listing (SceneList.v:25); pz_rt's runtime names are SIGMA SS___asan_memset, SS___asan_memcpy,
     SS___interceptor_trampoline_bcmp (SceneSyms.v:13, :16, :17).
   - Listing objects (atom A_OBJ i = 241 + i, PaTable.v:15): the shadow-base cell 0xa3af8 is object 16 (atom 257) and
     the UAR flag 0xa3b00 is object 17 (atom 258), ScenePaLib.v:309 pal_cell / :311 pal_uar_cell; the GOT words are
     objects 0 (0x9ba98, ld @0x8407c, :310 pal_got_uar) and 1 (0x9ba40, ld @0x84080, :308 pal_got_shadow). Every
     use of the donor's two cell indices changes to 16 and 17 (pa_obj_img, EOB, the cell atoms, the
     uar_got_regionP / uar_cell_regionP argument, pz_bases' AGX list); EOB's bound becomes scene_nobj = 18
     (SceneAddr.v:104). The entry atoms of the shadow base SB (PZx, bcell_regionP) and of sp1 stay.
   - OBJ_BCAST stays 15: object 15 = 0x20e40 = .str.4, 6 x 0xff then 0, built by auipc a0 @0x84210 (hi 26);
     addi a1,a0,-0x3d0 @0x84214, the bcmp's second argument (a2 = 6 @0x84218).
   - The cuts move, the UBSan checks being new code: cut A 0x8409c (AF + 0x74, after __asan_stack_malloc_1
     returns, as in the donor), cut B 0x84224 (AF + 0x1fc, after the bcmp wrapper returns), cut J 0x84448
     (AF + 0x420, the join of every path). On the header-rejecting paths the return code 0 is a0 = s3 & 3 of G14
     (andi a0,s3,3 @0x84440), not a `mv a0, zero`.
   - Each guard's unimp side (0x84824) is refuted, not walked, from the facts on atom 10 (f in [4096, 0x7fffff800000],
     8-aligned) and atom 12 (o, the same): G01-G03, G05-G13, G15-G21 by the range of f (with G09-G11, G15-G21 on
     a0 = f + 18), G04 and G14 by o mod 8 = 0. lib/AU/U_NotTrap.v's kill_not_trap (at
     27b1f2557dc) covers only the `not rX; bltu rX, rK` shape, which this function does not use.
   - The donor walk is closed at no cited commit, so no part of this file may be reported as "proved by port"
     while that holds. At d315cc159b2 the donor theorem itself ends in `admit` / `Admitted`
     (CtrlParse.v:381-382). At 119225419ab CtrlParse.v:318 is Qed, but every segment it
     applies is Admitted: pz_segB (CtrlParseMid.v:41), pz_segD (CtrlParseEpi.v:41), pz_segAcc
     (CtrlParseAcc.v:42), pz_segN (CtrlParseNone.v:42) and pz_tail1..pz_tail5 (CtrlParseTail1..5.v:41).
     So parse's inline release of its class-1 fake frame, and the AR re-establishment after it
     (astack_free_law), were machine-checked nowhere then: this port had to close every segment itself, or wait
     until the donor closed them. This tree's CtrlParseMid.v .. CtrlParseTail5.v close every segment with Qed.
   - The section hypotheses the port inherits from the donor theorem (CtrlParse.v:44-65 at 119225419ab, the
     same list at :133-151 of d315cc159b2): RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi; B : asyms, with
     LAWS : AR_laws SEGS B, TL : PALib B, TLF : PALibF B, ML : model_laws (as_universe B),
     AMEMSET / AMEMCPY : aintrin_realizes SEGS B OSet / OCpy (SIGMA SS___asan_memset / SS___asan_memcpy),
     ABCMP : abcmp_realizes SEGS B (SIGMA SS___interceptor_trampoline_bcmp),
     ASM1 : astack_malloc_realizes SEGS B 1, SMP : stack_malloc_progressP B, ASF : astack_free_law SEGS B,
     FFL : frame_flag_lawP SEGS B, KIND : tkind_of_link1_spec B; and, for the bcmp operand, G : list (Z * Z)
     with HGM : globs_marked SEGS B G, HG15 : In (VAL (A_OBJ OBJ_BCAST), 7) G,
     HIMGSH : img_shadow_vis SEGS B,
     HBC_RNG : IMG_LO + 64 <= VAL (A_OBJ OBJ_BCAST) /\ VAL (A_OBJ OBJ_BCAST) + 6 + 64 <= IMG_TOP, and
     HBC_VAL (the six bytes read by the bcmp are 0xff, through arodata_okP).
   - HGM and HIMGSH are the two of that list which quantify over all AR states, and nothing else in scene implies
     them: they close only with scene's B certificate (a Theorem Labs lane's collector, modelled on grant's
     GrantClose.v:407-443, which discharges the two at grant's concrete B), extended to .str.4 (object 15 =
     0x20e40, registered size 7). The other hypotheses are per-call-site or per-image facts. HBC_RNG and
     HBC_VAL hold for the pinned image: 0x10000 + 64 <= 0x20e40, 0x20e40 + 6 + 64 <= 0x5f9000 and the ROM
     bytes at 0x20e40 are 6 x 0xff. *)
End e.
End d.
End b.
