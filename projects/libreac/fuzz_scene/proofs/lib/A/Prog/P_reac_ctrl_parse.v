(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from projects/libreac/fuzz_grant/proofs/lib/A/Prog/CtrlParseCut.v. *)
(* reac_ctrl_parse (fuzz_scene.asan 0x83dd8, 616 instructions): the contract of the ASan build's code, in the
   caller-journal form (it writes the caller's 36-byte `struct reac_ctrl_parsed`). The return code and the 36 bytes
   it writes are Pau's model `ctrlparse` (lib/Prog/RcParse.v:45). Statement only; the walk is ported later.
   Ported from a Theorem Labs lane's proofs/libreac/fuzz_grant/lib/A/Prog/CtrlParseCut.v (at
   d315cc159b2; the same text at 9fb598002a1): the module paths and the listing's names changed; the
   text of A_ctrl_parseP, TPARSE_STK, tctrl_parse_post and tctrl_parse_spec is the donor's. The function's 616 words
   equal the donor image's except the 52 pc-relative ones (auipc / ld / addi of the two GOT words, the frame
   description and the broadcast string; jal to the runtime entries).
   Numbers: fuzz_scene.asan, sha256 43654a025fd02e1f248bcaf6b8ac44f9e5dbded7f2fc1d9a1e90f9d74feb3026
   (projects/libreac/fuzz_scene/harness.yaml at c8557374ad2e); symbols from the .symtab of
   unstripped/fuzz_scene/fuzz_scene.asan, whose bytes at 0x83dd8..0x84778 equal the pinned image's.
   - reac_ctrl_parse = 0x83dd8, st_size 2464 = 616 instructions (no compressed instruction).
   - LLVMFuzzerTestOneInput = 0x82878 = the listing's base (SceneAddr.v scene_text), so
     AF_reac_ctrl_parse = 0x83dd8 - 0x82878 = 0x1560 (SceneList.v:21; slots SceneList.v:1393-2008).
   - the arguments: a0 = f (mv s5,a0 @0x83e3c), a1 = n (mv s6,a1 @0x83e20), a2 = o (mv s4,a2 @0x83e1c).
   - f, 50 bytes: li a0,50 @0x83f18; bltu s6,a0 @0x83f1c rejects n < 50; it reads f[0..23) and f[32..39) (the two
     memcpys f[0..12), the bcmp f[0..6), checked byte loads f[12..23) and f[32..39)). The caller's object is
     `uint8_t frame[50]` (fuzz_scene.c:140, passed at fuzz_scene.c:160 as `reac_ctrl_parse(frame, sizeof frame, &p)`).
   - o, 36 bytes: li a2,36 @0x83f08; jal __asan_memset (0x53e60) @0x83f14 clears o[0..36) (o, or the local scratch
     when o = 0: beqz s4 @0x83f00); __asan_memcpy (0x539c4) o+10 <- f[0..6) @0x83f78, o+4 <- f[6..12) @0x83f88;
     the field stores, each after its shadow check, end at o+33 (sw o+0, sw o+16, sh o+20, sb o+22, sb o+23,
     sh o+24, sb o+26, sh o+28, sb o+30, sb o+31, sb o+32; 0x83fb8..0x84504). The caller's object is
     `struct reac_ctrl_parsed p` (fuzz_scene.c:143; check_step's frame description "128 36 5 p:143").
   - TPARSE_STK: addi sp,sp,-128 @0x83dd8 and andi sp,sp,-32 @0x83e14 give sp1 = 32 * ((sp - 128) / 32) >= sp - 144
     (sp mod 16 = 0). The fake frame is class 1 (li a0,128 @0x83e44; jal __asan_stack_malloc_1 (0x3f0e0) @0x83e48);
     on that path every call runs at sp1. (The real-stack fallback 0x83e60..0x83e78, taken when the flag read at
     0x83e34 is 0 or the call returns 0, does not happen in the model: the flag cell holds 1 and
     stack_malloc_progressP gives a class-1 frame under `length (frames Sc) <= 8`.) The deepest callee window is
     the bcmp wrapper's 2 * ESTACK
     (abcmp_realizes, lib/Reusable/YG0d.v): jal __interceptor_trampoline_bcmp (0x4430c) @0x83f9c; __asan_memset,
     __asan_memcpy and __asan_stack_malloc_1 take ESTACK, kind_of_link1 (0x84778, jal @0x842ec) takes
     KIND_OF_LINK1_STK = ESTACK. So the call needs 144 + 2 * ESTACK = 8336 bytes; 160 + 2 * ESTACK = 8352 covers it.
   - The one caller: check_step (0x8319c), jal @0x83538, return site 0x8353c, with a0 = F + 32 (addi s6,s10,32
     @0x83378), a1 = 50 (li a1,50 @0x8352c), a2 = F + 128 (addi s7,s10,128 @0x8337c), F = check_step's class-2 fake
     frame; its frame description "2 32 50 9 frame:140 128 36 5 p:143": f = frame, o = p, f + 50 <= o. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaRun PaShadow PaJournal SceneSyms SceneList ScenePa ScenePaLib.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import SceneBase YC81 YC4b YC1g YC1h YC45 YC85 SceneFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import P_kind_of_link1 SceneRo ACj1 SceneACja.
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
(* pb_ctrl_parse: proved in lib/A/Prog/CtrlParse.v:74 (Qed), which lib/A/G_Close.v applies. *)
(* The port plan, as written before the port (this file proves nothing): prove `pb_ctrl_parse : tctrl_parse_spec` by porting
   a Theorem Labs lane's walk of the same code (that walk is closed nowhere; see the last three items)
   (CtrlParse.v, CtrlParseMid.v, CtrlParseTail.v, CtrlParseEpi.v, with CtrlParseLib.v and
   the rest of CtrlParseCut.v: ss_cutA, pz_win_tac, pz_rebase, pz_bases, pz_awr_hd, pz_norm, pz_ctx, pz_rt, pz_ok,
   pz_E0, pz_cur, pz_post, the three cut specs, pz_open*, pz_std), with these changes, each measured in
   fuzz_scene.asan:
   - RET takes PL_scene; the listing is scene_listing.
   - Listing objects (atom A_OBJ i = 241 + i, PaTable.v:15): the shadow-base cell
     __asan_shadow_memory_dynamic_address 0xa37f8 is object 16 (atom 257) and the UAR flag
     __asan_option_detect_stack_use_after_return 0xa3800 is object 17 (atom 258), ScenePaLib.v pal_cell /
     pal_uar_cell; the GOT words are objects 0 (0x9b768, ld @0x83e2c) and 1 (0x9b710, ld @0x83e30), unchanged.
     Every object-index use of the walk changes accordingly (pa_obj_img, EOB, the atoms of the two cells, the
     uar_got_regionP / uar_cell_regionP argument, pz_bases' AGX list); EOB's bound becomes scene_nobj = 18.
     Atoms 32 (the shadow base SB) and 33 (sp1) are entry atoms, not objects: bcell_regionP 32, PZx = SOff 32 0
     and the regions based at atom 33 stay.
   - OBJ_BCAST stays 15: object 15 = 0x20e40 = .str.4, 6 x 0xff then 0 (registered size 7), built by
     auipc a0 @0x83f8c; addi a1,a0,-332 @0x83f90, the bcmp's second argument (a2 = 6 @0x83f94). pz_rt's image
     bound IMG_TOP (Reusable/YImgTop.v in the donor's later snapshots) is 0x5f9000 here: the last PT_LOAD ends at
     0x9d410 + 0x55ac68 = 0x5f8078, page-rounded; IMG_LO stays 0x10000.
   - The cuts keep their offsets from the entry (same code): cut A 0x83e4c (AF + 0x74, after
     __asan_stack_malloc_1 returns), cut M 0x83f18 (AF + 0x140, after __asan_memset returns), cut B 0x83fa0
     (AF + 0x1c8, after the bcmp wrapper returns), cut J 0x84180 (AF + 0x3a8).
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
