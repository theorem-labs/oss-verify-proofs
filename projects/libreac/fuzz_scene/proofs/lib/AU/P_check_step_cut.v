(* The statements of record for check_step's asan-ubsan walk: the cut states its five segment lemmas are proved
   against. No proof is Admitted in this file.

   The segment cuts of the asan-ubsan walk of libreac/fuzz_scene's check_step (fuzz_scene.asan-ubsan, sha256
   e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f, check_step = 0x83294 = BASE + AF_check_step 0x9f0,
   lib/AU/Prog/SceneList.v). The same text as lib/A/P_check_step_cut.v over the asan-ubsan kit (lib.AU.Prog), except
   where the code differs (a Theorem Labs lane's TWINMAP.md sections 2, 4.1, 5, 7):
     - `body` lives in t0 (x5), not a6 (0x832e0 `mv t0,a1`): cs_st1 and cs_st2 name register 5;
     - the off slice is computed in C2, before the length test (0x8353c-0x8357c), so at the S2 cut a2 = scene_off k
       is live (cs_st2 names register 12).
   Segments and cut pcs (dis: dis-check_step.asan-ubsan.txt (sha256 f0a4764a38cf; internal record)):
     S0  0x83294 .. 0x833f4 (+0x160): as asan (the poison stores end at 0x833f0; `srli a1,s3,3` 0x833b0).
     S1  0x833f4 .. 0x835c4 (+0x330): C1 + sum loop + C2 with the off slice; UBSan guards 0x83414, 0x8343c, 0x83464,
         0x834b8 (each of 32 turns), 0x8351c, 0x83570 (signed k - 1), 0x83588.
     S2  0x835c4 .. 0x8362c (+0x398): C3 payload bcmp 0x835f0 and C4 trailer bcmp 0x83624 (k = 342); guards 0x835d8,
         0x835e0 (`not` + `bltu`), 0x83604, 0x83610.
     S3  0x8362c .. 0x836d4 (+0x440): C5; the first __asan_memcpy copies 50 B (0x8365c), the second 34 B (0x83674);
         guard 0x83664; reac_ctrl_parse 0x8369c; reac_ctrl_checksum_verify 0x836cc.
     S4  0x836d4 .. ret 0x83860: inline class-2 release (0xf5 stores 0x8371c-0x83798, flag clear 0x8379c-0x837a0) and
         the epilogue.
   The 12 UBSan trap branches go to `unimp` 0x83864; each is decided on its no-trap edge inside its segment from
   these cut states (no extra premise).
   LAYOUT (gate 6o, a Theorem Labs lane 22:5xZ, as the asan-ubsan kit at ae48bfd851f): the image-specific YCbq (and YC5d) are Required from
   lib.AU; every other module from lib.Reusable, as in lib/A. *)
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
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq.  (* image-specific: lib.AU (gate 6o) *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaRun PaShadow SceneSyms SceneList ScenePa.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock.
(* reac_ctrl_parse (a Theorem Labs lane 8cd86323565, TPARSE_STK = 8352) and reac_ctrl_checksum_verify (a Theorem Labs lane 33d26845cd2,
   TCKV_STK = 16): a Theorem Labs lane's asan-ubsan statements, Required by name. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import P_reac_ctrl_checksum_verify P_reac_ctrl_parse.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* The block check_step checks: an 8904-byte scene body, block index 0..342, 34-byte block (Prog/SceneBlock.v,
   Prog/check_step_c.v:12-21). *)
Definition CS_BODY_LEN : Z := 8904.
Definition CS_LAST : Z := 342.
Definition CS_BLK_LEN : Z := 34.
(* check_step.trailer and __const.check_step.frame: their registered sizes. *)
Definition CS_TRAILER_LEN : Z := 12.
Definition CS_CFRAME_LEN : Z := 50.
(* The class and size of check_step's fake frame (__asan_stack_malloc_2, a0 = 224; fs_frame_bytes 2 = 256). *)
Definition CS_CID : Z := 2.
Definition CS_FRAME : Z := 224.
(* The stack window below the entry sp: the own frame (`addi sp,sp,-0x80` 0x83294), the realignment
   (`andi sp,sp,-0x20` 0x832d4: at most 16), and the largest callee window below the realigned sp: reac_ctrl_parse's
   TPARSE_STK = 8352 (a Theorem Labs lane 22:32Z); bcmp's 2 * ESTACK (YG0d.v:356), __asan_memcpy's and __asan_stack_malloc_2's
   ESTACK (YG0d.v:282, :321) and reac_ctrl_checksum_verify's TCKV_STK = 16 are smaller. = 8496. *)
Definition CHECK_STEP_FRAME : Z := 128.
Definition CHECK_STEP_REALIGN : Z := 16.
Definition CS_CALLEE_WIN : Z := Z.max (2 * ESTACK) (Z.max TPARSE_STK TCKV_STK).
Definition TCHECK_STEP_STK : Z := CHECK_STEP_FRAME + CHECK_STEP_REALIGN + CS_CALLEE_WIN.
(* Named increments: check_step and its callees call no allocator. *)
Definition EV_CHECK_STEP : Z := 0.
Definition LIVE_CHECK_STEP : Z := 0.
(* The 50-byte initializer __const.check_step.frame (as released U/Prog/check_step.v:200-201 scene_init). *)
Definition cs_frame_init : list byte :=
map (Z_to_bv 8) [255; 255; 255; 255; 255; 255; 0; 64; 171; 0; 0; 1; 136; 25; 0; 0] ++ repeat (Z_to_bv 8 0) 34.
(* The registers the prologue saves (0x8329c-0x832cc), in the order of their slots below the entry sp:
   ra at sp0 - 8, s0 at sp0 - 16, ..., s11 at sp0 - 104. *)
Definition cs_saved_regs : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head is an explicit Section Context the glue instantiates with scene's own (a Theorem Labs lane 22:57Z): never chosen by
   instance search (a global src0_sink_head comes into scope with the relocated core's YI5b). *)
Context (SK : YI16.sink_head). #[local] Existing Instance SK.
Definition cs_saved (regs : bvmap 5 word) (rd : Z -> option Z) : Prop :=
forall j, (j < 13)%nat ->
rdword rd (spZ regs - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr regs (Z_to_bv 5 (nth j cs_saved_regs 0)))).
(* The image bytes of a read-only object outside the runtime's own data: arodata_okP (SceneBase.v:21) then gives them
   in every state the journal reaches. A static fact of the image and of B, decided at the closing by vm_compute. *)
Definition ro_bytes (segs : list Segment) (rlo rhi : Z) (B : asyms) (a : Z) (l : list byte) : Prop :=
forall i, 0 <= i < Z.of_nat (length l) ->
in_roP segs rlo rhi (a + i) /\ ~ Exists (in_zr (a + i)) (as_owned_static B) /\ ~ (as_errno B <= a + i < as_errno B + 4) /\
option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 (a + i))) = Some (bv_unsigned (nth (Z.to_nat i) l (Z_to_bv 8 0))).
Section f.
Context {PI : PAImg scene_listing}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).
Definition A_check_step : Z := BASE + AF_check_step.
(* check_step.trailer (0x20d80, object 7 of lib/AU/Prog/SceneAddr.v) and __const.check_step.frame (0x20da0, object 8). *)
Definition A_CS_TRAILER : Z := VAL (A_OBJ 7).
Definition A_CS_CFRAME : Z := VAL (A_OBJ 8).
(* The cut pcs. *)
Definition CS_PC1 : Z := A_check_step + 0x160.
Definition CS_PC2 : Z := A_check_step + 0x330.
Definition CS_PC3 : Z := A_check_step + 0x398.
Definition CS_PC4 : Z := A_check_step + 0x440.
Section h.
Variable B : asyms.
(* The entry facts: the premises of P_check_step.tcheck_step_specX, as one conjunction. *)
Definition cs_pre ly S W (regs : bvmap 5 word) mem md ch (blk body k : Z) (b : list byte) : Prop :=
afn_pre SEGS B TCHECK_STEP_STK ly S W regs mem md ch /\
spZ regs mod 32 = 0 /\ spZ regs + 32 <= ly_top ly /\
Z.of_nat (length (frames S)) <= 7 /\
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) /\
getr regs 10 = w64 blk /\ getr regs 11 = w64 body /\ getr regs 12 = w64 k /\
0 <= k <= CS_LAST /\
afobj SEGS B ly S W mem blk CS_BLK_LEN /\
In (body, CS_BODY_LEN) (ablocks B ly S) /\
length b = Z.to_nat CS_BODY_LEN /\
(forall i, 0 <= i < CS_BODY_LEN ->
aview SEGS (w_H W) mem (body + i) = Some (bv_unsigned (nth (Z.to_nat i) b (Z_to_bv 8 0)))) /\
(forall i, 0 <= i < CS_BLK_LEN ->
aview SEGS (w_H W) mem (blk + i) = Some (bv_unsigned (nth (Z.to_nat i) (scene_block b k) (Z_to_bv 8 0)))) /\
st_nev S + EV_CHECK_STEP <= EV_MAX /\ blocks_bytes S + LIVE_CHECK_STEP <= LIVE_MAX.
(* The contract's post. *)
Definition cs_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md : world SEGS -> config -> Prop :=
apost_base SEGS B TCHECK_STEP_STK [] regs ly S W mem md EV_CHECK_STEP
(fun ly' S' W' regs' mem' md' => ablocks B ly' S' = ablocks B ly S).
(* What every cut after S0 carries: the journal with check_step's fake frame (2, fpos) in own, the heap blocks, the
   flag word, the saved registers, and the registers that hold sp, gp, tp, the frame pointer s0, the fake frame
   (s2, s10), its shadow address (s9) and the shadow base (s11). *)
Definition cs_frame (regs : bvmap 5 word) ly S (W : world SEGS) mem md (fpos : Z)
ly1 S1 (W1 : world SEGS) (regs1 : bvmap 5 word) mem1 md1 : Prop :=
ajournal SEGS B TCHECK_STEP_STK (spZ regs) [] ly S W mem md [(CS_CID, fpos)] ly1 S1 W1 mem1 md1 0 /\
ablocks B ly1 S1 = ablocks B ly S /\
rdword (aview SEGS (w_H W1) mem1) (frame_addr ly1 CS_CID fpos + fs_frame_bytes CS_CID - 8) = Some (flag_addr ly1 CS_CID fpos) /\
cs_saved regs (aview SEGS (w_H W1) mem1) /\
getr regs1 2 = w64 (spZ regs - CHECK_STEP_FRAME) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\
getr regs1 8 = w64 (spZ regs) /\
getr regs1 18 = w64 (frame_addr ly1 CS_CID fpos) /\
getr regs1 25 = w64 (SHADOW_OFF + frame_addr ly1 CS_CID fpos / 8) /\
getr regs1 26 = w64 (frame_addr ly1 CS_CID fpos) /\
getr regs1 27 = w64 SHADOW_OFF.
(* 0x833f4: s1 = the realigned sp (spill 0x833fc), s3 = blk, s4 = k, t0 = body, a1 = blk >> 3 (0x833b0). *)
Definition cs_st1 ly S W (regs : bvmap 5 word) mem md ch (blk body k : Z) (b : list byte) (fpos : Z)
ly1 S1 (W1 : world SEGS) (regs1 : bvmap 5 word) mem1 md1 : Prop :=
cs_pre ly S W regs mem md ch blk body k b /\
cs_frame regs ly S W mem md fpos ly1 S1 W1 regs1 mem1 md1 /\
getr regs1 9 = w64 (spZ regs - CHECK_STEP_FRAME) /\
getr regs1 19 = w64 blk /\ getr regs1 20 = w64 k /\ getr regs1 5 = w64 body /\
getr regs1 11 = w64 (blk / 8).
(* 0x835c4: s3 = blk, s4 = k, s5 = segment, s8 = length, s6 = &frame, s7 = &p, t0 = body, a2 = off (0x8355c-0x8357c). *)
Definition cs_st2 ly S W (regs : bvmap 5 word) mem md ch (blk body k : Z) (b : list byte) (fpos : Z)
ly1 S1 (W1 : world SEGS) (regs1 : bvmap 5 word) mem1 md1 : Prop :=
cs_pre ly S W regs mem md ch blk body k b /\
cs_frame regs ly S W mem md fpos ly1 S1 W1 regs1 mem1 md1 /\
getr regs1 19 = w64 blk /\ getr regs1 20 = w64 k /\
getr regs1 21 = w64 (scene_seg k) /\ getr regs1 24 = w64 (scene_len k) /\
getr regs1 22 = w64 (frame_addr ly1 CS_CID fpos + 32) /\ getr regs1 23 = w64 (frame_addr ly1 CS_CID fpos + 128) /\
getr regs1 5 = w64 body /\ getr regs1 12 = w64 (scene_off k).
(* 0x8362c: s3 = blk, s5 = segment, s8 = length, s6 = &frame, s7 = &p. *)
Definition cs_st3 ly S W (regs : bvmap 5 word) mem md ch (blk body k : Z) (b : list byte) (fpos : Z)
ly1 S1 (W1 : world SEGS) (regs1 : bvmap 5 word) mem1 md1 : Prop :=
cs_pre ly S W regs mem md ch blk body k b /\
cs_frame regs ly S W mem md fpos ly1 S1 W1 regs1 mem1 md1 /\
getr regs1 19 = w64 blk /\
getr regs1 21 = w64 (scene_seg k) /\ getr regs1 24 = w64 (scene_len k) /\
getr regs1 22 = w64 (frame_addr ly1 CS_CID fpos + 32) /\ getr regs1 23 = w64 (frame_addr ly1 CS_CID fpos + 128).
(* 0x836d4: the release reads only s2, s9, s10 and the epilogue s0 (all in cs_frame). *)
Definition cs_st4 ly S W (regs : bvmap 5 word) mem md ch (blk body k : Z) (b : list byte) (fpos : Z)
ly1 S1 (W1 : world SEGS) (regs1 : bvmap 5 word) mem1 md1 : Prop :=
cs_pre ly S W regs mem md ch blk body k b /\
cs_frame regs ly S W mem md fpos ly1 S1 W1 regs1 mem1 md1.
(* ---- the five segment statements ---- *)
Definition CS_S0_stmt : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (blk body k : Z) (b : list byte),
cs_pre ly S W regs mem md ch blk body k b ->
SRr SEGS W (cfg_at SEGS A_check_step regs mem md)
(fun W1 c1 => exists ly1 S1 regs1 mem1 md1 fpos, c1 = cfg_at SEGS CS_PC1 regs1 mem1 md1 /\
cs_st1 ly S W regs mem md ch blk body k b fpos ly1 S1 W1 regs1 mem1 md1).
Definition CS_S1_stmt : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (blk body k : Z) (b : list byte) (fpos : Z) ly1 S1 W1 regs1 mem1 md1,
cs_st1 ly S W regs mem md ch blk body k b fpos ly1 S1 W1 regs1 mem1 md1 ->
SRr SEGS W1 (cfg_at SEGS CS_PC1 regs1 mem1 md1)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2, c2 = cfg_at SEGS CS_PC2 regs2 mem2 md2 /\
cs_st2 ly S W regs mem md ch blk body k b fpos ly2 S2 W2 regs2 mem2 md2).
Definition CS_S2_stmt : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (blk body k : Z) (b : list byte) (fpos : Z) ly1 S1 W1 regs1 mem1 md1,
cs_st2 ly S W regs mem md ch blk body k b fpos ly1 S1 W1 regs1 mem1 md1 ->
SRr SEGS W1 (cfg_at SEGS CS_PC2 regs1 mem1 md1)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2, c2 = cfg_at SEGS CS_PC3 regs2 mem2 md2 /\
cs_st3 ly S W regs mem md ch blk body k b fpos ly2 S2 W2 regs2 mem2 md2).
Definition CS_S3_stmt : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (blk body k : Z) (b : list byte) (fpos : Z) ly1 S1 W1 regs1 mem1 md1,
cs_st3 ly S W regs mem md ch blk body k b fpos ly1 S1 W1 regs1 mem1 md1 ->
SRr SEGS W1 (cfg_at SEGS CS_PC3 regs1 mem1 md1)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2, c2 = cfg_at SEGS CS_PC4 regs2 mem2 md2 /\
cs_st4 ly S W regs mem md ch blk body k b fpos ly2 S2 W2 regs2 mem2 md2).
Definition CS_S4_stmt : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (blk body k : Z) (b : list byte) (fpos : Z) ly1 S1 W1 regs1 mem1 md1,
cs_st4 ly S W regs mem md ch blk body k b fpos ly1 S1 W1 regs1 mem1 md1 ->
SRr SEGS W1 (cfg_at SEGS CS_PC4 regs1 mem1 md1) (cs_post regs ly S W mem md).
End h.
End f.
End d.
