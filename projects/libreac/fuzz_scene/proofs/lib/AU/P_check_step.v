(* Rule 24 is met: no function is proved by assumption here. pb_check_stepX is closed by cs_chain (Qed) from the five
   segment lemmas cs_S0 .. cs_S4 of lib/AU/P_check_step_S0.v .. S4.v, EVERY ONE OF THEM PROVED, and frame_setup and
   afobj_of_own (lib/AU/P_check_step_frame.v) are proved too; `Print Assumptions pb_check_stepX` leaves only the
   primitive-integer / -string axioms and Stdlib's functional_extensionality_dep (toolchain/allowed-axioms.txt:94).
   Evidence, from fresh worktrees of the integration branch at bfcf9aa68da6 and e03c203366b8: for this image
   build-20261029T014523Z.log (sha256 d855378b10ce; internal record): rc=0, 87 files; for the asan twin
   build-20261029T005135Z.log (sha256 ba74856c8e19; internal record): rc=0, 83 files.

   The asan-ubsan twin of lib/A/P_check_step.v: the SAME statement text over the asan-ubsan kit (lib.AU.Prog,
   at 82cb6676c06). The cut states differ only where the code does (P_check_step_cut.v).

   Image: fuzz_scene.asan-ubsan, sha256 e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f; symbols from
   the unstripped twin (same loaded bytes). Every number is measured (a Theorem Labs lane's TWINMAP.md sections 2, 4.1, 5;
   pyelftools on the unstripped twin):
     - check_step = 0x83294 (1588 bytes, 397 insns) = listing base 0x828a4 + AF_check_step 0x9f0 (lib/AU/Prog/SceneList.v).
     - its stack: `addi sp,sp,-0x80` 0x83294, `andi sp,sp,-0x20` 0x832d4: the same frame and realignment as asan.
     - fake frame: class 2, __asan_stack_malloc_2 0x3f29c called at 0x8330c with a0 = 0xe0 (224); inline release
       (32 x 0xf5 at 0x8371c-0x83798, flag clear 0x8379c-0x837a0).
     - UAR flag as_uar_cell B = __asan_option_detect_stack_use_after_return 0xa3b00 (object 17) through GOT 0x9ba98
       (object 0); shadow base as_shadow_cell B = __asan_shadow_memory_dynamic_address 0xa3af8 (object 16) through GOT
       0x9ba40 (object 1). (0xa3800 lies inside __asan::ScopedInErrorReport::current_error_ in this image.)
     - check_step.trailer = 0x20d80 (object 7, 12 B) and __const.check_step.frame = 0x20da0 (object 8, 50 B), the
       same addresses and bytes as asan; asan-ubsan copies all 50 bytes of the initializer (0x8365c) where asan
       copies 16, then blk over F+48..F+82 (0x83674), so the 50 bytes parse reads are the same.
     - callees: __wrap_bcmp 0x44338, __asan_memcpy 0x539f0, reac_ctrl_parse 0x84028, reac_ctrl_checksum_verify 0x839e8.
     - read-only window .data.rel.ro + .got = 0x9b4e0..0x9c740 (pa_relro_lo/hi); image range 0x10000..0x5f9000.
   The 12 UBSan trap branches (to `unimp` 0x83864) are decided on the no-trap edge inside the segments; none needs a
   premise the asan statement does not have.
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
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaRun PaShadow SceneSyms SceneList ScenePa.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock RcModel RcParse.
(* reac_ctrl_parse (a Theorem Labs lane 8cd86323565, TPARSE_STK = 8352) and reac_ctrl_checksum_verify (a Theorem Labs lane 33d26845cd2,
   TCKV_STK = 16): a Theorem Labs lane's asan-ubsan statements, Required by name. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import P_reac_ctrl_checksum_verify P_reac_ctrl_parse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_check_step_frame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Export P_check_step_cut.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require P_check_step_S0 P_check_step_S1 P_check_step_S2 P_check_step_S3 P_check_step_S4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head is an explicit Section Context the glue instantiates with scene's own (a Theorem Labs lane 22:57Z): never chosen by
   instance search (a global src0_sink_head comes into scope with the relocated core's YI5b). *)
Context (SK : YI16.sink_head). #[local] Existing Instance SK.
Section f.
Context {PI : PAImg scene_listing}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
Section h.
Variable B : asyms.
Definition tcheck_step_specX : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (blk body k : Z) (b : list byte),
afn_pre SEGS B TCHECK_STEP_STK ly S W regs mem md ch ->
spZ regs mod 32 = 0 -> spZ regs + 32 <= ly_top ly ->
Z.of_nat (length (frames S)) <= 7 ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
getr regs 10 = w64 blk -> getr regs 11 = w64 body -> getr regs 12 = w64 k ->
0 <= k <= CS_LAST ->
afobj SEGS B ly S W mem blk CS_BLK_LEN ->
In (body, CS_BODY_LEN) (ablocks B ly S) ->
length b = Z.to_nat CS_BODY_LEN ->
(forall i, 0 <= i < CS_BODY_LEN ->
aview SEGS (w_H W) mem (body + i) = Some (bv_unsigned (nth (Z.to_nat i) b (Z_to_bv 8 0)))) ->
(forall i, 0 <= i < CS_BLK_LEN ->
aview SEGS (w_H W) mem (blk + i) = Some (bv_unsigned (nth (Z.to_nat i) (scene_block b k) (Z_to_bv 8 0)))) ->
st_nev S + EV_CHECK_STEP <= EV_MAX -> blocks_bytes S + LIVE_CHECK_STEP <= LIVE_MAX ->
SRr SEGS W (cfg_at SEGS A_check_step regs mem md)
(apost_base SEGS B TCHECK_STEP_STK [] regs ly S W mem md EV_CHECK_STEP
(fun ly' S' W' regs' mem' md' => ablocks B ly' S' = ablocks B ly S)).
(* The composition: the contract from the five segment statements, by SRr_bind alone. *)
Lemma cs_chain : CS_S0_stmt SK B -> CS_S1_stmt SK B -> CS_S2_stmt SK B -> CS_S3_stmt SK B -> CS_S4_stmt SK B -> tcheck_step_specX.
Proof.
intros H0 H1 H2 H3 H4. unfold tcheck_step_specX.
intros ly S W regs mem md ch blk body k b P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16.
assert (HP : cs_pre B ly S W regs mem md ch blk body k b) by (unfold cs_pre; tauto).
eapply SRr_bind; [exact (H0 ly S W regs mem md ch blk body k b HP)|].
intros W1 c1 _ (ly1 & S1 & regs1 & mem1 & md1 & fpos & -> & HS1).
eapply SRr_bind; [exact (H1 ly S W regs mem md ch blk body k b fpos ly1 S1 W1 regs1 mem1 md1 HS1)|].
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HS2).
eapply SRr_bind; [exact (H2 ly S W regs mem md ch blk body k b fpos ly2 S2 W2 regs2 mem2 md2 HS2)|].
intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HS3).
eapply SRr_bind; [exact (H3 ly S W regs mem md ch blk body k b fpos ly3 S3 W3 regs3 mem3 md3 HS3)|].
intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HS4).
exact (H4 ly S W regs mem md ch blk body k b fpos ly4 S4 W4 regs4 mem4 md4 HS4).
Qed.
Section k.
(* A Theorem Labs lane: the read-only range stays below the sink's overflow head (cgif A/ACeh.v ro_tfa_below_ofl). *)
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
(* -- relocated laws and the glue's bindings (cgif A/ACk1.v:64-74, :82; ScenePaLib.v:307, SceneFrame.v:96) -- *)
(* LAWS and SMP are theorems, not hypotheses (an internal review, CHECKSTEP-REVIEW item R4): AR_laws_ok (Reusable/YG0q.v:803) and
   the model law ml_stack_malloc_progress (YG0d.v:520-521). The UAR flag reads 1 in every AR state by al_const
   (AR_const_law, YG0d.v:461-467: `rd32 ... (as_uar_cell B) 1`), one line from afn_pre's AR, so no flag hypothesis is
   taken (R4; a Theorem Labs lane's ruling at 21:06Z named the fact, which LAWS now gives). *)
Hypothesis ML : model_laws (as_universe B).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let SMP : stack_malloc_progressP B := ml_stack_malloc_progress _ ML.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
(* -- runtime contracts -- *)
(* relocated cgif_file_fuzzer A/AF0u.v:514 stack_malloc2_contract (relocated by two Theorem Labs lanes). *)
Hypothesis ASM2 : astack_malloc_realizes SEGS B CS_CID.
(* A Theorem Labs lane. *)
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA SS___asan_memcpy).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA SS___interceptor_trampoline_bcmp).
(* -- the static shadow of check_step's two read-only globals, as named facts of scene's B (an internal review,
   CHECKSTEP-REVIEW.md R2, 22:40Z): scene's start-up (asan_globals descriptors asan 0x9ffd0 / asan-ubsan 0xa0300;
   __asan_register_globals: f9 redzone 0x416ac-0x416ec, partial granule 0x417f8-0x4181c) leaves 0x7fffc1b0 = 00,
   c1b1 = 04, c1b2-b3 = f9, c1b4-b9 = 00, c1ba = 02, c1bb-bf = f9. Static facts of B, decided by vm_compute on scene's
   B; the same addresses in both images. The walk derives range_addressable and shadow_hull_vis for [0x20d80, +12)
   and [0x20da0, +16) (asan) / [0x20da0, +50) (asan-ubsan) from am_const (YG0n.v:211) and al_zshadow
   (YG0d.v:435-438), as cgif A/AE2m.v:20-54 does. shadow_addr 0x20d80 = 0x7fffc1b0, shadow_addr 0x20da0 = 0x7fffc1b4. -- *)
Hypothesis HB_Z_TR : Exists (zr_sub (A_CS_TRAILER, 8)) (as_zero_shadow B).
Hypothesis HB_Z_CF : Exists (zr_sub (A_CS_CFRAME, 48)) (as_zero_shadow B).
Hypothesis HB_C_CS : forall ly,
  In (z1 (ANum (shadow_addr A_CS_TRAILER + 1)) 4) (as_const B ly) /\
  In (z1 (ANum (shadow_addr A_CS_TRAILER + 2)) 0xf9) (as_const B ly) /\
  In (z1 (ANum (shadow_addr A_CS_TRAILER + 3)) 0xf9) (as_const B ly) /\
  In (z1 (ANum (shadow_addr A_CS_CFRAME + 6)) 2) (as_const B ly) /\
  Forall (fun i => In (z1 (ANum (shadow_addr A_CS_CFRAME + i)) 0xf9) (as_const B ly)) [7; 8; 9; 10; 11].
(* static fact of the listing, closed by vm_compute on scene's PI: the two globals' addresses (same in both images); with HB_Z_TR / HB_Z_CF / HB_C_CS it pins every shadow byte of the 8-aligned hulls. *)
Hypothesis HB_ADDR : A_CS_TRAILER = 0x20d80 /\ A_CS_CFRAME = 0x20da0.
(* the image bytes of the two globals (arodata_okP gives them in every state). *)
Hypothesis HRO_TR : ro_bytes SEGS pa_relro_lo pa_relro_hi B A_CS_TRAILER scene_trailer.
Hypothesis HRO_CF : ro_bytes SEGS pa_relro_lo pa_relro_hi B A_CS_CFRAME cs_frame_init.
(* -- the program's callees: reac_ctrl_parse (a Theorem Labs lane 8cd86323565) and reac_ctrl_checksum_verify
   (a Theorem Labs lane 33d26845cd2), lib.AU.Prog -- *)
Hypothesis PARSE : tctrl_parse_spec (SK := SK) B.
Hypothesis CKV : tctrl_checksum_verify_spec (SK := SK) B.
Theorem pb_check_stepX : tcheck_step_specX.
Proof.
apply cs_chain.
- eapply P_check_step_S0.cs_S0; eassumption.
- eapply P_check_step_S1.cs_S1; eassumption.
- eapply P_check_step_S2.cs_S2; eassumption.
- eapply P_check_step_S3.cs_S3; eassumption.
- eapply P_check_step_S4.cs_S4; eassumption.
Qed.
End k.
End h.
End f.
End d.
About tcheck_step_specX.
About pb_check_stepX.
Print TCHECK_STEP_STK.
Eval vm_compute in TCHECK_STEP_STK.
Print Assumptions cs_chain.
Print Assumptions pb_check_stepX.
