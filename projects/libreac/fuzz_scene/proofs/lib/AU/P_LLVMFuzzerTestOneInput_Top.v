(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the TOP COMPOSITION of the walk of libreac/fuzz_scene's
   LLVMFuzzerTestOneInput in the ASAN-UBSAN build (lib/AU).  This is the twin of lib/A/P_LLVMFuzzerTestOneInput_Top.v
   (a working branch f4279258d43, Qed): the same text over this image's statement files, the
   lib/AU listing, this image's geometry `scene_geom_asan_ubsan` and this image's sink head 0x5f7190.  Two theorems,
   both Qed, below. *)

(*     llvmf_compose : forall segs B MT WK IM, llvmf_compose_stmt segs B MT WK IM
       -- the seven segment statements of lib/AU/P_LLVMFuzzerTestOneInput_seg.v compose into scene's entry contract
          `scene_tfib_lib_contract_x` (lib/AU/P_LLVMFuzzerTestOneInput_ctx.v);
     scene_llvmf : scene_llvmf_stmt B A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY
       -- that composition at scene's own asan-ubsan instance (lib/AU/P_LLVMFuzzerTestOneInput.v), so the glue
          takes ONE name.

   THE GLUE, AND WHY IT IS THIS SHORT.  The donor composes its harness stations the same way: cgif_file_fuzzer
   A/ACfj.v:258 chains the station lemmas by `SRr_bind` only because its stations are SYMBOLIC states, which must
   be threaded; its leaf step A/ACfi.v:139 then turns the last station's `SRr ... POST` into the contract's
   `srealizes ... (LIBK pl fs K)` by unfolding SRr at T := K l and handing POST to the contract's own third
   premise.  Here the cuts are SEMANTIC (P_LLVMFuzzerTestOneInput_seg.v header), and each segment statement is
   already written in the "next cut carries POST -> this cut carries POST" form (`sc_from_Cx`), so the chaining at
   a cut is function application, not an SRr_bind: there is no state to thread and no cut-point hypothesis to
   discharge.  What is left for this file is exactly the donor's A/ACfi.v:139 step:
     (1) pick the continuation.  POST is `sc_ret` (lib/AU/P_LLVMFuzzerTestOneInput_seg.v:507-513), i.e. "the config
         is the return to RA and the contract's post holds at scene's leaf".  It must be chosen BEFORE S0 runs,
         while the frame position fpos and the entry env E0 that S0 picks are still quantified; it is well defined
         there because `sc_ret` reads the entry record only through c_ly / c_S / c_W / c_regs / c_mem / c_md / c_p /
         c_n, which `mkRTCX` fixes from this file's own ly, S, W, regs, mem, md, p, n.  S6's conclusion is
         `sc_from_C6 ... cx (sc_ret ... cx)`, and `sc_ret ... cx` is convertible with that POST at every fpos / E0.
     (2) rebuild the cut kit's entry facts.  `sc_base0` is the contract's pre minus its two input-list clauses
         (`n = length pl`, `garr8 ... p pl`), at the meter budget T := XM_LIB n; `sc_base` adds the realigned stack
         pointer, which `mkRTCX` is applied at, so it is eq_refl.  S1 .. S6 each take `sc_base`.
     (3) the leaf.  The contract's conclusion is `srealizes segs (cfg_at segs A_LLVMF regs mem md)
         (LIBK pl (m_fs md) K)`; HLIBK rewrites LIBK to `K (LL 0 (m_fs md) [])`, SRr is unfolded at that trace set,
         and the resulting obligation IS the contract's third premise at l := LL 0 (m_fs md) [].
   The three of these are the whole file.  `SRr_bind` is not used: there is no intermediate state to thread.
   The 23 UBSan trap branches of this build add nothing here: they live inside the segments (lib/AU's statement
   file, the note on this build's traps), and this file looks inside no segment.

   WHAT IS TAKEN, AND FROM WHOM.  The seven segment statements are Section hypotheses here, each named with its
   owner.  Nothing else of the walk is taken: this file names no image value, no runtime contract and no callee
   spec, and it does not use any hypothesis of lib/AU/P_LLVMFuzzerTestOneInput.v's Section h (TL, TLF, ML, FFL, the
   shadow facts, the allocator and intrinsic contracts, the callee specs, HTRACE).  Those belong to the segment
   lanes.  HLIBK, the shape's leaf equation, is NOT a hypothesis: scene's shape is AgreeScene.ag_sil_shape =
   AgreeShape.ag_shape ZTraceSpec.checksum_shape, whose LIBK field is `fun pl fs K => K (LL 0 fs [])` by
   construction (ZTraceSpec.v:16, `Defined`), so it holds by reflexivity -- the harness does no I/O
   (lib/A/HaltsSpecS.v:3, HAND1-PLAN.md section 4.2).

   FILE ORDER.  lib/AU/P_LLVMFuzzerTestOneInput.v is Required only AFTER `llvmf_compose` is closed.  It pulls in
   lib/A/SceneAsanTop.v, which pulls in the released lib/U/Reusable twins of YI16 and YO09; those twins capture the
   short names `YI16.sink_head`, `lib_shape`, `LIBK` and `LL`, which Section d below has to write.  The statement
   file hit exactly this and had to fully qualify its sink head
   (lib/AU/P_LLVMFuzzerTestOneInput.v:163); here the Require is simply placed after the section that needs the
   short names, and the second section names none of them.
   MODULE LAYOUT (gate 6o, a Theorem Labs lane): every module of the trunk's lib/Reusable comes from lib.Reusable; the
   image-differing modules (YCbq, YC5d, YE01, YCbp), the listing lib.AU.Prog and the entry's own statement files
   come from lib.AU. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YO09 YE00.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YE01 YCbp.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import SceneSyms SceneList SceneAddr ScenePa SceneImg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput_ctx P_LLVMFuzzerTestOneInput_seg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- scene's segment list, meter and walk constants, resolved HERE, where the short names are the ones of
   lib/Reusable and lib/AU/Prog (see FILE ORDER above).  `scene_walk` takes the entry constants as arguments: the
   instance file binds them (lib/AU/P_LLVMFuzzerTestOneInput.v:182), this file must not.  The section is over
   RunCeil alone: `pa_segs` / `pa_relro_lo` / `pa_relro_hi` of PI_scene need it, as the statement file's own SEGS /
   RLO / RHI notations do (lib/AU/P_LLVMFuzzerTestOneInput.v:165-170, inside its Section d). ---- *)
Section c. Context {rc : YM05.RunCeil}.
Definition scene_segs : list Segment := @pa_segs _ scene_listing PI_scene.
Definition scene_mt : ameter_ops := ameter_triv.
(* The meter budgets are zero on both sides, as cgif A/ACfi.v:56 XL0 has them. *)
Definition scene_walk (SINK : list (Z * Z)) (A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY : Z) : swalk :=
{| sw_sink := SINK;
sw_entry := A_LLVMF; sw_ra := RA_LLVMF; sw_ev := EV_LIB; sw_live := LIVE_LIB;
sw_stk := LLVMF_STK; sw_empty := A_EMPTY;
sw_xm := fun _ : Z => 0; sw_xn := fun _ : Z => 0;
sw_rlo := @pa_relro_lo _ scene_listing PI_scene; sw_rhi := @pa_relro_hi _ scene_listing PI_scene |}.
End c.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {LS : lib_shape}.
Context {SK : YI16.sink_head}.

Lemma llvmf_compose : forall (segs : list Segment) (B : asyms) (MT : ameter_ops) (WK : swalk) (IM : sgeom),
llvmf_compose_stmt segs B MT WK IM.
Proof.
intros segs B MT WK IM HLIBK HS0 HS1 HS2 HS3 HS4 HS5 HS6.
intros ly S W regs mem md p n pl K HAI HPRE HKK.
(* (2) the entry facts the cut kit asks for: the contract's pre minus `n = length pl` and `garr8 ... p pl`, which
   no cut carries (a lane reads the input bytes from memory itself, seg.v sc_in), at the meter budget
   T := XM_LIB n = sw_xm WK n. *)
assert (Hb0 : sc_base0 segs B MT WK ly S W regs mem md p n (sw_xm WK n)).
{ unfold scene_tfib_lib_pre_x in HPRE.
  destruct HPRE as (H1 & H2 & H3 & H4 & H5 & _ & _ & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H8 (conj H9 (conj H10
  (conj H11 (conj H12 (conj H13 (conj H14 H15)))))))))))). }
(* (1) the continuation.  This is `sc_ret segs B MT WK cx` (seg.v:507-513) written out: `sc_ret` reads cx only
   through c_ly .. c_n, so it does not depend on the frame position and the entry env that S0 picks, and it can be
   fixed here, before S0 quantifies over them. *)
set (POST := fun (W' : world segs) (c' : config) =>
exists ly' S' regs' mem' md' ev,
c' = cfg_at segs (sw_ra WK) regs' mem' md' /\
@scene_tfib_lib_post_x rc SK segs (sw_sink WK) (sw_ev WK) (sw_stk WK) B MT (sw_xn WK)
regs ly S W mem md p n (LL 0 (m_fs md) []) ly' S' W' regs' mem' md' ev).
assert (HR : SRr segs W (cfg_at segs (sw_entry WK) regs mem md) POST).
{ apply (HS0 ly S W regs mem md p n (sw_xm WK n) POST Hb0).
  intros fpos E0.
  set (cx := mkRTCX segs ly S W regs mem md p n fpos (32 * ((spZ regs - 224) / 32)) E0 (sw_xm WK n)).
  (* sc_base's second conjunct is the realignment equation, and cx is applied at that very value. *)
  assert (Hb : sc_base segs B MT WK cx) by exact (conj Hb0 eq_refl).
  (* the chain at the cuts: C1 <- C2 <- C3 <- C5 <- C6 <- the return, with the T loop closed inside S4 over S3. *)
  apply (HS1 cx POST Hb).
  apply (HS2 cx POST Hb).
  apply (HS4 cx POST Hb).
  - intros k Hk Hnext Htx. exact (HS3 cx POST k Hb Hk Hnext Htx).
  - apply (HS5 cx POST Hb). exact (HS6 cx Hb). }
(* (3) the leaf: scene's harness does no I/O, so the shape's leaf is LL 0 (m_fs md) [], and unfolding SRr at
   T := K (LL 0 (m_fs md) []) leaves exactly the contract's own third premise at that leaf. *)
rewrite (HLIBK pl (m_fs md) K).
refine (HR HAI (K (LL 0 (m_fs md) [])) _).
intros W' c' Hle HAI' HP.
exact (HKK (LL 0 (m_fs md) []) W' c' Hle HAI' HP).
Qed.
End d.

(* ---- this image's closed sink head: musl's ofl_head of fuzz_scene.asan-ubsan, 0x5f7190 (MEASURED in the
   unstripped twin's .symtab; lib/AU/P_LLVMFuzzerTestOneInput.v:27-28 and :165).  WHY A LOCAL COPY IS NEEDED.  The
   seven `seg_*_stmt` applications of Section t have an implicit `sink_head` to resolve (the cuts' return post,
   seg.v, passes it to scene_tfib_lib_post_x), and gate 6h forbids a GLOBAL sink-head instance: the statement
   file's own head is `#[local]` (lib/AU/P_LLVMFuzzerTestOneInput.v:165), so its name does not leave that file, and
   lib/Reusable/SinkGuard.v removes the released src0 ones.  A Theorem Labs lane's glue meets the same wall and answers it
   the same way (G_Top.v: "both are passed by name, and neither is an instance here").  This is the SAME record
   value as the statement file's `scene_sink_head`, so every hypothesis below is convertible with the lanes' own
   statements and with the head `scene_llvmf_stmt` names; the `refine` in scene_llvmf is what checks that.  It is
   declared here, before the Require below, where `YI16` is still lib/Reusable's.  (The asan twin's own local copy
   is `top_sink_head` at 0x5f6e90; this build's head differs by the image's relocation.) ---- *)
#[local] Instance top_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := 0x5f7190 |}.

(* ================================================================================================================
   SCENE'S ASAN-UBSAN INSTANCE.  From here on lib/A/SceneAsanTop.v's released lib/U/Reusable twins are in scope, so
   the short names YI16.sink_head, lib_shape, LIBK and LL must not be written; the section below writes none of
   them.  The shape is resolved by unification against `scene_llvmf_stmt`, which names scene's own
   (lib/AU/P_LLVMFuzzerTestOneInput.v:164, :289).
   ================================================================================================================ *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The entry constants, in the order lib/AU/P_LLVMFuzzerTestOneInput.v's Section h declares them (A_EMPTY sixth). *)
Variable B : asyms.
Variables A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY : Z.
Definition scene_walk_asan_ubsan : swalk :=
scene_walk SCENE_SINK_OWNED A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY.

(* -- the seven segment statements of lib/AU/P_LLVMFuzzerTestOneInput_seg.v, each with its owner.  This file proves
   none of them and looks inside none of them. -- *)
(* A Theorem Labs lane (segment S0 AU): the prologue, the class-8 stack malloc, the frame poison, the E parse and the mac loop. *)
Hypothesis HS0 : seg_S0_stmt (SK := top_sink_head) scene_segs B scene_mt scene_walk_asan_ubsan scene_geom_asan_ubsan.
(* A Theorem Labs lane (segment S1 AU): n' / n'', the malloc at 0x82c4c, the fill loop and the xor loop. *)
Hypothesis HS1 : seg_S1_stmt (SK := top_sink_head) scene_segs B scene_mt scene_walk_asan_ubsan scene_geom_asan_ubsan.
(* the B block, build_scene_step, the changed loop and check_step. *)
Hypothesis HS2 : seg_S2_stmt (SK := top_sink_head) scene_segs B scene_mt scene_walk_asan_ubsan scene_geom_asan_ubsan.
(* one whole_transfer turn, 0x82eac .. 0x82f6c. *)
Hypothesis HS3 : seg_S3_turn_stmt (SK := top_sink_head) scene_segs B scene_mt scene_walk_asan_ubsan scene_geom_asan_ubsan.
(* the guard, M2, the loop closed over S3 by induction, the exit checks, bcmp, F1, and the no-T arm. *)
Hypothesis HS4 : seg_S4_stmt (SK := top_sink_head) scene_segs B scene_mt scene_walk_asan_ubsan scene_geom_asan_ubsan.
(* the malloc at 0x82fa8 and the D block. *)
Hypothesis HS5 : seg_S5_stmt (SK := top_sink_head) scene_segs B scene_mt scene_walk_asan_ubsan scene_geom_asan_ubsan.
(* the two frees, the re-poison, __asan_stack_free_8, a0 = 0 and the epilogue. *)
Hypothesis HS6 : seg_S6_stmt (SK := top_sink_head) scene_segs B scene_mt scene_walk_asan_ubsan scene_geom_asan_ubsan.

Theorem scene_llvmf : scene_llvmf_stmt B A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY.
Proof.
unfold scene_llvmf_stmt.
refine (llvmf_compose scene_segs B scene_mt scene_walk_asan_ubsan scene_geom_asan_ubsan _ HS0 HS1 HS2 HS3 HS4 HS5 HS6).
(* the shape's leaf equation: scene's shape is AgreeScene.ag_sil_shape = AgreeShape.ag_shape
   ZTraceSpec.checksum_shape, whose LIBK is `fun pl fs K => K (LL 0 fs [])` (ZTraceSpec.v:16, Defined) -- this
   harness returns 0, writes nothing and leaves the file system (lib/A/HaltsSpecS.v:3). *)
intros pl fs K. reflexivity.
Qed.
End t.

Print Assumptions llvmf_compose.
Print Assumptions scene_llvmf.
