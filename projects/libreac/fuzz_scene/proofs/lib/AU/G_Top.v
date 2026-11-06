(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YD2o.v and YD2p.v (the asan-ubsan
   twins of A/AD2o.v and A/AD2p.v; with the program-side premises of YCfi.v:65-138) for fuzz_scene's asan-ubsan
   image, module paths changed. *)
(* SceneAsanTop.ASAN_UBSAN_T from explicit leaves, in the form of cgif_file_fuzzer lib/YD2o.v + YD2p.v; lib/A/G_Top.v
   is the asan twin of this file, and the donor references below name the asan twins (A/Xnnn.v; the asan-ubsan twin
   of each is Ynnn.v). Nothing here
   walks a program function (rule 24): every function of scene's own code is ONE hypothesis W_<function>, its walk
   (the contracts of its callees and the runtime pieces it calls give its own contract; the lists are a Theorem Labs lane's
   measured calls, PROGFNS.md (sha256 0866c5ddb6f3; internal record) section 2), and every runtime or driver piece is
   one hypothesis.
   - The run ceiling: as A/AD2o.v:75-84, valid_sp gives sp's window (g_valid_sp_window), YM05.RunCeilOf the ceiling,
     YM05.ceil_of_top_run its ceil_of_top fact. Every leaf is stated for every RunCeil (A/AD2o.v:40 Section RC).
   - The program part: cgif_file's A/ACfi.v:139 tfib_lib_x_all is cgif-specific (it applies A/ACfj.v:258 tfib_lib_x,
     the walk of cgif's own LLVMFuzzerTestOneInput, and image facts A/ACfi.v:25-53). Scene's program contract is the
     Section Variable scene_tfib_lib_contract_x (G_Drv.v), whose instance is a Theorem Labs lane's scene contract (cgif's
     A/ACfn.v:59-69 with scene's closed sink, A_EMPTY as an argument and the trailer in pre and post); it enters as the
     hypothesis W_LLVMFuzzerTestOneInput, the statement of a Theorem Labs lane's walk (AU/P_LLVMFuzzerTestOneInput.v at
     f6ab6e97937, :180-316), with the sink as a parameter list instead of cgif's record.
   - sink_path (YI16.v:12-13, used by the contract's scene_sink_none) = cgif's literal "/tmp/out.gif", inert: scene
     opens no file, so `fd_names_path (m_fds md) sink_path = false` is discharged by the shared inertness lemmas
     (a Theorem Labs lane -> a Theorem Labs lane's lib/Reusable); it is not a hard-coded leaf (a Theorem Labs lane, 23:43Z).
   - The glue proves AR_laws (YG0q.v:803 AR_laws_ok), and the laws the donor proves without walking a function:
     astack_free_law (g_ASF), frame_flag_lawP (g_FFL), ro_below_ofl (g_RO), the read-only window (g_RO_IN) and, in
     G_Drv.v, the hand-off (g_hs_open). The driver's site types (read check, stdout / stderr sites) are Section
     Variables (G_Drv.v); G_Close.v binds them to the restaged core's YD1i / YD1w / YD1x Definitions. The exit site
     is the core's own type, AU/YD1x.v:94-110 exit_site_tfa, for the EXS row and for DRV's exit-site premise.
   - Owners' statements are imported by their trunk module paths and used by name: a Theorem Labs lane's entry contract
     (A/P_LLVMFuzzerTestOneInput_ctx.v: scene_tfib_lib_contract_x, rt_trace_in_stmt), a Theorem Labs lane's A/P_check_step.v
     (tcheck_step_specX, pb_check_stepX's premises), a Theorem Labs lane's A/Prog/P_kind_of_link1.v (tkind_of_link1_spec),
     A/Prog/P_reac_ctrl_checksum_verify.v (tctrl_checksum_verify_spec) and A/Prog/P_reac_ctrl_parse.v
     (tctrl_parse_spec), the scene listing A/Prog/* (PI_scene, PALib, PALibF, in_roP, ro_below_ofl, in_zs), the
     runtime types (lib/Reusable/AsStackSz.v, StackFreeDef.v, SetShadowDef.v) and the glue's sink laws (G_Sink.v).
     Opaque, each with its owner: a Theorem Labs lane's three callee contracts (premises here; each is proved in this tree by its walk pb_<fn>, which G_Close.v applies), TS (B's tables: the
     collector / a Theorem Labs lane's AF0m), and the driver's site types (G_Drv.v).
   - Image constants: the segments SEGS, the relro window, the runtime entries and the entry constants are the scene
     listing's or pinned Definitions (PI_scene: pa_segs, pa_relro_lo / pa_relro_hi, pa_sigma SS_*; A_LLVMF,
     RA_LLVMF, A_EMPTY, the sink's cells); the three driver format strings are scene's asan-ubsan .rodata 0x1d69c
     "cli: cannot open ", 0x1d6b1 "cli: read error on ", 0x157fc "usage: "
     (SCENE-TABLES.md (sha256 47d0f838a659; internal record), lines 16-18); the sink head is asan_ubsan_sink_head (musl's
     ofl_head, SCENE-TABLES.md:351). B, TF, HS, the program contract's budgets EV_LIB / LIVE_LIB / LLVMF_STK
     stay Variables. *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_scene.images Require Import AsanUbsan.
(* Required first, so that the short names below resolve to lib/Reusable (scene's released tree also has
   lib/U/Reusable twins of some of them). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require SceneAsanBase.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require SceneAsanTop.
(* Gate 6h: no sink-head instance is in scope (lib/Reusable/SinkGuard.v removes the released src0 instances). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require SinkGuard.
(* The core's exit-site type AU/YD1x.v:94-110 exit_site_tfa (the restaged core), used by qualified name. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require YD1x.
(* Gate 6o (the placement table of record, at 5977155c3d7 port/6o/placement.tsv): TRUNK and
   SHARED modules from lib/Reusable, the image-specific ones (YCbq and its dependents) from lib/AU. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
  YK11 YK15 YK18 YK0c YK0e YG0f YG00 YG01 YG0n YG0d YG05 YG0q YG0t YK04 YA0i YA0n YI16
  YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK09 YA0c YA0e YA01 YA02.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq YC5d YCbp.
(* A Theorem Labs lane's sink record and its laws, BY PATH (at 4d244de18f0). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YE00.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YE01.
(* The runtime contracts shared by both images (a Theorem Labs lane, 22:5xZ): astack_malloc_sz_realizes (pc cid) (a Theorem Labs lane,
   lib/Reusable/AsStackSz.v, at 578cf24e2f15), astack_free_realizes (pc cid)
   (lib/Reusable/StackFreeDef.v), aset_shadow_realizes (pc v) (a Theorem Labs lane's SetShadowDef.v at lib/Reusable). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import AsStackSz StackFreeDef SetShadowDef.
(* The asan-ubsan scene listing (lib/AU/Prog, gate 6o) and the owners'
   statement files: a Theorem Labs lane's callee contracts (AU/Prog/P_kind_of_link1.v, P_reac_ctrl_checksum_verify.v,
   P_reac_ctrl_parse.v, and the parse walk AU/Prog/CtrlParse*.v, at c2fc5d41458), a Theorem Labs lane's
   check_step (AU/P_check_step*.v at 722526c3436), the glue's sink
   laws (G_Sink.v). A Theorem Labs lane's asan-ubsan entry contract and statement are below. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import
  PaTable PaSym SceneSyms SceneList SceneCode ScenePa SceneImg ScenePaLib SceneBase SceneRo SceneFrame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import
  P_kind_of_link1 P_reac_ctrl_checksum_verify P_reac_ctrl_parse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_check_step_frame P_check_step_cut P_check_step.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import G_Sink.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_reac_ctrl_build_scene_step P_reac_ctrl_scene_build P_reac_ctrl_scene_set_mac P_cksum_stamp.
(* A Theorem Labs lane's class-8 table twin (at caa7a6e7cc2): PC_STACK_MALLOC_8 = 0x3f438, CID8 = 8,
   which a Theorem Labs lane's PALibF field palf_sm8 (AU/Prog/SceneFrame.v:106) and a Theorem Labs lane's class-8 leaf name. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Rt Require Import StackMalloc8Tbl.
(* The asan-ubsan entry contract and trace statement, and the entry statement file for A_TAIL_TRAILER and
   TAIL_TRAILER_N (AU :151-152), which HB_Z_TT names (at f6ab6e97937, the entry
   statement of record). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput_ctx.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import G_Drv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
(* The lib_shape is scene_shape (SceneAsanBase: AgreeScene.ag_sil_shape, built on ZTraceSpec.checksum_shape, as
   intended; the program contract's instance fixes it) and the sink head is asan_ubsan_sink_head; both are passed by name,
   and neither is an instance here. No G file imports A/AE2k.v, so its tfib_sink_head instance is never in scope;
   SinkGuard removes the released src0 ones (gate 6h). *)
#[local] Abbreviation TSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation TPH := AsanUbsan.M.phdrs.
(* The scene listing's image (SceneImg.v:56 PI_scene; SEGS is SceneCode.v:18 scene_segs = AsanUbsan.M.loaded_segments, the
   same list as the driver's tfibsegs, AB1v.v:11). *)
#[local] Abbreviation SEGS := (@pa_segs _ scene_listing PI_scene).
#[local] Abbreviation VAL := (@pa_val _ scene_listing PI_scene).
#[local] Abbreviation SIGMA := (@pa_sigma _ scene_listing PI_scene).
#[local] Abbreviation BASE := (@pa_val _ scene_listing PI_scene A_TEXT).
#[local] Abbreviation RLO := (@pa_relro_lo _ scene_listing PI_scene).
#[local] Abbreviation RHI := (@pa_relro_hi _ scene_listing PI_scene).
(* A/AD2o.v:27-28. *)
Lemma g_valid_sp_window : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.
(* A/ACfi.v:56 XL0. *)
Definition g_XL0 : Z -> Z := fun _ => 0.
(* The sink head of the asan-ubsan image: musl's ofl_head, 0x5f7190 in fuzz_scene.asan-ubsan (the unstripped twin's
   .symtab, SCENE-TABLES.md (sha256 47d0f838a659; internal record), line 351). The donor's is YE2k.v:44
   tfib_sink_head. *)
Definition asan_ubsan_sink_head : OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI16.sink_head :=
  {| OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable.YI16.sk_ofl_head := 0x5f7190 |}.
(* The entry constants of the asan-ubsan image: LLVMFuzzerTestOneInput 0x828a4 (PROGFNS.md section 2), target_run's
   return address 0x827a0 (cells6j.tsv), oft_aligned_copy.empty 0x5d6160 (a Theorem Labs lane, 22:26Z). *)
Definition A_LLVMF : Z := 0x828a4.
Definition RA_LLVMF : Z := 0x827a0.
Definition A_EMPTY : Z := 0x5d6160.
(* The return addresses of the six allocator calls (a Theorem Labs lane f6ab6e97937 AU :156-161, offsets from the entry; the same
   six that a Theorem Labs lane measured in the listing dis-LLVMF.asan-ubsan.txt: 0x82c50 0x82e70 0x82fac / 0x82fa0 0x83160 0x83168). *)
Definition g_RT_malloc1_ra : Z := A_LLVMF + 0x3ac.
Definition g_RT_malloc2_ra : Z := A_LLVMF + 0x5cc.
Definition g_RT_malloc3_ra : Z := A_LLVMF + 0x708.
Definition g_RT_free1_ra : Z := A_LLVMF + 0x6fc.
Definition g_RT_free2_ra : Z := A_LLVMF + 0x8bc.
Definition g_RT_free3_ra : Z := A_LLVMF + 0x8c4.
(* The closed sink's cells of the asan-ubsan image: __libc + 1 0x5f6d29, ofl_lock 0x5f7188, ofl_head 0x5f7190 (the
   unstripped twin's .symtab, read with a Theorem Labs lane's sceref). *)
Definition g_SINK_OWNED : list (Z * Z) := [(0x5f6d29, 1); (0x5f7188, 4); (0x5f7190, 8)].
(* The static shadow cells of reac_ctrl_build_scene_step.TAIL_TRAILER (0x20e20, 12 bytes) and of the f9 run above
   reac_scene_placeholder (0x20e80, 8904 bytes); both objects have the same addresses in the asan-ubsan image (the
   unstripped twin's .symtab). The text is a Theorem Labs lane's f6ab6e97937 AU :262-266. *)
Definition g_TT_SHCELLS : list acell :=
  z1 (ANum (shadow_addr (0x20e20 + 8))) (12 mod 8)
  :: map (fun k => z1 (ANum (shadow_addr (0x20e20 + 8) + 1 + Z.of_nat k)) 0xf9) (seq 0 2).
Definition g_PL_SHCELLS : list acell :=
  map (fun k => z1 (ANum (shadow_addr (0x20e80 + 8904) + Z.of_nat k)) 0xf9) (seq 0 8).
Lemma g_HA_LLVMF : forall (rc : YM05.RunCeil) (fx : YK11.FPState), A_LLVMF = BASE + AF_LLVMFuzzerTestOneInput.
Proof. intros rc fx. vm_compute. reflexivity. Qed.
(* A Theorem Labs lane's HB_ADDR (AU/P_check_step.v): check_step's two read-only globals are the asan-ubsan listing's objects 7 / 8
   at 0x20d80 / 0x20da0, by vm_compute on PI_scene. *)
Lemma g_HB_ADDR : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  A_CS_TRAILER (PI:=PI_scene) = 0x20d80 /\ A_CS_CFRAME (PI:=PI_scene) = 0x20da0.
Proof. intros rc fx. split; vm_compute; reflexivity. Qed.
(* The program's contract: a Theorem Labs lane's scene_tfib_lib_contract_x (AU/P_LLVMFuzzerTestOneInput_ctx.v:173 at
   f6ab6e97937) at the one sink head, scene_shape, SEGS and the sink's cells, in the
   argument order of G_Drv.v's scene_tfib_lib_contract_x. *)
Definition g_contract (rc : YM05.RunCeil) (fx : YK11.FPState) (a ra ev live stk empty : Z) (B : asyms)
  (MT : ameter_ops) (XM XN : Z -> Z) (rlo rhi : Z) : Prop :=
  @scene_tfib_lib_contract_x fx rc asan_ubsan_sink_head SceneAsanBase.scene_shape
    (@pa_segs rc scene_listing (@PI_scene rc)) g_SINK_OWNED a ra ev live stk empty B MT XM XN rlo rhi.
Section g.
(* Image constants and tables that stay Variables (owners in G_Close.v's table). *)
Variable B : asyms.                                        (* A/AD2l.v:14 TfibB: the collector *)
Variable TF : atable.                                      (* AU/YB12.v:12 TFIB: a Theorem Labs lane *)
Variable HS : nat -> option acs.                           (* AU/YB01.v:620 HS_tfib: a Theorem Labs lane *)
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.  (* the donor's A/AD1k.v:85 xst *)
Variable est : (word -> bool) -> (word -> option byte) -> Prop.         (* the donor's A/AD1k.v:124 est *)
(* The program contract's budgets (A/ACfn.v:23-25). *)
Variables EV_LIB LIVE_LIB LLVMF_STK : Z.
(* R11: both are a Theorem Labs lane's asan-ubsan text now (lib/AU/P_LLVMFuzzerTestOneInput_ctx.v at
   f6ab6e97937): the contract is g_contract below, the trace fact rt_trace_in_stmt. *)
(* B's tables: scene's TfibSyms (the collector / a Theorem Labs lane's AF0m). *)
Variable TS : asyms -> Prop.
(* The driver's site types (AU/YD1i.v:19, AU/YD1w.v:119 / :144 / :151, AU/YD1x.v:37 / :38 / :57 / :83 / :69), as in
   G_Drv.v: Section Variables, at every run ceiling; their instances are scene's relocated definitions at fx0. The
   read-only test is the scene listing's in_roP over SEGS and its relro window (SceneBase.v), the donor's
   A/ACeg.v:42-44 in_ro_tfa with scene's window. *)
Variable aread_check : YM05.RunCeil -> asyms -> Prop.
Variable xst_frame : YM05.RunCeil -> (nat -> (word -> bool) -> (word -> option byte) -> Prop) -> Prop.
Variables printf_first printf_next : YM05.RunCeil -> asyms -> (nat -> (word -> bool) -> (word -> option byte) -> Prop) -> Prop.
Variables est_img est_frame : YM05.RunCeil -> ((word -> bool) -> (word -> option byte) -> Prop) -> Prop.
Variables fwrite_site refused_site : YM05.RunCeil -> asyms -> ((word -> bool) -> (word -> option byte) -> Prop) -> Prop.
Variable fprintf_s_site : YM05.RunCeil -> asyms -> ((word -> bool) -> (word -> option byte) -> Prop) -> Z -> list byte -> list byte -> Prop.
(* A Theorem Labs lane's four asan-ubsan callee contracts are typed from AU/P_reac_ctrl_build_scene_step.v,
   AU/P_cksum_stamp.v, AU/P_reac_ctrl_scene_build.v and AU/P_reac_ctrl_scene_set_mac.v at
   a0866e7f49c, where each comes with its proved walk pb_<fn>. *)

Hypothesis HB : TS B.
(* The entry walk's budgets (a Theorem Labs lane's AU/P_LLVMFuzzerTestOneInput.v:203-206 at f6ab6e97937, with its LLVMF_EV 6,
   LLVMF_NMAX 65535, LLVMF_SPDROP 240). *)
Hypothesis HEV : 6 <= EV_LIB.
Hypothesis HLIVE : 2 * 65535 <= LIVE_LIB.
Hypothesis HSTK : 240 + ASTACK <= LLVMF_STK.
Hypothesis HSTK_CS : 240 + TCHECK_STEP_STK <= LLVMF_STK.
(* The listing's library bindings (ScenePaLib.v:308 PALib, SceneFrame.v:102 PALibF; AU/P_LLVMFuzzerTestOneInput.v:233-234, AU/P_check_step.v:118-119). *)
Hypothesis TL : forall (rc : YM05.RunCeil) (fx : YK11.FPState), PALib (L:=scene_listing) (PI:=PI_scene) B.
Hypothesis TLF : forall (rc : YM05.RunCeil) (fx : YK11.FPState), PALibF (L:=scene_listing) (PI:=PI_scene) B.
(* The universe's laws: the donor proves it from TfibSyms' ts_universe (A/ACfi.v:72-73), so it is blocked by TS. *)
Hypothesis ML : model_laws (as_universe B).
(* The sink's laws, BY PATH from a Theorem Labs lane's release text (at 4d244de18f0 Reusable/YE01.v:28-40
   asink_img_laws, 10 fields), at scene's own sink record G_Sink.scene_K and the one sink head. Blocked by TS. *)
Hypothesis AIL : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  asink_img_laws (SK:=asan_ubsan_sink_head) SEGS B scene_K.
(* The entry walk takes the one-clause form over the cells it reads as 0 (AIL, AU/P_LLVMFuzzerTestOneInput.v:242). *)
Lemma g_sink_img_laws : forall (rc : YM05.RunCeil) (fx : YK11.FPState), sink_img_laws SEGS B g_SINK_OWNED.
Proof.
  intros rc fx a Ha. apply (ail_env _ _ _ (AIL rc fx)). unfold aenv_addr.
  unfold g_SINK_OWNED in Ha.
  apply Exists_cons in Ha as [H1 | Ha];
    [left; unfold ak_owned, scene_K, scene_owned; apply Exists_cons_hd; exact H1 |].
  apply Exists_cons in Ha as [H2 | Ha];
    [left; unfold ak_owned, scene_K, scene_owned; apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; exact H2 |].
  apply Exists_cons in Ha as [H3 | Ha]; [| inversion Ha].
  right. assert (Hhd : ak_ofl_head scene_K = 0x5f7190) by reflexivity. rewrite Hhd. exact H3.
Qed.
(* Static facts of B the entry walk reads (a Theorem Labs lane f6ab6e97937 AU/P_LLVMFuzzerTestOneInput.v:267-270; SceneRo.v:41
   in_zs takes only B; owner a Theorem Labs lane, the start-up certificate): reac_scene_placeholder's zero range and the f9
   cells above it, TAIL_TRAILER's zero range and its partial-granule / redzone cells. HB_Z_TT is a Theorem Labs lane's text
   verbatim, over A_TAIL_TRAILER (0x20e20) and TAIL_TRAILER_N (12) (AU :151-152): the zero range (0x20e00, 0x28),
   which starts 0x20 below the trailer. *)
Hypothesis HZS_PL : forall (rc : YM05.RunCeil) (fx : YK11.FPState), in_zs B 0x20e80 8904.
Hypothesis HB_C_PL : forall ly, Forall (fun c => In c (as_const B ly)) g_PL_SHCELLS.
Hypothesis HB_Z_TT : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  in_zs B (A_TAIL_TRAILER - 0x20) (0x20 + (TAIL_TRAILER_N - TAIL_TRAILER_N mod 8)).
Hypothesis HB_C_TT : forall ly, Forall (fun c => In c (as_const B ly)) g_TT_SHCELLS.
(* The entry statement's HRO_TT (f6ab6e97937 AU/P_LLVMFuzzerTestOneInput.v:215-216), its text: TAIL_TRAILER's 12 bytes lie in no
   as_owned_static range and are not the errno cell. Owner a Theorem Labs lane (B certificate); G_Close.v decides it from
   TfibSyms. *)
Hypothesis HRO_TT : forall i, 0 <= i < 12 ->
  ~ Exists (in_zr (0x20e20 + i)) (as_owned_static B) /\ ~ (as_errno B <= 0x20e20 + i < as_errno B + 4).
(* The entry statement's HRO_PL / HRO_PLGOT (f6ab6e97937 AU/P_LLVMFuzzerTestOneInput.v:224-228), their texts: the placeholder's
   LLVMF_SCENE_BYTES (8904) bytes and the GOT word VAL (A_OBJ 4) lie in no as_owned_static range and avoid the errno
   cell. Owner a Theorem Labs lane (B certificate); G_Close.v decides both at the concrete B. *)
Hypothesis HRO_PL : forall (rc : YM05.RunCeil) (fx : YK11.FPState), forall i, 0 <= i < LLVMF_SCENE_BYTES ->
  ~ Exists (in_zr (A_reac_scene_placeholder + i)) (as_owned_static B) /\
  ~ (as_errno B <= A_reac_scene_placeholder + i < as_errno B + 4).
Hypothesis HRO_PLGOT : forall (rc : YM05.RunCeil) (fx : YK11.FPState), forall i, 0 <= i < 8 ->
  ~ Exists (in_zr (VAL (A_OBJ 4) + i)) (as_owned_static B) /\ ~ (as_errno B <= VAL (A_OBJ 4) + i < as_errno B + 4).
(* check_step's two read-only globals: static facts of B and image bytes (a Theorem Labs lane's A/P_check_step.v:134-146 at
   722526c3436; CUTS.md section 7.2 certificate). *)
Hypothesis HB_Z_TR : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  Exists (zr_sub (A_CS_TRAILER (PI:=PI_scene), 8)) (as_zero_shadow B).
Hypothesis HB_Z_CF : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  Exists (zr_sub (A_CS_CFRAME (PI:=PI_scene), 48)) (as_zero_shadow B).
Hypothesis HB_C_CS : forall (rc : YM05.RunCeil) (fx : YK11.FPState) ly,
  In (z1 (ANum (shadow_addr (A_CS_TRAILER (PI:=PI_scene)) + 1)) 4) (as_const B ly) /\
  In (z1 (ANum (shadow_addr (A_CS_TRAILER (PI:=PI_scene)) + 2)) 0xf9) (as_const B ly) /\
  In (z1 (ANum (shadow_addr (A_CS_TRAILER (PI:=PI_scene)) + 3)) 0xf9) (as_const B ly) /\
  In (z1 (ANum (shadow_addr (A_CS_CFRAME (PI:=PI_scene)) + 6)) 2) (as_const B ly) /\
  Forall (fun i => In (z1 (ANum (shadow_addr (A_CS_CFRAME (PI:=PI_scene)) + i)) 0xf9) (as_const B ly)) [7; 8; 9; 10; 11].
Hypothesis HRO_TR : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  ro_bytes SEGS RLO RHI B (A_CS_TRAILER (PI:=PI_scene)) scene_trailer.
Hypothesis HRO_CF : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  ro_bytes SEGS RLO RHI B (A_CS_CFRAME (PI:=PI_scene)) cs_frame_init.
(* The class-8 frame setup is no longer a premise: a Theorem Labs lane's `frame_setup` is a lemma (AU/P_check_step_frame.v, Qed
   at 722526c3436), and a Theorem Labs lane's revised walk
   applies it. The allocation traces are a Theorem Labs lane's rt_trace_in_stmt (AU/P_LLVMFuzzerTestOneInput_ctx.v). *)
Hypothesis HTRACE : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  rt_trace_in_stmt SEGS RA_LLVMF (pc_malloc_ra0 (as_code B)) (pc_free_ra0 (as_code B))
    g_RT_malloc1_ra g_RT_malloc2_ra g_RT_malloc3_ra g_RT_free1_ra g_RT_free2_ra g_RT_free3_ra (as_universe B).
(* The laws the donor proves without walking a function, proved here (no start-up or per-image table is used). *)
(* A/ACfi.v:88-89 link_ASF: YG0t.v:472 astack_free_law_ok, generic in segs and B. *)
Lemma g_ASF : forall (rc : YM05.RunCeil) (fx : YK11.FPState), astack_free_law SEGS B.
Proof. intros rc fx. exact (astack_free_law_ok SEGS B). Qed.
(* A/ACfi.v:76-87 link_FFL, from AR_laws_ok and scene's image cover (A/Prog/SceneImg.v:50 scene_img_cover, for the
   donor's A/ACeg.v:85 tfib_img_cover), with YCbq.v's off_img, whose bounds are now the unit's
   own Reusable/YImgTop.v (a Theorem Labs lane 2d4a68692f3: IMG_LO 0x10000, IMG_TOP 0x5f9000 for both ASan images). *)
Lemma g_FFL : forall (rc : YM05.RunCeil) (fx : YK11.FPState), frame_flag_lawP SEGS B.
Proof.
  intros rc fx ly S W mem md cid pos HAR Hin.
  pose proof (AR_laws_ok SEGS B) as LAWS.
  destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
  destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
  { right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
  pose proof HAR as (M & L & _). pose proof (scene_img_cover ly S md L) as [C1 C2].
  destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
  split; [exact Hp|]. split; [exact Ho|]. split.
  - split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
  - split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* A/ACfi.v:42-51 tfib_ROB: every read-only segment of scene's image, and the relro window 0x9b4e0..0x9c740
   (AU/Prog/SceneImg.v:70-71), end below ofl_head 0x5f7190. *)
Lemma g_ro_segs_chk : forall (rc : YM05.RunCeil) (fx : YK11.FPState), 
  forallb (fun s : Segment => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x5f7190))%bool SEGS = true.
Proof. intros rc fx. vm_compute. reflexivity. Qed.
Lemma g_RO : forall (rc : YM05.RunCeil) (fx : YK11.FPState), ro_below_ofl (SK:=asan_ubsan_sink_head) SEGS RLO RHI.
Proof.
  intros rc fx a [(s & Hin & Hw & Hr) | Hr]; change (a < 0x5f7190).
  - pose proof (proj1 (forallb_forall _ _) (g_ro_segs_chk rc fx) s Hin) as Hb. cbn beta in Hb. rewrite Hw in Hb.
    cbn [orb] in Hb. apply Z.leb_le in Hb. lia.
  - change RHI with 0x9c740 in Hr. lia.
Qed.
(* A/AD2o.v:47 RO_IN, `fun a H => or_intror H`. *)
Lemma g_RO_IN : forall (rc : YM05.RunCeil) (fx : YK11.FPState), forall a, RLO <= a < RHI -> in_roP SEGS RLO RHI a.
Proof. intros rc fx a H. right. exact H. Qed.
(* Runtime leaves, for every FP state (A/ACfi.v:129-130): __wrap_malloc / __wrap_free (YG0d.v:253 / :269),
   __asan_memcpy / __asan_memset (YG0d.v:317 aintrin_realizes), __interceptor_trampoline_bcmp (YG0d.v:352), the
   class-1 / class-2 fake frames (YG0d.v:284), class 8 and set_shadow (AsStackSz / StackFreeDef / SetShadowDef).
   Each entry pc is the listing's pa_sigma of its symbol. *)
Hypothesis AMALLOC : forall (rc : YM05.RunCeil) (fx : YK11.FPState), amalloc_realizes SEGS B.
Hypothesis AFREE : forall (rc : YM05.RunCeil) (fx : YK11.FPState), afree_realizes SEGS B.
Hypothesis AMEMCPY : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  aintrin_realizes SEGS B OCpy (SIGMA SS___asan_memcpy).
Hypothesis AMEMSET : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  aintrin_realizes SEGS B OSet (SIGMA SS___asan_memset).
Hypothesis ABCMP : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  abcmp_realizes SEGS B (SIGMA SS___interceptor_trampoline_bcmp).
Hypothesis ASM1 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), astack_malloc_realizes SEGS B 1.
Hypothesis ASM2 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), astack_malloc_realizes SEGS B CS_CID.
(* Class 8 under a Theorem Labs lane's names (AU/P_LLVMFuzzerTestOneInput.v:284-285, a Theorem Labs lane 23:23Z): lib/AU/Rt/StackMalloc8Tbl.v CID8 = 8 and
   PC_STACK_MALLOC_8 = 0x3f438, which a Theorem Labs lane's PALibF field palf_sm8 equates with SIGMA SS___asan_stack_malloc_8. *)
Hypothesis stack_malloc_8_sz : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  astack_malloc_sz_realizes SEGS B StackMalloc8Tbl.PC_STACK_MALLOC_8 StackMalloc8Tbl.CID8.
Hypothesis ASF8 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  StackFreeDef.astack_free_realizes SEGS B (SIGMA SS___asan_stack_free_8) 8.
Hypothesis ASH00 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  SetShadowDef.aset_shadow_realizes SEGS B (SIGMA SS___asan_set_shadow_00) 0.
Hypothesis ASHF8 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  SetShadowDef.aset_shadow_realizes SEGS B (SIGMA SS___asan_set_shadow_f8) 0xf8.
(* One hypothesis per function of scene's own code: its walk, in its owner's form where the owner states one;
   callees and runtime calls as PROGFNS.md (sha256 0866c5ddb6f3; internal record) section 2 measures them. *)
(* kind_of_link1 0x84aac (a Theorem Labs lane's A/Prog/P_kind_of_link1.v:136-152 pb_kind_of_link1). *)
Hypothesis W_kind_of_link1 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  AR_laws SEGS B -> tkind_of_link1_spec (SK:=asan_ubsan_sink_head) (PI:=PI_scene) B.
(* reac_ctrl_checksum_verify 0x839e8 (a Theorem Labs lane's A/Prog/P_reac_ctrl_checksum_verify.v:111-112, :239). *)
Hypothesis W_reac_ctrl_checksum_verify : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  AR_laws SEGS B -> PALib (L:=scene_listing) (PI:=PI_scene) B ->
  tctrl_checksum_verify_spec (SK:=asan_ubsan_sink_head) (PI:=PI_scene) B.
(* reac_ctrl_parse 0x84028: kind_of_link1; __asan_memset, __asan_memcpy x2, __wrap_bcmp; class-1 fake frame. Its
   asan-ubsan contract is AU/Prog/P_reac_ctrl_parse.v tctrl_parse_spec (a Theorem Labs lane's text); the premises are the
   measured calls. *)
(* R3 (a Theorem Labs lane's GLUE-REVIEW.md), from before the walk's premises were stated: the hypothesis takes EVERY law the glue
   holds as well as the measured calls, so that the owner's walk implies it; G_Close.v:419-423 discharges it with that walk (AU/Prog/CtrlParse.v:88 pb_ctrl_parse). *)
Hypothesis W_reac_ctrl_parse : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  AR_laws SEGS B -> model_laws (as_universe B) ->
  PALib (L:=scene_listing) (PI:=PI_scene) B -> PALibF (L:=scene_listing) (PI:=PI_scene) B ->
  frame_flag_lawP SEGS B -> ro_below_ofl (SK:=asan_ubsan_sink_head) SEGS RLO RHI ->
  tkind_of_link1_spec (SK:=asan_ubsan_sink_head) (PI:=PI_scene) B ->
  aintrin_realizes SEGS B OCpy (SIGMA SS___asan_memcpy) -> aintrin_realizes SEGS B OSet (SIGMA SS___asan_memset) ->
  abcmp_realizes SEGS B (SIGMA SS___interceptor_trampoline_bcmp) -> astack_malloc_realizes SEGS B 1 ->
  astack_free_law SEGS B ->
  tctrl_parse_spec (SK:=asan_ubsan_sink_head) (PI:=PI_scene) B.
(* check_step 0x83294: a Theorem Labs lane's pb_check_stepX (AU/P_check_step.v, at 722526c3436; the asan
   text's A/P_check_step.v:108-151),
   its premises in its order; the sink head is its explicit Context SK (:64). *)
Hypothesis W_check_step : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  ro_below_ofl (SK:=asan_ubsan_sink_head) SEGS RLO RHI ->
  model_laws (as_universe B) ->
  PALib (L:=scene_listing) (PI:=PI_scene) B -> PALibF (L:=scene_listing) (PI:=PI_scene) B ->
  astack_free_law SEGS B -> frame_flag_lawP SEGS B ->
  astack_malloc_realizes SEGS B CS_CID -> aintrin_realizes SEGS B OCpy (SIGMA SS___asan_memcpy) ->
  abcmp_realizes SEGS B (SIGMA SS___interceptor_trampoline_bcmp) ->
  Exists (zr_sub (A_CS_TRAILER (PI:=PI_scene), 8)) (as_zero_shadow B) ->
  Exists (zr_sub (A_CS_CFRAME (PI:=PI_scene), 48)) (as_zero_shadow B) ->
  (forall ly,
    In (z1 (ANum (shadow_addr (A_CS_TRAILER (PI:=PI_scene)) + 1)) 4) (as_const B ly) /\
    In (z1 (ANum (shadow_addr (A_CS_TRAILER (PI:=PI_scene)) + 2)) 0xf9) (as_const B ly) /\
    In (z1 (ANum (shadow_addr (A_CS_TRAILER (PI:=PI_scene)) + 3)) 0xf9) (as_const B ly) /\
    In (z1 (ANum (shadow_addr (A_CS_CFRAME (PI:=PI_scene)) + 6)) 2) (as_const B ly) /\
    Forall (fun i => In (z1 (ANum (shadow_addr (A_CS_CFRAME (PI:=PI_scene)) + i)) 0xf9) (as_const B ly)) [7; 8; 9; 10; 11]) ->
  A_CS_TRAILER (PI:=PI_scene) = 0x20d80 /\ A_CS_CFRAME (PI:=PI_scene) = 0x20da0 ->
  ro_bytes SEGS RLO RHI B (A_CS_TRAILER (PI:=PI_scene)) scene_trailer ->
  ro_bytes SEGS RLO RHI B (A_CS_CFRAME (PI:=PI_scene)) cs_frame_init ->
  tctrl_parse_spec (SK:=asan_ubsan_sink_head) (PI:=PI_scene) B ->
  tctrl_checksum_verify_spec (SK:=asan_ubsan_sink_head) (PI:=PI_scene) B ->
  tcheck_step_specX asan_ubsan_sink_head (PI:=PI_scene) B.
(* A Theorem Labs lane's three callees (STMT-*.md): reac_ctrl_build_scene_step 0x83a70 (__asan_memset, __asan_memcpy x2, the
   stamp), reac_ctrl_scene_build 0x83e58 (__asan_memset, __asan_memcpy), reac_ctrl_scene_set_mac 0x83e04
   (__asan_memcpy); premises AR_laws, PALib, OSet, OCpy as a Theorem Labs lane states them. *)
(* reac_ctrl_block_cksum_stamp 0x83930 (out of line in this image, PROGFNS.md section 2): a Theorem Labs lane's
   pb_reac_ctrl_block_cksum_stamp (AU/P_cksum_stamp.v:289-290, :418), caller-journal form (:273). *)
Hypothesis W_reac_ctrl_block_cksum_stamp : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  AR_laws SEGS B -> PALib (L:=scene_listing) (PI:=PI_scene) B ->
  treac_ctrl_block_cksum_stamp_spec (SK:=asan_ubsan_sink_head) (PI:=PI_scene) B.
Hypothesis W_reac_ctrl_build_scene_step : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  AR_laws SEGS B -> PALib (L:=scene_listing) (PI:=PI_scene) B ->
  aintrin_realizes SEGS B OSet (SIGMA SS___asan_memset) -> aintrin_realizes SEGS B OCpy (SIGMA SS___asan_memcpy) ->
  treac_ctrl_block_cksum_stamp_spec (SK:=asan_ubsan_sink_head) (PI:=PI_scene) B ->
  treac_ctrl_build_scene_step_spec (SK:=asan_ubsan_sink_head) (PI:=PI_scene) B.
(* A Theorem Labs lane's pb_reac_ctrl_scene_build (AU/P_reac_ctrl_scene_build.v:277-280, :834) and
   pb_reac_ctrl_scene_set_mac (AU/P_reac_ctrl_scene_set_mac.v:180-181, :210), premises in their order. *)
Hypothesis W_reac_ctrl_scene_build : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  AR_laws SEGS B -> PALib (L:=scene_listing) (PI:=PI_scene) B ->
  aintrin_realizes SEGS B OSet (SIGMA SS___asan_memset) -> aintrin_realizes SEGS B OCpy (SIGMA SS___asan_memcpy) ->
  treac_ctrl_scene_build_spec (SK:=asan_ubsan_sink_head) (PI:=PI_scene) B.
Hypothesis W_reac_ctrl_scene_set_mac : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  AR_laws SEGS B -> aintrin_realizes SEGS B OCpy (SIGMA SS___asan_memcpy) ->
  treac_ctrl_scene_set_mac_spec (SK:=asan_ubsan_sink_head) (PI:=PI_scene) B.
(* LLVMFuzzerTestOneInput 0x828a4: a Theorem Labs lane's scene_llvmf_stmt (AU/P_LLVMFuzzerTestOneInput.v:312-315 at
   f6ab6e97937) under its Section premises (:180-316) in their order, concluding a Theorem Labs lane's scene_tfib_lib_contract_x
   (AU/P_LLVMFuzzerTestOneInput_ctx.v:173) at the one sink head asan_ubsan_sink_head. *)
Hypothesis W_LLVMFuzzerTestOneInput : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  ro_below_ofl (SK:=asan_ubsan_sink_head) SEGS RLO RHI ->
  A_LLVMF = BASE + AF_LLVMFuzzerTestOneInput -> RA_LLVMF = 0x827a0 -> A_EMPTY = 0x5d6160 ->
  6 <= EV_LIB -> 2 * 65535 <= LIVE_LIB -> 240 + ASTACK <= LLVMF_STK -> 240 + TCHECK_STEP_STK <= LLVMF_STK ->
  (forall i, 0 <= i < 12 ->
     ~ Exists (in_zr (0x20e20 + i)) (as_owned_static B) /\ ~ (as_errno B <= 0x20e20 + i < as_errno B + 4)) ->
  (forall i, 0 <= i < LLVMF_SCENE_BYTES ->
     ~ Exists (in_zr (A_reac_scene_placeholder + i)) (as_owned_static B) /\
     ~ (as_errno B <= A_reac_scene_placeholder + i < as_errno B + 4)) ->
  (forall i, 0 <= i < 8 ->
     ~ Exists (in_zr (VAL (A_OBJ 4) + i)) (as_owned_static B) /\ ~ (as_errno B <= VAL (A_OBJ 4) + i < as_errno B + 4)) ->
  PALib (L:=scene_listing) (PI:=PI_scene) B -> PALibF (L:=scene_listing) (PI:=PI_scene) B ->
  model_laws (as_universe B) -> frame_flag_lawP SEGS B ->
  sink_img_laws SEGS B g_SINK_OWNED ->
  in_zs B 0x20e80 8904 ->
  (forall ly, Forall (fun c => In c (as_const B ly)) g_PL_SHCELLS) ->
  in_zs B (A_TAIL_TRAILER - 0x20) (0x20 + (TAIL_TRAILER_N - TAIL_TRAILER_N mod 8)) ->
  (forall ly, Forall (fun c => In c (as_const B ly)) g_TT_SHCELLS) ->
  amalloc_realizes SEGS B -> afree_realizes SEGS B ->
  aintrin_realizes SEGS B OSet (SIGMA SS___asan_memset) -> aintrin_realizes SEGS B OCpy (SIGMA SS___asan_memcpy) ->
  abcmp_realizes SEGS B (SIGMA SS___interceptor_trampoline_bcmp) ->
  astack_malloc_sz_realizes SEGS B StackMalloc8Tbl.PC_STACK_MALLOC_8 StackMalloc8Tbl.CID8 ->
  StackFreeDef.astack_free_realizes SEGS B (SIGMA SS___asan_stack_free_8) 8 ->
  SetShadowDef.aset_shadow_realizes SEGS B (SIGMA SS___asan_set_shadow_00) 0 ->
  SetShadowDef.aset_shadow_realizes SEGS B (SIGMA SS___asan_set_shadow_f8) 0xf8 ->
  treac_ctrl_build_scene_step_spec (SK:=asan_ubsan_sink_head) (PI:=PI_scene) B ->
  treac_ctrl_scene_build_spec (SK:=asan_ubsan_sink_head) (PI:=PI_scene) B ->
  treac_ctrl_scene_set_mac_spec (SK:=asan_ubsan_sink_head) (PI:=PI_scene) B ->
  tcheck_step_specX asan_ubsan_sink_head (PI:=PI_scene) B ->
  rt_trace_in_stmt SEGS RA_LLVMF (pc_malloc_ra0 (as_code B)) (pc_free_ra0 (as_code B))
    g_RT_malloc1_ra g_RT_malloc2_ra g_RT_malloc3_ra g_RT_free1_ra g_RT_free2_ra g_RT_free3_ra (as_universe B) ->
  g_contract rc fx A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY B ameter_triv g_XL0 g_XL0 RLO RHI.
(* The driver's leaves, at the FP state fx0 (A/AD2o.v:24, :41-62). *)
#[local] Existing Instance YK11.fx0.
Hypothesis AICPY : forall rc : YM05.RunCeil, aintrin_realizes SEGS B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis ARDCHK : forall rc : YM05.RunCeil, aread_check rc B.
Hypothesis XFR : forall rc : YM05.RunCeil, xst_frame rc xst.
Hypothesis PF1 : forall rc : YM05.RunCeil, printf_first rc B xst.
Hypothesis PFN : forall rc : YM05.RunCeil, printf_next rc B xst.
Hypothesis ESTI : forall rc : YM05.RunCeil, est_img rc est.
Hypothesis ESTF : forall rc : YM05.RunCeil, est_frame rc est.
Hypothesis FWS : forall rc : YM05.RunCeil, fwrite_site rc B est.
Hypothesis RFS : forall rc : YM05.RunCeil, refused_site rc B est.
Hypothesis FPO : forall rc : YM05.RunCeil, fprintf_s_site rc B est 0x1d69c (strB "cli: cannot open "%string) nlB.
Hypothesis FPR : forall rc : YM05.RunCeil, fprintf_s_site rc B est 0x1d6b1 (strB "cli: read error on "%string) nlB.
Hypothesis FPU : forall rc : YM05.RunCeil,
  fprintf_s_site rc B est 0x157fc (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
(* EXS: the core's exit-site type, AU/YD1x.v:94-110 exit_site_tfa, at fx0 and rc. *)
Hypothesis EXS : forall rc : YM05.RunCeil, YD1x.exit_site_tfa B est xst.
(* Start-up (AU/YB1n.v:51 tfib_startup_T1), hand-off (G_Drv.v g_hs_open), driver walk (AU/YD1p.v:84 tfib_drv_main);
   G_Close.v closes STARTUP and DRV by these. *)
Hypothesis STARTUP : forall rc : YM05.RunCeil, g_startup_stmt TF HS.

Hypothesis DRV : forall rc : YM05.RunCeil,
  g_drv_walk_stmt TF HS 0x1d69c 0x1d6b1 0x157fc A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY
    g_contract TS (in_roP SEGS RLO RHI) (aread_check rc) (xst_frame rc) (printf_first rc)
    (printf_next rc) (est_img rc) (est_frame rc) (fwrite_site rc) (refused_site rc) (fprintf_s_site rc)
    (fun B' est' xst' => YD1x.exit_site_tfa B' est' xst').
Section RC. Context {rc : YM05.RunCeil}.
(* A/AD2o.v:45-46 LIBX (the _all form of A/ACfn.v:71-72, built as A/ACfi.v:139 builds it), from the program walks. *)
Lemma g_libx : forall fx : YK11.FPState,
  g_contract rc fx A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY B ameter_triv g_XL0 g_XL0 RLO RHI.
Proof.
  intros fx.
  pose proof (AR_laws_ok SEGS B) as LAWS.
  exact (W_LLVMFuzzerTestOneInput rc fx (g_RO rc fx) (g_HA_LLVMF rc fx) eq_refl eq_refl
    HEV HLIVE HSTK HSTK_CS HRO_TT (HRO_PL rc fx) (HRO_PLGOT rc fx) (TL rc fx) (TLF rc fx) ML (g_FFL rc fx) (g_sink_img_laws rc fx) (HZS_PL rc fx) HB_C_PL (HB_Z_TT rc fx) HB_C_TT
    (AMALLOC rc fx) (AFREE rc fx) (AMEMSET rc fx) (AMEMCPY rc fx) (ABCMP rc fx)
    (stack_malloc_8_sz rc fx) (ASF8 rc fx) (ASH00 rc fx) (ASHF8 rc fx)
    (W_reac_ctrl_build_scene_step rc fx LAWS (TL rc fx) (AMEMSET rc fx) (AMEMCPY rc fx)
       (W_reac_ctrl_block_cksum_stamp rc fx LAWS (TL rc fx)))
    (W_reac_ctrl_scene_build rc fx LAWS (TL rc fx) (AMEMSET rc fx) (AMEMCPY rc fx))
    (W_reac_ctrl_scene_set_mac rc fx LAWS (AMEMCPY rc fx))
    (W_check_step rc fx (g_RO rc fx) ML (TL rc fx) (TLF rc fx) (g_ASF rc fx) (g_FFL rc fx) (ASM2 rc fx)
       (AMEMCPY rc fx) (ABCMP rc fx) (HB_Z_TR rc fx) (HB_Z_CF rc fx) (HB_C_CS rc fx) (g_HB_ADDR rc fx) (HRO_TR rc fx)
       (HRO_CF rc fx)
       (W_reac_ctrl_parse rc fx LAWS ML (TL rc fx) (TLF rc fx) (g_FFL rc fx) (g_RO rc fx)
          (W_kind_of_link1 rc fx LAWS) (AMEMCPY rc fx) (AMEMSET rc fx) (ABCMP rc fx) (ASM1 rc fx) (g_ASF rc fx))
       (W_reac_ctrl_checksum_verify rc fx LAWS (TL rc fx)))
    (HTRACE rc fx)).
Qed.
(* A/AD2o.v:63-74 tfib_srealizesX_rc. *)
Lemma g_srealizesX_rc : forall sp rdraw brk mb inp,
  valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
  srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp)
    (SPECX (LS:=SceneAsanBase.scene_shape) inp).
Proof.
  intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
  change target_alloc_limit with YA02.LIMIT.
  exact (@g_srealizes rc TF HS 0x1d69c 0x1d6b1 0x157fc A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY
    g_contract TS (in_roP SEGS RLO RHI) (aread_check rc) (xst_frame rc) (printf_first rc)
    (printf_next rc) (est_img rc) (est_frame rc) (fwrite_site rc) (refused_site rc) (fprintf_s_site rc)
    (fun B' est' xst' => YD1x.exit_site_tfa B' est' xst')
    B HB (AMALLOC rc YK11.fx0) (AFREE rc YK11.fx0) (AICPY rc) (ARDCHK rc) ameter_triv g_XL0 g_XL0 RLO RHI
    (fun _ _ => I) (g_RO_IN rc YK11.fx0) g_libx
    xst (XFR rc) (PF1 rc) (PFN rc) est (ESTI rc) (ESTF rc) (FWS rc) (RFS rc) (FPO rc) (FPR rc) (FPU rc) (EXS rc)
    (STARTUP rc) (DRV rc) sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil).
Qed.
End RC.
(* YD2o.v:70-77 tfib_srealizesX_top. *)
Theorem g_srealizesX_top : forall sp rdraw brk mb inp,
  valid_sp sp -> valid_brk TSEGS brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  srealizes TSEGS (init_config TSEGS AsanUbsan.M.init_pc TPH sp brk mb rdraw target_alloc_limit inp)
    (SPECX (LS:=SceneAsanBase.scene_shape) inp).
Proof.
  intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp.
  exact (@g_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (g_valid_sp_window sp Hsp)) sp rdraw brk mb inp
    Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.
(* YD2o.v:78-79 TFIB_T_of_partsXF, YD2p.v:11-17. *)
Theorem ASAN_UBSAN_T_of_glue : SceneAsanTop.ASAN_UBSAN_T.
Proof.
  intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
  exact (g_srealizesX_top sp rnd brk mbase inp Hsp Hbrk Hmb Hfit Hinp).
Qed.
End g.
About ASAN_UBSAN_T_of_glue.
Print Assumptions ASAN_UBSAN_T_of_glue.
