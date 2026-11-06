(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YD2p.v and YD2o.v (the closing of
   TFIB_T from its parts) for fuzz_scene's asan-ubsan image, in the form of fuzz_pcap's lib/A/PcapClose.v
   (a working branch fe3d720b4c7); module paths changed. *)
(* The closing of fuzz_scene's asan-ubsan statements (rule 24: no function proved; this file is assembly).
   SceneAsanTop.ASAN_UBSAN_T and Statements.asan_ubsan_agrees / asan_ubsan_halts follow from ASAN_UBSAN_T_of_glue (G_Top.v)
   applied to these instances: the budgets EV_LIB 2000, LIVE_LIB 2^33,
   LLVMF_STK 32768 (cgif A/ACfn.v:23-25; their four bounds by vm_compute), the owners' PROVED walks
   pb_kind_of_link1 and pb_ctrl_checksum_verify (a Theorem Labs lane c2fc5d41458), pb_check_stepX (a Theorem Labs lane 722526c3436, Qed in
   both images), pb_reac_ctrl_build_scene_step / pb_reac_ctrl_scene_build / pb_reac_ctrl_scene_set_mac / pb_reac_ctrl_block_cksum_stamp
   (a Theorem Labs lane a0866e7f49c), pb_ctrl_parse (a Theorem Labs lane c2fc5d41458 lib/AU/Prog/CtrlParse.v), and B's static facts
   at the CONCRETE B := YD2l.TfibB (a Theorem Labs lane d7f9043aaa7), whose tables are TS := YF0m.TfibSyms (a Theorem Labs lane
   e503e4f4264) and HB := YD2l.TfibB_syms; so B, TS and HB are not rows. A Theorem Labs lane's certificate lib/AU/SceneBCertU.v
   (c7fbc8da541), at B := TfibB, gives HZS_PL, HB_C_PL, HB_Z_TT, HB_C_TT, HB_Z_TR, HB_Z_CF, HB_C_CS and the parse walk's
   HGM / HIMGSH; ML is the donor's link_ML (A/ACfi.v:72-73); TL / TLF (PALib / PALibF; TLF's palf_sm8 field is a Theorem Labs lane's
   ScenePalfSm8.scene_palf_sm8, c3131b23386), HRO_TT / HRO_PL / HRO_PLGOT, HRO_TR / HRO_CF and the parse walk's
   HG15 / HBC_RNG / HBC_VAL are decided by vm_compute on TfibB and the image
   (a Theorem Labs lane's P_check_step_cut.v: "decided at the closing by vm_compute").
   On the restaged core (at 58c9f2eb390) every row is closed by a named term at the call site
   of ASAN_UBSAN_T_of_rows, or by a Let: AMEMSET / AMEMCPY / ABCMP by SceneIntrin.scene_AMEMSET / _AMEMCPY /
   _ABCMP (a Theorem Labs lane) at B := TfibB, HB := TfibB_syms; HTRACE by SceneTrace.scene_HTRACE (a Theorem Labs lane);
   stack_malloc_8_sz / ASF8 / ASH00 / ASHF8 by G_RowsU.p_stack_malloc_8_sz / p_ASF8 / p_ASH00 / p_ASHF8 (a Theorem Labs lane's
   proofs, at a423d9a58b9); AIL by G_SinkSub.scene_AIL; W_LLVMFuzzerTestOneInput by
   AU/P_LLVMFuzzerTestOneInput_Closed.v scene_llvmf_closed. The nine driver site types
   (aread_check, xst_frame, printf_first, printf_next, est_img, est_frame, fwrite_site, refused_site, fprintf_s_site)
   are Lets bound to their relocated Definitions (YD1i.v aread_check_stmt, YD1w.v xst_frame_tfa / printf_first_tfa /
   printf_next_tfa, YD1x.v est_img_tfa / est_frame_tfa / fwrite_site_tfa / refused_site_tfa / fprintf_s_site_tfa) at
   fx0, each with the type of the Variable it replaces. ASM1 / ASM2 close by YF0s.stack_malloc1_contract /
   YF0u.stack_malloc2_contract (CS_CID = 2) with AR_laws_ok and HB. A Theorem Labs lane's rows,
   ROWMAP.md (sha256 514eab570203; internal record), close by
   the core's terms: TF / HS / xst / est are Lets bound to YB12.TFIB, YB01.HS_tfib, YD1k.xst, YD1k.est; AICPY /
   ARDCHK by YD2m.tfib_AICPY / tfib_ARDCHK; XFR / ESTI / ESTF / FWS / RFS by YD1k.tfib_xst_frame / tfib_est_img /
   tfib_est_frame / tfib_fwrite_site / tfib_refused_site; PF1 / PFN by YD1o.tfib_printf_first / tfib_printf_next;
   STARTUP by YB1n.tfib_startup_T1; EXS, now the core's YD1x.exit_site_tfa (G_Top.v), by YD1j.tfib_exit_site. The
   exit site's image parts IMG_X / IMG_XL / stdout_img are the core's, inside exit_site_tfa, so they are rows no more.
   AMALLOC / AFREE close by a Theorem Labs lane's SceneAlloc.scene_AMALLOC / scene_AFREE. FPO / FPR / FPU close by
   YD1l.tfib_fprintf_open_site / _rderr_site / _usage_site, and DRV by YD1p.tfib_drv_main at LS := scene_shape.
   No Section Variable or Hypothesis is left (the Lets are definitions). Every owner sha the closing terms come from is
   in records/libreac-fuzz_scene/glue/G_OWNERS.md on the glue branch. Print Assumptions at the end lists the kernel's primitives,
   FunctionalExtensionality.functional_extensionality_dep (the owners' proved walks) and Classical_Prop.classic
   (through SceneAsanTop's *_of_asan_side and through SceneAlloc.scene_AFREE, over YF0q). *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_scene Require Statements.
From OSSVerify.libreac.fuzz_scene.images Require Import AsanUbsan.
(* Required first, so that the short names below resolve to lib/Reusable (scene's released tree also has
   lib/U/Reusable twins of some of them). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require SceneAsanTop.
(* Gate 6h: no sink-head instance is in scope (lib/Reusable/SinkGuard.v removes the released src0 instances). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require SinkGuard.
(* The closing terms of the restaged core, Required (not imported) and used by qualified name: a Theorem Labs lane's
   SceneIntrin.v / SceneTrace.v, the driver's relocated site types YD1i.v / YD1w.v / YD1x.v, the closed entry walk
   P_LLVMFuzzerTestOneInput_Closed.v, and the glue's G_RowsU.v (a Theorem Labs lane's proofs) and G_SinkSub.v. Required here,
   before the short names below, so that those short names still resolve as gate 6o places them. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require SceneIntrin SceneTrace YD1i YD1w YD1x.
(* A Theorem Labs lane's start-up and driver leaves (ROWMAP.md), from the restaged core: YB12 (TFIB), YB01 (HS_tfib), YB1n
   (tfib_startup_T1), YD1k (xst, est and the stderr / xst-frame leaves), YD1o (the printf leaves), YD1j
   (tfib_exit_site), YD2m (tfib_AICPY, tfib_ARDCHK). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require YB12 YB01 YB1n YD1k YD1o YD1j YD2m.
(* The restage's fourth commit 58c9f2eb390: YD1l (the three fprintf sites), YD1p (the driver walk tfib_drv_main),
   YF0s / YF0u (the class-1 / class-2 fake-frame contracts), SceneAlloc (scene_AMALLOC, scene_AFREE; a Theorem Labs lane,
   at 5387e903a6ae) and the closed entry walk P_LLVMFuzzerTestOneInput_Closed (scene_llvmf_closed). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require YD1l YD1p YF0s YF0u SceneAlloc P_LLVMFuzzerTestOneInput_Closed.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require G_RowsU G_SinkSub.
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
   P_reac_ctrl_parse.v, at c2fc5d41458), a Theorem Labs lane's check_step (AU/P_check_step*.v
   at 722526c3436), the glue's sink
   laws (G_Sink.v), and a Theorem Labs lane's asan-ubsan entry contract and statement (below). *)
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
   TAIL_TRAILER_N (AU :151-152), which HB_Z_TT names (at f6ab6e97937). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput_ctx.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_LLVMFuzzerTestOneInput.
(* A Theorem Labs lane's start-up record and certificate (SceneBCertU.v at c7fbc8da541; YF0m.v at
   e503e4f4264): TfibSyms (YF0m.v:906-930)
   and the lemmas of SceneBCertU.v over `HB : TfibSyms B`. Required, not imported: they are used by qualified name. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require YF0m SceneBCertU.
(* A Theorem Labs lane's concrete start-up record (at d7f9043aaa7): YD2l.TfibB and YD2l.TfibB_syms : TfibSyms TfibB,
   over YF0m.v (a Theorem Labs lane e503e4f4264) and its measured trace universe (a Theorem Labs lane 1c79108a270). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require YD2l.
(* A Theorem Labs lane's proved parse walk (at c2fc5d41458 lib/AU/Prog/CtrlParse.v pb_ctrl_parse;
   CtrlParseCut.OBJ_BCAST = 15, .str.4). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require CtrlParse.
(* A Theorem Labs lane's palf_sm8 lemma (at c3131b23386 lib/AU/ScenePalfSm8.v). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require ScenePalfSm8.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import G_Drv G_Top.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
#[local] Abbreviation TSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation TPH := AsanUbsan.M.phdrs.
#[local] Abbreviation SEGS := (@pa_segs _ scene_listing PI_scene).
#[local] Abbreviation VAL := (@pa_val _ scene_listing PI_scene).
#[local] Abbreviation SIGMA := (@pa_sigma _ scene_listing PI_scene).
#[local] Abbreviation BASE := (@pa_val _ scene_listing PI_scene A_TEXT).
#[local] Abbreviation RLO := (@pa_relro_lo _ scene_listing PI_scene).
#[local] Abbreviation RHI := (@pa_relro_hi _ scene_listing PI_scene).
(* The program contract's budgets, at cgif A/ACfn.v:23-25's values. *)
Definition EV_LIB : Z := 2000.
Definition LIVE_LIB : Z := 2 ^ 33.
Definition LLVMF_STK : Z := 32768.
(* HRO_TR / HRO_CF (and the like) as one boolean check per byte (rule 24: no function is walked; this decides a static
   fact of the image and of B, as a Theorem Labs lane's AU/P_check_step_cut.v:88-89 intends). g_ro_ok is ro_bytes' four clauses at
   one address, with the owned list and the errno cell given as numbers. *)
Definition g_ro_ok (segs : list Segment) (rlo rhi : Z) (own : list (Z * Z)) (errno a b : Z) : bool :=
  ((existsb (fun s : Segment => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a)
                                && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs
    || ((rlo <=? a) && (a <? rhi)))
   && negb (existsb (fun r : Z * Z => (fst r <=? a) && (a <? fst r + snd r)) own)
   && negb ((errno <=? a) && (a <? errno + 4))
   && match seg_rom segs (Z_to_bv 64 a) with Some x => bv_unsigned x =? b | None => false end)%bool.
Lemma g_ro_ok_sound : forall segs rlo rhi B a b,
  g_ro_ok segs rlo rhi (as_owned_static B) (as_errno B) a b = true ->
  in_roP segs rlo rhi a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\
  option_map (fun x : byte => bv_unsigned x) (seg_rom segs (Z_to_bv 64 a)) = Some b.
Proof.
  intros segs rlo rhi B a b H. unfold g_ro_ok in H.
  apply andb_prop in H as [H Hrom]. apply andb_prop in H as [H Herr]. apply andb_prop in H as [Hro Hown].
  split; [|split; [|split]].
  - apply orb_prop in Hro as [Hs | Hw].
    + left. apply existsb_exists in Hs as (s & Hin & Hs).
      apply andb_prop in Hs as [Hs H2]. apply andb_prop in Hs as [Hw H1].
      apply negb_true_iff in Hw. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
      exists s. split; [exact Hin|]. split; [exact Hw|]. lia.
    + right. apply andb_prop in Hw as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
  - intro HE. apply Exists_exists in HE as (r & Hin & Hr). unfold in_zr in Hr.
    apply negb_true_iff in Hown.
    assert (Hb : existsb (fun r : Z * Z => (fst r <=? a) && (a <? fst r + snd r))%bool (as_owned_static B) = true).
    { apply existsb_exists. exists r. split; [exact Hin|].
      apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    rewrite Hb in Hown. discriminate Hown.
  - intro HE. apply negb_true_iff in Herr.
    assert (Hb : ((as_errno B <=? a) && (a <? as_errno B + 4))%bool = true).
    { apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    rewrite Hb in Herr. discriminate Herr.
  - destruct (seg_rom segs (Z_to_bv 64 a)) as [x|]; [|discriminate Hrom].
    apply Z.eqb_eq in Hrom. cbn. rewrite Hrom. reflexivity.
Qed.
Lemma g_ro_bytes_of_chk : forall segs rlo rhi B a l,
  forallb (fun i => g_ro_ok segs rlo rhi (as_owned_static B) (as_errno B) (a + i)
                      (bv_unsigned (nth (Z.to_nat i) l (Z_to_bv 8 0))))
    (map Z.of_nat (seq 0 (length l))) = true ->
  ro_bytes segs rlo rhi B a l.
Proof.
  intros segs rlo rhi B a l H. unfold ro_bytes. intros i Hi.
  apply g_ro_ok_sound.
  refine (proj1 (forallb_forall _ _) H i _).
  apply in_map_iff. exists (Z.to_nat i). split.
  - apply Z2Nat.id. lia.
  - apply in_seq. lia.
Qed.
(* HRO_TT / HRO_PL / HRO_PLGOT's shape (a Theorem Labs lane's minimal form): [a, a + n) lies in no owned-static range and avoids
   the errno cell, from one boolean check per byte (rule 24: a static fact of B, decided by computation). *)
Lemma g_not_owned_errno : forall B a n,
  forallb (fun i => negb (existsb (fun r : Z * Z => (fst r <=? a + i) && (a + i <? fst r + snd r)) (as_owned_static B))
                    && negb ((as_errno B <=? a + i) && (a + i <? as_errno B + 4)))%bool
          (map Z.of_nat (seq 0 (Z.to_nat n))) = true ->
  forall i, 0 <= i < n -> ~ Exists (in_zr (a + i)) (as_owned_static B) /\ ~ (as_errno B <= a + i < as_errno B + 4).
Proof.
  intros B a n C i Hi.
  assert (Hin : In i (map Z.of_nat (seq 0 (Z.to_nat n)))).
  { apply in_map_iff. exists (Z.to_nat i). split; [apply Z2Nat.id; lia | apply in_seq; lia]. }
  pose proof (proj1 (forallb_forall _ _) C i Hin) as Ci. cbv beta in Ci.
  apply andb_prop in Ci as [Hown Herr]. apply negb_true_iff in Hown. apply negb_true_iff in Herr.
  split.
  - intro HE. apply Exists_exists in HE as (r & Hr & Hz). unfold in_zr in Hz.
    assert (Hb : existsb (fun r : Z * Z => (fst r <=? a + i) && (a + i <? fst r + snd r))%bool (as_owned_static B) = true).
    { apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    rewrite Hb in Hown. discriminate Hown.
  - intro HE. assert (Hb : ((as_errno B <=? a + i) && (a + i <? as_errno B + 4))%bool = true).
    { apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    rewrite Hb in Herr. discriminate Herr.
Qed.
Section close.
(* B is a Theorem Labs lane's concrete record YD2l.TfibB (donor A/AD2l.v:14 TfibB); TS is YF0m.TfibSyms; HB is
   YD2l.TfibB_syms. None of the three is a row. *)
#[local] Notation B := YD2l.TfibB (only parsing).
#[local] Notation HB := YD2l.TfibB_syms (only parsing).
(* The nine driver site types (donor A/AD1i.v:19, A/AD1w.v:120 / :145 / :152, A/AD1x.v:37 / :38 / :57 / :83 / :69;
   asan-ubsan twins YD1i.v / YD1w.v / YD1x.v) and a Theorem Labs lane's TF / HS / xst / est are rows no more: each is a Let
   below the fx0 instance, bound to the core's Definition. The exit site's image parts (IMG_X / IMG_XL / stdout_img)
   are inside the core's exit_site_tfa. *)
(* TL: donor (scene) ScenePaLib.v:307 PALib; cgif A/ACk1.v:64-74. Proved below at B := TfibB (g_TL), by computation. *)
(* TLF: donor (scene) SceneFrame.v:102 PALibF (a Theorem Labs lane 8df4a950395: palf_sm8 = StackMalloc8Tbl.PC_STACK_MALLOC_8); cgif
   A/ACk1.v:82. Proved below at B := TfibB (g_TLF), by computation. *)
(* AIL (donor A/AD1u.v:34 tfib_AIL over A/AE2k.v's record; a Theorem Labs lane's YE01.v:28-40 asink_img_laws at G_Sink.scene_K) is
   a row no more: G_SinkSub.scene_AIL at the concrete B, passed at the call site of ASAN_UBSAN_T_of_rows. *)
(* ---- The B facts, at the concrete B := YD2l.TfibB (rule 24: no function is walked; each is a static fact). ---- *)
(* ML: the donor's A/ACfi.v:72-73 link_ML, from TfibSyms' ts_universe and YG05.v:138 model_laws_ok. *)
Lemma g_ML : model_laws (as_universe B).
Proof. exact (model_laws_ok (as_universe B) (YF0m.ts_universe B HB)). Qed.
(* HZS_PL (a Theorem Labs lane f6ab6e97937 AU/P_LLVMFuzzerTestOneInput.v:267): SceneBCertU.v scene_zs_placeholder (a Theorem Labs lane c7fbc8da541). *)
Lemma g_HZS_PL : forall (rc : YM05.RunCeil) (fx : YK11.FPState), in_zs B 0x20e80 8904.
Proof. intros rc fx. exact (SceneBCertU.scene_zs_placeholder B HB). Qed.
(* HB_C_PL (AU/P_LLVMFuzzerTestOneInput.v:268): SceneBCertU.v:481 scene_c_pl (a Theorem Labs lane c7fbc8da541); g_PL_SHCELLS is its list with shadow_addr
   unfolded (shadow_addr (0x20e80 + 8904) = 0x7fffc629). *)
Lemma g_HB_C_PL : forall ly, Forall (fun c => In c (as_const B ly)) g_PL_SHCELLS.
Proof.
  intro ly.
  assert (E : g_PL_SHCELLS = map (fun k => z1 (ANum (0x7fffc629 + Z.of_nat k)) 0xf9) (seq 0 8)) by (vm_compute; reflexivity).
  rewrite E. exact (SceneBCertU.scene_c_pl B HB ly).
Qed.
(* HB_Z_TT (AU/P_LLVMFuzzerTestOneInput.v:269, its symbolic text): SceneBCertU.v:460 scene_z_tt (a Theorem Labs lane c7fbc8da541), the zero range (0x20e00, 0x28). *)
Lemma g_HB_Z_TT : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  in_zs B (A_TAIL_TRAILER - 0x20) (0x20 + (TAIL_TRAILER_N - TAIL_TRAILER_N mod 8)).
Proof. intros rc fx. exact (SceneBCertU.scene_z_tt B HB). Qed.
(* HB_C_TT (AU/P_LLVMFuzzerTestOneInput.v:270): SceneBCertU.v:416-423 scene_sh_kl1_p / _rz0 / _rz1. *)
Lemma g_HB_C_TT : forall ly, Forall (fun c => In c (as_const B ly)) g_TT_SHCELLS.
Proof.
  intro ly.
  assert (E : g_TT_SHCELLS = [z1 (ANum 0x7fffc1c5) 0x4; z1 (ANum 0x7fffc1c6) 0xf9; z1 (ANum 0x7fffc1c7) 0xf9])
    by (vm_compute; reflexivity).
  rewrite E.
  apply Forall_cons; [exact (SceneBCertU.scene_sh_kl1_p B HB ly)|].
  apply Forall_cons; [exact (SceneBCertU.scene_sh_kl1_rz0 B HB ly)|].
  apply Forall_cons; [exact (SceneBCertU.scene_sh_kl1_rz1 B HB ly)|].
  apply Forall_nil.
Qed.
(* HRO_TT / HRO_PL / HRO_PLGOT (the texts of AU/P_LLVMFuzzerTestOneInput.v:215-228 at f6ab6e97937): decided by
   vm_compute at B := TfibB (g_not_owned_errno): the trailer's 12 bytes, the placeholder's LLVMF_SCENE_BYTES = 8904
   bytes (not st_size 11136) and the GOT word VAL (A_OBJ 4) (0x9c6b8) lie in no Tfib_owned_static range and are not the
   errno cell. *)
Lemma g_HRO_TT : forall i, 0 <= i < 12 ->
  ~ Exists (in_zr (0x20e20 + i)) (as_owned_static B) /\ ~ (as_errno B <= 0x20e20 + i < as_errno B + 4).
Proof. apply g_not_owned_errno. vm_compute. reflexivity. Qed.
Lemma g_HRO_PL : forall (rc : YM05.RunCeil) (fx : YK11.FPState), forall i, 0 <= i < LLVMF_SCENE_BYTES ->
  ~ Exists (in_zr (A_reac_scene_placeholder + i)) (as_owned_static B) /\
  ~ (as_errno B <= A_reac_scene_placeholder + i < as_errno B + 4).
Proof. intros rc fx. apply g_not_owned_errno. vm_compute. reflexivity. Qed.
Lemma g_HRO_PLGOT : forall (rc : YM05.RunCeil) (fx : YK11.FPState), forall i, 0 <= i < 8 ->
  ~ Exists (in_zr (VAL (A_OBJ 4) + i)) (as_owned_static B) /\ ~ (as_errno B <= VAL (A_OBJ 4) + i < as_errno B + 4).
Proof. intros rc fx. apply g_not_owned_errno. vm_compute. reflexivity. Qed.
(* HB_Z_TR / HB_Z_CF (AU/P_check_step.v premises): SceneBCertU.v:439 scene_z_trailer / :444 scene_z_cframe, at
   g_HB_ADDR's 0x20d80 / 0x20da0. *)
Lemma g_HB_Z_TR : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  Exists (zr_sub (A_CS_TRAILER (PI:=PI_scene), 8)) (as_zero_shadow B).
Proof. intros rc fx. rewrite (proj1 (g_HB_ADDR rc fx)). exact (SceneBCertU.scene_z_trailer B HB). Qed.
Lemma g_HB_Z_CF : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  Exists (zr_sub (A_CS_CFRAME (PI:=PI_scene), 48)) (as_zero_shadow B).
Proof. intros rc fx. rewrite (proj2 (g_HB_ADDR rc fx)). exact (SceneBCertU.scene_z_cframe B HB). Qed.
(* HB_C_CS (AU/P_check_step.v premise): SceneBCertU.v:500 scene_cs_shadow, a Theorem Labs lane's shape, at g_HB_ADDR's addresses. *)
Lemma g_HB_C_CS : forall (rc : YM05.RunCeil) (fx : YK11.FPState) ly,
  In (z1 (ANum (shadow_addr (A_CS_TRAILER (PI:=PI_scene)) + 1)) 4) (as_const B ly) /\
  In (z1 (ANum (shadow_addr (A_CS_TRAILER (PI:=PI_scene)) + 2)) 0xf9) (as_const B ly) /\
  In (z1 (ANum (shadow_addr (A_CS_TRAILER (PI:=PI_scene)) + 3)) 0xf9) (as_const B ly) /\
  In (z1 (ANum (shadow_addr (A_CS_CFRAME (PI:=PI_scene)) + 6)) 2) (as_const B ly) /\
  Forall (fun i => In (z1 (ANum (shadow_addr (A_CS_CFRAME (PI:=PI_scene)) + i)) 0xf9) (as_const B ly)) [7; 8; 9; 10; 11].
Proof.
  intros rc fx ly. destruct (g_HB_ADDR rc fx) as [E1 E2]. rewrite E1, E2.
  exact (SceneBCertU.scene_cs_shadow B HB ly).
Qed.
(* HRO_TR / HRO_CF (AU/P_check_step.v premises): decided by vm_compute over the image and B's owned list / errno cell (MEASURED in
   the ELF as well: 00 00 03 00 00 00 01 00 00 00 00 00 at 0x20d80 and the 50-byte cs_frame_init at 0x20da0, both in
   the first, read-only PT_LOAD). *)
Lemma g_HRO_TR : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  ro_bytes SEGS RLO RHI B (A_CS_TRAILER (PI:=PI_scene)) scene_trailer.
Proof.
  intros rc fx. rewrite (proj1 (g_HB_ADDR rc fx)). apply g_ro_bytes_of_chk. vm_compute. reflexivity.
Qed.
Lemma g_HRO_CF : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  ro_bytes SEGS RLO RHI B (A_CS_CFRAME (PI:=PI_scene)) cs_frame_init.
Proof.
  intros rc fx. rewrite (proj2 (g_HB_ADDR rc fx)). apply g_ro_bytes_of_chk. vm_compute. reflexivity.
Qed.
(* HBC_VAL (a Theorem Labs lane's CtrlParse.v AU :82-83): the six 0xff bytes of listing object 15 (.str.4, 0x20e40, the
   bcmp operand of reac_ctrl_parse), from arodata_okP's image clause: each address is read-only, in no owned range,
   not the errno cell, and its ROM byte is 0xff (MEASURED in the ELF as well), one closed check per byte. *)
Lemma g_HBC_VAL : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (H : word -> bool) mem,
  arodata_okP SEGS RLO RHI B (aview SEGS H mem) ->
  forall i, 0 <= i < 6 -> aview SEGS H mem (VAL (A_OBJ CtrlParseCut.OBJ_BCAST) + i) = Some 255.
Proof.
  intros rc fx H mem Hok i Hi.
  assert (C : forallb (fun j => g_ro_ok SEGS RLO RHI (as_owned_static B) (as_errno B)
                                  (VAL (A_OBJ CtrlParseCut.OBJ_BCAST) + j) 255)
                (map Z.of_nat (seq 0 6)) = true) by (vm_compute; reflexivity).
  assert (Hin : In i (map Z.of_nat (seq 0 6))).
  { apply in_map_iff. exists (Z.to_nat i). split; [apply Z2Nat.id; lia | apply in_seq; lia]. }
  pose proof (proj1 (forallb_forall _ _) C i Hin) as Ci. cbv beta in Ci.
  destruct (g_ro_ok_sound _ _ _ B _ _ Ci) as (Hro & Hown & Herr & Hbyte).
  rewrite (Hok _ Hro Hown Herr). exact Hbyte.
Qed.
(* TL: PALib at B := TfibB, each field by computation on TfibB and PI_scene (pal_env through api_env's three parts). *)
Lemma g_TL : forall (rc : YM05.RunCeil) (fx : YK11.FPState), PALib (L:=scene_listing) (PI:=PI_scene) B.
Proof.
  intros rc fx. constructor.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - left. apply Z.leb_le. vm_compute. reflexivity.
  - split; [split; apply Z.leb_le; vm_compute; reflexivity|]. split.
    + intros a Ha.
      assert (C : forallb (fun i => existsb (fun s : Segment => (Z.of_N (seg_base s) <=? as_errno B + i)
                    && (as_errno B + i <? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool SEGS)
                    (map Z.of_nat (seq 0 4)) = true) by (vm_compute; reflexivity).
      assert (Hin : In (a - as_errno B) (map Z.of_nat (seq 0 4))).
      { apply in_map_iff. exists (Z.to_nat (a - as_errno B)). split; [apply Z2Nat.id; lia | apply in_seq; lia]. }
      pose proof (proj1 (forallb_forall _ _) C (a - as_errno B) Hin) as Ci. cbv beta in Ci.
      replace (as_errno B + (a - as_errno B)) with a in Ci by lia.
      apply existsb_exists in Ci as (s & Hs & Hb). apply andb_prop in Hb as [H1 H2].
      apply Z.leb_le in H1. apply Z.ltb_lt in H2.
      exists s. split; [exact Hs | lia].
    + split; apply YD2l.In_of_existsb; vm_compute; reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - split; apply Z.ltb_lt; vm_compute; reflexivity.
Qed.
(* TLF: PALibF at B := TfibB; palf_sm8 is StackMalloc8Tbl.PC_STACK_MALLOC_8 (a Theorem Labs lane 8df4a950395's ruled SceneFrame.v),
   given by a Theorem Labs lane's scene_palf_sm8; the other fields by computation. *)
Lemma g_TLF : forall (rc : YM05.RunCeil) (fx : YK11.FPState), PALibF (L:=scene_listing) (PI:=PI_scene) B.
Proof.
  intros rc fx. constructor.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - (* palf_sm8: a Theorem Labs lane's published lemma (ScenePalfSm8.v, at c3131b23386). *)
    exact ScenePalfSm8.scene_palf_sm8.
  - cbv [zseps zseps_from fst snd].
    repeat split; first [left; apply Z.leb_le; vm_compute; reflexivity | right; apply Z.leb_le; vm_compute; reflexivity].
Qed.
(* The parse walk's premises (a Theorem Labs lane's CtrlParse.v, AU :62-83) the glue holds at B := TfibB: G := SCENE_GLOBS (SceneBCertU.v:47),
   HGM / HIMGSH from SceneBCertU.v:561 / :547, HG15 and HBC_RNG by computation (object 15 is .str.4 at 0x20e40). *)
Lemma g_HG15 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  In (VAL (A_OBJ CtrlParseCut.OBJ_BCAST), 7) SceneBCertU.SCENE_GLOBS.
Proof.
  intros rc fx. assert (E : VAL (A_OBJ CtrlParseCut.OBJ_BCAST) = 0x20e40) by (vm_compute; reflexivity).
  rewrite E. exact SceneBCertU.scene_glob_str4.
Qed.
Lemma g_HBC_RNG : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  0x10000 + 64 <= VAL (A_OBJ CtrlParseCut.OBJ_BCAST) /\ VAL (A_OBJ CtrlParseCut.OBJ_BCAST) + 6 + 64 <= 0x5f9000.
Proof. intros rc fx. split; apply Z.leb_le; vm_compute; reflexivity. Qed.
(* HTRACE (donor A/ACeh.v:26; a Theorem Labs lane f6ab6e97937 AU/P_LLVMFuzzerTestOneInput_ctx.v:84 rt_trace_in_stmt) is a row no
   more: a Theorem Labs lane's SceneTrace.scene_HTRACE (RA_LLVMF and the six g_RT_* by conversion), at the call site. *)
(* AMALLOC / AFREE (donor A/AD1q.v:43 / :44; asan-ubsan twins AU/YF0w.v, AU/YF0q.v) are rows no more: a Theorem Labs lane's
   SceneAlloc.scene_AMALLOC / scene_AFREE (at 5387e903a6a), at the call site. *)
(* AMEMCPY / AMEMSET / ABCMP (donor A/ACfi.v:97 / :92, A/AE2s.v; YG0d.v:318 / :353) are rows no more: a Theorem Labs lane's
   SceneIntrin.scene_AMEMCPY / scene_AMEMSET / scene_ABCMP B HB (over AU/YE2q.v / YE2r.v / YE2s.v), at the call site. *)
(* ASM1 / ASM2 (YG0d.v:285) are rows no more: AU/YF0s.v:514 stack_malloc1_contract / AU/YF0u.v:514
   stack_malloc2_contract at B, with AR_laws_ok and HB (CS_CID = 2, AU/P_check_step_cut.v), at the call site. *)
(* stack_malloc_8_sz / ASF8 / ASH00 / ASHF8 (rgb YG0e.v:17 / :34 / :48) are rows no more: G_RowsU.p_stack_malloc_8_sz /
   p_ASF8 / p_ASH00 / p_ASHF8 (a Theorem Labs lane's proofs, at a423d9a58b9, over
   AU/Rt/StackMalloc8Closed.v, AU/Rt/StackFree8Closed.v, AU/RT_set_shadow.v and SceneBCertU.v), each of exactly the
   row's type, at the call site. *)
(* W_LLVMFuzzerTestOneInput (a Theorem Labs lane f6ab6e97937 AU/P_LLVMFuzzerTestOneInput.v:312-315 under its Section h) is a row no
   more: AU/P_LLVMFuzzerTestOneInput_Closed.v:212 scene_llvmf_closed, at the call site. It takes the row's premises
   except HRA_LLVMF, HA_EMPTY, HRO_PL, FFL and HB_C_PL, which its proof does not use. *)
(* The driver's leaves are stated at the FP state fx0, as in G_Top.v. *)
#[local] Existing Instance YK11.fx0.
(* The nine driver site types, as G_Drv.v's Variables instantiate them: scene's relocated definitions at fx0 (the
   one FPState instance here) and the run ceiling rc, each Let with the type of the Variable it replaces.
   aread_check: AU/YD1i.v:19 aread_check_stmt. xst_frame / printf_first / printf_next: AU/YD1w.v:119 / :144 / :151.
   est_img / est_frame / fwrite_site / refused_site / fprintf_s_site: AU/YD1x.v:37 / :38 / :57 / :83 / :69. *)
Let aread_check : YM05.RunCeil -> asyms -> Prop := fun rc B' => YD1i.aread_check_stmt B'.
Let xst_frame : YM05.RunCeil -> (nat -> (word -> bool) -> (word -> option byte) -> Prop) -> Prop :=
  fun rc xst' => YD1w.xst_frame_tfa xst'.
Let printf_first : YM05.RunCeil -> asyms -> (nat -> (word -> bool) -> (word -> option byte) -> Prop) -> Prop :=
  fun rc B' xst' => YD1w.printf_first_tfa B' xst'.
Let printf_next : YM05.RunCeil -> asyms -> (nat -> (word -> bool) -> (word -> option byte) -> Prop) -> Prop :=
  fun rc B' xst' => YD1w.printf_next_tfa B' xst'.
Let est_img : YM05.RunCeil -> ((word -> bool) -> (word -> option byte) -> Prop) -> Prop :=
  fun rc est' => YD1x.est_img_tfa est'.
Let est_frame : YM05.RunCeil -> ((word -> bool) -> (word -> option byte) -> Prop) -> Prop :=
  fun rc est' => YD1x.est_frame_tfa est'.
Let fwrite_site : YM05.RunCeil -> asyms -> ((word -> bool) -> (word -> option byte) -> Prop) -> Prop :=
  fun rc B' est' => YD1x.fwrite_site_tfa B' est'.
Let refused_site : YM05.RunCeil -> asyms -> ((word -> bool) -> (word -> option byte) -> Prop) -> Prop :=
  fun rc B' est' => YD1x.refused_site_tfa B' est'.
Let fprintf_s_site : YM05.RunCeil -> asyms -> ((word -> bool) -> (word -> option byte) -> Prop) -> Z -> list byte -> list byte -> Prop :=
  fun rc B' est' fmt lit1 lit2 => YD1x.fprintf_s_site_tfa B' est' fmt lit1 lit2.
(* A Theorem Labs lane's data rows (ROWMAP.md): TF AU/YB12.v:12 TFIB, HS AU/YB01.v:620 HS_tfib, xst AU/YD1k.v:125, est
   AU/YD1k.v:86. *)
Let TF : atable := YB12.TFIB.
Let HS : nat -> option acs := YB01.HS_tfib.
Let xst : nat -> (word -> bool) -> (word -> option byte) -> Prop := YD1k.xst.
Let est : (word -> bool) -> (word -> option byte) -> Prop := YD1k.est.
(* AICPY / ARDCHK (AU/YD2m.v:16 / :21), XFR (AU/YD1k.v:133), PF1 / PFN (AU/YD1o.v:247 / :283), ESTI / ESTF
   (AU/YD1k.v:114 / :116), FWS / RFS (AU/YD1k.v:281 / :322), EXS (AU/YD1j.v:123) and STARTUP (AU/YB1n.v:51) are rows
   no more: each is the core's term at the call site of ASAN_UBSAN_T_of_rows. *)
(* FPO / FPR / FPU (donor A/AD1q.v:60-62) are rows no more: AU/YD1l.v:149 / :154 / :159 tfib_fprintf_open_site /
   tfib_fprintf_rderr_site / tfib_fprintf_usage_site at the call site. DRV (donor A/AD1p.v:84-95) is a row no more:
   AU/YD1p.v:84 tfib_drv_main at LS := SceneAsanBase.scene_shape, whose LIBC is the statement of record's contract
   (g_contract here) and whose exit-site premise is the core's YD1x.exit_site_tfa, as EXS. *)
Theorem ASAN_UBSAN_T_of_rows : SceneAsanTop.ASAN_UBSAN_T.
Proof.
  exact (@ASAN_UBSAN_T_of_glue
    
B    TF    HS    xst    est    EV_LIB    LIVE_LIB    LLVMF_STK    YF0m.TfibSyms    aread_check    xst_frame    printf_first    printf_next    est_img    est_frame    fwrite_site    refused_site    fprintf_s_site    HB    ltac:(apply Z.leb_le; vm_compute; reflexivity)    ltac:(apply Z.leb_le; vm_compute; reflexivity)    ltac:(apply Z.leb_le; vm_compute; reflexivity)    ltac:(apply Z.leb_le; vm_compute; reflexivity)    g_TL    g_TLF    g_ML    G_SinkSub.scene_AIL    g_HZS_PL    g_HB_C_PL    g_HB_Z_TT    g_HB_C_TT    g_HRO_TT    g_HRO_PL    g_HRO_PLGOT    g_HB_Z_TR    g_HB_Z_CF    g_HB_C_CS    g_HRO_TR    g_HRO_CF    SceneTrace.scene_HTRACE    SceneAlloc.scene_AMALLOC    SceneAlloc.scene_AFREE
    (fun rc fx => SceneIntrin.scene_AMEMCPY B HB)    (fun rc fx => SceneIntrin.scene_AMEMSET B HB)    (fun rc fx => SceneIntrin.scene_ABCMP B HB)
    (fun rc fx => YF0s.stack_malloc1_contract B (AR_laws_ok _ B) HB)    (fun rc fx => YF0u.stack_malloc2_contract B (AR_laws_ok _ B) HB)
    G_RowsU.p_stack_malloc_8_sz    G_RowsU.p_ASF8    G_RowsU.p_ASH00    G_RowsU.p_ASHF8    (fun rc fx LAWS => @pb_kind_of_link1 fx rc asan_ubsan_sink_head (@PI_scene rc) B LAWS)    (fun rc fx LAWS TL => @pb_ctrl_checksum_verify fx rc asan_ubsan_sink_head (@PI_scene rc) B LAWS TL)    (fun rc fx LAWS ML TL TLF FFL RO KIND AMC AMS ABC ASM1 ASF =>
      CtrlParse.pb_ctrl_parse (fx:=fx) (rc:=rc) (SK:=asan_ubsan_sink_head) (PI:=@PI_scene rc) B LAWS TL TLF ML AMS AMC ABC ASM1
        (fun s cid Hw Hc Hn => ml_stack_malloc_progress _ ML s cid Hw Hc Hn) ASF FFL KIND SceneBCertU.SCENE_GLOBS
        (SceneBCertU.scene_globs_marked B HB _) (g_HG15 rc fx) (SceneBCertU.scene_img_shadow_vis B HB _) (g_HBC_RNG rc fx)
        (g_HBC_VAL rc fx))    (fun rc fx RO ML TL TLF ASF FFL ASM2 AMEMCPY ABCMP ZTR ZCF CCS ADDR RTR RCF PARSE CKV =>
      @pb_check_stepX fx rc asan_ubsan_sink_head (@PI_scene rc) B RO ML TL TLF ASF FFL ASM2 AMEMCPY ABCMP ZTR ZCF CCS ADDR RTR RCF PARSE CKV)    (fun rc fx LAWS TL => @pb_reac_ctrl_block_cksum_stamp fx rc asan_ubsan_sink_head (@PI_scene rc) B LAWS TL)    (fun rc fx LAWS TL AMS AMC ASTAMP => @pb_reac_ctrl_build_scene_step fx rc asan_ubsan_sink_head (@PI_scene rc) B LAWS TL AMS AMC ASTAMP)    (fun rc fx LAWS TL AMS AMC => @pb_reac_ctrl_scene_build fx rc asan_ubsan_sink_head (@PI_scene rc) B LAWS TL AMS AMC)    (fun rc fx LAWS AMC => @pb_reac_ctrl_scene_set_mac fx rc asan_ubsan_sink_head (@PI_scene rc) B LAWS AMC)
    (fun rc fx RO HA _ _ HEV HLIVE HSTK HSTKCS HRTT _ HRPG TL TLF ML _ AIL HZS _ HBZTT HBCTT
         AM AF AMS AMC ABC SM8 ASF8 ASH00 ASHF8 BSS SSB SSM TCX HTR =>
       @P_LLVMFuzzerTestOneInput_Closed.scene_llvmf_closed fx rc B A_LLVMF RA_LLVMF EV_LIB LIVE_LIB LLVMF_STK A_EMPTY
         RO HA HEV HLIVE HSTK HSTKCS HRTT HRPG TL TLF ML AIL HZS HBZTT HBCTT
         AM AF AMS AMC ABC SM8 ASF8 ASH00 ASHF8 BSS SSB SSM TCX HTR)
    (fun rc => YD2m.tfib_AICPY B HB)    (fun rc => YD2m.tfib_ARDCHK B HB)    (fun rc => YD1k.tfib_xst_frame)
    (fun rc => ltac:(eapply (YD1o.tfib_printf_first B); first [exact HB | exact (AR_laws_ok _ B)]))
    (fun rc => ltac:(eapply (YD1o.tfib_printf_next B); first [exact HB | exact (AR_laws_ok _ B)]))
    (fun rc => YD1k.tfib_est_img)    (fun rc => YD1k.tfib_est_frame)
    (fun rc => ltac:(eapply (YD1k.tfib_fwrite_site B); first [exact HB | exact (AR_laws_ok _ B)]))
    (fun rc => ltac:(eapply (YD1k.tfib_refused_site B); first [exact HB | exact (AR_laws_ok _ B)]))
    (fun rc => ltac:(eapply (YD1l.tfib_fprintf_open_site B); first [exact HB | exact (AR_laws_ok _ B)]))
    (fun rc => ltac:(eapply (YD1l.tfib_fprintf_rderr_site B); first [exact HB | exact (AR_laws_ok _ B)]))
    (fun rc => ltac:(eapply (YD1l.tfib_fprintf_usage_site B); first [exact HB | exact (AR_laws_ok _ B)]))
    (fun rc => ltac:(eapply (YD1j.tfib_exit_site B); first [exact HB | exact (AR_laws_ok _ B)]))
    (fun rc => YB1n.tfib_startup_T1)
    (fun rc => @YD1p.tfib_drv_main rc SceneAsanBase.scene_shape)).
Qed.
Theorem scene_asan_ubsan_agrees_of_rows : Statements.asan_ubsan_agrees.
Proof. exact (SceneAsanTop.asan_ubsan_agrees_of_asan_side ASAN_UBSAN_T_of_rows). Qed.
Theorem scene_asan_ubsan_halts_of_rows : Statements.asan_ubsan_halts.
Proof. exact (SceneAsanTop.asan_ubsan_halts_of_asan_side ASAN_UBSAN_T_of_rows). Qed.
(* R14 (a Theorem Labs lane): where the axioms come from. *)
Print Assumptions ASAN_UBSAN_T_of_rows.
Print Assumptions scene_asan_ubsan_agrees_of_rows.
Print Assumptions scene_asan_ubsan_halts_of_rows.
End close.
