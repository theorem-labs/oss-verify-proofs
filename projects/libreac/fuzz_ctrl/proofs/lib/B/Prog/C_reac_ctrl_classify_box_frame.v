(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* reac_ctrl_classify_box_frame (0x837c4) of fuzz_ctrl's ASan+UBSan build (image B, libreac v1.9.0): its contract in
   cgif's CALLER-JOURNAL form (CONVENTIONS.md section 2 (a working note, not in this delivery); cgif lib/YC20.v:311-365), because the
   call writes its caller's memory: the 4 bytes at v (sw a0,0(s0) at 0x83900) and, through reac_ctrl_parse, the 36
   bytes at o.  Image-B twin of a Theorem Labs lane's image-A spec (a working branch 4a9c3fec6d3,
   lib/A/Prog/C_reac_ctrl_classify_box_frame.v): the same premises C1-C22 and posts Q1-Q7, under a Theorem Labs lane's binding
   decisions (decisions.md (a working note, not in this delivery)):
     item 1 / 16  the segment term is Reusable.YB1v.tfibsegs and the sink head Reusable.YE2k.tfib_sink_head;
     item 2 / 17  the read-only premise is the core's arodata_okS over [RLO, RHI) (B: [0x9f168, 0xa15e8));
     item 3       the entry pc is a CONSTANT, REAC_CTRL_CLASSIFY_BOX_FRAME = 0x837c4 (not BASE + AF over a PAImg),
                  so Q7 is the core's acall_kept itself, not A's PA-layer tcj_kept (the same six conjuncts);
     item 4       the stack window is the proved B run's window K = 8864 = 64 + reac_ctrl_parse's 8800;
     item 5       the `achain` premise is DROPPED (exception 00:05Z: the proof does not consume it);
     item 12      classify gets its own caller-journal spec, proved from a split of ctrl's own image-B footprint run;
     item 15      no frame-route identifier appears in this statement.
   The function makes NO fake-stack call of its own and has no release of its own: reac_ctrl_parse's class-1 fake
   frame (taken at 0x83e74, released at 0x84294) is entirely inside reac_ctrl_parse.  Its 14 UBSan trap branches to
   `unimp` 0x83a38 are not taken (o and v are non-zero and 4-aligned, from afobj and frames_bounds).  The return
   value and the bytes are the shared model `classify` / `ctrlparse` (lib/Prog/RcClassify.v, RcParse.v).

   rule 24: proves function reac_ctrl_classify_box_frame (reuse search:
   reuse-search-B.md (a working note, not in this delivery) + checker a Theorem Labs lane CONFIRM 05:33Z: no
   released image-B proof; the released plain / ubsan proofs on origin/ossv/recipes e5e7eba2cc are other images).

   The proof `pb_reac_ctrl_classify_box_frame` cuts the run at the ONE call of reac_ctrl_parse (jal 0x83808, return
   0x8380c), because that callee takes a side-stack frame, which is an allocator EVENT in cgif's world and so cannot
   sit inside a lifted silent run:
     stretch A  0x837c4 .. 0x83808  lib/B/Prog/reac_ctrl_classify_box_frame_F.v `pro_A` (qualified), lifted;
     the call                       the callee's own cgif-form spec (TPARSE below);
     stretch B  0x8380c .. ret      lib/B/Prog/C_reac_ctrl_classify_box_frameLib.v `d1_B` (route (a) copy), lifted.
   Each lift is ProgBridge.fevt_of_evtF + the kit's YA0nR.SRr_fevt_hid at RNG := ProgBridge.RNG_W (w_H W), and each
   stretch runs on MemNorm.normalize of its own base memory (decisions.md item 27a: mem_inv is false at a real
   memory that holds a read-only byte), carried back by MemNormF.evtF_normalize_ro.  The glue is a port of image A's
   Qed glue (a working branch 4a9c3fec6d3, lib/A/Prog/reac_ctrl_classify_box_frame_glue.v): the same
   sections and lemma names, with image B's runs, numerals, normalization (lib/B/MemNorm, MemNormTr) and ProgWorld.

   ROUTE (C) (a Theorem Labs lane 16:05Z; the A twin's switch, a working branch 4888ecb2074, and A's stretch shape,
   a Theorem Labs lane 16:12Z): the glue takes neither AR_states_vis0_shadow (FALSE at an AR state) nor AR_states_owned_ro.
   ro_agree comes from the PROVED ProgWorldCtlRtC.ctl_rt_C_of_AR (its 4th part), asan_cells, the cut-shadow region and
   the runtime cells from the PROVED ProgWorldRtC.RT_used_of_AR_C (8 conjuncts).  Stretch B runs in its region form:
   d1_B takes `shadow_rw_on (reac_ctrl_classify_box_frame_post_call_shadow_R n u o)` (the two bcmp calls' range-check
   words of o + 4 / o + 10 and u), fed from RT_used_C's cut_shadow conjunct at the parse-return state through the (F)
   disjunct (o and u are bytes of caller frames, cls_sh_word_frame); no universal shadow_rw is used.  Its bcmp
   wrapper contract is the PROVED bcmp_wrap_on.bcmp_wrap_holds_F_on (no longer the Section hypothesis HBCMP), and
   reac_ctrl_checksum_verify's the PROVED reac_ctrl_checksum_verify_F_holds_on (cited inside d1_B).

   CLOSURE (porter's rule, brief.md): the _F files, lib/Lib and the B frame-route files are Required QUALIFIED and
   never Imported or Exported; the core (lib/Reusable) and the shared models (lib/Prog) are Imported.  Six modules
   exist twice in ctrl (core lib/Reusable and lib/B/Reusable: YI04, YI16, YK11, YK1b, YM05, YO09; porter a Theorem Labs lane's
   rule 04:24Z): each one this file uses is Required from the core's own directory and named only through a
   full-path Module alias below; neither copy is Imported.  lib/Lib is Required from its own directory
   (`...lib.Lib Require X`), because the partial form `...lib Require Lib.X` also matches lib/B/Bz/Lib and lib/AZ/Lib. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* the core, Imported: the cgif-world vocabulary of the statement *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK0h YK0i YK14 YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YE01 APostBase.
(* image B's core: the segments and the sink head (decisions.md items 1, 16) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YB1v YE2k YF0m YG0s.
(* the six doubled modules: Required from the CORE's own directory and used only through the full-path aliases *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YI16 YM05 YI04 YK1b.
Module CK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module CI16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Module CM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module CI04 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI04.
Module CK1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
(* the results: the shared, address-free models (lib/Prog, not frame-route files) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcClassify RcClassifyLib.
(* the kit bridge (a Theorem Labs lane's evtF -> SRr route) and the register-map transport *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK04R YA0nR YP09.
(* QUALIFIED, never Imported (porter's closure rule): ctrl's own footprint vocabulary and its proved image-B runs *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame Cells Step MState ExecF PropExec Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Img0 AsanRT ProgBridge MemNorm MemNormF MemNormTr ProgWorld.
(* route (C): the PROVED VIS0- and OWNED_RO-free producers of the cut's runtime facts (a Theorem Labs lane's B layer,
   a working branch 778cb94a47a, merged): ctl_rt_C_of_AR (ProgWorldCtlRtC.v) and RT_used_of_AR_C
   (ProgWorldRtC.v); the region form (ShadowRwOn) and the cut's regions (ACtlRtC); the bcmp wrapper's _on statement
   and its region (bcmp_wrap_c_on, sh_word_on, rng_asan). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ShadowRwOn ACtlRtC ProgWorldCtlRtC ProgWorldRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require
  ImgBounds bcmp_wrap_c bcmp_wrap_c_on bcmp_wrap_on rng_asan sh_word_on memcmp_c
  reac_ctrl_classify_box_frame_F C_reac_ctrl_classify_box_frameLib.
(* reac_ctrl_parse's cgif-form spec of record (a working branch ea59dbb03aa; owner of
   record a Theorem Labs lane), statement only, consumed at the cut *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require C_reac_ctrl_parse.
Module BPS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.C_reac_ctrl_parse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require reac_ctrl_classify_box_frame_c.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LCe := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module LSt := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LEx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Module LPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module LRg := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Regs6ss.
Module BI := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Img0.
Module BRT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.AsanRT.
Module BPB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.ProgBridge.
Module BMN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.MemNorm.
Module BMNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.MemNormF.
Module BMNT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.MemNormTr.
Module PW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.ProgWorld.
Module PWCC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.ProgWorldCtlRtC.
Module PWRC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.ProgWorldRtC.
Module SRO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.ShadowRwOn.
Module ARC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.ACtlRtC.
Module BIB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.ImgBounds.
Module BBC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.bcmp_wrap_c.
Module BWo := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.bcmp_wrap_c_on.
Module BWon := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.bcmp_wrap_on.
Module RNA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.rng_asan.
Module SWO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.sh_word_on.
Module BMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.memcmp_c.
Module BCLSF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_classify_box_frame_F.
Module BCLS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.C_reac_ctrl_classify_box_frameLib.
Module UCc := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.reac_ctrl_classify_box_frame_c.
Module KR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0nR.
Module CP09 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09.
Module CF0m := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YF0m.
Module CG0s := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0s.
(* Core names whose short form ALSO names a definition of a doubled family this closure reaches (ctrlgate DUP:
   astate / YO0i, frames / YO0f, spZ and in_img / YO0d, ret_ok / YK0s): written through these full-path aliases. *)
Module CG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Module CG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Module CG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module CK0s := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK0s.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope bv_scope.
Local Open Scope Z_scope.

(* B: the function's entry in fuzz_ctrl.asan-ubsan (lib/B/Prog/reac_ctrl_classify_box_frame_c.v:15; decisions.md
   item 3). *)
Definition REAC_CTRL_CLASSIFY_BOX_FRAME : Z := 0x837c4.
(* B: the machine stack the call needs = the window K of ctrl's proved image-B run that the glue re-uses
   (lib/B/Prog/reac_ctrl_classify_box_frame_c.v:16-18; decisions.md item 4): the 64-byte frame of `addi sp,sp,-64`
   at 0x837c4 and, below it, max(reac_ctrl_parse 8800, the bcmp wrapper 4560, reac_ctrl_checksum_verify 16) = 8800.
   reac_ctrl_parse's cgif spec at sp = S - 64 needs 64 + BPS.REAC_CTRL_PARSE_STK = 64 + 8800 of it: the whole window,
   with no slack. *)
Definition REAC_CTRL_CLASSIFY_BOX_FRAME_STK : Z := 8864.
(* B: reac_ctrl_parse's entry and window are its spec's own (BPS.A_reac_ctrl_parseP = 0x83e04,
   BPS.REAC_CTRL_PARSE_STK = 8800). *)
(* No heap allocation in the function or in any callee of it: the class-1 request and its release keep st_nev, so
   the journal's event budget k is unchanged. *)
Definition EV_CLASSIFY : Z := 0.

Section b. Context {fx : CK11.FPState} {rc : CM05.RunCeil}.
(* The journal's sink head is image B's core instance (decisions.md item 16; Reusable/YE2k.v:43), named explicitly
   because YE2k is only Required. *)
#[local] Existing Instance OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YE2k.tfib_sink_head.
#[local] Notation SEGS := Reusable.YB1v.tfibsegs.

Section e.
Variable B : asyms.
(* The read-only span of arodata_okS (decisions.md items 2 and 17, cgif lib/YC20.v:56): the composer instantiates it
   with the B PA instance's pa_relro = [0x9f168, 0xa15e8). *)
Variables RLO RHI : Z.


(* ----------------------------------------------------------------------------------------------------------
   This function's contract. *)

(* The caller bytes the call may write: the 36 bytes of the parsed record at o always, and the 4 bytes at v when
   the classification succeeds (the store at 0x83900 is on that path only). *)
Definition tclassify_out (o v : Z) (c : option Z) (a : Z) : Prop :=
  o <= a < o + 36 \/ (c <> None /\ v <= a < v + 4).

Definition treac_ctrl_classify_box_frame_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : CG00.astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : CG00.astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (n o v : Z) (fr us : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    (* Q1: the return configuration, at the caller's return address *)
    c2 = mkCfg (CK11.mkst regs2 (CK11.getr regs 1) mem2 (CK11.seg_rom SEGS)) md2 /\
    (* Q2: the caller's journal, with the same event budget (no heap allocation) *)
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_CLASSIFY) /\
    (* Q3: callee-saved registers, the caller's frames and blocks *)
    aregs_preserved regs regs2 /\ CG01.frames S2 = CG01.frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
    (* Q4: the return value is the model's *)
    CK11.getr regs2 10 = w64 (cl_r (classify n fr us)) /\
    (* Q5: the 36 bytes of the parsed record at o *)
    (forall i, (i < 36)%nat ->
       aview SEGS (w_H W2) mem2 (o + Z.of_nat i) = Some (bv_unsigned (nth i (snd (ctrlparse n fr)) cp_z))) /\
    (* Q6: on success, the 4 bytes at v hold the class *)
    (forall e, classify n fr us = Some e -> CI04.val_mem SEGS (mrestrict (w_H W2) mem2) v 4%nat e) /\
    (* Q7: everything else outside the call's own window is kept *)
    acall_kept SEGS B lyc Sc W memc W2 mem2
      (CG0d.spZ regs - REAC_CTRL_CLASSIFY_BOX_FRAME_STK) (CG0d.spZ regs) (tclassify_out o v (classify n fr us)).

Definition treac_ctrl_classify_box_frame_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (f n u o v : Z)
         (fr us : list byte),
    (* C1: the caller's journal (cgif YC20.v:349) *)
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    (* C2: the read-only image (decisions.md items 2, 17) *)
    arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) ->
    (* C3: the return address *)
    CK0s.ret_ok (CK11.getr regs 1) -> 4096 <= raZ regs ->
    (* C4: gp and tp *)
    CK11.getr regs 3 = w64 (as_gp B) -> CK11.getr regs 4 = w64 (as_tp B) ->
    (* C5: a0 = f, a1 = n, a2 = u, a3 = o, a4 = v, each a 64-bit value (image A's text).  (C6, the achain
       premise, is DROPPED: decisions.md item 5.) *)
    CK11.getr regs 10 = w64 f -> CK11.getr regs 11 = w64 n -> CK11.getr regs 12 = w64 u ->
    CK11.getr regs 13 = w64 o -> CK11.getr regs 14 = w64 v -> 0 <= n < 2 ^ 64 ->
    0 <= f < 2 ^ 64 -> 0 <= u < 2 ^ 64 ->
    (* C7: the call's window lies inside the caller's journal window *)
    CG0d.spZ regs mod 16 = 0 -> sp0 - STK <= CG0d.spZ regs - REAC_CTRL_CLASSIFY_BOX_FRAME_STK -> CG0d.spZ regs <= sp0 ->
    (* C8: room for reac_ctrl_parse's class-1 fake frame (__asan_stack_malloc_1 at 0x83e74) *)
    count_cid 1 (CG01.frames Sc) < fs_frames 1 ->
    (* C9 / C10 / C11: the 50-byte record at f, read when n >= 50 *)
    (50 <= n -> exists Lf : Z, In (f, Lf) (ablocks B lyc Sc) /\ 50 <= req_size Lf) ->
    length fr = 50%nat ->
    (50 <= n -> forall i, (i < 50)%nat -> aview SEGS (w_H W) memc (f + Z.of_nat i) = Some (cp_v fr i)) ->
    (* C12 / C13: the 36 bytes at o are an object of a caller frame that this call may write *)
    afobj SEGS B lyc Sc W memc o 36 ->
    (forall a, o <= a < o + 36 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
    (* C14 / C15: the same for the 4 bytes at v *)
    afobj SEGS B lyc Sc W memc v 4 ->
    (forall a, v <= a < v + 4 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
    (* C16 / C17 / C18: the 6 bytes of the OUI at u, read when n >= 50 *)
    length us = 6%nat ->
    (50 <= n -> afobj SEGS B lyc Sc W memc u 6) ->
    (50 <= n -> forall i, (i < 6)%nat -> aview SEGS (w_H W) memc (u + Z.of_nat i) = Some (cp_v us i)) ->
    (* C19 / C20 / C21 / C22: the buffers are pairwise apart *)
    o + 36 <= u \/ u + 6 <= o ->
    v + 4 <= o \/ o + 36 <= v ->
    v + 4 <= u \/ u + 6 <= v ->
    v + 4 <= f \/ f + 50 <= v ->
    SRr SEGS W (cfg_at SEGS REAC_CTRL_CLASSIFY_BOX_FRAME regs memc mdc)
      (treac_ctrl_classify_box_frame_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs n o v fr us).
End e.

(* ==============================================================================================================
   The proof.  Sections 1-7 are proof-internal lemmas (all Qed); section 8 is the glue under its Section
   hypotheses. *)

#[local] Ltac rlia := Z.div_mod_to_equations; lia.

(* ---------------------------------------------------------------------------------------------------------------
   1. The image, and normalization (decisions.md item 27a: a stretch runs on MemNorm.normalize of its base memory). *)

(* The image's segments do not wrap: the premise of the kit's SRr_fevt_hid. *)
Lemma cls_wx : wx_segs_nowrap SEGS.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* The image lies in [0x10000, 0x5fe000) (B ProgBridge's rsegs_spans). *)
Lemma cls_img_lt : forall a, CG0d.in_img SEGS a -> 0x10000 <= a < 0x5fe000.
Proof.
  intros a (sg & Hin & Hr).
  assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
                 (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) BI.rsegs))
    by exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) BI.rsegs sg Hin).
  rewrite BPB.rsegs_spans in H.
  remember (Z.of_N (seg_base sg)) as bb eqn:Eb. remember (Z.of_N (seg_size sg)) as zz eqn:Ez.
  clear Eb Ez Hin. cbn [In] in H.
  destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.

(* The image lies below kLowMemEnd: YCbq's Section a0 premise `segs_low` (donor A/ACeg.v:63). *)
Lemma cls_segs_low : forall a, CG0d.in_img SEGS a -> 0 <= a < kLowMemEnd.
Proof. intros a Ha. pose proof (cls_img_lt a Ha). unfold kLowMemEnd. lia. Qed.

Lemma cls_hi_noimg : forall a, 0x5fe000 <= a -> ~ CG0d.in_img SEGS a.
Proof. intros a Ha Hin. pose proof (cls_img_lt a Hin). lia. Qed.

Lemma cls_noimg_find : forall a, ~ CG0d.in_img SEGS a -> find_segment BI.rsegs a 1 = None.
Proof. intros a Hn. exact (find_segment_none SEGS a Hn). Qed.

Lemma cls_noimg_ro : forall x, ~ CG0d.in_img SEGS (bv_unsigned x) -> LMem.ro_addr BI.rsegs x = false.
Proof. intros x Hn. unfold LMem.ro_addr. rewrite (cls_noimg_find _ Hn). reflexivity. Qed.

Lemma cls_noimg_rom : forall x, ~ CG0d.in_img SEGS (bv_unsigned x) -> LPE.seg_rom BI.rsegs x = None.
Proof. intros x Hn. apply BMN.seg_rom_unmapped. exact (cls_noimg_find _ Hn). Qed.

(* A byte outside the image: the writable view is the memory itself. *)
Lemma cls_wview_noimg : forall m x, ~ CG0d.in_img SEGS (bv_unsigned x) -> wview BI.rsegs m x = m x.
Proof. intros m x Hn. unfold wview. destruct (m x); [reflexivity|]. rewrite (cls_noimg_find _ Hn). reflexivity. Qed.

(* the bytes of a range that holds no image byte are not read-only *)
Lemma cls_ro_free : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, 0 <= i < n -> ~ CG0d.in_img SEGS (a + i)) ->
  forall i, 0 <= i < n -> LMem.ro_addr BI.rsegs (LMem.wa (a + i)) = false.
Proof.
  intros a n H0 H1 Hn i Hi. apply cls_noimg_ro. rewrite LMem.wa_unsigned by lia. exact (Hn i Hi).
Qed.

(* addressable carried back from a normalized successor (MemNorm.mrd_rel) *)
Lemma cls_addressable_back : forall m m0 p n, BMN.mem_rel BI.rsegs m m0 ->
  BRT.addressable m0 p n -> BRT.addressable m p n.
Proof.
  intros m m0 p n HR (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H4 i Hi) as (Happ & b & Eb & Hok). split; [exact Happ|]. exists b.
  split; [rewrite (BMN.mrd_rel BI.rsegs m m0 _ HR); exact Eb | exact Hok].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   2. The two lifts.  Each states the proved stretch's premises on the REAL memory (ro_agree in place of mem_inv),
   one range_visible fact per footprint range, and hands the continuation the stretch's post on the real successor
   memory plus the kept hidden bytes. *)

(* SRr_fevt_hid for a run proved from the normalized memory (MemNormF.evtF_normalize_ro). *)
Lemma cls_lift :
  forall (W' : world SEGS) (R : bvmap 5 word) (pc : Z) (mb : word -> option byte) (md : Model)
         (P : machine_state -> Prop) (Q : world SEGS -> config -> Prop),
  BMN.ro_agree BI.rsegs mb ->
  LEx.evtF BI.rsegs (BPB.RNG_W (w_H W')) P
    (LMS.MS R CK11.fp_regs (Z_to_bv 64 pc) CK11.fp_csr None (BMN.normalize BI.rsegs mb)
            (CK11.seg_rom BI.rsegs)) ->
  (forall (ms1 : machine_state) (md1 : Model) (s0 : machine_state),
     P s0 -> BMN.ms_rel BI.rsegs ms1 s0 -> BMN.ro_agree BI.rsegs (ms_mem ms1) ->
     BMN.ro_same BI.rsegs mb (ms_mem ms1) ->
     (forall x : word, w_H W' x = true -> ms_mem ms1 x = mb x) ->
     same_but_materialized md md1 ->
     SRr SEGS W' (mkCfg ms1 md1) Q) ->
  SRr SEGS W' (mkCfg (LMS.MS R CK11.fp_regs (Z_to_bv 64 pc) CK11.fp_csr None mb (CK11.seg_rom BI.rsegs)) md) Q.
Proof.
  intros W' R pc mb md P Q RO HE K.
  pose proof (BMNF.evtF_normalize_ro (BPB.RNG_W (w_H W')) P R CK11.fp_regs (Z_to_bv 64 pc) CK11.fp_csr None mb
                (CK11.seg_rom BI.rsegs) RO HE) as HE'.
  apply (KR.SRr_fevt_hid SEGS cls_wx W' _ md (BPB.RNG_W (w_H W'))
           (fun s => exists s0, P s0 /\ BMN.ms_rel BI.rsegs s s0 /\ BMN.ro_same BI.rsegs mb (ms_mem s)) Q).
  - exact (BPB.fevt_of_evtF _ _ _ HE').
  - exact (BPB.fp_avoids_RNG_W (w_H W')).
  - intros ms1 md1 (s0 & HP & Hrel & Hsame) Hhid Hmat.
    pose proof Hrel as (_ & _ & _ & _ & _ & _ & _ & REL).
    exact (K ms1 md1 s0 HP Hrel (BMN.ro_agree_of_mem_rel BI.rsegs _ _ REL) Hsame Hhid Hmat).
Qed.

Lemma cls_rng_img : forall W : world SEGS, LEx.rng (BPB.RNG_W (w_H W)) 0x10000 0x5ee000.
Proof.
  intros W. pose proof (BPB.rng_of_visible _ _ _ (BPB.img_vis_W W)) as HI.
  cbv [BIB.IMG_LO BIB.IMG_HI] in HI. exact HI.
Qed.

(* Stretch A, lifted: classify's entry 0x837c4 to reac_ctrl_parse's entry 0x83e04 (ra = 0x8380c): ctrl's own
   `pro_A` (lib/B/Prog/reac_ctrl_classify_box_frame_F.v, a Theorem Labs lane), which takes no callee contract. *)
Lemma cls_liftA : forall (W : world SEGS) (model : Model)
    (ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (m : word -> option byte) (f n u o v S : Z) (fr us : list byte) (K : world SEGS -> config -> Prop),
  0 <= f < 2 ^ 64 -> 0 <= u < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> 8864 <= S < 2 ^ 64 ->
  length fr = 50%nat -> length us = 6%nat -> BRT.HIGHMEM_BEG <= S - 8864 ->
  LFr.stk BI.rsegs m (S - 8864) S -> BMN.ro_agree BI.rsegs m -> BRT.asan_cells m ->
  BPB.range_visible (w_H W) (S - 8864) 8864 ->
  (forall ms' model',
     (exists m1 : word -> option byte,
        ms' = LMS.MS (LFr.mkR (Z_to_bv 64 0x8380c) (Z_to_bv 64 (S + -64)) gp tp t0 t1 t2 (Z_to_bv 64 v) s1
                       (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 o) (Z_to_bv 64 o) (Z_to_bv 64 v) a5 a6 a7
                       (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 u) (Z_to_bv 64 BRT.ASAN_K) s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                CK11.fp_regs (Z_to_bv 64 0x83e04) CK11.fp_csr None m1 (CK11.seg_rom BI.rsegs) /\
        LFr.munch [(S + -64, S)] m m1 /\ LFr.wmono BI.rsegs m m1 /\
        LFr.stk BI.rsegs m1 (S - 8864) (S + -64) /\
        LSt.rw_cells BI.rsegs m1 (S + -64)
          [LCe.C8 s6; LCe.C8 s5; LCe.C8 s4; LCe.C8 s3; LCe.C8 s2; LCe.C8 s1; LCe.C8 s0; LCe.C8 ra]) ->
     (forall x : word, w_H W x = true -> ms_mem ms' x = m x) ->
     same_but_materialized model model' -> SRr SEGS W (mkCfg ms' model') K) ->
  SRr SEGS W
    (mkCfg (LMS.MS (LFr.mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 u)
                      (Z_to_bv 64 o) (Z_to_bv 64 v) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   CK11.fp_regs (Z_to_bv 64 0x837c4) CK11.fp_csr None m (CK11.seg_rom BI.rsegs)) model) K.
Proof.
  intros W model ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m f n u o v S fr us K
    Rf Ru Ro Rv RS Lfr Lus HHM ST HRO AC VW Hk.
  eapply (cls_lift W _ 0x837c4 m model _ K HRO).
  - exact (BCLSF.pro_A ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 CK11.fp_regs CK11.fp_csr
             (BMN.normalize BI.rsegs m) f n u o v S BRT.ASAN_K fr us (snd (ctrlparse n fr)) (BPB.RNG_W (w_H W))
             eq_refl Rf Ru Ro Rv RS Lfr Lus (ctrlparse_length n fr) HHM (cls_rng_img W)
             (BPB.rng_of_visible _ _ _ VW)
             (BMNT.stk_normalize_ro m (S - 8864) S HRO
                ltac:(cbv [BIB.IMG_HI]; unfold BRT.HIGHMEM_BEG in HHM; lia) ST)
             (BMN.mem_inv_normalize BI.rsegs m) (BMNT.asan_cells_normalize m HRO AC)
             t0 t1 t2 a5 a6 a7 t3 t4 t5 t6).
  - intros ms1 md1 s0' (m1 & E & MU & WM & _ & ST1 & RW) Hrel _ Hsame Hh Hs.
    apply Hk; [| exact Hh | exact Hs].
    subst s0'. destruct (BMNT.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Ems HR1].
    pose proof (BMN.mem_rel_normalize BI.rsegs m HRO) as HR0.
    exists (ms_mem ms1). split; [exact Ems|].
    split; [exact (BMN.munch_rel BI.rsegs _ m _ (ms_mem ms1) m1 HR0 HR1 Hsame MU)|].
    split; [exact (BMN.wmono_rel BI.rsegs m _ (ms_mem ms1) m1 HR0 HR1 Hsame WM)|].
    split; [exact (BMNT.stk_of_rel _ _ _ _ HR1 ST1) | exact (BMNT.rw_cells_of_rel _ _ _ _ HR1 RW)].
Qed.

(* route (C): a shadow region present at m is present at the normalized memory (the region twin of
   MemNormTr.shadow_rw_normalize, with the region guard carried: every shadow address lies above the image, so it is
   not read-only and normalize keeps its byte). *)
Lemma cls_shadow_rw_on_nrm : forall (P : Z -> Prop) m, BMN.ro_agree BI.rsegs m -> SRO.shadow_rw_on P m ->
  SRO.shadow_rw_on P (BMN.normalize BI.rsegs m).
Proof.
  intros P m RO H a Hp Ha. pose proof (BMN.mem_rel_normalize BI.rsegs m RO) as REL.
  destruct (H a Hp Ha) as [Hv [b Hb]].
  assert (E : LMem.ro_addr BI.rsegs (LMem.wa a) = false).
  { apply BMNT.ro_addr_above_img.
    unfold BRT.in_shadow, BRT.LOWMEM_END, BRT.LOWSHADOW_END, BRT.HIGHSHADOW_BEG, BRT.HIGHMEM_BEG in Ha.
    unfold BIB.IMG_HI. lia. }
  split; [rewrite (BMN.wview_rel_rw BI.rsegs m (BMN.normalize BI.rsegs m) _ REL E); exact Hv|].
  exists b. rewrite <- (BMN.mrd_rel BI.rsegs m (BMN.normalize BI.rsegs m) _ REL). exact Hb.
Qed.

(* Stretch B, lifted: reac_ctrl_parse's return point 0x8380c to classify's ret: the route-(a) copy `d1_B`
   (lib/B/Prog/C_reac_ctrl_classify_box_frameLib.v).  Its base memory and cut memory are both the normalized
   parse-return memory (so its munch / wmono premises are reflexive), and its post is carried back to the real
   successor memory.  Its two callee contracts: the bcmp wrapper's _on form (HBC, a premise here) and
   reac_ctrl_checksum_verify's (its PROVED reac_ctrl_checksum_verify_F_holds_on, cited inside d1_B).  route (C): the
   shadow premise is the stretch's region of record at m2 (was the universal shadow_rw m2). *)
Lemma cls_liftB : BWo.bcmp_wrap_contract_F_on -> forall (W : world SEGS) (model : Model)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (m2 : word -> option byte) (f n u o v S : Z) (fr us vb : list byte)
    (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word)
    (K : world SEGS -> config -> Prop),
  0 <= f < 2^64 -> 0 <= u < 2^64 -> 0 <= o < 2^64 -> 0 <= v < 2^64 -> 8864 <= S <= BRT.APPMEM_END ->
  S mod 16 = 0 -> length fr = 50%nat -> length us = 6%nat ->
  (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ LMem.bytes_at BI.rsegs m2 f fr /\ (f + 50 <= S - 8864 \/ S <= f)) ->
  (50 <= n -> u + 6 <= 2^64 /\ LMem.bytes_at BI.rsegs m2 u us /\ (u + 6 <= S - 8864 \/ S <= u)) ->
  o <> 0 -> o mod 4 = 0 -> o + 36 <= 2^64 -> (o + 36 <= S - 8864 \/ S <= o) ->
  (50 <= n -> o + 36 <= f \/ f + 50 <= o) -> (o + 36 <= u \/ u + 6 <= o) ->
  v <> 0 -> v mod 4 = 0 -> v + 4 <= 2^64 -> (v + 4 <= S - 8864 \/ S <= v) -> (v + 4 <= o \/ o + 36 <= v) ->
  (v + 4 <= f \/ f + 50 <= v) -> (v + 4 <= u \/ u + 6 <= v) ->
  BRT.HIGHMEM_BEG <= S - 8864 ->
  (50 <= n -> BRT.addressable m2 f 50 /\ BRT.addressable m2 u 6 /\ BRT.app_mem (u + 6) /\ BRT.app_mem (u + 7)) ->
  BRT.addressable m2 o 36 -> BRT.addressable m2 v 4 -> (v + 4 <= BRT.RT_LO \/ BRT.RT_HI <= v) ->
  (forall i, 0 <= i < 36 -> ~ CG0d.in_img SEGS (o + i)) -> (forall i, 0 <= i < 4 -> ~ CG0d.in_img SEGS (v + i)) ->
  BPB.range_visible (w_H W) (S - 8864) 8864 ->
  BPB.range_visible (w_H W) o 36 ->
  BPB.range_visible (w_H W) (BRT.shadow_addr o / 8 * 8)
    (BRT.shadow_addr (o + 36 - 1) / 8 * 8 + 8 - BRT.shadow_addr o / 8 * 8) ->
  BPB.range_visible (w_H W) v 4 ->
  BPB.range_visible (w_H W) (BRT.shadow_addr v) (BRT.shadow_addr (v + 4 - 1) - BRT.shadow_addr v + 1) ->
  (50 <= n -> BPB.range_visible (w_H W) f 50) ->
  (50 <= n -> BPB.range_visible (w_H W) (BRT.shadow_addr f / 8 * 8)
                (BRT.shadow_addr (f + 50 - 1) / 8 * 8 + 8 - BRT.shadow_addr f / 8 * 8)) ->
  (50 <= n -> BPB.range_visible (w_H W) u 6) ->
  (50 <= n -> BPB.range_visible (w_H W) (BRT.shadow_addr u / 8 * 8)
                (BRT.shadow_addr (u + 6 - 1) / 8 * 8 + 8 - BRT.shadow_addr u / 8 * 8)) ->
  LSt.rw_cells BI.rsegs m2 (S + -64)
    [LCe.C8 s6; LCe.C8 s5; LCe.C8 s4; LCe.C8 s3; LCe.C8 s2; LCe.C8 s1; LCe.C8 s0; LCe.C8 ra] ->
  LMem.bytes_at BI.rsegs m2 o (snd (ctrlparse n fr)) -> LMem.wr_at BI.rsegs m2 o 36 ->
  LSt.rw_cells BI.rsegs m2 v [LCe.CB 4 vb] ->
  LFr.stk BI.rsegs m2 (S - 8864) (S + -64) ->
  BMN.ro_agree BI.rsegs m2 -> BRT.asan_cells m2 ->
  SRO.shadow_rw_on (BCLS.reac_ctrl_classify_box_frame_post_call_shadow_R n u o) m2 ->
  BRT.addressable m2 (S - 8864) 8864 ->
  LMem.bytes_at BI.rsegs m2 BBC.REAL_BCMP (LMem.le8 (LMem.wa BBC.BCMP)) ->
  LMem.bytes_at BI.rsegs m2 BBC.REAL_MEMCMP (LMem.le8 (LMem.wa BMC.MEMCMP)) ->
  LMem.bytes_at BI.rsegs m2 BBC.GOT_CF (LMem.le8 (LMem.wa BBC.CF)) ->
  LMem.bytes_at BI.rsegs m2 (BBC.CF + 254) [Z_to_bv 8 1] ->
  LMem.bytes_at BI.rsegs m2 (BBC.CF + 255) [Z_to_bv 8 1] ->
  (forall ms' model',
     (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        ms' = LMS.MS (LFr.mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (cl_r (classify n fr us)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                CK11.fp_regs (LMS.ret_pc ra) CK11.fp_csr None m' (CK11.seg_rom BI.rsegs) /\
        LFr.munch [(o, o + 36); (v, v + 4); (S - 8864, S); (BRT.shadow_addr (S - 8864), BRT.shadow_addr S)] m2 m' /\
        LFr.wmono BI.rsegs m2 m' /\ LFr.stk BI.rsegs m' (S - 8864) S /\
        LSt.rw_cells BI.rsegs m' o [LCe.CB 36 (snd (ctrlparse n fr))] /\
        LSt.rw_cells BI.rsegs m' v [LCe.CB 4 (UCc.reac_ctrl_classify_box_frame_ev (classify n fr us) vb)] /\
        BRT.addressable m' (S - 8864) 8864) ->
     (forall x : word, w_H W x = true -> ms_mem ms' x = m2 x) ->
     same_but_materialized model model' -> SRr SEGS W (mkCfg ms' model') K) ->
  SRr SEGS W
    (mkCfg (LMS.MS (LFr.mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9
                      (Z_to_bv 64 (fst (ctrlparse n fr))) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 o) (Z_to_bv 64 f)
                      (Z_to_bv 64 u) (Z_to_bv 64 BRT.ASAN_K) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   CK11.fp_regs (Z_to_bv 64 0x8380c) CK11.fp_csr None m2 (CK11.seg_rom BI.rsegs)) model) K.
Proof.
  intros HBC W model ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m2 f n u o v S fr us vb
    x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 K
    Rf Ru Ro Rv RS S16 Lfr Lus HF HU Ho0 Ho4 Ho36 DOs DOf DOu Hv0 Hv4 Hv36 DVs DVo DVf DVu HHM AFU AO AV HVR
    NIo NIv VW VO VOS VV VVS VF VFS VU VUS FR HBo WRo HV ST HRO AC SW AW CL1 CL2 CL3 CL4 CL5 Hk.
  assert (HHM' : BIB.IMG_HI <= S - 8864) by (cbv [BIB.IMG_HI]; unfold BRT.HIGHMEM_BEG in HHM; lia).
  assert (RS' : 8864 <= S < 2 ^ 64) by (unfold BRT.APPMEM_END in RS; lia).
  pose proof (BMN.mem_rel_normalize BI.rsegs m2 HRO) as HR0.
  eapply (cls_lift W _ 0x8380c m2 model _ K HRO).
  - apply (BCLS.d1_B ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 CK11.fp_regs CK11.fp_csr
             (BMN.normalize BI.rsegs m2) f n u o v S (fst (ctrlparse n fr)) BRT.ASAN_K fr us vb
             (snd (ctrlparse n fr)) (BPB.RNG_W (w_H W))
             HBC eq_refl Rf Ru Ro Rv RS' S16 Lfr Lus
             (ctrlparse_length n fr) (ctrlparse_kind_range n fr) (cl_hk n fr)).
    (* the Section's premises *)
    + intros Hn. destruct (HF Hn) as (A1 & A2 & A3 & A4).
      split; [exact A1|]. split; [exact A2|]. split; [|exact A4].
      exact (BMN.bytes_at_normalize BI.rsegs m2 f fr HRO A3).
    + intros Hn. destruct (HU Hn) as (A2 & A3 & A4).
      split; [exact A2|]. split; [|exact A4].
      exact (BMN.bytes_at_normalize BI.rsegs m2 u us HRO A3).
    + exact Ho0.
    + exact Ho4.
    + exact Ho36.
    + exact DOs.
    + exact DOf.
    + exact DOu.
    + exact Hv0.
    + exact Hv4.
    + exact Hv36.
    + exact DVs.
    + exact DVo.
    + exact DVf.
    + exact DVu.
    + exact HHM.
    + lia.
    + intros Hn. destruct (AFU Hn) as (A1 & A2 & A3 & A4).
      split; [exact (BMNT.addressable_normalize m2 _ _ HRO A1)|].
      split; [exact (BMNT.addressable_normalize m2 _ _ HRO A2)|].
      split; [exact A3 | exact A4].
    + exact (BMNT.addressable_normalize m2 _ _ HRO AO).
    + exact (BMNT.addressable_normalize m2 _ _ HRO AV).
    + exact HVR.
    + (* route (C): HSR, the region of record at the normalized memory *)
      exact (cls_shadow_rw_on_nrm _ m2 HRO SW).
    (* the footprint *)
    + exact (BPB.rng_bytes_RNG_W (w_H W)).
    + apply cls_rng_img.
    + exact (BPB.rng_of_visible _ _ _ VW).
    + intros Hn. exact (BPB.rng_of_visible _ _ _ (VF Hn)).
    + intros Hn. exact (BPB.rng_of_visible _ _ _ (VFS Hn)).
    + exact (BPB.rng_of_visible _ _ _ VO).
    + exact (BPB.rng_of_visible _ _ _ VOS).
    + intros Hn. exact (BPB.rng_of_visible _ _ _ (VU Hn)).
    + intros Hn. exact (BPB.rng_of_visible _ _ _ (VUS Hn)).
    + exact (BPB.rng_of_visible _ _ _ VV).
    + exact (BPB.rng_of_visible _ _ _ VVS).
    (* the cut state at 0x8380c *)
    + reflexivity.
    + apply BMNT.rw_cells_normalize; [exact HRO | | exact FR].
      apply (cls_ro_free (S + -64) 64); [lia | lia |]. intros i Hi. apply cls_hi_noimg.
      unfold BRT.HIGHMEM_BEG in HHM. lia.
    + exact (BMN.bytes_at_normalize BI.rsegs m2 o _ HRO HBo).
    + apply (BMN.wr_at_norm BI.rsegs m2 _ o 36 HR0 WRo).
      exact (cls_ro_free o 36 ltac:(lia) ltac:(lia) NIo).
    + apply BMNT.rw_cells_normalize; [exact HRO | | exact HV].
      exact (cls_ro_free v 4 ltac:(lia) ltac:(lia) NIv).
    + apply BMN.mem_inv_normalize.
    + exact (BMNT.stk_normalize_ro m2 (S - 8864) (S + -64) HRO HHM' ST).
    + exact (BMNT.asan_cells_normalize m2 HRO AC).
    + exact (BMNT.addressable_normalize m2 _ _ HRO AW).
    + split; [exact (BMN.bytes_at_normalize BI.rsegs m2 _ _ HRO CL1)|].
      split; [exact (BMN.bytes_at_normalize BI.rsegs m2 _ _ HRO CL2)|].
      split; [exact (BMN.bytes_at_normalize BI.rsegs m2 _ _ HRO CL3)|].
      split; [exact (BMN.bytes_at_normalize BI.rsegs m2 _ _ HRO CL4)|].
      exact (BMN.bytes_at_normalize BI.rsegs m2 _ _ HRO CL5).
  - intros ms' model' s0'
      (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & _ &
       ST1 & RWo & RWv & _ & _ & AW1) Hrel _ Hsame Hh Hs.
    apply Hk; [| exact Hh | exact Hs].
    subst s0'. destruct (BMNT.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Ems HR1].
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem ms').
    split; [exact Ems|].
    split; [exact (BMN.munch_rel BI.rsegs _ m2 _ (ms_mem ms') m' HR0 HR1 Hsame MU)|].
    split; [exact (BMN.wmono_rel BI.rsegs m2 _ (ms_mem ms') m' HR0 HR1 Hsame WM)|].
    split; [exact (BMNT.stk_of_rel _ _ _ _ HR1 ST1)|].
    split; [exact (BMNT.rw_cells_of_rel _ _ _ _ HR1 RWo)|].
    split; [exact (BMNT.rw_cells_of_rel _ _ _ _ HR1 RWv) | exact (cls_addressable_back _ _ _ _ HR1 AW1)].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   3. Stretch B's munch list names the shadow of its window [shadow_addr (S - 8864), shadow_addr S), which is in
   none of awr_byte's cases.  The stretch never CHANGES those bytes: d1_B asks `addressable m1 (S - 8864) 8864` and
   gives `addressable m' (S - 8864) 8864`; the window is 8-aligned, so each of its shadow bytes covers a whole
   granule, and AsanRT.shadow_ok at granule offset 7 forces the value 0 before and after.  So the journal step
   (YCbq.ajournal_exec, whose write set only has to cover CHANGED bytes) leaves them out. *)
Lemma cls_byte_signed_small : forall b : byte, bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b Hb. unfold bv_signed. apply bv_swrap_small. change (bv_half_modulus 8) with 128.
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.

Lemma cls_byte_signed0 : forall b : byte, bv_signed b = 0 -> b = Z_to_bv 8 0.
Proof.
  intros b H. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  destruct (Z_lt_le_dec (bv_unsigned b) 128) as [L|L].
  - rewrite (cls_byte_signed_small b L) in H. apply bv_eq. rewrite H. reflexivity.
  - exfalso. unfold bv_signed in H.
    rewrite (CK11.bv_swrap_hi 8) in H;
      [ change (bv_modulus 8) with 256 in H; lia
      | discriminate
      | change (bv_half_modulus 8) with 128; lia
      | change (bv_modulus 8) with 256; lia ].
Qed.

Lemma cls_win_shadow_unchanged : forall (m m' : word -> option byte) (S : Z),
  S mod 8 = 0 -> BRT.HIGHMEM_BEG <= S - 8864 -> S <= BRT.APPMEM_END ->
  BRT.addressable m (S - 8864) 8864 -> BRT.addressable m' (S - 8864) 8864 ->
  forall x, BRT.shadow_addr (S - 8864) <= x < BRT.shadow_addr S -> m' (LMem.wa x) = m (LMem.wa x).
Proof.
  intros m m' S H8 HH HT (_ & _ & _ & A1) (_ & _ & _ & A2) x Hx.
  set (g := 8 * (x - BRT.ASAN_K) + 7).
  assert (Hg : S - 8864 <= g < S)
    by (unfold g, BRT.shadow_addr, BRT.ASAN_K in *; Z.div_mod_to_equations; lia).
  assert (Hsg : BRT.shadow_addr g = x) by (unfold g, BRT.shadow_addr; Z.div_mod_to_equations; lia).
  destruct (A1 (g - (S - 8864)) ltac:(lia)) as (_ & b1 & E1 & K1).
  destruct (A2 (g - (S - 8864)) ltac:(lia)) as (_ & b2 & E2 & K2).
  replace (S - 8864 + (g - (S - 8864))) with g in E1, K1, E2, K2 by lia.
  assert (G7 : g mod 8 = 7) by (unfold g; Z.div_mod_to_equations; lia).
  rewrite Hsg in E1, E2. unfold BRT.shadow_ok in K1, K2.
  assert (Z1 : b1 = Z_to_bv 8 0) by (apply cls_byte_signed0; destruct K1 as [K1|K1]; [exact K1 | lia]).
  assert (Z2 : b2 = Z_to_bv 8 0) by (apply cls_byte_signed0; destruct K2 as [K2|K2]; [exact K2 | lia]).
  subst b1 b2.
  assert (Hx64 : 0 <= x < 2 ^ 64)
    by (unfold BRT.shadow_addr, BRT.ASAN_K, BRT.HIGHMEM_BEG, BRT.APPMEM_END in *; Z.div_mod_to_equations; lia).
  assert (Hrom : LPE.seg_rom BI.rsegs (LMem.wa x) = None).
  { apply cls_noimg_rom. rewrite LMem.wa_unsigned by exact Hx64. apply cls_hi_noimg.
    unfold BRT.shadow_addr, BRT.ASAN_K, BRT.HIGHMEM_BEG in *. Z.div_mod_to_equations. lia. }
  assert (M1 : m (LMem.wa x) = Some (Z_to_bv 8 0)).
  { revert E1. unfold LMem.mrd. rewrite Hrom. destruct (m (LMem.wa x)); intros E; [exact E | discriminate E]. }
  assert (M2 : m' (LMem.wa x) = Some (Z_to_bv 8 0)).
  { revert E2. unfold LMem.mrd. rewrite Hrom. destruct (m' (LMem.wa x)); intros E; [exact E | discriminate E]. }
  rewrite M1, M2. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   4. From the cgif world's view (aview / apresent / range_addressable) to ctrl's memory predicates. *)
Lemma cls_aview_mrd : forall (H : word -> bool) (mem : word -> option byte) a,
  H (Z_to_bv 64 a) = false ->
  aview SEGS H mem a = option_map (fun b : byte => bv_unsigned b) (LMem.mrd BI.rsegs mem (LMem.wa a)).
Proof.
  intros H mem a Hh. unfold aview, CP09.mbyte, mrestrict. cbv beta. rewrite Hh.
  unfold LMem.mrd, LMem.wa. reflexivity.
Qed.

(* A hidden byte is off the segments (w_Hoff), so its view is None. *)
Lemma cls_vis_of_view : forall (W : world SEGS) (mem : word -> option byte) a,
  aview SEGS (w_H W) mem a <> None -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a Hv. destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity].
  exfalso. apply Hv. unfold aview, CP09.mbyte, mrestrict. rewrite E.
  assert (Hr : CK11.seg_rom SEGS (Z_to_bv 64 a) = None)
    by exact (BMN.seg_rom_unmapped BI.rsegs _ (w_Hoff W _ E)).
  rewrite Hr. reflexivity.
Qed.

(* Bytes the view reads, at visible addresses, are ctrl bytes. *)
Lemma cls_bytes_of_view : forall (H : word -> bool) (mem : word -> option byte) a (bs : list byte) (d : byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, (i < length bs)%nat -> H (Z_to_bv 64 (a + Z.of_nat i)) = false) ->
  (forall i, (i < length bs)%nat -> aview SEGS H mem (a + Z.of_nat i) = Some (bv_unsigned (nth i bs d))) ->
  LMem.bytes_at BI.rsegs mem a bs.
Proof.
  intros H mem a bs d Ha Hl Hh Hv. split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
  specialize (Hv i Hi). rewrite (cls_aview_mrd H mem (a + Z.of_nat i) (Hh i Hi)) in Hv.
  rewrite (nth_error_nth' bs d Hi).
  destruct (LMem.mrd BI.rsegs mem (LMem.wa (a + Z.of_nat i))) as [b|]; cbn in Hv; [|discriminate Hv].
  injection Hv as Hb. f_equal. apply bv_eq. exact Hb.
Qed.

(* Present bytes are ctrl stack bytes. *)
Lemma cls_stk_of_pres : forall (H : word -> bool) (mem : word -> option byte) lo hi,
  0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> apresent H mem a) -> LFr.stk BI.rsegs mem lo hi.
Proof.
  intros H mem lo hi Hlo Hhi Hp. split; [exact Hlo|]. split; [exact Hhi|]. intros a Ha.
  destruct (Hp a Ha) as [_ [b Hb]]. unfold LMem.wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold LMem.mrd. rewrite Hb. reflexivity.
Qed.

Lemma cls_wr_of_pres : forall (H : word -> bool) (mem : word -> option byte) a n,
  0 <= a -> a + n <= 2 ^ 64 -> (forall x, a <= x < a + n -> apresent H mem x) -> LMem.wr_at BI.rsegs mem a n.
Proof.
  intros H mem a n Ha Hn Hp. split; [exact Ha|]. split; [exact Hn|]. intros i Hi.
  destruct (Hp (a + i) ltac:(lia)) as [_ [b Hb]]. unfold LMem.wa. unfold wview. rewrite Hb. discriminate.
Qed.

Lemma cls_shadow_lt : forall a, 0 <= a < 2 ^ 47 -> 0 <= BRT.shadow_addr a < 2 ^ 47.
Proof. intros a Ha. unfold BRT.shadow_addr, BRT.ASAN_K in *. Z.div_mod_to_equations. lia. Qed.

(* Shadow facts the view states give ctrl's addressable. *)
Lemma cls_addressable_of_view : forall (W : world SEGS) (mem : word -> option byte) p n,
  0 <= p -> 0 <= n -> p + n <= BRT.APPMEM_END ->
  (forall i, 0 <= i < n -> BRT.app_mem (p + i)) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n ->
  BRT.addressable mem p n.
Proof.
  intros W mem p n H0 Hn Hp Happ HR. split; [exact H0|]. split; [exact Hn|]. split; [exact Hp|].
  intros i Hi. split; [exact (Happ i Hi)|].
  destruct (HR (p + i) ltac:(lia)) as (s & Es & Hok).
  assert (Esh : shadow_of_addr SHADOW_OFF (p + i) = BRT.shadow_addr (p + i))
    by (unfold shadow_of_addr, SHADOW_OFF, BRT.shadow_addr, BRT.ASAN_K; lia).
  rewrite Esh in Es.
  assert (Hv : w_H W (Z_to_bv 64 (BRT.shadow_addr (p + i))) = false)
    by (apply (cls_vis_of_view W mem); rewrite Es; discriminate).
  rewrite (cls_aview_mrd (w_H W) mem (BRT.shadow_addr (p + i)) Hv) in Es.
  destruct (LMem.mrd BI.rsegs mem (LMem.wa (BRT.shadow_addr (p + i)))) as [b|] eqn:Eb; cbn in Es;
    [|discriminate Es].
  injection Es as Es. subst s. exists b. split; [reflexivity|].
  unfold saddr_ok in Hok. assert (Hsm : bv_unsigned b < 128) by (destruct Hok; lia).
  unfold BRT.shadow_ok. rewrite (cls_byte_signed_small b Hsm). destruct Hok; [left | right]; lia.
Qed.

(* munch keeps the view of every byte outside its list. *)
Lemma cls_view_munch : forall Wl (H : word -> bool) (m m' : word -> option byte) a,
  LFr.munch Wl m m' -> 0 <= a < 2 ^ 64 -> LFr.outside Wl a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros Wl H m m' a MU Ha Ho. unfold aview, CP09.mbyte, mrestrict.
  rewrite (MU (Z_to_bv 64 a)); [reflexivity|]. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia).
  exact Ho.
Qed.

Lemma cls_munch_at : forall Wl (m m' : word -> option byte) a,
  LFr.munch Wl m m' -> 0 <= a < 2 ^ 64 -> LFr.outside Wl a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros Wl m m' a MU Ha Ho. apply MU. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia). exact Ho.
Qed.

Lemma cls_wr_dec : forall o v Sp x,
  (o <= x < o + 36 \/ v <= x < v + 4 \/ Sp - 8864 <= x < Sp) \/
  ~ (o <= x < o + 36 \/ v <= x < v + 4 \/ Sp - 8864 <= x < Sp).
Proof.
  intros o v Sp x.
  destruct (Z_le_gt_dec o x); destruct (Z_lt_le_dec x (o + 36)); destruct (Z_le_gt_dec v x);
    destruct (Z_lt_le_dec x (v + 4)); destruct (Z_le_gt_dec (Sp - 8864) x); destruct (Z_lt_le_dec x Sp);
    first [left; lia | right; lia].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   5. The caller's journal across the two lifted stretches (YCbq.ajournal_exec). *)
Section Journal.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

Ltac cls_exec_side :=
  first [ exact LAWS | exact cls_segs_low | assumption | idtac ].

(* Stretch A writes only its own 64-byte frame [Sp - 64, Sp), inside the journal's window. *)
Lemma cls_journal_A : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k m1 md1 Sp,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= Sp - 64 -> Sp <= sp0 -> 0x5fe000 <= Sp - 64 -> Sp <= 2 ^ 64 ->
  LFr.munch [(Sp + -64, Sp)] memc m1 -> LFr.wmono BI.rsegs memc m1 ->
  (forall x : word, w_H W x = true -> m1 x = memc x) ->
  same_but_materialized mdc md1 ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m1 md1 k.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k m1 md1 Sp HJ H1 H2 H3 H4 MU WM Hh Hs.
  eapply ajournal_exec with (Wr := fun a => Sp - 64 <= a < Sp) (memc := memc) (mdc := mdc).
  all: cls_exec_side.
  all: lazymatch goal with
  | |- forall x : word, ~ _ -> _ = _ =>
      intros x Hx; unfold mrestrict; destruct (w_H W x); [reflexivity|];
      apply MU; cbn; split; [intros [Hx1 Hx2]; apply Hx; lia | exact I]
  | |- CK1b.mem_grows _ _ =>
      intros x Hx; unfold mrestrict in *; destruct (w_H W x); [exact Hx|];
      pose proof (bv_unsigned_in_range 64 x) as Rx; change (bv_modulus 64) with (2 ^ 64) in Rx;
      destruct (Z_lt_le_dec (bv_unsigned x) (Sp - 64)) as [L|L];
      [ rewrite (MU x) by (cbn; split; [lia | exact I]); exact Hx
      | destruct (Z_lt_le_dec (bv_unsigned x) Sp) as [L2|L2];
        [ assert (Hn : ~ CG0d.in_img SEGS (bv_unsigned x)) by (apply cls_hi_noimg; lia);
          rewrite <- (cls_wview_noimg m1 x Hn); apply WM; rewrite (cls_wview_noimg memc x Hn); exact Hx
        | rewrite (MU x) by (cbn; split; [lia | exact I]); exact Hx ] ]
  | |- forall a, _ -> awr_byte _ _ _ _ _ _ _ _ =>
      intros a Ha; left; lia
  end.
Qed.

(* Stretch B's write set as the journal sees it: o, v and the window.  The window's shadow, which its munch list
   also names, is unchanged (cls_win_shadow_unchanged). *)
Lemma cls_journal_B : forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 (W2 : world SEGS) mem2 md2 k m' md' Sp o v,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k ->
  sp0 - STK <= Sp - 8864 -> Sp <= sp0 -> Sp mod 8 = 0 -> BRT.HIGHMEM_BEG <= Sp - 8864 -> Sp <= BRT.APPMEM_END ->
  0 <= o -> o + 36 <= 2 ^ 64 -> 0 <= v -> v + 4 <= 2 ^ 64 ->
  (forall i, 0 <= i < 36 -> ~ CG0d.in_img SEGS (o + i)) -> (forall i, 0 <= i < 4 -> ~ CG0d.in_img SEGS (v + i)) ->
  LFr.munch [(o, o + 36); (v, v + 4); (Sp - 8864, Sp); (BRT.shadow_addr (Sp - 8864), BRT.shadow_addr Sp)] mem2 m' ->
  LFr.wmono BI.rsegs mem2 m' ->
  BRT.addressable mem2 (Sp - 8864) 8864 -> BRT.addressable m' (Sp - 8864) 8864 ->
  (forall x : word, w_H W2 x = true -> m' x = mem2 x) ->
  same_but_materialized md2 md' ->
  (forall a, o <= a < o + 36 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly2 S2) ly2 own a) ->
  (forall a, v <= a < v + 4 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly2 S2) ly2 own a) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 m' md' k.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k m' md' Sp o v HJ H1 H2 H8 HH HT
    Ho0 Ho1 Hv0 Hv1 NIo NIv MU WM A2 A' Hh Hs Wo Wv.
  assert (UNCH : forall x : word, ~ ((o <= bv_unsigned x < o + 36) \/ (v <= bv_unsigned x < v + 4) \/
                                     (Sp - 8864 <= bv_unsigned x < Sp)) -> m' x = mem2 x).
  { intros x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
    destruct (Z_le_gt_dec (BRT.shadow_addr (Sp - 8864)) (bv_unsigned x)) as [L1|L1];
      [destruct (Z_lt_le_dec (bv_unsigned x) (BRT.shadow_addr Sp)) as [L2|L2]|].
    - rewrite <- (stdpp.bitvector.definitions.Z_to_bv_bv_unsigned _ x).
      change (Z_to_bv 64 (bv_unsigned x)) with (LMem.wa (bv_unsigned x)).
      exact (cls_win_shadow_unchanged mem2 m' Sp H8 HH HT A2 A' (bv_unsigned x) (conj L1 L2)).
    - apply MU. cbn. repeat split; try exact I; intros [Q1 Q2]; first [lia | apply Hx; lia].
    - apply MU. cbn. repeat split; try exact I; intros [Q1 Q2]; first [lia | apply Hx; lia]. }
  eapply ajournal_exec with (Wr := fun a => (o <= a < o + 36) \/ (v <= a < v + 4) \/ (Sp - 8864 <= a < Sp))
    (memc := mem2) (mdc := md2).
  all: cls_exec_side.
  all: lazymatch goal with
  | |- forall x : word, ~ _ -> _ = _ =>
      intros x Hx; unfold mrestrict; destruct (w_H W2 x); [reflexivity|]; exact (UNCH x Hx)
  | |- CK1b.mem_grows _ _ =>
      intros x Hx; unfold mrestrict in *; destruct (w_H W2 x); [exact Hx|];
      pose proof (bv_unsigned_in_range 64 x) as Rx; change (bv_modulus 64) with (2 ^ 64) in Rx;
      destruct (cls_wr_dec o v Sp (bv_unsigned x)) as [HW|HW];
      [ assert (Hn : ~ CG0d.in_img SEGS (bv_unsigned x))
          by (destruct HW as [Q|[Q|Q]];
              [ replace (bv_unsigned x) with (o + (bv_unsigned x - o)) by lia; apply NIo; lia
              | replace (bv_unsigned x) with (v + (bv_unsigned x - v)) by lia; apply NIv; lia
              | apply cls_hi_noimg; unfold BRT.HIGHMEM_BEG in HH; lia ]);
        rewrite <- (cls_wview_noimg m' x Hn); apply WM; rewrite (cls_wview_noimg mem2 x Hn); exact Hx
      | rewrite (UNCH x HW); exact Hx ]
  | |- forall a, _ -> awr_byte _ _ _ _ _ _ _ _ =>
      intros a [Ha|[Ha|Ha]]; [exact (Wo a Ha) | exact (Wv a Ha) | left; lia]
  end.
Qed.
End Journal.

(* ---------------------------------------------------------------------------------------------------------------
   6. Facts the composition takes from the cgif world. *)
Ltac cls_seg_bounds :=
  match goal with |- Z.le ?lo _ /\ Z.lt _ (?lo' + ?sz) =>
    let l := eval vm_compute in lo in let h := eval vm_compute in sz in change lo with l; change sz with h end;
  lia.

(* The four segments of image B tile [0x10000, 0x5fe000) (ProgBridge.rsegs_spans). *)
Lemma cls_img_in : forall a, 0x10000 <= a < 0x5fe000 -> CG0d.in_img SEGS a.
Proof.
  intros a Ha. unfold CG0d.in_img.
  destruct (Z_lt_le_dec a 0x31000) as [L1|L1]; [|destruct (Z_lt_le_dec a 0x9f000) as [L2|L2];
    [|destruct (Z_lt_le_dec a 0xa2000) as [L3|L3]]].
  - eexists. split; [left; reflexivity|]. cls_seg_bounds.
  - eexists. split; [right; left; reflexivity|]. cls_seg_bounds.
  - eexists. split; [right; right; left; reflexivity|]. cls_seg_bounds.
  - eexists. split; [right; right; right; left; reflexivity|]. cls_seg_bounds.
Qed.

Lemma cls_app_of_in_app : forall lo len a, in_app lo len -> lo <= a < lo + len -> BRT.app_mem a.
Proof.
  intros lo len a [H0 H1] Ha. pose proof (@CM05.alloc_ceiling_lt rc) as Hc.
  unfold BRT.app_mem, BRT.LOWMEM_END, BRT.HIGHMEM_BEG, BRT.APPMEM_END.
  unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in H1. lia.
Qed.

(* A sub-range of a visible range is visible. *)
Lemma cls_vis_sub : forall H lo len lo' len', BPB.range_visible H lo len -> lo <= lo' -> lo' + len' <= lo + len ->
  BPB.range_visible H lo' len'.
Proof. intros H lo len lo' len' (A1 & A2 & A3) H1 H2. split; [lia|]. split; [lia|]. intros a Ha. apply A3. lia. Qed.

Lemma cls_mod64_8 : forall z, z mod 64 = 0 -> z mod 8 = 0.
Proof.
  intros z H. pose proof (Z.div_mod z 64 ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
  rewrite D. replace (64 * (z / 64)) with ((8 * (z / 64)) * 8) by ring. apply Z_mod_mult.
Qed.

Lemma cls_al8_room : forall u e, u mod 8 = 0 -> e mod 8 = 0 -> u + 6 <= e -> u + 8 <= e.
Proof.
  intros u e Hu He H. pose proof (Z.div_mod u 8 ltac:(lia)) as Du. pose proof (Z.div_mod e 8 ltac:(lia)) as De.
  rewrite Hu, Z.add_0_r in Du. rewrite He, Z.add_0_r in De.
  assert (u / 8 < e / 8) by lia. lia.
Qed.

(* The shadow byte of an address of an 8-aligned range [fa, fa + bs) (bs a multiple of 8) is one of the range's
   shadow bytes. *)
Lemma cls_sh_in_frame : forall fa bs x, fa mod 8 = 0 -> bs mod 8 = 0 -> fa <= x < fa + bs ->
  in_zr (shadow_of_addr SHADOW_OFF x) (shadow_addr fa, bs / 8).
Proof.
  intros fa bs x H1 H2 H3. unfold in_zr, shadow_addr, shadow_of_addr. cbn [fst snd].
  assert (L1 : fa / 8 <= x / 8) by (apply Z.div_le_mono; lia).
  assert (E : fa + bs = 8 * (fa / 8 + bs / 8)).
  { pose proof (Z.div_mod fa 8 ltac:(lia)) as Da. pose proof (Z.div_mod bs 8 ltac:(lia)) as Db. lia. }
  assert (L2 : x / 8 < fa / 8 + bs / 8) by (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

(* A shadow byte of an address below 2^47 lies in the shadow band, so in no range of application memory. *)
Lemma cls_sh_not_in_app : forall lo len p n x, in_app lo len -> lo <= p -> p + n <= lo + len -> 0 <= x < 2 ^ 47 ->
  ~ (p <= shadow_of_addr SHADOW_OFF x < p + n).
Proof.
  intros lo len p n x [H0 H1] Hp Hn Hx. pose proof (@CM05.alloc_ceiling_lt rc).
  unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in H1. unfold shadow_of_addr, SHADOW_OFF.
  assert (L1 : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (L2 : x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

(* The 8-aligned shadow cover of a range is visible when the view reads every byte of it (shadow_hull_vis). *)
Lemma cls_hull_vis : forall (W : world SEGS) mem d n, 0 <= d -> d + n <= 2 ^ 47 -> 0 < n ->
  shadow_hull_vis (aview SEGS (w_H W) mem) d n ->
  BPB.range_visible (w_H W) (BRT.shadow_addr d / 8 * 8)
    (BRT.shadow_addr (d + n - 1) / 8 * 8 + 8 - BRT.shadow_addr d / 8 * 8).
Proof.
  intros W mem d n Hd Hn Hn0 HV.
  assert (E1 : forall x, BRT.shadow_addr x = shadow_addr x)
    by (intros x; unfold BRT.shadow_addr, shadow_addr, BRT.ASAN_K, SHADOW_OFF; lia).
  split; [unfold BRT.shadow_addr, BRT.ASAN_K; Z.div_mod_to_equations; lia|].
  split; [unfold BRT.shadow_addr, BRT.ASAN_K; Z.div_mod_to_equations; lia|].
  intros a Ha. apply (cls_vis_of_view W mem a). apply HV. rewrite <- !E1. lia.
Qed.

Lemma cls_ra_transfer : forall (rd rd' : reader) p n,
  (forall x, p <= x < p + n -> rd' (shadow_of_addr SHADOW_OFF x) = rd (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable rd SHADOW_OFF p n -> range_addressable rd' SHADOW_OFF p n.
Proof. intros rd rd' p n E H x Hx. rewrite (E x Hx). exact (H x Hx). Qed.

Lemma cls_view_eq_pt : forall (H : word -> bool) (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a E. unfold aview, CP09.mbyte, mrestrict. rewrite E. reflexivity. Qed.

Lemma cls_bytes_one : forall m a bs i (d : byte), LMem.bytes_at BI.rsegs m a bs -> (i < length bs)%nat ->
  LMem.bytes_at BI.rsegs m (a + Z.of_nat i) [nth i bs d].
Proof.
  intros m a bs i d (H1 & H2 & H3) Hi. split; [lia|]. split; [cbn; lia|]. intros j Hj. cbn in Hj.
  assert (j = 0%nat) by lia. subst j. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
  rewrite (H3 i Hi). apply nth_error_nth'. exact Hi.
Qed.

(* Bytes read through two views that agree, at bytes visible in both worlds, carry over. *)
Lemma cls_bytes_transfer : forall (H1 H2 : word -> bool) (m1 m2 : word -> option byte) a (bs : list byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> H1 (Z_to_bv 64 (a + i)) = false /\ H2 (Z_to_bv 64 (a + i)) = false) ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> aview SEGS H2 m2 (a + i) = aview SEGS H1 m1 (a + i)) ->
  LMem.bytes_at BI.rsegs m1 a bs -> LMem.bytes_at BI.rsegs m2 a bs.
Proof.
  intros H1 H2 m1 m2 a bs Ha Hl Hv Ee (B1 & B2 & B3). split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
  destruct (Hv (Z.of_nat i) ltac:(lia)) as [V1 V2].
  pose proof (Ee (Z.of_nat i) ltac:(lia)) as E.
  rewrite (cls_aview_mrd H2 m2 (a + Z.of_nat i) V2), (cls_aview_mrd H1 m1 (a + Z.of_nat i) V1) in E.
  rewrite <- (B3 i Hi). revert E.
  destruct (LMem.mrd BI.rsegs m2 (LMem.wa (a + Z.of_nat i))) as [x|];
    destruct (LMem.mrd BI.rsegs m1 (LMem.wa (a + Z.of_nat i))) as [y|]; cbn; intros E; try discriminate E;
    [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma cls_classify_range : forall n fr us e, classify n fr us = Some e -> 0 <= e <= 5.
Proof.
  intros n fr us e H. unfold classify in H. cbv zeta in H.
  repeat match type of H with context [if ?b then _ else _] => destruct b end; inversion H; lia.
Qed.

(* ret_ok k (YK0s: jalr k 0 lands on k) says k is even, so lib/Lib's ret_pc returns k itself (the proof of
   a Theorem Labs lane's bl_ret_pc, a working branch C_reac_ctrl_build_asLib.v:387). *)
Lemma cls_ret_pc_ok : forall k : word, CK0s.ret_ok k -> LMS.ret_pc k = k.
Proof.
  intros k H. unfold CK0s.ret_ok in H. rewrite <- H at 2.
  unfold LMS.ret_pc. apply bv_eq.
  unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK14.v_jalr, CK11.jalr_tgtZ.
  rewrite bv_and_unsigned, bv_not_unsigned, !Z_to_bv_unsigned.
  change (bv_wrap 64 1) with 1%Z. change (Z.lnot 1) with (-2)%Z.
  rewrite Z.add_0_r.
  rewrite <- (bv_wrap_small 64 (bv_unsigned k)) at 1 by apply bv_unsigned_in_range.
  apply CK11.Z_land_m2_wrap.
Qed.

(* Four present bytes are one ctrl rw cell, holding whatever bytes memory has there. *)
Lemma cls_cells4_of_pres : forall (H : word -> bool) (mem : word -> option byte) a,
  0 <= a -> a + 4 <= 2 ^ 64 -> (forall x, a <= x < a + 4 -> apresent H mem x) ->
  exists vb, length vb = 4%nat /\ LSt.rw_cells BI.rsegs mem a [LCe.CB 4 vb].
Proof.
  intros H mem a Ha Hn Hp.
  destruct (Hp a ltac:(lia)) as [_ [b0 E0]]. destruct (Hp (a + 1) ltac:(lia)) as [_ [b1 E1]].
  destruct (Hp (a + 2) ltac:(lia)) as [_ [b2 E2]]. destruct (Hp (a + 3) ltac:(lia)) as [_ [b3 E3]].
  exists [b0; b1; b2; b3]. split; [reflexivity|]. split.
  - split; [cbn; split; [reflexivity | exact I]|].
    split; [exact Ha|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. unfold LMem.mrd, LMem.wa.
    destruct i as [|[|[|[|i]]]].
    + change (Z.of_nat 0) with 0. rewrite Z.add_0_r, E0. reflexivity.
    + change (Z.of_nat 1) with 1. rewrite E1. reflexivity.
    + change (Z.of_nat 2) with 2. rewrite E2. reflexivity.
    + change (Z.of_nat 3) with 3. rewrite E3. reflexivity.
    + lia.
  - exact (cls_wr_of_pres H mem a 4 Ha Hn Hp).
Qed.

Section WinAddr.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

(* The machine stack's shadow is zero (AR_zshadow_law at the stack entry of zero_shadow_ranges), so every byte of a
   stack sub-range in high memory is addressable. *)
Lemma cls_win_addressable : forall ly S (W : world SEGS) mem md lo len,
  AR SEGS B ly S W mem md ->
  ly_stk_lo ly <= lo -> lo + len <= ly_stk_hi ly -> 0 <= len -> BRT.HIGHMEM_BEG <= lo ->
  lo + len <= BRT.APPMEM_END -> BRT.addressable mem lo len.
Proof.
  intros ly S W mem md lo len HAR Hlo Hhi Hlen HH HA.
  pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
  pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & Plo & Phi & Lbeg).
  pose proof (al_zshadow _ _ LAWS ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
    ltac:(unfold zero_shadow_ranges; left; reflexivity)) as HZ.
  cbn [fst snd] in HZ. unfold zero_shadow in HZ. unfold page_aligned in Plo, Phi.
  split; [unfold BRT.HIGHMEM_BEG in HH; lia|]. split; [exact Hlen|]. split; [exact HA|].
  intros i Hi. split; [unfold BRT.app_mem; right; lia|].
  set (L := ly_stk_lo ly) in *. set (Hh := ly_stk_hi ly) in *.
  assert (Hj : 0 <= (lo + i) / 8 - L / 8 < (Hh - L) / 8) by (Z.div_mod_to_equations; lia).
  pose proof (HZ _ Hj) as Z0.
  assert (Esh : shadow_of_addr SHADOW_OFF L + ((lo + i) / 8 - L / 8) = BRT.shadow_addr (lo + i))
    by (unfold shadow_of_addr, SHADOW_OFF, BRT.shadow_addr, BRT.ASAN_K; lia).
  rewrite Esh in Z0.
  assert (Hv : w_H W (Z_to_bv 64 (BRT.shadow_addr (lo + i))) = false)
    by (apply (cls_vis_of_view W mem); rewrite Z0; discriminate).
  rewrite (cls_aview_mrd (w_H W) mem (BRT.shadow_addr (lo + i)) Hv) in Z0.
  destruct (LMem.mrd BI.rsegs mem (LMem.wa (BRT.shadow_addr (lo + i)))) as [b|]; cbn in Z0; [|discriminate Z0].
  injection Z0 as Z0. exists b. split; [reflexivity|]. unfold BRT.shadow_ok. left.
  rewrite cls_byte_signed_small by lia. exact Z0.
Qed.

Lemma cls_frame_noimg : forall ly S (W : world SEGS) mem md cid pos a,
  AR SEGS B ly S W mem md -> In (cid, pos) (CG01.frames S) ->
  frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> ~ CG0d.in_img SEGS a.
Proof.
  intros ly S W mem md cid pos a HAR Hin Ha.
  exact (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR
                  (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hin Ha))))))).
Qed.

(* Every live fake frame is 64-aligned and a multiple of 64 bytes (A's CtrlFrame.v:257 frame_al64, a Theorem Labs lane's PA
   layer, copied: lib/A/Prog/CtrlFrame.v Requires image-A PA files that this closure does not need). *)
Lemma cls_frame_al64 : forall ly S W mem md cid pos,
  AR SEGS B ly S W mem md -> In (cid, pos) (CG01.frames S) ->
  frame_addr ly cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0 /\ 64 <= fs_frame_bytes cid.
Proof.
  intros ly S W mem md cid pos [M _] Hin.
  destruct (CG0s.frame_facts B ly S _ cid pos M Hin) as (_ & _ & _ & _ & Hpg & _ & _ & Hoff & H64 & Hb & _).
  unfold frame_addr, page_aligned in *. split; [|split; [exact Hb | exact H64]].
  rewrite Z.add_mod, Hoff, Z.add_0_r, Z.mod_mod by lia.
  replace (ly_F ly) with (64 * (ly_F ly / 4096 * 64)) by (pose proof (Z.div_mod (ly_F ly) 4096 ltac:(lia)); lia).
  rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

(* The shadow word cover of a sub-range of a live fake frame is visible (B CtrlFrame.v shadow_hull_vis_of_frame,
   copied). *)
Lemma cls_shadow_hull_vis_of_frame : forall ly S W mem md cid pos d n,
  AR SEGS B ly S W mem md -> In (cid, pos) (CG01.frames S) ->
  frame_addr ly cid pos <= d -> d + n <= frame_addr ly cid pos + fs_frame_bytes cid -> 0 < n ->
  shadow_hull_vis (aview SEGS (w_H W) mem) d n.
Proof.
  intros ly S W mem md cid pos d n HAR Hin Hfd Hdn Hn s Hs.
  destruct (cls_frame_al64 ly S W mem md cid pos HAR Hin) as (Hal & Hbal & Hb64).
  destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & _ & _ & Hsh).
  set (f := frame_addr ly cid pos) in *. set (bs := fs_frame_bytes cid) in *.
  pose proof (Z.div_mod f 64 ltac:(lia)) as Df. pose proof (Z.div_mod bs 64 ltac:(lia)) as Db.
  assert (E8f : f / 8 = 8 * (f / 64)) by (rewrite Hal, Z.add_0_r in Df; rewrite Df at 1; replace (64 * (f / 64)) with (8 * (f / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
  assert (E8b : bs / 8 = 8 * (bs / 64)) by (rewrite Hbal, Z.add_0_r in Db; rewrite Db at 1; replace (64 * (bs / 64)) with (8 * (bs / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
  assert (Hsf : shadow_addr f = 8 * (268431360 + f / 64)) by (unfold shadow_addr, SHADOW_OFF; lia).
  assert (L1 : shadow_addr f <= shadow_addr d / 8 * 8).
  { pose proof (shadow_mono f d Hfd) as M1. rewrite Hsf. rewrite Hsf in M1.
    assert (268431360 + f / 64 <= shadow_addr d / 8) by (apply Z.div_le_lower_bound; lia). lia. }
  assert (L2 : shadow_addr (d + n - 1) / 8 * 8 + 8 <= shadow_addr f + bs / 8).
  { assert (M2 : shadow_addr (d + n - 1) < shadow_addr f + bs / 8).
    { unfold shadow_addr in *. assert ((d + n - 1) / 8 < f / 8 + bs / 8) by (apply Z.div_lt_upper_bound; lia). lia. }
    rewrite Hsf, E8b in M2. rewrite Hsf, E8b.
    assert (shadow_addr (d + n - 1) / 8 < 268431360 + f / 64 + bs / 64) by (apply Z.div_lt_upper_bound; lia). lia. }
  specialize (Hsh (s - shadow_addr f) ltac:(lia)). replace (shadow_addr f + (s - shadow_addr f)) with s in Hsh by lia.
  apply (aview_some_of_apresent SEGS). exact (proj1 Hsh).
Qed.

(* The bytes of a live fake frame and of a live heap block are visible (al_frames / al_blocks: present). *)
Lemma cls_frame_vis : forall ly S (W : world SEGS) mem md cid pos lo len,
  AR SEGS B ly S W mem md -> In (cid, pos) (CG01.frames S) ->
  frame_addr ly cid pos <= lo -> lo + len <= frame_addr ly cid pos + fs_frame_bytes cid ->
  BPB.range_visible (w_H W) lo len.
Proof.
  intros ly S W mem md cid pos lo len HAR Hin H1 H2.
  destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (F0 & F1 & F2).
  destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & _ & Hb & _).
  pose proof (fs_frame_bytes_nonneg cid). pose proof (@CM05.alloc_ceiling_lt rc).
  split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (proj1 (Hb a ltac:(lia)))).
Qed.

Lemma cls_block_vis : forall ly S (W : world SEGS) mem md p nn lo len,
  AR SEGS B ly S W mem md -> In (p, nn) (ablocks B ly S) ->
  p <= lo -> lo + len <= p + req_size nn -> BPB.range_visible (w_H W) lo len.
Proof.
  intros ly S W mem md p nn lo len HAR Hin H1 H2.
  destruct (al_blocks _ _ LAWS ly S W mem md p nn HAR Hin) as (_ & H4 & Hc & _ & Hb & _).
  pose proof (@CM05.alloc_ceiling_lt rc).
  split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (proj1 (Hb a ltac:(lia)))).
Qed.
End WinAddr.

(* ---------------------------------------------------------------------------------------------------------------
   7. Q7: acall_kept over the window [S - 8864, S), composed from stretch A's munch, reac_ctrl_parse's acall_kept
   and stretch B's munch (with its window shadow unchanged, and v's bytes unchanged when classify = None). *)
Section Ack.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

Lemma cls_ack : forall lyc Sc (W W2 : world SEGS) memc mdc m1 mem2 m3 Sp o v (cN : Prop),
  AR SEGS B lyc Sc W memc mdc ->
  CM05.alloc_ceiling <= Sp - 8864 -> Sp <= 2 ^ 47 ->
  0 <= o -> o + 36 <= CM05.alloc_ceiling -> 0 <= v -> v + 4 <= CM05.alloc_ceiling ->
  (forall i, 0 <= i < 36 -> ~ CG0d.in_img SEGS (o + i)) -> (forall i, 0 <= i < 4 -> ~ CG0d.in_img SEGS (v + i)) ->
  (cN \/ ~ cN) ->
  LFr.munch [(Sp + -64, Sp)] memc m1 ->
  acall_kept SEGS B lyc Sc W m1 W2 mem2 (Sp - 64 - BPS.REAC_CTRL_PARSE_STK) (Sp - 64) (fun a => o <= a < o + 36) ->
  LFr.munch [(o, o + 36); (v, v + 4); (Sp - 8864, Sp); (BRT.shadow_addr (Sp - 8864), BRT.shadow_addr Sp)] mem2 m3 ->
  (~ cN -> forall i, 0 <= i < 4 -> m3 (LMem.wa (v + i)) = mem2 (LMem.wa (v + i))) ->
  (forall a, Sp - 8864 <= a < Sp -> apresent (w_H W2) m3 a) ->
  acall_kept SEGS B lyc Sc W memc W2 m3 (Sp - REAC_CTRL_CLASSIFY_BOX_FRAME_STK) Sp
    (fun a => o <= a < o + 36 \/ (cN /\ v <= a < v + 4)).
Proof.
  intros lyc Sc W W2 memc mdc m1 mem2 m3 Sp o v cN HAR B1 B2 Ho0 Ho1 Hv0 Hv1 NIo NIv DcN MUa
    (KP1 & KP2 & KP3 & KP4 & KP5 & KP6) MUb UNv P3.
  pose proof (@CM05.alloc_ceiling_value rc) as [[Hc0 Hc1] _].
  unfold BPS.REAC_CTRL_PARSE_STK in KP1, KP5.
  assert (SW1 : BRT.shadow_addr Sp <= 0x10007fff8000)
    by (unfold BRT.shadow_addr, BRT.ASAN_K; Z.div_mod_to_equations; lia).
  assert (SW0 : 0x20087ff7000 <= BRT.shadow_addr (Sp - 8864))
    by (unfold BRT.shadow_addr, BRT.ASAN_K; Z.div_mod_to_equations; lia).
  assert (STEPB : forall H a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 36) -> ~ (cN /\ v <= a < v + 4) ->
                    ~ (Sp - 8864 <= a < Sp) -> ~ (BRT.shadow_addr (Sp - 8864) <= a < BRT.shadow_addr Sp) ->
                    aview SEGS H m3 a = aview SEGS H mem2 a).
  { intros H a Ha Hno HnE Hnw Hns.
    destruct (Z_le_gt_dec v a) as [V1|V1]; [destruct (Z_lt_le_dec a (v + 4)) as [V2|V2]|].
    - destruct DcN as [Hc|Hc]; [exfalso; exact (HnE (conj Hc (conj V1 V2)))|].
      apply cls_view_eq_pt. specialize (UNv Hc (a - v) ltac:(lia)).
      replace (v + (a - v)) with a in UNv by lia. exact UNv.
    - apply (cls_view_munch _ H mem2 m3 a MUb Ha). cbn.
      repeat split; try exact I; intros [Q1 Q2]; first [lia | apply Hno; lia | apply Hnw; lia | apply Hns; lia].
    - apply (cls_view_munch _ H mem2 m3 a MUb Ha). cbn.
      repeat split; try exact I; intros [Q1 Q2]; first [lia | apply Hno; lia | apply Hnw; lia | apply Hns; lia]. }
  assert (STEPA : forall H a, 0 <= a < 2 ^ 64 -> ~ (Sp - 64 <= a < Sp) ->
                    aview SEGS H m1 a = aview SEGS H memc a).
  { intros H a Ha Hn. apply (cls_view_munch _ H memc m1 a MUa Ha). cbn.
    split; [intros [Q1 Q2]; apply Hn; lia | exact I]. }
  unfold REAC_CTRL_CLASSIFY_BOX_FRAME_STK.
  split; [|split; [|split; [|split; [|split]]]].
  - (* high memory outside the window *)
    intros a Ha Hw.
    rewrite (STEPB (w_H W2) a ltac:(lia)); [ | lia | intros [_ Q]; lia | exact Hw | lia ].
    rewrite (KP1 a Ha ltac:(lia)). apply STEPA; lia.
  - (* the caller's blocks *)
    intros b mm i Hin Hi HE.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HAR Hin) as (_ & Hb0 & Hb1 & Hb2 & _).
    pose proof (cls_app_of_in_app _ _ (b + i) Hb2 ltac:(lia)) as Happ.
    unfold BRT.app_mem, BRT.LOWMEM_END, BRT.HIGHMEM_BEG, BRT.APPMEM_END in Happ.
    rewrite (STEPB (w_H W2) (b + i) ltac:(lia));
      [ | intros Q; apply HE; left; exact Q | intros Q; apply HE; right; exact Q | lia | lia ].
    rewrite (KP2 b mm i Hin Hi ltac:(intros Q; apply HE; left; exact Q)). apply STEPA; lia.
  - (* the image *)
    intros a Hai Ho He.
    pose proof (cls_img_lt a Hai) as Hia.
    rewrite (STEPB (w_H W2) a ltac:(lia)); [ | | | lia | lia].
    + rewrite (KP3 a Hai Ho He). apply STEPA; lia.
    + intros Q. apply (NIo (a - o) ltac:(lia)). replace (o + (a - o)) with a by lia. exact Hai.
    + intros [_ Q]. apply (NIv (a - v) ltac:(lia)). replace (v + (a - v)) with a by lia. exact Hai.
  - (* the caller's frames and their shadow *)
    intros cid pos a Hin Ha HE.
    destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F0 & F1 & F2).
    pose proof (fs_frame_bytes_nonneg cid) as Fn.
    assert (Hra : 0 <= a < 2 ^ 64 /\ ~ (Sp - 8864 <= a < Sp) /\
                  ~ (BRT.shadow_addr (Sp - 8864) <= a < BRT.shadow_addr Sp) /\ a < Sp - 64).
    { destruct Ha as [Ha|Ha]; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha.
      - pose proof (cls_app_of_in_app _ _ a F2 Ha) as Happ.
        unfold BRT.app_mem, BRT.LOWMEM_END, BRT.HIGHMEM_BEG, BRT.APPMEM_END in Happ. lia.
      - unfold shadow_addr, SHADOW_OFF in Ha. unfold BRT.shadow_addr, BRT.ASAN_K.
        Z.div_mod_to_equations. lia. }
    destruct Hra as (Ha64 & Hw & Hs & Hlt).
    rewrite (STEPB (w_H W2) a Ha64);
      [ | intros Q; apply HE; left; exact Q | intros Q; apply HE; right; exact Q | exact Hw | exact Hs ].
    rewrite (KP4 cid pos a Hin Ha ltac:(intros Q; apply HE; left; exact Q)). apply STEPA; lia.
  - (* presence in high memory outside the window *)
    intros a Ha Hw Hp.
    assert (E3 : m3 (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)).
    { apply (cls_munch_at _ mem2 m3 a MUb ltac:(lia)). cbn.
      repeat split; try exact I; intros [Q1 Q2]; first [lia | apply Hw; lia]. }
    assert (E1 : m1 (Z_to_bv 64 a) = memc (Z_to_bv 64 a)).
    { apply (cls_munch_at _ memc m1 a MUa ltac:(lia)). cbn. split; [intros [Q1 Q2]; lia | exact I]. }
    destruct Hp as [Hh [b Hb]].
    assert (Hp1 : apresent (w_H W) m1 a) by (split; [exact Hh | exists b; rewrite E1; exact Hb]).
    destruct (KP5 a Ha ltac:(lia) Hp1) as [Hh2 [b2 Hb2]].
    split; [exact Hh2|]. exists b2. rewrite E3. exact Hb2.
  - (* the window *)
    intros a Ha. exact (P3 a Ha).
Qed.
End Ack.

(* route (C): fake frames are 64-aligned with a size a multiple of 64 (cls_frame_al64), so the aligned shadow words of
   a frame's bytes stay inside the frame's shadow: cut_shadow's (F) disjunct covers the region of record of stretch B at
   the caller's frames of o and u (the twin of A's cls_sh_word_frame, with the alignment given as premises). *)
Lemma cls_sh_word_frame : forall fa bs p n a, fa mod 64 = 0 -> bs mod 64 = 0 ->
  fa <= p -> p + n <= fa + bs -> 0 < n -> SWO.sh_word_on p n a ->
  shadow_addr fa <= a < shadow_addr fa + bs / 8.
Proof.
  intros fa bs p n a H64 Hb H1 H2 Hn (_ & Ha1 & Ha2).
  unfold RNA.sh_al8_lo, RNA.sh_al8_hi, BRT.shadow_addr, BRT.ASAN_K in Ha1, Ha2.
  unfold shadow_addr, SHADOW_OFF.
  Z.div_mod_to_equations. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   8. The glue.

   Section hypotheses, each with its owner (who discharges it):
   - RELRO_IMG: decisions.md item 17's twin rule; the composer, from PI_ctrl_B's pa_relro_img.
   - LAWS: the core's AR_laws (decisions.md item 76: core-level, Reusable.YG0q.AR_laws_ok at B's top).
   - TPARSE: reac_ctrl_parse's cgif-form spec of record, lib/B/Prog/C_reac_ctrl_parse.v (a Theorem Labs lane,
     a working branch ea59dbb03aa) at SEGS := tfibsegs and the core sink head; its proof
     pb_reac_ctrl_parse is a Theorem Labs lane's / a Theorem Labs lane's.
   - TS: image B's bundle law CtrlTSyms B (the composer, B := CtrlB, CtrlB_syms).
   route (C): no AR_states_vis0_shadow and no AR_states_owned_ro.  ro_agree and RT_used_C are not hypotheses: their
   PROVED producers PWCC.ctl_rt_C_of_AR / PWRC.RT_used_of_AR_C (a working branch
   778cb94a47a) are applied to TS and LAWS, the only premises their statements carry.  The bcmp wrapper's contract is
   not a hypothesis either (it was HBCMP): stretch B is given its PROVED route-(C) form bcmp_wrap_on.bcmp_wrap_holds_F_on
   (bcmp_wrap_c_on.bcmp_wrap_contract_F_on; a Theorem Labs lane's root-free text, a working branch
   417f5c8e944, taken by path). *)
Section m.
Variable B : asyms.
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> CG0d.in_img SEGS a.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TPARSE : BPS.treac_ctrl_parse_spec
  (SK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YE2k.tfib_sink_head) SEGS B RLO RHI.
Hypothesis TS : CF0m.CtrlTSyms B.

(* ro_agree at a cut memory: the 4th part of ctl_rt_C_of_AR, from AR and the read-only view there *)
Lemma cls_ro_of_AR : forall ly S (W : world SEGS) mem md,
  AR SEGS B ly S W mem md -> arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) mem) -> BMN.ro_agree BI.rsegs mem.
Proof.
  intros ly S W mem md HAR HRO.
  destruct (PWCC.ctl_rt_C_of_AR B TS LAWS RLO RHI ly S W mem md HAR
              (PW.arodata_okP_of_S B RLO RHI RLO RHI _ HRO (Z.le_refl _) (Z.le_refl _))) as (_ & _ & _ & HR).
  exact HR.
Qed.

Theorem pb_reac_ctrl_classify_box_frame : treac_ctrl_classify_box_frame_spec B RLO RHI.
Proof.
  unfold treac_ctrl_classify_box_frame_spec.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs f n u o v fr us
    C1 C2 C3a C3b C4a C4b C5f C5n C5u C5o C5v C5r C5fr C5ur C7a C7b C7c C8 C9 C10 C11 C12 C13 C14 C15 C16 C17
    C18 C19 C20 C21 C22.
  set (Sp := CG0d.spZ regs) in *.
  pose proof C1 as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _ & _).
  destruct Hastk as (_ & HSTK & Hceil & Hlo & Hhi & H47 & _).
  pose proof (@CM05.alloc_ceiling_value rc) as [[Hc0 Hc1] _].
  unfold REAC_CTRL_CLASSIFY_BOX_FRAME_STK in C7b.
  assert (B1 : CM05.alloc_ceiling <= Sp - 8864) by lia.
  assert (B2 : Sp <= 2 ^ 47) by lia.
  assert (B3 : BRT.HIGHMEM_BEG <= Sp - 8864) by (unfold BRT.HIGHMEM_BEG; lia).
  assert (Sp64 : 0 <= Sp < 2 ^ 64) by lia.
  destruct (PWRC.RT_used_of_AR_C B TS LAWS _ _ _ _ _ HAR) as (RACc & _ & _ & _ & _ & _ & _ & _).
  pose proof (cls_ro_of_AR _ _ _ _ _ HAR C2) as ROc.
  (* the caller's frames of o and v, and their bounds *)
  pose proof C12 as ((co & po & Ino & Hco & Hfo8 & Hfo1 & Hfo2) & Ho8 & RAo).
  pose proof C14 as ((cv & pv & Inv & Hcv & Hfv8 & Hfv1 & Hfv2) & Hv8 & RAv).
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc co po HAR Ino) as (Fo1 & Fo2 & Fo3).
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cv pv HAR Inv) as (Fv1 & Fv2 & Fv3).
  pose proof (fs_frame_bytes_nonneg co) as Fon. pose proof (fs_frame_bytes_nonneg cv) as Fvn.
  assert (NIo : forall i, 0 <= i < 36 -> ~ CG0d.in_img SEGS (o + i))
    by (intros i Hi; apply (cls_frame_noimg B LAWS lyc Sc W memc mdc co po); [exact HAR | exact Ino | lia]).
  assert (NIv : forall i, 0 <= i < 4 -> ~ CG0d.in_img SEGS (v + i))
    by (intros i Hi; apply (cls_frame_noimg B LAWS lyc Sc W memc mdc cv pv); [exact HAR | exact Inv | lia]).
  assert (Fo8s : fs_frame_bytes co mod 8 = 0)
    by exact (cls_mod64_8 _ (proj1 (proj2 (cls_frame_al64 B lyc Sc W memc mdc co po HAR Ino)))).
  assert (Fv8s : fs_frame_bytes cv mod 8 = 0)
    by exact (cls_mod64_8 _ (proj1 (proj2 (cls_frame_al64 B lyc Sc W memc mdc cv pv HAR Inv)))).
  (* G0: classify's entry as stretch A's start state *)
  rewrite BPB.cfg_at_MS. unfold REAC_CTRL_CLASSIFY_BOX_FRAME.
  change (CK11.seg_rom SEGS) with (CK11.seg_rom BI.rsegs).
  assert (XR0 : LRg.xregs_eqv
    (LFr.mkR (reg_get regs 1) (Z_to_bv 64 Sp) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5) (reg_get regs 6)
       (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 u)
       (Z_to_bv 64 o) (Z_to_bv 64 v) (reg_get regs 15) (reg_get regs 16) (reg_get regs 17) (reg_get regs 18)
       (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24)
       (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29) (reg_get regs 30)
       (reg_get regs 31)) regs).
  { apply LRg.xregs_eqv_sym. apply LRg.mkR_eqv_of;
      first [ reflexivity | exact C5f | exact C5n | exact C5u | exact C5o | exact C5v
            | (unfold Sp, CG0d.spZ; rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned; reflexivity) ]. }
  refine (KR.SRr_xregs_eqv SEGS W _ regs _ _ _ _ _ _ _ _ _ XR0).
  apply (cls_liftA W mdc (reg_get regs 1) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5) (reg_get regs 6)
           (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 15) (reg_get regs 16) (reg_get regs 17)
           (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
           (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27)
           (reg_get regs 28) (reg_get regs 29) (reg_get regs 30) (reg_get regs 31) memc f n u o v Sp fr us).
  { exact C5fr. }
  { exact C5ur. }
  { lia. }
  { lia. }
  { lia. }
  { exact C10. }
  { exact C16. }
  { exact B3. }
  { apply (cls_stk_of_pres (w_H W)); [lia | lia | intros a Ha; apply Hpres; lia]. }
  { exact ROc. }
  { exact RACc. }
  { split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hpres a ltac:(lia))). }
  intros ms1 md1 (m1 & E1 & MU1 & WM1 & ST1 & RW1) Hh1 Hs1. subst ms1.
  (* G1: the journal over stretch A, the read-only view at m1, and reac_ctrl_parse's spec *)
  assert (J1 : ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m1 md1 k).
  { apply (cls_journal_A B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k m1 md1 Sp C1);
      first [lia | exact MU1 | exact WM1 | exact Hh1 | exact Hs1]. }
  assert (C2' : arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) m1)).
  { intros a Hro Ho He. rewrite <- (C2 a Hro Ho He).
    assert (Hai : CG0d.in_img SEGS a)
      by (destruct Hro as [(s & Hs & _ & Hr) | Hg]; [exists s; split; [exact Hs | exact Hr] | exact (RELRO_IMG a Hg)]).
    pose proof (cls_img_lt a Hai) as Hia.
    apply (cls_view_munch [(Sp + -64, Sp)]); [exact MU1 | lia | cbn; split; [lia | exact I]]. }
  assert (VA : forall H a, 0 <= a < Sp - 64 -> aview SEGS H m1 a = aview SEGS H memc a).
  { intros H a Ha. apply (cls_view_munch [(Sp + -64, Sp)]); [exact MU1 | lia | cbn; split; [lia | exact I]]. }
  set (regsA := LFr.mkR (Z_to_bv 64 0x8380c) (Z_to_bv 64 (Sp + -64)) (reg_get regs 3) (reg_get regs 4)
         (reg_get regs 5) (reg_get regs 6) (reg_get regs 7) (Z_to_bv 64 v) (reg_get regs 9) (Z_to_bv 64 f)
         (Z_to_bv 64 n) (Z_to_bv 64 o) (Z_to_bv 64 o) (Z_to_bv 64 v) (reg_get regs 15) (reg_get regs 16)
         (reg_get regs 17) (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 u) (Z_to_bv 64 BRT.ASAN_K) (reg_get regs 22)
         (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27)
         (reg_get regs 28) (reg_get regs 29) (reg_get regs 30) (reg_get regs 31)).
  assert (ESA : CG0d.spZ regsA = Sp - 64).
  { unfold CG0d.spZ. change (CK11.getr regsA 2) with (Z_to_bv 64 (Sp + -64)).
    rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia). lia. }
  change (SRr SEGS W (cfg_at SEGS BPS.A_reac_ctrl_parseP regsA m1 md1)
            (treac_ctrl_classify_box_frame_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs
               n o v fr us)).
  eapply SRr_bind.
  { eapply (TPARSE STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m1 md1 k regsA f n o fr).
    - exact J1.
    - exact C2'.
    - apply CK0s.ret_ok_even. reflexivity.
    - change (raZ regsA) with 0x8380c. lia.
    - exact C4a.
    - exact C4b.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact C5r.
    - rewrite ESA. Z.div_mod_to_equations. lia.
    - rewrite ESA. unfold BPS.REAC_CTRL_PARSE_STK. lia.
    - rewrite ESA. lia.
    - exact C8.
    - exact C9.
    - intros _. split; [exact (ex_intro _ co (ex_intro _ po (conj Ino (conj Hco (conj Hfo8 (conj Hfo1 Hfo2))))))|].
      split; [exact Ho8|].
      apply (cls_ra_transfer (aview SEGS (w_H W) memc)); [|exact RAo].
      intros x Hx. apply VA. unfold shadow_of_addr, SHADOW_OFF. Z.div_mod_to_equations. lia.
    - intros _ a Ha. exact (C13 a Ha).
    - exact C10.
    - intros Hn i Hi. rewrite <- (C11 Hn i Hi). apply VA.
      destruct (C9 Hn) as (Lf & InF & HLf).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ f Lf HAR InF) as (_ & Hf0 & Hf1 & _). lia. }
  (* G2: from reac_ctrl_parse's post to stretch B's start state *)
  intros W2 c2 Hle (ly2 & S2 & regs2 & mem2 & md2 & Ec2 & J2 & Hpr2 & Hfr2 & Hbl2 & _ & Ha02 & Ho2 & KP).
  subst c2.
  rewrite ESA in KP.
  pose proof KP as (KP1 & KP2 & KP3 & KP4 & KP5 & KP6).
  pose proof J2 as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _ & _ & _).
  destruct (PWRC.RT_used_of_AR_C B TS LAWS _ _ _ _ _ HAR2) as (RAC2 & RCUT2 & _ & _ & RCF2 & _ & _ & RR2).
  assert (C2'' : arodata_okS SEGS B RLO RHI (aview SEGS (w_H W2) mem2)).
  { intros a Hro Ho He.
    assert (Hai : CG0d.in_img SEGS a)
      by (destruct Hro as [(s & Hs & _ & Hr) | Hg]; [exists s; split; [exact Hs | exact Hr] | exact (RELRO_IMG a Hg)]).
    rewrite (KP3 a Hai Ho He). exact (C2' a Hro Ho He). }
  pose proof (cls_ro_of_AR _ _ _ _ _ HAR2 C2'') as RO2.
  assert (HF2 : forall c p, frame_addr ly2 c p = frame_addr lyc c p).
  { intros c p. unfold frame_addr.
    destruct Hly as (_ & _ & _ & _ & _ & EF1 & _). destruct Hly2 as (_ & _ & _ & _ & _ & EF2 & _).
    rewrite EF1, EF2. reflexivity. }
  assert (HSL2 : ly_stk_lo ly2 = ly_stk_lo ly /\ ly_stk_hi ly2 = ly_stk_hi ly).
  { destruct Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E1' & E2' & _). split; assumption. }
  assert (Ino2 : In (co, po) (CG01.frames S2)) by (rewrite Hfr2; exact Ino).
  assert (Inv2 : In (cv, pv) (CG01.frames S2)) by (rewrite Hfr2; exact Inv).
  (* the caller's v bytes at the parse-return memory *)
  destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 cv pv HAR2 Inv2) as (_ & _ & Pv2 & _).
  destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 co po HAR2 Ino2) as (_ & _ & Po2 & _).
  rewrite HF2 in Pv2, Po2.
  destruct (cls_cells4_of_pres (w_H W2) mem2 v ltac:(lia) ltac:(lia)
              (fun x Hx => proj1 (Pv2 x ltac:(lia)))) as (vb & Lvb & HVv).
  (* visibility at W2 *)
  assert (VO2 : BPB.range_visible (w_H W2) o 36)
    by (apply (cls_frame_vis B LAWS ly2 S2 W2 mem2 md2 co po o 36 HAR2 Ino2); rewrite HF2; lia).
  assert (VV2 : BPB.range_visible (w_H W2) v 4)
    by (apply (cls_frame_vis B LAWS ly2 S2 W2 mem2 md2 cv pv v 4 HAR2 Inv2); rewrite HF2; lia).
  (* the stretch-B start state *)
  change (CK11.mkst regs2 (CK11.getr regsA 1) mem2 (CK11.seg_rom SEGS))
    with (LMS.MS regs2 CK11.fp_regs (Z_to_bv 64 0x8380c) CK11.fp_csr None mem2 (CK11.seg_rom BI.rsegs)).
  assert (XR2 : LRg.xregs_eqv
    (LFr.mkR (reg_get regs2 1) (Z_to_bv 64 (Sp + -64)) (reg_get regs 3) (reg_get regs 4) (reg_get regs2 5)
       (reg_get regs2 6) (reg_get regs2 7) (Z_to_bv 64 v) (reg_get regs2 9) (Z_to_bv 64 (fst (ctrlparse n fr)))
       (reg_get regs2 11) (reg_get regs2 12) (reg_get regs2 13) (reg_get regs2 14) (reg_get regs2 15)
       (reg_get regs2 16) (reg_get regs2 17) (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 u) (Z_to_bv 64 BRT.ASAN_K)
       (reg_get regs2 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
       (reg_get regs 27) (reg_get regs2 28) (reg_get regs2 29) (reg_get regs2 30) (reg_get regs2 31)) regs2).
  { apply LRg.xregs_eqv_sym. apply LRg.mkR_eqv_of;
      first [ reflexivity | exact Ha02
            | exact (Hpr2 2 ltac:(unfold acallee_saved; lia)) | exact (Hpr2 3 ltac:(unfold acallee_saved; lia))
            | exact (Hpr2 4 ltac:(unfold acallee_saved; lia)) | exact (Hpr2 8 ltac:(unfold acallee_saved; lia))
            | exact (Hpr2 18 ltac:(unfold acallee_saved; lia)) | exact (Hpr2 19 ltac:(unfold acallee_saved; lia))
            | exact (Hpr2 20 ltac:(unfold acallee_saved; lia)) | exact (Hpr2 21 ltac:(unfold acallee_saved; lia))
            | exact (Hpr2 23 ltac:(unfold acallee_saved; lia)) | exact (Hpr2 24 ltac:(unfold acallee_saved; lia))
            | exact (Hpr2 25 ltac:(unfold acallee_saved; lia)) | exact (Hpr2 26 ltac:(unfold acallee_saved; lia))
            | exact (Hpr2 27 ltac:(unfold acallee_saved; lia)) ]. }
  refine (KR.SRr_xregs_eqv SEGS W2 _ regs2 _ _ _ _ _ _ _ _ _ XR2).
  apply (cls_liftB BWon.bcmp_wrap_holds_F_on W2 md2 (reg_get regs 1) (reg_get regs 3) (reg_get regs 4)
           (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21)
           (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
           (reg_get regs 27) mem2 f n u o v Sp fr us vb
           (reg_get regs2 1) (reg_get regs2 5) (reg_get regs2 6) (reg_get regs2 7) (reg_get regs2 9)
           (reg_get regs2 11) (reg_get regs2 12) (reg_get regs2 13) (reg_get regs2 14) (reg_get regs2 15)
           (reg_get regs2 16) (reg_get regs2 17) (reg_get regs2 22) (reg_get regs2 28) (reg_get regs2 29)
           (reg_get regs2 30) (reg_get regs2 31)).
  - exact C5fr.
  - exact C5ur.
  - lia.
  - lia.
  - unfold BRT.APPMEM_END. lia.
  - exact C7a.
  - exact C10.
  - exact C16.
  - (* HF *)
    intros Hn. destruct (C9 Hn) as (Lf & InF & HLf).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ f Lf HAR InF) as (_ & Hf0 & Hf1 & _).
    assert (InF2 : In (f, Lf) (ablocks B ly2 S2)) by (rewrite Hbl2; exact InF).
    pose proof (cls_block_vis B LAWS ly2 S2 W2 mem2 md2 f Lf f 50 HAR2 InF2 ltac:(lia) ltac:(lia)) as (_ & _ & VF).
    split; [lia|]. split; [lia|]. split; [|left; lia].
    apply (cls_bytes_of_view (w_H W2) mem2 f fr cp_z); [lia | rewrite C10; lia | |].
    + intros i Hi. rewrite C10 in Hi. apply VF. lia.
    + intros i Hi. rewrite C10 in Hi.
      pose proof (sep_block_frame SEGS B LAWS lyc Sc W memc mdc f Lf co po HAR InF Ino) as SBo.
      unfold zdisjoint, frame_rng in SBo; cbn [fst snd] in SBo.
      rewrite (KP2 f Lf (Z.of_nat i) InF ltac:(lia) ltac:(cbn; lia)).
      rewrite VA by lia. exact (C11 Hn i Hi).
  - (* HU *)
    intros Hn. destruct (C17 Hn) as ((cu & pu & Inu & Hcu & Hfu8 & Hfu1 & Hfu2) & Hu8 & RAu).
    destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cu pu HAR Inu) as (Fu1 & Fu2 & Fu3).
    pose proof (fs_frame_bytes_nonneg cu) as Fun.
    assert (Inu2 : In (cu, pu) (CG01.frames S2)) by (rewrite Hfr2; exact Inu).
    pose proof (cls_frame_vis B LAWS ly2 S2 W2 mem2 md2 cu pu u 6 HAR2 Inu2 ltac:(rewrite HF2; lia)
                  ltac:(rewrite HF2; lia)) as (_ & _ & VU).
    split; [lia|]. split; [|left; lia].
    apply (cls_bytes_of_view (w_H W2) mem2 u us cp_z); [lia | rewrite C16; lia | |].
    + intros i Hi. rewrite C16 in Hi. apply VU. lia.
    + intros i Hi. rewrite C16 in Hi.
      rewrite (KP4 cu pu (u + Z.of_nat i) Inu ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; lia) ltac:(lia)).
      rewrite VA by lia. exact (C18 Hn i Hi).
  - lia.
  - Z.div_mod_to_equations. lia.
  - lia.
  - left. lia.
  - intros Hn. destruct (C9 Hn) as (Lf & InF & HLf).
    pose proof (sep_block_frame SEGS B LAWS lyc Sc W memc mdc f Lf co po HAR InF Ino) as SBo.
    unfold zdisjoint in SBo; cbn [fst snd] in SBo. lia.
  - exact C19.
  - lia.
  - Z.div_mod_to_equations. lia.
  - lia.
  - left. lia.
  - exact C20.
  - exact C22.
  - exact C21.
  - exact B3.
  - (* AFU *)
    intros Hn. destruct (C9 Hn) as (Lf & InF & HLf).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ f Lf HAR InF) as (_ & Hf0 & Hf1 & Hf2 & _).
    assert (InF2 : In (f, Lf) (ablocks B ly2 S2)) by (rewrite Hbl2; exact InF).
    destruct (C17 Hn) as ((cu & pu & Inu & Hcu & Hfu8 & Hfu1 & Hfu2) & Hu8 & RAu).
    destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cu pu HAR Inu) as (Fu1 & Fu2 & Fu3).
    pose proof (fs_frame_bytes_nonneg cu) as Fun.
    pose proof (@CM05.alloc_ceiling_lt rc) as Hcl.
    split; [|split; [|split]].
    + apply (cls_addressable_of_view W2 mem2 f 50); [lia | lia | unfold BRT.APPMEM_END; lia | |].
      * intros i Hi. apply (cls_app_of_in_app _ _ (f + i) Hf2). lia.
      * exact (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 f Lf f 50 HAR2 InF2
                 ltac:(lia) ltac:(lia)).
    + apply (cls_addressable_of_view W2 mem2 u 6); [lia | lia | unfold BRT.APPMEM_END; lia | |].
      * intros i Hi. apply (cls_app_of_in_app _ _ (u + i) Fu3). lia.
      * apply (cls_ra_transfer (aview SEGS (w_H W) memc)); [|exact RAu].
        intros x Hx. rewrite (KP4 cu pu (shadow_of_addr SHADOW_OFF x) Inu).
        { apply VA. unfold shadow_of_addr, SHADOW_OFF. Z.div_mod_to_equations. lia. }
        { right. destruct (cls_frame_al64 B lyc Sc W memc mdc cu pu HAR Inu) as (Au1 & Au2 & _).
          apply cls_sh_in_frame; [exact Hfu8 | exact (cls_mod64_8 _ Au2) | lia]. }
        { exact (cls_sh_not_in_app _ _ o 36 x Fo3 ltac:(lia) ltac:(lia) ltac:(lia)). }
    + destruct (cls_frame_al64 B lyc Sc W memc mdc cu pu HAR Inu) as (_ & Fub & _).
      pose proof (cls_al8_room u (frame_addr lyc cu pu + fs_frame_bytes cu) Hu8
                    ltac:(rewrite Zplus_mod, Hfu8, (cls_mod64_8 _ Fub); reflexivity) Hfu2) as R8.
      apply (cls_app_of_in_app _ _ (u + 6) Fu3). lia.
    + destruct (cls_frame_al64 B lyc Sc W memc mdc cu pu HAR Inu) as (_ & Fub & _).
      pose proof (cls_al8_room u (frame_addr lyc cu pu + fs_frame_bytes cu) Hu8
                    ltac:(rewrite Zplus_mod, Hfu8, (cls_mod64_8 _ Fub); reflexivity) Hfu2) as R8.
      apply (cls_app_of_in_app _ _ (u + 7) Fu3). lia.
  - (* AO *)
    apply (cls_addressable_of_view W2 mem2 o 36);
      [lia | lia | pose proof (@CM05.alloc_ceiling_lt rc); unfold BRT.APPMEM_END; lia | |].
    + intros i Hi. apply (cls_app_of_in_app _ _ (o + i) Fo3). lia.
    + apply (cls_ra_transfer (aview SEGS (w_H W) memc)); [|exact RAo].
      intros x Hx. rewrite (KP4 co po (shadow_of_addr SHADOW_OFF x) Ino).
      { apply VA. unfold shadow_of_addr, SHADOW_OFF. Z.div_mod_to_equations. lia. }
      { right. destruct (cls_frame_al64 B lyc Sc W memc mdc co po HAR Ino) as (Ao1 & Ao2 & _).
        apply cls_sh_in_frame; [exact Hfo8 | exact (cls_mod64_8 _ Ao2) | lia]. }
      { exact (cls_sh_not_in_app _ _ o 36 x Fo3 ltac:(lia) ltac:(lia) ltac:(lia)). }
  - (* AV *)
    apply (cls_addressable_of_view W2 mem2 v 4);
      [lia | lia | pose proof (@CM05.alloc_ceiling_lt rc); unfold BRT.APPMEM_END; lia | |].
    + intros i Hi. apply (cls_app_of_in_app _ _ (v + i) Fv3). lia.
    + apply (cls_ra_transfer (aview SEGS (w_H W) memc)); [|exact RAv].
      intros x Hx. rewrite (KP4 cv pv (shadow_of_addr SHADOW_OFF x) Inv).
      { apply VA. unfold shadow_of_addr, SHADOW_OFF. Z.div_mod_to_equations. lia. }
      { right. destruct (cls_frame_al64 B lyc Sc W memc mdc cv pv HAR Inv) as (Av1 & Av2 & _).
        apply cls_sh_in_frame; [exact Hfv8 | exact (cls_mod64_8 _ Av2) | lia]. }
      { exact (cls_sh_not_in_app _ _ o 36 x Fo3 ltac:(lia) ltac:(lia) ltac:(lia)). }
  - (* HVR: [RT_LO, RT_HI) lies in the image, v does not *)
    destruct (Z_le_gt_dec (v + 4) BRT.RT_LO); [left; lia|].
    destruct (Z_le_gt_dec BRT.RT_HI v); [right; lia|].
    exfalso. apply (NIv (Z.max v BRT.RT_LO - v)); [unfold BRT.RT_LO, BRT.RT_HI in *; lia|].
    replace (v + (Z.max v BRT.RT_LO - v)) with (Z.max v BRT.RT_LO) by lia.
    apply cls_img_in. unfold BRT.RT_LO, BRT.RT_HI in *. lia.
  - exact NIo.
  - exact NIv.
  - (* VW *)
    split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hpres2 a ltac:(lia))).
  - exact VO2.
  - apply (cls_hull_vis W2 mem2 o 36); [lia | pose proof (@CM05.alloc_ceiling_lt rc); lia | lia |].
    exact (cls_shadow_hull_vis_of_frame B LAWS ly2 S2 W2 mem2 md2 co po o 36 HAR2 Ino2
             ltac:(rewrite HF2; lia) ltac:(rewrite HF2; lia) ltac:(lia)).
  - exact VV2.
  - pose proof (cls_hull_vis W2 mem2 v 4 ltac:(lia) ltac:(pose proof (@CM05.alloc_ceiling_lt rc); lia) ltac:(lia)
                  (cls_shadow_hull_vis_of_frame B LAWS ly2 S2 W2 mem2 md2 cv pv v 4 HAR2 Inv2
                     ltac:(rewrite HF2; lia) ltac:(rewrite HF2; lia) ltac:(lia))) as VH.
    apply (cls_vis_sub _ _ _ _ _ VH); unfold BRT.shadow_addr, BRT.ASAN_K; Z.div_mod_to_equations; lia.
  - intros Hn. destruct (C9 Hn) as (Lf & InF & HLf).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ f Lf HAR InF) as (_ & Hf0 & Hf1 & _).
    assert (InF2 : In (f, Lf) (ablocks B ly2 S2)) by (rewrite Hbl2; exact InF).
    exact (cls_block_vis B LAWS ly2 S2 W2 mem2 md2 f Lf f 50 HAR2 InF2 ltac:(lia) ltac:(lia)).
  - intros Hn. destruct (C9 Hn) as (Lf & InF & HLf).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ f Lf HAR InF) as (_ & Hf0 & Hf1 & _).
    assert (InF2 : In (f, Lf) (ablocks B ly2 S2)) by (rewrite Hbl2; exact InF).
    apply (cls_hull_vis W2 mem2 f 50); [lia | pose proof (@CM05.alloc_ceiling_lt rc); lia | lia |].
    exact (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 f Lf f 50 HAR2 InF2
             ltac:(lia) ltac:(lia) ltac:(lia)).
  - intros Hn. destruct (C17 Hn) as ((cu & pu & Inu & Hcu & Hfu8 & Hfu1 & Hfu2) & Hu8 & RAu).
    assert (Inu2 : In (cu, pu) (CG01.frames S2)) by (rewrite Hfr2; exact Inu).
    exact (cls_frame_vis B LAWS ly2 S2 W2 mem2 md2 cu pu u 6 HAR2 Inu2 ltac:(rewrite HF2; lia)
             ltac:(rewrite HF2; lia)).
  - intros Hn. destruct (C17 Hn) as ((cu & pu & Inu & Hcu & Hfu8 & Hfu1 & Hfu2) & Hu8 & RAu).
    destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cu pu HAR Inu) as (Fu1 & Fu2 & Fu3).
    assert (Inu2 : In (cu, pu) (CG01.frames S2)) by (rewrite Hfr2; exact Inu).
    apply (cls_hull_vis W2 mem2 u 6); [lia | pose proof (@CM05.alloc_ceiling_lt rc); lia | lia |].
    exact (cls_shadow_hull_vis_of_frame B LAWS ly2 S2 W2 mem2 md2 cu pu u 6 HAR2 Inu2
             ltac:(rewrite HF2; lia) ltac:(rewrite HF2; lia) ltac:(lia)).
  - (* the saved registers at [S - 64, S) *)
    destruct RW1 as ((Wf1 & HB1) & _). split; [split; [exact Wf1|] | ].
    + apply (cls_bytes_transfer (w_H W) (w_H W2) m1 mem2 (Sp + -64));
        [lia | rewrite LCe.cells_bytes_length by exact Wf1; cbn; lia | | | exact HB1].
      * intros i Hi. rewrite LCe.cells_bytes_length in Hi by exact Wf1. cbn in Hi.
        split; [exact (proj1 (Hpres (Sp + -64 + i) ltac:(lia))) | exact (proj1 (Hpres2 (Sp + -64 + i) ltac:(lia)))].
      * intros i Hi. rewrite LCe.cells_bytes_length in Hi by exact Wf1. cbn in Hi.
        apply KP1; [lia | unfold BPS.REAC_CTRL_PARSE_STK; lia].
    + apply (cls_wr_of_pres (w_H W2)); [lia | cbn; lia | intros x Hx; cbn in Hx; apply Hpres2; lia].
  - (* o's 36 bytes = parse's model *)
    apply (cls_bytes_of_view (w_H W2) mem2 o (snd (ctrlparse n fr)) cp_z);
      [lia | rewrite ctrlparse_length; lia | |].
    + intros i Hi. rewrite ctrlparse_length in Hi. destruct VO2 as (_ & _ & VO2'). apply VO2'. lia.
    + intros i Hi. rewrite ctrlparse_length in Hi. apply Ho2; [lia | exact Hi].
  - apply (cls_wr_of_pres (w_H W2)); [lia | lia | intros x Hx; apply (proj1 (Po2 x ltac:(lia)))].
  - exact HVv.
  - apply (cls_stk_of_pres (w_H W2)); [lia | lia | intros a Ha; apply Hpres2; lia].
  - exact RO2.
  - exact RAC2.
  - (* route (C): stretch B's region of record (the two bcmp calls' range-check words of o + 4 / o + 10, 6 of o's 36
       bytes, and of u, 6 bytes) lies in cut_shadow B ly2 S2's (F) disjunct: o and u are bytes of caller frames
       (C12 / C17), still in frames S2 (Hfr2), at the same addresses (HF2), 64-aligned (cls_frame_al64). *)
    apply (SRO.shadow_rw_on_mono (ARC.cut_shadow B ly2 S2)); [| exact RCUT2].
    intros a Ha. unfold BCLS.reac_ctrl_classify_box_frame_post_call_shadow_R, BWo.bcmp_wrap_shadow_R in Ha.
    destruct (cls_frame_al64 B lyc Sc W memc mdc co po HAR Ino) as (Ao1 & Ao2 & _).
    destruct Ha as (HN & [[Ha | Ha] | [Ha | Ha]]);
      destruct (C17 HN) as ((cu & pu & Inu & _ & _ & Hfu1 & Hfu2) & _ & _);
      destruct (cls_frame_al64 B lyc Sc W memc mdc cu pu HAR Inu) as (Au1 & Au2 & _);
      assert (Inu2 : In (cu, pu) (CG01.frames S2)) by (rewrite Hfr2; exact Inu);
      unfold ARC.cut_shadow; left.
    + exists co, po. split; [exact Ino2|]. rewrite HF2.
      apply (cls_sh_word_frame _ _ (o + 4) 6 a Ao1 Ao2); [lia | lia | lia | exact Ha].
    + exists cu, pu. split; [exact Inu2|]. rewrite HF2.
      apply (cls_sh_word_frame _ _ u 6 a Au1 Au2); [lia | lia | lia | exact Ha].
    + exists co, po. split; [exact Ino2|]. rewrite HF2.
      apply (cls_sh_word_frame _ _ (o + 10) 6 a Ao1 Ao2); [lia | lia | lia | exact Ha].
    + exists cu, pu. split; [exact Inu2|]. rewrite HF2.
      apply (cls_sh_word_frame _ _ u 6 a Au1 Au2); [lia | lia | lia | exact Ha].
  - apply (cls_win_addressable B LAWS ly2 S2 W2 mem2 md2); [exact HAR2 | rewrite (proj1 HSL2); lia
      | rewrite (proj2 HSL2); lia | lia | exact B3 | unfold BRT.APPMEM_END; lia].
  - rewrite Forall_forall in RR2. exact (RR2 (0xa2610, 0x98930)
      ltac:(unfold BRT.RT_REALS; repeat first [left; reflexivity | right]) ltac:(unfold PW.REAL_USED; cbn; tauto)).
  - rewrite Forall_forall in RR2. exact (RR2 (0xa2608, 0x98a00)
      ltac:(unfold BRT.RT_REALS; repeat first [left; reflexivity | right]) ltac:(unfold PW.REAL_USED; cbn; tauto)).
  - exact (proj1 RCF2).
  - destruct RCF2 as (_ & _ & _ & _ & _ & _ & CFb & _).
    pose proof (cls_bytes_one _ _ _ 14 (Z_to_bv 8 0) CFb ltac:(cbn; lia)) as X.
    replace (BRT.RT_CF + 240 + Z.of_nat 14) with (BBC.CF + 254) in X by (unfold BRT.RT_CF, BBC.CF; lia). exact X.
  - destruct RCF2 as (_ & _ & _ & _ & _ & _ & CFb & _).
    pose proof (cls_bytes_one _ _ _ 15 (Z_to_bv 8 0) CFb ltac:(cbn; lia)) as X.
    replace (BRT.RT_CF + 240 + Z.of_nat 15) with (BBC.CF + 255) in X by (unfold BRT.RT_CF, BBC.CF; lia). exact X.
  - (* G3: the post *)
    intros ms3 md3 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & E3 & MU3 &
                    WM3 & ST3 & RWo3 & RWv3 & AW3) Hh3 Hs3.
    subst ms3. apply SRr_ret.
    assert (AW2 : BRT.addressable mem2 (Sp - 8864) 8864).
    { apply (cls_win_addressable B LAWS ly2 S2 W2 mem2 md2); [exact HAR2 | rewrite (proj1 HSL2); lia
        | rewrite (proj2 HSL2); lia | lia | exact B3 | unfold BRT.APPMEM_END; lia]. }
    assert (Wo2 : forall a, o <= a < o + 36 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly2 S2) ly2 own a).
    { intros a Ha. rewrite Hbl2. destruct (C13 a Ha) as [Q|[Q|[Q|(cid & pos & Hown & Q)]]];
        [left; exact Q | right; left; exact Q | right; right; left; exact Q | right; right; right].
      exists cid, pos. split; [exact Hown|]. rewrite !HF2. exact Q. }
    assert (Wv2 : forall a, v <= a < v + 4 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly2 S2) ly2 own a).
    { intros a Ha. rewrite Hbl2. destruct (C15 a Ha) as [Q|[Q|[Q|(cid & pos & Hown & Q)]]];
        [left; exact Q | right; left; exact Q | right; right; left; exact Q | right; right; right].
      exists cid, pos. split; [exact Hown|]. rewrite !HF2. exact Q. }
    assert (J3 : ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 m3 md3 k).
    { apply (cls_journal_B B LAWS STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k m3 md3 Sp o v J2);
        first [lia | Z.div_mod_to_equations; lia | exact NIo | exact NIv | exact MU3 | exact WM3 | exact AW2
              | exact AW3 | exact Hh3 | exact Hs3 | exact Wo2 | exact Wv2 | (unfold BRT.APPMEM_END; lia)]. }
    pose proof J3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _ & _ & _).
    exists ly2, S2,
      (LFr.mkR (reg_get regs 1) (Z_to_bv 64 Sp) (reg_get regs 3) (reg_get regs 4) t0' t1' t2' (reg_get regs 8)
         (reg_get regs 9) (Z_to_bv 64 (cl_r (classify n fr us))) a1' a2' a3' a4' a5' a6' a7' (reg_get regs 18)
         (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23)
         (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) t3' t4' t5' t6'), m3, md3.
    split.
    { (* Q1 *)
      rewrite (cls_ret_pc_ok (reg_get regs 1) C3a). reflexivity. }
    split.
    { (* Q2 *)
      unfold EV_CLASSIFY. rewrite Z.add_0_r. exact J3. }
    split.
    { (* Q3 *)
      intros r Hr. unfold acallee_saved in Hr.
      assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
        try reflexivity.
      change (CK11.getr regs (Z_to_bv 5 2)) with (reg_get regs 2).
      change (CK11.getr _ (Z_to_bv 5 2)) with (Z_to_bv 64 Sp).
      unfold Sp, CG0d.spZ. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned. reflexivity. }
    split; [exact Hfr2|]. split; [exact Hbl2|].
    split; [reflexivity|].
    split.
    { (* Q5 *)
      intros i Hi. destruct RWo3 as ((_ & Bo3) & _). destruct Bo3 as (_ & _ & Bo3).
      destruct VO2 as (_ & _ & VO2').
      assert (Hi' : (i < length (LCe.cells_bytes [LCe.CB 36 (snd (ctrlparse n fr))]))%nat)
        by (cbn [LCe.cells_bytes LCe.cbytes]; rewrite app_nil_r, ctrlparse_length; exact Hi).
      pose proof (Bo3 i Hi') as Bi. cbn [LCe.cells_bytes LCe.cbytes] in Bi. rewrite app_nil_r in Bi.
      rewrite (cls_aview_mrd (w_H W2) m3 (o + Z.of_nat i) (VO2' (o + Z.of_nat i) ltac:(lia))), Bi.
      rewrite (nth_error_nth' (snd (ctrlparse n fr)) cp_z ltac:(rewrite ctrlparse_length; exact Hi)).
      reflexivity. }
    split.
    { (* Q6 *)
      intros e He. destruct RWv3 as ((_ & Bv3) & _). rewrite He in Bv3. cbn [LCe.cells_bytes LCe.cbytes] in Bv3.
      rewrite app_nil_r in Bv3. unfold UCc.reac_ctrl_classify_box_frame_ev in Bv3.
      destruct Bv3 as (_ & _ & Bv3). destruct VV2 as (_ & _ & VV2').
      pose proof (cls_classify_range n fr us e He) as Re.
      intros kk Hkk.
      assert (Hl : (kk < length (LMem.le4 (Z_to_bv 64 e)))%nat) by (rewrite LMem.length_le4; exact Hkk).
      pose proof (Bv3 kk Hl) as Bk.
      unfold CP09.mbyte, mrestrict.
      rewrite (VV2' (v + Z.of_nat kk) ltac:(lia)).
      change (match m3 (Z_to_bv 64 (v + Z.of_nat kk)) with Some b => Some b
              | None => CK11.seg_rom SEGS (Z_to_bv 64 (v + Z.of_nat kk)) end)
        with (LMem.mrd BI.rsegs m3 (LMem.wa (v + Z.of_nat kk))).
      rewrite Bk.
      assert (Ee : e = 0 \/ e = 1 \/ e = 2 \/ e = 3 \/ e = 4 \/ e = 5) by lia.
      destruct kk as [|[|[|[|kk]]]]; [| | | | lia];
        destruct Ee as [->|[->|[->|[->|[->| ->]]]]]; vm_compute; reflexivity. }
    { (* Q7 *)
      unfold tclassify_out.
      apply (cls_ack B LAWS lyc Sc W W2 memc mdc m1 mem2 m3 Sp o v (classify n fr us <> None)); try lia.
      - exact HAR.
      - exact NIo.
      - exact NIv.
      - destruct (classify n fr us); [left; discriminate | right; intros Q; apply Q; reflexivity].
      - exact MU1.
      - exact KP.
      - exact MU3.
      - intros Hc i Hi.
        assert (Ec : classify n fr us = None)
          by (destruct (classify n fr us); [exfalso; apply Hc; discriminate | reflexivity]).
        destruct RWv3 as ((_ & Bv3) & _). rewrite Ec in Bv3. cbn [LCe.cells_bytes LCe.cbytes] in Bv3.
        rewrite app_nil_r in Bv3. unfold UCc.reac_ctrl_classify_box_frame_ev in Bv3.
        destruct HVv as ((_ & Bv2) & _). cbn [LCe.cells_bytes LCe.cbytes] in Bv2. rewrite app_nil_r in Bv2.
        destruct Bv3 as (_ & _ & Bv3). destruct Bv2 as (_ & _ & Bv2).
        assert (Hil : (Z.to_nat i < length vb)%nat) by lia.
        pose proof (Bv3 _ Hil) as X3. pose proof (Bv2 _ Hil) as X2. rewrite Z2Nat.id in X3, X2 by lia.
        rewrite <- X2 in X3. unfold LMem.mrd in X3.
        assert (Hrom : LPE.seg_rom BI.rsegs (LMem.wa (v + i)) = None).
        { apply cls_noimg_rom. rewrite LMem.wa_unsigned by lia. exact (NIv i Hi). }
        rewrite Hrom in X3. destruct (m3 (LMem.wa (v + i))), (mem2 (LMem.wa (v + i))); congruence.
      - intros a Ha. apply Hpres3. lia. }
Qed.
End m.

End b.
