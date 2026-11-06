(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/C_reac_ctrl_parse.v; 45 of its 74 lines of code are new or changed and 31 lines of the source are left out. *)
(* reac_ctrl_classify_box_frame (0x831b8) of fuzz_ctrl's ASan build (image A, libreac v1.9.0): its contract, in the
   caller-journal form.  It writes the caller's 4 bytes at v (the checked `sw a1,0(s0)` at 0x832d8, only when the
   model returns Some) and, through reac_ctrl_parse, the caller's 36 bytes at o.  The return value and the bytes are
   the model `classify` (lib/Prog/RcClassify.v) over `ctrlparse` (lib/Prog/RcParse.v).
   STATEMENTS ONLY: this file holds the two Definitions the caller (LLVMFuzzerTestOneInput's walk) and the glue cite.
   The glue `pb_reac_ctrl_classify_box_frame` (rule 24: no function proved; it composes ctrl's two proved v1.9 _F
   stretches, lifted through Reusable/YA0nR.v SRr_fevt_hid, with a Theorem Labs lane's treac_ctrl_parse_spec at the parse call)
   and the Section hypotheses it needs live in the proof file, not here.
   Text: spec-draft.md sections 1.2-1.3 (a working note, not in this delivery) (C6 dropped, a Theorem Labs lane's R5; R1's
   `exists ff, S2 = set_fs ff Sc` stays in parse's post only, a Theorem Labs lane 02:47Z).  The shape is cgif lib/YC20.v:311-365
   (a pattern only).  Generic pieces come from the core: ajournal / awr_byte (Reusable/YCbq.v), afobj
   (Reusable/APostBase.v), arodata_okS (Reusable/YE01.v), tcj_kept (A/Prog/CtrlCallerJ.v, the six conjuncts of
   acall_kept with slo := spZ regs - STK, shi := spZ regs).  Every segment list is tfibsegs (A/AB1v.v); tcj_kept, stated
   over `pa_segs PI_ctrl`, applies by conversion (CtrlImg.v: pa_segs := tfibsegs). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import APostBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import PaTable CtrlList CtrlPa CtrlImg CtrlCallerJ.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcClassify.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
#[local] Notation BASE := (@pa_val _ ctrl_listing PI_ctrl A_TEXT).
(* The entry slot on the position-abstract listing (AF_reac_ctrl_classify_box_frame = 0x22dc, CtrlList.v:14):
   0x80edc + 0x22dc = 0x831b8. *)
Definition A_reac_ctrl_classify_box_frameP : Z := BASE + AF_reac_ctrl_classify_box_frame.
(* The machine stack below sp that the call needs: the window [S - 8864, S) over which ctrl's proved run, and so both
   lifted stretches, are stated: the 64-byte frame of `addi sp,sp,-64` (0x831b8) and 8800 below it, ctrl's
   REAC_CTRL_CLASSIFY_BOX_FRAME_K (lib/A/Prog/reac_ctrl_classify_box_frame_c.v).  reac_ctrl_parse's spec at
   sp = S - 64 needs 64 + REAC_CTRL_PARSE_STK = 8416 of it. *)
Definition REAC_CTRL_CLASSIFY_BOX_FRAME_STK : Z := 8864.
(* The allocator events the call adds to the caller's journal bound: none.  classify makes no heap allocator call,
   and the fake-stack call inside reac_ctrl_parse leaves the event count unchanged (parse's post keeps plain k).
   Stated in the walk-callee form the caller's walk uses (a Theorem Labs lane, 03:35Z). *)
Definition EV_CLS : Z := 0.
Section e.
Variable B : asyms.
Variables RLO RHI : Z.
Definition treac_ctrl_classify_box_frame_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
(W0 : world tfibsegs) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world tfibsegs) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (n o v : Z) (fr us : list byte) : world tfibsegs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom tfibsegs)) md2 /\                                 (* Q1 *)
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_CLS) /\                 (* Q2 *)
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\          (* Q3 *)
getr regs2 10 = w64 (cl_r (classify n fr us)) /\                                                       (* Q4 *)
(forall i, (i < 36)%nat ->                                                                              (* Q5 *)
  aview tfibsegs (w_H W2) mem2 (o + Z.of_nat i) = Some (bv_unsigned (nth i (snd (ctrlparse n fr)) cp_z))) /\
(forall e, classify n fr us = Some e -> val_mem tfibsegs (mrestrict (w_H W2) mem2) v 4 e) /\           (* Q6 *)
tcj_kept (PI := PI_ctrl) B REAC_CTRL_CLASSIFY_BOX_FRAME_STK lyc Sc W memc W2 mem2 (spZ regs)          (* Q7 *)
  (fun a => o <= a < o + 36 \/ (classify n fr us <> None /\ v <= a < v + 4)).
Definition treac_ctrl_classify_box_frame_spec : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (f n u o v : Z)
  (fr us : list byte),
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->                            (* C1 *)
arodata_okS tfibsegs B RLO RHI (aview tfibsegs (w_H W) memc) ->                                       (* C2 *)
lib.Reusable.YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->                                         (* C3 *)
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->                                       (* C4 *)
getr regs 10 = w64 f -> getr regs 11 = w64 n -> getr regs 12 = w64 u ->                              (* C5 *)
getr regs 13 = w64 o -> getr regs 14 = w64 v -> 0 <= n < 2 ^ 64 ->
0 <= f < 2 ^ 64 -> 0 <= u < 2 ^ 64 ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_CTRL_CLASSIFY_BOX_FRAME_STK -> spZ regs <= sp0 ->  (* C7 *)
count_cid 1 (frames Sc) < fs_frames 1 ->                                                              (* C8 *)
(50 <= n -> exists Lf, In (f, Lf) (ablocks B lyc Sc) /\ 50 <= req_size Lf) ->                          (* C9 *)
length fr = 50%nat ->                                                                                 (* C10 *)
(50 <= n -> forall i, (i < 50)%nat -> aview tfibsegs (w_H W) memc (f + Z.of_nat i) = Some (cp_v fr i)) -> (* C11 *)
afobj tfibsegs B lyc Sc W memc o 36 ->                                                                (* C12 *)
(forall a, o <= a < o + 36 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->  (* C13 *)
afobj tfibsegs B lyc Sc W memc v 4 ->                                                                 (* C14 *)
(forall a, v <= a < v + 4 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->   (* C15 *)
length us = 6%nat ->                                                                                  (* C16 *)
(50 <= n -> afobj tfibsegs B lyc Sc W memc u 6) ->                                                    (* C17 *)
(50 <= n -> forall i, (i < 6)%nat -> aview tfibsegs (w_H W) memc (u + Z.of_nat i) = Some (cp_v us i)) -> (* C18 *)
o + 36 <= u \/ u + 6 <= o ->                                                                          (* C19 *)
v + 4 <= o \/ o + 36 <= v ->                                                                          (* C20 *)
v + 4 <= u \/ u + 6 <= v ->                                                                           (* C21 *)
v + 4 <= f \/ f + 50 <= v ->                                                                          (* C22 *)
SRr tfibsegs W (cfg_at tfibsegs A_reac_ctrl_classify_box_frameP regs memc mdc)
  (treac_ctrl_classify_box_frame_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs n o v fr us).
End e.
End b.
