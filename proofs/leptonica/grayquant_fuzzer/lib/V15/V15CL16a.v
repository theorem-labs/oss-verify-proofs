(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)

From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require PropExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatSim.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StepTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Hoare.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require ShapeAlg.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require AllocIface.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require PureModel.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require VmLedger.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StoreOk.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require FPSteps.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require AllocBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require WalksLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptArith.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptRoomPC.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptRoom14.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExecW.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExecT.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL8a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptPixCreate.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL10a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptPixCopy.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL14a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL15a.
Module V15LeptGq_iface.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPSteps.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoomPC.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom14.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecW.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecT.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import V15CL8a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCreate.
Import V15CL10a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCopy.
Import V15CL14a.
Import V15CL15a.
(* [comment removed for export] *)









Import V15CL8a.V15LeptPixHdr.


Import V15CL10a.V15LeptCmapValid.


Import V15CL14a.V15LeptDither_iface.

Import V15CL15a.V15LeptOwn.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition PC_fuzz : Z := 86856.
Definition PC_pixDeserialize : Z := 162088.
Definition PC_pixCopy : Z := 96784.
Definition PC_pixDestroy_gq : Z := 94372.
Definition PC_F1 : Z := 116080.      (* [comment removed for export] *)
Definition PC_F2 : Z := 112068.      (* [comment removed for export] *)
Definition PC_F3 : Z := 114844.      (* [comment removed for export] *)
Definition PC_F4 : Z := 123164.      (* [comment removed for export] *)
Definition PC_F5 : Z := 124628.      (* [comment removed for export] *)
Definition PC_F6 : Z := 119812.      (* [comment removed for export] *)
Definition TP_gq : Z := 284096.
Definition GQ_EDGES : Z := 66371.
(* [comment removed for export] *)
Definition F32_ZERO : word := Z_to_bv 64 0xffffffff00000000.

(* [comment removed for export] *)
Definition GQ_STACK_F : Z := 12288.          (* [comment removed for export] *)
Definition RK_mask : Z := RK_pix.            Definition RB_mask : Z := RB_pix14.
Definition RK_thr_gq : Z := 10 + RK_pix + RK_rmc.
Definition RB_thr_gq : Z := 10 * 2 ^ 17 + RB_pix14 + RB_rmc.
(* [comment removed for export] *)
Definition RK_gq : Z := RK_deser + 6 * RK_pixcopy + RK_d2bpp + RK_dbin + 3 * RK_mask + RK_thr_gq.
Definition RB_gq : Z := RB_deser + 6 * RB_pixcopy14 + RB_d2bpp + RB_dbin + 3 * RB_mask + RB_thr_gq.

Section GqIface.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition gq_res {fx : FPState} (C : lctx) (A A' : AS) (m' : word -> option byte) (regs' : bvmap 5 word) : Prop :=
  (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
  \/ (exists pixd w' h' dd cd datad cv', getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd w' h' dd cd datad cv' /\ (0 < 4 * (wpl_of w' dd * h'))%Z).

Definition gq_F_contract (pc : Z) (ARGS : FPState -> bvmap 5 word -> Prop) (STK RK RB : Z) : Prop :=
  forall (fx : FPState) C X A m md regs (s pix w h d cd data ad kd kna kn : Z) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + STK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 TP_gq ->
  getr regs 10 = Z_to_bv 64 pix -> ARGS fx regs ->
  oown C X A m pix w h d cd data ad kd kna kn -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK <= kR)%Z -> (RB <= bR)%Z ->
  (forall (fx' : FPState) A' m' vm' regs', frm_zero (@fp_csr fx') -> W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     gq_res C A A' m' regs' -> aroom A' vm' (kR - RK) (bR - RB) ->
     realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 pc) m al_rom) md) S.

Definition F1_contract : Prop := gq_F_contract PC_F1 (fun _ r => getr r 11 = Z_to_bv 64 1) GQ_STACK_F RK_d2bpp RB_d2bpp.
Definition F2_contract : Prop := gq_F_contract PC_F2 (fun _ _ => True) GQ_STACK_F RK_dbin RB_dbin.
Definition F3_contract : Prop := gq_F_contract PC_F3 (fun _ r => getr r 11 = Z_to_bv 64 1 /\ getr r 12 = Z_to_bv 64 2 /\ getr r 13 = Z_to_bv 64 1 /\ getr r 14 = Z_to_bv 64 1)
                                               GQ_STACK_F RK_mask RB_mask.
Definition F4_contract : Prop := gq_F_contract PC_F4 (fun fx r => getr r 11 = Z_to_bv 64 1 /\ getr r 12 = Z_to_bv 64 1 /\ getr r 13 = Z_to_bv 64 1 /\
                                                                   reg_get (@fp_regs fx) 10%bv = F32_ZERO /\ reg_get (@fp_regs fx) 11%bv = F32_ZERO)
                                               GQ_STACK_F RK_mask RB_mask.
Definition F5_contract : Prop := gq_F_contract PC_F5 (fun _ r => getr r 11 = Z_to_bv 64 10 /\ getr r 12 = Z_to_bv 64 10 /\ getr r 13 = Z_to_bv 64 1) GQ_STACK_F RK_mask RB_mask.
Definition F6_contract : Prop := gq_F_contract PC_F6 (fun _ r => getr r 11 = Z_to_bv 64 GQ_EDGES /\ getr r 12 = Z_to_bv 64 8 /\ getr r 13 = Z_to_bv 64 0 /\
                                                                  getr r 14 = Z_to_bv 64 0 /\ getr r 15 = Z_to_bv 64 0) GQ_STACK_F RK_thr_gq RB_thr_gq.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma copy_oown : forall (fx : FPState) C A A' (m' : word -> option byte) (regs' : bvmap 5 word) (w h d : Z) (cv : cmapv),
  hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
    \/ (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd w h d cd data cv) ) ->
  exists pixc cd data ad, getr regs' 10 = Z_to_bv 64 pixc /\ oown C A A' m' pixc w h d cd data ad (c_d cv) (c_nalloc cv) (c_n cv) /\
                          (forall q, ~ oblk pixc data cd ad q -> live A' q = live A q).
Proof.
  intros fx C A A' m' regs' w h d cv HOK Hw Hh [[A0 LEQ] | (pixd & cd & data & A0 & PN)].
  - exists 0%Z, 0%Z, 0%Z, 0%Z. split; [exact A0|]. split; [left; reflexivity | intros q _; apply LEQ].
  - destruct (pixt_new_pown C A A' m' pixd w h d cd data cv PN (raster_pos w h d HOK Hw Hh)) as (ad & OWN & LEQ).
    exists pixd, cd, data, ad. split; [exact A0|]. split; [right; exact OWN|]. intros q NB. apply LEQ. intros B. apply NB. split; [|exact B].
    destruct OWN as (Gp & _). lia.
Qed.

(* [comment removed for export] *)
Lemma res_oown : forall (fx : FPState) C A A' (m' : word -> option byte) (regs' : bvmap 5 word), gq_res C A A' m' regs' ->
  exists r w' h' dd cd data ad kd kna kn, getr regs' 10 = Z_to_bv 64 r /\ oown C A A' m' r w' h' dd cd data ad kd kna kn /\
                                          (forall q, ~ oblk r data cd ad q -> live A' q = live A q).
Proof.
  intros fx C A A' m' regs' [[A0 LEQ] | (pixd & w' & h' & dd & cd & data & cv' & A0 & PN & Rpos)].
  - exists 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z. split; [exact A0|]. split; [left; reflexivity | intros q _; apply LEQ].
  - destruct (pixt_new_pown C A A' m' pixd w' h' dd cd data cv' PN Rpos) as (ad & OWN & LEQ).
    exists pixd, w', h', dd, cd, data, ad, (c_d cv'), (c_nalloc cv'), (c_n cv'). split; [exact A0|]. split; [right; exact OWN|]. intros q NB. apply LEQ. intros B. apply NB.
    split; [|exact B]. destruct OWN as (Gp & _). lia.
Qed.

(* [comment removed for export] *)
Lemma cmf_sess : forall (fx : FPState) C (A : AS) (m M : word -> option byte) md (s F cm : Z) (cv : cmapv), Cok C -> W C A m md -> (c_top C - LSTK <= s - F)%Z ->
  cm_facts A m cm cv -> (forall x : word, ~ (s - F <= u x < s)%Z -> M x = m x) -> cm_facts A M cm cv.
Proof.
  intros fx C A m M md s F cm cv CK HW Hlo [->|(CM & OK & L1 & L2)] FR; [left; reflexivity | right].
  split; [exact (exT_cmap_sess C A m M md s F cm cv CK HW Hlo L1 CM FR) | split; [exact OK | split; [exact L1 | exact L2]]].
Qed.
Lemma cmf_livk : forall (fx : FPState) (A A' : AS) (m m' : word -> option byte) (cm : Z) (cv : cmapv), cm_facts A m cm cv -> sub_live A A' -> LIVK A m m' -> cm_facts A' m' cm cv.
Proof.
  intros fx A A' m m' cm cv [->|(CM & OK & L1 & L2)] SUB LK; [left; reflexivity | right].
  split; [exact (exT_cmap_livk A m m' cm cv CM LK L1) | split; [exact OK | split; [exact (SUB _ _ L1) | exact (SUB _ _ L2)]]].
Qed.

(* [comment removed for export] *)
Lemma round_live : forall (fx : FPState) C (A0 A1 A2 A3 A4 : AS) m1 m2 pc w h d cdc datac adc kd kna kn r w' h' d' cdr datar adr kd' kna' kn',
  oown C A0 A1 m1 pc w h d cdc datac adc kd kna kn -> (forall q, ~ oblk pc datac cdc adc q -> live A1 q = live A0 q) ->
  oown C A1 A2 m2 r w' h' d' cdr datar adr kd' kna' kn' -> (forall q, ~ oblk r datar cdr adr q -> live A2 q = live A1 q) ->
  (forall q, oblk pc datac cdc adc q -> live A3 q = None) -> (forall q, ~ oblk pc datac cdc adc q -> live A3 q = live A2 q) ->
  (forall q, oblk r datar cdr adr q -> live A4 q = None) -> (forall q, ~ oblk r datar cdr adr q -> live A4 q = live A3 q) ->
  forall q, live A4 q = live A0 q.
Proof.
  intros fx C A0 A1 A2 A3 A4 m1 m2 pc w h d cdc datac adc kd kna kn r w' h' d' cdr datar adr kd' kna' kn' OC LEQ1 OR LEQ2 D3 LEQ3 D4 LEQ4 q.
  pose proof (oown_sub_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ OC LEQ1) as SUB01.
  destruct (oblk_dec r datar cdr adr q) as [BR|NBR].
  - rewrite (D4 q BR). symmetry. pose proof (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OR q BR) as F1.
    destruct (live A0 q) as [k|] eqn:E; [|reflexivity]. rewrite (SUB01 _ _ E) in F1. discriminate F1.
  - rewrite (LEQ4 q NBR). destruct (oblk_dec pc datac cdc adc q) as [BC|NBC].
    + rewrite (D3 q BC). symmetry. exact (oblk_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ OC q BC).
    + rewrite (LEQ3 q NBC), (LEQ2 q NBR). exact (LEQ1 q NBC).
Qed.

End GqIface.
End V15LeptGq_iface.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require MemSplit.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Amb.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymExec2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymRun.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymDrive.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExecFP.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL7a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL9a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptCmap2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptPixCopyA.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptParse.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptThrTail.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptThrLutW.
Module V15LeptThr.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPSteps.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPStepsV.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecW.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecFP.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import V15CL7a.
Import V15CL8a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCreate.
Import V15CL9a.
Import V15CL10a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptCmap2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCopyA.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCopy.
Import V15CL14a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptParse.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptThrTail.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptThrLutW.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecT.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoomPC.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom14.
(* [comment removed for export] *)










Import V15CL7a.V15LeptErr.

Import V15CL8a.V15LeptPixHdr.


Import V15CL9a.V15LeptPixDestroy.

Import V15CL10a.V15LeptCmapValid.


Import V15CL14a.V15LeptDither_iface.


Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Chain.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
(* [comment removed for export] *)
#[local] Existing Instance exf_fxd | 100.

(* [comment removed for export] *)
Definition THR_STACK : Z := 12288.
Definition RK_thr : Z := 10 + RK_pix + RK_rmc.
Definition RB_thr : Z := 10 * 2 ^ 17 + RB_pix14 + RB_rmc.
Definition PC_pixThresholdGrayArb : Z := 119812.
Definition THR_EDGES : Z := 66371.                  (* [comment removed for export] *)

Section Thr.
Hypothesis HRMC : pixRemoveColormap_gray8_contract.
Hypothesis HRC2 : pixDestroy_rc2_contract.

(* [comment removed for export] *)
Theorem pixThresholdGrayArb_W : forall (fx : FPState) C A m md regs (s pixs w h cm data : Z) (cv : cmapv) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + THR_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 284096 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 THR_EDGES -> getr regs 12 = Z_to_bv 64 8 ->
  getr regs 13 = Z_to_bv 64 0 -> getr regs 14 = Z_to_bv 64 0 -> getr regs 15 = Z_to_bv 64 0 ->
  PIXat m pixs (hdv w h 8 cm data) -> hdr_ok w h 8 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None -> live A (Z_to_bv 64 data) = Some (4 * (wpl_of w 8 * h))%Z -> cm_facts A m cm cv ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_thr <= kR)%Z -> (RB_thr <= bR)%Z ->
  (forall (fx' : FPState) A' m' vm' regs', frm_zero (@fp_csr fx') -> W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
      (exists pixd datad cmap cmaparr, getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd w h 8 cmap datad (CMAPV cmaparr 8 256 5 0)) ->
      aroom A' vm' (kR - RK_thr) (bR - RB_thr) ->
      realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 PC_pixThresholdGrayArb) m al_rom) md) S.
Proof.
  intros fx C A m md regs s pixs w h cm data cv ret S FZ CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13 H14 H15 PXs HOK Hw1 Hh1 Lp L0p Ld CMF kR bR RM HkR HbR HC.
  unfold THR_STACK, RK_thr, RB_thr, PC_pixThresholdGrayArb, THR_EDGES in *.
  destruct (exT_pix_entry C A m md pixs _ CK HW Lp PXs) as (Rp & NZp & ALp).
  assert (Rw : (0 <= w < 2 ^ 31)%Z) by (destruct HOK as (_ & X & _); lia). assert (Rh : (0 <= h < 2 ^ 31)%Z) by (destruct HOK as (_ & _ & X & _); lia).
  assert (HkR0 : (0 <= RK_pix + RK_rmc)%Z) by (unfold RK_rmc, RK_pix; lia).
  assert (HbR0 : (0 <= RB_pix14 + RB_rmc)%Z) by (unfold RB_rmc, RB_pix14; lia).
  apply (thr_chain fx C A m md regs s pixs w h S CK HW FZ H2 Hs16 Hlo Hhi H4 H10 H11 H12 H13 H14 H15 Lp Rp NZp ALp Rw Rh
           ltac:(rewrite Z.add_0_r; exact (PIX_rd_w SEGS m pixs _ PXs)) (PIX_rd_h SEGS m pixs _ PXs) (PIX_rd_d SEGS m pixs _ PXs) kR bR RM ltac:(lia) ltac:(lia)).
  intros fx1 A1 m1 vm1 r1 qtab cmap cmaparr FZ1 HW1 SUB1 PM1 RM1 LDEL Lq Fq F0q RRq NEcq Lc Fc F0c RRc Lca Fca F0ca RRca C0 C8 C12 C16 C20 G1 G2 G3 G4 G8 G9 G10 G11 G12
         SV1 SV8 SV9 SV18 SV19 SV20 SV21 SV22 SV23 SV24 SV25 SV26 SV27 LCcmap LCh LCw LCqtab.
  assert (PXs1 : PIXat m1 pixs (hdv w h 8 cm data)) by exact (exT_pix_livk A m m1 pixs _ PXs (proj2 PM1) Lp).
  assert (CMF1 : cm_facts A1 m1 cm cv) by exact (cmf_keep _ A A1 m m1 cm cv CMF SUB1 (proj2 PM1)).
  assert (CMP1 : CMAPat m1 cmap (CMAPV cmaparr 8 256 5 0))
    by exact (exT_cmap_of_cells SEGS C A1 m1 _ cmap cmaparr 8 256 5 0 CK HW1 Lc RRc RRca ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) C0 C8 C12 C16 C20).
  apply (thr_tail_W HRMC HRC2 thr_lut_hop_W fx1 C A A1 m1 _ r1 regs s pixs w h cm data qtab cmap cmaparr cv ret S FZ1 CK HW1 SUB1 Hs16 ltac:(unfold THRT_WIN; lia) Hhi
           G1 G2 G3 G4 G8 G9 G10 G11 G12 SV1 SV8 SV9 SV18 SV19 SV20 SV21 SV22 SV23 SV24 SV25 SV26 SV27 LCcmap LCh LCw LCqtab H1 Hret H2 H4
           PXs1 HOK Hw1 Hh1 (SUB1 _ _ Lp) L0p (SUB1 _ _ Ld) CMF1 Lq Fq F0q RRq Lc Fc F0c Lca Fca F0ca CMP1 NEcq LDEL
           (kR - 10)%Z (bR - 10 * 2 ^ 17)%Z ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(lia) ltac:(lia)).
  intros fx2 A2 m2 vm2 r2 FZ2 HW2 CS2 PM2 RES RM2.
  rewrite with_vmmaps_twice in HW2 |- *.
  apply (HC fx2 A2 m2 vm2 r2 FZ2 HW2 CS2 (POSTM_trans _ _ _ _ _ _ PM1 PM2)).
  - destruct RES as (pixd & datad & G & PN). exists pixd, datad, cmap, cmaparr. split; assumption.
  - replace (kR - (10 + RK_pix + RK_rmc))%Z with (kR - 10 - RK_pix - RK_rmc)%Z by lia.
    replace (bR - (10 * 2 ^ 17 + RB_pix14 + RB_rmc))%Z with (bR - 10 * 2 ^ 17 - RB_pix14 - RB_rmc)%Z by lia. exact RM2.
Qed.
End Thr.
End Chain.
End V15LeptThr.
