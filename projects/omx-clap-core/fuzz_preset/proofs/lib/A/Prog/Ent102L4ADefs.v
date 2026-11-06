(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Ent102L4ADefs.v, with its module paths changed; 250 of its 440 lines of code are new or changed and 311 lines of the source are left out. *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102, PIN sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44): the SUPPORT LEMMAS of segment L4 of
   LLVMFuzzerTestOneInput (entry 0x815e0), +0x1b8 .. +0x2f0, for the segment proof lib/A/Prog/Ent102L4A.v, that the
   shared files do not state. No function is proved here:
   - l4_step_sub: the `sub` step over a listing slot at a generic image ({PA : PAImg A_prog_listing}, the PAListing
     PL_102_A), Ent102L6AfLem.v l6f_step_addi's form over YK14.v step_sub_at;
   - l4_call_x / l4_call_xF: a program call at a concrete callee entry (pc, registers, memory) whose text concludes in
     apost_base_x / apost_base_xF, lib/Reusable/YCbqGcall.v aj_call_x_sp / aj_call_xF_sp with their proof minus the
     symbolic state's st_ok rewrite (the callee's own window is d = 0, so YCbqGcallW.v's window forms do not apply);
   - l4_call_xbF: the same for a BUDGETED callee (its text concludes in YCbqGwild.apost_base_xbF P, the caller's journal
     at any budget WS0, after the call at WS0 ++ WS1 with P WS1): lib/Reusable/YCbqGwild.v aj_call_xbF_sp with its
     proof minus the st_ok rewrite;
   - l4_doc_sh: the shadow facts of the doc's 56 bytes (&doc = fk + 32) from the frame's sixteen shadow bytes
     (Ent102L6Af.v's inline proof at pj_free's call, by path);
   - l4_crcs_evs_doc0 / l4_rej_bridge / l4_supply_rej / l4_idx_crs0: the refused tail's run events at the exact room
     position (the starved check's run premise from the call's run, and cut_crs0's index).
   Everything else this lane uses is cited from lib/A/Prog/Ent102L6AfLem.v (blob a37e0dc13d12) and lib/A/Prog/Ent102CallA.v
   (blob aefcab75548d, with ec_ledger_cells for the ledger's two harness cells), as on the statement line.
   STATEMENT read: lib/A/Ent102CutsA.v (a working branch 83576a163e5b, statements of CUT STABLE 2ab248e3b164:
   ec_frame_shadow, ec_doc, ecx, ec_rej, ec_pn, ec_sc, ec_cno_evs, ec_ranout, ec_trip) and lib/A/Ent102PosA.v
   (ec_supply_run, ec_run_split, ec_call_evs_ranout_false).
   LISTING: lib/A/Listing_prog.v blob 1ab147923c5d (slot k = byte offset 4k from the entry), through the PAListing
   PL_102_A of lib/A/Ent102PLA.v (blob a55fa7414ddf); lib/A/PAImg_prog.v is not loaded, no vm_compute on pa_val /
   pa_sigma.
   The kit TEXTS (the kit of record f97c8b2f046b, names only): lib/A/PRH_Base.v (prh_run_at), lib/A/PRH_FnCheck.v
   (ck_crcs_evs, ck_ncalls).
   rule 24: proves function LLVMFuzzerTestOneInput, segment L4 (reuse search: main / ossv/recipes / ossv/candidates /
   release/pau-projects-recipes + the internal lemma index / proof-index LLVMFuzzerTestOneInput exit=0, checker CONFIRM;
   NEW walk on the #102 pins). This file: support lemmas of that segment only.
   NUMERALS: 56 / 32 / 16 / 10 / 8 / 4 are LENGTHs (struct pj, the doc's offset in the frame and its alignment, the
   frame's shadow bytes, the doc's last shadow byte, the granule, an instruction); 2 ^ 40 is the engine's code span;
   0x7fff8000 is ASan's shadow offset. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PresetReqAt PresetRun PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog Ent102PLA PRH_Base PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnReader PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Ent102CutsA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Ent102PosA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger Ent102L6AfLem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. The `sub` step at a generic image (Ent102L6AfLem.v l6f_step_addi's form). *)
Section S. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {PA : @PAImg rc A_prog_listing}.
#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Notation BASE := (@pa_val rc A_prog_listing PA A_TEXT).

(* over a world relation Rel (YA0nH.SRrG; the free move: segment L4 runs at wle' segs RZ_cf); a COPY beside the plain
   lemma, which keeps its proof *)
Lemma l4_step_subR : forall (Rel : world SEGS -> world SEGS -> Prop) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k w : Z) (rd rs1 rs2 : bv 5) (rd' : bv 5) (v : word),
  0 <= k < 2 ^ 40 ->
  plookup (@pl_tpi _ PL_102_A) k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Op ALU_SUB rd rs1 rs2, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false -> rd = rd' ->
  v_sub (getr regs rs1) (getr regs rs2) = v ->
  (forall X, SRrG SEGS Rel W (mkCfg (@YK11.mkst fx (regupd regs rd' v) (Z_to_bv 64 (BASE + (k + 4))) mem
     (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS Rel W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros Rel W regs mem md Q k w rd rs1 rs2 rd' v Hk Hpl Hd Hrd Erd Hv HK. subst rd'.
pose proof (pa_fetch_pw (PL := PL_102_A) (PI := PA) k w Hpl) as Hf.
eapply (SRrG_step SEGS Rel (@pa_wx rc A_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  exact (step_sub_at (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs1 rs2 v Hf (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hrd Hv).
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)).
  rewrite (l6f_pc4 k Hk). apply HK.
Qed.
Lemma l4_step_sub : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k w : Z) (rd rs1 rs2 : bv 5) (rd' : bv 5) (v : word),
  0 <= k < 2 ^ 40 ->
  plookup (@pl_tpi _ PL_102_A) k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Op ALU_SUB rd rs1 rs2, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false -> rd = rd' ->
  v_sub (getr regs rs1) (getr regs rs2) = v ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx (regupd regs rd' v) (Z_to_bv 64 (BASE + (k + 4))) mem
     (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rd rs1 rs2 rd' v Hk Hpl Hd Hrd Erd Hv HK. subst rd'.
pose proof (pa_fetch_pw (PL := PL_102_A) (PI := PA) k w Hpl) as Hf.
eapply (SRr_step SEGS (@pa_wx rc A_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  exact (step_sub_at (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs1 rs2 v Hf (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hrd Hv).
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)).
  rewrite (l6f_pc4 k Hk). apply HK.
Qed.
End S.

(* ---------------------------------------------------------------------- *)
(* 2. The calls: YCbqGcall.v aj_call_x_sp / aj_call_xF_sp at a concrete callee entry (pc, registers, memory). *)
Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
#[local] Notation AJ := (ajournal_x (SK := SK) segs B PST ARx).
(* THE CALL RULES OVER A WORLD RELATION Rel (transitive; the free move: the lanes after check_no_overread run at
   wle' segs RZ_cf): the caller's journal, the callee's post and the conclusion at Rel (YCbqG.ajournal_xR /
   apost_base_xR / apost_base_xFR, YCbqGwild.ajournal_xwR / apost_base_xbFR), each a COPY beside its plain lemma, which
   keeps its proof. A callee whose text is plain (does not free) is lifted into Rel by l4_lift_* below. *)
#[local] Notation AJR Rel := (ajournal_xR (SK := SK) segs B PST ARx Rel).

Lemma l4_call_xR : forall (Rel : world segs -> world segs -> Prop)
  (Rel_trans : forall W1 W2 W3, Rel W1 W2 -> Rel W2 W3 -> Rel W1 W3)
  (W : world segs) (regsc : bvmap 5 word) memc (pc : Z) STK sp0 FP ly S Hp W0 mem md own
  lyc Sc Hpc mdc k STK1 FP1 (o : Z) raw ch1
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  AJR Rel STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 ->
   SRrG segs Rel W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
     (apost_base_xR (SK := SK) segs B PST ARx Rel STK1 FP1 regsc lyc Sc Hpc W memc mdc Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRrG segs Rel W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (YK11.mkst regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       AJR Rel STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       AJR Rel STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       aregs_preserved regsc regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros Rel Rel_trans W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o raw ch1 Q
  HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRrG_mono.
{ apply Hcallee. eapply (afn_pre_x_atR (SK := SK) segs B PST ARx Rel STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc
    mdc k regsc STK1 o ch1); try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HQ).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. rewrite Hra. split; [reflexivity|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HQ]]].
change own with ([] ++ own).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & _).
eapply (ajournal_x_subR (SK := SK) segs B PST ARx LAWS segs_low Rel Rel_trans);
  [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.
Lemma l4_call_x : forall (W : world segs) (regsc : bvmap 5 word) memc (pc : Z) STK sp0 FP ly S Hp W0 mem md own
  lyc Sc Hpc mdc k STK1 FP1 (o : Z) raw ch1
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 ->
   SRr segs W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
     (apost_base_x (SK := SK) segs B PST ARx STK1 FP1 regsc lyc Sc Hpc W memc mdc Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRr segs W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (YK11.mkst regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       AJ STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       AJ STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       aregs_preserved regsc regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o raw ch1 Q
  HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_x_at (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc
    mdc k regsc STK1 o ch1); try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HQ).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. rewrite Hra. split; [reflexivity|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HQ]]].
change own with ([] ++ own).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & _).
eapply (ajournal_x_sub (SK := SK) segs B PST ARx LAWS segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.

Lemma l4_call_xFR : forall (Rel : world segs -> world segs -> Prop)
  (Rel_trans : forall W1 W2 W3, Rel W1 W2 -> Rel W2 W3 -> Rel W1 W3)
  (W : world segs) (regsc : bvmap 5 word) memc (pc : Z) STK sp0 FP ly S Hp W0 mem md own
  lyc Sc Hpc mdc k STK1 FP1 (o : Z) raw ch1
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  AJR Rel STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 ->
   SRrG segs Rel W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
     (apost_base_xFR (SK := SK) segs B PST ARx Rel STK1 FP1 regsc lyc Sc Hpc W memc mdc Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRrG segs Rel W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
       AJR Rel STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       AJR Rel STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       aregs_preserved regsc regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros Rel Rel_trans W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o raw ch1 Q
  HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRrG_mono.
{ apply Hcallee. eapply (afn_pre_x_atR (SK := SK) segs B PST ARx Rel STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc
    mdc k regsc STK1 o ch1); try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HFZ & HFK & HJ1 & HP & HQ).
exists fx', ly2, S2, Hp2, regs2, mem2, md2, k1. rewrite Hra. split; [reflexivity|].
split; [exact HFZ|]. split; [exact HFK|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HQ]]].
change own with ([] ++ own).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & _).
eapply (ajournal_x_subR (SK := SK) segs B PST ARx LAWS segs_low Rel Rel_trans);
  [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.
Lemma l4_call_xF : forall (W : world segs) (regsc : bvmap 5 word) memc (pc : Z) STK sp0 FP ly S Hp W0 mem md own
  lyc Sc Hpc mdc k STK1 FP1 (o : Z) raw ch1
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 ->
   SRr segs W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
     (apost_base_xF (SK := SK) segs B PST ARx STK1 FP1 regsc lyc Sc Hpc W memc mdc Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRr segs W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
       AJ STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       AJ STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       aregs_preserved regsc regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o raw ch1 Q
  HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_x_at (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc
    mdc k regsc STK1 o ch1); try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HFZ & HFK & HJ1 & HP & HQ).
exists fx', ly2, S2, Hp2, regs2, mem2, md2, k1. rewrite Hra. split; [reflexivity|].
split; [exact HFZ|]. split; [exact HFK|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HQ]]].
change own with ([] ++ own).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & _).
eapply (ajournal_x_sub (SK := SK) segs B PST ARx LAWS segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.

(* the budgeted twin (YCbqGwild.v aj_call_xbF_sp at a concrete callee entry): the caller's journal at any budget WS0 *)
Lemma l4_call_xbFR : forall (Rel : world segs -> world segs -> Prop)
  (Rel_trans : forall W1 W2 W3, Rel W1 W2 -> Rel W2 W3 -> Rel W1 W3)
  (W : world segs) (regsc : bvmap 5 word) memc (pc : Z) STK sp0 FP ly S Hp W0 mem md own
  lyc Sc Hpc mdc k WS0 STK1 FP1 (o : Z) raw ch1 (P : list (list Z) -> Prop)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal_xwR (SK := SK) segs B PST ARx Rel STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS0 ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 ->
   SRrG segs Rel W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
     (YCbqGwild.apost_base_xbFR (SK := SK) segs B PST ARx Rel P STK1 FP1 regsc lyc Sc Hpc W memc mdc Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRrG segs Rel W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
       c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\ P WS1 /\
       ajournal_xwR (SK := SK) segs B PST ARx Rel STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1)
         (WS0 ++ WS1) /\
       ajournal_xwR (SK := SK) segs B PST ARx Rel STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1
         WS1 /\
       aregs_preserved regsc regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros Rel Rel_trans W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 FP1 o raw ch1 P Q
  HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRrG_mono.
{ apply Hcallee. eapply (YCbqGwild.afn_pre_x_at_wR (SK := SK) segs B PST ARx Rel STK sp0 FP ly S Hp W0 mem md own lyc Sc
    Hpc W memc mdc k WS0 regsc STK1 o ch1); try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ & HFK & HPW & HJ1 & HP & HQ).
exists fx', ly2, S2, Hp2, regs2, mem2, md2, k1, WS1. rewrite Hra. split; [reflexivity|].
split; [exact HFZ|]. split; [exact HFK|]. split; [exact HPW|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HQ]]].
change own with ([] ++ own).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & _).
eapply (ajournal_xw_subR (SK := SK) segs B PST ARx LAWS segs_low Rel Rel_trans);
  [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.
Lemma l4_call_xbF : forall (W : world segs) (regsc : bvmap 5 word) memc (pc : Z) STK sp0 FP ly S Hp W0 mem md own
  lyc Sc Hpc mdc k WS0 STK1 FP1 (o : Z) raw ch1 (P : list (list Z) -> Prop)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal_xw (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS0 ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview segs (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  (afn_pre_x segs B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 ->
   SRr segs W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
     (YCbqGwild.apost_base_xbF (SK := SK) segs B PST ARx P STK1 FP1 regsc lyc Sc Hpc W memc mdc Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRr segs W (mkCfg (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
       c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\ P WS1 /\
       ajournal_xw (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1)
         (WS0 ++ WS1) /\
       ajournal_xw (SK := SK) segs B PST ARx STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
       aregs_preserved regsc regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k WS0 STK1 FP1 o raw ch1 P Q
  HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRr_mono.
{ apply Hcallee. eapply (YCbqGwild.afn_pre_x_at_w (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc
    Hpc W memc mdc k WS0 regsc STK1 o ch1); try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ & HFK & HPW & HJ1 & HP & HQ).
exists fx', ly2, S2, Hp2, regs2, mem2, md2, k1, WS1. rewrite Hra. split; [reflexivity|].
split; [exact HFZ|]. split; [exact HFK|]. split; [exact HPW|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HQ]]].
change own with ([] ++ own).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & _).
eapply (ajournal_xw_sub (SK := SK) segs B PST ARx LAWS segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.

(* A CALLEE WHOSE TEXT DOES NOT FREE (the unprimed callee texts): its SRr and its post at wle read at any Rel containing wle
   (YA0nH.SRr_SRrG; YCbqG.apost_base_x_R_lift / apost_base_xF_R_lift; ajournal_xwR_mono for the budgeted form) *)
Lemma l4_lift_x : forall (Rel : world segs -> world segs -> Prop) (Rel_wle : forall W W', wle W W' -> Rel W W')
  (W : world segs) c STK FP regs ly S Hp (W0 : world segs) mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  SRr segs W c (apost_base_x (SK := SK) segs B PST ARx STK FP regs ly S Hp W0 mem md Q) ->
  SRrG segs Rel W c (apost_base_xR (SK := SK) segs B PST ARx Rel STK FP regs ly S Hp W0 mem md Q).
Proof.
intros Rel Rel_wle W c STK FP regs ly S Hp W0 mem md Q H.
eapply SRrG_mono; [exact (SRr_SRrG segs Rel Rel_wle W c _ H)|].
intros W' c' _ HQ. exact (apost_base_x_R_lift segs B PST ARx Rel Rel_wle _ _ _ _ _ _ _ _ _ _ _ _ HQ).
Qed.
Lemma l4_lift_xF : forall (Rel : world segs -> world segs -> Prop) (Rel_wle : forall W W', wle W W' -> Rel W W')
  (W : world segs) c STK FP regs ly S Hp (W0 : world segs) mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  SRr segs W c (apost_base_xF (SK := SK) segs B PST ARx STK FP regs ly S Hp W0 mem md Q) ->
  SRrG segs Rel W c (apost_base_xFR (SK := SK) segs B PST ARx Rel STK FP regs ly S Hp W0 mem md Q).
Proof.
intros Rel Rel_wle W c STK FP regs ly S Hp W0 mem md Q H.
eapply SRrG_mono; [exact (SRr_SRrG segs Rel Rel_wle W c _ H)|].
intros W' c' _ HQ. exact (apost_base_xF_R_lift segs B PST ARx Rel Rel_wle _ _ _ _ _ _ _ _ _ _ _ _ HQ).
Qed.
Lemma l4_lift_xbF : forall (Rel : world segs -> world segs -> Prop) (Rel_wle : forall W W', wle W W' -> Rel W W')
  (W : world segs) c (P : list (list Z) -> Prop) STK FP regs ly S Hp (W0 : world segs) mem md
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  SRr segs W c (YCbqGwild.apost_base_xbF (fx := fx) (SK := SK) segs B PST ARx P STK FP regs ly S Hp W0 mem md Q) ->
  SRrG segs Rel W c (YCbqGwild.apost_base_xbFR (fx := fx) (SK := SK) segs B PST ARx Rel P STK FP regs ly S Hp W0 mem md Q).
Proof.
intros Rel Rel_wle W c P STK FP regs ly S Hp W0 mem md Q H.
eapply SRrG_mono; [exact (SRr_SRrG segs Rel Rel_wle W c _ H)|].
intros W' c' _ (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & Hz & Hk & HP & HJ & Hr & HQ).
exists fx', ly', S', Hp', regs', mem', md', k, WS.
split; [exact Hc|]. split; [exact Hz|]. split; [exact Hk|]. split; [exact HP|].
split; [|split; [exact Hr | exact HQ]].
eapply ajournal_xwR_mono; [exact Rel_wle | exact HJ].
Qed.

Lemma l4_fp_sub_nil : forall STK sp0 FP ly S own lyc Sc, fp_sub_x B STK sp0 FP [] ly S own lyc Sc.
Proof. intros STK sp0 FP ly S own lyc Sc a Ha. destruct (inFP_nil a Ha). Qed.
End C.

(* ---------------------------------------------------------------------- *)
(* 3. The doc's window. *)
Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
Context {PA : @PAImg rc A_prog_listing}.
#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).

(* THE DOC'S WINDOW: &doc = fk + 32, its 56 bytes inside the call's fake frame, their shadow bytes the frame's 4 .. 10 *)
Lemma l4_doc_sh : forall (H : word -> bool) (m : word -> option byte) fk,
  fk mod 32 = 0 -> 0 <= fk ->
  garr8 SEGS (mrestrict H m) (shadow_addr fk) ec_frame_shadow ->
  (forall i, 0 <= i < 16 -> apresent H m (shadow_addr fk + i)) ->
  range_addressable (aview SEGS H m) SHADOW_OFF (ec_doc fk) 56 /\
  shadow_hull_vis (aview SEGS H m) (ec_doc fk) 56.
Proof.
intros H m fk Hal Hfk0 Hshv Hpr.
assert (Hfk8 : fk = 8 * (fk / 8)).
{ pose proof (Z.div_mod fk 8 ltac:(lia)) as D0. pose proof (Z.mod_pos_bound fk 8 ltac:(lia)) as D1.
  pose proof (Z.div_mod fk 32 ltac:(lia)) as D2. lia. }
assert (Esh : shadow_addr fk = SHADOW_OFF + fk / 8) by reflexivity.
unfold ec_doc. split.
- intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
  replace (SHADOW_OFF + x / 8) with (shadow_addr fk + (x / 8 - fk / 8)) by (rewrite Esh; lia).
  apply (l6f_shadow_zero (PA := PA) H m (shadow_addr fk) Hshv).
  pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D2. lia.
- intros s Hs. apply (aview_some_of_apresent SEGS).
  assert (E1 : shadow_addr (fk + 32) = shadow_addr fk + 4).
  { unfold shadow_addr. rewrite Hfk8 at 1. replace (8 * (fk / 8) + 32) with ((fk / 8 + 4) * 8) by lia.
    rewrite Z.div_mul by lia. lia. }
  assert (E2 : shadow_addr (fk + 32 + 56 - 1) = shadow_addr fk + 10).
  { unfold shadow_addr. rewrite Hfk8 at 1. replace (8 * (fk / 8) + 32 + 56 - 1) with ((fk / 8 + 10) * 8 + 7) by lia.
    rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia. }
  rewrite E1, E2 in Hs.
  pose proof (Z.div_mod (shadow_addr fk + 4) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (shadow_addr fk + 4) 8 ltac:(lia)) as D2.
  pose proof (Z.div_mod (shadow_addr fk + 10) 8 ltac:(lia)) as D3.
  pose proof (Z.mod_pos_bound (shadow_addr fk + 10) 8 ltac:(lia)) as D4.
  assert (HS0 : shadow_addr fk = 0x7fff8000 + 4 * (fk / 32)).
  { rewrite Esh. unfold SHADOW_OFF. pose proof (Z.div_mod fk 32 ltac:(lia)) as D5.
    rewrite Hal in D5. lia. }
  replace s with (shadow_addr fk + (s - shadow_addr fk)) by lia.
  apply Hpr. lia.
Qed.
End G.

(* ---------------------------------------------------------------------- *)
(* 4. THE REFUSED TAIL'S RUN EVENTS (the exact room position). check_reject_clean_starved (.., NULL) takes the kit's
      entry premise `prh_run_at sm x os i (ck_crcs_evs sm x took 0 t)`; at doc = 0 its list is the model's starved
      reading `starved_parse sm x took`, and the walk supplies it from the call's run: past check_no_overread's piece
      (no reading ran out), parse_noting's reading and expected()'s scratch, the refused tail (`fst (jr_run sm x []) =
      None`) is exactly ec_rej E (PresetRun.call_rest / call_tail). The BRIDGE: the register took (= the reading's
      calls = ck_ncalls x at jr_strtod) is ec_rej's count when sm is jr_strtod (ec_pre's tie). *)
Section R. Context {rc : YM05.RunCeil} {L : ptable asym} {PA : @PAImg rc L}.
#[local] Notation ECX := (@ecx rc L PA).

(* at doc = 0 the starved check's events do not read the tree *)
Lemma l4_crcs_evs_doc0 : forall sm x took t,
  PRH_FnCheck.ck_crcs_evs sm x took 0 t = PresetReqAt.starved_parse sm x (Z.to_nat took).
Proof. intros sm x took t. unfold PRH_FnCheck.ck_crcs_evs. rewrite Z.eqb_refl, app_nil_r. reflexivity. Qed.

(* THE BRIDGE: the starved check's list at took = the reading's calls is the cut's refused piece ec_rej E *)
Lemma l4_rej_bridge : forall (E : ECX) (n : nat) t,
  e_sm E = ReaderRes.jr_strtod -> Z.of_nat n = PRH_FnCheck.ck_ncalls (e_x E) ->
  PRH_FnCheck.ck_crcs_evs (e_sm E) (e_x E) (Z.of_nat n) 0 t = ec_rej E.
Proof.
intros E n t Hsm Hn. rewrite l4_crcs_evs_doc0, Nat2Z.id. unfold ec_rej. f_equal.
unfold PRH_FnCheck.ck_ncalls, PjGrammar.ncalls in Hn. apply Nat2Z.inj in Hn. rewrite Hn.
unfold PresetReqAt.rtr. rewrite Hsm. reflexivity.
Qed.

(* THE SUPPLY of the refused tail at the caw index, from the call's run (Ent102PosA.ec_supply_run, split by
   ec_run_split after ec_call_evs_ranout_false and the None branch of call_tail) *)
Lemma l4_supply_rej : forall (E : ECX) (trp : ec_trip),
  Z.of_nat (length (e_x E)) <= PresetReqAt.MAXB -> ec_ranout E trp = false ->
  e_i0 E = length (PresetRun.hruns (e_sm E) (e_x E) (e_os E)) ->
  fst (PjGrammar.jr_run (e_sm E) (e_x E) []) = None ->
  prh_run_at (e_sm E) (e_x E) (e_os E ++ [trp]) (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E))
    (ec_rej E).
Proof.
intros E [[o1 o2] o0] Hn Hr Hi Hnone.
pose proof (Ent102PosA.ec_supply_run (e_sm E) (e_x E) (e_os E) o1 o2 o0) as HS.
rewrite <- Hi in HS.
change (PresetRun.call_evs (e_sm E) (e_x E) o1 o2 o0) with (ec_call_evs E (o1, o2, o0)) in HS.
rewrite (Ent102PosA.ec_call_evs_ranout_false rc L PA E (o1, o2, o0) Hn Hr) in HS.
assert (Eq : ec_cno_evs E (o1, o2, o0) ++ PresetRun.call_rest (e_sm E) (e_x E) =
  (ec_cno_evs E (o1, o2, o0) ++ ec_pn E ++ ec_sc E) ++ ec_rej E ++ []).
{ unfold PresetRun.call_rest, PresetRun.call_tail. cbv zeta. rewrite Hnone.
  unfold ec_pn, ec_sc, ec_rej. rewrite app_nil_r, <- !app_assoc. reflexivity. }
rewrite Eq in HS.
exact (Ent102PosA.ec_run_split _ _ _ _ _ _ _ HS).
Qed.

(* the cut's index after the refused tail, from the starved check's advance *)
Lemma l4_idx_crs0 : forall (E : ECX) (trp : ec_trip) (n : nat) t,
  e_sm E = ReaderRes.jr_strtod -> Z.of_nat n = PRH_FnCheck.ck_ncalls (e_x E) ->
  (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E) +
     length (PRH_FnCheck.ck_crcs_evs (e_sm E) (e_x E) (Z.of_nat n) 0 t))%nat =
  (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E ++ ec_rej E))%nat.
Proof.
intros E trp n t Hsm Hn. rewrite (l4_rej_bridge E n t Hsm Hn). rewrite !length_app. lia.
Qed.
End R.
