(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.

(* [comment removed for export] *)
Module SpineMallocU2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "ss_objs"; "ss_next"; "sprop"; "ss_facts"; "ss_lenient"; "swf"; "rw"; "rm"; "agree_below"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "sym_runA"; "ax_X"; "axst"; "la_state"; "@Corelib.Init.Datatypes"; "list"; "nil"; "bool"; "cons"; "true"; "prod"; "app"; "false"; "Some"; "option"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.SpineMallocU1"; "cU1"; "cU0"; "kU1"; "kU2"; "JU"; "cU2"; "perm_okb"; "O_arrF"; "O_pcmZ"; "eU"; "idx1"; "idx2"; "sU1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "nobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "O_st"; "O_pcc0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocR2"; "BASEF"; "BASEO"; "@Stdlib.Lists.List"; "incl"; "In"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "KcA"; "UStopLeOrPc"; "ustop"; "Kc_ok"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI"; "initA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "entryR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocR5"; "posts_conv"; "rho_after"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocS9 PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.RebuildRN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.SpineMallocU1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Section UCHAIN.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list Iface.ulink) (st : ustop) (rho : valuation).
Hypothesis HW : ltac2:(tb__ "0|0|
ScS42Vst;S41A3ScS13S3fA1VW;S14S3fA1A3F_;").
Hypothesis HE : ltac2:(tb__ "0|0|
S4cVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis Hini : aa_cache_inited A = false.
Notation JUp := (JU A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let T : Z := ag_thread (aa_geom A).

Lemma ju_run : ltac2:(tb__ "0|1|
S1dS13S21A1S11S13SeA1M0S15S2S13S3cQ40A1A1S33ScS1cG0A1SfS1eR8R7R6S17A5S1bG0R5A2A3ScS15S7SdR7A1A1S1aA3ScS15S3bPdcS4SdR8A1A1A2S17A3SeS2S3aSeR2RaA3SbS4SdRcA1A1R9R2A3VTR;S23S1eS29VA;VKc;Vrb;Vtp0;Vmd0;RbA6S12R4A1R3R9A5R8A2F_;F_;Fr';FL;VTR;S23S1eS29VA;VKc;Vrb;Vtp0;Vmd0;R8A6RaR7R6A5R5A2F_;F_;F_;F_;FQ;Ftp;Fr;Fs;Fleaves;FE;Fcuts;Ffuel;").
Proof.
  intros fuel cuts E leaves s r tp Q Hrun Hl Hn HL.
  apply (tr_run Kc TR KIT fuel cuts E leaves (JUp s) r tp Q (JU_K A Kc rb tp0 md0 s)); [|exact Hrun | exact Hl | exact HL].
  apply JU_stable; [exact HKc | apply Pos.leb_le; exact Hn].
Qed.

Variable F : nat.
Variable E3 : axst.
Variables LU1 LU2 : leafA.
Variable cellsF : list cell.
Let L1 : axst := la_state LU1.
Let L2 : axst := la_state LU2.
Hypothesis R_u1 : ltac2:(tb__ "0|1|
ScS1cS13SeA1M0A1SfS1eVF;S16S21Z411c4S14S21A1A3S26VE3;A1S17A5S1bG0S16SeVLU1;S14SeA1A3A2A3").
Hypothesis LN_u1 : ltac2:(tb__ "0|0|
ScS15S7SdS26VE3;A1A1A1S1aA3").
Hypothesis NX_u1 : ltac2:(tb__ "0|0|
ScS15S3bPdcS4SdS26VE3;A1A1A1A2S17A3").
Hypothesis PERM1 : ltac2:(tb__ "0|0|
ScS15S2bS32VL1;A1S2fVL1;A1A2S17A3").
Hypothesis OB_s1 : ltac2:(tb__ "0|1|
ScS13S0A1S3SdS31VL1;A1A1A1M0S19S0S20S0S3eS32VL1;A1U2A2G0A3S16S0S36S16S0S2dS14S0A1A3A3A3A3").
Hypothesis SK_k1 : ltac2:(tb__ "0|1|
ScS13S18S18S1S1A2S1A2M0A1S1fS0G0S24S3SdS27VL1;A1A1A1A4S1fS0G0S24S19S0S38VW;A1S16S0S35S14S0A1A3A3A4A3").
Hypothesis XF_k1 : ltac2:(tb__ "0|0|
S39S5S37VW;Vst;A2S6SdS27VL1;A1A1A1A3").
Hypothesis XX_k1 : ltac2:(tb__ "0|1|
ScS13S18S1S1A2M0A1S10S27VL1;A1A1S14G0A1A3").
Hypothesis W_c1 : ltac2:(tb__ "0|0|
ScS15S8SdS25VL1;A1A1A1S17A3").
Hypothesis R_u2 : ltac2:(tb__ "0|1|
ScS1cS13SeA1M0A1SfS1eVF;S16S21Z41260S14S21A1A3S25VL1;A1S17A5S1bG0S16SeVLU2;S14SeA1A3A2A3").
Hypothesis LN_u2 : ltac2:(tb__ "0|0|
ScS15S7SdS25VL1;A1A1A1S1aA3").
Hypothesis NX_u2 : ltac2:(tb__ "0|0|
ScS15S3bPdcS4SdS25VL1;A1A1A1A2S17A3").
Hypothesis OB_u2 : ltac2:(tb__ "0|1|
ScS13S0A1S3SdVL2;A1A1M0S19S0S20S0S3eS32VL2;A1U1A2G0A3S16S0S2cVcellsF;A1S14S0A1A3A3A3").
Hypothesis ARR_ok : arr_okb cellsF = true.
Hypothesis SK_k2 : ltac2:(tb__ "0|1|
ScS13S18S18S1S1A2S1A2M0A1S1fS0G0S24S3SdS28VL2;A1A1A1A4S1fS0G0S24S19S0S38VW;A1S16S0S35S14S0A1A3A3A4A3").
Hypothesis XF_k2 : ltac2:(tb__ "0|0|
S39S5S37VW;Vst;A2S6SdS28VL2;A1A1A1A3").
Hypothesis XX_k2 : ltac2:(tb__ "0|1|
ScS13S18S1S1A2M0A1S10S28VL2;A1A1S14G0A1A3").
Hypothesis W_c2 : ltac2:(tb__ "0|0|
ScS15S8SdS2aVL2;A1A1A1S17A3").
Hypothesis PERM2 : ltac2:(tb__ "0|1|
ScS15S2bS32S2aVL2;A1M0A1S30G0A1A2S17A3").

Lemma u_carve_arr : ltac2:(tb__ "0|1|
S2S13S3cQ40A1A1S34S23S1eS29VA;VKc;Vrb;Vtp0;Vmd0;S1aA6M0S27VL1;A1R3R2R1A6S23S1eG0S25VL1;A1R4R3R2A6F_;Fw;Ftp;Fr;").
Proof.
  intros r tp w Hsp. pose proof Hsp as [HsmA HJ]. destruct HJ as (HFz & _ & _ & HR & _). cbn [umem] in HR.
  destruct (u_nums A rb tp0 md0 W st rho HE) as (C1 & T1 & T2 & TG & TI & PCr). fold T in T1, T2, TI.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  pose proof (vT_val A rb r CF RG) as ET. fold T in ET.
  pose proof HE as (_ & HA & _). destruct (uninit_frame A rb tp0 md0 HA Hini) as (FZ & PRS). fold T in FZ, PRS.
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S (kU1 L1)) [O_st] r _ HW HE HFz Hsm SK_k1 XF_k1) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|os [|? ?]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (RNs : obj_range r os = (T + 2768, T + 3168)).
  { rewrite (obj_range_skel r os O_st SKs). unfold O_st. rewrite obj_range_mk by (clear; lia). rewrite ET. reflexivity. }

  assert (PR : forall z, T + 288 <= z < T + 2768 -> exists b, view segs (rm r) z = Some b).
  { intros z Hz. rewrite (HR z). destruct (Z_lt_dec z (T + 2688)) as [LT|GE]; [|apply PRS; clear -Hz GE; lia].
    exists (Z_to_bv 8 0). apply (FZ ((z - T - 208) / 80) z).
    - pose proof (Z.div_le_mono 80 (z - T - 208) 80 ltac:(clear; lia) ltac:(clear -Hz; lia)) as D1. change (80 / 80) with 1 in D1.
      pose proof (Z.div_lt_upper_bound (z - T - 208) 80 31 ltac:(clear; lia) ltac:(clear -LT; lia)) as D2. clear -D1 D2. lia.
    - pose proof (Z.div_mod (z - T - 208) 80 ltac:(clear; lia)) as DM. pose proof (Z.mod_pos_bound (z - T - 208) 80 ltac:(clear; lia)) as MB. clear -DM MB. lia. }
  assert (ZB : forall c' j, 1 <= c' <= 30 -> (j < 4)%nat -> rd_of segs (rm r) (Z_to_bv 64 (T + (208 + 80 * c') + Z.of_nat j)) = Some (Z_to_bv 8 0)).
  { intros c' j Hc' Hj. pose proof (FZ c' (T + (208 + 80 * c') + Z.of_nat j) Hc' ltac:(clear -Hj; lia)) as Hb. rewrite <- (HR _) in Hb.
    rewrite view_in in Hb by (clear -Hc' Hj T1 T2 TG; lia). exact Hb. }
  apply (SPA_carve_list segs _ r (kU1 L1) tp w NU1 (nxt L1) Hsp W_c1).
  - apply Pos.le_refl.
  - unfold NU1. apply Forall_cons; [|apply Forall_nil].
    rewrite ET. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear -T1; lia|]. split; [clear -T1 T2 TG; lia|].
    split.
    { unfold cells_inside, cnt_spec. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (c' & <- & Hc'). apply In_CLS30 in Hc'. clear -Hc'. lia. }
    split.
    { intros off Hoff. destruct (PR (T + off) ltac:(clear -Hoff; lia)) as [b Hb]. rewrite view_in in Hb by (clear -Hoff T1 T2 TG; lia).
      eapply wok_rd_off_image2; [| |exact Hb]; [clear -Hoff T1 T2 TG; lia | clear -Hoff TI; lia]. }
    split; [|unfold xwords_clear; rewrite XX_k1; intros rr y j []].
    unfold cells_in_view, cnt_spec. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (c' & <- & Hc'). apply In_CLS30 in Hc'.
    intros j Hj. cbn [eval]. rewrite (enc_bytes_zero_nth 4 (Z_to_bv 64 0) j ltac:(apply u64_lit; clear; lia) Hj). exact (ZB c' j Hc' Hj).
  - cbn [map carve_obj NU1]. unfold carved. apply Forall_cons; [|apply Forall_nil]. rewrite obj_range_mk by (clear; lia). rewrite ET.
    rewrite EO. apply Forall_app. split.
    + apply BZ. left. fold T. clear. lia.
    + apply Forall_cons; [|apply Forall_nil]. rewrite RNs. unfold ranges_disjoint; cbn [fst snd]. clear. lia.
  - cbn [map carve_obj NU1 pairwise_disjoint]. split; [apply Forall_nil | exact I].
Qed.

Lemma u_carve_cnt : ltac2:(tb__ "0|1|
S2S13S3cQ40A1A1S34S23S1eS29VA;VKc;Vrb;Vtp0;Vmd0;S17A6M0S28VL2;A1R3R2R1A6S23S1eG0S2aVL2;A1R4R3R2A6F_;Fw;Ftp;Fr;").
Proof.
  intros r tp w Hsp. pose proof Hsp as [HsmA HJ]. destruct HJ as (HFz & _ & _ & HR & _). cbn [umem] in HR. fold T in HR. destruct HR as (_ & L2' & L3).
  destruct (u_nums A rb tp0 md0 W st rho HE) as (C1 & T1 & T2 & TG & TI & PCr). fold T in T1, T2, TI, PCr. fold nv in C1, PCr. fold c in C1, PCr.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  pose proof (vT_val A rb r CF RG) as ET. fold T in ET. pose proof (pc_base_val A rb r CF RG) as EB. rewrite PCr in EB.
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S (kU2 L2)) [O_st] r _ HW HE HFz Hsm SK_k2 XF_k2) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|os [|? ?]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (RNs : obj_range r os = (T + 2768, T + 3168)).
  { rewrite (obj_range_skel r os O_st SKs). unfold O_st. rewrite obj_range_mk by (clear; lia). rewrite ET. reflexivity. }
  destruct (L3 c C1) as (K1 & _ & _).
  apply (SPA_carve_list segs _ r (kU2 L2) tp w NU2 (nxt L2) Hsp W_c2).
  - apply Pos.le_refl.
  - unfold NU2. apply Forall_cons; [|apply Forall_nil].
    rewrite EB. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear -C1 T1; lia|]. split; [clear -C1 T1 T2 TG; lia|].
    split; [repeat apply Forall_cons; try apply Forall_nil; clear; lia|].
    split.
    { intros off Hoff. pose proof (L2' (T + 208 + 80 * c + off) ltac:(unfold ZI, T; clear -Hoff C1; lia)) as D.
      destruct (view segs (rm r) (T + 208 + 80 * c + off)) as [b|] eqn:Eb; [|contradiction]. rewrite view_in in Eb by (clear -Hoff C1 T1 T2 TG; lia).
      eapply wok_rd_off_image2; [| |exact Eb]; [clear -Hoff C1 T1 T2 TG; lia | clear -Hoff C1 TI; lia]. }
    split; [|unfold xwords_clear; rewrite XX_k2; intros rr y j []].
    apply Forall_cons; [|apply Forall_nil]. intros j Hj. cbn [eval]. specialize (K1 j Hj). cbn [c_addr c_w RtCells.c_val] in K1.
    rewrite view_in in K1 by (clear -Hj C1 T1 T2 TG; lia). replace (T + 208 + 80 * c + 0 + Z.of_nat j) with (T + 208 + 80 * c + Z.of_nat j) by (clear; lia). exact K1.
  - cbn [map carve_obj NU2]. unfold carved. apply Forall_cons; [|apply Forall_nil]. rewrite obj_range_mk by (clear; lia). rewrite EB.
    rewrite EO. apply Forall_app. split.
    + apply BZ. left. fold T. clear -C1. lia.
    + apply Forall_cons; [|apply Forall_nil]. rewrite RNs. unfold ranges_disjoint; cbn [fst snd]. clear -C1. lia.
  - cbn [map carve_obj NU2 pairwise_disjoint]. split; [apply Forall_nil | exact I].
Qed.

Theorem uninit_chain : ltac2:(tb__ "0|1|
S2S13S3cQ40A1A1S33S2S44VCST;VXGL;VA;S4bVA;A1M0SaVrb;A1SaR1A1A6VTR;S23S1eS45VW;Vst;G0VKc;S50Vrho;R2A2A5S2eVL2;A1R2R4A5R3A2F_;Fr';VTR;S23S1eS29VA;VKc;Vrb;Vtp0;Vmd0;S1aA6S26VE3;A1R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HC.
  apply (ju_run F [0x411c4] (cU0 E3) [LU1] false r tp Q R_u1 LN_u1 NX_u1). intros L r1 [<-|[]] _. fold L1.

  destruct (perm_okb_sound _ _ PERM1) as (ND1 & LT1 & CV1).
  apply (tr_pre Kc TR KIT (SPA segs (JUp false) (sU1 L1) r1 tp)).
  { intros w Hw. exact (SPA_select segs (JUp false) r1 L1 (idx1 L1) tp w Hw ND1 LT1 CV1). }
  apply (tr_cut Kc TR KIT valuation _ (fun r2 => SPA segs (JUp false) (kU1 L1) r2 tp) Q).
  { intros [tr [ms md]] Hw. exists (rho_absorb r1 [O_pcc0; O_pcmZ] (vms md tp ms)).
    apply (SPA_unobj_J (JUp false) (JUp false) r1 (sU1 L1) _ [O_pcc0; O_pcmZ] tp tr ms md OB_s1 Hw).
    intros Hsm HJ. exact (u_release1 A Kc rb tp0 md0 W st rho HE Hini _ _ r1 tp tr (vms md tp ms) (vmd md) md OB_s1 Hsm HJ). }
  intros r2.

  apply (tr_pre Kc TR KIT (SPA segs (JUp false) (cU1 L1) r2 tp)); [intros w Hw; exact (u_carve_arr r2 tp w Hw)|].
  apply (ju_run F [0x41260] (cU1 L1) [LU2] false r2 tp Q R_u2 LN_u2 NX_u2). intros L r3 [<-|[]] _. fold L2.
  apply (tr_cut Kc TR KIT valuation _ (fun r4 => SPA segs (JUp true) (kU2 L2) r4 tp) Q).
  { intros [tr [ms md]] Hw. exists (rho_absorb r3 [O_arrF cellsF] (vms md tp ms)).
    apply (SPA_unobj_J (JUp false) (JUp true) r3 L2 _ [O_arrF cellsF] tp tr ms md OB_u2 Hw).
    intros Hsm HJ. exact (u_release2 A Kc rb tp0 md0 W st rho HE _ _ cellsF r3 tp tr (vms md tp ms) (vmd md) md OB_u2 ARR_ok Hsm HJ). }
  intros r4.

  apply (tr_pure Kc TR KIT (mem_keptA CST XGL A (initA A) (rm rb) (rm r4))).
  { intros w [_ HJ]. exact (proj2 (u_rebuild CST XGL HCST HXGL A Kc rb tp0 md0 W st rho HE Hini r4 tp _ _ HJ)). }
  intros HMK.
  apply (tr_pre Kc TR KIT (SPA segs (JG W st (initA A) Kc (rho_after rho r4)) (eU L2) r4 tp)); [|exact (HC r4 HMK)].
  intros w Hw. destruct (perm_okb_sound _ _ PERM2) as (ND2 & LT2 & CV2).
  apply (SPA_J (JUp true) (JG W st (initA A) Kc (rho_after rho r4)) (eU L2) r4 tp w).
  { intros HJ. exact (JG_init CST XGL HCST HXGL A Kc rb tp0 md0 W st rho HW HE Hini r4 tp _ _ HJ). }
  exact (SPA_select segs (JUp true) r4 (cU2 L2) (idx2 (cU2 L2)) tp w (u_carve_cnt r4 tp w Hw) ND2 LT2 CV2).
Qed.
End UCHAIN.

Section UTOP.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Variable PFam : ltac2:(tb__ "0|0|
S49S40S13S18S11S48A2A1F_;F_;").
Hypothesis HPF : ltac2:(tb__ "0|0|
S4fVCST;VXGL;VPFam;A3").
Variable nW : nat. Variable st : ustop.
Let W : list Iface.ulink := Wcan nW.
Variable F : nat.
Variable E3 : axst.
Variables LU1 LU2 : leafA.
Variable cellsF : list cell.
Let L1 : axst := la_state LU1.
Let L2 : axst := la_state LU2.
Hypothesis SK3 : ltac2:(tb__ "0|1|
ScS13S18S18S1S1A2S1A2M0A1S1fS0G0S24S3SdVE3;A1A1A4S1fS0G0S24S19S0S38VW;A1S16S0S36S16S0S35S14S0A1A3A3A3A4A3").
Hypothesis XX3 : ax_X E3 = [].
Hypothesis XF3 : ltac2:(tb__ "0|0|
S39S5S37VW;Vst;A2S6SdVE3;A1A1A3").
Hypothesis WU0 : ltac2:(tb__ "0|0|
ScS15S8SdS26VE3;A1A1A1S17A3").
Hypothesis R_u1 : ltac2:(tb__ "0|1|
ScS1cS13SeA1M0A1SfS1eVF;S16S21Z411c4S14S21A1A3S26VE3;A1S17A5S1bG0S16SeVLU1;S14SeA1A3A2A3").
Hypothesis LN_u1 : ltac2:(tb__ "0|0|
ScS15S7SdS26VE3;A1A1A1S1aA3").
Hypothesis NX_u1 : ltac2:(tb__ "0|0|
ScS15S3bPdcS4SdS26VE3;A1A1A1A2S17A3").
Hypothesis PERM1 : ltac2:(tb__ "0|0|
ScS15S2bS32VL1;A1S2fVL1;A1A2S17A3").
Hypothesis OB_s1 : ltac2:(tb__ "0|1|
ScS13S0A1S3SdS31VL1;A1A1A1M0S19S0S20S0S3eS32VL1;A1U2A2G0A3S16S0S36S16S0S2dS14S0A1A3A3A3A3").
Hypothesis SK_k1 : ltac2:(tb__ "0|1|
ScS13S18S18S1S1A2S1A2M0A1S1fS0G0S24S3SdS27VL1;A1A1A1A4S1fS0G0S24S19S0S38VW;A1S16S0S35S14S0A1A3A3A4A3").
Hypothesis XF_k1 : ltac2:(tb__ "0|0|
S39S5S37VW;Vst;A2S6SdS27VL1;A1A1A1A3").
Hypothesis XX_k1 : ltac2:(tb__ "0|1|
ScS13S18S1S1A2M0A1S10S27VL1;A1A1S14G0A1A3").
Hypothesis W_c1 : ltac2:(tb__ "0|0|
ScS15S8SdS25VL1;A1A1A1S17A3").
Hypothesis R_u2 : ltac2:(tb__ "0|1|
ScS1cS13SeA1M0A1SfS1eVF;S16S21Z41260S14S21A1A3S25VL1;A1S17A5S1bG0S16SeVLU2;S14SeA1A3A2A3").
Hypothesis LN_u2 : ltac2:(tb__ "0|0|
ScS15S7SdS25VL1;A1A1A1S1aA3").
Hypothesis NX_u2 : ltac2:(tb__ "0|0|
ScS15S3bPdcS4SdS25VL1;A1A1A1A2S17A3").
Hypothesis OB_u2 : ltac2:(tb__ "0|1|
ScS13S0A1S3SdVL2;A1A1M0S19S0S20S0S3eS32VL2;A1U1A2G0A3S16S0S2cVcellsF;A1S14S0A1A3A3A3").
Hypothesis ARR_ok : arr_okb cellsF = true.
Hypothesis SK_k2 : ltac2:(tb__ "0|1|
ScS13S18S18S1S1A2S1A2M0A1S1fS0G0S24S3SdS28VL2;A1A1A1A4S1fS0G0S24S19S0S38VW;A1S16S0S35S14S0A1A3A3A4A3").
Hypothesis XF_k2 : ltac2:(tb__ "0|0|
S39S5S37VW;Vst;A2S6SdS28VL2;A1A1A1A3").
Hypothesis XX_k2 : ltac2:(tb__ "0|1|
ScS13S18S1S1A2M0A1S10S28VL2;A1A1S14G0A1A3").
Hypothesis W_c2 : ltac2:(tb__ "0|0|
ScS15S8SdS2aVL2;A1A1A1S17A3").
Hypothesis PERM2 : ltac2:(tb__ "0|1|
ScS15S2bS32S2aVL2;A1M0A1S30G0A1A2S17A3").

Theorem refill_uninit : ltac2:(tb__ "0|3|
S49S40S2S13S3cQ40M0A1M1A1S33S33OF_;F_;S4dR4R1A2S43R5A1ScS42Vst;S41A3ScS13S3fA1VW;S14S3fA1A3F_;ScS15S4aR8A1S1aA3ScS21S4eR9S3dG0S9R7PcA2A2A2Z0A3S47S1eS46R8R7VPFam;RaR9A2A5S33S2S2ScS22G1F_;S9R2A1S9RbA1A3RaS23S1eS45VW;Vst;S4bReA1M2RdR3A5S2eVL2;A1R2RbA5S47S1eS46R3RbVPFam;G2RdA2A5A2F_;FrX;Frho1;S2R9S23S1eS45VW;Vst;RdRcRbA5VE3;R1RaA5R3A2FrhoE;F_;TQ;F_;F_;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp TR KIT HKc HW Hini Hcnt Q HCONT rhoE.
  apply (tr_cutP Kc TR KIT Model _ (fun md0 => entryR A rhoE tp md0 W st rho) (fun md0 => SPA segs (JU A Kc rhoE tp md0 false) (cU0 E3) rhoE tp) Q).
  { intros w Hw. exists (cfg_model (w_cfg w)). exact (uninit_entry nW st E3 SK3 XX3 XF3 WU0 A Kc rho rhoE tp w HW Hini Hcnt Hw). }
  intros md0 HE.
  refine (uninit_chain CST XGL HCST HXGL A Kc rhoE tp md0 TR KIT HKc W st rho HW HE Hini F E3 LU1 LU2 cellsF
            R_u1 LN_u1 NX_u1 PERM1 OB_s1 SK_k1 XF_k1 XX_k1 W_c1 R_u2 LN_u2 NX_u2 OB_u2 ARR_ok SK_k2 XF_k2 XX_k2 W_c2 PERM2 rhoE tp Q _).
  intros r' HMK.
  assert (Erm : rm rhoE = rm rho).
  { destruct HE as ((_ & _ & Hm) & _). apply functional_extensionality. intros a. rewrite <- (Hm a). unfold rhoM_of. rewrite rm_rho_sets. reflexivity. }
  rewrite Erm in HMK.
  apply (tr_post Kc TR KIT _ _ _ (fun w Hw => posts_init CST XGL A Kc rho PFam HPF r' tp w HMK Hw)).
  exact (HCONT (rho_after rho r') r' eq_refl).
Qed.
End UTOP.
End SpineMallocU2.

(* [comment removed for export] *)
Module RebuildRQ.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "false"; "length"; "nat"; "@Corelib.Init.Logic"; "eq"; "and"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c8.RebuildRQ"; "phQ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "gh_new"; "phase"; "JR"; "entryR"; "mkPh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.SpineMallocR15"; "phFin"; "phU3"; "phUF3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "mem_keptA"; "ulink"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "class_state"; "cs_free_array"; "cs_mapped_free_array"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineMallocR7"; "popfacts"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "mul"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit PrimCreditLaws Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM RefillModel RefillModelP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildRZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModelP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SpineMallocR6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineMallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineMallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bl.SpineMallocR12 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SpineMallocR13 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.SpineMallocR14 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.SpineMallocR15 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildRZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.RebuildRM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.RebuildR.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition phQ (b : bool) (new k : Z) : phase := ltac2:(tb__ "0|1|
S14U3M0S1S6Lb;Vb;G0U0X1x2Vnew;Vk;S2S2A6").
Lemma phQ_P : ltac2:(tb__ "0|0|
S0S0S7S11S15S16R2R1A3SdS4R2R1A3A3Fk;Fnew;"). Proof. reflexivity. Qed.
Lemma phQ_M : ltac2:(tb__ "0|0|
S0S0S7S11S15S17R2R1A3SdS2R2R1A3A3Fk;Fnew;"). Proof. reflexivity. Qed.

Section RQ.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.

Theorem refill_rebuild_Q : ltac2:(tb__ "0|3|
S1eS19SaS3S2cQ40M0A1A1M1SeS3S1bA1S1cSaS13R8R6R5R4R3R2R1A7S27R9R7A2S1S7S1S1fRbA1S2A3S2dG0ScRaPcA2A2S0S25R1A1S0S26ReR2A2S20S9S7S1R5S2A3S29S22R1A1S2aZ4S28S2bS5S0S21R1A1A2A1S10RfRdA2A2A2A2A2SaG1S3SfA1SeS12R14R13R12R11R10SdRaS10R14R12A2S23R7A1A3R4R3R2R1AaS8S1dS18S24R15R8A2M2R5R4R2A5S1aVCST;VXGL;R15G2SbR13A1SbR5A1A6A2F_;Fmd;Ftr;Ftp;Fr;F_;Tcs;Tc;Tnv;F_;Fb;FPF;FHE;Frho;Fst;FW;Fmd0;Ftp0;Frb;FKc;FA;").
Proof.
  intros A Kc rb tp0 md0 W st rho HE PF b Hini nv c cs HB r tp tr md (HFz & HGh & HK & HM & HR & HRM).
  destruct (pop_geo A rb tp0 md0 W st rho HE PF) as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & G13 & G14 & FAr & T1 & PS1 & TB).
  fold nv c cs in C1, S1, AU0, MU1, N4, K1, KN, NF0, MF1, MF2, MF0, FAr.
  destruct (entry_pure A rb tp0 md0 W st rho HE PF) as (HP & Hc0 & NP & RM). fold nv c cs in HP, Hc0, NP, RM.
  pose proof (P_csR A rb tp0 md0 W st rho HE PF) as (X1 & X2 & X3 & X5 & X6 & X7 & LP' & HIDS). cbn zeta in X1, X2, X3, X5, X6, X7, LP', HIDS. fold nv c cs in X1, X2, X3, X5, X6, X7, LP', HIDS.
  pose proof (P_fields c cs _ C1 HP NP RM) as PFL. cbn zeta in PFL. destruct PFL as (_ & _ & _ & XFA & _). pose proof (P_newZ A rb) as ENZ. fold nv c cs in ENZ. pose proof (P_faP_len c cs _ C1 HP RM) as LPz. rewrite ENZ in LPz. rewrite LPz in XFA.
  destruct (refill_pure c cs _ C1 HP Hc0 ltac:(intros _; exact RM)) as (HPR & _). cbn zeta in HPR.
  pose proof (pop_credit_eq A rb tp0 md0 W st rho HE PF) as CEQ. fold nv c cs in CEQ.
  set (k := kchunks c) in *. set (new := gh_new A rb) in *. set (nf := Z.of_nat (length (cs_free_array cs))) in *.
  set (mu := cs_mapped_user cs) in *. set (mfa := cs_mapped_free_array cs) in *. set (au := cs_allocated_user cs) in *. set (fP := faP c cs) in *.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *. set (T := ag_thread G) in *.
  assert (Eb : (mfa <? 4 * (nf + new)) = b).
  { destruct b; [apply Z.ltb_lt; apply (proj1 HB); reflexivity | apply Z.ltb_ge; destruct (Z_lt_dec mfa (4 * (nf + new))) as [X|X]; [discriminate (proj2 HB X) | clear -X; lia]]. }
  rewrite Eb in X7, CEQ.
  pose proof HE as (_ & HA & _ & _ & _ & Hnv & _ & _ & HWF). fold nv in Hnv.
  pose proof HA as (HG & _ & _ & HRest0 & HMI0 & HI3 & HB0). destruct HRest0 as (_ & _ & (PL & _) & _).

  assert (EU0 : U0 A rb = SB + c * 4294967296 + mu) by (unfold U0, region_beg, kRegionSize; fold nv c cs; fold G SB mu; clear; lia).
  assert (EF0 : F0 A rb = SB + c * 4294967296 + 3758096384 + mfa) by (unfold F0, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; fold nv c cs; fold G SB mfa; clear; lia).
  assert (PCr : PCE A rb = T + 208 + 80 * c) by (unfold PCE; fold nv c; fold G T; clear; lia).
  assert (G12 : SB mod 65536 = 0).
  { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. destruct CF as (_ & _ & _ & _ & _ & (X & _) & _). exact X. }
  assert (MU18 : mu mod 262144 = 0).
  { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF. destruct CF as (_ & _ & (X & _) & _). exact X. }
  assert (UM : U0 A rb mod 65536 = 0).
  { rewrite EU0. destruct (proj1 (Z.mod_divide mu 262144 ltac:(clear; lia)) MU18) as [q Hq]. destruct (proj1 (Z.mod_divide SB 65536 ltac:(clear; lia)) G12) as [q2 Hq2].
    rewrite Hq, Hq2. replace (q2 * 65536 + c * 4294967296 + q * 262144) with ((q2 + c * 65536 + q * 4) * 65536) by (clear; lia). apply Z_mod_mult. }
  assert (FM : F0 A rb mod 65536 = 0).
  { rewrite EF0. destruct (proj1 (Z.mod_divide mfa 262144 ltac:(clear; lia)) MF0) as [q Hq]. destruct (proj1 (Z.mod_divide SB 65536 ltac:(clear; lia)) G12) as [q2 Hq2].
    rewrite Hq, Hq2. replace (q2 * 65536 + c * 4294967296 + 3758096384 + q * 262144) with ((q2 + c * 65536 + 57344 + q * 4) * 65536) by (clear; lia). apply Z_mod_mult. }
  destruct (sh_run_nums SB (U0 A rb) ltac:(clear -G13; lia) ltac:(rewrite EU0; clear -C1 AU0; lia) ltac:(rewrite EU0; clear -C1 MU1; lia) G14 UM) as (QU1 & QU2 & QU3 & QU4).
  destruct (sh_run_nums SB (F0 A rb) ltac:(clear -G13; lia) ltac:(rewrite EF0; clear -C1 NF0 MF1; lia) ltac:(rewrite EF0; clear -C1 MF2; lia) G14 FM) as (QF1 & QF2 & QF3 & QF4).
  set (ri := region_info SB c) in *.
  assert (RIr : SB + 137438953472 + 128 <= ri /\ ri + 128 <= SB + 137438953472 + 4096).
  { unfold ri, region_info, kRegionInfoStride. rewrite kSpaceSize_val. clear -C1. lia. }

  set (ZQ := fun z : Z => (Sh (U0 A rb) <= z < Sh (U0 A rb) + 32768) \/ (U0 A rb <= z < U0 A rb + 262144)
                          \/ (b = true /\ Sh (F0 A rb) <= z < Sh (F0 A rb) + 32768) \/ (b = true /\ F0 A rb <= z < F0 A rb + 262144)
                          \/ (FAb A rb + 4 * nf <= z < FAb A rb + 4 * (nf + new))
                          \/ (PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k) \/ (PCE A rb <= z < PCE A rb + 4) \/ (ri <= z < ri + 128)).
  assert (ZI : forall z, zoneR A rb (phQ b new k) z <-> ZQ z).
  { intros z. unfold zoneR, phQ, ZQ, revealedp, releasedp, kUserMapSize, kFreeArrayMapSize. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri Nat.leb].
    unfold gh_nf. fold nv c cs nf new. fold G SB ri. replace (nf + new - new) with nf by (clear; lia).
    destruct b; cbn [Nat.leb]; split.
    - intros [[_ H]|[[_ H]|[[_ H]|[[_ H]|[[H _]|[H|[[_ H]|[_ H]]]]]]]].
      + left; exact H.
      + right; left; exact H.
      + right; right; left; split; [reflexivity | exact H].
      + right; right; right; left; split; [reflexivity | exact H].
      + right; right; right; right; left; exact H.
      + right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; right; exact H.
    - intros [H|[H|[[_ H]|[[_ H]|[H|[H|[H|H]]]]]]].
      + left; split; [reflexivity | exact H].
      + right; left; split; [reflexivity | exact H].
      + right; right; left; split; [reflexivity | exact H].
      + right; right; right; left; split; [reflexivity | exact H].
      + right; right; right; right; left; split; [exact H | clear -N4; lia].
      + right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; left; split; [reflexivity | exact H].
      + right; right; right; right; right; right; right; split; [reflexivity | exact H].
    - intros [[_ H]|[[_ H]|[[X _]|[[X _]|[[H _]|[H|[[_ H]|[_ H]]]]]]]]; try discriminate X.
      + left; exact H.
      + right; left; exact H.
      + right; right; right; right; left; exact H.
      + right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; right; exact H.
    - intros [H|[H|[[X _]|[[X _]|[H|[H|[H|H]]]]]]]; try discriminate X.
      + left; split; [reflexivity | exact H].
      + right; left; split; [reflexivity | exact H].
      + right; right; right; right; left; split; [exact H | clear -N4; lia].
      + right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; left; split; [reflexivity | exact H].
      + right; right; right; right; right; right; right; split; [reflexivity | exact H]. }
  assert (ZD : forall z, zoneR A rb (phQ b new k) z \/ ~ zoneR A rb (phQ b new k) z).
  { intros z. assert (D : ZQ z \/ ~ ZQ z).
    { unfold ZQ. destruct b.
      - assert (D' : (Sh (U0 A rb) <= z < Sh (U0 A rb) + 32768 \/ U0 A rb <= z < U0 A rb + 262144 \/ Sh (F0 A rb) <= z < Sh (F0 A rb) + 32768 \/ F0 A rb <= z < F0 A rb + 262144
                        \/ FAb A rb + 4 * nf <= z < FAb A rb + 4 * (nf + new) \/ PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)
                       \/ ~ (Sh (U0 A rb) <= z < Sh (U0 A rb) + 32768 \/ U0 A rb <= z < U0 A rb + 262144 \/ Sh (F0 A rb) <= z < Sh (F0 A rb) + 32768 \/ F0 A rb <= z < F0 A rb + 262144
                        \/ FAb A rb + 4 * nf <= z < FAb A rb + 4 * (nf + new) \/ PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)) by (clear; lia).
        destruct D' as [D'|D']; [left | right]; [clear -D'; tauto | intros X; apply D'; clear -X; tauto].
      - assert (D' : (Sh (U0 A rb) <= z < Sh (U0 A rb) + 32768 \/ U0 A rb <= z < U0 A rb + 262144
                        \/ FAb A rb + 4 * nf <= z < FAb A rb + 4 * (nf + new) \/ PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)
                       \/ ~ (Sh (U0 A rb) <= z < Sh (U0 A rb) + 32768 \/ U0 A rb <= z < U0 A rb + 262144
                        \/ FAb A rb + 4 * nf <= z < FAb A rb + 4 * (nf + new) \/ PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)) by (clear; lia).
        destruct D' as [D'|D']; [left; clear -D'; tauto|]. right. intros X. apply D'. clear -X. destruct X as [X|[X|[[E _]|[[E _]|X]]]]; try discriminate E; tauto. }
    destruct D as [D|D]; [left; apply ZI; exact D | right; intros X; apply D; apply ZI; exact X]. }
  unfold rlink in HR. destruct HR as (L1 & L2 & L3 & L4 & L5 & L6).
  set (m0 := view segs (rm rb)) in *. set (m := view segs (rm r)) in *.

  unfold mlink in HM. cbn zeta in HM. unfold phQ in HM. cbn [ph_u ph_f] in HM.
  destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & M9 & M10).
  assert (ECF : committed (if b then 3%nat else 0%nat) = b) by (destruct b; reflexivity).
  assert (ERF : revealedp (if b then 3%nat else 0%nat) = b) by (destruct b; reflexivity).
  rewrite ECF in M5, M6, M10. rewrite ERF in M8, M9, M10. change (committed 3) with true in M5, M6, M10. change (revealedp 3) with true in M8, M9, M10.
  apply (refill_rebuild CST XGL HCST HXGL A rb r tp0 tp md0 md nv (zoneR A rb (phQ b new k)) HA Hnv Hini); fold c cs; fold G; fold SB T; fold nf mu.
  - exact HPR.
  - rewrite X5. fold au. clear -N4 S1. nia.
  - rewrite X6. clear; lia.
  - rewrite X7. fold mfa. destruct b; clear; lia.
  - rewrite X2. destruct (kchunks_facts c C1) as (_ & K2 & _). fold k in K2. clear -K1 K2. lia.
  - exact ZD.
  -
    intros z HZ. apply ZI in HZ. unfold envR. unfold ZQ in HZ. rewrite EU0, EF0, FAr, PCr in HZ. rewrite EU0 in QU3, QU4. rewrite EF0 in QF3, QF4.
    pose proof (Geometry.Sh_mono (SB + c * 4294967296 + mu) (SB + c * 4294967296 + 3758096384 + mfa) ltac:(clear -MU1 NF0 MF1; lia)) as SM1.
    pose proof (Geometry.Sh_mono (SB + c * 4294967296 + mu + 262144) (SB + c * 2 ^ 32 + 2 ^ 32) ltac:(clear -MU1; lia)) as SM2.
    pose proof (Geometry.Sh_mono (SB + c * 4294967296 + 3758096384 + mfa + 262144) (SB + c * 2 ^ 32 + 2 ^ 32) ltac:(clear -MF2; lia)) as SM3.
    replace (SB + c * 2 ^ 32 + mu) with (SB + c * 4294967296 + mu) by (clear; lia).
    destruct HZ as [X|[X|[[_ X]|[[_ X]|[X|[X|[X|X]]]]]]].
    + right; right; right; right; right. clear -X QU4 SM2. lia.
    + right; right; right; right; left. clear -X MU1. lia.
    + right; right; right; right; right. clear -X QF4 SM1 SM3. lia.
    + right; right; right; left. clear -X MF1 MF2. lia.
    + right; right; right; left. clear -X N4 MF1 MF2. lia.
    + right; right; left. clear -X K1. lia.
    + right; left. clear -X. lia.
    + left. unfold ri, region_info, kRegionInfoStride in X. rewrite kSpaceSize_val in X. clear -X. lia.
  - intros z Hz. exact (L1 z Hz).
  - intros z Hz. pose proof (L2 z Hz) as D. change (exists b0, m z = Some b0). destruct (m z) as [b0|]; [exists b0; reflexivity | contradiction].
  - exact HRM.
  - exact (proj1 (L6 eq_refl)).
  - exact (proj1 (proj2 (L6 eq_refl))).
  - exact (proj1 (proj2 (proj2 (L6 eq_refl)))).
  - exact (proj1 (proj2 (proj2 (proj2 (L6 eq_refl))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl)))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl))))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl)))))))).
  - exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl)))))))).
  -
    rewrite XFA. intros i x Hi. pose proof (nth_error_Some_lt _ _ _ Hi) as Li. rewrite firstn_length_le in Li by (clear -LP' KN NF0 K1; lia).
    rewrite nth_error_firstn in Hi. replace (i <? Z.to_nat (nf + new - k))%nat with true in Hi by (symmetry; apply Nat.ltb_lt; exact Li).
    pose proof (P_HSRC A rb tp0 md0 W st rho HE PF (phQ b new k) m eq_refl ltac:(cbn [ph_pop phQ]; clear -K1; lia) (conj L1 (conj L2 (conj L3 (conj L4 (conj L5 L6))))) (Z.of_nat i)
                  ltac:(fold nv c cs fP; rewrite LP'; clear -Li KN NF0 K1; lia)) as CE.
    fold nv c cs fP in CE. rewrite Nat2Z.id in CE. rewrite (nth_error_nth _ _ 0 Hi) in CE.
    replace (free_array SB c) with (FAb A rb) by (unfold FAb; fold nv c; reflexivity). exact CE.
  - rewrite X2. replace (T + 208 + 80 * c) with (PCE A rb) by (rewrite PCr; reflexivity). exact (L5 eq_refl).
  - intros i x Hi. pose proof (nth_error_Some_lt _ _ _ Hi) as Li. rewrite <- (Nat2Z.id (length (cs_cache (refill_cs c cs)))) in Li. rewrite X2 in Li.
    pose proof (L4 (Z.of_nat i)) as CE. cbn [ph_pop phQ] in CE. specialize (CE ltac:(clear -Li K1; lia)).
    rewrite Nat2Z.id in CE. fold nv c cs in CE. rewrite (nth_error_nth _ _ 0 Hi) in CE.
    replace (T + 208 + 80 * c + 16 + 4 * Z.of_nat i) with (PCE A rb + 16 + 4 * Z.of_nat i) by (rewrite PCr; reflexivity). exact CE.
  - rewrite X6. intros z Hz. apply ZI. right; left. rewrite EU0. unfold region_beg, kRegionSize in Hz. clear -Hz. lia.
  - rewrite X6. intros z Hz. apply ZI. left. rewrite EU0 in QU4 |- *. unfold region_beg, kRegionSize in Hz.
    replace (SB + c * 2 ^ 32 + mu) with (SB + c * 4294967296 + mu) in Hz by (clear; lia).
    replace (SB + c * 2 ^ 32 + (mu + 262144)) with (SB + c * 4294967296 + mu + 262144) in Hz by (clear; lia). clear -Hz QU4. lia.
  - rewrite X7. fold mfa. intros z Hz. destruct b; [|exfalso; clear -Hz; lia]. apply ZI. right; right; right; left. split; [reflexivity|].
    rewrite EF0. unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in Hz. clear -Hz. lia.
  -
    change (subF A rb b (subU A rb true (vm_noaccess (m_vmmaps md0))))
      with (sub2 true (U0 A rb) (U0 A rb + kUserMapSize) b (F0 A rb) (F0 A rb + kFreeArrayMapSize) (vm_noaccess (m_vmmaps md0))) in M5.
    change (subF A rb b (subU A rb true (m_vm_lazy md0)))
      with (sub2 true (U0 A rb) (U0 A rb + kUserMapSize) b (F0 A rb) (F0 A rb + kFreeArrayMapSize) (m_vm_lazy md0)) in M6.
    rewrite M7.
    apply (model_inv_sub2 A (refillA A c) tp0 tp1 md0 md true b (U0 A rb) (U0 A rb + kUserMapSize) (F0 A rb) (F0 A rb + kFreeArrayMapSize)); try reflexivity; try assumption.
    + unfold kUserMapSize. clear; lia.
    + unfold kFreeArrayMapSize. clear; lia.
    + fold G SB. rewrite EU0. clear -C1 AU0. lia.
    + fold G SB. rewrite EU0, kSpaceSize_val. unfold kUserMapSize. clear -C1 MU1. lia.
    + fold G SB. rewrite EF0. clear -C1 NF0 MF1. lia.
    + fold G SB. rewrite EF0, kSpaceSize_val. unfold kFreeArrayMapSize. clear -C1 MF2. lia.
    + fold G SB. unfold HIGH_SHADOW_END. clear -G13. lia.
    + intros p Hp. destruct (M8 p Hp) as [_ [[_ (j & Hj & Ej)]|[_ (j & Hj & Ej)]]]; rewrite Ej; unfold band_page; right; unfold HIGH_SHADOW_BEG, HIGH_SHADOW_END, PG.
      * clear -Hj QU2 QU3. lia.
      * clear -Hj QF2 QF3. lia.
    +
      destruct HMI0 as (_ & PB0 & _). rewrite <- M7. unfold kUserMapSize, kFreeArrayMapSize in M10.
      destruct b; clear -PB0 M10 CEQ; lia.
  -
    rewrite M7. apply (bandtp_grow m tp0).
    + eapply bandtp_mono; [|exact HB0]. intros z _ Hd. fold m0 in Hd. destruct (ZD z) as [ZIz|ZOz]; [exact (L2 z ZIz) | rewrite (L1 z ZOz); exact Hd].
    + intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [|left; exact Hp]. right. intros _ z Hz.
      assert (ZIz : zoneR A rb (phQ b new k) z).
      { apply ZI. destruct (M8 p Hp) as [_ [[_ (j & Hj & Ej)]|[Eb' (j & Hj & Ej)]]]; rewrite Ej in Hz; unfold PG in Hz.
        - left. clear -Hz Hj. lia.
        - right; right; left. split; [exact Eb' | clear -Hz Hj; lia]. }
      pose proof (L2 z ZIz) as D. destruct (m z) as [b0|]; [exists b0; reflexivity | contradiction].
Qed.
End RQ.
End RebuildRQ.

(* [comment removed for export] *)
Module SpineCallocSecE4.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "DG"; "aa_sec"; "sec_chunk"; "aa_Km"; "aa_geom"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@Corelib.Init.Datatypes"; "list"; "prod"; "pair"; "None"; "length"; "option"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "mem_keptA"; "@Corelib.Init.Logic"; "eq"; "not"; "and"; "False"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "div"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf"; "dblocks"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3"; "clsP"; "JGs"; "JGsC"; "slink"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4"; "slink4"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require q0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.MmapSymA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bx.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SecRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c4.CSecLinks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.SpineCallocSecOK.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CallocBase2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section OKE.
Variable nW : nat. Variable st : ustop. Variable nx : positive. Variable hi : bool.
Let W : list ulink := Wcan nW.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Hypothesis HCSTS : ltac2:(tb__ "0|0|
SeS3bVCST;R1A2S3bS3eR2A2S24F_;F_;Fa;").
Hypothesis HCSTD : ltac2:(tb__ "0|0|
SeS3bVCST;R1A2S22S2fR2A1A1F_;Fa;").
Let JGs : ltac2:(tb__ "0|0|
S5S5F_;S5S1eS1ScQ40A1S13Fa;Frho;FKc;FA;FAX;") := ltac2:(tb__ "0|0|
S31VnW;Vst;Vnx;A3").
Let JGsC : ltac2:(tb__ "0|0|
S5S5F_;S5S1eS1ScQ40A1S13Fa;Frho;FKc;FA;FAX;") := ltac2:(tb__ "0|0|
S32VnW;Vst;Vnx;A3").
Let Posts (A : AA) (Kc : KcA) : ltac2:(tb__ "0|0|
S14S15S3cS37A2A1") := ltac2:(tb__ "0|0|
S3dVCST;VXGL;VW;Vst;VA;VKc;A6").
Variables (E1 D2 T4a T4b C5a C5b : axst).

Hypothesis EG12 : ltac2:(tb__ "0|5|
S5S1eS1ScQ40M0A1M1S14G1A1M2S11OF_;S1dVW;Vst;A2S1fR6A1S30Vhi;SbG0R5A2S1cSbG0S2R6PcM3A2A2A1A3S1S1G2S33SbG0R9A2S1cSbG0S2RaG3A2A2A1RaR3A4S10S0S12S0VJGs;S5R1LX;M4RdRcR4RaA5VD2;R3R2A5R8A3F_;FtpY;FrhoY;Frho';S1S10S0S12S0VJGsC;G4RbRaR9R8A5VE1;R1R7A5R6A3FrhoX;F_;F_;F_;F_;FQ;Ftp;Fa;Frho;FKc;FA;").
Hypothesis EG3 : ltac2:(tb__ "0|7|
S5S1eS1ScQ40M0A1M1S11OF_;S1dVW;Vst;A2S1fR5A1S27S26S29S18S8S7R7A1A2A1Z1A2S2aZ2Z14A2A2SeS23S25S3aSbG0R6A2A1M2R1A2S27R1S26G2S28S1cSbG0S2R7PcM3A2A2A1Z8A2A2A2A2S22S21S19ScQ8A1M4A1S3R8SdG0R2A2A2S17G4A1A3A1F_;Fz;S1S1S14G1A1M5S3fSaRcA1SbG0R9A2S1cSbG0S2RaG3A2A2A1RaR3A5S10S0S12S0VJGs;S5S38R1A1LX;RdRcR4RaA5VT4a;R3R2A5R9A3F_;FtY;FrY;Frho'';S1G5S10S0S12S0VJGs;S5R1LX;M6RcRbRaR9A5VT4b;R2R1A5R8A3FtY;FrY;S1G5S10S0S12S0VJGs;G6RdRcRbRaA5VD2;R2R1A5R9A3FtX;FrX;F_;F_;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Hypothesis EG41a : ltac2:(tb__ "0|5|
S5S1eS1ScQ40M0A1M1S11OF_;S39VW;Vst;A2S1dVW;Vst;A2S1fR6A1S6S1S1S14G1A1M2S15SeSeA2M3S34G3R1S2eR5A1A3S2dR2S16SeSeSbG0RbA2S1cSbG0S2RcPcA2A2A1A4A2F_;Fbn;S2cR5RbR4A3S10S0S12S0VJGs;S2bS5S38R1A1LX;M4R6A2ReRdR5RbA5VC5a;R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S1G2S10S0S12S0VJGs;G4RbRaR9R8A5VT4a;R2R1A5R7A3FtX;FrX;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Hypothesis EG41b : ltac2:(tb__ "0|5|
S5S1eS1ScQ40M0A1M1S11OF_;S39VW;Vst;A2S1dVW;Vst;A2S1fR6A1S6S1S1S14G1A1M2S15SeSeA2M3S34G3R1S2eR5A1A3S2dR2S16SeSeSbG0RbA2S1cSbG0S2RcPcA2A2A1A4A2F_;Fbn;S2cR5RbR4A3S10S0S12S0VJGs;S2bS5R1LX;M4R6A2ReRdR5RbA5VC5b;R4R3A5RaA3F_;F_;Ftp';FrhoX;Frho';FG2;S1G2S10S0S12S0VJGs;G4RbRaR9R8A5VT4b;R2R1A5R7A3FtX;FrX;F_;F_;F_;F_;FQ;Fa;Frho;FKc;FA;").
Hypothesis ETLa : ltac2:(tb__ "0|8|
S5S1eS1S1ScQ40M0A1M1S14G1A1M2S6S1dVW;Vst;A2S1fR7A1SfS21G1S2R7R1A2S2R8R1A2A3Fi;SfS21S14ScQ8A1M3A1S4R8R1A2S4R9R1A2A3Fl;S20VCST;VXGL;RbRbS3R9A1S3R8A1A6S25S29S18S8S7RcA1A2A1S9RcA1A2S15SeSeA2M4S34G4R1S2eR8A1A3S2dR2S16SeSeSbG0RbA2M5S1cSbG0S2RcPcA2A2A1M6A4A2F_;Fbn;SeS23S25S3aG5A1M7R1A2S27R1S26G7S28G6Z8A2A2A2A2S22S21S19G3A1S3RdSdG0R2A2A2S17G3A1A3A1F_;Fz;S1G2S10S0S12S0VJGs;S2bS5S38R1A1LX;RbA2R11R10ReRdA5VC5a;R2R1A5S36S0S35RfRcVPosts;R11R10A2A5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").
Hypothesis ETLb : ltac2:(tb__ "0|8|
S5S1eS1S1ScQ40M0A1M1S14G1A1M2S6S1dVW;Vst;A2S1fR7A1SfS21G1S2R7R1A2S2R8R1A2A3Fi;SfS21S14ScQ8A1M3A1S4R8R1A2S4R9R1A2A3Fl;S20VCST;VXGL;RbRbS3R9A1S3R8A1A6S25S29S18S8S7RcA1A2A1S9RcA1A2S15SeSeA2M4S34G4R1S2eR8A1A3S2dR2S16SeSeSbG0RbA2M5S1cSbG0S2RcPcA2A2A1M6A4A2F_;Fbn;SeS23S25S3aG5A1M7R1A2S27R1S26G7S28G6Z8A2A2A2A2S22S21S19G3A1S3RdSdG0R2A2A2S17G3A1A3A1F_;Fz;S1G2S10S0S12S0VJGs;S2bS5R1LX;RbA2R11R10ReRdA5VC5b;R2R1A5S36S0S35RfRcVPosts;R11R10A2A5A3FtX;FrX;F_;F_;F_;F_;F_;F_;F_;F_;FG2;Ftp0;Fa;Frho;Frho0;FKc;FA;").

Theorem esec_ok_chain : ltac2:(tb__ "0|2|
S5S1eS1ScQ40M0A1M1S14G1A1S39VW;Vst;A2S1dVW;Vst;A2S1fR6A1S30Vhi;SbG0R5A2S1cSbG0S2R6PcA2A2A1A3S1S10S0S12S0VJGsC;S5R1LX;RaR9R8R7A5VE1;R1R6A5S36S0S35R8R6VPosts;RaR9A2A5A3FrhoX;F_;F_;F_;F_;Ftp;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a tp HW HUS HKc HC rhoX.
  set (ua := bv_unsigned a) in *. set (L := secmapsize (bv_unsigned (rw rho 12%positive))) in *.
  apply (EG12 A Kc rho a tp _ HUS HKc HC). intros rho1 rhoY tpY SL1.
  apply (etriple_pre_pure segsA _ _ (Z.of_nat (length (aa_sec A)) + 1 < 2 ^ 20 /\ Z.of_nat (length (aa_sec A)) <= aa_Km A)).
  { intros [tr [ms md]] Hw. exact (d2_pure nW st nx A Kc rho1 a rhoY tpY tr md (proj2 Hw)). }
  intros [HRM HL9].
  assert (E1r : rw rho1 12%positive = rw rho 12%positive) by (destruct SL1 as (W1 & _); apply W1).
  assert (RD1 : forall z, Sh ua <= z < Sh ua + L / 8 -> rm rho1 (Z_to_bv 64 z) <> None) by (destruct SL1 as (_ & _ & _ & D1); exact D1).
  apply (EG3 A Kc rho1 a _ HUS HKc HRM); [rewrite E1r; exact RD1 | |].
  - rewrite E1r. fold ua L. intros rho2 rY tY SL4.
    assert (E2r : rw rho2 12%positive = rw rho 12%positive) by (destruct SL4 as (W2 & _); rewrite W2; exact E1r).
    apply (EG41a A Kc rho2 a _ HW HUS HKc). rewrite E2r. fold ua L. intros G2 rho3 rhoX3 tp3 HDB DL.
    apply (etriple_pre_pure segsA _ _ _ (fun w Hw => c5_pure nW st nx CST XGL HCST HXGL HCSTS HCSTD (fun X : AA => bumpP X) G2 A Kc rho rho1 rho2 rho3 a rhoX3 tp3 (w_tr w) (cfg_model (w_cfg w))
             (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) SL1 SL4 DL HDB (proj2 Hw))).
    intros (HK & RD & HWr & HLr & HDB3).
    exact (ETLa A Kc rho rho3 a tp G2 HUS HKc HWr HLr HK HL9 HDB3 RD rhoX3 tp3).
  - intros rY tY.
    apply (EG41b A Kc rho1 a _ HW HUS HKc). rewrite E1r. fold ua L. intros G2 rho3 rhoX3 tp3 HDB DL.
    apply (etriple_pre_pure segsA _ _ _ (fun w Hw => c5_pure nW st nx CST XGL HCST HXGL HCSTS HCSTD (fun X : AA => X) G2 A Kc rho rho1 rho1 rho3 a rhoX3 tp3 (w_tr w) (cfg_model (w_cfg w))
             (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) (fun X => eq_refl) SL1 (slink4_refl (aa_geom A) ua L rho1 RD1) DL HDB (proj2 Hw))).
    intros (HK & RD & HWr & HLr & HDB3).
    exact (ETLb A Kc rho rho3 a tp G2 HUS HKc HWr HLr HK HL9 HDB3 RD rhoX3 tp3).
Qed.

Lemma ecls_split : ltac2:(tb__ "0|5|
S5S1eS1ScQ40M0A1M1S3cS1S14G1A1S11OF_;S30S1bSbG0R5A2S1cSbG0S2R6PcM2A2A2A1A3S10S0S12S0VJGsC;S5R1LX;M3R9R8R7R6A5R5R4R3A5R2A3F_;S30S1aSbG0R6A2S1cSbG0S2R7G2A2A2A1A3S10S0S12S0VJGsC;G3RaR9R8R7A5R6R5R4A5R3A3M4F_;G4F_;F_;FQ;Ftp;FrhoX;FE;Fa;Frho;FKc;FA;").
Proof.
  intros A Kc rho a E rhoX tp Q HH HL.
  apply (etriple_pre_pure segsA _ _ (clsP true (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive)))
                                     \/ clsP false (bv_unsigned a) (secmapsize (bv_unsigned (rw rho 12%positive))))).
  - intros [tr [ms md]] Hw. pose proof (proj2 Hw) as HJ. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
    destruct HJ as [HJ _]. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.q0.SpineCallocSec3.JGs in HJ. cbn zeta in HJ. destruct HJ as (_ & _ & _ & HPD & _).
    destruct HPD as (_ & _ & _ & PDI & _). destruct PDI as (_ & _ & _ & _ & PDB).
    unfold clsP. destruct PDB as [X|X]; [right; exact X | left; exact X].
  - intros [X|X]; [exact (HH X) | exact (HL X)].
Qed.
End OKE.
End SpineCallocSecE4.

(* [comment removed for export] *)
Module DrainI1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "true"; "nil"; "bool"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "la_state"; "ax_S"; "leafA"; "sym_runA"; "ax_X"; "entailsA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "ss_next"; "sprop"; "ss_objs"; "ss_lenient"; "swf"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c8.DrainI1"; "N"; "FUEL"; "l1_0"; "l2_0"; "l2_1"; "l31_2"; "l30_0"; "l30_1"; "l30_2"; "l31_0"; "l31_1"; "cr_00"; "cr_01"; "cr_02"; "cr_10"; "cr_11"; "cr_12"; "s_00"; "s_01"; "s_02"; "s_10"; "s_11"; "s_12"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF"; "rstD"; "O_riX"; "ri_hasD"; "leaf_ok"; "mid_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "L_dh_f"; "NXD"; "O_cntD"; "O_dstD"; "dst_cells"; "Pre_dh_f"; "JD"; "JLD"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "nobj"; "vMFA"; "ri_e"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition N : Z := 1.
Definition FUEL : nat := 6000%nat.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3ef90S3S32A1A3S3eS1bA1S2A5").
Local Strategy expand [R_1__R].
Definition l1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition l1_0 := Eval vm_compute in (nth 0 l1 (mkLeafA (Pre_dh_f N) RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3ef90S3S32A1A3S3eS1bA1S2A5S7G0S1SeS1dS3SeA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [l1_0]). Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0S4S18SdS3eS1bA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Definition R_a__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3f440S3S32A1A3S33ScS1dA1U8A2S2A5").
Local Strategy expand [R_a__R].
Definition l2 := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_a__R).
Definition l2_0 := Eval vm_compute in (nth 0 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Definition l2_1 := Eval vm_compute in (nth 1 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Definition R_b0__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3ede4S3S32A1A3S33ScS1eA1U16A2S2A5").
Local Strategy expand [R_b0__R].
Definition l30 := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_b0__R).
Definition l30_0 := Eval vm_compute in (nth 0 l30 (mkLeafA (rstD (la_state l2_0) 22) RsCut)).
Definition l30_1 := Eval vm_compute in (nth 1 l30 (mkLeafA (rstD (la_state l2_0) 22) RsCut)).
Definition l30_2 := Eval vm_compute in (nth 2 l30 (mkLeafA (rstD (la_state l2_0) 22) RsCut)).
Definition cr_00 := Eval vm_compute in (ob_cells (nth (nobj (la_state l30_0) - 2) (ss_objs (ax_S (la_state l30_0))) O_pcc0)).
Definition s_00 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l30_0)) (ax_S (L_dh_f N))).
Lemma XX_00 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS21A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_00 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS21A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S26A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_00 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S26A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_00 : ltac2:(tb__ "0|0|
S0S4S11ScS21A1S39S1bA1S2cA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_00 : ltac2:(tb__ "0|0|
S0S4S43S2cS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_00 : leaf_ok N (la_state l30_0).
Proof. exists cr_00, s_00. exact (conj XX_00 (conj OB_00 (conj RI_00 (conj ENT_00 SID_00)))). Qed.
Definition cr_01 := Eval vm_compute in (ob_cells (nth (nobj (la_state l30_1) - 2) (ss_objs (ax_S (la_state l30_1))) O_pcc0)).
Definition s_01 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l30_1)) (ax_S (L_dh_f N))).
Lemma XX_01 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS22A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_01 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS22A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S27A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_01 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S27A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_01 : ltac2:(tb__ "0|0|
S0S4S11ScS22A1S39S1bA1S2dA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_01 : ltac2:(tb__ "0|0|
S0S4S43S2dS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_01 : leaf_ok N (la_state l30_1).
Proof. exists cr_01, s_01. exact (conj XX_01 (conj OB_01 (conj RI_01 (conj ENT_01 SID_01)))). Qed.
Definition cr_02 := Eval vm_compute in (ob_cells (nth (nobj (la_state l30_2) - 2) (ss_objs (ax_S (la_state l30_2))) O_pcc0)).
Definition s_02 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l30_2)) (ax_S (L_dh_f N))).
Lemma XX_02 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS23A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_02 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS23A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S28A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_02 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S28A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_02 : ltac2:(tb__ "0|0|
S0S4S11ScS23A1S39S1bA1S2eA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_02 : ltac2:(tb__ "0|0|
S0S4S43S2eS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_02 : leaf_ok N (la_state l30_2).
Proof. exists cr_02, s_02. exact (conj XX_02 (conj OB_02 (conj RI_02 (conj ENT_02 SID_02)))). Qed.
Lemma W_b0 : ltac2:(tb__ "0|0|
S0S4S19SdS33ScS1eA1U16A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b0 : ltac2:(tb__ "0|5|
S0S8S6S5S6S14S14A2M0A1M1S5S16A1M2A2M3A1S48SdScS1eA1M4A1SdS33G4U16A2A1A2S7G3S9G1G2S1G0S9S14S14S46S47A4S3G0A1A3S3S16A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b0 : ltac2:(tb__ "0|1|
S0S4S49S15SdS33ScS1eA1M0U16A2A1A1S15SdG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b0 : ltac2:(tb__ "0|0|
S0S4S18SdS33ScS1eA1U16A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b0 : ltac2:(tb__ "0|0|
S0S4S4aPf0S15SdS33ScS1eA1U16A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b0 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3ede4S3S32A1A3S33ScS1eA1U16A2S2A5S7G0S1SeS21S1SeS22S1SeS23S3SeA1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b0__R <: R_b0__R = Some [l30_0; l30_1; l30_2]). Qed.
Lemma m_b0 : ltac2:(tb__ "0|0|
S37S1cU16S1S32Z3ede4S3S32A1A3S36S1bA1ScS1eA1A5").
Proof.
  split; [exact W_b0|]. split; [exact D_b0|]. split; [exact NXe_b0|]. split; [exact LN_b0|]. split; [exact NL_b0|].
  exists [l30_0; l30_1; l30_2]. split; [exact R_b0|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_00 | exact k_01 | exact k_02 | destruct HIn].
Qed.
Definition R_b1__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3ede4S3S32A1A3S33ScS1fA1U16A2S2A5").
Local Strategy expand [R_b1__R].
Definition l31 := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_b1__R).
Definition l31_0 := Eval vm_compute in (nth 0 l31 (mkLeafA (rstD (la_state l2_1) 22) RsCut)).
Definition l31_1 := Eval vm_compute in (nth 1 l31 (mkLeafA (rstD (la_state l2_1) 22) RsCut)).
Definition l31_2 := Eval vm_compute in (nth 2 l31 (mkLeafA (rstD (la_state l2_1) 22) RsCut)).
Definition cr_10 := Eval vm_compute in (ob_cells (nth (nobj (la_state l31_0) - 2) (ss_objs (ax_S (la_state l31_0))) O_pcc0)).
Definition s_10 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l31_0)) (ax_S (L_dh_f N))).
Lemma XX_10 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS24A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_10 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS24A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S29A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_10 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S29A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_10 : ltac2:(tb__ "0|0|
S0S4S11ScS24A1S39S1bA1S2fA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_10 : ltac2:(tb__ "0|0|
S0S4S43S2fS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_10 : leaf_ok N (la_state l31_0).
Proof. exists cr_10, s_10. exact (conj XX_10 (conj OB_10 (conj RI_10 (conj ENT_10 SID_10)))). Qed.
Definition cr_11 := Eval vm_compute in (ob_cells (nth (nobj (la_state l31_1) - 2) (ss_objs (ax_S (la_state l31_1))) O_pcc0)).
Definition s_11 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l31_1)) (ax_S (L_dh_f N))).
Lemma XX_11 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS25A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_11 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS25A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S2aA1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_11 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S2aA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_11 : ltac2:(tb__ "0|0|
S0S4S11ScS25A1S39S1bA1S30A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_11 : ltac2:(tb__ "0|0|
S0S4S43S30S3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_11 : leaf_ok N (la_state l31_1).
Proof. exists cr_11, s_11. exact (conj XX_11 (conj OB_11 (conj RI_11 (conj ENT_11 SID_11)))). Qed.
Definition cr_12 := Eval vm_compute in (ob_cells (nth (nobj (la_state l31_2) - 2) (ss_objs (ax_S (la_state l31_2))) O_pcc0)).
Definition s_12 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l31_2)) (ax_S (L_dh_f N))).
Lemma XX_12 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS20A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_12 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS20A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S2bA1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_12 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S2bA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_12 : ltac2:(tb__ "0|0|
S0S4S11ScS20A1S39S1bA1S31A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_12 : ltac2:(tb__ "0|0|
S0S4S43S31S3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_12 : ltac2:(tb__ "0|0|
S36S1bScS20A1A2").
Proof. exists cr_12, s_12. exact (conj XX_12 (conj OB_12 (conj RI_12 (conj ENT_12 SID_12)))). Qed.
Lemma W_b1 : ltac2:(tb__ "0|0|
S0S4S19SdS33ScS1fA1U16A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b1 : ltac2:(tb__ "0|5|
S0S8S6S5S6S14S14A2M0A1M1S5S16A1M2A2M3A1S48SdScS1fA1M4A1SdS33G4U16A2A1A2S7G3S9G1G2S1G0S9S14S14S46S47A4S3G0A1A3S3S16A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b1 : ltac2:(tb__ "0|1|
S0S4S49S15SdS33ScS1fA1M0U16A2A1A1S15SdG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b1 : ltac2:(tb__ "0|0|
S0S4S18SdS33ScS1fA1U16A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b1 : ltac2:(tb__ "0|0|
S0S4S4aPf0S15SdS33ScS1fA1U16A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b1 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3ede4S3S32A1A3S33ScS1fA1U16A2S2A5S7G0S1SeS24S1SeS25S1SeS20S3SeA1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b1__R <: R_b1__R = Some [l31_0; l31_1; l31_2]). Qed.
Lemma m_b1 : ltac2:(tb__ "0|0|
S37S1cU16S1S32Z3ede4S3S32A1A3S36S1bA1ScS1fA1A5").
Proof.
  split; [exact W_b1|]. split; [exact D_b1|]. split; [exact NXe_b1|]. split; [exact LN_b1|]. split; [exact NL_b1|].
  exists [l31_0; l31_1; l31_2]. split; [exact R_b1|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_10 | exact k_11 | exact k_12 | destruct HIn].
Qed.
Lemma W_a : ltac2:(tb__ "0|0|
S0S4S19SdS33ScS1dA1U8A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a : ltac2:(tb__ "0|5|
S0S8S6S5S6S14S14A2M0A1M1S5S16A1M2A2M3A1S48SdScS1dA1M4A1SdS33G4U8A2A1A2S7G3S9G1G2S1G0S9S14S14S46S47A4S3G0A1A3S3S16A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a : ltac2:(tb__ "0|1|
S0S4S49S15SdS33ScS1dA1M0U8A2A1A1S15SdG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_a : ltac2:(tb__ "0|0|
S0S4S18SdS33ScS1dA1U8A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_a : ltac2:(tb__ "0|0|
S0S4S4aPf0S15SdS33ScS1dA1U8A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_a : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3f440S3S32A1A3S33ScS1dA1U8A2S2A5S7G0S1SeS1eS1SeS1fS3SeA1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_a__R <: R_a__R = Some [l2_0; l2_1]). Qed.
Lemma m_a : ltac2:(tb__ "0|1|
S37S1cU8S1S32Z3f440S3S32A1M0A3S37S1cU16S1S32Z3ede4G0A3S36S1bA1A4ScS1dA1A5").
Proof.
  split; [exact W_a|]. split; [exact D_a|]. split; [exact NXe_a|]. split; [exact LN_a|]. split; [exact NL_a|].
  exists [l2_0; l2_1]. split; [exact R_a|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact m_b0 | exact m_b1 | destruct HIn].
Qed.

Theorem drain_f_1 : ltac2:(tb__ "0|1|
S50S4bS4bOF_;F_;S4fR2R1A2S51R3A1S52S32S1aS5S53Q40A1A1R7S4eS38S3fS1bSbR4R8R3A5S3eS1bA1R2R1A5S4dS38S3aR2R1S1S6S12S4cA2M0S9S12S4cS39S1bA1S40R4R8R3A3A4S3G0A1A3A5A2Ftp;Frho;Fc;FA;FHKc;FKIT;FTR;FKc;").
Proof. exact (drain_f N FUEL l1_0 R_1 LN_1 m_a). Qed.
End DrainI1.

(* [comment removed for export] *)
Module DrainI2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "true"; "nil"; "bool"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "la_state"; "ax_S"; "leafA"; "sym_runA"; "ax_X"; "entailsA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "ss_next"; "sprop"; "ss_objs"; "ss_lenient"; "swf"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c8.DrainI2"; "N"; "FUEL"; "l1_0"; "l2_0"; "l2_1"; "l31_2"; "l30_0"; "l30_1"; "l30_2"; "l31_0"; "l31_1"; "cr_00"; "cr_01"; "cr_02"; "cr_10"; "cr_11"; "cr_12"; "s_00"; "s_01"; "s_02"; "s_10"; "s_11"; "s_12"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF"; "rstD"; "O_riX"; "ri_hasD"; "leaf_ok"; "mid_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "L_dh_f"; "NXD"; "O_cntD"; "O_dstD"; "dst_cells"; "Pre_dh_f"; "JD"; "JLD"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "nobj"; "vMFA"; "ri_e"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition N : Z := 2.
Definition FUEL : nat := 6000%nat.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3ef90S3S32A1A3S3eS1bA1S2A5").
Local Strategy expand [R_1__R].
Definition l1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition l1_0 := Eval vm_compute in (nth 0 l1 (mkLeafA (Pre_dh_f N) RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3ef90S3S32A1A3S3eS1bA1S2A5S7G0S1SeS1dS3SeA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [l1_0]). Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0S4S18SdS3eS1bA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Definition R_a__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3f440S3S32A1A3S33ScS1dA1U8A2S2A5").
Local Strategy expand [R_a__R].
Definition l2 := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_a__R).
Definition l2_0 := Eval vm_compute in (nth 0 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Definition l2_1 := Eval vm_compute in (nth 1 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Definition R_b0__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3ede4S3S32A1A3S33ScS1eA1U16A2S2A5").
Local Strategy expand [R_b0__R].
Definition l30 := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_b0__R).
Definition l30_0 := Eval vm_compute in (nth 0 l30 (mkLeafA (rstD (la_state l2_0) 22) RsCut)).
Definition l30_1 := Eval vm_compute in (nth 1 l30 (mkLeafA (rstD (la_state l2_0) 22) RsCut)).
Definition l30_2 := Eval vm_compute in (nth 2 l30 (mkLeafA (rstD (la_state l2_0) 22) RsCut)).
Definition cr_00 := Eval vm_compute in (ob_cells (nth (nobj (la_state l30_0) - 2) (ss_objs (ax_S (la_state l30_0))) O_pcc0)).
Definition s_00 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l30_0)) (ax_S (L_dh_f N))).
Lemma XX_00 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS21A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_00 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS21A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S26A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_00 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S26A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_00 : ltac2:(tb__ "0|0|
S0S4S11ScS21A1S39S1bA1S2cA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_00 : ltac2:(tb__ "0|0|
S0S4S43S2cS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_00 : leaf_ok N (la_state l30_0).
Proof. exists cr_00, s_00. exact (conj XX_00 (conj OB_00 (conj RI_00 (conj ENT_00 SID_00)))). Qed.
Definition cr_01 := Eval vm_compute in (ob_cells (nth (nobj (la_state l30_1) - 2) (ss_objs (ax_S (la_state l30_1))) O_pcc0)).
Definition s_01 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l30_1)) (ax_S (L_dh_f N))).
Lemma XX_01 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS22A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_01 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS22A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S27A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_01 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S27A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_01 : ltac2:(tb__ "0|0|
S0S4S11ScS22A1S39S1bA1S2dA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_01 : ltac2:(tb__ "0|0|
S0S4S43S2dS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_01 : leaf_ok N (la_state l30_1).
Proof. exists cr_01, s_01. exact (conj XX_01 (conj OB_01 (conj RI_01 (conj ENT_01 SID_01)))). Qed.
Definition cr_02 := Eval vm_compute in (ob_cells (nth (nobj (la_state l30_2) - 2) (ss_objs (ax_S (la_state l30_2))) O_pcc0)).
Definition s_02 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l30_2)) (ax_S (L_dh_f N))).
Lemma XX_02 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS23A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_02 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS23A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S28A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_02 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S28A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_02 : ltac2:(tb__ "0|0|
S0S4S11ScS23A1S39S1bA1S2eA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_02 : ltac2:(tb__ "0|0|
S0S4S43S2eS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_02 : leaf_ok N (la_state l30_2).
Proof. exists cr_02, s_02. exact (conj XX_02 (conj OB_02 (conj RI_02 (conj ENT_02 SID_02)))). Qed.
Lemma W_b0 : ltac2:(tb__ "0|0|
S0S4S19SdS33ScS1eA1U16A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b0 : ltac2:(tb__ "0|5|
S0S8S6S5S6S14S14A2M0A1M1S5S16A1M2A2M3A1S48SdScS1eA1M4A1SdS33G4U16A2A1A2S7G3S9G1G2S1G0S9S14S14S46S47A4S3G0A1A3S3S16A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b0 : ltac2:(tb__ "0|1|
S0S4S49S15SdS33ScS1eA1M0U16A2A1A1S15SdG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b0 : ltac2:(tb__ "0|0|
S0S4S18SdS33ScS1eA1U16A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b0 : ltac2:(tb__ "0|0|
S0S4S4aPf0S15SdS33ScS1eA1U16A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b0 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3ede4S3S32A1A3S33ScS1eA1U16A2S2A5S7G0S1SeS21S1SeS22S1SeS23S3SeA1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b0__R <: R_b0__R = Some [l30_0; l30_1; l30_2]). Qed.
Lemma m_b0 : ltac2:(tb__ "0|0|
S37S1cU16S1S32Z3ede4S3S32A1A3S36S1bA1ScS1eA1A5").
Proof.
  split; [exact W_b0|]. split; [exact D_b0|]. split; [exact NXe_b0|]. split; [exact LN_b0|]. split; [exact NL_b0|].
  exists [l30_0; l30_1; l30_2]. split; [exact R_b0|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_00 | exact k_01 | exact k_02 | destruct HIn].
Qed.
Definition R_b1__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3ede4S3S32A1A3S33ScS1fA1U16A2S2A5").
Local Strategy expand [R_b1__R].
Definition l31 := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_b1__R).
Definition l31_0 := Eval vm_compute in (nth 0 l31 (mkLeafA (rstD (la_state l2_1) 22) RsCut)).
Definition l31_1 := Eval vm_compute in (nth 1 l31 (mkLeafA (rstD (la_state l2_1) 22) RsCut)).
Definition l31_2 := Eval vm_compute in (nth 2 l31 (mkLeafA (rstD (la_state l2_1) 22) RsCut)).
Definition cr_10 := Eval vm_compute in (ob_cells (nth (nobj (la_state l31_0) - 2) (ss_objs (ax_S (la_state l31_0))) O_pcc0)).
Definition s_10 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l31_0)) (ax_S (L_dh_f N))).
Lemma XX_10 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS24A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_10 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS24A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S29A1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_10 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S29A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_10 : ltac2:(tb__ "0|0|
S0S4S11ScS24A1S39S1bA1S2fA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_10 : ltac2:(tb__ "0|0|
S0S4S43S2fS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_10 : leaf_ok N (la_state l31_0).
Proof. exists cr_10, s_10. exact (conj XX_10 (conj OB_10 (conj RI_10 (conj ENT_10 SID_10)))). Qed.
Definition cr_11 := Eval vm_compute in (ob_cells (nth (nobj (la_state l31_1) - 2) (ss_objs (ax_S (la_state l31_1))) O_pcc0)).
Definition s_11 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l31_1)) (ax_S (L_dh_f N))).
Lemma XX_11 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS25A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_11 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS25A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S2aA1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_11 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S2aA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_11 : ltac2:(tb__ "0|0|
S0S4S11ScS25A1S39S1bA1S30A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_11 : ltac2:(tb__ "0|0|
S0S4S43S30S3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_11 : leaf_ok N (la_state l31_1).
Proof. exists cr_11, s_11. exact (conj XX_11 (conj OB_11 (conj RI_11 (conj ENT_11 SID_11)))). Qed.
Definition cr_12 := Eval vm_compute in (ob_cells (nth (nobj (la_state l31_2) - 2) (ss_objs (ax_S (la_state l31_2))) O_pcc0)).
Definition s_12 := Eval vm_compute in (infer_sub NXD (ax_S (la_state l31_2)) (ax_S (L_dh_f N))).
Lemma XX_12 : ltac2:(tb__ "0|1|
S0S5S6S14S14A2M0A1S10ScS20A1A1S3G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_12 : ltac2:(tb__ "0|2|
S0S5S13A1S17SdScS20A1M0A1A1M1SaS13S42S13S41S44G0A1U3A2G1A3S1S13S3bS1bA1S1S13S34S2bA1S1S13S3cS1bS3dS1bA1A2S3S13A1A3A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_12 : ltac2:(tb__ "0|0|
S0S4S35S1bS45S2bA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_12 : ltac2:(tb__ "0|0|
S0S4S11ScS20A1S39S1bA1S31A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_12 : ltac2:(tb__ "0|0|
S0S4S43S31S3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma k_12 : ltac2:(tb__ "0|0|
S36S1bScS20A1A2").
Proof. exists cr_12, s_12. exact (conj XX_12 (conj OB_12 (conj RI_12 (conj ENT_12 SID_12)))). Qed.
Lemma W_b1 : ltac2:(tb__ "0|0|
S0S4S19SdS33ScS1fA1U16A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_b1 : ltac2:(tb__ "0|5|
S0S8S6S5S6S14S14A2M0A1M1S5S16A1M2A2M3A1S48SdScS1fA1M4A1SdS33G4U16A2A1A2S7G3S9G1G2S1G0S9S14S14S46S47A4S3G0A1A3S3S16A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_b1 : ltac2:(tb__ "0|1|
S0S4S49S15SdS33ScS1fA1M0U16A2A1A1S15SdG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_b1 : ltac2:(tb__ "0|0|
S0S4S18SdS33ScS1fA1U16A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_b1 : ltac2:(tb__ "0|0|
S0S4S4aPf0S15SdS33ScS1fA1U16A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_b1 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3ede4S3S32A1A3S33ScS1fA1U16A2S2A5S7G0S1SeS24S1SeS25S1SeS20S3SeA1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b1__R <: R_b1__R = Some [l31_0; l31_1; l31_2]). Qed.
Lemma m_b1 : ltac2:(tb__ "0|0|
S37S1cU16S1S32Z3ede4S3S32A1A3S36S1bA1ScS1fA1A5").
Proof.
  split; [exact W_b1|]. split; [exact D_b1|]. split; [exact NXe_b1|]. split; [exact LN_b1|]. split; [exact NL_b1|].
  exists [l31_0; l31_1; l31_2]. split; [exact R_b1|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_10 | exact k_11 | exact k_12 | destruct HIn].
Qed.
Lemma W_a : ltac2:(tb__ "0|0|
S0S4S19SdS33ScS1dA1U8A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_a : ltac2:(tb__ "0|5|
S0S8S6S5S6S14S14A2M0A1M1S5S16A1M2A2M3A1S48SdScS1dA1M4A1SdS33G4U8A2A1A2S7G3S9G1G2S1G0S9S14S14S46S47A4S3G0A1A3S3S16A1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NXe_a : ltac2:(tb__ "0|1|
S0S4S49S15SdS33ScS1dA1M0U8A2A1A1S15SdG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma LN_a : ltac2:(tb__ "0|0|
S0S4S18SdS33ScS1dA1U8A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NL_a : ltac2:(tb__ "0|0|
S0S4S4aPf0S15SdS33ScS1dA1U8A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_a : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3f440S3S32A1A3S33ScS1dA1U8A2S2A5S7G0S1SeS1eS1SeS1fS3SeA1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_a__R <: R_a__R = Some [l2_0; l2_1]). Qed.
Lemma m_a : ltac2:(tb__ "0|1|
S37S1cU8S1S32Z3f440S3S32A1M0A3S37S1cU16S1S32Z3ede4G0A3S36S1bA1A4ScS1dA1A5").
Proof.
  split; [exact W_a|]. split; [exact D_a|]. split; [exact NXe_a|]. split; [exact LN_a|]. split; [exact NL_a|].
  exists [l2_0; l2_1]. split; [exact R_a|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact m_b0 | exact m_b1 | destruct HIn].
Qed.

Theorem drain_f_2 : ltac2:(tb__ "0|1|
S50S4bS4bOF_;F_;S4fR2R1A2S51R3A1S52S32S1aS5S53Q40A1A1R7S4eS38S3fS1bSbR4R8R3A5S3eS1bA1R2R1A5S4dS38S3aR2R1S1S6S12S4cA2M0S9S12S4cS39S1bA1S40R4R8R3A3A4S3G0A1A3A5A2Ftp;Frho;Fc;FA;FHKc;FKIT;FTR;FKc;").
Proof. exact (drain_f N FUEL l1_0 R_1 LN_1 m_a). Qed.
End DrainI2.

(* [comment removed for export] *)
Module DrainG1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "iff"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "lt"; "of_nat"; "modulo"; "ge"; "sub"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c8.DrainG1.DG"; "F0d"; "mlinkG"; "zoneG"; "rlinkG"; "JDg"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "bool"; "list"; "nat"; "app"; "true"; "length"; "option"; "prod"; "None"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "vm_limit"; "alloc_top"; "m_vm_lazy"; "vm_maps"; "vm_noaccess"; "vm_reserved"; "VmMaps"; "maps_subtract"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "eval"; "rm"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Sh"; "free_array"; "max_count"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "revealedp"; "committed"; "shpage"; "releasedp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF"; "frozenD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "prim_credit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.RebuildRM"; "sub1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "cls_pure"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "model_ivs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "beg2"; "ri_e"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel"; "drainA"; "drain_cs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS"; "dfacts"; "dst_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "Kc_ok"; "top_high"; "tp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "live_ids"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ"; "AInvQ"; "rigidQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger"; "budget_boundD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "budget_bound"; "cs_cache"; "cs_mapped_free_array"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "JK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "q_ids"; "qall"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv InvLaws GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP PrimCredit PrimCreditLaws SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.RebuildRM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.RebuildD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Section DG.
Variable n : Z.
Variables (A : AA) (Kc : KcA) (c : Z) (rb : valuation) (tp0 : list word) (md0 : Model).
Let G : ageom := aa_geom A.
Let T : Z := ag_thread G.
Let SB : Z := ag_spacebeg G.
Let cs : class_state := SegQ_wf2.cls_of A c.
Let nf : Z := Z.of_nat (length (cs_free_array cs)).
Let mfa : Z := cs_mapped_free_array cs.

Definition F0d : Z := ltac2:(tb__ "0|0|
S7S36VSB;Vc;A2Vmfa;A2").

Definition entryG : Prop := ltac2:(tb__ "0|0|
S0S52VA;Vrb;Vtp0;Vmd0;A4S0S50VA;Vrb;A2S0S4fVA;Vrb;A2S0S53VA;Vrb;A2S0S4cVn;S1cVA;Vc;Vrb;A5S0S43Vmd0;A1S6S55VA;A1S34A2A2A2A2A2A2A2").

Definition mlinkG (f : nat) (tp : list word) (md : Model) : Prop := ltac2:(tb__ "0|a|
S21Vmd;A1S29S21Vmd0;A1S29S0S1S19S1fS15Q40A1M0G0A2A1M1S26R2A1S26R1A1A3S0S1G1S28R2A1S28R1A1A3S0S1SeS23R2A1S23R1A1A3S0S1SeS24R2A1S24R1A1A3S0S1G1S27R2A1S40S3aVf;A1M2S10S7S10Z40000M3A2M4S27R1A1A4A3S0S1G1S25Vmd;A1S40G2S10G4S25Vmd0;A1A4A3S5S19G0A1M5G5S0S1G5Vtp;S1bG0R1Vtp0;A3A3S0G0S33G0R1R2A3S0S2S33G0R2Vtp0;A3A1S0S1S18S39Vf;A1M6S1cA3S3bS10R2A2A2A2F_;Fp;S0S6SaS1dG0R1A2A1S18SeL_;M7G6Z8Z0M8X18x2M9A2S6S2cVmd;Vtp;A2S7S7S2cVmd0;Vtp0;A2G7G2G3G8X18x2A2S8Z1000G9A2A2A2A2A2A2Ltp1;A2A2A2A2A2A2A2TV0;TV;").

Definition zoneG (f : nat) (z : Z) : Prop := ltac2:(tb__ "0|1|
S3S0S1S18S39Vf;A1S1cA3S0S6S35S10A1M0Vz;A2S9Vz;S7G0Z8000A2A2A2A2S0S1S18S3cVf;A1S1cA3S0S6S10Vz;A2S9Vz;S7S10Z40000A2A2A2A2A2").
Definition rlinkG (f : nat) (r : valuation) : Prop := ltac2:(tb__ "0|3|
S0S15Q40M0A1S2S12Vf;S16G0R1A2A2A1S1S1eS15Q8A1M1A1M2S2fVr;R2A2S2fVrb;R2A2A3F_;Fa;SeS12Vf;R1A2S2S1G2S3dS32S2fVr;A1R2A3S20G1A1A3A1F_;Fz;A2").

Definition JDg (f : nat) : jpredA := ltac2:(tb__ "0|0|
S30S19S15Q40A1A1S19S2bA1S22S0S3eVrb;R4A2S0VKc;R2R1A2S0S11Vf;R3R1A3S13Vf;R4A2A2A2A2Lmd;Ltr;Ltp;Lr;").

Lemma JDg_K : ltac2:(tb__ "0|0|
S1aS59VKc;S14R1A1A2Ff;").
Proof. intros f r t tr md (_ & HK & _). exact HK. Qed.
Lemma JDg_stable : ltac2:(tb__ "0|0|
S1aSfS4eVKc;A1S5cPf0R2A2S44S32R3S14R4A1A3F_;F_;Fm;Ff;").
Proof.
  intros f m HKc Hm r r' tp tr md md' Hag Hme (HF & HK & HM & HR).
  destruct Hag as (Hw & Hl & Hrm). destruct Hme as ((mat' & ->) & Hpaid & _).
  assert (Erm : rm r' = rm r) by (apply functional_extensionality; intros a; symmetry; apply Hrm).
  split; [|split; [|split]].
  - destruct HF as [F1 F2]. split; [intros i Hi; rewrite (F1 i Hi); apply Hw; lia | intros l; rewrite (F2 l); apply Hl].
  - rewrite with_vm_backing_with_vm. apply HKc. exact HK.
  - unfold mlinkG in *. cbn zeta in *. destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & M9 & M10).
    split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|]. split; [exact M5|]. split; [exact M6|].
    exists tp1. split; [exact M7|]. split; [exact M8|]. split; [exact M9|]. rewrite Hpaid. exact M10.
  - unfold rlinkG. rewrite Erm. exact HR.
Qed.

Lemma zoneG_dec : ltac2:(tb__ "0|1|
S1aSeS3S12R2R1A2M0S2G0A1A2Fz;Ff;").
Proof. intros f z. unfold zoneG. destruct (revealedp f), (releasedp f); lia. Qed.
Lemma rlinkG_view : ltac2:(tb__ "0|0|
S1aS30S13R2R1A2SeS2S12R4R1A2A1S1S1eS15Q8A1A1S3dS32S2fR4A1R2A3S3dS32S2fVrb;A1R2A3A3F_;Fz;F_;Fr;Ff;").
Proof.
  intros f r [R1 _] z Hz. unfold view. destruct ((0 <=? z) && (z <? 2 ^ 64))%bool eqn:E; [|reflexivity].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  unfold rd_of. rewrite R1 by (rewrite u64_lit by lia; exact Hz). reflexivity.
Qed.

Lemma mlinkG_commit : ltac2:(tb__ "0|8|
S19S15Q40A1M0A1S22S22S11U0R3R2A3S1S19S1fG0G0A2A1M1S26S21R2A1A1S26S21R3A1M2A1A3S1G1S28G2A1S28S21R4A1M3A1A3S1SeS23G3A1S23S21R5A1M4A1A3S1SeS24G4A1S24S21R6A1M5A1A3S1G1S27G5A1S2aS27S21R7A1A1S10S7S10Z40000M6A2M7A3A3S1G1S25R7A1S2aS25R8A1S10G7A3A3S6S2cR8RaA2S7S2cR9RaA2G6A2A2S11U1RbR9A3F_;F_;F_;F_;F_;F_;F_;F_;Fmd';Fmd;Ftp;").
Proof.
  intros tp md md' HM EM ER EL ET EN ELz HP.
  unfold mlinkG in HM |- *. cbn zeta in HM |- *. destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & M9 & M10).
  rewrite EM, ER, EL, ET, EN, ELz, M5, M6. unfold committed, revealedp, sub1 in *. cbn [Nat.leb] in *.
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
  split; [reflexivity|]. split; [reflexivity|]. exists tp1. split; [exact M7|]. split; [exact M8|]. split; [exact M9|]. lia.
Qed.

Lemma mlinkG_reveal : ltac2:(tb__ "0|2|
S19S15Q40A1M0A1M1S22G1S11U1R3R2A3G0S33G0R1R3A3S0S2S33G0R2R6A3A1S3bS10R2A2A2F_;Fq;S6SaS1dG0R3A2A1Z8A2S6S2cR5S1bG0R4R6A3A2S7S2cR5R6A2Z8000A2A2S11U2S1bG0R5R7A3R6A3F_;F_;F_;F_;Ftpn;Fmd;Ftp;").
Proof.
  intros tp md tpn HM Hq Hn HP.
  unfold mlinkG in HM |- *. cbn zeta in HM |- *. destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & M9 & M10).
  unfold committed, revealedp in *. cbn [Nat.leb] in *.
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|]. split; [exact M5|]. split; [exact M6|].
  exists (tpn ++ tp1). split; [rewrite M7, app_assoc; reflexivity|].
  split.
  { intros q Hin. apply in_app_or in Hin as [Hin|Hin].
    - destruct (Hq q Hin) as [N S]. split; [intros X; apply N; rewrite M7; apply in_or_app; right; exact X | split; [reflexivity | exact S]].
    - destruct (M8 q Hin) as [_ [X _]]. discriminate X. }
  split; [rewrite length_app, Nat2Z.inj_add; lia | lia].
Qed.

Lemma mlinkG_release : ltac2:(tb__ "0|0|
S19S15Q40A1A1S22S11U2R2R1A3S11U3R3R2A3F_;Fmd;Ftp;").
Proof. intros tp md HM. exact HM. Qed.

Lemma zoneG_0 : ltac2:(tb__ "0|0|
SeS2S12U0R1A2A1Fz;").
Proof. intros z [[X _]|[X _]]; discriminate X. Qed.
Lemma zoneG_1 : ltac2:(tb__ "0|0|
SeS2S12U1R1A2A1Fz;").
Proof. intros z [[X _]|[X _]]; discriminate X. Qed.
Lemma zoneG_2 : ltac2:(tb__ "0|1|
SeS4S12U2R1A2S0S6S35S10A1M0R1A2S9R1S7G0Z8000A2A2A2A2Fz;").
Proof. intros z. unfold zoneG, revealedp, releasedp. cbn [Nat.leb]. split; [intros [[_ X]|[X _]]; [exact X | discriminate X] | intros X; left; split; [reflexivity | exact X]]. Qed.
Lemma zoneG_3 : ltac2:(tb__ "0|1|
SeS4S12U3R1A2S3S0S6S35S10A1M0R1A2S9R1S7G0Z8000A2A2A2S0S6S10R1A2S9R1S7S10Z40000A2A2A2A2A2Fz;").
Proof. intros z. unfold zoneG, revealedp, releasedp. cbn [Nat.leb]. split; [intros [[_ X]|[_ X]]; [left | right]; exact X | intros [X|X]; [left | right]; (split; [reflexivity | exact X])]. Qed.

Lemma rlinkG_01 : ltac2:(tb__ "0|0|
S30S13U0R1A2S13U1R2A2F_;Fr;").
Proof.
  intros r [R1 R2]. split; [intros a Ha; apply R1; apply zoneG_0 | intros z Hz; exfalso; exact (zoneG_1 z Hz)].
Qed.

Hypothesis HE : entryG.

Lemma g_pure : ltac2:(tb__ "0|2|
S0S0S6Z1Vc;A2S6Vc;Z1eA2A2S0S1SeS42Vc;A1Vn;A3S0S1SeSaS1dSeS56Vcs;A1A2A1S37Vc;A1A3S0S41Vc;Vcs;S1bSeS51VG;VA;Vc;A3S5aVG;S5bVA;A1Vc;A3A3M0A3S0S41Vc;S4bVc;Vcs;A2M1G0A3S1SeS57G1A1S7Vmfa;Z40000A2A3A2A2A2A2A2").
Proof.
  destruct HE as (HA & _ & _ & _ & DF & _). destruct DF as (_ & C1 & EK & HFULL & HGR & _). fold cs in HFULL, HGR.
  destruct (kchunks_facts c C1) as (K1 & K2 & K3).
  pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _ & (HQP & _) & _). destruct Hprim as (_ & _ & _ & PC).
  pose proof (entry_cls_pureQ _ A c C1 (PC c C1) HQP) as HP. change (nthZ (aa_cls A) c cs_empty) with cs in HP. fold G in HP.
  destruct (drain_pure c cs _ C1 HP ltac:(rewrite HFULL; lia)) as (HP' & _).
  split; [exact C1|]. split; [exact EK|]. split; [exact HFULL|]. split; [exact HP|]. split; [exact HP'|].
  unfold drain_cs. cbn [cs_mapped_free_array]. rewrite HGR. unfold kFreeArrayMapSize. reflexivity.
Qed.

Lemma g_nums : ltac2:(tb__ "0|9|
S0S0S6Z1M0Vc;A2S6Vc;Z1eA2A2S0S1SeS42Vc;A1Vn;A3S0S0S6G0Vn;A2S6Vn;Z8A2A2S0S1SeS37Vc;A1S8Z2Vn;A2A3S0S6Z1000M1VT;A2S0S6S7VT;G1A2M2S58VG;A1M3A2S0S6G3Z7fffff800000A2S0S3S6G2Z10000A2S6Z646000VT;A2A2S0S6Z10007fff8000M4VSB;A2S0S6S7S7VSB;Z2000000000A2G1A2M5G3A2S0S3S6G2VSB;A2S6G5VT;A2A2S0S3S6G2Z7fff7000A2S6G4VT;A2A2S0S6Z0M6Vnf;A2S0S6S8Z4M7Vnf;A2Vmfa;A2S0S9Vmfa;S8G7S7Vnf;Vn;A2A2A2S0S1SeSbVmfa;Z40000M8A2G6A3S6S7Vmfa;G8A2Z20000000A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  destruct g_pure as (C1 & EK & HFULL & HP & HP' & EMF).
  destruct HE as (HA & _ & _ & _ & DF & _). destruct DF as (_ & _ & _ & _ & HGR & _). fold cs in HGR.
  destruct (kchunks_facts c C1) as (K1 & K2 & K3). rewrite EK in K1, K2.
  pose proof HA as (HG & _ & _ & _ & _ & HI3 & _). fold G in HG.
  pose proof (geom_numsS _ HG) as (_ & _ & _ & G4 & G5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG). fold T in G4, G5.
  pose proof (geom_old _ HG) as X. rewrite FS_total_val, kSpaceSize_val in X. unfold HIGH_SHADOW_END in X. fold SB in X.
  pose proof (geom_bands _ HG) as (_ & TB & _ & _ & TI & _ & _). fold T in TB, TI. unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in TB, TI.
  destruct (proj1 HI3) as (T3 & _). rewrite kSpaceSize_val in T3. fold G in T3. fold T SB in T3.
  destruct HP as (_ & _ & _ & P4 & P4' & P5 & _). destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P11'). rewrite EMF in P11'.
  destruct (cap_facts c C1) as (_ & _ & _ & _ & FC & _). unfold kFreeArraySize in FC. unfold kFreeArrayMapSize in P4. fold mfa nf in P4, P4', P5.
  unfold drain_grows in HGR. fold nf mfa in HGR. apply Z.ltb_lt in HGR. rewrite EK in HGR.
  split; [exact C1|]. split; [exact EK|]. split; [exact K1|]. split; [symmetry; exact K2|].
  split; [exact G4|]. split; [exact G5|]. split; [clear -TG; lia|]. split; [clear -TI; lia|].
  split; [clear -X; tauto|]. split; [clear -X; lia|]. split; [clear -T3; lia|]. split; [clear -TB; lia|].
  split; [unfold nf; apply Zle_0_nat|]. split; [exact P5|]. split; [exact HGR|]. split; [exact P4 | clear -P11' FC; lia].
Qed.

Lemma g_piece : ltac2:(tb__ "0|1|
S0S6S7VSB;Z100000000M0A2S10A2S0S6S7S10Z40000A2S7VSB;Z2000000000A2A2S0S1SeSbS10Z10000A2Z0A3S1SeS36VSB;Vc;A2S7S7VSB;S8Vc;G0A2A2Ze0000000A2A3A2A2A2").
Proof.
  destruct g_nums as (C1 & _ & _ & _ & _ & _ & _ & _ & S1 & _ & _ & _ & NF0 & NF1 & _ & MM & MC).
  destruct HE as (HA & _). pose proof HA as (HG & _). fold G in HG.
  assert (FAv : free_array SB c = SB + c * 4294967296 + 3758096384) by (unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; lia).
  assert (SBA : SB mod 65536 = 0).
  { pose proof (geom_old _ HG) as X. fold SB in X. destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X12 & _). exact X12. }
  unfold F0d. rewrite FAv. split; [lia|]. split; [lia|]. split; [|reflexivity].
  destruct (proj1 (Z.mod_divide SB 65536 ltac:(lia)) SBA) as [q Hq]. destruct (proj1 (Z.mod_divide mfa 262144 ltac:(lia)) MM) as [q2 Hq2].
  rewrite Hq, Hq2. replace (q * 65536 + c * 4294967296 + 3758096384 + q2 * 262144) with ((q + c * 65536 + 57344 + q2 * 4) * 65536) by lia. apply Z_mod_mult.
Qed.

Lemma g_credit : ltac2:(tb__ "0|3|
S0S1SeS7S3fS4aVA;Vc;A2A1Z48000M0A2S3fVA;A1M1A3S0S6S7S2cVmd0;Vtp0;A2M2G1A2S54VA;A1A2S0S6S7G2G0A2S34A2S1SeS23S21Vmd0;A1A1S34A3A2A2A2").
Proof.
  destruct g_pure as (C1 & EK & HFULL & HP & HP' & EMF).
  destruct HE as (HA & _ & _ & _ & DF & _ & HBUD). destruct DF as (Hini & _).
  pose proof HA as (_ & _ & _ & HRest & HM & _). destruct HRest as (_ & _ & (PL & _) & _ & _ & HD & _).
  assert (Hlen : (Z.to_nat c < length (aa_cls A))%nat) by (rewrite PL; clear -C1; lia).
  assert (E1 : nth (Z.to_nat c) (aa_cls (drainA A c)) cs_empty = drain_cs c cs).
  { unfold drainA. cbn [aa_cls]. rewrite nth_list_upd_same by exact Hlen. reflexivity. }
  assert (E0 : nth (Z.to_nat c) (aa_cls A) cs_empty = cs) by reflexivity.
  pose proof (prim_credit_famap A (drainA A c) c C1) as PP. cbn zeta in PP. rewrite E1, E0 in PP.
  destruct HP as (P1 & _ & _ & P4 & _ & _ & _ & _ & _ & _ & P10 & _). destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P11').
  assert (M8 : cs_mapped_user cs mod 8 = 0).
  { unfold kUserMapSize in P1. destruct (proj1 (Z.mod_divide _ (2 ^ 18) ltac:(clear; lia)) P1) as [q Hq]. rewrite Hq. replace (q * 2 ^ 18) with (q * 32768 * 8) by (clear; lia). apply Z_mod_mult. }
  assert (F8 : mfa mod 8 = 0).
  { unfold kFreeArrayMapSize in P4. fold mfa in P4. destruct (proj1 (Z.mod_divide mfa (2 ^ 18) ltac:(clear; lia)) P4) as [q Hq]. rewrite Hq. replace (q * 2 ^ 18) with (q * 32768 * 8) by (clear; lia). apply Z_mod_mult. }
  rewrite EMF in PP, P11'. fold mfa in PP.
  specialize (PP ltac:(intros c' Hc' Hne; unfold drainA; cbn [aa_cls]; apply nth_list_upd_other; clear -C1 Hc' Hne; lia)
                 ltac:(reflexivity) M8 P10 F8 ltac:(rewrite Z.add_mod, F8 by (clear; lia); reflexivity) ltac:(clear -P11'; lia)).
  replace (mfa + 262144 - mfa) with 262144 in PP by (clear; lia). change (262144 / 8) with 32768 in PP.
  pose proof (prim_credit_nonneg (drainA A c)) as NN.
  destruct HM as (_ & PB & VL & V0 & K0' & F0' & _ & _ & _ & _ & _ & _ & DN & PC & _).
  assert (BB : budget_boundD A <= budget_bound A).
  { apply budgetD_le_budget; [exact (dep_cost_bound_mem _ _ HD) | exact (dm_F_NFBLK _ _ HD) | exact DN | exact PC | exact K0' | exact F0']. }
  split; [clear -PP; lia|]. split; [exact PB|]. split; [clear -PP NN PB BB HBUD; lia | exact VL].
Qed.

Lemma g_headroom : ltac2:(tb__ "0|2|
S1aS19S15Q40A1A1S22S11R3R2R1A3ScS2dR2R3A2SdZ48000S7S18SeL_;M0S3aR4A1Z40000Z0M1X18x2S8Z1000G0S39R4A1Z8G1X18x2A2A2A2A2F_;Fmd;Ftp;Ff;").
Proof.
  intros f tp md HM. destruct g_credit as (_ & _ & CR & VL).
  unfold mlinkG in HM. cbn zeta in HM. destruct HM as (_ & _ & M3 & _ & _ & _ & tp1 & _ & _ & _ & M10).
  unfold headroom. rewrite M3, VL. destruct (committed f), (revealedp f); clear -CR M10; lia.
Qed.

Lemma g_evals : ltac2:(tb__ "0|3|
S30S3eVrb;R1A2S0S1SeS16Q40M0S2eR2S45A2A2S7S7VT;Zd0A2S8Z50Vc;A2A2A3S0S1SeS16G0S2eR2S48A2M1A2S38VSB;Vc;A2A3S0S1S15G0A1M2S2eR2S47A2G1A3S0S1SeS16G0S2eR2S4dA2A2S7S36VSB;Vc;A2S8Z4Vnf;A2A2A3S0S1SeS16G0S2eR2S46A2A2S10A3S0S1SeS16G0S2eR2S49A2A2VT;A3S0S1G2S31R2PddA2S17G0Vnf;A2A3S1G2S31R2PdeA2S17G0Vmfa;A2A3A2A2A2A2A2A2A2F_;Fr;").
Proof.
  intros r [Fw _]. destruct g_nums as (C1 & _ & K1 & _ & T1 & T2 & TG & _ & S1 & S2 & _ & _ & NF0 & NF1 & NF2 & _ & NF3).
  destruct g_piece as (_ & _ & _ & FAv).
  destruct HE as (_ & _ & _ & (E151 & _ & E155 & E156) & DF & _). destruct DF as (_ & _ & _ & _ & _ & E158 & _ & E221 & E222 & _ & _ & E225 & _).
  fold G in E151, E155, E156, E225. fold T in E151. fold SB in E155, E156, E225. fold cs in E221, E222. fold nf in E221. fold mfa in E222.
  rewrite (Fw 151%positive) in E151 by lia. rewrite (Fw 155%positive) in E155 by lia. rewrite (Fw 156%positive) in E156 by lia.
  rewrite (Fw V_CLS) in E158 by (unfold V_CLS; lia). rewrite (Fw 221%positive) in E221 by lia. rewrite (Fw 222%positive) in E222 by lia. rewrite (Fw 225%positive) in E225 by lia.
  rewrite kSpaceSize_val in E156.
  assert (RIv : region_info SB c = SB + 137438953472 + c * 128) by (unfold region_info, kRegionInfoStride; rewrite kSpaceSize_val; lia).
  assert (EFA : bv_unsigned (eval r fa_e) = free_array SB c).
  { unfold fa_e, vSB, V_CLS in *. cbn [eval]. rewrite E155, E158.
    rewrite add_val, add_val, sll_val, !u64_lit by lia. change (32 mod 64) with 32. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite (Z.mod_small (_ * 2 ^ 32)) by lia. rewrite (Z.mod_small (_ + 3758096384)) by lia. rewrite Z.mod_small by lia. rewrite FAv. lia. }
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - unfold pc_base, vT, V_CLS in *. cbn [eval]. rewrite E151, E158. rewrite add_val, add_val, mul_val, !u64_lit by lia.
    rewrite (Z.mod_small (_ * 80)) by lia. rewrite (Z.mod_small (T + 208)) by lia. rewrite Z.mod_small by lia. lia.
  - unfold vRI. cbn [eval]. rewrite E225. apply u64_lit. rewrite RIv. lia.
  - unfold ri_e, vRI, vRIS, V_CLS in *. cbn [eval]. rewrite E156, E158, E225. apply bv_eq.
    rewrite add_val, sll_val, !u64_lit by (rewrite ?RIv; lia). change (7 mod 64) with 7. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite (Z.mod_small (_ * 2 ^ 7)) by lia. rewrite Z.mod_small by lia. rewrite RIv. lia.
  - unfold dst_e, vNF. cbn [eval]. rewrite add_val, EFA, sll_val, E221, !u64_lit by lia. change (2 mod 64) with 2. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite (Z.mod_small (nf * 2 ^ 2)) by lia. rewrite Z.mod_small by (rewrite FAv; lia). lia.
  - unfold beg2, fa_e2, rb_e, vMFA, vSB, V_CLS, F0d in *. cbn [eval]. rewrite !add_val, sll_val, E155, E158, E222, !u64_lit by lia.
    change (32 mod 64) with 32. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_small (_ * 2 ^ 32)) by lia. rewrite (Z.mod_small (_ + _ * 2 ^ 32)) by lia.
    rewrite (Z.mod_small (_ + _ * 2 ^ 32 + 3758096384)) by lia. rewrite Z.mod_small by lia. rewrite FAv. lia.
  - unfold vT. cbn [eval]. rewrite E151. apply u64_lit. lia.
  - exact E221.
  - exact E222.
Qed.
End DG.
End DrainG1.

