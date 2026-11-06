(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw jr k4.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.

(* [comment removed for export] *)
Module SpineMallocU2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "ss_objs"; "ss_next"; "sprop"; "ss_facts"; "ss_lenient"; "swf"; "rw"; "rm"; "agree_below"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "sym_runA"; "ax_X"; "axst"; "la_state"; "@Corelib.Init.Datatypes"; "list"; "nil"; "bool"; "cons"; "true"; "prod"; "app"; "false"; "Some"; "option"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineMallocU1"; "cU1"; "cU0"; "kU1"; "kU2"; "JU"; "cU2"; "perm_okb"; "O_arrF"; "O_pcmZ"; "eU"; "idx1"; "idx2"; "sU1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "nobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "O_st"; "O_pcc0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2"; "BASEF"; "BASEO"; "@Stdlib.Lists.List"; "incl"; "In"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "KcA"; "UStopLeOrPc"; "ustop"; "Kc_ok"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_cache_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.RebuildI"; "initA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "entryR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocR5"; "posts_conv"; "rho_after"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocS9 PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jq.SpineMallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jz.RebuildRN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.RebuildI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineMallocU1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

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
ScS1cS13SeA1M0A1SfS1eVF;S16S21Z41358S14S21A1A3S26VE3;A1S17A5S1bG0S16SeVLU1;S14SeA1A3A2A3").
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
ScS1cS13SeA1M0A1SfS1eVF;S16S21Z413f4S14S21A1A3S25VL1;A1S17A5S1bG0S16SeVLU2;S14SeA1A3A2A3").
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
  apply (ju_run F [0x41358] (cU0 E3) [LU1] false r tp Q R_u1 LN_u1 NX_u1). intros L r1 [<-|[]] _. fold L1.

  destruct (perm_okb_sound _ _ PERM1) as (ND1 & LT1 & CV1).
  apply (tr_pre Kc TR KIT (SPA segs (JUp false) (sU1 L1) r1 tp)).
  { intros w Hw. exact (SPA_select segs (JUp false) r1 L1 (idx1 L1) tp w Hw ND1 LT1 CV1). }
  apply (tr_cut Kc TR KIT valuation _ (fun r2 => SPA segs (JUp false) (kU1 L1) r2 tp) Q).
  { intros [tr [ms md]] Hw. exists (rho_absorb r1 [O_pcc0; O_pcmZ] (vms md tp ms)).
    apply (SPA_unobj_J (JUp false) (JUp false) r1 (sU1 L1) _ [O_pcc0; O_pcmZ] tp tr ms md OB_s1 Hw).
    intros Hsm HJ. exact (u_release1 A Kc rb tp0 md0 W st rho HE Hini _ _ r1 tp tr (vms md tp ms) (vmd md) md OB_s1 Hsm HJ). }
  intros r2.

  apply (tr_pre Kc TR KIT (SPA segs (JUp false) (cU1 L1) r2 tp)); [intros w Hw; exact (u_carve_arr r2 tp w Hw)|].
  apply (ju_run F [0x413f4] (cU1 L1) [LU2] false r2 tp Q R_u2 LN_u2 NX_u2). intros L r3 [<-|[]] _. fold L2.
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
ScS1cS13SeA1M0A1SfS1eVF;S16S21Z41358S14S21A1A3S26VE3;A1S17A5S1bG0S16SeVLU1;S14SeA1A3A2A3").
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
ScS1cS13SeA1M0A1SfS1eVF;S16S21Z413f4S14S21A1A3S25VL1;A1S17A5S1bG0S16SeVLU2;S14SeA1A3A2A3").
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
Module SpineCallocR14.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "of_nat"; "lt"; "ltb"; "sub"; "to_nat"; "ge"; "modulo"; "pow"; "@Corelib.Init.Datatypes"; "bool"; "length"; "list"; "None"; "app"; "nil"; "option"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SAlu"; "eval"; "valuation"; "rm"; "SLit"; "SMd"; "SVar"; "sv"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ"; "FAb"; "phase"; "committed"; "frozen"; "ghosts"; "ph_f"; "ph_fill"; "ph_pop"; "revealedp"; "rlink"; "entryR"; "mlink"; "ph_u"; "releasedp"; "zoneR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "prim_credit"; "MUCAP"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "ALU_SLL"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR"; "vNEW"; "vK"; "vNF"; "vAU"; "vFA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "m_vmmaps"; "vm_limit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "class_state"; "cs_allocated_user"; "cs_cache"; "cs_free_array"; "cs_mapped_free_array"; "cs_mapped_user"; "AA"; "ag_spacebeg"; "ag_thread"; "budget_bound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refill_cs"; "cls_pure"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "view"; "cell_ok"; "mkACell"; "@Corelib.Lists.ListDef"; "nth"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kUserMapSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "live_ids"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModelP"; "newZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "q_ids"; "qall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k2.SpineCallocR14.ARMP"; "e16P"; "e32P"; "e48P"; "e_srcP"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require PrimCredit PrimCreditLaws Inv InvLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel RefillModelP RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModelP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.CRefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jr.SpineCallocR6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j9.SpineCallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SpineCallocR12 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.SpineCallocR13.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

Lemma AInvA_credit : ltac2:(tb__ "0|0|
S4aS1aS12S21Q40A1A1S3eS59S3dR4R3R2R1A5S0S5S6S41R2R3A2S31R5A1A2S4dR5A1A2S1S4S40S3fR2A1A1S37A3A2F_;Fmd;Ftp;Frho;FA;").
Proof.
  intros A rho tp md (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (_ & _ & _ & _ & _ & HD & _). unfold depot_wf in HD.
  destruct HM as (_ & PB & VL & V0 & K0 & F0 & _ & _ & _ & _ & _ & _ & DN & PC & _).
  split; [|exact VL]. eapply Z.le_trans; [exact PB|].
  apply budgetD_le_budget; [| |exact DN|exact PC|exact K0|exact F0].
  - exact (dep_cost_bound_mem _ _ HD).
  - exact (dm_F_NFBLK _ _ HD).
Qed.

Section ARMP.
Variables (A : AA) (rb : valuation) (tp0 : list word) (md0 : Model) (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HE : ltac2:(tb__ "0|0|
S2cVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis PF : popfacts A rb.
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let cs : class_state := cst_of A nv.
Let k : Z := kchunks c.
Let S : Z := Size c.
Let nf : Z := Z.of_nat (length (cs_free_array cs)).
Let au : Z := cs_allocated_user cs.
Let mu : Z := cs_mapped_user cs.
Let mfa : Z := cs_mapped_free_array cs.
Let new : Z := gh_new A rb.
Let out : list Z := ltac2:(tb__ "0|1|
S14S4S5aS43VA;A1M0VA;Vc;A3S5cG0S5dVA;A1Vc;A3A3").
Let fP : list Z := faP c cs.

Lemma P_c : 1 <= c <= 30.
Proof. pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. destruct CF as ((_ & C1 & _) & _). exact C1. Qed.

Lemma entry_pure : ltac2:(tb__ "0|0|
S0S4fVc;Vcs;Vout;A3S0S1S12S4A1S46Vcs;A1S15S4A1A3S0S9Vnf;Vk;A2S5S6Vmu;S58A2S32Vc;A1A2A2A2A2").
Proof.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF.
  destruct CF as (_ & _ & _ & _ & (_ & _ & Hc0) & _).
  destruct HE as (_ & HA & _). pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _ & Hq & _). destruct Hprim as (_ & _ & _ & PC).
  destruct PF as (NP & RM & _). fold nv c cs in NP, RM.
  split; [exact (entry_cls_pure _ A c P_c HG (PC c P_c) Hq)|]. split; [exact Hc0|]. split; [exact NP | unfold kUserMapSize; exact RM].
Qed.

Lemma P_newZ : ltac2:(tb__ "0|0|
S1S4S5bVc;Vcs;A2Vnew;A3").
Proof. unfold newZ, new, gh_new. fold nv c cs. reflexivity. Qed.

Lemma P_csR : ltac2:(tb__ "0|4|
S4eVc;Vcs;A2S44S0S1S12S4A1S46R1A1M0S56S4ScSbS6Vnf;Vnew;A2M1Vk;A2M2A1VfP;A3A3S0S1S4S8S11S4G0A2A1Vk;A3S0S1S4S8S11S4S47R1A1A2A1G2A3S0S1S4S45R1A1S6Vau;S7Vnew;VS;A2A2A3S0S1S4S49R1A1S6Vmu;Z40000M3A2A3S0S1S4S48R1A1S10S4L_;SaVmfa;S7Z4G1A2A2S6Vmfa;G3A2Vmfa;X10x2A3S0S1S4S8S11S4VfP;A2A1G1A3S4S62S4R1VfP;A3S0S5Z0R2A2S9R2SfZ2Z1cA2A2A2F_;Fx;A2A2A2A2A2A2A2TcsR;").
Proof.
  destruct entry_pure as (HP & Hc0 & NP & RM).
  pose proof (P_fields c cs out P_c HP NP RM) as X. cbn zeta in X. rewrite P_newZ in X. fold nf au mu mfa S k fP in X.
  pose proof (P_faP_len c cs out P_c HP RM) as LP. rewrite P_newZ in LP. fold nf fP in LP.
  destruct X as (X1 & X2 & X3 & _ & X5 & X6 & X7). rewrite LP in X1.
  cbn zeta. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X5|]. split; [exact X6|]. split; [exact X7|]. split; [exact LP|].
  exact (P_ids c cs out P_c HP RM).
Qed.

Lemma pop_credit_eq : ltac2:(tb__ "0|1|
S1S4S6S6S31S50VA;Vc;A2A1Z48000M0A2S10S4L_;SaVmfa;S7Z4S6Vnf;Vnew;A2A2A2G0Z0X10x2A2S31VA;A1A3").
Proof.
  destruct entry_pure as (HP & Hc0 & NP & RM). pose proof P_csR as (_ & _ & _ & _ & EMU & EMF & _). cbn zeta in EMU, EMF.
  destruct (refill_pure c cs out P_c HP Hc0 ltac:(intros _; exact RM)) as (HPR & _). cbn zeta in HPR.
  destruct HPR as (R1 & _ & _ & R4 & _ & _ & _ & _ & _ & _ & R10 & R11). destruct HP as (P1 & _ & _ & P4 & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof HE as (_ & HA & _).
  pose proof HA as (_ & _ & _ & HRest & _). destruct HRest as (_ & _ & (PL & _) & _).
  assert (Hlen : (Z.to_nat c < length (aa_cls A))%nat) by (rewrite PL; pose proof P_c as C1; clear -C1; lia).
  pose proof (prim_credit_populate A (refillA A c) c P_c) as PP. cbn zeta in PP.
  assert (E1 : nth (Z.to_nat c) (aa_cls (refillA A c)) cs_empty = refill_cs c cs).
  { unfold refillA. cbn [aa_cls]. rewrite nth_list_upd_same by exact Hlen. reflexivity. }
  assert (E0 : nth (Z.to_nat c) (aa_cls A) cs_empty = cs) by reflexivity.
  rewrite E1, E0 in PP. fold mu mfa in PP, P1, P4. rewrite EMU in PP, R1, R10. rewrite EMF in PP, R4, R11.
  assert (M8 : mu mod 8 = 0).
  { unfold kUserMapSize in P1. destruct (proj1 (Z.mod_divide mu (2 ^ 18) ltac:(clear; lia)) P1) as [q Hq]. rewrite Hq. replace (q * 2 ^ 18) with (q * 32768 * 8) by (clear; lia). apply Z_mod_mult. }
  assert (F8 : mfa mod 8 = 0).
  { unfold kFreeArrayMapSize in P4. destruct (proj1 (Z.mod_divide mfa (2 ^ 18) ltac:(clear; lia)) P4) as [q Hq]. rewrite Hq. replace (q * 2 ^ 18) with (q * 32768 * 8) by (clear; lia). apply Z_mod_mult. }
  specialize (PP ltac:(intros c' Hc' Hne; unfold refillA; cbn [aa_cls]; apply nth_list_upd_other; pose proof P_c as C1; clear -C1 Hc' Hne; lia) M8).
  destruct (mfa <? 4 * (nf + new)) eqn:E.
  - specialize (PP ltac:(rewrite Z.add_mod, M8 by (clear; lia); reflexivity) ltac:(clear -R10; lia) F8 ltac:(rewrite Z.add_mod, F8 by (clear; lia); reflexivity) ltac:(clear -R11; lia)).
    replace (mu + 262144 - mu) with 262144 in PP by (clear; lia). replace (mfa + 262144 - mfa) with 262144 in PP by (clear; lia). change (262144 / 8) with 32768 in PP. clear -PP. lia.
  - specialize (PP ltac:(rewrite Z.add_mod, M8 by (clear; lia); reflexivity) ltac:(clear -R10; lia) F8 F8 ltac:(clear -R11; lia)).
    replace (mu + 262144 - mu) with 262144 in PP by (clear; lia). replace (mfa - mfa) with 0 in PP by (clear; lia). change (262144 / 8) with 32768 in PP. change (0 / 8) with 0 in PP. clear -PP. lia.
Qed.

Lemma pop_credit : ltac2:(tb__ "0|2|
S0S5S6Z48000M0S10S4L_;SaVmfa;S7Z4S6Vnf;Vnew;A2A2A2G0Z0X10x2A2S31VA;A1M1A2S0S5S6S41Vmd0;Vtp0;A2G1A2S37A2S1S4S40S3fVmd0;A1A1S37A3A2A2").
Proof.
  pose proof pop_credit_eq as EQ. pose proof (prim_credit_nonneg (refillA A c)) as NN.
  pose proof HE as (_ & HA & _ & _ & HBud & Hnv & _). fold nv in HBud.
  destruct (AInvA_credit A rb tp0 md0 HA) as (CR & VL).
  unfold budget_ok_alloc, limit_ok_alloc in HBud. destruct HBud as (LO & _). unfold budget_bound in CR.
  pose proof (acost_mono (aa_V A) (aa_V A + nv) ltac:(clear -Hnv; lia)) as AM. unfold BETA_M in *.
  pose proof HA as (_ & _ & _ & _ & HMI & _). destruct HMI as (_ & _ & _ & _ & K0 & _).
  split; [clear -EQ NN; lia|]. split; [clear -CR LO AM K0; lia | exact VL].
Qed.

Lemma pop_headroom : ltac2:(tb__ "0|6|
S23S12S21Q40A1A1S3eS2dVA;Vrb;Vtp0;Vmd0;R3R2R1A7SdS42R2R3A2SbS31VA;A1S6S6S10S4L_;M0S24S2eR4A1M1A1Z40000M2Z0M3X10x2G0S24S27R4A1M4A1G2G3X10x2A2S7Z1000S6G0S2aG1A1Z8M5G3X10x2G0S2aG4A1G5G3X10x2A2A2A2A2A2F_;Fmd;Ftp;Fph;").
Proof.
  intros ph tp md HM. destruct pop_credit as (_ & CR & VL).
  unfold mlink in HM. cbn zeta in HM. destruct HM as (_ & _ & M3 & _ & _ & _ & tp1 & _ & _ & _ & M10).
  unfold headroom. rewrite M3, VL. unfold kUserMapSize, kFreeArrayMapSize in M10.
  destruct (committed (ph_u ph)), (committed (ph_f ph)), (revealedp (ph_u ph)), (revealedp (ph_f ph)); clear -CR M10; lia.
Qed.

Lemma pop_geo : ltac2:(tb__ "0|9|
S0S0S5Z1M0Vc;A2S5Vc;Z1eA2A2S0S0S5Z20VS;A2S5VS;Z10000A2A2S0S0S5Z0M1Vau;A2S5Vau;Vmu;A2A2S0S5Vmu;Zdffc0000A2S0S0S5Z4M2Vnew;A2S5Vnew;Z2001A2A2S0S0S5G0Vk;A2S5Vk;Z8A2A2S0S5Vk;Vnew;A2S0S5G1Vnf;A2S0S5S7G2Vnf;A2Vmfa;A2S0S5Vmfa;Z1ffc0000A2S0S1S4SeVmfa;Z40000A2G1A3S0S5Z100080000000S4bS43VA;A1M3A1M4A2S0S5S6S6G4Z2000000000A2Z1000M5A2M6Z7fffff800000A2S0S1S4S22VA;Vrb;A2S6S6G4S7Vc;Z100000000A2A2Ze0000000A2A3S0S5G5S4cG3A1M7A2S0S2S5S6G7G5A2M8G4A2S5G6G7A2A2S2S5G8Z7fff7000A2S5Z10007fff8000G7A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  destruct (new_nums A rb CF PF) as (N1 & N2 & N3 & N4 & N5 & _ & _ & N8 & N9 & N10 & N11 & _). cbn zeta in N1, N2, N3, N4, N5, N8, N9, N10, N11.
  unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((_ & C1 & _) & (K1 & _) & _ & _ & _ & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  assert (FAr : FAb A rb = ag_spacebeg (aa_geom A) + c * 4294967296 + 3758096384).
  { unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. clear; lia. }
  repeat (split; [first [assumption | exact K1 | clear -G14 TG; lia]|]). exact TB.
Qed.

Lemma old_cell_off : ltac2:(tb__ "0|1|
S23S4S5S28R2A1Vnew;A2S5S29R3A1Z10A2S0S5S22VA;Vrb;A2M0R3A2S9R3S6G0S7Z4Vnf;A2A2A2A2S3S30VA;Vrb;R5R4A4A1F_;F_;F_;Fz;Fph;").
Proof.
  intros ph z HFL HPO Hz HZ.
  destruct pop_geo as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & G13 & G14 & FAr & T1 & PS1 & TB).
  unfold zoneR in HZ. unfold gh_nf in HZ. fold nv c cs nf new in HZ.
  unfold U0, F0, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize, kFreeArrayMapSize, region_info, kRegionInfoStride, PCE in HZ. fold nv c cs mu mfa in HZ.
  rewrite kSpaceSize_val in HZ. rewrite FAr in Hz, HZ.
  assert (SHB : forall x, 0 <= x <= 140737479966720 -> 2147450880 <= Sh x /\ Sh x + 32768 <= 17594333495296 + 32768) by (intros x Hx; unfold Sh, SHADOW_OFF; clear -Hx; lia).
  pose proof (SHB (ag_spacebeg (aa_geom A) + c * 2 ^ 32 + mu) ltac:(clear -C1 G13 G14 AU0 MU1; lia)) as B1.
  pose proof (SHB (ag_spacebeg (aa_geom A) + c * 2 ^ 32 + (2 ^ 32 - 2 ^ 29) + mfa) ltac:(clear -C1 G13 G14 NF0 MF1 MF2; lia)) as B2.
  assert (B1' : Sh (ag_spacebeg (aa_geom A) + c * 2 ^ 32 + mu) + 32768 <= 17594333495296).
  { unfold Sh, SHADOW_OFF. clear -C1 G13 G14 AU0 MU1. lia. }
  assert (B2' : Sh (ag_spacebeg (aa_geom A) + c * 2 ^ 32 + (2 ^ 32 - 2 ^ 29) + mfa) + 32768 <= 17594333495296).
  { unfold Sh, SHADOW_OFF. clear -C1 G13 G14 NF0 MF1 MF2. lia. }
  destruct HZ as [[_ X]|[[_ X]|[[_ X]|[[_ X]|[[X _]|[X|[[_ X]|[_ X]]]]]]]]; clear -X Hz C1 AU0 MU1 NF0 MF1 MF2 G13 G14 T1 PS1 TB B1' B2' HFL HPO N4; lia.
Qed.

Lemma P_HSRC : ltac2:(tb__ "0|1|
S23S51S1S4S28R2A1Vnew;A3S5S29R3A1Z10A2S2bVA;Vrb;R4S52S3dS1bVrb;A1A2R3A5S4S0S5Z0M0R1A2S9R1S8S11S4VfP;A2A1A2A2S53R6S54S6S22VA;Vrb;A2S7Z4R2A2A2U4S55S4ScR2A1VfP;G0A4A3A2F_;Fidx;F_;F_;F_;Fm;Fph;").
Proof.
  intros ph m HFL HPO (L1 & _ & L3 & _) idx Hidx.
  destruct entry_pure as (HP & Hc0 & NP & RM). pose proof P_csR as (_ & _ & _ & _ & _ & _ & LP & _). cbn zeta in LP. rewrite LP in Hidx.
  destruct pop_geo as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & _).
  destruct (Z_lt_dec idx nf) as [OLD|NEW].
  - unfold fP. rewrite (P_nth_old c cs (Z.to_nat idx)) by (fold nf in OLD; unfold nf in OLD; clear -OLD Hidx; lia).
    eapply cell_ok_agree_range; [|exact (proj1 (entry_fa _ _ _ _ _ _ _ HE) idx ltac:(fold nv c cs nf; clear -OLD Hidx; lia))].
    cbn [c_addr c_w]. change (Z.of_nat 4) with 4. intros z Hz. apply L1. apply (old_cell_off ph z ltac:(rewrite HFL; clear; lia) HPO). clear -Hz OLD Hidx. lia.
  - set (j := nf + new - 1 - idx). assert (Hj : 0 <= j < new) by (unfold j; clear -NEW Hidx; lia).
    pose proof (L3 j ltac:(rewrite HFL; exact Hj)) as CE. unfold gh_nf in CE. fold nv c cs nf new au S in CE.
    replace (nf + new - 1 - j) with idx in CE by (unfold j; clear; lia).
    unfold fP. replace (Z.to_nat idx) with (Z.to_nat (Z.of_nat (length (cs_free_array cs)) + newZ c cs - 1 - j)) by (rewrite P_newZ; fold nf; unfold j; clear -Hidx; lia).
    rewrite (P_nth_new c cs j ltac:(rewrite P_newZ; exact Hj)). fold au S. exact CE.
Qed.

Lemma P_HDEF : ltac2:(tb__ "0|4|
S23S51S2S1S10S2fS27R2A1A1S17A3S5S7Z4M0S6Vnf;Vnew;A2A2M1Vmfa;A2A2S2bVA;Vrb;R3S52S3dS1bVrb;A1A2R2A5S4S0S5S6S22VA;Vrb;A2M2S7G0Vnf;A2A2R1A2S9R1S6G2G1A2A2A2S3S1S16S21Q8A1M3A1R5R2A1S13G3A1A3A1F_;Fz;F_;F_;Fm;Fph;").
Proof.
  intros ph m HARM (L1 & L2 & _) z Hz.
  destruct pop_geo as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & G13 & G14 & FAr & _).
  assert (ZD : zoneR A rb ph z \/ ~ zoneR A rb ph z).
  { unfold zoneR. destruct (revealedp (ph_u ph)), (releasedp (ph_u ph)), (revealedp (ph_f ph)), (releasedp (ph_f ph)), (ph_cnt ph), (ph_ri ph); clear; lia. }
  destruct ZD as [ZI|ZO]; [exact (L2 z ZI)|]. rewrite (L1 z ZO).

  assert (LT : z < FAb A rb + mfa).
  { destruct (Z_lt_dec z (FAb A rb + mfa)) as [X|X]; [exact X|]. exfalso. destruct HARM as [REL|FIT]; [|clear -Hz X FIT; lia].
    apply ZO. unfold zoneR. right; right; right; left. split; [exact REL|]. unfold F0, kFreeArrayMapSize. fold nv c cs mfa. unfold FAb in Hz, X. fold nv c in Hz, X. clear -Hz X N4 MF1. lia. }
  destruct HE as (_ & HA & _). pose proof HA as (HG & _ & _ & HRest & _). destruct HRest as (_ & _ & Hprim & _). destruct Hprim as (_ & _ & _ & P4). specialize (P4 c C1).
  unfold class_repr in P4. change (nthZ (aa_cls A) c cs_empty) with cs in P4.
  destruct P4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PR & _).
  destruct (PR z ltac:(unfold FAb in Hz, LT; fold nv c in Hz, LT; fold nf mfa; clear -Hz LT; lia)) as [b Hb].
  rewrite maskv_out in Hb; [change (view segs (rm rb) z = Some b) in Hb; rewrite Hb; discriminate|].
  apply fs_footb_space; [exact HG|]. rewrite kSpaceSize_val. rewrite FAr in Hz. clear -Hz C1 NF0 N4 MF1 MF2 G13 G14. lia.
Qed.

Definition e_srcP : sv := ltac2:(tb__ "0|0|
S18S33S3cS18S35S18S34S18S33S3aS38A3S39A3S1cZ2A1A3A3").
Definition e16P : sv := ltac2:(tb__ "0|0|
S18S34S18S33S3aS38A3S39A3").
Definition e32P : sv := ltac2:(tb__ "0|0|
S18S33S3bS1dS36S38S1eS57A1A3A3").
Definition e48P : sv := SAlu ALU_ADD vMU (SLit 262144).
Definition e24M : sv := SAlu ALU_ADD vMFA (SLit 262144).

Lemma P_HSRCP : ltac2:(tb__ "0|1|
S1aS25Vrb;R1A2S26VA;Vrb;R2A3S1S21Q40M0A1S19R3S61A2S20G0S6S22VA;Vrb;A2S7Z4SbS8S11S4VfP;A2A1Vk;A2A2A2A2A3F_;F_;Fr;").
Proof.
  intros r HFz HGh. pose proof P_csR as (_ & _ & _ & _ & _ & _ & LP & _). cbn zeta in LP. rewrite LP.
  destruct pop_geo as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & G13 & G14 & FAr & _).
  destruct HGh as (_ & Q221 & _ & _ & _ & _ & Q226 & Q227 & Q228 & _). unfold gh_nf in Q221. fold nv c cs nf in Q221. fold nv c k in Q227. fold new in Q228.
  unfold e_srcP, vFA, vNF, vNEW, vK. cbn [eval]. rewrite Q221, Q226, Q227, Q228. apply bv_eq.
  rewrite add_val, sll_val, sub_val, add_val. rewrite !u64_lit by (rewrite ?FAr; clear -C1 G13 G14 NF0 MF1 MF2 N4 K1; lia).
  change (2 mod 64) with 2. rewrite (Z.mod_small (nf + new)) by (clear -NF0 MF1 MF2 N4; lia).
  rewrite (Z.mod_small (nf + new - k)) by (clear -NF0 MF1 MF2 N4 KN K1; lia).
  rewrite Z.shiftl_mul_pow2 by (clear; lia). rewrite (Z.mod_small (_ * 2 ^ 2)) by (clear -NF0 MF1 MF2 N4 KN K1; lia).
  rewrite Z.mod_small by (rewrite FAr; clear -C1 G13 G14 NF0 MF1 MF2 N4 KN K1; lia). clear; lia.
Qed.

Lemma P_HRIv : ltac2:(tb__ "0|2|
S1fS1aS25Vrb;R1A2S26VA;Vrb;R2A3S1S21Q40M0A1M1S19R3R4A2S20G0S10S4L_;SaVmfa;S7Z4S6Vnf;Vnew;A2A2A2S6Vmfa;Z40000A2Vmfa;X10x2A2A3S4eVc;Vcs;A2S44S0S1G1S19R5S5eA2S20G0S8S11S4S47R1A1A2A1A2A3S0S1G1S19R5R6A2S20G0S48R1A1A2A3S0S1G1S19R5S5fA2S20G0S45R1A1A2A3S1G1S19R5S60A2S20G0S49R1A1A2A3A2A2A2TcsR;F_;F_;F_;Fr;Fe24;").
Proof.
  intros e24 r HFz HGh E24 csR. pose proof P_csR as (_ & _ & X3 & X5 & X6 & X7 & _). cbn zeta in X3, X5, X6, X7. fold csR in X3, X5, X6, X7.
  destruct pop_geo as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & G13 & G14 & FAr & _).
  pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG. destruct RG as (_ & E148 & _). fold nv c S in E148.
  destruct HGh as (_ & Q221 & _ & Q223 & Q224 & _ & _ & Q227 & Q228 & _). unfold gh_nf in Q221. fold nv c cs nf in Q221. fold nv c cs au in Q223. fold nv c cs mu in Q224. fold nv c k in Q227. fold new in Q228.
  assert (NS : 0 <= new * S <= 3758096384) by (pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF; destruct (new_nums A rb CF PF) as (_ & _ & _ & _ & _ & M6 & _); cbn zeta in M6; fold nv c cs in M6; fold S au mu new in M6; clear -M6 AU0 MU1 N4 S1; nia).
  rewrite X3, X5, X6, X7. split; [|split; [exact E24|split]].
  - unfold e16P, vNF, vNEW, vK. cbn [eval]. rewrite Q221, Q227, Q228. apply bv_eq. rewrite sub_val, add_val, !u64_lit by (clear -NF0 MF1 MF2 N4 K1 KN; lia).
    rewrite (Z.mod_small (nf + new)) by (clear -NF0 MF1 MF2 N4; lia). rewrite Z.mod_small by (clear -NF0 MF1 MF2 N4 KN K1; lia). reflexivity.
  - unfold e32P, vAU, vNEW, V_SIZE. cbn [eval]. rewrite Q223, Q228, E148. apply bv_eq. rewrite add_val, mul_val, !u64_lit by (clear -AU0 MU1 N4 S1 NS; lia).
    rewrite (Z.mod_small (new * S)) by (clear -NS; lia). rewrite Z.mod_small by (clear -NS AU0 MU1; lia). reflexivity.
  - unfold e48P, vMU. cbn [eval]. rewrite Q224. apply bv_eq. rewrite add_val, !u64_lit by (clear -AU0 MU1; lia). rewrite Z.mod_small by (clear -AU0 MU1; lia). reflexivity.
Qed.
End ARMP.
End SpineCallocR14.

(* [comment removed for export] *)
Module SpineCallocSecE4.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rm"; "rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "DG"; "aa_sec"; "sec_chunk"; "aa_Km"; "aa_geom"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@Corelib.Init.Datatypes"; "list"; "prod"; "pair"; "None"; "length"; "option"; "false"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "secmapsize"; "stopJ_stable"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "mem_keptA"; "@Corelib.Init.Logic"; "eq"; "not"; "and"; "False"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "div"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS"; "AXK"; "dlink"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "dblocks"; "dfp_static"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3"; "clsP"; "JGs"; "JGsC"; "slink"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts"; "PFc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2"; "IMG_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4"; "slink4"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertCallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ip.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ip.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.SpineCallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.RebuildN.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import MmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocSec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ir.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CDepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.CertCallocSS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.CertCallocSN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocSec OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.SpineCallocSec2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ir.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SecRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jx.SpineCallocSec4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CDepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k5.CDepotCallS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k6.CSecLinks OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k4.SpineCallocSecOK.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import CallocBase2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ii.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocI2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ii.CallocPosts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.CallocBase.
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
    destruct HJ as [HJ _]. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jp.SpineCallocSec3.JGs in HJ. cbn zeta in HJ. destruct HJ as (_ & _ & _ & HPD & _).
    destruct HPD as (_ & _ & _ & PDI & _). destruct PDI as (_ & _ & _ & _ & PDB).
    unfold clsP. destruct PDB as [X|X]; [right; exact X | left; exact X].
  - intros [X|X]; [exact (HH X) | exact (HL X)].
Qed.
End OKE.
End SpineCallocSecE4.

(* [comment removed for export] *)
Module DrainI1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "true"; "nil"; "bool"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "la_state"; "ax_S"; "leafA"; "sym_runA"; "ax_X"; "entailsA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "ss_next"; "sprop"; "ss_objs"; "ss_lenient"; "swf"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k2.DrainI1"; "N"; "FUEL"; "l1_0"; "l2_0"; "l2_1"; "l31_2"; "l30_0"; "l30_1"; "l30_2"; "l31_0"; "l31_1"; "cr_00"; "cr_01"; "cr_02"; "cr_10"; "cr_11"; "cr_12"; "s_00"; "s_01"; "s_02"; "s_10"; "s_11"; "s_12"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF"; "rstD"; "O_riX"; "ri_hasD"; "leaf_ok"; "mid_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "L_dh_f"; "NXD"; "O_cntD"; "O_dstD"; "dst_cells"; "Pre_dh_f"; "JD"; "JLD"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "nobj"; "vMFA"; "ri_e"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition N : Z := 1.
Definition FUEL : nat := 6000%nat.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3f124S3S32A1A3S3eS1bA1S2A5").
Local Strategy expand [R_1__R].
Definition l1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition l1_0 := Eval vm_compute in (nth 0 l1 (mkLeafA (Pre_dh_f N) RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3f124S3S32A1A3S3eS1bA1S2A5S7G0S1SeS1dS3SeA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [l1_0]). Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0S4S18SdS3eS1bA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Definition R_a__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3f5d4S3S32A1A3S33ScS1dA1U8A2S2A5").
Local Strategy expand [R_a__R].
Definition l2 := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_a__R).
Definition l2_0 := Eval vm_compute in (nth 0 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Definition l2_1 := Eval vm_compute in (nth 1 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Definition R_b0__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1eA1U16A2S2A5").
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
S0S8S5SeA1M0A1SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1eA1U16A2S2A5S7G0S1SeS21S1SeS22S1SeS23S3SeA1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b0__R <: R_b0__R = Some [l30_0; l30_1; l30_2]). Qed.
Lemma m_b0 : ltac2:(tb__ "0|0|
S37S1cU16S1S32Z3ef78S3S32A1A3S36S1bA1ScS1eA1A5").
Proof.
  split; [exact W_b0|]. split; [exact D_b0|]. split; [exact NXe_b0|]. split; [exact LN_b0|]. split; [exact NL_b0|].
  exists [l30_0; l30_1; l30_2]. split; [exact R_b0|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_00 | exact k_01 | exact k_02 | destruct HIn].
Qed.
Definition R_b1__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1fA1U16A2S2A5").
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
S0S8S5SeA1M0A1SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1fA1U16A2S2A5S7G0S1SeS24S1SeS25S1SeS20S3SeA1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b1__R <: R_b1__R = Some [l31_0; l31_1; l31_2]). Qed.
Lemma m_b1 : ltac2:(tb__ "0|0|
S37S1cU16S1S32Z3ef78S3S32A1A3S36S1bA1ScS1fA1A5").
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
S0S8S5SeA1M0A1SfS38S1cS1S32Z3f5d4S3S32A1A3S33ScS1dA1U8A2S2A5S7G0S1SeS1eS1SeS1fS3SeA1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_a__R <: R_a__R = Some [l2_0; l2_1]). Qed.
Lemma m_a : ltac2:(tb__ "0|1|
S37S1cU8S1S32Z3f5d4S3S32A1M0A3S37S1cU16S1S32Z3ef78G0A3S36S1bA1A4ScS1dA1A5").
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
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "true"; "nil"; "bool"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "la_state"; "ax_S"; "leafA"; "sym_runA"; "ax_X"; "entailsA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "ss_next"; "sprop"; "ss_objs"; "ss_lenient"; "swf"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k2.DrainI2"; "N"; "FUEL"; "l1_0"; "l2_0"; "l2_1"; "l31_2"; "l30_0"; "l30_1"; "l30_2"; "l31_0"; "l31_1"; "cr_00"; "cr_01"; "cr_02"; "cr_10"; "cr_11"; "cr_12"; "s_00"; "s_01"; "s_02"; "s_10"; "s_11"; "s_12"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF"; "rstD"; "O_riX"; "ri_hasD"; "leaf_ok"; "mid_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "L_dh_f"; "NXD"; "O_cntD"; "O_dstD"; "dst_cells"; "Pre_dh_f"; "JD"; "JLD"; "@Corelib.Init.Nat"; "sub"; "@Corelib.Lists.ListDef"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "nobj"; "vMFA"; "ri_e"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@stdpp.bitvector.definitions"; "bv"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition N : Z := 2.
Definition FUEL : nat := 6000%nat.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3f124S3S32A1A3S3eS1bA1S2A5").
Local Strategy expand [R_1__R].
Definition l1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition l1_0 := Eval vm_compute in (nth 0 l1 (mkLeafA (Pre_dh_f N) RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0S8S5SeA1M0A1SfS38S1cS1S32Z3f124S3S32A1A3S3eS1bA1S2A5S7G0S1SeS1dS3SeA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [l1_0]). Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0S4S18SdS3eS1bA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Definition R_a__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3f5d4S3S32A1A3S33ScS1dA1U8A2S2A5").
Local Strategy expand [R_a__R].
Definition l2 := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_a__R).
Definition l2_0 := Eval vm_compute in (nth 0 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Definition l2_1 := Eval vm_compute in (nth 1 l2 (mkLeafA (rstD (la_state l1_0) 8) RsCut)).
Definition R_b0__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1eA1U16A2S2A5").
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
S0S8S5SeA1M0A1SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1eA1U16A2S2A5S7G0S1SeS21S1SeS22S1SeS23S3SeA1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b0__R <: R_b0__R = Some [l30_0; l30_1; l30_2]). Qed.
Lemma m_b0 : ltac2:(tb__ "0|0|
S37S1cU16S1S32Z3ef78S3S32A1A3S36S1bA1ScS1eA1A5").
Proof.
  split; [exact W_b0|]. split; [exact D_b0|]. split; [exact NXe_b0|]. split; [exact LN_b0|]. split; [exact NL_b0|].
  exists [l30_0; l30_1; l30_2]. split; [exact R_b0|]. intros L' HIn. repeat (destruct HIn as [<-|HIn]); [exact k_00 | exact k_01 | exact k_02 | destruct HIn].
Qed.
Definition R_b1__R : option (list leafA) := ltac2:(tb__ "0|0|
SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1fA1U16A2S2A5").
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
S0S8S5SeA1M0A1SfS38S1cS1S32Z3ef78S3S32A1A3S33ScS1fA1U16A2S2A5S7G0S1SeS24S1SeS25S1SeS20S3SeA1A3A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_b1__R <: R_b1__R = Some [l31_0; l31_1; l31_2]). Qed.
Lemma m_b1 : ltac2:(tb__ "0|0|
S37S1cU16S1S32Z3ef78S3S32A1A3S36S1bA1ScS1fA1A5").
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
S0S8S5SeA1M0A1SfS38S1cS1S32Z3f5d4S3S32A1A3S33ScS1dA1U8A2S2A5S7G0S1SeS1eS1SeS1fS3SeA1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_a__R <: R_a__R = Some [l2_0; l2_1]). Qed.
Lemma m_a : ltac2:(tb__ "0|1|
S37S1cU8S1S32Z3f5d4S3S32A1M0A3S37S1cU16S1S32Z3ef78G0A3S36S1bA1A4ScS1dA1A5").
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
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "iff"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "lt"; "of_nat"; "modulo"; "ge"; "sub"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k2.DrainG1.DG"; "F0d"; "mlinkG"; "zoneG"; "rlinkG"; "JDg"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "bool"; "list"; "nat"; "app"; "true"; "length"; "option"; "prod"; "None"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "vm_limit"; "alloc_top"; "m_vm_lazy"; "vm_maps"; "vm_noaccess"; "vm_reserved"; "VmMaps"; "maps_subtract"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "eval"; "rm"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "free_array"; "max_count"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ"; "revealedp"; "committed"; "shpage"; "releasedp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF"; "frozenD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "prim_credit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.RebuildRM"; "sub1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "cls_pure"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "model_ivs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "beg2"; "ri_e"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel"; "drainA"; "drain_cs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS"; "dfacts"; "dst_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Kc_ok"; "top_high"; "tp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "live_ids"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "AInvQ"; "rigidQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "budget_boundD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "budget_bound"; "cs_cache"; "cs_mapped_free_array"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR"; "JK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "q_ids"; "qall"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP PrimCredit PrimCreditLaws SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.RebuildRM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jh.RebuildD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jw.DrainF.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.

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
S0S0S6Z1M0Vc;A2S6Vc;Z1eA2A2S0S1SeS42Vc;A1Vn;A3S0S0S6G0Vn;A2S6Vn;Z8A2A2S0S1SeS37Vc;A1S8Z2Vn;A2A3S0S6Z1000M1VT;A2S0S6S7VT;G1A2M2S58VG;A1M3A2S0S6G3Z7fffff800000A2S0S3S6G2Z10000A2S6Z643000VT;A2A2S0S6Z10007fff8000M4VSB;A2S0S6S7S7VSB;Z2000000000A2G1A2M5G3A2S0S3S6G2VSB;A2S6G5VT;A2A2S0S3S6G2Z7fff7000A2S6G4VT;A2A2S0S6Z0M6Vnf;A2S0S6S8Z4M7Vnf;A2Vmfa;A2S0S9Vmfa;S8G7S7Vnf;Vn;A2A2A2S0S1SeSbVmfa;Z40000M8A2G6A3S6S7Vmfa;G8A2Z20000000A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
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

