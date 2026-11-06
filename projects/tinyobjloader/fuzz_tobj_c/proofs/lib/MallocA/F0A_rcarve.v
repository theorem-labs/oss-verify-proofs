(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "false"; "bool"; "true"; "list"; "prod"; "cons"; "andb"; "nil"; "orb"; "app"; "Some"; "nat"; "option"; "negb"; "pair"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "rw"; "sprop"; "sobj"; "ss_next"; "obj_range"; "ss_lenient"; "sprop_eqb"; "ss_facts"; "ss_objs"; "swf"; "pairwise_disjoint"; "rl"; "ob_base"; "ob_hi"; "ob_lo"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "liftKA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states"; "qvar"; "QA"; "FUELF"; "leaves_at"; "O_blkN"; "O_sh"; "QBe"; "QBf"; "entsF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone"; "same_rng"; "rng_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst"; "NV"; "NFS"; "NRT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "free_depth"; "F_depth"; "Wcan"; "chain_pre"; "KcA"; "Kc_ok"; "O_got"; "O_rtc"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rcarve"; "NV3"; "tr_okb"; "NVH"; "base_on"; "cchkb"; "P3"; "Pb"; "cchkb_sound"; "cpins"; "lowwinb"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "qbatch"; "aa_geom"; "aa_live"; "aa_q_thread"; "ag_ctx"; "ag_spacebeg"; "ag_thread"; "ageom"; "qb_addr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS"; "RF_ENT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "RETQ"; "leaf"; "runA"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "opp"; "div"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot"; "isnil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain"; "rq_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok"; "cnt24"; "lastq"; "top24"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ax.F0A_pins"; "spec_on"; "sv_on"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d6.F0A_refill"; "ax_carve"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "max_count"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymSoundW SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA CompleteA EntailA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull SpineMallocS4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_rebuild.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_rebuild.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_skel F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require af.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ax.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require dy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require d6.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.af.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.F0A_dzone OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c6.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ax.F0A_pins OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.dy.F0A_skelC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.d6.F0A_refill.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition NV3 : list carve_spec := skipn 1 (NV QBe).
Definition NVH (q : qvar) : list carve_spec := ltac2:(tb__ "0|0|
S38S3S2eA1Lq;Vq;S47S39A1S5eS2eU1S47S3eA1A3S5eS2eU2S47S3fA1A3X38x3").
Lemma NV_split : ltac2:(tb__ "0|0|
S38S11SfS38R1S39A3A1SfS3S2eA1S47R2A1S9S2eS56R2A1S54A3A3F_;Fq;").
Proof. intros [| |] H; [exfalso; exact (H eq_refl) | reflexivity | reflexivity]. Qed.

Definition lowwinb (o : sobj) : bool := ltac2:(tb__ "0|14|
S15S1Lx;M0S23Vo;A1S13S0Lz;M1S12S0Li;S30S15S15S30S1Lop;R3S15S1La;R2G1S12S12S1Li;R1S12S0Lp;S12S12S1Lp;R1S12S12S1Lp0;R1S12S0Lp1;S12S12S1Lp1;R1S12S0Lp2;M2G2S15S1Lb;R5S13G0S25Vo;A1G1S12S0Li0;M3S30S15S15S30S1Lop0;R3S15S1La0;R2G1S12S12S1Li0;R1S12S12S1Lp2;R1S12S12S1Lp3;R1S12S12S1Lp4;R1S12S0Lp5;M4G4S15S1Lb0;R5S13G0S24Vo;A1S13S13S1Lz;R1S6S6S72R2S70RaA1A2S6fS70S4aA1RaA2A2S6fRaZ0A2A2G4G4X13x3Lz;S12S0Li1;M5S30S15S15S0Lb1;La1;M6Lop1;M7G7S31G6Lop1;M8G8S1S14S15S0La1;Lw;Lsgn;M9S12S15S13S0Lk;MaLi1;Ll;MbX15x8Lc';G5G7G7G8G8G9GbX15x8X12x3Lp4;S12S0Lp4;S0X12x3Lp3;S12S0Lp3;S0X12x3Lp2;G2S0X12x3Li0;G7G7G8G8G9S12S15GaLi0;Ll;McX15x8S0S0S0S0S0S0S0S0S0X30xaLb0;La0;Lop0;S30S15S15S0Lb0;La0;MdLop0;MeS31GdLop0;MfGfS1S14S15S0La0;Lw;Lsgn;M10GcX15x8Lc;G3GeGeGfGfG10GcX15x8X12x3Lp1;S0X12x3Lp0;S12S0Lp0;S0X12x3Lp;S0X12x3Li;GeGeGfGfG10S12S15GaLi;Ll;M11X15x8S0S0S0S0S0S0S0S0S0X30xaLb;La;Lop;S30S15S15S0Lb;La;M12Lop;S31G12Lop;M13G13S1S14S15S0La;Lw;Lsgn;G11X15x8").
Definition tr_okb (nW : nat) (q : qvar) (o : sobj) : bool := ltac2:(tb__ "0|0|
S8S8S8S8S8S8S29S19S45Vo;A1S5fS2eS19S2fS9S2eS49S56Vq;A1A3A4A3S45Vo;S3dA2A2S45Vo;S3cA2A2S74VnW;Vo;A2A2S5dVo;A1A2S45Vo;S50A2A2S45Vo;S51A2A2").

Definition Pb (q : qvar) (i : positive) : bool :=
  existsb (Pos.eqb i) (([12; 127; 130; 151; 152; 155]%positive : list positive) ++ (match q with QBf => ([122]%positive : list positive) | _ => [] end)).
Definition P3 (i : positive) : bool := ltac2:(tb__ "0|0|
S29S12S53Vi;A1S5S12P7fS5S12P80S5S12P81S5S12P82S5S12P97S5S12P9bS7S12A1A3A3A3A3A3A3A3").
Definition base_on (P : positive -> bool) (k : carve_spec) : bool := ltac2:(tb__ "0|3|
S4S4S4S15S13A2M0S13A2M1S3S4S4S13SbA2S15A2A1M2A2S1Lk;Vk;G1G2G1S1Lp;R2G0S13G0S1Lp0;R2S15S13S7aVP;R2A2Lz0;Lb;X4x1Lz;Lp0;X4x1Ll;Lp;X4x1").
Lemma NFS_base_on : ltac2:(tb__ "0|0|
S38S11SfS38R1S39A3A1SfS1S28S2eS57S5aR2A1A1S48R2A1A3S2A3F_;Fq;").
Proof. intros [| |] H; [exfalso; exact (H eq_refl) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. Qed.
Lemma NV3_on : ltac2:(tb__ "0|0|
SfS1S28S2eS79S59A1S54A3S2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma range_on : ltac2:(tb__ "0|1|
S12S1F_;S16S16S12SfS1R4R1A1S2A3SfS27Q40A1S17R3R2A2S17R4R2A2A3F_;Fi;S12SfS3S27Q8A1A1S22R3R1A2S22R4R1A2A3Fl;S2eSfS1S57R6R1A2S2A3SfS4S13S13A2S1bR5S2fR2A1M0A2S1bR6G0A2A3F_;Fk;F_;F_;Fr2;Fr1;FP;").
Proof.
  intros P r1 r2 HW HL [[[base lo] hi] cs] Hb. unfold base_on in Hb. cbn [carve_obj]. unfold carved, obj_range, obj_lo_of, obj_hi_of, soff. cbn [ob_base ob_lo ob_hi eval].
  rewrite (eval_on P r1 r2 HW HL base Hb). reflexivity.
Qed.

Lemma pd_on_ranges : ltac2:(tb__ "0|0|
S16S16S3S19A1S19S2aS19R1R2A3SfS4S13S13A2S1bR5R2A2S1bR4R2A2A3F_;Fo;S21R3R2A2S21R5R3A2F_;F_;Fl;Fr1;Fr2;").
Proof.
  intros r2 r1 l. induction l as [|o t IH]; intros HR Hpd; [exact I|]. cbn [SymState.pairwise_disjoint] in Hpd |- *. destruct Hpd as [Hf Hpd].
  split; [|apply IH; [intros o' Ho'; apply HR; right; exact Ho' | exact Hpd]].
  apply Forall_forall. intros o' Ho'. rewrite (HR o (or_introl eq_refl)), (HR o' (or_intror Ho')). exact (proj1 (Forall_forall _ _) Hf o' Ho').
Qed.

Definition cpins (q : qvar) (A2 : AA) (p n : Z) (r : valuation) : Prop := ltac2:(tb__ "0|4|
S63VA2;A1S69S10SfS27Q40M0A1M1S17Vr;PcA2S26G0Vp;A2A3S10SfG1S17Vr;PdA2S26G0Vn;A2A3S10SfG1S17Vr;P69A2S26G0S78Vn;A1M2A2A3S10SfG1S17Vr;P6aA2S26G0S71G2Z8A2A2A3S10SfG1S17Vr;P97A2S26G0S68R1A1A2A3S10SfG1S17Vr;P98A2S26G0S66R1A1A2A3S10SfG1S17Vr;P9bA2S26G0S67R1A1A2A3S10SfG1S17Vr;P7fA2S26G0S75VA2;A1A2A3S10SfG1S17Vr;P80A2S26G0S7dZ18M3A1A2A3S10SfG1S17Vr;P81A2S26G0S7cG3A1A2A3S10SfG1S17Vr;P82A2S26G0S77VA2;A1A2A3S11SfS3S62A1S65VA2;A1S7S62A1A3A1SfG1S17Vr;P7aA2S26G0S6aS76VA2;A1A1A2A3F_;A2A2A2A2A2A2A2A2A2A2A2TG;").

Definition cchkb (nW : nat) (q : qvar) (TR TRs : axst) : bool := ltac2:(tb__ "0|3|
S6S73S4S15S15A2S34VTR;A1A2S6S20S32VTRs;A1M0A1S6S28S19S55VnW;Vq;A2S1fS32VTR;A1M1A1M2A3S6S28S19S46S36A1G2A3S6S28S18S18S29S18S1dR1A1S1eG1A1A3Lg;S9S18S4dS4cVnW;A1A1S4bS4aA1A3A3S6S52S36S1aG0A1A2SdS1cG0A1A1A2A2A2A2A2A2").
Lemma cchkb_sound : ltac2:(tb__ "0|3|
SbS38S33S33SfS1S58R4R3R2R1A4S2A3S10SfS3S4S15S15A2M0A1S34R3A1S7G0A1A3S10SfS1S20S32R2A1M1A1S2A3S10SfS1S28S19S55R5R4A2S1fS32R3A1A1M2A3S2A3S10SfS1S28S19S46S36A1G2A3S2A3S10SfS1S28S18S18S29S18S1dR1A1S1eS32R4A1A1A3Lg;S9S18S4dS4cR5A1A1S4bS4aA1A3A3S2A3S10SfS1S52S36S1aG1A1A2S2A3SfS1S1cG1A1S0A3A2A2A2A2A2A2F_;FTRs;FTR;Fq;FnW;").
Proof.
  intros nW q TR TRs H. unfold cchkb in H. do 6 (apply andb_prop in H as [?X H]). apply isnil_sound in X. apply negb_true_iff in H.
  repeat split; assumption.
Qed.

Section S5C.
Variable nW : nat.
Let st : ustop := UStopLe.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables (TM Erf EC : axst) (l5 : list leafA) (XR : list axform).
Hypothesis NX5 : ltac2:(tb__ "0|1|
S10SfS1S52S36S1aS32VTM;A1M0A1A2S2A3SfS1S1cG0A1S0A3A2").
Hypothesis RUN5 : ltac2:(tb__ "0|0|
SfS3S35A1S6eS3aS5S13S6bS7S13A1A3VTM;A3Vl5;A3").
Hypothesis L5 : ltac2:(tb__ "0|0|
S10SfS1S3bVl5;S5S13S6bS7S13A1A3A2S2A3SfS33S6dU0Vl5;A2VErf;A3A2").
Hypothesis AXR : ltac2:(tb__ "0|0|
SfScS33A1S60VErf;VXR;A2SaS33VEC;A2A3").

Theorem f0_s5c : ltac2:(tb__ "0|0|
S41OF_;S61S4eS16S3S27Q40A1A1S44S4fR4A1S2dVsegs;R7S2cR5A1A3S16S43Vsegs;R9S2bVsegs;S37VnW;Vst;S0R8R7R6A6VEC;R1R5A5R4A4FrhoE;S16S43Vsegs;RaS2bVsegs;S37VnW;Vst;S0R9R8R7A6VTM;R1R6A5R5A4FrhoE;F_;F_;F_;FQ;Ftp;Frho1;FKc;FA;Fok;").
Proof.
  intros ok A Kc rho1 tp Q HKc Hok HC rhoE. destruct NX5 as [Na Nb]. destruct L5 as [La Lb].
  pose proof (JF_stable nW st false A Kc rho1 (stopJ_stable_le _) HKc) as HST. pose proof (JF_okf nW st false ok A Kc rho1 Hok) as HOK.
  apply (run_cont1 FUELF [RF_ENT] TM l5 (ss_next (ax_S TM)) Erf Nb eq_refl RUN5 Lb RF_ENT (JF nW st false A Kc rho1) ok rhoE tp Q (leaves_at1 _ _ La) HOK).
  - eapply stableA_mono; [|exact HST]. apply Pos.leb_le. exact Na.
  - intros rhoX HagX.
    eapply triple_conseq; [intros w Hw; exact (SPA_axforms segs _ XR rhoX Erf EC tp w AXR Hw) | intros w Hw; exact Hw | apply HC].
Qed.
Theorem ef0_s5c : ltac2:(tb__ "0|0|
S61S4eS16S3S27Q40A1A1S41OF_;S4fR4A1S16S42Vsegs;S2bVsegs;S37VnW;Vst;S0R7R6R5A6VEC;R1R4A5R3A3FrhoE;S16S42Vsegs;S2bVsegs;S37VnW;Vst;S0R8R7R6A6VTM;R1R5A5R4A3FrhoE;F_;F_;FQ;Ftp;Frho1;FKc;FA;").
Proof.
  intros A Kc rho1 tp Q HKc HC rhoE. destruct NX5 as [Na Nb]. destruct L5 as [La Lb].
  pose proof (JF_stable nW st false A Kc rho1 (stopJ_stable_le _) HKc) as HST.
  apply (run_econt1 FUELF [RF_ENT] TM l5 (ss_next (ax_S TM)) Erf Nb eq_refl RUN5 Lb RF_ENT (JF nW st false A Kc rho1) rhoE tp Q (leaves_at1 _ _ La)).
  - eapply stableA_mono; [|exact HST]. apply Pos.leb_le. exact Na.
  - intros rhoX HagX.
    eapply etriple_conseq; [intros w Hw; exact (SPA_axforms segs _ XR rhoX Erf EC tp w AXR Hw) | intros w Hw; exact Hw | apply HC].
Qed.
End S5C.

Section S5D.
Variable nW : nat. Variable q : qvar.
Let st : ustop := UStopLe.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Hypothesis Hq : q <> QA.
Variables (TR TRs Erq Erq2 TQ : axst) (l5 : list leafA) (XWl : list axform).
Hypothesis HTRs : ltac2:(tb__ "0|0|
SfS33VTRs;S7bVTR;S54S1aS32VTR;A1A1A3A3").
Hypothesis CCHK : ltac2:(tb__ "0|0|
SfS1S58VnW;Vq;VTR;VTRs;A4S2A3").
Hypothesis RUN5 : ltac2:(tb__ "0|0|
SfS3S35A1S6eS3aS5S13S6cS7S13A1A3VTRs;A3Vl5;A3").
Hypothesis L5 : ltac2:(tb__ "0|0|
S10SfS1S3bVl5;S5S13S6cS7S13A1A3A2S2A3SfS33S6dU0Vl5;A2VErq;A3A2").
Hypothesis AXW : ltac2:(tb__ "0|0|
SfScS33A1S60VErq;VXWl;A2SaS33VErq2;A2A3").
Hypothesis ENTQ : ltac2:(tb__ "0|0|
SfS1S40VErq2;VTQ;A2S2A3").
Definition CPARTS := cchkb_sound nW q TR TRs CCHK.

Section SITE.
Variables (A2 : AA) (Kc : KcA) (rho1 : valuation) (p n : Z).
Hypothesis HKc : Kc_ok Kc.
Hypothesis HL : ltac2:(tb__ "0|0|
S2aS4S13S13A2SeS13S13Vp;Vn;A4S64VA2;A1A3").
Hypothesis HCLS : blk_cls p n.
Hypothesis Hii : aa_internal_inited A2 = true.
Hypothesis QC : qcond q A2.
Hypothesis HPIN : ltac2:(tb__ "0|0|
S5cVq;VA2;Vp;Vn;Vrho1;A5").
#[local] Abbreviation G := (aa_geom A2).

Lemma carve3 : ltac2:(tb__ "0|1|
S16S3S27Q40A1A1S41S2bVsegs;S37VnW;Vst;S0VA2;VKc;Vrho1;A6M0VTR;R3R2R1A6S2bVsegs;G0VTRs;R4R3R2A6F_;Fw;Ftp;FrhoX;").
Proof.
  intros rhoX tp w Hw. pose proof CPARTS as (XTR & SWFS & TROK & TRWF & FCH & _ & _).
  destruct w as [tr [ms md]]. pose proof (proj2 Hw) as [Hag HJ]. cbn [w_tr w_cfg cfg_model fst snd] in Hag, HJ.
  destruct HJ as (HA & _ & _ & _ & _ & _ & Htop).
  pose proof (proj1 Hw) as (Hsm & _). unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.

  assert (FIN : forall g, In g (chain_pre W ++ F_depth free_depth) -> holds rhoX g).
  { intros g Hg. pose proof (proj1 (forallb_forall _ _) FCH g Hg) as X. apply existsb_exists in X as (g' & Hg' & E). apply sprop_eqb_sound in E. subst g'.
    exact (proj1 (Forall_forall _ _) HFa g Hg'). }
  assert (Hdep : - 2 ^ 40 <= bv_signed (rw rhoX V_DEPTH) <= - free_depth).
  { assert (D1 : holds rhoX (SPBranch BC_GE (SLit (- free_depth)) (SVar V_DEPTH))) by (apply FIN; apply in_or_app; right; left; reflexivity).
    assert (D2 : holds rhoX (SPBranch BC_GE (SVar V_DEPTH) (SLit (- 2 ^ 40)))) by (apply FIN; apply in_or_app; right; right; left; reflexivity).
    cbn [holds eval branch_taken] in D1, D2. unfold bv_lts in D1, D2. apply negb_true_iff in D1, D2. apply Z.ltb_ge in D1, D2.
    change (bv_signed (Z_to_bv 64 (- free_depth))) with (- free_depth) in D1. change (bv_signed (Z_to_bv 64 (- 2 ^ 40))) with (- 2 ^ 40) in D2. lia. }
  assert (Hch : Forall (holds rhoX) (chain_pre W)) by (apply Forall_forall; intros g Hg; apply FIN; apply in_or_app; left; exact Hg).

  assert (ERW : forall i, (i < GW)%positive -> rw rhoX i = rw rho1 i) by (intros i Hi; symmetry; exact (proj1 Hag i Hi)).
  destruct HPIN as (P12 & P13 & P105 & P106 & P151 & P152 & P155 & P127 & P128 & P129 & P130 & P122).
  pose proof (F0A_rebuild.GEO A2 rhoX tp md 0 0 HA) as (T1' & T2' & SB1 & SB2 & _ & _ & _ & _ & _ & TG & _).
  pose proof (blkF_geom A2 rhoX tp md p n HA HL HCLS) as (B1 & B2 & B3 & B4 & _).
  pose proof (N8_facts n B3) as (N1 & N2 & N3 & N4). unfold blk_geo in B1. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in B1.
  assert (E12u : bv_unsigned (rw rhoX 12%positive) = p) by (rewrite ERW, P12 by (unfold GW; lia); apply u64_lit; lia).
  assert (E13u : bv_unsigned (rw rhoX 13%positive) = n) by (rewrite ERW, P13 by (unfold GW; lia); apply u64_lit; lia).
  destruct (blkF_mem A2 rhoX tp md p n HA HL HCLS) as (t2 & T1x & T2x & HW2 & HL2 & _).
  destruct (junkF_ok A2 rhoX tp md HA) as (jv2 & JV).
  set (rho2 := rhoF_of A2 rhoX p n t2 jv2).
  assert (HLr : forall l, rl rhoX l = rl rho2 l) by (intros l; unfold rho2, rhoF_of; rewrite rl_rho_sets; reflexivity).
  assert (HMr : rm rhoX = rm rho2) by (unfold rho2, rhoF_of; rewrite rm_rho_sets; reflexivity).
  assert (HPb : forall i, Pb q i = true -> rw rhoX i = rw rho2 i).
  { intros i Hi. unfold Pb in Hi. apply existsb_exists in Hi as (j & Hj & Eij). apply Pos.eqb_eq in Eij. subst j.
    apply in_app_or in Hj as [Hj|Hj].
    - destruct Hj as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; unfold rho2, rhoF_of; cbn [rho_sets rw rho_set_rw Pos.eqb];
        try reflexivity; rewrite ERW by (unfold GW; lia); first [exact P127 | exact P130 | exact P151 | exact P152 | exact P155].
    - destruct q; try (destruct Hj; fail). destruct Hj as [<-|[]]. cbn [qcond] in QC. destruct QC as (HNE & _).
      unfold rho2, rhoF_of; cbn [rho_sets rw rho_set_rw Pos.eqb]. rewrite ERW by (unfold GW; lia).
      destruct (aa_q_thread A2) eqn:EQ; [exfalso; exact (HNE eq_refl) | exact (P122 ltac:(discriminate))]. }
  assert (HP3 : forall i, P3 i = true -> rw rhoX i = rw rho2 i).
  { intros i Hi. unfold P3 in Hi. apply existsb_exists in Hi as (j & Hj & Eij). apply Pos.eqb_eq in Eij. subst j.
    destruct Hj as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; unfold rho2, rhoF_of; cbn [rho_sets rw rho_set_rw Pos.eqb]; rewrite ERW by (unfold GW; lia);
      first [exact P127 | exact P128 | exact P129 | exact P130 | exact P151 | exact P155]. }
  pose proof (carve_NV A2 rhoX tp md p n HA HL t2 (conj T1x (conj T2x (conj HW2 HL2))) jv2 JV q QC) as CNV.
  pose proof (pd_NFS A2 rhoX tp md p n HA HL HCLS E12u t2 (conj T1x (conj T2x (conj HW2 HL2))) jv2 JV q QC) as PD.
  pose proof (zone_NFS A2 rhoX tp md p n HA HL HCLS Hii E12u E13u t2 (conj T1x (conj T2x (conj HW2 HL2))) jv2 JV q QC) as ZN.
  fold rho2 in CNV, PD, ZN. unfold NFS in PD, ZN. rewrite (NV_split q Hq) in CNV, PD, ZN.
  apply Forall_app in CNV as [_ CNV3]. rewrite app_assoc in PD, ZN. apply Forall_app in ZN as [_ ZN3].
  rewrite map_app in PD. destruct (SymFrame.pairwise_disjoint_app_inv rho2 _ _ PD) as (_ & PD3 & PDX).
  assert (B3on : forall k, In k NV3 -> base_on (Pb q) k = true).
  { intros k Hk. apply (proj1 (forallb_forall _ _) (NFS_base_on q Hq) k). unfold NFS. rewrite (NV_split q Hq). apply in_or_app. right. apply in_or_app. right. exact Hk. }
  assert (RNG3 : forall k, In k NV3 -> obj_range rhoX (carve_obj k) = obj_range rho2 (carve_obj k)).
  { intros k Hk. exact (range_on (Pb q) rho2 rhoX HPb HLr k (B3on k Hk)). }

  assert (ZR : forall k, In k NV3 -> zone_ok (topG G) p (N8 n) (fst (obj_range rhoX (carve_obj k))) (snd (obj_range rhoX (carve_obj k)))).
  { intros k Hk. rewrite (RNG3 k Hk). pose proof (proj1 (Forall_forall _ _) ZN3 k Hk) as Zk. pose proof (proj1 (Forall_forall _ _) CNV3 k Hk) as Ck.
    destruct k as [[[base lo] hi] cs]. unfold spec_zone in Zk. unfold carve_ok in Ck. destruct Ck as (C1 & C2 & C3 & _).
    cbn [carve_obj]. unfold carved. rewrite obj_range_mk by lia. cbn [fst snd]. exact Zk. }
  rewrite HTRs. apply (SPA_carve_list segs (JF nW st false A2 Kc rho1) rhoX TR tp _ NV3 (ss_next (ax_S TR)) Hw).
  - rewrite HTRs in SWFS. exact SWFS.
  - lia.
  - apply Forall_forall. intros k Hk. pose proof (proj1 (Forall_forall _ _) CNV3 k Hk) as C.
    pose proof (carve_ok_on P3 rho2 rhoX HP3 HLr HMr k (proj1 (forallb_forall _ _) NV3_on k Hk) C) as C'.
    destruct k as [[[base lo] hi] cs]. unfold carve_ok in C'. cbn zeta in C' |- *.
    destruct C' as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
    refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 _)))))))).
    intros rr y j Hin. rewrite XTR in Hin. destruct Hin.
  - apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (k & <- & Hk). apply Forall_forall. intros o' Ho'.
    pose proof (ZR k Hk) as (ZL & ZZ). set (lo := fst (obj_range rhoX (carve_obj k))) in *. set (hi := snd (obj_range rhoX (carve_obj k))) in *.
    pose proof (proj1 (forallb_forall _ _) TROK o' Ho') as X. unfold tr_okb in X.
    assert (RD : forall a b, (hi <= a \/ b <= lo) -> ranges_disjoint (a, b) (obj_range rhoX (carve_obj k))).
    { intros a b D. unfold ranges_disjoint. fold lo hi. cbn [fst snd]. clear -D. lia. }
    unfold GOT_LO, GOT_HI, RTC_LO, RTC_HI, IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in ZZ.
    apply orb_prop in X as [X|X]; [apply orb_prop in X as [X|X]; [apply orb_prop in X as [X|X]; [apply orb_prop in X as [X|X]; [apply orb_prop in X as [X|X]; [apply orb_prop in X as [X|X]|]|]|]|]|].
    +
      apply existsb_exists in X as (o2 & Ho2 & Hs). rewrite (same_rng_range rhoX o' o2 Hs). apply in_map_iff in Ho2 as (k2 & <- & Hk2).
      assert (B2on : base_on (Pb q) k2 = true).
      { apply (proj1 (forallb_forall _ _) (NFS_base_on q Hq) k2). unfold NFS. rewrite (NV_split q Hq). rewrite app_assoc. apply in_or_app. left. exact Hk2. }
      rewrite (range_on (Pb q) rho2 rhoX HPb HLr k2 B2on), (RNG3 k Hk).
      exact (PDX (carve_obj k2) (carve_obj k) (in_map _ _ _ Hk2) (in_map _ _ _ Hk)).
    +
      rewrite (same_rng_range rhoX o' O_sh X).
      assert (RS : obj_range rhoX O_sh = (Sh p, Sh p + N8 n / 8)).
      { unfold O_sh, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
        assert (Es : bv_unsigned (eval rhoX shb) = Sh p).
        { cbn [eval shb]. rewrite (ERW 12%positive), P12, add_val, srl_val, !u64_lit by (unfold SHADOW_OFF, GW; lia). change (3 mod 64) with 3.
          rewrite Z.shiftr_div_pow2 by lia. unfold Sh, SHADOW_OFF. pose proof (Z.div_lt_upper_bound p (2 ^ 3) (2 ^ 44) ltac:(lia) ltac:(lia)).
          pose proof (Z.div_pos p (2 ^ 3) ltac:(lia) ltac:(lia)). rewrite Z.mod_small by lia. reflexivity. }
        pose proof (Z.div_pos (N8 n) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound (N8 n) 8 (N8 n) ltac:(lia) ltac:(lia)).
        assert (S106 : soff rhoX vN8g = N8 n / 8) by (apply soff_of_val; [cbn [eval vN8g]; rewrite ERW, P106 by (unfold GW; lia); apply u64_lit; lia | lia]).
        rewrite Es, soff_lit_small, S106 by lia.
        f_equal; lia. }
      rewrite RS. pose proof (Sh_in_band p ltac:(lia)) as S1. pose proof (Sh_in_band (p + N8 n) ltac:(lia)) as S2.
      assert (S3 : Sh p + N8 n / 8 <= Sh (p + N8 n)) by (unfold Sh; rewrite <- N4 at 2; rewrite Z.div_add by lia; lia).
      unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in S1, S2.
      apply RD. clear -ZZ S1 S2 S3. lia.
    +
      rewrite (same_rng_range rhoX o' O_blkN X).
      assert (RB : obj_range rhoX O_blkN = (p, p + N8 n)).
      { unfold O_blkN, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi eval].
        assert (S105 : soff rhoX vN8 = N8 n) by (apply soff_of_val; [cbn [eval vN8]; rewrite ERW, P105 by (unfold GW; lia); apply u64_lit; lia | lia]).
        rewrite S105.
        rewrite E12u, soff_lit_small by lia. f_equal; lia. }
      rewrite RB. apply RD. clear -ZZ B1 B4 TG. lia.
    +
      unfold ranges_disjoint. fold lo hi. destruct (obj_range rhoX o') as [a b] eqn:ER. cbn [fst snd].
      destruct (Z_lt_dec a b) as [Lab|]; [|lia].
      pose proof (rq_top nW A2 rhoX o' a Htop (proj2 Hdep) Hch X ltac:(rewrite ER; cbn [fst snd]; lia)) as TA. clear -ZZ TA TG. lia.
    +
      unfold lowwinb in X. destruct o' as [ob olo ohi ocs od]. cbn [ob_base ob_lo ob_hi] in X.
      destruct ob as [| | a1 e1 e2 | | | | |]; try discriminate X. destruct a1; try discriminate X.
      destruct e1 as [|v| | | | | |]; try discriminate X. destruct v as [v|v|]; try discriminate X. do 3 (destruct v as [v|v|]; try discriminate X).
      destruct e2 as [c| | | | | | |]; try discriminate X.
      destruct olo as [| | a2 f1 f2 | | | | |]; try discriminate X. destruct a2; try discriminate X.
      destruct f1 as [|v| | | | | |]; try discriminate X. destruct v as [v|v|]; try discriminate X. do 3 (destruct v as [v|v|]; try discriminate X).
      destruct f2 as [c'| | | | | | |]; try discriminate X.
      destruct ohi as [h| | | | | | |]; try discriminate X. destruct h; try discriminate X.
      apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2]. apply Z.eqb_eq in X1. apply Z.leb_le in X2, X3. subst c'. unfold free_depth in *.
      unfold top_high in Htop. unfold V_DEPTH in *. pose proof (urange (rw rhoX 10%positive)) as R10.
      assert (Eb : bv_unsigned (eval rhoX (SAlu ALU_ADD (SVar 10) (SLit c))) = bv_unsigned (rw rhoX 10%positive) + c).
      { cbn [eval]. rewrite add_val. destruct (Z.eq_dec c 0) as [->|NZ]; [rewrite u64_lit by lia; rewrite Z.add_0_r; apply Z.mod_small; lia|].
        replace (bv_unsigned (Z_to_bv 64 c)) with (2 ^ 64 + c) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64);
          rewrite <- (Z.mod_add c 1 (2 ^ 64)) by lia; rewrite Z.mod_small by lia; lia).
        rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia. }
      assert (El : soff rhoX (SAlu ALU_ADD (SVar 15) (SLit (- c))) = bv_signed (rw rhoX 15%positive) - c).
      { change (soff rhoX (SAlu ALU_ADD (SVar 15) (SLit (- c)))) with (bv_signed (eval rhoX (SAlu ALU_ADD (SVar 15) (SLit (- c))))).
        rewrite signed_add_lit by (cbn [eval]; lia). cbn [eval]. lia. }
      assert (RO : obj_range rhoX (mkObj (SAlu ALU_ADD (SVar 10) (SLit c)) (SAlu ALU_ADD (SVar 15) (SLit (- c))) (SLit 0) ocs od)
                   = (bv_unsigned (rw rhoX 10%positive) + c + (bv_signed (rw rhoX 15%positive) - c), bv_unsigned (rw rhoX 10%positive) + c + 0)).
      { unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite Eb, El, soff_lit_small by lia. reflexivity. }
      rewrite RO. apply RD. clear -ZZ Htop TG X2 X3 Hdep. lia.
    +
      rewrite (same_rng_range rhoX o' O_got X). unfold O_got. rewrite obj_range_mk by (unfold GOT_LO, GOT_HI; lia). cbn [eval]. rewrite u64_lit by lia.
      unfold GOT_LO, GOT_HI. apply RD. clear -ZZ. lia.
    +
      rewrite (same_rng_range rhoX o' O_rtc X). unfold O_rtc. rewrite obj_range_mk by (unfold RTC_LO, RTC_HI; lia). cbn [eval]. rewrite u64_lit by lia.
      unfold RTC_LO, RTC_HI. apply RD. clear -ZZ. lia.
  - apply (pd_on_ranges rhoX rho2 (map carve_obj NV3)); [|exact PD3]. intros o Ho. apply in_map_iff in Ho as (k & <- & Hk). exact (RNG3 k Hk).
Qed.

Theorem f0_s5d : ltac2:(tb__ "0|1|
S41OF_;S3S27Q40A1A1S44S2dVsegs;R3S2cVKc;A1A3S16S43Vsegs;R5S2bVsegs;S37VnW;Vst;S0VA2;VKc;Vrho1;A6M0VTQ;R1R4A5R3A4FrhoE;S16S43Vsegs;R6S2bVsegs;G0VTR;R1R5A5R4A4FrhoX;F_;F_;FQ;Ftp;Fok;").
Proof.
  intros ok tp Q Hok HC rhoX. pose proof CPARTS as (_ & _ & _ & _ & _ & Na & Nb). destruct L5 as [La Lb].
  pose proof (JF_stable nW st false A2 Kc rho1 (stopJ_stable_le _) HKc) as HST. pose proof (JF_okf nW st false ok A2 Kc rho1 Hok) as HOK.
  eapply triple_conseq; [intros w Hw; exact (carve3 rhoX tp w Hw) | intros w Hw; exact Hw |].
  apply (run_cont1 FUELF [RETQ] TRs l5 (ss_next (ax_S TRs)) Erq Nb eq_refl RUN5 Lb RETQ (JF nW st false A2 Kc rho1) ok rhoX tp Q (leaves_at1 _ _ La) HOK).
  - eapply stableA_mono; [|exact HST]. apply Pos.leb_le. exact Na.
  - intros rhoY HagY.
    eapply triple_conseq; [intros w Hw; exact (SPA_axforms segs _ XWl rhoY Erq Erq2 tp w AXW Hw) | intros w Hw; exact Hw |].
    apply (entF_cont (JF nW st false A2 Kc rho1) ok Erq2 TQ rhoY tp Q ENTQ HST). intros rho' _. apply HC.
Qed.
Theorem ef0_s5d : ltac2:(tb__ "0|1|
S3S27Q40A1A1S41OF_;S16S42Vsegs;S2bVsegs;S37VnW;Vst;S0VA2;VKc;Vrho1;A6M0VTQ;R1R3A5R2A3FrhoE;S16S42Vsegs;S2bVsegs;G0VTR;R1R4A5R3A3FrhoX;F_;FQ;Ftp;").
Proof.
  intros tp Q HC rhoX. pose proof CPARTS as (_ & _ & _ & _ & _ & Na & Nb). destruct L5 as [La Lb].
  pose proof (JF_stable nW st false A2 Kc rho1 (stopJ_stable_le _) HKc) as HST.
  eapply etriple_conseq; [intros w Hw; exact (carve3 rhoX tp w Hw) | intros w Hw; exact Hw |].
  apply (run_econt1 FUELF [RETQ] TRs l5 (ss_next (ax_S TRs)) Erq Nb eq_refl RUN5 Lb RETQ (JF nW st false A2 Kc rho1) rhoX tp Q (leaves_at1 _ _ La)).
  - eapply stableA_mono; [|exact HST]. apply Pos.leb_le. exact Na.
  - intros rhoY HagY.
    eapply etriple_conseq; [intros w Hw; exact (SPA_axforms segs _ XWl rhoY Erq Erq2 tp w AXW Hw) | intros w Hw; exact Hw |].
    apply (entF_econt (JF nW st false A2 Kc rho1) Erq2 TQ rhoY tp Q ENTQ HST). intros rho' _. apply HC.
Qed.
End SITE.
End S5D.
