(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_ins i7 SegD_laws2.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From LinuxProcessSemantics.Riscv Require Prelude Decode DecodeC Sem.

(* [comment removed for export] *)
Module DepotK.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "not"; "@Corelib.Init.Datatypes"; "list"; "app"; "length"; "prod"; "pair"; "bool"; "true"; "cons"; "nat"; "option"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "mul"; "ge"; "modulo"; "pow"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "event"; "vm_maps"; "vm_reserved"; "vm_noaccess"; "alloc_top"; "vm_limit"; "region_free"; "vm_init_sp"; "with_vmmaps"; "VmMaps"; "page_in_ranges"; "vm_add_lazy"; "m_vm_lazy"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.DepotK.DepotK"; "KD"; "AK"; "hcD"; "TOPr"; "dfp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "DG"; "dFB"; "dNB"; "aa_geom"; "aa_depot"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_ptr_committed"; "aa_sec"; "dFP"; "sec_chunk"; "aa_cls"; "aa_live"; "dN"; "topG"; "AA"; "ag_top"; "ageom"; "class_state"; "depot_state"; "sc_map_beg"; "sc_map_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "rl"; "rm"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "NBSZ"; "FBSZ"; "dep_cost"; "dblocks"; "sumZ"; "DNMAX"; "DFPw"; "FBPAGES"; "G_fblk"; "G_ins"; "G_nblk"; "G_page"; "depot_inv"; "droom"; "dtrans"; "fpage"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD"; "AInvX"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "PG"; "dyn_in"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "band_page"; "in_maps"; "secondary_repr"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "prim_credit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "bview"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "LIMIT"; "U0"; "acost"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_DEPTH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "BETA1"; "Q1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_laws2"; "KD_laws2"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt StepA SoundA SummaryA LedgerA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts Placement.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_ins.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_laws2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_ins OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.LedgerLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_laws2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section DepotK.
Let segs : list Segment := segsA.
Variables (A0 : AA) (Kc : KcA) (rhoE : valuation) (nreq : Z).
Hypothesis HKc : Kc_ok Kc.
Hypothesis HB : budget_ok_alloc A0 nreq.
Hypothesis Hn : 0 <= nreq.
Hypothesis HKm0 : 0 <= aa_Km A0.

Definition AK (G : DG) : AA := bumpK (with_depot A0 G).

Definition TOPr (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S3S12S41S35VA0;A1A1M0S11S29Q40M1S4aVrho;PaA2A2S2cG1S4aVrho;S75A2A2A2A2S12G0S29G1S4aVrho;PcA2A2A2A2").

Definition dfp_ok (G : DG) : Prop := ltac2:(tb__ "0|3|
S3S2SfS9S0S3cVG;A1M0A2S9S0S33VG;A1A2M1A3SfS6aR1G1A2S12Z0M2S62S0R2G0G2A4A2F_;Fb;A2").
Definition KD (G : DG) : jpredA := ltac2:(tb__ "0|0|
S49S7S2aQ40A1A1S7S1cA1S1bS3S60S2eVG;A1VrhoE;R3R1A4S3VKc;R2R1A2S3S31VG;A1S30R4A1A2A2A2Lmd;Ltr;Ltp;Lrho;").

Definition hcD : Z := ltac2:(tb__ "0|0|
S19S72S11S11S11S11S73S74S39VA0;A1A1A2S15S76S11S11S38VA0;A1Z1A2S37VA0;A1A2A2A2S77A2S3aVA0;A1A2A2").

Lemma AK_proj : ltac2:(tb__ "0|1|
S32S3S2S44S35S2eR1A1M0A1S35VA0;A1A3S3S2S7S45A1S3eG0A1S3eVA0;A1A3S3S2S7S3dA1S3bG0A1S3bVA0;A1A3S3S2S7SaS0S0A2A1S3fG0A1S3fVA0;A1A3S3S2S46S36G0A1R1A3S3S2S0S39G0A1S39VA0;A1A3S3S2S0S38G0A1S11S38VA0;A1Z1A2A3S3S2S0S37G0A1S37VA0;A1A3S2S0S3aG0A1S3aVA0;A1A3A2A2A2A2A2A2A2A2FG;").
Proof. intros G. repeat split; reflexivity. Qed.

Lemma AK_credit : ltac2:(tb__ "0|0|
S32S2S0S6bS2eR1A1A1S6bVA0;A1A3FG;").
Proof. intros G. apply PrimCredit.prim_credit_same. reflexivity. Qed.

Lemma KD_room : ltac2:(tb__ "0|0|
S32S49S7S2aQ40A1A1S7S1cA1S1bS2dR5R4R3R2R1A5S16S11S4fR2R4A2S52R6A1A2S2fA2F_;Fmd;Ftr;Ftp;Frho;FG;").
Proof.
  intros G rho tp tr md ((_ & _ & _ & _ & HM & _) & _).
  destruct HM as (_ & V2 & V3 & _). unfold headroom, hcD. rewrite V3.
  rewrite AK_credit in V2. pose proof (PrimCredit.prim_credit_nonneg A0) as PCN.
  unfold budget_boundD in V2. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed AK bumpK with_depot] in V2. lia.
Qed.

Lemma KD_reserved : ltac2:(tb__ "0|1|
S32S49S7S2aQ40A1M0A1S7S1cA1S1bS2dR5R4R3R2R1A5S2S7SaG0G0A2A1S1eS1aR2A1A1S6fVsegs;A1A3F_;Fmd;Ftr;Ftp;Frho;FG;").
Proof. intros G rho tp tr md ((_ & _ & _ & _ & HM & _) & _). destruct HM as (_ & _ & _ & _ & _ & _ & _ & L1 & _). exact L1. Qed.

Lemma KD_noacc : ltac2:(tb__ "0|5|
S32S49S7S2aQ40M0A1M1A1S7S1cA1S1bG1G1S0S2dR8R7R6R5R4A5S4dSaG1G1A2M2SbG1G1R4R3A4S1fS1aR5A1A1A3S3S12S29G0R5A2M3R3A2S13R3S11G3S29G0R4A2A2A2A2S5G1G1S5G1G1S3S4dG2SbG1G1R2R1A4S1dS1aR9A1A1A3S3S12S29G0R2A2M4R6A2S13R6S11G4S29G0R1A2A2A2A2A2Lm;A2Lb;A2F_;F_;F_;Fx;Fn;Fa;Fmd;Ftr;Ftp;Frho;FG;").
Proof.
  intros G rho tp tr md a n x ((_ & _ & _ & _ & HM & _) & _) Hin Hx. destruct HM as ((V1 & _) & _).
  destruct (V1 (a, n) x Hin Hx) as ([b m] & Hbm & Hr). exists b, m. exact (conj Hbm Hr).
Qed.

Lemma KD_top : ltac2:(tb__ "0|0|
S32S49S7S2aQ40A1A1S7S1cA1S1bS2dR5R4R3R2R1A5S2S0S20S1aR2A1A1S43S35VA0;A1A1A3F_;Fmd;Ftr;Ftp;Frho;FG;").
Proof. intros G rho tp tr md ((_ & _ & _ & _ & HM & _) & _). destruct HM as (_ & _ & _ & _ & _ & _ & V7 & _). exact V7. Qed.

Lemma KD_Kc : ltac2:(tb__ "0|0|
S32S49S7S2aQ40A1A1S7S1cA1S1bS2dR5R4R3R2R1A5VKc;R3R2A2F_;Fmd;Ftr;Ftp;Frho;FG;").
Proof. intros G rho tp tr md (_ & HK & _). exact HK. Qed.

Lemma KD_view : ltac2:(tb__ "0|2|
S32S49S49S7S2aQ40A1M0A1S7S1cA1S1bS1S2G0S4aR5R1A2S4aR6R1A2A3Fi;S1S2S7S2aQ8A1M1A1S4bR6R1A2S4bR7R1A2A3Fl;S0S6S56R9R1A2A1S2S10G1A1S6cVsegs;S4cR8A1R2A3S6cVsegs;S4cR9A1R2A3A3F_;Fz;S2dR9R8R6R5R4A5S2dRaR8R7R6R5A5F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho';Frho;FG;").
Proof. intros G rho rho' tp tr md Hw _ _ (HX & HK & HL & HT). unfold KD, TOPr in *. rewrite !Hw. exact (conj HX (conj HK (conj HL HT))). Qed.

Lemma KD_stable : ltac2:(tb__ "0|0|
S1S6eP10R1A2S32S71Vsegs;R3S2dR1A1A3FG;F_;Fn;").
Proof.
  intros n Hn16 G rho rho' tp tr md md' Hag Hme (HX & HK & HL & HT). split; [exact (AInvX_mat (AK G) rhoE tp md md' HX Hme)|].
  split; [|split; [exact HL | destruct Hag as (Hw & _ & _); unfold TOPr, V_DEPTH in *; rewrite <- (Hw 10%positive), <- (Hw 15%positive), <- (Hw 12%positive) by lia; exact HT]].
  destruct Hme as ((mat' & ->) & _). rewrite with_vm_backing_with_vm. apply HKc. exact HK.
Qed.

Lemma AInvX_depot_cost : ltac2:(tb__ "0|5|
S32S32S7S2aQ40M0A1M1A1M2G2S1bS2S7S0A1M3S34R4A1S34R5A1A3S2G3S33R5A1S33R6A1A3S12S11S4eR3R4A2S52R7A1A2S11S4eR3R5A2S52R6A1A2A2G1S4dG1R1R6A3S4S4dG1R2R8A3S6S67S29G0R2A2A1A1A2F_;Fq;S60S2eR9A1M4VrhoE;R7R5A4S60G4VrhoE;R7R6A4F_;F_;F_;F_;F_;Fmd;Ftp';Ftp;FG';FG;").
Proof.
  intros G G' tp tp' md EN EF HP HTP (HG & HR & HF & HRest & HM & HI3 & HBT).
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [exact HRest|]. split; [|split].
  - unfold model_inv_nd, ledger_inv_nd, gap_ok, gapN_ok, gapS_ok, blocks_left, budget_boundD in HM |- *.
    rewrite !AK_credit in HM |- *.
    cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_geom aa_sec AK bumpK with_depot] in HM |- *. rewrite EN, EF.
    destruct HM as (V1 & V2 & VR). split; [exact V1|]. split; [clear -V2 HP; lia | exact VR].
  - unfold inv3 in HI3 |- *. cbn [aa_geom aa_sec aa_live aa_depot aa_q_thread aa_q_global aa_cls AK bumpK with_depot] in HI3 |- *.
    unfold dblocks in HI3 |- *. rewrite EN, EF. exact HI3.
  - eapply bandtp_grow; [exact HBT|]. intros q Hq. destruct (HTP q Hq) as [H|H]; [left; exact H | right; intros Hb; exfalso; exact (H Hb)].
Qed.

Lemma u64_of_Z0 : ltac2:(tb__ "0|1|
S0S3S12Z0R1A2S13R1S18Z2Z40A2A2A2S2S0S29Q40M0S2bG0R2A2A2R2A3F_;Fz;").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64%N) with (2 ^ 64). apply Z.mod_small. exact Hz. Qed.

Lemma KD_trans_page : ltac2:(tb__ "0|3|
S32S7S2aQ40M0A1M1A1S1bSfG1S49S7S1cA1S6aR4S9S0S33R7A1A2A2S13S62S0R5S3cR8A1Z0M2A4S57A2S2G1R5S2bG0S5fR9R6S62S0R6S3cR9A1G2A4A3A2A3S2dRaR5R9R4R8A5S2dS5bRbR8A2R6SeG1R7RaA3R5R9A5F_;F_;F_;F_;Ftr;Frho;Fp;Fb;Fmd;Ftp;FG;").
Proof.
  intros G tp md b p rho tr Hb Hk Hp (HX & HK & [HL HNN] & HT). subst p. split; [|split; [exact HK | split; [| exact HT]]].
  2:{ split; [unfold G_page; cbn [dFP dFB]; rewrite length_list_upd; exact HL|].
      intros b' Hb'. unfold G_page in Hb' |- *. cbn [dFP dFB] in Hb' |- *.
      destruct (Nat.eq_dec b' b) as [->|Hne].
      - rewrite Model.nth_list_upd_same by (rewrite HL; exact Hb). pose proof (HNN b Hb). lia.
      - rewrite Model.nth_list_upd_other by (intros E; exact (Hne (eq_sym E))). exact (HNN b' Hb'). }
  apply (AInvX_depot_cost G (G_page G b) tp (_ :: tp) md); [reflexivity | reflexivity | | | exact HX].
  - rewrite (dep_cost_G_page G b) by (rewrite HL; exact Hb). pose proof (paid_cons_le md (Z_to_bv 64 (fpage G b (nth b (dFP G) 0))) tp). unfold PG. unfold page_size in *. lia.
  -
    intros q [<-|Hq]; [right | left; exact Hq].
    destruct HX as (_ & _ & _ & _ & _ & HI3 & _). destruct HI3 as (_ & _ & _ & _ & X5 & _).
    cbn [aa_geom aa_depot AK bumpK with_depot] in X5.
    destruct (X5 (nth b (dFB G) 0, FBSZ) ltac:(unfold dblocks; apply in_or_app; right; apply in_map_iff; exists (nth b (dFB G) 0); split; [reflexivity | apply nth_In; exact Hb])) as (DI & _).
    cbn [fst snd] in DI. destruct DI as (D1 & _ & D3 & _ & D5). pose proof (topG_range (aa_geom A0)) as TG. pose proof (HNN b Hb) as K0.
    unfold fpage. rewrite u64_of_Z0 by (unfold FBSZ, FBPAGES, PG in *; lia).
    intros HBP. apply band_page_band in HBP. unfold FBSZ, FBPAGES, PG in *. clear -D5 HBP K0 Hk D1 D3 TG. lia.
Qed.

Lemma apart_in_maps : ltac2:(tb__ "0|3|
S25S2aQ40M0A1M1G1S0S0S2ScS22S8SaG1G1A2S1eR5A1S1dR5A1A3R4R3A3SdA3S68R6R3R2A3S4S12S11S29G0R6A2M2S29G0R5A2A2R4A2S12R3G2A2A2F_;F_;Fhi;Flo;Fn;Fa;FV;").
Proof.
  intros V a n lo hi Hfree (e & Hin & H1 & H2).
  destruct (apart_of_region_free _ a n Hfree e ltac:(apply in_or_app; right; exact Hin)) as [X|X]; cbn [fst snd] in X; [left | right]; lia.
Qed.

Lemma sec_dyn : ltac2:(tb__ "0|0|
S6dS42S3dS69R3R2A2S4dS3dR2S3bR3A1A3S65S41S35R4A1A1S47R3A1S48R3A1A3F_;F_;Fch;FA;Fm;").
Proof.
  intros m A ch (HS & _) Hin. apply In_nth_error in Hin as (i & Hi).
  destruct (HS i ch Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & DI & _). exact DI.
Qed.

Lemma u64_of_Z : ltac2:(tb__ "0|1|
S0S3S12Z0R1A2S13R1S18Z2Z40A2A2A2S2S0S29Q40M0S2bG0R2A2A2R2A3F_;Fz;").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64%N) with (2 ^ 64). apply Z.mod_small. exact Hz. Qed.

Lemma AInvX_grant : ltac2:(tb__ "0|e|
S32S32S7S2aQ40M0A1M1A1S1bS1bG1G1S0S2S7SaG1G1A2M2A1M3S1dS1aR4A1A1SeG2SbG1G1R3R2A4S1dS1aR5A1M4A1A3A3S2G3S1fG4A1S1fS1aR6A1M5A1A3S2G3S1eG5A1S1eS1aR7A1M6A1A3S2S0S21G6A1S21S1aR8A1M7A1A3S2S0S20G7A1S20S1aR9A1A1A3G1S2ScS26R1S28RbA1M8A2SdA3S2ScS26R2G8A2SdA3F_;Fp;S2S0S29G0R8A2R7A3S13Z0R8A2S12S63S29G0RbA2A2S12S11S29G0RcA2RaA2S20S1aReA1A1A2S2ScS22S8G2S1eS1aRfA1M9A1S1dG9A1A3RdRcA3SdA3S12S11S4eRfR11A2S52R13A1A2S11S4eR10R11A2S52R12A1A2A2SaS0S0A2MaS4dGaR1S53R14A1A3S4S4dGaR2S53R16A1A3S2GaR2SbS0S0S29G0R11A2RfA4A3A2F_;Fbn;S2S0S11S14S9S0S34R14A1A2A1S14S9S0S33R14A1A2A1A2S11S11S14S9S0S34R15A1A2A1MbS14S9S0S33R15A1A2A1McA2Z1A2A3S2S0S11S15S50GbA2S15S51GcA2A2S11S11S15S50S14S9S0S34R16A1A2A1A2S15S51S14S9S0S33R16A1A2A1A2A2RfA2A3S60S2eR17A1MdVrhoE;R15R14A4S60GdVrhoE;R16R14A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FL;Fn;Fa;Fmd';Fmd;Ftp;FG';FG;").
Proof.
  intros G G' tp md md' a n L Hvm Hna Hrs Hlm Htop Hlz HnL HL Himg Hceil Hfree Hpaid Hblk Hcnt Hsz (HG & HR & HF & HRest & HM & HI3 & HBT).
  cbn [aa_geom AK bumpK with_depot] in HG, HR, HF, HRest.
  split; [exact HG|]. split; [exact HR|]. split; [exact HF|]. split; [exact HRest|].
  unfold model_inv_nd, ledger_inv_nd in HM. rewrite AK_credit in HM.
  cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_geom aa_sec AK bumpK with_depot] in HM.
  destruct HM as (VG & V2 & V3 & V4 & V5 & V6 & V7 & L1 & L2 & L3 & L4 & _ & _ & L7 & L8 & L9).
  set (G0g := aa_geom A0) in *.
  assert (APT : forall lo sz, in_maps (m_vmmaps md) lo (lo + sz) -> sepZ (bv_unsigned a, L) (lo, sz)).
  { intros lo sz Him. destruct (apart_in_maps _ a n lo (lo + sz) Hfree Him) as [X|X]; unfold sepZ; cbn [fst snd]; lia. }
  assert (INM : forall lo hi, in_maps (m_vmmaps md) lo hi -> in_maps (m_vmmaps md') lo hi).
  { intros lo hi (e & Hin & He). exists e. split; [rewrite Hvm; right; exact Hin | exact He]. }
  split; [|split; [|exact HBT]].
  -
    unfold model_inv_nd, ledger_inv_nd. rewrite AK_credit.
    cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_geom aa_sec AK bumpK with_depot].
    destruct VG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
    split.
    { unfold vm_geom. cbn [aa_geom aa_sec AK bumpK with_depot]. fold G0g. rewrite Hna.
      split; [|split; [apply INM; exact G2 | split; [apply INM; exact G3 | split; [apply INM; exact G4 | split; [apply INM; exact G5 | split; [apply INM; exact G6 | split; [apply INM; exact G7 | split]]]]]]].
      - intros e x He Hx. destruct (G1 e x He Hx) as (e' & He' & Hx'). exists e'. split; [rewrite Hvm; right; exact He' | exact Hx'].
      - intros ch Hch. rewrite Hvm. right. exact (G8 ch Hch).
      - intros p Hal Hw. destruct (G9 p Hal Hw) as [P1 P2]. split; [apply Hlz; exact P1 | exact P2]. }
    split.
    { unfold budget_boundD in V2 |- *. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed AK bumpK with_depot] in V2 |- *. clear -V2 Hpaid. lia. }
    split; [rewrite Hlm; exact V3|]. split; [exact V4|]. split; [exact V5|]. split; [exact V6|]. split; [rewrite Htop; exact V7|].
    split; [rewrite Hrs; exact L1|]. split; [rewrite Hvm; apply band_covered_cons; exact L2|].
    split.
    { rewrite Hrs, Hvm. apply maps_disjoint_insert; [exact L3|]. intros e' He'. exact (apart_of_region_free _ a n Hfree e' He'). }
    split.
    { unfold gap_ok, gapN_ok, gapS_ok, blocks_left, ledger in L4 |- *. cbn [aa_V aa_depot AK bumpK with_depot] in L4 |- *.
      rewrite Hrs, Hvm. destruct L4 as [N4 S4].
      pose proof (hwN_insert_le (vm_reserved (m_vmmaps md)) (a, n) (vm_maps (m_vmmaps md))) as IN.
      pose proof (hwS_insert_le (vm_reserved (m_vmmaps md)) (a, n) (vm_maps (m_vmmaps md))) as IS. cbn [snd] in IS. rewrite HnL in IS.
      split; [clear -N4 IN Hcnt; unfold GN in *; lia | clear -S4 IS Hsz; lia]. }
    split; [exact I|]. split; [exact I|]. split; [exact L7 | split; [| rewrite Hna; exact L9]].

    destruct L8 as (L8p & L8a & L8b). split; [|split; [exact (INM _ _ L8a) | exact (INM _ _ L8b)]].
    intros b s Hbs. rewrite Hvm in Hbs. destruct Hbs as [E|Hbs]; [injection E as <- <-; rewrite HnL; exact HL | exact (L8p b s Hbs)].
  -
    unfold inv3 in HI3 |- *. cbn [aa_geom aa_sec aa_live aa_depot aa_q_thread aa_q_global aa_cls AK bumpK with_depot] in HI3 |- *. fold G0g in HI3 |- *.
    destruct HI3 as (X1 & X2 & X3 & X4 & X5 & X6).
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [|exact X6].
    intros bn Hbn. destruct (Hblk bn Hbn) as [Hold | ->]; [exact (X5 bn Hold)|].
    destruct VG as (_ & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). fold G0g in G2, G3, G4, G5, G6, G7.
    cbn [fst snd]. split.
    {
      pose proof (geom_top _ HG) as TG. fold G0g in TG.
      assert (BC : band_covered (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) Geometry.SHADOW_BAND_LO Geometry.SHADOW_BAND_HI).
      { apply band_covered_app_r. exact L2. }
      pose proof (grant_avoids_band _ _ _ a n BC ltac:(unfold Geometry.SHADOW_BAND_LO, Geometry.SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END; lia) Hfree ltac:(lia)) as W.
      rewrite HnL in W. unfold dyn_in. unfold IMG_HI in *. rewrite TG. rewrite <- V7. split; [lia|]. split; [lia|]. split; [lia|]. split; [right; lia | exact W]. }
    split; [apply APT; exact G3|]. split; [apply APT; exact G4|]. split; [apply APT; exact G5|]. split; [apply APT; exact G6|].
    split; [apply APT; replace (ag_spacebeg G0g + (kSpaceSize + 4096)) with (ag_spacebeg G0g + kSpaceSize + 4096) by lia; exact G2|]. split; [apply APT; exact G7|].
    intros ch Hch.
    destruct HRest as (_ & _ & _ & HSR & _). pose proof (sec_dyn _ _ ch HSR Hch) as DI. cbn [aa_geom AK bumpK with_depot] in DI. fold G0g in DI.
    destruct DI as (D1 & D2 & D3 & _). pose proof (topG_range G0g) as TGR.
    pose proof (apart_of_region_free _ a n Hfree (Z_to_bv 64 (sc_map_beg ch), Z_to_bv 64 (sc_map_size ch)) ltac:(apply in_or_app; right; exact (G8 ch Hch))) as X.
    unfold apartW in X. cbn [fst snd] in X. rewrite !u64_of_Z in X by lia. unfold sepZ. cbn [fst snd]. lia.
Qed.

Lemma sumZ_app : ltac2:(tb__ "0|1|
S7S0A1M0G0S2S0S54S8S0R2R1A3A1S11S54R2A1S54R1A1A2A3Fl2;Fl1;").
Proof. induction l1; intros l2; cbn; [reflexivity | rewrite IHl1; unfold sumZ; cbn; lia]. Qed.

Lemma in_dblocks_app : ltac2:(tb__ "0|4|
S32SaS0S0A2M0S7S0A1M1G1S4dG0R3S8G0S61S0G0S0SbS0S0R1S50A4Lb;M2S8S0S34R4A1R2A3A4S61S0G0S0SbS0S0R1S51A4Lb;M3S8S0S33R4A1R1A3A4A3A3S4S4dG0R4S53R5A1A3S4dG0R4S8G0S61S0G0G2R3A4S61S0G0G3R2A4A3A3A2F_;Fl2;Fl1;Fbn;FG;").
Proof.
  intros G bn l1 l2 H. unfold dblocks. rewrite !map_app in H.
  apply in_app_or in H as [H|H]; apply in_app_or in H as [H|H].
  - left. apply in_or_app. left. exact H.
  - right. apply in_or_app. left. exact H.
  - left. apply in_or_app. right. exact H.
  - right. apply in_or_app. right. exact H.
Qed.

Lemma KD_trans_fblk : ltac2:(tb__ "0|5|
S32S7S2aQ40M0A1M1A1S1bS25G1G1S49S7S1cA1S2S7SaG1G1A2M2A1M3S1dR5A1SeG2SbG1G1R4R3A4S1dS1aR6A1A1A3A3S2G3S1fR6A1S1fS1aR7A1A1A3S2G3S1eR7A1S1eS1aR8A1A1A3S2S0S21R8A1S21S1aR9A1A1A3S2G1S23R9A1S23S1aRaA1A1A3S2S0S29G0R8A2S51A3S2S0S17S29G0RaA2S64A2Z0A3S12S63S29G0RbA2A2S12S11S29G0RcA2S51A2S20S1aReA1A1A2S2ScS22S8G2S1eS1aRfA1M4A1S1dG4A1A3RdRcA3SdA3S12S4eS27ReRdS24RfR10A2A3R11A2S4eR10R11A2A2S2dR13RdR12RcR11A5S2dS58R14S29G0R10A2A2ReR13RdS27R10RfS24R11R12A2A3A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftr;Frho;Fn;Fa;Fh';Fmd;Ftp;FG;").
Proof.
  intros G tp md h' a n rho tr Hvm Hna Hrs Hlm Hsp HnL Hal Himg Hceil Hfree Hpaid (HX & HK & HL & HT).
  split; [|split; [|split; [|exact HT]]].
  - apply (AInvX_grant G (G_fblk G (bv_unsigned a)) tp md _ a n FBSZ); rewrite ?m_vmmaps_vm_add_lazy, ?m_vmmaps_with_vmmaps, ?m_vm_lazy_vm_add_lazy, ?m_vm_lazy_with_vmmaps;
      try assumption.
    + apply alloc_top_same. exact Hsp.
    + intros p Hp. rewrite page_in_ranges_app, Hp. apply orb_true_r.
    + unfold FBSZ; lia.
    + unfold dep_cost, dep_pages, G_fblk. cbn [dNB dFP]. rewrite sumZ_app. cbn [sumZ fold_right]. lia.
    + intros bn Hbn. unfold G_fblk in Hbn. cbn [dNB dFB] in Hbn. unfold dblocks in Hbn. cbn [dNB dFB] in Hbn.
      rewrite <- (app_nil_r (dNB G)) in Hbn.
      destruct (in_dblocks_app G bn [] [bv_unsigned a] Hbn) as [X|X]; [left; exact X | right]. cbn in X. destruct X as [X|[]]. symmetry. exact X.
    + unfold G_fblk. cbn [dNB dFB]. rewrite length_app. cbn [length]. lia.
    + unfold G_fblk. cbn [dNB dFB]. rewrite length_app. cbn [length]. lia.
  - unfold vm_add_lazy. rewrite with_vm_backing_with_vm. apply HKc.
    replace (with_vmmaps h' md) with (with_vm (mkVmState h' (m_vm_lazy md) (m_vm_materialized md)) md) by (destruct md; reflexivity).
    apply HKc. exact HK.
  - destruct HL as [HL HNN]. split; [unfold G_fblk; cbn [dFP dFB]; rewrite !length_app; cbn [length]; lia|].
    intros b Hb. unfold G_fblk in Hb |- *. cbn [dFP dFB] in Hb |- *. rewrite length_app in Hb. cbn [length] in Hb.
    destruct (Nat.lt_ge_cases b (length (dFB G))) as [Hlt|Hge].
    + rewrite app_nth1 by (rewrite HL; exact Hlt). exact (HNN b Hlt).
    + rewrite app_nth2 by (rewrite HL; exact Hge). replace (b - length (dFP G))%nat with 0%nat by (rewrite HL; lia). cbn. lia.
Qed.

Lemma KD_trans_nblk : ltac2:(tb__ "0|5|
S32S7S2aQ40M0A1M1A1S1bS25G1G1S49S7S1cA1S2S7SaG1G1A2M2A1M3S1dR5A1SeG2SbG1G1R4R3A4S1dS1aR6A1A1A3A3S2G3S1fR6A1S1fS1aR7A1A1A3S2G3S1eR7A1S1eS1aR8A1A1A3S2S0S21R8A1S21S1aR9A1A1A3S2G1S23R9A1S23S1aRaA1A1A3S2S0S29G0R8A2S50A3S2S0S17S29G0RaA2S64A2Z0A3S12S63S29G0RbA2A2S12S11S29G0RcA2S50A2S20S1aReA1A1A2S2ScS22S8G2S1eS1aRfA1M4A1S1dG4A1A3RdRcA3SdA3S12S4eS24RfR10A2R11A2S11S4eR10R11A2S50A2A2S2dR13RdR12RcR11A5S2dS5aR14S29G0R10A2A2ReR13RdS24R11R12A2A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftr;Frho;Fn;Fa;Fh';Fmd;Ftp;FG;").
Proof.
  intros G tp md h' a n rho tr Hvm Hna Hrs Hlm Hsp HnL Hal Himg Hceil Hfree Hpaid (HX & HK & HL & HT).
  split; [|split; [|split; [|exact HT]]].
  - apply (AInvX_grant G (G_nblk G (bv_unsigned a)) tp md _ a n NBSZ); rewrite ?m_vmmaps_with_vmmaps, ?m_vm_lazy_with_vmmaps; try assumption.
    + apply alloc_top_same. exact Hsp.
    + intros p Hp. exact Hp.
    + unfold NBSZ; lia.
    + unfold dep_cost, dep_pages, G_nblk. cbn [dNB dFP]. rewrite length_app. cbn [length]. lia.
    + intros bn Hbn. unfold G_nblk in Hbn. cbn [dNB dFB] in Hbn. unfold dblocks in Hbn. cbn [dNB dFB] in Hbn.
      rewrite <- (app_nil_r (dFB G)) in Hbn.
      destruct (in_dblocks_app G bn [bv_unsigned a] [] Hbn) as [X|X]; [left; exact X | right]. cbn in X. destruct X as [X|[]]. symmetry. exact X.
    + unfold G_nblk. cbn [dNB dFB]. rewrite length_app. cbn [length]. lia.
    + unfold G_nblk. cbn [dNB dFB]. rewrite length_app. cbn [length]. lia.
  - replace (with_vmmaps h' md) with (with_vm (mkVmState h' (m_vm_lazy md) (m_vm_materialized md)) md) by (destruct md; reflexivity).
    apply HKc. exact HK.
  - unfold dfp_ok, G_nblk. cbn [dFP dFB]. exact HL.
Qed.

Lemma KD_trans_ins : ltac2:(tb__ "0|0|
S32S7S2aQ40A1A1S1bS0S49S7S1cA1S2dR6R2R5R1R4A5S2dS59R7R4A2R3R6R2R5A5F_;Ftr;Frho;FdF';Fmd;Ftp;FG;").
Proof.
  intros G tp md dF' rho tr (HX & HK & HL & HT). split; [|split; [exact HK | split; [unfold dfp_ok, G_ins; cbn [dFP dFB]; exact HL | exact HT]]].
  apply (AInvX_depot_cost G (G_ins G dF') tp tp md); [reflexivity | reflexivity | | intros q Hq; left; exact Hq | exact HX].
  unfold dep_cost, dep_pages, G_ins. cbn [dNB dFP]. lia.
Qed.

Theorem KD_trans : ltac2:(tb__ "0|1|
S32S7S2aQ40A1A1M0S1bS32G0S1bS49S7S1cA1S5eR8R7R6R5R4R3A6S2dR9R3R8R2R7A5S2dR7R4R6R3R5A5F_;F_;Ftr;Frho;Fmd';Ftp';FG';Fmd;Ftp;FG;").
Proof.
  intros G tp md G' tp' md' rho tr HT HK. destruct HT.
  - eapply KD_trans_page; eassumption.
  - apply KD_trans_fblk; assumption.
  - eapply KD_trans_nblk; eassumption.
  - apply KD_trans_ins; assumption.
Qed.

Lemma KD_place : ltac2:(tb__ "0|2|
S32S49S7S2aQ40M0A1M1A1S7S1cA1S1bS0S2dR6R5R4R3R2A5S5cVsegs;R7R6R3R5A5S12S40R8A1S55A2S4S2S0R4S50A3S2S0R4S51A3A2S5G1G1S70S2bG0Z0A2R7S2bG0R6A2R1A4La;A2F_;F_;F_;F_;FL;Fmd;Ftr;Ftp;Frho;FG;").
Proof.
  intros G rho tp tr md L ((HG & _ & _ & _ & HM & _) & _) [DM _] HDN HL.
  cbn [aa_geom AK bumpK with_depot] in HG.
  destruct HM as (_ & _ & _ & V4 & V5 & V6 & V7 & _ & _ & _ & L4 & _).
  pose proof (dm_map1_len _ _ DM) as [_ M2]. pose proof (dm_fb_len _ _ DM) as [[_ F2] _].
  pose proof (dm_N _ _ DM) as [[N1 _] _]. pose proof (dm_F _ _ DM) as (F0 & _ & F32 & _).
  apply (depot_place (AK G) md L).
  - exact L4.
  - cbn [aa_V AK bumpK with_depot]. cbn [aa_V aa_Km aa_Kf AK bumpK with_depot] in V4, V5, V6. pose proof (budget_ok_alloc_limit _ _ HB) as HBl.
    pose proof (VCAP_limit_alloc (aa_V A0) (aa_Km A0) (aa_Kf A0) nreq ltac:(lia) HKm0 V6 HBl) as VC. lia.
  - cbn [aa_depot AK bumpK with_depot]. unfold nblk in M2. unfold NBMAX, DNMAX in *.
    destruct (Z.eqb_spec (dN G + 1) 0); [lia|].
    pose proof (Z.div_le_mono (dN G + 1) (2 ^ 28 + 2) 65536 ltac:(lia) ltac:(lia)) as DV. change ((2 ^ 28 + 2) / 65536) with 4096 in DV. lia.
  - cbn [aa_depot AK bumpK with_depot]. unfold fblk in F2. unfold FBMAX.
    pose proof (Z.div_le_mono (dF G + 1048576 - 1) (2 ^ 32 - 2 ^ 21 + 1048576 - 1) 1048576 ltac:(lia) ltac:(lia)) as DV.
    change ((2 ^ 32 - 2 ^ 21 + 1048576 - 1) / 1048576) with 4094 in DV. lia.
  - rewrite V7. cbn [aa_geom AK bumpK with_depot]. pose proof (geom_top _ HG) as TG. pose proof (topG_range (aa_geom A0)). rewrite GAPC_eq. unfold alloc_ceiling_lo. lia.
  - exact HL.
Qed.

Theorem KD_laws : ltac2:(tb__ "0|0|
S1S6eP10R1A2S78Vsegs;S2dR2S2fA4F_;Fn;").
Proof.
  intros n Hn16. constructor.
  - exact (KD_stable n Hn16).
  - exact KD_view.
  - exact KD_trans.
  - intros G rho tp tr md HK _. exact (KD_room G rho tp tr md HK).
  - exact KD_reserved.
  - exact KD_noacc.
  - exact KD_place.
Qed.

Lemma KD_intro : ltac2:(tb__ "0|0|
S7S2aQ40A1A1S7S1cA1S1bS66Vsegs;VA0;VrhoE;R3R1A5VKc;R3R2A2S49S30R1A1S2dS36VA0;A1R2R7R6R5A5F_;Frho;F_;F_;Fmd;Ftr;Ftp;").
Proof.
  intros tp tr md HA HK rho HT. destruct (AInvA_X A0 rhoE tp md HA) as (HX & HD & _).
  split; [|split; [exact HK | split; [split; [exact (proj2 (dm_fb_len _ _ (proj1 HD))) | intros b Hb; exact (proj1 (proj1 (dm_fp _ _ (proj1 HD) b Hb)))] | exact HT]]].
  unfold AK. replace (with_depot A0 (aa_depot A0)) with A0 by (destruct A0; reflexivity). exact (AInvX_bumpK A0 rhoE tp md HX).
Qed.

Lemma dN_entry : ltac2:(tb__ "0|0|
S7S2aQ40A1A1S1bS66Vsegs;VA0;VrhoE;R2R1A5S12S11S40S36VA0;A1A1Z1A2S55A2F_;Fmd;Ftp;").
Proof.
  intros tp md HA. destruct (AInvA_X A0 rhoE tp md HA) as ((_ & _ & _ & _ & HM & _) & _ & L6).
  destruct HM as (_ & _ & _ & V4 & V5 & V6 & _). pose proof (budget_ok_alloc_limit _ _ HB) as HBl.
  pose proof (limit_ok_alloc_K (aa_V A0) (aa_Km A0) (aa_Kf A0) nreq ltac:(lia) HBl). unfold DNMAX. lia.
Qed.

Lemma QMAX_Q1 : QMAX - Q1 = 2813952.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma hcD_entry : ltac2:(tb__ "0|1|
S7S2aQ40A1A1S1bS66Vsegs;VA0;VrhoE;R2R1A5S16S2fS11S52S36VA0;A1M0A1S5dG0A1A2A2F_;Fmd;Ftp;").
Proof.
  intros tp md HA. destruct (AInvA_X A0 rhoE tp md HA) as ((_ & _ & _ & _ & HM & _) & HD & L6).
  destruct HM as (_ & _ & _ & V4 & V5 & V6 & _ & _ & _ & _ & _ & _ & _ & L7 & _).
  pose proof (dep_cost_bound segs _ _ _ _ HD) as DC. pose proof (dm_F _ _ (proj1 HD)) as (F0 & F11 & F32 & _). pose proof (dm_N _ _ (proj1 HD)) as [[N1 _] _].
  pose proof (fblk_amort _ (dm_F_NFBLK _ _ (proj1 HD))) as FB. destruct F11 as (F11 & _).
  pose proof (budget_ok_alloc_limit _ _ HB) as HBl. unfold limit_ok_alloc in HBl. unfold hcD.
  pose proof (acost_mono (aa_V A0) (aa_V A0 + nreq) ltac:(lia)) as AM.
  pose proof QMAX_Q1 as CL.
  assert (DR : droom (aa_depot A0) <= PG + NBSZ) by (unfold droom; destruct ((dN (aa_depot A0) + 1) mod 65536 =? 0); unfold PG, NBSZ; lia).
  unfold DEPC, PG, NBSZ, BETA1, BETA_M, BETA_F, kPtrArrayCommit, LIMIT in *.
  set (q1 := Q1) in *. set (qm := QMAX) in *. set (u0 := U0) in *. set (dc := dep_cost (aa_depot A0)) in *. set (dr := droom (aa_depot A0)) in *.
  set (av := acost (aa_V A0)) in *. set (avn := acost (aa_V A0 + nreq)) in *. set (fb := fblk (dF (aa_depot A0))) in *.
  clearbody q1 qm u0 dc dr av avn fb. lia.
Qed.
End DepotK.

End DepotK.

(* [comment removed for export] *)
Module InvReveal.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_depot"; "ageom"; "qbatch"; "DG"; "class_state"; "dFB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "image_byte"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.InvReveal"; "bext"; "cellZ_e"; "cell_ok_e"; "filled_e"; "present_e"; "@Corelib.Init.Datatypes"; "list"; "app"; "option"; "None"; "nat"; "Some"; "bool"; "prod"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "view"; "present"; "cell_ok"; "filled"; "acell"; "cells_ok"; "maskv"; "restrictv"; "rtc_inv"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "band_page"; "AInvA"; "alloc_magic_ok"; "bandtp_inv"; "batch_repr"; "class_repr"; "depot_wf"; "fs_inv"; "ia_inv"; "inv3"; "live_block_repr"; "misc_inv"; "present_but"; "primary_repr"; "q_item_ok"; "qhdr_repr"; "qlinks"; "quarantine_repr"; "rest_inv"; "secondary_repr"; "shadow_unpoisoned"; "thread_inv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "PG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD"; "AInvX"; "rest_inv_nd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "budget_boundD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit"; "prim_credit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "cellZ"; "depot_mem"; "depot_vm"; "FBPAGES"; "fpage"; "@Corelib.Init.Peano"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.SegD_cost OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.InvD.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition bext (m m' : bview) : Prop := ltac2:(tb__ "0|2|
S0SfQ8A1M0SbS18G0A1M1Vm;R2A1S1bG0R1A2A3SbG1Vm';R3A1S1bG0R2A2A3F_;Fb;Fz;").

Lemma bext_refl : ltac2:(tb__ "0|0|
S1fS11R1R1A2Fm;").
Proof. intros m z b H. exact H. Qed.
Lemma bext_trans : ltac2:(tb__ "0|1|
S1fS1fS1fS11R3R2A2M0G0S11R5R3A2F_;F_;Fm3;Fm2;Fm1;").
Proof. intros m1 m2 m3 H1 H2 z b H. exact (H2 z b (H1 z b H)). Qed.
Lemma bext_restrictv : ltac2:(tb__ "0|0|
S0S1cF_;S1fS1fS11R2R1A2S11S27R4R3A2S27R4R2A2A2F_;Fm';Fm;FP;").
Proof. intros P m m' H z b. unfold restrictv. destruct (P z); [apply H | intros X; exact X]. Qed.
Lemma bext_maskv : ltac2:(tb__ "0|0|
S0S1cF_;S1fS1fS11R2R1A2S11S26R4R3A2S26R4R2A2A2F_;Fm';Fm;FP;").
Proof. intros P m m' H z b. unfold maskv. destruct (P z); [intros X; exact X | apply H]. Qed.
Lemma bext_def : ltac2:(tb__ "0|3|
S1fS1fS0S11R3R2A2SdSbS18SfQ8A1M0A1M1R4R2A1S19G0A1M2A3A1SdSbG1R4R3A1G2A3A1F_;F_;Fz;Fm';Fm;").
Proof. intros m m' z H Hz. destruct (m z) as [b|] eqn:E; [|exact (fun X => Hz eq_refl)]. rewrite (H z b E). discriminate. Qed.

Section Atoms.
Variables (m m' : bview).
Hypothesis EXT : bext m m'.
Lemma cell_ok_e : ltac2:(tb__ "0|0|
S24S22Vm;R1A2S22Vm';R2A2F_;Fc;").
Proof. intros c H k Hk. exact (EXT _ _ (H k Hk)). Qed.
Lemma cells_ok_e : ltac2:(tb__ "0|0|
S16S24A1S25Vm;R1A2S25Vm';R2A2F_;Fcs;").
Proof. intros cs H. unfold cells_ok in *. apply Forall_forall. intros c Hc. apply cell_ok_e. exact (proj1 (Forall_forall _ _) H c Hc). Qed.
Lemma cellZ_e : ltac2:(tb__ "0|0|
S0S1aS0S4bVm;R3R2R1A4S4bVm';R4R3R2A4F_;Fv;Fw;Fa;").
Proof. intros a w v H. unfold cellZ in *. apply cell_ok_e. exact H. Qed.
Lemma present_e : ltac2:(tb__ "0|0|
S0S0S21Vm;R2R1A3S21Vm';R3R2A3F_;Fhi;Flo;").
Proof. intros lo hi H z Hz. destruct (H z Hz) as [b Hb]. exists b. exact (EXT _ _ Hb). Qed.
Lemma filled_e : ltac2:(tb__ "0|0|
S0S0S0S23Vm;R3R2R1A4S23Vm';R4R3R2A4F_;Fv;Fhi;Flo;").
Proof. intros lo hi v H z Hz. exact (EXT _ _ (H z Hz)). Qed.
End Atoms.

Section Components.
Variables (m m' : bview).
Hypothesis EXT : bext m m'.
Let CE : ltac2:(tb__ "0|0|
S24S22Vm;R1A2S22Vm';R2A2F_;Fc;") := ltac2:(tb__ "0|0|
S13Vm;Vm';VEXT;A3"). Let CZ : ltac2:(tb__ "0|0|
S0S1aS0S4bVm;R3R2R1A4S4bVm';R4R3R2A4F_;Fv;Fw;Fa;") := ltac2:(tb__ "0|0|
S12Vm;Vm';VEXT;A3"). Let PE : ltac2:(tb__ "0|0|
S0S0S21Vm;R2R1A3S21Vm';R3R2A3F_;Fhi;Flo;") := ltac2:(tb__ "0|0|
S15Vm;Vm';VEXT;A3"). Let FE : ltac2:(tb__ "0|0|
S0S0S0S23Vm;R3R2R1A4S23Vm';R4R3R2A4F_;Fv;Fhi;Flo;") := ltac2:(tb__ "0|0|
S14Vm;Vm';VEXT;A3").

Lemma shadow_unpoisoned_e : ltac2:(tb__ "0|0|
S0S0S40Vm;R2R1A3S40Vm';R3R2A3F_;Fn;Fb;").
Proof. intros b n [H1 H2]. split; [intros g Hg; exact (EXT _ _ (H1 g Hg)) | intros Hn; exact (EXT _ _ (H2 Hn))]. Qed.

Lemma alloc_magic_ok_e : ltac2:(tb__ "0|0|
S0S0S2eVm;R2R1A3S2eVm';R3R2A3F_;Fn;Fb;").
Proof. intros b n [H|[H1 H2]]; [left; exact H | right; split; apply CE; assumption]. Qed.

Lemma present_but_e : ltac2:(tb__ "0|0|
S0S0S16S1dS0S0A2A1S38Vm;R3R2R1A4S38Vm';R4R3R2A4F_;FL;Fhi;Flo;").
Proof. intros lo hi L H z Hz Hn. destruct (H z Hz Hn) as [b Hb]. exists b. exact (EXT _ _ Hb). Qed.

Ltac bleaf :=
  first [ intros H; exact H
        | intros H; exact (EXT _ _ H)
        | intros H; exact (cell_ok_e m m' EXT _ H)
        | intros H; exact (cellZ_e m m' EXT _ _ _ H)
        | intros H; exact (present_e m m' EXT _ _ H)
        | intros H; exact (present_but_e _ _ _ H)
        | intros H; exact (filled_e m m' EXT _ _ _ H)
        | intros H; exact (cells_ok_e m m' EXT _ H)
        | intros H; exact (shadow_unpoisoned_e _ _ H)
        | intros H; exact (alloc_magic_ok_e _ _ H) ].
Ltac bmono :=
  lazymatch goal with
  | |- (_ /\ _) -> (_ /\ _) => let HA := fresh "HA" in let HB := fresh "HB" in intros [HA HB]; split; [revert HA; bmono | revert HB; bmono]
  | |- (exists x, _) -> (exists y, _) => let x := fresh "x" in let Hx := fresh "Hx" in intros [x Hx]; exists x; revert Hx; bmono
  | |- (_ \/ _) -> (_ \/ _) => let H := fresh "HH" in intros [H|H]; [left | right]; revert H; bmono
  | |- (forall a, _) -> (forall b, _) => let H := fresh "HH" in let a := fresh "a" in intros H a; specialize (H a); revert H; bmono
  | |- _ => bleaf
  end.

Lemma rtc_inv_e : ltac2:(tb__ "0|0|
S3S28Vm;R1A2S28Vm';R2A2F_;FG;").
Proof. intros G H. unfold rtc_inv in *. exact (cells_ok_e m m' EXT _ H). Qed.

Lemma thread_inv_e : ltac2:(tb__ "0|0|
S3S41Vm;R1A2S41Vm';R2A2F_;FG;").
Proof. intros G. unfold thread_inv. bmono. Qed.

Lemma misc_inv_e : ltac2:(tb__ "0|0|
S37Vm;A1S37Vm';A1F_;").
Proof. unfold misc_inv. bmono. Qed.

Lemma ia_inv_e : ltac2:(tb__ "0|0|
S1S34Vm;R1A2S34Vm';R2A2F_;FA;").
Proof. intros A. unfold ia_inv. destruct (aa_internal_inited A); bmono. Qed.

Lemma live_block_repr_e : ltac2:(tb__ "0|0|
S1S36Vm;R1A2S36Vm';R2A2F_;FA;").
Proof. intros A. unfold live_block_repr. bmono. Qed.

Lemma class_repr_e : ltac2:(tb__ "0|0|
S3S1S0S6S31Vm;R4R3R2R1A5S31Vm';R5R4R3R2A5F_;Fcs;Fc;FA;FG;").
Proof. intros G A c cs. unfold class_repr. bmono. Qed.

Lemma primary_repr_e : ltac2:(tb__ "0|0|
S1S39Vm;R1A2S39Vm';R2A2F_;FA;").
Proof. intros A (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. intros c Hc. apply class_repr_e. exact (H4 c Hc). Qed.

Lemma secondary_repr_e : ltac2:(tb__ "0|0|
S1S3fVm;R1A2S3fVm';R2A2F_;FA;").
Proof. intros A. unfold secondary_repr. bmono. Qed.

Lemma q_item_ok_e : ltac2:(tb__ "0|0|
S1S1dS0S0A2S3aVm;R2R1A3S3aVm';R3R2A3F_;Fit;FA;").
Proof. intros A it. unfold q_item_ok. bmono. Qed.

Lemma batch_repr_e : ltac2:(tb__ "0|0|
S1S4S30Vm;R2R1A3S30Vm';R3R2A3F_;Fb;FA;").
Proof.
  intros A b H. unfold batch_repr in H |- *. destruct H as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  split; [exact B1|]. split; [exact (CE _ B2)|]. split; [exact (CE _ B3)|]. split; [exact B4|]. split; [exact B5|]. split; [exact (PE _ _ B6)|].
  split; [|exact B8]. intros i it Hi. destruct (B7 i it Hi) as [X1 X2]. split; [exact (CE _ X1) | exact (q_item_ok_e _ _ X2)].
Qed.

Lemma qlinks_e : ltac2:(tb__ "0|0|
S16S4A1S3cVm;R1A2S3cVm';R2A2F_;Fl;").
Proof. induction l as [|b r IH]; intros H; [exact I|]. destruct H as [H1 H2]. split; [exact (CE _ H1) | exact (IH H2)]. Qed.

Lemma qhdr_repr_e : ltac2:(tb__ "0|0|
S0S16S4A1S3bVm;R2R1A3S3bVm';R3R2A3F_;Fl;Fhdr;").
Proof. intros hdr l. unfold qhdr_repr. bmono. Qed.

Lemma quarantine_repr_e : ltac2:(tb__ "0|0|
S1S3dVm;R1A2S3dVm';R2A2F_;FA;").
Proof.
  intros A H. unfold quarantine_repr in H |- *. destruct H as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  split; [apply Forall_forall; intros b Hb; apply batch_repr_e; exact (proj1 (Forall_forall _ _) Q1 b Hb)|].
  split; [exact (qlinks_e _ Q2)|]. split; [exact (qlinks_e _ Q3)|]. split; [exact (qhdr_repr_e _ _ Q4)|]. split; [exact (qhdr_repr_e _ _ Q5)|].
  split; [exact (CE _ Q6)|]. split; [exact (CE _ Q7)|]. split; [exact Q8 | exact Q9].
Qed.

Lemma depot_mem_e : ltac2:(tb__ "0|0|
S5S4cR1Vm;A2S4cR2Vm';A2F_;FG;").
Proof.
  intros G H. destruct H as [HN HF Hmu Hal Htab Hl1 Hm1 Hnb Hlk Hfl Hfb Hfz Hfbs Hfp Hflo Hfh Hdj].
  constructor.
  - split; [exact (proj1 HN) | exact (CZ _ _ _ (proj2 HN))].
  - destruct HF as (F1 & F2 & F3 & F4). split; [exact F1|]. split; [exact F2|]. split; [exact F3 | exact (CZ _ _ _ F4)].
  - exact (CZ _ _ _ Hmu).
  - exact (PE _ _ Hal).
  - intros i Hi. destruct (Htab i Hi) as (w & Hw & Hr). exists w. split; [exact (CZ _ _ _ Hw) | exact Hr].
  - exact Hl1.
  - intros j Hj. exact (CZ _ _ _ (Hm1 j Hj)).
  - intros b Hb. destruct (Hnb b Hb) as (A1 & A2 & A3 & A4). split; [exact A1|]. split; [exact A2|]. split; [exact A3 | exact (PE _ _ A4)].
  - intros s Hs. destruct (Hlk s Hs) as (h & l & Hh & Hl & Hr). exists h, l. split; [exact (CZ _ _ _ Hh)|]. split; [exact (CZ _ _ _ Hl) | exact Hr].
  - exact Hfl.
  - intros b Hb. destruct (Hfb b Hb) as (A1 & A2 & A3 & A4). split; [exact (CZ _ _ _ A1)|]. split; [exact A2|]. split; [exact (PE _ _ A3) | exact (CZ _ _ _ A4)].
  - intros b Hb. destruct (Hfz b Hb) as (A1 & A2 & A3). split; [exact (FE _ _ _ A1)|]. split; [exact (PE _ _ A2) | exact (FE _ _ _ A3)].
  - exact Hfbs.
  - intros b Hb. destruct (Hfp b Hb) as [A1 A2]. split; [exact A1 | exact (PE _ _ A2)].
  - exact Hflo.
  - exact Hfh.
  - exact Hdj.
Qed.

Lemma depot_wf_e : ltac2:(tb__ "0|0|
S1S32Vm;R1A2S32Vm';R2A2F_;FA;").
Proof. intros A H. unfold depot_wf in *. exact (depot_mem_e _ H). Qed.

Lemma rest_inv_e : ltac2:(tb__ "0|0|
S1S3eVm;R1A2S3eVm';R2A2F_;FA;").
Proof.
  intros A (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
  split; [exact R1|]. split; [exact (live_block_repr_e _ R2)|]. split; [exact (primary_repr_e _ R3)|]. split; [exact (secondary_repr_e _ R4)|].
  split; [exact (quarantine_repr_e _ R5)|]. split; [exact (depot_wf_e _ R6)|]. split; [exact (ia_inv_e _ R7)|].
  split; [exact (thread_inv_e _ R8) | exact (misc_inv_e R9)].
Qed.

Lemma rest_inv_nd_e : ltac2:(tb__ "0|0|
S1S48Vm;R1A2S48Vm';R2A2F_;FA;").
Proof.
  intros A (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
  split; [exact R1|]. split; [exact (live_block_repr_e _ R2)|]. split; [exact (primary_repr_e _ R3)|]. split; [exact (secondary_repr_e _ R4)|].
  split; [exact (quarantine_repr_e _ R5)|]. split; [exact I|]. split; [exact (ia_inv_e _ R7)|].
  split; [exact (thread_inv_e _ R8) | exact (misc_inv_e R9)].
Qed.

Lemma fs_inv_e : ltac2:(tb__ "0|0|
S1S33Vm;R1A2S33Vm';R2A2F_;FA;").
Proof. intros A. unfold fs_inv. bmono. Qed.

Lemma bandtp_inv_e : ltac2:(tb__ "0|0|
S16SfQ40A1A1S2fVm;R1A2S2fVm';R2A2F_;Ftp;").
Proof. intros tp H. eapply bandtp_mono; [|exact H]. intros z _ Hz. exact (bext_def m m' z EXT Hz). Qed.
End Components.

Section WithSegs.
Variable segs : list Segment.

Lemma fpage_not_band : ltac2:(tb__ "0|0|
S1S1aS0S35R3A1S50R3S1eS0S7S2R4A1A1A2A2ScS2aZ0R3A2S2bR3S4eA2A2SdS2cS4fS2R6A1R5R4A3A1A1F_;F_;F_;Fk;Fb;FA;").
Proof.
  intros A b k HI3 Hb Hk HB. destruct HI3 as (_ & _ & _ & _ & X5 & _).
  set (bb := nth b (dFB (aa_depot A)) 0).
  assert (Hin : In (bb, FBSZ) (dblocks (aa_depot A))).
  { unfold dblocks. apply in_or_app. right. apply in_map_iff. exists bb. split; [reflexivity|]. apply nth_In. exact Hb. }
  destruct (X5 _ Hin) as (DI & _). cbn [fst snd] in DI. destruct DI as (_ & _ & _ & _ & WB).
  pose proof (band_page_band _ HB) as R. unfold fpage in R. fold bb in R.
  unfold FBSZ, FBPAGES, PG, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
Qed.

Lemma depot_vm_grow_band : ltac2:(tb__ "0|3|
S1S42S16SfQ40M0A1M1A1M2G2S35R4A1S4dS2R5A1R4R3A3G1S44G1R1R4A3S2cS10G0R2A2A1F_;Fp;S4dS2R7A1R6S17G1R4R5A3A3F_;F_;F_;Ftp1;Ftp;Fmd;FA;").
Proof.
  intros A md tp tp1 HI3 [D1 D2 D3 D4 D5 D6] Hb. constructor; try assumption.
  intros b k Hbk Hk. rewrite in_app_iff. split.
  - intros [H|H]; [|exact (proj1 (D4 b k Hbk Hk) H)]. exfalso. apply (fpage_not_band A b k HI3 Hbk Hk).
    pose proof (Hb _ H) as X. rewrite u64_lit in X; [exact X|].
    destruct HI3 as (_ & _ & _ & _ & X5 & _).
    assert (Hin : In (nth b (dFB (aa_depot A)) 0, FBSZ) (dblocks (aa_depot A))).
    { unfold dblocks. apply in_or_app. right. apply in_map_iff. exists (nth b (dFB (aa_depot A)) 0). split; [reflexivity|]. apply nth_In. exact Hbk. }
    destruct (X5 _ Hin) as (DI & _). cbn [fst snd] in DI. destruct DI as (D0 & _ & DT & _). pose proof (topG_range (aa_geom A)).
    unfold fpage, FBSZ, FBPAGES, PG in *. lia.
  - intros H. right. exact (proj2 (D4 b k Hbk Hk) H).
Qed.

Theorem AInvA_ext : ltac2:(tb__ "0|4|
S1S9S9S16SfQ40M0A1M1A1M2G2S42S2dVsegs;R6R5R3R1A5S11S20Vsegs;S8R6A1A2S20Vsegs;S8R5A1A2A2G1S44G1R1R5A3ScS2cS10G0R2A2M3A1S21S20Vsegs;S8R8A1A2G3S29G3S46A2A3A2F_;Fp;S2aS29S45R4S17G1R5R6A3A2S4aR9A1A2S49R9A1A2S2dVsegs;RaR8S17G1R6R7A3R5A5F_;F_;F_;F_;Fmd;Ftp1;Ftp;Frho';Frho;FA;").
Proof.
  intros A rho rho' tp tp1 md (HG & HR & HF & HRest & HM & HI3 & HB) EXT Htp1 Hpaid.
  split; [exact HG|]. split; [exact (rtc_inv_e _ _ EXT _ HR)|].
  split; [exact (fs_inv_e _ _ (bext_restrictv _ _ _ EXT) _ HF)|].
  split; [exact (rest_inv_e _ _ (bext_maskv _ _ _ EXT) _ HRest)|].
  split.
  { unfold model_inv, ledger_inv in HM |- *.
    destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
    refine (conj V1 (conj Hpaid (conj V3 (conj V4 (conj V5 (conj V6 (conj V7 (conj L1 (conj L2 (conj L3 (conj L4 (conj _ (conj L6 (conj L7 (conj L8 L9))))))))))))))).
    apply depot_vm_grow_band; [exact HI3 | exact L5 |]. intros p Hp. exact (proj1 (Htp1 p Hp)). }
  split; [exact HI3|].
  apply (bandtp_grow _ tp); [exact (bandtp_inv_e _ _ EXT _ HB)|].
  intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [|left; exact Hp]. right. intros _. exact (proj2 (Htp1 p Hp)).
Qed.

Theorem AInvX_ext : ltac2:(tb__ "0|4|
S1S9S9S16SfQ40M0A1M1A1M2G2S42S47R6R5R3R1A4S11S20S43S8R6A1A2S20S43S8R5A1A2A2G1S44G1R1R5A3ScS2cS10G0R2A2M3A1S21S20S43S8R8A1A2G3S29G3S46A2A3A2F_;Fp;S2aS29S45R4S17G1R5R6A3A2S4aR9A1A2S49R9A1A2S47RaR8S17G1R6R7A3R5A4F_;F_;F_;F_;Fmd;Ftp1;Ftp;Frho';Frho;FA;").
Proof.
  intros A rho rho' tp tp1 md (HG & HR & HF & HRest & HM & HI3 & HB) EXT Htp1 Hpaid.
  split; [exact HG|]. split; [exact (rtc_inv_e _ _ EXT _ HR)|].
  split; [exact (fs_inv_e _ _ (bext_restrictv _ _ _ EXT) _ HF)|].
  split; [exact (rest_inv_nd_e _ _ (bext_maskv _ _ _ EXT) _ HRest)|].
  split.
  { unfold model_inv_nd, ledger_inv_nd in HM |- *.
    destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
    exact (conj V1 (conj Hpaid (conj V3 (conj V4 (conj V5 (conj V6 (conj V7 (conj L1 (conj L2 (conj L3 (conj L4 (conj I (conj I (conj L7 (conj L8 L9))))))))))))))). }
  split; [exact HI3|].
  apply (bandtp_grow _ tp); [exact (bandtp_inv_e _ _ EXT _ HB)|].
  intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [|left; exact Hp]. right. intros _. exact (proj2 (Htp1 p Hp)).
Qed.

Lemma view_bext : ltac2:(tb__ "0|4|
S9S9SfQ40A1SeSbS18SfQ8A1M0A1M1S8R2R1A2S8R3R1A2M2A3ScSbG1G2S19G0A1M3A3SbG1SaVsegs;R1A2G3A3A2A2Fa;S11S20Vsegs;S8R3A1A2S20Vsegs;S8R2A1A2A2F_;Frho';Frho;").
Proof.
  intros rho rho' H z b Hz.
  destruct (Z_le_dec 0 z); [destruct (Z_lt_dec z (2 ^ 64))|]; [|rewrite view_out in Hz by lia; discriminate | rewrite view_out in Hz by lia; discriminate].
  rewrite view_in in Hz |- * by lia. unfold rd_of in Hz |- *.
  destruct (H (Z_to_bv 64 z)) as [E|[E1 E2]].
  - rewrite E. exact Hz.
  - rewrite E1, E2 in Hz. discriminate.
Qed.

Theorem AInvA_reveal : ltac2:(tb__ "0|8|
S1S9S9S16SfQ40M0A1M1A1M2G2S42S2dVsegs;R6R5R3R1A5G1SeSbS18SfQ8A1M3A1M4S8R6R1A2S8R7R1A2M5A3ScSbG4G5S19G3A1M6A3SbG4SaVsegs;R1A2G6A3A2A2Fa;G1S44G1R1R5A3ScS2cS10G0R2A2M7A1S21S20Vsegs;S8R8A1A2G7S29G7S46A2A3A2F_;Fp;S2aS29S45R4S17G1R5R6A3A2S4aR9A1A2S49R9A1A2S2dVsegs;RaR8S17G1R6R7A3R5A5F_;F_;F_;F_;Fmd;Ftp1;Ftp;Frho';Frho;FA;").
Proof. intros A rho rho' tp tp1 md HA H Htp1 Hpaid. exact (AInvA_ext A rho rho' tp tp1 md HA (view_bext rho rho' H) Htp1 Hpaid). Qed.

End WithSegs.

Theorem AInvX_reveal : ltac2:(tb__ "0|8|
S1S9S9S16SfQ40M0A1M1A1M2G2S42S47R6R5R3R1A4G1SeSbS18SfQ8A1M3A1M4S8R6R1A2S8R7R1A2M5A3ScSbG4G5S19G3A1M6A3SbG4SaS43R1A2G6A3A2A2Fa;G1S44G1R1R5A3ScS2cS10G0R2A2M7A1S21S20S43S8R8A1A2G7S29G7S46A2A3A2F_;Fp;S2aS29S45R4S17G1R5R6A3A2S4aR9A1A2S49R9A1A2S47RaR8S17G1R6R7A3R5A4F_;F_;F_;F_;Fmd;Ftp1;Ftp;Frho';Frho;FA;").
Proof. intros A rho rho' tp tp1 md HA H Htp1 Hpaid. exact (AInvX_ext A rho rho' tp tp1 md HA (view_bext segsA rho rho' H) Htp1 Hpaid). Qed.
End InvReveal.

(* [comment removed for export] *)
Module MallocMemoSP.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "A_globals"; "malloc_depth"; "mkA"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@Corelib.Init.Datatypes"; "nil"; "cons"; "list"; "option"; "true"; "nat"; "pair"; "app"; "false"; "prod"; "None"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "axst"; "sym_runA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "SVar"; "ss_regs"; "SPUle"; "FcsrFrm0"; "mkSS"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "leaf"; "upd"; "F_cls"; "F_pop"; "LIVE"; "prune_sw"; "HAVOC_CALLER"; "set_obj_from_end"; "MSENT"; "MSRET"; "V_RZ"; "C2_ru"; "HAVOC_C8"; "LUe"; "O_L"; "O_UB"; "O_st"; "ube"; "BP"; "BR"; "BSH"; "BU"; "C1g"; "C1g_regs"; "C2p"; "C2p0"; "C2r"; "C2r0"; "C3"; "C5"; "C5b"; "C5c"; "C5d"; "C5e"; "C5m1"; "C5m2"; "C6"; "C6b"; "C6l"; "C6m"; "C7"; "C7p"; "C8"; "C8ma"; "C8mpa"; "C8p"; "C9"; "C9a"; "C9b"; "C9p"; "C9pa"; "C9pb"; "E2a"; "E2b"; "E3p"; "E3r"; "E4d"; "E5f"; "E5j"; "E5m1"; "E5m2"; "E5n"; "E5s1"; "E5s2"; "E6j"; "E6l"; "E6m"; "E6s"; "E7c1"; "E7c2"; "E7p"; "E7q1"; "E7q2"; "E8a"; "E8b"; "E8pa"; "E8pb"; "F_gen"; "HAVOC_JOIN"; "HAVOC_JOIN6"; "LLe"; "LPe"; "LRe"; "O_R"; "O_Uz"; "O_pcc"; "O_pcc0"; "O_pck"; "O_pcs"; "PIECES"; "V_CLS"; "V_SIZE"; "creg7a"; "creg7b"; "creg7c"; "creg7d"; "creg_a"; "creg_b"; "prune_call"; "run2"; "run3p"; "run3r"; "run4"; "run5"; "run5b"; "run5c"; "run5d"; "run5e"; "run6"; "run6b"; "run6l"; "run7"; "run7p"; "run8"; "run8p"; "run9a"; "run9b"; "run9pa"; "run9pb"; "sreg1"; "sreg2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSP"; "m_E2b"; "m_run7"; "m_C9"; "m_C9p"; "m_E5s1"; "m_E7c1"; "m_E7q1"; "m_run2"; "m_run5"; "m_run5b"; "m_run6"; "m_run7p"; "m_run8"; "m_run8p"; "m_C1g"; "m_C2p"; "m_C2p0"; "m_C2r"; "m_C2r0"; "m_C3"; "m_C5"; "m_C5b"; "m_C5c"; "m_C5d"; "m_C5e"; "m_C5m1"; "m_C5m2"; "m_C6"; "m_C6b"; "m_C6l"; "m_C6m"; "m_C7"; "m_C7p"; "m_C8"; "m_C8ma"; "m_C8mpa"; "m_C8p"; "m_C9a"; "m_C9b"; "m_C9pa"; "m_C9pb"; "m_E2a"; "m_E3p"; "m_E4d"; "m_E5f"; "m_E5m1"; "m_E5m2"; "m_E5n"; "m_E5s2"; "m_E6j"; "m_E6l"; "m_E6m"; "m_E7c2"; "m_E7p"; "m_E7q2"; "m_E8a"; "m_E8pa"; "m_run3p"; "m_run3r"; "m_run4"; "m_run5c"; "m_run5d"; "m_run5e"; "m_run6b"; "m_run6l"; "m_E3r"; "m_E5j"; "m_E6s"; "m_E8b"; "m_E8pb"; "m_creg7a"; "m_creg7b"; "m_creg7c"; "m_creg7d"; "m_creg_a"; "m_creg_b"; "m_run9a"; "m_run9b"; "m_run9pa"; "m_run9pb"; "m_sreg1"; "m_sreg2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "F_geom_fn"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "F_s1"; "RT_m1"; "V_TSZ"; "sw_s1"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import CertMallocSP.
Import ListNotations.
Open Scope Z_scope.

Ltac MallocMemoSP_sub0 t := t.
Ltac MallocMemoSP_all0 := idtac.
Definition m_C1g : axst := ltac2:(tb__ "0|2|
S4S20Z40bacS39Sf0S1fS12S18A1SfS1aSfS1aS9S1aSf6SfS1aS7S1U0A1M0A1S2A3A3Sf4A3S8S1aA1A3SfS19SfS19SfS19SfS19S6G0S0A2S5S3A1A3Sf1A3Sf3A3SfS19S9S19S1eS1bZ1A1S1cSf5A1M1A2S9S19S1eG1S1bZ2A1A2S8S19A1A3A3S6fA3A3Sf2S10A9S8S11S18S18A2A1A2").
Lemma m_C1g_eq : ltac2:(tb__ "0|0|
S13S15S38S1U0A1S0Z2A3SacA3"). Proof. cbv delta [C1g m_C1g]; cbv beta zeta. MallocMemoSP_all0. reflexivity. Qed.
Ltac MallocMemoSP_sub1 t := let t := MallocMemoSP_sub0 t in lazymatch (eval pattern (C1g (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C1g) end.
Ltac MallocMemoSP_all1 := MallocMemoSP_all0; MemoFast.memo_rw m_C1g_eq.
Definition m_run2 : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Z40d40S8S21A1A3SacScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run2_eq : ltac2:(tb__ "0|0|
S13SaS14A1S85S1U0A1S0Z2A3Sa5A3"). Proof. cbv delta [run2 m_run2]; cbv beta zeta. MallocMemoSP_all1. reflexivity. Qed.
Ltac MallocMemoSP_sub2 t := let t := MallocMemoSP_sub1 t in lazymatch (eval pattern (run2 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_run2) end.
Ltac MallocMemoSP_all2 := MallocMemoSP_all1; MemoFast.memo_rw m_run2_eq.
Definition m_E2a : axst := ltac2:(tb__ "0|0|
S22U0Sa5A2").
Lemma m_E2a_eq : ltac2:(tb__ "0|0|
S13S15S56S1U0A1S0Z2A3Sc7A3"). Proof. cbv delta [E2a m_E2a]; cbv beta zeta. MallocMemoSP_all2. reflexivity. Qed.
Ltac MallocMemoSP_sub3 t := let t := MallocMemoSP_sub2 t in lazymatch (eval pattern (E2a (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E2a) end.
Ltac MallocMemoSP_all3 := MallocMemoSP_all2; MemoFast.memo_rw m_E2a_eq.
Definition m_E2b : axst := ltac2:(tb__ "0|0|
S22U1Sa5A2").
Lemma m_E2b_eq : ltac2:(tb__ "0|0|
S13S15S57S1U0A1S0Z2A3S9eA3"). Proof. cbv delta [E2b m_E2b]; cbv beta zeta. MallocMemoSP_all3. reflexivity. Qed.
Ltac MallocMemoSP_sub4 t := let t := MallocMemoSP_sub3 t in lazymatch (eval pattern (E2b (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E2b) end.
Ltac MallocMemoSP_all4 := MallocMemoSP_all3; MemoFast.memo_rw m_E2b_eq.
Definition m_creg_a : sv := ltac2:(tb__ "0|0|
S9cS18U8S1dS17Sc7A1A1S1bZ0A1A4").
Lemma m_creg_a_eq : ltac2:(tb__ "0|0|
S13S18S82S1U0A1S0Z2A3Se8A3"). Proof. cbv delta [creg_a m_creg_a]; cbv beta zeta. MallocMemoSP_all4. reflexivity. Qed.
Ltac MallocMemoSP_sub5 t := let t := MallocMemoSP_sub4 t in lazymatch (eval pattern (creg_a (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_creg_a) end.
Ltac MallocMemoSP_all5 := MallocMemoSP_all4; MemoFast.memo_rw m_creg_a_eq.
Definition m_creg_b : sv := ltac2:(tb__ "0|0|
S9cS18U8S1dS17S9eA1A1S1bZ0A1A4").
Lemma m_creg_b_eq : ltac2:(tb__ "0|0|
S13S18S83S1U0A1S0Z2A3Se9A3"). Proof. cbv delta [creg_b m_creg_b]; cbv beta zeta. MallocMemoSP_all5. reflexivity. Qed.
Ltac MallocMemoSP_sub6 t := let t := MallocMemoSP_sub5 t in lazymatch (eval pattern (creg_b (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_creg_b) end.
Ltac MallocMemoSP_all6 := MallocMemoSP_all5; MemoFast.memo_rw m_creg_b_eq.
Definition m_C2p0 : axst := ltac2:(tb__ "0|0|
S23S1U0A1S0Z2S9eZ40d40S2dS9S1aS77S9S1aS7aS9S1aS79S9S1aS32S8S1aA1A3A3A3A3ScS8S19A1A9").
Lemma m_C2p0_eq : ltac2:(tb__ "0|0|
S13S15S3bS1U0A1S0Z2A3SaeA3"). Proof. cbv delta [C2p0 m_C2p0]; cbv beta zeta. MallocMemoSP_all6. reflexivity. Qed.
Ltac MallocMemoSP_sub7 t := let t := MallocMemoSP_sub6 t in lazymatch (eval pattern (C2p0 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C2p0) end.
Ltac MallocMemoSP_all7 := MallocMemoSP_all6; MemoFast.memo_rw m_C2p0_eq.
Definition m_C2r0 : axst := ltac2:(tb__ "0|0|
S23S1U0A1S0Z2S9eZ40d40S2dS9S1aS78S9S1aS32S8S1aA1A3A3ScS8S19A1A9").
Lemma m_C2r0_eq : ltac2:(tb__ "0|0|
S13S15S3dS1U0A1S0Z2A3Sb0A3"). Proof. cbv delta [C2r0 m_C2r0]; cbv beta zeta. MallocMemoSP_all7. reflexivity. Qed.
Ltac MallocMemoSP_sub8 t := let t := MallocMemoSP_sub7 t in lazymatch (eval pattern (C2r0 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C2r0) end.
Ltac MallocMemoSP_all8 := MallocMemoSP_all7; MemoFast.memo_rw m_C2r0_eq.
Definition m_C2p : axst := ltac2:(tb__ "0|0|
S9dSfS19S24S25A3SaeA2").
Lemma m_C2p_eq : ltac2:(tb__ "0|0|
S13S15S3aS1U0A1S0Z2A3SadA3"). Proof. cbv delta [C2p m_C2p]; cbv beta zeta. MallocMemoSP_all8. reflexivity. Qed.
Ltac MallocMemoSP_sub9 t := let t := MallocMemoSP_sub8 t in lazymatch (eval pattern (C2p (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C2p) end.
Ltac MallocMemoSP_all9 := MallocMemoSP_all8; MemoFast.memo_rw m_C2p_eq.
Definition m_C2r : axst := ltac2:(tb__ "0|0|
S9dS24Sb0A2").
Lemma m_C2r_eq : ltac2:(tb__ "0|0|
S13S15S3cS1U0A1S0Z2A3SafA3"). Proof. cbv delta [C2r m_C2r]; cbv beta zeta. MallocMemoSP_all9. reflexivity. Qed.
Ltac MallocMemoSP_sub10 t := let t := MallocMemoSP_sub9 t in lazymatch (eval pattern (C2r (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C2r) end.
Ltac MallocMemoSP_all10 := MallocMemoSP_all9; MemoFast.memo_rw m_C2r_eq.
Definition m_run3p : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Z40e58S9S21Z3c614S8S21A1A3A3SadScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run3p_eq : ltac2:(tb__ "0|0|
S13SaS14A1S86S1U0A1S0Z2A3Sd7A3"). Proof. cbv delta [run3p m_run3p]; cbv beta zeta. MallocMemoSP_all10. reflexivity. Qed.
Ltac MallocMemoSP_sub11 t := let t := MallocMemoSP_sub10 t in lazymatch (eval pattern (run3p (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_run3p) end.
Ltac MallocMemoSP_all11 := MallocMemoSP_all10; MemoFast.memo_rw m_run3p_eq.
Definition m_run3r : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Z40e58S9S21Z3c614S8S21A1A3A3SafScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run3r_eq : ltac2:(tb__ "0|0|
S13SaS14A1S87S1U0A1S0Z2A3Sd8A3"). Proof. cbv delta [run3r m_run3r]; cbv beta zeta. MallocMemoSP_all11. reflexivity. Qed.
Ltac MallocMemoSP_sub12 t := let t := MallocMemoSP_sub11 t in lazymatch (eval pattern (run3r (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_run3r) end.
Ltac MallocMemoSP_all12 := MallocMemoSP_all11; MemoFast.memo_rw m_run3r_eq.
Definition m_E3p : axst := ltac2:(tb__ "0|0|
S22U0Sd7A2").
Lemma m_E3p_eq : ltac2:(tb__ "0|0|
S13S15S58S1U0A1S0Z2A3Sc8A3"). Proof. cbv delta [E3p m_E3p]; cbv beta zeta. MallocMemoSP_all12. reflexivity. Qed.
Ltac MallocMemoSP_sub13 t := let t := MallocMemoSP_sub12 t in lazymatch (eval pattern (E3p (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E3p) end.
Ltac MallocMemoSP_all13 := MallocMemoSP_all12; MemoFast.memo_rw m_E3p_eq.
Definition m_E3r : axst := ltac2:(tb__ "0|0|
S22U0Sd8A2").
Lemma m_E3r_eq : ltac2:(tb__ "0|0|
S13S15S59S1U0A1S0Z2A3SdfA3"). Proof. cbv delta [E3r m_E3r]; cbv beta zeta. MallocMemoSP_all13. reflexivity. Qed.
Ltac MallocMemoSP_sub14 t := let t := MallocMemoSP_sub13 t in lazymatch (eval pattern (E3r (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E3r) end.
Ltac MallocMemoSP_all14 := MallocMemoSP_all13; MemoFast.memo_rw m_E3r_eq.
Definition m_C3 : axst := ltac2:(tb__ "0|0|
S23S1U0A1S0Z2Sc8Z3c614S8S11SdS18A2A1S7bS10S8S19A1A9").
Lemma m_C3_eq : ltac2:(tb__ "0|0|
S13S15S3eS1U0A1S0Z2A3Sb1A3"). Proof. cbv delta [C3 m_C3]; cbv beta zeta. MallocMemoSP_all14. reflexivity. Qed.
Ltac MallocMemoSP_sub15 t := let t := MallocMemoSP_sub14 t in lazymatch (eval pattern (C3 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C3) end.
Ltac MallocMemoSP_all15 := MallocMemoSP_all14; MemoFast.memo_rw m_C3_eq.
Definition m_run4 : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Z7e9e4S8S21A1A3Sb1ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run4_eq : ltac2:(tb__ "0|0|
S13SaS14A1S88S1U0A1S0Z2A3Sd9A3"). Proof. cbv delta [run4 m_run4]; cbv beta zeta. MallocMemoSP_all15. reflexivity. Qed.
Ltac MallocMemoSP_sub16 t := let t := MallocMemoSP_sub15 t in lazymatch (eval pattern (run4 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_run4) end.
Ltac MallocMemoSP_all16 := MallocMemoSP_all15; MemoFast.memo_rw m_run4_eq.
Definition m_E4d : axst := ltac2:(tb__ "0|0|
S22U0Sd9A2").
Lemma m_E4d_eq : ltac2:(tb__ "0|0|
S13S15S5aS1U0A1S0Z2A3Sc9A3"). Proof. cbv delta [E4d m_E4d]; cbv beta zeta. MallocMemoSP_all16. reflexivity. Qed.
Ltac MallocMemoSP_sub17 t := let t := MallocMemoSP_sub16 t in lazymatch (eval pattern (E4d (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E4d) end.
Ltac MallocMemoSP_all17 := MallocMemoSP_all16; MemoFast.memo_rw m_E4d_eq.
Definition m_C5 : axst := ltac2:(tb__ "0|1|
S84S23S1U0A1S0Z2Sc9Z7ec58S9S11SdS18A2M0SeSdS18UaS1cPaaA1A4S9G0SeSdS18U1S1bZ3c720A1A4S28A3A3S8S1aA1S10S8S19A1A9A1").
Lemma m_C5_eq : ltac2:(tb__ "0|0|
S13S15S3fS1U0A1S0Z2A3Sb2A3"). Proof. cbv delta [C5 m_C5]; cbv beta zeta. MallocMemoSP_all17. reflexivity. Qed.
Ltac MallocMemoSP_sub18 t := let t := MallocMemoSP_sub17 t in lazymatch (eval pattern (C5 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C5) end.
Ltac MallocMemoSP_all18 := MallocMemoSP_all17; MemoFast.memo_rw m_C5_eq.
Definition m_run5 : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Z3c774S9S21Z3c80cS8S21A1A3A3Sb2ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run5_eq : ltac2:(tb__ "0|0|
S13SaS14A1S89S1U0A1S0Z2A3Sa6A3"). Proof. cbv delta [run5 m_run5]; cbv beta zeta. MallocMemoSP_all18. reflexivity. Qed.
Ltac MallocMemoSP_sub19 t := let t := MallocMemoSP_sub18 t in lazymatch (eval pattern (run5 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_run5) end.
Ltac MallocMemoSP_all19 := MallocMemoSP_all18; MemoFast.memo_rw m_run5_eq.
Definition m_E5n : axst := ltac2:(tb__ "0|0|
S22U0Sa6A2").
Lemma m_E5n_eq : ltac2:(tb__ "0|0|
S13S15S5fS1U0A1S0Z2A3ScdA3"). Proof. cbv delta [E5n m_E5n]; cbv beta zeta. MallocMemoSP_all19. reflexivity. Qed.
Ltac MallocMemoSP_sub20 t := let t := MallocMemoSP_sub19 t in lazymatch (eval pattern (E5n (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E5n) end.
Ltac MallocMemoSP_all20 := MallocMemoSP_all19; MemoFast.memo_rw m_E5n_eq.
Definition m_E5f : axst := ltac2:(tb__ "0|0|
S22U1Sa6A2").
Lemma m_E5f_eq : ltac2:(tb__ "0|0|
S13S15S5bS1U0A1S0Z2A3ScaA3"). Proof. cbv delta [E5f m_E5f]; cbv beta zeta. MallocMemoSP_all20. reflexivity. Qed.
Ltac MallocMemoSP_sub21 t := let t := MallocMemoSP_sub20 t in lazymatch (eval pattern (E5f (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E5f) end.
Ltac MallocMemoSP_all21 := MallocMemoSP_all20; MemoFast.memo_rw m_E5f_eq.
Definition m_C5b : axst := ltac2:(tb__ "0|2|
S23S1U0A1S0Z2ScaZ3c774S9S11SdS18A2M0SeSdS18U8S1cS7cA1M1A4S9G0SeSdS18UaG1A4S8G0A1A3A3S8S1aA1S10S8S19A1A9").
Lemma m_C5b_eq : ltac2:(tb__ "0|0|
S13S15S40S1U0A1S0Z2A3Sb3A3"). Proof. cbv delta [C5b m_C5b]; cbv beta zeta. MallocMemoSP_all21. reflexivity. Qed.
Ltac MallocMemoSP_sub22 t := let t := MallocMemoSP_sub21 t in lazymatch (eval pattern (C5b (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C5b) end.
Ltac MallocMemoSP_all22 := MallocMemoSP_all21; MemoFast.memo_rw m_C5b_eq.
Definition m_run5b : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Z3c7e0S8S21A1A3Sb3ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run5b_eq : ltac2:(tb__ "0|0|
S13SaS14A1S8aS1U0A1S0Z2A3Sa7A3"). Proof. cbv delta [run5b m_run5b]; cbv beta zeta. MallocMemoSP_all22. reflexivity. Qed.
Ltac MallocMemoSP_sub23 t := let t := MallocMemoSP_sub22 t in lazymatch (eval pattern (run5b (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_run5b) end.
Ltac MallocMemoSP_all23 := MallocMemoSP_all22; MemoFast.memo_rw m_run5b_eq.
Definition m_E5s1 : axst := ltac2:(tb__ "0|0|
S22U0Sa7A2").
Lemma m_E5s1_eq : ltac2:(tb__ "0|0|
S13S15S60S1U0A1S0Z2A3Sa2A3"). Proof. cbv delta [E5s1 m_E5s1]; cbv beta zeta. MallocMemoSP_all23. reflexivity. Qed.
Ltac MallocMemoSP_sub24 t := let t := MallocMemoSP_sub23 t in lazymatch (eval pattern (E5s1 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E5s1) end.
Ltac MallocMemoSP_all24 := MallocMemoSP_all23; MemoFast.memo_rw m_E5s1_eq.
Definition m_E5s2 : axst := ltac2:(tb__ "0|0|
S22U1Sa7A2").
Lemma m_E5s2_eq : ltac2:(tb__ "0|0|
S13S15S61S1U0A1S0Z2A3SceA3"). Proof. cbv delta [E5s2 m_E5s2]; cbv beta zeta. MallocMemoSP_all24. reflexivity. Qed.
Ltac MallocMemoSP_sub25 t := let t := MallocMemoSP_sub24 t in lazymatch (eval pattern (E5s2 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E5s2) end.
Ltac MallocMemoSP_all25 := MallocMemoSP_all24; MemoFast.memo_rw m_E5s2_eq.
Definition m_sreg1 : sv := ltac2:(tb__ "0|0|
S9cS18U8S1dS17Sa2A1A1S1bZ0A1A4").
Lemma m_sreg1_eq : ltac2:(tb__ "0|0|
S13S18S99S1U0A1S0Z2A3SeeA3"). Proof. cbv delta [sreg1 m_sreg1]; cbv beta zeta. MallocMemoSP_all25. reflexivity. Qed.
Ltac MallocMemoSP_sub26 t := let t := MallocMemoSP_sub25 t in lazymatch (eval pattern (sreg1 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_sreg1) end.
Ltac MallocMemoSP_all26 := MallocMemoSP_all25; MemoFast.memo_rw m_sreg1_eq.
Definition m_sreg2 : sv := ltac2:(tb__ "0|0|
S9cS18U8S1dS17SceA1A1S1bZ0A1A4").
Lemma m_sreg2_eq : ltac2:(tb__ "0|0|
S13S18S9aS1U0A1S0Z2A3SefA3"). Proof. cbv delta [sreg2 m_sreg2]; cbv beta zeta. MallocMemoSP_all26. reflexivity. Qed.
Ltac MallocMemoSP_sub27 t := let t := MallocMemoSP_sub26 t in lazymatch (eval pattern (sreg2 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_sreg2) end.
Ltac MallocMemoSP_all27 := MallocMemoSP_all26; MemoFast.memo_rw m_sreg2_eq.
Definition m_C5c : axst := ltac2:(tb__ "0|1|
S27S26S23S1U0A1S0Z2Sa2Z3c7e0S9S11SdS18A2M0SeSdS18U8S1cS7dA1A4S9G0SeSdS18UaS1cPb4A1A4S9G0SeSdS18UbS1cPabA1A4S8G0A1A3A3A3S8S1aA1ScSfS19S24S25A3A9A2").
Lemma m_C5c_eq : ltac2:(tb__ "0|0|
S13S15S41S1U0A1S0Z2A3Sb4A3"). Proof. cbv delta [C5c m_C5c]; cbv beta zeta. MallocMemoSP_all27. reflexivity. Qed.
Ltac MallocMemoSP_sub28 t := let t := MallocMemoSP_sub27 t in lazymatch (eval pattern (C5c (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C5c) end.
Ltac MallocMemoSP_all28 := MallocMemoSP_all27; MemoFast.memo_rw m_C5c_eq.
Definition m_run5c : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Zdb004S8S21A1A3Sb4ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run5c_eq : ltac2:(tb__ "0|0|
S13SaS14A1S8bS1U0A1S0Z2A3SdaA3"). Proof. cbv delta [run5c m_run5c]; cbv beta zeta. MallocMemoSP_all28. reflexivity. Qed.
Ltac MallocMemoSP_sub29 t := let t := MallocMemoSP_sub28 t in lazymatch (eval pattern (run5c (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_run5c) end.
Ltac MallocMemoSP_all29 := MallocMemoSP_all28; MemoFast.memo_rw m_run5c_eq.
Definition m_E5m1 : axst := ltac2:(tb__ "0|0|
S22U0SdaA2").
Lemma m_E5m1_eq : ltac2:(tb__ "0|0|
S13S15S5dS1U0A1S0Z2A3ScbA3"). Proof. cbv delta [E5m1 m_E5m1]; cbv beta zeta. MallocMemoSP_all29. reflexivity. Qed.
Ltac MallocMemoSP_sub30 t := let t := MallocMemoSP_sub29 t in lazymatch (eval pattern (E5m1 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E5m1) end.
Ltac MallocMemoSP_all30 := MallocMemoSP_all29; MemoFast.memo_rw m_E5m1_eq.
Definition m_C5m1 : axst := ltac2:(tb__ "0|1|
S23S1U0A1S0Z2ScbS2aS9S11SdS18A2M0SeSdS18UaS36A4S9G0SeSdS18UcS72A4S8G0A1A3A3S8S1aA1S10S8S19A1A9").
Lemma m_C5m1_eq : ltac2:(tb__ "0|0|
S13S15S44S1U0A1S0Z2A3Sb7A3"). Proof. cbv delta [C5m1 m_C5m1]; cbv beta zeta. MallocMemoSP_all30. reflexivity. Qed.
Ltac MallocMemoSP_sub31 t := let t := MallocMemoSP_sub30 t in lazymatch (eval pattern (C5m1 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C5m1) end.
Ltac MallocMemoSP_all31 := MallocMemoSP_all30; MemoFast.memo_rw m_C5m1_eq.
Definition m_C5d : axst := ltac2:(tb__ "0|0|
S29U3S30S23S1U0A1S0Z2Sb7S2bS28S8S1aA1S10S8S19A1A9A3").
Lemma m_C5d_eq : ltac2:(tb__ "0|0|
S13S15S42S1U0A1S0Z2A3Sb5A3"). Proof. cbv delta [C5d m_C5d]; cbv beta zeta. MallocMemoSP_all31. reflexivity. Qed.
Ltac MallocMemoSP_sub32 t := let t := MallocMemoSP_sub31 t in lazymatch (eval pattern (C5d (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C5d) end.
Ltac MallocMemoSP_all32 := MallocMemoSP_all31; MemoFast.memo_rw m_C5d_eq.
Definition m_run5d : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Zdb004S8S21A1A3Sb5ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run5d_eq : ltac2:(tb__ "0|0|
S13SaS14A1S8cS1U0A1S0Z2A3SdbA3"). Proof. cbv delta [run5d m_run5d]; cbv beta zeta. MallocMemoSP_all32. reflexivity. Qed.
Ltac MallocMemoSP_sub33 t := let t := MallocMemoSP_sub32 t in lazymatch (eval pattern (run5d (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_run5d) end.
Ltac MallocMemoSP_all33 := MallocMemoSP_all32; MemoFast.memo_rw m_run5d_eq.
Definition m_E5m2 : axst := ltac2:(tb__ "0|0|
S22U0SdbA2").
Lemma m_E5m2_eq : ltac2:(tb__ "0|0|
S13S15S5eS1U0A1S0Z2A3SccA3"). Proof. cbv delta [E5m2 m_E5m2]; cbv beta zeta. MallocMemoSP_all33. reflexivity. Qed.
Ltac MallocMemoSP_sub34 t := let t := MallocMemoSP_sub33 t in lazymatch (eval pattern (E5m2 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E5m2) end.
Ltac MallocMemoSP_all34 := MallocMemoSP_all33; MemoFast.memo_rw m_E5m2_eq.
Definition m_C5m2 : axst := ltac2:(tb__ "0|1|
S23S1U0A1S0Z2SccS2aS9S11SdS18A2M0SeSdS18UaS35A4S9G0SeSdS18UcS74A4S8G0A1A3A3S8S1aA1S10S8S19A1A9").
Lemma m_C5m2_eq : ltac2:(tb__ "0|0|
S13S15S45S1U0A1S0Z2A3Sb8A3"). Proof. cbv delta [C5m2 m_C5m2]; cbv beta zeta. MallocMemoSP_all34. reflexivity. Qed.
Ltac MallocMemoSP_sub35 t := let t := MallocMemoSP_sub34 t in lazymatch (eval pattern (C5m2 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C5m2) end.
Ltac MallocMemoSP_all35 := MallocMemoSP_all34; MemoFast.memo_rw m_C5m2_eq.
Definition m_C5e : axst := ltac2:(tb__ "0|1|
S29U0M0S75S23S1G0A1S0Z2Sb8S2bS28S8S1aA1S10S8S19A1A9A3").
Lemma m_C5e_eq : ltac2:(tb__ "0|0|
S13S15S43S1U0A1S0Z2A3Sb6A3"). Proof. cbv delta [C5e m_C5e]; cbv beta zeta. MallocMemoSP_all35. reflexivity. Qed.
Ltac MallocMemoSP_sub36 t := let t := MallocMemoSP_sub35 t in lazymatch (eval pattern (C5e (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C5e) end.
Ltac MallocMemoSP_all36 := MallocMemoSP_all35; MemoFast.memo_rw m_C5e_eq.
Definition m_run5e : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Z3c80cS8S21A1A3Sb6ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run5e_eq : ltac2:(tb__ "0|0|
S13SaS14A1S8dS1U0A1S0Z2A3SdcA3"). Proof. cbv delta [run5e m_run5e]; cbv beta zeta. MallocMemoSP_all36. reflexivity. Qed.
Ltac MallocMemoSP_sub37 t := let t := MallocMemoSP_sub36 t in lazymatch (eval pattern (run5e (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_run5e) end.
Ltac MallocMemoSP_all37 := MallocMemoSP_all36; MemoFast.memo_rw m_run5e_eq.
Definition m_E5j : axst := ltac2:(tb__ "0|0|
S22U0SdcA2").
Lemma m_E5j_eq : ltac2:(tb__ "0|0|
S13S15S5cS1U0A1S0Z2A3Se0A3"). Proof. cbv delta [E5j m_E5j]; cbv beta zeta. MallocMemoSP_all37. reflexivity. Qed.
Ltac MallocMemoSP_sub38 t := let t := MallocMemoSP_sub37 t in lazymatch (eval pattern (E5j (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E5j) end.
Ltac MallocMemoSP_all38 := MallocMemoSP_all37; MemoFast.memo_rw m_E5j_eq.
Definition m_C6 : axst := ltac2:(tb__ "0|0|
S27S26S29U3S30S23S1U0A1S0Z2ScdZ3c80cS71S8S1aA1ScSfS19S24S25A3A9A3A2").
Lemma m_C6_eq : ltac2:(tb__ "0|0|
S13S15S46S1U0A1S0Z2A3Sb9A3"). Proof. cbv delta [C6 m_C6]; cbv beta zeta. MallocMemoSP_all38. reflexivity. Qed.
Ltac MallocMemoSP_sub39 t := let t := MallocMemoSP_sub38 t in lazymatch (eval pattern (C6 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C6) end.
Ltac MallocMemoSP_all39 := MallocMemoSP_all38; MemoFast.memo_rw m_C6_eq.
Definition m_run6 : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Z5f9f8S9S21Z3c82cS8S21A1A3A3Sb9ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run6_eq : ltac2:(tb__ "0|0|
S13SaS14A1S8eS1U0A1S0Z2A3Sa8A3"). Proof. cbv delta [run6 m_run6]; cbv beta zeta. MallocMemoSP_all39. reflexivity. Qed.
Ltac MallocMemoSP_sub40 t := let t := MallocMemoSP_sub39 t in lazymatch (eval pattern (run6 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_run6) end.
Ltac MallocMemoSP_all40 := MallocMemoSP_all39; MemoFast.memo_rw m_run6_eq.
Definition m_E6s : axst := ltac2:(tb__ "0|0|
S22U0Sa8A2").
Lemma m_E6s_eq : ltac2:(tb__ "0|0|
S13S15S65S1U0A1S0Z2A3Se1A3"). Proof. cbv delta [E6s m_E6s]; cbv beta zeta. MallocMemoSP_all40. reflexivity. Qed.
Ltac MallocMemoSP_sub41 t := let t := MallocMemoSP_sub40 t in lazymatch (eval pattern (E6s (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E6s) end.
Ltac MallocMemoSP_all41 := MallocMemoSP_all40; MemoFast.memo_rw m_E6s_eq.
Definition m_E6l : axst := ltac2:(tb__ "0|0|
S22U1Sa8A2").
Lemma m_E6l_eq : ltac2:(tb__ "0|0|
S13S15S63S1U0A1S0Z2A3Sd0A3"). Proof. cbv delta [E6l m_E6l]; cbv beta zeta. MallocMemoSP_all41. reflexivity. Qed.
Ltac MallocMemoSP_sub42 t := let t := MallocMemoSP_sub41 t in lazymatch (eval pattern (E6l (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E6l) end.
Ltac MallocMemoSP_all42 := MallocMemoSP_all41; MemoFast.memo_rw m_E6l_eq.
Definition m_C6l : axst := ltac2:(tb__ "0|1|
S23S1U0A1S0Z2Sd0Z5f9f8S9S11SdS18A2M0SeSdS18U8S2fA4S8G0A1A3S8S1aA1S10S8S19A1A9").
Lemma m_C6l_eq : ltac2:(tb__ "0|0|
S13S15S48S1U0A1S0Z2A3SbbA3"). Proof. cbv delta [C6l m_C6l]; cbv beta zeta. MallocMemoSP_all42. reflexivity. Qed.
Ltac MallocMemoSP_sub43 t := let t := MallocMemoSP_sub42 t in lazymatch (eval pattern (C6l (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C6l) end.
Ltac MallocMemoSP_all43 := MallocMemoSP_all42; MemoFast.memo_rw m_C6l_eq.
Definition m_run6l : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Zdb004S8S21A1A3SbbScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run6l_eq : ltac2:(tb__ "0|0|
S13SaS14A1S90S1U0A1S0Z2A3SdeA3"). Proof. cbv delta [run6l m_run6l]; cbv beta zeta. MallocMemoSP_all43. reflexivity. Qed.
Ltac MallocMemoSP_sub44 t := let t := MallocMemoSP_sub43 t in lazymatch (eval pattern (run6l (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_run6l) end.
Ltac MallocMemoSP_all44 := MallocMemoSP_all43; MemoFast.memo_rw m_run6l_eq.
Definition m_E6m : axst := ltac2:(tb__ "0|0|
S22U0SdeA2").
Lemma m_E6m_eq : ltac2:(tb__ "0|0|
S13S15S64S1U0A1S0Z2A3Sd1A3"). Proof. cbv delta [E6m m_E6m]; cbv beta zeta. MallocMemoSP_all44. reflexivity. Qed.
Ltac MallocMemoSP_sub45 t := let t := MallocMemoSP_sub44 t in lazymatch (eval pattern (E6m (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E6m) end.
Ltac MallocMemoSP_all45 := MallocMemoSP_all44; MemoFast.memo_rw m_E6m_eq.
Definition m_C6m : axst := ltac2:(tb__ "0|1|
S23S1U0A1S0Z2Sd1S2aS9S11SdS18A2M0SeSdS18UaS37A4S9G0SeSdS18UcS2fA4S8G0A1A3A3S8S1aA1S10S8S19A1A9").
Lemma m_C6m_eq : ltac2:(tb__ "0|0|
S13S15S49S1U0A1S0Z2A3SbcA3"). Proof. cbv delta [C6m m_C6m]; cbv beta zeta. MallocMemoSP_all45. reflexivity. Qed.
Ltac MallocMemoSP_sub46 t := let t := MallocMemoSP_sub45 t in lazymatch (eval pattern (C6m (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C6m) end.
Ltac MallocMemoSP_all46 := MallocMemoSP_all45; MemoFast.memo_rw m_C6m_eq.
Definition m_C6b : axst := ltac2:(tb__ "0|0|
S29U2S76S23S1U0A1S0Z2SbcS2bS28S8S1aA1S10S8S19A1A9A3").
Lemma m_C6b_eq : ltac2:(tb__ "0|0|
S13S15S47S1U0A1S0Z2A3SbaA3"). Proof. cbv delta [C6b m_C6b]; cbv beta zeta. MallocMemoSP_all46. reflexivity. Qed.
Ltac MallocMemoSP_sub47 t := let t := MallocMemoSP_sub46 t in lazymatch (eval pattern (C6b (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C6b) end.
Ltac MallocMemoSP_all47 := MallocMemoSP_all46; MemoFast.memo_rw m_C6b_eq.
Definition m_run6b : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Z3c82cS8S21A1A3SbaScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run6b_eq : ltac2:(tb__ "0|0|
S13SaS14A1S8fS1U0A1S0Z2A3SddA3"). Proof. cbv delta [run6b m_run6b]; cbv beta zeta. MallocMemoSP_all47. reflexivity. Qed.
Ltac MallocMemoSP_sub48 t := let t := MallocMemoSP_sub47 t in lazymatch (eval pattern (run6b (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_run6b) end.
Ltac MallocMemoSP_all48 := MallocMemoSP_all47; MemoFast.memo_rw m_run6b_eq.
Definition m_E6j : axst := ltac2:(tb__ "0|0|
S22U0SddA2").
Lemma m_E6j_eq : ltac2:(tb__ "0|0|
S13S15S62S1U0A1S0Z2A3ScfA3"). Proof. cbv delta [E6j m_E6j]; cbv beta zeta. MallocMemoSP_all48. reflexivity. Qed.
Ltac MallocMemoSP_sub49 t := let t := MallocMemoSP_sub48 t in lazymatch (eval pattern (E6j (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E6j) end.
Ltac MallocMemoSP_all49 := MallocMemoSP_all48; MemoFast.memo_rw m_E6j_eq.
Definition m_C7 : axst := ltac2:(tb__ "0|0|
S27S26S23S1U0A1S0Z2ScfZ3c82cS70S8S1aA1ScSfS19S24S25A3A9A2").
Lemma m_C7_eq : ltac2:(tb__ "0|0|
S13S15S4aS1U0A1S0Z2A3SbdA3"). Proof. cbv delta [C7 m_C7]; cbv beta zeta. MallocMemoSP_all49. reflexivity. Qed.
Ltac MallocMemoSP_sub50 t := let t := MallocMemoSP_sub49 t in lazymatch (eval pattern (C7 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C7) end.
Ltac MallocMemoSP_all50 := MallocMemoSP_all49; MemoFast.memo_rw m_C7_eq.
Definition m_run7 : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Z3c8bcS9S21Z3ca04S8S21A1A3A3SbdScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run7_eq : ltac2:(tb__ "0|0|
S13SaS14A1S91S1U0A1S0Z2A3S9fA3"). Proof. cbv delta [run7 m_run7]; cbv beta zeta. MallocMemoSP_all50. reflexivity. Qed.
Ltac MallocMemoSP_sub51 t := let t := MallocMemoSP_sub50 t in lazymatch (eval pattern (run7 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_run7) end.
Ltac MallocMemoSP_all51 := MallocMemoSP_all50; MemoFast.memo_rw m_run7_eq.
Definition m_E7c1 : axst := ltac2:(tb__ "0|0|
S22U0S9fA2").
Lemma m_E7c1_eq : ltac2:(tb__ "0|0|
S13S15S66S1U0A1S0Z2A3Sa3A3"). Proof. cbv delta [E7c1 m_E7c1]; cbv beta zeta. MallocMemoSP_all51. reflexivity. Qed.
Ltac MallocMemoSP_sub52 t := let t := MallocMemoSP_sub51 t in lazymatch (eval pattern (E7c1 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E7c1) end.
Ltac MallocMemoSP_all52 := MallocMemoSP_all51; MemoFast.memo_rw m_E7c1_eq.
Definition m_E7c2 : axst := ltac2:(tb__ "0|0|
S22U1S9fA2").
Lemma m_E7c2_eq : ltac2:(tb__ "0|0|
S13S15S67S1U0A1S0Z2A3Sd2A3"). Proof. cbv delta [E7c2 m_E7c2]; cbv beta zeta. MallocMemoSP_all52. reflexivity. Qed.
Ltac MallocMemoSP_sub53 t := let t := MallocMemoSP_sub52 t in lazymatch (eval pattern (E7c2 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E7c2) end.
Ltac MallocMemoSP_all53 := MallocMemoSP_all52; MemoFast.memo_rw m_E7c2_eq.
Definition m_E7p : axst := ltac2:(tb__ "0|0|
S22U2S9fA2").
Lemma m_E7p_eq : ltac2:(tb__ "0|0|
S13S15S68S1U0A1S0Z2A3Sd3A3"). Proof. cbv delta [E7p m_E7p]; cbv beta zeta. MallocMemoSP_all53. reflexivity. Qed.
Ltac MallocMemoSP_sub54 t := let t := MallocMemoSP_sub53 t in lazymatch (eval pattern (E7p (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E7p) end.
Ltac MallocMemoSP_all54 := MallocMemoSP_all53; MemoFast.memo_rw m_E7p_eq.
Definition m_creg7a : sv := ltac2:(tb__ "0|0|
S9cS18UbS1dS17Sa3A1A1S1bZ0A1A4").
Lemma m_creg7a_eq : ltac2:(tb__ "0|0|
S13S18S7eS1U0A1S0Z2A3Se4A3"). Proof. cbv delta [creg7a m_creg7a]; cbv beta zeta. MallocMemoSP_all54. reflexivity. Qed.
Ltac MallocMemoSP_sub55 t := let t := MallocMemoSP_sub54 t in lazymatch (eval pattern (creg7a (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_creg7a) end.
Ltac MallocMemoSP_all55 := MallocMemoSP_all54; MemoFast.memo_rw m_creg7a_eq.
Definition m_creg7b : sv := ltac2:(tb__ "0|0|
S9cS18UbS1dS17Sd2A1A1S1bZ0A1A4").
Lemma m_creg7b_eq : ltac2:(tb__ "0|0|
S13S18S7fS1U0A1S0Z2A3Se5A3"). Proof. cbv delta [creg7b m_creg7b]; cbv beta zeta. MallocMemoSP_all55. reflexivity. Qed.
Ltac MallocMemoSP_sub56 t := let t := MallocMemoSP_sub55 t in lazymatch (eval pattern (creg7b (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_creg7b) end.
Ltac MallocMemoSP_all56 := MallocMemoSP_all55; MemoFast.memo_rw m_creg7b_eq.
Definition m_C7p : axst := ltac2:(tb__ "0|1|
S23S1U0A1S0Z2Sd3Z3c8bcS9S11SdS18A2M0SeSdS18UaS34A4S8G0A1A3S8S1aA1S10S9S19S1eS1bZ1A1S73A2S8S19A1A3A9").
Lemma m_C7p_eq : ltac2:(tb__ "0|0|
S13S15S4bS1U0A1S0Z2A3SbeA3"). Proof. cbv delta [C7p m_C7p]; cbv beta zeta. MallocMemoSP_all56. reflexivity. Qed.
Ltac MallocMemoSP_sub57 t := let t := MallocMemoSP_sub56 t in lazymatch (eval pattern (C7p (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C7p) end.
Ltac MallocMemoSP_all57 := MallocMemoSP_all56; MemoFast.memo_rw m_C7p_eq.
Definition m_run7p : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Z3ca04S8S21A1A3SbeScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run7p_eq : ltac2:(tb__ "0|0|
S13SaS14A1S92S1U0A1S0Z2A3Sa9A3"). Proof. cbv delta [run7p m_run7p]; cbv beta zeta. MallocMemoSP_all57. reflexivity. Qed.
Ltac MallocMemoSP_sub58 t := let t := MallocMemoSP_sub57 t in lazymatch (eval pattern (run7p (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_run7p) end.
Ltac MallocMemoSP_all58 := MallocMemoSP_all57; MemoFast.memo_rw m_run7p_eq.
Definition m_E7q1 : axst := ltac2:(tb__ "0|0|
S22U0Sa9A2").
Lemma m_E7q1_eq : ltac2:(tb__ "0|0|
S13S15S69S1U0A1S0Z2A3Sa4A3"). Proof. cbv delta [E7q1 m_E7q1]; cbv beta zeta. MallocMemoSP_all58. reflexivity. Qed.
Ltac MallocMemoSP_sub59 t := let t := MallocMemoSP_sub58 t in lazymatch (eval pattern (E7q1 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E7q1) end.
Ltac MallocMemoSP_all59 := MallocMemoSP_all58; MemoFast.memo_rw m_E7q1_eq.
Definition m_E7q2 : axst := ltac2:(tb__ "0|0|
S22U1Sa9A2").
Lemma m_E7q2_eq : ltac2:(tb__ "0|0|
S13S15S6aS1U0A1S0Z2A3Sd4A3"). Proof. cbv delta [E7q2 m_E7q2]; cbv beta zeta. MallocMemoSP_all59. reflexivity. Qed.
Ltac MallocMemoSP_sub60 t := let t := MallocMemoSP_sub59 t in lazymatch (eval pattern (E7q2 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E7q2) end.
Ltac MallocMemoSP_all60 := MallocMemoSP_all59; MemoFast.memo_rw m_E7q2_eq.
Definition m_creg7c : sv := ltac2:(tb__ "0|0|
S9cS18UbS1dS17Sa4A1A1S1bZ0A1A4").
Lemma m_creg7c_eq : ltac2:(tb__ "0|0|
S13S18S80S1U0A1S0Z2A3Se6A3"). Proof. cbv delta [creg7c m_creg7c]; cbv beta zeta. MallocMemoSP_all60. reflexivity. Qed.
Ltac MallocMemoSP_sub61 t := let t := MallocMemoSP_sub60 t in lazymatch (eval pattern (creg7c (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_creg7c) end.
Ltac MallocMemoSP_all61 := MallocMemoSP_all60; MemoFast.memo_rw m_creg7c_eq.
Definition m_creg7d : sv := ltac2:(tb__ "0|0|
S9cS18UbS1dS17Sd4A1A1S1bZ0A1A4").
Lemma m_creg7d_eq : ltac2:(tb__ "0|0|
S13S18S81S1U0A1S0Z2A3Se7A3"). Proof. cbv delta [creg7d m_creg7d]; cbv beta zeta. MallocMemoSP_all61. reflexivity. Qed.
Ltac MallocMemoSP_sub62 t := let t := MallocMemoSP_sub61 t in lazymatch (eval pattern (creg7d (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_creg7d) end.
Ltac MallocMemoSP_all62 := MallocMemoSP_all61; MemoFast.memo_rw m_creg7d_eq.
Definition m_C8 : axst := ltac2:(tb__ "0|0|
S27S26S23S1U0A1S0Z2Sa3Z3ca04S2eS8S1aA1ScSfS19S24S25A3A9A2").
Lemma m_C8_eq : ltac2:(tb__ "0|0|
S13S15S4cS1U0A1S0Z2A3SbfA3"). Proof. cbv delta [C8 m_C8]; cbv beta zeta. MallocMemoSP_all62. reflexivity. Qed.
Ltac MallocMemoSP_sub63 t := let t := MallocMemoSP_sub62 t in lazymatch (eval pattern (C8 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C8) end.
Ltac MallocMemoSP_all63 := MallocMemoSP_all62; MemoFast.memo_rw m_C8_eq.
Definition m_C8p : axst := ltac2:(tb__ "0|0|
S27S26S23S1U0A1S0Z2Sa4Z3ca04S2eS8S1aA1ScSfS19S24S25A3A9A2").
Lemma m_C8p_eq : ltac2:(tb__ "0|0|
S13S15S4fS1U0A1S0Z2A3Sc2A3"). Proof. cbv delta [C8p m_C8p]; cbv beta zeta. MallocMemoSP_all63. reflexivity. Qed.
Ltac MallocMemoSP_sub64 t := let t := MallocMemoSP_sub63 t in lazymatch (eval pattern (C8p (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C8p) end.
Ltac MallocMemoSP_all64 := MallocMemoSP_all63; MemoFast.memo_rw m_C8p_eq.
Definition m_run8 : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Zdb004S9S21Z3ca54S8S21A1A3A3SbfScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run8_eq : ltac2:(tb__ "0|0|
S13SaS14A1S93S1U0A1S0Z2A3SaaA3"). Proof. cbv delta [run8 m_run8]; cbv beta zeta. MallocMemoSP_all64. reflexivity. Qed.
Ltac MallocMemoSP_sub65 t := let t := MallocMemoSP_sub64 t in lazymatch (eval pattern (run8 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_run8) end.
Ltac MallocMemoSP_all65 := MallocMemoSP_all64; MemoFast.memo_rw m_run8_eq.
Definition m_run8p : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Zdb004S9S21Z3ca54S8S21A1A3A3Sc2ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run8p_eq : ltac2:(tb__ "0|0|
S13SaS14A1S94S1U0A1S0Z2A3SabA3"). Proof. cbv delta [run8p m_run8p]; cbv beta zeta. MallocMemoSP_all65. reflexivity. Qed.
Ltac MallocMemoSP_sub66 t := let t := MallocMemoSP_sub65 t in lazymatch (eval pattern (run8p (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_run8p) end.
Ltac MallocMemoSP_all66 := MallocMemoSP_all65; MemoFast.memo_rw m_run8p_eq.
Definition m_E8a : axst := ltac2:(tb__ "0|0|
S22U0SaaA2").
Lemma m_E8a_eq : ltac2:(tb__ "0|0|
S13S15S6bS1U0A1S0Z2A3Sd5A3"). Proof. cbv delta [E8a m_E8a]; cbv beta zeta. MallocMemoSP_all66. reflexivity. Qed.
Ltac MallocMemoSP_sub67 t := let t := MallocMemoSP_sub66 t in lazymatch (eval pattern (E8a (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E8a) end.
Ltac MallocMemoSP_all67 := MallocMemoSP_all66; MemoFast.memo_rw m_E8a_eq.
Definition m_E8b : axst := ltac2:(tb__ "0|0|
S22U1SaaA2").
Lemma m_E8b_eq : ltac2:(tb__ "0|0|
S13S15S6cS1U0A1S0Z2A3Se2A3"). Proof. cbv delta [E8b m_E8b]; cbv beta zeta. MallocMemoSP_all67. reflexivity. Qed.
Ltac MallocMemoSP_sub68 t := let t := MallocMemoSP_sub67 t in lazymatch (eval pattern (E8b (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E8b) end.
Ltac MallocMemoSP_all68 := MallocMemoSP_all67; MemoFast.memo_rw m_E8b_eq.
Definition m_E8pa : axst := ltac2:(tb__ "0|0|
S22U0SabA2").
Lemma m_E8pa_eq : ltac2:(tb__ "0|0|
S13S15S6dS1U0A1S0Z2A3Sd6A3"). Proof. cbv delta [E8pa m_E8pa]; cbv beta zeta. MallocMemoSP_all68. reflexivity. Qed.
Ltac MallocMemoSP_sub69 t := let t := MallocMemoSP_sub68 t in lazymatch (eval pattern (E8pa (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E8pa) end.
Ltac MallocMemoSP_all69 := MallocMemoSP_all68; MemoFast.memo_rw m_E8pa_eq.
Definition m_E8pb : axst := ltac2:(tb__ "0|0|
S22U1SabA2").
Lemma m_E8pb_eq : ltac2:(tb__ "0|0|
S13S15S6eS1U0A1S0Z2A3Se3A3"). Proof. cbv delta [E8pb m_E8pb]; cbv beta zeta. MallocMemoSP_all69. reflexivity. Qed.
Ltac MallocMemoSP_sub70 t := let t := MallocMemoSP_sub69 t in lazymatch (eval pattern (E8pb (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_E8pb) end.
Ltac MallocMemoSP_all70 := MallocMemoSP_all69; MemoFast.memo_rw m_E8pb_eq.
Definition m_C8ma : axst := ltac2:(tb__ "0|1|
S23S1U0A1S0Z2Sd5S2aS9S11SdS18A2M0SeSdS18UaS33A4S8G0A1A3S8S1aA1S10S8S19A1A9").
Lemma m_C8ma_eq : ltac2:(tb__ "0|0|
S13S15S4dS1U0A1S0Z2A3Sc0A3"). Proof. cbv delta [C8ma m_C8ma]; cbv beta zeta. MallocMemoSP_all70. reflexivity. Qed.
Ltac MallocMemoSP_sub71 t := let t := MallocMemoSP_sub70 t in lazymatch (eval pattern (C8ma (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C8ma) end.
Ltac MallocMemoSP_all71 := MallocMemoSP_all70; MemoFast.memo_rw m_C8ma_eq.
Definition m_C8mpa : axst := ltac2:(tb__ "0|1|
S23S1U0A1S0Z2Sd6S2aS9S11SdS18A2M0SeSdS18UaS33A4S8G0A1A3S8S1aA1S10S8S19A1A9").
Lemma m_C8mpa_eq : ltac2:(tb__ "0|0|
S13S15S4eS1U0A1S0Z2A3Sc1A3"). Proof. cbv delta [C8mpa m_C8mpa]; cbv beta zeta. MallocMemoSP_all71. reflexivity. Qed.
Ltac MallocMemoSP_sub72 t := let t := MallocMemoSP_sub71 t in lazymatch (eval pattern (C8mpa (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C8mpa) end.
Ltac MallocMemoSP_all72 := MallocMemoSP_all71; MemoFast.memo_rw m_C8mpa_eq.
Definition m_C9 : axst := ltac2:(tb__ "0|0|
S27S26S29U5S31S23S1U0A1S0Z2Sc0S2bS28S8S1aA1ScSfS19S24S25A3A9A3A2").
Lemma m_C9_eq : ltac2:(tb__ "0|0|
S13S15S50S1U0A1S0Z2A3Sa0A3"). Proof. cbv delta [C9 m_C9]; cbv beta zeta. MallocMemoSP_all72. reflexivity. Qed.
Ltac MallocMemoSP_sub73 t := let t := MallocMemoSP_sub72 t in lazymatch (eval pattern (C9 (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C9) end.
Ltac MallocMemoSP_all73 := MallocMemoSP_all72; MemoFast.memo_rw m_C9_eq.
Definition m_C9p : axst := ltac2:(tb__ "0|0|
S27S26S29U5S31S23S1U0A1S0Z2Sc1S2bS28S8S1aA1ScSfS19S24S25A3A9A3A2").
Lemma m_C9p_eq : ltac2:(tb__ "0|0|
S13S15S53S1U0A1S0Z2A3Sa1A3"). Proof. cbv delta [C9p m_C9p]; cbv beta zeta. MallocMemoSP_all73. reflexivity. Qed.
Ltac MallocMemoSP_sub74 t := let t := MallocMemoSP_sub73 t in lazymatch (eval pattern (C9p (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C9p) end.
Ltac MallocMemoSP_all74 := MallocMemoSP_all73; MemoFast.memo_rw m_C9p_eq.
Definition m_C9a : axst := ltac2:(tb__ "0|0|
S9dS9S19S1eS1bZ20A1S1cS2cA1A2S8S19A1A3Sa0A2").
Lemma m_C9a_eq : ltac2:(tb__ "0|0|
S13S15S51S1U0A1S0Z2A3Sc3A3"). Proof. cbv delta [C9a m_C9a]; cbv beta zeta. MallocMemoSP_all74. reflexivity. Qed.
Ltac MallocMemoSP_sub75 t := let t := MallocMemoSP_sub74 t in lazymatch (eval pattern (C9a (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C9a) end.
Ltac MallocMemoSP_all75 := MallocMemoSP_all74; MemoFast.memo_rw m_C9a_eq.
Definition m_C9b : axst := ltac2:(tb__ "0|0|
S9dS9S19S1eS1cS2cA1S1bZ10A1A2S8S19A1A3Sa0A2").
Lemma m_C9b_eq : ltac2:(tb__ "0|0|
S13S15S52S1U0A1S0Z2A3Sc4A3"). Proof. cbv delta [C9b m_C9b]; cbv beta zeta. MallocMemoSP_all75. reflexivity. Qed.
Ltac MallocMemoSP_sub76 t := let t := MallocMemoSP_sub75 t in lazymatch (eval pattern (C9b (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C9b) end.
Ltac MallocMemoSP_all76 := MallocMemoSP_all75; MemoFast.memo_rw m_C9b_eq.
Definition m_C9pa : axst := ltac2:(tb__ "0|0|
S9dS9S19S1eS1bZ20A1S1cS2cA1A2S8S19A1A3Sa1A2").
Lemma m_C9pa_eq : ltac2:(tb__ "0|0|
S13S15S54S1U0A1S0Z2A3Sc5A3"). Proof. cbv delta [C9pa m_C9pa]; cbv beta zeta. MallocMemoSP_all76. reflexivity. Qed.
Ltac MallocMemoSP_sub77 t := let t := MallocMemoSP_sub76 t in lazymatch (eval pattern (C9pa (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C9pa) end.
Ltac MallocMemoSP_all77 := MallocMemoSP_all76; MemoFast.memo_rw m_C9pa_eq.
Definition m_C9pb : axst := ltac2:(tb__ "0|0|
S9dS9S19S1eS1cS2cA1S1bZ10A1A2S8S19A1A3Sa1A2").
Lemma m_C9pb_eq : ltac2:(tb__ "0|0|
S13S15S55S1U0A1S0Z2A3Sc6A3"). Proof. cbv delta [C9pb m_C9pb]; cbv beta zeta. MallocMemoSP_all77. reflexivity. Qed.
Ltac MallocMemoSP_sub78 t := let t := MallocMemoSP_sub77 t in lazymatch (eval pattern (C9pb (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_C9pb) end.
Ltac MallocMemoSP_all78 := MallocMemoSP_all77; MemoFast.memo_rw m_C9pb_eq.
Definition m_run9a : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S8S21A1Sc3ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run9a_eq : ltac2:(tb__ "0|0|
S13SaS14A1S95S1U0A1S0Z2A3SeaA3"). Proof. cbv delta [run9a m_run9a]; cbv beta zeta. MallocMemoSP_all78. reflexivity. Qed.
Ltac MallocMemoSP_sub79 t := let t := MallocMemoSP_sub78 t in lazymatch (eval pattern (run9a (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_run9a) end.
Ltac MallocMemoSP_all79 := MallocMemoSP_all78; MemoFast.memo_rw m_run9a_eq.
Definition m_run9b : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S8S21A1Sc4ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run9b_eq : ltac2:(tb__ "0|0|
S13SaS14A1S96S1U0A1S0Z2A3SebA3"). Proof. cbv delta [run9b m_run9b]; cbv beta zeta. MallocMemoSP_all79. reflexivity. Qed.
Ltac MallocMemoSP_sub80 t := let t := MallocMemoSP_sub79 t in lazymatch (eval pattern (run9b (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_run9b) end.
Ltac MallocMemoSP_all80 := MallocMemoSP_all79; MemoFast.memo_rw m_run9b_eq.
Definition m_run9pa : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S8S21A1Sc5ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run9pa_eq : ltac2:(tb__ "0|0|
S13SaS14A1S97S1U0A1S0Z2A3SecA3"). Proof. cbv delta [run9pa m_run9pa]; cbv beta zeta. MallocMemoSP_all80. reflexivity. Qed.
Ltac MallocMemoSP_sub81 t := let t := MallocMemoSP_sub80 t in lazymatch (eval pattern (run9pa (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_run9pa) end.
Ltac MallocMemoSP_all81 := MallocMemoSP_all80; MemoFast.memo_rw m_run9pa_eq.
Definition m_run9pb : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S8S21A1Sc6ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run9pb_eq : ltac2:(tb__ "0|0|
S13SaS14A1S98S1U0A1S0Z2A3SedA3"). Proof. cbv delta [run9pb m_run9pb]; cbv beta zeta. MallocMemoSP_all81. reflexivity. Qed.
Ltac MallocMemoSP_sub82 t := let t := MallocMemoSP_sub81 t in lazymatch (eval pattern (run9pb (Wcan 0) UStopLe 2) in t) with ?P _ => eval cbv beta in (P m_run9pb) end.
Ltac MallocMemoSP_all82 := MallocMemoSP_all81; MemoFast.memo_rw m_run9pb_eq.

Ltac MallocMemoSP_subst t := MallocMemoSP_sub82 t.
Ltac MallocMemoSP_all := MallocMemoSP_all82.
End MallocMemoSP.

(* [comment removed for export] *)
Module CertMallocSS.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "nil"; "app"; "prod"; "option"; "false"; "list"; "None"; "true"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SVar"; "SPUle"; "sobj"; "SAlu"; "FcsrFrm0"; "SPAlign"; "SPBranch"; "SPUlt"; "mkSS"; "DZero"; "SPNot"; "cell"; "mkObj"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "SEC_INST"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "ALU_AND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_setS"; "sym_runA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS"; "V_MS"; "V_NS"; "msx"; "V_NCH"; "V_NRES"; "V_PAB"; "RT_sec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.CertMallocSS.W"; "CS1"; "nxS"; "regs_ss"; "ES1"; "ES1f"; "SS0"; "SSa_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kPtrArrayReserve"; "IMG_HI"; "PG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "ERRNO_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "A_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "E_regs"; "E_s1"; "F_fam"; "F_s1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "upd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@Stdlib.PArith.BinPos.Pos"; "succ"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymCall ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition V_NS : positive := 141%positive.
Definition V_MS : positive := 142%positive.
Definition V_PAB : positive := 145%positive.
Definition V_NRES : positive := 146%positive.
Definition V_NCH : positive := 147%positive.

Definition N_sec : list carve_spec := ltac2:(tb__ "0|d|
S1S5S5S5ScSbA2M0SbA2M1S8S5S5SbS2A2M2ScA2M3A1M4A2M5S0G1G4S0G0SbS0ScSbSeZ0A1M6S1dA4S1eS1dZ40A2M7A4S1G3S0G2ScS0SbS2S1dU8M8A4SeS3dA1A4S1G3S0G2ScS0SbS2S1eS1dZ8A2G8A4SfS2dA1M9A4S1G3S0G2ScS0SbS2S1eS1dZ10A2G8A4G9A4S1G3S0G2ScS0SbS2S1eS1dZ18A2G8A4SeS3bA1A4S1G3S0G2ScS0SbS2S1eS1dZ30A2G8A4SfS2cA1A4S1G3S0G2ScS0SbS2S1eS1dZ38A2G8A4SfS2bA1A4S3G3A1MaA3A3A3A3A3A3A4S1G5S0G1G4S0G0SbS0ScSbG6G7A4Zead00MbA4GaA4S1G5S0G1G4S0G0SbS0ScSbG6GbA4Zead04A4S1G3S0G2ScS0SbS2GbU4A4G6A4GaA3A4S1G5S0G1G4S0G0SbS0ScSbG6Zead08A4Zead30A4GaA4S1G5S0G1G4S0G0SbS0ScSbG6Ze67b8McA4Ze67c0A4S1G3S0G2ScS0SbS2GcG8A4SeZ1a309A1A4GaA3A4S1G5S0G1G4S0G0SbS0ScSbG6Z170320A4Z170322A4S1G3S0G2ScS0SbS2Z170321U1A4SeZ1A1A4GaA3A4S1G5S0G1G4S0G0SbS0ScSbG6S3eA4S1eS3eZ4A2A4GaA4S1G5S0G1G4S0G0SbS0ScSbS48Zad0A4Zc60A4GaA4S3G5A1A3A3A3A3A3A3A3A3").
Definition RT_sec : list sobj := map carve_obj N_sec.
Definition O_seci : sobj := nth 0 RT_sec O_st. Definition O_secs : sobj := nth 1 RT_sec O_st. Definition O_secm : sobj := nth 2 RT_sec O_st.
Definition O_secg : sobj := nth 3 RT_sec O_st. Definition O_san : sobj := nth 4 RT_sec O_st. Definition O_oom : sobj := nth 5 RT_sec O_st.
Definition O_errno : sobj := nth 6 RT_sec O_st.

Definition msx : sv := ltac2:(tb__ "0|0|
S12S21S12S23S12S21SfS29A1SeZfffA1A3SeZfffffffffffff000A1A3SeZ1000A1A3").
Definition F_sgen : list sprop := ltac2:(tb__ "0|6|
S1SdS14S29Z3A2S1SdS10SeZ10c08A1SfS29A1M0A2S1SdS16G0SeS1eS1fZ2M1Z27A2Z1008A2A1A2S1SdS14S28ZcA2S1SdS10S12S21G0SeZ1000A1A3SfS28A1M2A2S1SdS10G2S12S21G0SeZ1fffA1A3A2S1SdS16G2SeS1fG1Z28A2A1M3A2S1SdS15S22G2S2aA3S1SdS10SeS3cA1SfS2dA1M4A2S1SdS10G4SeS20Z7fffff800000S3bA2A1A2S1SdS10SfS2bA1SfS2cA1M5A2S1SdS10G5SeS1fG1Z14A2A1A2S1SdS10G0S2aA2S1SdS10S2aG3A2S1SdS19S15S22S12S21SfPaA1SeN998A1A3SeZ0A1A3A1S3SdA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Section W.
Variable W : list ulink.
Variable st : ustop.
Variable tmax : Z.

Let FACTS1 : list sprop := ltac2:(tb__ "0|0|
S4SdS4SdS4SdS4SdS4cVW;Vst;A2S4bS4aA1A3S39A3S44A3S43Vtmax;Z8A2A3").
Let OBJS1 : list sobj := ltac2:(tb__ "0|0|
S4S11S1S11S46S4S11S4dVW;A1S49A3A3S45A3").

Definition regs_ss : list sv := ltac2:(tb__ "0|2|
S37S41Z8A1S1S5S2ScA2M0S0S2ScUcSfS29A1M1A4S1G0S0S2ScU13G1A4S3G0A1A3A3A2").
Definition SSa_S : sstate := ltac2:(tb__ "0|0|
S17Z40bacS31S36S13S9ScA1VOBJS1;VFACTS1;S38S7A9").
Definition SSa : axst := ltac2:(tb__ "0|0|
S25S42VW;Vst;Vtmax;Z8A4S35A2").
Definition SSb_S : sstate := ltac2:(tb__ "0|0|
S17Z40bacS31S36S13S9ScA1S4S11VOBJS1;S2eA3VFACTS1;S38S7A9").
Definition SSb : axst := ax_setS SSa SSb_S.
Definition SS0 : axst := ax_add_facts F_sgen SSb.
Definition runS1 : list leafA := ltac2:(tb__ "0|1|
S6S8S24A1M0A1G0Lx;S26S3aUfa0S1SbZ706a0S3SbA1A3S34SaA5G0R1Ll;S3S24A1X6x2").
Definition ES1 : axst := leaf 0 runS1.

Definition CS1 : axst := ltac2:(tb__ "0|1|
S47VW;Vst;Vtmax;S32Z706a0S1S5S2ScA2M0S0S2ScUbSfS28A1A4S3G0A1A3S3S11A1S7S3SdA1A9").

Definition ES1f : axst := ltac2:(tb__ "0|0|
S40S2fSeS20S1fZ2Z40A2ZcA2A1A2").
Definition runSf : list leafA := ltac2:(tb__ "0|1|
S6S8S24A1M0A1G0Lx;S26S3aUfa0S1SbZ5e52cS3SbA1A3S33SaA5G0R1Ll;S3S24A1X6x2").
Definition ESn : axst := leaf 0 runSf.

Definition nxS : positive := ss_next (ax_S CS1).
Definition ES1g : axst := ltac2:(tb__ "0|2|
S25S2fS3fS27S2fA1M0SfS30A1M1S4S11S1cG0A1S1S11S1bG1SeZ0A1SfS28A1S3S1aA1S18A5S3S11A1A3A3S4eS30A1A4A2").
End W.

Goal map (fun L => (ss_pc (ax_S (la_state L)), la_reason L)) (runS1 (Wcan 0) UStopLe 2) = [(0x706a0, RsCut)]
  /\ nth 11 (ss_regs (ax_S (ES1 (Wcan 0) UStopLe 2))) (SLit 0) = SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_ADD (SVar V_NS) (SLit 4095)) (SLit 18446744073709547520)) (SLit 8191)) (SLit 18446744073709547520)
  /\ nth 17 (ss_regs (ax_S (ES1 (Wcan 0) UStopLe 2))) (SLit 0) = SLit 222.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Goal map (fun L => (ss_pc (ax_S (la_state L)), la_reason L)) (runSf (Wcan 0) UStopLe 2) = [(0x5e52c, RsCut)].
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End CertMallocSS.

(* [comment removed for export] *)
Module CertCallocS1e.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@Corelib.Lists.ListDef"; "map"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "mkVNA"; "vnodeA"; "check_ecfgA"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "nil"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "s1_exits"; "s1_cuts"; "s1_cuts_pcs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "UStopLeOrPc"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1.
Import ListNotations.
Open Scope Z_scope.
Lemma s1_ecert_0 : ltac2:(tb__ "0|3|
SaS6S5S10Ufa0S7S2Z40bacS8S2A1A3SfS1S0S4S0S3R1Z1SbZ0M0A1M1A3Lc;SdU0M2S11A2A4S1S0S4S0S3R1G0G1A3Le;ScG2S11Z2A3A4A6S9A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma s1_ecert_1 : ltac2:(tb__ "0|3|
SaS6S5S10Ufa0S7S2Z40bacS8S2A1A3SfS1S0S4S0S3R1Z1SbZ0M0A1M1A3Lc;SeU1M2S12A2A4S1S0S4S0S3R1G0G1A3Le;ScG2S12Z3A3A4A6S9A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
End CertCallocS1e.

(* [comment removed for export] *)
Module MallocMemoSPW2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "A_globals"; "malloc_depth"; "mkA"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "@Corelib.Init.Datatypes"; "nil"; "cons"; "list"; "option"; "true"; "nat"; "pair"; "app"; "false"; "prod"; "None"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "axst"; "sym_runA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "SVar"; "ss_regs"; "SPUle"; "FcsrFrm0"; "mkSS"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "leaf"; "upd"; "F_cls"; "F_pop"; "LIVE"; "prune_sw"; "HAVOC_CALLER"; "set_obj_from_end"; "MSENT"; "MSRET"; "V_RZ"; "C2_ru"; "HAVOC_C8"; "LUe"; "O_L"; "O_UB"; "O_st"; "ube"; "BP"; "BR"; "BSH"; "BU"; "C1g"; "C1g_regs"; "C2p"; "C2p0"; "C2r"; "C2r0"; "C3"; "C5"; "C5b"; "C5c"; "C5d"; "C5e"; "C5m1"; "C5m2"; "C6"; "C6b"; "C6l"; "C6m"; "C7"; "C7p"; "C8"; "C8ma"; "C8mpa"; "C8p"; "C9"; "C9a"; "C9b"; "C9p"; "C9pa"; "C9pb"; "E2a"; "E2b"; "E3p"; "E3r"; "E4d"; "E5f"; "E5j"; "E5m1"; "E5m2"; "E5n"; "E5s1"; "E5s2"; "E6j"; "E6l"; "E6m"; "E6s"; "E7c1"; "E7c2"; "E7p"; "E7q1"; "E7q2"; "E8a"; "E8b"; "E8pa"; "E8pb"; "F_gen"; "HAVOC_JOIN"; "HAVOC_JOIN6"; "LLe"; "LPe"; "LRe"; "O_R"; "O_Uz"; "O_pcc"; "O_pcc0"; "O_pck"; "O_pcs"; "PIECES"; "V_CLS"; "V_SIZE"; "creg7a"; "creg7b"; "creg7c"; "creg7d"; "creg_a"; "creg_b"; "prune_call"; "run2"; "run3p"; "run3r"; "run4"; "run5"; "run5b"; "run5c"; "run5d"; "run5e"; "run6"; "run6b"; "run6l"; "run7"; "run7p"; "run8"; "run8p"; "run9a"; "run9b"; "run9pa"; "run9pb"; "sreg1"; "sreg2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i8.MallocMemoSPW2"; "m_E2b"; "m_run7"; "m_C9"; "m_C9p"; "m_E5s1"; "m_E7c1"; "m_E7q1"; "m_run2"; "m_run5"; "m_run5b"; "m_run6"; "m_run7p"; "m_run8"; "m_run8p"; "m_C1g"; "m_C2p"; "m_C2p0"; "m_C2r"; "m_C2r0"; "m_C3"; "m_C5"; "m_C5b"; "m_C5c"; "m_C5d"; "m_C5e"; "m_C5m1"; "m_C5m2"; "m_C6"; "m_C6b"; "m_C6l"; "m_C6m"; "m_C7"; "m_C7p"; "m_C8"; "m_C8ma"; "m_C8mpa"; "m_C8p"; "m_C9a"; "m_C9b"; "m_C9pa"; "m_C9pb"; "m_E2a"; "m_E3p"; "m_E4d"; "m_E5f"; "m_E5m1"; "m_E5m2"; "m_E5n"; "m_E5s2"; "m_E6j"; "m_E6l"; "m_E6m"; "m_E7c2"; "m_E7p"; "m_E7q2"; "m_E8a"; "m_E8pa"; "m_run3p"; "m_run3r"; "m_run4"; "m_run5c"; "m_run5d"; "m_run5e"; "m_run6b"; "m_run6l"; "m_E3r"; "m_E5j"; "m_E6s"; "m_E8b"; "m_E8pb"; "m_creg7a"; "m_creg7b"; "m_creg7c"; "m_creg7d"; "m_creg_a"; "m_creg_b"; "m_run9a"; "m_run9b"; "m_run9pa"; "m_run9pb"; "m_sreg1"; "m_sreg2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "F_geom_fn"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1"; "F_s1"; "RT_m1"; "V_TSZ"; "sw_s1"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import CertMallocSP.
Import ListNotations.
Open Scope Z_scope.

Ltac MallocMemoSPW2_sub0 t := t.
Ltac MallocMemoSPW2_all0 := idtac.
Definition m_C1g : axst := ltac2:(tb__ "0|2|
S4S20Z40bacS39Sf0S1fS12S18A1SfS1aSfS1aS9S1aSf6SfS1aS7S1U2A1M0A1S2A3A3Sf4A3S8S1aA1A3SfS19SfS19SfS19SfS19S6G0S0A2S5S3A1A3Sf1A3Sf3A3SfS19S9S19S1eS1bZ1A1S1cSf5A1M1A2S9S19S1eG1S1bZ4A1A2S8S19A1A3A3S6fA3A3Sf2S10A9S8S11S18S18A2A1A2").
Lemma m_C1g_eq : ltac2:(tb__ "0|0|
S13S15S38S1U2A1S0Z4A3SacA3"). Proof. cbv delta [C1g m_C1g]; cbv beta zeta. MallocMemoSPW2_all0. reflexivity. Qed.
Ltac MallocMemoSPW2_sub1 t := let t := MallocMemoSPW2_sub0 t in lazymatch (eval pattern (C1g (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C1g) end.
Ltac MallocMemoSPW2_all1 := MallocMemoSPW2_all0; MemoFast.memo_rw m_C1g_eq.
Definition m_run2 : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Z40d40S8S21A1A3SacScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run2_eq : ltac2:(tb__ "0|0|
S13SaS14A1S85S1U2A1S0Z4A3Sa5A3"). Proof. cbv delta [run2 m_run2]; cbv beta zeta. MallocMemoSPW2_all1. reflexivity. Qed.
Ltac MallocMemoSPW2_sub2 t := let t := MallocMemoSPW2_sub1 t in lazymatch (eval pattern (run2 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_run2) end.
Ltac MallocMemoSPW2_all2 := MallocMemoSPW2_all1; MemoFast.memo_rw m_run2_eq.
Definition m_E2a : axst := ltac2:(tb__ "0|0|
S22U0Sa5A2").
Lemma m_E2a_eq : ltac2:(tb__ "0|0|
S13S15S56S1U2A1S0Z4A3Sc7A3"). Proof. cbv delta [E2a m_E2a]; cbv beta zeta. MallocMemoSPW2_all2. reflexivity. Qed.
Ltac MallocMemoSPW2_sub3 t := let t := MallocMemoSPW2_sub2 t in lazymatch (eval pattern (E2a (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E2a) end.
Ltac MallocMemoSPW2_all3 := MallocMemoSPW2_all2; MemoFast.memo_rw m_E2a_eq.
Definition m_E2b : axst := ltac2:(tb__ "0|0|
S22U1Sa5A2").
Lemma m_E2b_eq : ltac2:(tb__ "0|0|
S13S15S57S1U2A1S0Z4A3S9eA3"). Proof. cbv delta [E2b m_E2b]; cbv beta zeta. MallocMemoSPW2_all3. reflexivity. Qed.
Ltac MallocMemoSPW2_sub4 t := let t := MallocMemoSPW2_sub3 t in lazymatch (eval pattern (E2b (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E2b) end.
Ltac MallocMemoSPW2_all4 := MallocMemoSPW2_all3; MemoFast.memo_rw m_E2b_eq.
Definition m_creg_a : sv := ltac2:(tb__ "0|0|
S9cS18U8S1dS17Sc7A1A1S1bZ0A1A4").
Lemma m_creg_a_eq : ltac2:(tb__ "0|0|
S13S18S82S1U2A1S0Z4A3Se8A3"). Proof. cbv delta [creg_a m_creg_a]; cbv beta zeta. MallocMemoSPW2_all4. reflexivity. Qed.
Ltac MallocMemoSPW2_sub5 t := let t := MallocMemoSPW2_sub4 t in lazymatch (eval pattern (creg_a (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_creg_a) end.
Ltac MallocMemoSPW2_all5 := MallocMemoSPW2_all4; MemoFast.memo_rw m_creg_a_eq.
Definition m_creg_b : sv := ltac2:(tb__ "0|0|
S9cS18U8S1dS17S9eA1A1S1bZ0A1A4").
Lemma m_creg_b_eq : ltac2:(tb__ "0|0|
S13S18S83S1U2A1S0Z4A3Se9A3"). Proof. cbv delta [creg_b m_creg_b]; cbv beta zeta. MallocMemoSPW2_all5. reflexivity. Qed.
Ltac MallocMemoSPW2_sub6 t := let t := MallocMemoSPW2_sub5 t in lazymatch (eval pattern (creg_b (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_creg_b) end.
Ltac MallocMemoSPW2_all6 := MallocMemoSPW2_all5; MemoFast.memo_rw m_creg_b_eq.
Definition m_C2p0 : axst := ltac2:(tb__ "0|0|
S23S1U2A1S0Z4S9eZ40d40S2dS9S1aS77S9S1aS7aS9S1aS79S9S1aS32S8S1aA1A3A3A3A3ScS8S19A1A9").
Lemma m_C2p0_eq : ltac2:(tb__ "0|0|
S13S15S3bS1U2A1S0Z4A3SaeA3"). Proof. cbv delta [C2p0 m_C2p0]; cbv beta zeta. MallocMemoSPW2_all6. reflexivity. Qed.
Ltac MallocMemoSPW2_sub7 t := let t := MallocMemoSPW2_sub6 t in lazymatch (eval pattern (C2p0 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C2p0) end.
Ltac MallocMemoSPW2_all7 := MallocMemoSPW2_all6; MemoFast.memo_rw m_C2p0_eq.
Definition m_C2r0 : axst := ltac2:(tb__ "0|0|
S23S1U2A1S0Z4S9eZ40d40S2dS9S1aS78S9S1aS32S8S1aA1A3A3ScS8S19A1A9").
Lemma m_C2r0_eq : ltac2:(tb__ "0|0|
S13S15S3dS1U2A1S0Z4A3Sb0A3"). Proof. cbv delta [C2r0 m_C2r0]; cbv beta zeta. MallocMemoSPW2_all7. reflexivity. Qed.
Ltac MallocMemoSPW2_sub8 t := let t := MallocMemoSPW2_sub7 t in lazymatch (eval pattern (C2r0 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C2r0) end.
Ltac MallocMemoSPW2_all8 := MallocMemoSPW2_all7; MemoFast.memo_rw m_C2r0_eq.
Definition m_C2p : axst := ltac2:(tb__ "0|0|
S9dSfS19S24S25A3SaeA2").
Lemma m_C2p_eq : ltac2:(tb__ "0|0|
S13S15S3aS1U2A1S0Z4A3SadA3"). Proof. cbv delta [C2p m_C2p]; cbv beta zeta. MallocMemoSPW2_all8. reflexivity. Qed.
Ltac MallocMemoSPW2_sub9 t := let t := MallocMemoSPW2_sub8 t in lazymatch (eval pattern (C2p (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C2p) end.
Ltac MallocMemoSPW2_all9 := MallocMemoSPW2_all8; MemoFast.memo_rw m_C2p_eq.
Definition m_C2r : axst := ltac2:(tb__ "0|0|
S9dS24Sb0A2").
Lemma m_C2r_eq : ltac2:(tb__ "0|0|
S13S15S3cS1U2A1S0Z4A3SafA3"). Proof. cbv delta [C2r m_C2r]; cbv beta zeta. MallocMemoSPW2_all9. reflexivity. Qed.
Ltac MallocMemoSPW2_sub10 t := let t := MallocMemoSPW2_sub9 t in lazymatch (eval pattern (C2r (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C2r) end.
Ltac MallocMemoSPW2_all10 := MallocMemoSPW2_all9; MemoFast.memo_rw m_C2r_eq.
Definition m_run3p : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Z40e58S9S21Z3c614S8S21A1A3A3SadScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run3p_eq : ltac2:(tb__ "0|0|
S13SaS14A1S86S1U2A1S0Z4A3Sd7A3"). Proof. cbv delta [run3p m_run3p]; cbv beta zeta. MallocMemoSPW2_all10. reflexivity. Qed.
Ltac MallocMemoSPW2_sub11 t := let t := MallocMemoSPW2_sub10 t in lazymatch (eval pattern (run3p (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_run3p) end.
Ltac MallocMemoSPW2_all11 := MallocMemoSPW2_all10; MemoFast.memo_rw m_run3p_eq.
Definition m_run3r : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Z40e58S9S21Z3c614S8S21A1A3A3SafScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run3r_eq : ltac2:(tb__ "0|0|
S13SaS14A1S87S1U2A1S0Z4A3Sd8A3"). Proof. cbv delta [run3r m_run3r]; cbv beta zeta. MallocMemoSPW2_all11. reflexivity. Qed.
Ltac MallocMemoSPW2_sub12 t := let t := MallocMemoSPW2_sub11 t in lazymatch (eval pattern (run3r (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_run3r) end.
Ltac MallocMemoSPW2_all12 := MallocMemoSPW2_all11; MemoFast.memo_rw m_run3r_eq.
Definition m_E3p : axst := ltac2:(tb__ "0|0|
S22U0Sd7A2").
Lemma m_E3p_eq : ltac2:(tb__ "0|0|
S13S15S58S1U2A1S0Z4A3Sc8A3"). Proof. cbv delta [E3p m_E3p]; cbv beta zeta. MallocMemoSPW2_all12. reflexivity. Qed.
Ltac MallocMemoSPW2_sub13 t := let t := MallocMemoSPW2_sub12 t in lazymatch (eval pattern (E3p (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E3p) end.
Ltac MallocMemoSPW2_all13 := MallocMemoSPW2_all12; MemoFast.memo_rw m_E3p_eq.
Definition m_E3r : axst := ltac2:(tb__ "0|0|
S22U0Sd8A2").
Lemma m_E3r_eq : ltac2:(tb__ "0|0|
S13S15S59S1U2A1S0Z4A3SdfA3"). Proof. cbv delta [E3r m_E3r]; cbv beta zeta. MallocMemoSPW2_all13. reflexivity. Qed.
Ltac MallocMemoSPW2_sub14 t := let t := MallocMemoSPW2_sub13 t in lazymatch (eval pattern (E3r (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E3r) end.
Ltac MallocMemoSPW2_all14 := MallocMemoSPW2_all13; MemoFast.memo_rw m_E3r_eq.
Definition m_C3 : axst := ltac2:(tb__ "0|0|
S23S1U2A1S0Z4Sc8Z3c614S8S11SdS18A2A1S7bS10S8S19A1A9").
Lemma m_C3_eq : ltac2:(tb__ "0|0|
S13S15S3eS1U2A1S0Z4A3Sb1A3"). Proof. cbv delta [C3 m_C3]; cbv beta zeta. MallocMemoSPW2_all14. reflexivity. Qed.
Ltac MallocMemoSPW2_sub15 t := let t := MallocMemoSPW2_sub14 t in lazymatch (eval pattern (C3 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C3) end.
Ltac MallocMemoSPW2_all15 := MallocMemoSPW2_all14; MemoFast.memo_rw m_C3_eq.
Definition m_run4 : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Z7e9e4S8S21A1A3Sb1ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run4_eq : ltac2:(tb__ "0|0|
S13SaS14A1S88S1U2A1S0Z4A3Sd9A3"). Proof. cbv delta [run4 m_run4]; cbv beta zeta. MallocMemoSPW2_all15. reflexivity. Qed.
Ltac MallocMemoSPW2_sub16 t := let t := MallocMemoSPW2_sub15 t in lazymatch (eval pattern (run4 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_run4) end.
Ltac MallocMemoSPW2_all16 := MallocMemoSPW2_all15; MemoFast.memo_rw m_run4_eq.
Definition m_E4d : axst := ltac2:(tb__ "0|0|
S22U0Sd9A2").
Lemma m_E4d_eq : ltac2:(tb__ "0|0|
S13S15S5aS1U2A1S0Z4A3Sc9A3"). Proof. cbv delta [E4d m_E4d]; cbv beta zeta. MallocMemoSPW2_all16. reflexivity. Qed.
Ltac MallocMemoSPW2_sub17 t := let t := MallocMemoSPW2_sub16 t in lazymatch (eval pattern (E4d (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E4d) end.
Ltac MallocMemoSPW2_all17 := MallocMemoSPW2_all16; MemoFast.memo_rw m_E4d_eq.
Definition m_C5 : axst := ltac2:(tb__ "0|1|
S84S23S1U2A1S0Z4Sc9Z7ec58S9S11SdS18A2M0SeSdS18UaS1cPaaA1A4S9G0SeSdS18U1S1bZ3c720A1A4S28A3A3S8S1aA1S10S8S19A1A9A1").
Lemma m_C5_eq : ltac2:(tb__ "0|0|
S13S15S3fS1U2A1S0Z4A3Sb2A3"). Proof. cbv delta [C5 m_C5]; cbv beta zeta. MallocMemoSPW2_all17. reflexivity. Qed.
Ltac MallocMemoSPW2_sub18 t := let t := MallocMemoSPW2_sub17 t in lazymatch (eval pattern (C5 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C5) end.
Ltac MallocMemoSPW2_all18 := MallocMemoSPW2_all17; MemoFast.memo_rw m_C5_eq.
Definition m_run5 : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Z3c774S9S21Z3c80cS8S21A1A3A3Sb2ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run5_eq : ltac2:(tb__ "0|0|
S13SaS14A1S89S1U2A1S0Z4A3Sa6A3"). Proof. cbv delta [run5 m_run5]; cbv beta zeta. MallocMemoSPW2_all18. reflexivity. Qed.
Ltac MallocMemoSPW2_sub19 t := let t := MallocMemoSPW2_sub18 t in lazymatch (eval pattern (run5 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_run5) end.
Ltac MallocMemoSPW2_all19 := MallocMemoSPW2_all18; MemoFast.memo_rw m_run5_eq.
Definition m_E5n : axst := ltac2:(tb__ "0|0|
S22U0Sa6A2").
Lemma m_E5n_eq : ltac2:(tb__ "0|0|
S13S15S5fS1U2A1S0Z4A3ScdA3"). Proof. cbv delta [E5n m_E5n]; cbv beta zeta. MallocMemoSPW2_all19. reflexivity. Qed.
Ltac MallocMemoSPW2_sub20 t := let t := MallocMemoSPW2_sub19 t in lazymatch (eval pattern (E5n (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E5n) end.
Ltac MallocMemoSPW2_all20 := MallocMemoSPW2_all19; MemoFast.memo_rw m_E5n_eq.
Definition m_E5f : axst := ltac2:(tb__ "0|0|
S22U1Sa6A2").
Lemma m_E5f_eq : ltac2:(tb__ "0|0|
S13S15S5bS1U2A1S0Z4A3ScaA3"). Proof. cbv delta [E5f m_E5f]; cbv beta zeta. MallocMemoSPW2_all20. reflexivity. Qed.
Ltac MallocMemoSPW2_sub21 t := let t := MallocMemoSPW2_sub20 t in lazymatch (eval pattern (E5f (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E5f) end.
Ltac MallocMemoSPW2_all21 := MallocMemoSPW2_all20; MemoFast.memo_rw m_E5f_eq.
Definition m_C5b : axst := ltac2:(tb__ "0|2|
S23S1U2A1S0Z4ScaZ3c774S9S11SdS18A2M0SeSdS18U8S1cS7cA1M1A4S9G0SeSdS18UaG1A4S8G0A1A3A3S8S1aA1S10S8S19A1A9").
Lemma m_C5b_eq : ltac2:(tb__ "0|0|
S13S15S40S1U2A1S0Z4A3Sb3A3"). Proof. cbv delta [C5b m_C5b]; cbv beta zeta. MallocMemoSPW2_all21. reflexivity. Qed.
Ltac MallocMemoSPW2_sub22 t := let t := MallocMemoSPW2_sub21 t in lazymatch (eval pattern (C5b (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C5b) end.
Ltac MallocMemoSPW2_all22 := MallocMemoSPW2_all21; MemoFast.memo_rw m_C5b_eq.
Definition m_run5b : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Z3c7e0S8S21A1A3Sb3ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run5b_eq : ltac2:(tb__ "0|0|
S13SaS14A1S8aS1U2A1S0Z4A3Sa7A3"). Proof. cbv delta [run5b m_run5b]; cbv beta zeta. MallocMemoSPW2_all22. reflexivity. Qed.
Ltac MallocMemoSPW2_sub23 t := let t := MallocMemoSPW2_sub22 t in lazymatch (eval pattern (run5b (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_run5b) end.
Ltac MallocMemoSPW2_all23 := MallocMemoSPW2_all22; MemoFast.memo_rw m_run5b_eq.
Definition m_E5s1 : axst := ltac2:(tb__ "0|0|
S22U0Sa7A2").
Lemma m_E5s1_eq : ltac2:(tb__ "0|0|
S13S15S60S1U2A1S0Z4A3Sa2A3"). Proof. cbv delta [E5s1 m_E5s1]; cbv beta zeta. MallocMemoSPW2_all23. reflexivity. Qed.
Ltac MallocMemoSPW2_sub24 t := let t := MallocMemoSPW2_sub23 t in lazymatch (eval pattern (E5s1 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E5s1) end.
Ltac MallocMemoSPW2_all24 := MallocMemoSPW2_all23; MemoFast.memo_rw m_E5s1_eq.
Definition m_E5s2 : axst := ltac2:(tb__ "0|0|
S22U1Sa7A2").
Lemma m_E5s2_eq : ltac2:(tb__ "0|0|
S13S15S61S1U2A1S0Z4A3SceA3"). Proof. cbv delta [E5s2 m_E5s2]; cbv beta zeta. MallocMemoSPW2_all24. reflexivity. Qed.
Ltac MallocMemoSPW2_sub25 t := let t := MallocMemoSPW2_sub24 t in lazymatch (eval pattern (E5s2 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E5s2) end.
Ltac MallocMemoSPW2_all25 := MallocMemoSPW2_all24; MemoFast.memo_rw m_E5s2_eq.
Definition m_sreg1 : sv := ltac2:(tb__ "0|0|
S9cS18U8S1dS17Sa2A1A1S1bZ0A1A4").
Lemma m_sreg1_eq : ltac2:(tb__ "0|0|
S13S18S99S1U2A1S0Z4A3SeeA3"). Proof. cbv delta [sreg1 m_sreg1]; cbv beta zeta. MallocMemoSPW2_all25. reflexivity. Qed.
Ltac MallocMemoSPW2_sub26 t := let t := MallocMemoSPW2_sub25 t in lazymatch (eval pattern (sreg1 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_sreg1) end.
Ltac MallocMemoSPW2_all26 := MallocMemoSPW2_all25; MemoFast.memo_rw m_sreg1_eq.
Definition m_sreg2 : sv := ltac2:(tb__ "0|0|
S9cS18U8S1dS17SceA1A1S1bZ0A1A4").
Lemma m_sreg2_eq : ltac2:(tb__ "0|0|
S13S18S9aS1U2A1S0Z4A3SefA3"). Proof. cbv delta [sreg2 m_sreg2]; cbv beta zeta. MallocMemoSPW2_all26. reflexivity. Qed.
Ltac MallocMemoSPW2_sub27 t := let t := MallocMemoSPW2_sub26 t in lazymatch (eval pattern (sreg2 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_sreg2) end.
Ltac MallocMemoSPW2_all27 := MallocMemoSPW2_all26; MemoFast.memo_rw m_sreg2_eq.
Definition m_C5c : axst := ltac2:(tb__ "0|1|
S27S26S23S1U2A1S0Z4Sa2Z3c7e0S9S11SdS18A2M0SeSdS18U8S1cS7dA1A4S9G0SeSdS18UaS1cPb4A1A4S9G0SeSdS18UbS1cPabA1A4S8G0A1A3A3A3S8S1aA1ScSfS19S24S25A3A9A2").
Lemma m_C5c_eq : ltac2:(tb__ "0|0|
S13S15S41S1U2A1S0Z4A3Sb4A3"). Proof. cbv delta [C5c m_C5c]; cbv beta zeta. MallocMemoSPW2_all27. reflexivity. Qed.
Ltac MallocMemoSPW2_sub28 t := let t := MallocMemoSPW2_sub27 t in lazymatch (eval pattern (C5c (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C5c) end.
Ltac MallocMemoSPW2_all28 := MallocMemoSPW2_all27; MemoFast.memo_rw m_C5c_eq.
Definition m_run5c : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Zdb004S8S21A1A3Sb4ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run5c_eq : ltac2:(tb__ "0|0|
S13SaS14A1S8bS1U2A1S0Z4A3SdaA3"). Proof. cbv delta [run5c m_run5c]; cbv beta zeta. MallocMemoSPW2_all28. reflexivity. Qed.
Ltac MallocMemoSPW2_sub29 t := let t := MallocMemoSPW2_sub28 t in lazymatch (eval pattern (run5c (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_run5c) end.
Ltac MallocMemoSPW2_all29 := MallocMemoSPW2_all28; MemoFast.memo_rw m_run5c_eq.
Definition m_E5m1 : axst := ltac2:(tb__ "0|0|
S22U0SdaA2").
Lemma m_E5m1_eq : ltac2:(tb__ "0|0|
S13S15S5dS1U2A1S0Z4A3ScbA3"). Proof. cbv delta [E5m1 m_E5m1]; cbv beta zeta. MallocMemoSPW2_all29. reflexivity. Qed.
Ltac MallocMemoSPW2_sub30 t := let t := MallocMemoSPW2_sub29 t in lazymatch (eval pattern (E5m1 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E5m1) end.
Ltac MallocMemoSPW2_all30 := MallocMemoSPW2_all29; MemoFast.memo_rw m_E5m1_eq.
Definition m_C5m1 : axst := ltac2:(tb__ "0|1|
S23S1U2A1S0Z4ScbS2aS9S11SdS18A2M0SeSdS18UaS36A4S9G0SeSdS18UcS72A4S8G0A1A3A3S8S1aA1S10S8S19A1A9").
Lemma m_C5m1_eq : ltac2:(tb__ "0|0|
S13S15S44S1U2A1S0Z4A3Sb7A3"). Proof. cbv delta [C5m1 m_C5m1]; cbv beta zeta. MallocMemoSPW2_all30. reflexivity. Qed.
Ltac MallocMemoSPW2_sub31 t := let t := MallocMemoSPW2_sub30 t in lazymatch (eval pattern (C5m1 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C5m1) end.
Ltac MallocMemoSPW2_all31 := MallocMemoSPW2_all30; MemoFast.memo_rw m_C5m1_eq.
Definition m_C5d : axst := ltac2:(tb__ "0|0|
S29U3S30S23S1U2A1S0Z4Sb7S2bS28S8S1aA1S10S8S19A1A9A3").
Lemma m_C5d_eq : ltac2:(tb__ "0|0|
S13S15S42S1U2A1S0Z4A3Sb5A3"). Proof. cbv delta [C5d m_C5d]; cbv beta zeta. MallocMemoSPW2_all31. reflexivity. Qed.
Ltac MallocMemoSPW2_sub32 t := let t := MallocMemoSPW2_sub31 t in lazymatch (eval pattern (C5d (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C5d) end.
Ltac MallocMemoSPW2_all32 := MallocMemoSPW2_all31; MemoFast.memo_rw m_C5d_eq.
Definition m_run5d : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Zdb004S8S21A1A3Sb5ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run5d_eq : ltac2:(tb__ "0|0|
S13SaS14A1S8cS1U2A1S0Z4A3SdbA3"). Proof. cbv delta [run5d m_run5d]; cbv beta zeta. MallocMemoSPW2_all32. reflexivity. Qed.
Ltac MallocMemoSPW2_sub33 t := let t := MallocMemoSPW2_sub32 t in lazymatch (eval pattern (run5d (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_run5d) end.
Ltac MallocMemoSPW2_all33 := MallocMemoSPW2_all32; MemoFast.memo_rw m_run5d_eq.
Definition m_E5m2 : axst := ltac2:(tb__ "0|0|
S22U0SdbA2").
Lemma m_E5m2_eq : ltac2:(tb__ "0|0|
S13S15S5eS1U2A1S0Z4A3SccA3"). Proof. cbv delta [E5m2 m_E5m2]; cbv beta zeta. MallocMemoSPW2_all33. reflexivity. Qed.
Ltac MallocMemoSPW2_sub34 t := let t := MallocMemoSPW2_sub33 t in lazymatch (eval pattern (E5m2 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E5m2) end.
Ltac MallocMemoSPW2_all34 := MallocMemoSPW2_all33; MemoFast.memo_rw m_E5m2_eq.
Definition m_C5m2 : axst := ltac2:(tb__ "0|1|
S23S1U2A1S0Z4SccS2aS9S11SdS18A2M0SeSdS18UaS35A4S9G0SeSdS18UcS74A4S8G0A1A3A3S8S1aA1S10S8S19A1A9").
Lemma m_C5m2_eq : ltac2:(tb__ "0|0|
S13S15S45S1U2A1S0Z4A3Sb8A3"). Proof. cbv delta [C5m2 m_C5m2]; cbv beta zeta. MallocMemoSPW2_all34. reflexivity. Qed.
Ltac MallocMemoSPW2_sub35 t := let t := MallocMemoSPW2_sub34 t in lazymatch (eval pattern (C5m2 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C5m2) end.
Ltac MallocMemoSPW2_all35 := MallocMemoSPW2_all34; MemoFast.memo_rw m_C5m2_eq.
Definition m_C5e : axst := ltac2:(tb__ "0|0|
S29U0S75S23S1U2A1S0Z4Sb8S2bS28S8S1aA1S10S8S19A1A9A3").
Lemma m_C5e_eq : ltac2:(tb__ "0|0|
S13S15S43S1U2A1S0Z4A3Sb6A3"). Proof. cbv delta [C5e m_C5e]; cbv beta zeta. MallocMemoSPW2_all35. reflexivity. Qed.
Ltac MallocMemoSPW2_sub36 t := let t := MallocMemoSPW2_sub35 t in lazymatch (eval pattern (C5e (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C5e) end.
Ltac MallocMemoSPW2_all36 := MallocMemoSPW2_all35; MemoFast.memo_rw m_C5e_eq.
Definition m_run5e : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Z3c80cS8S21A1A3Sb6ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run5e_eq : ltac2:(tb__ "0|0|
S13SaS14A1S8dS1U2A1S0Z4A3SdcA3"). Proof. cbv delta [run5e m_run5e]; cbv beta zeta. MallocMemoSPW2_all36. reflexivity. Qed.
Ltac MallocMemoSPW2_sub37 t := let t := MallocMemoSPW2_sub36 t in lazymatch (eval pattern (run5e (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_run5e) end.
Ltac MallocMemoSPW2_all37 := MallocMemoSPW2_all36; MemoFast.memo_rw m_run5e_eq.
Definition m_E5j : axst := ltac2:(tb__ "0|0|
S22U0SdcA2").
Lemma m_E5j_eq : ltac2:(tb__ "0|0|
S13S15S5cS1U2A1S0Z4A3Se0A3"). Proof. cbv delta [E5j m_E5j]; cbv beta zeta. MallocMemoSPW2_all37. reflexivity. Qed.
Ltac MallocMemoSPW2_sub38 t := let t := MallocMemoSPW2_sub37 t in lazymatch (eval pattern (E5j (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E5j) end.
Ltac MallocMemoSPW2_all38 := MallocMemoSPW2_all37; MemoFast.memo_rw m_E5j_eq.
Definition m_C6 : axst := ltac2:(tb__ "0|0|
S27S26S29U3S30S23S1U2A1S0Z4ScdZ3c80cS71S8S1aA1ScSfS19S24S25A3A9A3A2").
Lemma m_C6_eq : ltac2:(tb__ "0|0|
S13S15S46S1U2A1S0Z4A3Sb9A3"). Proof. cbv delta [C6 m_C6]; cbv beta zeta. MallocMemoSPW2_all38. reflexivity. Qed.
Ltac MallocMemoSPW2_sub39 t := let t := MallocMemoSPW2_sub38 t in lazymatch (eval pattern (C6 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C6) end.
Ltac MallocMemoSPW2_all39 := MallocMemoSPW2_all38; MemoFast.memo_rw m_C6_eq.
Definition m_run6 : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Z5f9f8S9S21Z3c82cS8S21A1A3A3Sb9ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run6_eq : ltac2:(tb__ "0|0|
S13SaS14A1S8eS1U2A1S0Z4A3Sa8A3"). Proof. cbv delta [run6 m_run6]; cbv beta zeta. MallocMemoSPW2_all39. reflexivity. Qed.
Ltac MallocMemoSPW2_sub40 t := let t := MallocMemoSPW2_sub39 t in lazymatch (eval pattern (run6 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_run6) end.
Ltac MallocMemoSPW2_all40 := MallocMemoSPW2_all39; MemoFast.memo_rw m_run6_eq.
Definition m_E6s : axst := ltac2:(tb__ "0|0|
S22U0Sa8A2").
Lemma m_E6s_eq : ltac2:(tb__ "0|0|
S13S15S65S1U2A1S0Z4A3Se1A3"). Proof. cbv delta [E6s m_E6s]; cbv beta zeta. MallocMemoSPW2_all40. reflexivity. Qed.
Ltac MallocMemoSPW2_sub41 t := let t := MallocMemoSPW2_sub40 t in lazymatch (eval pattern (E6s (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E6s) end.
Ltac MallocMemoSPW2_all41 := MallocMemoSPW2_all40; MemoFast.memo_rw m_E6s_eq.
Definition m_E6l : axst := ltac2:(tb__ "0|0|
S22U1Sa8A2").
Lemma m_E6l_eq : ltac2:(tb__ "0|0|
S13S15S63S1U2A1S0Z4A3Sd0A3"). Proof. cbv delta [E6l m_E6l]; cbv beta zeta. MallocMemoSPW2_all41. reflexivity. Qed.
Ltac MallocMemoSPW2_sub42 t := let t := MallocMemoSPW2_sub41 t in lazymatch (eval pattern (E6l (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E6l) end.
Ltac MallocMemoSPW2_all42 := MallocMemoSPW2_all41; MemoFast.memo_rw m_E6l_eq.
Definition m_C6l : axst := ltac2:(tb__ "0|1|
S23S1U2A1S0Z4Sd0Z5f9f8S9S11SdS18A2M0SeSdS18U8S2fA4S8G0A1A3S8S1aA1S10S8S19A1A9").
Lemma m_C6l_eq : ltac2:(tb__ "0|0|
S13S15S48S1U2A1S0Z4A3SbbA3"). Proof. cbv delta [C6l m_C6l]; cbv beta zeta. MallocMemoSPW2_all42. reflexivity. Qed.
Ltac MallocMemoSPW2_sub43 t := let t := MallocMemoSPW2_sub42 t in lazymatch (eval pattern (C6l (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C6l) end.
Ltac MallocMemoSPW2_all43 := MallocMemoSPW2_all42; MemoFast.memo_rw m_C6l_eq.
Definition m_run6l : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Zdb004S8S21A1A3SbbScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run6l_eq : ltac2:(tb__ "0|0|
S13SaS14A1S90S1U2A1S0Z4A3SdeA3"). Proof. cbv delta [run6l m_run6l]; cbv beta zeta. MallocMemoSPW2_all43. reflexivity. Qed.
Ltac MallocMemoSPW2_sub44 t := let t := MallocMemoSPW2_sub43 t in lazymatch (eval pattern (run6l (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_run6l) end.
Ltac MallocMemoSPW2_all44 := MallocMemoSPW2_all43; MemoFast.memo_rw m_run6l_eq.
Definition m_E6m : axst := ltac2:(tb__ "0|0|
S22U0SdeA2").
Lemma m_E6m_eq : ltac2:(tb__ "0|0|
S13S15S64S1U2A1S0Z4A3Sd1A3"). Proof. cbv delta [E6m m_E6m]; cbv beta zeta. MallocMemoSPW2_all44. reflexivity. Qed.
Ltac MallocMemoSPW2_sub45 t := let t := MallocMemoSPW2_sub44 t in lazymatch (eval pattern (E6m (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E6m) end.
Ltac MallocMemoSPW2_all45 := MallocMemoSPW2_all44; MemoFast.memo_rw m_E6m_eq.
Definition m_C6m : axst := ltac2:(tb__ "0|1|
S23S1U2A1S0Z4Sd1S2aS9S11SdS18A2M0SeSdS18UaS37A4S9G0SeSdS18UcS2fA4S8G0A1A3A3S8S1aA1S10S8S19A1A9").
Lemma m_C6m_eq : ltac2:(tb__ "0|0|
S13S15S49S1U2A1S0Z4A3SbcA3"). Proof. cbv delta [C6m m_C6m]; cbv beta zeta. MallocMemoSPW2_all45. reflexivity. Qed.
Ltac MallocMemoSPW2_sub46 t := let t := MallocMemoSPW2_sub45 t in lazymatch (eval pattern (C6m (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C6m) end.
Ltac MallocMemoSPW2_all46 := MallocMemoSPW2_all45; MemoFast.memo_rw m_C6m_eq.
Definition m_C6b : axst := ltac2:(tb__ "0|1|
S29U2M0S76S23S1G0A1S0Z4SbcS2bS28S8S1aA1S10S8S19A1A9A3").
Lemma m_C6b_eq : ltac2:(tb__ "0|0|
S13S15S47S1U2A1S0Z4A3SbaA3"). Proof. cbv delta [C6b m_C6b]; cbv beta zeta. MallocMemoSPW2_all46. reflexivity. Qed.
Ltac MallocMemoSPW2_sub47 t := let t := MallocMemoSPW2_sub46 t in lazymatch (eval pattern (C6b (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C6b) end.
Ltac MallocMemoSPW2_all47 := MallocMemoSPW2_all46; MemoFast.memo_rw m_C6b_eq.
Definition m_run6b : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Z3c82cS8S21A1A3SbaScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run6b_eq : ltac2:(tb__ "0|0|
S13SaS14A1S8fS1U2A1S0Z4A3SddA3"). Proof. cbv delta [run6b m_run6b]; cbv beta zeta. MallocMemoSPW2_all47. reflexivity. Qed.
Ltac MallocMemoSPW2_sub48 t := let t := MallocMemoSPW2_sub47 t in lazymatch (eval pattern (run6b (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_run6b) end.
Ltac MallocMemoSPW2_all48 := MallocMemoSPW2_all47; MemoFast.memo_rw m_run6b_eq.
Definition m_E6j : axst := ltac2:(tb__ "0|0|
S22U0SddA2").
Lemma m_E6j_eq : ltac2:(tb__ "0|0|
S13S15S62S1U2A1S0Z4A3ScfA3"). Proof. cbv delta [E6j m_E6j]; cbv beta zeta. MallocMemoSPW2_all48. reflexivity. Qed.
Ltac MallocMemoSPW2_sub49 t := let t := MallocMemoSPW2_sub48 t in lazymatch (eval pattern (E6j (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E6j) end.
Ltac MallocMemoSPW2_all49 := MallocMemoSPW2_all48; MemoFast.memo_rw m_E6j_eq.
Definition m_C7 : axst := ltac2:(tb__ "0|0|
S27S26S23S1U2A1S0Z4ScfZ3c82cS70S8S1aA1ScSfS19S24S25A3A9A2").
Lemma m_C7_eq : ltac2:(tb__ "0|0|
S13S15S4aS1U2A1S0Z4A3SbdA3"). Proof. cbv delta [C7 m_C7]; cbv beta zeta. MallocMemoSPW2_all49. reflexivity. Qed.
Ltac MallocMemoSPW2_sub50 t := let t := MallocMemoSPW2_sub49 t in lazymatch (eval pattern (C7 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C7) end.
Ltac MallocMemoSPW2_all50 := MallocMemoSPW2_all49; MemoFast.memo_rw m_C7_eq.
Definition m_run7 : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Z3c8bcS9S21Z3ca04S8S21A1A3A3SbdScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run7_eq : ltac2:(tb__ "0|0|
S13SaS14A1S91S1U2A1S0Z4A3S9fA3"). Proof. cbv delta [run7 m_run7]; cbv beta zeta. MallocMemoSPW2_all50. reflexivity. Qed.
Ltac MallocMemoSPW2_sub51 t := let t := MallocMemoSPW2_sub50 t in lazymatch (eval pattern (run7 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_run7) end.
Ltac MallocMemoSPW2_all51 := MallocMemoSPW2_all50; MemoFast.memo_rw m_run7_eq.
Definition m_E7c1 : axst := ltac2:(tb__ "0|0|
S22U0S9fA2").
Lemma m_E7c1_eq : ltac2:(tb__ "0|0|
S13S15S66S1U2A1S0Z4A3Sa3A3"). Proof. cbv delta [E7c1 m_E7c1]; cbv beta zeta. MallocMemoSPW2_all51. reflexivity. Qed.
Ltac MallocMemoSPW2_sub52 t := let t := MallocMemoSPW2_sub51 t in lazymatch (eval pattern (E7c1 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E7c1) end.
Ltac MallocMemoSPW2_all52 := MallocMemoSPW2_all51; MemoFast.memo_rw m_E7c1_eq.
Definition m_E7c2 : axst := ltac2:(tb__ "0|0|
S22U1S9fA2").
Lemma m_E7c2_eq : ltac2:(tb__ "0|0|
S13S15S67S1U2A1S0Z4A3Sd2A3"). Proof. cbv delta [E7c2 m_E7c2]; cbv beta zeta. MallocMemoSPW2_all52. reflexivity. Qed.
Ltac MallocMemoSPW2_sub53 t := let t := MallocMemoSPW2_sub52 t in lazymatch (eval pattern (E7c2 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E7c2) end.
Ltac MallocMemoSPW2_all53 := MallocMemoSPW2_all52; MemoFast.memo_rw m_E7c2_eq.
Definition m_E7p : axst := ltac2:(tb__ "0|0|
S22U2S9fA2").
Lemma m_E7p_eq : ltac2:(tb__ "0|0|
S13S15S68S1U2A1S0Z4A3Sd3A3"). Proof. cbv delta [E7p m_E7p]; cbv beta zeta. MallocMemoSPW2_all53. reflexivity. Qed.
Ltac MallocMemoSPW2_sub54 t := let t := MallocMemoSPW2_sub53 t in lazymatch (eval pattern (E7p (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E7p) end.
Ltac MallocMemoSPW2_all54 := MallocMemoSPW2_all53; MemoFast.memo_rw m_E7p_eq.
Definition m_creg7a : sv := ltac2:(tb__ "0|0|
S9cS18UbS1dS17Sa3A1A1S1bZ0A1A4").
Lemma m_creg7a_eq : ltac2:(tb__ "0|0|
S13S18S7eS1U2A1S0Z4A3Se4A3"). Proof. cbv delta [creg7a m_creg7a]; cbv beta zeta. MallocMemoSPW2_all54. reflexivity. Qed.
Ltac MallocMemoSPW2_sub55 t := let t := MallocMemoSPW2_sub54 t in lazymatch (eval pattern (creg7a (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_creg7a) end.
Ltac MallocMemoSPW2_all55 := MallocMemoSPW2_all54; MemoFast.memo_rw m_creg7a_eq.
Definition m_creg7b : sv := ltac2:(tb__ "0|0|
S9cS18UbS1dS17Sd2A1A1S1bZ0A1A4").
Lemma m_creg7b_eq : ltac2:(tb__ "0|0|
S13S18S7fS1U2A1S0Z4A3Se5A3"). Proof. cbv delta [creg7b m_creg7b]; cbv beta zeta. MallocMemoSPW2_all55. reflexivity. Qed.
Ltac MallocMemoSPW2_sub56 t := let t := MallocMemoSPW2_sub55 t in lazymatch (eval pattern (creg7b (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_creg7b) end.
Ltac MallocMemoSPW2_all56 := MallocMemoSPW2_all55; MemoFast.memo_rw m_creg7b_eq.
Definition m_C7p : axst := ltac2:(tb__ "0|1|
S23S1U2A1S0Z4Sd3Z3c8bcS9S11SdS18A2M0SeSdS18UaS34A4S8G0A1A3S8S1aA1S10S9S19S1eS1bZ1A1S73A2S8S19A1A3A9").
Lemma m_C7p_eq : ltac2:(tb__ "0|0|
S13S15S4bS1U2A1S0Z4A3SbeA3"). Proof. cbv delta [C7p m_C7p]; cbv beta zeta. MallocMemoSPW2_all56. reflexivity. Qed.
Ltac MallocMemoSPW2_sub57 t := let t := MallocMemoSPW2_sub56 t in lazymatch (eval pattern (C7p (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C7p) end.
Ltac MallocMemoSPW2_all57 := MallocMemoSPW2_all56; MemoFast.memo_rw m_C7p_eq.
Definition m_run7p : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Z3ca04S8S21A1A3SbeScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run7p_eq : ltac2:(tb__ "0|0|
S13SaS14A1S92S1U2A1S0Z4A3Sa9A3"). Proof. cbv delta [run7p m_run7p]; cbv beta zeta. MallocMemoSPW2_all57. reflexivity. Qed.
Ltac MallocMemoSPW2_sub58 t := let t := MallocMemoSPW2_sub57 t in lazymatch (eval pattern (run7p (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_run7p) end.
Ltac MallocMemoSPW2_all58 := MallocMemoSPW2_all57; MemoFast.memo_rw m_run7p_eq.
Definition m_E7q1 : axst := ltac2:(tb__ "0|0|
S22U0Sa9A2").
Lemma m_E7q1_eq : ltac2:(tb__ "0|0|
S13S15S69S1U2A1S0Z4A3Sa4A3"). Proof. cbv delta [E7q1 m_E7q1]; cbv beta zeta. MallocMemoSPW2_all58. reflexivity. Qed.
Ltac MallocMemoSPW2_sub59 t := let t := MallocMemoSPW2_sub58 t in lazymatch (eval pattern (E7q1 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E7q1) end.
Ltac MallocMemoSPW2_all59 := MallocMemoSPW2_all58; MemoFast.memo_rw m_E7q1_eq.
Definition m_E7q2 : axst := ltac2:(tb__ "0|0|
S22U1Sa9A2").
Lemma m_E7q2_eq : ltac2:(tb__ "0|0|
S13S15S6aS1U2A1S0Z4A3Sd4A3"). Proof. cbv delta [E7q2 m_E7q2]; cbv beta zeta. MallocMemoSPW2_all59. reflexivity. Qed.
Ltac MallocMemoSPW2_sub60 t := let t := MallocMemoSPW2_sub59 t in lazymatch (eval pattern (E7q2 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E7q2) end.
Ltac MallocMemoSPW2_all60 := MallocMemoSPW2_all59; MemoFast.memo_rw m_E7q2_eq.
Definition m_creg7c : sv := ltac2:(tb__ "0|0|
S9cS18UbS1dS17Sa4A1A1S1bZ0A1A4").
Lemma m_creg7c_eq : ltac2:(tb__ "0|0|
S13S18S80S1U2A1S0Z4A3Se6A3"). Proof. cbv delta [creg7c m_creg7c]; cbv beta zeta. MallocMemoSPW2_all60. reflexivity. Qed.
Ltac MallocMemoSPW2_sub61 t := let t := MallocMemoSPW2_sub60 t in lazymatch (eval pattern (creg7c (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_creg7c) end.
Ltac MallocMemoSPW2_all61 := MallocMemoSPW2_all60; MemoFast.memo_rw m_creg7c_eq.
Definition m_creg7d : sv := ltac2:(tb__ "0|0|
S9cS18UbS1dS17Sd4A1A1S1bZ0A1A4").
Lemma m_creg7d_eq : ltac2:(tb__ "0|0|
S13S18S81S1U2A1S0Z4A3Se7A3"). Proof. cbv delta [creg7d m_creg7d]; cbv beta zeta. MallocMemoSPW2_all61. reflexivity. Qed.
Ltac MallocMemoSPW2_sub62 t := let t := MallocMemoSPW2_sub61 t in lazymatch (eval pattern (creg7d (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_creg7d) end.
Ltac MallocMemoSPW2_all62 := MallocMemoSPW2_all61; MemoFast.memo_rw m_creg7d_eq.
Definition m_C8 : axst := ltac2:(tb__ "0|0|
S27S26S23S1U2A1S0Z4Sa3Z3ca04S2eS8S1aA1ScSfS19S24S25A3A9A2").
Lemma m_C8_eq : ltac2:(tb__ "0|0|
S13S15S4cS1U2A1S0Z4A3SbfA3"). Proof. cbv delta [C8 m_C8]; cbv beta zeta. MallocMemoSPW2_all62. reflexivity. Qed.
Ltac MallocMemoSPW2_sub63 t := let t := MallocMemoSPW2_sub62 t in lazymatch (eval pattern (C8 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C8) end.
Ltac MallocMemoSPW2_all63 := MallocMemoSPW2_all62; MemoFast.memo_rw m_C8_eq.
Definition m_C8p : axst := ltac2:(tb__ "0|0|
S27S26S23S1U2A1S0Z4Sa4Z3ca04S2eS8S1aA1ScSfS19S24S25A3A9A2").
Lemma m_C8p_eq : ltac2:(tb__ "0|0|
S13S15S4fS1U2A1S0Z4A3Sc2A3"). Proof. cbv delta [C8p m_C8p]; cbv beta zeta. MallocMemoSPW2_all63. reflexivity. Qed.
Ltac MallocMemoSPW2_sub64 t := let t := MallocMemoSPW2_sub63 t in lazymatch (eval pattern (C8p (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C8p) end.
Ltac MallocMemoSPW2_all64 := MallocMemoSPW2_all63; MemoFast.memo_rw m_C8p_eq.
Definition m_run8 : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Zdb004S9S21Z3ca54S8S21A1A3A3SbfScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run8_eq : ltac2:(tb__ "0|0|
S13SaS14A1S93S1U2A1S0Z4A3SaaA3"). Proof. cbv delta [run8 m_run8]; cbv beta zeta. MallocMemoSPW2_all64. reflexivity. Qed.
Ltac MallocMemoSPW2_sub65 t := let t := MallocMemoSPW2_sub64 t in lazymatch (eval pattern (run8 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_run8) end.
Ltac MallocMemoSPW2_all65 := MallocMemoSPW2_all64; MemoFast.memo_rw m_run8_eq.
Definition m_run8p : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S9S21Zdb004S9S21Z3ca54S8S21A1A3A3Sc2ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run8p_eq : ltac2:(tb__ "0|0|
S13SaS14A1S94S1U2A1S0Z4A3SabA3"). Proof. cbv delta [run8p m_run8p]; cbv beta zeta. MallocMemoSPW2_all65. reflexivity. Qed.
Ltac MallocMemoSPW2_sub66 t := let t := MallocMemoSPW2_sub65 t in lazymatch (eval pattern (run8p (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_run8p) end.
Ltac MallocMemoSPW2_all66 := MallocMemoSPW2_all65; MemoFast.memo_rw m_run8p_eq.
Definition m_E8a : axst := ltac2:(tb__ "0|0|
S22U0SaaA2").
Lemma m_E8a_eq : ltac2:(tb__ "0|0|
S13S15S6bS1U2A1S0Z4A3Sd5A3"). Proof. cbv delta [E8a m_E8a]; cbv beta zeta. MallocMemoSPW2_all66. reflexivity. Qed.
Ltac MallocMemoSPW2_sub67 t := let t := MallocMemoSPW2_sub66 t in lazymatch (eval pattern (E8a (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E8a) end.
Ltac MallocMemoSPW2_all67 := MallocMemoSPW2_all66; MemoFast.memo_rw m_E8a_eq.
Definition m_E8b : axst := ltac2:(tb__ "0|0|
S22U1SaaA2").
Lemma m_E8b_eq : ltac2:(tb__ "0|0|
S13S15S6cS1U2A1S0Z4A3Se2A3"). Proof. cbv delta [E8b m_E8b]; cbv beta zeta. MallocMemoSPW2_all67. reflexivity. Qed.
Ltac MallocMemoSPW2_sub68 t := let t := MallocMemoSPW2_sub67 t in lazymatch (eval pattern (E8b (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E8b) end.
Ltac MallocMemoSPW2_all68 := MallocMemoSPW2_all67; MemoFast.memo_rw m_E8b_eq.
Definition m_E8pa : axst := ltac2:(tb__ "0|0|
S22U0SabA2").
Lemma m_E8pa_eq : ltac2:(tb__ "0|0|
S13S15S6dS1U2A1S0Z4A3Sd6A3"). Proof. cbv delta [E8pa m_E8pa]; cbv beta zeta. MallocMemoSPW2_all68. reflexivity. Qed.
Ltac MallocMemoSPW2_sub69 t := let t := MallocMemoSPW2_sub68 t in lazymatch (eval pattern (E8pa (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E8pa) end.
Ltac MallocMemoSPW2_all69 := MallocMemoSPW2_all68; MemoFast.memo_rw m_E8pa_eq.
Definition m_E8pb : axst := ltac2:(tb__ "0|0|
S22U1SabA2").
Lemma m_E8pb_eq : ltac2:(tb__ "0|0|
S13S15S6eS1U2A1S0Z4A3Se3A3"). Proof. cbv delta [E8pb m_E8pb]; cbv beta zeta. MallocMemoSPW2_all69. reflexivity. Qed.
Ltac MallocMemoSPW2_sub70 t := let t := MallocMemoSPW2_sub69 t in lazymatch (eval pattern (E8pb (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_E8pb) end.
Ltac MallocMemoSPW2_all70 := MallocMemoSPW2_all69; MemoFast.memo_rw m_E8pb_eq.
Definition m_C8ma : axst := ltac2:(tb__ "0|1|
S23S1U2A1S0Z4Sd5S2aS9S11SdS18A2M0SeSdS18UaS33A4S8G0A1A3S8S1aA1S10S8S19A1A9").
Lemma m_C8ma_eq : ltac2:(tb__ "0|0|
S13S15S4dS1U2A1S0Z4A3Sc0A3"). Proof. cbv delta [C8ma m_C8ma]; cbv beta zeta. MallocMemoSPW2_all70. reflexivity. Qed.
Ltac MallocMemoSPW2_sub71 t := let t := MallocMemoSPW2_sub70 t in lazymatch (eval pattern (C8ma (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C8ma) end.
Ltac MallocMemoSPW2_all71 := MallocMemoSPW2_all70; MemoFast.memo_rw m_C8ma_eq.
Definition m_C8mpa : axst := ltac2:(tb__ "0|1|
S23S1U2A1S0Z4Sd6S2aS9S11SdS18A2M0SeSdS18UaS33A4S8G0A1A3S8S1aA1S10S8S19A1A9").
Lemma m_C8mpa_eq : ltac2:(tb__ "0|0|
S13S15S4eS1U2A1S0Z4A3Sc1A3"). Proof. cbv delta [C8mpa m_C8mpa]; cbv beta zeta. MallocMemoSPW2_all71. reflexivity. Qed.
Ltac MallocMemoSPW2_sub72 t := let t := MallocMemoSPW2_sub71 t in lazymatch (eval pattern (C8mpa (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C8mpa) end.
Ltac MallocMemoSPW2_all72 := MallocMemoSPW2_all71; MemoFast.memo_rw m_C8mpa_eq.
Definition m_C9 : axst := ltac2:(tb__ "0|0|
S27S26S29U5S31S23S1U2A1S0Z4Sc0S2bS28S8S1aA1ScSfS19S24S25A3A9A3A2").
Lemma m_C9_eq : ltac2:(tb__ "0|0|
S13S15S50S1U2A1S0Z4A3Sa0A3"). Proof. cbv delta [C9 m_C9]; cbv beta zeta. MallocMemoSPW2_all72. reflexivity. Qed.
Ltac MallocMemoSPW2_sub73 t := let t := MallocMemoSPW2_sub72 t in lazymatch (eval pattern (C9 (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C9) end.
Ltac MallocMemoSPW2_all73 := MallocMemoSPW2_all72; MemoFast.memo_rw m_C9_eq.
Definition m_C9p : axst := ltac2:(tb__ "0|0|
S27S26S29U5S31S23S1U2A1S0Z4Sc1S2bS28S8S1aA1ScSfS19S24S25A3A9A3A2").
Lemma m_C9p_eq : ltac2:(tb__ "0|0|
S13S15S53S1U2A1S0Z4A3Sa1A3"). Proof. cbv delta [C9p m_C9p]; cbv beta zeta. MallocMemoSPW2_all73. reflexivity. Qed.
Ltac MallocMemoSPW2_sub74 t := let t := MallocMemoSPW2_sub73 t in lazymatch (eval pattern (C9p (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C9p) end.
Ltac MallocMemoSPW2_all74 := MallocMemoSPW2_all73; MemoFast.memo_rw m_C9p_eq.
Definition m_C9a : axst := ltac2:(tb__ "0|0|
S9dS9S19S1eS1bZ20A1S1cS2cA1A2S8S19A1A3Sa0A2").
Lemma m_C9a_eq : ltac2:(tb__ "0|0|
S13S15S51S1U2A1S0Z4A3Sc3A3"). Proof. cbv delta [C9a m_C9a]; cbv beta zeta. MallocMemoSPW2_all74. reflexivity. Qed.
Ltac MallocMemoSPW2_sub75 t := let t := MallocMemoSPW2_sub74 t in lazymatch (eval pattern (C9a (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C9a) end.
Ltac MallocMemoSPW2_all75 := MallocMemoSPW2_all74; MemoFast.memo_rw m_C9a_eq.
Definition m_C9b : axst := ltac2:(tb__ "0|0|
S9dS9S19S1eS1cS2cA1S1bZ10A1A2S8S19A1A3Sa0A2").
Lemma m_C9b_eq : ltac2:(tb__ "0|0|
S13S15S52S1U2A1S0Z4A3Sc4A3"). Proof. cbv delta [C9b m_C9b]; cbv beta zeta. MallocMemoSPW2_all75. reflexivity. Qed.
Ltac MallocMemoSPW2_sub76 t := let t := MallocMemoSPW2_sub75 t in lazymatch (eval pattern (C9b (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C9b) end.
Ltac MallocMemoSPW2_all76 := MallocMemoSPW2_all75; MemoFast.memo_rw m_C9b_eq.
Definition m_C9pa : axst := ltac2:(tb__ "0|0|
S9dS9S19S1eS1bZ20A1S1cS2cA1A2S8S19A1A3Sa1A2").
Lemma m_C9pa_eq : ltac2:(tb__ "0|0|
S13S15S54S1U2A1S0Z4A3Sc5A3"). Proof. cbv delta [C9pa m_C9pa]; cbv beta zeta. MallocMemoSPW2_all76. reflexivity. Qed.
Ltac MallocMemoSPW2_sub77 t := let t := MallocMemoSPW2_sub76 t in lazymatch (eval pattern (C9pa (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C9pa) end.
Ltac MallocMemoSPW2_all77 := MallocMemoSPW2_all76; MemoFast.memo_rw m_C9pa_eq.
Definition m_C9pb : axst := ltac2:(tb__ "0|0|
S9dS9S19S1eS1cS2cA1S1bZ10A1A2S8S19A1A3Sa1A2").
Lemma m_C9pb_eq : ltac2:(tb__ "0|0|
S13S15S55S1U2A1S0Z4A3Sc6A3"). Proof. cbv delta [C9pb m_C9pb]; cbv beta zeta. MallocMemoSPW2_all77. reflexivity. Qed.
Ltac MallocMemoSPW2_sub78 t := let t := MallocMemoSPW2_sub77 t in lazymatch (eval pattern (C9pb (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_C9pb) end.
Ltac MallocMemoSPW2_all78 := MallocMemoSPW2_all77; MemoFast.memo_rw m_C9pb_eq.
Definition m_run9a : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S8S21A1Sc3ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run9a_eq : ltac2:(tb__ "0|0|
S13SaS14A1S95S1U2A1S0Z4A3SeaA3"). Proof. cbv delta [run9a m_run9a]; cbv beta zeta. MallocMemoSPW2_all78. reflexivity. Qed.
Ltac MallocMemoSPW2_sub79 t := let t := MallocMemoSPW2_sub78 t in lazymatch (eval pattern (run9a (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_run9a) end.
Ltac MallocMemoSPW2_all79 := MallocMemoSPW2_all78; MemoFast.memo_rw m_run9a_eq.
Definition m_run9b : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S8S21A1Sc4ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run9b_eq : ltac2:(tb__ "0|0|
S13SaS14A1S96S1U2A1S0Z4A3SebA3"). Proof. cbv delta [run9b m_run9b]; cbv beta zeta. MallocMemoSPW2_all79. reflexivity. Qed.
Ltac MallocMemoSPW2_sub80 t := let t := MallocMemoSPW2_sub79 t in lazymatch (eval pattern (run9b (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_run9b) end.
Ltac MallocMemoSPW2_all80 := MallocMemoSPW2_all79; MemoFast.memo_rw m_run9b_eq.
Definition m_run9pa : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S8S21A1Sc5ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run9pa_eq : ltac2:(tb__ "0|0|
S13SaS14A1S97S1U2A1S0Z4A3SecA3"). Proof. cbv delta [run9pa m_run9pa]; cbv beta zeta. MallocMemoSPW2_all80. reflexivity. Qed.
Ltac MallocMemoSPW2_sub81 t := let t := MallocMemoSPW2_sub80 t in lazymatch (eval pattern (run9pa (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_run9pa) end.
Ltac MallocMemoSPW2_all81 := MallocMemoSPW2_all80; MemoFast.memo_rw m_run9pa_eq.
Definition m_run9pb : list leafA := ltac2:(tb__ "0|1|
SbSaS14A1M0A1G0Lx;S16S9bUfa0S8S21A1Sc6ScA5G0R1Ll;S8S14A1Xbx2").
Lemma m_run9pb_eq : ltac2:(tb__ "0|0|
S13SaS14A1S98S1U2A1S0Z4A3SedA3"). Proof. cbv delta [run9pb m_run9pb]; cbv beta zeta. MallocMemoSPW2_all81. reflexivity. Qed.
Ltac MallocMemoSPW2_sub82 t := let t := MallocMemoSPW2_sub81 t in lazymatch (eval pattern (run9pb (Wcan 2) UStopLe 4) in t) with ?P _ => eval cbv beta in (P m_run9pb) end.
Ltac MallocMemoSPW2_all82 := MallocMemoSPW2_all81; MemoFast.memo_rw m_run9pb_eq.

Ltac MallocMemoSPW2_subst t := MallocMemoSPW2_sub82 t.
Ltac MallocMemoSPW2_all := MallocMemoSPW2_all82.
End MallocMemoSPW2.

