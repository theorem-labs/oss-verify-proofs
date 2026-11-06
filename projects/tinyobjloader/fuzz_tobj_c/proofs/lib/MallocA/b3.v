(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4 b0 RefillModelP RefillBits b9 CRefillJ.
From Stdlib Require Permutation.

(* [comment removed for export] *)
Module CInvEnsure.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "of_nat"; "div"; "modulo"; "ge"; "sub"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kPtrArrayCommit"; "kPtrArrayReserve"; "IMG_HI"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "Sh"; "FS_total"; "IMG_LO"; "PG"; "kSpaceSize"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "aa_geom"; "AA"; "ag_pab"; "aa_ptr_committed"; "aa_sec"; "ageom"; "sec_chunk"; "topG"; "aa_cls"; "aa_live"; "ag_ctx"; "ag_dtls"; "ag_fsb"; "ag_spacebeg"; "ag_thread"; "ag_top"; "budget_bound"; "class_state"; "cs_empty"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "list"; "prod"; "length"; "pair"; "bool"; "option"; "false"; "true"; "Some"; "cons"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "maps_subtract"; "Model"; "alloc_top"; "m_vm_lazy"; "vm_noaccess"; "vm_limit"; "vm_maps"; "vm_reserved"; "iv_subtract"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "secondary_repr"; "AInvA"; "SEC_INST"; "inv3"; "geom_ok"; "primary_repr"; "live_sep"; "nthZ"; "q_foot"; "quarantine_repr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "view"; "cell_ok"; "mkACell"; "present"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "ivs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.CInvEnsure"; "zens"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump"; "bumpP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM"; "cls_foot"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymSummary SymFrame Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra LedgerA Virt StepA SoundA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4 RebuildM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.RebuildN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.CSecOKInv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.CSecBump OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.SegD_cost.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition zens (G : ageom) (A : AA) (z : Z) : Prop := ltac2:(tb__ "0|1|
ScSaS0S1S47Z30A2Vz;A2S2Vz;S1S47Z38A2A2A2SaS0S1S1cVG;A1S1dVA;A1A2M0Vz;A2S2Vz;S1G0SfA2A2A2A2").

Section Foot.
Let pabZ (G : ageom) (z : Z) : Prop := ltac2:(tb__ "0|1|
SaS0S1cVG;A1M0Vz;A2S2Vz;S1G0S10A2A2A2").

Lemma pab_facts : ltac2:(tb__ "0|3|
S4fS1bS45R2R1A2S1aR2A1S1fSaS0S11S1cR1A1M0A2SaS0S1G0S10A2M1S21R1A1A2SaScS0G1S13A2S0S12G0A2A2SaSaS0S3Z8S4S31S20S1eR3A1A2A1A2S1dR3A1M2A2S0G2S10A2A2SbS9S6G2SfA2Z0A3A2A2A2A2TG;F_;FA;Fm;").
Proof.
  intros m A HSR G. destruct HSR as (_ & _ & S2 & S3 & S45 & _). fold G in S45.
  pose proof (dyn_ok_big _ _ _ S45 ltac:(unfold kPtrArrayReserve; lia)) as B. destruct S45 as [_ (D1 & D2 & D3 & D4 & D5)].
  repeat split; try assumption; lia.
Qed.

Lemma sh_run_band : ltac2:(tb__ "0|2|
S9S9S9S0Z0R3A2M0G0S0S1R5R4A2Z7fffff800000A2SaS0S14R6A1M1R4A2S2R4S1G1S5S1R5Z7A2Z8A2A2A2A2SaS0S13R5A2S2R5S12A2A2F_;F_;F_;F_;Fy;Flen;Fb;").
Proof.
  intros b len y Hb Hl Htop Hy. unfold Sh, SHADOW_OFF, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  pose proof (Z.div_le_mono (b + len + 7) (140737479966720 + 7) 8 ltac:(lia) ltac:(lia)) as D1. cbn in D1.
  pose proof (Z.div_pos b 8 Hb ltac:(lia)) as D3.
  pose proof (Z.div_mod b 8 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound b 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (len + 7) 8 ltac:(lia)) as E2. pose proof (Z.mod_pos_bound (len + 7) 8 ltac:(lia)) as M2.
  pose proof (Z.div_mod (b + len + 7) 8 ltac:(lia)) as E3. pose proof (Z.mod_pos_bound (b + len + 7) 8 ltac:(lia)) as M3.
  lia.
Qed.
Lemma sh_run_band2 : ltac2:(tb__ "0|0|
S9S9S9S0Z0R3A2SaS0R4R3A2S0R3Z7fffff800000A2A2SaS0S14R5A1R3A2S2R3S14R4A1A2A2SaS0S13R4A2S2R4S12A2A2F_;F_;F_;Fy;Fe;Fb;").
Proof.
  intros b e y Hb He Hy. unfold Sh, SHADOW_OFF, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  pose proof (Z.div_le_mono e 140737479966720 8 ltac:(lia) ltac:(lia)) as D1. cbn in D1.
  pose proof (Z.div_pos b 8 Hb ltac:(lia)) as D3. lia.
Qed.

Lemma live_foot_pab : ltac2:(tb__ "0|1|
S4fS1bS49S1aR1A1A1S4bR2A1S48R3A1S4aR5R4A2S45R6R5A2S9S9S9S56S30S9S9A2S32S9S9R3R2A4S23R9A1A3ScSaS0S8R4S19R3A1A2R2A2S2R2S1R4R3A2A2A2SaS0S14R4A1M0R2A2S2R2S1G0S5S1R3Z7A2Z8A2A2A2A2A2SdVpabZ;S1aRbA1R3A2A1F_;F_;Fz;Fn;Fb;F_;F_;F_;F_;F_;FA;Fm;").
Proof.
  intros m A HG Hsep HI3 HPR HSR b n z Hin Hz. unfold pabZ.
  pose proof (pab_facts m A HSR) as (P1 & P2 & P3 & _).
  pose proof (topG_range (aa_geom A)) as ACV.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *.
  destruct (Hsep b n Hin) as (L1 & L2 & L3 & _). unfold IMG_HI in L2. fold G in L3.
  pose proof (rz_bound n) as RZB.
  destruct HI3 as (SG3 & LIV3 & SEC3 & _). fold G in SG3, SEC3.
  destruct SG3 as (_ & _ & _ & PS & _). fold SB in PS. rewrite kSpaceSize_val in PS.
  destruct Hz as [Hz|Hz].
  2: { pose proof (sh_run_band b n z ltac:(clear -L2; lia) ltac:(clear -L1; lia) ltac:(clear -L3 ACV; lia) Hz) as BY. clear -BY P3. intros X. lia. }
  destruct (LIV3 b n Hin) as [PRM | (ch & Hch & Eb & Esz)].
  - assert (Hn : 1 <= n <= 64512).
    { split; [exact L1|]. destruct (Z_le_dec n 64512) as [Hle|Hgt]; [clear -Hle; lia|]. rewrite (not_primary_large n) in PRM by (clear -Hgt; lia). discriminate. }
    pose proof (cls_needed n Hn) as [CNo _]. pose proof (cls_facts n Hn) as (D1 & D2 & D3 & D4). pose proof (rz_facts n Hn) as (Y1 & Y2 & Y3).
    rewrite <- CNo in D1, D2, D3, Y3. set (c := ClassID (needed n)) in D1, D2, D3, Y3.
    destruct HPR as (_ & _ & _ & PC). pose proof (PC c D1) as PC'. fold G in PC'. unfold class_repr in PC'.
    destruct PC' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV & _ & _).
    destruct (LV b n Hin PRM eq_refl) as (V1 & V2 & V3). fold SB in V1, V2, V3.
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in M3.
    assert (ERB : region_beg SB c = SB + c * 2 ^ 32) by reflexivity. rewrite ERB in V1, V3.
    assert (BLO : SB <= b - rz n /\ b + n <= SB + 2 ^ 37) by (clear -V1 V3 M2 M3 D1 Y1 Y3 Hn; nia).
    clear -Hz BLO PS RZB. intros X. lia.
  - destruct (In_nth_error _ _ Hch) as [i Hi].
    destruct HSR as (SC1 & _). destruct (SC1 i ch Hi) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). unfold PG in D6, D8, D11, Eb.
    pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU1. pose proof (round_up_ge (sc_size ch) 4096 ltac:(clear; lia)) as RU2.
    destruct (SEC3 i ch Hi) as (_ & _ & SP & _). fold G in SP.
    assert (INM : sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch) by (clear -Hz Eb Esz RZB D8 D11 RU1 RU2 L1; lia).
    clear -INM SP. intros X. lia.
Qed.

Lemma q_foot_pab : ltac2:(tb__ "0|0|
S4fS1bS49S1aR1A1A1S48R2A1S4aR4R3A2S45R5R4A2S4eR6R5A2S9S4dR7R1A2SdVpabZ;S1aR8A1R2A2A1F_;Fz;F_;F_;F_;F_;F_;FA;Fm;").
Proof.
  intros m A HG HI3 HPR HSR (Q1 & _) z Hq. unfold pabZ.
  pose proof (pab_facts m A HSR) as (P1 & P2 & P3 & _).
  pose proof (topG_range (aa_geom A)) as ACV.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *.
  destruct HI3 as (SG3 & LIV3 & SEC3 & _). fold G in SG3, SEC3.
  destruct SG3 as (_ & _ & _ & PS & _). fold SB in PS. rewrite kSpaceSize_val in PS.
  destruct HPR as (_ & _ & _ & PC).
  assert (REG : forall c, 1 <= c <= 30 -> SB <= region_beg SB c /\ region_beg SB c + cs_allocated_user (nthZ (aa_cls A) c cs_empty) <= SB + 2 ^ 37).
  { intros c Hc. pose proof (PC c Hc) as X. fold G SB in X. unfold class_repr in X.
    destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _).
    unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize in *. unfold region_beg, kRegionSize. clear -Hc M1 M2 M3. nia. }
  assert (GSB : 17594333495296 <= SB /\ SB + 2 ^ 37 + 4096 <= topG G).
  { pose proof (geom_old _ HG) as X. rewrite kSpaceSize_val in X. unfold HIGH_SHADOW_END in X. fold G SB in X. clear -X. tauto. }
  unfold q_foot in Hq. apply Exists_exists in Hq as (qb & Hqb & Hz).
  pose proof (proj1 (Forall_forall _ _) Q1 qb Hqb) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7). fold G SB in B7.
  destruct Hz as [Hz|Hz].
  { destruct B7 as (x & Ex & X0 & _ & XA). destruct (REG 24 ltac:(lia)) as [R1 R2]. unfold kQuarantineBatchSize in *. clear -Hz Ex X0 XA R1 R2 PS. intros X. lia. }
  apply Exists_exists in Hz as (it & Hit & Hz). destruct (In_nth_error _ _ Hit) as [i Hi]. destruct (B6 i it Hi) as [_ IT].
  destruct IT as (J1 & J2 & _ & _ & _ & _ & _ & _ & JP & JS & _). unfold IMG_HI in J1. fold G SB in JP.
  pose proof (rz_bound (snd it)) as RZ. set (u := fst it) in *. set (n := snd it) in *.
  destruct Hz as [Hz|Hz].
  2: {
       assert (UT : u + n <= 140737479966720).
       { destruct (is_primary n) eqn:PRM.
         - assert (Hn : 1 <= n <= 64512).
           { split; [exact J2|]. destruct (Z_le_dec n 64512) as [Hle|Hgt]; [clear -Hle; lia|]. rewrite (not_primary_large n) in PRM by (clear -Hgt; lia). discriminate. }
           pose proof (cls_needed n Hn) as [CNo _]. pose proof (cls_facts n Hn) as (D1 & D2 & D3 & D4). pose proof (rz_facts n Hn) as (Y1 & Y2 & Y3).
           rewrite <- CNo in D1, D2, D3, Y3. destruct (JP eq_refl) as (V1 & V2 & V3). fold n in V1, V2, V3.
           set (c := ClassID (needed n)) in *. destruct (REG c D1) as [R1 R2]. clear -V1 V3 R1 R2 GSB ACV Y1 Y3 Hn. nia.
         - destruct (JS eq_refl) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [j Hj].
           destruct HSR as (SC1 & _). destruct (SC1 j ch Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). fold G in D12. unfold PG in *.
           pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU1. pose proof (round_up_ge (sc_size ch) 4096 ltac:(clear; lia)) as RU2.
           clear -Eu Esz D8 D11 D12 RU1 RU2 ACV J2. lia. }
       pose proof (sh_run_band u n z ltac:(clear -J1; lia) ltac:(clear -J2; lia) UT Hz) as BY. clear -BY P3. intros X. lia. }
  destruct (is_primary n) eqn:PRM.
  - assert (Hn : 1 <= n <= 64512).
    { split; [exact J2|]. destruct (Z_le_dec n 64512) as [Hle|Hgt]; [clear -Hle; lia|]. rewrite (not_primary_large n) in PRM by (clear -Hgt; lia). discriminate. }
    pose proof (cls_needed n Hn) as [CNo _]. pose proof (cls_facts n Hn) as (D1 & D2 & D3 & D4). pose proof (rz_facts n Hn) as (Y1 & Y2 & Y3).
    rewrite <- CNo in D1, D2, D3, Y3. destruct (JP eq_refl) as (V1 & V2 & V3). fold n in V1, V2, V3.
    set (c := ClassID (needed n)) in *. destruct (REG c D1) as [R1 R2]. clear -Hz V1 V3 R1 R2 PS Y1 Y3 Hn RZ. intros X. nia.
  - destruct (JS eq_refl) as (ch & Hch & Eu & Esz). destruct (In_nth_error _ _ Hch) as [j Hj].
    destruct HSR as (SC1 & _). destruct (SC1 j ch Hj) as (_ & _ & _ & _ & _ & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _). unfold PG in *.
    destruct (SEC3 j ch Hj) as (_ & _ & SP & _). fold G in SP.
    pose proof (round_up_ge n 8 ltac:(clear; lia)) as RU1. pose proof (round_up_ge (sc_size ch) 4096 ltac:(clear; lia)) as RU2.
    assert (INM : sc_map_beg ch <= z < sc_map_beg ch + sc_map_size ch) by (clear -Hz Eu Esz RZ D8 D11 RU1 RU2 J2; lia).
    clear -INM SP. intros X. lia.
Qed.

Lemma cls_foot_pab : ltac2:(tb__ "0|0|
S4fS1bS9S49S1aR2A1A1S48R3A1S4aR5R4A2S45R6R5A2SaS0Z1R5A2S0R5Z1eA2A2S9S5eS1aR8A1R7S4cS2bS22R8A1R7S2cA4R1A4SdVpabZ;S1aR9A1R2A2A1F_;Fz;F_;F_;F_;F_;F_;Fc;FA;Fm;").
Proof.
  intros m A c HG HI3 HPR HSR Hc z Hz. unfold pabZ.
  pose proof (pab_facts m A HSR) as (P1 & P2 & P3 & _).
  pose proof (topG_range (aa_geom A)) as ACV.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *. set (T := ag_thread G) in *.
  destruct HI3 as (SG3 & _). fold G in SG3. destruct SG3 as (_ & _ & _ & PS & PT & _). fold SB in PS. fold T in PT. rewrite kSpaceSize_val in PS.
  destruct HPR as (_ & _ & _ & PC). pose proof (PC c Hc) as X. fold G in X. unfold class_repr in X.
  destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M1 & M2 & M3 & _ & M5 & M6 & _).
  pose proof (geom_old _ HG) as Y. rewrite kSpaceSize_val in Y. unfold HIGH_SHADOW_END in Y. fold G SB in Y.
  destruct Y as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GS1 & GS2 & _).
  unfold cls_foot in Hz. cbn zeta in Hz. fold G T SB in Hz. unfold region_info, free_array, region_beg in Hz.
  unfold kUserSpaceSize, kUserMapSize, kRegionSize, kFreeArraySize, kRegionInfoStride, kSpaceSize in *.
  destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]].
  - clear -Hz Hc PS. intros X. lia.
  - clear -Hz Hc PS M5 M6. intros X. nia.
  - clear -Hz Hc PS M1 M2 M3. intros X. nia.
  - assert (BY : SHADOW_BAND_LO <= z < SHADOW_BAND_HI).
    { apply (sh_run_band2 (SB + c * 2 ^ 32) (SB + c * 2 ^ 32 + cs_mapped_user (nthZ (aa_cls A) c cs_empty)) z); [clear -Hc GS1; nia | clear -Hc M1 M2 M3 GS2 ACV; nia | exact Hz]. }
    clear -BY P3. intros X. lia.
  - clear -Hz Hc PT. intros X. lia.
Qed.
End Foot.

Lemma iv_subtract_apartE : ltac2:(tb__ "0|4|
S2dQ40M0A1M1G1S9S9S2R2R1A2S2Z0S2eG0R4A2A2ScS0S1S2eG0R6A2M2S2eG0R5A2A2R4A2S0R3G2A2A2SbS2fS30G1G1A2M3A1S44R7R6R5R4A4S38G3S32G1G1R7R6A4S39G3A1A3A3F_;F_;F_;Fhi;Flo;Fsz;Fa;").
Proof.
  intros a sz lo hi Hlh Hs Hd. unfold iv_subtract. cbv zeta. destruct Hd as [Hd|Hd].
  - rewrite (proj2 (Z.ltb_lt (bv_unsigned a) lo)) by lia. rewrite (proj2 (Z.ltb_ge hi (bv_unsigned a + bv_unsigned sz))) by lia.
    cbn [app]. rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned a) lo)) by lia. rewrite (proj2 (Z.ltb_lt hi (bv_unsigned a + bv_unsigned sz))) by lia.
    cbn [app]. rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma in_maps_subtract_apart : ltac2:(tb__ "0|4|
S2fS30S2dQ40M0A1M1G1A2M2A1G1G1S9S9S2R2R1A2S2Z0S2eG0R4A2A2ScS0S1S2eG0R6A2M3S2eG0R5A2A2R4A2S0R3G3A2A2S56G2S32G1G1R7R6A4R8A3S56G2S32G1G1R8R7A4S3cR9R6R5A3A3F_;F_;F_;F_;Fhi;Flo;Fsz;Fa;Fl;").
Proof.
  induction l as [|[a' s'] l IH]; intros a sz lo hi Hlh Hs Hd Hin; [destruct Hin|].
  cbn [maps_subtract]. apply in_app_iff. destruct Hin as [E|Hin].
  - left. injection E as -> ->. rewrite (iv_subtract_apartE a sz lo hi Hlh Hs Hd). left. reflexivity.
  - right. exact (IH _ _ _ _ Hlh Hs Hd Hin).
Qed.

Lemma maps_subtract_pos : ltac2:(tb__ "0|5|
S2fS30S2dQ40M0A1M1G1A2M2A1S9S9G1G1S56G2S32G1G1R2R1A4M3R5A3S2Z0S2eG0R2A2A2M4F_;Fs;Fb;G1G1S56G2G3S3cR6R5R4A3A3G4F_;Fs;Fb;F_;Fhi;Flo;Fl;").
Proof.
  intros l lo hi H. induction l as [|[a sz] l IH]; [intros b s []|]. cbn [maps_subtract]. intros b s Hin.
  apply in_app_or in Hin as [Hin|Hin]; [|exact (IH (fun b' s' Hi => H b' s' (or_intror Hi)) b s Hin)].
  pose proof (H a sz (or_introl eq_refl)) as Hsz. pose proof (urange a) as Ra. pose proof (urange sz) as Rs.
  unfold iv_subtract in Hin. apply in_app_or in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [Hin|[]]. injection Hin as <- <-.
    rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [Hin|[]]. injection Hin as <- <-.
    rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.

Lemma covered_subtract_false : ltac2:(tb__ "0|1|
S2fS30S2dQ40A1M0G0A2A1S9S9S9S58R4A1S0R4R3A2SbS33S57R6R3A2S35A3SbS33S57S3cR7R6R5A3R4A2S35A3F_;F_;F_;Fx;Fhi;Flo;Fl;").
Proof.
  intros l lo hi x Hwf Hlh H. destruct (maps_subtract_sem l lo hi Hwf Hlh) as (_ & _ & C). rewrite C, H. reflexivity.
Qed.
Lemma covered_subtract_true : ltac2:(tb__ "0|1|
S2fS30S2dQ40A1M0G0A2A1S9S9S9S58R4A1S0R4R3A2SbS33S57S3cR6R5R4A3R3A2S36A3SbS33S57R7R4A2S36A3F_;F_;F_;Fx;Fhi;Flo;Fl;").
Proof.
  intros l lo hi x Hwf Hlh H. destruct (maps_subtract_sem l lo hi Hwf Hlh) as (_ & _ & C). rewrite C in H.
  destruct (covered l x); [reflexivity | discriminate H].
Qed.

Lemma secondary_repr_ensure : ltac2:(tb__ "0|1|
S4fS4fS1bS1aR1A1S1fS1dR2A1S9S9SdS5bR3R4R1A3A1ScS0S11R2A2SaS0S16R2A2S2R2S11A2A2A2SbS34S2dQ8A1A1R7R3A1R8R3A1A3F_;F_;Fz;S0S1R2SfA2S10A2S51R6S52S1S47Z30A2U8S5S1R3SfA2Z8A2A3A2S53R7S1S1cR5A1R4A2M0S1G0SfA2A3S48R7A1S45RaR8A2S45RaS5cR9A1A2F_;F_;F_;F_;F_;F_;Tc;TG;FA;Fm';Fm;").
Proof.
  intros m m' A. cbn zeta. intros AG HcR HC48 HPB HI3 HSR.
  pose proof (pab_facts m A HSR) as (P1 & P2 & P3 & P4 & P5).
  destruct HSR as (S1 & SP & S2 & S3 & S45 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
  destruct HI3 as (_ & _ & SEC3 & _).
  unfold secondary_repr. cbn [aa_geom aa_sec aa_ptr_committed bumpP].
  set (G := aa_geom A) in *. set (c := aa_ptr_committed A) in *.
  pose proof (topG_range G) as ACV.
  assert (AGI : forall z, IMG_LO <= z < IMG_HI -> ~ (SEC_INST + 48 <= z < SEC_INST + 56) -> m' z = m z).
  { intros z H1 H2. apply AG; [|right; exact H1]. intros [X|X]; [exact (H2 X)|]. unfold IMG_HI in *. clear -H1 X P1 P4. lia. }
  assert (AGH : forall z, IMG_HI <= z -> ~ (ag_pab G + c <= z < ag_pab G + c + kPtrArrayCommit) -> m' z = m z).
  { intros z H1 H2. apply AG; [|left; exact H1]. intros [X|X]; [|exact (H2 X)]. unfold IMG_HI, SEC_INST in *. clear -H1 X. lia. }
  split.
  { intros i ch Hi. destruct (S1 i ch Hi) as (C1 & C2 & C3 & C4 & C5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
    pose proof (nth_error_Some_lt _ _ _ Hi) as L. fold G in D10, D12.
    assert (MS : 0 <= sc_map_size ch) by (unfold PG in D8; lia).
    pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in D8; clear -D8 D9; lia)) as MB.
    destruct (SEC3 i ch Hi) as (_ & _ & SPB & _).
    assert (CA : forall off w v, 0 <= off -> off + Z.of_nat w <= 32 -> cell_ok m (mkACell (sc_map_beg ch + off) w v) -> cell_ok m' (mkACell (sc_map_beg ch + off) w v)).
    { intros off w v Ho Hw. apply cell_ok_agree. cbn [c_addr c_w]. intros k Hk. apply AGH; [clear -MB Ho; lia|]. unfold PG in D8. clear -SPB D8 D9 Ho Hw Hk P4 HcR. intros X. lia. }
    split; [apply CA; [lia| cbn; lia | exact C1]|]. split; [apply CA; [lia| cbn; lia | exact C2]|].
    split; [apply CA; [lia| cbn; lia | exact C3]|]. split; [apply CA; [lia| cbn; lia | exact C4]|].
    split; [eapply cell_ok_agree; [|exact C5]; cbn [c_addr c_w]; intros k Hk; apply AGH; [clear -P1 Hk; lia | clear -L P4 Hk; intros X; lia]|].
    split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
    split; [eapply present_but_agree; [|exact D13]; intros z Hz _; apply AGH; [clear -MB Hz; lia | clear -SPB Hz P4 HcR MS; intros X; lia]|].
    eapply present_agree; [|exact D14]. intros z Hz.
    pose proof (sh_run_band2 (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) z ltac:(clear -MB; unfold IMG_HI in MB; lia) ltac:(clear -MS D12 ACV; lia) Hz) as BY.
    apply AGH; [clear -BY; unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, IMG_HI in *; lia | clear -BY P3 P4 HcR; intros X; lia]. }
  split.
  {
    intros z Hz. destruct (Z_lt_dec z (ag_pab G + c)) as [Hlt|Hge].
    - rewrite AGH; [apply SP; lia | pose proof (Zle_0_nat (length (aa_sec A))); clear -Hz Hlt P1 H; lia | clear -Hlt; intros X; lia].
    - apply HPB. lia. }
  split; [clear -S2 HcR; unfold kPtrArrayCommit in *; lia|].
  split. { rewrite <- Z.add_mod_idemp_l by (unfold kPtrArrayCommit; lia). rewrite S3, Z.add_0_l. apply Z_mod_same_full. }
  split; [exact S45|].
  assert (CI : forall cc, (SEC_INST <= c_addr cc /\ c_addr cc + Z.of_nat (c_w cc) <= SEC_INST + 48) \/ (SEC_INST + 56 <= c_addr cc /\ c_addr cc + Z.of_nat (c_w cc) <= 0xee048) ->
               cell_ok m cc -> cell_ok m' cc).
  { intros cc H1. apply cell_ok_agree. intros k Hk. apply AGI; unfold SEC_INST, IMG_LO, IMG_HI in *; clear -H1 Hk; lia. }
  unfold SEC_INST in *.
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I1]|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I2]|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I3]|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I4]|].
  split; [exact HC48|].
  split; [apply CI; [cbn [c_addr c_w Z.of_nat]; lia | exact I6]|].
  split; [eapply present_agree; [|exact I7]; intros z Hz; apply AGI; unfold IMG_LO, IMG_HI; clear -Hz; lia|].
  split; [eapply cell_ok_agree; [|exact I8]; cbn [c_addr c_w]; intros k Hk; apply AGI; unfold IMG_LO, IMG_HI; clear -Hk; lia|].
  eapply present_agree; [|exact I9]; intros z Hz; apply AGI; unfold IMG_LO, IMG_HI; clear -Hz; lia.
Qed.

Theorem AInvA_ensure : ltac2:(tb__ "0|8|
S1bS54S54S2fS2dQ40A1M0A1S3dS3dS1aR6A1S1fS1dR7A1S9S1S1cR2A1R1A2S9S46S3aR9R8R6R5A5SbS9S3Z8M1S4S31S20S1eRaA1A2A1A2R3A3S0S1R4SfA2S10A2SbS2fS30G0G0A2A1M2S42S3bR7A1A1S42S3bR8A1M3A1A3SbG2S43G3A1S43S3bR9A1M4A1A3SbG2S40G4A1S3cS40S3bRaA1A1R6S1R6SfA2A3A3SbG2S3fRaA1S3cS3fRbA1R7S1R7SfA2A3A3SbS9S41S3bRbA1A1S41S3bRcA1M5A1A3SbS9S3eG5A1S3eS3bRdA1A1A3S58S40S3bReA1A1A1S58S3fRfA1A1S0S59RfR11A2S1S59R10R11A2SfA2A2S9SdS5bR10R16R1A3A1SbS34S2dQ8A1A1S50S3aS55R15A1M6R2A3S50S3aS55R16A1R2A3A3F_;Fz;S51S50S3aS55R14A1A2S52S1S47Z30A2U8S5S1RfSfA2M7G1A2A3A2S53S50S3aG6A2RfG7A3S46S3aS5cR18A1R16R15R13A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;TPB;Tc;TG;Fmd';Fmd;Ftp;Frho3;FrhoE;FA;").
Proof.
  intros A rhoE rho3 tp md md'. cbn zeta. intros HA HcN HcR EM ER EN EL ELIM ETOP WN WL HPAID VO HC48 HPB.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HB).
  destruct HRest as (Hsep & Hlive & HPR & HSR & HQR & HDW & HIA & HTH & HMI).
  pose proof (pab_facts _ A HSR) as (P1 & P2 & P3 & P4 & P5).
  pose proof HI3 as (SG3 & LIV3 & SEC3 & Q3 & DEP3 & ND3).
  pose proof SG3 as (_ & _ & _ & PS & PT & PF & PC & PD).
  set (G := aa_geom A) in *. set (c := aa_ptr_committed A) in *. set (PB := ag_pab G + c) in *. set (T := ag_thread G) in *.
  set (vE := view segsA (rm rhoE)) in *. set (v3 := view segsA (rm rho3)) in *.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & ACV). fold T in G4, G5, G10, G13, G14.
  pose proof (geom_bands _ HG) as (_ & TB & _ & _ & TI & CI & DI). fold T in TB, TI. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in TB, TI, CI, DI.
  assert (ZD : forall z, zens G A z \/ ~ zens G A z) by (intros z; unfold zens; clear; lia).

  assert (AGI : forall z, z < IMG_HI -> ~ (SEC_INST + 48 <= z < SEC_INST + 56) -> v3 z = vE z).
  { intros z H1 H2. apply VO. intros [X|X]; [exact (H2 X)|]. fold c in X. unfold IMG_HI in *. clear -H1 X P1 P4. lia. }
  assert (AGH : forall z, IMG_HI <= z -> ~ (PB <= z < PB + kPtrArrayCommit) -> v3 z = vE z).
  { intros z H1 H2. apply VO. intros [X|X]; [|exact (H2 X)]. unfold IMG_HI, SEC_INST in *. clear -H1 X. lia. }
  assert (AGP : forall z, IMG_HI <= z -> ~ (ag_pab G <= z < ag_pab G + kPtrArrayReserve) -> v3 z = vE z).
  { intros z H1 H2. apply AGH; [exact H1|]. unfold PB. clear -H2 P4 HcR. intros X. lia. }
  assert (AGZ : forall z, ~ (SEC_INST + 48 <= z < SEC_INST + 56) -> ~ (ag_pab G <= z < ag_pab G + kPtrArrayReserve) -> v3 z = vE z).
  { intros z H1 H2. apply VO. intros [X|X]; [exact (H1 X)|]. apply H2. unfold PB in X. clear -X P4 HcR. lia. }

  assert (HRTC : rtc_inv v3 G).
  { unfold rtc_inv. eapply cells_ok_frame; [|exact HR]. intros z Hz.
    unfold cells_footb in Hz. apply existsb_exists in Hz as (cc & Hc & Hin).
    unfold in_cellb in Hin. apply andb_prop in Hin as [X Y]. apply Z.leb_le in X. apply Z.ltb_lt in Y.
    unfold rtc_cells in Hc. apply in_app_or in Hc as [Hc|Hc].
    - unfold rtc_cells_img in Hc. apply AGI; unfold IMG_HI, SEC_INST;
      repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; clear -X Y; lia|]); destruct Hc.
    - unfold rtc_cells_geom in Hc. unfold fs_log_cell, fs_needs_gc_cell in Hc. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *.
      apply AGZ; unfold SEC_INST;
      repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in X, Y; cbn in Y; fold G T in X, Y;
        first [ clear -X Y TI PT; lia | clear -X Y CI PC; lia | clear -X Y DI PD; lia | clear -X Y G2 PF; lia ] |]); destruct Hc. }

  assert (HFS : fs_inv (restrictv (fs_footb G) v3) (bumpP A)).
  { rewrite (restrictv_ext (fs_footb G) vE v3).
    2: { intros z Hz. apply VO. intros Zz. unfold zens in Zz. fold G c in Zz.
         destruct Zz as [Zz|Zz].
         - rewrite (fs_footb_img G z HG) in Hz; [discriminate|]. unfold SEC_INST in Zz. clear -Zz. lia.
         - rewrite (fs_footb_false_intro G z) in Hz; [discriminate| | |].
           + clear -Zz PF P4 HcR. rewrite FS_total_val in *. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia.
           + clear -Zz PF P4 HcR. rewrite FS_total_val, FS_kFlagsOffset_val in *. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia.
           + pose proof (sh_run_band2 (ag_fsb G + FS_frames_off) (ag_fsb G + FS_total)) as BY.
             rewrite FS_frames_off_val, FS_total_val in *.
             destruct (Z_lt_dec z (Sh (ag_fsb G + 36864))) as [L|L]; [left; exact L|right].
             destruct (Z_le_dec (Sh (ag_fsb G + 11571200)) z) as [R|R]; [exact R|exfalso].
             specialize (BY z ltac:(clear -G2; lia) ltac:(clear -G3 ACV; lia) ltac:(clear -L R; lia)).
             clear -BY Zz P3 P4 HcR. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia. }
    exact HF. }

  set (mE := maskv (fs_footb G) vE) in *. set (m3 := maskv (fs_footb G) v3).
  assert (AGm : forall z, ~ zens G A z -> m3 z = mE z).
  { intros z Hz. unfold m3, mE, maskv. destruct (fs_footb G z); [reflexivity|]. apply VO. exact Hz. }
  assert (AGmI : forall z, z < IMG_HI -> ~ (SEC_INST + 48 <= z < SEC_INST + 56) -> m3 z = mE z).
  { intros z H1 H2. apply AGm. intros [X|X]; [exact (H2 X)|]. fold c in X. unfold IMG_HI in *. clear -H1 X P1 P4. lia. }
  assert (AGmH : forall z, IMG_HI <= z -> ~ (PB <= z < PB + kPtrArrayCommit) -> m3 z = mE z).
  { intros z H1 H2. apply AGm. intros [X|X]; [|exact (H2 X)]. unfold IMG_HI, SEC_INST in *. clear -H1 X. lia. }
  assert (AGmP : forall z, IMG_HI <= z -> ~ (ag_pab G <= z < ag_pab G + kPtrArrayReserve) -> m3 z = mE z).
  { intros z H1 H2. apply AGmH; [exact H1|]. unfold PB. clear -H2 P4 HcR. intros X. lia. }
  assert (AGmT : forall z, T <= z < T + 0x1000 -> m3 z = mE z).
  { intros z Hz. destruct (Z_lt_dec z IMG_HI) as [L|L].
    - apply AGmI; [exact L|]. unfold IMG_HI, SEC_INST in *. clear -Hz L TI. lia.
    - apply AGmP; [clear -L; lia|]. clear -Hz PT. intros X. lia. }
  assert (PRm : forall z, zens G A z -> exists b, m3 z = Some b).
  { intros z Hz. unfold m3.
    assert (FZ : fs_footb G z = false).
    { unfold zens in Hz. fold G c in Hz. destruct Hz as [Zz|Zz].
      - apply (fs_footb_img G z HG). unfold SEC_INST in Zz. clear -Zz. lia.
      - apply (fs_footb_false_intro G z).
        + clear -Zz PF P4 HcR. rewrite FS_total_val in *. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia.
        + clear -Zz PF P4 HcR. rewrite FS_total_val, FS_kFlagsOffset_val in *. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia.
        + pose proof (sh_run_band2 (ag_fsb G + FS_frames_off) (ag_fsb G + FS_total)) as BY.
          rewrite FS_frames_off_val, FS_total_val in *.
          destruct (Z_lt_dec z (Sh (ag_fsb G + 36864))) as [L|L]; [left; exact L|right].
          destruct (Z_le_dec (Sh (ag_fsb G + 11571200)) z) as [R|R]; [exact R|exfalso].
          specialize (BY z ltac:(clear -G2; lia) ltac:(clear -G3 ACV; lia) ltac:(clear -L R; lia)).
          clear -BY Zz P3 P4 HcR. unfold kPtrArrayReserve, kPtrArrayCommit in *. lia. }
    rewrite maskv_out by exact FZ.
    unfold zens in Hz. fold G c in Hz. destruct Hz as [Zz|Zz].
    - pose proof (HC48 (Z.to_nat (z - (SEC_INST + 48))) ltac:(cbn [c_w]; clear -Zz; lia)) as X. cbn [c_addr] in X.
      rewrite Z2Nat.id in X by (clear -Zz; lia). replace (SEC_INST + 48 + (z - (SEC_INST + 48))) with z in X by lia.
      eexists. exact X.
    - exact (HPB z Zz). }
  assert (PRESX : forall lo hi, present mE lo hi -> present m3 lo hi).
  { intros lo hi Hp z Hz. destruct (ZD z) as [Hc|Hn].
    - exact (PRm z Hc).
    - rewrite (AGm z Hn). exact (Hp z Hz). }
  assert (HLB : live_block_repr m3 (bumpP A)).
  { intros b n Hin. change (aa_live (bumpP A)) with (aa_live A) in Hin.
    destruct (Hlive b n Hin) as (B1 & B2 & B3 & [B4 B5] & B6 & B7).
    assert (NO : forall z, (b - rz n <= z < b + n \/ Sh b <= z < Sh b + (n + 7) / 8) -> m3 z = mE z).
    { intros z Hz. destruct (live_foot mE A HG Hsep HI3 HPR HSR b n z Hin Hz) as (X & _ & _).
      pose proof (live_foot_pab mE A HG Hsep HI3 HPR HSR b n z Hin Hz) as Y. fold G in Y. apply AGmP; [exact X | exact Y]. }
    pose proof (rz_bound n) as RZ. destruct (Hsep b n Hin) as (L1 & _).
    pose proof (Z.div_le_mono n (n + 7) 8 ltac:(clear; lia) ltac:(clear; lia)) as DL. pose proof (Z.div_pos n 8 ltac:(clear -L1; lia) ltac:(clear; lia)) as DP.
    split; [rewrite NO by (left; clear -RZ L1; lia); exact B1|].
    split; [eapply cell_ok_agree; [|exact B2]; cbn [c_addr c_w]; intros k Hk; apply NO; left; clear -RZ L1 Hk; lia|].
    split; [eapply cell_ok_agree; [|exact B3]; cbn [c_addr c_w]; intros k Hk; apply NO; left; clear -RZ L1 Hk; lia|].
    split; [split|split].
    + intros g Hg. rewrite NO by (right; clear -Hg DL; lia). exact (B4 g Hg).
    + intros Hm. rewrite NO; [exact (B5 Hm)|]. right.
      replace ((n + 7) / 8) with (n / 8 + 1) by (apply Z.div_unique with (n mod 8 - 1); [pose proof (Z.mod_pos_bound n 8); clear -Hm H; lia | pose proof (Z.div_mod n 8); clear -H; lia]).
      clear -DP. lia.
    + apply (alloc_magic_ok_agree mE m3); [intros z Hz; apply NO; left; clear -Hz L1; lia | clear -RZ; lia | exact B6].
    + destruct B7 as (t & Ht & Hm4). exists t. split; [rewrite NO by (left; clear -RZ L1; lia); exact Ht | exact Hm4]. }
  assert (HPR' : primary_repr m3 (bumpP A)).
  { destruct HPR as (Q1 & Q2 & Q3' & P4'). split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3'|].
    intros cl Hc. change (aa_geom (bumpP A)) with G. change (aa_cls (bumpP A)) with (aa_cls A).
    apply (class_repr_agree mE m3 G A (bumpP A) cl); [exact Hc | reflexivity | reflexivity | reflexivity | intros b n Hin _ _; exact Hin | intros z Hz; exact Hz | | exact (P4' cl Hc)].
    intros z Hz.
    pose proof (cls_foot_pab mE A cl HG HI3 (conj Q1 (conj Q2 (conj Q3' P4'))) HSR Hc z Hz) as Y. fold G in Y.

    unfold cls_foot in Hz. cbn zeta in Hz. fold G T in Hz.
    destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]].
    5: { apply AGmT. clear -Hz Hc. lia. }
    all: apply AGmP; [|exact Y].
    all: pose proof (geom_old _ HG) as X; rewrite kSpaceSize_val in X; unfold HIGH_SHADOW_END in X; fold G in X;
         destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GS1 & GS2 & _).
    all: unfold region_info, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, kSpaceSize, kRegionInfoStride, Sh, SHADOW_OFF, IMG_HI in *.
    - clear -Hz Hc GS1. lia.
    - clear -Hz Hc GS1. nia.
    - clear -Hz Hc GS1. nia.
    - pose proof (Z.div_pos (ag_spacebeg G + cl * 2 ^ 32) 8 ltac:(clear -Hc GS1; lia) ltac:(clear; lia)) as D2. clear -Hz D2. lia. }
  assert (HSR' : secondary_repr m3 (bumpP A)).
  { apply (secondary_repr_ensure mE m3 A); [| exact HcR | | | exact HI3 | exact HSR].
    - intros z Hz [H|H]; [|apply AGmI; [clear -H; unfold IMG_LO, IMG_HI in *; lia | intros X; apply Hz; left; exact X]].
      apply AGmH; [exact H | intros X; apply Hz; right; exact X].
    - intros k Hk. unfold m3. rewrite maskv_out; [exact (HC48 k Hk)|]. apply (fs_footb_img G _ HG). cbn [c_addr c_w] in *. unfold SEC_INST. clear -Hk. lia.
    - intros z Hz. apply PRm. right. exact Hz. }
  assert (HQR' : quarantine_repr m3 (bumpP A)).
  { apply (quarantine_repr_agreeQ mE m3 A (bumpP A)); try reflexivity.
    - exact (q_items_rz A).
    - intros z Hz. pose proof (q_foot_high mE A z HQR Hz) as QH. pose proof (q_foot_pab mE A HG HI3 HPR HSR HQR z Hz) as Y. fold G in Y.
      apply AGmP; [exact QH | exact Y].
    - intros z Hz. fold G T in Hz. apply AGmT. clear -Hz. lia.
    - intros z Hz. apply AGmI; unfold QG, SEC_INST, IMG_HI in *; clear -Hz; lia.
    - exact HQR. }
  assert (HIA' : ia_inv m3 (bumpP A)).
  { apply (ia_inv_agreeN mE m3 A (bumpP A)); [reflexivity | | exact HIA].
    intros z Hz. apply AGmI; unfold IA_BEG, IA_END, SEC_INST, IMG_HI in *; clear -Hz; lia. }
  assert (HTH' : thread_inv m3 G).
  { destruct HTH as [X Y]. fold T in X, Y |- *. split.
    - fold T. rewrite AGmT; [exact X | clear; lia].
    - fold T. apply PRESX. exact Y. }
  assert (HMI' : misc_inv m3).
  { apply (misc_inv_N mE m3); [| | | exact HMI].
    - intros z Hz. apply AGmI; unfold SEC_INST, IMG_HI in *; clear -Hz; lia.
    - apply PRESX. destruct HMI as (_ & X & _). exact X.
    - apply PRESX. destruct HMI as (_ & _ & X). exact X. }

  unfold AInvA. change (aa_geom (bumpP A)) with G. fold v3.
  split; [exact HG|]. split; [exact HRTC|]. split; [exact HFS|]. split.
  { unfold rest_inv. fold m3. split; [exact Hsep|]. split; [exact HLB|]. split; [exact HPR'|]. split; [exact HSR'|]. split; [exact HQR'|].
    split.
    { unfold depot_wf in HDW |- *. change (aa_depot (bumpP A)) with (aa_depot A).
      eapply depot_mem_frame; [|exact HDW]. intros a Ha.
      destruct Ha as [Hs|[(bb & Hbb & Hab)|(bb & Hbb & Hab)]].
      - unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs. apply AGmI; unfold SEC_INST, IMG_HI; clear -Hs; lia.
      - destruct (dm_nb _ _ HDW bb Hbb) as (_ & Hb1 & _).
        destruct (DEP3 (bb, NBSZ) ltac:(unfold dblocks; apply in_or_app; left; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb])) as (_ & _ & _ & _ & _ & _ & SPb & _).
        unfold sepZ in SPb. cbn [fst snd] in SPb. fold G in SPb. unfold NBSZ in *. unfold IMG_HI in Hb1; apply AGmP; unfold IMG_HI; [clear -Hb1 Hab; lia | clear -SPb Hab; intros X; lia].
      - destruct (dm_fbases _ _ HDW bb Hbb) as (_ & Hb1 & _).
        destruct (DEP3 (bb, FBSZ) ltac:(unfold dblocks; apply in_or_app; right; apply in_map_iff; exists bb; split; [reflexivity | exact Hbb])) as (_ & _ & _ & _ & _ & _ & SPb & _).
        unfold sepZ in SPb. cbn [fst snd] in SPb. fold G in SPb. unfold FBSZ in *. unfold IMG_HI in Hb1; apply AGmP; unfold IMG_HI; [clear -Hb1 Hab; lia | clear -SPb Hab; intros X; lia]. }
    split; [exact HIA'|]. split; [exact HTH' | exact HMI']. }
  split.
  {
    unfold model_inv in HM |- *. change (aa_geom (bumpP A)) with G in *. cbn [aa_V aa_Km aa_Kf bumpP].
    destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8).
    assert (KLH : PB < PB + kPtrArrayCommit) by (unfold kPtrArrayCommit; clear; lia).
    split.
    { unfold vm_geom, in_maps in V1 |- *. cbn [aa_sec aa_geom bumpP]. fold G. fold G in V1. rewrite EM, EN, EL.
      destruct V1 as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
      split.
      { intros e x He Hx.
        assert (CV : covered (vm_noaccess (m_vmmaps md)) x = true).
        { apply (covered_subtract_true _ PB (PB + kPtrArrayCommit) x WN ltac:(clear -KLH; lia)).
          unfold covered. apply existsb_exists. exists e. split; [exact He|]. unfold in_iv, in_rng, ivB, ivS. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
        unfold covered in CV. apply existsb_exists in CV as (e0 & He0 & Hx0). unfold in_iv, in_rng, ivB, ivS in Hx0. apply andb_prop in Hx0 as [X1 X2].
        apply Z.leb_le in X1. apply Z.ltb_lt in X2. exact (N1 e0 x He0 (conj X1 X2)). }
      split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|]. split; [exact N7|]. split; [exact N8|].
      intros p Hal Hband. destruct (N9 p Hal Hband) as [L1 L2]. split.
      - apply page_in_ranges_spec in L1 as (r & Hr & Hpr). apply page_in_range_spec in Hpr as [Q1 Q2]. change page_size with 4096 in Q2.
        assert (OUT : bv_unsigned p + 4096 <= PB \/ PB + kPtrArrayCommit <= bv_unsigned p).
        { unfold PB. clear -Hband P3 P4 HcR. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *. unfold LOW_SHADOW_BEG, SHADOW_GAP_BEG, HIGH_SHADOW_BEG, HIGH_SHADOW_END, PG, kPtrArrayReserve, kPtrArrayCommit in *. lia. }
        destruct (maps_subtract_keeps (m_vm_lazy md) PB (PB + kPtrArrayCommit) r (bv_unsigned p) (bv_unsigned p + 4096) WL ltac:(clear -KLH; lia) Hr Q1 Q2 ltac:(clear; lia) OUT)
          as (r' & Hr' & X1 & X2).
        apply page_in_ranges_spec. exists r'. split; [exact Hr'|]. apply page_in_range_spec. change page_size with 4096. clear -X1 X2. lia.
      - intros j Hj. apply covered_subtract_false; [exact WN | clear -KLH; lia | exact (L2 j Hj)]. }
    split; [rewrite (PrimCredit.prim_credit_same A (bumpP A) eq_refl); rewrite budget_boundD_bumpP; fold c;
            set (pcr := PrimCredit.prim_credit A) in *; clearbody pcr; clear -V2 HPAID; lia|].
    split; [rewrite ELIM; exact V3|]. split; [exact V4|]. split; [exact V5|]. split; [exact V6|]. split; [rewrite ETOP; exact V7|].

    unfold ledger_inv in V8 |- *. cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed aa_cls aa_sec bumpP] in V8 |- *.
    destruct V8 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10).
    rewrite ER, EM.
    split; [exact L1|]. split; [exact L2|]. split; [exact L3|].
    split.
    { unfold gap_ok, gapN_ok, gapS_ok, ledger in L4 |- *. cbn [aa_V aa_depot bumpP]. rewrite ER, EM. exact L4. }
    split.
    { destruct L5 as [D1 D2 D3 D4 D5 D6]. constructor.
      - intros bn Hbn. rewrite EM. exact (D1 bn Hbn).
      - intros b Hb. rewrite EL.
        destruct (DEP3 (b, FBSZ) ltac:(unfold dblocks; apply in_or_app; right; apply in_map_iff; exists b; split; [reflexivity | exact Hb])) as (DY & _ & _ & _ & _ & _ & SPb & _).
        unfold sepZ in SPb. cbn [fst snd] in SPb, DY. fold G in SPb, DY.
        pose proof (dyn_in_big _ _ _ DY ltac:(unfold FBSZ; clear; lia)) as BB. destruct DY as (_ & _ & DT & _).
        pose proof (topG_range G) as TR.
        apply in_maps_subtract_apart; [exact KLH | rewrite u64_lit; unfold FBSZ; clear; lia | | exact (D2 b Hb)].
        rewrite !u64_lit by (unfold FBSZ, IMG_HI in *; clear -BB DT TR; lia).
        unfold PB. clear -SPb P4 HcR. unfold FBSZ, kPtrArrayReserve, kPtrArrayCommit in *. lia.
      - intros b j Hb Hj. rewrite EN. apply covered_subtract_false; [exact WN | clear -KLH; lia | exact (D3 b j Hb Hj)].
      - exact D4.
      - intros bn Hbn. rewrite ETOP. exact (D5 bn Hbn).
      - rewrite ETOP. exact D6. }
    split; [exact L6|]. split; [clear -L7 L9 HcN; fold c in L7 |- *; unfold kPtrArrayCommit in *; lia|].
    split; [unfold in_maps; rewrite ?EM; exact L8|]. split; [exact L9|]. rewrite EN. apply maps_subtract_pos. exact L10. }
  split; [exact HI3|].

  eapply bandtp_agree; [|exact HB]. intros z Hz. apply VO. unfold zens. fold G c.
  unfold SEC_INST, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, kPtrArrayReserve, kPtrArrayCommit in *. clear -Hz P3 P4 HcR. intros X. lia.
Qed.

Lemma AInvA_pab : ltac2:(tb__ "0|8|
S1bS54S2fS2dQ40A1A1S3dS46S3aR4R3R2R1A5S1aR5A1S1fS1dR6A1S9SaS0S11S1cR2A1M0A2SaS0S1G0S10A2M1S21R2A1M2A2SaSbS9S6G0S17A2Z0M3A3SaScS0G1S13A2S0S12G0A2A2SaSaS0S3Z8M4S4S31S20S1eR7A1A2A1A2R1A2S0R1S10A2A2SaSbS9S6R1SfA2G3A3SaSbS9G2S29R2A1M5A3SaSbS9S3eS3bR4A1A1G5A3S9SaS0S1S1cR3A1M6S3G4S4S31S20S1eR8A1A2A1A2A2R1A2S2R1S1G6R2A2A2A2SeS2dQ8A1M7G7SbS34G7A1S50S3aS55R9A1R3A3S37G7R1A2A3Lb;A2F_;Fz;A2A2A2A2A2A2A2A2Tc;TG;F_;Fmd;Ftp;Frho;FX;").
Proof.
  intros X rho tp md HA. cbn zeta.
  pose proof HA as (HG & _ & _ & HRest & HM & _). destruct HRest as (_ & _ & _ & HSR & _).
  pose proof (pab_facts _ X HSR) as (P1 & P2 & P3 & P4 & P5).
  destruct HSR as (_ & SP & _). destruct HM as (_ & _ & _ & _ & _ & _ & TOP & _).
  pose proof (geom_top _ HG) as GT. pose proof (geom_pab _ HG) as GP.
  repeat split; try assumption; try (clear -P4; lia).
  intros z Hz. destruct (SP z Hz) as [b Hb]. exists b. rewrite <- Hb. symmetry. apply maskv_out.
  apply (fs_footb_false_intro X.(aa_geom) z); pose proof HA as (_ & _ & _ & _ & _ & HI3 & _); destruct HI3 as ((_ & _ & _ & _ & _ & PF & _) & _);
    pose proof (geom_numsS _ HG) as (_ & G2 & G3 & _); pose proof (topG_range (aa_geom X)) as TG.
  - clear -Hz PF P4. rewrite FS_total_val in PF. unfold kPtrArrayReserve in *. pose proof (Zle_0_nat (length (aa_sec X))). lia.
  - clear -Hz PF P4. rewrite FS_total_val, FS_kFlagsOffset_val in *. unfold kPtrArrayReserve in *. pose proof (Zle_0_nat (length (aa_sec X))). lia.
  - rewrite FS_frames_off_val, FS_total_val in *.
    destruct (Z_lt_dec z (Sh (ag_fsb (aa_geom X) + 36864))) as [L|L]; [left; exact L|right].
    destruct (Z_le_dec (Sh (ag_fsb (aa_geom X) + 11571200)) z) as [R|R]; [exact R|exfalso].
    pose proof (sh_run_band2 (ag_fsb (aa_geom X) + 36864) (ag_fsb (aa_geom X) + 11571200) z ltac:(clear -G2; lia) ltac:(clear -G3 TG; lia) ltac:(clear -L R; lia)) as BY.
    clear -BY Hz P3 P4. unfold kPtrArrayReserve in *. pose proof (Zle_0_nat (length (aa_sec X))). lia.
Qed.

Lemma ensure_headroom : ltac2:(tb__ "0|0|
S1bS54S2fS2dQ40A1A1S3dS46S3aR4R3R2R1A5SbS9S3Z8S4S31S20S1eR5A1A2A1A2S1dR5A1A3S0S2aR6A1S5dA2S7S5aR4R5A2SfA2F_;F_;F_;Fmd;Ftp;Frho;FX;").
Proof.
  intros X rho tp md HA HcN HB.
  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HBT).
  destruct HRest as (_ & _ & _ & _ & _ & HD & _). unfold depot_wf in HD.
  destruct HM as (_ & PB & VL & V0 & K0 & F0 & _ & _ & _ & _ & _ & _ & DN & PC & _ & L9 & _).
  pose proof (budgetD_le_budget (bumpP X) (dep_cost_bound_mem _ _ HD) (dm_F_NFBLK _ _ HD) DN) as BD.
  cbn [aa_V aa_Km aa_Kf aa_depot aa_ptr_committed bumpP] in BD.
  rewrite budget_boundD_bumpP, budget_bound_bumpP in BD.
  pose proof (PrimCredit.prim_credit_nonneg X) as PCN.
  unfold headroom. rewrite VL. unfold kPtrArrayCommit in *. set (pcr := PrimCredit.prim_credit X) in *. clearbody pcr. clear -PB BD HB HcN L9 PC K0 F0 PCN. lia.
Qed.

Lemma AInvA_pabsep : ltac2:(tb__ "0|8|
S1bS54S2fS2dQ40A1A1S3dS46S3aR4R3R2R1A5S1aR5A1S1fSaScS0S1S1cR1A1M0S10A2M1S27R1A1M2A2S0S1S1G2S18A2Z1000M3A2G0A2A2SaScS0G1S28R1A1M4A2S0S1G4G3A2G0A2A2SaScS0G1S26R1A1M5A2S0S1G5S15A2G0A2A2SaScS0G1S24R1A1M6A2S0S1G6G3A2G0A2A2ScS0G1S25R1A1M7A2S0S1G7G3A2G0A2A2A2A2A2A2TG;F_;Fmd;Ftp;Frho;FX;").
Proof.
  intros X rho tp md HA. cbn zeta. pose proof HA as (_ & _ & _ & _ & _ & HI3 & _).
  destruct HI3 as ((_ & _ & _ & PS & PT & PF & PC & PD) & _). repeat split; assumption.
Qed.
End CInvEnsure.

(* [comment removed for export] *)
Module SpineMallocR7.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "entailsA"; "sym_runA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SAlu"; "ss_next"; "eval"; "SVar"; "ss_facts"; "swf"; "valuation"; "SPNot"; "holds"; "ss_lenient"; "SPBranch"; "SPUle"; "rw"; "SMd"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "list"; "nil"; "pair"; "prod"; "Some"; "option"; "andb"; "false"; "length"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "cP2"; "GR"; "vMU"; "HINT_map"; "cPa"; "cPb"; "req_e"; "vAU"; "vK"; "vNF"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "of_nat"; "mul"; "sub"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SLL"; "ALU_SRL"; "BC_LTU"; "ALU_SRA"; "ALU_XOR"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "V_CLS"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineMallocR7"; "F_mu0"; "F_hi"; "size_e_hi"; "size_e_lo"; "x19_e0"; "x19_e1"; "popfacts"; "total_e"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "cs_free_array"; "cs_allocated_user"; "cs_mapped_user"; "AA"; "class_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "JR"; "entryR"; "ph0"; "gh_nf"; "ghosts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2"; "only_var"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5"; "tab1_ok"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "ulink"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "MUCAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocR2"; "rigids"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymObj SymFrame SymEntail SymCFG Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv InvLaws PrimCredit PrimCreditLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel RefillModelP RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.PrimRoom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModelP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocR2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition size_e_hi : sv := ltac2:(tb__ "0|4|
SbS37SbS38SbS3cSbS39SeS40A1M0SaZ3fA1M1A3G1A3SbS3aSbS39SaZ200A1SbS3aSbS37G0SaN10A1A3SaZ1A1M2A3A3M3G2A3A3G3A3").
Definition size_e_lo : sv := ltac2:(tb__ "0|0|
SbS39SeS40A1SaZ5A1A3").
Definition tabS_okb : bool := ltac2:(tb__ "0|0|
S22S22S22S61S40S45S51Z11UeA5S60S40S45A2A2S61S40S46S51Z1U10A5A2S60S40S46A2A2").
Lemma tabS_ok : tabS_okb = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Definition F_hi : sprop := ltac2:(tb__ "0|0|
S15S3bSaZ10A1SeS40A1A3").

Definition total_e : sv := ltac2:(tb__ "0|0|
SbS37S2dS18S3eSeS41A1S2cA3A3").
Definition x19_e0 : sv := ltac2:(tb__ "0|0|
SbS37SbS38SbS37S4aSaN1A1A3SaZfffffffffffc0000A1A3SaZ40000A1A3").
Definition x19_e1 : sv := ltac2:(tb__ "0|0|
SbS37SbS38SbS37S4aSbS3dS28SaZffffffffffffffffA1A3A3SaZfffffffffffc0000A1A3SaZ40000A1A3").
Definition F_mu0 : sprop := SPBranch BC_EQ vMU (SLit 0).

Definition popfacts (A : AA) (rb : valuation) : Prop := ltac2:(tb__ "0|1|
S4eQ40S17Vrb;PcA2A2S25S5eR1A1S25S5fVA;R2A2S57S6S31S33S24S25S53R1A1A2A1S52R2A1A2S6S30S32S55R1A1Z40000A2S65R2A1M0A2S30G0Ze0000000A2A2A2Tcs;Tc;Tnv;").

Lemma entry_popfacts : ltac2:(tb__ "0|1|
S56S11S1cS4dQ40M0A1A1S62S1cS63A1S64S11S5aR7R6R5R4R3R2R1A7S31S5cR8R7A2S52S5eS4eG0S17R7PcA2A2A1A1A2S49R9R8A2F_;F_;Frho;Fst;FW;Fmd0;Ftp0;Frb;FA;").
Proof.
  intros A rb tp0 md0 W st rho HE HNP. pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF.
  destruct CF as ((_ & C1 & _) & (K1 & _) & _ & _ & (_ & _ & Hc0) & _).
  destruct HE as (_ & HA & _). unfold popfacts. cbn zeta. unfold gh_nf in HNP. split; [exact HNP|].
  pose proof (populate_room segs A rb tp0 md0 _ HA C1 Hc0 ltac:(unfold cst_of in HNP; lia)) as [R1 R2].
  unfold kUserMapSize, kUserSpaceSize, kRegionSize, kFreeArraySize in *. unfold cst_of. split; [exact R1 | exact R2].
Qed.

Section VALS.
Variables (A : AA) (rb r : valuation).
Hypothesis CF : cfacts A rb.
Hypothesis PF : popfacts A rb.
Hypothesis RG : ltac2:(tb__ "0|0|
S66VA;Vrb;Vr;A3").
Hypothesis GH : ltac2:(tb__ "0|0|
S5dVA;Vrb;Vr;A3").
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let cs : class_state := cst_of A nv.

Lemma size_hi_val : ltac2:(tb__ "0|0|
S13Vr;S44A2S5S4dQ40A1SdVr;S45A2SdVr;SeS41A1A2A3F_;").
Proof.
  intros HF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((_ & C1 & _) & _).
  destruct RG as (_ & E148 & _ & _ & _ & _ & _ & E158). fold nv c in E148, E158.
  unfold F_hi in HF. cbn [holds eval] in HF. unfold branch_taken, bv_ltu in HF. apply Z.ltb_lt in HF. unfold V_CLS in HF. rewrite E158 in HF. rewrite !u64_lit in HF by (clear -C1; lia).
  pose proof tabS_ok as T. unfold tabS_okb in T. apply andb_prop in T as [T _]. apply andb_prop in T as [T _]. apply andb_prop in T as [T1 T2].
  cbn [eval]. unfold V_SIZE. rewrite E148. exact (tab1_ok_sound V_CLS size_e_hi Size 17 14 r c T1 T2 E158 ltac:(clear -C1 HF; lia)).
Qed.
Lemma size_lo_val : ltac2:(tb__ "0|0|
S7S13Vr;S44A2A1S5S4dQ40A1SdVr;S46A2SdVr;SeS41A1A2A3F_;").
Proof.
  intros HF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF. destruct CF as ((_ & C1 & _) & _).
  destruct RG as (_ & E148 & _ & _ & _ & _ & _ & E158). fold nv c in E148, E158.
  unfold F_hi in HF. cbn [holds eval] in HF. unfold branch_taken, bv_ltu in HF. unfold V_CLS in HF. rewrite E158 in HF. rewrite !u64_lit in HF by (clear -C1; lia).
  assert (C16 : c <= 16) by (destruct (Z.ltb_spec 16 c) as [X|X]; [exfalso; apply HF; reflexivity | exact X]).
  pose proof tabS_ok as T. unfold tabS_okb in T. apply andb_prop in T as [T T4]. apply andb_prop in T as [T T3].
  cbn [eval]. unfold V_SIZE. rewrite E148. exact (tab1_ok_sound V_CLS size_e_lo Size 1 16 r c T3 T4 E158 ltac:(clear -C1 C16; lia)).
Qed.

Lemma pop_nums : ltac2:(tb__ "0|4|
S51Vc;A1S25S52Vc;A1S25S33S24S25S53Vcs;A1A2A1S25S54Vcs;A1S25S55Vcs;A1S25S6S6S30Z20R5A2S30R5Z10000M0A2A2S6S6S30Z1R4A2S30R4Z8A2A2S6S6S30Z0M1R3A2S31R3R4A2A2S6S6S30G1R2A2S30R2R1A2A2S6S30R1Zdffc0000A2S6S31R1S32R2R5A2A2S6S6S31G1S34R5S35R4R3A2A2M2A2S30G2G0A2A2S6S31R1S32R2G2A2M3A2S30G3S32R1G0A2A2A2A2A2A2A2A2A2A2Tmu;Tau;Tnf;Tk;TS;").
Proof.
  intros S k nf au mu.
  unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF. fold S k nf au mu in CF.
  destruct CF as ((_ & _ & S1 & _) & (K1 & _ & K3) & (_ & AU0 & _ & _ & TI0) & _).
  destruct PF as (NP & RM & RC). fold nv c cs in NP, RM, RC. fold k nf mu in NP, RM.
  pose proof (Zle_0_nat (length (cs_free_array cs))) as NF0. fold nf in NF0.
  clear -S1 K1 K3 AU0 TI0 NP RM RC NF0.
  assert (B1 : 0 < S * (k - nf)) by nia. assert (B2 : S * (k - nf) <= S * k) by nia. assert (B3 : S <= S * (k - nf)) by nia. lia.
Qed.

Lemma total_val : ltac2:(tb__ "0|0|
S5S25S4eQ40SdVr;S4aA2A2S32S54Vcs;A1S34S51Vc;A1S35S52Vc;A1S33S24S25S53Vcs;A1A2A1A2A2A2A3").
Proof.
  pose proof pop_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8.
  destruct RG as (_ & E148 & _). fold nv c in E148.
  destruct GH as (_ & Q221 & _ & Q223 & _ & _ & _ & Q227 & _). unfold gh_nf in Q221. fold nv c cs in Q221, Q223, Q227.
  unfold total_e, req_e, vAU, vK, vNF, V_SIZE. cbn [eval]. rewrite add_val, mul_val, sub_val, E148, Q221, Q223, Q227.
  rewrite !u64_lit by (clear -N1 N2 N3 N4 N5; lia).
  rewrite (Z.mod_small (kchunks c - _)) by (clear -N2 N3; lia). rewrite (Z.mod_small (Size c * _)) by (clear -N7; lia).
  rewrite Z.mod_small by (clear -N4 N5 N7; lia). reflexivity.
Qed.

Lemma F_pop_hold : Forall (holds r) F_pop.
Proof.
  pose proof total_val as TV.
  pose proof pop_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8.
  destruct GH as (_ & Q221 & _ & Q223 & Q224 & _ & _ & Q227 & _). unfold gh_nf in Q221. fold nv c cs in Q221, Q223, Q224, Q227.
  unfold F_pop. repeat apply Forall_cons; try apply Forall_nil.
  - cbn [holds]. unfold branch_taken, bv_ltu, vNF, vK. cbn [eval]. rewrite Q221, Q227. rewrite !u64_lit by (clear -N2 N3; lia). apply Z.ltb_lt. exact (proj2 N3).
  - unfold HINT_map. cbn [holds]. unfold branch_taken, bv_ltu. fold total_e. rewrite TV. unfold vMU. cbn [eval]. rewrite Q224. rewrite u64_lit by (clear -N4 N5; lia).
    apply Z.ltb_lt. exact (proj1 N8).
  - cbn [holds]. unfold vMU. cbn [eval]. rewrite Q224. rewrite !u64_lit by (clear -N4 N5; lia). exact N5.
Qed.

Lemma x19_val1 : ltac2:(tb__ "0|0|
S5S4dQ40A1SdVr;S48A2SdVr;SaZ40000A1A2A3").
Proof.
  pose proof total_val as TV.
  pose proof pop_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8.
  destruct GH as (_ & _ & _ & _ & Q224 & _). fold nv c cs in Q224.
  set (tot := cs_allocated_user cs + Size c * (kchunks c - Z.of_nat (length (cs_free_array cs)))) in *.
  unfold x19_e1. cbn [eval]. apply bv_eq. rewrite add_val, and_val, add_val, xor_val. fold total_e. rewrite TV. unfold vMU. cbn [eval]. rewrite Q224.
  rewrite !u64_lit by (clear -N4 N5; lia).
  rewrite lxor_ones64 by (clear -N4 N5; lia).
  replace ((tot + (18446744073709551615 - cs_mapped_user cs)) mod 2 ^ 64) with (tot - cs_mapped_user cs - 1).
  2: { apply (Z.mod_unique_pos _ _ 1); clear -N4 N5 N8; lia. }
  rewrite land_m18_small by (clear -N8; lia). rewrite Z.mod_small by (clear; lia). reflexivity.
Qed.
Lemma x19_val0 : ltac2:(tb__ "0|1|
S13Vr;S43A2S6S5S4dQ40A1M0SdVr;S47A2SdVr;SaZ40000A1A2A3S5G0SdVr;SaZ0A1A2SdVr;S28A2A3A2F_;").
Proof.
  intros HF. pose proof total_val as TV.
  pose proof pop_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8.
  destruct GH as (_ & _ & _ & _ & Q224 & _). fold nv c cs in Q224.
  unfold F_mu0 in HF. cbn [holds] in HF. unfold branch_taken, bv_eqb, vMU in HF. cbn [eval] in HF. rewrite Q224 in HF. rewrite !u64_lit in HF by (clear -N4 N5; lia). apply Z.eqb_eq in HF.
  set (tot := cs_allocated_user cs + Size c * (kchunks c - Z.of_nat (length (cs_free_array cs)))) in *.
  split.
  - unfold x19_e0. cbn [eval]. apply bv_eq. rewrite add_val, and_val, add_val. fold total_e. rewrite TV.
    replace (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615 by reflexivity. rewrite !u64_lit by (clear; lia).
    replace ((tot + 18446744073709551615) mod 2 ^ 64) with (tot - 1).
    2: { apply (Z.mod_unique_pos _ _ 1); clear -N4 N8 HF; lia. }
    rewrite land_m18_small by (clear -N4 N8 HF; lia). rewrite Z.mod_small by (clear; lia). reflexivity.
  - unfold vMU. cbn [eval]. rewrite Q224, HF. reflexivity.
Qed.
End VALS.

Section POP1.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HE : ltac2:(tb__ "0|0|
S5aVA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Notation JRp := (JR A Kc rb tp0 md0).

Variable F : nat.
Variables (E3 : axst) (LP : axst) (La Lb La0 La1 Lb0 Lb1 : leafA) (CP2C : axst) (sa0 sa1 sb0 sb1 : wsub).
Let FR : list sprop := factsR E3.
Let CPA : axst := ltac2:(tb__ "0|0|
S2aVFR;S1VLa;A1A2").
Let CPB : axst := ltac2:(tb__ "0|0|
S2bVFR;S1VLb;A1A2").
Hypothesis FP_in : ltac2:(tb__ "0|0|
S36S9S15S3bS2fS2eA3SfS0VLP;A1A1A3").
Hypothesis R_p1 : ltac2:(tb__ "0|1|
S5S21S1cS2A1M0A1S4S42VF;S1bS25Z415c0S1bS25Z41600S1dS25A1A3A3VLP;S1aA5S20G0S1bS2VLa;S1bS2VLb;S1dS2A1A3A3A2A3").
Hypothesis LN_p : ltac2:(tb__ "0|0|
S5S19S14S0VLP;A1A1S23A3").
Hypothesis NX_p : ltac2:(tb__ "0|0|
S5S19S4cS27ScS0VLP;A1A1A2S1aA3").
Hypothesis Fa_in : ltac2:(tb__ "0|0|
S36S9S44SfS0S1VLa;A1A1A1A3").
Hypothesis Fb_in : ltac2:(tb__ "0|0|
S36S9S12S44A1SfS0S1VLb;A1A1A1A3").
Hypothesis W_pa : ltac2:(tb__ "0|0|
S5S19S10S0VCPA;A1A1S1aA3").
Hypothesis D_pa : ltac2:(tb__ "0|4|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLa;A1A1S0VCPA;A1A2S20G3S1eG1G2S1bG0S1eS8S8S45SeS41A1A4S1dG0A1A3S1bS9S29S1bS9S16S28SaZdffc0000A1A2S1dS9A1A3A3A4A2A3").
Hypothesis NX_pa : ltac2:(tb__ "0|0|
S5S19S4bScS0VCPA;A1A1ScS0S1VLa;A1A1A1A2S1aA3").
Hypothesis W_pb : ltac2:(tb__ "0|0|
S5S19S10S0VCPB;A1A1S1aA3").
Hypothesis D_pb : ltac2:(tb__ "0|4|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLb;A1A1S0VCPB;A1A2S20G3S1eG1G2S1bG0S1eS8S8S46SeS41A1A4S1dG0A1A3S1bS9S29S1bS9S16S28SaZdffc0000A1A2S1dS9A1A3A3A4A2A3").
Hypothesis NX_pb : ltac2:(tb__ "0|0|
S5S19S4bScS0VCPB;A1A1ScS0S1VLb;A1A1A1A2S1aA3").
Hypothesis R_p2a : ltac2:(tb__ "0|1|
S5S21S1cS2A1M0A1S4S42VF;S1bS25Z41630S1dS25A1A3VCPA;S1aA5S20G0S1bS2VLa0;S1bS2VLa1;S1dS2A1A3A3A2A3").
Hypothesis LN_pa : ltac2:(tb__ "0|0|
S5S19S14S0VCPA;A1A1S23A3").
Hypothesis NXr_pa : ltac2:(tb__ "0|0|
S5S19S4cS27ScS0VCPA;A1A1A2S1aA3").
Hypothesis R_p2b : ltac2:(tb__ "0|1|
S5S21S1cS2A1M0A1S4S42VF;S1bS25Z41630S1dS25A1A3VCPB;S1aA5S20G0S1bS2VLb0;S1bS2VLb1;S1dS2A1A3A3A2A3").
Hypothesis LN_pb : ltac2:(tb__ "0|0|
S5S19S14S0VCPB;A1A1S23A3").
Hypothesis NXr_pb : ltac2:(tb__ "0|0|
S5S19S4cS27ScS0VCPB;A1A1A2S1aA3").

Section LEAF.
Variables (L : leafA) (s : wsub) (mu0 : bool).
Let C2 : axst := ltac2:(tb__ "0|0|
S26VFR;S1VL;A1A2").
Hypothesis F_in : ltac2:(tb__ "0|0|
S36S9S19S9Lmu0;Vmu0;S43S12S43A1X19x2SfS0S1VL;A1A1A1A3").
Hypothesis W_2 : ltac2:(tb__ "0|0|
S5S19S10S0VC2;A1A1S1aA3").
Hypothesis D_2 : ltac2:(tb__ "0|6|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VL;A1A1S0VC2;A1A2S20G3S1eG1G2S19G1Lmu0;Vmu0;S1bG0S1eS8S8S47SaZ40000A1M4A4S1bG0S1eS8S8SaZ0A1S28A4S1dG0A1M5A3A3S1bG0S1eS8S8S48G4A4G5A3X19x2S1dS9A1A4A2A3").
Hypothesis NX_2 : ltac2:(tb__ "0|0|
S5S19S4bScS0VC2;A1A1ScS0S1VL;A1A1A1A2S1aA3").
Hypothesis ENT_2 : ltac2:(tb__ "0|0|
S5S19S3VC2;VCP2C;Vs;A3S1aA3").
Hypothesis SID_2 : ltac2:(tb__ "0|0|
S5S19S4fVs;S27A2S1aA3").

Lemma join_leaf : ltac2:(tb__ "0|1|
S11S1cS4dQ40A1A1S58S49VA;Vrb;A2S11VTR;S50S42S59VA;VKc;Vrb;Vtp0;Vmd0;S5bA6M0VCP2C;R1R4A5R3A2Fr';VTR;S50S42G0S1VL;A1R5R4A5R3A2F_;F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q PF HC.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state L) (ax_S C2) _ _ ph0 r tp Q W_2 D_2 NX_2).
  { intros tr md (HFz & HGh & _) HF. split; [|constructor].
    pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
    pose proof (proj1 (Forall_forall _ _) HF _ F_in) as HB.
    unfold diffs_ok. destruct mu0.
    - destruct (x19_val0 A rb r CF PF RG HGh HB) as [X1 X2]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; assumption.
    - repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. exact (x19_val1 A rb r CF PF RG HGh). }
  change (ax_setS (la_state L) (ax_S C2)) with C2.
  apply (tr_pre Kc TR KIT (SPA segs (JRp ph0) CP2C (rho_sub r s) tp)); [|exact (HC _)].
  intros w Hw. apply (SPA_entails_J (JRp ph0) (JRp ph0) C2 CP2C s r tp w ENT_2); [|exact Hw].
  intros HJ. eapply (JR_stable A Kc rb tp0 md0 ph0 GR HKc ltac:(lia)); [exact (rho_sub_agree s GR r SID_2) | apply mat_equiv_refl | exact HJ].
Qed.
End LEAF.

Hypothesis Fa0_in : ltac2:(tb__ "0|0|
S36S9S43SfS0S1VLa0;A1A1A1A3").
Hypothesis Fa1_in : ltac2:(tb__ "0|0|
S36S9S12S43A1SfS0S1VLa1;A1A1A1A3").
Hypothesis Fb0_in : ltac2:(tb__ "0|0|
S36S9S43SfS0S1VLb0;A1A1A1A3").
Hypothesis Fb1_in : ltac2:(tb__ "0|0|
S36S9S12S43A1SfS0S1VLb1;A1A1A1A3").
Hypothesis W_a0 : ltac2:(tb__ "0|0|
S5S19S10S0S26VFR;S1VLa0;A1A2A1A1S1aA3").
Hypothesis W_a1 : ltac2:(tb__ "0|0|
S5S19S10S0S26VFR;S1VLa1;A1A2A1A1S1aA3").
Hypothesis W_b0 : ltac2:(tb__ "0|0|
S5S19S10S0S26VFR;S1VLb0;A1A2A1A1S1aA3").
Hypothesis W_b1 : ltac2:(tb__ "0|0|
S5S19S10S0S26VFR;S1VLb1;A1A2A1A1S1aA3").
Hypothesis D_a0 : ltac2:(tb__ "0|5|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLa0;A1M4A1S0S26VFR;G4A2A1A2S20G3S1eG1G2S1bG0S1eS8S8S47SaZ40000A1A4S1bG0S1eS8S8SaZ0A1S28A4S1dG0A1A3A3S1dS9A1A4A2A3").
Hypothesis D_a1 : ltac2:(tb__ "0|5|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLa1;A1M4A1S0S26VFR;G4A2A1A2S20G3S1eG1G2S1bG0S1eS8S8S48SaZ40000A1A4S1dG0A1A3S1dS9A1A4A2A3").
Hypothesis D_b0 : ltac2:(tb__ "0|5|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLb0;A1M4A1S0S26VFR;G4A2A1A2S20G3S1eG1G2S1bG0S1eS8S8S47SaZ40000A1A4S1bG0S1eS8S8SaZ0A1S28A4S1dG0A1A3A3S1dS9A1A4A2A3").
Hypothesis D_b1 : ltac2:(tb__ "0|5|
S5S21S1fS1cS1fS8S8A2M0A1M1S1cS9A1M2A2M3A1S3fS0S1VLb1;A1M4A1S0S26VFR;G4A2A1A2S20G3S1eG1G2S1bG0S1eS8S8S48SaZ40000A1A4S1dG0A1A3S1dS9A1A4A2A3").
Hypothesis NX_a0 : ltac2:(tb__ "0|1|
S5S19S4bScS0S26VFR;S1VLa0;A1M0A2A1A1ScS0G0A1A1A2S1aA3").
Hypothesis NX_a1 : ltac2:(tb__ "0|1|
S5S19S4bScS0S26VFR;S1VLa1;A1M0A2A1A1ScS0G0A1A1A2S1aA3").
Hypothesis NX_b0 : ltac2:(tb__ "0|1|
S5S19S4bScS0S26VFR;S1VLb0;A1M0A2A1A1ScS0G0A1A1A2S1aA3").
Hypothesis NX_b1 : ltac2:(tb__ "0|1|
S5S19S4bScS0S26VFR;S1VLb1;A1M0A2A1A1ScS0G0A1A1A2S1aA3").
Hypothesis ENT_a0 : ltac2:(tb__ "0|0|
S5S19S3S26VFR;S1VLa0;A1A2VCP2C;Vsa0;A3S1aA3").
Hypothesis ENT_a1 : ltac2:(tb__ "0|0|
S5S19S3S26VFR;S1VLa1;A1A2VCP2C;Vsa1;A3S1aA3").
Hypothesis ENT_b0 : ltac2:(tb__ "0|0|
S5S19S3S26VFR;S1VLb0;A1A2VCP2C;Vsb0;A3S1aA3").
Hypothesis ENT_b1 : ltac2:(tb__ "0|0|
S5S19S3S26VFR;S1VLb1;A1A2VCP2C;Vsb1;A3S1aA3").
Hypothesis SID_a0 : ltac2:(tb__ "0|0|
S5S19S4fVsa0;S27A2S1aA3").
Hypothesis SID_a1 : ltac2:(tb__ "0|0|
S5S19S4fVsa1;S27A2S1aA3").
Hypothesis SID_b0 : ltac2:(tb__ "0|0|
S5S19S4fVsb0;S27A2S1aA3").
Hypothesis SID_b1 : ltac2:(tb__ "0|0|
S5S19S4fVsb1;S27A2S1aA3").

Theorem populate_head : ltac2:(tb__ "0|1|
S11S1cS4dQ40A1A1S58S49VA;Vrb;A2S11VTR;S50S42S59VA;VKc;Vrb;Vtp0;Vmd0;S5bA6M0VCP2C;R1R4A5R3A2Fr';F_;VTR;S50S42G0VLP;R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HC.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.

  apply (tr_facts Kc TR KIT). intros HF0. pose proof (proj1 (Forall_forall _ _) HF0 _ FP_in) as BF. cbn [holds] in BF.
  apply (tr_pure Kc TR KIT (popfacts A rb)).
  { intros w [_ (HFz & HGh & _)]. apply (entry_popfacts _ _ _ _ _ _ _ HE).
    destruct HGh as (_ & Q221 & _ & _ & _ & _ & _ & Q227 & _).
    unfold cfacts in CF. cbn zeta in CF. destruct CF as (_ & (K1 & _) & _ & (_ & MF0) & _).
    unfold branch_taken, bv_ltu, vNF, vK in BF. cbn [eval] in BF. rewrite Q221, Q227 in BF. unfold gh_nf in *.
    rewrite !u64_lit in BF by lia. apply Z.ltb_lt in BF. exact BF. }
  intros PF.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x415c0; 0x41600] LP [La; Lb] ph0 r tp Q R_p1 LN_p NX_p).
  intros L r1 [<-|[<-|[]]] _.
  -
    apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state La) (ax_S CPA) _ _ ph0 r1 tp Q W_pa D_pa NX_pa).
    { intros tr md (HFz & HGh & _) HF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
      split.
      - unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        exact (size_hi_val A rb r1 CF RG (proj1 (Forall_forall _ _) HF _ Fa_in)).
      - pose proof (F_pop_hold A rb r1 CF PF RG HGh) as FPH. unfold F_pop in FPH. inversion FPH as [|? ? _ FPH']; subst. exact FPH'. }
    change (ax_setS (la_state La) (ax_S CPA)) with CPA.
    apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x41630] CPA [La0; La1] ph0 r1 tp Q R_p2a LN_pa NXr_pa).
    intros L r2 [<-|[<-|[]]] _.
    + exact (join_leaf La0 sa0 true Fa0_in W_a0 D_a0 NX_a0 ENT_a0 SID_a0 r2 tp Q PF (HC PF)).
    + exact (join_leaf La1 sa1 false Fa1_in W_a1 D_a1 NX_a1 ENT_a1 SID_a1 r2 tp Q PF (HC PF)).
  -
    apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state Lb) (ax_S CPB) _ _ ph0 r1 tp Q W_pb D_pb NX_pb).
    { intros tr md (HFz & HGh & _) HF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
      split.
      - unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        exact (size_lo_val A rb r1 CF RG (proj1 (Forall_forall _ _) HF _ Fb_in)).
      - pose proof (F_pop_hold A rb r1 CF PF RG HGh) as FPH. unfold F_pop in FPH. inversion FPH as [|? ? _ FPH']; subst. exact FPH'. }
    change (ax_setS (la_state Lb) (ax_S CPB)) with CPB.
    apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x41630] CPB [Lb0; Lb1] ph0 r1 tp Q R_p2b LN_pb NXr_pb).
    intros L r2 [<-|[<-|[]]] _.
    + exact (join_leaf Lb0 sb0 true Fb0_in W_b0 D_b0 NX_b0 ENT_b0 SID_b0 r2 tp Q PF (HC PF)).
    + exact (join_leaf Lb1 sb1 false Fb1_in W_b1 D_b1 NX_b1 ENT_b1 SID_b1 r2 tp Q PF (HC PF)).
Qed.
End POP1.
End SpineMallocR7.

(* [comment removed for export] *)
Module SpineCallocR1.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "prod"; "nat"; "app"; "list"; "nil"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "rw"; "valuation"; "holds"; "ss_facts"; "ss_objs"; "SLit"; "agree_below"; "obj_range"; "ranges_disjoint"; "smatch"; "sprop_below"; "ss_next"; "sstate"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "bv_signed"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "ag_spacebeg"; "ag_thread"; "aa_cache_inited"; "aa_geom"; "ag_ctx"; "ageom"; "class_state"; "cs_allocated_user"; "cs_mapped_free_array"; "cs_mapped_user"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1"; "r0_of"; "ghostl"; "NR0"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "A_globals"; "unwind_objs"; "F_sp_high"; "KcA"; "V_DEPTH"; "chain_pre"; "malloc_depth"; "pre_facts"; "unwind_factsS"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "w_cfg"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "FAb"; "JR"; "entryR"; "gh_chx"; "gh_new"; "gh_nf"; "ghosts"; "ph0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "F_gen"; "O_pcc0"; "O_st"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "F_r0"; "F_r1"; "GR"; "O_pcm"; "O_ri"; "cR0"; "cR0a"; "vAU"; "vMC"; "vMFA"; "vMU"; "vNF"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kSpaceSize"; "max_count"; "region_info"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "geom_ok"; "sep_geom3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1.ZONE"; "armint"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cnt_of"; "cst_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.PArith.BinPos.Pos"; "le"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require al.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineCallocS4 PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.al.SpineCallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineCallocS4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ZONE.
Let segs : list Segment := segsA.
Variable W : list ulink.

Definition armint (G : ageom) (lo hi : Z) : Prop := ltac2:(tb__ "0|2|
S22S21S23S24S2aVG;A1M0Z120A2Vlo;A2S23Vhi;S24G0Zc60A2A2A2S22S21S23S29VG;A1M1Vlo;A2S23Vhi;S24S24G1S68A2Z1000A2A2A2S21S23S67Vlo;A2S23Vhi;S66A2A2A2A2").

Lemma base_zone : ltac2:(tb__ "0|3|
S2eSdS18S2S5S49A1S48A2S5S9A1S1aS1aS6eR7A1S6fR8A1S15Vsegs;R8R7R6A4S9S38S9R1R7A3S38S9R2S10RaA1A3F_;Fo;S20S5S2S2SaSaA2SaA2M0A1S25S9G0S34R7A4S25S9G0S34S4S9S1S9S3cS4S9S3fVW;A1S3eA3A3S3dA3A4A3SeRbS40A2S26SbSeRcA1S43VW;A1A3S23S33ReA1S24S1eQ40M1ScRdPaA2A2S1fG1ScRdS42A2A2A2A2S20S1dG1A1M2ScReP97A2S1cG1S2aRfA1A2A3S20G2ScRfP98A2S1cG1S2dR10A1A2A3S71R11RcRbA3S26S9S9S14S13R12R1A2S0S1aS1aReRdA4A2Lo';ReA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fhi;Flo;Fobjs;Fw;FS;FrhoE;FG;").
Proof.
  intros G rhoE S w objs lo hi HG0 HS3 Hsm Hsub HSK Hhigh HCH Htop E151 E152 HI.
  pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  clear G15 G16 G17 G18 G20 G21 G1 G2 G3 G4 G10 G11.
  pose proof (geom_bands _ HG0) as (_ & TB & CB & _ & TI & CI & _). unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in TB, CB, TI, CI.
  destruct HS3 as (PS1 & PS2 & _). rewrite kSpaceSize_val in PS1, PS2.
  pose proof (topG_range G) as TG.
  unfold armint, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in HI. rewrite kSpaceSize_val in HI.
  destruct objs as [|osw orest]; [cbn [map] in HSK; exfalso; clear -HSK; discriminate HSK|].
  cbn [map] in HSK.
  assert (SKsw : skel osw = (SVar 10, SVar V_DEPTH, SLit 0)) by exact (f_equal (hd (skel osw)) HSK).
  assert (SKrest : map skel orest = map skel ((unwind_objs W ++ A_globals) ++ RT_m1)) by exact (f_equal (@tl _) HSK).
  destruct (sw_range_gen _ rhoE _ _ osw Hsm (Hsub osw (or_introl eq_refl)) SKsw Hhigh) as (SW1 & SW2 & SW3).
  assert (SW0 : topG G <= fst (obj_range rhoE osw)) by (rewrite (sw_lo_gen rhoE osw SKsw); exact Htop).
  assert (LNK : Forall (fun o => topG G + 16 <= bv_unsigned (eval rhoE (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0) (unwind_objs W)).
  { apply (unwind_objs_above _ _ (topG G)); [exact HCH | clear -SW0 SW2 SW3; lia | clear -TG; lia]. }
  constructor.
  - clear -SW0 G14 HI G6 TG. unfold ranges_disjoint. cbn [fst snd]. lia.
  - apply (Forall_ranges_skel rhoE (fun r => ranges_disjoint r (lo, hi)) orest _ SKrest).
    apply Forall_app. split.
    + apply Forall_app. split.
      * eapply Forall_impl; [|exact LNK]. intros [ob olo ohi ocs od] (B & L & Hh). cbn [ob_base ob_lo ob_hi] in B, L, Hh. subst olo ohi.
        unfold ranges_disjoint. rewrite !obj_range_mk by (clear -B TG; lia). cbn [fst snd]. clear -B G14 HI G6 TG. lia.
      * unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI.
        repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval]; rewrite ?u64_lit by lia;
          clear -HI G5 G13 TI; lia.
    + unfold RT_m1, RT_m0, O_rt1a, O_rt1b, O_tsda, O_tsdb, O_tsdc, O_self_tsd, O_tsd0, O_ctx8, O_ctx98, O_T0, O_T40, O_T3168, O_cfa, O_pga, O_pgb, O_mcs,
             O_insta, O_insta2, O_instb, O_rss, O_cfb, O_cfc, O_rms, O_ppf, O_hooks, O_lsan, O_cft, O_afl, O_csd, O_die.
      unfold carved, vT, vCTX, vTOP, vBOT, vSB, vRIS.
      repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint; rewrite ?obj_range_mk by lia; cbn [fst snd eval];
        rewrite ?E151, ?E152, ?u64_lit by (first [ clear -G5 G6 TG; lia | clear -G8 G9 TG; lia | lia ]);
        (first [ clear -HI G5 G13 TI; lia | clear -HI G5 G6 TB TI PS1 G13 TG; lia | clear -HI G8 G9 CB CI PS2 G13 G24 TG G5 G6 G19; lia ]).
Qed.
End ZONE.

Definition NR0 : list carve_spec := ltac2:(tb__ "0|b|
S1S2S2S2SaS1aA2M0S1aA2M1S5S2S2S1aS3A2M2SaA2M3A1M4A2M5S0G1G4S0G0S1aS0SaS1aS58Z4M6A4Z8A4S1G3S0G2SaS0S1aS3G6U4A4S61A4S6G3A1M7A3A4S1G5S0G1G4S0G0S1aS0SaS1aS65Z0M8A4Z80A4S1G3S0G2SaS0S1aS3G8U8M9A4S11G8A1MaA4S1G3S0G2SaS0S1aS3Z10G9A4S64A4S1G3S0G2SaS0S1aS3Z18G9A4S62A4S1G3S0G2SaS0S1aS3Z20G9A4S60A4S1G3S0G2SaS0S1aS3Z28G9A4GaA4S1G3S0G2SaS0S1aS3Z30G9A4S63A4S1G3S0G2SaS0S1aS3Z38G9A4GaA4S1G3S0G2SaS0S1aS3Z44U1A4GaA4G7A3A3A3A3A3A3A3A3A4S6G5A1A3A3").
Lemma NR0_objs : ltac2:(tb__ "0|0|
S20S5S9A1S25S6cS9S6bS37A4S1S9S5cS1S9S5dS6S9A1A3A3A3"). Proof. reflexivity. Qed.

Definition ghostl (A : AA) (rb : valuation) : list (positive * word) := ltac2:(tb__ "0|3|
S1eQ40M0ScVrb;PcA2A2S1aS72R1A1S1aS74VA;R2A2S2fS29S2cVA;A1A1S1aS1S2S1bS1dG0A1M1A2M2S0S1bG1PdcS1cG0S69R3A1A2A4S1G2S0S1bG1PddS1cG0S51VA;Vrb;A2A2A4S1G2S0S1bG1PdeS1cG0S31R2A1A2A4S1G2S0S1bG1PdfS1cG0S30R2A1A2A4S1G2S0S1bG1Pe0S1cG0S32R2A1A2A4S1G2S0S1bG1Pe1S1cG0S6aR1R3A2A2A4S1G2S0S1bG1Pe2S1cG0S4cVA;Vrb;A2A2A4S1G2S0S1bG1Pe3S1cG0S70R3A1A2A4S1G2S0S1bG1Pe4S1cG0S50VA;Vrb;A2A2A4S1G2S0S1bG1Pe5S1cG0S4fVA;Vrb;A2A2A4S6G2A1A3A3A3A3A3A3A3A3A3A3TSB;Tcs;Tc;Tnv;").
Definition r0_of (A : AA) (rb : valuation) : valuation := ltac2:(tb__ "0|0|
S6dVrb;S36VA;Vrb;A2A2").

Lemma ghostl_ge : ltac2:(tb__ "0|1|
S28SdS1bS1dQ40A1M0S38S2S1bG0A2S0S1bG0R2R1A4S36R4R3A2A3S76PdcR3A2F_;Fv;Fj;Frb;FA;").
Proof. intros A rb j v H. unfold ghostl in H. cbn [In] in H. repeat (destruct H as [H|H]; [injection H as <- _; lia|]). destruct H. Qed.
Lemma r0_agree : ltac2:(tb__ "0|0|
S28SdS12PdcR1S35R2R1A2A3Frb;FA;").
Proof. intros A rb. apply agree_below_rho_sets. apply ghostl_ge. Qed.
Lemma r0_ghosts : ltac2:(tb__ "0|0|
S28SdS52R2R1S35R2R1A2A3Frb;FA;").
Proof.
  intros A rb. unfold ghosts, r0_of.
  assert (ND : List.NoDup (map fst (ghostl A rb))).
  { unfold ghostl. cbn [map fst]. repeat (constructor; [cbn [In]; intros H; repeat (destruct H as [H|H]; [discriminate H|]); exact H|]). constructor. }
  repeat split; apply (rw_rho_sets_in rb (ghostl A rb) _ _ ND); unfold ghostl; cbn [In]; tauto.
Qed.

Section ENTRY.
Let segs : list Segment := segsA.
Variable nW : nat. Variable st : ustop.
Let W : list ulink := Wcan nW.

Variable E3 : axst.
Hypothesis SK3 : ltac2:(tb__ "0|1|
S20S5S2S2SaSaA2SaA2M0A1S25S9G0S34S10S27VE3;A1A1A4S25S9G0S34S4S9S4S9S1S9S3cS4S9S3fVW;A1S3eA3A3S3dA3S1S9S56S1S9S57S6S9A1A3A3A3A4A3").
Hypothesis XX3 : ax_X E3 = [].
Hypothesis XF3 : ltac2:(tb__ "0|0|
S3aSbS4SbS4SbS46VW;Vst;A2S45S44A1A3S55A3SfS27VE3;A1A1A3").
Hypothesis NX3 : ltac2:(tb__ "0|0|
S20S7S77S17S27VE3;A1A1PdcA2S8A3").
Hypothesis WR0a : ltac2:(tb__ "0|0|
S20S7S19S27S5fVE3;A1A1A1S8A3").
Hypothesis FB0 : ltac2:(tb__ "0|0|
S20S7S39SbS16S5bA1S4SbSfS27VE3;A1A1S4SbS59S5aA3A3A3S8A3").

Lemma refill_entry : ltac2:(tb__ "0|2|
S28S41SdSdS5S1dQ40M0A1A1S4bS54VW;Vst;A2S20S7S2bR7A1S8A3S20S1aS73R8S1eG0ScR6PcA2A2A2Z0A3S3bVsegs;S75VW;Vst;R9R8R7A5VE3;R6R5R4A6S21S4eRaR7R6S47S4aR5A1A1M1VW;Vst;R8A7S3bVsegs;S4dRaR9R7R6G1S53A6S5eVE3;A1S35RaR7A2R6R5A6A2F_;F_;F_;F_;Fw;Ftp;FrhoE;Frho;FKc;FA;").
Proof.
  intros A Kc rho rhoE tp w HW Hini Hcnt H.
  pose proof H as [HsmA [Hag HJ]]. pose proof Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN, HB.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  rewrite <- E12 in Hcnt. set (nv := bv_unsigned (rw rhoE 12%positive)) in *.
  assert (E151 : rw rhoE 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))). { rewrite <- (Hagw 151%positive) by (unfold GW; lia). reflexivity. }
  assert (E152 : rw rhoE 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))). { rewrite <- (Hagw 152%positive) by (unfold GW; lia). reflexivity. }
  assert (E158 : rw rhoE 158%positive = Z_to_bv 64 (cls_of nv)). { rewrite <- (Hagw 158%positive) by (unfold GW; lia). cbn. rewrite <- E12. reflexivity. }
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (HFX : forall p, In p ((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_gen) -> holds rhoE p).
  { intros p Hp. exact (proj1 (Forall_forall _ _) HFa p (XF3 p Hp)). }
  assert (Hnv : nv <= 64512).
  { pose proof (HFX (SPUle (SVar 12) (SLit 64512)) ltac:(apply in_or_app; right; unfold F_gen; cbn; tauto)) as F. cbn [holds eval] in F.
    rewrite u64_lit in F by lia. exact F. }
  pose proof (cls_facts nv ltac:(lia)) as (C1 & C2 & C3 & C4).
  destruct (kchunks_facts _ C1) as (K1 & K2 & K3).
  split.
  { unfold entryR. split; [exact Hag|]. split; [exact HA|]. split; [exact Htp|]. split; [exact HU|]. split; [exact HB|]. split; [lia|]. split; [exact Htop|]. split; [exact Hcnt|].
    exact (MI_ivs_wf segs _ _ (proj1 (proj2 HsmA))). }
  idtac "entry:1".

  pose proof HA as (HG & HR & HF & HRest & HM & HI3 & HBT). pose proof HG as HG0.
  destruct HRest as (Hsep & Hlive & Hprim & _ & _ & _ & _ & HTH & _).
  destruct Hprim as (_ & _ & _ & P4). specialize (P4 (cls_of nv) C1).
  pose proof (proj1 HI3) as HS3.
  pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (_ & _ & _ & _ & G5 & G6 & _ & _ & _ & _ & _ & G12 & G13 & G14 & _).
  pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & _ & _). unfold IMG_LO, IMG_HI in TI.
  pose proof (topG_range (aa_geom A)) as TG.
  set (G := aa_geom A) in *. set (c := cls_of nv) in *. set (T := ag_thread G) in *. set (SB := ag_spacebeg G) in *.
  assert (MT : forall z, T <= z < T + 0x1000 -> maskv (fs_footb G) (view segs (rm rhoE)) z = view segs (rm rhoE) z).
  { intros z Hz. apply maskv_out. apply fs_footb_thread; [exact HG | exact Hz]. }
  assert (MS : forall z, SB <= z < SB + kSpaceSize + 4096 -> maskv (fs_footb G) (view segs (rm rhoE)) z = view segs (rm rhoE) z).
  { intros z Hz. apply maskv_out. apply fs_footb_space; [exact HG | exact Hz]. }
  unfold class_repr in P4. fold G SB in P4.
  destruct P4 as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & PRI & N1 & N2 & N3 & N4 & N5 & N6 & _ & _ & _ & _ & _ & PE & _ & _ & CI & _).
  destruct (CI Hini) as (_ & D2 & _).
  set (cs := nthZ (aa_cls A) c cs_empty) in *.
  idtac "entry:2".
  set (r0 := r0_of A rhoE).
  pose proof (r0_agree A rhoE) as AG0. pose proof (r0_ghosts A rhoE) as GH0. fold r0 in AG0, GH0.
  assert (Erm0 : rm r0 = rm rhoE) by (unfold r0, r0_of; apply rm_rho_sets).

  assert (Ha : SPA segs (JR A Kc rhoE tp (cfg_model (w_cfg w)) ph0) E3 r0 tp w).
  { split.
    - eapply smatchA_agree; [|exact HsmA]. eapply agree_below_le; [|exact AG0]. apply Pos.leb_le. exact NX3.
    - unfold JR. split; [|split; [exact GH0|split; [exact HK|split; [|split]]]].
      + destruct AG0 as (Aw & Al & _). split; [exact Aw | exact Al].
      + unfold mlink, ph0, committed, revealedp, subU, subF. cbn [ph_u ph_f Nat.leb].
        repeat (split; [reflexivity|]). exists []. cbn [app length Z.of_nat]. split; [reflexivity|]. split; [intros p []|]. split; [lia | lia].
      + rewrite Erm0. unfold rlink, zoneR, ph0, revealedp, releasedp. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri Nat.leb].
        split; [intros; reflexivity|]. split.
        { intros z [[X _]|[[X _]|[[X _]|[[X _]|[[_ X]|[X|[[X _]|[X _]]]]]]]]; try discriminate X; exfalso; lia. }
        split; [intros j Hj; exfalso; lia|]. split; [intros i Hi; exfalso; lia|]. split; intros X; discriminate X.
      + intros a _. rewrite Erm0. reflexivity. }
  idtac "entry:3".

  destruct AG0 as (A0w & A0l & A0m).
  assert (R151 : rw r0 151%positive = Z_to_bv 64 T) by (rewrite <- (A0w 151%positive) by (clear; lia); exact E151).
  assert (R152 : rw r0 152%positive = Z_to_bv 64 (ag_ctx G)) by (rewrite <- (A0w 152%positive) by (clear; lia); exact E152).
  assert (R158 : rw r0 158%positive = Z_to_bv 64 c) by (rewrite <- (A0w 158%positive) by (clear; lia); exact E158).
  assert (R10 : rw r0 10%positive = rw rhoE 10%positive) by (rewrite <- (A0w 10%positive) by (clear; lia); reflexivity).
  assert (R15 : rw r0 V_DEPTH = rw rhoE V_DEPTH) by (rewrite <- (A0w V_DEPTH) by (unfold V_DEPTH; clear; lia); reflexivity).
  destruct GH0 as (Q220 & Q221 & Q222 & Q223 & Q224 & Q225 & Q226 & Q227 & Q228 & Q229).
  unfold gh_nf, FAb, cst_of in Q220, Q221, Q222, Q223, Q224, Q225, Q226, Q227.
  fold nv in Q220, Q221, Q222, Q223, Q224, Q225, Q226, Q227. fold c in Q220, Q221, Q222, Q223, Q224, Q225, Q226, Q227.
  fold cs in Q221, Q222, Q223, Q224. fold G in Q225, Q226. fold SB in Q225, Q226.
  assert (EB : bv_unsigned (eval r0 pc_base) = T + 208 + 80 * c).
  { unfold pc_base, vT, V_CLS. cbn [eval]. rewrite R151, R158. rewrite add_val, add_val, mul_val, !u64_lit by (clear -C1 G5 G6 TG; lia).
    rewrite (Z.mod_small (c * 80)) by (clear -C1; lia). rewrite (Z.mod_small (T + 208)) by (clear -G5 G6 TG; lia). rewrite Z.mod_small by (clear -C1 G5 G6 TG; lia). clear; lia. }
  pose proof kSpaceSize_val as KSV.
  assert (RIr : SB + kSpaceSize <= region_info SB c /\ region_info SB c + 128 <= SB + kSpaceSize + 4096).
  { unfold region_info, kRegionInfoStride. clear -C1. lia. }
  assert (ERI : bv_unsigned (eval r0 vRI) = region_info SB c).
  { unfold vRI. cbn [eval]. rewrite Q225. apply u64_lit. rewrite kSpaceSize_val in *. clear -RIr G13 G14 TG. unfold HIGH_SHADOW_END in *. lia. }
  pose proof (proj1 Ha) as HsmA0. pose proof (proj1 HsmA0) as Hsm0. unfold virt in Hsm0. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm0.
  pose proof (smatch_facts_hold _ _ _ _ Hsm0) as HFa0.
  assert (HFX0 : forall p, In p ((unwind_factsS W st ++ pre_facts malloc_depth) ++ F_gen) -> holds r0 p).
  { intros p Hp. exact (proj1 (Forall_forall _ _) HFa0 p (XF3 p Hp)). }

  destruct (map_eq_app _ _ _ _ ltac:(rewrite <- map_app; exact SK3)) as (ob & ox & EO & SKb & SKx).
  destruct ox as [|oc [|os [|? ?]]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKc : skel oc = skel O_pcc0) by (clear -SKx; congruence).
  assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (RNc : obj_range r0 oc = (T + 208 + 80 * c, T + 208 + 80 * c + 4)).
  { rewrite (obj_range_skel r0 oc O_pcc0 SKc). unfold O_pcc0. rewrite obj_range_mk by (clear; lia). rewrite EB. f_equal; clear; lia. }
  assert (RNs : obj_range r0 os = (T + 2768, T + 3168)).
  { rewrite (obj_range_skel r0 os O_st SKs). unfold O_st, vT. rewrite obj_range_mk by (clear; lia). cbn [eval]. rewrite R151, u64_lit by (clear -G5 G6 TG; lia). reflexivity. }
  assert (BZ : forall lo hi, armint G lo hi -> Forall (fun o' => ranges_disjoint (obj_range r0 o') (lo, hi)) ob).
  { intros lo hi HI. apply (base_zone W G r0 (ax_S E3) _ ob lo hi HG0 HS3 Hsm0); [intros o Ho; rewrite EO; apply in_or_app; left; exact Ho | exact SKb | | | | exact R151 | exact R152 | exact HI].
    - apply HFX0. apply in_or_app; left. apply in_or_app; right. cbn; tauto.
    - apply Forall_forall. intros p Hp. apply HFX0. apply in_or_app; left. apply in_or_app; left.
      destruct st; [apply chain_pre_in; exact Hp|]. exact (chain_pre_factsS' _ _ _ Hp).
    - rewrite R10, R15. exact Htop. }
  idtac "entry:4".

  assert (PRT : forall z, T <= z < T + 4096 -> (exists b, view segs (rm rhoE) z = Some b) ->
            wok_of segs (rm r0) (Z_to_bv 64 z) = true /\ exists x, rd_of segs (rm r0) (Z_to_bv 64 z) = Some x).
  { intros z Hz [b Hb]. rewrite Erm0. rewrite view_in in Hb by (clear -Hz G5 G6 TG; lia).
    eapply wok_rd_off_image2; [| |exact Hb]; [clear -Hz G5 G6 TG; lia | clear -Hz TI; lia]. }
  assert (PRS : forall z, SB <= z < SB + kSpaceSize + 4096 -> (exists b, view segs (rm rhoE) z = Some b) ->
            wok_of segs (rm r0) (Z_to_bv 64 z) = true /\ exists x, rd_of segs (rm r0) (Z_to_bv 64 z) = Some x).
  { intros z Hz [b Hb]. rewrite kSpaceSize_val in Hz. rewrite Erm0. rewrite view_in in Hb by (clear -Hz G13 G14 TG; unfold HIGH_SHADOW_END in *; lia).
    eapply wok_rd_off_image; [|exact Hb]. clear -Hz G13 G14 TG. unfold HIGH_SHADOW_END in *. lia. }

  assert (CVT : forall a k v (e : sv), T <= a -> a + Z.of_nat k <= T + 4096 -> eval r0 e = Z_to_bv 64 v ->
            cell_ok (maskv (fs_footb G) (view segs (rm rhoE))) (mkACell a k v) ->
            forall j, (j < k)%nat -> rd_of segs (rm r0) (Z_to_bv 64 (a + Z.of_nat j)) = Some (nth j (enc_bytes k (eval r0 e)) (Z_to_bv 8 0))).
  { intros a k v e Ha1 Ha2 Ee Hc j Hj. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc.
    rewrite MT in Hc by (clear -Ha1 Ha2 Hj; lia). rewrite view_in in Hc by (clear -Ha1 Ha2 Hj G5 G6 TG; lia). rewrite Erm0, Ee. exact Hc. }
  assert (CVS : forall a k v (e : sv), SB <= a -> a + Z.of_nat k <= SB + kSpaceSize + 4096 -> eval r0 e = Z_to_bv 64 v ->
            cell_ok (maskv (fs_footb G) (view segs (rm rhoE))) (mkACell a k v) ->
            forall j, (j < k)%nat -> rd_of segs (rm r0) (Z_to_bv 64 (a + Z.of_nat j)) = Some (nth j (enc_bytes k (eval r0 e)) (Z_to_bv 8 0))).
  { intros a k v e Ha1 Ha2 Ee Hc j Hj. specialize (Hc j Hj). cbn [c_addr c_w RtCells.c_val] in Hc.
    rewrite MS in Hc by (clear -Ha1 Ha2 Hj; lia). rewrite kSpaceSize_val in Ha2.
    rewrite view_in in Hc by (clear -Ha1 Ha2 Hj G13 G14 TG; unfold HIGH_SHADOW_END in *; lia). rewrite Erm0, Ee. exact Hc. }
  idtac "entry:5".
  assert (Hb : SPA segs (JR A Kc rhoE tp (cfg_model (w_cfg w)) ph0) (cR0a E3) r0 tp w).
  { apply (SPA_carve_list segs _ r0 E3 tp w NR0 GR Ha WR0a).
    - apply Pos.leb_le in NX3. clear -NX3. unfold GR. lia.
    - unfold NR0. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + rewrite EB. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear -C1 G5 TG; lia|]. split; [clear -C1 G5 G6 TG; lia|].
        split; [repeat apply Forall_cons; try apply Forall_nil; clear; lia|].
        split.
        { intros off Hoff. apply PRT; [clear -Hoff C1; lia|]. destruct (PE (T + 208 + 80 * c + off) ltac:(unfold T, G, c; clear -Hoff; lia)) as [b Hb']. exists b. rewrite <- MT by (clear -Hoff C1; lia). exact Hb'. }
        split; [|unfold xwords_clear; rewrite XX3; intros rr y j []].
        apply Forall_cons; [|apply Forall_nil]. intros j Hj.
        exact (CVT (T + 208 + 80 * c + 4) 4%nat (max_count c) vMC ltac:(clear -C1; lia) ltac:(clear -C1; lia) Q220 D2 j Hj).
      + rewrite ERI. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|].
        split; [clear -RIr G13; unfold HIGH_SHADOW_END in *; rewrite kSpaceSize_val in *; lia|].
        split; [clear -RIr G13 G14 TG; unfold HIGH_SHADOW_END in *; rewrite kSpaceSize_val in *; lia|].
        split; [repeat apply Forall_cons; try apply Forall_nil; clear; lia|].
        split.
        { intros off Hoff. apply PRS; [clear -Hoff RIr KSV; lia|]. destruct (PRI (region_info SB c + off) ltac:(unfold kRegionInfoStride; clear -Hoff; lia)) as [b Hb']. exists b. rewrite <- MS by (clear -Hoff RIr KSV; lia). exact Hb'. }
        split; [|unfold xwords_clear; rewrite XX3; intros rr y j []].
        unfold RI_mutex, RI_num_freed, RI_mapped_free_array, RI_allocated_user, RI_allocated_meta, RI_mapped_user, RI_mapped_meta, RI_exhausted in *.
        repeat apply Forall_cons; try apply Forall_nil; intros j Hj.
        * exact (CVS (region_info SB c + 0) 8%nat 0 (SLit 0) ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) eq_refl R1 j Hj).
        * exact (CVS (region_info SB c + 16) 8%nat _ vNF ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) Q221 R2 j Hj).
        * exact (CVS (region_info SB c + 24) 8%nat _ vMFA ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) Q222 R3 j Hj).
        * exact (CVS (region_info SB c + 32) 8%nat _ vAU ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) Q223 R4 j Hj).
        * exact (CVS (region_info SB c + 40) 8%nat 0 (SLit 0) ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) eq_refl R5 j Hj).
        * exact (CVS (region_info SB c + 48) 8%nat _ vMU ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) Q224 R6 j Hj).
        * exact (CVS (region_info SB c + 56) 8%nat 0 (SLit 0) ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) eq_refl R7 j Hj).
        * exact (CVS (region_info SB c + 68) 1%nat 0 (SLit 0) ltac:(clear -RIr KSV; lia) ltac:(clear -RIr KSV; cbn [Z.of_nat Pos.to_nat Pos.of_succ_nat]; lia) eq_refl R8 j Hj).
    - idtac "entry:6". cbn [map carve_obj NR0].
      assert (RNm : obj_range r0 (carved pc_base 4 8 [(4, 4%nat, vMC)]) = (T + 208 + 80 * c + 4, T + 208 + 80 * c + 8)).
      { unfold carved. rewrite obj_range_mk by (clear; lia). rewrite EB. reflexivity. }
      assert (RNr : obj_range r0 (carved vRI 0 128 [(0, 8%nat, SLit 0); (16, 8%nat, vNF); (24, 8%nat, vMFA); (32, 8%nat, vAU); (40, 8%nat, SLit 0); (48, 8%nat, vMU); (56, 8%nat, SLit 0); (68, 1%nat, SLit 0)])
                    = (region_info SB c + 0, region_info SB c + 128)).
      { unfold carved. rewrite obj_range_mk by (clear; lia). rewrite ERI. reflexivity. }
      destruct HS3 as (PS1 & _). fold T SB in PS1.
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; rewrite EO; apply Forall_app; split.
      + rewrite RNm. apply BZ. left. fold T. clear -C1. lia.
      + rewrite RNm. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; [rewrite RNc | rewrite RNs]; unfold ranges_disjoint; cbn [fst snd]; clear -C1; lia.
      + rewrite RNr. apply BZ. right; left. fold SB. clear -RIr KSV. lia.
      + rewrite RNr. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; [rewrite RNc | rewrite RNs]; unfold ranges_disjoint; cbn [fst snd]; clear -C1 RIr KSV PS1; lia.
    - cbn [map carve_obj NR0 pairwise_disjoint]. split; [|split; [constructor | exact I]].
      apply Forall_cons; [|apply Forall_nil]. unfold carved. rewrite !obj_range_mk by (clear; lia). rewrite EB, ERI.
      destruct HS3 as (PS1 & _). fold T SB in PS1. unfold ranges_disjoint; cbn [fst snd]. clear -C1 RIr KSV PS1. lia. }
  idtac "entry:7".

  unfold cR0. apply (SPA_refacts segs _ r0 (cR0a E3) _ tp w Hb FB0).
  intros HF0. apply Forall_app. split; [exact HF0|].
  assert (E155 : rw r0 155%positive = Z_to_bv 64 SB) by (rewrite <- (A0w 155%positive) by (clear; lia); rewrite <- (Hagw 155%positive) by (unfold GW; clear; lia); reflexivity).
  unfold kUserMapSize, kUserSpaceSize, kRegionSize, kFreeArraySize, kFreeArrayMapSize in N1, N2, N3, N5, N6.
  pose proof (Zle_0_nat (length (cs_free_array cs))) as NF0.
  assert (DSB : exists q, SB = q * 2 ^ 16) by (apply Z.mod_divide in G12; [destruct G12 as [q Hq]; exists q; exact Hq | clear; lia]).
  destruct DSB as [q Hq].
  unfold F_r0, F_r1, vMC, vK, vNF, vAU, vMU. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval].
  - rewrite Q220, !u64_lit by (clear -C4; lia). clear -K1 K2. lia.
  - rewrite Q220, !u64_lit by (clear -C4; lia). clear -C4. lia.
  - split; [clear; lia|]. rewrite Q225, u64_lit by (clear -RIr KSV G13 G14 TG; unfold HIGH_SHADOW_END in *; lia).
    unfold region_info, kRegionInfoStride. rewrite KSV, Hq. replace (q * 2 ^ 16 + 2 ^ 37 + c * 128) with ((q * 512 + 2 ^ 30 + c) * 2 ^ 7) by (clear; lia). apply Z_mod_mult.
  - split; [clear; lia|]. rewrite Q226.
    unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize.
    rewrite u64_lit by (clear -C1 G13 G14 TG KSV; unfold HIGH_SHADOW_END in *; lia).
    rewrite Hq. replace (q * 2 ^ 16 + c * 2 ^ 32 + (2 ^ 32 - 2 ^ 29)) with ((q * 16 + c * 2 ^ 20 + (2 ^ 20 - 2 ^ 17)) * 2 ^ 12) by (clear; lia). apply Z_mod_mult.
  - rewrite Q227, !u64_lit by (clear -K1; lia). clear -K1. lia.
  - rewrite Q227, !u64_lit by (clear -K1; lia). clear -K1. lia.
  - rewrite Q221, !u64_lit by (clear -N6 NF0; lia). clear -N6. lia.
  - rewrite Q223, Q224, !u64_lit by (clear -N2 N3; lia). clear -N2. lia.
  - split; [clear; lia|]. rewrite Q224, u64_lit by (clear -N2 N3; lia). exact N1.
  - split; [clear; lia|]. rewrite E155, u64_lit by (clear -G13 G14 TG KSV; unfold HIGH_SHADOW_END in *; lia). exact G12.
Qed.
End ENTRY.
End SpineCallocR1.

(* [comment removed for export] *)
Module SegQ3D_sum.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "AA"; "aa_q_global"; "aa_q_thread"; "@Corelib.Init.Datatypes"; "list"; "nil"; "app"; "nat"; "prod"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "holds"; "agree_below"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit"; "F_T0x"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel"; "A1T"; "rhoT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "TR"; "JOK"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel"; "JRQ"; "HVP"; "@Corelib.Init.Logic"; "eq"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMax"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "qsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "KEEP3"; "ReQ3e"; "ReQ3n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "JQ3"; "QW"; "sec_foot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece"; "keeps"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv"; "JRD"; "JRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop"; "QC_step"; "QI_step"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM"; "PreR2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states"; "PM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post"; "PostsQ3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep"; "hd_addr"; "last_addr"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQ3_post OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section RecSum.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Variables (A : AA) (rho : valuation) (tp : list word).
Hypothesis HTL : aa_q_thread A <> [].
Hypothesis HCI : aa_cache_inited A = true.
Hypothesis HBND : qbounded A.
Context {Q : assn} (X : trk Q).
Hypothesis HQ : ltac2:(tb__ "0|0|
S1cS2bSaS1fVrho;Vtp;S32VK;VA;A2R1A6VQ;R2A1F_;Fw;").
Hypothesis HJQ : ltac2:(tb__ "0|1|
S1S4S0A1M0G0S16VQ;VX;S18VK;VA;Vrho;R3R2R1A6A3Frest;Fpre;FA1;").
Hypothesis HJD : ltac2:(tb__ "0|1|
S1S4S0A1M0G0S16VQ;VX;S2cVK;VA;Vrho;R3R2R1A6A3Frest;Ftmp;FA1;").
Hypothesis HJI : ltac2:(tb__ "0|1|
S1S9S9S7S4S8S9S9A2A1S4S0A1M0G0S16VQ;VX;S2dVK;VA;Vrho;R7R6R5R4R3R2R1AaA3Frest;Ftmp;Fits;Fnd;Fn0;Fa;FA1;").
Let TPI : list word -> Prop := fun _ => True.
Let all : list qbatch := ltac2:(tb__ "0|0|
S6S0S2VA;A1S3VA;A1A3").

Definition PM_step : Prop := ltac2:(tb__ "0|0|
S17SbSdVrho;A1S12A3S28S1dS1eVall;A1A2ScS19R1Vall;A2S15VQ;VX;S10SaS18VK;VA;Vrho;S13VA;A1S5S0A1Vall;A6S31R2Vtp;A5A3F_;Frho';F_;F_;").
Hypothesis HQI : ltac2:(tb__ "0|0|
S4S0A1S2fVK;VA;Vrho;VQ;VX;R1VTPI;A7Frest;").
Hypothesis HQC : ltac2:(tb__ "0|0|
S4S0A1S2eVK;VA;Vrho;VQ;VX;R1VTPI;A7Frest;").
Hypothesis HPM : PM_step.

Lemma QW_A1T : ltac2:(tb__ "0|0|
S9S24S13VA;A1R1A2S24VA;R2A2F_;Fz;").
Proof.
  intros z [H|H]; [left | right; exact H]. unfold A1T in H.
  apply (proj1 (qzone_perm A [] (aa_q_global A ++ aa_q_thread A) z ltac:(unfold qall; cbn [app]; apply Permutation_app_comm))). exact H.
Qed.

Lemma SF_A1T : ltac2:(tb__ "0|0|
S9S25S13VA;A1R1A2S25VA;R2A2F_;Fz;").
Proof.
  intros z. apply sec_foot_mono; [reflexivity | intros y Hy; exact Hy |]. unfold A1T, qall. cbn [aa_q_thread aa_q_global set_q app].
  intros y Hy. rewrite qitems_app in *. apply in_app_or in Hy. apply in_or_app. tauto.
Qed.

Lemma rec_core : ltac2:(tb__ "0|0|
ScS17SbSdVrho;A1S12A3S19R2Vall;A2S28S1dS1eVall;A1A2S15VQ;VX;S10SaS18VK;VA;Vrho;S13VA;A1S5S0A1Vall;A6S30R4Vtp;A5A3F_;F_;F_;Frho2;").
Proof.
  intros rho2 HF0 HVp HGT.
  assert (HSZ : qsize all < 2 ^ 62).
  { unfold all. rewrite qsize_app. destruct HBND as [B1 B2]. unfold kQuarantineMax in B2. lia. }
  assert (NE : all <> []) by (unfold all; intros E; apply app_eq_nil in E as [_ E]; exact (HTL E)).
  apply (recycle_deq K HL A rho (A1T A) eq_refl HCI QW_A1T X (HJQ _) tp HSZ); [| exact (HPM HF0) | exact NE | exact HGT | exact HVp].
  intros tmp rest' rho3 NEt HG HS HV. change (aa_q_global (A1T A)) with all in HG.
  apply (tr_pure X _ (0 <= qsize rest')).
  { intros [tr [ms md]] Hw. destruct (proj2 Hw) as (HK & (HBM & _) & _). cbn [w_tr w_cfg cfg_model fst snd] in HK, HBM.
    pose proof (benv_of_K K HL (A1T A) HCI rho3 tp tr md HK) as BE. pose proof (proj1 (be_qp _ _ BE)) as HBP. rewrite (qall_A1 (A1T A) eq_refl) in HBP.
    change (aa_q_global (A1T A)) with all in HBP. rewrite HG in HBP. apply Forall_app in HBP as [_ P2]. apply Forall_app in HBM as [_ M2].
    pose proof (qsize_ge (A1T A) _ rest' P2 M2) as Q2. unfold kQuarantineBatchSize in Q2. lia. }
  intros HR0.
  apply (dorecycle_xg K HL A rho X HJD HJI rest' TPI (HQI rest') (HQC rest')); [| exact I | exact NEt | | | exact HV].
  - intros A' rho4 tp4 HTP (I1 & I2 & I3 & I4 & I5 & I6) E208.
    eapply (tr_conseq X); [|apply (tr_done X); exact HQ]. intros w Hw.
    apply (exit_R K HL A rho A' rest' rho4 tp tp4 w I1 I2 I3 I4 I5); [| exact E208 | exact HF0 | exact Hw].
    unfold kQuarantineMin, kQuarantineMax in *. lia.
  - split; [reflexivity|]. split; [exact HCI|]. split; [exact QW_A1T|]. split; [apply QP_refl_q|]. split; [exact HG | exact SF_A1T].
  - rewrite HG, qsize_app in HSZ. lia.
Qed.

Lemma F0x_of : ltac2:(tb__ "0|0|
S2aScS1cS11SeS1fVrho;R3A3S10SaR2R5R4Vtp;R3A6SbS27SbR1S12A3S27SbR2SfS29R8A1A1A3F_;Ff;S17SbSdVrho;A1S12A3F_;F_;F_;FJ;Fw;Frho';FSt;").
Proof.
  intros St rho' w J Hag Hw HIN. pose proof (SPA_facts_hold segsA _ rho' St tp w Hw) as HFa. apply Forall_forall. intros f Hf.
  apply (holds_agree_vals NPRE rho rho' f (agree_below_vals _ _ _ Hag) (proj1 (forallb_forall _ _) F_T0x_below f Hf)).
  exact (proj1 (Forall_forall _ _) HFa f (HIN f Hf)).
Qed.

Theorem recycle_sum_n : ltac2:(tb__ "0|1|
S1bS1aS4S0A1S2VA;A1M0S5S0A1A3A1ScS26S20S14VA;S33G0A1S34G0A1Vrho;A4R1A3S15VQ;VX;S10SaS23SaVK;VA;A3S22R2Vtp;A5A3F_;Frho';F_;").
Proof.
  intros HGL rho' HKp.
  destruct (rhoT_vals A (hd_addr (aa_q_global A)) (last_addr (aa_q_global A)) rho) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RAG).
  apply (tr_pure X _ (Forall (holds rho) F_T0x)).
  { intros w Hw. apply (F0x_of ReQ3n rho' w _ (agree_below_trans _ _ _ _ RAG (proj1 HKp)) Hw). intros f Hf. unfold F_T0x in Hf. cbn [In] in Hf.
    unfold ReQ3n, mkPost3; cbn [ax_S mkA ss_facts]. apply in_or_app; left. unfold F_Tn. apply in_or_app; left. unfold F_T0. apply in_or_app. right. cbn [In]. tauto. }
  intros HF0.
  apply (tr_glue X _ (JRQ K A rho (A1T A) [] all) PreR2 tp (fun r => HVP r all /\ kQuarantineMax < qsize all)).
  - intros w Hw. exact (entry_Rn K HL A rho rho' tp w HTL HGL HCI HBND HKp Hw).
  - intros r [R1 R2]. exact (rec_core r HF0 R1 R2).
Qed.

Theorem recycle_sum_e : ltac2:(tb__ "0|0|
S1aS4S0A1S2VA;A1S5S0A1A3S9S9ScS26S20S14VA;R3R2Vrho;A4R1A3S15VQ;VX;S10SaS23SaVK;VA;A3S21R2Vtp;A5A3F_;Frho';Fgb;Fgf;F_;").
Proof.
  intros HGL gf gb rho' HKp.
  destruct (rhoT_vals A gf gb rho) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RAG).
  apply (tr_pure X _ (Forall (holds rho) F_T0x)).
  { intros w Hw. apply (F0x_of ReQ3e rho' w _ (agree_below_trans _ _ _ _ RAG (proj1 HKp)) Hw). intros f Hf. unfold F_T0x in Hf. cbn [In] in Hf.
    unfold ReQ3e, mkPost3; cbn [ax_S mkA ss_facts]. apply in_or_app; left. unfold F_T. apply in_or_app; left. unfold F_T0. apply in_or_app. right. cbn [In]. tauto. }
  intros HF0.
  apply (tr_glue X _ (JRQ K A rho (A1T A) [] all) PreR2 tp (fun r => HVP r all /\ kQuarantineMax < qsize all)).
  - intros w Hw. exact (entry_Re K HL A gf gb rho rho' tp w HTL HGL HCI HBND HKp Hw).
  - intros r [R1 R2]. exact (rec_core r HF0 R1 R2).
Qed.
End RecSum.
End SegQ3D_sum.

(* [comment removed for export] *)
Module SegQ3D_qc_defs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "bool"; "list"; "true"; "option"; "prod"; "app"; "Some"; "false"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "valuation"; "SVar"; "ss_facts"; "sprop_below"; "SLit"; "ss_objs"; "FcsrFrm0"; "SPAlign"; "agree_below"; "mkSS"; "ss_lenient"; "ss_regs"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "la_state"; "ax_X"; "ax_setS"; "axwf"; "mkLeafA"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs"; "Cqc"; "RCr"; "sC"; "PostsQC"; "RC0"; "TC1"; "TQCf"; "TQC"; "KEPTC"; "TC2"; "idxC"; "renC"; "runCr"; "FRAMEC"; "RESTC"; "TC4"; "factsC"; "objsC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states"; "PreQC"; "PostQC"; "QCRET"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "LQA"; "stableA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM"; "vmap"; "chkNM"; "entsM"; "keepsM"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "TR"; "JOK"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "pre_facts"; "O_got"; "O_rtc"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM"; "MC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states"; "QCRET2"; "RC"; "DQC"; "DQCs"; "clsB"; "mkD"; "vB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states"; "vXF"; "vXK"; "vXL"; "vXS"; "FRlo"; "O_cbD"; "O_mtx00"; "SWD"; "cb_cells"; "NXR"; "WLOW"; "spD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "DEPTH_R"; "O_gmax"; "cbC"; "@Stdlib.Lists.List"; "forallb"; "In"; "fold_right"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "O_sb"; "runA"; "add"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "obj_subst"; "sprop_subst_opt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states"; "optR"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition renC : wsub := ltac2:(tb__ "0|2|
S0S8S3eSeA2M0S3S3eSePaS66A4S0G0S3S3eSePfM1S75S12G1A1S15Zc0A1A2A4S0G0S3S3eSePcS69A4S0G0S3S3eSePeS58A4S0G0S3S3eSeP7fS12PceA1A4S0G0S3S3eSeP80S12PcfA1A4S0G0S3S3eSeP81S12Pc9A1A4S0G0S3S3eSeP83S12Pd1A1A4S1G0A1A3A3A3A3A3A3A3A3").
Definition objsC : list sobj := ltac2:(tb__ "0|0|
S6dSdSdS7cS33A1S16S1eS3bA1A1A4").
Definition factsC : list sprop := ltac2:(tb__ "0|1|
S6cS5SfA1M0SfSfG0S7SfA1G0Lx;S7dS33R2A2SfS0SfR1R2A3Lg;R1X7x2Lacc;Lf;S1SfA1S13S1eS3bA1A1A5").
Definition FRAMEC : list sobj := ltac2:(tb__ "0|0|
S0SdS5fS0SdS60S63A1S0SdS62S5cS5bS5dS5eA4S0SdS61S0SdS68S1SdA1A3A3A3A3A3").
Definition Cqc : axst := ltac2:(tb__ "0|1|
S52S1aS56S1cS1eS57A1M0A1S7aS17ScSeA1S9SdS39S35A3S9SfS13G0A1S9SfS38S0SfS18P97ZcA2S1SfA1A3A3A3S64SbA9S1S8SeSeA2A1A2").
Definition sC : wsub := ltac2:(tb__ "0|0|
S7bP1S1eS28A1S1eS3bA1A3").
Definition RC0 : list sobj := ltac2:(tb__ "0|0|
S80S6fS28S3bS2aA3A1").
Definition PostsQC : list leafA := ltac2:(tb__ "0|0|
S0S20S25S3cS7eA2S1S20A1A3").
Definition TQC : axst := ltac2:(tb__ "0|0|
S70S2aS3bS3cS28S2cA5").
Definition TQCf : axst := ltac2:(tb__ "0|0|
S6eS2fS13S1eS28A1A1A2").

Lemma Cqc_wf : ltac2:(tb__ "0|1|
S27S26S4S24S28A1S6A3S27S26S4S1dS1eS28A1A1S6A3S26S5S8SeSeA2M0A1S22S28A1S1G0A1A3A2A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RC0_eq : RC0 = FRAMEC. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HeC : ltac2:(tb__ "0|1|
S26S7S5SdA1M0A1S6fS28S3bS2aA3SaG0S2cA2A3"). Proof. vm_cast_no_check (eq_refl (Some FRAMEC)). Qed.
Lemma HchkC : ltac2:(tb__ "0|0|
S26S4S71S28S3bS2aS2cS6dS20S1fS21S2bA4A5S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma HTC : ltac2:(tb__ "0|0|
S20S6bS20R1S2bA3S26S1fS70S2aS3bS21R2A1S28S2cA5S2fA3F_;FP;"). Proof. intros P [<-|[]]. reflexivity. Qed.
Lemma FBCC : ltac2:(tb__ "0|1|
S26S4S6aSfS14S10S1eS28A1M0A1A1S13G0A1A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FBTC : ltac2:(tb__ "0|0|
S26S4S6aSfS14S10S1eS2fA1A1A1S13S1eS28A1A1A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NXCC : ltac2:(tb__ "0|0|
S76S72S10S1eS28A1A1A2"). Proof. unfold Pos.le. cbn. discriminate. Qed.

Definition idxC : list nat := ltac2:(tb__ "0|0|
S0S2U0S0S2U7S0S2U8S0S2U9S0S2UaS0S2UbS0S2U5S0S2U6S0S2U4S0S2U1S0S2U2S0S2U3S1S2A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition TC1 : axst := ltac2:(tb__ "0|0|
S7S1fA1S1fLx;S4bS2eS0S49S4aS32A1S1S49A1A3A2S1fR1LX;S2eX7x2").
Lemma TC1_eq : ltac2:(tb__ "0|0|
S26S7S1fA1S4bS2eS0S49S4aS32A1S1S49A1A3A2SaS1fS2dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition KEPTC : list sobj := ltac2:(tb__ "0|0|
S0SdS65S0SdS5fS0SdS60S63A1S0SdS62S5cS5bS5dS5eA4S0SdS61S0SdS68S0SdS50S0SdS51S0SdS73S1SdA1A3A3A3A3A3A3A3A3A3").
Definition RESTC : list sobj := skipn 9 (ss_objs (ax_S TC1)).
Lemma TC1_objs : ltac2:(tb__ "0|0|
S26S5SdA1S16S1eS2dA1A1S9SdS30S36A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition TC2 : axst := ltac2:(tb__ "0|0|
S23S2dS7fS1eS2dA1S30A2A2").
Definition TC4 : axst := ltac2:(tb__ "0|0|
S6eS31S4fS67A1A2").
Definition RCr : axst := ltac2:(tb__ "0|1|
S59S3dS0S8S2SeA2M0S3S2SeU14S5aA4S0G0S3S2SeU1S15S54A1A4S1G0A1A3A3S5cS5bS5dS5eS0SdS73S1SdA1A3S4fS67A1A8").
Lemma TC4_ent : ltac2:(tb__ "0|0|
S26S4S47S37S29S53A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma TC4_below : ltac2:(tb__ "0|0|
S26S4S6aSfS14S10S1eS31A1A1A1S4fS67A1A3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition runCr : list leafA := ltac2:(tb__ "0|0|
S74UaS0S3fS54S1S3fA1A3S29A3").
Lemma runCr_eq : ltac2:(tb__ "0|0|
S26S5S20A1S74UaS0S3fS54S1S3fA1A3S29A3S34A3"). Proof. unfold runCr. reflexivity. Qed.
Lemma chkCrM : ltac2:(tb__ "0|1|
S26S4S46S10S1eS29A1A1S34S0S8S1fS45A2M0S3S1fS45S55S53A4S1G0A1A3A3S6A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma nxRCr : ltac2:(tb__ "0|1|
S27S26S4S1bS1eS29A1M0A1SbA3S76S72S10G0A1A2A2"). Proof. split; [reflexivity | unfold Pos.le; cbn; discriminate]. Qed.

Lemma QC_sumS : ltac2:(tb__ "0|1|
S79OF_;S41S11S5S4eQ40A1A1S44S3aR4R3A3S43S3aS10S1eS3bA1A1M0R4A3S78S3aR6S40S3aR5S3bR4R3A5S42S3aR5G0R4R3S2bA6A4F_;F_;Ftp;Frho;FJx;Fok;").
Proof.
  intros ok Jx rho tp HOK HST. rewrite (proj1 preQC_nx) in *.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (JQ_LQA1 Jx NPRE rho tp PostQC w Hw) | exact (seg_QC_sound Jx ok rho tp HOK HST)].
Qed.
Lemma QC_sumC : ltac2:(tb__ "0|1|
S41S11S5S4eQ40A1A1S43S3aS10S1eS3bA1A1M0R3A3S77S3aS40S3aR4S3bR3R2A5S42S3aR4G0R3R2S2bA6A3F_;Ftp;Frho;FJx;").
Proof.
  intros Jx rho tp HST. rewrite (proj1 preQC_nx) in *.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (JQ_LQA1 Jx NPRE rho tp PostQC w Hw) | exact (seg_QC_complete Jx rho tp HST)].
Qed.

Section TR.
Context {Q : assn} (X : trk Q).
Theorem seg_D_CrM : ltac2:(tb__ "0|1|
S41S11S5S4eQ40A1A1S4dVQ;VX;R3A3S1fS45S11S6bS8S1fS45A2M0S3S1fS45R3R2A4S0G0S3S1fS45S55S53A4S1G0A1A3A3S48R3R7R2A3S4cVQ;VX;S40S3aR9R5R3R7A5A3F_;F_;Frho';FM;FT;S4cVQ;VX;S40S3aR5S29R4R3A5A3F_;F_;Ftp;Frho;FJ;").
Proof. intros J rho tp HJ HC. exact (tr_piece X 10%nat _ RCr runCr [(RC, MC)] runCr_eq chkCrM (proj1 nxRCr) (proj2 nxRCr) J rho tp HJ HC). Qed.
Theorem qc_call : ltac2:(tb__ "0|0|
S41S11S5S4eQ40A1A1S4dVQ;VX;R3A3S11S19S10S1eS28A1A1R4R1A3S4cVQ;VX;S40S3aR6S2eR2R4A5A3F_;Frho';S4cVQ;VX;S40S3aR5S28R4R3A5A3F_;F_;Ftp;FrhoE;FJ;").
Proof.
  intros J rhoE tp HJ HC.
  exact (tr_call X Cqc PreQC PostsQC sC RC0 TQC QC_sumS QC_sumC HeC HchkC HTC FBCC FBTC NXCC J rhoE tp HJ HC).
Qed.
End TR.
End SegQ3D_qc_defs.

(* [comment removed for export] *)
Module SegQIF_defs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "cons"; "list"; "nil"; "true"; "option"; "pair"; "prod"; "app"; "None"; "Some"; "false"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "sprop"; "ss_next"; "ss_facts"; "valuation"; "sobj"; "SLit"; "rw"; "sprop_below"; "FcsrFrm0"; "agree_below"; "mkSS"; "ss_objs"; "ss_regs"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "la_state"; "ax_X"; "axwf"; "mkLeafA"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQIF_defs"; "CqiP"; "sP"; "RP"; "PostsQIP"; "TQP"; "TQPf"; "factsP"; "objsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQIP_states"; "PreQIP"; "PostQIP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "obj_subst"; "rho_sub"; "sprop_subst_opt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs"; "SIDEQ"; "FRAMEQ"; "renQ"; "sQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "LQA"; "stableA"; "ok_frameA"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "import_postA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "TR"; "JOK"; "@Stdlib.Lists.List"; "In"; "forallb"; "fold_right"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states"; "DQI"; "DQIs"; "vIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states"; "NXR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states"; "optR"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQIP_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.SegQIP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Definition objsP (vb : bool) : list sobj := ltac2:(tb__ "0|0|
S3fS14S14S31S37A1S1bS1eS2eVvb;A1A1A1A4").
Definition factsP (vb : bool) : list sprop := ltac2:(tb__ "0|1|
S48S2S10A1M0S10S10G0S5S10A1G0Lx;S33S37R2A2S10S1S10R1R2A3Lg;R1X5x2Lacc;Lf;S3S10A1S12S1eS2eVvb;A1A1A1A5").
Definition CqiP (vb : bool) : axst := ltac2:(tb__ "0|1|
S4fS1aS51S1cS1eS52A1M0A1S4cS18S9SeA1S8S14S2dVvb;A1S36A3S8S10S12G0A1S2cVvb;A1A3S54SbA9S3S7SeSeA2A1A2").

Definition sP (vb : bool) : wsub := ltac2:(tb__ "0|1|
S1S7S25SeA2M0S6S25SeP99S15Z1A1A4S1G0S6S25SeP9aS15Z0A1A4S1G0S6S25SeP94SfPc9A1A4S4dP1S1eS26Vvb;A1A1S1eS2eVvb;A1A1A3A3A3A3").
Definition RP (vb : bool) : list sobj := ltac2:(tb__ "0|0|
S55S41S26Vvb;A1S2eVvb;A1S27Vvb;A1A3A1").
Definition PostsQIP (vb : bool) : list leafA := ltac2:(tb__ "0|0|
S1S1fS24S2fVvb;A1S4eA2S3S1fA1A3").
Definition TQP (vb : bool) : axst := ltac2:(tb__ "0|0|
S42S27Vvb;A1S2eVvb;A1S2fVvb;A1S26Vvb;A1S28Vvb;A1A5").
Definition TQPf_of (vb : bool) : axst := ltac2:(tb__ "0|0|
S40S2aVvb;A1S12S1eS26Vvb;A1A1A1A2").
Definition TQPf_a : axst := Eval vm_compute in (TQPf_of false).
Definition TQPf_b : axst := Eval vm_compute in (TQPf_of true).
Definition TQPf (vb : bool) : axst := if vb then TQPf_b else TQPf_a.
Lemma TQPf_eq : ltac2:(tb__ "0|0|
S0ScS20S40S2aR1A1S12S1eS26R1A1A1A1A2S2bR1A1A3Fvb;"). Proof. intros [|]; vmr. Qed.

Lemma CqiP_wf : ltac2:(tb__ "0|2|
S0SdScS0S23S26R1A1M0A1S4A3SdScS0S1dS1eG0A1A1S4A3ScS2S7SeSeA2M1A1S22G0A1S3G1A1A3A2A2Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma RP_eq : ltac2:(tb__ "0|0|
S0ScS2S14A1S28R1A1S36A3Fvb;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma HeP : ltac2:(tb__ "0|1|
S0ScS5S2S14A1M0A1S41S26R1A1S2eR1A1S27R1A1A3SaG0S28R1A1A2A3Fvb;"). Proof. intros [|]; vm_cast_no_check (eq_refl (Some FRAMEQ)). Qed.
Lemma HchkP : ltac2:(tb__ "0|0|
S0ScS0S43S26R1A1S2eR1A1S27R1A1S28R1A1S3fS1fS20S21S29R1A1A4A5S4A3Fvb;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma HTP : ltac2:(tb__ "0|0|
S0S1fS46S1fR1S29R2A1A3ScS20S42S27R3A1S2eR3A1S21R2A1S26R3A1S28R3A1A5S2aR3A1A3F_;FP;Fvb;").
Proof. intros vb P [<-|[]]. reflexivity. Qed.
Lemma FBCP : ltac2:(tb__ "0|1|
S0ScS0S47S10S17S11S1eS26R1A1A1M0A1A1S12G0A1A3S4A3Fvb;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma FBTP : ltac2:(tb__ "0|0|
S0ScS0S47S10S17S11S1eS2aR1A1A1A1A1S12S1eS26R1A1A1A1A3S4A3Fvb;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Lemma NXCP : ltac2:(tb__ "0|0|
S0S56S50S11S1eS26R1A1A1A1A2Fvb;"). Proof. intros vb. unfold Pos.le. cbn. discriminate. Qed.

Lemma sP_vals : ltac2:(tb__ "0|3|
S0SdScSeS30S27R1A1M0PdA2S53A3SdScSeS30G0P9bM1A2SfG1A1A3SdScSeS30G0P9eA2SfPc8A1A3SdScSeS30G0P94A2SfPc9A1A3SdScSeS30G0P8aA2SfPcaA1A3SdScSeS30G0P8bA2SfPcbA1A3SdScSeS30G0P8dA2SfPccA1A3SdScSeS30G0P91A2SfPcdA1A3ScSeS30G0P92M2A2S0SeLvb;R1SfPd2A1SfG2A1X0x2A3A2A2A2A2A2A2A2A2Fvb;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma sP_sQ : ltac2:(tb__ "0|0|
S0S25S46S25R1S1S25PdS1S25P9bS1S25P9eS1S25P94S1S25P8aS1S25P8bS1S25P8dS1S25P91S1S25P92S3S25A1A3A3A3A3A3A3A3A3A3A3ScSeS30S27R3A1R2A2S30S38R3A1R2A2A3F_;Fv;Fvb;").
Proof. intros [|] v Hv; cbn [In] in Hv; repeat (destruct Hv as [<-|Hv]; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|]); destruct Hv. Qed.

Lemma SIDEP_ext : ltac2:(tb__ "0|0|
S0S13S13S25S57R1S11S1eS2eR4A1A1A1A2ScS3eQ40A1S16R3R2A2S16R4R2A2A3F_;Fi;S35R4R3A2S35R5R3A2F_;F_;Fr';Fr;Fvb;").
Proof.
  intros vb r r' HE. apply (SIDEQ_ext vb r r'). intros i Hi. apply HE. rewrite (proj1 (proj2 (proj2 (preQIP_wf vb)))). rewrite (proj1 (proj2 (proj2 (preQI_wf vb)))) in Hi. exact Hi.
Qed.
Lemma QIP_sumS : ltac2:(tb__ "0|1|
S0S4bOF_;S3aS13S2S3eQ40A1A1S3dS34R4R3A3S3cS34S11S1eS2eR6A1A1A1R4A3S35R7R4A2S4aS34R7S39S34R6S2eR8A1M0R5R4A5S3bS34R6S11S1eG0A1A1R5R4S29R8A1A6A4F_;F_;F_;Ftp;Frho;FJx;Fok;Fvb;").
Proof.
  intros vb ok Jx rho tp HOK HST (x & d & HS). rewrite (proj1 (proj2 (proj2 (preQIP_wf vb)))) in *.
  eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (JQ_LQA1 Jx NPRE rho tp (PostQIP vb) w Hw) | exact (seg_QIP_sound_clean vb Jx ok rho tp x d HOK HST HS)].
Qed.
Lemma QIP_sumC : ltac2:(tb__ "0|1|
S0S3aS13S2S3eQ40A1A1S3cS34S11S1eS2eR4A1A1A1R3A3S35R5R3A2S49S34S39S34R5S2eR6A1M0R4R3A5S3bS34R5S11S1eG0A1A1R4R3S29R6A1A6A3F_;F_;Ftp;Frho;FJx;Fvb;").
Proof.
  intros vb Jx rho tp HST (x & d & HS). rewrite (proj1 (proj2 (proj2 (preQIP_wf vb)))) in *.
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (JQ_LQA1 Jx NPRE rho tp (PostQIP vb) w Hw) | exact (seg_QIP_complete_clean vb Jx rho tp x d HST HS)].
Qed.

Section CALLP.
Context {Q : assn} (X : trk Q).
Theorem qip_call : ltac2:(tb__ "0|1|
S0S3aS13S2S3eQ40A1A1S45VQ;VX;R3A3S35R5S32R3S27R5A1A2A2S13S19S11S1eS26R7A1M0A1A1R5R1A3S44VQ;VX;S39S34R7S2bR8A1R2R5A5A3F_;Frho';S44VQ;VX;S39S34R6G0R5R4A5A3F_;F_;F_;Ftp;FrhoE;FJ;Fvb;").
Proof.
  intros vb J rhoE tp HJ HS HC.
  apply (tr_callS X (CqiP vb) (PreQIP vb) (PostsQIP vb) (sP vb) (RP vb) (TQP vb) (SIDEQ vb) (SIDEP_ext vb) (QIP_sumS vb) (QIP_sumC vb)
           (HeP vb) (HchkP vb) (HTP vb) (FBCP vb) (FBTP vb) (NXCP vb) J rhoE tp HJ HS).
  intros rho' Hag. rewrite (TQPf_eq vb). exact (HC rho' Hag).
Qed.
End CALLP.
End SegQIF_defs.

